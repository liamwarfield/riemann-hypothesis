module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.ExistsDecayBoundTwo
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.HcToIdele

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.IsFiniteMeasureRestrictFd
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap ContDiff
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem integral_count_Xi (f : Xi F → ℂ) : ∫ ξ, f ξ ∂(Measure.count : Measure (Xi F)) = ∑' ξ, f ξ := by
  by_cases hf : Summable f
  · have hi : Integrable f (Measure.count : Measure (Xi F)) := by
      rw [integrable_count_iff]
      exact summable_norm_iff.mpr hf
    rw [integral_countable hi]
    simp [count_real_singleton]
  · rw [tsum_eq_zero_of_not_summable hf, integral_undef]
    intro hi
    rw [integrable_count_iff] at hi
    exact hf (summable_norm_iff.mp hi)

theorem integral_iter_eq (S : Set {r : ℝ // 0 < r}) (hS : MeasurableSet S) {h : Pp F × Xi F → ℂ}
    (hh : Integrable h (μS F S)) :
    IntegrableOn (fun t => ∫ u in normOneFundamentalDomain F, ∑' ξ : Xi F, h ((t, u), ξ) ∂normOneMeasure F)
        S posRealMeasure ∧
      ∫ t in S, ∫ u in normOneFundamentalDomain F, ∑' ξ : Xi F, h ((t, u), ξ) ∂normOneMeasure F
          ∂posRealMeasure = ∫ q, h q ∂μS F S := by
  have e1 : ∀ p : Pp F, ∫ ξ, h (p, ξ) ∂(Measure.count : Measure (Xi F)) = ∑' ξ : Xi F, h (p, ξ) :=
    fun p => integral_count_Xi _
  have hG : Integrable (fun p : Pp F => ∑' ξ : Xi F, h (p, ξ))
      ((posRealMeasure.restrict S).prod ((normOneMeasure F).restrict (normOneFundamentalDomain F))) := by
    have := hh.integral_prod_left
    simp only [e1] at this
    exact this
  refine ⟨?_, ?_⟩
  · have := hG.integral_prod_left
    exact this
  · rw [μS, integral_prod _ hh]
    simp only [e1]
    rw [integral_prod _ hG]

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.PFinModuleSectionInv
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap ContDiff
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem norm_vecMul_le' (v : Vr F) (M : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    ‖v ᵥ* M‖ ≤ ‖v‖ * ∑ i, ∑ j, ‖M i j‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  calc ‖(v ᵥ* M) j‖ = ‖∑ i, v i * M i j‖ := by simp only [Matrix.vecMul, dotProduct]
    _ ≤ ∑ i, ‖v i * M i j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖v‖ * ‖M i j‖ := Finset.sum_le_sum fun i _ =>
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_le_pi_norm v i) (norm_nonneg _))
    _ = ‖v‖ * ∑ i, ‖M i j‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ ‖v‖ * ∑ i, ∑ j, ‖M i j‖ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
        Finset.single_le_sum (f := fun j => ‖M i j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j))
        (norm_nonneg _)

theorem norm_mulVec_le' (M : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) (v : Vr F) :
    ‖M *ᵥ v‖ ≤ (∑ i, ∑ j, ‖M i j‖) * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  calc ‖(M *ᵥ v) i‖ = ‖∑ j, M i j * v j‖ := by simp only [Matrix.mulVec, dotProduct]
    _ ≤ ∑ j, ‖M i j * v j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖M i j‖ * ‖v‖ := Finset.sum_le_sum fun j _ =>
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (norm_nonneg _))
    _ = (∑ j, ‖M i j‖) * ‖v‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ i, ∑ j, ‖M i j‖) * ‖v‖ := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖) (fun _ _ => by positivity) (Finset.mem_univ i))
        (norm_nonneg _)

theorem inv_pow_le_of_le {p w K : ℝ} (hp : 0 ≤ p) (hw : 0 ≤ w) (hK : 0 ≤ K) (h : p ≤ K * w) (k : ℕ) :
    ((1 + w) ^ k)⁻¹ ≤ (K + 1) ^ k * ((1 + p) ^ k)⁻¹ := by
  have h1 : 1 + p ≤ (K + 1) * (1 + w) := by nlinarith
  have hpos : 0 < (1 + p) ^ k := by positivity
  calc ((1 + w) ^ k)⁻¹ = (K + 1) ^ k * (((K + 1) * (1 + w)) ^ k)⁻¹ := by
        rw [mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    _ ≤ (K + 1) ^ k * ((1 + p) ^ k)⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ hpos (pow_le_pow_left₀ (by positivity) h1 k)) (by positivity)

theorem rowv_eq (g : GA F 2) (a : Ideles F) (ξ : Fin 2 → F) :
    rowv g a ξ = fun j => (a : Ad F) * (rowA ξ ᵥ* (g : Matrix (Fin 2) (Fin 2) (Ad F))) j := by
  funext j
  simp only [rowv, Mrow, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_mul, Matrix.vecMul, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem colv_eq (g : GA F 2) (a : Ideles F) (ξ : Fin 2 → F) :
    colv g a ξ = fun j => ((a⁻¹ : Ideles F) : Ad F) *
      (((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ) j := by
  funext j
  simp only [colv, Mcol, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.mul_diagonal, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem vInf_rowv (g : GA F 2) (a : Ideles F) (ξ : Fin 2 → F) :
    vInf (rowv g a ξ) = (fun i => UpperTheory.V.TR.pInf F ((a : Ad F) * algebraMap F (Ad F) (ξ i))) ᵥ*
      (g : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) := by
  funext j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [vInf, rowv_eq, Matrix.vecMul, dotProduct, Finset.mul_sum, map_sum, map_mul, Matrix.map_apply, rowA]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem vInf_colv (g : GA F 2) (a : Ideles F) (ξ : Fin 2 → F) :
    vInf (colv g a ξ) = ((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) *ᵥ
      (fun i => UpperTheory.V.TR.pInf F (((a⁻¹ : Ideles F) : Ad F) * algebraMap F (Ad F) (ξ i))) := by
  funext j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [vInf, colv_eq, Matrix.mulVec, dotProduct, Finset.mul_sum, map_sum, map_mul, Matrix.map_apply, rowA]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem map_pInf_mul_inv (g : GA F 2) :
    (g : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) *
      ((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem pFin_moduleSection (t : {r : ℝ // 0 < r}) :
    pFin F ((moduleSection (w0 F) t : Ideles F) : Ad F) = 1 := by
  rw [coe_moduleSection]
  rfl

theorem pFin_moduleSection_inv (t : {r : ℝ // 0 < r}) :
    pFin F ((((moduleSection (w0 F) t)⁻¹ : Ideles F)) : Ad F) = 1 := by
  have h : pFin F (((moduleSection (w0 F) t)⁻¹ : Ideles F) : Ad F) *
      pFin F ((moduleSection (w0 F) t : Ideles F) : Ad F) = 1 := by
    rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  rwa [pFin_moduleSection, mul_one] at h

theorem finite_row_congr {c : HeightOneSpectrum (𝓞 F) → ℕ} {y y' : Fin 2 → Ad F}
    (h : ∀ i, pFin F (y i) = pFin F (y' i)) : finRow c y = finRow c y' := by
  unfold finRow
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (by simpa only [h] using h1) h2
  · exact absurd (by simpa only [← h] using h2) h1
  · rfl

theorem finite_column_congr {c : HeightOneSpectrum (𝓞 F) → ℕ} {y y' : Fin 2 → Ad F}
    (h : ∀ i, pFin F (y i) = pFin F (y' i)) : finCol c y = finCol c y' := by
  unfold finCol
  split_ifs with h1 h2 h2
  · rw [h 1]
  · exact absurd (by simpa only [h] using h1) h2
  · exact absurd (by simpa only [← h] using h2) h1
  · rfl

theorem finRow_av (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (p : Pp F) (ξ : Fin 2 → F) :
    finRow c (rowv g (av p) ξ) = finRow c (rowv g (p.2 : Ideles F) ξ) := by
  refine finite_row_congr fun i => ?_
  simp only [rowv_eq, av, Units.val_mul, map_mul, pFin_moduleSection, one_mul]

theorem finCol_av (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (p : Pp F) (ξ : Fin 2 → F) :
    finCol c (colv g (av p) ξ) = finCol c (colv g (p.2 : Ideles F) ξ) := by
  refine finite_column_congr fun i => ?_
  simp only [colv_eq, av, mul_inv_rev, Units.val_mul, map_mul, pFin_moduleSection_inv, mul_one]

theorem norm_finRow_le (c : HeightOneSpectrum (𝓞 F) → ℕ) (y : Fin 2 → Ad F) : ‖finRow c y‖ ≤ 1 := by
  unfold finRow
  split_ifs <;> simp

theorem norm_finCol_le (c : HeightOneSpectrum (𝓞 F) → ℕ) (y : Fin 2 → Ad F) : ‖finCol c y‖ ≤ 1 := by
  unfold finCol
  split_ifs
  · exact (Circle.norm_coe _).le
  · simp

theorem hint1 {χ : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (H : Hyp χ c) (g : GA F 2)
    (hκ : AEStronglyMeasurable (kap1 χ c g) (μS F {t | 1 ≤ (t : ℝ)}))
    (hw : AEStronglyMeasurable (w1 g) (μS F {t | 1 ≤ (t : ℝ)})) :
    ∃ k : ℕ, Integrable (fun q => ‖kap1 χ c g q‖ * ((1 + ‖w1 g q‖) ^ k)⁻¹) (μS F {t | 1 ≤ (t : ℝ)}) := by
  classical
  set E := normOneFundamentalDomain F with hEdef
  set C : Set (Ideles F) := (fun u : normOneSubgroup F => (u : Ideles F)) '' closure E with hCdef
  have hC : IsCompact C := (isCompact_closure_normOneFundamentalDomain (K := F)).image continuous_subtype_val
  obtain ⟨d, hd0, hd⟩ := exists_den_row c g hC
  obtain ⟨k, U, hU, hdec⟩ := exists_decay_bound_two F hC d hd0 2
  set G' := ((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) with hG'
  set K := ∑ i, ∑ j, ‖G' i j‖ with hKdef
  have hK : 0 ≤ K := by positivity
  refine ⟨k, ?_⟩
  haveI : IsFiniteMeasure ((normOneMeasure F).restrict E) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact normOneMeasure_normOneFundamentalDomain_lt_top F⟩
  set bnd : Pp F × Xi F → ℝ := fun q =>
    (K + 1) ^ k * (((((q.1.1 : ℝ) ^ 2)⁻¹ * (q.1.1 : ℝ)) * 1) * |U q.2.1|) with hbnddef
  have hbnd : Integrable bnd (μS F {t | 1 ≤ (t : ℝ)}) := by
    have h1 : Integrable (fun t : {r : ℝ // 0 < r} => ((t : ℝ) ^ 2)⁻¹ * (t : ℝ))
        (posRealMeasure.restrict {t | 1 ≤ (t : ℝ)}) := integrableOn_ge_one le_rfl
    have h2 : Integrable (fun _ : normOneSubgroup F => (1 : ℝ)) ((normOneMeasure F).restrict E) :=
      integrable_const _
    have h3 : Integrable (fun ξ : Xi F => |U ξ.1|) Measure.count := by
      rw [integrable_count_iff]
      have hi : Function.Injective (fun x : Xi F => x.1) := fun x y h => Subtype.ext h
      simpa [Function.comp_def] using hU.abs.comp_injective hi
    exact ((h1.mul_prod h2).mul_prod h3).const_mul ((K + 1) ^ k)
  refine hbnd.mono' ?_ ?_
  · exact (hκ.aemeasurable.norm.mul ((hw.aemeasurable.norm.const_add 1).pow_const k).inv).aestronglyMeasurable
  have hae : ∀ᵐ q ∂(μS F {t | 1 ≤ (t : ℝ)}), 1 ≤ (q.1.1 : ℝ) ∧ q.1.2 ∈ E := by
    have ha : ∀ᵐ t : {r : ℝ // 0 < r} ∂(posRealMeasure.restrict {t : {r : ℝ // 0 < r} | 1 ≤ (t : ℝ)}), 1 ≤ (t : ℝ) :=
      ae_restrict_mem measurableSet_ge_one
    have hb : ∀ᵐ u ∂((normOneMeasure F).restrict E), u ∈ E :=
      ae_restrict_mem (measurableSet_normOneFundamentalDomain F)
    have h1 : ∀ᵐ p ∂((posRealMeasure.restrict {t : {r : ℝ // 0 < r} | 1 ≤ (t : ℝ)}).prod
        ((normOneMeasure F).restrict E)), 1 ≤ (p.1 : ℝ) ∧ p.2 ∈ E := by
      filter_upwards [Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually ha,
        Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually hb] with p h1 h2 using ⟨h1, h2⟩
    exact Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually h1
  filter_upwards [hae] with q hq
  obtain ⟨⟨t, u⟩, ⟨ξ, hξ⟩⟩ := q
  obtain ⟨ht, hu⟩ := hq
  simp only at ht hu
  have hbpos : 0 ≤ bnd ((t, u), ⟨ξ, hξ⟩) := by simp only [hbnddef]; positivity
  rw [Real.norm_of_nonneg (by positivity)]
  by_cases hf : finRow c (rowv g (av (t, u)) ξ) = 0
  · have : kap1 χ c g ((t, u), ⟨ξ, hξ⟩) = 0 := by simp only [kap1]; rw [hf, zero_mul, zero_mul]
    rw [this, norm_zero, zero_mul]
    exact hbpos
  have huC : (u : Ideles F) ∈ C := ⟨u, subset_closure hu, rfl⟩
  have hcond : ∀ w, Valued.v (pLoc F w (pFin F ((rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2)
      (u : Ideles F) * g : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) 0))) ≤ WithZero.exp (-(c w : ℤ)) ∧
      Valued.v (pLoc F w (pFin F ((rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) (u : Ideles F) * g :
        GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) 1)) - 1) ≤ WithZero.exp (-(c w : ℤ)) := by
    rw [finRow_av] at hf
    unfold finRow at hf
    split_ifs at hf with hc
    · exact hc
    · exact absurd rfl hf
  have hden := hd _ huC ξ hcond
  have hdecay := hdec _ huC t ht ξ hξ hden
  set P : Vr F := fun i => UpperTheory.V.TR.pInf F (((moduleSection (w0 F) t * (u : Ideles F) : Ideles F) : Ad F) *
    algebraMap F (Ad F) (ξ i)) with hPdef
  have hw1 : w1 g ((t, u), ⟨ξ, hξ⟩) = P ᵥ* (g : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) := by
    simp only [w1]
    rw [vInf_rowv]
    rfl
  have hPw : ‖P‖ ≤ K * ‖w1 g ((t, u), ⟨ξ, hξ⟩)‖ := by
    have e : P = w1 g ((t, u), ⟨ξ, hξ⟩) ᵥ* G' := by
      rw [hw1, Matrix.vecMul_vecMul, hG', map_pInf_mul_inv, Matrix.vecMul_one]
    calc ‖P‖ = ‖w1 g ((t, u), ⟨ξ, hξ⟩) ᵥ* G'‖ := by rw [← e]
      _ ≤ ‖w1 g ((t, u), ⟨ξ, hξ⟩)‖ * K := norm_vecMul_le' _ _
      _ = K * ‖w1 g ((t, u), ⟨ξ, hξ⟩)‖ := mul_comm _ _
  have hkap : ‖kap1 χ c g ((t, u), ⟨ξ, hξ⟩)‖ ≤ (t : ℝ) := by
    simp only [kap1, norm_mul, norm_inv, norm_hchar_of_finOrder H.fin, inv_one, mul_one, Complex.norm_real,
      Real.norm_of_nonneg t.2.le]
    exact mul_le_of_le_one_left t.2.le (norm_finRow_le c _)
  have hw' := inv_pow_le_of_le (norm_nonneg P) (norm_nonneg _) hK hPw k
  have hUabs : U ξ ≤ |U ξ| := le_abs_self _
  have ht0 : (0 : ℝ) < t := t.2
  calc ‖kap1 χ c g ((t, u), ⟨ξ, hξ⟩)‖ * ((1 + ‖w1 g ((t, u), ⟨ξ, hξ⟩)‖) ^ k)⁻¹
      ≤ (t : ℝ) * ((K + 1) ^ k * (((t : ℝ) ^ 2)⁻¹ * U ξ)) :=
        mul_le_mul hkap (hw'.trans (mul_le_mul_of_nonneg_left hdecay (by positivity))) (by positivity) ht0.le
    _ ≤ (t : ℝ) * ((K + 1) ^ k * (((t : ℝ) ^ 2)⁻¹ * |U ξ|)) := by gcongr
    _ = bnd ((t, u), ⟨ξ, hξ⟩) := by simp only [hbnddef]; ring

theorem hint2 {χ : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (H : Hyp χ c) (g : GA F 2)
    (hκ : AEStronglyMeasurable (kap2 χ c g) (μS F {t | (t : ℝ) < 1}))
    (hw : AEStronglyMeasurable (w2 g) (μS F {t | (t : ℝ) < 1})) :
    ∃ k : ℕ, Integrable (fun q => ‖kap2 χ c g q‖ * ((1 + ‖w2 g q‖) ^ k)⁻¹) (μS F {t | (t : ℝ) < 1}) := by
  classical
  set E := normOneFundamentalDomain F with hEdef
  set C : Set (Ideles F) := (fun u : normOneSubgroup F => (u : Ideles F)) '' closure E with hCdef
  have hC : IsCompact C := (isCompact_closure_normOneFundamentalDomain (K := F)).image continuous_subtype_val
  set C2 : Set (Ideles F) := (fun u : normOneSubgroup F => ((u : Ideles F))⁻¹) '' closure E with hC2def
  have hC2 : IsCompact C2 :=
    (isCompact_closure_normOneFundamentalDomain (K := F)).image continuous_subtype_val.inv
  obtain ⟨d, hd0, hd⟩ := exists_den_col c (finite_support_of_hyp H) g hC
  obtain ⟨k, U, hU, hdec⟩ := exists_decay_bound_two F hC2 d hd0 2
  set G := (g : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) with hG
  set G' := ((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) with hG'
  set K := ∑ i, ∑ j, ‖G i j‖ with hKdef
  have hK : 0 ≤ K := by positivity
  refine ⟨k, ?_⟩
  haveI : IsFiniteMeasure ((normOneMeasure F).restrict E) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact normOneMeasure_normOneFundamentalDomain_lt_top F⟩
  set bnd : Pp F × Xi F → ℝ := fun q =>
    (K + 1) ^ k * (((((q.1.1 : ℝ) ^ 2) * (q.1.1 : ℝ)⁻¹) * 1) * |U q.2.1|) with hbnddef
  have hbnd : Integrable bnd (μS F {t | (t : ℝ) < 1}) := by
    have h1 : Integrable (fun t : {r : ℝ // 0 < r} => (t : ℝ) ^ 2 * (t : ℝ)⁻¹)
        (posRealMeasure.restrict {t | (t : ℝ) < 1}) := integrableOn_lt_one le_rfl
    have h2 : Integrable (fun _ : normOneSubgroup F => (1 : ℝ)) ((normOneMeasure F).restrict E) :=
      integrable_const _
    have h3 : Integrable (fun ξ : Xi F => |U ξ.1|) Measure.count := by
      rw [integrable_count_iff]
      have hi : Function.Injective (fun x : Xi F => x.1) := fun x y h => Subtype.ext h
      simpa [Function.comp_def] using hU.abs.comp_injective hi
    exact ((h1.mul_prod h2).mul_prod h3).const_mul ((K + 1) ^ k)
  refine hbnd.mono' ?_ ?_
  · exact (hκ.aemeasurable.norm.mul ((hw.aemeasurable.norm.const_add 1).pow_const k).inv).aestronglyMeasurable
  have hae : ∀ᵐ q ∂(μS F {t | (t : ℝ) < 1}), (q.1.1 : ℝ) < 1 ∧ q.1.2 ∈ E := by
    have ha : ∀ᵐ t : {r : ℝ // 0 < r} ∂(posRealMeasure.restrict {t : {r : ℝ // 0 < r} | (t : ℝ) < 1}),
        (t : ℝ) < 1 := ae_restrict_mem measurableSet_lt_one
    have hb : ∀ᵐ u ∂((normOneMeasure F).restrict E), u ∈ E :=
      ae_restrict_mem (measurableSet_normOneFundamentalDomain F)
    have h1 : ∀ᵐ p ∂((posRealMeasure.restrict {t : {r : ℝ // 0 < r} | (t : ℝ) < 1}).prod
        ((normOneMeasure F).restrict E)), (p.1 : ℝ) < 1 ∧ p.2 ∈ E := by
      filter_upwards [Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually ha,
        Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually hb] with p h1 h2 using ⟨h1, h2⟩
    exact Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually h1
  filter_upwards [hae] with q hq
  obtain ⟨⟨t, u⟩, ⟨ξ, hξ⟩⟩ := q
  obtain ⟨ht, hu⟩ := hq
  simp only at ht hu
  have hbpos : 0 ≤ bnd ((t, u), ⟨ξ, hξ⟩) := by
    simp only [hbnddef]
    exact mul_nonneg (pow_nonneg (by linarith) _) (mul_nonneg (mul_nonneg (mul_nonneg
      (pow_nonneg t.2.le _) (inv_nonneg.2 t.2.le)) zero_le_one) (abs_nonneg _))
  rw [Real.norm_of_nonneg (by positivity)]
  by_cases hf : finCol c (colv g (av (t, u)) ξ) = 0
  · have : kap2 χ c g ((t, u), ⟨ξ, hξ⟩) = 0 := by simp only [kap2]; rw [hf, zero_mul, zero_mul]
    rw [this, norm_zero, zero_mul]
    exact hbpos
  have huC : (u : Ideles F) ∈ C := ⟨u, subset_closure hu, rfl⟩
  have hu2 : ((u : Ideles F))⁻¹ ∈ C2 := ⟨u, subset_closure hu, rfl⟩
  have hden := hd _ huC ξ (by
    rw [finCol_av] at hf
    unfold finCol at hf
    split_ifs at hf with hc
    · exact hc
    · exact absurd rfl hf)
  have ht0 : (0 : ℝ) < t := t.2
  have hT : ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ) = (t : ℝ)⁻¹ := Positive.coe_inv t
  have hT1 : 1 ≤ ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ) := by
    rw [hT]; exact (one_le_inv₀ ht0).2 ht.le
  have hdecay := hdec _ hu2 t⁻¹ hT1 ξ hξ hden
  have hav : moduleSection (w0 F) t⁻¹ * ((u : Ideles F))⁻¹ = (av (t, u))⁻¹ := by
    simp only [av, map_inv, mul_inv]
  set P : Vr F := fun i => UpperTheory.V.TR.pInf F (((moduleSection (w0 F) t⁻¹ * ((u : Ideles F))⁻¹ : Ideles F) :
    Ad F) * algebraMap F (Ad F) (ξ i)) with hPdef
  have hw2 : w2 g ((t, u), ⟨ξ, hξ⟩) = G' *ᵥ P := by
    simp only [w2]
    rw [vInf_colv, hPdef, hav]
  have hPw : ‖P‖ ≤ K * ‖w2 g ((t, u), ⟨ξ, hξ⟩)‖ := by
    have e : P = G *ᵥ w2 g ((t, u), ⟨ξ, hξ⟩) := by
      rw [hw2, Matrix.mulVec_mulVec, hG, hG', map_pInf_mul_inv, Matrix.one_mulVec]
    calc ‖P‖ = ‖G *ᵥ w2 g ((t, u), ⟨ξ, hξ⟩)‖ := by rw [← e]
      _ ≤ K * ‖w2 g ((t, u), ⟨ξ, hξ⟩)‖ := norm_mulVec_le' _ _
  have hkap : ‖kap2 χ c g ((t, u), ⟨ξ, hξ⟩)‖ ≤ (t : ℝ)⁻¹ := by
    simp only [kap2, norm_mul, norm_inv, norm_hchar_of_finOrder H.fin, inv_one, mul_one, Complex.norm_real,
      Real.norm_of_nonneg t.2.le]
    exact mul_le_of_le_one_left (inv_nonneg.2 t.2.le) (norm_finCol_le c _)
  have hw' := inv_pow_le_of_le (norm_nonneg P) (norm_nonneg _) hK hPw k
  have hUabs : U ξ ≤ |U ξ| := le_abs_self _
  calc ‖kap2 χ c g ((t, u), ⟨ξ, hξ⟩)‖ * ((1 + ‖w2 g ((t, u), ⟨ξ, hξ⟩)‖) ^ k)⁻¹
      ≤ (t : ℝ)⁻¹ * ((K + 1) ^ k * (((((t⁻¹ : {r : ℝ // 0 < r}) : ℝ)) ^ 2)⁻¹ * U ξ)) :=
        mul_le_mul hkap (hw'.trans (mul_le_mul_of_nonneg_left hdecay (by positivity))) (by positivity)
          (inv_nonneg.2 ht0.le)
    _ ≤ (t : ℝ)⁻¹ * ((K + 1) ^ k * (((((t⁻¹ : {r : ℝ // 0 < r}) : ℝ)) ^ 2)⁻¹ * |U ξ|)) := by gcongr
    _ = bnd ((t, u), ⟨ξ, hξ⟩) := by simp only [hbnddef]; rw [hT]; field_simp

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.HasFDerivAtIntegralSchwartzBilin
open MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff

noncomputable section

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

set_option linter.unusedSectionVars false

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

theorem natCast_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top

theorem natCast_lt_infty (m : ℕ) : (m : WithTop ℕ∞) < ∞ := WithTop.coe_lt_coe.2 (ENat.natCast_lt_top m)

theorem infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

def bilD (Ψ : 𝓢(V, ℂ)) (B : V →L[ℝ] X →L[ℝ] V) (m : ℕ) (v : V) (x : X) :
    ContinuousMultilinearMap ℝ (fun _ : Fin m => X) ℂ :=
  iteratedFDeriv ℝ m (fun x => Ψ (B v x)) x

theorem contDiff_bil (Ψ : 𝓢(V, ℂ)) (B : V →L[ℝ] X →L[ℝ] V) (v : V) :
    ContDiff ℝ ∞ (fun x => Ψ (B v x)) :=
  (Ψ.smooth ⊤).comp (B v).contDiff

theorem bilD_eq (Ψ : 𝓢(V, ℂ)) (B : V →L[ℝ] X →L[ℝ] V) (m : ℕ) (v : V) (x : X) :
    bilD Ψ B m v x = (iteratedFDeriv ℝ m Ψ (B v x)).compContinuousLinearMap fun _ => B v :=
  (B v).iteratedFDeriv_comp_right (Ψ.smooth ⊤) x (natCast_le_infty m)

theorem continuous_compCLM (m : ℕ) :
    Continuous (fun fg : ContinuousMultilinearMap ℝ (fun _ : Fin m => V) ℂ × (Fin m → X →L[ℝ] V) =>
      fg.1.compContinuousLinearMap fg.2) :=
  continuous_iff_continuousAt.2 fun fg =>
    (ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap fg).hasFDerivAt.continuousAt

theorem continuous_bilD_left (Ψ : 𝓢(V, ℂ)) (B : V →L[ℝ] X →L[ℝ] V) (m : ℕ) (x : X) :
    Continuous fun v => bilD Ψ B m v x := by
  have h1 : Continuous fun v => B v x := B.continuous.clm_apply continuous_const
  have h2 : Continuous fun v => iteratedFDeriv ℝ m Ψ (B v x) :=
    ((Ψ.smooth ⊤).continuous_iteratedFDeriv (natCast_le_infty m)).comp h1
  have h3 : Continuous fun v => (fun _ : Fin m => B v) := continuous_pi fun _ => B.continuous
  have h := (continuous_compCLM (V := V) (X := X) m).comp (h2.prodMk h3)
  refine h.congr fun v => ?_
  exact (bilD_eq Ψ B m v x).symm

theorem continuous_fderiv_bil_left (Ψ : 𝓢(V, ℂ)) (B : V →L[ℝ] X →L[ℝ] V) (x : X) :
    Continuous fun v => fderiv ℝ (fun x => Ψ (B v x)) x := by
  have h1 : Continuous fun v => B v x := B.continuous.clm_apply continuous_const
  have h2 : Continuous fun v => fderiv ℝ Ψ (B v x) :=
    ((Ψ.smooth ⊤).continuous_fderiv infty_ne_zero).comp h1
  have h := h2.clm_comp B.continuous
  refine h.congr fun v => ?_
  have hd : HasFDerivAt (fun x => Ψ (B v x)) ((fderiv ℝ Ψ (B v x)).comp (B v)) x :=
    (((Ψ.smooth ⊤).differentiable infty_ne_zero) (B v x)).hasFDerivAt.comp x (B v).hasFDerivAt
  exact hd.fderiv.symm

theorem exists_bound_bilD (Ψ : 𝓢(V, ℂ)) (B : V →L[ℝ] X →L[ℝ] V) {U : Set X} {c : ℝ} (hc : 0 < c)
    (hB : ∀ x ∈ U, ∀ v, c * ‖v‖ ≤ ‖B v x‖) (m k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ∀ v, ‖bilD Ψ B m v x‖ ≤ C * ((1 + ‖v‖) ^ k)⁻¹ := by
  set S : ℝ := 2 ^ (k + m) *
    (Finset.Iic (k + m, m)).sup (fun p : ℕ × ℕ => SchwartzMap.seminorm ℝ p.1 p.2) Ψ with hSdef
  have hS : 0 ≤ S := mul_nonneg (by positivity) (apply_nonneg _ _)
  set c' := min 1 c
  have hc' : 0 < c' := lt_min one_pos hc
  refine ⟨S * ‖B‖ ^ m / c' ^ (k + m), by positivity, fun x hx v => ?_⟩
  have hp : 0 < 1 + ‖v‖ := by positivity
  have hq : c' * (1 + ‖v‖) ≤ 1 + ‖B v x‖ := by
    have h0 := hB x hx v
    have h1 : c' ≤ 1 := min_le_left _ _
    have h2 : c' ≤ c := min_le_right _ _
    nlinarith [norm_nonneg v]
  have hSch : (1 + ‖B v x‖) ^ (k + m) * ‖iteratedFDeriv ℝ m Ψ (B v x)‖ ≤ S :=
    SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k + m, m)) le_rfl le_rfl Ψ (B v x)
  have hBv : ‖B v‖ ≤ ‖B‖ * (1 + ‖v‖) :=
    (B.le_opNorm v).trans (mul_le_mul_of_nonneg_left (by linarith [norm_nonneg v]) (norm_nonneg _))
  have hcomp : ‖bilD Ψ B m v x‖ ≤ ‖iteratedFDeriv ℝ m Ψ (B v x)‖ * ‖B v‖ ^ m := by
    rw [bilD_eq]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp [Finset.prod_const]
  have hI : ‖iteratedFDeriv ℝ m Ψ (B v x)‖ ≤ S / (c' * (1 + ‖v‖)) ^ (k + m) := by
    rw [le_div_iff₀ (by positivity)]
    calc ‖iteratedFDeriv ℝ m Ψ (B v x)‖ * (c' * (1 + ‖v‖)) ^ (k + m)
        ≤ ‖iteratedFDeriv ℝ m Ψ (B v x)‖ * (1 + ‖B v x‖) ^ (k + m) := by gcongr
      _ ≤ S := by linarith [hSch]
  have hp' := hp.ne'
  have hc'' := hc'.ne'
  calc ‖bilD Ψ B m v x‖ ≤ ‖iteratedFDeriv ℝ m Ψ (B v x)‖ * ‖B v‖ ^ m := hcomp
    _ ≤ S / (c' * (1 + ‖v‖)) ^ (k + m) * (‖B‖ * (1 + ‖v‖)) ^ m := by gcongr
    _ = S * ‖B‖ ^ m / c' ^ (k + m) * ((1 + ‖v‖) ^ k)⁻¹ := by
        rw [mul_pow, mul_pow, pow_add, pow_add]
        field_simp

section Main

variable (Ψ : 𝓢(V, ℂ)) (B : V →L[ℝ] X →L[ℝ] V) {U : Set X} (hU : IsOpen U) {c : ℝ} (hc : 0 < c)
    (hB : ∀ x ∈ U, ∀ v, c * ‖v‖ ≤ ‖B v x‖)
    {κ : α → ℂ} {w : α → V} (hκ : AEStronglyMeasurable κ μ) (hw : AEStronglyMeasurable w μ)
    {k : ℕ} (hint : Integrable (fun a => ‖κ a‖ * ((1 + ‖w a‖) ^ k)⁻¹) μ)

include hc hB hκ hw hint in
theorem integrable_schwartz_bilin {x : X} (hx : x ∈ U) :
    Integrable (fun a => κ a * Ψ (B (w a) x)) μ := by
  obtain ⟨C, -, hC⟩ := exists_bound_bilD Ψ B hc hB 0 k
  have hm : AEStronglyMeasurable (fun a => κ a * Ψ (B (w a) x)) μ :=
    hκ.mul ((Ψ.continuous.comp (B.continuous.clm_apply continuous_const)).comp_aestronglyMeasurable hw)
  refine (hint.const_mul C).mono' hm (ae_of_all _ fun a => ?_)
  have h := hC x hx (w a)
  rw [bilD, norm_iteratedFDeriv_zero] at h
  rw [norm_mul]
  calc ‖κ a‖ * ‖Ψ (B (w a) x)‖ ≤ ‖κ a‖ * (C * ((1 + ‖w a‖) ^ k)⁻¹) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = C * (‖κ a‖ * ((1 + ‖w a‖) ^ k)⁻¹) := by ring

include hU hc hB hκ hw hint in
theorem hasFDerivAt_integral_schwartz_bilin {x : X} (hx : x ∈ U) :
    HasFDerivAt (fun x => ∫ a, κ a * Ψ (B (w a) x) ∂μ)
      (∫ a, κ a • fderiv ℝ (fun x => Ψ (B (w a) x)) x ∂μ) x := by
  obtain ⟨C, -, hC⟩ := exists_bound_bilD Ψ B hc hB 1 k
  have hbd : ∀ y ∈ U, ∀ a, ‖κ a • fderiv ℝ (fun x => Ψ (B (w a) x)) y‖ ≤
      C * (‖κ a‖ * ((1 + ‖w a‖) ^ k)⁻¹) := by
    intro y hy a
    have h := hC y hy (w a)
    rw [bilD, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero] at h
    rw [norm_smul]
    calc ‖κ a‖ * ‖fderiv ℝ (fun x => Ψ (B (w a) x)) y‖ ≤ ‖κ a‖ * (C * ((1 + ‖w a‖) ^ k)⁻¹) :=
          mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ = C * (‖κ a‖ * ((1 + ‖w a‖) ^ k)⁻¹) := by ring
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x a => κ a * Ψ (B (w a) x))
    (F' := fun x a => κ a • fderiv ℝ (fun x => Ψ (B (w a) x)) x) (hU.mem_nhds hx) ?_
    (integrable_schwartz_bilin Ψ B hc hB hκ hw hint hx) ?_ ?_ (hint.const_mul C) ?_
  · exact Filter.Eventually.of_forall fun y =>
      hκ.mul ((Ψ.continuous.comp (B.continuous.clm_apply continuous_const)).comp_aestronglyMeasurable hw)
  · exact hκ.smul ((continuous_fderiv_bil_left Ψ B x).comp_aestronglyMeasurable hw)
  · exact ae_of_all _ fun a y hy => hbd y hy a
  · refine ae_of_all _ fun a y _ => ?_
    exact (((contDiff_bil Ψ B (w a)).differentiable infty_ne_zero) y).hasFDerivAt.const_mul (κ a)

include hU hc hB hκ hw hint in
theorem contDiffOn_integral_schwartz_bilin :
    ContDiffOn ℝ ∞ (fun x => ∫ a, κ a * Ψ (B (w a) x) ∂μ) U := by
  classical
  choose C hC0 hC using fun m => exists_bound_bilD Ψ B hc hB m k
  have hmeas : ∀ m x, AEStronglyMeasurable (fun a => κ a • bilD Ψ B m (w a) x) μ := fun m x =>
    hκ.smul ((continuous_bilD_left Ψ B m x).comp_aestronglyMeasurable hw)
  have hbd : ∀ m, ∀ x ∈ U, ∀ a, ‖κ a • bilD Ψ B m (w a) x‖ ≤
      C m * (‖κ a‖ * ((1 + ‖w a‖) ^ k)⁻¹) := by
    intro m x hx a
    rw [norm_smul]
    calc ‖κ a‖ * ‖bilD Ψ B m (w a) x‖ ≤ ‖κ a‖ * (C m * ((1 + ‖w a‖) ^ k)⁻¹) :=
          mul_le_mul_of_nonneg_left (hC m x hx (w a)) (norm_nonneg _)
      _ = C m * (‖κ a‖ * ((1 + ‖w a‖) ^ k)⁻¹) := by ring
  have hint' : ∀ m, ∀ x ∈ U, Integrable (fun a => κ a • bilD Ψ B m (w a) x) μ := fun m x hx =>
    (hint.const_mul (C m)).mono' (hmeas m x) (ae_of_all _ (hbd m x hx))
  let p : X → FormalMultilinearSeries ℝ X ℂ := fun x m => ∫ a, κ a • bilD Ψ B m (w a) x ∂μ
  have hTay : HasFTaylorSeriesUpToOn ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => ∫ a, κ a * Ψ (B (w a) x) ∂μ) p U := by
    refine ⟨fun x hx => ?_, fun m _ x hx => ?_, fun m _ => ?_⟩
    · show (∫ a, κ a • bilD Ψ B 0 (w a) x ∂μ) 0 = _
      rw [ContinuousMultilinearMap.integral_apply (hint' 0 x hx)]
      simp [bilD]
    · let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => X) ℂ
      have hL : (p x m.succ).curryLeft = ∫ a, L (κ a • bilD Ψ B (m + 1) (w a) x) ∂μ :=
        (L.toContinuousLinearEquiv.integral_comp_comm (μ := μ)
          (fun a => κ a • bilD Ψ B (m + 1) (w a) x)).symm
      rw [hL]
      show HasFDerivWithinAt (fun y => ∫ a, κ a • bilD Ψ B m (w a) y ∂μ) _ U x
      refine (hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F := fun y a => κ a • bilD Ψ B m (w a) y)
        (F' := fun y a => L (κ a • bilD Ψ B (m + 1) (w a) y)) (hU.mem_nhds hx)
        (Filter.Eventually.of_forall fun y => hmeas m y) (hint' m x hx)
        (L.continuous.comp_aestronglyMeasurable (hmeas (m + 1) x)) ?_
        (hint.const_mul (C (m + 1))) ?_).hasFDerivWithinAt
      · exact ae_of_all _ fun a y hy => by rw [L.norm_map]; exact hbd (m + 1) y hy a
      · refine ae_of_all _ fun a y _ => ?_
        have h := ((contDiff_bil Ψ B (w a)).ftaylorSeries).fderiv m (natCast_lt_infty m) y
        have h2 := h.const_smul (κ a)
        have e : L (κ a • bilD Ψ B (m + 1) (w a) y) =
            κ a • (ftaylorSeries ℝ (fun x => Ψ (B (w a) x)) y m.succ).curryLeft := by
          ext v u
          simp [L, bilD, ftaylorSeries]
        rw [e]
        exact h2
    · exact continuousOn_of_dominated (fun x _ => hmeas m x) (fun x hx => ae_of_all _ (hbd m x hx))
        (hint.const_mul (C m)) (ae_of_all _ fun a => by
          have hc1 : Continuous fun y => bilD Ψ B m (w a) y :=
            (contDiff_bil Ψ B (w a)).continuous_iteratedFDeriv (natCast_le_infty m)
          exact (hc1.const_smul (κ a)).continuousOn)
  exact hTay.contDiffOn

end Main

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
end
end

noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap ContDiff Topology
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

set_option linter.unusedSectionVars false

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem norm_vecMul_le (w : Vr F) (x : UpperTheory.V.TR.Lie F 2) : ‖w ᵥ* Matrix.of x‖ ≤ 2 * ‖w‖ * ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.of_apply]
  have h0 : ‖x 0 j‖ ≤ ‖x‖ := (norm_le_pi_norm (x 0) j).trans (norm_le_pi_norm x 0)
  have h1 : ‖x 1 j‖ ≤ ‖x‖ := (norm_le_pi_norm (x 1) j).trans (norm_le_pi_norm x 1)
  calc ‖w 0 * x 0 j + w 1 * x 1 j‖ ≤ ‖w 0‖ * ‖x 0 j‖ + ‖w 1‖ * ‖x 1 j‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ ‖w‖ * ‖x‖ + ‖w‖ * ‖x‖ :=
        add_le_add (mul_le_mul (norm_le_pi_norm w 0) h0 (norm_nonneg _) (norm_nonneg _))
          (mul_le_mul (norm_le_pi_norm w 1) h1 (norm_nonneg _) (norm_nonneg _))
    _ = 2 * ‖w‖ * ‖x‖ := by ring

theorem norm_mulVec_le (w : Vr F) (x : UpperTheory.V.TR.Lie F 2) : ‖Matrix.of x *ᵥ w‖ ≤ 2 * ‖w‖ * ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply]
  have h0 : ‖x i 0‖ ≤ ‖x‖ := (norm_le_pi_norm (x i) 0).trans (norm_le_pi_norm x i)
  have h1 : ‖x i 1‖ ≤ ‖x‖ := (norm_le_pi_norm (x i) 1).trans (norm_le_pi_norm x i)
  calc ‖x i 0 * w 0 + x i 1 * w 1‖ ≤ ‖x i 0‖ * ‖w 0‖ + ‖x i 1‖ * ‖w 1‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ ‖x‖ * ‖w‖ + ‖x‖ * ‖w‖ :=
        add_le_add (mul_le_mul h0 (norm_le_pi_norm w 0) (norm_nonneg _) (norm_nonneg _))
          (mul_le_mul h1 (norm_le_pi_norm w 1) (norm_nonneg _) (norm_nonneg _))
    _ = 2 * ‖w‖ * ‖x‖ := by ring

theorem half_norm_le_norm_left_bilinear {x : UpperTheory.V.TR.Lie F 2} (hx : x ∈ Metric.ball (UpperTheory.V.TR.oneL F 2) (1 / 4)) (v : Vr F) :
    (1 / 2 : ℝ) * ‖v‖ ≤ ‖B1 v x‖ := by
  have hx' : ‖x - UpperTheory.V.TR.oneL F 2‖ < 1 / 4 := by rwa [Metric.mem_ball, dist_eq_norm] at hx
  set r := v ᵥ* Matrix.of (x - UpperTheory.V.TR.oneL F 2)
  have e : B1 v x = v + r := by
    rw [left_bilinear_apply]
    have : Matrix.of (x - UpperTheory.V.TR.oneL F 2) = Matrix.of x - 1 := rfl
    simp only [r, this, Matrix.vecMul_sub, Matrix.vecMul_one]
    abel
  have h2 : ‖r‖ ≤ 2 * ‖v‖ * ‖x - UpperTheory.V.TR.oneL F 2‖ := norm_vecMul_le v _
  have h3 : ‖v‖ ≤ ‖v + r‖ + ‖r‖ := by
    have := norm_sub_le (v + r) r
    rwa [add_sub_cancel_right] at this
  have h4 : ‖v‖ * ‖x - UpperTheory.V.TR.oneL F 2‖ ≤ ‖v‖ * (1 / 4) := mul_le_mul_of_nonneg_left hx'.le (norm_nonneg v)
  rw [e]
  nlinarith [norm_nonneg v]

theorem half_norm_le_norm_right_bilinear {x : UpperTheory.V.TR.Lie F 2} (hx : x ∈ Metric.ball (UpperTheory.V.TR.oneL F 2) (1 / 4)) (v : Vr F) :
    (1 / 2 : ℝ) * ‖v‖ ≤ ‖B2 v x‖ := by
  have hx' : ‖x - UpperTheory.V.TR.oneL F 2‖ < 1 / 4 := by rwa [Metric.mem_ball, dist_eq_norm] at hx
  set r := Matrix.of (x - UpperTheory.V.TR.oneL F 2) *ᵥ v
  have e : B2 v x = v + r := by
    rw [right_bilinear_apply]
    have : Matrix.of (x - UpperTheory.V.TR.oneL F 2) = Matrix.of x - 1 := rfl
    simp only [r, this, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  have h2 : ‖r‖ ≤ 2 * ‖v‖ * ‖x - UpperTheory.V.TR.oneL F 2‖ := norm_mulVec_le v _
  have h3 : ‖v‖ ≤ ‖v + r‖ + ‖r‖ := by
    have := norm_sub_le (v + r) r
    rwa [add_sub_cancel_right] at this
  have h4 : ‖v‖ * ‖x - UpperTheory.V.TR.oneL F 2‖ ≤ ‖v‖ * (1 / 4) := mul_le_mul_of_nonneg_left hx'.le (norm_nonneg v)
  rw [e]
  nlinarith [norm_nonneg v]

theorem invL_val (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    invL (UpperTheory.V.TR.toL y.val) = UpperTheory.V.TR.toL (y⁻¹).val := by
  simp only [invL, UpperTheory.V.TR.toL, Equiv.apply_symm_apply]
  rw [Matrix.coe_units_inv]

theorem invL_one : invL (UpperTheory.V.TR.oneL F 2) = UpperTheory.V.TR.oneL F 2 := by
  simp [invL, UpperTheory.V.TR.oneL, UpperTheory.V.TR.toL, show Matrix.of (Matrix.row (1 : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F))) = 1 from rfl]

theorem contDiffAt_invL : ContDiffAt ℝ ∞ (invL (F := F)) (UpperTheory.V.TR.oneL F 2) := by
  have hdet : ContDiffAt ℝ ∞ (fun x : UpperTheory.V.TR.Lie F 2 => Ring.inverse (Matrix.of x).det)
      (UpperTheory.V.TR.oneL F 2) := by
    have hx : (Matrix.of (UpperTheory.V.TR.oneL F 2)).det = ((1 : (UpperTheory.V.TR.Rinf F)ˣ) : UpperTheory.V.TR.Rinf F) := by
      simp [UpperTheory.V.TR.oneL, UpperTheory.V.TR.toL, show Matrix.of (Matrix.row (1 : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F))) = 1 from rfl]
    refine ContDiffAt.comp (g := Ring.inverse) (UpperTheory.V.TR.oneL F 2) ?_
      (UpperTheory.V.TR.contDiff_det (E := F) (a := 2)).contDiffAt
    rw [hx]
    exact contDiffAt_ringInverse (𝕜 := ℝ) (1 : (UpperTheory.V.TR.Rinf F)ˣ)
  have e : invL (F := F) = fun x => fun i j => Ring.inverse (Matrix.of x).det * Matrix.adjugate (Matrix.of x) i j := by
    funext x i j
    simp [invL, Matrix.inv_def, UpperTheory.V.TR.toL]
  rw [e]
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => hdet.mul ?_
  have hp : ∀ a b : Fin 2, ContDiff ℝ ∞ fun x : UpperTheory.V.TR.Lie F 2 => x a b := fun a b =>
    by
      simpa only [Function.comp_def] using
        (contDiff_apply ℝ (fun _ : Fin 2 => UpperTheory.V.TR.Rinf F) b).comp
          (contDiff_apply ℝ (fun _ : Fin 2 => Fin 2 → UpperTheory.V.TR.Rinf F) a)
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.adjugate_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta,
      Fin.mk_one] <;>
    first
    | exact (hp _ _).contDiffAt
    | exact (hp _ _).neg.contDiffAt

theorem dl_eq (g : GA F 2) (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F))
    (hy : ∀ v, 0 < (Matrix.det (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F))) v) :
    absD (g * UpperTheory.V.TR.infGL F 2 y) = dl g (UpperTheory.V.TR.toL y.val) := by
  rw [absD_mul, absD_infGL, dl]
  congr 1
  exact Finset.prod_congr rfl fun v _ => abs_of_pos (hy v)

theorem contDiff_dl (g : GA F 2) : ContDiff ℝ ∞ (dl (F := F) g) :=
  contDiff_const.mul (contDiff_prod fun v _ =>
    (contDiff_apply ℝ (fun _ => ℝ) v).comp (UpperTheory.V.TR.contDiff_det (E := F) (a := 2)))

theorem dl_one (g : GA F 2) : dl g (UpperTheory.V.TR.oneL F 2) = absD g := by
  simp [dl, UpperTheory.V.TR.oneL, UpperTheory.V.TR.toL, show Matrix.of (Matrix.row (1 : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F))) = 1 from rfl]

theorem eis_decomp (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) {C : ℂ}
    (hC : ∀ h : GA F 2, thetaS (Phi c) h = C * ((absD h)⁻¹ : ℝ) * thetaT (PhiH c) h)
    (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F))
    (h1 : Integrable (fun q => kap1 χ c g q * archS F (B1 (w1 g q) (UpperTheory.V.TR.toL y.val)))
      (μS F {t | 1 ≤ (t : ℝ)}))
    (h2 : Integrable (fun q => kap2 χ c g q * archS F (B2 (w2 g q) (UpperTheory.V.TR.toL (y⁻¹).val)))
      (μS F {t | (t : ℝ) < 1})) :
    Eis χ (Phi c) (g * UpperTheory.V.TR.infGL F 2 y) =
      ((absD (g * UpperTheory.V.TR.infGL F 2 y) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) *
          ∫ q, kap1 χ c g q * archS F (B1 (w1 g q) (UpperTheory.V.TR.toL y.val)) ∂μS F {t | 1 ≤ (t : ℝ)} +
        C * (((absD (g * UpperTheory.V.TR.infGL F 2 y))⁻¹ : ℝ) : ℂ) *
          ((absD (g * UpperTheory.V.TR.infGL F 2 y) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) *
          ∫ q, kap2 χ c g q * archS F (B2 (w2 g q) (UpperTheory.V.TR.toL (y⁻¹).val)) ∂μS F {t | (t : ℝ) < 1} := by
  set g' := g * UpperTheory.V.TR.infGL F 2 y
  set Dc : ℂ := ((absD g' ^ ((1 : ℝ) / 2) : ℝ) : ℂ)
  set Ac : ℂ := (((absD g')⁻¹ : ℝ) : ℂ)
  set S1 : Set {r : ℝ // 0 < r} := {t | 1 ≤ (t : ℝ)}
  set S2 : Set {r : ℝ // 0 < r} := {t | (t : ℝ) < 1}
  have hS2 : S2 = S1ᶜ := by
    ext t
    simp [S1, S2]
  obtain ⟨hi1, he1⟩ := integral_iter_eq S1 measurableSet_ge_one h1
  obtain ⟨hi2, he2⟩ := integral_iter_eq S2 measurableSet_lt_one h2
  set G : {r : ℝ // 0 < r} → ℂ := fun t => ∫ u in normOneFundamentalDomain F, eisInt χ (Phi c) g' t u ∂normOneMeasure F
  have eG1 : G = fun t => (∫ u in normOneFundamentalDomain F, ∑' ξ : Xi F,
      kap1 χ c g ((t, u), ξ) * archS F (B1 (w1 g ((t, u), ξ)) (UpperTheory.V.TR.toL y.val)) ∂normOneMeasure F) * Dc := by
    funext t
    simp only [G, g', eisInt_row]
    exact integral_mul_const _ _
  have eG2 : G = fun t => C * Ac * Dc * ∫ u in normOneFundamentalDomain F, ∑' ξ : Xi F,
      kap2 χ c g ((t, u), ξ) * archS F (B2 (w2 g ((t, u), ξ)) (UpperTheory.V.TR.toL (y⁻¹).val)) ∂normOneMeasure F := by
    funext t
    simp only [G, g', eisInt_col χ c g hC]
    exact integral_const_mul _ _
  have hG1 : IntegrableOn G S1 posRealMeasure := by
    rw [eG1]
    exact hi1.mul_const _
  have hG2 : IntegrableOn G S1ᶜ posRealMeasure := by
    rw [eG2, ← hS2]
    exact hi2.const_mul _
  have hG : Integrable G posRealMeasure := by
    have := hG1.union hG2
    rwa [Set.union_compl_self, integrableOn_univ] at this
  change ∫ t, G t ∂posRealMeasure = _
  rw [← integral_add_compl measurableSet_ge_one hG]
  congr 1
  · rw [eG1, integral_mul_const, he1, mul_comm]
  · rw [eG2, ← hS2, integral_const_mul, he2]

theorem contDiffAt_chart_one (hP : SPois) (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (H : Hyp χ c)
    (g : GA F 2) : ContDiffAt ℝ ∞ (UpperTheory.V.TR.chart (Eis χ (Phi c)) g) (UpperTheory.V.TR.oneL F 2) := by
  obtain ⟨C, hC⟩ := hP F χ c H
  have hC' : ∀ h : GA F 2, thetaS (Phi c) h = C * ((absD h)⁻¹ : ℝ) * thetaT (PhiH c) h :=
    fun h => (hC h).2.2
  set U : Set (UpperTheory.V.TR.Lie F 2) := Metric.ball (UpperTheory.V.TR.oneL F 2) (1 / 4)
  have hU : IsOpen U := Metric.isOpen_ball
  have h1U : UpperTheory.V.TR.oneL F 2 ∈ U := Metric.mem_ball_self (by norm_num)
  have m1 := aestronglyMeasurable_first_kernel χ c g {t | 1 ≤ (t : ℝ)}
  have mw1 := aestronglyMeasurable_row_weight (F := F) g {t | 1 ≤ (t : ℝ)}
  have m2 := aestronglyMeasurable_second_kernel χ c g {t | (t : ℝ) < 1}
  have mw2 := aestronglyMeasurable_column_weight (F := F) g {t | (t : ℝ) < 1}
  obtain ⟨k1, hk1⟩ := hint1 H g m1 mw1
  obtain ⟨k2, hk2⟩ := hint2 H g m2 mw2
  have hc : (0 : ℝ) < 1 / 2 := by norm_num
  set I1 : UpperTheory.V.TR.Lie F 2 → ℂ := fun x =>
    ∫ q, kap1 χ c g q * archS F (B1 (w1 g q) x) ∂μS F {t | 1 ≤ (t : ℝ)}
  set I2 : UpperTheory.V.TR.Lie F 2 → ℂ := fun z =>
    ∫ q, kap2 χ c g q * archS F (B2 (w2 g q) z) ∂μS F {t | (t : ℝ) < 1}
  have hI1 : ContDiffOn ℝ ∞ I1 U :=
    contDiffOn_integral_schwartz_bilin (archS F) B1 hU hc (fun x hx v => half_norm_le_norm_left_bilinear hx v) m1 mw1 hk1
  have hI2 : ContDiffOn ℝ ∞ I2 U :=
    contDiffOn_integral_schwartz_bilin (archS F) B2 hU hc (fun x hx v => half_norm_le_norm_right_bilinear hx v) m2 mw2 hk2
  have hI1a : ContDiffAt ℝ ∞ I1 (UpperTheory.V.TR.oneL F 2) := hI1.contDiffAt (hU.mem_nhds h1U)
  have hI2a : ContDiffAt ℝ ∞ (fun x => I2 (invL x)) (UpperTheory.V.TR.oneL F 2) :=
    by
      refine ContDiffAt.comp (g := I2) (UpperTheory.V.TR.oneL F 2) ?_ contDiffAt_invL
      rw [invL_one]
      exact hI2.contDiffAt (hU.mem_nhds h1U)
  have hdl := (contDiff_dl (F := F) g).contDiffAt (x := UpperTheory.V.TR.oneL F 2)
  have hdl0 : dl g (UpperTheory.V.TR.oneL F 2) ≠ 0 := by rw [dl_one]; exact (absD_pos g).ne'
  have hD : ContDiffAt ℝ ∞ (fun x => ((dl g x ^ ((1 : ℝ) / 2) : ℝ) : ℂ)) (UpperTheory.V.TR.oneL F 2) :=
    (Complex.ofRealCLM.contDiff.contDiffAt).comp _ (hdl.rpow_const_of_ne hdl0)
  have hA : ContDiffAt ℝ ∞ (fun x => (((dl g x)⁻¹ : ℝ) : ℂ)) (UpperTheory.V.TR.oneL F 2) :=
    (Complex.ofRealCLM.contDiff.contDiffAt).comp _ (hdl.inv hdl0)
  have hΦ : ContDiffAt ℝ ∞ (fun x => ((dl g x ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * I1 x +
      C * (((dl g x)⁻¹ : ℝ) : ℂ) * ((dl g x ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * I2 (invL x)) (UpperTheory.V.TR.oneL F 2) :=
    (hD.mul hI1a).add (((contDiffAt_const.mul hA).mul hD).mul hI2a)
  refine hΦ.congr_of_eventuallyEq ?_
  have hinv : ∀ᶠ x in 𝓝 (UpperTheory.V.TR.oneL F 2), invL x ∈ U :=
    contDiffAt_invL.continuousAt.preimage_mem_nhds (by rw [invL_one]; exact hU.mem_nhds h1U)
  have hunit : ∀ᶠ x in 𝓝 (UpperTheory.V.TR.oneL F 2), x ∈ UpperTheory.V.TR.invSet F 2 :=
    UpperTheory.V.TR.isOpen_invSet.mem_nhds (by simp [UpperTheory.V.TR.invSet, UpperTheory.V.TR.oneL, UpperTheory.V.TR.toL, show Matrix.of (Matrix.row (1 : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F))) = 1 from rfl])
  have hdet : ∀ᶠ x in 𝓝 (UpperTheory.V.TR.oneL F 2), ∀ v, 0 < (Matrix.det (Matrix.of x)) v := by
    refine Filter.eventually_all.2 fun v => ?_
    have hcont : ContinuousAt (fun x : UpperTheory.V.TR.Lie F 2 => (Matrix.det (Matrix.of x)) v) (UpperTheory.V.TR.oneL F 2) :=
      ((continuous_apply v).comp (UpperTheory.V.TR.contDiff_det (E := F) (a := 2)).continuous).continuousAt
    exact continuousAt_const.eventually_lt hcont (by simp [UpperTheory.V.TR.oneL, UpperTheory.V.TR.toL, show Matrix.of (Matrix.row (1 : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F))) = 1 from rfl])
  filter_upwards [hU.mem_nhds h1U, hinv, hunit, hdet] with x hxU hxi hxu hxd
  set y : GL (Fin 2) (UpperTheory.V.TR.Rinf F) := (show IsUnit (Matrix.of x) from hxu).unit
  have hy : UpperTheory.V.TR.toL y.val = x := rfl
  have hyi : UpperTheory.V.TR.toL (y⁻¹).val = invL x := by rw [← invL_val, hy]
  have hyd : absD (g * UpperTheory.V.TR.infGL F 2 y) = dl g x := by
    rw [dl_eq g y hxd, hy]
  have i1 := integrable_schwartz_bilin (archS F) B1 hc (fun x hx v => half_norm_le_norm_left_bilinear hx v) m1 mw1 hk1 hxU
  have i2 := integrable_schwartz_bilin (archS F) B2 hc (fun x hx v => half_norm_le_norm_right_bilinear hx v) m2 mw2 hk2 hxi
  rw [← hy] at i1
  rw [← hyi] at i2
  rw [← hy, UpperTheory.V.TR.chart_val, eis_decomp χ c g hC' y i1 i2, hyd, hyi, hy]

theorem contDiffOn_of_contDiffAt_one {φ : GA F 2 → ℂ}
    (h : ∀ g, ContDiffAt ℝ ∞ (UpperTheory.V.TR.chart φ g) (UpperTheory.V.TR.oneL F 2))
    (g : GA F 2) : ContDiffOn ℝ ∞ (UpperTheory.V.TR.chart φ g) (UpperTheory.V.TR.invSet F 2) := by
  intro x hx
  set y : GL (Fin 2) (UpperTheory.V.TR.Rinf F) := (show IsUnit (Matrix.of x) from hx).unit
  have hy : UpperTheory.V.TR.toL y.val = x := rfl
  have e : UpperTheory.V.TR.chart φ g =
      UpperTheory.V.TR.chart φ (g * UpperTheory.V.TR.infGL F 2 y) ∘ UpperTheory.V.TR.lmul (UpperTheory.V.TR.toL (y⁻¹).val) := by
    rw [← UpperTheory.V.TR.chart_mul, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  rw [e]
  refine ContDiffAt.contDiffWithinAt ?_
  have h1 : UpperTheory.V.TR.lmul (UpperTheory.V.TR.toL (y⁻¹).val) x = UpperTheory.V.TR.oneL F 2 := by
    rw [← hy]
    change Matrix.of.symm (Matrix.of (UpperTheory.V.TR.toL (y⁻¹).val) * Matrix.of (UpperTheory.V.TR.toL y.val)) = _
    change Matrix.of.symm ((y⁻¹).val * y.val) = Matrix.of.symm 1
    simp
  refine ContDiffAt.comp x ?_
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) (UpperTheory.V.TR.lmul (UpperTheory.V.TR.toL (y⁻¹).val))).contDiffAt
  rw [h1]
  exact h _

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

namespace UpperTheory.HilbertEisensteinWeightOne

theorem smoothness_holds : SPois → SInt → SSmooth := by
  intro hP _ F _ _ _ χ c H g
  exact EisensteinSmoothness.contDiffOn_of_contDiffAt_one (fun g => EisensteinSmoothness.contDiffAt_chart_one hP χ c H g) g

end UpperTheory.HilbertEisensteinWeightOne
