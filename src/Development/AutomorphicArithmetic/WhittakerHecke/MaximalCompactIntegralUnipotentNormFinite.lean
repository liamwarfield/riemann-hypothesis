module

public import Development.AutomorphicArithmetic.WhittakerHecke.WhittakerFunctionContinuousBoundedEquivariant
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.MaximalCompactIntegralUnipotentNormFinite
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem row_nU (b : A ℚ) (g : G1 ℚ) (u : (A ℚ)ˣ) (j : Fin 2) :
    (gl (nU b * g) * dM u).val 1 j = (gl g * dM u).val 1 j := by
  rw [Units.val_mul, Units.val_mul, M.val_gl, M.val_gl, M.val_mul]
  simp [nU, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

private theorem row_mD (a u : (A ℚ)ˣ) (k : G1 ℚ) (j : Fin 2) :
    (gl (mD a * cD u k) * dM u).val 1 j = ((a⁻¹ * u : (A ℚ)ˣ) : A ℚ) * G.row k j := by
  have h : gl (mD a * cD u k) = gl (mD a) * gl (cD u k) := map_mul _ _ _
  rw [h, mul_assoc, M.gl_cD, Units.val_mul, Units.val_mul, M.val_gl, M.val_gl]
  simp [mD, dM, G.row, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc, Matrix.vecMul, dotProduct]

theorem UpperTheory.maximalCompact_integral_unipotent_norm_finite :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ → ∀ (M₀ : Meas ℚ), ∀ Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2), ∀ (t : ℝ) (u : IdeleGroup ℚ), u ∈ UU →
        (_root_.UpperTheory.ConvolutionTheory.R2.M.J0 M₀ fun g => ∫⁻ b in fundamentalSet ℚ, ‖Un.Uu φ Φ t u (nU b * g)‖ₑ ∂(adeleMeasure ℚ)) ≠ ⊤ := by
  intro E _ _ D ω φ hA M₀ Φ hΦ t u hu
  obtain ⟨B, hB⟩ := hA.bdd
  obtain ⟨hmp, hme⟩ := UpperTheory.measurePreserving_idele_scale_and_conj_on_maximalCompact M₀ t u hu
  obtain ⟨C, hC⟩ := UpperTheory.schwartzBruhat_row_lintegral_abs_pow_bounded Φ hΦ 2 (by norm_num)
  obtain ⟨-, hiy, -, hU⟩ := UpperTheory.realIdele_mul_abs_continuous_and_unit_abs_eq_one
  haveI := M₀.prob
  have hw : ∀ g : G1 ℚ, ∫⁻ b in fundamentalSet ℚ, ‖Un.Uu φ Φ t u (nU b * g)‖ₑ ∂(adeleMeasure ℚ) ≤
      ENNReal.ofReal B * ‖Φ fun j => (iy (Real.exp t) : A ℚ) * (gl g * dM u).val 1 j‖ₑ := by
    intro g
    refine (lintegral_mono (g := fun _ => ENNReal.ofReal B * ‖Φ fun j => (iy (Real.exp t) : A ℚ) * (gl g * dM u).val 1 j‖ₑ)
      fun b => ?_).trans ?_
    · simp only [Un.Uu, row_nU, enorm_mul]
      refine mul_le_mul_left ?_ _
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hB _)
    · rw [setLIntegral_const, adeleMeasure_fundamentalSet, mul_one]
  let F : IdeleGroup ℚ × G1 ℚ → ℝ≥0∞ := fun p =>
    ‖Φ fun j => ((p.1 : (A ℚ)ˣ) : A ℚ) * G.row p.2 j‖ₑ * ENNReal.ofReal (ab p.1 ^ (2 : ℝ))
  have hF : Measurable F := by
    have h1 : Continuous fun p : IdeleGroup ℚ × G1 ℚ => Φ fun j => ((p.1 : (A ℚ)ˣ) : A ℚ) * G.row p.2 j :=
      (continuous_of_mem_schwartzBruhatPi hΦ).comp (continuous_pi fun j =>
        (Units.continuous_val.comp continuous_fst).mul ((M.continuous_entry 1 j).comp continuous_snd))
    have h2 : Continuous fun p : IdeleGroup ℚ × G1 ℚ => ab p.1 ^ (2 : ℝ) :=
      (M.continuous_ab.comp continuous_fst).rpow_const fun _ => Or.inr (by norm_num)
    exact h1.measurable.enorm.mul h2.measurable.ennreal_ofReal
  have hI : ∫⁻ p, F p ∂M₀.ν ≤ C := by
    rw [Meas.ν, lintegral_prod_symm _ hF.aemeasurable]
    have hae : ∀ᵐ k ∂M₀.κ, k ∈ KK ℚ := by
      rw [ae_iff]
      exact M₀.supp
    refine (lintegral_mono_ae (g := fun _ => (C : ℝ≥0∞)) (hae.mono fun k hk => hC k hk)).trans ?_
    rw [lintegral_const, measure_univ, mul_one]
  unfold M.J0
  rw [← hmp.lintegral_comp_emb hme]
  have hK : ENNReal.ofReal B * ENNReal.ofReal ((Real.exp t)⁻¹ ^ 2) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hK (ENNReal.coe_ne_top (r := C))) ?_
  refine le_trans ?_ (mul_le_mul_right hI _)
  rw [← lintegral_const_mul _ hF]
  refine lintegral_mono fun p => ?_
  refine (mul_le_mul_right (hw _) _).trans (le_of_eq ?_)
  have e1 : (fun j => (iy (Real.exp t) : A ℚ) * (gl (mD (Un.aa t u p.1) * cD u p.2) * dM u).val 1 j) =
      fun j => ((p.1 : (A ℚ)ˣ) : A ℚ) * G.row p.2 j := by
    funext j
    rw [row_mD, ← mul_assoc, ← Units.val_mul]
    have : (iy (Real.exp t) * ((Un.aa t u p.1)⁻¹ * u) : (A ℚ)ˣ) = p.1 := by
      have h : ∀ x y z : (A ℚ)ˣ, x * ((x * y * z⁻¹)⁻¹ * y) = z := fun x y z => by
        rw [mul_left_comm, ← mul_assoc, mul_right_comm, mul_comm x y, mul_assoc _ y x, mul_comm y x, mul_inv, inv_inv,
          mul_right_comm, inv_mul_cancel, one_mul]
      exact h _ _ _
    rw [this]
  have e2 : M.wt (Un.aa t u p.1) = ENNReal.ofReal ((Real.exp t)⁻¹ ^ 2) * ENNReal.ofReal (ab p.1 ^ (2 : ℝ)) := by
    have h : ab (Un.aa t u p.1) = Real.exp t * (ab p.1)⁻¹ := by
      have h0 : ab (Un.aa t u p.1) = ab (iy (Real.exp t)) * ab u * ab (p.1⁻¹ : (A ℚ)ˣ) := by
        rw [← M.ab_mul, ← M.ab_mul]
        rfl
      rw [h0, hiy _ (Real.exp_ne_zero t), hU u hu, M.ab_inv, abs_of_pos (Real.exp_pos t), mul_one]
    rw [M.wt, h, ← ENNReal.ofReal_mul (by positivity), Real.rpow_two, mul_inv, inv_inv, mul_pow]
  simp only [e1, e2, F]
  ring
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.UnfoldedIntegrandMeasurableIntegrableOfReGtFour
section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.WhittakerLintegralAbsPowBoundedOnMaximalCompact
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.whittaker_lintegral_abs_pow_bounded_on_maximalCompact :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ → ∀ x : ℝ, 1 < x → ∃ C : ℝ≥0, ∀ k ∈ KK ℚ,
        ∫⁻ y : IdeleGroup ℚ, ‖Wo D φ (em E (aE y * gl k))‖ₑ * ENNReal.ofReal (ab y ^ x) ∂(ideleMeasure ℚ) ≤ C := by
  intro E _ _ D ω φ hA x hx
  have hemc : Continuous (em E) :=
    Continuous.units_map _ (Continuous.matrix_map continuous_id AdeleBaseChange.continuous_adeleMap)
  have hglc : Continuous (gl : G1 ℚ → GL (Fin 2) (A ℚ)) := Matrix.SpecialLinearGroup.continuous_toGL
  have hC : IsCompact ((fun k : G1 ℚ => em E (gl k)) '' KK ℚ) :=
    (UpperTheory.ConvolutionTheory.R2.M.kkCpt ℚ).2.image (hemc.comp hglc)
  obtain ⟨K, hKc, hK⟩ := hA.wdec _ hC
  obtain ⟨r, hr⟩ := exists_nat_gt x
  obtain ⟨B, hB⟩ := hK r
  have hI := UpperTheory.lintegral_idele_rat_polyDecay_mul_norm_rpow_lt_top K hKc x hx r hr
  refine ⟨(ENNReal.ofReal |B| * ∫⁻ y : IdeleGroup ℚ, (if (y : A ℚ).2 ∈ K then ENNReal.ofReal (((1 + |re (y : A ℚ)|) ^ r)⁻¹ * ab y ^ x) else 0) ∂(ideleMeasure ℚ)).toNNReal, fun k hk => ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.ne),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun y => ?_
  have hb := hB y (em E (gl k)) ⟨k, hk, rfl⟩
  rw [← map_mul] at hb
  have hab : 0 ≤ ab y ^ x := Real.rpow_nonneg (IdeleGroup.ideleModule ℚ y).2.le x
  by_cases hy : (y : A ℚ).2 ∈ K
  · rw [if_pos hy, ← ENNReal.ofReal_mul (abs_nonneg _), ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_mul (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right (hb.1.trans ?_) hab
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  · have h0 : Wo D φ (em E (aE y * gl k)) = 0 := by
      by_contra h
      exact hy (hb.2 h)
    rw [h0, enorm_zero, zero_mul]
    exact bot_le
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.MeasurableWhittakerIdeleDiagTorusMul
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem cont_aE {K : Type} [Field K] [NumberField K] : Continuous (aE : (A K)ˣ → GL (Fin 2) (A K)) := by
  refine Units.continuous_iff.2 ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
  · fin_cases i <;> fin_cases j
    exacts [Units.continuous_val, continuous_const, continuous_const, continuous_const]
  · fin_cases i <;> fin_cases j
    exacts [Units.continuous_coe_inv, continuous_const, continuous_const, continuous_const]

theorem UpperTheory.measurable_whittaker_idele_diagTorus_mul :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ →
        Measurable (fun p : IdeleGroup ℚ × G1 ℚ => Wo D φ (em E (aE p.1 * gl p.2))) := by
  intro E _ _ D ω φ h
  have hem : Continuous (em E) := Continuous.units_map _
    (continuous_matrix fun i j => AdeleBaseChange.continuous_adeleMap.comp (continuous_id.matrix_elem i j))
  have h1 : Continuous fun p : IdeleGroup ℚ × G1 ℚ => em E (aE p.1 * gl p.2) :=
    hem.comp ((cont_aE.comp continuous_fst).mul (M.continuous_gl.comp continuous_snd))
  have hn : Continuous (nE D) :=
    M.continuous_gl.comp (M.continuous_nU.comp
      ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 0)).add
        ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 1)).mul continuous_const)))
  have hψ : Continuous (ψ (F := ℚ)) := continuous_subtype_val.comp continuous_adelicChar
  have h2 : Continuous fun q : (IdeleGroup ℚ × G1 ℚ) × (Fin 2 → A ℚ) => φ (nE D q.2 * em E (aE q.1.1 * gl q.1.2)) * ψ (q.2 1) :=
    (h.cont.comp ((hn.comp continuous_snd).mul (h1.comp continuous_fst))).mul
      (hψ.comp ((continuous_apply 1).comp continuous_snd))
  have : BorelSpace ((IdeleGroup ℚ × G1 ℚ) × (Fin 2 → A ℚ)) := inferInstance
  exact (h2.measurable.stronglyMeasurable.integral_prod_right' (ν := (adeleMeasurePi ℚ).restrict (FS2 ℚ))).measurable
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.unfoldedIntegrand_measurable_integrable_of_re_gt_four :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω χ : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ → Unit1 ω → (∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) → ∀ (M₀ : Meas ℚ), ∀ Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2), ∀ s : ℂ, 4 < s.re →
        Measurable (Un.Hh D χ φ Φ s) ∧ Integrable (Un.Hh D χ φ Φ s) ((ideleMeasure ℚ).prod ((ideleMeasure ℚ).prod M₀.κ)) := by
  intro E _ _ D ω χ φ hA hU hχ M₀ Φ hΦ s hs
  haveI := M₀.prob
  have hχn : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1 := by
    intro a
    have h := congrArg (fun u : ℂˣ => ‖(u : ℂ)‖) (hχ a)
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, norm_pow, norm_mul, Units.val_one, norm_one, hU a, mul_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h
  have hχe : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ₑ = 1 := by
    intro a
    rw [← ofReal_norm, hχn a, ENNReal.ofReal_one]
  have hcn : ∀ (y : IdeleGroup ℚ) (w : ℂ), ‖((ab y : ℝ) : ℂ) ^ w‖ₑ = ENNReal.ofReal (ab y ^ w.re) := by
    intro y w
    rw [← ofReal_norm, Complex.norm_cpow_eq_rpow_re_of_pos (M.ab_pos y)]
  have hW := UpperTheory.measurable_whittaker_idele_diagTorus_mul E D ω φ hA
  have hχm : Measurable fun y : IdeleGroup ℚ => ((χ.1 y : ℂˣ) : ℂ) :=
    (Units.continuous_val.comp χ.2.1).measurable
  have habm : Measurable fun y : IdeleGroup ℚ => ab y := M.continuous_ab.measurable
  have hΦc : Continuous fun p : IdeleGroup ℚ × G1 ℚ => Φ fun j => ((p.1 : (A ℚ)ˣ) : A ℚ) * row p.2 j :=
    (continuous_of_mem_schwartzBruhatPi hΦ).comp (continuous_pi fun j =>
      (Units.continuous_val.comp continuous_fst).mul ((M.continuous_entry 1 j).comp continuous_snd))
  have hΦm := hΦc.measurable
  have hcp : ∀ w : ℂ, Measurable fun y : IdeleGroup ℚ => ((ab y : ℝ) : ℂ) ^ w := fun w =>
    (Complex.measurable_ofReal.comp habm).pow_const w
  have hrp : ∀ x : ℝ, Measurable fun y : IdeleGroup ℚ => ENNReal.ofReal (ab y ^ x) := fun x =>
    (habm.pow_const x).ennreal_ofReal
  have hm : Measurable (Un.Hh D χ φ Φ s) :=
    ((((hW.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).mul
      (hχm.comp measurable_fst)).mul ((hcp _).comp measurable_fst))).mul
      ((hΦm.comp measurable_snd).mul ((hcp _).comp (measurable_fst.comp measurable_snd)))
  refine ⟨hm, hm.aestronglyMeasurable, ?_⟩
  obtain ⟨C₁, hC₁⟩ := UpperTheory.whittaker_lintegral_abs_pow_bounded_on_maximalCompact E D ω φ hA (s.re - 1) (by linarith)
  obtain ⟨C₂, hC₂⟩ := UpperTheory.schwartzBruhat_row_lintegral_abs_pow_bounded Φ hΦ (2 * s.re) (by linarith)
  let Aa : IdeleGroup ℚ × G1 ℚ → ℝ≥0∞ := fun p =>
    ‖Wo D φ (em E (aE p.1 * gl p.2))‖ₑ * ENNReal.ofReal (ab p.1 ^ (s.re - 1))
  let Bb : IdeleGroup ℚ × G1 ℚ → ℝ≥0∞ := fun p =>
    ‖Φ fun j => ((p.1 : (A ℚ)ˣ) : A ℚ) * row p.2 j‖ₑ * ENNReal.ofReal (ab p.1 ^ (2 * s.re))
  have hAm : Measurable Aa := hW.enorm.mul ((hrp _).comp measurable_fst)
  have hBm : Measurable Bb := hΦm.enorm.mul ((hrp _).comp measurable_fst)
  have hnorm : ∀ q, ‖Un.Hh D χ φ Φ s q‖ₑ = Aa (q.1, q.2.2) * Bb q.2 := by
    intro q
    have e1 : (s - 1).re = s.re - 1 := by simp
    have e2 : (2 * s).re = 2 * s.re := by simp
    simp only [Un.Hh, enorm_mul, hχe, mul_one, hcn, e1, e2, Aa, Bb]
  have hFm : Measurable fun q : IdeleGroup ℚ × IdeleGroup ℚ × G1 ℚ => Aa (q.1, q.2.2) * Bb q.2 :=
    (hAm.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).mul (hBm.comp measurable_snd)
  have hae : ∀ᵐ k ∂M₀.κ, k ∈ KK ℚ := by
    rw [ae_iff]
    exact M₀.supp
  show ∫⁻ q, ‖Un.Hh D χ φ Φ s q‖ₑ ∂((ideleMeasure ℚ).prod ((ideleMeasure ℚ).prod M₀.κ)) < ⊤
  simp_rw [hnorm]
  rw [lintegral_prod_symm _ hFm.aemeasurable, lintegral_prod_symm _ hFm.lintegral_prod_left'.aemeasurable]
  refine lt_of_le_of_lt (lintegral_mono_ae (g := fun _ => (C₁ * C₂ : ℝ≥0∞)) (hae.mono fun k hk => ?_)) ?_
  · have h1 : ∀ z : IdeleGroup ℚ, ∫⁻ y : IdeleGroup ℚ, Aa (y, k) * Bb (z, k) ∂(ideleMeasure ℚ) ≤ C₁ * Bb (z, k) := by
      intro z
      have hAk : Measurable fun y : IdeleGroup ℚ => Aa (y, k) := hAm.comp measurable_prodMk_right
      rw [lintegral_mul_const _ hAk]
      exact mul_le_mul_left (hC₁ k hk) _
    refine (lintegral_mono h1).trans ?_
    have hBk : Measurable fun z : IdeleGroup ℚ => Bb (z, k) := hBm.comp measurable_prodMk_right
    rw [lintegral_const_mul _ hBk]
    exact mul_le_mul_right (hC₂ k hk) _
  · rw [lintegral_const, measure_univ, mul_one]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top
end
