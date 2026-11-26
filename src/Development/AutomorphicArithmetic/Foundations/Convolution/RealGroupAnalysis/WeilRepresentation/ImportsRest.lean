module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.UnfL

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsRest
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.RedDet
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.redDet :
    ∀ (F : Type) [Field F] [NumberField F], ∀ (g : G1 F) (γ : GL (Fin 2) F), ∀ b ∈ Reduction.adelicBorel (K := F) (n := 2), ∀ k : GL (Fin 2) (A F), AdelicGLn.diagonal F 2 γ * gl g = b * k → ∃ γ' : Matrix.SpecialLinearGroup (Fin 2) F, ∃ b' ∈ Reduction.adelicBorel (K := F) (n := 2), gl (ratS F γ' * g) = b' * k ∧ b'.val 0 0 = b.val 0 0 ∧ Reduction.adeleAbs (b'.val 1 1) = Reduction.adeleAbs (b.val 1 1) := by
  intro F _ _ g γ b hb k h
  set d : Fˣ := Matrix.GeneralLinearGroup.det γ with hd
  have hdet : γ.val.det = (d : F) := rfl
  set t : (A F)ˣ := (IdeleGroup.diagonal F d)⁻¹ with ht
  have htv : ((t : (A F)ˣ) : A F) = algebraMap F (A F) ((d⁻¹ : Fˣ) : F) := by
    simp [ht, IdeleGroup.diagonal, ← map_inv]
  let γ' : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![1, 0; 0, ((d⁻¹ : Fˣ) : F)] * γ.val, by
      rw [Matrix.det_mul, hdet, Matrix.det_fin_two_of]; simp⟩
  have hg : gl (ratS F γ') = dM t * AdelicGLn.diagonal F 2 γ := by
    refine Units.ext ?_
    rw [Units.val_mul, val_gl, val_ratS]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [γ', dM, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, htv, map_mul]
  obtain ⟨u, hu⟩ := Reduction.isUnit_apply_self_of_mem_adelicBorel hb 1
  have hlow : b.val 1 0 = 0 := Reduction.mem_adelicBorel.1 hb (by decide)
  refine ⟨γ', dM t * b, ?_, ?_, ?_, ?_⟩
  · refine mul_mem (Reduction.mem_adelicBorel.2 ?_) hb
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | (simp [dM]; done) | (simp at hij)
  · have hm : gl (ratS F γ' * g) = gl (ratS F γ') * gl g := map_mul _ _ _
    rw [hm, hg, mul_assoc, h, mul_assoc]
  · simp [dM, Matrix.mul_apply, Fin.sum_univ_two]
  · have e : (dM t * b).val 1 1 = ((t * u : (A F)ˣ) : A F) := by
      simp [dM, Matrix.mul_apply, Fin.sum_univ_two, hu]
    rw [e, ← hu, Reduction.adeleAbs_units, Reduction.adeleAbs_units]
    have := ab_mul t u
    have h1 : ab t = 1 := by rw [ht, ab_inv, ab_diag, inv_one]
    rw [h1, one_mul] at this
    exact this
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.red :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], St.Red F := by
  intro F _ _ _
  obtain ⟨t₀, ht₀, h⟩ := Reduction.exists_reduced (K := F)
  refine ⟨Real.sqrt t₀, Real.sqrt_pos.2 ht₀, fun g => ?_⟩
  obtain ⟨γ, b, hb, k, hk, he, hr⟩ := h 2 (gl g)
  obtain ⟨γ', b', hb', he', h0, h1⟩ := M.redDet F g γ b hb k he
  obtain ⟨x, a, k', hk', hg, ha, ha'⟩ := M.fromGL F (ratS F γ' * g) b' hb' k hk he'
  refine ⟨γ', x, a, k', hk', hg, ?_⟩
  have := hr 0 1 rfl
  rw [← h1, ← h0, ha', ← ha, Reduction.adeleAbs_units] at this
  change t₀ * (ab a)⁻¹ ≤ ab a at this
  have hp := M.ab_pos a
  rw [mul_inv_le_iff₀ hp] at this
  exact Real.sqrt_le_iff.2 ⟨hp.le, by rwa [pow_two]⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsMore
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.LintegralUnipotentQuotientCompDiagonalConj
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.lintegral_unipotent_quotient_comp_diagonal_conj :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (u : G1 F → ℝ≥0∞), Measurable u → (∀ b g, u (nU b * g) = u g) → ∀ t, (M.J0 M₀ fun g => u (cD t g)) = ENNReal.ofReal (ab t)⁻¹ * M.J0 M₀ u := by
  intro F _ _ M₀ u hu hN t
  obtain ⟨β, hβ⟩ := M.wtEx F
  have h1 := M.wtOne F β hβ
  have hcm : ∀ s : (A F)ˣ, Measurable (cD s : G1 F → G1 F) := fun s => (M.continuous_cD s).measurable
  have hβ' : Measurable fun g => β (cD t⁻¹ g) := hβ.1.comp (hcm _)
  have hu' : Measurable fun g => u (cD t g) := hu.comp (hcm _)
  have hN' : ∀ b g, u (cD t (nU b * g)) = u (cD t g) := by
    intro b g
    rw [M.cD_mul, M.cD_nU, hN]
  have hc : ∀ g, ∫⁻ b, β (cD t⁻¹ (nU b * g)) ∂(adeleMeasure F) = ENNReal.ofReal (ab t)⁻¹ := by
    intro g
    have hf : Measurable fun b : A F => β (nU b * cD t⁻¹ g) :=
      hβ.1.comp ((M.continuous_nU.mul continuous_const).measurable)
    have hs : Measurable fun x : A F => (t : IdeleGroup F) • x := by
      have : Continuous fun x : A F => (t : IdeleGroup F) • x := by
        simp only [Units.smul_def, smul_eq_mul]
        exact continuous_const.mul continuous_id
      exact this.measurable
    have e := lintegral_map (μ := adeleMeasure F) hf hs
    rw [map_smul_adeleMeasure, lintegral_smul_measure, h1] at e
    have e2 : ∀ b : A F, β (cD t⁻¹ (nU b * g)) = β (nU ((t : IdeleGroup F) • b) * cD t⁻¹ g) := by
      intro b
      rw [M.cD_mul, M.cD_nU, inv_inv, Units.smul_def, smul_eq_mul, mul_comm b]
    simp_rw [e2]
    rw [← e, smul_eq_mul, mul_one]
    rfl
  have a1 := M.wtA F M₀ β (fun g => u (cD t g)) 1 hβ.1 h1 hu' hN'
  have a2 := M.wtA F M₀ (fun g => β (cD t⁻¹ g)) u _ hβ' hc hu hN
  have a3 := (M.cdMeas F M₀ t).lintegral_comp
    (f := fun h => u h * β (cD t⁻¹ h)) (hu.mul hβ')
  have e3 : ∀ g, β (cD t⁻¹ (cD t g)) = β g := by
    intro g
    rw [M.cD_cD, inv_mul_cancel, M.cD_one]
  simp only [e3] at a3
  rw [one_mul] at a1
  rw [← a1, a3, a2]
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.inv :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], St.Inv F := by
  intro F _ _ _ M₀ u hu hN hi
  obtain ⟨ρ, -, hρ, hρ'⟩ := M.iwDens F M₀
  have hp : Measurable fun p : IdeleGroup F × G1 F => mD p.1 * p.2 :=
    ((M.continuous_mD.comp continuous_fst).mul continuous_snd).measurable
  have hi' : Integrable (fun p : IdeleGroup F × G1 F => u (mD p.1 * p.2)) ρ := (hρ' _).1.2 hi
  refine ⟨fun g₀ => ?_, fun t => ?_⟩
  · have hg : Measurable fun g => u (g * g₀) := hu.comp (measurable_mul_const g₀)
    obtain ⟨h1, h2⟩ := M.transfer (m := ρ) (n := ρ) (hg.comp hp) (hu.comp hp) fun φ hφ =>
      (hρ (fun g => φ (u (g * g₀))) (hφ.comp hg)).trans
        ((M.lintegral_unipotent_quotient_right_invariant F M₀ (fun g => φ (u g)) (hφ.comp hu) (fun b g => by simp only [hN]) g₀).trans
          (hρ (fun g => φ (u g)) (hφ.comp hu)).symm)
    exact ⟨(hρ' _).1.1 (h1.2 hi'), (hρ' _).2.symm.trans (h2.trans (hρ' _).2)⟩
  · have hg : Measurable fun g => u (cD t g) := hu.comp (M.continuous_cD t).measurable
    obtain ⟨h1, h2⟩ := M.transfer (m := ρ) (n := ENNReal.ofReal (ab t)⁻¹ • ρ) (hg.comp hp) (hu.comp hp) fun φ hφ => by
      rw [lintegral_smul_measure, smul_eq_mul]
      exact (hρ (fun g => φ (u (cD t g))) (hφ.comp hg)).trans
        ((M.lintegral_unipotent_quotient_comp_diagonal_conj F M₀ (fun g => φ (u g)) (hφ.comp hu) (fun b g => by simp only [hN]) t).trans
          (congrArg _ (hρ (fun g => φ (u g)) (hφ.comp hu)).symm))
    refine ⟨(hρ' _).1.1 (h1.2 (hi'.smul_measure ENNReal.ofReal_ne_top)), (hρ' _).2.symm.trans (h2.trans ?_)⟩
    rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_pos.2 (M.ab_pos t)).le, Complex.real_smul]
    exact congrArg _ (hρ' _).2
end
