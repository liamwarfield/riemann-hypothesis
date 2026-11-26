module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.FtBasic
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

namespace UpperTheory.ConvolutionTheory.R2.C

variable {F : Type} [Field F] [NumberField F]

private noncomputable def Gm (δ : F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, -1, 0, 0; -1, 0, 0, 0; 0, 0, 2, 0; 0, 0, 0, -(2 * δ)]

private noncomputable def Hm (δ : F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, -1, 0, 0; -1, 0, 0, 0; 0, 0, 2⁻¹, 0; 0, 0, 0, -(2 * δ)⁻¹]

private lemma Gm_mul_Hm {δ : F} (hδ : δ ≠ 0) : Gm δ * Hm δ = 1 := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Gm, Hm, Matrix.mul_apply, Fin.sum_univ_four, h2, hδ]
  field_simp

private lemma Hm_mul_Gm {δ : F} (hδ : δ ≠ 0) : Hm δ * Gm δ = 1 :=
  mul_eq_one_comm.1 (Gm_mul_Hm hδ)

private lemma Gm_transpose (δ : F) : (Gm δ)ᵀ = Gm δ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Gm]

private lemma sum_eq_quaternaryForm (δ : F) (y v : V4 F) :
    ∑ i, y i * ((Gm δ).map (algebraMap F (A F)) *ᵥ v) i = B4 δ y v := by
  have h2 : algebraMap F (A F) 2 = 2 := map_ofNat _ 2
  simp [Gm, B4, Fin.sum_univ_four, Matrix.mulVec, dotProduct, rt, h2]
  ring

private lemma quaternaryFourier_eq_adelic (δ : F) (φ : V4 F → ℂ) (v : V4 F) :
    ft4 δ φ v = adelicFourierPi F φ ((Gm δ).map (algebraMap F (A F)) *ᵥ v) := by
  simp only [ft4, adelicFourierPi, sum_eq_quaternaryForm, ψ]

end UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.ftBasic :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F), δ ≠ 0 → ∀ φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4),
    ft4 δ φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4) ∧ (∀ v, ft4 δ (ft4 δ φ) v = φ (-v)) ∧ Th (ft4 δ φ) = Th φ := by
  intro F _ _ δ hδ φ hφ
  have hGH := Gm_mul_Hm hδ
  have hHG := Hm_mul_Gm hδ
  have hfun : ft4 δ φ = fun v => adelicFourierPi F φ ((Gm δ).map (algebraMap F (A F)) *ᵥ v) :=
    funext (quaternaryFourier_eq_adelic δ φ)
  have hF := adelicFourierPi_mem_schwartzBruhatPi hφ
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]
    exact GroundTheory.Heights₂.Theta.comp_mulVec_mem_schwartzBruhatPi (Gm δ) (Hm δ) hHG hGH hF
  · intro v
    rw [quaternaryFourier_eq_adelic, hfun, GroundTheory.Heights₂.Theta.adelicFourierPi_comp_mulVec (Gm δ) (Hm δ) hHG hGH,
      adelicFourierPi_adelicFourierPi hφ]
    have hT : ((Hm δ).map (algebraMap F (A F)))ᵀ * (Gm δ).map (algebraMap F (A F)) = 1 := by
      have h : (Hm δ)ᵀ * Gm δ = 1 := by
        have h' := congrArg Matrix.transpose hGH
        rwa [Matrix.transpose_mul, Gm_transpose, Matrix.transpose_one] at h'
      rw [← Matrix.transpose_map]
      exact GroundTheory.Heights₂.Theta.map_mul_map_eq_one _ h
    simp only [Matrix.mulVec_mulVec, hT, Matrix.one_mulVec]
  · have hmap : ∀ ξ : Fin 4 → F, ((Gm δ).map (algebraMap F (A F)) *ᵥ fun i => rt (ξ i)) =
        fun i => rt ((Gm δ *ᵥ ξ) i) := by
      intro ξ
      exact (GroundTheory.Heights₂.Theta.map_mulVec_eq (algebraMap F (A F)) (Gm δ) ξ).symm
    let e : (Fin 4 → F) ≃ (Fin 4 → F) :=
      { toFun := fun ξ => Gm δ *ᵥ ξ
        invFun := fun ξ => Hm δ *ᵥ ξ
        left_inv := fun ξ => by simp only [Matrix.mulVec_mulVec, hHG, Matrix.one_mulVec]
        right_inv := fun ξ => by simp only [Matrix.mulVec_mulVec, hGH, Matrix.one_mulVec] }
    have h1 : Th (ft4 δ φ) = ∑' ξ : Fin 4 → F, adelicFourierPi F φ fun i => rt (ξ i) := by
      unfold Th
      rw [← e.tsum_eq (fun ξ : Fin 4 → F => adelicFourierPi F φ fun i => rt (ξ i))]
      refine tsum_congr fun ξ => ?_
      rw [quaternaryFourier_eq_adelic, hmap]
      rfl
    rw [h1]
    exact (tsum_algebraMap_eq_tsum_adelicFourierPi hφ).symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.SplitA
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private noncomputable def hI (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    (InfinitePlace F → ℝ) ≃ₜ InfiniteAdeleRing F where
  toEquiv := (TR.infEq F).toEquiv
  continuous_toFun := TR.continuous_infEq F
  continuous_invFun := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)

private theorem map_inf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    ∃ c : ENNReal, (infiniteAdeleMeasure F).map (hI F).symm =
      c • (volume : Measure (InfinitePlace F → ℝ)) := by
  have hH : ((infiniteAdeleMeasure F).map (hI F).symm).IsAddHaarMeasure :=
    (TR.infEq F).symm.toAddEquiv.isAddHaarMeasure_map (infiniteAdeleMeasure F)
      (hI F).symm.continuous (hI F).continuous
  have h := Measure.isAddLeftInvariant_eq_smul ((infiniteAdeleMeasure F).map (hI F).symm)
    (volume : Measure (InfinitePlace F → ℝ))
  obtain ⟨c, hν⟩ : ∃ c : NNReal, (infiniteAdeleMeasure F).map (hI F).symm =
      c • (volume : Measure (InfinitePlace F → ℝ)) := ⟨_, h⟩
  refine ⟨(c : ENNReal), hν.trans ?_⟩
  ext s _
  rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def]

private theorem psi_inf (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (y : InfinitePlace F → ℝ) :
    adelicChar F (infiniteAdeleInl (TR.infEq F y)) = Real.fourierChar (-∑ w, y w) := by
  rw [adelicChar_infiniteAdeleInl, ← Finset.sum_neg_distrib, addChar_map_finsetSum]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [infiniteAdelicChar_apply_of_isReal (IsTotallyReal.isReal w)]
  have e2 : InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)
      (TR.infEq F y w) = y w :=
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).apply_symm_apply (y w)
  rw [e2]

theorem UpperTheory.ConvolutionTheory.R2.C.splitA :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], (∃ (e : A F ≃ᵐ (InfinitePlace F → ℝ) × FiniteAdeleRing (𝓞 F) F) (c : ENNReal), (∀ x, e x = (TR.pInf F x, x.2)) ∧
      (adeleMeasure F).map e = c • (volume : Measure (InfinitePlace F → ℝ)).prod (finiteAdeleMeasure F)) ∧
    ∀ x : A F, ψ x = (∏ w, Complex.exp (-(2 * Real.pi * Complex.I) * ((TR.pInf F x w : ℝ) : ℂ))) * ((finiteAdelicChar F x.2 : Circle) : ℂ) := by
  intro F _ _ _
  refine ⟨?_, fun x => ?_⟩
  · obtain ⟨c, hc⟩ := map_inf F
    let e : A F ≃ᵐ (InfinitePlace F → ℝ) × FiniteAdeleRing (𝓞 F) F :=
      MeasurableEquiv.prodCongr (hI F).symm.toMeasurableEquiv (MeasurableEquiv.refl _)
    refine ⟨e, c, fun x => rfl, ?_⟩
    have h1 : ((infiniteAdeleMeasure F).map (hI F).symm).prod
        ((finiteAdeleMeasure F).map id) =
        ((infiniteAdeleMeasure F).prod (finiteAdeleMeasure F)).map (Prod.map (hI F).symm id) :=
      Measure.map_prod_map _ _ (hI F).symm.measurable measurable_id
    rw [Measure.map_id, hc, Measure.prod_smul_left] at h1
    exact h1.symm
  · have hx : x = infiniteAdeleInl (TR.infEq F (TR.pInf F x)) + finiteAdeleInr x.2 := by
      have h0 : TR.infEq F (TR.pInf F x) = x.1 := (TR.infEq F).apply_symm_apply x.1
      rw [h0]
      exact (infiniteAdeleInl_add_finiteAdeleInr x).symm
    have h1 : ψ x = ((Real.fourierChar (-∑ w, TR.pInf F x w) : Circle) : ℂ) *
        ((finiteAdelicChar F x.2 : Circle) : ℂ) := by
      rw [ψ]
      conv_lhs => rw [hx]
      rw [AddChar.map_add_eq_mul, Circle.coe_mul, psi_inf, finiteAdelicChar_apply]
    rw [h1, Real.fourierChar_apply, ← Complex.exp_sum]
    congr 2
    push_cast
    rw [← Finset.mul_sum]
    ring_nf
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ChirpQ
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ChirpInf
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.chirpInf :
    ∀ (K ι : Type) [Field K] [NumberField K] [Fintype ι] (p : MvPolynomial ι (mixedEmbedding.mixedSpace K)) (l : mixedEmbedding.mixedSpace K →L[ℝ] ℝ),
    Function.HasTemperateGrowth fun x : ι → mixedEmbedding.mixedSpace K => ((Real.fourierChar (l (MvPolynomial.eval x p)) : Circle) : ℂ) := by
  intro K ι _ _ _ p l
  have hp : Function.HasTemperateGrowth
      fun x : ι → mixedEmbedding.mixedSpace K => MvPolynomial.eval x p := by
    induction p using MvPolynomial.induction_on with
    | C a =>
      simpa using Function.HasTemperateGrowth.const (E := ι → mixedEmbedding.mixedSpace K) a
    | add p q hp hq =>
      simp only [map_add (f := _)]
      exact hp.fun_add hq
    | mul_X p i hp =>
      have hi : Function.HasTemperateGrowth fun x : ι → mixedEmbedding.mixedSpace K => x i :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => mixedEmbedding.mixedSpace K)
          i).hasTemperateGrowth
      simp only [map_mul, MvPolynomial.eval_X]
      exact hp.fun_mul hi
  exact GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp (l.hasTemperateGrowth.comp hp)
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C
open GroundTheory.Heights₂.Theta

section ChirpQ

variable {F : Type} [Field F] [NumberField F]

private theorem eval_map_hom {R S ι : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (p : MvPolynomial ι R) (v : ι → R) :
    MvPolynomial.eval (fun i => f (v i)) (p.map f) = f (MvPolynomial.eval v p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

private theorem continuous_eval_poly {R ι : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (p : MvPolynomial ι R) :
    Continuous fun v : ι → R => MvPolynomial.eval v p := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using continuous_const
  | add p q hp hq => simp only [map_add (f := _)]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, MvPolynomial.eval_X]; exact hp.mul (continuous_apply i)


variable (F) in
private noncomputable def lT : mixedEmbedding.mixedSpace F →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (-((mixedTraceForm F).flip 1))

private theorem psi_split (x : A F) :
    ψ x = ((Real.fourierChar (lT F (adeleInfHom x)) : Circle) : ℂ) *
      ((finiteAdelicChar F (adeleFinHom x) : Circle) : ℂ) := by
  have h := adelicChar_mul_eq (K := F) x 1
  rw [mul_one] at h
  have h1 : homeomorphMixedSpace F (1 : A F).1 = 1 := by
    exact map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  rw [h1] at h
  have h2 : x.2 * (1 : A F).2 = adeleFinHom x := by
    change x.2 * 1 = x.2
    rw [mul_one]
  rw [h2] at h
  exact h

private theorem chirp_poly (p : MvPolynomial (Fin 4) (A F)) (φ : V4 F → ℂ)
    (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) :
    (fun v => ψ (MvPolynomial.eval v p) * φ v) ∈ schwartzBruhatPi (K := F) (ι := Fin 4) := by
  refine Submodule.span_induction
    (p := fun f _ => (fun v => ψ (MvPolynomial.eval v p) * f v) ∈ schwartzBruhatPi (K := F) (ι := Fin 4))
    ?_ ?_ ?_ ?_ hφ
  · rintro _ ⟨φ0, g, hg, rfl⟩
    have hT := chirpInf F (Fin 4) (p.map adeleInfHom) (lT F)
    have hloc : IsLocallyConstant fun w : Fin 4 → FiniteAdeleRing (𝓞 F) F =>
        ((finiteAdelicChar F (MvPolynomial.eval w (p.map adeleFinHom)) : Circle) : ℂ) := by
      have h1 := (isLocallyConstant_finiteAdelicChar_mul (K := F) 1).comp_continuous
        (continuous_eval_poly (p.map (adeleFinHom (K := F))))
      simpa [Function.comp_def] using h1
    have hg' : (fun w => ((finiteAdelicChar F (MvPolynomial.eval w (p.map adeleFinHom)) : Circle) : ℂ) * g w)
        ∈ finiteSchwartzBruhatPi F (ι := Fin 4) :=
      ⟨hloc.mul hg.1, hg.2.mul_left⟩
    convert schwartzBruhatTensorPi_mem (SchwartzMap.smulLeftCLM ℂ (fun x : Fin 4 → mixedEmbedding.mixedSpace F =>
      ((Real.fourierChar (lT F (MvPolynomial.eval x (p.map adeleInfHom))) : Circle) : ℂ)) φ0) hg' using 1
    funext v
    simp only [schwartzBruhatTensorPi]
    rw [SchwartzMap.smulLeftCLM_apply_apply hT, psi_split]
    simp only [smul_eq_mul, infPartPi_eq_adeleInfHom, finPartPi_eq_adeleFinHom, eval_map_hom]
    ring
  · convert (schwartzBruhatPi (K := F) (ι := Fin 4)).zero_mem using 1
    funext v
    simp
  · intro f g _ _ hf hg
    convert (schwartzBruhatPi (K := F) (ι := Fin 4)).add_mem hf hg using 1
    funext v
    simp [mul_add]
  · intro a f _ hf
    convert (schwartzBruhatPi (K := F) (ι := Fin 4)).smul_mem a hf using 1
    funext v
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

end ChirpQ

theorem UpperTheory.ConvolutionTheory.R2.C.chirpQ :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (b : A F) (y : V4 F) (φ : V4 F → ℂ), φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4) →
    (fun v => ψ (b * q4 δ v + B4 δ v y) * φ v) ∈ schwartzBruhatPi (K := F) (ι := Fin 4) := by
  intro F _ _ δ b y φ hφ
  open MvPolynomial in
  have h := chirp_poly (F := F)
    (C b * (X 2 ^ 2 - C (rt δ) * X 3 ^ 2 - X 1 * X 0) +
      (2 * (X 2 * C (y 2) - C (rt δ) * (X 3 * C (y 3))) - X 1 * C (y 0) - X 0 * C (y 1))) φ hφ
  convert h using 3 with v
  simp [q4, B4]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.UnitA
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.unitA :
    ∀ (F : Type) [Field F] [NumberField F] (x : A F), IsUnit x ↔ (∀ w, x.1 w ≠ 0) ∧ (∀ v, x.2 v ≠ 0) ∧ ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, Valued.v (x.2 v) = 1 := by
  intro F _ _ x
  constructor
  · rintro ⟨a, rfl⟩
    have hinf : ∀ w, (a : A F).1 w * ((a⁻¹ : (A F)ˣ) : A F).1 w = 1 := fun w =>
      congrArg (fun z : A F => z.1 w) a.mul_inv
    have hfin : ∀ v, (a : A F).2 v * ((a⁻¹ : (A F)ˣ) : A F).2 v = 1 := fun v =>
      congrArg (fun z : A F => z.2 v) a.mul_inv
    refine ⟨fun w h => ?_, fun v h => ?_, ?_⟩
    · have := hinf w
      rw [h, zero_mul] at this
      exact zero_ne_one this
    · have := hfin v
      rw [h, zero_mul] at this
      exact zero_ne_one this
    · filter_upwards [(a : A F).2.2, ((a⁻¹ : (A F)ˣ) : A F).2.2] with v h3 h4
      have hm := congrArg Valued.v (hfin v)
      rw [map_mul, map_one] at hm
      refine le_antisymm h3 ?_
      rw [← hm]
      exact mul_le_of_le_one_right' h4
  · rintro ⟨h1, h2, h3⟩
    have hmem : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
        (x.2 v)⁻¹ ∈ v.adicCompletionIntegers F := by
      filter_upwards [h3] with v hv
      change Valued.v (x.2 v)⁻¹ ≤ 1
      rw [map_inv₀, hv, inv_one]
    let y : A F := (fun w => (x.1 w)⁻¹, ⟨fun v => (x.2 v)⁻¹, hmem⟩)
    refine IsUnit.of_mul_eq_one y (Prod.ext (funext fun w => ?_) ?_)
    · exact mul_inv_cancel₀ (h1 w)
    · apply RestrictedProduct.ext
      intro v
      exact mul_inv_cancel₀ (h2 v)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.TestEx
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.GaussS
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private noncomputable def gaussEquiv (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ι : Type) [Fintype ι] :
    (ι → NumberField.mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ (ι × InfinitePlace F) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => WithLp.toLp 2 fun p => (x p.1).1 ⟨p.2, IsTotallyReal.isReal p.2⟩
      map_add' := fun x y => by ext p; simp
      map_smul' := fun c x => by ext p; simp
      invFun := fun y i => (fun w => y (i, w.1), fun _ => 0)
      left_inv := fun x => by
        funext i
        refine Prod.ext (funext fun w => rfl) (funext fun w => ?_)
        exact absurd (IsTotallyReal.isReal w.1) (InfinitePlace.not_isReal_iff_isComplex.2 w.2)
      right_inv := fun y => by ext p; rfl }

private theorem gaussEquiv_apply {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {ι : Type} [Fintype ι]
    (v : ι → A F) (p : ι × InfinitePlace F) :
    gaussEquiv F ι (infPartPi v) p = TR.pInf F (v p.1) p.2 := by
  change (infPartPi v p.1).1 ⟨p.2, IsTotallyReal.isReal p.2⟩ = _
  simp only [infPartPi, homeomorphMixedSpace_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  change _ = InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal p.2) ((v p.1).1 p.2)
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]

theorem UpperTheory.ConvolutionTheory.R2.C.gaussS :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ι : Type) [Fintype ι] (g : FiniteAdeleRing (𝓞 F) F → ℂ), g ∈ finiteSchwartzBruhat F → (fun v : ι → A F => ∏ i, g1 g (v i)) ∈ schwartzBruhatPi (K := F) (ι := ι) := by
  intro F _ _ _ ι _ g hg
  have h := schwartzBruhatTensorPi_mem
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (gaussEquiv F ι)
      (gaussianSchwartz (EuclideanSpace ℝ (ι × InfinitePlace F))))
    (finiteTensor_mem (ι := ι) fun _ => hg)
  convert h using 1
  funext v
  have hn : ‖gaussEquiv F ι (infPartPi v)‖ ^ 2 = ∑ i, ∑ w, TR.pInf F (v i) w ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun w _ => by rw [gaussEquiv_apply]
  simp only [schwartzBruhatTensorPi, finiteTensor, g1, Finset.prod_mul_distrib,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, gaussianSchwartz_apply, hn]
  congr 1
  · push_cast
    rw [Finset.mul_sum, Complex.exp_sum]
    refine (Finset.prod_congr rfl fun i _ => ?_)
    rw [Finset.mul_sum, Complex.exp_sum]
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

namespace UpperTheory.ConvolutionTheory.R2.C.TestFunctionExistence

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private noncomputable abbrev g0 (F : Type) [Field F] [NumberField F] : FiniteAdeleRing (𝓞 F) F → ℂ :=
  cosetIndicator (1 : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ) 0

private theorem gaussianTest_real_nonneg (x : A F) : ∃ r : ℝ, 0 ≤ r ∧ g1 (g0 F) x = (r : ℂ) := by
  refine ⟨(∏ w, Real.exp (-Real.pi * (TR.pInf F x w) ^ 2)) *
    (if x.2 - 0 ∈ idealFiniteAdeles (1 : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ) then 1 else 0), ?_, ?_⟩
  · exact mul_nonneg (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le) (by split_ifs <;> norm_num)
  · simp only [g1, g0, cosetIndicator_apply]
    push_cast
    split_ifs <;> simp

private theorem four_real (v : V4 F) : ∃ r : ℝ, 0 ≤ r ∧ four (g1 (g0 F)) v = (r : ℂ) := by
  obtain ⟨a, ha, ea⟩ := gaussianTest_real_nonneg (F := F) (rt (2⁻¹ : F) * (v 1 - v 0))
  obtain ⟨b, hb, eb⟩ := gaussianTest_real_nonneg (F := F) (rt (2⁻¹ : F) * (v 1 + v 0))
  obtain ⟨c, hc, ec⟩ := gaussianTest_real_nonneg (F := F) (v 2)
  obtain ⟨d, hd, ed⟩ := gaussianTest_real_nonneg (F := F) (v 3)
  refine ⟨a * b * c * d, by positivity, ?_⟩
  simp only [four, ea, eb, ec, ed]
  push_cast
  rfl

private theorem gaussianTest_zero : g1 (g0 F) (0 : A F) = 1 := by
  have h : TR.pInf F (0 : A F) = 0 := by
    simp
  simp [g1, g0, cosetIndicator_apply, h]

private theorem four_zero : four (g1 (g0 F)) (0 : V4 F) = 1 := by
  simp [four, gaussianTest_zero]

private def Mt (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![-2⁻¹, 2⁻¹, 0, 0; 2⁻¹, 2⁻¹, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private def Nt (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![-1, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private theorem NM : Nt F * Mt F = 1 := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Nt, Mt, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp <;> norm_num

private theorem MN : Mt F * Nt F = 1 := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Nt, Mt, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp <;> norm_num

private theorem four_mem : four (g1 (g0 F)) ∈ schwartzBruhatPi (K := F) (ι := Fin 4) := by
  have h := GroundTheory.Heights₂.Theta.comp_mulVec_mem_schwartzBruhatPi (Mt F) (Nt F) NM MN
    (gaussS F (Fin 4) (g0 F) (cosetIndicator_mem_finiteSchwartzBruhat _ _))
  convert h using 1
  funext v
  have hv : ((Mt F).map (algebraMap F (A F)) *ᵥ v) =
      ![rt (2⁻¹ : F) * (v 1 - v 0), rt (2⁻¹ : F) * (v 1 + v 0), v 2, v 3] := by
    funext i
    fin_cases i <;>
      simp [Mt, Matrix.mulVec, dotProduct, Fin.sum_univ_four, rt, mul_sub, mul_add] <;> ring
  rw [hv]
  simp [four, Fin.prod_univ_four]

end UpperTheory.ConvolutionTheory.R2.C.TestFunctionExistence

open UpperTheory.ConvolutionTheory.R2.C.TestFunctionExistence in
theorem UpperTheory.ConvolutionTheory.R2.C.testEx :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ g : FiniteAdeleRing (𝓞 F) F → ℂ, four (g1 g) ∈ schwartzBruhatPi (K := F) (ι := Fin 4) ∧ ∫ v, four (g1 g) v ∂(adeleMeasurePi F) ≠ 0 ∧ Th (four (g1 g)) ≠ 0 := by
  intro F _ _ _
  have hm := four_mem (F := F)
  have hre : ∀ v : V4 F, four (g1 (g0 F)) v = (((four (g1 (g0 F)) v).re : ℝ) : ℂ) := by
    intro v
    obtain ⟨r, -, e⟩ := four_real (F := F) v
    rw [e]
    simp
  have hnn : ∀ v : V4 F, 0 ≤ (four (g1 (g0 F)) v).re := by
    intro v
    obtain ⟨r, h, e⟩ := four_real (F := F) v
    rw [e]
    simpa using h
  have hc : Continuous fun v : V4 F => (four (g1 (g0 F)) v).re :=
    Complex.continuous_re.comp (continuous_of_mem_schwartzBruhatPi hm)
  have hi : Integrable (fun v : V4 F => (four (g1 (g0 F)) v).re) (adeleMeasurePi F) :=
    (integrable_of_mem_schwartzBruhatPi hm).re
  refine ⟨g0 F, hm, ?_, ?_⟩
  · have hpos : 0 < ∫ v, (four (g1 (g0 F)) v).re ∂(adeleMeasurePi F) := by
      rw [integral_pos_iff_support_of_nonneg hnn hi]
      have ho : IsOpen (Function.support fun v : V4 F => (four (g1 (g0 F)) v).re) :=
        isOpen_compl_singleton.preimage hc
      refine ho.measure_pos _ ⟨0, ?_⟩
      simp [Function.mem_support, four_zero]
    have he : ∫ v, four (g1 (g0 F)) v ∂(adeleMeasurePi F) =
        ((∫ v, (four (g1 (g0 F)) v).re ∂(adeleMeasurePi F) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      exact integral_congr_ae (Eventually.of_forall hre)
    rw [he]
    exact_mod_cast hpos.ne'
  · have hs : Summable fun ξ : Fin 4 → F => four (g1 (g0 F)) fun i => rt (ξ i) :=
      (poisson_of_mem_schwartzBruhatPi hm).1.of_norm
    have hsr : Summable fun ξ : Fin 4 → F => (four (g1 (g0 F)) fun i => rt (ξ i)).re :=
      Complex.reCLM.summable hs
    have h1 : (1 : ℝ) ≤ ∑' ξ : Fin 4 → F, (four (g1 (g0 F)) fun i => rt (ξ i)).re := by
      have h := hsr.le_tsum (0 : Fin 4 → F) fun ξ _ => hnn _
      have h0 : (fun i : Fin 4 => rt ((0 : Fin 4 → F) i)) = (0 : V4 F) := by
        funext i
        simp [rt]
      rw [h0, four_zero] at h
      simpa using h
    intro hT
    have h2 : (Th (four (g1 (g0 F)))).re = ∑' ξ : Fin 4 → F, (four (g1 (g0 F)) fun i => rt (ξ i)).re :=
      Complex.re_tsum hs
    rw [hT] at h2
    simp at h2
    linarith
end
