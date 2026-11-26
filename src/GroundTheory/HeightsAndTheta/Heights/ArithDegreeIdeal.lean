module

public import GroundTheory.HeightsAndTheta.Heights.ArithDegreeExact
public import GroundTheory.HeightsAndTheta.Heights.FubiniStudyMetric

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithDegreeIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem projective_of_isTorsionFree (M : Type*) [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] [Module.IsTorsionFree (𝓞 K) M] : Module.Projective (𝓞 K) M := by
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

instance submodule_projective {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
    [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] (F : Submodule (𝓞 K) E) :
    Module.Projective (𝓞 K) F := by
  have : Module.IsTorsionFree (𝓞 K) F := inferInstance
  exact projective_of_isTorsionFree F

section Comap

variable {E E' : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] [AddCommGroup E'] [Module (𝓞 K) E'] [Module.Finite (𝓞 K) E']
  [Module.Projective (𝓞 K) E']

def fibreMap (σ : K →+* ℂ) (f : E' →ₗ[𝓞 K] E) : Fibre σ E' →ₗ[ℂ] Fibre σ E where
  toFun x := f.lTensor (ComplexAt σ) x
  map_add' := map_add _
  map_smul' := lTensor_complex_smul σ f



omit [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] [Module.Finite (𝓞 K) E']
  [Module.Projective (𝓞 K) E'] in
theorem fibreMap_injective (σ : K →+* ℂ) {f : E' →ₗ[𝓞 K] E} (hf : Function.Injective f) :
    Function.Injective (fibreMap σ f) :=
  Module.Flat.lTensor_preserves_injective_linearMap f hf


omit [NumberField K] [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E]
  [Module.Finite (𝓞 K) E'] [Module.Projective (𝓞 K) E'] in
theorem conjMap_fibreMap (σ : K →+* ℂ) (f : E' →ₗ[𝓞 K] E) (x : Fibre σ E') :
    conjMap σ E (fibreMap σ f x) = fibreMap (conjugate σ) f (conjMap σ E' x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [(fibreMap σ f).map_zero, (conjMap σ E).map_zero,
      (conjMap σ E').map_zero, (fibreMap (conjugate σ) f).map_zero]
  | tmul z e => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]

def HermitianMetric.comap (h : HermitianMetric K E) (f : E' →ₗ[𝓞 K] E)
    (hf : Function.Injective f) : HermitianMetric K E' where
  form σ := coreComap (h.form σ) (fibreMap σ f) (fibreMap_injective σ hf)
  form_conj σ x y := by
    rw [coreComap_inner, coreComap_inner, ← conjMap_fibreMap, ← conjMap_fibreMap, h.form_conj]

theorem HermitianMetric.comap_inner (h : HermitianMetric K E) (f : E' →ₗ[𝓞 K] E)
    (hf : Function.Injective f) (σ : K →+* ℂ) (x y : Fibre σ E') :
    ((h.comap f hf).form σ).inner x y = (h.form σ).inner (fibreMap σ f x) (fibreMap σ f y) := rfl

end Comap

def HermitianMetric.ideal (I : Ideal (𝓞 K)) : HermitianMetric K I :=
  (HermitianMetric.integers K).comap (Submodule.subtype I) (Submodule.injective_subtype I)

def HermitianBundle.ideal (I : Ideal (𝓞 K)) : HermitianBundle K := ⟨I, HermitianMetric.ideal I⟩

theorem finrank_ideal {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : Module.finrank (𝓞 K) I = 1 := by
  obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hle : Module.finrank (𝓞 K) I ≤ 1 := by
    have := Submodule.finrank_le I
    rwa [Module.finrank_self] at this
  have hge : 1 ≤ Module.finrank (𝓞 K) I := by
    have hli : LinearIndependent (𝓞 K) (fun _ : Fin 1 ↦ (⟨a, haI⟩ : I)) :=
      linearIndependent_unique_iff.mpr (by simpa using ha)
    simpa using hli.fintype_card_le_finrank
  omega

theorem arithDegree_ideal {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    (HermitianBundle.ideal I).arithDegree = -Real.log (Ideal.absNorm I) := by
  obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  set s : I := ⟨a, haI⟩
  have hs : s ≠ 0 := by simpa [s] using ha
  change arithDegree (HermitianMetric.ideal I) = _
  rw [arithDegree_line _ (finrank_ideal hI) hs]

  set T : Ideal (𝓞 K) := Ideal.span {a}
  have hTI : T ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr haI
  have hcard : Nat.card (I ⧸ Submodule.span (𝓞 K) {s}) * Ideal.absNorm I =
      (Algebra.norm ℤ a).natAbs := by
    rw [← Ideal.absNorm_span_singleton, Ideal.absNorm_apply, Ideal.absNorm_apply,
      Submodule.cardQuot_apply, Submodule.cardQuot_apply,
      ← Submodule.card_quotient_mul_card_quotient I T hTI]
    congr 1
    have hker : LinearMap.ker (T.mkQ ∘ₗ I.subtype) = Submodule.span (𝓞 K) {s} := by
      ext x
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, Submodule.subtype_apply, T, Ideal.mem_span_singleton',
        Submodule.mem_span_singleton]
      constructor
      · rintro ⟨c, hc⟩; exact ⟨c, Subtype.ext hc⟩
      · rintro ⟨c, hc⟩; exact ⟨c, congrArg Subtype.val hc⟩
    have hrange : Submodule.map T.mkQ I = LinearMap.range (T.mkQ ∘ₗ I.subtype) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    rw [← hker, hrange]
    exact Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv

  have hnorm : ∀ σ : K →+* ℂ, ‖fibreVec (HermitianMetric.ideal I) σ s‖ = ‖σ (a : K)‖ := by
    intro σ
    have h1 := norm_fibreVec_sq (HermitianMetric.ideal I) σ s
    rw [HermitianMetric.ideal, HermitianMetric.comap_inner] at h1
    erw [HermitianMetric.integers_inner] at h1
    simp only [Submodule.subtype_apply, s, LinearMap.id_apply, map_one, mul_one] at h1
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq] at h1
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1
  simp only [hnorm, sum_log_norm_embedding a ha]
  have hN : (0 : ℝ) < Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hc : (Nat.card (I ⧸ Submodule.span (𝓞 K) {s}) : ℝ) =
      (Algebra.norm ℤ a).natAbs / Ideal.absNorm I := by
    rw [eq_div_iff hN.ne', ← hcard]
    push_cast; ring
  rw [hc, Real.log_div]
  · ring
  · exact_mod_cast Int.natAbs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr ha)
  · exact hN.ne'

theorem HermitianBundle.degree_eq_arithDegree (E : HermitianBundle K)
    (F : Submodule (𝓞 K) E.carrier) :
    E.degree F = GroundTheory.Heights₂.Heights.arithDegree (E.metric.comap F.subtype F.injective_subtype) := by
  have hf := (HermitianBundle.exists_linearIndependent_rank E F).choose_spec
  set f := (HermitianBundle.exists_linearIndependent_rank E F).choose
  rw [arithDegree_eq _ hf (Fintype.card_fin _)]
  simp only [HermitianBundle.degree, HermitianBundle.degreeWith, degreeWith]
  congr 2
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  congr 1
  have hG : (gram ℂ fun i ↦ fibreVec (E.metric.comap F.subtype F.injective_subtype) σ (f i)) =
      Matrix.of fun i j ↦ (E.metric.form σ).inner
        ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (f i : E.carrier)) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (f j : E.carrier)) := by
    ext i j
    rfl
  have hD := (posSemidef_gram ℂ fun i ↦
    fibreVec (E.metric.comap F.subtype F.injective_subtype) σ (f i)).det_nonneg
  rw [hG] at hD
  simp only [GroundTheory.Heights₂.Heights.gramDet, HermitianBundle.gramDet]
  rw [hG]
  have := congrArg Complex.re (Complex.norm_of_nonneg' hD)
  simpa [f] using this

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FubiniStudyChern
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped ContDiff ComplexConjugate Matrix ComplexOrder
open Topology Set

noncomputable section

variable {N : ℕ}

def wirtinger (f : (Fin N → ℂ) → ℂ) (j : Fin N) (z : Fin N → ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f z (Pi.single j 1) - Complex.I * fderiv ℝ f z (Pi.single j Complex.I))

def wirtingerBar (f : (Fin N → ℂ) → ℂ) (j : Fin N) (z : Fin N → ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f z (Pi.single j 1) + Complex.I * fderiv ℝ f z (Pi.single j Complex.I))

def normSqSum (z : Fin N → ℂ) : ℝ := ∑ j, ‖z j‖ ^ 2

lemma normSqSum_nonneg (z : Fin N → ℂ) : 0 ≤ normSqSum z :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma one_add_normSqSum_pos (z : Fin N → ℂ) : 0 < 1 + normSqSum z := by
  have := normSqSum_nonneg z; linarith

def dNormSqSum (z : Fin N → ℂ) : (Fin N → ℂ) →L[ℝ] ℝ :=
  ∑ m, (2 • innerSL ℝ (z m)).comp (ContinuousLinearMap.proj m)

lemma hasFDerivAt_normSqSum (z : Fin N → ℂ) : HasFDerivAt normSqSum (dNormSqSum z) z := by
  have h : ∀ m ∈ (Finset.univ : Finset (Fin N)), HasFDerivAt
      ((fun x : ℂ => ‖x‖ ^ 2) ∘ (fun u : Fin N → ℂ => u m))
      ((2 • innerSL ℝ (z m)).comp (ContinuousLinearMap.proj m)) z := fun m _ =>
    (hasStrictFDerivAt_norm_sq (z m)).hasFDerivAt.comp z (hasFDerivAt_apply (𝕜 := ℝ) m z)
  exact HasFDerivAt.fun_sum h

lemma dNormSqSum_single (z : Fin N → ℂ) (j : Fin N) (w : ℂ) :
    dNormSqSum z (Pi.single j w) = 2 * (w * conj (z j)).re := by
  rw [dNormSqSum, FunLike.coe_sum, Finset.sum_apply, Finset.sum_eq_single j]
  · simp [Complex.inner]; ring
  · intro m _ hm; simp [hm]
  · simp

lemma hasFDerivAt_logPot (z : Fin N → ℂ) :
    HasFDerivAt (fun u => ((Real.log (1 + normSqSum u) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((1 + normSqSum z)⁻¹ • dNormSqSum z)) z :=
  Complex.ofRealCLM.hasFDerivAt.comp z
    (((hasFDerivAt_normSqSum z).const_add 1).log (one_add_normSqSum_pos z).ne')

lemma wirtingerBar_logPot (k : Fin N) (z : Fin N → ℂ) :
    wirtingerBar (fun u => ((Real.log (1 + normSqSum u) : ℝ) : ℂ)) k z =
      (((1 + normSqSum z)⁻¹ : ℝ) : ℂ) * z k := by
  rw [wirtingerBar, (hasFDerivAt_logPot z).fderiv]
  simp only [ContinuousLinearMap.comp_apply, FunLike.coe_smul, Pi.smul_apply, dNormSqSum_single,
    Complex.ofRealCLM_apply, smul_eq_mul]
  have h1 : (1 * conj (z k)).re = (z k).re := by simp
  have h2 : (Complex.I * conj (z k)).re = (z k).im := by simp
  rw [h1, h2]
  conv_rhs => rw [← Complex.re_add_im (z k)]
  push_cast
  ring

lemma hasFDerivAt_coordDiv (k : Fin N) (z : Fin N → ℂ) :
    HasFDerivAt (fun u : Fin N → ℂ => (1 + normSqSum u)⁻¹ • u k)
      ((1 + normSqSum z)⁻¹ • (ContinuousLinearMap.proj k : (Fin N → ℂ) →L[ℝ] ℂ) +
        ((-((1 + normSqSum z) ^ 2)⁻¹) • dNormSqSum z).smulRight (z k)) z := by
  have hinv : HasFDerivAt (fun u : Fin N → ℂ => (1 + normSqSum u)⁻¹)
      ((-((1 + normSqSum z) ^ 2)⁻¹) • dNormSqSum z) z :=
    (hasDerivAt_inv (one_add_normSqSum_pos z).ne').comp_hasFDerivAt z
      ((hasFDerivAt_normSqSum z).const_add 1)
  exact hinv.smul (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℂ) k).hasFDerivAt

namespace CP

def kahlerPotential (i : Fin (N + 1)) (z : Fin N → ℂ) : ℝ :=
  -Real.log (fsNorm (chartInv i z) (restrictForm (coordForm i) _) ^ 2)

lemma kahlerPotential_eq (i : Fin (N + 1)) (z : Fin N → ℂ) :
    kahlerPotential i z = Real.log (1 + normSqSum z) := by
  rw [kahlerPotential, fsNorm_sq_frame, one_div, Real.log_inv, neg_neg]; rfl

def chernCoeff (i : Fin (N + 1)) (z : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k => ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    wirtinger (fun w => wirtingerBar (fun u => ((kahlerPotential i u : ℝ) : ℂ)) k w) j z

theorem chernCoeff_apply (i : Fin (N + 1)) (z : Fin N → ℂ) (j k : Fin N) :
    chernCoeff i z j k = ((1 / (2 * Real.pi * (1 + normSqSum z)) : ℝ) : ℂ) *
      ((1 : Matrix (Fin N) (Fin N) ℂ) j k -
        (((1 + normSqSum z)⁻¹ : ℝ) : ℂ) * (conj (z j) * z k)) := by
  have hpot : (fun u => ((kahlerPotential i u : ℝ) : ℂ)) =
      fun u => ((Real.log (1 + normSqSum u) : ℝ) : ℂ) := by
    funext u; rw [kahlerPotential_eq]
  have hfun : (fun w => wirtingerBar (fun u => ((kahlerPotential i u : ℝ) : ℂ)) k w) =
      fun u : Fin N → ℂ => (1 + normSqSum u)⁻¹ • u k := by
    funext w; rw [hpot, wirtingerBar_logPot, Complex.real_smul]
  rw [chernCoeff, Matrix.of_apply, hfun, wirtinger, (hasFDerivAt_coordDiv k z).fderiv]
  simp only [FunLike.coe_add, Pi.add_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.smulRight_apply, dNormSqSum_single,
    smul_eq_mul, Complex.real_smul]
  have h1 : (1 * conj (z j)).re = (z j).re := by simp
  have h2 : (Complex.I * conj (z j)).re = (z j).im := by simp
  rw [h1, h2]
  have hS := one_add_normSqSum_pos z
  have hconj : conj (z j) = ((z j).re : ℂ) - ((z j).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hS' : (1 + (normSqSum z : ℂ)) ≠ 0 := by exact_mod_cast hS.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hconj, Matrix.one_apply]
  by_cases h : j = k
  · subst h
    simp only [Pi.single_eq_same, if_true]
    push_cast
    field_simp
    ring_nf
    all_goals (try simp only [Complex.I_sq])
    all_goals ring
  · simp only [Pi.single_apply, if_neg (Ne.symm h), if_neg h]
    push_cast
    field_simp
    ring_nf

theorem chernCoeff_eq_matrix (i : Fin (N + 1)) (z : Fin N → ℂ) :
    chernCoeff i z = ((1 / (2 * Real.pi * (1 + normSqSum z)) : ℝ) : ℂ) •
      (1 - (((1 + normSqSum z)⁻¹ : ℝ) : ℂ) • Matrix.vecMulVec (star z) z) := by
  ext j k
  rw [chernCoeff_apply]
  simp [Matrix.vecMulVec_apply]

lemma star_dotProduct_self (x : Fin N → ℂ) : star x ⬝ᵥ x = ((∑ j, ‖x j‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
  push_cast; rfl

theorem chernCoeff_quadForm (i : Fin (N + 1)) (z x : Fin N → ℂ) :
    star x ⬝ᵥ (chernCoeff i z *ᵥ x) = ((1 / (2 * Real.pi * (1 + normSqSum z)) *
      (∑ j, ‖x j‖ ^ 2 - (1 + normSqSum z)⁻¹ * ‖z ⬝ᵥ x‖ ^ 2) : ℝ) : ℂ) := by
  rw [chernCoeff_eq_matrix, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, dotProduct_sub,
    dotProduct_smul, dotProduct_smul, Matrix.star_dotProduct_star, star_dotProduct_self]
  simp only [smul_eq_mul, Complex.star_def, Complex.mul_conj']
  push_cast
  ring

lemma norm_dotProduct_sq_le (z x : Fin N → ℂ) :
    ‖z ⬝ᵥ x‖ ^ 2 ≤ normSqSum z * ∑ j, ‖x j‖ ^ 2 := by
  have h1 : ‖z ⬝ᵥ x‖ ≤ ∑ j, ‖z j‖ * ‖x j‖ := by
    simp only [dotProduct]
    exact (norm_sum_le _ _).trans (le_of_eq (by simp))
  have h2 : (∑ j, ‖z j‖ * ‖x j‖) ^ 2 ≤ (∑ j, ‖z j‖ ^ 2) * (∑ j, ‖x j‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem det_chernCoeff (i : Fin (N + 1)) (z : Fin N → ℂ) :
    (chernCoeff i z).det = (((1 / (2 * Real.pi)) ^ N / (1 + normSqSum z) ^ (N + 1) : ℝ) : ℂ) := by
  rw [chernCoeff_eq_matrix, Matrix.det_smul, Fintype.card_fin]
  have hmat : (1 : Matrix (Fin N) (Fin N) ℂ) - (((1 + normSqSum z)⁻¹ : ℝ) : ℂ) •
      Matrix.vecMulVec (star z) z = 1 + Matrix.replicateCol Unit
        (-((((1 + normSqSum z)⁻¹ : ℝ) : ℂ)) • star z) * Matrix.replicateRow Unit z := by
    ext j k
    simp [Matrix.vecMulVec_apply, Matrix.mul_apply, sub_eq_add_neg]
    ring
  have hzz : z ⬝ᵥ star z = ((normSqSum z : ℝ) : ℂ) := by
    rw [dotProduct_comm, star_dotProduct_self]; rfl
  rw [hmat, Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, hzz, smul_eq_mul]
  have hS := one_add_normSqSum_pos z
  have hpi := Real.pi_pos
  have key : (1 / (2 * Real.pi * (1 + normSqSum z))) ^ N * (1 + -(1 + normSqSum z)⁻¹ * normSqSum z) =
      (1 / (2 * Real.pi)) ^ N / (1 + normSqSum z) ^ (N + 1) := by
    simp only [div_pow, mul_pow, one_pow, pow_succ]
    field_simp
    ring
  rw [← key]
  push_cast
  ring

def fsVolumeDensity (i : Fin (N + 1)) (z : Fin N → ℂ) : ℝ :=
  (N.factorial : ℝ) * 2 ^ N * ((chernCoeff i z).det).re

theorem fsVolumeDensity_eq (i : Fin (N + 1)) (z : Fin N → ℂ) :
    fsVolumeDensity i z = N.factorial / (Real.pi ^ N * (1 + normSqSum z) ^ (N + 1)) := by
  rw [fsVolumeDensity, det_chernCoeff, Complex.ofReal_re, div_pow, one_pow, mul_pow]
  have hS := one_add_normSqSum_pos z
  have hpi := Real.pi_pos
  field_simp

lemma fsVolumeDensity_pos (i : Fin (N + 1)) (z : Fin N → ℂ) : 0 < fsVolumeDensity i z := by
  rw [fsVolumeDensity_eq]
  have hS := one_add_normSqSum_pos z
  have hpi := Real.pi_pos
  positivity

end CP

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Covolume
namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix MeasureTheory Module

open scoped Kronecker

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

section Real

variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] (h : HermitianMetric K E)

namespace RealSpace

end RealSpace

end Real

open scoped Classical in
open Classical in
theorem det_basisMatrix_sq : (basisMatrix K).det ^ 2 = ((discr K : ℤ) : ℂ) := by
  exact (discr_eq_basisMatrix_det_sq K).symm

theorem basisMatrix_apply' (τ σ : K →+* ℂ) :
    basisMatrix K τ σ = σ ((RingOfIntegers.basis K (equivReindex K τ) : 𝓞 K) : K) := by
  simp [basisMatrix, canonicalEmbedding.latticeBasis_apply, integralBasis_apply,
    canonicalEmbedding.apply_at]

section Gram

variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) {ι : Type*} [Fintype ι] [DecidableEq ι]

end Gram

section RiemannRoch

variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) {ι : Type*} [Fintype ι] [DecidableEq ι]
  {s : ι → E}



end RiemannRoch

namespace HermitianExtension

variable {E' E E'' : HermitianBundle K} (X : HermitianExtension E' E E'')

end HermitianExtension

end

end GroundTheory.Heights₂.Heights
end
