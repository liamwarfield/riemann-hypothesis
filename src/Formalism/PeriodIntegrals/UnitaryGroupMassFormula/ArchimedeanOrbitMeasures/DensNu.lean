module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.MatNDHHolds

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DensGen
noncomputable section

namespace PI.AprimeInfW.GenericDensity

open scoped RealInnerProductSpace FourierTransform
open MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {V W ι : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V]
  [BorelSpace V] [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
  [BorelSpace W] [Fintype ι] [DecidableEq ι]

private theorem exists_linearMap_inner_eq_and_det_eq_gram_det (β : W → W → ℝ)
    (hL : ∀ x x' y, β (x + x') y = β x y + β x' y) (hR : ∀ x y y', β x (y + y') = β x y + β x y')
    (hcL : ∀ y, Continuous fun x => β x y) (hcR : ∀ x, Continuous fun y => β x y)
    (b : OrthonormalBasis ι ℝ W) :
    ∃ A : W →ₗ[ℝ] W, (∀ x y, β x y = ⟪x, A y⟫) ∧
      LinearMap.det A = (Matrix.of fun i j => β (b i) (b j)).det := by
  have sL : ∀ (r : ℝ) x y, β (r • x) y = r * β x y := fun r x y =>
    map_real_smul (AddMonoidHom.mk' (fun x => β x y) (fun x x' => hL x x' y)) (hcL y) r x
  have sR : ∀ (r : ℝ) x y, β x (r • y) = r * β x y := fun r x y =>
    map_real_smul (AddMonoidHom.mk' (fun y => β x y) (fun y y' => hR x y y')) (hcR x) r y
  let A : W →ₗ[ℝ] W :=
    { toFun := fun y => ∑ i, β (b i) y • b i
      map_add' := fun y y' => by simp only [hR, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r y => by simp only [sR, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hA : ∀ x y, β x y = ⟪x, A y⟫ := by
    intro x y
    have h1 : β x y = ∑ i, ⟪b i, x⟫ * β (b i) y := by
      conv_lhs => rw [← b.sum_repr' x]
      change (AddMonoidHom.mk' (fun x => β x y) (fun x x' => hL x x' y)) (∑ i, ⟪b i, x⟫ • b i) = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp [sL]
    have h2 : ⟪x, A y⟫ = ∑ i, β (b i) y * ⟪x, b i⟫ := by
      simp [A, inner_sum, inner_smul_right]
    rw [h1, h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm, mul_comm]
  refine ⟨A, hA, ?_⟩
  rw [← LinearMap.det_toMatrix b.toBasis]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.of_apply, hA]
  simp [OrthonormalBasis.repr_apply_apply]

private theorem integral_fourier_map_eq_neg_of_integrable (μ : Measure V) (χ : V → V → ℂ) (hμ : SelfDual μ χ) (e : V ≃ₜ W)
    (he : ∀ x y, e (x + y) = e x + e y) (β : W → W → ℝ)
    (hχ : ∀ x y, χ (e.symm x) (e.symm y) = ((𝐞 (β x y) : Circle) : ℂ))
    (Φ : W → ℂ) (hΦc : Continuous Φ) (hΦs : HasCompactSupport Φ)
    (hint : Integrable (fun y => ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂(μ.map e)) (μ.map e))
    (z : W) :
    ∫ y, (∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂(μ.map e)) * ((𝐞 (β y z) : Circle) : ℂ) ∂(μ.map e)
      = Φ (-z) := by
  have hme : MeasurableEmbedding e := e.measurableEmbedding
  have hmap : ∀ g : W → ℂ, ∫ w, g w ∂(μ.map e) = ∫ x, g (e x) ∂μ := fun g => hme.integral_map g
  have hχ' : ∀ x y, χ x y = ((𝐞 (β (e x) (e y)) : Circle) : ℂ) := fun x y => by
    simpa using hχ (e x) (e y)
  set F := fun y => ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂(μ.map e) with hFdef
  have hF : ∀ y, ∫ x, (Φ ∘ e) x * χ x y ∂μ = F (e y) := by
    intro y
    simp only [hFdef, hmap, Function.comp_apply, hχ']
  have hint' : Integrable (fun y => ∫ x, (Φ ∘ e) x * χ x y ∂μ) μ := by
    simp only [hF]
    exact hme.integrable_map_iff.mp hint
  have key := hμ.2 (Φ ∘ e) (hΦc.comp e.continuous) (hΦs.comp_homeomorph e) hint' (e.symm z)
  have hneg : e (-(e.symm z)) = -z := by
    have := map_neg (AddMonoidHom.mk' e he) (e.symm z)
    simpa using this
  simp only [hF, hχ', Homeomorph.apply_symm_apply, Function.comp_apply, hneg] at key
  rw [hmap]
  simp only [hFdef, hmap]
  exact key

private theorem false_of_degenerate_of_fourier_inversion (ν : Measure W) [ν.IsAddHaarMeasure] (β : W → W → ℝ)
    (hL : ∀ x x' y, β (x + x') y = β x y + β x' y) (hcL : ∀ y, Continuous fun x => β x y)
    (k : W) (hk : k ≠ 0) (hk0 : ∀ y, β k y = 0)
    (hP : ∀ Φ : W → ℂ, Continuous Φ → HasCompactSupport Φ →
      Integrable (fun y => ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂ν) ν → ∀ z : W,
      ∫ y, (∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂ν) * ((𝐞 (β y z) : Circle) : ℂ) ∂ν = Φ (-z)) :
    False := by
  have hkpos : 0 < ‖k‖ := norm_pos_iff.mpr hk
  let bump : ContDiffBump (0 : W) := ⟨‖k‖ / 2, ‖k‖, by positivity, by linarith⟩
  let ψ : W → ℂ := fun x => ((bump x : ℝ) : ℂ)
  have hψc : Continuous ψ := Complex.continuous_ofReal.comp bump.continuous
  have hψs : HasCompactSupport ψ := bump.hasCompactSupport.comp_left Complex.ofReal_zero
  have hψs' : HasCompactSupport (fun x => ψ (x + k)) := hψs.comp_homeomorph (Homeomorph.addRight k)
  let Φ : W → ℂ := fun x => ψ x - ψ (x + k)
  have hΦc : Continuous Φ := hψc.sub (hψc.comp (Homeomorph.addRight k).continuous)
  have hΦs : HasCompactSupport Φ := hψs.sub hψs'
  have hzero : ∀ y, ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂ν = 0 := by
    intro y
    let g : W → ℂ := fun x => ψ x * ((𝐞 (β x y) : Circle) : ℂ)
    have hgc : Continuous g := by
      have := hcL y
      fun_prop
    have hg : Integrable g ν := hgc.integrable_of_hasCompactSupport hψs.mul_right
    have heq : (fun x => Φ x * ((𝐞 (β x y) : Circle) : ℂ)) = fun x => g x - g (x + k) := by
      funext x
      simp only [Φ, g, hL, hk0, add_zero]
      ring
    rw [heq, integral_sub hg (hg.comp_add_right k), integral_add_right_eq_self, sub_self]
  have hint : Integrable (fun y => ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂ν) ν := by
    simp only [hzero]
    exact integrable_zero _ _ _
  have key := hP Φ hΦc hΦs hint 0
  simp only [hzero, zero_mul, integral_zero, neg_zero] at key
  have h0 : bump 0 = 1 := bump.one_of_mem_closedBall (by simp; positivity)
  have h1 : bump k = 0 := by
    apply Function.notMem_support.mp
    rw [bump.support_eq]
    simp
    exact le_rfl
  simp [Φ, ψ, h0, h1] at key

private theorem measure_eq_sqrt_abs_det_smul_volume_of_inversion (ν : Measure W) [ν.IsAddHaarMeasure] (A : W →ₗ[ℝ] W)
    (hdet : LinearMap.det A ≠ 0)
    (hP : ∀ Φ : W → ℂ, Continuous Φ → HasCompactSupport Φ →
      Integrable (fun y => ∫ x, Φ x * ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) ∂ν) ν → ∀ z : W,
      ∫ y, (∫ x, Φ x * ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) ∂ν) * ((𝐞 ⟪A y, z⟫ : Circle) : ℂ) ∂ν = Φ (-z)) :
    ν = ENNReal.ofReal (Real.sqrt |LinearMap.det A|) • volume := by
  set s := ν.addHaarScalarFactor volume with hsdef
  have hs : 0 < s := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν volume
  have hν : ν = (s : ENNReal) • volume := by
    rw [← ENNReal.smul_def]
    exact Measure.isAddLeftInvariant_eq_smul ν volume
  let bump : ContDiffBump (0 : W) := ⟨1, 2, one_pos, one_lt_two⟩
  have h0 : bump 0 = 1 := bump.one_of_mem_closedBall (by simp; exact bump.rIn_pos.le)
  let Φ : W → ℂ := fun x => ((bump x : ℝ) : ℂ)
  have hΦs : HasCompactSupport Φ := bump.hasCompactSupport.comp_left Complex.ofReal_zero
  have hΦd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ :=
    Complex.ofRealCLM.contDiff.comp (bump.contDiff (n := ⊤))
  let S : SchwartzMap W ℂ := hΦs.toSchwartzMap hΦd
  have hSΦ : (S : W → ℂ) = Φ := rfl
  let g : W → ℂ := 𝓕⁻ Φ
  have hgS : g = ⇑(𝓕⁻ S : SchwartzMap W ℂ) := by rw [SchwartzMap.fourierInv_coe, hSΦ]
  have hgi : Integrable g := by rw [hgS]; exact (𝓕⁻ S : SchwartzMap W ℂ).integrable
  have hgg : ∫ v, g v = 1 := by
    have h1 : 𝓕⁻ g 0 = ∫ v, g v := by simp [Real.fourierInv_eq]
    have h2 : 𝓕⁻ g 0 = Φ 0 := by
      rw [Real.fourierInv_eq_fourier_neg, hgS, ← SchwartzMap.fourier_coe,
        FourierInvPair.fourier_fourierInv_eq, hSΦ, neg_zero]
    rw [← h1, h2]
    simp [Φ, h0]
  have hAc : Continuous A := A.continuous_of_finiteDimensional
  have hAm : AEMeasurable A volume := hAc.measurable.aemeasurable
  have hmapA : (volume : Measure W).map A = ENNReal.ofReal |(LinearMap.det A)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet
  have hgim : Integrable g ((volume : Measure W).map A) := by
    rw [hmapA]
    exact hgi.smul_measure ENNReal.ofReal_ne_top
  have hgA : Integrable (fun y => g (A y)) volume :=
    (integrable_map_measure hgim.aestronglyMeasurable hAm).mp hgim
  have hinner : ∀ y, ∫ x, Φ x * ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) ∂ν = (s : ℝ) • g (A y) := by
    intro y
    show _ = (s : ℝ) • 𝓕⁻ Φ (A y)
    rw [hν, integral_smul_measure, ENNReal.coe_toReal, Real.fourierInv_eq]
    congr 1
    congr 1
    funext x
    rw [Circle.smul_def, smul_eq_mul, mul_comm]
  have hint : Integrable (fun y => ∫ x, Φ x * ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) ∂ν) ν := by
    simp only [hinner]
    rw [hν]
    exact (hgA.smul (s : ℝ)).smul_measure ENNReal.coe_ne_top
  have hcomp : ∫ y, g (A y) = (ENNReal.ofReal |(LinearMap.det A)⁻¹|).toReal • (1 : ℂ) := by
    rw [← integral_map hAm hgim.aestronglyMeasurable, hmapA, integral_smul_measure, hgg]
  have key := hP Φ hΦd.continuous hΦs hint 0
  simp only [hinner, inner_zero_right, AddChar.map_zero_eq_one, Circle.coe_one, mul_one] at key
  rw [hν, integral_smul_measure, integral_smul, hcomp, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (abs_nonneg _)] at key
  have hreal : (s : ℝ) * ((s : ℝ) * |(LinearMap.det A)⁻¹|) = 1 := by
    have h2 : Φ (-0) = 1 := by simp [Φ, h0]
    rw [h2] at key
    have := congrArg Complex.re key
    simp only [Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one] at this
    exact this
  have hdpos : 0 < |LinearMap.det A| := abs_pos.mpr hdet
  have hsq : (s : ℝ) ^ 2 = |LinearMap.det A| := by
    rw [abs_inv] at hreal
    field_simp at hreal
    nlinarith [hreal]
  rw [hν]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal, ← hsq, Real.sqrt_sq s.coe_nonneg]

theorem dens_generic (μ : Measure V) (χ : V → V → ℂ) (hμ : SelfDual μ χ) (e : V ≃ₜ W)
    (he : ∀ x y, e (x + y) = e x + e y) (β : W → W → ℝ)
    (hχ : ∀ x y, χ (e.symm x) (e.symm y) = ((𝐞 (β x y) : Circle) : ℂ))
    (hL : ∀ x x' y, β (x + x') y = β x y + β x' y) (hR : ∀ x y y', β x (y + y') = β x y + β x y')
    (hcL : ∀ y, Continuous fun x => β x y) (hcR : ∀ x, Continuous fun y => β x y)
    (hS : ∀ x y, β x y = β y x) (b : OrthonormalBasis ι ℝ W) :
    μ.map e = ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j => β (b i) (b j)).det|) • volume := by
  obtain ⟨A, hA, hdet⟩ := exists_linearMap_inner_eq_and_det_eq_gram_det β hL hR hcL hcR b
  have hP := fun Φ hc hs hi z => integral_fourier_map_eq_neg_of_integrable μ χ hμ e he β hχ Φ hc hs hi z
  haveI : μ.IsAddHaarMeasure := hμ.1
  haveI : (μ.map e).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map μ (AddMonoidHom.mk' e he) e.continuous e.surjective
      e.isClosedEmbedding.tendsto_cocompact
  by_cases hd : (Matrix.of fun i j => β (b i) (b j)).det = 0
  · exfalso
    rw [← hdet] at hd
    obtain ⟨k, hkker, hk⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hd)
    have hk0 : ∀ y, β k y = 0 := fun y => by
      rw [hS, hA, LinearMap.mem_ker.mp hkker, inner_zero_right]
    exact false_of_degenerate_of_fourier_inversion (μ.map e) β hL hcL k hk hk0 hP
  · rw [← hdet] at hd ⊢
    apply measure_eq_sqrt_abs_det_smul_volume_of_inversion (μ.map e) A hd
    intro Φ hc hs hi z
    have hβ' : ∀ y z, ⟪A y, z⟫ = β y z := fun y z => by rw [hS, hA, real_inner_comm]
    simp only [← hA, hβ'] at hi ⊢
    exact hP Φ hc hs hi z

end PI.AprimeInfW.GenericDensity
end
end

noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct RealInnerProductSpace FourierTransform
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

section Coord

variable {D : D7} (X : HidaSetting D)

def matCoord : (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) → Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) ≃ₜ EuclideanSpace ℝ (Fin (D.R.rS + 1 + D.R.rS) × Fin (D.R.rS + 1 + D.R.rS) × Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) × InfinitePlace X.B.I.F) :=
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hReal : ∀ v : InfinitePlace X.B.I.F, v.IsReal := X.B.I.cm.totReal.isReal
  (Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ =>
    (tensCoord (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F)).trans
      (Homeomorph.piCongrRight fun _ => ainfReal (totReal_of X))).trans (flat4 _ _ _ _)

theorem matCoord_add (x y : (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) → Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) : matCoord X (x + y) = matCoord X x + matCoord X y := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  simp only [matCoord, Homeomorph.trans_apply]
  rw [← flatten_four_add]
  congr 1
  funext a i k
  simp only [Homeomorph.piCongrRight_apply, Homeomorph.trans_apply, Pi.add_apply]
  rw [tensCoord_add]
  exact ainfReal_add (totReal_of X) _ _

def scalI (t : ℝ) : Ainf X.B.I.F := (ainfReal (totReal_of X)).symm fun _ => t

theorem matCoord_scal (t : ℝ) (S : (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) → Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
    matCoord X (fun a b => algebraMap (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) (scalI X t) * S a b) =
      t • matCoord X S := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  simp only [matCoord, Homeomorph.trans_apply]
  have hf : ∀ f : Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) → Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) → InfinitePlace X.B.I.F → ℝ,
      flat4 _ _ _ _ (t • f) = t • flat4 _ _ _ _ f := by
    intro f
    show (EuclideanSpace.equiv _ ℝ).symm _ = t • (EuclideanSpace.equiv _ ℝ).symm _
    rw [← map_smul]
    rfl
  rw [← hf]
  congr 1
  funext a i k v
  simp only [Homeomorph.piCongrRight_apply, Homeomorph.trans_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Algebra.smul_def]
  have h1 : tensCoord (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (scalI X t • S a i) =
      scalI X t • tensCoord (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (S a i) :=
    map_smul (Module.Free.chooseBasis (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)).equivFun _ _
  rw [h1]
  show complReal v ((totReal_of X) v) ((scalI X t) v * _) = t * _
  rw [show complReal v ((totReal_of X) v) ((scalI X t) v * tensCoord (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (S a i) k v) =
      complReal v ((totReal_of X) v) ((scalI X t) v) *
        complReal v ((totReal_of X) v) (tensCoord (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (S a i) k v) from
    map_mul (InfinitePlace.Completion.ringEquivRealOfIsReal ((totReal_of X) v)) _ _]
  congr 1
  show ainfReal (totReal_of X) (scalI X t) v = t
  simp [scalI]

theorem herm_scal (t : ℝ) (S : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) :
    Matrix.of (fun a b => algebraMap (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) (scalI X t) * (S : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) a b) ∈ HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) := by
  intro a b
  have hS := S.2 a b
  simp only [Matrix.of_apply, map_mul]
  rw [hS]
  congr 1
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem matCoord_symm_add (c c' : EuclideanSpace ℝ (Fin (D.R.rS + 1 + D.R.rS) × Fin (D.R.rS + 1 + D.R.rS) × Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) × InfinitePlace X.B.I.F)) :
    (matCoord X).symm (c + c') = (matCoord X).symm c + (matCoord X).symm c' := by
  apply (matCoord X).injective; rw [matCoord_add]; simp

theorem matCoord_symm_zero : (matCoord X).symm 0 = 0 := by
  apply (matCoord X).injective
  have h := matCoord_add X 0 0
  simp only [add_zero] at h
  rw [Homeomorph.apply_symm_apply]
  exact (by simpa using h : matCoord X 0 = 0).symm

theorem matCoord_symm_smul (t : ℝ) (c : EuclideanSpace ℝ (Fin (D.R.rS + 1 + D.R.rS) × Fin (D.R.rS + 1 + D.R.rS) × Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) × InfinitePlace X.B.I.F)) :
    (matCoord X).symm (t • c) = fun a b => algebraMap (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) (scalI X t) * (matCoord X).symm c a b := by
  apply (matCoord X).injective; rw [matCoord_scal]; simp

def Wh : Submodule ℝ (EuclideanSpace ℝ (Fin (D.R.rS + 1 + D.R.rS) × Fin (D.R.rS + 1 + D.R.rS) × Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) × InfinitePlace X.B.I.F)) where
  carrier := {c | Matrix.of ((matCoord X).symm c) ∈ HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)}
  add_mem' := by
    intro c c' hc hc'
    show Matrix.of ((matCoord X).symm (c + c')) ∈ HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)
    rw [matCoord_symm_add, ← Matrix.of_add_of]
    exact add_mem hc hc'
  zero_mem' := by
    show Matrix.of ((matCoord X).symm 0) ∈ HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)
    rw [matCoord_symm_zero, Matrix.of_zero]
    exact zero_mem _
  smul_mem' := by
    intro t c hc
    show Matrix.of ((matCoord X).symm (t • c)) ∈ HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)
    rw [matCoord_symm_smul]
    exact herm_scal X t ⟨_, hc⟩

theorem hermCoord_mem (S : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) : matCoord X (Matrix.of.symm (S : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))) ∈ Wh X := by
  show Matrix.of ((matCoord X).symm (matCoord X (Matrix.of.symm (S : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))))) ∈ HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)
  rw [Homeomorph.symm_apply_apply, Equiv.apply_symm_apply]; exact S.2

def hermCoord : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) ≃ₜ Wh X where
  toFun S := ⟨matCoord X (Matrix.of.symm (S : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))), hermCoord_mem X S⟩
  invFun w := ⟨Matrix.of ((matCoord X).symm w), w.2⟩
  left_inv S := by
    apply Subtype.ext
    simp only [Homeomorph.symm_apply_apply]
    ext i j
    rfl
  right_inv w := by apply Subtype.ext; simp
  continuous_toFun := ((matCoord X).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((matCoord X).symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem hermCoord_add (S T : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) : hermCoord X (S + T) = hermCoord X S + hermCoord X T := by
  apply Subtype.ext
  exact matCoord_add X (Matrix.of.symm (S : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))) (Matrix.of.symm (T : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)))

theorem hermCoord_symm_add (x y : Wh X) :
    (hermCoord X).symm (x + y) = (hermCoord X).symm x + (hermCoord X).symm y := by
  apply (hermCoord X).injective
  rw [hermCoord_add X]
  rw [(hermCoord X).apply_symm_apply, (hermCoord X).apply_symm_apply,
    (hermCoord X).apply_symm_apply]

end Coord

section Pair

variable {D : D7} (X : HidaSetting D)

theorem pairHerm_addL (S S' T : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) :
    pairHerm (Ainf X.B.I.F) X.B.I.cm.sig _ (S + S') T =
      pairHerm (Ainf X.B.I.F) X.B.I.cm.sig _ S T + pairHerm (Ainf X.B.I.F) X.B.I.cm.sig _ S' T := by
  simp only [pairHerm, AddSubgroup.coe_add, Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _), mul_add]

theorem pairHerm_addR (S T T' : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) :
    pairHerm (Ainf X.B.I.F) X.B.I.cm.sig _ S (T + T') =
      pairHerm (Ainf X.B.I.F) X.B.I.cm.sig _ S T + pairHerm (Ainf X.B.I.F) X.B.I.cm.sig _ S T' := by
  simp only [pairHerm, AddSubgroup.coe_add, Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem pairHerm_symm (S T : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) :
    pairHerm (Ainf X.B.I.F) X.B.I.cm.sig _ S T = pairHerm (Ainf X.B.I.F) X.B.I.cm.sig _ T S := by
  simp only [pairHerm]
  congr 2
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _

theorem continuous_pairHerm_leftP (T : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) :
    Continuous fun S : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) => pairHerm (Ainf X.B.I.F) X.B.I.cm.sig _ S T := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  show Continuous fun S : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) => algebraMap X.B.I.F (Ainf X.B.I.F) (1 / 2) *
    Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)
      (∑ a, ∑ b, (S : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) a b * (T : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) b a)
  refine continuous_const.mul ((continuous_traceP X).comp ?_)
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  exact (Continuous.matrix_elem continuous_subtype_val a b).mul continuous_const

def sumReI (a : Ainf X.B.I.F) : ℝ :=
  ∑ w : InfinitePlace X.B.I.F, (InfinitePlace.Completion.extensionEmbedding w (a w)).re

theorem sumReI_add (a b : Ainf X.B.I.F) : sumReI X (a + b) = sumReI X a + sumReI X b := by
  simp only [sumReI]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [show (a + b) w = a w + b w from rfl, map_add (f := _), Complex.add_re]

theorem continuous_sumReI : Continuous (sumReI X) :=
  continuous_finsetSum _ fun w _ => Complex.continuous_re.comp
    ((InfinitePlace.Completion.isometry_extensionEmbedding (v := w)).continuous.comp (continuous_apply w))

def betaH (x y : Wh X) : ℝ := sumReI X (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) ((hermCoord X).symm x) ((hermCoord X).symm y))

end Pair

def DensNu : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    νinf.map (hermCoord X) = ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j =>
      betaH X (stdOrthonormalBasis ℝ (Wh X) i) (stdOrthonormalBasis ℝ (Wh X) j)).det|) • volume

theorem densNu_holds : DensNu := by
  intro D X u' ψ hT μinf νinf fibInf hP
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : BorelSpace (HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) := ⟨rfl⟩
  have hS := hP.2.2.1
  have hν : SelfDual νinf (fun S T : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) => psiInf X.B.I.F ψ (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) S T)) := hP.2.2.2.2.2.1
  have h1 : ∀ x y : Wh X, (fun S T : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) => psiInf X.B.I.F ψ (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) S T)) ((hermCoord X).symm x) ((hermCoord X).symm y) = ((𝐞 (betaH X x y) : Circle) : ℂ) := by
    intro x y
    simp only [betaH, sumReI]
    rw [psiInf_eq ψ hS, Real.fourierChar_apply]
    push_cast
    ring_nf
  have h2 : ∀ x x' y : Wh X, betaH X (x + x') y = betaH X x y + betaH X x' y := by
    intro x x' y
    simp only [betaH, hermCoord_symm_add, pairHerm_addL, sumReI_add]
  have h3 : ∀ x y y' : Wh X, betaH X x (y + y') = betaH X x y + betaH X x y' := by
    intro x y y'
    simp only [betaH, hermCoord_symm_add, pairHerm_addR, sumReI_add]
  have h4 : ∀ y : Wh X, Continuous fun x => betaH X x y := fun y =>
    (continuous_sumReI X).comp ((continuous_pairHerm_leftP X _).comp (hermCoord X).symm.continuous)
  have h6 : ∀ x y : Wh X, betaH X x y = betaH X y x := by
    intro x y
    simp only [betaH]
    rw [pairHerm_symm]
  have h5 : ∀ x : Wh X, Continuous fun y => betaH X x y := by
    intro x
    have e : (fun y => betaH X x y) = fun y => betaH X y x := funext fun y => h6 x y
    rw [e]
    exact h4 x
  exact PI.AprimeInfW.GenericDensity.dens_generic νinf (fun S T : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) => psiInf X.B.I.F ψ (pairHerm (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) S T)) hν (hermCoord X) (hermCoord_add X) (betaH X) h1 h2 h3 h4 h5 h6
    (stdOrthonormalBasis ℝ (Wh X))

end PI.AprimeInfW
