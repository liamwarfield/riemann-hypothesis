module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MemPolarizationStabilizerOfDualPair

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SchwartzFunctionSlopeEstimate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.SchwartzSlope
open Filter Topology
open scoped SchwartzMap RealInnerProductSpace
theorem schwartz_coordinate_slope_bound (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (l : Type) [Fintype l] [DecidableEq l]
    (A : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)) (T : ℝ → GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l)
    (hA : ∀ w, Continuous fun t => A t w) (hT : ∀ s t f, T (s + t) f = T s (T t f)) (hT0 : ∀ f, T 0 f = f)
    (hI : ∀ t w (f f₁ : GlobalTheory.RealWeil.Sch l), ⇑f₁ = GlobalTheory.RealWeil.rhoFun w ⇑f →
      ⇑(T t f₁) = GlobalTheory.RealWeil.rhoFun (A t w) ⇑(T t f))
    (hiso : ∀ t f, ∫ x, ‖T t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) (hpt : ∀ f y, Continuous fun t => T t f y) :
    ∀ f, ∃ g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (𝓝[≠] 0) (𝓝 g) := by
  obtain ⟨hs, hgrp, h0⟩ := GlobalTheory.T.symplectic_and_flow_of_intertwining_unitary l A T hT hT0 hI hiso
  have hT0' : T 0 = LinearMap.id := LinearMap.ext hT0
  have hTadd : ∀ s t, T (s + t) = T s ∘ₗ T t := fun s t => LinearMap.ext (hT s t)
  have hiso' : ∀ t h, ∫⁻ x, ‖T t h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2 := fun t h =>
    lintegral_of_integral l _ _ (hiso t h)
  obtain ⟨X, hsp, hB⟩ : ∃ X : Matrix (l ⊕ l) (l ⊕ l) ℝ, X ∈ LieAlgebra.Symplectic.sp l ℝ ∧
      ∀ t w, NormedSpace.exp (t • X) *ᵥ w = A t w := by
    cases isEmpty_or_nonempty l with
    | inl hl => exact ⟨0, zero_mem _, fun t w => Subsingleton.elim _ _⟩
    | inr hl =>
      let M : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ := fun t => LinearMap.toMatrix' (A t)
      have hM : ∀ t w, M t *ᵥ w = A t w := fun t w => LinearMap.toMatrix'_mulVec (A t) w
      have hMc : Continuous M := by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [M, LinearMap.toMatrix'_apply]
        exact (continuous_apply i).comp (hA _)
      have hM0 : M 0 = 1 := by
        have : A 0 = LinearMap.id := LinearMap.ext h0
        simp only [M, this, LinearMap.toMatrix'_id]
      have hMm : ∀ s t, M (s + t) = M s * M t := by
        intro s t
        have : A (s + t) = (A s).comp (A t) := LinearMap.ext (hgrp s t)
        simp only [M, this, LinearMap.toMatrix'_comp]
      obtain ⟨X, hX⟩ := GlobalTheory.T.continuous_matrix_oneParameterGroup_eq_exp _ M hMc hM0 hMm
      have hsp : X ∈ LieAlgebra.Symplectic.sp l ℝ := by
        refine GlobalTheory.T.mem_symplecticLieAlgebra_of_exp_smul_mem_symplecticGroup l X fun t => ?_
        obtain ⟨N, hN⟩ := GlobalTheory.exists_symplecticGroup_of_sympl l (A t) (hs t)
        have e : Matrix.toLin' (N : Matrix (l ⊕ l) (l ⊕ l) ℝ) = A t := LinearMap.ext fun w => by
          rw [Matrix.toLin'_apply, hN]
        have e2 : (N : Matrix (l ⊕ l) (l ⊕ l) ℝ) = M t := by
          simp only [M, ← e, LinearMap.toMatrix'_toLin']
        rw [← hX t, ← e2]
        exact N.2
      exact ⟨X, hsp, fun t w => by rw [← hX, hM]⟩
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.T.metaplectic_lift_scalar_derivative_eq hP l X hsp T hT0' hTadd
    (fun t w h h₁ hh => by rw [hI t w h h₁ hh, hB]) hiso' hpt
  exact fun f => ⟨_, ha f⟩
open GlobalTheory.ArchUniq GlobalTheory.RealWeil in
theorem schwartz_slope_bound (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (P : V → V → ℝ) (hPp : IsPairing P)
    (A : ℝ → (V × V) →ₗ[ℝ] (V × V)) (T : ℝ → 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ))
    (hAc : ∀ v, Continuous fun t => A t v) (hTadd : ∀ s t f, T (s + t) f = T s (T t f)) (hT0 : ∀ f, T 0 f = f)
    (hTi : ∀ t v (f f₁ : 𝓢(V, ℂ)), ⇑f₁ = schrF P v ⇑f → ⇑(T t f₁) = schrF P (A t v) ⇑(T t f))
    (hTl2 : ∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) (hTc : ∀ f y, Continuous fun t => T t f y) :
    ∀ f, ∃ g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (𝓝[≠] 0) (𝓝 g) := by
  obtain ⟨C, φ, hp, hq⟩ := SchrTransport.coords P hPp (Module.finrank ℝ V) rfl
  have hS := SchrTransport.schr_coords P C φ hp hq
  let toE : 𝓢(V, ℂ) →L[ℂ] Sch (Fin (Module.finrank ℝ V)) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C.symm
  let toV : Sch (Fin (Module.finrank ℝ V)) →L[ℂ] 𝓢(V, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C
  have htoE : ∀ g, ⇑(toE g) = ⇑g ∘ ⇑C.symm := fun g => rfl
  have htoV : ∀ h, ⇑(toV h) = ⇑h ∘ ⇑C := fun h => rfl
  have hVE : ∀ g, toV (toE g) = g := fun g => by ext x; simp [htoE, htoV]
  have hEV : ∀ h, toE (toV h) = h := fun h => by ext x; simp [htoE, htoV]
  let T' : ℝ → Sch (Fin (Module.finrank ℝ V)) →ₗ[ℂ] Sch (Fin (Module.finrank ℝ V)) :=
    fun t => toE.toLinearMap ∘ₗ T t ∘ₗ toV.toLinearMap
  let A' : ℝ → (Fin (Module.finrank ℝ V) ⊕ Fin (Module.finrank ℝ V) → ℝ) →ₗ[ℝ]
      (Fin (Module.finrank ℝ V) ⊕ Fin (Module.finrank ℝ V) → ℝ) :=
    fun t => φ.toLinearMap ∘ₗ A t ∘ₗ φ.symm.toLinearMap
  have hT' : ∀ t h, T' t h = toE (T t (toV h)) := fun t h => rfl
  obtain ⟨k, hk, hint⟩ := SchrTransport.haar_coords μ C
  have c1 : ∀ w, Continuous fun t => A' t w := by
    intro w
    exact (φ.toLinearMap.continuous_of_finiteDimensional).comp (hAc (φ.symm w))
  have c2 : ∀ s t f, T' (s + t) f = T' s (T' t f) := by
    intro s t h
    simp only [hT', hVE, hTadd]
  have c3 : ∀ f, T' 0 f = f := by
    intro h
    simp [hT', hT0, hEV]
  have c4 : ∀ t w (f f₁ : Sch (Fin (Module.finrank ℝ V))), ⇑f₁ = rhoFun w ⇑f →
      ⇑(T' t f₁) = rhoFun (A' t w) ⇑(T' t f) := by
    intro t w f f₁ hf
    have e1 : ⇑(toV f₁) = schrF P (φ.symm w) ⇑(toV f) := by
      funext x
      have := congrFun (hS (φ.symm w) ⇑f) x
      simp only [Function.comp_apply, LinearEquiv.apply_symm_apply] at this
      simp only [htoV, Function.comp_apply, hf]
      exact this.symm
    have e2 := hTi t _ _ _ e1
    rw [hT' t f₁, hT' t f, htoE, htoE, e2]
    obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℂ, ⇑(T t (toV f)) = G ∘ ⇑C :=
      ⟨⇑(T t (toV f)) ∘ ⇑C.symm, by ext x; simp⟩
    have hGC : (G ∘ ⇑C) ∘ ⇑C.symm = G := by funext x; simp
    rw [hG, hS, hGC]
    funext x
    simp [A']
  have c5 : ∀ t f, ∫ x, ‖T' t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
    intro t h
    have e := hTl2 t (toV h)
    rw [hint, hint] at e
    simp only [htoV, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] at e
    exact mul_left_cancel₀ hk.ne' e
  have c6 : ∀ f y, Continuous fun t => T' t f y := by
    intro h y
    exact hTc (toV h) (C.symm y)
  have hlim := _root_.GlobalTheory.SchwartzSlope.schwartz_coordinate_slope_bound hP (Fin (Module.finrank ℝ V)) A' T' c1 c2 c3 c4 c5 c6
  intro f
  obtain ⟨g, hg⟩ := hlim (toE f)
  refine ⟨toV g, ?_⟩
  have e : (fun t : ℝ => t⁻¹ • (T t f - f)) =
      fun t : ℝ => (toV.restrictScalars ℝ) (t⁻¹ • (T' t (toE f) - toE f)) := by
    funext t
    rw [map_smul, map_sub]
    simp only [ContinuousLinearMap.coe_restrictScalars', hT', hVE]
  rw [e]
  exact ((toV.restrictScalars ℝ).continuous.tendsto g).comp hg
theorem lift_splits_locally : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W), IsCMExt F E σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W,
    ∀ T : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
    (∀ t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(T t f)) →
    (∀ s t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), T (s + t) f = T s (T t f)) →
    (∀ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), T 0 f = f) →
    ∀ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), ∃ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      Filter.Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (nhdsWithin 0 {0}ᶜ) (nhds g) := by
  classical
  intro hP F E _ _ _ _ _ σ n d X W M ψ χX χW om hCM hψ hW γ hγ T hT hadd h0
  obtain ⟨A, hAc, hA⟩ := GlobalTheory.T.archimedeanLine_intertwines_realSchrodinger M ψ χX χW om hψ hW γ hγ T hT
  haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  let μ : Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Measure.addHaar
  have hiso : ∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := fun t f =>
    GlobalTheory.T.weil_representation_integral_action M ψ χX χW om hW μ inferInstance (γ (Multiplicative.ofAdd t)) f (T t f) (hT t f)
  obtain ⟨hc1, -⟩ := GlobalTheory.T.archimedeanOneParameterFamily_continuous M ψ χX χW om hW γ hγ T hT
  have trace_pi_real_eq_sum' {ι : Type} [Fintype ι] (f : ι → ℝ) :
      Algebra.trace ℝ (ι → ℝ) f = ∑ i, f i := by
    rw [Algebra.trace_eq_matrix_trace (Pi.basisFun ℝ ι)]
    simp [Matrix.trace, Algebra.leftMulMatrix_eq_repr_mul, Pi.single_apply]

  have trace_pi_complex_eq_sum_two_mul_re {ι : Type} [Fintype ι] (f : ι → ℂ) :
      Algebra.trace ℝ (ι → ℂ) f = ∑ i, 2 * (f i).re := by
    rw [Algebra.trace_eq_matrix_trace (Pi.basis fun _ : ι => Complex.basisOneI)]
    simp [Matrix.trace, Algebra.leftMulMatrix_eq_repr_mul, Fintype.sum_sigma, Pi.single_apply, Fin.sum_univ_two,
      Complex.coe_basisOneI, Complex.coe_basisOneI_repr]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

  have eq_zero_of_trace (x : mixedEmbedding.mixedSpace F)
      (h : ∀ b, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x * b) = 0) : x = 0 := by
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · have h1 := h (Pi.single w 1, 0)
      rw [Algebra.trace_prod_apply, trace_pi_real_eq_sum', trace_pi_complex_eq_sum_two_mul_re] at h1
      simpa [Pi.single_apply] using h1
    · have h1 := h (0, Pi.single w (star (x.2 w)))
      rw [Algebra.trace_prod_apply, trace_pi_real_eq_sum', trace_pi_complex_eq_sum_two_mul_re] at h1
      have h2 : (x.2 w).re * (x.2 w).re + (x.2 w).im * (x.2 w).im = 0 := by
        simpa [Pi.single_apply, apply_ite Complex.re, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', Complex.star_def,
          Complex.mul_conj] using h1
      have hre : (x.2 w).re = 0 := by nlinarith [mul_self_nonneg (x.2 w).re, mul_self_nonneg (x.2 w).im]
      have him : (x.2 w).im = 0 := by nlinarith [mul_self_nonneg (x.2 w).re, mul_self_nonneg (x.2 w).im]
      show x.2 w = 0
      exact Complex.ext hre him

  have hPair : GlobalTheory.ArchUniq.IsPairing (GlobalTheory.ArchUniq.trP F (Fin n × Fin d)) := by
    exact {
      addL x x' y := by
        simp only [GlobalTheory.ArchUniq.trP, Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)]
      addR x y y' := by
        simp only [GlobalTheory.ArchUniq.trP, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]
      smulL c x y := by
        simp only [GlobalTheory.ArchUniq.trP, Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul, smul_eq_mul]
      smulR c x y := by
        simp only [GlobalTheory.ArchUniq.trP, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul, smul_eq_mul]
      nondegL x hx := by
        funext i
        apply eq_zero_of_trace
        intro b
        have h := hx (Pi.single i b)
        simpa [GlobalTheory.ArchUniq.trP, Pi.single_apply, mul_ite, Finset.sum_ite_eq'] using h
      nondegR y hy := by
        funext i
        apply eq_zero_of_trace
        intro b
        have h := hy (Pi.single i b)
        simpa [GlobalTheory.ArchUniq.trP, Pi.single_apply, ite_mul, Finset.sum_ite_eq', mul_comm] using h
    }

  exact _root_.GlobalTheory.SchwartzSlope.schwartz_slope_bound hP (Fin n × Fin d → mixedEmbedding.mixedSpace F) μ _ hPair A T hAc hadd h0 hA hiso hc1
end GlobalTheory.SchwartzSlope
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_function_slope_estimate : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W), IsCMExt F E σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W,
    ∀ T : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
    (∀ t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(T t f)) →
    (∀ s t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), T (s + t) f = T s (T t f)) →
    (∀ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), T 0 f = f) →
    ∀ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), ∃ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      Filter.Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (nhdsWithin 0 {0}ᶜ) (nhds g) := by
  first | exact @_root_.GlobalTheory.SchwartzSlope.lift_splits_locally | exact _root_.GlobalTheory.SchwartzSlope.lift_splits_locally | (intros; apply _root_.GlobalTheory.SchwartzSlope.lift_splits_locally <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanWeilRepresentationContinuous
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.ArchCont
open scoped SchwartzMap
theorem continuous_of_intertwining_operator (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (l : Type) [Fintype l] [DecidableEq l]
    (A : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)) (T : ℝ → GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l)
    (hT : ∀ s t f, T (s + t) f = T s (T t f)) (hT0 : ∀ f, T 0 f = f)
    (hI : ∀ t w (f f₁ : GlobalTheory.RealWeil.Sch l), ⇑f₁ = GlobalTheory.RealWeil.rhoFun w ⇑f →
      ⇑(T t f₁) = GlobalTheory.RealWeil.rhoFun (A t w) ⇑(T t f))
    (hiso : ∀ t f, ∫ x, ‖T t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) (t : ℝ) : Continuous (T t) := by
  obtain ⟨hs, -, -⟩ := GlobalTheory.T.symplectic_and_flow_of_intertwining_unitary l A T hT hT0 hI hiso
  rcases isEmpty_or_nonempty l with hl | hl
  · obtain ⟨f0, hf0⟩ := GlobalTheory.MetaplecticScalarDeriv.exists_schwartz_one l
    have hsub : ∀ x : EuclideanSpace ℝ l, x = 0 := fun x => by
      ext i
      exact isEmptyElim i
    have hdec : ∀ f : GlobalTheory.RealWeil.Sch l, f = f 0 • f0 := by
      intro f
      ext x
      rw [hsub x, SchwartzMap.smul_apply, hf0, smul_eq_mul, mul_one]
    have e : ⇑(T t) = fun f => f 0 • T t f0 := by
      funext f
      conv_lhs => rw [hdec f]
      exact map_smul _ _ _
    rw [e]
    exact (GlobalTheory.MetaplecticScalarDeriv.continuous_eval l 0).smul continuous_const
  · obtain ⟨G, _, _, _, pr, om, omS, ⟨-, hsurj, -⟩, -, h3, h4, -, -⟩ := hP.realMetaplecticRepresentation l
    obtain ⟨N, hN⟩ := GlobalTheory.exists_symplecticGroup_of_sympl l (A t) (hs t)
    obtain ⟨g, hg⟩ := hsurj N
    have hmat : ∀ w, A t ((pr g⁻¹ : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) = w := by
      intro w
      have e : pr g * pr g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      have e' : (pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) * (pr g⁻¹ : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 1 :=
        congrArg (fun x : Matrix.symplecticGroup l ℝ => (x : Matrix (l ⊕ l) (l ⊕ l) ℝ)) e
      rw [← hN, ← hg, Matrix.mulVec_mulVec, e', Matrix.one_mulVec]
    have hU1 : ∀ (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
        ⇑((T t ∘ₗ (omS g⁻¹ : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l)) h₁) =
          GlobalTheory.RealWeil.rhoFun w ⇑((T t ∘ₗ (omS g⁻¹ : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l)) h) := by
      intro w h h₁ hh
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [hI t _ _ _ (GlobalTheory.MetaplecticScalarDeriv.intertwine_fun l _ (om g⁻¹) (omS g⁻¹) (h3 _) (h4 _) w h h₁ hh), hmat]
    have hU2 : ∀ h : GlobalTheory.RealWeil.Sch l,
        ∫⁻ x, ‖(T t ∘ₗ (omS g⁻¹ : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l)) h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2 := by
      intro h
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [lintegral_of_integral _ _ (hiso t _), GlobalTheory.MetaplecticScalarDeriv.lintegral_iso l (om g⁻¹) (omS g⁻¹) (h4 _)]
    obtain ⟨a, -, ha⟩ := _root_.GlobalTheory.T.real_weil_representation_schur_scalar hP l _ hU1 hU2
    have e : ⇑(T t) = fun f => a • omS g f := by
      funext f
      have h1 := ha (omS g f)
      have e2 : omS g⁻¹ (omS g f) = f := by
        rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one, ContinuousLinearMap.one_apply]
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, e2] at h1
      exact h1
    rw [e]
    exact (omS g).continuous.const_smul a
end GlobalTheory.ArchCont
namespace GlobalTheory.ArchCont
open scoped SchwartzMap RealInnerProductSpace
theorem continuous_schrodinger_model_action (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (P : V → V → ℝ) (hp : GlobalTheory.ArchUniq.IsPairing P)
    (A : ℝ → (V × V) →ₗ[ℝ] (V × V)) (T : ℝ → 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ))
    (hTadd : ∀ s t f, T (s + t) f = T s (T t f)) (hT0 : ∀ f, T 0 f = f)
    (hTi : ∀ t v (f f₁ : 𝓢(V, ℂ)), ⇑f₁ = GlobalTheory.ArchUniq.schrF P v ⇑f →
      ⇑(T t f₁) = GlobalTheory.ArchUniq.schrF P (A t v) ⇑(T t f))
    (hTl2 : ∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) (t : ℝ) : Continuous (T t) := by
  obtain ⟨C, φ, hp', hq⟩ := GlobalTheory.ArchUniq.SchrTransport.coords P hp _ rfl
  have hS := GlobalTheory.ArchUniq.SchrTransport.schr_coords P C φ hp' hq
  let toE : 𝓢(V, ℂ) →L[ℂ] GlobalTheory.RealWeil.Sch (Fin (Module.finrank ℝ V)) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C.symm
  let toV : GlobalTheory.RealWeil.Sch (Fin (Module.finrank ℝ V)) →L[ℂ] 𝓢(V, ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C
  have htoE : ∀ g, ⇑(toE g) = ⇑g ∘ ⇑C.symm := fun g => rfl
  have htoV : ∀ h, ⇑(toV h) = ⇑h ∘ ⇑C := fun h => rfl
  have hVE : ∀ g, toV (toE g) = g := fun g => by ext x; simp [htoE, htoV]
  have hEV : ∀ h, toE (toV h) = h := fun h => by ext x; simp [htoE, htoV]
  let T' : ℝ → GlobalTheory.RealWeil.Sch (Fin (Module.finrank ℝ V)) →ₗ[ℂ] GlobalTheory.RealWeil.Sch (Fin (Module.finrank ℝ V)) :=
    fun t => toE.toLinearMap ∘ₗ T t ∘ₗ toV.toLinearMap
  let A' : ℝ → (Fin (Module.finrank ℝ V) ⊕ Fin (Module.finrank ℝ V) → ℝ) →ₗ[ℝ]
      (Fin (Module.finrank ℝ V) ⊕ Fin (Module.finrank ℝ V) → ℝ) :=
    fun t => φ.toLinearMap ∘ₗ A t ∘ₗ φ.symm.toLinearMap
  have hT' : ∀ t h, T' t h = toE (T t (toV h)) := fun t h => rfl
  obtain ⟨k, hk, hint⟩ := GlobalTheory.ArchUniq.SchrTransport.haar_coords μ C
  have c2 : ∀ s t f, T' (s + t) f = T' s (T' t f) := by
    intro s t h
    simp only [hT', hVE, hTadd]
  have c3 : ∀ f, T' 0 f = f := by
    intro h
    simp [hT', hT0, hEV]
  have c4 : ∀ t w (f f₁ : GlobalTheory.RealWeil.Sch (Fin (Module.finrank ℝ V))), ⇑f₁ = GlobalTheory.RealWeil.rhoFun w ⇑f →
      ⇑(T' t f₁) = GlobalTheory.RealWeil.rhoFun (A' t w) ⇑(T' t f) := by
    intro t w f f₁ hf
    have e1 : ⇑(toV f₁) = GlobalTheory.ArchUniq.schrF P (φ.symm w) ⇑(toV f) := by
      funext x
      have := congrFun (hS (φ.symm w) ⇑f) x
      simp only [Function.comp_apply, LinearEquiv.apply_symm_apply] at this
      simp only [htoV, Function.comp_apply, hf]
      exact this.symm
    have e2 := hTi t _ _ _ e1
    rw [hT' t f₁, hT' t f, htoE, htoE, e2]
    obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℂ, ⇑(T t (toV f)) = G ∘ ⇑C :=
      ⟨⇑(T t (toV f)) ∘ ⇑C.symm, by ext x; simp⟩
    have hGC : (G ∘ ⇑C) ∘ ⇑C.symm = G := by funext x; simp
    rw [hG, hS, hGC]
    funext x
    simp [A']
  have c5 : ∀ t f, ∫ x, ‖T' t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
    intro t h
    have e := hTl2 t (toV h)
    rw [hint, hint] at e
    simp only [htoV, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] at e
    exact mul_left_cancel₀ hk.ne' e
  have hc := _root_.GlobalTheory.ArchCont.continuous_of_intertwining_operator hP (Fin (Module.finrank ℝ V)) A' T' c2 c3 c4 c5 t
  have e : ⇑(T t) = fun f => toV (T' t (toE f)) := by
    funext f
    simp only [hT', hVE]
  rw [e]
  exact toV.continuous.comp (hc.comp toE.continuous)
end GlobalTheory.ArchCont
open scoped Classical in
theorem GlobalTheory.ArchCont.continuous_weil_action_on_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W), IsCMExt F E σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W,
    ∀ T : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
    (∀ t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(T t f)) →
    (∀ s t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), T (s + t) f = T s (T t f)) →
    (∀ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), T 0 f = f) → ∀ t, Continuous (T t) := by
  intro hP F E _ _ _ _ _ σ n d X W M ψ χX χW om hCM hψ hW γ hγ T hT hadd h0 t
  obtain ⟨A, -, hA⟩ := GlobalTheory.T.archimedeanLine_intertwines_realSchrodinger M ψ χX χW om hψ hW γ hγ T hT
  haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  let μ : MeasureTheory.Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F) := MeasureTheory.Measure.addHaar
  have hiso : ∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := fun t f =>
    GlobalTheory.T.weil_representation_integral_action M ψ χX χW om hW μ inferInstance (γ (Multiplicative.ofAdd t)) f (T t f) (hT t f)
  exact _root_.GlobalTheory.ArchCont.continuous_schrodinger_model_action hP _ μ _ (GlobalTheory.ArchUniq.Coord.isPairing_trP (F := F) (Fin n × Fin d)) A T
    hadd h0 hA hiso t
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_weil_representation_continuous : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W), IsCMExt F E σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W,
    ∀ T : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
    (∀ t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(T t f)) →
    (∀ s t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), T (s + t) f = T s (T t f)) →
    (∀ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), T 0 f = f) → ∀ t, Continuous (T t) := by
  first | exact @_root_.GlobalTheory.ArchCont.continuous_weil_action_on_line | exact _root_.GlobalTheory.ArchCont.continuous_weil_action_on_line | (intros; apply _root_.GlobalTheory.ArchCont.continuous_weil_action_on_line <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.ArchProdRule
open Filter Topology
open scoped Classical in
theorem archimedean_hasDerivAt_prod : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W), IsCMExt F E σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ (k : ℕ) (γ : Fin k → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)),
    (∀ i, γ i ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W) →
    ∀ T : Fin k → ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
    (∀ i t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (1, γ i (Multiplicative.ofAdd t))) ⇑f ⇑(T i t f)) →
    (∀ i s t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), T i (s + t) f = T i s (T i t f)) →
    (∀ i (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), T i 0 f = f) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (y : Fin n × Fin d → mixedEmbedding.mixedSpace F) (c : Fin k → ℂ),
    (∀ i, HasDerivAt (fun t : ℝ => T i t f y) (c i) 0) →
    HasDerivAt (fun t : ℝ => (List.ofFn fun i => T i t).prod f y) (∑ i, c i) 0 := by
  intro hP F E _ _ _ _ _ σ n d X W M ψ χX χW om hCM hψ hW k γ hγ T hT hadd h0 f y c hc
  have hQ : ∀ i g, ∃ q, Tendsto (fun t : ℝ => t⁻¹ • (T i t g - g)) (𝓝[≠] 0) (𝓝 q) := fun i g =>
    _root_.GlobalTheory.T.schwartz_function_slope_estimate hP M ψ χX χW om hCM hψ hW (γ i) (hγ i) (T i) (hT i) (hadd i) (h0 i) g
  choose Q hQ using hQ
  have hcont : ∀ i t, Continuous (T i t) := fun i =>
    _root_.GlobalTheory.T.archimedean_weil_representation_continuous hP M ψ χX χW om hCM hψ hW (γ i) (hγ i) (T i) (hT i) (hadd i) (h0 i)
  have hprod := slope_prod k T Q hcont h0 hQ f
  let ev : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →L[ℂ] ℂ :=
    (BoundedContinuousFunction.evalCLM ℂ y).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)
  have hev : ∀ (s : ℝ) (g h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), ev (s • (g - h)) = s • (g y - h y) := by
    intro s g h
    rw [ContinuousLinearMap.map_smul_of_tower, map_sub]
    rfl
  have hevq : ∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), ev g = g y := fun g => rfl
  have hci : ∀ i, c i = Q i f y := by
    intro i
    have h1 := hasDerivAt_iff_tendsto_slope_zero.1 (hc i)
    have h2 := (ev.continuous.tendsto _).comp (hQ i f)
    rw [hevq] at h2
    simp only [zero_add, h0] at h1
    refine tendsto_nhds_unique h1 (h2.congr fun t => ?_)
    exact hev _ _ _
  have hsum : (∑ i, c i) = ev (∑ i, Q i f) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => (hci i).trans (hevq _).symm
  rw [hasDerivAt_iff_tendsto_slope_zero, hsum]
  have hp0 : (List.ofFn fun i => T i 0).prod = 1 := by
    have e : (fun i => T i 0) = fun _ => (1 : Module.End ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))) :=
      funext fun i => LinearMap.ext (h0 i)
    rw [e, List.ofFn_const, List.prod_replicate, one_pow]
  have h1 := (ev.continuous.tendsto _).comp hprod
  refine h1.congr fun t => ?_
  simp only [Function.comp_apply, zero_add, hp0]
  exact hev _ _ _
end GlobalTheory.ArchProdRule
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_product_rule_derivative : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W), IsCMExt F E σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ (k : ℕ) (γ : Fin k → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)),
    (∀ i, γ i ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W) →
    ∀ T : Fin k → ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
    (∀ i t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (1, γ i (Multiplicative.ofAdd t))) ⇑f ⇑(T i t f)) →
    (∀ i s t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), T i (s + t) f = T i s (T i t f)) →
    (∀ i (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), T i 0 f = f) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (y : Fin n × Fin d → mixedEmbedding.mixedSpace F) (c : Fin k → ℂ),
    (∀ i, HasDerivAt (fun t : ℝ => T i t f y) (c i) 0) →
    HasDerivAt (fun t : ℝ => (List.ofFn fun i => T i t).prod f y) (∑ i, c i) 0 := by
  first | exact @_root_.GlobalTheory.ArchProdRule.archimedean_hasDerivAt_prod | exact _root_.GlobalTheory.ArchProdRule.archimedean_hasDerivAt_prod | (intros; apply _root_.GlobalTheory.ArchProdRule.archimedean_hasDerivAt_prod <;> assumption)
end
