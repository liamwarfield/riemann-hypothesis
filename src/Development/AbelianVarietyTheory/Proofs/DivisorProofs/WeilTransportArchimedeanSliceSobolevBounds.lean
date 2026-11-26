module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFiniteDimFinitePartsWeilOperators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepDerivativeLawOfL2Isometric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerDerivativeSliceDirectionalAddPhase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeUNuInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationDarbouxCoordinates

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedArchHeisenbergDirectionsContinuous
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedArchHeisenbergDirectionsContinuous
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchTransportHost

theorem archDir_transport_host : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (m n : ℕ) (JA : Matrix (Fin m) (Fin m) D.host.E)
    (JB : Matrix (Fin n) (Fin n) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ)
    (om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ)),
    (∀ p w, ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
      om p (co.rho ψ w φ) = co.rho ψ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) p w) (om p φ)) →
    ∃ M : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
        GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) → ((κ → mixedEmbedding.mixedSpace D.host.F) × (κ → mixedEmbedding.mixedSpace D.host.F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace D.host.F) × (κ → mixedEmbedding.mixedSpace D.host.F)),
      (∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        om p (GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair D.host.F (M p h)) φ) =
          GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair D.host.F h) (om p φ)) ∧
      ∀ h, Continuous fun p => M p h := by
  intro D ψ m n JA JB ξ κ _ co om hom
  exact GlobalTheory.ArchTransportDir.archDir_transport D.host.F D.host.E D.sp.cm.sig ψ m n JA JB ξ κ co om hom

end GlobalTheory.ArchTransportHost

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedArchHeisenbergDirectionsContinuousStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transported_archHeisenbergDirections_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (m n : ℕ) (JA : Matrix (Fin m) (Fin m) D.host.E)
    (JB : Matrix (Fin n) (Fin n) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ)
    (om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ)),
    (∀ p w, ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
      om p (co.rho ψ w φ) = co.rho ψ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) p w) (om p φ)) →
    ∃ M : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
        GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) → ((κ → mixedEmbedding.mixedSpace D.host.F) × (κ → mixedEmbedding.mixedSpace D.host.F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace D.host.F) × (κ → mixedEmbedding.mixedSpace D.host.F)),
      (∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        om p (GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair D.host.F (M p h)) φ) =
          GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair D.host.F h) (om p φ)) ∧
      ∀ h, Continuous fun p => M p h := by
  first | exact @GlobalTheory.ArchTransportHost.archDir_transport_host | exact GlobalTheory.ArchTransportHost.archDir_transport_host | (intros; apply GlobalTheory.ArchTransportHost.archDir_transport_host <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicDualBasisIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicDualBasisIntegral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.WeilL2Words

open MeasureTheory

theorem enorm_sum_mul_sq_le {m : ℕ} (a b : Fin m → ℂ) :
    ‖∑ i, a i * b i‖ₑ ^ 2 ≤ (∑ i, ‖b i‖ₑ ^ 2) * ∑ i, ‖a i‖ₑ ^ 2 := by
  have h1 : ‖∑ i, a i * b i‖₊ ≤ ∑ i, ‖b i‖₊ * ‖a i‖₊ := by
    refine (nnnorm_sum_le _ _).trans (le_of_eq ?_)
    simp [nnnorm_mul, mul_comm]
  have h2 : ‖∑ i, a i * b i‖₊ ^ 2 ≤ (∑ i, ‖b i‖₊ ^ 2) * ∑ i, ‖a i‖₊ ^ 2 :=
    (pow_le_pow_left₀ (by positivity) h1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  simp only [enorm_eq_nnnorm]
  exact_mod_cast h2

theorem slice_le_l2A (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (m : ℕ)
    (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (yy : Fin m → (κ → FiniteAdeleRing (𝓞 F) F))
    (hg : ∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) (hyy : ∀ i j, g i (yy j) = if i = j then 1 else 0)
    (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _))
    (hμ : @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (y : κ → FiniteAdeleRing (𝓞 F) F) : ∃ C : ENNReal, C ≠ ⊤ ∧
      ∀ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      ∫⁻ x, ‖(∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2 ≤
        C * GlobalTheory.WeilL2Words.l2A F μ (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) := by
  have hmeas : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, Measurable fun x => ‖f x‖ₑ ^ 2 :=
    fun f => by
      haveI : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
      exact (f.continuous.measurable.enorm).pow_const 2
  letI : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI := hμ
  have hev : ∀ (f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) x y',
      (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y') = ∑ i, f i x * g i y' := by
    intro f x y'
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => GlobalTheory.WeilCont.pureA_adeleJoin F _ _ x y'

  let U : Fin m → Set (κ → FiniteAdeleRing (𝓞 F) F) := fun j => ⋂ i, {y' | g i y' = g i (yy j)}
  have hUo : ∀ j, IsOpen (U j) := fun j => isOpen_iInter_of_finite fun i => (hg i).1.isOpen_fiber _
  have hUm : ∀ j, yy j ∈ U j := fun j => Set.mem_iInter.2 fun i => rfl
  have hUv : ∀ j, ∀ y' ∈ U j, ∀ i, g i y' = if i = j then 1 else 0 := fun j y' hy' i => by
    rw [← hyy]; exact Set.mem_iInter.1 hy' i
  have hU0 : ∀ j, μ (U j) ≠ 0 := fun j => (hUo j).measure_ne_zero μ ⟨_, hUm j⟩
  have hUt : ∀ j, μ (U j) ≠ ⊤ := by
    intro j
    refine ne_top_of_le_ne_top ((hg j).2.isCompact.measure_lt_top).ne (measure_mono ?_)
    intro y' hy'
    apply subset_tsupport
    rw [Function.mem_support, hUv j y' hy' j, if_pos rfl]
    exact one_ne_zero
  have hB : (∑ i, ‖g i y‖ₑ ^ 2) ≠ ⊤ := ENNReal.sum_ne_top.2 fun i _ => ENNReal.pow_ne_top enorm_ne_top
  refine ⟨(∑ i, ‖g i y‖ₑ ^ 2) * ∑ j, (μ (U j))⁻¹, ENNReal.mul_ne_top hB
    (ENNReal.sum_ne_top.2 fun j _ => ENNReal.inv_ne_top.2 (hU0 j)), ?_⟩
  intro f
  have hA : ∀ j, ∫⁻ x, ‖f j x‖ₑ ^ 2 ≤ (μ (U j))⁻¹ * GlobalTheory.WeilL2Words.l2A F μ (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) := by
    intro j
    rw [← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl (hU0 j)) (Or.inl (hUt j))]
    have e : ∫⁻ y' in U j, (∫⁻ x, ‖(∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y')‖ₑ ^ 2) ∂μ
        = ∫⁻ y' in U j, (∫⁻ x, ‖f j x‖ₑ ^ 2) ∂μ := by
      refine setLIntegral_congr_fun (hUo j).measurableSet (fun y' hy' => ?_)
      refine lintegral_congr fun x => ?_
      rw [hev, Finset.sum_eq_single j]
      · rw [hUv j y' hy' j, if_pos rfl, mul_one]
      · intro i _ hij
        rw [hUv j y' hy' i, if_neg hij, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    rw [setLIntegral_const] at e
    rw [← e]
    exact setLIntegral_le_lintegral _ _
  calc ∫⁻ x, ‖(∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2
      ≤ ∫⁻ x, (∑ i, ‖g i y‖ₑ ^ 2) * ∑ i, ‖f i x‖ₑ ^ 2 := by
        refine lintegral_mono fun x => ?_
        rw [hev]
        exact enorm_sum_mul_sq_le _ _
    _ = (∑ i, ‖g i y‖ₑ ^ 2) * ∑ i, ∫⁻ x, ‖f i x‖ₑ ^ 2 := by
        rw [lintegral_const_mul' _ _ hB, lintegral_finsetSum]
        intro i _
        exact hmeas (f i)
    _ ≤ (∑ i, ‖g i y‖ₑ ^ 2) * ∑ j, (μ (U j))⁻¹ * GlobalTheory.WeilL2Words.l2A F μ (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) := by
        gcongr with j
        exact hA j
    _ = _ := by rw [← Finset.sum_mul, mul_assoc]

end GlobalTheory.WeilL2Words

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicDualBasisIntegralStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adelic_dual_basis_integral : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (yy : Fin m → (κ → FiniteAdeleRing (𝓞 F) F)), (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) → (∀ i j, g i (yy j) = if i = j then 1 else 0) →
    ∀ (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ y : (κ → FiniteAdeleRing (𝓞 F) F), ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      ∫⁻ x, ‖(∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2 ≤
        C * GlobalTheory.WeilL2Words.l2A F μ (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) := by
  first | exact @GlobalTheory.WeilL2Words.slice_le_l2A | exact GlobalTheory.WeilL2Words.slice_le_l2A | (intros; apply GlobalTheory.WeilL2Words.slice_le_l2A <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzL2WordBoundExists
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceMultiplicationDerivativeWordIteratedFDeriv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceMultiplicationDerivativeWordIteratedFDeriv
open IsDedekindDomain NumberField
open scoped Classical

namespace GlobalTheory.WeilL2Words

theorem slice_word_fderivs (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type)
    [Fintype κ] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hψ : ∀ z, ψ (GlobalTheory.WeilL2Words.arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z))
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)))
    (vs : List (κ → mixedEmbedding.mixedSpace F)) :
    (fun x => word F ψ (vs.map fun v => (v, 0)) Φ (GlobalTheory.WeilCont.adeleJoin F x y)) =
        vs.foldr (fun v g' => fun z => fderiv ℝ g' z v) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (vs.foldr (fun v g' => fun z => fderiv ℝ g' z v) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y))) := by
  induction vs with
  | nil => exact ⟨rfl, hΦ⟩
  | cons v vs ih =>
    obtain ⟨h1, h2⟩ := ih
    have hd : Differentiable ℝ (fun x => word F ψ (vs.map fun v => (v, 0)) Φ (GlobalTheory.WeilCont.adeleJoin F x y)) := by
      rw [h1]; exact h2.differentiable (by simp)
    refine ⟨?_, ?_⟩
    · funext x
      simp only [List.map_cons, List.foldr_cons]
      rw [word_cons, GlobalTheory.T.schroedingerDerivative_slice_directional_add_phase F κ ψ ℓ hψ _ y hd (v, 0) x, h1]
      simp
    · simp only [List.foldr_cons]
      exact (h2.fderiv_right (by simp)).clm_apply contDiff_const

theorem slice_word_mul_fderivs : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ z, ψ (GlobalTheory.WeilL2Words.arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z)) →
    ∀ (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) →
      ∀ (u : κ → mixedEmbedding.mixedSpace F) (i : ℕ) (vs : List (κ → mixedEmbedding.mixedSpace F))
        (x : κ → mixedEmbedding.mixedSpace F),
        GlobalTheory.WeilL2Words.word F ψ (List.replicate i (0, u) ++ vs.map fun v => (v, 0)) Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
          (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * u k) : ℂ)) ^ i *
            vs.foldr (fun v g' => fun z => fderiv ℝ g' z v) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x := by
  intro F _ _ _ κ _ ψ ℓ hψ Φ y hΦ u i vs x
  obtain ⟨h1, h2⟩ := slice_word_fderivs F κ ψ ℓ hψ Φ y hΦ vs
  have hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : κ → mixedEmbedding.mixedSpace F => ℓ (∑ k, x k * u k)) := by
    let L : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
      ℓ ∘ₗ ∑ k, (LinearMap.mulRight ℝ (u k)) ∘ₗ LinearMap.proj k
    have hLe : (fun x : κ → mixedEmbedding.mixedSpace F => ℓ (∑ k, x k * u k)) = L := by
      funext x; simp [L, LinearMap.sum_apply]
    rw [hLe]
    exact (LinearMap.toContinuousLinearMap L).contDiff
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : κ → mixedEmbedding.mixedSpace F => 2 * Real.pi * Complex.I * (ℓ (∑ k, x k * u k) : ℂ)) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hL)
  suffices H : ∀ i : ℕ,
      (fun x => word F ψ (List.replicate i (0, u) ++ vs.map fun v => (v, 0)) Φ (GlobalTheory.WeilCont.adeleJoin F x y)) =
        (fun x => (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * u k) : ℂ)) ^ i *
          vs.foldr (fun v g' => fun z => fderiv ℝ g' z v) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * u k) : ℂ)) ^ i *
          vs.foldr (fun v g' => fun z => fderiv ℝ g' z v) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x) by
    exact congrFun (H i).1 x
  intro i
  induction i with
  | zero =>
    refine ⟨?_, ?_⟩
    · funext x; simp only [List.replicate_zero, List.nil_append, pow_zero, one_mul]; exact congrFun h1 x
    · simpa using h2
  | succ i ih =>
    obtain ⟨e1, e2⟩ := ih
    have hd : Differentiable ℝ (fun x =>
        word F ψ (List.replicate i (0, u) ++ vs.map fun v => (v, 0)) Φ (GlobalTheory.WeilCont.adeleJoin F x y)) := by
      rw [e1]; exact e2.differentiable (by simp)
    refine ⟨?_, (hc.pow (i + 1)).mul h2⟩
    funext x
    rw [List.replicate_succ, List.cons_append, word_cons, GlobalTheory.T.schroedingerDerivative_slice_directional_add_phase F κ ψ ℓ hψ _ y hd (0, u) x]
    have e1x := congrFun e1 x
    simp only [ContinuousLinearMap.map_zero, zero_add, e1x]
    ring

end GlobalTheory.WeilL2Words
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceMultiplicationDerivativeWordIteratedFDerivStatement
open IsDedekindDomain NumberField
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slice_multiplicationDerivativeWord_iteratedFDeriv : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ z, ψ (GlobalTheory.WeilL2Words.arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z)) →
    ∀ (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) →
      ∀ (u : κ → mixedEmbedding.mixedSpace F) (i : ℕ) (vs : List (κ → mixedEmbedding.mixedSpace F))
        (x : κ → mixedEmbedding.mixedSpace F),
        GlobalTheory.WeilL2Words.word F ψ (List.replicate i (0, u) ++ vs.map fun v => (v, 0)) Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
          (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * u k) : ℂ)) ^ i *
            vs.foldr (fun v g' => fun z => fderiv ℝ g' z v) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x := by
  first | exact @GlobalTheory.WeilL2Words.slice_word_mul_fderivs | exact GlobalTheory.WeilL2Words.slice_word_mul_fderivs | (intros; apply GlobalTheory.WeilL2Words.slice_word_mul_fderivs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedFDerivApplyEqFoldrDirectionalFderiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedFDerivApplyEqFoldrDirectionalFderiv
open IsDedekindDomain NumberField
open scoped Classical

namespace GlobalTheory

theorem iteratedFDeriv_apply_eq_foldr_fderiv :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (g : E → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g →
    ∀ (j : ℕ) (m : Fin j → E) (x : E),
      iteratedFDeriv ℝ j g x m = (List.ofFn m).foldr (fun v g' => fun z => fderiv ℝ g' z v) g x := by
  intro E _ _ g hg j
  induction j with
  | zero =>
    intro m x
    simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    intro m x
    rw [iteratedFDeriv_succ_apply_left, List.ofFn_succ, List.foldr_cons]
    have hfun : (List.ofFn (fun i : Fin n => m i.succ)).foldr (fun v g' => fun z => fderiv ℝ g' z v) g
        = fun z => iteratedFDeriv ℝ n g z (Fin.tail m) := by
      funext z
      exact (ih (Fin.tail m) z).symm
    simp only [hfun]
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n g) x :=
      (hg.differentiable_iteratedFDeriv (by first | exact_mod_cast ENat.coe_lt_top n | simp | exact WithTop.coe_lt_coe.2 (ENat.coe_lt_top n))) x
    rw [fderiv_continuousMultilinear_apply_const_apply hd]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedFDerivApplyEqFoldrDirectionalFderivStatement
open IsDedekindDomain NumberField
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedFDeriv_apply_eq_foldr_directional_fderiv : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (g : E → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g →
    ∀ (j : ℕ) (m : Fin j → E) (x : E),
      iteratedFDeriv ℝ j g x m = (List.ofFn m).foldr (fun v g' => fun z => fderiv ℝ g' z v) g x := by
  first | exact @GlobalTheory.iteratedFDeriv_apply_eq_foldr_fderiv | exact GlobalTheory.iteratedFDeriv_apply_eq_foldr_fderiv | (intros; apply GlobalTheory.iteratedFDeriv_apply_eq_foldr_fderiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSqLeSumLintegralEnormSqOfPointwise
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSqLeSumLintegralEnormSqOfPointwise
open IsDedekindDomain NumberField
open scoped Classical

namespace GlobalTheory

theorem sq_le_sum_enorm_sq_lintegral_bound
    (E : Type) [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E] (μ : MeasureTheory.Measure E)
    (ι : Type) [Fintype ι] (f : E → ℝ) (g : ι → E → ℂ) (C : ℝ) (hg : ∀ a, Continuous (g a))
    (hfg : ∀ x, f x ^ 2 ≤ C * ∑ a, ‖g a x‖ ^ 2) :
    ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) ≤ ENNReal.ofReal C * ∑ a, ∫⁻ x, ‖g a x‖ₑ ^ 2 ∂μ := by
  by_cases hi : MeasureTheory.Integrable (fun x => f x ^ 2) μ
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hi
      (MeasureTheory.ae_of_all _ (fun x => sq_nonneg (f x)))]
    have hm : ∀ a, Measurable (fun x => ‖g a x‖ₑ ^ 2) := fun a =>
      ((hg a).measurable.enorm).pow_const 2
    calc ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ
        ≤ ∫⁻ x, ENNReal.ofReal C * ∑ a, ‖g a x‖ₑ ^ 2 ∂μ := by
          refine MeasureTheory.lintegral_mono (fun x => ?_)
          calc ENNReal.ofReal (f x ^ 2) ≤ ENNReal.ofReal (C * ∑ a, ‖g a x‖ ^ 2) :=
                ENNReal.ofReal_le_ofReal (hfg x)
            _ = ENNReal.ofReal C * ENNReal.ofReal (∑ a, ‖g a x‖ ^ 2) :=
                ENNReal.ofReal_mul' (Finset.sum_nonneg (fun a _ => sq_nonneg _))
            _ = ENNReal.ofReal C * ∑ a, ‖g a x‖ₑ ^ 2 := by
                rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => sq_nonneg _)]
                congr 1
                refine Finset.sum_congr rfl (fun a _ => ?_)
                rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
      _ = ENNReal.ofReal C * ∑ a, ∫⁻ x, ‖g a x‖ₑ ^ 2 ∂μ := by
          rw [MeasureTheory.lintegral_const_mul _ (Finset.measurable_sum _ (fun a _ => hm a))]
          congr 1
          exact MeasureTheory.lintegral_finsetSum Finset.univ (fun a _ => hm a)
  · rw [MeasureTheory.integral_undef hi, ENNReal.ofReal_zero]
    exact zero_le

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSqLeSumLintegralEnormSqOfPointwiseStatement
open IsDedekindDomain NumberField
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_sq_le_sum_lintegral_enorm_sq_of_pointwise : ∀ (E : Type) [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E] (μ : MeasureTheory.Measure E)
    (ι : Type) [Fintype ι] (f : E → ℝ) (g : ι → E → ℂ) (C : ℝ), (∀ a, Continuous (g a)) →
    (∀ x, f x ^ 2 ≤ C * ∑ a, ‖g a x‖ ^ 2) →
    ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) ≤ ENNReal.ofReal C * ∑ a, ∫⁻ x, ‖g a x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.sq_le_sum_enorm_sq_lintegral_bound | exact GlobalTheory.sq_le_sum_enorm_sq_lintegral_bound | (intros; apply GlobalTheory.sq_le_sum_enorm_sq_lintegral_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedSpaceDualVectorTraceForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedSpaceDualVectorTraceForm
open IsDedekindDomain NumberField
open scoped Classical

namespace GlobalTheory

theorem dualform : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ z : mixedEmbedding.mixedSpace F, z ≠ 0 → ∃ u, ℓ (z * u) ≠ 0) →
    ∀ lam : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ, ∃ u : κ → mixedEmbedding.mixedSpace F,
      ∀ x, ℓ (∑ k, x k * u k) = lam x := by
  intro F _ _ κ _ ℓ hℓ lam
  set M := mixedEmbedding.mixedSpace F
  let Φ : (κ → M) →ₗ[ℝ] Module.Dual ℝ (κ → M) :=
    { toFun := fun u =>
        { toFun := fun x => ℓ (∑ k, x k * u k)
          map_add' := by intro x y; simp [add_mul, Finset.sum_add_distrib]
          map_smul' := by intro c x; simp [smul_mul_assoc, ← Finset.smul_sum] }
      map_add' := by
        intro u v; refine LinearMap.ext fun x => ?_
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c u; refine LinearMap.ext fun x => ?_
        simp [mul_smul_comm, ← Finset.smul_sum] }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    funext k
    by_contra hne
    obtain ⟨w, hw⟩ := hℓ (u k) hne
    apply hw
    have := LinearMap.congr_fun hu (Pi.single k w)
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply] at this
    rw [Finset.sum_eq_single k] at this
    · simpa [mul_comm] using this
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  have hsurj : Function.Surjective Φ := by
    have : Module.finrank ℝ (κ → M) = Module.finrank ℝ (Module.Dual ℝ (κ → M)) :=
      (Subspace.dual_finrank_eq).symm
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank this).mp hinj
  obtain ⟨u, hu⟩ := hsurj lam
  exact ⟨u, fun x => by rw [← hu]; rfl⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedSpaceDualVectorTraceFormStatement
open IsDedekindDomain NumberField
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mixedSpace_dual_vector_traceForm : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ z : mixedEmbedding.mixedSpace F, z ≠ 0 → ∃ u, ℓ (z * u) ≠ 0) →
    ∀ lam : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ, ∃ u : κ → mixedEmbedding.mixedSpace F,
      ∀ x, ℓ (∑ k, x k * u k) = lam x := by
  first | exact @GlobalTheory.dualform | exact GlobalTheory.dualform | (intros; apply GlobalTheory.dualform <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMultilinearMapNormLeSumBasisValues
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMultilinearMapNormLeSumBasisValues
open IsDedekindDomain NumberField
open scoped Classical

theorem GlobalTheory.continuousMultilinear_norm_le_basis_sum : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : Type) [Fintype ι] (b : Module.Basis ι ℝ E) (j : ℕ),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℂ,
      ‖M‖ ≤ K * ∑ cs : Fin j → ι, ‖M (fun r => b (cs r))‖ := by
  intro E _ _ ι _ b j
  haveI : FiniteDimensional ℝ E := Module.Finite.of_basis b
  set C := ‖(b.equivFunL : E →L[ℝ] (ι → ℝ))‖ with hC
  have hC0 : 0 ≤ C := norm_nonneg _
  have hcoord : ∀ (x : E) (c : ι), ‖b.repr x c‖ ≤ C * ‖x‖ := by
    intro x c
    have h1 : b.repr x c = (b.equivFunL : E →L[ℝ] (ι → ℝ)) x c := rfl
    rw [h1]
    exact (norm_le_pi_norm _ c).trans ((b.equivFunL : E →L[ℝ] (ι → ℝ)).le_opNorm x)
  refine ⟨C ^ j, pow_nonneg hC0 _, fun M => ?_⟩
  apply ContinuousMultilinearMap.opNorm_le_bound
  · exact mul_nonneg (pow_nonneg hC0 _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro v
  have hv : v = fun r => ∑ c, b.repr (v r) c • b c := funext fun r => (b.sum_repr (v r)).symm
  have key : M v = ∑ cs : Fin j → ι, (∏ r, b.repr (v r) (cs r)) • M (fun r => b (cs r)) := by
    conv_lhs => rw [hv]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [M.map_sum]
    refine Finset.sum_congr rfl fun cs _ => ?_
    exact M.map_smul_univ (fun r => b.repr (v r) (cs r)) (fun r => b (cs r))
  rw [key]
  calc ‖∑ cs : Fin j → ι, (∏ r, b.repr (v r) (cs r)) • M (fun r => b (cs r))‖
      ≤ ∑ cs : Fin j → ι, ‖(∏ r, b.repr (v r) (cs r)) • M (fun r => b (cs r))‖ := norm_sum_le _ _
    _ ≤ ∑ cs : Fin j → ι, (C ^ j * ∏ r, ‖v r‖) * ‖M (fun r => b (cs r))‖ := by
      refine Finset.sum_le_sum fun cs _ => ?_
      rw [norm_smul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [norm_prod, ← Fin.prod_const, ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun r _ => hcoord (v r) (cs r)
    _ = C ^ j * (∑ cs : Fin j → ι, ‖M (fun r => b (cs r))‖) * ∏ r, ‖v r‖ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun cs _ => ?_
      ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMultilinearMapNormLeSumBasisValuesStatement
open IsDedekindDomain NumberField
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousMultilinearMap_norm_le_sum_basis_values : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : Type) [Fintype ι] (b : Module.Basis ι ℝ E) (j : ℕ),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℂ,
      ‖M‖ ≤ K * ∑ cs : Fin j → ι, ‖M (fun r => b (cs r))‖ := by
  first | exact @GlobalTheory.continuousMultilinear_norm_le_basis_sum | exact GlobalTheory.continuousMultilinear_norm_le_basis_sum | (intros; apply GlobalTheory.continuousMultilinear_norm_le_basis_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPowLeConstMulOneAddSumAbsBasisCoordPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPowLeConstMulOneAddSumAbsBasisCoordPow
open IsDedekindDomain NumberField
open scoped Classical

namespace GlobalTheory

theorem norm_pow_le_const_mul_one_add_sum_abs_coord_pow :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : Type) [Fintype ι] (b : Module.Basis ι ℝ E) (i : ℕ),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : E, ‖x‖ ^ i ≤ K * (1 + ∑ c, |b.coord c x| ^ i) := by
  intro E _ _ ι _ b i
  have hB1 : 1 ≤ 1 + ∑ c, ‖b c‖ := by
    have : 0 ≤ ∑ c, ‖b c‖ := Finset.sum_nonneg (fun c _ => norm_nonneg _)
    linarith
  refine ⟨(1 + ∑ c, ‖b c‖) ^ i, by positivity, fun x => ?_⟩
  have hS : 0 ≤ ∑ c, |b.coord c x| ^ i := Finset.sum_nonneg (fun c _ => by positivity)
  have hx : ‖x‖ ≤ ∑ c, |b.coord c x| * ‖b c‖ := by
    conv_lhs => rw [← b.sum_repr x]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, Module.Basis.coord_apply]
  rcases isEmpty_or_nonempty ι with hι | hι
  · have h0 : ‖x‖ = 0 := by
      have : ∑ c, |b.coord c x| * ‖b c‖ = 0 := by simp
      linarith [norm_nonneg x]
    rw [h0]
    have hp : 1 ≤ (1 + ∑ c, ‖b c‖) ^ i := one_le_pow₀ hB1
    calc (0:ℝ) ^ i ≤ 1 := pow_le_one₀ le_rfl zero_le_one
      _ ≤ (1 + ∑ c, ‖b c‖) ^ i * (1 + ∑ c, |b.coord c x| ^ i) := by nlinarith
  · obtain ⟨c0, -, hc0⟩ := Finset.exists_max_image Finset.univ (fun c => |b.coord c x|)
      Finset.univ_nonempty
    have h1 : ‖x‖ ≤ |b.coord c0 x| * (1 + ∑ c, ‖b c‖) := by
      calc ‖x‖ ≤ ∑ c, |b.coord c x| * ‖b c‖ := hx
        _ ≤ ∑ c, |b.coord c0 x| * ‖b c‖ := Finset.sum_le_sum (fun c _ =>
            mul_le_mul_of_nonneg_right (hc0 c (Finset.mem_univ _)) (norm_nonneg _))
        _ = |b.coord c0 x| * ∑ c, ‖b c‖ := by rw [Finset.mul_sum]
        _ ≤ |b.coord c0 x| * (1 + ∑ c, ‖b c‖) :=
            mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    have h2 : |b.coord c0 x| ^ i ≤ ∑ c, |b.coord c x| ^ i :=
      Finset.single_le_sum (f := fun c => |b.coord c x| ^ i) (fun c _ => by positivity)
        (Finset.mem_univ c0)
    calc ‖x‖ ^ i ≤ (|b.coord c0 x| * (1 + ∑ c, ‖b c‖)) ^ i :=
          pow_le_pow_left₀ (norm_nonneg _) h1 i
      _ = (1 + ∑ c, ‖b c‖) ^ i * |b.coord c0 x| ^ i := by rw [mul_pow, mul_comm]
      _ ≤ (1 + ∑ c, ‖b c‖) ^ i * (1 + ∑ c, |b.coord c x| ^ i) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPowLeConstMulOneAddSumAbsBasisCoordPowStatement
open IsDedekindDomain NumberField
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_pow_le_const_mul_one_add_sum_abs_basisCoord_pow : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : Type) [Fintype ι] (b : Module.Basis ι ℝ E) (i : ℕ),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : E, ‖x‖ ^ i ≤ K * (1 + ∑ c, |b.coord c x| ^ i) := by
  first | exact @GlobalTheory.norm_pow_le_const_mul_one_add_sum_abs_coord_pow | exact GlobalTheory.norm_pow_le_const_mul_one_add_sum_abs_coord_pow | (intros; apply GlobalTheory.norm_pow_le_const_mul_one_add_sum_abs_coord_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzL2WordBoundExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.WeilL2Words

theorem adelic_schwartz_slice_l2_word_bound : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ → ∀ i j : ℕ,
    ∃ (L : List (List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))) (C : ℝ), ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ y : (κ → FiniteAdeleRing (𝓞 F) F),
      ENNReal.ofReal (∫ x, (‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖) ^ 2) ≤
        ENNReal.ofReal C * (L.map fun w => ∫⁻ x, ‖GlobalTheory.WeilL2Words.word F ψ w Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2).sum := by
  intro F _ _ _ κ _ ψ hψ i j
  obtain ⟨ℓ, hnd, hℓ⟩ := hψ
  obtain ⟨n, ⟨b⟩⟩ : ∃ n, Nonempty (Module.Basis (Fin n) ℝ (κ → mixedEmbedding.mixedSpace F)) :=
    ⟨_, ⟨Module.finBasis ℝ _⟩⟩
  obtain ⟨K4, hK4, hb4⟩ := GlobalTheory.T.continuousMultilinearMap_norm_le_sum_basis_values (κ → mixedEmbedding.mixedSpace F) _ b j
  obtain ⟨K5, hK5, hb5⟩ := GlobalTheory.T.norm_pow_le_const_mul_one_add_sum_abs_basisCoord_pow (κ → mixedEmbedding.mixedSpace F) _ b i
  choose u hu using fun c => GlobalTheory.T.exists_mixedSpace_dual_vector_traceForm F κ ℓ hnd (b.coord c)
  let ia : Option (Fin n) → ℕ := fun a => a.elim 0 (fun _ => i)
  let ua : Option (Fin n) → (κ → mixedEmbedding.mixedSpace F) := fun a => a.elim 0 u
  let wd : Option (Fin n) × (Fin j → Fin n) →
      List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :=
    fun p => List.replicate (ia p.1) (0, ua p.1) ++ (List.ofFn fun r => b (p.2 r)).map fun v => (v, 0)
  refine ⟨Finset.univ.toList.map wd, (K5 * K4) ^ 2 * (Fintype.card (Option (Fin n) × (Fin j → Fin n)) : ℝ),
    fun Φ hΦ y => ?_⟩
  obtain ⟨s, hs⟩ := GlobalTheory.WeilCont.exists_slice F hΦ y
  have hsf : (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) = s := funext fun x => (hs x).symm
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) := hsf ▸ s.smooth ⊤
  have hℓc : Continuous ℓ := LinearMap.continuous_of_finiteDimensional ℓ
  have key : ∀ p x, GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
      (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * ua p.1 k) : ℂ)) ^ (ia p.1) *
        iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x (fun r => b (p.2 r)) := by
    intro p x
    rw [GlobalTheory.T.slice_multiplicationDerivativeWord_iteratedFDeriv F κ ψ ℓ hℓ Φ y hsm, GlobalTheory.T.iteratedFDeriv_apply_eq_foldr_directional_fderiv _ _ hsm]
  have hcont : ∀ p, Continuous fun x => GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y) := by
    intro p
    simp_rw [key]
    have h1 : Continuous fun x : κ → mixedEmbedding.mixedSpace F => ∑ k, x k * ua p.1 k := by fun_prop
    have h2 : Continuous fun x => iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x :=
      hsm.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    exact ((continuous_const.mul (Complex.continuous_ofReal.comp (hℓc.comp h1))).pow _).mul
      ((ContinuousMultilinearMap.apply ℝ _ ℂ (fun r => b (p.2 r))).continuous.comp h2)
  rw [List.map_map, Finset.sum_map_toList]
  refine GlobalTheory.T.integral_sq_le_sum_lintegral_enorm_sq_of_pointwise _ MeasureTheory.volume _ _ _ _ hcont fun x => ?_
  have hterm : ∀ p : Option (Fin n) × (Fin j → Fin n),
      p.1.elim 1 (fun c => |b.coord c x| ^ i) *
          ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x (fun r => b (p.2 r))‖ ≤
        ‖GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ := by
    intro p
    rw [key, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rcases p with ⟨_ | c, cs⟩
    · simp [ia]
    · simp only [Option.elim, ia, ua, hu, norm_pow, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Complex.norm_I, Real.norm_eq_abs, mul_one]
      rw [mul_pow]
      refine le_mul_of_one_le_left (by positivity) (one_le_pow₀ ?_)
      rw [abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_gt_three]
  have h1 : ‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖ ≤
      K5 * K4 * ∑ p : Option (Fin n) × (Fin j → Fin n),
        ‖GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ := by
    calc _ ≤ (K5 * (1 + ∑ c, |b.coord c x| ^ i)) *
          (K4 * ∑ cs : Fin j → Fin n, ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x
            (fun r => b (cs r))‖) :=
          mul_le_mul (hb5 x) (hb4 _) (norm_nonneg _) (by positivity)
      _ = K5 * K4 * ∑ p : Option (Fin n) × (Fin j → Fin n), p.1.elim 1 (fun c => |b.coord c x| ^ i) *
          ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x (fun r => b (p.2 r))‖ := by
          rw [Fintype.sum_prod_type, Fintype.sum_option]
          simp only [Option.elim, one_mul, ← Finset.mul_sum, ← Finset.sum_mul]
          ring
      _ ≤ _ := by
          gcongr with p
          exact hterm p
  have h0 : 0 ≤ ‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖ := by positivity
  calc _ ≤ (K5 * K4 * ∑ p : Option (Fin n) × (Fin j → Fin n),
        ‖GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = (K5 * K4) ^ 2 * (∑ p : Option (Fin n) × (Fin j → Fin n),
        ‖GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖) ^ 2 := by ring
    _ ≤ (K5 * K4) ^ 2 * ((Fintype.card (Option (Fin n) × (Fin j → Fin n)) : ℝ) * ∑ p : Option (Fin n) × (Fin j → Fin n),
        ‖GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ ^ 2) := by
          gcongr
          exact sq_sum_le_card_mul_sum_sq
    _ = _ := by ring

end GlobalTheory.WeilL2Words
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzL2WordBoundExistsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_schwartz_l2_word_bound_exists : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ → ∀ i j : ℕ,
    ∃ (L : List (List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))) (C : ℝ), ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ y : (κ → FiniteAdeleRing (𝓞 F) F),
      ENNReal.ofReal (∫ x, (‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖) ^ 2) ≤
        ENNReal.ofReal C * (L.map fun w => ∫⁻ x, ‖GlobalTheory.WeilL2Words.word F ψ w Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2).sum := by
  first | exact @GlobalTheory.WeilL2Words.adelic_schwartz_slice_l2_word_bound | exact GlobalTheory.WeilL2Words.adelic_schwartz_slice_l2_word_bound | (intros; apply GlobalTheory.WeilL2Words.adelic_schwartz_slice_l2_word_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilTransportArchimedeanSliceSobolevBounds
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

open MeasureTheory

namespace GlobalTheory.WeilL2Words

section Core

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem schA_decomp {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) :
    ∃ (n : ℕ) (f : Fin n → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : Fin n → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ Φ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i) := by
  rw [GlobalTheory.WeilM.schA, Submodule.mem_span_set'] at hΦ
  obtain ⟨n, c, s, rfl⟩ := hΦ
  choose f g hg hfg using fun i => (s i).2
  refine ⟨n, fun i => c i • f i, g, hg, Finset.sum_congr rfl fun i _ => ?_⟩
  rw [hfg i]
  ext a
  simp [GlobalTheory.WeilM.pureA, mul_assoc]

theorem list_sum_ne_top {l : List ENNReal} (h : ∀ a ∈ l, a ≠ ⊤) : l.sum ≠ ⊤ := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.sum_cons]
    exact ENNReal.add_ne_top.2 ⟨h a (by simp), ih fun b hb => h b (by simp [hb])⟩

variable [Invertible (2 : AdeleRing (𝓞 F) F)] {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}

theorem dS_mem (hψ : IsStdInf F ψ) (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) : dS F ψ h Φ ∈ GlobalTheory.WeilM.schA F κ := by
  obtain ⟨n, f, g, hg, rfl⟩ := schA_decomp hΦ
  obtain ⟨f', hf'⟩ := GlobalTheory.T.archDerivative_keeps_sums_fixed_finite_parts F κ ψ hψ n g f h
  rw [hf']
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f' i, g i, hg i, rfl⟩

theorem word_mem (hψ : IsStdInf F ψ) : ∀ (w : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))) {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ},
    Φ ∈ GlobalTheory.WeilM.schA F κ → word F ψ w Φ ∈ GlobalTheory.WeilM.schA F κ
  | [], _, hΦ => hΦ
  | h :: w, _, hΦ => by
    rw [word_cons]
    exact dS_mem hψ h (word_mem hψ w hΦ)

theorem word_sum (hψ : IsStdInf F ψ) {m : ℕ} (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    ∀ (w : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))) (f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ), ∃ f' : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      word F ψ w (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) = ∑ i, GlobalTheory.WeilM.pureA F (f' i) (g i) := by
  intro w f
  induction w with
  | nil => exact ⟨f, rfl⟩
  | cons h w ih =>
    obtain ⟨f1, e1⟩ := ih
    obtain ⟨f2, e2⟩ := GlobalTheory.T.archDerivative_keeps_sums_fixed_finite_parts F κ ψ hψ m g f1 h
    exact ⟨f2, by rw [word_cons, e1, e2]⟩

theorem word_law (hψ : IsStdInf F ψ) {G : Type} [Group G] (om : G →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ))
    (pres : ∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, om p φ ∈ GlobalTheory.WeilM.schA F κ)
    (M : G → ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
    (himpl : ∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
      om p (GlobalTheory.WeilM.schr ψ (archPair F (M p h)) φ) = GlobalTheory.WeilM.schr ψ (archPair F h) (om p φ))
    (μ : @Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (hiso : ∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, l2A F μ (om p φ) = l2A F μ φ) (p : G) :
    ∀ (w : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))) {φ : (κ → AdeleRing (𝓞 F) F) → ℂ}, φ ∈ GlobalTheory.WeilM.schA F κ →
      word F ψ w (om p φ) = om p (word F ψ (w.map (M p)) φ)
  | [], _, _ => rfl
  | h :: w, φ, hφ => by
    rw [List.map_cons, word_cons, word_cons, word_law hψ om pres M himpl μ hμ hiso p w hφ]
    exact GlobalTheory.T.weilRep_derivative_law_of_L2Isometric F κ ψ hψ om pres M himpl μ hμ hiso p h _ (word_mem hψ _ hφ)

theorem slice_l2_of (hψ : IsStdInf F ψ) {G : Type} [Group G] [TopologicalSpace G]
    (om : G →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ))
    (pres : ∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, om p φ ∈ GlobalTheory.WeilM.schA F κ)
    (M : G → ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
    (himpl : ∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
      om p (GlobalTheory.WeilM.schr ψ (archPair F (M p h)) φ) = GlobalTheory.WeilM.schr ψ (archPair F h) (om p φ))
    (hM : ∀ h, Continuous fun p => M p h)
    (μ : @Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (hiso : ∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, l2A F μ (om p φ) = l2A F μ φ)
    {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) (p0 : G)
    (hfin : ∃ N ∈ nhds p0, ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (yy : Fin m → (κ → FiniteAdeleRing (𝓞 F) F)),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (∀ i j, g i (yy j) = if i = j then 1 else 0) ∧
      ∀ p ∈ N, ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, om p Φ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i))
    (y : (κ → FiniteAdeleRing (𝓞 F) F)) (i j : ℕ) :
    ∃ B : ℝ, ∀ᶠ p in nhds p0,
      ∫ x, (‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖) ^ 2 ≤ B := by
  obtain ⟨L, C, hL⟩ := GlobalTheory.T.adelic_schwartz_l2_word_bound_exists F κ ψ hψ i j
  obtain ⟨N, hN, m, g, yy, hg, hdual, hf⟩ := hfin
  obtain ⟨CG, hCG, hG⟩ := GlobalTheory.T.finite_adelic_dual_basis_integral F κ m g yy hg hdual μ hμ y
  set R : ℝ := ∑ h ∈ L.flatten.toFinset, (‖M p0 h‖ + 1) with hR
  have hev : ∀ᶠ p in nhds p0, ∀ h ∈ L.flatten.toFinset, ‖M p h‖ ≤ R := by
    refine (Filter.eventually_all_finset _).2 fun h hh => ?_
    have hc : ContinuousAt (fun p => ‖M p h‖) p0 := ((hM h).norm).continuousAt
    filter_upwards [hc.eventually_lt continuousAt_const (lt_add_one ‖M p0 h‖)] with p hp
    exact hp.le.trans (Finset.single_le_sum (f := fun h => ‖M p0 h‖ + 1) (fun _ _ => by positivity) hh)
  have hB : ∀ w ∈ L, ∃ B : ENNReal, B ≠ ⊤ ∧ ∀ ws : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)), ws.length = w.length →
      (∀ h ∈ ws, ‖h‖ ≤ R) → l2A F μ (word F ψ ws Φ) ≤ B :=
    fun w _ => GlobalTheory.T.exists_finite_l2A_bound_words F κ ψ hψ Φ hΦ μ hμ w.length R
  choose! B hBtop hBle using hB
  have htop : ENNReal.ofReal C * (L.map fun w => CG * B w).sum ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (list_sum_ne_top fun a ha => ?_)
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ha
    exact ENNReal.mul_ne_top hCG (hBtop w hw)
  refine ⟨(ENNReal.ofReal C * (L.map fun w => CG * B w).sum).toReal, ?_⟩
  filter_upwards [hev, hN] with p hp hpN
  have key := hL (om p Φ) (pres p Φ hΦ) y
  have hsum : (L.map fun w => ∫⁻ x, ‖word F ψ w (om p Φ) (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2).sum ≤
      (L.map fun w => CG * B w).sum := by
    refine List.sum_le_sum fun w hw => ?_
    obtain ⟨f, hfp⟩ := hf p hpN
    obtain ⟨f', hf'⟩ := word_sum hψ g w f
    have e1 : word F ψ w (om p Φ) = ∑ i, GlobalTheory.WeilM.pureA F (f' i) (g i) := by rw [hfp, hf']
    calc ∫⁻ x, ‖word F ψ w (om p Φ) (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2
        ≤ CG * l2A F μ (word F ψ w (om p Φ)) := by rw [e1]; exact hG f'
      _ = CG * l2A F μ (word F ψ (w.map (M p)) Φ) := by
          rw [word_law hψ om pres M himpl μ hμ hiso p w hΦ, hiso p _ (word_mem hψ _ hΦ)]
      _ ≤ CG * B w := by
          gcongr
          refine hBle w hw _ (List.length_map _) fun h hh => ?_
          obtain ⟨h0, h0m, rfl⟩ := List.mem_map.1 hh
          exact hp h0 (List.mem_toFinset.2 (List.mem_flatten.2 ⟨w, hw, h0m⟩))
  exact (ENNReal.ofReal_le_iff_le_toReal htop).1 (key.trans (by gcongr))

end Core

end GlobalTheory.WeilL2Words

theorem GlobalTheory.WeilL2Words.weilTransport_archimedeanSlice_sobolev_bounds_alt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
  ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ (y : κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) p0 (i j : ℕ), ∃ B : ℝ,
      ∀ᶠ p in nhds p0, ∫ x, (‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin D.host.F x y)) x‖) ^ 2 ≤ B := by
  intro D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hA hJB κ _ co hco ω hω om hom Φ hΦ y p0 i j
  have hI := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hA hJB κ co hco ω hω om hom
  obtain ⟨M, himpl, hM⟩ := GlobalTheory.T.transported_archHeisenbergDirections_continuous D ψ _ _ JA JB ξ κ co om hI.2
  obtain ⟨μ, hμ, hiso⟩ := GlobalTheory.T.l2A_transport_gram_transpose D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hA hJB κ co hco ω hω om hom
  exact GlobalTheory.WeilL2Words.slice_l2_of (GlobalTheory.T.isStandardArchimedeanAddChar_of_standardChar D ψ hψ) om hI.1 M himpl hM μ hμ hiso hΦ p0
    (GlobalTheory.T.exists_local_finiteDim_finiteParts_weilOperators D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hA hJB κ co hco ω hω om hom Φ hΦ p0) y i j
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilTransportArchimedeanSliceSobolevBoundsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilTransport_archimedeanSlice_sobolev_bounds : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
  ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ (y : κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) p0 (i j : ℕ), ∃ B : ℝ,
      ∀ᶠ p in nhds p0, ∫ x, (‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin D.host.F x y)) x‖) ^ 2 ≤ B := by
  first | exact @GlobalTheory.WeilL2Words.weilTransport_archimedeanSlice_sobolev_bounds_alt | exact GlobalTheory.WeilL2Words.weilTransport_archimedeanSlice_sobolev_bounds_alt | (intros; apply GlobalTheory.WeilL2Words.weilTransport_archimedeanSlice_sobolev_bounds_alt <;> assumption)
end
