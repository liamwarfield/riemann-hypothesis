module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsAddBlockArrow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableAdelicMatrixRapidDecayCompactFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableAdelicMatrixRapidDecayCompactFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdelicIntegrable

theorem integrable_of_rapid_decay : ∀ (D : D7) (a b : ℕ) (μ : Measure (Mx D a b)), μ.IsAddHaarMeasure → ∀ θ : InfFam D, IsInfFam θ → ∀ f : Mx D a b → ℂ, Continuous f → ∀ K : Set (Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K → (∀ y : Mx D a b, y.map (finPart D) ∉ K → f y = 0) → (∀ N : ℕ, ∃ C : ℝ, ∀ y : Mx D a b, (1 + ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ^ N * ‖f y‖ ≤ C) → Integrable f μ := by
  intro D a b μ hμ θ hθ f hf K hK hKf hdec
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D a b
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ

  let π : Mx D a b → (Fin a → Fin b → D.what₂.Tau → ℂ) := fun y i j τ => θ τ (infPart D (y i j))
  have hπc : Continuous π := continuous_pi fun i => continuous_pi fun j => continuous_pi fun τ =>
    (GlobalTheory.FockCompare.continuous_comp hθ τ).comp ((continuous_apply j).comp (continuous_apply i))
  have hπm : Measurable π := hπc.measurable

  let s : (Fin a → Fin b → D.what₂.Tau → ℂ) → Mx D a b := fun c => Matrix.of fun i j => σ (c i j)
  have hπs : ∀ c y, π (s c + y) = c + π y := by
    intro c y; funext i j τ
    show θ τ (infPart D (σ (c i j) + y i j)) = c i j τ + θ τ (infPart D (y i j))
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hσ.comp]
  have hfs : ∀ c (y : Mx D a b), (s c + y).map (finPart D) = y.map (finPart D) := by
    intro c y; ext i j
    show finPart D (σ (c i j) + y i j) = finPart D (y i j)
    rw [RingHom.map_add (f := _), hσ.fin, zero_add]
  let S : Set (Mx D a b) := {y | y.map (finPart D) ∈ K}
  let ν : Measure (Fin a → Fin b → D.what₂.Tau → ℂ) := (μ.restrict S).map π
  have hνA : ∀ A, MeasurableSet A → ν A = μ (π ⁻¹' A ∩ S) := fun A hA => by
    rw [Measure.map_apply hπm hA, Measure.restrict_apply (hπm hA)]
  haveI : ν.IsAddLeftInvariant := by
    refine ⟨fun c => Measure.ext fun A hA => ?_⟩
    rw [Measure.map_apply (measurable_const_add c) hA, hνA _ (measurable_const_add c hA), hνA _ hA]
    have e : π ⁻¹' ((fun x => c + x) ⁻¹' A) ∩ S = (fun y => s c + y) ⁻¹' (π ⁻¹' A ∩ S) := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_preimage, S, Set.mem_setOf_eq, hπs, hfs]
    rw [e, measure_preimage_add]
  haveI : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun A hA => ?_⟩
    obtain ⟨R, hR⟩ := hA.isBounded.exists_norm_le
    choose C hC hCK using fun i j => GlobalTheory.StabCompact.exists_compact_adele D θ hθ R
      ((fun M : Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E) => M i j) '' K)
      (hK.image ((continuous_apply j).comp (continuous_apply i)))
    have hc : IsCompact (Set.pi Set.univ fun i => Set.pi Set.univ fun j => C i j : Set (Mx D a b)) :=
      isCompact_univ_pi fun i => isCompact_univ_pi fun j => hC i j
    rw [hνA _ hA.isClosed.measurableSet]
    haveI : IsFiniteMeasureOnCompacts μ := hμ.toIsFiniteMeasureOnCompacts
    refine lt_of_le_of_lt (measure_mono ?_) (IsFiniteMeasureOnCompacts.lt_top_of_isCompact (μ := μ) hc)
    rintro y ⟨hyA, hyS⟩ i - j -
    refine hCK i j _ ⟨_, hyS, rfl⟩ fun ρ => le_trans ?_ (hR _ hyA)
    exact (norm_le_pi_norm (π y i j) ρ).trans ((norm_le_pi_norm (π y i) j).trans (norm_le_pi_norm (π y) i))
  have hνe : ν = ν.addHaarScalarFactor Measure.addHaar • (Measure.addHaar : Measure (Fin a → Fin b → D.what₂.Tau → ℂ)) :=
    Measure.isAddLeftInvariant_eq_smul ν Measure.addHaar

  set N : ℕ := Module.finrank ℝ (Fin a → Fin b → D.what₂.Tau → ℂ) + 1 with hN
  obtain ⟨C, hC⟩ := hdec N
  let G : (Fin a → Fin b → D.what₂.Tau → ℂ) → ℝ := fun x => C * (1 + ‖x‖) ^ (-(N : ℝ))
  have hGv : Integrable G (Measure.addHaar : Measure (Fin a → Fin b → D.what₂.Tau → ℂ)) :=
    (integrable_one_add_norm (by rw [hN]; push_cast; linarith)).const_mul C
  have hGν : Integrable G ν := by
    rw [hνe]; exact hGv.smul_measure ENNReal.coe_ne_top
  have hGπ : Integrable (G ∘ π) (μ.restrict S) :=
    (integrable_map_measure hGν.aestronglyMeasurable hπm.aemeasurable).1 hGν
  have hbound : ∀ y, ‖f y‖ ≤ G (π y) := by
    intro y
    have hsum : ‖π y‖ ≤ ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖ := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2
        fun j => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun τ => ?_
      refine le_trans ?_ (Finset.single_le_sum (f := fun τ => ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖)
        (fun _ _ => by positivity) (Finset.mem_univ τ))
      refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖θ τ (infPart D (y i j))‖)
        (fun _ _ => by positivity) (Finset.mem_univ i))
      exact Finset.single_le_sum (f := fun j => ‖θ τ (infPart D (y i j))‖) (fun _ _ => by positivity)
        (Finset.mem_univ j)
    have h1 : 0 < 1 + ‖π y‖ := by positivity
    have h2 : (1 + ‖π y‖) ^ N ≤ (1 + ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ^ N :=
      pow_le_pow_left₀ h1.le (by linarith) N
    have h3 := hC y
    have h4 : (1 + ‖π y‖) ^ N * ‖f y‖ ≤ C := le_trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) h3
    show ‖f y‖ ≤ C * (1 + ‖π y‖) ^ (-(N : ℝ))
    rw [Real.rpow_neg h1.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (pow_pos h1 N), mul_comm]
    exact h4
  have hfS : IntegrableOn f S μ :=
    hGπ.mono' hf.aestronglyMeasurable.restrict (Filter.Eventually.of_forall hbound)
  exact hfS.integrable_of_forall_notMem_eq_zero fun y hy => hKf y hy

end GlobalTheory.AdelicIntegrable

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableAdelicMatrixRapidDecayCompactFiniteStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_adelicMatrix_rapid_decay_compact_finite : ∀ (D : D7) (a b : ℕ) (μ : Measure (Mx D a b)), μ.IsAddHaarMeasure → ∀ θ : InfFam D, IsInfFam θ → ∀ f : Mx D a b → ℂ, Continuous f → ∀ K : Set (Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K → (∀ y : Mx D a b, y.map (finPart D) ∉ K → f y = 0) → (∀ N : ℕ, ∃ C : ℝ, ∀ y : Mx D a b, (1 + ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ^ N * ‖f y‖ ≤ C) → Integrable f μ := by
  first | exact @GlobalTheory.AdelicIntegrable.integrable_of_rapid_decay | exact GlobalTheory.AdelicIntegrable.integrable_of_rapid_decay | (intros; apply GlobalTheory.AdelicIntegrable.integrable_of_rapid_decay <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousThetaMatrixCoeffAlongSandwich
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousThetaMatrixCoeffAlongSandwich
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaCoefCont

private theorem measure_fundamentalDomain_ratL_lt_infty {D : D7} (V W : HSp D) (ν : Measure (WO V W)) (𝓕 : Set (WO V W))
    (hν : ν.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 ν) : ν 𝓕 < ⊤ := by
  obtain ⟨hg, -, hsc, -, hdisc, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  haveI := hg
  haveI := hsc
  haveI := hdisc
  haveI : BorelSpace (WO V W) := ⟨rfl⟩
  haveI : Countable (ratL W V) := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (ratL W V) hK hcov ν h𝓕

theorem continuous_coef : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Continuous (fun y : Mx D a b => ∫ u in 𝓕, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) := by
  intro D V W a b P Q ψ hψ ν 𝓕 hν h𝓕 G G' hG hG'
  haveI : BorelSpace (WO V W) := ⟨rfl⟩
  have hfin : ν 𝓕 < ⊤ := measure_fundamentalDomain_ratL_lt_infty V W ν 𝓕 hν h𝓕
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  obtain ⟨C', hC'⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hG'
  obtain ⟨C, hC⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hG
  have hE : Continuous (GlobalTheory.IsoMean.emb V W P Q) := by
    unfold GlobalTheory.IsoMean.emb
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  rw [continuous_iff_continuousAt]
  intro y₀
  haveI : SecondCountableTopology (Mx D a b) := (GlobalTheory.MixModel.lattice_Mx D a b).2.2.1
  haveI : FirstCountableTopology (Mx D a b) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  refine MeasureTheory.continuousAt_of_dominated (bound := fun _ => C * C') ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun y =>
      (((hψ.1.1.comp (continuous_const.mul (GlobalTheory.SplitScalar.continuous_symplO V W continuous_id continuous_const))).mul
        (hG.cont.comp (continuous_id.add continuous_const))).mul
        (continuous_star.comp hG'.cont)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y => Filter.Eventually.of_forall fun u => ?_
    rw [norm_mul, norm_star, heisO, norm_mul, hψ.1.2.1, one_mul]
    exact mul_le_mul (hC _) (hC' _) (norm_nonneg _) ((norm_nonneg (G u)).trans (hC u))
  · exact integrable_const _
  · refine Filter.Eventually.of_forall fun u => ?_
    exact (((hψ.1.1.comp (continuous_const.mul (GlobalTheory.SplitScalar.continuous_symplO V W continuous_const hE))).mul
      (hG.cont.comp (continuous_const.add hE))).mul continuous_const).continuousAt

end GlobalTheory.ThetaCoefCont

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousThetaMatrixCoeffAlongSandwichStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_thetaMatrixCoeff_along_sandwich : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Continuous (fun y : Mx D a b => ∫ u in 𝓕, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) := by
  first | exact @GlobalTheory.ThetaCoefCont.continuous_coef | exact GlobalTheory.ThetaCoefCont.continuous_coef | (intros; apply GlobalTheory.ThetaCoefCont.continuous_coef <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffEqZeroUnlessCharacterTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffEqZeroUnlessCharacterTrivial
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoeffVanish

theorem matrixCoeff_eq_zero : ∀ (D : D7) (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν →
    ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' →
    ∃ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) ∧ ∀ ξ : WO V W, ∀ u ∈ U, u.map (infPart D) = 0 →
      ψ (symplO V W ξ u) ≠ 1 → ∫ x in 𝓕, heisO ψ V W ξ G x * star (G' x) ∂ν = 0 := by
  intro D V W ψ hψ ν 𝓕 hν h𝓕 G G' hG hG'

  obtain ⟨U₁, hU₁, hGfix⟩ := hG.level
  obtain ⟨U₂, hU₂, hG'fix⟩ := hG'.level
  refine ⟨U₁ ⊓ U₂, ?_, ?_⟩
  · rw [AddSubgroup.coe_inf]
    exact hU₁.inter hU₂
  intro ξ u hu hfin hψu
  obtain ⟨hcomp, -, hkeep, hunit, -⟩ := GlobalTheory.ThetaSquare.heisUnitary (V := V) (W := W) hψ
  have hGu : heisO ψ V W u G = G := hGfix u hu.1 hfin
  have hG'u : heisO ψ V W u G' = G' := hG'fix u hu.2 hfin

  have hswap : symplOH V W u ξ = -symplOH V W ξ u := GlobalTheory.MixModel.symplOH_skew V W ξ u
  have hmove : heisO ψ V W u (heisO ψ V W ξ G) = ψ (-symplO V W ξ u) • heisO ψ V W ξ G := by
    have hξG : heisO ψ V W ξ G = ψ (symplOH V W ξ u) • heisO ψ V W (ξ + u) G := by
      have h := hcomp ξ u G
      rwa [hGu] at h
    rw [hcomp u ξ G, add_comm u ξ, hξG, smul_smul, ← AddChar.map_add_eq_mul]
    congr 2
    rw [hswap, GlobalTheory.ThetaSquare.symplO_eq]
    ring

  set c : ℂ := ψ (-symplO V W ξ u) with hc
  have hI := hunit ν 𝓕 hν h𝓕 u (heisO ψ V W ξ G) G' (hkeep ξ G hG) hG'
  rw [hmove, hG'u] at hI
  unfold GlobalTheory.Ker.ipO at hI
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, starRingEnd_apply] at hI
  rw [MeasureTheory.integral_const_mul] at hI
  have hc1 : c ≠ 1 := by
    intro h1
    apply hψu
    have hprod : ψ (symplO V W ξ u) * c = 1 := by
      rw [hc, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rwa [h1, mul_one] at hprod
  have hsub : (c - 1) * ∫ x in 𝓕, heisO ψ V W ξ G x * star (G' x) ∂ν = 0 := by
    rw [sub_mul, one_mul, hI, sub_self]
  rcases mul_eq_zero.mp hsub with h | h
  · exact absurd (sub_eq_zero.mp h) hc1
  · exact h

end GlobalTheory.CoeffVanish

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffEqZeroUnlessCharacterTrivialStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMatrixCoeff_eq_zero_unless_character_trivial : ∀ (D : D7) (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → ∃ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) ∧ ∀ ξ : WO V W, ∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO V W ξ u) ≠ 1 → ∫ x in 𝓕, heisO ψ V W ξ G x * star (G' x) ∂ν = 0 := by
  first | exact @GlobalTheory.CoeffVanish.matrixCoeff_eq_zero | exact GlobalTheory.CoeffVanish.matrixCoeff_eq_zero | (intros; apply GlobalTheory.CoeffVanish.matrixCoeff_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RapidDecayAllRealCoordinatesOfFunctionals
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RapidDecayAllRealCoordinatesOfFunctionals
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DecayCoord

theorem theta_incA {D : D7} (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (x : D.host.E) :
    θ τ (infPart D (incA D x)) = tauE D τ x := by
  have h : infPart D (incA D x) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] x := by
    simp [infPart, incA, inclR, Algebra.TensorProduct.map_tmul]
  rw [h]
  exact (hθ τ).1 x

theorem compAt_emb {D : D7} (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (V W : HSp D) {a b : ℕ}
    (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (y : Mx D a b) :
    compAt θ τ (GlobalTheory.IsoMean.emb V W P Q y) = P.map (tauE D τ) * compAt θ τ y * Q.map (tauE D τ) := by
  have hm : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)), compAt θ τ M = M.map ((θ τ).comp (infPart D)) :=
    fun M => rfl
  have hE : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E),
      (M.map (incA D)).map ((θ τ).comp (infPart D)) = M.map (tauE D τ) := by
    intro m n M; ext i j; simp [theta_incA θ hθ]
  rw [hm, hm, GlobalTheory.IsoMean.emb, Matrix.map_mul, Matrix.map_mul, hE, hE]

theorem exists_left_inv {K : Type*} [Field K] {n a : ℕ} (P : Matrix (Fin n) (Fin a) K) (hP : P.rank = a) :
    ∃ P' : Matrix (Fin a) (Fin n) K, P' * P = 1 := by
  have hker : LinearMap.ker P.mulVecLin = ⊥ := by
    have h1 := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
    rw [Matrix.rank] at hP
    rw [hP, Module.finrank_fin_fun] at h1
    exact Submodule.finrank_eq_zero.1 (by omega)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h2 := congrArg LinearMap.toMatrix' hg
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at h2
  have h3 : LinearMap.toMatrix' P.mulVecLin = P := LinearMap.toMatrix'_toLin' P
  rwa [h3] at h2

theorem exists_right_inv {K : Type*} [Field K] {n b : ℕ} (Q : Matrix (Fin b) (Fin n) K) (hQ : Q.rank = b) :
    ∃ Q' : Matrix (Fin n) (Fin b) K, Q * Q' = 1 := by
  obtain ⟨R, hR⟩ := exists_left_inv Qᵀ (by rw [Matrix.rank_transpose, hQ])
  refine ⟨Rᵀ, ?_⟩
  have := congrArg Matrix.transpose hR
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this

theorem sum_pow_le {κ : Type*} [Fintype κ] [Nonempty κ] (u : κ → ℝ) (hu : ∀ k, 0 ≤ u k) (N : ℕ) :
    (∑ k, u k) ^ N ≤ (Fintype.card κ : ℝ) ^ N * ∑ k, u k ^ N := by
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ u Finset.univ_nonempty
  have h1 : ∑ k, u k ≤ Fintype.card κ * u j := by
    have := Finset.sum_le_card_nsmul Finset.univ u (u j) (fun k _ => hj k (Finset.mem_univ _))
    simpa [nsmul_eq_mul] using this
  calc (∑ k, u k) ^ N ≤ (Fintype.card κ * u j) ^ N :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun k _ => hu k) h1 N
    _ = (Fintype.card κ : ℝ) ^ N * u j ^ N := mul_pow _ _ _
    _ ≤ _ := by
        gcongr
        exact Finset.single_le_sum (f := fun k => u k ^ N) (fun k _ => pow_nonneg (hu k) N) (Finset.mem_univ j)

theorem trace_single {a b : ℕ} (Y : Matrix (Fin a) (Fin b) ℂ) (k : Fin a) (l : Fin b) (α : ℂ) :
    (Yᴴ * Matrix.single k l α).trace = star (Y k l) * α := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single l, Finset.sum_eq_single k]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · simp
  · intro i _ hi; apply Finset.sum_eq_zero; intro j _; simp [Ne.symm hi]
  · simp

theorem norm_le_re (c w : ℂ) (hc : c ≠ 0) :
    ‖w‖ ≤ |2 * (c * (star w * c⁻¹)).re| + |2 * (c * (star w * (Complex.I * c⁻¹))).re| := by
  have e1 : c * (star w * c⁻¹) = star w := by field_simp
  have e2 : c * (star w * (Complex.I * c⁻¹)) = Complex.I * star w := by field_simp
  rw [e1, e2]
  have := Complex.norm_le_abs_re_add_abs_im w
  simp only [Complex.star_def, Complex.conj_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.conj_im, abs_mul]
  norm_num
  linarith [abs_nonneg w.re, abs_nonneg w.im]

end GlobalTheory.DecayCoord

namespace GlobalTheory.DecayCoord

theorem det_gramAt_ne {D : D7} (V : HSp D) (τ : D.what₂.Tau) : (gramAt D V τ).det ≠ 0 := by
  unfold gramAt
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero _).2 (GlobalTheory.StabCompact.det_gram_ne_zero V)

theorem herm_key {D : D7} (V W : HSp D) (τ : D.what₂.Tau) {a b : ℕ} (Pc : Matrix (Fin W.rank) (Fin a) ℂ)
    (Pl : Matrix (Fin a) (Fin W.rank) ℂ) (hP : Pl * Pc = 1) (Qc : Matrix (Fin b) (Fin V.rank) ℂ)
    (Qr : Matrix (Fin V.rank) (Fin b) ℂ) (hQ : Qc * Qr = 1) (Y X : Matrix (Fin a) (Fin b) ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.hermAt V W τ ((gramAt D W τ)⁻¹ * Plᴴ * X * Qrᴴ * gramAt D V τ) (Pc * Y * Qc) =
      (Yᴴ * X).trace := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.hermAt
  set GV := gramAt D V τ
  set GW := gramAt D W τ
  have hW : GW * GW⁻¹ = 1 := Matrix.mul_nonsing_inv GW (Ne.isUnit (det_gramAt_ne W τ))
  have hV : GV * GV⁻¹ = 1 := Matrix.mul_nonsing_inv GV (Ne.isUnit (det_gramAt_ne V τ))
  have hP' : Pcᴴ * Plᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hP, Matrix.conjTranspose_one]
  have hQ' : Qrᴴ * Qcᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQ, Matrix.conjTranspose_one]
  have e : GV⁻¹ * (Pc * Y * Qc)ᴴ * GW * (GW⁻¹ * Plᴴ * X * Qrᴴ * GV) = GV⁻¹ * ((Qcᴴ * Yᴴ * X * Qrᴴ) * GV) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc GW GW⁻¹, hW, Matrix.one_mul, ← Matrix.mul_assoc Pcᴴ Plᴴ, hP', Matrix.one_mul]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc _ GV, hV, Matrix.mul_one, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ', Matrix.one_mul]

end GlobalTheory.DecayCoord

namespace GlobalTheory.DecayCoord

theorem decay_real_coords : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → ∀ θ : InfFam D, IsInfFam θ → ∀ f : Mx D a b → ℂ, (∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (m : ℕ), ∃ C : ℝ, ∀ y : Mx D a b, |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt V W τ z (compAt θ τ (GlobalTheory.IsoMean.emb V W P Q y))| ^ m * ‖f y‖ ≤ C) → ∀ N : ℕ, ∃ C : ℝ, ∀ y : Mx D a b, (1 + ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ^ N * ‖f y‖ ≤ C := by
  intro D V W a b P Q hP hQ θ hθ f hf N
  classical
  obtain ⟨Pl, hPl⟩ := exists_left_inv P hP
  obtain ⟨Qr, hQr⟩ := exists_right_inv Q hQ
  have hPlτ : ∀ τ, Pl.map (tauE D τ) * P.map (tauE D τ) = 1 := fun τ => by
    rw [← Matrix.map_mul, hPl, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQrτ : ∀ τ, Q.map (tauE D τ) * Qr.map (tauE D τ) = 1 := fun τ => by
    rw [← Matrix.map_mul, hQr, Matrix.map_one _ (map_zero _) (map_one _)]
  let c : D.what₂.Tau → ℂ := fun τ => tauE D τ D.host.xi0
  have hc : ∀ τ, c τ ≠ 0 := fun τ => (map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  let zOf : D.what₂.Tau → Matrix (Fin a) (Fin b) ℂ → Matrix (Fin W.rank) (Fin V.rank) ℂ := fun τ X =>
    (gramAt D W τ)⁻¹ * (Pl.map (tauE D τ))ᴴ * X * (Qr.map (tauE D τ))ᴴ * gramAt D V τ
  let zι : D.what₂.Tau × Fin a × Fin b × Bool → Matrix (Fin W.rank) (Fin V.rank) ℂ := fun i =>
    zOf i.1 (Matrix.single i.2.1 i.2.2.1 (if i.2.2.2 then Complex.I * (c i.1)⁻¹ else (c i.1)⁻¹))
  let ℓ : D.what₂.Tau × Fin a × Fin b × Bool → Mx D a b → ℝ := fun i y =>
    |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt V W i.1 (zι i) (compAt θ i.1 (GlobalTheory.IsoMean.emb V W P Q y))|
  have hterm : ∀ (y : Mx D a b) (τ : D.what₂.Tau) (k : Fin a) (l : Fin b),
      ‖θ τ (infPart D (y k l))‖ ≤ ∑ β : Bool, ℓ (τ, k, l, β) y := by
    intro y τ k l
    have hs : ∀ α : ℂ, GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt V W τ (zOf τ (Matrix.single k l α))
        (compAt θ τ (GlobalTheory.IsoMean.emb V W P Q y)) = 2 * (c τ * (star (compAt θ τ y k l) * α)).re := by
      intro α
      rw [compAt_emb θ hθ τ V W P Q y]
      show 2 * (c τ * GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.hermAt V W τ _ _).re = _
      rw [herm_key V W τ _ _ (hPlτ τ) _ _ (hQrτ τ), trace_single]
    rw [Fintype.sum_bool]
    simp only [ℓ, zι, if_true, if_false, Bool.false_eq_true]
    rw [hs, hs]
    have := norm_le_re (c τ) (compAt θ τ y k l) (hc τ)
    rw [add_comm]
    exact this
  have hS : ∀ y : Mx D a b, (∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ≤ ∑ i, ℓ i y := by
    intro y
    simp only [Fintype.sum_prod_type]
    gcongr with τ _ k _ l _
    exact hterm y τ k l
  obtain ⟨τ0⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  obtain ⟨C0, hC0⟩ := hf τ0 0 0
  choose Cf hCf using fun i : D.what₂.Tau × Fin a × Fin b × Bool => hf i.1 (zι i) N
  refine ⟨(Fintype.card (Option (D.what₂.Tau × Fin a × Fin b × Bool)) : ℝ) ^ N * (C0 + ∑ i, Cf i), fun y => ?_⟩
  let u : Option (D.what₂.Tau × Fin a × Fin b × Bool) → ℝ := fun o => o.elim 1 fun i => ℓ i y
  have hu : ∀ o, 0 ≤ u o := fun o => by cases o <;> simp [u, ℓ]
  have hsum : ∑ o, u o = 1 + ∑ i, ℓ i y := by rw [Fintype.sum_option]; rfl
  have hpow : ∑ o, u o ^ N = 1 + ∑ i, ℓ i y ^ N := by rw [Fintype.sum_option]; simp [u]
  have hS0 : 0 ≤ ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖ := by positivity
  have hf0 : 0 ≤ ‖f y‖ := norm_nonneg _
  have hC0' : ‖f y‖ ≤ C0 := by simpa using hC0 y
  have hCf' : ∑ i, ℓ i y ^ N * ‖f y‖ ≤ ∑ i, Cf i := Finset.sum_le_sum fun i _ => hCf i y
  calc (1 + ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ^ N * ‖f y‖
      ≤ (1 + ∑ i, ℓ i y) ^ N * ‖f y‖ := by gcongr; exact hS y
    _ = (∑ o, u o) ^ N * ‖f y‖ := by rw [hsum]
    _ ≤ ((Fintype.card (Option (D.what₂.Tau × Fin a × Fin b × Bool)) : ℝ) ^ N * ∑ o, u o ^ N) * ‖f y‖ := by
        gcongr; exact sum_pow_le u hu N
    _ = (Fintype.card (Option (D.what₂.Tau × Fin a × Fin b × Bool)) : ℝ) ^ N *
          (‖f y‖ + ∑ i, ℓ i y ^ N * ‖f y‖) := by rw [hpow, ← Finset.sum_mul]; ring
    _ ≤ _ := by gcongr

end GlobalTheory.DecayCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RapidDecayAllRealCoordinatesOfFunctionalsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rapid_decay_all_real_coordinates_of_functionals : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → ∀ θ : InfFam D, IsInfFam θ → ∀ f : Mx D a b → ℂ, (∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (m : ℕ), ∃ C : ℝ, ∀ y : Mx D a b, |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt V W τ z (compAt θ τ (GlobalTheory.IsoMean.emb V W P Q y))| ^ m * ‖f y‖ ≤ C) → ∀ N : ℕ, ∃ C : ℝ, ∀ y : Mx D a b, (1 + ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ^ N * ‖f y‖ ≤ C := by
  first | exact @GlobalTheory.DecayCoord.decay_real_coords | exact GlobalTheory.DecayCoord.decay_real_coords | (intros; apply GlobalTheory.DecayCoord.decay_real_coords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableThetaMatrixCoeffIsotropicRational
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMean

theorem integrable_coef : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)), μ.IsAddHaarMeasure → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Integrable (fun y => ∫ u in 𝓕, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) μ := by
  intro D V W a b P Q hP hQ _hiso ψ hψ μ hμ ν 𝓕 hν h𝓕 G G' hG hG'
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨U, hU, hvan⟩ := GlobalTheory.T.thetaMatrixCoeff_eq_zero_unless_character_trivial D V W ψ hψ ν 𝓕 hν h𝓕 G G' hG hG'
  obtain ⟨K, hK, hKmem⟩ := GlobalTheory.T.finitePart_mem_compact_of_isotropicAnnihilator D V W a b P Q hP hQ ψ hψ U hU
  refine GlobalTheory.T.integrable_adelicMatrix_rapid_decay_compact_finite D a b μ hμ θ hθ _ (GlobalTheory.T.continuous_thetaMatrixCoeff_along_sandwich D V W a b P Q ψ hψ ν 𝓕 hν h𝓕 G G' hG hG') K hK ?_ ?_
  · intro y hy
    by_contra hne
    apply hy
    refine hKmem y fun u hu hu0 => ?_
    by_contra h1
    exact hne (hvan _ u hu hu0 h1)
  · refine GlobalTheory.T.rapid_decay_all_real_coordinates_of_functionals D V W a b P Q hP hQ θ hθ _ fun τ z m => ?_
    obtain ⟨C, hC⟩ := GlobalTheory.T.thetaMatrixCoeff_rapid_decay_real_functional D V W ψ hψ ν 𝓕 hν h𝓕 G G' hG hG' θ hθ τ z m
    exact ⟨C, fun y => hC _⟩

end GlobalTheory.IsoMean

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableThetaMatrixCoeffIsotropicRationalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_thetaMatrixCoeff_isotropic_rational : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)), μ.IsAddHaarMeasure → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Integrable (fun y => ∫ u in 𝓕, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) μ := by
  first | exact @GlobalTheory.IsoMean.integrable_coef | exact GlobalTheory.IsoMean.integrable_coef | (intros; apply GlobalTheory.IsoMean.integrable_coef <;> assumption)
end
