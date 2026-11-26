module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorEqTopOrLeKerFiniteLengthModules
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanDarbouxCoordsOneParamOrbitSmooth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemAdelicLatticeAtPlaceOfTensorWithLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesPolynomialVectorsSmallPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorFinal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstMemberMaximalCompactPreservesPolynomialFock
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstMemberMaximalCompactPreservesPolynomialFock
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.FockCompactX

open GlobalTheory.RealLift GlobalTheory.FockCompactW

section Der

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

theorem at_mul_left {m p q : Type} [Fintype p] {z : Matrix p q (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hz : At (evI F) z)
    (A : Matrix m p (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : At (evI F) (A * z) := by
  intro u hu; rw [← Matrix.mul_smul, hz u hu, Matrix.mul_zero]

theorem sd_intertwine_left {M : Model σ Y W} {ψ : AddChar (AF F) ℂ} {χ₁ χ₂ : Chr F E} {om : Rep σ Y W}
    (hw : M.IsWeil ψ χ₁ χ₂ om) (h : UA σ Y.J) {f f₁ g g₁ : SInf F (Fin n × Fin d)}
    (hf : Acts (evI F) (om (h, 1)) f g) (hf₁ : Acts (evI F) (om (h, 1)) f₁ g₁) {u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))}
    (hD : SD (M.heisLine ψ u) f f₁) : SD (M.heisLine ψ (mat h * u)) g g₁ := by
  have hS := IsUWeilPair.isUSplitting hw
  intro r hr l hl
  have h1 := hD r hr _ (hS.adm (h, 1) l hl)
  simp only [LinearMap.comp_apply] at h1
  rw [sa_of_acts hf₁ r hr] at h1
  refine h1.congr_of_eventuallyEq (.of_forall fun t => ?_)
  have h2 := hS.impl (h, 1) (realAd F t • u) (pureA F f r) (Submodule.subset_span ⟨f, r, hr, rfl⟩)
  have h3 : actAB (cA σ) ((h, 1) : UA σ Y.J × UA σ W.J) (realAd F t • u) = realAd F t • (mat h * u) := by
    change mat h * (realAd F t • u) * (1 : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ = _
    rw [Matrix.transpose_one, Matrix.mul_one, Matrix.mul_smul]
  rw [h3, sa_of_acts hf r hr] at h2
  exact congrArg l h2.symm

end Der

theorem pol_stable_compact_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ k ∈ KInf σ X τ, ∀ f ∈ M.Pol ψ τ,
          ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (k, 1)) f f₁ → f₁ ∈ M.Pol ψ τ := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om hψ _ _ _ _ _ _ _ _ hw τ _ _ k hk f hf f₁ hf₁
  have h1 : (1 : UA σ W.J) ∈ UAt σ W (evI F) := by
    intro u _
    simp [mat]
  obtain ⟨A, hA⟩ := exists_op_of_UAt hψ hw (k, 1) hk.1 h1
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ ψ _ _ M.co hψ
  have hL := actsLaws F (Fin n × Fin d)
  have hSD : ∀ u, At (evI F) u → ∀ φ, SD (M.heisLine ψ u) φ (D u φ) := fun u hu φ => (hD u hu φ).1
  have hAD : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) φ (D u φ) :=
    fun u hu φ => (hL φ _ φ).1 _ (FockCompactW.heisLine_zero M ψ u) (hSD u hu φ)
  have hint : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ (mat k * u)) (A φ) (A (D u φ)) :=
    fun u hu φ => (hL _ _ φ).1 _ (FockCompactW.heisLine_zero M ψ _)
      (sd_intertwine_left hw k (hA φ) (hA _) (hSD u hu φ))
  have hkk : mat k * mat k⁻¹ = 1 := by
    change mat (k * k⁻¹) = 1
    rw [mul_inv_cancel]
    rfl
  have hcan : ∀ u : Matrix (Fin n) (Fin d) (AE F E), mat k * (mat k⁻¹ * u) = u := fun u => by
    rw [← Matrix.mul_assoc, hkk, Matrix.one_mul]
  have hle : M.Pol ψ τ ≤ (M.Pol ψ τ).comap A := by
    refine sInf_le ⟨fun f₀ hf₀ => ?_, fun u hu φ hφ φ₁ hφ₁ => ?_⟩
    · refine Submodule.mem_sInf.2 fun N hN => hN.1 _ ?_
      obtain ⟨ε, hε⟩ := hf₀
      refine ⟨ε, fun u u' hu hu' huu g g' hg hg' => ?_⟩
      have hv := at_mul_left hu (mat k⁻¹)
      have hv' := at_mul_left hu' (mat k⁻¹)
      have h1 := hint _ hv f₀
      have h2 := hint _ hv' f₀
      rw [hcan] at h1 h2
      have e1 := (hL _ _ _).2.2.1 _ hg h1
      have e2 := (hL _ _ _).2.2.1 _ hg' h2
      have key := hε _ _ hv hv' (fun w => ?_) _ _ (hAD _ hv f₀) (hAD _ hv' f₀)
      · rw [e1, e2, key, map_smul]
      · have hm : (mat k⁻¹).map (piInf (τ w)) * (mat k).map (piInf (τ w)) = 1 := by
          rw [← Matrix.map_mul]
          change (mat (k⁻¹ * k)).map _ = 1
          rw [inv_mul_cancel]
          exact Matrix.map_one _ (map_zero _) (map_one _)
        have hm' : (mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w)) = 1 := mul_eq_one_comm.1 hm
        have hc : (mat k⁻¹).map (piInf (τ w)) * X.θ w = X.θ w * (mat k⁻¹).map (piInf (τ w)) := by
          calc _ = (mat k⁻¹).map (piInf (τ w)) * X.θ w *
                ((mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w))) := by rw [hm', Matrix.mul_one]
            _ = (mat k⁻¹).map (piInf (τ w)) * (X.θ w * (mat k).map (piInf (τ w))) *
                (mat k⁻¹).map (piInf (τ w)) := by simp only [Matrix.mul_assoc]
            _ = _ := by rw [← (hk.2 w).eq, ← Matrix.mul_assoc, hm, Matrix.one_mul]
        rw [Matrix.map_mul, Matrix.map_mul, huu w, Matrix.mul_smul]
        congr 1
        simp only [← Matrix.mul_assoc]
        rw [hc]
    · have e : φ₁ = D u φ := (hL _ _ _).2.2.1 _ hφ₁ (hAD u hu φ)
      rw [e]
      exact Submodule.mem_sInf.2 fun N hN =>
        hN.2 _ (at_mul_left hu _) _ (Submodule.mem_sInf.1 hφ N hN) _ (hint u hu φ)
  rw [(hL f f₁ (A f)).2.2.2.1 _ hf₁ (hA f)]
  exact hle hf

end GlobalTheory.FockCompactX

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstMemberMaximalCompactPreservesPolynomialFockStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstMember_maximalCompact_preserves_polynomialFock : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → GlobalTheory.LFun.IsHecke F E χX → GlobalTheory.LFun.IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w, (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X τ, ∀ f ∈ M.Pol ψ τ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (k, 1)) f f₁ → f₁ ∈ M.Pol ψ τ := by
  first | exact @GlobalTheory.FockCompactX.pol_stable_compact_left | exact GlobalTheory.FockCompactX.pol_stable_compact_left | (intros; apply GlobalTheory.FockCompactX.pol_stable_compact_left <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstMemberLieAlgebraPreservesPolynomialFock
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelResidueCharacterPow
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelResidueCharacterPow
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchimedeanUnitaryL2

open MeasureTheory
open scoped ENNReal

theorem integral_norm_sq_eq_pair_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∀ (μ : MeasureTheory.Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F)), μ.IsAddHaarMeasure →
        ∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om _ _ _ _ _ _ _ _ _ hW γ _ T hA μ hμ t f
  obtain ⟨g, hg, hg0⟩ : ∃ g : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ℂ,
      g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∧ g 0 ≠ 0 := by
    refine ⟨_, GlobalTheory.SchANonzero.indicator_intPts_mem_SB F _, ?_⟩
    have h0 : (0 : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∈ GlobalTheory.SchANonzero.intPts F (Fin n × Fin d) :=
      fun i _ v => zero_mem (v.adicCompletionIntegers F)
    rw [Set.indicator_of_mem h0]
    exact one_ne_zero
  obtain ⟨μA, hμA, c, hc0, hct, hc⟩ := exists_haar F _ μ g hg hg0
  let r : (Fin n × Fin d → AF F) → ℂ := fun x => g fun i => (x i).2
  have hS : tens (evI F) f r ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hr : ∀ x z, At (evI F) z → r (x + z) = r x := by
    intro x z hz
    refine congrArg g (funext fun i => ?_)
    show (x i).2 + (z i).2 = (x i).2
    have h := hz (((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F) (by
      show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
      exact map_zero _)
    have h2 : (((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) * ((z i).1, (z i).2)).2 =
        (0 : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F).2 := congrArg Prod.snd (congrFun h i)
    have hz0 : (z i).2 = 0 := by simpa using h2
    rw [hz0, add_zero]
  have hU := (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hW).unit μA hμA (γ (Multiplicative.ofAdd t), 1) (tens (evI F) f r) hS
  have hAct : om (γ (Multiplicative.ofAdd t), 1) (tens (evI F) f r) = tens (evI F) (T t f) r := hA t f r ⟨hr, hS⟩
  change ∫⁻ x, ‖om (γ (Multiplicative.ofAdd t), 1) (tens (evI F) f r) x‖ₑ ^ 2 ∂μA = _ at hU
  rw [hAct] at hU
  have h1 := ((hc (T t f)).symm.trans hU).trans (hc f)
  haveI := opensMeasurable F (Fin n × Fin d)
  rw [integral_sq_eq μ (T t f).continuous, integral_sq_eq μ f.continuous, (ENNReal.mul_right_inj hc0 hct).1 h1]

end GlobalTheory.ArchimedeanUnitaryL2

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelResidueCharacterPowStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_model_residue_character_pow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∀ (μ : MeasureTheory.Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F)), μ.IsAddHaarMeasure →
        ∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  first | exact @GlobalTheory.ArchimedeanUnitaryL2.integral_norm_sq_eq_pair_left | exact GlobalTheory.ArchimedeanUnitaryL2.integral_norm_sq_eq_pair_left | (intros; apply GlobalTheory.ArchimedeanUnitaryL2.integral_norm_sq_eq_pair_left <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanDarbouxCoordsOneParamOrbitSmoothStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_darboux_coords_one_param_orbit_smooth : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W), ∀ γ ∈ Lines σ X, ∀ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)) ∧
    ∃ u' : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u' ∧
      HasDerivAt (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)) (GlobalTheory.HeisOrbit.archCo M.co u') 0 := by
  first | exact @GlobalTheory.HeisOrbitSmoothLeft.archCo_orbit_smooth_left | exact GlobalTheory.HeisOrbitSmoothLeft.archCo_orbit_smooth_left | (intros; apply GlobalTheory.HeisOrbitSmoothLeft.archCo_orbit_smooth_left <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorLeftIntertwinesHeisenbergDerivative
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorLeftIntertwinesHeisenbergDerivative
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.HeisOrbit

namespace GlobalTheory.HeisOrbit

theorem weil_heisDeriv_intertw_left {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (χX χW : Chr F E) (om : Rep σ X W) (hψ : IsStd ψ) (hW : M.IsWeil ψ χX χW om) (g : UA σ X.J)
    (Tg : SInf F (Fin n × Fin d) → SInf F (Fin n × Fin d))
    (hTg : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, 1)) f (Tg f)) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hu : At (evI F) u) (f f₁ : SInf F (Fin n × Fin d)) (hf : ActsD (evI F) (M.heisLine ψ u) f f₁) (y) :
    Tg f₁ y = GlobalTheory.HeisOrbit.dOp (GlobalTheory.HeisOrbit.archCo M.co (mat g * u)).1
      (GlobalTheory.HeisOrbit.archCo M.co (mat g * u)).2 (Tg f) y := by
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin n) (Fin d) (Fin n × Fin d) ψ (incM F X.J) (incM F W.J) M.co hψ
  have hS := hW.isUSplitting
  have laws := GlobalTheory.RealLift.actsLaws F (Fin n × Fin d)
  have h1 : f₁ = D u f := by
    have hAD : ActsD (evI F) (M.heisLine ψ u) f (D u f) :=
      (laws f (D u f) (D u f)).1 (M.heisLine ψ u) (fun t => by funext x; simp [Model.heisLine, Darboux.rho, schr])
        (hD u hu f).1
    exact (laws f f₁ (D u f)).2.2.1 _ hf hAD
  have h2 : ∀ (f' : SInf F (Fin n × Fin d)) (g' : (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ), g' ∈ SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) →
      om (g, 1) (pureA F f' g') = pureA F (Tg f') g' := by
    intro f' g' hg
    have hr : Rest (evI F) (⇑f') (fun x => g' (fun i => (x i).2)) := by
      refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨f', g', hg, rfl⟩⟩
      show g' _ = g' _
      congr 1
      funext i
      show (x i).2 + (z i).2 = (x i).2
      rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz, add_zero]
    exact hTg f' _ hr
  set g₀ : (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ := (GlobalTheory.RealLift.intPts F (Fin n × Fin d)).indicator 1 with hg₀def
  have hg₀ : g₀ ∈ SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) := GlobalTheory.RealLift.indicator_intPts_mem_SB
  have hg₀0 : g₀ 0 = 1 := by rw [hg₀def, Set.indicator_of_mem GlobalTheory.RealLift.zero_mem_intPts]; rfl
  set x₀ := GlobalTheory.RealLift.ptAt y (0 : Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) with hx₀
  set u' := mat g * u with hu'def
  have hu' : At (evI F) u' := fun a ha => by rw [hu'def, ← Matrix.mul_smul, hu a ha, Matrix.mul_zero]
  have hl := GlobalTheory.RealLift.eval_mem_adm (F := F) x₀
  have hl' := hS.adm (g, 1) _ hl
  have dA := (hD u hu f).1 g₀ hg₀ _ hl'
  have dB := (hD u' hu' (Tg f)).1 g₀ hg₀ _ hl
  have hfun : (fun t : ℝ => (LinearMap.proj x₀ ∘ₗ om (g, 1)) (M.co.rho ψ (realAd F t • u) (pureA F f g₀))) =
      fun t : ℝ => (LinearMap.proj x₀ : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ)
        (M.co.rho ψ (realAd F t • u') (pureA F (Tg f) g₀)) := by
    funext t
    rw [LinearMap.comp_apply, hS.impl (g, 1) _ _ (Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩), h2 f g₀ hg₀]
    congr 3
    simp [actAB, hu'def, mat, Matrix.mul_smul]
  change HasDerivAt (fun t : ℝ => (LinearMap.proj x₀ ∘ₗ om (g, 1))
    (M.co.rho ψ (realAd F t • u) (pureA F f g₀))) _ 0 at dA
  rw [hfun] at dA
  have e := dA.unique dB
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, h2 _ g₀ hg₀, hx₀, GlobalTheory.RealLift.pureA_ptAt, hg₀0,
    mul_one] at e
  rw [h1, e, (hD u' hu' (Tg f)).2]
  rfl

end GlobalTheory.HeisOrbit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorLeftIntertwinesHeisenbergDerivativeStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_operator_left_intertwines_heisenberg_derivative : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsStd ψ → M.IsWeil ψ χX χW om → ∀ (g : UA σ X.J) (Tg : SInf F (Fin n × Fin d) → SInf F (Fin n × Fin d)),
    (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, 1)) f (Tg f)) → ∀ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u →
    ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ → ∀ y,
      Tg f₁ y = GlobalTheory.HeisOrbit.dOp (GlobalTheory.HeisOrbit.archCo M.co (mat g * u)).1 (GlobalTheory.HeisOrbit.archCo M.co (mat g * u)).2 (Tg f) y := by
  first | exact @GlobalTheory.HeisOrbit.weil_heisDeriv_intertw_left | exact GlobalTheory.HeisOrbit.weil_heisDeriv_intertw_left | (intros; apply GlobalTheory.HeisOrbit.weil_heisDeriv_intertw_left <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanWeilLineIntertwinesHeisenbergLeft
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanWeilLineIntertwinesHeisenbergLeft
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

noncomputable section

theorem GlobalTheory.ArchLineAct.intertwine_pair_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∃ A : ℝ → ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
          (∀ w, Continuous fun t => A t w) ∧ (∀ s t, A (s + t) = (A s).comp (A t)) ∧ A 0 = LinearMap.id ∧
          ∀ (t : ℝ) (p q : (Fin n × Fin d → mixedEmbedding.mixedSpace F)) (f g : SInf F (Fin n × Fin d)),
            ⇑g = GlobalTheory.GaussLine.heisFun (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) p q ⇑f →
            ⇑(T t g) = GlobalTheory.GaussLine.heisFun (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) (A t (p, q)).1 (A t (p, q)).2 ⇑(T t f) := by
  intro F E _ _ _ _ _ σ _hcm n d X W M ψ χX χW om hψ _ _ _ _ _ _ _ _ hWeil γ hγ T hTact
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.ArchRest.exists_rest_arch (F := F) (Fin n × Fin d)
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hWeil
  have hRsh : ∀ x z, At (evI F) z → R (x + z) = R x := (hR 0).1
  let L : ℝ → Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] Matrix (Fin n) (Fin d) (AE F E) :=
    fun t => GlobalTheory.ArchLineAct.lmulL (k := d) (mat (γ (Multiplicative.ofAdd t)))
  have hmat : ∀ g h : UA σ X.J, mat (g * h) = mat g * mat h := fun _ _ => rfl
  have hmat1 : mat (1 : UA σ X.J) = 1 := rfl
  refine ⟨fun t => GlobalTheory.ArchLineAct.archMap M.co (L t), fun w => ?_, fun s t => ?_, ?_, fun t p q f g hg => ?_⟩
  · have hm : Continuous fun t : ℝ => (mat (γ (Multiplicative.ofAdd t))) :=
      (Units.continuous_val.comp (continuous_subtype_val.comp (hγ.1.comp continuous_ofAdd)))
    set u := M.co.e.symm (GlobalTheory.ArchLineAct.archLift w.1, GlobalTheory.ArchLineAct.archLift w.2) with hu
    let Ru : Matrix (Fin n) (Fin n) (AE F E) →ₗ[AF F] Matrix (Fin n) (Fin d) (AE F E) :=
      { toFun := fun x => x * u, map_add' := fun x y => Matrix.add_mul x y u,
        map_smul' := fun c x => Matrix.smul_mul c x u }
    let K := M.co.e.toLinearMap ∘ₗ Ru
    haveI : IsModuleTopology (AF F) (Matrix (Fin n) (Fin n) (AE F E)) :=
      inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin n → AE F E))
    have hK : Continuous K := IsModuleTopology.continuous_of_linearMap K
    have hc : Continuous fun t : ℝ => M.co.e (L t u) := hK.comp hm
    show Continuous fun t : ℝ => (GlobalTheory.ArchLineAct.archPart (M.co.e (L t u)).1,
      GlobalTheory.ArchLineAct.archPart (M.co.e (L t u)).2)
    exact Continuous.prodMk
      (continuous_pi fun i => GlobalTheory.ArchLineAct.continuous_evI.comp ((continuous_apply i).comp (continuous_fst.comp hc)))
      (continuous_pi fun i => GlobalTheory.ArchLineAct.continuous_evI.comp ((continuous_apply i).comp (continuous_snd.comp hc)))
  · show GlobalTheory.ArchLineAct.archMap M.co (L (s + t)) =
      (GlobalTheory.ArchLineAct.archMap M.co (L s)).comp (GlobalTheory.ArchLineAct.archMap M.co (L t))
    rw [GlobalTheory.ArchLineAct.archMap_comp]
    congr 1
    refine LinearMap.ext fun x => ?_
    show mat (γ (Multiplicative.ofAdd (s + t))) * x =
      mat (γ (Multiplicative.ofAdd s)) * (mat (γ (Multiplicative.ofAdd t)) * x)
    rw [ofAdd_add, map_mul, hmat, Matrix.mul_assoc]
  · show GlobalTheory.ArchLineAct.archMap M.co (L 0) = LinearMap.id
    have hL : L 0 = LinearMap.id := by
      refine LinearMap.ext fun x => ?_
      show mat (γ (Multiplicative.ofAdd 0)) * x = x
      rw [ofAdd_zero, map_one, hmat1, Matrix.one_mul]
    rw [hL, GlobalTheory.ArchLineAct.archMap_id]
  · set u := M.co.e.symm (GlobalTheory.ArchLineAct.archLift p, GlobalTheory.ArchLineAct.archLift q) with hu
    have hue : M.co.e u = (GlobalTheory.ArchLineAct.archLift p, GlobalTheory.ArchLineAct.archLift q) :=
      LinearEquiv.apply_symm_apply _ _
    have hu' : At (evI F) (L t u) := GlobalTheory.ArchLineAct.at_lin _ (GlobalTheory.ArchLineAct.at_symm _ p q)
    have hue' := GlobalTheory.ArchLineAct.coord_eq M.co hu'
    have himpl := hW.impl (γ (Multiplicative.ofAdd t), (1 : UA σ W.J)) u (tens (evI F) (⇑f) R) (hR f).2
    have hact : GlobalTheory.WeilM.actAB (cA σ) (γ (Multiplicative.ofAdd t), (1 : UA σ W.J)) u = L t u := by
      show (mat (γ (Multiplicative.ofAdd t))) * u * ((1 : UA σ W.J) : GL (Fin d) (AE F E)).1ᵀ =
        mat (γ (Multiplicative.ofAdd t)) * u
      rw [show ((1 : UA σ W.J) : GL (Fin d) (AE F E)).1 = 1 from rfl, Matrix.transpose_one, Matrix.mul_one]
    rw [hact, GlobalTheory.ArchLineAct.rho_tens hψ M.co u p q hue (⇑f) R hRsh, ← hg, hTact t g R (hR g),
      hTact t f R (hR f), GlobalTheory.ArchLineAct.rho_tens hψ M.co (L t u) _ _ hue' _ R hRsh] at himpl
    funext x
    have h := congrFun himpl (GlobalTheory.ArchLineAct.archLift x)
    rw [GlobalTheory.ArchLineAct.tens_archLift _ R hRsh, GlobalTheory.ArchLineAct.tens_archLift _ R hRsh] at h
    exact mul_right_cancel₀ hR0 h

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanWeilLineIntertwinesHeisenbergLeftStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_weil_line_intertwines_heisenberg_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∃ A : ℝ → ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
          (∀ w, Continuous fun t => A t w) ∧ (∀ s t, A (s + t) = (A s).comp (A t)) ∧ A 0 = LinearMap.id ∧
          ∀ (t : ℝ) (p q : (Fin n × Fin d → mixedEmbedding.mixedSpace F)) (f g : SInf F (Fin n × Fin d)),
            ⇑g = GlobalTheory.GaussLine.heisFun (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) p q ⇑f →
            ⇑(T t g) = GlobalTheory.GaussLine.heisFun (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) (A t (p, q)).1 (A t (p, q)).2 ⇑(T t f) := by
  first | exact @GlobalTheory.ArchLineAct.intertwine_pair_left | exact GlobalTheory.ArchLineAct.intertwine_pair_left | (intros; apply GlobalTheory.ArchLineAct.intertwine_pair_left <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousArchimedeanWeilOperatorLinePairX
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousArchimedeanWeilOperatorLinePairX
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical
open GlobalTheory.WeilM

namespace GlobalTheory.ArchLineContPairLeft

theorem continuous_apply : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∀ (f : SInf F (Fin n × Fin d)) (x : (Fin n × Fin d → mixedEmbedding.mixedSpace F)), Continuous fun t => T t f x := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om _ _ _ _ _ _ _ _ _ hW γ hγ T hAct f x
  classical
  let κ := Fin n × Fin d
  let g₀ : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := (GlobalTheory.SchANonzero.intPts F κ).indicator 1
  have hg₀ : g₀ ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := GlobalTheory.SchANonzero.indicator_intPts_mem_SB F κ
  let r₀ : (κ → AF F) → ℂ := fun y => g₀ (fun i => (y i).2)
  have htens : ∀ h : SInf F κ, tens (evI F) (⇑h) r₀ = pureA F (⇑h) g₀ := fun h => rfl
  have hRest : ∀ h : SInf F κ, Rest (evI F) (⇑h) r₀ := by
    intro h
    refine ⟨fun y z hz => ?_, ?_⟩
    · have h2 : ∀ i, (z i).2 = 0 := by
        intro i
        have hu := hz ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) (by
          show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
          exact map_zero _)
        have h1 : (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 = 0 := congrArg Prod.snd (congrFun hu i)
        rwa [one_mul] at h1
      show g₀ (fun i => (y i + z i).2) = g₀ (fun i => (y i).2)
      congr 1
      funext i
      show (y i).2 + (z i).2 = (y i).2
      rw [h2 i, add_zero]
    · rw [htens]
      exact Submodule.subset_span ⟨h, g₀, hg₀, rfl⟩
  let xh : κ → AF F := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), (0 : FiniteAdeleRing (𝓞 F) F))
  let l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj xh
  have hxh : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (xh i).1) = x := by
    funext i
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (x i)
  have hg0 : g₀ (fun i => (xh i).2) = 1 := by
    have hm : (fun i => (xh i).2) ∈ GlobalTheory.SchANonzero.intPts F κ := fun i _ v => by
      show (0 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F
      exact zero_mem (v.adicCompletionIntegers F)
    simp only [g₀, Set.indicator_of_mem hm, Pi.one_apply]
  have hl : l ∈ (adeleClass F).adm κ := by
    intro g _
    refine ⟨g (fun i => (xh i).2) • ((BoundedContinuousFunction.evalCLM ℂ x).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun h => ?_⟩
    show pureA F (⇑h) g xh = _
    simp only [pureA, hxh, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      BoundedContinuousFunction.evalCLM_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply, smul_eq_mul]
    exact mul_comm _ _
  have hφ : pureA F (⇑f) g₀ ∈ (adeleClass F).sp κ := Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩
  have hc := hW.2.2 l hl _ hφ
  have key : (fun t : ℝ => T t f x) =
      (fun p => l (om p (pureA F (⇑f) g₀))) ∘ (fun t : ℝ => (γ (Multiplicative.ofAdd t), (1 : UA σ W.J))) := by
    funext t
    have e := hAct t f r₀ (hRest f)
    rw [htens, htens] at e
    simp only [Function.comp_apply]
    rw [e]
    show _ = pureA F _ g₀ xh
    simp only [pureA, hxh, hg0, mul_one]
  rw [key]
  exact hc.comp ((hγ.1.comp continuous_ofAdd).prodMk continuous_const)

end GlobalTheory.ArchLineContPairLeft
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousArchimedeanWeilOperatorLinePairXStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_archimedeanWeilOperator_line_pairX : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∀ (f : SInf F (Fin n × Fin d)) (x : (Fin n × Fin d → mixedEmbedding.mixedSpace F)), Continuous fun t => T t f x := by
  first | exact @GlobalTheory.ArchLineContPairLeft.continuous_apply | exact GlobalTheory.ArchLineContPairLeft.continuous_apply | (intros; apply GlobalTheory.ArchLineContPairLeft.continuous_apply <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstMemberLieAlgebraPreservesPolynomialFock
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix
open scoped Classical

noncomputable section

namespace GlobalTheory.RealLieFockX

theorem lineGroupX : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        (∀ (s t : ℝ) (f : SInf F (Fin n × Fin d)), T (s + t) f = T s (T t f)) ∧ ∀ f : SInf F (Fin n × Fin d), T 0 f = f := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om _ _ _ _ _ _ _ _ _ _ γ _ T hA
  obtain ⟨r₀, hR, hinj⟩ := GlobalTheory.ArchUniq.exists_admissible_finite_factor (F := F) (Fin n × Fin d)
  refine ⟨fun s t f => hinj _ _ ?_, fun f => hinj _ _ ?_⟩
  · rw [← hA (s + t) f r₀ (hR f), ← hA s (T t f) r₀ (hR _), ← hA t f r₀ (hR f), ofAdd_add, map_mul,
      show (γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd t), (1 : UA σ W.J)) =
        (γ (Multiplicative.ofAdd s), (1 : UA σ W.J)) * (γ (Multiplicative.ofAdd t), 1) by
          simp [Prod.mk_mul_mk], map_mul, Module.End.mul_apply]
  · rw [← hA 0 f r₀ (hR f), ofAdd_zero, map_one, Prod.mk_one_one, map_one, Module.End.one_apply]

theorem vacX : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∀ f₀, M.IsGauss ψ τ f₀ →
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f₀ p.2) ∧ ∃ f' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f₀ x) (f' x) 0 := by
  intro F E _ _ _ _ _ σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe τ hcX hcW γ hγ T hTa f₀ hf₀
  obtain ⟨h1, h0⟩ := lineGroupX F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe γ hγ T hTa
  have hU := GlobalTheory.T.weil_model_residue_character_pow F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe γ hγ T hTa MeasureTheory.Measure.addHaar inferInstance
  obtain ⟨A, hAc, hAadd, hA0, hAint⟩ := GlobalTheory.T.archimedean_weil_line_intertwines_heisenberg_left F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe γ hγ T hTa
  have hC := GlobalTheory.T.continuous_archimedeanWeilOperator_line_pairX F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe γ hγ T hTa
  obtain ⟨J₀, hJ, hvac⟩ := GlobalTheory.T.exists_complexStructure_gaussVacuum_isFockVacuum F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe τ hcX hcW f₀ hf₀
  haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  obtain ⟨hsm, k, qs, qs', cs, c, hd⟩ := GlobalTheory.T.weilOneParam_moves_fockVacuum_smoothly (V := Fin n × Fin d → mixedEmbedding.mixedSpace F)
    MeasureTheory.Measure.addHaar (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d))
    (GlobalTheory.GaussLine.pairInf_nondeg F _) T h1 h0 hU A hAc hAadd hA0 hAint hC J₀ hJ f₀ hvac
  refine ⟨hsm, ?_⟩
  have hf₀P : f₀ ∈ M.Pol ψ τ := Submodule.mem_sInf.2 fun N hN => hN.1 f₀ hf₀
  have hmul := GlobalTheory.T.polynomial_fock_space_stable_mul_trace_pairing F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWs hWd hrX hrW hhX hhW hwe τ hcX hcW
  choose m hmP hmE using hmul
  refine ⟨(∑ i, cs i • m (qs i) (m (qs' i) f₀ hf₀P) (hmP _ _ _)) + c • f₀,
    add_mem (sum_mem fun i _ => Submodule.smul_mem _ _ (hmP _ _ _)) (Submodule.smul_mem _ _ hf₀P), fun x => ?_⟩
  convert hd x using 1
  simp only [SchwartzMap.add_apply, SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul, hmE]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem heisX : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∀ u, At (evI F) u → ∀ f ∈ M.Pol ψ τ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f p.2) →
          (∃ f' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f x) (f' x) 0) →
          ∀ f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ →
            ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f₁ p.2) ∧ ∃ f₁' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f₁ x) (f₁' x) 0 := by
  intro F E _ _ _ _ _ σ _hCM n d X W M ψ χX χW om hψ _ _ _ _ _ _ _ _ hW τ _ _ γ hγ T hTa u hu f hf hsm hder f₁ hf₁
  obtain ⟨f', hf'P, hf'd⟩ := hder
  have hstab : ∀ v : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) v → ∀ g ∈ M.Pol ψ τ,
      ∃ g₁ ∈ M.Pol ψ τ, ∀ y, g₁ y = GlobalTheory.HeisOrbit.dOp (GlobalTheory.HeisOrbit.archCo M.co v).1 (GlobalTheory.HeisOrbit.archCo M.co v).2 g y := by
    intro v hv g hg
    obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin n) (Fin d) (Fin n × Fin d) ψ (incM F X.J) (incM F W.J)
      M.co hψ
    have h0 : ∀ t, M.heisLine ψ v t 0 = 0 := fun t => by
      funext x
      simp [Model.heisLine, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
    have hA : ActsD (evI F) (M.heisLine ψ v) g (D v g) :=
      (GlobalTheory.RealLift.actsLaws F _ g (D v g) (D v g)).1 _ h0 (hD v hv g).1
    refine ⟨D v g, Submodule.mem_sInf.2 fun N hN => hN.2 v hv g (Submodule.mem_sInf.1 hg N hN) _ hA, fun y => ?_⟩
    rw [(hD v hv g).2 y]
    rfl
  have hrel : ∀ t y, T t f₁ y = GlobalTheory.HeisOrbit.dOp (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)).1
      (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)).2 (T t f) y := fun t =>
    GlobalTheory.T.weil_operator_left_intertwines_heisenberg_derivative M ψ χX χW om hψ hW (γ (Multiplicative.ofAdd t)) (T t) (hTa t) u hu f f₁ hf₁
  obtain ⟨hφ, u', hu', hφd⟩ := GlobalTheory.T.archimedean_darboux_coords_one_param_orbit_smooth (W := W) M γ hγ u hu
  have hfun : (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f₁ p.2) =
      fun p => GlobalTheory.HeisOrbit.dOp (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd p.1)) * u)).1
        (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd p.1)) * u)).2 (T p.1 f) p.2 :=
    funext fun p => hrel p.1 p.2
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact GlobalTheory.HeisOrbit.dOp_contDiff_family (fun t => T t f) (fun t => (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)).1)
      (fun t => (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)).2) hsm hφ.fst hφ.snd
  have hT0 : T 0 f = f := by
    have h1 : om (γ (Multiplicative.ofAdd 0), 1) = 1 := by
      rw [ofAdd_zero, map_one]
      exact map_one om
    have hA : Acts (evI F) (om (γ (Multiplicative.ofAdd 0), 1)) f f := by
      rw [h1]
      intro r _
      rfl
    exact (GlobalTheory.RealLift.actsLaws F _ f (T 0 f) f).2.2.2.1 _ (hTa 0 f) hA
  have hφ0 : GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd (0 : ℝ))) * u) = GlobalTheory.HeisOrbit.archCo M.co u := by
    rw [ofAdd_zero, map_one]
    simp [mat]
  obtain ⟨g₁, hg₁P, hg₁⟩ := hstab u hu f' hf'P
  obtain ⟨g₂, hg₂P, hg₂⟩ := hstab u' hu' f hf
  refine ⟨g₁ + g₂, add_mem hg₁P hg₂P, fun x => ?_⟩
  have hP := (hasFDerivAt_fst (𝕜 := ℝ)).comp_hasDerivAt (0 : ℝ) hφd
  have hQ := (hasFDerivAt_snd (𝕜 := ℝ)).comp_hasDerivAt (0 : ℝ) hφd
  have h4 := GlobalTheory.HeisOrbit.DOpDeriv.dOp_hasDerivAt (fun t => T t f) (fun t => (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)).1)
    (fun t => (GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)).2) f' _ _ hsm hf'd hP hQ x
  simp only [hφ0, hT0] at h4
  rw [SchwartzMap.add_apply, hg₁, hg₂]
  exact h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hrel t x)

theorem lie_deriv_polX : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → GlobalTheory.LFun.IsHecke F E χX → GlobalTheory.LFun.IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w, (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, ∀ f ∈ M.Pol ψ τ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ M.Pol ψ τ := by
  intro F E _ _ _ _ _ σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hwe τ hcX hcW γ hγ
  have h1W : (1 : UA σ W.J) ∈ UAt σ W (evI F) := by
    intro u _
    have e : mat (1 : UA σ W.J) = 1 := rfl
    show u • (mat (1 : UA σ W.J) - 1) = 0
    rw [e, sub_self, smul_zero]
  choose T hT' using fun t : ℝ => GlobalTheory.FockCompactW.exists_op_of_UAt hψ hwe (γ (Multiplicative.ofAdd t), 1) (hγ.2 _) h1W
  have hvac : ∀ f₀, M.IsGauss ψ τ f₀ → f₀ ∈ M.Pol ψ τ := fun f₀ h =>
    Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h
  have hstab : ∀ u, At (evI F) u → ∀ f ∈ M.Pol ψ τ, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ u) f f₁ → f₁ ∈ M.Pol ψ τ := fun u hu f hf f₁ h =>
    Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h
  let N : Submodule ℂ (SInf F (Fin n × Fin d)) :=
    { carrier := {f | f ∈ M.Pol ψ τ ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f p.2) ∧
        ∃ f' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f x) (f' x) 0}
      zero_mem' := ⟨zero_mem _, by simpa using contDiff_const, 0, zero_mem _, fun x => by simpa using hasDerivAt_const _ _⟩
      add_mem' := by
        rintro f g ⟨hf, hf1, f', hf', hf2⟩ ⟨hg, hg1, g', hg', hg2⟩
        refine ⟨add_mem hf hg, by simpa using hf1.add hg1, f' + g', add_mem hf' hg', fun x => ?_⟩
        show HasDerivAt (fun t => T t (f + g) x) ((f' + g') x) 0
        simp only [map_add (f := _), SchwartzMap.add_apply]
        exact (hf2 x).add (hg2 x)
      smul_mem' := by
        rintro c f ⟨hf, hf1, f', hf', hf2⟩
        refine ⟨Submodule.smul_mem _ c hf, by simpa using hf1.const_smul c, c • f', Submodule.smul_mem _ c hf', fun x => ?_⟩
        simpa using (hf2 x).const_mul c }
  have hPN : M.Pol ψ τ ≤ N := by
    refine sInf_le ⟨fun f₀ h => ?_, fun u hu f hf f₁ h => ?_⟩
    · exact ⟨hvac f₀ h, vacX F E σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hwe τ hcX hcW γ hγ T hT' f₀ h⟩
    · obtain ⟨hf0, hf1, hf2⟩ := hf
      exact ⟨hstab u hu f hf0 f₁ h,
        heisX F E σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hwe τ hcX hcW γ hγ T hT' u hu f hf0 hf1 hf2 f₁ h⟩
  intro f hf f₁ h₁
  obtain ⟨-, -, f', hf', hd⟩ := hPN hf
  have hA : ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f' := by
    intro r hr x
    have h1 : ∀ t : ℝ, om (γ (Multiplicative.ofAdd t), 1) (tens (evI F) f r) = tens (evI F) (T t f) r :=
      fun t => hT' t f r hr
    simp only [h1]
    exact (hd _).mul_const (r x)
  have e : f₁ = f' := (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f f₁ f').2.2.1 _ h₁ hA
  rw [e]; exact hf'

end GlobalTheory.RealLieFockX

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstMemberLieAlgebraPreservesPolynomialFockStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstMember_lieAlgebra_preserves_polynomialFock : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → GlobalTheory.LFun.IsHecke F E χX → GlobalTheory.LFun.IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w, (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, ∀ f ∈ M.Pol ψ τ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ M.Pol ψ τ := by
  first | exact @GlobalTheory.RealLieFockX.lie_deriv_polX | exact GlobalTheory.RealLieFockX.lie_deriv_polX | (intros; apply GlobalTheory.RealLieFockX.lie_deriv_polX <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

noncomputable section

namespace GlobalTheory.HoweGlobalPair

theorem decomp {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] {ι : Type} [Fintype ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (t : M₀ ⊗[ℂ] (⨂[ℂ] i, M i)) :
    ∃ (m : ℕ) (f : Fin m → M₀) (φ : Fin m → ∀ i, M i), t = ∑ j, f j ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (φ j) := by
  classical

  have join : ∀ t₁ t₂ : M₀ ⊗[ℂ] (⨂[ℂ] i, M i),
      (∃ (m : ℕ) (f : Fin m → M₀) (φ : Fin m → ∀ i, M i), t₁ = ∑ j, f j ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (φ j)) →
      (∃ (m : ℕ) (f : Fin m → M₀) (φ : Fin m → ∀ i, M i), t₂ = ∑ j, f j ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (φ j)) →
      ∃ (m : ℕ) (f : Fin m → M₀) (φ : Fin m → ∀ i, M i), t₁ + t₂ = ∑ j, f j ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (φ j) := by
    rintro t₁ t₂ ⟨m₁, f₁, φ₁, rfl⟩ ⟨m₂, f₂, φ₂, rfl⟩
    refine ⟨m₁ + m₂, Fin.append f₁ f₂, Fin.append φ₁ φ₂, ?_⟩
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul x y =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r g =>
      refine ⟨1, fun _ => r • x, fun _ => g, ?_⟩
      rw [Fin.sum_univ_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    | add y₁ y₂ h₁ h₂ =>
      rw [TensorProduct.tmul_add]
      exact join _ _ h₁ h₂
  | add t₁ t₂ h₁ h₂ => exact join _ _ h₁ h₂

theorem det_ne_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h

  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let B : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have key : Bᵀ * M * B.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [B, Matrix.mul_apply]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul] at hdet
  intro h0
  rw [h0, mul_zero, zero_mul, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one] at hdet
  exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero) hdet.symm

theorem det_ne_sig_map {E : Type} [Field E] {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (τ : E →+* ℂ) (c : ℂ)
    (h : HasSig (c • J.map τ) r s) : J.det ≠ 0 := by
  intro h0
  apply det_ne_hasSig h
  have hmap : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
  rw [Matrix.det_smul, hmap, h0, map_zero, mul_zero]

theorem hecke_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') := by
  refine ⟨?_, fun x => ?_⟩
  · have hc : Continuous fun z => χ z / χ' z := h.1.div' h'.1
    exact hc
  · rw [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

theorem resEta_div {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) (hk : k = n + m) :
    ResEtaPow K (χ / χ') k := by
  subst hk
  intro x
  rw [MonoidHom.div_apply, Circle.coe_div, h x, h' x]
  split_ifs
  · exact div_one 1
  · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg, inv_one]

end GlobalTheory.HoweGlobalPair

end
