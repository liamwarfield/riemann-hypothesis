module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralElementCharPolyNonsplit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjThetaKOMulIntegrableOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdParEqFlag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolSub0LeSpanRaw
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaHeisenbergCommutingThetaOperator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaHeisenbergCommutingThetaOperator
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

namespace GlobalTheory.ThetaSchurF

section Lemmas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
  {ψ : AddChar (AF F) ℂ}

theorem half_add_half (x y : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ x y + symplOHF σ JS JT ξ₀ x y = symplOF σ JS JT ξ₀ x y := by
  simp only [symplOHF, ← add_mul, ← map_add (f := _)]
  norm_num

theorem symplOF_add_left (x x' y : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ (x + x') y = symplOF σ JS JT ξ₀ x y + symplOF σ JS JT ξ₀ x' y := by
  simp only [symplOF, hOF, Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem symplOF_add_right (x y y' : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ x (y + y') = symplOF σ JS JT ξ₀ x y + symplOF σ JS JT ξ₀ x y' := by
  simp only [symplOF, hOF, Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem symplOF_zero_right (x : WOF F E nS nT) : symplOF σ JS JT ξ₀ x 0 = 0 := by
  simp [symplOF, hOF]

theorem continuous_symplOF_left (y : WOF F E nS nT) : Continuous fun x => symplOF σ JS JT ξ₀ x y := by
  have h := GlobalTheory.HeisThetaF.continuous_symplOHF_left (σ := σ) (JS := JS) (JT := JT) (xi0 := ξ₀) y
  have e : (fun x => symplOF σ JS JT ξ₀ x y) = fun x => symplOHF σ JS JT ξ₀ x y + symplOHF σ JS JT ξ₀ x y :=
    funext fun x => (half_add_half x y).symm
  rw [e]
  exact h.add h

theorem mul_star_psi (hψ : ∀ a, ‖ψ a‖ = 1) (a : AF F) : ψ a * star (ψ a) = 1 := by
  rw [Complex.star_def, Complex.mul_conj', hψ a]
  simp

theorem heis_rat (hskew : ∀ x y : WOF F E nS nT, symplOF σ JS JT ξ₀ y x = -symplOF σ JS JT ξ₀ x y)
    {f : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT ξ₀ ψ f) {γ : WOF F E nS nT} (hγ : γ ∈ ratLF F E nS nT)
    (x : WOF F E nS nT) : heisOF σ JS JT ξ₀ ψ γ f x = ψ (symplOF σ JS JT ξ₀ x γ) * f x := by
  obtain ⟨γ, rfl⟩ := hγ
  have hs : symplOHF σ JS JT ξ₀ (ratWF γ) x = -symplOHF σ JS JT ξ₀ x (ratWF γ) := by
    simp only [symplOHF]
    rw [hskew, mul_neg]
  show ψ (symplOHF σ JS JT ξ₀ x (ratWF γ)) * f (x + ratWF γ) = ψ (symplOF σ JS JT ξ₀ x (ratWF γ)) * f x
  rw [add_comm x, hf.quasi, hs, neg_neg, ← mul_assoc, ← AddChar.map_add_eq_mul, half_add_half]

theorem prod_periodic (hψ : ∀ a, ‖ψ a‖ = 1) {f f' : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT ξ₀ ψ f)
    (hf' : IsThetaFunOF σ JS JT ξ₀ ψ f') {γ : WOF F E nS nT} (hγ : γ ∈ ratLF F E nS nT) (x : WOF F E nS nT) :
    f (γ + x) * star (f' (γ + x)) = f x * star (f' x) := by
  obtain ⟨γ, rfl⟩ := hγ
  show f (ratWF γ + x) * star (f' (ratWF γ + x)) = _
  rw [hf.quasi, hf'.quasi, star_mul']
  linear_combination (f x * star (f' x)) * mul_star_psi hψ (-(symplOHF σ JS JT ξ₀ (ratWF γ) x))

theorem scalar_eq (hψ : ∀ a, ‖ψ a‖ = 1) (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT))
    (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ)
    (M : Module.End ℂ (WOF F E nS nT → ℂ))
    (hM : ∀ f, IsThetaFunOF σ JS JT ξ₀ ψ f → IsThetaFunOF σ JS JT ξ₀ ψ (M f))
    (hn : ∀ f, IsThetaFunOF σ JS JT ξ₀ ψ f → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ)
    (f f' : WOF F E nS nT → ℂ) (hf : IsThetaFunOF σ JS JT ξ₀ ψ f) (hf' : IsThetaFunOF σ JS JT ξ₀ ψ f') :
    ∫ x in 𝓕, M f x * star (M f' x) ∂μ = ∫ x in 𝓕, f x * star (f' x) ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc μ h𝓕⟩
  have hb : ∀ (g : WOF F E nS nT → ℂ), g ∈ GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ → ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C :=
    fun g (hg : IsThetaFunOF σ JS JT ξ₀ ψ g) => by
      have hp : ∀ γ ∈ ratLF F E nS nT, ∀ w, ‖g (γ + w)‖ = ‖g w‖ := by
        rintro _ ⟨γ, rfl⟩ w
        exact (congrArg norm (hg.quasi γ w)).trans (by rw [norm_mul, hψ, one_mul])
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.cont.continuousOn
      refine ⟨C, fun w => ?_⟩
      obtain ⟨γ, hγ, h⟩ := hKc w
      rw [← hp γ hγ w]
      exact hC _ h
  exact GlobalTheory.Mem.LiftPolar.integral_mul_star_eq (μ.restrict 𝓕) (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ)
    (fun g (hg : IsThetaFunOF σ JS JT ξ₀ ψ g) => hg.cont.measurable) hb M hM hn f f' hf hf'

theorem prod_eq (hψ : IsCharAF F ψ)
    (hskew : ∀ x y : WOF F E nS nT, symplOF σ JS JT ξ₀ y x = -symplOF σ JS JT ξ₀ x y)
    (hann : ∀ x : WOF F E nS nT, (∀ γ ∈ ratLF F E nS nT, ψ (symplOF σ JS JT ξ₀ x γ) = 1) ↔ x ∈ ratLF F E nS nT)
    (hth : ∀ w f, IsThetaFunOF σ JS JT ξ₀ ψ f → IsThetaFunOF σ JS JT ξ₀ ψ (heisOF σ JS JT ξ₀ ψ w f))
    (M : Module.End ℂ (WOF F E nS nT → ℂ))
    (hM : ∀ f, IsThetaFunOF σ JS JT ξ₀ ψ f → IsThetaFunOF σ JS JT ξ₀ ψ (M f))
    (hc : ∀ w f, IsThetaFunOF σ JS JT ξ₀ ψ f → M (heisOF σ JS JT ξ₀ ψ w f) = heisOF σ JS JT ξ₀ ψ w (M f))
    (hn : ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ f, IsThetaFunOF σ JS JT ξ₀ ψ f →
        ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ)
    {f f' : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT ξ₀ ψ f) (hf' : IsThetaFunOF σ JS JT ξ₀ ψ f')
    (x : WOF F E nS nT) : M f x * star (M f' x) = f x * star (f' x) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨μ, 𝓕, hμ, h𝓕, -⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WOF F E nS nT) (ratLF F E nS nT) K hK hKc).1
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc μ h𝓕⟩
  have hint : ∀ g g', IsThetaFunOF σ JS JT ξ₀ ψ g → IsThetaFunOF σ JS JT ξ₀ ψ g' →
      Integrable (fun x => g x * star (g' x)) (μ.restrict 𝓕) := fun g g' hg hg' => by
    have hcont : Continuous fun x => g x * star (g' x) := hg.cont.mul hg'.cont.star
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    refine Integrable.of_bound hcont.aestronglyMeasurable C (Filter.Eventually.of_forall fun w => ?_)
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← prod_periodic hψ.2.1 hg hg' hγ w]
    exact hC _ h
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (WOF F E nS nT) (ratLF F E nS nT) K hK hKc
    (ratLF F E nS nT) (fun γ x => ψ (symplOF σ JS JT ξ₀ x γ))
    (fun γ => hψ.1.comp (continuous_symplOF_left _))
    (fun γ x y => by simp only [symplOF_add_left, AddChar.map_add_eq_mul])
    (fun γ γ' x => by simp only [AddSubgroup.coe_add, symplOF_add_right, AddChar.map_add_eq_mul])
    (fun x => by simp only [AddSubgroup.coe_zero, symplOF_zero_right, AddChar.map_zero_eq_one])
    (fun γ x => hψ.2.1 _)
    (fun x => by
      rw [← hann x]
      exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)
    μ 𝓕 hμ h𝓕 (fun x => M f x * star (M f' x) - f x * star (f' x))
    (((hM f hf).cont.mul (hM f' hf').cont.star).sub (hf.cont.mul hf'.cont.star))
    (fun γ hγ x => by
      rw [prod_periodic hψ.2.1 hf hf' hγ, prod_periodic hψ.2.1 (hM f hf) (hM f' hf') hγ])
    (fun γ => by
      have e : (fun x => ψ (symplOF σ JS JT ξ₀ x γ) * (M f x * star (M f' x) - f x * star (f' x))) = fun x =>
          M (heisOF σ JS JT ξ₀ ψ γ f) x * star (M f' x) - heisOF σ JS JT ξ₀ ψ γ f x * star (f' x) := by
        funext x
        rw [hc _ f hf, heis_rat hskew hf γ.2, heis_rat hskew (hM f hf) γ.2]
        ring
      rw [e, integral_sub (hint _ _ (hM _ (hth _ f hf)) (hM f' hf')) (hint _ _ (hth _ f hf) hf'),
        scalar_eq hψ.2.1 μ 𝓕 hμ h𝓕 M hM (hn μ 𝓕 hμ h𝓕) _ _ (hth _ f hf) hf', sub_self])
  exact sub_eq_zero.1 (congrFun key x)

end Lemmas

theorem schur : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ M : Module.End ℂ (WOF F E nS nT → ℂ),
      (∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ (M f)) →
      (∀ w f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M (heisOF σ JS JT ξ₀ B.ψ w f) = heisOF σ JS JT ξ₀ B.ψ w (M f)) →
      (∀ (μ : MeasureTheory.Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
        MeasureTheory.IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
          ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) →
      ∃ c : ℂ, ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M f = c • f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ M hM hc hn
  have hψ : IsCharAF F B.ψ := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB).1
  have hinv : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
  have hskew := GlobalTheory.T.adelicSymplecticTraceForm_alternating_swap F E σ hinv nS nT JS JT hJS hJT ξ₀ hσξ
  have hann := GlobalTheory.T.rational_points_self_annihilator_symplectic_standardChar F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ
  have hth : ∀ w f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ (heisOF σ JS JT ξ₀ B.ψ w f) :=
    fun w f hf => GlobalTheory.HeisThetaF.isThetaFunOF_heisOF F E σ B hB nS nT JS JT ξ₀ w f hf
  have h2 : ∀ f f', IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ f' → ∀ x y,
      M f x * star (M f' y) = f x * star (f' y) := fun f f' hf hf' x y => by
    have h := prod_eq hψ hskew hann hth M hM hc hn hf (hth (y - x) f' hf') x
    rw [hc _ _ hf'] at h
    simp only [heisOF, add_sub_cancel, star_mul'] at h
    linear_combination B.ψ (symplOHF σ JS JT ξ₀ x (y - x)) * h -
      (M f x * star (M f' y) - f x * star (f' y)) * mul_star_psi hψ.2.1 (symplOHF σ JS JT ξ₀ x (y - x))
  by_cases h0 : ∃ f₀ y, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ ∧ f₀ y ≠ 0
  · obtain ⟨f₀, y, hf₀, hy⟩ := h0
    have h1 := h2 f₀ f₀ hf₀ hf₀ y y
    have hn1 : ‖M f₀ y‖ = ‖f₀ y‖ := by
      have := congrArg norm h1
      rw [norm_mul, norm_mul, norm_star, norm_star] at this
      exact (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).1 this
    have hy' : M f₀ y ≠ 0 := by
      rw [← norm_ne_zero_iff, hn1]
      exact norm_ne_zero_iff.2 hy
    have hs : star (M f₀ y) ≠ 0 := star_ne_zero.2 hy'
    refine ⟨star (f₀ y) / star (M f₀ y), fun f hf => ?_⟩
    funext x
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hs, h2 f f₀ hf hf₀, mul_comm]
  · refine ⟨1, fun f hf => ?_⟩
    have : f = 0 := funext fun y => by
      by_contra hy
      exact h0 ⟨f, y, hf, hy⟩
    rw [this, map_zero, smul_zero]

end GlobalTheory.ThetaSchurF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaHeisenbergCommutingThetaOperatorStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_lemma_heisenberg_commuting_thetaOperator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ M : Module.End ℂ (WOF F E nS nT → ℂ),
      (∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ (M f)) →
      (∀ w f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M (heisOF σ JS JT ξ₀ B.ψ w f) = heisOF σ JS JT ξ₀ B.ψ w (M f)) →
      (∀ (μ : MeasureTheory.Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
        MeasureTheory.IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
          ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) →
      ∃ c : ℂ, ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M f = c • f := by
  first | exact @GlobalTheory.ThetaSchurF.schur | exact GlobalTheory.ThetaSchurF.schur | (intros; apply GlobalTheory.ThetaSchurF.schur <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWLink

variable {D : D7} {m n : ℕ}

abbrev cAl (D : D7) : AE D →ₐ[AF D.host.F] AE D := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig

abbrev UD (D : D7) {k : ℕ} (J : Matrix (Fin k) (Fin k) D.host.E) : Type := UA D.sp.cm.sig J

theorem cAl_eq (z : AE D) : cAl D z = cA D z := GlobalTheory.IwLine.cA_eq_sigR _ z

variable {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E} {T : GL (Fin (n + n)) D.host.E} {κ : UD D J₂ ≃* StdUnn.G D n}

section Witt

variable {J : Matrix (Fin n) (Fin n) D.host.E}

theorem trA_cA (z : AE D) : StdUnn.trA (cA D z) = StdUnn.trA z := by
  let e : AE D ≃ₐ[AF D.host.F] AE D := AlgEquiv.ofAlgHom (cAl D) (cAl D)
    (AlgHom.ext fun z => by simp only [AlgHom.comp_apply, cAl_eq, cA_cA, AlgHom.id_apply])
    (AlgHom.ext fun z => by simp only [AlgHom.comp_apply, cAl_eq, cA_cA, AlgHom.id_apply])
  rw [← cAl_eq]
  exact Algebra.trace_eq_of_algEquiv e z

theorem trA_inner_comm (V : HSp D) (x y : Mx D V.rank n) :
    StdUnn.trA (Matrix.trace (StdUnn.inner V x y)) = StdUnn.trA (Matrix.trace (StdUnn.inner V y x)) := by
  rw [← trA_cA, ← trace_adj, StdUnn.inner, StdUnn.inner, adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]

end Witt

end GlobalTheory.SWLink

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameOnBaseCharacter
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MuLift

section Ring

end Ring

section General

open NumberField Formalism.L2.DIV
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end General

section Adelic

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
open Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj GlobalTheory.StepLaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_idemSum (P : Finset (Pl D.host.E))
    (h : ∀ Q ∈ P, ∀ Q' ∈ P, ¬ Formalism.IndefR.Lev.IsConjPl Q Q') :
    ∃ e : AE D, IsIdemSum e P :=
  GlobalTheory.GridIdem.exists_isIdemSum P (fun Q hQ => GlobalTheory.ParahoricLift.exists_isIdemAt (h Q hQ Q hQ))
    fun Q hQ Q' hQ' e => (GlobalTheory.IdemSupport.eq_or_eq_cP e).resolve_right fun e' =>
      h Q' hQ' Q hQ ((GlobalTheory.IdemSupport.isConjPl_iff Q' Q).2 e')


end Adelic

open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar


end GlobalTheory.MuLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOpDoubledGramDoublingThetaTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOpDoubledGramDoublingThetaTensor
open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace GlobalTheory.DblHeis
open Formalism.IndefR.DatumF GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sum_fin_add_add {M : Type} [AddCommMonoid M] {n : ℕ} (f : Fin (n + n) → M) :
    ∑ d, f d = ∑ d, f (finSumFinEquiv (Sum.inl d)) + ∑ d, f (finSumFinEquiv (Sum.inr d)) := by
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]

theorem hOF_dblG (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (x y : WOF F E nS (nT + nT)) :
    hOF σ JS (dblG JT) x y = hOF σ JS JT (topR x) (topR y) - hOF σ JS JT (botR x) (botR y) := by
  simp only [hOF, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [sum_fin_add_add (n := nT), dblG, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, dbl,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.neg_apply, map_zero, map_neg, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    mul_neg, neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg, topR, botR, Function.comp_apply, id, Finset.sum_sub_distrib]
  ring

theorem hOF_neg_neg (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (x y : WOF F E nS nT) : hOF σ JS JT (-x) (-y) = hOF σ JS JT x y := by
  simp only [hOF, Matrix.neg_apply, map_neg, mul_neg, neg_mul, neg_neg]

theorem symplOHF_dblG (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (ξ₀ : E) (x y : WOF F E nS (nT + nT)) :
    symplOHF σ JS (dblG JT) ξ₀ x y =
      symplOHF σ JS JT ξ₀ (topR x) (topR y) - symplOHF σ JS JT ξ₀ (-botR x) (-botR y) := by
  simp only [symplOHF, symplOF, hOF_dblG, hOF_neg_neg, mul_sub, map_sub]

theorem conj_psi {ψ : AddChar (AF F) ℂ} (h : ∀ x, ‖ψ x‖ = 1) (s : AF F) : conj (ψ s) = ψ (-s) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, h s]
  simp

theorem heisOF_dblG_deltaT : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (w : Formalism.IndefR.DatumF.WOF F E nS (nT + nT)) (f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ w (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) =
          GlobalTheory.DblTargetDelta.deltaT (Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (GlobalTheory.DblTargetDelta.topR w) f₁)
            (Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (-GlobalTheory.DblTargetDelta.botR w) f₂) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ w f₁ f₂
  have hn : ∀ x, ‖B.ψ x‖ = 1 := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB).1.2.1
  funext x
  have ht : topR (x + w) = topR x + topR w := rfl
  have hb : -botR (x + w) = -botR x + -botR w := by
    rw [← neg_add]; rfl
  simp only [heisOF, deltaT_apply, ht, hb, symplOHF_dblG, map_mul, conj_psi hn, sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring

end GlobalTheory.DblHeis

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOpDoubledGramDoublingThetaTensorStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOp_doubledGram_doublingThetaTensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (w : Formalism.IndefR.DatumF.WOF F E nS (nT + nT)) (f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ w (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) =
          GlobalTheory.DblTargetDelta.deltaT (Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (GlobalTheory.DblTargetDelta.topR w) f₁)
            (Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (-GlobalTheory.DblTargetDelta.botR w) f₂) := by
  first | exact @GlobalTheory.DblHeis.heisOF_dblG_deltaT | exact GlobalTheory.DblHeis.heisOF_dblG_deltaT | (intros; apply GlobalTheory.DblHeis.heisOF_dblG_deltaT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnipotentRadicalEqLeviMulUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnipotentRadicalEqLeviMulUnipotent
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.RatLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}


omit [NumberField E] in
theorem col_coeff {X : Matrix (Fin n) (Fin r) E} {T : Finset (Fin r)} {g : GAd σ J}
    (hg : g ∈ GlobalTheory.StdPar.unip σ J X T) (j : Fin r) :
    ∃ c : Fin r → AF F ⊗[F] E, (∀ i, j ≤ i → c i = 0) ∧
      (matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ j = (adMat F X)ᵀ j + adMat F X *ᵥ c := by
  have h := (Subgroup.mem_iInf.1 hg.1 j).2 _ (Submodule.subset_span ⟨j, rfl, rfl⟩)
  obtain ⟨l, hl, e⟩ := (Finsupp.mem_span_image_iff_linearCombination _).1 h
  refine ⟨l, fun i hi => ?_, ?_⟩
  · by_contra hne
    obtain ⟨k, -, hik, hkj⟩ := hl (Finsupp.mem_support_iff.2 hne)
    exact absurd (hik.trans_lt hkj) (not_lt.2 hi)
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype l (fun i a => a • (adMat F X)ᵀ i) (fun i => zero_smul _ _)] at e
    beta_reduce at e
    have e2 : adMat F X *ᵥ ⇑l = ∑ i, l i • (adMat F X)ᵀ i := by
      rw [Matrix.mulVec_eq_sum]; simp only [op_smul_eq_smul]
    rw [e2, e, add_sub_cancel]


omit [NumberField E] in
theorem par_of_unip {X : Matrix (Fin n) (Fin r) E} {T : Finset (Fin r)} {s : ℕ} (hs : s ≤ r) {d : Fin s → ℕ}
    (hd : Monotone d) {g : GAd σ J} (hg : g ∈ GlobalTheory.StdPar.unip σ J X T) :
    ∃ B : Matrix (Fin s) (Fin s) (AF F ⊗[F] E), B.BlockTriangular d ∧
      (matHom _ σ J g).1 * adMat F (X.submatrix id (Fin.castLE hs)) = adMat F (X.submatrix id (Fin.castLE hs)) * B := by
  choose c hc hce using col_coeff hg
  refine ⟨1 + Matrix.of fun i j => c (Fin.castLE hs j) (Fin.castLE hs i), fun i j hlt => ?_, ?_⟩
  · have hji : j < i := not_le.1 fun h => absurd hlt (not_lt.2 (hd h))
    have hle : Fin.castLE hs j ≤ Fin.castLE hs i := by
      rw [Fin.le_def]; simp only [Fin.coe_castLE]; exact hji.le
    simp [Matrix.one_apply_ne hji.ne', hc _ _ hle]
  · ext k j
    have h1 := congrFun (hce (Fin.castLE hs j)) k
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.add_apply] at h1
    rw [Matrix.mul_apply, Matrix.mul_add, Matrix.add_apply, Matrix.mul_one, Matrix.mul_apply]
    simp only [Matrix.map_apply, Matrix.submatrix_apply, id, Matrix.of_apply] at h1 ⊢
    rw [h1]
    congr 1
    symm
    refine Fintype.sum_of_injective (Fin.castLE hs) (Fin.castLE_injective hs) _ _ (fun i hi => ?_) (fun i => rfl)
    have : s ≤ i.val := by
      by_contra hlt
      exact hi ⟨⟨i.val, by omega⟩, rfl⟩
    rw [hc _ _ (by rw [Fin.le_def]; simp only [Fin.coe_castLE]; omega), mul_zero]

end GlobalTheory.RatLevi

theorem GlobalTheory.RatLevi.rat_unip_eq_levi_mul_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ S T : Finset (Fin r), S ⊆ T → ∀ γ ∈ ratPts σ J, γ ∈ GlobalTheory.StdPar.unip σ J X T →
        ∃ m ∈ ratPts σ J, m ∈ GlobalTheory.StdPar.levi σ J X Y S ∧ ∃ ν ∈ GlobalTheory.StdPar.unip σ J X S, γ = m * ν := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S T _ γ hγ hγT
  obtain ⟨s, hsdef⟩ : ∃ s, s = S.sup fun k => k.val + 1 := ⟨_, rfl⟩
  have hs : s ≤ r := hsdef ▸ Finset.sup_le fun k _ => k.2
  have hS : ∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k := fun i => by
    rw [hsdef, Finset.lt_sup_iff]
    exact exists_congr fun k => and_congr_right fun _ => by rw [Fin.le_def]; omega
  obtain ⟨d, hddef⟩ : ∃ d : Fin s → ℕ, ∀ i, d i = (S.filter (· < Fin.castLE hs i)).card := ⟨fun i => (S.filter (· < Fin.castLE hs i)).card, fun _ => rfl⟩
  have hdm : Monotone d := fun i j hij => by
    rw [hddef, hddef]
    refine Finset.card_le_card fun k hk => ?_
    simp only [Finset.mem_filter] at hk ⊢
    refine ⟨hk.1, lt_of_lt_of_le hk.2 ?_⟩
    rw [Fin.le_def]; simp only [Fin.coe_castLE]; exact hij
  obtain ⟨hu, hl, -⟩ := GlobalTheory.TieStd.stdPar_eq_flag F E σ h n J hJ r X Y hW S s hs hS d hddef
  have hp : γ⁻¹ ∈ parFlag σ J (X.submatrix id (Fin.castLE hs)) d :=
    ⟨GlobalTheory.RatLevi.par_of_unip hs hdm (inv_mem hγT), by rw [inv_inv]; exact GlobalTheory.RatLevi.par_of_unip hs hdm hγT⟩
  obtain ⟨u, huF, m, hmF, hpm, hr⟩ := (GlobalTheory.T.leviDecomposition_gradedIsotropicFlag F E σ h n J hJ s (X.submatrix id (Fin.castLE hs))
    (Y.submatrix id (Fin.castLE hs)) d
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xx]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.yy]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xy]; exact Matrix.submatrix_one _ (Fin.castLE_injective hs))).1 _ hp
  refine ⟨m⁻¹, inv_mem (hr (inv_mem hγ)), by rw [hl]; exact inv_mem hmF, u⁻¹, by rw [hu]; exact inv_mem huF, ?_⟩
  rw [← inv_inv γ, hpm, mul_inv_rev]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnipotentRadicalEqLeviMulUnipotentStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_unipotentRadical_eq_levi_mul_unipotent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ S T : Finset (Fin r), S ⊆ T → ∀ γ ∈ ratPts σ J, γ ∈ GlobalTheory.StdPar.unip σ J X T →
        ∃ m ∈ ratPts σ J, m ∈ GlobalTheory.StdPar.levi σ J X Y S ∧ ∃ ν ∈ GlobalTheory.StdPar.unip σ J X S, γ = m * ν := by
  first | exact @GlobalTheory.RatLevi.rat_unip_eq_levi_mul_unip | exact GlobalTheory.RatLevi.rat_unip_eq_levi_mul_unip | (intros; apply GlobalTheory.RatLevi.rat_unip_eq_levi_mul_unip <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstAlongCocompactUniqueStages
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open GlobalTheory.Cusp (Cocompact constTermOn)
open GlobalTheory.AutomorphicL2Unitary (LeftInv)

namespace GlobalTheory.StdPar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem ratPts_inf_subgroupOf {N P : Subgroup (GAd σ J)} (hNP : N ≤ P) :
    (ratPts σ J ⊓ P).subgroupOf N = (ratPts σ J).subgroupOf N := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, hNP x.2⟩⟩

theorem isConstTermOn_iff_ratPts_inf {N P : Subgroup (GAd σ J)} [LocallyCompactSpace N] (hNP : N ≤ P)
    (hc : Cocompact (ratPts σ J) N) {φ c : GAd σ J → ℂ} (hφ : LeftInv (ratPts σ J ⊓ P) φ) :
    IsConstTermOn σ J N φ c ↔ c = constTermOn (ratPts σ J ⊓ P) N φ := by
  have e := ratPts_inf_subgroupOf (σ := σ) (J := J) hNP
  constructor
  · intro h
    obtain ⟨μ, 𝓕, h1, h2, h3⟩ := exists_mass_one hc
    funext g
    rw [h μ 𝓕 h1 h2 h3 g, GlobalTheory.Cusp.constTermOn_eq_of_measure_eq_one (e ▸ h2) h3 hφ g]
  · rintro rfl μ 𝓕 h1 h2 h3 g
    exact GlobalTheory.Cusp.constTermOn_eq_of_measure_eq_one (e ▸ h2) h3 hφ g

theorem cocompact_ratPts_inf {N P : Subgroup (GAd σ J)} (hNP : N ≤ P) (hc : Cocompact (ratPts σ J) N) :
    Cocompact (ratPts σ J ⊓ P) N := by
  unfold Cocompact
  rw [ratPts_inf_subgroupOf hNP]
  exact hc

section Witt

variable (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
include h hJ hW

theorem locallyCompact_unip (S : Finset (Fin r)) : LocallyCompactSpace (unip σ J X S) :=
  (isClosed_unip S h hJ hW).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem cocompact_unip_std (S : Finset (Fin r)) : Cocompact (ratPts σ J) (unip σ J X S) := by
  by_cases hS0 : S = ∅
  · subst hS0
    refine ⟨{1}, isCompact_singleton, fun u => ⟨u⁻¹, ?_, by simp⟩⟩
    have hu : (u : GAd σ J) = 1 := Subgroup.mem_bot.1 (le_of_eq (unip_empty (σ := σ) (J := J) (X := X)) u.2)
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_inv, hu, inv_one]
    exact one_mem _
  obtain ⟨m, hm, hm'⟩ : ∃ m ∈ S, ∀ k ∈ S, k ≤ m := ⟨S.max' (Finset.nonempty_iff_ne_empty.2 hS0),
    S.max'_mem _, fun k hk => S.le_max' k hk⟩
  rw [GlobalTheory.ConstTrans.unip_eq_unipFlag F E σ h n J hJ r X Y hW S m hm hm']
  exact cocompact_unipFlag hJ (sigma_sigma h) (isIsoCols_of_isWittFrame hW (sigma_sigma h) hJ m.2) _

theorem conj_mem_unip_of_subset {S T : Finset (Fin r)} (hTS : T ⊆ S) {p u : GAd σ J} (hp : p ∈ unip σ J X S)
    (hu : u ∈ unip σ J X T) : p * u * p⁻¹ ∈ unip σ J X T := by
  by_cases hT0 : T = ∅
  · subst hT0
    rw [unip_empty, Subgroup.mem_bot] at hu ⊢
    simp [hu]
  obtain ⟨m, hm, hm'⟩ : ∃ m ∈ T, ∀ k ∈ T, k ≤ m := ⟨T.max' (Finset.nonempty_iff_ne_empty.2 hT0),
    T.max'_mem _, fun k hk => T.le_max' k hk⟩
  have hσ := sigma_sigma h
  have eT := GlobalTheory.ConstTrans.unip_eq_unipFlag F E σ h n J hJ r X Y hW T m hm hm'
  rw [eT] at hu ⊢
  exact conj_mem_unipFlag hJ hσ (isIsoCols_of_isWittFrame hW hσ hJ m.2) _
    (GlobalTheory.ConstTrans.unip_le_parFlag F E σ h n J hJ r X Y hW S T m hTS hm hm' hp) hu

theorem constAlong_cocompact_unique_stages :
    (∀ S : Finset (Fin r), Cocompact (ratPts σ J) (unip σ J X S) ∧
      ∃ (μ : Measure (unip σ J X S)) (𝓕 : Set (unip σ J X S)), μ.IsHaarMeasure ∧
        IsFundamentalDomain ((ratPts σ J).subgroupOf (unip σ J X S)) 𝓕 μ ∧ μ 𝓕 = 1) ∧
    (∀ S T : Finset (Fin r), T ⊆ S → unip σ J X T ≤ unip σ J X S ∧ levi σ J X Y S ≤ levi σ J X Y T) ∧
    (∀ (S : Finset (Fin r)) (φ c c' : GAd σ J → ℂ), IsConstAlong σ J X S φ c → IsConstAlong σ J X S φ c' → c = c') ∧
    (∀ (S : Finset (Fin r)) (φ : GAd σ J → ℂ), (∀ γ ∈ ratPts σ J, γ ∈ unip σ J X S → ∀ g, φ (γ * g) = φ g) →
      ∃ c, IsConstAlong σ J X S φ c) ∧
    (∀ (S T : Finset (Fin r)) (φ c c' : GAd σ J → ℂ), T ⊆ S → Continuous φ →
      (∀ γ ∈ ratPts σ J, γ ∈ unip σ J X S → ∀ g, φ (γ * g) = φ g) →
      IsConstAlong σ J X T φ c → IsConstAlong σ J X S c c' → IsConstAlong σ J X S φ c') := by
  refine ⟨fun S => ?_, fun S T hTS => ⟨unip_mono_of_subset F E σ h n J hJ r X Y hW S T hTS, ?_⟩,
    fun S φ c c' h1 h2 => ?_, fun S φ hφ => ?_, fun S T φ c c' hTS hφc hφ hc hc' => ?_⟩
  · haveI := locallyCompact_unip h hJ hW S
    exact ⟨cocompact_unip_std h hJ hW S, exists_mass_one (cocompact_unip_std h hJ hW S)⟩
  · intro g hg
    simp only [levi, Subgroup.mem_iInf] at hg ⊢
    exact fun k hk => hg k (hTS hk)
  · haveI := locallyCompact_unip h hJ hW S
    exact IsConstTermOn.unique (cocompact_unip_std h hJ hW S) h1 h2
  · haveI := locallyCompact_unip h hJ hW S
    exact ⟨_, isConstTermOn_constTermOn (N := unip σ J X S) fun γ hγ g => hφ γ hγ.1 hγ.2 g⟩
  · haveI := locallyCompact_unip h hJ hW S
    haveI := locallyCompact_unip h hJ hW T
    have hle : unip σ J X T ≤ unip σ J X S := unip_mono_of_subset F E σ h n J hJ r X Y hW S T hTS
    have cS := cocompact_unip_std h hJ hW S
    have cT := cocompact_unip_std h hJ hW T
    have hfΓ : LeftInv (ratPts σ J ⊓ unip σ J X S) φ := fun γ hγ g => hφ γ hγ.1 hγ.2 g
    have hnorm : ∀ p ∈ unip σ J X S, ∀ u ∈ unip σ J X T, p * u * p⁻¹ ∈ unip σ J X T :=
      fun p hp u hu => conj_mem_unip_of_subset h hJ hW hTS hp hu
    have hc0 : c = constTermOn (ratPts σ J ⊓ unip σ J X S) (unip σ J X T) φ :=
      (isConstTermOn_iff_ratPts_inf hle cT hfΓ).1 hc
    subst hc0
    have hcΓ : LeftInv (ratPts σ J ⊓ unip σ J X S) (constTermOn (ratPts σ J ⊓ unip σ J X S) (unip σ J X T) φ) :=
      fun γ hγ g => GlobalTheory.Cusp.constTermOn_mul_left_of_normalizer hfΓ hγ
        (fun m => ⟨hnorm _ hγ.2 m, fun hm => by simpa [mul_assoc] using hnorm _ (inv_mem hγ.2) _ hm⟩) g
    have st : constTermOn (ratPts σ J ⊓ unip σ J X S) (unip σ J X S) φ =
        constTermOn (ratPts σ J ⊓ unip σ J X S) (unip σ J X S)
          (constTermOn (ratPts σ J ⊓ unip σ J X S) (unip σ J X T) φ) := funext fun x =>
      GlobalTheory.Cusp.Stages.constTermOn_stages (GAd σ J) (ratPts σ J ⊓ unip σ J X S) (unip σ J X S) (unip σ J X T) hle hnorm
        (cocompact_ratPts_inf le_rfl cS) (cocompact_ratPts_inf hle cT) φ hfΓ hφc x
    change IsConstTermOn σ J (unip σ J X S) _ c' at hc'
    change IsConstTermOn σ J (unip σ J X S) φ c'
    rw [isConstTermOn_iff_ratPts_inf le_rfl cS hcΓ] at hc'
    rw [isConstTermOn_iff_ratPts_inf le_rfl cS hfΓ, st]
    exact hc'

end Witt

end GlobalTheory.StdPar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnipotentRealisedOnAdelicSchwartz
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnipotentRealisedOnAdelicSchwartz
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN
open scoped Matrix

namespace GlobalTheory.AdelicSvNQuad

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic
open scoped Classical

def quad {R κ : Type} [CommRing R] [Fintype κ] (h : R) (A : Matrix κ κ R) (x : κ → R) : R := h * (x ⬝ᵥ (A *ᵥ x))

theorem map_quad {R S κ : Type} [CommRing R] [CommRing S] [Fintype κ] (q : R →+* S) (h : R) (A : Matrix κ κ R)
    (x : κ → R) : q (quad h A x) = quad (q h) (A.map q) (fun i => q (x i)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [quad, dotProduct, Matrix.mulVec, map_sum]

theorem quad_neg {R κ : Type} [CommRing R] [Fintype κ] (h : R) (A : Matrix κ κ R) (x : κ → R) :
    quad h (-A) x = -quad h A x := by
  simp [quad, Matrix.neg_mulVec]

theorem continuous_quad {R κ : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Fintype κ] (h : R)
    (A : Matrix κ κ R) : Continuous (quad h A) :=
  continuous_const.mul (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id))

theorem quad_add {R κ : Type} [CommRing R] [Invertible (2 : R)] [Fintype κ] (A : Matrix κ κ R) (hA : Aᵀ = A)
    (x u v : κ → R) : quad (⅟2) A x + (x ⬝ᵥ v + ⅟(2 : R) * (u ⬝ᵥ v)) =
      (x ⬝ᵥ (-(A *ᵥ u) + v) + ⅟(2 : R) * (u ⬝ᵥ (-(A *ᵥ u) + v))) + quad (⅟2) A (x + u) := by
  have hs : u ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (A *ᵥ u) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, dotProduct_comm]
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self _
  simp only [quad, Matrix.mulVec_add, dotProduct_add, add_dotProduct, dotProduct_neg, hs]
  linear_combination (-(x ⬝ᵥ (A *ᵥ u))) * h2

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def archMul (h : mixedEmbedding.mixedSpace F) (A : Matrix κ κ (mixedEmbedding.mixedSpace F))
    (y : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  eChar (-Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (quad h A y))

theorem archMul_temperate (h : mixedEmbedding.mixedSpace F) (A : Matrix κ κ (mixedEmbedding.mixedSpace F)) :
    Function.HasTemperateGrowth (archMul h A) := by
  have hp : ∀ i : κ, Function.HasTemperateGrowth fun y : κ → mixedEmbedding.mixedSpace F => y i := fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => mixedEmbedding.mixedSpace F) i).hasTemperateGrowth
  have hq : Function.HasTemperateGrowth (quad h A) := by
    have e : quad h A = fun y => h * ∑ i, y i * ∑ j, A i j * y j := rfl
    rw [e]
    refine (Function.HasTemperateGrowth.const h).mul (Function.HasTemperateGrowth.sum fun i _ => (hp i).mul ?_)
    exact Function.HasTemperateGrowth.sum fun j _ => (Function.HasTemperateGrowth.const _).mul (hp j)
  let L : mixedEmbedding.mixedSpace F →L[ℝ] ℝ :=
    -LinearMap.toContinuousLinearMap (Algebra.trace ℝ (mixedEmbedding.mixedSpace F))
  exact hasTemperateGrowth_eChar.comp (L.hasTemperateGrowth.comp hq)

def mulQ (ψ : AddChar (AF F) ℂ) (h : AF F) (A : Matrix κ κ (AF F)) :
    ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun φ x := ψ (quad h A x) * φ x
  map_add' φ φ' := funext fun x => mul_add _ _ _
  map_smul' a φ := funext fun x => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem mulQ_apply (ψ : AddChar (AF F) ℂ) (h : AF F) (A : Matrix κ κ (AF F)) (φ : (κ → AF F) → ℂ) (x : κ → AF F) :
    mulQ ψ h A φ x = ψ (quad h A x) * φ x := rfl

theorem mulQ_pureA (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (h : AF F) (A : Matrix κ κ (AF F))
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ g' ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ M : SInf F κ →L[ℂ] SInf F κ,
      ∀ f : SInf F κ, mulQ ψ h A (pureA F f g) = pureA F (M f) g' := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let q : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F := e.toRingHom.comp p1
  refine ⟨fun z => finChar ψ (quad (p2 h) (A.map p2) z) * g z,
    ⟨((finChar_isLocallyConstant ψ hψ.1).comp_continuous (continuous_quad _ _)).mul hg.1, hg.2.mul_left⟩,
    SchwartzMap.smulLeftCLM ℂ (archMul (q h) (A.map q)), fun f => funext fun x => ?_⟩
  let y : κ → mixedEmbedding.mixedSpace F := fun i => q (x i)
  let z : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (x i)
  have h3 : ψ (quad h A x) = archMul (q h) (A.map q) y * finChar ψ (quad (p2 h) (A.map p2) z) := by
    rw [map_eq_mul ψ, hψ.2.2 _ (at_mk _)]
    congr 1
    · have e1 : evI F (mk (p1 (quad h A x)) 0) = quad (q h) (A.map q) y := map_quad q h A x
      rw [e1, archMul, eChar_apply]
      congr 1
      push_cast
      ring
    · exact congrArg _ (map_quad p2 h A x)
  change ψ (quad h A x) * (f y * g z) =
    SchwartzMap.smulLeftCLM ℂ (archMul (q h) (A.map q)) f y * (finChar ψ (quad (p2 h) (A.map p2) z) * g z)
  rw [h3, SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _), smul_eq_mul]
  ring

theorem mulQ_mem (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (h : AF F) (A : Matrix κ κ (AF F)) :
    ∀ φ ∈ schA F κ, mulQ ψ h A φ ∈ schA F κ := by
  have hle : schA F κ ≤ (schA F κ).comap (mulQ ψ h A) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, g, hg, rfl⟩
    obtain ⟨g', hg', M, hM⟩ := mulQ_pureA ψ hψ h A hg
    exact Submodule.subset_span ⟨M f, g', hg', hM f⟩
  exact fun φ hφ => hle hφ

theorem act_unip {K R ι : Type} [Field K] [CommRing R] [Algebra K R] [Fintype ι] [DecidableEq ι] (C : Matrix ι ι K)
    (w : (ι → R) × (ι → R)) :
    AdelicSvN.act (Matrix.fromBlocks 1 0 (-C) 1) w = (w.1, -(C.map (algebraMap K R) *ᵥ w.1) + w.2) := by
  have h1 : (1 : Matrix ι ι K).map (algebraMap K R) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h0 : (0 : Matrix ι ι K).map (algebraMap K R) = 0 := Matrix.map_zero _ (map_zero _)
  have hn : (-C).map (algebraMap K R) = -C.map (algebraMap K R) := Matrix.map_neg _ (map_neg _) _
  simp only [AdelicSvN.act, Matrix.fromBlocks_map, h1, h0, hn, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, Matrix.neg_mulVec]

theorem realised_unip : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [DecidableEq κ] (C : Matrix κ κ F), Cᵀ = C → Realised ψ (Matrix.fromBlocks 1 0 (-C) 1) := by
  intro F _ _ ψ hψ κ _ _ C hC
  let A : Matrix κ κ (AF F) := C.map (algebraMap F (AF F))
  have hA : Aᵀ = A := by rw [← Matrix.transpose_map, hC]
  refine ⟨mulQ ψ (⅟2) A, mulQ_mem ψ hψ _ A, fun φ hφ => ⟨mulQ ψ (⅟2) (-A) φ, mulQ_mem ψ hψ _ _ φ hφ, ?_⟩,
    fun l hl => ⟨l ∘ₗ mulQ ψ (⅟2) A, fun g hg => ?_, fun _ _ => rfl⟩, fun w φ _ => funext fun x => ?_⟩
  · funext x
    rw [mulQ_apply, mulQ_apply, ← mul_assoc, ← AddChar.map_add_eq_mul, quad_neg, add_neg_cancel,
      AddChar.map_zero_eq_one, one_mul]
  · obtain ⟨g', hg', M, hM⟩ := mulQ_pureA ψ hψ (⅟2) A hg
    obtain ⟨T, hT⟩ := hl g' hg'
    exact ⟨T.comp M, fun f => (congrArg l (hM f)).trans (hT (M f))⟩
  · rw [act_unip, mulQ_apply]
    simp only [schr]
    rw [mulQ_apply, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, quad_add A hA]

end GlobalTheory.AdelicSvNQuad

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnipotentRealisedOnAdelicSchwartzStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerUnipotent_realisedOnAdelicSchwartz : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [DecidableEq κ] (C : Matrix κ κ F), Cᵀ = C → Realised ψ (Matrix.fromBlocks 1 0 (-C) 1) := by
  first | exact @GlobalTheory.AdelicSvNQuad.realised_unip | exact GlobalTheory.AdelicSvNQuad.realised_unip | (intros; apply GlobalTheory.AdelicSvNQuad.realised_unip <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDlNonneg
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SumSize.PairInt

open GlobalTheory.SumSize.TopInt

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

section Claims

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (C b : ℝ)

def PairIntRatAt : Prop := ∃ dl, Loss dl (bOne ch.G C b) ∧ ∀ (t : T) (p : Pair T), DefPair D.R.m p → ∀ w, Away ch.G t w →
  ∀ (k : ℕ) (d : FinDatum ch.G t p), 0 < k → IsCosetDatum k d → d.z = 1 → d.P = locPl ch.G t →
    (∀ l : ℕ, l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → padicValNat l k ≤ depL ch.G l) →
    ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big), ch.S.Z.IsRatAt d x y → ∀ (a : ℝ) v,
      InLat _ w a (latAt ch.S.toGridChoice p.small x) v →
        InLat _ w (a + dl w) (latAt ch.S.toGridChoice p.big y) (ch.S.Z.kkMap 1 d x y v)

end Claims

def PairIntRatK : Prop := BigC fun _ ch C b => PairIntRatAt ch C b

end GlobalTheory.SumSize.PairInt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerOperatorMemAdelicSchwartzStdChar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerOperatorMemAdelicSchwartzStdChar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchrSchA

theorem schr_mem_schA_of_isStdChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ]
    (w : (κ → AF D.host.F) × (κ → AF D.host.F)), ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
      GlobalTheory.WeilM.schr ψ w φ ∈ GlobalTheory.WeilM.schA D.host.F κ := by
  intro D ψ hψ κ _ w φ hφ
  exact GlobalTheory.HeisSchA.schr_mem_schA ψ (GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ) w φ hφ

end GlobalTheory.SchrSchA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerOperatorMemAdelicSchwartzStdCharStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodingerOperator_mem_adelicSchwartz_stdChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ]
    (w : (κ → AF D.host.F) × (κ → AF D.host.F)), ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
      GlobalTheory.WeilM.schr ψ w φ ∈ GlobalTheory.WeilM.schA D.host.F κ := by
  first | exact @GlobalTheory.SchrSchA.schr_mem_schA_of_isStdChar | exact GlobalTheory.SchrSchA.schr_mem_schA_of_isStdChar | (intros; apply GlobalTheory.SchrSchA.schr_mem_schA_of_isStdChar <;> assumption)
end
end
