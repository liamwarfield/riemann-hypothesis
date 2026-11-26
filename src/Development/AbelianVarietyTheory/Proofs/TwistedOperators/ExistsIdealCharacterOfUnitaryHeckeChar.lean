module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdealCharacterOfUnitaryHeckeChar
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdealCharacterOfUnitaryHeckeChar
open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open Formalism.L2.Host (HChar)

namespace GlobalTheory

theorem exists_ideal_character_of_unitary_hchar : ∀ (K : Type) [Field K] [NumberField K] (χ : HChar K), χ.IsUnitary → ∃ (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ), m ≠ ⊥ ∧ X ⊥ = 0 ∧ X ⊤ = 1 ∧ (∀ I J, X (I * J) = X I * X J) ∧ (∀ I, I ≠ ⊥ → I ⊔ m = ⊤ → ‖X I‖ = 1) ∧ (∀ I, I ⊔ m ≠ ⊤ → X I = 0) ∧ (∀ P : HeightOneSpectrum (𝓞 K), X P.asIdeal = if χ.UnrAt P then ((χ.val P : ℂˣ) : ℂ) else 0) ∧ ∀ (β : 𝓞 K) (k : Kˣ), (k : K) = β → β - 1 ∈ m → X (Ideal.span {β}) = (((χ.inf k : ℂˣ) : ℂ))⁻¹ := by
  intro K _ _ χ hχ
  have hfin := GlobalTheory.Mem.UnrAe.finite_ramified χ
  choose n hn using GlobalTheory.Mem.UnrAe.exists_levelLe χ
  let S : Finset (HeightOneSpectrum (𝓞 K)) := hfin.toFinset
  have hS : ∀ P, P ∈ S ↔ ¬ χ.UnrAt P := fun P => by simp [S]
  let m : Ideal (𝓞 K) := ∏ P ∈ S, P.asIdeal ^ (n P + 1)
  have hdvd : ∀ P ∈ S, P.asIdeal ^ (n P + 1) ∣ m := fun P hP =>
    Finset.dvd_prod_of_mem (fun P : HeightOneSpectrum (𝓞 K) => P.asIdeal ^ (n P + 1)) hP
  have hm : ∀ P : HeightOneSpectrum (𝓞 K), m ≤ P.asIdeal ↔ P ∈ S := by
    intro P
    constructor
    · intro h
      have hprod : ∀ (T : Finset (HeightOneSpectrum (𝓞 K))),
          P.asIdeal ∣ ∏ Q ∈ T, Q.asIdeal ^ (n Q + 1) →
          ∃ Q ∈ T, P.asIdeal ∣ Q.asIdeal ^ (n Q + 1) := by
        intro T
        induction T using Finset.induction_on with
        | empty =>
          simp only [Finset.prod_empty]
          intro hd
          exact (P.prime.not_dvd_one hd).elim
        | @insert Q T hQT ih =>
          simp only [Finset.prod_insert hQT]
          intro hd
          rcases P.prime.dvd_or_dvd hd with hd | hd
          · exact ⟨Q, Finset.mem_insert_self _ _, hd⟩
          · obtain ⟨R, hR, hd⟩ := ih hd
            exact ⟨R, Finset.mem_insert_of_mem hR, hd⟩
      obtain ⟨Q, hQ, hQP⟩ := hprod S (Ideal.dvd_iff_le.2 h)
      have h1 : Q.asIdeal ≤ P.asIdeal := Ideal.le_of_dvd (P.prime.dvd_of_dvd_pow hQP)
      have h2 : Q = P := HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h1)
      exact h2 ▸ hQ
    · intro h
      exact Ideal.le_of_dvd ((dvd_pow_self _ (Nat.succ_ne_zero _)).trans (hdvd P h))
  have hm0 : m ≠ ⊥ := Finset.prod_ne_zero_iff.2 fun P _ => pow_ne_zero _ P.ne_bot
  obtain ⟨X, h0, h1, hmul, hnorm, hz, hP⟩ := GlobalTheory.exists_multiplicative_ideal_extension K m
    (fun P => ((χ.val P : ℂˣ) : ℂ)) (fun P _ => hχ _)
  refine ⟨m, X, hm0, h0, h1, hmul, hnorm, hz, ?_, ?_⟩
  · intro P
    split_ifs with h
    · exact hP P fun h' => (hS P).1 ((hm P).1 h') h
    · apply hz
      rw [sup_eq_left.2 ((hm P).2 ((hS P).2 h))]
      exact P.isPrime.ne_top
  · intro β k hk hβ1
    have hβ : β ≠ 0 := by
      rintro rfl
      exact k.ne_zero (by simpa using hk)
    have hne : (Ideal.span {β} : Ideal (𝓞 K)) ≠ 0 := by
      simpa [Ideal.span_singleton_eq_bot] using hβ
    have hval : ∀ (P : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K),
        Valued.v (algebraMap K (P.adicCompletion K) (r : K)) = P.intValuation r := by
      intro P r
      rw [← HeightOneSpectrum.valuation_of_algebraMap (K := K)]
      exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P (r : K)
    have hnot : ∀ P ∈ S, β ∉ P.asIdeal := by
      intro P hPS h
      apply P.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have := P.asIdeal.sub_mem h ((hm P).2 hPS hβ1)
      simpa using this
    have hloc : ∀ P ∈ S, χ.locK P k = 1 := by
      intro P hPS
      have e : ((Formalism.L2.Host.atFin P k : (P.adicCompletion K)ˣ) : P.adicCompletion K)
          = algebraMap K (P.adicCompletion K) (β : K) := by
        rw [← hk]; rfl
      refine hn P _ ?_ ?_
      · unfold Formalism.L2.Host.IsUnitAt
        rw [e, hval]
        exact HeightOneSpectrum.intValuation_eq_one_iff.2 (hnot P hPS)
      · have e2 : algebraMap K (P.adicCompletion K) (β : K) - 1
            = algebraMap K (P.adicCompletion K) ((β - 1 : 𝓞 K) : K) := by simp
        rw [e, e2, hval, HeightOneSpectrum.intValuation_le_pow_iff_mem]
        exact Ideal.le_of_dvd ((pow_dvd_pow _ (Nat.le_succ _)).trans (hdvd P hPS)) hβ1
    have hpr := GlobalTheory.HeckeProduct.hchar_productRule K χ S
      (fun v hv => not_not.1 fun h => hv ((hS v).2 h)) k
    rw [Finset.prod_eq_one hloc, mul_one] at hpr
    let φ : Ideal (𝓞 K) →* ℂ :=
      { toFun := X, map_one' := by rw [Ideal.one_eq_top, h1], map_mul' := hmul }
    have hφ : ∀ I, φ I = X I := fun _ => rfl
    have hord : ∀ v : HeightOneSpectrum (𝓞 K), Formalism.L2.Host.ordF v k =
        ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {β} : Ideal (𝓞 K))).factors : ℕ) := by
      intro v
      unfold Formalism.L2.Host.ordF
      rw [hk]
      have : v.valuation K (β : K) = v.intValuation β := HeightOneSpectrum.valuation_of_algebraMap v β
      rw [this, HeightOneSpectrum.intValuation_if_neg _ hβ, WithZero.log_exp, neg_neg]
    have hfs : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) =>
        ∏ᶠ (_ : v ∉ S), χ.val v ^ Formalism.L2.Host.ordF v k).Finite := by
      refine (GlobalTheory.HeckeProduct.finite_ordF k).subset fun v hv h => hv ?_
      simp only [h, zpow_zero, finprod_one]
    have key : X (Ideal.span {β}) = ((∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ S),
        χ.val v ^ Formalism.L2.Host.ordF v k : ℂˣ) : ℂ) := by
      have e1 := (Units.coeHom ℂ).map_finprod hfs
      rw [Units.coeHom_apply] at e1
      rw [e1, ← hφ, ← Ideal.finprod_heightOneSpectrum_factorization hne,
        φ.map_finprod (Ideal.hasFiniteMulSupport hne)]
      refine finprod_congr fun v => ?_
      rw [HeightOneSpectrum.maxPowDividing, map_pow, hφ, hord, Units.coeHom_apply]
      by_cases hv : v ∈ S
      · have hc : (Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span {β} : Ideal (𝓞 K))).factors = 0 := by
          by_contra hc
          have := (Associates.count_ne_zero_iff_dvd hne v.irreducible).1 hc
          exact hnot v hv (Ideal.dvd_span_singleton.1 this)
        simp [hc]
      · rw [hP v fun h => hv ((hm v).1 h)]
        simp [hv]
    rw [key, ← Units.val_inv_eq_inv_val, (inv_eq_of_mul_eq_one_right hpr)]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdealCharacterOfUnitaryHeckeCharStatement
open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open Formalism.L2.Host (HChar)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idealCharacter_of_unitary_heckeChar : ∀ (K : Type) [Field K] [NumberField K] (χ : HChar K), χ.IsUnitary → ∃ (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ), m ≠ ⊥ ∧ X ⊥ = 0 ∧ X ⊤ = 1 ∧ (∀ I J, X (I * J) = X I * X J) ∧ (∀ I, I ≠ ⊥ → I ⊔ m = ⊤ → ‖X I‖ = 1) ∧ (∀ I, I ⊔ m ≠ ⊤ → X I = 0) ∧ (∀ P : HeightOneSpectrum (𝓞 K), X P.asIdeal = if χ.UnrAt P then ((χ.val P : ℂˣ) : ℂ) else 0) ∧ ∀ (β : 𝓞 K) (k : Kˣ), (k : K) = β → β - 1 ∈ m → X (Ideal.span {β}) = (((χ.inf k : ℂˣ) : ℂ))⁻¹ := by
  first | exact @GlobalTheory.exists_ideal_character_of_unitary_hchar | exact GlobalTheory.exists_ideal_character_of_unitary_hchar | (intros; apply GlobalTheory.exists_ideal_character_of_unitary_hchar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerFderivKAveragedMinorOperatorIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerFderivKAveragedMinorOperatorIntegral
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.SphJet.PsDer

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private lemma aestronglyMeasurable_of_continuous_compact {K E : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K]
    [OpensMeasurableSpace K] [NormedAddCommGroup E] (μ : Measure K) {f : K → E} (hf : Continuous f) :
    AEStronglyMeasurable f μ := by
  have h := hf.continuousOn.aestronglyMeasurable_of_isCompact (μ := μ) isCompact_univ MeasurableSet.univ
  rwa [Measure.restrict_univ] at h

private lemma integrable_of_continuous_compact' {K E : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [OpensMeasurableSpace K] [NormedAddCommGroup E] (μ : Measure K) [IsFiniteMeasure μ]
    {f : K → E} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound (aestronglyMeasurable_of_continuous_compact μ hf) C
    (Filter.Eventually.of_forall fun k => hC k (Set.mem_univ k))

theorem hasDerivAt_integral_cpt {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K]
    [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] {F F' : ℂ → K → ℂ} {s : Set ℂ} (hs : s ∈ 𝓝 (0 : ℂ))
    (hF : ∀ t ∈ s, Continuous (F t)) (hF' : ContinuousOn (fun x : ℂ × K => F' x.1 x.2) (s ×ˢ Set.univ))
    (hd : ∀ k, ∀ t ∈ s, HasDerivAt (F · k) (F' t k) t) :
    HasDerivAt (fun t => ∫ k, F t k ∂μ) (∫ k, F' 0 k ∂μ) 0 := by
  have h0 : (0 : ℂ) ∈ s := mem_of_mem_nhds hs
  obtain ⟨r, hr, hrs⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hs
  have hcpt : IsCompact (Metric.closedBall (0 : ℂ) r ×ˢ (Set.univ : Set K)) :=
    (isCompact_closedBall 0 r).prod isCompact_univ
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn (hF'.mono (Set.prod_mono hrs subset_rfl))
  have hF'0 : Continuous (F' 0) :=
    hF'.comp_continuous (continuous_const.prodMk continuous_id) fun k => ⟨h0, Set.mem_univ k⟩
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C)
    (Metric.closedBall_mem_nhds 0 hr) ?_ (integrable_of_continuous_compact' μ (hF 0 h0))
    (aestronglyMeasurable_of_continuous_compact μ hF'0) ?_ (integrable_const C) ?_).2
  · exact Filter.eventually_of_mem hs fun t ht => aestronglyMeasurable_of_continuous_compact μ (hF t ht)
  · exact Filter.Eventually.of_forall fun k t ht => hC (t, k) ⟨ht, Set.mem_univ k⟩
  · exact Filter.Eventually.of_forall fun k t ht => hd k t (hrs ht)

private lemma analyticAt_leadMinor' (z₀ : Matrix (Fin n) (Fin n) ℂ) (l : ℕ) (hl : l ≤ n) :
    AnalyticAt ℂ (fun z : Matrix (Fin n) (Fin n) ℂ => leadMinor z l hl) z₀ := by
  have he : ∀ a b : Fin n, AnalyticAt ℂ (fun z : Matrix (Fin n) (Fin n) ℂ => z a b) z₀ := fun a b =>
    (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ a b)).analyticAt z₀
  simp only [leadMinor, Matrix.det_apply, Matrix.submatrix_apply, Units.smul_def, zsmul_eq_mul]
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  refine AnalyticAt.mul ?_ ?_
  · exact analyticAt_const
  · exact Finset.analyticAt_fun_prod _ fun i _ => he _ _

theorem analyticOnNhd_Phi (lam : Fin n → ℝ) : AnalyticOnNhd ℂ (Phi lam) (Omega n) := by
  intro z hz
  have hz' : ∀ i : Fin n, leadMinor z (i.val + 1) i.isLt ≠ 0 := hz
  show AnalyticAt ℂ (fun y => ∏ i : Fin n, leadMinor y (i.val + 1) i.isLt ^ (-(sInt lam i))) z
  exact Finset.analyticAt_fun_prod _ fun i _ => (analyticAt_leadMinor' z _ _).fun_zpow (hz' i)

theorem continuous_conj {ε : Fin n → Bool} {X : Type} [TopologicalSpace X] {f : X → KG ε}
    {g : X → Matrix (Fin n) (Fin n) ℂ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun p => (toMK (f p))⁻¹ * g p * toMK (f p)) := by
  have hK : Continuous (fun k : KG ε => toMK k) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hinv : ∀ k : KG ε, (toMK k)⁻¹ = toMK k⁻¹ := fun k => by
    simp [toMK, toM, Matrix.coe_units_inv]
  have e : (fun p => (toMK (f p))⁻¹ * g p * toMK (f p)) = fun p => toMK (f p)⁻¹ * g p * toMK (f p) := by
    funext p; rw [hinv]
  rw [e]
  exact ((hK.comp hf.inv).matrix_mul hg).matrix_mul (hK.comp hf)

private lemma toMK_inv_mul_mul_toMK_mem_Omega {ε : Fin n → Bool} {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ U1 ε)
    (k : KG ε) : (toMK k)⁻¹ * z * toMK k ∈ Omega n :=
  hz _ ((mem_KG ε _).1 k.2)

private lemma continuous_toMK_inv_mul_mul_toMK {ε : Fin n → Bool} (M : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun k : KG ε => (toMK k)⁻¹ * M * toMK k) :=
  continuous_conj (f := fun k => k) (g := fun _ => M) continuous_id continuous_const

private lemma continuous_inner_tau_toMK {ε : Fin n → Bool} {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W} (h : IsTau ε abelian₂ τ w)
    (u v : W) : Continuous (fun k : KG ε => ⟪u, τ (toMK k) v⟫_ℂ) := by
  have hK : Continuous (fun k : KG ε => toMK k) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hd := h.2.2.1 u v
  exact hd.continuousOn.comp_continuous hK fun k =>
    ⟨((k : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ).isUnit, ((mem_KG ε _).1 k.2).2⟩

private lemma continuous_tau_toMK_apply {ε : Fin n → Bool} {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W} (h : IsTau ε abelian₂ τ w)
    (v : W) : Continuous (fun k : KG ε => τ (toMK k) v) := by
  haveI : FiniteDimensional ℂ W := h.1
  let b := stdOrthonormalBasis ℂ W
  have e : (fun k : KG ε => τ (toMK k) v) = fun k => ∑ i, ⟪b i, τ (toMK k) v⟫_ℂ • b i := by
    funext k; exact (b.sum_repr' _).symm
  rw [e]
  exact continuous_finsetSum _ fun i _ => (continuous_inner_tau_toMK h (b i) v).smul continuous_const

private lemma continuous_Phi_conj_toMK {ε : Fin n → Bool} (lam : Fin n → ℝ) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ U1 ε) : Continuous (fun k : KG ε => Phi lam ((toMK k)⁻¹ * z * toMK k)) :=
  continuous_iff_continuousAt.2 fun k =>
    ContinuousAt.comp (g := Phi lam) (f := fun k : KG ε => (toMK k)⁻¹ * z * toMK k)
      (analyticOnNhd_Phi lam _ (toMK_inv_mul_mul_toMK_mem_Omega hz k)).continuousAt (continuous_toMK_inv_mul_mul_toMK z).continuousAt

theorem inner_ps_eq {ε : Fin n → Bool} (lam : Fin n → ℝ) {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W} (h : IsTau ε abelian₂ τ w)
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ U1 ε) (y u : W) :
    ⟪y, ps ε lam τ w z u⟫_ℂ = (Module.finrank ℂ W : ℂ) * ∫ k : KG ε, Phi lam ((toMK k)⁻¹ * z * toMK k) *
      (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, u⟫_ℂ) ∂(muK ε) := by
  haveI : FiniteDimensional ℂ W := h.1
  have hv : Continuous (fun k : KG ε => τ (toMK k) w) := continuous_tau_toMK_apply h w
  have hR : Continuous (fun k : KG ε => (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w)) := by
    have h1 := ((ContinuousLinearMap.smulRightL ℂ W W).continuous.comp
      ((innerSL ℂ).continuous.comp hv)).clm_apply hv
    simpa using h1
  have hG : Continuous (fun k : KG ε => Phi lam ((toMK k)⁻¹ * z * toMK k) •
      (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w)) :=
    (continuous_Phi_conj_toMK lam hz).smul hR
  have hGi := integrable_of_continuous_compact' (muK ε) hG
  have hGu := hGi.apply_continuousLinearMap u
  simp only [ps]
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, ContinuousLinearMap.integral_apply hGi u,
    ← integral_inner hGu y]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    inner_smul_right]
  ring

theorem inner_fderiv_ps : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam → IsTau ε (lowK ε lam) τ w → ∀ z ∈ U1 ε, ∀ (A : Matrix (Fin n) (Fin n) ℂ) (y x : W), Integrable (fun k : KG ε => fderiv ℂ (Phi lam) ((toMK k)⁻¹ * z * toMK k) ((toMK k)⁻¹ * A * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ)) (muK ε) ∧ ⟪y, fderiv ℂ (ps ε lam τ w) z A x⟫_ℂ = (Module.finrank ℂ W : ℂ) * ∫ k : KG ε, fderiv ℂ (Phi lam) ((toMK k)⁻¹ * z * toMK k) ((toMK k)⁻¹ * A * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ) ∂(muK ε) := by
  intro n ε lam W _ _ τ w hHC hTau z hz A y x
  haveI : FiniteDimensional ℂ W := hTau.1
  obtain ⟨hopen, -, hdiff, -⟩ := psBasic n ε lam W τ w hHC hTau
  have hU : IsOpen (U1 ε) := hopen
  have hSn : {t : ℂ | z + t • A ∈ U1 ε} ∈ 𝓝 (0 : ℂ) := by
    have hcont : Continuous (fun t : ℂ => z + t • A) := continuous_const.add (continuous_id.smul continuous_const)
    exact hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simpa using hz))
  have hpsD : DifferentiableAt ℂ (ps ε lam τ w) z := hdiff.differentiableAt (hopen.mem_nhds hz)
  have hline : HasDerivAt (fun t : ℂ => z + t • A) A 0 := by
    have h := ((hasDerivAt_id' (0 : ℂ)).smul_const A).const_add z
    rw [one_smul] at h
    exact h
  have hg1 : HasDerivAt (fun t : ℂ => ⟪y, ps ε lam τ w (z + t • A) x⟫_ℂ)
      ⟪y, fderiv ℂ (ps ε lam τ w) z A x⟫_ℂ 0 := by
    let L : (W →L[ℂ] W) →L[ℂ] ℂ := (innerSL ℂ y).comp (ContinuousLinearMap.apply ℂ W x)
    have h1 := hpsD.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hline (by simp)
    have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℂ) h1
    have h3 := h2
    simp only [L, Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      innerSL_apply_apply] at h3
    exact h3
  have hv : Continuous (fun k : KG ε => τ (toMK k) w) := continuous_tau_toMK_apply hTau w
  have hc : Continuous (fun k : KG ε => ⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ) :=
    (continuous_const.inner hv).mul (hv.inner continuous_const)
  have hconj : Continuous (fun p : ℂ × KG ε => (toMK p.2)⁻¹ * (z + p.1 • A) * toMK p.2) :=
    continuous_conj continuous_snd (continuous_const.add (continuous_fst.smul continuous_const))
  have hmem : ∀ t ∈ {t : ℂ | z + t • A ∈ U1 ε}, ∀ k : KG ε,
      (toMK k)⁻¹ * (z + t • A) * toMK k ∈ Omega n := fun t ht k => toMK_inv_mul_mul_toMK_mem_Omega ht k
  have hAn := analyticOnNhd_Phi (n := n) lam
  have hdA := hAn.fderiv
  have hFc : ∀ t ∈ {t : ℂ | z + t • A ∈ U1 ε}, Continuous (fun k : KG ε =>
      Phi lam ((toMK k)⁻¹ * (z + t • A) * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ)) :=
    fun t ht => (continuous_Phi_conj_toMK lam ht).mul hc
  have hF'c : ContinuousOn (fun p : ℂ × KG ε => fderiv ℂ (Phi lam) ((toMK p.2)⁻¹ * (z + p.1 • A) * toMK p.2)
      ((toMK p.2)⁻¹ * A * toMK p.2) * (⟪y, τ (toMK p.2) w⟫_ℂ * ⟪τ (toMK p.2) w, x⟫_ℂ))
      ({t : ℂ | z + t • A ∈ U1 ε} ×ˢ Set.univ) := by
    intro p hp
    have h1 : ContinuousAt (fun q : ℂ × KG ε =>
        fderiv ℂ (Phi lam) ((toMK q.2)⁻¹ * (z + q.1 • A) * toMK q.2)) p :=
      ContinuousAt.comp (g := fderiv ℂ (Phi lam))
        (f := fun q : ℂ × KG ε => (toMK q.2)⁻¹ * (z + q.1 • A) * toMK q.2)
        (hdA _ (hmem p.1 hp.1 p.2)).continuousAt hconj.continuousAt
    have h2 : Continuous (fun q : ℂ × KG ε => (toMK q.2)⁻¹ * A * toMK q.2) :=
      continuous_conj continuous_snd continuous_const
    exact ((h1.clm_apply h2.continuousAt).mul (hc.comp continuous_snd).continuousAt).continuousWithinAt
  have hder : ∀ k : KG ε, ∀ t ∈ {t : ℂ | z + t • A ∈ U1 ε}, HasDerivAt
      (fun s : ℂ => Phi lam ((toMK k)⁻¹ * (z + s • A) * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ))
      (fderiv ℂ (Phi lam) ((toMK k)⁻¹ * (z + t • A) * toMK k) ((toMK k)⁻¹ * A * toMK k) *
        (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ)) t := by
    intro k t ht
    have hl : HasDerivAt (fun s : ℂ => (toMK k)⁻¹ * (z + s • A) * toMK k) ((toMK k)⁻¹ * A * toMK k) t := by
      have e : (fun s : ℂ => (toMK k)⁻¹ * (z + s • A) * toMK k) =
          fun s => (toMK k)⁻¹ * z * toMK k + s • ((toMK k)⁻¹ * A * toMK k) := by
        funext s; simp [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul]
      rw [e]
      have h := ((hasDerivAt_id' t).smul_const ((toMK k)⁻¹ * A * toMK k)).const_add ((toMK k)⁻¹ * z * toMK k)
      rw [one_smul] at h
      exact h
    exact ((hAn _ (hmem t ht k)).differentiableAt.hasFDerivAt.comp_hasDerivAt t hl).mul_const _
  have hD := hasDerivAt_integral_cpt (muK ε) hSn hFc hF'c hder
  have hg2 : HasDerivAt (fun t : ℂ => ⟪y, ps ε lam τ w (z + t • A) x⟫_ℂ)
      ((Module.finrank ℂ W : ℂ) * ∫ k, fderiv ℂ (Phi lam) ((toMK k)⁻¹ * (z + (0 : ℂ) • A) * toMK k)
        ((toMK k)⁻¹ * A * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ) ∂(muK ε)) 0 := by
    refine (hD.const_mul _).congr_of_eventuallyEq ?_
    filter_upwards [hSn] with t ht
    exact inner_ps_eq lam hTau ht y x
  have heq := hg1.unique hg2
  simp only [zero_smul, add_zero] at heq
  refine ⟨?_, heq⟩
  have hcont0 : Continuous (fun k : KG ε => fderiv ℂ (Phi lam) ((toMK k)⁻¹ * z * toMK k)
      ((toMK k)⁻¹ * A * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ)) := by
    refine continuous_iff_continuousAt.2 fun k => ContinuousAt.mul ?_ hc.continuousAt
    exact (ContinuousAt.comp (g := fderiv ℂ (Phi lam)) (f := fun k : KG ε => (toMK k)⁻¹ * z * toMK k)
      (hdA _ (toMK_inv_mul_mul_toMK_mem_Omega hz k)).continuousAt
      (continuous_toMK_inv_mul_mul_toMK z).continuousAt).clm_apply (continuous_toMK_inv_mul_mul_toMK A).continuousAt
  exact integrable_of_continuous_compact' (muK ε) hcont0

end GlobalTheory.SphJet.PsDer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerFderivKAveragedMinorOperatorIntegralStatement
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_fderiv_kAveragedMinorOperator_integral : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam → IsTau ε (lowK ε lam) τ w → ∀ z ∈ U1 ε, ∀ (A : Matrix (Fin n) (Fin n) ℂ) (y x : W), Integrable (fun k : KG ε => fderiv ℂ (Phi lam) ((toMK k)⁻¹ * z * toMK k) ((toMK k)⁻¹ * A * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ)) (muK ε) ∧ ⟪y, fderiv ℂ (ps ε lam τ w) z A x⟫_ℂ = (Module.finrank ℂ W : ℂ) * ∫ k : KG ε, fderiv ℂ (Phi lam) ((toMK k)⁻¹ * z * toMK k) ((toMK k)⁻¹ * A * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ) ∂(muK ε) := by
  first | exact @GlobalTheory.SphJet.PsDer.inner_fderiv_ps | exact GlobalTheory.SphJet.PsDer.inner_fderiv_ps | (intros; apply GlobalTheory.SphJet.PsDer.inner_fderiv_ps <;> assumption)
end
end
