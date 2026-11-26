module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.OsgoodSeparate
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartGramMA
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormDimLe

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsGraphAreaIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

def GraphAreaIntegral.Statement : Prop :=
  ∀ (d m n : ℕ) (e : Fin n ≃ Fin d ⊕ Fin m) (Ω : Set (EuclideanSpace ℂ (Fin d)))
    (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)),
    IsOpen Ω → DifferentiableOn ℂ F Ω → ∀ A ⊆ Ω, MeasurableSet A →
    ∀ h : EuclideanSpace ℂ (Fin n) → ℝ≥0∞,
      ∫⁻ y in graphPt e F '' A, h y ∂(μH[((2 * d : ℕ) : ℝ)]) =
        ∫⁻ x in A, h (graphPt e F x) * ENNReal.ofReal (areaJacobian
          (fderiv ℝ (graphPt e F) x : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)))
          ∂(μH[((2 * d : ℕ) : ℝ)])

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartLengthAlgClosed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section


open Classical in
def ChartLengthAlgClosed.Statement : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t u : Fin n → F)
    (q : MvPolynomial (Fin e × Fin n) F) (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I → Prime q → p = Ideal.span {q} →
      ¬ q ∣ specFirst f t →
        Module.length (Localization.AtPrime p) (ChartLoc I t e p ⧸ LinearMap.range
            (LinearMap.mulLeft (Localization.AtPrime p)
              (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u)))) =
          ∑ W ∈ (divCycle I u).support with Ideal.span {q} = incIdeal W e,
            ((divCycle I u W : ℕ) : ℕ∞)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PClosedPointConeCoord
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

theorem aeval_cone_of_isHomogeneous {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {n d : ℕ}
    (y : Fin n → Ω) {p : MvPolynomial (Fin n) F} (hp : p.IsHomogeneous d) :
    aeval (fun j => Polynomial.C (y j) * Polynomial.X) p =
      Polynomial.C (aeval y p) * Polynomial.X ^ d := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ j ∈ m.support, m j = d := by
    have := hp (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  rw [aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg, ← map_pow,
    ← map_prod, Polynomial.algebraMap_apply, map_mul, mul_assoc]

theorem ClosedPointConeCoord.proof : ClosedPointConeCoord.Statement := by
  intro F _ n I i hI hdim hXi Ω _ _ y hy hyI
  classical
  let φ : MvPolynomial (Fin n) F →ₐ[F] Polynomial Ω :=
    aeval fun j => Polynomial.C (y j) * Polynomial.X
  let P : Ideal (MvPolynomial (Fin n) F) := RingHom.ker φ
  have hPprime : P.IsPrime := RingHom.ker_isPrime _
  have hIP : I ≤ P := by
    intro g hg
    show φ g = 0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← sum_homogeneousComponent g, map_sum]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [show φ (homogeneousComponent d g) = _ from
      aeval_cone_of_isHomogeneous y (homogeneousComponent_isHomogeneous d g),
      hyI _ (hI.isHomog g hg d), map_zero, zero_mul]
  let m : Ideal (MvPolynomial (Fin n) F) := RingHom.ker (constantCoeff : MvPolynomial (Fin n) F →+* F)
  have hmprime : m.IsPrime := RingHom.ker_isPrime _
  have key : (Polynomial.evalRingHom (0 : Ω)).comp (φ : MvPolynomial (Fin n) F →+* Polynomial Ω) =
      (algebraMap F Ω).comp constantCoeff := by
    apply MvPolynomial.ringHom_ext <;> intro <;> simp [φ]
  have hPm : P ≤ m := by
    intro g hg
    have hg' : φ g = 0 := hg
    have h0 := RingHom.congr_fun key g
    simp only [RingHom.comp_apply, RingHom.coe_coe, hg', map_zero] at h0
    show constantCoeff g = 0
    exact (algebraMap F Ω).injective (by rw [← h0, map_zero])
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra h
    push Not at h
    exact hy (funext h)
  have hXjP : X j ∉ P := by
    intro h
    have h' : φ (X j) = 0 := h
    simp only [φ, aeval_X] at h'
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hj) Polynomial.X_ne_zero h'
  have hXjm : X j ∈ m := by
    show constantCoeff (X j : MvPolynomial (Fin n) F) = 0
    simp
  have hPlt : P < m := lt_of_le_of_ne hPm fun h => hXjP (h ▸ hXjm)
  have hIeq : I = P := by
    by_contra hne
    have hIlt : I < P := lt_of_le_of_ne hIP hne
    have h2 : ((2 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) F ⧸ I) := by
      rw [ringKrullDim_quotient, Order.le_krullDim_iff]
      let a : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) F) I :=
        ⟨⟨I, hI.isPrime⟩, fun _ h => h⟩
      let b : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) F) I :=
        ⟨⟨P, hPprime⟩, fun _ h => hIP h⟩
      let c : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) F) I :=
        ⟨⟨m, hmprime⟩, fun _ h => hPm (hIP h)⟩
      have hab : a < b := hIlt
      have hbc : b < c := hPlt
      exact ⟨LTSeries.mk 2 ![a, b, c]
        (Fin.strictMono_iff_lt_succ.mpr fun k => by fin_cases k; exacts [hab, hbc]), rfl⟩
    rw [hdim] at h2
    norm_num at h2
  intro hyi
  apply hXi
  rw [hIeq]
  show φ (X i) = 0
  simp [φ, hyi]

end ObjectsChow

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeFsLogIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Set Matrix Filter

noncomputable section

namespace ConeFsLog

variable {n : ℕ}

theorem dualNorm_pointOf (h : HermNorm n) (y : EuclideanSpace ℂ (Fin n)) :
    h.dualNorm (h.pointOf y) = ‖y‖ := by
  have hA : IsUnit h.matᵀ.det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  rw [HermNorm.dualNorm, HermNorm.pointOf, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA,
    Matrix.one_mulVec, EuclideanSpace.norm_eq]

theorem sum_mul_pointOf (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    ∑ j, u j * h.pointOf y j = ∑ i, (h.mat *ᵥ u) i * y i := by
  simp only [HermNorm.pointOf, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem norm_sum_mul_pointOf_le (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    ‖∑ j, u j * h.pointOf y j‖ ≤ h.norm u * ‖y‖ := by
  rw [sum_mul_pointOf, HermNorm.norm, EuclideanSpace.norm_eq]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

theorem fsLog_pointOf (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    fsLog h u (h.pointOf y) = Real.log (‖∑ j, u j * h.pointOf y j‖ / ‖y‖) := by
  rw [fsLog, dualNorm_pointOf]

theorem fsLog_pointOf_le (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    fsLog h u (h.pointOf y) ≤ max (Real.log (h.norm u)) 0 := by
  rw [fsLog_pointOf]
  rcases (div_nonneg (norm_nonneg _) (norm_nonneg y) :
    0 ≤ ‖∑ j, u j * h.pointOf y j‖ / ‖y‖).eq_or_lt with hr | hr
  · rw [← hr, Real.log_zero]; exact le_max_right _ _
  · refine (Real.log_le_log hr ?_).trans (le_max_left _ _)
    have hy : 0 < ‖y‖ := by
      rcases (norm_nonneg y).eq_or_lt with h0 | h0
      · simp [← h0] at hr
      · exact h0
    exact (div_le_iff₀ hy).mpr (norm_sum_mul_pointOf_le h u y)

theorem norm_le_of_fsLog_le (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) {t : ℝ}
    (hy : fsLog h u (h.pointOf y) ≤ -t) :
    ‖∑ j, u j * h.pointOf y j‖ ≤ Real.exp (-t) * ‖y‖ := by
  rw [fsLog_pointOf] at hy
  rcases (norm_nonneg y).eq_or_lt with h0 | h0
  · have := norm_sum_mul_pointOf_le h u y
    rw [← h0, mul_zero] at this
    rw [← h0, mul_zero]; exact this
  rcases (norm_nonneg (∑ j, u j * h.pointOf y j)).eq_or_lt with ha | ha
  · rw [← ha]; positivity
  · have := (Real.log_le_iff_le_exp (div_pos ha h0)).mp hy
    rwa [div_le_iff₀ h0] at this

end ConeFsLog


open ConeFsLog in
theorem ConeFsLogIntegrable.proof (hfin : ConeBallFinite.Statement)
    (hslab : ConeSlabBound.Statement) : ConeFsLogIntegrable.Statement := by
  intro n e h W f u hW hf hu
  have hS := hfin n e h W f hW hf
  obtain ⟨C, α, hα, hC⟩ := hslab n e h W f u hW hf hu
  set μ := (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)).restrict (coneBall h W)
  set F : EuclideanSpace ℂ (Fin n) → ℝ := fun y => fsLog h u (h.pointOf y) with hFdef
  set M := max (Real.log (h.norm u)) 0
  have hFm : Measurable F := by
    have : F = fun y => Real.log (‖∑ j, u j * h.pointOf y j‖ / ‖y‖) :=
      funext fun y => fsLog_pointOf h u y
    rw [this]
    have hp : Continuous (fun y : EuclideanSpace ℂ (Fin n) => h.pointOf y) := by
      unfold HermNorm.pointOf; fun_prop
    refine Real.measurable_log.comp (Measurable.div ?_ measurable_norm)
    exact (continuous_finsetSum _ fun j _ =>
      continuous_const.mul ((continuous_apply j).comp hp)).norm.measurable
  set G : EuclideanSpace ℂ (Fin n) → ℝ := fun y => max (-F y) 0
  have hGm : Measurable G := hFm.neg.max measurable_const

  have hG : ∫⁻ y, ENNReal.ofReal (G y) ∂μ < ⊤ := by
    rw [lintegral_eq_lintegral_meas_le (f := G) μ (Filter.Eventually.of_forall fun y => le_max_right _ _)
      hGm.aemeasurable]
    have hint : IntegrableOn (fun t => C * Real.exp (-α * t)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hα).const_mul C
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hint.lintegral_lt_top
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t (ht : 0 < t) => ?_)
    rw [Measure.restrict_apply (measurableSet_le measurable_const hGm)]
    refine (measure_mono ?_).trans ((hC (Real.exp (-t)) (Real.exp_pos _)
      (Real.exp_le_one_iff.mpr (by linarith))).trans_eq ?_)
    · rintro y ⟨hy, hyS⟩
      refine ⟨hyS, norm_le_of_fsLog_le h u y ?_⟩
      have : t ≤ -F y := by
        rcases le_max_iff.mp (show t ≤ G y from hy) with h1 | h1
        · exact h1
        · linarith
      change F y ≤ -t; linarith
    · rw [← Real.exp_mul]; ring_nf
  refine ⟨hFm.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hle : ∀ y, ‖F y‖ₑ ≤ ENNReal.ofReal M + ENNReal.ofReal (G y) := by
    intro y
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := fsLog_pointOf_le h u y
    rcases le_or_gt 0 (F y) with h2 | h2
    · rw [abs_of_nonneg h2]; have := le_max_right (-F y) 0; linarith
    · rw [abs_of_neg h2]; have := le_max_left (-F y) 0; have := le_max_right (Real.log (h.norm u)) 0
      linarith
  refine lt_of_le_of_lt (lintegral_mono hle) ?_
  rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hS, hG⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PHolomorphicImplicitGraph
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module Function

noncomputable section

namespace HolomorphicImplicitGraph

theorem exists_coordSplitting {n m : ℕ} (L : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin (n - m) → ℂ))
    (hL : finrank ℂ (LinearMap.ker L) = m) :
    ∃ e : Fin n ≃ Fin m ⊕ Fin (n - m), ∀ v : EuclideanSpace ℂ (Fin n),
      (∀ j k, e j = Sum.inl k → v j = 0) → L v = 0 → v = 0 := by
  classical
  have hmn : m ≤ n := by
    have := Submodule.finrank_le (LinearMap.ker L)
    simpa [hL] using this
  have hrange : LinearMap.range L = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have := LinearMap.finrank_range_add_finrank_ker L
    simp only [finrank_euclideanSpace_fin, hL] at this
    simp only [Module.finrank_fin_fun]
    omega
  let w : Fin n → (Fin (n - m) → ℂ) := fun j => L (EuclideanSpace.single j 1)
  have hw : Submodule.span ℂ (Set.range w) = ⊤ := by
    rw [← hrange, LinearMap.range_eq_map, ← (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.span_eq,
      Submodule.map_span, ← Set.range_comp]
    congr 2
    ext j
    simp [w]
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' ℂ w
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hcardκ : Fintype.card κ = n - m := by
    have := finrank_span_eq_card hli
    rw [hsp, hw, finrank_top, Module.finrank_fin_fun] at this
    exact this.symm
  let s : Set (Fin n) := Set.range a
  have hcs : Fintype.card s = n - m := by
    rw [← hcardκ]
    exact Fintype.card_congr (Equiv.ofInjective a ha).symm
  have hcc : Fintype.card (sᶜ : Set (Fin n)) = m := by
    rw [Fintype.card_compl_set, hcs, Fintype.card_fin]
    omega
  let eS : s ≃ Fin (n - m) := Fintype.equivFinOfCardEq hcs
  let eM : (sᶜ : Set (Fin n)) ≃ Fin m := Fintype.equivFinOfCardEq hcc
  let e : Fin n ≃ Fin m ⊕ Fin (n - m) :=
    (Equiv.Set.sumCompl s).symm.trans ((Equiv.sumComm _ _).trans (Equiv.sumCongr eM eS))
  refine ⟨e, fun v hv hLv => ?_⟩
  have hout : ∀ j ∉ s, v j = 0 := fun j hj =>
    hv j (eM ⟨j, hj⟩) (by simp [e, Equiv.Set.sumCompl_symm_apply_of_notMem hj])
  have hv' : L v = ∑ j, v j • w j := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr v]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [w, map_sum, map_smul]
  have hsum : ∑ c, v (a c) • w (a c) = 0 := by
    rw [Fintype.sum_of_injective a ha (fun c => v (a c) • w (a c)) (fun j => v j • w j)
      (fun j hj => by rw [hout j hj, zero_smul]) (fun c => rfl), ← hv', hLv]
  have hin : ∀ c, v (a c) = 0 := Fintype.linearIndependent_iff.1 hli (fun c => v (a c)) hsum
  refine PiLp.ext fun j => ?_
  by_cases hj : j ∈ s
  · obtain ⟨c, rfl⟩ := hj
    simpa using hin c
  · simpa using hout j hj

end HolomorphicImplicitGraph

theorem HolomorphicImplicitGraph.proof : HolomorphicImplicitGraph.Statement := by
  classical
  intro n m f y V hf hV hyV hfy hK

  let L : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin (n - m) → ℂ) :=
    LinearMap.pi fun i => (fderiv ℂ (f i) y : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ)
  obtain ⟨e, he⟩ := exists_coordSplitting L (by rw [LinearMap.ker_pi]; exact hK)

  let F : EuclideanSpace ℂ (Fin n) → (Fin n → ℂ) := fun z j =>
    Sum.elim (fun _ => z j) (fun i => f i z) (e j)
  let D : EuclideanSpace ℂ (Fin n) → (EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)) := fun z =>
    ContinuousLinearMap.pi fun j =>
      Sum.elim (fun _ => EuclideanSpace.proj j) (fun i => fderiv ℂ (f i) z) (e j)
  have hFd : ∀ z, HasFDerivAt F (D z) z := by
    intro z
    refine hasFDerivAt_pi.2 fun j => ?_
    rcases h : e j with k | i
    · simp only [Sum.elim_inl]
      exact (EuclideanSpace.proj (𝕜 := ℂ) j).hasFDerivAt
    · simp only [Sum.elim_inr]
      exact ((hf i).differentiable one_ne_zero z).hasFDerivAt
  have hFc : ContDiff ℂ 1 F := by
    refine contDiff_pi.2 fun j => ?_
    rcases h : e j with k | i
    · simp only [F, h, Sum.elim_inl]
      exact (EuclideanSpace.proj (𝕜 := ℂ) j).contDiff
    · simp only [F, h, Sum.elim_inr]
      exact hf i

  have hDy : Injective (D y) := by
    refine (injective_iff_map_eq_zero (D y)).2 fun v hv => he v (fun j k hj => ?_) ?_
    · have := congr_fun hv j
      simpa [D, hj] using this
    · funext i
      have := congr_fun hv (e.symm (Sum.inr i))
      simpa [D, L] using this
  let A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ) :=
    (LinearEquiv.ofInjectiveOfFinrankEq (D y : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ)) hDy
      (by simp)).toContinuousLinearEquiv
  have hA : (A : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)) = D y := by
    ext1 v
    rfl
  let P := hFc.contDiffAt.toOpenPartialHomeomorph F (f' := A) (by rw [hA]; exact hFd y) one_ne_zero

  let W : Set (EuclideanSpace ℂ (Fin n)) := (fun z => fderiv ℂ F z) ⁻¹'
    Set.range ((↑) : (EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ)) → _)
  have hW : IsOpen W := ContinuousLinearEquiv.isOpen.preimage (hFc.continuous_fderiv one_ne_zero)
  have hyW : y ∈ W := ⟨A, by rw [hA]; exact (hFd y).fderiv.symm⟩
  have hWinj : ∀ z ∈ W, Injective (D z) := by
    rintro z ⟨A', hA'⟩
    have hA'' : (A' : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)) = fderiv ℂ F z := hA'
    rw [← (hFd z).fderiv, ← hA'']
    exact A'.injective
  let U := P.source ∩ V ∩ W
  have hU : IsOpen U := (P.open_source.inter hV).inter hW
  have hyU : y ∈ U := ⟨⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _, hyV⟩, hyW⟩

  let ι : EuclideanSpace ℂ (Fin m) →L[ℂ] (Fin n → ℂ) := ContinuousLinearMap.pi fun j =>
    Sum.elim (fun k => EuclideanSpace.proj k) (fun _ => (0 : EuclideanSpace ℂ (Fin m) →L[ℂ] ℂ)) (e j)
  let g := P.symm
  let Φ : EuclideanSpace ℂ (Fin m) → EuclideanSpace ℂ (Fin (n - m)) := fun x =>
    WithLp.toLp 2 fun i => g (ι x) (e.symm (Sum.inr i))
  let Ω : Set (EuclideanSpace ℂ (Fin m)) := ι ⁻¹' (P.target ∩ g ⁻¹' U)
  have hΩ : IsOpen Ω := (P.isOpen_inter_preimage_symm hU).preimage ι.continuous
  have hG : ∀ x, ι x ∈ P.target → graphPt e Φ x = g (ι x) := by
    intro x hx
    have hFg : F (g (ι x)) = ι x := P.right_inv hx
    refine PiLp.ext fun j => ?_
    have hj := congr_fun hFg j
    rcases h : e j with k | i
    · simp [graphPt, F, ι, h] at hj ⊢
      exact hj.symm
    · have hs : e.symm (Sum.inr i) = j := e.symm_apply_eq.2 h.symm
      simp [graphPt, Φ, h, hs]
  have hzero : ∀ x, ι x ∈ P.target → ∀ i, f i (g (ι x)) = 0 := by
    intro x hx i
    have := congr_fun (P.right_inv hx) (e.symm (Sum.inr i))
    simpa [P, F, ι] using this
  let pin : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin m) := fun z =>
    WithLp.toLp 2 fun k => z (e.symm (Sum.inl k))
  have hFpin : ∀ z, (∀ i, f i z = 0) → F z = ι (pin z) := by
    intro z hz
    funext j
    rcases h : e j with k | i
    · have hs : e.symm (Sum.inl k) = j := e.symm_apply_eq.2 h.symm
      simp [F, ι, pin, h, hs]
    · simp [F, ι, h, hz i]
  have hgdiff : ∀ x ∈ Ω, DifferentiableAt ℂ g (ι x) := by
    intro x hx
    obtain ⟨A', hA'⟩ := hx.2.2
    have h1 : HasFDerivAt P (A' : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)) (P.symm (ι x)) := by
      rw [hA']
      exact (hFd _).differentiableAt.hasFDerivAt
    exact (P.contDiffAt_symm hx.1 h1 hFc.contDiffAt).differentiableAt one_ne_zero
  refine ⟨e, Ω, Φ, U, hU, hyU, fun z hz => hz.1.2, hΩ, ?_, ?_, ?_⟩
  · intro x hx
    refine (differentiableAt_euclidean.2 fun i => ?_).differentiableWithinAt
    show DifferentiableAt ℂ (fun x => g (ι x) (e.symm (Sum.inr i))) x
    exact (EuclideanSpace.proj (𝕜 := ℂ) (e.symm (Sum.inr i))).differentiableAt.comp x
      ((hgdiff x hx).comp x ι.differentiableAt)
  · ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hG x hx.1]
      exact ⟨hx.2, hzero x hx.1⟩
    · rintro ⟨hzU, hz0⟩
      have hFz := hFpin z hz0
      have ht : ι (pin z) ∈ P.target := by
        rw [← hFz]
        exact P.map_source hzU.1.1
      have hgz : g (ι (pin z)) = z := by
        rw [← hFz]
        exact P.left_inv hzU.1.1
      refine ⟨pin z, ⟨ht, ?_⟩, by rw [hG _ ht, hgz]⟩
      show g (ι (pin z)) ∈ U
      rw [hgz]
      exact hzU
  · intro x hx
    have hgx := hgdiff x hx
    let g' := fderiv ℂ g (ι x)
    have hGd : HasFDerivAt (graphPt e Φ) (g'.comp ι) x := by
      have h1 : HasFDerivAt (fun x => g (ι x)) (g'.comp ι) x :=
        hgx.hasFDerivAt.comp x ι.hasFDerivAt
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [hΩ.mem_nhds hx] with x' hx' using hG x' hx'.1
    have hDg : ∀ w, D (g (ι x)) (g' w) = w := by
      have h1 : HasFDerivAt (fun w => F (g w)) ((D (g (ι x))).comp g') (ι x) :=
        (hFd _).comp (ι x) hgx.hasFDerivAt
      have h2 : HasFDerivAt (fun w => F (g w)) (ContinuousLinearMap.id ℂ (Fin n → ℂ)) (ι x) := by
        refine (hasFDerivAt_id (ι x)).congr_of_eventuallyEq ?_
        filter_upwards [P.open_target.mem_nhds hx.1] with w hw using P.right_inv hw
      intro w
      have := congr_arg (fun T => T w) (h1.unique h2)
      simpa using this
    rw [hGd.fderiv, hG x hx.1]
    ext u
    simp only [LinearMap.mem_range, Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    constructor
    · rintro ⟨v, rfl⟩ i
      have := congr_fun (hDg (ι v)) (e.symm (Sum.inr i))
      simpa [D, ι] using this
    · intro hu
      refine ⟨pin u, ?_⟩
      show g' (ι (pin u)) = u
      apply hWinj _ hx.2.2
      rw [hDg]
      funext j
      rcases h : e j with k | i
      · have hs : e.symm (Sum.inl k) = j := e.symm_apply_eq.2 h.symm
        simp [D, ι, pin, h, hs]
      · have h2 : D (g (ι x)) u j = 0 := by
          simp only [D, ContinuousLinearMap.pi_apply, h, Sum.elim_inr]
          exact hu i
        rw [h2]
        simp [ι, h]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeSlabBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

open scoped ENNReal NNReal

noncomputable section

theorem ConeSlabBound.proof (hV : VarietySlabMeasure.Statement) : ConeSlabBound.Statement := by
  intro n e h W f u hW hf hu
  have hWp : W.IsPrime := hW.isPrime
  have hdim := ChowFormDimLe.proof ℂ n (e + 1) W f hW hf

  let E := WithLp.linearEquiv 2 ℂ (Fin n → ℂ)
  let F : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (E.symm.toLinearMap ∘ₗ h.matᵀ.mulVecLin ∘ₗ E.toLinearMap)
  let L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (E.symm.toLinearMap ∘ₗ (h.matᵀ)⁻¹.mulVecLin ∘ₗ E.toLinearMap)
  have hF : ∀ y i, F y i = h.pointOf y i := fun _ _ => rfl
  have hdet : IsUnit (h.matᵀ).det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  have hLF : ∀ y, L (F y) = y := by
    intro y
    ext i
    change ((h.matᵀ)⁻¹ *ᵥ (h.matᵀ *ᵥ fun j => y j)) i = y i
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  obtain ⟨C, α, hC, hα, hb⟩ := hV n (e + 1) W u hWp hdim hu ‖F‖
  set s : ℝ := ((2 * (e + 1) : ℕ) : ℝ) with hs
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  let K : ℝ≥0 := ‖L‖₊
  refine ⟨(K : ℝ) ^ s * C, α, hα, fun ε hε hε1 => ?_⟩

  have hsub : coneBall h W ∩ {y | ‖∑ j, u j * h.pointOf y j‖ ≤ ε * ‖y‖} ⊆
      L '' {z | z ∈ zeroSetEuc W ∧ ‖z‖ ≤ ‖F‖ ∧ ‖∑ j, u j * z j‖ ≤ ε} := by
    rintro y ⟨⟨hy1, hyW⟩, hyu⟩
    refine ⟨F y, ⟨fun q hq => ?_, ?_, ?_⟩, hLF y⟩
    · have : (fun i => F y i) = h.pointOf y := funext (hF y)
      rw [this]
      exact hyW q hq
    · calc ‖F y‖ ≤ ‖F‖ * ‖y‖ := F.le_opNorm y
        _ ≤ ‖F‖ * 1 := mul_le_mul_of_nonneg_left hy1.le (norm_nonneg _)
        _ = ‖F‖ := mul_one _
    · simp only [hF]
      calc ‖∑ j, u j * h.pointOf y j‖ ≤ ε * ‖y‖ := hyu
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hy1.le hε.le
        _ = ε := mul_one _
  calc μH[s] (coneBall h W ∩ {y | ‖∑ j, u j * h.pointOf y j‖ ≤ ε * ‖y‖})
      ≤ μH[s] (L '' {z | z ∈ zeroSetEuc W ∧ ‖z‖ ≤ ‖F‖ ∧ ‖∑ j, u j * z j‖ ≤ ε}) := measure_mono hsub
    _ ≤ (K : ℝ≥0∞) ^ s * μH[s] {z | z ∈ zeroSetEuc W ∧ ‖z‖ ≤ ‖F‖ ∧ ‖∑ j, u j * z j‖ ≤ ε} :=
        L.lipschitz.hausdorffMeasure_image_le hs0 _
    _ ≤ (K : ℝ≥0∞) ^ s * ENNReal.ofReal (C * ε ^ α) := by
        gcongr
        exact hb ε hε hε1
    _ = ENNReal.ofReal ((K : ℝ) ^ s * C * ε ^ α) := by
        rw [mul_assoc, ENNReal.ofReal_mul (Real.rpow_nonneg K.coe_nonneg _),
          ← ENNReal.ofReal_rpow_of_nonneg K.coe_nonneg hs0, ENNReal.ofReal_coe_nnreal]

end

end GroundTheory.Heights₂.Heights
end
