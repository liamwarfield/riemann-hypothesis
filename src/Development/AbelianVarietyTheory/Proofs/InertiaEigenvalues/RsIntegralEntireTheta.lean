module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DifferentiableIntegralMulCpow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameGenAtTransport

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnMinAbsDetInvFundamentalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnMinAbsDetInvFundamentalDomain
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open scoped ENNReal

noncomputable section

open GlobalTheory.UnitaryBC

namespace GlobalTheory.FinVolGL

theorem exists_tsum_min_le {T : ℝ} (hT : 1 < T) : ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ u : ℝ, 0 < u →
    ∑' n : ℤ, ENNReal.ofReal (min (T ^ n * u) (T ^ n * u)⁻¹) ≤ B := by
  have hT0 : 0 < T := one_pos.trans hT
  have hq0 : 0 ≤ T⁻¹ := inv_nonneg.2 hT0.le
  have hq : T⁻¹ < 1 := inv_lt_one_of_one_lt₀ hT
  have hsum : Summable fun k : ℤ => T * T⁻¹ ^ k.natAbs :=
    (Summable.of_nat_of_neg (by simpa using summable_geometric_of_lt_one hq0 hq)
      (by simpa using summable_geometric_of_lt_one hq0 hq)).mul_left T
  refine ⟨∑' k : ℤ, ENNReal.ofReal (T * T⁻¹ ^ k.natAbs), hsum.tsum_ofReal_ne_top, fun u hu => ?_⟩
  obtain ⟨m, h1, h2⟩ := exists_mem_Ico_zpow hu hT
  rw [← (Equiv.subRight m).tsum_eq]
  refine ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal ?_
  rw [Equiv.subRight_apply]
  have hp : 0 < T ^ (k - m) := zpow_pos hT0 _
  have e1 : T ^ (k - m) * T ^ m = T ^ k := by rw [← zpow_add₀ hT0.ne', sub_add_cancel]
  have e2 : T ^ (k - m) * T ^ (m + 1) = T ^ (k + 1) := by
    rw [← zpow_add₀ hT0.ne']; congr 1; ring
  have hv1 : T ^ k ≤ T ^ (k - m) * u := e1 ▸ mul_le_mul_of_nonneg_left h1 hp.le
  have hv2 : T ^ (k - m) * u < T ^ (k + 1) := e2 ▸ mul_lt_mul_of_pos_left h2 hp
  obtain ⟨j, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · refine (min_le_right _ _).trans ?_
    have h3 := inv_anti₀ (zpow_pos hT0 _) hv1
    rw [zpow_natCast, ← inv_pow] at h3
    rw [Int.natAbs_natCast]
    exact h3.trans (le_mul_of_one_le_left (pow_nonneg hq0 _) hT.le)
  · refine (min_le_left _ _).trans (hv2.le.trans (le_of_eq ?_))
    rw [zpow_add_one₀ hT0.ne', _root_.zpow_neg, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast, inv_pow, mul_comm]

theorem integrableOn_min_absDet : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ), 0 < m →
    ∀ (μ : Measure (GA E m)) [μ.IsHaarMeasure] (𝓕 : Set (GA E m)),
      IsFundamentalDomain (ratGL E m).range 𝓕 μ →
      IntegrableOn (fun h : GA E m => min (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det h) : ℝ)
        (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det h) : ℝ)⁻¹) 𝓕 μ := by
  intro E _ _ _ a ha μ _ 𝓕 h𝓕
  set δ : GA E a → ℝ := fun g => (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδ
  have hδc : Continuous δ := GlobalTheory.RSTheta.continuous_absDet
  have hδ0 : ∀ g, 0 < δ g := fun g => (GroundTheory.Global.IdeleGroup.ideleModule E _).2
  have hδr : ∀ γ g, δ (ratGL E a γ * g) = δ g := fun γ g => by
    simp only [hδ, map_mul, GlobalTheory.ShortVecDecay.ideleModule_det_rat, one_mul]
  set T : ℝ := Real.exp 1 ^ (a * Module.finrank ℚ E) with hT
  have hT1 : 1 < T := one_lt_pow₀ (Real.one_lt_exp_iff.2 one_pos) (Nat.mul_pos ha Module.finrank_pos).ne'
  have hδz : ∀ (n : ℤ) g, δ (@GlobalTheory.UnitaryBC.splitCentre E _ _ _ a 1 ^ n * g) = T ^ n * δ g := GlobalTheory.RSTheta.absDet_zpow_mul
  have hc : Continuous fun g => min (δ g) (δ g)⁻¹ := hδc.min (hδc.inv₀ fun g => (hδ0 g).ne')
  refine ⟨hc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
    (.of_forall fun g => le_min (hδ0 g).le (inv_nonneg.2 (hδ0 g).le))).2 ?_⟩
  let φ : (ratGL E a).range × ℤ → latticeGL E a := fun p =>
    ⟨p.1 * @GlobalTheory.UnitaryBC.splitCentre E _ _ _ a 1 ^ p.2, mul_mem (Subgroup.mem_sup_left p.1.2) (zpow_mem_latticeGL _)⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨⟨_, γ, rfl⟩, n⟩ ⟨⟨_, γ', rfl⟩, n'⟩ h
      have h1 : ratGL E a γ * @GlobalTheory.UnitaryBC.splitCentre E _ _ _ a 1 ^ n = ratGL E a γ' * @GlobalTheory.UnitaryBC.splitCentre E _ _ _ a 1 ^ n' := congrArg Subtype.val h
      have h2 := congrArg (fun x => δ (x * 1)) h1
      simp only [mul_assoc, hδr, hδz] at h2
      obtain rfl : n = n' := zpow_right_injective₀ (one_pos.trans hT1) hT1.ne' (mul_right_cancel₀ (hδ0 1).ne' h2)
      exact Prod.ext (Subtype.ext (mul_right_cancel h1)) rfl
    · rintro ⟨g, hg⟩
      obtain ⟨γ, n, rfl⟩ := mem_latticeGL_iff.1 hg
      exact ⟨⟨⟨_, γ, rfl⟩, n⟩, rfl⟩
  haveI : Countable (latticeGL E a) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hd := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom (latticeGL E a) μ
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have h1 : μ (GlobalTheory.AutomorphicL2Unitary.stdDom (latticeGL E a)) ≠ ⊤ := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hd]; exact measure_ne_top _ _
  rw [← GlobalTheory.ThetaUnfold.lintegral_unfold μ (latticeGL E a) (ratGL E a).range (fun n : ℤ => @GlobalTheory.UnitaryBC.splitCentre E _ _ _ a 1 ^ n)
    (Equiv.ofBijective φ hφ) (fun _ => rfl) hd h𝓕 (fun g => ENNReal.ofReal (min (δ g) (δ g)⁻¹))
    (by rintro _ ⟨γ, rfl⟩ g; simp only [hδr])
    hc.measurable.ennreal_ofReal.aemeasurable]
  obtain ⟨B, hB, h⟩ := exists_tsum_min_le hT1
  refine (lintegral_mono (g := fun _ => B) fun g => ?_).trans_lt ?_
  · refine le_of_eq_of_le (tsum_congr fun n => ?_) (h _ (hδ0 g))
    simp only [hδz]
  · rw [setLIntegral_const]
    exact ENNReal.mul_lt_top hB.lt_top h1.lt_top

end GlobalTheory.FinVolGL
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnMinAbsDetInvFundamentalDomainStatement
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_min_absDet_inv_fundamentalDomain : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ), 0 < m →
    ∀ (μ : Measure (GA E m)) [μ.IsHaarMeasure] (𝓕 : Set (GA E m)),
      IsFundamentalDomain (ratGL E m).range 𝓕 μ →
      IntegrableOn (fun h : GA E m => min (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det h) : ℝ)
        (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det h) : ℝ)⁻¹) 𝓕 μ := by
  first | exact @GlobalTheory.FinVolGL.integrableOn_min_absDet | exact GlobalTheory.FinVolGL.integrableOn_min_absDet | (intros; apply GlobalTheory.FinVolGL.integrableOn_min_absDet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MellinTypeIntegralEntireOfRapidDecay
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MellinTypeIntegralEntireOfRapidDecay
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.MellinEntire

lemma min_inv_pos {t : ℝ} (ht : 0 < t) : 0 < min t t⁻¹ := lt_min ht (inv_pos.mpr ht)

lemma min_inv_le_one {t : ℝ} (ht : 0 < t) : min t t⁻¹ ≤ 1 := by
  rcases le_total t 1 with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (inv_le_one_of_one_le₀ h)

lemma le_inv_of_le_one' {t : ℝ} (ht : 0 < t) (h : t ≤ 1) : t ≤ t⁻¹ :=
  h.trans ((one_le_inv₀ ht).mpr h)

lemma inv_le_of_one_le' {t : ℝ} (h : 1 ≤ t) : t⁻¹ ≤ t :=
  (inv_le_one_of_one_le₀ h).trans h

lemma rpow_mul_min_pow_le {t σ : ℝ} {K : ℕ} (ht : 0 < t) (hσ : |σ| ≤ K) :
    t ^ σ * (min t t⁻¹) ^ K ≤ 1 := by
  rcases le_total t 1 with h | h
  · rw [min_eq_left (le_inv_of_le_one' ht h)]
    have h1 : t ^ σ ≤ t ^ (-(K:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge ht h (by linarith [neg_abs_le σ])
    calc t ^ σ * t ^ K ≤ t ^ (-(K:ℝ)) * t ^ K := by gcongr
      _ = 1 := by
        rw [Real.rpow_neg ht.le, Real.rpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ ht.ne')]
  · rw [min_eq_right (inv_le_of_one_le' h)]
    have h1 : t ^ σ ≤ t ^ (K:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h (le_trans (le_abs_self σ) hσ)
    calc t ^ σ * t⁻¹ ^ K ≤ t ^ (K:ℝ) * t⁻¹ ^ K := by gcongr
      _ = 1 := by rw [Real.rpow_natCast, ← mul_pow, mul_inv_cancel₀ ht.ne', one_pow]

lemma min_mul_abs_log_le {t : ℝ} (ht : 0 < t) : min t t⁻¹ * |Real.log t| ≤ 1 := by
  rcases le_total t 1 with h | h
  · rw [min_eq_left (le_inv_of_le_one' ht h)]
    have := Real.abs_log_mul_self_lt t ht h
    rw [abs_mul, abs_of_pos ht] at this
    linarith
  · rw [min_eq_right (inv_le_of_one_le' h)]
    have := Real.abs_log_mul_self_lt t⁻¹ (inv_pos.mpr ht) (inv_le_one_of_one_le₀ h)
    rw [Real.log_inv, abs_mul, abs_neg, abs_of_pos (inv_pos.mpr ht)] at this
    linarith

theorem integrable_and_differentiable {X : Type} [MeasurableSpace X] (ν : Measure X)
    (A : X → ℂ) (T : X → ℝ)
    (hA : AEStronglyMeasurable A ν) (hT : Measurable T) (hTpos : ∀ x, 0 < T x)
    (hw : Integrable (fun x => min (T x) (T x)⁻¹) ν)
    (hdec : ∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C * (min (T x) (T x)⁻¹) ^ N) :
    (∀ s : ℂ, Integrable (fun x => A x * ((T x : ℝ) : ℂ) ^ s) ν) ∧
      Differentiable ℂ (fun s : ℂ => ∫ x, A x * ((T x : ℝ) : ℂ) ^ s ∂ν) := by
  have wpos : ∀ x, 0 < min (T x) (T x)⁻¹ := fun x => min_inv_pos (hTpos x)
  have wle : ∀ x, min (T x) (T x)⁻¹ ≤ 1 := fun x => min_inv_le_one (hTpos x)
  have hTc : Measurable fun x => ((T x : ℝ) : ℂ) := Complex.measurable_ofReal.comp hT
  have meas : ∀ s : ℂ, AEStronglyMeasurable (fun x => A x * ((T x : ℝ) : ℂ) ^ s) ν :=
    fun s => hA.mul (hTc.pow_const s).aestronglyMeasurable
  have bnd : ∀ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x (s : ℂ), |s.re| ≤ K →
      ‖A x * ((T x : ℝ) : ℂ) ^ s‖ ≤ C * (min (T x) (T x)⁻¹) ^ 2 := by
    intro K
    obtain ⟨C, hC⟩ := hdec (K + 2)
    refine ⟨|C|, abs_nonneg _, fun x s hs => ?_⟩
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hTpos x)]
    have hA' : ‖A x‖ ≤ |C| * (min (T x) (T x)⁻¹) ^ (K + 2) :=
      (hC x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (wpos x).le _))
    have h2 := rpow_mul_min_pow_le (hTpos x) hs
    have h0 : 0 ≤ T x ^ s.re := Real.rpow_nonneg (hTpos x).le _
    calc ‖A x‖ * T x ^ s.re ≤ |C| * (min (T x) (T x)⁻¹) ^ (K + 2) * T x ^ s.re :=
          mul_le_mul_of_nonneg_right hA' h0
      _ = |C| * (min (T x) (T x)⁻¹) ^ 2 * (T x ^ s.re * (min (T x) (T x)⁻¹) ^ K) := by ring
      _ ≤ |C| * (min (T x) (T x)⁻¹) ^ 2 * 1 := by
          gcongr
      _ = |C| * (min (T x) (T x)⁻¹) ^ 2 := mul_one _
  have sq_le : ∀ x, (min (T x) (T x)⁻¹) ^ 2 ≤ min (T x) (T x)⁻¹ := fun x => by
    nlinarith [wpos x, wle x]
  refine ⟨fun s => ?_, fun s₀ => ?_⟩
  · obtain ⟨C, hC0, hC⟩ := bnd ⌈|s.re|⌉₊
    refine Integrable.mono' (hw.const_mul C) (meas s) (ae_of_all _ fun x => ?_)
    exact (hC x s (Nat.le_ceil _)).trans (mul_le_mul_of_nonneg_left (sq_le x) hC0)
  · obtain ⟨C, hC0, hC⟩ := bnd (⌈|s₀.re|⌉₊ + 1)
    have hre : ∀ s ∈ Metric.ball s₀ 1, |s.re| ≤ ((⌈|s₀.re|⌉₊ + 1 : ℕ) : ℝ) := by
      intro s hs
      rw [Metric.mem_ball, dist_eq_norm] at hs
      have h1 : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
        rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
      have h2 : |s.re| ≤ |s₀.re| + |s.re - s₀.re| := by
        have := abs_add_le s₀.re (s.re - s₀.re); simpa using this
      have h3 := Nat.le_ceil |s₀.re|
      push_cast
      linarith
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
      (F := fun s x => A x * ((T x : ℝ) : ℂ) ^ s)
      (F' := fun s x => A x * (((T x : ℝ) : ℂ) ^ s * Complex.log ((T x : ℝ) : ℂ)))
      (x₀ := s₀) (bound := fun x => C * min (T x) (T x)⁻¹) (s := Metric.ball s₀ 1) (Metric.ball_mem_nhds s₀ one_pos)
      (Filter.Eventually.of_forall fun s => meas s) ((fun s => ?_ : ∀ s : ℂ,
        Integrable (fun x => A x * ((T x : ℝ) : ℂ) ^ s) ν) s₀)
      (hA.mul ((hTc.pow_const s₀).mul (Complex.measurable_log.comp hTc)).aestronglyMeasurable)
      (ae_of_all _ fun x s hs => ?_) (hw.const_mul C)
      (ae_of_all _ fun x s _ => ?_)
    · exact key.2.differentiableAt
    · obtain ⟨C', hC0', hC'⟩ := bnd ⌈|s.re|⌉₊
      refine Integrable.mono' (hw.const_mul C') (meas s) (ae_of_all _ fun x => ?_)
      exact (hC' x s (Nat.le_ceil _)).trans (mul_le_mul_of_nonneg_left (sq_le x) hC0')
    · show ‖A x * (((T x : ℝ) : ℂ) ^ s * Complex.log ((T x : ℝ) : ℂ))‖ ≤ C * min (T x) (T x)⁻¹
      rw [← mul_assoc, norm_mul, ← Complex.ofReal_log (hTpos x).le, Complex.norm_real,
        Real.norm_eq_abs]
      have h1 := hC x s (hre s hs)
      have h2 := min_mul_abs_log_le (hTpos x)
      calc ‖A x * ((T x : ℝ) : ℂ) ^ s‖ * |Real.log (T x)|
          ≤ C * (min (T x) (T x)⁻¹) ^ 2 * |Real.log (T x)| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = C * min (T x) (T x)⁻¹ * (min (T x) (T x)⁻¹ * |Real.log (T x)|) := by ring
        _ ≤ C * min (T x) (T x)⁻¹ * 1 := by
            gcongr
            exact mul_nonneg hC0 (wpos x).le
        _ = C * min (T x) (T x)⁻¹ := mul_one _
    · have hne : ((T x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hTpos x).ne'
      exact (Complex.hasStrictDerivAt_const_cpow (Or.inl hne)).hasDerivAt.const_mul (A x)

end GlobalTheory.MellinEntire
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MellinTypeIntegralEntireOfRapidDecayStatement
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mellinType_integral_entire_of_rapid_decay : ∀ {X : Type} [MeasurableSpace X] (ν : Measure X) (A : X → ℂ) (T : X → ℝ),
    AEStronglyMeasurable A ν → Measurable T → (∀ x, 0 < T x) → Integrable (fun x => min (T x) (T x)⁻¹) ν →
    (∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C * (min (T x) (T x)⁻¹) ^ N) →
    (∀ s : ℂ, Integrable (fun x => A x * ((T x : ℝ) : ℂ) ^ s) ν) ∧
      Differentiable ℂ (fun s : ℂ => ∫ x, A x * ((T x : ℝ) : ℂ) ^ s ∂ν) := by
  first | exact @GlobalTheory.MellinEntire.integrable_and_differentiable | exact GlobalTheory.MellinEntire.integrable_and_differentiable | (intros; apply GlobalTheory.MellinEntire.integrable_and_differentiable <;> assumption)
end
end

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.ShortVecDecay

namespace GlobalTheory.RSnm

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem invT_invT (g : GA E a) : invT a (Ad E) (invT a (Ad E) g) = g :=
  Units.ext (by change ((g.val)ᵀ)ᵀ = g.val; exact transpose_transpose _)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_invT : Continuous (invT a (Ad E)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · change Continuous fun g : GA E a => ((g⁻¹ : GA E a).val)ᵀ
    exact (Units.continuous_val.comp continuous_inv).matrix_transpose
  · change Continuous fun g : GA E a => (g.val)ᵀ
    exact Units.continuous_val.matrix_transpose

theorem bounded_of_decays (ha : 0 < a) {F : GA E a → ℂ} (hF : Decays F) : ∃ C, ∀ g, ‖F g‖ ≤ C := by
  obtain ⟨C, hC⟩ := hF (Set.univ.pi fun _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)))
    (isCompact_univ_pi fun _ => GroundTheory.Global.isCompact_integralFiniteAdeles E) {1} isCompact_singleton 0
  refine ⟨C, fun g => ?_⟩
  set e : Fin a → E := Pi.single ⟨0, ha⟩ 1
  obtain ⟨d, hd, hmem⟩ := GlobalTheory.AdelicMatLat.exists_nat_mul_mem_family E
    (fun i => pFin E (((fun j => algebraMap E (Ad E) (e j)) ᵥ* g.val) i))
  have hξ : (fun j => (d : E) * e j) ≠ 0 := by
    intro h
    have := congrFun h ⟨0, ha⟩
    simp [e] at this
    omega
  have key := hC g 1 rfl (fun j => (d : E) * e j) hξ (fun i _ => by
    have h1 : pFin E (((fun j => algebraMap E (Ad E) ((d : E) * e j)) ᵥ* g.val) i) =
        (d : Af E) * pFin E (((fun j => algebraMap E (Ad E) (e j)) ᵥ* g.val) i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [vecMul, dotProduct, map_mul, map_natCast, Finset.mul_sum, map_sum, mul_assoc]
    show pFin E _ ∈ _
    rw [h1]
    exact hmem i)
  simpa using key

theorem decays_smoothInf_invT {F : GA E a → ℂ} (hF : Decays fun g => F (invT a (Ad E) g)) {f : Lie E a → ℂ}
    (hf : Continuous f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ invSet E a) :
    Decays fun g => GlobalTheory.JSW.smoothInf f F (invT a (Ad E) g) := by
  intro L hL C₀ hC₀ N
  have hK : IsCompact ((fun y : GL (Fin a) (Cinf E) => toL y.val) ⁻¹' tsupport f) :=
    GlobalTheory.CuspQuot.isOpenEmbedding_val.isInducing.isCompact_preimage' hc fun x hx => hs hx
  obtain ⟨C, h⟩ := hF L hL _ (hC₀.mul ((hK.image GlobalTheory.CuspQuot.continuous_infGL).image continuous_invT)) N
  haveI : IsFiniteMeasureOnCompacts (volume : Measure (Lie E a)) :=
    MeasureTheory.Measure.pi.isFiniteMeasureOnCompacts _
  have hi : Integrable f := hf.integrable_of_hasCompactSupport hc
  refine ⟨(∫ x, ‖f x‖) * C, fun g c hcC ξ hξ hm => ?_⟩
  rw [mul_assoc, ← integral_mul_const]
  refine norm_integral_le_of_norm_le (hi.norm.mul_const _) (.of_forall fun x => ?_)
  by_cases hx : x ∈ tsupport f
  · obtain ⟨u, hu⟩ := hs hx
    obtain rfl : x = toL u.val := hu.symm
    rw [norm_mul, chart_val]
    have e : invT a (Ad E) (g * c) * infGL E a u =
        invT a (Ad E) (g * (c * invT a (Ad E) (infGL E a u))) := by
      rw [map_mul, map_mul, map_mul, invT_invT, mul_assoc]
    rw [e]
    exact mul_le_mul_of_nonneg_left (h g _ (Set.mul_mem_mul hcC ⟨_, ⟨u, hx, rfl⟩, rfl⟩) ξ hξ hm) (norm_nonneg _)
  · simp [image_eq_zero_of_notMem_tsupport hx]


variable (a) in
def goodFns : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | Continuous F ∧ Decays F ∧ Decays fun g => F (invT a (Ad E) g)}
  zero_mem' := ⟨continuous_const, Decays.zero, Decays.zero⟩
  add_mem' := fun h h' => ⟨h.1.add h'.1, h.2.1.add h'.2.1, h.2.2.add h'.2.2⟩
  smul_mem' := fun z _ h => ⟨h.1.const_smul z, h.2.1.smul z, h.2.2.smul z⟩

theorem mem_goodFns (ha : 0 < a) {π : CuspSub E a} (hπ : π.IsUnitary) {F : GA E a → ℂ}
    (hF : F ∈ π.V.map (Sm E a).subtype ⊔ GlobalTheory.JSW.smoothSpan π) : F ∈ goodFns a := by
  have hV : ∀ φ ∈ π.V, φ.1 ∈ goodFns (E := E) a := fun φ hφ =>
    ⟨ContAut.continuous_of_isOpen_stab E a φ (π.cusp φ hφ).1.level, decays_of_mem hπ hφ,
      decays_of_mem hπ.contra (show UpperTheory.V.TC.dualFn E a φ ∈ π.contra.V from ⟨φ, hφ, rfl⟩)⟩
  refine (sup_le ?_ (Submodule.span_le.2 ?_) : _ ≤ goodFns a) hF
  · rintro _ ⟨φ, hφ, rfl⟩
    exact hV φ hφ
  · rintro _ ⟨f, φ, hf, hφ, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hV φ hφ
    obtain ⟨C, hC⟩ := bounded_of_decays ha h2
    exact ⟨(GlobalTheory.CuspQuot.continuous_smoothing (volume : Measure (Lie E a)) ⟨hf.1, hf.2⟩ h1 hC :),
      h2.smoothInf hf.1.continuous hf.2.1 hf.2.2, decays_smoothInf_invT h3 hf.1.continuous hf.2.1 hf.2.2⟩

end GlobalTheory.RSnm

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.ShortVecDecay
open GroundTheory.Automorphic.FourierWhittaker (colGL uMat uMat_apply colX colX_apply coe_uGL blockGL blockMat blockMat_apply
  coe_blockGL partialCoeff stepCoeff vecCoeff vecDomain vecMeasure det_uMat)

namespace GlobalTheory.RSnm

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a n m : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem mul_apply_of_row {R : Type} [CommRing R] {A B : Matrix (Fin n) (Fin n) R} {j : Fin n}
    (hA : ∀ t, A j t = (1 : Matrix (Fin n) (Fin n) R) j t) (l : Fin n) : (A * B) j l = B j l := by
  rw [Matrix.mul_apply, ← one_mul B, Matrix.mul_apply]
  simp only [hA, one_mul]


omit [_root_.NumberField.IsTotallyComplex E] in
theorem mul_apply_of_col {R : Type} [CommRing R] {A B : Matrix (Fin n) (Fin n) R} {l : Fin n}
    (hB : ∀ t, B t l = (1 : Matrix (Fin n) (Fin n) R) t l) (i : Fin n) : (A * B) i l = A i l := by
  rw [Matrix.mul_apply]
  simp only [hB]
  rw [← Matrix.mul_apply, mul_one]


omit [_root_.NumberField.IsTotallyComplex E] in
theorem colGL_row_last {R : Type} [CommRing R] (k : ℕ) (y : Fin k → R) {j : Fin n} (hj : j.val + 1 = n) (t : Fin n) :
    (colGL (n := n) k y : Matrix (Fin n) (Fin n) R) j t = (1 : Matrix (Fin n) (Fin n) R) j t := by
  rw [colGL, coe_uGL, uMat_apply, Matrix.one_apply]
  split_ifs with h1 h2
  · rfl
  · exact absurd h2 (by rw [Fin.lt_def]; omega)
  · rfl


omit [_root_.NumberField.IsTotallyComplex E] in
theorem colGL_col {R : Type} [CommRing R] {k : ℕ} (hk : k ≠ m) (y : Fin k → R) {l : Fin n} (hl : l.val = m)
    (i : Fin n) : (colGL (n := n) k y : Matrix (Fin n) (Fin n) R) i l = (1 : Matrix (Fin n) (Fin n) R) i l := by
  rw [colGL, coe_uGL, uMat_apply, Matrix.one_apply]
  split_ifs with h1 h2
  · rfl
  · rw [colX_apply, dite_eq_right (by simp only; omega)]
  · rfl

omit [_root_.NumberField.IsTotallyComplex E] in
theorem blockGL_row_last {R : Type} [CommRing R] (hmn : m < n) (h : GL (Fin m) R) {j : Fin n} (hj : j.val + 1 = n)
    (t : Fin n) : (blockGL hmn.le h : Matrix (Fin n) (Fin n) R) j t = (1 : Matrix (Fin n) (Fin n) R) j t := by
  rw [coe_blockGL, blockMat_apply, dite_eq_right (by omega), Matrix.one_apply]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem blockGL_col {R : Type} [CommRing R] (hmn : m < n) (h : GL (Fin m) R) {l : Fin n} (hl : l.val = m)
    (i : Fin n) : (blockGL hmn.le h : Matrix (Fin n) (Fin n) R) i l = (1 : Matrix (Fin n) (Fin n) R) i l := by
  rw [coe_blockGL, blockMat_apply, Matrix.one_apply]
  split_ifs with h1 h2 h3 <;> first | rfl | omega | (subst h3; omega)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem det_colGL {R : Type} [CommRing R] (k : ℕ) (y : Fin k → R) :
    GeneralLinearGroup.det (colGL (n := n) k y) = 1 :=
  Units.ext (by rw [GeneralLinearGroup.val_det_apply, colGL, coe_uGL, det_uMat, Units.val_one])

omit [_root_.NumberField.IsTotallyComplex E] in
theorem det_blockGL {R : Type} [CommRing R] (hmn : m ≤ n) (h : GL (Fin m) R) :
    GeneralLinearGroup.det (blockGL hmn h) = GeneralLinearGroup.det h := by
  refine Units.ext ?_
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply, coe_blockGL, blockMat,
    det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, mul_one]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_blockGL (hmn : m ≤ n) : Continuous fun h : GA E m => (blockGL hmn h : GA E n) := by
  have hc : ∀ M : GA E m → Matrix (Fin m) (Fin m) (Ad E), Continuous M →
      Continuous fun h => blockMat (n := n) hmn (M h) := fun M hM => by
    refine continuous_matrix fun a b => ?_
    simp only [blockMat_apply]
    split_ifs
    · exact hM.matrix_elem _ _
    all_goals exact continuous_const
  refine Units.continuous_iff.2 ⟨hc _ Units.continuous_val, ?_⟩
  have e : (fun h : GA E m => ((blockGL hmn h)⁻¹ : GA E n).val) = fun h => blockMat hmn (h⁻¹ : GA E m).val := by
    funext h; rw [← map_inv, coe_blockGL]
  rw [e]
  exact hc _ (Units.continuous_val.comp continuous_inv)

end GlobalTheory.RSnm

namespace GlobalTheory.RSnm

open GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a n m : ℕ}

def detAbs (g : GA E a) : ℝ := (ideleModule E (GeneralLinearGroup.det g) : ℝ)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem detAbs_pos (g : GA E a) : 0 < detAbs g := (ideleModule E _).2

omit [_root_.NumberField.IsTotallyComplex E] in
theorem detAbs_mul (g h : GA E a) : detAbs (g * h) = detAbs g * detAbs h := by
  simp only [detAbs, map_mul, Positive.val_mul]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_detAbs : Continuous (detAbs (E := E) (a := a)) :=
  continuous_subtype_val.comp (continuous_ideleModule.comp (AdelicGLn.continuous_det E a))

theorem detAbs_invT (g : GA E a) : detAbs (invT a (Ad E) g) = (detAbs g)⁻¹ := by
  have h : GeneralLinearGroup.det (invT a (Ad E) g) = (GeneralLinearGroup.det g)⁻¹ := by
    refine Units.ext ?_
    rw [GeneralLinearGroup.val_det_apply, invT_val_eq, det_nonsing_inv, det_transpose,
      ← GeneralLinearGroup.val_det_apply, Ring.inverse_unit]
  rw [detAbs, h, map_inv, Positive.coe_inv]
  rfl

omit [_root_.NumberField.IsTotallyComplex E] in
theorem detAbs_colGL (k : ℕ) (y : Fin k → Ad E) : detAbs (colGL (n := a) k y) = 1 := by
  rw [detAbs, det_colGL, map_one]; rfl

omit [_root_.NumberField.IsTotallyComplex E] in
theorem detAbs_blockGL (hmn : m ≤ n) (h : GA E m) : detAbs (blockGL hmn h : GA E n) = detAbs h := by
  rw [detAbs, detAbs, det_blockGL]


variable (m) in
def InS (g : GA E n) : Prop :=
  (∀ j t : Fin n, j.val + 1 = n → g.val j t = (1 : Matrix (Fin n) (Fin n) (Ad E)) j t) ∧
    ∀ i l : Fin n, l.val = m → g.val i l = (1 : Matrix (Fin n) (Fin n) (Ad E)) i l

theorem single_vecMul_eq (j : Fin n) (M : Matrix (Fin n) (Fin n) (Ad E)) :
    (fun i => algebraMap E (Ad E) ((Pi.single j 1 : Fin n → E) i)) ᵥ* M = fun t => M j t := by
  have : (fun i => algebraMap E (Ad E) ((Pi.single j 1 : Fin n → E) i)) = Pi.single j 1 := by
    funext i; by_cases h : i = j
    · subst h; simp
    · simp [h]
  rw [this, single_one_vecMul]
  rfl

theorem norm_le_of_inS (hmn : m < n) {φ : GA E n → ℂ} (hφ : φ ∈ goodFns n) {L : Set (Fin m → Af E)}
    (hL : IsCompact L) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GA E n, InS m g → ∀ x : Fin m → Ad E, (fun i => pFin E (x i)) ∈ L →
      ‖φ (g * colGL m x)‖ ≤
        C * (1 + ‖fun i => pInf E (x i)‖) ^ (n * Module.finrank ℚ E * N) * (min (detAbs g) (detAbs g)⁻¹) ^ N := by
  set last : Fin n := ⟨n - 1, by omega⟩
  set mm : Fin n := ⟨m, hmn⟩
  set d := n * Module.finrank ℚ E
  set r : Fin n → Ad E := fun t => (1 : Matrix (Fin n) (Fin n) (Ad E)) last t
  set Φ : (Fin m → Af E) → (Fin n → Af E) := fun v t => if t = mm then 1 else if h : t.val < m then -v ⟨t, h⟩ else 0
  have hΦ : Continuous Φ := continuous_pi fun t => by
    simp only [Φ]
    split_ifs
    · exact continuous_const
    · exact (continuous_apply _).neg
    · exact continuous_const
  obtain ⟨C₁, h₁⟩ := hφ.2.1 {fun i => pFin E (r i)} isCompact_singleton {1} isCompact_singleton N
  obtain ⟨C₂, h₂⟩ := hφ.2.2 (Φ '' L) (hL.image hΦ) {1} isCompact_singleton N
  refine ⟨max (max C₁ C₂) 0, le_max_right _ _, fun g hg x hx => ?_⟩
  set T := detAbs g
  have hT : 0 < T := detAbs_pos g
  set X := ‖fun i => pInf E (x i)‖
  have hX : 0 ≤ X := norm_nonneg _
  set u := (colGL (n := n) m x : GA E n)
  have hTu : detAbs (g * u) = T := by rw [detAbs_mul, detAbs_colGL, mul_one]

  have hrow : (fun i => algebraMap E (Ad E) ((Pi.single last 1 : Fin n → E) i)) ᵥ* (g * u).val = r := by
    rw [single_vecMul_eq]
    funext t
    rw [Units.val_mul, mul_apply_of_row (fun t => hg.1 last t (by simp only [last]; omega))]
    exact colGL_row_last m x (by simp only [last]; omega) t
  have hne1 : (Pi.single last 1 : Fin n → E) ≠ 0 := fun h => by simpa using congrFun h last
  have b1 := h₁ (g * u) 1 rfl _ hne1 (by rw [hrow]; rfl)
  rw [mul_one, hrow] at b1
  change ‖φ (g * u)‖ ≤ C₁ * (_ / detAbs (g * u)) ^ N at b1
  rw [hTu] at b1
  have hr : ‖fun i => pInf E (r i)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun t => ?_
    simp only [r, Matrix.one_apply]
    split_ifs
    · rw [map_one]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => by simp
    · simp
  have b1' : ‖φ (g * u)‖ ≤ max (max C₁ C₂) 0 * T⁻¹ ^ N := by
    refine b1.trans ?_
    have e1 : (‖fun i => pInf E (r i)‖ ^ d / T) ^ N ≤ T⁻¹ ^ N := by
      refine pow_le_pow_left₀ (by positivity) ?_ N
      rw [div_eq_mul_inv]
      exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ (norm_nonneg _) hr)
    calc C₁ * (‖fun i => pInf E (r i)‖ ^ d / T) ^ N ≤ max (max C₁ C₂) 0 * (‖fun i => pInf E (r i)‖ ^ d / T) ^ N :=
          mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_left _ _)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left e1 (le_max_right _ _)

  set w : Fin n → Ad E := fun t => ((colGL (n := n) m (-x) : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) t mm
  have hginv : ∀ t, ((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) t mm = (1 : Matrix (Fin n) (Fin n) (Ad E)) t mm := by
    intro t
    have := mul_apply_of_col (A := ((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E))) (B := g.val) (l := mm)
      (fun t => hg.2 t mm rfl) t
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one] at this
    exact this.symm
  have hcol : (fun i => algebraMap E (Ad E) ((Pi.single mm 1 : Fin n → E) i)) ᵥ* (invT n (Ad E) (g * u)).val = w := by
    rw [single_vecMul_eq]
    funext t
    change (((g * u)⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E))ᵀ mm t = _
    rw [transpose_apply, _root_.mul_inv_rev, Units.val_mul, mul_apply_of_col hginv]
    simp only [w, u]
    rw [← GroundTheory.Automorphic.FourierWhittaker.colGL_neg]
  have hne2 : (Pi.single mm 1 : Fin n → E) ≠ 0 := fun h => by simpa using congrFun h mm
  have hmm : mm.val = m := rfl
  have hw : (fun t => pFin E (w t)) = Φ fun i => pFin E (x i) := by
    funext t
    simp only [w, Φ, colGL, coe_uGL, uMat_apply, colX_apply]
    split_ifs <;> first | (simp; done) | (exfalso; simp only [Fin.lt_def] at *; omega) | (simp only [Fin.lt_def] at *; omega)
  have b2 := h₂ (invT n (Ad E) (g * u)) 1 rfl _ hne2 (by rw [hcol, hw]; exact ⟨_, hx, rfl⟩)
  rw [mul_one, hcol] at b2
  change ‖φ (invT n (Ad E) (invT n (Ad E) (g * u)))‖ ≤ C₂ * (_ / detAbs (invT n (Ad E) (g * u))) ^ N at b2
  rw [invT_invT, detAbs_invT, hTu] at b2
  have hw' : ‖fun t => pInf E (w t)‖ ≤ 1 + X := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun t => ?_
    simp only [w, colGL, coe_uGL, uMat_apply, colX_apply]
    split_ifs with h1 h2 h3
    · rw [map_one]
      exact ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => by simp).trans (le_add_of_nonneg_right hX)
    · rw [Pi.neg_apply, map_neg, norm_neg]
      exact (norm_le_pi_norm (fun i => pInf E (x i)) _).trans (le_add_of_nonneg_left zero_le_one)
    · simp only [map_zero, norm_zero]; positivity
  have b2' : ‖φ (g * u)‖ ≤ max (max C₁ C₂) 0 * (1 + X) ^ (d * N) * T ^ N := by
    refine b2.trans ?_
    have e2 : (‖fun t => pInf E (w t)‖ ^ d / T⁻¹) ^ N ≤ (1 + X) ^ (d * N) * T ^ N := by
      rw [div_inv_eq_mul, mul_pow, ← pow_mul]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hw' _) (by positivity)
    calc C₂ * (‖fun t => pInf E (w t)‖ ^ d / T⁻¹) ^ N ≤ max (max C₁ C₂) 0 * (‖fun t => pInf E (w t)‖ ^ d / T⁻¹) ^ N :=
          mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_right _ _)) (by positivity)
      _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left e2 (le_max_right _ _)
  have hX1 : 1 ≤ (1 + X) ^ (d * N) := one_le_pow₀ (le_add_of_nonneg_right hX)
  rcases le_total T 1 with hT1 | hT1
  · rw [min_eq_left (hT1.trans ((one_le_inv₀ hT).mpr hT1))]
    exact b2'
  · rw [min_eq_right (by exact (inv_le_one_of_one_le₀ hT1).trans hT1)]
    refine b1'.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
    exact le_mul_of_one_le_left (by positivity) hX1

end GlobalTheory.RSnm

namespace GlobalTheory.RSnm

open GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff_self partialCoeff_of_lt continuous_partialCoeff continuous_colGL
  vecMeasure_vecDomain measurableSet_vecDomain)

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a n m : ℕ}

theorem inS_colGL_mul {k : ℕ} (hk : k ≠ m) (y : Fin k → Ad E) {g : GA E n} (hg : InS m g) :
    InS m (colGL (n := n) k y * g) := by
  refine ⟨fun j t hj => ?_, fun i l hl => ?_⟩
  · rw [Units.val_mul, mul_apply_of_row (fun t => colGL_row_last k y hj t)]
    exact hg.1 j t hj
  · rw [Units.val_mul, mul_apply_of_col (fun t => hg.2 t l hl)]
    exact colGL_col hk y hl i

theorem inS_blockGL (hmn : m < n) (h : GA E m) : InS m (blockGL hmn.le h : GA E n) :=
  ⟨fun j t hj => blockGL_row_last hmn h hj t, fun i l hl => blockGL_col hmn h hl i⟩


variable (m) in
def colSmooth (F : (Fin m → Ad E) → ℂ) (φ : GA E n → ℂ) (g : GA E n) : ℂ :=
  ∫ x, F x * φ (g * colGL m x) ∂GJMatrix.adeleMeasurePi E

set_option synthInstance.maxHeartbeats 200000 in
theorem continuous_colSmooth {F : (Fin m → Ad E) → ℂ} (hF : F ∈ GJMatrix.schwartzBruhatPi (K := E) (ι := Fin m))
    {φ : GA E n → ℂ} (hc : Continuous φ) {C : ℝ} (hC : ∀ g, ‖φ g‖ ≤ C) : Continuous (colSmooth m F φ) :=
  continuous_of_dominated (bound := fun x => ‖F x‖ * C)
    (fun g => ((GJMatrix.continuous_of_mem_schwartzBruhatPi hF).mul
      (hc.comp (continuous_const.mul (continuous_colGL m)))).aestronglyMeasurable)
    (fun g => .of_forall fun x => (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)))
    ((GJMatrix.integrable_of_mem_schwartzBruhatPi hF).norm.mul_const C)
    (.of_forall fun x => continuous_const.mul (hc.comp (continuous_id.mul continuous_const)))

theorem colSmooth_bound (hmn : m < n) {φ : GA E n → ℂ} (hφ : φ ∈ goodFns n) {F : (Fin m → Ad E) → ℂ}
    (hF : F ∈ GJMatrix.schwartzBruhatPi (K := E) (ι := Fin m)) (N : ℕ) :
    ∃ C : ℝ, ∀ g, InS m g → ‖colSmooth m F φ g‖ ≤ C * (min (detAbs g) (detAbs g)⁻¹) ^ N := by
  obtain ⟨⟨L, hL, hsupp⟩, hint⟩ := GlobalTheory.T.schwartz_bruhat_integrable_moments E m F hF
  obtain ⟨C, hC0, hC⟩ := norm_le_of_inS hmn hφ hL N
  set k := n * Module.finrank ℚ E * N
  refine ⟨C * ∫ x, ‖F x‖ * (1 + ‖fun i => pInf E (x i)‖) ^ k ∂GJMatrix.adeleMeasurePi E, fun g hg => ?_⟩
  set W := (min (detAbs g) (detAbs g)⁻¹) ^ N
  have hW : 0 ≤ W := pow_nonneg (le_min (detAbs_pos g).le (inv_nonneg.2 (detAbs_pos g).le)) N
  refine (norm_integral_le_of_norm_le ((hint k).mul_const (C * W)) (.of_forall fun x => ?_)).trans_eq ?_
  · rw [norm_mul]
    by_cases hx : F x = 0
    · rw [hx, norm_zero, zero_mul, zero_mul, zero_mul]
    · rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ((hC g hg x (hsupp x hx)).trans_eq ?_) (norm_nonneg _)
      ring
  · rw [integral_mul_const]
    ring

theorem partialCoeff_bound (hmn : m < n) {G : GA E n → ℂ} {b : ℝ → ℝ}
    (hG : ∀ g, InS m g → ‖G g‖ ≤ b (detAbs g)) :
    ∀ i j, j + i = n → m + 1 ≤ j → ∀ g, InS m g → ‖partialCoeff G j g‖ ≤ b (detAbs g) := by
  intro i
  induction i with
  | zero =>
    intro j hj _ g hg
    rw [add_zero] at hj
    subst hj
    rw [partialCoeff_self]
    exact hG g hg
  | succ i ih =>
    intro j hj hmj g hg
    have hjn : j < n := by omega
    rw [partialCoeff_of_lt G hjn]
    have hb : 0 ≤ b (detAbs g) := (norm_nonneg _).trans (hG g hg)
    refine (norm_setIntegral_le_of_norm_le_const (C := b (detAbs g)) (by rw [vecMeasure_vecDomain]; exact ENNReal.one_lt_top)
      fun x _ => ?_).trans_eq ?_
    · rw [norm_mul, Circle.norm_coe, mul_one]
      have := ih (j + 1) (by omega) (by omega) _ (inS_colGL_mul (by omega) x hg)
      rwa [detAbs_mul, detAbs_colGL, one_mul] at this
    · rw [measureReal_def, vecMeasure_vecDomain, ENNReal.toReal_one, mul_one]

end GlobalTheory.RSnm

namespace GlobalTheory.RSnm

open GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic.FourierWhittaker (continuous_partialCoeff)
open scoped ComplexConjugate nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n m : ℕ}


variable (m) in
def rsIntegrand (hmn : m ≤ n) (F : (Fin m → Ad E) → ℂ) (φ : GA E n → ℂ) (φ' : GA E m → ℂ) (s : ℂ) (h : GA E m) : ℂ :=
  FourierWhittaker.partialCoeff (colSmooth m F φ) (m + 1) (blockGL hmn h) * conj (φ' h) *
    ((detAbs h : ℝ) : ℂ) ^ (s - ((n : ℂ) - m) / 2)

end GlobalTheory.RSnm
