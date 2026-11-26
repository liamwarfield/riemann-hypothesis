module

public import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero

@[expose] public section

section -- merged from ReciprocityTheory.L2DbarEstimates.Localization.Primed
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem primed_lintegral_sq_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (a F G : α → ℝ≥0∞) (hF : AEMeasurable F μ) (hG : AEMeasurable G μ)
    (h : ∀ x, a x ^ 2 ≤ F x * G x) :
    (∫⁻ x, a x ∂μ) ^ 2 ≤ (∫⁻ x, F x ∂μ) * ∫⁻ x, G x ∂μ := by
  have hpt : ∀ x, a x ≤ F x ^ (1 / 2 : ℝ) * G x ^ (1 / 2 : ℝ) := by
    intro x
    calc a x = (a x ^ 2) ^ (1 / 2 : ℝ) := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
      _ ≤ (F x * G x) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow (h x) (by norm_num)
      _ = F x ^ (1 / 2 : ℝ) * G x ^ (1 / 2 : ℝ) := ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (hF.pow_const (1 / 2 : ℝ)) (hG.pow_const (1 / 2 : ℝ))
  have hsq : ∀ y : ℝ≥0∞, (y ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = y := by
    intro y; rw [← ENNReal.rpow_mul]; norm_num
  simp only [hsq, Pi.mul_apply] at hH
  have hle : ∫⁻ x, a x ∂μ ≤ (∫⁻ x, F x ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ x, G x ∂μ) ^ (1 / 2 : ℝ) :=
    (lintegral_mono hpt).trans hH
  calc (∫⁻ x, a x ∂μ) ^ 2
      ≤ ((∫⁻ x, F x ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ x, G x ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = (∫⁻ x, F x ∂μ) * ∫⁻ x, G x ∂μ := by
      rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (n := 2),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      norm_num

theorem primed_ofReal_integral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) : ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hm : AEStronglyMeasurable f μ
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf) hm]
    exact ENNReal.ofReal_toReal_le
  · rw [integral_non_aestronglyMeasurable hm]
    simp

theorem primed_inner_norm (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n) (F0 : M → ℂ)
    (g : M → V n) (x : M) :
    ‖⟪dbarF n z F0 x, g x⟫_ℂ‖ = ‖dbarDot n z F0 x (fun j => g x j)‖ := by
  have : ⟪dbarF n z F0 x, g x⟫_ℂ = starRingEnd ℂ (dbarDot n z F0 x (fun j => g x j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [dbarF, dbarDot, PiLp.inner_apply, map_sum, mul_comm]
  rw [this, Complex.norm_conj]

theorem primedIneq (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hAP : APStatement n M) : PrimedIneqStatement n M := by
  intro z hz ph ph' ψ F0 h ε hph hlev hph' hψ hF0 hh hdom hε hpp hlevi hA g hg
  have cR : ∀ f : M → ℝ, SmoothR n z f → Continuous f := fun f hf => by
    exact (Complex.continuous_re.comp (Smooth.continuous n z hz _ hf)).congr fun x => by simp
  have cph' := cR ph' hph'
  have cψ := cR ψ hψ
  have cg : ∀ j, Continuous fun x => g x j := fun j => Ck.continuous n z hz 2 _ (hg j).1
  have cLevi : ∀ q : M → ℝ, SmoothR n z q →
      Continuous fun x => (Levi n z q x (fun j => g x j)).re := by
    intro q hq
    refine Complex.continuous_re.comp ?_
    unfold Levi
    refine continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ => ?_
    exact ((Smooth.continuous n z hz _ (Smooth.d n z j _ (Smooth.db n z k _ hq))).mul
      (cg j)).mul (Complex.continuous_conj.comp (cg k))
  have cdS : Continuous fun x => dSqR n z ψ x := by
    unfold dSqR
    exact continuous_finsetSum _ fun j _ =>
      ((Smooth.continuous n z hz _ (Smooth.d n z j _ hψ)).norm.pow 2)
  have hnorm : ∀ x, ‖g x‖ ^ 2 = ∑ j, ‖g x j‖ ^ 2 := fun x => EuclideanSpace.norm_sq_eq (g x)
  have cgn : Continuous fun x => ‖g x‖ ^ 2 := by
    simp_rw [hnorm]; exact continuous_finsetSum _ fun j _ => (cg j).norm.pow 2
  have hKc : IsCompact (⋃ j, tsupport (fun x => g x j)) :=
    isCompact_iUnion fun j => (hg j).2
  have hgK : ∀ x, x ∉ (⋃ j, tsupport (fun x => g x j)) → g x = 0 := by
    intro x hx
    simp only [mem_iUnion, not_exists] at hx
    ext j
    exact image_eq_zero_of_notMem_tsupport (f := fun x => g x j) (hx j)
  set Q : M → ℝ := fun x => ((Levi n z ph' x (fun j => g x j)).re -
      (1 + 1 / ε) * dSqR n z ψ x * ‖g x‖ ^ 2) * Real.exp (-ph' x) with hQ
  have cQ : Continuous Q := ((cLevi ph' hph').sub ((continuous_const.mul cdS).mul cgn)).mul
    (Real.continuous_exp.comp cph'.neg)
  have sQ : HasCompactSupport Q := HasCompactSupport.intro hKc fun x hx => by
    simp [hQ, hgK x hx, Levi]
  have iQ : Integrable Q (vol n z) := integrable_of_continuous_real n z hz Q cQ sQ
  have hL0 : ∀ x, 0 ≤ (Levi n z ph x (fun j => g x j)).re := fun x => hlev x _
  have hLQ : ∀ x, (Levi n z ph x (fun j => g x j)).re * Real.exp (-ph' x) ≤ Q x := by
    intro x
    have h1 := hlevi x (fun j => g x j)
    beta_reduce at h1
    rw [← hnorm x] at h1
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  have hQ0 : ∀ x, 0 ≤ Q x := fun x =>
    (mul_nonneg (hL0 x) (Real.exp_pos _).le).trans (hLQ x)
  have hap := hAP z hz ph' ψ ε g (SmoothR.ckR n z 2 ph' hph') (SmoothR.ckR n z 1 ψ hψ) hε hg
  set Gf : M → ℝ≥0∞ := fun x =>
    ENNReal.ofReal ((Levi n z ph x (fun j => g x j)).re * Real.exp (-ph' x)) with hGf
  set Ff : M → ℝ≥0∞ := fun x => h x * ENNReal.ofReal (Real.exp (2 * ψ x - ph' x)) with hFf
  have hG : ∫⁻ x, Gf x ∂vol n z ≤ ENNReal.ofReal (1 + ε) *
      wint n z (tstar n z (w1 ph' ψ) (w2 ph' ψ) g) (w1 ph' ψ) + n2 n z (sbar n z g) ph' := by
    calc ∫⁻ x, Gf x ∂vol n z ≤ ∫⁻ x, ENNReal.ofReal (Q x) ∂vol n z :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hLQ x)
      _ = ENNReal.ofReal (∫ x, Q x ∂vol n z) :=
          (ofReal_integral_eq_lintegral_ofReal iQ (Eventually.of_forall hQ0)).symm
      _ ≤ ENNReal.ofReal ((1 + ε) * (∫ x, ‖tstar n z (fun y => ph' y - 2 * ψ y)
            (fun y => ph' y - ψ y) g x‖ ^ 2 * Real.exp (-(ph' x - 2 * ψ x)) ∂vol n z) +
            ∫ x, sq2 n (sbar n z g x) * Real.exp (-ph' x) ∂vol n z) :=
          ENNReal.ofReal_le_ofReal hap
      _ ≤ ENNReal.ofReal (1 + ε) * ENNReal.ofReal (∫ x, ‖tstar n z (fun y => ph' y - 2 * ψ y)
            (fun y => ph' y - ψ y) g x‖ ^ 2 * Real.exp (-(ph' x - 2 * ψ x)) ∂vol n z) +
            ENNReal.ofReal (∫ x, sq2 n (sbar n z g x) * Real.exp (-ph' x) ∂vol n z) := by
          rw [← ENNReal.ofReal_mul (by linarith)]; exact ENNReal.ofReal_add_le
      _ ≤ _ := by
          gcongr
          · exact primed_ofReal_integral_le _ _ fun x =>
              mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
          · exact primed_ofReal_integral_le _ _ fun x =>
              mul_nonneg (by unfold sq2; positivity) (Real.exp_pos _).le
  have hF : ∫⁻ x, Ff x ∂vol n z ≤ ∫⁻ x, h x * ENNReal.ofReal (Real.exp (-ph x)) ∂vol n z :=
    lintegral_mono fun x => by
      simp only [hFf]
      gcongr
      linarith [hpp x]
  have mF : AEMeasurable Ff (vol n z) :=
    (hh.mul (ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.comp ((continuous_const.mul cψ).sub cph')).measurable)).aemeasurable
  have mG : AEMeasurable Gf (vol n z) :=
    (ENNReal.continuous_ofReal.comp ((cLevi ph hph).mul
      (Real.continuous_exp.comp cph'.neg))).measurable.aemeasurable
  set I : M → ℂ := fun x => ⟪dbarF n z F0 x, g x⟫_ℂ * (Real.exp (-w2 ph' ψ x) : ℂ) with hI
  have hpt : ∀ x, ‖I x‖ₑ ^ 2 ≤ Ff x * Gf x := by
    intro x
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    simp only [hI, hFf, hGf]
    rw [norm_mul, primed_inner_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), mul_pow]
    have he : Real.exp (-w2 ph' ψ x) ^ 2 = Real.exp (2 * ψ x - ph' x) * Real.exp (-ph' x) := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; simp only [w2]; ring
    rw [he, ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul (Real.exp_pos _).le,
      ENNReal.ofReal_mul (hL0 x)]
    calc ENNReal.ofReal (‖dbarDot n z F0 x (fun j => g x j)‖ ^ 2) *
          (ENNReal.ofReal (Real.exp (2 * ψ x - ph' x)) * ENNReal.ofReal (Real.exp (-ph' x)))
        ≤ h x * ENNReal.ofReal (Levi n z ph x (fun j => g x j)).re *
          (ENNReal.ofReal (Real.exp (2 * ψ x - ph' x)) * ENNReal.ofReal (Real.exp (-ph' x))) := by
          gcongr; exact hdom x _
      _ = _ := by ring
  show ENNReal.ofReal (‖∫ x, I x ∂vol n z‖ ^ 2) ≤ _
  calc ENNReal.ofReal (‖∫ x, I x ∂vol n z‖ ^ 2) = ‖∫ x, I x ∂vol n z‖ₑ ^ 2 := by
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    _ ≤ (∫⁻ x, ‖I x‖ₑ ∂vol n z) ^ 2 := by
        gcongr; exact enorm_integral_le_lintegral_enorm _
    _ ≤ (∫⁻ x, Ff x ∂vol n z) * ∫⁻ x, Gf x ∂vol n z :=
        primed_lintegral_sq_le _ _ _ _ mF mG hpt
    _ ≤ _ := mul_le_mul' hF hG

end

end ReciprocityTheory.L2DbarEstimates.F
end

section -- merged from ReciprocityTheory.L2DbarEstimates.Localization.LeviZCoordChart
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

private theorem coe_symm_apply_of_isChart_val {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e e' : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (he' : IsChart n z e')
    (y : M) (hy : y ∈ e.source) (hy' : y ∈ e'.source) :
    e'.symm =ᶠ[𝓝 (z y)] e.symm := by

  have hzy : z y = e' y := he' hy'
  have hzy2 : z y = e y := he hy
  have hopen : IsOpen (e.target ∩ (e'.target ∩ e'.symm ⁻¹' e.source)) :=
    e.open_target.inter (e'.isOpen_inter_preimage_symm e.open_source)
  have hmem : z y ∈ e.target ∩ (e'.target ∩ e'.symm ⁻¹' e.source) := by
    refine ⟨by rw [hzy2]; exact e.map_source hy, by rw [hzy]; exact e'.map_source hy', ?_⟩
    show e'.symm (z y) ∈ e.source
    rw [hzy, e'.left_inv hy']
    exact hy
  filter_upwards [hopen.mem_nhds hmem] with w hw
  obtain ⟨_, hw2, hw3⟩ := hw
  have ha : e'.symm w ∈ e'.source := e'.map_target hw2
  have hea : e (e'.symm w) = w := by
    rw [← he hw3, he' ha, e'.right_inv hw2]
  calc e'.symm w = e.symm (e (e'.symm w)) := (e.left_inv hw3).symm
    _ = e.symm w := by rw [hea]

private theorem wdb_apply_congr_of_eventuallyEq (n : ℕ) (k : Fin n) {F G : V n → ℂ} {p : V n} (h : F =ᶠ[𝓝 p] G) :
    wdb n k F p = wdb n k G p := by
  unfold wdb
  rw [h.fderiv_eq]

private theorem wd_apply_congr_of_eventuallyEq (n : ℕ) (k : Fin n) {F G : V n → ℂ} {p : V n} (h : F =ᶠ[𝓝 p] G) :
    wd n k F p = wd n k G p := by
  unfold wd
  rw [h.fderiv_eq]

private theorem db_apply_eq_wdb_of_mem_source {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : Fin n)
    (f : M → ℂ) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (y : M)
    (hy : y ∈ e.source) : db n z k f y = wdb n k (f ∘ e.symm) (z y) := by
  have hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ y ∈ e.source := ⟨e, he, hy⟩
  unfold db
  rw [dite_eq_left hex]
  apply wdb_apply_congr_of_eventuallyEq
  exact (coe_symm_apply_of_isChart_val n z e (Classical.choose hex) he (Classical.choose_spec hex).1 y hy
    (Classical.choose_spec hex).2).fun_comp f

private theorem d_apply_eq_wd_of_mem_source {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : Fin n)
    (f : M → ℂ) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (y : M)
    (hy : y ∈ e.source) : d n z k f y = wd n k (f ∘ e.symm) (z y) := by
  have hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ y ∈ e.source := ⟨e, he, hy⟩
  unfold d
  rw [dite_eq_left hex]
  apply wd_apply_congr_of_eventuallyEq
  exact (coe_symm_apply_of_isChart_val n z e (Classical.choose hex) he (Classical.choose_spec hex).1 y hy
    (Classical.choose_spec hex).2).fun_comp f

theorem leviZ_coord_chart {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (l : Fin n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) :
    EqOn ((fun y => z y l) ∘ e.symm) (fun w : V n => w l) e.target := by
  intro w hw
  simp only [Function.comp_apply]
  rw [he (e.map_target hw), e.right_inv hw]

theorem leviZ_wd_coord (n : ℕ) (j l : Fin n) (y : V n) :
    wd n j (fun w : V n => w l) y = if j = l then 1 else 0 := by
  have hL : fderiv ℝ (fun w : V n => w l) y =
      ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ) :=
    ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).hasFDerivAt.restrictScalars ℝ).fderiv
  unfold wd
  rw [hL]
  by_cases h : j = l
  · subst h
    simp [bas, PiLp.single_apply, Complex.I_mul_I]
  · simp [bas, PiLp.single_apply, h, Ne.symm h]

theorem leviZ_d_coord {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (j l : Fin n) (x : M) :
    d n z j (fun y => z y l) x = if j = l then 1 else 0 := by
  obtain ⟨e, hx, hze⟩ := hz x
  have he : IsChart n z e := fun y _ => congrFun hze y
  have hzx : z x ∈ e.target := by rw [he hx]; exact e.map_source hx
  rw [d_apply_eq_wd_of_mem_source n z j _ e he x hx,
    wd_apply_congr_of_eventuallyEq n j (G := fun w : V n => w l) (by
      filter_upwards [e.open_target.mem_nhds hzx] with w hw
      exact leviZ_coord_chart n z l e he hw)]
  exact leviZ_wd_coord n j l (z x)

private theorem wdb_sum_mul_conj_eq_coord (n : ℕ) (k : Fin n) (p : V n) :
    wdb n k (fun w : V n => ∑ l, w l * conj (w l)) p = p k := by
  have hP : ∀ l, HasFDerivAt (fun w : V n => w l)
      ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ) p :=
    fun l => (EuclideanSpace.proj l : V n →L[ℂ] ℂ).hasFDerivAt.restrictScalars ℝ
  have hC : ∀ l, HasFDerivAt (fun w : V n => conj (w l))
      (Complex.conjCLE.toContinuousLinearMap.comp
        ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ)) p :=
    fun l => Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp p (hP l)
  have hF : HasFDerivAt (fun w : V n => ∑ l, w l * conj (w l))
      (∑ l, (p l • Complex.conjCLE.toContinuousLinearMap.comp
        ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ) +
        conj (p l) • (EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ)) p :=
    HasFDerivAt.fun_sum (fun l _ => (hP l).mul (hC l))
  unfold wdb
  rw [hF.fderiv]
  simp [bas, PiLp.single_apply]
  simp only [apply_ite (starRingEnd ℂ), map_zero, mul_ite, mul_zero, Complex.conj_I,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  linear_combination ((starRingEnd ℂ (p.ofLp k) - p.ofLp k) / 2) * Complex.I_sq

theorem leviNormSq (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : LeviNormSqStatement n M := by
  intro z hz
  have hchart : ∀ x, ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source := by
    intro x
    obtain ⟨e, hx, hze⟩ := hz x
    exact ⟨e, fun y _ => congrFun hze y, hx⟩

  have hloc : ∀ e : OpenPartialHomeomorph M (V n), IsChart n z e →
      EqOn ((fun y => ((‖z y‖ ^ 2 : ℝ) : ℂ)) ∘ e.symm) (fun w : V n => ((‖w‖ ^ 2 : ℝ) : ℂ))
        e.target := by
    intro e he w hw
    simp only [Function.comp_apply]
    rw [he (e.map_target hw), e.right_inv hw]
  have hsq : (fun w : V n => ((‖w‖ ^ 2 : ℝ) : ℂ)) = fun w => ∑ l, w l * conj (w l) := by
    funext w
    rw [EuclideanSpace.norm_sq_eq]
    push_cast
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  refine ⟨fun e he => ?_, fun x ξ => ?_⟩
  · have hsm : ContDiffOn ℝ ∞ (fun w : V n => ∑ l, w l * conj (w l)) e.target := by
      refine ContDiffOn.sum (fun l _ => ?_)
      have hPc : ContDiff ℝ ∞ (fun w : V n => w l) :=
        ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ).contDiff
      have hCc : ContDiff ℝ ∞ (fun w : V n => conj (w l)) :=
        (Complex.conjCLE.toContinuousLinearMap.comp
          ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ)).contDiff
      exact (hPc.mul hCc).contDiffOn
    rw [← hsq] at hsm
    exact hsm.congr (hloc e he)
  ·
    have hdb : ∀ k, db n z k (fun y => ((‖z y‖ ^ 2 : ℝ) : ℂ)) = fun y => z y k := by
      intro k
      funext y
      obtain ⟨e, he, hy⟩ := hchart y
      have hzy : z y ∈ e.target := by rw [he hy]; exact e.map_source hy
      rw [db_apply_eq_wdb_of_mem_source n z k _ e he y hy,
        wdb_apply_congr_of_eventuallyEq n k (G := fun w : V n => ∑ l, w l * conj (w l)) (by
          rw [← hsq]
          filter_upwards [e.open_target.mem_nhds hzy] with w hw
          exact hloc e he hw)]
      exact wdb_sum_mul_conj_eq_coord n k (z y)
    simp only [Levi, hdb, leviZ_d_coord n z hz]
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_eq_single j]
    · simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    · intro k _ hkj
      simp [Ne.symm hkj]
    · simp

end

end ReciprocityTheory.L2DbarEstimates.F
end

section -- merged from ReciprocityTheory.L2DbarEstimates.Localization.ShellCeilEq
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

lemma shell_mem (a t : ℝ) (ht : a + 1 < t) :
    a + 1 + (⌈t - a - 2⌉₊ : ℝ) < t ∧ t ≤ a + 2 + (⌈t - a - 2⌉₊ : ℝ) := by
  constructor
  · rcases le_or_gt 0 (t - a - 2) with h | h
    · have := Nat.ceil_lt_add_one h
      linarith
    · rw [Nat.ceil_eq_zero.mpr h.le]
      simp only [CharP.cast_eq_zero, add_zero]
      linarith
  · have := Nat.le_ceil (t - a - 2)
    linarith

lemma shell_coef (C : ℝ) (hC : 0 ≤ C) (k : ℕ) :
    ENNReal.ofReal (Real.exp (-(Real.log (1 + C) + k))) * ENNReal.ofReal C ≤
      ENNReal.ofReal (Real.exp (-(k : ℝ))) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  rw [neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log (by linarith)]
  have h1 : 0 < 1 + C := by linarith
  have h2 := Real.exp_pos (-(k : ℝ))
  have h3 : (1 + C)⁻¹ * C ≤ 1 := by
    rw [inv_mul_le_iff₀ h1]
    linarith
  have h4 : 0 ≤ (1 + C)⁻¹ := inv_nonneg.mpr h1.le
  nlinarith [mul_le_mul_of_nonneg_left h3 h2.le]

private lemma vol_lt_infty_of_compact {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [MeasurableSpace M]
    [BorelSpace M] (z : M → V n) (hz : IsLocalHomeomorph z) {K : Set M} (hK : IsCompact K) :
    vol n z K < ⊤ := by
  classical
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  unfold vol
  split_ifs with h
  · rw [Measure.ofMeasurable_apply K hKm]
    unfold volFun
    have hz' : ∀ x, ∃ e : OpenPartialHomeomorph M (V n), x ∈ e.source ∧ z = e :=
      fun x => (isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mp hz) x (Set.mem_univ x)
    choose e he hze using hz'
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x => (e x).source) (fun x => (e x).open_source)
      (fun x _ => Set.mem_iUnion.mpr ⟨x, he x⟩)
    have hbound : ∀ y : V n, ((K ∩ z ⁻¹' {y}).encard : ℝ≥0∞) ≤
        (z '' K).indicator (fun _ => (t.card : ℝ≥0∞)) y := by
      intro y
      by_cases hy : y ∈ z '' K
      · rw [Set.indicator_of_mem hy]
        have hidx : ∀ p ∈ K ∩ z ⁻¹' {y}, ∃ i ∈ t, p ∈ (e i).source := by
          intro p hp
          have := ht hp.1
          simp only [Set.mem_iUnion] at this
          obtain ⟨i, hi, hpi⟩ := this
          exact ⟨i, hi, hpi⟩
        choose! f hf1 hf2 using hidx
        have h1 : (K ∩ z ⁻¹' {y}).encard ≤ ((t : Set M)).encard := by
          refine Set.encard_le_encard_of_injOn (fun p hp => hf1 p hp) ?_
          intro p hp q hq hpq
          have hp' := hf2 p hp
          have hq' := hf2 q hq
          rw [hpq] at hp'
          apply (e (f q)).injOn hp' hq'
          have h3 := congrFun (hze (f q))
          rw [← h3 p, ← h3 q, Set.mem_singleton_iff.mp hp.2, Set.mem_singleton_iff.mp hq.2]
        rw [Set.encard_coe_eq_coe_finsetCard] at h1
        calc ((K ∩ z ⁻¹' {y}).encard : ℝ≥0∞) ≤ ((t.card : ℕ∞) : ℝ≥0∞) := ENat.toENNReal_le.mpr h1
          _ = t.card := by simp
      · rw [Set.indicator_of_notMem hy]
        have : K ∩ z ⁻¹' {y} = ∅ := by
          ext p
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
            iff_false, not_and]
          intro hp hzp
          exact hy ⟨p, hp, hzp⟩
        rw [this, Set.encard_empty]
        simp
    calc ∫⁻ y, ((K ∩ z ⁻¹' {y}).encard : ℝ≥0∞) ≤ ∫⁻ y, (z '' K).indicator (fun _ => (t.card : ℝ≥0∞)) y :=
          lintegral_mono hbound
      _ = t.card * volume (z '' K) :=
          lintegral_indicator_const (hK.image hz.continuous).isClosed.measurableSet _
      _ < ⊤ := ENNReal.mul_lt_top (by simp) (hK.image hz.continuous).measure_lt_top
  · simp

theorem shell (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : ShellStatement n M := by
  classical
  intro z hz e ph ψ v a he hK hph hψ hv
  set g : M → ℝ := fun x => ‖v x‖ ^ 2 * Real.exp (-ph x + ψ x) with hg
  have hgc : Continuous g := by
    simp only [hg]
    fun_prop
  have hgm : Measurable fun x => ENNReal.ofReal (g x) := ENNReal.measurable_ofReal.comp hgc.measurable
  have hfin : ∀ b : ℝ, ∫⁻ x in {x | e x ≤ b}, ENNReal.ofReal (g x) ∂vol n z < ⊤ := by
    intro b
    exact setLIntegral_lt_top_of_isCompact (vol_lt_infty_of_compact z hz (hK b)).ne (hK b)
      (f := fun x => (g x).toNNReal) (continuous_real_toNNReal.comp hgc)
  set C : ℕ → ℝ := fun k => (∫⁻ x in {x | e x ≤ a + 2 + k}, ENNReal.ofReal (g x) ∂vol n z).toReal with hC
  have hC0 : ∀ k : ℕ, 0 ≤ C k := fun k => ENNReal.toReal_nonneg
  have hCeq : ∀ k : ℕ, ∫⁻ x in {x | e x ≤ a + 2 + k}, ENNReal.ofReal (g x) ∂vol n z = ENNReal.ofReal (C k) :=
    fun k => (ENNReal.ofReal_toReal (hfin _).ne).symm
  set R : ℝ → ℝ := fun t => if a + 1 < t then Real.log (1 + C ⌈t - a - 2⌉₊) + ⌈t - a - 2⌉₊ else 0 with hR
  have hterm0 : ∀ k : ℕ, 0 ≤ Real.log (1 + C k) + k :=
    fun k => add_nonneg (Real.log_nonneg (by linarith [hC0 k])) (Nat.cast_nonneg k)
  refine ⟨R, ?_, ?_⟩
  · intro b
    refine ⟨∑ k ∈ Finset.range (⌈b - a - 2⌉₊ + 1), (Real.log (1 + C k) + k), ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    simp only [Set.mem_Iic] at ht
    simp only [hR]
    split_ifs with h
    · exact Finset.single_le_sum (f := fun k : ℕ => Real.log (1 + C k) + k) (fun k _ => hterm0 k)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.ceil_mono (by linarith))))
    · exact Finset.sum_nonneg fun k _ => hterm0 k
  · intro χ hχ0 hχR
    unfold nV
    set S : ℕ → Set M := fun k => {x | a + 1 + k < e x ∧ e x ≤ a + 2 + k} with hS
    have hSm : ∀ k, MeasurableSet (S k) := fun k =>
      (measurableSet_lt measurable_const he.measurable).inter (measurableSet_le he.measurable measurable_const)
    have hLm : MeasurableSet {x | e x ≤ a + 1} := measurableSet_le he.measurable measurable_const
    have hpt : ∀ x, ENNReal.ofReal (‖v x‖ ^ 2 * Real.exp (-(ph x + χ (e x) - ψ x))) ≤
        {x | e x ≤ a + 1}.indicator (fun x => ENNReal.ofReal (g x)) x +
        ∑' k, (S k).indicator (fun x => ENNReal.ofReal (Real.exp (-(Real.log (1 + C k) + k))) *
          ENNReal.ofReal (g x)) x := by
      intro x
      by_cases hx : e x ≤ a + 1
      · rw [Set.indicator_of_mem (show x ∈ {x | e x ≤ a + 1} from hx)]
        refine le_trans ?_ le_self_add
        apply ENNReal.ofReal_le_ofReal
        simp only [hg]
        gcongr
        linarith [hχ0 (e x)]
      · push_neg at hx
        have hxS : x ∈ S ⌈e x - a - 2⌉₊ := shell_mem a (e x) hx
        refine le_trans ?_ (le_add_left (ENNReal.le_tsum ⌈e x - a - 2⌉₊))
        rw [Set.indicator_of_mem hxS, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        apply ENNReal.ofReal_le_ofReal
        have hRx : Real.log (1 + C ⌈e x - a - 2⌉₊) + ⌈e x - a - 2⌉₊ ≤ χ (e x) := by
          have := hχR (e x) hx.le
          simp only [hR, if_pos hx] at this
          exact this
        simp only [hg]
        rw [show -(ph x + χ (e x) - ψ x) = -(χ (e x)) + (-ph x + ψ x) by ring, Real.exp_add]
        have h1 : Real.exp (-(χ (e x))) ≤ Real.exp (-(Real.log (1 + C ⌈e x - a - 2⌉₊) + ⌈e x - a - 2⌉₊)) :=
          Real.exp_le_exp.mpr (by linarith)
        have h2 : 0 ≤ ‖v x‖ ^ 2 * Real.exp (-ph x + ψ x) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right h1 h2]
    calc ∫⁻ x, ENNReal.ofReal (‖v x‖ ^ 2 * Real.exp (-(ph x + χ (e x) - ψ x))) ∂vol n z
        ≤ ∫⁻ x, ({x | e x ≤ a + 1}.indicator (fun x => ENNReal.ofReal (g x)) x +
          ∑' k, (S k).indicator (fun x => ENNReal.ofReal (Real.exp (-(Real.log (1 + C k) + k))) *
            ENNReal.ofReal (g x)) x) ∂vol n z := lintegral_mono hpt
      _ = ∫⁻ x in {x | e x ≤ a + 1}, ENNReal.ofReal (g x) ∂vol n z +
          ∑' k, ENNReal.ofReal (Real.exp (-(Real.log (1 + C k) + k))) *
            ∫⁻ x in S k, ENNReal.ofReal (g x) ∂vol n z := by
        rw [lintegral_add_left (hgm.indicator hLm), lintegral_indicator hLm,
          lintegral_tsum (fun k => ((hgm.const_mul _).indicator (hSm k)).aemeasurable)]
        congr 1
        refine tsum_congr fun k => ?_
        rw [lintegral_indicator (hSm k), lintegral_const_mul _ hgm]
      _ ≤ ∫⁻ x in {x | e x ≤ a + 1}, ENNReal.ofReal (g x) ∂vol n z +
          ∑' k : ℕ, ENNReal.ofReal (Real.exp (-(k : ℝ))) := by
        refine add_le_add le_rfl (ENNReal.tsum_le_tsum fun k => ?_)
        calc ENNReal.ofReal (Real.exp (-(Real.log (1 + C k) + k))) * ∫⁻ x in S k, ENNReal.ofReal (g x) ∂vol n z
            ≤ ENNReal.ofReal (Real.exp (-(Real.log (1 + C k) + k))) * ENNReal.ofReal (C k) := by
              gcongr
              rw [← hCeq k]
              exact lintegral_mono_set (fun x hx => hx.2)
          _ ≤ _ := shell_coef (C k) (hC0 k) k
      _ < ⊤ := by
        refine ENNReal.add_lt_top.mpr ⟨hfin (a + 1), ?_⟩
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => (Real.exp_pos _).le) Real.summable_exp_neg_nat]
        exact ENNReal.ofReal_lt_top

end

end ReciprocityTheory.L2DbarEstimates.F
end

section -- merged from ReciprocityTheory.L2DbarEstimates.Localization.DerivSmoothTransitionOfOneLt
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem deriv_smoothTransition_of_neg {t : ℝ} (ht : t < 0) : deriv Real.smoothTransition t = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hs)
  rw [h.deriv_eq]
  simp

theorem deriv_smoothTransition_of_one_lt {t : ℝ} (ht : 1 < t) : deriv Real.smoothTransition t = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact Real.smoothTransition.one_of_one_le (le_of_lt hs)
  rw [h.deriv_eq]
  simp

theorem deriv_smoothTransition_bounded : ∃ C : ℝ, ∀ t, |deriv Real.smoothTransition t| ≤ C := by
  have hd : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hd.continuousOn
  refine ⟨C, fun t => ?_⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, zero_le_one⟩)
  rcases lt_or_ge t 0 with ht | ht
  · rw [deriv_smoothTransition_of_neg ht]; simpa using hC0
  rcases lt_or_ge 1 t with ht' | ht'
  · rw [deriv_smoothTransition_of_one_lt ht']; simpa using hC0
  · simpa [Real.norm_eq_abs] using hC t ⟨ht, ht'⟩

theorem smoothReal_dbar_sq {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e : M → ℝ) (he : SmoothR n z e) : SmoothR n z (dbarSq n z (fun y => (e y : ℂ))) := by
  unfold SmoothR Smooth at *
  intro c hc
  have hG := he c hc
  have hfd : ContDiffOn ℝ ∞ (fun y => fderiv ℝ ((fun x => (e x : ℂ)) ∘ c.symm) y) c.target :=
    hG.fderiv_of_isOpen c.open_target (by simp)
  have hw : ∀ j, ContDiffOn ℝ ∞ (fun y => wdb n j ((fun x => (e x : ℂ)) ∘ c.symm) y) c.target := by
    intro j
    unfold wdb
    exact ((hfd.clm_apply contDiffOn_const).add
      (contDiffOn_const.mul (hfd.clm_apply contDiffOn_const))).div_const 2
  have hsum : ContDiffOn ℝ ∞
      (fun y => ∑ j ∈ Finset.univ, ‖wdb n j ((fun x => (e x : ℂ)) ∘ c.symm) y‖ ^ 2) c.target :=
    ContDiffOn.sum fun j _ => (contDiff_norm_sq ℝ).comp_contDiffOn (hw j)
  have hΦ := Complex.ofRealCLM.contDiff.comp_contDiffOn hsum
  refine hΦ.congr fun y hy => ?_
  simp only [Function.comp_apply, Complex.ofRealCLM_apply]
  congr 1
  unfold dbarSq
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  have hx : c.symm y ∈ c.source := c.map_target hy
  have hzx : z (c.symm y) = y := by rw [hc hx]; exact c.right_inv hy
  have hex : ∃ e' : OpenPartialHomeomorph M (V n), IsChart n z e' ∧ c.symm y ∈ e'.source :=
    ⟨c, hc, hx⟩
  unfold db
  rw [dite_eq_left hex]
  obtain ⟨hc1, hc2⟩ := Classical.choose_spec hex
  set c' := Classical.choose hex
  rw [hzx]
  have hcx : c' (c.symm y) = y := by rw [← hc1 hc2]; exact hzx
  have hsym : c'.symm y = c.symm y := by
    calc c'.symm y = c'.symm (c' (c.symm y)) := by rw [hcx]
      _ = c.symm y := c'.left_inv hc2
  have hyt : y ∈ c'.target := hcx ▸ c'.map_source hc2
  have hloc : (fun x => (e x : ℂ)) ∘ c'.symm =ᶠ[𝓝 y] (fun x => (e x : ℂ)) ∘ c.symm := by
    have h1 : ∀ᶠ w in 𝓝 y, w ∈ c'.target := c'.open_target.mem_nhds hyt
    have h2 : ∀ᶠ w in 𝓝 y, c'.symm w ∈ c.source :=
      (c'.continuousAt_symm hyt).preimage_mem_nhds (c.open_source.mem_nhds (by rw [hsym]; exact hx))
    filter_upwards [h1, h2] with w hw1 hw2
    have hcw : c (c'.symm w) = w := by
      rw [← hc hw2, hc1 (c'.map_target hw1), c'.right_inv hw1]
    have hsw : c'.symm w = c.symm w := by
      calc c'.symm w = c.symm (c (c'.symm w)) := (c.left_inv hw2).symm
        _ = c.symm w := by rw [hcw]
    simp only [Function.comp_apply, hsw]
  unfold wdb
  rw [hloc.fderiv_eq]

theorem dbar_sq_nonneg {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (u : M → ℂ) (x : M) : 0 ≤ dbarSq n z u x := by
  unfold dbarSq
  exact Finset.sum_nonneg fun j _ => by positivity

theorem dbar_sq_comp_eq {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (k : ℝ → ℝ) (hk : ContDiff ℝ ∞ k) (e : M → ℝ) (he : SmoothR n z e) (x : M) :
    dbarSq n z (fun y => (k (e y) : ℂ)) x = deriv k (e x) ^ 2 * dbarSq n z (fun y => (e y : ℂ)) x := by
  unfold dbarSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold db
  split_ifs with h
  · obtain ⟨hc1, hc2⟩ := Classical.choose_spec h
    set c := Classical.choose h
    have hy : z x ∈ c.target := by rw [hc1 hc2]; exact c.map_source hc2
    have hE : DifferentiableAt ℝ ((fun y => (e y : ℂ)) ∘ c.symm) (z x) :=
      ((he c hc1).differentiableOn (by simp)).differentiableAt (c.open_target.mem_nhds hy)
    obtain ⟨r, hr⟩ : ∃ r : V n → ℝ, r = fun y => (((fun y => (e y : ℂ)) ∘ c.symm) y).re :=
      ⟨_, rfl⟩
    have hR : DifferentiableAt ℝ r (z x) := by
      rw [hr]; exact Complex.reCLM.differentiableAt.comp _ hE
    have hK : (fun y => ((k (e y) : ℝ) : ℂ)) ∘ c.symm = Complex.ofRealCLM ∘ (k ∘ r) := by
      funext y; simp [hr]
    have hG : (fun y => ((e y : ℝ) : ℂ)) ∘ c.symm = Complex.ofRealCLM ∘ r := by
      funext y; simp [hr]
    have hrx : r (z x) = e x := by simp [hr, hc1 hc2, c.left_inv hc2]
    have hk' : HasDerivAt k (deriv k (e x)) (r (z x)) := by
      rw [hrx]
      exact ((hk.differentiable (by simp)) (e x)).hasDerivAt
    have hd1 := Complex.ofRealCLM.hasFDerivAt.comp (z x) (hk'.comp_hasFDerivAt (z x) hR.hasFDerivAt)
    have hd2 := Complex.ofRealCLM.hasFDerivAt.comp (z x) hR.hasFDerivAt
    rw [hK, hG]
    unfold wdb
    rw [hd1.fderiv, hd2.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      Complex.ofRealCLM_apply]
    rw [show ∀ a b c' : ℝ, (((a * b : ℝ) : ℂ) + Complex.I * ((a * c' : ℝ) : ℂ)) / 2 =
        (a : ℂ) * (((b : ℂ) + Complex.I * (c' : ℂ)) / 2) from fun a b c' => by push_cast; ring]
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  · simp

theorem continuous_of_smoothReal {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (e : M → ℝ) (he : SmoothR n z e) : Continuous e := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨c, hx, hzc⟩ := hz x
  have hc : IsChart n z c := fun y _ => by rw [hzc]
  have hg := (he c hc).continuousOn
  have h1 : ContinuousAt (((fun y => (e y : ℂ)) ∘ c.symm) ∘ c) x :=
    (hg.continuousAt (c.open_target.mem_nhds (c.map_source hx))).comp (c.continuousAt hx)
  have h2 : ((fun y => (e y : ℂ)) ∘ c.symm) ∘ c =ᶠ[𝓝 x] fun y => (e y : ℂ) := by
    filter_upwards [c.open_source.mem_nhds hx] with y hy
    simp [c.left_inv hy]
  have h3 := Complex.continuous_re.continuousAt.comp (h1.congr h2)
  simpa [Function.comp_def] using h3

theorem psi (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : PsiStatement n M := by
  intro z hz e a he hcomp
  have hec : Continuous e := continuous_of_smoothReal n z hz e he
  obtain ⟨C, hC⟩ := deriv_smoothTransition_bounded
  set D := dbarSq n z (fun y => (e y : ℂ)) with hD
  have hDs : SmoothR n z D := smoothReal_dbar_sq n z e he
  have hk0 : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition (t - a - 2)) :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).sub contDiff_const)
  refine ⟨fun x => Real.smoothTransition (e x - a - 2) * (C ^ 2 * D x), ?_, ?_, ?_⟩
  · refine SmoothR.mul n z _ _ (SmoothR.comp n z _ hk0 e he) (SmoothR.mul n z _ _ ?_ hDs)
    show Smooth n z (fun _ => ((C ^ 2 : ℝ) : ℂ))
    exact Smooth.const n z _
  · intro x hx
    have h0 : ∀ y, e y < a + 2 →
        Real.smoothTransition (e y - a - 2) * (C ^ 2 * D y) = 0 := by
      intro y hy
      rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
    refine ⟨h0 x (by linarith), ?_⟩
    unfold dSqR
    refine Finset.sum_eq_zero fun j _ => ?_
    have hnot : x ∉ tsupport (fun y =>
        ((Real.smoothTransition (e y - a - 2) * (C ^ 2 * D y) : ℝ) : ℂ)) := by
      rw [notMem_tsupport_iff_eventuallyEq]
      filter_upwards [(isOpen_lt hec continuous_const).mem_nhds
        (show e x < a + 2 by linarith)] with y hy
      simp [h0 y hy]
    have hnot2 := fun h => hnot (tsupport_d_subset n z j _ h)
    rw [image_eq_zero_of_notMem_tsupport hnot2]
    simp
  · intro ν
    set N : ℝ := max (ν : ℝ) (a + 3) with hN
    have hk : ContDiff ℝ ∞ (fun t : ℝ => 1 - Real.smoothTransition (t - N)) :=
      contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))
    refine ⟨fun x => 1 - Real.smoothTransition (e x - N), ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · exact SmoothR.comp n z _ hk e he
    · refine HasCompactSupport.intro (hcomp (N + 1)) fun x hx => ?_
      simp only [Set.mem_ofPred_eq, not_le] at hx
      beta_reduce
      rw [Real.smoothTransition.one_of_one_le (show 1 ≤ e x - N by linarith)]
      simp
    · intro x
      exact ⟨by linarith [Real.smoothTransition.le_one (e x - N)],
        by linarith [Real.smoothTransition.nonneg (e x - N)]⟩
    · intro x hx
      beta_reduce
      rw [Real.smoothTransition.zero_of_nonpos (show e x - N ≤ 0 by linarith [le_max_left (ν : ℝ) (a + 3)])]
      simp
    · intro x
      have hcomp' : dbarSq n z (fun y => ((1 - Real.smoothTransition (e y - N) : ℝ) : ℂ)) x =
          deriv (fun t : ℝ => 1 - Real.smoothTransition (t - N)) (e x) ^ 2 * D x :=
        dbar_sq_comp_eq n z _ hk e he x
      have hder : deriv (fun t : ℝ => 1 - Real.smoothTransition (t - N)) (e x) =
          -deriv Real.smoothTransition (e x - N) := by
        rw [deriv_const_sub, deriv_comp_sub_const]
      rw [hcomp', hder, neg_sq]
      have hD0 : 0 ≤ D x := dbar_sq_nonneg n z _ x
      by_cases hlt : e x < N
      · rw [deriv_smoothTransition_of_neg (by linarith)]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
        exact (Real.exp_pos _).le
      · have hge : a + 3 ≤ e x := le_trans (le_max_right _ _) (not_lt.1 hlt)
        beta_reduce
        rw [Real.smoothTransition.one_of_one_le (show 1 ≤ e x - a - 2 by linarith), one_mul]
        have h1 : deriv Real.smoothTransition (e x - N) ^ 2 ≤ C ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hC _) 2
        have h2 := Real.add_one_le_exp (C ^ 2 * D x)
        nlinarith

end

end ReciprocityTheory.L2DbarEstimates.F
end
