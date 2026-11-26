module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaEqLatticeIndex
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionCardLeAbsNormPow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CmConjugationProperties
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductLintegralLimit
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.EnnrealRpowTwoEqSq

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelEigenfunctionEquicontinuous
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelEigenfunctionEquicontinuous
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc.WeightedCauchySchwarzLintegral

open scoped Pointwise

theorem sq_lintegral_mul_le {X : Type*} [MeasurableSpace X] (ν : Measure X) {a b : X → ℝ≥0∞}
    (ha : Measurable a) (hb : Measurable b) :
    (∫⁻ w, a w * b w ∂ν) ^ 2 ≤ (∫⁻ w, a w ∂ν) * ∫⁻ w, a w * b w ^ 2 ∂ν :=
  _root_.UpperTheory.Reformulated.B.P6.r96a.GlobalTheory.CompanionTheory.Conc.WeightedCauchySchwarzLintegral.sq_lintegral_mul_le ν ha hb

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem eventually_lintegral_translate_le [LocallyCompactSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] {α : G → ℂ} (hα : Continuous α) (hs : HasCompactSupport α)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 (1 : G), ∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ ≤ ε := by
  obtain ⟨V, hVc, hV⟩ := exists_compact_mem_nhds (1 : G)
  have hC : IsCompact (V * tsupport α) := hVc.mul hs
  set C : Set G := V * tsupport α with hCdef
  have hfin : μ C ≠ ∞ := hC.measure_lt_top.ne
  have hc : 0 < ε / (μ C + 1) :=
    ENNReal.div_pos hε.ne' (by simp [hfin])
  set c : ℝ≥0∞ := ε / (μ C + 1) with hcdef
  have hunif : ∀ᶠ y in 𝓝 (1 : G), ∀ w ∈ C, ‖α (y⁻¹ * w) - α w‖ₑ < c := by
    refine hC.eventually_forall_of_forall_eventually fun w _ => ?_
    have hcont : Continuous fun z : G × G => ‖α (z.1⁻¹ * z.2) - α z.2‖ₑ := by
      fun_prop
    have h0 : ‖α ((1 : G)⁻¹ * w) - α w‖ₑ < c := by simpa using hc
    exact hcont.continuousAt.eventually_lt continuousAt_const h0
  filter_upwards [hunif, hV] with y hy hyV
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have hle : ∀ w, ‖α (y⁻¹ * w) - α w‖ₑ ≤ C.indicator (fun _ => c) w := by
    intro w
    by_cases hw : w ∈ C
    · rw [Set.indicator_of_mem hw]
      exact (hy w hw).le
    · rw [Set.indicator_of_notMem hw]
      have h1 : α w = 0 := by
        by_contra h
        exact hw (Set.mem_mul.2 ⟨1, mem_of_mem_nhds hV, w, subset_tsupport _ h, one_mul w⟩)
      have h2 : α (y⁻¹ * w) = 0 := by
        by_contra h
        exact hw (Set.mem_mul.2 ⟨y, hyV, y⁻¹ * w, subset_tsupport _ h, by group⟩)
      simp [h1, h2]
  calc ∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ ≤ ∫⁻ w, C.indicator (fun _ => c) w ∂μ := lintegral_mono hle
    _ = c * μ C := lintegral_indicator_const hCm c
    _ ≤ c * (μ C + 1) := by gcongr; exact le_self_add
    _ = ε := ENNReal.div_mul_cancel (by simp) (by simp [hfin])

variable [LocallyCompactSpace G] [SecondCountableTopology G]

theorem enorm_translate_sub_le (μ : Measure G) [μ.IsHaarMeasure] {α ψ : G → ℂ} (hα : Continuous α)
    (hs : HasCompactSupport α) (hψ : Continuous ψ) {s : ℂ}
    (hrep : ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) (x y : G) :
    ‖s‖ₑ * ‖ψ (x * y) - ψ x‖ₑ ≤ ∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ * ‖ψ (x * w)‖ₑ ∂μ := by
  have h1 : s * ψ (x * y) = ∫ w, α (y⁻¹ * w) * ψ (x * w) ∂μ := by
    rw [← hrep (x * y), ← integral_mul_left_eq_self (fun w => α (y⁻¹ * w) * ψ (x * w)) y]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp [mul_assoc]
  have hcs : HasCompactSupport fun w => α (y⁻¹ * w) := hs.comp_homeomorph (Homeomorph.mulLeft y⁻¹)
  have hi1 : Integrable (fun w => α (y⁻¹ * w) * ψ (x * w)) μ :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hcs.mul_right
  have hi2 : Integrable (fun w => α w * ψ (x * w)) μ :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hs.mul_right
  have h3 : s * (ψ (x * y) - ψ x) = ∫ w, (α (y⁻¹ * w) - α w) * ψ (x * w) ∂μ := by
    rw [mul_sub, h1, ← hrep x, ← integral_sub hi1 hi2]
    exact integral_congr_ae (ae_of_all _ fun w => by ring)
  rw [← enorm_mul, h3]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  exact lintegral_congr fun w => enorm_mul _ _

theorem lintegral_right_translate (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Γ : Subgroup G) [Countable Γ] {F : Set G} (hF : IsFundamentalDomain Γ F μ) {ψ : G → ℂ}
    (hl : ∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) (w : G) :
    ∫⁻ x in F, ‖ψ (x * w)‖ₑ ^ 2 ∂μ = ∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ := by
  have hF' : IsFundamentalDomain Γ (MulOpposite.op w • F) μ := hF.smul_of_comm (MulOpposite.op w)
  have himg : (fun x => x * w) '' F = MulOpposite.op w • F := rfl
  have h1 := (measurePreserving_mul_right μ w).setLIntegral_comp_emb
    (MeasurableEquiv.mulRight w).measurableEmbedding (fun x => ‖ψ x‖ₑ ^ 2) F
  rw [h1, himg]
  refine hF'.setLIntegral_eq hF _ fun γ x => ?_
  simp only [Subgroup.smul_def, smul_eq_mul]
  rw [hl _ γ.2]

theorem sq_mean_translate_le (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Γ : Subgroup G) [Countable Γ] {F : Set G} (hF : IsFundamentalDomain Γ F μ) {α ψ : G → ℂ}
    (hα : Continuous α) (hs : HasCompactSupport α) (hψ : Continuous ψ)
    (hl : ∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) {s : ℂ}
    (hrep : ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x)
    (hn : (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1) (y : G)
    (hA : ∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ ≠ ∞) :
    ‖s‖ₑ ^ 2 * ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ ≤ (∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ) ^ 2 := by
  set a : G → ℝ≥0∞ := fun w => ‖α (y⁻¹ * w) - α w‖ₑ with ha_def
  have hac : Continuous a := by fun_prop
  have ha : Measurable a := hac.measurable
  have hjm : Measurable fun z : G × G => a z.2 * ‖ψ (z.1 * z.2)‖ₑ ^ 2 := by
    have hc : Continuous fun z : G × G => ‖ψ (z.1 * z.2)‖ₑ := by fun_prop
    exact (ha.comp measurable_snd).mul (hc.measurable.pow_const 2)
  calc ‖s‖ₑ ^ 2 * ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ
      = ∫⁻ x in F, (‖s‖ₑ * ‖ψ (x * y) - ψ x‖ₑ) ^ 2 ∂μ := by
        rw [← lintegral_const_mul' _ _ (by simp)]
        exact lintegral_congr fun x => (mul_pow _ _ _).symm
    _ ≤ ∫⁻ x in F, (∫⁻ w, a w * ‖ψ (x * w)‖ₑ ∂μ) ^ 2 ∂μ :=
        lintegral_mono fun x => by
          gcongr
          exact enorm_translate_sub_le μ hα hs hψ hrep x y
    _ ≤ ∫⁻ x in F, (∫⁻ w, a w ∂μ) * ∫⁻ w, a w * ‖ψ (x * w)‖ₑ ^ 2 ∂μ ∂μ :=
        lintegral_mono fun x => sq_lintegral_mul_le μ ha (by
          have : Continuous fun w => ‖ψ (x * w)‖ₑ := by fun_prop
          exact this.measurable)
    _ = (∫⁻ w, a w ∂μ) * ∫⁻ x in F, ∫⁻ w, a w * ‖ψ (x * w)‖ₑ ^ 2 ∂μ ∂μ :=
        lintegral_const_mul' _ _ hA
    _ = (∫⁻ w, a w ∂μ) * ∫⁻ w, ∫⁻ x in F, a w * ‖ψ (x * w)‖ₑ ^ 2 ∂μ ∂μ := by
        rw [lintegral_lintegral_swap hjm.aemeasurable]
    _ = (∫⁻ w, a w ∂μ) * ∫⁻ w, a w ∂μ := by
        congr 1
        refine lintegral_congr fun w => ?_
        rw [lintegral_const_mul' _ _ enorm_ne_top, lintegral_right_translate μ Γ hF hl w, hn, mul_one]
    _ = (∫⁻ w, a w ∂μ) ^ 2 := (sq _).symm

theorem exists_nhds_sq_mean_le (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Γ : Subgroup G) [Countable Γ] {α : G → ℂ} {δ : ℝ} {F : Set G}
    (hα : Continuous α) (hs : HasCompactSupport α) (hδ : 0 < δ) (hF : IsFundamentalDomain Γ F μ)
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ U ∈ 𝓝 (1 : G), ∀ ψ : G → ℂ, Continuous ψ → (∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) →
      (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) →
      (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1 → ∀ y ∈ U, ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ ≤ η := by
  set d : ℝ≥0∞ := ENNReal.ofReal δ with hd
  have hd0 : d ≠ 0 := by simpa [hd] using hδ
  have hdt : d ≠ ∞ := ENNReal.ofReal_ne_top
  have hd2 : d ^ 2 ≠ 0 := pow_ne_zero 2 hd0
  have hd2t : d ^ 2 ≠ ∞ := ENNReal.pow_ne_top hdt
  set ε : ℝ≥0∞ := min 1 (η * d ^ 2) with hε
  have hε0 : 0 < ε := lt_min one_pos (ENNReal.mul_pos hη.ne' hd2)
  have hε1 : ε ≤ 1 := min_le_left _ _
  refine ⟨_, eventually_lintegral_translate_le μ hα hs hε0, ?_⟩
  rintro ψ hψ hl ⟨s, hsδ, hrep⟩ hn y hy
  have hy' : ∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ ≤ ε := hy
  have hA : ∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ ≠ ∞ := (hy'.trans hε1).trans_lt ENNReal.one_lt_top |>.ne
  have hb := sq_mean_translate_le μ Γ hF hα hs hψ hl hrep hn y hA
  have hds : d ≤ ‖s‖ₑ := by
    rw [hd, ← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal hsδ
  have hεε : ε ^ 2 ≤ η * d ^ 2 := by
    calc ε ^ 2 = ε * ε := sq ε
      _ ≤ 1 * ε := by gcongr
      _ = ε := one_mul ε
      _ ≤ η * d ^ 2 := min_le_right _ _
  have hfin : d ^ 2 * ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ ≤ d ^ 2 * η := by
    calc d ^ 2 * ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ
        ≤ ‖s‖ₑ ^ 2 * ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ := by gcongr
      _ ≤ (∫⁻ w, ‖α (y⁻¹ * w) - α w‖ₑ ∂μ) ^ 2 := hb
      _ ≤ ε ^ 2 := by gcongr
      _ ≤ η * d ^ 2 := hεε
      _ = d ^ 2 * η := mul_comm _ _
  exact (ENNReal.mul_le_mul_iff_right hd2 hd2t).1 hfin

end GlobalTheory.CompanionTheory.Conc.WeightedCauchySchwarzLintegral

theorem GlobalTheory.CompanionTheory.Conc.translate_sq_mean_close : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] (α : GA E N → ℂ) (δ : ℝ) (F : Set (GA E N)), Continuous α → HasCompactSupport α → 0 < δ →
  IsFundamentalDomain (latticeGL E N) F μ → ∀ η : ℝ≥0∞, 0 < η → ∃ U ∈ 𝓝 (1 : GA E N), ∀ ψ : GA E N → ℂ, Continuous ψ →
  (∀ γ ∈ latticeGL E N, ∀ g, ψ (γ * g) = ψ g) → (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) →
  (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1 → ∀ y ∈ U, ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ ≤ η := by
  intro E _ _ _ N _ _ μ _ α δ F hα hs hδ hF η hη
  haveI : μ.IsMulRightInvariant := GlobalTheory.T.haar_right_invariant_totally_complex E N μ
  haveI : Countable (latticeGL E N) := GlobalTheory.DiscreteUnit.countable_latticeGL
  set_option synthInstance.maxHeartbeats 200000 in
    exact GlobalTheory.CompanionTheory.Conc.WeightedCauchySchwarzLintegral.exists_nhds_sq_mean_le μ (latticeGL E N) hα hs hδ hF hη
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelEigenfunctionEquicontinuousStatement
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_eigenfunction_equicontinuous : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] (α : GA E N → ℂ) (δ : ℝ) (F : Set (GA E N)), Continuous α → HasCompactSupport α → 0 < δ →
  IsFundamentalDomain (latticeGL E N) F μ → ∀ η : ℝ≥0∞, 0 < η → ∃ U ∈ 𝓝 (1 : GA E N), ∀ ψ : GA E N → ℂ, Continuous ψ →
  (∀ γ ∈ latticeGL E N, ∀ g, ψ (γ * g) = ψ g) → (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) →
  (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1 → ∀ y ∈ U, ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ ≤ η := by
  first | exact @GlobalTheory.CompanionTheory.Conc.translate_sq_mean_close | exact GlobalTheory.CompanionTheory.Conc.translate_sq_mean_close | (intros; apply GlobalTheory.CompanionTheory.Conc.translate_sq_mean_close <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitIntegralInvariantE0
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitIntegralInvariantE0
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StabInv

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

section Alg

variable {K : Type} [CommRing K] {M : ℕ}

def lowerB (U : Matrix (Fin (M + 2)) (Fin (M + 2)) K) : Matrix (Fin M) (Fin M) K :=
  Matrix.of fun i j => U i.succ.succ j.succ.succ

theorem col_zero {U : Matrix (Fin (M + 2)) (Fin (M + 2)) K}
    (h : U.mulVec (Fin.cons 1 fun _ => 0) = Fin.cons 1 fun _ => 0) (i : Fin (M + 2)) :
    U i 0 = (Fin.cons 1 (fun _ => 0) : Fin (M + 2) → K) i := by
  have := congrFun h i
  rw [← this]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem row_one (s : K →+* K) (A : Matrix (Fin M) (Fin M) K)
    {U : Matrix (Fin (M + 2)) (Fin (M + 2)) K} (hU : cT s U * hypOne A * U = hypOne A)
    (h0 : ∀ i, U i 0 = (Fin.cons 1 (fun _ => 0) : Fin (M + 2) → K) i) (j : Fin M) :
    U 1 j.succ.succ = 0 := by
  have h := congrFun (congrFun hU 0) j.succ.succ
  have h1 : U 1 0 = 0 := h0 1
  have hr : ∀ i : Fin M, U i.succ.succ 0 = 0 := fun i => h0 i.succ.succ
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, Fin.sum_univ_succ] at h
  simpa [hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest,
      hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest, h0 0, h1, hr] using h

theorem lowerB_isometry (s : K →+* K) (A : Matrix (Fin M) (Fin M) K)
    {U : Matrix (Fin (M + 2)) (Fin (M + 2)) K} (hU : cT s U * hypOne A * U = hypOne A)
    (h0 : ∀ i, U i 0 = (Fin.cons 1 (fun _ => 0) : Fin (M + 2) → K) i) :
    cT s (lowerB U) * A * lowerB U = A := by
  ext i j
  have h := congrFun (congrFun hU i.succ.succ) j.succ.succ
  have h1 : ∀ j : Fin M, U 1 j.succ.succ = 0 := row_one s A hU h0
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, Fin.sum_univ_succ] at h ⊢
  simpa [lowerB, hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest,
      hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest, h1] using h

theorem mulVec_cons (U : Matrix (Fin (M + 2)) (Fin (M + 2)) K)
    (h0 : ∀ i, U i 0 = (Fin.cons 1 (fun _ => 0) : Fin (M + 2) → K) i)
    (h1 : ∀ j : Fin M, U 1 j.succ.succ = 0) (a : K) (Y : Fin M → K) :
    U.mulVec (Fin.cons a (Fin.cons 0 Y)) =
      Fin.cons (a + ∑ i, U 0 i.succ.succ * Y i) (Fin.cons 0 ((lowerB U).mulVec Y)) := by
  have e1 : U 1 0 = 0 := h0 1
  have er : ∀ i : Fin M, U i.succ.succ 0 = 0 := fun i => h0 i.succ.succ
  have e0 : U 0 0 = 1 := h0 0
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, e0]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, e1, h1]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, er, lowerB]

theorem mulVec_consA {n : ℕ} (U : Matrix (Fin (M + 2)) (Fin (M + 2)) K)
    (hfix : U.mulVec (Fin.cons 1 fun _ => 0) = Fin.cons 1 fun _ => 0)
    (h0 : ∀ i, U i 0 = (Fin.cons 1 (fun _ => 0) : Fin (M + 2) → K) i)
    (h1 : ∀ j : Fin M, U 1 j.succ.succ = 0) (a : Fin 1 → Fin n → K) (Y : Fin n → Fin M → K) :
    (fun k => U.mulVec (consA a Y k)) =
      consA (a + fun _ j => ∑ i, U 0 i.succ.succ * Y j i) (fun j => (lowerB U).mulVec (Y j)) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simpa [consA] using hfix
  · simpa [consA] using mulVec_cons U h0 h1 (a 0 j) (Y j)

theorem map_hypOne {L : Type} [CommRing L] (f : K →+* L) (A : Matrix (Fin M) (Fin M) K) :
    (hypOne A).map f = hypOne (A.map f) := by
  ext i j
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
  all_goals
    simp [hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest,
      hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest]

end Alg

section Main

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem JR_hypOne (R : Type) [CommRing R] [Algebra F R] {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    JR (F := F) R (hypOne J) = hypOne (JR (F := F) R J) :=
  map_hypOne (inclR R) J

theorem exists_HA (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : J.det ≠ 0) {κ : Matrix (Fin M) (Fin M) (R ⊗[F] E)}
    (hκ : cT (sigR R σ) κ * JR (F := F) R J * κ = JR (F := F) R J) :
    ∃ h : HA R σ J, ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = κ := by
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ
  have hi : (J⁻¹).map (inclR (F := F) R) * JR (F := F) R J = 1 := by
    have h1 := congrArg (fun A : Matrix (Fin M) (Fin M) E => A.map (inclR (F := F) R)) (Matrix.nonsing_inv_mul J hu)
    simpa [JR, Matrix.map_mul, Matrix.map_one] using h1
  have hl : ((J⁻¹).map (inclR (F := F) R) * cT (sigR R σ) κ * JR (F := F) R J) * κ = 1 := by
    calc ((J⁻¹).map (inclR (F := F) R) * cT (sigR R σ) κ * JR (F := F) R J) * κ
        = (J⁻¹).map (inclR (F := F) R) * (cT (sigR R σ) κ * JR (F := F) R J * κ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hκ, hi]
  have hr := mul_eq_one_comm.mp hl
  let G : GL (Fin M) (R ⊗[F] E) := ⟨κ, _, hr, hl⟩
  have hG : G ∈ HR R σ J := hκ
  exact ⟨(⟨G, hG⟩ : HR R σ J), rfl⟩

end Main

theorem stageInt_eq_of_e0 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m₀ : Measure (Fin n → Fin M → R ⊗[F] E), (∀ h : HA R σ J, m₀.map (actW R σ J h) = m₀) → ∀ φ : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ g g' : HA R σ (hypOne J), actW R σ (hypOne J) g (e0 _ M) = actW R σ (hypOne J) g' (e0 _ M) → stageInt R σ J b lam m₀ φ g = stageInt R σ J b lam m₀ φ g' := by
  intro F E _ _ _ _ _ σ hcm M J hJ R _ _ _ _ _ hL n d b lam hlam m₀ hm₀ φ hφ g g' hgg
  haveI : IsTopologicalRing R := hL.1
  haveI : LocallyCompactSpace R := hL.2.1
  haveI : SecondCountableTopology R := hL.2.2.1
  haveI : T2Space R := hL.2.2.2.1
  obtain ⟨tK1, tK2, tK3, tK4, -, -, -, tK8, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  haveI := tK1
  haveI := tK2
  haveI := tK3
  haveI := tK4
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := tK8 n M
  haveI : BorelSpace (Fin 1 → Fin n → R ⊗[F] E) := tK8 1 n
  haveI : BorelSpace (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) := tK8 (n + 1) (M + 2)
  obtain ⟨-, hW, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hcm R d b lam hlam
  haveI := hW 1 n
  obtain ⟨-, -, -, -, -, hA⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm (M + 2) (hypOne J) (isHermND_hypOne σ hJ) R
  obtain ⟨-, -, -, -, -, hA'⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm M J hJ R
  obtain ⟨-, e1, em, -⟩ := hA 1
  obtain ⟨hc, -, hm, -⟩ := hA (n + 1)
  obtain ⟨hc', -, -, -⟩ := hA' n

  set u : HA R σ (hypOne J) := g⁻¹ * g' with hu_def
  have hg' : g' = g * u := by simp [hu_def]
  have hfix : actW R σ (hypOne J) u (e0 _ M) = e0 _ M := by
    rw [hu_def, em, ← hgg, ← em, inv_mul_cancel, e1]
  set U : Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E) :=
    (HA.mat R σ (hypOne J) u).val with hU_def
  have hfixV : U.mulVec (Fin.cons 1 fun _ => 0) = Fin.cons 1 fun _ => 0 := congrFun hfix 0
  have h0 := col_zero hfixV
  have hUu : cT (sigR R σ) U * hypOne (JR (F := F) R J) * U = hypOne (JR (F := F) R J) := by
    rw [← JR_hypOne]
    exact (show HR R σ (hypOne J) from u).2
  have h1 := row_one _ _ hUu h0
  obtain ⟨k, hk⟩ := exists_HA R σ hJ.2 (lowerB_isometry _ _ hUu h0)

  have hact : ∀ (a : Fin 1 → Fin n → R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E),
      actW R σ (hypOne J) u (consA a Y) =
        consA (a + fun _ j => ∑ i, U 0 i.succ.succ * Y j i) (actW R σ J k Y) := by
    intro a Y
    have := mulVec_consA U hfixV h0 h1 a Y
    have e : actW R σ J k Y = fun j => (lowerB U).mulVec (Y j) := by
      funext j
      simp only [actW, actTup, hk]
    rw [e, ← this]
    rfl

  let G : (Fin n → Fin M → R ⊗[F] E) → ℝ≥0∞ := fun Y =>
    ∫⁻ a, φ (actW R σ (hypOne J) g (consA a Y)) ∂(coordW R b lam 1 n)
  have hcons : Continuous fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) =>
      (consA p.2 p.1 : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) := by
    refine continuous_pi fun k => continuous_pi fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) k
    · refine Fin.cases ?_ (fun i => ?_) i <;> simpa [consA] using continuous_const
    · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
      · simp only [consA, Fin.cons_succ, Fin.cons_zero]
        fun_prop
      · simpa [consA] using continuous_const
      · simp only [consA, Fin.cons_succ]
        fun_prop
  have hGm : Measurable G := by
    have hf : Measurable fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) =>
        φ (actW R σ (hypOne J) g (consA p.2 p.1)) :=
      hφ.comp (hc.comp (continuous_const.prodMk hcons)).measurable
    exact hf.lintegral_prod_right'
  have hkm : Measurable (actW R σ J k : (Fin n → Fin M → R ⊗[F] E) → _) :=
    (hc'.comp (continuous_const.prodMk continuous_id)).measurable
  have hinner : ∀ Y, (∫⁻ a, φ (actW R σ (hypOne J) g' (consA a Y)) ∂(coordW R b lam 1 n)) =
      G (actW R σ J k Y) := by
    intro Y
    have : ∀ a, actW R σ (hypOne J) g' (consA a Y) =
        actW R σ (hypOne J) g (consA (a + fun _ j => ∑ i, U 0 i.succ.succ * Y j i) (actW R σ J k Y)) := by
      intro a
      rw [hg', hm, hact]
    simp only [this]
    exact lintegral_add_right_eq_self
      (fun a => φ (actW R σ (hypOne J) g (consA a (actW R σ J k Y)))) _
  show (∫⁻ Y, G Y ∂m₀) = ∫⁻ Y, (∫⁻ a, φ (actW R σ (hypOne J) g' (consA a Y)) ∂(coordW R b lam 1 n)) ∂m₀
  simp only [hinner]
  rw [← lintegral_map hGm hkm, hm₀ k]

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StabInv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitIntegralInvariantE0Statement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_integral_invariant_e0 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m₀ : Measure (Fin n → Fin M → R ⊗[F] E), (∀ h : HA R σ J, m₀.map (actW R σ J h) = m₀) → ∀ φ : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ g g' : HA R σ (hypOne J), actW R σ (hypOne J) g (e0 _ M) = actW R σ (hypOne J) g' (e0 _ M) → stageInt R σ J b lam m₀ φ g = stageInt R σ J b lam m₀ φ g' := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StabInv.stageInt_eq_of_e0 | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StabInv.stageInt_eq_of_e0 | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StabInv.stageInt_eq_of_e0 <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockMatrixMultiplicative
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockMatrixMultiplicative
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.IndexFormula

theorem relIndex_split {G H : Type*} [AddCommGroup G] [AddCommGroup H] (f : G →+ H)
    (A B : AddSubgroup G) (hAB : A ≤ B) :
    A.relIndex B = (A.map f).relIndex (B.map f) * A.relIndex (B ⊓ f.ker) := by
  have h1 : (A.map f).relIndex (B.map f) = (A ⊔ f.ker).relIndex B := by
    rw [← AddSubgroup.relIndex_comap, AddSubgroup.comap_map_eq]
  have h2 : (A ⊔ f.ker) ⊓ B = A ⊔ (B ⊓ f.ker) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hx1, hx2⟩ := AddSubgroup.mem_inf.mp hx
      obtain ⟨a, ha, k, hk, rfl⟩ := AddSubgroup.mem_sup.mp hx1
      refine AddSubgroup.mem_sup.mpr ⟨a, ha, k, AddSubgroup.mem_inf.mpr ⟨?_, hk⟩, rfl⟩
      have := B.sub_mem hx2 (hAB ha)
      simpa using this
    · refine sup_le (le_inf le_sup_left hAB) (le_inf ?_ inf_le_left)
      exact inf_le_right.trans le_sup_right
  have h3 : A.relIndex (A ⊔ (B ⊓ f.ker)) = A.relIndex (B ⊓ f.ker) :=
    AddSubgroup.relIndex_sup_left _ _
  have h4 := AddSubgroup.relIndex_mul_relIndex A ((A ⊔ f.ker) ⊓ B) B
    (le_inf le_sup_left hAB) inf_le_right
  rw [AddSubgroup.inf_relIndex_right, h2, h3] at h4
  rw [h1, ← h4, mul_comm]

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem blk_castSucc_castSucc {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) (a b : Fin m) :
    blk σ c u d a.castSucc b.castSucc = c a b := by
  simp [blk]

theorem blk_castSucc_last {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) (a : Fin m) :
    blk σ c u d a.castSucc (Fin.last m) = u a := by
  simp [blk]

theorem blk_mulVec_castSucc {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) (y : Fin (m + 1) → E) (i : Fin m) :
    (blk σ c u d).mulVec y i.castSucc
      = c.mulVec (fun j => y j.castSucc) i + y (Fin.last m) * u i := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, blk_castSucc_castSucc,
    blk_castSucc_last]
  ring

variable [NumberField E]

def proj (E : Type) [Field E] [NumberField E] (m : ℕ) :
    (Fin (m + 1) → E) →ₗ[𝓞 E] (Fin m → E) :=
  LinearMap.funLeft (𝓞 E) E Fin.castSucc

@[simp] theorem proj_apply (m : ℕ) (v : Fin (m + 1) → E) (i : Fin m) :
    proj E m v i = v i.castSucc := rfl

theorem snoc_mem_intVec {m : ℕ} {y : Fin m → E} (hy : y ∈ intVec E m) (o : 𝓞 E) :
    (Fin.snoc (α := fun _ => E) y (algebraMap (𝓞 E) E o) : Fin (m + 1) → E) ∈ intVec E (m + 1) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact ⟨o, by simp⟩
  · obtain ⟨p, hp⟩ := hy j
    exact ⟨p, by simp [hp]⟩

theorem proj_mem_intVec {m : ℕ} {y : Fin (m + 1) → E} (hy : y ∈ intVec E (m + 1)) :
    proj E m y ∈ intVec E m := fun i => hy i.castSucc

theorem map_proj_intVec (m : ℕ) : (intVec E (m + 1)).map (proj E m) = intVec E m := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact proj_mem_intVec hy
  · intro y hy
    refine ⟨_, snoc_mem_intVec hy 0, ?_⟩
    funext i
    simp

theorem intVec_le_lam {m : ℕ} (c : Matrix (Fin m) (Fin m) E) : intVec E m ≤ lam c := le_sup_left

theorem mulVec_mem_lam {m : ℕ} (c : Matrix (Fin m) (Fin m) E) {y : Fin m → E}
    (hy : y ∈ intVec E m) : c.mulVec y ∈ lam c :=
  Submodule.mem_sup_right ⟨y, hy, rfl⟩

theorem map_proj_lam {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) :
    (lam (blk σ c u d)).map (proj E m) = lam c ⊔ Submodule.span (𝓞 E) {u} := by
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨x, hx, z, ⟨y, hy, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨o, ho⟩ := hy (Fin.last m)
    have e : proj E m (x + (blk σ c u d).mulVecLin.restrictScalars (𝓞 E) y)
        = (proj E m x + c.mulVec (proj E m y)) + o • u := by
      funext i
      have := blk_mulVec_castSucc σ c u d y i
      simp only [proj_apply, Pi.add_apply, map_add (f := _), LinearMap.restrictScalars_apply,
        Matrix.mulVecLin_apply, Pi.smul_apply, Algebra.smul_def, ho]
      rw [this, add_assoc]
      rfl
    rw [e]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)))
    exact Submodule.add_mem _ (intVec_le_lam c (proj_mem_intVec hx))
      (mulVec_mem_lam c (proj_mem_intVec hy))
  · refine sup_le (sup_le ?_ ?_) ?_
    · rw [← map_proj_intVec m]
      exact Submodule.map_mono (intVec_le_lam _)
    · rintro _ ⟨y, hy, rfl⟩
      refine ⟨(blk σ c u d).mulVec (Fin.snoc (α := fun _ => E) y (algebraMap (𝓞 E) E 0)),
        mulVec_mem_lam _ (snoc_mem_intVec hy 0), ?_⟩
      funext i
      rw [proj_apply, blk_mulVec_castSucc]
      simp
    · rw [Submodule.span_singleton_le_iff_mem]
      refine ⟨(blk σ c u d).mulVec (Fin.snoc (α := fun _ => E) 0 (algebraMap (𝓞 E) E 1)),
        mulVec_mem_lam _ (snoc_mem_intVec (Submodule.zero_mem _) 1), ?_⟩
      funext i
      rw [proj_apply, blk_mulVec_castSucc]
      simp [show (fun _ : Fin m => (0 : E)) = 0 from rfl]

theorem relIndex_lam_sup {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) :
    (lam c).toAddSubgroup.relIndex (lam c ⊔ Submodule.span (𝓞 E) {u}).toAddSubgroup
      = Ideal.absNorm (tor c u) := by
  let φ : 𝓞 E →+ (Fin m → E) := (LinearMap.toSpanSingleton (𝓞 E) _ u).toAddMonoidHom
  have hsup : (lam c ⊔ Submodule.span (𝓞 E) {u}).toAddSubgroup
      = (lam c).toAddSubgroup ⊔ (⊤ : AddSubgroup (𝓞 E)).map φ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hb
      exact AddSubgroup.add_mem_sup ha ⟨t, trivial, rfl⟩
    · refine sup_le (fun x hx => Submodule.mem_sup_left hx) ?_
      rintro _ ⟨t, -, rfl⟩
      exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u))
  have hcomap : (lam c).toAddSubgroup.comap φ = (tor c u).toAddSubgroup := by
    ext t
    change t • u ∈ lam c ↔ t ∈ tor c u
    rw [tor, Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
  rw [hsup, AddSubgroup.relIndex_sup_left, ← AddSubgroup.relIndex_comap, hcomap,
    AddSubgroup.relIndex_top_right]
  exact (Ideal.absNorm_eq_index _).symm

def lastInc (E : Type) [Field E] [NumberField E] (m : ℕ) : E →+ (Fin (m + 1) → E) :=
  (LinearMap.single (𝓞 E) (fun _ : Fin (m + 1) => E) (Fin.last m)).toAddMonoidHom

theorem comap_lastInc_intVec (m : ℕ) :
    (intVec E (m + 1)).toAddSubgroup.comap (lastInc E m)
      = (1 : Submodule (𝓞 E) E).toAddSubgroup := by
  ext x
  change (Pi.single (Fin.last m) x : Fin (m + 1) → E) ∈ intVec E (m + 1) ↔
    x ∈ (1 : Submodule (𝓞 E) E)
  rw [Submodule.mem_one]
  constructor
  · intro h
    obtain ⟨o, ho⟩ := h (Fin.last m)
    exact ⟨o, by simpa using ho⟩
  · rintro ⟨o, rfl⟩ i
    by_cases hi : i = Fin.last m
    · subst hi
      exact ⟨o, by simp⟩
    · exact ⟨0, by simp [Pi.single_apply, hi]⟩

theorem map_lastInc_lastFib {m : ℕ} (C : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    (lastFib C).toAddSubgroup.map (lastInc E m)
      = (lam C).toAddSubgroup ⊓ (proj E m).toAddMonoidHom.ker := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine AddSubgroup.mem_inf.mpr ⟨hx, ?_⟩
    rw [AddMonoidHom.mem_ker]
    funext i
    simp [lastInc, Pi.single_apply, Fin.castSucc_ne_last]
  · intro hv
    obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.mp hv
    rw [AddMonoidHom.mem_ker] at h2
    have hv' : lastInc E m (v (Fin.last m)) = v := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [lastInc]
      · have := congrFun h2 j
        simp only [LinearMap.toAddMonoidHom_coe, proj_apply, Pi.zero_apply] at this
        simp [lastInc, Pi.single_apply, Fin.castSucc_ne_last, this]
    refine ⟨v (Fin.last m), ?_, hv'⟩
    change lastInc E m (v (Fin.last m)) ∈ lam C
    rw [hv']
    exact h1

theorem delta_blk (F E : Type) [Field F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (m : ℕ) (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E) :
    delta (blk σ c u d) = delta c * Ideal.absNorm (tor c u) * idx E (lastFib (blk σ c u d)) := by
  have hC := (GlobalTheory.T.delta_eq_lattice_index E (m + 1) (blk σ c u d)).2
  have hc := (GlobalTheory.T.delta_eq_lattice_index E m c).2
  have hsplit := relIndex_split (proj E m).toAddMonoidHom (intVec E (m + 1)).toAddSubgroup
    (lam (blk σ c u d)).toAddSubgroup (intVec_le_lam (blk σ c u d))
  have hA : (intVec E (m + 1)).toAddSubgroup.map (proj E m).toAddMonoidHom
      = (intVec E m).toAddSubgroup := by
    rw [← map_proj_intVec m]; rfl
  have hB : (lam (blk σ c u d)).toAddSubgroup.map (proj E m).toAddMonoidHom
      = (lam c ⊔ Submodule.span (𝓞 E) {u}).toAddSubgroup := by
    rw [← map_proj_lam σ c u d]; rfl
  have hmul := AddSubgroup.relIndex_mul_relIndex (intVec E m).toAddSubgroup
    (lam c).toAddSubgroup (lam c ⊔ Submodule.span (𝓞 E) {u}).toAddSubgroup
    (intVec_le_lam c) (fun x hx => Submodule.mem_sup_left hx)
  have hfib : (intVec E (m + 1)).toAddSubgroup.relIndex
      ((lam (blk σ c u d)).toAddSubgroup ⊓ (proj E m).toAddMonoidHom.ker)
      = idx E (lastFib (blk σ c u d)) := by
    rw [← map_lastInc_lastFib, ← AddSubgroup.relIndex_comap, comap_lastInc_intVec]
    rfl
  rw [hC, hc, hsplit, hA, hB, hfib, ← hmul, relIndex_lam_sup]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.IndexFormula
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockMatrixMultiplicativeStatement
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delta_block_matrix_multiplicative : ∀ (F E : Type) [Field F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (m : ℕ) (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E), delta (blk σ c u d) = delta c * Ideal.absNorm (tor c u) * idx E (lastFib (blk σ c u d)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.IndexFormula.delta_blk | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.IndexFormula.delta_blk | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.IndexFormula.delta_blk <;> assumption)
end
end
