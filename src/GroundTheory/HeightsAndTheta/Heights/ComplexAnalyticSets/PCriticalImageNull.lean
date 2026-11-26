module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCriticalImageNull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

noncomputable section

section Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def shrinkAlong (i0 : ι) (k : ι → ℝ) (δ : ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.id - (1 - δ) • (LinearMap.proj i0 : (ι → ℝ) →ₗ[ℝ] ℝ).smulRight k

omit [Fintype ι] [DecidableEq ι] in
theorem shrinkAlong_apply (i0 : ι) (k : ι → ℝ) (δ : ℝ) (z : ι → ℝ) :
    shrinkAlong i0 k δ z = z - ((1 - δ) * z i0) • k := by
  simp [shrinkAlong, smul_smul]

theorem det_shrinkAlong (i0 : ι) (k : ι → ℝ) (δ : ℝ) :
    LinearMap.det (shrinkAlong i0 k δ) = 1 - (1 - δ) * k i0 := by
  rw [← LinearMap.det_toMatrix']
  have hM : LinearMap.toMatrix' (shrinkAlong i0 k δ) =
      1 + Matrix.replicateCol Unit (-(1 - δ) • k) * Matrix.replicateRow Unit (Pi.single i0 (1 : ℝ)) := by
    ext i j
    simp only [LinearMap.toMatrix'_apply, shrinkAlong_apply, Matrix.add_apply, Matrix.one_apply,
      Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Finset.univ_unique, Finset.sum_singleton, Pi.single_apply]
    by_cases hij : i = j <;> by_cases hj : j = i0 <;> simp [hij, hj, eq_comm (a := i0)] <;> ring
  rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct, Pi.single_apply]
  ring

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

theorem hausdorffMeasure_image_le_of_approximatesLinearOn_of_mem_ker {f : (ι → ℝ) → F}
    {A : (ι → ℝ) →L[ℝ] F} {k : ι → ℝ} {i0 : ι} (hk : A k = 0) (hki : k i0 = 1) {δ : ℝ≥0}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {t : Set (ι → ℝ)} (ht : ApproximatesLinearOn f A t δ) :
    μH[Fintype.card ι] (f '' t) ≤
      ((Real.toNNReal (‖A‖ + 1 + ‖k‖) : ℝ≥0∞)) ^ (Fintype.card ι : ℝ) * ENNReal.ofReal δ *
        volume t := by
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hδ1' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  set T := shrinkAlong i0 k (δ : ℝ) with hTdef
  have hT : ∀ z, T z = z - ((1 - (δ : ℝ)) * z i0) • k := shrinkAlong_apply i0 k _
  have hTi : ∀ z, T z i0 = δ * z i0 := by
    intro z; rw [hT]; simp [hki]; ring
  let S : (ι → ℝ) → (ι → ℝ) := fun w => w + (((δ : ℝ)⁻¹ - 1) * w i0) • k
  have hST : ∀ x, S (T x) = x := by
    intro x
    simp only [S, hTi]
    have hδne : (δ : ℝ) ≠ 0 := hδ0'.ne'
    have : ((δ : ℝ)⁻¹ - 1) * (δ * x i0) = (1 - δ) * x i0 := by field_simp
    rw [this, hT, sub_add_cancel]
  have himg : f '' t = (f ∘ S) '' (T '' t) := by
    rw [image_image]; simp [hST]
  have hlip : LipschitzOnWith (Real.toNNReal (‖A‖ + 1 + ‖k‖)) (f ∘ S) (T '' t) := by
    refine LipschitzOnWith.of_dist_le' ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, hST, dist_eq_norm]
    rw [← map_sub]
    set v := x - y with hv
    have hAv : A v = A (T v) := by
      rw [hT, map_sub A v, map_smul, hk, smul_zero, sub_zero]
    have hsplit : (δ : ℝ) • v = (δ : ℝ) • T v + ((1 - δ) * T v i0) • k := by
      rw [hTi, hT]; ext j; simp; ring
    have hδv : (δ : ℝ) * ‖v‖ ≤ ‖T v‖ + ‖T v‖ * ‖k‖ := by
      have h1 : ‖(δ : ℝ) • T v‖ ≤ ‖T v‖ := by
        rw [norm_smul, Real.norm_of_nonneg hδ0'.le]
        exact mul_le_of_le_one_left (norm_nonneg _) hδ1'
      have h2 : ‖((1 - (δ : ℝ)) * T v i0) • k‖ ≤ ‖T v‖ * ‖k‖ := by
        rw [norm_smul, norm_mul, Real.norm_of_nonneg (by linarith)]
        have h3 : ‖T v i0‖ ≤ ‖T v‖ := norm_le_pi_norm _ _
        have h4 : (1 - (δ : ℝ)) * ‖T v i0‖ ≤ ‖T v‖ := by
          calc (1 - (δ : ℝ)) * ‖T v i0‖ ≤ 1 * ‖T v‖ :=
                mul_le_mul (by linarith) h3 (norm_nonneg _) zero_le_one
            _ = ‖T v‖ := one_mul _
        exact mul_le_mul_of_nonneg_right h4 (norm_nonneg _)
      calc (δ : ℝ) * ‖v‖ = ‖(δ : ℝ) • v‖ := by rw [norm_smul, Real.norm_of_nonneg hδ0'.le]
        _ ≤ ‖(δ : ℝ) • T v‖ + ‖((1 - (δ : ℝ)) * T v i0) • k‖ := by
          rw [hsplit]; exact norm_add_le _ _
        _ ≤ ‖T v‖ + ‖T v‖ * ‖k‖ := add_le_add h1 h2
    have happ := ht x hx y hy
    have hAT : ‖A (T v)‖ ≤ ‖A‖ * ‖T v‖ := A.le_opNorm _
    calc ‖f x - f y‖ = ‖(f x - f y - A v) + A v‖ := by rw [sub_add_cancel]
      _ ≤ ‖f x - f y - A v‖ + ‖A v‖ := norm_add_le _ _
      _ ≤ (δ : ℝ) * ‖v‖ + ‖A‖ * ‖T v‖ := by rw [hAv] at happ ⊢; exact add_le_add happ hAT
      _ ≤ (‖A‖ + 1 + ‖k‖) * ‖T v‖ := by nlinarith [hδv]
  rw [himg]
  calc μH[Fintype.card ι] ((f ∘ S) '' (T '' t))
      ≤ ((Real.toNNReal (‖A‖ + 1 + ‖k‖) : ℝ≥0∞)) ^ (Fintype.card ι : ℝ) *
          μH[Fintype.card ι] (T '' t) := hlip.hausdorffMeasure_image_le (by positivity)
    _ = ((Real.toNNReal (‖A‖ + 1 + ‖k‖) : ℝ≥0∞)) ^ (Fintype.card ι : ℝ) *
          (ENNReal.ofReal δ * volume t) := by
      rw [hausdorffMeasure_pi_real, Measure.addHaar_image_linearMap, hTdef, det_shrinkAlong, hki]
      congr 3
      rw [abs_of_pos (by linarith)]
      ring
    _ = _ := by rw [mul_assoc]

end Real

section Global

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

theorem exists_pos_hausdorffMeasure_image_le_of_not_injective (f : (ι → ℝ) → F)
    (A : (ι → ℝ) →L[ℝ] F) (hA : ¬ Function.Injective A) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ t : Set (ι → ℝ), ApproximatesLinearOn f A t δ →
      μH[Fintype.card ι] (f '' t) ≤ ε * volume t := by
  obtain ⟨a, b, hab, hne⟩ : ∃ a b, A a = A b ∧ a ≠ b := by
    simpa [Function.Injective, not_forall] using hA
  have hk0 : a - b ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨i0, hi0⟩ : ∃ i0, (a - b) i0 ≠ 0 := by
    simpa using Function.ne_iff.mp hk0
  set k : ι → ℝ := ((a - b) i0)⁻¹ • (a - b) with hkdef
  have hk : A k = 0 := by rw [hkdef, map_smul, map_sub, hab, sub_self, smul_zero]
  have hki : k i0 = 1 := by
    rw [hkdef, Pi.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hi0
  set K : ℝ≥0 := Real.toNNReal (‖A‖ + 1 + ‖k‖)
  set δ : ℝ≥0 := min 1 (ε / (K ^ Fintype.card ι + 1))
  have hδ0 : 0 < δ := lt_min one_pos (div_pos hε (by positivity))
  refine ⟨δ, hδ0, fun t ht => ?_⟩
  have key :=
    hausdorffMeasure_image_le_of_approximatesLinearOn_of_mem_ker hk hki hδ0 (min_le_left _ _) ht
  refine key.trans ?_
  have hKδ : K ^ Fintype.card ι * δ ≤ ε := by
    calc K ^ Fintype.card ι * δ ≤ (K ^ Fintype.card ι + 1) * (ε / (K ^ Fintype.card ι + 1)) := by
          gcongr
          · exact le_self_add
          · exact min_le_right _ _
      _ = ε := by
        rw [mul_div_assoc']
        exact mul_div_cancel_left₀ ε (by positivity)
  have hcoe : (K : ℝ≥0∞) ^ (Fintype.card ι : ℝ) * ENNReal.ofReal δ =
      ((K ^ Fintype.card ι * δ : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.rpow_natCast, ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul, ENNReal.coe_pow]
  rw [hcoe]
  gcongr

variable [SecondCountableTopology F]

theorem hausdorffMeasure_image_le_of_not_injective_ball {f : (ι → ℝ) → F} {s : Set (ι → ℝ)}
    {f' : (ι → ℝ) → (ι → ℝ) →L[ℝ] F} (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hinj : ∀ x ∈ s, ¬ Function.Injective (f' x)) (R : ℝ) (hs : s ⊆ closedBall 0 R)
    (ε : ℝ≥0) (εpos : 0 < ε) :
    μH[Fintype.card ι] (f '' s) ≤ ε * volume (closedBall (0 : ι → ℝ) R) := by
  rcases eq_empty_or_nonempty s with (rfl | h's)
  · simp
  have : ∀ A : (ι → ℝ) →L[ℝ] F, ∃ δ : ℝ≥0, 0 < δ ∧ (¬ Function.Injective A →
      ∀ t : Set (ι → ℝ), ApproximatesLinearOn f A t δ →
        μH[Fintype.card ι] (f '' t) ≤ ε * volume t) := by
    intro A
    by_cases hA : Function.Injective A
    · exact ⟨1, one_pos, fun h => absurd hA h⟩
    · obtain ⟨δ, hδ, h⟩ := exists_pos_hausdorffMeasure_image_le_of_not_injective f A hA εpos
      exact ⟨δ, hδ, fun _ => h⟩
  choose δ hδ using this
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, Af'⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' δ
      fun A => (hδ A).1.ne'
  calc
    μH[Fintype.card ι] (f '' s) ≤ μH[Fintype.card ι] (⋃ n, f '' (s ∩ t n)) := by
      rw [← image_iUnion, ← inter_iUnion]
      gcongr
      exact subset_inter Subset.rfl t_cover
    _ ≤ ∑' n, μH[Fintype.card ι] (f '' (s ∩ t n)) := measure_iUnion_le _
    _ ≤ ∑' n, (ε : ℝ≥0∞) * volume (s ∩ t n) := by
      gcongr with n
      obtain ⟨y, ys, hy⟩ := Af' h's n
      exact (hδ (A n)).2 (by rw [hy]; exact hinj y ys) _ (ht n)
    _ ≤ ε * ∑' n, volume (closedBall (0 : ι → ℝ) R ∩ t n) := by
      rw [ENNReal.tsum_mul_left]
      gcongr
    _ = ε * volume (⋃ n, closedBall (0 : ι → ℝ) R ∩ t n) := by
      rw [measure_iUnion]
      · exact pairwise_disjoint_mono t_disj fun n => inter_subset_right
      · intro n
        exact measurableSet_closedBall.inter (t_meas n)
    _ ≤ ε * volume (closedBall (0 : ι → ℝ) R) := by grw [← inter_iUnion, inter_subset_left]

theorem hausdorffMeasure_image_eq_zero_of_not_injective {f : (ι → ℝ) → F} {s : Set (ι → ℝ)}
    {f' : (ι → ℝ) → (ι → ℝ) →L[ℝ] F} (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hinj : ∀ x ∈ s, ¬ Function.Injective (f' x)) :
    μH[Fintype.card ι] (f '' s) = 0 := by
  suffices H : ∀ R, μH[Fintype.card ι] (f '' (s ∩ closedBall 0 R)) = 0 by
    rw [← nonpos_iff_eq_zero, ← iUnion_inter_closedBall_nat s 0]
    calc
      μH[Fintype.card ι] (f '' ⋃ n : ℕ, s ∩ closedBall 0 n)
          ≤ ∑' n : ℕ, μH[Fintype.card ι] (f '' (s ∩ closedBall 0 n)) := by
        rw [image_iUnion]; exact measure_iUnion_le _
      _ ≤ 0 := by simp only [H, tsum_zero, le_refl]
  intro R
  have hA : ∀ ε : ℝ≥0, 0 < ε →
      μH[Fintype.card ι] (f '' (s ∩ closedBall 0 R)) ≤ ε * volume (closedBall (0 : ι → ℝ) R) :=
    fun ε εpos => hausdorffMeasure_image_le_of_not_injective_ball
      (by exact fun x hx => (hf' x hx.1).mono inter_subset_left) (by exact fun x hx => hinj x hx.1) R
      inter_subset_right ε εpos
  have hB : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * volume (closedBall (0 : ι → ℝ) R)) (𝓝[>] 0)
      (𝓝 0) := by
    have : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * volume (closedBall (0 : ι → ℝ) R)) (𝓝 0)
        (𝓝 (((0 : ℝ≥0) : ℝ≥0∞) * volume (closedBall (0 : ι → ℝ) R))) :=
      ENNReal.Tendsto.mul_const (ENNReal.tendsto_coe.2 tendsto_id)
        (Or.inr measure_closedBall_lt_top.ne)
    simp only [zero_mul, ENNReal.coe_zero] at this
    exact Tendsto.mono_left this nhdsWithin_le_nhds
  rw [← nonpos_iff_eq_zero]
  apply ge_of_tendsto hB
  filter_upwards [self_mem_nhdsWithin]
  exact hA

end Global

theorem CriticalImageNull.proof : CriticalImageNull.Statement := by
  intro d n U f hU hf
  let b := Pi.basis (fun _ : Fin d => Complex.basisOneI)
  let e : ((Σ _ : Fin d, Fin 2) → ℝ) ≃L[ℝ] (Fin d → ℂ) :=
    b.equivFun.symm.toContinuousLinearEquiv
  have hcard : Fintype.card (Σ _ : Fin d, Fin 2) = 2 * d := by
    simp [Fintype.card_sigma, mul_comm]
  set C := {s | s ∈ U ∧ ¬ Function.Injective (fderiv ℂ f s)} with hC
  have himg : f '' C = (f ∘ e) '' (e ⁻¹' C) := by
    rw [image_comp, image_preimage_eq _ e.surjective]
  have key := hausdorffMeasure_image_eq_zero_of_not_injective (f := f ∘ e) (s := e ⁻¹' C)
    (f' := fun x => ((fderiv ℂ f (e x)).restrictScalars ℝ).comp (e : _ →L[ℝ] _)) ?_ ?_
  · rw [himg, ← hcard]
    exact key
  · intro x hx
    have hU' : U ∈ 𝓝 (e x) := hU.mem_nhds hx.1
    have h1 : HasFDerivAt f (fderiv ℂ f (e x)) (e x) := (hf.differentiableAt hU').hasFDerivAt
    exact ((h1.restrictScalars ℝ).comp x e.hasFDerivAt).hasFDerivWithinAt
  · intro x hx hinj
    apply hx.2
    intro a c hac
    have h2 := @hinj (e.symm a) (e.symm c) (by simpa using hac)
    simpa using congrArg e h2

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericPrimitive
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

noncomputable section

open MvPolynomial

def linearFormPoly {k : Type*} [Field k] {n : ℕ} (φ : (Fin n → k) →ₗ[k] k) : MvPolynomial (Fin n) k :=
  ∑ j, C (φ (Pi.single j 1)) * X j

theorem eval_linearFormPoly {k : Type*} [Field k] {n : ℕ} (φ : (Fin n → k) →ₗ[k] k) (c : Fin n → k) :
    eval c (linearFormPoly φ) = φ c := by
  have hc : c = ∑ j, c j • (Pi.single j 1 : Fin n → k) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hc]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [linearFormPoly, map_sum, mul_comm]

theorem GenericPrimitive.proof : GenericPrimitive.Statement := by
  intro k K L _ _ _ _ _ _ _ _ _ n x hx
  have hfin : Finite (IntermediateField K L) :=
    Field.finite_intermediateField_of_exists_primitive_element K L (Field.exists_primitive_element K L)
  have := Fintype.ofFinite (IntermediateField K L)
  classical

  let f : (Fin n → k) →ₗ[k] L := Fintype.linearCombination k x
  have hf : ∀ c, f c = ∑ j, c j • x j := fun c => Fintype.linearCombination_apply k x c

  let W : IntermediateField K L → Submodule k (Fin n → k) := fun M =>
    (M.toSubalgebra.toSubmodule.restrictScalars k).comap f
  have hW : ∀ M : IntermediateField K L, M ≠ ⊤ → W M < ⊤ := by
    intro M hM
    refine lt_top_iff_ne_top.2 fun htop => hM ?_
    have hxM : Set.range x ⊆ M := by
      rintro _ ⟨j, rfl⟩
      have hj : (Pi.single j 1 : Fin n → k) ∈ W M := htop ▸ Submodule.mem_top
      have : f (Pi.single j 1) = x j := by
        rw [hf]; simp [Pi.single_apply]
      simpa [W, this] using hj
    exact eq_top_iff.2 (hx ▸ IntermediateField.adjoin_le_iff.2 hxM)
  have hφ : ∀ M : IntermediateField K L, ∃ φ : (Fin n → k) →ₗ[k] k,
      M ≠ ⊤ → φ ≠ 0 ∧ W M ≤ LinearMap.ker φ := by
    intro M
    by_cases hM : M = ⊤
    · exact ⟨0, fun h => (h hM).elim⟩
    · obtain ⟨φ, h0, hle⟩ := (W M).exists_le_ker_of_lt_top (hW M hM)
      exact ⟨φ, fun _ => ⟨h0, hle⟩⟩
  choose φ hφ using hφ
  let S : Finset (IntermediateField K L) := Finset.univ.filter (· ≠ ⊤)
  refine ⟨∏ M ∈ S, linearFormPoly (φ M), ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro M hM
    have hM' : M ≠ ⊤ := (Finset.mem_filter.1 hM).2
    obtain ⟨c, hc⟩ : ∃ c, φ M c ≠ 0 := by
      by_contra h
      exact (hφ M hM').1 (LinearMap.ext fun c => by simpa using not_not.1 (not_exists.1 h c))
    intro h0
    apply hc
    rw [← eval_linearFormPoly, h0, map_zero]
  · intro c hc
    by_contra hne
    rw [map_prod, Finset.prod_ne_zero_iff] at hc
    have hmem : IntermediateField.adjoin K {∑ j, c j • x j} ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩
    apply hc _ hmem
    rw [eval_linearFormPoly]
    apply (hφ _ hne).2
    show f c ∈ IntermediateField.adjoin K {∑ j, c j • x j}
    rw [hf]
    exact IntermediateField.mem_adjoin_simple_self K _

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAnalyticGermComponents
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def AnalyticGermComponents.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ), IsAnalyticNear X w → w ∈ X →
    ∃ (n : ℕ) (Y : Fin n → Set (σ → ℂ)), (∀ i, IsAnalyticNear (Y i) w ∧ GermIrreducibleAt (Y i) w) ∧
      ∃ W ∈ 𝓝 w, X ∩ W = (⋃ i, Y i) ∩ W

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleFiniteGermProjectionOpenAt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def IrreducibleFiniteGermProjectionOpenAt.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X x → GermIrreducibleAt X x →
    (∃ W ∈ 𝓝 x, ∀ x' ∈ X ∩ W, A x' = A x → x' = x) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A x) → (∀ᶠ z in 𝓝 x, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A x), h y = 0) →
    ∀ V ∈ 𝓝 x, A '' (X ∩ V) ∈ 𝓝 (A x)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermProjectionImageNear
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def IrreducibleGermProjectionImageNear.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∃ N₀ ∈ 𝓝 w, ∀ x ∈ X ∩ N₀, ∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A x) →
      (∀ᶠ z in 𝓝 x, z ∈ X → h (A z) = 0) → ∀ᶠ y in 𝓝 (A x), h y = 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDiscrAdjoin
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

noncomputable section

def DiscrAdjoin.Statement : Prop :=
  ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (ℓ : L), IsIntegral R ℓ →
    IntermediateField.adjoin K {ℓ} = ⊤ →
      (minpoly R ℓ).natDegree = Module.finrank K L ∧ (minpoly R ℓ).discr ≠ 0 ∧
      ∀ z : L, IsIntegral R z → (minpoly R ℓ).discr • z ∈ Algebra.adjoin R {ℓ}

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteModuloEliminate
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable def zeroCoordinate {τ : Type} [DecidableEq τ] (c : τ) : (τ → ℂ) →L[ℂ] (τ → ℂ) :=
  ContinuousLinearMap.pi fun c' => if c' = c then 0 else ContinuousLinearMap.proj c'

theorem zeroCoordinate_apply {τ : Type} [DecidableEq τ] (c : τ) (y : τ → ℂ) (c' : τ) :
    zeroCoordinate c y c' = if c' = c then 0 else y c' := by
  by_cases h : c' = c <;> simp [zeroCoordinate, h]

def FiniteModuloEliminate.Statement : Prop :=
  ∀ (σ τ : Type) [Fintype σ] [Fintype τ] [DecidableEq τ] (x : σ → ℂ) (k : ℕ)
    (f : Fin k → (σ → ℂ) → ℂ) (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) (c : τ),
    (∀ i, AnalyticAt ℂ (f i) x) → IsFiniteModuloOver x f L →
    (∃ (r : ℕ) (h : Fin k → (σ → ℂ) → ℂ) (h' : τ → (σ → ℂ) → ℂ),
      (∀ i, AnalyticAt ℂ (h i) x) ∧ (∀ c', AnalyticAt ℂ (h' c') x) ∧
      ∀ᶠ z in 𝓝 x, (L z c - L x c) ^ r =
        ∑ i, h i z * f i z + ∑ c', h' c' z * (zeroCoordinate c (L z) c' - zeroCoordinate c (L x) c')) →
    IsFiniteModuloOver x f ((zeroCoordinate c).comp L)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionsGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def FiniteProjectionsContainOpen.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
      ∃ W : Set (Matrix (Fin d) (Fin n) ℂ), IsZariskiOpen W ∧ W.Nonempty ∧
        W ⊆ {A | IsFiniteProjection J A}

def FiniteProjectionsGeneric.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
      (∃ W : Set (Matrix (Fin d) (Fin n) ℂ), IsZariskiOpen W ∧ W.Nonempty ∧
        W ⊆ {A | IsFiniteProjection J A}) ∧
      (∀ D : Set (Matrix (Fin d) (Fin n) ℂ), D ⊆ orthoRows d n → orthoRows d n ⊆ closure D →
        ∃ A ∈ D, IsFiniteProjection J A) ∧
      (∀ (m : ℕ) (F : Fin m → Matrix.unitaryGroup (Fin n) ℂ),
        ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ (k : Fin m) (s : Fin d ↪ Fin n),
          IsFiniteProjection J (((F k : Matrix (Fin n) (Fin n) ℂ) * U).submatrix s id))

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.CutOffNear
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Set Topology MvPolynomial ComplexSets
open scoped ContDiff Manifold

theorem exists_cutoff_near {n : ℕ} {S U : Set (Fin n → ℂ)} (hS : IsClosed S) (hU : IsOpen U)
    (hSU : S ⊆ U) :
    ∃ χ : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ tsupport χ ⊆ U ∧
      ∃ V : Set (Fin n → ℂ), IsOpen V ∧ S ⊆ V ∧ ∀ x ∈ V, χ x = 1 := by
  obtain ⟨V, hV, hSV, hVU⟩ := normal_exists_closure_subset hS hU hSU
  obtain ⟨f, hf1, hf0, hf⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    𝓘(ℝ, Fin n → ℂ) (n := ⊤) hS (t := closure V) (hSV.trans (interior_maximal subset_closure hV))
  refine ⟨f, f.contMDiff.contDiff, hf, ?_, ?_⟩
  · refine (closure_minimal (fun x hx => ?_) isClosed_closure).trans hVU
    by_contra h
    exact hx (hf0 x h)
  · obtain ⟨W, hW, hSW, hWf⟩ := mem_nhdsSet_iff_exists.1 hf1
    exact ⟨W, hW, hSW, fun x hx => hWf hx⟩

theorem exists_cutoff_near_zeroSet {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hIU : zeroSet I ⊆ U) :
    ∃ χ : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ tsupport χ ⊆ U ∧
      ∃ V : Set (Fin n → ℂ), IsOpen V ∧ zeroSet I ⊆ V ∧ ∀ x ∈ V, χ x = 1 := by
  refine exists_cutoff_near ?_ hU hIU
  have : zeroSet I = ⋂ q ∈ I, {x : Fin n → ℂ | eval x q = 0} := by
    ext x
    simp [zeroSet]
  rw [this]
  exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicDerivNeZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Filter Topology

theorem InjectiveHolomorphicDerivNeZero.proof : InjectiveHolomorphicDerivNeZero.Statement := by
  intro D f hD hf hinj a ha hder
  have hDa : D ∈ 𝓝 a := hD.mem_nhds ha
  set g : ℂ → ℂ := fun z ↦ f z - f a with hg
  have hga : AnalyticAt ℂ g a := (hf.analyticAt hDa).sub analyticAt_const

  have hntop : analyticOrderAt g a ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have hev : ∀ᶠ z in 𝓝[≠] a, (g z = 0 ∧ z ∈ D) ∧ z ∈ ({a}ᶜ : Set ℂ) :=
      ((htop.and (hDa : ∀ᶠ z in 𝓝 a, z ∈ D)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    obtain ⟨z, ⟨hz0, hzD⟩, hza⟩ := hev.exists
    exact hza (hinj hzD ha (sub_eq_zero.mp hz0))
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hntop
  obtain ⟨u, hu, hua, hfac⟩ := hga.analyticOrderAt_eq_natCast.mp hn.symm
  simp only [smul_eq_mul] at hfac
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := hfac.self_of_nhds
    simp [hg] at this
    exact hua this.symm
  have hn1 : n ≠ 1 := by
    rintro rfl
    have hd : HasDerivAt (fun z ↦ (z - a) ^ 1 * u z) (u a) a := by
      have := ((hasDerivAt_id' a).sub_const a).mul hu.differentiableAt.hasDerivAt
      simp only [pow_one]
      exact this.congr_deriv (by simp)
    have : deriv g a = u a :=
      (EventuallyEq.deriv_eq (hfac : g =ᶠ[𝓝 a] fun z ↦ (z - a) ^ 1 * u z)).trans hd.deriv
    rw [hg, deriv_sub_const, hder] at this
    exact hua this.symm

  set c : ℂ := u a ^ ((n : ℂ)⁻¹) with hc
  set v : ℂ → ℂ := fun z ↦ c * (u z / u a) ^ ((n : ℂ)⁻¹) with hv
  have hva : AnalyticAt ℂ v a := analyticAt_const.mul
    ((hu.div analyticAt_const hua).cpow analyticAt_const (by simp [hua, Complex.one_mem_slitPlane]))
  have hvpow : ∀ z, v z ^ n = u z := by
    intro z
    rw [hv, mul_pow, hc, Complex.cpow_nat_inv_pow _ hn0, Complex.cpow_nat_inv_pow _ hn0]
    field_simp
  have hv0 : v a ≠ 0 := by
    intro h
    have := hvpow a
    rw [h, zero_pow hn0] at this
    exact hua this.symm
  set w : ℂ → ℂ := fun z ↦ (z - a) * v z with hw
  have hwd : HasDerivAt w (v a) a := by
    have := ((hasDerivAt_id' a).sub_const a).mul hva.differentiableAt.hasDerivAt
    exact this.congr_deriv (by simp)
  have hwa : w a = 0 := by simp [hw]
  have hgw : ∀ z, g z = (z - a) ^ n * u z → g z = w z ^ n := by
    intro z hz
    rw [hz, ← hvpow z, ← mul_pow]

  have hmap : 𝓝 (w a) ≤ map w (𝓝 a) := by
    have hwan : AnalyticAt ℂ w a := (analyticAt_id.sub analyticAt_const).mul hva
    refine hwan.eventually_constant_or_nhds_le_map_nhds.resolve_left ?_
    intro hconst
    have h1 : deriv w a = 0 := by
      rw [EventuallyEq.deriv_eq (hconst : w =ᶠ[𝓝 a] fun _ ↦ w a)]
      simp
    exact hv0 (hwd.deriv.symm.trans h1)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (hmap (image_mem_map (inter_mem hDa hfac)))
  rw [hwa] at hball
  have hk : 1 < n := by omega
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n) with hζ
  have hprim : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn0
  set t : ℂ := ((ε / 2 : ℝ) : ℂ) with ht
  have htn : ‖t‖ = ε / 2 := by rw [ht, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, norm_zero] at htn
    linarith
  obtain ⟨z₁, ⟨hz₁D, hz₁⟩, hw₁⟩ := hball (by
    rw [Metric.mem_ball, dist_zero_right, htn]; linarith)
  obtain ⟨z₂, ⟨hz₂D, hz₂⟩, hw₂⟩ := hball (show ζ * t ∈ Metric.ball 0 ε by
    rw [Metric.mem_ball, dist_zero_right, norm_mul, hprim.norm'_eq_one hn0, htn]; linarith)
  have hg₁ := hgw z₁ hz₁
  have hg₂ := hgw z₂ hz₂
  rw [hw₁] at hg₁
  rw [hw₂, mul_pow, hprim.pow_eq_one, one_mul] at hg₂
  have hf12 : f z₁ = f z₂ := by
    have : g z₁ = g z₂ := hg₁.trans hg₂.symm
    simpa [hg] using this
  have h12 := hinj hz₁D hz₂D hf12
  rw [h12, hw₂] at hw₁
  have : (ζ - 1) * t = 0 := by rw [sub_mul, one_mul, hw₁, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact hprim.ne_one hk (sub_eq_zero.mp h)
  · exact ht0 h

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PUnitaryZariskiDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial Matrix Complex

noncomputable section

namespace UnitaryZariskiDense

theorem eval_aeval_subst {σ τ : Type*} (F : σ → MvPolynomial τ ℂ) (p : MvPolynomial σ ℂ)
    (x : τ → ℂ) : eval x (aeval F p) = eval (fun i => eval x (F i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p i hp => rw [map_mul, map_mul, hp, aeval_X, map_mul, eval_X]

theorem polyEval_aeval_subst {σ : Type*} (F : σ → Polynomial ℂ) (p : MvPolynomial σ ℂ) (z : ℂ) :
    (aeval F p).eval z = eval (fun i => (F i).eval z) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem unit_circle_infinite : {z : ℂ | ‖z‖ = 1}.Infinite := by
  intro hfin
  have hsub : Polynomial.nthRootsFinset (hfin.toFinset.card + 1) (1 : ℂ) ⊆ hfin.toFinset := by
    intro z hz
    rw [Polynomial.mem_nthRootsFinset (Nat.succ_pos _)] at hz
    rw [Set.Finite.mem_toFinset]
    exact Complex.norm_eq_one_of_pow_eq_one hz (Nat.succ_ne_zero _)
  have hc := Finset.card_le_card hsub
  rw [(Complex.isPrimitiveRoot_exp (hfin.toFinset.card + 1) (Nat.succ_ne_zero _)).card_nthRootsFinset]
    at hc
  omega

theorem conj_diagonal_mem {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ} (hV : V ∈ unitaryGroup (Fin n) ℂ)
    {d : Fin n → ℂ} (hd : ∀ k, ‖d k‖ = 1) : V * diagonal d * star V ∈ unitaryGroup (Fin n) ℂ := by
  have hD : diagonal d ∈ unitaryGroup (Fin n) ℂ := by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext k
    simpa [Complex.mul_conj', hd k]
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hV hD) (Unitary.star_mem hV)

end UnitaryZariskiDense


open UnitaryZariskiDense in
theorem UnitaryZariskiDense.proof : UnitaryZariskiDense.Statement := by
  intro n p hp
  by_contra hall
  push Not at hall
  apply hp

  have herm : ∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian →
      eval (fun ij : Fin n × Fin n => H ij.1 ij.2) p = 0 := by
    intro H hH
    have hspec := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hspec
    set V : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hVdef
    have hV : V ∈ unitaryGroup (Fin n) ℂ := hH.eigenvectorUnitary.2
    have hentry : ∀ d : Fin n → ℂ,
        eval d (aeval (fun ij : Fin n × Fin n => ∑ k, C (V ij.1 k * star V k ij.2) * X k) p) =
          eval (fun ij : Fin n × Fin n => (V * diagonal d * star V) ij.1 ij.2) p := by
      intro d
      rw [eval_aeval_subst]
      refine congrArg (fun f => eval f p) (funext fun ij => ?_)
      rw [Matrix.mul_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, eval_C, eval_X, Matrix.mul_diagonal]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hr : aeval (fun ij : Fin n × Fin n => ∑ k, C (V ij.1 k * star V k ij.2) * X k) p = 0 :=
      funext_set (fun _ => {z : ℂ | ‖z‖ = 1}) (fun _ => unit_circle_infinite) fun d hd => by
        rw [hentry, map_zero]
        exact hall _ (conj_diagonal_mem hV fun k => hd k trivial)
    have h0 := hentry (RCLike.ofReal ∘ hH.eigenvalues)
    rw [hr, map_zero] at h0
    rw [h0]
    refine congrArg (fun f => eval f p) (funext fun ij => ?_)
    exact congrFun (congrFun hspec ij.1) ij.2

  have all : ∀ A : Matrix (Fin n) (Fin n) ℂ, eval (fun ij : Fin n × Fin n => A ij.1 ij.2) p = 0 := by
    intro A
    set g : Polynomial ℂ := aeval (fun ij : Fin n × Fin n =>
      Polynomial.C (A ij.1 ij.2) * (Polynomial.C (1 / 2) - Polynomial.C (I / 2) * Polynomial.X) +
        Polynomial.C (Aᴴ ij.1 ij.2) * (Polynomial.C (1 / 2) + Polynomial.C (I / 2) * Polynomial.X)) p
      with hgdef
    have hg : ∀ z : ℂ, g.eval z = eval (fun ij : Fin n × Fin n =>
        A ij.1 ij.2 * (1 / 2 - I / 2 * z) + Aᴴ ij.1 ij.2 * (1 / 2 + I / 2 * z)) p := by
      intro z
      rw [hgdef, polyEval_aeval_subst]
      refine congrArg (fun f => eval f p) (funext fun ij => ?_)
      simp
    have g0 : g = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
      rintro _ ⟨t, rfl⟩
      simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, hg]
      have hstar : star (1 / 2 - I / 2 * (t : ℂ)) = 1 / 2 + I / 2 * (t : ℂ) := by
        apply Complex.ext <;> (simp; try ring)
      have hM : ((1 / 2 - I / 2 * (t : ℂ)) • A + (1 / 2 + I / 2 * (t : ℂ)) • Aᴴ).IsHermitian := by
        unfold IsHermitian
        rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_conjTranspose,
          hstar, ← hstar, star_star, add_comm]
      have h := herm _ hM
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h
      rw [← h]
      refine congrArg (fun f => eval f p) (funext fun ij => ?_)
      ring
    have h := hg I
    rw [g0, Polynomial.eval_zero] at h
    rw [h]
    refine congrArg (fun f => eval f p) (funext fun ij => ?_)
    have h1 : (1 / 2 - I / 2 * I : ℂ) = 1 := by
      ring_nf
      rw [I_sq]
      norm_num
    have h2 : (1 / 2 + I / 2 * I : ℂ) = 0 := by
      ring_nf
      rw [I_sq]
      norm_num
    rw [h1, h2]
    ring

  exact MvPolynomial.funext fun x => by
    simpa using all (Matrix.of fun i j => x (i, j))

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelExists
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def NormalModelExists.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime → Nonempty (NormalModel J)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelProper
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def NormalModelProper.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (M : NormalModel J) (K : Set (Fin n → ℂ)),
    Bornology.IsBounded K →
      Bornology.IsBounded {w : Fin n ⊕ Fin M.m → ℂ | w ∈ zeroSetIn M.ideal ∧ firstCoords w ∈ K}

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInjectiveHolomorphicInverse
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def InjectiveHolomorphicInverse.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin k → ℂ),
    IsOpen U → DifferentiableOn ℂ f U → Set.InjOn f U →
      IsOpen (f '' U) ∧
        ∃ g : (Fin k → ℂ) → Fin k → ℂ, DifferentiableOn ℂ g (f '' U) ∧ ∀ t ∈ U, g (f t) = t

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIsolatedFibreNear
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def IsolatedFibreNear.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    ∃ N₀ ∈ 𝓝 w, ∀ x ∈ X ∩ N₀, ∃ W ∈ 𝓝 x, ∀ x' ∈ X ∩ W, A x' = A x → x' = x

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermFiniteProjection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def GermFiniteProjection.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ), IsAnalyticNear X w → GermIrreducibleAt X w →
    ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
      (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) ∧
      ∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteGermProjectionOpenAt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def FiniteGermProjectionOpenAt.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X x →
    (∃ W ∈ 𝓝 x, ∀ x' ∈ X ∩ W, A x' = A x → x' = x) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A x) → (∀ᶠ z in 𝓝 x, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A x), h y = 0) →
    ∀ V ∈ 𝓝 x, A '' (X ∩ V) ∈ 𝓝 (A x)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalRiemannExtensionLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def NormalRiemannExtensionLocal.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial σ ℂ) (w : σ → ℂ)
    (U : Set (σ → ℂ)) (f : (σ → ℂ) → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → h ∉ I → w ∈ zeroSetIn I → U ∈ 𝓝 w →
    HolomorphicOnSubset f ((zeroSetIn I ∩ U) \ {z | eval z h = 0}) →
    Bornology.IsBounded (f '' ((zeroSetIn I ∩ U) \ {z | eval z h = 0})) →
    ∃ V : Set (σ → ℂ), IsOpen V ∧ w ∈ V ∧ V ⊆ U ∧ ∃ F : (σ → ℂ) → ℂ, DifferentiableOn ℂ F V ∧
      Set.EqOn F f ((zeroSetIn I ∩ V) \ {z | eval z h = 0})

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
