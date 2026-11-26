module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeLEntireAndNonzeroAtOneHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeThetaKernelPoissonSummation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchFactorMulPSeriesEqIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckePartialLSeriesEntireBoundedStrips
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaplaceIntegralEntireBoundedInVerticalStrips
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaplaceIntegralEntireBoundedInVerticalStrips
open NumberField MeasureTheory

noncomputable section

namespace GlobalTheory.LaplaceStrip

theorem norm_integrand {α : Type} (ℓ : α → ℝ) (g : α → ℂ) (s : ℂ) (x : α) :
    ‖g x * Complex.exp (s * (ℓ x : ℂ))‖ = ‖g x‖ * Real.exp (s.re * ℓ x) := by
  rw [norm_mul, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re]

theorem laplace_entire_boundedInStrips {α : Type} [MeasurableSpace α] (μ : MeasureTheory.Measure α) (ℓ : α → ℝ) (g : α → ℂ)
    (hℓ : Measurable ℓ) (hg : MeasureTheory.AEStronglyMeasurable g μ) (hpos : ∀ᵐ x ∂μ, 0 ≤ ℓ x)
    (hint : ∀ σ : ℝ, MeasureTheory.Integrable (fun x => ‖g x‖ * Real.exp (σ * ℓ x)) μ) :
    Differentiable ℂ (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) := by
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun x => g x * Complex.exp (s * (ℓ x : ℂ))) μ := fun s =>
    hg.mul (by fun_prop : Measurable fun x => Complex.exp (s * (ℓ x : ℂ))).aestronglyMeasurable
  have hI : ∀ s : ℂ, Integrable (fun x => g x * Complex.exp (s * (ℓ x : ℂ))) μ := fun s =>
    (hint s.re).mono' (hmeas s) (Filter.Eventually.of_forall fun x => (norm_integrand ℓ g s x).le)
  refine ⟨fun s₀ => ?_, fun a b _ => ⟨∫ x, ‖g x‖ * Real.exp (b * ℓ x) ∂μ, fun s _ hsb => ?_⟩⟩
  · have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun s x => g x * Complex.exp (s * (ℓ x : ℂ)))
      (F' := fun s x => g x * (Complex.exp (s * (ℓ x : ℂ)) * (1 * (ℓ x : ℂ))))
      (x₀ := s₀) (bound := fun x => ‖g x‖ * Real.exp ((s₀.re + 2) * ℓ x)) (Metric.ball_mem_nhds s₀ one_pos)
      (Filter.Eventually.of_forall hmeas) (hI s₀)
      (hg.mul (by fun_prop : Measurable fun x =>
        Complex.exp (s₀ * (ℓ x : ℂ)) * (1 * (ℓ x : ℂ))).aestronglyMeasurable)
      ?_ (hint _) ?_
    · exact key.2.differentiableAt
    · filter_upwards [hpos] with x hx s hs
      have hre : s.re ≤ s₀.re + 1 := by
        have h1 : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
        have h2 : ‖s - s₀‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hs
        have h3 := (abs_le.mp h1).2
        simp only [Complex.sub_re] at h3
        linarith
      rw [one_mul, ← mul_assoc, norm_mul, norm_integrand, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
      have e1 : Real.exp (s.re * ℓ x) ≤ Real.exp ((s₀.re + 1) * ℓ x) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hre hx)
      have e2 : ℓ x ≤ Real.exp (ℓ x) := by linarith [Real.add_one_le_exp (ℓ x)]
      have e3 : Real.exp ((s₀.re + 2) * ℓ x) = Real.exp ((s₀.re + 1) * ℓ x) * Real.exp (ℓ x) := by
        rw [← Real.exp_add]; ring_nf
      rw [e3, mul_assoc]
      gcongr
    · exact Filter.Eventually.of_forall fun x s _ => by
        have := (((hasDerivAt_id s).mul_const (ℓ x : ℂ)).cexp).const_mul (g x)
        simpa using this
  · refine norm_integral_le_of_norm_le (hint b) ?_
    filter_upwards [hpos] with x hx
    rw [norm_integrand]
    gcongr

end GlobalTheory.LaplaceStrip
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaplaceIntegralEntireBoundedInVerticalStripsStatement
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laplace_integral_entire_boundedInVerticalStrips : ∀ {α : Type} [MeasurableSpace α] (μ : MeasureTheory.Measure α) (ℓ : α → ℝ) (g : α → ℂ), Measurable ℓ → MeasureTheory.AEStronglyMeasurable g μ → (∀ᵐ x ∂μ, 0 ≤ ℓ x) → (∀ σ : ℝ, MeasureTheory.Integrable (fun x => ‖g x‖ * Real.exp (σ * ℓ x)) μ) → Differentiable ℂ (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) := by
  first | exact @GlobalTheory.LaplaceStrip.laplace_entire_boundedInStrips | exact GlobalTheory.LaplaceStrip.laplace_entire_boundedInStrips | (intros; apply GlobalTheory.LaplaceStrip.laplace_entire_boundedInStrips <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMeasurablePartitionOfUnityUnitLogTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMeasurablePartitionOfUnityUnitLogTranslate
open NumberField MeasureTheory
open scoped ContDiff

noncomputable section

namespace GlobalTheory
namespace UnitLogPartition

open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace

theorem exists_nonneg_hasSum_lattice_translates (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ η : V → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ (∀ z, 0 ≤ η z) ∧
      ∀ y, HasSum (fun l : L => η (y + l)) 1 := by
  obtain ⟨R, hR, hcov⟩ := GlobalTheory.exists_radius_lattice_translate_norm_le V L
  let b : ContDiffBump (0 : V) := ⟨R, R + 1, hR, by linarith⟩
  have hφc : HasCompactSupport (b : V → ℝ) := b.hasCompactSupport
  have hφs : ContDiff ℝ ∞ (b : V → ℝ) := b.contDiff
  have hlf := GlobalTheory.PeriodicPartition.locallyFinite_support_translate L b hφc
  set S : V → ℝ := fun z => ∑ᶠ l : L, b (z + l) with hS
  have hSs : ContDiff ℝ ∞ S := by
    rw [← contMDiff_iff_contDiff]
    refine contMDiff_finsum (f := fun (l : L) (z : V) => b (z + l)) (fun l => ?_) hlf
    rw [contMDiff_iff_contDiff]
    exact hφs.comp (contDiff_id.add contDiff_const)
  have hSp : ∀ (l : L) z, S (z + l) = S z := by
    intro l z
    show ∑ᶠ m : L, b (z + l + m) = ∑ᶠ m : L, b (z + m)
    rw [← finsum_comp_equiv (Equiv.addLeft l) (f := fun m : L => b (z + m))]
    simp [add_assoc]
  have hSpos : ∀ z, 0 < S z := by
    intro z
    obtain ⟨l, hl⟩ := hcov z
    have h1 := single_le_finsum (f := fun l : L => b (z + l)) l (hlf.point_finite z)
      (fun l => b.nonneg)
    have h2 : b (z + l) = 1 := b.one_of_mem_closedBall (by simpa using hl)
    simp only [h2] at h1
    exact lt_of_lt_of_le one_pos h1
  refine ⟨fun z => b z / S z, hφs.div hSs fun z => (hSpos z).ne', ?_,
    fun z => div_nonneg b.nonneg (hSpos z).le, fun y => ?_⟩
  · simp only [div_eq_mul_inv]
    exact hφc.mul_right
  · simp only [hSp]
    have hfin : (Function.support fun l : L => b (y + l)).Finite := hlf.point_finite y
    have h1 : HasSum (fun l : L => b (y + l)) (S y) := by
      have hs : Summable (fun l : L => b (y + l)) := summable_of_hasFiniteSupport hfin
      have := hs.hasSum
      rwa [tsum_eq_finsum hfin] at this
    have := h1.div_const (S y)
    rwa [div_self (hSpos y).ne'] at this

variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I] {φ : I → K →+* ℂ}

def idx (hφ : GlobalTheory.CMVal.IsCMType φ) (w : InfinitePlace K) : I := (hφ w.embedding).exists.choose

theorem idx_spec (hφ : GlobalTheory.CMVal.IsCMType φ) (w : InfinitePlace K) :
    w.embedding = φ (idx hφ w) ∨ w.embedding = ComplexEmbedding.conjugate (φ (idx hφ w)) :=
  (hφ w.embedding).exists.choose_spec

theorem apply_eq_norm (hφ : GlobalTheory.CMVal.IsCMType φ) (w : InfinitePlace K) (x : K) :
    w x = ‖φ (idx hφ w) x‖ := by
  rcases idx_spec hφ w with h | h
  · rw [← norm_embedding_eq, h]
  · rw [← norm_embedding_eq, h, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]

theorem idx_surjective (hφ : GlobalTheory.CMVal.IsCMType φ) (i : I) : ∃ w, idx hφ w = i := by
  refine ⟨InfinitePlace.mk (φ i), ?_⟩
  exact (hφ (InfinitePlace.mk (φ i)).embedding).unique (idx_spec hφ _) (embedding_mk_eq (φ i))

theorem ulog_idx [_root_.NumberField.IsTotallyComplex K] (hφ : GlobalTheory.CMVal.IsCMType φ) (u : (𝓞 K)ˣ) (w : InfinitePlace K) :
    GlobalTheory.HeckeTheta.ulog φ u (idx hφ w) = w.mult * Real.log (w (u : K)) := by
  unfold GlobalTheory.HeckeTheta.ulog
  rw [(IsTotallyComplex.isComplex w).mult_eq_two, ← apply_eq_norm hφ, Real.log_pow]

theorem sum_ulog_idx [_root_.NumberField.IsTotallyComplex K] (hφ : GlobalTheory.CMVal.IsCMType φ) (u : (𝓞 K)ˣ) :
    ∑ w : InfinitePlace K, GlobalTheory.HeckeTheta.ulog φ u (idx hφ w) = 0 := by
  simp only [ulog_idx hφ]
  exact sum_mult_mul_log u

def mean (hφ : GlobalTheory.CMVal.IsCMType φ) (y : I → ℝ) : ℝ :=
  (∑ w : InfinitePlace K, y (idx hφ w)) / Fintype.card (InfinitePlace K)

def proj (hφ : GlobalTheory.CMVal.IsCMType φ) (y : I → ℝ) : logSpace K :=
  fun w => y (idx hφ w.1) - mean hφ y

theorem proj_add_ulog [_root_.NumberField.IsTotallyComplex K] (hφ : GlobalTheory.CMVal.IsCMType φ) (y : I → ℝ) (u : (𝓞 K)ˣ) :
    proj hφ (y + GlobalTheory.HeckeTheta.ulog φ u) = proj hφ y + logEmbedding K (Additive.ofMul u) := by
  funext w
  have hm : mean hφ (y + GlobalTheory.HeckeTheta.ulog φ u) = mean hφ y := by
    unfold mean
    simp only [Pi.add_apply, Finset.sum_add_distrib, sum_ulog_idx hφ, add_zero]
  simp only [proj, hm, Pi.add_apply, logEmbedding_component, ← ulog_idx hφ]
  ring

theorem continuous_proj (hφ : GlobalTheory.CMVal.IsCMType φ) : Continuous (proj hφ) := by
  unfold proj mean
  fun_prop

end UnitLogPartition


open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace UnitLogPartition in
theorem exists_measurable_nonneg_hasSum_ulog_translates : ∀ (K : Type) [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ →
    ∃ p : (I → ℝ) → ℝ, Measurable p ∧ (∀ y, 0 ≤ p y) ∧
      (∀ y, HasSum (fun u : (NumberField.RingOfIntegers K)ˣ => p (y + GlobalTheory.HeckeTheta.ulog φ u)) 1) ∧
      ∃ R : ℝ, ∀ y, p y ≠ 0 → ∀ i j, y i - y j ≤ R := by
  classical
  intro K _ _ _ I _ φ hφ
  obtain ⟨η, hη, hc, h0, hs⟩ := exists_nonneg_hasSum_lattice_translates (logSpace K) (unitLattice K)
  refine ⟨fun y => η (proj hφ y) / Nat.card (torsion K), ?_, ?_, ?_, ?_⟩
  · exact ((hη.continuous.comp (continuous_proj hφ)).div_const _).measurable
  · intro y
    exact div_nonneg (h0 _) (Nat.cast_nonneg _)
  · intro y
    have h1 := ((Additive.ofMul.trans (logEmbeddingEquiv K).toEquiv).hasSum_iff).mpr (hs (proj hφ y))
    have h2 := GlobalTheory.UnitPartition.hasSum_quot (torsion K) _ _ h1
    convert h2 using 2 with u
    beta_reduce
    rw [proj_add_ulog hφ]
    rfl
  · obtain ⟨ρ, hρ⟩ := hc.isCompact.isBounded.exists_norm_le
    set n : ℝ := (Fintype.card (InfinitePlace K) : ℝ) with hn_def
    refine ⟨2 * (n * |ρ|), fun y hy i j => ?_⟩
    have hη0 : η (proj hφ y) ≠ 0 := fun h => hy (by simp [h])
    have hn : ‖proj hφ y‖ ≤ ρ := hρ _ (subset_tsupport _ hη0)
    set d : InfinitePlace K → ℝ := fun w => y (idx hφ w) - mean hφ y with hd
    have hn1 : (1 : ℝ) ≤ n := by
      rw [hn_def]; exact Nat.one_le_cast.mpr (Fintype.card_pos : 0 < Fintype.card (InfinitePlace K))
    have hsub : ∀ w : {w : InfinitePlace K // w ≠ w₀}, |d w.1| ≤ |ρ| := fun w =>
      ((norm_le_pi_norm (proj hφ y) w).trans hn).trans (le_abs_self ρ)
    have hsum : ∑ w, d w = 0 := by
      have hn0 : n ≠ 0 := by positivity
      simp only [hd, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mean]
      rw [← hn_def, mul_div_cancel₀ _ hn0, sub_self]
    have hall : ∀ w, |d w| ≤ n * |ρ| := by
      intro w
      by_cases hw : w = w₀
      · rw [hw]
        rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hsum
        rw [eq_neg_of_add_eq_zero_left hsum, abs_neg]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_card_nsmul _ _ |ρ| fun v _ => hsub v).trans ?_
        rw [nsmul_eq_mul]
        gcongr
        rw [Finset.card_univ, hn_def]
        exact_mod_cast Fintype.card_subtype_le _
      · exact (hsub ⟨w, hw⟩).trans (le_mul_of_one_le_left (abs_nonneg _) hn1)
    obtain ⟨v, rfl⟩ := idx_surjective hφ i
    obtain ⟨v', rfl⟩ := idx_surjective hφ j
    have e : y (idx hφ v) - y (idx hφ v') = d v - d v' := by simp [hd]
    rw [e]
    linarith [le_abs_self (d v), neg_abs_le (d v'), hall v, hall v']

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMeasurablePartitionOfUnityUnitLogTranslateStatement
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_measurable_partitionOfUnity_unitLogTranslates : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∃ p : (I → ℝ) → ℝ, Measurable p ∧ (∀ y, 0 ≤ p y) ∧ (∀ y, HasSum (fun u : (NumberField.RingOfIntegers K)ˣ => p (y + GlobalTheory.HeckeTheta.ulog φ u)) 1) ∧ ∃ R : ℝ, ∀ y, p y ≠ 0 → ∀ i j, y i - y j ≤ R := by
  first | exact @GlobalTheory.exists_measurable_nonneg_hasSum_ulog_translates | exact GlobalTheory.exists_measurable_nonneg_hasSum_ulog_translates | (intros; apply GlobalTheory.exists_measurable_nonneg_hasSum_ulog_translates <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicBoundedGaussianSummableCmType
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicBoundedGaussianSummableCmType
open NumberField MeasureTheory

noncomputable section

namespace GlobalTheory.HeckeLat

variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]

theorem exists_one_le_norm {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) {α : 𝓞 K} (hα : α ≠ 0) :
    ∃ i, 1 ≤ ‖φ i (α : K)‖ := by
  by_contra h
  push_neg at h
  have hlt : ∀ w : InfinitePlace K, w (α : K) < 1 := by
    intro w
    obtain ⟨i, hi, -⟩ := hφ w.embedding
    rw [← InfinitePlace.norm_embedding_eq]
    rcases hi with hi | hi
    · rw [hi]; exact h i
    · rw [hi, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]; exact h i
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  exact absurd (InfinitePlace.one_le_of_lt_one hα (fun z _ => hlt z)) (not_le.2 (hlt w))

theorem one_le_norm_emb {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) {α : 𝓞 K}
    (hα : GlobalTheory.HeckeTheta.emb φ (α : K) ≠ 0) : 1 ≤ ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ := by
  have h0 : α ≠ 0 := by
    rintro rfl
    apply hα
    funext i
    simp [GlobalTheory.HeckeTheta.emb]
  obtain ⟨i, hi⟩ := exists_one_le_norm hφ h0
  exact hi.trans (norm_le_pi_norm (GlobalTheory.HeckeTheta.emb φ (α : K)) i)

def embHom (φ : I → K →+* ℂ) : 𝓞 K →+ (I → ℂ) where
  toFun α := GlobalTheory.HeckeTheta.emb φ (α : K)
  map_zero' := by funext i; simp [GlobalTheory.HeckeTheta.emb]
  map_add' a b := by funext i; simp [GlobalTheory.HeckeTheta.emb]

theorem embHom_injective {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) : Function.Injective (embHom φ) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra h0
  obtain ⟨i, hi⟩ := exists_one_le_norm hφ h0
  have : φ i (a : K) = 0 := congrFun ha i
  rw [this, norm_zero] at hi
  exact absurd hi (by norm_num)


omit [Fintype I] in
theorem summable_exp_neg_mul_norm_sq {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] {a : ℝ} (ha : 0 < a) :
    Summable fun x : L ↦ Real.exp (-a * ‖(x : E)‖ ^ 2) := by
  set k := Module.finrank ℤ L + 1 with hk
  have h := (ZLattice.summable_norm_pow_inv L (2 * k) (by omega)).mul_left
    ((k.factorial : ℝ) / a ^ k)
  refine .of_norm_bounded_eventually h ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with x h0
  have hn : 0 < ‖(x : E)‖ := norm_pos_iff.2 (by simpa using h0)
  have h1 := Real.pow_div_factorial_le_exp (a * ‖(x : E)‖ ^ 2) (by positivity) k
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, neg_mul, Real.exp_neg]
  refine (inv_anti₀ (by positivity) h1).trans_eq ?_
  change _ = _ * ‖(x : E)‖⁻¹ ^ (2 * k)
  rw [mul_pow, ← pow_mul, inv_pow]
  field_simp

def embLat (φ : I → K →+* ℂ) : Submodule ℤ (I → ℂ) := LinearMap.range (embHom φ).toIntLinearMap

theorem discrete_embLat {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) : DiscreteTopology (embLat φ) := by
  refine DiscreteTopology.of_forall_le_dist one_pos fun x y hxy => ?_
  obtain ⟨a, ha⟩ := x.2
  obtain ⟨b, hb⟩ := y.2
  rw [Subtype.dist_eq, dist_eq_norm]
  have hsub : (x : I → ℂ) - y = GlobalTheory.HeckeTheta.emb φ ((a - b : 𝓞 K) : K) := by
    rw [← ha, ← hb]
    funext i
    simp [embHom, GlobalTheory.HeckeTheta.emb]
  rw [hsub]
  apply one_le_norm_emb hφ
  rw [← hsub, sub_ne_zero]
  exact fun h => hxy (Subtype.ext h)

theorem summable_exp_emb {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) {ε : ℝ} (hε : 0 < ε) :
    Summable fun α : 𝓞 K => Real.exp (-ε * ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ ^ 2) := by
  haveI := discrete_embLat hφ
  have hs : Summable fun x : embLat φ ↦ Real.exp (-ε * ‖(x : I → ℂ)‖ ^ 2) :=
    summable_exp_neg_mul_norm_sq (embLat φ) hε
  have hmem : ∀ α : 𝓞 K, embHom φ α ∈ embLat φ := fun α => LinearMap.mem_range_self _ α
  let j : 𝓞 K → embLat φ := fun α => ⟨embHom φ α, hmem α⟩
  have hj : Function.Injective j := fun a b h => embHom_injective hφ (congrArg Subtype.val h)
  have h2 := hs.comp_injective hj
  refine h2.congr fun α => ?_
  simp only [Function.comp_apply, j]
  rfl

theorem bounded_of_periodic {M : Ideal (𝓞 K)} (F : 𝓞 K → ℂ) (hM : M ≠ ⊥)
    (hF : ∀ α μ : 𝓞 K, μ ∈ M → F (α + μ) = F α) : ∃ C : ℝ, ∀ α, ‖F α‖ ≤ C := by
  haveI := Ideal.finiteQuotientOfFreeOfNeBot M hM
  haveI := Fintype.ofFinite (𝓞 K ⧸ M)
  refine ⟨∑ q : 𝓞 K ⧸ M, ‖F (Quotient.out q)‖, fun α => ?_⟩
  have hmem : α - Quotient.out (Ideal.Quotient.mk M α) ∈ M := by
    rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
  have hα : F α = F (Quotient.out (Ideal.Quotient.mk M α)) := by
    have := hF (Quotient.out (Ideal.Quotient.mk M α)) _ hmem
    rwa [add_sub_cancel] at this
  rw [hα]
  exact Finset.single_le_sum (f := fun q : 𝓞 K ⧸ M => ‖F (Quotient.out q)‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ _)

theorem periodic_bound_summable_norm :
    ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ),
      GlobalTheory.CMVal.IsCMType φ → ∀ (M : Ideal (NumberField.RingOfIntegers K)) (F : NumberField.RingOfIntegers K → ℂ),
      M ≠ ⊥ → (∀ α μ : NumberField.RingOfIntegers K, μ ∈ M → F (α + μ) = F α) → (∃ C : ℝ, ∀ α, ‖F α‖ ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → Summable (fun α : NumberField.RingOfIntegers K =>
        ‖F α‖ * Real.exp (-ε * ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ ^ 2))) ∧
      ∀ α : NumberField.RingOfIntegers K, GlobalTheory.HeckeTheta.emb φ (α : K) ≠ 0 → 1 ≤ ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ := by
  intro K _ _ _ I _ φ hφ M F hM hF
  obtain ⟨C, hC⟩ := bounded_of_periodic F hM hF
  refine ⟨⟨C, hC⟩, fun ε hε => ?_, fun α hα => one_le_norm_emb hφ hα⟩
  refine ((summable_exp_emb hφ hε).mul_left C).of_nonneg_of_le (fun α => by positivity) fun α => ?_
  exact mul_le_mul_of_nonneg_right (hC α) (Real.exp_pos _).le

end GlobalTheory.HeckeLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicBoundedGaussianSummableCmTypeStatement
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_bounded_gaussian_summable_cmType : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (M : Ideal (NumberField.RingOfIntegers K)) (F : NumberField.RingOfIntegers K → ℂ), M ≠ ⊥ → (∀ α μ : NumberField.RingOfIntegers K, μ ∈ M → F (α + μ) = F α) → (∃ C : ℝ, ∀ α, ‖F α‖ ≤ C) ∧ (∀ ε : ℝ, 0 < ε → Summable (fun α : NumberField.RingOfIntegers K => ‖F α‖ * Real.exp (-ε * ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ ^ 2))) ∧ ∀ α : NumberField.RingOfIntegers K, GlobalTheory.HeckeTheta.emb φ (α : K) ≠ 0 → 1 ≤ ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ := by
  first | exact @GlobalTheory.HeckeLat.periodic_bound_summable_norm | exact GlobalTheory.HeckeLat.periodic_bound_summable_norm | (intros; apply GlobalTheory.HeckeLat.periodic_bound_summable_norm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MellinIntegralSplitFunctionalEquation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MellinIntegralSplitFunctionalEquation
open NumberField MeasureTheory

namespace GlobalTheory

theorem mellinSplit_hyperplane_null (I : Type) [Fintype I] [Nonempty I] :
    (volume : Measure (I → ℝ)) {y : I → ℝ | ∑ i, y i = 0} = 0 := by
  let L : (I → ℝ) →ₗ[ℝ] ℝ := ∑ i, LinearMap.proj i
  have hL : ∀ y, L y = ∑ i, y i := by intro y; simp [L]
  have hset : {y : I → ℝ | ∑ i, y i = 0} = (LinearMap.ker L : Set (I → ℝ)) := by
    ext y; simp [hL]
  rw [hset]
  apply Measure.addHaar_submodule
  intro htop
  classical
  obtain ⟨i⟩ := (inferInstance : Nonempty I)
  have hmem : Pi.single i (1:ℝ) ∈ LinearMap.ker L := htop ▸ Submodule.mem_top
  rw [LinearMap.mem_ker, hL] at hmem
  simp at hmem

theorem mellinSplit_neg (I : Type) [Fintype I] [Nonempty I] (p : (I → ℝ) → ℝ) (θ θ' : (I → ℝ) → ℂ) (κ s : ℂ)
    (hθ : ∀ y, θ y = κ * (Real.exp (-∑ i, y i) : ℂ) * θ' (-y))
    (h1 : MeasureTheory.Integrable (fun y => (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i}))
    (h2 : MeasureTheory.Integrable (fun y => (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ))) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i})) :
    ∫ y, (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) = (∫ y in {y : I → ℝ | 0 ≤ ∑ i, y i}, (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) + κ * ∫ y in {y : I → ℝ | 0 ≤ ∑ i, y i}, (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ)) := by
  set f : (I → ℝ) → ℂ := fun y => (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) with hf
  set g : (I → ℝ) → ℂ := fun y => (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ)) with hg
  set S : Set (I → ℝ) := {y | 0 ≤ ∑ i, y i} with hS
  set P : Set (I → ℝ) := {y | 0 < ∑ i, y i} with hP
  have hcont : Continuous (fun y : I → ℝ => ∑ i, y i) :=
    continuous_finsetSum _ fun i _ => continuous_apply i
  have hSm : MeasurableSet S := (isClosed_le continuous_const hcont).measurableSet
  have hsumneg : ∀ y : I → ℝ, ∑ i, (-y) i = -∑ i, y i := by
    intro y; simp [Finset.sum_neg_distrib]
  have hfg : ∀ y, f y = κ * g (-y) := by
    intro y
    simp only [hf, hg, hθ, neg_neg, hsumneg]
    have e : Complex.exp (-((∑ i, y i : ℝ) : ℂ)) * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))
        = Complex.exp ((1 - s) * ((-∑ i, y i : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]; push_cast; ring_nf
    have e2 : ((Real.exp (-∑ i, y i) : ℝ) : ℂ) = Complex.exp (-((∑ i, y i : ℝ) : ℂ)) := by
      push_cast; rfl
    rw [e2]
    linear_combination ((p y : ℂ) * κ * θ' (-y)) * e
  have hpre : (Neg.neg : (I → ℝ) → (I → ℝ)) ⁻¹' P = Sᶜ := by
    ext y; simp [hP, hS, hsumneg]
  have hmp : MeasurePreserving (Neg.neg : (I → ℝ) → (I → ℝ)) volume volume :=
    Measure.measurePreserving_neg _
  have hemb : MeasurableEmbedding (Neg.neg : (I → ℝ) → (I → ℝ)) :=
    (MeasurableEquiv.neg (I → ℝ)).measurableEmbedding
  have hPS : P =ᵐ[volume] S := by
    rw [ae_eq_set]
    constructor
    · have : P \ S = ∅ := Set.diff_eq_empty.mpr (fun y (hy : 0 < ∑ i, y i) => (le_of_lt hy : 0 ≤ ∑ i, y i))
      rw [this, measure_empty]
    · apply measure_mono_null _ (mellinSplit_hyperplane_null I)
      intro y hy
      simp only [hP, hS, Set.mem_diff, Set.mem_setOf_eq, not_lt] at hy
      exact le_antisymm hy.2 hy.1
  have hgP : IntegrableOn g P volume :=
    IntegrableOn.congr_set_ae (show IntegrableOn g S volume from h2) hPS
  have hfc : IntegrableOn f Sᶜ volume := by
    have := (hmp.integrableOn_comp_preimage hemb).2 hgP
    rw [hpre] at this
    have h3 := this.const_mul κ
    refine IntegrableOn.congr_fun h3 (fun y _ => ?_) hSm.compl
    simp [hfg y]
  have hfint : Integrable f volume := by
    have := IntegrableOn.union (show IntegrableOn f S volume from h1) hfc
    rwa [Set.union_compl_self, integrableOn_univ] at this
  rw [← integral_add_compl hSm hfint]
  congr 1
  calc ∫ y in Sᶜ, f y = ∫ y in Sᶜ, κ * g (-y) := by simp_rw [hfg]
    _ = κ * ∫ y in Sᶜ, g (-y) := integral_const_mul _ _
    _ = κ * ∫ y in P, g y := by
        rw [← hpre, hmp.setIntegral_preimage_emb hemb]
    _ = κ * ∫ y in S, g y := by rw [setIntegral_congr_set hPS]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MellinIntegralSplitFunctionalEquationStatement
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mellin_integral_split_functional_equation : ∀ (I : Type) [Fintype I] [Nonempty I] (p : (I → ℝ) → ℝ) (θ θ' : (I → ℝ) → ℂ) (κ s : ℂ), (∀ y, θ y = κ * (Real.exp (-∑ i, y i) : ℂ) * θ' (-y)) → MeasureTheory.Integrable (fun y => (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i}) → MeasureTheory.Integrable (fun y => (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ))) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i}) → ∫ y, (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) = (∫ y in {y : I → ℝ | 0 ≤ ∑ i, y i}, (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) + κ * ∫ y in {y : I → ℝ | 0 ≤ ∑ i, y i}, (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.mellinSplit_neg | exact GlobalTheory.mellinSplit_neg | (intros; apply GlobalTheory.mellinSplit_neg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckePartialLSeriesEntireBoundedStrips
noncomputable section
open NumberField MeasureTheory

namespace GlobalTheory.HeckeStrip

theorem completed_pSeries_entire_bounded : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ), (∃ i, n i ≠ 0) → ∀ (M : Ideal (𝓞 K)) (F : 𝓞 K → ℂ), M ≠ ⊥ → (∀ α μ : 𝓞 K, μ ∈ M → F (α + μ) = F α) → (∀ (u : (𝓞 K)ˣ) (α : 𝓞 K), F ((u : 𝓞 K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : 𝓞 K) * α : 𝓞 K) : K) = F α * GlobalTheory.HeckeStrip.wt φ n (α : K)) → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips Λ ∧ ∀ s : ℂ, 1 < s.re → Λ s = GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.pSeries F φ n s := by
  intro K _ _ _ I _ φ hφ n hn M F hM hper hinv
  haveI : Nonempty I := ⟨hn.choose⟩
  obtain ⟨p, hpm, hp0, hpsum, R, hpR⟩ := GlobalTheory.T.exists_measurable_partitionOfUnity_unitLogTranslates K I φ hφ
  obtain ⟨⟨C, hC⟩, hsumm, hge⟩ := GlobalTheory.T.periodic_bounded_gaussian_summable_cmType K I φ hφ M F hM hper
  obtain ⟨a, κ, hasumm, ⟨δ, hδ, hδa⟩, hfe⟩ := GlobalTheory.T.heckeThetaKernel_poisson_summation K I φ hφ n M F hM hper
  have hp1 : ∀ y, p y ≤ 1 := fun y => by
    have h := le_hasSum (hpsum y) 1 (fun u _ => hp0 _)
    have h0 : GlobalTheory.HeckeTheta.ulog φ (1 : (𝓞 K)ˣ) = 0 := by
      funext i; simp [GlobalTheory.HeckeTheta.ulog]
    simpa [h0] using h
  have hpB : ∀ y, |p y| ≤ 1 := fun y => abs_le.2 ⟨by linarith [hp0 y], hp1 y⟩
  set S : Set (I → ℝ) := {y | 0 ≤ ∑ i, y i} with hSdef
  have hSm : MeasurableSet S := measurableSet_le measurable_const (by fun_prop)
  have hℓ : Measurable (fun y : I → ℝ => ∑ i, y i) := by fun_prop
  have hS0 : ∀ᵐ y ∂(volume.restrict S), 0 ≤ ∑ i, y i := ae_restrict_of_forall_mem hSm fun y hy => hy
  obtain ⟨D1m, D1i⟩ := GlobalTheory.T.integrable_weighted_heckeThetaKernel_halfSpace I (fun α : 𝓞 K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n p 1 R hn hsumm
    ⟨1, one_pos, fun α _ h => hge α h⟩ hpm hpB hpR
  obtain ⟨D2m, D2i⟩ := GlobalTheory.T.integrable_weighted_heckeThetaKernel_halfSpace I (fun v : I → ℂ => v) a n (fun y => p (-y)) 1 R hn hasumm ⟨δ, hδ, hδa⟩
    (hpm.comp measurable_neg) (fun y => hpB _) (fun y hy i j => by
      have := hpR (-y) hy j i
      simp only [Pi.neg_apply] at this
      linarith)
  have A1 := GlobalTheory.T.laplace_integral_entire_boundedInVerticalStrips (volume.restrict S) (fun y : I → ℝ => ∑ i, y i) _ hℓ D1m.restrict hS0 D1i
  have A2 := GlobalTheory.T.laplace_integral_entire_boundedInVerticalStrips (volume.restrict S) (fun y : I → ℝ => ∑ i, y i) _ hℓ D2m.restrict hS0 D2i
  have hint : ∀ (g : (I → ℝ) → ℂ) (t : ℂ), AEStronglyMeasurable g volume →
      (∀ σ : ℝ, Integrable (fun y => ‖g y‖ * Real.exp (σ * ∑ i, y i)) (volume.restrict S)) →
      Integrable (fun y => g y * Complex.exp (t * ((∑ i, y i : ℝ) : ℂ))) (volume.restrict S) := by
    intro g t hg hgi
    refine (hgi t.re).mono' (hg.restrict.mul (Continuous.aestronglyMeasurable (by fun_prop))) (ae_of_all _ fun y => ?_)
    rw [norm_mul, Complex.norm_exp]
    apply le_of_eq
    congr 2
    simp [Complex.mul_re]
  set f1 : ℂ → ℂ := fun s => ∫ y in S, (p y : ℂ) * GlobalTheory.HeckeTheta.theta (fun α : 𝓞 K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) with hf1
  set f2 : ℂ → ℂ := fun s => ∫ y in S, (p (-y) : ℂ) * GlobalTheory.HeckeTheta.theta (fun v : I → ℂ => v) a n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) with hf2
  have hd1 : Differentiable ℂ f1 := A1.1
  have hd2 : Differentiable ℂ f2 := A2.1
  have hb1 : GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips f1 := A1.2
  have hb2 : GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips f2 := A2.2
  refine ⟨fun s => 2 ^ Fintype.card I * (f1 s + κ * f2 (1 - s)), ?_, ?_, ?_⟩
  · exact (hd1.add ((hd2.comp ((differentiable_const (1 : ℂ)).sub differentiable_id)).const_mul κ)).const_mul _
  · intro a' b' hab
    obtain ⟨C1, hC1⟩ := hb1 a' b' hab
    obtain ⟨C2, hC2⟩ := hb2 (1 - b') (1 - a') (by linarith)
    refine ⟨‖(2 : ℂ) ^ Fintype.card I‖ * (C1 + ‖κ‖ * C2), fun s h1 h2 => ?_⟩
    rw [norm_mul]
    gcongr
    refine (norm_add_le _ _).trans (add_le_add (hC1 s h1 h2) ?_)
    rw [norm_mul]
    gcongr
    exact hC2 (1 - s) (by simp; linarith) (by simp; linarith)
  · intro s hs
    rw [GlobalTheory.T.archFactor_mul_pSeries_eq_integral_alt K I φ hφ n hn F C hC hinv p hpm hp0 hpsum s hs,
      GlobalTheory.T.mellin_integral_split_functional_equation I p _ _ κ s hfe (hint _ s D1m D1i) (hint _ (1 - s) D2m D2i)]

end GlobalTheory.HeckeStrip
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckePartialLSeriesEntireBoundedStripsStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completed_heckePartialLSeries_entire_bounded_strips : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ), (∃ i, n i ≠ 0) → ∀ (M : Ideal (𝓞 K)) (F : 𝓞 K → ℂ), M ≠ ⊥ → (∀ α μ : 𝓞 K, μ ∈ M → F (α + μ) = F α) → (∀ (u : (𝓞 K)ˣ) (α : 𝓞 K), F ((u : 𝓞 K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : 𝓞 K) * α : 𝓞 K) : K) = F α * GlobalTheory.HeckeStrip.wt φ n (α : K)) → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips Λ ∧ ∀ s : ℂ, 1 < s.re → Λ s = GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.pSeries F φ n s := by
  first | exact @GlobalTheory.HeckeStrip.completed_pSeries_entire_bounded | exact GlobalTheory.HeckeStrip.completed_pSeries_entire_bounded | (intros; apply GlobalTheory.HeckeStrip.completed_pSeries_entire_bounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLSeriesEqSumPrincipalPartialSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLSeriesEqSumPrincipalPartialSeries
noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory.HeckeStrip


open Classical in
theorem tsum_ideal_eq_sum_classGroup_of_summable {K : Type} [Field K] [NumberField K]
    (b : ClassGroup (𝓞 K) → (Ideal (𝓞 K))⁰) (G : Ideal (𝓞 K) → ℂ) (H : ClassGroup (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hb : Function.Bijective (fun c => ClassGroup.mk0 (b c))) (h0 : G ⊥ = 0) (hsum : Summable G)
    (hH : ∀ c I, I ≠ ⊥ → H c (I * b c) = G I) :
    ∑' I, G I = ∑ c, ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ (b c : Ideal (𝓞 K))}, H c J := by
  let S : ClassGroup (𝓞 K) → Set (Ideal (𝓞 K)) :=
    fun c => {I | I ≠ ⊥ ∧ (I * (b c : Ideal (𝓞 K))).IsPrincipal}
  have h1 : ∀ I, G I = ∑ c, (S c).indicator G I := by
    intro I
    by_cases hI : I = ⊥
    · subst hI
      rw [h0]
      exact (Finset.sum_eq_zero fun c _ => Set.indicator_of_notMem (by exact fun h => h.1 rfl) _).symm
    · obtain ⟨c, hc, hu⟩ := GlobalTheory.existsUnique_isPrincipal_mul_classRep b hb I hI
      rw [Finset.sum_eq_single c]
      · exact (Set.indicator_of_mem (show I ∈ S c from ⟨hI, hc⟩) _).symm
      · intro c' _ hne
        exact Set.indicator_of_notMem (by exact fun h => hne (hu c' h.2)) _
      · simp
  rw [tsum_congr h1, Summable.tsum_finsetSum (fun c _ => hsum.indicator (S c))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← tsum_subtype, ← GlobalTheory.tsum_isPrincipal_mul_eq (b c : Ideal (𝓞 K))
    (mem_nonZeroDivisors_iff_ne_zero.mp (b c).2) (H c)]
  exact tsum_congr fun I => (hH c I.1 I.2.1).symm

variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]

def classUnitPart (φ : I → K →+* ℂ) (n : I → ℤ) (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ) (α : 𝓞 K) : ℂ :=
  open Classical in if m = ⊤ then 1 else X (Ideal.span {α}) * (wt φ n (α : K))⁻¹

def classPartFun (φ : I → K →+* ℂ) (n : I → ℤ) (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ) (b : Ideal (𝓞 K))
    (α : 𝓞 K) : ℂ :=
  open Classical in if α ∈ b then classUnitPart φ n m X α else 0

theorem wt_ne_zero_of_ne_zero (φ : I → K →+* ℂ) (n : I → ℤ) {α : 𝓞 K} (hα : α ≠ 0) : wt φ n (α : K) ≠ 0 := by
  have hαK : (α : K) ≠ 0 := fun h => hα (RingOfIntegers.coe_eq_zero_iff.mp h)
  intro h
  have := norm_wt φ n hαK
  rw [h, norm_zero] at this
  exact zero_ne_one this

section

variable {φ : I → K →+* ℂ} {n : I → ℤ} {m : Ideal (𝓞 K)} {X : Ideal (𝓞 K) → ℂ}

theorem classPartFun_mul_wt
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    (b : Ideal (𝓞 K)) {α : 𝓞 K} (hα : α ≠ 0) :
    classPartFun φ n m X b α * wt φ n (α : K) = open Classical in if α ∈ b then X (Ideal.span {α}) else 0 := by
  unfold classPartFun classUnitPart
  by_cases hb : α ∈ b
  · rw [if_pos hb, if_pos hb]
    by_cases hm : m = ⊤
    · rw [if_pos hm, one_mul, hβ α hα (hm ▸ Submodule.mem_top)]
    · rw [if_neg hm, mul_assoc, inv_mul_cancel₀ (wt_ne_zero_of_ne_zero φ n hα), mul_one]
  · rw [if_neg hb, if_neg hb, zero_mul]

theorem classUnitPart_eq_of_inv
    (hmul : ∀ a b : Ideal (𝓞 K), X (a * b) = X a * X b)
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    (hm : m ≠ ⊤) {α γ : 𝓞 K} (h : γ * α - 1 ∈ m) :
    classUnitPart φ n m X α = wt φ n (γ : K) * (X (Ideal.span {γ}))⁻¹ := by
  have hγα : γ * α ≠ 0 := by
    intro h0
    rw [h0, zero_sub] at h
    exact hm ((Ideal.eq_top_iff_one m).2 (by simpa using m.neg_mem h))
  have hα : α ≠ 0 := right_ne_zero_of_mul hγα
  have hγ : γ ≠ 0 := left_ne_zero_of_mul hγα
  have key := hβ _ hγα h
  rw [← Ideal.span_singleton_mul_span_singleton, hmul] at key
  have hc : ((γ * α : 𝓞 K) : K) = (γ : K) * α := by push_cast; rfl
  rw [hc, wt_mul] at key
  have hwα := wt_ne_zero_of_ne_zero φ n hα
  have hwγ := wt_ne_zero_of_ne_zero φ n hγ
  have hXγ : X (Ideal.span {γ}) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at key
    exact mul_ne_zero hwγ hwα key.symm
  unfold classUnitPart
  rw [if_neg hm]
  field_simp
  linear_combination key

theorem classUnitPart_add
    (hmul : ∀ a b : Ideal (𝓞 K), X (a * b) = X a * X b)
    (hzero : ∀ a : Ideal (𝓞 K), a ⊔ m ≠ ⊤ → X a = 0)
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    {α μ : 𝓞 K} (hμ : μ ∈ m) :
    classUnitPart φ n m X (α + μ) = classUnitPart φ n m X α := by
  by_cases hm : m = ⊤
  · simp [classUnitPart, hm]
  have hsup : Ideal.span {α + μ} ⊔ m = Ideal.span {α} ⊔ m := by
    apply le_antisymm
    · exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 (Ideal.add_mem _
        (Ideal.mem_sup_left (Ideal.mem_span_singleton_self α)) (Ideal.mem_sup_right hμ))) le_sup_right
    · refine sup_le ((Ideal.span_singleton_le_iff_mem _).2 ?_) le_sup_right
      have h : (α + μ) + -μ ∈ Ideal.span {α + μ} ⊔ m :=
        Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
          (Ideal.mem_sup_right (m.neg_mem hμ))
      simpa using h
  by_cases hc : Ideal.span {α} ⊔ m = ⊤
  · have h1 : (1 : 𝓞 K) ∈ Ideal.span {α} ⊔ m := hc ▸ Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
    obtain ⟨γ, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    have e1 : γ * α - 1 ∈ m := by
      have e : γ * α - 1 = -z := by rw [← hyz]; ring
      rw [e]; exact m.neg_mem hz
    have e2 : γ * (α + μ) - 1 ∈ m := by
      have e : γ * (α + μ) - 1 = (γ * α - 1) + γ * μ := by ring
      rw [e]; exact m.add_mem e1 (m.mul_mem_left γ hμ)
    rw [classUnitPart_eq_of_inv hmul hβ hm e1, classUnitPart_eq_of_inv hmul hβ hm e2]
  · have hc' : Ideal.span {α + μ} ⊔ m ≠ ⊤ := hsup ▸ hc
    simp only [classUnitPart, if_neg hm, hzero _ hc, hzero _ hc', zero_mul]

theorem classPartFun_add
    (hmul : ∀ a b : Ideal (𝓞 K), X (a * b) = X a * X b)
    (hzero : ∀ a : Ideal (𝓞 K), a ⊔ m ≠ ⊤ → X a = 0)
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    (b : Ideal (𝓞 K)) {α μ : 𝓞 K} (hμ : μ ∈ m * b) :
    classPartFun φ n m X b (α + μ) = classPartFun φ n m X b α := by
  have hμm : μ ∈ m := (Ideal.mul_le_inf.trans inf_le_left) hμ
  have hμb : μ ∈ b := (Ideal.mul_le_inf.trans inf_le_right) hμ
  unfold classPartFun
  by_cases h : α ∈ b
  · rw [if_pos h, if_pos (b.add_mem h hμb), classUnitPart_add hmul hzero hβ hμm]
  · have h' : α + μ ∉ b := fun h' => h (by simpa using b.sub_mem h' hμb)
    rw [if_neg h, if_neg h']

theorem classPartFun_unit
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    (b : Ideal (𝓞 K)) (u : (𝓞 K)ˣ) (α : 𝓞 K) :
    classPartFun φ n m X b ((u : 𝓞 K) * α) * wt φ n (((u : 𝓞 K) * α : 𝓞 K) : K) =
      classPartFun φ n m X b α * wt φ n (α : K) := by
  by_cases hα : α = 0
  · subst hα; simp
  have huα : (u : 𝓞 K) * α ≠ 0 := mul_ne_zero u.ne_zero hα
  rw [classPartFun_mul_wt hβ b huα, classPartFun_mul_wt hβ b hα, Ideal.span_singleton_mul_left_unit u.isUnit]
  have hiff : (u : 𝓞 K) * α ∈ b ↔ α ∈ b :=
    ⟨fun h => by simpa using b.mul_mem_left ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) h, fun h => b.mul_mem_left _ h⟩
  by_cases h : α ∈ b
  · rw [if_pos h, if_pos (hiff.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.1 h'))]

theorem pval_classPartFun
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    (b J : Ideal (𝓞 K)) [J.IsPrincipal] (hJ : J ≠ ⊥) :
    pval (classPartFun φ n m X b) φ n J = open Classical in if J ≤ b then X J else 0 := by
  have hg : Submodule.IsPrincipal.generator J ≠ 0 := by
    rwa [Ne, ← Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero]
  have hle : Submodule.IsPrincipal.generator J ∈ b ↔ J ≤ b := by
    conv_rhs => rw [← Ideal.span_singleton_generator J]
    exact (Ideal.span_singleton_le_iff_mem b).symm
  unfold pval
  rw [classPartFun_mul_wt hβ b hg, Ideal.span_singleton_generator]
  by_cases h : J ≤ b
  · rw [if_pos (hle.2 h), if_pos h]
  · rw [if_neg (fun h' => h (hle.1 h')), if_neg h]

theorem pSeries_classPartFun
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    (b : Ideal (𝓞 K)) (s : ℂ) :
    pSeries (classPartFun φ n m X b) φ n s =
      ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ b}, X J.1 * ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s) := by
  classical
  let f : Ideal (𝓞 K) → ℂ := fun J => (if J ≤ b then X J else 0) * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s)
  let g : Ideal (𝓞 K) → ℂ := fun J => X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s)
  have h1 : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal},
      (haveI := J.2.2; pval (classPartFun φ n m X b) φ n J.1) * ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s) = f J.1 := by
    rintro ⟨J, hJ, hP⟩
    simp only [f]
    rw [pval_classPartFun hβ b J hJ]
  unfold pSeries
  rw [tsum_congr h1]
  have e1 := tsum_subtype {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal} f
  have e2 := tsum_subtype {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ b} g
  refine e1.trans (Eq.trans ?_ e2.symm)
  refine tsum_congr fun J => ?_
  by_cases hJ : J ≠ ⊥ ∧ J.IsPrincipal
  · by_cases h : J ≤ b
    · rw [Set.indicator_of_mem (show J ∈ {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal} from hJ),
        Set.indicator_of_mem (show J ∈ {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ b} from ⟨hJ.1, hJ.2, h⟩)]
      simp only [f, g, if_pos h]
    · rw [Set.indicator_of_mem (show J ∈ {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal} from hJ),
        Set.indicator_of_notMem (show J ∉ {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ b} from fun h' => h h'.2.2)]
      simp only [f, if_neg h, zero_mul]
  · rw [Set.indicator_of_notMem (show J ∉ {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal} from hJ),
      Set.indicator_of_notMem (show J ∉ {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ b} from
        fun h' => hJ ⟨h'.1, h'.2.1⟩)]

end

theorem heckeSeries_eq_sum_pSeries : ∀ (K : Type) [Field K] [NumberField K] (I : Type) [Fintype I] (φ : I → K →+* ℂ) (n : I → ℤ) (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ), m ≠ ⊥ → X ⊥ = 0 → (∀ a b : Ideal (𝓞 K), X (a * b) = X a * X b) → (∀ a : Ideal (𝓞 K), a ≠ ⊥ → a ⊔ m = ⊤ → ‖X a‖ = 1) → (∀ a : Ideal (𝓞 K), a ⊔ m ≠ ⊤ → X a = 0) → (∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = GlobalTheory.HeckeStrip.wt φ n (β : K)) → ∃ (r : ℕ) (c : Fin r → ℂ) (B : Fin r → ℕ) (M : Fin r → Ideal (𝓞 K)) (F : Fin r → 𝓞 K → ℂ), (∀ k, 0 < B k) ∧ (∀ k, M k ≠ ⊥) ∧ (∀ k (α μ : 𝓞 K), μ ∈ M k → F k (α + μ) = F k α) ∧ (∀ k (u : (𝓞 K)ˣ) (α : 𝓞 K), F k ((u : 𝓞 K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : 𝓞 K) * α : 𝓞 K) : K) = F k α * GlobalTheory.HeckeStrip.wt φ n (α : K)) ∧ ∀ s : ℂ, 1 < s.re → ∑' a : Ideal (𝓞 K), X a * ((Ideal.absNorm a : ℕ) : ℂ) ^ (-s) = ∑ k, c k * ((B k : ℕ) : ℂ) ^ s * GlobalTheory.HeckeStrip.pSeries (F k) φ n s := by
  intro K _ _ I _ φ n m X hm hX0 hmul hnorm hzero hβ
  choose b hb hbm using GlobalTheory.exists_integral_ideal_in_class_coprime K m hm
  have hbij : Function.Bijective (fun c => ClassGroup.mk0 (b c)) := by
    have e : (fun c => ClassGroup.mk0 (b c)) = id := funext hb
    rw [e]; exact Function.bijective_id
  have hb0 : ∀ c, (b c : Ideal (𝓞 K)) ≠ ⊥ := fun c => nonZeroDivisors.coe_ne_zero (b c)
  have hXb : ∀ c, X (b c) ≠ 0 := fun c h => by
    have := hnorm _ (hb0 c) (hbm c)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hNb : ∀ c, Ideal.absNorm (b c : Ideal (𝓞 K)) ≠ 0 := fun c h => hb0 c (Ideal.absNorm_eq_zero_iff.mp h)
  let e := Fintype.equivFin (ClassGroup (𝓞 K))
  refine ⟨Fintype.card (ClassGroup (𝓞 K)), fun k => (X (b (e.symm k)))⁻¹,
    fun k => Ideal.absNorm (b (e.symm k) : Ideal (𝓞 K)), fun k => m * (b (e.symm k) : Ideal (𝓞 K)),
    fun k => classPartFun φ n m X (b (e.symm k)), fun k => Nat.pos_of_ne_zero (hNb _),
    fun k => mul_ne_zero hm (hb0 _), fun k α μ hμ => classPartFun_add hmul hzero hβ _ hμ,
    fun k u α => classPartFun_unit hβ _ u α, fun s hs => ?_⟩
  have hXle : ∀ J, ‖X J‖ ≤ 1 := by
    intro J
    by_cases h0 : J = ⊥
    · rw [h0, hX0, norm_zero]; exact zero_le_one
    by_cases hc : J ⊔ m = ⊤
    · rw [hnorm J h0 hc]
    · rw [hzero J hc, norm_zero]; exact zero_le_one
  have hsum : Summable fun J : Ideal (𝓞 K) => X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s) :=
    (GlobalTheory.Mem.summable_norm_absNorm_cpow K hs).of_norm_bounded fun J => by
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hXle J)
  have hH : ∀ c (J : Ideal (𝓞 K)), J ≠ ⊥ →
      (X (b c))⁻¹ * ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ s *
        (X (J * (b c : Ideal (𝓞 K))) * ((Ideal.absNorm (J * (b c : Ideal (𝓞 K))) : ℕ) : ℂ) ^ (-s)) =
      X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s) := by
    intro c J _
    have hpow : ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ s *
        ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s) = 1 := by
      rw [Complex.cpow_neg, mul_inv_cancel₀]
      rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
      exact Or.inl (Nat.cast_ne_zero.mpr (hNb c))
    rw [hmul, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    calc (X (b c))⁻¹ * ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ s *
          (X J * X (b c) * (((Ideal.absNorm J : ℕ) : ℂ) ^ (-s) *
            ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)))
        = X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s) * ((X (b c))⁻¹ * X (b c)) *
          (((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ s *
            ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) := by ring
      _ = X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s) := by rw [inv_mul_cancel₀ (hXb c), hpow, mul_one, mul_one]
  rw [tsum_ideal_eq_sum_classGroup_of_summable b (fun J => X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s))
    (fun c J => (X (b c))⁻¹ * ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ s *
      (X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s))) hbij (by simp only [hX0, zero_mul]) hsum hH]
  refine (Equiv.sum_comp e.symm _).symm.trans (Finset.sum_congr rfl fun k _ => ?_)
  beta_reduce
  rw [tsum_mul_left, pSeries_classPartFun hβ]

end GlobalTheory.HeckeStrip
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLSeriesEqSumPrincipalPartialSeriesStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeLSeries_eq_sum_principalPartialSeries : ∀ (K : Type) [Field K] [NumberField K] (I : Type) [Fintype I] (φ : I → K →+* ℂ) (n : I → ℤ) (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ), m ≠ ⊥ → X ⊥ = 0 → (∀ a b : Ideal (𝓞 K), X (a * b) = X a * X b) → (∀ a : Ideal (𝓞 K), a ≠ ⊥ → a ⊔ m = ⊤ → ‖X a‖ = 1) → (∀ a : Ideal (𝓞 K), a ⊔ m ≠ ⊤ → X a = 0) → (∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = GlobalTheory.HeckeStrip.wt φ n (β : K)) → ∃ (r : ℕ) (c : Fin r → ℂ) (B : Fin r → ℕ) (M : Fin r → Ideal (𝓞 K)) (F : Fin r → 𝓞 K → ℂ), (∀ k, 0 < B k) ∧ (∀ k, M k ≠ ⊥) ∧ (∀ k (α μ : 𝓞 K), μ ∈ M k → F k (α + μ) = F k α) ∧ (∀ k (u : (𝓞 K)ˣ) (α : 𝓞 K), F k ((u : 𝓞 K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : 𝓞 K) * α : 𝓞 K) : K) = F k α * GlobalTheory.HeckeStrip.wt φ n (α : K)) ∧ ∀ s : ℂ, 1 < s.re → ∑' a : Ideal (𝓞 K), X a * ((Ideal.absNorm a : ℕ) : ℂ) ^ (-s) = ∑ k, c k * ((B k : ℕ) : ℂ) ^ s * GlobalTheory.HeckeStrip.pSeries (F k) φ n s := by
  first | exact @GlobalTheory.HeckeStrip.heckeSeries_eq_sum_pSeries | exact GlobalTheory.HeckeStrip.heckeSeries_eq_sum_pSeries | (intros; apply GlobalTheory.HeckeStrip.heckeSeries_eq_sum_pSeries <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckeLBoundedInVerticalStrips
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal
open Formalism.L2.Host (HChar)

namespace GlobalTheory.HeckeStrip

theorem completedLBoundedInStrips : GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips := by
  intro E _ _ _ I _ φ hφ χ n hu hi hn
  obtain ⟨m, X, hm, hX0, hX1, hXm, hXn, hXz, hXP, hXβ⟩ := GlobalTheory.T.exists_idealCharacter_of_unitary_heckeChar E χ hu
  have hβ : ∀ β : 𝓞 E, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : E) := by
    intro β h0 h1
    have h0' : (β : E) ≠ 0 := by exact_mod_cast h0
    rw [hXβ β (Units.mk0 _ h0') rfl h1, hi (Units.mk0 _ h0')]
    simp only [wt, Units.val_mk0, zpow_neg, Finset.prod_inv_distrib]
  have hle : ∀ a, ‖X a‖ ≤ 1 := fun a => by
    by_cases ha : a = ⊥
    · simp [ha, hX0]
    by_cases ha' : a ⊔ m = ⊤
    · exact (hXn a ha ha').le
    · simp [hXz a ha']
  obtain ⟨r, c, B, M, F, hB, hM, hper, hinv, hdec⟩ := GlobalTheory.T.heckeLSeries_eq_sum_principalPartialSeries E I φ n m X hm hX0 hXm hXn hXz hβ
  choose Λ hΛd hΛb hΛe using fun k => GlobalTheory.T.completed_heckePartialLSeries_entire_bounded_strips E I φ hφ n hn (M k) (F k) (hM k) (hper k) (hinv k)
  have hB0 : ∀ k, ((B k : ℕ) : ℂ) ≠ 0 := fun k => by exact_mod_cast (hB k).ne'
  refine ⟨fun s => ∑ k, c k * ((B k : ℕ) : ℂ) ^ s * Λ k s, ⟨?_, fun s hs => ?_⟩, ?_⟩
  · intro s
    refine DifferentiableAt.fun_sum fun k _ => ?_
    exact ((differentiableAt_const _).mul ((differentiableAt_id.const_cpow (Or.inl (hB0 k))))).mul ((hΛd k).differentiableAt)
  · refine ⟨∑' a : Ideal (𝓞 E), X a * ((Ideal.absNorm a : ℕ) : ℂ) ^ (-s), ?_, ?_⟩
    · rw [GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum E X hX0 hX1 hXm hle s hs]
      convert GlobalTheory.HeckeOne.hasProd_exp hu hs using 1
      simp only [hXP, GlobalTheory.HeckeOne.cf]
    · rw [hdec s hs, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hΛe k s hs]
      ring
  · intro a b hab
    choose C hC using fun k => hΛb k a b hab
    refine ⟨∑ k, ‖c k‖ * ((B k : ℝ) ^ b * |C k|), fun s h1 h2 => ?_⟩
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul, mul_assoc, Complex.norm_natCast_cpow_of_pos (hB k)]
    have hB1 : (1 : ℝ) ≤ (B k : ℝ) := by exact_mod_cast hB k
    gcongr
    exact (hC k s h1 h2).trans (le_abs_self _)

end GlobalTheory.HeckeStrip
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckeLBoundedInVerticalStripsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedHeckeL_bounded_in_vertical_strips : GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips := by
  first | exact @GlobalTheory.HeckeStrip.completedLBoundedInStrips | exact GlobalTheory.HeckeStrip.completedLBoundedInStrips | (intros; apply GlobalTheory.HeckeStrip.completedLBoundedInStrips <;> assumption)
end
