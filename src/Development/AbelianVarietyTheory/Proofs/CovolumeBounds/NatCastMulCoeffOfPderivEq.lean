module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq
namespace GlobalTheory.FormalCalc

open MvPowerSeries Finsupp
open scoped MvPowerSeries.WithPiTopology

section Chain

variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem subst_zero' {a : σ → MvPowerSeries τ S} (ha : HasSubst a) :
    subst a (0 : MvPowerSeries σ R) = 0 := by
  rw [← substAlgHom_apply ha, map_zero]

theorem subst_one' {a : σ → MvPowerSeries τ S} (ha : HasSubst a) :
    subst a (1 : MvPowerSeries σ R) = 1 := by
  rw [← substAlgHom_apply ha, map_one]

theorem subst_neg' {a : σ → MvPowerSeries τ S} (ha : HasSubst a) (f : MvPowerSeries σ R) :
    subst a (-f) = -subst a f := by
  rw [← substAlgHom_apply ha, map_neg, substAlgHom_apply]

theorem subst_sum' {κ : Type*} {a : σ → MvPowerSeries τ S} (ha : HasSubst a) (s : Finset κ)
    (f : κ → MvPowerSeries σ R) : subst a (∑ k ∈ s, f k) = ∑ k ∈ s, subst a (f k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← substAlgHom_apply ha, map_sum]
  simp only [substAlgHom_apply]

theorem subst_C' {a : σ → MvPowerSeries τ S} (ha : HasSubst a) (r : R) :
    subst a (C r : MvPowerSeries σ R) = C (algebraMap R S r) := by
  rw [← substAlgHom_apply ha, show (C r : MvPowerSeries σ R) = algebraMap R _ r from rfl,
    AlgHom.commutes, MvPowerSeries.algebraMap_apply]

open MvPowerSeries.WithPiTopology in
theorem continuous_pderiv [TopologicalSpace R] [DiscreteTopology R] (i : σ) :
    Continuous (pderiv (R := R) i : MvPowerSeries σ R → MvPowerSeries σ R) := by
  refine continuous_iff_continuousAt.mpr fun f => ?_
  rw [ContinuousAt, MvPowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro d
  simp only [coeff_pderiv]
  exact ((MvPowerSeries.WithPiTopology.continuous_coeff R (d + single i 1)).mul
    continuous_const).continuousAt

theorem pderiv_comm (i j : σ) (f : MvPowerSeries σ R) :
    pderiv (R := R) i (pderiv (R := R) j f) = pderiv (R := R) j (pderiv (R := R) i f) := by
  classical
  by_cases h : i = j
  · rw [h]
  ext d
  simp only [coeff_pderiv, Finsupp.add_apply, single_eq_of_ne h, single_eq_of_ne (Ne.symm h),
    add_zero]
  rw [add_right_comm]
  ring

open MvPowerSeries.WithPiTopology in
theorem pderiv_subst [Fintype σ] {a : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (f : MvPowerSeries σ R) (j : τ) :
    pderiv (R := S) j (subst a f) = ∑ i, subst a (pderiv (R := R) i f) * pderiv (R := S) j (a i) := by
  classical
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  have hc := continuous_subst (R := R) ha
  refine congr_fun (DenseRange.equalizer
    (MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries (σ := σ) (R := R))
    (g := fun f => pderiv (R := S) j (subst a f))
    (h := fun f => ∑ i, subst a (pderiv (R := R) i f) * pderiv (R := S) j (a i))
    ((continuous_pderiv j).comp hc)
    (continuous_finsetSum _ fun i _ => (hc.comp (continuous_pderiv i)).mul continuous_const)
    ?_) f
  funext p
  simp only [Function.comp_apply]
  induction p using MvPolynomial.induction_on with
  | C r =>
    simp [MvPolynomial.coe_C, pderiv_C, subst_C' ha, subst_zero' ha]
  | add p q hp hq =>
    simp only [MvPolynomial.coe_add, subst_add ha, map_add (f := _), hp, hq, add_mul,
      Finset.sum_add_distrib]
  | mul_X p n hp =>
    simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, subst_mul ha, Derivation.leibniz, hp,
      smul_eq_mul, subst_add ha, subst_X ha, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_eq_single n]
      · simp [subst_one' ha]
      · intro b _ hb
        simp [pderiv_X_of_ne (Ne.symm hb), subst_zero' ha]
      · simp
    · exact Finset.sum_congr rfl fun i _ => by ring

theorem pderiv_powerSeries_subst {a : MvPowerSeries τ S} (ha : PowerSeries.HasSubst a)
    (f : PowerSeries R) (j : τ) :
    pderiv (R := S) j (PowerSeries.subst a f) =
      PowerSeries.subst a (PowerSeries.derivative (R := R) f) * pderiv (R := S) j a := by
  have h := pderiv_subst (σ := Unit) (a := fun _ => a) ha.const f j
  simpa [PowerSeries.subst, PowerSeries.derivative] using h

theorem constantCoeff_subst_of_zero {a : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = algebraMap R S (constantCoeff f) := by
  have h : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by simp
  have h' : constantCoeff (subst a (f - C (constantCoeff f))) = 0 :=
    constantCoeff_subst_eq_zero ha ha0 (by simp)
  conv_lhs => rw [h, subst_add ha, map_add (f := _), h', subst_C' ha]
  simp

theorem pderiv_map {T : Type*} [CommRing T] (φ : R →+* T) (i : σ) (f : MvPowerSeries σ R) :
    pderiv (R := T) i (map φ f) = map φ (pderiv (R := R) i f) := by
  ext d
  simp [coeff_pderiv]

end Chain

section Poincare

variable {σ ι A : Type*} [CommRing A]

theorem natCast_mul_coeff_of_pderiv_eq {f a : MvPowerSeries σ A} {s : σ}
    (h : pderiv (R := A) s f = a) {α : σ →₀ ℕ} (hα : α s ≠ 0) :
    (α s : A) * coeff α f = coeff (α - single s 1) a := by
  have hle : single s 1 ≤ α := single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hα)
  rw [← h, coeff_pderiv, tsub_add_cancel_of_le hle, coe_tsub, Pi.sub_apply, single_eq_same,
    Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hα), Nat.cast_one, sub_add_cancel, mul_comm]

theorem ext_of_pderiv_of_coeff [IsAddTorsionFree A] (e : ι → σ) {f g : MvPowerSeries σ A}
    (hD : ∀ i, pderiv (R := A) (e i) f = pderiv (R := A) (e i) g)
    (h0 : ∀ α : σ →₀ ℕ, (∀ i, α (e i) = 0) → coeff α f = coeff α g) : f = g := by
  ext α
  by_cases h : ∀ i, α (e i) = 0
  · exact h0 α h
  push Not at h
  obtain ⟨i, hi⟩ := h
  have h1 := natCast_mul_coeff_of_pderiv_eq (hD i) hi
  have h2 := natCast_mul_coeff_of_pderiv_eq (rfl : pderiv (R := A) (e i) g = _) hi
  rw [← h2, ← nsmul_eq_mul, ← nsmul_eq_mul] at h1
  exact IsAddTorsionFree.eq_of_nsmul_eq_nsmul_of_addCommute hi (AddCommute.all _ _) h1

variable [Algebra ℚ A]

theorem existsUnique_primitive_param {e : ι → σ} (he : Function.Injective e)
    (a : ι → MvPowerSeries σ A) (ha : ∀ i j, pderiv (R := A) (e i) (a j) = pderiv (R := A) (e j) (a i)) :
    ∃! f : MvPowerSeries σ A, (∀ α : σ →₀ ℕ, (∀ i, α (e i) = 0) → coeff α f = 0) ∧
      ∀ i, pderiv (R := A) (e i) f = a i := by
  classical
  have huniq : HasUniqueDiv A := HasUniqueDiv.of_module_rat A
  haveI : IsAddTorsionFree A :=
    ⟨fun {n} hn {a b} _ hh => huniq.nsmul_right_injective (n := n) hn hh⟩
  have key : ∀ (α : σ →₀ ℕ) (i j : ι), α (e i) ≠ 0 → α (e j) ≠ 0 →
      (α (e j) : A) * coeff (α - single (e i) 1) (a i) =
        (α (e i) : A) * coeff (α - single (e j) 1) (a j) := by
    intro α i j hi hj
    by_cases hij : i = j
    · rw [hij]
    have hne : e i ≠ e j := fun h => hij (he h)
    have e1 : (α - single (e i) 1 : σ →₀ ℕ) (e j) = α (e j) := by
      simp [single_eq_of_ne (Ne.symm hne)]
    have e2 : (α - single (e j) 1 : σ →₀ ℕ) (e i) = α (e i) := by
      simp [single_eq_of_ne hne]
    have h1 := natCast_mul_coeff_of_pderiv_eq (rfl : pderiv (R := A) (e j) (a i) = _) (e1 ▸ hj)
    have h2 := natCast_mul_coeff_of_pderiv_eq (rfl : pderiv (R := A) (e i) (a j) = _) (e2 ▸ hi)
    rw [e1] at h1
    rw [e2] at h2
    rw [h1, h2, ha, tsub_right_comm]
  let f : MvPowerSeries σ A := fun α =>
    if h : ∃ i, α (e i) ≠ 0 then
      ((α (e h.choose) : ℚ)⁻¹) • coeff (α - single (e h.choose) 1) (a h.choose) else 0
  have hf : ∀ α, coeff α f = if h : ∃ i, α (e i) ≠ 0 then
      ((α (e h.choose) : ℚ)⁻¹) • coeff (α - single (e h.choose) 1) (a h.choose) else 0 :=
    fun _ => rfl
  have hf0 : ∀ α : σ →₀ ℕ, (∀ i, α (e i) = 0) → coeff α f = 0 := by
    intro α h
    rw [hf, dite_eq_right]
    push Not
    exact h
  have hf1 : ∀ i, pderiv (R := A) (e i) f = a i := by
    intro i
    ext n
    have hi : (n + single (e i) 1 : σ →₀ ℕ) (e i) ≠ 0 := by simp
    have hex : ∃ j, (n + single (e i) 1 : σ →₀ ℕ) (e j) ≠ 0 := ⟨i, hi⟩
    have hk := key _ hex.choose i hex.choose_spec hi
    have hq : (((n + single (e i) 1 : σ →₀ ℕ) (e hex.choose) : ℕ) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hex.choose_spec
    rw [add_tsub_cancel_right] at hk
    rw [coeff_pderiv, hf, dite_eq_left hex, smul_mul_assoc, mul_comm]
    have : ((n (e i) : A) + 1) = (((n + single (e i) 1 : σ →₀ ℕ) (e i) : ℕ) : A) := by simp
    rw [this, hk, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hq,
      one_smul]
  refine ⟨f, ⟨hf0, hf1⟩, fun g hg => ?_⟩
  exact ext_of_pderiv_of_coeff e (fun i => by rw [hg.2, hf1]) fun α h => by rw [hg.1 α h, hf0 α h]

end Poincare

end GlobalTheory.FormalCalc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EncardSmulMemLeEncardSmulInterNonempty
open MeasureTheory Set
open scoped ENNReal Pointwise

namespace GlobalTheory

section Multiplicity

variable {G X : Type*} [Group G] [MulAction G X]

variable [MeasurableSpace X] {μ : Measure X} [MeasurableConstSMul G X]
  [SMulInvariantMeasure G X μ] [Countable G] {B D : Set X}

@[to_additive
]
theorem tsum_indicator_smul_eq_encard (B : Set X) (x : X) :
    ∑' g : G, ((fun y => g • y) ⁻¹' B).indicator (fun _ => (1 : ℝ≥0∞)) x
      = ({g : G | g • x ∈ B}.encard : ℝ≥0∞) := by
  rw [← ENNReal.tsum_set_one, tsum_subtype {g : G | g • x ∈ B} (fun _ => (1 : ℝ≥0∞))]
  refine tsum_congr fun g => ?_
  by_cases h : g • x ∈ B <;> simp [Set.indicator, h]

@[to_additive
]
theorem sum_restrict_preimage_smul_le (hB : NullMeasurableSet B μ) {m : ℝ≥0∞}
    (hm : ∀ᵐ x ∂μ.restrict D, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ≤ m) :
    (Measure.sum fun g : G => (μ.restrict D).restrict ((fun y => g • y) ⁻¹' B))
      ≤ m • μ.restrict D := by
  have hB' : ∀ g : G, NullMeasurableSet ((fun y => g • y) ⁻¹' B) (μ.restrict D) := fun g =>
    (hB.preimage (measurePreserving_smul g μ).quasiMeasurePreserving).mono
      Measure.restrict_le_self
  rw [Measure.le_iff]
  intro A hA
  rw [Measure.sum_apply _ hA, Measure.smul_apply, smul_eq_mul]
  have h1 : ∀ g : G, ((μ.restrict D).restrict ((fun y => g • y) ⁻¹' B)) A
      = ∫⁻ x in A, ((fun y => g • y) ⁻¹' B).indicator (fun _ => (1 : ℝ≥0∞)) x
          ∂(μ.restrict D) := by
    intro g
    rw [lintegral_indicator₀ ((hB' g).mono Measure.restrict_le_self), setLIntegral_one,
      Measure.restrict_apply hA,
      Measure.restrict_apply₀ ((hB' g).mono Measure.restrict_le_self), inter_comm]
  simp_rw [h1]
  rw [← lintegral_tsum fun g => (aemeasurable_const.indicator₀
    ((hB' g).mono Measure.restrict_le_self))]
  simp_rw [tsum_indicator_smul_eq_encard]
  calc ∫⁻ x in A, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ∂(μ.restrict D)
      ≤ ∫⁻ _ in A, m ∂(μ.restrict D) := lintegral_mono_ae (ae_restrict_of_ae hm)
    _ = m * (μ.restrict D) A := by rw [setLIntegral_const]

@[to_additive setLIntegral_le_mul_of_ae_covers_vadd
]
theorem setLIntegral_le_mul_of_ae_covers (hD : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D)
    (hB : NullMeasurableSet B μ) {u : X → ℝ≥0∞} (hu : ∀ (g : G) (x : X), u (g • x) = u x)
    {m : ℝ≥0∞} (hm : ∀ᵐ x ∂μ.restrict D, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ≤ m) :
    ∫⁻ x in B, u x ∂μ ≤ m * ∫⁻ x in D, u x ∂μ := by
  have hcov : B ≤ᵐ[μ] (⋃ g : G, g • (((fun y => g • y) ⁻¹' B) ∩ D) : Set X) := by
    filter_upwards [hD] with x ⟨g, hg⟩ hx
    refine mem_iUnion.2 ⟨g⁻¹, g • x, ⟨?_, hg⟩, by simp⟩
    change g⁻¹ • g • x ∈ B
    rw [inv_smul_smul]
    exact hx
  have hB' : ∀ g : G, NullMeasurableSet ((fun y => g • y) ⁻¹' B) (μ.restrict D) := fun g =>
    (hB.preimage (measurePreserving_smul g μ).quasiMeasurePreserving).mono
      Measure.restrict_le_self
  calc ∫⁻ x in B, u x ∂μ
      ≤ ∫⁻ x in ⋃ g : G, g • (((fun y => g • y) ⁻¹' B) ∩ D), u x ∂μ :=
        lintegral_mono_set' hcov
    _ ≤ ∑' g : G, ∫⁻ x in g • (((fun y => g • y) ⁻¹' B) ∩ D), u x ∂μ := lintegral_iUnion_le _ _
    _ = ∑' g : G, ∫⁻ x, u x ∂((μ.restrict D).restrict ((fun y => g • y) ⁻¹' B)) := by
        refine tsum_congr fun g => ?_
        rw [Measure.restrict_restrict₀ (hB' g), ← image_smul,
          ← (measurePreserving_smul g μ).setLIntegral_comp_emb (measurableEmbedding_const_smul g)]
        simp only [hu]
    _ = ∫⁻ x, u x ∂(Measure.sum fun g : G =>
          (μ.restrict D).restrict ((fun y => g • y) ⁻¹' B)) := (lintegral_sum_measure _ _).symm
    _ ≤ ∫⁻ x, u x ∂(m • μ.restrict D) :=
        lintegral_mono' (sum_restrict_preimage_smul_le hB hm) le_rfl
    _ = m * ∫⁻ x in D, u x ∂μ := by rw [lintegral_smul_measure, smul_eq_mul]

omit [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] in
@[to_additive ae_encard_vadd_mem_le_one
]
theorem ae_encard_smul_mem_le_one (hD : IsFundamentalDomain G D μ) :
    ∀ᵐ x ∂μ, {g : G | g • x ∈ D}.encard ≤ 1 := by
  have h : ∀ᵐ x ∂μ, ∀ g₁ g₂ : G, g₁ ≠ g₂ → x ∉ g₁ • D ∩ g₂ • D := by
    refine ae_all_iff.2 fun g₁ => ae_all_iff.2 fun g₂ => ?_
    by_cases h : g₁ = g₂
    · simp [h]
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hD.aedisjoint h)] with x hx _ using hx
  filter_upwards [h] with x hx
  rw [encard_le_one_iff]
  intro a b ha hb
  by_contra hab
  refine hx a⁻¹ b⁻¹ (by simpa using hab) ⟨?_, ?_⟩
  · rw [mem_smul_set_iff_inv_smul_mem, inv_inv]; exact ha
  · rw [mem_smul_set_iff_inv_smul_mem, inv_inv]; exact hb

@[to_additive setLIntegral_le_of_isAddFundamentalDomain_of_ae_covers
]
theorem setLIntegral_le_of_isFundamentalDomain_of_ae_covers {D' : Set X}
    (hD : IsFundamentalDomain G D μ) (hD' : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D')
    {u : X → ℝ≥0∞} (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ∫⁻ x in D, u x ∂μ ≤ ∫⁻ x in D', u x ∂μ := by
  have := setLIntegral_le_mul_of_ae_covers hD' hD.nullMeasurableSet hu (m := 1) (by
    filter_upwards [ae_restrict_of_ae (ae_encard_smul_mem_le_one hD)] with x hx
    exact_mod_cast ENat.toENNReal_le.2 hx)
  simpa using this

@[to_additive measure_le_of_isAddFundamentalDomain_of_ae_covers
]
theorem measure_le_of_isFundamentalDomain_of_ae_covers {D' : Set X}
    (hD : IsFundamentalDomain G D μ) (hD' : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D') : μ D ≤ μ D' := by
  simpa using setLIntegral_le_of_isFundamentalDomain_of_ae_covers hD hD' (u := fun _ => 1)
    (fun _ _ => rfl)

end Multiplicity

section Subgroup

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}
  [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] [Countable G] {D D' : Set X}
  {K : Subgroup G}

variable {E : Type*} [NormedAddCommGroup E]

variable [NormedSpace ℝ E]

end Subgroup

section Kernel

variable {G H X : Type*} [Group G] [Group H] [MulAction G X] [MulAction H X] [MeasurableSpace X]
  {μ : Measure X} {B D D' : Set X} {φ : G →* H}

variable [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] [Countable G]

variable {K : Subgroup G} {H' : Type*} [Group H'] [MulAction H' X] {φ' : K →* H'}

end Kernel

section Image

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}
  [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] [Countable G] {B D D' : Set X}
  {K : Subgroup G}

end Image

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsOrthonormalOfLinearIndependent
open Matrix Module
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.Hadamard

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem norm_orthonormalBasis_det_le (b : OrthonormalBasis ι 𝕜 E) (x : ι → E) :
    ‖b.toBasis.det x‖ ≤ ∏ k, ‖x k‖ := by
  classical
  haveI : FiniteDimensional 𝕜 E := b.toBasis.finiteDimensional_of_finite
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  letI : LocallyFiniteOrderBot ι :=
    LocallyFiniteOrderBot.ofIic ι (fun a => Finset.univ.filter (· ≤ a)) (by simp)
  have h : finrank 𝕜 E = Fintype.card ι := finrank_eq_card_basis b.toBasis
  set c := InnerProductSpace.gramSchmidtOrthonormalBasis h x with hc
  have h1 : b.toBasis.det x = b.toBasis.det c * c.toBasis.det x := by
    conv_lhs => rw [b.toBasis.det.eq_smul_basis_det c.toBasis]
    simp
  have h2 : c.toBasis.det x = ∏ i, ⟪c i, x i⟫_𝕜 := by
    convert InnerProductSpace.gramSchmidtOrthonormalBasis_det h x
  rw [h1, norm_mul, b.det_to_matrix_orthonormalBasis c, one_mul, h2, norm_prod]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => ?_
  simpa [c.orthonormal.1 i] using norm_inner_le_norm (𝕜 := 𝕜) (c i) (x i)

theorem norm_det_le_prod_col (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ≤ ∏ j, √(∑ i, ‖A i j‖ ^ 2) := by
  have h := norm_orthonormalBasis_det_le (EuclideanSpace.basisFun ι 𝕜)
    (fun j => (WithLp.toLp 2 fun i => A i j : EuclideanSpace 𝕜 ι))
  simp only [EuclideanSpace.norm_eq] at h
  convert h using 2
  rw [Basis.det_apply]
  congr 1

theorem norm_det_le_prod_row (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ≤ ∏ i, √(∑ j, ‖A i j‖ ^ 2) := by
  rw [← det_transpose]
  exact norm_det_le_prod_col Aᵀ

theorem norm_det_sq_le_prod_col (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ^ 2 ≤ ∏ j, ∑ i, ‖A i j‖ ^ 2 := by
  refine (pow_le_pow_left₀ (norm_nonneg _) (norm_det_le_prod_col A) 2).trans_eq ?_
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun j _ => Real.sq_sqrt (by positivity)

theorem norm_det_sq_le_prod_row (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ^ 2 ≤ ∏ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [← det_transpose]
  exact norm_det_sq_le_prod_col Aᵀ

theorem det_gram_nonneg (x : ι → E) : 0 ≤ (gram 𝕜 x).det :=
  (posSemidef_gram 𝕜 x).det_nonneg

theorem re_det_gram_nonneg (x : ι → E) : 0 ≤ RCLike.re (gram 𝕜 x).det :=
  (RCLike.nonneg_iff.mp (det_gram_nonneg x)).1

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem gram_sum_smul [Fintype κ] (e : ι → E) (m : Matrix ι κ 𝕜) :
    gram 𝕜 (fun j => ∑ i, m i j • e i) = mᴴ * gram 𝕜 e * m := by
  ext j k
  simp only [gram_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, Matrix.mul_apply,
    conjTranspose_apply, Finset.sum_mul, Finset.mul_sum, RCLike.star_def]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem re_det_gram_sum_smul (e : ι → E) (m : Matrix ι ι 𝕜) :
    RCLike.re (gram 𝕜 (fun j => ∑ i, m i j • e i)).det
      = ‖m.det‖ ^ 2 * RCLike.re (gram 𝕜 e).det := by
  rw [gram_sum_smul, det_mul, det_mul, det_conjTranspose, mul_right_comm, RCLike.star_def,
    RCLike.conj_mul]
  norm_cast
  rw [RCLike.re_ofReal_mul]

theorem exists_orthonormal_of_linearIndependent {x : ι → E} (hx : LinearIndependent 𝕜 x) :
    ∃ (e : ι → E) (m : Matrix ι ι 𝕜), Orthonormal 𝕜 e ∧ ∀ j, x j = ∑ i, m i j • e i := by
  set S := Submodule.span 𝕜 (Set.range x)
  haveI : FiniteDimensional 𝕜 S := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range x)
  have h : finrank 𝕜 S = Fintype.card ι := finrank_span_eq_card hx
  let b : OrthonormalBasis ι 𝕜 S :=
    (stdOrthonormalBasis 𝕜 S).reindex (Fintype.equivFinOfCardEq h.symm).symm
  let y : ι → S := fun j => ⟨x j, Submodule.subset_span ⟨j, rfl⟩⟩
  refine ⟨fun i => (b i : E), of fun i j => b.repr (y j) i,
    b.orthonormal.comp_linearIsometry S.subtypeₗᵢ, fun j => ?_⟩
  have := congrArg (fun s : S => (s : E)) (b.sum_repr (y j))
  simpa using this.symm

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem norm_sum_smul_sq {e : ι → E} (he : Orthonormal 𝕜 e) (c : ι → 𝕜) :
    ‖∑ i, c i • e i‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
  have h := he.inner_sum c c Finset.univ
  rw [inner_self_eq_norm_sq_to_K] at h
  simp only [RCLike.conj_mul] at h
  exact_mod_cast h

theorem re_det_gram_le_prod (x : ι → E) : RCLike.re (gram 𝕜 x).det ≤ ∏ k, ‖x k‖ ^ 2 := by
  by_cases hx : LinearIndependent 𝕜 x
  · obtain ⟨e, m, he, hm⟩ := exists_orthonormal_of_linearIndependent hx
    obtain rfl : x = fun j => ∑ i, m i j • e i := funext hm
    rw [re_det_gram_sum_smul, gram_eq_one_iff_orthonormal.mpr he]
    simp only [det_one, RCLike.one_re, mul_one, norm_sum_smul_sq he]
    exact norm_det_sq_le_prod_col m
  · rw [← det_gram_ne_zero_iff_linearIndependent, not_not] at hx
    rw [hx, map_zero]
    positivity

omit [DecidableEq ι] in
theorem det_gram_comp_equiv [DecidableEq ι] (x : ι → E) (σ : κ ≃ ι) :
    (gram 𝕜 (x ∘ σ)).det = (gram 𝕜 x).det :=
  det_submatrix_equiv_self σ (gram 𝕜 x)

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem sum_norm_apply_sq_le {e : ι → E} (he : Orthonormal 𝕜 e) (φ : E →L[𝕜] 𝕜) :
    ∑ i, ‖φ (e i)‖ ^ 2 ≤ ‖φ‖ ^ 2 := by
  set s := ∑ i, ‖φ (e i)‖ ^ 2 with hs
  set v := ∑ i, (starRingEnd 𝕜) (φ (e i)) • e i with hv
  have hs0 : 0 ≤ s := by positivity
  have h1 : ‖v‖ ^ 2 = s := by simp [hv, norm_sum_smul_sq he, hs]
  have h2 : φ v = (s : 𝕜) := by
    simp [hv, hs, RCLike.conj_mul]
  have h3 : s ≤ ‖φ‖ * ‖v‖ := by
    have := φ.le_opNorm v
    rwa [h2, RCLike.norm_ofReal, abs_of_nonneg hs0] at this
  nlinarith [sq_nonneg (‖φ‖ - ‖v‖)]

theorem norm_det_apply_sq_le (φ : ι → E →L[𝕜] 𝕜) (x : ι → E) :
    ‖(of fun j k => φ j (x k)).det‖ ^ 2 ≤ RCLike.re (gram 𝕜 x).det * ∏ j, ‖φ j‖ ^ 2 := by
  by_cases hx : LinearIndependent 𝕜 x
  · obtain ⟨e, m, he, hm⟩ := exists_orthonormal_of_linearIndependent hx
    have h : (of fun j k => φ j (x k)) = (of fun j i => φ j (e i)) * m := by
      ext j k
      simp [hm, Matrix.mul_apply, mul_comm]
    rw [h]
    obtain rfl : x = fun j => ∑ i, m i j • e i := funext hm
    rw [re_det_gram_sum_smul, gram_eq_one_iff_orthonormal.mpr he, det_mul, norm_mul, mul_pow,
      det_one, RCLike.one_re, mul_one, mul_comm]
    refine mul_le_mul_of_nonneg_left ((norm_det_sq_le_prod_row _).trans ?_) (by positivity)
    exact Finset.prod_le_prod₀ (fun _ _ => by positivity) fun j _ => sum_norm_apply_sq_le he (φ j)
  · obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hx
    have h0 : (of fun j k => φ j (x k)).det = 0 := by
      refine exists_mulVec_eq_zero_iff.mp ⟨g, fun h => hi (congrFun h i), ?_⟩
      funext j
      have := congrArg (φ j) hg
      simpa [mulVec, dotProduct, mul_comm] using this
    rw [h0, norm_zero]
    exact (by norm_num : (0 : ℝ) ^ 2 ≤ 0).trans
      (mul_nonneg (re_det_gram_nonneg x) (by positivity))

theorem norm_det_apply_le (φ : ι → E →L[𝕜] 𝕜) (x : ι → E) :
    ‖(of fun j k => φ j (x k)).det‖ ≤ (∏ k, ‖x k‖) * ∏ j, ‖φ j‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [mul_pow, ← Finset.prod_pow, ← Finset.prod_pow]
  exact (norm_det_apply_sq_le φ x).trans
    (mul_le_mul_of_nonneg_right (re_det_gram_le_prod x) (by positivity))

end GlobalTheory.Hadamard
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.StarInvMulVecDotProductMulVecInvMulVec
section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.OneLeDetOneAdd
open scoped ComplexOrder

namespace GlobalTheory.OneLeDetOneAdd

theorem one_le_det_one_add {𝕜 : Type*} {n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    {D : Matrix n n 𝕜} (hD : D.PosSemidef) : (1 : 𝕜) ≤ (1 + D).det := by
  have hA : (1 + D).IsHermitian := Matrix.isHermitian_one.add hD.1
  have hμ : ∀ i, 1 ≤ hA.eigenvalues i := by
    intro i
    have hv1 : RCLike.re (star ⇑(hA.eigenvectorBasis i) ⬝ᵥ ⇑(hA.eigenvectorBasis i)) = 1 := by
      rw [dotProduct_comm]
      simp only [← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
        hA.eigenvectorBasis.orthonormal.1 i, algebraMap.coe_one, one_pow, RCLike.one_re]
    have h := hA.eigenvalues_eq i
    rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, map_add (f := _), hv1] at h
    have h0 := hD.re_dotProduct_nonneg ⇑(hA.eigenvectorBasis i)
    linarith
  have hprod : (1 : ℝ) ≤ ∏ i, hA.eigenvalues i := by
    calc (1 : ℝ) = ∏ _i : n, (1 : ℝ) := by simp
      _ ≤ ∏ i, hA.eigenvalues i := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun i _ => hμ i)
  rw [hA.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
  calc (1 : 𝕜) = ((1 : ℝ) : 𝕜) := by simp
    _ ≤ _ := RCLike.ofReal_le_ofReal.mpr hprod

end GlobalTheory.OneLeDetOneAdd
end

open Matrix
open scoped ComplexOrder MatrixOrder

namespace GlobalTheory

section RCLike

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]

theorem trace_mul_nonneg_of_posSemidef {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  classical
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have h := (hB.mul_mul_conjTranspose_same C).trace_nonneg
  rwa [trace_mul_cycle, ← star_eq_conjTranspose] at h

theorem re_trace_mul_nonneg_of_posSemidef {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ RCLike.re (A * B).trace :=
  (RCLike.nonneg_iff.mp (trace_mul_nonneg_of_posSemidef hA hB)).1

omit [Fintype n] in
theorem posSemidef_of_le {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (h : A ≤ B) : B.PosSemidef :=
  (hA.nonneg.trans h).posSemidef

omit [Fintype n] in
theorem posDef_of_le {A B : Matrix n n 𝕜} (hA : A.PosDef) (h : A ≤ B) : B.PosDef := by
  have := hA.add_posSemidef (le_iff.mp h)
  rwa [add_sub_cancel] at this

theorem conjTranspose_mul_mul_le_of_le {m : Type*} [Finite m] {A B : Matrix n n 𝕜} (h : A ≤ B)
    (C : Matrix n m 𝕜) : Cᴴ * A * C ≤ Cᴴ * B * C := by
  have := (le_iff.mp h).conjTranspose_mul_mul_same C
  rwa [Matrix.mul_sub, Matrix.sub_mul] at this

omit [Fintype n] in
theorem transpose_le_transpose_of_le {A B : Matrix n n 𝕜} (h : A ≤ B) : Aᵀ ≤ Bᵀ := by
  have := (le_iff.mp h).transpose
  rwa [transpose_sub] at this

omit [Fintype n] in
theorem real_smul_le_real_smul_of_le {A B : Matrix n n 𝕜} (h : A ≤ B) {c : ℝ} (hc : 0 ≤ c) :
    c • A ≤ c • B := by
  have := (le_iff.mp h).smul hc
  rwa [smul_sub] at this

variable [DecidableEq n]

theorem inv_le_inv_of_posDef_of_le {A B : Matrix n n 𝕜} (hA : A.PosDef) (h : A ≤ B) :
    B⁻¹ ≤ A⁻¹ := by
  have hB := posDef_of_le hA h
  have hAi := hA.inv
  let _ := hB.isUnit.invertible
  let _ := hA.isUnit.invertible
  let _ := hAi.isUnit.invertible
  have h1 := PosDef.fromBlocks₁₁ (1 : Matrix n n 𝕜) B hAi
  have h2 := PosDef.fromBlocks₂₂ A⁻¹ (1 : Matrix n n 𝕜) hB
  simp only [conjTranspose_one, Matrix.mul_one, Matrix.one_mul, inv_inv_of_invertible] at h1 h2
  exact h2.mp (h1.mpr h)

theorem one_le_det_one_add_of_posSemidef {D : Matrix n n 𝕜} (hD : D.PosSemidef) :
    1 ≤ (1 + D).det := by
  apply _root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add <;> assumption

theorem det_le_det_of_posSemidef_of_le {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (h : A ≤ B) :
    A.det ≤ B.det := by
  by_cases h0 : A.det = 0
  · rw [h0]; exact (posSemidef_of_le hA h).det_nonneg
  have hA' := hA.posDef_iff_det_ne_zero.mpr h0
  obtain ⟨C, hC, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    hA'.isStrictlyPositive
  let _ := hC.invertible
  have hD := (le_iff.mp h).conjTranspose_mul_mul_same C⁻¹
  have hB : B = star C * (1 + C⁻¹ᴴ * (B - star C * C) * C⁻¹) * C := by
    have e1 : star C * C⁻¹ᴴ = 1 := by
      rw [star_eq_conjTranspose, ← conjTranspose_mul, inv_mul_of_invertible, conjTranspose_one]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1,
      Matrix.one_mul, Matrix.mul_assoc, inv_mul_of_invertible, Matrix.mul_one, add_sub_cancel]
  have h1 := one_le_det_one_add_of_posSemidef hD
  rw [hB, det_mul_right_comm, det_mul (star C * C)]
  exact le_mul_of_one_le_right hA.det_nonneg h1

theorem re_det_le_re_det_of_posSemidef_of_le {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (h : A ≤ B) : RCLike.re A.det ≤ RCLike.re B.det :=
  (RCLike.le_iff_re_im.mp (det_le_det_of_posSemidef_of_le hA h)).1

theorem re_det_pos_of_posDef {A : Matrix n n 𝕜} (hA : A.PosDef) : 0 < RCLike.re A.det :=
  (RCLike.pos_iff.mp hA.det_pos).1

theorem pow_mul_re_det_le_of_smul_le {B B' : Matrix n n 𝕜} (hB : B.PosSemidef) {c : ℝ}
    (hc : 0 ≤ c) (h : c • B ≤ B') :
    c ^ Fintype.card n * RCLike.re B.det ≤ RCLike.re B'.det := by
  have := re_det_le_re_det_of_posSemidef_of_le (hB.smul hc) h
  rwa [RCLike.real_smul_eq_coe_smul (K := 𝕜), det_smul, ← RCLike.ofReal_pow,
    RCLike.re_ofReal_mul] at this

theorem inv_real_smul_of_posDef {B : Matrix n n 𝕜} (hB : B.PosDef) {c : ℝ} (hc : c ≠ 0) :
    (c • B)⁻¹ = c⁻¹ • B⁻¹ := by
  let _ := hB.isUnit.invertible
  apply inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul,
    inv_mul_of_invertible]

theorem le_trace_smul_one_of_posSemidef {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    A ≤ A.trace • (1 : Matrix n n 𝕜) := by
  have hU : (hA.1.eigenvectorUnitary : Matrix n n 𝕜) * star (hA.1.eigenvectorUnitary : Matrix n n 𝕜)
      = 1 := Unitary.coe_mul_star_self _
  have h1 : A.trace • (1 : Matrix n n 𝕜) - A = (hA.1.eigenvectorUnitary : Matrix n n 𝕜) *
      diagonal (fun i => A.trace - (hA.1.eigenvalues i : 𝕜)) *
        star (hA.1.eigenvectorUnitary : Matrix n n 𝕜) := by
    rw [← diagonal_sub, ← smul_one_eq_diagonal, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hU]
    congr 1
    conv_lhs => rw [hA.1.spectral_theorem]
    rfl
  rw [le_iff, h1]
  refine PosSemidef.mul_mul_conjTranspose_same (PosSemidef.diagonal fun i => ?_) _
  have : hA.1.eigenvalues i ≤ ∑ j, hA.1.eigenvalues j :=
    Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  simp only [Pi.zero_apply, sub_nonneg]
  rw [hA.1.trace_eq_sum_eigenvalues]
  exact_mod_cast this

omit [Fintype n] [DecidableEq n] in
theorem smul_eq_re_smul_of_nonneg {c : 𝕜} (hc : 0 ≤ c) (A : Matrix n n 𝕜) :
    c • A = RCLike.re c • A := by
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  congr 1
  exact (RCLike.conj_eq_iff_re.mp (RCLike.conj_eq_iff_im.mpr (RCLike.nonneg_iff.mp hc).2)).symm

theorem le_re_trace_smul_one_of_posSemidef {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    A ≤ RCLike.re A.trace • (1 : Matrix n n 𝕜) := by
  rw [← smul_eq_re_smul_of_nonneg hA.trace_nonneg]
  exact le_trace_smul_one_of_posSemidef hA

section Gram

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

end Gram

theorem inv_smul_one_le_inv_of_le_smul_one {A : Matrix n n 𝕜} (hA : A.PosDef) {c : ℝ}
    (hc : 0 < c) (h : A ≤ c • (1 : Matrix n n 𝕜)) : c⁻¹ • (1 : Matrix n n 𝕜) ≤ A⁻¹ := by
  have := inv_le_inv_of_posDef_of_le hA h
  rwa [inv_real_smul_of_posDef PosDef.one hc.ne', inv_one] at this

end RCLike

section Rational

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

open NumberField IsCMField

variable [NumberField K] [IsCMField K]

end Rational

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FiniteInterClosedBallOfSeparated
open Metric MeasureTheory Module Set

namespace GlobalTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem finset_card_le_of_separated (s : Finset E) {d R : ℝ} (hd : 0 < d) (hR : 0 ≤ R) (x : E)
    (hs : ∀ a ∈ s, dist a x ≤ R) (hsep : (s : Set E).Pairwise fun a b => d ≤ dist a b) :
    (s.card : ℝ) ≤ (1 + 2 * R / d) ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  have hδ : 0 < d / 2 := by positivity
  have hρ : 0 < R + d / 2 := by positivity
  have D : Set.Pairwise (s : Set E) (Function.onFun Disjoint fun c => ball (c : E) (d / 2)) := by
    intro a ha b hb hab
    exact ball_disjoint_ball (by have := hsep ha hb hab; linarith)
  have hsub : (⋃ c ∈ s, ball (c : E) (d / 2)) ⊆ ball x (R + d / 2) := by
    refine iUnion₂_subset fun a ha => ball_subset_ball' ?_
    have := hs a ha
    linarith
  have I : (s.card : ENNReal) * ENNReal.ofReal ((d / 2) ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal ((R + d / 2) ^ finrank ℝ E) * μ (ball 0 1) := by
    calc (s.card : ENNReal) * ENNReal.ofReal ((d / 2) ^ finrank ℝ E) * μ (ball 0 1)
        = μ (⋃ c ∈ s, ball (c : E) (d / 2)) := by
          rw [measure_biUnion_finset D fun c _ => measurableSet_ball]
          simp only [μ.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball x (R + d / 2)) := measure_mono hsub
      _ = _ := μ.addHaar_ball_of_pos _ hρ
  have J : (s.card : ENNReal) * ENNReal.ofReal ((d / 2) ^ finrank ℝ E) ≤
      ENNReal.ofReal ((R + d / 2) ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos μ _ zero_lt_one).ne' measure_ball_lt_top.ne).1 I
  have K : (s.card : ℝ) * (d / 2) ^ finrank ℝ E ≤ (R + d / 2) ^ finrank ℝ E := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top J
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)] at this
  have e : 1 + 2 * R / d = (R + d / 2) / (d / 2) := by field_simp; ring
  rw [e, div_pow, le_div_iff₀ (by positivity)]
  exact K

theorem one_add_two_mul_div_pow_le {d R : ℝ} (hd : 0 < d) (hR : d ≤ R) (n : ℕ) :
    (1 + 2 * R / d) ^ n ≤ (3 * R / d) ^ n := by
  have hR0 : 0 ≤ R := hd.le.trans hR
  refine pow_le_pow_left₀ (by positivity) ?_ n
  have h1 : 1 ≤ R / d := (one_le_div hd).2 hR
  have : 3 * R / d = R / d + 2 * R / d := by ring
  linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsQr
open Matrix
open scoped ComplexOrder

namespace GlobalTheory.QRDecomp

theorem _root_.GlobalTheory.QRDecomp.exists_qr (n m : ℕ) (A : Matrix (Fin n) (Fin m) ℂ) (hA : IsUnit (Aᴴ * A).det) :
    ∃ (Q : Matrix (Fin n) (Fin m) ℂ) (u : Matrix (Fin m) (Fin m) ℂ),
      Qᴴ * Q = 1 ∧ u.BlockTriangular id ∧ IsUnit u.det ∧ A = Q * u := by
  classical
  have hinj : Function.Injective A.mulVec := by
    intro v w h
    have h2 : (Aᴴ * A) *ᵥ v = (Aᴴ * A) *ᵥ w := by rw [← mulVec_mulVec, ← mulVec_mulVec, h]
    exact (mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr hA)) h2
  have hS : (Aᴴ * A).PosDef := PosDef.conjTranspose_mul_self A hinj
  set L := LDL.lowerInv hS
  set d := LDL.diagEntries hS
  haveI : Invertible L := LDL.invertibleLowerInv hS
  have hLu : IsUnit L.det := isUnit_det_of_invertible L
  have hD : diagonal d = L * (Aᴴ * A) * Lᴴ := LDL.diag_eq_lowerInv_conj hS
  have hDpos : (diagonal d).PosDef := by
    rw [hD]
    exact hS.mul_mul_conjTranspose_same
      (vecMul_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr hLu))
  have hd : ∀ i, 0 < d i := fun i => by simpa using hDpos.diag_pos (i := i)
  have hdre : ∀ i, d i = ((d i).re : ℂ) ∧ 0 < (d i).re := fun i => by
    have h := hd i
    rw [Complex.pos_iff] at h
    exact ⟨Complex.ext (by simp) (by simp [h.2]), h.1⟩
  let r : Fin m → ℂ := fun i => ((Real.sqrt (d i).re : ℝ) : ℂ)
  have hr0 : ∀ i, r i ≠ 0 := fun i => by
    simp only [r, ne_eq, Complex.ofReal_eq_zero]
    exact (Real.sqrt_pos.mpr (hdre i).2).ne'
  have hrr : ∀ i, star (r i) * r i = d i := fun i => by
    simp only [r, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hdre i).2.le, ← (hdre i).1]
  have hLt : Lᴴ.BlockTriangular id := fun i j hij => by
    have h : LDL.lowerInv hS j i = 0 := LDL.isLowerTriangular_lowerInv hS hij
    simp [conjTranspose_apply, L, h]
  refine ⟨A * Lᴴ * diagonal (fun i => (r i)⁻¹), diagonal r * (Lᴴ)⁻¹, ?_, ?_, ?_, ?_⟩
  · have h1 : (A * Lᴴ * diagonal fun i => (r i)⁻¹)ᴴ * (A * Lᴴ * diagonal fun i => (r i)⁻¹)
        = (diagonal fun i => star (r i)⁻¹) * (L * (Aᴴ * A) * Lᴴ) * diagonal fun i => (r i)⁻¹ := by
      simp only [conjTranspose_mul, diagonal_conjTranspose, conjTranspose_conjTranspose,
        Matrix.mul_assoc]
      rfl
    rw [h1, ← hD, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [← hrr i]
    have h0 := hr0 i
    have h0' : star (r i) ≠ 0 := star_ne_zero.mpr h0
    rw [star_inv₀]
    field_simp
  · exact (blockTriangular_diagonal r).mul (blockTriangular_inv_of_blockTriangular hLt)
  · rw [det_mul, det_diagonal]
    exact (IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => hr0 i)).mul
      (isUnit_nonsing_inv_det _ (isUnit_det_of_invertible Lᴴ))
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal]
    have h1 : (fun i => (r i)⁻¹ * r i) = fun _ => (1 : ℂ) :=
      funext fun i => inv_mul_cancel₀ (hr0 i)
    rw [h1, diagonal_one, Matrix.one_mul, mul_inv_of_invertible, Matrix.mul_one]

end GlobalTheory.QRDecomp
end
