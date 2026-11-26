module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivRemCompLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzContinuousAtOfPointwiseOfBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzContinuousAtOfPointwiseOfBounded
open Filter Topology

namespace GlobalTheory

theorem norm_fderiv_le_of_small_of_lipschitz {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {g : V → E} (hg : Differentiable ℝ g) {C δ t : ℝ}
    (hC : 0 ≤ C) (ht : 0 < t)
    (hL : ∀ a b, ‖fderiv ℝ g a - fderiv ℝ g b‖ ≤ C * ‖a - b‖) (hδ : ∀ w, ‖g w‖ ≤ δ) (v : V) :
    ‖fderiv ℝ g v‖ ≤ 2 * δ / t + C * t := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ 0)
  have key : ∀ h : V, ‖h‖ = t → ‖fderiv ℝ g v h‖ ≤ 2 * δ + C * t * t := by
    intro h hh
    have hψd : ∀ x, DifferentiableAt ℝ (fun y => g y - fderiv ℝ g v y) x :=
      fun x => (hg x).sub (fderiv ℝ g v).differentiableAt
    have hψf : ∀ x, fderiv ℝ (fun y => g y - fderiv ℝ g v y) x = fderiv ℝ g x - fderiv ℝ g v := by
      intro x
      exact ((hg x).hasFDerivAt.sub (fderiv ℝ g v).hasFDerivAt).fderiv
    have hb : ∀ x ∈ Metric.closedBall v t,
        ‖fderiv ℝ (fun y => g y - fderiv ℝ g v y) x‖ ≤ C * t := by
      intro x hx
      rw [hψf]
      rw [Metric.mem_closedBall, dist_eq_norm] at hx
      exact (hL x v).trans (mul_le_mul_of_nonneg_left hx hC)
    have hvh : v + h ∈ Metric.closedBall v t := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, hh]
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hψd x) hb
      (convex_closedBall v t) (Metric.mem_closedBall_self ht.le) hvh
    rw [add_sub_cancel_left, hh, map_add (f := _)] at hmv
    have e1 : g (v + h) - (fderiv ℝ g v v + fderiv ℝ g v h) - (g v - fderiv ℝ g v v) =
        (g (v + h) - g v) - fderiv ℝ g v h := by abel
    rw [e1] at hmv
    have e2 : fderiv ℝ g v h = (g (v + h) - g v) - ((g (v + h) - g v) - fderiv ℝ g v h) := by abel
    rw [e2]
    calc _ ≤ ‖g (v + h) - g v‖ + ‖(g (v + h) - g v) - fderiv ℝ g v h‖ := norm_sub_le _ _
      _ ≤ (δ + δ) + C * t * t :=
          add_le_add ((norm_sub_le _ _).trans (add_le_add (hδ _) (hδ _))) hmv
      _ = 2 * δ + C * t * t := by ring
  have hnn : 0 ≤ 2 * δ / t + C * t := add_nonneg (div_nonneg (by linarith) ht.le) (mul_nonneg hC ht.le)
  refine ContinuousLinearMap.opNorm_le_bound _ hnn (fun u => ?_)
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hu' : 0 < ‖u‖ := norm_pos_iff.2 hu
  have hs : 0 ≤ t / ‖u‖ := div_nonneg ht.le hu'.le
  have hk := key ((t / ‖u‖) • u) (by rw [norm_smul, Real.norm_of_nonneg hs, div_mul_cancel₀ t hu'.ne'])
  rw [ContinuousLinearMap.map_smul, norm_smul, Real.norm_of_nonneg hs] at hk
  have h3 : ‖fderiv ℝ g v u‖ * t ≤ (2 * δ + C * t * t) * ‖u‖ := by
    have e : ‖fderiv ℝ g v u‖ * t = (t / ‖u‖ * ‖fderiv ℝ g v u‖) * ‖u‖ := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hk hu'.le
  have e3 : (2 * δ / t + C * t) * ‖u‖ = (2 * δ + C * t * t) * ‖u‖ / t := by
    field_simp
  rw [e3, le_div_iff₀ ht]
  exact h3

theorem norm_iteratedFDeriv_sub_le_of_bound {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : V → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) {C : ℝ}
    (hC : ∀ v, ‖iteratedFDeriv ℝ (n + 1) f v‖ ≤ C) (a b : V) :
    ‖iteratedFDeriv ℝ n f a - iteratedFDeriv ℝ n f b‖ ≤ C * ‖a - b‖ := by
  have hd : Differentiable ℝ (iteratedFDeriv ℝ n f) :=
    hf.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n)
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (f := iteratedFDeriv ℝ n f) (fun x _ => hd x)
    (fun x _ => by rw [norm_fderiv_iteratedFDeriv]; exact hC x) convex_univ (Set.mem_univ b)
    (Set.mem_univ a)

theorem eventually_forall_norm_le_of_lipschitz_of_decay {X V E : Type*} {l : Filter X}
    [NormedAddCommGroup V] [ProperSpace V] [NormedAddCommGroup E] {h : X → V → E}
    (hp : ∀ v, Tendsto (fun x => h x v) l (𝓝 0)) {C D : ℝ} (hC : 0 ≤ C)
    (hL : ∀ᶠ x in l, ∀ a b, ‖h x a - h x b‖ ≤ C * ‖a - b‖)
    (hD : ∀ᶠ x in l, ∀ v, ‖v‖ * ‖h x v‖ ≤ D) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in l, ∀ v, ‖h x v‖ ≤ ε := by
  have hR1 : (1 : ℝ) ≤ max 1 (D / ε) := le_max_left _ _
  have hDR : D ≤ ε * max 1 (D / ε) := by
    calc D = ε * (D / ε) := by field_simp
      _ ≤ ε * max 1 (D / ε) := mul_le_mul_of_nonneg_left (le_max_right _ _) hε.le
  have hη : 0 < ε / (2 * (C + 1)) := div_pos hε (by linarith)
  have hCη : C * (ε / (2 * (C + 1))) ≤ ε / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by linarith) two_pos]
    nlinarith
  obtain ⟨S, -, hSfin, hcover⟩ :=
    finite_cover_balls_of_compact (isCompact_closedBall (0 : V) (max 1 (D / ε))) hη
  have hS : ∀ᶠ x in l, ∀ s ∈ S, ‖h x s‖ < ε / 2 := by
    rw [hSfin.eventually_all]
    intro s _
    have hs := hp s
    rw [tendsto_zero_iff_norm_tendsto_zero] at hs
    exact hs.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hS, hL, hD] with x hxS hxL hxD v
  by_cases hv : ‖v‖ ≤ max 1 (D / ε)
  · have hvb : v ∈ Metric.closedBall (0 : V) (max 1 (D / ε)) := by rwa [mem_closedBall_zero_iff]
    obtain ⟨s, hs, hvs⟩ := Set.mem_iUnion₂.1 (hcover hvb)
    rw [Metric.mem_ball, dist_eq_norm] at hvs
    have e : h x v = h x s + (h x v - h x s) := by abel
    calc ‖h x v‖ = ‖h x s + (h x v - h x s)‖ := by rw [← e]
      _ ≤ ‖h x s‖ + ‖h x v - h x s‖ := norm_add_le _ _
      _ ≤ ε / 2 + C * (ε / (2 * (C + 1))) :=
          add_le_add (hxS s hs).le ((hxL v s).trans (mul_le_mul_of_nonneg_left hvs.le hC))
      _ ≤ ε := by linarith
  · replace hv := not_le.1 hv
    have hvpos : 0 < ‖v‖ := lt_of_lt_of_le one_pos (hR1.trans hv.le)
    have hmul : ‖v‖ * ‖h x v‖ ≤ ‖v‖ * ε := by
      calc ‖v‖ * ‖h x v‖ ≤ D := hxD v
        _ ≤ ε * max 1 (D / ε) := hDR
        _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_left hv.le hε.le
        _ = ‖v‖ * ε := mul_comm _ _
    exact le_of_mul_le_mul_left hmul hvpos

theorem eventually_forall_norm_iteratedFDeriv_le {X V : Type*} {l : Filter X}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {h : X → SchwartzMap V ℂ}
    (hp : ∀ v, Tendsto (fun x => h x v) l (𝓝 0))
    (hb : ∀ k n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in l, ∀ v, ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (h x) v‖ ≤ C)
    (n : ℕ) : ∀ ε : ℝ, 0 < ε → ∀ᶠ x in l, ∀ v, ‖iteratedFDeriv ℝ n (h x) v‖ ≤ ε := by
  induction n with
  | zero =>
    intro ε hε
    obtain ⟨C, hC0, hCb⟩ := hb 0 1
    obtain ⟨D, -, hDb⟩ := hb 1 0
    refine eventually_forall_norm_le_of_lipschitz_of_decay
      (h := fun x v => iteratedFDeriv ℝ 0 (h x) v) (C := C) (D := D) (fun v => ?_) hC0 ?_ ?_ hε
    · rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [norm_iteratedFDeriv_zero]
      exact tendsto_zero_iff_norm_tendsto_zero.1 (hp v)
    · filter_upwards [hCb] with x hx a b
      exact norm_iteratedFDeriv_sub_le_of_bound ((h x).smooth ⊤) 0 (fun w => by simpa using hx w) a b
    · filter_upwards [hDb] with x hx w
      simpa using hx w
  | succ n ih =>
    intro ε hε
    obtain ⟨C, hC0, hCb⟩ := hb 0 (n + 2)
    have ht : 0 < ε / (2 * (C + 1)) := div_pos hε (by linarith)
    have hCt : C * (ε / (2 * (C + 1))) ≤ ε / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by linarith) two_pos]
      nlinarith
    have hδ : 0 < ε * (ε / (2 * (C + 1))) / 4 := by
      have := mul_pos hε ht
      linarith
    filter_upwards [ih _ hδ, hCb] with x hx hxC v
    have hsm := (h x).smooth ⊤
    have hdiff : Differentiable ℝ (iteratedFDeriv ℝ n (h x)) :=
      hsm.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n)
    have hLip : ∀ a b, ‖fderiv ℝ (iteratedFDeriv ℝ n (h x)) a - fderiv ℝ (iteratedFDeriv ℝ n (h x)) b‖ ≤
        C * ‖a - b‖ := by
      intro a b
      rw [fderiv_iteratedFDeriv, Function.comp_apply, Function.comp_apply,
        ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]
      exact norm_iteratedFDeriv_sub_le_of_bound hsm (n + 1) (fun w => by simpa using hxC w) a b
    have hv := norm_fderiv_le_of_small_of_lipschitz hdiff hC0 ht hLip hx v
    rw [norm_fderiv_iteratedFDeriv] at hv
    have e : 2 * (ε * (ε / (2 * (C + 1))) / 4) / (ε / (2 * (C + 1))) = ε / 2 := by
      field_simp
      ring
    rw [e] at hv
    linarith

theorem schwartz_continuousAt_of_pointwise_of_bounded :
    ∀ {X : Type} [TopologicalSpace X] {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (F : X → SchwartzMap V ℂ) (x0 : X), (∀ v, ContinuousAt (fun x => F x v) x0) →
    (∀ k n : ℕ, ∃ C : ℝ, ∀ᶠ x in nhds x0, ∀ v, ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (F x) v‖ ≤ C) → ContinuousAt F x0 := by
  intro X _ V _ _ _ F x0 hc hb
  have hb' : ∀ k n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in nhds x0, ∀ v,
      ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (F x - F x0) v‖ ≤ C := by
    intro k n
    obtain ⟨C, hC⟩ := hb k n
    refine ⟨max C 0 + SchwartzMap.seminorm ℝ k n (F x0), add_nonneg (le_max_right _ _) (apply_nonneg _ _), ?_⟩
    filter_upwards [hC] with x hx v
    calc _ ≤ SchwartzMap.seminorm ℝ k n (F x - F x0) := SchwartzMap.le_seminorm ℝ k n _ v
      _ ≤ SchwartzMap.seminorm ℝ k n (F x) + SchwartzMap.seminorm ℝ k n (F x0) := map_sub_le_add _ _ _
      _ ≤ _ := add_le_add (SchwartzMap.seminorm_le_bound ℝ k n (F x) (le_max_right _ _)
          (fun w => (hx w).trans (le_max_left _ _))) le_rfl
  have hp : ∀ v, Tendsto (fun x => (F x - F x0) v) (nhds x0) (𝓝 0) := by
    intro v
    have h2 := (hc v).tendsto.sub_const (F x0 v)
    rw [sub_self] at h2
    exact h2
  rw [ContinuousAt, (schwartz_withSeminorms ℝ V ℂ).tendsto_nhds F (F x0)]
  rintro ⟨k, n⟩ ε hε
  obtain ⟨C2, hC20, hC2⟩ := hb' (2 * k) n
  have hη : 0 < ε ^ 2 / (4 * (C2 + 1)) := div_pos (pow_pos hε 2) (by linarith)
  have hCη : C2 * (ε ^ 2 / (4 * (C2 + 1))) ≤ (ε / 2) ^ 2 := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg ε]
  filter_upwards [eventually_forall_norm_iteratedFDeriv_le (h := fun x => F x - F x0) hp hb' n _ hη, hC2]
    with x hx hx2
  show SchwartzMap.seminorm ℝ k n (F x - F x0) < ε
  refine lt_of_le_of_lt (SchwartzMap.seminorm_le_bound ℝ k n _ (by linarith : (0 : ℝ) ≤ ε / 2)
    (fun v => ?_)) (by linarith)
  have ha : 0 ≤ ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (F x - F x0) v‖ := by positivity
  have hsq : (‖v‖ ^ k * ‖iteratedFDeriv ℝ n (F x - F x0) v‖) ^ 2 ≤ (ε / 2) ^ 2 := by
    have e : (‖v‖ ^ k * ‖iteratedFDeriv ℝ n (F x - F x0) v‖) ^ 2 =
        (‖v‖ ^ (2 * k) * ‖iteratedFDeriv ℝ n (F x - F x0) v‖) * ‖iteratedFDeriv ℝ n (F x - F x0) v‖ := by
      rw [pow_mul']
      ring
    rw [e]
    exact (mul_le_mul (hx2 v) (hx v) (norm_nonneg _) hC20).trans hCη
  nlinarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzContinuousAtOfPointwiseOfBoundedStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_continuousAt_of_continuousAt_apply_of_bounded : ∀ {X : Type} [TopologicalSpace X] {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (F : X → SchwartzMap V ℂ) (x0 : X), (∀ v, ContinuousAt (fun x => F x v) x0) →
    (∀ k n : ℕ, ∃ C : ℝ, ∀ᶠ x in nhds x0, ∀ v, ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (F x) v‖ ≤ C) → ContinuousAt F x0 := by
  first | exact @GlobalTheory.schwartz_continuousAt_of_pointwise_of_bounded | exact GlobalTheory.schwartz_continuousAt_of_pointwise_of_bounded | (intros; apply GlobalTheory.schwartz_continuousAt_of_pointwise_of_bounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainIntegralMulRight
open MeasureTheory

namespace GlobalTheory

theorem fundamentalDomain_integral_mul_right {G : Type} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (Γ : Subgroup G) [Countable Γ] (𝓕 : Set G) (f : G → ℂ) (a : G)
    (h : IsFundamentalDomain Γ 𝓕 μ) (hf : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) :
    (IntegrableOn f 𝓕 μ ↔ IntegrableOn (fun g => f (g * a)) 𝓕 μ) ∧
      ∫ g in 𝓕, f (g * a) ∂μ = ∫ g in 𝓕, f g ∂μ := by
  have hmp : MeasurePreserving (fun g : G => g * a) μ μ := measurePreserving_mul_right μ a
  have hme : MeasurableEmbedding (fun g : G => g * a) := measurableEmbedding_mulRight a
  have h' : IsFundamentalDomain Γ ((fun g : G => g * a) ⁻¹' 𝓕) μ :=
    h.preimage_of_equiv (e := id) hmp.quasiMeasurePreserving Function.bijective_id
      (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
  have hfa : ∀ (γ : Γ) (x : G), (fun g => f (g * a)) (γ • x) = (fun g => f (g * a)) x := by
    intro γ x
    simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc]
    exact hf γ γ.2 _
  refine ⟨?_, ?_⟩
  · rw [h.integrableOn_iff h' (f := fun g => f (g * a)) hfa]
    exact (hmp.integrableOn_comp_preimage hme (f := f) (s := 𝓕)).symm
  · rw [h.setIntegral_eq h' (f := fun g => f (g * a)) hfa]
    exact hmp.setIntegral_preimage_emb hme f 𝓕

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumFiberwiseOfFiniteSupportComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumFiberwiseOfFiniteSupportComplex
namespace GlobalTheory

theorem finsum_fiberwise_of_finite_support {A B : Type} (ρ : A → B) (f : A → ℂ)
    (hf : (Function.support f).Finite) :
    ∑ᶠ a, f a = ∑ᶠ b, ∑ᶠ a : {a // ρ a = b}, f a.1 := by
  classical
  set S := hf.toFinset with hS
  have hsupp : Function.support f ⊆ (S : Set A) := by simp [hS]
  have hinner : ∀ b, (∑ᶠ a : {a // ρ a = b}, f a.1) = ∑ a ∈ S with ρ a = b, f a := by
    intro b
    rw [finsum_subtype_eq_finsum_cond (fun a => ρ a = b)]
    have : (fun a => ∑ᶠ (_ : ρ a = b), f a) = fun a => if ρ a = b then f a else 0 := by
      funext a; exact finsum_eq_if
    rw [this, finsum_eq_sum_of_support_subset _ (s := S), Finset.sum_filter]
    intro a ha
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at ha
    obtain ⟨_, h⟩ := ha
    exact hsupp h
  simp_rw [hinner]
  rw [finsum_eq_sum_of_support_subset f hsupp,
    finsum_eq_sum_of_support_subset _ (s := S.image ρ)]
  · exact (Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem ρ ha) f).symm
  · intro b hb
    rw [Function.mem_support] at hb
    obtain ⟨a, ha, hab⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
    rw [Finset.mem_filter] at ha
    rw [Finset.coe_image]
    exact ⟨a, ha.1, ha.2⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumFiberwiseOfFiniteSupportComplexStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_fiberwise_of_finite_support_complex : ∀ {A B : Type} (ρ : A → B) (f : A → ℂ), (Function.support f).Finite → ∑ᶠ a, f a = ∑ᶠ b, ∑ᶠ a : {a // ρ a = b}, f a.1 := by
  first | exact @GlobalTheory.finsum_fiberwise_of_finite_support | exact GlobalTheory.finsum_fiberwise_of_finite_support | (intros; apply GlobalTheory.finsum_fiberwise_of_finite_support <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtaleSurjectiveProj
open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace GlobalTheory.Et.TrivTors

def sigmaFinSuccIso (V : Scheme.{0}) (k : ℕ) :
    (∐ fun _ : Fin (k + 1) => V) ≅ V ⨿ (∐ fun _ : Fin k => V) where
  hom := Sigma.desc (Fin.cases coprod.inl fun i => Sigma.ι (fun _ : Fin k => V) i ≫ coprod.inr)
  inv := coprod.desc (Sigma.ι (fun _ : Fin (k + 1) => V) 0)
    (Sigma.desc fun i => Sigma.ι (fun _ : Fin (k + 1) => V) i.succ)
  hom_inv_id := by
    ext i
    induction i using Fin.cases
    · simp only [Fin.cases_zero, Sigma.ι_comp_desc_assoc]
      exact coprod.inl_desc _ _
    · simp only [Fin.cases_succ, Sigma.ι_comp_desc_assoc, Category.assoc, Category.comp_id]
      erw [coprod.inr_desc, Sigma.ι_comp_desc]
  inv_hom_id := by
    apply coprod.hom_ext
    · erw [coprod.inl_desc_assoc, Sigma.ι_comp_desc]
      simp
    · erw [coprod.inr_desc_assoc]
      ext i
      simp

theorem sigmaFinSuccIso_hom_desc (V : Scheme.{0}) (k : ℕ) :
    (sigmaFinSuccIso V k).hom ≫ coprod.desc (𝟙 V) (Sigma.desc fun _ : Fin k => 𝟙 V) =
      Sigma.desc fun _ : Fin (k + 1) => 𝟙 V := by
  ext i
  induction i using Fin.cases
  · simp only [sigmaFinSuccIso, Sigma.ι_comp_desc_assoc, Fin.cases_zero, Sigma.ι_comp_desc]
    exact coprod.inl_desc _ _
  · simp only [sigmaFinSuccIso, Sigma.ι_comp_desc_assoc, Fin.cases_succ, Sigma.ι_comp_desc,
      Category.assoc]
    erw [coprod.inr_desc, Sigma.ι_comp_desc]

theorem isFinite_sigmaDesc_fin (V : Scheme.{0}) : ∀ k : ℕ, IsFinite (Sigma.desc fun _ : Fin k => 𝟙 V)
  | 0 => by
    have : IsEmpty (∐ fun _ : Fin 0 => V : Scheme.{0}) := by
      exact ⟨fun x => ((sigmaMk fun _ : Fin 0 => V).symm x).1.elim0⟩
    exact ((IsClosedImmersion.iff_isFinite_and_mono _).mp (by infer_instance)).1
  | k + 1 => by
    have := isFinite_sigmaDesc_fin V k
    rw [← sigmaFinSuccIso_hom_desc]
    infer_instance

end GlobalTheory.Et.TrivTors
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionBySetPowOfDivisibleNumberField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionBySetPowOfDivisibleNumberField
open NumberField

namespace GlobalTheory

open Submodule

theorem torsion_pow_card_succ {R : Type} [CommRing R] [IsDedekindDomain R]
    (M : Type) [AddCommGroup M] [Module R M] (w0 : Ideal R) (hmax : w0.IsMaximal) (hne : w0 ≠ ⊥)
    (hdiv : ∀ c : R, c ≠ 0 → Function.Surjective (fun g : M => c • g)) (j : ℕ) :
    Nat.card (torsionBySet R M ((w0 ^ (j + 1) : Ideal R) : Set R)) =
      Nat.card (torsionBySet R M ((w0 ^ j : Ideal R) : Set R)) *
        Nat.card (torsionBySet R M ((w0 : Ideal R) : Set R)) := by
  have hlt : w0 ^ 2 < w0 := by simpa using Ideal.pow_succ_lt_pow hne 1
  obtain ⟨c0, hc0, hc02⟩ := SetLike.exists_of_lt hlt
  have hdvd : w0 ∣ Ideal.span {c0} := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hc0)
  obtain ⟨b, hb⟩ := hdvd
  have hbw : ¬ b ≤ w0 := by
    intro hle
    apply hc02
    have : Ideal.span {c0} ≤ w0 ^ 2 := by rw [hb, pow_two]; exact Ideal.mul_mono_right hle
    exact this (Ideal.subset_span rfl)
  have hbtop : b ⊔ w0 = ⊤ := by
    by_contra h
    exact hbw (le_sup_left.trans (hmax.eq_of_le h le_sup_right).symm.le)
  have hcop : ∀ n : ℕ, b ⊔ w0 ^ n = ⊤ := by
    intro n
    rw [← Ideal.isCoprime_iff_sup_eq]
    exact (Ideal.isCoprime_iff_sup_eq.mpr hbtop).pow_right
  have hc0ne : c0 ≠ 0 := by rintro rfl; exact hc02 (zero_mem _)

  let Tj := torsionBySet R M ((w0 ^ j : Ideal R) : Set R)
  let Tj1 := torsionBySet R M ((w0 ^ (j + 1) : Ideal R) : Set R)
  let T1 := torsionBySet R M ((w0 : Ideal R) : Set R)
  have hmapsto : ∀ x ∈ Tj1, c0 • x ∈ Tj := by
    intro x hx
    rw [mem_torsionBySet_iff] at hx ⊢
    rintro ⟨a, ha⟩
    have : a * c0 ∈ w0 ^ (j + 1) := by rw [pow_succ]; exact Ideal.mul_mem_mul ha hc0
    simpa [smul_smul] using hx ⟨_, this⟩
  let φ : Tj1 →ₗ[R] Tj :=
    { toFun := fun x => ⟨c0 • (x : M), hmapsto x x.2⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun r x => by ext; simp [smul_comm c0 r] }
  have hsurj : Function.Surjective φ := by
    rintro ⟨g, hg⟩
    obtain ⟨g', hg'⟩ := hdiv c0 hc0ne g
    simp only at hg'
    have h1 : (1 : R) ∈ b ⊔ w0 ^ (j + 1) := by rw [hcop]; trivial
    obtain ⟨v, hv, u, hu, huv⟩ := Submodule.mem_sup.mp h1
    have hmem : v • g' ∈ Tj1 := by
      rw [mem_torsionBySet_iff]
      rintro ⟨a, ha⟩
      have hav : a * v ∈ w0 ^ j * Ideal.span {c0} := by
        rw [hb, ← mul_assoc, ← pow_succ]
        exact Ideal.mul_mem_mul ha hv
      obtain ⟨z, hz, hzc⟩ := (Submodule.mem_mul_span_singleton).mp hav
      simp only
      rw [smul_smul, ← hzc, ← smul_smul, hg']
      exact (mem_torsionBySet_iff _ _).mp hg ⟨z, hz⟩
    refine ⟨⟨v • g', hmem⟩, ?_⟩
    ext
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [smul_comm, hg']
    have hug : u • g = 0 := by
      have : u ∈ w0 ^ j := Ideal.pow_le_pow_right (Nat.le_succ j) hu
      exact (mem_torsionBySet_iff _ _).mp hg ⟨u, this⟩
    have : v = 1 - u := by rw [← huv]; ring
    rw [this, sub_smul, one_smul, hug, sub_zero]
  have hsub : T1 ≤ Tj1 := torsionBySet_le_torsionBySet_of_subset (by
    intro a ha
    exact Ideal.pow_le_self (Nat.succ_ne_zero j) ha)
  have hker : ∀ x : Tj1, x ∈ LinearMap.ker φ ↔ (x : M) ∈ T1 := by
    intro x
    rw [LinearMap.mem_ker]
    constructor
    · intro hx
      have hx' : c0 • (x : M) = 0 := by
        have := congrArg Subtype.val hx
        simpa [φ] using this
      rw [mem_torsionBySet_iff]
      rintro ⟨a, ha⟩
      have hw : w0 ≤ Ideal.span {c0} ⊔ w0 ^ (j + 1) := by
        have e : w0 * (b ⊔ w0 ^ j) = Ideal.span {c0} ⊔ w0 ^ (j + 1) := by
          rw [Ideal.mul_sup, ← hb, ← pow_succ']
        rw [hcop, Ideal.mul_top] at e
        exact e.le
      obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp (hw ha)
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hs
      have key : (r * c0 + t) • (x : M) = 0 := by
        rw [add_smul, mul_smul, hx', smul_zero, zero_add]
        exact (mem_torsionBySet_iff _ _).mp x.2 ⟨t, ht⟩
      rwa [hst] at key
    · intro hx
      ext
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, ZeroMemClass.coe_zero]
      exact (mem_torsionBySet_iff _ _).mp hx ⟨c0, hc0⟩
  have e1 : Nat.card (Tj1 ⧸ LinearMap.ker φ) = Nat.card Tj :=
    Nat.card_congr (φ.quotKerEquivOfSurjective hsurj).toEquiv
  have e2 : Nat.card (LinearMap.ker φ) = Nat.card T1 :=
    Nat.card_congr
      { toFun := fun x => ⟨(x.1 : M), (hker x.1).mp x.2⟩
        invFun := fun y => ⟨⟨y.1, hsub y.2⟩, (hker _).mpr y.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker φ), e1, e2, mul_comm]

theorem torsion_pow_card (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M]
    [Module (𝓞 F) M] (w0 : Ideal (𝓞 F)) (h : ℕ) :
    w0.IsMaximal → w0 ≠ ⊥ → (∀ c : 𝓞 F, c ≠ 0 → Function.Surjective (fun g : M => c • g)) →
    Nat.card (Submodule.torsionBySet (𝓞 F) M (w0 : Set (𝓞 F))) = Nat.card (𝓞 F ⧸ w0) ^ h →
    ∀ j : ℕ, Nat.card (Submodule.torsionBySet (𝓞 F) M ((w0 ^ j : Ideal (𝓞 F)) : Set (𝓞 F))) =
      Nat.card (𝓞 F ⧸ w0) ^ (j * h) := by
  intro hmax hne hdiv h1 j
  induction j with
  | zero =>
    simp only [pow_zero, zero_mul]
    have : torsionBySet (𝓞 F) M ((⊤ : Ideal (𝓞 F)) : Set (𝓞 F)) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [mem_torsionBySet_iff] at hx
      simpa using hx ⟨1, trivial⟩
    rw [Ideal.one_eq_top, this]
    simp
  | succ n ih =>
    rw [torsion_pow_card_succ M w0 hmax hne hdiv n, ih, h1, ← pow_add]
    ring_nf

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionBySetPowOfDivisibleNumberFieldStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_torsionBySet_pow_of_divisible_numberField : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (w0 : Ideal (𝓞 F)) (h : ℕ), w0.IsMaximal → w0 ≠ ⊥ → (∀ c : 𝓞 F, c ≠ 0 → Function.Surjective (fun g : M => c • g)) → Nat.card (Submodule.torsionBySet (𝓞 F) M (w0 : Set (𝓞 F))) = Nat.card (𝓞 F ⧸ w0) ^ h → ∀ j : ℕ, Nat.card (Submodule.torsionBySet (𝓞 F) M ((w0 ^ j : Ideal (𝓞 F)) : Set (𝓞 F))) = Nat.card (𝓞 F ⧸ w0) ^ (j * h) := by
  first | (exact @GlobalTheory.torsion_pow_card) | (exact GlobalTheory.torsion_pow_card) | (intros; apply GlobalTheory.torsion_pow_card  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormSmulLeftLinearPhaseLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormSmulLeftLinearPhaseLe
open scoped SchwartzMap
open Complex

namespace GlobalTheory.LinPhaseSeminorm

theorem iteratedDeriv_const_mul_cexp (a c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => c * Complex.exp (a * y)) =
      fun y : ℝ => c * a ^ n * Complex.exp (a * y) := _root_.GlobalTheory.CharFormDeriv.iteratedDeriv_const_mul_cexp a c n

theorem norm_cexp_neg_two_pi_I_mul (r : ℝ) :
    ‖Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]; simp

noncomputable def phaseLine (c t : ℝ) : ℝ → ℂ := fun y =>
  Complex.exp (-(2 * Real.pi * Complex.I) * ((t ^ 2 * c : ℝ) : ℂ)) *
    Complex.exp ((-(2 * Real.pi * Complex.I) * (t : ℂ)) * (y : ℂ))

theorem phase_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (c t : ℝ) :
    (fun x : V => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ)))
      = phaseLine c t ∘ ⇑L := by
  funext x
  simp only [phaseLine, Function.comp_apply, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem contDiff_phaseLine (c t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (phaseLine c t) := by
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  unfold phaseLine; fun_prop

theorem norm_iteratedDeriv_phaseLine (c t : ℝ) (i : ℕ) (y : ℝ) :
    ‖iteratedDeriv i (phaseLine c t) y‖ = (2 * Real.pi * |t|) ^ i := by
  have e : phaseLine c t = fun y : ℝ =>
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t ^ 2 * c : ℝ) : ℂ)) *
        Complex.exp ((-(2 * Real.pi * Complex.I) * (t : ℂ)) * (y : ℂ)) := rfl
  rw [e, iteratedDeriv_const_mul_cexp]
  have h2 : (-(2 * Real.pi * Complex.I) * (t : ℂ)) * (y : ℂ)
      = -(2 * Real.pi * Complex.I) * ((t * y : ℝ) : ℂ) := by push_cast; ring
  simp only
  rw [h2, norm_mul, norm_mul, norm_cexp_neg_two_pi_I_mul, norm_cexp_neg_two_pi_I_mul, norm_pow]
  simp [abs_of_pos Real.pi_pos]

theorem norm_iteratedFDeriv_phase_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (c : ℝ) {t : ℝ} (ht : |t| ≤ 1) (i : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ i (phaseLine c t ∘ ⇑L) x‖ ≤ (2 * Real.pi * ‖L‖) ^ i := by
  rw [L.iteratedFDeriv_comp_right (contDiff_phaseLine c t) x (i := i) (by exact_mod_cast le_top)]
  calc _ ≤ ‖iteratedFDeriv ℝ i (phaseLine c t) (L x)‖ * ∏ _j : Fin i, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = (2 * Real.pi * |t|) ^ i * ‖L‖ ^ i := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedDeriv_phaseLine]; simp
    _ ≤ (2 * Real.pi * 1) ^ i * ‖L‖ ^ i := by gcongr
    _ = (2 * Real.pi * ‖L‖) ^ i := by ring

theorem hasTemperateGrowth_phase {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (c t : ℝ) : Function.HasTemperateGrowth (phaseLine c t ∘ ⇑L) := by
  refine ⟨(contDiff_phaseLine c t).comp L.contDiff, fun n => ⟨0, (2 * Real.pi * |t| * ‖L‖) ^ n, fun x => ?_⟩⟩
  rw [L.iteratedFDeriv_comp_right (contDiff_phaseLine c t) x (i := n) (by exact_mod_cast le_top),
    pow_zero, mul_one]
  calc _ ≤ ‖iteratedFDeriv ℝ n (phaseLine c t) (L x)‖ * ∏ _j : Fin n, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = (2 * Real.pi * |t| * ‖L‖) ^ n := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedDeriv_phaseLine]; simp [mul_pow]

theorem seminorm_smulLeft_phase_le : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (c : ℝ) (k n : ℕ), ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 → ∀ f : 𝓢(V, ℂ),
      SchwartzMap.seminorm ℂ k n (SchwartzMap.smulLeftCLM ℂ
        (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ))) f)
        ≤ C * ∑ m ∈ Finset.range (n + 1), SchwartzMap.seminorm ℂ k m f := by
  intro V _ _ L c k n
  set B : ℝ := 2 ^ n * (1 + 2 * Real.pi * ‖L‖) ^ n with hB
  refine ⟨(n + 1) * B, fun t ht f => ?_⟩
  rw [phase_eq L c t]
  set S := ∑ m ∈ Finset.range (n + 1), SchwartzMap.seminorm ℂ k m f with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun m _ => apply_nonneg _ _
  have hL0 : 0 ≤ 2 * Real.pi * ‖L‖ := by positivity
  have hB0 : 0 ≤ B := by positivity
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun x => ?_
  have happ : (⇑(SchwartzMap.smulLeftCLM ℂ (phaseLine c t ∘ ⇑L) f))
      = fun y => (phaseLine c t ∘ ⇑L) y * f y := by
    funext y
    rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_phase L c t), smul_eq_mul]
  rw [happ]
  have hmul := norm_iteratedFDeriv_mul_le (N := ((⊤ : ℕ∞) : WithTop ℕ∞))
    ((contDiff_phaseLine c t).comp L.contDiff) (f.smooth ⊤) x (n := n) (by exact_mod_cast le_top)
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (phaseLine c t ∘ ⇑L) x‖ *
        ‖iteratedFDeriv ℝ (n - i) f x‖) ≤ B * S := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 := norm_iteratedFDeriv_phase_le L c ht i x
    have h2 : ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖ ≤ S :=
      (SchwartzMap.le_seminorm ℂ k (n - i) f x).trans
        (Finset.single_le_sum (f := fun m => SchwartzMap.seminorm ℂ k m f)
          (fun m _ => apply_nonneg _ _)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le n i))))
    have hc : (n.choose i : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n i
    have h4 : (2 * Real.pi * ‖L‖) ^ i ≤ (1 + 2 * Real.pi * ‖L‖) ^ n :=
      calc (2 * Real.pi * ‖L‖) ^ i ≤ (1 + 2 * Real.pi * ‖L‖) ^ i := by gcongr; linarith
        _ ≤ (1 + 2 * Real.pi * ‖L‖) ^ n := pow_le_pow_right₀ (by linarith) hi'
    calc ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (phaseLine c t ∘ ⇑L) x‖ *
          ‖iteratedFDeriv ℝ (n - i) f x‖)
        = ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (phaseLine c t ∘ ⇑L) x‖) *
          (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖) := by ring
      _ ≤ (2 ^ n * (1 + 2 * Real.pi * ‖L‖) ^ n) * S := by
          gcongr
          exact h1.trans h4
      _ = B * S := by rw [hB]
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => (phaseLine c t ∘ ⇑L) y * f y) x‖
      ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (phaseLine c t ∘ ⇑L) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ := by
        gcongr
    _ = ∑ i ∈ Finset.range (n + 1), ‖x‖ ^ k * ((n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (phaseLine c t ∘ ⇑L) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ _i ∈ Finset.range (n + 1), B * S := Finset.sum_le_sum hterm
    _ = (n + 1) * B * S := by simp; ring

end GlobalTheory.LinPhaseSeminorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormSmulLeftLinearPhaseLeStatement
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_seminorm_smulLeft_linear_phase_le : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (c : ℝ) (k n : ℕ), ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 → ∀ f : 𝓢(V, ℂ), SchwartzMap.seminorm ℂ k n (SchwartzMap.smulLeftCLM ℂ (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ))) f) ≤ C * ∑ m ∈ Finset.range (n + 1), SchwartzMap.seminorm ℂ k m f := by
  first | exact @GlobalTheory.LinPhaseSeminorm.seminorm_smulLeft_phase_le | exact GlobalTheory.LinPhaseSeminorm.seminorm_smulLeft_phase_le | (intros; apply GlobalTheory.LinPhaseSeminorm.seminorm_smulLeft_phase_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicMemRangeCompleteDvrPadicAlgCl
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicMemRangeCompleteDvrPadicAlgCl
open IsLocalRing

namespace GlobalTheory.PadicUnitBall

variable {p : ℕ} [Fact p.Prime] {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {κ : FractionRing V →+* PadicAlgCl p}

theorem norm_lt_one_of_mem_maximalIdeal
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V)))
    {v : V} (hv : v ∈ maximalIdeal V) : ‖κ (algebraMap V (FractionRing V) v)‖ < 1 := by
  have hle : ‖κ (algebraMap V (FractionRing V) v)‖ ≤ 1 := (hV _).2 ⟨v, rfl⟩
  refine lt_of_le_of_ne hle fun h1 => ?_
  have hv0 : v ≠ 0 := by
    rintro rfl; simp at h1
  have hι : algebraMap V (FractionRing V) v ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hv0
  have hinv : ‖κ (algebraMap V (FractionRing V) v)⁻¹‖ ≤ 1 := by
    rw [map_inv₀, norm_inv, h1, inv_one]
  obtain ⟨w, hw⟩ := (hV _).1 hinv
  have hvw : v * w = 1 := by
    apply IsFractionRing.injective V (FractionRing V)
    rw [map_mul, hw, map_one, mul_inv_cancel₀ hι]
  exact (mem_maximalIdeal _).1 hv ⟨⟨v, w, hvw, by rw [mul_comm]; exact hvw⟩, rfl⟩

theorem norm_natCast_p : ‖((p : ℕ) : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  have : ((p : ℕ) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]) := by
    rw [map_natCast]
  rw [this, PadicAlgCl.norm_extends, Padic.norm_p]

theorem p_mem_maximalIdeal
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) :
    ((p : ℕ) : V) ∈ maximalIdeal V := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, hu⟩
  have h1 : ‖κ (algebraMap V (FractionRing V) (u⁻¹ : Vˣ))‖ ≤ 1 := (hV _).2 ⟨_, rfl⟩
  have h2 : κ (algebraMap V (FractionRing V) ((p : ℕ) : V)) *
      κ (algebraMap V (FractionRing V) (u⁻¹ : Vˣ)) = 1 := by
    rw [← map_mul, ← map_mul, ← hu, Units.mul_inv, map_one, map_one]
  have h3 := congrArg norm h2
  rw [norm_mul, norm_one, map_natCast, map_natCast, norm_natCast_p] at h3
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have : (p : ℝ)⁻¹ * ‖κ (algebraMap V (FractionRing V) (u⁻¹ : Vˣ))‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) h1) (inv_lt_one_of_one_lt₀ hp)
  linarith

end GlobalTheory.PadicUnitBall

namespace GlobalTheory.PadicUnitBall

variable {p : ℕ} [Fact p.Prime] {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {κ : FractionRing V →+* PadicAlgCl p}

theorem exists_norm_le_pow
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ n : ℕ, ∀ x ∈ maximalIdeal V ^ n,
      ‖κ (algebraMap V (FractionRing V) x)‖ ≤ r ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hmax := hϖ.maximalIdeal_eq
  refine ⟨‖κ (algebraMap V (FractionRing V) ϖ)‖, norm_nonneg _,
    norm_lt_one_of_mem_maximalIdeal hV (by rw [hmax]; exact Ideal.mem_span_singleton_self ϖ),
    fun n x hx => ?_⟩
  rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨w, rfl⟩ := hx
  rw [map_mul, map_mul, norm_mul, map_pow, map_pow, norm_pow]
  have hw : ‖κ (algebraMap V (FractionRing V) w)‖ ≤ 1 := (hV _).2 ⟨w, rfl⟩
  exact mul_le_of_le_one_right (by positivity) hw

theorem smul_top_eq (I : Ideal V) : (I • ⊤ : Submodule V V) = I := by
  rw [smul_eq_mul, Ideal.mul_top]

theorem padicInt_mem_range
    (hc : IsAdicComplete (maximalIdeal V) V)
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) (z : ℤ_[p]) :
    ∃ L : V, κ (algebraMap V (FractionRing V) L) = algebraMap ℚ_[p] (PadicAlgCl p) (z : ℚ_[p]) := by
  set f : ℕ → V := fun n => ((z.appr n : ℕ) : V) with hf
  have hpm := p_mem_maximalIdeal hV
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD (maximalIdeal V) ^ m • (⊤ : Submodule V V)] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_top_eq]
    obtain ⟨c, hc⟩ := PadicInt.dvd_appr_sub_appr z m n hmn
    have hmono : z.appr m ≤ z.appr n := PadicInt.appr_mono z hmn
    have heq : z.appr n = z.appr m + p ^ m * c := by
      generalize p ^ m * c = k at hc; omega
    have : f m - f n = ((p : ℕ) : V) ^ m * (-(c : V)) := by
      simp only [hf, heq]; push_cast; ring
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hpm m)
  obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec hcauchy
  refine ⟨L, ?_⟩
  obtain ⟨r, hr0, hr1, hr⟩ := exists_norm_le_pow hV
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hbound : ∀ n : ℕ, ‖κ (algebraMap V (FractionRing V) L) - algebraMap ℚ_[p] (PadicAlgCl p) (z : ℚ_[p])‖
      ≤ r ^ n + ((p : ℝ)⁻¹) ^ n := by
    intro n
    have h1 : f n - L ∈ maximalIdeal V ^ n := by
      have := hL n
      rwa [SModEq.sub_mem, smul_top_eq] at this
    have h1' := hr n _ h1
    have hfn : κ (algebraMap V (FractionRing V) (f n)) =
        algebraMap ℚ_[p] (PadicAlgCl p) (((z.appr n : ℕ) : ℤ_[p]) : ℚ_[p]) := by
      simp only [hf, map_natCast, PadicInt.coe_natCast]
    have h2 : ‖z - ((z.appr n : ℕ) : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) :=
      (PadicInt.norm_le_pow_iff_mem_span_pow _ n).2 (PadicInt.appr_spec n z)
    rw [zpow_neg, zpow_natCast, ← inv_pow] at h2
    have h2' : ‖algebraMap ℚ_[p] (PadicAlgCl p) (((z.appr n : ℕ) : ℤ_[p]) : ℚ_[p]) -
        algebraMap ℚ_[p] (PadicAlgCl p) (z : ℚ_[p])‖ ≤ ((p : ℝ)⁻¹) ^ n := by
      rw [← map_sub, PadicAlgCl.norm_extends, ← PadicInt.coe_sub, PadicInt.norm_def.symm, norm_sub_rev]
      exact h2
    calc _ = ‖(κ (algebraMap V (FractionRing V) L) - κ (algebraMap V (FractionRing V) (f n))) +
          (κ (algebraMap V (FractionRing V) (f n)) - algebraMap ℚ_[p] (PadicAlgCl p) (z : ℚ_[p]))‖ := by
            congr 1; ring
      _ ≤ _ := norm_add_le _ _
      _ ≤ r ^ n + ((p : ℝ)⁻¹) ^ n := by
        gcongr
        · rw [norm_sub_rev, ← map_sub, ← map_sub]; exact h1'
        · rw [hfn]; exact h2'
  have ht : Filter.Tendsto (fun n : ℕ => r ^ n + ((p : ℝ)⁻¹) ^ n) Filter.atTop (nhds 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp))
    simpa using this
  have h0 := ge_of_tendsto' ht hbound
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

end GlobalTheory.PadicUnitBall

namespace GlobalTheory.PadicUnitBall

theorem padic_mem_range : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V →
    ∀ (κ : FractionRing V →+* PadicAlgCl p),
    (∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) →
    ∀ q : ℚ_[p], algebraMap ℚ_[p] (PadicAlgCl p) q ∈ κ.range := by
  intro p _ V _ _ _ _ hc κ hV q
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖q‖ hp
  have hz : ‖q * (p : ℚ_[p]) ^ k‖ ≤ 1 := by
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
    rw [mul_inv_le_iff₀ (by positivity), one_mul]
    exact hk.le
  obtain ⟨L, hL⟩ := padicInt_mem_range hc hV (⟨q * (p : ℚ_[p]) ^ k, hz⟩ : ℤ_[p])
  have hpne : ((p : ℕ) : PadicAlgCl p) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨algebraMap V (FractionRing V) L * (((p : ℕ) : FractionRing V) ^ k)⁻¹, ?_⟩
  rw [map_mul, hL, map_inv₀, map_pow, map_natCast]
  show algebraMap ℚ_[p] (PadicAlgCl p) (q * (p : ℚ_[p]) ^ k) * _ = _
  simp only [map_mul, map_pow, map_natCast]
  field_simp

end GlobalTheory.PadicUnitBall
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicMemRangeCompleteDvrPadicAlgClStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_mem_range_complete_dvr_padicAlgCl : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (κ : FractionRing V →+* PadicAlgCl p), (∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → ∀ q : ℚ_[p], algebraMap ℚ_[p] (PadicAlgCl p) q ∈ κ.range := by
  first | exact @GlobalTheory.PadicUnitBall.padic_mem_range | exact GlobalTheory.PadicUnitBall.padic_mem_range | (intros; apply GlobalTheory.PadicUnitBall.padic_mem_range <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Glues
open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

namespace GlobalTheory.PinchLift

def Glues {X X' Z Z' : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z) : Prop :=
  ∀ (W : X.Opens) (a : Γ(X', p ⁻¹ᵁ W)) (b : Γ(Z, i ⁻¹ᵁ W)),
    (i'.appLE (p ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_left).hom a =
      (p'.appLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_right).hom b →
    ∃! s : Γ(X, W), (p.app W).hom s = a ∧ (i.app W).hom s = b

end GlobalTheory.PinchLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GoodEtale

def Hart (A R M : Type) [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup M] [Module R M] : Prop :=
  ∀ a : A, a ≠ 0 → ∀ m : M,
    (∀ p : Ideal A, p.IsPrime → p.height ≤ 1 →
      ∃ u : A, u ∉ p ∧ ∃ m' : M, algebraMap A R u • m = algebraMap A R a • m') →
    ∃ m' : M, m = algebraMap A R a • m'

def TorsionFreeOver (A R M : Type) [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup M]
    [Module R M] : Prop :=
  ∀ a : A, a ≠ 0 → ∀ m : M, algebraMap A R a • m = 0 → m = 0

def EtaleLow (A R C : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C] : Prop :=
  ∀ (P : Ideal R) [P.IsPrime], (P.comap (algebraMap A R)).height ≤ 1 →
    Algebra.Etale (Localization.AtPrime P) (Localization.AtPrime P ⊗[R] C)

end GlobalTheory.GoodEtale
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMemFinDimSubspace
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DualMemSpanEvalOfFiniteDimensional
theorem UpperTheory.Reformulated.B.Yyc2.dual_mem_span_eval_of_finiteDimensional :
    ∀ {Y : Type} (E : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ ↥E] (φ : Module.Dual ℂ ↥E),
      φ ∈ Submodule.span ℂ (Set.range fun (y : Y) ↦ LinearMap.proj y ∘ₗ E.subtype) := by
  intro Y E _ φ
  apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
  intro x hx
  have h0 : x = 0 := by
    apply Subtype.ext
    funext y
    exact (Submodule.mem_iInf _).1 hx y
  rw [h0]
  exact Submodule.zero_mem _
end

open MeasureTheory Filter Topology

namespace GlobalTheory

theorem dual_mem_span_eval_of_finiteDimensional {Y : Type} (E : Submodule ℂ (Y → ℂ))
    [FiniteDimensional ℂ E] (φ : Module.Dual ℂ E) :
    φ ∈ Submodule.span ℂ
      (Set.range fun y : Y => (LinearMap.proj y : (Y → ℂ) →ₗ[ℂ] ℂ).comp E.subtype) :=
  _root_.UpperTheory.Reformulated.B.Yyc2.dual_mem_span_eval_of_finiteDimensional E φ

end GlobalTheory
end
