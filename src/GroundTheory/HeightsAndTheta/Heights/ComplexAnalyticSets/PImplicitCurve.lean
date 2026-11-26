module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.OsgoodSeparate
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicJacobianNeZero
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreRFlatAscent

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PImplicitCurve
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Topology Metric

noncomputable section

namespace ImplicitCurve

theorem analyticOnNhd_of_differentiableOn {m p : ℕ} {U : Set (Fin m → ℂ)}
    {Φ : (Fin m → ℂ) → Fin p → ℂ} (hU : IsOpen U) (hΦ : DifferentiableOn ℂ Φ U) :
    AnalyticOnNhd ℂ Φ U := by
  refine analyticOnNhd_pi_iff.2 fun j => ?_
  have hj : DifferentiableOn ℂ (fun t => Φ t j) U := differentiableOn_pi.1 hΦ j
  refine IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn
    fun w hw i => ?_
  have hw : DifferentiableAt ℂ (fun t => Φ t j) (Function.update w i (w i)) := by
    rw [Function.update_eq_self]; exact (hj w hw).differentiableAt (hU.mem_nhds hw)
  exact hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt

theorem proof : ImplicitCurve.Statement := by
  intro n k γ R L s hγ hs hbij
  set F : (Fin (k + 1) → ℂ) → Fin (k + 1) → ℂ := fun t => vecCons (t 0) (L *ᵥ γ t) with hF
  have hFd : DifferentiableOn ℂ F (ball 0 R) := by
    refine differentiableOn_pi.2 fun i => Fin.cases ?_ (fun j => ?_) i
    · simpa [hF] using (differentiableOn_pi.1 (differentiableOn_id (s := ball (0 : Fin (k + 1) → ℂ) R)) 0)
    · simp only [hF, cons_val_succ, mulVec, dotProduct]
      exact DifferentiableOn.fun_sum fun l _ => (differentiableOn_pi.1 hγ l).const_mul _
  have hFa := analyticOnNhd_of_differentiableOn isOpen_ball hFd
  set e := (LinearEquiv.ofBijective
    (fderiv ℂ F s : (Fin (k + 1) → ℂ) →ₗ[ℂ] Fin (k + 1) → ℂ) hbij).toContinuousLinearEquiv
  have he : (e : (Fin (k + 1) → ℂ) →L[ℂ] Fin (k + 1) → ℂ) = fderiv ℂ F s := by ext1 x; rfl
  have hst : HasStrictFDerivAt F (e : (Fin (k + 1) → ℂ) →L[ℂ] Fin (k + 1) → ℂ) s := by
    rw [he]; exact (hFa s hs).hasStrictFDerivAt
  have hV : ∀ᶠ t in 𝓝 s, (t ∈ ball (0 : Fin (k + 1) → ℂ) R ∧ fderiv ℂ F t ∈
      Set.range ((↑) : ((Fin (k + 1) → ℂ) ≃L[ℂ] (Fin (k + 1) → ℂ)) → _)) ∧
      t ∈ (hst.toOpenPartialHomeomorph F).source :=
    (Filter.Eventually.and (isOpen_ball.mem_nhds hs) ((hFa s hs).fderiv.continuousAt.preimage_mem_nhds
      (ContinuousLinearEquiv.isOpen.mem_nhds ⟨e, he⟩))).and
      ((hst.toOpenPartialHomeomorph F).open_source.mem_nhds hst.mem_toOpenPartialHomeomorph_source)
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV
  set Ψ := (hst.toOpenPartialHomeomorph F).restrOpen (ball s ε) isOpen_ball
  have hΨs : Ψ.source = (hst.toOpenPartialHomeomorph F).source ∩ ball s ε :=
    OpenPartialHomeomorph.restrOpen_source _ _ _
  have hsΨ : s ∈ Ψ.source := hΨs ▸ ⟨hst.mem_toOpenPartialHomeomorph_source, mem_ball_self hε⟩
  have hsrc : ∀ t ∈ Ψ.source, t ∈ ball 0 R ∧
      ∃ e' : (Fin (k + 1) → ℂ) ≃L[ℂ] (Fin (k + 1) → ℂ), HasFDerivAt Ψ (e' : _ →L[ℂ] _) t := by
    intro t ht
    obtain ⟨⟨htR, e', he'⟩, -⟩ := hεV (hΨs ▸ ht).2
    refine ⟨htR, e', ?_⟩
    rw [he']; exact (hFa t htR).differentiableAt.hasFDerivAt
  obtain ⟨r, hr, hrT⟩ := Metric.isOpen_iff.1 Ψ.open_target (F s) (Ψ.map_source hsΨ)
  set p : (Fin 1 → ℂ) → Fin (k + 1) → ℂ := fun τ => vecCons (s 0 + τ 0) (L *ᵥ γ s) with hp
  have hpT : ∀ τ ∈ ball (0 : Fin 1 → ℂ) r, p τ ∈ Ψ.target := by
    intro τ hτ
    refine hrT ((dist_pi_lt_iff hr).2 fun i => Fin.cases ?_ (fun j => ?_) i)
    · simpa [hp, hF, dist_eq_norm] using (norm_le_pi_norm τ 0).trans_lt (mem_ball_zero_iff.1 hτ)
    · simpa [hp, hF] using hr
  refine ⟨r, hr, fun τ => Ψ.symm (p τ), fun τ hτ => ?_, ?_, fun τ hτ => ?_, ?_⟩
  · have hpd : Differentiable ℂ p := differentiable_pi.2 fun i => Fin.cases
      (by simpa [hp] using (differentiable_const (s 0)).add (differentiable_pi.1 differentiable_id 0))
      (fun j => by simp [hp]) i
    obtain ⟨-, e', he'⟩ := hsrc _ (Ψ.map_target (hpT τ hτ))
    exact ((Ψ.hasFDerivAt_symm (hpT τ hτ) he').differentiableAt.comp τ
      (hpd τ)).differentiableWithinAt
  · have h0 : p 0 = F s := by simp [hp, hF]
    show Ψ.symm (p 0) = s
    rw [h0]; exact Ψ.left_inv hsΨ
  · have h2 : F (Ψ.symm (p τ)) = p τ := Ψ.right_inv (hpT τ hτ)
    refine ⟨(hsrc _ (Ψ.map_target (hpT τ hτ))).1, ?_, ?_⟩
    · simpa [hF, hp] using congrFun h2 0
    · simpa [hF, hp] using congrArg Fin.tail h2
  · refine ⟨Ψ.source ∩ {t | ‖t 0 - s 0‖ < r}, Filter.inter_mem (Ψ.open_source.mem_nhds hsΨ)
      ((isOpen_lt ((continuous_apply 0).sub continuous_const).norm continuous_const).mem_nhds
        (by simpa using hr)), ?_⟩
    rintro t ⟨ht, htr⟩ hL
    refine ⟨fun _ => t 0 - s 0, by simpa [pi_norm_const] using htr, ?_⟩
    have hpt : p (fun _ => t 0 - s 0) = F t := by simp [hp, hF, hL]
    dsimp only
    rw [hpt]; exact Ψ.left_inv ht

end ImplicitCurve

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalLocalDepthTwo
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing RingTheory.Sequence

theorem NormalLocalDepthTwo.mem_span_of_maximalIdeal_mul_le {B : Type*} [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [IsDomain B] [IsIntegrallyClosed B] (hm : ¬ (maximalIdeal B).IsPrincipal)
    {x y : B} (hx : x ≠ 0) (hy : ∀ a ∈ maximalIdeal B, ∃ b, a * y = x * b) : ∃ c, y = x * c := by
  let K := FractionRing B
  by_cases h : ∀ a ∈ maximalIdeal B, ∀ b, a * y = x * b → b ∈ maximalIdeal B
  ·
    set u : K := algebraMap B K y / algebraMap B K x with hu
    have hxK : algebraMap B K x ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective B K)).mpr hx
    let N : Submodule B K := Submodule.map (Algebra.linearMap B K) (maximalIdeal B)
    have hmbot : maximalIdeal B ≠ ⊥ := fun h0 => hm (h0 ▸ ⟨⟨0, by simp⟩⟩)
    have hN : N ≠ ⊥ := by
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmbot
      intro hN0
      have : algebraMap B K a ∈ N := Submodule.mem_map_of_mem ha
      rw [hN0, Submodule.mem_bot] at this
      exact ha0 ((map_eq_zero_iff _ (IsFractionRing.injective B K)).mp this)
    have hNfg : N.FG := (IsNoetherian.noetherian (maximalIdeal B)).map _
    have hstab : ∀ n ∈ N, u • n ∈ N := by
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨b, hb⟩ := hy a ha
      refine ⟨b, h a ha b hb, ?_⟩
      change algebraMap B K b = u * algebraMap B K a
      rw [hu, div_mul_eq_mul_div, eq_div_iff hxK, ← map_mul, ← map_mul]
      congr 1
      linear_combination -hb
    obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp
      (isIntegral_of_smul_mem_submodule N hN hNfg u hstab)
    refine ⟨c, IsFractionRing.injective B K ?_⟩
    rw [map_mul, hc, hu]
    exact (mul_div_cancel₀ _ hxK).symm
  ·
    push Not at h
    obtain ⟨a, ha, b, hab, hb⟩ := h
    have hbu : IsUnit b := by
      by_contra hb'
      exact hb ((mem_maximalIdeal b).mpr hb')
    by_cases hy0 : y = 0
    · exact ⟨0, by simp [hy0]⟩
    exfalso
    apply hm
    refine ⟨⟨a, le_antisymm ?_ ?_⟩⟩
    · intro a' ha'
      obtain ⟨b', hb'⟩ := hy a' ha'
      have hab' : a' * b = a * b' := mul_right_cancel₀ hy0 (by linear_combination b * hb' - b' * hab)
      refine Submodule.mem_span_singleton.mpr ⟨b' * ↑hbu.unit⁻¹, ?_⟩
      rw [smul_eq_mul, show b' * ↑hbu.unit⁻¹ * a = (a * b') * ↑hbu.unit⁻¹ by ring, ← hab', mul_assoc,
        hbu.mul_val_inv, mul_one]
    · rw [Ideal.submodule_span_eq, Ideal.span_le, Set.singleton_subset_iff]
      exact ha

theorem NormalLocalDepthTwo.proof : NormalLocalDepthTwo.Statement := by
  intro B _ _ _ _ _
  by_cases hfield : IsField B
  · refine ⟨[], by simp, IsWeaklyRegular.nil B B, ?_⟩
    rw [ringKrullDim_eq_zero_of_isField hfield]
    simp
  have hmbot : maximalIdeal B ≠ ⊥ := isField_iff_maximalIdeal_eq.not.mp hfield
  obtain ⟨x, hxm, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmbot
  have hxreg : IsSMulRegular B x := fun a b h => mul_left_cancel₀ hx0 h
  by_cases hp : (maximalIdeal B).IsPrincipal
  ·
    have : IsDiscreteValuationRing B := ((IsDiscreteValuationRing.TFAE B hfield).out 5 1).mp hp
    refine ⟨[x], by simpa using hxm,
      (isWeaklyRegular_cons_iff _ _ _).mpr ⟨hxreg, IsWeaklyRegular.nil _ _⟩, ?_⟩
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one]
    simp

  have hreg : ∃ y ∈ maximalIdeal B, IsSMulRegular (QuotSMulTop x B) y := by
    by_contra hcon
    push Not at hcon
    have hsub : ((maximalIdeal B : Ideal B) : Set B) ⊆
        ⋃ p ∈ associatedPrimes B (QuotSMulTop x B), (p : Set B) := by
      rw [biUnion_associatedPrimes_eq_zero_divisors]
      intro y hy
      have h1 := hcon y hy
      rw [isSMulRegular_iff_right_eq_zero_of_smul] at h1
      push Not at h1
      obtain ⟨z, hz, hz0⟩ := h1
      exact ⟨z, hz0, hz⟩
    have hmem := (Ideal.subset_iUnion_iff_mem_of_isMaximal_of_finite
      (associatedPrimes.finite B (QuotSMulTop x B)) ⊥ ⊥
      (fun I hI _ _ => IsAssociatedPrime.isPrime hI) bot_ne_top bot_ne_top).mp hsub
    obtain ⟨-, z, hz⟩ := isAssociatedPrime_iff.mp hmem
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hyx : ∀ a ∈ maximalIdeal B, ∃ b, a * y = x * b := by
      intro a ha
      rw [hz, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at ha
      obtain ⟨b, -, hb⟩ := ha
      exact ⟨b, by simpa [smul_eq_mul] using hb.symm⟩
    obtain ⟨c, hc⟩ := NormalLocalDepthTwo.mem_span_of_maximalIdeal_mul_le hp hx0 hyx
    have h1 : (1 : B) ∈ maximalIdeal B := by
      rw [hz, Submodule.mem_colon_singleton, one_smul, Submodule.mem_bot,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨c, trivial, by rw [hc, smul_eq_mul]⟩
    exact (maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  obtain ⟨y, hym, hy⟩ := hreg
  refine ⟨[x, y], ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption
  · exact (isWeaklyRegular_cons_iff _ _ _).mpr
      ⟨hxreg, (isWeaklyRegular_cons_iff _ _ _).mpr ⟨hy, IsWeaklyRegular.nil _ _⟩⟩
  · exact (min_le_left _ _).trans (by simp)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParametrisationSheetsConnected
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter MeasureTheory

theorem exists_clm_ne_zero_of_countable {σ : Type} [Fintype σ] {T : Set (σ → ℂ)} (hT : T.Countable)
    (h0 : (0 : σ → ℂ) ∉ T) : ∃ ℓ : (σ → ℂ) →L[ℂ] ℂ, ∀ u ∈ T, ℓ u ≠ 0 := by
  classical
  let φ : (σ → ℂ) → ((σ → ℂ) →ₗ[ℝ] ℂ) := fun u =>
    { toFun := fun v => ∑ i, v i * u i
      map_add' := fun a b => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c a => by simp [Finset.mul_sum, mul_assoc] }
  have hφ : ∀ u v, φ u v = ∑ i, v i * u i := fun _ _ => rfl
  have hker : ∀ u ∈ T, volume (LinearMap.ker (φ u) : Set (σ → ℂ)) = 0 := by
    intro u hu
    refine Measure.addHaar_submodule volume _ fun htop => ?_
    obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra h
      push Not at h
      exact h0 (by rwa [show u = 0 from funext h] at hu)
    have hm : Pi.single i 1 ∈ LinearMap.ker (φ u) := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hφ] at hm
    simp [Pi.single_apply] at hm
    exact hi hm
  have hnull : volume (⋃ u ∈ T, (LinearMap.ker (φ u) : Set (σ → ℂ))) = 0 :=
    (measure_biUnion_null_iff hT).2 hker
  obtain ⟨v, hv⟩ : ∃ v, v ∉ ⋃ u ∈ T, (LinearMap.ker (φ u) : Set (σ → ℂ)) := by
    by_contra h
    push Not at h
    have hu : (Set.univ : Set (σ → ℂ)) ⊆ ⋃ u ∈ T, (LinearMap.ker (φ u) : Set (σ → ℂ)) := fun x _ => h x
    have hpos := isOpen_univ.measure_pos (volume : Measure (σ → ℂ)) Set.univ_nonempty
    exact hpos.ne' (measure_mono_null hu hnull)
  refine ⟨∑ i, v i • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i, fun u hu => ?_⟩
  have hvu : φ u v ≠ 0 := fun h => hv (Set.mem_biUnion hu (LinearMap.mem_ker.2 h))
  rw [hφ] at hvu
  simpa [ContinuousLinearMap.sum_apply] using hvu

theorem ParametrisationSheetsConnected.proof (h₁ : SheetPieceProductAnalytic.Statement)
    (h₂ : SheetPieceReachesCentre.Statement) : ParametrisationSheetsConnected.Statement := by
  classical
  intro σ _ X w B d A D δ N hP hirr
  obtain ⟨hB, hwXB, hD, -, hmaps, -, -, -, -, hcard, -, hdense⟩ := id hP
  set S := {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} with hS
  by_contra hnc
  rw [IsPreconnected] at hnc
  push Not at hnc
  obtain ⟨u, v, hu, hv, hSuv, hSu, hSv, hdisj⟩ := hnc
  have hdisj' : S ∩ (v ∩ u) = ∅ := by rwa [Set.inter_comm v u]
  have hSvu : S ⊆ v ∪ u := by rwa [Set.union_comm]
  have hwu := h₂ σ X w B d A D δ N u v hP hu hv hSuv hdisj hSu
  have hwv := h₂ σ X w B d A D δ N v u hP hv hu hSvu hdisj' hSv
  obtain ⟨p, hpS, hpw⟩ := mem_closure_iff_seq_limit.1 hwu
  obtain ⟨q, hqS, hqw⟩ := mem_closure_iff_seq_limit.1 hwv

  have hfin : ∀ (U' : Set (σ → ℂ)), ∀ x ∈ S, {x' | x' ∈ X ∩ B ∧ x' ∈ U' ∧ A x' = A x}.Finite :=
    fun U' x hx => (Set.finite_of_encard_eq_coe (hcard (A x) (hmaps hx.1) hx.2)).subset
      fun x' hx' => ⟨hx'.1, hx'.2.2⟩
  set T : Set (σ → ℂ) :=
    (⋃ n, (fun x' => p n - x') '' {x' | x' ∈ X ∩ B ∧ x' ∈ v ∧ A x' = A (p n)}) ∪
      ⋃ n, (fun x' => q n - x') '' {x' | x' ∈ X ∩ B ∧ x' ∈ u ∧ A x' = A (q n)} with hT
  have hTc : T.Countable :=
    (Set.countable_iUnion fun n => ((hfin v (p n) (hpS n).1).image _).countable).union
      (Set.countable_iUnion fun n => ((hfin u (q n) (hqS n).1).image _).countable)
  have hT0 : (0 : σ → ℂ) ∉ T := by
    have key : ∀ (r : σ → ℂ) (U₁ U₂ : Set (σ → ℂ)), r ∈ S ∩ U₁ → S ∩ (U₁ ∩ U₂) = ∅ →
        ∀ x' ∈ {x' | x' ∈ X ∩ B ∧ x' ∈ U₂ ∧ A x' = A r}, r - x' ≠ 0 := by
      intro r U₁ U₂ hr hd x' hx' h0
      have hrx : r = x' := sub_eq_zero.1 h0
      have hx'S : x' ∈ S := ⟨hx'.1, by rw [hx'.2.2]; exact hr.1.2⟩
      exact (Set.eq_empty_iff_forall_notMem.1 hd x') ⟨hx'S, hrx ▸ hr.2, hx'.2.1⟩
    rintro (h | h) <;> obtain ⟨n, x', hx', hx0⟩ := Set.mem_iUnion.1 h
    · exact key (p n) u v (hpS n) hdisj x' hx' hx0
    · exact key (q n) v u (hqS n) hdisj' x' hx' hx0
  obtain ⟨ℓ, hℓ⟩ := exists_clm_ne_zero_of_countable hTc hT0
  obtain ⟨f, hfan, hfeq⟩ := h₁ σ X w B d A D δ N u v ℓ hP hu hv hSuv hdisj
  obtain ⟨g, hgan, hgeq⟩ := h₁ σ X w B d A D δ N v u ℓ hP hv hu hSvu hdisj'

  have hzero : ∀ (U' : Set (σ → ℂ)) (F : (σ → ℂ) → ℂ),
      (∀ z, A z ∈ D → δ (A z) ≠ 0 →
        F z = ∏ᶠ x ∈ {x | x ∈ X ∩ B ∧ x ∈ U' ∧ A x = A z}, (ℓ z - ℓ x)) →
      ∀ x ∈ S, x ∈ U' → F x = 0 := by
    intro U' F hF x hx hxU
    rw [hF x (hmaps hx.1) hx.2, finprod_mem_eq_finite_toFinset_prod _ (hfin U' x hx)]
    exact Finset.prod_eq_zero ((hfin U' x hx).mem_toFinset.2 ⟨hx.1, hxU, rfl⟩) (sub_self _)

  have hne : ∀ (U' : Set (σ → ℂ)) (F : (σ → ℂ) → ℂ) (r : σ → ℂ),
      (∀ z, A z ∈ D → δ (A z) ≠ 0 →
        F z = ∏ᶠ x ∈ {x | x ∈ X ∩ B ∧ x ∈ U' ∧ A x = A z}, (ℓ z - ℓ x)) → r ∈ S →
      (∀ x' ∈ {x' | x' ∈ X ∩ B ∧ x' ∈ U' ∧ A x' = A r}, r - x' ∈ T) → F r ≠ 0 := by
    intro U' F r hF hr hrT
    rw [hF r (hmaps hr.1) hr.2, finprod_mem_eq_finite_toFinset_prod _ (hfin U' r hr)]
    refine Finset.prod_ne_zero_iff.2 fun x' hx' => ?_
    rw [← map_sub]
    exact hℓ _ (hrT x' ((hfin U' r hr).mem_toFinset.1 hx'))
  have hfq : ∀ n, f (q n) ≠ 0 := fun n => hne u f (q n) hfeq (hqS n).1
    fun x' hx' => Or.inr (Set.mem_iUnion.2 ⟨n, x', hx', rfl⟩)
  have hgp : ∀ n, g (p n) ≠ 0 := fun n => hne v g (p n) hgeq (hpS n).1
    fun x' hx' => Or.inl (Set.mem_iUnion.2 ⟨n, x', hx', rfl⟩)

  have hprod : ∀ z ∈ X ∩ B, f z * g z = 0 := by
    intro z hz
    have hc : ContinuousAt (fun z => f z * g z) z :=
      (hfan z (hmaps hz)).continuousAt.mul (hgan z (hmaps hz)).continuousAt
    have := mem_closure_iff_nhdsWithin_neBot.1 (hdense hz)
    have h2 : (fun z => f z * g z) =ᶠ[𝓝[S] z] fun _ => 0 :=
      eventually_nhdsWithin_of_forall fun x hx => by
        rcases hSuv hx with hxu | hxv
        · simp [hzero u f hfeq x hx hxu]
        · simp [hzero v g hgeq x hx hxv]
    exact tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' h2.symm)
  have hw : A w ∈ D := hmaps hwXB
  have hev : ∀ᶠ z in 𝓝 w, z ∈ X → f z * g z = 0 := by
    filter_upwards [hB.mem_nhds hwXB.2] with z hzB hzX using hprod z ⟨hzX, hzB⟩
  rcases hirr.2 f g (hfan w hw) (hgan w hw) hev with hf0 | hg0
  · obtain ⟨n, hn⟩ := (hqw.eventually hf0).exists
    exact hfq n (hn (hqS n).1.1.1)
  · obtain ⟨n, hn⟩ := (hpw.eventually hg0).exists
    exact hgp n (hn (hpS n).1.1.1)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.HolomorphicZerosNotIsolated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric

theorem analyticAt_det_fderiv {k : ℕ} {f : (Fin k → ℂ) → Fin k → ℂ} {x : Fin k → ℂ}
    (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℂ (fun z => LinearMap.det (fderiv ℂ f z : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)) x := by
  have hd : AnalyticAt ℂ (fderiv ℂ f) x := hf.fderiv
  have he : ∀ i j : Fin k, AnalyticAt ℂ (fun z => fderiv ℂ f z (Pi.single j 1) i) x := by
    intro i j
    let L : ((Fin k → ℂ) →L[ℂ] Fin k → ℂ) →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i).comp
        (ContinuousLinearMap.apply ℂ (Fin k → ℂ) (Pi.single j 1))
    show AnalyticAt ℂ (L ∘ fderiv ℂ f) x
    exact (L.analyticAt _).comp hd
  have heq : (fun z => LinearMap.det (fderiv ℂ f z : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)) =
      fun z => ∑ σ : Equiv.Perm (Fin k),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, fderiv ℂ f z (Pi.single i 1) (σ i) := by
    funext z
    rw [← LinearMap.det_toMatrix', Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    rfl
  rw [heq]
  exact Finset.analyticAt_fun_sum _ fun σ _ =>
    analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => he (σ i) i)

theorem exists_zero_ne_near {k : ℕ} (hk : 2 ≤ k) {J : (Fin k → ℂ) → ℂ} {c : Fin k → ℂ}
    (hJ : AnalyticAt ℂ J c) (hc : J c = 0) {W : Set (Fin k → ℂ)} (hW : W ∈ 𝓝 c) :
    ∃ z ∈ W, z ≠ c ∧ J z = 0 := by
  have : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  by_cases h0 : ∀ᶠ y in 𝓝 c, J y = 0
  · have h1 : ∀ᶠ y in 𝓝[≠] c, y ∈ W ∧ J y = 0 := nhdsWithin_le_nhds (Filter.inter_mem hW h0)
    obtain ⟨y, ⟨hyW, hy0⟩, hyc⟩ := (h1.and self_mem_nhdsWithin).exists
    exact ⟨y, hyW, hyc, hy0⟩
  obtain ⟨v, hv⟩ := exists_line_eventually_ne_zero hJ h0
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨t, ht⟩ := hv.exists
    simp [hc] at ht

  obtain ⟨u, -, hu⟩ : ∃ u ∈ (⊤ : Submodule ℂ (Fin k → ℂ)), u ∉ ℂ ∙ v := by
    refine SetLike.exists_of_lt (lt_top_iff_ne_top.2 fun htop => ?_)
    have h1 := finrank_span_singleton (K := ℂ) hv0
    rw [htop, finrank_top, Module.finrank_fin_fun] at h1
    omega
  obtain ⟨R, hR, han⟩ := hJ.exists_ball_analyticOnNhd
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.1 hW
  set ρ := min R ε with hρ
  have hρ0 : 0 < ρ := lt_min hR hε
  obtain ⟨δ, hδ, hδv⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hv)
  set r := min (δ / 2) (ρ / (2 * (‖v‖ + 1))) with hr
  have hr0 : 0 < r := lt_min (by positivity) (by positivity)
  have hrδ : r < δ := (min_le_left _ _).trans_lt (by linarith)
  have hrv : r * ‖v‖ < ρ / 2 := by
    have h1 : r ≤ ρ / (2 * (‖v‖ + 1)) := min_le_right _ _
    have h2 : r * ‖v‖ ≤ ρ / (2 * (‖v‖ + 1)) * ‖v‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have h3 : ρ / (2 * (‖v‖ + 1)) * ‖v‖ < ρ / 2 := by
      rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [norm_nonneg v]
    linarith

  have hmem : ∀ s t : ℂ, ‖s • u‖ < ρ / 2 → ‖t‖ ≤ r → c + s • u + t • v ∈ ball c ρ := by
    intro s t hs ht
    rw [mem_ball, dist_eq_norm, add_assoc, add_sub_cancel_left]
    calc ‖s • u + t • v‖ ≤ ‖s • u‖ + ‖t‖ * ‖v‖ := (norm_add_le _ _).trans (le_of_eq (by rw [norm_smul t v]))
      _ < ρ / 2 + ρ / 2 := add_lt_add_of_lt_of_le hs (by nlinarith [norm_nonneg v])
      _ = ρ := by ring
  have hballR : ball c ρ ⊆ ball c R := ball_subset_ball (min_le_left _ _)

  have hK : IsCompact (sphere (0 : ℂ) r) := isCompact_sphere 0 r
  have hKne : (sphere (0 : ℂ) r).Nonempty := NormedSpace.sphere_nonempty.2 hr0.le
  have hcontJ : ∀ p ∈ ball c ρ, ContinuousAt J p := fun p hp => (han p (hballR hp)).continuousAt
  have hF0 : ∀ t ∈ sphere (0 : ℂ) r, J (c + t • v) ≠ 0 := by
    intro t ht
    have htn : ‖t‖ = r := by simpa using ht
    refine hδv (by simpa [dist_eq_norm, htn] using hrδ) (by rintro rfl; simp at htn; linarith)
  have hline : ∀ t : ℂ, ‖t‖ ≤ r → c + t • v ∈ ball c ρ := by
    intro t ht
    have h1 := hmem 0 t (by rw [zero_smul, norm_zero]; exact half_pos hρ0) ht
    rwa [zero_smul, add_zero] at h1
  have hcontK : ContinuousOn (fun t : ℂ => ‖J (c + t • v)‖) (sphere 0 r) := by
    intro t ht
    have hp := hline t (mem_sphere_zero_iff_norm.1 ht).le
    exact (ContinuousAt.comp (f := fun t : ℂ => c + t • v) (hcontJ _ hp) (by fun_prop)).norm.continuousWithinAt
  obtain ⟨t0, ht0K, ht0min⟩ := hK.exists_isMinOn hKne hcontK
  set m := ‖J (c + t0 • v)‖ with hm
  have hm0 : 0 < m := norm_pos_iff.2 (hF0 t0 ht0K)

  have hcirc : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ t ∈ sphere (0 : ℂ) r, m / 2 < ‖J (c + s • u + t • v)‖ := by
    refine hK.eventually_forall_of_forall_eventually fun t ht => ?_
    have htr : ‖t‖ ≤ r := (mem_sphere_zero_iff_norm.1 ht).le
    have hcont : ContinuousAt (fun p : ℂ × ℂ => J (c + p.1 • u + p.2 • v)) (0, t) := by
      refine ContinuousAt.comp (f := fun p : ℂ × ℂ => c + p.1 • u + p.2 • v) ?_ (by fun_prop)
      exact hcontJ _ (hmem 0 t (by simpa using half_pos hρ0) htr)
    have hle : ‖J (c + t0 • v)‖ ≤ ‖J (c + t • v)‖ := isMinOn_iff.1 ht0min t ht
    exact hcont.norm.eventually (lt_mem_nhds (by simp only [zero_smul, add_zero]; linarith))
  have hcen : ∀ᶠ s in 𝓝 (0 : ℂ), ‖J (c + s • u)‖ < m / 2 := by
    have hcont : ContinuousAt (fun s : ℂ => J (c + s • u)) 0 :=
      ContinuousAt.comp (f := fun s : ℂ => c + s • u) (by simpa using hcontJ c (mem_ball_self hρ0))
        (by fun_prop)
    have h1 : ‖J (c + (0 : ℂ) • u)‖ < m / 2 := by simpa [hc] using half_pos hm0
    exact hcont.norm.eventually (gt_mem_nhds h1)
  have hsmall : ∀ᶠ s in 𝓝 (0 : ℂ), ‖s • u‖ < ρ / 2 := by
    have hcont : ContinuousAt (fun s : ℂ => ‖s • u‖) 0 := by fun_prop
    exact hcont.eventually (gt_mem_nhds (by simpa using half_pos hρ0))
  obtain ⟨s, ⟨⟨hs1, hs2⟩, hs3⟩, hs0⟩ :=
    ((((hcirc.and hcen).and hsmall).filter_mono (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))).and
      (self_mem_nhdsWithin (s := {(0 : ℂ)}ᶜ))).exists

  obtain ⟨t, ht, htz⟩ : ∃ t ∈ closedBall (0 : ℂ) r, J (c + s • u + t • v) = 0 := by
    by_contra hne
    simp only [not_exists, not_and] at hne
    have hdiff : DifferentiableOn ℂ (fun t : ℂ => (J (c + s • u + t • v))⁻¹) (closedBall 0 r) := by
      intro t ht
      have htr : ‖t‖ ≤ r := by simpa using ht
      have hp := hmem s t hs3 htr
      have hJd : DifferentiableAt ℂ J (c + s • u + t • v) := (han _ (hballR hp)).differentiableAt
      have hcomp : DifferentiableAt ℂ (fun t : ℂ => J (c + s • u + t • v)) t :=
        hJd.comp t (by fun_prop : DifferentiableAt ℂ (fun t : ℂ => c + s • u + t • v) t)
      exact (hcomp.inv (hne t ht)).differentiableWithinAt
    have hdc : DiffContOnCl ℂ (fun t : ℂ => (J (c + s • u + t • v))⁻¹) (ball 0 r) :=
      hdiff.diffContOnCl_ball subset_rfl
    have hbd := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc (C := (m / 2)⁻¹)
      (fun t ht => by
        rw [frontier_ball 0 hr0.ne'] at ht
        rw [norm_inv]
        exact inv_anti₀ (half_pos hm0) (hs1 t ht).le)
      (subset_closure (mem_ball_self hr0))
    have hJs : J (c + s • u) ≠ 0 := by simpa using hne 0 (mem_closedBall_self hr0.le)
    simp only [zero_smul, add_zero, norm_inv] at hbd
    have := inv_lt_inv₀ (half_pos hm0) (norm_pos_iff.2 hJs) |>.2 hs2
    linarith
  refine ⟨c + s • u + t • v, hεW ?_, ?_, htz⟩
  · exact ball_subset_ball (min_le_right R ε) (hmem s t hs3 (by simpa using ht))
  · intro heq
    apply hu
    have h1 : s • u = -(t • v) := by
      have : s • u + t • v = 0 := by
        have := congrArg (· - c) heq
        simpa [add_assoc] using this
      exact eq_neg_of_add_eq_zero_left this
    have hs : s ≠ 0 := by simpa using hs0
    rw [Submodule.mem_span_singleton]
    refine ⟨-(s⁻¹ * t), ?_⟩
    calc -(s⁻¹ * t) • v = s⁻¹ • (-(t • v)) := by rw [smul_neg, smul_smul, neg_smul]
      _ = s⁻¹ • (s • u) := by rw [h1]
      _ = u := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProperHolomorphicSurjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric MeasureTheory
open scoped ENNReal NNReal

namespace ProperHolomorphicSurjective

theorem analyticOnNhd_of_differentiableOn {k m : ℕ} {U : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → Fin m → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by
  refine analyticOnNhd_pi_iff.2 fun j => ?_
  have hj : DifferentiableOn ℂ (fun t => f t j) U := differentiableOn_pi.1 hf j
  refine analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn fun w hw i => ?_
  have hw : DifferentiableAt ℂ (fun t => f t j) (Function.update w i (w i)) := by
    rw [Function.update_eq_self]
    exact (hj w hw).differentiableAt (hU.mem_nhds hw)
  exact hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt

noncomputable def jac {k : ℕ} (g : (Fin k → ℂ) → Fin k → ℂ) (v : Fin k → ℂ) : ℂ :=
  LinearMap.det (fderiv ℂ g v : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)

theorem jac_ne_zero_iff {k : ℕ} (g : (Fin k → ℂ) → Fin k → ℂ) (v : Fin k → ℂ) :
    jac g v ≠ 0 ↔ Function.Injective (fderiv ℂ g v) := by
  rw [jac, ← isUnit_iff_ne_zero, ← LinearMap.isUnit_iff_isUnit_det, Module.End.isUnit_iff]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, LinearMap.injective_iff_surjective.1 h⟩

theorem differentiableOn_jac {k : ℕ} {Ω : Set (Fin k → ℂ)} {g : (Fin k → ℂ) → Fin k → ℂ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) : DifferentiableOn ℂ (jac g) Ω := by
  have hfd : DifferentiableOn ℂ (fderiv ℂ g) Ω :=
    (analyticOnNhd_of_differentiableOn hΩ hg).fderiv.differentiableOn
  have hentry : ∀ i j : Fin k,
      DifferentiableOn ℂ (fun v => fderiv ℂ g v (Pi.single j 1) i) Ω := fun i j =>
    differentiableOn_pi.1 (hfd.clm_apply (differentiableOn_const _)) i
  have hjac : jac g = fun v => ∑ σ : Equiv.Perm (Fin k),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, fderiv ℂ g v (Pi.single i 1) (σ i) := by
    funext v
    rw [jac, ← LinearMap.det_toMatrix', Matrix.det_apply']
    simp [LinearMap.toMatrix'_apply]
  rw [hjac]
  refine DifferentiableOn.fun_sum fun σ _ => (differentiableOn_const _).mul ?_
  intro x hx
  exact (HasFDerivWithinAt.finsetProd (u := Finset.univ)
    (g := fun i v => fderiv ℂ g v (Pi.single i 1) (σ i))
    fun i _ => ((hentry (σ i) i) x hx).hasFDerivWithinAt).differentiableWithinAt

theorem proof (hFin : CompactHolomorphicFibreFinite.Statement) (hInf : RankDeficientFibreInfinite.Statement)
    (hDim : HolomorphicZeroSetDimH.Statement) (hConn : HausdorffNullComplementConnected.Statement) :
    ProperHolomorphicSurjective.Statement := by
  intro k Ω D g hΩ hΩne hD hDc hg hmaps hprop
  refine Set.Subset.antisymm (Set.image_subset_iff.2 hmaps) ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · intro y _
    obtain ⟨v, hv⟩ := hΩne
    exact ⟨v, hv, Subsingleton.elim _ _⟩
  have han := analyticOnNhd_of_differentiableOn hΩ hg
  have hfr : Module.finrank ℝ (Fin k → ℂ) = 2 * k := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]

  have hopen : ∀ v ∈ Ω, jac g v ≠ 0 → g '' Ω ∈ 𝓝 (g v) := by
    intro v hv hdet
    have he : ((LinearMap.equivOfDetNeZero (fderiv ℂ g v : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)
        hdet).toContinuousLinearEquiv : (Fin k → ℂ) →L[ℂ] Fin k → ℂ) = fderiv ℂ g v := by
      ext1 u
      rfl
    have hs : HasStrictFDerivAt g ((LinearMap.equivOfDetNeZero
        (fderiv ℂ g v : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) hdet).toContinuousLinearEquiv :
          (Fin k → ℂ) →L[ℂ] Fin k → ℂ) v := by
      rw [he]
      exact (han v hv).hasStrictFDerivAt
    rw [← hs.map_nhds_eq_of_equiv]
    exact Filter.image_mem_map (hΩ.mem_nhds hv)

  have hreg : ∀ W ⊆ Ω, IsOpen W → W.Nonempty → ∃ w ∈ W, jac g w ≠ 0 := by
    intro W hW hWo hWne
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    obtain ⟨y, hy⟩ := hInf k k W g hWo hWne (hg.mono hW)
      fun v hv hinj => (jac_ne_zero_iff g v).2 hinj (hcon v hv)
    obtain ⟨t, htW, hty⟩ := hy.nonempty
    have hyD : y ∈ D := hty ▸ hmaps (hW htW)
    have hcpt : IsCompact {v | v ∈ Ω ∧ g v = y} :=
      hprop {y} (Set.singleton_subset_iff.2 hyD) isCompact_singleton
    exact hy ((hFin k k Ω g y hΩ hg hcpt).subset fun t ht => ⟨hW ht.1, ht.2⟩)

  set C : Set (Fin k → ℂ) := g '' {v | v ∈ Ω ∧ jac g v = 0} with hC
  have hdimC : dimH C ≤ 2 * ((k - 1 : ℕ) : ℝ≥0∞) := by
    refine le_trans ?_ (hDim k Ω (jac g) hΩ (differentiableOn_jac hΩ hg) hreg)
    refine dimH_image_le_of_locally_lipschitzOn fun x hx => ?_
    obtain ⟨K, t, ht, hL⟩ := ((han x hx.1).contDiffAt (n := 1)).exists_lipschitzOnWith
    exact ⟨K, t, nhdsWithin_le_nhds ht, hL⟩
  have hnull : μH[(Module.finrank ℝ (Fin k → ℂ) : ℝ) - 1] C = 0 := by
    have hlt : dimH C < (((2 * k - 1 : ℕ) : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_natCast]
      calc dimH C ≤ 2 * ((k - 1 : ℕ) : ℝ≥0∞) := hdimC
        _ = ((2 * (k - 1) : ℕ) : ℝ≥0∞) := by push_cast; ring
        _ < ((2 * k - 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast (by omega : 2 * (k - 1) < 2 * k - 1)
    have h0 := hausdorffMeasure_of_dimH_lt hlt
    have hexp : ((((2 * k - 1 : ℕ) : ℝ≥0)) : ℝ) = (Module.finrank ℝ (Fin k → ℂ) : ℝ) - 1 := by
      rw [hfr, NNReal.coe_natCast, Nat.cast_sub (by omega)]
      push_cast
      ring
    rwa [hexp] at h0
  have hR : IsPreconnected (D \ C) := hConn (Fin k → ℂ) D C hD hDc hnull

  have hclosed : ∀ y ∈ D, y ∈ closure (g '' Ω) → y ∈ g '' Ω := by
    intro y hyD hycl
    obtain ⟨r, hr, hrD⟩ := Metric.isOpen_iff.1 hD y hyD
    have hLD : closedBall y (r / 2) ⊆ D := (closedBall_subset_ball (by linarith)).trans hrD
    have hK := hprop (closedBall y (r / 2)) hLD (isCompact_closedBall y (r / 2))
    have hgK : IsCompact (g '' (Ω ∩ g ⁻¹' closedBall y (r / 2))) :=
      hK.image_of_continuousOn (hg.continuousOn.mono Set.inter_subset_left)
    refine Set.image_mono Set.inter_subset_left (hgK.isClosed.closure_subset ?_)
    rw [mem_closure_iff_nhds] at hycl ⊢
    intro U hU
    obtain ⟨z, ⟨hzU, hzB⟩, v, hv, rfl⟩ :=
      hycl (U ∩ ball y (r / 2)) (Filter.inter_mem hU (ball_mem_nhds y (by linarith)))
    exact ⟨g v, hzU, v, ⟨hv, ball_subset_closedBall hzB⟩, rfl⟩

  have hne : ((D \ C) ∩ interior (g '' Ω)).Nonempty := by
    obtain ⟨w, hwΩ, hw⟩ := hreg Ω subset_rfl hΩ hΩne
    have hN : g '' Ω ∈ 𝓝 (g w) := hopen w hwΩ hw
    by_contra hcon
    have hsubC : interior (g '' Ω) ⊆ C := by
      intro z hz
      by_contra hzC
      exact hcon ⟨z, ⟨Set.image_subset_iff.2 hmaps (interior_subset hz), hzC⟩, hz⟩
    have h1 : dimH (interior (g '' Ω)) = Module.finrank ℝ (Fin k → ℂ) :=
      Real.dimH_of_nonempty_interior (by rw [interior_interior]; exact ⟨g w, mem_interior_iff_mem_nhds.2 hN⟩)
    have h2 := (dimH_mono hsubC).trans hdimC
    rw [h1, hfr, show (2 : ℝ≥0∞) * ((k - 1 : ℕ) : ℝ≥0∞) = ((2 * (k - 1) : ℕ) : ℝ≥0∞) by push_cast; ring]
      at h2
    have h3 : 2 * k ≤ 2 * (k - 1) := by exact_mod_cast h2
    omega

  have hRsub : D \ C ⊆ interior (g '' Ω) ∪ (closure (g '' Ω))ᶜ := by
    rintro y ⟨hyD, hyC⟩
    by_cases hyE : y ∈ g '' Ω
    · left
      obtain ⟨v, hv, rfl⟩ := hyE
      have hjv : jac g v ≠ 0 := fun h0 => hyC ⟨v, ⟨hv, h0⟩, rfl⟩
      exact mem_interior_iff_mem_nhds.2 (hopen v hv hjv)
    · right
      exact fun hcl => hyE (hclosed y hyD hcl)
  have hdisj : Disjoint (interior (g '' Ω)) (closure (g '' Ω))ᶜ :=
    Set.disjoint_compl_right_iff_subset.2 (interior_subset.trans subset_closure)
  have hRE := hR.subset_left_of_subset_union isOpen_interior isClosed_closure.isOpen_compl hdisj hRsub hne
  intro y hyD
  by_cases hyC : y ∈ C
  · obtain ⟨v, ⟨hv, _⟩, rfl⟩ := hyC
    exact ⟨v, hv, rfl⟩
  · exact interior_subset (hRE ⟨hyD, hyC⟩)

end ProperHolomorphicSurjective

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMaximalCountUnbranched
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric

namespace MaximalCountUnbranched

theorem analyticOnNhd_of_differentiableOn_pi {d : ℕ} {σ : Type} [Fintype σ] {U : Set (Fin d → ℂ)}
    {G : (Fin d → ℂ) → σ → ℂ} (hU : IsOpen U) (hG : DifferentiableOn ℂ G U) : AnalyticOnNhd ℂ G U := by
  intro y hy
  refine AnalyticAt.pi fun s => ?_
  have hs : DifferentiableOn ℂ (fun x => G x s) U := differentiableOn_pi.1 hG s
  refine analyticOnNhd_of_continuousOn_of_separately hU hs.continuousOn (fun z hz i => ?_) y hy
  have h1 : DifferentiableAt ℂ (fun x => G x s) (Function.update z i (z i)) := by
    rw [Function.update_eq_self]
    exact hs.differentiableAt (hU.mem_nhds hz)
  exact h1.comp (z i) (hasFDerivAt_update (𝕜 := ℂ) z (z i)).differentiableAt

theorem fibre_unique_near {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {N : ℕ} (hmaps : Set.MapsTo A Y D)
    (hopen : ∀ x ∈ Y, ∀ V ∈ 𝓝 x, A '' (Y ∩ V) ∈ 𝓝 (A x))
    (hle : ∀ y ∈ D, {x | x ∈ Y ∧ A x = y}.encard ≤ N)
    {z : σ → ℂ} (hz : z ∈ Y) (hzN : {x' | x' ∈ Y ∧ A x' = A z}.encard = N) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ W ∈ 𝓝 (A z), ∀ y ∈ W,
      {x' | x' ∈ Y ∧ A x' = y}.encard = N ∧ (∃ x' ∈ Y, A x' = y ∧ dist x' z < ε) ∧
      ∀ x₁ ∈ Y, ∀ x₂ ∈ Y, A x₁ = y → A x₂ = y → dist x₁ z < ε → dist x₂ z < ε → x₁ = x₂ := by
  have hSfin : {x' | x' ∈ Y ∧ A x' = A z}.Finite := Set.finite_of_encard_eq_coe hzN
  have hzS : z ∈ {x' | x' ∈ Y ∧ A x' = A z} := ⟨hz, rfl⟩
  have hsep : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p ∈ {x' | x' ∈ Y ∧ A x' = A z} ×ˢ {x' | x' ∈ Y ∧ A x' = A z},
      p.1 ≠ p.2 → 2 * ε < dist p.1 p.2 := by
    refine (eventually_all_finite (hSfin.prod hSfin)).2 fun p _ => ?_
    by_cases hp : p.1 = p.2
    · exact Eventually.of_forall fun _ h => absurd hp h
    · have hpos : 0 < dist p.1 p.2 / 2 := half_pos (dist_pos.2 hp)
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hpos)] with ε hε _
      linarith
  filter_upwards [hsep, self_mem_nhdsWithin] with ε hε hε0
  have hε0 : (0 : ℝ) < ε := hε0
  refine ⟨⋂ s ∈ {x' | x' ∈ Y ∧ A x' = A z}, A '' (Y ∩ ball s ε), (biInter_mem hSfin).2 fun s hs => ?_,
    fun y hy => ?_⟩
  · have := hopen s hs.1 (ball s ε) (ball_mem_nhds s hε0)
    rwa [hs.2] at this
  have hch : ∀ s ∈ {x' | x' ∈ Y ∧ A x' = A z}, ∃ p, p ∈ Y ∧ dist p s < ε ∧ A p = y := by
    intro s hs
    obtain ⟨p, ⟨hpY, hpb⟩, hpA⟩ := Set.mem_iInter₂.1 hy s hs
    exact ⟨p, hpY, mem_ball.1 hpb, hpA⟩
  choose! f hfY hfd hfA using hch
  have hinj : Set.InjOn f {x' | x' ∈ Y ∧ A x' = A z} := by
    intro s hs s' hs' he
    by_contra hne
    have h1 : 2 * ε < dist s s' := hε (s, s') ⟨hs, hs'⟩ hne
    have h2 : dist s s' ≤ dist (f s) s + dist (f s') s' := by
      calc dist s s' ≤ dist s (f s) + dist (f s) s' := dist_triangle _ _ _
        _ = dist (f s) s + dist (f s') s' := by rw [dist_comm s, he]
    linarith [hfd s hs, hfd s' hs']
  have hyD : y ∈ D := hfA z hzS ▸ hmaps (hfY z hzS)
  have hsub : f '' {x' | x' ∈ Y ∧ A x' = A z} ⊆ {x' | x' ∈ Y ∧ A x' = y} := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨hfY s hs, hfA s hs⟩
  have himg : (f '' {x' | x' ∈ Y ∧ A x' = A z}).encard = N := by rw [hinj.encard_image, hzN]
  have hFle := hle y hyD
  have hFeq : {x' | x' ∈ Y ∧ A x' = y}.encard = N :=
    le_antisymm hFle (himg ▸ Set.encard_le_encard hsub)
  have huniq : ∀ x₁ ∈ Y, A x₁ = y → dist x₁ z < ε → x₁ = f z := by
    intro x₁ hx₁ hA₁ hd₁
    by_contra hne
    have hnot : x₁ ∉ f '' {x' | x' ∈ Y ∧ A x' = A z} := by
      rintro ⟨s, hs, rfl⟩
      by_cases hsz : s = z
      · exact hne (hsz ▸ rfl)
      · have h1 : 2 * ε < dist s z := hε (s, z) ⟨hs, hzS⟩ hsz
        have h2 : dist s z ≤ dist (f s) s + dist (f s) z := by
          calc dist s z ≤ dist s (f s) + dist (f s) z := dist_triangle _ _ _
            _ = dist (f s) s + dist (f s) z := by rw [dist_comm s]
        linarith [hfd s hs]
    have hins : insert x₁ (f '' {x' | x' ∈ Y ∧ A x' = A z}) ⊆ {x' | x' ∈ Y ∧ A x' = y} :=
      Set.insert_subset ⟨hx₁, hA₁⟩ hsub
    have hc := Set.encard_le_encard hins
    rw [Set.encard_insert_of_notMem hnot, himg] at hc
    have hc' : ((N + 1 : ℕ) : ℕ∞) ≤ (N : ℕ∞) := by exact_mod_cast hc.trans hFle
    have : N + 1 ≤ N := by exact_mod_cast hc'
    omega
  refine ⟨hFeq, ⟨f z, hfY z hzS, hfA z hzS, hfd z hzS⟩, fun x₁ hx₁ x₂ hx₂ hA₁ hA₂ hd₁ hd₂ => ?_⟩
  rw [huniq x₁ hx₁ hA₁ hd₁, huniq x₂ hx₂ hA₂ hd₂]

theorem proof (hRE : RiemannExtensionAnalytic.Statement) : MaximalCountUnbranched.Statement := by
  intro σ _ Y d A D N _hD hmaps _hprop hopen hgen x hx hxN
  have key := fun (z : σ → ℂ) (hz : z ∈ Y) (hzN : {x' | x' ∈ Y ∧ A x' = A z}.encard = N) =>
    fibre_unique_near hmaps hopen hgen.1 hz hzN
  obtain ⟨ε, ⟨W₀, hW₀, hW₀p⟩, hε0⟩ := ((key x hx hxN).and self_mem_nhdsWithin).exists
  have hε0 : (0 : ℝ) < ε := hε0
  obtain ⟨U, g, hUo, hxU, _hUD, hg, hgnz, hgsec⟩ := hgen.2 (A x) (hmaps hx)
  have hOo : IsOpen (interior W₀ ∩ U) := isOpen_interior.inter hUo
  have hOW : ∀ y ∈ interior W₀ ∩ U, y ∈ W₀ := fun y hy => interior_subset hy.1
  have hex : ∀ y ∈ interior W₀ ∩ U, ∃ x' ∈ Y, A x' = y ∧ dist x' x < ε :=
    fun y hy => (hW₀p y (hOW y hy)).2.1
  choose! h hhY hhA hhd using hex
  have hu : ∀ y ∈ interior W₀ ∩ U, ∀ x' ∈ Y, A x' = y → dist x' x < ε → x' = h y :=
    fun y hy x' hx' hA hd =>
      (hW₀p y (hOW y hy)).2.2 x' hx' (h y) (hhY y hy) hA (hhA y hy) hd (hhd y hy)

  have hcont : ContinuousOn h (interior W₀ ∩ U) := by
    intro y₀ hy₀
    refine ContinuousAt.continuousWithinAt ?_
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro η hη
    have hzN : {x' | x' ∈ Y ∧ A x' = A (h y₀)}.encard = N := by
      rw [hhA y₀ hy₀]; exact (hW₀p y₀ (hOW y₀ hy₀)).1
    have hgap : 0 < ε - dist (h y₀) x := by linarith [hhd y₀ hy₀]
    have hsmall : ∀ᶠ e in 𝓝[>] (0 : ℝ), e < min η (ε - dist (h y₀) x) :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (lt_min hη hgap))
    obtain ⟨e, ⟨W₁, hW₁, hW₁p⟩, he⟩ := ((key (h y₀) (hhY y₀ hy₀) hzN).and hsmall).exists
    rw [hhA y₀ hy₀] at hW₁
    filter_upwards [hW₁, hOo.mem_nhds hy₀] with y hy1 hyO
    obtain ⟨x'', hx''Y, hx''A, hx''d⟩ := (hW₁p y hy1).2.1
    have hm1 := min_le_left η (ε - dist (h y₀) x)
    have hm2 := min_le_right η (ε - dist (h y₀) x)
    have hx''x : dist x'' x < ε := by
      have := dist_triangle x'' (h y₀) x
      linarith
    rw [← hu y hyO x'' hx''Y hx''A hx''x]
    linarith

  have hdiff : ∀ y₀ ∈ interior W₀ ∩ U, g y₀ ≠ 0 → DifferentiableAt ℂ h y₀ := by
    intro y₀ hy₀ hg₀
    obtain ⟨_, hsec⟩ := hgsec y₀ hy₀.2 hg₀
    obtain ⟨O₁, V₁, h₁, hO₁, _hV₁, hzV₁, han₁, hA₁, hYV₁⟩ := hsec (h y₀) (hhY y₀ hy₀) (hhA y₀ hy₀)
    have hz : h y₀ ∈ h₁ '' O₁ := hYV₁ ▸ ⟨hhY y₀ hy₀, hzV₁⟩
    obtain ⟨y₁, hy₁, hy₁e⟩ := hz
    have hy₁₀ : y₁ = y₀ := by rw [← hA₁ y₁ hy₁, hy₁e, hhA y₀ hy₀]
    rw [hy₁₀] at hy₁ hy₁e
    have hc₁ : ContinuousAt h₁ y₀ := (han₁ y₀ hy₁).continuousAt
    have hball : ball x ε ∈ 𝓝 (h₁ y₀) := by
      rw [hy₁e]; exact isOpen_ball.mem_nhds (mem_ball.2 (hhd y₀ hy₀))
    have heq : h₁ =ᶠ[𝓝 y₀] h := by
      filter_upwards [hc₁.preimage_mem_nhds hball, hO₁.mem_nhds hy₁, hOo.mem_nhds hy₀]
        with y hyb hyO₁ hyO
      have hyY : h₁ y ∈ Y := by
        have hmem : h₁ y ∈ h₁ '' O₁ := ⟨y, hyO₁, rfl⟩
        rw [← hYV₁] at hmem
        exact hmem.1
      exact hu y hyO (h₁ y) hyY (hA₁ y hyO₁) (mem_ball.1 hyb)
    exact (han₁ y₀ hy₁).differentiableAt.congr_of_eventuallyEq heq.symm

  have hgd : DifferentiableOn ℂ g (interior W₀ ∩ U) := hg.differentiableOn.mono fun y hy => hy.2
  have hgnz' : ∀ V : Set (Fin d → ℂ), IsOpen V → V ⊆ interior W₀ ∩ U → V.Nonempty → ∃ t ∈ V, g t ≠ 0 :=
    fun V hV hVO hVn => hgnz V hV (hVO.trans Set.inter_subset_right) hVn
  have hdense : interior W₀ ∩ U ⊆ closure ((interior W₀ ∩ U) ∩ {t | g t ≠ 0}) := by
    intro y hy
    rw [_root_.mem_closure_iff]
    intro o ho hyo
    obtain ⟨t, ht, hgt⟩ := hgnz' (o ∩ (interior W₀ ∩ U)) (ho.inter hOo) Set.inter_subset_right ⟨y, hyo, hy⟩
    exact ⟨t, ht.1, ht.2, hgt⟩
  have hcoord : ∀ j : σ, DifferentiableOn ℂ (fun y => h y j) (interior W₀ ∩ U) := by
    intro j
    have hdj : DifferentiableOn ℂ (fun y => h y j) ((interior W₀ ∩ U) ∩ {t | g t ≠ 0}) :=
      fun y hy => (differentiableAt_pi.1 (hdiff y hy.1 hy.2) j).differentiableWithinAt
    have hbj : ∀ τ ∈ interior W₀ ∩ U, ∃ M ∈ 𝓝 τ,
        Bornology.IsBounded ((fun y => h y j) '' (M ∩ (interior W₀ ∩ U) ∩ {t | g t ≠ 0})) := by
      intro τ _
      refine ⟨Set.univ, univ_mem, ?_⟩
      rw [isBounded_iff_forall_norm_le]
      refine ⟨‖x‖ + ε, ?_⟩
      rintro _ ⟨y, ⟨⟨_, hyO⟩, _⟩, rfl⟩
      calc ‖h y j‖ ≤ ‖h y‖ := norm_le_pi_norm (h y) j
        _ ≤ ‖x‖ + ε := norm_le_of_mem_closedBall (mem_closedBall.2 (hhd y hyO).le)
    obtain ⟨F, hF, hFe⟩ := hRE d (interior W₀ ∩ U) g (fun y => h y j) hOo hgd hgnz' hdj hbj
    have hEq : Set.EqOn F (fun y => h y j) (interior W₀ ∩ U) :=
      hFe.of_subset_closure hF.continuousOn (continuousOn_pi.1 hcont j) Set.inter_subset_left hdense
    exact hF.congr fun y hy => (hEq hy).symm
  have han : AnalyticOnNhd ℂ h (interior W₀ ∩ U) :=
    analyticOnNhd_of_differentiableOn_pi hOo (differentiableOn_pi.2 hcoord)
  refine ⟨interior W₀ ∩ U, ball x ε ∩ A ⁻¹' (interior W₀ ∩ U), h, hOo,
    isOpen_ball.inter (hOo.preimage A.continuous),
    ⟨mem_ball_self hε0, mem_interior_iff_mem_nhds.2 hW₀, hxU⟩, han, hhA, ?_⟩
  ext x'
  constructor
  · rintro ⟨hx'Y, hx'b, hx'O⟩
    exact ⟨A x', hx'O, (hu (A x') hx'O x' hx'Y rfl (mem_ball.1 hx'b)).symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hhY y hy, mem_ball.2 (hhd y hy), show A (h y) ∈ interior W₀ ∩ U from (hhA y hy).symm ▸ hy⟩

end MaximalCountUnbranched

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
