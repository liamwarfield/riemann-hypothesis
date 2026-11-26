module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseVectorProperties
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightTendstoC2
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralTendstoOffDivisor

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralLimitOnModel
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralLimitOnModel
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix

theorem continuous_of_atlasSmooth {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {f : X → ℝ} (hf : A.Smooth f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousOn (f ∘ (A.chart j).symm) (A.chart j).target := by
    have := (hf j).continuousOn
    simpa [Set.preimage_univ, Set.inter_univ] using this
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) x :=
    (h1.continuousAt ((A.chart j).open_target.mem_nhds ((A.chart j).map_source hj))).comp
      ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
  simp [(A.chart j).left_inv hz]

theorem tendsto_ptsIntegral_of_chart_conv : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData M.atlas) (Θ : LocPot M.Xc) (Pp : Fin n → LocPot M.Xc) (f : Fin n → M.Xc → ℝ) (fT : Fin n → ℝ → M.Xc → ℝ) (G : M.Xc → ℝ) (GT : ℝ → M.Xc → ℝ) (C : ℝ) (L : ℝ → Fin n → HermLine ι) (g : ℝ → ((Σ k, ι k) → ℂ) → ℝ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (n + 1) → IsPotential M.atlas Θ → IsPosPot M.atlas Θ → (∀ i, IsPotential M.atlas (Pp i)) → (∀ i, M.atlas.SmoothOn R.Yo (f i)) → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, M.atlas.Smooth (fT i t) ∧ IsPsh M.atlas (Pp i + LocPot.ofFun (fT i t) + Θ) ∧ ∀ x ∈ R.Yo, |fT i t x| ≤ C + C * Real.log (R.r x) ∧ fT i t x ≤ C) → (∀ i, ∀ j, ∀ K' ⊆ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' R.Yo, IsCompact K' → TendstoUniformlyOn (fun t => fT i t ∘ (M.atlas.chart j).symm) (f i ∘ (M.atlas.chart j).symm) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fT i t ∘ (M.atlas.chart j).symm)) (fderiv ℝ (f i ∘ (M.atlas.chart j).symm)) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (fT i t ∘ (M.atlas.chart j).symm))) (fderiv ℝ (fderiv ℝ (f i ∘ (M.atlas.chart j).symm))) (𝓝[>] 0) K') → (∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (GT t) ∧ ∀ x ∈ R.Yo, |GT t x| ≤ C + C * Real.log (R.r x)) → (∀ K' ⊆ R.Yo, IsCompact K' → TendstoUniformlyOn GT G (𝓝[>] 0) K') → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i x, ∀ y₀ ∈ (Pp i + LocPot.ofFun (fT i t)).U x ∩ Set.univ, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Pp i + LocPot.ofFun (fT i t)).U x ∩ Set.univ ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts P ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G' : M.Xc → ℂ, M.atlas.HoloOn U G' ∧ ∀ y' ∈ U, (Pp i + LocPot.ofFun (fT i t)).φ x y' - Real.log ((L t i).h (s y')) = (G' y').re) → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ mcPts P, g t z = GT t (M.proj z)) → ∃ l : ℝ, Tendsto (fun t => ptsIntegral P (pot (L t)) (g t)) (𝓝[>] 0) (𝓝 l) := by
  intro K _ ι _ P n M R Θ Pp f fT G GT C L g hV hΘ hΘp hP hf hfT hconv hGT hGc hrel hg
  classical
  by_cases hQ : ∃ Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ), IsGoodProj P Q
  · have hYo := (GlobalTheory.T.regular_chart_data_properties n M.Xc M.atlas R).1
    have hmeas : ∀ᶠ t in 𝓝[>] (0 : ℝ), @Measurable M.Xc ℝ (borel M.Xc) _ (R.Yo.indicator (GT t)) ∧
        ∀ x ∈ R.Yo, |GT t x| ≤ C + C * Real.log (R.r x) := by
      filter_upwards [hGT] with t ht
      refine ⟨?_, ht.2⟩
      letI : MeasurableSpace M.Xc := borel M.Xc
      haveI : BorelSpace M.Xc := ⟨rfl⟩
      exact (continuous_of_atlasSmooth ht.1).measurable.indicator hYo.measurableSet
    obtain ⟨-, hint, hlim⟩ := GlobalTheory.T.mixed_integral_tendsto_off_divisor n M.Xc M.atlas R Θ hΘ hΘp Pp f fT G GT C hP hf hfT hconv
      hmeas hGc
    refine ⟨_, hlim.congr' ?_⟩
    filter_upwards [hint, hfT, hGT, hrel, hg] with t hit hft hgt hrt hgt'
    have hpush := GlobalTheory.T.mixed_integral_model_formula K ι P n M hQ.choose Set.univ ∅ ∅ (fun _ => 1) (L t)
      (fun i => Pp i + LocPot.ofFun (fT i t)) (g t) (GT t) hV hQ.choose_spec isOpen_univ
      (fun j => by simp)
      (fun Ψ _ => by simp)
      (fun i x => by
        intro j
        have h1 := (hP i).1 x j
        have h2 := (hft i).1 j
        have h3 := h1.add (h2.mono (fun y hy => ⟨hy.1, Set.mem_univ _⟩))
        refine (h3.mono ?_).congr ?_
        · rintro y ⟨hy, hy'⟩
          exact ⟨hy, hy'.1.1⟩
        · intro y _
          rfl)
      (fun i x y₀ hy₀ => by
        obtain ⟨U, hU, hyU, hUs, s, hs, hsp, G', hG', hrel'⟩ := hrt i x y₀ hy₀
        exact ⟨U, hU, hyU, hUs, s, hs, hsp, G', hG', fun y' hy' => by
          simpa using hrel' y' hy'⟩)
      (fun z hz _ _ _ => hgt' z hz)
      (fun j => ((continuous_of_atlasSmooth hgt.1).comp_continuousOn
        (M.atlas.chart j).continuousOn_symm).aestronglyMeasurable (M.atlas.chart j).open_target.measurableSet)
    have h3 := (hpush.2.2 hit).2
    have hpot : (fun i z => (fun _ : Fin n => (1 : ℝ)) i * Real.log ((L t i).h z)) = pot (L t) := by
      funext i z
      simp [pot]
    rw [hpot] at h3
    rw [ptsIntegral, dite_eq_left hQ, h3]
  · refine ⟨0, ?_⟩
    have : (fun t => ptsIntegral P (pot (L t)) (g t)) = fun _ => (0 : ℝ) := by
      funext t
      rw [ptsIntegral, dite_eq_right hQ]
    rw [this]
    exact tendsto_const_nhds

end GlobalTheory.CompanionTheory.Ar.Giv.Mix
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralLimitOnModelStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_integral_limit_on_model : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData M.atlas) (Θ : LocPot M.Xc) (Pp : Fin n → LocPot M.Xc) (f : Fin n → M.Xc → ℝ) (fT : Fin n → ℝ → M.Xc → ℝ) (G : M.Xc → ℝ) (GT : ℝ → M.Xc → ℝ) (C : ℝ) (L : ℝ → Fin n → HermLine ι) (g : ℝ → ((Σ k, ι k) → ℂ) → ℝ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (n + 1) → IsPotential M.atlas Θ → IsPosPot M.atlas Θ → (∀ i, IsPotential M.atlas (Pp i)) → (∀ i, M.atlas.SmoothOn R.Yo (f i)) → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, M.atlas.Smooth (fT i t) ∧ IsPsh M.atlas (Pp i + LocPot.ofFun (fT i t) + Θ) ∧ ∀ x ∈ R.Yo, |fT i t x| ≤ C + C * Real.log (R.r x) ∧ fT i t x ≤ C) → (∀ i, ∀ j, ∀ K' ⊆ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' R.Yo, IsCompact K' → TendstoUniformlyOn (fun t => fT i t ∘ (M.atlas.chart j).symm) (f i ∘ (M.atlas.chart j).symm) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fT i t ∘ (M.atlas.chart j).symm)) (fderiv ℝ (f i ∘ (M.atlas.chart j).symm)) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (fT i t ∘ (M.atlas.chart j).symm))) (fderiv ℝ (fderiv ℝ (f i ∘ (M.atlas.chart j).symm))) (𝓝[>] 0) K') → (∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (GT t) ∧ ∀ x ∈ R.Yo, |GT t x| ≤ C + C * Real.log (R.r x)) → (∀ K' ⊆ R.Yo, IsCompact K' → TendstoUniformlyOn GT G (𝓝[>] 0) K') → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i x, ∀ y₀ ∈ (Pp i + LocPot.ofFun (fT i t)).U x ∩ Set.univ, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Pp i + LocPot.ofFun (fT i t)).U x ∩ Set.univ ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts P ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G' : M.Xc → ℂ, M.atlas.HoloOn U G' ∧ ∀ y' ∈ U, (Pp i + LocPot.ofFun (fT i t)).φ x y' - Real.log ((L t i).h (s y')) = (G' y').re) → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ mcPts P, g t z = GT t (M.proj z)) → ∃ l : ℝ, Tendsto (fun t => ptsIntegral P (pot (L t)) (g t)) (𝓝[>] 0) (𝓝 l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Mix.tendsto_ptsIntegral_of_chart_conv | exact GlobalTheory.CompanionTheory.Ar.Giv.Mix.tendsto_ptsIntegral_of_chart_conv | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Mix.tendsto_ptsIntegral_of_chart_conv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedHodgeMetricFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedHodgeMetricFormula
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix

private theorem hermOfFun_h_eq_of_homogeneous_of_pos {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (a : K → ℤ) (F : ((Σ k, ι k) → ℂ) → ℝ) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hF : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z)
    (hpos : 0 < F z) : (hermOfFun ι a F).h z = F z := by
  have h0 : (torusSetoid (ι := ι)).r (orbitRep z) z := Quotient.mk_out (s := torusSetoid) z
  obtain ⟨c, hc, hcz⟩ := h0
  have ho : orbitRep z = torusSmul (fun k => (c k)⁻¹) z := by
    funext p
    conv_rhs => rw [hcz]
    simp only [torusSmul]
    rw [← mul_assoc, inv_mul_cancel₀ (hc p.1), one_mul]
  have hc' : ∀ k, (c k)⁻¹ ≠ 0 := fun k => inv_ne_zero (hc k)
  have hpc : 0 < ∏ k, ‖(c k)⁻¹‖ ^ a k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hc' k)) _
  have hr := refNorm_pos a hz
  show refNorm a z * Real.exp (Real.log (F (orbitRep z) / refNorm a (orbitRep z))) = F z
  rw [ho, hF _ hc', refNorm_smul, mul_div_mul_left _ _ hpc.ne', Real.exp_log (div_pos hpos hr)]
  field_simp

private theorem smoothRep_h_eq_of_mem_mcPts {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (A : HermLine ι) (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P) :
    (smoothRep P A).h z = A.h z := by
  unfold smoothRep
  split_ifs with h
  · exact h.choose_spec.2.2 z hz
  · rfl

private theorem eval_torusSmul_map_eq_eval_mConeMap {K : Type} {ι : K → Type} (c : K → ℂ) (z : (Σ k, ι k) → ℂ)
    (f : MRing ι) :
    eval (torusSmul c z) (map (Int.castRingHom ℂ) f) = MvPolynomial.eval c (mConeMap z f) := by
  have h : (eval (torusSmul c z)).comp (map (Int.castRingHom ℂ)) =
      (MvPolynomial.eval c).comp (mConeMap z).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro n
      simp
    · intro q
      simp [mConeMap, torusSmul, mul_comm]
  exact RingHom.congr_fun h f

private theorem torusSmul_mem_mcPts_mCoordIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) :
    torusSmul c z ∈ mcPts (mCoordIdeal y) := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, mul_ne_zero (hc k) hi⟩
  · have hf' : f ∈ mCoordIdeal z := VertFactorPos.mCoordIdeal_le hz hf
    rw [eval_torusSmul_map_eq_eval_mConeMap, RingHom.mem_ker.1 hf', map_zero]

theorem muReg_h_eq_of_mem_mcPts : ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ) (t : ℝ), ∀ z ∈ mcPts (mCoordIdeal D.y), (muReg X.H X.S B t).h z = X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z)) * ∏ p ∈ D.SB B, D.vertFactor p z := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B t z hz
  have hz' : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := hz.1
  have hpos := VertFactorPos.proof II Ψ K ι Ω E D
  have hsm := VertFactorSmooth.proof VertFactorPos.proof II Ψ K ι Ω E D
  have hproj : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → X.M.proj (torusSmul c z) = X.M.proj z := fun c hc =>
    ((X.M.fibre z hz (torusSmul c z) (torusSmul_mem_mcPts_mCoordIdeal D.y hz hc)).2 ⟨c, hc, rfl⟩).symm
  have hreg : (X.S.regLine t).h z = X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z)) := by
    refine hermOfFun_h_eq_of_homogeneous_of_pos (muLine X.H).a
      (fun w => X.S.ref.h w * Real.exp (X.S.regWeight t (X.M.proj w))) z hz' ?_
      (mul_pos (X.S.ref.pos z hz') (Real.exp_pos _))
    intro c hc
    show X.S.ref.h (torusSmul c z) * Real.exp (X.S.regWeight t (X.M.proj (torusSmul c z))) =
      (∏ k, ‖c k‖ ^ (muLine X.H).a k) * (X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z)))
    have hs : X.S.ref.h (torusSmul c z) = (∏ k, ‖c k‖ ^ (muLine X.H).a k) * X.S.ref.h z := by
      rw [← X.S.ref_deg]
      exact X.S.ref.smul c z hc
    rw [hproj c hc, hs, mul_assoc]
  rw [muReg, smoothRep_h_eq_of_mem_mcPts _ _ z hz]
  refine (hermOfFun_h_eq_of_homogeneous_of_pos (muTwDeg X.H B)
    (fun w => (X.S.regLine t).h w * ∏ p ∈ D.SB B, D.vertFactor p w) z hz' ?_ ?_).trans ?_
  · intro c hc
    show (X.S.regLine t).h (torusSmul c z) * ∏ p ∈ D.SB B, D.vertFactor p (torusSmul c z) =
      (∏ k, ‖c k‖ ^ muTwDeg X.H B k) * ((X.S.regLine t).h z * ∏ p ∈ D.SB B, D.vertFactor p z)
    have h1 : (X.S.regLine t).h (torusSmul c z) = (∏ k, ‖c k‖ ^ X.H.aMu k) * (X.S.regLine t).h z :=
      (X.S.regLine t).smul c z hc
    have h2 : ∀ p ∈ D.SB B,
        D.vertFactor p (torusSmul c z) = (∏ k, ‖c k‖ ^ D.vdeg p k) * D.vertFactor p z :=
      fun p hp => (hsm p (Finset.mem_filter.1 hp).1).1 z hz c hc
    rw [h1, Finset.prod_congr rfl h2, Finset.prod_mul_distrib, muTwDeg,
      MuRegSmooth.prod_norm_zpow_add_sum hc]
    ring
  · exact mul_pos ((X.S.regLine t).pos z hz')
      (Finset.prod_pos fun p hp => hpos p (Finset.mem_filter.1 hp).1 z hz)
  · show (X.S.regLine t).h z * ∏ p ∈ D.SB B, D.vertFactor p z = _
    rw [hreg]

end GlobalTheory.CompanionTheory.Ar.Giv.Mix
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedHodgeMetricFormulaStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularized_hodge_metric_formula : ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ) (t : ℝ), ∀ z ∈ mcPts (mCoordIdeal D.y), (muReg X.H X.S B t).h z = X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z)) * ∏ p ∈ D.SB B, D.vertFactor p z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Mix.muReg_h_eq_of_mem_mcPts | exact GlobalTheory.CompanionTheory.Ar.Giv.Mix.muReg_h_eq_of_mem_mcPts | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Mix.muReg_h_eq_of_mem_mcPts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionNumberTelescoping
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionNumberTelescoping
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix.Tele

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def positionPerm {n : ℕ} (m : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  finSuccEquivLast.trans (finSuccEquiv' m).symm

theorem positionPerm_last {n : ℕ} (m : Fin (n + 1)) : positionPerm m (Fin.last n) = m := by
  simp [positionPerm]

theorem positionPerm_castSucc {n : ℕ} (m : Fin (n + 1)) (j : Fin n) :
    positionPerm m (Fin.castSucc j) = m.succAbove j := by
  simp [positionPerm]

def word {n : ℕ} (a a₀ A' : HermLine ι) (k m : ℕ) : Fin (n + 1) → HermLine ι :=
  fun j => if (j : ℕ) < m then a else if (j : ℕ) < k then a₀ else A'

theorem word_comp_low {n : ℕ} (a a₀ A' : HermLine ι) (k m : ℕ) (hm : m < n + 1) (hk : m < k) :
    word (n := n) a a₀ A' k m ∘ positionPerm ⟨m, hm⟩ = Fin.snoc (mixWord (n := n) a a₀ A' k m) a₀ := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [word, positionPerm_last, hk]
  | cast i =>
    simp only [Function.comp_apply, positionPerm_castSucc, Fin.snoc_castSucc, word, mixWord]
    rcases lt_or_ge (i : ℕ) m with h | h
    · rw [Fin.succAbove_of_castSucc_lt ⟨m, hm⟩ i (Fin.lt_def.mpr h)]
      simp [h]
    · rw [Fin.succAbove_of_le_castSucc ⟨m, hm⟩ i (Fin.le_def.mpr h)]
      have h1 : ¬ (i : ℕ) + 1 < m := by omega
      have h2 : ¬ (i : ℕ) < m := by omega
      simp [h1, h2]

theorem word_comp_high {n : ℕ} (a a₀ A' : HermLine ι) (k m : ℕ) (hm : m < n + 1) :
    word (n := n) a a₀ A' k (m + 1) ∘ positionPerm ⟨m, hm⟩ = Fin.snoc (mixWord (n := n) a a₀ A' k m) a := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [word, positionPerm_last]
  | cast i =>
    simp only [Function.comp_apply, positionPerm_castSucc, Fin.snoc_castSucc, word, mixWord]
    rcases lt_or_ge (i : ℕ) m with h | h
    · rw [Fin.succAbove_of_castSucc_lt ⟨m, hm⟩ i (Fin.lt_def.mpr h)]
      have h1 : (i : ℕ) < m + 1 := by omega
      simp [h, h1]
    · rw [Fin.succAbove_of_le_castSucc ⟨m, hm⟩ i (Fin.le_def.mpr h)]
      have h1 : ¬ (i : ℕ) + 1 < m + 1 := by omega
      have h2 : ¬ (i : ℕ) < m := by omega
      simp [h1, h2]

theorem forall_snoc {n : ℕ} {p : HermLine ι → Prop} {L : Fin n → HermLine ι} {x : HermLine ι}
    (hL : ∀ j, p (L j)) (hx : p x) : ∀ j, p ((Fin.snoc L x : Fin (n + 1) → HermLine ι) j) := by
  intro j
  induction j using Fin.lastCases with
  | last => simpa using hx
  | cast i => simpa using hL i

theorem cone_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) :
    (∀ k, ∃ i, (fun p : Σ k, ι k => c p.1 * z p) ⟨k, i⟩ ≠ 0) ↔ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
  constructor
  · intro h k
    obtain ⟨i, hi⟩ := h k
    exact ⟨i, right_ne_zero_of_mul hi⟩
  · intro h k
    obtain ⟨i, hi⟩ := h k
    exact ⟨i, mul_ne_zero (hc k) hi⟩

theorem logRatio_smul {a a₀ : HermLine ι} (hd : a.a = a₀.a) (c : K → ℂ) (z : (Σ k, ι k) → ℂ)
    (hc : ∀ k, c k ≠ 0) : logRatio a a₀ (fun p => c p.1 * z p) = logRatio a a₀ z := by
  have hcone := cone_smul c z hc
  unfold logRatio
  by_cases h : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
  · rw [if_pos (hcone.mpr h), if_pos h, a.smul c z hc, a₀.smul c z hc, hd]
    have hprod : (∏ k, ‖c k‖ ^ a₀.a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
    rw [Real.log_mul hprod (a₀.pos z h).ne', Real.log_mul hprod (a.pos z h).ne']
    ring
  · rw [if_neg (fun h' => h (hcone.mp h')), if_neg h]

theorem logRatio_smooth {a a₀ : HermLine ι} (ha : IsSmoothHerm a) (ha₀ : IsSmoothHerm a₀) :
    ReciprocityTheory.ChartRestriction.G.AI.I2.SmoothFn (logRatio a a₀) := by
  have h0 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a₀.h {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := ha₀
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a.h {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := ha
  show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (logRatio a a₀) {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  refine ((h0.log fun z hz => (a₀.pos z hz).ne').sub (h1.log fun z hz => (a.pos z hz).ne')).congr ?_
  intro z hz
  have hz' : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := hz
  simp only [logRatio, if_pos hz']

theorem tensor_logRatio_h {a a₀ : HermLine ι}
    (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → logRatio a a₀ (fun p => c p.1 * z p) = logRatio a a₀ z)
    (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    (a₀.tensor (HermLine.ofWeight (logRatio a a₀) hu)).h z = a.h z := by
  have h0 := a₀.pos z hz
  have h1 := a.pos z hz
  show a₀.h z * Real.exp (-logRatio a a₀ z) = a.h z
  rw [logRatio, if_pos hz, neg_sub, Real.exp_sub, Real.exp_log h1, Real.exp_log h0,
    ← mul_div_assoc, mul_div_right_comm, div_self h0.ne', one_mul]

theorem word_step (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) (P : Ideal (MRing ι)) (n : ℕ) (a a₀ A' : HermLine ι) (k m : ℕ)
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (n + 1)) (ha : IsSmoothHerm a) (ha₀ : IsSmoothHerm a₀) (hA' : IsSmoothHerm A')
    (hd : a.a = a₀.a) (hk : k ≤ n + 1) (hm : m < k) :
    I P (n + 1) (word a a₀ A' k (m + 1)) - I P (n + 1) (word a a₀ A' k m) =
      -ptsIntegral P (pot (mixWord (n := n) a a₀ A' k m)) (logRatio a a₀) := by
  have hu : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      logRatio a a₀ (fun p => c p.1 * z p) = logRatio a a₀ z := fun c z hc => logRatio_smul hd c z hc
  have hMs : ∀ j, IsSmoothHerm (mixWord (n := n) a a₀ A' k m j) := fun j => by
    simp only [mixWord]
    split_ifs <;> assumption
  have hWs : ∀ r (j : Fin (n + 1)), IsSmoothHerm (word (n := n) a a₀ A' k r j) := fun r j => by
    simp only [word]
    split_ifs <;> assumption
  have hmn : m < n + 1 := lt_of_lt_of_le hm hk
  have h0 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a₀.h {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := ha₀
  have hlr : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (logRatio a a₀)
      {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := logRatio_smooth ha ha₀
  have hT : IsSmoothHerm (a₀.tensor (HermLine.ofWeight (logRatio a a₀) hu)) := by
    show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => a₀.h z * Real.exp (-logRatio a a₀ z))
      {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
    exact h0.mul hlr.neg.exp
  have e1 : I P (n + 1) (word (n := n) a a₀ A' k (m + 1)) =
      I P (n + 1) (Fin.snoc (mixWord (n := n) a a₀ A' k m) a) := by
    rw [← word_comp_high a a₀ A' k m hmn, hI.1 P (n + 1) _ _ hP (hWs (m + 1))]
  have e0 : I P (n + 1) (word (n := n) a a₀ A' k m) =
      I P (n + 1) (Fin.snoc (mixWord (n := n) a a₀ A' k m) a₀) := by
    rw [← word_comp_low a a₀ A' k m hmn hm, hI.1 P (n + 1) _ _ hP (hWs m)]
  have e2 : I P (n + 1) (Fin.snoc (mixWord (n := n) a a₀ A' k m) a) =
      I P (n + 1) (Fin.snoc (mixWord (n := n) a a₀ A' k m)
        (a₀.tensor (HermLine.ofWeight (logRatio a a₀) hu))) := by
    refine metricLocal K ι I hI P (n + 1) _ _ hP (forall_snoc (p := IsSmoothHerm) hMs ha)
      (forall_snoc (p := IsSmoothHerm) hMs hT) ?_ ?_
    · intro j
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        show a.a = a₀.a + 0
        rw [add_zero, hd]
      | cast i => simp only [Fin.snoc_castSucc]
    · intro j z hz
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        exact (tensor_logRatio_h hu z hz.1).symm
      | cast i => simp only [Fin.snoc_castSucc]
  have e3 := metricChange K ι I hI P n (mixWord (n := n) a a₀ A' k m) a₀ (logRatio a a₀) hu hP hMs ha₀
    (logRatio_smooth ha ha₀)
  rw [e1, e0, e2, e3]
  ring

theorem positionTelescope : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I →
    ∀ (P : Ideal (MRing ι)) (n : ℕ) (a a₀ A' : HermLine ι) (k : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (n + 1) →
      IsSmoothHerm a → IsSmoothHerm a₀ → IsSmoothHerm A' → a.a = a₀.a → k ≤ n + 1 →
      I P (n + 1) (fun j => if (j : ℕ) < k then a else A') -
          I P (n + 1) (fun j => if (j : ℕ) < k then a₀ else A') =
        -∑ i ∈ Finset.range k, ptsIntegral P (pot (mixWord (n := n) a a₀ A' k i)) (logRatio a a₀) := by
  intro K _ ι _ I hI P n a a₀ A' k hP ha ha₀ hA' hd hk
  have h1 : (fun j : Fin (n + 1) => if (j : ℕ) < k then a else A') = word (n := n) a a₀ A' k k := by
    funext j
    by_cases h : (j : ℕ) < k <;> simp [word, h]
  have h0 : (fun j : Fin (n + 1) => if (j : ℕ) < k then a₀ else A') = word (n := n) a a₀ A' k 0 := by
    funext j
    simp [word]
  have hs := Finset.sum_range_sub (fun r => I P (n + 1) (word (n := n) a a₀ A' k r)) k
  rw [h1, h0, ← hs, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact word_step I hI P n a a₀ A' k i hP ha ha₀ hA' hd hk (Finset.mem_range.mp hi)

end GlobalTheory.CompanionTheory.Ar.Giv.Mix.Tele
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionNumberTelescopingStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_number_telescoping : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (P : Ideal (MRing ι)) (n : ℕ) (a a₀ A' : HermLine ι) (k : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (n + 1) → IsSmoothHerm a → IsSmoothHerm a₀ → IsSmoothHerm A' → a.a = a₀.a → k ≤ n + 1 → I P (n + 1) (fun j => if (j : ℕ) < k then a else A') - I P (n + 1) (fun j => if (j : ℕ) < k then a₀ else A') = -∑ i ∈ Finset.range k, ptsIntegral P (pot (mixWord (n := n) a a₀ A' k i)) (logRatio a a₀) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Mix.Tele.positionTelescope | exact GlobalTheory.CompanionTheory.Ar.Giv.Mix.Tele.positionTelescope | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Mix.Tele.positionTelescope <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PshDoublePositivePotential
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PshDoublePositivePotential
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix.TwicePos

theorem isPsh_add_zero_add (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ : LocPot X) (hΘ : IsPotential A Θ) (hpos : IsPosPot A Θ) :
    IsPsh A (Θ + LocPot.ofFun (fun _ => (0 : ℝ)) + Θ) := by
  unfold ReciprocityTheory.AnForm.M.IsPsh
  intro x j y hy w
  have hy' : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x := ⟨hy.1, hy.2.2⟩
  have hfun : ((Θ + LocPot.ofFun (fun _ => (0 : ℝ)) + Θ).φ x ∘ (A.chart j).symm) =
      fun z => (2 : ℝ) • (Θ.φ x ∘ (A.chart j).symm) z := by
    funext z
    show Θ.φ x _ + 0 + Θ.φ x _ = (2 : ℝ) • Θ.φ x _
    rw [smul_eq_mul]
    ring
  have hlevi : ∀ z v, ReciprocityTheory.AnForm.levi (fun z => (2 : ℝ) • (Θ.φ x ∘ (A.chart j).symm) z) z v =
      2 * ReciprocityTheory.AnForm.levi (Θ.φ x ∘ (A.chart j).symm) z v := by
    intro z v
    unfold ReciprocityTheory.AnForm.levi
    have h1 : fderiv ℝ (fun z => (2 : ℝ) • (Θ.φ x ∘ (A.chart j).symm) z) =
        (2 : ℝ) • fderiv ℝ (Θ.φ x ∘ (A.chart j).symm) := fderiv_const_smul_field (2 : ℝ)
    have h2 : fderiv ℝ ((2 : ℝ) • fderiv ℝ (Θ.φ x ∘ (A.chart j).symm)) =
        (2 : ℝ) • fderiv ℝ (fderiv ℝ (Θ.φ x ∘ (A.chart j).symm)) := fderiv_const_smul_field (2 : ℝ)
    rw [h1, h2]
    simp only [Pi.smul_apply, smul_apply, smul_eq_mul]
    ring
  rw [hfun, hlevi]
  by_cases hw : w = 0
  · subst hw
    simp [ReciprocityTheory.AnForm.levi]
  · exact mul_nonneg (by norm_num) (hpos x j y hy' w hw).le

end GlobalTheory.CompanionTheory.Ar.Giv.Mix.TwicePos
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PshDoublePositivePotentialStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psh_double_positive_potential : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (Θ : LocPot X), IsPotential A Θ → IsPosPot A Θ → IsPsh A (Θ + LocPot.ofFun (fun _ => (0 : ℝ)) + Θ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Mix.TwicePos.isPsh_add_zero_add | exact GlobalTheory.CompanionTheory.Ar.Giv.Mix.TwicePos.isPsh_add_zero_add | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Mix.TwicePos.isPsh_add_zero_add <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightUniformOnCompact
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightUniformOnCompact
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix

theorem tendstoUniformlyOn_regWeight_of_isCompact_subset_Yo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Xo : Set ((Σ k, ι k) → ℂ)) (B : HermLine ι) (S : LogLogRegularisationSetting M Xo B), S.IsTied → ∀ K' ⊆ S.R.Yo, IsCompact K' → TendstoUniformlyOn S.regWeight S.R.ph (𝓝[>] 0) K' := by
  intro K _ ι _ P n M Xo B S hS K' hK' hc
  have hYo : IsOpen S.R.Yo := (GlobalTheory.T.regular_chart_data_properties n M.Xc M.atlas S.R).1
  rw [← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hc]
  intro u hu x hx
  obtain ⟨j, hj⟩ := M.atlas.cover x
  have hO : IsOpen ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' S.R.Yo) :=
    (M.atlas.chart j).isOpen_inter_preimage_symm hYo
  have hy : M.atlas.chart j x ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' S.R.Yo :=
    ⟨(M.atlas.chart j).map_source hj, by
      simpa [Set.mem_preimage, (M.atlas.chart j).left_inv hj] using hK' hx⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO _ hy
  have hsub : Metric.closedBall (M.atlas.chart j x) (ε / 2) ⊆
      (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' S.R.Yo :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hU := (GlobalTheory.T.regularized_weight_tendsto_C2 K ι P n M Xo B S hS j _ hsub (isCompact_closedBall _ _)).1
  refine ⟨(M.atlas.chart j).source ∩ (M.atlas.chart j) ⁻¹' Metric.ball (M.atlas.chart j x) (ε / 2),
    mem_nhdsWithin_of_mem_nhds (((M.atlas.chart j).isOpen_inter_preimage Metric.isOpen_ball).mem_nhds
      ⟨hj, by simp [hε]⟩), ?_⟩
  filter_upwards [hU u hu] with t ht y hy'
  have h := ht (M.atlas.chart j y) (Metric.ball_subset_closedBall hy'.2)
  simpa [Function.comp, (M.atlas.chart j).left_inv hy'.1] using h

end GlobalTheory.CompanionTheory.Ar.Giv.Mix
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightUniformOnCompactStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularized_weight_uniform_on_compact : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Xo : Set ((Σ k, ι k) → ℂ)) (B : HermLine ι) (S : LogLogRegularisationSetting M Xo B), S.IsTied → ∀ K' ⊆ S.R.Yo, IsCompact K' → TendstoUniformlyOn S.regWeight S.R.ph (𝓝[>] 0) K' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Mix.tendstoUniformlyOn_regWeight_of_isCompact_subset_Yo | exact GlobalTheory.CompanionTheory.Ar.Giv.Mix.tendstoUniformlyOn_regWeight_of_isCompact_subset_Yo | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Mix.tendstoUniformlyOn_regWeight_of_isCompact_subset_Yo <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TopMixedLimitOfResolution
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

namespace Mix

section
variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

def GoodAt (X : ComponentSetting D O Lt) (B : ℕ) (Θ : LocPot X.M.Xc) (C₁ t : ℝ) : Prop :=
  IsSmoothHerm (muReg X.H X.S B t) ∧ X.M.atlas.Smooth (X.S.regWeight t) ∧
    (∀ x ∈ X.S.R.Yo, X.S.R.ph x ≤ X.S.regWeight t x ∧ X.S.regWeight t x ≤ C₁) ∧
    IsPsh X.M.atlas (X.S.R.th + LocPot.ofFun (X.S.regWeight t) + Θ)

theorem tendstoUniformlyOn_const' {α β : Type*} [UniformSpace β] (F : α → β) (s : Set α) :
    TendstoUniformlyOn (fun _ : ℝ => F) F (𝓝[>] 0) s := fun _ hu =>
  Eventually.of_forall fun _ _ _ => mem_uniformity_of_eq hu rfl

theorem regWeight_bound (X : ComponentSetting D O Lt) {C₁ v : ℝ} {x : X.M.Xc} (hx : x ∈ X.S.R.Yo)
    (h1 : X.S.R.ph x ≤ v) (h2 : v ≤ C₁) :
    |v| ≤ (|C₁| + |X.S.R.Clog|) + (|C₁| + |X.S.R.Clog|) * Real.log (X.S.R.r x) := by
  have hr : 0 ≤ Real.log (X.S.R.r x) := Real.log_nonneg (X.S.R.one_le_r x hx)
  have h3 := X.S.R.ph_ge x hx
  have h4 : X.S.R.Clog * Real.log (X.S.R.r x) ≤ |X.S.R.Clog| * Real.log (X.S.R.r x) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hr
  have h5 : |C₁| * 0 ≤ |C₁| * Real.log (X.S.R.r x) := mul_le_mul_of_nonneg_left hr (abs_nonneg _)
  have h6 : 0 ≤ |X.S.R.Clog| * Real.log (X.S.R.r x) := mul_nonneg (abs_nonneg _) hr
  have h7 := le_abs_self C₁
  have h8 := abs_nonneg C₁
  have h9 := abs_nonneg X.S.R.Clog
  rw [abs_le]
  constructor <;> nlinarith

theorem log_vert_prod (M : XModel D) (U : Set M.Xc) (σ : M.Xc → (Σ k, ι k) → ℂ) (hU : IsOpen U)
    (hσ : ∀ y ∈ U, σ y ∈ mcPts (mCoordIdeal D.y)) (hh : ∀ q, M.atlas.HoloOn U fun y => σ y q) {y₀ : M.Xc}
    (hy₀ : y₀ ∈ U) (s : Finset ℕ) (hs : s ⊆ D.S) :
    ∃ V : Set M.Xc, IsOpen V ∧ y₀ ∈ V ∧ V ⊆ U ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn V G ∧
      ∀ y ∈ V, Real.log (∏ p ∈ s, D.vertFactor p (σ y)) = (G y).re := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨U, hU, hy₀, subset_rfl, fun _ => 0, fun _ => analyticOnNhd_const, fun y _ => by simp⟩
  | insert p s hp ih =>
    have hpS : p ∈ D.S := hs (Finset.mem_insert_self p s)
    obtain ⟨V₁, hV₁, hy₁, hVU₁, G₁, hG₁, hl₁⟩ :=
      GlobalTheory.T.local_section_vertical_factor II Ψ K ι Ω E D p M U σ hpS hU hσ hh y₀ hy₀
    obtain ⟨V₂, hV₂, hy₂, hVU₂, G₂, hG₂, hl₂⟩ := ih fun q hq => hs (Finset.mem_insert_of_mem hq)
    refine ⟨V₁ ∩ V₂, hV₁.inter hV₂, ⟨hy₁, hy₂⟩, fun y hy => hVU₁ hy.1, fun y => G₁ y + G₂ y, fun j => ?_,
      fun y hy => ?_⟩
    · exact ((hG₁ j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left))).add
        ((hG₂ j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_right)))
    · have hz := hσ y (hVU₁ hy.1)
      have hpos : ∀ q ∈ D.S, 0 < D.vertFactor q (σ y) := fun q hq =>
        VertFactorPos.proof II Ψ K ι Ω E D q hq _ hz
      rw [Finset.prod_insert hp, Real.log_mul (hpos p hpS).ne'
        (Finset.prod_pos fun q hq => hpos q (hs (Finset.mem_insert_of_mem hq))).ne', hl₁ y hy.1, hl₂ y hy.2,
        Complex.add_re]

theorem reg_rel (X : ComponentSetting D O Lt) (B : ℕ) (t : ℝ) (x : X.M.Xc) :
    ∀ y₀ ∈ (X.S.R.th + LocPot.ofFun (X.S.regWeight t)).U x ∩ Set.univ, ∃ U : Set X.M.Xc, IsOpen U ∧ y₀ ∈ U ∧
      U ⊆ (X.S.R.th + LocPot.ofFun (X.S.regWeight t)).U x ∩ Set.univ ∧ ∃ s : X.M.Xc → (Σ k, ι k) → ℂ,
        (∀ y' ∈ U, s y' ∈ mcPts (mCoordIdeal D.y) ∧ X.M.proj (s y') = y') ∧
        (∀ p, X.M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : X.M.Xc → ℂ, X.M.atlas.HoloOn U G ∧
          ∀ y' ∈ U, (X.S.R.th + LocPot.ofFun (X.S.regWeight t)).φ x y' -
            Real.log ((muReg X.H X.S B t).h (s y')) = (G y').re := by
  intro y₀ hy
  obtain ⟨U₀, hU₀, hy₀, hsub, s, hs, hh, G₀, hG₀, hrel⟩ := X.S.th_ref x y₀ hy.1.1
  obtain ⟨V, hV, hyV, hVU, Gv, hGv, hlog⟩ := log_vert_prod X.M U₀ s hU₀ (fun y h => (hs y h).1) hh hy₀
    (D.SB B) (Finset.filter_subset _ _)
  refine ⟨V, hV, hyV, fun y h => ⟨⟨hsub (hVU h), trivial⟩, trivial⟩, s, fun y h => hs y (hVU h),
    fun p j => (hh p j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hVU)), fun y => G₀ y - Gv y,
    fun j => ((hG₀ j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hVU))).sub (hGv j), fun y' hy' => ?_⟩
  have hz := (hs y' (hVU hy')).1
  have hvp : 0 < ∏ p ∈ D.SB B, D.vertFactor p (s y') :=
    Finset.prod_pos fun p hp => VertFactorPos.proof II Ψ K ι Ω E D p (Finset.mem_filter.1 hp).1 _ hz
  have h1 := hrel y' (hVU hy')
  have h2 := hlog y' hy'
  have hproj := (hs y' (hVU hy')).2
  show X.S.R.th.φ x y' + X.S.regWeight t y' - _ = _
  rw [GlobalTheory.T.regularized_hodge_metric_formula II Ψ K ι Ω E D O Lt X B t (s y') hz, Real.log_mul
    (mul_pos (X.S.ref.pos _ hz.1) (Real.exp_pos _)).ne' hvp.ne', Real.log_mul (X.S.ref.pos _ hz.1).ne'
    (Real.exp_pos _).ne', Real.log_exp, hproj, h2, Complex.sub_re]
  linarith

theorem term_tendsto (X : ComponentSetting D O Lt) (B : ℕ) (Θ : LocPot X.M.Xc) (C₁ t₀ : ℝ) (k i : ℕ)
    (hΘ : IsPotential X.M.atlas Θ) (hΘp : IsPosPot X.M.atlas Θ)
    (hrel : ∀ x, ∀ y₀ ∈ Θ.U x ∩ Set.univ, ∃ U : Set X.M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ Θ.U x ∩ Set.univ ∧
      ∃ s : X.M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (mCoordIdeal D.y) ∧ X.M.proj (s y') = y') ∧
        (∀ p, X.M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : X.M.Xc → ℂ, X.M.atlas.HoloOn U G ∧
          ∀ y' ∈ U, Θ.φ x y' - (fun z => Real.log (D.A'.h z)) (s y') = (G y').re)
    (hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), GoodAt X B Θ C₁ t) (h₀ : GoodAt X B Θ C₁ t₀) :
    ∃ l : ℝ, Tendsto (fun t => ptsIntegral (mCoordIdeal D.y)
      (pot (mixWord (n := D.n) (muReg X.H X.S B t) (muReg X.H X.S B t₀) D.A' k i))
      (logRatio (muReg X.H X.S B t) (muReg X.H X.S B t₀))) (𝓝[>] 0) (𝓝 l) := by
  classical
  set R := X.S.R with hR
  set φ := X.S.regWeight with hφ
  set b := |C₁| + |R.Clog| with hb
  have hb0 : 0 ≤ b := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hrpos : ∀ x ∈ R.Yo, 0 ≤ Real.log (R.r x) := fun x hx => Real.log_nonneg (R.one_le_r x hx)
  have hth : IsPotential X.M.atlas R.th := R.th_pot
  let Pp : Fin D.n → LocPot X.M.Xc := fun j => if (j : ℕ) < i ∨ (j : ℕ) + 1 < k then R.th else Θ
  let f : Fin D.n → X.M.Xc → ℝ := fun j =>
    if (j : ℕ) < i then R.ph else if (j : ℕ) + 1 < k then φ t₀ else fun _ => 0
  let fT : Fin D.n → ℝ → X.M.Xc → ℝ := fun j t =>
    if (j : ℕ) < i then φ t else if (j : ℕ) + 1 < k then φ t₀ else fun _ => 0
  have hcases : ∀ j : Fin D.n, ((j : ℕ) < i ∧ Pp j = R.th ∧ f j = R.ph ∧ ∀ t, fT j t = φ t) ∨
      (¬ (j : ℕ) < i ∧ (j : ℕ) + 1 < k ∧ Pp j = R.th ∧ f j = φ t₀ ∧ ∀ t, fT j t = φ t₀) ∨
      (¬ (j : ℕ) < i ∧ ¬ (j : ℕ) + 1 < k ∧ Pp j = Θ ∧ f j = (fun _ => 0) ∧ ∀ t, fT j t = fun _ => 0) := by
    intro j
    by_cases h1 : (j : ℕ) < i
    · exact Or.inl ⟨h1, by simp [Pp, h1], by simp [f, h1], fun t => by simp [fT, h1]⟩
    · by_cases h2 : (j : ℕ) + 1 < k
      · exact Or.inr (Or.inl ⟨h1, h2, by simp [Pp, h2], by simp [f, h1, h2], fun t => by simp [fT, h1, h2]⟩)
      · exact Or.inr (Or.inr ⟨h1, h2, by simp [Pp, h1, h2], by simp [f, h1, h2], fun t => by simp [fT, h1, h2]⟩)
  have hbd' : ∀ x ∈ R.Yo, ∀ v, R.ph x ≤ v → v ≤ C₁ → |v| ≤ b + b * Real.log (R.r x) :=
    fun x hx v h1 h2 => regWeight_bound X hx h1 h2
  have hbd : ∀ x ∈ R.Yo, ∀ v, R.ph x ≤ v → v ≤ C₁ → |v| ≤ 2 * b + 2 * b * Real.log (R.r x) ∧ v ≤ 2 * b := by
    intro x hx v h1 h2
    have h3 := hbd' x hx v h1 h2
    have h4 := mul_nonneg hb0 (hrpos x hx)
    have h5 : C₁ ≤ b := (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
    constructor <;> nlinarith
  have hsm0 : X.M.atlas.Smooth (fun _ : X.M.Xc => (0 : ℝ)) := fun _ => contDiffOn_const
  have hYo : IsOpen R.Yo := (GlobalTheory.T.regular_chart_data_properties D.n X.M.Xc X.M.atlas R).1
  refine GlobalTheory.T.mixed_integral_limit_on_model K ι (mCoordIdeal D.y) D.n X.M R Θ Pp f fT (fun x => φ t₀ x - R.ph x)
    (fun t x => φ t₀ x - φ t x) (2 * b)
    (fun t => mixWord (n := D.n) (muReg X.H X.S B t) (muReg X.H X.S B t₀) D.A' k i)
    (fun t => logRatio (muReg X.H X.S B t) (muReg X.H X.S B t₀)) D.arith hΘ hΘp ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j
    rcases hcases j with ⟨-, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> rw [h]
    · exact hth
    · exact hth
    · exact hΘ
  · intro j
    rcases hcases j with ⟨-, -, h, -⟩ | ⟨-, -, -, h, -⟩ | ⟨-, -, -, h, -⟩ <;> rw [h]
    · exact R.ph_smooth
    · exact fun c => (h₀.2.1 c).mono (fun y hy => ⟨hy.1, Set.mem_univ _⟩)
    · exact fun c => contDiffOn_const
  · filter_upwards [hev] with t ht j
    rcases hcases j with ⟨-, hP, -, hT⟩ | ⟨-, -, hP, -, hT⟩ | ⟨-, -, hP, -, hT⟩ <;> rw [hP, hT t]
    · exact ⟨ht.2.1, ht.2.2.2, fun x hx => hbd x hx _ (ht.2.2.1 x hx).1 (ht.2.2.1 x hx).2⟩
    · exact ⟨h₀.2.1, h₀.2.2.2, fun x hx => hbd x hx _ (h₀.2.2.1 x hx).1 (h₀.2.2.1 x hx).2⟩
    · refine ⟨hsm0, GlobalTheory.T.psh_double_positive_potential _ _ _ _ hΘ hΘp, fun x hx => ?_⟩
      have := hrpos x hx
      have h2 : 0 ≤ b * Real.log (R.r x) := mul_nonneg hb0 this
      simp only [abs_zero]
      constructor <;> nlinarith
  · intro j c K' hK' hc
    rcases hcases j with ⟨-, -, hf, hT⟩ | ⟨-, -, -, hf, hT⟩ | ⟨-, -, -, hf, hT⟩ <;> simp only [hT, hf]
    · exact GlobalTheory.T.regularized_weight_tendsto_C2 K ι (mCoordIdeal D.y) D.n X.M D.Xo (muLine X.H) X.S X.S_tied c K' hK' hc
    · exact ⟨tendstoUniformlyOn_const' _ _, tendstoUniformlyOn_const' _ _, tendstoUniformlyOn_const' _ _⟩
    · exact ⟨tendstoUniformlyOn_const' _ _, tendstoUniformlyOn_const' _ _, tendstoUniformlyOn_const' _ _⟩
  · filter_upwards [hev] with t ht
    refine ⟨fun c => (h₀.2.1 c).sub (ht.2.1 c), fun x hx => ?_⟩
    have h1 := hbd' x hx _ (h₀.2.2.1 x hx).1 (h₀.2.2.1 x hx).2
    have h2 := hbd' x hx _ (ht.2.2.1 x hx).1 (ht.2.2.1 x hx).2
    have h3 := abs_sub (φ t₀ x) (φ t x)
    nlinarith
  · intro K' hK' hc
    have hU := GlobalTheory.T.regularized_weight_uniform_on_compact K ι (mCoordIdeal D.y) D.n X.M D.Xo (muLine X.H) X.S X.S_tied K' hK' hc
    rw [Metric.tendstoUniformlyOn_iff] at hU ⊢
    intro ε hε
    filter_upwards [hU ε hε] with t ht x hx
    show dist (φ t₀ x - R.ph x) (φ t₀ x - φ t x) < ε
    rw [Real.dist_eq, sub_sub_sub_cancel_left, abs_sub_comm, ← Real.dist_eq]
    exact ht x hx
  · filter_upwards [hev] with t ht j x y₀ hy
    rcases hcases j with ⟨h1, hP, -, hT⟩ | ⟨h1, h2, hP, -, hT⟩ | ⟨h1, h2, hP, -, hT⟩
    · have hw : mixWord (n := D.n) (muReg X.H X.S B t) (muReg X.H X.S B t₀) D.A' k i j = muReg X.H X.S B t := by
        simp [mixWord, h1]
      simp only [hP, hT, hw] at hy ⊢
      exact reg_rel X B t x y₀ hy
    · have hw : mixWord (n := D.n) (muReg X.H X.S B t) (muReg X.H X.S B t₀) D.A' k i j = muReg X.H X.S B t₀ := by
        simp [mixWord, h1, h2]
      simp only [hP, hT, hw] at hy ⊢
      exact reg_rel X B t₀ x y₀ hy
    · have hw : mixWord (n := D.n) (muReg X.H X.S B t) (muReg X.H X.S B t₀) D.A' k i j = D.A' := by
        simp [mixWord, h1, h2]
      simp only [hP, hT, hw] at hy ⊢
      obtain ⟨U, hU, hyU, hsub, s, hs, hh, G, hG, hrelG⟩ := hrel x y₀ ⟨hy.1.1, trivial⟩
      refine ⟨U, hU, hyU, fun y hy' => ⟨⟨(hsub hy').1, trivial⟩, trivial⟩, s, hs, hh, G, hG, fun y' hy' => ?_⟩
      have := hrelG y' hy'
      show Θ.φ x y' + 0 - _ = _
      simpa using this
  · filter_upwards with t z hz
    have hvp : ∀ u : ℝ, 0 < ∏ p ∈ D.SB B, D.vertFactor p z := fun _ =>
      Finset.prod_pos fun p hp => VertFactorPos.proof II Ψ K ι Ω E D p (Finset.mem_filter.1 hp).1 z hz
    have hlog : ∀ u : ℝ, Real.log ((muReg X.H X.S B u).h z) = Real.log (X.S.ref.h z) + φ u (X.M.proj z) +
        Real.log (∏ p ∈ D.SB B, D.vertFactor p z) := by
      intro u
      rw [GlobalTheory.T.regularized_hodge_metric_formula II Ψ K ι Ω E D O Lt X B u z hz, Real.log_mul (mul_pos (X.S.ref.pos z hz.1) (Real.exp_pos _)).ne'
        (hvp 0).ne', Real.log_mul (X.S.ref.pos z hz.1).ne' (Real.exp_pos _).ne', Real.log_exp]
    unfold logRatio
    rw [if_pos hz.1, hlog, hlog]
    ring

end

end Mix


open Mix in
theorem mixed_limit : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → TopNMixedLimit.Statement := by
  intro _ II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B hII _ k hk
  obtain ⟨Θ, hΘ, hrel⟩ := GlobalTheory.T.local_holomorphic_section_of_potential K ι (mCoordIdeal D.y) D.n X.M D.A' D.A'_pos.1
  have hΘp := GlobalTheory.T.local_section_of_potential_on_model II Ψ K ι Ω E D X.M Θ hΘ hrel
  obtain ⟨-, ⟨C₁, hC₁⟩, hpsh⟩ := GlobalTheory.T.regularized_weight_psh_and_bounds K ι (mCoordIdeal D.y) D.n X.M D.Xo (muLine X.H) X.S Θ X.S_tied hΘ hΘp
  have hsm : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (muReg X.H X.S B t) :=
    MuRegSmooth.proof HermExtend.proof (ProjSmoothAlong.proof HoloInjDerivInj.proof GlobalTheory.T.local_orbit_chart_statement_holds)
      (VertFactorSmooth.proof VertFactorPos.proof) VertFactorPos.proof II Ψ K ι Ω E D O Lt X B
  have hone : Θ.rsmul 1 = Θ := by
    cases Θ
    simp [LocPot.rsmul]
  have hp1 := hpsh 1 one_pos
  rw [hone] at hp1
  have hgood : ∀ᶠ t in 𝓝[>] (0 : ℝ), GoodAt X B Θ C₁ t := by
    filter_upwards [hsm, hC₁, hp1] with t h1 h2 h3
    exact ⟨h1, h2.1, h2.2, h3⟩
  obtain ⟨t₀, h₀⟩ := hgood.exists
  have hterm := fun i => term_tendsto X B Θ C₁ t₀ k i hΘ hΘp hrel hgood h₀
  choose l hl using hterm
  refine ⟨X.mixN B k t₀ - ∑ i ∈ Finset.range k, l i, ?_⟩
  have hlim := (tendsto_const_nhds (x := X.mixN B k t₀)).sub (tendsto_finsetSum (Finset.range k) fun i _ => hl i)
  refine hlim.congr' ?_
  filter_upwards [hgood] with t ht
  have ha : ∀ u, (muReg X.H X.S B u).a = muTwDeg X.H B := fun u => smoothRep_a _ _
  have hT := GlobalTheory.T.intersection_number_telescoping K ι (II K ι) (hII K ι) (mCoordIdeal D.y) D.n (muReg X.H X.S B t) (muReg X.H X.S B t₀) D.A' k
    D.arith ht.1 h₀.1 D.A'_pos.1 ((ha t).trans (ha t₀).symm) (by omega)
  have hm : ∀ u, X.mixN B k u = II K ι (mCoordIdeal D.y) (D.n + 1)
      (fun j => if (j : ℕ) < k then muReg X.H X.S B u else D.A') := fun _ => rfl
  rw [hm t, hm t₀]
  linarith

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TopMixedLimitOfResolutionStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_mixed_limit_of_resolution : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GroundTheory.Heights₂.Heights.LowerBoundFree.TopNMixedLimit.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.mixed_limit | exact GlobalTheory.CompanionTheory.Ar.Giv.mixed_limit | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.mixed_limit <;> assumption)
end
