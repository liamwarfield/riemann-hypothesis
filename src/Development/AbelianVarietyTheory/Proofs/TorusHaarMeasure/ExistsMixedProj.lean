module

public import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContinuousInvLeadingBlockEntry
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MulSgnMatMulConjTranspose

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsMixedProj
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Up.PoleValue

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

variable {X : Data E r} {x0 x1 : Frame X.Ψ r}

private theorem det_mat_cpt_ne_zero_iff_det_nmat (h : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) :
    (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) τ).det ≠ 0 ↔ (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat X z) τ).det ≠ 0 := by
  have hx := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IW.orth_mem_dom X x0 h
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG at hx
  have hdet := (Set.mem_setOf_eq ▸ hx) τ |>.1
  rw [show _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat X z) τ from rfl,
    Matrix.det_mul]
  exact ⟨fun hne ↦ right_ne_zero_of_mul hne, fun hne ↦ mul_ne_zero hdet hne⟩

private theorem dmin_cpt_eq_of_isOrth (h0 : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) (h1 : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x1)
    (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) (i : Fin (r + 1)) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x1 z) τ i = _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) τ i := by
  have g0 : ∀ τ : X.Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ) =
      Matrix.diagonal fun a : Fin r ↦ ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 ↑a : ℝ) : ℂ) := h0
  have g1 : ∀ τ : X.Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x1 τ) =
      Matrix.diagonal fun a : Fin r ↦ ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 ↑a : ℝ) : ℂ) := h1
  have hmat : ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r,
      _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat X z) τ := fun _ ↦ rfl
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin
  rw [hmat, hmat, _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_mul, _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_mul, g0, g1]

theorem _root_.GlobalTheory.Up.PoleValue.OmF_eq (h0 : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) (h1 : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x1) :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x1 = _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x0 := by
  ext z
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG
  simp only [Set.mem_setOf_eq, det_mat_cpt_ne_zero_iff_det_nmat h0, det_mat_cpt_ne_zero_iff_det_nmat h1,
    dmin_cpt_eq_of_isOrth h0 h1]

theorem _root_.GlobalTheory.Up.PoleValue.rhF_eq (h0 : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) (h1 : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x1) :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.rhF X x1 = _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.rhF X x0 := by
  funext z
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.rhF
  simp only [dmin_cpt_eq_of_isOrth h0 h1]

theorem _root_.GlobalTheory.Up.PoleValue.muF_eq (h0 : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) (h1 : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x1) :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x1 = _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF
  rw [_root_.GlobalTheory.Up.PoleValue.OmF_eq h0 h1]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF
  simp only [dmin_cpt_eq_of_isOrth h0 h1]

end GlobalTheory.Up.PoleValue

namespace GlobalTheory.Up

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem _root_.GlobalTheory.Up.polePoint_holds : _root_.GlobalTheory.Up.PolePoint (E := E) := by
  unfold _root_.GlobalTheory.Up.PolePoint
  intro r X ρ c hdim hρ hc
  set d := _root_.GlobalTheory.Up.dimX X with hd
  by_cases hex : ∃ x0, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0
  swap
  · exact ⟨1, one_pos, fun x1 h1 ↦ absurd ⟨x1, h1⟩ hex⟩
  obtain ⟨x0, h0⟩ := hex
  obtain ⟨ε, hε, m, hm, hdens⟩ : ∃ ε > 0, ∃ m > 0,
      ∀ w ∈ Metric.ball (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) ε, m ≤ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x0 w := by
    have hc' : ∀ τ i, Continuous fun w ↦ _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 w) τ i :=
      fun τ i ↦ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IW.dmin_cpt_cd X x0 τ i).continuous
    have hne : ∀ τ i, _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 0) τ i ≠ 0 := by
      intro τ i
      rw [_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IW.cpt_zero]
      exact _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IW.dmin_ne_zero X (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IW.orth_mem_dom X x0 h0) τ i
    have hcont : ContinuousAt (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x0) 0 := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF
      refine tendsto_finsetProd _ fun τ _ ↦ tendsto_finsetProd _ fun i _ ↦ ?_
      exact ((hc' τ _).continuousAt.norm).zpow₀ _ (Or.inl (norm_ne_zero_iff.2 (hne τ _)))
    have hpos : 0 < _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x0 0 := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF
      exact Finset.prod_pos fun τ _ ↦ Finset.prod_pos fun i _ ↦
        zpow_pos (norm_pos_iff.2 (hne τ _)) _
    obtain ⟨ε, hε, hball⟩ :=
      Metric.eventually_nhds_iff_ball.1 (hcont.eventually (lt_mem_nhds (half_lt_self hpos)))
    exact ⟨ε, hε, _, half_pos hpos, fun w hw ↦ (hball w hw).le⟩
  obtain ⟨hnonneg, ρ1, C, hρ1, hquad⟩ := _root_.GlobalTheory.SharpGradient.rhF_sharp_gradient r X x0 h0
  obtain ⟨L, hLsurj, hLnorm⟩ : ∃ L : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) →L[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V d,
      Function.Surjective L ∧ ∀ z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖L z‖ ^ 2 =
        ∑ e : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X, if (e.2.1.2 : ℕ) < X.p0 ∧ X.p0 ≤ (e.2.1.1 : ℕ) then
          ‖z.ofLp ((Fintype.equivFin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X)) e)‖ ^ 2 else 0 := by
    let σ := Fintype.equivFinOfCardEq (_root_.GlobalTheory.Up.card_mixedEnt X)
    let f : Fin d → Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) := fun k ↦ Fintype.equivFin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X) (σ.symm k).1
    have hf : Function.Injective f := fun a b hab ↦
      σ.symm.injective (Subtype.ext ((Fintype.equivFin _).injective hab))
    let L₀ : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) →ₗ[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V d :=
      (WithLp.linearEquiv 2 ℂ (Fin d → ℂ)).symm.toLinearMap ∘ₗ LinearMap.funLeft ℂ ℂ f ∘ₗ
        (WithLp.linearEquiv 2 ℂ (Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ)).toLinearMap
    refine ⟨LinearMap.toContinuousLinearMap L₀, ?_, ?_⟩
    · intro y
      obtain ⟨g, hg⟩ := LinearMap.funLeft_surjective_of_injective ℂ ℂ f hf
        (WithLp.linearEquiv 2 ℂ (Fin d → ℂ) y)
      refine ⟨(WithLp.linearEquiv 2 ℂ (Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ)).symm g, ?_⟩
      simp [L₀, hg]
    · intro z
      rw [EuclideanSpace.norm_sq_eq]
      change ∑ k, ‖z.ofLp ((Fintype.equivFin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X)) (σ.symm k).1)‖ ^ 2 = _
      rw [← Finset.sum_filter]
      rw [Equiv.sum_comp σ.symm (fun x ↦ ‖z.ofLp ((Fintype.equivFin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X)) x.1)‖ ^ 2)]
      rw [← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
  set ρ' := min ρ (min ρ1 ε) with hρ'
  have hρ'pos : 0 < ρ' := lt_min hρ (lt_min hρ1 hε)
  obtain ⟨δ', hδ', hball, hblow⟩ := _root_.ReciprocityTheory.L2DbarEstimates.Y.ap_local_blowup (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) d hdim _root_.ReciprocityTheory.L2DbarEstimates.mv (_root_.ReciprocityTheory.L2DbarEstimates.mvInt d)
    (Metric.ball 0 ρ') Metric.isOpen_ball L L.differentiableOn 0
    (Metric.mem_ball_self hρ'pos) (map_zero L) (by rw [L.fderiv]; exact hLsurj)
  set K := max C 0 + 1 with hK
  have hKpos : 0 < K := by positivity
  obtain ⟨τ0, hτ0, hτ⟩ := hblow (K ^ (d : ℝ) / (c * m))
  refine ⟨τ0, hτ0, fun x1 h1 δ hδ hδτ u hu ↦ ?_⟩
  rw [_root_.GlobalTheory.Up.PoleValue.OmF_eq h0 h1] at hu
  rw [_root_.GlobalTheory.Up.PoleValue.rhF_eq h0 h1,
    _root_.GlobalTheory.Up.PoleValue.muF_eq h0 h1]
  have hsub : Metric.ball (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) δ' ⊆ Metric.ball 0 ρ' :=
    Metric.ball_subset_closedBall.trans hball
  have hmem : ∀ v ∈ Metric.ball (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) δ',
      ‖v‖ < ρ ∧ ‖v‖ < ρ1 ∧ ‖v‖ < ε := by
    intro v hv
    have h := hsub hv
    rw [Metric.mem_ball, dist_zero_right] at h
    exact ⟨h.trans_le (min_le_left _ _), h.trans_le ((min_le_right _ _).trans (min_le_left _ _)),
      h.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩
  have hu' : DifferentiableOn ℂ u (Metric.ball 0 δ') := by
    refine hu.mono fun v hv ↦ ⟨?_, (hquad v (hmem v hv).2.1).1⟩
    rw [Metric.mem_ball, dist_zero_right]
    exact (hmem v hv).1
  have key := hτ δ hδ hδτ u hu'
  have hμ : ENNReal.ofReal m • volume.restrict (Metric.ball (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) δ') ≤
      (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0).restrict (Metric.ball 0 ρ) := by
    rw [Measure.le_iff]
    intro s hs
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hs, Measure.restrict_apply hs]
    unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.muF
    rw [withDensity_apply _ (hs.inter measurableSet_ball),
      Measure.restrict_restrict (hs.inter measurableSet_ball)]
    calc ENNReal.ofReal m * volume (s ∩ Metric.ball 0 δ')
        = ∫⁻ _ in s ∩ Metric.ball 0 δ', ENNReal.ofReal m := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ a in s ∩ Metric.ball 0 δ', ENNReal.ofReal (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x0 a) :=
          setLIntegral_mono' (hs.inter measurableSet_ball) fun a ha ↦
            ENNReal.ofReal_le_ofReal (hdens a (by
              rw [Metric.mem_ball, dist_zero_right]; exact (hmem a ha.2).2.2))
      _ ≤ _ := by
          refine lintegral_mono_set fun a ha ↦ Set.mem_inter (Set.mem_inter ha.1 ?_)
            (hquad a (hmem a ha.2).2.1).1
          rw [Metric.mem_ball, dist_zero_right]
          exact (hmem a ha.2).1
  have hpt : ∀ v ∈ Metric.ball (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) δ',
      ENNReal.ofReal (K ^ (-(d : ℝ))) *
          ENNReal.ofReal (‖u v‖ ^ 2 * max (‖L v‖ ^ 2) δ ^ (-(d : ℝ))) ≤
        ENNReal.ofReal (‖u v‖ ^ 2 * (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.rhF X x0 v + δ) ^ (-(d : ℝ))) := by
    intro v hv
    have hvmem := (hquad v (hmem v hv).2.1).1
    have hw0 : 0 ≤ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.rhF X x0 v := (hnonneg v hvmem).1
    have hq := (hquad v (hmem v hv).2.1).2
    rw [← hLnorm v] at hq
    have ht : 0 ≤ ‖L v‖ ^ 2 := by positivity
    have hM : 0 < max (‖L v‖ ^ 2) δ := lt_max_of_lt_right hδ
    have hle : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.rhF X x0 v + δ ≤ K * max (‖L v‖ ^ 2) δ := by
      have h1 : C * ‖L v‖ ^ 2 ≤ max C 0 * max (‖L v‖ ^ 2) δ :=
        mul_le_mul (le_max_left _ _) (le_max_left _ _) ht (le_max_right _ _)
      rw [hK, add_mul, one_mul]
      linarith [le_max_right (‖L v‖ ^ 2) δ]
    have hpow : (K * max (‖L v‖ ^ 2) δ) ^ (-(d : ℝ)) ≤ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.rhF X x0 v + δ) ^ (-(d : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (add_pos_of_nonneg_of_pos hw0 hδ) hle
        (neg_nonpos.2 (Nat.cast_nonneg _))
    rw [Real.mul_rpow hKpos.le hM.le] at hpow
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hKpos.le _)]
    apply ENNReal.ofReal_le_ofReal
    calc K ^ (-(d : ℝ)) * (‖u v‖ ^ 2 * max (‖L v‖ ^ 2) δ ^ (-(d : ℝ)))
        = ‖u v‖ ^ 2 * (K ^ (-(d : ℝ)) * max (‖L v‖ ^ 2) δ ^ (-(d : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  calc ENNReal.ofReal (‖u 0‖ ^ 2)
      = ENNReal.ofReal c * (ENNReal.ofReal m * (ENNReal.ofReal (K ^ (-(d : ℝ))) *
          ENNReal.ofReal (K ^ (d : ℝ) / (c * m) * ‖u 0‖ ^ 2))) := by
        rw [← ENNReal.ofReal_mul, ← ENNReal.ofReal_mul, ← ENNReal.ofReal_mul]
        · congr 1
          rw [Real.rpow_neg hKpos.le]
          have hKd : 0 < K ^ (d : ℝ) := Real.rpow_pos_of_pos hKpos _
          field_simp
        all_goals positivity
    _ ≤ ENNReal.ofReal c * (ENNReal.ofReal m * (ENNReal.ofReal (K ^ (-(d : ℝ))) *
          ∫⁻ v in Metric.ball 0 δ', ENNReal.ofReal (‖u v‖ ^ 2 * max (‖L v‖ ^ 2) δ ^ (-(d : ℝ))))) := by
        gcongr
    _ = ENNReal.ofReal c * (ENNReal.ofReal m * ∫⁻ v in Metric.ball 0 δ',
          ENNReal.ofReal (K ^ (-(d : ℝ))) *
            ENNReal.ofReal (‖u v‖ ^ 2 * max (‖L v‖ ^ 2) δ ^ (-(d : ℝ)))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal c * (ENNReal.ofReal m * ∫⁻ v in Metric.ball 0 δ',
          ENNReal.ofReal (‖u v‖ ^ 2 * (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.rhF X x0 v + δ) ^ (-(d : ℝ)))) := by
        gcongr ENNReal.ofReal c * (ENNReal.ofReal m * ?_)
        exact setLIntegral_mono' Metric.isOpen_ball.measurableSet hpt
    _ = ENNReal.ofReal c * ∫⁻ v, ENNReal.ofReal (‖u v‖ ^ 2 * (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.rhF X x0 v + δ) ^ (-(d : ℝ)))
          ∂(ENNReal.ofReal m • volume.restrict (Metric.ball (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) δ')) := by
        rw [lintegral_smul_measure, smul_eq_mul]
    _ ≤ _ := by
        gcongr ENNReal.ofReal c * ?_
        exact lintegral_mono' hμ le_rfl

end GlobalTheory.Up
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContDiffAtLogMinorProd
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.PotentialTransfer

open Filter Matrix GlobalTheory.SharpGradient GlobalTheory.Up
open scoped ComplexOrder ComplexConjugate

section Matrices

variable {n p : ℕ}

def topT (h : p ≤ n) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  (g.submatrix (Fin.castLE h) (Fin.castLE h))ᵀ

def lowT (h : p ≤ n) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin p) (Fin n) ℂ :=
  Matrix.of fun a k => if (k : ℕ) < p then 0 else g k (Fin.castLE h a)

noncomputable def graphT (h : p ≤ n) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin p) (Fin n) ℂ :=
  (topT h g)⁻¹ * lowT h g

theorem leading_gram (h : p ≤ n) (g : Matrix (Fin n) (Fin n) ℂ) :
    (gᵀ * (Matrix.diagonal fun a : Fin n => ((sgn p (a : ℕ) : ℝ) : ℂ)) *
      g.map (starRingEnd ℂ)).submatrix (Fin.castLE h) (Fin.castLE h) =
      topT h g * (topT h g)ᴴ - lowT h g * (lowT h g)ᴴ := by
  ext a b
  have e2 : (topT h g * (topT h g)ᴴ) a b = ∑ k : Fin n, if (k : ℕ) < p then
      g k (Fin.castLE h a) * starRingEnd ℂ (g k (Fin.castLE h b)) else 0 := by
    rw [Matrix.mul_apply]
    refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun k hk => ?_)
      (fun k => ?_)
    · rw [if_neg]
      intro hlt
      exact hk ⟨⟨k, hlt⟩, Fin.ext rfl⟩
    · simp [topT, Matrix.conjTranspose_apply]
  rw [Matrix.sub_apply, e2, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal]
  by_cases hk : (k : ℕ) < p
  · simp [lowT, sgn, hk, Matrix.conjTranspose_apply]
  · simp [lowT, sgn, hk, Matrix.conjTranspose_apply]

theorem one_sub_graph (h : p ≤ n) (g : Matrix (Fin n) (Fin n) ℂ) (hd : (topT h g).det ≠ 0) :
    1 - graphT h g * (graphT h g)ᴴ =
      (topT h g)⁻¹ * (topT h g * (topT h g)ᴴ - lowT h g * (lowT h g)ᴴ) * ((topT h g)⁻¹)ᴴ := by
  have hu : IsUnit (topT h g).det := isUnit_iff_ne_zero.2 hd
  have h1 : (topT h g)⁻¹ * topT h g = 1 := Matrix.nonsing_inv_mul _ hu
  have h2 : (topT h g)ᴴ * ((topT h g)⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, h1, Matrix.one_mul, h2, graphT,
    Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem graph_posDef (h : p ≤ n) (g : Matrix (Fin n) (Fin n) ℂ) (hd : (topT h g).det ≠ 0)
    (hP : (topT h g * (topT h g)ᴴ - lowT h g * (lowT h g)ᴴ).PosDef) :
    (1 - graphT h g * (graphT h g)ᴴ).PosDef ∧
      (1 - graphT h g * (graphT h g)ᴴ).det.re =
        ‖(topT h g * (topT h g)ᴴ - lowT h g * (lowT h g)ᴴ).det‖ / ‖(topT h g).det‖ ^ 2 := by
  have hu : IsUnit (topT h g)⁻¹ := by
    rw [Matrix.isUnit_nonsing_inv_iff, Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.2 hd
  have hpd : (1 - graphT h g * (graphT h g)ᴴ).PosDef := by
    rw [one_sub_graph h g hd]
    exact (Matrix.IsUnit.posDef_star_right_conjugate_iff hu).2 hP
  refine ⟨hpd, ?_⟩
  rw [← ExF.norm_of_pos hpd.det_pos, one_sub_graph h g hd, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_conjTranspose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', norm_mul, norm_mul,
    norm_star, norm_inv]
  have : ‖(topT h g).det‖ ≠ 0 := norm_ne_zero_iff.2 hd
  field_simp

theorem contDiffAt_graph {m : ℕ} (h : p ≤ n) {g : V m → Matrix (Fin n) (Fin n) ℂ}
    (hg : ∀ a b, ContDiff ℂ ∞ fun y => g y a b) {z : V m} (hd : (topT h (g z)).det ≠ 0)
    (a : Fin p) (k : Fin n) : ContDiffAt ℂ ∞ (fun y => graphT h (g y) a k) z := by
  have ht : ∀ i j, ContDiff ℂ ∞ fun y => topT h (g y) i j := fun i j => hg _ _
  have e : (fun y => graphT h (g y) a k) = fun y => ∑ b, (((topT h (g y)).det)⁻¹ *
      ((topT h (g y)).updateRow b (Pi.single a 1)).det) * lowT h (g y) b k := by
    funext y
    simp [graphT, Matrix.inv_def, Matrix.mul_apply, Matrix.adjugate_apply, Ring.inverse_eq_inv']
  rw [e]
  refine ContDiffAt.sum fun b _ => ContDiffAt.mul (ContDiffAt.mul ?_ ?_) ?_
  · exact (ExhD.contDiff_det_of ht).contDiffAt.inv hd
  · refine (ExhD.contDiff_det_of fun i j => ?_).contDiffAt
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact contDiff_const
    · exact ht _ _
  · simp only [lowT, Matrix.of_apply]
    split_ifs
    · exact contDiffAt_const
    · exact (hg _ _).contDiffAt

end Matrices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
  {x1 x2 x : Frame X.Ψ r}

theorem det_topT_ne_zero (h2 : IsOrth X x2) (hx : x ∈ X.dom) (τ : X.Ψ) :
    (topT X.p0_le ((mat x2 τ)⁻¹ * mat x τ)).det ≠ 0 := by
  rw [topT, Matrix.det_transpose]
  exact lminor_inv_mul_ne_zero h2 hx τ

theorem gramPos_eq (h2 : IsOrth X x2) (x : Frame X.Ψ r) (τ : X.Ψ) :
    X.gramPos x τ = topT X.p0_le ((mat x2 τ)⁻¹ * mat x τ) * (topT X.p0_le ((mat x2 τ)⁻¹ * mat x τ))ᴴ -
      lowT X.p0_le ((mat x2 τ)⁻¹ * mat x τ) * (lowT X.p0_le ((mat x2 τ)⁻¹ * mat x τ))ᴴ := by
  have hu : IsUnit (mat x2 τ).det := isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X x2 h2 τ)
  rw [← leading_gram, ← h2 τ, ← FrameDegreeData.gram_mul, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  rfl

theorem graph_posDef_of_mem (h2 : IsOrth X x2) (hx : x ∈ X.dom) (τ : X.Ψ) :
    (1 - graphT X.p0_le ((mat x2 τ)⁻¹ * mat x τ) *
      (graphT X.p0_le ((mat x2 τ)⁻¹ * mat x τ))ᴴ).PosDef :=
  (graph_posDef _ _ (det_topT_ne_zero h2 hx τ) (gramPos_eq h2 x τ ▸ X.gramPos_posDef hx τ)).1

theorem rhX_eq_sum_graph (h2 : IsOrth X x2) (hx : x ∈ X.dom) :
    rhX X x2 x = ∑ τ, -Real.log (1 - graphT X.p0_le ((mat x2 τ)⁻¹ * mat x τ) *
      (graphT X.p0_le ((mat x2 τ)⁻¹ * mat x τ))ᴴ).det.re := by
  rw [rhX_eq_sum_log h2 hx]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [(graph_posDef _ _ (det_topT_ne_zero h2 hx τ) (gramPos_eq h2 x τ ▸ X.gramPos_posDef hx τ)).2,
    ← gramPos_eq h2 x τ, topT, Matrix.det_transpose]
  rfl

theorem contDiff_inv_mul_cpt (x1 x2 : Frame X.Ψ r) (τ : X.Ψ) (a b : Fin r) :
    ContDiff ℂ ∞ fun y : V (nd X) => ((mat x2 τ)⁻¹ * mat (cpt X x1 y) τ) a b := by
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun c _ => contDiff_const.mul (OntoB.cd_cpt_entry X x1 τ c b)

noncomputable def minorProd (X : Data E r) (x1 x2 : Frame X.Ψ r) (y : V (nd X)) : ℂ :=
  ∏ τ, lminor ((mat x2 τ)⁻¹ * mat (cpt X x1 y) τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩

theorem contDiff_minorProd (x1 x2 : Frame X.Ψ r) : ContDiff ℂ ∞ (minorProd X x1 x2) :=
  contDiff_prod fun τ _ => ExhD.contDiff_det_of fun _ _ => contDiff_inv_mul_cpt x1 x2 τ _ _

theorem minorProd_ne_zero (h2 : IsOrth X x2) {y : V (nd X)} (hy : y ∈ OmF X x1) :
    minorProd X x1 x2 y ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun τ _ => lminor_inv_mul_ne_zero h2 hy τ

theorem rhX_cpt_eq_add (h2 : IsOrth X x2) {y : V (nd X)} (hy : y ∈ OmF X x1) :
    rhX X x2 (cpt X x1 y) = rhF X x1 y + Real.log (Complex.normSq (minorProd X x1 x2 y)) := by
  rw [rhX_eq_sum h2 hy, minorProd, map_prod, Real.log_prod fun τ _ =>
    (Complex.normSq_pos.2 (lminor_inv_mul_ne_zero h2 hy τ)).ne']
  simp only [Complex.normSq_eq_norm_sq]
  rfl

theorem contDiffAt_log_minorProd (h2 : IsOrth X x2) {z : V (nd X)} (hz : z ∈ OmF X x1) :
    ContDiffAt ℝ ∞ (fun y => Real.log (Complex.normSq (minorProd X x1 x2 y))) z := by
  have hn : ContDiff ℝ ∞ fun y : V (nd X) => Complex.normSq (minorProd X x1 x2 y) := by
    simp only [Complex.normSq_eq_norm_sq]
    exact (contDiff_norm_sq ℝ).comp ((contDiff_minorProd x1 x2).restrict_scalars ℝ)
  exact (Real.contDiffAt_log.2 (Complex.normSq_pos.2 (minorProd_ne_zero h2 hz)).ne').comp z
    hn.contDiffAt

theorem rhX_cpt_eventuallyEq (h2 : IsOrth X x2) {z : V (nd X)} (hz : z ∈ OmF X x1) :
    (fun y => rhX X x2 (cpt X x1 y)) =ᶠ[𝓝 z]
      fun y => rhF X x1 y + Real.log (Complex.normSq (minorProd X x1 x2 y)) := by
  filter_upwards [(OntoB.isOpen_OmF X x1).mem_nhds hz] with y hy
  exact rhX_cpt_eq_add h2 hy

theorem contDiffAt_rhX_cpt (h2 : IsOrth X x2) {z : V (nd X)} (hz : z ∈ OmF X x1) :
    ContDiffAt ℝ ∞ (fun y => rhX X x2 (cpt X x1 y)) z :=
  ((OntoB.rhF_contDiffAt hz).add (contDiffAt_log_minorProd h2 hz)).congr_of_eventuallyEq
    (rhX_cpt_eventuallyEq h2 hz)

theorem leviO_rhX (h2 : IsOrth X x2) {z : V (nd X)} (hz : z ∈ OmF X x1) (ξ : Fin (nd X) → ℂ) :
    leviO X x1 (rhX X x2) z ξ = leviRh X x1 z ξ := by
  have e : (fun y => ((rhX X x2 (cpt X x1 y) : ℝ) : ℂ)) =ᶠ[𝓝 z]
      fun y => ((rhF X x1 y + Real.log (Complex.normSq (minorProd X x1 x2 y)) : ℝ) : ℂ) := by
    filter_upwards [rhX_cpt_eventuallyEq h2 hz] with y hy
    rw [hy]
  unfold leviO leviM leviRh
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr e ξ,
    ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_add
      ((OntoB.rhF_contDiffAt hz).of_le ExhE.two_le_infty)
      ((contDiffAt_log_minorProd h2 hz).of_le ExhE.two_le_infty) ξ,
    ExF.levi_logNormSq_zero _ (contDiff_minorProd x1 x2) z (minorProd_ne_zero h2 hz) ξ, add_zero]

theorem sharpAt_rhX_cpt (h2 : IsOrth X x2) {z : V (nd X)} (hz : z ∈ OmF X x1)
    (ξ : Fin (nd X) → ℂ) : SharpAt (fun y => rhX X x2 (cpt X x1 y)) z ξ := by
  choose U hU he using fun τ => exists_unitary_rows (graph_posDef_of_mem h2 hz τ)
  have hS : SharpAt (fun y => ∑ τ, ∑ a, -Real.log (1 - ∑ b, Complex.normSq
      (((U τ)ᴴ * graphT X.p0_le ((mat x2 τ)⁻¹ * mat (cpt X x1 y) τ)) a b))) z ξ := by
    refine sharpAt_sum' fun τ => sharpAt_sum fun a => ?_
    refine sharpAt_ball
      (g := fun b y => ((U τ)ᴴ * graphT X.p0_le ((mat x2 τ)⁻¹ * mat (cpt X x1 y) τ)) a b) ξ
      (fun b => ?_) (row_lt_one _ (hU τ) (graph_posDef_of_mem h2 hz τ) a)
    simp only [Matrix.mul_apply]
    exact (ContDiffAt.sum fun c _ => contDiffAt_const.mul
      (contDiffAt_graph X.p0_le (contDiff_inv_mul_cpt x1 x2 τ) (det_topT_ne_zero h2 hz τ) c b)).of_le
      ExhE.two_le_infty
  refine hS.of_minorant ((contDiffAt_rhX_cpt h2 hz).of_le ExhE.two_le_infty) ?_ ?_
  · filter_upwards [(OntoB.isOpen_OmF X x1).mem_nhds hz] with y hy
    rw [rhX_eq_sum_graph h2 hy]
    exact Finset.sum_le_sum fun τ _ => rows_le_neg_log_det _ (hU τ) (graph_posDef_of_mem h2 hy τ)
  · rw [rhX_eq_sum_graph h2 hz]
    exact Finset.sum_congr rfl fun τ _ => he τ

theorem potential_transfer : RhTr (E := E) := by
  intro r X x1 x2 _ h2
  refine ⟨fun z hz => (contDiffAt_rhX_cpt h2 hz).contDiffWithinAt, fun z hz =>
    ⟨rhX_nonneg h2 hz, fun ξ => ⟨leviO_rhX h2 hz ξ, ?_⟩⟩⟩
  rw [← leviO_rhX h2 hz ξ]
  exact (sharpAt_rhX_cpt h2 hz ξ).2.2.2

end GlobalTheory.PotentialTransfer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MuFSublevelLtTop
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.SublevelFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isClosed_isOrth {r : ℕ} (X : Data E r) : IsClosed {x : Frame X.Ψ r | IsOrth X x} := by
  have e : {x : Frame X.Ψ r | IsOrth X x} = ⋂ τ : X.Ψ, {x | gram τ.1 X.Gm (mat x τ) =
      Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)} := by
    ext x; simp [IsOrth]
  rw [e]
  refine isClosed_iInter fun τ => isClosed_eq ?_ continuous_const
  have hm : Continuous fun x : Frame X.Ψ r => mat x τ := continuous_apply τ
  simp only [FrameDegreeData.gram_eq]
  exact (hm.matrix_transpose.matrix_mul continuous_const).matrix_mul
    (hm.matrix_map Complex.continuous_conj)

theorem entry_sq_le {r : ℕ} (X : Data E r) {x0 x : Frame X.Ψ r} (h0 : IsOrth X x0)
    (hx : IsOrth X x) (τ : X.Ψ) (i j : Fin r) :
    ‖((mat x0 τ)⁻¹ * mat x τ) i j‖ ^ 2 ≤ ((r : ℝ) + 1) *
      ‖lminor ((mat x0 τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ ^ 2 := by
  have h := sumBd_entry_bound (FrameSumBound.isUpq_frame X h0 hx τ)
    ((FrameSumBound.swapIdx X.p0_le).symm i) ((FrameSumBound.swapIdx X.p0_le).symm j)
  have hm : ∀ M : Matrix (Fin r) (Fin r) ℂ,
      lminor M (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1)) =
        (M.submatrix (FrameSumBound.swapIdx X.p0_le)
          (FrameSumBound.swapIdx X.p0_le)).toBlocks₂₂.det := fun M => by
    unfold lminor
    congr 1
  rw [Matrix.submatrix_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Nat.sub_add_cancel X.p0_le, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, ← hm] at h
  exact h

theorem minor_sq_le {r : ℕ} (X : Data E r) {x0 x b : Frame X.Ψ r} (h0 : IsOrth X x0)
    (hx : IsOrth X x) (hb : b ∈ Bor X.Ψ r) {z : V (nd X)} (hz : z ∈ OmF X x0)
    (he : cpt X x0 z = rmul x b) {a : ℝ} (ha : rhF X x0 z ≤ a) (τ : X.Ψ) :
    ‖lminor ((mat x0 τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ ^ 2 ≤ Real.exp a := by
  classical
  have h := (FramePotential.frame_potential_basic r X x0 h0).2.2.2 z hz
  rw [he] at h
  simp only [FramePotential.factor_rmul X x0 x hb, FramePotential.norm_dmin_of_isOrth X hx,
    one_div, Finset.prod_inv_distrib, Real.exp_neg, inv_inj] at h
  refine le_trans ?_ (h.le.trans (Real.exp_le_exp.2 ha))
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
  refine le_mul_of_one_le_right (by positivity) ?_
  exact Finset.prod_induction _ (fun t : ℝ => 1 ≤ t) (fun _ _ => one_le_mul_of_one_le_of_one_le)
    le_rfl fun σ _ => FramePotential.one_le_minor_of_isOrth X h0 hx σ

theorem muF_sublevel_lt_top : MeasInvStatement (E := E) → ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ a : ℝ,
    muF X x0 {z | rhF X x0 z ≤ a} < ⊤ := by
  intro hI r X x0 h0 a
  set M : ℝ := Real.sqrt (((r : ℝ) + 1) * Real.exp a) with hM
  have hc : Continuous fun g : Frame X.Ψ r => rmul x0 g := by
    refine continuous_pi fun τ => ?_
    have hm : Continuous fun x : Frame X.Ψ r => mat x τ := continuous_apply τ
    exact continuous_const.matrix_mul hm
  have hK : IsCompact ((fun g : Frame X.Ψ r => rmul x0 g) '' Metric.closedBall 0 M ∩
      {x | IsOrth X x}) :=
    ((isCompact_closedBall _ _).image hc).inter_right (isClosed_isOrth X)
  have hfin := SatFin.muF_sat_lt_top hI r X x0 h0 _ hK fun x hx => IW.orth_mem_dom X x hx.2
  have hnull : muF X x0 (OmF X x0)ᶜ = 0 := by
    unfold muF
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.restrict_apply (OntoB.isOpen_OmF X x0).measurableSet.compl]
    simp
  refine lt_of_le_of_lt (measure_mono (t := sat X x0 _ ∪ (OmF X x0)ᶜ) fun z ha => ?_)
    (measure_union_lt_top hfin (by rw [hnull]; exact ENNReal.zero_lt_top))
  by_cases hz : z ∈ OmF X x0
  swap
  · exact Or.inr hz
  obtain ⟨x, hx, b, hb, he⟩ := ortho_holds r X _ hz
  refine Or.inl ⟨hz, x, ⟨⟨fun τ i j => ((mat x0 τ)⁻¹ * mat x τ : Matrix (Fin r) (Fin r) ℂ) i j, ?_, ?_⟩, hx⟩,
    b, hb, he⟩
  · have hM0 : 0 ≤ M := Real.sqrt_nonneg _
    refine mem_closedBall_zero_iff.2 ?_
    refine (pi_norm_le_iff_of_nonneg hM0).2 fun τ => (pi_norm_le_iff_of_nonneg hM0).2 fun i =>
      (pi_norm_le_iff_of_nonneg hM0).2 fun j => ?_
    refine Real.le_sqrt_of_sq_le ((entry_sq_le X h0 hx τ i j).trans ?_)
    exact mul_le_mul_of_nonneg_left (minor_sq_le X h0 hx hb hz he ha τ) (by positivity)
  · funext τ
    have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X h0 τ)
    exact Matrix.mul_nonsing_inv_cancel_left (mat x0 τ) (mat x τ) hu

end GlobalTheory.SublevelFin
end
