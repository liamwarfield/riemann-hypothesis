module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfC

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContinuousOnOfCharts
namespace GlobalTheory.KronMetric

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem inv_rmul {r : ℕ} {X : Data E r} {ψ : Frame X.Ψ r → ℝ} (h : IsInvFn X ψ) {x b : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) : ψ (rmul x b) = ψ x := by
  have := h 1 X.Γ.one_mem x hx b hb
  rwa [FundSetPf.lact_one] at this

theorem inv_lact {r : ℕ} {X : Data E r} {ψ : Frame X.Ψ r → ℝ} (h : IsInvFn X ψ) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) : ψ (lact γ x) = ψ x := by
  have := h γ hγ x hx _ (ExtFPf.oneF_mem X)
  rwa [ExtFPf.rmul_oneF] at this

theorem continuousOn_of_charts {r : ℕ} {X : Data E r} {ψ : Frame X.Ψ r → ℝ} (h : IsInvFn X ψ)
    (hs : ∀ x0, IsOrth X x0 → ContinuousOn (fun z => ψ (cpt X x0 z)) (OmF X x0)) :
    ContinuousOn ψ X.dom := by
  intro x hx
  obtain ⟨x1, ho, b, hb, hxe⟩ := ortho_holds r X x hx
  obtain ⟨D⟩ := ExtFPf.luData_of lu_holds X x1 ho
  have h0 : (0 : V (nd X)) ∈ OmF X x1 := by
    show cpt X x1 0 ∈ X.dom
    rw [IW.cpt_zero]
    exact IW.orth_mem_dom X x1 ho
  have hΔ : D.Δ x ≠ 0 := by
    have := (D.uniq 0 h0 b hb).1
    rwa [IW.cpt_zero, ← hxe] at this
  have hc : ContinuousOn (fun y => ψ (cpt X x1 (D.zOf y))) (ExtFPf.cell D) :=
    (hs x1 ho).comp D.hz.continuousOn fun y hy => (D.split y hy.1 hy.2).1
  have hc' : ContinuousOn ψ (ExtFPf.cell D) := by
    refine hc.congr fun y hy => ?_
    obtain ⟨h1, h2, h3⟩ := D.split y hy.1 hy.2
    show ψ y = ψ (cpt X x1 (D.zOf y))
    conv_lhs => rw [h3]
    exact inv_rmul h h1 h2
  exact (hc'.continuousAt ((ExtFPf.isOpen_cell D).mem_nhds ⟨hx, hΔ⟩)).continuousWithinAt

theorem exp_neg_phla {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Real.exp (-phla X la x) = X.nfac la x ^ 2 := by
  have hn := FlowCoefficientBounds.nfac_pos X hx la
  unfold phla
  rw [neg_mul, neg_neg, show 2 * Real.log (X.nfac la x) = Real.log (X.nfac la x ^ 2) by
    rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]

theorem exp_neg_add {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) :
    Real.exp (-(phla X la x + ψ x)) = X.nfac la x ^ 2 * Real.exp (-ψ x) := by
  rw [neg_add, Real.exp_add, exp_neg_phla X la hx]

theorem kronMetric :
    (NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r), ∀ ψ : Frame X.Ψ r → ℝ, IsInvFn X ψ → (∀ x0, IsOrth X x0 → ContDiffOn ℝ ∞ (fun z => ψ (cpt X x0 z)) (OmF X x0)) → (∃ C : ℝ, ∀ x ∈ X.dom, ψ x ≤ C) → ContinuousOn ψ X.dom ∧ IsMetricW X la (X.dom.indicator fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x)))) ∧ WLower X la (X.dom.indicator fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x))))) := by
  rintro ⟨hR, hL, -⟩ r X la ψ hinv hs ⟨C, hC⟩
  classical
  have hψc : ContinuousOn ψ X.dom := continuousOn_of_charts hinv fun x0 h => (hs x0 h).continuousOn
  refine ⟨hψc, ⟨?_, ?_, ?_⟩, Real.exp (-C), Real.exp_pos _, ?_⟩
  · have hc : ContinuousOn (fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x)))) X.dom := by
      refine ENNReal.continuous_ofReal.comp_continuousOn ?_
      refine (((ExtFPf.nfac_contOn X la).pow 2).mul
        (Real.continuous_exp.comp_continuousOn hψc.neg)).congr fun x hx => ?_
      exact exp_neg_add X la ψ hx
    rw [← Set.piecewise_eq_indicator]
    exact hc.measurable_piecewise continuousOn_const (FourierCoefficientDomain.isOpen_dom X).measurableSet
  · intro x hx b hb
    have hxb := OntoS.dom_rmul X hx hb
    have hpos : 0 < ‖bchar la b‖ := norm_pos_iff.2 (OntoE.bchar_ne X la hb)
    rw [Set.indicator_of_mem hxb, Set.indicator_of_mem hx, exp_neg_add X la ψ hxb,
      exp_neg_add X la ψ hx, hR r X la x hx b hb, inv_rmul hinv hx hb,
      ← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
  · intro γ hγ x hx
    have hγx := OntoS.dom_lact X hγ hx
    rw [Set.indicator_of_mem hγx, Set.indicator_of_mem hx, exp_neg_add X la ψ hγx,
      exp_neg_add X la ψ hx, hL r X la γ hγ x hx, inv_lact hinv hγ hx]
  · intro x hx
    rw [Set.indicator_of_mem hx, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    linarith [hC x hx]

end GlobalTheory.KronMetric
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MuFLtTopOfIsCompact
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.SatFin

open GlobalTheory.FrameMeas

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem muF_lt_top_of_isCompact {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) {K : Set (V (nd X))}
    (hK : IsCompact K) (hKO : K ⊆ OmF X x0) : muF X x0 K < ⊤ := by
  obtain ⟨M, hM⟩ := hK.bddAbove_image (OntoB.densF_continuousOn.mono hKO)
  unfold muF
  rw [withDensity_apply _ hK.measurableSet]
  calc ∫⁻ z in K, ENNReal.ofReal (densF X x0 z) ∂(volume.restrict (OmF X x0))
      ≤ ∫⁻ _ in K, ENNReal.ofReal M ∂(volume.restrict (OmF X x0)) :=
        setLIntegral_mono' hK.measurableSet fun z hz =>
          ENNReal.ofReal_le_ofReal (hM ⟨z, hz, rfl⟩)
    _ = ENNReal.ofReal M * (volume.restrict (OmF X x0)) K := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ((Measure.restrict_apply_le _ _).trans_lt hK.measure_lt_top)

theorem muF_borSat_eq (hI : MeasInvStatement (E := E)) {r : ℕ} (X : Data E r)
    {x0 x1 : Frame X.Ψ r} (h0 : IsOrth X x0) (h1 : IsOrth X x1) {C : Set (Frame X.Ψ r)}
    (hK : IsCompact C) (hC : C ⊆ X.dom) :
    muF X x0 (cpt X x0 ⁻¹' borSat X C) = muF X x1 (cpt X x1 ⁻¹' borSat X C) := by
  have hS := measurableSet_borSat X hK hC
  have h := hI r X x0 x1 h0 h1 ((borSat X C).indicator 1) (measurable_one.indicator hS) (by
    intro x _ b hb
    by_cases hxS : x ∈ borSat X C
    · rw [Set.indicator_of_mem hxS, Set.indicator_of_mem ((rmul_mem_borSat_iff X C hb).mpr hxS)]
      rfl
    · rw [Set.indicator_of_notMem hxS,
        Set.indicator_of_notMem fun h => hxS ((rmul_mem_borSat_iff X C hb).mp h)])
  rw [← lintegral_indicator_one ((FundSetPf.cont_cpt X x0).measurable hS),
    ← lintegral_indicator_one ((FundSetPf.cont_cpt X x1).measurable hS)]
  exact h

theorem muF_sat_lt_top (hI : MeasInvStatement (E := E)) (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r)
    (hx0 : IsOrth X x0) (C : Set (Frame X.Ψ r)) (hK : IsCompact C) (hC : C ⊆ X.dom) :
    muF X x0 (sat X x0 C) < ⊤ := by
  rw [sat_eq_preimage X x0 hC]
  refine hK.induction_on (p := fun s => muF X x0 (cpt X x0 ⁻¹' borSat X s) < ⊤) ?_ ?_ ?_ ?_
  · have : borSat X (∅ : Set (Frame X.Ψ r)) = ∅ := by
      ext y; simp [borSat]
    simp [this]
  · intro s t hst ht
    refine (measure_mono fun z hz => ?_).trans_lt ht
    obtain ⟨x, hx, h⟩ := hz
    exact ⟨x, hst hx, h⟩
  · intro s t hs ht
    refine (measure_mono (t := cpt X x0 ⁻¹' borSat X s ∪ cpt X x0 ⁻¹' borSat X t)
      fun z hz => ?_).trans_lt (measure_union_lt_top hs ht)
    obtain ⟨x, hx | hx, h⟩ := hz
    · exact Or.inl ⟨x, hx, h⟩
    · exact Or.inr ⟨x, hx, h⟩
  · intro x hx
    have hxd := hC hx
    obtain ⟨x1, hx1, b1, hb1, hxe⟩ := ortho_holds r X x hxd
    obtain ⟨Δ, zOf, bOf, hΔ, -, hz, -, hdec, huniq⟩ := lu_holds r X x1 hx1
    have h0 := IW.zero_mem_OmF X x1 hx1
    obtain ⟨u1, u2, -⟩ := huniq 0 h0 b1 hb1
    rw [IW.cpt_zero, ← hxe] at u1 u2
    obtain ⟨ρ, hρ, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      ((OntoB.isOpen_OmF X x1).mem_nhds h0)
    have hW : {y | y ∈ X.dom ∧ Δ y ≠ 0} ∈ 𝓝 x :=
      ((FourierCoefficientDomain.isOpen_dom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)).mem_nhds
        ⟨hxd, u1⟩
    have hzc : ContinuousAt zOf x := hz.continuousOn.continuousAt hW
    have hV : zOf ⁻¹' Metric.closedBall 0 ρ ∈ 𝓝 x :=
      hzc.preimage_mem_nhds (by rw [u2]; exact Metric.closedBall_mem_nhds _ hρ)
    refine ⟨{y | y ∈ X.dom ∧ Δ y ≠ 0} ∩ zOf ⁻¹' Metric.closedBall 0 ρ,
      mem_nhdsWithin_of_mem_nhds (Filter.inter_mem hW hV), ?_⟩
    have hKc : IsCompact (cpt X x1 '' Metric.closedBall 0 ρ) :=
      (isCompact_closedBall _ _).image (FundSetPf.cont_cpt X x1)
    have hKd : cpt X x1 '' Metric.closedBall 0 ρ ⊆ X.dom := by
      rintro _ ⟨z, hz, rfl⟩
      exact hball hz
    calc muF X x0 (cpt X x0 ⁻¹' borSat X
          ({y | y ∈ X.dom ∧ Δ y ≠ 0} ∩ zOf ⁻¹' Metric.closedBall 0 ρ))
        ≤ muF X x0 (cpt X x0 ⁻¹' borSat X (cpt X x1 '' Metric.closedBall 0 ρ)) := by
          refine measure_mono fun z hz => ?_
          obtain ⟨y, ⟨⟨hyd, hyΔ⟩, hyz⟩, b, hb, h⟩ := hz
          obtain ⟨-, hb', hy⟩ := hdec y hyd hyΔ
          refine ⟨_, ⟨zOf y, hyz, rfl⟩, rmul (bOf y) b, ExtFPf.mul_mem X hb' hb, ?_⟩
          rw [← ExtFPf.rmul_assoc, ← hy, h]
      _ = muF X x1 (cpt X x1 ⁻¹' borSat X (cpt X x1 '' Metric.closedBall 0 ρ)) :=
          muF_borSat_eq hI X hx0 hx1 hKc hKd
      _ ≤ muF X x1 (Metric.closedBall 0 ρ) := by
          refine measure_mono fun z hz => ?_
          obtain ⟨_, ⟨z', hz', rfl⟩, b, hb, h⟩ := hz
          rw [← ExtFPf.rmul_oneF X (cpt X x1 z)] at h
          rwa [FundSetPf.cpt_uniq X hx1 (ExtFPf.oneF_mem X) hb h]
      _ < ⊤ := muF_lt_top_of_isCompact X x1 (isCompact_closedBall _ _) hball

end GlobalTheory.SatFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetFderivNeZeroOrbit
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.OrbitCoord

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


omit [NumberField E] [IsCMField E] in
theorem rmul_left_cancel {r : ℕ} {Ψ : Finset (E →+* ℂ)} {o a c : Frame Ψ r}
    (ho : ∀ τ, (mat o τ).det ≠ 0) (h : rmul o a = rmul o c) : a = c := by
  funext τ
  have h1 : mat o τ * mat a τ = mat o τ * mat c τ := congrFun h τ
  have hu : IsUnit (mat o τ) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (ho τ))
  exact hu.mul_left_cancel h1

theorem exists_swap {r : ℕ} (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    ∃ (U : Set (V (nd X))) (Φ : V (nd X) → V (nd X)) (bf : V (nd X) → Frame X.Ψ r),
      IsOpen U ∧ 0 ∈ U ∧ DifferentiableOn ℂ Φ U ∧ Φ 0 = 0 ∧
      ∀ z ∈ U, bf z ∈ Bor X.Ψ r ∧ rmul b (nmat X z) = rmul (nmat X (Φ z)) (bf z) := by
  have ho : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2
  have hod : x0F X ∈ X.dom := IW.orth_mem_dom X _ ho
  obtain ⟨Δ, zOf, bOf, hΔ, -, hz, -, hsplit, huniq⟩ := lu_holds r X (x0F X) ho
  have hcd := OntoB.cd_cpt X (rmul (x0F X) b)
  have h0 := huniq 0 (IW.zero_mem_OmF X _ ho) b hb
  rw [IW.cpt_zero] at h0
  refine ⟨cpt X (rmul (x0F X) b) ⁻¹' {x | x ∈ X.dom ∧ Δ x ≠ 0},
    fun z => zOf (cpt X (rmul (x0F X) b) z), fun z => bOf (cpt X (rmul (x0F X) b) z), ?_, ?_, ?_, ?_, ?_⟩
  · exact ((FourierCoefficientDomain.isOpen_dom X).inter
      (isOpen_ne_fun hΔ.continuous continuous_const)).preimage hcd.continuous
  · show cpt X _ 0 ∈ X.dom ∧ Δ (cpt X _ 0) ≠ 0
    rw [IW.cpt_zero]
    exact ⟨OntoS.dom_rmul X hod hb, h0.1⟩
  · exact hz.comp (hcd.differentiable (by simp)).differentiableOn fun _ h => h
  · show zOf (cpt X _ 0) = 0
    rw [IW.cpt_zero]
    exact h0.2.1
  · intro z hzU
    obtain ⟨-, h2, h3⟩ := hsplit _ hzU.1 hzU.2
    refine ⟨h2, rmul_left_cancel (fun τ => (hod τ).1) ?_⟩
    rw [← ExtFPf.rmul_assoc, ← ExtFPf.rmul_assoc]
    exact h3

theorem det_fderiv_ne_zero_orbit : (KapGGStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (L : Wt X.Ψ r) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ), X.IsSec L w0 → (∀ k, X.IsSec L (s k)) → ∀ x ∈ X.dom, w0 x ≠ 0 → (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => s k (cpt X (x) z) / w0 (cpt X (x) z) : V (nd X))) 0).det ≠ 0 → ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => s k (cpt X (lact γ (rmul x b)) z) / w0 (cpt X (lact γ (rmul x b)) z) : V (nd X))) 0).det ≠ 0) := by
  intro hK r X L w0 s hw0 hs x hx hwx hdet γ hγ b hb
  obtain ⟨U, Φ, bf, hU, h0U, hΦ, hΦ0, hsw⟩ := exists_swap X hb
  set y := lact γ (rmul x b) with hy
  have hyd : y ∈ X.dom := OntoS.dom_lact X hγ (OntoS.dom_rmul X hx hb)
  have hcpt : ∀ z ∈ U, cpt X y z = lact γ (rmul (cpt X x (Φ z)) (bf z)) := by
    intro z hz
    unfold cpt
    rw [hy, ← FundSetPf.lact_rmul, ExtFPf.rmul_assoc, (hsw z hz).2, ExtFPf.rmul_assoc]
  have h0y : (0 : V (nd X)) ∈ OmF X y := by
    show cpt X y 0 ∈ X.dom
    rwa [IW.cpt_zero]
  have h0x : (0 : V (nd X)) ∈ OmF X x := by
    show cpt X x 0 ∈ X.dom
    rwa [IW.cpt_zero]
  have hJ : (fderiv ℂ Φ 0).det = bchar (kapW X) (bf 0) :=
    hK r X y x γ (U ∩ OmF X y) Φ bf (hU.inter (OntoB.isOpen_OmF X y)) (hΦ.mono Set.inter_subset_left)
      (fun z hz => ⟨hz.2, (hsw z hz.1).1, hcpt z hz.1⟩) 0 ⟨h0U, h0y⟩
  have hJ0 : (fderiv ℂ Φ 0).det ≠ 0 := hJ ▸ OntoE.bchar_ne X _ (hsw 0 h0U).1
  have hΦd : DifferentiableAt ℂ Φ 0 := hΦ.differentiableAt (hU.mem_nhds h0U)
  have hnx : OmF X x ∈ 𝓝 (0 : V (nd X)) := (OntoB.isOpen_OmF X x).mem_nhds h0x
  set F : V (nd X) → V (nd X) := fun z : V (nd X) =>
    (WithLp.toLp 2 fun k => s k (cpt X (x) z) / w0 (cpt X (x) z) : V (nd X)) with hF
  have hFd : DifferentiableAt ℂ F 0 := by
    have hw : DifferentiableAt ℂ (fun z => w0 (cpt X x z)) 0 :=
      (OntoB.hol_comp X x hw0.1).differentiableAt hnx
    have hsk : ∀ k, DifferentiableAt ℂ (fun z => s k (cpt X x z)) 0 := fun k =>
      (OntoB.hol_comp X x (hs k).1).differentiableAt hnx
    rw [hF]
    refine (differentiableAt_piLp 2).2 fun k => ?_
    have hne : w0 (cpt X x 0) ≠ 0 := by rwa [IW.cpt_zero]
    have := (hsk k).mul (hw.inv hne)
    simp only [div_eq_mul_inv]
    exact this
  have hev : (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      s k (cpt X y z) / w0 (cpt X y z) : V (nd X))) =ᶠ[𝓝 0] F ∘ Φ := by
    have h1 : ∀ᶠ z in 𝓝 (0 : V (nd X)), Φ z ∈ OmF X x :=
      hΦd.continuousAt.preimage_mem_nhds (by rwa [hΦ0])
    filter_upwards [hU.mem_nhds h0U, h1] with z hz hzx
    have hzx' : cpt X x (Φ z) ∈ X.dom := hzx
    have hbz := (hsw z hz).1
    have hd := OntoS.dom_rmul X hzx' hbz
    have hχ : X.χ L γ ≠ 0 := by
      intro h
      have := OntoE.chi_norm X L hγ
      rw [h, norm_zero] at this
      exact zero_ne_one this
    show _ = F (Φ z)
    rw [hF]
    show (WithLp.toLp 2 _ : V (nd X)) = WithLp.toLp 2 _
    congr 1
    funext k
    rw [hcpt z hz, (hs k).2.2 γ hγ _ hd, hw0.2.2 γ hγ _ hd, mul_div_mul_left _ _ hχ,
      (hs k).2.1 _ hzx' _ hbz, hw0.2.1 _ hzx' _ hbz, mul_div_mul_left _ _ (OntoE.bchar_ne X L hbz)]
  rw [hev.fderiv_eq, fderiv_comp 0 (by rwa [hΦ0]) hΦd, hΦ0]
  have : ((fderiv ℂ F 0).comp (fderiv ℂ Φ 0)).det = (fderiv ℂ F 0).det * (fderiv ℂ Φ 0).det := by
    unfold ContinuousLinearMap.det
    rw [← LinearMap.det_comp]
    rfl
  rw [this]
  exact mul_ne_zero hdet hJ0

end GlobalTheory.OrbitCoord
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OneLeMinorOfIsOrth
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexOrder

namespace GlobalTheory.FramePotential

theorem one_le_norm_lminor_sq {n p : ℕ} (h : p ≤ n) (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : gᵀ * (Matrix.diagonal fun a : Fin n => ((sgn p (a : ℕ) : ℝ) : ℂ)) * g.map (starRingEnd ℂ) =
      Matrix.diagonal fun a : Fin n => ((sgn p (a : ℕ) : ℝ) : ℂ)) :
    1 ≤ ‖lminor g ⟨p, Nat.lt_succ_of_le h⟩‖ ^ 2 := by
  set A : Matrix (Fin p) (Fin p) ℂ := g.submatrix (Fin.castLE h) (Fin.castLE h) with hA
  set C : Matrix (Fin n) (Fin p) ℂ :=
    Matrix.of fun k a => if (k : ℕ) < p then 0 else g k (Fin.castLE h a) with hC
  have key : Aᴴ * A = 1 + Cᴴ * C := by
    ext a b
    have e := congrFun (congrFun hg (Fin.castLE h b)) (Fin.castLE h a)
    rw [Matrix.mul_apply] at e
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.diagonal_apply, Fin.castLE_inj] at e
    have e1 : (1 : Matrix (Fin p) (Fin p) ℂ) a b =
        ∑ k, g k (Fin.castLE h b) * ((sgn p (k : ℕ) : ℝ) : ℂ) * starRingEnd ℂ (g k (Fin.castLE h a)) := by
      rw [e, Matrix.one_apply]
      by_cases hab : a = b
      · subst hab; simp [sgn]
      · rw [if_neg hab, if_neg (Ne.symm hab)]
    have e2 : (Aᴴ * A) a b = ∑ k : Fin n, if (k : ℕ) < p then
        starRingEnd ℂ (g k (Fin.castLE h a)) * g k (Fin.castLE h b) else 0 := by
      rw [Matrix.mul_apply]
      refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun k hk => ?_)
        (fun k => ?_)
      · rw [if_neg]
        intro hlt
        exact hk ⟨⟨k, hlt⟩, Fin.ext rfl⟩
      · simp [hA, Matrix.conjTranspose_apply]
    rw [e2, Matrix.add_apply, e1, Matrix.mul_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : (k : ℕ) < p
    · simp [hC, sgn, hk, Matrix.conjTranspose_apply, mul_comm]
    · simp [hC, sgn, hk, Matrix.conjTranspose_apply, mul_comm]
  have h1 := sumBd_det_one_add_ge (Matrix.posSemidef_conjTranspose_mul_self C)
  rw [← key, sumBd_normSq_det, sumBd_trace_ctm] at h1
  have h2 := sumBdFsq_nonneg C
  rw [← Complex.normSq_eq_norm_sq]
  show 1 ≤ Complex.normSq A.det
  linarith

theorem lminor_mul_upper {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) {B : Matrix (Fin n) (Fin n) ℂ}
    (hB : B.BlockTriangular id) (k : Fin (n + 1)) :
    lminor (M * B) k = lminor M k * ∏ j : Fin k, B (Fin.castLE (Nat.le_of_lt_succ k.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) := by
  have h := Nat.le_of_lt_succ k.isLt
  unfold lminor
  rw [FrameDegreeData.sub_mul_sub h M B (fun a c m hm => by
      rw [FrameDegreeData.upper_lt hB (show Fin.castLE h c < m by rw [Fin.lt_def]; simp; omega), mul_zero]),
    Matrix.det_mul, FrameDegreeData.det_sub_upper h hB]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem factor_rmul {r : ℕ} (X : Data E r) (x0 x : Frame X.Ψ r) {b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm (rmul x b) τ i‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (rmul x b) τ) i‖ ^ 2 =
      ‖dmin X.Gm x τ i‖ / ‖lminor ((mat x0 τ)⁻¹ * mat x τ) i‖ ^ 2 := by
  have e : mat (rmul x b) τ = mat x τ * mat b τ := rfl
  rw [FrameDegreeData.dmin_rmul X x hb, e, ← Matrix.mul_assoc,
    lminor_mul_upper _ (FrameDegreeData.upper_of_bor X hb τ)]
  have hc : (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => FrameDegreeData.bdiag_ne X hb τ _
  generalize (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) = c at hc ⊢
  have hc' : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hc)
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, mul_pow,
    ← mul_div_mul_right ‖dmin X.Gm x τ i‖ _ hc']
  congr 1
  ring

theorem norm_dmin_of_isOrth {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ)
    (i : Fin (r + 1)) : ‖dmin X.Gm x τ i‖ = 1 := by
  unfold dmin lminor
  rw [hx τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _),
    Matrix.det_diagonal, norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  simp only [Function.comp, sgn]
  split_ifs <;> simp

theorem one_le_minor_of_isOrth {r : ℕ} (X : Data E r) {x0 x : Frame X.Ψ r} (h0 : IsOrth X x0)
    (hx : IsOrth X x) (τ : X.Ψ) :
    1 ≤ ‖lminor ((mat x0 τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ ^ 2 := by
  apply one_le_norm_lminor_sq X.p0_le
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X x0 h0 τ)
  conv_lhs => rw [← h0 τ]
  rw [← FrameDegreeData.gram_mul, Matrix.mul_nonsing_inv_cancel_left _ _ hu, hx τ]

theorem factor_mem {r : ℕ} (X : Data E r) {x0 x : Frame X.Ψ r} (h0 : IsOrth X x0)
    (hx : x ∈ X.dom) (τ : X.Ψ) :
    0 < ‖dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ /
        ‖lminor ((mat x0 τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ ^ 2 ∧
      ‖dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ /
        ‖lminor ((mat x0 τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ ^ 2 ≤ 1 := by
  obtain ⟨x1, h1, b, hb, rfl⟩ := ortho_holds r X x hx
  rw [factor_rmul X x0 x1 hb, norm_dmin_of_isOrth X h1]
  have h := one_le_minor_of_isOrth X h0 h1 τ
  exact ⟨div_pos one_pos (by linarith), (div_le_one (by linarith)).mpr h⟩

theorem lminor_cpt {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} (h0 : IsOrth X x0) (z : V (nd X))
    (τ : X.Ψ) (i : Fin (r + 1)) : lminor ((mat x0 τ)⁻¹ * mat (cpt X x0 z) τ) i = 1 := by
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X x0 h0 τ)
  have e : mat (cpt X x0 z) τ = mat x0 τ * mat (nmat X z) τ := rfl
  rw [e, Matrix.nonsing_inv_mul_cancel_left _ _ hu, ← Matrix.mul_one (mat (nmat X z) τ),
    LUPf.lminor_nb _ _ (fun a c hac => ?_) (fun a => ?_) Matrix.blockTriangular_one]
  · simp
  · simp [mat, nmat, hac.ne, not_lt.mpr hac.le]
  · simp [mat, nmat]

theorem frame_potential_basic :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → Measurable (fun x : Frame X.Ψ r => (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2)) ∧ (∀ x ∈ X.dom, 0 < (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) ∧ (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, (∏ τ : X.Ψ, ‖dmin X.Gm (rmul x b) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (rmul x b) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) = (∏ τ : X.Ψ, ‖dmin X.Gm (x) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (x) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2)) ∧ ∀ z ∈ OmF X x0, (∏ τ : X.Ψ, ‖dmin X.Gm (cpt X x0 z) τ (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (cpt X x0 z) τ) (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1))‖ ^ 2) = Real.exp (-rhF X x0 z)) := by
  intro r X x0 h0
  refine ⟨?_, fun x hx => ⟨?_, ?_⟩, fun x _ b hb => ?_, fun z hz => ?_⟩
  · refine Finset.measurable_prod _ fun τ _ => Measurable.div ?_ ?_
    · exact (ExtFPf.cont_dmin X τ _).norm.measurable
    · have hm : Continuous fun x : Frame X.Ψ r => mat x τ := continuous_apply τ
      exact ((((continuous_const.matrix_mul hm).matrix_submatrix _ _).matrix_det).norm.pow 2).measurable
  · exact Finset.prod_pos fun τ _ => (factor_mem X h0 hx τ).1
  · exact Finset.prod_le_one₀ (fun τ _ => (factor_mem X h0 hx τ).1.le)
      fun τ _ => (factor_mem X h0 hx τ).2
  · exact Finset.prod_congr rfl fun τ _ => factor_rmul X x0 x hb τ _
  · unfold rhF
    rw [neg_neg, Real.exp_sum]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [lminor_cpt X h0, Real.exp_log (norm_pos_iff.mpr (FlowCoefficientBounds.dmin_ne X hz τ _))]
    simp

end GlobalTheory.FramePotential
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormLeOfDet
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.OrderToIntegral

open Filter Metric

theorem norm_le_of_det {n : ℕ} {f : V n → V n} {f' : V n →L[ℂ] V n} (hf : HasFDerivAt f f' 0)
    (hdet : f'.det ≠ 0) (h0 : f 0 = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ z in 𝓝 (0 : V n), ‖z‖ ≤ K * ‖f z‖ := by
  obtain ⟨K, hKpos, hK⟩ := (f' : V n →ₗ[ℂ] V n).exists_antilipschitzWith (HE.ker_bot_of_det hdet)
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hK' : ∀ z : V n, ‖z‖ ≤ K * ‖f' z‖ := fun z => by
    have := hK.le_mul_dist z 0
    simpa using this
  have hlo := hf.isLittleO.bound (c := 1 / (2 * K)) (by positivity)
  refine ⟨2 * K, by positivity, ?_⟩
  filter_upwards [hlo] with z hz
  rw [h0, sub_zero, sub_zero] at hz
  have h1 : ‖f' z‖ ≤ ‖f z‖ + 1 / (2 * K) * ‖z‖ := by
    have : ‖f' z‖ ≤ ‖f z‖ + ‖f z - f' z‖ := by
      calc ‖f' z‖ = ‖f z - (f z - f' z)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    linarith
  have h2 : (K : ℝ) * (1 / (2 * K) * ‖z‖) = ‖z‖ / 2 := by field_simp
  have h3 := mul_le_mul_of_nonneg_left h1 hK0.le
  have h4 := hK' z
  rw [mul_add, h2] at h3
  linarith

theorem sum_sq_lower {n : ℕ} (hn : 0 < n) {w : V n → ℂ} {s : Fin n → V n → ℂ}
    (hw : ContinuousAt w 0) (hw0 : w 0 ≠ 0) (hs0 : ∀ k, s k 0 = 0)
    (hdet : (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => s k z / w z : V n)) 0).det ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ z in 𝓝 (0 : V n), c * ‖z‖ ^ 2 ≤ ∑ k, ‖s k z‖ ^ 2 := by
  have hF : DifferentiableAt ℂ (fun z : V n => (WithLp.toLp 2 fun k => s k z / w z : V n)) 0 := by
    by_contra hnd
    rw [fderiv_zero_of_not_differentiableAt hnd] at hdet
    apply hdet
    show LinearMap.det (0 : V n →ₗ[ℂ] V n) = 0
    rw [LinearMap.det_zero, finrank_euclideanSpace, Fintype.card_fin, zero_pow (by omega)]
  obtain ⟨K, hK, hle⟩ := norm_le_of_det hF.hasFDerivAt hdet (by ext k; simp [hs0])
  have hpos : 0 < ‖w 0‖ := norm_pos_iff.2 hw0
  have hg : ∀ᶠ z in 𝓝 (0 : V n), ‖w 0‖ / 2 ≤ ‖w z‖ :=
    (hw.norm.tendsto.eventually (lt_mem_nhds (half_lt_self hpos))).mono fun z hz => le_of_lt hz
  refine ⟨(‖w 0‖ / 2) ^ 2 / K ^ 2, by positivity, ?_⟩
  filter_upwards [hle, hg] with z hz hwz
  have hwz0 : 0 < ‖w z‖ := lt_of_lt_of_le (half_pos hpos) hwz
  have e1 : ‖(WithLp.toLp 2 fun k => s k z / w z : V n)‖ ^ 2 = (∑ k, ‖s k z‖ ^ 2) / ‖w z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Finset.sum_div]
    simp [div_pow]
  have h1 : ‖z‖ ^ 2 ≤ K ^ 2 * ((∑ k, ‖s k z‖ ^ 2) / ‖w z‖ ^ 2) := by
    rw [← e1, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hz 2
  have h2 : (‖w 0‖ / 2) ^ 2 ≤ ‖w z‖ ^ 2 := pow_le_pow_left₀ (by positivity) hwz 2
  calc (‖w 0‖ / 2) ^ 2 / K ^ 2 * ‖z‖ ^ 2
      ≤ ‖w z‖ ^ 2 / K ^ 2 * (K ^ 2 * ((∑ k, ‖s k z‖ ^ 2) / ‖w z‖ ^ 2)) := by gcongr
    _ = ∑ k, ‖s k z‖ ^ 2 := by field_simp

theorem lintegral_lt_top {n : ℕ} (hn : 0 < n) {g : V n → ℂ} {S : V n → ℝ} {a : ℕ} {c : ℝ}
    (hc : 0 < c) (hS : ∀ᶠ z in 𝓝 (0 : V n), c * ‖z‖ ^ 2 ≤ S z)
    (hg : g =O[𝓝 0] fun z => ‖z‖ ^ a) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∫⁻ z in ball (0 : V n) ρ,
      ENNReal.ofReal (‖g z‖ ^ 2 * S z ^ (-((a : ℝ) + (n : ℝ) - 1 / 2))) < ⊤ := by
  obtain ⟨C, hC, hO⟩ := hg.exists_pos
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hO.bound.and hS)
  have : Nontrivial (V n) := ⟨⟨EuclideanSpace.single ⟨0, hn⟩ (1 : ℂ), 0, by
    intro h
    have h1 := congrArg (fun v : V n => v ⟨0, hn⟩) h
    simp at h1⟩⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set e : ℝ := (a : ℝ) + (n : ℝ) - 1 / 2 with he
  have he0 : 0 ≤ e := by
    have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    linarith
  have hint := (mvInt n hn ((n : ℝ) - 1 / 2)).2 (by linarith)
  refine ⟨min ε 1, lt_min hε one_pos, ?_⟩
  have hfin : ENNReal.ofReal (C ^ 2 * c ^ (-e)) *
      ∫⁻ y in ball (0 : V n) 1, ENNReal.ofReal ‖y‖ ^ (-2 * ((n : ℝ) - 1 / 2)) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint
  refine lt_of_le_of_lt ?_ hfin
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine le_trans ?_ (lintegral_mono_set (ball_subset_ball (min_le_right ε 1)))
  refine lintegral_mono_ae ?_
  have h0 : ∀ᵐ z ∂(volume.restrict (ball (0 : V n) (min ε 1))), z ≠ 0 :=
    ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton (0 : V n)))
  filter_upwards [h0, ae_restrict_mem measurableSet_ball] with z hz0 hz
  obtain ⟨h1, h2⟩ := hball z (ball_subset_ball (min_le_left ε 1) hz)
  have hz : 0 < ‖z‖ := norm_pos_iff.2 hz0
  rw [ENNReal.ofReal_rpow_of_pos hz, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [norm_pow, norm_norm] at h1
  have h3 : ‖g z‖ ^ 2 ≤ (C * ‖z‖ ^ a) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h4 : S z ^ (-e) ≤ (c * ‖z‖ ^ 2) ^ (-e) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by linarith)
  have hSz : 0 ≤ S z := le_trans (by positivity) h2
  have h5 : (‖z‖ ^ a) ^ 2 * (‖z‖ ^ 2) ^ (-e) = ‖z‖ ^ (-2 * ((n : ℝ) - 1 / 2)) := by
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hz.le,
      ← Real.rpow_add hz]
    congr 1
    rw [he]
    push_cast
    ring
  calc ‖g z‖ ^ 2 * S z ^ (-e) ≤ (C * ‖z‖ ^ a) ^ 2 * (c * ‖z‖ ^ 2) ^ (-e) :=
        mul_le_mul h3 h4 (Real.rpow_nonneg hSz _) (by positivity)
    _ = C ^ 2 * c ^ (-e) * ((‖z‖ ^ a) ^ 2 * (‖z‖ ^ 2) ^ (-e)) := by
        rw [Real.mul_rpow hc.le (by positivity)]
        ring
    _ = _ := by rw [h5]

end GlobalTheory.OrderToIntegral

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem vanS_of_isBigO : ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (a : ℕ)
    (g : Frame X.Ψ r → ℂ), ContinuousOn g X.dom →
    (∀ j, (fun z : V (nd X) => g (cpt X (Fl.xs j) z)) =O[𝓝 0] fun z => ‖z‖ ^ a) →
    VanS X Fl.xs Fl.s a g := by
  intro r X Xa Fl a g _ hO j
  have hn : 0 < nd X := lt_of_lt_of_le (by norm_num) Xa.n_ge
  have hw0 : X.IsSec Xa.L Fl.w0 := Fl.weightForm_vanishes.1.1.1
  have hs0 : ∀ k, Fl.s k (Fl.xs j) = 0 :=
    (Fl.S_eq _ (Fl.xs_mem j)).2 ⟨j, 1, X.Γ.one_mem, ExtFPf.oneF X, ExtFPf.oneF_mem X, by
      rw [FundSetPf.lact_one, ExtFPf.rmul_oneF]⟩
  have hw : ContinuousAt (fun z : V (nd X) => Fl.w0 (cpt X (Fl.xs j) z)) 0 := by
    refine ContinuousAt.comp (g := Fl.w0) ?_ (FundSetPf.cont_cpt X (Fl.xs j)).continuousAt
    rw [IW.cpt_zero]
    exact hw0.1.continuousOn.continuousAt ((FourierCoefficientDomain.isOpen_dom X).mem_nhds (Fl.xs_mem j))
  obtain ⟨c, hc, hS⟩ := OrderToIntegral.sum_sq_lower
    (w := fun z => Fl.w0 (cpt X (Fl.xs j) z)) (s := fun k z => Fl.s k (cpt X (Fl.xs j) z)) hn hw
    (by simpa only [IW.cpt_zero] using Fl.w0_ne j) (by simpa only [IW.cpt_zero] using hs0)
    (Fl.coord j)
  exact OrderToIntegral.lintegral_lt_top hn hc hS (hO j)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.WeightContDiffOn
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.KronSolve

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def weight (X : Data E r) (la L : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) (x0 : Frame X.Ψ r) (bb : ℝ)
    (z : V (nd X)) : ℝ :=
  phla X la (cpt X x0 z) + ((-1) * Real.log (densF X x0 z) +
    ((-(nd X : ℝ)) * phla X L (cpt X x0 z) + (ψ (cpt X x0 z) + (-bb) * rhF X x0 z)))

theorem weight_contDiffOn (X : Data E r) (la L : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) (x0 : Frame X.Ψ r)
    (bb : ℝ) (hψ : ContDiffOn ℝ ∞ (fun z => ψ (cpt X x0 z)) (OmF X x0)) :
    ContDiffOn ℝ ∞ (weight X la L ψ x0 bb) (OmF X x0) := by
  intro z hz
  have h1 := IW.phla_cpt_cdAt X x0 hz la
  have h2 := IW.logDens_cdAt X x0 hz
  have h3 := IW.phla_cpt_cdAt X x0 hz L
  have h4 := hψ.contDiffAt ((OntoB.isOpen_OmF X x0).mem_nhds hz)
  have h5 := OntoB.rhF_contDiffAt hz
  exact (h1.add ((contDiffAt_const.mul h2).add ((contDiffAt_const.mul h3).add
    (h4.add (contDiffAt_const.mul h5))))).contDiffWithinAt

theorem levi_weight (X : Data E r) (la L : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) (x0 : Frame X.Ψ r)
    (bb : ℝ) (hψ : ContDiffOn ℝ ∞ (fun z => ψ (cpt X x0 z)) (OmF X x0)) {z : V (nd X)}
    (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ) :
    (leviV (nd X) (fun w => ((weight X la L ψ x0 bb w : ℝ) : ℂ)) z ξ).re =
      leviO X x0 (phla X la) z ξ - leviDens X x0 z ξ - (nd X : ℝ) * leviO X x0 (phla X L) z ξ +
        leviO X x0 ψ z ξ - bb * leviRh X x0 z ξ := by
  have h1 := (IW.phla_cpt_cdAt X x0 hz la).of_le HE.two_le_inf
  have h2 := (IW.logDens_cdAt X x0 hz).of_le HE.two_le_inf
  have h3 := (IW.phla_cpt_cdAt X x0 hz L).of_le HE.two_le_inf
  have h4 := (hψ.contDiffAt ((OntoB.isOpen_OmF X x0).mem_nhds hz)).of_le HE.two_le_inf
  have h5 : ContDiffAt ℝ 2 (fun w => rhF X x0 w) z := (OntoB.rhF_contDiffAt hz).of_le HE.two_le_inf
  unfold weight leviO leviM leviDens leviRh
  rw [Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 ((contDiffAt_const.mul h2).add ((contDiffAt_const.mul h3).add
      (h4.add (contDiffAt_const.mul h5)))),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h2) ((contDiffAt_const.mul h3).add
      (h4.add (contDiffAt_const.mul h5))),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h3) (h4.add (contDiffAt_const.mul h5)),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add h4 (contDiffAt_const.mul h5),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h2, Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h3,
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h5]
  simp only [Complex.add_re, Complex.re_ofReal_mul]
  ring

theorem pnorm_sq (X : Data E r) (L : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x0 : Frame X.Ψ r)
    {z : V (nd X)} (hz : z ∈ OmF X x0) :
    X.pnorm L P (cpt X x0 z) ^ 2 =
      Complex.normSq (P (cpt X x0 z)) * Real.exp (-phla X L (cpt X x0 z)) := by
  have hp := OntoE.nfac_pos X x0 (la := L) hz
  have e : X.pnorm L P (cpt X x0 z) = ‖P (cpt X x0 z)‖ * X.nfac L (cpt X x0 z) := rfl
  have e2 : Real.exp (-phla X L (cpt X x0 z)) = X.nfac L (cpt X x0 z) ^ 2 := by
    have : -phla X L (cpt X x0 z) = Real.log (X.nfac L (cpt X x0 z) ^ 2) := by
      rw [Real.log_pow]; unfold phla; push_cast; ring
    rw [this, Real.exp_log (pow_pos hp 2)]
  rw [e, e2, Complex.normSq_eq_norm_sq, mul_pow]

theorem integrand_eq (X : Data E r) (la L : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) (x0 : Frame X.Ψ r)
    (bb : ℝ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) (A : ℝ) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    densF X x0 z * (A * Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z *
      (∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2) ^ (-(nd X : ℝ))) =
    A * Real.exp (-weight X la L ψ x0 bb z) *
      HE.nsq (fun k w => s k (cpt X x0 w)) z ^ (-(nd X : ℝ)) := by
  have hs : ∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2 =
      HE.nsq (fun k w => s k (cpt X x0 w)) z * Real.exp (-phla X L (cpt X x0 z)) := by
    unfold HE.nsq
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => pnorm_sq X L (s k) x0 hz
  rw [hs, Real.mul_rpow (HE.nsq_nonneg _ _) (Real.exp_pos _).le, ← Real.exp_mul]
  have hd : densF X x0 z = Real.exp (Real.log (densF X x0 z)) :=
    (Real.exp_log (OntoB.densF_pos hz)).symm
  have hw : Real.exp (-weight X la L ψ x0 bb z) =
      Real.exp (Real.log (densF X x0 z)) * Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) *
        Real.exp (-(-bb * rhF X x0 z)) * Real.exp (-phla X L (cpt X x0 z) * -(nd X : ℝ)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    unfold weight
    ring
  rw [hw, ← hd, kaF, Real.exp_neg (-bb * rhF X x0 z), div_eq_mul_inv]
  ring

end

end GlobalTheory.KronSolve

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem kronSolve : (∀ (r : ℕ) (X : Data E r) (la L : Wt X.Ψ r) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) (ψ : Frame X.Ψ r → ℝ) (x0 : Frame X.Ψ r) (bb m η : ℝ), 0 < nd X → IsOrth X x0 → X.IsSec L w0 → (∀ k, X.IsSec L (s k)) → ContDiffOn ℝ ∞ (fun z => ψ (cpt X x0 z)) (OmF X x0) → 0 ≤ bb → bb < m → 0 < η → (∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, m * leviRh X x0 z ξ ≤ leviO X x0 (phla X la) z ξ - leviDens X x0 z ξ - (nd X : ℝ) * leviO X x0 (phla X L) z ξ + leviO X x0 ψ z ξ) → (∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 2 * η * leviO X x0 (phla X L) z ξ ≤ leviO X x0 (phla X la) z ξ - leviDens X x0 z ξ - (nd X : ℝ) * leviO X x0 (phla X L) z ξ + leviO X x0 ψ z ξ) → (∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 → 0 < leviO X x0 (phla X L) z ξ) → w0 x0 ≠ 0 → (∀ k, s k x0 = 0) → (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => s k (cpt X (x0) z) / w0 (cpt X (x0) z) : V (nd X))) 0).det ≠ 0 → ∃ (ε : ℝ) (χ F : V (nd X) → ℂ), 0 < ε ∧ Metric.closedBall (0 : V (nd X)) (2 * ε) ⊆ OmF X x0 ∧ (∀ z ∈ Metric.closedBall (0 : V (nd X)) (2 * ε), (∀ k, s k (cpt X x0 z) = 0) → z = 0) ∧ Continuous χ ∧ (∀ z, ‖z‖ ≤ ε → χ z = 1) ∧ (∀ z, 2 * ε ≤ ‖z‖ → χ z = 0) ∧ DifferentiableOn ℂ F (OmF X x0) ∧ ∫⁻ z, ENNReal.ofReal (‖χ z - F z‖ ^ 2 * Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z * (∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2) ^ (-(nd X : ℝ))) ∂muF X x0 < ⊤) := by
  intro r X la L w0 s ψ x0 bb m η hn ho hw0 hs hψ hbb hbm hη hm h2 hL hw00 hs0 hdet
  have hU := OntoB.isOpen_OmF X x0
  have h0 := IW.zero_mem_OmF X x0 ho
  have hc0 := IW.cpt_zero X x0
  have hsd : ∀ k, DifferentiableOn ℂ (fun z => s k (cpt X x0 z)) (OmF X x0) :=
    fun k => OntoB.hol_comp X x0 (hs k).1
  have hwd : DifferentiableOn ℂ (fun z => w0 (cpt X x0 z)) (OmF X x0) := OntoB.hol_comp X x0 hw0.1
  set f : V (nd X) → V (nd X) := fun z =>
    (WithLp.toLp 2 fun k => s k (cpt X x0 z) / w0 (cpt X x0 z) : V (nd X)) with hf
  have hfd : DifferentiableAt ℂ f 0 := by
    rw [differentiableAt_euclidean]
    intro k
    have hne : w0 (cpt X x0 0) ≠ 0 := by rw [hc0]; exact hw00
    have h1 := (hsd k).differentiableAt (hU.mem_nhds h0)
    have h2 := (hwd.differentiableAt (hU.mem_nhds h0)).inv hne
    have h3 := h1.mul h2
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
    simp [hf, div_eq_mul_inv]
  have hf0 : f 0 = 0 := by
    ext k
    simp [hf, hc0, hs0 k]
  obtain ⟨δ, hδ, hiso⟩ := HE.iso_zero hfd.hasFDerivAt hdet hf0
  obtain ⟨k0, hk0⟩ := HE.coord_ne_of_det (f := f) hn hdet
  have hk0' : ¬ (fun z => s k0 (cpt X x0 z)) =ᶠ[𝓝 0] 0 := by
    intro h
    apply hk0
    filter_upwards [h] with z hz
    have hz' : s k0 (cpt X x0 z) = 0 := hz
    simp [hf, hz']
  have hgn := HE.hgn_of hU (OmFConnStatement_holds r X x0 ho) (hsd k0) h0 hk0'
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hU 0 h0
  set ε : ℝ := min δ ρ / 4 with hεdef
  have hmin : 0 < min δ ρ := lt_min hδ hρ
  have hε : 0 < ε := by positivity
  have hε1 : 2 * ε ≤ δ := by have := min_le_left δ ρ; linarith
  have hε2 : 2 * ε < ρ := by have := min_le_right δ ρ; linarith
  have hcb : Metric.closedBall (0 : V (nd X)) (2 * ε) ⊆ OmF X x0 :=
    (Metric.closedBall_subset_ball hε2).trans hball
  have hiso' : ∀ z ∈ Metric.closedBall (0 : V (nd X)) (2 * ε),
      (∀ k, s k (cpt X x0 z) = 0) → z = 0 := by
    intro z hz hsz
    refine hiso z (Metric.closedBall_subset_closedBall hε1 hz) ?_
    ext k
    simp [hf, hsz k]
  have hW := KronSolve.weight_contDiffOn X la L ψ x0 bb hψ
  have hWpos : ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
      0 < (leviV (nd X) (fun w => ((KronSolve.weight X la L ψ x0 bb w : ℝ) : ℂ)) z ξ).re := by
    intro z hz ξ hξ
    rw [KronSolve.levi_weight X la L ψ x0 bb hψ hz ξ]
    have a1 := hm z hz ξ
    have a2 := h2 z hz ξ
    have a3 := hL z hz ξ hξ
    set Q := leviO X x0 (phla X la) z ξ - leviDens X x0 z ξ -
      (nd X : ℝ) * leviO X x0 (phla X L) z ξ + leviO X x0 ψ z ξ
    set R := leviRh X x0 z ξ
    have hQ : 0 < Q := lt_of_lt_of_le (by positivity) a2
    have hm0 : 0 < m := lt_of_le_of_lt hbb hbm
    have : 0 < m * (Q - bb * R) := by
      have b1 : 0 < (m - bb) * Q := mul_pos (by linarith) hQ
      have b2 : 0 ≤ bb * (Q - m * R) := mul_nonneg hbb (by linarith)
      nlinarith
    exact (mul_pos_iff_of_pos_left hm0).1 this
  have hWnn : ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      0 ≤ (leviV (nd X) (fun w => ((KronSolve.weight X la L ψ x0 bb w : ℝ) : ℂ)) z ξ).re := by
    intro z hz ξ
    by_cases hξ : ξ = 0
    · subst hξ
      simp [leviV]
    · exact (hWpos z hz ξ hξ).le
  obtain ⟨c, hc, hunif⟩ := HE.levi_unif hU hW (isCompact_closedBall (0 : V (nd X)) (2 * ε)) hcb
    (fun z hz => hWpos z (hcb hz))
  have he : ContDiffOn ℝ ∞ (eF X x0) (OmF X x0) :=
    fun z hz => (ExF.eF_contDiffAt X x0 ho hz).contDiffWithinAt
  have hel : ∀ y ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      0 ≤ (leviV (nd X) (fun w => ((eF X x0 w : ℝ) : ℂ)) y ξ).re := by
    intro y hy ξ
    have e1 : (fun y : V (nd X) => ((eF X x0 y : ℝ) : ℂ)) =
        fun y => ((rhF X x0 y + Real.log (1 + ‖y‖ ^ 2) : ℝ) : ℂ) := rfl
    rw [e1, Y.LocalMaximumSecondDerivative.leviV_ofReal_add
      ((ExF.rhF_contDiffAt X x0 ho hy).of_le HE.two_le_inf)
      (ExF.T_cd.contDiffAt.of_le HE.two_le_inf) ξ, Complex.add_re]
    exact add_nonneg (ExF.levi_rhF_nonneg X x0 ho hy ξ) (ExF.leviT_nonneg _ ξ)
  have he0 : ∀ y ∈ OmF X x0, 0 ≤ eF X x0 y := fun y hy =>
    add_nonneg (ExF.rhF_nonneg X x0 ho hy) (Real.log_nonneg (by nlinarith [sq_nonneg ‖y‖]))
  obtain ⟨F, hFd, hF⟩ := HE.interp_euclid hU (eF X x0) he hel (ExF.isCompact_subF X x0 ho) he0
    (fun k w => s k (cpt X x0 w)) hsd k0 hgn (KronSolve.weight X la L ψ x0 bb) hW hWnn ε hε hcb hiso'
    c hc hunif
  refine ⟨ε, HE.cut ε hε, F, hε, hcb, hiso', (HE.cut_contDiff ε hε).continuous,
    fun z hz => HE.cut_one ε hε hz, fun z hz => HE.cut_zero ε hε hz, hFd, ?_⟩
  refine lt_of_eq_of_lt ?_ hF
  unfold muF
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ (OntoC.measurable_densF X x0)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setLIntegral_congr_fun hU.measurableSet fun z hz => ?_
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (OntoB.densF_pos hz).le, KronSolve.integrand_eq X la L ψ x0 bb s _ hz]

end GlobalTheory
end
