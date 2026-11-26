module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricFrameEqRiemannFormAtInteriorPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionNewCellMultiplicityLt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PunctPolydiscCoverLatticeBasisRealHolomorphic
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PunctPolydiscCoverLatticeBasisRealHolomorphic
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.ShFam.Hor.LogCh

theorem latBasis_logCover_real_holo : ∀ (n a g r : ℕ) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ), IsLatFam (Metric.ball 0 1) K → ContinuousOn lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → r = 2 * g ∧ (∀ s ∈ logDom n a, LinearIndependent ℝ (lam s)) ∧ ∀ (j : Fin r) (k : Fin g), DifferentiableOn ℂ (fun s => lam s j k) (logDom n a) := by
  intro n a g r K lam hK hlam hB

  have hne : (fun k : Fin n => if (k : ℕ) < a then (-1 : ℂ) else 0) ∈ logDom n a := by
    intro k
    by_cases h : (k : ℕ) < a <;> simp [h]
  obtain ⟨hOpen, -, hAn, hMaps⟩ := GlobalTheory.logDom_chart_props n a

  have hmem : ∀ s ∈ logDom n a, ∀ j, lam s j ∈ K (logExp a s) := by
    intro s hs j
    refine ((hB s hs).2.2 _).2 ⟨Pi.single j 1, ?_⟩
    simp [Pi.single_apply]
  have hreal : ∀ s ∈ logDom n a, LinearIndependent ℝ (lam s) := by
    intro s hs
    obtain ⟨hli, hsp, hK'⟩ := hB s hs
    have hspanK : Submodule.span ℝ (K (logExp a s)) = ⊤ := by
      rw [eq_top_iff, ← hsp]
      exact Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact hmem s hs j)
    exact (GlobalTheory.LatReal.isRealBasis_of_isLatFam n g r (Metric.ball 0 1) K (logExp a s) (lam s) hK
      (hMaps hs) hspanK hli hK').1
  refine ⟨?_, hreal, ?_⟩
  · set s₀ := (fun k : Fin n => if (k : ℕ) < a then (-1 : ℂ) else 0)
    have hli := hreal s₀ hne
    have hsp := (hB s₀ hne).2.1
    have h1 := linearIndependent_iff_card_eq_finrank_span.1 hli
    rw [Set.finrank, hsp, finrank_top, Fintype.card_fin] at h1
    rw [h1, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  · intro j k
    have hF := IsLatFam.pullback_analytic n n g (Metric.ball 0 1) (logDom n a) K (logExp a) hK hOpen
      (fun s _ => hAn s) hMaps
    intro s₀ hs₀
    have hnhds : logDom n a ∈ 𝓝 s₀ := hOpen.mem_nhds hs₀
    obtain ⟨ζ, hζ0, hζa, hev⟩ := hF.2.2.2 s₀ hs₀ (lam s₀ j) (hmem s₀ hs₀ j)
    have hc : ContinuousAt (fun s => (s, lam s j)) s₀ :=
      continuousAt_id.prodMk ((continuous_apply j).continuousAt.comp (hlam.continuousAt hnhds))
    have hev' : ∀ᶠ s in 𝓝 s₀, (lam s j ∈ K (logExp a s) ↔ lam s j = ζ s) := by
      have := hc.tendsto.eventually hev
      simpa [hζ0] using this
    have heq : (fun s => lam s j) =ᶠ[𝓝 s₀] ζ := by
      filter_upwards [hev', hnhds] with s h1 h2
      exact h1.1 (hmem s h2 j)
    have hd : DifferentiableAt ℂ (fun s => lam s j) s₀ :=
      hζa.differentiableAt.congr_of_eventuallyEq heq
    exact (differentiableAt_pi.1 hd k).differentiableWithinAt

end GlobalTheory.ShFam.Hor.LogCh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PunctPolydiscCoverLatticeBasisRealHolomorphicStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.punctPolydiscCover_latticeBasis_real_holomorphic : ∀ (n a g r : ℕ) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ), IsLatFam (Metric.ball 0 1) K → ContinuousOn lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → r = 2 * g ∧ (∀ s ∈ logDom n a, LinearIndependent ℝ (lam s)) ∧ ∀ (j : Fin r) (k : Fin g), DifferentiableOn ℂ (fun s => lam s j k) (logDom n a) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.latBasis_logCover_real_holo | exact GlobalTheory.ShFam.Hor.LogCh.latBasis_logCover_real_holo | (intros; apply GlobalTheory.ShFam.Hor.LogCh.latBasis_logCover_real_holo <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodChartRescaleBallToUnitPolydisc
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodChartRescaleBallToUnitPolydisc
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase.HodgeChart


open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram in
theorem periodChart_rescale_ball : ∀ (n a g rk : ℕ) (ha : a ≤ n) (ρ : ℝ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < ρ → ρ ≤ 1 → rk ≤ g → (∀ j k, DifferentiableOn ℂ (fun z => τ₀ z j k) (Metric.ball 0 ρ)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (τ₀ z).IsSymm) → (∀ i, ((B i).map (Int.cast : ℤ → ℝ)).PosSemidef) → (∀ i (j k : Fin g), (rk ≤ j.val ∨ rk ≤ k.val) → B i j k = 0) → (((∑ i, B i).map (Int.cast : ℤ → ℝ)).submatrix (Subtype.val : {j : Fin g // j.val < rk} → Fin g) Subtype.val).PosDef → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (((τ₀ z).map Complex.im).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val).PosDef) → GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk (fun u => τ₀ (ρ • u) + ∑ i, (((Real.log ρ : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) • (B i).map (Int.cast : ℤ → ℂ)) B ∧ ∀ z : Fin n → ℂ, (∀ i : Fin a, z (Fin.castLE ha i) ≠ 0) → GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha (fun u => τ₀ (ρ • u) + ∑ i, (((Real.log ρ : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) • (B i).map (Int.cast : ℤ → ℂ)) B (ρ⁻¹ • z) = GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B z := by
  intro n a g rk ha ρ τ₀ B hr hr1 hrk hholo hsymm hpsd hsupp htoric habel
  set cst : ℂ := (((Real.log ρ : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) with hcst
  have him : cst.im = -Real.log ρ / (2 * Real.pi) := by
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have e : cst = ((-Real.log ρ / (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      rw [hcst]; push_cast; field_simp; rw [Complex.I_sq]; ring
    rw [e, Complex.im_ofReal_mul, Complex.I_im, _root_.mul_one]
  have hBs : ∀ i (j k : Fin g), B i k j = B i j k := fun i j k => by
    have := (hpsd i).isHermitian.apply j k
    simp at this
    exact_mod_cast this
  have hmaps : ∀ z ∈ polydisc n 1, ρ • z ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
    intro u hu
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hr.le]
    have : ‖u‖ < 1 := (pi_norm_lt_iff one_pos).2 hu
    calc ρ * ‖u‖ < ρ * 1 := by gcongr
      _ = ρ := _root_.mul_one ρ
  have hdiff : DifferentiableOn ℂ (fun z : Fin n → ℂ => ρ • z) (polydisc n 1) :=
    ((differentiable_id.const_smul (ρ : ℂ)).differentiableOn).congr fun u _ => by
      funext k; simp [Complex.real_smul]
  refine ⟨⟨hrk, fun j k => ?_, fun z hz => ?_, hpsd, hsupp, htoric, fun z hz => ?_⟩, fun u hu => ?_⟩
  · have h1 := (hholo j k).comp hdiff hmaps
    refine (h1.add (differentiableOn_const (∑ i, cst * (B i j k : ℂ)))).congr fun z _ => ?_
    simp [Matrix.add_apply, Matrix.sum_apply, Function.comp]
  · refine Matrix.IsSymm.ext fun j k => ?_
    have := (hsymm _ (hmaps z hz)).apply j k
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, hBs, this]
  · have h1 := habel _ (hmaps z hz)
    convert h1 using 1
    ext ⟨j, hj⟩ ⟨k, hk⟩
    simp [Matrix.sum_apply, hsupp _ j k (Or.inl hj)]
  · have hρu : ρ • (ρ⁻¹ • u) = u := smul_inv_smul₀ hr.ne' u
    ext j k
    have hu' : ∀ i : Fin a, tlog ((ρ⁻¹ • u) (Fin.castLE ha i)) = Real.log ρ / (2 * Real.pi) + tlog (u (Fin.castLE ha i)) := by
      intro i
      rw [Pi.smul_apply, tlog, tlog, norm_smul, Real.norm_of_nonneg (inv_pos.2 hr).le,
        Real.log_mul (inv_pos.2 hr).ne' (norm_ne_zero_iff.2 (hu i)), Real.log_inv]
      ring
    simp only [hodgeGram, imPeriod, Matrix.map_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      hu', hρu, Complex.add_im, Complex.im_sum, smul_eq_mul]
    push_cast
    simp only [Complex.smul_im, Complex.intCast_im, Complex.intCast_re, smul_eq_mul, him, add_mul, Finset.sum_add_distrib]
    simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, mul_zero, add_zero, him]
    push_cast
    simp only [zero_add]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring

end GlobalTheory.LieBase.HodgeChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodChartRescaleBallToUnitPolydiscStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodChart_rescale_ball_to_unitPolydisc : ∀ (n a g rk : ℕ) (ha : a ≤ n) (ρ : ℝ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < ρ → ρ ≤ 1 → rk ≤ g → (∀ j k, DifferentiableOn ℂ (fun z => τ₀ z j k) (Metric.ball 0 ρ)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (τ₀ z).IsSymm) → (∀ i, ((B i).map (Int.cast : ℤ → ℝ)).PosSemidef) → (∀ i (j k : Fin g), (rk ≤ j.val ∨ rk ≤ k.val) → B i j k = 0) → (((∑ i, B i).map (Int.cast : ℤ → ℝ)).submatrix (Subtype.val : {j : Fin g // j.val < rk} → Fin g) Subtype.val).PosDef → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (((τ₀ z).map Complex.im).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val).PosDef) → GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk (fun u => τ₀ (ρ • u) + ∑ i, (((Real.log ρ : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) • (B i).map (Int.cast : ℤ → ℂ)) B ∧ ∀ z : Fin n → ℂ, (∀ i : Fin a, z (Fin.castLE ha i) ≠ 0) → GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha (fun u => τ₀ (ρ • u) + ∑ i, (((Real.log ρ : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) • (B i).map (Int.cast : ℤ → ℂ)) B (ρ⁻¹ • z) = GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B z := by
  first | exact @GlobalTheory.LieBase.HodgeChart.periodChart_rescale_ball | exact GlobalTheory.LieBase.HodgeChart.periodChart_rescale_ball | (intros; apply GlobalTheory.LieBase.HodgeChart.periodChart_rescale_ball <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExpChartRescale
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem isExpChart_rescale : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (n g : ℕ) (e : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g) (P : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (ρ : ℝ), IsExpChart e ex → 0 < ρ → ρ ≤ 1 → (∀ i j, DifferentiableOn ℂ (fun z => P z i j) (Metric.ball 0 ρ)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, IsUnit (P z).det) → ∃ ch : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr Z) σ) (Fin n → ℂ), IsExpChart ch (fun x v => ex x (P (e x) *ᵥ v)) ∧ (∀ x, x ∈ ch.source ↔ x ∈ e.source ∧ e x ∈ Metric.ball (0 : Fin n → ℂ) ρ) ∧ ∀ x ∈ ch.source, e x = ρ • ch x := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ n g e ex P ρ hE hρ hρ1 hP hPu
  obtain ⟨htarget, hholE, hsymmHol, hadd, hjoint, htan⟩ := hE
  have hρ0 : ρ ≠ 0 := hρ.ne'
  have hSo : IsOpen (e.source ∩ e ⁻¹' Metric.ball (0 : Fin n → ℂ) ρ) :=
    e.isOpen_inter_preimage Metric.isOpen_ball
  let ch : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr Z) σ) (Fin n → ℂ) :=
    (e.restrOpen _ hSo).transHomeomorph (Homeomorph.smulOfNeZero (ρ⁻¹ : ℝ) (inv_ne_zero hρ0))
  have hch : ∀ x, ch x = (ρ⁻¹ : ℝ) • e x := fun x ↦ rfl
  have hchs : ∀ z, ch.symm z = e.symm (ρ • z) := fun z ↦ by
    show e.symm ((ρ⁻¹ : ℝ)⁻¹ • z) = _
    rw [inv_inv]
  have hsrc : ∀ x, x ∈ ch.source ↔ x ∈ e.source ∧ e x ∈ Metric.ball (0 : Fin n → ℂ) ρ := fun x ↦ by
    show x ∈ e.source ∩ (e.source ∩ e ⁻¹' Metric.ball (0 : Fin n → ℂ) ρ) ↔ _
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    tauto
  have hball : ∀ z : Fin n → ℂ, ρ • z ∈ Metric.ball (0 : Fin n → ℂ) ρ ↔ z ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
    intro z
    simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  have hsub : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ρ • z ∈ e.target := fun z hz ↦ by
    rw [htarget]; exact Metric.ball_subset_ball hρ1 ((hball z).2 hz)
  have htgt : ch.target = Metric.ball 0 1 := by
    ext z
    show (Homeomorph.smulOfNeZero (ρ⁻¹ : ℝ) (inv_ne_zero hρ0)).symm z ∈
      e.target ∩ e.symm ⁻¹' (e.source ∩ e ⁻¹' Metric.ball (0 : Fin n → ℂ) ρ) ↔ _
    have hz : (Homeomorph.smulOfNeZero (ρ⁻¹ : ℝ) (inv_ne_zero hρ0)).symm z = ρ • z := by
      show (ρ⁻¹ : ℝ)⁻¹ • z = _
      rw [inv_inv]
    rw [hz]
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨h1, -, h⟩
      rw [e.right_inv h1] at h
      exact (hball z).1 h
    · intro h
      have h2 := hsub z h
      exact ⟨h2, e.map_target h2, by rw [e.right_inv h2]; exact (hball z).2 h⟩
  refine ⟨ch, ⟨htgt, ?_, ?_, ?_, ?_, ?_⟩, hsrc, ?_⟩
  · intro k V _ _ _ B x hB hx hm
    have := hholE k V B x hB hx fun b hb ↦ ((hsrc _).1 (hm hb)).1
    simp only [hch, Pi.smul_apply]
    exact this.const_smul (ρ⁻¹ : ℝ)
  · rw [htgt]
    have := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun z : Fin n → ℂ ↦ ρ • z) hsymmHol Metric.isOpen_ball
      (differentiableOn_id.const_smul ρ) fun z hz ↦ hsub z hz
    refine GlobalTheory.HolPeriods.isHolTo_congr this fun z _ ↦ ?_
    simp only [hchs]
  · intro x hx v w
    simp only [Matrix.mulVec_add]
    exact hadd x ((hsrc x).1 hx).1 _ _
  · rw [htgt]
    have hφ : DifferentiableOn ℂ (fun zw : (Fin n → ℂ) × (Fin g → ℂ) ↦ (ρ • zw.1, P (ρ • zw.1) *ᵥ zw.2))
        (Metric.ball 0 1 ×ˢ Set.univ) := by
      refine (differentiableOn_fst.const_smul ρ).prodMk ?_
      refine differentiableOn_pi.2 fun i ↦ ?_
      simp only [Matrix.mulVec, dotProduct]
      refine DifferentiableOn.fun_sum fun j _ ↦ ?_
      exact ((hP i j).comp (differentiableOn_fst.const_smul ρ) fun zw (hzw : zw ∈ Metric.ball (0 : Fin n → ℂ) 1 ×ˢ Set.univ) ↦ (hball _).2 hzw.1).mul
        (by fun_prop : Differentiable ℂ fun zw : (Fin n → ℂ) × (Fin g → ℂ) ↦ zw.2 j).differentiableOn
    have := GlobalTheory.HolPeriods.isHolTo_comp hjoint (Metric.isOpen_ball.prod isOpen_univ) hφ
      fun zw hzw ↦ ⟨hsub _ hzw.1, Set.mem_univ _⟩
    refine GlobalTheory.HolPeriods.isHolTo_congr this fun zw hzw ↦ ?_
    dsimp only
    rw [hchs, e.right_inv (hsub _ hzw.1)]
  · intro x hx
    have hxe := (hsrc x).1 hx
    have hhol : IsHolTo Set.univ (fun w ↦ (ex x w).left) := by
      have := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun w : Fin g → ℂ ↦ (e x, w)) hjoint isOpen_univ
        ((differentiableOn_const _).prodMk differentiableOn_id)
        fun w _ ↦ Set.mk_mem_prod (e.map_source hxe.1) (Set.mem_univ w)
      refine GlobalTheory.HolPeriods.isHolTo_congr this fun w _ ↦ ?_
      dsimp only
      rw [e.left_inv hxe.1]
    have hex : IsExpAt Z.t (x.1 ≫ genι Z) (ex x) := ⟨hadd x hxe.1, (htan x hxe.1).1, (htan x hxe.1).2⟩
    have := isExpAt_mulVec H _ Z.t (x.1 ≫ genι Z) g (ex x) (P (e x)) (hPu _ hxe.2) hhol hex
    exact ⟨this.2.1, this.2.2⟩
  · intro x _
    rw [hch, smul_smul, mul_inv_cancel₀ hρ0, one_smul]

end GlobalTheory.ShFam.Hor.LogCh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonIntKernelPsdBlockNotPosDef
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonIntKernelPsdBlockNotPosDef
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem intPsd_common_kernel_of_sum_not_posDef : ∀ (a g rk : ℕ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), (∀ k, ((B k).map (Int.cast : ℤ → ℝ)).PosSemidef) → (∀ k (j l : Fin g), (rk ≤ j.val ∨ rk ≤ l.val) → B k j l = 0) → ¬ (((∑ k, B k).map (Int.cast : ℤ → ℝ)).submatrix (Subtype.val : {j : Fin g // j.val < rk} → Fin g) Subtype.val).PosDef → ∃ v : Fin g → ℤ, v ≠ 0 ∧ (∀ j : Fin g, rk ≤ j.val → v j = 0) ∧ ∀ k, (B k).mulVec v = 0 := by
  intro a g rk B hpsd hsupp hnot
  set S : Matrix (Fin g) (Fin g) ℤ := ∑ k, B k with hS
  let e : {j : Fin g // j.val < rk} → Fin g := Subtype.val
  have hcast : ∀ (M : Matrix (Fin g) (Fin g) ℤ) (u : Fin g → ℤ) (i : Fin g),
      ((M.map (Int.cast : ℤ → ℝ)) *ᵥ (fun j => (u j : ℝ))) i = (((M *ᵥ u) i : ℤ) : ℝ) := by
    intro M u i
    simp [mulVec, dotProduct]
  have hSmap : S.map (Int.cast : ℤ → ℝ) = ∑ k, (B k).map (Int.cast : ℤ → ℝ) := by
    ext i j; simp [hS, Matrix.sum_apply]
  have hSR : ((S.map (Int.cast : ℤ → ℝ)).submatrix e e).PosSemidef := by
    rw [hSmap]
    exact (posSemidef_sum _ (fun k _ => hpsd k)).submatrix e
  have hdetR : ((S.map (Int.cast : ℤ → ℝ)).submatrix e e).det = 0 := by
    by_contra hdet
    apply hnot
    rw [posDef_iff_dotProduct_mulVec]
    refine ⟨hSR.isHermitian, fun x hx => ?_⟩
    have hnn := (posSemidef_iff_dotProduct_mulVec.1 hSR).2 x
    rcases hnn.lt_or_eq with h | h
    · exact h
    · exfalso
      have hk := hSR.dotProduct_mulVec_zero_iff.1 h.symm
      exact hdet (exists_mulVec_eq_zero_iff.1 ⟨x, hx, hk⟩)
  have hdetZ : (S.submatrix e e).det = 0 := by
    have h := (Int.castRingHom ℝ).map_det (S.submatrix e e)
    have h2 : (Int.castRingHom ℝ).mapMatrix (S.submatrix e e)
        = (S.map (Int.cast : ℤ → ℝ)).submatrix e e := rfl
    rw [h2, hdetR, eq_intCast] at h
    exact_mod_cast h
  obtain ⟨w, hw0, hw⟩ := exists_mulVec_eq_zero_iff.2 hdetZ
  let v : Fin g → ℤ := fun j => if h : j.val < rk then w ⟨j, h⟩ else 0
  have hSi : ∀ i j : Fin g, rk ≤ i.val → S i j = 0 := by
    intro i j hi
    simp [hS, Matrix.sum_apply, hsupp _ i j (Or.inl hi)]
  have hsplit : ∀ i : Fin g, (S *ᵥ v) i = ∑ j : {j : Fin g // j.val < rk}, S i j * w j := by
    intro i
    simp only [mulVec, dotProduct]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun j : Fin g => j.val < rk)]
    have h2 : ∑ j : {j : Fin g // ¬ j.val < rk}, S i j * v j = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [v, j.2]
    rw [h2, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [v, j.2]
  have hSv : S *ᵥ v = 0 := by
    funext i
    rw [hsplit]
    by_cases hi : i.val < rk
    · have := congrFun hw ⟨i, hi⟩
      simpa [mulVec, dotProduct, e] using this
    · push_neg at hi
      simp [hSi i _ hi]
  refine ⟨v, ?_, ?_, ?_⟩
  · intro hv
    apply hw0
    funext j
    have := congrFun hv j.val
    simpa [v, j.2] using this
  · intro j hj
    simp [v, not_lt.2 hj]
  · intro k
    let vR : Fin g → ℝ := fun j => (v j : ℝ)
    have hQnn : ∀ k, 0 ≤ star vR ⬝ᵥ (((B k).map (Int.cast : ℤ → ℝ)) *ᵥ vR) := fun k =>
      (posSemidef_iff_dotProduct_mulVec.1 (hpsd k)).2 vR
    have hsum : ∑ k, star vR ⬝ᵥ (((B k).map (Int.cast : ℤ → ℝ)) *ᵥ vR) = 0 := by
      rw [← dotProduct_sum, ← sum_mulVec, ← hSmap]
      have : (S.map (Int.cast : ℤ → ℝ)) *ᵥ vR = 0 := by
        funext i; rw [hcast, hSv]; simp
      rw [this, dotProduct_zero]
    have hk0 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hQnn k)).1 hsum k (Finset.mem_univ _)
    have hker := (hpsd k).dotProduct_mulVec_zero_iff.1 hk0
    funext i
    have := congrFun hker i
    rw [hcast] at this
    simpa using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonIntKernelPsdBlockNotPosDefStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_int_kernel_psd_block_not_posDef : ∀ (a g rk : ℕ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), (∀ k, ((B k).map (Int.cast : ℤ → ℝ)).PosSemidef) → (∀ k (j l : Fin g), (rk ≤ j.val ∨ rk ≤ l.val) → B k j l = 0) → ¬ (((∑ k, B k).map (Int.cast : ℤ → ℝ)).submatrix (Subtype.val : {j : Fin g // j.val < rk} → Fin g) Subtype.val).PosDef → ∃ v : Fin g → ℤ, v ≠ 0 ∧ (∀ j : Fin g, rk ≤ j.val → v j = 0) ∧ ∀ k, (B k).mulVec v = 0 := by
  first | exact @GlobalTheory.intPsd_common_kernel_of_sum_not_posDef | exact GlobalTheory.intPsd_common_kernel_of_sum_not_posDef | (intros; apply GlobalTheory.intPsd_common_kernel_of_sum_not_posDef <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntIsometryFixingRowSpaceSymplecticShift
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntIsometryFixingRowSpaceSymplecticShift
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem symplecticPair_decomp {g r : ℕ} (hr : r = 2 * g) (M' : Matrix (Fin r) (Fin r) ℚ)
    (hM : M'ᵀ = -M') (ε φ : Matrix (Fin g) (Fin r) ℚ) (h1 : ε * M' * εᵀ = 0)
    (h2 : φ * M' * φᵀ = 0) (h3 : φ * M' * εᵀ = 1) (X : Matrix (Fin g) (Fin r) ℚ) :
    X = -(X * M' * φᵀ) * ε + (X * M' * εᵀ) * φ := by
  have h4 : ε * M' * φᵀ = -1 := by
    have := congrArg Matrix.transpose h3
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hM,
      Matrix.transpose_one] at this
    rw [← neg_neg (ε * M' * φᵀ), ← this]
    simp [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
  have hPR : Matrix.fromRows ε φ * (M' * Matrix.fromCols (-φᵀ) εᵀ) = 1 := by
    rw [Matrix.mul_fromCols, Matrix.fromRows_mul_fromCols, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_neg, Matrix.mul_neg,
      h1, h2, h3, h4, neg_neg, neg_zero, Matrix.fromBlocks_one]
  let e : Fin g ⊕ Fin g ≃ Fin r := finSumFinEquiv.trans (finCongr (by omega))
  have hRP : (M' * Matrix.fromCols (-φᵀ) εᵀ) * Matrix.fromRows ε φ = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv e).mp hPR
  calc X = X * ((M' * Matrix.fromCols (-φᵀ) εᵀ) * Matrix.fromRows ε φ) := by
        rw [hRP, Matrix.mul_one]
    _ = -(X * M' * φᵀ) * ε + (X * M' * εᵀ) * φ := by
        rw [Matrix.mul_assoc M', Matrix.fromCols_mul_fromRows]
        simp only [Matrix.mul_add, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]

theorem isometry_fixing_rowSpace_shift : ∀ (g r r₀ rk : ℕ) (M T : Matrix (Fin r) (Fin r) ℤ) (c : Matrix (Fin r₀) (Fin r) ℤ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (β : Matrix (Fin g) (Fin r₀) ℚ), r = 2 * g → Mᵀ = -M → T * M * Tᵀ = M → c * T = c → (α * c.map (Int.cast : ℤ → ℚ)) * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * φᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 1 → (∀ j : Fin g, rk ≤ j.val → ∀ m, φ j m = (β * c.map (Int.cast : ℤ → ℚ)) j m) → ∃ b : Matrix (Fin g) (Fin g) ℚ, (∀ i j : Fin g, (rk ≤ i.val ∨ rk ≤ j.val) → b i j = 0) ∧ φ * T.map (Int.cast : ℤ → ℚ) = φ + bᵀ * (α * c.map (Int.cast : ℤ → ℚ)) := by
  intro g r r₀ rk M T c α φ β hr hMt hTM hcT hεε hφφ hφε hβ
  have keyZ : T * M * cᵀ = M * cᵀ := by
    calc T * M * cᵀ = T * M * (c * T)ᵀ := by rw [hcT]
      _ = T * M * Tᵀ * cᵀ := by rw [Matrix.transpose_mul, Matrix.mul_assoc (T * M)]
      _ = M * cᵀ := by rw [hTM]
  have hcTZ : c * T = c := hcT
  have map_mul' : ∀ {a b d : ℕ} (A : Matrix (Fin a) (Fin b) ℤ) (B : Matrix (Fin b) (Fin d) ℤ),
      (A * B).map (Int.cast : ℤ → ℚ) = A.map (Int.cast : ℤ → ℚ) * B.map (Int.cast : ℤ → ℚ) :=
    fun A B => Matrix.map_mul (f := Int.castRingHom ℚ)
  set M' := M.map (Int.cast : ℤ → ℚ) with hM'
  set T' := T.map (Int.cast : ℤ → ℚ) with hT'
  set c' := c.map (Int.cast : ℤ → ℚ) with hc'
  have key : T' * M' * c'ᵀ = M' * c'ᵀ := by
    have := congrArg (fun A => A.map (Int.cast : ℤ → ℚ)) keyZ
    simpa only [map_mul', Matrix.transpose_map] using this
  have hcT' : c' * T' = c' := by
    have := congrArg (fun A => A.map (Int.cast : ℤ → ℚ)) hcTZ
    simpa only [map_mul'] using this
  have hMt' : M'ᵀ = -M' := by
    rw [hM', ← Matrix.transpose_map, hMt]; ext i j; simp
  set ε := α * c' with hε
  set X := φ * T' - φ with hX
  have hXc : X * M' * c'ᵀ = 0 := by
    rw [hX, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc φ T', Matrix.mul_assoc φ (T' * M'),
      key, Matrix.mul_assoc φ M', sub_self]
  have hXε : X * M' * εᵀ = 0 := by
    rw [hε, Matrix.transpose_mul, ← Matrix.mul_assoc, hXc, Matrix.zero_mul]
  have hdec := symplecticPair_decomp hr M' hMt' ε φ hεε hφφ hφε X
  rw [hXε, Matrix.zero_mul, add_zero] at hdec
  refine ⟨-(X * M' * φᵀ)ᵀ, ?_, ?_⟩
  · intro i j hij
    simp only [Matrix.neg_apply, Matrix.transpose_apply, neg_eq_zero]
    rcases hij with hi | hj
    ·
      have : (X * M' * φᵀ) j i = (X * M' * c'ᵀ * βᵀ) j i := by
        rw [Matrix.mul_assoc (X * M') c'ᵀ, ← Matrix.transpose_mul]
        simp only [Matrix.mul_apply, Matrix.transpose_apply]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hβ i hi m]
        simp only [Matrix.mul_apply]
      rw [this, hXc, Matrix.zero_mul, Matrix.zero_apply]
    · have hrow : ∀ m, X j m = 0 := by
        intro m
        have hφj : ∀ m, φ j m = (β * c') j m := hβ j hj
        rw [hX, Matrix.sub_apply, Matrix.mul_apply, hφj m]
        have : ∑ k, φ j k * T' k m = ((β * c') * T') j m := by
          simp only [Matrix.mul_apply]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hφj k]; simp only [Matrix.mul_apply]
        rw [this, Matrix.mul_assoc, hcT', sub_self]
      simp only [Matrix.mul_apply, hrow, zero_mul, Finset.sum_const_zero]
  · rw [Matrix.transpose_neg, Matrix.transpose_transpose, ← hdec, hX]
    abel

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntIsometryFixingRowSpaceSymplecticShiftStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intIsometry_fixing_rowSpace_symplectic_shift : ∀ (g r r₀ rk : ℕ) (M T : Matrix (Fin r) (Fin r) ℤ) (c : Matrix (Fin r₀) (Fin r) ℤ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (β : Matrix (Fin g) (Fin r₀) ℚ), r = 2 * g → Mᵀ = -M → T * M * Tᵀ = M → c * T = c → (α * c.map (Int.cast : ℤ → ℚ)) * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * φᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 1 → (∀ j : Fin g, rk ≤ j.val → ∀ m, φ j m = (β * c.map (Int.cast : ℤ → ℚ)) j m) → ∃ b : Matrix (Fin g) (Fin g) ℚ, (∀ i j : Fin g, (rk ≤ i.val ∨ rk ≤ j.val) → b i j = 0) ∧ φ * T.map (Int.cast : ℤ → ℚ) = φ + bᵀ * (α * c.map (Int.cast : ℤ → ℚ)) := by
  first | exact @GlobalTheory.isometry_fixing_rowSpace_shift | exact GlobalTheory.isometry_fixing_rowSpace_shift | (intros; apply GlobalTheory.isometry_fixing_rowSpace_shift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOnRationalFramePeriodMatrixLogCove
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOnRationalFramePeriodMatrixLogCove
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodFrame

private theorem differentiableOn_finsetProd' {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {Idx : Type}
    (u : Finset Idx) (f : Idx → E → ℂ) {S : Set E} (h : ∀ i ∈ u, DifferentiableOn ℂ (f i) S) :
    DifferentiableOn ℂ (fun s => ∏ i ∈ u, f i s) S := by
  classical
  revert h
  refine Finset.induction_on u ?_ ?_
  · intro _
    simp only [Finset.prod_empty]
    exact differentiableOn_const _
  · intro a u ha ih h
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a u)).fun_mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem differentiableOn_det_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    {M : E → Matrix (Fin g) (Fin g) ℂ} {S : Set E} (h : ∀ i j, DifferentiableOn ℂ (fun s => M s i j) S) :
    DifferentiableOn ℂ (fun s => (M s).det) S := by
  have hdet : (fun s => (M s).det) = fun s => ∑ σ : Equiv.Perm (Fin g),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M s (σ i) i := by
    funext s
    exact Matrix.det_apply' (M s)
  rw [hdet]
  apply DifferentiableOn.fun_sum
  intro σ _
  apply DifferentiableOn.const_mul
  exact differentiableOn_finsetProd' Finset.univ (fun i s => M s (σ i) i) (fun i _ => h (σ i) i)

theorem differentiableOn_inv_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    {M : E → Matrix (Fin g) (Fin g) ℂ} {S : Set E} (h : ∀ i j, DifferentiableOn ℂ (fun s => M s i j) S)
    (hu : ∀ s ∈ S, IsUnit (M s).det) (i j : Fin g) :
    DifferentiableOn ℂ (fun s => (M s)⁻¹ i j) S := by
  have hdet : DifferentiableOn ℂ (fun s => (M s).det) S := differentiableOn_det_of_entries h
  have hadj : DifferentiableOn ℂ (fun s => (M s).adjugate i j) S := by
    have hupd : ∀ k l, DifferentiableOn ℂ (fun s => ((M s).updateRow j (Pi.single i 1)) k l) S := by
      intro k l
      by_cases hk : k = j
      · subst hk
        simp only [Matrix.updateRow_self]
        exact differentiableOn_const _
      · simp only [Matrix.updateRow_ne hk]
        exact h k l
    have := differentiableOn_det_of_entries hupd
    simpa only [Matrix.adjugate_apply] using this
  have hinv : DifferentiableOn ℂ (fun s => ((M s).det)⁻¹) S :=
    hdet.fun_inv fun s hs => (hu s hs).ne_zero
  have heq : (fun s => (M s)⁻¹ i j) = fun s => ((M s).det)⁻¹ * (M s).adjugate i j := by
    funext s
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [heq]
  exact hinv.fun_mul hadj

theorem differentiableOn_combMat_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g r : ℕ}
    {l : E → Fin r → Fin g → ℂ} {S : Set E} (ε : Matrix (Fin g) (Fin r) ℚ)
    (h : ∀ m k, DifferentiableOn ℂ (fun s => l s m k) S) (i j : Fin g) :
    DifferentiableOn ℂ (fun s => combMat (l s) ε i j) S := by
  simp only [combMat, Matrix.of_apply]
  apply DifferentiableOn.fun_sum
  intro m _
  exact (h m i).const_mul _

theorem differentiableOn_combMat_perTau : ∀ (n a g r₀ r : ℕ) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (D : ℕ), AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ (j : Fin r) (k : Fin g), DifferentiableOn ℂ (fun s => lam s j k) (logDom n a)) → (∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det) → (∀ i j, DifferentiableOn ℂ (fun z => GlobalTheory.PeriodFrame.combMat (ζ z) α i j) (Metric.ball 0 1)) ∧ ∀ i j, DifferentiableOn ℂ (fun s => GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1} := by
  intro n a g r₀ r ζ lam α φ D hζ hlam hunit
  have hζd : DifferentiableOn ℂ ζ (Metric.ball 0 1) := hζ.differentiableOn
  have hζe : ∀ m k, DifferentiableOn ℂ (fun z => ζ z m k) (Metric.ball 0 1) := by
    intro m k
    have h1 := differentiableOn_pi.1 hζd m
    exact differentiableOn_pi.1 h1 k
  have hA : ∀ i j, DifferentiableOn ℂ (fun z => combMat (ζ z) α i j) (Metric.ball 0 1) :=
    fun i j => differentiableOn_combMat_of_entries α hζe i j
  refine ⟨hA, ?_⟩
  intro i j
  set T : Set (Fin n → ℂ) := {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1} with hT
  have hexp : Differentiable ℂ (fun s : Fin n → ℂ => logExp a s) := by
    refine differentiable_pi.2 fun k => ?_
    simp only [logExp]
    split_ifs
    · exact (differentiable_apply k).cexp
    · exact differentiable_apply k
  have hAT : ∀ i j, DifferentiableOn ℂ (fun s => combMat (ζ (logExp a s)) α i j) T := by
    intro i j
    exact (hA i j).comp hexp.differentiableOn (fun s hs => hs.2)
  have hinvT : ∀ i j, DifferentiableOn ℂ (fun s => (combMat (ζ (logExp a s)) α)⁻¹ i j) T :=
    differentiableOn_inv_of_entries hAT (fun s hs => hunit s hs.1)
  have hBT : ∀ i j, DifferentiableOn ℂ (fun s => combMat (lam s) φ i j) T := by
    intro i j
    exact (differentiableOn_combMat_of_entries φ hlam i j).mono (fun s hs => hs.1)
  simp only [perTau, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
  apply DifferentiableOn.const_mul
  apply DifferentiableOn.fun_sum
  intro k _
  exact (hinvT i k).fun_mul (hBT k j)

end GlobalTheory.PeriodFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOnRationalFramePeriodMatrixLogCoveStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableOn_rationalFrame_periodMatrix_logCover : ∀ (n a g r₀ r : ℕ) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (D : ℕ), AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ (j : Fin r) (k : Fin g), DifferentiableOn ℂ (fun s => lam s j k) (logDom n a)) → (∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det) → (∀ i j, DifferentiableOn ℂ (fun z => GlobalTheory.PeriodFrame.combMat (ζ z) α i j) (Metric.ball 0 1)) ∧ ∀ i j, DifferentiableOn ℂ (fun s => GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1} := by
  first | exact @GlobalTheory.PeriodFrame.differentiableOn_combMat_perTau | exact GlobalTheory.PeriodFrame.differentiableOn_combMat_perTau | (intros; apply GlobalTheory.PeriodFrame.differentiableOn_combMat_perTau <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstForm
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh.ConstForm

theorem constForm : ∀ (n a g r₀ : ℕ) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (Pair : ℕ → (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℂˣ → Prop), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∃ C : ℝ, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ‖ζ z‖ ≤ C) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → (∀ N z v w c c', Pair N z v w c → Pair N z v w c' → c = c') → (∀ (m N : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ) (v w : (Fin m → ℂ) → Fin g → ℂ) (c : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → _root_.IsPreconnected B → DifferentiableOn ℂ φ B → Set.MapsTo φ B (Metric.ball 0 1) → DifferentiableOn ℂ v B → DifferentiableOn ℂ w B → (∀ b ∈ B, v b ∈ K (φ b) ∧ w b ∈ K (φ b)) → b₀ ∈ B → b₁ ∈ B → Pair N (φ b₀) (v b₀) (w b₀) c → Pair N (φ b₁) (v b₁) (w b₁) c) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ Submodule.span ℝ (K z) = ⊤ ∧ (∀ v ∈ K z, ∀ w ∈ K z, ∃ m : ℤ, (hermForm Hm v w).im = m) ∧ ∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K z → w ∈ K z → Pair N z v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N)) (Complex.exp_ne_zero _))) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ a a' : Fin r₀ → ℤ, (fun j => (a j : ZMod N)) ∈ S → Pair N 0 (∑ j, a j • ζ 0 j) (∑ j, a' j • ζ 0 j) 1) → ∃ (r : ℕ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), ContinuousOn lam (logDom n a) ∧ (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) ∧ (∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ ∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) ∧ (∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ v ∈ K (logExp a s), ∀ w ∈ K (logExp a s), ∃ m : ℤ, (hermForm Hm v w).im = m) → (∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K (logExp a s) → w ∈ K (logExp a s) → Pair N (logExp a s) v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N)) (Complex.exp_ne_zero _))) → ∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) ∧ ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ u u' : Fin r₀ → ℤ, (fun j => (u j : ZMod N)) ∈ S → ∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → ∃ m : ℤ, (hermForm Hm (∑ i, u i • ζ (logExp a s) i) (∑ j, u' j • ζ (logExp a s) j)).im = N * m := by
  intro n a g r₀ K ζ Pair hK hζan hζli hζK hζ0 hζbd hstd huniq hprop hinner hS
  obtain ⟨hDo, hDc, hEa, hEm⟩ := Core.logDom_facts n a
  have hDp : _root_.IsPreconnected (logDom n a) := hDc.isPreconnected
  have hEd : Differentiable ℂ (logExp a : (Fin n → ℂ) → Fin n → ℂ) := fun s => (hEa s).differentiableAt
  have hK' : IsLatFam (logDom n a) (fun s => K (logExp a s)) :=
    Core.isLatFam_comp n n g _ _ K (logExp a) hK hDo (fun s _ => hEa s) hEm
  have hin := fun s (hs : s ∈ logDom n a) => hinner _ (hEm hs) (fun k hk => Core.logExp_ne_zero n a s k hk)
  obtain ⟨lam, hlamD, hlamB⟩ := GlobalTheory.T.exists_global_holomorphic_lattice_basis_convex n g (2 * g) (logDom n a) (fun s => K (logExp a s)) hDo hDc
    (fun s hs => GlobalTheory.T.exists_analytic_local_lattice_basis n g (logDom n a) (fun s => K (logExp a s)) s hK' hs (hin s hs).choose_spec.2.2.1)
  have hmem : ∀ s ∈ logDom n a, ∀ i, lam s i ∈ K (logExp a s) := fun s hs i => Core.mem_of_isLatBasis (hlamB s hs) i
  have hlamDi : ∀ i, DifferentiableOn ℂ (fun s => lam s i) (logDom n a) := fun i => differentiableOn_pi.1 hlamD i
  let s₀ : Fin n → ℂ := fun _ => (-1 / 2 : ℂ)
  have hs₀ : s₀ ∈ logDom n a := by
    simp only [logDom, Set.mem_setOf_eq]
    intro k
    split_ifs <;> norm_num [s₀]
  obtain ⟨Hm₀, -, hpos₀, hspan₀, hint₀, hpair₀⟩ := hin s₀ hs₀
  have hMex : ∀ i j, ∃ m : ℤ, (hermForm Hm₀ (lam s₀ i) (lam s₀ j)).im = m := fun i j =>
    hint₀ _ (hmem s₀ hs₀ i) _ (hmem s₀ hs₀ j)
  obtain ⟨M, hM₀⟩ : ∃ M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ, ∀ i j, (hermForm Hm₀ (lam s₀ i) (lam s₀ j)).im = M i j :=
    ⟨fun i j => (hMex i j).choose, fun i j => (hMex i j).choose_spec⟩
  have hM : ∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ,
      (∀ v ∈ K (logExp a s), ∀ w ∈ K (logExp a s), ∃ m : ℤ, (hermForm Hm v w).im = m) →
      (∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K (logExp a s) → w ∈ K (logExp a s) →
        Pair N (logExp a s) v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N))
          (Complex.exp_ne_zero _))) →
      ∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j := by
    intro s hs Hm hint hpair i j
    obtain ⟨m', hm'⟩ := hint _ (hmem s hs i) _ (hmem s hs j)
    have key : m' = M i j := by
      apply Core.eq_of_exp_eq
      intro N hN
      have h1 := hpair₀ N _ _ hN (hmem s₀ hs₀ i) (hmem s₀ hs₀ j)
      have h2 := hprop n N (logDom n a) (logExp a) (fun s => lam s i) (fun s => lam s j) _ s₀ s hN hDo hDp
        hEd.differentiableOn hEm (hlamDi i) (hlamDi j) (fun b hb => ⟨hmem b hb i, hmem b hb j⟩) hs₀ hs h1
      have h3 := hpair N _ _ hN (hmem s hs i) (hmem s hs j)
      have h4 := congrArg Units.val (huniq _ _ _ _ _ _ h3 h2)
      simp only [Units.val_mk0, hm', hM₀, Complex.ofReal_intCast] at h4
      exact h4
    rw [hm', key]
  have hζc : ContinuousOn ζ (Metric.ball 0 1) := hζan.continuousOn
  have hζEc : ∀ i, ContinuousOn (fun s => ζ (logExp a s) i) (logDom n a) := fun i =>
    (continuousOn_pi.1 (hζc.comp hEd.continuous.continuousOn hEm)) i
  have hAex : ∀ i, ∃ m : Fin (2 * g) → ℤ, ∀ s ∈ logDom n a, ζ (logExp a s) i = ∑ k, m k • lam s k := fun i =>
    GlobalTheory.T.exists_const_integral_coords_lattice_section n g (2 * g) (logDom n a) (fun s => K (logExp a s)) lam (fun s => ζ (logExp a s) i) s₀ hDp
      hlamD.continuousOn (hζEc i) hlamB (fun s hs => hζK _ (hEm hs) i) hs₀
  choose A hA using hAex
  have hz₁ : logExp a s₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 := hEm hs₀
  have hsumK : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ c : Fin r₀ → ℤ, ∑ j, c j • ζ z j ∈ K z := by
    intro z hz c
    obtain ⟨H, hH⟩ := hK.2.1 z hz
    have hj : ∀ j, ζ z j ∈ H := fun j => by rw [← SetLike.mem_coe, hH]; exact hζK z hz j
    rw [← hH]
    exact H.sum_mem fun j _ => H.zsmul_mem (hj j) _
  have hζd : DifferentiableOn ℂ ζ (Metric.ball 0 1) := hζan.differentiableOn
  have hsumD : ∀ c : Fin r₀ → ℤ, DifferentiableOn ℂ (fun z => ∑ j, c j • ζ z j) (Metric.ball 0 1) := by
    intro c
    have h : ∀ j ∈ (Finset.univ : Finset (Fin r₀)), DifferentiableOn ℂ (fun z => c j • ζ z j) (Metric.ball 0 1) :=
      fun j _ => (differentiableOn_pi.1 hζd j).const_smul (c j)
    refine (DifferentiableOn.sum h).congr fun z _ => ?_
    simp [Finset.sum_apply]
  have hsum_eq : ∀ s ∈ logDom n a, ∀ c : Fin r₀ → ℤ,
      ∑ j, c j • ζ (logExp a s) j = ∑ k, (∑ i, c i • A i) k • lam s k := by
    intro s hs c
    simp only [fun i => hA i s hs, Finset.smul_sum, smul_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_smul]
    exact Finset.sum_comm
  have hform : ∀ (s : Fin n → ℂ) (Hm : Matrix (Fin g) (Fin g) ℂ),
      (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → ∀ x y : Fin (2 * g) → ℤ,
      (hermForm Hm (∑ k, x k • lam s k) (∑ k, y k • lam s k)).im =
      ((x ⬝ᵥ (M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) *ᵥ y : ℤ) : ℝ) := by
    intro s Hm hHm x y
    rw [Core.hermForm_im_sum]
    simp only [hHm, dotProduct, Matrix.mulVec, Int.cast_sum, Int.cast_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hdvd : ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧
      ∀ c c' : Fin r₀ → ℤ, (fun j => (c j : ZMod N)) ∈ S →
        (N : ℤ) ∣ (∑ i, c i • A i) ⬝ᵥ (M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) *ᵥ (∑ i, c' i • A i) := by
    intro N hN
    obtain ⟨S, hcard, hSp⟩ := hS N hN
    refine ⟨S, hcard, fun c c' hc => ?_⟩
    have h1 := hSp c c' hc
    have h2 := hprop n N (Metric.ball 0 1) id (fun z => ∑ j, c j • ζ z j) (fun z => ∑ j, c' j • ζ z j) 1 0
      (logExp a s₀) hN Metric.isOpen_ball (convex_ball 0 1).isPreconnected differentiableOn_id (Set.mapsTo_id _)
      (hsumD c) (hsumD c') (fun b hb => ⟨hsumK b hb c, hsumK b hb c'⟩) (Metric.mem_ball_self one_pos) hz₁ h1
    have h3 := hpair₀ N _ _ hN (hsumK _ hz₁ c) (hsumK _ hz₁ c')
    have h4 := congrArg Units.val (huniq _ _ _ _ _ _ h3 h2)
    simp only [Units.val_mk0, Units.val_one, id, hsum_eq s₀ hs₀, hform s₀ Hm₀ hM₀, Complex.ofReal_intCast] at h4
    exact Core.dvd_of_exp_eq_one _ N hN h4
  refine ⟨2 * g, lam, M, hlamD.continuousOn, fun s hs => ⟨(hlamB s hs).1.restrict_scalars' ℤ,
    Core.span_top_of_isLatBasis (hlamB s hs) (hin s hs).choose_spec.2.2.1, (hlamB s hs).2⟩, fun s hs => ?_, hM,
    fun N hN => ?_⟩
  · obtain ⟨Hm, -, hpos, -, hint, hpair⟩ := hin s hs
    exact ⟨Hm, hpos, hM s hs Hm hint hpair⟩
  · obtain ⟨S, hcard, hSd⟩ := hdvd N hN
    refine ⟨S, hcard, fun u u' hu s hs Hm hHm => ?_⟩
    obtain ⟨m, hm⟩ := hSd u u' hu
    refine ⟨m, ?_⟩
    rw [hsum_eq s hs u, hsum_eq s hs u', hform s Hm hHm, hm]
    push_cast
    ring

end GlobalTheory.ShFam.Hor.LogCh.ConstForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayPrimeHostIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRayPrimeOfNormIntegerCongruentOne
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRayPrimeOfNormIntegerCongruentOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.RayPrimeOfNorm

theorem isRayPrime_of_norm_eq : ∀ (D : D7) (i : Fin 2) (jE : D.host.E →+* Qb), (D.host.g i).Prime → (∃ π : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧ (π : D.host.E) * D.host.conj (π : D.host.E) = (D.host.g i : D.host.E) ∧ (π - 1) ∈ Ideal.span {((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E)}) → IsRayPrime (GlobalTheory.HeightCounting.KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g i) := by
  intro D i jE hp ⟨π, hK, hnorm, hm⟩
  letI : Algebra D.host.E Qb := jE.toAlgebra
  haveI : IsScalarTower ℚ D.host.E Qb := IsScalarTower.of_algebraMap_eq fun x =>
    RingHom.congr_fun (Subsingleton.elim (algebraMap ℚ Qb) (jE.comp (algebraMap ℚ D.host.E))) x
  let σ : Qb →ₐ[ℚ] Qb := (D.host.conj : D.host.E →ₐ[ℚ] D.host.E).liftNormal Qb
  have hσ : ∀ x : D.host.E, σ (jE x) = jE (D.host.conj x) := fun x =>
    AlgHom.liftNormal_commutes (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) Qb x
  refine ⟨hp, jE (π : D.host.E), (IntermediateField.mem_map _).2 ⟨_, hK, rfl⟩, ?_, ?_, σ, ?_⟩
  · exact (RingOfIntegers.isIntegral_coe π).map jE.toIntAlgHom
  · obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hm
    by_cases hm0 : (((D.host.QS * D.host.q * D.host.d : ℕ)) : Qb) = 0
    · rw [hm0, div_zero]; exact isIntegral_zero
    · have e : (jE (π : D.host.E) - 1) / (((D.host.QS * D.host.q * D.host.d : ℕ)) : Qb) = jE (y : D.host.E) := by
        rw [div_eq_iff hm0]
        have e1 := congrArg (fun z : 𝓞 D.host.E => jE (algebraMap (𝓞 D.host.E) D.host.E z)) hy
        simp only [map_mul, map_sub, map_one, map_natCast] at e1
        push_cast at e1 ⊢
        exact e1.symm
      rw [e]
      exact (RingOfIntegers.isIntegral_coe y).map jE.toIntAlgHom
  · rw [hσ, ← map_mul, hnorm, map_natCast]

end GlobalTheory.RayPrimeOfNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRayPrimeOfNormIntegerCongruentOneStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRayPrime_of_norm_integer_congruent_one : ∀ (D : D7) (i : Fin 2) (jE : D.host.E →+* Qb), (D.host.g i).Prime → (∃ π : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧ (π : D.host.E) * D.host.conj (π : D.host.E) = (D.host.g i : D.host.E) ∧ (π - 1) ∈ Ideal.span {((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E)}) → IsRayPrime (GlobalTheory.HeightCounting.KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g i) := by
  first | exact @GlobalTheory.RayPrimeOfNorm.isRayPrime_of_norm_eq | exact GlobalTheory.RayPrimeOfNorm.isRayPrime_of_norm_eq | (intros; apply GlobalTheory.RayPrimeOfNorm.isRayPrime_of_norm_eq <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.ElemAtStates

theorem allSt_and {p q : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop}
    (h1 : AllSt p) (h2 : AllSt q) : AllSt fun K B f T w P x => p K B f T w P x ∧ q K B f T w P x :=
  EvG.imp (Step.and h1 h2) fun _ _ _ _ _ H => H.imp fun _ _ _ _ G a b c w hw P x => ⟨(G a b c).1 w hw P x, (G a b c).2 w hw P x⟩

theorem allSt_mono {p q : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop}
    (h : AllSt p) (hq : ∀ K B f T w P x, p K B f T w P x → q K B f T w P x) : AllSt q :=
  EvG.imp h fun _ _ _ _ _ H => H.imp fun _ _ _ _ G a b c w hw P x => hq _ _ _ _ _ _ _ (G a b c w hw P x)

end GlobalTheory.ElemAtStates
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionNoNewCellOfMaximalMultiplicityFan
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionNoNewCellOfMaximalMultiplicityFan
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem GlobalTheory.PolFan.starMult : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab w ψ' : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → SimpLab H.bar q φ lab → IsCentreSet H.bar q φ w →
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
          ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) →
    IsPolyFan H.bar q ψ' → Subordinate H.bar q ψ' φ → IsStarOf H.bar q φ w ψ' → ∀ M : ℕ, maxMult H.bar q φ ≤ M →
    maxMult H.bar q ψ' ≤ M ∧
      ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell H.bar ψ' M δ →
          IsMultCell H.bar φ M δ ∧ ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → w.evalZ β ≠ 1 := by
  intro E _ _ _ H q φ lab w ψ' hD hφ hSL hW hC hψ' hSub hStar M hM
  have cI := GlobalTheory.T.starSubdivision_oldCell_multiplicity_le E H q φ lab w ψ' hD hφ hSL M hM
  have cII := GlobalTheory.T.starSubdivision_newCell_multiplicity_lt E H q φ lab w ψ' hSL hW hC M hM
  refine ⟨?_, ?_⟩
  · refine iSup_le fun X => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun hX =>
      iSup_le fun n => iSup_le fun γ' => iSup_le fun hγ' => iSup_le fun hli => iSup_le fun hpr => ?_
    rcases hStar.2.2 X hX n γ' hγ' with ⟨m, γ, hγ, hw, hin⟩ | ⟨m, γ, β₀, m', s, h, hγ, hb, hp, hw1, hin0, hcut, hpos, hin⟩
    · obtain ⟨hφγ, hle, -⟩ := cI X hX n γ' hγ' hli hpr m γ hγ (hStar.1 X hX m γ hγ hw) hw hin
      exact_mod_cast hle
    · have := cII X hX n γ' hγ' hli hpr m γ β₀ m' s h hγ hb hp hw1 hin0 hcut hpos
        (hStar.2.1 X hX m γ hγ β₀ hb hp hw1 hin0 m' s h hcut hpos) hin
      exact_mod_cast this.le
  · intro X _ _ _ _ hX n γ' ⟨hγ', hli, hpr, heq⟩
    rcases hStar.2.2 X hX n γ' hγ' with ⟨m, γ, hγ, hw, hin⟩ | ⟨m, γ, β₀, m', s, h, hγ, hb, hp, hw1, hin0, hcut, hpos, hin⟩
    · obtain ⟨hφγ, -, hno⟩ := cI X hX n γ' hγ' hli hpr m γ hγ (hStar.1 X hX m γ hγ hw) hw hin
      exact ⟨⟨hφγ, hli, hpr, heq⟩, hno⟩
    · have := cII X hX n γ' hγ' hli hpr m γ β₀ m' s h hγ hb hp hw1 hin0 hcut hpos
        (hStar.2.1 X hX m γ hγ β₀ hb hp hw1 hin0 m' s h hcut hpos) hin
      omega
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionNoNewCellOfMaximalMultiplicityFanStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.starSubdivision_no_new_cell_of_maximal_multiplicity_fan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab w ψ' : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → SimpLab H.bar q φ lab → IsCentreSet H.bar q φ w →
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
          ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) →
    IsPolyFan H.bar q ψ' → Subordinate H.bar q ψ' φ → IsStarOf H.bar q φ w ψ' → ∀ M : ℕ, maxMult H.bar q φ ≤ M →
    maxMult H.bar q ψ' ≤ M ∧
      ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell H.bar ψ' M δ →
          IsMultCell H.bar φ M δ ∧ ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → w.evalZ β ≠ 1 := by
  first | exact @GlobalTheory.PolFan.starMult | exact GlobalTheory.PolFan.starMult | (intros; apply GlobalTheory.PolFan.starMult <;> assumption)
end
end
