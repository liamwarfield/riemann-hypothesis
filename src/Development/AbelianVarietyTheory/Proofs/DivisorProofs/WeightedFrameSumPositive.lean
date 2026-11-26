module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardGroupElementsChartReturnLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneZeroInsertionLinearApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeEqOfRealUnitaryConj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingCompatibleAddSecondSlotComplexStatement
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuAllData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedDictionaryBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedDictionaryBound
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LevGeo.MassLev

theorem mass_components_le : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (x0 : ∀ k, Frame ((U σ).X k).Ψ D.R.r) (FF : ∀ k, Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U σ).X k)))), (∀ k, IsOrth ((U σ).X k) (x0 k) ∧ IsFundSet ((U σ).X k) (x0 k) (FF k)) → ∑ k, muF ((U σ).X k) (x0 k) (FF k) ≤ ENNReal.ofReal (massLev D.host.E D.R.r l.M) := by
  intro hMB hTB D j H Dw l Xo c U dict hL σ hσ x0 FF hF
  obtain ⟨G, Λ, g, Λk, u, hSD, hk, hdist⟩ := GlobalTheory.T.principalLevel_components_doubleCosets_congruence D j H Dw l Xo c U dict hL σ hσ
  have hX' := fun k => GlobalTheory.T.exists_flagDomainData_principalCongruenceLevel D.host.E D.R.r l.M ((U σ).X k) (Λk k) l.three_le (hk k).2.2.2.1 (hk k).2.2.2.2.1
  choose X' hX'Gm hX'Ψ hX'p0 hX'Λ hX'Γ using hX'
  have hfm : ∀ k, ∃ y, IsOrth (X' k) y ∧ ∃ FF', IsFundSet (X' k) y FF' ∧ muF (X' k) y FF' < ⊤ :=
    fun k => GlobalTheory.finMu_all_data D.host.E D.R.r (X' k)
  choose y hy FF' hFF' _ using hfm
  have hμ : ∀ k, muF ((U σ).X k) (x0 k) (FF k) = muF (X' k) (y k) (FF' k) := by
    intro k
    obtain ⟨hGm, -, -, -, -, hgram, hfw, hbw⟩ := hk k
    refine GlobalTheory.T.covolume_eq_of_realUnitary_conj D.host.E D.R.r ((U σ).X k) (X' k) (hX'Ψ k) (u k) (x0 k) (y k) (FF k) (FF' k)
      (hX'Gm k) (hX'p0 k) (by rw [hGm]; exact hgram) ?_ ?_ (hF k).1 (hy k) (hF k).2 (hFF' k)
    · intro γ hγ
      obtain ⟨γ', hγ', hc⟩ := hfw γ hγ
      exact ⟨γ', (hX'Γ k γ').2 (by rw [hGm]; exact hγ'), hc⟩
    · intro γ' hγ'
      have := (hX'Γ k γ').1 hγ'
      rw [hGm] at this
      exact hbw γ' this
  have hunf := hL.unf σ hσ
  set Ψ : Finset (D.host.E →+* ℂ) := Finset.univ.filter (fun τ => τ (H.rt : D.host.E) = H.rt0) with hΨdef
  have hΨ : ∀ k, (X' k).Ψ = Ψ := by
    intro k
    rw [hX'Ψ k]
    ext τ
    rw [(hunf.2.1 k).2 τ, hΨdef, Finset.mem_filter]
    simp
  rw [Finset.sum_congr rfl (fun k _ => hμ k)]
  set e := Fintype.equivFin (U σ).Comp
  rw [← e.symm.sum_comp]
  have hr : 2 ≤ D.R.r := Formalism.L2.Geo.two_le_r D
  have hTor := hTB D.host.E D.R.r l.M G Λ (by omega) (by have := l.three_le; omega) H.unram hSD
  exact hMB D.host.E D.R.r l.M _ _ G Λ Ψ (fun i => X' (e.symm i)) (fun i => g (e.symm i)) (fun i => y (e.symm i))
    (fun i => FF' (e.symm i)) hr l.three_le H.unram hSD hTor (fun i => (hk (e.symm i)).2.1)
    (fun i i' h => e.symm.injective (hdist _ _ h))
    (fun i => ⟨(hX'Gm _).trans (hk _).1, hΨ _, by rw [hX'Λ]; exact (hk _).2.2.1, fun γ => by rw [hX'Λ, hX'Γ, (hk _).1],
      hy _, hFF' _⟩)

end GlobalTheory.LevGeo.MassLev
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedDictionaryBoundStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framed_dictionary_bound : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (x0 : ∀ k, Frame ((U σ).X k).Ψ D.R.r) (FF : ∀ k, Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U σ).X k)))), (∀ k, IsOrth ((U σ).X k) (x0 k) ∧ IsFundSet ((U σ).X k) (x0 k) (FF k)) → ∑ k, muF ((U σ).X k) (x0 k) (FF k) ≤ ENNReal.ofReal (massLev D.host.E D.R.r l.M) := by
  first | exact @GlobalTheory.LevGeo.MassLev.mass_components_le | exact GlobalTheory.LevGeo.MassLev.mass_components_le | (intros; apply GlobalTheory.LevGeo.MassLev.mass_components_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormSupNormLePeterssonIntegralComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMeanValueFlagChartInvariantMeasure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMeanValueFlagChartInvariantMeasure
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.SubmeanChart

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem card_strictLower (r : ℕ) : Fintype.card {p : Fin r × Fin r // p.2 < p.1} = r * (r - 1) / 2 := by
  have e : {p : Fin r × Fin r // p.2 < p.1} ≃ Σ a : Fin r, Finset.Iio a :=
    { toFun := fun p => ⟨p.1.1, p.1.2, Finset.mem_Iio.2 p.2⟩
      invFun := fun x => ⟨(x.1, x.2.1), Finset.mem_Iio.1 x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_coe, Fin.card_Iio]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) r, Finset.sum_range_id]

theorem nd_eq_dimFl (X : Data E r) : nd X = dimFl E r := by
  unfold nd dimFl
  rw [Fintype.card_prod, card_strictLower, QuadraticCoefficientForms.card_Psi]

theorem cpt_zero (X : Data E r) (x0 : Frame X.Ψ r) : cpt X x0 0 = x0 := by
  funext τ a b
  have h1 : mat (nmat X 0) τ = 1 := by
    ext i j
    simp only [mat, nmat, Matrix.of_apply, Matrix.one_apply]
    by_cases h : j < i
    · rw [dif_pos h, if_neg (ne_of_gt h)]
      rfl
    · rw [dif_neg h]
  show (mat x0 τ * mat (nmat X 0) τ) a b = x0 τ a b
  rw [h1, Matrix.mul_one]
  rfl

theorem differentiable_cpt (X : Data E r) (x0 : Frame X.Ψ r) : Differentiable ℂ (cpt X x0) := by
  rw [differentiable_pi]; intro τ
  rw [differentiable_pi]; intro a
  rw [differentiable_pi]; intro b
  simp only [cpt, rmul, mat, Matrix.mul_apply, Matrix.of_apply]
  refine Differentiable.fun_sum fun k _ => Differentiable.const_mul ?_ _
  by_cases h : b < k
  · simp only [nmat, dif_pos h]
    fun_prop
  · simp only [nmat, dif_neg h]
    exact differentiable_const _

theorem norm_dmin_of_orth (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm x τ i‖ = 1 := by
  unfold dmin lminor
  rw [hx τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  simp only [Function.comp_apply, sgn]
  split_ifs <;> simp

theorem nfac_of_orth (X : Data E r) (la : Wt X.Ψ r) {x : Frame X.Ψ r} (hx : IsOrth X x) : X.nfac la x = 1 := by
  unfold Data.nfac
  refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun i _ => ?_
  rw [norm_div, norm_dmin_of_orth X hx, norm_dmin_of_orth X hx, div_one, Real.one_rpow]

theorem pnorm_eq (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la P x = ‖P x‖ * X.nfac la x := rfl

theorem spread_nonneg (X : Data E r) (la : Wt X.Ψ r) (hr : 0 < r) (τ : X.Ψ) : 0 ≤ X.spread la τ := by
  unfold Data.spread
  have i : Fin r := ⟨0, hr⟩
  have h1 := ciInf_le (Set.finite_range fun i => (la τ i : ℝ)).bddBelow i
  have h2 := le_ciSup (Set.finite_range fun i => (la τ i : ℝ)).bddAbove i
  linarith

theorem chartRad_pos (X : Data E r) (la : Wt X.Ψ r) {w : ℝ} (hr : 0 < r) (hw : (∑ τ, X.spread la τ) ≤ w) :
    0 < chartRad E r w := by
  have h0 : 0 ≤ w := le_trans (Finset.sum_nonneg fun τ _ => spread_nonneg X la hr τ) hw
  have hf : (0 : ℝ) < fdeg E := by exact_mod_cast (QuadraticCoefficientForms.card_Psi X) ▸ QuadraticCoefficientForms.card_Psi_pos X
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  unfold chartRad
  positivity

end

end GlobalTheory.SubmeanChart

namespace GlobalTheory.SubmeanChart
noncomputable section

theorem submean_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (w : ℝ) (x : Frame X.Ψ r) (P : Frame X.Ψ r → ℂ), 0 < r → IsOrth X x → (∑ τ, X.spread la τ) ≤ w → DifferentiableOn ℂ P X.dom → ENNReal.ofReal (X.pnorm la P x ^ 2) ≤ ENNReal.ofReal (2 * ((dimFl E r).factorial : ℝ) / (Real.pi * chartRad E r w ^ 2) ^ dimFl E r) * ∫⁻ z in Metric.ball (0 : V (nd X)) (chartRad E r w), ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) ∂(muF X x) := by
  intro E _ _ _ r X la w x P hr hx hw hP
  set ρ := chartRad E r w with hρdef
  have hρ : 0 < ρ := chartRad_pos X la hr hw
  have hch := GlobalTheory.T.normFactor_and_density_near_one_in_flagChart E r X la w x hr hx hw

  set φ : V (nd X) → ℂ := fun z => P (cpt X x z) with hφdef
  have hφ : DifferentiableOn ℂ φ (Metric.ball 0 ρ) :=
    hP.comp (differentiable_cpt X x).differentiableOn fun z hz =>
      (hch z (le_of_lt (mem_ball_zero_iff.1 hz))).1
  have hsub := GlobalTheory.enorm_pow_le_inv_measure_mul_lintegral_ball (volume : Measure (V (nd X))) (a := 0) hρ hφ 2
  have hne : ENNReal.ofReal (Real.pi ^ nd X * ρ ^ (2 * nd X) / ((nd X).factorial : ℝ)) =
      ENNReal.ofReal (Real.pi ^ dimFl E r * ρ ^ (2 * dimFl E r) / ((dimFl E r).factorial : ℝ)) := by
    rw [nd_eq_dimFl]
  rw [GlobalTheory.volume_ball_euclideanSpace_complex (0 : V (nd X)) hρ, Fintype.card_fin, hne] at hsub
  set D := dimFl E r with hD

  have h1 : ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ‖φ z‖ₑ ^ 2 ≤
      ENNReal.ofReal (Real.exp (1 / 20)) *
        ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
    obtain ⟨-, hn, -⟩ := hch z (le_of_lt (mem_ball_zero_iff.1 hz))
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [pnorm_eq, mul_pow]
    have he : 1 ≤ Real.exp (1 / 20) * X.nfac la (cpt X x z) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hn (Real.exp_pos (1 / 20)).le
      rwa [← Real.exp_add, show (1 / 20 : ℝ) + -(1 / 20) = 0 by norm_num, Real.exp_zero] at this
    calc ‖φ z‖ ^ 2 = ‖φ z‖ ^ 2 * 1 := (mul_one _).symm
      _ ≤ ‖φ z‖ ^ 2 * (Real.exp (1 / 20) * X.nfac la (cpt X x z) ^ 2) :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by rw [hφdef]; ring

  have hμ : ENNReal.ofReal (Real.exp (-(1 / 10))) • (volume.restrict (Metric.ball (0 : V (nd X)) ρ)) ≤
      (muF X x).restrict (Metric.ball 0 ρ) := by
    have hb : Metric.ball (0 : V (nd X)) ρ ∩ OmF X x = Metric.ball 0 ρ :=
      Set.inter_eq_left.2 fun z hz => (hch z (le_of_lt (mem_ball_zero_iff.1 hz))).1
    rw [muF, restrict_withDensity measurableSet_ball, Measure.restrict_restrict measurableSet_ball, hb,
      ← withDensity_const]
    refine withDensity_mono (ae_restrict_of_forall_mem measurableSet_ball fun z hz => ?_)
    exact ENNReal.ofReal_le_ofReal (hch z (le_of_lt (mem_ball_zero_iff.1 hz))).2.2
  have h2 : ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) ≤
      ENNReal.ofReal (Real.exp (1 / 10)) *
        ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) ∂(muF X x) := by
    have h3 := lintegral_mono' hμ (le_refl (fun z => ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2)))
    rw [lintegral_smul_measure, smul_eq_mul] at h3
    calc _ = ENNReal.ofReal (Real.exp (1 / 10)) * (ENNReal.ofReal (Real.exp (-(1 / 10))) *
          ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
            show (1 / 10 : ℝ) + -(1 / 10) = 0 by norm_num, Real.exp_zero, ENNReal.ofReal_one, one_mul]
      _ ≤ _ := by gcongr

  have h0 : ENNReal.ofReal (X.pnorm la P x ^ 2) = ‖φ 0‖ₑ ^ 2 := by
    rw [pnorm_eq, nfac_of_orth X la hx, mul_one, show φ 0 = P x by simp only [hφdef, cpt_zero], ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

  have hvol : (ENNReal.ofReal (Real.pi ^ D * ρ ^ (2 * D) / (D.factorial : ℝ)))⁻¹ =
      ENNReal.ofReal ((D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D) := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity), inv_div, mul_pow, ← pow_mul, mul_comm 2 D]
  have hexp : Real.exp (1 / 20) * Real.exp (1 / 10) ≤ 2 := by
    rw [← Real.exp_add]
    calc Real.exp (1 / 20 + 1 / 10) ≤ Real.exp (Real.log 2) :=
          Real.exp_le_exp.2 (by linarith [Real.log_two_gt_d9])
      _ = 2 := Real.exp_log two_pos
  have hc : ENNReal.ofReal ((D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D) *
      (ENNReal.ofReal (Real.exp (1 / 20)) * ENNReal.ofReal (Real.exp (1 / 10))) ≤
      ENNReal.ofReal (2 * (D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hq : 0 ≤ (D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D := by positivity
    calc (D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D * (Real.exp (1 / 20) * Real.exp (1 / 10))
        ≤ (D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D * 2 := mul_le_mul_of_nonneg_left hexp hq
      _ = _ := by ring
  rw [h0]
  calc ‖φ 0‖ₑ ^ 2 ≤ _ := hsub
    _ ≤ ENNReal.ofReal ((D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D) *
          (ENNReal.ofReal (Real.exp (1 / 20)) * (ENNReal.ofReal (Real.exp (1 / 10)) *
            ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) ∂(muF X x))) := by
        rw [hvol]
        gcongr
        exact h1.trans (by gcongr)
    _ = (ENNReal.ofReal ((D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D) *
          (ENNReal.ofReal (Real.exp (1 / 20)) * ENNReal.ofReal (Real.exp (1 / 10)))) *
            ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) ∂(muF X x) := by
        ring
    _ ≤ _ := by gcongr

end
end GlobalTheory.SubmeanChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMeanValueFlagChartInvariantMeasureStatement
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subMeanValue_flagChart_invariantMeasure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (w : ℝ) (x : Frame X.Ψ r) (P : Frame X.Ψ r → ℂ), 0 < r → IsOrth X x → (∑ τ, X.spread la τ) ≤ w → DifferentiableOn ℂ P X.dom → ENNReal.ofReal (X.pnorm la P x ^ 2) ≤ ENNReal.ofReal (2 * ((dimFl E r).factorial : ℝ) / (Real.pi * chartRad E r w ^ 2) ^ dimFl E r) * ∫⁻ z in Metric.ball (0 : V (nd X)) (chartRad E r w), ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) ∂(muF X x) := by
  first | exact @GlobalTheory.SubmeanChart.submean_chart | exact GlobalTheory.SubmeanChart.submean_chart | (intros; apply GlobalTheory.SubmeanChart.submean_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormSupNormLePeterssonIntegralComponent
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.SupLoc

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem fdeg_pos' : 0 < fdeg E := by
  unfold fdeg
  have h2 := IsTotallyComplex.finrank (K := E)
  have hp : 0 < Module.finrank ℚ E := Module.finrank_pos
  omega

theorem pnorm_nonneg' {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (y : Frame X.Ψ r) :
    0 ≤ X.pnorm la P y := by
  unfold Data.pnorm; positivity

theorem pnorm_lact' {r : ℕ} (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P)
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    X.pnorm la P (lact γ y) = X.pnorm la P y := by
  have hχ : ‖X.χ la γ‖ = 1 := by
    obtain ⟨n, hn, h⟩ := X.χ_fin la
    have := congrArg norm (h γ hγ)
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  unfold Data.pnorm dmin
  simp only [GlobalTheory.MajInv.gram_lact X (X.Γ_stab γ hγ)]
  rw [hP.2.2 γ hγ _ hy, norm_mul, hχ, one_mul]

theorem pnorm_piecewise {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {y : Frame X.Ψ r}
    (hy : y ∈ X.dom) : X.pnorm la (X.dom.piecewise P 0) y = X.pnorm la P y := by
  classical
  unfold Data.pnorm
  rw [Set.piecewise_eq_of_mem _ _ _ hy]

theorem pnorm_piecewise_le {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (y : Frame X.Ψ r) :
    X.pnorm la (X.dom.piecewise P 0) y ^ 2 ≤ X.pnorm la P y ^ 2 := by
  classical
  by_cases hy : y ∈ X.dom
  · rw [pnorm_piecewise X la P hy]
  · have : X.pnorm la (X.dom.piecewise P 0) y = 0 := by
      unfold Data.pnorm
      rw [Set.piecewise_eq_of_notMem _ _ _ hy]; simp
    rw [this, sq, zero_mul]; positivity

end GlobalTheory.SupLoc


open GlobalTheory.SupLoc in
theorem GlobalTheory.supLoc_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (M w : ℝ) (x0 : Frame X.Ψ r) (FF : Set (V (nd X.toData))), 0 < r → P ∈ X.SS la → 0 < M → (∑ τ, X.spread la τ) ≤ w → 0 < w → (∀ γ ∈ X.Γ, ∀ v ∈ X.L', (γ : Matrix (Fin r) (Fin r) E).mulVec v ∈ X.L') → (∀ v ∈ X.L', herm X.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b → ∃ γ ∈ X.Γ, X.χ la γ = 1 ∧ ∀ τ : X.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = X.flowMat v τ ((M : ℂ) * τ.1 b)) → IsOrth X.toData x0 → IsFundSet X.toData x0 FF → ∀ y ∈ X.dom, ENNReal.ofReal (X.pnorm la P y ^ 2) ≤ ENNReal.ofReal (locConst E r w (epStar M (fdeg E) w X.k0)) * ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la P (cpt X.toData x0 z) ^ 2) ∂(muF X.toData x0) := by
  classical
  intro E _ _ _ r X la P M w x0 FF hr hP hM hw hw0 hΓL hTr hx0 hFF y hy
  have hsec : X.IsSec la P := hP.1.1
  obtain ⟨C, hC⟩ := hP.1.2
  by_cases hy0 : X.pnorm la P y = 0
  · rw [hy0]; simp
  have hypos : 0 < X.pnorm la P y := lt_of_le_of_ne (pnorm_nonneg' _ _ _ _) (Ne.symm hy0)

  set S := sSup (X.pnorm la P '' X.dom) with hSdef
  have hbdd : BddAbove (X.pnorm la P '' X.dom) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hC x hx
  have hle : ∀ x ∈ X.dom, X.pnorm la P x ≤ S := fun x hx => le_csSup hbdd ⟨x, hx, rfl⟩
  have hSpos : 0 < S := lt_of_lt_of_le hypos (hle y hy)
  obtain ⟨_, ⟨z0, hz0, rfl⟩, hz0S⟩ := exists_lt_of_lt_csSup ((show X.dom.Nonempty from ⟨y, hy⟩).image (X.pnorm la P)) (half_lt_self hSpos)
  have hhalf : ∀ x ∈ X.dom, X.pnorm la P x ≤ 2 * X.pnorm la P z0 := fun x hx => by
    linarith [hle x hx]
  have hz0pos : 0 < X.pnorm la P z0 := by linarith
  have hmax := maxBound_holds (E := E) r X la P M w hP hM hw hw0 hTr z0 hz0 hhalf hz0pos

  obtain ⟨b, hb, hxo, hmaj⟩ := ModeHalfC.orthonormalize X.toData hz0
  set x := rmul z0 b with hxdef
  have hpx : X.pnorm la P x = X.pnorm la P z0 := FrameDegreeData.pnorm_rmul X.toData la P hsec.2.1 z0 hz0 b hb
  set ε := epStar M (fdeg E) w X.k0 with hεdef
  have hf1 : (1 : ℝ) ≤ fdeg E := by exact_mod_cast (fdeg_pos' (E := E))
  have hε : 0 < ε := by
    rw [hεdef]; unfold epStar
    have hk := X.minWeight_pos
    have hl := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    refine lt_min one_pos (div_pos Real.pi_pos ?_)
    have : 0 < (fdeg E : ℝ) * w + 2 := by positivity
    positivity
  have hshort : ∀ v ∈ X.L', v ≠ 0 → ε ≤ ∑ τ, X.maj x τ (Data.emb τ.1 v) := by
    intro v hv hv0
    obtain ⟨τ, hτ⟩ := hmax v hv hv0
    rw [← hmaj τ] at hτ
    exact hτ.trans (Finset.single_le_sum (f := fun τ => X.maj x τ (Data.emb τ.1 v))
      (fun τ _ => ModeHalfC.maj_nonneg_orth X.toData hxo τ _) (Finset.mem_univ τ))
  set ρ := chartRad E r w with hρdef
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hρ : (r : ℝ) ^ 2 * ρ ≤ 1 / 100 := by
    rw [hρdef]; unfold chartRad
    have h1 : 0 < (r : ℝ) := by linarith
    have h2 : 0 < w + fdeg E := by linarith
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul hr1 (show (1:ℝ) ≤ w + fdeg E by linarith) zero_le_one h1.le]
  have hmult := GlobalTheory.T.card_group_elements_chart_return_le E r X x ε ρ hr hxo hε hρ hΓL hshort
  have hsub := GlobalTheory.T.subMeanValue_flagChart_invariantMeasure E r X.toData la w x P hr hxo hw hsec.1

  set P' : Frame X.Ψ r → ℂ := X.dom.piecewise P 0 with hP'def
  set Φ : Frame X.Ψ r → ℝ≥0∞ := fun u => ENNReal.ofReal (X.pnorm la P' u ^ 2) with hΦdef
  have hdomO := FourierCoefficientDomain.isOpen_dom X.toData
  have hΦm : Measurable Φ := by
    have hm := GlobalTheory.PeterssonCompare.measurable_pnorm X.toData la (P := P')
      (hsec.1.continuousOn.congr fun u hu => Set.piecewise_eq_of_mem _ _ _ hu)
      (fun u hu => by rw [hP'def, Set.piecewise_eq_of_notMem _ _ _ hu]; rfl)
    exact ENNReal.measurable_ofReal.comp (hm.pow_const 2)
  have hΦΓ : ∀ γ ∈ X.Γ, ∀ u ∈ X.dom, Φ (lact γ u) = Φ u := by
    intro γ hγ u hu
    have hu' := GlobalTheory.MajInv.lact_mem_dom X.toData (X.Γ_stab γ hγ) hu
    show ENNReal.ofReal (X.pnorm la P' (lact γ u) ^ 2) = ENNReal.ofReal (X.pnorm la P' u ^ 2)
    rw [hP'def, pnorm_piecewise X.toData la P hu, pnorm_piecewise X.toData la P hu',
      pnorm_lact' X.toData hsec hγ hu]
  have hΦB : ∀ c ∈ Bor X.Ψ r, ∀ u ∈ X.dom, Φ (rmul u c) = Φ u := by
    intro c hc u hu
    have hu' := OrthogonalFrameDomain.rmul_mem_dom X.toData hu hc
    show ENNReal.ofReal (X.pnorm la P' (rmul u c) ^ 2) = ENNReal.ofReal (X.pnorm la P' u ^ 2)
    rw [hP'def, pnorm_piecewise X.toData la P hu, pnorm_piecewise X.toData la P hu',
      FrameDegreeData.pnorm_rmul X.toData la P hsec.2.1 u hu c hc]
  set A := Metric.ball (0 : V (nd X.toData)) ρ ∩ OmF X.toData x with hAdef
  have hOm := ExF.isOpen_OmF X.toData x
  have hA : MeasurableSet A := measurableSet_ball.inter hOm.measurableSet
  have hAsub : A ⊆ OmF X.toData x := Set.inter_subset_right
  have hmA : (({γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z ∈ A, ∃ z' ∈ A, ∃ c ∈ Bor X.Ψ r,
      lact γ (cpt X.toData x z) = rmul (cpt X.toData x z') c}.encard : ℝ≥0∞)) ≤
      ENNReal.ofReal (multBd E r ε) := by
    refine le_trans (ENat.toENNReal_le.2 (Set.encard_le_encard ?_)) hmult
    rintro γ ⟨hγ, z, hz, z', hz', c, hc, he⟩
    exact ⟨hγ, z, z', (mem_ball_zero_iff.1 hz.1).le, (mem_ball_zero_iff.1 hz'.1).le, c, hc, he⟩
  have hunf := GlobalTheory.T.lintegral_invariant_chartSet_le_mul_fundamentalSet E r X.toData x0 x FF A _ Φ hx0 hxo hFF hA hAsub hΦm hΦΓ hΦB hmA

  have hae : ∀ᵐ z ∂(muF X.toData x), z ∈ OmF X.toData x := by
    have h1 : ∀ᵐ z ∂(volume.restrict (OmF X.toData x)), z ∈ OmF X.toData x :=
      ae_restrict_mem hOm.measurableSet
    exact (withDensity_absolutelyContinuous _ _).ae_le h1
  have hball : ∫⁻ z in Metric.ball (0 : V (nd X.toData)) ρ,
      ENNReal.ofReal (X.pnorm la P (cpt X.toData x z) ^ 2) ∂(muF X.toData x) =
      ∫⁻ z in A, Φ (cpt X.toData x z) ∂(muF X.toData x) := by
    have hset : A =ᵐ[muF X.toData x] Metric.ball (0 : V (nd X.toData)) ρ := by
      filter_upwards [hae] with z hz
      simp [hAdef, hz]
    rw [Measure.restrict_congr_set hset]
    refine setLIntegral_congr_fun_ae measurableSet_ball ?_
    filter_upwards [hae] with z hz
    try intro _
    show ENNReal.ofReal (X.pnorm la P (cpt X.toData x z) ^ 2) = ENNReal.ofReal (X.pnorm la P' (cpt X.toData x z) ^ 2)
    rw [hP'def, pnorm_piecewise X.toData la P hz]
  have hFFle : ∫⁻ z in FF, Φ (cpt X.toData x0 z) ∂(muF X.toData x0) ≤
      ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la P (cpt X.toData x0 z) ^ 2) ∂(muF X.toData x0) :=
    lintegral_mono fun z => ENNReal.ofReal_le_ofReal (pnorm_piecewise_le X.toData la P _)

  set C2 : ℝ := 2 * ((dimFl E r).factorial : ℝ) / (Real.pi * chartRad E r w ^ 2) ^ dimFl E r with hC2
  have hC2n : 0 ≤ C2 := by positivity
  have hyx : X.pnorm la P y ^ 2 ≤ 4 * X.pnorm la P x ^ 2 := by
    have h := hhalf y hy
    rw [← hpx] at h
    have := pnorm_nonneg' X.toData la P y
    nlinarith
  have hconst : ENNReal.ofReal (locConst E r w ε) =
      ENNReal.ofReal 4 * (ENNReal.ofReal C2 * ENNReal.ofReal (multBd E r ε)) := by
    rw [← ENNReal.ofReal_mul hC2n, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    rw [hC2]; unfold locConst; ring
  calc ENNReal.ofReal (X.pnorm la P y ^ 2) ≤ ENNReal.ofReal (4 * X.pnorm la P x ^ 2) :=
        ENNReal.ofReal_le_ofReal hyx
    _ = ENNReal.ofReal 4 * ENNReal.ofReal (X.pnorm la P x ^ 2) := ENNReal.ofReal_mul (by norm_num)
    _ ≤ ENNReal.ofReal 4 * (ENNReal.ofReal C2 * ∫⁻ z in A, Φ (cpt X.toData x z) ∂(muF X.toData x)) := by
        rw [← hball]; gcongr
    _ ≤ ENNReal.ofReal 4 * (ENNReal.ofReal C2 * (ENNReal.ofReal (multBd E r ε) *
          ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la P (cpt X.toData x0 z) ^ 2) ∂(muF X.toData x0))) := by
        gcongr
        exact hunf.trans (by gcongr)
    _ = _ := by rw [hconst]; ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormSupNormLePeterssonIntegralComponentStatement
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_sup_norm_le_petersson_integral_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (M w : ℝ) (x0 : Frame X.Ψ r) (FF : Set (V (nd X.toData))), 0 < r → P ∈ X.SS la → 0 < M → (∑ τ, X.spread la τ) ≤ w → 0 < w → (∀ γ ∈ X.Γ, ∀ v ∈ X.L', (γ : Matrix (Fin r) (Fin r) E).mulVec v ∈ X.L') → (∀ v ∈ X.L', herm X.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b → ∃ γ ∈ X.Γ, X.χ la γ = 1 ∧ ∀ τ : X.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = X.flowMat v τ ((M : ℂ) * τ.1 b)) → IsOrth X.toData x0 → IsFundSet X.toData x0 FF → ∀ y ∈ X.dom, ENNReal.ofReal (X.pnorm la P y ^ 2) ≤ ENNReal.ofReal (locConst E r w (epStar M (fdeg E) w X.k0)) * ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la P (cpt X.toData x0 z) ^ 2) ∂(muF X.toData x0) := by
  first | exact @GlobalTheory.supLoc_component | exact GlobalTheory.supLoc_component | (intros; apply GlobalTheory.supLoc_component <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedFrameSumPositive
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.SupModel

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem pnorm_nonneg₀ {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (y : Frame X.Ψ r) :
    0 ≤ X.pnorm la P y := by
  unfold Data.pnorm; positivity

theorem pnorm_lact_eq {r : ℕ} (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P)
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    X.pnorm la P (lact γ y) = X.pnorm la P y := by
  have hχ : ‖X.χ la γ‖ = 1 := by
    obtain ⟨n, hn, h⟩ := X.χ_fin la
    have := congrArg norm (h γ hγ)
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  unfold Data.pnorm dmin
  simp only [GlobalTheory.MajInv.gram_lact X (X.Γ_stab γ hγ)]
  rw [hP.2.2 γ hγ _ hy, norm_mul, hχ, one_mul]

theorem pnorm_piecewise_eq {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {y : Frame X.Ψ r}
    (hy : y ∈ X.dom) : X.pnorm la (X.dom.piecewise P 0) y = X.pnorm la P y := by
  unfold Data.pnorm
  rw [Set.piecewise_eq_of_mem _ _ _ hy]

theorem epStar_eq_epsLev (d M : ℕ) (w M' k0 : ℝ) (hk : M' * k0 = 2 * (M : ℝ) * Real.sqrt d) :
    epStar M' (fdeg E) w k0 = epsLev E d M w := by
  unfold epsLev epStar
  congr 2
  rw [show M' * ((fdeg E : ℝ) * w + 2) * k0 * Real.log 2 = (M' * k0) * ((fdeg E : ℝ) * w + 2) * Real.log 2 by ring, hk]
  ring

theorem comp_bound {r : ℕ} (hr : 0 < r) (X : Data E r) (Xx : DataX E r) (hX : Xx.toData = X) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) (hP : P ∈ X.SS la) (w : ℝ) (hw0 : 0 < w) (hw : (∑ τ, X.spread la τ) ≤ w)
    (hχ : ∀ γ ∈ X.Γ, X.χ la γ = 1) (d M : ℕ)
    (hL : ∀ γ ∈ Xx.Γ, ∀ v ∈ Xx.L', (γ : Matrix (Fin r) (Fin r) E).mulVec v ∈ Xx.L') (M' : ℝ) (hM' : 0 < M')
    (hk : M' * Xx.k0 = 2 * (M : ℝ) * Real.sqrt d)
    (hT : ∀ v ∈ Xx.L', herm Xx.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b → ∃ γ ∈ Xx.Γ, ∀ τ : Xx.Ψ,
      (γ : Matrix (Fin r) (Fin r) E).map τ.1 = Xx.flowMat v τ ((M' : ℂ) * τ.1 b))
    (x0 : Frame X.Ψ r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (nd X))) (ho : IsOrth X x0) (hF : IsFundSet X x0 FF) :
    ∀ y ∈ X.dom, ENNReal.ofReal (X.pnorm la P y ^ 2) ≤ ENNReal.ofReal (locConst E r w (epsLev E d M w)) *
      ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la (X.dom.piecewise P 0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ∂(muF X x0) := by
  subst hX
  intro y hy
  have h := GlobalTheory.T.cuspForm_sup_norm_le_petersson_integral_component E r Xx la P M' w x0 FF hr hP hM' hw hw0 hL
    (fun v hv hiso b hb hbi => by
      obtain ⟨γ, hγ, he⟩ := hT v hv hiso b hb hbi
      exact ⟨γ, hγ, hχ γ hγ, he⟩) ho hF y hy
  rw [epStar_eq_epsLev d M w M' Xx.k0 hk] at h
  refine h.trans (mul_le_mul' le_rfl ?_)
  have hae : ∀ᵐ z ∂(muF Xx.toData x0), z ∈ OmF Xx.toData x0 := by
    have h1 : ∀ᵐ z ∂(volume.restrict (OmF Xx.toData x0)), z ∈ OmF Xx.toData x0 :=
      ae_restrict_mem (ExF.isOpen_OmF Xx.toData x0).measurableSet
    exact (withDensity_absolutelyContinuous _ _).ae_le h1
  refine lintegral_mono_ae (ae_restrict_of_ae ?_)
  filter_upwards [hae] with z hz
  rw [pnorm_piecewise_eq Xx.toData la P hz]

end GlobalTheory.SupModel


open GlobalTheory.SupModel in
theorem GlobalTheory.supPet_principal : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (la : ∀ k, Wt ((U σ).X k).Ψ D.R.r) (w : ℝ), 0 < w → (∀ k, (∑ τ, ((U σ).X k).spread (la k) τ) ≤ w) → (∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (la k) γ = 1) → ∀ P ∈ holSub (U σ).X la, supE (U σ).X la P ^ 2 ≤ ENNReal.ofReal (supConst D.host.E D.R.r D.host.d l.M w) * petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 := by
  classical
  intro hMB hTB D j H Dw l Xo c U dict hLw σ hσ la w hw0 hspread hχ P hP
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hcusp := abelian₂.holSub_SS siegelSpaceAlgebra_holds (U σ).X la hP
  have hdat := fun k => GlobalTheory.T.exists_selfDual_data_transvection_principal_level D j H Dw l Xo c U dict hLw σ hσ k
  choose Xx hXx hg hΛ hL' M' hM' hk hT using hdat
  have hfs : ∀ k, ∃ x0, IsOrth ((U σ).X k) x0 ∧ ∃ FF, IsFundSet ((U σ).X k) x0 FF := fun k => by
    obtain ⟨x0, ho, FF, hF, -⟩ := GlobalTheory.DriftCovolume.finMu_unconditional D.R.r ((U σ).X k)
    exact ⟨x0, ho, FF, hF⟩
  choose x0 ho FF hF using hfs

  set Φ : ∀ k, Frame ((U σ).X k).Ψ D.R.r → ℝ≥0∞ := fun k u =>
    ENNReal.ofReal (((U σ).X k).pnorm (la k) (((U σ).X k).dom.piecewise (P k) 0) u ^ 2) with hΦdef
  have hsec : ∀ k, ((U σ).X k).IsSec (la k) (P k) := fun k => (hcusp k).1.1
  have hΦm : ∀ k, Measurable (Φ k) := fun k => by
    have hm := GlobalTheory.PeterssonCompare.measurable_pnorm ((U σ).X k) (la k)
      (P := ((U σ).X k).dom.piecewise (P k) 0)
      ((hsec k).1.continuousOn.congr fun u hu => Set.piecewise_eq_of_mem _ _ _ hu)
      (fun u hu => by rw [Set.piecewise_eq_of_notMem _ _ _ hu]; rfl)
    exact ENNReal.measurable_ofReal.comp (hm.pow_const 2)
  have hΦΓ : ∀ k, ∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, Φ k (lact γ x) = Φ k x := by
    intro k γ hγ u hu
    have hu' := GlobalTheory.MajInv.lact_mem_dom ((U σ).X k) (((U σ).X k).Γ_stab γ hγ) hu
    simp only [hΦdef]
    rw [pnorm_piecewise_eq _ _ _ hu, pnorm_piecewise_eq _ _ _ hu', pnorm_lact_eq _ (hsec k) hγ hu]
  have hΦB : ∀ k, ∀ b ∈ Bor ((U σ).X k).Ψ D.R.r, ∀ x ∈ ((U σ).X k).dom, Φ k (rmul x b) = Φ k x := by
    intro k b hb u hu
    have hu' := OrthogonalFrameDomain.rmul_mem_dom ((U σ).X k) hu hb
    simp only [hΦdef]
    rw [pnorm_piecewise_eq _ _ _ hu, pnorm_piecewise_eq _ _ _ hu',
      FrameDegreeData.pnorm_rmul ((U σ).X k) (la k) (P k) (hsec k).2.1 u hu b hb]
  obtain ⟨hS0, hStop, hΦeq⟩ := GlobalTheory.T.adelicProbability_eq_normalised_fundamentalSets D j H Dw l Xo c U dict hLw σ hσ x0 FF (fun k => ⟨ho k, hF k⟩)
  have heq := hΦeq Φ hΦm hΦΓ hΦB
  have hms := GlobalTheory.T.framed_dictionary_bound hMB hTB D j H Dw l Xo c U dict hLw σ hσ x0 FF (fun k => ⟨ho k, hF k⟩)

  obtain ⟨Kf, th, hr', -, -, hU, -⟩ := hLw.dictU σ hσ
  have hdom : ∀ g, (dict σ g).2 ∈ ((U σ).X (dict σ g).1).dom := hU.2.2.2.1

  have hpet : (∫⁻ q, Φ (dict σ q.out).1 (dict σ q.out).2 ∂(muQ1 (D.sp.W j))) =
      petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 := by
    rw [petE, eLpNorm'_eq_lintegral_eNorm, ← ENNReal.rpow_natCast,
      ← ENNReal.rpow_mul]
    norm_num
    refine lintegral_congr fun q => ?_
    simp only [hΦdef, ptN]
    rw [pnorm_piecewise_eq _ _ _ (hdom _), Real.enorm_eq_ofReal (pnorm_nonneg₀ _ _ _ _), ← ENNReal.ofReal_pow (pnorm_nonneg₀ _ _ _ _)]
  set S := ∑ k, muF ((U σ).X k) (x0 k) (FF k) with hSdef

  have hpt : ∀ p : Formalism.L2.Pj.FPt (U σ).X, ENNReal.ofReal (((U σ).X p.1).pnorm (la p.1) (P p.1) p.2) ^ 2 ≤
      ENNReal.ofReal (supConst D.host.E D.R.r D.host.d l.M w) * petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 := by
    rintro ⟨k, y, hy⟩
    rw [← ENNReal.ofReal_pow (pnorm_nonneg₀ _ _ _ _)]
    have h1 := GlobalTheory.SupModel.comp_bound hr ((U σ).X k) (Xx k) (hXx k) (la k) (P k) (hcusp k) w hw0 (hspread k) (hχ k)
      D.host.d l.M (hL' k) (M' k) (hM' k) (hk k) (hT k) (x0 k) (FF k) (ho k) (hF k) y hy
    have h2 : (∫⁻ z in FF k, Φ k (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt ((U σ).X k) (x0 k) z) ∂(muF ((U σ).X k) (x0 k))) ≤
        petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 * ENNReal.ofReal (massLev D.host.E D.R.r l.M) := by
      calc _ ≤ ∑ k', ∫⁻ z in FF k', Φ k' (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt ((U σ).X k') (x0 k') z) ∂(muF ((U σ).X k') (x0 k')) :=
            Finset.single_le_sum (f := fun k' => ∫⁻ z in FF k', Φ k' (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt ((U σ).X k') (x0 k') z)
              ∂(muF ((U σ).X k') (x0 k'))) (fun _ _ => bot_le) (Finset.mem_univ k)
        _ = petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 * S := by rw [← heq, hpet]
        _ ≤ _ := mul_le_mul' le_rfl hms
    by_cases hLc : 0 ≤ locConst D.host.E D.R.r w (epsLev D.host.E D.host.d l.M w)
    · calc _ ≤ ENNReal.ofReal (locConst D.host.E D.R.r w (epsLev D.host.E D.host.d l.M w)) * (petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 * ENNReal.ofReal (massLev D.host.E D.R.r l.M)) :=
            h1.trans (mul_le_mul' le_rfl h2)
        _ = _ := by
          rw [supConst, ENNReal.ofReal_mul hLc]
          ring
    · rw [ENNReal.ofReal_of_nonpos (le_of_lt (not_le.mp hLc)), zero_mul] at h1
      exact (le_antisymm h1 bot_le) ▸ bot_le

  show (⨆ p : Formalism.L2.Pj.FPt (U σ).X, ENNReal.ofReal (((U σ).X p.1).pnorm (la p.1) (P p.1) p.2)) ^ 2 ≤ _
  rcases isEmpty_or_nonempty (Formalism.L2.Pj.FPt (U σ).X) with hE | hN
  · rw [iSup_of_empty]; simp
  · rw [ENNReal.iSup_pow]
    exact iSup_le hpt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedFrameSumPositiveStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_frame_sum_positive : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (la : ∀ k, Wt ((U σ).X k).Ψ D.R.r) (w : ℝ), 0 < w → (∀ k, (∑ τ, ((U σ).X k).spread (la k) τ) ≤ w) → (∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (la k) γ = 1) → ∀ P ∈ holSub (U σ).X la, supE (U σ).X la P ^ 2 ≤ ENNReal.ofReal (supConst D.host.E D.R.r D.host.d l.M w) * petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 := by
  first | exact @GlobalTheory.supPet_principal | exact GlobalTheory.supPet_principal | (intros; apply GlobalTheory.supPet_principal <;> assumption)
end
