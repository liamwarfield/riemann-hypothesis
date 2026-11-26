module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FoldIntegralBesselQuotientSupportedFunctions

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedPeriodEqIntegralBesselPeriods
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnFunctionContinuousOnBesselGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnFunctionContinuousOnBesselGroup
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.PhCont

variable {D : D7}

theorem psiBes_mul_embA (ψ : AddChar (AF D.host.F) ℂ) {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    (o : OrthDec S₀ A L) (θ : D.host.E) (ζ : Fin L.rank → D.host.E) (n : GA D S) (a : GA D A) :
    psiBes ψ d θ (vecB o ζ) (n * embA d o a) = psiBes ψ d θ (vecB o ζ) n := by
  have hX : blockX d (n * embA d o a) = blockX d n := by
    rw [blockX, blockX, mt_mul, Matrix.mul_assoc, embA_apply, d.wittDecomp_anisotropicEmbedding_inclX]
  have hC : coefX d (vecB o ζ) (n * embA d o a) = coefX d (vecB o ζ) n := by
    rw [coefX, coefX, mt_mul, Matrix.mul_assoc, embA_apply, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mulVec_mulVec, GlobalTheory.CharLaws.emb_vecB]
    simp only [Matrix.mul_assoc]
  rw [psiBes, psiBes, simpleSum, simpleSum, hX, hC]

theorem ph_continuousOn : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK)
    (y : X.B.I.Ginf), IsCharAF D.host.F ψ →
      ContinuousOn (fun g => Ph X u hK T (iotaX X h g * (y, X.xu u))) (besGrp B.d B.o : Set (GA D (D.sp.Y 0))) := by
  intro D X h u ψ A B hK T y hψ
  obtain ⟨p, hp, hpv⟩ := GlobalTheory.BesProj.exists_continuous_proj D _ _ A _ _ B.d B.o
  obtain ⟨hcont, hval⟩ := GlobalTheory.Core.Mi.PhCol.ph_colForm D X h u ψ A B hK T
  refine continuousOn_iff_continuous_restrict.2 ?_
  show Continuous fun g : (besGrp B.d B.o : Set (GA D (D.sp.Y 0))) => Ph X u hK T (iotaX X h g.1 * (y, X.xu u))
  have e : (fun g : (besGrp B.d B.o : Set (GA D (D.sp.Y 0))) => Ph X u hK T (iotaX X h g.1 * (y, X.xu u))) =
      fun g => star (psiBes ψ B.d 1 (vecB B.o B.ζ) g.1) * B.colForm T.1 (X.Wu u y) (p g) := by
    funext g
    obtain ⟨g, hg⟩ := g
    obtain ⟨n, hn, a, rfl⟩ := (GlobalTheory.CharLaws.mem_besGrp B.d B.o _).1 hg
    have hpa : p ⟨n * embA B.d B.o a, hg⟩ = a := hpv a ⟨n, hn⟩
    show Ph X u hK T (iotaX X h (n * embA B.d B.o a) * (y, X.xu u)) = _
    rw [hval n hn a y]
    show _ = star (psiBes ψ B.d 1 (vecB B.o B.ζ) (n * embA B.d B.o a)) * B.colForm T.1 (X.Wu u y) (p ⟨n * embA B.d B.o a, hg⟩)
    rw [psiBes_mul_embA]
    exact congrArg (fun a' => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) * B.colForm T.1 (X.Wu u y) a') hpa.symm
  rw [e]
  have hps : Continuous (psiBes ψ B.d 1 (vecB B.o B.ζ)) :=
    GlobalTheory.CharLaws.continuous_psiBes ψ B.d hψ.1 1 _
  exact (continuous_star.comp (hps.comp continuous_subtype_val)).mul ((hcont (X.Wu u y)).2.comp hp)

end GlobalTheory.Core.Mi.PhCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnFunctionContinuousOnBesselGroupStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_column_function_continuousOn_bessel_group : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (y : X.B.I.Ginf), IsCharAF D.host.F ψ → ContinuousOn (fun g => Ph X u hK T (iotaX X h g * (y, X.xu u))) (besGrp B.d B.o : Set (GA D (D.sp.Y 0))) := by
  first | exact @GlobalTheory.Core.Mi.PhCont.ph_continuousOn | exact GlobalTheory.Core.Mi.PhCont.ph_continuousOn | (intros; apply GlobalTheory.Core.Mi.PhCont.ph_continuousOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnScalarFormNormBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnScalarFormNormBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.ColBound

theorem colForm_bound : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK), ∃ C : ℝ, ∀ (ξ : X.Vpi u) (a : GA D A), ‖B.colForm T.1 ξ a‖ ≤ C * ‖ξ‖ := by
  intro D X h u ψ A B hK T
  have hca := (GlobalTheory.Core.Mi.PhCol.ph_colForm D X h u ψ A B hK T).1
  obtain ⟨K, hKc, hKg⟩ := B.cpt
  have hb : ∀ ξ, ∃ c : ℝ, 0 ≤ c ∧ ∀ a, ‖B.colForm T.1 ξ a‖ ≤ c := by
    intro ξ
    obtain ⟨c, hc⟩ := hKc.exists_bound_of_continuousOn ((hca ξ).2.continuousOn)
    refine ⟨max c 0, le_max_right _ _, fun a => ?_⟩
    obtain ⟨γ, hγ, hγK⟩ := hKg a
    rw [← (hca ξ).1 γ hγ a]
    exact (hc _ hγK).trans (le_max_left _ _)
  let b := Module.finBasis ℂ (X.Vpi u)
  choose c hc0 hc using fun i => hb (b i)
  let L : ∀ i, X.Vpi u →L[ℂ] ℂ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  refine ⟨∑ i, ‖L i‖ * c i, fun ξ a => ?_⟩
  have hlin : B.colForm T.1 ξ a = ∑ i, L i ξ * B.colForm T.1 (b i) a := by
    have hξ : ξ = ∑ i, b.repr ξ i • b i := (b.sum_repr ξ).symm
    have e1 : B.colForm T.1 ξ a = (T.1 ξ) (B.toH a) := rfl
    rw [e1]
    conv_lhs => rw [hξ]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
    rfl
  rw [hlin, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  calc ‖L i ξ‖ * ‖B.colForm T.1 (b i) a‖ ≤ (‖L i‖ * ‖ξ‖) * c i :=
        mul_le_mul ((L i).le_opNorm ξ) (hc i a) (norm_nonneg _) (by positivity)
    _ = ‖L i‖ * c i * ‖ξ‖ := by ring

end GlobalTheory.Core.Mi.ColBound

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnScalarFormNormBoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_column_scalar_form_norm_bound : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK), ∃ C : ℝ, ∀ (ξ : X.Vpi u) (a : GA D A), ‖B.colForm T.1 ξ a‖ ≤ C * ‖ξ‖ := by
  first | exact @GlobalTheory.Core.Mi.ColBound.colForm_bound | exact GlobalTheory.Core.Mi.ColBound.colForm_bound | (intros; apply GlobalTheory.Core.Mi.ColBound.colForm_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralFoldViaLintegralFormula
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralFoldViaLintegralFormula
open MeasureTheory

namespace GlobalTheory.FoldIntegral

theorem integral_integral_eq_pos_sub_neg {Y Z : Type} [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Y) (m : Measure Z) [SFinite m] (h : Y × Z → ℝ) (hh : Measurable h)
    (hfin : ∫⁻ y, ∫⁻ s, ‖h (y, s)‖ₑ ∂m ∂ν < ⊤) :
    ∫ y, ∫ s, h (y, s) ∂m ∂ν =
      (∫⁻ y, ∫⁻ s, ENNReal.ofReal (h (y, s)) ∂m ∂ν).toReal -
        (∫⁻ y, ∫⁻ s, ENNReal.ofReal (-h (y, s)) ∂m ∂ν).toReal := by
  have hN : Measurable fun y => ∫⁻ s, ‖h (y, s)‖ₑ ∂m := hh.enorm.lintegral_prod_right'
  have hp : Measurable fun y => ∫⁻ s, ENNReal.ofReal (h (y, s)) ∂m :=
    hh.ennreal_ofReal.lintegral_prod_right'
  have hn : Measurable fun y => ∫⁻ s, ENNReal.ofReal (-h (y, s)) ∂m :=
    hh.neg.ennreal_ofReal.lintegral_prod_right'
  have bp : ∫⁻ y, ∫⁻ s, ENNReal.ofReal (h (y, s)) ∂m ∂ν < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun y => lintegral_mono fun s => Real.ofReal_le_enorm _) hfin
  have bn : ∫⁻ y, ∫⁻ s, ENNReal.ofReal (-h (y, s)) ∂m ∂ν < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun y => lintegral_mono fun s =>
      (Real.ofReal_le_enorm _).trans (enorm_neg _).le) hfin
  rw [← integral_toReal hp.aemeasurable (ae_lt_top hp bp.ne),
    ← integral_toReal hn.aemeasurable (ae_lt_top hn bn.ne),
    ← integral_sub (integrable_toReal_of_lintegral_ne_top hp.aemeasurable bp.ne)
      (integrable_toReal_of_lintegral_ne_top hn.aemeasurable bn.ne)]
  refine integral_congr_ae ?_
  filter_upwards [ae_lt_top hN hfin.ne] with y hy
  exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part
    ⟨(hh.comp measurable_prodMk_left).aestronglyMeasurable, hy⟩

theorem clm_integral_integral {Y Z : Type} [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Y) (m : Measure Z) [SFinite m] (H : Y × Z → ℂ) (hH : Measurable H)
    (hfin : ∫⁻ y, ∫⁻ s, ‖H (y, s)‖ₑ ∂m ∂ν < ⊤) (L : ℂ →L[ℝ] ℝ) :
    L (∫ y, ∫ s, H (y, s) ∂m ∂ν) = ∫ y, ∫ s, L (H (y, s)) ∂m ∂ν := by
  have hN : Measurable fun y => ∫⁻ s, ‖H (y, s)‖ₑ ∂m := hH.enorm.lintegral_prod_right'
  have hI : Integrable (fun y => ∫ s, H (y, s) ∂m) ν :=
    ⟨hH.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable,
      lt_of_le_of_lt (lintegral_mono fun y => enorm_integral_le_lintegral_enorm _) hfin⟩
  rw [← L.integral_comp_comm hI]
  refine integral_congr_ae ?_
  filter_upwards [ae_lt_top hN hfin.ne] with y hy
  exact (L.integral_comp_comm
    ⟨(hH.comp measurable_prodMk_left).aestronglyMeasurable, hy⟩).symm

theorem fold : ∀ {α Y Z : Type} [MeasurableSpace α] [MeasurableSpace Y] [MeasurableSpace Z] (μ : Measure α) (Fs : Set α) (ν : Measure Y) (m : Measure Z) (S : Set Z), m S < ⊤ → ∀ (Φ : Y → Z → α), Measurable (Function.uncurry Φ) → ∀ (c : ℝ), 0 ≤ c → ∀ (P : (α → ENNReal) → Prop), (∀ F : α → ENNReal, Measurable F → P F → ∫⁻ x in Fs, F x ∂μ = ENNReal.ofReal c * ∫⁻ y, ∫⁻ s in S, F (Φ y s) ∂m ∂ν) → ∀ (G : α → ℂ), Measurable G → (∀ φ : ℂ → ENNReal, φ 0 = 0 → P (fun x => φ (G x))) → ∫⁻ y, ∫⁻ s in S, ‖G (Φ y s)‖ₑ ∂m ∂ν < ⊤ → IntegrableOn G Fs μ ∧ ∫ x in Fs, G x ∂μ = (c : ℂ) * ∫ y, ∫ s in S, G (Φ y s) ∂m ∂ν := by
  intro α Y Z _ _ _ μ Fs ν m S hS Φ hΦ c hc P hQ G hG hP hfin
  haveI : IsFiniteMeasure (m.restrict S) := ⟨by simpa using hS⟩
  have hint : IntegrableOn G Fs μ := by
    refine ⟨hG.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, hQ _ hG.enorm (hP (fun z => ‖z‖ₑ) (by simp))]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  refine ⟨hint, ?_⟩
  have hH : Measurable fun p : Y × Z => G (Φ p.1 p.2) := hG.comp hΦ
  have key : ∀ L : ℂ →L[ℝ] ℝ, (∀ z, ‖L z‖ ≤ ‖z‖) →
      L (∫ x in Fs, G x ∂μ) = c * L (∫ y, ∫ s in S, G (Φ y s) ∂m ∂ν) := by
    intro L hL
    have hLm : Measurable L := L.continuous.measurable
    have h1 := clm_integral_integral ν (m.restrict S) _ hH hfin L
    have h2 := integral_integral_eq_pos_sub_neg ν (m.restrict S)
      (fun p : Y × Z => L (G (Φ p.1 p.2))) (hLm.comp hH)
      (lt_of_le_of_lt (lintegral_mono fun y => lintegral_mono fun s => by
        rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal (hL _)) hfin)
    have h3 := hQ (fun x => ENNReal.ofReal (L (G x))) (hLm.comp hG).ennreal_ofReal
      (hP (fun z => ENNReal.ofReal (L z)) (by simp))
    have h4 := hQ (fun x => ENNReal.ofReal (-L (G x))) (hLm.comp hG).neg.ennreal_ofReal
      (hP (fun z => ENNReal.ofReal (-L z)) (by simp))
    simp only at h1 h2
    rw [h1, h2, ← L.integral_comp_comm hint,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part (L.integrable_comp hint), h3, h4,
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc, mul_sub]
  apply Complex.ext
  · have := key Complex.reCLM (fun z => by simpa using Complex.abs_re_le_norm z)
    simpa using this
  · have := key Complex.imCLM (fun z => by simpa using Complex.abs_im_le_norm z)
    simpa using this

end GlobalTheory.FoldIntegral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralFoldViaLintegralFormulaStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_fold_via_lintegral_formula : ∀ {α Y Z : Type} [MeasurableSpace α] [MeasurableSpace Y] [MeasurableSpace Z] (μ : Measure α) (Fs : Set α) (ν : Measure Y) (m : Measure Z) (S : Set Z), m S < ⊤ → ∀ (Φ : Y → Z → α), Measurable (Function.uncurry Φ) → ∀ (c : ℝ), 0 ≤ c → ∀ (P : (α → ENNReal) → Prop), (∀ F : α → ENNReal, Measurable F → P F → ∫⁻ x in Fs, F x ∂μ = ENNReal.ofReal c * ∫⁻ y, ∫⁻ s in S, F (Φ y s) ∂m ∂ν) → ∀ (G : α → ℂ), Measurable G → (∀ φ : ℂ → ENNReal, φ 0 = 0 → P (fun x => φ (G x))) → ∫⁻ y, ∫⁻ s in S, ‖G (Φ y s)‖ₑ ∂m ∂ν < ⊤ → IntegrableOn G Fs μ ∧ ∫ x in Fs, G x ∂μ = (c : ℂ) * ∫ y, ∫ s in S, G (Φ y s) ∂m ∂ν := by
  first | exact @GlobalTheory.FoldIntegral.fold | exact GlobalTheory.FoldIntegral.fold | (intros; apply GlobalTheory.FoldIntegral.fold <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedPeriodEqIntegralBesselPeriods
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Core.MiFold

open scoped ENNReal

variable {D : D7}

theorem mul_mem_sfin (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) {n : X.B.I.Gf} (hn : n ∈ X.NfinU u)
    {g : X.B.I.Gf} (hg : g ∈ Hfin X u) : n * g ∈ SfinU X u := by
  have hfix : ∀ y ∈ fixSet X u, X.B.I.fmat g *ᵥ incl X.B.I y = incl X.B.I y := hg
  have hm : X.B.I.fmat (n * g) = X.B.I.fmat n * X.B.I.fmat g := by simp [Formalism.MainNotions.S.AutInst.fmat]
  have key : ∀ y ∈ fixSet X u,
      (X.B.I.fmat (n * g) - 1) *ᵥ incl X.B.I y = (X.B.I.fmat n - 1) *ᵥ incl X.B.I y := by
    intro y hy
    rw [hm, Matrix.sub_mulVec, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hfix y hy]
  refine ⟨fun a => ?_, ?_⟩
  · rw [key _ (Or.inl (Or.inl ⟨a, rfl⟩))]; exact hn.1 a
  · rw [key _ (Or.inr rfl)]; exact hn.2.1

theorem ph_supp (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (x : X.B.I.GA)
    (hx : Ph X u hK T x ≠ 0) : ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x.2 = s * X.xu u * k := by
  unfold Ph at hx
  split_ifs at hx with hd
  · obtain ⟨n, g, k, hdec⟩ := hd
    obtain ⟨hn, hk, he⟩ := hdec
    exact ⟨n * (g : X.B.I.Gf), mul_mem_sfin X u hn g.2, k, hk, he⟩
  · exact absurd rfl hx

end GlobalTheory.Core.MiFold

namespace GlobalTheory.Core.MiFold

open scoped ENNReal

variable {D : D7}

theorem norm_psiBes {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    (θ : D.host.E) (z : Fin S₀.rank → D.host.E) (n : GA D S) : ‖psiBes ψ d θ z n‖ = 1 := by
  simp only [psiBes, psiE]; exact hψ.2.1 _

theorem iota_mul_assoc (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (γ s : GA D (D.sp.Y 0)) (y : X.B.I.Ginf) (x : X.B.I.Gf) :
    iotaX X h (γ * s) * (y, x) = iotaX X h γ * (iotaX X h s * (y, x)) := by
  rw [map_mul]
  exact mul_assoc _ _ _

end GlobalTheory.Core.MiFold


set_option maxHeartbeats 1000000 in
open GlobalTheory.Core.MiFold in
theorem GlobalTheory.Core.Mi.unfoldedPer : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (hK : X.LevelSubgroupCharacter), IsStdChar D ψ (-1) → ∀ Fs : Set X.B.I.GA, IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) → ∃ c : ℂ, ∀ (T : Cu X u hK), IntegrableOn (Ph X u hK T) Fs (X.B.I.muA X.B.μf) ∧ ∀ f : X.B.I.GA → ℂ, RowFun X f → ∫ x in Fs, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) = c * ∫ y, B.lev.per ψ (B.colForm T.1 (X.Wu u y)) (fun g => f (iotaX X h g * (y, X.xu u))) ∂(X.nuQ u) := by
  intro D X h u ψ A B hK hψ Fs hFs
  obtain ⟨𝓢, h𝓢, h𝓢fin, hI⟩ := (GlobalTheory.T.besselGroup_quotient_fundamentalDomain_cocompact D D.R.rS B.lev).2.2.2
  obtain ⟨c, hc, hQ⟩ := GlobalTheory.T.fold_integral_besselQuotient_supportedFunctions D X h u ψ A B 𝓢 h𝓢 Fs hFs
  refine ⟨(c : ℂ), fun T => ?_⟩
  have hPh := Formalism.L2.SG.PoincareInHH.Cut.phProps_closed X u hK (Formalism.L2.SG.Pf.ksetSplit_holds X u)
    (Formalism.L2.SG.Pf.unipotent_in_level X u) (Formalism.L2.SG.Pf.ratLevi_holds X u) (Formalism.L2.SG.Pf.psiProd_holds X u) T
  have hgrp := GlobalTheory.Core.Mi.besGrp_eq_sGroup D X h u ψ A B
  have hph := GlobalTheory.Core.Mi.PhCol.ph_colForm D X h u ψ A B hK T

  set Φ : X.B.I.Ginf → besGrp B.d B.o → X.B.I.GA := fun y s => iotaX X h s.1 * (y, X.xu u) with hΦdef
  have hι : Continuous fun s : besGrp B.d B.o => iotaX X h s.1 := (iotaX X h).continuous.comp continuous_subtype_val
  have hΦ : Measurable (Function.uncurry Φ) := by
    have h1 : Measurable fun p : X.B.I.Ginf × besGrp B.d B.o => (iotaX X h p.2.1).1 * p.1 :=
      ((continuous_fst.comp hι).measurable.comp measurable_snd).mul measurable_fst
    have h2 : Measurable fun p : X.B.I.Ginf × besGrp B.d B.o => (iotaX X h p.2.1).2 * X.xu u :=
      ((continuous_snd.comp hι).measurable.comp measurable_snd).mul_const _
    exact h1.prodMk h2

  obtain ⟨C, hC⟩ := GlobalTheory.T.bessel_column_scalar_form_norm_bound D X h u ψ A B hK T
  have hbd : ∀ y (s : besGrp B.d B.o), ‖Ph X u hK T (Φ y s)‖ ≤ C * ‖X.Wu u y‖ := by
    intro y s
    obtain ⟨n, hn, a, ha⟩ := (GlobalTheory.CharLaws.mem_besGrp B.d B.o s.1).1 s.2
    simp only [hΦdef, ha, hph.2 n hn a y, norm_mul, norm_star, norm_psiBes hψ.1, one_mul]
    exact hC _ _
  have hWu : ∫⁻ y, ‖X.Wu u y‖ₑ ∂(X.nuQ u) < ⊤ := (X.Wu_spec u).2.2.2.1
  have hfin : ∀ K : ℝ, 0 ≤ K → ∀ G : X.B.I.GA → ℂ, (∀ x, ‖G x‖ ≤ K * ‖Ph X u hK T x‖) →
      ∫⁻ y, ∫⁻ s in 𝓢, ‖G (Φ y s)‖ₑ ∂B.lev.μR ∂(X.nuQ u) < ⊤ := by
    intro K hK0 G hG
    have hpt : ∀ y (s : besGrp B.d B.o), ‖G (Φ y s)‖ₑ ≤ ENNReal.ofReal (K * |C|) * ‖X.Wu u y‖ₑ := by
      intro y s
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ((hG _).trans ?_)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left ((hbd y s).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))) hK0
    calc ∫⁻ y, ∫⁻ s in 𝓢, ‖G (Φ y s)‖ₑ ∂B.lev.μR ∂(X.nuQ u)
        ≤ ∫⁻ y, B.lev.μR 𝓢 * (ENNReal.ofReal (K * |C|) * ‖X.Wu u y‖ₑ) ∂(X.nuQ u) := by
          refine lintegral_mono fun y => ?_
          calc ∫⁻ s in 𝓢, ‖G (Φ y s)‖ₑ ∂B.lev.μR ≤ ∫⁻ s in 𝓢, ENNReal.ofReal (K * |C|) * ‖X.Wu u y‖ₑ ∂B.lev.μR :=
                lintegral_mono fun s => hpt y s
            _ = _ := by rw [setLIntegral_const, mul_comm]
      _ = B.lev.μR 𝓢 * ENNReal.ofReal (K * |C|) * ∫⁻ y, ‖X.Wu u y‖ₑ ∂(X.nuQ u) := by
          rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top h𝓢fin.ne ENNReal.ofReal_ne_top)]
          simp only [mul_assoc]
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top h𝓢fin ENNReal.ofReal_lt_top) hWu

  set P : (X.B.I.GA → ENNReal) → Prop := fun F => (∀ γ ∈ Srat X u, ∀ x, F (γ * x) = F x) ∧
    (∀ k ∈ X.K2, ∀ x, F (x * (1, k)) = F x) ∧
    (∀ x, F x ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x.2 = s * X.xu u * k) with hPdef
  have hQ' : ∀ F : X.B.I.GA → ENNReal, Measurable F → P F →
      ∫⁻ x in Fs, F x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c * ∫⁻ y, ∫⁻ s in 𝓢, F (Φ y s) ∂B.lev.μR ∂(X.nuQ u) :=
    fun F hF hP => hQ F hF hP.1 hP.2.1 hP.2.2
  have hsupp : ∀ G : X.B.I.GA → ℂ, (∀ x, G x ≠ 0 → Ph X u hK T x ≠ 0) → ∀ φ : ℂ → ENNReal, φ 0 = 0 →
      ∀ x, φ (G x) ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x.2 = s * X.xu u * k := by
    intro G hG φ hφ x hx
    refine ph_supp X u hK T x (hG x ?_)
    intro h0; rw [h0, hφ] at hx; exact hx rfl
  have hchi : ∀ k ∈ X.K2, ‖X.chi2 k‖ = 1 := hK.2.2.2.2

  have hint : IntegrableOn (Ph X u hK T) Fs (X.B.I.muA X.B.μf) := by
    refine ⟨hPh.1.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, hQ' (fun x => ‖Ph X u hK T x‖ₑ) hPh.1.enorm ⟨fun γ hγ x => by dsimp only; rw [hPh.2.1 γ hγ x],
      fun k hk x => by dsimp only; rw [hPh.2.2.1 x k hk, enorm_mul, ← ofReal_norm_eq_enorm (X.chi2 k), hchi k hk,
        ENNReal.ofReal_one, one_mul],
      hsupp (Ph X u hK T) (fun x hx => hx) (fun z => ‖z‖ₑ) enorm_zero⟩]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin 1 zero_le_one _ fun x => by rw [one_mul])
  refine ⟨hint, fun f hf => ?_⟩
  obtain ⟨Cf, hCf⟩ := hf.bdd
  have hCf0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf 1)
  have hfm : Measurable f := hf.cont.measurable

  obtain ⟨G, hGdef⟩ : ∃ G : X.B.I.GA → ℂ, G = fun x => f x * Ph X u hK T x := ⟨_, rfl⟩
  have hGl : ∀ γ ∈ Srat X u, ∀ x, G (γ * x) = G x := by
    intro γ hγ x
    simp only [hGdef, hPh.2.1 γ hγ x, hf.left γ (Subgroup.mem_inf.1 hγ).1 x]
  have hGr : ∀ k ∈ X.K2, ∀ x, G (x * (1, k)) = G x := by
    intro k hk x
    have h1 : star (X.chi2 k) * X.chi2 k = 1 := by
      rw [Complex.star_def, Complex.conj_mul', hchi k hk]; norm_num
    simp only [hGdef, hPh.2.2.1 x k hk, hf.right k hk x]
    calc star (X.chi2 k) * f x * (X.chi2 k * Ph X u hK T x) = (star (X.chi2 k) * X.chi2 k) * (f x * Ph X u hK T x) := by ring
      _ = _ := by rw [h1, one_mul]
  have hGs : ∀ x, G x ≠ 0 → Ph X u hK T x ≠ 0 := fun x hx h0 => hx (by simp only [hGdef, h0, mul_zero])
  have hGm : Measurable G := by rw [hGdef]; exact hfm.mul hPh.1
  have hGb : ∀ x, ‖G x‖ ≤ Cf * ‖Ph X u hK T x‖ := fun x => by
    rw [hGdef, norm_mul]; exact mul_le_mul_of_nonneg_right (hCf x) (norm_nonneg _)
  obtain ⟨-, hfold⟩ := GlobalTheory.T.integral_fold_via_lintegral_formula (X.B.I.muA X.B.μf) Fs (X.nuQ u) B.lev.μR 𝓢 h𝓢fin Φ hΦ c hc.le P hQ' G hGm
    (fun φ hφ => ⟨fun γ hγ x => by simp only [hGl γ hγ x], fun k hk x => by simp only [hGr k hk x],
      hsupp G hGs φ hφ⟩) (hfin Cf hCf0 G hGb)
  rw [show (∫ x in Fs, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf)) = ∫ x in Fs, G x ∂(X.B.I.muA X.B.μf) by rw [hGdef], hfold]
  subst hGdef
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)

  have hcont : ContinuousOn (fun g => f (iotaX X h g * (y, X.xu u)) * Ph X u hK T (iotaX X h g * (y, X.xu u)))
      (besGrp B.d B.o : Set (GA D (D.sp.Y 0))) := by
    refine ContinuousOn.mul ?_ (GlobalTheory.T.bessel_column_function_continuousOn_bessel_group D X h u ψ A B hK T y hψ.1)
    exact (hf.cont.comp ((iotaX X h).continuous.mul continuous_const)).continuousOn
  have hinv : ∀ γ ∈ GQ (D.sp.Y 0) ⊓ besGrp B.d B.o, ∀ s ∈ besGrp B.d B.o,
      f (iotaX X h (γ * s) * (y, X.xu u)) * Ph X u hK T (iotaX X h (γ * s) * (y, X.xu u)) =
        f (iotaX X h s * (y, X.xu u)) * Ph X u hK T (iotaX X h s * (y, X.xu u)) := by
    intro γ hγ s _
    have hγ' := (hgrp.2 γ).1 hγ
    have := hGl _ hγ' (iotaX X h s * (y, X.xu u))
    dsimp only at this
    exact (congrArg (fun z => f z * Ph X u hK T z) (iota_mul_assoc X h γ s y (X.xu u))).trans this
  have hIy := (hI _ hcont hinv).2
  refine hIy.trans ?_
  simp only [BesLev.per, besPer, besFun]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  simp only [hph.2 n.1 n.2 a y]
  ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedPeriodEqIntegralBesselPeriodsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedPeriod_eq_integral_besselPeriods : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (hK : X.LevelSubgroupCharacter), IsStdChar D ψ (-1) → ∀ Fs : Set X.B.I.GA, IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) → ∃ c : ℂ, ∀ (T : Cu X u hK), IntegrableOn (Ph X u hK T) Fs (X.B.I.muA X.B.μf) ∧ ∀ f : X.B.I.GA → ℂ, RowFun X f → ∫ x in Fs, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) = c * ∫ y, B.lev.per ψ (B.colForm T.1 (X.Wu u y)) (fun g => f (iotaX X h g * (y, X.xu u))) ∂(X.nuQ u) := by
  first | exact @GlobalTheory.Core.Mi.unfoldedPer | exact GlobalTheory.Core.Mi.unfoldedPer | (intros; apply GlobalTheory.Core.Mi.unfoldedPer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InnerPoincareSeriesEqSetIntegralUnfolding
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InnerPoincareSeriesEqSetIntegralUnfolding
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open Formalism.MainNotions.LeviCoordinates in
theorem GlobalTheory.Core.Mi.inner_pser_eq_setIntegral : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (Dt Fs : Set X.B.I.GA), IsReps X u Dt → InHH X u hK → IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) → ∀ T : Cu X u hK, IntegrableOn (Ph X u hK T) Fs (X.B.I.muA X.B.μf) → ∀ (f : X.B.I.GA → ℂ) (φ : L2X X), RowFun X f → (φ : X.B.I.GA → ℂ) =ᵐ[muX X] f → ⟪star φ, PuFun X u hK Dt T⟫_ℂ = ∫ x in Fs, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) := by
  intro D X u hK Dt Fs hD hin hFs T hPI f φ hf hφf
  have := X.B.sf
  have := X.B.haar
  have := Formalism.L2.SG.Pf.gf_secondCountable X.B.I
  have := Formalism.L2.SG.Pf.muf_right X
  have := rr_muA_sigmaFinite X.B.I X.B.μf
  have := rr_muA_left X.B.I X.B.μf
  have := rr_muA_right X.B.I X.B.μf
  have hPP := Formalism.L2.SG.PoincareInHH.Cut.phProps_closed X u hK (Formalism.L2.SG.Pf.ksetSplit_holds X u)
    (Formalism.L2.SG.Pf.unipotent_in_level X u) (Formalism.L2.SG.Pf.ratLevi_holds X u) (Formalism.L2.SG.Pf.psiProd_holds X u)
  have hFD := rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec
  have hS : Srat X u ≤ rr_GF X.B.I := inf_le_left
  have hDc : Dt.Countable :=
    (Set.countable_coe_iff.1 (inferInstance : Countable (rr_GF X.B.I))).mono hD.1
  have := hDc.to_subtype
  have hSc : Countable (Srat X u) := Function.Injective.countable (Subgroup.inclusion_injective hS)
  have hSinv : SMulInvariantMeasure (Srat X u) X.B.I.GA (X.B.I.muA X.B.μf) := ⟨fun s A _ => by
      show (X.B.I.muA X.B.μf) ((fun y => (s : X.B.I.GA) * y) ⁻¹' A) = (X.B.I.muA X.B.μf) A
      exact measure_preimage_mul _ (s : X.B.I.GA) A⟩
  have hPm : Measurable (Ph X u hK T) := (hPP T).1
  have hPinv : ∀ s ∈ Srat X u, ∀ y, Ph X u hK T (s * y) = Ph X u hK T y := (hPP T).2.1
  have hfm : Measurable f := hf.cont.measurable
  obtain ⟨C, hC⟩ := hf.bdd
  have hfinv : ∀ γ ∈ rr_GF X.B.I, ∀ y, f (γ * y) = f y := fun γ hγ y => hf.left γ hγ y
  have hginv : ∀ (s : Srat X u) (x : X.B.I.GA),
      (fun x => f x * Ph X u hK T x) ((s : X.B.I.GA) * x) = (fun x => f x * Ph X u hK T x) x := by
    intro s x
    show f (s * x) * Ph X u hK T (s * x) = f x * Ph X u hK T x
    rw [hfinv s (hS s.2) x, hPinv s s.2 x]
  have hF' : IsFundamentalDomain (Srat X u) (⋃ δ ∈ Dt, (fun y => δ * y) '' X.B.fund) (X.B.I.muA X.B.μf) :=
    rr_isFD (Formalism.L2.SG.Pf.InHHLeaf.rr_FD_union hFD (Srat X u) hS Dt hD hDc)
  have hgFs : IntegrableOn (fun x => f x * Ph X u hK T x) Fs (X.B.I.muA X.B.μf) :=
    Integrable.bdd_mul (c := C) hPI hfm.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  have hgFs' := (hFs.integrableOn_iff hF' hginv).1 hgFs
  have e1 : ∫ x in Fs, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) =
      ∫ x in (⋃ δ ∈ Dt, (fun y => δ * y) '' X.B.fund), f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) :=
    hFs.setIntegral_eq hF' (f := fun x => f x * Ph X u hK T x) hginv
  have hU : (⋃ δ ∈ Dt, (fun y => δ * y) '' X.B.fund) = ⋃ δ : Dt, (fun y => (δ : X.B.I.GA) * y) '' X.B.fund := by
    rw [Set.biUnion_eq_iUnion]
  have hmeas : ∀ δ : Dt, MeasurableSet ((fun y => (δ : X.B.I.GA) * y) '' X.B.fund) := by
    intro δ; rw [Formalism.L2.SG.Pf.InHHLeaf.img_mul]; exact hFD.meas.preimage (measurable_const_mul _)
  have hdisj : Pairwise (Function.onFun (AEDisjoint (X.B.I.muA X.B.μf))
      fun δ : Dt => (fun y => (δ : X.B.I.GA) * y) '' X.B.fund) := by
    intro δ δ' hne
    show X.B.I.muA X.B.μf (((fun y => (δ : X.B.I.GA) * y) '' X.B.fund) ∩ ((fun y => (δ' : X.B.I.GA) * y) '' X.B.fund)) = 0
    have hsub : ((fun y => (δ : X.B.I.GA) * y) '' X.B.fund) ∩ ((fun y => (δ' : X.B.I.GA) * y) '' X.B.fund) ⊆
        (fun y => (δ' : X.B.I.GA) * y) '' ((fun y => ((δ' : X.B.I.GA)⁻¹ * δ) * y) '' X.B.fund ∩ X.B.fund) := by
      rintro _ ⟨⟨x, hx, rfl⟩, ⟨x', hx', hxx⟩⟩
      simp only at hxx
      refine ⟨x', ⟨⟨x, hx, ?_⟩, hx'⟩, hxx⟩
      show (δ' : X.B.I.GA)⁻¹ * δ * x = x'
      rw [show x' = (δ' : X.B.I.GA)⁻¹ * ((δ' : X.B.I.GA) * x') by group, hxx]; group
    refine measure_mono_null hsub ?_
    have hγ : (δ' : X.B.I.GA)⁻¹ * δ ∈ rr_GF X.B.I := (rr_GF X.B.I).mul_mem ((rr_GF X.B.I).inv_mem (hD.1 δ'.2)) (hD.1 δ.2)
    have hne' : (δ' : X.B.I.GA)⁻¹ * δ ≠ 1 := by
      intro h1
      apply hne
      apply Subtype.ext
      rw [← mul_one (δ' : X.B.I.GA), ← h1]; group
    rw [Formalism.L2.SG.Pf.InHHLeaf.img_mul, measure_preimage_mul]
    exact hFD.disj _ hγ hne'
  have e2 : ∫ x in (⋃ δ ∈ Dt, (fun y => δ * y) '' X.B.fund), f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) =
      ∑' δ : Dt, ∫ x in (fun y => (δ : X.B.I.GA) * y) '' X.B.fund, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) := by
    rw [hU] at hgFs' ⊢
    exact integral_iUnion_ae (fun δ => (hmeas δ).nullMeasurableSet) hdisj hgFs'
  have e3 : ∀ δ : Dt, ∫ x in (fun y => (δ : X.B.I.GA) * y) '' X.B.fund, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) =
      ∫ y in X.B.fund, f y * Ph X u hK T ((δ : X.B.I.GA) * y) ∂(X.B.I.muA X.B.μf) := by
    intro δ
    have hpre : (fun y => (δ : X.B.I.GA) * y) ⁻¹' ((fun y => (δ : X.B.I.GA) * y) '' X.B.fund) = X.B.fund :=
      Set.preimage_image_eq _ (mul_right_injective (δ : X.B.I.GA))
    have h2 := (measurePreserving_mul_left (X.B.I.muA X.B.μf) (δ : X.B.I.GA)).setIntegral_preimage_emb
      (measurableEmbedding_mulLeft (δ : X.B.I.GA)) (fun x => f x * Ph X u hK T x)
      ((fun y => (δ : X.B.I.GA) * y) '' X.B.fund)
    rw [hpre] at h2
    rw [← h2]
    refine setIntegral_congr_fun hFD.meas fun y _ => ?_
    show f ((δ : X.B.I.GA) * y) * Ph X u hK T ((δ : X.B.I.GA) * y) = f y * Ph X u hK T ((δ : X.B.I.GA) * y)
    rw [hfinv _ (hD.1 δ.2) y]
  have hbound : ∑' δ : Dt, ∫⁻ y in X.B.fund, ‖f y * Ph X u hK T ((δ : X.B.I.GA) * y)‖ₑ ∂(X.B.I.muA X.B.μf) ≠ ⊤ := by
    have hle : ∀ δ : Dt, ∫⁻ y in X.B.fund, ‖f y * Ph X u hK T ((δ : X.B.I.GA) * y)‖ₑ ∂(X.B.I.muA X.B.μf) ≤
        ENNReal.ofReal C * ∫⁻ y in X.B.fund, ‖Ph X u hK T ((δ : X.B.I.GA) * y)‖ₑ ∂(X.B.I.muA X.B.μf) := by
      intro δ
      rw [← lintegral_const_mul (f := fun y => ‖Ph X u hK T ((δ : X.B.I.GA) * y)‖ₑ) _ (hPm.comp (measurable_const_mul _)).enorm]
      refine lintegral_mono fun y => ?_
      rw [enorm_mul]
      refine mul_le_mul' ?_ le_rfl
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hC y)
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [ENNReal.tsum_mul_left, ← lintegral_tsum (f := fun (δ : Dt) y => ‖Ph X u hK T ((δ : X.B.I.GA) * y)‖ₑ) (fun δ => (hPm.comp (measurable_const_mul _)).enorm.aemeasurable),
      Formalism.L2.SG.Pf.InHHLeaf.unfold_lint hFD (Srat X u) hS Dt hD Fs hFs (fun w => ‖Ph X u hK T w‖ₑ) hPm.enorm
        (fun s hs y => by simp only [hPinv s hs y])]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hPI.2.ne
  have e4 : ∫ y in X.B.fund, f y * Pser X u hK Dt T y ∂(X.B.I.muA X.B.μf) =
      ∑' δ : Dt, ∫ y in X.B.fund, f y * Ph X u hK T ((δ : X.B.I.GA) * y) ∂(X.B.I.muA X.B.μf) := by
    have hfun : (fun y => f y * Pser X u hK Dt T y) = fun y => ∑' δ : Dt, f y * Ph X u hK T ((δ : X.B.I.GA) * y) := by
      funext y
      show f y * ∑' δ : Dt, Ph X u hK T ((δ : X.B.I.GA) * y) = _
      rw [tsum_mul_left]
    rw [hfun]
    exact integral_tsum (fun δ => (hfm.mul (hPm.comp (measurable_const_mul _))).aestronglyMeasurable) hbound
  have hm := (hin T Dt hD).2.2.1
  have eL : ⟪star φ, PuFun X u hK Dt T⟫_ℂ = ∫ y in X.B.fund, f y * Pser X u hK Dt T y ∂(X.B.I.muA X.B.μf) := by
    have e0 : PuFun X u hK Dt T = hm.toLp (Pser X u hK Dt T) := dif_pos hm
    rw [e0, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_star φ, hm.coeFn_toLp, hφf] with a h1 h2 h3
    rw [h1, h2, Pi.star_apply, h3, RCLike.inner_apply]
    rw [mul_comm]
    congr 1
    first
      | exact Complex.conj_conj (f a)
      | simp [Complex.star_def]
  rw [eL, e4, e1, e2]
  exact tsum_congr fun δ => (e3 δ).symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InnerPoincareSeriesEqSetIntegralUnfoldingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_poincareSeries_eq_setIntegral_unfolding : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (Dt Fs : Set X.B.I.GA), IsReps X u Dt → InHH X u hK → IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) → ∀ T : Cu X u hK, IntegrableOn (Ph X u hK T) Fs (X.B.I.muA X.B.μf) → ∀ (f : X.B.I.GA → ℂ) (φ : L2X X), RowFun X f → (φ : X.B.I.GA → ℂ) =ᵐ[muX X] f → ⟪star φ, PuFun X u hK Dt T⟫_ℂ = ∫ x in Fs, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) := by
  first | exact @GlobalTheory.Core.Mi.inner_pser_eq_setIntegral | exact GlobalTheory.Core.Mi.inner_pser_eq_setIntegral | (intros; apply GlobalTheory.Core.Mi.inner_pser_eq_setIntegral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateRowPairingPoincareSeriesBesselPeriods
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem perLaw_holds : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (Y : Formalism.L2.SG.Full.Full X), IsStdChar D ψ (-1) → InHH X u Y.hK → B.PerLaw Y := by
  intro D X h u ψ A B Y hψ hH
  obtain ⟨Fs, hFs⟩ := Formalism.L2.SG.PoincareInHH.Cut.sratFund_holds X u
  obtain ⟨c, hc⟩ := GlobalTheory.T.unfoldedPeriod_eq_integral_besselPeriods D X h u ψ A B Y.hK hψ Fs hFs
  refine ⟨c, fun T f φ hf hφ => ?_⟩
  rw [GlobalTheory.T.inner_poincareSeries_eq_setIntegral_unfolding D X u Y.hK (Y.Dt u) Fs (Y.reps u) hH hFs T (hc T).1 f φ hf hφ]
  exact (hc T).2 f hf

end GlobalTheory.Core.Mi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateRowPairingPoincareSeriesBesselPeriodsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateRow_pairing_poincareSeries_besselPeriods : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (Y : Formalism.L2.SG.Full.Full X), IsStdChar D ψ (-1) → InHH X u Y.hK → B.PerLaw Y := by
  first | exact @GlobalTheory.Core.Mi.perLaw_holds | exact GlobalTheory.Core.Mi.perLaw_holds | (intros; apply GlobalTheory.Core.Mi.perLaw_holds <;> assumption)
end
