module

public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LeadingBlockLowerEntriesToBlockCoords
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuAllData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBallLeadingGramMinorLowerBoundFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralCutoffGramBoundMixedBlockRankFourLtTopStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralCutoffGramBoundMixedBlockRankThreeLtTop
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralCutoffGramBoundMixedBlockRankThreeLtTop
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall.Fin3

theorem norm_one_add_conj_mul (z : ℂ) : ‖1 + (starRingEnd ℂ) z * z‖ = 1 + ‖z‖ ^ 2 := by
  rw [Complex.conj_mul', show (1 : ℂ) + (‖z‖ : ℂ) ^ 2 = ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_of_nonneg (by positivity)]

theorem gB_one (w : Low 3 → ℂ) : gB 1 w = (1 + ‖w ⟨(2, 1), by decide⟩‖ ^ 2) ^ (-2 : ℤ) := by
  simp [gB, Fin.prod_univ_two, colGram, lminor, Matrix.det_fin_one, Matrix.mul_apply, Fin.sum_univ_two, blkW, lowMat]
  rw [norm_one_add_conj_mul]

theorem gB_two (w : Low 3 → ℂ) : gB 2 w = (1 + ‖w ⟨(1, 0), by decide⟩‖ ^ 2) ^ (-2 : ℤ) := by
  simp [gB, Fin.prod_univ_two, colGram, lminor, Matrix.det_fin_one, Matrix.mul_apply, Fin.sum_univ_two, blkW, lowMat]
  rw [norm_one_add_conj_mul]

noncomputable def dom (x : ℂ) : ℝ≥0∞ :=
  (Metric.closedBall (0 : ℂ) 1).indicator 1 x + ENNReal.ofReal ((1 + ‖x‖ ^ 2) ^ (-(4 : ℝ) / 2))

theorem measurable_dom : Measurable dom := by
  unfold dom
  refine Measurable.add ((measurable_const).indicator Metric.isClosed_closedBall.measurableSet) ?_
  exact ENNReal.measurable_ofReal.comp (by fun_prop)

theorem lintegral_dom_lt_top : ∫⁻ x, dom x < ⊤ := by
  unfold dom
  rw [lintegral_add_left (f := (Metric.closedBall (0 : ℂ) 1).indicator (1 : ℂ → ℝ≥0∞))
    (measurable_one.indicator Metric.isClosed_closedBall.measurableSet)]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · rw [lintegral_indicator_one Metric.isClosed_closedBall.measurableSet]
    exact measure_closedBall_lt_top
  · exact (integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 4)
      (by rw [Complex.finrank_real_complex]; norm_num)).lintegral_lt_top

theorem le_prod_dom (w : Low 3 → ℂ) (e : Low 3) (hw : ∀ p, p ≠ e → ‖w p‖ ≤ 1) :
    ENNReal.ofReal ((1 + ‖w e‖ ^ 2) ^ (-2 : ℤ)) ≤ ∏ p, dom (w p) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e)]
  calc ENNReal.ofReal ((1 + ‖w e‖ ^ 2) ^ (-2 : ℤ)) = ENNReal.ofReal ((1 + ‖w e‖ ^ 2) ^ (-2 : ℤ)) * 1 :=
        (mul_one _).symm
    _ ≤ dom (w e) * ∏ p ∈ Finset.univ.erase e, dom (w p) := by
      refine mul_le_mul' ?_ ?_
      · unfold dom
        refine le_trans (le_of_eq ?_) le_add_self
        congr 1
        rw [show (-(4 : ℝ) / 2) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      · refine Finset.one_le_prod' fun p hp => ?_
        unfold dom
        refine le_trans (le_of_eq ?_) le_self_add
        rw [Set.indicator_of_mem (by simpa using hw p (Finset.ne_of_mem_erase hp))]
        rfl

theorem hB_le (p0 : ℕ) (hp : p0 = 1 ∨ p0 = 2) (w : Low 3 → ℂ) : hB p0 w ≤ ∏ p, dom (w p) := by
  unfold hB
  by_cases hS : w ∈ {w : Low 3 → ℂ | ∀ p : Low 3, (p.1.2 : ℕ) < p0 → p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1}
  · rw [Set.indicator_of_mem hS]
    rcases hp with rfl | rfl
    · rw [gB_one]
      refine le_prod_dom w _ fun p hpe => hS p ?_ ?_
      · revert hpe; revert p; decide
      · revert hpe; revert p; decide
    · rw [gB_two]
      refine le_prod_dom w _ fun p hpe => hS p ?_ ?_
      · revert hpe; revert p; decide
      · revert hpe; revert p; decide
  · rw [Set.indicator_of_notMem hS]
    exact bot_le

theorem lintegral_hB_lt_top : ∀ p0 : ℕ, (p0 = 1 ∨ p0 = 2) → ∫⁻ w : Low 3 → ℂ, hB p0 w < ⊤ := by
  intro p0 hp
  refine lt_of_le_of_lt (lintegral_mono fun w => hB_le p0 hp w) ?_
  have h := GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod (E := fun _ : Low 3 => ℂ)
    (μ := fun _ => (volume : Measure ℂ)) (f := fun _ => dom) (fun _ => measurable_dom.aemeasurable)
  rw [volume_pi, h]
  exact ENNReal.prod_lt_top fun _ _ => lintegral_dom_lt_top

end GlobalTheory.IntBall.Fin3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralCutoffGramBoundMixedBlockRankThreeLtTopStatement
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_cutoffGramBoundMixedBlock_rankThree_lt_top : ∀ p0 : ℕ, (p0 = 1 ∨ p0 = 2) → ∫⁻ w : Low 3 → ℂ, hB p0 w < ⊤ := by
  first | exact @GlobalTheory.IntBall.Fin3.lintegral_hB_lt_top | exact GlobalTheory.IntBall.Fin3.lintegral_hB_lt_top | (intros; apply GlobalTheory.IntBall.Fin3.lintegral_hB_lt_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralProdChartCoordinatesEqProd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralProdChartCoordinatesEqProd
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall

noncomputable section

theorem measurePreserving_curry_lowCoord (ι κ : Type) [Fintype ι] [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℂ) volume volume := by
  have h : (volume : Measure (ι × κ → ℂ)) =
      (volume : Measure (ι → κ → ℂ)).map (MeasurableEquiv.curry ι κ ℂ).symm := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi hs)]
    have e : (MeasurableEquiv.curry ι κ ℂ).symm ⁻¹' Set.univ.pi s =
        Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
      ext f; simp [MeasurableEquiv.coe_curry_symm, Function.uncurry]
    rw [e, volume_pi, Measure.pi_pi]
    simp_rw [volume_pi, Measure.pi_pi]
    rw [Fintype.prod_prod_type]
  refine ⟨(MeasurableEquiv.curry ι κ ℂ).measurable, ?_⟩
  rw [h, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
  simp

theorem lintegral_prod_zOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (h : (Low r → ℂ) → ℝ≥0∞), Measurable h → ∫⁻ z, ∏ τ, h (zOf X z τ) = ∏ _τ : X.Ψ, ∫⁻ w, h w := by
  intro E _ _ _ r X h hh
  set e := Fintype.equivFin (Ent X) with he
  set G : (Fin (nd X) → ℂ) → ℝ≥0∞ := fun y => ∏ τ, h (fun p => y (e ⟨τ, p⟩)) with hG
  have hGm : Measurable G :=
    Finset.measurable_prod _ fun τ _ => hh.comp (Measurable.of_eval fun p => measurable_pi_apply _)
  have s1 : ∫⁻ z : V (nd X), ∏ τ, h (zOf X z τ) = ∫⁻ y, G y :=
    (GlobalTheory.volume_preserving_ofLp_complex (Fin (nd X))).lintegral_comp hGm
  set K : (X.Ψ → Low r → ℂ) → ℝ≥0∞ := fun g => ∏ τ, h (g τ) with hK
  have hKm : Measurable K := Finset.measurable_prod _ fun τ _ => hh.comp (measurable_pi_apply τ)
  have s2 : ∫⁻ y, G y = ∫⁻ f : Ent X → ℂ, K (MeasurableEquiv.curry X.Ψ (Low r) ℂ f) := by
    refine ((volume_measurePreserving_piCongrLeft (fun _ => ℂ) e).lintegral_comp hGm).symm.trans
      (lintegral_congr fun f => ?_)
    simp only [hG, hK, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    rfl
  have s3 : ∫⁻ f : Ent X → ℂ, K (MeasurableEquiv.curry X.Ψ (Low r) ℂ f) = ∫⁻ g, K g :=
    (measurePreserving_curry_lowCoord X.Ψ (Low r)).lintegral_comp hKm
  rw [s1, s2, s3, hK, volume_pi]
  exact GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod fun _ => hh.aemeasurable

end

end GlobalTheory.IntBall
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralProdChartCoordinatesEqProdStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_prod_chartCoordinates_eq_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (h : (Low r → ℂ) → ℝ≥0∞), Measurable h → ∫⁻ z, ∏ τ, h (zOf X z τ) = ∏ _τ : X.Ψ, ∫⁻ w, h w := by
  first | exact @GlobalTheory.IntBall.lintegral_prod_zOf | exact GlobalTheory.IntBall.lintegral_prod_zOf | (intros; apply GlobalTheory.IntBall.lintegral_prod_zOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralExpRhoEqSetLIntegralUnitBallDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralExpRhoEqSetLIntegralUnitBallDomain
namespace GlobalTheory.IntBall

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

noncomputable section

theorem lintegral_exp_muF_eq_setLIntegral_Om (E : Type) [Field E] [NumberField E] [IsCMField E]
    (r : ℕ) (X : Data E r) (x0 : Base X) (s : ℝ) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (-(s * rhF X x0.1 z))) ∂muF X x0.1 =
      ∫⁻ z in Om X, ENNReal.ofReal (density X x0 z) * ENNReal.ofReal (Real.exp (-(s * rho X z))) := by
  have hT : Measurable (GlobalTheory.UpCoordCompare.toEntries X) :=
    (GlobalTheory.UpCoordCompare.contDiff_toEntries X).continuous.measurable
  have hf : Measurable fun z => ENNReal.ofReal (Real.exp (-(s * rhF X x0.1 z))) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((GlobalTheory.PoleDbar.measurable_rhF X x0.1).const_mul s).neg)
  have hd : Measurable fun z => ENNReal.ofReal (density X x0 z) := by
    have e : (fun z => ENNReal.ofReal (density X x0 z)) =
        (fun z => ENNReal.ofReal (densF X x0.1 z)) ∘ GlobalTheory.UpCoordCompare.toEntries X := by
      funext z
      simp only [Function.comp_apply, GlobalTheory.UpCoordCompare.densF_toEntries]
    rw [e]
    exact (OntoC.measurable_densF X x0.1).comp hT
  have hOm : MeasurableSet (Om X) := by
    have : Om X = GlobalTheory.UpCoordCompare.toEntries X ⁻¹' OmF X x0.1 := by
      ext z; exact (GlobalTheory.UpCoordCompare.toEntries_mem_OmF_iff X x0 z).symm
    rw [this]
    exact hT (ExF.isOpen_OmF X x0.1).measurableSet
  rw [← GlobalTheory.UpCoordCompare.map_mu X x0, lintegral_map hf hT, mu,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ hd
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setLIntegral_congr_fun hOm fun z hz => ?_
  simp only [Pi.mul_apply, GlobalTheory.UpCoordCompare.rhF_toEntries X x0 hz]

end

end GlobalTheory.IntBall
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralExpRhoEqSetLIntegralUnitBallDomainStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_expRho_eq_setLIntegral_unitBallDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Base X) (s : ℝ), ∫⁻ z, ENNReal.ofReal (Real.exp (-(s * rhF X x0.1 z))) ∂muF X x0.1 = ∫⁻ z in Om X, ENNReal.ofReal (density X x0 z) * ENNReal.ofReal (Real.exp (-(s * rho X z))) := by
  first | exact @GlobalTheory.IntBall.lintegral_exp_muF_eq_setLIntegral_Om | exact GlobalTheory.IntBall.lintegral_exp_muF_eq_setLIntegral_Om | (intros; apply GlobalTheory.IntBall.lintegral_exp_muF_eq_setLIntegral_Om <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetOneSubOffDiagonalBlockGramLeOneBall
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetOneSubOffDiagonalBlockGramLeOneBall
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall.DetLe

theorem re_det_one_sub_le_of_unique {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι] [Unique ι]
    (Z : Matrix κ ι ℂ) : ((1 - Zᴴ * Z).det).re ≤ 1 := by
  rw [Matrix.det_unique]
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.sub_re, Complex.one_re, Complex.re_sum]
  have : ∀ a : κ, 0 ≤ (star (Z a default) * Z a default).re := by
    intro a
    rw [show star (Z a default) = (starRingEnd ℂ) (Z a default) from rfl, mul_comm, Complex.mul_conj]
    simp [Complex.normSq_nonneg]
  linarith [Finset.sum_nonneg fun a (_ : a ∈ Finset.univ) => this a]

theorem re_det_one_sub_le_of_unique' {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] [Unique κ] (Z : Matrix κ ι ℂ) : ((1 - Zᴴ * Z).det).re ≤ 1 := by
  rw [Matrix.det_one_sub_mul_comm]
  have := re_det_one_sub_le_of_unique (Zᴴ)
  rwa [Matrix.conjTranspose_conjTranspose] at this

end GlobalTheory.IntBall.DetLe

namespace GlobalTheory.IntBall

open GlobalTheory.IntBall.DetLe

theorem zDet_le_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (X.p0 = 1 ∨ X.p0 + 1 = r) → ∀ z : V (nd X), z ∈ Om X → ∀ τ : X.Ψ, zDet X z τ ≤ 1 := by
  intro E _ _ _ r X h z _ τ
  have hle := X.p0_le
  unfold zDet
  rcases h with h | h
  · letI : Unique {b : Fin r // (b : ℕ) < X.p0} :=
      { default := ⟨⟨0, by omega⟩, by simp [h]⟩
        uniq := fun b => Subtype.ext (Fin.ext (by have := b.2; simp only; omega)) }
    exact re_det_one_sub_le_of_unique _
  · letI : Unique {a : Fin r // X.p0 ≤ (a : ℕ)} :=
      { default := ⟨⟨X.p0, by omega⟩, le_refl _⟩
        uniq := fun a => Subtype.ext (Fin.ext (by have := a.2; have := a.1.2; simp only; omega)) }
    exact re_det_one_sub_le_of_unique' _

end GlobalTheory.IntBall
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetOneSubOffDiagonalBlockGramLeOneBallStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detOneSubOffDiagonalBlockGram_le_one_ball : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (X.p0 = 1 ∨ X.p0 + 1 = r) → ∀ z : V (nd X), z ∈ Om X → ∀ τ : X.Ψ, zDet X z τ ≤ 1 := by
  first | exact @GlobalTheory.IntBall.zDet_le_one | exact GlobalTheory.IntBall.zDet_le_one | (intros; apply GlobalTheory.IntBall.zDet_le_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBallLeadingGramMinorLowerBoundLast
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBallLeadingGramMinorLowerBoundLast
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall.MinorLast

open Matrix
open scoped ComplexOrder

theorem det_sub_bound {p m : ℕ} (N : Matrix (Fin p) (Fin m) ℂ) (q : Fin p → ℂ) :
    (1 - ∑ c, ‖q c‖ ^ 2) * ‖(Nᴴ * N).det‖ ≤
      ‖(Nᴴ * N - vecMulVec (star (q ᵥ* N)) (q ᵥ* N)).det‖ := by
  set A := Nᴴ * N with hAdef
  set u := q ᵥ* N with hu
  by_cases hA : A.det = 0
  · rw [hA]; simp
  have hU : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hsplit : A - vecMulVec (star u) u = A + replicateCol Unit (-star u) * replicateRow Unit u := by
    ext i j
    simp [vecMulVec, replicateCol, replicateRow, Matrix.mul_apply, sub_eq_add_neg]
  have key : (A - vecMulVec (star u) u).det = A.det * (1 - u ⬝ᵥ A⁻¹ *ᵥ star u) := by
    rw [hsplit, Matrix.det_add_mul _ _ hU]
    congr 1
    rw [Matrix.det_unique]
    simp [Matrix.mul_apply, replicateRow, replicateCol, dotProduct, mulVec, sub_eq_add_neg,
      Finset.mul_sum]
    simp only [Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  set P := N * A⁻¹ * Nᴴ with hPdef
  have hs : u ⬝ᵥ A⁻¹ *ᵥ star u = q ⬝ᵥ P *ᵥ star q := by
    rw [hu, Matrix.star_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
  have hAh : Aᴴ = A := by rw [hAdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hPh : Pᴴ = P := by
    rw [hPdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_nonsing_inv, hAh, Matrix.mul_assoc]
  have hPP : P * P = P := by
    have h1 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hU
    calc P * P = N * (A⁻¹ * (Nᴴ * N) * A⁻¹) * Nᴴ := by simp only [hPdef, Matrix.mul_assoc]
      _ = P := by rw [← hAdef, h1, Matrix.one_mul, hPdef, Matrix.mul_assoc]
  have hQ : (1 - P) = (1 - P)ᴴ * (1 - P) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPh, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, hPP]
    simp
  have hpsd : (1 - P).PosSemidef := by rw [hQ]; exact Matrix.posSemidef_conjTranspose_mul_self _
  have ht := hpsd.dotProduct_mulVec_nonneg (star q)
  rw [star_star, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub] at ht
  have hqq : q ⬝ᵥ star q = ((∑ c, ‖q c‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.ofReal_sum,
      Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have ha := (Matrix.posSemidef_conjTranspose_mul_self N).det_nonneg
  rw [← hAdef] at ha
  rw [key, hs]
  set a := A.det
  set t := q ⬝ᵥ star q - q ⬝ᵥ P *ᵥ star q with htdef
  have hsq : q ⬝ᵥ P *ᵥ star q = ((∑ c, ‖q c‖ ^ 2 : ℝ) : ℂ) - t := by rw [htdef, hqq]; ring
  rw [hsq]
  obtain ⟨ha1, ha2⟩ := Complex.nonneg_iff.1 ha
  obtain ⟨ht1, ht2⟩ := Complex.nonneg_iff.1 ht
  have hae : a = (a.re : ℂ) := Complex.ext rfl (by simp [← ha2])
  have hte : t = (t.re : ℂ) := Complex.ext rfl (by simp [← ht2])
  rw [hae, hte, Complex.norm_real, Real.norm_of_nonneg ha1]
  rw [show (a.re : ℂ) * (1 - (((∑ c, ‖q c‖ ^ 2 : ℝ) : ℂ) - (t.re : ℂ))) = ((a.re * (1 - ∑ c, ‖q c‖ ^ 2 + t.re) : ℝ) : ℂ) by push_cast; ring]
  rw [Complex.norm_real]
  calc (1 - ∑ c, ‖q c‖ ^ 2) * a.re ≤ a.re * (1 - ∑ c, ‖q c‖ ^ 2 + t.re) := by nlinarith
    _ ≤ _ := Real.le_norm_self _

end GlobalTheory.IntBall.MinorLast

namespace GlobalTheory.IntBall.MinorLast

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem gram_eq_mul {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gram_mul {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x y : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G (x * y) = yᵀ * ReciprocityTheory.ChartRestriction.G.FD.gram τ G x * y.map (starRingEnd ℂ) := by
  rw [gram_eq_mul, gram_eq_mul, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem entry_tdm {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (d : Fin r → ℂ) (i j : Fin r) :
    (Mᵀ * Matrix.diagonal d * M.map (starRingEnd ℂ)) i j = ∑ l, M l i * d l * starRingEnd ℂ (M l j) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply]

variable {p : ℕ} (X : Data E (p + 1))

theorem nmat_eq (z : V (nd X)) (τ : X.Ψ) (a b : Fin (p + 1)) :
    nmat X z τ a b = lowMat (zOf X z τ) a b := rfl

theorem n_top (hp : X.p0 = p) (z : V (nd X)) (τ : X.Ψ) (i a : Fin p) :
    mat (nFrame X z) τ i.castSucc a.castSucc = lowMat (zOf X z τ) i.castSucc a.castSucc := by
  show (∑ c, zFrame X z τ i.castSucc c * leviFrame X z τ c a.castSucc) = _
  rw [Fin.sum_univ_castSucc]
  have hl : zFrame X z τ i.castSucc (Fin.last p) = 0 := by
    simp [zFrame, hp, Fin.ext_iff]; omega
  rw [hl, zero_mul, add_zero]
  rw [Finset.sum_eq_single i]
  · simp [zFrame, leviFrame, hp, nmat_eq]
    rw [if_neg (by omega), if_neg (by omega)]
  · intro b _ hb
    have : i.castSucc ≠ b.castSucc := fun h => hb (Fin.castSucc_injective _ h).symm
    simp [zFrame, hp, this]
  · simp

theorem n_last (hp : X.p0 = p) (z : V (nd X)) (τ : X.Ψ) (a : Fin p) :
    mat (nFrame X z) τ (Fin.last p) a.castSucc =
      ∑ c : Fin p, lowMat (zOf X z τ) (Fin.last p) c.castSucc * lowMat (zOf X z τ) c.castSucc a.castSucc := by
  show (∑ c, zFrame X z τ (Fin.last p) c * leviFrame X z τ c a.castSucc) = _
  simp [zFrame, leviFrame, hp, nmat_eq, Fin.sum_univ_castSucc]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [if_neg (by omega)]

end GlobalTheory.IntBall.MinorLast

namespace GlobalTheory.IntBall.MinorLast

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {p : ℕ}

theorem finiteRing_sq_sub_mul_sq_eq_of_card (X : Data E (p + 1)) (hp : X.p0 = p) (x0 : Base X) (z : V (nd X)) (τ : X.Ψ)
    (k : Fin p) :
    zDet X z τ * colGram (blkW X.p0 (zOf X z τ)) k.succ ≤
      ‖dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩‖ := by
  set w := zOf X z τ with hw
  let N : Matrix (Fin p) (Fin ((k : ℕ) + 1)) ℂ := fun i a => lowMat w i.castSucc (Fin.castSucc ⟨a, by omega⟩)
  let q : Fin p → ℂ := fun c => lowMat w (Fin.last p) c.castSucc
  have hA : colGram (blkW X.p0 w) k.succ = ‖(Nᴴ * N).det‖ := by
    have hB : blkW X.p0 w = fun (i j : Fin (p + 1 - 1)) => lowMat w ⟨i, by omega⟩ ⟨j, by omega⟩ := by
      funext i j
      unfold blkW
      split_ifs with h
      · have hi : (i : ℕ) = 0 := by omega
        have hj : (j : ℕ) = 0 := by omega
        simp [lowMat, hi, hj, Fin.ext_iff]
      · rfl
    rw [hB]
    rfl
  have hZ : zDet X z τ = 1 - ∑ c, ‖q c‖ ^ 2 := by
    unfold zDet
    rw [Matrix.det_one_sub_mul_comm]
    letI hU : Unique {a : Fin (p + 1) // X.p0 ≤ (a : ℕ)} :=
      { default := ⟨Fin.last p, by simp [hp]⟩
        uniq := fun a => Subtype.ext (Fin.ext (by have := a.2; have := a.1.2; simp; omega)) }
    rw [Matrix.det_unique]
    let e : Fin p ≃ {b : Fin (p + 1) // (b : ℕ) < X.p0} :=
      { toFun := fun c => ⟨c.castSucc, by simp [hp]⟩
        invFun := fun b => ⟨b.1, by have := b.2; omega⟩
        left_inv := fun c => rfl
        right_inv := fun b => rfl }
    have hs : ∑ b : {b : Fin (p + 1) // (b : ℕ) < X.p0},
        zBlock X z τ default b * star (zBlock X z τ default b) = ((∑ c, ‖q c‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Fintype.sum_equiv e (fun c => zBlock X z τ default (e c) * star (zBlock X z τ default (e c)))
        _ (fun _ => rfl)]
      push_cast
      refine Finset.sum_congr rfl fun c _ => ?_
      change q c * star (q c) = _
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; rfl
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [hs]
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
  have hD : dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩ =
      (Nᴴ * N - Matrix.vecMulVec (star (q ᵥ* N)) (q ᵥ* N)).det := by
    have hg : ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (mat (point X x0 z) τ) =
        (mat (nFrame X z) τ)ᵀ * Matrix.diagonal (fun a : Fin (p + 1) => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) *
          (mat (nFrame X z) τ).map (starRingEnd ℂ) := by
      rw [show mat (point X x0 z) τ = mat x0.1 τ * mat (nFrame X z) τ from rfl, gram_mul, x0.2 τ]
    unfold dmin lminor
    rw [hg, ← Matrix.det_transpose (Nᴴ * N - _)]
    congr 1
    ext a b
    have hc : ∀ a : Fin ((k : ℕ) + 1), (Fin.castLE (by omega) a : Fin (p + 1)) =
        Fin.castSucc (⟨a, by omega⟩ : Fin p) := fun a => Fin.ext rfl
    rw [Matrix.submatrix_apply, hc, hc, entry_tdm, Fin.sum_univ_castSucc]
    simp only [n_top X hp, n_last X hp, Fin.val_castSucc, Fin.val_last, sgn, hp, Fin.is_lt, if_true,
      lt_irrefl, if_false, Matrix.transpose_apply, Matrix.sub_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct, Pi.star_apply, N, q, ← hw]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.ofReal_one, Complex.ofReal_neg,
      mul_one, Complex.star_def]
    rw [sub_eq_add_neg]
    congr 1
    · exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    · ring
  rw [hA, hZ, hD]
  exact det_sub_bound N q

end GlobalTheory.IntBall.MinorLast

namespace GlobalTheory.IntBall.MinorLast

theorem zDet_mul_colGram_le_dmin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), X.p0 + 1 = r → ∀ (x0 : Base X) (z : V (nd X)), z ∈ Om X → ∀ (τ : X.Ψ) (k : Fin (r - 1)), zDet X z τ * colGram (blkW X.p0 (zOf X z τ)) k.succ ≤ ‖dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩‖ := by
  intro E _ _ _ r X hr x0 z _ τ k
  obtain ⟨p, rfl⟩ : ∃ p, r = p + 1 := ⟨X.p0, hr.symm⟩
  exact finiteRing_sq_sub_mul_sq_eq_of_card X (by omega) x0 z τ k

end GlobalTheory.IntBall.MinorLast
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBallLeadingGramMinorLowerBoundLastStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitBall_leadingGramMinor_lower_bound_last : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), X.p0 + 1 = r → ∀ (x0 : Base X) (z : V (nd X)), z ∈ Om X → ∀ (τ : X.Ψ) (k : Fin (r - 1)), zDet X z τ * colGram (blkW X.p0 (zOf X z τ)) k.succ ≤ ‖dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩‖ := by
  first | exact @GlobalTheory.IntBall.MinorLast.zDet_mul_colGram_le_dmin | exact GlobalTheory.IntBall.MinorLast.zDet_mul_colGram_le_dmin | (intros; apply GlobalTheory.IntBall.MinorLast.zDet_mul_colGram_le_dmin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRealGramDeterminantBoundLeProdCutoff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRealGramDeterminantBoundLeProdCutoff
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall.Cutoff

noncomputable section

theorem norm_entry_le_opNorm {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (Z : Matrix m n ℂ) (a : m) (b : n) :
    ‖Z a b‖ ≤ ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Z)‖ := by
  set v : EuclideanSpace ℂ n := EuclideanSpace.single b (1 : ℂ)
  have h1 := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Z)).le_opNorm v
  have hv : ‖v‖ = 1 := by simp [v]
  rw [hv, mul_one] at h1
  have h2 := PiLp.norm_apply_le (Matrix.toEuclideanLin Z v) a
  have h3 : (Matrix.toEuclideanLin Z v) a = Z a b := by
    simp [v, Matrix.toLpLin_apply, Matrix.mulVec_single]
  rw [h3] at h2
  exact h2.trans h1

theorem gB_nonneg {r : ℕ} (p0 : ℕ) (w : Low r → ℂ) : 0 ≤ gB p0 w :=
  Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem zOf_mem_cut (X : Data E r) {z : V (nd X)} (hz : z ∈ Om X) (τ : X.Ψ) :
    zOf X z τ ∈ {w : Low r → ℂ | ∀ p : Low r, (p.1.2 : ℕ) < X.p0 → X.p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1} := by
  intro p hb ha
  have he : zOf X z τ p = zBlock X z τ ⟨p.1.1, ha⟩ ⟨p.1.2, hb⟩ := by
    simp [zBlock, nmat, zOf, p.2]
  rw [he]
  exact ((norm_entry_le_opNorm _ _ _).trans (hz τ).le)

theorem ofReal_bnd_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (z : V (nd X)), z ∈ Om X → ENNReal.ofReal (bnd X z) ≤ ∏ τ, hB X.p0 (zOf X z τ) := by
  intro E _ _ _ r X z hz
  rw [bnd, ENNReal.ofReal_prod_of_nonneg (fun τ _ => gB_nonneg _ _)]
  refine le_of_eq (Finset.prod_congr rfl fun τ _ => ?_)
  rw [hB, Set.indicator_of_mem (zOf_mem_cut X hz τ)]

end

end GlobalTheory.IntBall.Cutoff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRealGramDeterminantBoundLeProdCutoffStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ofReal_gramDeterminantBound_le_prod_cutoff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (z : V (nd X)), z ∈ Om X → ENNReal.ofReal (bnd X z) ≤ ∏ τ, hB X.p0 (zOf X z τ) := by
  first | exact @GlobalTheory.IntBall.Cutoff.ofReal_bnd_le | exact GlobalTheory.IntBall.Cutoff.ofReal_bnd_le | (intros; apply GlobalTheory.IntBall.Cutoff.ofReal_bnd_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralCutoffGramBoundMixedBlockTwoLtTop
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralCutoffGramBoundMixedBlockTwoLtTop
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall

theorem lintegral_hB_one_two_lt_top : ∫⁻ w : Low 2 → ℂ, hB 1 w < ⊤ := by
  have hg : ∀ w : Low 2 → ℂ, gB 1 w = 1 := by
    intro w
    simp [gB, colGram, lminor]
  have hset : {w : Low 2 → ℂ | ∀ p : Low 2, (p.1.2 : ℕ) < 1 → 1 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1}
      = Metric.closedBall (0 : Low 2 → ℂ) 1 := by
    ext w
    simp only [Set.mem_setOf_eq, mem_closedBall_zero_iff]
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    constructor
    · intro h p
      have hp := p.2
      have h1 : (p.1.2 : ℕ) < p.1.1 := hp
      have h2 : (p.1.1 : ℕ) < 2 := p.1.1.isLt
      exact h p (by omega) (by omega)
    · intro h p _ _
      exact h p
  have hfun : hB 1 = Set.indicator (Metric.closedBall (0 : Low 2 → ℂ) 1) (fun _ => (1 : ℝ≥0∞)) := by
    funext w
    simp only [hB, hset, hg, ENNReal.ofReal_one]
  rw [hfun, lintegral_indicator Metric.isClosed_closedBall.measurableSet]
  simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, one_mul]
  exact measure_closedBall_lt_top

end GlobalTheory.IntBall
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralCutoffGramBoundMixedBlockTwoLtTopStatement
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_cutoffGramBoundMixedBlock_two_lt_top : ∫⁻ w : Low 2 → ℂ, hB 1 w < ⊤ := by
  first | exact @GlobalTheory.IntBall.lintegral_hB_one_two_lt_top | exact GlobalTheory.IntBall.lintegral_hB_one_two_lt_top | (intros; apply GlobalTheory.IntBall.lintegral_hB_one_two_lt_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnGramDeterminantUnitLowerBlockLastEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnGramDeterminantUnitLowerBlockLastEqOne
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall

theorem blkW_det_eq_one (r p0 : ℕ) (w : Low r → ℂ) : (blkW p0 w).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_eq_one
    intro i _
    simp [blkW, lowMat]
  · intro i j hij
    have hij' : (i : ℕ) < j := hij
    simp only [blkW, lowMat]
    split_ifs with h1 h2 h3 h4 h5 h6
    all_goals first
      | rfl
      | (exfalso; simp only [Fin.lt_def, Fin.ext_iff] at *; omega)

theorem colGram_blkW_last (r p0 : ℕ) (w : Low r → ℂ) :
    colGram (blkW p0 w) (Fin.last (r - 1)) = 1 := by
  unfold colGram lminor
  have : (Fin.castLE (Nat.le_of_lt_succ (Fin.last (r - 1)).isLt) : Fin (r - 1) → Fin (r - 1)) = id := by
    funext i; ext; simp
  rw [this, Matrix.submatrix_id_id, Matrix.det_mul, Matrix.det_conjTranspose, blkW_det_eq_one]
  simp

theorem colGramLast : ∀ (r p0 : ℕ) (w : Low r → ℂ), colGram (blkW p0 w) (Fin.last (r - 1)) = 1 :=
  colGram_blkW_last

end GlobalTheory.IntBall
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnGramDeterminantUnitLowerBlockLastEqOneStatement
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnGramDeterminant_unitLowerBlock_last_eq_one : ∀ (r p0 : ℕ) (w : Low r → ℂ), colGram (blkW p0 w) (Fin.last (r - 1)) = 1 := by
  first | exact @GlobalTheory.IntBall.colGramLast | exact GlobalTheory.IntBall.colGramLast | (intros; apply GlobalTheory.IntBall.colGramLast <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnGramDeterminantDiagonalBlockUnitLowerPos
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnGramDeterminantDiagonalBlockUnitLowerPos
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall.ColGramPos

open scoped ComplexOrder

theorem blkW_upper {r : ℕ} (p0 : ℕ) (w : Low r → ℂ) (i j : Fin (r - 1)) (h : i < j) :
    blkW p0 w i j = 0 := by
  have h' : (i : ℕ) < j := h
  unfold blkW
  split_ifs
  · unfold lowMat
    rw [dite_eq_right (by rw [Fin.lt_def]; simp only; omega), if_neg (by rw [Fin.ext_iff]; simp only; omega)]
  · unfold lowMat
    rw [dite_eq_right (by rw [Fin.lt_def]; simp only; omega), if_neg (by rw [Fin.ext_iff]; simp only; omega)]

theorem blkW_diag {r : ℕ} (p0 : ℕ) (w : Low r → ℂ) (i : Fin (r - 1)) :
    blkW p0 w i i = 1 := by
  unfold blkW
  split_ifs
  · unfold lowMat
    rw [dite_eq_right (lt_irrefl _), if_pos rfl]
  · unfold lowMat
    rw [dite_eq_right (lt_irrefl _), if_pos rfl]

theorem lowerTri_det_one {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hu : ∀ i j, i < j → T i j = 0) (hd : ∀ i, T i i = 1) : T.det = 1 := by
  rw [Matrix.det_of_lowerTriangular T (fun i j hij => hu i j hij)]
  simp [hd]

theorem colGram_blkW_pos : ∀ (r p0 : ℕ) (w : Low r → ℂ) (k : Fin (r - 1 + 1)), 0 < colGram (blkW p0 w) k := by
  intro r p0 w k
  set B := blkW p0 w with hB
  have hk : (k : ℕ) ≤ r - 1 := Nat.le_of_lt_succ k.isLt
  set N : Matrix (Fin (r - 1)) (Fin k) ℂ := B.submatrix id (Fin.castLE hk) with hN
  have hsub : (Bᴴ * B).submatrix (Fin.castLE hk) (Fin.castLE hk) = Nᴴ * N := by
    ext a b
    simp [N, Matrix.mul_apply, Matrix.conjTranspose_apply]
  set T : Matrix (Fin k) (Fin k) ℂ := B.submatrix (Fin.castLE hk) (Fin.castLE hk) with hT
  have hTdet : T.det = 1 := by
    apply lowerTri_det_one
    · intro i j hij
      exact blkW_upper p0 w _ _ (by rw [Fin.lt_def] at hij ⊢; simpa using hij)
    · intro i
      exact blkW_diag p0 w _
  have hinj : Function.Injective N.mulVec := by
    intro u v huv
    have h0 : N *ᵥ (u - v) = 0 := by rw [Matrix.mulVec_sub, huv, sub_self]
    have hT0 : T *ᵥ (u - v) = 0 := by
      ext i
      have := congrFun h0 (Fin.castLE hk i)
      simpa [T, N, Matrix.mulVec, dotProduct] using this
    have := Matrix.eq_zero_of_mulVec_eq_zero (by rw [hTdet]; exact one_ne_zero) hT0
    exact sub_eq_zero.mp this
  have hpd : (Nᴴ * N).PosDef := Matrix.PosDef.conjTranspose_mul_self N hinj
  have hdet : (Nᴴ * N).det ≠ 0 := hpd.det_pos.ne'
  unfold colGram lminor
  rw [hsub]
  exact norm_pos_iff.mpr hdet

end GlobalTheory.IntBall.ColGramPos
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnGramDeterminantDiagonalBlockUnitLowerPosStatement
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnGramDeterminant_diagonalBlockUnitLower_pos : ∀ (r p0 : ℕ) (w : Low r → ℂ) (k : Fin (r - 1 + 1)), 0 < colGram (blkW p0 w) k := by
  first | exact @GlobalTheory.IntBall.ColGramPos.colGram_blkW_pos | exact GlobalTheory.IntBall.ColGramPos.colGram_blkW_pos | (intros; apply GlobalTheory.IntBall.ColGramPos.colGram_blkW_pos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableCutoffGramBoundMixedBlock
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableCutoffGramBoundMixedBlock
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall

theorem measurable_hB : ∀ (r p0 : ℕ), Measurable (hB (r := r) p0) := by
  intro r p0
  have hlow : Continuous (fun w : Low r → ℂ => lowMat w) := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [lowMat]
    split_ifs <;> first | exact continuous_apply _ | exact continuous_const
  have hblk : Continuous (fun w : Low r → ℂ => blkW p0 w) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have hent : ∀ a b : Fin r, Continuous (fun w : Low r → ℂ => lowMat w a b) := fun a b =>
      (continuous_apply b).comp ((continuous_apply a).comp hlow)
    by_cases h : p0 = 1
    · simp only [blkW, h, if_true]
      exact hent _ _
    · simp only [blkW, h, if_false]
      exact hent _ _
  have hcg : ∀ k, Continuous (fun w : Low r → ℂ => colGram (blkW p0 w) k) := by
    intro k
    simp only [colGram, lminor]
    exact (((hblk.matrix_conjTranspose.matrix_mul hblk).matrix_submatrix _ _).matrix_det).norm
  have hg : Measurable (fun w : Low r → ℂ => gB p0 w) := by
    have hz : ∀ x : ℝ, x ^ (-2 : ℤ) = (x ^ 2)⁻¹ := fun x => by
      rw [zpow_neg]; norm_cast
    simp only [gB, hz]
    refine Finset.measurable_prod _ fun k _ => ?_
    exact ((hcg k.castSucc).measurable.pow_const 2).inv
  have hS : IsClosed {w : Low r → ℂ | ∀ p : Low r, (p.1.2 : ℕ) < p0 → p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun p => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le (continuous_apply p).norm continuous_const
  unfold hB
  exact (ENNReal.measurable_ofReal.comp hg).indicator hS.measurableSet

end GlobalTheory.IntBall
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableCutoffGramBoundMixedBlockStatement
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_cutoffGramBoundMixedBlock : ∀ (r p0 : ℕ), Measurable (hB (r := r) p0) := by
  first | exact @GlobalTheory.IntBall.measurable_hB | exact GlobalTheory.IntBall.measurable_hB | (intros; apply GlobalTheory.IntBall.measurable_hB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformBoundLintegralFlagDomainBallCase
namespace GlobalTheory.IntBall

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
  GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames
open scoped ENNReal Matrix

theorem prod_inv_sq_mul_rpow_le {q : ℕ} {t s : ℝ} (d g : Fin q → ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hs : 2 * (q : ℝ) ≤ s) (hg : ∀ k, 0 < g k) (hdg : ∀ k, t * g k ≤ d k) :
    (∏ k, (d k ^ 2)⁻¹) * t ^ s ≤ ∏ k, g k ^ (-2 : ℤ) := by
  have h1 : ∏ k, (d k ^ 2)⁻¹ ≤ ∏ k, (t ^ 2)⁻¹ * (g k ^ 2)⁻¹ := by
    refine Finset.prod_le_prod₀ (fun k _ => by positivity) fun k _ => ?_
    rw [← mul_inv, ← mul_pow]
    exact inv_anti₀ (by have := hg k; positivity) (pow_le_pow_left₀ (by have := hg k; positivity) (hdg k) 2)
  have h2 : t ^ s ≤ t ^ (2 * (q : ℝ)) := Real.rpow_le_rpow_of_exponent_ge ht ht1 hs
  have h3 : t ^ (2 * (q : ℝ)) = (t ^ 2) ^ q := by
    rw [Real.rpow_mul ht.le, Real.rpow_two, Real.rpow_natCast]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  calc (∏ k, (d k ^ 2)⁻¹) * t ^ s ≤ ((t ^ 2)⁻¹ ^ q * ∏ k, (g k ^ 2)⁻¹) * (t ^ 2) ^ q := by
        refine mul_le_mul h1 (h2.trans h3.le) (by positivity) (by positivity)
    _ = ∏ k, g k ^ (-2 : ℤ) := by
        rw [mul_comm, ← mul_assoc, inv_pow, mul_inv_cancel₀ (by positivity), one_mul]
        exact Finset.prod_congr rfl fun k _ => by rw [zpow_neg, zpow_ofNat]

theorem prod_fin_split {r : ℕ} (hr : 1 ≤ r) (f : Fin r → ℝ) :
    ∏ i, f i = f ⟨0, by omega⟩ * ∏ k : Fin (r - 1), f ⟨k + 1, by omega⟩ := by
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
  rw [Fin.prod_univ_succ]
  rfl

theorem colGram_zero {q : ℕ} (M : Matrix (Fin q) (Fin q) ℂ) : colGram M 0 = 1 := by
  simp [colGram, lminor, Matrix.det_isEmpty]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem norm_dmin_zero (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (h : 0 < r + 1) :
    ‖dmin X.Gm x τ ⟨0, h⟩‖ = 1 := by
  simp [dmin, lminor, Matrix.det_isEmpty]

theorem ball_cases {X : Data E r} (h1 : 0 < X.p0) (h2 : X.p0 < r) (h3 : X.p0 * (r - X.p0) ≤ 3) :
    X.p0 = 1 ∨ X.p0 + 1 = r := by
  by_contra hc
  push_neg at hc
  have ha : 2 ≤ X.p0 := by omega
  have hb : 2 ≤ r - X.p0 := by omega
  have := Nat.mul_le_mul ha hb
  omega

theorem exp_neg_rho {X : Data E r} {z : V (nd X)} (hz : z ∈ Om X) (s : ℝ) :
    Real.exp (-(s * rho X z)) = ∏ τ, zDet X z τ ^ s := by
  have e : -(s * rho X z) = ∑ τ, Real.log (zDet X z τ) * s := by
    simp only [rho, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun τ _ => by ring
  rw [e, Real.exp_sum]
  exact Finset.prod_congr rfl fun τ _ => (Real.rpow_def_of_pos (zDet_pos X hz τ) s).symm

theorem density_mul_exp_le (X : Data E r) (h1 : 0 < X.p0) (h2 : X.p0 < r) (h3 : X.p0 * (r - X.p0) ≤ 3)
    (x0 : Base X) {z : V (nd X)} (hz : z ∈ Om X) {s : ℝ} (hs : 2 * ((r : ℝ) - 1) ≤ s) :
    density X x0 z * Real.exp (-(s * rho X z)) ≤ bnd X z := by
  have hcase := ball_cases h1 h2 h3
  have hq : 2 * ((r - 1 : ℕ) : ℝ) ≤ s := by
    rw [Nat.cast_sub (by omega)]
    simpa using hs
  have hle : ∀ τ, zDet X z τ ≤ 1 := GlobalTheory.T.detOneSubOffDiagonalBlockGram_le_one_ball E r X hcase z hz
  unfold density bnd
  rw [exp_neg_rho hz, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun τ _ => mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity)
    (Real.rpow_nonneg (zDet_pos X hz τ).le s)) fun τ _ => ?_
  rw [prod_fin_split (by omega)]
  simp only [Fin.castSucc_mk]
  rw [show (‖dmin X.Gm (point X x0 z) τ ⟨0, by omega⟩‖ ^ 2)⁻¹ = 1 by
    rw [norm_dmin_zero]; norm_num, one_mul]
  rcases hcase with hp | hp
  · exact prod_inv_sq_mul_rpow_le (fun k : Fin (r - 1) => ‖dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩‖)
      (fun k => colGram (blkW X.p0 (zOf X z τ)) k.castSucc) (zDet_pos X hz τ) (hle τ) hq
      (fun k => GlobalTheory.T.columnGramDeterminant_diagonalBlockUnitLower_pos r X.p0 _ _) (fun k => GlobalTheory.T.unitBall_leadingGramMinor_lower_bound_first E r X hp x0 z hz τ k)
  · have := prod_inv_sq_mul_rpow_le (fun k : Fin (r - 1) => ‖dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩‖)
      (fun k => colGram (blkW X.p0 (zOf X z τ)) k.succ) (zDet_pos X hz τ) (hle τ) hq
      (fun k => GlobalTheory.T.columnGramDeterminant_diagonalBlockUnitLower_pos r X.p0 _ _) (fun k => GlobalTheory.T.unitBall_leadingGramMinor_lower_bound_last E r X hp x0 z hz τ k)
    refine this.trans_eq ?_
    have e1 := Fin.prod_univ_succ fun j : Fin (r - 1 + 1) => colGram (blkW X.p0 (zOf X z τ)) j ^ (-2 : ℤ)
    have e2 := Fin.prod_univ_castSucc fun j : Fin (r - 1 + 1) => colGram (blkW X.p0 (zOf X z τ)) j ^ (-2 : ℤ)
    rw [colGram_zero, one_zpow, one_mul] at e1
    rw [GlobalTheory.T.columnGramDeterminant_unitLowerBlock_last_eq_one r X.p0 (zOf X z τ), one_zpow, mul_one] at e2
    rw [← e1, e2]
    rfl

theorem block_fin {p0 : ℕ} (h1 : 0 < p0) (h2 : p0 < r) (h3 : p0 * (r - p0) ≤ 3) :
    ∫⁻ w : Low r → ℂ, hB p0 w < ⊤ := by
  obtain ⟨k, rfl⟩ : ∃ k, r = p0 + k + 1 := ⟨r - p0 - 1, by omega⟩
  have h3' : p0 * (k + 1) ≤ 3 := by simpa [show p0 + k + 1 - p0 = k + 1 by omega] using h3
  have hr : p0 + k ≤ 3 := by nlinarith
  have hp : p0 ≤ 3 := by omega
  have hk : k ≤ 2 := by omega
  interval_cases p0 <;> interval_cases k <;> first
    | omega
    | exact GlobalTheory.T.lintegral_cutoffGramBoundMixedBlock_two_lt_top
    | exact GlobalTheory.T.lintegral_cutoffGramBoundMixedBlock_rankThree_lt_top _ (by decide)
    | exact GlobalTheory.T.lintegral_cutoffGramBoundMixedBlock_rankFour_lt_top _ (by decide)

theorem lintegral_lt_top (X : Data E r) (x0 : Base X) (h1 : 0 < X.p0) (h2 : X.p0 < r)
    (h3 : X.p0 * (r - X.p0) ≤ 3) {s : ℝ} (hs : 2 * ((r : ℝ) - 1) ≤ s) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (-(s * rhF X x0.1 z))) ∂muF X x0.1 < ⊤ := by
  have hm : Measurable fun z : V (nd X) => ∏ τ, hB X.p0 (zOf X z τ) := by
    refine Finset.measurable_prod _ fun τ _ => (GlobalTheory.T.measurable_cutoffGramBoundMixedBlock r X.p0).comp ?_
    exact Measurable.of_eval fun p => (EuclideanSpace.proj (𝕜 := ℂ) _).continuous.measurable
  rw [GlobalTheory.T.lintegral_expRho_eq_setLIntegral_unitBallDomain E r X x0 s]
  calc ∫⁻ z in Om X, ENNReal.ofReal (density X x0 z) * ENNReal.ofReal (Real.exp (-(s * rho X z)))
      ≤ ∫⁻ z in Om X, ∏ τ, hB X.p0 (zOf X z τ) := by
        refine setLIntegral_mono hm fun z hz => ?_
        rw [← ENNReal.ofReal_mul (by unfold density; positivity)]
        exact (ENNReal.ofReal_le_ofReal (density_mul_exp_le X h1 h2 h3 x0 hz hs)).trans
          (GlobalTheory.T.ofReal_gramDeterminantBound_le_prod_cutoff E r X z hz)
    _ ≤ ∫⁻ z, ∏ τ, hB X.p0 (zOf X z τ) := setLIntegral_le_lintegral _ _
    _ = ∏ _τ : X.Ψ, ∫⁻ w, hB X.p0 w := GlobalTheory.T.lintegral_prod_chartCoordinates_eq_prod E r X _ (GlobalTheory.T.measurable_cutoffGramBoundMixedBlock r X.p0)
    _ < ⊤ := ENNReal.prod_lt_top fun _ _ => block_fin h1 h2 h3

theorem intBall : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), 0 < X.p0 →
    X.p0 < r → X.p0 * (r - X.p0) ≤ 3 → ∀ s : ℝ, 2 * ((r : ℝ) - 1) ≤ s → ∃ I : ℝ≥0∞, I < ⊤ ∧
      ∀ x1 : Frame X.Ψ r, IsOrth X x1 →
        ∫⁻ z, ENNReal.ofReal (Real.exp (-(s * rhF X x1 z))) ∂muF X x1 ≤ I := by
  intro E _ _ _ r X h1 h2 h3 s hs
  have h0 : IsOrth X (x0F X) := GlobalTheory.OrthNear.isOrth_x0F X
  refine ⟨_, lintegral_lt_top X ⟨x0F X, h0⟩ h1 h2 h3 hs, fun x1 hx1 => ?_⟩
  rw [GlobalTheory.Up.PoleValue.rhF_eq h0 hx1, GlobalTheory.Up.PoleValue.muF_eq h0 hx1]

end GlobalTheory.IntBall
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformBoundLintegralFlagDomainBallCaseStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniform_bound_lintegral_flagDomain_ball_case : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), 0 < X.p0 → X.p0 < r → X.p0 * (r - X.p0) ≤ 3 → ∀ s : ℝ, 2 * ((r : ℝ) - 1) ≤ s → ∃ I : ℝ≥0∞, I < ⊤ ∧ ∀ x1 : Frame X.Ψ r, IsOrth X x1 → ∫⁻ z, ENNReal.ofReal (Real.exp (-(s * rhF X x1 z))) ∂muF X x1 ≤ I := by
  first | exact @GlobalTheory.IntBall.intBall | exact GlobalTheory.IntBall.intBall | (intros; apply GlobalTheory.IntBall.intBall <;> assumption)
end
