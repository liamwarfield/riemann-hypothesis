module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushM
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvT
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarUnitaryGroupWbDensityChart
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstGVolMt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGroupGaugeVolumeInHermitianUnitary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerTubeGaugeMassAsymptotic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserUnitaryGroupHasGaugeMeasure
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserUnitaryGroupHasGaugeMeasure
noncomputable section

namespace GlobalTheory.GaugeKExists

theorem gaugeK : PI.RhsWLim.W.GaugeK := by
  intro k r _
  exact ⟨Formalism.L2.SG.Pf.GV.nu0 k r, Formalism.L2.SG.Pf.GV.gauge_measure_is_gauge⟩

end GlobalTheory.GaugeKExists
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserUnitaryGroupHasGaugeMeasureStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabiliser_unitaryGroup_has_gaugeMeasure : PI.RhsWLim.W.GaugeK := by
  first | exact @GlobalTheory.GaugeKExists.gaugeK | exact GlobalTheory.GaugeKExists.gaugeK | (intros; apply GlobalTheory.GaugeKExists.gaugeK <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidInvariantMeasurePolarForm
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidInvariantMeasurePolarForm
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace GlobalTheory.HyperboloidPolar

open PI.RhsWLim PI.RhsWLim.W

variable {k r : ℕ}

theorem opVec_inWb (p : (Fin k → ℂ) × ℂ) : inWb k r (opVec k r p) := by
  intro i hi
  unfold opVec
  rw [dif_neg (by omega), if_neg (by omega)]

theorem wbPart_opVec (p : (Fin k → ℂ) × ℂ) : wbPart k r (opVec k r p) = toW k p := by
  funext m
  have := m.isLt
  unfold wbPart opVec toW wI
  by_cases h : m.val < k
  · rw [dif_pos (by simp only; omega), dif_pos h]
    exact congrArg p.1 (Fin.ext (by simp))
  · rw [dif_neg (by simp only; omega), dif_neg h, if_pos (by simp only; omega)]

theorem opCo_eq (v : Fin (2 * r + k + 1) → ℂ) : opCo k r v = ofW k (wbPart k r v) := rfl

theorem opCo_opVec (p : (Fin k → ℂ) × ℂ) : opCo k r (opVec k r p) = p := by
  rw [opCo_eq, wbPart_opVec, ofW_toW]

theorem eq_of_wbPart {v w : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (hw : inWb k r w)
    (h : wbPart k r v = wbPart k r w) : v = w := by
  funext i
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [hv i hi, hw i hi]
  · have hm : MB.mid k r i := by constructor <;> omega
    have := congrFun h (MB.midx hm)
    simpa only [wbPart, MB.wI_midx] using this

theorem opVec_opCo {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) : opVec k r (opCo k r v) = v :=
  eq_of_wbPart (opVec_inWb _) hv (by rw [wbPart_opVec, opCo_eq, toW_ofW])

theorem inWb_uwb {s : Mat k r} (hs : s ∈ UWb k r) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    inWb k r (s *ᵥ v) := by
  rw [op_uwb_eq_emb hs]
  exact RI.inWb_emb _ hv

theorem continuous_opVec : Continuous (opVec k r) := by
  refine continuous_pi fun i => ?_
  unfold opVec
  by_cases h : r ≤ i.val ∧ i.val < r + k
  · simp only [dif_pos h]
    exact (continuous_apply _).comp continuous_fst
  · simp only [dif_neg h]
    by_cases h' : i.val = r + k
    · simp only [if_pos h']
      exact continuous_snd
    · simp only [if_neg h']
      exact continuous_const

theorem continuous_opCo : Continuous (opCo k r) :=
  (continuous_pi fun i => continuous_apply (wI k r (Fin.castSucc i))).prodMk
    (continuous_apply (wI k r (Fin.last k)))

theorem herm_opVec (p : (Fin k → ℂ) × ℂ) :
    herm (Hpk k r) (opVec k r p) (opVec k r p) = (qf k p : ℂ) := by
  rw [herm_wb _ _ (opVec_inWb p), wbPart_opVec, qf_eq]
  rfl

theorem herm_self_eq {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    herm (Hpk k r) z z = ((-Tz k r z : ℝ) : ℂ) := by
  unfold Tz
  rw [neg_neg, herm_wb _ _ hz, hermHb_self, Complex.ofReal_re]

def hypAmb (k r : ℕ) (T' : ℝ) : Measure (Fin (2 * r + k + 1) → ℂ) := (hypM k T').map (opVec k r)

theorem hypAmb_sigmaFinite {T' : ℝ} (hT' : 0 < T') : SigmaFinite (hypAmb k r T') := by
  have : IsFiniteMeasureOnCompacts (hypAmb k r T') := by
    refine ⟨fun C hC => ?_⟩
    rw [hypAmb, Measure.map_apply continuous_opVec.measurable hC.measurableSet]
    refine lt_of_le_of_lt (measure_mono ?_) ((hypLF k T' hT').2 _ (hC.image continuous_opCo))
    intro p hp
    exact ⟨_, hp, opCo_opVec p⟩
  infer_instance

theorem hypAmb_inv (hk : 1 ≤ k) {T' : ℝ} (hT' : 0 < T') {s : Mat k r} (hs : s ∈ UWb k r) :
    (hypAmb k r T').map (fun v => s *ᵥ v) = hypAmb k r T' := by
  have hI := hypInv_of lebInvB (coneForm_of hypTh coneVol) k r T' hk hT' s hs
  have hm : Continuous (fun v : Fin (2 * r + k + 1) → ℂ => s *ᵥ v) :=
    continuous_const.matrix_mulVec continuous_id
  have hA : Continuous (opAct k r s) := continuous_opCo.comp (hm.comp continuous_opVec)
  have e : (fun v => s *ᵥ v) ∘ opVec k r = opVec k r ∘ opAct k r s := by
    funext p
    exact (opVec_opCo (inWb_uwb hs (opVec_inWb p))).symm
  rw [hypAmb, Measure.map_map hm.measurable continuous_opVec.measurable, e,
    ← Measure.map_map continuous_opVec.measurable hA.measurable, hI]

theorem hypAmb_conc {z' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') (hT' : 0 < Tz k r z') :
    hypAmb k r (Tz k r z') {v | ¬ (inWb k r v ∧ herm (Hpk k r) v v = herm (Hpk k r) z' z')} = 0 := by
  have hc : IsClosed {v : Fin (2 * r + k + 1) → ℂ |
      inWb k r v ∧ herm (Hpk k r) v v = herm (Hpk k r) z' z'} := by
    change IsClosed ({v : Fin (2 * r + k + 1) → ℂ | inWb k r v} ∩
      {v : Fin (2 * r + k + 1) → ℂ | herm (Hpk k r) v v = herm (Hpk k r) z' z'})
    apply IsClosed.inter
    · have : {v : Fin (2 * r + k + 1) → ℂ | inWb k r v} =
          ⋂ i : Fin (2 * r + k + 1), ⋂ _ : (i.val < r ∨ r + k < i.val), {v | v i = 0} := by
        ext v
        simp only [inWb, Set.mem_iInter]
        rfl
      show IsClosed {v : Fin (2 * r + k + 1) → ℂ | inWb k r v}
      rw [this]
      exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_eq (continuous_apply i) continuous_const
    · apply isClosed_eq
      · unfold herm
        exact continuous_id.star.dotProduct (continuous_const.matrix_mulVec continuous_id)
      · exact continuous_const
  have hm : MeasurableSet {v : Fin (2 * r + k + 1) → ℂ |
      ¬ (inWb k r v ∧ herm (Hpk k r) v v = herm (Hpk k r) z' z')} := hc.measurableSet.compl
  rw [hypAmb, Measure.map_apply continuous_opVec.measurable hm]
  refine measure_mono_null ?_ (hypLF k _ hT').1
  intro p hp hS
  apply hp
  refine ⟨opVec_inWb p, ?_⟩
  rw [herm_opVec, herm_self_eq hz', (hypS_iff _ p).1 hS]

theorem hypAmb_polar (hk : 1 ≤ k) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {T' : ℝ} (hT' : 0 < T') (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ v, g (herm (Hpk k r) v z) ∂hypAmb k r T' =
      ENNReal.ofReal (2 * Real.pi ^ k / (k - 1).factorial / (2 * Tz k r z ^ k)) *
        ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) T' ζ) * g ζ := by
  obtain ⟨p, hp, hpz⟩ := transW k r z hz hT
  set s := Real.sqrt (Tz k r z) with hs
  have hs0 : (s : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact (Real.sqrt_pos.2 hT).ne'
  set zs := ((s : ℂ) • wLast k r) with hzs
  have hgm : Measurable fun v => g (herm (Hpk k r) v zs) := hg.comp (RI.cont_herm zs).measurable
  have hm : Measurable (fun v : Fin (2 * r + k + 1) → ℂ => p⁻¹ *ᵥ v) :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have step1 : ∫⁻ v, g (herm (Hpk k r) v z) ∂hypAmb k r T' = ∫⁻ v, g (herm (Hpk k r) v zs) ∂hypAmb k r T' := by
    calc ∫⁻ v, g (herm (Hpk k r) v z) ∂hypAmb k r T'
        = ∫⁻ v, (fun y => g (herm (Hpk k r) y zs)) (p⁻¹ *ᵥ v) ∂hypAmb k r T' := by
          refine lintegral_congr fun v => ?_
          rw [← hpz, herm_mulVec_right hp.1]
      _ = ∫⁻ y, g (herm (Hpk k r) y zs) ∂((hypAmb k r T').map (fun v => p⁻¹ *ᵥ v)) :=
          (lintegral_map hgm hm).symm
      _ = _ := by rw [hypAmb_inv hk hT' (HU.uwb_inv hp)]
  set f : (Fin k → ℂ) × ℂ → ℝ≥0∞ := fun v => g (-((s : ℂ) * v.2)) with hf
  have hfm : Measurable f := hg.comp (continuous_const.mul continuous_snd).neg.measurable
  have step2 : ∫⁻ v, g (herm (Hpk k r) v zs) ∂hypAmb k r T' = hypMeas k T' f := by
    rw [hypMeas_eq k T' hfm, hypAmb, lintegral_map hgm continuous_opVec.measurable]
    refine lintegral_congr fun q => ?_
    have e : opVec k r q (wI k r (Fin.last k)) = q.2 := congrArg Prod.snd (opCo_opVec (r := r) q)
    rw [hzs, herm_wLast, e]
  set G : ℝ → ℂ → ℝ≥0∞ := fun _ c => g (-((s : ℂ) * c)) with hGdef
  have hGm : Measurable (Function.uncurry G) :=
    hg.comp (continuous_const.mul continuous_snd).neg.measurable
  have step3 := polarHyp k (Tz k r z) T' hk hT hT' G hGm
  rw [← hs] at step3
  have hcancel : ∀ ζ : ℂ, -((s : ℂ) * -(ζ / (s : ℂ))) = ζ := by
    intro ζ; field_simp
  have e3 : hypMeas k T' f =
      hypMeas k T' (fun v => G ‖(WithLp.equiv 2 (Fin k → ℂ)).symm v.1‖ v.2) := rfl
  rw [step1, step2, e3, step3]
  simp only [hGdef, hcancel]

theorem hypQ : RI.HypQ := by
  intro k r z z' hk hz hz' hT hT'
  refine ⟨hypAmb k r (Tz k r z'), hypAmb_sigmaFinite hT', fun s hs => hypAmb_inv hk hT' hs,
    hypAmb_conc hz' hT', ENNReal.ofReal (2 * Real.pi ^ k / (k - 1).factorial / (2 * Tz k r z ^ k)),
    ?_, ENNReal.ofReal_ne_top, fun g hg => hypAmb_polar hk hz hT hT' g hg⟩
  have := Real.pi_pos
  exact (ENNReal.ofReal_pos.2 (by positivity)).ne'

end GlobalTheory.HyperboloidPolar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidInvariantMeasurePolarFormStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperboloid_invariant_measure_polar_form : PI.RhsWLim.W.RI.HypQ := by
  first | exact @GlobalTheory.HyperboloidPolar.hypQ | exact GlobalTheory.HyperboloidPolar.hypQ | (intros; apply GlobalTheory.HyperboloidPolar.hypQ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidInvariantMeasureOrbitRepresentation
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidInvariantMeasureOrbitRepresentation
noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace GlobalTheory.HypOrbitUnique

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.HU PI.RhsWLim.W.MB

theorem fubini_identity {G X : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
    [MeasurableSpace X] (act : G → X → X) (hm : Measurable (Function.uncurry act))
    (hmul : ∀ g g' x, act (g * g') x = act g (act g' x)) (hone : ∀ x, act 1 x = x)
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (Q : Measure X) [SFinite Q] (hQ : ∀ g, Q.map (act g) = Q) (x₀ : X)
    (htr : ∀ᵐ x ∂Q, ∃ g, act g x₀ = x) {f h : X → ℝ≥0∞} (hf : Measurable f) (hh : Measurable h) :
    (∫⁻ g, f (act g x₀) ∂μ) * ∫⁻ x, h x ∂Q = (∫⁻ x, f x ∂Q) * ∫⁻ g, h (act g⁻¹ x₀) ∂μ := by
  have hmg : ∀ g, Measurable (act g) := fun g => hm.comp measurable_prodMk_left
  have hm1 : Measurable fun p : X × G => act p.2 p.1 := hm.comp measurable_swap
  have hm2 : Measurable fun p : G × X => act p.1⁻¹ p.2 :=
    hm.comp (measurable_fst.inv.prodMk measurable_snd)
  calc (∫⁻ g, f (act g x₀) ∂μ) * ∫⁻ x, h x ∂Q
      = ∫⁻ x, (∫⁻ g, f (act g x₀) ∂μ) * h x ∂Q := (lintegral_const_mul _ hh).symm
    _ = ∫⁻ x, ∫⁻ g, f (act g x) * h x ∂μ ∂Q := by
        refine lintegral_congr_ae (htr.mono ?_)
        rintro x ⟨p, rfl⟩
        have hmx : Measurable fun g => f (act g (act p x₀)) := hf.comp (hm.comp measurable_prodMk_right)
        simp only
        rw [lintegral_mul_const _ hmx]
        congr 1
        simp_rw [← hmul]
        exact (lintegral_mul_right_eq_self (fun g => f (act g x₀)) p).symm
    _ = ∫⁻ g, ∫⁻ x, f (act g x) * h x ∂Q ∂μ :=
        lintegral_lintegral_swap ((hf.comp hm1).mul (hh.comp measurable_fst)).aemeasurable
    _ = ∫⁻ g, ∫⁻ x, f x * h (act g⁻¹ x) ∂Q ∂μ := by
        refine lintegral_congr fun g => ?_
        conv_rhs => rw [← hQ g]
        rw [lintegral_map (f := fun x => f x * h (act g⁻¹ x)) (hf.mul (hh.comp (hmg g⁻¹))) (hmg g)]
        refine lintegral_congr fun x => ?_
        rw [← hmul, inv_mul_cancel, hone]
    _ = ∫⁻ x, ∫⁻ g, f x * h (act g⁻¹ x) ∂μ ∂Q :=
        lintegral_lintegral_swap ((hf.comp measurable_snd).mul (hh.comp hm2)).aemeasurable
    _ = ∫⁻ x, f x * ∫⁻ g, h (act g⁻¹ x₀) ∂μ ∂Q := by
        refine lintegral_congr_ae (htr.mono ?_)
        rintro x ⟨p, rfl⟩
        have hmx : Measurable fun g : G => h (act g⁻¹ (act p x₀)) :=
          hh.comp (hm2.comp measurable_prodMk_right)
        simp only
        rw [lintegral_const_mul _ hmx]
        congr 1
        rw [← lintegral_mul_left_eq_self (fun g : G => h (act g⁻¹ x₀)) p⁻¹]
        refine lintegral_congr fun g => ?_
        rw [← hmul, _root_.mul_inv_rev, inv_inv]
    _ = _ := lintegral_mul_const _ hf

variable {k r : ℕ}

def act (g : Gp k r) (p : (Fin k → ℂ) × ℂ) : (Fin k → ℂ) × ℂ := opAct k r (Matrix.of (inc g)) p

theorem opVec_wI (p : (Fin k → ℂ) × ℂ) (m : Fin (k + 1)) : opVec k r p (wI k r m) = toW k p m := by
  have := m.isLt
  unfold opVec toW wI
  by_cases h : m.val < k
  · rw [dite_eq_left (by simp only; omega), dite_eq_left h]
    exact congrArg p.1 (Fin.ext (by simp))
  · rw [dite_eq_right (by simp only; omega), dite_eq_right h, if_pos (by simp only; omega)]

theorem opVec_inWb (p : (Fin k → ℂ) × ℂ) : inWb k r (opVec k r p) := by
  intro i hi
  unfold opVec
  rw [dite_eq_right (by omega), if_neg (by omega)]

theorem opCo_opVec (p : (Fin k → ℂ) × ℂ) : opCo k r (opVec k r p) = p := by
  refine Eq.trans ?_ (ofW_toW p)
  unfold opCo ofW
  simp only [opVec_wI]

theorem continuous_opVec : Continuous (opVec k r) := by
  refine continuous_pi fun i => ?_
  unfold opVec
  split_ifs
  · exact (continuous_apply _).comp continuous_fst
  · exact continuous_snd
  · exact continuous_const

theorem continuous_act : Continuous (Function.uncurry (act (k := k) (r := r))) := by
  have hc : Continuous fun q : Gp k r × ((Fin k → ℂ) × ℂ) =>
      (Matrix.of (inc q.1) : Mat k r) *ᵥ opVec k r q.2 :=
    Continuous.matrix_mulVec (inc_cont.comp continuous_fst) (continuous_opVec.comp continuous_snd)
  exact (continuous_pi fun i => (continuous_apply (wI k r (Fin.castSucc i))).comp hc).prodMk
    ((continuous_apply (wI k r (Fin.last k))).comp hc)

theorem act_mul (g g' : Gp k r) (p : (Fin k → ℂ) × ℂ) : act (g * g') p = act g (act g' p) := by
  unfold act
  have e : (Matrix.of (inc (g * g')) : Mat k r) = Matrix.of (inc g) * Matrix.of (inc g') := rfl
  rw [e, op_uwb_eq_emb (inc_mem g), op_uwb_eq_emb (inc_mem g'), ← emb_mul, opAct_emb, opAct_emb, opAct_emb,
    blkAct_mul]

theorem act_one (p : (Fin k → ℂ) × ℂ) : act (1 : Gp k r) p = p := by
  have e : (Matrix.of (inc (1 : Gp k r)) : Mat k r) = 1 := rfl
  unfold act opAct
  rw [e, Matrix.one_mulVec, opCo_opVec]

def pt (k : ℕ) (T' : ℝ) : (Fin k → ℂ) × ℂ := (0, (Real.sqrt T' : ℂ))

theorem opVec_pt (T' : ℝ) : opVec k r (pt k T') = opBase k r T' := by
  funext i
  unfold opVec pt opBase wLast
  simp only [Pi.smul_apply, bvec_apply, wI, Fin.ext_iff, Fin.val_last, smul_eq_mul, Pi.zero_apply]
  split_ifs <;> first | omega | simp

theorem act_pt (T' : ℝ) (g : Gp k r) : act g (pt k T') = opOrb k r T' (inc g) := by
  unfold act opAct opOrb
  rw [opVec_pt]

theorem act_trans {T' : ℝ} (hT : 0 < T') {x : (Fin k → ℂ) × ℂ} (hx : x ∈ hypS k T') :
    ∃ g : Gp k r, act g (pt k T') = x := by
  have hTz : Tz k r (opVec k r x) = T' := by
    unfold Tz
    rw [herm_wb _ _ (opVec_inWb x)]
    have e : wbPart k r (opVec k r x) = toW k x := funext fun m => opVec_wI x m
    rw [e]
    unfold herm
    rw [← qf_eq, Complex.ofReal_re, (hypS_iff T' x).1 hx, neg_neg]
  obtain ⟨p, hp, hpz⟩ := transW k r (opVec k r x) (opVec_inWb x) (hTz ▸ hT)
  rw [hTz] at hpz
  refine ⟨⟨p, hp⟩, (act_pt T' _).trans ?_⟩
  show opCo k r (p *ᵥ ((Real.sqrt T' : ℂ) • wLast k r)) = x
  rw [hpz, opCo_opVec]

theorem entry_bound {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hμ : μᴴ * Hb k * μ = Hb k) (i j : Fin (k + 1)) :
    Complex.normSq (μ i j) ≤ 1 + Complex.normSq (μ (Fin.last k) (Fin.last k)) := by
  have col : ∀ {ν : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}, νᴴ * Hb k * ν = Hb k → ∀ j,
      ∑ l : Fin k, Complex.normSq (ν l.castSucc j) - Complex.normSq (ν (Fin.last k) j) =
        if j = Fin.last k then -1 else 1 := by
    intro ν hν j
    have h := form_apply ν j j
    rw [hν] at h
    simp only [Hb, Matrix.diagonal_apply_eq, ← Complex.normSq_eq_conj_mul_self] at h
    apply Complex.ofReal_injective
    push_cast
    rw [← h]
    split_ifs <;> simp
  have hsq : Hb k * Hb k = 1 := by
    rw [Hb, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext j; split_ifs <;> norm_num
  have hμ' : (μᴴ)ᴴ * Hb k * μᴴ = Hb k := by
    have h1 : μ * (Hb k * μᴴ * Hb k) = 1 := mul_eq_one_comm.1 (hb_inv_mul hμ)
    rw [conjTranspose_conjTranspose]
    calc μ * Hb k * μᴴ = μ * (Hb k * μᴴ * Hb k) * Hb k := by
          simp only [Matrix.mul_assoc]; rw [hsq, Matrix.mul_one]
      _ = Hb k := by rw [h1, Matrix.one_mul]
  have row : ∀ j, Complex.normSq (μ (Fin.last k) j) ≤ Complex.normSq (μ (Fin.last k) (Fin.last k)) := by
    intro j
    refine Fin.lastCases le_rfl (fun j => ?_) j
    have h := col hμ' (Fin.last k)
    simp only [conjTranspose_apply, if_true, Complex.star_def, Complex.normSq_conj] at h
    have := Finset.single_le_sum (f := fun l : Fin k => Complex.normSq (μ (Fin.last k) l.castSucc))
      (fun l _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
    linarith
  refine Fin.lastCases (by linarith [row j]) (fun i => ?_) i
  have h := col hμ j
  have := Finset.single_le_sum (f := fun l : Fin k => Complex.normSq (μ l.castSucc j))
    (fun l _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  have h2 := row j
  split_ifs at h <;> linarith

theorem inc_closedEmbedding : IsClosedEmbedding (inc : Gp k r → Mt k r) :=
  amb_closed.isClosedEmbedding_subtypeVal

theorem orbit_proper {T' : ℝ} (hT : 0 < T') (R : ℝ) :
    ∃ K : Set (Gp k r), IsCompact K ∧ ∀ g, act g (pt k T') ∈ Metric.closedBall 0 R → g ∈ K := by
  refine ⟨inc ⁻¹' Metric.closedBall 0 (Real.sqrt (1 + R ^ 2 / T')),
    inc_closedEmbedding.isCompact_preimage (isCompact_closedBall _ _), fun g hg => ?_⟩
  set μ := (Matrix.of (inc g) : Mat k r).submatrix (wI k r) (wI k r) with hμdef
  have he : (Matrix.of (inc g) : Mat k r) = embWb k r μ := op_uwb_eq_emb (inc_mem g)
  have hμ : μᴴ * Hb k * μ = Hb k := by
    rw [← emb_mem (r := r), ← he]; exact (inc_mem g).1
  have hlast : Complex.normSq (μ (Fin.last k) (Fin.last k)) ≤ R ^ 2 / T' := by
    rw [mem_closedBall_zero_iff] at hg
    have h2 : ‖(act g (pt k T')).2‖ ≤ R := (norm_snd_le _).trans hg
    have e : (act g (pt k T')).2 = (Real.sqrt T' : ℂ) * μ (Fin.last k) (Fin.last k) := by
      rw [act_pt]
      show ((Matrix.of (inc g) : Mat k r) *ᵥ ((Real.sqrt T' : ℂ) • bvec (wI k r (Fin.last k))))
        (wI k r (Fin.last k)) = _
      rw [Matrix.mulVec_smul, Pi.smul_apply, mulVec_bvec]
      rfl
    have h3 : Complex.normSq (act g (pt k T')).2 ≤ R ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) h2 2
    rw [e, Complex.normSq_mul, Complex.normSq_ofReal, Real.mul_self_sqrt hT.le] at h3
    rw [le_div_iff₀ hT]
    linarith
  have hpos : 0 ≤ R ^ 2 / T' := by positivity
  have hent : ∀ i j, Complex.normSq (inc g i j) ≤ 1 + R ^ 2 / T' := by
    intro i j
    have e : inc g i j = embWb k r μ i j := congrFun (congrFun he i) j
    rw [e]
    by_cases hi : mid k r i
    · by_cases hj : mid k r j
      · rw [emb_mid _ i j hi hj]
        linarith [entry_bound hμ (midx hi) (midx hj)]
      · rw [emb_out_col _ i j hj]
        split_ifs <;> simp <;> linarith
    · rw [emb_out_row _ i j hi]
      split_ifs <;> simp <;> linarith
  show inc g ∈ Metric.closedBall 0 _
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro i
  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro j
  apply Real.le_sqrt_of_sq_le
  rw [← Complex.normSq_eq_norm_sq]
  exact hent i j

theorem pull_right (ν : Measure (Mt k r)) (hc : ν {x | Matrix.of x ∉ UWb k r} = 0)
    (h : ∀ p ∈ UWb k r, ν.map (rmulM p) = ν) : (pull ν).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  apply inc_memb.map_injective
  have e : (inc : Gp k r → Mt k r) ∘ (fun x => x * g) = rmulM (Matrix.of (inc g)) ∘ inc := rfl
  show ((pull ν).map (fun x => x * g)).map inc = (pull ν).map inc
  rw [Measure.map_map inc_memb.measurable (continuous_mul_const g).measurable, e,
    ← Measure.map_map (rmulM_cont _).measurable inc_memb.measurable, map_pull ν hc, h _ (inc_mem g)]

theorem pull_compact (ν : Measure (Mt k r)) (hG : IsGaugeOn k r (UWb k r) ν) {K : Set (Gp k r)}
    (hK : IsCompact K) : pull ν K ≠ ⊤ := by
  obtain ⟨ρ, h0, ht⟩ := gauge_ball ν hG
  obtain ⟨⟨hσ, hne, hc, hl⟩, -⟩ := hG
  haveI : LocallyCompactSpace (Gp k r) := inc_closedEmbedding.locallyCompactSpace
  haveI : T2Space (Gp k r) := inc_closedEmbedding.isEmbedding.t2Space
  haveI := pull_sigmaFinite ν
  haveI := pull_left ν hl
  have key := measure_eq_div_smul (Measure.haar : Measure (Gp k r)) (pull ν) (s := inc ⁻¹' bBall k r ρ)
    (by rw [pull_apply ν hc]; exact h0.ne') (by rw [pull_apply ν hc]; exact ht.ne)
  set c := (Measure.haar : Measure (Gp k r)) (inc ⁻¹' bBall k r ρ) / pull ν (inc ⁻¹' bBall k r ρ)
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_smul] at key
    exact NeZero.ne _ key
  have h1 : (Measure.haar : Measure (Gp k r)) K ≠ ⊤ := hK.measure_lt_top.ne
  rw [key, Measure.smul_apply, smul_eq_mul] at h1
  intro htop
  rw [htop, ENNReal.mul_top hc0] at h1
  exact h1 rfl

theorem orbRepY : OrbRepY := by
  intro k r T' hk hT νg hG Q hQ hS hC
  by_cases hQ0 : Q = 0
  · exact ⟨0, ENNReal.zero_ne_top, by rw [hQ0, zero_smul]⟩
  haveI : IsFiniteMeasureOnCompacts Q := ⟨fun C h => hC C h⟩
  obtain ⟨R, hR⟩ : ∃ R : ℕ, Q (Metric.closedBall 0 R) ≠ 0 := by
    by_contra h
    push Not at h
    apply hQ0
    rw [← Measure.measure_univ_eq_zero, ← Metric.iUnion_closedBall_nat (0 : (Fin k → ℂ) × ℂ)]
    exact measure_iUnion_null h
  set C : Set ((Fin k → ℂ) × ℂ) := Metric.closedBall 0 R with hCdef
  have hCm : MeasurableSet C := Metric.isClosed_closedBall.measurableSet
  have hRt : Q C ≠ ⊤ := (hC C (isCompact_closedBall _ _)).ne
  have hU := unimodW k r νg hk hG
  have hfin := fun K => pull_compact νg hG (K := K)
  obtain ⟨⟨hσ, hne, hc, hl⟩, -⟩ := hG
  haveI := pull_sigmaFinite νg
  haveI := pull_left νg hl
  haveI := pull_right νg hc hU
  have hom := (continuous_opOrb (k := k) (r := r) T').measurable
  have htr : ∀ᵐ x ∂Q, ∃ g : Gp k r, act g (pt k T') = x := by
    have : ∀ᵐ x ∂Q, x ∈ hypS k T' := hS
    exact this.mono fun x hx => act_trans hT hx
  set b := ∫⁻ g : Gp k r, C.indicator 1 (act g⁻¹ (pt k T')) ∂(pull νg) with hb
  have key : ∀ E, MeasurableSet E → νg.map (opOrb k r T') E * Q C = Q E * b := by
    intro E hE
    have h := fubini_identity act continuous_act.measurable act_mul act_one (pull νg) Q
      (fun g => hQ _ (inc_mem g)) (pt k T') htr (measurable_one.indicator hE) (measurable_one.indicator hCm)
    rw [lintegral_indicator_one hE, lintegral_indicator_one hCm] at h
    rw [← h]
    congr 1
    rw [← lintegral_indicator_one hE, ← map_pull νg hc, lintegral_map (measurable_one.indicator hE) hom,
      inc_memb.lintegral_map, map_pull νg hc]
    simp_rw [act_pt]
  have hbt : b ≠ ⊤ := by
    open scoped Pointwise in
    obtain ⟨K, hK, hKm⟩ := orbit_proper (k := k) (r := r) hT R
    haveI : T2Space (Gp k r) := inc_closedEmbedding.isEmbedding.t2Space
    refine ne_top_of_le_ne_top (hfin K⁻¹ hK.inv) ?_
    rw [← lintegral_indicator_one hK.inv.measurableSet]
    refine lintegral_mono fun g => ?_
    by_cases hg : act g⁻¹ (pt k T') ∈ C
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (Set.mem_inv.2 (hKm _ hg))]
      rfl
    · rw [Set.indicator_of_notMem hg]; exact zero_le
  have hb0 : b ≠ 0 := by
    intro h0
    have h := key Set.univ MeasurableSet.univ
    rw [h0, mul_zero, Measure.map_apply hom MeasurableSet.univ, Set.preimage_univ] at h
    rcases mul_eq_zero.1 h with h | h
    · exact hne (Measure.measure_univ_eq_zero.1 h)
    · exact hR h
  refine ⟨Q C / b, (ENNReal.div_lt_top hRt hb0).ne, ?_⟩
  ext E hE
  rw [Measure.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_right_comm, mul_comm (Q C), key E hE, mul_assoc,
    ENNReal.mul_inv_cancel hb0 hbt, mul_one]

end GlobalTheory.HypOrbitUnique
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidInvariantMeasureOrbitRepresentationStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperboloid_invariant_measure_orbit_representation : PI.RhsWLim.W.OrbRepY := by
  first | exact @GlobalTheory.HypOrbitUnique.orbRepY | exact GlobalTheory.HypOrbitUnique.orbRepY | (intros; apply GlobalTheory.HypOrbitUnique.orbRepY <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidChartMeasureFormula
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidChartMeasureFormula
noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace GlobalTheory.HypChartPf

open PI.RhsWLim PI.RhsWLim.W

private lemma ofLp_qFw_kapT (k : ℕ) (v : (Fin k → ℂ) × ℂ) :
    WithLp.ofLp (qFw k (kapT k v)) = (WithLp.toLp 2 v.1, Complex.arg v.2) := by
  ext a
  · simp [qFw, kapT, Complex.re_add_im]
  · simp [qFw, kapT]

private lemma hypPar_toLp_arg_of_mem_hypS (k : ℕ) (T' : ℝ) (v : (Fin k → ℂ) × ℂ) (hv : v ∈ hypS k T') :
    hypPar k T' (WithLp.toLp 2 v.1, Complex.arg v.2) = v := by
  simp only [hypS, Set.mem_ofPred_eq] at hv
  have hn : ‖(WithLp.toLp 2 v.1 : EuclideanSpace ℂ (Fin k))‖ ^ 2 + T' = ‖v.2‖ ^ 2 := by
    rw [← normSq_sum_eq, ← Complex.normSq_eq_norm_sq]
    simp only []
    linarith
  simp only [hypPar, hn, Real.sqrt_sq (norm_nonneg _), Complex.norm_mul_exp_arg_mul_I, ]

private lemma kapT_hypPar_ofLp_qFw (k : ℕ) (T' : ℝ) (hT' : 0 < T') (x : TrE k)
    (hx : (WithLp.ofLp (qFw k x)).2 ∈ Set.Ioc (-Real.pi) Real.pi) :
    kapT k (hypPar k T' (WithLp.ofLp (qFw k x))) = x := by
  ext o
  rcases o with _ | ⟨a, b⟩
  · simp only [kapT, hypPar]
    simp only [qFw] at hx ⊢
    simp only [WithLp.equiv_symm_apply, WithLp.ofLp_toLp]
    rw [Complex.arg_real_mul _ (Real.sqrt_pos.2 (add_pos_of_nonneg_of_pos (sq_nonneg _) hT')),
      Complex.exp_mul_I, Complex.arg_cos_add_sin_mul_I hx]
  · cases b <;> simp [kapT, hypPar, qFw]

theorem restrict_periodic (A : Set ℝ) (hA : MeasurableSet A) (hp : ∀ x, x + 2 * Real.pi ∈ A ↔ x ∈ A) :
    volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)) A = volume.restrict (Set.Ioc (-Real.pi) Real.pi) A := by
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h1 := isAddFundamentalDomain_Ioc hpos 0 (volume : Measure ℝ)
  have h2 := isAddFundamentalDomain_Ioc hpos (-Real.pi) (volume : Measure ℝ)
  rw [zero_add] at h1
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at h2
  have key : ∀ n : ℤ, ∀ x, n • (2 * Real.pi) + x ∈ A ↔ x ∈ A := by
    intro n
    induction n using Int.induction_on with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [← ih x, ← hp ((m : ℤ) • (2 * Real.pi) + x)]
      rw [show ((m : ℤ) + 1) • (2 * Real.pi) + x = (m : ℤ) • (2 * Real.pi) + x + 2 * Real.pi by
        rw [add_smul, one_smul]; abel]
    | pred m ih =>
      intro x
      have h := hp ((-(m : ℤ) - 1) • (2 * Real.pi) + x)
      rw [show (-(m : ℤ) - 1) • (2 * Real.pi) + x + 2 * Real.pi = (-(m : ℤ)) • (2 * Real.pi) + x by
        rw [sub_smul, one_smul]; abel, ih x] at h
      exact h.symm
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  refine h1.measure_set_eq h2 hA ?_
  rintro ⟨g, hg⟩
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hg
  ext x
  exact key n x

theorem hypM_eq (k : ℕ) (T' : ℝ) (E : Set ((Fin k → ℂ) × ℂ)) (hE : MeasurableSet E) :
    hypM k T' E = (1 / 2) * (volume.prod volume)
      (hypPar k T' ⁻¹' E ∩ Set.univ ×ˢ Set.Ioc (-Real.pi) Real.pi) := by
  have hmeas : Measurable (hypPar k T') := (continuous_hypPar k T').measurable
  have hP : MeasurableSet (hypPar k T' ⁻¹' E) := hmeas hE
  unfold hypM
  rw [Measure.smul_apply, Measure.map_apply hmeas hE, smul_eq_mul]
  congr 1
  rw [Measure.prod_apply hP, Measure.prod_apply (hP.inter (MeasurableSet.univ.prod measurableSet_Ioc))]
  refine lintegral_congr (fun y => ?_)
  have hs : MeasurableSet (Prod.mk y ⁻¹' (hypPar k T' ⁻¹' E)) := measurable_prodMk_left hP
  rw [restrict_periodic _ hs ?_, Measure.restrict_apply hs]
  · congr 1
    ext θ
    simp
  · intro x
    have e : hypPar k T' (y, x + 2 * Real.pi) = hypPar k T' (y, x) := by
      simp only [hypPar, Prod.mk.injEq, true_and]
      rw [show ((x + 2 * Real.pi : ℝ) : ℂ) * Complex.I = (x : ℂ) * Complex.I + 2 * Real.pi * Complex.I by
        push_cast; ring, Complex.exp_periodic]
    simp only [Set.mem_preimage]
    rw [e]

theorem hypM_eq_kapT (k : ℕ) (T' : ℝ) (hT' : 0 < T') (E : Set ((Fin k → ℂ) × ℂ)) (hE : MeasurableSet E)
    (hS : E ⊆ hypS k T') : hypM k T' E = (1 / 2) * volume (kapT k '' E) := by
  rw [hypM_eq k T' E hE]
  congr 1
  have hFm : MeasurableSet (hypPar k T' ⁻¹' E ∩ Set.univ ×ˢ Set.Ioc (-Real.pi) Real.pi) :=
    ((continuous_hypPar k T').measurable hE).inter (MeasurableSet.univ.prod measurableSet_Ioc)
  have hset : kapT k '' E =
      (fun x : TrE k => WithLp.ofLp (qFw k x)) ⁻¹' (hypPar k T' ⁻¹' E ∩ Set.univ ×ˢ Set.Ioc (-Real.pi) Real.pi) := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [ofLp_qFw_kapT k v, hypPar_toLp_arg_of_mem_hypS k T' v (hS hv)]
      exact ⟨hv, Complex.arg_mem_Ioc _⟩
    · rintro ⟨h1, h2⟩
      exact ⟨_, h1, kapT_hypPar_ofLp_qFw k T' hT' x h2⟩
  rw [hset, (qIso_measurePreserving k).measure_preimage hFm.nullMeasurableSet]

def sgn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if r ≤ i.val ∧ i.val < r + k then 1 else if i.val = r + k then -1 else 0

theorem gen_semiconj (k r : ℕ) (q : TrE k) :
    SemiconjBy (Matrix.diagonal (sgn k r)) (-opGen k r q) (opGen k r q)ᴴ := by
  show _ = _
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.neg_apply]
  unfold opGen sgn
  split_ifs <;> (try (exfalso; omega)) <;> simp

private lemma exp_conjTranspose_mul_mul_exp_of_skew {n : Type*} [Fintype n] [DecidableEq n] (U X : Matrix n n ℂ)
    (hU : IsUnit U) (h : U * -X = Xᴴ * U) : (NormedSpace.exp X)ᴴ * U * NormedSpace.exp X = U := by
  have hdet : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).mp hU
  have h1 : Xᴴ = U * -X * U⁻¹ := by rw [h, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]
  have h3 : NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl X)), neg_add_cancel,
      NormedSpace.exp_zero]
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ hU]
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hdet, h3, Matrix.mul_one]

private lemma exp_opGen_conjTranspose_mul_diagonal_mul (k r : ℕ) (q : TrE k) (u : ℂ) (hu : u ≠ 0) :
    (NormedSpace.exp (opGen k r q))ᴴ * Matrix.diagonal (fun i => if sgn k r i = 0 then u else sgn k r i) *
      NormedSpace.exp (opGen k r q) = Matrix.diagonal (fun i => if sgn k r i = 0 then u else sgn k r i) := by
  have hsemi := gen_semiconj k r q
  unfold SemiconjBy at hsemi
  have hent : ∀ i j, sgn k r i * -opGen k r q i j = star (opGen k r q j i) * sgn k r j := by
    intro i j
    have := congrFun (congrFun hsemi i) j
    rwa [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.neg_apply] at this
  have hz : ∀ i j, sgn k r i = 0 → opGen k r q i j = 0 ∧ opGen k r q j i = 0 := by
    intro i j hi
    unfold sgn at hi
    split_ifs at hi with h1 h2
    · norm_num at hi
    · norm_num at hi
    · unfold opGen
      constructor <;> split_ifs <;> rfl
  apply exp_conjTranspose_mul_mul_exp_of_skew
  · refine (Matrix.isUnit_iff_isUnit_det _).2 ?_
    rw [Matrix.det_diagonal]
    refine isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
    split_ifs with h
    · exact hu
    · exact h
  · ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.neg_apply]
    by_cases hi : sgn k r i = 0
    · obtain ⟨h1, h2⟩ := hz i j hi
      simp [h1, h2]
    by_cases hj : sgn k r j = 0
    · obtain ⟨h1, h2⟩ := hz j i hj
      simp [h1, h2]
    simp only [if_neg hi, if_neg hj]
    exact hent i j

theorem exp_form (k r : ℕ) (q : TrE k) :
    (NormedSpace.exp (opGen k r q))ᴴ * Matrix.diagonal (sgn k r) * NormedSpace.exp (opGen k r q) =
      Matrix.diagonal (sgn k r) := by
  have hD : Matrix.diagonal (sgn k r) = (1 / 2 : ℂ) •
      (Matrix.diagonal (fun i => if sgn k r i = 0 then 1 else sgn k r i) +
        Matrix.diagonal (fun i => if sgn k r i = 0 then -1 else sgn k r i)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
      split_ifs with h <;> [rw [h]; skip] <;> ring
    · simp [Matrix.diagonal_apply_ne _ hij]
  rw [hD, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    exp_opGen_conjTranspose_mul_diagonal_mul k r q 1 one_ne_zero, exp_opGen_conjTranspose_mul_diagonal_mul k r q (-1) (neg_ne_zero.2 one_ne_zero)]

private lemma wI_injective' (k r : ℕ) : Function.Injective (wI k r) := by
  intro a b h
  ext
  have := congrArg Fin.val h
  simp [wI] at this
  omega

theorem form_eq (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) :
    star v ⬝ᵥ (Matrix.diagonal (sgn k r) *ᵥ v) =
      ((∑ i, Complex.normSq ((opCo k r v).1 i) - Complex.normSq (opCo k r v).2 : ℝ) : ℂ) := by
  have hs : star v ⬝ᵥ (Matrix.diagonal (sgn k r) *ᵥ v) =
      ∑ j : Fin (k + 1), star (v (wI k r j)) * (sgn k r (wI k r j) * v (wI k r j)) := by
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
    symm
    refine Fintype.sum_of_injective _ (wI_injective' k r) _ (fun i => star (v i) * (sgn k r i * v i)) ?_ (fun _ => rfl)
    intro i hi
    have : sgn k r i = 0 := by
      unfold sgn
      rw [if_neg, if_neg]
      · intro h; exact hi ⟨⟨i.val - r, by omega⟩, by ext; simp [wI]; omega⟩
      · rintro ⟨h1, h2⟩; exact hi ⟨⟨i.val - r, by omega⟩, by ext; simp [wI]; omega⟩
    simp [this]
  have h1 : ∀ j : Fin k, sgn k r (wI k r j.castSucc) = 1 := by
    intro j; unfold sgn; rw [if_pos]; simp [wI]
  have h2 : sgn k r (wI k r (Fin.last k)) = -1 := by
    unfold sgn; rw [if_neg, if_pos] <;> simp [wI]
  rw [hs, Fin.sum_univ_castSucc, h2]
  simp only [h1, opCo]
  push_cast
  simp [Complex.normSq_eq_conj_mul_self, sub_eq_add_neg]

theorem opE_subset (k r : ℕ) (T' : ℝ) (hT' : 0 < T') (ρ : ℝ) : opE k r T' ρ ⊆ hypS k T' := by
  rintro p ⟨q, -, rfl⟩
  have hq : star (NormedSpace.exp (opGen k r q) *ᵥ opBase k r T') ⬝ᵥ
      (Matrix.diagonal (sgn k r) *ᵥ (NormedSpace.exp (opGen k r q) *ᵥ opBase k r T')) =
      star (opBase k r T') ⬝ᵥ (Matrix.diagonal (sgn k r) *ᵥ opBase k r T') := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, exp_form]
  rw [form_eq, form_eq] at hq
  have hb : ∀ i : Fin k, opBase k r T' (wI k r i.castSucc) = 0 := by
    intro i
    have hne : wI k r i.castSucc ≠ wI k r (Fin.last k) := fun h => (Fin.castSucc_lt_last i).ne (wI_injective' k r h)
    simp [opBase, wLast, bvec, hne]
  have hl : opBase k r T' (wI k r (Fin.last k)) = (Real.sqrt T' : ℂ) := by
    simp [opBase, wLast, bvec]
  simp only [opCo, hb, hl, map_zero, Finset.sum_const_zero, Complex.normSq_ofReal,
    Real.mul_self_sqrt hT'.le] at hq
  simp only [hypS, Set.mem_ofPred_eq, opCo]
  linarith [Complex.ofReal_injective hq]

theorem hypChart : HypChart := by
  unfold HypChart
  intro k r T' hk hT'
  refine ⟨1, one_pos, fun ρ _ _ => ?_⟩
  have himg : phiT k r T' '' Metric.ball 0 ρ = kapT k '' opE k r T' ρ := by
    rw [opE, Set.image_image]; rfl
  rw [himg, hypM_eq_kapT k T' hT' _ (opEMeas k r T' ρ) (opE_subset k r T' hT' ρ)]

end GlobalTheory.HypChartPf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidChartMeasureFormulaStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperboloid_chart_measure_formula : PI.RhsWLim.W.HypChart := by
  first | exact @GlobalTheory.HypChartPf.hypChart | exact GlobalTheory.HypChartPf.hypChart | (intros; apply GlobalTheory.HypChartPf.hypChart <;> assumption)
end
end

noncomputable section

namespace GlobalTheory.RankOneChart

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.RI

theorem rhsWLim_of_leaves (hD : HaarDens) (hQ : HypQ) (hC : HypChart) (hK : GaugeK) (hV : GaugeVolUk)
    (hT : TubeLimK) (hR : OrbRepY) : Formalism.L2.SG.Pf.WB.RhsWLim := by
  have hL : PI.RhsWLim.RhsWLim :=
    rhsWLim_of mBaseMem tBallMeas (gaugeExists_of_dens hD) (rhsHaar_of (rhsWInv_of_hypQ hQ)) haarUniq
      (constVal_of_orbit (orbitPush_of hV hK hT (hypInv_of lebInvB (coneForm_of hypTh coneVol)) hR
        (hypLocal_of chartJac hC hermitianDefectAdd) opEMeas hypLF))
  exact fun k r z z' μW μW' a a' μsec hW => hL k r z z' μW μW' a a' μsec
    ⟨hW.k_pos, hW.z_mem, hW.z'_mem, hW.T_pos, hW.T'_pos, hW.haarW, hW.haarW', hW.a_pos, hW.a'_pos, hW.massW,
      hW.massW', hW.sec⟩

theorem rhsWLim : Formalism.L2.SG.Pf.WB.RhsWLim :=
  rhsWLim_of_leaves GlobalTheory.T.haar_unitaryGroupWb_density_chart GlobalTheory.T.hyperboloid_invariant_measure_polar_form GlobalTheory.T.hyperboloid_chart_measure_formula GlobalTheory.T.stabiliser_unitaryGroup_has_gaugeMeasure GlobalTheory.T.unitaryGroup_gaugeVolume_in_hermitianUnitary GlobalTheory.T.stabilizerTube_gaugeMass_asymptotic GlobalTheory.T.hyperboloid_invariant_measure_orbit_representation

instance : Fact (Formalism.L2.SG.Pf.WB.RhsWLim) := ⟨rhsWLim⟩

end GlobalTheory.RankOneChart
