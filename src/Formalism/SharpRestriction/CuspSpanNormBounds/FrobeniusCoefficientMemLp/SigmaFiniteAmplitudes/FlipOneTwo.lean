module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.InPairOfStab

@[expose] public section

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.ProductFirstParts
section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.ProductFirstZerothParts
section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.AeInPairPair
section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.SigmaFiniteOfWeight
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

section Gen

variable {Y : Type*} [MeasurableSpace Y]

theorem sigmaFinite_of_weight (ν : Measure Y) (W : Y → ℝ≥0∞) (hWm : Measurable W) (hWi : ∫⁻ y, W y ∂ν < ⊤)
    (hW0 : ν {y | W y = 0} = 0) : SigmaFinite ν := by
  refine Measure.sigmaFinite_of_countable
    (S := insert {y | W y = 0} (Set.range fun n : ℕ => {y | ((n : ℝ≥0∞) + 1)⁻¹ ≤ W y})) ?_ ?_ ?_
  · exact (Set.countable_range _).insert _
  · intro s hs
    rcases hs with rfl | ⟨n, rfl⟩
    · rw [hW0]
      exact ENNReal.zero_lt_top
    · calc ν {y | ((n : ℝ≥0∞) + 1)⁻¹ ≤ W y} ≤ (∫⁻ y, W y ∂ν) / ((n : ℝ≥0∞) + 1)⁻¹ :=
            meas_ge_le_lintegral_div hWm.aemeasurable (by simp) (by simp)
        _ < ⊤ := ENNReal.div_lt_top hWi.ne (by simp)
  · apply Set.eq_univ_of_forall
    intro y
    by_cases h : W y = 0
    · exact Set.mem_sUnion.2 ⟨_, Set.mem_insert _ _, h⟩
    · obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt h
      refine Set.mem_sUnion.2 ⟨_, Set.mem_insert_of_mem _ ⟨n, rfl⟩, ?_⟩
      show ((n : ℝ≥0∞) + 1)⁻¹ ≤ W y
      exact le_trans (ENNReal.inv_le_inv.2 le_self_add) hn.le

end Gen

def mStab (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (q : PairSp k r × Mt k r) : PairSp k r :=
  stabAct γ (Matrix.of q.2) q.1

def qG (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (q : Mt k r × Mt k r) : Mt k r :=
  Matrix.of.symm (γ⁻¹ * Matrix.of q.2 * γ * Matrix.of q.1)

theorem measurable_mStab (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (mStab (k := k) (r := r) γ) := by
  unfold mStab stabAct
  have c1 : Continuous (fun q : PairSp k r × Mt k r => (Matrix.of.symm (of q.2 * of q.1.1.2) : Mt k r)) :=
    continuous_snd.matrix_mul continuous_fst.fst.snd
  have c2 : Continuous (fun q : PairSp k r × Mt k r =>
      (Matrix.of.symm (γ⁻¹ * of q.2 * γ * of q.1.2.2) : Mt k r)) :=
    ((continuous_const.matrix_mul continuous_snd).matrix_mul continuous_const).matrix_mul
      continuous_fst.snd.snd
  exact (measurable_fst.fst.fst.prodMk c1.measurable).prodMk (measurable_fst.snd.fst.prodMk c2.measurable)

theorem continuous_qG (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Continuous (qG (k := k) (r := r) γ) := by
  exact ((continuous_const.matrix_mul continuous_snd).matrix_mul continuous_const).matrix_mul continuous_fst

section Cell

variable (L : LocBessel k r) {μG : Measure (Mt k r)} {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
  {μR νR : Measure (Mt k r)} {ν : Measure (PairSp k r)}

theorem pairMeas_eq_map (hμR : IsHaarOn (RStab k r γ) μR) (hOQ : IsOrbQuot L γ μR ν) :
    pairMeas L = (ν.prod μR).map (mStab γ) := by
  haveI : SigmaFinite μR := hμR.1
  ext s hs
  have hf : Measurable (s.indicator (1 : PairSp k r → ℝ≥0∞)) := measurable_one.indicator hs
  rw [← lintegral_indicator_one (μ := pairMeas L) hs,
    ← lintegral_indicator_one (μ := (ν.prod μR).map (mStab γ)) hs, hOQ _ hf,
    lintegral_map hf (measurable_mStab γ),
    lintegral_prod (fun q => s.indicator 1 (mStab γ q)) (hf.comp (measurable_mStab γ)).aemeasurable]
  rfl

theorem unfold_G (hμR : IsHaarOn (RStab k r γ) μR)
    (hQ : PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR) :
    ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, ∫⁻ a, f (qG γ (x, a)) ∂μR ∂νR := by
  intro f hf
  rw [hQ f hf]
  refine lintegral_congr fun x => ?_
  have hc : Measurable (fun y : Mt k r => fun i j => (γ⁻¹ * Matrix.of y * γ) i j) := by
    have : Continuous (fun y : Mt k r => (Matrix.of.symm (γ⁻¹ * Matrix.of y * γ) : Mt k r)) :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact this.measurable
  have hm : Measurable (fun s : Mt k r => f (fun i j => (of s * of x) i j)) := by
    have : Continuous (fun s : Mt k r => (Matrix.of.symm (of s * of x) : Mt k r)) :=
      continuous_id.matrix_mul continuous_const
    exact hf.comp this.measurable
  rw [lintegral_map hm hc]
  rfl

theorem muG_eq_map (hμR : IsHaarOn (RStab k r γ) μR)
    (hQ : PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR) :
    μG = (νR.prod μR).map (qG γ) := by
  have : SigmaFinite μR := hμR.1
  exact map_of_unfold μG νR μR (qG γ) (continuous_qG γ).measurable (unfold_G hμR hQ)

theorem sigmaFinite_nuR (hμG : IsHaarOn (UH (Hpk k r)) μG) (hμR : IsHaarOn (RStab k r γ) μR)
    (hQ : PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR) :
    SigmaFinite νR := by
  have : SigmaFinite μR := hμR.1
  have : SigmaFinite μG := hμG.1
  exact sigmaFinite_of_unfold μG νR μR hμR.2.1 (qG γ) (continuous_qG γ).measurable (unfold_G hμR hQ)

end Cell

end Formalism.MainNotions.S.Pv.AmpDDPf
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

theorem ae_inPair_pair (L : LocBessel k r) : ∀ᵐ p ∂(pairMeas L), InPair L p := by
  haveI := L.hμW.1.1
  haveI := L.hμW'.1.1
  have hW := ae_mem_sk L.hμW.1
  have hW' := ae_mem_sk L.hμW'.1
  have hN : ∀ᵐ x ∂L.μN, of x ∈ Nset k r := ae_mem_haarLieN _
  have h1 : ∀ᵐ p ∂(L.μW.prod L.μN), of p.1 ∈ UWset k r L.z ∧ of p.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hW).and (Measure.quasiMeasurePreserving_snd.ae hN)
  have h2 : ∀ᵐ p ∂(L.μW'.prod L.μN), of p.1 ∈ UWset k r L.z' ∧ of p.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hW').and (Measure.quasiMeasurePreserving_snd.ae hN)
  have h := (Measure.quasiMeasurePreserving_fst.ae h1).and (Measure.quasiMeasurePreserving_snd.ae h2)
  filter_upwards [h] with p hp
  exact ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩

theorem ae_inPair_nu (L : LocBessel k r) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {μR : Measure (Mt k r)} {ν : Measure (PairSp k r)} (hμR : IsHaarOn (RStab k r γ) μR)
    (hOQ : IsOrbQuot L γ μR ν) : ∀ᵐ p ∂ν, InPair L p := by
  classical
  have hc : IsClosed {p : PairSp k r | InPair L p} := by
    have hU : IsClosed {x : Mt k r | of x ∈ UWset k r L.z} := Formalism.FourierDecayAlt.P.B6.isClosed_UWset k r L.z
    have hU' : IsClosed {x : Mt k r | of x ∈ UWset k r L.z'} := Formalism.FourierDecayAlt.P.B6.isClosed_UWset k r L.z'
    have hN : IsClosed {x : Mt k r | of x ∈ Nset k r} := Formalism.FourierDecayAlt.P.B6.isClosed_Nset k r
    exact (hU.preimage (continuous_fst.comp continuous_fst)).inter
      ((hN.preimage (continuous_snd.comp continuous_fst)).inter
        ((hU'.preimage (continuous_fst.comp continuous_snd)).inter
          (hN.preimage (continuous_snd.comp continuous_snd))))
  have hB : MeasurableSet {p : PairSp k r | ¬ InPair L p} := hc.measurableSet.compl
  have hpair : pairMeas L {p | ¬ InPair L p} = 0 := ae_iff.mp (ae_inPair_pair L)
  have hq := hOQ _ (measurable_one.indicator hB)
  rw [lintegral_indicator_one hB, hpair] at hq
  have hR : ∀ᵐ a ∂μR, of a ∈ RStab k r γ := ae_mem_sk hμR
  have hμR0 : μR Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hμR.2.1
  have key : ∀ x ∈ {p : PairSp k r | ¬ InPair L p},
      μR Set.univ ≤ ∫⁻ a, {p : PairSp k r | ¬ InPair L p}.indicator 1 (stabAct γ (of a) x) ∂μR := by
    intro x hx
    calc μR Set.univ = ∫⁻ _a, (1 : ℝ≥0∞) ∂μR := by simp
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [hR] with a ha
        have hm : stabAct γ (of a) x ∈ {p : PairSp k r | ¬ InPair L p} :=
          fun h => hx (inPair_of_stab L ha h)
        simp [Set.indicator_of_mem hm]
  have h2 : ∫⁻ x, {p : PairSp k r | ¬ InPair L p}.indicator (fun _ => μR Set.univ) x ∂ν = 0 := by
    apply le_antisymm ?_ zero_le
    rw [hq]
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ {p : PairSp k r | ¬ InPair L p}
    · rw [Set.indicator_of_mem hx]
      exact key x hx
    · simp only [Set.indicator, hx, if_false]
      exact zero_le
  rw [lintegral_indicator_const hB] at h2
  rw [ae_iff]
  exact (mul_eq_zero.mp h2).resolve_left hμR0

theorem ae_uh_nuR {μG : Measure (Mt k r)} {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {μR νR : Measure (Mt k r)} (hγ : γ ∈ UH (Hpk k r)) (hμG : IsHaarOn (UH (Hpk k r)) μG)
    (hμR : IsHaarOn (RStab k r γ) μR)
    (hQ : PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR) :
    ∀ᵐ x ∂νR, Matrix.of x ∈ UH (Hpk k r) := by
  classical
  have hUH : IsClosed {x : Mt k r | of x ∈ UH (Hpk k r)} := Formalism.MainNotions.LowestKTypeMultiplicity.isClosed_UH k r
  have hB : MeasurableSet {x : Mt k r | of x ∉ UH (Hpk k r)} := hUH.measurableSet.compl
  have hG : μG {x : Mt k r | of x ∉ UH (Hpk k r)} = 0 := ae_iff.mp (ae_mem_sk hμG)
  have hq := hQ _ (measurable_one.indicator hB)
  rw [lintegral_indicator_one hB, hG] at hq
  have hFc : Continuous (fun x : Mt k r => fun i j => (γ⁻¹ * Matrix.of x * γ) i j) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact ((continuous_const.matrix_mul (continuous_id : Continuous fun x : Mt k r => x)).matrix_mul
      continuous_const).matrix_elem i j
  have hS : ∀ᵐ s ∂(μR.map (fun x : Mt k r => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)),
      of s ∈ UH (Hpk k r) := by
    rw [ae_map_iff hFc.measurable.aemeasurable hUH.measurableSet]
    filter_upwards [ae_mem_sk hμR] with a ha
    exact ha.2.1
  have hμ0 : (μR.map (fun x : Mt k r => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) Set.univ ≠ 0 := by
    rw [Measure.map_apply hFc.measurable MeasurableSet.univ, Set.preimage_univ]
    exact Measure.measure_univ_ne_zero.mpr hμR.2.1
  have mulUH : ∀ s x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      s ∈ UH (Hpk k r) → s * x ∈ UH (Hpk k r) → x ∈ UH (Hpk k r) := by
    intro s x hs hsx
    simp only [UH, Set.mem_setOf_eq] at hs hsx ⊢
    rw [Matrix.conjTranspose_mul] at hsx
    calc xᴴ * Hpk k r * x = xᴴ * (sᴴ * Hpk k r * s) * x := by rw [hs]
      _ = xᴴ * sᴴ * Hpk k r * (s * x) := by simp only [Matrix.mul_assoc]
      _ = Hpk k r := hsx
  have key : ∀ x ∈ {x : Mt k r | of x ∉ UH (Hpk k r)},
      (μR.map (fun x : Mt k r => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) Set.univ ≤
        ∫⁻ s, {x : Mt k r | of x ∉ UH (Hpk k r)}.indicator 1 (fun i j => (of s * of x) i j)
          ∂(μR.map (fun x : Mt k r => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) := by
    intro x hx
    calc _ = ∫⁻ _s, (1 : ℝ≥0∞) ∂(μR.map (fun x : Mt k r => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) := by simp
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [hS] with s hs
        have hm : (fun i j => (of s * of x) i j : Mt k r) ∈ {x : Mt k r | of x ∉ UH (Hpk k r)} :=
          fun h => hx (mulUH _ _ hs h)
        simp [Set.indicator_of_mem hm]
  have h2 : ∫⁻ x, {x : Mt k r | of x ∉ UH (Hpk k r)}.indicator
      (fun _ => (μR.map (fun x : Mt k r => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) Set.univ) x ∂νR = 0 := by
    apply le_antisymm ?_ zero_le
    rw [hq]
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ {x : Mt k r | of x ∉ UH (Hpk k r)}
    · rw [Set.indicator_of_mem hx]
      exact key x hx
    · simp only [Set.indicator, hx, if_false]
      exact zero_le
  rw [lintegral_indicator_const hB] at h2
  rw [ae_iff]
  exact (mul_eq_zero.mp h2).resolve_left hμ0

end Formalism.MainNotions.S.Pv.AmpDDPf
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

theorem measurable_pairMaj (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (b : ℝ) :
    Measurable (Formalism.MainNotions.S.Pv.AmpDD.pairMaj (k := k) (r := r) γ b) := by
  let g0 : Mt k r := γ
  have hM : Measurable fun p : PairSp k r =>
      Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM (Formalism.FourierDecayAlt.P.B7.mulM
        (Formalism.FourierDecayAlt.P.B7.invM p.1.1) (Formalism.FourierDecayAlt.P.B7.invM p.1.2)) g0) p.2.2) p.2.1 :=
    Formalism.FourierDecayAlt.P.B7.meas_mulM (Formalism.FourierDecayAlt.P.B7.meas_mulM (Formalism.FourierDecayAlt.P.B7.meas_mulM (Formalism.FourierDecayAlt.P.B7.meas_mulM
      (Formalism.FourierDecayAlt.P.B7.measurable_invM.comp (measurable_fst.comp measurable_fst))
      (Formalism.FourierDecayAlt.P.B7.measurable_invM.comp (measurable_snd.comp measurable_fst))) measurable_const)
      (measurable_snd.comp measurable_snd)) (measurable_fst.comp measurable_snd)
  exact (meas_gN_rpow (-b)).comp hM

theorem sigmaFinite_nu (L : LocBessel k r) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hγ : γ ∈ UH (Hpk k r)) {μR : Measure (Mt k r)} {ν : Measure (PairSp k r)} (hμR : IsHaarOn (RStab k r γ) μR)
    (hOQ : IsOrbQuot L γ μR ν) (hNI : Formalism.FourierDecayAlt.ThreeDimData.NormInv) {b : ℝ}
    (hpm : Integrable (Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b) ν) : SigmaFinite ν := by
  refine sigmaFinite_of_weight ν (fun p => ENNReal.ofReal (Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b p))
    (ENNReal.measurable_ofReal.comp (measurable_pairMaj γ b)) ?_ ?_
  · have h := hpm.2
    refine lt_of_le_of_lt (lintegral_mono fun p => ?_) h
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  · have hae : ∀ᵐ p ∂ν, ¬ (ENNReal.ofReal (Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b p) = 0) := ?_
    · have := ae_iff.mp hae
      simpa only [not_not] using this
    filter_upwards [ae_inPair_nu L hμR hOQ] with p hp
    obtain ⟨hh, hn, hh', hn'⟩ := hp
    have hM : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of p.2.2 * Matrix.of p.2.1 ∈ UH (Hpk k r) :=
      PI.WBL.Cv.uh_mul (PI.WBL.Cv.uh_mul (PI.WBL.Cv.uh_mul (PI.WBL.Cv.uh_mul (PI.WBL.Cv.uh_inv hh.1).2.2
        (PI.WBL.Cv.uh_inv hn.1).2.2) hγ) hn'.1) hh'.1
    have h1 := ((hNI k r).2 _ hM).2
    have hpos : 0 < Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b p := by
      unfold Formalism.MainNotions.S.Pv.AmpDD.pairMaj
      exact Real.rpow_pos_of_pos (by linarith) _
    simpa using hpos

end Formalism.MainNotions.S.Pv.AmpDDPf
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

attribute [local instance] Formalism.FourierDecayAlt.P.B7.properFD

theorem qG_invM (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (x a : Mt k r) :
    qG γ (x, Formalism.FourierDecayAlt.P.B7.invM a) = Matrix.of.symm (γ⁻¹ * (Matrix.of a)⁻¹ * γ * Matrix.of x) := rfl

theorem qG_inv_mem {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r))
    {x a : Mt k r} (hx : Matrix.of x ∈ UH (Hpk k r)) (ha : Matrix.of a ∈ UH (Hpk k r)) :
    Matrix.of (qG γ (x, Formalism.FourierDecayAlt.P.B7.invM a)) ∈ UH (Hpk k r) := by
  rw [qG_invM, Equiv.apply_symm_apply]
  exact Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul
    (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hγ) (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv ha)) hγ) hx

section Cell

variable (L : LocBessel k r) (w0 v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
  {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {μG μR νR : Measure (Mt k r)}

theorem PsiM_stab (hγ : γ ∈ UH (Hpk k r)) (hrel : IsRelStab L γ) {p : PairSp k r} (hp : InPair L p)
    {a : Mt k r} (ha : Matrix.of a ∈ RStab k r γ) {x : Mt k r} (hx : Matrix.of x ∈ UH (Hpk k r)) :
    PsiM L w0 v v' ξ ξ' γ (mStab γ (p, a), x) = PsiM L w0 v v' ξ ξ' γ (p, qG γ (x, Formalism.FourierDecayAlt.P.B7.invM a)) := by
  have hq := qG_inv_mem hγ hx ha.1.1
  rw [PsiM_eq L w0 v v' ξ ξ' hγ hp hq, qG_invM]
  show PsiM L w0 v v' ξ ξ' γ (stabAct γ (Matrix.of a) p, x) = _
  rw [PsiM_eq L w0 v v' ξ ξ' hγ (inPair_stab L hp ha) hx, Psi_stab L w0 v v' ξ ξ' hγ hrel hp ha x]

theorem lint_cell (hγ : γ ∈ UH (Hpk k r)) (hrel : IsRelStab L γ) (hμG : IsHaarOn (UH (Hpk k r)) μG)
    (hμR : IsHaarOn (RStab k r γ) μR) (hinv : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μR μR)
    (hQ : PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR)
    {p : PairSp k r} (hp : InPair L p) :
    ∫⁻ a, ∫⁻ x, ‖PsiM L w0 v v' ξ ξ' γ (mStab γ (p, a), x)‖ₑ ∂νR ∂μR =
      ∫⁻ y, ‖Psi L w0 v v' ξ ξ' γ p y‖ₑ ∂μG := by
  haveI : SigmaFinite μR := hμR.1
  haveI : SigmaFinite νR := sigmaFinite_nuR hμG hμR hQ
  have hmeasP : Measurable (fun y : Mt k r => ‖PsiM L w0 v v' ξ ξ' γ (p, y)‖ₑ) :=
    ((sm_PsiM L w0 v v' ξ ξ' γ).measurable.comp measurable_prodMk_left).enorm
  have hmeasQ : Measurable (fun q : Mt k r × Mt k r => ‖PsiM L w0 v v' ξ ξ' γ (p, qG γ q)‖ₑ) :=
    hmeasP.comp (continuous_qG γ).measurable
  have hR : ∀ᵐ a ∂μR, Matrix.of a ∈ RStab k r γ := ae_iff.mpr hμR.2.2.1
  have hU := ae_uh_nuR hγ hμG hμR hQ
  calc ∫⁻ a, ∫⁻ x, ‖PsiM L w0 v v' ξ ξ' γ (mStab γ (p, a), x)‖ₑ ∂νR ∂μR
      = ∫⁻ a, ∫⁻ x, ‖PsiM L w0 v v' ξ ξ' γ (p, qG γ (x, Formalism.FourierDecayAlt.P.B7.invM a))‖ₑ ∂νR ∂μR := by
        refine lintegral_congr_ae (hR.mono (fun a ha => ?_))
        refine lintegral_congr_ae (hU.mono (fun x hx => ?_))
        dsimp only
        rw [PsiM_stab L w0 v v' ξ ξ' hγ hrel hp ha hx]
    _ = ∫⁻ a, ∫⁻ x, ‖PsiM L w0 v v' ξ ξ' γ (p, qG γ (x, a))‖ₑ ∂νR ∂μR :=
        hinv.lintegral_comp hmeasQ.lintegral_prod_left'
    _ = ∫⁻ x, ∫⁻ a, ‖PsiM L w0 v v' ξ ξ' γ (p, qG γ (x, a))‖ₑ ∂μR ∂νR :=
        lintegral_lintegral_swap (hmeasQ.comp measurable_swap).aemeasurable
    _ = ∫⁻ q, ‖PsiM L w0 v v' ξ ξ' γ (p, qG γ q)‖ₑ ∂(νR.prod μR) :=
        (lintegral_prod _ hmeasQ.aemeasurable).symm
    _ = ∫⁻ y, ‖PsiM L w0 v v' ξ ξ' γ (p, y)‖ₑ ∂μG := by
        rw [muG_eq_map hμR hQ, lintegral_map hmeasP (continuous_qG γ).measurable]
    _ = ∫⁻ y, ‖Psi L w0 v v' ξ ξ' γ p y‖ₑ ∂μG := by
        have hG : ∀ᵐ y ∂μG, Matrix.of y ∈ UH (Hpk k r) := ae_iff.mpr hμG.2.2.1
        refine lintegral_congr_ae (hG.mono (fun y hy => ?_))
        dsimp only
        rw [PsiM_eq L w0 v v' ξ ξ' hγ hp hy]

theorem int_cell (hγ : γ ∈ UH (Hpk k r)) (hrel : IsRelStab L γ) (hμG : IsHaarOn (UH (Hpk k r)) μG)
    (hμR : IsHaarOn (RStab k r γ) μR) (hinv : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μR μR)
    (hQ : PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR)
    {p : PairSp k r} (hp : InPair L p) (hint : Integrable (fun y => Psi L w0 v v' ξ ξ' γ p y) μG) :
    ∫ a, ∫ x, PsiM L w0 v v' ξ ξ' γ (mStab γ (p, a), x) ∂νR ∂μR = ∫ y, Psi L w0 v v' ξ ξ' γ p y ∂μG := by
  haveI : SigmaFinite μR := hμR.1
  haveI : SigmaFinite νR := sigmaFinite_nuR hμG hμR hQ
  have hsmP : StronglyMeasurable (fun y : Mt k r => PsiM L w0 v v' ξ ξ' γ (p, y)) :=
    (sm_PsiM L w0 v v' ξ ξ' γ).comp_measurable measurable_prodMk_left
  have hsmQ : StronglyMeasurable (fun q : Mt k r × Mt k r => PsiM L w0 v v' ξ ξ' γ (p, qG γ q)) :=
    hsmP.comp_measurable (continuous_qG γ).measurable
  have hR : ∀ᵐ a ∂μR, Matrix.of a ∈ RStab k r γ := ae_iff.mpr hμR.2.2.1
  have hU := ae_uh_nuR hγ hμG hμR hQ
  have hG : ∀ᵐ y ∂μG, Matrix.of y ∈ UH (Hpk k r) := ae_iff.mpr hμG.2.2.1
  have hGeq : (fun y => PsiM L w0 v v' ξ ξ' γ (p, y)) =ᵐ[μG] fun y => Psi L w0 v v' ξ ξ' γ p y :=
    hG.mono (fun y hy => PsiM_eq L w0 v v' ξ ξ' hγ hp hy)
  have hintP : Integrable (fun y => PsiM L w0 v v' ξ ξ' γ (p, y)) μG := hint.congr hGeq.symm
  have hμ := muG_eq_map hμR hQ
  have hintQ : Integrable (fun q : Mt k r × Mt k r => PsiM L w0 v v' ξ ξ' γ (p, qG γ q)) (νR.prod μR) := by
    rw [hμ] at hintP
    exact (integrable_map_measure hsmP.aestronglyMeasurable (continuous_qG γ).measurable.aemeasurable).mp hintP
  have hsmA : StronglyMeasurable (fun a => ∫ x, PsiM L w0 v v' ξ ξ' γ (p, qG γ (x, a)) ∂νR) :=
    hsmQ.integral_prod_left
  calc ∫ a, ∫ x, PsiM L w0 v v' ξ ξ' γ (mStab γ (p, a), x) ∂νR ∂μR
      = ∫ a, ∫ x, PsiM L w0 v v' ξ ξ' γ (p, qG γ (x, Formalism.FourierDecayAlt.P.B7.invM a)) ∂νR ∂μR := by
        refine integral_congr_ae (hR.mono (fun a ha => ?_))
        refine integral_congr_ae (hU.mono (fun x hx => ?_))
        dsimp only
        rw [PsiM_stab L w0 v v' ξ ξ' hγ hrel hp ha hx]
    _ = ∫ a, ∫ x, PsiM L w0 v v' ξ ξ' γ (p, qG γ (x, a)) ∂νR ∂μR := by
        have h := integral_map (μ := μR) hinv.measurable.aemeasurable
          (f := fun a => ∫ x, PsiM L w0 v v' ξ ξ' γ (p, qG γ (x, a)) ∂νR)
          (by rw [hinv.map_eq]; exact hsmA.aestronglyMeasurable)
        rw [hinv.map_eq] at h
        exact h.symm
    _ = ∫ x, ∫ a, PsiM L w0 v v' ξ ξ' γ (p, qG γ (x, a)) ∂μR ∂νR :=
        integral_integral_swap hintQ.swap
    _ = ∫ q, PsiM L w0 v v' ξ ξ' γ (p, qG γ q) ∂(νR.prod μR) := (integral_prod _ hintQ).symm
    _ = ∫ y, PsiM L w0 v v' ξ ξ' γ (p, y) ∂μG := by
        rw [hμ, integral_map (continuous_qG γ).measurable.aemeasurable hsmP.aestronglyMeasurable]
    _ = ∫ y, Psi L w0 v v' ξ ξ' γ p y ∂μG := integral_congr_ae hGeq

end Cell

end Formalism.MainNotions.S.Pv.AmpDDPf
end
end

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

attribute [local instance] Formalism.FourierDecayAlt.P.B7.properFD

theorem pairMaj_nonneg (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (b : ℝ) (p : PairSp k r) :
    0 ≤ Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b p :=
  Real.rpow_nonneg (Formalism.FourierDecayAlt.P.S3dx6.gN_nonneg _) _

theorem amp_core' (L : LocBessel k r) {μG : Measure (Mt k r)} (hμG : IsHaarOn (UH (Hpk k r)) μG) {d : ℝ}
    (hd : 0 < d)
    (hSch : ∀ v w v' w' : L.Hs,
      Integrable (fun x : Mt k r => ⟪w, L.σ (Matrix.of x) v⟫_ℂ * star ⟪w', L.σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, L.σ (Matrix.of x) v⟫_ℂ * star ⟪w', L.σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ))
    (hNI : Formalism.FourierDecayAlt.ThreeDimData.NormInv) {w0 : L.Hs} (hw1 : ⟪w0, w0⟫_ℂ = 1) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq)
    {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r)) (hrel : IsRelStab L γ)
    {μR νR : Measure (Mt k r)} {ν : Measure (PairSp k r)} (hμR : IsHaarOn (RStab k r γ) μR)
    (hOQ : IsOrbQuot L γ μR ν)
    (hQ : PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR)
    (hinv : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μR μR)
    {a b C1 C2 : ℝ} (hb : 0 ≤ b) (hab : b ≤ a)
    (hIG : Integrable (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (b - a)) μG)
    (hpm : Integrable (Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b) ν)
    {v v' : L.Hs}
    (hbe1 : ∀ t ∈ UH (Hpk k r), Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π L.σ L.μW L.μN (L.σ t w0) v =
      (innerSL ℂ (l v)).smulRight (l (L.σ t w0)))
    (hbe2 : ∀ t ∈ UH (Hpk k r), Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' L.σ L.μW' L.μN (L.σ t w0) v' =
      (innerSL ℂ (l' v')).smulRight (l' (L.σ t w0)))
    (hC1 : ∀ g ∈ UH (Hpk k r), ‖⟪v, L.σ g w0⟫_ℂ‖ ≤ C1 * Formalism.FourierDecayAlt.B.gN g ^ (-a))
    (hC2 : ∀ g ∈ UH (Hpk k r), ‖⟪v', L.σ g w0⟫_ℂ‖ ≤ C2 * Formalism.FourierDecayAlt.B.gN g ^ (-a))
    (ξ : L.Wp) (ξ' : L.Wq) :
    (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • ampJ νR 1 (fun g => l (L.σ g w0)) (fun g => l' (L.σ g w0)) γ =
      ((d : ℂ)⁻¹) • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ') γ ν := by
  have hσR : SigmaFinite μR := hμR.1
  have hσνR : SigmaFinite νR := sigmaFinite_nuR hμG hμR hQ
  have hσν : SigmaFinite ν := sigmaFinite_nu L hγ hμR hOQ hNI hpm
  have hσW : SigmaFinite L.μW := L.hμW.1.1
  have hσW' : SigmaFinite L.μW' := L.hμW'.1.1
  have hWi := mp_inv_W_sk L.hz.1 L.hz.2 L.hμW.1
  have hWi' := mp_inv_W_sk L.hz'.1 L.hz'.2 L.hμW'.1
  have hNi : MeasurePreserving Formalism.FourierDecayAlt.P.B7.invM L.μN L.μN :=
    ⟨hinv.measurable, map_inv_haarLieN L.κN⟩
  have hWae : ∀ᵐ x ∂L.μW, Matrix.of x ∈ UWset k r L.z := ae_mem_sk L.hμW.1
  have hWae' : ∀ᵐ x ∂L.μW', Matrix.of x ∈ UWset k r L.z' := ae_mem_sk L.hμW'.1
  have hNae : ∀ᵐ x ∂L.μN, Matrix.of x ∈ Nset k r := ae_mem_haarLieN L.κN
  have hsm : StronglyMeasurable (fun q : (PairSp k r × Mt k r) × Mt k r =>
      PsiM L w0 v v' ξ ξ' γ (mStab γ q.1, q.2)) :=
    (sm_PsiM L w0 v v' ξ ξ' γ).comp_measurable
      (((measurable_mStab γ).comp measurable_fst).prodMk measurable_snd)
  have hF : Integrable (fun q : (PairSp k r × Mt k r) × Mt k r =>
      PsiM L w0 v v' ξ ξ' γ (mStab γ q.1, q.2)) ((ν.prod μR).prod νR) := by
    refine ⟨hsm.aestronglyMeasurable, ?_⟩
    have hmeas : Measurable (fun q : (PairSp k r × Mt k r) × Mt k r =>
        ‖PsiM L w0 v v' ξ ξ' γ (mStab γ q.1, q.2)‖ₑ) := hsm.measurable.enorm
    have hmeas2 : Measurable (fun pa : PairSp k r × Mt k r =>
        ∫⁻ x, ‖PsiM L w0 v v' ξ ξ' γ (mStab γ pa, x)‖ₑ ∂νR) :=
      hmeas.lintegral_prod_right'
    show ∫⁻ q, ‖PsiM L w0 v v' ξ ξ' γ (mStab γ q.1, q.2)‖ₑ ∂((ν.prod μR).prod νR) < ⊤
    calc ∫⁻ q, ‖PsiM L w0 v v' ξ ξ' γ (mStab γ q.1, q.2)‖ₑ ∂((ν.prod μR).prod νR)
        = ∫⁻ pa, ∫⁻ x, ‖PsiM L w0 v v' ξ ξ' γ (mStab γ pa, x)‖ₑ ∂νR ∂(ν.prod μR) :=
          lintegral_prod _ hmeas.aemeasurable
      _ = ∫⁻ p, ∫⁻ a, ∫⁻ x, ‖PsiM L w0 v v' ξ ξ' γ (mStab γ (p, a), x)‖ₑ ∂νR ∂μR ∂ν :=
          lintegral_prod _ hmeas2.aemeasurable
      _ = ∫⁻ p, ∫⁻ y, ‖Psi L w0 v v' ξ ξ' γ p y‖ₑ ∂μG ∂ν := by
          refine lintegral_congr_ae ((ae_inPair_nu L hμR hOQ).mono fun p hp => ?_)
          exact lint_cell L w0 v v' ξ ξ' hγ hrel hμG hμR hinv hQ hp
      _ ≤ ∫⁻ p, ENNReal.ofReal ((‖ξ‖ * ‖ξ'‖ * (|C1| * |C2|) *
            ∫ x, Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (b - a) ∂μG) *
              Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b p) ∂ν := by
          refine lintegral_mono_ae ((ae_inPair_nu L hμR hOQ).mono fun p hp => ?_)
          exact lint_G_bound L hμG hNI hb hab hIG w0 v v' ξ ξ' hC1 hC2 hγ hp
      _ < ⊤ := (hpm.const_mul _).lintegral_lt_top
  have hmap := pairMeas_eq_map L hμR hOQ
  have hL : ∀ᵐ x ∂νR, (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) •
      (innerSL ℂ (l' (L.σ (Matrix.of x) w0))).smulRight (l (L.σ (γ * Matrix.of x) w0)) =
      ∫ pa, PsiM L w0 v v' ξ ξ' γ (mStab γ pa, x) ∂(ν.prod μR) := by
    filter_upwards [ae_uh_nuR hγ hμG hμR hQ, hF.prod_left_ae] with x hx hix
    have hgx : γ * Matrix.of x ∈ UH (Hpk k r) := WeylGroupFacts.uh_mul hγ hx
    have hsmx : StronglyMeasurable (fun q : PairSp k r => PsiM L w0 v v' ξ ξ' γ (q, x)) :=
      (sm_PsiM L w0 v v' ξ ξ' γ).comp_measurable (measurable_id.prodMk measurable_const)
    have hPM : (fun q => Psi L w0 v v' ξ ξ' γ q x) =ᵐ[pairMeas L]
        (fun q => PsiM L w0 v v' ξ ξ' γ (q, x)) :=
      (ae_inPair_pair L).mono fun q hq => (PsiM_eq L w0 v v' ξ ξ' hγ hq hx).symm
    have hintM : Integrable (fun q : PairSp k r => PsiM L w0 v v' ξ ξ' γ (q, x)) (pairMeas L) := by
      rw [hmap]
      exact (integrable_map_measure hsmx.aestronglyMeasurable (measurable_mStab γ).aemeasurable).2 hix
    rw [← pair_split L hWi hWi' hNi hWae hWae' hNae w0 v v' ξ ξ' l l' hx hgx (hbe1 _ hgx)
      (hbe2 _ hx) (hintM.congr hPM.symm), integral_congr_ae hPM, hmap,
      integral_map (measurable_mStab γ).aemeasurable hsmx.aestronglyMeasurable]
  have hsch : ∀ᵐ p ∂ν, ∫ a, ∫ x, PsiM L w0 v v' ξ ξ' γ (mStab γ (p, a), x) ∂νR ∂μR =
      ((d : ℂ)⁻¹) • besselIntg L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ') γ p := by
    filter_upwards [ae_inPair_nu L hμR hOQ] with p hp
    have hs := schur_step L hμG hd hSch hw1 v v' ξ ξ' hγ hp
    rw [int_cell L w0 v v' ξ ξ' hγ hrel hμG hμR hinv hQ hp hs.1, hs.2]
  calc (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) •
        ampJ νR 1 (fun g => l (L.σ g w0)) (fun g => l' (L.σ g w0)) γ
      = ∫ x, (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) •
          (innerSL ℂ (l' (L.σ (Matrix.of x) w0))).smulRight (l (L.σ (γ * Matrix.of x) w0)) ∂νR := by
        rw [integral_smul]
        simp [ampJ]
    _ = ∫ x, ∫ pa, PsiM L w0 v v' ξ ξ' γ (mStab γ pa, x) ∂(ν.prod μR) ∂νR := integral_congr_ae hL
    _ = ∫ pa, ∫ x, PsiM L w0 v v' ξ ξ' γ (mStab γ pa, x) ∂νR ∂(ν.prod μR) :=
        (integral_integral_swap (f := fun pa x => PsiM L w0 v v' ξ ξ' γ (mStab γ pa, x)) hF).symm
    _ = ∫ p, ∫ a, ∫ x, PsiM L w0 v v' ξ ξ' γ (mStab γ (p, a), x) ∂νR ∂μR ∂ν :=
        integral_prod _ hF.integral_prod_left
    _ = ∫ p, ((d : ℂ)⁻¹) • besselIntg L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ') γ p ∂ν :=
        integral_congr_ae hsch
    _ = ((d : ℂ)⁻¹) • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ') γ ν := by
        rw [integral_smul]
        rfl

theorem amp_core (L : LocBessel k r) {μG : Measure (Mt k r)} (hμG : IsHaarOn (UH (Hpk k r)) μG) {d : ℝ}
    (hd : 0 < d)
    (hSch : ∀ v w v' w' : L.Hs,
      Integrable (fun x : Mt k r => ⟪w, L.σ (Matrix.of x) v⟫_ℂ * star ⟪w', L.σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, L.σ (Matrix.of x) v⟫_ℂ * star ⟪w', L.σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ))
    (hNI : Formalism.FourierDecayAlt.ThreeDimData.NormInv) {w0 : L.Hs} (hw1 : ⟪w0, w0⟫_ℂ = 1) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq)
    (hl : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0, ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0,
      Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π L.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x))
    (hl' : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0, ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0,
      Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' L.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x))
    {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r)) (hrel : IsRelStab L γ)
    {μR νR : Measure (Mt k r)} {ν : Measure (PairSp k r)} (hμR : IsHaarOn (RStab k r γ) μR)
    (hOQ : IsOrbQuot L γ μR ν)
    (hQ : PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR)
    (hinv : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μR μR)
    {a b C1 C2 : ℝ} (hb : 0 ≤ b) (hab : b ≤ a)
    (hIG : Integrable (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (b - a)) μG)
    (hpm : Integrable (Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b) ν)
    {v v' : L.Hs} (hv : v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0) (hv' : v' ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0)
    (hC1 : ∀ g ∈ UH (Hpk k r), ‖⟪v, L.σ g w0⟫_ℂ‖ ≤ C1 * Formalism.FourierDecayAlt.B.gN g ^ (-a))
    (hC2 : ∀ g ∈ UH (Hpk k r), ‖⟪v', L.σ g w0⟫_ℂ‖ ≤ C2 * Formalism.FourierDecayAlt.B.gN g ^ (-a))
    (ξ : L.Wp) (ξ' : L.Wq) :
    (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • ampJ νR 1 (fun g => l (L.σ g w0)) (fun g => l' (L.σ g w0)) γ =
      ((d : ℂ)⁻¹) • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ') γ ν := by
  exact amp_core' L hμG hd hSch hNI hw1 l l' hγ hrel hμR hOQ hQ hinv hb hab hIG hpm
    (fun t ht => hl _ (Submodule.subset_span ⟨t, ht, rfl⟩) v hv)
    (fun t ht => hl' _ (Submodule.subset_span ⟨t, ht, rfl⟩) v' hv') hC1 hC2 ξ ξ'

end Formalism.MainNotions.S.Pv.AmpDDPf
