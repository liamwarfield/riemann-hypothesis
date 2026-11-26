module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiffQuotientBesselMapTendsto
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentEqLebesgue
public import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataBothAmplitudeSides
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataBothAmplitudeSides
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.Side

theorem urep_irred_of_ds {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}
    (h : IsDSHpk k r ε lam σ) : IsURepOn (GG k r) σ ∧ IsIrredOn (GG k r) σ := by
  obtain ⟨P, ⟨⟨hP, hH⟩, -⟩, -, -, ⟨⟨h1, hm⟩, hn, hc⟩, hi, -⟩ := h
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hPi : P * P⁻¹ = 1 := mul_nonsing_inv _ hd
  have hiP : P⁻¹ * P = 1 := nonsing_inv_mul _ hd
  have mem : ∀ g, g ∈ GG k r ↔ P * g * P⁻¹ ∈ UJset ε := uHConj _ ε _ P hd hH
  have back : ∀ g : Mat k r, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    calc P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hiP]; simp
  have forth : ∀ g : Mat k r, P * (P⁻¹ * g * P) * P⁻¹ = g := fun g => by
    calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hPi]; simp
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · simpa [hiP] using h1
  · intro a ha b hb
    have := hm _ ((mem a).1 ha) _ ((mem b).1 hb)
    have e : P * a * P⁻¹ * (P * b * P⁻¹) = P * (a * b) * P⁻¹ := by
      calc P * a * P⁻¹ * (P * b * P⁻¹) = P * a * (P⁻¹ * P) * b * P⁻¹ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hiP]; simp only [Matrix.mul_assoc, Matrix.one_mul]
    simpa only [e, back] using this
  · intro g hg v
    have := hn _ ((mem g).1 hg) v
    simpa only [back] using this
  · intro v
    have hcont : Continuous fun g : Mat k r => P * g * P⁻¹ :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have := (hc v).comp hcont.continuousOn (s := GG k r) (fun g hg => (mem g).1 hg)
    refine this.congr fun g _ => ?_
    simp only [Function.comp, back]
  · intro S hS hst
    refine hi S hS fun g hg v hv => hst _ ((mem _).2 ?_) v hv
    rw [forth]; exact hg

theorem isHaarOn_smul {k r : ℕ} {S : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn S μ) {c : ℝ}
    (hc : 0 < c) : IsHaarOn S (ENNReal.ofReal c • μ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : ENNReal.ofReal c • μ = c.toNNReal • μ := rfl
    rw [this]; infer_instance
  · intro h0
    rcases Measure.ennreal_smul_eq_zero.1 h0 with h | h
    · exact (ENNReal.ofReal_pos.2 hc).ne' h
    · exact h2 h
  · rw [Measure.smul_apply, h3, smul_zero]
  · intro s hs
    rw [Measure.map_smul, h4 s hs]
    have hcm : Continuous (fun x : Mt k r => Matrix.of.symm (s * Matrix.of x)) :=
      continuous_const.matrix_mul (continuous_id (X := Mat k r))
    exact hcm.measurable.aemeasurable

theorem oneSide_of_bessel {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    {σ : Mat k r → (H →L[ℂ] H)} {z : Fin (2 * r + k + 1) → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)} {u : Fin k → ℝ}
    {s : ℂ} {μG μW μN νS : Measure (Mt k r)} {B : H → Wp} {v : H} {c : ℝ}
    (hσ : IsURepOn (GG k r) σ) (hz : inWb k r z) (hT : 0 < Tz k r z) (hπ : IsHCTypeW k r z u π)
    (hG : IsHaarOn (GG k r) μG) (hW : IsHaarOn (UWset k r z) μW) (hW1 : μW Set.univ = 1)
    (hN : IsHaarOn (Nset k r) μN) (hq : IsQuotMeas μG (muS μW μN) νS)
    (hB : IsBesselMapSm z (psi k r z s) σ π B) (hv : IsSmoothVec σ v) (hc : 0 < c)
    (hl : l2SG νS (fun g => B (σ g v)) = ENNReal.ofReal (c * Module.finrank ℂ Wp)) :
    OneSide z π (psi k r z s) μG μW μN νS (fun g => B (σ g v)) c := by
  have := FiniteDimensional.complete ℂ Wp
  obtain ⟨hnt, hu, hi⟩ := (GlobalTheory.Amp.Schur.type_irred_and_avg k r z π hz hT).1 u hπ
  refine ⟨hz, hT, hnt, hu, hi, hG, hW, hW1, hN, hq, fun n hn => (psiChar k r z s hz n hn).2, ?_, ?_, hc, hl⟩
  · intro h hh m hm g hg
    have hdet : IsUnit (Hpk k r).det :=
      Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1
    have hhm : h * m ∈ GG k r := (uHGroup _ _ hdet).2.1 h hh.1 m hm.1
    have hs : IsSmoothVec σ (σ g v) := ((GlobalTheory.T.smooth_vectors_dense_invariant k r σ v hσ).2.2.2.1 v hv).1 g hg
    have := hB.2.2.1 h hh m hm (σ g v) hs
    show B (σ (h * m * g) v) = _
    rw [hσ.1.2 _ hhm _ hg]
    exact this
  · exact (GlobalTheory.T.diffQuotient_besselMap_tendsto k r σ z _ π B v 0 hσ hB hv (by simp [InLieHpk])).2.1

theorem both_sides : ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) lam (A : LocS W), 0 < θ → 0 < D.host.v → HypTT D w w' → GoodW D τ w w' θ W → GoodS D lam A → IsURepOn (GG D.R.k D.R.rS) A.σ ∧ IsIrredOn (GG D.R.k D.R.rS) A.σ ∧ W.μN = ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • lebN D.R.k D.R.rS ∧ OneSide W.z W.π (psiS D W.z) W.μG W.μW W.μN W.νS A.Φ A.cN ∧ OneSide W.z' W.π' (psiS D W.z') W.μG W.μW' W.μN W.νS' A.Φ' A.cN := by
  intro D τ w w' θ W lam A hθ hv hTT hW hA
  obtain ⟨c1, c2, z1, z2, t1, t2, hG, w1, w1', w2, w2', hN, q1, q2⟩ := hW
  obtain ⟨-, hds, b1, b2, hsm, -, -, hc, l1, l2, -⟩ := hA
  obtain ⟨hu, hi⟩ := urep_irred_of_ds hds
  have hpos : 0 < (2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ := by positivity
  have hμ : W.μN = ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ *
      2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • lebN D.R.k D.R.rS := by
    have e : haarLie (Nset D.R.k D.R.rS) (kapN D θ) = kapN D θ • haarLie (Nset D.R.k D.R.rS) 1 := by
      unfold haarLie; rw [one_smul]
    rw [hN, e, GlobalTheory.T.haar_lie_nilpotent_eq_lebesgue, smul_smul, ENNReal.ofReal_mul hpos.le, ENNReal.ofReal_pow (by norm_num)]
    simp [kapN]
  have hNH : IsHaarOn (Nset D.R.k D.R.rS) W.μN := by
    rw [hμ]; exact isHaarOn_smul (GlobalTheory.T.flagUnipotentLebesgueMeasure_isHaarOn _ _) (by positivity)
  have hT1 : 0 < Tz D.R.k D.R.rS W.z := by
    rw [t1]; unfold Tr; exact_mod_cast hTT.1.pos
  have hT2 : 0 < Tz D.R.k D.R.rS W.z' := by
    rw [t2]; unfold Tr; exact_mod_cast hTT.2.1.pos
  exact ⟨hu, hi, hμ, oneSide_of_bessel hu z1 hT1 c1 hG w1 w1' hNH q1 b1 hsm hc l1,
    oneSide_of_bessel hu z2 hT2 c2 hG w2 w2' hNH q2 b2 hsm hc l2⟩

end GlobalTheory.Amp.Side
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataBothAmplitudeSidesStatement
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_data_both_amplitude_sides : ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) lam (A : LocS W), 0 < θ → 0 < D.host.v → HypTT D w w' → GoodW D τ w w' θ W → GoodS D lam A → IsURepOn (GG D.R.k D.R.rS) A.σ ∧ IsIrredOn (GG D.R.k D.R.rS) A.σ ∧ W.μN = ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • lebN D.R.k D.R.rS ∧ OneSide W.z W.π (psiS D W.z) W.μG W.μW W.μN W.νS A.Φ A.cN ∧ OneSide W.z' W.π' (psiS D W.z') W.μG W.μW' W.μN W.νS' A.Φ' A.cN := by
  first | exact @GlobalTheory.Amp.Side.both_sides | exact GlobalTheory.Amp.Side.both_sides | (intros; apply GlobalTheory.Amp.Side.both_sides <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellDataSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellDataSupport
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellOrbInt

theorem ae_of_weil {X A : Type} [MeasurableSpace X] [MeasurableSpace A]
    (P ν : Measure X) (μ : Measure A) (act : A → X → X) (S : Set X) (hS : MeasurableSet S)
    (hP : ∀ᵐ x ∂P, x ∈ S) (hμ : μ ≠ 0)
    (hW : ∀ f : X → ENNReal, Measurable f → ∫⁻ x, f x ∂P = ∫⁻ x, (∫⁻ a, f (act a x) ∂μ) ∂ν)
    (hact : ∀ᵐ a ∂μ, ∀ x, act a x ∈ S → x ∈ S) : ∀ᵐ x ∂ν, x ∈ S := by
  classical
  have h := hW (Sᶜ.indicator 1) (measurable_one.indicator hS.compl)
  have h0 : ∫⁻ x, Sᶜ.indicator (1 : X → ENNReal) x ∂P = 0 := by
    rw [lintegral_indicator_one hS.compl]; exact hP
  have h1 : ∀ x, Sᶜ.indicator (fun _ => μ Set.univ) x ≤ ∫⁻ a, Sᶜ.indicator (1 : X → ENNReal) (act a x) ∂μ := by
    intro x
    by_cases hx : x ∈ S
    · simp [hx]
    · have : ∫⁻ a, Sᶜ.indicator (1 : X → ENNReal) (act a x) ∂μ = ∫⁻ _, 1 ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hact] with a ha
        have : act a x ∉ S := fun h => hx (ha x h)
        simp [this]
      rw [this, lintegral_const]
      simp [hx]
  have h2 := lintegral_mono (μ := ν) h1
  rw [← h, h0, lintegral_indicator_const hS.compl, nonpos_iff_eq_zero] at h2
  rcases mul_eq_zero.1 h2 with h2 | h2
  · exact absurd (Measure.measure_univ_eq_zero.1 h2) hμ
  · exact h2

variable {k r : ℕ}

theorem ae_mem_N (κ : ℝ≥0∞) : ∀ᵐ y ∂(haarLie (Nset k r) κ), Matrix.of y ∈ Nset k r := by
  unfold haarLie
  apply Measure.ae_smul_measure
  have hu : Continuous fun x : lieE (Nset k r) => unrealify (m := 2 * r + k + 1) x.1 := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [unrealify, Complex.mk_eq_add_mul_I]
    fun_prop
  have h : AEMeasurable (fun x : lieE (Nset k r) =>
      (fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j : Mt k r)) volume := by
    have hc : Continuous (fun x : lieE (Nset k r) =>
        (fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j : Mt k r)) :=
      GlobalTheory.Amp.NLie.cont_exp.comp hu
    exact hc.measurable.aemeasurable
  have hcl : IsClosed {y : Mt k r | Matrix.of y ∈ Nset k r} := (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r).closed
  rw [ae_map_iff h hcl.measurableSet]
  exact Filter.Eventually.of_forall fun x => GlobalTheory.Amp.NLie.exp_mem (GlobalTheory.Amp.NLie.mem_lieE x.2)

def pairSet (L : LocBessel k r) : Set (PairSp k r) :=
  {p | Matrix.of p.1.1 ∈ UWset k r L.z ∧ Matrix.of p.1.2 ∈ Nset k r ∧ Matrix.of p.2.1 ∈ UWset k r L.z' ∧
    Matrix.of p.2.2 ∈ Nset k r}

theorem closed_pairSet (L : LocBessel k r) : IsClosed (pairSet L) := by
  have hWc := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r L.z).closed
  have hWc' := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r L.z').closed
  have hNc := (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r).closed
  exact (hWc.preimage continuous_fst.fst).inter ((hNc.preimage continuous_fst.snd).inter
    ((hWc'.preimage continuous_snd.fst).inter (hNc.preimage continuous_snd.snd)))

theorem meas_pairSet (L : LocBessel k r) : MeasurableSet (pairSet L) := by
  haveI : BorelSpace (PairSp k r) := Prod.borelSpace
  exact (closed_pairSet L).measurableSet

theorem ae_pairMeas (L : LocBessel k r) : ∀ᵐ p ∂(pairMeas L), p ∈ pairSet L := by
  have : SFinite L.μN := by unfold LocBessel.μN haarLie; infer_instance
  have : SigmaFinite L.μW := L.hμW.1.1
  have : SigmaFinite L.μW' := L.hμW'.1.1
  have aN : ∀ᵐ y ∂L.μN, Matrix.of y ∈ Nset k r := ae_mem_N _
  have aW : ∀ᵐ y ∂L.μW, Matrix.of y ∈ UWset k r L.z := by rw [ae_iff]; exact L.hμW.1.2.2.1
  have aW' : ∀ᵐ y ∂L.μW', Matrix.of y ∈ UWset k r L.z' := by rw [ae_iff]; exact L.hμW'.1.2.2.1
  have b1 := (Measure.quasiMeasurePreserving_fst (μ := L.μW) (ν := L.μN)).ae aW
  have b2 := (Measure.quasiMeasurePreserving_snd (μ := L.μW) (ν := L.μN)).ae aN
  have c1 := (Measure.quasiMeasurePreserving_fst (μ := L.μW') (ν := L.μN)).ae aW'
  have c2 := (Measure.quasiMeasurePreserving_snd (μ := L.μW') (ν := L.μN)).ae aN
  have d1 := (Measure.quasiMeasurePreserving_fst (μ := L.μW.prod L.μN) (ν := L.μW'.prod L.μN)).ae (b1.and b2)
  have d2 := (Measure.quasiMeasurePreserving_snd (μ := L.μW.prod L.μN) (ν := L.μW'.prod L.μN)).ae (c1.and c2)
  unfold pairMeas
  filter_upwards [d1, d2] with p hp hq
  exact ⟨hp.1, hp.2, hq.1, hq.2⟩

theorem mem_N_of_mul {a x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ Nset k r)
    (h : a * x ∈ Nset k r) : x ∈ Nset k r := by
  have hN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have := hN.mul_mem _ (hN.inv_mem a ha) _ h
  rwa [Matrix.nonsing_inv_mul_cancel_left _ _ (hN.unit a ha)] at this

theorem ae_quot (L : LocBessel k r) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {μR : Measure (Mt k r)} {ν : Measure (PairSp k r)} (hR : IsHaarOn (RStab k r γ) μR)
    (hQ : IsOrbQuot L γ μR ν) : ∀ᵐ p ∂ν, p ∈ pairSet L := by
  refine ae_of_weil (pairMeas L) ν μR (fun x p => stabAct γ (Matrix.of x) p) _ (meas_pairSet L) (ae_pairMeas L)
    hR.2.1 hQ ?_
  have aR : ∀ᵐ y ∂μR, Matrix.of y ∈ RStab k r γ := by rw [ae_iff]; exact hR.2.2.1
  filter_upwards [aR] with a ha p hp
  exact ⟨hp.1, mem_N_of_mul ha.1 hp.2.1, hp.2.2.1, mem_N_of_mul ha.2 hp.2.2.2⟩

theorem point_mem (L : LocBessel k r) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hγ : γ ∈ UH (Hpk k r)) {p : PairSp k r} (hp : p ∈ pairSet L) :
    (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of p.2.2 * Matrix.of p.2.1 ∈ UH (Hpk k r) := by
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  exact hG.mul_mem _ (hG.mul_mem _ (hG.mul_mem _ (hG.mul_mem _ (hG.inv_mem _ hp.1.1) _ (hG.inv_mem _ hp.2.1.1)) _ hγ)
    _ hp.2.2.2.1) _ hp.2.2.1.1

theorem continuous_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    Continuous fun x : Mt k r => psi k r z c (Matrix.of x) := by
  unfold psi
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_const.mul (Formalism.FourierDecayAlt.P.B7.continuous_ell z)))))

theorem norm_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ‖psi k r z c g‖ = 1 := by
  unfold psi
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem contOn_intg (L : LocBessel k r) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hγ : γ ∈ UH (Hpk k r)) {F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)}
    (hF : ContinuousOn F (UH (Hpk k r))) : ContinuousOn (besselIntg L F γ) (pairSet L) := by
  set S := pairSet L with hS
  have hc : ContinuousOn L.π (UWset k r L.z) :=
    continuousOn_clm_apply.mpr (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_cont L.hz.2 (u := L.u) L.hπ)
  have hc' : ContinuousOn L.π' (UWset k r L.z') :=
    continuousOn_clm_apply.mpr (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_cont L.hz'.2 (u := L.u') L.hπ')
  have hxi : Continuous fun p : PairSp k r =>
      psi k r L.z L.c (Matrix.of p.1.2) * star (psi k r L.z' L.c (Matrix.of p.2.2)) :=
    ((continuous_psi L.z L.c).comp continuous_fst.snd).mul ((continuous_psi L.z' L.c).comp continuous_snd.snd).star
  have hπ : ContinuousOn (fun p : PairSp k r => L.π (Matrix.of p.1.1)) S :=
    hc.comp (continuous_fst.fst).continuousOn (fun p hp => hp.1)
  have hinv1 : ContinuousOn (fun p : PairSp k r => (Matrix.of p.1.1 : Formalism.FourierDecayAlt.B.Mat k r)⁻¹) S :=
    (Formalism.FourierDecayAlt.P.B6.inv_continuousOn k r).comp (continuous_fst.fst).continuousOn (fun p hp => hp.1.1)
  have hinv2 : ContinuousOn (fun p : PairSp k r => (Matrix.of p.1.2 : Formalism.FourierDecayAlt.B.Mat k r)⁻¹) S :=
    (Formalism.FourierDecayAlt.P.B6.inv_continuousOn k r).comp (continuous_fst.snd).continuousOn (fun p hp => hp.2.1.1)
  have hinv3 : ContinuousOn (fun p : PairSp k r => (Matrix.of p.2.1 : Formalism.FourierDecayAlt.B.Mat k r)⁻¹) S :=
    (Formalism.FourierDecayAlt.P.B6.inv_continuousOn k r).comp (continuous_snd.fst).continuousOn (fun p hp => hp.2.2.1.1)
  have hπ' : ContinuousOn (fun p : PairSp k r => L.π' (Matrix.of p.2.1 : Formalism.FourierDecayAlt.B.Mat k r)⁻¹) S :=
    hc'.comp hinv3 (fun p hp => (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hp.2.2.1).1)
  have hc4 : ContinuousOn (fun p : PairSp k r => (Matrix.of p.2.2 : Formalism.FourierDecayAlt.B.Mat k r)) S :=
    (continuous_snd.snd).continuousOn
  have hc5 : ContinuousOn (fun p : PairSp k r => (Matrix.of p.2.1 : Formalism.FourierDecayAlt.B.Mat k r)) S :=
    (continuous_snd.fst).continuousOn
  have hsgs : ContinuousOn (fun p : PairSp k r =>
      (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of p.2.2 * Matrix.of p.2.1) S :=
    ((((hinv1.mul hinv2).mul continuousOn_const).mul hc4).mul hc5)
  have hFs := hF.comp hsgs (fun p hp => point_mem L hγ hp)
  unfold besselIntg
  exact hxi.continuousOn.smul (hπ.clm_comp (hFs.clm_comp hπ'))

theorem norm_intg_le (L : LocBessel k r) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)) {p : PairSp k r}
    (hp : p ∈ pairSet L) : ‖besselIntg L F γ p‖ ≤
      ‖F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of p.2.2 * Matrix.of p.2.1)‖ := by
  have hu := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary L.hz.2 (u := L.u) L.hπ _ hp.1
  have hu' := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary L.hz'.2 (u := L.u') L.hπ' _ (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hp.2.2.1).1
  unfold besselIntg
  rw [norm_smul, norm_mul, norm_star, norm_psi, norm_psi, one_mul, one_mul]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun w => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hu, ← hu' w]
  exact ContinuousLinearMap.le_opNorm _ _

theorem coefF_eq (L : LocBessel k r) (v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    coefF L v v' ξ ξ' g = ⟪v, L.σ g v'⟫_ℂ • (innerSL ℂ ξ').smulRight ξ := by
  ext w
  simp only [coefF, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply]
  rw [smul_comm]

theorem orbInt_integrable : Hyps → ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r)) (ν : Measure (PairSp k r)), GapAtLeast L.ε L.lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → L.κN ≠ ⊤ → CellData L μG γ μR νR ν → (∀ᵐ p ∂ν, Matrix.of p.1.1 ∈ UWset k r L.z ∧ Matrix.of p.1.2 ∈ Nset k r ∧ Matrix.of p.2.1 ∈ UWset k r L.z' ∧ Matrix.of p.2.2 ∈ Nset k r) ∧ ∀ b : ℝ, 0 ≤ b → b ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 → Integrable (pairMaj γ b) ν → ∀ v v' : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v → PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v' → ∀ (ξ : L.Wp) (ξ' : L.Wq), Integrable (besselIntg L (coefF L v v' ξ ξ') γ) ν := by
  intro H k r L h μG γ μR νR ν hgap hok _ hC
  obtain ⟨hγ, -, -, -, hR, hQ, -⟩ := hC
  have hae := ae_quot L hR hQ
  refine ⟨hae, fun b _ hb hint v v' hv hv' ξ ξ' => ?_⟩
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  have hsm := H.1.2.2.1 k r L.ε L.lam L.Hs L.σ L.hlam hσ v' hv'
  obtain ⟨C, Ws, -, hdec⟩ := H.1.2.1 k r L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hok v hv
  have hd := hdec v' hsm
  generalize C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) L.σ W v'‖).sum = A at hd
  have hF : ContinuousOn (coefF L v v' ξ ξ') (UH (Hpk k r)) := by
    have e : coefF L v v' ξ ξ' = fun g => ⟪v, L.σ g v'⟫_ℂ • (innerSL ℂ ξ').smulRight ξ :=
      funext (coefF_eq L v v' ξ ξ')
    rw [e]
    exact (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const (Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hσ v')).smul continuousOn_const
  haveI : BorelSpace (PairSp k r) := Prod.borelSpace
  have hm : AEStronglyMeasurable (besselIntg L (coefF L v v' ξ ξ') γ) ν := by
    have := (contOn_intg L hγ hF).aestronglyMeasurable (μ := ν) (meas_pairSet L)
    rwa [Measure.restrict_eq_self_of_ae_mem hae] at this
  refine (hint.const_mul (|A| * ‖(innerSL ℂ ξ').smulRight ξ‖)).mono' hm ?_
  filter_upwards [hae] with p hp
  refine (norm_intg_le L γ _ hp).trans ?_
  have hx := point_mem L hγ hp
  unfold pairMaj
  set x := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of p.2.2 * Matrix.of p.2.1
  have h1 : 1 ≤ Formalism.FourierDecayAlt.B.gN x := PI.PolynomialProperness.GN.gN_ge_one hx
  have h2 : Formalism.FourierDecayAlt.B.gN x ^ (1 - Formalism.FourierDecayAlt.ThreeDimData.aOf r h) ≤ Formalism.FourierDecayAlt.B.gN x ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  have h3 : ‖⟪v, L.σ x v'⟫_ℂ‖ ≤ |A| * Formalism.FourierDecayAlt.B.gN x ^ (-b) :=
    (hd x hx).trans ((mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)).trans
      (mul_le_mul_of_nonneg_left h2 (abs_nonneg A)))
  rw [coefF_eq, norm_smul, mul_right_comm]
  exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)

end GlobalTheory.CellOrbInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellDataSupportStatement
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_data_support : Hyps → ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r)) (ν : Measure (PairSp k r)), GapAtLeast L.ε L.lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → L.κN ≠ ⊤ → CellData L μG γ μR νR ν → (∀ᵐ p ∂ν, Matrix.of p.1.1 ∈ UWset k r L.z ∧ Matrix.of p.1.2 ∈ Nset k r ∧ Matrix.of p.2.1 ∈ UWset k r L.z' ∧ Matrix.of p.2.2 ∈ Nset k r) ∧ ∀ b : ℝ, 0 ≤ b → b ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 → Integrable (pairMaj γ b) ν → ∀ v v' : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v → PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v' → ∀ (ξ : L.Wp) (ξ' : L.Wq), Integrable (besselIntg L (coefF L v v' ξ ξ') γ) ν := by
  first | exact @GlobalTheory.CellOrbInt.orbInt_integrable | exact GlobalTheory.CellOrbInt.orbInt_integrable | (intros; apply GlobalTheory.CellOrbInt.orbInt_integrable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueRootCoordinatesMapBesselTorusConj
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueRootCoordinatesMapBesselTorusConj
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory.ThA.TorusJac

variable {k r : ℕ}

noncomputable def dT (k r : ℕ) (α : ℂ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then α ^ (r - i.val) else if i.val ≤ r + k then 1 else ((star α) ^ (i.val - (r + k)))⁻¹

theorem aT_eq (α : ℂ) : aT k r α = Matrix.diagonal (dT k r α) := rfl

theorem dT_mul (α β : ℂ) (i : Fin (2 * r + k + 1)) : dT k r α i * dT k r β i = dT k r (α * β) i := by
  unfold dT
  split_ifs
  · rw [mul_pow]
  · simp
  · rw [star_mul', mul_pow, mul_inv]

theorem dT_one (i : Fin (2 * r + k + 1)) : dT k r 1 i = 1 := by
  unfold dT
  split_ifs <;> simp

theorem aT_mul (α β : ℂ) : aT k r α * aT k r β = aT k r (α * β) := by
  rw [aT_eq, aT_eq, aT_eq, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact dT_mul α β i

theorem aT_one : aT k r 1 = 1 := by
  rw [aT_eq, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact dT_one i

theorem aT_inv {α : ℂ} (h : α ≠ 0) : (aT k r α)⁻¹ = aT k r α⁻¹ :=
  Matrix.inv_eq_right_inv (by rw [aT_mul, mul_inv_cancel₀ h, aT_one])

theorem aT_unit {α : ℂ} (h : α ≠ 0) : IsUnit (aT k r α).det :=
  Matrix.isUnit_det_of_right_inverse (B := aT k r α⁻¹) (by rw [aT_mul, mul_inv_cancel₀ h, aT_one])

theorem aT_real (t : ℝ) : aT k r (t : ℂ) = B.aDil k r t := by
  unfold aT B.aDil
  congr 1
  funext i
  split_ifs <;> simp

theorem aT_mem {α : ℂ} (h : α ≠ 0) : aT k r α ∈ UH (Hpk k r) := by
  show (aT k r α)ᴴ * Hpk k r * aT k r α = Hpk k r
  rw [aT_eq, Matrix.diagonal_conjTranspose]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hs : star α ≠ 0 := star_ne_zero.2 h
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, Pi.star_apply]
  by_cases h1 : i.val < r ∧ i.val + j.val = 2 * r + k
  · rw [if_pos h1]
    unfold dT
    rw [if_pos h1.1, if_neg (by omega), if_neg (by omega), show j.val - (r + k) = r - i.val by omega, star_pow,
      mul_one, mul_inv_cancel₀ (pow_ne_zero _ hs)]
  rw [if_neg h1]
  by_cases h2 : j.val < r ∧ i.val + j.val = 2 * r + k
  · rw [if_pos h2]
    unfold dT
    rw [if_pos h2.1, if_neg (by omega), if_neg (by omega), show i.val - (r + k) = r - j.val by omega, star_inv₀,
      star_pow, star_star, mul_one, inv_mul_cancel₀ (pow_ne_zero _ h)]
  rw [if_neg h2]
  by_cases h3 : r ≤ i.val ∧ i.val ≤ r + k ∧ i = j
  · rw [if_pos h3]
    obtain ⟨h3, h4, rfl⟩ := h3
    unfold dT
    rw [if_neg (show ¬ i.val < r by omega), if_pos h4, star_one, one_mul, mul_one]
  rw [if_neg h3, mul_zero, zero_mul]

theorem conj_entry {α : ℂ} (h : α ≠ 0) (g : B.Mat k r) (i j : Fin (2 * r + k + 1))
    (hg : g i j = if i = j then 1 else 0) :
    (aT k r α * g * (aT k r α)⁻¹) i j = if i = j then 1 else 0 := by
  rw [aT_inv h, aT_eq, aT_eq, Matrix.mul_diagonal, Matrix.diagonal_mul, hg]
  split_ifs with e
  · subst e
    rw [mul_one, dT_mul, mul_inv_cancel₀ h, dT_one]
  · simp

theorem conj_mem {α : ℂ} (h : α ≠ 0) {n : B.Mat k r} (hn : n ∈ Nset k r) :
    aT k r α * n * (aT k r α)⁻¹ ∈ Nset k r := by
  have hG := Formalism.FourierDecayAlt.Final.closed_subgroup_general_linear k r
  obtain ⟨h1, h2, h3⟩ := hn
  refine ⟨hG.mul_mem _ (hG.mul_mem _ (aT_mem h) _ h1) _ (hG.inv_mem _ (aT_mem h)), fun a i hi => ?_,
    fun i j a b c => ?_⟩
  · exact conj_entry h n _ _ (h2 a i hi)
  · exact conj_entry h n _ _ (h3 i j a b c)

theorem contOn : ContinuousOn (aT k r) (Metric.sphere (0 : ℂ) 1) := by
  have : ContinuousOn (dT k r) (Metric.sphere (0 : ℂ) 1) := by
    refine continuousOn_pi.2 fun i => ?_
    unfold dT
    split_ifs
    · fun_prop
    · fun_prop
    · refine ContinuousOn.inv₀ (by fun_prop) fun x hx => pow_ne_zero _ (star_ne_zero.2 ?_)
      exact ne_zero_of_mem_unit_sphere ⟨x, hx⟩
  exact (Continuous.matrix_diagonal continuous_id).comp_continuousOn this

theorem circle_compact : IsCompact (aT k r '' Metric.sphere (0 : ℂ) 1) :=
  (isCompact_sphere _ _).image_of_continuousOn contOn

theorem circle_subgroup : B2.IsClosedSubgroup (aT k r '' Metric.sphere (0 : ℂ) 1) := by
  refine ⟨⟨1, by simp, aT_one⟩, ?_, ?_, ?_, circle_compact.isClosed⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    refine ⟨a * b, ?_, (aT_mul a b).symm⟩
    simp only [mem_sphere_zero_iff_norm] at *
    rw [norm_mul, ha, hb, mul_one]
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨a⁻¹, ?_, (aT_inv (ne_zero_of_mem_unit_sphere ⟨a, ha⟩)).symm⟩
    simp only [mem_sphere_zero_iff_norm] at *
    rw [norm_inv, ha, inv_one]
  · rintro _ ⟨a, ha, rfl⟩
    exact aT_unit (ne_zero_of_mem_unit_sphere ⟨a, ha⟩)

theorem conj_cont (a : B.Mat k r) : Continuous (conjM a : Mt k r → Mt k r) :=
  (continuous_const.matrix_mul (continuous_id (X := B.Mat k r))).matrix_mul continuous_const

theorem conj_conj (a b : B.Mat k r) : (conjM a : Mt k r → Mt k r) ∘ conjM b = conjM (a * b) := by
  funext x
  show (a * (b * Matrix.of x * b⁻¹) * a⁻¹ : B.Mat k r) = a * b * Matrix.of x * (a * b)⁻¹
  simp only [Matrix.mul_inv_rev, Matrix.mul_assoc]

theorem haar_map_conj (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Nset k r) μ) (α : ℂ) (h : α ≠ 0) :
    μ.map (conjM (aT k r α)) = ENNReal.ofReal ((‖α‖ ^ B.kap k r)⁻¹) • μ := by
  have hp : 0 < ‖α‖ := norm_pos_iff.2 h
  have hc : (‖α‖ : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hu : α / (‖α‖ : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, norm_norm, div_self hp.ne']
  have e : aT k r α = B.aDil k r ‖α‖ * aT k r (α / (‖α‖ : ℂ)) := by
    rw [← aT_real, aT_mul, mul_div_cancel₀ _ hc]
  have h1 : μ.map (conjM (aT k r (α / (‖α‖ : ℂ)))) = μ := by
    refine Formalism.FourierDecayAlt.Final.compact_conjugation k r _ _ μ (Formalism.FourierDecayAlt.Final.closed_subgroup_unipotent_radical k r) circle_subgroup circle_compact
      ?_ hμ _ ⟨_, hu, rfl⟩
    rintro _ ⟨a, ha, rfl⟩ u hu
    exact conj_mem (ne_zero_of_mem_unit_sphere ⟨a, ha⟩) hu
  rw [e, ← conj_conj, ← Measure.map_map (conj_cont _).measurable (conj_cont _).measurable, h1]
  exact Formalism.FourierDecayAlt.Final.dilation_jacobian_formula k r μ hμ _ hp

theorem muN_map_conj : ∀ (k r : ℕ) (α : ℂ), α ≠ 0 →
    (D.muN k r).map (conjM (aT k r α)) = ENNReal.ofReal ((‖α‖ ^ B.kap k r)⁻¹) • D.muN k r :=
  fun k r α h => haar_map_conj _ (Formalism.FourierDecayAlt.Final.d_muNHaar k r) α h

end GlobalTheory.ThA.TorusJac
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueRootCoordinatesMapBesselTorusConjStatement
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lebesgue_rootCoordinates_map_besselTorus_conj : ∀ (k r : ℕ) (α : ℂ), α ≠ 0 → (D.muN k r).map (conjM (aT k r α)) = ENNReal.ofReal ((‖α‖ ^ B.kap k r)⁻¹) • D.muN k r := by
  first | exact @GlobalTheory.ThA.TorusJac.muN_map_conj | exact GlobalTheory.ThA.TorusJac.muN_map_conj | (intros; apply GlobalTheory.ThA.TorusJac.muN_map_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOneSideOfGoodLocalData
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOneSideOfGoodLocalData
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.AmpSides

open Filter Topology GlobalTheory.CWDeriv

variable {k r : ℕ}

theorem cwCont_of {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp]
    {σ : Mat k r → (H →L[ℂ] H)} {Bm : H → Wp} (h : IsCWCont (k := k) (r := r) σ Bm) :
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) σ Bm := by
  have e : ∀ (w : List (Mat k r)) (v : H),
      dsigW (k := k) (r := r) σ w v = PI.UpqRep.dsigW (k := k) (r := r) σ w v := by
    intro w v
    induction w with
    | nil => rfl
    | cons X w ih => show dsig σ X _ = PI.UpqRep.dsig σ X _; rw [ih]; rfl
  unfold IsCWCont at h
  simp only [e] at h
  exact h

theorem continuousOn_orbit {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} (R : BranchingSupport.Rep k r)
    (hR : R.IsDS ε mu) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (Bm : R.H → V)
    (ha : ∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) (hs : ∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v)
    (hB : PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm) {v : R.H} (hv : v ∈ R.sm) :
    ContinuousOn (fun g => Bm (R.σ g v)) (GG k r) := by
  have hD : DerFacts R := fun X hX =>
    ⟨fun _ hv => ⟨DerivedAction.dsig_smooth hR.2 hX hv, DerivedAction.hasDerivAt_dsig hX hv⟩,
      fun _ hv _ hw => DerivedAction.dsig_skew hR.2 hX hv hw⟩
  have hsm := PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε mu R.H R.σ hR.2 v hv
  have h0 : (0 : R.H) ∈ R.sm := R.smSub.zero_mem
  have hB0 : Bm 0 = 0 := by simpa using hs 0 0 h0
  intro g hg
  have h1 := cw_tendsto hB (l := 𝓝[GG k r] g) (u := fun x => (1 : ℂ) • (R.σ x v - R.σ g v) - 0)
    (by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact sm_comb 1 (hsm x hx) (hsm g hg) h0)
    (by
      intro W hW
      have h2 : Tendsto _ (𝓝[GG k r] g) _ :=
        (smoothOnH_continuousOn (dsigW_orbit_smooth hR hD hv W hW) g hg).tendsto
      have hW0 : PI.UpqRep.dsigW (k := k) (r := r) R.σ W 0 = 0 := by
        have h := dsigW_comb hD W hW 0 h0 h0 h0
        simp only [zero_smul, zero_sub, neg_zero] at h
        rw [eq_neg_iff_add_eq_zero, ← two_smul ℂ] at h
        simpa using h
      rw [← tendsto_sub_nhds_zero_iff] at h2
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [dsigW_comb hD W hW 1 (hsm x hx) (hsm g hg) h0, hW0, one_smul, sub_zero])
  refine tendsto_sub_nhds_zero_iff.mp (h1.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [lin_comb ha hs 1 (hsm x hx) (hsm g hg) h0, hB0, one_smul, sub_zero]

theorem isHaarOn_smul {S : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn S μ) {x : ℝ} (hx : 0 < x) :
    IsHaarOn S (ENNReal.ofReal x • μ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, fun h0 => h2 ?_, by rw [Measure.smul_apply, h3, smul_zero], fun s hs => by
    rw [Measure.map_smul, h4 s hs]
    exact (BesselUnitaryEquiv.continuous_lmulM s).measurable.aemeasurable⟩
  · exact inferInstanceAs (SigmaFinite (x.toNNReal • μ))
  · have h1 := Measure.measure_univ_eq_zero.2 h0
    rw [Measure.smul_apply, smul_eq_mul] at h1
    exact Measure.measure_univ_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left (ENNReal.ofReal_pos.2 hx).ne')

theorem haarLie_eq (x : ℝ) :
    haarLie (Nset k r) (ENNReal.ofReal x) =
      ENNReal.ofReal (x * 2 ^ (r * (k + 1) + r * (r - 1))) • lebN k r := by
  have h := GlobalTheory.T.haar_lie_nilpotent_eq_lebesgue k r
  unfold haarLie at h ⊢
  rw [one_smul] at h
  rw [h, smul_smul, mul_comm x, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
    mul_comm (ENNReal.ofReal x)]
  simp

theorem oneSide_of {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}
    {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ} {π : Mat k r → (Wp →L[ℂ] Wp)} {c : ℂ}
    {μG μW νS : Measure (Mt k r)} {Bm : H → Wp} {v₀ : H} {cN x : ℝ} (hx : 0 < x)
    (hlam : IsHCParam lam) (hσ : IsDSHpk k r ε lam σ) (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hπ : IsHCTypeW k r z u π) (hG : IsHaarOn (GG k r) μG) (hW : IsHaarOn (UWset k r z) μW) (hW1 : μW Set.univ = 1)
    (hq : IsQuotMeas μG (muS μW (haarLie (Nset k r) (ENNReal.ofReal x))) νS)
    (hB : IsBesselMapSm z (psi k r z c) σ π Bm) (hv : v₀ ∈ smoothVecs (k := k) (r := r) σ) (hc : 0 < cN)
    (hl : l2SG νS (fun g => Bm (σ g v₀)) = ENNReal.ofReal (cN * Module.finrank ℂ Wp)) :
    OneSide z π (psi k r z c) μG μW (ENNReal.ofReal (x * 2 ^ (r * (k + 1) + r * (r - 1))) • lebN k r) νS
      (fun g => Bm (σ g v₀)) cN := by
  let R : BranchingSupport.Rep k r := ⟨H, σ⟩
  have hR : R.IsDS ε lam := ⟨hlam, hσ⟩
  obtain ⟨e1, e2, e3⟩ := (GlobalTheory.Amp.Schur.type_irred_and_avg k r z π hz hT).1 u hπ
  rw [haarLie_eq] at hq
  refine ⟨hz, hT, e1, e2, e3, hG, hW, hW1, isHaarOn_smul (GlobalTheory.T.flagUnipotentLebesgueMeasure_isHaarOn k r) (by positivity), hq,
    fun n _ => by unfold psi; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _, fun a ha m hm g hg => ?_,
    continuousOn_orbit R hR Bm hB.1 hB.2.1 (cwCont_of hB.2.2.2) hv, hc, hl⟩
  have ham : a * m ∈ GG k r := (PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r a ha.1).2.2 m hm.1
  have h1 := PI.UnitaryGroupMassFormula.CapelliEig.Hecke_multiplication k r ε lam H σ hσ _ ham g hg
  have h2 := PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε lam H σ hσ v₀ hv g hg
  show Bm (σ (a * m * g) v₀) = _
  rw [h1]
  exact hB.2.2.1 a ha m hm _ h2

theorem oneSide_of_good : ∀ (D : D7) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), 0 < D.host.v → 0 < θ → 0 < Tr D w → 0 < Tr D w' → GoodW D τ w w' θ W → GoodS D lam A → OneSide W.z W.π (psiS D W.z) W.μG W.μW (ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • lebN D.R.k D.R.rS) W.νS A.Φ A.cN ∧ OneSide W.z' W.π' (psiS D W.z') W.μG W.μW' (ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • lebN D.R.k D.R.rS) W.νS' A.Φ' A.cN := by
  intro D τ w w' θ W lam A hv hθ hT hT' hW hA
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14⟩ := hW
  obtain ⟨a1, a2, a3, a4, a5, -, -, a8, a9, a10, -⟩ := hA
  rw [w12] at w13 w14
  have hx : 0 < (2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ := by positivity
  exact ⟨oneSide_of hx a1 a2 w3 (w5 ▸ hT) w1 w7 w8 w9 w13 a3 a5 a8 a9,
    oneSide_of hx a1 a2 w4 (w6 ▸ hT') w2 w7 w10 w11 w14 a4 a5 a8 a10⟩

end GlobalTheory.AmpSides
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOneSideOfGoodLocalDataStatement
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitude_one_side_of_good_local_data : ∀ (D : D7) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), 0 < D.host.v → 0 < θ → 0 < Tr D w → 0 < Tr D w' → GoodW D τ w w' θ W → GoodS D lam A → OneSide W.z W.π (psiS D W.z) W.μG W.μW (ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • lebN D.R.k D.R.rS) W.νS A.Φ A.cN ∧ OneSide W.z' W.π' (psiS D W.z') W.μG W.μW' (ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • lebN D.R.k D.R.rS) W.νS' A.Φ' A.cN := by
  first | exact @GlobalTheory.AmpSides.oneSide_of_good | exact GlobalTheory.AmpSides.oneSide_of_good | (intros; apply GlobalTheory.AmpSides.oneSide_of_good <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExpInjectiveStrictUpperTriangular
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExpInjectiveStrictUpperTriangular
open Matrix Filter Topology

namespace GlobalTheory.ExpStrictUpper

theorem conj_diagonal_eq {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) (hX : ∀ i j, j ≤ i → X i j = 0)
    {τ : ℂ} (hτ : τ ≠ 0) :
    (Matrix.diagonal fun i : Fin m => (τ ^ (i : ℕ))⁻¹) * X *
      (Matrix.diagonal fun i : Fin m => τ ^ (i : ℕ)) =
      Matrix.of fun i j : Fin m => τ ^ ((j : ℕ) - (i : ℕ)) * X i j := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
  by_cases h : j ≤ i
  · simp [hX i j h]
  · have hij : (i : ℕ) ≤ (j : ℕ) := by
      have := Fin.lt_def.mp (not_le.mp h)
      omega
    have hp : τ ^ (j : ℕ) = τ ^ (i : ℕ) * τ ^ ((j : ℕ) - (i : ℕ)) := by
      rw [← pow_add, Nat.add_sub_cancel' hij]
    rw [hp]
    calc (τ ^ (i : ℕ))⁻¹ * X i j * (τ ^ (i : ℕ) * τ ^ ((j : ℕ) - (i : ℕ)))
        = ((τ ^ (i : ℕ))⁻¹ * τ ^ (i : ℕ)) * (τ ^ ((j : ℕ) - (i : ℕ)) * X i j) := by ring
      _ = τ ^ ((j : ℕ) - (i : ℕ)) * X i j := by
        rw [inv_mul_cancel₀ (pow_ne_zero _ hτ), one_mul]

theorem tendsto_scale {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) (hX : ∀ i j, j ≤ i → X i j = 0) :
    Tendsto (fun τ : ℂ => (Matrix.of fun i j : Fin m => τ ^ ((j : ℕ) - (i : ℕ)) * X i j))
      (𝓝 0) (𝓝 0) := by
  have hc : Continuous (fun τ : ℂ => (Matrix.of fun i j : Fin m => τ ^ ((j : ℕ) - (i : ℕ)) * X i j)) :=
    continuous_matrix fun i j => by
      simp only [Matrix.of_apply]
      exact (continuous_pow _).mul continuous_const
  have h0 : (Matrix.of fun i j : Fin m => (0 : ℂ) ^ ((j : ℕ) - (i : ℕ)) * X i j) = 0 := by
    ext i j
    rw [Matrix.of_apply, Matrix.zero_apply]
    by_cases h : j ≤ i
    · rw [hX i j h, mul_zero]
    · have hn : (j : ℕ) - (i : ℕ) ≠ 0 := by
        have := Fin.lt_def.mp (not_le.mp h)
        omega
      rw [zero_pow hn, zero_mul]
  simpa only [h0] using hc.tendsto 0

theorem exp_inj_strictUpper : ∀ (m : ℕ) (X Y : Matrix (Fin m) (Fin m) ℂ),
    (∀ i j, j ≤ i → X i j = 0) → (∀ i j, j ≤ i → Y i j = 0) →
    NormedSpace.exp X = NormedSpace.exp Y → X = Y := by
  intro m X Y hX hY hXY
  obtain ⟨S, hS, hinj⟩ := (GlobalTheory.ExpBallNhds.exp_local_matrix (Fin m)).1
  have h1 : ∀ᶠ τ in 𝓝[≠] (0 : ℂ),
      (Matrix.of fun i j : Fin m => τ ^ ((j : ℕ) - (i : ℕ)) * X i j) ∈ S ∧
        (Matrix.of fun i j : Fin m => τ ^ ((j : ℕ) - (i : ℕ)) * Y i j) ∈ S :=
    nhdsWithin_le_nhds (((tendsto_scale X hX).eventually_mem hS).and
      ((tendsto_scale Y hY).eventually_mem hS))
  have h2 : ∀ᶠ τ in 𝓝[≠] (0 : ℂ), τ ≠ 0 := self_mem_nhdsWithin
  have hev := h1.and h2
  obtain ⟨τ, ⟨hxS, hyS⟩, hτ⟩ := hev.exists
  set D : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal fun i : Fin m => τ ^ (i : ℕ) with hD
  set E : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal fun i : Fin m => (τ ^ (i : ℕ))⁻¹ with hE
  have hDE : D * E = 1 := by
    rw [hD, hE, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (pow_ne_zero _ hτ)
  have hED : E * D = 1 := by
    rw [hD, hE, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (pow_ne_zero _ hτ)
  have hU : IsUnit D := ⟨⟨D, E, hDE, hED⟩, rfl⟩
  have hinv : D⁻¹ = E := Matrix.inv_eq_left_inv hED
  have hexp : ∀ Z : Matrix (Fin m) (Fin m) ℂ,
      NormedSpace.exp (E * Z * D) = E * NormedSpace.exp Z * D := by
    intro Z
    rw [← hinv]
    exact Matrix.exp_conj' D Z hU
  have hxS' : E * X * D ∈ S := by
    rw [hE, hD, conj_diagonal_eq X hX hτ]
    exact hxS
  have hyS' : E * Y * D ∈ S := by
    rw [hE, hD, conj_diagonal_eq Y hY hτ]
    exact hyS
  have key : E * X * D = E * Y * D :=
    hinj hxS' hyS' (by rw [hexp, hexp, hXY])
  calc X = (D * E) * X * (D * E) := by rw [hDE, one_mul, mul_one]
    _ = D * (E * X * D) * E := by simp only [mul_assoc]
    _ = D * (E * Y * D) * E := by rw [key]
    _ = (D * E) * Y * (D * E) := by simp only [mul_assoc]
    _ = Y := by rw [hDE, one_mul, mul_one]

end GlobalTheory.ExpStrictUpper
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExpInjectiveStrictUpperTriangularStatement
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exp_injective_strictUpperTriangular : ∀ (m : ℕ) (X Y : Matrix (Fin m) (Fin m) ℂ), (∀ i j, j ≤ i → X i j = 0) → (∀ i j, j ≤ i → Y i j = 0) → NormedSpace.exp X = NormedSpace.exp Y → X = Y := by
  first | exact @GlobalTheory.ExpStrictUpper.exp_inj_strictUpper | exact GlobalTheory.ExpStrictUpper.exp_inj_strictUpper | (intros; apply GlobalTheory.ExpStrictUpper.exp_inj_strictUpper <;> assumption)
end
end
