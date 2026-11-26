module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellConv
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformBesselConstant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerDilationWeightsDualIsotropicVector

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableBesselPairMajorantMulRight
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableBesselPairMajorantMulRight
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

noncomputable section

namespace GlobalTheory.CellMajTransfer


open Formalism.FourierDecayAlt in
theorem pt_bound {k r : ℕ} (L : LocBessel k r) {γ₁ a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hγ : γ₁ ∈ UH (Hpk k r)) (ha : a ∈ UH (Hpk k r)) {b : ℝ} (hb : 0 ≤ b) {K : ℝ} (hK1 : 1 ≤ K)
    (hK : ∀ h ∈ UWset k r L.z', B.gN h ≤ K)
    {p : PairSp k r} (hp : p ∈ GlobalTheory.CellOrbInt.pairSet L) {h'' : Mt k r} (hh : Matrix.of h'' ∈ UWset k r L.z') :
    pairMaj (γ₁ * a) b p ≤ (K * K * B.gN a⁻¹) ^ b * pairMaj γ₁ b (p.1, (h'', conjM a p.2.2)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  set X : B.Mat k r := (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2 : B.Mat k r)⁻¹ * (γ₁ * a) *
    Matrix.of p.2.2 * Matrix.of p.2.1 with hX
  set Y : B.Mat k r := (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ₁ *
    (a * Matrix.of p.2.2 * a⁻¹) * Matrix.of h'' with hY
  have hXv : pairMaj (γ₁ * a) b p = B.gN X ^ (-b) := rfl
  have hYv : pairMaj γ₁ b (p.1, (h'', conjM a p.2.2)) = B.gN Y ^ (-b) := rfl
  rw [hXv, hYv]
  have hh'u : IsUnit (Matrix.of p.2.1 : B.Mat k r).det := (P.unitary_group_closed k r).unit _ h3.1
  have eY : Y = X * ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹ * Matrix.of h'') := by
    simp only [hX, hY, Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hh'u]
  have hai : a⁻¹ ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv ha
  have hA1 : 1 ≤ B.gN a⁻¹ := P.BetaSesquilinearity.gN_ge_one hai
  have hYG : Y ∈ B.GV k r := by
    rw [hY]
    exact Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul
      (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv h1.1) (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv h2.1)) hγ)
      (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul ha h4.1) hai)) hh.1
  have hY1 : 1 ≤ B.gN Y := P.BetaSesquilinearity.gN_ge_one hYG
  have hX0 : 0 ≤ B.gN X := P.B6.gN_nonneg X
  have hle : B.gN Y ≤ (K * K * B.gN a⁻¹) * B.gN X := by
    rw [eY]
    have e1 := P.B6.gN_mul_le X ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹ * Matrix.of h'')
    have e2 := P.B6.gN_mul_le ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹) (Matrix.of h'')
    have e3 := P.B6.gN_mul_le ((Matrix.of p.2.1 : B.Mat k r)⁻¹) a⁻¹
    have k1 := hK _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv h3)
    have k2 := hK _ hh
    have n1 := P.B6.gN_nonneg ((Matrix.of p.2.1 : B.Mat k r)⁻¹)
    have n2 := P.B6.gN_nonneg (a⁻¹)
    have n3 := P.B6.gN_nonneg (Matrix.of h'' : B.Mat k r)
    have n4 := P.B6.gN_nonneg ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹)
    have n5 := P.B6.gN_nonneg ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹ * Matrix.of h'')
    have s1 : B.gN ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹ * Matrix.of h'') ≤ K * K * B.gN a⁻¹ := by
      calc _ ≤ B.gN ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹) * B.gN (Matrix.of h'' : B.Mat k r) := e2
        _ ≤ (B.gN ((Matrix.of p.2.1 : B.Mat k r)⁻¹) * B.gN a⁻¹) * K :=
            mul_le_mul e3 k2 n3 (mul_nonneg n1 n2)
        _ ≤ (K * B.gN a⁻¹) * K := by gcongr
        _ = K * K * B.gN a⁻¹ := by ring
    calc _ ≤ B.gN X * B.gN ((Matrix.of p.2.1 : B.Mat k r)⁻¹ * a⁻¹ * Matrix.of h'') := e1
      _ ≤ B.gN X * (K * K * B.gN a⁻¹) := mul_le_mul_of_nonneg_left s1 hX0
      _ = (K * K * B.gN a⁻¹) * B.gN X := by ring
  set c : ℝ := K * K * B.gN a⁻¹ with hc
  have hc1 : 1 ≤ c := by rw [hc]; nlinarith
  have hc0 : 0 < c := by linarith
  have hcb : c ^ b * c ^ (-b) = 1 := by
    rw [← Real.rpow_add hc0, add_neg_cancel, Real.rpow_zero]
  have hmono : (c * B.gN X) ^ (-b) ≤ B.gN Y ^ (-b) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hle (by linarith)
  calc B.gN X ^ (-b) = c ^ b * (c * B.gN X) ^ (-b) := by
        rw [Real.mul_rpow hc0.le hX0, ← mul_assoc, hcb, one_mul]
    _ ≤ c ^ b * B.gN Y ^ (-b) := mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg hc0.le _)

end GlobalTheory.CellMajTransfer

namespace GlobalTheory.CellMajTransfer


open Formalism.FourierDecayAlt in
theorem inner_eq {k r : ℕ} (L : LocBessel k r) (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) {C : ℝ≥0∞}
    (hmap : L.μN.map (conjM a) = C • L.μN) {f : PairSp k r → ℝ≥0∞} (hfm : Measurable f) (x : Mt k r × Mt k r) :
    ∫⁻ y, ∫⁻ h'', f (x, (h'', conjM a y.2)) ∂L.μW' ∂(L.μW'.prod L.μN) = C * ∫⁻ y, f (x, y) ∂(L.μW'.prod L.μN) := by
  have : SFinite L.μN := by unfold LocBessel.μN haarLie; infer_instance
  have : SigmaFinite L.μW' := L.hμW'.1.1
  have hconj : Measurable (conjM (k := k) (r := r) a) := by
    have : Continuous (conjM (k := k) (r := r) a) := by
      unfold conjM
      exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact this.measurable
  have hF : Measurable fun q : Mt k r × (Mt k r × Mt k r) => f (x, (q.1, conjM a q.2.2)) :=
    hfm.comp (measurable_const.prodMk (measurable_fst.prodMk (hconj.comp measurable_snd.snd)))
  have hG : Measurable fun y : Mt k r × Mt k r => ∫⁻ h'', f (x, (h'', conjM a y.2)) ∂L.μW' :=
    hF.lintegral_prod_left'
  have hH' : Measurable fun q : Mt k r × Mt k r => f (x, (q.1, q.2)) :=
    hfm.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
  have hH : Measurable fun n' : Mt k r => ∫⁻ h'', f (x, (h'', n')) ∂L.μW' := hH'.lintegral_prod_left'
  have hfx : Measurable fun y : Mt k r × Mt k r => f (x, y) := hfm.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_prod _ hG.aemeasurable, lintegral_prod _ hfx.aemeasurable]
  simp only [lintegral_const, L.hμW'.2, one_mul]
  have e1 : ∫⁻ n', ∫⁻ h'', f (x, (h'', conjM a n')) ∂L.μW' ∂L.μN =
      ∫⁻ n', ∫⁻ h'', f (x, (h'', n')) ∂L.μW' ∂(L.μN.map (conjM a)) := by
    rw [lintegral_map hH hconj]
  rw [e1, hmap, lintegral_smul_measure, smul_eq_mul]
  have hs := lintegral_lintegral_swap (μ := L.μW') (ν := L.μN) (f := fun h'' n' => f (x, (h'', n')))
    hH'.aemeasurable
  rw [hs, mul_one]


open Formalism.FourierDecayAlt in
theorem integrable_mul_right : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (γ₁ a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (b : ℝ) (C : ℝ≥0∞), 0 < L.κN → L.κN ≠ ⊤ → 0 ≤ b → γ₁ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → C ≠ ⊤ → L.μN.map (Formalism.QuantumDeterminants.conjM a) = C • L.μN → MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj γ₁ b) (Formalism.MainNotions.S.pairMeas L) → MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj (γ₁ * a) b) (Formalism.MainNotions.S.pairMeas L) := by
  intro k r L γ₁ a b C _hκ0 _hκ hb hγ ha hC hmap hint
  have : SFinite L.μN := by unfold LocBessel.μN haarLie; infer_instance
  have : SigmaFinite L.μW := L.hμW.1.1
  have : SigmaFinite L.μW' := L.hμW'.1.1
  obtain ⟨K, hK1, hK⟩ := P.Dx3.UW_bound L.z' L.hz'.1 L.hz'.2
  set c : ℝ := K * K * B.gN a⁻¹ with hc
  set f : PairSp k r → ℝ≥0∞ := fun p => ENNReal.ofReal (pairMaj γ₁ b p) with hfdef
  have hfm : Measurable f := ENNReal.measurable_ofReal.comp (GlobalTheory.CellMaj.meas_pairMaj γ₁ b)
  have hconj : Measurable (conjM (k := k) (r := r) a) := by
    have : Continuous (conjM (k := k) (r := r) a) := by
      unfold conjM
      exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact this.measurable
  set Φ : PairSp k r × Mt k r → PairSp k r := fun q => (q.1.1, (q.2, conjM a q.1.2.2)) with hΦdef
  have hΦ : Measurable Φ := measurable_fst.fst.prodMk (measurable_snd.prodMk (hconj.comp measurable_fst.snd.snd))
  have aW' : ∀ᵐ y ∂L.μW', Matrix.of y ∈ UWset k r L.z' := by rw [ae_iff]; exact L.hμW'.1.2.2.1
  have hP0 : ∀ p, 0 ≤ pairMaj (γ₁ * a) b p := fun p => Real.rpow_nonneg (P.B6.gN_nonneg _) _
  have hQ0 : ∀ p, 0 ≤ pairMaj γ₁ b p := fun p => Real.rpow_nonneg (P.B6.gN_nonneg _) _
  have hcb0 : 0 ≤ c ^ b := Real.rpow_nonneg (by rw [hc]; have := P.B6.gN_nonneg a⁻¹; positivity) _
  have step1 : ∀ᵐ p ∂(pairMeas L), ENNReal.ofReal (pairMaj (γ₁ * a) b p) ≤
      ∫⁻ h'', ENNReal.ofReal (c ^ b) * f (Φ (p, h'')) ∂L.μW' := by
    filter_upwards [GlobalTheory.CellOrbInt.ae_pairMeas L] with p hp
    calc ENNReal.ofReal (pairMaj (γ₁ * a) b p) = ∫⁻ _h'', ENNReal.ofReal (pairMaj (γ₁ * a) b p) ∂L.μW' := by
          rw [lintegral_const, L.hμW'.2, mul_one]
      _ ≤ _ := by
          refine lintegral_mono_ae ?_
          filter_upwards [aW'] with h'' hh
          rw [hfdef, ← ENNReal.ofReal_mul hcb0]
          exact ENNReal.ofReal_le_ofReal (pt_bound L hγ ha hb hK1 hK hp hh)
  have step2 : ∫⁻ p, ∫⁻ h'', f (Φ (p, h'')) ∂L.μW' ∂(pairMeas L) = C * ∫⁻ p, f p ∂(pairMeas L) := by
    have hm : Measurable fun p : PairSp k r => ∫⁻ h'', f (Φ (p, h'')) ∂L.μW' := (hfm.comp hΦ).lintegral_prod_right'
    unfold pairMeas
    rw [lintegral_prod _ hm.aemeasurable, lintegral_prod _ hfm.aemeasurable]
    rw [← lintegral_const_mul' _ _ hC]
    refine lintegral_congr fun x => ?_
    exact inner_eq L a hmap hfm x
  have hfin : ∫⁻ p, f p ∂(pairMeas L) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hQ0)).1 hint.2
  refine ⟨(GlobalTheory.CellMaj.meas_pairMaj (γ₁ * a) b).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hP0)]
  calc ∫⁻ p, ENNReal.ofReal (pairMaj (γ₁ * a) b p) ∂(pairMeas L)
      ≤ ∫⁻ p, ∫⁻ h'', ENNReal.ofReal (c ^ b) * f (Φ (p, h'')) ∂L.μW' ∂(pairMeas L) := lintegral_mono_ae step1
    _ = ENNReal.ofReal (c ^ b) * (C * ∫⁻ p, f p ∂(pairMeas L)) := by
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rw [step2]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top hC.lt_top hfin)

end GlobalTheory.CellMajTransfer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableBesselPairMajorantMulRightStatement
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_besselPairMajorant_mul_right : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (γ₁ a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (b : ℝ) (C : ℝ≥0∞), 0 < L.κN → L.κN ≠ ⊤ → 0 ≤ b → γ₁ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → C ≠ ⊤ → L.μN.map (Formalism.QuantumDeterminants.conjM a) = C • L.μN → MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj γ₁ b) (Formalism.MainNotions.S.pairMeas L) → MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj (γ₁ * a) b) (Formalism.MainNotions.S.pairMeas L) := by
  first | exact @GlobalTheory.CellMajTransfer.integrable_mul_right | exact GlobalTheory.CellMajTransfer.integrable_mul_right | (intros; apply GlobalTheory.CellMajTransfer.integrable_mul_right <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapConjUnipotentHaarEqSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapConjUnipotentHaarEqSmul
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
namespace GlobalTheory.NConjHaar

theorem map_conj_eq_smul : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r), 0 < L.κN → L.κN ≠ ⊤ → ∀ a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → (∀ n, n ∈ Formalism.QuantumDeterminants.Nset k r ↔ a * n * a⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r) → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ L.μN.map (Formalism.QuantumDeterminants.conjM a) = C • L.μN := by
  intro k r L h0 ht a ha hN
  have hμ := GlobalTheory.haarLie_isHaarOn_Nset k r L.κN h0 ht.lt_top
  have hu : IsUnit a.det := GlobalTheory.Amp.StabHaar.unit_of_GG ha
  have hmap := GlobalTheory.Amp.StabHaar.haar_conj (G := Formalism.QuantumDeterminants.Nset k r) (G' := Formalism.QuantumDeterminants.Nset k r) a hu hN hμ
  obtain ⟨c, c0, ct, hc⟩ := GlobalTheory.BesselPeriodCompare.haar_unique (Formalism.FourierDecayAlt.P.B2x2.closedN k r) hmap hμ
  exact ⟨c, ct, hc⟩

end GlobalTheory.NConjHaar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapConjUnipotentHaarEqSmulStatement
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_conj_unipotentHaar_eq_smul : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r), 0 < L.κN → L.κN ≠ ⊤ → ∀ a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → (∀ n, n ∈ Formalism.QuantumDeterminants.Nset k r ↔ a * n * a⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r) → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ L.μN.map (Formalism.QuantumDeterminants.conjM a) = C • L.μN := by
  first | exact @GlobalTheory.NConjHaar.map_conj_eq_smul | exact GlobalTheory.NConjHaar.map_conj_eq_smul | (intros; apply GlobalTheory.NConjHaar.map_conj_eq_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellQuotientNormalisesUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellQuotientNormalisesUnipotent
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

namespace GlobalTheory.BigConvLevi

open Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.BigCellHermitian

variable {k r : ℕ}

theorem hb_mul_self : Hb k * Hb k = 1 := by
  unfold Hb
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  split_ifs <;> norm_num

theorem isUnit_det_of_hb {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (h : μᴴ * Hb k * μ = Hb k) :
    IsUnit μ.det := by
  apply Matrix.isUnit_det_of_left_inverse (B := Hb k * μᴴ * Hb k)
  calc Hb k * μᴴ * Hb k * μ = Hb k * (μᴴ * Hb k * μ) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, hb_mul_self]

theorem conj_mem_of_levi (A B n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hAB : A * B = 1) (hA : A ∈ UH (Hpk k r)) (hB : B ∈ UH (Hpk k r))
    (hA1 : ∀ i j, ¬ mid k r j → A i j = if i = j then 1 else 0)
    (hB1 : ∀ i j, ¬ mid k r j → B i j = if i = j then 1 else 0)
    (hB3 : ∀ m j, mid k r j → ¬ mid k r m → B m j = 0)
    (hn : n ∈ Nset k r) : A * n * B ∈ Nset k r := by
  refine ⟨WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul hA hn.1) hB, ?_, ?_⟩
  · intro a i hai
    have hea : ¬ mid k r (eI k r a) := by
      have := a.isLt; simp only [mid, eI]; omega
    rw [Matrix.mul_apply, Finset.sum_eq_single (eI k r a)]
    · rw [hB1 _ _ hea, if_pos rfl, mul_one, Matrix.mul_apply, Finset.sum_eq_single (eI k r a)]
      · rw [hn.2.1 a (eI k r a) (by simp [eI]), if_pos rfl, mul_one, hA1 _ _ hea]
      · intro l _ hl
        by_cases hla : a.val ≤ l.val
        · rw [hn.2.1 a l hla, if_neg hl, mul_zero]
        · have hlm : ¬ mid k r l := by have := a.isLt; simp only [mid]; omega
          rw [hA1 i l hlm, if_neg (by rw [Fin.ext_iff]; omega), zero_mul]
      · simp
    · intro l _ hl
      rw [hB1 _ _ hea, if_neg hl, mul_zero]
    · simp
  · intro i j hj1 hj2 hi
    have hjm : mid k r j := ⟨hj1, hj2⟩
    rw [Matrix.mul_apply]
    have key : ∀ m, (A * n) i m * B m j = A i m * B m j := by
      intro m
      by_cases hm : mid k r m
      · congr 1
        rw [Matrix.mul_apply, Finset.sum_eq_single m]
        · rw [hn.2.2 m m hm.1 hm.2 hm.1, if_pos rfl, mul_one]
        · intro l _ hl
          by_cases hlr : r ≤ l.val
          · rw [hn.2.2 l m hm.1 hm.2 hlr, if_neg hl, mul_zero]
          · have hlm : ¬ mid k r l := by simp only [mid]; omega
            rw [hA1 i l hlm, if_neg (by rw [Fin.ext_iff]; omega), zero_mul]
        · simp
      · rw [hB3 m j hjm hm, mul_zero, mul_zero]
    rw [Finset.sum_congr rfl (fun m _ => key m), ← Matrix.mul_apply, hAB, Matrix.one_apply]

theorem cellQuot_props (c : Fin r → ℂ) (μ₁ μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hc : ∀ a, c a ≠ 0) (h₁ : μ₁ᴴ * Hb k * μ₁ = Hb k) (h : μᴴ * Hb k * μ = Hb k) :
    (bigCell k r c μ₁)⁻¹ * bigCell k r c μ ∈ UH (Hpk k r) ∧
    (∀ i j, ¬ mid k r j → ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ) i j = if i = j then 1 else 0) ∧
    (∀ m j, mid k r j → ¬ mid k r m → ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ) m j = 0) := by
  have hg₁ := big_cell_mem_holds k r c μ₁ hc h₁
  have hg := big_cell_mem_holds k r c μ hc h
  have u₁ := WeylGroupFacts.isUnit_of_uh hg₁
  have hμ₁ := isUnit_det_of_hb h₁
  refine ⟨WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hg₁) hg, ?_, ?_⟩
  · intro i j hj
    rw [Matrix.mul_apply, Finset.sum_congr rfl (fun l _ => by rw [bc_out_col c μ μ₁ l j hj]),
      ← Matrix.mul_apply, Matrix.nonsing_inv_mul _ u₁, Matrix.one_apply]
  · intro m j hj hm
    obtain ⟨t, rfl⟩ := mid_exists hj
    have e1 : (Pi.single (wI k r t) 1 : Fin (2 * r + k + 1) → ℂ) = jV k r (Pi.single t 1) := by
      funext i
      by_cases hi : mid k r i
      · obtain ⟨s, rfl⟩ := mid_exists hi
        rw [jV_wI]
        simp only [Pi.single_apply, wI_inj.eq_iff]
      · rw [jV_out _ hi, Pi.single_apply, if_neg (fun he : i = wI k r t => hi (he ▸ mid_wI t))]
    have col : ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ) m (wI k r t) =
        (((bigCell k r c μ₁)⁻¹ * bigCell k r c μ) *ᵥ Pi.single (wI k r t) 1) m := by
      rw [Matrix.mulVec_single_one]; rfl
    have back : ∀ v : Fin (k + 1) → ℂ,
        jV k r v = bigCell k r c μ₁ *ᵥ jV k r (μ₁⁻¹ *ᵥ v) := by
      intro v
      rw [bigCell_mulVec_jV, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hμ₁, Matrix.one_mulVec]
    rw [col, ← Matrix.mulVec_mulVec, e1, bigCell_mulVec_jV, back, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ u₁, Matrix.one_mulVec, jV_out _ hm]

theorem levi_conj_mem_iff : ∀ (k r : ℕ) (c : Fin r → ℂ) (μ₁ μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    (∀ a, c a ≠ 0) → μ₁ᴴ * Formalism.QuantumDeterminants.Hb k * μ₁ = Formalism.QuantumDeterminants.Hb k →
    μᴴ * Formalism.QuantumDeterminants.Hb k * μ = Formalism.QuantumDeterminants.Hb k →
    ∀ n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, n ∈ Formalism.QuantumDeterminants.Nset k r ↔
      (Formalism.QuantumDeterminants.bigCell k r c μ₁)⁻¹ * Formalism.QuantumDeterminants.bigCell k r c μ * n *
        ((Formalism.QuantumDeterminants.bigCell k r c μ₁)⁻¹ * Formalism.QuantumDeterminants.bigCell k r c μ)⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r := by
  intro k r c μ₁ μ hc h₁ h n
  have u₁ := WeylGroupFacts.isUnit_of_uh (big_cell_mem_holds k r c μ₁ hc h₁)
  have u := WeylGroupFacts.isUnit_of_uh (big_cell_mem_holds k r c μ hc h)
  obtain ⟨hA, hA1, hA3⟩ := cellQuot_props c μ₁ μ hc h₁ h
  obtain ⟨hB, hB1, hB3⟩ := cellQuot_props c μ μ₁ hc h h₁
  have hinv : ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ)⁻¹ = (bigCell k r c μ)⁻¹ * bigCell k r c μ₁ := by
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ u₁]
  have hAB : (bigCell k r c μ₁)⁻¹ * bigCell k r c μ * ((bigCell k r c μ)⁻¹ * bigCell k r c μ₁) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ u, Matrix.nonsing_inv_mul _ u₁]
  have hBA : (bigCell k r c μ)⁻¹ * bigCell k r c μ₁ * ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ u₁, Matrix.nonsing_inv_mul _ u]
  rw [hinv]
  constructor
  · exact conj_mem_of_levi _ _ n hAB hA hB hA1 hB1 hB3
  · intro hn'
    have := conj_mem_of_levi _ _ _ hBA hB hA hB1 hA1 hA3 hn'
    have e : (bigCell k r c μ)⁻¹ * bigCell k r c μ₁ *
        ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ * n * ((bigCell k r c μ)⁻¹ * bigCell k r c μ₁)) *
        ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ) = n := by
      calc _ = ((bigCell k r c μ)⁻¹ * bigCell k r c μ₁ * ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ)) * n *
            ((bigCell k r c μ)⁻¹ * bigCell k r c μ₁ * ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ)) := by
            simp only [Matrix.mul_assoc]
        _ = n := by rw [hBA, Matrix.one_mul, Matrix.mul_one]
    rwa [e] at this

end GlobalTheory.BigConvLevi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellQuotientNormalisesUnipotentStatement
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigCell_quotient_normalises_unipotent : ∀ (k r : ℕ) (c : Fin r → ℂ) (μ₁ μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) → μ₁ᴴ * Formalism.QuantumDeterminants.Hb k * μ₁ = Formalism.QuantumDeterminants.Hb k → μᴴ * Formalism.QuantumDeterminants.Hb k * μ = Formalism.QuantumDeterminants.Hb k → ∀ n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, n ∈ Formalism.QuantumDeterminants.Nset k r ↔ (Formalism.QuantumDeterminants.bigCell k r c μ₁)⁻¹ * Formalism.QuantumDeterminants.bigCell k r c μ * n * ((Formalism.QuantumDeterminants.bigCell k r c μ₁)⁻¹ * Formalism.QuantumDeterminants.bigCell k r c μ)⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r := by
  first | exact @GlobalTheory.BigConvLevi.levi_conj_mem_iff | exact GlobalTheory.BigConvLevi.levi_conj_mem_iff | (intros; apply GlobalTheory.BigConvLevi.levi_conj_mem_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairSpaceMajorantIntegrableBigCell
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

noncomputable section
namespace GlobalTheory.BigConv

theorem good_point (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (hk : 1 ≤ k) (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) :
    ∃ μ₁ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, μ₁ᴴ * Formalism.QuantumDeterminants.Hb k * μ₁ = Formalism.QuantumDeterminants.Hb k ∧
      0 < Formalism.QuantumDeterminants.Gf k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c μ₁) := by
  obtain ⟨μs, -, hμ⟩ := Formalism.FourierDecayAlt.P.SettingConstruction.sectionExists k r L.z L.z' hk L.hz.1 L.hz'.1 L.hz.2 L.hz'.2
  set τ := Formalism.QuantumDeterminants.Tz k r L.z * Formalism.QuantumDeterminants.Tz k r L.z' with hτ
  have hτ0 : 0 < τ := mul_pos L.hz.2 L.hz'.2
  set ζ : ℂ := ((τ + 1 : ℝ) : ℂ) with hζ
  have hn : τ < Complex.normSq ζ := by
    rw [hζ, Complex.normSq_ofReal]; nlinarith
  obtain ⟨hU, hzz⟩ := hμ ζ hn
  refine ⟨μs ζ, hU, ?_⟩
  have hmin := Formalism.QuantumDeterminants.big_cell_minors_holds k r L.z L.z' c (μs ζ) L.hz.1 L.hz'.1
  have hz := hmin.2.2 hc
  rw [Formalism.FourierDecayAlt.P.BigCellHermitian.herm_bigCell _ _ L.hz.1 L.hz'.1, hzz] at hz
  have hr := hmin.1 (Fin.last r)
  set P := Formalism.QuantumDeterminants.Dmin k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c (μs ζ)) ⟨r, by omega⟩ with hP
  have hP0 : P ≠ 0 := by
    have : P = ∏ a : Fin r with a.val < (Fin.last r).val, c a := hr
    rw [this]; exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
  have hlast : Formalism.QuantumDeterminants.Dmin k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c (μs ζ)) (Fin.last (r + 1)) = ζ * P := by
    unfold Formalism.QuantumDeterminants.zeta at hz
    rw [← hP] at hz
    have h2 := div_mul_cancel₀ (Formalism.QuantumDeterminants.Dmin k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c (μs ζ)) (Fin.last (r + 1))) hP0
    rw [hz] at h2
    exact h2.symm
  unfold Formalism.QuantumDeterminants.Gf
  rw [hlast, ← hP, Complex.normSq_mul]
  have h1 : 0 < Complex.normSq P := Complex.normSq_pos.2 hP0
  nlinarith


open Formalism.FourierDecayAlt in
theorem conv_good (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h)
    (hgap : GlobalTheory.CellAmp.GapCell k r h) (hκ : L.κN ≠ ⊤) (c : Fin r → ℂ)
    (μ₁ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hc : ∀ a, c a ≠ 0) (hμ₁ : μ₁ᴴ * Formalism.QuantumDeterminants.Hb k * μ₁ = Formalism.QuantumDeterminants.Hb k)
    (hG : 0 < Formalism.QuantumDeterminants.Gf k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c μ₁)) :
    ∃ b : ℝ, 0 ≤ b ∧ Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b ∧
      MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj (Formalism.QuantumDeterminants.bigCell k r c μ₁) b) (Formalism.MainNotions.S.pairMeas L) := by
  have hg := Formalism.QuantumDeterminants.big_cell_mem_holds k r c μ₁ hc hμ₁
  have hu := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg
  have hinv : (Formalism.QuantumDeterminants.bigCell k r c μ₁)⁻¹ * Formalism.QuantumDeterminants.bigCell k r c μ₁ = 1 := Matrix.nonsing_inv_mul _ hu
  have hZ := Formalism.QuantumDeterminants.bigCellZhat k r L.z L.z' c μ₁ L.hz.1 L.hz'.1
  set ζ := Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.bigCell k r c μ₁ *ᵥ L.z') L.z with hζ
  have hmono : Formalism.FourierDecayAlt.C2.IsMonomial (Formalism.QuantumDeterminants.Zhat k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c μ₁)) := by
    have hζ0 : ζ ≠ 0 := by
      intro h0
      have hmin := Formalism.QuantumDeterminants.big_cell_minors_holds k r L.z L.z' c μ₁ L.hz.1 L.hz'.1
      have hz := hmin.2.2 hc
      set P := Formalism.QuantumDeterminants.Dmin k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c μ₁) ⟨r, by omega⟩ with hP
      have hr := hmin.1 (Fin.last r)
      have hP0 : P ≠ 0 := by
        have : P = ∏ a : Fin r with a.val < (Fin.last r).val, c a := hr
        rw [this]; exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
      unfold Formalism.QuantumDeterminants.zeta at hz
      rw [← hP, ← hζ, h0, div_eq_zero_iff] at hz
      have hD : Formalism.QuantumDeterminants.Dmin k r L.z L.z' (Formalism.QuantumDeterminants.bigCell k r c μ₁) (Fin.last (r + 1)) = 0 :=
        hz.resolve_right hP0
      unfold Formalism.QuantumDeterminants.Gf at hG
      rw [hD, ← hP] at hG
      have : 0 ≤ Complex.normSq P := Complex.normSq_nonneg _
      have := mul_pos L.hz.2 L.hz'.2
      simp at hG
      nlinarith
    refine ⟨1, fun a => if h : a.val < r then c ⟨a.val, h⟩ else ζ, fun a => ?_, ?_⟩
    · dsimp only
      split_ifs
      · exact hc _
      · exact hζ0
    · refine hZ.trans ?_
      ext i j
      rw [Matrix.diagonal_apply]
      show _ = if i = j then _ else _
      by_cases h : i = j
      · rw [if_pos h, if_pos h, h]
      · rw [if_neg h, if_neg h]
  have hR := GlobalTheory.AmpNorm.rStab_bigCell c μ₁ hc hg
  have hcd := GlobalTheory.CellAmp.Model.cellData_open L 0 _ hg hinv hG hmono hR
  exact GlobalTheory.CellMaj.cellConv k r L h 0 _ _ _ _ hκ hok hgap hcd hmono

theorem bigConv : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ), Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GlobalTheory.CellAmp.GapCell k r h → L.κN ≠ ⊤ → 0 < L.κN → L.c ≠ 0 → ∀ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) → μᴴ * Formalism.QuantumDeterminants.Hb k * μ = Formalism.QuantumDeterminants.Hb k → ∃ b : ℝ, 0 ≤ b ∧ Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b ∧ MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj (Formalism.QuantumDeterminants.bigCell k r c μ) b) (Formalism.MainNotions.S.pairMeas L) := by
  intro k r L h hok hgap hκ hκ0 hcL c μ hc hμ
  obtain ⟨μ₁, hμ₁, hG⟩ := good_point k r L hok.1 c hc
  obtain ⟨b, hb0, hb1, hint⟩ := conv_good k r L h hok hgap hκ c μ₁ hc hμ₁ hG
  have hg₁ := Formalism.QuantumDeterminants.big_cell_mem_holds k r c μ₁ hc hμ₁
  have hg := Formalism.QuantumDeterminants.big_cell_mem_holds k r c μ hc hμ
  have hu₁ := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg₁
  set a := (Formalism.QuantumDeterminants.bigCell k r c μ₁)⁻¹ * Formalism.QuantumDeterminants.bigCell k r c μ with ha
  have haU : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hg₁) hg
  have hN := GlobalTheory.T.bigCell_quotient_normalises_unipotent k r c μ₁ μ hc hμ₁ hμ
  obtain ⟨C, hC, hmap⟩ := GlobalTheory.T.map_conj_unipotentHaar_eq_smul k r L hκ0 hκ a haU hN
  refine ⟨b, hb0, hb1, ?_⟩
  have e : Formalism.QuantumDeterminants.bigCell k r c μ₁ * a = Formalism.QuantumDeterminants.bigCell k r c μ := by
    rw [ha, Matrix.mul_nonsing_inv_cancel_left _ _ hu₁]
  rw [← e]
  exact GlobalTheory.T.integrable_besselPairMajorant_mul_right k r L _ a b C hκ0 hκ hb0 hg₁ haU hC hmap hint

end GlobalTheory.BigConv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairSpaceMajorantIntegrableBigCellStatement
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_space_majorant_integrable_big_cell : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ), Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GlobalTheory.CellAmp.GapCell k r h → L.κN ≠ ⊤ → 0 < L.κN → L.c ≠ 0 → ∀ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) → μᴴ * Formalism.QuantumDeterminants.Hb k * μ = Formalism.QuantumDeterminants.Hb k → ∃ b : ℝ, 0 ≤ b ∧ Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b ∧ MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj (Formalism.QuantumDeterminants.bigCell k r c μ) b) (Formalism.MainNotions.S.pairMeas L) := by
  first | exact @GlobalTheory.BigConv.bigConv | exact GlobalTheory.BigConv.bigConv | (intros; apply GlobalTheory.BigConv.bigConv <;> assumption)
end
