module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingDecay
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocOpAdj

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.EmbeddingMapApplyFirstBlock
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def NFHypL : Prop :=
  ∀ (k r : ℕ) (a : C.LPt) (hle : D.ptSize a ≤ r) (g' : B.Mat k (r - D.ptSize a)), g' ∈ B.GV k (r - D.ptSize a) →
    D.IsLocPt a (D.ptSize a) →
    levelZeroPointOver a hle g' ∈ B.GV k r ∧
    (∀ (a' : Fin r) (q : Fin (2 * r + k + 1)) (ha' : a'.val < D.ptSize a),
      PBG.xi0 (levelZeroPointOver a hle g') a' q =
        if hq : q.val < D.ptSize a then U.hMat (D.ptPerm a) (D.ptDiag a) ⟨a'.val, ha'⟩ ⟨q.val, hq⟩ else 0) ∧
    (∀ (a' : Fin r) (q : Fin (2 * r + k + 1)) (ha' : a'.val < D.ptSize a),
      PBG.y0 (levelZeroPointOver a hle g') a' q =
        if hq : r + k < q.val ∧ 2 * r + k - q.val < D.ptSize a then
          star (U.hMat (D.ptPerm a) (D.ptDiag a) ⟨a'.val, ha'⟩ ⟨2 * r + k - q.val, hq.2⟩) else 0)

theorem castM_apply' {k a b : ℕ} (h : a = b) (g : B.Mat k a) (i j : Fin (2 * b + k + 1)) :
    D.castM h g i j = g (Fin.cast (by rw [h]) i) (Fin.cast (by rw [h]) j) := rfl

theorem embedding_map_apply_last_block {k p ρ : ℕ} (Z : Matrix (Fin p) (Fin p) ℂ) (γ : B.Mat k ρ) (c : Fin p)
    (j : Fin (2 * (p + ρ) + k + 1)) :
    U.mMap k p ρ Z γ (U.eB k p ρ (Sum.inr c)) j =
      if hj : j.val < p then Z c.rev ⟨j.val, hj⟩ else 0 := by
  obtain ⟨y, rfl⟩ := (U.eB k p ρ).surjective j
  rw [U.mMap, Ux3.block3_apply]
  rcases y with (y | y) | y
  · rw [dite_eq_left (by rw [Ux3.block_index_first_val]; exact y.isLt)]
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromCols_apply_inl]
    rw [Ux3.wMat_mul_apply]
    exact congrArg (Z c.rev) (Fin.ext (Ux3.block_index_first_val (k := k) (ρ := ρ) y).symm)
  · rw [dite_eq_right (by rw [Ux3.block_index_middle_val]; omega)]
    simp [Matrix.fromBlocks_apply₂₁, Matrix.fromCols_apply_inr]
  · rw [dite_eq_right (by rw [Ux3.block_index_last_val]; omega)]
    simp [Matrix.fromBlocks_apply₂₂]

theorem embedding_map_apply_first_block {k p ρ : ℕ} (Z : Matrix (Fin p) (Fin p) ℂ) (γ : B.Mat k ρ) (b : Fin p)
    (i : Fin (2 * (p + ρ) + k + 1)) :
    U.mMap k p ρ Z γ i (U.eB k p ρ (Sum.inl (Sum.inl b))) =
      if hi : p + (2 * ρ + k + 1) ≤ i.val then
        (G.wMat p * Z) ⟨i.val - (p + (2 * ρ + k + 1)), by omega⟩ b else 0 := by
  obtain ⟨y, rfl⟩ := (U.eB k p ρ).surjective i
  rw [U.mMap, Ux3.block3_apply]
  rcases y with (y | y) | y
  · rw [dite_eq_right (by rw [Ux3.block_index_first_val]; omega)]
    simp [Matrix.fromBlocks_apply₁₁]
  · rw [dite_eq_right (by rw [Ux3.block_index_middle_val]; omega)]
    simp [Matrix.fromBlocks_apply₁₁]
  · rw [dite_eq_left (by rw [Ux3.block_index_last_val]; omega)]
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromCols_apply_inl]
    exact congrArg (fun c => (G.wMat p * Z) c b) (Fin.ext (by
      show (U.eB k p ρ (Sum.inr y)).val - (p + (2 * ρ + k + 1)) = y.val
      rw [Ux3.block_index_last_val]; omega)).symm

theorem normal_form_left_hypothesis : NFHypL := by
  intro k r a hle g' hg' hloc
  have hd : ∀ i, D.ptDiag a i ≠ 0 := fun i => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne a hloc.1 i i.2
  have hZ : (U.hMat (D.ptPerm a) (D.ptDiag a)).det ≠ 0 := Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne _ _ hd
  have hM : U.mMap k (D.ptSize a) (r - D.ptSize a) (U.hMat (D.ptPerm a) (D.ptDiag a)) g' ∈
      B.GV k (D.ptSize a + (r - D.ptSize a)) :=
    (Formalism.FourierDecayAlt.P.slice_membership k (D.ptSize a) (r - D.ptSize a)).1 _ g' hZ hg'
  refine ⟨Formalism.FourierDecayAlt.P.PBE.castM_GV _ hM, fun a' q ha' => ?_, fun a' q ha' => ?_⟩
  · unfold PBG.xi0
    rw [Formalism.FourierDecayAlt.P.PBM.herm_bvec_eI', Formalism.FourierDecayAlt.P.PBM.mulVec_bvec_apply]
    unfold levelZeroPointOver
    rw [castM_apply']
    have hi : (Fin.cast (by omega) (esI k r a') : Fin (2 * (D.ptSize a + (r - D.ptSize a)) + k + 1)) =
        U.eB k (D.ptSize a) (r - D.ptSize a) (Sum.inr ⟨D.ptSize a - 1 - a'.val, by omega⟩) := by
      ext; rw [Ux3.block_index_last_val]; simp [esI]; omega
    rw [hi, embedding_map_apply_last_block]
    by_cases hq : q.val < D.ptSize a
    · rw [dite_eq_left (by simpa using hq), dite_eq_left hq]
      congr 1; ext; simp [Fin.val_rev]; omega
    · rw [dite_eq_right (by simpa using hq), dite_eq_right hq]
  · unfold PBG.y0
    rw [Formalism.FourierDecayAlt.P.PBM.mulVec_bvec_apply]
    have hgu : IsUnit g'.det := WeylGroupFacts.isUnit_of_uh hg'
    unfold levelZeroPointOver
    rw [← Formalism.FourierDecayAlt.P.PBH.asm_castM_inv, Formalism.FourierDecayAlt.P.PBM.mMap_inv _ _ (isUnit_iff_ne_zero.mpr hZ) hgu, castM_apply']
    have hj : (Fin.cast (by omega) (eI k r a') : Fin (2 * (D.ptSize a + (r - D.ptSize a)) + k + 1)) =
        U.eB k (D.ptSize a) (r - D.ptSize a) (Sum.inl (Sum.inl ⟨a'.val, ha'⟩)) := by
      ext; rw [Ux3.block_index_first_val]; simp [eI]
    rw [hj, embedding_map_apply_first_block]
    by_cases hq : r + k < q.val ∧ 2 * r + k - q.val < D.ptSize a
    · rw [dite_eq_left (by simp; omega), dite_eq_left hq, Ux3.wMat_mul_apply, Matrix.conjTranspose_apply]
      congr 2 <;> ext <;> simp [Fin.val_rev] <;> omega
    · rw [dite_eq_right (by simp; omega), dite_eq_right hq]

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACSmooth
open MeasureTheory Topology Matrix
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

def linM {k r : ℕ} (A Bb : B.Mat k r) : Mt k r →ₗ[ℝ] Mt k r :=
  ((LinearMap.mulLeft ℝ A).comp (LinearMap.mulRight ℝ Bb) : B.Mat k r →ₗ[ℝ] B.Mat k r)

theorem linM_apply {k r : ℕ} (A Bb : B.Mat k r) (v : Mt k r) :
    (Matrix.of (linM A Bb v) : B.Mat k r) = A * Matrix.of v * Bb := by
  show A * ((Matrix.of v : B.Mat k r) * Bb) = _
  rw [Matrix.mul_assoc]

theorem aCSmooth_of_proper (hP : ACProper) : ACSmooth := by
  intro k r Wp Wq _ _ _ _ D φ₀ hφ hφc hφs g₀ hg₀

  obtain ⟨ε₀, hε₀, hball⟩ :=
    Metric.mem_nhds_iff.1 ((Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open D.z D.z').mem_nhds hg₀.2)
  have hε : 0 < ε₀ / 2 := by positivity
  have hCb : Metric.closedBall g₀ (ε₀ / 2) ⊆ Q.OmPlus k r D.z D.z' := fun x hx =>
    hball (Metric.closedBall_subset_ball (by linarith) hx)
  have hC'c : IsCompact (Metric.closedBall g₀ (ε₀ / 2) ∩ B.GV k r) :=
    (isCompact_closedBall g₀ (ε₀ / 2)).inter_right Formalism.FourierDecayAlt.P.B5.GV_closed
  have hC'O : Metric.closedBall g₀ (ε₀ / 2) ∩ B.GV k r ⊆ JF.Om k r D.z D.z' := fun x hx => ⟨hx.2, hCb hx.1⟩
  obtain ⟨P, hPc, hPp⟩ := hP k r Wp Wq D (tsupport φ₀) _ hφc hC'c hC'O

  set Am : B.SS k r → B.Mat k r := fun p =>
    (Hpk k r * (Matrix.of p.1.1 : B.Mat k r)ᴴ * Hpk k r) * (Hpk k r * (Matrix.of p.1.2 : B.Mat k r)ᴴ * Hpk k r)
    with hAm
  set Bm : B.SS k r → B.Mat k r := fun p => (Matrix.of p.2.2 : B.Mat k r) * Matrix.of p.2.1 with hBm
  have hsgs : ∀ p, D.inSS p → ∀ g, B.sgs p g = Am p * g * Bm p := by
    intro p hp g
    show (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 * Matrix.of p.2.1 = _
    rw [Formalism.FourierDecayAlt.P.Qx3.uh_inv_eq hp.1.1, Formalism.FourierDecayAlt.P.Qx3.uh_inv_eq hp.2.1.1]
    simp only [hAm, hBm, Matrix.mul_assoc]
  have hof : Continuous (fun ν : Mt k r => (Matrix.of ν : B.Mat k r)) := continuous_id
  have hAc : Continuous Am := by
    have h1 : Continuous (fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r)) := hof.comp continuous_fst.fst
    have h2 : Continuous (fun p : B.SS k r => (Matrix.of p.1.2 : B.Mat k r)) := hof.comp continuous_fst.snd
    exact ((continuous_const.mul h1.matrix_conjTranspose).mul continuous_const).mul
      ((continuous_const.mul h2.matrix_conjTranspose).mul continuous_const)
  have hBc : Continuous Bm := by
    have h3 : Continuous (fun p : B.SS k r => (Matrix.of p.2.2 : B.Mat k r)) := hof.comp continuous_snd.snd
    have h4 : Continuous (fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r)) := hof.comp continuous_snd.fst
    exact h3.mul h4
  have hcont : Continuous (fun p : B.SS k r => B.gN (Am p) * B.gN (Bm p)) :=
    (Formalism.FourierDecayAlt.P.B6.gN_continuous.comp hAc).mul (Formalism.FourierDecayAlt.P.B6.gN_continuous.comp hBc)
  obtain ⟨M₁, hM₁⟩ := hPc.exists_bound_of_continuousOn hcont.continuousOn
  set L : B.SS k r → (Mt k r →L[ℝ] Mt k r) := fun p => LinearMap.toContinuousLinearMap (linM (Am p) (Bm p))
    with hLdef
  have hL : ∀ p (v : Mt k r), (Matrix.of (L p v) : B.Mat k r) = Am p * Matrix.of v * Bm p := fun p v =>
    linM_apply (Am p) (Bm p) v
  set nn : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hnn
  have hnn0 : 0 ≤ nn := by positivity
  set ML : ℝ := nn * max M₁ 0 with hML
  have hML0 : 0 ≤ ML := mul_nonneg hnn0 (le_max_right _ _)
  have hLn : ∀ p ∈ P, ‖L p‖ ≤ ML := by
    intro p hp
    apply ContinuousLinearMap.opNorm_le_bound _ hML0
    intro v
    have e1 : ‖L p v‖ = ‖(Matrix.of (L p v) : B.Mat k r)‖ := rfl
    have e2 : ‖v‖ = ‖(Matrix.of v : B.Mat k r)‖ := rfl
    rw [e1, e2, hL]
    set g : B.Mat k r := Matrix.of v
    have hgA := Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.gN_nonneg (Am p)
    have hgB := Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.gN_nonneg (Bm p)
    have hgg := Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.gN_nonneg g
    have hgn : B.gN g ≤ nn * ‖g‖ :=
      Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.gN_le_of_ent g ‖g‖ (norm_nonneg _) (fun i j => Matrix.norm_entry_le_entrywise_sup_norm g)
    have hAB : B.gN (Am p) * B.gN (Bm p) ≤ max M₁ 0 := by
      have := hM₁ p hp
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hgA hgB)] at this
      exact this.trans (le_max_left _ _)
    calc ‖Am p * g * Bm p‖ ≤ B.gN (Am p * g * Bm p) := Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm.sup_le_gN _
      _ ≤ B.gN (Am p * g) * B.gN (Bm p) := Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _
      _ ≤ (B.gN (Am p) * B.gN g) * B.gN (Bm p) :=
          mul_le_mul_of_nonneg_right (Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _) hgB
      _ = (B.gN (Am p) * B.gN (Bm p)) * B.gN g := by ring
      _ ≤ max M₁ 0 * (nn * ‖g‖) := mul_le_mul hAB hgn hgg (le_max_right _ _)
      _ = ML * ‖g‖ := by rw [hML]; ring

  set φ₁ : Mt k r → ℝ := fun v => φ₀ (Matrix.of v) with hφ₁def
  have hφ₁ : ContDiff ℝ ∞ φ₁ := hφ
  have hφ₁c : HasCompactSupport φ₁ := hφc
  have hK : ∀ i : ℕ, ∃ K : ℝ, ∀ x, ‖iteratedFDeriv ℝ i φ₁ x‖ ≤ K := fun i =>
    (hφ₁.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support (hφ₁c.iteratedFDeriv i)
  choose K hKb using hK

  set F : B.SS k r → Mt k r → ℝ := fun p y => P.indicator (fun p => φ₁ (L p y)) p with hF
  have hFin : ∀ p ∈ P, F p = φ₁ ∘ (L p) := fun p hp => by
    funext y; simp [hF, hp]
  have hFout : ∀ p ∉ P, F p = fun _ => 0 := fun p hp => by
    funext y; simp [hF, hp]

  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  have : IsFiniteMeasureOnCompacts D.μW := ⟨D.haarW.finite_compact⟩
  have : IsFiniteMeasureOnCompacts D.μN := ⟨D.haarN.finite_compact⟩
  have : IsFiniteMeasureOnCompacts D.μW' := ⟨D.haarW'.finite_compact⟩
  have : IsFiniteMeasureOnCompacts (D.μW.prod D.μN) := inferInstance
  have : IsFiniteMeasureOnCompacts (D.μW'.prod D.μN) := inferInstance
  have : IsFiniteMeasureOnCompacts D.μSS := by
    show IsFiniteMeasureOnCompacts ((D.μW.prod D.μN).prod (D.μW'.prod D.μN))
    infer_instance
  have hPfin : D.μSS P ≠ ⊤ := (hPc.measure_lt_top (μ := D.μSS)).ne
  have hPm : MeasurableSet P := hPc.isClosed.measurableSet
  have hFm : ∀ y, AEStronglyMeasurable (fun p => F p y) D.μSS := by
    intro y
    have hc : Continuous (fun p => φ₁ (L p y)) := by
      have : (fun p => φ₁ (L p y)) = fun p => φ₀ (Am p * Matrix.of y * Bm p) := by
        funext p; simp only [hφ₁def]; rw [hL]
      rw [this]
      exact hφ.continuous.comp ((hAc.mul continuous_const).mul hBc)
    exact (hc.measurable.indicator hPm).aestronglyMeasurable
  have hsm : ContDiffOn ℝ ∞ (fun y => ∫ p, F p y ∂D.μSS) (Metric.ball (Matrix.of.symm g₀ : Mt k r) (ε₀ / 2)) := by
    rw [contDiffOn_infty]
    intro N
    set Kt : ℝ := (∑ i ∈ Finset.range (N + 1), |K i|) * (max ML 1) ^ N with hKt
    have hb : Integrable (P.indicator fun _ => Kt) D.μSS :=
      (integrableOn_const hPfin).integrable_indicator hPm
    refine (Formalism.FourierDecayAlt.P.Ux10.pint Metric.isOpen_ball (P.indicator fun _ => Kt) hb N ℝ F ?_ (fun y _ => hFm y) ?_).1
    · intro p
      by_cases hp : p ∈ P
      · rw [hFin p hp]
        exact (hφ₁.comp (L p).contDiff).contDiffOn.of_le (mod_cast le_top)
      · rw [hFout p hp]; exact contDiffOn_const
    · intro i hi y _ p
      by_cases hp : p ∈ P
      · rw [hFin p hp, ContinuousLinearMap.iteratedFDeriv_comp_right (L p) hφ₁ y (mod_cast le_top)]
        simp only [Set.indicator_of_mem hp]
        refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        have h1 : ‖iteratedFDeriv ℝ i φ₁ (L p y)‖ ≤ ∑ j ∈ Finset.range (N + 1), |K j| :=
          (hKb i _).trans ((le_abs_self _).trans
            (Finset.single_le_sum (f := fun j => |K j|) (fun j _ => abs_nonneg _) (Finset.mem_range.2 (by omega))))
        have h2 : ‖L p‖ ^ i ≤ (max ML 1) ^ N :=
          (pow_le_pow_left₀ (norm_nonneg _) ((hLn p hp).trans (le_max_left _ _)) i).trans
            (pow_le_pow_right₀ (le_max_right _ _) hi)
        exact mul_le_mul h1 h2 (pow_nonneg (norm_nonneg _) _)
          (Finset.sum_nonneg fun j _ => abs_nonneg _)
      · rw [hFout p hp, iteratedFDeriv_fun_zero]
        simp [Set.indicator_of_notMem hp]
  refine ⟨Metric.ball g₀ (ε₀ / 2), fun g => ∫ p, F p (Matrix.of.symm g) ∂D.μSS, Metric.isOpen_ball,
    Metric.mem_ball_self hε, hsm, ?_⟩
  intro g hg hgG
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp
  by_cases hpP : p ∈ P
  · have e : φ₁ (L p (Matrix.of.symm g)) = φ₀ (Am p * g * Bm p) := by
      simp only [hφ₁def]; rw [hL]; rfl
    simp only [hF, Set.indicator_of_mem hpP, e, hsgs p hp g]
  · have h0 : φ₀ (B.sgs p g) = 0 := by
      by_contra hne
      exact hpP (hPp p hp g ⟨Metric.ball_subset_closedBall hg, hgG⟩ (subset_tsupport _ hne))
    simp [hF, hpP, h0]

theorem averaging_smoothness_holds : ACSmooth := aCSmooth_of_proper averaging_properness_holds

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjAsm
namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section clm

variable {k r : ℕ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
  [NormedSpace ℂ E']

theorem contDiff_clm_comp (Λ : E →L[ℂ] E') {ψ : B.Mat k r → E} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (fun g => Λ (ψ g)) :=
  (Λ.restrictScalars ℝ).contDiff.comp hψ

theorem rdV_clm (Λ : E →L[ℂ] E') {ψ : B.Mat k r → E} (hψ : ContDiff ℝ ∞ ψ) (X : B.Mat k r) :
    RdV X (fun g => Λ (ψ g)) = fun g => Λ (RdV X ψ g) := by
  rw [rdV_global (contDiff_clm_comp Λ hψ) X, rdV_global hψ X]
  funext g
  have hd : HasFDerivAt ψ (fderiv ℝ ψ g) g := ((hψ.differentiable (by simp)) g).hasFDerivAt
  have h := (Λ.restrictScalars ℝ).hasFDerivAt.comp g hd
  exact (DFunLike.congr_fun h.fderiv (g * X)).trans rfl

theorem rw_clm' (Λ : E →L[ℂ] E') {ψ : B.Mat k r → E} (hψ : ContDiff ℝ ∞ ψ) :
    ∀ w : List (B.Mat k r), B.Rw w (fun g => Λ (ψ g)) = fun g => Λ (B.Rw w ψ g)
  | [] => rfl
  | X :: w => by
    show RdV X (B.Rw w (fun g => Λ (ψ g))) = fun g => Λ (RdV X (B.Rw w ψ) g)
    rw [rw_clm' Λ hψ w, rdV_clm Λ (rw_contDiff hψ w) X]

end clm

section comps

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def lam (i : Fin (Module.finrank ℂ Wq)) (j : Fin (Module.finrank ℂ Wp)) : (Wq →L[ℂ] Wp) →L[ℂ] ℂ :=
  (innerSL ℂ (stdOrthonormalBasis ℂ Wp j)).comp (ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i))

theorem lam_apply (i j) (A : Wq →L[ℂ] Wp) :
    lam i j A = inner ℂ (stdOrthonormalBasis ℂ Wp j) (A (stdOrthonormalBasis ℂ Wq i)) := rfl

theorem hsInner_eq_sum (A C : Wq →L[ℂ] Wp) :
    B.hsInner A C = ∑ i, ∑ j, lam i j A * star (lam i j C) := by
  unfold B.hsInner B.hsVec
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [PiLp.toLp_apply]
  rw [← (stdOrthonormalBasis ℂ Wp).sum_inner_mul_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lam_apply, lam_apply, mul_comm]
  congr 1
  rw [← inner_conj_symm]
  rfl

end comps

section terms

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem lam_opAdj_tail (i j) (s : ℂ) {ψ : B.Mat k r → (Wq →L[ℂ] Wp)} (hψ : ContDiff ℝ ∞ ψ) :
    ∀ (L : List (ℂ × List (B.Mat k r))), (∀ cw ∈ L, ∀ X ∈ cw.2, B.inLie k r X) → ∀ g,
    lam i j (((L.map fun cw => TLB.cTerm (Wp := Wp) (Wq := Wq) (s * cw.1) cw.2).map
        (fun T => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (fun x => T.coefAdj x (ψ x)) g)).sum) =
      conj s * (L.map fun cw => conj cw.1 * (-1 : ℂ) ^ cw.2.length *
        B.Rw cw.2.reverse (fun x => lam i j (ψ x)) g).sum
  | [], _, g => by simp
  | cw :: L, hL, g => by
    simp only [List.map_cons, List.sum_cons, map_add (f := _), mul_add]
    rw [lam_opAdj_tail i j s hψ L (fun cw' h => hL cw' (List.mem_cons_of_mem _ h)) g]
    congr 1
    rw [TLB.cTerm_word (hL cw List.mem_cons_self)]
    have e : (fun x => (TLB.cTerm (Wp := Wp) (Wq := Wq) (s * cw.1) cw.2).coefAdj x (ψ x)) =
        conj (s * cw.1) • ψ := by
      funext x; simp [TLB.cTerm]
    rw [e, Formalism.FourierDecayAlt.P.PositiveOrbitOpen.rw_smul, map_smul, Pi.smul_apply, map_smul]
    have e2 := congrFun (rw_clm' (lam i j) hψ cw.2.reverse) g
    rw [← e2, smul_eq_mul, smul_eq_mul, map_mul]
    ring

theorem lam_wordSum (i j) {ψ : B.Mat k r → (Wq →L[ℂ] Wp)} (hψ : ContDiff ℝ ∞ ψ) :
    ∀ (L : List (ℂ × List (B.Mat k r))) (g : B.Mat k r),
    lam i j ((L.map fun cw => cw.1 • B.Rw cw.2 ψ g).sum) =
      (L.map fun cw => cw.1 • B.Rw cw.2 (fun x => lam i j (ψ x)) g).sum
  | [], _ => by simp
  | cw :: L, g => by
    simp only [List.map_cons, List.sum_cons, map_add (f := _), map_smul]
    rw [lam_wordSum i j hψ L g, congrFun (rw_clm' (lam i j) hψ cw.2) g]

theorem wsAdj_contDiff (L : List (ℂ × List (B.Mat k r))) {b : B.Mat k r → ℂ} (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (wsAdj L b) := by
  unfold wsAdj
  exact contDiff_listSum (fun (cw : ℂ × List (B.Mat k r)) x => conj cw.1 * (-1 : ℂ) ^ cw.2.length * B.Rw cw.2.reverse b x) L
    fun cw _ => contDiff_const.mul (rw_contDiff hb _)

end terms

theorem capacity_adjoint_integral_scalar : CapAdjIntOfScalar := by
  intro hS k r Wp Wq _ _ _ _ _ _ s Y μ hμ φ ψ hφ hφc hψ hψc
  haveI : IsFiniteMeasureOnCompacts μ := ⟨hμ.finite_compact⟩
  have hLw := (Classical.choose_spec (Formalism.FourierDecayAlt.P.capelli_word_sum k r Y)).1
  obtain ⟨L', hL', hCV'⟩ := Formalism.FourierDecayAlt.P.capelli_word_sum k r (conj Y)
  set a : Fin (Module.finrank ℂ Wq) → Fin (Module.finrank ℂ Wp) → B.Mat k r → ℂ :=
    fun i j g => lam i j (φ g) with ha
  set b : Fin (Module.finrank ℂ Wq) → Fin (Module.finrank ℂ Wp) → B.Mat k r → ℂ :=
    fun i j g => lam i j (ψ g) with hb
  have ha_s : ∀ i j, ContDiff ℝ ∞ (a i j) := fun i j => contDiff_clm_comp (lam i j) hφ
  have hb_s : ∀ i j, ContDiff ℝ ∞ (b i j) := fun i j => contDiff_clm_comp (lam i j) hψ
  have ha_c : ∀ i j, HasCompactSupport (a i j) := fun i j => hφc.comp_left (map_zero (lam i j))
  have hb_c : ∀ i j, HasCompactSupport (b i j) := fun i j => hψc.comp_left (map_zero (lam i j))

  have hAdj : ∀ i j g, lam i j (B.opAdj (capTh k r Wp Wq s Y) ψ g) = conj s * wsAdj (capLw k r Y) (b i j) g := by
    intro i j g
    unfold B.opAdj
    rw [capTh, TLB.capOp, List.map_cons, List.sum_cons, map_add (f := _)]
    have h0 : (fun x => (TLB.cTerm (Wp := Wp) (Wq := Wq) 0
        (List.replicate (2 * r + k + 1) (0 : B.Mat k r))).coefAdj x (ψ x)) = (0 : ℂ) • ψ := by
      funext x; simp [TLB.cTerm]
    rw [h0, Formalism.FourierDecayAlt.P.PositiveOrbitOpen.rw_smul, zero_smul]
    rw [lam_opAdj_tail i j s hψ (capLw k r Y) (fun cw h X hX => ((hLw cw h).1 X hX).1) g]
    simp [wsAdj, b]

  have hCVc : ∀ i j, ∀ g ∈ B.GV k r, lam i j (Q.CV k r (conj Y) ψ g) = Q.CV k r (conj Y) (b i j) g := by
    intro i j g hg
    rw [hCV' _ (B.GV k r) ψ (ckOn_of_contDiff hψ _ _) g hg hg,
      hCV' _ (B.GV k r) (b i j) (ckOn_of_contDiff (hb_s i j) _ _) g hg hg]
    exact lam_wordSum i j hψ L' g

  have hP1 : ∀ x : Mt k r, B.hsInner (φ (Matrix.of x)) (B.opAdj (capTh k r Wp Wq s Y) ψ (Matrix.of x)) =
      ∑ i, ∑ j, s * (a i j (Matrix.of x) * star (wsAdj (capLw k r Y) (b i j) (Matrix.of x))) := by
    intro x
    rw [hsInner_eq_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hAdj, star_mul', Complex.star_def, Complex.conj_conj]
    simp only [ha]; ring
  have hP2 : ∀ᵐ x ∂μ, B.hsInner (φ (Matrix.of x)) (conj s • Q.CV k r (conj Y) ψ (Matrix.of x)) =
      ∑ i, ∑ j, s * (a i j (Matrix.of x) * star (Q.CV k r (conj Y) (b i j) (Matrix.of x))) := by
    filter_upwards [Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.ae_mem hμ] with x hx
    rw [hsInner_eq_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hCVc i j _ hx, smul_eq_mul, star_mul', Complex.star_def, Complex.conj_conj]
    simp only [ha]; ring

  have hI1 : ∀ i j, Integrable (fun x : Mt k r => s * (a i j (Matrix.of x) *
      star (wsAdj (capLw k r Y) (b i j) (Matrix.of x)))) μ := by
    intro i j
    have hc : Continuous (fun x : Mt k r => a i j (Matrix.of x) * star (wsAdj (capLw k r Y) (b i j) (Matrix.of x))) :=
      (ha_s i j).continuous.mul (continuous_star.comp (wsAdj_contDiff _ (hb_s i j)).continuous)
    have hcs : HasCompactSupport
        (fun x : Mt k r => a i j (Matrix.of x) * star (wsAdj (capLw k r Y) (b i j) (Matrix.of x))) :=
      (ha_c i j).mul_right
    exact (hc.integrable_of_hasCompactSupport (μ := μ) hcs).const_mul s
  have hI2 : ∀ i j, Integrable (fun x : Mt k r => s * (a i j (Matrix.of x) *
      star (Q.CV k r (conj Y) (b i j) (Matrix.of x)))) μ := by
    intro i j
    have hS' : ContDiff ℝ ∞ (fun g => (L'.map fun cw => cw.1 • B.Rw cw.2 (b i j) g).sum) :=
      contDiff_listSum (fun cw g => cw.1 • B.Rw cw.2 (b i j) g) L' fun cw _ =>
        (rw_contDiff (hb_s i j) _).const_smul _
    have hc : Continuous (fun x : Mt k r => a i j (Matrix.of x) *
        star ((L'.map fun cw => cw.1 • B.Rw cw.2 (b i j) (Matrix.of x)).sum)) :=
      (ha_s i j).continuous.mul (continuous_star.comp hS'.continuous)
    have hcs : HasCompactSupport (fun x : Mt k r => a i j (Matrix.of x) *
        star ((L'.map fun cw => cw.1 • B.Rw cw.2 (b i j) (Matrix.of x)).sum)) :=
      (ha_c i j).mul_right
    refine ((hc.integrable_of_hasCompactSupport (μ := μ) hcs).const_mul s).congr ?_
    filter_upwards [Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.ae_mem hμ] with x hx
    rw [hCV' _ (B.GV k r) (b i j) (ckOn_of_contDiff (hb_s i j) _ _) _ hx hx]
  rw [integral_congr_ae (Eventually.of_forall hP1), integral_congr_ae hP2,
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hI1 i j),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hI2 i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => hI1 i j), integral_finsetSum _ (fun j _ => hI2 i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_const_mul,
    hS k r Y μ hμ (a i j) (b i j) (ha_s i j) (ha_c i j) (hb_s i j) (hb_c i j)]

theorem capAdjInt_of_scalar (hS : CapAdjScalar) : CapAdjInt := capacity_adjoint_integral_scalar hS

end

end Formalism.FourierDecayAlt.P.CutMP.ER
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PbHeadTopOf
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadWeightAt
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadWeightAtOfExists
open Matrix MeasureTheory Finset
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace Formalism.FourierDecayAlt.P.DiagonalScalarMatrices

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Dx2.DF

theorem interp_any {ι : Type} [Fintype ι] (node : ι → ℂ) (hinj : Function.Injective node) (f : ι → ℂ) :
    ∃ q : Polynomial ℂ, ∀ i, q.eval (node i) = f i := by
  classical
  refine ⟨Lagrange.interpolate Finset.univ node f, fun i => ?_⟩
  exact Lagrange.eval_interpolate_at_node f hinj.injOn (Finset.mem_univ i)

section frame

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem frame_dframe (S : B.RealPlaceData k r Wp Wq) (hr : r = 0) {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ γ : B.Mat k r}
    (hD : D.IsDFrame S ν' m₀ γ) {m : ℕ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : Q.IsFrameOf k r [S.z', ν'] Bs) :
    Q.IsFrameOf k r [γ⁻¹ *ᵥ S.z, S.z'] Bs := by
  subst hr
  obtain ⟨hB1, hB2, hB3⟩ := hB
  refine ⟨hB1, hB2, fun a v hv => ?_⟩
  simp only [List.mem_cons, List.mem_singleton] at hv
  rcases hv with rfl | rfl | hv
  · obtain ⟨-, ⟨α, -, hα⟩, -⟩ := hD
    have hcof : Formalism.FourierDecayAlt.D.cofL S γ = S.z := by
      unfold Formalism.FourierDecayAlt.D.cofL
      simp [Matrix.adjugate_fin_one, fvec, Matrix.one_apply]
    rw [hcof] at hα
    have hvb : (fun i : Fin (2 * 0 + k + 1) => if 0 ≤ i.val ∧ i.val ≤ 0 + k then (γ⁻¹ *ᵥ S.z) i else 0) =
        γ⁻¹ *ᵥ S.z := by
      funext i
      have := i.isLt
      rw [if_pos (by omega)]
    have hpr : γ⁻¹ *ᵥ S.z = Formalism.FourierDecayAlt.D.prW k 0 S.z' (γ⁻¹ *ᵥ S.z) +
        (herm (Hpk k 0) (γ⁻¹ *ᵥ S.z) S.z' / herm (Hpk k 0) S.z' S.z') • S.z' := by
      unfold Formalism.FourierDecayAlt.D.prW
      dsimp only
      rw [hvb, sub_add_cancel]
    have h1 : herm (Hpk k 0) (Bs a) ν' = 0 := hB3 a ν' (by simp)
    have h2 : herm (Hpk k 0) (Bs a) S.z' = 0 := hB3 a S.z' (by simp)
    rw [hpr, hα]
    unfold herm at h1 h2 ⊢
    rw [star_add, star_smul, star_smul, add_dotProduct, smul_dotProduct, smul_dotProduct, h1, h2, smul_zero,
      smul_zero, add_zero]
  · exact hB3 a S.z' (by simp)
  · simp at hv

end frame

def HeadWeightAtOfEx : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (w : List C.Letter)
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π')) (JC.parLev P P.r).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π'))) (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ)
    (m₀r : B.Mat P.k (P.r - P.r)),
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    KB.CutWord P p.l0 w → PBI.LevFrame p ν'r m₀r →
    ∀ x ∈ Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z',
    ∀ γ₀ ∈ B.GV P.k (P.r - P.r),
      Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀ =
        Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2 →
      D.IsDFrame (p.T.bs P.r) ν'r m₀r γ₀ →
    (∀ Ψ : Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π
          (p.T.bs P.r).π',
        ∑ ρ : M.Ty P, (p.TP.E ρ).comp ((Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀) =
          (Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀) →
    (∀ h : C.LPt, D.IsLocPt h P.r →
        ∀ (y : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z
          (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π') e,
        (P5.act ((Fr.ofWord L st (D.positionted w)).d L) y e :
            Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀ =
          ∑ ρ : M.Ty P, ((Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w
              (h ++ [(1, Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2)]) e ρ ^ 2 : ℝ) : ℂ) •
            (p.TP.E ρ).comp ((y e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀))

end Formalism.FourierDecayAlt.P.DiagonalScalarMatrices

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexOrder

theorem head_weight_at_of_exists : DiagonalScalarMatrices.HeadWeightAtOfEx := by
  intro Wp Wq _ _ _ _ _ _ P p w X μ L st ν'r m₀r hD hcut hLF x hx γ₀ hγG hζ hγF hex h hh y e
  obtain ⟨hl1, hlk, hk2⟩ := p.hl
  have hr : P.r - P.r = 0 := by omega
  have hD' := hD
  obtain ⟨hPl, -, -, -, hq, hinv, -, -⟩ := hD'
  have hOK := hPl.1

  have hw := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of (JC.parLev P P.r) _ _ _ _ st p.l0 hOK hl1 hlk hq hinv w hcut.1 hcut.2

  have hGx : 0 < Complex.normSq (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2) -
      Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z' := hx.2.2
  have hx' : (x.1, γ₀) ∈ Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' := by
    refine ⟨hx.1, ⟨hγG, fun a ha => by
      exfalso; have h1 := a.isLt; have h2 : (JC.parLev P P.r).r = P.r - P.r := rfl; omega⟩, ?_⟩
    show 0 < Complex.normSq (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀) -
      Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z'
    rw [hζ]; exact hGx

  have hbase := hLF.2.2
  obtain ⟨hν, hνz, hνν, -, -⟩ := id hbase
  obtain ⟨Bs', hB'⟩ := Formalism.FourierDecayAlt.P.Topx1.vecw_frame_exists P.k (P.r - P.r) (by omega) (p.T.bs P.r).z' ν'r
    (p.T.bs P.r).z'_mem (p.T.bs P.r).T'_pos hν hνz hνν
  have hBγ := DiagonalScalarMatrices.frame_dframe (p.T.bs P.r) hr hγF hB'

  obtain ⟨Y₀, hY₀⟩ := Formalism.FourierDecayAlt.P5.Kfp.sep_real hOK
  set f : M.Ty P → ℂ := fun ρ => Fr.cs (M.x0 P p.l0 ρ) (M.qC P) (D.positionted w) e with hfdef
  obtain ⟨q, hq'⟩ := DiagonalScalarMatrices.interp_any (fun ρ : M.Ty P => M.xC P ρ (Y₀ : ℂ)) hY₀ f
  set V := ((y e : Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
    (p.T.bs P.r).π (p.T.bs P.r).π') : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀ with hVdef
  have hV := PBI.grpInt_at_dframe p hLF (y e) x hx hγG hζ hγF
  refine ContinuousLinearMap.ext fun v => ?_
  have h1 := DiagonalScalarMatrices.dw_pt (JC.parLev P P.r) _ _ _ _ X μ L st p.l0 hD (D.positionted w) hw Y₀ e q hq' y x.1 γ₀ hx' Bs' hBγ v
  have h2 := DiagonalScalarMatrices.poly_types p ν'r m₀r hLF hB' V hV (hex (y e)) (Y₀ : ℂ) q v
  rw [show ((JC.parLev P P.r).k : ℂ) = (P.k : ℂ) from rfl, ← hVdef] at h1
  erw [h2] at h1
  rw [h1]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  congr 1
  rw [hq' ρ]
  set ζx := Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2 with hζx
  have hTb : Tz P.k P.r p.T.base.z = P.T := p.hP.2.2.2.1
  have hTb' : Tz P.k P.r p.T.base.z' = P.T' := p.hP.2.2.2.2.1
  have hTr : Tz P.k (P.r - P.r) (p.T.bs P.r).z = P.T := hPl.2.2.2.1
  have hTr' : Tz P.k (P.r - P.r) (p.T.bs P.r).z' = P.T' := hPl.2.2.2.2.1
  have hzγ : Q.zetaL (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (Fin.last (JC.parLev P P.r).r) γ₀ = ζx := hζ
  have hGG : Q.GGl (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' γ₀ =
      Complex.normSq ζx - P.T * P.T' := by
    show Complex.normSq (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀) -
      Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z' = _
    rw [hζ, hTr, hTr']
  have hG0 : 0 < Complex.normSq ζx - P.T * P.T' := by rw [← hTr, ← hTr']; exact hGx
  have hlen : (D.positionted w).length = w.length := List.length_ofFn
  have hcW : Top.cW P p.l0 w e ρ = f ρ := by
    simp only [Top.cW, hfdef]
    congr 1
  have hc := Formalism.FourierDecayAlt.P.c_pos_truncated Formalism.FourierDecayAlt.P.interlacing_sign Formalism.FourierDecayAlt.P.q_positive_interlacing
    Formalism.FourierDecayAlt.P.q_positive_shift Formalism.FourierDecayAlt.P.cPos_true (Fin w.length) P.k P.u P.u' (M.rho P ρ) p.l0 P.T P.T'
    (D.positionted w) hl1 hlk (Formalism.FourierDecayAlt.P.types_interlace P p.hP.1 ρ) p.hP.1.T_pos p.hP.1.T'_pos hw.2.1 hw.2.2 e
  have hpos : 0 < f ρ := by rw [Complex.lt_def]; exact ⟨hc.1, hc.2.symm⟩
  have hre : 0 < (f ρ).re := (Complex.lt_def.1 hpos).1
  have him : (f ρ).im = 0 := (Complex.lt_def.1 hpos).2.symm
  have hfre : f ρ = ((f ρ).re : ℂ) := Complex.ext (by simp) (by simp [him])
  have hW := PBI.wPt_app (P.T * P.T') ζx h P.r hh
  have hWnn : 0 ≤ Top.wPt (P.T * P.T') P.r (h ++ [(1, ζx)]) := by
    rw [hW]; exact div_nonneg (Complex.normSq_nonneg _) hG0.le
  unfold Top.dH
  rw [hTb, hTb', hW, hcW, Real.sq_sqrt (mul_nonneg (pow_nonneg (by rw [← hW]; exact hWnn) _) hre.le), hGG, hzγ, hlen]
  rw [hfre]
  push_cast
  rw [div_eq_mul_inv, Complex.ofReal_re]

end Formalism.FourierDecayAlt.P
end
end

namespace Formalism.FourierDecayAlt.P

theorem head_weight_at : PBI.HeadWeightAt := by
  intro Wp Wq _ _ _ _ _ _ P p F w X μ L st Cb ν'r m₀r hD hdd hF hcut hLev x hx γ₀ hγG hζ hγF
  exact head_weight_at_of_exists Wp Wq P p w X μ L st ν'r m₀r hD hcut hLev x hx γ₀ hγG hζ hγF
    (fun Ψ => PBI.exAt p hLev Ψ x hx hγG hζ hγF)

end Formalism.FourierDecayAlt.P
end

namespace Formalism.FourierDecayAlt.P

theorem pb_headTop_of (hU5 : PBI.HighestUnipotentIntegral) (hPic : PBI.ExhPic) : KB.HeadTop :=
  head_top_of_radial_exhaustion hU5 hPic head_weight_at

end Formalism.FourierDecayAlt.P
end
