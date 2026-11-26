module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqUnitNormalizationLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselNormSqEqBigCellNormSq
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselNormSqEqBigCellNormSq
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.jN2_eq_normSq_base

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem good_of_weight_ne_zero (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ)
    (hw : bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
        ((fun j => c j.castSucc), c (Fin.last P.r)) ≠ 0) :
    (∀ a, c a ≠ 0) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c) := by
  set T := Tz P.k P.r p.T.base.z with hT
  set T' := Tz P.k P.r p.T.base.z' with hT'
  have hk : 2 ≤ P.k := p.hl.2.2
  have hTT : 0 < T * T' := mul_pos p.T.base.T_pos p.T.base.T'_pos
  have hw' := hw
  unfold bcWeight at hw'
  split_ifs at hw' with hle
  · have hprod := left_ne_zero_of_mul hw'
    have hgg := right_ne_zero_of_mul hw'
    have hlt : T * T' < Complex.normSq (c (Fin.last P.r)) := by
      rcases hle.lt_or_eq with h | h
      · exact h
      · exfalso; apply hgg; rw [← h, sub_self, zero_pow (by omega)]
    have hc : ∀ a : Fin P.r, c a.castSucc ≠ 0 := by
      intro a ha
      apply hprod
      refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
      dsimp only
      rw [ha, norm_zero, zero_pow]
      unfold Mdim; have := a.isLt; omega
    have hlast : c (Fin.last P.r) ≠ 0 := by
      intro h0; rw [h0, Complex.normSq_zero] at hlt; linarith
    have hd : ∀ a, c a ≠ 0 := by
      intro a
      induction a using Fin.lastCases with
      | last => exact hlast
      | cast i => exact hc i
    refine ⟨hd, ?_⟩
    show 0 < D.ptG (T * T') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c)
    unfold D.ptG
    rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
      Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
    have hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
      Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hc a)
    nlinarith [mul_lt_mul_of_pos_left hlt hp]
  · exact absurd rfl hw'

theorem pt_eq (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ) :
    TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c) =
    bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
        ((fun j => c j.castSucc), c (Fin.last P.r)) *
      ‖B.hsVec (B.JF p.T.base F (bigCell P.k P.r (fun j => c j.castSucc)
        (p.T.base.μsec (c (Fin.last P.r)))))‖ ^ 2 := by
  by_cases h : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)
  · obtain ⟨hl, hG⟩ := h
    have hd : ∀ a, c a ≠ 0 := fun a =>
      (hl.1 (1, c a) (by unfold TBB.bigPt; exact (List.mem_ofFn' _ _).2 ⟨a, rfl⟩)).2
    have hG' : 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c) := hG
    have hζ : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r)) :=
      Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG'
    rw [TBBx2.Tri.Ew_top p F hl, hsVec_norm_V_bigPt p F c hd hG]
    have hn : TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) =
        bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
          ((fun j => c j.castSucc), c (Fin.last P.r)) := nPt_bigPt P.k P.r _ _ c hζ.le
    rw [hn, Real.mul_self_sqrt (bcWeight_nonneg0 _ _ _ _ _)]
  · have hw : bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
        ((fun j => c j.castSucc), c (Fin.last P.r)) = 0 := by
      by_contra hw
      obtain ⟨hd, hG⟩ := good_of_weight_ne_zero p c hw
      exact h ⟨Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hd, hG⟩
    rw [TBBx4.ew_zero_of p F h, hw, zero_mul]

theorem besselNormSq_eq_bigCellNormSq : ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TBB.jN2 p F = B.normSq p.T.base F := by
  intro P Wp Wq _ _ _ _ _ _ p F
  let e : (Fin (P.r + 1) → ℂ) ≃ᵐ (Fin P.r → ℂ) × ℂ :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last P.r)).trans MeasurableEquiv.prodComm
  have hmp : MeasurePreserving e volume volume :=
    (Measure.measurePreserving_swap).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin (P.r + 1) => ℂ) (Fin.last P.r))
  have he : ∀ c, e c = ((fun j => c j.castSucc), c (Fin.last P.r)) := by
    intro c
    simp [e, MeasurableEquiv.piFinSuccAbove]
    rfl
  unfold B.normSq jNormSq
  rw [← hmp.lintegral_comp_emb e.measurableEmbedding]
  unfold TBB.jN2
  refine lintegral_congr fun c => ?_
  rw [he c, pt_eq p F c]
  rfl

end GlobalTheory.jN2_eq_normSq_base
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselNormSqEqBigCellNormSqStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jN2_eq_normSq_base : ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TBB.jN2 p F = B.normSq p.T.base F := by
  first | exact @GlobalTheory.jN2_eq_normSq_base.besselNormSq_eq_bigCellNormSq | exact GlobalTheory.jN2_eq_normSq_base.besselNormSq_eq_bigCellNormSq | (intros; apply GlobalTheory.jN2_eq_normSq_base.besselNormSq_eq_bigCellNormSq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AemeasurableBesselNormIntegrandBigCell
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AemeasurableBesselNormIntegrandBigCell
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory


open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P in
theorem bigCell_density_eq {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ) (hd : ∀ a, c a ≠ 0) :
    TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c) =
      if Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r)) then
        bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
            ((fun j => c j.castSucc), c (Fin.last P.r)) *
          ‖B7.hsL (B7.JM p.T.base F (1, 1) ((fun j => c j.castSucc), c (Fin.last P.r)))‖ ^ 2
      else 0 := by
  have hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hd
  have hc : ∀ a : Fin P.r, c a.castSucc ≠ 0 := fun a => hd _
  rw [TBBx2.Tri.Ew_top p F hl]
  split_ifs with hlt
  · have hG : 0 < TBB.Gp p (TBB.bigPt P.r c) := by
      show 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c)
      unfold D.ptG
      rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
        Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
      have hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
        Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hc a)
      nlinarith [mul_lt_mul_of_pos_left hlt hp]
    have hn : TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) =
        bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
          ((fun j => c j.castSucc), c (Fin.last P.r)) := CutBP.nPt_bigPt P.k P.r _ _ c hlt.le
    have hq : ((fun j => c j.castSucc), c (Fin.last P.r)) ∈ B7.Q0 p.T.base := ⟨hc, hlt⟩
    rw [CutBP.hsVec_norm_V_bigPt p F c hd hG, hn, Real.mul_self_sqrt (CutBP.bcWeight_nonneg0 _ _ _ _ _),
      B7.JM_eq p.T.base F (1, 1) hq, bessel_function_trivial_index P.k P.r Wp Wq p.T.base F, B7.hsL_apply]
    rfl
  · have hV : p.V F (TBB.bigPt P.r c) = 0 := by
      show D.vecV p.T.base p.ν' p.m₀ F (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = 0
      unfold D.vecV
      rw [dite_eq_right]
      rintro ⟨-, hG⟩
      exact hlt (Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG)
    rw [hV, TBBx2.Tri.hsVec_zero]
    simp


open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P in
theorem bigCell_density_aemeasurable :
    ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq)
      (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), ContinuousOn F (B.GV P.k P.r) →
      AEMeasurable fun c : Fin (P.r + 1) → ℂ =>
        ENNReal.ofReal (TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c)) := by
  intro P Wp Wq _ _ _ _ _ _ p F hF
  have hq : Measurable fun c : Fin (P.r + 1) → ℂ =>
      (((fun j => c j.castSucc), c (Fin.last P.r)) : (Fin P.r → ℂ) × ℂ) := by fun_prop
  have hJ : StronglyMeasurable fun q : (Fin P.r → ℂ) × ℂ => B7.JM p.T.base F (1, 1) q :=
    (B7.sm_JM p.T.base hF).comp_measurable measurable_prodMk_left
  have hN : Measurable fun q : (Fin P.r → ℂ) × ℂ => ‖B7.hsL (B7.JM p.T.base F (1, 1) q)‖ :=
    ((B7.hsL (Wp := Wp) (Wq := Wq)).continuous.comp_stronglyMeasurable hJ).norm.measurable
  have hm : Measurable fun c : Fin (P.r + 1) → ℂ =>
      if Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r)) then
        bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
            ((fun j => c j.castSucc), c (Fin.last P.r)) *
          ‖B7.hsL (B7.JM p.T.base F (1, 1) ((fun j => c j.castSucc), c (Fin.last P.r)))‖ ^ 2
      else 0 := by
    refine Measurable.ite ?_ ?_ measurable_const
    · exact measurableSet_lt measurable_const
        (Complex.continuous_normSq.measurable.comp (measurable_pi_apply _))
    · exact ((B7.measurable_bcWeight _ _).comp hq).mul ((hN.comp hq).pow_const 2)
  have hae : ∀ᵐ c : Fin (P.r + 1) → ℂ, ∀ a, c a ≠ 0 := by
    rw [ae_all_iff]
    intro a
    exact Measure.ae_eval_ne (fun _ => (volume : Measure ℂ)) a 0
  refine (ENNReal.measurable_ofReal.comp hm).aemeasurable.congr ?_
  filter_upwards [hae] with c hc
  rw [bigCell_density_eq p F c hc]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AemeasurableBesselNormIntegrandBigCellStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aemeasurable_besselNormIntegrand_bigCell : ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), ContinuousOn F (B.GV P.k P.r) → AEMeasurable fun c : Fin (P.r + 1) → ℂ => ENNReal.ofReal (TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c)) := by
  first | exact @GlobalTheory.bigCell_density_aemeasurable | exact GlobalTheory.bigCell_density_aemeasurable | (intros; apply GlobalTheory.bigCell_density_aemeasurable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellExpansionOfBesselFunctionZero
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellExpansionOfBesselFunctionZero
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem bigCellExpansion_of_besselFunction_zero : ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ), 0 ≤ b → (AEMeasurable fun c : Fin (P.r + 1) → ℂ => ENNReal.ofReal (TBB.Ew p (fun _ => 1) f (P.r + 1) [] (TBB.bigPt P.r c))) → (∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) → p.V f (TBB.bigPt P.r c) = 0) → Formalism.FourierDecayAlt.P.CutBP.FamilyDerivativeExpansion p f b C₃ a₁ := by
  intro P Wp Wq _ _ _ _ _ _ p f b C₃ a₁ hb hm hV
  have hV' : ∀ c : Fin (P.r + 1) → ℂ, p.V f (TBB.bigPt P.r c) = 0 := by
    intro c
    by_cases hc : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)
    · exact hV c hc.1 hc.2
    · exact Formalism.FourierDecayAlt.P.TBBx4.V_zero p _ hc
  refine ⟨ℤ, inferInstance, fun _ => f, 0, fun _ => 0, fun _ => 0, 0, (P.r + 1) * a₁, 0, rfl, le_rfl,
    fun _ _ => le_rfl, fun _ _ => le_rfl, rfl, rfl, ?_, le_rfl, ?_, fun _ => le_rfl, fun _ => hm⟩
  · intro μ _
    refine ⟨0, ?_, ?_, ?_⟩
    · funext c
      simp [hV' c]
    · simp
    · simp
  · rw [zero_pow (Nat.succ_ne_zero _)]
    exact Real.rpow_nonneg hb _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellExpansionOfBesselFunctionZeroStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyDerivativeExpansion_of_V_eq_zero : ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ), 0 ≤ b → (AEMeasurable fun c : Fin (P.r + 1) → ℂ => ENNReal.ofReal (TBB.Ew p (fun _ => 1) f (P.r + 1) [] (TBB.bigPt P.r c))) → (∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) → p.V f (TBB.bigPt P.r c) = 0) → Formalism.FourierDecayAlt.P.CutBP.FamilyDerivativeExpansion p f b C₃ a₁ := by
  first | exact @GlobalTheory.bigCellExpansion_of_besselFunction_zero | exact GlobalTheory.bigCellExpansion_of_besselFunction_zero | (intros; apply GlobalTheory.bigCellExpansion_of_besselFunction_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellExpansionSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellExpansionSmul
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem familyDerivativeExpansion_smul (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ) (t : ℂ)
    (h : Formalism.FourierDecayAlt.P.CutBP.FamilyDerivativeExpansion p f b C₃ a₁) :
    Formalism.FourierDecayAlt.P.CutBP.FamilyDerivativeExpansion p (fun g => t • f g) b C₃ a₁ := by
  obtain ⟨Par, inst, fam, lam, n₁, ninf, c0, q0, Gam, hf, hGam, h1, h2, h3, h4, hstep, hrange, hGb,
    hnorm, hmeas⟩ := h
  refine ⟨Par, inst, fun μ g => t • fam μ g, lam, n₁, ninf, c0, q0, Gam, ?_, hGam, h1, h2, h3, h4, ?_,
    hrange, hGb, ?_, ?_⟩
  · subst hf; rfl
  · intro μ hμ
    obtain ⟨a, hE, hS, hsupp⟩ := hstep μ hμ
    refine ⟨a, ?_, hS, hsupp⟩
    funext c
    have hc := congrFun hE c
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply] at hc ⊢
    rw [Formalism.FourierDecayAlt.P.CutBP.V_csmul p (fam μ) t, smul_comm, hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Formalism.FourierDecayAlt.P.CutBP.V_csmul p (fam (μ + ν)) t, smul_comm]
  · intro μ
    rw [Formalism.FourierDecayAlt.P.CutBP.norm_sq_const_smul p (fam μ) t, Formalism.FourierDecayAlt.P.CutBP.norm_sq_const_smul p f t]
    gcongr
    exact hnorm μ
  · intro μ
    have e : (fun c : Fin (P.r + 1) → ℂ =>
        ENNReal.ofReal (TBB.Ew p (fun _ => 1) (fun g => t • fam μ g) (P.r + 1) [] (TBB.bigPt P.r c))) =
        fun c => ENNReal.ofReal (‖t‖ ^ 2) *
          ENNReal.ofReal (TBB.Ew p (fun _ => 1) (fam μ) (P.r + 1) [] (TBB.bigPt P.r c)) := by
      funext c
      rw [Formalism.FourierDecayAlt.P.CutBP.Ew_csmul p (fam μ) t, ENNReal.ofReal_mul (sq_nonneg _)]
    rw [e]
    exact (hmeas μ).const_mul _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellExpansionSmulStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigCellExpansion_smul : ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ) (t : ℂ), Formalism.FourierDecayAlt.P.CutBP.FamilyDerivativeExpansion p f b C₃ a₁ → Formalism.FourierDecayAlt.P.CutBP.FamilyDerivativeExpansion p (fun g => t • f g) b C₃ a₁ := by
  first | exact @GlobalTheory.familyDerivativeExpansion_smul | exact GlobalTheory.familyDerivativeExpansion_smul | (intros; apply GlobalTheory.familyDerivativeExpansion_smul <;> assumption)
end
end
