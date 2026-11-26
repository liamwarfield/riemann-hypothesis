module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelModuleFormEqIntegralOfCompactCoeff
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AestronglyMeasurableTopVectorSmoothCoefficientStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopDensityBigCellEqProdLevelWeightsMulTopForm
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopDensityBigCellEqProdLevelWeightsMulTopForm
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory.TopDensity

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem RR_top_diag (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (γ : C.LPt) :
    ∃ x : ℝ, 0 ≤ x ∧ p.RR H (P.r + 1) w γ γ = (x : ℂ) := by
  unfold KB.Pl.RR D.RRplace
  split_ifs with h1 h2 h3 h4
  · omega
  · exact ⟨_, sq_nonneg _, Formalism.FourierDecayAlt.P.TBBx2.Tri.hsInner_self _⟩
  · unfold Top.topOf
    simp_rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.hsInner_self, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
    exact ⟨_, Finset.sum_nonneg fun e _ => Finset.sum_nonneg fun ρ _ =>
      mul_nonneg (mul_self_nonneg _) (sq_nonneg _), rfl⟩
  · exact ⟨0, le_rfl, by simp⟩
  · exact ⟨0, le_rfl, by simp⟩

theorem RR_top_zero (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (γ : C.LPt)
    (hv : ∀ F, p.V F γ = 0) : p.RR H (P.r + 1) w γ γ = 0 := by
  have hv' : ∀ F, D.vecV p.T.base p.ν' p.m₀ F γ = 0 := hv
  have h0 : B.hsInner (0 : Wq →L[ℂ] Wp) 0 = 0 := by
    unfold B.hsInner B.hsVec
    have : (WithLp.toLp 2 fun i : Fin (Module.finrank ℂ Wq) =>
        (0 : Wq →L[ℂ] Wp) (stdOrthonormalBasis ℂ Wq i)) = 0 := by
      simp; rfl
    rw [this, inner_zero_right]
  unfold KB.Pl.RR D.RRplace
  split_ifs with h1 h2 h3 h4
  · omega
  · rw [hv', h0]
  · unfold Top.topOf
    refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun ρ _ => ?_
    rw [hv', ContinuousLinearMap.comp_zero, h0, mul_zero]
  · rfl
  · rfl

theorem V_bigPt_zero (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ)
    (hζ : Complex.normSq (c (Fin.last P.r)) ≤ TBB.TTp p) : p.V F (TBB.bigPt P.r c) = 0 := by
  show D.vecV p.T.base p.ν' p.m₀ F (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = 0
  unfold D.vecV
  rw [dite_eq_right]
  rintro ⟨-, hG⟩
  have := Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG
  exact absurd this (not_lt.2 hζ)

theorem nPt_eq_prod (P : M.Par) (c : Fin (P.r + 1) → ℂ) (hζ : P.T * P.T' ≤ Complex.normSq (c (Fin.last P.r))) :
    TBB.nPt P.k P.r (P.T * P.T') (TBB.bigPt P.r c) = ∏ i : Fin (P.r + 1), KB.levW P ((i : ℕ) + 1) (c i) := by
  unfold TBB.nPt
  have e : D.ptGG (P.T * P.T') (TBB.bigPt P.r c) = Complex.normSq (c (Fin.last P.r)) - P.T * P.T' := by
    unfold D.ptGG
    rw [Formalism.FourierDecayAlt.P.CutBP.ptLast_bigPt]
  rw [e]
  unfold TBB.bigPt
  rw [Formalism.FourierDecayAlt.P.CutBP.level_product_of_constant_weights]
  refine Finset.prod_congr rfl fun i _ => ?_
  unfold KB.levW
  rw [add_comm 1 (i : ℕ)]
  split_ifs with h
  · have hi : i = Fin.last P.r := Fin.ext (by simp only [Fin.val_last]; omega)
    subst hi
    unfold B2.zWeight
    rw [if_pos hζ]
  · rfl

theorem levW_nonneg (P : M.Par) (i : ℕ) (c : ℂ) : 0 ≤ KB.levW P i c := by
  unfold KB.levW B2.zWeight
  split_ifs with h1 h2
  · exact pow_nonneg (sub_nonneg.2 h2) _
  · exact le_rfl
  · exact zpow_nonneg (norm_nonneg _) _

theorem topDensity_eq : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ), (∀ a, c a ≠ 0) → TBB.Ew p (fun _ => 1) H (P.r + 1) w (TBB.bigPt P.r c) = (∏ i : Fin (P.r + 1), KB.levW P ((i : ℕ) + 1) (c i)) * (p.RR H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c)).re ∧ (p.RR H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c)).im = 0 ∧ 0 ≤ (p.RR H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c)).re := by
  intro Wp Wq _ _ _ _ _ _ P p H w c _
  obtain ⟨x, hx, hRR⟩ := RR_top_diag p H w (TBB.bigPt P.r c)
  refine ⟨?_, by rw [hRR, Complex.ofReal_im], by rw [hRR, Complex.ofReal_re]; exact hx⟩
  have hTT : TBB.TTp p = P.T * P.T' := by
    unfold TBB.TTp
    rw [p.hP.2.2.2.1, p.hP.2.2.2.2.1]
  by_cases hζ : P.T * P.T' ≤ Complex.normSq (c (Fin.last P.r))
  · have hn : TBB.normC (fun _ => 1) w = 1 := by
      unfold TBB.normC
      simp
    unfold TBB.Ew TBB.NP
    rw [hn, hTT, nPt_eq_prod P c hζ, div_one,
      Real.mul_self_sqrt (Finset.prod_nonneg fun i _ => levW_nonneg P _ _), Complex.re_ofReal_mul]
  · have h0 := RR_top_zero p H w (TBB.bigPt P.r c) fun F =>
      V_bigPt_zero p F c (by rw [hTT]; exact (not_le.1 hζ).le)
    unfold TBB.Ew TBB.NP
    rw [h0]
    simp

end GlobalTheory.TopDensity
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopDensityBigCellEqProdLevelWeightsMulTopFormStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDensity_bigCell_eq_prod_levelWeights_mul_topForm : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ), (∀ a, c a ≠ 0) → TBB.Ew p (fun _ => 1) H (P.r + 1) w (TBB.bigPt P.r c) = (∏ i : Fin (P.r + 1), KB.levW P ((i : ℕ) + 1) (c i)) * (p.RR H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c)).re ∧ (p.RR H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c)).im = 0 ∧ 0 ≤ (p.RR H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c)).re := by
  first | exact @GlobalTheory.TopDensity.topDensity_eq | exact GlobalTheory.TopDensity.topDensity_eq | (intros; apply GlobalTheory.TopDensity.topDensity_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroFormDiagonalBigCellImEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroFormDiagonalBigCellImEqZero
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory.LevelFormsReal

theorem isLocPt_ofFn {j : ℕ} (c : Fin j → ℂ) (hc : ∀ l, c l ≠ 0) :
    D.IsLocPt (List.ofFn fun l => ((1 : ℕ), c l)) j := by
  refine ⟨fun b hb => ?_, ?_⟩
  · simp only [List.mem_ofFn] at hb
    obtain ⟨l, rfl⟩ := hb
    exact ⟨by simp, hc l⟩
  · simp [D.ptSize, List.map_ofFn, Function.comp_def]

theorem ofFn_snoc {j : ℕ} (c : Fin j → ℂ) (t : ℂ) :
    (List.ofFn fun l => ((1 : ℕ), (Fin.snoc c t : Fin (j + 1) → ℂ) l))
      = (List.ofFn fun l => ((1 : ℕ), c l)) ++ [(1, t)] := by
  rw [List.ofFn_succ']
  simp

theorem integral_im_eq_zero {f : ℂ → ℂ} (hf : ∀ t, t ≠ 0 → (f t).im = 0) :
    (∫ t : ℂ, f t).im = 0 := by
  have h : f =ᵐ[volume] fun t => (((f t).re : ℝ) : ℂ) := by
    filter_upwards [Measure.ae_ne volume (0 : ℂ)] with t ht
    exact Complex.ext (by simp) (by simp [hf t ht])
  rw [integral_congr_ae h, integral_complex_ofReal]
  simp

theorem levelZero_im_eq_zero : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base H → KB.CutWord P p.l0 w → (p.RR H 0 w [] []).im = 0 := by
  intro hP Wp Wq _ _ _ _ _ _ P p Cb H w hD hH hw
  have key : ∀ (n j : ℕ), j + n = P.r + 1 → ∀ c : Fin j → ℂ, (∀ l, c l ≠ 0) →
      (p.RR H j w (List.ofFn fun l => ((1 : ℕ), c l)) (List.ofFn fun l => ((1 : ℕ), c l))).im = 0 := by
    intro n
    induction n with
    | zero =>
      intro j hj c hc
      obtain rfl : j = P.r + 1 := hj
      exact (GlobalTheory.T.topDensity_bigCell_eq_prod_levelWeights_mul_topForm Wp Wq P p H w c hc).2.1
    | succ n ih =>
      intro j hj c hc
      rw [(GlobalTheory.T.levelModuleForm_eq_integral_of_compactCoeff hP Wp Wq P p Cb H w j _ hD hH hw (by omega) (isLocPt_ofFn c hc)).2]
      refine integral_im_eq_zero fun t ht => ?_
      have h := ih (j + 1) (by omega) (Fin.snoc c t) (fun l => by
        refine Fin.lastCases ?_ (fun i => ?_) l
        · simpa using ht
        · simpa using hc i)
      rw [ofFn_snoc] at h
      simp [Complex.mul_im, h]
  simpa using key (P.r + 1) 0 (by omega) (fun l => l.elim0) (fun l => l.elim0)

end GlobalTheory.LevelFormsReal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroFormDiagonalBigCellImEqZeroStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelZeroForm_diagonal_bigCell_im_eq_zero : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base H → KB.CutWord P p.l0 w → (p.RR H 0 w [] []).im = 0 := by
  first | exact @GlobalTheory.LevelFormsReal.levelZero_im_eq_zero | exact GlobalTheory.LevelFormsReal.levelZero_im_eq_zero | (intros; apply GlobalTheory.LevelFormsReal.levelZero_im_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MeasurePreservingSnocMeasurableEquiv
open MeasureTheory Filter Topology

namespace GlobalTheory

noncomputable def snocMeasurableEquiv (n : ℕ) : ((Fin n → ℂ) × ℂ) ≃ᵐ (Fin (n + 1) → ℂ) :=
  MeasurableEquiv.prodComm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) (Fin.last n)).symm

lemma snocMeasurableEquiv_apply (n : ℕ) (p : (Fin n → ℂ) × ℂ) :
    snocMeasurableEquiv n p = Fin.snoc (α := fun _ => ℂ) p.1 p.2 := by
  simp [snocMeasurableEquiv, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm,
    Fin.insertNthEquiv, Fin.insertNth_last']

lemma measurePreserving_snocMeasurableEquiv (n : ℕ) :
    MeasurePreserving (snocMeasurableEquiv n)
      ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) volume := by
  have h1 := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) (Fin.last n)).symm
  have h2 : MeasurePreserving (MeasurableEquiv.prodComm : ((Fin n → ℂ) × ℂ) ≃ᵐ (ℂ × (Fin n → ℂ)))
      ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ))
      ((volume : Measure ℂ).prod (volume : Measure (Fin n → ℂ))) :=
    Measure.measurePreserving_swap
  exact h2.trans h1

lemma ae_coords_ne_zero (n : ℕ) : ∀ᵐ c : Fin n → ℂ, ∀ i, c i ≠ 0 := by
  rw [ae_all_iff]
  intro i
  exact Measure.ae_eval_ne (fun _ : Fin n => (volume : Measure ℂ)) i 0

theorem iterated_integral_eq_integral_pi :
    ∀ (n : ℕ) (W : ℕ → ℂ → ℝ) (R : (j : ℕ) → (Fin j → ℂ) → ℝ), (∀ j t, 0 ≤ W j t) → (∀ c : Fin n → ℂ, (∀ i, c i ≠ 0) → 0 ≤ R n c) → AEMeasurable (fun c : Fin n → ℂ => (∏ i : Fin n, W ((i : ℕ) + 1) (c i)) * R n c) → (∀ j, j < n → ∀ c : Fin j → ℂ, (∀ i, c i ≠ 0) → Integrable (fun t : ℂ => W (j + 1) t * R (j + 1) (Fin.snoc c t)) ∧ R j c = ∫ t : ℂ, W (j + 1) t * R (j + 1) (Fin.snoc c t)) → Integrable (fun c : Fin n → ℂ => (∏ i : Fin n, W ((i : ℕ) + 1) (c i)) * R n c) ∧ R 0 (fun i => i.elim0) = ∫ c : Fin n → ℂ, (∏ i : Fin n, W ((i : ℕ) + 1) (c i)) * R n c := by
  intro n W R hW
  induction n with
  | zero =>
    intro _ _ _
    refine ⟨Integrable.of_finite, ?_⟩
    rw [integral_unique]
    have : (volume : Measure (Fin 0 → ℂ)).real Set.univ = 1 := by
      simp [Measure.real, volume_pi, Measure.pi_univ]
    rw [this]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, smul_eq_mul]
    exact congrArg _ (Subsingleton.elim _ _)
  | succ n ih =>
    intro hR hm hstep
    have hmp := measurePreserving_snocMeasurableEquiv n
    set T : (Fin (n + 1) → ℂ) → ℝ :=
      fun c => (∏ i : Fin (n + 1), W ((i : ℕ) + 1) (c i)) * R (n + 1) c with hT
    set F : (Fin n → ℂ) × ℂ → ℝ := fun p => T (snocMeasurableEquiv n p) with hF
    have hFm : AEStronglyMeasurable F
        ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) :=
      (hm.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving).aestronglyMeasurable
    have hFeq : ∀ (c : Fin n → ℂ) (t : ℂ), F (c, t) =
        (∏ i : Fin n, W ((i : ℕ) + 1) (c i)) *
          (W (n + 1) t * R (n + 1) (Fin.snoc (α := fun _ => ℂ) c t)) := by
      intro c t
      simp only [hF, hT, snocMeasurableEquiv_apply, Fin.prod_univ_castSucc, Fin.snoc_castSucc,
        Fin.snoc_last, Fin.val_castSucc, Fin.val_last, mul_assoc]
    have hpos : ∀ c : Fin n → ℂ, (∀ i, c i ≠ 0) → ∀ᵐ t : ℂ,
        0 ≤ W (n + 1) t * R (n + 1) (Fin.snoc (α := fun _ => ℂ) c t) := by
      intro c hc
      have h0 : ∀ᵐ t : ℂ, t ≠ 0 := by
        simp [ae_iff]
      filter_upwards [h0] with t ht
      refine mul_nonneg (hW _ _) (hR _ ?_)
      intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa using ht
      · simpa using hc i
    have hslice : ∀ c : Fin n → ℂ, (∀ i, c i ≠ 0) →
        ∫ t, F (c, t) = (∏ i : Fin n, W ((i : ℕ) + 1) (c i)) * R n c := by
      intro c hc
      simp only [hFeq]
      rw [integral_const_mul, (hstep n (Nat.lt_succ_self n) c hc).2]
    have hae : (fun c => ∫ t, F (c, t)) =ᵐ[volume]
        fun c : Fin n → ℂ => (∏ i : Fin n, W ((i : ℕ) + 1) (c i)) * R n c := by
      filter_upwards [ae_coords_ne_zero n] with c hc using hslice c hc
    obtain ⟨hint, heq⟩ := ih
      (fun c hc => by
        rw [(hstep n (Nat.lt_succ_self n) c hc).2]
        exact integral_nonneg_of_ae (hpos c hc))
      (hFm.integral_prod_right'.aemeasurable.congr hae)
      (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
    have hFi : Integrable F ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℂ)) := by
      rw [integrable_prod_iff hFm]
      constructor
      · filter_upwards [ae_coords_ne_zero n] with c hc
        simp only [hFeq]
        exact (hstep n (Nat.lt_succ_self n) c hc).1.const_mul _
      · refine hint.congr ?_
        filter_upwards [ae_coords_ne_zero n] with c hc
        rw [← hslice c hc]
        refine integral_congr_ae ?_
        filter_upwards [hpos c hc] with t ht
        rw [Real.norm_of_nonneg]
        rw [hFeq]
        exact mul_nonneg (Finset.prod_nonneg fun i _ => hW _ _) ht
    refine ⟨?_, ?_⟩
    · exact (hmp.integrable_comp_emb (snocMeasurableEquiv n).measurableEmbedding).1 hFi
    · rw [heq, ← hmp.integral_comp' T, ← integral_congr_ae hae]
      exact (integral_prod F hFi).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroFormEqBigCellIntegralTopDensityCompact
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

lemma levWeight_nonneg (P : M.Par) (j : ℕ) (t : ℂ) : 0 ≤ KB.levW P j t := by
  unfold KB.levW
  split_ifs
  · exact Formalism.FourierDecayAlt.P.JCx2.rb_zWeight_nonneg _ _ _ _
  · positivity

lemma ofFn_snoc_unit {j : ℕ} (c : Fin j → ℂ) (t : ℂ) :
    (List.ofFn fun l : Fin (j + 1) => ((1 : ℕ), Fin.snoc (α := fun _ => ℂ) c t l)) =
      (List.ofFn fun l : Fin j => ((1 : ℕ), c l)) ++ [((1 : ℕ), t)] := by
  rw [List.ofFn_succ']
  simp

lemma isLocPt_ofFn_unit {j : ℕ} (c : Fin j → ℂ) (hc : ∀ i, c i ≠ 0) :
    D.IsLocPt (List.ofFn fun l : Fin j => ((1 : ℕ), c l)) j := by
  refine ⟨?_, ?_⟩
  · intro b hb
    rw [List.mem_ofFn] at hb
    obtain ⟨i, rfl⟩ := hb
    exact ⟨le_rfl, hc i⟩
  · simp [D.ptSize, List.map_ofFn, List.sum_ofFn]

theorem levelZero_eq_integral_topVector_of_cpt :
    P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base H → KB.CutWord P p.l0 w → MemLp (tv p H w) 2 volume ∧ B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) (H) w) H = ((∫ c, ‖tv p H w c‖ ^ 2 : ℝ) : ℂ) := by
  intro hP Wp Wq _ _ _ _ _ _ P p Cb H w hD hH hw
  have hmeas := GlobalTheory.T.aestronglyMeasurable_topVector_smoothCoefficient Wp Wq P p Cb H w hD hw hH.1
  set R : (j : ℕ) → (Fin j → ℂ) → ℝ := fun j c =>
    (p.RR H j w (List.ofFn fun l : Fin j => ((1 : ℕ), c l)) (List.ofFn fun l : Fin j => ((1 : ℕ), c l))).re with hR
  have hae : (fun c : Fin (P.r + 1) → ℂ => (∏ i : Fin (P.r + 1), KB.levW P ((i : ℕ) + 1) (c i)) * R (P.r + 1) c)
      =ᵐ[volume] fun c => ‖tv p H w c‖ ^ 2 := by
    filter_upwards [GlobalTheory.ae_coords_ne_zero (P.r + 1)] with c hc
    rw [← GlobalTheory.TopVec.Ew_eq_norm_tv_sq Wp Wq P p H w c, (GlobalTheory.T.topDensity_bigCell_eq_prod_levelWeights_mul_topForm Wp Wq P p H w c hc).1]
    rfl
  obtain ⟨hint, heq⟩ := GlobalTheory.iterated_integral_eq_integral_pi (P.r + 1) (KB.levW P) R (levWeight_nonneg P)
    (fun c hc => (GlobalTheory.T.topDensity_bigCell_eq_prod_levelWeights_mul_topForm Wp Wq P p H w c hc).2.2)
    ((hmeas.norm.pow 2).aemeasurable.congr hae.symm)
    (fun j hj c hc => by
      obtain ⟨h1, h2⟩ := GlobalTheory.T.levelModuleForm_eq_integral_of_compactCoeff hP Wp Wq P p Cb H w j _ hD hH hw (Nat.lt_succ_iff.1 hj)
        (isLocPt_ofFn_unit c hc)
      have h3 := h1.re
      have h4 := integral_re h1
      simp only [RCLike.re_to_complex, Complex.re_ofReal_mul] at h3 h4
      simp only [hR, ofFn_snoc_unit]
      exact ⟨h3, by rw [h4, ← h2]⟩)
  refine ⟨(memLp_two_iff_integrable_sq_norm hmeas).2 (hint.congr hae), ?_⟩
  rw [← integral_congr_ae hae, ← heq]
  have him := GlobalTheory.T.levelZeroForm_diagonal_bigCell_im_eq_zero hP Wp Wq P p Cb H w hD hH hw
  have h0 : p.RR H 0 w [] [] = B.beta p.T.base
      (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) (H) w) H := by
    unfold KB.Pl.RR
    rw [Formalism.FourierDecayAlt.P.level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hH.1 (Formalism.FourierDecayAlt.P.CutBP.good_positioned_of_cut hw)]
    rfl
  rw [← h0]
  apply Complex.ext
  · simp [hR]
  · simpa using him

end GlobalTheory.TopVec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroFormEqBigCellIntegralTopDensityCompactStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelZeroForm_eq_bigCell_integral_topDensity_compact : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base H → KB.CutWord P p.l0 w → MemLp (tv p H w) 2 volume ∧ B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) (H) w) H = ((∫ c, ‖tv p H w c‖ ^ 2 : ℝ) : ℂ) := by
  first | exact @GlobalTheory.TopVec.levelZero_eq_integral_topVector_of_cpt | exact GlobalTheory.TopVec.levelZero_eq_integral_topVector_of_cpt | (intros; apply GlobalTheory.TopVec.levelZero_eq_integral_topVector_of_cpt <;> assumption)
end
