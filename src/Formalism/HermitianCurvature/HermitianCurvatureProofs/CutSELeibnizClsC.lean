module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEWaveJc
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEPairAtDeriv

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSELeibnizCls
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEOuterLeib
open MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

theorem norm_wl_le (A B : ℂ) : ‖wl A B‖ ≤ ‖A‖ + ‖B‖ := by
  unfold wl
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · refine le_trans (norm_smul_le _ _) ?_
    calc ‖A‖ * ‖ContinuousLinearMap.id ℝ ℂ‖ ≤ ‖A‖ * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
      _ = ‖A‖ := mul_one _
  · refine le_trans (norm_smul_le _ _) ?_
    calc ‖B‖ * ‖Complex.conjCLE.toContinuousLinearMap‖ ≤ ‖B‖ * 1 :=
          mul_le_mul_of_nonneg_left (le_of_eq Complex.conjCLE_norm) (norm_nonneg _)
      _ = ‖B‖ := mul_one _

theorem integral_wl {α : Type*} [MeasurableSpace α] {ν : Measure α} {f g : α → ℂ} (hf : Integrable f ν)
    (hg : Integrable g ν) : ∫ x, wl (f x) (g x) ∂ν = wl (∫ x, f x ∂ν) (∫ x, g x ∂ν) := by
  unfold wl
  rw [integral_add (hf.smul_const _) (hg.smul_const _), integral_smul_const, integral_smul_const]

theorem aesm_wl {α : Type*} [MeasurableSpace α] {ν : Measure α} {f g : α → ℂ} (hf : AEStronglyMeasurable f ν)
    (hg : AEStronglyMeasurable g ν) : AEStronglyMeasurable (fun x => wl (f x) (g x)) ν := by
  unfold wl
  exact (hf.smul_const _).add (hg.smul_const _)

section Fin

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem slDom_fin {ι : Type*} [Fintype ι] (μ : Measure (Mt k r)) (l : Fin r) (c : Fin r → ℂ)
    (Φ : ι → RadSp k r z z' π π') (h : ∀ i, SlDom μ l c (Φ i)) (t0 : ℂ) (ht0 : t0 ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ F : Cf r l.succ → ℝ, Integrable F ∧ ∀ s ∈ Metric.ball t0 ε, ∀ c' i,
      ‖wtI l.succ c' * pairAt μ (Φ i) (Φ i) (glue l.succ (Function.update c l s) c')‖ ≤ F c' := by
  choose ε hε F hF hb using fun i => h i t0 ht0
  have hF0 : ∀ i c', 0 ≤ F i c' := fun i c' => (norm_nonneg _).trans (hb i t0 (Metric.mem_ball_self (hε i)) c')
  have hS : 0 ≤ ∑ i, 1 / ε i := Finset.sum_nonneg fun i _ => (one_div_pos.mpr (hε i)).le
  have hpos : 0 < 1 + ∑ i, 1 / ε i := by linarith
  refine ⟨1 / (1 + ∑ i, 1 / ε i), div_pos one_pos hpos, fun c' => ∑ i, F i c',
    integrable_finsetSum _ fun i _ => hF i, ?_⟩
  intro s hs c' i
  have hle : 1 / (1 + ∑ i, 1 / ε i) ≤ ε i := by
    rw [div_le_iff₀ hpos]
    have h1 : 1 / ε i ≤ ∑ j, 1 / ε j :=
      Finset.single_le_sum (f := fun j => 1 / ε j) (fun j _ => (one_div_pos.mpr (hε j)).le) (Finset.mem_univ i)
    have h2 : ε i * (1 / ε i) = 1 := by field_simp [(hε i).ne']
    calc (1 : ℝ) = ε i * (1 / ε i) := h2.symm
      _ ≤ ε i * ∑ j, 1 / ε j := mul_le_mul_of_nonneg_left h1 (hε i).le
      _ ≤ ε i * (1 + ∑ j, 1 / ε j) := by nlinarith [hε i]
  refine (hb i s (Metric.ball_subset_ball hle hs) c').trans ?_
  exact Finset.single_le_sum (f := fun j => F j c') (fun j _ => hF0 j c') (Finset.mem_univ i)

theorem level_l2_of_slice_domination (μ : Measure (Mt k r)) [SFinite μ] (l : Fin r) (c : Fin r → ℂ) {Φ : RadSp k r z z' π π'}
    (h : SlDom μ l c Φ) {t : ℂ} (ht : t ≠ 0) : LevelSquareIntegrable μ l.succ Φ (Function.update c l t) := by
  obtain ⟨ε, hε, F, hF, hb⟩ := h t ht
  exact hF.mono' ((wtI_measurable _).aestronglyMeasurable.mul (pairAt_measI μ _ Φ Φ _).aestronglyMeasurable)
    (Eventually.of_forall fun c' => hb t (Metric.mem_ball_self hε) c')

theorem wOp_nil (X : ActualOps k r z z' π π') (l : Fin r) (Φ : RadSp k r z z' π π') : wOp X l [] Φ = Φ := by
  simp [wOp]

theorem wOp_dT (X : ActualOps k r z z' π π') (l : Fin r) (Φ : RadSp k r z z' π π') :
    wOp X l [2, 0] Φ = dT X l Φ := by
  simp [wOp, dT]

theorem wOp_dTb (X : ActualOps k r z z' π π') (l : Fin r) (Φ : RadSp k r z z' π π') :
    wOp X l [5, 3] Φ = dTb X l Φ := by
  simp [wOp, dTb]

theorem dT_lc_OuterLeib (X : ActualOps k r z z' π π') (l : Fin r) {Φ : RadSp k r z z' π π'} (h : Φ ∈ lcSub k r z z' π π') :
    dT X l Φ ∈ lcSub k r z z' π π' :=
  op_lc X l 2 _ (op_lc X l 0 _ h)

theorem dTb_lc_OuterLeib (X : ActualOps k r z z' π π') (l : Fin r) {Φ : RadSp k r z z' π π'} (h : Φ ∈ lcSub k r z z' π π') :
    dTb X l Φ ∈ lcSub k r z z' π π' :=
  op_lc X l 5 _ (op_lc X l 3 _ h)

theorem norm_wpair_le (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) {Φ Ψ : RadSp k r z z' π π'}
    (hΦ : Φ ∈ lcSub k r z z' π π') (hΨ : Ψ ∈ lcSub k r z z' π π') (w : ℂ) (p : Fin r → ℂ) :
    ‖w * pairAt μ Φ Ψ p‖ ≤ ‖w * pairAt μ Φ Φ p‖ + ‖w * pairAt μ Ψ Ψ p‖ := by
  rw [norm_mul, norm_mul, norm_mul, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_pairAt_leI μ hμ hΦ hΨ p) (norm_nonneg _)

end Fin

theorem outerLeib_of (hP : PairAtDeriv) : OuterLeib := by
  intro k r z z' Wp Wq _ _ _ _ _ _ π π' X μ hμ l S _ _ u v c hc hu hv t ht
  have : SFinite μ := sfinite_of_isHaarOn _ μ hμ

  let Φs : Ix S × Fin 6 → RadSp k r z z' π π' := fun q =>
    ![u q.1, v q.1, dT X l (u q.1), dTb X l (u q.1), dT X l (v q.1), dTb X l (v q.1)] q.2
  have hΦs : ∀ q, SlDom μ l c (Φs q) := by
    rintro ⟨a, j⟩
    fin_cases j
    · simpa [Φs, wOp_nil] using (hu a).2 []
    · simpa [Φs, wOp_nil] using (hv a).2 []
    · simpa [Φs, wOp_dT] using (hu a).2 [2, 0]
    · simpa [Φs, wOp_dTb] using (hu a).2 [5, 3]
    · simpa [Φs, wOp_dT] using (hv a).2 [2, 0]
    · simpa [Φs, wOp_dTb] using (hv a).2 [5, 3]
  obtain ⟨ε0, hε0, F, hF, hb⟩ := slDom_fin μ l c Φs hΦs t ht
  have hF0 : ∀ c', 0 ≤ F c' := fun c' =>
    (norm_nonneg _).trans (hb t (Metric.mem_ball_self hε0) c' (Classical.arbitrary _))

  have lu : ∀ a, u a ∈ lcSub k r z z' π π' := fun a => (hu a).1
  have lv : ∀ a, v a ∈ lcSub k r z z' π π' := fun a => (hv a).1

  have Iu : ∀ a (js : List (Fin 6)) s, s ≠ 0 → LevelSquareIntegrable μ l.succ (wOp X l js (u a)) (Function.update c l s) :=
    fun a js s hs => level_l2_of_slice_domination μ l c ((hu a).2 js) hs
  have Iv : ∀ a (js : List (Fin 6)) s, s ≠ 0 → LevelSquareIntegrable μ l.succ (wOp X l js (v a)) (Function.update c l s) :=
    fun a js s hs => level_l2_of_slice_domination μ l c ((hv a).2 js) hs
  have I0u : ∀ a s, s ≠ 0 → LevelSquareIntegrable μ l.succ (u a) (Function.update c l s) := fun a s hs => by
    simpa [wOp_nil] using Iu a [] s hs
  have I0v : ∀ a s, s ≠ 0 → LevelSquareIntegrable μ l.succ (v a) (Function.update c l s) := fun a s hs => by
    simpa [wOp_nil] using Iv a [] s hs
  have ITu : ∀ a s, s ≠ 0 → LevelSquareIntegrable μ l.succ (dT X l (u a)) (Function.update c l s) := fun a s hs => by
    simpa [wOp_dT] using Iu a [2, 0] s hs
  have ITv : ∀ a s, s ≠ 0 → LevelSquareIntegrable μ l.succ (dT X l (v a)) (Function.update c l s) := fun a s hs => by
    simpa [wOp_dT] using Iv a [2, 0] s hs
  have IBu : ∀ a s, s ≠ 0 → LevelSquareIntegrable μ l.succ (dTb X l (u a)) (Function.update c l s) := fun a s hs => by
    simpa [wOp_dTb] using Iu a [5, 3] s hs
  have IBv : ∀ a s, s ≠ 0 → LevelSquareIntegrable μ l.succ (dTb X l (v a)) (Function.update c l s) := fun a s hs => by
    simpa [wOp_dTb] using Iv a [5, 3] s hs

  set A : Ix S → ℂ → Cf r l.succ → ℂ := fun a s c' =>
    pairAt μ (dT X l (u a)) (v a) (glue l.succ (Function.update c l s) c') +
      pairAt μ (u a) (dTb X l (v a)) (glue l.succ (Function.update c l s) c') with hA
  set Bf : Ix S → ℂ → Cf r l.succ → ℂ := fun a s c' =>
    pairAt μ (dTb X l (u a)) (v a) (glue l.succ (Function.update c l s) c') +
      pairAt μ (u a) (dT X l (v a)) (glue l.succ (Function.update c l s) c') with hB
  set F0 : ℂ → Cf r l.succ → ℂ := fun s c' =>
    wtI l.succ c' * ∑ a, pairAt μ (u a) (v a) (glue l.succ (Function.update c l s) c') with hF0def
  set F' : ℂ → Cf r l.succ → (ℂ →L[ℝ] ℂ) := fun s c' =>
    wl (wtI l.succ c' * ∑ a, A a s c') (wtI l.succ c' * ∑ a, Bf a s c') with hF'def
  have hε : 0 < min ε0 ‖t‖ := lt_min hε0 (norm_pos_iff.mpr ht)
  have hne : ∀ s ∈ Metric.ball t (min ε0 ‖t‖), s ≠ 0 := by
    intro s hs h0
    rw [h0, Metric.mem_ball, dist_zero_left] at hs
    exact (lt_irrefl _ (hs.trans_le (min_le_right _ _)))
  have hball : ∀ s ∈ Metric.ball t (min ε0 ‖t‖), s ∈ Metric.ball t ε0 := fun s hs =>
    Metric.ball_subset_ball (min_le_left _ _) hs

  have intF0 : ∀ s, s ≠ 0 → Integrable (F0 s) :=
    fun s hs => formIntOuter_of_l2I μ hμ l.succ u v lu lv (Function.update c l s) (fun a => I0u a s hs)
      (fun a => I0v a s hs)
  have hA1 := formIntOuter_of_l2I μ hμ l.succ (fun a => dT X l (u a)) v (fun a => dT_lc_OuterLeib X l (lu a)) lv
    (Function.update c l t) (fun a => ITu a t ht) (fun a => I0v a t ht)
  have hA2 := formIntOuter_of_l2I μ hμ l.succ u (fun a => dTb X l (v a)) lu (fun a => dTb_lc_OuterLeib X l (lv a))
    (Function.update c l t) (fun a => I0u a t ht) (fun a => IBv a t ht)
  have hB1 := formIntOuter_of_l2I μ hμ l.succ (fun a => dTb X l (u a)) v (fun a => dTb_lc_OuterLeib X l (lu a)) lv
    (Function.update c l t) (fun a => IBu a t ht) (fun a => I0v a t ht)
  have hB2 := formIntOuter_of_l2I μ hμ l.succ u (fun a => dT X l (v a)) lu (fun a => dT_lc_OuterLeib X l (lv a))
    (Function.update c l t) (fun a => I0u a t ht) (fun a => ITv a t ht)
  have intA : Integrable (fun c' => wtI l.succ c' * ∑ a, A a t c') := by
    refine (hA1.add hA2).congr (Eventually.of_forall fun c' => ?_)
    simp only [hA, Pi.add_apply, Finset.sum_add_distrib, mul_add, wtI]
  have intB : Integrable (fun c' => wtI l.succ c' * ∑ a, Bf a t c') := by
    refine (hB1.add hB2).congr (Eventually.of_forall fun c' => ?_)
    simp only [hB, Pi.add_apply, Finset.sum_add_distrib, mul_add, wtI]
  have hIA : ∫ c', wtI l.succ c' * ∑ a, A a t c' =
      form μ l.succ (fun b => dT X l (u b)) v (Function.update c l t) +
        form μ l.succ u (fun b => dTb X l (v b)) (Function.update c l t) := by
    unfold form
    rw [← integral_add hA1 hA2]
    refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
    simp only [hA, Finset.sum_add_distrib, mul_add, wtI]
  have hIB : ∫ c', wtI l.succ c' * ∑ a, Bf a t c' =
      form μ l.succ (fun b => dTb X l (u b)) v (Function.update c l t) +
        form μ l.succ u (fun b => dT X l (v b)) (Function.update c l t) := by
    unfold form
    rw [← integral_add hB1 hB2]
    refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
    simp only [hB, Finset.sum_add_distrib, mul_add, wtI]
  have key : HasFDerivAt (fun s => ∫ c', F0 s c') (∫ c', F' t c') t := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le
      (bound := fun c' => 8 * (Fintype.card (Ix S) : ℝ) * F c') (Metric.ball_mem_nhds t hε) ?_ (intF0 t ht)
      (aesm_wl intA.aestronglyMeasurable intB.aestronglyMeasurable) ?_ (hF.const_mul _) ?_
    · exact Filter.eventually_of_mem (Metric.ball_mem_nhds t hε) fun s hs =>
        (intF0 s (hne s hs)).aestronglyMeasurable
    · refine Eventually.of_forall fun c' s hs => ?_
      have hs' := hball s hs
      have hd : ∀ a j, ‖wtI l.succ c' * pairAt μ (Φs (a, j)) (Φs (a, j)) (glue l.succ (Function.update c l s) c')‖
          ≤ F c' := fun a j => hb s hs' c' (a, j)
      have hAa : ∀ a, ‖wtI l.succ c' * A a s c'‖ ≤ 4 * F c' := by
        intro a
        have e0 : ‖wtI l.succ c' * pairAt μ (u a) (u a) (glue l.succ (Function.update c l s) c')‖ ≤ F c' := hd a 0
        have e1 : ‖wtI l.succ c' * pairAt μ (v a) (v a) (glue l.succ (Function.update c l s) c')‖ ≤ F c' := hd a 1
        have e2 : ‖wtI l.succ c' * pairAt μ (dT X l (u a)) (dT X l (u a)) (glue l.succ (Function.update c l s) c')‖
            ≤ F c' := hd a 2
        have e5 : ‖wtI l.succ c' * pairAt μ (dTb X l (v a)) (dTb X l (v a)) (glue l.succ (Function.update c l s) c')‖
            ≤ F c' := hd a 5
        have p1 := norm_wpair_le μ hμ (dT_lc_OuterLeib X l (lu a)) (lv a) (wtI l.succ c') (glue l.succ (Function.update c l s) c')
        have p2 := norm_wpair_le μ hμ (lu a) (dTb_lc_OuterLeib X l (lv a)) (wtI l.succ c') (glue l.succ (Function.update c l s) c')
        have : ‖wtI l.succ c' * A a s c'‖ ≤
            ‖wtI l.succ c' * pairAt μ (dT X l (u a)) (v a) (glue l.succ (Function.update c l s) c')‖ +
            ‖wtI l.succ c' * pairAt μ (u a) (dTb X l (v a)) (glue l.succ (Function.update c l s) c')‖ := by
          simp only [hA, mul_add]; exact norm_add_le _ _
        linarith
      have hBa : ∀ a, ‖wtI l.succ c' * Bf a s c'‖ ≤ 4 * F c' := by
        intro a
        have e0 : ‖wtI l.succ c' * pairAt μ (u a) (u a) (glue l.succ (Function.update c l s) c')‖ ≤ F c' := hd a 0
        have e1 : ‖wtI l.succ c' * pairAt μ (v a) (v a) (glue l.succ (Function.update c l s) c')‖ ≤ F c' := hd a 1
        have e3 : ‖wtI l.succ c' * pairAt μ (dTb X l (u a)) (dTb X l (u a)) (glue l.succ (Function.update c l s) c')‖
            ≤ F c' := hd a 3
        have e4 : ‖wtI l.succ c' * pairAt μ (dT X l (v a)) (dT X l (v a)) (glue l.succ (Function.update c l s) c')‖
            ≤ F c' := hd a 4
        have p1 := norm_wpair_le μ hμ (dTb_lc_OuterLeib X l (lu a)) (lv a) (wtI l.succ c') (glue l.succ (Function.update c l s) c')
        have p2 := norm_wpair_le μ hμ (lu a) (dT_lc_OuterLeib X l (lv a)) (wtI l.succ c') (glue l.succ (Function.update c l s) c')
        have : ‖wtI l.succ c' * Bf a s c'‖ ≤
            ‖wtI l.succ c' * pairAt μ (dTb X l (u a)) (v a) (glue l.succ (Function.update c l s) c')‖ +
            ‖wtI l.succ c' * pairAt μ (u a) (dT X l (v a)) (glue l.succ (Function.update c l s) c')‖ := by
          simp only [hB, mul_add]; exact norm_add_le _ _
        linarith
      have sA : ‖wtI l.succ c' * ∑ a, A a s c'‖ ≤ (Fintype.card (Ix S) : ℝ) * (4 * F c') := by
        rw [Finset.mul_sum]
        refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun a _ => hAa a).trans ?_)
        simp
      have sB : ‖wtI l.succ c' * ∑ a, Bf a s c'‖ ≤ (Fintype.card (Ix S) : ℝ) * (4 * F c') := by
        rw [Finset.mul_sum]
        refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun a _ => hBa a).trans ?_)
        simp
      calc ‖F' s c'‖ ≤ ‖wtI l.succ c' * ∑ a, A a s c'‖ + ‖wtI l.succ c' * ∑ a, Bf a s c'‖ := norm_wl_le _ _
        _ ≤ (Fintype.card (Ix S) : ℝ) * (4 * F c') + (Fintype.card (Ix S) : ℝ) * (4 * F c') := add_le_add sA sB
        _ = 8 * (Fintype.card (Ix S) : ℝ) * F c' := by ring
    · refine Eventually.of_forall fun c' s hs => ?_
      have hd : ∀ a ∈ (Finset.univ : Finset (Ix S)),
          HasFDerivAt (fun s => pairAt μ (u a) (v a) (glue l.succ (Function.update c l s) c'))
            (wl (A a s c') (Bf a s c')) s :=
        fun a _ => hP k r z z' Wp Wq π π' X μ hμ l (u a) (v a) (lu a) (lv a) c hc c' s (hne s hs)
      have hs2 := (HasFDerivAt.sum hd).const_mul (wtI l.succ c')
      have e1 : (fun x => F0 x c') = fun y => wtI l.succ c' *
          (∑ i, fun s => pairAt μ (u i) (v i) (glue l.succ (Function.update c l s) c')) y := by
        funext y
        simp only [hF0def, Finset.sum_apply]
      have e2 : F' s c' = wtI l.succ c' • ∑ i, wl (A i s c') (Bf i s c') := by
        refine ContinuousLinearMap.ext fun h => ?_
        simp only [hF'def, wl_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
          smul_eq_mul]
        have alg : ∀ (f g : Ix S → ℂ) (w h : ℂ), w * (∑ a, f a) * h + w * (∑ a, g a) * conj h =
            w * ∑ a, (f a * h + g a * conj h) := by
          intro f g w h
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
          ring
        exact alg (fun a => A a s c') (fun a => Bf a s c') _ _
      rw [e1, e2]
      exact hs2
  have hfin : ∫ c', F' t c' =
      wl (form μ l.succ (fun b => dT X l (u b)) v (Function.update c l t) +
            form μ l.succ u (fun b => dTb X l (v b)) (Function.update c l t))
        (form μ l.succ (fun b => dTb X l (u b)) v (Function.update c l t) +
            form μ l.succ u (fun b => dT X l (v b)) (Function.update c l t)) := by
    rw [← hIA, ← hIB]
    exact integral_wl intA intB
  rw [hfin] at key
  exact key

end Formalism.FourierDecayAlt.P.CutSE
end
end

open MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

section Clos

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)) (l : Fin r) (c : Fin r → ℂ)

theorem wOp_cons (j : Fin 6) (js : List (Fin 6)) (Φ : RadSp k r z z' π π') :
    wOp X l (j :: js) Φ = X.op l j (wOp X l js Φ) := by
  simp only [wOp, List.map_cons, List.prod_cons]
  rfl

theorem wOp_nil_sg (Φ : RadSp k r z z' π π') : wOp X l [] Φ = Φ := by
  simp only [wOp, List.map_nil, List.prod_nil]
  rfl

theorem wOp_op (js : List (Fin 6)) (j : Fin 6) (Φ : RadSp k r z z' π π') :
    wOp X l js (X.op l j Φ) = wOp X l (js ++ [j]) Φ := by
  simp only [wOp, List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
    List.prod_nil, _root_.mul_one]
  rfl

theorem wOp_lc (js : List (Fin 6)) : ∀ Φ ∈ lcSub k r z z' π π', wOp X l js Φ ∈ lcSub k r z z' π π' := by
  intro Φ hΦ
  induction js with
  | nil => rwa [wOp_nil_sg]
  | cons j js ih =>
    rw [wOp_cons]
    exact Formalism.FourierDecayAlt.P5.HerC.op_lc X l j _ ih

theorem slDom_zero : SlDom μ l c (0 : RadSp k r z z' π π') := by
  have hz : B.hsInner (0 : Wq →L[ℂ] Wp) 0 = 0 := by
    unfold B.hsInner
    rw [show B.hsVec (0 : Wq →L[ℂ] Wp) = 0 from map_zero hsVecLin, inner_zero_left]
  have h0 : ∀ p : Fin r → ℂ, pairAt μ (0 : RadSp k r z z' π π') 0 p = 0 := fun p => by
    unfold pairAt
    simp only [Submodule.coe_zero, ZeroMemClass.coe_zero, Pi.zero_apply, hz, integral_zero]
  intro t0 _
  refine ⟨1, one_pos, fun _ => 0, integrable_zero _ _ _, fun t _ c' => ?_⟩
  rw [h0, mul_zero, norm_zero]

theorem slDom_add (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) {Φ Ψ : RadSp k r z z' π π'}
    (hΦ : Φ ∈ lcSub k r z z' π π') (hΨ : Ψ ∈ lcSub k r z z' π π') (h1 : SlDom μ l c Φ) (h2 : SlDom μ l c Ψ) :
    SlDom μ l c (Φ + Ψ) := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨hμ.finite_compact⟩
  haveI : SFinite μ := by
    first
      | infer_instance
      | exact (sigmaFinite_of_locallyFinite (μ := μ)).toSFinite

  have hconj : ∀ (A C : RadSp k r z z' π π') p, pairAt μ A C p = starRingEnd ℂ (pairAt μ C A p) := by
    intro A C p
    unfold pairAt
    rw [← integral_conj]
    congr 1
    funext x
    unfold B.hsInner
    rw [inner_conj_symm]
  have hpos : ∀ (A : RadSp k r z z' π π') p, ∃ s : ℝ, 0 ≤ s ∧ pairAt μ A A p = s := by
    intro A p
    refine ⟨∫ x, ‖B.hsVec ((A : Fn k r (Wq →L[ℂ] Wp)) p (Matrix.of x))‖ ^ 2 ∂μ,
      integral_nonneg fun _ => by positivity, ?_⟩
    unfold pairAt B.hsInner
    first
      | rw [← integral_complex_ofReal]
      | rw [← integral_ofReal]
      | rw [← integral_coe]
    congr 1
    funext x
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hadd : ∀ (A1 A2 C : RadSp k r z z' π π') p, A1 ∈ lcSub k r z z' π π' → A2 ∈ lcSub k r z z' π π' →
      C ∈ lcSub k r z z' π π' → pairAt μ (A1 + A2) C p = pairAt μ A1 C p + pairAt μ A2 C p :=
    fun A1 A2 C p h1 h2 h3 => pairAt_add_left_lc (μ := μ) hμ h1 h2 h3 p
  have hsub : ∀ (A1 A2 C : RadSp k r z z' π π') p, A1 ∈ lcSub k r z z' π π' → A2 ∈ lcSub k r z z' π π' →
      C ∈ lcSub k r z z' π π' → pairAt μ (A1 - A2) C p = pairAt μ A1 C p - pairAt μ A2 C p := by
    intro A1 A2 C p h1 h2 h3
    have h := hadd (A1 - A2) A2 C p (sub_mem h1 h2) h2 h3
    rw [sub_add_cancel] at h
    rw [h]
    ring
  have hkey : ∀ p, ‖pairAt μ (Φ + Ψ) (Φ + Ψ) p‖ ≤ 2 * ‖pairAt μ Φ Φ p‖ + 2 * ‖pairAt μ Ψ Ψ p‖ := by
    intro p
    have hs := hadd Φ Ψ (Φ + Ψ) p hΦ hΨ (add_mem hΦ hΨ)
    have hd := hsub Φ Ψ (Φ - Ψ) p hΦ hΨ (sub_mem hΦ hΨ)
    have e1 : pairAt μ Φ (Φ + Ψ) p = pairAt μ Φ Φ p + pairAt μ Φ Ψ p := by
      rw [hconj, hadd Φ Ψ Φ p hΦ hΨ hΦ, map_add (f := _), ← hconj, ← hconj]
    have e2 : pairAt μ Ψ (Φ + Ψ) p = pairAt μ Ψ Φ p + pairAt μ Ψ Ψ p := by
      rw [hconj, hadd Φ Ψ Ψ p hΦ hΨ hΨ, map_add (f := _), ← hconj, ← hconj]
    have e3 : pairAt μ Φ (Φ - Ψ) p = pairAt μ Φ Φ p - pairAt μ Φ Ψ p := by
      rw [hconj, hsub Φ Ψ Φ p hΦ hΨ hΦ, map_sub, ← hconj, ← hconj]
    have e4 : pairAt μ Ψ (Φ - Ψ) p = pairAt μ Ψ Φ p - pairAt μ Ψ Ψ p := by
      rw [hconj, hsub Φ Ψ Ψ p hΦ hΨ hΨ, map_sub, ← hconj, ← hconj]
    obtain ⟨s1, hs1, q1⟩ := hpos (Φ + Ψ) p
    obtain ⟨s2, hs2, q2⟩ := hpos (Φ - Ψ) p
    obtain ⟨a, ha, qa⟩ := hpos Φ p
    obtain ⟨b, hb, qb⟩ := hpos Ψ p
    have hpar : (s1 : ℂ) = 2 * a + 2 * b - s2 := by
      rw [← q1, ← q2, ← qa, ← qb, hs, hd, e1, e2, e3, e4]
      ring
    have hpar' : s1 = 2 * a + 2 * b - s2 := by exact_mod_cast hpar
    rw [q1, qa, qb, Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hs1,
      Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    linarith
  intro t0 ht0
  obtain ⟨ε1, hε1, F1, hF1, hb1⟩ := h1 t0 ht0
  obtain ⟨ε2, hε2, F2, hF2, hb2⟩ := h2 t0 ht0
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun c' => 2 * F1 c' + 2 * F2 c', (hF1.const_mul 2).add (hF2.const_mul 2),
    fun t ht c' => ?_⟩
  have ht1 : t ∈ Metric.ball t0 ε1 := Metric.ball_subset_ball (min_le_left _ _) ht
  have ht2 : t ∈ Metric.ball t0 ε2 := Metric.ball_subset_ball (min_le_right _ _) ht
  have k1 := hb1 t ht1 c'
  have k2 := hb2 t ht2 c'
  rw [norm_mul] at k1 k2 ⊢
  have hk := hkey (glue l.succ (Function.update c l t) c')
  have hw := norm_nonneg (wtI l.succ c')
  nlinarith [mul_le_mul_of_nonneg_left hk hw]

theorem slDom_smul (a : ℂ) {Φ : RadSp k r z z' π π'} (h : SlDom μ l c Φ) : SlDom μ l c (a • Φ) := by
  have hp : ∀ p, pairAt μ (a • Φ) (a • Φ) p = (starRingEnd ℂ a * a) * pairAt μ Φ Φ p := fun p => by
    simp only [pairAt, B.hsInner, Submodule.coe_smul, Pi.smul_apply, hsVec_smul', inner_smul_left,
      inner_smul_right]
    first
      | (rw [← integral_const_mul]; congr 1; funext x; ring)
      | (rw [← integral_mul_left]; congr 1; funext x; ring)
  intro t0 ht0
  obtain ⟨ε, hε, F, hF, hb⟩ := h t0 ht0
  refine ⟨ε, hε, fun c' => ‖a‖ ^ 2 * F c', hF.const_mul _, fun t ht c' => ?_⟩
  have e : ‖starRingEnd ℂ a * a‖ = ‖a‖ ^ 2 := by rw [norm_mul, RCLike.norm_conj, sq]
  rw [hp, show ∀ w q : ℂ, w * (starRingEnd ℂ a * a * q) = (starRingEnd ℂ a * a) * (w * q) from
    fun w q => by ring, norm_mul, e]
  exact mul_le_mul_of_nonneg_left (hb t ht c') (by positivity)

def sgSub (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) : Submodule ℂ (RadSp k r z z' π π') where
  carrier := {Φ | SliceGood X μ l c Φ}
  zero_mem' := ⟨(lcSub k r z z' π π').zero_mem, fun js => by rw [map_zero]; exact slDom_zero μ l c⟩
  add_mem' := by
    rintro Φ Ψ ⟨h1, h1'⟩ ⟨h2, h2'⟩
    refine ⟨(lcSub k r z z' π π').add_mem h1 h2, fun js => ?_⟩
    rw [map_add (f := _)]
    exact slDom_add μ l c hμ (wOp_lc X l js Φ h1) (wOp_lc X l js Ψ h2) (h1' js) (h2' js)
  smul_mem' := by
    rintro a Φ ⟨h1, h1'⟩
    refine ⟨(lcSub k r z z' π π').smul_mem a h1, fun js => ?_⟩
    rw [map_smul]
    exact slDom_smul μ l c a (h1' js)

theorem sliceGood_op {Φ : RadSp k r z z' π π'} (h : SliceGood X μ l c Φ) (j : Fin 6) :
    SliceGood X μ l c (X.op l j Φ) :=
  ⟨Formalism.FourierDecayAlt.P5.HerC.op_lc X l j Φ h.1, fun js => by rw [wOp_op]; exact h.2 _⟩

theorem sliceGood_dT {Φ : RadSp k r z z' π π'} (h : SliceGood X μ l c Φ) : SliceGood X μ l c (dT X l Φ) :=
  sliceGood_op X μ l c (sliceGood_op X μ l c h 0) 2

theorem sliceGood_dTb {Φ : RadSp k r z z' π π'} (h : SliceGood X μ l c Φ) : SliceGood X μ l c (dTb X l Φ) :=
  sliceGood_op X μ l c (sliceGood_op X μ l c h 3) 5

end Clos

theorem wirt_of_hasFDerivAt {F : ℂ → ℂ} {A B t : ℂ} (h : HasFDerivAt F (wl A B) t) :
    wirt true F t = A ∧ wirt false F t = B := by
  have hf := h.fderiv
  refine ⟨?_, ?_⟩ <;> simp [wirt, hf, wl]
  · first
      | linear_combination ((B - A) / 2) * Complex.I_sq
      | linear_combination ((A - B) / 2) * Complex.I_sq
  · first
      | linear_combination ((A - B) / 2) * Complex.I_sq
      | linear_combination ((B - A) / 2) * Complex.I_sq

theorem levelSquareIntegrable_succ_update_of_sliceGood {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
    (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)) [SFinite μ] (l : Fin r) (c : Fin r → ℂ)
    {Φ : RadSp k r z z' π π'} (h : SliceGood X μ l c Φ) {t : ℂ} (ht : t ≠ 0) :
    LevelSquareIntegrable μ l.succ Φ (Function.update c l t) := by
  have h0 := h.2 []
  rw [wOp_nil_sg] at h0
  exact level_l2_of_slice_domination μ l c h0 ht

theorem contDiffOn_inverse_norm_sq (n : ℕ) :
    ContDiffOn ℝ n (fun t : ℂ => (((‖t‖ ^ (-2 : ℤ) : ℝ)) : ℂ)) {t : ℂ | t ≠ 0} := by
  have hN : (fun t : ℂ => Complex.normSq t) = fun t => t.re * t.re + t.im * t.im :=
    funext Complex.normSq_apply
  have hq : ContDiff ℝ n (fun t : ℂ => Complex.normSq t) := by
    rw [hN]
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  have hi : ContDiffOn ℝ n (fun t : ℂ => (Complex.normSq t)⁻¹) {t : ℂ | t ≠ 0} :=
    hq.contDiffOn.inv fun t ht => by simpa [Complex.normSq_eq_zero] using ht
  refine (Complex.ofRealCLM.contDiff.comp_contDiffOn hi).congr fun t _ => ?_
  simp [zpow_neg, Complex.normSq_eq_norm_sq]

theorem form_contDiffOn (hO : OuterLeib) {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
    (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (l : Fin r)
    (S : Type) [Fintype S] [DecidableEq S] (c : Fin r → ℂ) (hc : c ∈ OmX r) (n : ℕ) :
    ∀ (u v : Ix S → RadSp k r z z' π π'), (∀ b, SliceGood X μ l c (u b)) → (∀ b, SliceGood X μ l c (v b)) →
      ContDiffOn ℝ n (fun t => form μ l.succ u v (Function.update c l t)) {t : ℂ | t ≠ 0} := by
  have hs : IsOpen {t : ℂ | t ≠ 0} := isOpen_ne

  let Lw : ℂ × ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
    (ContinuousLinearMap.fst ℝ ℂ ℂ).smulRight (ContinuousLinearMap.id ℝ ℂ) +
      (ContinuousLinearMap.snd ℝ ℂ ℂ).smulRight Complex.conjCLE.toContinuousLinearMap
  induction n with
  | zero =>
    intro u v hu hv
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun t ht => (hO k r z z' Wp Wq π π' X μ hμ l S u v c hc hu hv t ht).continuousAt.continuousWithinAt
  | succ n ih =>
    intro u v hu hv
    have hd := fun t (ht : t ∈ {t : ℂ | t ≠ 0}) => hO k r z z' Wp Wq π π' X μ hμ l S u v c hc hu hv t ht
    have hA := (ih (fun b => dT X l (u b)) v (fun b => sliceGood_dT X μ l c (hu b)) hv).add
      (ih u (fun b => dTb X l (v b)) hu (fun b => sliceGood_dTb X μ l c (hv b)))
    have hB := (ih (fun b => dTb X l (u b)) v (fun b => sliceGood_dTb X μ l c (hu b)) hv).add
      (ih u (fun b => dT X l (v b)) hu (fun b => sliceGood_dT X μ l c (hv b)))
    have hW : ContDiffOn ℝ n (fun t => wl
        (form μ l.succ (fun b => dT X l (u b)) v (Function.update c l t) +
          form μ l.succ u (fun b => dTb X l (v b)) (Function.update c l t))
        (form μ l.succ (fun b => dTb X l (u b)) v (Function.update c l t) +
          form μ l.succ u (fun b => dT X l (v b)) (Function.update c l t))) {t : ℂ | t ≠ 0} := by
      first
        | exact (Lw.contDiff.comp_contDiffOn (hA.prodMk hB)).congr fun t _ => rfl
        | exact (Lw.contDiff.comp_contDiffOn (hA.prod hB)).congr fun t _ => rfl
    have hF : ContDiffOn ℝ n (fderiv ℝ fun t => form μ l.succ u v (Function.update c l t)) {t : ℂ | t ≠ 0} :=
      hW.congr fun t ht => (hd t ht).fderiv
    rw [Nat.cast_succ]
    first
      | exact (contDiffOn_succ_iff_fderiv_of_isOpen hs).2
          ⟨fun t ht => (hd t ht).differentiableAt.differentiableWithinAt, fun h => by simp at h, hF⟩
      | exact (contDiffOn_succ_iff_fderiv_of_isOpen hs).2
          ⟨fun t ht => (hd t ht).differentiableAt.differentiableWithinAt, hF⟩

end Formalism.FourierDecayAlt.P.CutSE
end
end

open MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

theorem clsE_sliceGood_ofC (hJ : JSliceGenC) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (hD : IsData P z z' π π' X μ L st l0) (h1 : 1 ≤ l0) (h2 : l0 ≤ P.k)
    (hz : D.z = z) (hz' : D.z' = z') (hπ : D.π = π) (hπ' : D.π' = π') (l : Fin P.r) (hl : l.val = 0)
    (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r) (Φ : RadSp P.k P.r z z' π π')
    (hΦ : Φ ∈ ClsE S P z z' π π' X L st l0 D l) : SliceGood X μ l c Φ := by
  have hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ := hD.2.1
  have hle : ClsE S P z z' π π' X L st l0 D l ≤ sgSub (X := X) (μ := μ) (l := l) (c := c) hμ := by
    refine opClos_le X l ?_ ?_
    · refine le_trans (base0_le_waveJc (S := S) P z z' π π' X μ L st l0 D hD hz hz' hπ hπ' l hl) ?_
      refine Submodule.span_le.mpr ?_
      intro Ψ hΨ
      exact hJ Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl c hc Ψ hΨ
    · intro j Ψ hΨ
      have h' : SliceGood X μ l c Ψ := hΨ
      exact sliceGood_op (h := h') (j := j)
  exact hle hΦ

theorem leibnizCls_ofC (hO : OuterLeib) (hJ : JSliceGenC) : LeibnizCls := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl u v hu hv c hc t ht
  have hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ := hD.2.1
  have hsu : ∀ b, SliceGood X μ l c (u b) := fun b =>
    clsE_sliceGood_ofC hJ S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl c hc (u b) (hu b)
  have hsv : ∀ b, SliceGood X μ l c (v b) := fun b =>
    clsE_sliceGood_ofC hJ S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl c hc (v b) (hv b)
  exact wirt_of_hasFDerivAt (hO P.k P.r z z' Wp Wq π π' X μ hμ l S u v c hc hsu hsv t ht)

theorem densSmoothCls_ofC (hO : OuterLeib) (hJ : JSliceGenC) : DensSmoothCls := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl u v hu hv c hc
  have hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ := hD.2.1
  haveI : SFinite μ := Formalism.FourierDecayAlt.P5.sfinite_of_isHaarOn _ μ hμ
  have hsu : ∀ b, SliceGood X μ l c (u b) := fun b =>
    clsE_sliceGood_ofC hJ S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl c hc (u b) (hu b)
  have hsv : ∀ b, SliceGood X μ l c (v b) := fun b =>
    clsE_sliceGood_ofC hJ S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl c hc (v b) (hv b)
  refine ⟨fun n => ?_, fun t ht b => ⟨levelSquareIntegrable_succ_update_of_sliceGood X μ l c (hsu b) ht, levelSquareIntegrable_succ_update_of_sliceGood X μ l c (hsv b) ht⟩⟩
  exact (contDiffOn_inverse_norm_sq n).mul (form_contDiffOn hO X μ hμ l S c hc n u v hsu hsv)

theorem leibnizCls_of_jSliceC (hJ : JSliceGenC) : LeibnizCls :=
  leibnizCls_ofC (outerLeib_of pairing_derivative_formula) hJ

theorem densSmoothCls_of_jSliceC (hJ : JSliceGenC) : DensSmoothCls :=
  densSmoothCls_ofC (outerLeib_of pairing_derivative_formula) hJ

end Formalism.FourierDecayAlt.P.CutSE
