module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsPoint

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsFolnerConv
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

def cnt (μS : Measure G) (Ω : Set G) (q : G) : ℝ≥0∞ := μS {t | t ∈ Ω ∧ q * t ∈ Ω}

theorem cnt_measurable {μS : Measure G} [SFinite μS] {Ω : Set G} (hΩ : MeasurableSet Ω) :
    Measurable (cnt μS Ω) := by
  have hT : MeasurableSet {p : G × G | p.2 ∈ Ω ∧ p.1 * p.2 ∈ Ω} :=
    (measurable_snd hΩ).inter ((measurable_fst.mul measurable_snd) hΩ)
  exact measurable_measure_prodMk_left hT

theorem cnt_le (μS : Measure G) (Ω : Set G) (q : G) : cnt μS Ω q ≤ μS Ω := measure_mono fun t ht => ht.1

theorem conv_map {S : Set G} {μS : Measure G} [SFinite μS] (hS : IsHaarSub S μS) {Ω : Set G}
    (hΩm : MeasurableSet Ω) (hΩS : Ω ⊆ S) :
    ((μS.restrict Ω).prod (μS.restrict Ω)).map (fun p : G × G => p.1 * p.2⁻¹) = μS.withDensity (cnt μS Ω) := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, -, hright, -⟩ := hS
  have hg : Measurable (fun p : G × G => p.1 * p.2⁻¹) := measurable_fst.mul measurable_snd.inv
  ext A hA
  rw [Measure.map_apply hg hA, withDensity_apply _ hA]
  set P : Set (G × G) := {p | p.1 ∈ A ∧ p.2 ∈ Ω ∧ p.1 * p.2 ∈ Ω} with hPdef
  have hP : MeasurableSet P :=
    (measurable_fst hA).inter ((measurable_snd hΩm).inter ((measurable_fst.mul measurable_snd) hΩm))
  have h1 : (μS.prod μS) P = ∫⁻ q in A, cnt μS Ω q ∂μS := by
    rw [Measure.prod_apply hP, ← lintegral_indicator hA]
    refine lintegral_congr fun q => ?_
    rw [Set.indicator_apply]
    by_cases hq : q ∈ A
    · rw [if_pos hq]
      unfold cnt
      congr 1
      ext t
      simp [hPdef, hq]
    · rw [if_neg hq]
      have hempty : Prod.mk q ⁻¹' P = ∅ := by
        ext t
        simp [hPdef, hq]
      rw [hempty, measure_empty]
  have h2 : (μS.prod μS) P =
      ((μS.restrict Ω).prod (μS.restrict Ω)) ((fun p : G × G => p.1 * p.2⁻¹) ⁻¹' A) := by
    rw [Measure.prod_apply_symm hP, Measure.prod_apply_symm (hg hA), ← lintegral_indicator hΩm]
    refine lintegral_congr fun t => ?_
    rw [Set.indicator_apply]
    by_cases ht : t ∈ Ω
    · rw [if_pos ht]
      have hBt : MeasurableSet
          ((fun x => (x, t)) ⁻¹' ((fun p : G × G => p.1 * p.2⁻¹) ⁻¹' A)) :=
        (measurable_mul_const t⁻¹) hA
      rw [Measure.restrict_apply hBt]
      have hmt := hright t (hΩS ht)
      calc μS ((fun x => (x, t)) ⁻¹' P)
          = μS ((fun x => x * t) ⁻¹'
              ((fun x => (x, t)) ⁻¹' ((fun p : G × G => p.1 * p.2⁻¹) ⁻¹' A) ∩ Ω)) := by
            congr 1
            ext q
            simp [hPdef, ht]
        _ = (μS.map (fun x => x * t))
              ((fun x => (x, t)) ⁻¹' ((fun p : G × G => p.1 * p.2⁻¹) ⁻¹' A) ∩ Ω) :=
            (Measure.map_apply (measurable_mul_const t) (hBt.inter hΩm)).symm
        _ = μS ((fun x => (x, t)) ⁻¹' ((fun p : G × G => p.1 * p.2⁻¹) ⁻¹' A) ∩ Ω) := by
            rw [hmt]
    · rw [if_neg ht]
      have hempty : (fun x => (x, t)) ⁻¹' P = ∅ := by
        ext q
        simp [hPdef, ht]
      rw [hempty, measure_empty]
  exact h2.symm.trans h1

theorem conv_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set G} {μS : Measure G} [SFinite μS]
    (hS : IsHaarSub S μS) {Ω : Set G} (hΩm : MeasurableSet Ω) (hΩS : Ω ⊆ S) (hfin : μS Ω < ⊤) (f : G → E)
    (hf : StronglyMeasurable f)
    (hint : Integrable (fun p : G × G => f (p.1 * p.2⁻¹)) ((μS.restrict Ω).prod (μS.restrict Ω))) :
    ∫ s in Ω, ∫ t in Ω, f (s * t⁻¹) ∂μS ∂μS = ∫ q, (cnt μS Ω q).toReal • f q ∂μS := by
  have hg : Measurable (fun p : G × G => p.1 * p.2⁻¹) := measurable_fst.mul measurable_snd.inv
  have hI : Integrable (fun p : G × G => f (p.1 * p.2⁻¹)) ((μS.restrict Ω).prod (μS.restrict Ω)) := by
    assumption
  have h1 : ∫ s in Ω, ∫ t in Ω, f (s * t⁻¹) ∂μS ∂μS
      = ∫ p, f (p.1 * p.2⁻¹) ∂((μS.restrict Ω).prod (μS.restrict Ω)) :=
    (integral_prod (fun p : G × G => f (p.1 * p.2⁻¹)) hI).symm
  have h2 : ∫ p, f (p.1 * p.2⁻¹) ∂((μS.restrict Ω).prod (μS.restrict Ω))
      = ∫ q, f q ∂(((μS.restrict Ω).prod (μS.restrict Ω)).map (fun p : G × G => p.1 * p.2⁻¹)) :=
    (integral_map_of_stronglyMeasurable hg hf).symm
  rw [h1, h2, conv_map hS hΩm hΩS]
  exact integral_withDensity_eq_integral_toReal_smul (cnt_measurable hΩm)
    (ae_of_all _ fun q => (cnt_le μS Ω q).trans_lt hfin) f

end Formalism.L2.S.Pv.EnergyAbs
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsFolnerExp
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

section General

variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]

private theorem norm_eq_of_inner_self_eq_inner_self_lemma {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {a b : E} (h : ⟪a, a⟫_ℂ = ⟪b, b⟫_ℂ) : ‖a‖ = ‖b‖ := by
  have h2 : ‖a‖ ^ 2 = ‖b‖ ^ 2 := by
    have h' := h
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h'
    exact_mod_cast h'
  nlinarith [norm_nonneg a, norm_nonneg b]

end General

section Main

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

def gvec (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (x : G) :
    PiLp 2 (fun _ : Fin (Module.finrank ℂ V) => HH) :=
  WithLp.toLp 2 (fun i => ⟪W x, stdOrthonormalBasis ℂ V i⟫_ℂ • σ x w)

def Fk (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (z z' q : G) : ℂ :=
  ⟪W (q * z'), W z⟫_ℂ * ⟪σ z w, σ (q * z') w⟫_ℂ

theorem fol_rep_norm {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (x : G) (a : HH) : ‖σ x a‖ = ‖a‖ := by
  obtain ⟨-, -, hin, -⟩ := id hσ
  exact norm_eq_of_inner_self_eq_inner_self_lemma (hin x a a)

theorem fol_rep_mul {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (x y : G) (a : HH) :
    σ (x * y) a = σ x (σ y a) := by
  obtain ⟨-, hmul, -, -⟩ := id hσ
  calc σ (x * y) a = (σ x * σ y) a := by rw [hmul x y]
    _ = σ x (σ y a) := rfl

theorem W_inner_trans {S : Set G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    {s : G} (hs : s ∈ S) (x y : G) : ⟪W (s * x), W (s * y)⟫_ℂ = ⟪W x, W y⟫_ℂ := by
  rw [hWeq s hs x, hWeq s hs y, hτu s hs]

theorem W_norm_trans {S : Set G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    {s : G} (hs : s ∈ S) (x : G) : ‖W (s * x)‖ = ‖W x‖ :=
  norm_eq_of_inner_self_eq_inner_self_lemma (W_inner_trans hWeq hτu hs x x)

theorem gvec_continuous {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {W : G → V} (hWc : Continuous W) :
    Continuous (gvec σ w W) := by
  obtain ⟨-, -, -, hσc⟩ := id hσ
  have hi : ∀ i : Fin (Module.finrank ℂ V),
      Continuous fun x => ⟪W x, stdOrthonormalBasis ℂ V i⟫_ℂ • σ x w :=
    fun i => (hWc.inner continuous_const).smul (hσc w)
  show Continuous fun x =>
    (WithLp.toLp 2 (fun i => ⟪W x, stdOrthonormalBasis ℂ V i⟫_ℂ • σ x w) :
      PiLp 2 (fun _ : Fin (Module.finrank ℂ V) => HH))
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi hi)

theorem gvec_norm {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {w : HH} (hw : ‖w‖ = 1) (W : G → V) (x : G) :
    ‖gvec σ w W x‖ = ‖W x‖ := by
  have hn : ‖σ x w‖ = 1 := by rw [(fol_rep_norm hσ), hw]
  have key : ∑ i, ‖⟪W x, stdOrthonormalBasis ℂ V i⟫_ℂ‖ ^ 2 = ‖W x‖ ^ 2 := by
    exact (stdOrthonormalBasis ℂ V).sum_sq_norm_inner_left (W x)
  have hs : ‖gvec σ w W x‖ ^ 2 = ‖W x‖ ^ 2 := by
    rw [← key]
    rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_congr rfl fun i _ => by simp [gvec, norm_smul, hn]
  nlinarith [norm_nonneg (gvec σ w W x), norm_nonneg (W x)]

theorem gvec_inner (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (x y : G) :
    ⟪gvec σ w W x, gvec σ w W y⟫_ℂ = ⟪W y, W x⟫_ℂ * ⟪σ x w, σ y w⟫_ℂ := by
  have hb : ∑ i, ⟪W y, stdOrthonormalBasis ℂ V i⟫_ℂ * ⟪stdOrthonormalBasis ℂ V i, W x⟫_ℂ = ⟪W y, W x⟫_ℂ := by
    exact (stdOrthonormalBasis ℂ V).sum_inner_mul_inner (W y) (W x)
  rw [← hb, Finset.sum_mul]
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [gvec, PiLp.toLp_apply, inner_smul_left, inner_smul_right, inner_conj_symm]
  ring

theorem Fk_continuous {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {W : G → V} (hWc : Continuous W)
    {X : Type} [TopologicalSpace X] {a b c : X → G} (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    Continuous (fun x => Fk σ w W (a x) (b x) (c x)) := by
  obtain ⟨-, -, -, hσc⟩ := id hσ
  have hcb : Continuous fun x => c x * b x := hc.mul hb
  have h1 : Continuous fun x => W (c x * b x) := hWc.comp hcb
  have h2 : Continuous fun x => W (a x) := hWc.comp ha
  have h3 : Continuous fun x => σ (a x) w := (hσc w).comp ha
  have h4 : Continuous fun x => σ (c x * b x) w := (hσc w).comp hcb
  show Continuous fun x => ⟪W (c x * b x), W (a x)⟫_ℂ * ⟪σ (a x) w, σ (c x * b x) w⟫_ℂ
  exact (h1.inner h2).mul (h3.inner h4)

theorem Fk_bound {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {w : HH} (hw : ‖w‖ = 1) {S : Set G}
    {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (z z' : G) {q : G} (hq : q ∈ S) : ‖Fk σ w W z z' q‖ ≤ ‖W z‖ * ‖W z'‖ := by
  have h1 : ‖⟪W (q * z'), W z⟫_ℂ‖ ≤ ‖W z‖ * ‖W z'‖ := by
    calc ‖⟪W (q * z'), W z⟫_ℂ‖ ≤ ‖W (q * z')‖ * ‖W z‖ := norm_inner_le_norm _ _
      _ = ‖W z‖ * ‖W z'‖ := by rw [W_norm_trans hWeq hτu hq z', mul_comm]
  have h2 : ‖⟪σ z w, σ (q * z') w⟫_ℂ‖ ≤ 1 := by
    calc ‖⟪σ z w, σ (q * z') w⟫_ℂ‖ ≤ ‖σ z w‖ * ‖σ (q * z') w‖ := norm_inner_le_norm _ _
      _ = 1 := by rw [(fol_rep_norm hσ), (fol_rep_norm hσ), hw, mul_one]
  show ‖⟪W (q * z'), W z⟫_ℂ * ⟪σ z w, σ (q * z') w⟫_ℂ‖ ≤ ‖W z‖ * ‖W z'‖
  rw [norm_mul]
  calc ‖⟪W (q * z'), W z⟫_ℂ‖ * ‖⟪σ z w, σ (q * z') w⟫_ℂ‖ ≤ (‖W z‖ * ‖W z'‖) * 1 :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = ‖W z‖ * ‖W z'‖ := mul_one _

theorem kF {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {S : Set G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hSinv : ∀ a ∈ S, a⁻¹ ∈ S)
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (z z' : G) {s t : G} (hs : s ∈ S) :
    ⟪W (t⁻¹ * z'), W (s⁻¹ * z)⟫_ℂ * ⟪σ (s⁻¹ * z) w, σ (t⁻¹ * z') w⟫_ℂ = Fk σ w W z z' (s * t⁻¹) := by
  obtain ⟨-, -, hin, -⟩ := id hσ
  have e1 : ⟪W (t⁻¹ * z'), W (s⁻¹ * z)⟫_ℂ = ⟪W (s * t⁻¹ * z'), W z⟫_ℂ := by
    rw [← W_inner_trans hWeq hτu hs (t⁻¹ * z') (s⁻¹ * z), mul_assoc, mul_inv_cancel_left]
  have e2 : ⟪σ (s⁻¹ * z) w, σ (t⁻¹ * z') w⟫_ℂ = ⟪σ z w, σ (s * t⁻¹ * z') w⟫_ℂ := by
    rw [← hin s (σ (s⁻¹ * z) w) (σ (t⁻¹ * z') w), ← (fol_rep_mul hσ), ← (fol_rep_mul hσ), mul_inv_cancel_left,
      mul_assoc]
  rw [e1, e2]
  rfl

end Main

end Formalism.L2.S.Pv.EnergyAbs
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsEnergy
noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

theorem continuous_hsA_Xop {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (μS ν μS' ν' : Measure G) (d : ℝ)
    (w : HH) (W : G → V) (W' : G → V') (A A' : Set G) :
    Continuous (fun g => hsA (Xop μS ν μS' ν' σ d w W W' A A' g)) := by
  have hc : ∀ a : HH, Continuous (fun g => σ g a) := hσ.2.2.2
  unfold hsA Xop sand
  refine continuous_finsetSum _ fun i _ => ?_
  refine (continuous_norm.comp ?_).pow 2
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply]
  exact ((ContinuousLinearMap.adjoint _).continuous.comp (hc _)).const_smul _

theorem lintegral_hsA_Xop {μ : Measure G} {σ : G → (HH →L[ℂ] HH)} {d : ℝ} (hSch : IsSchur μ σ d)
    (μS ν μS' ν' : Measure G) (w : HH) (W : G → V) (W' : G → V') (A A' : Set G) :
    ∫⁻ g, ENNReal.ofReal (hsA (Xop μS ν μS' ν' σ d w W W' A A' g)) ∂μ =
      ENNReal.ofReal (d * (∑ i, ‖yv μS ν σ w W A (stdOrthonormalBasis ℂ V i)‖ ^ 2) *
        (∑ j, ‖yv μS' ν' σ w W' A' (stdOrthonormalBasis ℂ V' j)‖ ^ 2)) := by
  have hd : 0 < d := hSch.1
  have h1 : ∀ g, ENNReal.ofReal (hsA (Xop μS ν μS' ν' σ d w W W' A A' g)) =
      ENNReal.ofReal (d ^ 2) *
        ENNReal.ofReal (hsA (sand σ (Yop μS ν σ w W A) (Yop μS' ν' σ w W' A') g)) := by
    intro g
    rw [Xop, hsA_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs, ENNReal.ofReal_mul (sq_nonneg d)]
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_hsA_sand hSch,
    ← ENNReal.ofReal_mul (sq_nonneg d)]
  congr 1
  simp only [Yop_apply_basis]
  field_simp

theorem tendsto_energy {d : ℝ} (hd : 0 < d) {a b : ℕ → ℝ≥0∞} (ha : ∀ n, 0 < a n ∧ a n < ⊤)
    (hb : ∀ n, 0 < b n ∧ b n < ⊤) {N N' : ℕ → ℝ}
    (hN : Tendsto (fun n => N n / (a n).toReal) atTop (𝓝 (1 / d)))
    (hN' : Tendsto (fun n => N' n / (b n).toReal) atTop (𝓝 (1 / d))) :
    Tendsto (fun n => (a n * b n)⁻¹ * ENNReal.ofReal (d * N n * N' n)) atTop (𝓝 (ENNReal.ofReal (1 / d))) := by
  have key : ∀ n, (a n * b n)⁻¹ * ENNReal.ofReal (d * N n * N' n) =
      ENNReal.ofReal (d * (N n / (a n).toReal) * (N' n / (b n).toReal)) := by
    intro n
    obtain ⟨ha0, hat⟩ := ha n
    obtain ⟨hb0, hbt⟩ := hb n
    have ha' : 0 < (a n).toReal := ENNReal.toReal_pos ha0.ne' hat.ne
    have hb' : 0 < (b n).toReal := ENNReal.toReal_pos hb0.ne' hbt.ne
    have hab : (a n * b n)⁻¹ = ENNReal.ofReal (((a n).toReal * (b n).toReal)⁻¹) := by
      rw [ENNReal.ofReal_inv_of_pos (mul_pos ha' hb'), ← ENNReal.toReal_mul,
        ENNReal.ofReal_toReal (ENNReal.mul_ne_top hat.ne hbt.ne)]
    rw [hab, ← ENNReal.ofReal_mul (inv_nonneg.mpr (mul_pos ha' hb').le)]
    congr 1
    field_simp
  simp_rw [key]
  apply ENNReal.tendsto_ofReal
  have hlim := (hN.const_mul d).mul hN'
  rwa [show d * (1 / d) * (1 / d) = 1 / d by field_simp] at hlim

end Formalism.L2.S.Pv.EnergyAbs
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsFolner
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsFolnerSum
noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem sumsq_eq {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {w : HH} (hw : ‖w‖ = 1) {S : Set G}
    {μS ν : Measure G} (hS : IsHaarSub S μS) [SFinite ν] {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (hWc : Continuous W) (hW1 : ∫⁻ x, ‖W x‖ₑ ∂ν < ⊤) {Ω : Set G} (hΩm : MeasurableSet Ω) (hΩS : Ω ⊆ S)
    (hfin : μS Ω < ⊤) :
    ((∑ i, ‖yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V i)‖ ^ 2 : ℝ) : ℂ) =
      ∫ z, ∫ z', ∫ q, (cnt μS Ω q).toReal • Fk σ w W z z' q ∂μS ∂ν ∂ν := by
  have hS' := hS
  obtain ⟨-, -, hSmul, hSinv, hSig, -, -, -, -, -, -⟩ := hS'
  haveI : SigmaFinite μS := hSig
  haveI : IsFiniteMeasure (μS.restrict Ω) := isFiniteMeasure_restrict.mpr hfin.ne
  have hleft : ∀ (μ : Measure G) (f : G → PiLp 2 (fun _ : Fin (Module.finrank ℂ V) => HH)),
      Integrable f μ → ∀ c, ⟪∫ x, f x ∂μ, c⟫_ℂ = ∫ x, ⟪f x, c⟫_ℂ ∂μ := by
    intro μ f hf c
    rw [← inner_conj_symm, ← integral_inner hf, ← integral_conj]
    simp_rw [inner_conj_symm]
  set g := gvec σ w W with hg
  have hgc : Continuous g := gvec_continuous hσ w hWc
  have hWn : ∀ s ∈ S, ∀ x, ‖W (s * x)‖ = ‖W x‖ := by
    intro s hs x
    rw [hWeq s hs x]
    have h := hτu s hs (W x) (W x)
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h' : ‖τ s (W x)‖ ^ 2 = ‖W x‖ ^ 2 := by exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h'
  have hgn : ∀ s ∈ Ω, ∀ z, ‖g (s⁻¹ * z)‖ = ‖W z‖ := by
    intro s hs z
    rw [hg, gvec_norm hσ hw]
    exact hWn s⁻¹ (hSinv s (hΩS hs)) z
  have hgint : ∀ z, Integrable (fun s => g (s⁻¹ * z)) (μS.restrict Ω) := by
    intro z
    refine Integrable.mono' (integrable_const ‖W z‖) ?_ ?_
    · exact (hgc.comp (continuous_inv.mul continuous_const)).aestronglyMeasurable
    · exact (ae_restrict_iff' hΩm).mpr (Filter.Eventually.of_forall fun s hs => (hgn s hs z).le)
  set F : G → PiLp 2 (fun _ : Fin (Module.finrank ℂ V) => HH) :=
    fun z => ∫ s in Ω, g (s⁻¹ * z) ∂μS with hF
  have hWi : Integrable W ν := ⟨hWc.aestronglyMeasurable, hW1⟩
  have hWint : Integrable (fun z => ‖W z‖) ν := hWi.norm
  have hFint : Integrable F ν := by
    refine Integrable.mono' (hWint.const_mul (μS.real Ω)) ?_ ?_
    · have hsm : StronglyMeasurable (Function.uncurry fun (z s : G) => g (s⁻¹ * z)) := by
        apply Continuous.stronglyMeasurable
        exact hgc.comp ((continuous_snd.inv).mul continuous_fst)
      exact (hsm.integral_prod_right (ν := μS.restrict Ω)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun z => ?_
      have h1 := norm_integral_le_of_norm_le_const (μ := μS.restrict Ω) (f := fun s => g (s⁻¹ * z))
        (C := ‖W z‖) ((ae_restrict_iff' hΩm).mpr (Filter.Eventually.of_forall fun s hs => (hgn s hs z).le))
      calc ‖F z‖ ≤ ‖W z‖ * (μS.restrict Ω).real Set.univ := h1
        _ = μS.real Ω * ‖W z‖ := by
          simp only [Measure.real, Measure.restrict_apply_univ]
          ring
  have hY : ∀ i, (∫ z, F z ∂ν).ofLp i = yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V i) := by
    intro i
    have h1 := (PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin (Module.finrank ℂ V) => HH) i).integral_comp_comm hFint
    simp only [PiLp.proj_apply] at h1
    rw [← h1]
    unfold yv
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    have h2 := (PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin (Module.finrank ℂ V) => HH) i).integral_comp_comm
      (hgint z)
    simp only [PiLp.proj_apply] at h2
    simp only [hF]
    rw [← h2]
    simp [hg, gvec]
  have hr : (∑ i, ‖yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V i)‖ ^ 2) = ‖∫ z, F z ∂ν‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [hY]
  rw [hr]
  push_cast
  refine (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (∫ z, F z ∂ν)).symm.trans ?_
  calc ⟪∫ z, F z ∂ν, ∫ z, F z ∂ν⟫_ℂ = ∫ z, ⟪F z, ∫ z', F z' ∂ν⟫_ℂ ∂ν := hleft ν F hFint _
    _ = ∫ z, ∫ z', ⟪F z, F z'⟫_ℂ ∂ν ∂ν := by
        congr 1
        funext z
        exact (integral_inner hFint _).symm
    _ = ∫ z, ∫ z', ∫ q, (cnt μS Ω q).toReal • Fk σ w W z z' q ∂μS ∂ν ∂ν := by
        congr 1
        funext z
        congr 1
        funext z'
        have hae : ∀ᵐ p ∂((μS.restrict Ω).prod (μS.restrict Ω)), p ∈ Ω ×ˢ Ω := by
          rw [Measure.prod_restrict]
          exact ae_restrict_mem (hΩm.prod hΩm)
        have hint : Integrable (fun p : G × G => Fk σ w W z z' (p.1 * p.2⁻¹))
            ((μS.restrict Ω).prod (μS.restrict Ω)) := by
          refine Integrable.mono' (integrable_const (‖W z‖ * ‖W z'‖)) ?_ ?_
          · exact (Fk_continuous hσ w hWc (a := fun _ => z) (b := fun _ => z')
              (c := fun p : G × G => p.1 * p.2⁻¹) continuous_const continuous_const
              (continuous_fst.mul continuous_snd.inv)).aestronglyMeasurable
          · exact hae.mono fun p hp =>
              Fk_bound hσ hw hWeq hτu z z' (hSmul _ (hΩS hp.1) _ (hSinv _ (hΩS hp.2)))
        calc ⟪F z, F z'⟫_ℂ = ∫ s in Ω, ⟪g (s⁻¹ * z), F z'⟫_ℂ ∂μS := hleft _ _ (hgint z) _
          _ = ∫ s in Ω, ∫ t in Ω, ⟪g (s⁻¹ * z), g (t⁻¹ * z')⟫_ℂ ∂μS ∂μS := by
              congr 1
              funext s
              exact (integral_inner (hgint z') _).symm
          _ = ∫ s in Ω, ∫ t in Ω, Fk σ w W z z' (s * t⁻¹) ∂μS ∂μS := by
              refine setIntegral_congr_fun hΩm fun s hs => ?_
              congr 1
              funext t
              rw [hg, gvec_inner]
              exact kF hσ w hSinv hWeq hτu z z' (hΩS hs)
          _ = _ := conv_integral hS hΩm hΩS hfin _
              (Fk_continuous hσ w hWc (a := fun _ => z) (b := fun _ => z') (c := fun q => q)
                continuous_const continuous_const continuous_id).stronglyMeasurable hint

end Formalism.L2.S.Pv.EnergyAbs
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsFolnerLim
noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem Fk_enorm_le {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {S : Set G}
    {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (z z' : G) {q : G} (hq : q ∈ S) :
    ‖Fk σ w W z z' q‖ₑ ≤ ‖⟪σ z w, σ q (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ := by
  unfold Fk
  rw [hWeq q hq z', hσ.2.1 q z', ContinuousLinearMap.mul_apply]
  have hn : ‖τ q (W z')‖ = ‖W z'‖ := by
    have h := hτu q hq (W z') (W z')
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h' : ‖τ q (W z')‖ ^ 2 = ‖W z'‖ ^ 2 := by exact_mod_cast h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h'
  have hA : ‖⟪τ q (W z'), W z⟫_ℂ‖ ≤ ‖W z‖ * ‖W z'‖ :=
    (norm_inner_le_norm _ _).trans (by rw [hn, mul_comm])
  have hAe : ‖⟪τ q (W z'), W z⟫_ℂ‖ₑ ≤ ‖W z‖ₑ * ‖W z'‖ₑ := by
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hA
  rw [enorm_mul]
  calc ‖⟪τ q (W z'), W z⟫_ℂ‖ₑ * ‖⟪σ z w, σ q (σ z' w)⟫_ℂ‖ₑ
      ≤ (‖W z‖ₑ * ‖W z'‖ₑ) * ‖⟪σ z w, σ q (σ z' w)⟫_ℂ‖ₑ := by gcongr
    _ = ‖⟪σ z w, σ q (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ := by ring

private theorem continuous_Fk_uncurry {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {W : G → V}
    (hWc : Continuous W) : Continuous (fun x : G × G × G => Fk σ w W x.1 x.2.1 x.2.2) := by
  have hσc := hσ.2.2.2 w
  unfold Fk
  refine Continuous.mul ?_ ?_
  · exact (hWc.comp (continuous_snd.snd.mul continuous_snd.fst)).inner (hWc.comp continuous_fst)
  · exact (hσc.comp continuous_fst).inner (hσc.comp (continuous_snd.snd.mul continuous_snd.fst))

private theorem lintegral_enorm_Fk_lt_infty {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {S : Set G}
    {μS ν : Measure G} [SFinite μS] [SFinite ν] (hS0 : μS Sᶜ = 0) {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (hmeas : Measurable (fun x : G × G × G => ‖Fk σ w W x.1 x.2.1 x.2.2‖ₑ))
    (hconv : ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS ∂ν ∂ν < ⊤) :
    ∫⁻ x, ‖Fk σ w W x.1 x.2.1 x.2.2‖ₑ ∂(ν.prod (ν.prod μS)) < ⊤ := by
  have hSae : ∀ᵐ q ∂μS, q ∈ S := by
    have h := compl_mem_ae_iff.2 hS0
    rw [compl_compl] at h
    exact h
  calc ∫⁻ x, ‖Fk σ w W x.1 x.2.1 x.2.2‖ₑ ∂(ν.prod (ν.prod μS))
      = ∫⁻ z, ∫⁻ y, ‖Fk σ w W z y.1 y.2‖ₑ ∂(ν.prod μS) ∂ν := lintegral_prod _ hmeas.aemeasurable
    _ = ∫⁻ z, ∫⁻ z', ∫⁻ q, ‖Fk σ w W z z' q‖ₑ ∂μS ∂ν ∂ν :=
        lintegral_congr fun z => lintegral_prod _ (hmeas.comp measurable_prodMk_left).aemeasurable
    _ ≤ ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS ∂ν ∂ν :=
        lintegral_mono fun z => lintegral_mono fun z' => lintegral_mono_ae (by
          filter_upwards [hSae] with q hq
          exact Fk_enorm_le hσ w hWeq hτu z z' hq)
    _ < ⊤ := hconv

theorem Fk_integrable {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {S : Set G}
    {μS ν : Measure G} [SFinite μS] [SFinite ν] (hS0 : μS Sᶜ = 0) {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (hWc : Continuous W)
    (hconv : ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS ∂ν ∂ν < ⊤) :
    Integrable (fun x : G × G × G => Fk σ w W x.1 x.2.1 x.2.2) (ν.prod (ν.prod μS)) := by
  have hcont := continuous_Fk_uncurry hσ w hWc
  exact ⟨hcont.aestronglyMeasurable,
    lintegral_enorm_Fk_lt_infty hσ w hS0 hWeq hτu (continuous_enorm.measurable.comp hcont.measurable) hconv⟩

theorem integral_norm_sq_eq_one {ν : Measure G} {W : G → V} (hWc : Continuous W) (h2 : ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν = 1) :
    ∫ z, ‖W z‖ ^ 2 ∂ν = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg _)
    ((hWc.norm.pow 2).aestronglyMeasurable)]
  have h : (fun x => ENNReal.ofReal (‖W x‖ ^ 2)) = fun x => ‖W x‖ₑ ^ 2 := by
    funext x
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  rw [h, h2]
  simp

theorem integral_inner_mul_inner_eq_norm_sq_div {μ : Measure G} [μ.IsMulLeftInvariant] {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {d : ℝ}
    (hd : 0 < d) {w : HH} {S : Set G} {τ : G → (V →L[ℂ] V)} {ν : Measure G} {W : G → V}
    (hW : IsWAbs μ σ d w S τ ν W) (z : G) :
    ∫ x, ⟪W x, W z⟫_ℂ * ⟪σ z w, σ x w⟫_ℂ ∂μ = ((‖W z‖ ^ 2 / d : ℝ) : ℂ) := by
  obtain ⟨hint, heq⟩ := hW.2.2.2.2.2.1 z
  rw [← integral_mul_left_eq_self _ z]
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hpt : ∀ y, ⟪W (z * y), W z⟫_ℂ * ⟪σ z w, σ (z * y) w⟫_ℂ =
      conj (((1 / d : ℝ) : ℂ) * ⟪W z, ((d : ℂ) * conj ⟪w, σ y w⟫_ℂ) • W (z * y)⟫_ℂ) := by
    intro y
    rw [hσ.2.1 z y, ContinuousLinearMap.mul_apply, hσ.2.2.1, inner_smul_right]
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal, inner_conj_symm]
    push_cast
    first | (field_simp; ring) | field_simp | ring
  simp_rw [hpt]
  have hself : ⟪W z, W z⟫_ℂ = ((‖W z‖ ^ 2 : ℝ) : ℂ) := by
    refine Complex.ext ?_ ?_
    · first
        | simp [inner_self_eq_norm_sq]
        | (rw [Complex.ofReal_re]; exact inner_self_eq_norm_sq (𝕜 := ℂ) (W z))
    · first
        | simp
        | (rw [Complex.ofReal_im]; exact inner_self_im (𝕜 := ℂ) (W z))
  rw [integral_conj, integral_const_mul, integral_inner hint, heq, hself, ← Complex.ofReal_mul,
    Complex.conj_ofReal]
  congr 1
  ring

theorem Fk_value {μ : Measure G} [μ.IsMulLeftInvariant] {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {d : ℝ}
    (hd : 0 < d) {w : HH} {S : Set G} {μS ν : Measure G} [SFinite μS] [SFinite ν] (hq : IsQuot μ μS ν)
    {τ : G → (V →L[ℂ] V)} {W : G → V} (hW : IsWAbs μ σ d w S τ ν W)
    (hΦ : Integrable (fun x : G × G × G => Fk σ w W x.1 x.2.1 x.2.2) (ν.prod (ν.prod μS))) :
    ∫ x, Fk σ w W x.1 x.2.1 x.2.2 ∂(ν.prod (ν.prod μS)) = ((1 / d : ℝ) : ℂ) := by
  have hWc : Continuous W := hW.2.2.2.2.1
  have hL2 := hW.2.2.2.2.2.2.2
  have hm : Measurable (fun p : G × G => p.2 * p.1) := measurable_snd.mul measurable_fst
  have hmap : μ = Measure.map (fun p : G × G => p.2 * p.1) (ν.prod μS) := by
    ext s hs
    rw [Measure.map_apply hm hs, ← lintegral_indicator_one hs, hq _ (measurable_one.indicator hs),
      ← lintegral_indicator_one (hm hs),
      lintegral_prod _ ((measurable_one.indicator (hm hs)).aemeasurable)]
    first
      | rfl
      | (simp only [Set.indicator_apply, Set.mem_preimage]; rfl)
  have hinner : ∀ z, ∫ y, Fk σ w W z y.1 y.2 ∂(ν.prod μS) = ((‖W z‖ ^ 2 / d : ℝ) : ℂ) := by
    intro z
    have hg := integral_inner_mul_inner_eq_norm_sq_div hσ hd hW z
    have hgc : Continuous (fun x : G => ⟪W x, W z⟫_ℂ * ⟪σ z w, σ x w⟫_ℂ) :=
      (hWc.inner continuous_const).mul (continuous_const.inner (hσ.2.2.2 w))
    rw [hmap, integral_map hm.aemeasurable hgc.aestronglyMeasurable] at hg
    exact hg
  rw [integral_prod _ hΦ]
  refine (integral_congr_ae (ae_of_all _ fun z => hinner z)).trans ?_
  first
    | rw [integral_complex_ofReal, integral_div, integral_norm_sq_eq_one hWc hL2]
    | rw [integral_ofReal, integral_div, integral_norm_sq_eq_one hWc hL2]

end Formalism.L2.S.Pv.EnergyAbs
end
end

noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

section Folner

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]

theorem ratio_le_one {μS : Measure G} {Ω A : Set G} (hA : A ⊆ Ω) (hfin : μS Ω < ⊤) :
    (μS A).toReal / (μS Ω).toReal ≤ 1 := by
  apply div_le_one_of_le₀ _ ENNReal.toReal_nonneg
  exact ENNReal.toReal_mono hfin.ne (measure_mono hA)

theorem ratio_nonneg {μS : Measure G} {Ω A : Set G} : 0 ≤ (μS A).toReal / (μS Ω).toReal := div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

theorem folner_seq [LocallyCompactSpace G] [SecondCountableTopology G] {S : Set G} {μS : Measure G}
    (hS : IsHaarSub S μS) (hF : IsFolner S μS) :
    ∃ Ω : ℕ → Set G, (∀ n, MeasurableSet (Ω n) ∧ Ω n ⊆ S ∧ 0 < μS (Ω n) ∧ μS (Ω n) < ⊤) ∧
      ∀ K : Set G, IsCompact K → K ⊆ S →
        Tendsto (fun n => (μS {t | t ∈ Ω n ∧ ∀ k ∈ K, k * t ∈ Ω n}).toReal / (μS (Ω n)).toReal) atTop (𝓝 1) := by
  let Kx := CompactExhaustion.choice G
  have hε : ∀ n : ℕ, (0 : ℝ≥0∞) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) := fun n =>
    ENNReal.ofReal_pos.mpr (by positivity)
  choose Ω hΩm hΩS hpos hfin hle using fun n : ℕ =>
    hF (Kx n ∩ S) ((Kx.isCompact n).inter_right hS.1) Set.inter_subset_right _ (hε n)
  refine ⟨Ω, fun n => ⟨hΩm n, hΩS n, hpos n, hfin n⟩, ?_⟩
  intro K hK hKS
  obtain ⟨N, hN⟩ := Kx.exists_superset_of_isCompact hK
  have hlow : Tendsto (fun n : ℕ => 1 / (1 + 1 / ((n : ℝ) + 1))) atTop (𝓝 1) := by
    have h1 := tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)
    have h2 : Tendsto (fun n : ℕ => (1 : ℝ) / (1 + 1 / ((n : ℝ) + 1))) atTop (𝓝 (1 / (1 + 0))) :=
      tendsto_const_nhds.div h1 (by norm_num)
    rwa [add_zero, div_one] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hsub : {t | t ∈ Ω n ∧ ∀ k ∈ Kx n ∩ S, k * t ∈ Ω n} ⊆ {t | t ∈ Ω n ∧ ∀ k ∈ K, k * t ∈ Ω n} :=
      fun t ht => ⟨ht.1, fun k hk => ht.2 k ⟨Kx.subset hn (hN hk), hKS hk⟩⟩
    have hAB := measure_mono (μ := μS) hsub
    have hBΩ : μS {t | t ∈ Ω n ∧ ∀ k ∈ K, k * t ∈ Ω n} ≤ μS (Ω n) := measure_mono (fun t ht => ht.1)
    have hBfin := (hBΩ.trans_lt (hfin n)).ne
    have hAfin := ((hAB.trans hBΩ).trans_lt (hfin n)).ne
    have hΩpos : 0 < (μS (Ω n)).toReal := ENNReal.toReal_pos (hpos n).ne' (hfin n).ne
    have hkey := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hAfin) (hle n)
    rw [ENNReal.toReal_mul, ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_one] at hkey
    have hAB' := ENNReal.toReal_mono hBfin hAB
    have hc : 0 < 1 + 1 / ((n : ℝ) + 1) := by positivity
    rw [div_le_div_iff₀ hc hΩpos]
    nlinarith [mul_le_mul_of_nonneg_left hAB' hc.le]
  · exact Filter.Eventually.of_forall fun n => ratio_le_one (fun t ht => ht.1) (hfin n)

end Folner

section Limit

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

def rat (μS : Measure G) (Ω : Set G) (q : G) : ℝ := (cnt μS Ω q).toReal / (μS Ω).toReal

theorem sumsq_div_eq {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {w : HH} (hw : ‖w‖ = 1) {S : Set G}
    {μS ν : Measure G} (hS : IsHaarSub S μS) [SFinite ν] {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (hWc : Continuous W) (hW1 : ∫⁻ x, ‖W x‖ₑ ∂ν < ⊤) {Ω : Set G} (hΩm : MeasurableSet Ω) (hΩS : Ω ⊆ S)
    (hfin : μS Ω < ⊤)
    (hint : Integrable (fun x : G × G × G => rat μS Ω x.2.2 • Fk σ w W x.1 x.2.1 x.2.2) (ν.prod (ν.prod μS))) :
    (((∑ i, ‖yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V i)‖ ^ 2) / (μS Ω).toReal : ℝ) : ℂ) =
      ∫ x, rat μS Ω x.2.2 • Fk σ w W x.1 x.2.1 x.2.2 ∂(ν.prod (ν.prod μS)) := by
  have : SigmaFinite μS := hS.2.2.2.2.1
  by_cases hm : (μS Ω).toReal = 0
  · simp [rat, hm]
  · have hI := ‹Integrable (fun x : G × G × G => rat μS Ω x.2.2 • Fk σ w W x.1 x.2.1 x.2.2)
      (ν.prod (ν.prod μS))›
    have hfI : Integrable (fun x : G × G × G => (cnt μS Ω x.2.2).toReal • Fk σ w W x.1 x.2.1 x.2.2)
        (ν.prod (ν.prod μS)) := by
      refine (hI.smul (μS Ω).toReal).congr (ae_of_all _ fun x => ?_)
      simp only [Pi.smul_apply, rat, smul_smul]
      congr 1
      first
        | rw [mul_div_assoc', mul_div_cancel_left₀ _ hm]
        | field_simp
    have hprod : ∫ x, (cnt μS Ω x.2.2).toReal • Fk σ w W x.1 x.2.1 x.2.2 ∂(ν.prod (ν.prod μS)) =
        ∫ z, ∫ z', ∫ q, (cnt μS Ω q).toReal • Fk σ w W z z' q ∂μS ∂ν ∂ν := by
      rw [integral_prod _ hfI]
      refine integral_congr_ae ?_
      filter_upwards [hfI.prod_right_ae] with z hz
      exact integral_prod _ hz
    have hrhs : ∫ x, rat μS Ω x.2.2 • Fk σ w W x.1 x.2.1 x.2.2 ∂(ν.prod (ν.prod μS)) =
        ∫ x, ((μS Ω).toReal⁻¹ : ℝ) • ((cnt μS Ω x.2.2).toReal • Fk σ w W x.1 x.2.1 x.2.2)
          ∂(ν.prod (ν.prod μS)) := by
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [rat, smul_smul, div_eq_inv_mul]
    rw [hrhs, integral_smul, hprod, ← sumsq_eq hσ hw hS hWeq hτu hWc hW1 hΩm hΩS hfin,
      Complex.real_smul]
    push_cast
    ring

theorem folner_limit {μ : Measure G} [μ.IsHaarMeasure] {σ : G → (HH →L[ℂ] HH)} {d : ℝ} {w : HH}
    {S : Set G} {μS ν : Measure G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hσ : IsUnitRep σ) (hSch : IsSchur μ σ d) (hw : ‖w‖ = 1) (hS : IsHaarSub S μS) (hν : SFinite ν)
    (hq : IsQuot μ μS ν) (hW : IsWAbs μ σ d w S τ ν W)
    (hconv : ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS ∂ν ∂ν < ⊤)
    (Ω : ℕ → Set G) (hΩ : ∀ n, MeasurableSet (Ω n) ∧ Ω n ⊆ S ∧ 0 < μS (Ω n) ∧ μS (Ω n) < ⊤)
    (hF : ∀ K : Set G, IsCompact K → K ⊆ S →
      Tendsto (fun n => (μS {t | t ∈ Ω n ∧ ∀ k ∈ K, k * t ∈ Ω n}).toReal / (μS (Ω n)).toReal) atTop (𝓝 1)) :
    Tendsto (fun n => (∑ i, ‖yv μS ν σ w W (Ω n) (stdOrthonormalBasis ℂ V i)‖ ^ 2) / (μS (Ω n)).toReal)
      atTop (𝓝 (1 / d)) := by
  have : SFinite ν := hν
  have : SigmaFinite μS := hS.2.2.2.2.1
  have hd : 0 < d := hSch.1
  have hWeq := hW.2.2.2.1
  have hτu := hW.2.2.1
  have hWc := hW.2.2.2.2.1
  have hW1 := hW.2.2.2.2.2.2.1
  have hS0 : μS Sᶜ = 0 := hS.2.2.2.2.2.2.1
  have hΦ := Fk_integrable hσ w hS0 hWeq hτu hWc hconv
  have hmeas : ∀ n, Measurable (fun x : G × G × G => rat μS (Ω n) x.2.2) := fun n =>
    (((cnt_measurable (μS := μS) (hΩ n).1).ennreal_toReal).div_const _).comp measurable_snd.snd
  have hr : ∀ n q, 0 ≤ rat μS (Ω n) q ∧ rat μS (Ω n) q ≤ 1 := by
    intro n q
    unfold rat cnt
    exact ⟨ratio_nonneg, ratio_le_one (fun t ht => ht.1) (hΩ n).2.2.2⟩
  have hbound : ∀ n (x : G × G × G), ‖rat μS (Ω n) x.2.2 • Fk σ w W x.1 x.2.1 x.2.2‖ ≤
      ‖Fk σ w W x.1 x.2.1 x.2.2‖ := by
    intro n x
    rw [norm_smul, Real.norm_of_nonneg (hr n x.2.2).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hr n x.2.2).2
  have hint_r : ∀ n, Integrable (fun x : G × G × G => rat μS (Ω n) x.2.2 • Fk σ w W x.1 x.2.1 x.2.2)
      (ν.prod (ν.prod μS)) := fun n =>
    hΦ.mono ((hmeas n).aestronglyMeasurable.smul hΦ.aestronglyMeasurable) (ae_of_all _ (hbound n))
  have hS_ae : ∀ᵐ x ∂(ν.prod (ν.prod μS)), x.2.2 ∈ S := by
    rw [ae_iff]
    have hset : {x : G × G × G | ¬ x.2.2 ∈ S} = Set.univ ×ˢ (Set.univ ×ˢ Sᶜ) := by
      ext x; simp
    rw [hset, Measure.prod_prod, Measure.prod_prod, hS0, mul_zero, mul_zero]
  have hlim : Tendsto (fun n => ∫ x, rat μS (Ω n) x.2.2 • Fk σ w W x.1 x.2.1 x.2.2
      ∂(ν.prod (ν.prod μS))) atTop (𝓝 (∫ x, Fk σ w W x.1 x.2.1 x.2.2 ∂(ν.prod (ν.prod μS)))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖Fk σ w W x.1 x.2.1 x.2.2‖)
      (fun n => (hint_r n).aestronglyMeasurable) hΦ.norm (fun n => ae_of_all _ (hbound n)) ?_
    filter_upwards [hS_ae] with x hx
    have h1 : Tendsto (fun n => rat μS (Ω n) x.2.2) atTop (𝓝 1) := by
      have h0 := hF {x.2.2} isCompact_singleton (Set.singleton_subset_iff.mpr hx)
      simpa [rat, cnt] using h0
    have h2 := h1.smul_const (Fk σ w W x.1 x.2.1 x.2.2)
    rwa [one_smul] at h2
  rw [Fk_value hσ hd hq hW hΦ] at hlim
  have hlim' : Tendsto (fun n => (((∑ i, ‖yv μS ν σ w W (Ω n) (stdOrthonormalBasis ℂ V i)‖ ^ 2) /
      (μS (Ω n)).toReal : ℝ) : ℂ)) atTop (𝓝 ((1 / d : ℝ) : ℂ)) :=
    hlim.congr fun n => (sumsq_div_eq hσ hw hS hWeq hτu hWc hW1 (hΩ n).1 (hΩ n).2.1
      (hΩ n).2.2.2 (hint_r n)).symm
  have h3 := (Complex.continuous_re.tendsto _).comp hlim'
  simpa only [Function.comp_def, Complex.ofReal_re] using h3

end Limit

end Formalism.L2.S.Pv.EnergyAbs
end
end

noncomputable section

open MeasureTheory Measure Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

theorem energyAbs_holds : EnergyAbs := by
  intro G _ _ _ _ _ _ _ _ μ _ _ HH _ _ _ σ d w V V' _ _ _ _ _ _ S S' μS μS' ν ν' τ τ' W W' C _ m h
    hσ hSch hw hS hS' hF hF' hν hν' hq hq' hW hW' hD hhm hOOi hB hC hC'
  haveI := hν
  haveI := hν'
  haveI : SigmaFinite μS := hS.2.2.2.2.1
  haveI : SigmaFinite μS' := hS'.2.2.2.2.1
  obtain ⟨Ω, hΩ, hΩF⟩ := folner_seq hS hF
  obtain ⟨Ω', hΩ', hΩF'⟩ := folner_seq hS' hF'
  have hlim := folner_limit hσ hSch hw hS hν hq hW hC Ω hΩ hΩF
  have hlim' := folner_limit hσ hSch hw hS' hν' hq' hW' hC' Ω' hΩ' hΩF'
  have hd : 0 < d := hSch.1
  set φn : ℕ → G → ℝ≥0∞ := fun n g => ENNReal.ofReal (hsA (Xop μS ν μS' ν' σ d w W W' (Ω n) (Ω' n) g))
    with hφn
  have hφm : ∀ n, Measurable (φn n) := fun n =>
    ENNReal.measurable_ofReal.comp (continuous_hsA_Xop hσ μS ν μS' ν' d w W W' (Ω n) (Ω' n)).measurable
  set Fn : ℕ → C → ℝ≥0∞ := fun n c => (μS (Ω n) * μS' (Ω' n))⁻¹ *
    ∫⁻ s, ∫⁻ s', φn n (s * h c * s'⁻¹) ∂μS' ∂μS with hFn
  have hpt : ∀ c, ENNReal.ofReal (hsA (∫ x, rk1A (W x) (W' ((h c)⁻¹ * x)) ∂μ)) ≤ liminf (fun n => Fn n c) atTop :=
    fun c => point_lower hσ hS hS' hq hq' hW hW' Ω Ω' hΩ hΩ' hΩF hΩF'
      (fun n => continuous_hsA_Xop hσ μS ν μS' ν' d w W W' (Ω n) (Ω' n)) (h c) (hB c)
  have hinner : ∀ n, Measurable (fun c => ∫⁻ s, ∫⁻ s', φn n (s * h c * s'⁻¹) ∂μS' ∂μS) := by
    intro n
    have h3 : Measurable (fun r : (C × G) × G => φn n (r.1.2 * h r.1.1 * r.2⁻¹)) :=
      (hφm n).comp (((measurable_snd.comp measurable_fst).mul (hhm.comp (measurable_fst.comp measurable_fst))).mul
        measurable_snd.inv)
    exact h3.lintegral_prod_right'.lintegral_prod_right'
  have hmeasF : ∀ n, Measurable (Fn n) := fun n => (hinner n).const_mul _
  have hint : ∀ n, ∫⁻ c, Fn n c ∂m = (μS (Ω n) * μS' (Ω' n))⁻¹ *
      ENNReal.ofReal (d * (∑ i, ‖yv μS ν σ w W (Ω n) (stdOrthonormalBasis ℂ V i)‖ ^ 2) *
        (∑ j, ‖yv μS' ν' σ w W' (Ω' n) (stdOrthonormalBasis ℂ V' j)‖ ^ 2)) := by
    intro n
    rw [lintegral_const_mul _ (hinner n), ← hD (φn n) (hφm n), lintegral_hsA_Xop hSch]
  have htend := tendsto_energy hd (fun n => ⟨(hΩ n).2.2.1, (hΩ n).2.2.2⟩)
    (fun n => ⟨(hΩ' n).2.2.1, (hΩ' n).2.2.2⟩) hlim hlim'
  calc ∫⁻ c, ENNReal.ofReal (hsA (∫ x, rk1A (W x) (W' ((h c)⁻¹ * x)) ∂μ)) ∂m
      ≤ ∫⁻ c, liminf (fun n => Fn n c) atTop ∂m := lintegral_mono hpt
    _ ≤ liminf (fun n => ∫⁻ c, Fn n c ∂m) atTop := lintegral_liminf_le hmeasF
    _ = ENNReal.ofReal (1 / d) := by
        simp only [hint]
        exact htend.liminf_eq

end Formalism.L2.S.Pv.EnergyAbs
