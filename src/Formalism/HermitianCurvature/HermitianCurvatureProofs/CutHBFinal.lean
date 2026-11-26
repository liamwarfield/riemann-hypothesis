module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Side1PosOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PartialBesselSmoothCompactSupport

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SideZeroOfLocalProperness
namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt

theorem side_zero_of_local_properness (hPr : ProperLeftVariablesDomain) : CutHB.Side0 :=
  CutHB.side_zero_of_positive_and_zero (side0Pos_of'' hPr) (side0Zero_of Formalism.FourierDecayAlt.P.letters_pass_partial_bessel hPr CutHB.pts)

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.WordSmoothPartialBessel
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.WordSmoothPartialBesselInduction
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialBesselWordSmoothness

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBQ

def ProperDomPH : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (j : ℕ) (hj : j ≤ P.r) (Cs : Set (B.Mat P.k P.r)), IsCompact Cs →
    PartialBesselProperness.Proper (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) Cs (domP P.k P.r j p.T.base.z p.T.base.z')

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem smooth_pbT (hP : ProperDomPH) (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (j : ℕ) (hj : j ≤ P.r) (hF : KB.CptCoef p.T.base F) :
    Q.SmoothLev P.k P.r 0 (domP P.k P.r j p.T.base.z p.T.base.z') (pbT p j hj F) := by
  obtain ⟨hck, ⟨R, hR⟩, -⟩ := hF
  have hCs : IsCompact {g : B.Mat P.k P.r | B.gN g ≤ R} := Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le P.k P.r R
  have hz : ∀ g ∈ B.GV P.k P.r, g ∉ {g : B.Mat P.k P.r | B.gN g ≤ R} → F g = 0 := fun g hg hgC => by
    by_contra h; exact hgC (hR g hg h)
  have hzl : p.T.base.z = D.castV (by omega : j + (P.r - j) = P.r) (liftVec P.k j (P.r - j) (p.T.bs j).z) :=
    (p.T.z_lev j hj).symm
  refine Formalism.FourierDecayAlt.P.PBG.smoothLev_of_loc fun x hx => ?_
  exact Formalism.FourierDecayAlt.P.partial_bessel_smooth_compact_support P.k j (P.r - j) P.r Wp Wq (p.T.bs j) p.T.base (by omega) hzl F _ hck hCs hz
    _ (isOpen_domP P.k P.r j p.T.base.z p.T.base.z') (hP Wp Wq P p j hj _ hCs) x hx.2 hx.1.1

theorem word_smooth_partial_bessel_induction (hP : ProperDomPH) (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (j : ℕ) (hj : j + 1 ≤ P.r) (hF : KB.CptCoef p.T.base F) :
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)),
      Q.SmoothLev P.k P.r 0 (domP P.k P.r j p.T.base.z p.T.base.z')
        (D.uwG P.k P.r p.T.base.z p.T.base.z' (pbT p j (by omega) F) j (by omega) w e)
  | [], _ => smooth_pbT hP P p F j (by omega) hF
  | l :: w, e => by
    show Q.SmoothLev P.k P.r 0 _ (D.vLet P.k P.r p.T.base.z p.T.base.z' j (by omega) l (e 0)
      (D.uwG P.k P.r p.T.base.z p.T.base.z' (pbT p j (by omega) F) j (by omega) w fun a => e a.succ))
    exact Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts.smooth_vLet _ _ j (by omega) l (e 0) (isOpen_domP P.k P.r j p.T.base.z p.T.base.z')
      (word_smooth_partial_bessel_induction hP P p F j hj hF w _) (fun g hg => hg.1 ⟨j, by omega⟩ (show j ≤ j from le_rfl) (show j ≤ P.r by omega))

end

theorem wordSmooth_of (hP : ProperDomPH) : CutHB.WordSmooth := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w hF _ e
  exact word_smooth_partial_bessel_induction hP P p F j hj hF w e

end Formalism.FourierDecayAlt.P.PartialBesselWordSmoothness
end
end

namespace Formalism.FourierDecayAlt.P

theorem word_smooth_partial_bessel : CutHB.WordSmooth := PartialBesselWordSmoothness.wordSmooth_of proper_left_variables_domain

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.OneVariableLettersUnderIntegral
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.EntrywiseClassWordTransfer
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.GoodCongr
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtInt
open MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.LevelPointCoordinates

section fam

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X]
  [BorelSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def UX (X : Type) [TopologicalSpace X] : Set (X × ℂ) := Set.univ ×ˢ {τ : ℂ | τ ≠ 0}

theorem isOpen_UX : IsOpen (UX X) := isOpen_univ.prod isOpen_ne_zero_complex

def Good (Φ : X → V1 E) : Prop :=
  ContDiffOn ℝ ∞ (fun q : X × ℂ => (Φ q.1 : ℂ → E) q.2) (UX X) ∧
    ∀ K : Set ℂ, IsCompact K → K ⊆ {τ | τ ≠ 0} →
      ∃ C : Set X, IsCompact C ∧ ∀ v, v ∉ C → ∀ τ ∈ K, (Φ v : ℂ → E) τ = 0

def IsInt (μ : Measure X) (ℓ : X → E →L[ℂ] E) (Φ : X → V1 E) (f : V1 E) : Prop :=
  ∀ τ : ℂ, τ ≠ 0 → (f : ℂ → E) τ = ∫ v, ℓ v ((Φ v : ℂ → E) τ) ∂μ

theorem good_cont_at {Φ : X → V1 E} (h : Good Φ) {τ : ℂ} (hτ : τ ≠ 0) :
    Continuous (fun v => (Φ v : ℂ → E) τ) :=
  h.1.continuousOn.comp_continuous (continuous_id.prodMk continuous_const) fun _ => ⟨Set.mem_univ _, hτ⟩

theorem partial_fderiv {Φ : X → V1 E} (h : Good Φ) (v : X) {τ : ℂ} (hτ : τ ≠ 0) :
    fderiv ℝ (Φ v : ℂ → E) τ =
      (fderiv ℝ (fun q : X × ℂ => (Φ q.1 : ℂ → E) q.2) (v, τ)).comp (ContinuousLinearMap.inr ℝ X ℂ) := by
  have hd : DifferentiableAt ℝ (fun q : X × ℂ => (Φ q.1 : ℂ → E) q.2) (v, τ) :=
    (h.1.differentiableOn (by simp)).differentiableAt (isOpen_UX.mem_nhds ⟨Set.mem_univ _, hτ⟩)
  have hi : HasFDerivAt (fun t : ℂ => (v, t)) (ContinuousLinearMap.inr ℝ X ℂ) τ := hasFDerivAt_prodMk_right v τ
  exact (hd.hasFDerivAt.comp τ hi).fderiv

theorem fd_contOn {Φ : X → V1 E} (h : Good Φ) :
    ContinuousOn (fun q : X × ℂ => fderiv ℝ (Φ q.1 : ℂ → E) q.2) (UX X) := by
  have h1 : ContinuousOn (fun q : X × ℂ =>
      (fderiv ℝ (fun q : X × ℂ => (Φ q.1 : ℂ → E) q.2) q).comp (ContinuousLinearMap.inr ℝ X ℂ)) (UX X) :=
    (h.1.continuousOn_fderiv_of_isOpen isOpen_UX (by simp)).clm_comp continuousOn_const
  exact h1.congr fun q hq => partial_fderiv h q.1 hq.2

theorem cd_partial {Φ : X → V1 E} (h : Good Φ) (w : ℂ) :
    ContDiffOn ℝ ∞ (fun q : X × ℂ => fderiv ℝ (Φ q.1 : ℂ → E) q.2 w) (UX X) := by
  have h1 : ContDiffOn ℝ ∞ (fun q : X × ℂ =>
      (fderiv ℝ (fun q : X × ℂ => (Φ q.1 : ℂ → E) q.2) q) (ContinuousLinearMap.inr ℝ X ℂ w)) (UX X) :=
    (h.1.fderiv_of_isOpen isOpen_UX (by simp)).clm_apply contDiffOn_const
  refine h1.congr fun q hq => ?_
  rw [partial_fderiv h q.1 hq.2]
  rfl

theorem fderiv_zero_of {Φ : X → V1 E} (h : Good Φ) {K : Set ℂ} (hK : IsCompact K) (hK0 : K ⊆ {τ | τ ≠ 0}) :
    ∃ C : Set X, IsCompact C ∧ ∀ v, v ∉ C → ∀ τ ∈ K, fderiv ℝ (Φ v : ℂ → E) τ = 0 := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK isOpen_ne_zero_complex hK0
  obtain ⟨C, hC, hz⟩ := h.2 L hL hLU
  refine ⟨C, hC, fun v hv τ hτ => ?_⟩
  have hev : (Φ v : ℂ → E) =ᶠ[𝓝 τ] fun _ => (0 : E) :=
    Filter.eventually_of_mem (isOpen_interior.mem_nhds (hKL hτ)) fun t ht => hz v hv t (interior_subset ht)
  rw [hev.fderiv_eq]
  exact fderiv_const_apply _

section int

variable (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (ℓ : X → E →L[ℂ] E)

theorem good_int {Φ : X → V1 E} (h : Good Φ) (hℓ : Continuous ℓ) {τ : ℂ} (hτ : τ ≠ 0) :
    Integrable (fun v => ℓ v ((Φ v : ℂ → E) τ)) μ := by
  obtain ⟨C, hC, hz⟩ := h.2 {τ} isCompact_singleton (Set.singleton_subset_iff.2 hτ)
  refine Continuous.integrable_of_hasCompactSupport (hℓ.clm_apply (good_cont_at h hτ)) ?_
  refine HasCompactSupport.intro hC fun v hv => ?_
  rw [hz v hv τ rfl, map_zero]

theorem fd_int {Φ : X → V1 E} (h : Good Φ) (hℓ : Continuous ℓ) {τ : ℂ} (hτ : τ ≠ 0) (w : ℂ) :
    Integrable (fun v => ℓ v (fderiv ℝ (Φ v : ℂ → E) τ w)) μ := by
  obtain ⟨C, hC, hz⟩ := fderiv_zero_of h isCompact_singleton (Set.singleton_subset_iff.2 hτ)
  have hc : Continuous (fun v => fderiv ℝ (Φ v : ℂ → E) τ) :=
    (fd_contOn h).comp_continuous (continuous_id.prodMk continuous_const) fun _ => ⟨Set.mem_univ _, hτ⟩
  refine Continuous.integrable_of_hasCompactSupport (hℓ.clm_apply (hc.clm_apply continuous_const)) ?_
  refine HasCompactSupport.intro hC fun v hv => ?_
  rw [hz v hv τ rfl]; simp

theorem rs_cont (hℓ : Continuous ℓ) : Continuous (fun v => (ℓ v).restrictScalars ℝ) :=
  (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).continuous.comp hℓ

theorem hasFDerivAt_int {Φ : X → V1 E} (h : Good Φ) (hℓ : Continuous ℓ) {τ0 : ℂ} (hτ0 : τ0 ≠ 0) :
    HasFDerivAt (fun τ => ∫ v, ℓ v ((Φ v : ℂ → E) τ) ∂μ)
      (∫ v, ((ℓ v).restrictScalars ℝ).comp (fderiv ℝ (Φ v : ℂ → E) τ0) ∂μ) τ0 := by
  have hn : 0 < ‖τ0‖ := norm_pos_iff.2 hτ0
  set r := ‖τ0‖ / 2 with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hK : IsCompact (Metric.closedBall τ0 r) := isCompact_closedBall _ _
  have hK0 : Metric.closedBall τ0 r ⊆ {τ | τ ≠ 0} := by
    intro τ hτ
    show τ ≠ 0
    rintro rfl
    rw [Metric.mem_closedBall, dist_zero_left] at hτ
    linarith
  have hB : ∀ τ ∈ Metric.ball τ0 r, τ ≠ 0 := fun τ hτ => hK0 (Metric.ball_subset_closedBall hτ)
  obtain ⟨C, hC, hz⟩ := fderiv_zero_of h hK hK0
  obtain ⟨Mf, hMf⟩ := (hC.prod hK).exists_bound_of_continuousOn
    ((fd_contOn h).mono fun q hq => ⟨Set.mem_univ _, hK0 hq.2⟩)
  obtain ⟨Ml, hMl⟩ := hC.exists_bound_of_continuousOn hℓ.continuousOn
  have hc0 : Continuous (fun v => fderiv ℝ (Φ v : ℂ → E) τ0) :=
    (fd_contOn h).comp_continuous (continuous_id.prodMk continuous_const) fun _ => ⟨Set.mem_univ _, hτ0⟩
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (𝕜 := ℝ)
    (F := fun τ v => ℓ v ((Φ v : ℂ → E) τ))
    (F' := fun τ v => ((ℓ v).restrictScalars ℝ).comp (fderiv ℝ (Φ v : ℂ → E) τ))
    (bound := Set.indicator C fun _ => Ml * Mf) (Metric.ball_mem_nhds τ0 hr0) ?_ (good_int μ ℓ h hℓ hτ0) ?_ ?_ ?_ ?_
  · filter_upwards [Metric.ball_mem_nhds τ0 hr0] with τ hτ
    exact (hℓ.clm_apply (good_cont_at h (hB τ hτ))).aestronglyMeasurable
  · exact ((rs_cont ℓ hℓ).clm_comp hc0).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun v τ hτ => ?_
    by_cases hv : v ∈ C
    · rw [Set.indicator_of_mem hv]
      have h1 := hMl v hv
      have h2 := hMf (v, τ) ⟨hv, Metric.ball_subset_closedBall hτ⟩
      calc ‖((ℓ v).restrictScalars ℝ).comp (fderiv ℝ (Φ v : ℂ → E) τ)‖
          ≤ ‖(ℓ v).restrictScalars ℝ‖ * ‖fderiv ℝ (Φ v : ℂ → E) τ‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ = ‖ℓ v‖ * ‖fderiv ℝ (Φ v : ℂ → E) τ‖ := by rw [ContinuousLinearMap.norm_restrictScalars]
        _ ≤ Ml * Mf := mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
    · rw [Set.indicator_of_notMem hv, hz v hv τ (Metric.ball_subset_closedBall hτ),
        ContinuousLinearMap.comp_zero, norm_zero]
  · exact (continuousOn_const.integrableOn_compact hC).integrable_indicator hC.measurableSet
  · refine Filter.Eventually.of_forall fun v τ hτ => ?_
    exact ((ℓ v).restrictScalars ℝ).hasFDerivAt.comp τ (differentiableAt_of_punctured_smooth (Φ v).2 (hB τ hτ)).hasFDerivAt

theorem fderiv_int {Φ : X → V1 E} (h : Good Φ) (hℓ : Continuous ℓ) {f : V1 E} (hf : IsInt μ ℓ Φ f) {τ0 : ℂ}
    (hτ0 : τ0 ≠ 0) (w : ℂ) :
    fderiv ℝ (f : ℂ → E) τ0 w = ∫ v, ℓ v (fderiv ℝ (Φ v : ℂ → E) τ0 w) ∂μ := by
  have hev : (f : ℂ → E) =ᶠ[𝓝 τ0] fun τ => ∫ v, ℓ v ((Φ v : ℂ → E) τ) ∂μ :=
    Filter.eventually_of_mem (isOpen_ne_zero_complex.mem_nhds hτ0) fun τ hτ => hf τ hτ
  rw [hev.fderiv_eq, (hasFDerivAt_int μ ℓ h hℓ hτ0).fderiv]
  have hc0 : Continuous (fun v => fderiv ℝ (Φ v : ℂ → E) τ0) :=
    (fd_contOn h).comp_continuous (continuous_id.prodMk continuous_const) fun _ => ⟨Set.mem_univ _, hτ0⟩
  obtain ⟨C, hC, hz⟩ := fderiv_zero_of h isCompact_singleton (Set.singleton_subset_iff.2 hτ0)
  have hI : Integrable (fun v => ((ℓ v).restrictScalars ℝ).comp (fderiv ℝ (Φ v : ℂ → E) τ0)) μ := by
    refine Continuous.integrable_of_hasCompactSupport ((rs_cont ℓ hℓ).clm_comp hc0) ?_
    refine HasCompactSupport.intro hC fun v hv => ?_
    rw [hz v hv τ0 rfl, ContinuousLinearMap.comp_zero]
  rw [ContinuousLinearMap.integral_apply hI]
  rfl

theorem dz_int {Φ : X → V1 E} (h : Good Φ) (hℓ : Continuous ℓ) {f : V1 E} (hf : IsInt μ ℓ Φ f) {τ0 : ℂ}
    (hτ0 : τ0 ≠ 0) : PBP.dz (f : ℂ → E) τ0 = ∫ v, ℓ v (PBP.dz (Φ v : ℂ → E) τ0) ∂μ := by
  unfold PBP.dz
  have hI2 : Integrable (fun v => Complex.I • ℓ v (fderiv ℝ (Φ v : ℂ → E) τ0 Complex.I)) μ :=
    (fd_int μ ℓ h hℓ hτ0 Complex.I).smul Complex.I
  rw [fderiv_int μ ℓ h hℓ hf hτ0, fderiv_int μ ℓ h hℓ hf hτ0, ← integral_smul, ← integral_sub
    (fd_int μ ℓ h hℓ hτ0 1) hI2, ← integral_smul]
  congr 1
  funext v
  rw [map_smul, map_sub, map_smul]

theorem dzb_int {Φ : X → V1 E} (h : Good Φ) (hℓ : Continuous ℓ) {f : V1 E} (hf : IsInt μ ℓ Φ f) {τ0 : ℂ}
    (hτ0 : τ0 ≠ 0) : PBP.dzb (f : ℂ → E) τ0 = ∫ v, ℓ v (PBP.dzb (Φ v : ℂ → E) τ0) ∂μ := by
  unfold PBP.dzb
  have hI2 : Integrable (fun v => Complex.I • ℓ v (fderiv ℝ (Φ v : ℂ → E) τ0 Complex.I)) μ :=
    (fd_int μ ℓ h hℓ hτ0 Complex.I).smul Complex.I
  rw [fderiv_int μ ℓ h hℓ hf hτ0, fderiv_int μ ℓ h hℓ hf hτ0, ← integral_smul, ← integral_add
    (fd_int μ ℓ h hℓ hτ0 1) hI2, ← integral_smul]
  congr 1
  funext v
  rw [map_smul, map_add (f := _), map_smul]

end int

end fam

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas
end
end

open MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.LevelPointCoordinates

section fam2

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X]
  [BorelSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem good_congr {Φ Ψ : X → V1 E} (h : Good Φ) (hΨ : ∀ v τ, τ ≠ 0 → (Ψ v : ℂ → E) τ = (Φ v : ℂ → E) τ) :
    Good Ψ := by
  refine ⟨h.1.congr fun q hq => hΨ q.1 q.2 hq.2, fun K hK hK0 => ?_⟩
  obtain ⟨C, hC, hz⟩ := h.2 K hK hK0
  exact ⟨C, hC, fun v hv τ hτ => by rw [hΨ v τ (hK0 hτ), hz v hv τ hτ]⟩

theorem good_zero : Good (fun _ : X => (0 : V1 E)) :=
  ⟨contDiffOn_const.congr fun _ _ => rfl, fun _ _ _ => ⟨∅, isCompact_empty, fun _ _ _ _ => rfl⟩⟩

theorem good_add {Φ Ψ : X → V1 E} (h : Good Φ) (h' : Good Ψ) : Good (fun v => Φ v + Ψ v) := by
  refine ⟨(h.1.add h'.1).congr fun _ _ => rfl, fun K hK hK0 => ?_⟩
  obtain ⟨C, hC, hz⟩ := h.2 K hK hK0
  obtain ⟨C', hC', hz'⟩ := h'.2 K hK hK0
  refine ⟨C ∪ C', hC.union hC', fun v hv τ hτ => ?_⟩
  simp only [Set.mem_union, not_or] at hv
  show (Φ v : ℂ → E) τ + (Ψ v : ℂ → E) τ = 0
  rw [hz v hv.1 τ hτ, hz' v hv.2 τ hτ, add_zero]

theorem good_smul {Φ : X → V1 E} (h : Good Φ) (c : ℂ) : Good (fun v => c • Φ v) := by
  refine ⟨(h.1.const_smul c).congr fun _ _ => rfl, fun K hK hK0 => ?_⟩
  obtain ⟨C, hC, hz⟩ := h.2 K hK hK0
  refine ⟨C, hC, fun v hv τ hτ => ?_⟩
  show c • (Φ v : ℂ → E) τ = 0
  rw [hz v hv τ hτ, smul_zero]

theorem good_sum {ι : Type*} (s : Finset ι) (Φ : ι → X → V1 E) (h : ∀ i ∈ s, Good (Φ i)) :
    Good (fun v => ∑ i ∈ s, Φ i v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (good_zero : Good (fun _ : X => (0 : V1 E)))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact good_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem good_opM {Φ : X → V1 E} (h : Good Φ) (m : ℂ → ℂ) (hm : ContDiffOn ℝ ∞ m {τ | τ ≠ 0}) :
    Good (fun v => opM m hm (Φ v)) := by
  have hm2 : ContDiffOn ℝ ∞ (fun q : X × ℂ => m q.2) (UX X) :=
    hm.comp contDiff_snd.contDiffOn fun q hq => hq.2
  refine ⟨(hm2.smul h.1).congr fun _ _ => rfl, fun K hK hK0 => ?_⟩
  obtain ⟨C, hC, hz⟩ := h.2 K hK hK0
  refine ⟨C, hC, fun v hv τ hτ => ?_⟩
  show m τ • (Φ v : ℂ → E) τ = 0
  rw [hz v hv τ hτ, smul_zero]

def dzF (Φ : X → V1 E) : X → V1 E := fun v => ⟨PBP.dz (Φ v : ℂ → E), contDiffOn_wirtinger_dz (Φ v).2⟩

def dzbF (Φ : X → V1 E) : X → V1 E := fun v => ⟨PBP.dzb (Φ v : ℂ → E), contDiffOn_wirtinger_dzbar (Φ v).2⟩

theorem good_dz {Φ : X → V1 E} (h : Good Φ) : Good (dzF Φ) := by
  have hc : ContDiffOn ℝ ∞ (fun q : X × ℂ => PBP.dz (Φ q.1 : ℂ → E) q.2) (UX X) := by
    unfold PBP.dz
    exact ((cd_partial h 1).sub ((cd_partial h Complex.I).const_smul Complex.I)).const_smul _
  refine ⟨hc.congr fun _ _ => rfl, fun K hK hK0 => ?_⟩
  obtain ⟨C, hC, hz⟩ := fderiv_zero_of h hK hK0
  refine ⟨C, hC, fun v hv τ hτ => ?_⟩
  show PBP.dz (Φ v : ℂ → E) τ = 0
  unfold PBP.dz
  rw [hz v hv τ hτ]
  simp

theorem good_dzb {Φ : X → V1 E} (h : Good Φ) : Good (dzbF Φ) := by
  have hc : ContDiffOn ℝ ∞ (fun q : X × ℂ => PBP.dzb (Φ q.1 : ℂ → E) q.2) (UX X) := by
    unfold PBP.dzb
    exact ((cd_partial h 1).add ((cd_partial h Complex.I).const_smul Complex.I)).const_smul _
  refine ⟨hc.congr fun _ _ => rfl, fun K hK hK0 => ?_⟩
  obtain ⟨C, hC, hz⟩ := fderiv_zero_of h hK hK0
  refine ⟨C, hC, fun v hv τ hτ => ?_⟩
  show PBP.dzb (Φ v : ℂ → E) τ = 0
  unfold PBP.dzb
  rw [hz v hv τ hτ]
  simp

theorem opP_apply (κ : ℂ) (f : V1 E) {τ : ℂ} (hτ : τ ≠ 0) :
    ((opP κ f : V1 E) : ℂ → E) τ = τ • PBP.dz (f : ℂ → E) τ + κ • (f : ℂ → E) τ := by
  show off0 (fun τ => τ • PBP.dz (f : ℂ → E) τ + κ • (f : ℂ → E) τ) τ = _
  rw [off0, if_neg hτ]

theorem opPb_apply (κ : ℂ) (f : V1 E) {τ : ℂ} (hτ : τ ≠ 0) :
    ((opPb κ f : V1 E) : ℂ → E) τ = conj τ • PBP.dzb (f : ℂ → E) τ + κ • (f : ℂ → E) τ := by
  show off0 (fun τ => conj τ • PBP.dzb (f : ℂ → E) τ + κ • (f : ℂ → E) τ) τ = _
  rw [off0, if_neg hτ]

section ok

variable (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (ℓ : X → E →L[ℂ] E)

def OK (T : Module.End ℂ (V1 E)) : Prop :=
  ∀ (Φ : X → V1 E) (f : V1 E), Good Φ → IsInt μ ℓ Φ f →
    Good (fun v => T (Φ v)) ∧ IsInt μ ℓ (fun v => T (Φ v)) (T f)

variable {μ ℓ}

theorem int_add {Φ Ψ : X → V1 E} {f g : V1 E} (hℓ : Continuous ℓ) (h : Good Φ) (h' : Good Ψ)
    (hf : IsInt μ ℓ Φ f) (hg : IsInt μ ℓ Ψ g) : IsInt μ ℓ (fun v => Φ v + Ψ v) (f + g) := by
  intro τ hτ
  show (f : ℂ → E) τ + (g : ℂ → E) τ = ∫ v, ℓ v ((Φ v : ℂ → E) τ + (Ψ v : ℂ → E) τ) ∂μ
  rw [hf τ hτ, hg τ hτ, ← integral_add (good_int μ ℓ h hℓ hτ) (good_int μ ℓ h' hℓ hτ)]
  congr 1
  funext v
  rw [map_add (f := _)]

theorem int_smul {Φ : X → V1 E} {f : V1 E} (hf : IsInt μ ℓ Φ f) (c : ℂ) :
    IsInt μ ℓ (fun v => c • Φ v) (c • f) := by
  intro τ hτ
  show c • (f : ℂ → E) τ = ∫ v, ℓ v (c • (Φ v : ℂ → E) τ) ∂μ
  rw [hf τ hτ, ← integral_smul]
  congr 1
  funext v
  rw [map_smul]

theorem int_zero : IsInt μ ℓ (fun _ : X => (0 : V1 E)) 0 := by
  intro τ _
  show (0 : E) = ∫ v, ℓ v (0 : E) ∂μ
  simp

theorem int_sum {ι : Type*} (hℓ : Continuous ℓ) (s : Finset ι) (Φ : ι → X → V1 E) (f : ι → V1 E)
    (h : ∀ i ∈ s, Good (Φ i)) (hf : ∀ i ∈ s, IsInt μ ℓ (Φ i) (f i)) :
    IsInt μ ℓ (fun v => ∑ i ∈ s, Φ i v) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (int_zero : IsInt μ ℓ (fun _ : X => (0 : V1 E)) 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact int_add hℓ (h a (Finset.mem_insert_self a s))
      (good_sum s Φ fun i hi => h i (Finset.mem_insert_of_mem hi)) (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem ok_zero : OK μ ℓ (0 : Module.End ℂ (V1 E)) := fun _ _ _ _ => ⟨good_zero, int_zero⟩

theorem ok_one : OK μ ℓ (1 : Module.End ℂ (V1 E)) := fun _ _ h hf => ⟨h, hf⟩

theorem ok_add (hℓ : Continuous ℓ) {T T' : Module.End ℂ (V1 E)} (h : OK μ ℓ T) (h' : OK μ ℓ T') :
    OK μ ℓ (T + T') := fun Φ f hΦ hf =>
  ⟨good_add (h Φ f hΦ hf).1 (h' Φ f hΦ hf).1, int_add hℓ (h Φ f hΦ hf).1 (h' Φ f hΦ hf).1 (h Φ f hΦ hf).2
    (h' Φ f hΦ hf).2⟩

theorem ok_mul {T T' : Module.End ℂ (V1 E)} (h : OK μ ℓ T) (h' : OK μ ℓ T') : OK μ ℓ (T * T') :=
  fun Φ f hΦ hf => h _ _ (h' Φ f hΦ hf).1 (h' Φ f hΦ hf).2

theorem ok_smul {T : Module.End ℂ (V1 E)} (h : OK μ ℓ T) (c : ℂ) : OK μ ℓ (c • T) := fun Φ f hΦ hf =>
  ⟨good_smul (h Φ f hΦ hf).1 c, int_smul (h Φ f hΦ hf).2 c⟩

theorem ok_neg {T : Module.End ℂ (V1 E)} (h : OK μ ℓ T) : OK μ ℓ (-T) := by
  rw [← neg_one_smul ℂ T]
  exact ok_smul h (-1)

theorem ok_alg (c : ℂ) : OK μ ℓ (algebraMap ℂ (Module.End ℂ (V1 E)) c) := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact ok_smul ok_one c

theorem ok_opM (m : ℂ → ℂ) (hm : ContDiffOn ℝ ∞ m {τ | τ ≠ 0}) : OK μ ℓ (opM (E := E) m hm) := by
  intro Φ f hΦ hf
  refine ⟨good_opM hΦ m hm, fun τ hτ => ?_⟩
  show m τ • (f : ℂ → E) τ = ∫ v, ℓ v (m τ • (Φ v : ℂ → E) τ) ∂μ
  rw [hf τ hτ, ← integral_smul]
  congr 1
  funext v
  rw [map_smul]

theorem ok_opP (hℓ : Continuous ℓ) (κ : ℂ) : OK μ ℓ (opP (E := E) κ) := by
  intro Φ f hΦ hf
  have hg : Good (fun v => opM (fun τ => τ) cd_id (dzF Φ v) + κ • Φ v) :=
    good_add (good_opM (good_dz hΦ) _ _) (good_smul hΦ κ)
  refine ⟨good_congr hg fun v τ hτ => by rw [opP_apply κ _ hτ]; rfl, fun τ hτ => ?_⟩
  have i1 : Integrable (fun v => τ • ℓ v (PBP.dz (Φ v : ℂ → E) τ)) μ := (good_int μ ℓ (good_dz hΦ) hℓ hτ).smul τ
  have i2 : Integrable (fun v => κ • ℓ v ((Φ v : ℂ → E) τ)) μ := (good_int μ ℓ hΦ hℓ hτ).smul κ
  rw [opP_apply κ f hτ, dz_int μ ℓ hΦ hℓ hf hτ, hf τ hτ, ← integral_smul, ← integral_smul, ← integral_add i1 i2]
  congr 1
  funext v
  rw [opP_apply κ _ hτ, map_add (f := _), map_smul, map_smul]

theorem ok_opPb (hℓ : Continuous ℓ) (κ : ℂ) : OK μ ℓ (opPb (E := E) κ) := by
  intro Φ f hΦ hf
  have hg : Good (fun v => opM (fun τ => conj τ) cd_conj (dzbF Φ v) + κ • Φ v) :=
    good_add (good_opM (good_dzb hΦ) _ _) (good_smul hΦ κ)
  refine ⟨good_congr hg fun v τ hτ => by rw [opPb_apply κ _ hτ]; rfl, fun τ hτ => ?_⟩
  have i1 : Integrable (fun v => conj τ • ℓ v (PBP.dzb (Φ v : ℂ → E) τ)) μ :=
    (good_int μ ℓ (good_dzb hΦ) hℓ hτ).smul (conj τ)
  have i2 : Integrable (fun v => κ • ℓ v ((Φ v : ℂ → E) τ)) μ := (good_int μ ℓ hΦ hℓ hτ).smul κ
  rw [opPb_apply κ f hτ, dzb_int μ ℓ hΦ hℓ hf hτ, hf τ hτ, ← integral_smul, ← integral_smul, ← integral_add i1 i2]
  congr 1
  funext v
  rw [opPb_apply κ _ hτ, map_add (f := _), map_smul, map_smul]

end ok

end fam2

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas
end
end

open MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.LevelPointCoordinates

section pr

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X]
  [BorelSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (ℓ : X → E →L[ℂ] E)

def PG (x : Q.Pr (V1 E)) : Prop := OK μ ℓ x.1 ∧ OK μ ℓ x.2.unop

variable {μ ℓ}

theorem pg_zero : PG μ ℓ (0 : Q.Pr (V1 E)) := ⟨ok_zero, ok_zero⟩

theorem pg_one : PG μ ℓ (1 : Q.Pr (V1 E)) := ⟨ok_one, ok_one⟩

theorem pg_add (hℓ : Continuous ℓ) {x y : Q.Pr (V1 E)} (hx : PG μ ℓ x) (hy : PG μ ℓ y) : PG μ ℓ (x + y) :=
  ⟨ok_add hℓ hx.1 hy.1, ok_add hℓ hx.2 hy.2⟩

theorem pg_mul {x y : Q.Pr (V1 E)} (hx : PG μ ℓ x) (hy : PG μ ℓ y) : PG μ ℓ (x * y) :=
  ⟨ok_mul hx.1 hy.1, ok_mul hy.2 hx.2⟩

theorem pg_neg {x : Q.Pr (V1 E)} (hx : PG μ ℓ x) : PG μ ℓ (-x) := ⟨ok_neg hx.1, ok_neg hx.2⟩

theorem pg_star {x : Q.Pr (V1 E)} (hx : PG μ ℓ x) : PG μ ℓ (star x) := ⟨hx.2, hx.1⟩

theorem pg_alg (c : ℂ) : PG μ ℓ (algebraMap ℂ (Q.Pr (V1 E)) c) := ⟨ok_alg c, ok_alg (conj c)⟩

theorem pg_sum (hℓ : Continuous ℓ) {ι : Type*} (s : Finset ι) (f : ι → Q.Pr (V1 E)) (h : ∀ i ∈ s, PG μ ℓ (f i)) :
    PG μ ℓ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (pg_zero : PG μ ℓ (0 : Q.Pr (V1 E)))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact pg_add hℓ (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

variable {S : Type} [Fintype S] [DecidableEq S]


variable (μ ℓ) in
def EntrywiseClass (M : Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E))) : Prop := ∀ a b, PG μ ℓ (M a b)

theorem entrywise_class_mul (hℓ : Continuous ℓ) {M N : Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E))} (hM : EntrywiseClass μ ℓ M) (hN : EntrywiseClass μ ℓ N) :
    EntrywiseClass μ ℓ (M * N) := fun a b => by
  rw [Matrix.mul_apply]
  exact pg_sum hℓ _ _ fun c _ => pg_mul (hM a c) (hN c b)

theorem entrywise_class_sum (hℓ : Continuous ℓ) {ι : Type*} (s : Finset ι) (M : ι → Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E)))
    (h : ∀ i ∈ s, EntrywiseClass μ ℓ (M i)) : EntrywiseClass μ ℓ (∑ i ∈ s, M i) := fun a b => by
  rw [Matrix.sum_apply]
  exact pg_sum hℓ _ _ fun i hi => h i hi a b

theorem entrywise_class_one : EntrywiseClass μ ℓ (1 : Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E))) := fun a b => by
  rw [Matrix.one_apply]
  split_ifs
  · exact pg_one
  · exact pg_zero

theorem entrywise_class_unit_matrix (a : S) (i j : Fin 2) : EntrywiseClass μ ℓ (Wd.eU a i j : Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E))) := fun x y => by
  unfold Wd.eU
  rw [Matrix.of_apply]
  split_ifs
  · exact pg_one
  · exact pg_zero

theorem entrywise_class_scalar {x : Q.Pr (V1 E)} (hx : PG μ ℓ x) : EntrywiseClass μ ℓ (Wd.io x : Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E))) := fun a b => by
  unfold Wd.io
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact hx
  · exact pg_zero

theorem entrywise_class_insert (hℓ : Continuous ℓ) (a : S) {M : Wd.M2 (Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E)))} (hM : ∀ i j, EntrywiseClass μ ℓ (M i j)) :
    EntrywiseClass μ ℓ (Wd.ins a M) := by
  unfold Wd.ins
  exact entrywise_class_sum hℓ _ _ fun i _ => entrywise_class_sum hℓ _ _ fun j _ => entrywise_class_mul hℓ (entrywise_class_unit_matrix a i j) (hM i j)

theorem pg_Ts (hℓ : Continuous ℓ) (σ : Wd.Site (Q.Pr (V1 E))) (hp : PG μ ℓ σ.p) (hc : PG μ ℓ σ.c)
    (hci : PG μ ℓ σ.ci) (Y : ℂ) : ∀ i j, PG μ ℓ (Wd.Ts σ Y i j) := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact pg_add hℓ (pg_alg Y) hp
  · exact pg_neg hc
  · exact hci
  · exact pg_zero

theorem entrywise_class_letter (hℓ : Continuous ℓ) (σ : Wd.Site (Q.Pr (V1 E))) (hp : PG μ ℓ σ.p) (hc : PG μ ℓ σ.c)
    (hci : PG μ ℓ σ.ci) (l : Wd.Letter ℂ S) : EntrywiseClass μ ℓ (Wd.vlet σ l) := by
  unfold Wd.vlet
  refine entrywise_class_insert hℓ _ fun i j => ?_
  unfold Wd.lift0
  rw [Matrix.map_apply]
  refine entrywise_class_scalar ?_
  split_ifs
  · exact pg_Ts hℓ σ hp hc hci _ i j
  · rw [Matrix.map_apply]
    exact pg_star (pg_Ts hℓ σ hp hc hci _ i j)

theorem entrywise_class_word_transfer (hℓ : Continuous ℓ) (σ : Wd.Site (Q.Pr (V1 E))) (hp : PG μ ℓ σ.p) (hc : PG μ ℓ σ.c)
    (hci : PG μ ℓ σ.ci) : ∀ w : List (Wd.Letter ℂ S), EntrywiseClass μ ℓ (Wd.bT σ w)
  | [] => by rw [Wd.bT]; exact entrywise_class_one
  | l :: w => by
      rw [Wd.bT]
      exact entrywise_class_mul hℓ (entrywise_class_letter hℓ σ hp hc hci l) (entrywise_class_word_transfer hℓ σ hp hc hci w)

theorem entrywise_class_site_one (hℓ : Continuous ℓ) (κ : ℂ) (w : List (Wd.Letter ℂ S)) :
    EntrywiseClass μ ℓ (Wd.bT (site1 (E := E) κ) w) :=
  entrywise_class_word_transfer hℓ _ ⟨ok_opP hℓ κ, ok_neg (ok_opPb hℓ κ)⟩ ⟨ok_opM _ cd_id, ok_opM _ cd_conj⟩
    ⟨ok_opM _ cd_inv, ok_opM _ cd_conjinv⟩ w

theorem oneBT_int (hℓ : Continuous ℓ) (κ : ℂ) (w : List (Wd.Letter ℂ S)) (Φ : X → Wd.Ix S → V1 E)
    (x : Wd.Ix S → V1 E) (hG : ∀ b, Good (fun v => Φ v b)) (hI : ∀ b, IsInt μ ℓ (fun v => Φ v b) (x b))
    (a : Wd.Ix S) :
    Good (fun v => oneBT κ w (Φ v) a) ∧ IsInt μ ℓ (fun v => oneBT κ w (Φ v) a) (oneBT κ w x a) := by
  have hB := entrywise_class_site_one (μ := μ) (ℓ := ℓ) hℓ κ w
  unfold oneBT act1
  exact ⟨good_sum _ _ fun b _ => ((hB a b).1 _ _ (hG b) (hI b)).1,
    int_sum hℓ _ _ _ (fun b _ => ((hB a b).1 _ _ (hG b) (hI b)).1) fun b _ => ((hB a b).1 _ _ (hG b) (hI b)).2⟩

end pr

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas
end
end

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem good_of_goodFam {E X S : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup X]
    [NormedSpace ℝ X] {Φ : X → S → V1 E} (h : CutHB.GoodFam Φ) (e : S) : Good (fun v => Φ v e) := by
  refine ⟨h.1 e, fun K hK hK0 => ?_⟩
  obtain ⟨C, hC, hz⟩ := h.2 K hK hK0
  exact ⟨C, hC, fun v hv τ hτ => hz v hv τ hτ e⟩

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.SliceIntegralLemmas

theorem one_variable_letters_under_integral : CutHB.OneBTInt := by
  intro E _ _ _ X _ _ _ _ _ μ _ ℓ hℓ S _ _ κ w Φ hΦ f hf t ht e
  exact (oneBT_int (μ := μ) hℓ κ w Φ f (good_of_goodFam hΦ) (fun b τ hτ => hf b τ hτ) e).2 t ht

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RulesEq
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RulesOnPbT
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBQ

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section nl

variable {k : ℕ}

def cL {j ρ : ℕ} (a : Fin j → ℂ) : Fin (2 * ρ + k + 1) → Fin j → ℂ :=
  fun v α => if v.val = 2 * ρ + k then a (Fin.rev α) else 0

theorem nL_apply {j ρ : ℕ} (hρ : 1 ≤ ρ) (a : Fin j → ℂ) (p q : Fin (2 * (j + ρ) + k + 1)) :
    LevelPointCoordinates.nL k (j + ρ) j (by omega) a p q =
      (if p = q then 1 else 0) +
        (if h : p.val = j + 2 * ρ + k ∧ j + 2 * ρ + k + 1 ≤ q.val then a ⟨2 * (j + ρ) + k - q.val, by omega⟩ else 0) -
        (if h : p.val < j ∧ q.val = j then conj (a ⟨p.val, h.1⟩) else 0) := by
  have hS1 : (∑ c : Fin j, if esI k (j + ρ) ⟨j, by omega⟩ = p ∧ esI k (j + ρ) ⟨c.val, by omega⟩ = q then a c else 0) =
      (if h : p.val = j + 2 * ρ + k ∧ j + 2 * ρ + k + 1 ≤ q.val then a ⟨2 * (j + ρ) + k - q.val, by omega⟩ else 0) := by
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨2 * (j + ρ) + k - q.val, by omega⟩]
      · rw [if_pos]
        constructor <;> apply Fin.ext <;> simp [esI] <;> omega
      · intro b _ hb
        rw [if_neg]
        rintro ⟨_, h2⟩
        apply hb
        apply Fin.ext
        have := congrArg Fin.val h2
        simp [esI] at this
        simp
        omega
      · simp
    · refine Finset.sum_eq_zero fun b _ => ?_
      rw [if_neg]
      rintro ⟨h1, h2⟩
      apply h
      have e1 := congrArg Fin.val h1
      have e2 := congrArg Fin.val h2
      simp [esI] at e1 e2
      have := b.isLt
      omega
  have hS2 : (∑ c : Fin j, if eI k (j + ρ) ⟨c.val, by omega⟩ = p ∧ eI k (j + ρ) ⟨j, by omega⟩ = q then
      conj (a c) else 0) = (if h : p.val < j ∧ q.val = j then conj (a ⟨p.val, h.1⟩) else 0) := by
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨p.val, h.1⟩]
      · rw [if_pos]
        constructor <;> apply Fin.ext <;> simp [eI] <;> omega
      · intro b _ hb
        rw [if_neg]
        rintro ⟨h1, _⟩
        apply hb
        apply Fin.ext
        have := congrArg Fin.val h1
        simp [eI] at this
        simp
        omega
      · simp
    · refine Finset.sum_eq_zero fun b _ => ?_
      rw [if_neg]
      rintro ⟨h1, h2⟩
      apply h
      have e1 := congrArg Fin.val h1
      have e2 := congrArg Fin.val h2
      simp [eI] at e1 e2
      have := b.isLt
      omega
  unfold LevelPointCoordinates.nL
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.sum_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
  rw [hS1, hS2]
  ring

theorem skewOf_zero {j : ℕ} : U.skewOf (0 : (G.UT j → ℂ) × (Fin j → ℝ)) = 0 := by
  ext a b
  simp [U.skewOf, G.strictUpper]

theorem hpk_last {ρ : ℕ} (hρ : 1 ≤ ρ) (v : Fin (2 * ρ + k + 1)) :
    Hpk k ρ ⟨2 * ρ + k, by omega⟩ v = if v.val = 0 then 1 else 0 := by
  unfold Hpk
  have hv := v.isLt
  simp only [Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem cL_last {j ρ : ℕ} (a : Fin j → ℂ) (v : Fin (2 * ρ + k + 1)) (α : Fin j) :
    (cL (k := k) (ρ := ρ) a) v α = if v.val = 2 * ρ + k then a (Fin.rev α) else 0 := rfl

theorem cHc_zero {j ρ : ℕ} (hρ : 1 ≤ ρ) (a : Fin j → ℂ) :
    (Matrix.of (cL (k := k) (ρ := ρ) a))ᴴ * Hpk k ρ * Matrix.of (cL (k := k) (ρ := ρ) a) = 0 := by
  ext β γ
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, cL_last, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun v _ => ?_
  by_cases hv : v.val = 2 * ρ + k
  · rw [if_pos hv, Finset.sum_eq_single v]
    · have h := hpk_last (k := k) hρ v
      rw [show (⟨2 * ρ + k, by omega⟩ : Fin (2 * ρ + k + 1)) = v from Fin.ext hv.symm] at h
      rw [h, if_neg (show ¬ (v.val = 0) by omega)]
      simp
    · intro u _ hu
      by_cases hu' : u.val = 2 * ρ + k
      · exact absurd (Fin.ext (hu'.trans hv.symm)) hu
      · simp [hu']
    · simp
  · simp [hv]

theorem wcH_apply {j ρ : ℕ} (hρ : 1 ≤ ρ) (a : Fin j → ℂ) (α : Fin j) (v : Fin (2 * ρ + k + 1)) :
    (G.wMat j * (Matrix.of (cL (k := k) (ρ := ρ) a))ᴴ * Hpk k ρ) α v = if v.val = 0 then conj (a α) else 0 := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single α.rev]
  · rw [show G.wMat j α α.rev = 1 by simp [G.wMat], one_mul, Matrix.mul_apply,
      Finset.sum_eq_single ⟨2 * ρ + k, by omega⟩]
    · rw [hpk_last hρ, Matrix.conjTranspose_apply, Matrix.of_apply, cL_last, if_pos rfl, Fin.rev_rev]
      split_ifs <;> simp
    · intro u _ hu
      rw [Matrix.conjTranspose_apply, Matrix.of_apply, cL_last, if_neg (fun h => hu (Fin.ext h))]
      simp
    · simp
  · intro β _ hβ
    rw [show G.wMat j α β = 0 by simp [G.wMat]; exact fun h => hβ h, zero_mul]
  · simp

theorem nL_eq {j ρ : ℕ} (hρ : 1 ≤ ρ) (a : Fin j → ℂ) :
    LevelPointCoordinates.nL k (j + ρ) j (by omega) a = U.Rn k j ρ (cL a, 0) := by
  ext p q
  obtain ⟨x, rfl⟩ := (U.eB k j ρ).surjective p
  obtain ⟨y, rfl⟩ := (U.eB k j ρ).surjective q
  rw [nL_apply hρ, Ux3.rn_eq, Ux3.block3_apply]
  simp only [cHc_zero hρ, skewOf_zero, smul_zero, add_zero, Matrix.mul_zero]
  have v1 := @Ux3.block_index_first_val k j ρ
  have v2 := @Ux3.block_index_middle_val k j ρ
  have v3 := @Ux3.block_index_last_val k j ρ
  rcases x with ((α | u) | α) <;> rcases y with ((β | v) | β) <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply, Matrix.one_apply, Matrix.neg_apply, Matrix.of_apply,
      EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, v1, v2, v3]
  · have := α.isLt; have := β.isLt
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]; ring
  · have := α.isLt; have := v.isLt
    rw [wcH_apply hρ, dite_eq_right (by omega)]
    by_cases hv : v.val = 0
    · rw [dite_eq_left ⟨α.isLt, by omega⟩, if_pos hv]; simp
    · rw [dite_eq_right (by omega), if_neg hv]; simp
  · have := α.isLt; have := β.isLt
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]; ring
  · have := u.isLt; have := β.isLt
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]; ring
  · have := u.isLt; have := v.isLt
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]; ring
  · have := u.isLt; have := β.isLt
    rw [cL_last, dite_eq_right (show ¬(j + u.val < j ∧ j + (2 * ρ + k + 1) + β.val = j) by omega)]
    by_cases hu : u.val = 2 * ρ + k
    · rw [dite_eq_left (show j + u.val = j + 2 * ρ + k ∧ j + 2 * ρ + k + 1 ≤ j + (2 * ρ + k + 1) + β.val by omega),
        if_pos hu]
      have e : (⟨2 * (j + ρ) + k - (j + (2 * ρ + k + 1) + β.val), by omega⟩ : Fin j) = β.rev :=
        Fin.ext (by simp [Fin.rev]; omega)
      rw [e]; ring
    · rw [dite_eq_right (show ¬(j + u.val = j + 2 * ρ + k ∧ j + 2 * ρ + k + 1 ≤ j + (2 * ρ + k + 1) + β.val) by omega),
        if_neg hu]; ring
  · have := α.isLt; have := β.isLt
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]; ring
  · have := α.isLt; have := v.isLt
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]; ring
  · have := α.isLt; have := β.isLt
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]; ring

end nl

section tower

variable {k : ℕ}

theorem nL_castM {r j : ℕ} (hj : j + 1 ≤ r) (a : Fin j → ℂ) :
    LevelPointCoordinates.nL k r j hj a = D.castM (by omega : j + (r - j) = r) (U.Rn k j (r - j) (cL a, 0)) := by
  have key : ∀ (ρ r' : ℕ) (e : j + ρ = r') (hj' : j + 1 ≤ r'),
      LevelPointCoordinates.nL k r' j hj' a = D.castM e (U.Rn k j ρ (cL a, 0)) := by
    intro ρ r' e hj'
    subst e
    rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
    exact nL_eq (by omega) a
  exact key (r - j) r (by omega) hj

theorem nL_mem {r j : ℕ} (hj : j + 1 ≤ r) (a : Fin j → ℂ) : LevelPointCoordinates.nL k r j hj a ∈ Nset k r := by
  rw [nL_castM hj a]
  exact PBH.castM_N _ (LeftFubiniLemmas.rn_nset _)

theorem psi_castM {j ρ r : ℕ} (e : j + ρ = r) (zj : Fin (2 * ρ + k + 1) → ℂ) (z : Fin (2 * r + k + 1) → ℂ)
    (hz : D.castV e (liftVec k j ρ zj) = z) (c : ℂ) (M : B.Mat k (j + ρ)) :
    psi k r z c (D.castM e M) = psi k (j + ρ) (liftVec k j ρ zj) c M := by
  subst e
  rw [Formalism.FourierDecayAlt.P.JCTx5.castV_rfl] at hz
  subst hz
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem domP_sgs {r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (j : ℕ) {pp : B.SS k r} (hp : Bs.inSS pp) {g : Q.Mx k r}
    (hg : g ∈ domP k r j Bs.z Bs.z') : B.sgs pp g ∈ domP k r j Bs.z Bs.z' :=
  ⟨fun l h1 h2 => by rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp]; exact hg.1 l h1 h2,
    by unfold Gf; rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp, Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp]; exact hg.2⟩

theorem minorDomain_mul_unipotent {r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (j : ℕ) {g : Q.Mx k r}
    (hg : g ∈ domP k r j Bs.z Bs.z') {m : Q.Mx k r} (hm : m ∈ Nset k r) : g * m ∈ domP k r j Bs.z Bs.z' := by
  have hp : Bs.inSS ((Matrix.of.symm 1, Matrix.of.symm 1), (Matrix.of.symm 1, Matrix.of.symm m)) :=
    ⟨Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_one, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, hm⟩
  have hs : B.sgs ((Matrix.of.symm 1, Matrix.of.symm 1), (Matrix.of.symm 1, Matrix.of.symm m)) g = g * m := by
    simp only [B.sgs, Equiv.apply_symm_apply, inv_one, one_mul, mul_one]
  rw [← hs]
  exact domP_sgs Bs j hp hg

theorem domP_N_mul {r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (j : ℕ) {g : Q.Mx k r}
    (hg : g ∈ domP k r j Bs.z Bs.z') {m : Q.Mx k r} (hm : m ∈ Nset k r) : m * g ∈ domP k r j Bs.z Bs.z' := by
  have hmi : m⁻¹ ∈ Nset k r := Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hm
  have hp : Bs.inSS ((Matrix.of.symm 1, Matrix.of.symm m⁻¹), (Matrix.of.symm 1, Matrix.of.symm 1)) :=
    ⟨Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, hmi, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_one⟩
  have hu : IsUnit m.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hm.1
  have hs : B.sgs ((Matrix.of.symm 1, Matrix.of.symm m⁻¹), (Matrix.of.symm 1, Matrix.of.symm 1)) g = m * g := by
    simp only [B.sgs, Equiv.apply_symm_apply, inv_one, one_mul, mul_one,
      Matrix.nonsing_inv_nonsing_inv _ hu]
  rw [← hs]
  exact domP_sgs Bs j hp hg

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

end tower

end Formalism.FourierDecayAlt.P.PBQ
end
end

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBQ

theorem rules_eq : CutHB.RulesEq := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj _hF
  refine ⟨fun g hg m hm => ⟨minorDomain_mul_unipotent p.T.base j hg.2 hm, ?_⟩,
    fun g hg a => ⟨domP_N_mul p.T.base j hg.2 (nL_mem hj a), ?_⟩⟩
  · exact pbF_right _ _ _ F g m hm
  · show pbF (p.T.bs j) p.T.base _ F (LevelPointCoordinates.nL P.k P.r j hj a * g) =
      psi P.k P.r p.T.base.z cStd (LevelPointCoordinates.nL P.k P.r j hj a) • pbF (p.T.bs j) p.T.base _ F g
    rw [nL_castM hj a, pbF_left_rn p.T.base _ (p.T.bs j).z_mem F (cL a, 0) g,
      psi_castM _ (p.T.bs j).z p.T.base.z (p.T.z_lev j (by omega))]

end Formalism.FourierDecayAlt.P
end
end

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHB

theorem headBridge_of_rest (hPr : ProperDomP) (hW : WordSmooth) (h1 : Side1) : LevelPointCoordinates.HeadBridge :=
  headBridge_of Formalism.FourierDecayAlt.P.rules_eq hW pts curveSmooth (supp_of Formalism.FourierDecayAlt.P.letters_pass_partial_bessel hPr)
    (Formalism.FourierDecayAlt.P.SliceIntegralLemmas.side_zero_of_local_properness hPr) h1 Formalism.FourierDecayAlt.P.one_variable_letters_under_integral

end Formalism.FourierDecayAlt.P.CutHB
