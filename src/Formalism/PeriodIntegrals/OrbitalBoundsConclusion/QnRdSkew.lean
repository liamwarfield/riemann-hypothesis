module

public import Formalism.HermitianCurvature.StatementQ
public import Formalism.FormalDegreeBessel.FinalG
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmCapComm

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkewAnalyticGroup.Development
open Matrix MeasureTheory
open scoped ContDiff

noncomputable section

namespace QnRdSkewW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def SmoothOnSet {n : ℕ} (G : Set (Matrix (Fin n) (Fin n) ℂ)) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∀ g₀ ∈ G, ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → ℂ),
    IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ g ∈ U, g ∈ G → f g = F g

def StepGroup : Prop :=
  ∀ (k r : ℕ) (i : Fin (r + 1)) (X : Mx k r), inLieLev k r i X →
    IsClosed (Glev k r i) ∧ (∀ g ∈ Glev k r i, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i) ∧
      ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i

def StepAnalytic : Prop :=
  ∀ (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ)) (μ : Measure (Fin n → Fin n → ℂ)) (X : Matrix (Fin n) (Fin n) ℂ)
    (f₁ f₂ : Matrix (Fin n) (Fin n) ℂ → ℂ),
    IsClosed G → (∀ g ∈ G, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ G) → μ Gᶜ = 0 →
    (∀ t : ℝ, μ.map (B.rmulF (NormedSpace.exp ((t : ℂ) • X))) = μ) →
    (∀ K : Set (Fin n → Fin n → ℂ), IsCompact K → μ K < ⊤) →
    SmoothOnSet G f₁ → SmoothOnSet G f₂ →
    (∃ K : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact K ∧ ∀ g ∈ G, g ∉ K → f₁ g = 0) →
    (∃ K : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact K ∧ ∀ g ∈ G, g ∉ K → f₂ g = 0) →
    (∫ x, RdV X f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ) =
      -∫ x, f₁ (Matrix.of x) * star (RdV X f₂ (Matrix.of x)) ∂μ

theorem rdSkew_of (h1 : StepGroup) (h2 : StepAnalytic) : RdSkew := by
  intro k r i μ hμ X f₁ f₂ hX hs₁ hs₂ hc₁ hc₂
  obtain ⟨hcl, hfl, hexp⟩ := h1 k r i X hX
  exact h2 (2 * r + k + 1) (Glev k r i) μ X f₁ f₂ hcl hfl hμ.conc
    (fun t => hμ.right _ (hexp t)) hμ.finite_compact
    (fun g₀ hg₀ => hs₁ g₀ ⟨hg₀, Set.mem_univ _⟩) (fun g₀ hg₀ => hs₂ g₀ ⟨hg₀, Set.mem_univ _⟩) hc₁ hc₂

end QnRdSkewW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkewAnalyticGroup.Analytic
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkewAnalyticGroup.IntegrableOfContOn
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkewAnalyticGroup.HasDerivAtShift
open Matrix MeasureTheory Filter Topology Set
open scoped ContDiff

noncomputable section

namespace QnRdSkewW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma exp_flow_cont {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) := by
  fun_prop

end Linfty

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {X : Matrix (Fin n) (Fin n) ℂ}

lemma flow_zero (g : Matrix (Fin n) (Fin n) ℂ) :
    g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by
  simp

lemma hasDerivAt_local (hG : ∀ g ∈ G, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ G)
    {f F : Matrix (Fin n) (Fin n) ℂ → ℂ} {U : Set (Matrix (Fin n) (Fin n) ℂ)} {g : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsOpen U) (hgU : g ∈ U) (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ h ∈ U, h ∈ G → f h = F h) (hg : g ∈ G) :
    HasDerivAt (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 := by
  have h0 := Formalism.REAL.hasDerivAt_matrix_exp_smul_at_zero X
  have hc : HasDerivAt (fun u : ℝ => g * NormedSpace.exp ((u : ℂ) • X)) (g * X) 0 := by
    have hL := (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ g)).hasFDerivAt
      (x := NormedSpace.exp (((0 : ℝ) : ℂ) • X))
    exact hL.comp_hasDerivAt (0 : ℝ) h0
  have hFd : HasFDerivAt F (fderiv ℝ F g) g :=
    ((hF.contDiffAt (hU.mem_nhds hgU)).differentiableAt (by simp)).hasFDerivAt
  have hcomp : HasDerivAt (fun u : ℝ => F (g * NormedSpace.exp ((u : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 :=
    hFd.comp_hasDerivAt_of_eq (0 : ℝ) hc (flow_zero g).symm
  have hU0 : U ∈ 𝓝 (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [flow_zero]; exact hU.mem_nhds hgU
  have hev : (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) =ᶠ[𝓝 0]
      (fun u : ℝ => F (g * NormedSpace.exp ((u : ℂ) • X))) := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds hU0] with u hu
    exact hfF _ hu (hG g hg u)
  exact hcomp.congr_of_eventuallyEq hev

lemma rdV_local (hG : ∀ g ∈ G, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ G)
    {f F : Matrix (Fin n) (Fin n) ℂ → ℂ} {U : Set (Matrix (Fin n) (Fin n) ℂ)} {g : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsOpen U) (hgU : g ∈ U) (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ h ∈ U, h ∈ G → f h = F h) (hg : g ∈ G) :
    RdV X f g = fderiv ℝ F g (g * X) := (hasDerivAt_local hG hU hgU hF hfF hg).deriv

lemma hasDerivAt_zero (hG : ∀ g ∈ G, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ G)
    {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnSet G f) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G) :
    HasDerivAt (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) (RdV X f g) 0 := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  rw [rdV_local hG hU hgU hF hfF hg]
  exact hasDerivAt_local hG hU hgU hF hfF hg

lemma hasDerivAt_shift (hG : ∀ g ∈ G, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ G)
    {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnSet G f) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (g * NormedSpace.exp ((s : ℂ) • X)))
      (RdV X f (g * NormedSpace.exp ((t : ℂ) • X))) t := by
  have hh : g * NormedSpace.exp ((t : ℂ) • X) ∈ G := hG g hg t
  have h0 := hasDerivAt_zero hG hf hh
  have h0' : HasDerivAt (fun u : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((u : ℂ) • X)))
      (RdV X f (g * NormedSpace.exp ((t : ℂ) • X))) (t - t) := by
    rw [sub_self]; exact h0
  refine (h0'.comp_sub_const t t).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  show f (g * NormedSpace.exp ((s : ℂ) • X)) =
    f (g * NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp (((s - t : ℝ) : ℂ) • X))
  have hcomm : Commute ((t : ℂ) • X) (((s - t : ℝ) : ℂ) • X) :=
    ((Commute.refl X).smul_left _).smul_right _
  have e : (t : ℂ) • X + ((s - t : ℝ) : ℂ) • X = (s : ℂ) • X := by
    rw [← add_smul]; congr 1; push_cast; ring
  rw [mul_assoc, ← Matrix.exp_add_of_commute _ _ hcomm, e]

lemma contOn_of_smooth {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnSet G f) : ContinuousOn f G := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ hg₀
  have hFc : ContinuousAt F g₀ := hF.continuousOn.continuousAt (hU.mem_nhds hg₀U)
  refine hFc.continuousWithinAt.congr_of_eventuallyEq ?_ (hfF g₀ hg₀U hg₀)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hg₀U), self_mem_nhdsWithin] with g hgU hgG
  exact hfF g hgU hgG

lemma contOn_rdV (hG : ∀ g ∈ G, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ G)
    {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnSet G f) : ContinuousOn (RdV X f) G := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ hg₀
  have hd : ContinuousOn (fderiv ℝ F) U := hF.continuousOn_fderiv_of_isOpen hU (by simp)
  have hc : ContinuousAt (fun g => fderiv ℝ F g (g * X)) g₀ :=
    (hd.continuousAt (hU.mem_nhds hg₀U)).clm_apply
      ((continuous_id.matrix_mul continuous_const).continuousAt)
  refine hc.continuousWithinAt.congr_of_eventuallyEq ?_ (rdV_local hG hU hg₀U hF hfF hg₀)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hg₀U), self_mem_nhdsWithin] with g hgU hgG
  exact rdV_local hG hU hgU hF hfF hgG

end QnRdSkewW
end
end

open Matrix MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

noncomputable section

namespace QnRdSkewW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {μ : Measure (Fin n → Fin n → ℂ)}

lemma cont_of : Continuous (fun x : Fin n → Fin n → ℂ => (Matrix.of x : Matrix (Fin n) (Fin n) ℂ)) := continuous_id

lemma ae_mem (hconc : μ Gᶜ = 0) : ∀ᵐ x ∂μ, (Matrix.of x : Matrix (Fin n) (Fin n) ℂ) ∈ G := by
  exact MeasureTheory.mem_ae_iff.mpr hconc

lemma aesm_of_contOn (hGc : IsClosed G) (hconc : μ Gᶜ = 0) {φ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hφ : ContinuousOn φ G) : AEStronglyMeasurable (fun x : Fin n → Fin n → ℂ => φ (Matrix.of x)) μ := by
  have hcl : IsClosed {x : Fin n → Fin n → ℂ | Matrix.of x ∈ G} := hGc.preimage cont_of
  have h1 : ContinuousOn (fun x : Fin n → Fin n → ℂ => φ (Matrix.of x))
      {x : Fin n → Fin n → ℂ | Matrix.of x ∈ G} :=
    hφ.comp cont_of.continuousOn (fun x hx => hx)
  have h2 := h1.aestronglyMeasurable (μ := μ) hcl.measurableSet
  rwa [Measure.restrict_eq_self_of_ae_mem (s := {x : Fin n → Fin n → ℂ | Matrix.of x ∈ G}) (ae_mem hconc)] at h2

lemma integrable_of_contOn (hGc : IsClosed G) (hconc : μ Gᶜ = 0)
    (hfin : ∀ K : Set (Fin n → Fin n → ℂ), IsCompact K → μ K < ⊤) {φ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hφ : ContinuousOn φ G) {K : Set (Matrix (Fin n) (Fin n) ℂ)} (hK : IsCompact K)
    (hz : ∀ g ∈ G, g ∉ K → φ g = 0) : Integrable (fun x : Fin n → Fin n → ℂ => φ (Matrix.of x)) μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨hfin⟩
  have hSc : IsCompact {x : Fin n → Fin n → ℂ | Matrix.of x ∈ K ∩ G} := hK.inter_right hGc
  have hcont : ContinuousOn (fun x : Fin n → Fin n → ℂ => φ (Matrix.of x))
      {x : Fin n → Fin n → ℂ | Matrix.of x ∈ K ∩ G} :=
    hφ.comp cont_of.continuousOn (fun x hx => hx.2)
  have hI := hcont.integrableOn_compact (μ := μ) hSc
  have hInd := (integrable_indicator_iff hSc.isClosed.measurableSet).mpr hI
  refine hInd.congr ?_
  filter_upwards [ae_mem hconc] with x hx
  by_cases hxK : (Matrix.of x) ∈ K
  · exact Set.indicator_of_mem (show x ∈ {x : Fin n → Fin n → ℂ | Matrix.of x ∈ K ∩ G} from ⟨hxK, hx⟩) _
  · rw [Set.indicator_of_notMem (by exact fun h => hxK h.1), hz _ hx hxK]

end QnRdSkewW
end
end

open Matrix MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

noncomputable section

namespace QnRdSkewW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private theorem RdV_eq_zero_of_not_mem_compact {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}
    {X : Matrix (Fin n) (Fin n) ℂ}
    (hG : ∀ g ∈ G, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ G)
    {f : Matrix (Fin n) (Fin n) ℂ → ℂ} {K : Set (Matrix (Fin n) (Fin n) ℂ)} (hK : IsCompact K)
    (hz : ∀ g ∈ G, g ∉ K → f g = 0) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G) (hgK : g ∉ K) :
    RdV X f g = 0 := by
  rw [rdV_local (F := fun _ => (0 : ℂ)) hG hK.isClosed.isOpen_compl hgK contDiffOn_const
    (fun h hU hGh => hz h hGh hU) hg]
  simp

theorem skew_reduction_analytic : StepAnalytic := by
  intro n G μ X f₁ f₂ hGc hG hconc hinv hfin hs₁ hs₂ hK₁ _
  obtain ⟨K₁, hK₁c, hz₁⟩ := hK₁
  have hc₁ := contOn_of_smooth hs₁
  have hc₂ := contOn_of_smooth hs₂
  have hd₁ : ContinuousOn (RdV X f₁) G := contOn_rdV hG hs₁
  have hd₂ : ContinuousOn (RdV X f₂) G := contOn_rdV hG hs₂
  have hr₁ : ∀ g ∈ G, g ∉ K₁ → RdV X f₁ g = 0 := fun g hg hgK => RdV_eq_zero_of_not_mem_compact hG hK₁c hz₁ hg hgK
  have hPc : ContinuousOn (fun g => f₁ g * star (f₂ g)) G := hc₁.mul hc₂.star
  have hQc : ContinuousOn (fun g => RdV X f₁ g * star (f₂ g) + f₁ g * star (RdV X f₂ g)) G :=
    (hd₁.mul hc₂.star).add (hc₁.mul hd₂.star)
  have hQz : ∀ g ∈ G, g ∉ K₁ → RdV X f₁ g * star (f₂ g) + f₁ g * star (RdV X f₂ g) = 0 := by
    intro g hg hgK
    rw [hr₁ g hg hgK, hz₁ g hg hgK]
    simp
  have hrm : ∀ a : Matrix (Fin n) (Fin n) ℂ, Measurable (B.rmulF a) := fun a =>
    Continuous.measurable (show Continuous (B.rmulF a) from cont_of.matrix_mul continuous_const)
  have hinvI : ∀ t : ℝ,
      ∫ x, f₁ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X)) *
          star (f₂ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X))) ∂μ =
        ∫ x, f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ := by
    intro t
    have hsm : AEStronglyMeasurable (fun y : Fin n → Fin n → ℂ => f₁ (Matrix.of y) * star (f₂ (Matrix.of y)))
        (μ.map (B.rmulF (NormedSpace.exp ((t : ℂ) • X)))) := by
      rw [hinv t]
      exact aesm_of_contOn hGc hconc hPc
    have h := integral_map (hrm (NormedSpace.exp ((t : ℂ) • X))).aemeasurable hsm
    rw [hinv t] at h
    exact h.symm
  have hF_meas : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), AEStronglyMeasurable (fun x : Fin n → Fin n → ℂ =>
      f₁ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X)) *
        star (f₂ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X)))) μ :=
    Filter.Eventually.of_forall fun t =>
      aesm_of_contOn (φ := fun g => f₁ (g * NormedSpace.exp ((t : ℂ) • X)) *
          star (f₂ (g * NormedSpace.exp ((t : ℂ) • X)))) hGc hconc
        (hPc.comp (continuous_id.matrix_mul continuous_const).continuousOn fun g hg => hG g hg t)
  have hF_int : Integrable (fun x : Fin n → Fin n → ℂ =>
      f₁ (Matrix.of x * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) *
        star (f₂ (Matrix.of x * NormedSpace.exp (((0 : ℝ) : ℂ) • X)))) μ := by
    simp only [flow_zero]
    exact integrable_of_contOn hGc hconc hfin hPc hK₁c (fun g hg hgK => by simp [hz₁ g hg hgK])
  have hF'_meas : AEStronglyMeasurable (fun x : Fin n → Fin n → ℂ =>
      RdV X f₁ (Matrix.of x * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) *
          star (f₂ (Matrix.of x * NormedSpace.exp (((0 : ℝ) : ℂ) • X))) +
        f₁ (Matrix.of x * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) *
          star (RdV X f₂ (Matrix.of x * NormedSpace.exp (((0 : ℝ) : ℂ) • X)))) μ := by
    simp only [flow_zero]
    exact aesm_of_contOn hGc hconc hQc
  obtain ⟨C, hC⟩ := (hK₁c.inter_left hGc).exists_bound_of_continuousOn (hQc.mono Set.inter_subset_left)
  set L : Set (Matrix (Fin n) (Fin n) ℂ) :=
    (fun p : Matrix (Fin n) (Fin n) ℂ × ℝ => p.1 * NormedSpace.exp ((p.2 : ℂ) • X)) ''
      (K₁ ×ˢ Icc (-1 : ℝ) 1) with hLdef
  have hL : IsCompact L :=
    (hK₁c.prod isCompact_Icc).image (continuous_fst.matrix_mul ((exp_flow_cont X).comp continuous_snd))
  have hS : IsCompact (Matrix.of ⁻¹' L : Set (Fin n → Fin n → ℂ)) := hL
  have hbound_int : Integrable ((Matrix.of ⁻¹' L).indicator fun _ => max C 0) μ :=
    (integrable_indicator_iff hS.measurableSet).2 (integrableOn_const (hfin _ hS).ne)
  have h_bound : ∀ᵐ x ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) 1,
      ‖RdV X f₁ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X)) *
            star (f₂ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X))) +
          f₁ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X)) *
            star (RdV X f₂ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X)))‖ ≤
        (Matrix.of ⁻¹' L).indicator (fun _ => max C 0) x := by
    filter_upwards [ae_mem hconc] with x hx t ht
    have hgt := hG _ hx t
    by_cases hk : Matrix.of x * NormedSpace.exp ((t : ℂ) • X) ∈ K₁
    · have ht' : |t| < 1 := by simpa [Real.dist_eq] using ht
      have hxS : x ∈ (Matrix.of ⁻¹' L : Set (Fin n → Fin n → ℂ)) := by
        refine ⟨(Matrix.of x * NormedSpace.exp ((t : ℂ) • X), -t),
          ⟨hk, by linarith [abs_lt.1 ht'], by linarith [abs_lt.1 ht']⟩, ?_⟩
        have hcomm : Commute ((t : ℂ) • X) (-((t : ℂ) • X)) := (Commute.refl _).neg_right
        show Matrix.of x * NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp (((-t : ℝ) : ℂ) • X) =
          Matrix.of x
        rw [mul_assoc, show (((-t : ℝ) : ℂ) • X) = -((t : ℂ) • X) by push_cast; exact neg_smul _ _,
          ← Matrix.exp_add_of_commute _ _ hcomm, add_neg_cancel, NormedSpace.exp_zero, mul_one]
      rw [Set.indicator_of_mem hxS]
      exact (hC _ ⟨hgt, hk⟩).trans (le_max_left _ _)
    · rw [hQz _ hgt hk, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => le_max_right _ _) _
  have h_diff : ∀ᵐ x ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => f₁ (Matrix.of x * NormedSpace.exp ((s : ℂ) • X)) *
          star (f₂ (Matrix.of x * NormedSpace.exp ((s : ℂ) • X))))
        (RdV X f₁ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X)) *
            star (f₂ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X))) +
          f₁ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X)) *
            star (RdV X f₂ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X)))) t := by
    filter_upwards [ae_mem hconc] with x hx t _
    exact (hasDerivAt_shift hG hs₁ hx t).mul (hasDerivAt_shift hG hs₂ hx t).star
  have hderiv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (t : ℝ) (x : Fin n → Fin n → ℂ) => f₁ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X)) *
      star (f₂ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X))))
    (F' := fun (t : ℝ) (x : Fin n → Fin n → ℂ) =>
      RdV X f₁ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X)) *
          star (f₂ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X))) +
        f₁ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X)) *
          star (RdV X f₂ (Matrix.of x * NormedSpace.exp ((t : ℂ) • X))))
    (Metric.ball_mem_nhds (0 : ℝ) one_pos) hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  have hconst : HasDerivAt (fun _ : ℝ => ∫ x, f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ)
      (∫ x, (RdV X f₁ (Matrix.of x * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) *
          star (f₂ (Matrix.of x * NormedSpace.exp (((0 : ℝ) : ℂ) • X))) +
        f₁ (Matrix.of x * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) *
          star (RdV X f₂ (Matrix.of x * NormedSpace.exp (((0 : ℝ) : ℂ) • X)))) ∂μ) 0 := by
    exact hderiv.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (hinvI t).symm)
  have h0 := hconst.unique (hasDerivAt_const _ _)
  simp only [flow_zero] at h0
  have hI1 : Integrable (fun x : Fin n → Fin n → ℂ => RdV X f₁ (Matrix.of x) * star (f₂ (Matrix.of x))) μ :=
    integrable_of_contOn hGc hconc hfin (hd₁.mul hc₂.star) hK₁c (fun g hg hgK => by simp [hr₁ g hg hgK])
  have hI2 : Integrable (fun x : Fin n → Fin n → ℂ => f₁ (Matrix.of x) * star (RdV X f₂ (Matrix.of x))) μ :=
    integrable_of_contOn hGc hconc hfin (hc₁.mul hd₂.star) hK₁c (fun g hg hgK => by simp [hz₁ g hg hgK])
  rw [integral_add hI1 hI2] at h0
  exact eq_neg_of_add_eq_zero_left h0

end QnRdSkewW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkewAnalyticGroup.SkewReductionGroup
open Matrix Filter Topology

noncomputable section

namespace QnRdSkewW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma exp_mul_fix {n : ℕ} (X E : Matrix (Fin n) (Fin n) ℂ) (hXE : X * E = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) * E = E := _root_.QmCapCommW.exp_mul_fix (n := n) X E hXE t

end Linfty

lemma exp_mulVec_fix {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (hXv : X *ᵥ v = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) *ᵥ v = v := by
  let E : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun j _ => v j
  have hXE : X * E = 0 := by
    ext j l
    have := congrFun hXv j
    simpa [E, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have h := exp_mul_fix X E hXE t
  funext j
  have := congrFun (congrFun h j) j
  simpa [E, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

lemma exp_mem_UH {n : ℕ} (H Y : Matrix (Fin n) (Fin n) ℂ) (hH : H * H = 1) (hY : Yᴴ * H + H * Y = 0) :
    NormedSpace.exp Y ∈ UH H := by
  have hU : IsUnit H := IsUnit.of_mul_eq_one _ hH
  have hinv : H⁻¹ = H := Matrix.inv_eq_left_inv hH
  have h1 : Yᴴ * H = -(H * Y) := eq_neg_of_add_eq_zero_left hY
  have hYh : Yᴴ = H * (-Y) * H⁻¹ := by
    rw [hinv]
    calc Yᴴ = Yᴴ * H * H := by rw [Matrix.mul_assoc, hH, Matrix.mul_one]
      _ = H * (-Y) * H := by rw [h1, Matrix.mul_neg, Matrix.neg_mul]
  have hexp : (NormedSpace.exp Y)ᴴ = H * NormedSpace.exp (-Y) * H := by
    rw [← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ hU, hinv]
  have hc : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
      NormedSpace.exp_zero]
  show (NormedSpace.exp Y)ᴴ * H * NormedSpace.exp Y = H
  rw [hexp, Matrix.mul_assoc (H * NormedSpace.exp (-Y)) H H, hH, Matrix.mul_one, Matrix.mul_assoc, hc,
    Matrix.mul_one]

lemma glev_mul {k r : ℕ} {i : Fin (r + 1)} {g h : Mx k r} (hg : g ∈ Glev k r i) (hh : h ∈ Glev k r i) :
    g * h ∈ Glev k r i := by
  obtain ⟨hgU, hgF⟩ := hg
  obtain ⟨hhU, hhF⟩ := hh
  refine ⟨?_, fun a ha => ?_⟩
  · show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
    have e1 : gᴴ * Hpk k r * g = Hpk k r := hgU
    have e2 : hᴴ * Hpk k r * h = Hpk k r := hhU
    calc (g * h)ᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r := by rw [e1, e2]
  · obtain ⟨g1, g2⟩ := hgF a ha
    obtain ⟨h1, h2⟩ := hhF a ha
    refine ⟨?_, ?_⟩
    · rw [← Matrix.mulVec_mulVec, h1, g1]
    · rw [← Matrix.mulVec_mulVec, h2, g2]

lemma glev_closed (k r : ℕ) (i : Fin (r + 1)) : IsClosed (Glev k r i) := by
  have e : Glev k r i = {g : Mx k r | gᴴ * Hpk k r * g = Hpk k r} ∩
      ⋂ a : Fin r, ⋂ (_ : a.val < i.val),
        ({g : Mx k r | g *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩
          {g : Mx k r | g *ᵥ bvec (esI k r a) = bvec (esI k r a)}) := by
    ext g
    simp only [Glev, UH, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  refine IsClosed.inter ?_ (isClosed_iInter fun a => isClosed_iInter fun _ => IsClosed.inter ?_ ?_)
  · exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  · exact isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const
  · exact isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const

lemma exp_mem_glev {k r : ℕ} {i : Fin (r + 1)} {X : Mx k r} (hX : inLieLev k r i X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i := by
  obtain ⟨hL, hF⟩ := hX
  have hH : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  refine ⟨exp_mem_UH _ _ hH ?_, fun a ha => ?_⟩
  · rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, hL, smul_zero]
  · obtain ⟨h1, h2⟩ := hF a ha
    exact ⟨exp_mulVec_fix X _ h1 t, exp_mulVec_fix X _ h2 t⟩

theorem skew_reduction_group : StepGroup := by
  intro k r i X hX
  exact ⟨glev_closed k r i, fun g hg t => glev_mul hg (exp_mem_glev hX t), exp_mem_glev hX⟩

end QnRdSkewW
end
end

theorem qnRdSkew : Formalism.FourierDecayAlt.Q.RdSkew :=
  QnRdSkewW.rdSkew_of QnRdSkewW.skew_reduction_group QnRdSkewW.skew_reduction_analytic
