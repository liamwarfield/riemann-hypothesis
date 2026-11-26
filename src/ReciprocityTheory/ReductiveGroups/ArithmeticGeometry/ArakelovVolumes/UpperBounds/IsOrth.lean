module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.QuotientIsHausdorff
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.MvBlowup
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPfC

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def x0F (X : Data E r) : Frame X.Ψ r := fun τ => (X.signature τ).choose

def OmF (X : Data E r) (x0 : Frame X.Ψ r) : Set (V (nd X)) := {z | cpt X x0 z ∈ X.dom}

def rhF (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) : ℝ :=
  -∑ τ, Real.log ‖dmin X.Gm (cpt X x0 z) τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖

def eF (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) : ℝ := rhF X x0 z + Real.log (1 + ‖z‖ ^ 2)

def densF (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) : ℝ :=
  ∏ τ, ∏ i : Fin r, ‖dmin X.Gm (cpt X x0 z) τ i.castSucc‖ ^ (-2 : ℤ)

def muF (X : Data E r) (x0 : Frame X.Ψ r) : Measure (V (nd X)) :=
  (volume.restrict (OmF X x0)).withDensity fun z => ENNReal.ofReal (densF X x0 z)

def sat (X : Data E r) (x0 : Frame X.Ψ r) (C : Set (Frame X.Ψ r)) : Set (V (nd X)) :=
  {z | z ∈ OmF X x0 ∧ ∃ x ∈ C, ∃ b ∈ Bor X.Ψ r, cpt X x0 z = rmul x b}

def kaF (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (z : V (nd X)) : ℝ := Real.exp (-bb * rhF X x0 z)

def IsOrth (X : Data E r) (x : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

def poin (X : Data E r) (la : Wt X.Ψ r) (F : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℂ :=
  ∑' γ : X.Γ, (X.χ la γ.1)⁻¹ * F (lact γ.1 x)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStatementPfLA
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Asymptotics

noncomputable section

theorem analyticAt_of_diffOn {n : ℕ} {f : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {z : V n} (hz : z ∈ U) : AnalyticAt ℂ f z := by
  let e : V n ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  have hU' : IsOpen (e.symm ⁻¹' U) := hU.preimage e.symm.continuous
  have hf' : DifferentiableOn ℂ (f ∘ e.symm) (e.symm ⁻¹' U) :=
    hf.comp (e.symm : (Fin n → ℂ) →L[ℂ] V n).differentiableOn (fun y hy => hy)
  have hz' : e z ∈ e.symm ⁻¹' U := by simpa using hz
  have ha := ReciprocityTheory.AnForm.Osgood.osgood n _ _ hU' hf' (e z) hz'
  have hfe : f = (f ∘ e.symm) ∘ e := by
    funext w
    simp
  rw [hfe]
  exact ha.comp ((e : V n →L[ℂ] (Fin n → ℂ)).analyticAt z)

theorem isBigO_norm_pow_of_le {F : Type*} [NormedAddCommGroup F] {k d : ℕ} (h : k ≤ d) :
    (fun y : F => ‖y‖ ^ d) =O[𝓝 0] (fun y => ‖y‖ ^ k) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Metric.ball_mem_nhds (0 : F) one_pos] with y hy
  rw [mem_ball_zero_iff] at hy
  simp only [norm_pow, norm_norm, one_mul]
  exact pow_le_pow_of_le_one (norm_nonneg _) hy.le h

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustStatementPfB
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC

open Matrix Topology Filter
open scoped ComplexOrder Matrix
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB

variable {f p q N' : ℕ}

def dk (w : V (nD f p q)) (k : Fin f) : ℝ := (1 - Zof w k * (Zof w k)ᴴ).det.re

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD

open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC

variable {f p q N' : ℕ}

theorem contDiff_det_of {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {m : ℕ} {M : E → Matrix (Fin m) (Fin m) ℂ}
    (h : ∀ i j, ContDiff 𝕜 ∞ fun x => M x i j) : ContDiff 𝕜 ∞ fun x => (M x).det := by
  have e : (fun x => (M x).det) = fun x =>
      ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, M x (σ j) j := by
    funext x; rw [Matrix.det_apply']
  rw [e]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun j _ => h _ _)

theorem cd_coord {n : ℕ} (i : Fin n) : ContDiff ℂ ∞ fun v : V n => v i := by
  have h : (fun v : V n => v i) = ⇑(EuclideanSpace.proj i : V n →L[ℂ] ℂ) := by
    funext v; simp
  rw [h]; exact ContinuousLinearMap.contDiff _

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfD
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoD

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Set Metric

noncomputable section

variable {n : ℕ} {Ω : Set (V n)} {g : V n → ℂ}

theorem not_loc_zero (hΩ : IsOpen Ω) (hc : IsPreconnected Ω) (hg : DifferentiableOn ℂ g Ω)
    (hne : ∃ z ∈ Ω, g z ≠ 0) : ∀ z ∈ Ω, ¬ g =ᶠ[𝓝 z] 0 := by
  intro z hz hzero
  obtain ⟨z0, hz0, hgz0⟩ := hne
  set u := {w : V n | ∀ᶠ y in 𝓝 w, g y = (0 : V n → ℂ) y} with hu_def
  set v := {w : V n | ∀ᶠ y in 𝓝 w, ¬ (g =ᶠ[𝓝 y] 0)} with hv_def
  have hu : IsOpen u := isOpen_setOfPred_eventually_nhds
  have hv : IsOpen v := isOpen_setOfPred_eventually_nhds
  have hcov : Ω ⊆ u ∪ v := by
    intro w hw
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    obtain ⟨hnu, hnv⟩ := hcon
    obtain ⟨ρ, hρ, hB⟩ := Metric.isOpen_iff.1 hΩ w hw
    have hfr : ∃ᶠ y in 𝓝 w, g =ᶠ[𝓝 y] 0 := by
      rw [Filter.Frequently]; intro h; exact hnv h
    obtain ⟨y, hy1, hy2⟩ := (hfr.and_eventually (ball_mem_nhds w hρ)).exists
    have hB0 := C.ident n (ball w ρ) g y isOpen_ball (convex_ball w ρ) (hg.mono hB) hy2 hy1
    exact hnu (Filter.eventually_of_mem (ball_mem_nhds w hρ) fun x hx => hB0 hx)
  have hv0 : z0 ∈ v := by
    have hct : ContinuousAt g z0 := hg.continuousOn.continuousAt (hΩ.mem_nhds hz0)
    have hev : ∀ᶠ y in 𝓝 z0, g y ≠ 0 := hct.eventually_ne hgz0
    exact hev.mono fun y hy h => hy (by simpa using h.eq_of_nhds)
  obtain ⟨w, -, hwu, hwv⟩ := hc u v hu hv hcov ⟨z, hz, hzero⟩ ⟨z0, hz0, hv0⟩
  obtain ⟨y, hy1, hy2⟩ := ((Filter.Eventually.eventually_nhds hwu).and hwv).exists
  exact hy2 hy1

theorem null_zero (hΩ : IsOpen Ω) (hc : IsPreconnected Ω) (hg : DifferentiableOn ℂ g Ω)
    (hne : ∃ z ∈ Ω, g z ≠ 0) : volume (Ω ∩ {z | g z = 0}) = 0 := by
  apply measure_null_of_locally_null
  intro x hx
  obtain ⟨ρ, hρ, hB⟩ := Metric.isOpen_iff.1 hΩ x hx.1
  refine ⟨(Ω ∩ {z | g z = 0}) ∩ ball x ρ, inter_mem_nhdsWithin _ (ball_mem_nhds x hρ), ?_⟩
  have hnz : ∃ y ∈ ball x ρ, g y ≠ 0 := by
    by_contra h
    push Not at h
    exact not_loc_zero hΩ hc hg hne x hx.1
      (Filter.eventually_of_mem (ball_mem_nhds x hρ) fun y hy => h y hy)
  exact measure_mono_null (fun y hy => by
    simp only [mem_inter_iff, mem_setOf_eq, Metric.mem_ball] at hy ⊢; tauto) (extNull n x ρ g (hg.mono hB) hnz)

theorem ext_glue (hΩ : IsOpen Ω) (hc : IsPreconnected Ω) (hg : DifferentiableOn ℂ g Ω)
    (hne : ∃ z ∈ Ω, g z ≠ 0) {F' : V n → ℂ} (hF' : DifferentiableOn ℂ F' {z | z ∈ Ω ∧ g z ≠ 0})
    (hL2 : ∀ z ∈ Ω, ∃ ρ > 0, ball z ρ ⊆ Ω ∧
      ∫⁻ y in ball z ρ \ {y | g y = 0}, ENNReal.ofReal (‖F' y‖ ^ 2) < ⊤) :
    ∃ F : V n → ℂ, DifferentiableOn ℂ F Ω ∧ ∀ z ∈ Ω, g z ≠ 0 → F z = F' z := by
  classical
  have hU : ∀ z ∈ Ω, ∃ ρ > 0, ball z ρ ⊆ Ω ∧ ∃ U : V n → ℂ, DifferentiableOn ℂ U (ball z ρ) ∧
      EqOn U F' (ball z ρ \ {y | g y = 0}) := by
    intro z hz
    obtain ⟨ρ, hρ, hB, hI⟩ := hL2 z hz
    obtain ⟨U, hU1, hU2⟩ := ext n z ρ g F' (hg.mono hB) (hF'.mono fun y hy => ⟨hB hy.1, hy.2⟩) hI
    exact ⟨ρ, hρ, hB, U, hU1, hU2⟩
  choose! ρ hρ hB U hUd hEq using hU
  let F : V n → ℂ := fun z => if g z ≠ 0 then F' z else U z z
  have key : ∀ z0 ∈ Ω, ∀ w ∈ ball z0 (ρ z0), F w = U z0 w := by
    intro z0 hz0 w hw
    by_cases hgw : g w = 0
    · have hwΩ : w ∈ Ω := hB z0 hz0 hw
      simp only [F, hgw, ne_eq, not_true_eq_false, if_false]
      by_contra hne'
      have hN : ∀ᶠ y in 𝓝 w, y ∈ ball z0 (ρ z0) ∩ ball w (ρ w) :=
        (isOpen_ball.inter isOpen_ball).mem_nhds ⟨hw, mem_ball_self (hρ w hwΩ)⟩
      have h1 : ContinuousAt (U z0) w :=
        ((hUd z0 hz0).differentiableAt (isOpen_ball.mem_nhds hw)).continuousAt
      have h2 : ContinuousAt (U w) w :=
        ((hUd w hwΩ).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (hρ w hwΩ)))).continuousAt
      have hev : ∀ᶠ y in 𝓝 w, U w y - U z0 y ≠ 0 := (h2.sub h1).eventually_ne (sub_ne_zero.2 hne')
      have hfr : ∃ᶠ y in 𝓝 w, g y ≠ 0 := by
        rw [Filter.Frequently]
        intro h
        exact not_loc_zero hΩ hc hg hne w hwΩ (h.mono fun y hy => by simpa using hy)
      obtain ⟨y, hy1, hy2, hy3⟩ := (hfr.and_eventually (hN.and hev)).exists
      exact hy3 (sub_eq_zero.2 ((hEq w hwΩ ⟨hy2.2, hy1⟩).trans (hEq z0 hz0 ⟨hy2.1, hy1⟩).symm))
    · simp only [F, ne_eq, hgw, not_false_eq_true, if_true]
      exact (hEq z0 hz0 ⟨hw, hgw⟩).symm
  refine ⟨F, fun z0 hz0 => ?_, fun z _ hgz => by simp [F, hgz]⟩
  have hd : DifferentiableAt ℂ (U z0) z0 :=
    (hUd z0 hz0).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (hρ z0 hz0)))
  refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
  exact Filter.eventually_of_mem (ball_mem_nhds z0 (hρ z0 hz0)) fun w hw => key z0 hz0 w hw

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPf
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open Matrix
open scoped Matrix ComplexOrder ENNReal

noncomputable section

theorem SumBoundStatement_holds : SumBoundStatement := by
  intro f p q s hs Γ hd hU
  obtain ⟨c, hc, hsepΓ⟩ := sumBd_sep Γ hd hU
  obtain ⟨C, hC, hbound⟩ := sumBd_sum (p := p) (q := q) (f := f) hs hc
  refine ⟨C, hC, fun v hv => ?_⟩
  choose G hG hGw using fun k => sumBd_frame (hv k)
  let x : Γ → Fin f → Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := fun γ k =>
    ((γ.1 k : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * G k
  have hxU : ∀ a k, IsUpq (x a k) := fun a k => sumBd_isUpq_mul (hU a.1 a.2 k) (hG k)
  have hxsep : ∀ a b : Γ, a ≠ b → ∃ k i j,
      c ≤ ‖(x b k * (x a k)⁻¹) i j - (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖ := by
    intro a b hab
    have hmem : b.1 * a.1⁻¹ ∈ Γ := Γ.mul_mem b.2 (Γ.inv_mem a.2)
    have hne : b.1 * a.1⁻¹ ≠ 1 := fun h => hab (Subtype.ext (mul_inv_eq_one.mp h).symm)
    obtain ⟨k, i, j, hk⟩ := hsepΓ _ hmem hne
    refine ⟨k, i, j, le_of_le_of_eq hk ?_⟩
    have : x b k * (x a k)⁻¹ = (((b.1 * a.1⁻¹) k : GL (Fin p ⊕ Fin q) ℂ) :
        Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := by
      simp only [x, Pi.mul_apply, Pi.inv_apply, Units.val_mul, Matrix.coe_units_inv]
      rw [Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (G k), sumBd_mul_inv (hG k), Matrix.one_mul]
    rw [this]
  calc ∑' γ : Γ, ENNReal.ofReal (∏ k, dpow (mob ((γ.1 k : GL (Fin p ⊕ Fin q) ℂ) :
        Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (Zof v k)) s)
      = ∑' γ : Γ, ENNReal.ofReal (∏ k, (Complex.normSq (det (x γ k).toBlocks₂₂))⁻¹ ^ s) := by
        congr 1; funext γ
        rw [Finset.prod_congr rfl fun k _ => hGw k _ (hU γ.1 γ.2 k) s]
    _ ≤ C := hbound Γ x hxU hxsep

end
end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfD
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.HE

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ENNReal

noncomputable section

variable {n : ℕ} {U : Set (V n)}

theorem ext_glue (hU : IsOpen U) (g G : V n → ℂ) (hg : DifferentiableOn ℂ g U)
    (hgn : ∀ W : Set (V n), IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, g y ≠ 0)
    (hG : DifferentiableOn ℂ G {y | y ∈ U ∧ g y ≠ 0})
    (hL : ∀ p ∈ U, ∃ ρ > 0, ball p ρ ⊆ U ∧
      ∫⁻ y in ball p ρ \ {y | g y = 0}, ENNReal.ofReal (‖G y‖ ^ 2) < ⊤) :
    ∃ G' : V n → ℂ, DifferentiableOn ℂ G' U ∧ Set.EqOn G' G {y | y ∈ U ∧ g y ≠ 0} := by
  classical
  have hloc : ∀ p ∈ U, ∃ ρ > 0, ball p ρ ⊆ U ∧ ∃ F : V n → ℂ, DifferentiableOn ℂ F (ball p ρ) ∧
      Set.EqOn F G (ball p ρ \ {y | g y = 0}) := by
    intro p hp
    obtain ⟨ρ, hρ, hsub, hint⟩ := hL p hp
    obtain ⟨F, hF, hFeq⟩ := ReciprocityTheory.L2DbarEstimates.ext n p ρ g G (hg.mono hsub)
      (hG.mono fun y hy => ⟨hsub hy.1, hy.2⟩) hint
    exact ⟨ρ, hρ, hsub, F, hF, hFeq⟩
  choose ρ hρ hsub F hF hFeq using hloc
  have agree : ∀ y (hy : y ∈ U) z (hz : z ∈ U) x, x ∈ ball y (ρ y hy) → x ∈ ball z (ρ z hz) →
      F y hy x = F z hz x := by
    intro y hy z hz x hxy hxz
    by_contra hne
    have hcy : ContinuousAt (F y hy) x :=
      (hF y hy).continuousOn.continuousAt (isOpen_ball.mem_nhds hxy)
    have hcz : ContinuousAt (F z hz) x :=
      (hF z hz).continuousOn.continuousAt (isOpen_ball.mem_nhds hxz)
    have hev : ∀ᶠ t in 𝓝 x, F y hy t ≠ F z hz t := by
      first
        | exact hcy.eventually_ne hcz hne
        | exact ((hcy.sub hcz).eventually_ne (sub_ne_zero.mpr hne)).mono fun t ht h => ht (sub_eq_zero.mpr h)
    have hs : {t | t ∈ ball y (ρ y hy) ∧ t ∈ ball z (ρ z hz) ∧ F y hy t ≠ F z hz t} ∈ 𝓝 x :=
      Filter.inter_mem (isOpen_ball.mem_nhds hxy) (Filter.inter_mem (isOpen_ball.mem_nhds hxz) hev)
    obtain ⟨W, hWs, hWo, hxW⟩ := _root_.mem_nhds_iff.mp hs
    obtain ⟨t, htW, hgt⟩ := hgn W hWo (fun t ht => hsub y hy (hWs ht).1) ⟨x, hxW⟩
    have h1 := hFeq y hy ⟨(hWs htW).1, hgt⟩
    have h2 := hFeq z hz ⟨(hWs htW).2.1, hgt⟩
    exact (hWs htW).2.2 (h1.trans h2.symm)
  refine ⟨fun y => if hy : y ∈ U then F y hy y else 0, ?_, ?_⟩
  · intro y hy
    have hnb : ball y (ρ y hy) ∈ 𝓝 y := isOpen_ball.mem_nhds (mem_ball_self (hρ y hy))
    have heq : (fun y => if hy : y ∈ U then F y hy y else 0) =ᶠ[𝓝 y] F y hy := by
      filter_upwards [hnb] with x hx
      have hxU : x ∈ U := hsub y hy hx
      rw [dite_eq_left hxU]
      exact agree x hxU y hy x (mem_ball_self (hρ x hxU)) hx
    exact (((hF y hy).differentiableAt hnb).congr_of_eventuallyEq heq).differentiableWithinAt
  · intro y hy
    show (if h : y ∈ U then F y h y else 0) = G y
    rw [dite_eq_left hy.1]
    exact hFeq y hy.1 ⟨mem_ball_self (hρ y hy.1), hy.2⟩

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.HE
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderPfA
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.NOrd

theorem exists_val_of_prime {Kf : Type*} [Field Kf] (A : Subring Kf) (P : Ideal A) [P.IsPrime] :
    ∃ V : ValuationSubring Kf, (∀ a : A, (a : Kf) ∈ V) ∧ (∀ a : A, a ∉ P → (a : Kf)⁻¹ ∈ V) ∧
      ∀ a : A, a ∈ P → V.valuation (a : Kf) < 1 := by
  obtain ⟨B, hB⟩ := (LocalSubring.ofPrime A P).exists_le_valuationSubring
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.1 hB
  let e := LocalSubring.ofPrimeEquiv A P
  let f : Localization.AtPrime P →+* B.toLocalSubring.toSubring :=
    (Subring.inclusion hle).comp (e : Localization.AtPrime P →+* (LocalSubring.ofPrime A P).toSubring)
  have hf : ∀ a : A, ((f (algebraMap A (Localization.AtPrime P) a) : B.toLocalSubring.toSubring) : Kf) = a := by
    intro a
    show ((e (algebraMap A (Localization.AtPrime P) a) : (LocalSubring.ofPrime A P).toSubring) : Kf) = a
    rw [AlgEquiv.commutes]
    rfl
  have hmem : ∀ a : A, (a : Kf) ∈ B := by
    intro a
    have h := (f (algebraMap A (Localization.AtPrime P) a)).2
    rw [hf] at h
    exact h
  refine ⟨B, hmem, fun a ha => ?_, fun a ha => ?_⟩
  · have hu : IsUnit (algebraMap A (Localization.AtPrime P) a) :=
      IsLocalization.map_units _ (⟨a, ha⟩ : P.primeCompl)
    obtain ⟨u, hu'⟩ := hu.map f
    have h1 : ((u⁻¹ : (B.toLocalSubring.toSubring)ˣ) : B.toLocalSubring.toSubring) * (u : _) = 1 :=
      u.inv_mul
    have h2 : (((u⁻¹ : (B.toLocalSubring.toSubring)ˣ) : B.toLocalSubring.toSubring) : Kf) * (a : Kf) = 1 := by
      rw [← hf a, ← hu']
      exact congrArg Subtype.val h1
    rw [← eq_inv_of_mul_eq_one_left h2]
    exact ((u⁻¹ : (B.toLocalSubring.toSubring)ˣ) : B.toLocalSubring.toSubring).2
  · have hnu : ¬ IsUnit (algebraMap A (Localization.AtPrime P) a) := fun h =>
      (IsLocalization.AtPrime.isUnit_to_map_iff _ P a).1 h ha
    have hnu2 : ¬ IsUnit (f (algebraMap A (Localization.AtPrime P) a)) := by
      intro h
      apply hnu
      have h' : IsUnit (e (algebraMap A (Localization.AtPrime P) a)) := hloc.map_nonunit _ h
      have h'' := h'.map (e.symm : (LocalSubring.ofPrime A P).toSubring →+* Localization.AtPrime P)
      first
      | (convert h'' using 1
         exact (e.symm_apply_apply _).symm)
      | (rwa [show (e.symm : (LocalSubring.ofPrime A P).toSubring →+* Localization.AtPrime P)
            (e (algebraMap A (Localization.AtPrime P) a)) = algebraMap A (Localization.AtPrime P) a from
            e.symm_apply_apply _] at h'')
    by_contra hge
    push_neg at hge
    have hv1 : B.valuation (a : Kf) = 1 := le_antisymm ((B.valuation_le_one_iff _).2 (hmem a)) hge
    have hunit : IsUnit (⟨a, hmem a⟩ : B) := (B.valuation_eq_one_iff ⟨a, hmem a⟩).2 hv1
    apply hnu2
    have heq : f (algebraMap A (Localization.AtPrime P) a) = ⟨a, hmem a⟩ := Subtype.ext (hf a)
    rw [heq]
    exact hunit

end ReciprocityTheory.ChartRestriction.G.AR.Up.NOrd
end
