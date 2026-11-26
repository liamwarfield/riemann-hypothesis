module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.EnergyStep

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassReplaceKappa
section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassReplaceLevi
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open ReciprocityTheory.AnForm (levi levi_add_smul levi_re_analytic)

noncomputable section

variable {ι : Type} [Fintype ι]

theorem fderiv2_comp_real {ψ : (ι → ℂ) → ℝ} {G G₁ : ℝ → ℝ} {g₂ : ℝ} {y : ι → ℂ}
    (hψ : ContDiffAt ℝ 2 ψ y) (hG : ∀ᶠ z in 𝓝 y, HasDerivAt G (G₁ (ψ z)) (ψ z))
    (hG₁ : HasDerivAt G₁ g₂ (ψ y)) (v w : ι → ℂ) :
    fderiv ℝ (fderiv ℝ (fun z => G (ψ z))) y v w =
      G₁ (ψ y) * fderiv ℝ (fderiv ℝ ψ) y v w + g₂ * fderiv ℝ ψ y v * fderiv ℝ ψ y w := by
  have hev : fderiv ℝ (fun z => G (ψ z)) =ᶠ[𝓝 y] fun z => G₁ (ψ z) • fderiv ℝ ψ z := by
    filter_upwards [hG, hψ.eventually (by simp)] with z h1 h2
    exact (h1.comp_hasFDerivAt z (h2.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hD2 : HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) y) y :=
    ((hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hc : HasFDerivAt (fun z => G₁ (ψ z)) (g₂ • fderiv ℝ ψ y) y :=
    hG₁.comp_hasFDerivAt y (hψ.differentiableAt (by norm_num)).hasFDerivAt
  have h := ((hc.smul hD2).congr_of_eventuallyEq hev).fderiv
  rw [h]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]

theorem fderiv_comp_real {ψ : (ι → ℂ) → ℝ} {G : ℝ → ℝ} {g₁ : ℝ} {y : ι → ℂ}
    (hψ : DifferentiableAt ℝ ψ y) (hG : HasDerivAt G g₁ (ψ y)) (v : ι → ℂ) :
    fderiv ℝ (fun z => G (ψ z)) y v = g₁ * fderiv ℝ ψ y v := by
  have h := (hG.comp_hasFDerivAt y hψ.hasFDerivAt).fderiv
  rw [show (fun z => G (ψ z)) = G ∘ ψ from rfl, h]
  simp

theorem levi_comp_real {ψ : (ι → ℂ) → ℝ} {G G₁ : ℝ → ℝ} {g₂ : ℝ} {y : ι → ℂ}
    (hψ : ContDiffAt ℝ 2 ψ y) (hG : ∀ᶠ z in 𝓝 y, HasDerivAt G (G₁ (ψ z)) (ψ z))
    (hG₁ : HasDerivAt G₁ g₂ (ψ y)) (w : ι → ℂ) :
    levi (fun z => G (ψ z)) y w = G₁ (ψ y) * levi ψ y w +
      g₂ * ((fderiv ℝ ψ y w) ^ 2 + (fderiv ℝ ψ y (Complex.I • w)) ^ 2) / 4 := by
  unfold levi
  rw [fderiv2_comp_real hψ hG hG₁, fderiv2_comp_real hψ hG hG₁]
  ring

theorem fderiv_re_analytic {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) (v : ι → ℂ) :
    fderiv ℝ (fun z => (S z).re) y v = (fderiv ℂ S y v).re := by
  have hS' : HasFDerivAt S ((fderiv ℂ S y).restrictScalars ℝ) y :=
    hS.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have h := (Complex.reCLM.hasFDerivAt.comp y hS').fderiv
  rw [show (fun z => (S z).re) = Complex.reCLM ∘ S from rfl, h]
  simp

theorem im_eq_re_mul (c : ℂ) : c.im = (-Complex.I * c).re := by
  simp [Complex.mul_re]

theorem fderiv_im_analytic {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) (v : ι → ℂ) :
    fderiv ℝ (fun z => (S z).im) y v = (fderiv ℂ S y v).im := by
  have hS2 : AnalyticAt ℂ (fun z => -Complex.I * S z) y := analyticAt_const.mul hS
  have h1 : (fun z => (S z).im) = fun z => (-Complex.I * S z).re := funext fun z => im_eq_re_mul _
  rw [h1, fderiv_re_analytic hS2, fderiv_const_mul hS.differentiableAt]
  simp [Complex.mul_re]

theorem levi_im_analytic {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) (w : ι → ℂ) :
    levi (fun z => (S z).im) y w = 0 := by
  have hS2 : AnalyticAt ℂ (fun z => -Complex.I * S z) y := analyticAt_const.mul hS
  have h1 : (fun z => (S z).im) = fun z => (-Complex.I * S z).re := funext fun z => im_eq_re_mul _
  rw [h1]
  exact levi_re_analytic hS2 w

theorem contDiffAt_re_analytic {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) :
    ContDiffAt ℝ 2 (fun z => (S z).re) y :=
  (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp y (hS.restrictScalars (𝕜 := ℝ)).contDiffAt

theorem contDiffAt_im_analytic {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) :
    ContDiffAt ℝ 2 (fun z => (S z).im) y :=
  (Complex.imCLM.contDiff (n := 2)).contDiffAt.comp y (hS.restrictScalars (𝕜 := ℝ)).contDiffAt

theorem sq_norm_eq_re_im (c : ℂ) : ‖c‖ ^ 2 = c.re ^ 2 + 1 * c.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem hasDerivAt_sq' (x : ℝ) : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
  simpa using hasDerivAt_pow 2 x

theorem levi_normSq_analytic {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) (w : ι → ℂ) :
    levi (fun z => ‖S z‖ ^ 2) y w = ‖fderiv ℂ S y w‖ ^ 2 := by
  have hre := contDiffAt_re_analytic hS
  have him := contDiffAt_im_analytic hS
  have e : (fun z => ‖S z‖ ^ 2) = fun z => (S z).re ^ 2 + 1 * (S z).im ^ 2 :=
    funext fun z => sq_norm_eq_re_im _
  have hG : ∀ (ψ : (ι → ℂ) → ℝ), ∀ᶠ z in 𝓝 y, HasDerivAt (fun x : ℝ => x ^ 2) (2 * ψ z) (ψ z) :=
    fun ψ => Eventually.of_forall fun z => hasDerivAt_sq' _
  have hG₁ : ∀ x : ℝ, HasDerivAt (fun x : ℝ => 2 * x) 2 x := fun x => by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have l1 := levi_comp_real (G₁ := fun x => 2 * x) hre (hG _) (hG₁ _) w
  have l2 := levi_comp_real (G₁ := fun x => 2 * x) him (hG _) (hG₁ _) w
  have hsq : ∀ (ψ : (ι → ℂ) → ℝ), ContDiffAt ℝ 2 ψ y → ContDiffAt ℝ 2 (fun z => ψ z ^ 2) y :=
    fun ψ h => h.pow 2
  rw [e, levi_add_smul 1 (hsq _ hre) (hsq _ him), l1, l2, levi_re_analytic hS,
    levi_im_analytic hS, fderiv_re_analytic hS, fderiv_re_analytic hS, fderiv_im_analytic hS,
    fderiv_im_analytic hS, map_smul, sq_norm_eq_re_im]
  simp only [smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

theorem fderiv_normSq_analytic {S : (ι → ℂ) → ℂ} {y : ι → ℂ} (hS : AnalyticAt ℂ S y) (v : ι → ℂ) :
    fderiv ℝ (fun z => ‖S z‖ ^ 2) y v =
      2 * ((S y).re * (fderiv ℂ S y v).re + (S y).im * (fderiv ℂ S y v).im) := by
  have hre := contDiffAt_re_analytic hS
  have him := contDiffAt_im_analytic hS
  have e : (fun z => ‖S z‖ ^ 2) = fun z => (S z).re ^ 2 + (S z).im ^ 2 :=
    funext fun z => by rw [sq_norm_eq_re_im, one_mul]
  have d1 : DifferentiableAt ℝ (fun z => (S z).re ^ 2) y :=
    (hre.differentiableAt (by norm_num)).pow 2
  have d2 : DifferentiableAt ℝ (fun z => (S z).im ^ 2) y :=
    (him.differentiableAt (by norm_num)).pow 2
  rw [e, fderiv_fun_add d1 d2, ContinuousLinearMap.add_apply,
    fderiv_comp_real (G := fun x : ℝ => x ^ 2) (hre.differentiableAt (by norm_num))
      (hasDerivAt_sq' _),
    fderiv_comp_real (G := fun x : ℝ => x ^ 2) (him.differentiableAt (by norm_num))
      (hasDerivAt_sq' _), fderiv_re_analytic hS, fderiv_im_analytic hS]
  ring

theorem levi_log_normSq_add_exp {S : (ι → ℂ) → ℂ} {Φ : (ι → ℂ) → ℝ} {y : ι → ℂ} {ε : ℝ}
    (hS : AnalyticAt ℂ S y) (hΦ : ContDiffAt ℝ 2 Φ y) (hε : 0 < ε) (w : ι → ℂ) :
    2 * (ε * Real.exp (2 * Φ y)) / (‖S y‖ ^ 2 + ε * Real.exp (2 * Φ y)) * levi Φ y w ≤
      levi (fun z => Real.log (‖S z‖ ^ 2 + ε * Real.exp (2 * Φ z))) y w := by
  set h : (ι → ℂ) → ℝ := fun z => ‖S z‖ ^ 2 + ε * Real.exp (2 * Φ z) with hh
  have hpos : ∀ z, 0 < h z := fun z => by
    have := Real.exp_pos (2 * Φ z)
    positivity
  have hSc : ContDiffAt ℝ 2 S y := (hS.restrictScalars (𝕜 := ℝ)).contDiffAt
  have hQ : ContDiffAt ℝ 2 (fun z => ‖S z‖ ^ 2) y := (contDiff_norm_sq ℝ).contDiffAt.comp y hSc
  have h2Φ : ContDiffAt ℝ 2 (fun z => 2 * Φ z) y := contDiffAt_const.mul hΦ
  have hE : ContDiffAt ℝ 2 (fun z => Real.exp (2 * Φ z)) y := h2Φ.exp
  have hhc : ContDiffAt ℝ 2 h y := hQ.add (contDiffAt_const.mul hE)
  have l2Φ := levi_comp_real (G := fun x : ℝ => 2 * x) (G₁ := fun _ => 2) (g₂ := 0) hΦ
    (Eventually.of_forall fun z => by simpa using (hasDerivAt_id (Φ z)).const_mul (2 : ℝ))
    (hasDerivAt_const _ _) w
  have lE := levi_comp_real (G := Real.exp) (G₁ := Real.exp) (g₂ := Real.exp (2 * Φ y)) h2Φ
    (Eventually.of_forall fun z => Real.hasDerivAt_exp _) (Real.hasDerivAt_exp _) w
  have d2Φ : ∀ v, fderiv ℝ (fun z => 2 * Φ z) y v = 2 * fderiv ℝ Φ y v := fun v =>
    fderiv_comp_real (G := fun x : ℝ => 2 * x) (hΦ.differentiableAt (by norm_num))
      (by simpa using (hasDerivAt_id (Φ y)).const_mul (2 : ℝ)) v
  have dE : ∀ v, fderiv ℝ (fun z => Real.exp (2 * Φ z)) y v =
      Real.exp (2 * Φ y) * (2 * fderiv ℝ Φ y v) := fun v => by
    rw [fderiv_comp_real (G := Real.exp) (h2Φ.differentiableAt (by norm_num))
      (Real.hasDerivAt_exp _), d2Φ]
  have dh : ∀ v, fderiv ℝ h y v = 2 * ((S y).re * (fderiv ℂ S y v).re +
      (S y).im * (fderiv ℂ S y v).im) + ε * (Real.exp (2 * Φ y) * (2 * fderiv ℝ Φ y v)) := by
    intro v
    have d1 : DifferentiableAt ℝ (fun z => ‖S z‖ ^ 2) y := hQ.differentiableAt (by norm_num)
    have d2 : DifferentiableAt ℝ (fun z => ε * Real.exp (2 * Φ z)) y :=
      (contDiffAt_const.mul hE).differentiableAt (by norm_num)
    rw [hh, fderiv_fun_add d1 d2, ContinuousLinearMap.add_apply, fderiv_normSq_analytic hS,
      fderiv_const_mul (hE.differentiableAt (by norm_num)), ContinuousLinearMap.smul_apply,
      dE, smul_eq_mul]
  have lh : levi h y w = ‖fderiv ℂ S y w‖ ^ 2 + ε * (Real.exp (2 * Φ y) * (2 * levi Φ y w) +
      Real.exp (2 * Φ y) * ((2 * fderiv ℝ Φ y w) ^ 2 +
        (2 * fderiv ℝ Φ y (Complex.I • w)) ^ 2) / 4) := by
    rw [hh, levi_add_smul ε hQ hE, levi_normSq_analytic hS, lE, l2Φ, d2Φ, d2Φ]
    ring
  have lK := levi_comp_real (G := Real.log) (G₁ := fun x => x⁻¹) (g₂ := -(h y ^ 2)⁻¹) hhc
    (Eventually.of_forall fun z => Real.hasDerivAt_log (hpos z).ne')
    (hasDerivAt_inv (hpos y).ne') w
  change _ ≤ levi (fun z => Real.log (h z)) y w
  rw [lK, lh, dh, dh, (fderiv ℂ S y).map_smul Complex.I w, sq_norm_eq_re_im (fderiv ℂ S y w)]
  simp only [smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  set E := ε * Real.exp (2 * Φ y) with hEdef
  have hEpos : 0 < E := mul_pos hε (Real.exp_pos _)
  have hy : h y = ‖S y‖ ^ 2 + E := rfl
  rw [sq_norm_eq_re_im (S y)] at hy
  set σr := (S y).re
  set σi := (S y).im
  set ar := (fderiv ℂ S y w).re
  set ai := (fderiv ℂ S y w).im
  set b₁ := fderiv ℝ Φ y w
  set b₂ := fderiv ℝ Φ y (Complex.I • w)
  set L := levi Φ y w
  have hhy : 0 < h y := hpos y
  rw [show ‖S y‖ ^ 2 + E = h y from rfl]
  have key : (h y)⁻¹ * (ar ^ 2 + 1 * ai ^ 2 + ε * (Real.exp (2 * Φ y) * (2 * L) +
      Real.exp (2 * Φ y) * ((2 * b₁) ^ 2 + (2 * b₂) ^ 2) / 4)) +
      -(h y ^ 2)⁻¹ * ((2 * (σr * ar + σi * ai) + ε * (Real.exp (2 * Φ y) * (2 * b₁))) ^ 2 +
        (2 * (σr * (0 * ar - 1 * ai) + σi * (0 * ai + 1 * ar)) +
          ε * (Real.exp (2 * Φ y) * (2 * b₂))) ^ 2) / 4 - 2 * E / h y * L =
      E * ((ar - (σr * b₁ + σi * b₂)) ^ 2 + (ai - (σi * b₁ - σr * b₂)) ^ 2) / h y ^ 2 := by
    rw [hy]
    field_simp
    rw [hEdef]
    ring
  have hnn : 0 ≤ E * ((ar - (σr * b₁ + σi * b₂)) ^ 2 + (ai - (σi * b₁ - σr * b₂)) ^ 2) / h y ^ 2 :=
    by positivity
  linarith

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology MeasureTheory
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_congr levi_add_smul)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsSNC logNormSec)

noncomputable section

namespace GreenMassReplace

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem secNorm_eq_local {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ}
    (hS : IsSection A L s) {x y : X} (hy : y ∈ L.U x) :
    secNorm L s y = ‖s x y‖ * Real.exp (-L.φ x y) :=
  hS.2 y x y ⟨L.mem_U y, hy⟩

def logNormSqAdd (L : LocPot X) (s : X → X → ℂ) (ε : ℝ) (y : X) : ℝ :=
  Real.log (secNorm L s y ^ 2 + ε)

theorem logNormSqAdd_eq_local {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ}
    (hS : IsSection A L s) {x y : X} (hy : y ∈ L.U x) {ε : ℝ} (hε : 0 < ε) :
    logNormSqAdd L s ε y =
      Real.log (‖s x y‖ ^ 2 + ε * Real.exp (2 * L.φ x y)) - 2 * L.φ x y := by
  unfold logNormSqAdd
  rw [secNorm_eq_local hS hy]
  have hP : 0 < ‖s x y‖ ^ 2 + ε * Real.exp (2 * L.φ x y) := by positivity
  have h1 : Real.exp (-L.φ x y) ^ 2 = Real.exp (-(2 * L.φ x y)) := by
    rw [sq, ← Real.exp_add]
    ring_nf
  have h2 : Real.exp (2 * L.φ x y) * Real.exp (-(2 * L.φ x y)) = 1 := by
    rw [← Real.exp_add]
    simp
  have h3 : (‖s x y‖ * Real.exp (-L.φ x y)) ^ 2 + ε =
      (‖s x y‖ ^ 2 + ε * Real.exp (2 * L.φ x y)) * Real.exp (-(2 * L.φ x y)) := by
    rw [mul_pow, h1, add_mul, mul_assoc ε, h2, mul_one]
  rw [h3, Real.log_mul hP.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

theorem kappaEp_φ_eq_local {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ}
    (hS : IsSection A L s) {x y : X} (hy : y ∈ L.U x) {ε : ℝ} (hε : 0 < ε) :
    (kappaEp L s ε).φ x y = Real.log (‖s x y‖ ^ 2 + ε * Real.exp (2 * L.φ x y)) := by
  have h := logNormSqAdd_eq_local hS hy hε
  unfold logNormSqAdd at h
  show 2 * L.φ x y + Real.log (secNorm L s y ^ 2 + ε) = _
  rw [h]
  ring

theorem smooth_logNormSqAdd {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ}
    (hL : IsPotential A L) (hS : IsSection A L s) {ε : ℝ} (hε : 0 < ε) :
    A.Smooth (logNormSqAdd L s ε) := by
  intro j y hy
  refine ContDiffAt.contDiffWithinAt ?_
  have hyt : y ∈ (A.chart j).target := hy.1
  set q := (A.chart j).symm y with hq
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U q) :=
    (A.chart j).isOpen_inter_preimage_symm (L.isOpen_U q)
  have hyO : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U q := ⟨hyt, L.mem_U q⟩
  have heq : (logNormSqAdd L s ε ∘ (A.chart j).symm) =ᶠ[𝓝 y] fun z =>
      Real.log (‖(s q ∘ (A.chart j).symm) z‖ ^ 2 +
        ε * Real.exp (2 * (L.φ q ∘ (A.chart j).symm) z)) - 2 * (L.φ q ∘ (A.chart j).symm) z := by
    filter_upwards [hO.mem_nhds hyO] with z hz
    exact logNormSqAdd_eq_local hS hz.2 hε
  refine ContDiffAt.congr_of_eventuallyEq ?_ heq
  have hSc : ContDiffAt ℝ ∞ (s q ∘ (A.chart j).symm) y :=
    ((hS.1 q j y hyO).restrictScalars (𝕜 := ℝ)).contDiffAt
  have hΦ : ContDiffAt ℝ ∞ (L.φ q ∘ (A.chart j).symm) y :=
    ReciprocityTheory.AnForm.M.contDiffAt_of_isPotential A L hL q j hyO
  refine ((((contDiff_norm_sq ℝ).contDiffAt.comp y hSc).add
    (contDiffAt_const.mul (contDiffAt_const.mul hΦ).exp)).log ?_).sub (contDiffAt_const.mul hΦ)
  exact (by positivity : (0 : ℝ) < ‖(s q ∘ (A.chart j).symm) y‖ ^ 2 +
    ε * Real.exp (2 * (L.φ q ∘ (A.chart j).symm) y)).ne'

theorem isPotential_kappaEp {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ}
    (hL : IsPotential A L) (hS : IsSection A L s) {ε : ℝ} (hε : 0 < ε) :
    IsPotential A (kappaEp L s ε) :=
  ReciprocityTheory.AnForm.M.isPotentialAdd A _ _ (ReciprocityTheory.AnForm.M.isPotentialRsmul A 2 L hL)
    (ReciprocityTheory.AnForm.M.isPotential_ofFun A _ (smooth_logNormSqAdd hL hS hε))

theorem kappaEp_formNonneg [CompactSpace X] {A : FinHolAtlas e X} (Om : KaehlerForm A)
    {L : LocPot X} {s : X → X → ℂ} (hL : IsPotential A L) (hS : IsSection A L s) :
    ∃ Cκ : ℝ, 0 ≤ Cκ ∧ ∀ ε, 0 < ε → FormNonneg A Set.univ (kappaEp L s ε + Om.pot.rsmul Cκ) := by
  obtain ⟨M, hM0, hM⟩ := levi_abs_le_global A isCompact_univ L Om.pot hL Om.isPot Om.pos
  refine ⟨2 * M, by positivity, fun ε hε x k y hy w => ?_⟩
  have hyt : y ∈ (A.chart k).target := hy.1
  have hyL : (A.chart k).symm y ∈ L.U x := hy.2.2.1.1
  have hyΩ : (A.chart k).symm y ∈ Om.pot.U x := hy.2.2.2
  set S := s x ∘ (A.chart k).symm with hSdef
  set Φ := L.φ x ∘ (A.chart k).symm with hΦdef
  set Ψ := Om.pot.φ x ∘ (A.chart k).symm with hΨdef
  have hO : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' L.U x) :=
    (A.chart k).isOpen_inter_preimage_symm (L.isOpen_U x)
  have hSa : AnalyticAt ℂ S y := hS.1 x k y ⟨hyt, hyL⟩
  have hΦ2 : ContDiffAt ℝ 2 Φ y := ReciprocityTheory.AnForm.M.pot_contDiffAt_two hL x k hyt hyL
  have hΨ2 : ContDiffAt ℝ 2 Ψ y := ReciprocityTheory.AnForm.M.pot_contDiffAt_two Om.isPot x k hyt hyΩ
  have heq : (kappaEp L s ε).φ x ∘ (A.chart k).symm =ᶠ[𝓝 y]
      fun z => Real.log (‖S z‖ ^ 2 + ε * Real.exp (2 * Φ z)) := by
    filter_upwards [hO.mem_nhds ⟨hyt, hyL⟩] with z hz
    exact kappaEp_φ_eq_local hS hz.2 hε
  have hK2 : ContDiffAt ℝ 2 (fun z => Real.log (‖S z‖ ^ 2 + ε * Real.exp (2 * Φ z))) y := by
    have hSc : ContDiffAt ℝ 2 S y := (hSa.restrictScalars (𝕜 := ℝ)).contDiffAt
    refine (((contDiff_norm_sq ℝ).contDiffAt.comp y hSc).add
      (contDiffAt_const.mul (contDiffAt_const.mul hΦ2).exp)).log ?_
    exact (by positivity : (0 : ℝ) < ‖S y‖ ^ 2 + ε * Real.exp (2 * Φ y)).ne'
  have hκ2 := hK2.congr_of_eventuallyEq heq
  have hsum : (kappaEp L s ε + Om.pot.rsmul (2 * M)).φ x ∘ (A.chart k).symm =
      fun z => ((kappaEp L s ε).φ x ∘ (A.chart k).symm) z + (2 * M) * Ψ z := rfl
  rw [hsum, levi_add_smul (2 * M) hκ2 hΨ2 w, levi_congr heq w]
  have hA := levi_log_normSq_add_exp hSa hΦ2 hε w
  have hB := hM x k y ⟨hyt, hyL, hyΩ⟩ w
  have hΨnn : 0 ≤ levi Ψ y w := by
    rcases eq_or_ne w 0 with h0 | h0
    · rw [h0, ReciprocityTheory.AnForm.levi_zero]
    · exact (Om.pos x k y ⟨hyt, hyΩ⟩ w h0).le
  set E := ε * Real.exp (2 * Φ y) with hE
  have hE0 : 0 < E := mul_pos hε (Real.exp_pos _)
  have hh : 0 < ‖S y‖ ^ 2 + E := by positivity
  set c := 2 * E / (‖S y‖ ^ 2 + E) with hc
  have hc0 : 0 ≤ c := by positivity
  have hc2 : c ≤ 2 := by
    rw [hc, div_le_iff₀ hh]
    nlinarith [sq_nonneg ‖S y‖]
  have hl := (abs_le.mp hB).1
  have hMΨ : 0 ≤ M * levi Ψ y w := mul_nonneg hM0 hΨnn
  nlinarith

def zeroSet (s : X → X → ℂ) : Set X := {y | s y y = 0}

theorem zero_iff_local {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ}
    (hS : IsSection A L s) {x y : X} (hy : y ∈ L.U x) : s y y = 0 ↔ s x y = 0 := by
  have h := hS.2 y x y ⟨L.mem_U y, hy⟩
  constructor
  · intro h0
    rw [h0, norm_zero, zero_mul] at h
    exact norm_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_right (Real.exp_pos _).ne')
  · intro h0
    rw [h0, norm_zero, zero_mul] at h
    exact norm_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (Real.exp_pos _).ne')

theorem zeroSet_analytic {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ}
    (hS : IsSection A L s) : A.IsAnalyticSubset (zeroSet s) := by
  intro x
  refine ⟨L.U x, L.isOpen_U x, L.mem_U x, 1, fun _ => s x, fun _ => hS.1 x, ?_⟩
  ext y
  simp only [zeroSet, Set.mem_inter_iff, Set.mem_ofPred_eq, forall_const]
  constructor
  · rintro ⟨h0, hy⟩
    exact ⟨hy, (zero_iff_local hS hy).1 h0⟩
  · rintro ⟨hy, h0⟩
    exact ⟨(zero_iff_local hS hy).2 h0, hy⟩

theorem interior_zeroSet {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ}
    (hS : IsSection A L s) {r : ℕ} {m : Fin r → ℕ} {W : Fin r → Set X}
    (hsnc : IsSNC A L s m W) : interior (zeroSet s) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨ψ, -, hxψ, hψL, σ, -, -, u, -, hu0, hprod⟩ := hsnc x
  have hOimg : IsOpen (ψ '' (ψ.source ∩ interior (zeroSet s))) :=
    ψ.isOpen_image_source_inter isOpen_interior
  have hne : (ψ '' (ψ.source ∩ interior (zeroSet s))).Nonempty := ⟨ψ x, x, ⟨hxψ, hx⟩, rfl⟩
  have hsub : ψ '' (ψ.source ∩ interior (zeroSet s)) ⊆ ⋃ i, {z : Fin e → ℂ | z i = 0} := by
    rintro _ ⟨y, ⟨hyψ, hyZ⟩, rfl⟩
    have hz : y ∈ zeroSet s := interior_subset hyZ
    have h0 : s x y = 0 := (zero_iff_local hS (hψL hyψ)).1 hz
    rw [hprod y hyψ] at h0
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h (hu0 y hyψ)
    · obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 h
      revert hk
      cases hσ : σ k with
      | none => intro hk; exact absurd hk one_ne_zero
      | some i => intro hk; exact Set.mem_iUnion.2 ⟨i, eq_zero_of_pow_eq_zero hk⟩
  have hpos := hOimg.measure_pos volume hne
  have hnull : volume (⋃ i, {z : Fin e → ℂ | z i = 0}) = 0 :=
    measure_iUnion_null fun i => ReciprocityTheory.AnForm.M.PLAux.volume_coord_eq_zero i
  exact hpos.ne' (measure_mono_null hsub hnull)

theorem greenEp_eq_off (L : LocPot X) (s : X → X → ℂ) {ε : ℝ} (hε : 0 < ε) {y : X}
    (hy : y ∉ zeroSet s) :
    greenEp L s ε y = -2 * logNormSec L s y + logNormSqAdd L s ε y := by
  have hn : 0 < secNorm L s y := mul_pos (norm_pos_iff.2 hy) (Real.exp_pos _)
  have h1 : 1 + ε / secNorm L s y ^ 2 = (secNorm L s y ^ 2 + ε) / secNorm L s y ^ 2 := by
    field_simp
  unfold greenEp logNormSqAdd
  rw [h1, Real.log_div (by positivity) (by positivity), Real.log_pow]
  show _ = -2 * Real.log (secNorm L s y) + _
  push_cast
  ring

theorem greenEp_nonneg (L : LocPot X) (s : X → X → ℂ) {ε : ℝ} (hε : 0 < ε) (y : X) :
    0 ≤ greenEp L s ε y :=
  Real.log_nonneg (le_add_of_nonneg_right (div_nonneg hε.le (sq_nonneg _)))

end GreenMassReplace

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology MeasureTheory
open ReciprocityTheory.AnForm (levi levi_add_smul)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt MIntegrable logNormSec)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

namespace GreenMassReplace

theorem ell_anti {t t₀ : ℝ} (ht : 0 < t) (htt : t ≤ t₀) : ell t₀ ≤ ell t :=
  Real.log_le_log (inv_pos.2 (ht.trans_le htt)) (inv_anti₀ ht htt)

theorem formNonneg_mono {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {V : Set X} {P : LocPot X} (h : FormNonneg A Set.univ P) : FormNonneg A V P :=
  fun x k y hy w => h x k y ⟨hy.1, trivial, hy.2.2⟩ w

theorem formNonneg_kaehler {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    (Om : KaehlerForm A) (V : Set X) : FormNonneg A V Om.pot :=
  fun x k y hy w => KaehlerForm.isPsh Om x k y ⟨hy.1, hy.2.2⟩ w

theorem mInt_nonneg_of_compl {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (V : Set X) (hAn : A.IsAnalyticSubset Vᶜ) (hint : interior Vᶜ = ∅) (Φ : Fin e → LocPot X)
    (hpot : ∀ i, IsPotential A (Φ i)) (hnn : ∀ i, FormNonneg A V (Φ i)) (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ mInt A Φ f := by
  have mIntCongrNull : ∀ (Φ : Fin e → LocPot X) (S : Set X), A.IsAnalyticSubset S →
      interior S = ∅ → ∀ g g' : X → ℝ, (∀ x ∉ S, g x = g' x) →
      mInt A Φ g = mInt A Φ g' := by
    intro Φ S hS hS' g g' hg
    unfold mInt
    split_ifs with h
    · exact ReciprocityTheory.AnForm.M.integralWith_congr_null A h.some Φ hS hS' hg
    · rfl
  rw [mIntCongrNull Φ Vᶜ hAn hint f (V.indicator f) (fun x hx => by
    rw [Set.indicator_of_mem (Set.not_notMem.mp hx)])]
  refine SystemIndependence.mInt_nonneg_on A V Φ hpot hnn _ (fun x => ?_)
    (fun x hx => Set.indicator_of_notMem hx _)
  by_cases hx : x ∈ V
  · rw [Set.indicator_of_mem hx]
    exact hf x
  · rw [Set.indicator_of_notMem hx]

theorem levi_smul' {ι : Type} [Fintype ι] {f : (ι → ℂ) → ℝ} {y : ι → ℂ} (c : ℝ)
    (hf : ContDiffAt ℝ 2 f y) (w : ι → ℂ) : levi (fun z => c * f z) y w = c * levi f y w := by
  have h := levi_add_smul c (contDiffAt_const (c := (0 : ℝ))) hf w
  simp only [zero_add] at h
  rw [h, levi_const, zero_add]

theorem mixedForms_eq_cons {W : Type} [TopologicalSpace W] {D : ℕ} (Om : LocPot W)
    (T : Fin (D + 1) → LocPot W) (a : ℕ) (ha : a < D + 1) :
    mixedForms Om T a = Fin.cons Om (restForms Om T a) ∘ Fin.cycleRange (⟨a, ha⟩ : Fin (D + 1)) := by
  funext i
  simp only [Function.comp_apply, mixedForms]
  rcases lt_trichotomy i ⟨a, ha⟩ with h | h | h
  · have hi : (i : ℕ) < a := h
    have hD : (i : ℕ) < D := by omega
    have hc : Fin.cycleRange (⟨a, ha⟩ : Fin (D + 1)) i = Fin.succ ⟨i, hD⟩ :=
      Fin.ext (by simp [Fin.coe_cycleRange_of_lt h])
    rw [hc, Fin.cons_succ, if_pos hi]
    simp only [restForms, if_pos hi]
    rfl
  · rw [h, Fin.cycleRange_self, Fin.cons_zero, if_neg (lt_irrefl a)]
  · have hi : a < (i : ℕ) := h
    have hne : i ≠ 0 := fun h0 => by rw [h0] at hi; exact Nat.not_lt_zero _ hi
    rw [Fin.cycleRange_of_gt h, if_neg (by omega)]
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hne
    rw [Fin.cons_succ]
    simp only [restForms]
    rw [if_neg]
    simp only [Fin.val_succ] at hi
    omega

variable {D : ℕ} {W : Type} [TopologicalSpace W]

theorem divInt_linear [CompactSpace W] [T2Space W] (S : UIData D W) (Φ : Fin D → LocPot W)
    (hΦ : ∀ i, IsPotential S.A (Φ i)) (c : ℝ) {f g : W → ℝ} (hf : Continuous f)
    (hg : Continuous g) :
    S.divInt Φ (fun x => c * f x + g x) = c * S.divInt Φ f + S.divInt Φ g := by
  unfold UIData.divInt
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : CompactSpace (S.comp k) := isCompact_iff_compactSpace.mp
    (ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.isClosed_divisorComponent S.A S.L S.s S.mult S.comp S.s_snc k).isCompact
  have hpot : ∀ i, IsPotential (S.B k) (restrictForms (S.comp k) Φ i) := fun i =>
    ReciprocityTheory.AnForm.M.isPotentialPullback S.A (S.B k) Subtype.val (S.B_holo k) (Φ i) (hΦ i)
  have h := ReciprocityTheory.AnForm.M.mIntLinear (S.B k) (restrictForms (S.comp k) Φ) hpot c
    (f ∘ Subtype.val) (g ∘ Subtype.val)
    (ReciprocityTheory.AnForm.M.mIntegrableCont _ _ hpot _ (hf.comp continuous_subtype_val))
    (ReciprocityTheory.AnForm.M.mIntegrableCont _ _ hpot _ (hg.comp continuous_subtype_val))
  have e : ((fun x => c * f x + g x) ∘ Subtype.val : S.comp k → ℝ) =
      fun x => c * (f ∘ Subtype.val) x + (g ∘ Subtype.val) x := rfl
  rw [e, h]
  ring

end GreenMassReplace

open GreenMassReplace in
theorem GreenMassReplace.proof : GreenMassReplace.Statement := by
  intro D W _ _ _ S
  obtain ⟨Cκ, hCκ0, hκ⟩ := kappaEp_formNonneg S.Om S.L_pot S.s_sec
  refine ⟨Cκ, hCκ0, fun a ha t₀ ht₀ hℓ₀ => ?_⟩
  have hform₀ := S.form ⟨a, ha⟩ t₀ ht₀ hℓ₀
  set ut : W → ℝ := fun x => S.u ⟨a, ha⟩ t₀ x + S.C * errE S.C t₀ with hutdef
  have hut : S.A.Smooth ut := fun j => (hform₀.2 j).add contDiffOn_const
  have hutpot : IsPotential S.A (LocPot.ofFun ut) := ReciprocityTheory.AnForm.M.isPotential_ofFun _ _ hut
  obtain ⟨K, hK0, hK⟩ := levi_abs_le_global S.A isCompact_univ (LocPot.ofFun ut) S.Om.pot hutpot
    S.Om.isPot S.Om.pos
  refine ⟨K, hK0, fun ε t hε _ ht htt => ?_⟩
  have hℓ : S.ell₀ ≤ ell t := hℓ₀.trans (ell_anti ht htt)

  have hTpot : ∀ j, IsPotential S.A (S.T t j) := fun j =>
    ReciprocityTheory.AnForm.M.isPotentialAdd S.A _ _ (S.form j t ht hℓ).1.th_pot
      (ReciprocityTheory.AnForm.M.isPotential_ofFun _ _ (S.form j t ht hℓ).2)
  have hTnn : ∀ j, FormNonneg S.A S.Yo (S.T t j) := fun j => (S.form j t ht hℓ).1.nonneg
  set Φ' := S.rest a t with hΦ'
  have hΦpot : ∀ i, IsPotential S.A (Φ' i) := by
    intro i
    simp only [hΦ', UIData.rest, restForms]
    split_ifs
    · exact hTpot _
    · exact S.Om.isPot
  have hΦnn : ∀ i, FormNonneg S.A S.Yo (Φ' i) := by
    intro i
    simp only [hΦ', UIData.rest, restForms]
    split_ifs
    · exact hTnn _
    · exact formNonneg_kaehler S.Om S.Yo
  have hcons : ∀ P, IsPotential S.A P →
      ∀ i, IsPotential S.A ((Fin.cons P Φ' : Fin (D + 1) → LocPot W) i) := by
    intro P hP i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hP
    · simpa using hΦpot j
  have hconsnn : ∀ P, FormNonneg S.A S.Yo P →
      ∀ i, FormNonneg S.A S.Yo ((Fin.cons P Φ' : Fin (D + 1) → LocPot W) i) := by
    intro P hP i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hP
    · simpa using hΦnn j
  have hκpot := isPotential_kappaEp S.L_pot S.s_sec hε
  have hOmK : ∀ c : ℝ, IsPotential S.A (S.Om.pot.rsmul c) := fun c =>
    ReciprocityTheory.AnForm.M.isPotentialRsmul S.A c _ S.Om.isPot

  set u := S.u ⟨a, ha⟩ t with hudef
  have hu : S.A.Smooth u := (S.form ⟨a, ha⟩ t ht hℓ).2
  have hut_c : Continuous ut := ReciprocityTheory.AnForm.M.PLAux.smooth_continuous hut
  have hu_c : Continuous u := ReciprocityTheory.AnForm.M.PLAux.smooth_continuous hu
  set g := S.gap a ha t₀ t with hgdef
  have hg_eq : g = fun x => ut x - u x := rfl
  have hg_c : Continuous g := by rw [hg_eq]; exact hut_c.sub hu_c
  have hgnn : ∀ x, 0 ≤ g x := fun x => by
    have := S.mono ⟨a, ha⟩ t t₀ ht htt hℓ₀ x
    rw [hg_eq]
    simp only [hutdef, hudef]
    linarith
  have hu_eq : (fun x => -1 * g x + ut x) = u := by
    funext x
    rw [hg_eq]
    ring
  set F := logNormSqAdd S.L S.s ε with hFdef
  have hF : S.A.Smooth F := smooth_logNormSqAdd S.L_pot S.s_sec hε
  have hF_c : Continuous F := ReciprocityTheory.AnForm.M.PLAux.smooth_continuous hF
  have hint : ∀ P, IsPotential S.A P → ∀ f : W → ℝ, Continuous f →
      MIntegrable S.A (Fin.cons P Φ') f := fun P hP f hf =>
    ReciprocityTheory.AnForm.M.mIntegrableCont S.A _ (hcons P hP) f hf

  have sA : mInt S.A (Fin.cons (kappaEp S.L S.s ε) Φ') u =
      mInt S.A (Fin.cons (kappaEp S.L S.s ε) Φ') ut -
        mInt S.A (Fin.cons (kappaEp S.L S.s ε) Φ') g := by
    have h := ReciprocityTheory.AnForm.M.mIntLinear S.A _ (hcons _ hκpot) (-1) g ut
      (hint _ hκpot g hg_c) (hint _ hκpot ut hut_c)
    rw [hu_eq] at h
    linarith

  have sB : 0 ≤ mInt S.A (Fin.cons (kappaEp S.L S.s ε) Φ') g +
      Cκ * mInt S.A (Fin.cons S.Om.pot Φ') g := by
    have hPpot : IsPotential S.A (kappaEp S.L S.s ε + S.Om.pot.rsmul Cκ) :=
      ReciprocityTheory.AnForm.M.isPotentialAdd S.A _ _ hκpot (hOmK Cκ)
    have h0 := mInt_nonneg_of_compl S.A S.Yo S.bd_analytic S.bd_interior _ (hcons _ hPpot)
      (hconsnn _ (formNonneg_mono (hκ ε hε))) g hgnn
    rw [ReciprocityTheory.AnForm.M.mIntAdd S.A _ _ Φ' hκpot (hOmK Cκ) hΦpot g (hint _ hκpot g hg_c)
      (hint _ (hOmK Cκ) g hg_c),
      ReciprocityTheory.AnForm.M.mIntRsmul S.A Cκ S.Om.pot Φ' S.Om.isPot hΦpot g] at h0
    exact h0

  have sC : S.divInt Φ' u = S.divInt Φ' ut - S.divInt Φ' g := by
    have h := divInt_linear S Φ' hΦpot (-1) hg_c hut_c
    rw [hu_eq] at h
    linarith

  set H : W → ℝ := fun x => -2 * logNormSec S.L S.s x + F x with hHdef
  have hlns : ∀ P, IsPotential S.A P → MIntegrable S.A (Fin.cons P Φ') (logNormSec S.L S.s) :=
    fun P hP => ReciprocityTheory.AnForm.M.logNormIntegrable S.A S.L S.s S.mult S.comp S.L_pot S.s_sec
      S.s_snc _ (hcons P hP)
  have sD : mInt S.A (Fin.cons (kappaEp S.L S.s ε) Φ') ut - 2 * S.divInt Φ' ut =
      mInt S.A (Fin.cons (LocPot.ofFun ut) Φ') H := by
    have hL2 := ReciprocityTheory.AnForm.M.isPotentialRsmul S.A 2 S.L S.L_pot
    have hFpot : IsPotential S.A (LocPot.ofFun F) := ReciprocityTheory.AnForm.M.isPotential_ofFun _ _ hF
    have hadd := ReciprocityTheory.AnForm.M.mIntAdd S.A (S.L.rsmul 2) (LocPot.ofFun F) Φ' hL2 hFpot hΦpot ut
      (hint _ hL2 ut hut_c) (hint _ hFpot ut hut_c)
    have hrs := ReciprocityTheory.AnForm.M.mIntRsmul S.A 2 S.L Φ' S.L_pot hΦpot ut
    have hbp := ReciprocityTheory.AnForm.M.byPartsSymm S.A ut F hut hF Φ' hΦpot
    have hpl := ReciprocityTheory.AnForm.M.poincareLelong S.A S.L S.s S.mult S.comp S.B S.L_pot S.s_sec
      S.s_snc S.B_holo ut hut Φ' hΦpot
    have hlin := ReciprocityTheory.AnForm.M.mIntLinear S.A _ (hcons _ hutpot) (-2) (logNormSec S.L S.s) F
      (hlns _ hutpot) (hint _ hutpot F hF_c)
    have hk : kappaEp S.L S.s ε = S.L.rsmul 2 + LocPot.ofFun F := rfl
    have hdiv : S.divInt Φ' ut = ∑ k, (S.mult k : ℝ) * mInt (S.B k)
        (fun i => (Φ' i).pullback Subtype.val continuous_subtype_val) (ut ∘ Subtype.val) := rfl
    rw [hk, hadd, hrs, hbp, hdiv]
    rw [show (fun x => -2 * logNormSec S.L S.s x + F x) = H from rfl] at hlin
    rw [hlin]
    linarith

  have hZ := zeroSet_analytic (A := S.A) S.s_sec
  have hZi := interior_zeroSet S.s_sec S.s_snc
  have hGH : ∀ x ∉ zeroSet S.s, S.green ε x = H x := fun x hx =>
    greenEp_eq_off S.L S.s hε hx
  have hHint : ∀ P, IsPotential S.A P → MIntegrable S.A (Fin.cons P Φ') H := by
    intro P hP j K' hK' hKc
    have h1 := hlns P hP j K' hK' hKc
    have h2 := hint P hP F hF_c j K' hK' hKc
    exact IntegrableOn.congr_fun ((h1.const_mul (-2)).add h2)
      (fun y _ => by simp only [hHdef, Pi.add_apply]; ring) hKc.measurableSet
  have hPnn : FormNonneg S.A Set.univ ((LocPot.ofFun ut).rsmul (-1) + S.Om.pot.rsmul K) := by
    intro x k y hy w
    have hyt : y ∈ (S.A.chart k).target := hy.1
    have hyΩ : (S.A.chart k).symm y ∈ S.Om.pot.U x := hy.2.2.2
    have hu2 : ContDiffAt ℝ 2 ((LocPot.ofFun ut).φ x ∘ (S.A.chart k).symm) y :=
      ReciprocityTheory.AnForm.M.pot_contDiffAt_two hutpot x k hyt trivial
    have hΨ2 : ContDiffAt ℝ 2 (S.Om.pot.φ x ∘ (S.A.chart k).symm) y :=
      ReciprocityTheory.AnForm.M.pot_contDiffAt_two S.Om.isPot x k hyt hyΩ
    have hsum : ((LocPot.ofFun ut).rsmul (-1) + S.Om.pot.rsmul K).φ x ∘ (S.A.chart k).symm =
        fun z => (fun z' => -1 * ((LocPot.ofFun ut).φ x ∘ (S.A.chart k).symm) z') z +
          K * (S.Om.pot.φ x ∘ (S.A.chart k).symm) z := rfl
    rw [hsum, levi_add_smul K (contDiffAt_const.mul hu2) hΨ2 w, levi_smul' (-1) hu2 w]
    have hb := abs_le.mp (hK x k y ⟨hyt, trivial, hyΩ⟩ w)
    linarith [hb.2]
  have mIntCongrNull : ∀ (Φ : Fin (D + 1) → LocPot W) (Z : Set W),
      S.A.IsAnalyticSubset Z → interior Z = ∅ → ∀ g g' : W → ℝ,
      (∀ x ∉ Z, g x = g' x) → mInt S.A Φ g = mInt S.A Φ g' := by
    intro Φ Z hZ hZi g g' hg
    unfold mInt
    split_ifs with h
    · exact ReciprocityTheory.AnForm.M.integralWith_congr_null S.A h.some Φ hZ hZi hg
    · rfl
  have sE : 0 ≤ -mInt S.A (Fin.cons (LocPot.ofFun ut) Φ') H +
      K * mInt S.A (Fin.cons S.Om.pot Φ') H := by
    have hm1 := ReciprocityTheory.AnForm.M.isPotentialRsmul S.A (-1) _ hutpot
    have hPpot : IsPotential S.A ((LocPot.ofFun ut).rsmul (-1) + S.Om.pot.rsmul K) :=
      ReciprocityTheory.AnForm.M.isPotentialAdd S.A _ _ hm1 (hOmK K)
    have h0 := mInt_nonneg_of_compl S.A S.Yo S.bd_analytic S.bd_interior _ (hcons _ hPpot)
      (hconsnn _ (formNonneg_mono hPnn)) (S.green ε)
      (fun x => GreenMassReplace.greenEp_nonneg S.L S.s hε x)
    rw [mIntCongrNull _ (zeroSet S.s) hZ hZi (S.green ε) H hGH,
      ReciprocityTheory.AnForm.M.mIntAdd S.A _ _ Φ' hm1 (hOmK K) hΦpot H (hHint _ hm1) (hHint _ (hOmK K)),
      ReciprocityTheory.AnForm.M.mIntRsmul S.A (-1) _ Φ' hutpot hΦpot H,
      ReciprocityTheory.AnForm.M.mIntRsmul S.A K S.Om.pot Φ' S.Om.isPot hΦpot H] at h0
    linarith

  have hperm : ∀ f : W → ℝ, mInt S.A (mixedForms S.Om.pot (S.T t) a) f =
      mInt S.A (Fin.cons S.Om.pot Φ') f := fun f => by
    rw [mixedForms_eq_cons S.Om.pot (S.T t) a ha, ReciprocityTheory.AnForm.M.mIntSymm]
    rfl
  have hJ : S.J a ε t = mInt S.A (Fin.cons S.Om.pot Φ') H := by
    rw [← mIntCongrNull _ (zeroSet S.s) hZ hZi (S.green ε) H hGH]
    exact hperm _
  have hW : S.errW a ha t₀ t = mInt S.A (Fin.cons S.Om.pot Φ') g := hperm _
  have hP : S.plTerm a ha ε t = mInt S.A (Fin.cons (kappaEp S.L S.s ε) Φ') u -
      2 * S.divInt Φ' u := rfl
  have hD : S.errDiv a ha t₀ t = S.divInt Φ' g := rfl
  rw [hP, hJ, hW, hD, sA, sC]
  nlinarith [sA, sB, sC, sD, sE]

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
