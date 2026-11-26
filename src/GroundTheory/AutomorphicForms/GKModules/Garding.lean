module

public import GroundTheory.AutomorphicForms.GKModules.SmoothVectors
public import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
public import GroundTheory.AutomorphicForms.DixmierMalliavinBasic

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.GKModules.Garding
namespace GroundTheory.Automorphic

open MeasureTheory NormedSpace Set Filter Topology Metric
open scoped Manifold ContDiff

set_option linter.unusedSectionVars false

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

theorem secondCountableTopology_subgroup_units (G : Subgroup 𝔸ˣ) : SecondCountableTopology G := by
  have hemb : Topology.IsEmbedding (fun x : G => ((x : 𝔸ˣ) : 𝔸)) :=
    Units.isOpenEmbedding_val.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  exact hemb.secondCountableTopology

noncomputable def BanachRep.integrated {K : Type*} [Group K] [TopologicalSpace K] [MeasurableSpace K]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep K E) (μ : Measure K)
    (f : K → ℂ) (v : E) : E :=
  ∫ g, f g • π g v ∂μ

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

theorem continuous_iteratedFDeriv_param {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] (ψ : P → G → E')
    (hψ : ∀ g₀ : G, ContDiff ℝ ∞ (fun q : P × 𝔤 => ψ q.1 (g₀ * h.expG q.2))) (k : ℕ) :
    Continuous (fun p : P × G => iteratedFDeriv ℝ k (fun Y => ψ Y p.2) p.1) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨Y₀, g₀⟩
  set Φ : P × 𝔤 → E' := fun q => ψ q.1 (g₀ * h.expG q.2) with hΦdef
  have hΦ : ContDiff ℝ ∞ Φ := hψ g₀
  set L := ContinuousLinearMap.inl ℝ P 𝔤
  set H : P × 𝔤 → ContinuousMultilinearMap ℝ (fun _ : Fin k => P) E' :=
    fun q => ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => L) (iteratedFDeriv ℝ k Φ q)
  have hH : Continuous H :=
    (ContinuousLinearMap.continuous _).comp (hΦ.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  have hpart : ∀ (Z : 𝔤) (Y : P), iteratedFDeriv ℝ k (fun Y => Φ (Y, Z)) Y = H (Y, Z) := by
    intro Z Y
    have e : (fun Y => Φ (Y, Z)) = (fun w => Φ (w + (0, Z))) ∘ L := by
      funext Y; simp [L]
    have hΦZ : ContDiff ℝ ∞ (fun w : P × 𝔤 => Φ (w + (0, Z))) :=
      hΦ.comp (contDiff_id.add contDiff_const)
    rw [e, L.iteratedFDeriv_comp_right hΦZ Y (by exact_mod_cast le_top),
      iteratedFDeriv_comp_add_right]
    simp [H, L]
  letI := h.chartedSpace
  have hg₀ : g₀ ∈ (h.chart g₀).source := mem_chart_source 𝔤 g₀
  have hsrc : (h.chart g₀).source ∈ 𝓝 g₀ := (h.chart g₀).open_source.mem_nhds hg₀
  have hev : (fun p : P × G => iteratedFDeriv ℝ k (fun Y => ψ Y p.2) p.1) =ᶠ[𝓝 (Y₀, g₀)]
      fun p => H (p.1, h.chart g₀ p.2) := by
    filter_upwards [prod_mem_nhds univ_mem hsrc] with p hp
    have e : (fun Y => ψ Y p.2) = fun Y => Φ (Y, h.chart g₀ p.2) := by
      funext Y
      simp only [hΦdef]
      rw [show g₀ * h.expG (h.chart g₀ p.2) = p.2 from (h.chart g₀).left_inv hp.2]
    rw [e, hpart]
  refine ContinuousAt.congr ?_ hev.symm
  exact hH.continuousAt.comp (continuousAt_fst.prodMk
    (((h.chart g₀).continuousAt hg₀).comp continuousAt_snd))

def IsTestFunction (f : G → ℂ) : Prop :=
  (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) ∧ HasCompactSupport f

theorem IsTestFunction.continuous {f : G → ℂ} (hf : h.IsTestFunction f) : Continuous f := by
  letI := h.chartedSpace
  exact hf.1.continuous

theorem contDiff_comp_expG_mul_expG {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : G → F} (hf : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, F) ∞ f)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {φ₁ φ₂ : V → 𝔤}
    (h₁ : ContDiff ℝ ∞ φ₁) (a : G) (h₂ : ContDiff ℝ ∞ φ₂) :
    ContDiff ℝ ∞ (fun p => f (h.expG (φ₁ p) * a * h.expG (φ₂ p))) := by
  letI := h.chartedSpace
  haveI := h.lieGroup ∞
  have hm : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, 𝔤) ∞ (fun p => h.expG (φ₁ p) * a * h.expG (φ₂ p)) :=
    ((h.contMDiff_expG_comp h₁).mul contMDiff_const).mul (h.contMDiff_expG_comp h₂)
  exact (ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) hf hm).contDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (π : BanachRep G E)
variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
  [IsFiniteMeasureOnCompacts μ]

theorem integrable_smul_orbit {f : G → ℂ} (hf : h.IsTestFunction f) (v : E) :
    Integrable (fun g => f g • π g v) μ := by
  haveI := secondCountableTopology_subgroup_units G
  refine ((hf.continuous h).smul (π.continuous_orbit v)).integrable_of_hasCompactSupport ?_
  exact hf.2.smul_right

theorem isSmoothVector_integrated {f : G → ℂ} (hf : h.IsTestFunction f) (v : E) :
    h.IsSmoothVector π (π.integrated μ f v) := by
  haveI := secondCountableTopology_subgroup_units G
  rw [isSmoothVector_iff]

  set F : 𝔤 → G → E := fun Y g => f (h.expG (-Y) * g) • π g v with hFdef
  have hexp : h.expOrbit π (π.integrated μ f v) = fun Y => ∫ g, F Y g ∂μ := by
    funext Y
    rw [expOrbit_apply, BanachRep.integrated,
      ← (π (h.expG Y)).integral_comp_comm (h.integrable_smul_orbit π μ hf v)]
    rw [← integral_mul_left_eq_self (F Y) (h.expG Y)]
    congr 1
    funext x
    simp [hFdef, BanachRep.map_mul_apply, expG_neg]
  rw [hexp]

  set ψ : 𝔤 → G → ℂ := fun Y g => f (h.expG (-Y) * g) with hψdef
  have hψ : ∀ g₀ : G, ContDiff ℝ ∞ (fun q : 𝔤 × 𝔤 => ψ q.1 (g₀ * h.expG q.2)) := by
    intro g₀
    have := h.contDiff_comp_expG_mul_expG hf.1 (contDiff_fst.neg) g₀ contDiff_snd
    simpa [hψdef, mul_assoc] using this
  have hψY : ∀ g : G, ContDiff ℝ ∞ (fun Y => ψ Y g) := by
    intro g
    have := h.contDiff_comp_expG_mul_expG hf.1 (contDiff_id.neg) g (contDiff_const (c := (0 : 𝔤)))
    simpa [hψdef] using this

  set Lw : G → ℂ →L[ℝ] E := fun g => (ContinuousLinearMap.lsmul ℝ ℂ).flip (π g v) with hLw
  have hLwc : Continuous Lw := (ContinuousLinearMap.continuous _).comp (π.continuous_orbit v)
  have hFL : ∀ g, (fun Y => F Y g) = Lw g ∘ fun Y => ψ Y g := by
    intro g; funext Y; simp [hFdef, hLw, hψdef]
  have hiter : ∀ (k : ℕ) (Y : 𝔤) (g : G), ParamIntegral.iter F k Y g =
      (Lw g).compContinuousMultilinearMap (iteratedFDeriv ℝ k (fun Y => ψ Y g) Y) := by
    intro k Y g
    rw [ParamIntegral.iter, hFL g]
    exact (Lw g).iteratedFDeriv_comp_left (hψY g).contDiffAt (by exact_mod_cast le_top)
  refine contDiff_integral_of_iteratedFDeriv F (fun g => ?_) (fun k => ?_) (fun Y₀ => ?_)
  · rw [hFL g]; exact (Lw g).contDiff.comp (hψY g)
  · simp_rw [hiter]
    have hc := h.continuous_iteratedFDeriv_param ψ hψ k
    have hB := ContinuousLinearMap.continuous₂ (𝕜 := ℝ) (E := ℂ →L[ℝ] E)
      (F := ContinuousMultilinearMap ℝ (fun _ : Fin k => 𝔤) ℂ)
      (G := ContinuousMultilinearMap ℝ (fun _ : Fin k => 𝔤) E)
      (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k => 𝔤) ℂ E)
    exact hB.comp ((hLwc.comp continuous_snd).prodMk hc)
  ·
    refine ⟨closedBall Y₀ 1, closedBall_mem_nhds Y₀ one_pos,
      (fun p : 𝔤 × G => h.expG p.1 * p.2) '' (closedBall Y₀ 1 ×ˢ tsupport f), ?_, ?_⟩
    · exact ((isCompact_closedBall Y₀ 1).prod hf.2).image
        ((h.continuous_expG.comp continuous_fst).mul continuous_snd)
    · intro Y hY g hg
      simp only [hFdef]
      by_contra hne
      apply hg
      refine ⟨(Y, h.expG (-Y) * g), ⟨hY, subset_tsupport f ?_⟩, ?_⟩
      · intro h0; apply hne; simp [h0]
      · simp [expG_neg]

end IsExpLieAlgebra

end GroundTheory.Automorphic
end

section -- merged from GroundTheory.AutomorphicForms.GKModules.RightRegular
namespace GroundTheory.Automorphic

open NormedSpace Set Filter Topology
open scoped Manifold ContDiff

set_option linter.unusedSectionVars false

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

def rightTranslate {M : Type*} [Mul M] {F : Type*} (a : M) (f : M → F) (g : M) : F := f (g * a)

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

def IsSmoothFun (f : G → F) : Prop :=
  letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, F) ∞ f

theorem isSmoothFun_iff {f : G → F} :
    h.IsSmoothFun f ↔ ∀ g : G, ContDiff ℝ ∞ (fun Y : 𝔤 => f (g * h.expG Y)) :=
  h.contMDiff_iff_expG f

theorem IsSmoothFun.contDiff_comp {f : G → F} (hf : h.IsSmoothFun f) (g₀ : G) {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {φ₁ φ₂ φ₃ : V → 𝔤} (h₁ : ContDiff ℝ ∞ φ₁)
    (h₂ : ContDiff ℝ ∞ φ₂) (h₃ : ContDiff ℝ ∞ φ₃) :
    ContDiff ℝ ∞ (fun p => f (g₀ * h.expG (φ₁ p) * h.expG (φ₂ p) * h.expG (φ₃ p))) := by
  letI := h.chartedSpace
  haveI := h.lieGroup ∞
  have hm : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, 𝔤) ∞
      (fun p => g₀ * h.expG (φ₁ p) * h.expG (φ₂ p) * h.expG (φ₃ p)) :=
    ((contMDiff_const.mul (h.contMDiff_expG_comp h₁)).mul (h.contMDiff_expG_comp h₂)).mul
      (h.contMDiff_expG_comp h₃)
  exact (ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) hf hm).contDiff

noncomputable def rightDeriv (X : 𝔤) (f : G → F) (g : G) : F :=
  fderiv ℝ (fun Y : 𝔤 => f (g * h.expG Y)) 0 X

theorem differentiable_comp_expG {f : G → F} (hf : h.IsSmoothFun f) (g : G) :
    Differentiable ℝ (fun Y : 𝔤 => f (g * h.expG Y)) :=
  ((h.isSmoothFun_iff).1 hf g).differentiable (by simp)

theorem hasDerivAt_rightDeriv {f : G → F} (hf : h.IsSmoothFun f) (X : 𝔤) (g : G) :
    HasDerivAt (fun t : ℝ => f (g * h.expG (t • X))) (h.rightDeriv X f g) 0 := by
  have h1 := hasDerivAt_comp_line (h.differentiable_comp_expG hf g 0) X
  simp only [zero_add] at h1
  exact h1

theorem isSmoothFun_rightTranslate {f : G → F} (hf : h.IsSmoothFun f) (a : G) :
    h.IsSmoothFun (rightTranslate a f) := by
  letI := h.chartedSpace
  haveI := h.lieGroup ∞
  exact ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) hf (contMDiff_id.mul contMDiff_const)

theorem isSmoothFun_rightDeriv {f : G → F} (hf : h.IsSmoothFun f) (X : 𝔤) :
    h.IsSmoothFun (h.rightDeriv X f) := by
  rw [isSmoothFun_iff]
  intro g₀
  have hΨ : ContDiff ℝ ∞ (Function.uncurry fun Z Y : 𝔤 => f (g₀ * h.expG Z * h.expG Y)) := by
    have := hf.contDiff_comp h g₀ (φ₁ := fun p : 𝔤 × 𝔤 => p.1) (φ₂ := fun p => p.2)
      (φ₃ := fun _ => 0) contDiff_fst contDiff_snd contDiff_const
    convert this using 2 with p
    simp [Function.uncurry]
  have hd : ContDiff ℝ ∞ (fun Z : 𝔤 => fderiv ℝ (fun Y : 𝔤 => f (g₀ * h.expG Z * h.expG Y)) 0) :=
    ContDiff.fderiv hΨ contDiff_const (by simp)
  exact hd.clm_apply contDiff_const

theorem rightDeriv_add_left (X Y : 𝔤) (f : G → F) :
    h.rightDeriv (X + Y) f = h.rightDeriv X f + h.rightDeriv Y f := by
  funext g; simp [rightDeriv]

theorem rightDeriv_smul_left (r : ℝ) (X : 𝔤) (f : G → F) :
    h.rightDeriv (r • X) f = r • h.rightDeriv X f := by
  funext g; simp [rightDeriv]

theorem rightDeriv_neg_left (X : 𝔤) (f : G → F) : h.rightDeriv (-X) f = -h.rightDeriv X f := by
  funext g; simp [rightDeriv]

theorem rightDeriv_add {f₁ f₂ : G → F} (hf₁ : h.IsSmoothFun f₁) (hf₂ : h.IsSmoothFun f₂)
    (X : 𝔤) : h.rightDeriv X (f₁ + f₂) = h.rightDeriv X f₁ + h.rightDeriv X f₂ := by
  funext g
  simp only [rightDeriv, Pi.add_apply]
  rw [fderiv_fun_add (h.differentiable_comp_expG hf₁ g 0) (h.differentiable_comp_expG hf₂ g 0)]
  rfl

theorem rightDeriv_smul {f : G → F} (hf : h.IsSmoothFun f) (c : ℂ) (X : 𝔤) :
    h.rightDeriv X (c • f) = c • h.rightDeriv X f := by
  funext g
  simp only [rightDeriv, Pi.smul_apply]
  rw [fderiv_fun_const_smul (h.differentiable_comp_expG hf g 0) c]
  rfl

theorem rightDeriv_rightTranslate {f : G → F} (hf : h.IsSmoothFun f) (a : G) (X : 𝔤) :
    h.rightDeriv X (rightTranslate a f) = rightTranslate a (h.rightDeriv (h.Ad a⁻¹ X) f) := by
  funext g
  simp only [rightDeriv, rightTranslate]
  have e : (fun Y : 𝔤 => f (g * h.expG Y * a)) =
      (fun Y : 𝔤 => f (g * a * h.expG Y)) ∘ h.AdL a⁻¹ := by
    funext Y
    simp only [Function.comp_apply, AdL_apply, expG_Ad, inv_inv]
    congr 1
    group
  rw [e]
  have hF : HasFDerivAt (fun Y : 𝔤 => f (g * a * h.expG Y))
      (fderiv ℝ (fun Y : 𝔤 => f (g * a * h.expG Y)) 0) (h.AdL a⁻¹ 0) := by
    simpa using (h.differentiable_comp_expG hf (g * a) 0).hasFDerivAt
  rw [(hF.comp (0 : 𝔤) (h.AdL a⁻¹).hasFDerivAt).fderiv]
  rfl

theorem rightDeriv_bracket {f : G → F} (hf : h.IsSmoothFun f) (X Y : 𝔤) :
    h.rightDeriv (h.bracket X Y) f =
      h.rightDeriv X (h.rightDeriv Y f) - h.rightDeriv Y (h.rightDeriv X f) := by
  funext g
  set A : ℝ × ℝ × ℝ → F :=
    fun p => f (g * h.expG (p.1 • X) * h.expG (p.2.1 • Y) * h.expG (p.2.2 • (-X))) with hAdef
  have hA : ContDiff ℝ ∞ A := hf.contDiff_comp h g
    (contDiff_fst.smul contDiff_const) ((contDiff_fst.comp contDiff_snd).smul contDiff_const)
    ((contDiff_snd.comp contDiff_snd).smul contDiff_const)
  have hAd : Differentiable ℝ A := hA.differentiable (by simp)
  set D2 := fderiv ℝ (fderiv ℝ A) 0
  set er : ℝ × ℝ × ℝ := (1, 0, 0)
  set et : ℝ × ℝ × ℝ := (0, 1, 0)
  set eu : ℝ × ℝ × ℝ := (0, 0, 1)
  have hY := h.isSmoothFun_rightDeriv hf Y
  have hX := h.isSmoothFun_rightDeriv hf X
  have da : ∀ r : ℝ, fderiv ℝ A (r • er) et = h.rightDeriv Y f (g * h.expG (r • X)) := by
    intro r
    have h1 := hasDerivAt_comp_line (hAd (r • er)) et
    have h2 := h.hasDerivAt_rightDeriv hf Y (g * h.expG (r • X))
    refine h1.unique (h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_))
    simp [A, er, et]
  have dc : ∀ t : ℝ, fderiv ℝ A (t • et) eu = -h.rightDeriv X f (g * h.expG (t • Y)) := by
    intro t
    have h1 := hasDerivAt_comp_line (hAd (t • et)) eu
    have h2 := h.hasDerivAt_rightDeriv hf (-X) (g * h.expG (t • Y))
    rw [rightDeriv_neg_left] at h2
    refine h1.unique (h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_))
    simp [A, et, eu]
  have db : D2 er et = h.rightDeriv X (h.rightDeriv Y f) g := by
    have h1 := hasDerivAt_fderiv_line hA 0 er et
    have h2 := h.hasDerivAt_rightDeriv hY X g
    refine h1.unique (h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_))
    simp only [zero_add]
    rw [da]
  have dd : D2 et eu = -h.rightDeriv Y (h.rightDeriv X f) g := by
    have h1 := hasDerivAt_fderiv_line hA 0 et eu
    have h2 := (h.hasDerivAt_rightDeriv hX Y g).neg
    refine h1.unique (h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_))
    simp only [zero_add]
    rw [dc]
    rfl
  have hsymm : D2 eu et = D2 et eu :=
    (hA.contDiffAt.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)) eu et
  have diag : ∀ s : ℝ, fderiv ℝ A (s • (er + eu)) et =
      fderiv ℝ (fun Z : 𝔤 => f (g * h.expG Z)) 0 (h.Ad (h.expG (s • X)) Y) := by
    intro s
    have h1 := hasDerivAt_comp_line (hAd (s • (er + eu))) et
    have h2 := h.hasDerivAt_rightDeriv hf (h.Ad (h.expG (s • X)) Y) g
    refine h1.unique (h2.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_))
    simp only [A, er, eu, et, Prod.smul_mk, Prod.mk_add_mk, smul_zero, smul_eq_mul, mul_one,
      mul_zero, add_zero, zero_add]
    rw [← map_smul, expG_Ad, smul_neg, expG_neg]
    simp only [mul_assoc]
  have hg := hasDerivAt_fderiv_line hA 0 (er + eu) et
  have hg' := (fderiv ℝ (fun Z : 𝔤 => f (g * h.expG Z)) 0).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (h.hasDerivAt_Ad_expG X Y)
  have e := hg.unique (hg'.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_))
  · change D2 (er + eu) et = h.rightDeriv (h.bracket X Y) f g at e
    rw [Pi.sub_apply, ← e, map_add (f := _), ContinuousLinearMap.add_apply, db, hsymm, dd, sub_eq_add_neg]
  · simp only [zero_add, Function.comp_apply]
    rw [diag]

def smoothFuns : Submodule ℂ (G → F) where
  carrier := {f | h.IsSmoothFun f}
  zero_mem' := by
    show h.IsSmoothFun (0 : G → F)
    letI := h.chartedSpace
    exact contMDiff_const
  add_mem' {f₁ f₂} hf₁ hf₂ := by
    change h.IsSmoothFun f₁ at hf₁
    change h.IsSmoothFun f₂ at hf₂
    show h.IsSmoothFun (f₁ + f₂)
    letI := h.chartedSpace
    exact hf₁.add hf₂
  smul_mem' c f hf := by
    change h.IsSmoothFun f at hf
    show h.IsSmoothFun (c • f)
    letI := h.chartedSpace
    have e : c • f = ((c • ContinuousLinearMap.id ℂ F).restrictScalars ℝ) ∘ f := by
      funext g; simp
    rw [e]
    exact ((c • ContinuousLinearMap.id ℂ F).restrictScalars ℝ).contDiff.comp_contMDiff hf

theorem mem_smoothFuns {f : G → F} : f ∈ h.smoothFuns (F := F) ↔ h.IsSmoothFun f := Iff.rfl

noncomputable def rightDerivEnd (X : 𝔤) : Module.End ℂ (h.smoothFuns (F := F)) where
  toFun f := ⟨h.rightDeriv X f, h.isSmoothFun_rightDeriv f.2 X⟩
  map_add' f₁ f₂ := by ext1; exact h.rightDeriv_add f₁.2 f₂.2 X
  map_smul' c f := by ext1; exact h.rightDeriv_smul f.2 c X

@[simp] theorem coe_rightDerivEnd (X : 𝔤) (f : h.smoothFuns (F := F)) :
    ((h.rightDerivEnd X f : h.smoothFuns (F := F)) : G → F) = h.rightDeriv X f := rfl

def rightTranslateEnd (a : G) : Module.End ℂ (h.smoothFuns (F := F)) where
  toFun f := ⟨rightTranslate a f, h.isSmoothFun_rightTranslate f.2 a⟩
  map_add' f₁ f₂ := rfl
  map_smul' c f := rfl

@[simp] theorem coe_rightTranslateEnd (a : G) (f : h.smoothFuns (F := F)) :
    ((h.rightTranslateEnd a f : h.smoothFuns (F := F)) : G → F) = rightTranslate a f := rfl

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable def rightDerivLie : h.lieSubalgebra →ₗ⁅ℝ⁆ Module.End ℂ (h.smoothFuns (F := F)) where
  toFun X := h.rightDerivEnd (h.ofLie X)
  map_add' X Y := by ext1 f; ext1; exact h.rightDeriv_add_left _ _ _
  map_smul' r X := by ext1 f; ext1; exact h.rightDeriv_smul_left r _ _
  map_lie' {X Y} := by
    ext1 f; ext1
    rw [h.ofLie_lie, Ring.lie_def]
    exact h.rightDeriv_bracket f.2 _ _

noncomputable def rightUAction :
    UniversalEnvelopingAlgebra ℝ h.lieSubalgebra →ₐ[ℝ] Module.End ℂ (h.smoothFuns (F := F)) :=
  UniversalEnvelopingAlgebra.lift ℝ h.rightDerivLie

@[simp] theorem rightUAction_ι (X : h.lieSubalgebra) :
    h.rightUAction (F := F) (UniversalEnvelopingAlgebra.ι ℝ X) = h.rightDerivEnd (h.ofLie X) :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℝ h.rightDerivLie X

def centerU : Subalgebra ℝ (UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) :=
  Subalgebra.center ℝ _

def IsZFinite (f : h.smoothFuns (F := F)) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ ((fun z => h.rightUAction z f) '' (h.centerU : Set _)))

def IsRightKFinite (K : Subgroup G) (f : G → F) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ (range fun k : K => rightTranslate (k : G) f))

end IsExpLieAlgebra

end GroundTheory.Automorphic
end
