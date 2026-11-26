module

public import ReciprocityTheory.AnalyticForms.MaIntEmpty

@[expose] public section

section -- merged from ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
namespace ReciprocityTheory.AnForm

open Filter Topology
open scoped ContDiff

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem levi_congr {φ ψ : (ι → ℂ) → ℝ} {z : ι → ℂ} (h : φ =ᶠ[𝓝 z] ψ) (w : ι → ℂ) :
    levi φ z w = levi ψ z w := by
  have h2 : fderiv ℝ φ =ᶠ[𝓝 z] fderiv ℝ ψ := h.eventuallyEq_nhds.mono fun y hy => hy.fderiv_eq
  unfold levi
  rw [h2.fderiv_eq]

private theorem fderiv_fderiv_I_smul_I_smul_of_analyticAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {τ : E → F} {z : E}
    (hτ : AnalyticAt ℂ τ z) (a : E) :
    fderiv ℝ (fderiv ℝ τ) z (Complex.I • a) (Complex.I • a) = - fderiv ℝ (fderiv ℝ τ) z a a := by
  have hH : AnalyticAt ℂ (fderiv ℂ τ) z := hτ.fderiv
  let R := ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℝ

  have hev : fderiv ℝ τ =ᶠ[𝓝 z] fun y => R (fderiv ℂ τ y) := by
    filter_upwards [hτ.eventually_analyticAt] with y hy
    exact (hy.differentiableAt.hasFDerivAt.restrictScalars ℝ).fderiv
  have hD : HasFDerivAt (fun y => R (fderiv ℂ τ y))
      (R.comp ((fderiv ℂ (fderiv ℂ τ) z).restrictScalars ℝ)) z :=
    R.hasFDerivAt.comp z (hH.differentiableAt.hasFDerivAt.restrictScalars ℝ)
  rw [hev.fderiv_eq, hD.fderiv]
  simp [R, smul_smul]

theorem sndDeriv_I_I {τ : (ι → ℂ) → (κ → ℂ)} {z : ι → ℂ} (hτ : AnalyticAt ℂ τ z) (a : ι → ℂ) :
    fderiv ℝ (fderiv ℝ τ) z (Complex.I • a) (Complex.I • a) = - fderiv ℝ (fderiv ℝ τ) z a a :=
  fderiv_fderiv_I_smul_I_smul_of_analyticAt hτ a

theorem levi_comp {φ : (κ → ℂ) → ℝ} {τ : (ι → ℂ) → (κ → ℂ)} {z : ι → ℂ} (w : ι → ℂ)
    (hτ : AnalyticAt ℂ τ z) (hφ : ContDiffAt ℝ 2 φ (τ z)) :
    levi (φ ∘ τ) z w = levi φ (τ z) (fderiv ℂ τ z w) := by
  have hτR : ∀ n : ℕ∞, ContDiffAt ℝ n τ z := fun n => (hτ.contDiffAt (n := n)).restrict_scalars ℝ
  have hφ1 : ∀ᶠ x in 𝓝 (τ z), DifferentiableAt ℝ φ x :=
    (hφ.eventually (by simp)).mono fun x hx => hx.differentiableAt (by norm_num)
  have hφ1' : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ φ (τ y) := hτ.continuousAt.eventually hφ1

  have hev : fderiv ℝ (φ ∘ τ) =ᶠ[𝓝 z] fun y => (fderiv ℝ φ (τ y)).comp (fderiv ℝ τ y) := by
    filter_upwards [hτ.eventually_analyticAt, hφ1'] with y hy hφy
    exact fderiv_comp y hφy (hy.differentiableAt.restrictScalars ℝ)
  have hdA : DifferentiableAt ℝ (fderiv ℝ φ) (τ z) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdB : DifferentiableAt ℝ (fderiv ℝ τ) z :=
    ((hτR 2).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hτz : HasFDerivAt τ (fderiv ℝ τ z) z := ((hτR 1).differentiableAt one_ne_zero).hasFDerivAt
  have hc : HasFDerivAt (fun y => fderiv ℝ φ (τ y))
      ((fderiv ℝ (fderiv ℝ φ) (τ z)).comp (fderiv ℝ τ z)) z :=
    hdA.hasFDerivAt.comp z hτz

  have hD := hc.clm_comp hdB.hasFDerivAt
  have hB : fderiv ℝ τ z = (fderiv ℂ τ z).restrictScalars ℝ :=
    (hτ.differentiableAt.hasFDerivAt.restrictScalars ℝ).fderiv
  have hI := sndDeriv_I_I hτ w
  unfold levi
  rw [hev.fderiv_eq, hD.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply, hI, map_neg, hB,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul]
  ring

theorem levi_zero (φ : (ι → ℂ) → ℝ) (z : ι → ℂ) : levi φ z 0 = 0 := by
  simp [levi]

theorem levi_smul_dir (φ : (ι → ℂ) → ℝ) (z w : ι → ℂ) (t : ℝ) :
    levi φ z (t • w) = t ^ 2 * levi φ z w := by
  unfold levi
  rw [smul_comm Complex.I t w]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem levi_add_smul {f g : (ι → ℂ) → ℝ} {z : ι → ℂ} (c : ℝ) (hf : ContDiffAt ℝ 2 f z)
    (hg : ContDiffAt ℝ 2 g z) (w : ι → ℂ) :
    levi (fun y => f y + c * g y) z w = levi f z w + c * levi g z w := by
  have hf1 : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ f y :=
    (hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hg1 : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ g y :=
    (hg.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hev : fderiv ℝ (fun y => f y + c * g y) =ᶠ[𝓝 z]
      fun y => fderiv ℝ f y + c • fderiv ℝ g y := by
    filter_upwards [hf1, hg1] with y hfy hgy
    exact (hfy.hasFDerivAt.add (hgy.hasFDerivAt.const_mul c)).fderiv
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdg : DifferentiableAt ℝ (fderiv ℝ g) z :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  unfold levi
  have hD : HasFDerivAt (fun y => fderiv ℝ f y + c • fderiv ℝ g y)
      (fderiv ℝ (fderiv ℝ f) z + c • fderiv ℝ (fderiv ℝ g) z) z :=
    hdf.hasFDerivAt.add (hdg.hasFDerivAt.const_smul c)
  rw [hev.fderiv_eq, hD.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem levi_clm (L : (ι → ℂ) →L[ℝ] ℝ) (z w : ι → ℂ) : levi (⇑L) z w = 0 := by
  have h : fderiv ℝ (⇑L) = fun _ => L := funext fun _ => L.fderiv
  simp [levi, h]

theorem levi_re_analytic {G : (ι → ℂ) → ℂ} {z : ι → ℂ} (hG : AnalyticAt ℂ G z) (w : ι → ℂ) :
    levi (fun y => (G y).re) z w = 0 := by
  have hcd : ∀ n : ℕ∞, ContDiffAt ℝ n G z := fun n => (hG.contDiffAt (n := n)).restrict_scalars ℝ
  have hG1 : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ G y :=
    hG.eventually_analyticAt.mono fun y hy => hy.differentiableAt.restrictScalars ℝ
  let Q := ContinuousLinearMap.compL ℝ (ι → ℂ) ℂ ℝ Complex.reCLM
  have hev : fderiv ℝ (fun y => (G y).re) =ᶠ[𝓝 z] fun y => Q (fderiv ℝ G y) := by
    filter_upwards [hG1] with y hy
    exact ((Complex.reCLM.hasFDerivAt).comp y hy.hasFDerivAt).fderiv
  have hdG : DifferentiableAt ℝ (fderiv ℝ G) z :=
    ((hcd 2).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hD : HasFDerivAt (fun y => Q (fderiv ℝ G y)) (Q.comp (fderiv ℝ (fderiv ℝ G) z)) z :=
    Q.hasFDerivAt.comp z hdG.hasFDerivAt
  unfold levi
  rw [hev.fderiv_eq, hD.fderiv]
  have hI := fderiv_fderiv_I_smul_I_smul_of_analyticAt hG w
  simp only [ContinuousLinearMap.comp_apply, Q, ContinuousLinearMap.compL_apply,
    Complex.reCLM_apply, hI, Complex.neg_re]
  ring

theorem continuousOn_levi {φ : (ι → ℂ) → ℝ} {U : Set (ι → ℂ)} (hU : IsOpen U)
    (hφ : ContDiffOn ℝ 2 φ U) :
    ContinuousOn (fun p : (ι → ℂ) × (ι → ℂ) => levi φ p.1 p.2) (U ×ˢ Set.univ) := by
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ φ) U := hφ.fderiv_of_isOpen hU (by norm_num)
  have h2 : ContinuousOn (fderiv ℝ (fderiv ℝ φ)) U := h1.continuousOn_fderiv_of_isOpen hU le_rfl
  have h3 : ContinuousOn (fun p : (ι → ℂ) × (ι → ℂ) => fderiv ℝ (fderiv ℝ φ) p.1) (U ×ˢ Set.univ) :=
    h2.comp continuousOn_fst fun p hp => hp.1
  have h4 : ContinuousOn (fun p : (ι → ℂ) × (ι → ℂ) => Complex.I • p.2) (U ×ˢ Set.univ) :=
    (by fun_prop : Continuous fun p : (ι → ℂ) × (ι → ℂ) => Complex.I • p.2).continuousOn
  unfold levi
  exact (((h3.clm_apply continuousOn_snd).clm_apply continuousOn_snd).add
    ((h3.clm_apply h4).clm_apply h4)).div_const 4

end

end ReciprocityTheory.AnForm
end

section -- merged from ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
namespace ReciprocityTheory.AnForm.M

open MeasureTheory
open scoped ContDiff

noncomputable section

structure FinHolAtlas (e : ℕ) (X : Type*) [TopologicalSpace X] where

  n : ℕ

  chart : Fin n → OpenPartialHomeomorph X (Fin e → ℂ)

  cover : ∀ x, ∃ j, x ∈ (chart j).source

  holo : ∀ j k, AnalyticOnNhd ℂ (chart k ∘ (chart j).symm)
    ((chart j).target ∩ (chart j).symm ⁻¹' (chart k).source)

namespace FinHolAtlas

variable {e : ℕ} {X : Type*} [TopologicalSpace X]

def SmoothOn (A : FinHolAtlas e X) (U : Set X) (f : X → ℝ) : Prop :=
  ∀ j, ContDiffOn ℝ ∞ (f ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U)

def Smooth (A : FinHolAtlas e X) (f : X → ℝ) : Prop :=
  A.SmoothOn Set.univ f

def HoloOn (A : FinHolAtlas e X) (U : Set X) (g : X → ℂ) : Prop :=
  ∀ j, AnalyticOnNhd ℂ (g ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U)

def Compatible {e : ℕ} (A B : FinHolAtlas e X) : Prop :=
  (∀ j k, AnalyticOnNhd ℂ (B.chart k ∘ (A.chart j).symm)
    ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (B.chart k).source)) ∧
  ∀ j k, AnalyticOnNhd ℂ (A.chart k ∘ (B.chart j).symm)
    ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (A.chart k).source)

def IsAnalyticSubset (A : FinHolAtlas e X) (S : Set X) : Prop :=
  ∀ x, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ ∃ (r : ℕ) (f : Fin r → X → ℂ),
    (∀ i, A.HoloOn W (f i)) ∧ S ∩ W = {y ∈ W | ∀ i, f i y = 0}

end FinHolAtlas

open FinHolAtlas

structure LocPot (X : Type*) [TopologicalSpace X] where

  U : X → Set X
  isOpen_U : ∀ x, IsOpen (U x)
  mem_U : ∀ x, x ∈ U x

  φ : X → X → ℝ

namespace LocPot

variable {e : ℕ} {X : Type*} [TopologicalSpace X]

def ofFun (u : X → ℝ) : LocPot X where
  U _ := Set.univ
  isOpen_U _ := isOpen_univ
  mem_U _ := Set.mem_univ _
  φ _ := u

instance : Add (LocPot X) where
  add P Q :=
    { U := fun x => P.U x ∩ Q.U x
      isOpen_U := fun x => (P.isOpen_U x).inter (Q.isOpen_U x)
      mem_U := fun x => ⟨P.mem_U x, Q.mem_U x⟩
      φ := fun x y => P.φ x y + Q.φ x y }

def zsmul (m : ℤ) (P : LocPot X) : LocPot X where
  U := P.U
  isOpen_U := P.isOpen_U
  mem_U := P.mem_U
  φ x y := (m : ℝ) * P.φ x y

def rsmul (c : ℝ) (P : LocPot X) : LocPot X where
  U := P.U
  isOpen_U := P.isOpen_U
  mem_U := P.mem_U
  φ x y := c * P.φ x y

def pullback {Y : Type*} [TopologicalSpace Y] (h : Y → X) (hh : Continuous h) (P : LocPot X) :
    LocPot Y where
  U y := h ⁻¹' P.U (h y)
  isOpen_U y := (P.isOpen_U (h y)).preimage hh
  mem_U y := P.mem_U (h y)
  φ y z := P.φ (h y) (h z)

end LocPot

variable {e : ℕ} {X : Type*} [TopologicalSpace X]

def IsPotential (A : FinHolAtlas e X) (P : LocPot X) : Prop :=
  (∀ x, A.SmoothOn (P.U x) (P.φ x)) ∧
  ∀ x x', ∀ y ∈ P.U x ∩ P.U x', ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ ∃ G : X → ℂ,
    A.HoloOn W G ∧ ∀ z ∈ W ∩ P.U x ∩ P.U x', P.φ x z - P.φ x' z = (G z).re

def IsPsh (A : FinHolAtlas e X) (P : LocPot X) : Prop :=
  ∀ x j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x, ∀ w : Fin e → ℂ,
    0 ≤ levi (P.φ x ∘ (A.chart j).symm) y w

def IsPosPot (A : FinHolAtlas e X) (P : LocPot X) : Prop :=
  ∀ x j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x, ∀ w : Fin e → ℂ, w ≠ 0 →
    0 < levi (P.φ x ∘ (A.chart j).symm) y w

def locDens (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (j : Fin A.n) (y : Fin e → ℂ) : ℝ :=
  maDens (fun i y' => (Φ i).φ ((A.chart j).symm y) ((A.chart j).symm y')) y

structure ChartPartition (A : FinHolAtlas e X) where

  χ : Fin A.n → X → ℝ
  smooth : ∀ j, A.Smooth (χ j)
  nonneg : ∀ j x, 0 ≤ χ j x
  tsupport_subset : ∀ j, tsupport (χ j) ⊆ (A.chart j).source
  sum_eq_one : ∀ x, ∑ j, χ j x = 1

def integralWith (A : FinHolAtlas e X) (P : ChartPartition A) (Φ : Fin e → LocPot X)
    (g : X → ℝ) : ℝ :=
  ∑ j, ∫ y in (A.chart j).target,
    P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y


open scoped Classical in
def mInt (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (g : X → ℝ) : ℝ :=
  by classical exact if h : Nonempty (ChartPartition A) then integralWith A h.some Φ g else 0

def MIntegrable (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (g : X → ℝ) : Prop :=
  ∀ j, ∀ K ⊆ (A.chart j).target, IsCompact K →
    IntegrableOn (fun y => g ((A.chart j).symm y) * locDens A Φ j y) K

def HoloMap {e' : ℕ} {Y : Type*} [TopologicalSpace Y] (B : FinHolAtlas e' Y)
    (A : FinHolAtlas e X) (h : Y → X) : Prop :=
  Continuous h ∧ ∀ j k, AnalyticOnNhd ℂ (A.chart k ∘ h ∘ (B.chart j).symm)
    ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (h ⁻¹' (A.chart k).source))

def IsSection (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) : Prop :=
  (∀ x, A.HoloOn (L.U x) (s x)) ∧
  ∀ x x', ∀ y ∈ L.U x ∩ L.U x',
    ‖s x y‖ * Real.exp (-L.φ x y) = ‖s x' y‖ * Real.exp (-L.φ x' y)

def logNormSec (L : LocPot X) (s : X → X → ℂ) (y : X) : ℝ :=
  Real.log (‖s y y‖ * Real.exp (-L.φ y y))

def IsCompatChart (A : FinHolAtlas e X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) : Prop :=
  ∀ j, AnalyticOnNhd ℂ (ψ ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source) ∧
    AnalyticOnNhd ℂ (A.chart j ∘ ψ.symm) (ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source)

def IsSNC (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) {r : ℕ} (m : Fin r → ℕ)
    (W : Fin r → Set X) : Prop :=
  ∀ x, ∃ ψ : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ ∧ x ∈ ψ.source ∧
    ψ.source ⊆ L.U x ∧ ∃ σ : Fin r → Option (Fin e),
      (∀ k k' i, σ k = some i → σ k' = some i → k = k') ∧
      (∀ k, W k ∩ ψ.source = {y ∈ ψ.source | ∃ i, σ k = some i ∧ ψ y i = 0}) ∧
      ∃ u : X → ℂ, A.HoloOn ψ.source u ∧ (∀ y ∈ ψ.source, u y ≠ 0) ∧
        ∀ y ∈ ψ.source, s x y = u y * ∏ k, (match σ k with
          | some i => ψ y i ^ m k
          | none => 1)

def chartIdx (A : FinHolAtlas e X) (x : X) : Fin A.n := Classical.choose (A.cover x)

def pushDens (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (q : X → Fin e → ℂ) (x : X) : ℝ :=
  locDens A Φ (chartIdx A x) (A.chart (chartIdx A x) x) /
    ‖LinearMap.det (fderiv ℂ (q ∘ (A.chart (chartIdx A x)).symm) (A.chart (chartIdx A x) x) :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2


open scoped Classical in
def maMeasure [MeasurableSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) : Measure X :=
  by classical exact if h : Nonempty (ChartPartition A) then
    ∑ j, ((volume.restrict (A.chart j).target).withDensity fun y =>
      ENNReal.ofReal (h.some.χ j ((A.chart j).symm y) * locDens A Φ j y)).map (A.chart j).symm
  else 0

theorem isPotential_ofFun (A : FinHolAtlas e X) (u : X → ℝ) (hu : A.Smooth u) :
    IsPotential A (LocPot.ofFun u) := by
  refine ⟨fun x => hu, fun x x' y _ => ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => 0,
    fun j => by exact analyticOnNhd_const, fun z _ => by simp [LocPot.ofFun]⟩⟩

end

end ReciprocityTheory.AnForm.M
end
