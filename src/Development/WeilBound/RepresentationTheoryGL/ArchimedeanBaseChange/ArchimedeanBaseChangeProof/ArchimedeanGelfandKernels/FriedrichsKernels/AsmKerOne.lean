module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenseDomainFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevSpacePreserved
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcentrationTimeBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniqueEmbeddingExtension
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothOperatorFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRegularity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelWeightFacts

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusCurveStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functional_calculus_curve : PositivityTheory.RgBcC.Fc.Fcurve := by
  first | exact @GlobalTheory.CompanionTheory.WaveCurve.fcurve | exact GlobalTheory.CompanionTheory.WaveCurve.fcurve | (intros; apply GlobalTheory.CompanionTheory.WaveCurve.fcurve <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsoluteFourierCoefficients
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsoluteFourierCoefficients
noncomputable section

open scoped ZeroAtInfty InnerProductSpace ComplexConjugate
open Complex Filter Topology

namespace GlobalTheory.CompanionTheory.FuncCalc

section Ops

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : Submodule ℂ H} {Ω : M →ₗ[ℂ] M} {T : H →L[ℂ] H}

theorem res_val (h3 : ∀ x : M, ∃ v : M, (v : H) = T x ∧ (v : H) + (Ω (Ω v) : H) = x)
    (x v : M) (hv : (v : H) = T x) : (v : H) + (Ω (Ω v) : H) = x := by
  obtain ⟨v', hv', h⟩ := h3 x
  have : v' = v := Subtype.ext (hv'.trans hv.symm)
  subst this
  exact h

theorem res_symm (hd : Dense (M : Set H)) (hs : ∀ x y : M, ⟪(Ω x : H), y⟫_ℂ = ⟪(x : H), Ω y⟫_ℂ)
    (h3 : ∀ x : M, ∃ v : M, (v : H) = T x ∧ (v : H) + (Ω (Ω v) : H) = x) (x y : H) :
    ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ := by
  have h0 : ∀ x y : M, ⟪T x, (y : H)⟫_ℂ = ⟪(x : H), T y⟫_ℂ := by
    intro x y
    obtain ⟨v, hv, hx⟩ := h3 x
    obtain ⟨u, hu, hy⟩ := h3 y
    rw [← hv, ← hu, ← hy, ← hx, inner_add_right, inner_add_left, hs (Ω v) u, hs v (Ω u)]
  have h1 : ∀ (x : M) (y : H), ⟪T x, y⟫_ℂ = ⟪(x : H), T y⟫_ℂ := fun x =>
    congrFun (Continuous.ext_on hd (f := fun y => ⟪T x, y⟫_ℂ) (g := fun y => ⟪(x : H), T y⟫_ℂ)
      (by fun_prop) (by fun_prop) (fun y hy => h0 x ⟨y, hy⟩))
  exact congrFun (Continuous.ext_on hd (f := fun x => ⟪T x, y⟫_ℂ) (g := fun x => ⟪x, T y⟫_ℂ)
      (by fun_prop) (by fun_prop) (fun x hx => h1 ⟨x, hx⟩ y)) x

theorem res_omega (h3 : ∀ x : M, ∃ v : M, (v : H) = T x ∧ (v : H) + (Ω (Ω v) : H) = x)
    (h4 : ∀ x : M, T ((x : H) + (Ω (Ω x) : H)) = x) (w v : M) (hv : (v : H) = T w) :
    T (Ω w) = Ω v := by
  have hw : w = v + Ω (Ω v) := Subtype.ext (by simpa using (res_val h3 w v hv).symm)
  have := h4 (Ω v)
  rw [hw]
  simpa using this

theorem res_inj (hd : Dense (M : Set H)) (hs : ∀ x y : M, ⟪(Ω x : H), y⟫_ℂ = ⟪(x : H), Ω y⟫_ℂ)
    (h3 : ∀ x : M, ∃ v : M, (v : H) = T x ∧ (v : H) + (Ω (Ω v) : H) = x)
    (h4 : ∀ x : M, T ((x : H) + (Ω (Ω x) : H)) = x) : Function.Injective T := by
  refine (injective_iff_map_eq_zero T).2 fun x hx => ?_
  have h : (fun y => ⟪x, y⟫_ℂ) = fun _ => 0 :=
    Continuous.ext_on hd (by fun_prop) (by fun_prop) (fun y hy => by
      have h1 := h4 ⟨y, hy⟩
      have h2 := res_symm hd hs h3 x ((⟨y, hy⟩ : M) + Ω (Ω ⟨y, hy⟩) : M)
      simp only [Submodule.coe_add] at h2
      rw [h1, hx, inner_zero_left] at h2
      exact h2.symm)
  exact inner_self_eq_zero.1 (congrFun h x)

theorem exists_bdd (hd : Dense (M : Set H)) (hs : ∀ x y : M, ⟪(Ω x : H), y⟫_ℂ = ⟪(x : H), Ω y⟫_ℂ)
    (h3 : ∀ x : M, ∃ v : M, (v : H) = T x ∧ (v : H) + (Ω (Ω v) : H) = x) :
    ∃ Z : H →L[ℂ] H, ∀ x v : M, (v : H) = T x → Z x = (Ω v : H) - I • (v : H) := by
  let T₀ : M →ₗ[ℂ] M := (T.toLinearMap.comp M.subtype).codRestrict M (fun x => by
    obtain ⟨v, hv, _⟩ := h3 x
    simpa [← hv] using v.2)
  have hT₀ : ∀ x : M, ((T₀ x : M) : H) = T x := fun x => rfl
  let Z₀ : M →ₗ[ℂ] H := M.subtype ∘ₗ (Ω - I • LinearMap.id) ∘ₗ T₀
  have hZ₀ : ∀ x : M, Z₀ x = (Ω (T₀ x) : H) - I • ((T₀ x : M) : H) := fun x => by
    simp [Z₀]
  have hb : ∀ x : M, ‖Z₀ x‖ ≤ 1 * ‖x‖ := by
    intro x
    set v := T₀ x with hvdef
    have hx : (v : H) + (Ω (Ω v) : H) = x := res_val h3 x v (hT₀ x)
    have him : (⟪(Ω v : H), (v : H)⟫_ℂ).im = 0 := by
      have h := hs v v
      rw [← inner_conj_symm (v : H) (Ω v : H)] at h
      exact Complex.conj_eq_iff_im.1 h.symm
    have hsq : ‖Z₀ x‖ ^ 2 = ‖(Ω v : H)‖ ^ 2 + ‖(v : H)‖ ^ 2 := by
      rw [hZ₀, ← hvdef, @norm_sub_sq ℂ, norm_smul, inner_smul_right]
      simp [him]
    have hre : (⟪(x : H), (v : H)⟫_ℂ).re = ‖(Ω v : H)‖ ^ 2 + ‖(v : H)‖ ^ 2 := by
      have a1 : ∀ a : H, (⟪a, a⟫_ℂ).re = ‖a‖ ^ 2 := fun a => inner_self_eq_norm_sq (𝕜 := ℂ) a
      rw [← hx, inner_add_left, hs (Ω v) v, Complex.add_re, a1, a1]
      ring
    have hcs : (⟪(x : H), (v : H)⟫_ℂ).re ≤ ‖(x : H)‖ * ‖(v : H)‖ :=
      (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
    have hN0 := norm_nonneg (Z₀ x)
    have hv0 := norm_nonneg (v : H)
    have hx0 := norm_nonneg (x : H)
    have hΩ0 := norm_nonneg (Ω v : H)
    have hvN : ‖(v : H)‖ ≤ ‖Z₀ x‖ := by
      by_contra h
      push_neg at h
      nlinarith
    rw [one_mul]
    change ‖Z₀ x‖ ≤ ‖(x : H)‖
    by_contra h
    push_neg at h
    nlinarith
  let Z₁ : M →L[ℂ] H := Z₀.mkContinuous 1 hb
  refine ⟨Z₁.extend M.subtypeL, fun x v hv => ?_⟩
  have h := Z₁.extend_eq (e := M.subtypeL) (by simpa using hd.denseRange_val) isUniformEmbedding_subtype_val.isUniformInducing x
  have hv' : T₀ x = v := Subtype.ext hv.symm
  simp only [Submodule.subtypeL_apply] at h
  rw [h]
  simp [Z₁, hZ₀, hv']

end Ops

section Ops2

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : Submodule ℂ H} {Ω : M →ₗ[ℂ] M} {T : H →L[ℂ] H}

theorem bdd_adjoint (hd : Dense (M : Set H)) (hs : ∀ x y : M, ⟪(Ω x : H), y⟫_ℂ = ⟪(x : H), Ω y⟫_ℂ)
    (h3 : ∀ x : M, ∃ v : M, (v : H) = T x ∧ (v : H) + (Ω (Ω v) : H) = x)
    (h4 : ∀ x : M, T ((x : H) + (Ω (Ω x) : H)) = x) (Z : H →L[ℂ] H)
    (hZ : ∀ x v : M, (v : H) = T x → Z x = (Ω v : H) - I • (v : H)) (x v : M) (hv : (v : H) = T x) :
    ContinuousLinearMap.adjoint Z x = (Ω v : H) + I • (v : H) := by
  refine ext_inner_left ℂ fun y => ?_
  have h : (fun y => ⟪y, ContinuousLinearMap.adjoint Z x⟫_ℂ) =
      fun y => ⟪y, (Ω v : H) + I • (v : H)⟫_ℂ := by
    refine Continuous.ext_on hd (by fun_prop) (by fun_prop) (fun y hy => ?_)
    obtain ⟨u, hu, -⟩ := h3 ⟨y, hy⟩
    have e1 : ⟪(u : H), (x : H)⟫_ℂ = ⟪y, (v : H)⟫_ℂ := by
      rw [hu, hv]
      exact res_symm hd hs h3 _ _
    have e2 : ⟪(Ω u : H), (x : H)⟫_ℂ = ⟪y, (Ω v : H)⟫_ℂ := by
      rw [hs, hu, ← res_omega h3 h4 x v hv]
      exact res_symm hd hs h3 _ _
    simp only [ContinuousLinearMap.adjoint_inner_right]
    rw [hZ ⟨y, hy⟩ u hu, inner_sub_left, inner_smul_left, inner_add_right, inner_smul_right, e1, e2]
    simp
  exact congrFun h y

theorem bdd_mul (hd : Dense (M : Set H)) (hs : ∀ x y : M, ⟪(Ω x : H), y⟫_ℂ = ⟪(x : H), Ω y⟫_ℂ)
    (h3 : ∀ x : M, ∃ v : M, (v : H) = T x ∧ (v : H) + (Ω (Ω v) : H) = x)
    (h4 : ∀ x : M, T ((x : H) + (Ω (Ω x) : H)) = x) (Z : H →L[ℂ] H)
    (hZ : ∀ x v : M, (v : H) = T x → Z x = (Ω v : H) - I • (v : H)) :
    ContinuousLinearMap.adjoint Z * Z = T ∧ Z * ContinuousLinearMap.adjoint Z = T ∧
      Z - ContinuousLinearMap.adjoint Z = (-2 * I) • T := by
  have hA := bdd_adjoint hd hs h3 h4 Z hZ
  have key : ∀ (S : H →L[ℂ] H), (∀ x : M, S x = T x) → S = T := fun S h =>
    ContinuousLinearMap.coeFn_injective (Continuous.ext_on hd S.continuous T.continuous
      (fun x hx => h ⟨x, hx⟩))
  refine ⟨key _ fun x => ?_, key _ fun x => ?_, ?_⟩
  · obtain ⟨v, hv, -⟩ := h3 x
    obtain ⟨u, hu, hvu⟩ := h3 v
    have hTa : ((Ω u - I • u : M) : H) = T ((Ω v - I • v : M) : H) := by
      simp [← res_omega h3 h4 v u hu, hu]
    have h1 : Z x = ((Ω v - I • v : M) : H) := by simpa using hZ x v hv
    rw [ContinuousLinearMap.mul_apply, h1, hA _ _ hTa, ← hv, ← hvu]
    simp only [map_sub, map_smul, Submodule.coe_sub, Submodule.coe_smul]
    have : I • I • (u : H) = -(u : H) := by rw [smul_smul]; simp
    rw [smul_sub, this]
    abel
  · obtain ⟨v, hv, -⟩ := h3 x
    obtain ⟨u, hu, hvu⟩ := h3 v
    have hTa : ((Ω u + I • u : M) : H) = T ((Ω v + I • v : M) : H) := by
      simp [← res_omega h3 h4 v u hu, hu]
    have h1 : ContinuousLinearMap.adjoint Z x = ((Ω v + I • v : M) : H) := by simpa using hA x v hv
    rw [ContinuousLinearMap.mul_apply, h1, hZ _ _ hTa, ← hv, ← hvu]
    simp only [map_add (f := _), map_smul, Submodule.coe_add, Submodule.coe_smul]
    have : I • I • (u : H) = -(u : H) := by rw [smul_smul]; simp
    rw [smul_add, this]
    abel
  · refine ContinuousLinearMap.coeFn_injective (Continuous.ext_on hd (by fun_prop) (by fun_prop)
      (fun x hx => ?_))
    obtain ⟨v, hv, -⟩ := h3 ⟨x, hx⟩
    have a := hZ ⟨x, hx⟩ v hv
    have b := hA ⟨x, hx⟩ v hv
    simp only [] at a b
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, a, b]
    rw [← hv.trans rfl]
    module

theorem bdd_omega (hd : Dense (M : Set H)) (hs : ∀ x y : M, ⟪(Ω x : H), y⟫_ℂ = ⟪(x : H), Ω y⟫_ℂ)
    (h3 : ∀ x : M, ∃ v : M, (v : H) = T x ∧ (v : H) + (Ω (Ω v) : H) = x)
    (h4 : ∀ x : M, T ((x : H) + (Ω (Ω x) : H)) = x) (Z : H →L[ℂ] H)
    (hZ : ∀ x v : M, (v : H) = T x → Z x = (Ω v : H) - I • (v : H)) (v : M) :
    Z ((Ω v : H) + I • (v : H)) = v := by
  have hA := bdd_adjoint hd hs h3 h4 Z hZ (v + Ω (Ω v)) v (by simpa using (h4 v).symm)
  have h2 := (bdd_mul hd hs h3 h4 Z hZ).2.1
  rw [← hA, ← ContinuousLinearMap.mul_apply, h2]
  simpa using h4 v

theorem bdd_comm (hd : Dense (M : Set H)) (hs : ∀ x y : M, ⟪(Ω x : H), y⟫_ℂ = ⟪(x : H), Ω y⟫_ℂ)
    (h3 : ∀ x : M, ∃ v : M, (v : H) = T x ∧ (v : H) + (Ω (Ω v) : H) = x)
    (h4 : ∀ x : M, T ((x : H) + (Ω (Ω x) : H)) = x) (Z : H →L[ℂ] H)
    (hZ : ∀ x v : M, (v : H) = T x → Z x = (Ω v : H) - I • (v : H)) (S : H →L[ℂ] H)
    (hS : ∀ x : M, ∃ v : M, (v : H) = S x ∧ (Ω v : H) = S (Ω x)) :
    Commute Z S ∧ Commute (ContinuousLinearMap.adjoint Z) S := by
  have hA := bdd_adjoint hd hs h3 h4 Z hZ
  have hST : ∀ (x p v s : M), (p : H) = S x → (v : H) = T x → (s : H) = S v → (s : H) = T p := by
    intro x p v s hp hv hs'
    obtain ⟨s', hs1, hs2⟩ := hS v
    have hss : s' = s := Subtype.ext (hs1.trans hs'.symm)
    subst hss
    obtain ⟨t, ht1, ht2⟩ := hS (Ω v)
    have hts : t = Ω s' := Subtype.ext (ht1.trans hs2.symm)
    subst hts
    have hx := res_val h3 x v hv
    have : (p : H) = (s' : H) + Ω (Ω s') := by
      rw [hp, ← hx, map_add (f := _), ← hs1, ht2]
    have h5 := h4 s'
    rw [← this] at h5
    exact h5.symm
  have key : ∀ (A B : H →L[ℂ] H), (∀ x : M, A x = B x) → A = B := fun A B h =>
    ContinuousLinearMap.coeFn_injective (Continuous.ext_on hd A.continuous B.continuous
      (fun x hx => h ⟨x, hx⟩))
  constructor
  · refine key _ _ fun x => ?_
    obtain ⟨v, hv, -⟩ := h3 x
    obtain ⟨p, hp, -⟩ := hS x
    obtain ⟨s, hs1, hs2⟩ := hS v
    have := hST x p v s hp hv hs1
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, ← hp, hZ _ _ this, hZ _ _ hv,
      map_sub, map_smul, hs2, hs1]
  · refine key _ _ fun x => ?_
    obtain ⟨v, hv, -⟩ := h3 x
    obtain ⟨p, hp, -⟩ := hS x
    obtain ⟨s, hs1, hs2⟩ := hS v
    have := hST x p v s hp hv hs1
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, ← hp, hA _ _ this, hA _ _ hv,
      map_add, map_smul, hs2, hs1]

end Ops2

section Calc

variable {A : Type*} [CStarAlgebra A]

def yOf (z : ℂ) : ℝ := (z⁻¹).re

def lift (g : C₀(ℝ, ℂ)) (z : ℂ) : ℂ := if z = 0 then 0 else g (yOf z)

theorem circ_inv {z : ℂ} (hz : z ≠ 0) (h : z - conj z = (-2 * I) * (conj z * z)) :
    z⁻¹ = (yOf z : ℂ) + I := by
  have hc : conj z ≠ 0 := (map_ne_zero _).2 hz
  have h1 : z⁻¹ - conj z⁻¹ = 2 * I := by
    rw [map_inv₀]
    field_simp
    linear_combination -h
  have h2 : (z⁻¹).im = 1 := by
    rw [Complex.sub_conj] at h1
    have := congrArg Complex.im h1
    simpa using this
  apply Complex.ext
  · simp [yOf]
  · simpa using h2

theorem spec_circle (Z : A) (hn : IsStarNormal Z)
    (hsp : Z - star Z = (-2 * I) • (star Z * Z)) :
    ∀ z ∈ spectrum ℂ Z, z - conj z = (-2 * I) * (conj z * z) := by
  have hcj : ContinuousOn (fun z : ℂ => conj z) (spectrum ℂ Z) := Complex.continuous_conj.continuousOn
  have h1 : cfc (fun z : ℂ => conj z) Z = star Z := cfc_star_id (R := ℂ) Z
  have h2 : cfc (fun z : ℂ => z) Z = Z := cfc_id' ℂ Z
  have e1 : cfc (fun z : ℂ => z - conj z) Z = Z - star Z := by
    rw [cfc_sub (fun z : ℂ => z) (fun z : ℂ => conj z) Z continuousOn_id hcj, h1, h2]
  have e2 : cfc (fun z : ℂ => (-2 * I) * (conj z * z)) Z = (-2 * I) • (star Z * Z) := by
    rw [cfc_const_mul (-2 * I) (fun z : ℂ => conj z * z) Z (hcj.mul continuousOn_id),
      cfc_mul (fun z : ℂ => conj z) (fun z : ℂ => z) Z hcj continuousOn_id, h1, h2]
  have h := (cfc_eq_cfc_iff_eqOn (R := ℂ) (a := Z) (f := fun z : ℂ => z - conj z)
    (g := fun z : ℂ => (-2 * I) * (conj z * z)) hn (continuousOn_id.sub hcj)
    (continuousOn_const.mul (hcj.mul continuousOn_id))).1 (by rw [e1, e2, hsp])
  exact fun z hz => h hz

theorem tendsto_yOf (K : Set ℂ) (hK : ∀ z ∈ K, z - conj z = (-2 * I) * (conj z * z)) :
    Tendsto yOf (𝓝[K \ {0}] 0) (cocompact ℝ) := by
  rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
  have h1 : Tendsto (fun z : ℂ => z⁻¹) (𝓝[K \ {0}] 0) (Bornology.cobounded ℂ) :=
    tendsto_inv₀_nhdsNE_zero.mono_left (nhdsWithin_mono _ fun z hz => hz.2)
  have h2 : Tendsto (fun z : ℂ => ‖z⁻¹‖ - 1) (𝓝[K \ {0}] 0) atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_norm_atTop_iff_cobounded.2 h1)
  refine tendsto_atTop_mono' _ ?_ h2
  filter_upwards [self_mem_nhdsWithin] with z hz
  have h3 := circ_inv (by simpa using hz.2) (hK z hz.1)
  have h4 : ‖z⁻¹‖ ≤ ‖yOf z‖ + 1 := by
    rw [h3]
    refine (norm_add_le _ _).trans ?_
    simp
  linarith

theorem lift_cont (K : Set ℂ) (hK : ∀ z ∈ K, z - conj z = (-2 * I) * (conj z * z))
    (g : C₀(ℝ, ℂ)) : ContinuousOn (lift g) K := by
  intro z0 hz0
  by_cases h0 : z0 = 0
  · subst h0
    rw [← continuousWithinAt_diff_self]
    have h1 : Tendsto (fun z => g (yOf z)) (𝓝[K \ {0}] 0) (𝓝 0) :=
      g.zero_at_infty'.comp (tendsto_yOf K hK)
    have h2 : lift g 0 = 0 := by simp [lift]
    rw [ContinuousWithinAt, h2]
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have : z ≠ 0 := by simpa using hz.2
    simp [lift, this]
  · have h1 : lift g =ᶠ[𝓝 z0] fun z => g (yOf z) := by
      filter_upwards [eventually_ne_nhds h0] with z hz
      simp [lift, hz]
    have h2 : ContinuousAt (fun z => g (yOf z)) z0 :=
      g.continuous.continuousAt.comp
        (Complex.continuous_re.continuousAt.comp (continuousAt_inv₀ h0))
    exact (h2.congr h1.symm).continuousWithinAt

theorem lift_norm_le (g : C₀(ℝ, ℂ)) (z : ℂ) : ‖lift g z‖ ≤ ‖g‖ := by
  unfold lift
  split_ifs
  · simp
  · rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    exact g.toBCF.norm_coe_le_norm _

theorem abs_calc (Z : A) (hn : IsStarNormal Z) (hsp : Z - star Z = (-2 * I) • (star Z * Z)) :
    ∃ Φ : C₀(ℝ, ℂ) →L[ℂ] A, (∀ g h, Φ (g * h) = Φ g * Φ h) ∧ (∀ g, Φ (star g) = star (Φ g)) ∧
      (∀ g, ‖Φ g‖ ≤ ‖g‖) ∧
      (∀ g : C₀(ℝ, ℂ), (∀ y, g y = ((1 + y ^ 2)⁻¹ : ℝ)) → Φ g = star Z * Z) ∧
      (∀ g h : C₀(ℝ, ℂ), (∀ y, h y = y * g y) → Z * (Φ h + I • Φ g) = Φ g) ∧
      (∀ S : A, Commute Z S → Commute (star Z) S → ∀ g, Commute (Φ g) S) := by
  have hK := spec_circle Z hn hsp
  have hc : ∀ g, ContinuousOn (lift g) (spectrum ℂ Z) := lift_cont _ hK
  have hcj : ContinuousOn (fun z : ℂ => conj z) (spectrum ℂ Z) := Complex.continuous_conj.continuousOn
  have hb : ∀ g, ‖cfc (lift g) Z‖ ≤ ‖g‖ := fun g =>
    norm_cfc_le (norm_nonneg g) fun z _ => lift_norm_le g z
  let L : C₀(ℝ, ℂ) →ₗ[ℂ] A :=
    { toFun := fun g => cfc (lift g) Z
      map_add' := fun g h => by
        rw [← cfc_add Z (lift g) (lift h) (hc g) (hc h)]
        congr 1
        funext z
        by_cases hz : z = 0 <;> simp [lift, hz]
      map_smul' := fun c g => by
        rw [RingHom.id_apply, ← cfc_smul c (lift g) Z (hc g)]
        congr 1
        funext z
        by_cases hz : z = 0 <;> simp [lift, hz] }
  have hL : ∀ g, L g = cfc (lift g) Z := fun g => rfl
  refine ⟨L.mkContinuous 1 (fun g => by rw [hL, one_mul]; exact hb g), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g h
    simp only [LinearMap.mkContinuous_apply, hL]
    rw [← cfc_mul (lift g) (lift h) Z (hc g) (hc h)]
    congr 1
    funext z
    by_cases hz : z = 0 <;> simp [lift, hz]
  · intro g
    simp only [LinearMap.mkContinuous_apply, hL]
    rw [← cfc_star (lift g) Z]
    congr 1
    funext z
    by_cases hz : z = 0 <;> simp [lift, hz]
  · intro g
    exact hb g
  · intro g hg
    simp only [LinearMap.mkContinuous_apply, hL]
    have h1 : cfc (fun z : ℂ => conj z * z) Z = star Z * Z := by
      rw [cfc_mul (fun z : ℂ => conj z) (fun z : ℂ => z) Z hcj continuousOn_id,
        show cfc (fun z : ℂ => conj z) Z = star Z from cfc_star_id (R := ℂ) Z, cfc_id' ℂ Z]
    rw [← h1]
    refine cfc_congr fun z hz => ?_
    by_cases h0 : z = 0
    · simp [lift, h0]
    · have h3 := circ_inv h0 (hK z hz)
      have hc0 : conj z ≠ 0 := (map_ne_zero _).2 h0
      have h4 : conj z⁻¹ = (yOf z : ℂ) - I := by
        rw [h3]
        simp [sub_eq_add_neg]
      have h5 : ((1 + (yOf z) ^ 2 : ℝ) : ℂ) = z⁻¹ * conj z⁻¹ := by
        rw [h4, h3]
        push_cast
        ring_nf
        simp
        ring
      simp only [lift, h0, if_false, hg]
      rw [Complex.ofReal_inv, h5, map_inv₀]
      field_simp
  · intro g h hh
    simp only [LinearMap.mkContinuous_apply, hL]
    have h1 : Z * (cfc (lift h) Z + I • cfc (lift g) Z) =
        cfc (fun z : ℂ => z * (lift h z + I • lift g z)) Z := by
      rw [cfc_mul (fun z : ℂ => z) (fun z : ℂ => lift h z + I • lift g z) Z continuousOn_id
        ((hc h).add ((hc g).const_smul I)), cfc_id' ℂ Z,
        cfc_add Z (lift h) (fun z : ℂ => I • lift g z) (hc h) ((hc g).const_smul I),
        cfc_smul I (lift g) Z (hc g)]
    rw [h1]
    refine cfc_congr fun z hz => ?_
    by_cases h0 : z = 0
    · simp [lift, h0]
    · have h3 := circ_inv h0 (hK z hz)
      simp only [lift, h0, if_false, hh, smul_eq_mul]
      have h4 : z * ((yOf z : ℂ) + I) = 1 := by
        rw [← h3]
        exact mul_inv_cancel₀ h0
      linear_combination (g (yOf z)) * h4
  · intro S h1 h2 g
    simp only [LinearMap.mkContinuous_apply, hL]
    exact Commute.cfc (𝕜 := ℂ) h1 h2 _

end Calc

theorem absFC : PositivityTheory.RgBcC.Fc.AbsFC := by
  intro H _ _ _ M Ω T hd hs h3 h4
  obtain ⟨Z, hZ⟩ := exists_bdd hd hs h3
  obtain ⟨m1, m2, m3⟩ := bdd_mul hd hs h3 h4 Z hZ
  have hstar : star Z = ContinuousLinearMap.adjoint Z := ContinuousLinearMap.star_eq_adjoint Z
  have hn : IsStarNormal Z := ⟨by
    change star Z * Z = Z * star Z
    rw [hstar, m1, m2]⟩
  have hsp : Z - star Z = (-2 * I) • (star Z * Z) := by rw [hstar, m1, m3]
  obtain ⟨Φ, p1, p2, p3, p4, p5, p6⟩ := abs_calc Z hn hsp
  have hinj : Function.Injective Z := fun x y hxy => res_inj hd hs h3 h4 (by
    rw [← m1, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hxy])
  refine ⟨⟨Φ, p1, fun g => ?_, p3, fun g hg => ?_, ?_, ?_⟩⟩
  · rw [p2, ContinuousLinearMap.star_eq_adjoint]
  · rw [p4 g hg, hstar, m1]
  · intro g h hh x v hv
    have e1 := congrArg (fun A : H →L[ℂ] H => A x) (p5 g h hh)
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ← hv] at e1
    have e2 := bdd_omega hd hs h3 h4 Z hZ v
    have e3 := hinj (e1.trans e2.symm)
    exact (add_right_cancel e3).symm
  · intro S hS g
    obtain ⟨c1, c2⟩ := bdd_comm hd hs h3 h4 Z hZ S hS
    exact (p6 S c1 (hstar ▸ c2) g).eq.symm

end GlobalTheory.CompanionTheory.FuncCalc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsoluteFourierCoefficientsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absolute_fourier_coefficients : PositivityTheory.RgBcC.Fc.AbsFC := by
  first | exact @GlobalTheory.CompanionTheory.FuncCalc.absFC | exact GlobalTheory.CompanionTheory.FuncCalc.absFC | (intros; apply GlobalTheory.CompanionTheory.FuncCalc.absFC <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsoluteCutoffBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsoluteCutoffBound
noncomputable section

open Filter Topology
open scoped ZeroAtInfty InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.FcCut

open PositivityTheory.RgBcC.Fc

def mulC (a : ℝ → ℂ) (ha : Continuous a) (f : C₀(ℝ, ℂ)) (R : ℝ) (hf : ∀ y, R ≤ |y| → a y * f y = 0) :
    C₀(ℝ, ℂ) :=
  ⟨⟨fun y => a y * f y, ha.mul f.continuous⟩, by
    have hK : (Set.Icc (-R) R)ᶜ ∈ cocompact ℝ := isCompact_Icc.compl_mem_cocompact
    refine (tendsto_const_nhds (x := (0 : ℂ))).congr' ?_
    filter_upwards [hK] with y hy
    have hR : R ≤ |y| := by
      by_contra hlt
      push_neg at hlt
      exact hy ⟨(abs_lt.mp hlt).1.le, (abs_lt.mp hlt).2.le⟩
    show (0 : ℂ) = a y * f y
    rw [hf y hR]⟩

@[simp] theorem mulC_apply (a : ℝ → ℂ) (ha : Continuous a) (f : C₀(ℝ, ℂ)) (R : ℝ)
    (hf : ∀ y, R ≤ |y| → a y * f y = 0) (y : ℝ) : mulC a ha f R hf y = a y * f y := rfl

section Core

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : Submodule ℂ H} {Ω : M →ₗ[ℂ] M} {T : H →L[ℂ] H}

theorem inner_star_mul (F : FCalc H M Ω T) (x : H) (a b : C₀(ℝ, ℂ)) :
    ⟪F.Φ (star a * b) x, x⟫_ℂ = ⟪F.Φ b x, F.Φ a x⟫_ℂ := by
  rw [F.map_mul, F.map_star, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.adjoint_inner_left]

theorem core (F : FCalc H M Ω T) (c : ℝ) (x : H)
    (hyp : ∀ g, ∃ v : M, (v : H) = F.Φ g x ∧ (⟪(Ω v : H), v⟫_ℂ).re ≤ c * ‖(v : H)‖ ^ 2)
    (f : C₀(ℝ, ℂ)) (δ R : ℝ) (hδ : 0 < δ) (h1 : ∀ y, y ≤ c + δ → f y = 0)
    (h2 : ∀ y, R ≤ |y| → f y = 0) : F.Φ f x = 0 := by
  let h := mulC (fun y => (y : ℂ)) Complex.continuous_ofReal f R
    (fun y hy => by rw [h2 y hy, mul_zero])
  let r := mulC (fun y => ((Real.sqrt (max (y - c - δ) 0) : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (by fun_prop)) f R (fun y hy => by rw [h2 y hy, mul_zero])
  obtain ⟨v, hv, hle⟩ := hyp f
  have hΩ : (Ω v : H) = F.Φ h x := F.omega f h (fun y => rfl) x v hv
  have hid : star r * r = star f * h - ((c + δ : ℝ) : ℂ) • (star f * f) := by
    ext y
    by_cases hy : y ≤ c + δ
    · simp [r, h, h1 y hy]
    · have hpos : 0 ≤ y - c - δ := by linarith [not_le.mp hy]
      have hs : ((Real.sqrt (y - c - δ) : ℝ) : ℂ) * ((Real.sqrt (y - c - δ) : ℝ) : ℂ)
          = (y : ℂ) - c - δ := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt hpos]; push_cast; ring
      simp only [r, h, ZeroAtInftyContinuousMap.coe_mul, ZeroAtInftyContinuousMap.coe_star,
        ZeroAtInftyContinuousMap.coe_sub, ZeroAtInftyContinuousMap.coe_smul, Pi.mul_apply, Pi.star_apply,
        Pi.sub_apply, Pi.smul_apply, mulC_apply, max_eq_left hpos, star_mul', smul_eq_mul]
      simp only [Complex.star_def, Complex.conj_ofReal]
      push_cast
      linear_combination ((starRingEnd ℂ) (f y) * f y) * hs
  have e : ((‖F.Φ r x‖ ^ 2 : ℝ) : ℂ) = ⟪(Ω v : H), v⟫_ℂ - ((c + δ : ℝ) : ℂ) * ((‖(v : H)‖ ^ 2 : ℝ) : ℂ) := by
    have a1 := inner_star_mul F x r r
    have a2 := inner_star_mul F x f h
    have a3 := inner_star_mul F x f f
    rw [hid, map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      inner_sub_left, inner_smul_left, a2, a3, Complex.conj_ofReal,
      inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at a1
    rw [hΩ, hv]
    push_cast
    simpa using a1.symm
  have e' := congrArg Complex.re e
  rw [Complex.ofReal_re, Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re] at e'
  have hn : ‖(v : H)‖ ^ 2 ≤ 0 := by
    have p1 : 0 ≤ ‖F.Φ r x‖ ^ 2 := by positivity
    nlinarith
  have hv0 : ‖(v : H)‖ = 0 := by
    have := sq_nonneg ‖(v : H)‖
    exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm hn this)
  rw [← hv]
  exact norm_eq_zero.mp hv0

theorem approx (c : ℝ) (g : C₀(ℝ, ℂ)) (hg : ∀ y, y ≤ c → g y = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ (f : C₀(ℝ, ℂ)) (δ R : ℝ), 0 < δ ∧ (∀ y, y ≤ c + δ → f y = 0) ∧ (∀ y, R ≤ |y| → f y = 0) ∧
      ‖g - f‖ ≤ 2 * ε := by

  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ y, R ≤ |y| → ‖g y‖ ≤ ε := by
    have ht : Tendsto g (cocompact ℝ) (𝓝 0) := g.zero_at_infty'
    have hm : {y | ‖g y‖ < ε} ∈ cocompact ℝ := by
      have := ht (Metric.ball_mem_nhds (0 : ℂ) hε)
      simpa [Metric.ball, dist_zero_right] using this
    obtain ⟨t, ht1, ht2⟩ := Filter.mem_cocompact.mp hm
    obtain ⟨r, hr⟩ := ht1.isBounded.subset_closedBall (0 : ℝ)
    refine ⟨r + 1, fun y hy => ?_⟩
    have hyt : y ∈ tᶜ := fun hyt => by
      have := hr hyt
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      linarith
    exact (ht2 hyt).le

  obtain ⟨δ, hδ, hδc⟩ : ∃ δ > 0, ∀ y, y ≤ c + δ → ‖g y‖ ≤ ε := by
    obtain ⟨d, hd, hdc⟩ := Metric.continuous_iff.mp g.continuous c ε hε
    refine ⟨d / 2, by positivity, fun y hy => ?_⟩
    by_cases hyc : y ≤ c
    · rw [hg y hyc, norm_zero]; exact hε.le
    · have : dist y c < d := by
        rw [Real.dist_eq, abs_of_pos (by linarith [not_le.mp hyc])]
        linarith
      have h3 : dist (g y) (g c) < ε := hdc y this
      rw [hg c le_rfl, dist_zero_right] at h3
      exact h3.le
  let m : ℝ → ℝ := fun y => min 1 (max 0 (‖g y‖ / ε - 1))
  have hm0 : ∀ y, ‖g y‖ ≤ ε → m y = 0 := fun y hy => by
    have : ‖g y‖ / ε - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one hε]; exact hy
    simp only [m, max_eq_left this]
    exact min_eq_right zero_le_one
  have hmc : Continuous m := by
    have := g.continuous
    fun_prop
  let f := mulC (fun y => (m y : ℂ)) (Complex.continuous_ofReal.comp hmc) g R
    (fun y hy => by rw [hm0 y (hR y hy)]; simp)
  refine ⟨f, δ, R, hδ, fun y hy => ?_, fun y hy => ?_, ?_⟩
  · simp [f, hm0 y (hδc y hy)]
  · simp [f, hm0 y (hR y hy)]
  · rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    refine (BoundedContinuousFunction.norm_le (by positivity)).mpr fun y => ?_
    have hy : (g - f).toBCF y = (1 - (m y : ℂ)) * g y := by
      show g y - (m y : ℂ) * g y = _
      ring
    rw [hy, norm_mul]
    have hm1 : m y ≤ 1 := min_le_left _ _
    have hm2 : 0 ≤ m y := le_min zero_le_one (le_max_left _ _)
    have hn : ‖(1 - (m y : ℂ))‖ = 1 - m y := by
      have : (1 - (m y : ℂ)) = ((1 - m y : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    rw [hn]
    by_cases hb : 2 * ε ≤ ‖g y‖
    · have : m y = 1 := by
        have h1 : 1 ≤ ‖g y‖ / ε - 1 := by
          have : 2 ≤ ‖g y‖ / ε := by rw [le_div_iff₀ hε]; exact hb
          linarith
        exact min_eq_left (h1.trans (le_max_right _ _))
      rw [this]; simp; positivity
    · have hgy := (not_le.mp hb).le
      have : 0 ≤ ‖g y‖ := norm_nonneg _
      nlinarith

theorem absCut : AbsCut := by
  intro H _ _ _ M Ω T F c x hyp g hg
  refine norm_eq_zero.mp (le_antisymm (le_of_forall_pos_le_add fun e he => ?_) (norm_nonneg _))
  have hx : 0 < ‖x‖ + 1 := by positivity
  obtain ⟨f, δ, R, hδ, h1, h2, hfg⟩ := approx c g hg (e / (2 * (‖x‖ + 1))) (by positivity)
  have hz := core F c x hyp f δ R hδ h1 h2
  have hsplit : F.Φ g x = F.Φ (g - f) x := by
    rw [map_sub, ContinuousLinearMap.sub_apply, hz, sub_zero]
  have hb : ‖F.Φ (g - f) x‖ ≤ 2 * (e / (2 * (‖x‖ + 1))) * ‖x‖ :=
    ((F.Φ (g - f)).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right ((F.norm_le _).trans hfg) (norm_nonneg _))
  have hc : 2 * (e / (2 * (‖x‖ + 1))) * ‖x‖ ≤ e := by
    have : 2 * (e / (2 * (‖x‖ + 1))) * ‖x‖ = e * (‖x‖ / (‖x‖ + 1)) := by
      field_simp
    rw [this]
    have : ‖x‖ / (‖x‖ + 1) ≤ 1 := by
      rw [div_le_one hx]; linarith
    nlinarith
  rw [hsplit]
  linarith

end Core

end GlobalTheory.CompanionTheory.FcCut
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsoluteCutoffBoundStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absolute_cutoff_bound : PositivityTheory.RgBcC.Fc.AbsCut := by
  first | exact @GlobalTheory.CompanionTheory.FcCut.absCut | exact GlobalTheory.CompanionTheory.FcCut.absCut | (intros; apply GlobalTheory.CompanionTheory.FcCut.absCut <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactSobolevEmbedding
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactSobolevEmbedding
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.CptSobProof

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def Van {V : Type} [Zero V] (R : ℝ) (f : Mat n → V) : Prop := ∀ y ∈ GLs n, R < lg y → f y = 0

theorem isOpen_GLs : IsOpen (GLs n) := by
  have h : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage h

theorem val_mem_GLs (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem isOpen_far (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (R : ℝ) :
    IsOpen {y : Mat n | y ∈ GLs n ∧ R < lg y} := by
  have h := hlg.isOpen_inter_preimage isOpen_GLs (isOpen_Ioi (a := R))
  exact h

section Vanish

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {R : ℝ} {f : Mat n → V}

theorem Van.rd (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) (X : Mat n) : Van R (Rd X f) := by
  intro y hy hR
  have he : f =ᶠ[𝓝 y] fun _ => (0 : V) := by
    filter_upwards [(isOpen_far hlg R).mem_nhds ⟨hy, hR⟩] with z hz using h z hz.1 hz.2
  simp [Rd, he.fderiv_eq]

theorem Van.eu (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) (s : Bool) (a b : Fin n) :
    Van R (Eu s a b f) := by
  intro y hy hR
  have h1 := h.rd hlg (Matrix.single a b 1) y hy hR
  have h2 := h.rd hlg (Matrix.single a b Complex.I) y hy hR
  cases s <;> simp [Eu, h1, h2]

theorem Van.epow (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) (s : Bool) (m : ℕ) (a b : Fin n) :
    Van R (Epow s m a b f) := by
  induction m generalizing a b with
  | zero =>
    intro y hy hR
    by_cases hab : a = b
    · simp [Epow, hab, h y hy hR]
    · simp [Epow, hab]
  | succ m ih =>
    intro y hy hR
    simp only [Epow, Finset.sum_apply]
    exact Finset.sum_eq_zero fun c _ => (ih c b).eu hlg s a c y hy hR

theorem Van.gel (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) (s : Bool) (m : ℕ) :
    Van R (gel s m f) := by
  intro y hy hR
  simp only [PositivityTheory.RgBcC.gel, Finset.sum_apply]
  exact Finset.sum_eq_zero fun a _ => h.epow hlg s m a a y hy hR

theorem Van.om (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) : Van R (Om f) := by
  intro y hy hR
  have h1 := h.gel hlg true 2 y hy hR
  have h2 := h.gel hlg false 2 y hy hR
  simp [Om, h1, h2]

theorem Van.rw (hlg : ContinuousOn (lg : Mat n → ℝ) (GLs n)) (h : Van R f) (w : List (Bool × Fin n × Fin n)) :
    Van R (Rw w f) := by
  induction w with
  | nil => exact h
  | cons p w ih => exact ih.rd hlg (bs p)

theorem rw_smooth (hC : RCalc) (hf : ContDiffOn ℝ ∞ f (GLs n)) (w : List (Bool × Fin n × Fin n)) :
    ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact ((hC n).1 V _ ih).1 (bs p)

end Vanish

theorem memLp_of_van [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {R : ℝ} {g : Mat n → V}
    (hK : IsCompact {y : G n | lg y.val ≤ R}) (hc : ContinuousOn g (GLs n)) (hv : Van R g) :
    MemLp (fun y : G n => g y.val) 2 μ := by
  have hcont : Continuous (fun y : G n => g y.val) :=
    hc.comp_continuous Units.continuous_val val_mem_GLs
  have hsupp : HasCompactSupport (fun y : G n => g y.val) :=
    HasCompactSupport.intro hK fun y hy => hv y.val (val_mem_GLs y) (not_le.1 hy)
  exact hcont.memLp_of_hasCompactSupport hsupp

theorem cptSob : CptSob := by
  intro n _ _ μ _ V _ _ hL hC f hf hcpt
  obtain ⟨-, -, -, hs, hk, -⟩ := hL n
  obtain ⟨R, hR⟩ := hcpt
  have hv : Van R f := hR
  exact ⟨⟨hf, fun w => memLp_of_van μ (hk R) (rw_smooth hC hf w).continuousOn (hv.rw hs.continuousOn w)⟩,
    R, hv.om hs.continuousOn⟩

end GlobalTheory.CompanionTheory.CptSobProof
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactSobolevEmbeddingStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_sobolev_embedding : PositivityTheory.RgBcC.Fc.CptSob := by
  first | exact @GlobalTheory.CompanionTheory.CptSobProof.cptSob | exact GlobalTheory.CompanionTheory.CptSobProof.cptSob | (intros; apply GlobalTheory.CompanionTheory.CptSobProof.cptSob <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WvAlg
namespace GlobalTheory.CompanionTheory.WaveFc

open PositivityTheory.RgBcC.Fc

theorem wvAlg : WvAlg := by
  intro c N t y
  have hsq : ((y : ℂ) ^ (1 / 2 : ℂ)) ^ 2 = y := by
    rw [← Complex.cpow_nat_mul]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h2 : Even 2 := ⟨1, rfl⟩
    have h0 : Even 0 := ⟨0, rfl⟩
    simp only [PositivityTheory.RgBcC.Fc.wv, PositivityTheory.RgBcC.Fc.chj, h2, h0, if_true, hsq, pow_zero, one_mul]
    first
      | ring
      | (simp [hsq]; ring_nf)
      | simp [hsq]
  · simp [PositivityTheory.RgBcC.Fc.wv, PositivityTheory.RgBcC.Fc.chj]
  · simp [PositivityTheory.RgBcC.Fc.wv, PositivityTheory.RgBcC.Fc.chj]
  · intro j
    simp only [PositivityTheory.RgBcC.Fc.wv]
    rw [pow_succ (1 + y ^ 2) N, mul_inv]
    push_cast
    ring

end GlobalTheory.CompanionTheory.WaveFc
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.AsmKerOneOfSteps
namespace PositivityTheory.RgBcC.Fc

open PositivityTheory.RgBcC

theorem asmKerOne_of_steps (hC : AsmCpt) (hS : CalcSteps) (hO : SmoothOp) (hP : PWdecay) (hK : KerCore)
    (hL : KerLoc) (hW : KerW) : AsmKerOne := by
  intro h1 h2 h3 h4 h5 h6 n _ _ μ _ E w g T hg
  have hWC : WaveCpt := hC h1 h2 h3 h4
  apply hW n μ E w g h1 h2 h3
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := hK n μ E g T hg h1 h2 h3 h4 h5 h6 hWC hS hO hP
  exact ⟨k, hL n μ E g T k hg h1 h2 h3 h6 hWC hk1 hk2 hk3 hk4⟩

end PositivityTheory.RgBcC.Fc
end

namespace PositivityTheory.RgBcC.Fc

open PositivityTheory.RgBcC

theorem calcSteps : CalcSteps :=
  ⟨GlobalTheory.T.absolute_fourier_coefficients, GlobalTheory.T.absolute_cutoff_bound, GlobalTheory.T.functional_calculus_curve, GlobalTheory.CompanionTheory.WaveFc.wvAlg, GlobalTheory.T.closure_operator_facts, GlobalTheory.T.sobolev_operator_facts, GlobalTheory.T.compact_sobolev_embedding,
    GlobalTheory.T.section_norm_bound, GlobalTheory.T.sobolev_space_preserved, GlobalTheory.T.concentration_time_bound, GlobalTheory.T.functional_calculus_joint_curve, GlobalTheory.T.friedrichs_extension_facts, GlobalTheory.T.casimir_operator_formula, GlobalTheory.T.sobolev_integration_by_parts,
    GlobalTheory.T.dense_domain_facts⟩

theorem asmCpt : AsmCpt :=
  GlobalTheory.T.functional_calculus_first_assumption GlobalTheory.T.absolute_fourier_coefficients GlobalTheory.T.absolute_cutoff_bound GlobalTheory.T.functional_calculus_curve GlobalTheory.CompanionTheory.WaveFc.wvAlg GlobalTheory.T.closure_operator_facts GlobalTheory.T.sobolev_operator_facts GlobalTheory.T.compact_sobolev_embedding
    GlobalTheory.T.section_norm_bound GlobalTheory.T.sobolev_space_preserved GlobalTheory.T.concentration_time_bound GlobalTheory.T.functional_calculus_joint_curve GlobalTheory.T.friedrichs_extension_facts GlobalTheory.T.casimir_operator_formula GlobalTheory.T.sobolev_integration_by_parts GlobalTheory.T.dense_domain_facts

theorem asmKerOne : AsmKerOne :=
  asmKerOne_of_steps asmCpt calcSteps GlobalTheory.T.smooth_operator_facts GlobalTheory.T.paley_wiener_decay GlobalTheory.T.kernel_regularity GlobalTheory.T.kernel_localization GlobalTheory.T.kernel_weight_facts

end PositivityTheory.RgBcC.Fc
