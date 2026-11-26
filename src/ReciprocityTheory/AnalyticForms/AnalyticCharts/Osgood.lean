module

public import Mathlib

@[expose] public section

section -- merged from ReciprocityTheory.AnalyticForms.AnalyticCharts.OsgoodA
noncomputable section

namespace ReciprocityTheory.AnForm.Osgood

open Complex Metric MeasureTheory Set Filter Topology

open scoped Real

theorem differentiable_cons_right {n : ℕ} (x : ℂ) :
    Differentiable ℂ (fun y : Fin n → ℂ => (Fin.cons x y : Fin (n + 1) → ℂ)) := by
  refine differentiable_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact differentiable_const x
  · simp only [Fin.cons_succ]
    exact differentiable_pi.1 differentiable_id j

theorem differentiable_cons_left {n : ℕ} (y : Fin n → ℂ) :
    Differentiable ℂ (fun x : ℂ => (Fin.cons x y : Fin (n + 1) → ℂ)) := by
  refine differentiable_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact differentiable_id
  · simp only [Fin.cons_succ]
    exact differentiable_const _

theorem mem_closedBall_pi_iff {n : ℕ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 ≤ r) :
    z ∈ closedBall c r ↔ ∀ i, z i ∈ closedBall (c i) r := by
  rw [closedBall_pi c hr, Set.mem_univ_pi]

theorem mem_ball_pi_iff {n : ℕ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) :
    z ∈ ball c r ↔ ∀ i, z i ∈ ball (c i) r := by
  rw [ball_pi c hr, Set.mem_univ_pi]

theorem norm_torusMap_sub {n : ℕ} (c : Fin n → ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : Fin n → ℝ) (i : Fin n) :
    ‖torusMap c (fun _ => r) θ i - c i‖ = r := by
  have h : torusMap c (fun _ => r) θ i - c i = (r : ℂ) * exp ((θ i : ℂ) * I) := by
    simp only [torusMap]
    ring
  have h1 : ‖exp ((θ i : ℂ) * I)‖ = 1 := by
    exact Complex.norm_exp_ofReal_mul_I _
  have h2 : ‖(r : ℂ)‖ = r := by
    exact Complex.norm_of_nonneg hr
  rw [h, norm_mul, h1, h2, mul_one]

theorem torusMap_mem_closedBall {n : ℕ} (c : Fin n → ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : Fin n → ℝ) :
    torusMap c (fun _ => r) θ ∈ closedBall c r := by
  refine (mem_closedBall_pi_iff hr).2 fun i => ?_
  rw [mem_closedBall, dist_eq_norm]
  exact (norm_torusMap_sub c hr θ i).le

theorem torusMap_sub_ne {n : ℕ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) (hz : z ∈ ball c r)
    (θ : Fin n → ℝ) (i : Fin n) : torusMap c (fun _ => r) θ i - z i ≠ 0 := by
  intro h
  have h1 := (mem_ball_pi_iff hr).1 hz i
  rw [mem_ball, dist_eq_norm] at h1
  have h2 := norm_torusMap_sub c hr.le θ i
  rw [sub_eq_zero] at h
  rw [h] at h2
  linarith

theorem continuous_torusMap {n : ℕ} (c : Fin n → ℂ) (r : ℝ) :
    Continuous (torusMap c (fun _ => r)) := by
  refine continuous_pi fun i => ?_
  simp only [torusMap]
  fun_prop

theorem continuous_comp_torusMap {n : ℕ} {f : (Fin n → ℂ) → ℂ} {c : Fin n → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : ∀ ζ ∈ closedBall c r, DifferentiableAt ℂ f ζ) :
    Continuous fun θ => f (torusMap c (fun _ => r) θ) := by
  refine continuous_iff_continuousAt.2 fun θ => ?_
  exact (hf _ (torusMap_mem_closedBall c hr θ)).continuousAt.comp
    (continuous_torusMap c r).continuousAt

theorem torusIntegrable_kernel {n : ℕ} {f : (Fin n → ℂ) → ℂ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : ∀ ζ ∈ closedBall c r, DifferentiableAt ℂ f ζ) (hz : z ∈ ball c r) :
    TorusIntegrable (fun ζ => (∏ i, (ζ i - z i)⁻¹) * f ζ) c (fun _ => r) := by
  have hK : Continuous fun θ => ∏ i, (torusMap c (fun _ => r) θ i - z i)⁻¹ := by
    refine continuous_finsetProd Finset.univ fun i _ => ?_
    refine Continuous.inv₀ ?_ ?_
    · exact ((continuous_apply i).comp (continuous_torusMap c r)).sub continuous_const
    · intro θ
      exact torusMap_sub_ne hr hz θ i
  have hcont : Continuous fun θ =>
      (∏ i, (torusMap c (fun _ => r) θ i - z i)⁻¹) * f (torusMap c (fun _ => r) θ) :=
    hK.mul (continuous_comp_torusMap hr.le hf)
  unfold TorusIntegrable
  exact hcont.continuousOn.integrableOn_compact isCompact_Icc

theorem cauchy_polydisc : ∀ (n : ℕ) (f : (Fin n → ℂ) → ℂ) (c : Fin n → ℂ) (r : ℝ), 0 < r →
    (∀ ζ ∈ closedBall c r, DifferentiableAt ℂ f ζ) → ∀ z ∈ ball c r,
    (∯ ζ in T(c, fun _ => r), (∏ i, (ζ i - z i)⁻¹) * f ζ) = (2 * π * I) ^ n * f z
  | 0, f, c, r, _, _, z, _ => by
    rw [torusIntegral_dim0]
    simp [Subsingleton.elim z c]
  | n + 1, f, c, r, hr, hf, z, hz => by
    rw [torusIntegral_succ (torusIntegrable_kernel hr hf hz)]
    have hz0 : z 0 ∈ ball (c 0) r := (mem_ball_pi_iff hr).mp hz 0
    have hz' : Fin.tail z ∈ ball (c ∘ Fin.succ) r :=
      (mem_ball_pi_iff (c := c ∘ Fin.succ) (z := Fin.tail z) hr).mpr fun i =>
        (mem_ball_pi_iff hr).mp hz i.succ
    have hcons : ∀ x ∈ closedBall (c 0) r, ∀ y ∈ closedBall (fun i => c (Fin.succ i)) r,
        (Fin.cons x y : Fin (n + 1) → ℂ) ∈ closedBall c r := by
      intro x hx y hy
      refine (mem_closedBall_pi_iff hr.le).mpr fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hx
      · simpa using (mem_closedBall_pi_iff hr.le).mp hy j
    have key : EqOn (fun x => ∯ y in T(c ∘ Fin.succ, (fun _ => r) ∘ Fin.succ),
          (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - z i)⁻¹) * f (Fin.cons x y))
        (fun x => (2 * π * I) ^ n * ((x - z 0)⁻¹ * f (Fin.cons x (Fin.tail z)))) (sphere (c 0) r) := by
      intro x hx
      have hxc : x ∈ closedBall (c 0) r := sphere_subset_closedBall hx
      have ih := cauchy_polydisc n (fun y => f (Fin.cons x y)) (fun i => c (Fin.succ i)) r hr
        (fun ζ hζ => (hf _ (hcons x hxc ζ hζ)).comp ζ (differentiable_cons_right x ζ)) (Fin.tail z) hz'
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Function.comp_def, mul_assoc]
      rw [torusIntegral_const_mul]
      simp only [Fin.tail] at ih
      rw [ih]
      ring
    rw [circleIntegral.integral_congr hr.le key, circleIntegral.integral_const_mul]
    have hd : DifferentiableOn ℂ (fun x => f (Fin.cons x (Fin.tail z))) (closedBall (c 0) r) :=
      fun x hx => ((hf _ (hcons x hx _ (ball_subset_closedBall hz'))).comp x
        (differentiable_cons_left (Fin.tail z) x)).differentiableWithinAt
    have h1 := hd.circleIntegral_sub_inv_smul hz0
    simp only [smul_eq_mul] at h1
    rw [h1, Fin.cons_self_tail, pow_succ]
    ring

end ReciprocityTheory.AnForm.Osgood
end
end

noncomputable section

namespace ReciprocityTheory.AnForm.Osgood

open Complex Metric MeasureTheory Set Filter Topology

open scoped Real

def OsgoodStatement : Prop :=
  ∀ (e : ℕ) (U : Set (Fin e → ℂ)) (f : (Fin e → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f U →
    AnalyticOnNhd ℂ f U

variable {n : ℕ}

abbrev Cube (n : ℕ) : Type := Icc (0 : Fin n → ℝ) (fun _ => 2 * π)

instance : CompactSpace (Cube n) := isCompact_iff_compactSpace.mp isCompact_Icc

def cubeProj (θ : Fin n → ℝ) : Cube n :=
  ⟨fun i => (projIcc 0 (2 * π) Real.two_pi_pos.le (θ i) : ℝ),
    fun i => (projIcc 0 (2 * π) Real.two_pi_pos.le (θ i)).2.1,
    fun i => (projIcc 0 (2 * π) Real.two_pi_pos.le (θ i)).2.2⟩

theorem continuous_cubeProj : Continuous (cubeProj (n := n)) := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  exact continuous_subtype_val.comp (continuous_projIcc.comp (continuous_apply i))

theorem cubeProj_of_mem {θ : Fin n → ℝ} (hθ : θ ∈ Icc (0 : Fin n → ℝ) (fun _ => 2 * π)) :
    (cubeProj θ : Fin n → ℝ) = θ := by
  funext i
  show ((projIcc 0 (2 * π) Real.two_pi_pos.le (θ i) : ℝ)) = θ i
  have hi : θ i ∈ Icc (0 : ℝ) (2 * π) := ⟨hθ.1 i, hθ.2 i⟩
  rw [projIcc_of_mem _ hi]

def cubeCoord (c : Fin n → ℂ) (r : ℝ) (i : Fin n) : C(Cube n, ℂ) :=
  ⟨fun θ => torusMap c (fun _ => r) θ.1 i,
    ((continuous_apply i).comp (continuous_torusMap c r)).comp continuous_subtype_val⟩

def kern (c : Fin n → ℂ) (r : ℝ) (z : Fin n → ℂ) : C(Cube n, ℂ) :=
  ∏ i, Ring.inverse (cubeCoord c r i - z i • (1 : C(Cube n, ℂ)))

private theorem cubeCoord_sub_smul_one_apply (c z : Fin n → ℂ) (r : ℝ) (i : Fin n) (θ : Cube n) :
    (cubeCoord c r i - z i • (1 : C(Cube n, ℂ))) θ = torusMap c (fun _ => r) θ.1 i - z i := by
  simp [cubeCoord]

private theorem cubeCoord_sub_smul_one_ne_zero_of_mem_ball {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) (hz : z ∈ ball c r) (i : Fin n)
    (θ : Cube n) : (cubeCoord c r i - z i • (1 : C(Cube n, ℂ))) θ ≠ 0 := by
  rw [cubeCoord_sub_smul_one_apply]
  exact torusMap_sub_ne hr hz θ.1 i

private theorem continuousMap_isUnit_of_forall_ne_zero {X : Type*} [TopologicalSpace X] (g : C(X, ℂ)) (hg : ∀ x, g x ≠ 0) :
    IsUnit g :=
  ⟨⟨g, ⟨fun x => (g x)⁻¹, g.continuous.inv₀ hg⟩, by ext x; simp [hg x], by ext x; simp [hg x]⟩, rfl⟩

private theorem continuousMap_ring_inverse_apply {X : Type*} [TopologicalSpace X] (g : C(X, ℂ)) (hg : ∀ x, g x ≠ 0)
    (x : X) : Ring.inverse g x = (g x)⁻¹ := by
  obtain ⟨u, rfl⟩ := continuousMap_isUnit_of_forall_ne_zero g hg
  rw [Ring.inverse_unit]
  exact eq_inv_of_mul_eq_one_right (by rw [← ContinuousMap.mul_apply, Units.mul_inv, ContinuousMap.one_apply])

theorem kern_apply {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) (hz : z ∈ ball c r) (θ : Cube n) :
    kern c r z θ = ∏ i, (torusMap c (fun _ => r) θ.1 i - z i)⁻¹ := by
  unfold kern
  simp only [ContinuousMap.coe_prod, Finset.prod_apply]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [continuousMap_ring_inverse_apply _ (cubeCoord_sub_smul_one_ne_zero_of_mem_ball hr hz i) θ, cubeCoord_sub_smul_one_apply]

theorem kern_analyticAt (c : Fin n → ℂ) {r : ℝ} (hr : 0 < r) : AnalyticAt ℂ (kern c r) c := by
  have hK : kern c r = ∏ i ∈ Finset.univ,
      fun z : Fin n → ℂ => Ring.inverse (cubeCoord c r i - z i • (1 : C(Cube n, ℂ))) := by
    funext z
    rw [Finset.prod_apply]
    rfl
  rw [hK]
  refine Finset.analyticAt_prod _ fun i _ => ?_
  have hlin : AnalyticAt ℂ (fun z : Fin n → ℂ => z i • (1 : C(Cube n, ℂ))) c :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).smulRight
      (1 : C(Cube n, ℂ))).analyticAt c
  obtain ⟨u, hu⟩ := continuousMap_isUnit_of_forall_ne_zero _ (cubeCoord_sub_smul_one_ne_zero_of_mem_ball hr (mem_ball_self hr) i)
  exact (analyticAt_inverse (𝕜 := ℂ) u).comp_of_eq (analyticAt_const.sub hlin) hu.symm

def jac (r : ℝ) (θ : Fin n → ℝ) : ℂ := ∏ i, (r : ℂ) * exp (θ i * I) * I

def fctl (c : Fin n → ℂ) (r : ℝ) (f : (Fin n → ℂ) → ℂ) (g : C(Cube n, ℂ)) : ℂ :=
  ∫ θ in Icc (0 : Fin n → ℝ) (fun _ => 2 * π), jac r θ * g (cubeProj θ) * f (torusMap c (fun _ => r) θ)

theorem continuous_jac (r : ℝ) : Continuous (jac (n := n) r) := by
  unfold jac
  exact continuous_finsetProd _ fun i _ => by fun_prop

theorem integrableOn_fctl {c : Fin n → ℂ} {r : ℝ} (hr : 0 < r) {f : (Fin n → ℂ) → ℂ}
    (hf : ∀ ζ ∈ closedBall c r, DifferentiableAt ℂ f ζ) (g : C(Cube n, ℂ)) :
    IntegrableOn (fun θ => jac r θ * g (cubeProj θ) * f (torusMap c (fun _ => r) θ))
      (Icc (0 : Fin n → ℝ) (fun _ => 2 * π)) :=
  (((continuous_jac r).mul (g.continuous.comp continuous_cubeProj)).mul
    (continuous_comp_torusMap hr.le hf)).integrableOn_Icc

def fctlCLM (c : Fin n → ℂ) {r : ℝ} (hr : 0 < r) (f : (Fin n → ℂ) → ℂ)
    (hf : ∀ ζ ∈ closedBall c r, DifferentiableAt ℂ f ζ) : C(Cube n, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fctl c r f
      map_add' := fun g g' => by
        simp only [fctl, ContinuousMap.add_apply, mul_add, add_mul]
        exact integral_add (integrableOn_fctl hr hf g) (integrableOn_fctl hr hf g')
      map_smul' := fun a g => by
        simp only [fctl, ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext θ
        ring }
    (by
      obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := fun _ => 2 * π)).exists_bound_of_continuousOn
        (((continuous_jac r).mul (continuous_comp_torusMap hr.le hf)).continuousOn)
      refine ⟨M * volume.real (Icc (0 : Fin n → ℝ) (fun _ => 2 * π)), fun g => ?_⟩
      refine (norm_setIntegral_le_of_norm_le_const (C := M * ‖g‖) measure_Icc_lt_top
        fun θ hθ => ?_).trans (le_of_eq (by ring))
      have h1 : ‖jac r θ * f (torusMap c (fun _ => r) θ)‖ ≤ M := hM θ hθ
      rw [mul_comm (jac r θ), mul_assoc, norm_mul, mul_comm M]
      calc ‖g (cubeProj θ)‖ * ‖jac r θ * f (torusMap c (fun _ => r) θ)‖
          ≤ ‖g‖ * ‖jac r θ * f (torusMap c (fun _ => r) θ)‖ :=
            mul_le_mul_of_nonneg_right (g.norm_coe_le_norm _) (norm_nonneg _)
        _ ≤ ‖g‖ * M := mul_le_mul_of_nonneg_left h1 (norm_nonneg _))

theorem fctlCLM_kern {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) {f : (Fin n → ℂ) → ℂ}
    (hf : ∀ ζ ∈ closedBall c r, DifferentiableAt ℂ f ζ) (hz : z ∈ ball c r) :
    fctlCLM c hr f hf (kern c r z) = (2 * π * I) ^ n * f z := by
  have hcauchy : ∀ (m : ℕ) (g : (Fin m → ℂ) → ℂ) (a : Fin m → ℂ),
      (∀ ζ ∈ closedBall a r, DifferentiableAt ℂ g ζ) → ∀ w ∈ ball a r,
      (∯ ζ in T(a, fun _ => r), (∏ i, (ζ i - w i)⁻¹) * g ζ) = (2 * π * I) ^ m * g w := by
    intro m
    induction m with
    | zero =>
      intro g a _ w _
      rw [torusIntegral_dim0]
      simp [Subsingleton.elim w a]
    | succ m ih =>
      intro g a hg w hw
      rw [torusIntegral_succ (torusIntegrable_kernel hr hg hw)]
      have hw₀ : w 0 ∈ ball (a 0) r := (mem_ball_pi_iff hr).mp hw 0
      have hwTail : Fin.tail w ∈ ball (a ∘ Fin.succ) r :=
        (mem_ball_pi_iff hr).mpr fun i => (mem_ball_pi_iff hr).mp hw i.succ
      have hcons : ∀ x ∈ closedBall (a 0) r, ∀ y ∈ closedBall (a ∘ Fin.succ) r,
          Fin.cons x y ∈ closedBall a r := by
        intro x hx y hy
        refine (mem_closedBall_pi_iff hr.le).mpr (Fin.cases ?_ fun j => ?_)
        · simpa using hx
        · simpa using (mem_closedBall_pi_iff hr.le).mp hy j
      have hslice : EqOn (fun x => ∯ y in T(a ∘ Fin.succ, (fun _ => r) ∘ Fin.succ),
            (∏ i, (Fin.cons x y i - w i)⁻¹) * g (Fin.cons x y))
          (fun x => (2 * π * I) ^ m * ((x - w 0)⁻¹ * g (Fin.cons x (Fin.tail w))))
          (sphere (a 0) r) := by
        intro x hx
        have hxc := sphere_subset_closedBall hx
        have htail := ih (fun y => g (Fin.cons x y)) (a ∘ Fin.succ)
          (fun ζ hζ => (hg _ (hcons x hxc ζ hζ)).comp ζ (differentiable_cons_right x ζ))
          (Fin.tail w) hwTail
        simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Function.comp_def, mul_assoc]
        rw [torusIntegral_const_mul]
        simp only [Fin.tail, Function.comp_def] at htail
        rw [htail]
        ring
      rw [circleIntegral.integral_congr hr.le hslice, circleIntegral.integral_const_mul]
      have hd : DifferentiableOn ℂ (fun x => g (Fin.cons x (Fin.tail w))) (closedBall (a 0) r) :=
        fun x hx => ((hg _ (hcons x hx _ (ball_subset_closedBall hwTail))).comp x
          (differentiable_cons_left (Fin.tail w) x)).differentiableWithinAt
      have hcircle := hd.circleIntegral_sub_inv_smul hw₀
      simp only [smul_eq_mul] at hcircle
      rw [hcircle, Fin.cons_self_tail, pow_succ]
      ring
  rw [← hcauchy n f c hf z hz]
  show fctl c r f (kern c r z) = _
  unfold fctl torusIntegral
  refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  dsimp only
  rw [kern_apply hr hz, cubeProj_of_mem hθ, smul_eq_mul, jac]
  ring

theorem osgood : OsgoodStatement := by
  intro e U f hU hf x hx
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx)
  have hfd : ∀ ζ ∈ closedBall x r, DifferentiableAt ℂ f ζ := fun ζ hζ =>
    hf.differentiableAt (hU.mem_nhds (hrU hζ))
  have hne : ((2 * π * I) ^ e : ℂ) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)) I_ne_zero)
  have hA : AnalyticAt ℂ
      (fun z => ((2 * π * I) ^ e)⁻¹ * fctlCLM x hr f hfd (kern x r z)) x :=
    analyticAt_const.mul (((fctlCLM x hr f hfd).analyticAt _).comp (kern_analyticAt x hr))
  refine hA.congr ?_
  filter_upwards [ball_mem_nhds x hr] with z hz
  rw [fctlCLM_kern hr hfd hz, inv_mul_cancel_left₀ hne]

end ReciprocityTheory.AnForm.Osgood
