module

public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.CovLog

@[expose] public section

section -- merged from ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.ComplexHessianIsHermitianOfContDiffAt
namespace ReciprocityTheory.AnForm.A.TraceConjugationCover

open Complex Filter Topology Matrix

noncomputable section

section Lv

def lv {D : ℕ} (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (a b : Fin D → ℂ) : ℂ :=
  ((H a b + H (I • a) (I • b) : ℝ) + I * ((H a (I • b) - H (I • a) b : ℝ))) / 4

theorem hessC_eq_lv {D : ℕ} (f : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (i j : Fin D) :
    hessC f z i j = lv (fderiv ℝ (fderiv ℝ f) z) (Pi.single i 1) (Pi.single j 1) := rfl

variable {D : ℕ} (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)

theorem lv_add_left (a a' b : Fin D → ℂ) : lv H (a + a') b = lv H a b + lv H a' b := by
  simp only [lv, smul_add, map_add (f := _), ContinuousLinearMap.add_apply]
  push_cast
  ring

theorem lv_add_right (a b b' : Fin D → ℂ) : lv H a (b + b') = lv H a b + lv H a b' := by
  simp only [lv, smul_add, map_add (f := _)]
  push_cast
  ring

private theorem smul_decomp (c : ℂ) (a : Fin D → ℂ) :
    c • a = c.re • a + c.im • (I • a) ∧ I • (c • a) = c.re • (I • a) - c.im • a := by
  constructor
  · ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    ring
  · ext k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    linear_combination ((c.im : ℂ) * a k) * Complex.I_sq

theorem lv_smul_left (c : ℂ) (a b : Fin D → ℂ) : lv H (c • a) b = c * lv H a b := by
  obtain ⟨h1, h2⟩ := smul_decomp c a
  unfold lv
  rw [h2, h1]
  simp only [map_add (f := _), map_sub, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply Complex.ext <;> simp <;> ring

theorem lv_smul_right (c : ℂ) (a b : Fin D → ℂ) :
    lv H a (c • b) = starRingEnd ℂ c * lv H a b := by
  obtain ⟨h1, h2⟩ := smul_decomp c b
  unfold lv
  rw [h2, h1]
  simp only [map_add (f := _), map_sub, map_smul, smul_eq_mul]
  apply Complex.ext <;> simp <;> ring

theorem vec_eq_sum (v : Fin D → ℂ) : v = ∑ i, v i • (Pi.single i 1 : Fin D → ℂ) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext k
  by_cases h : k = i
  · subst h; simp
  · simp [h]

theorem lv_sum_left (v b : Fin D → ℂ) :
    lv H v b = ∑ i, v i * lv H (Pi.single i 1) b := by
  let ℓ : (Fin D → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun a => lv H a b
      map_add' := fun a a' => lv_add_left H a a' b
      map_smul' := fun c a => lv_smul_left H c a b }
  have := map_sum ℓ (fun i => v i • (Pi.single i 1 : Fin D → ℂ)) Finset.univ
  rw [← vec_eq_sum] at this
  simp only [map_smul, smul_eq_mul] at this
  exact this

theorem lv_sum_right (a v : Fin D → ℂ) :
    lv H a v = ∑ i, starRingEnd ℂ (v i) * lv H a (Pi.single i 1) := by
  let ℓ : (Fin D → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun b => starRingEnd ℂ (lv H a b)
      map_add' := fun b b' => by simp [lv_add_right]
      map_smul' := fun c b => by simp [lv_smul_right] }
  have := map_sum ℓ (fun i => v i • (Pi.single i 1 : Fin D → ℂ)) Finset.univ
  rw [← vec_eq_sum] at this
  simp only [map_smul, smul_eq_mul] at this
  have h := congrArg (starRingEnd ℂ) this
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ℓ, LinearMap.coe_mk, AddHom.coe_mk, Complex.conj_conj, map_sum, map_mul] at h
  exact h

theorem lv_expand (u v : Fin D → ℂ) :
    lv H u v = ∑ a, ∑ b, u a * lv H (Pi.single a 1) (Pi.single b 1) * starRingEnd ℂ (v b) := by
  rw [lv_sum_left]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [lv_sum_right, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

end Lv

section Comp

variable {D E : ℕ}

theorem hess_comp (φ : (Fin E → ℂ) → ℝ) (τ : (Fin D → ℂ) → (Fin E → ℂ))
    (z : Fin D → ℂ) (hτ : AnalyticAt ℂ τ z) (hφ : ContDiffAt ℝ 2 φ (τ z)) (w b : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ (φ ∘ τ)) z w b =
      fderiv ℝ (fderiv ℝ φ) (τ z) (fderiv ℂ τ z w) (fderiv ℂ τ z b) +
      fderiv ℝ φ (τ z) (fderiv ℂ (fun x => fderiv ℂ τ x b) z w) := by
  have hτev : ∀ᶠ x in 𝓝 z, AnalyticAt ℂ τ x := hτ.eventually_analyticAt
  have hφev : ∀ᶠ y in 𝓝 (τ z), DifferentiableAt ℝ φ y :=
    (hφ.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hφev' : ∀ᶠ x in 𝓝 z, DifferentiableAt ℝ φ (τ x) :=
    hτ.continuousAt.tendsto.eventually hφev
  have heq : (fun x => fderiv ℝ (φ ∘ τ) x b) =ᶠ[𝓝 z]
      (fun x => fderiv ℝ φ (τ x) (fderiv ℂ τ x b)) := by
    filter_upwards [hτev, hφev'] with x hx hφx
    have hxR : DifferentiableAt ℝ τ x := hx.differentiableAt.restrictScalars ℝ
    rw [fderiv_comp x hφx hxR, hx.differentiableAt.fderiv_restrictScalars ℝ]
    rfl
  have hf2 : ContDiffAt ℝ 2 (φ ∘ τ) z :=
    hφ.comp z ((hτ.contDiffAt (n := 2)).restrict_scalars ℝ)
  have hD : DifferentiableAt ℝ (fderiv ℝ (φ ∘ τ)) z :=
    (hf2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h1 : fderiv ℝ (fderiv ℝ (φ ∘ τ)) z w b = fderiv ℝ (fun x => fderiv ℝ (φ ∘ τ) x b) z w := by
    rw [fderiv_clm_apply hD (differentiableAt_const b)]
    simp
  rw [h1, heq.fderiv_eq]
  have hφ2 : DifferentiableAt ℝ (fderiv ℝ φ) (τ z) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hτR : DifferentiableAt ℝ τ z := hτ.differentiableAt.restrictScalars ℝ
  have hc : HasFDerivAt (fun x => fderiv ℝ φ (τ x))
      ((fderiv ℝ (fderiv ℝ φ) (τ z)).comp (fderiv ℝ τ z)) z :=
    hφ2.hasFDerivAt.comp z hτR.hasFDerivAt
  have hg : DifferentiableAt ℂ (fun x => fderiv ℂ τ x b) z :=
    hτ.fderiv.differentiableAt.clm_apply (differentiableAt_const b)
  have hu : HasFDerivAt (fun x => fderiv ℂ τ x b)
      ((fderiv ℂ (fun x => fderiv ℂ τ x b) z).restrictScalars ℝ) z :=
    hg.hasFDerivAt.restrictScalars ℝ
  rw [(hc.clm_apply hu).fderiv]
  have hwR : fderiv ℝ τ z w = fderiv ℂ τ z w := by
    rw [hτ.differentiableAt.fderiv_restrictScalars ℝ]
    rfl
  simp [hwR, add_comm]

theorem lv_comp (φ : (Fin E → ℂ) → ℝ) (τ : (Fin D → ℂ) → (Fin E → ℂ))
    (z : Fin D → ℂ) (hτ : AnalyticAt ℂ τ z) (hφ : ContDiffAt ℝ 2 φ (τ z)) (a b : Fin D → ℂ) :
    lv (fderiv ℝ (fderiv ℝ (φ ∘ τ)) z) a b =
      lv (fderiv ℝ (fderiv ℝ φ) (τ z)) (fderiv ℂ τ z a) (fderiv ℂ τ z b) := by
  have hg : ∀ c : Fin D → ℂ, DifferentiableAt ℂ (fun x => fderiv ℂ τ x c) z := fun c =>
    hτ.fderiv.differentiableAt.clm_apply (differentiableAt_const c)
  have hGI : fderiv ℂ (fun x => fderiv ℂ τ x (I • b)) z =
      I • fderiv ℂ (fun x => fderiv ℂ τ x b) z := by
    have : (fun x => fderiv ℂ τ x (I • b)) = fun x => I • fderiv ℂ τ x b := by
      funext x; rw [map_smul]
    rw [this]
    exact ((hg b).hasFDerivAt.const_smul I).fderiv
  unfold lv
  rw [hess_comp φ τ z hτ hφ a b, hess_comp φ τ z hτ hφ (I • a) (I • b),
    hess_comp φ τ z hτ hφ a (I • b), hess_comp φ τ z hτ hφ (I • a) b, hGI]
  simp only [ContinuousLinearMap.smul_apply, map_smul, smul_smul, I_mul_I, neg_one_smul, map_neg]
  push_cast
  ring

theorem complexHessian_comp_holomorphic_matrix (φ : (Fin E → ℂ) → ℝ) (τ : (Fin D → ℂ) → (Fin E → ℂ)) (z : Fin D → ℂ)
    (hτ : AnalyticAt ℂ τ z) (hφ : ContDiffAt ℝ 2 φ (τ z)) :
    hessC (φ ∘ τ) z = (Matrix.of fun a k => fderiv ℂ τ z (Pi.single k 1) a)ᵀ * hessC φ (τ z) *
      (Matrix.of fun a k => fderiv ℂ τ z (Pi.single k 1) a).map (starRingEnd ℂ) := by
  ext i j
  rw [hessC_eq_lv, lv_comp φ τ z hτ hφ, lv_expand]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply,
    Finset.sum_mul, ← hessC_eq_lv]
  rw [Finset.sum_comm]

theorem complexHessian_isHermitian_of_contDiffAt (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z) :
    (hessC φ z).IsHermitian := by
  have hs : IsSymmSndFDerivAt ℝ φ z := hφ.isSymmSndFDerivAt (by simp)
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [hessC_eq_lv, lv]
  rw [hs (Pi.single j 1) (Pi.single i 1), hs (I • Pi.single j 1) (I • Pi.single i 1),
    hs (Pi.single j 1) (I • Pi.single i 1), hs (I • Pi.single j 1) (Pi.single i 1)]
  apply Complex.ext <;> simp

theorem complexHessian_add_of_contDiffAt (φ ψ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z)
    (hψ : ContDiffAt ℝ 2 ψ z) :
    hessC (fun w => φ w + ψ w) z = hessC φ z + hessC ψ z := by
  have hev : fderiv ℝ (fun w => φ w + ψ w) =ᶠ[𝓝 z] fun w => fderiv ℝ φ w + fderiv ℝ ψ w := by
    filter_upwards [hφ.eventually (by simp), hψ.eventually (by simp)] with w hw1 hw2
    exact fderiv_add (hw1.differentiableAt (by norm_num)) (hw2.differentiableAt (by norm_num))
  have hφ' : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hψ' : DifferentiableAt ℝ (fderiv ℝ ψ) z :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hD : fderiv ℝ (fderiv ℝ fun w => φ w + ψ w) z =
      fderiv ℝ (fderiv ℝ φ) z + fderiv ℝ (fderiv ℝ ψ) z := by
    rw [hev.fderiv_eq]; exact fderiv_add hφ' hψ'
  ext i j
  simp only [hessC_eq_lv, lv, hD, ContinuousLinearMap.add_apply, Matrix.add_apply]
  push_cast
  ring

end Comp

section SqForm

variable {D : ℕ}

def sqForm (D : ℕ) : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ :=
  ∑ i : Fin D, (((innerSL ℝ (E := ℂ)).comp (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin D => ℂ) i)).flip.comp (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin D => ℂ) i)).flip

theorem sqForm_apply (v u : Fin D → ℂ) :
    sqForm D v u = ∑ i, inner ℝ (v i) (u i) := by
  simp [sqForm]

theorem fderiv_sum_normSq :
    fderiv ℝ (fun w : Fin D → ℂ => ∑ i, Complex.normSq (w i)) =
      fun w => sqForm D w + (sqForm D).flip w := by
  have hf : (fun w : Fin D → ℂ => ∑ i, Complex.normSq (w i)) = fun w => sqForm D w w := by
    funext w
    rw [sqForm_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_self_eq_norm_sq, Complex.normSq_eq_norm_sq]
  rw [hf]
  funext w
  have h : fderiv ℝ (fun y => sqForm D y y) w = _ :=
    ((sqForm D).hasFDerivAt_of_bilinear (hasFDerivAt_id w) (hasFDerivAt_id w)).fderiv
  rw [h]
  ext v
  simp [add_comm]

theorem sqForm_single (i j : Fin D) (a b : ℂ) :
    sqForm D (Pi.single i a) (Pi.single j b) = if i = j then inner ℝ a b else 0 := by
  rw [sqForm_apply, Finset.sum_eq_single i]
  · by_cases h : i = j
    · subst h; simp
    · simp [h, Pi.single_apply, Ne.symm h]
  · intro k _ hk; simp [hk]
  · simp

theorem smul_single_one (i : Fin D) (c : ℂ) :
    c • (Pi.single i 1 : Fin D → ℂ) = Pi.single i c := by
  ext k
  by_cases h : k = i
  · subst h; simp
  · simp [h]

theorem complexHessian_sum_normSq_coord (z : Fin D → ℂ) :
    hessC (fun w => ∑ i, Complex.normSq (w i)) z = 1 := by
  have h : (fun w => sqForm D w + (sqForm D).flip w) = ⇑(sqForm D + (sqForm D).flip) := by
    funext w; rfl
  ext i j
  simp only [hessC, fderiv_sum_normSq, h, ContinuousLinearMap.fderiv, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.flip_apply, smul_single_one, sqForm_single]
  by_cases hij : i = j
  · subst hij
    simp [Matrix.one_apply, Complex.inner]
    norm_num
  · simp [Matrix.one_apply, hij, Ne.symm hij]

end SqForm

end

end ReciprocityTheory.AnForm.A.TraceConjugationCover
end

namespace ReciprocityTheory.AnForm.A

open MeasureTheory Matrix

noncomputable section

variable {D E : ℕ}

def jacC (τ : (Fin D → ℂ) → (Fin E → ℂ)) (z : Fin D → ℂ) : Matrix (Fin E) (Fin D) ℂ :=
  Matrix.of fun a k => fderiv ℂ τ z (Pi.single k 1) a

theorem jacC_eq_toMatrix' (τ : (Fin D → ℂ) → (Fin E → ℂ)) (z : Fin D → ℂ) :
    jacC τ z = LinearMap.toMatrix' (fderiv ℂ τ z : (Fin D → ℂ) →ₗ[ℂ] (Fin E → ℂ)) := by
  ext a k
  rw [LinearMap.toMatrix'_apply]
  rfl

theorem det_jacC (τ : (Fin D → ℂ) → (Fin D → ℂ)) (z : Fin D → ℂ) :
    (jacC τ z).det = LinearMap.det (fderiv ℂ τ z : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) := by
  rw [jacC_eq_toMatrix', LinearMap.det_toMatrix']

theorem hessC_isHermitian (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z) :
    (hessC φ z).IsHermitian := by
  exact TraceConjugationCover.complexHessian_isHermitian_of_contDiffAt φ z hφ

theorem hessC_add (φ ψ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z)
    (hψ : ContDiffAt ℝ 2 ψ z) :
    hessC (fun w => φ w + ψ w) z = hessC φ z + hessC ψ z := by
  exact TraceConjugationCover.complexHessian_add_of_contDiffAt φ ψ z hφ hψ

theorem hessC_comp (φ : (Fin E → ℂ) → ℝ) (τ : (Fin D → ℂ) → (Fin E → ℂ)) (z : Fin D → ℂ)
    (hτ : AnalyticAt ℂ τ z) (hφ : ContDiffAt ℝ 2 φ (τ z)) :
    hessC (φ ∘ τ) z = (jacC τ z)ᵀ * hessC φ (τ z) * (jacC τ z).map (starRingEnd ℂ) := by
  exact TraceConjugationCover.complexHessian_comp_holomorphic_matrix φ τ z hτ hφ

theorem maDens_comp (φ : Fin D → (Fin D → ℂ) → ℝ) (τ : (Fin D → ℂ) → (Fin D → ℂ))
    (z : Fin D → ℂ) (hτ : AnalyticAt ℂ τ z) (hφ : ∀ k, ContDiffAt ℝ 2 (φ k) (τ z)) :
    maDens (fun k => φ k ∘ τ) z = maDens φ (τ z) * Complex.normSq (jacC τ z).det := by
  have h : (fun k => hessC (φ k ∘ τ) z) =
      fun k => (jacC τ z)ᵀ * hessC (φ k) (τ z) * (jacC τ z).map (starRingEnd ℂ) :=
    funext fun k => hessC_comp (φ k) τ z hτ (hφ k)
  simp only [maDens]
  rw [h, mdisc_transpose_mul_mul_conj, Complex.re_ofReal_mul]
  ring

theorem hessC_log_norm (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ) (hg : AnalyticAt ℂ g z)
    (hz : g z ≠ 0) : hessC (fun w => Real.log ‖g w‖) z = 0 := by
  exact hessC_log_norm' g z hg hz

theorem hessC_add_log_norm (φ : (Fin D → ℂ) → ℝ) (g : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ z) (hg : AnalyticAt ℂ g z) (hz : g z ≠ 0) :
    hessC (fun w => φ w + Real.log ‖g w‖) z = hessC φ z := by
  exact hessC_add_log_norm' φ g z hφ hg hz

theorem hessC_add_re_analytic (φ : (Fin D → ℂ) → ℝ) (G : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ z) (hG : AnalyticAt ℂ G z) :
    hessC (fun w => φ w + (G w).re) z = hessC φ z := by
  exact hessC_add_re_analytic' φ G z hφ hG

theorem det_restrictScalars_real {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : V →ₗ[ℂ] V) :
    LinearMap.det (f.restrictScalars ℝ) = Complex.normSq (LinearMap.det f) := by
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]

theorem det_fderiv_real_eq_normSq (τ : (Fin D → ℂ) → (Fin D → ℂ)) (z : Fin D → ℂ)
    (hτ : DifferentiableAt ℂ τ z) :
    (fderiv ℝ τ z).det = Complex.normSq (jacC τ z).det := by
  rw [(hτ.hasFDerivAt.restrictScalars ℝ).fderiv, det_jacC]
  exact det_restrictScalars_real (fderiv ℂ τ z : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))

theorem integral_image_eq_integral_normSq_det_smul {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (τ : (Fin D → ℂ) → (Fin D → ℂ)) (U : Set (Fin D → ℂ)) (hU : IsOpen U)
    (hτ : AnalyticOnNhd ℂ τ U) (hinj : Set.InjOn τ U) (f : (Fin D → ℂ) → F) :
    ∫ w in τ '' U, f w = ∫ z in U, Complex.normSq (jacC τ z).det • f (τ z) := by
  have hd : ∀ x ∈ U, HasFDerivWithinAt τ ((fderiv ℂ τ x).restrictScalars ℝ) U x :=
    fun x hx => ((hτ x hx).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hdet : ∀ x, |((fderiv ℂ τ x).restrictScalars ℝ).det| = Complex.normSq (jacC τ x).det := by
    intro x
    rw [det_jacC]
    have e := det_restrictScalars_real (fderiv ℂ τ x : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))
    rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, e,
      abs_of_nonneg (Complex.normSq_nonneg _)]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hU.measurableSet hd hinj f]
  simp_rw [hdet]

theorem lintegral_image_eq_lintegral_normSq_det_mul (τ : (Fin D → ℂ) → (Fin D → ℂ))
    (U : Set (Fin D → ℂ)) (hU : IsOpen U) (hτ : AnalyticOnNhd ℂ τ U) (hinj : Set.InjOn τ U)
    (f : (Fin D → ℂ) → ENNReal) :
    ∫⁻ w in τ '' U, f w = ∫⁻ z in U, ENNReal.ofReal (Complex.normSq (jacC τ z).det) * f (τ z) := by
  have hd : ∀ x ∈ U, HasFDerivWithinAt τ ((fderiv ℂ τ x).restrictScalars ℝ) U x :=
    fun x hx => ((hτ x hx).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hdet : ∀ x, |((fderiv ℂ τ x).restrictScalars ℝ).det| = Complex.normSq (jacC τ x).det := by
    intro x
    rw [det_jacC]
    have e := det_restrictScalars_real (fderiv ℂ τ x : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))
    rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, e,
      abs_of_nonneg (Complex.normSq_nonneg _)]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hU.measurableSet hd hinj f]
  simp_rw [hdet]

theorem integrableOn_image_iff_analytic {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (τ : (Fin D → ℂ) → (Fin D → ℂ)) (U : Set (Fin D → ℂ)) (hU : IsOpen U)
    (hτ : AnalyticOnNhd ℂ τ U) (hinj : Set.InjOn τ U) (f : (Fin D → ℂ) → F) :
    IntegrableOn f (τ '' U) ↔
      IntegrableOn (fun z => Complex.normSq (jacC τ z).det • f (τ z)) U := by
  have hd : ∀ x ∈ U, HasFDerivWithinAt τ ((fderiv ℂ τ x).restrictScalars ℝ) U x :=
    fun x hx => ((hτ x hx).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hdet : ∀ x, |((fderiv ℂ τ x).restrictScalars ℝ).det| = Complex.normSq (jacC τ x).det := by
    intro x
    rw [det_jacC]
    have e := det_restrictScalars_real (fderiv ℂ τ x : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))
    rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, e,
      abs_of_nonneg (Complex.normSq_nonneg _)]
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hU.measurableSet hd hinj f]
  simp_rw [hdet]

theorem hessC_sum_normSq (z : Fin D → ℂ) :
    hessC (fun w => ∑ i, Complex.normSq (w i)) z = 1 := by
  exact TraceConjugationCover.complexHessian_sum_normSq_coord z

end

end ReciprocityTheory.AnForm.A
