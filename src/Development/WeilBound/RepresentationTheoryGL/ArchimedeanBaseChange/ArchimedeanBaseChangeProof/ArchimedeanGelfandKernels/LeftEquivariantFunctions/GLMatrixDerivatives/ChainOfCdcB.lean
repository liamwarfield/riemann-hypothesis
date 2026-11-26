module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfSt

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfCdc
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfCdcA
noncomputable section

open Matrix Finset

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cdc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat hb)

variable {n : ℕ}

theorem isOpen_GLs : IsOpen (GLs n) :=
  isOpen_ne_fun (continuous_id.matrix_det) continuous_const

theorem hb_herm (p : Fin n × Fin n) : (hb p : Mat n).IsHermitian := by
  obtain ⟨a, b⟩ := p
  unfold hb
  split_ifs with h1 h2
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_single]
  · simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_single]
    simp [add_comm]
  · simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_single]
    simp [star_mul', Complex.conj_I]
    rw [← smul_neg, neg_sub]

theorem hb_apply (p : Fin n × Fin n) (i j : Fin n) : (hb p : Mat n) i j =
    if p.1 = p.2 then (if p.1 = i ∧ p.1 = j then 1 else 0)
    else if p.1 < p.2 then ((Real.sqrt 2)⁻¹ : ℂ) * ((if p.1 = i ∧ p.2 = j then 1 else 0) + (if p.2 = i ∧ p.1 = j then 1 else 0))
    else (((Real.sqrt 2)⁻¹ : ℂ) * Complex.I) * ((if p.1 = i ∧ p.2 = j then 1 else 0) - (if p.2 = i ∧ p.1 = j then 1 else 0)) := by
  obtain ⟨a, b⟩ := p
  unfold hb
  dsimp only
  by_cases hab : a = b
  · subst hab
    simp only [if_true, Matrix.single_apply]
  · rw [if_neg hab, if_neg hab]
    by_cases hlt : a < b
    · rw [if_pos hlt, if_pos hlt]
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply, smul_eq_mul]
    · rw [if_neg hlt, if_neg hlt]
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply, smul_eq_mul]

theorem hb_tr (H : Mat n) (p : Fin n × Fin n) : (H * hb p).trace =
    if p.1 = p.2 then H p.1 p.1
    else if p.1 < p.2 then ((Real.sqrt 2)⁻¹ : ℂ) * (H p.2 p.1 + H p.1 p.2)
    else (((Real.sqrt 2)⁻¹ : ℂ) * Complex.I) * (H p.2 p.1 - H p.1 p.2) := by
  obtain ⟨a, b⟩ := p
  unfold hb
  dsimp only
  by_cases hab : a = b
  · subst hab
    simp [Matrix.trace_mul_single]
  · rw [if_neg hab, if_neg hab]
    by_cases hlt : a < b
    · rw [if_pos hlt, if_pos hlt]
      simp [Matrix.mul_add, Matrix.trace_add, Matrix.trace_mul_single]
      ring
    · rw [if_neg hlt, if_neg hlt]
      simp [Matrix.mul_sub, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_mul_single]

theorem key_pair (h : ℂ) (s : ℝ) (hs : s * s = 2) :
    (((((s : ℂ))⁻¹ * (star h + h)).re : ℝ) : ℂ) * ((s : ℂ))⁻¹ +
      (((((s : ℂ))⁻¹ * Complex.I * (h - star h)).re : ℝ) : ℂ) * (-((s : ℂ))⁻¹ * Complex.I) = h := by
  rw [← Complex.ofReal_inv]
  have hc2 : s⁻¹ * s⁻¹ = 1 / 2 := by rw [← mul_inv, hs]; norm_num
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
    linear_combination (2 * h.re) * hc2
  · simp [Complex.mul_re, Complex.mul_im]
    linear_combination (2 * h.im) * hc2

theorem key_pair2 (h : ℂ) (s : ℝ) (hs : s * s = 2) :
    (((((s : ℂ))⁻¹ * Complex.I * (star h - h)).re : ℝ) : ℂ) * (((s : ℂ))⁻¹ * Complex.I) +
      (((((s : ℂ))⁻¹ * (h + star h)).re : ℝ) : ℂ) * ((s : ℂ))⁻¹ = h := by
  rw [← Complex.ofReal_inv]
  have hc2 : s⁻¹ * s⁻¹ = 1 / 2 := by rw [← mul_inv, hs]; norm_num
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
    linear_combination (2 * h.re) * hc2
  · simp [Complex.mul_re, Complex.mul_im]
    linear_combination (2 * h.im) * hc2

theorem hb_expand (H : Mat n) (hH : H.IsHermitian) : ∑ p, ((H * hb p).trace.re : ℝ) • (hb p : Mat n) = H := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  have hji : H j i = star (H i j) := (hH.apply j i).symm
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  by_cases hij : i = j
  · subst hij
    have him : (H i i).im = 0 := by
      have := congrArg Complex.im (hH.apply i i)
      simp only [Complex.star_def, Complex.conj_im] at this
      linarith
    rw [Finset.sum_eq_single (i, i)]
    · rw [hb_tr, hb_apply]
      simp only [if_true, and_self, Complex.real_smul, mul_one]
      apply Complex.ext <;> simp [him]
    · intro p _ hp
      obtain ⟨a, b⟩ := p
      have hne : ¬(a = i ∧ b = i) := fun h => hp (by rw [h.1, h.2])
      have hne' : ¬(b = i ∧ a = i) := fun h => hne ⟨h.2, h.1⟩
      rw [hb_apply]
      dsimp only
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl, if_neg hne, smul_zero]
      · rw [if_neg hab, if_neg hne, if_neg hne']
        split_ifs <;> simp
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hne : (i, j) ≠ (j, i) := fun h => hij (Prod.mk.inj h).1
    rw [Finset.sum_eq_add (i, j) (j, i) hne]
    · rw [hb_tr, hb_tr, hb_apply, hb_apply]
      dsimp only
      rw [if_neg hij, if_neg (Ne.symm hij)]
      simp only [hji, Complex.real_smul]
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · rw [if_pos hlt, if_pos hlt, if_neg (not_lt.mpr hlt.le), if_neg (not_lt.mpr hlt.le)]
        simp only [and_self, if_true, hij, Ne.symm hij, false_and, if_false, add_zero, zero_sub, mul_one, mul_neg]
        have := key_pair (H i j) (Real.sqrt 2) hs
        convert this using 1
        ring
      · simp only [hlt, not_lt.mpr hlt.le, if_true, if_false]
        simp only [and_self, if_true, hij, Ne.symm hij, false_and, and_false, if_false, add_zero, zero_add, sub_zero,
          zero_sub, mul_one, mul_neg]
        have := key_pair2 (H i j) (Real.sqrt 2) hs
        convert this using 1
    · intro p _ hp
      obtain ⟨a, b⟩ := p
      have h1 : ¬(a = i ∧ b = j) := fun h => hp.1 (by rw [h.1, h.2])
      have h2 : ¬(b = i ∧ a = j) := fun h => hp.2 (by rw [h.1, h.2])
      rw [hb_apply]
      dsimp only
      by_cases hab : a = b
      · subst hab
        have h3 : ¬(a = i ∧ a = j) := fun h => hij (h.1.symm.trans h.2)
        rw [if_pos rfl, if_neg h3, smul_zero]
      · rw [if_neg hab, if_neg h1, if_neg h2]
        split_ifs <;> simp
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h

theorem unit_mul_star (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 * (k.1)ᴴ = 1 := by
  have := Matrix.mem_unitaryGroup_iff.mp k.2
  rwa [Matrix.star_eq_conjTranspose] at this

theorem unit_star_mul (k : Matrix.unitaryGroup (Fin n) ℂ) : (k.1)ᴴ * k.1 = 1 := by
  have := Matrix.mem_unitaryGroup_iff'.mp k.2
  rwa [Matrix.star_eq_conjTranspose] at this

theorem conj_herm (k : Mat n) (H : Mat n) (hH : H.IsHermitian) : (k * H * kᴴ).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH.eq, Matrix.mul_assoc]

theorem expand_conj (k : Matrix.unitaryGroup (Fin n) ℂ) (H : Mat n) (hH : H.IsHermitian) :
    ∑ p, ((H * (k.1 * hb p * (k.1)ᴴ)).trace.re : ℝ) • (k.1 * hb p * (k.1)ᴴ) = H := by
  have h1 := hb_expand ((k.1)ᴴ * H * k.1) (by
    have := conj_herm (k.1)ᴴ H hH
    rwa [Matrix.conjTranspose_conjTranspose] at this)
  have h2 : ∀ p, ((k.1)ᴴ * H * k.1 * hb p).trace = (H * (k.1 * hb p * (k.1)ᴴ)).trace := by
    intro p
    rw [show (k.1)ᴴ * H * k.1 * hb p = (k.1)ᴴ * (H * k.1 * hb p) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm, show H * k.1 * hb p * (k.1)ᴴ = H * (k.1 * hb p * (k.1)ᴴ) by simp only [Matrix.mul_assoc]]
  simp only [h2] at h1
  have h3 := congrArg (fun M => k.1 * M * (k.1)ᴴ) h1
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul] at h3
  rw [h3, ← Matrix.mul_assoc, ← Matrix.mul_assoc, unit_mul_star, Matrix.one_mul, Matrix.mul_assoc, unit_mul_star,
    Matrix.mul_one]

theorem basis_inv {W : Type} [AddCommGroup W] [Module ℝ W] (B : Mat n →ₗ[ℝ] Mat n →ₗ[ℝ] W)
    (k : Matrix.unitaryGroup (Fin n) ℂ) :
    ∑ p, B (k.1 * hb p * (k.1)ᴴ) (k.1 * hb p * (k.1)ᴴ) = ∑ p, B (hb p) (hb p) := by
  set Y : Fin n × Fin n → Mat n := fun p => k.1 * hb p * (k.1)ᴴ with hYdef
  have hY : ∀ p, (Y p).IsHermitian := fun p => conj_herm k.1 (hb p) (hb_herm p)
  calc ∑ p, B (Y p) (Y p) = ∑ p, B (Y p) (∑ q, ((Y p * hb q).trace.re : ℝ) • (hb q : Mat n)) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hb_expand _ (hY p)]
    _ = ∑ p, ∑ q, ((Y p * hb q).trace.re : ℝ) • B (Y p) (hb q) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul]
    _ = ∑ q, ∑ p, ((hb q * Y p).trace.re : ℝ) • B (Y p) (hb q) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
        rw [Matrix.trace_mul_comm]
    _ = ∑ q, B (∑ p, ((hb q * Y p).trace.re : ℝ) • Y p) (hb q) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    _ = ∑ q, B (hb q) (hb q) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [expand_conj k (hb q) (hb_herm q)]

end PositivityTheory.RgBcC.LfSt.ChainPf.Cdc
end
end

noncomputable section

open Matrix Finset
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cdc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def mulRL (c : Mat n) : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ c)

@[simp] theorem mulRL_apply (c y : Mat n) : mulRL c y = y * c := rfl

def mulLRL (a c : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap ((LinearMap.mulLeft ℝ a).comp (LinearMap.mulRight ℝ c))

theorem mem_GLs_mul {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

theorem unit_mem (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq]
  intro h
  have := congrArg Matrix.det (unit_star_mul k)
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at this
  exact zero_ne_one this

theorem unit_star_mem (k : Matrix.unitaryGroup (Fin n) ℂ) : (k.1)ᴴ ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq]
  intro h
  have := congrArg Matrix.det (unit_mul_star k)
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at this
  exact zero_ne_one this

theorem inv_val (k : Matrix.unitaryGroup (Fin n) ℂ) : (k⁻¹ : Matrix.unitaryGroup (Fin n) ℂ).1 = (k.1)ᴴ := by
  rw [← Matrix.star_eq_conjTranspose]
  rfl

theorem fderiv_right {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (F : Mat n → W) (c g : Mat n) (Φ : W →L[ℝ] W)
    (hF : DifferentiableAt ℝ F (g * c)) (hF' : DifferentiableAt ℝ F g)
    (hEq : (fun y => F (y * c)) =ᶠ[nhds g] fun y => Φ (F y)) (Z : Mat n) :
    fderiv ℝ F (g * c) (Z * c) = Φ (fderiv ℝ F g Z) := by
  have e := hEq.fderiv_eq (𝕜 := ℝ)
  have h1 : HasFDerivAt (fun y => F (y * c)) ((fderiv ℝ F (g * c)).comp (mulRL c)) g := by
    exact hF.hasFDerivAt.comp g (mulRL c).hasFDerivAt
  have h2 : HasFDerivAt (fun y => Φ (F y)) (Φ.comp (fderiv ℝ F g)) g := Φ.hasFDerivAt.comp g hF'.hasFDerivAt
  rw [h1.fderiv, h2.fderiv] at e
  have := congrArg (fun L : Mat n →L[ℝ] W => L Z) e
  simpa using this

section Cx

variable {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)}
  {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}

theorem fr_star (h : CxData lam E Fr ε ι S Γ T) (k : Matrix.unitaryGroup (Fin n) ℂ) : Fr (k.1)ᴴ = E.ρ k⁻¹ := by
  rw [← inv_val, h.onK]

theorem rho_mul_inv (k : Matrix.unitaryGroup (Fin n) ℂ) : E.ρ k * E.ρ k⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

theorem eps_rho_inv (h : CxData lam E Fr ε ι S Γ T) (k : Matrix.unitaryGroup (Fin n) ℂ) (X : Mat n) (hX : X.IsHermitian) :
    ε X * E.ρ k⁻¹ = E.ρ k⁻¹ * ε (k.1 * X * (k.1)ᴴ) := by
  have := h.frε (k.1)ᴴ (unit_star_mem k) X hX
  rwa [fr_star h, Matrix.conjTranspose_conjTranspose] at this

theorem eps_rho (h : CxData lam E Fr ε ι S Γ T) (k : Matrix.unitaryGroup (Fin n) ℂ) (Y : Mat n) (hY : Y.IsHermitian) :
    ε Y * E.ρ k = E.ρ k * ε ((k.1)ᴴ * Y * k.1) := by
  have := h.frε k.1 (unit_mem k) Y hY
  rwa [h.onK] at this

theorem fr_diff (h : CxData lam E Fr ε ι S Γ T) {x : Mat n} (hx : x ∈ GLs n) : DifferentiableAt ℝ Fr x :=
  (h.smooth.differentiableOn (by simp)).differentiableAt (isOpen_GLs.mem_nhds hx)

theorem one_mem_GLs : (1 : Mat n) ∈ GLs n := by
  simp [GLs]

theorem dFr_conj (h : CxData lam E Fr ε ι S Γ T) (k : Matrix.unitaryGroup (Fin n) ℂ) (Y : Mat n) :
    fderiv ℝ Fr 1 ((k.1)ᴴ * (Y * k.1)) = E.ρ k⁻¹ * fderiv ℝ Fr 1 Y * E.ρ k := by
  set L : (E.V →L[ℂ] E.V) →L[ℝ] (E.V →L[ℂ] E.V) :=
    (ContinuousLinearMap.mulLeftRight ℂ (E.V →L[ℂ] E.V) (E.ρ k⁻¹) (E.ρ k)).restrictScalars ℝ with hL
  have hEq : (fun y => Fr ((k.1)ᴴ * (y * k.1))) =ᶠ[nhds (1 : Mat n)] fun y => L (Fr y) := by
    filter_upwards [isOpen_GLs.mem_nhds (one_mem_GLs (n := n))] with y hy
    rw [h.mul _ (unit_star_mem k) _ (mem_GLs_mul hy (unit_mem k)), h.mul _ hy _ (unit_mem k), fr_star h, h.onK]
    simp [hL, ContinuousLinearMap.mulLeftRight_apply, mul_assoc]
  have e := hEq.fderiv_eq (𝕜 := ℝ)
  have hpt : (k.1)ᴴ * ((1 : Mat n) * k.1) = 1 := by rw [Matrix.one_mul, unit_star_mul]
  have h1 : HasFDerivAt (fun y => Fr ((k.1)ᴴ * (y * k.1))) ((fderiv ℝ Fr 1).comp (mulLRL (k.1)ᴴ k.1)) 1 := by
    have hd := (fr_diff h (one_mem_GLs (n := n))).hasFDerivAt
    rw [← hpt] at hd
    have := hd.comp (1 : Mat n) (mulLRL (k.1)ᴴ k.1).hasFDerivAt
    rw [hpt] at this
    exact this
  have h2 : HasFDerivAt (fun y => L (Fr y)) (L.comp (fderiv ℝ Fr 1)) 1 :=
    L.hasFDerivAt.comp (1 : Mat n) (fr_diff h (one_mem_GLs (n := n))).hasFDerivAt
  rw [h1.fderiv, h2.fderiv] at e
  have := congrArg (fun M : Mat n →L[ℝ] (E.V →L[ℂ] E.V) => M Y) e
  simpa [hL, mulLRL, ContinuousLinearMap.mulLeftRight_apply] using this

end Cx

end PositivityTheory.RgBcC.LfSt.ChainPf.Cdc
end
end

noncomputable section

open Matrix Finset
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cdc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem hb_conj_back (k : Matrix.unitaryGroup (Fin n) ℂ) (X : Mat n) :
    (k.1)ᴴ * ((k.1 * X * (k.1)ᴴ) * k.1) = X := by
  have h : (k.1)ᴴ * ((k.1 * X * (k.1)ᴴ) * k.1) = ((k.1)ᴴ * k.1) * X * ((k.1)ᴴ * k.1) := by
    simp only [Matrix.mul_assoc]
  rw [h, unit_star_mul]
  simp

theorem dCinCE : DCinCE := by
  intro n lam E Fr ε ι S Γ T hD f hf
  obtain ⟨hs, heq⟩ := hf
  have hdiff : ∀ x ∈ GLs n, DifferentiableAt ℝ f x := fun x hx =>
    (hs.differentiableOn (by simp)).differentiableAt (isOpen_GLs.mem_nhds hx)
  refine ⟨?_, ?_⟩
  · have hfa := contDiffOn_fderivWithin_apply (m := ∞) hs isOpen_GLs.uniqueDiffOn (le_of_eq rfl)
    unfold DC
    refine ContDiffOn.sum fun p _ => ?_
    have h1 : ContDiffOn ℝ ∞ (fun x => Rd (hb p) f x) (GLs n) := by
      refine (hfa.comp (contDiffOn_id.prodMk (mulRL (hb p)).contDiff.contDiffOn)
        (fun x hx => ⟨hx, Set.mem_univ _⟩)).congr fun x hx => ?_
      show fderiv ℝ f x (x * hb p) = fderivWithin ℝ f (GLs n) x (mulRL (hb p) x)
      rw [fderivWithin_of_isOpen isOpen_GLs hx, mulRL_apply]
    have h2 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ Fr 1 (hb p) (f x)) (GLs n) :=
      ((fderiv ℝ Fr 1 (hb p)).restrictScalars ℝ).contDiff.comp_contDiffOn hs
    exact ((ε (hb p)).restrictScalars ℝ).contDiff.comp_contDiffOn (h1.add h2)
  · intro g hg k
    have hgk : g * k.1 ∈ GLs n := mem_GLs_mul hg (unit_mem k)
    have hRd : ∀ X : Mat n, Rd X f (g * k.1) = E.ρ k⁻¹ (Rd (k.1 * X * (k.1)ᴴ) f g) := by
      intro X
      have hev : (fun y : Mat n => f (y * k.1)) =ᶠ[nhds g]
          fun y => ((E.ρ k⁻¹).restrictScalars ℝ) (f y) := by
        filter_upwards [isOpen_GLs.mem_nhds hg] with y hy
        simpa using heq y hy k
      have h := fderiv_right f k.1 g _ (hdiff _ hgk) (hdiff _ hg) hev (g * (k.1 * X * (k.1)ᴴ))
      have hm : g * (k.1 * X * (k.1)ᴴ) * k.1 = g * k.1 * X := by
        simp only [Matrix.mul_assoc, unit_star_mul, Matrix.mul_one]
      show fderiv ℝ f (g * k.1) (g * k.1 * X) = E.ρ k⁻¹ (fderiv ℝ f g (g * (k.1 * X * (k.1)ᴴ)))
      rw [← hm]
      simpa using h
    have hv : ∀ v, E.ρ k (E.ρ k⁻¹ v) = v := by
      intro v
      rw [← ContinuousLinearMap.mul_apply, rho_mul_inv]
      rfl
    have hdF : ∀ (X : Mat n) (v : E.V), (fderiv ℝ Fr 1 X) (E.ρ k⁻¹ v)
        = E.ρ k⁻¹ (fderiv ℝ Fr 1 (k.1 * X * (k.1)ᴴ) v) := by
      intro X v
      have h := dFr_conj hD k (k.1 * X * (k.1)ᴴ)
      rw [hb_conj_back k X] at h
      rw [h, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hv]
    have heps : ∀ (X : Mat n), IsHermitian X → ∀ w,
        ε X (E.ρ k⁻¹ w) = E.ρ k⁻¹ (ε (k.1 * X * (k.1)ᴴ) w) := by
      intro X hX w
      rw [← ContinuousLinearMap.mul_apply, eps_rho_inv hD k X hX, ContinuousLinearMap.mul_apply]
    let B : Mat n →ₗ[ℝ] Mat n →ₗ[ℝ] E.V :=
      LinearMap.mk₂ ℝ (fun Y Z => ε Y (Rd Z f g + fderiv ℝ Fr 1 Z (f g)))
        (by
          intro a b c
          simp only [map_add (f := _), ContinuousLinearMap.add_apply]
          abel)
        (by intro c a b; simp only [map_smul, ContinuousLinearMap.smul_apply])
        (by
          intro a b c
          simp only [Rd, Matrix.mul_add, map_add (f := _), ContinuousLinearMap.add_apply]
          abel)
        (by
          intro c a b
          simp only [Rd, Matrix.mul_smul, map_smul, ContinuousLinearMap.smul_apply]
          rw [← smul_add]
          exact (ε a).map_smul_of_tower c _)
    have key := basis_inv B k
    unfold DC
    rw [heq g hg k]
    calc ∑ p : Fin n × Fin n, ε (hb p) (Rd (hb p) f (g * k.1) + fderiv ℝ Fr 1 (hb p) (E.ρ k⁻¹ (f g)))
        = ∑ p : Fin n × Fin n, E.ρ k⁻¹ (B (k.1 * hb p * (k.1)ᴴ) (k.1 * hb p * (k.1)ᴴ)) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [hRd, hdF, ← map_add (f := _), heps _ (hb_herm p)]
          rfl
      _ = E.ρ k⁻¹ (∑ p : Fin n × Fin n, B (hb p) (hb p)) := by rw [← map_sum, key]
      _ = _ := rfl

end PositivityTheory.RgBcC.LfSt.ChainPf.Cdc
