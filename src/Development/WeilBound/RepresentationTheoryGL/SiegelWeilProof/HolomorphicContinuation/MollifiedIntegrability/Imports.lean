module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GaussM
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsBound
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GBClose
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ContinuousHerm
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.DensOf3

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ImportsAlt
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GWickC
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.EvXPderivPhiP
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GWickB
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GWickA
noncomputable section

open MeasureTheory Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def ent (a : Fin m) (i : Fin n) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a)

def crd (k : Fin m × Fin n × Bool) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  if k.2.2 then (Complex.conjCLE.toContinuousLinearMap).comp (ent k.1 k.2.1) else ent k.1 k.2.1

theorem ent_apply (a : Fin m) (i : Fin n) (v : Fin m → Fin n → ℂ) : ent a i v = v a i := rfl

theorem crd_apply (k : Fin m × Fin n × Bool) (v : Fin m → Fin n → ℂ) :
    crd k v = if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1 := by
  unfold crd; split_ifs <;> simp [ent_apply, Complex.conjCLE_apply]

theorem evX_eq (P : PX m n) (x : Fin m → Fin n → ℂ) : evX P x = MvPolynomial.eval (fun k => crd k x) P := by
  simp only [evX, crd_apply]

theorem evX_pderiv_mul_X (p : PX m n) (k b : Fin m × Fin n × Bool) (x : Fin m → Fin n → ℂ) :
    evX (pderiv b (p * X k)) x = evX (pderiv b p) x * crd k x + evX p x * (if k = b then 1 else 0) := by
  rw [pderiv_mul, pderiv_X]
  by_cases h : k = b
  · subst h; simp [evX_eq]
  · simp [evX_eq, Pi.single_apply, h]

def dEv (P : PX m n) (x : Fin m → Fin n → ℂ) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  ∑ k, evX (pderiv k P) x • crd k

theorem hasFDerivAt_evX (P : PX m n) (x : Fin m → Fin n → ℂ) : HasFDerivAt (evX P) (dEv P x) x := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h : evX (C a : PX m n) = fun _ => a := by funext y; simp [evX]
    rw [h]; refine (hasFDerivAt_const a x).congr_fderiv ?_
    simp [dEv, evX]
  | add p q hp hq =>
    have h : evX (p + q) = fun y => evX p y + evX q y := by funext y; simp [evX]
    rw [h]; refine (hp.add hq).congr_fderiv ?_
    unfold dEv; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun k _ => ?_
    rw [← add_smul]; congr 1; simp [evX]
  | mul_X p k hp =>
    have h : evX (p * X k) = fun y => evX p y * crd k y := by funext y; simp [evX_eq]
    rw [h]; refine (hp.mul (crd k).hasFDerivAt).congr_fderiv ?_
    ext v
    simp only [dEv, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.coe_sum', Finset.sum_apply, smul_eq_mul, evX_pderiv_mul_X, add_mul,
      Finset.sum_add_distrib]
    have e1 : ∑ b, evX (pderiv b p) x * crd k x * crd b v = crd k x * ∑ b, evX (pderiv b p) x * crd b v := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => ?_; ring
    have e2 : ∑ b, (evX p x * if k = b then 1 else 0) * crd b v = evX p x * crd k v := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    rw [e1, e2]; ring

end PositivityTheory.Rg.Sw.WR.G
end
end

noncomputable section

open MeasureTheory Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem gramX_apply (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (i j : Fin n) :
    gramX ε x i j = ∑ a, sgn ε a * star (x a i) * x a j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramX, Qp, Qb, map_sub, map_sum, map_mul, evX, eval_X, if_true, Bool.false_eq_true, if_false]
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases h : ε a <;> simp [sgn, h]

theorem gramX_herm (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) : (gramX ε x)ᴴ = gramX ε x := by
  ext i j
  simp only [conjTranspose_apply, gramX_apply, star_sum, star_mul', star_star]
  refine Finset.sum_congr rfl fun a _ => ?_
  have : star (sgn ε a) = sgn ε a := by unfold sgn; split_ifs <;> simp
  rw [this]; ring

theorem trace_im_zero (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian)
    (x : Fin m → Fin n → ℂ) : (b * gramX ε x).trace.im = 0 := by
  have h : star (b * gramX ε x).trace = (b * gramX ε x).trace := by
    rw [← trace_conjTranspose, conjTranspose_mul, gramX_herm, hb.eq, trace_mul_comm]
  have := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith

theorem norm_exp_tr (ε : Fin m → Bool) (t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian)
    (x : Fin m → Fin n → ℂ) : ‖Complex.exp (Complex.I * t * (b * gramX ε x).trace)‖ = 1 := by
  rw [Complex.norm_exp]
  have h := trace_im_zero ε b hb x
  simp [Complex.mul_re, h]

def phiP (ε : Fin m → Bool) (c t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) : PX m n :=
  -∑ a, ∑ k, ∑ j, C ((Amat ε c t b a) k j) * X (a, k, true) * X (a, j, false)

theorem evX_phiP (ε : Fin m → Bool) (c t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    evX (phiP ε c t b) x = -∑ a, ∑ k, ∑ j, (Amat ε c t b a) k j * star (x a k) * x a j := by
  simp [phiP, evX]

theorem exp_phiP (ε : Fin m → Bool) (c t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    gs c x * Complex.exp (Complex.I * t * (b * gramX ε x).trace) = Complex.exp (evX (phiP ε c t b) x) := by
  rw [gs, ← Complex.exp_add, evX_phiP]
  congr 1
  have h1 : (((c * ∑ a, ∑ i, ‖x a i‖ ^ 2 : ℝ)) : ℂ) = ∑ a, ∑ k, (c : ℂ) * (star (x a k) * x a k) := by
    push_cast
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_
    have hz : (starRingEnd ℂ) (x a k) * x a k = ((‖x a k‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [Complex.star_def, hz]; push_cast; ring
  have h2 : (b * gramX ε x).trace = ∑ a, ∑ k, ∑ j, sgn ε a * b j k * star (x a k) * x a j := by
    simp only [trace, diag, Matrix.mul_apply, gramX_apply, Finset.mul_sum]
    conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h3 : ∀ a k, ∑ j, (Amat ε c t b a) k j * star (x a k) * x a j =
      (c : ℂ) * (star (x a k) * x a k) - ∑ j, Complex.I * t * (sgn ε a * b j k * star (x a k) * x a j) := by
    intro a k
    simp only [Amat, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply, smul_eq_mul,
      sub_mul, Finset.sum_sub_distrib]
    congr 1
    · simp [Finset.sum_ite_eq, mul_assoc]
    · refine Finset.sum_congr rfl fun j _ => ?_; ring
  rw [h1, h2]
  simp only [h3, Finset.sum_sub_distrib, Finset.mul_sum]
  ring

end PositivityTheory.Rg.Sw.WR.G
end
end

noncomputable section

open MeasureTheory Matrix MvPolynomial
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem amat_det_ne (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (t : ℝ) {b : Matrix (Fin n) (Fin n) ℂ}
    (hb : b.IsHermitian) (a : Fin m) : (Amat ε c t b a).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hA : Amat ε c t b a *ᵥ v = (c : ℂ) • v - (Complex.I * t * sgn ε a) • (bᵀ *ᵥ v) := by
    rw [Amat, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, one_mulVec]
  have key : (c : ℂ) * (star v ⬝ᵥ v) - (Complex.I * t * sgn ε a) * (star v ⬝ᵥ (bᵀ *ᵥ v)) = 0 := by
    have h1 : star v ⬝ᵥ (Amat ε c t b a *ᵥ v) = 0 := by rw [hv, dotProduct_zero]
    rw [hA, dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h1
    exact h1
  have hq : (star v ⬝ᵥ (bᵀ *ᵥ v)).im = 0 := hb.transpose.im_star_dotProduct_mulVec_self v
  have hd : (star v ⬝ᵥ v).im = 0 := by
    have := Matrix.isHermitian_one.im_star_dotProduct_mulVec_self (𝕜 := ℂ) v
    rwa [one_mulVec] at this
  have hq' : star v ⬝ᵥ (bᵀ *ᵥ v) = ((star v ⬝ᵥ (bᵀ *ᵥ v)).re : ℂ) := Complex.ext (by simp) (by simp [hq])
  have hs' : sgn ε a = ((if ε a then 1 else -1 : ℝ) : ℂ) := by unfold sgn; split_ifs <;> simp
  have h0re : (Complex.I * t * sgn ε a * (star v ⬝ᵥ (bᵀ *ᵥ v))).re = 0 := by
    rw [hq', hs']; simp [Complex.mul_re]
  have hre := congrArg Complex.re key
  rw [Complex.sub_re, h0re, Complex.re_ofReal_mul, Complex.zero_re, sub_zero] at hre
  have hdre : (star v ⬝ᵥ v).re = 0 := by
    rcases mul_eq_zero.mp hre with h | h
    · exact absurd h hc.ne'
    · exact h
  have hd0 : star v ⬝ᵥ v = 0 := Complex.ext hdre hd
  exact hv0 (dotProduct_star_self_eq_zero.mp hd0)

theorem dEv_apply (P : PX m n) (x v : Fin m → Fin n → ℂ) :
    dEv P x v = evX (∑ k, C (crd k v) * pderiv k P) x := by
  simp [dEv, evX_eq, mul_comm]

theorem evX_continuous (P : PX m n) : Continuous (evX P) :=
  continuous_iff_continuousAt.2 fun x => (hasFDerivAt_evX P x).continuousAt

theorem crd_wirt (a : Fin m) (j : Fin n) (k : Fin m × Fin n × Bool) :
    crd k (fun a' i' => if a' = a ∧ i' = j then (1 : ℂ) else 0) -
      Complex.I * crd k (fun a' i' => if a' = a ∧ i' = j then Complex.I else 0) =
      if k = (a, j, false) then 2 else 0 := by
  obtain ⟨a', i', bb⟩ := k
  rw [crd_apply, crd_apply]
  by_cases h : a' = a ∧ i' = j
  · obtain ⟨rfl, rfl⟩ := h
    cases bb <;> simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  · have h' : ¬ ((a', i', bb) = (a, j, false)) := by intro e; simp at e; exact h ⟨e.1, e.2.1⟩
    simp [h, h']

theorem dEv_wirt (P : PX m n) (x : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) :
    dEv P x (fun a' i' => if a' = a ∧ i' = j then (1 : ℂ) else 0) -
      Complex.I * dEv P x (fun a' i' => if a' = a ∧ i' = j then Complex.I else 0) =
      2 * evX (pderiv (a, j, false) P) x := by
  simp only [dEv, ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single (a, j, false)]
  · have := crd_wirt a j (a, j, false); simp only [if_true] at this
    rw [← this]; ring
  · intro k _ hk
    have := crd_wirt a j k; rw [if_neg hk] at this
    calc _ = evX (pderiv k P) x * (crd k (fun a' i' => if a' = a ∧ i' = j then (1 : ℂ) else 0) -
          Complex.I * crd k (fun a' i' => if a' = a ∧ i' = j then Complex.I else 0)) := by ring
      _ = 0 := by rw [this, mul_zero]
  · simp

theorem evX_pderiv_phiP (ε : Fin m → Bool) (c t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ)
    (a : Fin m) (j : Fin n) :
    evX (pderiv (a, j, false) (phiP ε c t b)) x = -∑ k, (Amat ε c t b a) k j * star (x a k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [phiP, map_neg, map_sum, pderiv_mul, pderiv_C, pderiv_X, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [evX, map_neg, map_sum, map_mul, Prod.ext_iff]
  simp only [mul_zero, mul_one, zero_mul, Pi.single_apply, Prod.mk.injEq, and_true, Bool.false_eq_true, and_false,
    if_false, map_zero, add_zero, zero_add]
  rw [neg_inj, Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj; simp [hj]
    · simp
  · intro a' _ ha; simp [ha]
  · simp

end PositivityTheory.Rg.Sw.WR.G
end
end

noncomputable section

open MeasureTheory Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

theorem wick_of (hI : IntegP) : Wick := by
  intro m n ε c t hc b hb M a i
  have hdet := amat_det_ne ε hc t hb a
  have : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  set E : (Fin m → Fin n → ℂ) → ℂ := fun x => Complex.exp (evX (phiP ε c t b) x) with hEdef
  have hsec : ∀ P, secN ε c t P b = ∫ x, evX P x * E x := by
    intro P; unfold secN; congr 1; funext x; rw [mul_assoc, exp_phiP]
  have hint : ∀ P, Integrable (fun x => evX P x * E x) := by
    intro P
    refine (hI m n c hc P).mono ?_ ?_
    · exact ((evX_continuous P).mul (evX_continuous (phiP ε c t b)).cexp).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      have hx : E x = gs c x * Complex.exp (Complex.I * t * (b * gramX ε x).trace) := (exp_phiP ε c t b x).symm
      rw [hx, ← mul_assoc, norm_mul _ (Complex.exp _), norm_exp_tr ε t b hb x, mul_one]
  have hE : ∀ x, HasFDerivAt E (E x • dEv (phiP ε c t b) x) x := fun x => (hasFDerivAt_evX (phiP ε c t b) x).cexp
  have hfd : ∀ x v, fderiv ℝ E x v = E x * evX (∑ k, C (crd k v) * pderiv k (phiP ε c t b)) x := by
    intro x v; rw [(hE x).fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul, dEv_apply]
  have hPd : ∀ (P : PX m n) x v, fderiv ℝ (evX P) x v = evX (∑ k, C (crd k v) * pderiv k P) x := by
    intro P x v; rw [(hasFDerivAt_evX P x).fderiv, dEv_apply]
  have hintD : ∀ (P : PX m n) v, Integrable (fun x => evX P x * fderiv ℝ E x v) := by
    intro P v
    refine (hint (P * ∑ k, C (crd k v) * pderiv k (phiP ε c t b))).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [hfd]; simp only [evX, map_mul]; ring
  have hintM : ∀ (P : PX m n) v, Integrable (fun x => fderiv ℝ (evX P) x v * E x) := by
    intro P v; simp_rw [hPd]; exact hint _
  have ibp : ∀ (P : PX m n) (v : Fin m → Fin n → ℂ),
      ∫ x, evX P x * fderiv ℝ E x v = -∫ x, fderiv ℝ (evX P) x v * E x := by
    intro P v
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hintM P v) (hintD P v) (hint P)
      (fun x _ => (hasFDerivAt_evX P x).differentiableAt) (fun x _ => (hE x).differentiableAt)
  have ibpW : ∀ j : Fin n, ∫ x, evX M x * (E x * evX (pderiv (a, j, false) (phiP ε c t b)) x) =
      -∫ x, evX (pderiv (a, j, false) M) x * E x := by
    intro j
    have hWE : ∀ x, fderiv ℝ E x (fun a' i' => if a' = a ∧ i' = j then (1 : ℂ) else 0) -
        Complex.I * fderiv ℝ E x (fun a' i' => if a' = a ∧ i' = j then Complex.I else 0) =
        2 * (E x * evX (pderiv (a, j, false) (phiP ε c t b)) x) := by
      intro x
      rw [(hE x).fderiv, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
      have := dEv_wirt (phiP ε c t b) x a j
      linear_combination (E x) * this
    have hpt : ∀ x, evX M x * (E x * evX (pderiv (a, j, false) (phiP ε c t b)) x) =
        (evX M x * fderiv ℝ E x (fun a' i' => if a' = a ∧ i' = j then (1 : ℂ) else 0) -
          Complex.I * (evX M x * fderiv ℝ E x (fun a' i' => if a' = a ∧ i' = j then Complex.I else 0))) / 2 := by
      intro x
      rw [eq_div_iff (two_ne_zero)]
      linear_combination (-(evX M x)) * hWE x
    have hptM : ∀ x, evX (pderiv (a, j, false) M) x * E x =
        (fderiv ℝ (evX M) x (fun a' i' => if a' = a ∧ i' = j then (1 : ℂ) else 0) * E x -
          Complex.I * (fderiv ℝ (evX M) x (fun a' i' => if a' = a ∧ i' = j then Complex.I else 0) * E x)) / 2 := by
      intro x
      rw [eq_div_iff (two_ne_zero), (hasFDerivAt_evX M x).fderiv]
      have := dEv_wirt M x a j
      linear_combination (-(E x)) * this
    simp_rw [hpt, hptM]
    rw [integral_div, integral_div, integral_sub (hintD M _) ((hintD M _).const_mul _),
      integral_sub (hintM M _) ((hintM M _).const_mul _), integral_const_mul, integral_const_mul, ibp, ibp]
    ring
  have hAA : Amat ε c t b a * (Amat ε c t b a)⁻¹ = 1 := Matrix.mul_nonsing_inv (Amat ε c t b a) (isUnit_iff_ne_zero.mpr hdet)
  have key : ∀ x, evX (X (a, i, true) * M) x * E x =
      -∑ j, (Amat ε c t b a)⁻¹ j i * (evX M x * (E x * evX (pderiv (a, j, false) (phiP ε c t b)) x)) := by
    intro x
    simp only [evX_pderiv_phiP]
    have h1 : ∀ k, ∑ j, Amat ε c t b a k j * (Amat ε c t b a)⁻¹ j i = if k = i then 1 else 0 := by
      intro k; rw [← Matrix.mul_apply, hAA, Matrix.one_apply]
    have h2 : ∑ j, (Amat ε c t b a)⁻¹ j i * (evX M x * (E x * -∑ k, Amat ε c t b a k j * star (x a k))) =
        -(evX M x * E x * ∑ k, star (x a k) * ∑ j, Amat ε c t b a k j * (Amat ε c t b a)⁻¹ j i) := by
      simp only [Finset.mul_sum, mul_neg, Finset.sum_neg_distrib, neg_inj]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h2]
    simp only [h1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, neg_neg]
    simp only [evX, map_mul, eval_X, if_true]
    ring
  rw [hsec]
  simp_rw [key]
  rw [integral_neg, MeasureTheory.integral_finsetSum]
  · simp only [integral_const_mul, ibpW, hsec]
    simp only [Finset.sum_neg_distrib, mul_neg, neg_neg]
  · intro j _
    refine Integrable.const_mul ?_ _
    refine (hint (M * pderiv (a, j, false) (phiP ε c t b))).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [evX, map_mul]; ring

end PositivityTheory.Rg.Sw.WR.G
end
end

namespace PositivityTheory.Rg.Sw.WR.G

theorem gauss : Gauss := gauss_of integP (wick_of integP) rot base

end PositivityTheory.Rg.Sw.WR.G
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsShift
noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.WR.T

open PositivityTheory.Rg.Sw

theorem cls_shift {n : ℕ} (s z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (y : E n) :
    ((dP y : ℝ) : ℂ) ^ (-z) * cls s 0 p q R y = cls s z p q R y := by
  simp only [cls, neg_zero, Complex.cpow_zero, one_mul]
  ring

theorem wr_of : Gauss → ClsBound → ClsGain → IBP → Integr → Dens → WRSt := by
  intro hG hB hGain hIBP hI hD m n ε c t hc ht P
  obtain ⟨R, hR⟩ := hG m n ε c t hc ht P
  have ht0 : t ≠ 0 := by
    rcases ht with rfl | rfl
    · exact hc.ne'
    · exact neg_ne_zero.2 hc.ne'
  have hs' : ((t / c : ℝ) : ℂ) = 1 ∨ ((t / c : ℝ) : ℂ) = -1 := by
    rcases ht with rfl | rfl
    · left; simp [hc.ne']
    · right; simp [hc.ne']
  generalize ((t / c : ℝ) : ℂ) = s at hR hs'
  have hs := hs'
  generalize (Finset.univ.filter fun a => ε a = true).card = p at hR
  generalize (Finset.univ.filter fun a => ε a = false).card = q at hR
  obtain ⟨-, hint⟩ := hI n
  obtain ⟨g, hgc, hgd, hgv⟩ := hD m n ε c t hc ht P (n ^ 2 + 1) (by
    push_cast
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith)
  refine ⟨g, hgc, hgd, fun β hβ => ?_⟩
  have hGN := fun N => hGain n s hs p q N R
  choose J a G hGc hGb hGeq using hGN
  choose CG hCG using hGb
  have hCG' : ∀ N j y, ‖G N j y‖ ≤ CG N * dP y ^ (-(((p + q + N : ℕ) : ℝ) / 2)) := fun N j y => by
    have := hCG N j y
    rwa [neg_div] at this
  set KK : ℂ := (-1) ^ n * ((-(Complex.I * t)) ^ n * (herm β).det)⁻¹ with hKK
  let Fj : (N : ℕ) → Fin (J N) → ℂ → ℂ := fun N j z => ∫ y, ((dP y : ℝ) : ℂ) ^ (-z) * G N j y * chr t β y
  let WN : ℕ → ℂ → ℂ := fun N z => KK ^ N * ∑ j, (a N j).eval z * Fj N j z
  let U : ℕ → Set ℂ := fun N => {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re + ((p + q + N : ℕ) : ℝ) / 2}
  let orig : ℂ → ℂ := fun z => ∫ y, ((dP y : ℝ) : ℂ) ^ (-z) * secN ε c t P (herm y) * chr t β y
  have hUopen : ∀ N, IsOpen (U N) := fun N =>
    isOpen_lt continuous_const (Complex.continuous_re.add continuous_const)
  have hWdiff : ∀ N, DifferentiableOn ℂ (WN N) (U N) := by
    intro N
    refine DifferentiableOn.const_mul (DifferentiableOn.fun_sum fun j _ => ?_) _
    exact (a N j).differentiable.differentiableOn.mul
      (holo hI t β (hGc N j) (((p + q + N : ℕ) : ℝ) / 2) (CG N) (hCG' N j))

  have hsum : ∀ N z, (n : ℝ) ^ 2 / 2 < z.re + ((p + q + N : ℕ) : ℝ) / 2 →
      ∫ y, (Delta^[N] (cls s z p q R)) y * chr t β y = ∑ j, (a N j).eval z * Fj N j z := by
    intro N z hz
    have e : (fun y => (Delta^[N] (cls s z p q R)) y * chr t β y) =
        fun y => ∑ j, (a N j).eval z * (((dP y : ℝ) : ℂ) ^ (-z) * G N j y * chr t β y) := by
      funext y
      rw [hGeq N z y, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [e, integral_finsetSum _ fun j _ => (integ_term hI t β (hGc N j) (hCG' N j) hz).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
  have hbig : ∀ N z, (n : ℝ) ^ 2 / 2 < z.re → WN N z = orig z := by
    intro N z hz
    have e1 : (fun y => ((dP y : ℝ) : ℂ) ^ (-z) * secN ε c t P (herm y) * chr t β y) =
        fun y => cls s z p q R y * chr t β y := by
      funext y
      rw [hR y, ← cls_shift s z]
    have hpq : (0 : ℝ) ≤ ((p : ℝ) + q) / 2 := by positivity
    have good : Good (cls s z p q R) := by
      refine ⟨(hB n s hs p q R z).1, fun L => ?_⟩
      obtain ⟨C, hC⟩ := (hB n s hs p q R z).2 L
      exact ⟨fun y => C * dP y ^ (-(z.re + ((p : ℝ) + q) / 2)), (hint _ (by linarith)).const_mul C, hC⟩
    have hz' : (n : ℝ) ^ 2 / 2 < z.re + ((p + q + N : ℕ) : ℝ) / 2 := by
      have : (0 : ℝ) ≤ ((p + q + N : ℕ) : ℝ) / 2 := by positivity
      linarith
    show KK ^ N * _ = ∫ y, ((dP y : ℝ) : ℂ) ^ (-z) * secN ε c t P (herm y) * chr t β y
    rw [e1, ibp_iter hIBP good t β ht0 hβ N, hsum N z hz']
  have agree : ∀ N N', N ≤ N' → Set.EqOn (WN N) (WN N') (U N) := by
    intro N N' hNN'
    have hsub : U N ⊆ U N' := fun z hz => by
      simp only [U, Set.mem_ofPred_eq] at hz ⊢
      have : ((p + q + N : ℕ) : ℝ) ≤ ((p + q + N' : ℕ) : ℝ) := by exact_mod_cast (by omega)
      linarith
    have hA : AnalyticOnNhd ℂ (WN N) (U N) := (hWdiff N).analyticOnNhd (hUopen N)
    have hA' : AnalyticOnNhd ℂ (WN N') (U N) := ((hWdiff N').mono hsub).analyticOnNhd (hUopen N)
    have hU : U N = {z : ℂ | (n : ℝ) ^ 2 / 2 - ((p + q + N : ℕ) : ℝ) / 2 < z.re} := by
      ext z
      simp only [U, Set.mem_ofPred_eq]
      constructor <;> intro h <;> linarith
    have hpre : IsPreconnected (U N) := by
      rw [hU]; exact (convex_halfSpace_re_gt _).isPreconnected
    set z1 : ℂ := (((n : ℝ) ^ 2 / 2 + 1 : ℝ) : ℂ) with hz1
    have hz1re : z1.re = (n : ℝ) ^ 2 / 2 + 1 := by rw [hz1, Complex.ofReal_re]
    have hz1U : z1 ∈ U N := by
      simp only [U, Set.mem_ofPred_eq, hz1re]
      have : (0 : ℝ) ≤ ((p + q + N : ℕ) : ℝ) / 2 := by positivity
      linarith
    have hO : IsOpen {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hz1O : z1 ∈ {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re} := by
      simp only [Set.mem_ofPred_eq, hz1re]; linarith
    have hev : WN N =ᶠ[𝓝 z1] WN N' :=
      Filter.eventuallyEq_of_mem (hO.mem_nhds hz1O) fun z hz => (hbig N z hz).trans (hbig N' z hz).symm
    exact hA.eqOn_of_preconnected_of_eventuallyEq hA' hpre hz1U hev
  have agree' : ∀ N N' z, z ∈ U N → z ∈ U N' → WN N z = WN N' z := by
    intro N N' z hz hz'
    rcases le_total N N' with h | h
    · exact agree N N' h hz
    · exact (agree N' N h hz').symm
  obtain ⟨Nf, hNfdef⟩ : ∃ Nf : ℂ → ℕ, ∀ z, Nf z = ⌈(n : ℝ) ^ 2 - 2 * z.re⌉₊ + 1 := ⟨_, fun _ => rfl⟩
  have hNf : ∀ z, z ∈ U (Nf z) := by
    intro z
    show (n : ℝ) ^ 2 / 2 < z.re + ((p + q + Nf z : ℕ) : ℝ) / 2
    rw [hNfdef z]
    have h1 := Nat.le_ceil ((n : ℝ) ^ 2 - 2 * z.re)
    push_cast
    have : (0 : ℝ) ≤ (p : ℝ) + q := by positivity
    linarith
  refine ⟨fun z => WN (Nf z) z, ?_, ⟨(n : ℝ) ^ 2 / 2, fun z hz => ⟨?_, ?_⟩⟩, ?_⟩
  · intro z0
    have hev : (fun z => WN (Nf z) z) =ᶠ[𝓝 z0] WN (Nf z0) :=
      Filter.eventuallyEq_of_mem ((hUopen (Nf z0)).mem_nhds (hNf z0)) fun z hz => agree' _ _ z (hNf z) hz
    exact (((hWdiff (Nf z0)).differentiableAt ((hUopen (Nf z0)).mem_nhds (hNf z0)))).congr_of_eventuallyEq hev
  · have e2 : (fun y => ((dP y : ℝ) : ℂ) ^ (-z) * secN ε c t P (herm y) * chr t β y) =
        fun y => ((dP y : ℝ) : ℂ) ^ (-z) * cls s 0 p q R y * chr t β y := by
      funext y; rw [hR y]
    rw [e2]
    obtain ⟨C, hC⟩ := (hB n s hs p q R 0).2 []
    have hC0 : ∀ y, ‖cls s 0 p q R y‖ ≤ C * dP y ^ (-(((p : ℝ) + q) / 2)) := by
      intro y
      have := hC y
      simp only [List.foldr_nil, Complex.zero_re, zero_add] at this
      exact this
    have hpq : (0 : ℝ) ≤ ((p : ℝ) + q) / 2 := by positivity
    exact integ_term hI t β (hB n s hs p q R 0).1.continuous hC0 (by linarith)
  · exact hbig (Nf z) z hz
  · have hN0 : Nf 0 = n ^ 2 + 1 := by
      rw [hNfdef, Complex.zero_re, mul_zero, sub_zero,
        show ((n : ℝ) ^ 2) = ((n ^ 2 : ℕ) : ℝ) by push_cast; ring, Nat.ceil_natCast]
    show WN (Nf 0) 0 = _
    rw [hN0, hgv β hβ]
    have hfun : (fun y => secN ε c t P (herm y)) = cls s 0 p q R := funext hR
    rw [hfun, hsum (n ^ 2 + 1) 0 (by
      simp only [Complex.zero_re, zero_add]
      push_cast
      have : (0 : ℝ) ≤ (p : ℝ) + q := by positivity
      linarith)]
    show KK ^ (n ^ 2 + 1) * _ = _
    rw [hKK]
    ring

end PositivityTheory.Rg.Sw.WR.T
end
end

namespace PositivityTheory.Rg.Sw.WR

theorem wr : WRSt :=
  T.wr_of G.gauss B.clsBound K.GB.clsGainB ibp I.integr (D.densOf3 G.gauss K.GB.clsGainB I.integr)

end PositivityTheory.Rg.Sw.WR
