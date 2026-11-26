module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SpectralSobolevSecondOrder
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLFrozen
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSELeibnizClsC

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSWordNF
open MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE.JSW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

theorem fderiv_apply_sm {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (v : ℂ) :
    ContDiffOn ℝ ∞ (fun ζ => fderiv ℝ g ζ v) U :=
  (hg.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

theorem dZ_sm {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (NF.dZ g) U := by
  unfold NF.dZ
  exact contDiffOn_const.mul ((fderiv_apply_sm hU hg 1).sub
    (contDiffOn_const.mul (fderiv_apply_sm hU hg Complex.I)))

theorem dZb_sm {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (NF.dZb g) U := by
  unfold NF.dZb
  exact contDiffOn_const.mul ((fderiv_apply_sm hU hg 1).add
    (contDiffOn_const.mul (fderiv_apply_sm hU hg Complex.I)))

theorem hasFDerivAt_exponential_character (s t : ℂ) :
    ∃ D : ℂ →L[ℝ] ℂ, HasFDerivAt (fsv s) D t ∧ D 1 = (s - conj s) * fsv s t ∧
      D Complex.I = Complex.I * (s + conj s) * fsv s t := by
  have h1 : HasFDerivAt (fun t' : ℂ => t') (ContinuousLinearMap.id ℝ ℂ) t := hasFDerivAt_id t
  have h2 : HasFDerivAt (fun t' : ℂ => conj t') Complex.conjCLE.toContinuousLinearMap t :=
    Complex.conjCLE.hasFDerivAt
  have h3 := ((h1.const_mul s).sub (h2.const_mul (conj s))).cexp
  refine ⟨_, h3, ?_, ?_⟩
  · simp [fsv]; ring
  · simp [fsv]; ring

theorem dZ_exponential_character (s t : ℂ) : NF.dZ (fsv s) t = s * fsv s t := by
  obtain ⟨D, hD, h1, hI⟩ := hasFDerivAt_exponential_character s t
  simp only [NF.dZ, hD.fderiv, h1, hI]
  linear_combination (-(1 / 2) * (s + conj s) * fsv s t) * Complex.I_sq

theorem dZbar_exponential_character (s t : ℂ) : NF.dZb (fsv s) t = -conj s * fsv s t := by
  obtain ⟨D, hD, h1, hI⟩ := hasFDerivAt_exponential_character s t
  simp only [NF.dZb, hD.fderiv, h1, hI]
  linear_combination ((1 / 2) * (s + conj s) * fsv s t) * Complex.I_sq

theorem fsv_diff (s t : ℂ) : DifferentiableAt ℝ (fsv s) t :=
  (hasFDerivAt_exponential_character s t).choose_spec.1.differentiableAt

theorem dZ_mul_leibniz {φ f : ℂ → ℂ} {c : ℂ} (hφ : DifferentiableAt ℝ φ c) (hf : DifferentiableAt ℝ f c) :
    NF.dZ (fun w => φ w * f w) c = NF.dZ φ c * f c + φ c * NF.dZ f c := by
  have h : HasFDerivAt (fun w => φ w * f w) _ c := hφ.hasFDerivAt.mul hf.hasFDerivAt
  unfold NF.dZ
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem dZbar_mul_leibniz {φ f : ℂ → ℂ} {c : ℂ} (hφ : DifferentiableAt ℝ φ c) (hf : DifferentiableAt ℝ f c) :
    NF.dZb (fun w => φ w * f w) c = NF.dZb φ c * f c + φ c * NF.dZb f c := by
  have h : HasFDerivAt (fun w => φ w * f w) _ c := hφ.hasFDerivAt.mul hf.hasFDerivAt
  unfold NF.dZb
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem mfs_dZ {m : ℂ → ℂ} {t : ℂ} (s : ℂ) (hm : DifferentiableAt ℝ m t) :
    NF.dZ (fun w => m w * fsv s w) t = (NF.dZ m t + s * m t) * fsv s t := by
  rw [dZ_mul_leibniz hm (fsv_diff s t), dZ_exponential_character]; ring

theorem mfs_dZb {m : ℂ → ℂ} {t : ℂ} (s : ℂ) (hm : DifferentiableAt ℝ m t) :
    NF.dZb (fun w => m w * fsv s w) t = (NF.dZb m t + -conj s * m t) * fsv s t := by
  rw [dZbar_mul_leibniz hm (fsv_diff s t), dZbar_exponential_character]; ring

theorem sm_diff {m : ℂ → ℂ} (hm : ContDiffOn ℝ ∞ m {0}ᶜ) {t : ℂ} (ht : t ≠ 0) : DifferentiableAt ℝ m t :=
  (hm.contDiffAt (isOpen_compl_singleton.mem_nhds ht)).differentiableAt (by simp)

section Wirt

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem wirt_comp_smul (l : Fin m) (φ : ℂ → ℂ) (v : (Fin m → ℂ) → E) (c : Fin m → ℂ)
    (hφ : DifferentiableAt ℝ φ (c l)) (hv : DifferentiableAt ℝ v c) :
    Formalism.QuantumDeterminants.wirt l (fun c' => φ (c' l) • v c') c = φ (c l) • Formalism.QuantumDeterminants.wirt l v c + NF.dZ φ (c l) • v c ∧
      Formalism.QuantumDeterminants.wirtBar l (fun c' => φ (c' l) • v c') c = φ (c l) • Formalism.QuantumDeterminants.wirtBar l v c + NF.dZb φ (c l) • v c := by
  have h1 : HasFDerivAt (fun c' : Fin m → ℂ => c' l)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℂ) l) c := hasFDerivAt_apply l c
  have h2 : HasFDerivAt (fun c' : Fin m → ℂ => φ (c' l))
      ((fderiv ℝ φ (c l)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℂ) l)) c :=
    hφ.hasFDerivAt.comp c h1
  have hp := h2.fun_smul hv.hasFDerivAt
  unfold Formalism.QuantumDeterminants.wirt Formalism.QuantumDeterminants.wirtBar NF.dZ NF.dZb
  rw [hp.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    Pi.single_eq_same]
  constructor
  · match_scalars <;> ring
  · match_scalars <;> ring

theorem wirt_fsum {ι : Type*} (u : Finset ι) (l : Fin m) (F : ι → (Fin m → ℂ) → E) (c : Fin m → ℂ)
    (hF : ∀ i ∈ u, DifferentiableAt ℝ (F i) c) :
    Formalism.QuantumDeterminants.wirt l (fun c' => ∑ i ∈ u, F i c') c = ∑ i ∈ u, Formalism.QuantumDeterminants.wirt l (F i) c ∧
      Formalism.QuantumDeterminants.wirtBar l (fun c' => ∑ i ∈ u, F i c') c = ∑ i ∈ u, Formalism.QuantumDeterminants.wirtBar l (F i) c := by
  have h : HasFDerivAt (fun c' => ∑ i ∈ u, F i c') (∑ i ∈ u, fderiv ℝ (F i) c) c :=
    HasFDerivAt.fun_sum fun i hi => (hF i hi).hasFDerivAt
  unfold Formalism.QuantumDeterminants.wirt Formalism.QuantumDeterminants.wirtBar
  rw [h.fderiv]
  refine ⟨?_, ?_⟩
  · simp [Finset.smul_sum]
    rw [← Finset.sum_sub_distrib, Finset.smul_sum]
  · simp [Finset.smul_sum, Finset.sum_add_distrib]

end Wirt

section Word

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem op_pt (X : ActualOps k r z z' π π') (l : Fin r) (i : Fin 6) (Ψ : RadSp k r z z' π π') (p : Fin r → ℂ)
    (g : Mx k r) : (X.op l i Ψ : Fn k r (Wq →L[ℂ] Wp)) p g =
      opL l i (fun c' => (Ψ : Fn k r (Wq →L[ℂ] Wp)) c' g) p := by
  rw [X.op_apply]; rfl

theorem wOp_cons (X : ActualOps k r z z' π π') (l : Fin r) (j : Fin 6) (js : List (Fin 6))
    (Ψ : RadSp k r z z' π π') : wOp X l (j :: js) Ψ = X.op l j (wOp X l js Ψ) := by
  simp [wOp, List.map_cons, List.prod_cons, Module.End.mul_apply]

theorem wOp_nil (X : ActualOps k r z z' π π') (l : Fin r) (Ψ : RadSp k r z z' π π') : wOp X l [] Ψ = Ψ := by
  simp [wOp]

theorem slice_diffAt (Ψ : RadSp k r z z' π π') (g : Mx k r) {p : Fin r → ℂ} (hp : p ∈ OmX r) :
    DifferentiableAt ℝ (fun c' => (Ψ : Fn k r (Wq →L[ℂ] Wp)) c' g) p :=
  (radSp_regular Ψ g p).1 hp

theorem isOpen_OmX' (m : ℕ) : IsOpen (OmX m) := by
  have : OmX m = ⋂ l : Fin m, (fun x : Fin m → ℂ => x l) ⁻¹' {0}ᶜ := by
    ext x; simp [OmX]
  rw [this]
  exact isOpen_iInter_of_finite fun l => isOpen_compl_singleton.preimage (continuous_apply l)

def NFP (X : ActualOps k r z z' π π') (l : Fin r) (s : ℂ) (Wv : Module.End ℂ (RadSp k r z z' π π'))
    (js : List (Fin 6)) : Prop :=
  ∃ (K : ℕ) (m : Fin K → ℂ → ℂ) (ab : Fin K → List (Fin 6)),
    (∀ i, ContDiffOn ℝ ∞ (m i) {0}ᶜ) ∧ (∀ i, ∀ j ∈ ab i, j = 0 ∨ j = 3) ∧
    ∀ (Φ : RadSp k r z z' π π') (p : Fin r → ℂ), p ∈ OmX r → ∀ g : Mx k r,
      (wOp X l js (Wv Φ) : Fn k r (Wq →L[ℂ] Wp)) p g =
        ∑ i, (m i (p l) * fsv s (p l)) • (wOp X l (ab i) Φ : Fn k r (Wq →L[ℂ] Wp)) p g

variable (X : ActualOps k r z z' π π') (l : Fin r) (s : ℂ) (Wv : Module.End ℂ (RadSp k r z z' π π'))

theorem nfp_nil (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) : NFP X l s Wv [] := by
  refine ⟨1, fun _ _ => 1, fun _ => [], fun _ => contDiffOn_const, fun _ j hj => by simp at hj, ?_⟩
  intro Φ p _ g
  simp only [wOp_nil, Fin.sum_univ_one, one_mul]
  exact hW Φ p g

theorem nfp_mul (j : Fin 6) (a : ℂ → ℂ) (ha : ContDiffOn ℝ ∞ a {0}ᶜ)
    (hop : ∀ (Ψ : RadSp k r z z' π π') (p : Fin r → ℂ) (g : Mx k r),
      (X.op l j Ψ : Fn k r (Wq →L[ℂ] Wp)) p g = a (p l) • (Ψ : Fn k r (Wq →L[ℂ] Wp)) p g)
    (js : List (Fin 6)) (h : NFP X l s Wv js) : NFP X l s Wv (j :: js) := by
  obtain ⟨K, m, ab, hm, hab, hE⟩ := h
  refine ⟨K, fun i t => a t * m i t, ab, fun i => ha.mul (hm i), hab, ?_⟩
  intro Φ p hp g
  rw [wOp_cons, hop, hE Φ p hp g, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]; ring_nf

theorem nfp_der (b : Bool) (js : List (Fin 6)) (h : NFP X l s Wv js) :
    NFP X l s Wv ((if b then (0 : Fin 6) else 3) :: js) := by
  obtain ⟨K, m, ab, hm, hab, hE⟩ := h
  let mL : Fin K → ℂ → ℂ := fun i t =>
    if b then t * (NF.dZ (m i) t + s * m i t) else star t * (NF.dZb (m i) t + -conj s * m i t)
  have hmL : ∀ i, ContDiffOn ℝ ∞ (mL i) {0}ᶜ := by
    intro i
    cases b
    · exact (Complex.conjCLE.contDiff.contDiffOn).mul
        ((dZb_sm isOpen_compl_singleton (hm i)).add (contDiffOn_const.mul (hm i)))
    · exact contDiffOn_id.mul ((dZ_sm isOpen_compl_singleton (hm i)).add (contDiffOn_const.mul (hm i)))
  refine ⟨K + K, Fin.append mL m, Fin.append ab (fun i => (if b then (0 : Fin 6) else 3) :: ab i),
    ?_, ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_)
    · rw [Fin.append_left]; exact hmL i
    · rw [Fin.append_right]; exact hm i
  · refine Fin.addCases (fun i => ?_) (fun i => ?_)
    · rw [Fin.append_left]; exact hab i
    · rw [Fin.append_right]
      intro j hj
      rcases List.mem_cons.1 hj with hj | hj
      · subst hj; cases b <;> simp
      · exact hab i j hj
  intro Φ p hp g

  set v : Fin K → (Fin r → ℂ) → (Wq →L[ℂ] Wp) := fun i c' => (wOp X l (ab i) Φ : Fn k r (Wq →L[ℂ] Wp)) c' g
    with hv
  have hvd : ∀ i, DifferentiableAt ℝ (v i) p := fun i => slice_diffAt _ g hp
  have hmd : ∀ i, DifferentiableAt ℝ (m i) (p l) := fun i => sm_diff (hm i) (hp l)
  have hqd : ∀ i, DifferentiableAt ℝ (fun t => m i t * fsv s t) (p l) := fun i => (hmd i).mul (fsv_diff s (p l))

  have hev : (fun c' => (wOp X l js (Wv Φ) : Fn k r (Wq →L[ℂ] Wp)) c' g) =ᶠ[𝓝 p]
      fun c' => ∑ i, (fun t => m i t * fsv s t) (c' l) • v i c' := by
    filter_upwards [(isOpen_OmX' r).mem_nhds hp] with c' hc'
    exact hE Φ c' hc' g
  have hsd : ∀ i ∈ (Finset.univ : Finset (Fin K)),
      DifferentiableAt ℝ (fun c' => (fun t => m i t * fsv s t) (c' l) • v i c') p := by
    intro i _
    have h1 : DifferentiableAt ℝ (fun c' : Fin r → ℂ => (fun t => m i t * fsv s t) (c' l)) p :=
      DifferentiableAt.comp (g := fun t => m i t * fsv s t) (f := fun c' : Fin r → ℂ => c' l) p (hqd i)
        (differentiableAt_apply l p)
    exact h1.smul (hvd i)
  have hW1 : Formalism.QuantumDeterminants.wirt l (fun c' => (wOp X l js (Wv Φ) : Fn k r (Wq →L[ℂ] Wp)) c' g) p =
      ∑ i, ((m i (p l) * fsv s (p l)) • Formalism.QuantumDeterminants.wirt l (v i) p + ((NF.dZ (m i) (p l) + s * m i (p l)) * fsv s (p l)) • v i p) := by
    have e1 : Formalism.QuantumDeterminants.wirt l (fun c' => (wOp X l js (Wv Φ) : Fn k r (Wq →L[ℂ] Wp)) c' g) p =
        Formalism.QuantumDeterminants.wirt l (fun c' => ∑ i, (fun t => m i t * fsv s t) (c' l) • v i c') p := by
      unfold Formalism.QuantumDeterminants.wirt; rw [hev.fderiv_eq]
    rw [e1, (wirt_fsum Finset.univ l _ p hsd).1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(wirt_comp_smul l _ (v i) p (hqd i) (hvd i)).1, mfs_dZ s (hmd i)]
  have hW2 : Formalism.QuantumDeterminants.wirtBar l (fun c' => (wOp X l js (Wv Φ) : Fn k r (Wq →L[ℂ] Wp)) c' g) p =
      ∑ i, ((m i (p l) * fsv s (p l)) • Formalism.QuantumDeterminants.wirtBar l (v i) p + ((NF.dZb (m i) (p l) + -conj s * m i (p l)) * fsv s (p l)) • v i p) := by
    have e1 : Formalism.QuantumDeterminants.wirtBar l (fun c' => (wOp X l js (Wv Φ) : Fn k r (Wq →L[ℂ] Wp)) c' g) p =
        Formalism.QuantumDeterminants.wirtBar l (fun c' => ∑ i, (fun t => m i t * fsv s t) (c' l) • v i c') p := by
      unfold Formalism.QuantumDeterminants.wirtBar; rw [hev.fderiv_eq]
    rw [e1, (wirt_fsum Finset.univ l _ p hsd).2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(wirt_comp_smul l _ (v i) p (hqd i) (hvd i)).2, mfs_dZb s (hmd i)]
  rw [wOp_cons, op_pt, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  have hR : ∀ i, (wOp X l ((if b then (0 : Fin 6) else 3) :: ab i) Φ : Fn k r (Wq →L[ℂ] Wp)) p g =
      if b then p l • Formalism.QuantumDeterminants.wirt l (v i) p else star (p l) • Formalism.QuantumDeterminants.wirtBar l (v i) p := by
    intro i
    rw [wOp_cons, op_pt]
    cases b
    · simp only [Bool.false_eq_true, if_false]
      show Formalism.QuantumDeterminants.pbOp l _ p = _
      unfold Formalism.QuantumDeterminants.pbOp; rw [if_pos hp]
    · simp only [if_true]
      show Formalism.QuantumDeterminants.pOp l _ p = _
      unfold Formalism.QuantumDeterminants.pOp; rw [if_pos hp]
  simp only [hR]
  cases b
  · simp only [Bool.false_eq_true, if_false, mL]
    show Formalism.QuantumDeterminants.pbOp l _ p = _
    unfold Formalism.QuantumDeterminants.pbOp
    rw [if_pos hp, hW2, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [v]
    module
  · simp only [if_true, mL]
    show Formalism.QuantumDeterminants.pOp l _ p = _
    unfold Formalism.QuantumDeterminants.pOp
    rw [if_pos hp, hW1, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [v]
    module

theorem nfp_all (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) : ∀ js, NFP X l s Wv js := by
  intro js
  induction js with
  | nil => exact nfp_nil X l s Wv hW
  | cons j js ih =>
    fin_cases j
    · exact nfp_der X l s Wv true js ih
    · exact nfp_mul X l s Wv 1 (fun t => t) contDiffOn_id (fun Ψ p g => by rw [op_pt]; rfl) js ih
    · exact nfp_mul X l s Wv 2 (fun t => t⁻¹) (contDiffOn_id.inv fun x hx => hx)
        (fun Ψ p g => by rw [op_pt]; rfl) js ih
    · exact nfp_der X l s Wv false js ih
    · exact nfp_mul X l s Wv 4 (fun t => star t) Complex.conjCLE.contDiff.contDiffOn
        (fun Ψ p g => by rw [op_pt]; rfl) js ih
    · exact nfp_mul X l s Wv 5 (fun t => (star t)⁻¹)
        (Complex.conjCLE.contDiff.contDiffOn.inv fun x hx => by simpa using hx)
        (fun Ψ p g => by rw [op_pt]; rfl) js ih

end Word

end Formalism.FourierDecayAlt.P.CutSE.JSW

namespace Formalism.FourierDecayAlt.P.CutSE

theorem spectral_word_normal_form : JSWordNF := by
  intro k r z z' Wp Wq _ _ _ _ _ _ π π' X l s Wv hW js
  obtain ⟨K, m, ab, hm, hab, hE⟩ := JSW.nfp_all X l s Wv hW js
  exact ⟨K, m, ab, fun i => (hm i).continuousOn, hab, hE⟩

end Formalism.FourierDecayAlt.P.CutSE
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSliceAsm
open MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

section Sob

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem hsVecR_dSl (U V : Wq →L[ℂ] Wp) :
    (hsVecR (Wp := Wp) (Wq := Wq)).comp (dSl U V) = Complex.reCLM.smulRight (hsVecR (U + V)) +
      Complex.imCLM.smulRight (hsVecR (Complex.I • (U - V))) := by
  refine ContinuousLinearMap.ext fun h => ?_
  obtain ⟨x, y, rfl⟩ : ∃ x y : ℝ, h = x + y * Complex.I := ⟨h.re, h.im, (Complex.re_add_im h).symm⟩
  simp only [ContinuousLinearMap.comp_apply, dSl_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smulRight_apply, Complex.reCLM_apply, Complex.imCLM_apply, hsVecR_apply, hsVec_add',
    hsVec_smul']
  have hs : B.hsVec (U - V) = B.hsVec U - B.hsVec V := by
    rw [sub_eq_add_neg, hsVec_add', ← neg_one_smul ℂ V, hsVec_smul', neg_one_smul, sub_eq_add_neg]
  rw [hs]
  simp only [map_add (f := _), map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im]
  simp only [mul_zero, mul_one, sub_zero, zero_add, add_zero, zero_sub]
  rw [← Complex.coe_smul, ← Complex.coe_smul]
  module

def Dx (X : ActualOps k r z z' π π') (l : Fin r) (Ξ : RadSp k r z z' π π') : RadSp k r z z' π π' :=
  dT X l Ξ + dTb X l Ξ

def Dy (X : ActualOps k r z z' π π') (l : Fin r) (Ξ : RadSp k r z z' π π') : RadSp k r z z' π π' :=
  Complex.I • (dT X l Ξ - dTb X l Ξ)

theorem sl_hasFDerivAt (X : ActualOps k r z z' π π') (l : Fin r) (Ξ : RadSp k r z z' π π') (y : Fin r → ℂ)
    (g : Mx k r) {s : ℂ} (hs : s ≠ 0) :
    HasFDerivAt (fun s' => hsVecR ((Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s') g))
      (Complex.reCLM.smulRight (hsVecR ((Dx X l Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)) +
        Complex.imCLM.smulRight (hsVecR ((Dy X l Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g))) s := by
  have h := hsVecR.hasFDerivAt.comp s (slice_hasFDerivAt X l Ξ y g hs)
  rw [hsVecR_dSl] at h
  simpa only [Dx, Dy, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sub, Pi.add_apply, Pi.smul_apply,
    Pi.sub_apply, Function.comp_def] using h

theorem sq_add_le_two {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 := norm_add_le a b
  have h2 := norm_nonneg (a + b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

theorem sq_sub_le_two {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have := sq_add_le_two a (-b)
  rwa [← sub_eq_add_neg, norm_neg] at this

def wd7 (X : ActualOps k r z z' π π') (l : Fin r) (Ξ : RadSp k r z z' π π') : Fin 7 → RadSp k r z z' π π' :=
  ![Ξ, dT X l Ξ, dTb X l Ξ, dT X l (dT X l Ξ), dTb X l (dT X l Ξ), dT X l (dTb X l Ξ), dTb X l (dTb X l Ξ)]

theorem hsVecR_Ismul (A : Wq →L[ℂ] Wp) : ‖hsVecR (Complex.I • A)‖ = ‖hsVecR A‖ := by
  rw [hsVecR_apply, hsVecR_apply, hsVec_smul', norm_smul, Complex.norm_I, one_mul]

theorem four_le_seven (X : ActualOps k r z z' π π') (l : Fin r) (Ξ : RadSp k r z z' π π') (p : Fin r → ℂ)
    (g : Mx k r) :
    ‖hsVecR ((Ξ : Fn k r (Wq →L[ℂ] Wp)) p g)‖ ^ 2 + ‖hsVecR ((Dx X l Ξ : Fn k r (Wq →L[ℂ] Wp)) p g)‖ ^ 2 +
      ‖hsVecR ((Dy X l Ξ : Fn k r (Wq →L[ℂ] Wp)) p g)‖ ^ 2 +
      ‖hsVecR ((Dx X l (Dy X l Ξ) : Fn k r (Wq →L[ℂ] Wp)) p g)‖ ^ 2 ≤
    4 * ∑ i, ‖hsVecR ((wd7 X l Ξ i : Fn k r (Wq →L[ℂ] Wp)) p g)‖ ^ 2 := by
  set a := fun Ψ : RadSp k r z z' π π' => hsVecR ((Ψ : Fn k r (Wq →L[ℂ] Wp)) p g) with ha
  have eA : ∀ Ψ Ψ' : RadSp k r z z' π π', a (Ψ + Ψ') = a Ψ + a Ψ' := fun Ψ Ψ' => by
    simp only [ha, Submodule.coe_add, Pi.add_apply, map_add (f := _)]
  have eS : ∀ Ψ Ψ' : RadSp k r z z' π π', a (Ψ - Ψ') = a Ψ - a Ψ' := fun Ψ Ψ' => by
    simp only [ha, Submodule.coe_sub, Pi.sub_apply, map_sub]
  have eI : ∀ Ψ : RadSp k r z z' π π', ‖a (Complex.I • Ψ)‖ = ‖a Ψ‖ := fun Ψ => by
    simp only [ha, Submodule.coe_smul, Pi.smul_apply]
    exact hsVecR_Ismul _
  have hx : ‖a (Dx X l Ξ)‖ ^ 2 ≤ 2 * ‖a (dT X l Ξ)‖ ^ 2 + 2 * ‖a (dTb X l Ξ)‖ ^ 2 := by
    rw [Dx, eA]; exact sq_add_le_two _ _
  have hy : ‖a (Dy X l Ξ)‖ ^ 2 ≤ 2 * ‖a (dT X l Ξ)‖ ^ 2 + 2 * ‖a (dTb X l Ξ)‖ ^ 2 := by
    rw [Dy, eI, eS]; exact sq_sub_le_two _ _
  have exy : Dx X l (Dy X l Ξ) = Complex.I • (dT X l (dT X l Ξ) - dT X l (dTb X l Ξ)) +
      Complex.I • (dTb X l (dT X l Ξ) - dTb X l (dTb X l Ξ)) := by
    simp only [Dx, Dy, map_smul, map_sub]
  have hxy : ‖a (Dx X l (Dy X l Ξ))‖ ^ 2 ≤ 4 * ‖a (dT X l (dT X l Ξ))‖ ^ 2 + 4 * ‖a (dT X l (dTb X l Ξ))‖ ^ 2 +
      4 * ‖a (dTb X l (dT X l Ξ))‖ ^ 2 + 4 * ‖a (dTb X l (dTb X l Ξ))‖ ^ 2 := by
    rw [exy, eA]
    refine (sq_add_le_two _ _).trans ?_
    rw [eI, eI, eS, eS]
    nlinarith [sq_sub_le_two (a (dT X l (dT X l Ξ))) (a (dT X l (dTb X l Ξ))),
      sq_sub_le_two (a (dTb X l (dT X l Ξ))) (a (dTb X l (dTb X l Ξ)))]
  simp only [Fin.sum_univ_seven, wd7, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, Matrix.cons_val_four]
  show ‖a Ξ‖ ^ 2 + ‖a (Dx X l Ξ)‖ ^ 2 + ‖a (Dy X l Ξ)‖ ^ 2 + ‖a (Dx X l (Dy X l Ξ))‖ ^ 2 ≤ _
  simp only [Matrix.cons_val]
  nlinarith [sq_nonneg ‖a Ξ‖, sq_nonneg ‖a (dT X l Ξ)‖, sq_nonneg ‖a (dTb X l Ξ)‖]

end Sob

section Dom

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem dT_lc (X : ActualOps k r z z' π π') (l : Fin r) {Ξ : RadSp k r z z' π π'} (h : Ξ ∈ lcSub k r z z' π π') :
    dT X l Ξ ∈ lcSub k r z z' π π' := by
  simp only [dT, Module.End.mul_apply]; exact op_lc X l 2 _ (op_lc X l 0 _ h)

theorem dTb_lc (X : ActualOps k r z z' π π') (l : Fin r) {Ξ : RadSp k r z z' π π'} (h : Ξ ∈ lcSub k r z z' π π') :
    dTb X l Ξ ∈ lcSub k r z z' π π' := by
  simp only [dTb, Module.End.mul_apply]; exact op_lc X l 5 _ (op_lc X l 3 _ h)

theorem seven_derivatives_preserve_compact (X : ActualOps k r z z' π π') (l : Fin r) {Ξ : RadSp k r z z' π π'} (h : Ξ ∈ lcSub k r z z' π π')
    (i : Fin 7) : wd7 X l Ξ i ∈ lcSub k r z z' π π' := by
  fin_cases i <;>
    first
    | exact h
    | exact dT_lc X l h
    | exact dTb_lc X l h
    | exact dT_lc X l (dT_lc X l h)
    | exact dTb_lc X l (dT_lc X l h)
    | exact dT_lc X l (dTb_lc X l h)
    | exact dTb_lc X l (dTb_lc X l h)

theorem pairAt_self_real (μ : Measure (Mt k r)) (Ξ : RadSp k r z z' π π') (p : Fin r → ℂ) :
    pairAt μ Ξ Ξ p = ((‖pairAt μ Ξ Ξ p‖ : ℝ) : ℂ) := by
  have e : pairAt μ Ξ Ξ p = ((∫ x : Mt k r, ‖B.hsVec ((Ξ : Fn k r (Wq →L[ℂ] Wp)) p (Matrix.of x))‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    unfold pairAt
    simp_rw [hsInner_self_ofRealI]
    exact integral_complex_ofReal
  rw [e, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun _ => by positivity)]

theorem wtI_real (i : Fin (r + 1)) (c' : Cf r i) : wtI i c' = ((‖wtI i c'‖ : ℝ) : ℂ) := by
  unfold wtI
  rw [Complex.norm_real, Real.norm_of_nonneg (Finset.prod_nonneg fun _ _ => by positivity)]

theorem norm_fs_self (μ : Measure (Mt k r)) (l : Fin r) (Ξ : RadSp k r z z' π π') (c : Fin r → ℂ) (t : ℂ) :
    ‖fs μ l Ξ Ξ c t‖ = ∫ c' : Cf r l.succ, ‖wtI l.succ c' * pairAt μ Ξ Ξ (glue l.succ (Function.update c l t) c')‖ := by
  unfold fs
  have e : (fun c' : Cf r l.succ => wtI l.succ c' * pairAt μ Ξ Ξ (glue l.succ (Function.update c l t) c')) =
      fun c' => ((‖wtI l.succ c' * pairAt μ Ξ Ξ (glue l.succ (Function.update c l t) c')‖ : ℝ) : ℂ) := by
    funext c'
    rw [norm_mul, Complex.ofReal_mul, ← wtI_real, ← pairAt_self_real]
  rw [e, integral_complex_ofReal, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]

theorem norm_hsInner_self (A : Wq →L[ℂ] Wp) : ‖B.hsInner A A‖ = ‖hsVecR A‖ ^ 2 := by
  rw [hsInner_self_ofRealI, Complex.norm_real, Real.norm_of_nonneg (by positivity), hsVecR_apply]

theorem pt_sob (hS : JSSob2) (t0 : ℂ) (δ : ℝ) (hδ : 0 < δ) (hB : ∀ s ∈ Metric.closedBall t0 (2 * δ), s ≠ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (X : ActualOps k r z z' π π') (l : Fin r) (Ξ : RadSp k r z z' π π') (y : Fin r → ℂ)
      (g : Mx k r), ∀ t ∈ Metric.ball t0 δ, ‖hsVecR ((Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l t) g)‖ ^ 2 ≤
        K * ∫ s in Metric.closedBall t0 (2 * δ),
          4 * ∑ i, ‖hsVecR ((wd7 X l Ξ i : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2 := by
  obtain ⟨K, hK⟩ := hS t0 δ hδ
  refine ⟨|K|, abs_nonneg _, fun X l Ξ y g t ht => ?_⟩
  have slc : ∀ Ψ : RadSp k r z z' π π', ContinuousOn
      (fun s => ‖hsVecR ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2)
      (Metric.closedBall t0 (2 * δ)) := fun Ψ s hs =>
    ((sl_hasFDerivAt X l Ψ y g (hB s hs)).continuousAt.norm.pow 2).continuousWithinAt
  have key := hK (PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp))
    (fun s => hsVecR ((Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g))
    (fun s => hsVecR ((Dx X l Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g))
    (fun s => hsVecR ((Dy X l Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g))
    (fun s => hsVecR ((Dx X l (Dy X l Ξ) : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g))
    (fun s hs => sl_hasFDerivAt X l Ξ y g (hB s hs))
    (fun s hs => ⟨_, sl_hasFDerivAt X l (Dy X l Ξ) y g (hB s hs)⟩)
    (fun s hs => (sl_hasFDerivAt X l (Dx X l Ξ) y g (hB s hs)).continuousAt.continuousWithinAt)
    (fun s hs => (sl_hasFDerivAt X l (Dx X l (Dy X l Ξ)) y g (hB s hs)).continuousAt.continuousWithinAt) t ht
  refine key.trans ?_
  have hI4 : IntegrableOn (fun s => ‖hsVecR ((Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2 +
      ‖hsVecR ((Dx X l Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2 +
      ‖hsVecR ((Dy X l Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2 +
      ‖hsVecR ((Dx X l (Dy X l Ξ) : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2)
      (Metric.closedBall t0 (2 * δ)) :=
    ((((slc Ξ).add (slc _)).add (slc _)).add (slc _)).integrableOn_compact (isCompact_closedBall _ _)
  have hI7 : IntegrableOn (fun s => 4 * ∑ i, ‖hsVecR ((wd7 X l Ξ i : Fn k r (Wq →L[ℂ] Wp))
      (Function.update y l s) g)‖ ^ 2) (Metric.closedBall t0 (2 * δ)) :=
    (continuousOn_const.mul (continuousOn_finsetSum _ fun i _ => slc _)).integrableOn_compact
      (isCompact_closedBall _ _)
  calc K * ∫ s in Metric.closedBall t0 (2 * δ), (‖hsVecR ((Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2 +
        ‖hsVecR ((Dx X l Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2 +
        ‖hsVecR ((Dy X l Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2 +
        ‖hsVecR ((Dx X l (Dy X l Ξ) : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2)
      ≤ |K| * ∫ s in Metric.closedBall t0 (2 * δ), (‖hsVecR ((Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2 +
        ‖hsVecR ((Dx X l Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2 +
        ‖hsVecR ((Dy X l Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2 +
        ‖hsVecR ((Dx X l (Dy X l Ξ) : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self K) (setIntegral_nonneg measurableSet_closedBall fun s _ => by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (setIntegral_mono_on hI4 hI7 measurableSet_closedBall
        fun s _ => four_le_seven X l Ξ _ g) (abs_nonneg K)

end Dom

section Main

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem slDom_of_loc (hS : JSSob2) (hM : JSMeas) (X : ActualOps k r z z' π π') (μ : Measure (Mt k r))
    (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (l : Fin r) (c : Fin r → ℂ) (Φ : RadSp k r z z' π π')
    (hΦ : Φ ∈ lcSub k r z z' π π') (t0 : ℂ) (ht0 : t0 ≠ 0)
    (hloc : ∀ i : Fin 7, ∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ, ∀ t ∈ Metric.ball t0 ε,
      LevelSquareIntegrable μ l.succ (wd7 X l Φ i) (Function.update c l t) ∧ ‖fs μ l (wd7 X l Φ i) (wd7 X l Φ i) c t‖ ≤ M) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ F : Cf r l.succ → ℝ, Integrable F ∧
      ∀ t ∈ Metric.ball t0 ε, ∀ c' : Cf r l.succ,
        ‖wtI l.succ c' * pairAt μ Φ Φ (glue l.succ (Function.update c l t) c')‖ ≤ F c' := by
  have : SFinite μ := sfinite_of_isHaarOn _ μ hμ
  choose ε hε M hMb using hloc
  set ε0 := Finset.univ.inf' Finset.univ_nonempty ε with hε0def
  have hε0 : 0 < ε0 := (Finset.lt_inf'_iff _).2 fun i _ => hε i
  have hε0i : ∀ i, ε0 ≤ ε i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  have ht0n : 0 < ‖t0‖ := norm_pos_iff.2 ht0
  set δ : ℝ := min (‖t0‖ / 4) (ε0 / 4) with hδdef
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ1 : δ ≤ ‖t0‖ / 4 := min_le_left _ _
  have hδ2 : δ ≤ ε0 / 4 := min_le_right _ _
  set B' := Metric.closedBall t0 (2 * δ) with hB'
  have hB : ∀ s ∈ B', s ≠ 0 := by
    intro s hs h0
    rw [h0, Metric.mem_closedBall, dist_zero_left] at hs
    linarith
  have hBε : ∀ s ∈ B', ∀ i, s ∈ Metric.ball t0 (ε i) := by
    intro s hs i
    rw [Metric.mem_closedBall] at hs
    rw [Metric.mem_ball]
    linarith [hε0i i]
  obtain ⟨K, hK0, hK⟩ := pt_sob (k := k) (r := r) (z := z) (z' := z') (π := π) (π' := π') hS t0 δ hδ hB
  have hwlc := seven_derivatives_preserve_compact X l hΦ

  set P : Fin 7 → ℂ × Cf r l.succ → ℂ := fun i q =>
    pairAt μ (wd7 X l Φ i) (wd7 X l Φ i) (glue l.succ (Function.update c l q.1) q.2) with hPdef
  have hPm : ∀ i, StronglyMeasurable (P i) := fun i =>
    (hM k r z z' Wp Wq π π' l c (wd7 X l Φ i) (wd7 X l Φ i)).stronglyMeasurable.integral_prod_right'
  have hPcont : ∀ i c', ContinuousOn (fun s => ‖P i (s, c')‖) B' := by
    intro i c' s hs
    simp only [hPdef, glue_succ_update_eq]
    by_cases hyO : Function.update (glue l.succ c c') l s ∈ OmX r
    · exact ((pairAt_hasFDerivAt X μ hμ l _ _ (hwlc i) (hwlc i) _ (hB s hs) hyO).continuousAt.norm).continuousWithinAt
    · refine (continuousWithinAt_const (b := (0 : ℝ))).congr (fun s' _ => ?_) ?_
      · rw [pairAt_off _ _ _ _ (omX_update_any _ l (hB s hs) hyO s'), norm_zero]
      · rw [pairAt_off _ _ _ _ hyO, norm_zero]
  have hPint : ∀ i c', IntegrableOn (fun s => ‖P i (s, c')‖) B' := fun i c' =>
    (hPcont i c').integrableOn_compact (isCompact_closedBall _ _)
  set F : Cf r l.succ → ℝ := fun c' => 4 * K * (‖wtI l.succ c'‖ * ∑ i, ∫ s in B', ‖P i (s, c')‖) with hF
  have hS0 : ∀ c', 0 ≤ ∑ i, ∫ s in B', ‖P i (s, c')‖ := fun c' =>
    Finset.sum_nonneg fun i _ => setIntegral_nonneg measurableSet_closedBall fun s _ => norm_nonneg _
  have hF0 : ∀ c', 0 ≤ F c' := fun c' => by
    have := hS0 c'
    simp only [hF]
    positivity
  refine ⟨δ, hδ, F, ?_, ?_⟩
  ·
    have hFm : Measurable F := by
      simp only [hF]
      refine measurable_const.mul ((wtI_measurable l.succ).norm.mul (Finset.measurable_sum _ fun i _ => ?_))
      exact ((hPm i).norm.integral_prod_left (μ := volume.restrict B')).measurable
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hF0)]
    have hper : ∀ c', ENNReal.ofReal (F c') = ENNReal.ofReal (4 * K) *
        ∑ i, ∫⁻ s in B', ENNReal.ofReal ‖wtI l.succ c' * P i (s, c')‖ := by
      intro c'
      simp only [hF]
      rw [ENNReal.ofReal_mul (by positivity), Finset.mul_sum,
        ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (norm_nonneg _)
          (setIntegral_nonneg measurableSet_closedBall fun s _ => norm_nonneg _)]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal ((hPint i c').const_mul _)
        (Eventually.of_forall fun _ => by positivity)]
      simp only [norm_mul]
    have hswap : ∀ i, ∫⁻ c', ∫⁻ s in B', ENNReal.ofReal ‖wtI l.succ c' * P i (s, c')‖ =
        ∫⁻ s in B', ∫⁻ c', ENNReal.ofReal ‖wtI l.succ c' * P i (s, c')‖ := by
      intro i
      refine lintegral_lintegral_swap ?_
      have hm : Measurable (fun q : Cf r l.succ × ℂ => ENNReal.ofReal ‖wtI l.succ q.1 * P i (q.2, q.1)‖) :=
        ENNReal.measurable_ofReal.comp
          (((wtI_measurable l.succ).comp measurable_fst).mul ((hPm i).measurable.comp measurable_swap)).norm
      exact hm.aemeasurable
    have hinner : ∀ i, ∀ s ∈ B', ∫⁻ c', ENNReal.ofReal ‖wtI l.succ c' * P i (s, c')‖ ≤ ENNReal.ofReal (M i) := by
      intro i s hs
      have hL := (hMb i s (hBε s hs i)).1
      rw [← ofReal_integral_eq_lintegral_ofReal hL.norm (Eventually.of_forall fun _ => norm_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← norm_fs_self]
      exact (hMb i s (hBε s hs i)).2
    calc ∫⁻ c', ENNReal.ofReal (F c') = ENNReal.ofReal (4 * K) *
          ∑ i, ∫⁻ s in B', ∫⁻ c', ENNReal.ofReal ‖wtI l.succ c' * P i (s, c')‖ := by
          simp_rw [hper]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          rw [lintegral_finsetSum']
          · exact Finset.sum_congr rfl fun i _ => hswap i
          · intro i _
            exact ((ENNReal.measurable_ofReal.comp (((wtI_measurable l.succ).comp measurable_fst).mul
              ((hPm i).measurable.comp measurable_swap)).norm).lintegral_prod_right'
                (ν := volume.restrict B')).aemeasurable
      _ ≤ ENNReal.ofReal (4 * K) * ∑ i, ∫⁻ s in B', ENNReal.ofReal (M i) := by
          exact mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ =>
            setLIntegral_mono' measurableSet_closedBall fun s hs => hinner i s hs)
      _ < ⊤ := by
          refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.2 fun i _ => ?_)
          rw [setLIntegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top
  ·
    intro t ht c'
    rw [glue_succ_update_eq, norm_mul]
    set y := glue l.succ c c' with hy
    by_cases hyO : Function.update y l t ∈ OmX r
    swap
    · rw [pairAt_off _ _ _ _ hyO, norm_zero, mul_zero]; exact hF0 c'
    have hP : ‖pairAt μ Φ Φ (Function.update y l t)‖ ≤ 4 * K * ∑ i, ∫ s in B', ‖P i (s, c')‖ := by
      have hx_int : ∀ Ξ ∈ lcSub k r z z' π π', ∀ s, Integrable (fun x : Mt k r =>
          ‖hsVecR ((Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) (Matrix.of x))‖ ^ 2) μ := by
        intro Ξ hΞ s
        have := (int_lc μ hμ hΞ hΞ (Function.update y l s)).norm
        simpa only [norm_hsInner_self] using this
      have hpair : ∀ Ξ : RadSp k r z z' π π', ∀ s, ‖pairAt μ Ξ Ξ (Function.update y l s)‖ =
          ∫ x, ‖hsVecR ((Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) (Matrix.of x))‖ ^ 2 ∂μ := by
        intro Ξ s; rw [norm_pairAt_selfI]; simp only [norm_hsInner_self]
      have hPy : ∀ i s, ‖P i (s, c')‖ = ‖pairAt μ (wd7 X l Φ i) (wd7 X l Φ i) (Function.update y l s)‖ := by
        intro i s; simp only [hPdef, glue_succ_update_eq, hy]
      have hsint : ∀ x : Mt k r, IntegrableOn (fun s => 4 * ∑ i, ‖hsVecR ((wd7 X l Φ i : Fn k r (Wq →L[ℂ] Wp))
          (Function.update y l s) (Matrix.of x))‖ ^ 2) B' := fun x =>
        (continuousOn_const.mul (continuousOn_finsetSum _ fun i _ => fun s hs =>
          ((sl_hasFDerivAt X l (wd7 X l Φ i) y (Matrix.of x) (hB s hs)).continuousAt.norm.pow 2).continuousWithinAt)
          ).integrableOn_compact (isCompact_closedBall _ _)
      have hmeas : Measurable (fun q : Mt k r × ℂ => ENNReal.ofReal (4 * ∑ i, ‖hsVecR ((wd7 X l Φ i :
          Fn k r (Wq →L[ℂ] Wp)) (Function.update y l q.2) (Matrix.of q.1))‖ ^ 2)) := by
        refine ENNReal.measurable_ofReal.comp (measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_))
        have hm := hM k r z z' Wp Wq π π' l c (wd7 X l Φ i) (wd7 X l Φ i)
        have hc : Measurable (fun q : Mt k r × ℂ => (((q.2, c') : ℂ × Cf r l.succ), q.1)) := by fun_prop
        have e : (fun q : Mt k r × ℂ => ‖hsVecR ((wd7 X l Φ i : Fn k r (Wq →L[ℂ] Wp))
            (Function.update y l q.2) (Matrix.of q.1))‖ ^ 2) = fun q => ‖B.hsInner
              ((wd7 X l Φ i : Fn k r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l q.2) c') (Matrix.of q.1))
              ((wd7 X l Φ i : Fn k r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l q.2) c') (Matrix.of q.1))‖ := by
          funext q; rw [glue_succ_update_eq, norm_hsInner_self]
        rw [e]
        exact (hm.comp hc).norm
      have hinner : ∀ s, ∫⁻ x, ENNReal.ofReal (4 * ∑ i, ‖hsVecR ((wd7 X l Φ i : Fn k r (Wq →L[ℂ] Wp))
          (Function.update y l s) (Matrix.of x))‖ ^ 2) ∂μ = ENNReal.ofReal (4 * ∑ i, ‖P i (s, c')‖) := by
        intro s
        rw [← ofReal_integral_eq_lintegral_ofReal
          ((integrable_finsetSum _ fun i _ => hx_int _ (hwlc i) s).const_mul 4)
          (Eventually.of_forall fun _ => by positivity)]
        congr 1
        rw [integral_const_mul, integral_finsetSum _ fun i _ => hx_int _ (hwlc i) s]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by rw [hPy, hpair]
      have hRHS0 : 0 ≤ 4 * K * ∑ i, ∫ s in B', ‖P i (s, c')‖ := by
        have := hS0 c'
        positivity
      rw [← ENNReal.ofReal_le_ofReal_iff hRHS0, hpair Φ t,
        ofReal_integral_eq_lintegral_ofReal (hx_int Φ hΦ t) (Eventually.of_forall fun _ => by positivity)]
      calc ∫⁻ x, ENNReal.ofReal (‖hsVecR ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l t) (Matrix.of x))‖ ^ 2) ∂μ
          ≤ ∫⁻ x, (ENNReal.ofReal K * ∫⁻ s in B', ENNReal.ofReal (4 * ∑ i, ‖hsVecR ((wd7 X l Φ i :
              Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) (Matrix.of x))‖ ^ 2)) ∂μ := by
            refine lintegral_mono fun x => ?_
            rw [← ofReal_integral_eq_lintegral_ofReal (hsint x) (Eventually.of_forall fun _ => by positivity),
              ← ENNReal.ofReal_mul hK0]
            exact ENNReal.ofReal_le_ofReal (hK X l Φ y (Matrix.of x) t ht)
        _ = ENNReal.ofReal K * ∫⁻ s in B', ∫⁻ x, ENNReal.ofReal (4 * ∑ i, ‖hsVecR ((wd7 X l Φ i :
              Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) (Matrix.of x))‖ ^ 2) ∂μ := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            congr 1
            exact lintegral_lintegral_swap hmeas.aemeasurable
        _ = ENNReal.ofReal K * ∫⁻ s in B', ENNReal.ofReal (4 * ∑ i, ‖P i (s, c')‖) := by
            simp_rw [hinner]
        _ = ENNReal.ofReal (4 * K * ∑ i, ∫ s in B', ‖P i (s, c')‖) := by
            rw [← ofReal_integral_eq_lintegral_ofReal
              ((integrable_finsetSum _ fun i _ => hPint i c').const_mul 4)
              (Eventually.of_forall fun _ => mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => norm_nonneg _)),
              ← ENNReal.ofReal_mul hK0]
            congr 1
            rw [integral_const_mul, integral_finsetSum _ fun i _ => hPint i c']
            ring
    calc ‖wtI l.succ c'‖ * ‖pairAt μ Φ Φ (Function.update y l t)‖
        ≤ ‖wtI l.succ c'‖ * (4 * K * ∑ i, ∫ s in B', ‖P i (s, c')‖) :=
          mul_le_mul_of_nonneg_left hP (norm_nonneg _)
      _ = F c' := by simp only [hF]; ring

end Main

section Gen

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def wlist7 : Fin 7 → List (Fin 6) :=
  ![[], [2, 0], [5, 3], [2, 0, 2, 0], [5, 3, 2, 0], [2, 0, 5, 3], [5, 3, 5, 3]]

theorem seven_derivatives_of_word_operator (X : ActualOps k r z z' π π') (l : Fin r) (js : List (Fin 6)) (Ψ : RadSp k r z z' π π')
    (i : Fin 7) : wd7 X l (wOp X l js Ψ) i = wOp X l (wlist7 i ++ js) Ψ := by
  fin_cases i <;>
    simp [wd7, wlist7, wOp, dT, dTb, List.map_cons, List.prod_cons, Module.End.mul_apply, mul_assoc]

theorem wOp_lcJ (X : ActualOps k r z z' π π') (l : Fin r) (js : List (Fin 6)) :
    ∀ Ψ ∈ lcSub k r z z' π π', wOp X l js Ψ ∈ lcSub k r z z' π π' := by
  induction js with
  | nil => intro Ψ h; simpa [wOp] using h
  | cons j js ih =>
    intro Ψ h
    have e : wOp X l (j :: js) Ψ = X.op l j (wOp X l js Ψ) := by
      simp [wOp, List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [e]
    exact op_lc X l j _ (ih Ψ h)

end Gen

theorem jSliceGenC_of_sob2_meas_locality (hS : JSSob2) (hM : JSMeas) (hL : SpectralL2Locality) : JSliceGenC := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' l hl c hc Ψ hΨ
  refine ⟨hΨ.1, fun js t0 ht0 => ?_⟩
  refine slDom_of_loc hS hM X μ hD.2.1 l c (wOp X l js Ψ) (wOp_lcJ X l js Ψ hΨ.1) t0 ht0 fun i => ?_
  rw [seven_derivatives_of_word_operator]
  exact hL Wp Wq S P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' l hl c hc Ψ hΨ (wlist7 i ++ js) t0 ht0

end Formalism.FourierDecayAlt.P.CutSE
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSMeas
open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section MeasJ

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def glueMapS (l : Fin r) (c : Fin r → ℂ) (q : (ℂ × Cf r l.succ) × Mt k r) : (Fin r → ℂ) × Mx k r :=
  (glue l.succ (Function.update c l q.1.1) q.1.2, Matrix.of q.2)

theorem glueMapS_continuous (l : Fin r) (c : Fin r → ℂ) : Continuous (glueMapS (k := k) l c) := by
  unfold glueMapS
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi fun m => ?_
    by_cases h : (l.succ : Fin (r + 1)).val ≤ m.val
    · simp only [glue, h, dif_pos]
      exact (continuous_apply _).comp (continuous_snd.comp continuous_fst)
    · simp only [glue, h, dif_neg, not_false_eq_true, Function.update_apply]
      by_cases hm : m = l
      · simp only [hm, eq_self_iff_true, if_true, ite_true] <;> fun_prop
      · simp only [hm, if_false, ite_false] <;> fun_prop
  · exact continuous_matrix fun i j => by simp only [Matrix.of_apply]; fun_prop

theorem measurableSet_glueMapS_DomR (l : Fin r) (c : Fin r → ℂ) :
    MeasurableSet (glueMapS (k := k) l c ⁻¹' DomR k r z z') := by
  rw [DomR_eq, Set.preimage_inter]
  exact ((Formalism.FourierDecayAlt.P.Qx5.isOpen_OpR k r z z').preimage (glueMapS_continuous l c)).measurableSet.inter
    (((Formalism.FourierDecayAlt.P.Qx5.Glev_closed (Fin.last r)).preimage continuous_snd).preimage
      (glueMapS_continuous l c)).measurableSet

end MeasJ

theorem spectral_measurability : JSMeas := by
  intro k r z z' Wp Wq _ _ _ _ _ _ π π' l c Φ Ψ
  have hmaps : Set.MapsTo (glueMapS (k := k) l c) (glueMapS (k := k) l c ⁻¹' DomR k r z z') (DomR k r z z') :=
    fun q hq => hq
  have hΦc := (radSp_continuousOn Φ).comp (glueMapS_continuous l c).continuousOn hmaps
  have hΨc := (radSp_continuousOn Ψ).comp (glueMapS_continuous l c).continuousOn hmaps
  refine measurable_of_continuousOn_zero (measurableSet_glueMapS_DomR l c)
    ((Formalism.FourierDecayAlt.P.B6.hsInner_continuous (Wp := Wp) (Wq := Wq)).comp_continuousOn (hΦc.prodMk hΨc)) ?_
  intro q hq
  have h0 : (Φ : Fn k r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l q.1.1) q.1.2) (Matrix.of q.2) = 0 :=
    radSp_zero_off Φ hq
  show B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l q.1.1) q.1.2) (Matrix.of q.2)) _ = 0
  rw [h0, Formalism.FourierDecayAlt.P.B6.hilbert_schmidt_inner_basis_sum]
  simp

end Formalism.FourierDecayAlt.P.CutSE
end
end

namespace Formalism.FourierDecayAlt.P.CutSE

theorem jSliceGenC_of_radLoc (hR : JSRadLoc) : JSliceGenC :=
  jSliceGenC_of_sob2_meas_locality spectral_sobolev_second_order spectral_measurability (jSL2Loc_of spectral_word_normal_form hR)

theorem leibnizCls_of_radLoc (hR : JSRadLoc) : LeibnizCls :=
  leibnizCls_of_jSliceC (jSliceGenC_of_radLoc hR)

theorem densSmoothCls_of_radLoc (hR : JSRadLoc) : DensSmoothCls :=
  densSmoothCls_of_jSliceC (jSliceGenC_of_radLoc hR)

end Formalism.FourierDecayAlt.P.CutSE
