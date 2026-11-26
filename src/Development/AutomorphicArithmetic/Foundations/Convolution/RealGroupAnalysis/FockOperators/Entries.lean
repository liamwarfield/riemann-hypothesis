module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.OpsEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.StepInv

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.AnnVac
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private noncomputable def kA (δ : F) : Fin 4 → A F := ![1, 1, 2, -2 * rt δ]

private noncomputable def qG (δ : F) (v : V4 F) : A F := v 0 ^ 2 + v 1 ^ 2 + 2 * (v 2 ^ 2 - rt δ * v 3 ^ 2)

private theorem kap_eq (δ : F) (w : InfinitePlace F) (i : Fin 4) :
    kap δ w i = ((TR.pInf F (kA δ i) w : ℝ) : ℂ) := by
  have h2 : TR.pInf F (2 : A F) w = 2 := by
    rw [map_ofNat]
    rfl
  fin_cases i <;> simp [kap, kA, cw, h2]

private theorem form_step (δ : F) (v : V4 F) (i : Fin 4) (s : A F) :
    qG δ (v + Pi.single i s) = qG δ v + kA δ i * (2 * v i * s + s * s) := by
  fin_cases i <;> simp [qG, kA, Pi.single_apply] <;> ring

private theorem sum_step (w : InfinitePlace F) (K b : InfinitePlace F → ℝ) (t : ℝ) :
    ∑ w', (K * (2 * b * Pi.single w t + Pi.single w t * Pi.single w t) : InfinitePlace F → ℝ) w' =
      K w * (2 * b w * t + t * t) := by
  rw [Finset.sum_eq_single w]
  · simp
  · intro b' _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ w) h

private theorem gauss_step (δ : F) (v : V4 F) (i : Fin 4) (w : InfinitePlace F) (t : ℝ) :
    gauss δ (v + Pi.single i (at1 w t)) =
      gauss δ v * Complex.exp (-((Real.pi : ℂ) * kap δ w i * (2 * cw w (v i) * t + t * t))) := by
  have hp : TR.pInf F (at1 w t) = Pi.single w t := (atLaws F w).2.2.1 t
  have hs : (∑ w', TR.pInf F (qG δ (v + Pi.single i (at1 w t))) w' : ℝ) =
      (∑ w', TR.pInf F (qG δ v) w') +
        TR.pInf F (kA δ i) w * (2 * TR.pInf F (v i) w * t + t * t) := by
    rw [form_step, ← sum_step w (TR.pInf F (kA δ i)) (TR.pInf F (v i)) t,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w' _ => ?_
    have h2 : TR.pInf F (2 : A F) = 2 := by rw [map_ofNat]
    simp only [map_add (f := _), map_mul, hp, h2, Pi.add_apply]
  have hg : ∀ u : V4 F, gauss δ u =
      Complex.exp (-(Real.pi : ℂ) * ((∑ w', TR.pInf F (qG δ u) w' : ℝ) : ℂ)) := by
    intro u
    unfold gauss qG
    rfl
  rw [hg, hg, hs, ← Complex.exp_add, kap_eq]
  congr 1
  simp only [cw]
  push_cast
  ring

private theorem cw_step (v : V4 F) (i : Fin 4) (w : InfinitePlace F) (t : ℝ) :
    cw w ((v + Pi.single i (at1 w t) : V4 F) i) = cw w (v i) + t := by
  have hp : TR.pInf F (at1 w t) = Pi.single w t := (atLaws F w).2.2.1 t
  simp [cw, hp]

private theorem line_step (δ : F) (O : Ops F) (φ : S4 F)
    (h : ∀ w i, O.d w i φ = (-2 * Real.pi * kap δ w i) • O.x w i φ)
    (v : V4 F) (i : Fin 4) (w : InfinitePlace F) (t : ℝ) :
    φ.1 (v + Pi.single i (at1 w t)) * gauss δ v = φ.1 v * gauss δ (v + Pi.single i (at1 w t)) := by
  set a : ℂ := cw w (v i) with ha
  set κ : ℂ := kap δ w i with hκ
  let f : ℝ → ℂ := fun t => φ.1 (v + Pi.single i (at1 w t))
  let X : ℝ → ℂ := fun t => (Real.pi : ℂ) * κ * (2 * a * t + t * t)
  have hf : ∀ t, HasDerivAt f (-2 * Real.pi * κ * (a + t) * f t) t := by
    intro t
    have h0 := O.d_spec w i φ (v + Pi.single i (at1 w t))
    have e : (fun s : ℝ => φ.1 (v + Pi.single i (at1 w t) + Pi.single i (at1 w s))) = fun s => f (t + s) := by
      funext s
      simp only [f]
      rw [(atLaws F w).2.2.2.1 t s, Pi.single_add, add_assoc]
    rw [e] at h0
    have h1 : HasDerivAt (fun s => f (t + s)) ((O.d w i φ).1 (v + Pi.single i (at1 w t))) (t - t) := by
      simpa using h0
    have h2 := h1.comp_sub_const t t
    have e2 : (fun x => f (t + (x - t))) = f := by
      funext x
      simp
    rw [e2] at h2
    have key : (O.d w i φ).1 (v + Pi.single i (at1 w t)) = -2 * Real.pi * κ * (a + t) * f t := by
      rw [h w i]
      change (-2 * Real.pi * kap δ w i) * (O.x w i φ).1 (v + Pi.single i (at1 w t)) = _
      rw [O.x_apply, cw_step]
      simp only [f]
      ring
    rw [key] at h2
    exact h2
  have hX : ∀ t : ℝ, HasDerivAt X ((Real.pi : ℂ) * κ * (2 * a + 2 * t)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
    have h2 := ((h1.const_mul (2 * a)).add (h1.mul h1)).const_mul ((Real.pi : ℂ) * κ)
    exact h2.congr_deriv (by ring)
  have hE : ∀ t : ℝ, HasDerivAt (fun t => f t * Complex.exp (X t)) 0 t := by
    intro t
    have h2 := (hf t).mul (hX t).cexp
    exact h2.congr_deriv (by ring)
  have hc := is_const_of_deriv_eq_zero (fun t => (hE t).differentiableAt) (fun t => (hE t).deriv) t 0
  have h0 : f 0 = φ.1 v := by
    simp only [f]
    rw [(atLaws F w).2.2.2.2.1]
    simp
  have hX0 : X 0 = 0 := by simp [X]
  simp only [hX0, Complex.exp_zero, mul_one, h0] at hc
  rw [gauss_step, ← hc]
  have : Complex.exp (X t) * Complex.exp (-X t) = 1 := by
    rw [← Complex.exp_add]
    simp
  change f t * gauss δ v = f t * Complex.exp (X t) * (gauss δ v * Complex.exp (-X t))
  linear_combination (-(f t * gauss δ v)) * this

private theorem chain_step (δ : F) (O : Ops F) (φ : S4 F)
    (h : ∀ w i, O.d w i φ = (-2 * Real.pi * kap δ w i) • O.x w i φ)
    (v : V4 F) (c : Fin 4 × InfinitePlace F → ℝ) (s : Finset (Fin 4 × InfinitePlace F)) :
    φ.1 (v + ∑ p ∈ s, Pi.single p.1 (at1 p.2 (c p))) * gauss δ v =
      φ.1 v * gauss δ (v + ∑ p ∈ s, Pi.single p.1 (at1 p.2 (c p))) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
    rw [Finset.sum_insert hp, add_comm (Pi.single p.1 _), ← add_assoc]
    have hs := line_step δ O φ h (v + ∑ p ∈ s, Pi.single p.1 (at1 p.2 (c p))) p.1 p.2 (c p)
    have hg : gauss δ (v + ∑ p ∈ s, Pi.single p.1 (at1 p.2 (c p))) ≠ 0 := Complex.exp_ne_zero _
    refine mul_right_cancel₀ hg ?_
    linear_combination (gauss δ v) * hs +
      (gauss δ (v + ∑ p ∈ s, Pi.single p.1 (at1 p.2 (c p)) + Pi.single p.1 (at1 p.2 (c p)))) * ih

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.Fo.annVac :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F) (O : Ops F) (φ : S4 F), (∀ w i, O.d w i φ = (-2 * Real.pi * kap δ w i) • O.x w i φ) → φ ∈ Vac δ := by
  intro F _ _ _ δ O φ h v v' e
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  let c : Fin 4 × InfinitePlace F → ℝ := fun p => TR.pInf F (v' p.1 - v p.1) p.2
  have hv : v' = v + ∑ p, Pi.single p.1 (at1 p.2 (c p)) := by
    funext j
    have h0 : (v' j - v j).2 = 0 := by
      have := congrFun e j
      change (v j).2 = (v' j).2 at this
      change (v' j).2 - (v j).2 = 0
      rw [this, sub_self]
    have h1 := (atLaws F w₀).2.2.2.2.2.2.1 (v' j - v j) h0
    have h2 : (∑ p : Fin 4 × InfinitePlace F, (Pi.single p.1 (at1 p.2 (c p)) : V4 F)) j = v' j - v j := by
      rw [h1, Fintype.sum_prod_type, Finset.sum_apply, Finset.sum_eq_single j]
      · rw [Finset.sum_apply]
        refine Finset.sum_congr rfl fun w _ => ?_
        simp [c, ← h1]
      · intro b _ hb
        rw [Finset.sum_apply]
        exact Finset.sum_eq_zero fun w _ => Pi.single_eq_of_ne hb.symm _
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [Pi.add_apply, h2]
    abel
  have := chain_step δ O φ h v c Finset.univ
  rw [← hv] at this
  exact this.symm ▸ (by ring)
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem entries {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (k : G1 F) (hk : InfOrth k)
    (w : InfinitePlace F) : cw w (k 1 0) = -cw w (k 0 1) ∧ cw w (k 1 1) = cw w (k 0 0) := by
  let pw : A F →+* ℝ := (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) w).comp (TR.pInf F)
  have hO : ∀ i j, pw ((k.1 * k.1ᵀ) i j) = pw ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j) := fun i j =>
    congrFun (congrArg (TR.infEq F).symm (hk i j)) w
  have h00 := hO 0 0
  have h01 := hO 0 1
  have hd : pw (k 0 0) * pw (k 1 1) - pw (k 0 1) * pw (k 1 0) = 1 := by
    have h := k.det_coe
    rw [Matrix.det_fin_two] at h
    have := congrArg pw h
    simpa using this
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, map_add (f := _), map_mul] at h00 h01
  simp only [Matrix.one_apply_eq, map_one] at h00
  simp only [Matrix.one_apply_ne (zero_ne_one : (0 : Fin 2) ≠ 1), map_zero] at h01
  change pw (k 0 0) * pw (k 0 0) + pw (k 0 1) * pw (k 0 1) = 1 at h00
  have hc : pw (k 1 0) = -pw (k 0 1) := by
    linear_combination (-pw (k 1 0)) * h00 + pw (k 0 0) * h01 - pw (k 0 1) * hd
  have he : pw (k 1 1) = pw (k 0 0) := by
    linear_combination (-pw (k 1 1)) * h00 + pw (k 0 1) * h01 + pw (k 0 0) * hd
  constructor
  · change ((pw (k 1 0) : ℝ) : ℂ) = -((pw (k 0 1) : ℝ) : ℂ)
    rw [hc]; push_cast; rfl
  · change ((pw (k 1 1) : ℝ) : ℂ) = ((pw (k 0 0) : ℝ) : ℂ)
    rw [he]

private theorem step {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) (k : G1 F)
    (w : InfinitePlace F) (i j : Fin 4) (s : ℂ) (hs : s * s = -1)
    (hc : cw w (k 1 0) = -cw w (k 0 1)) (he : cw w (k 1 1) = cw w (k 0 0)) (φ : S4 F)
    (h1 : O.d w i φ = s • O.p D.δ w j φ) (h2 : O.d w j φ = s • O.p D.δ w i φ) :
    O.d w i (W.Om k φ) = s • O.p D.δ w j (W.Om k φ) := by
  have e1 := congrArg (fun T : Module.End ℂ (S4 F) => T φ) (Heisenberg₂ F E D W O k w i).1
  have e2 := congrArg (fun T : Module.End ℂ (S4 F) => T φ) (Heisenberg₂ F E D W O k w j).2
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, map_add (f := _), map_smul] at e1 e2
  rw [e1, e2, hc, he, h1, h2]
  simp only [map_smul, smul_add, smul_smul]
  have : s * (-cw w (k 0 1) * s) = cw w (k 0 1) := by linear_combination (-cw w (k 0 1)) * hs
  rw [this, add_comm]
  congr 1
  rw [mul_comm]

private theorem scal {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F) (O : Ops F)
    (w : InfinitePlace F) (f : S4 F) :
    ((-2 * Real.pi * kap δ w 0 : ℂ) • O.x w 0 f = Complex.I • O.p δ w 1 f) ∧
    ((-2 * Real.pi * kap δ w 1 : ℂ) • O.x w 1 f = Complex.I • O.p δ w 0 f) ∧
    ((-2 * Real.pi * kap δ w 2 : ℂ) • O.x w 2 f = (-Complex.I) • O.p δ w 2 f) ∧
    ((-2 * Real.pi * kap δ w 3 : ℂ) • O.x w 3 f = (-Complex.I) • O.p δ w 3 f) := by
  have hI := Complex.I_mul_I
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Ops.p, kap, cc, Matrix.cons_val, LinearMap.smul_apply, smul_smul] <;>
    congr 1
  · linear_combination (-2 * (Real.pi : ℂ)) * hI
  · linear_combination (-2 * (Real.pi : ℂ)) * hI
  · linear_combination (-4 * (Real.pi : ℂ)) * hI
  · linear_combination (4 * (Real.pi : ℂ) * cw w (rt δ)) * hI

theorem UpperTheory.ConvolutionTheory.R2.Fo.vacOm :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (k : G1 F), InfOrth k → ∀ φ ∈ Vac D.δ, W.Om k φ ∈ Vac D.δ := by
  intro F E _ _ _ _ _ _ _ D W k hk φ hφ
  obtain ⟨O⟩ := opsEx F
  have hv := vacAnn F D.δ O φ hφ
  refine annVac F D.δ O (W.Om k φ) fun w i => ?_
  obtain ⟨hc, he⟩ := entries k hk w
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hJ : (-Complex.I) * (-Complex.I) = -1 := by rw [neg_mul_neg, hI]
  obtain ⟨s0, s1, s2, s3⟩ := scal D.δ O w φ
  obtain ⟨t0, t1, t2, t3⟩ := scal D.δ O w (W.Om k φ)
  have v0 := (hv w 0).trans s0
  have v1 := (hv w 1).trans s1
  have v2 := (hv w 2).trans s2
  have v3 := (hv w 3).trans s3
  fin_cases i
  · exact (step D W O k w 0 1 _ hI hc he φ v0 v1).trans t0.symm
  · exact (step D W O k w 1 0 _ hI hc he φ v1 v0).trans t1.symm
  · exact (step D W O k w 2 2 _ hJ hc he φ v2 v2).trans t2.symm
  · exact (step D W O k w 3 3 _ hJ hc he φ v3 v3).trans t3.symm
