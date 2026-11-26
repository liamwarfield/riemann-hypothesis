module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.AtLaws

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CwShift
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private lemma cw_shift {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    (w w' : InfinitePlace F) (i j : Fin 4) (v : V4 F) (t : ℝ) :
    cw w' ((v + Pi.single i (at1 w t) : V4 F) j) = cw w' (v j) + if w = w' ∧ i = j then (t : ℂ) else 0 := by
  have hp := ((atLaws F w).2.2.1) t
  by_cases hij : i = j
  · subst hij
    have h1 : (v + Pi.single i (at1 w t) : V4 F) i = v i + at1 w t := by simp
    rw [h1]
    unfold cw
    rw [map_add (f := _), Pi.add_apply, hp]
    by_cases hw : w = w'
    · subst hw; simp
    · have : w' ≠ w := fun h => hw h.symm
      simp [hw, this]
  · have h1 : (v + Pi.single i (at1 w t) : V4 F) j = v j := by
      simp [Pi.single_apply, Ne.symm hij]
    rw [h1]
    simp [hij]

theorem UpperTheory.ConvolutionTheory.R2.Fo.weyl :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (O : Ops F) w w' i j, O.x w i * O.x w' j = O.x w' j * O.x w i ∧
    O.d w i * O.x w' j = O.x w' j * O.d w i + if w = w' ∧ i = j then 1 else 0 := by
  intro F _ _ _ O w w' i j
  refine ⟨?_, ?_⟩
  · refine LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_)
    change (O.x w i (O.x w' j φ)).1 v = (O.x w' j (O.x w i φ)).1 v
    rw [O.x_apply, O.x_apply, O.x_apply, O.x_apply, mul_left_comm]
  · refine LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_)
    have h0 : at1 w 0 = (0 : A F) := (atLaws F w).2.2.2.2.1
    have hv : (v + Pi.single i (at1 w 0) : V4 F) = v := by rw [h0]; simp
    set C : Prop := w = w' ∧ i = j with hC
    have hg := O.d_spec w i φ v
    have hh : HasDerivAt (fun t : ℝ => cw w' (v j) + if C then (t : ℂ) else 0) (if C then 1 else 0) 0 := by
      by_cases c : C
      · simp only [if_pos c]
        exact (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_add _ |>.congr_deriv (by simp)
      · simp only [if_neg c]
        exact hasDerivAt_const _ _
    have hm := hh.mul hg
    have hd := O.d_spec w i (O.x w' j φ) v
    have he : (fun t : ℝ => (O.x w' j φ).1 (v + Pi.single i (at1 w t) : V4 F)) =
        (fun t : ℝ => cw w' (v j) + if C then (t : ℂ) else 0) * fun t : ℝ => φ.1 (v + Pi.single i (at1 w t) : V4 F) := by
      funext t
      rw [O.x_apply, cw_shift]
      rfl
    rw [he] at hd
    have hu := hd.unique hm
    change (O.d w i (O.x w' j φ)).1 v = (O.x w' j (O.d w i φ)).1 v + ((if C then (1 : Module.End ℂ (S4 F)) else 0) φ).1 v
    rw [hu, O.x_apply, hv]
    by_cases c : C
    · simp [c]; ring
    · simp [c]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.VacAnn
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem hasDerivAt_sumq {ι : Type} [Fintype ι] [DecidableEq ι] (K b r : ι → ℝ) (w : ι) :
    HasDerivAt (fun t : ℝ => ∑ w', (K w' * (b w' + (Pi.single w t : ι → ℝ) w') ^ 2 + r w')) (2 * K w * b w) 0 := by
  have h : ∀ w' ∈ (Finset.univ : Finset ι), HasDerivAt (fun t : ℝ => K w' * (b w' + (Pi.single w t : ι → ℝ) w') ^ 2 + r w')
      (if w' = w then 2 * K w * b w else 0) 0 := by
    intro w' _
    by_cases hw : w' = w
    · subst hw
      simp only [Pi.single_eq_same, if_true]
      have h0 : HasDerivAt (fun t : ℝ => b w' + t) 1 0 := (hasDerivAt_id (0 : ℝ)).const_add (b w')
      refine (((h0.fun_pow 2).const_mul (K w')).add_const (r w')).congr_deriv ?_
      simp only [add_zero, Nat.add_one_sub_one, pow_one, mul_one, Nat.cast_ofNat]
      ring
    · simp only [Pi.single_eq_of_ne hw, if_neg hw]
      exact hasDerivAt_const _ _
  have := HasDerivAt.fun_sum h
  simpa using this

private theorem gauss_deriv {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F) (v : V4 F) (w : InfinitePlace F) (i : Fin 4) :
    HasDerivAt (fun t : ℝ => gauss δ (v + Pi.single i (at1 w t)))
      (-2 * Real.pi * kap δ w i * cw w (v i) * gauss δ v) 0 := by
  obtain ⟨-, -, hp, -, h0, -, -, -⟩ := atLaws F w
  set p := TR.pInf F with hpdef
  let Kf : InfinitePlace F → ℝ := fun w' => ![1, 1, 2, -2 * p (rt δ) w'] i
  let bf : InfinitePlace F → ℝ := fun w' => p (v i) w'
  let Q : V4 F → A F := fun u => u 0 ^ 2 + u 1 ^ 2 + 2 * (u 2 ^ 2 - rt δ * u 3 ^ 2)
  let rf : InfinitePlace F → ℝ := fun w' => p (Q v) w' - Kf w' * bf w' ^ 2
  have hQ : ∀ (t : ℝ) w', p (Q (v + Pi.single i (at1 w t))) w' =
      Kf w' * (bf w' + (Pi.single w t : InfinitePlace F → ℝ) w') ^ 2 + rf w' := by
    intro t w'
    have h2 : p (2 : A F) w' = 2 := by
      rw [map_ofNat]
      rfl
    fin_cases i <;> simp [Q, Kf, bf, rf, hp, h2, map_add (f := _), map_mul, map_pow, map_sub, Pi.single_apply] <;> ring
  have hK : kap δ w i = ((Kf w : ℝ) : ℂ) := by
    fin_cases i <;> simp [kap, Kf, cw, hpdef]
  have hfun : (fun t : ℝ => gauss δ (v + Pi.single i (at1 w t))) = fun t : ℝ => Complex.exp (-(Real.pi : ℂ) *
      ((∑ w', (Kf w' * (bf w' + (Pi.single w t : InfinitePlace F → ℝ) w') ^ 2 + rf w') : ℝ) : ℂ)) := by
    funext t
    simp only [← hQ]
    rfl
  have hC : HasDerivAt (fun t : ℝ => ((∑ w', (Kf w' * (bf w' + (Pi.single w t : InfinitePlace F → ℝ) w') ^ 2 + rf w') : ℝ) : ℂ))
      ((2 * Kf w * bf w : ℝ) : ℂ) 0 := (hasDerivAt_sumq Kf bf rf w).ofReal_comp
  have hX := (hC.const_mul (-(Real.pi : ℂ))).cexp
  have e0 : v + Pi.single i (at1 w 0) = v := by
    rw [h0]
    simp
  have hval := (congrArg (gauss δ) e0).symm.trans (congrFun hfun 0)
  rw [hfun]
  refine hX.congr_deriv ?_
  beta_reduce at hval ⊢
  rw [← hval, hK]
  have hb : cw w (v i) = ((bf w : ℝ) : ℂ) := rfl
  rw [hb]
  push_cast
  ring

theorem UpperTheory.ConvolutionTheory.R2.Fo.vacAnn :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F) (O : Ops F), ∀ φ ∈ Vac δ, ∀ w i, O.d w i φ = (-2 * Real.pi * kap δ w i) • O.x w i φ := by
  intro F _ _ _ δ O φ hφ w i
  obtain ⟨-, -, -, -, -, -, -, hfin⟩ := atLaws F w
  apply Subtype.ext
  funext v
  have hg := gauss_deriv δ v w i
  have hne : gauss δ v ≠ 0 := Complex.exp_ne_zero _
  have hf : ∀ t : ℝ, finPartPi (v + Pi.single i (at1 w t)) = finPartPi v := by
    intro t
    have := hfin t i
    funext j
    have hj := congrFun this j
    simp only [finPartPi] at hj ⊢
    change (v j).2 + ((Pi.single i (at1 w t) : V4 F) j).2 = (v j).2
    rw [hj]
    exact add_zero _
  have h1 : (fun t : ℝ => φ.1 (v + Pi.single i (at1 w t))) = fun t : ℝ => (φ.1 v / gauss δ v) * gauss δ (v + Pi.single i (at1 w t)) := by
    funext t
    have := hφ (v + Pi.single i (at1 w t)) v (hf t)
    field_simp
    exact this
  have hd := O.d_spec w i φ v
  rw [h1] at hd
  have hu := hd.unique (hg.const_mul (φ.1 v / gauss δ v))
  change _ = (-2 * Real.pi * kap δ w i) * (O.x w i φ).1 v
  rw [hu, O.x_apply]
  field_simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.PsiShift
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

section
variable {F : Type} [Field F] [NumberField F]

private theorem psi_add (a b : A F) : ψ (a + b) = ψ a * ψ b := by
  simp only [ψ, AddChar.map_add_eq_mul, Circle.coe_mul]

private theorem norm_psi (a : A F) : ‖ψ a‖ = 1 := by
  exact Circle.norm_coe _

private theorem cont_psi : Continuous (ψ : A F → ℂ) :=
  continuous_subtype_val.comp continuous_adelicChar

private theorem B_add (δ : F) (y v v' : V4 F) : B4 δ y (v + v') = B4 δ y v + B4 δ y v' := by
  simp only [B4, Pi.add_apply]
  ring

private theorem B_single (δ : F) (y : V4 F) (i : Fin 4) (a : A F) :
    B4 δ y (Pi.single i a) = a * B4 δ y (Pi.single i 1) := by
  fin_cases i <;> simp [B4] <;> ring

private theorem cont_B (δ : F) (v : V4 F) : Continuous fun y : V4 F => B4 δ y v := by
  unfold B4
  exact ((continuous_const.mul (((continuous_apply 2).mul continuous_const).sub
    (continuous_const.mul ((continuous_apply 3).mul continuous_const)))).sub
    ((continuous_apply 1).mul continuous_const)).sub ((continuous_apply 0).mul continuous_const)

variable [IsTotallyReal F]

private theorem cw_add (w : InfinitePlace F) (a b : A F) : cw w (a + b) = cw w a + cw w b := by
  simp [cw]
private theorem cw_sub (w : InfinitePlace F) (a b : A F) : cw w (a - b) = cw w a - cw w b := by
  simp [cw]
private theorem cw_mul (w : InfinitePlace F) (a b : A F) : cw w (a * b) = cw w a * cw w b := by
  simp [cw]
private theorem cw_neg (w : InfinitePlace F) (a : A F) : cw w (-a) = -cw w a := by
  simp [cw]
private theorem cw_two (w : InfinitePlace F) : cw w (2 : A F) = 2 := by
  have h1 : cw w (1 : A F) = 1 := by simp [cw]
  rw [show (2 : A F) = 1 + 1 by norm_num, cw_add, h1]
  norm_num

private theorem p_apply (δ : F) (O : Ops F) (w : InfinitePlace F) (i : Fin 4) (φ : S4 F) (y : V4 F) :
    (O.p δ w i φ).1 y = cc * cw w (B4 δ y (Pi.single i 1)) * φ.1 y := by
  fin_cases i <;>
    simp [Ops.p, B4, O.x_apply, cw_add, cw_sub, cw_mul, cw_neg, cw_two] <;> ring

private theorem psi_shift (δ : F) (w : InfinitePlace F) (i : Fin 4) (y v : V4 F) (t : ℝ) :
    ψ (B4 δ y (v + Pi.single i (at1 w t))) =
      ψ (B4 δ y v) * Complex.exp (cc * cw w (B4 δ y (Pi.single i 1)) * t) := by
  obtain ⟨h1, -, -, -, -, h6, -, -⟩ := atLaws F w
  rw [B_add, psi_add, B_single, h6, h1]
  congr 2
  simp only [cw]
  push_cast
  ring

private theorem deriv_gen {X : Type} [MeasurableSpace X] (μ : Measure X) (f G : X → ℂ) (u : ℝ → X → ℂ) (c : X → ℂ)
    (hf : Integrable f μ) (hG : Integrable G μ) (hu : ∀ t, AEStronglyMeasurable (u t) μ)
    (hn : ∀ t y, ‖u t y‖ = 1) (hd : ∀ t y, HasDerivAt (fun s => u s y) (c y * u t y) t)
    (hc : ∀ y, G y = c y * f y) :
    HasDerivAt (fun t => ∫ y, f y * u t y ∂μ) (∫ y, G y * u 0 y ∂μ) 0 := by
  have hm : ∀ t, AEStronglyMeasurable (fun y => f y * u t y) μ := fun t => hf.1.mul (hu t)
  have hm' : ∀ t, AEStronglyMeasurable (fun y => G y * u t y) μ := fun t => hG.1.mul (hu t)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun t y => f y * u t y) (F' := fun t y => G y * u t y)
    (x₀ := (0 : ℝ)) (s := Set.univ) (bound := fun y => ‖G y‖) univ_mem
    (Eventually.of_forall hm)
    (hf.mono (hm 0) (ae_of_all _ fun y => by rw [norm_mul, hn, mul_one]))
    (hm' 0)
    (ae_of_all _ fun y t _ => by rw [norm_mul, hn, mul_one])
    hG.norm
    (ae_of_all _ fun y t _ => ?_)).2
  refine ((hd t y).const_mul (f y)).congr_deriv ?_
  rw [hc]
  ring

private theorem psi_deriv (δ : F) (w : InfinitePlace F) (i : Fin 4) (y v : V4 F) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ψ (B4 δ y (v + Pi.single i (at1 w s))))
      (cc * cw w (B4 δ y (Pi.single i 1)) * ψ (B4 δ y (v + Pi.single i (at1 w t)))) t := by
  have h1 : HasDerivAt (fun s : ℝ => cc * cw w (B4 δ y (Pi.single i 1)) * (s : ℂ))
      (cc * cw w (B4 δ y (Pi.single i 1))) t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (cc * cw w (B4 δ y (Pi.single i 1)))
  have h2 := h1.cexp.const_mul (ψ (B4 δ y v))
  simp only [psi_shift]
  refine h2.congr_deriv ?_
  ring

private theorem deriv_ops (O : Ops F) (δ : F) (w : InfinitePlace F) (i : Fin 4) (φ : S4 F) (u : ℝ → V4 F → ℂ) (c : V4 F → ℂ)
    (hu : ∀ t, AEStronglyMeasurable (u t) (adeleMeasurePi F)) (hn : ∀ t y, ‖u t y‖ = 1)
    (hd : ∀ t y, HasDerivAt (fun s => u s y) (c y * u t y) t) (hc : ∀ y, (O.p δ w i φ).1 y = c y * φ.1 y) :
    HasDerivAt (fun t => ∫ y, φ.1 y * u t y ∂(adeleMeasurePi F)) (∫ y, (O.p δ w i φ).1 y * u 0 y ∂(adeleMeasurePi F)) 0 :=
  deriv_gen (adeleMeasurePi F) φ.1 (O.p δ w i φ).1 u c (integrable_of_mem_schwartzBruhatPi φ.2)
    (integrable_of_mem_schwartzBruhatPi (O.p δ w i φ).2) hu hn hd hc

private theorem key (δ : F) (O : Ops F) (w : InfinitePlace F) (i : Fin 4) (φ : S4 F) (v : V4 F) :
    HasDerivAt (fun t : ℝ => ft4 δ φ.1 (v + Pi.single i (at1 w t))) (ft4 δ (O.p δ w i φ).1 v) 0 := by
  obtain ⟨-, -, -, -, h0, -, -, -⟩ := atLaws F w
  obtain ⟨u, hu⟩ : ∃ u : ℝ → V4 F → ℂ, ∀ t y, u t y = ψ (B4 δ y (v + Pi.single i (at1 w t))) := ⟨_, fun _ _ => rfl⟩
  have hm : ∀ t, AEStronglyMeasurable (u t) (adeleMeasurePi F) := fun t => by
    rw [show u t = fun y => ψ (B4 δ y (v + Pi.single i (at1 w t))) from funext (hu t)]
    exact (cont_psi.comp (cont_B δ _)).aestronglyMeasurable
  have hn : ∀ t y, ‖u t y‖ = 1 := fun t y => by rw [hu]; exact norm_psi _
  have hd : ∀ t y, HasDerivAt (fun s => u s y) (cc * cw w (B4 δ y (Pi.single i 1)) * u t y) t := fun t y => by
    rw [show (fun s => u s y) = fun s => ψ (B4 δ y (v + Pi.single i (at1 w s))) from funext fun s => hu s y, hu]
    exact psi_deriv δ w i y v t
  have h := deriv_ops O δ w i φ u (fun y => cc * cw w (B4 δ y (Pi.single i 1))) hm hn hd (fun y => p_apply δ O w i φ y)
  have e1 : (fun t : ℝ => ft4 δ φ.1 (v + Pi.single i (at1 w t))) = fun t => ∫ y, φ.1 y * u t y ∂(adeleMeasurePi F) := by
    simp only [ft4, hu]
  have e2 : ft4 δ (O.p δ w i φ).1 v = ∫ y, (O.p δ w i φ).1 y * u 0 y ∂(adeleMeasurePi F) := by
    simp only [ft4, hu, h0, Pi.single_zero, add_zero]
  rw [e1, e2]
  exact h

end

theorem UpperTheory.ConvolutionTheory.R2.Fo.dW :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) w i, O.d w i * W.Om (wW F) = W.Om (wW F) * O.p D.δ w i := by
  intro F E _ _ _ _ _ _ _ D W O w i
  refine LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_)
  rw [Module.End.mul_apply, Module.End.mul_apply]
  rw [W.Om_w (O.p D.δ w i φ) v]
  have hd := O.d_spec w i (W.Om (wW F) φ) v
  simp only [W.Om_w] at hd
  exact hd.unique (key D.δ O w i φ v)
end
