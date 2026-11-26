module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CapOf
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.LieL

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Mov
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.DerOm
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThDerOm
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.thDerOm :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), ThDerOm W := by
  intro F E _ _ _ _ _ _ _ D W φ φ' hφ' G hG hD g h t

  have hcomm : ∀ (g : G1 F) (x : S4 F),
      W.Om g (W.L h x) = W.L h (W.Om (cD (nu F h)⁻¹ g) x) := by
    intro g x
    have e := W.comm h (cD (nu F h)⁻¹ g)
    rw [← cD_mul_left, mul_inv_cancel, cD_one_left] at e
    have e' := congrArg (fun T : Module.End ℂ (S4 F) => T x) e
    simpa only [Module.End.mul_apply] using e'.symm
  have hmul : ∀ (a b : G1 F) (x : S4 F), W.Om (a * b) x = W.Om a (W.Om b x) := by
    intro a b x
    rw [map_mul, Module.End.mul_apply]

  have hDL : Der (fun s => W.L h (W.Om (G s) φ)) (fun s => W.L h (W.Om (G s) φ')) := by
    intro s v
    simp only [W.L_apply]
    exact (hD s _).const_mul _

  have hdom : ∀ (g : G1 F) (t : ℝ),
      Dom (Metric.ball t 1) fun s => (W.Om g (W.L h (W.Om (G s) φ'))).1 := by
    intro g t
    let c : ℝ → G1 F := fun s => cD (nu F h)⁻¹ g * G s
    have hc : Continuous c := continuous_const.mul hG
    have hC : IsCompact (c '' Metric.closedBall t 1) := (isCompact_closedBall t 1).image hc
    obtain ⟨K, hK, hB⟩ := lDom F E D W (G1 F) (c '' Metric.closedBall t 1) (fun k => W.Om k φ')
      (omCpt F E D W φ' hφ' _ hC) {h} isCompact_singleton
    refine ⟨K, hK, fun N => ?_⟩
    obtain ⟨B, hB⟩ := hB N
    refine ⟨B, fun s hs v => ?_⟩
    have hmem : ((h, c s) : GL (Fin 2) (A E) × G1 F) ∈ ({h} : Set _) ×ˢ (c '' Metric.closedBall t 1) :=
      ⟨rfl, s, Metric.ball_subset_closedBall hs, rfl⟩
    have := hB _ hmem v
    simpa only [hcomm, hmul, c] using this
  exact thDer F _ _ (omDer F E D W _ _ hDL hdom g) t (hdom g t)
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.derOm :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), DerOm W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ φ' hφ' G hG hG0 hD h
  have hc : Continuous fun g : G1 F => f.1 (gl g * dM (nu F h)) :=
    (decay F π f hf).1.comp (Matrix.SpecialLinearGroup.continuous_toGL.mul continuous_const)
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using vol F M⟩
  have hm : ∀ ψ₀ : S4 F, AEStronglyMeasurable
      (fun g => f.1 (gl g * dM (nu F h)) * Th (W.Om g ψ₀).1) (M.μ.restrict M.D) := fun ψ₀ =>
    (hc.measurable.mul (thMeas F E D W ψ₀).1).aestronglyMeasurable
  have hP : Continuous fun s : ℝ => (gl (cD (nu F h) (G s)))⁻¹ * dM (nu F h) :=
    (continuous_gl.comp (continuous_cD.comp (continuous_const.prodMk hG))).inv.mul continuous_const
  have key : ∀ φ₀ ∈ Fock D.δ, ∃ B : ℝ, ∀ s ∈ Metric.closedBall (0 : ℝ) 1, ∀ g,
      ‖f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h (W.Om (G s) φ₀))).1‖ ≤ B := by
    intro φ₀ hφ₀
    obtain ⟨B, hB⟩ := thBoundH F E D W π f hf φ₀ hφ₀ h _
      ((isCompact_closedBall (0 : ℝ) 1).image hP) {1} isCompact_singleton
      (by rintro _ rfl; simp [Ff.One, nu])
    refine ⟨B, fun s hs g => ?_⟩
    have e1 : W.L h (W.Om (G s) φ₀) = W.Om (cD (nu F h) (G s)) (W.L h φ₀) :=
      LinearMap.congr_fun (W.comm h (G s)) φ₀
    have e2 : W.Om g (W.Om (cD (nu F h) (G s)) (W.L h φ₀)) = W.Om (g * cD (nu F h) (G s)) (W.L h φ₀) := by
      rw [map_mul]; rfl
    have e3 : gl g * dM (nu F h) =
        gl (g * cD (nu F h) (G s)) * ((gl (cD (nu F h) (G s)))⁻¹ * dM (nu F h)) := by
      rw [gl_mul, mul_assoc, mul_inv_cancel_left]
    have h1 := hB (g * cD (nu F h) (G s)) _ ⟨s, hs, rfl⟩ 1 rfl
    rw [← e3] at h1
    rw [e1, e2]
    simpa using h1
  obtain ⟨B, hB⟩ := key φ' hφ'
  obtain ⟨B₀, hB₀⟩ := key φ hφ
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := M.μ.restrict M.D)
    (F := fun s g => f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h (W.Om (G s) φ))).1)
    (F' := fun s g => f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h (W.Om (G s) φ'))).1)
    (x₀ := (0 : ℝ)) (s := Metric.closedBall 0 1) (bound := fun _ => B)
    (Metric.closedBall_mem_nhds 0 one_pos)
    (Eventually.of_forall fun s => hm _)
    (Integrable.of_bound (hm _) B₀ (ae_of_all _ fun g => hB₀ 0 (by simp) g))
    (hm _)
    (ae_of_all _ fun g s hs => hB s hs g)
    (integrable_const B)
    (ae_of_all _ fun g s _ => (thDerOm F E D W φ φ' hφ' G hG hD g h s).const_mul _)
  have e : (∫ g in M.D, f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h (W.Om (G 0) φ'))).1 ∂M.μ) =
      lift W M f.1 φ' h := by
    simp [lift, hG0]
  have := hmain.2
  rw [e] at this
  exact this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.MovG
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.RtInv
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.rtInv :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], RtInv F := by
  intro F _ _ _ M u hu k
  haveI := M.haar
  haveI := M.right
  have hmp : MeasurePreserving (· * k) M.μ M.μ := measurePreserving_mul_right M.μ k
  have hemb : MeasurableEmbedding (· * k : G1 F → G1 F) := (MeasurableEquiv.mulRight k).measurableEmbedding
  have hfd : IsFundamentalDomain (Gam F) ((Equiv.mulRight k) '' M.D) M.μ := by
    refine M.fund.image_of_equiv (Equiv.mulRight k) ?_ (Equiv.refl _) ?_
    · exact (measurePreserving_mul_right M.μ k⁻¹).quasiMeasurePreserving
    · intro g x
      simp [Subgroup.smul_def, mul_assoc]
  have hinv : ∀ (g : Gam F) x, u (g • x) = u x := by
    rintro ⟨_, γ, rfl⟩ x
    simpa [Subgroup.smul_def] using hu γ x
  have hpre : (· * k : G1 F → G1 F) ⁻¹' ((Equiv.mulRight k) '' M.D) = M.D := by
    ext x; simp
  have h3 := hmp.setIntegral_preimage_emb hemb u ((Equiv.mulRight k) '' M.D)
  rw [hpre] at h3
  rw [h3]
  exact hfd.setIntegral_eq M.fund hinv
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.movG :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F), MovG W M := by
  intro F E _ _ _ _ _ _ _ D W M f hf φ g₀ h
  have hu : LInv (fun g : G1 F => f (gl g * dM (nu F h) * (gl g₀)⁻¹) * Th (W.Om g (W.L h φ)).1) := by
    intro γ g
    have h1 : gl (ratS F γ * g) * dM (nu F h) * (gl g₀)⁻¹ =
        ratGL F 2 (Matrix.SpecialLinearGroup.toGL γ) * (gl g * dM (nu F h) * (gl g₀)⁻¹) := by
      rw [gl_mul, gl_ratS]; group
    have h2 : W.Om (ratS F γ * g) (W.L h φ) = W.Om (ratS F γ) (W.Om g (W.L h φ)) := by
      rw [map_mul, Module.End.mul_apply]
    show f (gl (ratS F γ * g) * dM (nu F h) * (gl g₀)⁻¹) * Th (W.Om (ratS F γ * g) (W.L h φ)).1 = _
    rw [h1, hf, h2, W.th_Om]
  have key := rtInv F M _ hu (cD (nu F h) g₀)
  refine Eq.trans (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)) key
  have h1 : gl (g * cD (nu F h) g₀) * dM (nu F h) * (gl g₀)⁻¹ = gl g * dM (nu F h) := by
    rw [gl_mul, gl_cD]; group
  have h2 : W.L h (W.Om g₀ φ) = W.Om (cD (nu F h) g₀) (W.L h φ) := by
    have := congrArg (fun T : Module.End ℂ (S4 F) => T φ) (W.comm h g₀)
    simpa only [Module.End.mul_apply] using this
  have h3 : W.Om (g * cD (nu F h) g₀) (W.L h φ) = W.Om g (W.L h (W.Om g₀ φ)) := by
    rw [h2, map_mul, Module.End.mul_apply]
  show f (gl g * dM (nu F h)) * Th (W.Om g (W.L h (W.Om g₀ φ))).1 =
    f (gl (g * cD (nu F h) g₀) * dM (nu F h) * (gl g₀)⁻¹) * Th (W.Om (g * cD (nu F h) g₀) (W.L h φ)).1
  rw [h1, h3]
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.mov :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), Mov W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ φ' hφ' G c Y hP hG hD
  obtain ⟨hinf, hPc⟩ := UpperTheory.ConvolutionTheory.R2.Ff.parCont F
  obtain ⟨hc0, hcc, hPn⟩ := hPc c Y hP
  have hGc : Continuous G := continuous_adelicSL2_of_continuous_entries fun i j => by
    have e : (fun t => G t i j) = fun t => (TR.infGL F 2 (c t)).val i j := by
      funext t
      rw [← hG t]
      rfl
    rw [e]
    have hv : Continuous fun t => (TR.infGL F 2 (c t)).val :=
      Units.continuous_val.comp (hinf.comp hcc)
    exact hv.matrix_elem i j
  have hG0 : G 0 = 1 := gl_injective (by rw [hG, hc0, map_one, gl_one])
  have hL : LRat f.1 := (π.cusp f hf).1.left
  have hinv : ∀ t, (gl (G t))⁻¹ = TR.infGL F 2 (c (-t)) := fun t => by
    have h1 : c (-t) = (c t)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← hP.1, neg_add_cancel, hc0])
    rw [hG, h1, map_inv]
  funext h
  have d1 := UpperTheory.ConvolutionTheory.R2.Ff.derOm F E D W M π f hf φ hφ φ' hφ' G hGc hG0 hD h
  have d2 := UpperTheory.ConvolutionTheory.R2.Ff.derF F E D W M π f hf φ hφ (fun t => c (-t)) (-Y) hPn h
  have e : (fun t => lift W M (fun x => f.1 (x * TR.infGL F 2 (c (-t)))) φ h) =
      fun t => lift W M f.1 (W.Om (G t) φ) h := by
    funext t
    rw [UpperTheory.ConvolutionTheory.R2.Ff.movG F E D W M f.1 hL φ (G t) h, hinv]
  rw [e] at d2
  have hu := d1.unique d2
  have hl : (TR.lie F 2 (-Y) f).1 = (-1 : ℂ) • (TR.lie F 2 Y f).1 := by
    rw [map_neg]
    funext x
    simp
  have h4 := (UpperTheory.ConvolutionTheory.R2.Ff.lin F E D W M π).2.2.2 (TR.lie F 2 Y f).1 (-1) φ
  rw [hu, hl, h4]
  simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.MoveE
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.CurveE
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private theorem pInf_sInf (x : TR.Rinf F) : TR.pInf F (TR.sInf F x) = x :=
  (TR.infEq F).symm_apply_apply x

private theorem pFin_sInf (x : TR.Rinf F) : pFin F (TR.sInf F x) = 0 := rfl

private noncomputable def cU (w : InfinitePlace F) (t : ℝ) : GL (Fin 2) (TR.Rinf F) :=
  ⟨!![1, Pi.single w t; 0, 1], !![1, Pi.single w (-t); 0, 1],
    by
      ext i j v
      fin_cases i <;> fin_cases j <;> by_cases h : v = w <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Pi.single_apply, h],
    by
      ext i j v
      fin_cases i <;> fin_cases j <;> by_cases h : v = w <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Pi.single_apply, h]⟩

private theorem cU_val (w : InfinitePlace F) (t : ℝ) : (cU w t).val = !![1, Pi.single w t; 0, 1] := rfl

private theorem cU_add (w : InfinitePlace F) (s t : ℝ) : cU w (s + t) = cU w s * cU w t := by
  refine Units.ext ?_
  rw [Units.val_mul, cU_val, cU_val, cU_val]
  ext i j v
  fin_cases i <;> fin_cases j <;> by_cases h : v = w <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Pi.single_apply, h, add_comm]

private theorem cU_der (w : InfinitePlace F) :
    HasDerivAt (fun t => TR.toL (cU w t).val) (TR.toL (Matrix.single 0 1 (Pi.single w 1))) 0 := by
  have e : (fun t => TR.toL (cU w t).val) =
      fun t : ℝ => TR.toL (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) + t • TR.toL (Matrix.single 0 1 (Pi.single w 1)) := by
    funext t
    ext i j v
    fin_cases i <;> fin_cases j <;> by_cases h : v = w <;> simp [cU_val, Matrix.single_apply, Pi.single_apply, h]
  rw [e]
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const (TR.toL (Matrix.single 0 1 (Pi.single w 1)) : TR.Lie F 2)).const_add
    (TR.toL (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) : TR.Lie F 2)
  simpa only [id, one_smul] using h

private theorem unipotent_placeEmbed_gl (w : InfinitePlace F) (t : ℝ) : gl (nU (Fo.at1 w t)) = TR.infGL F 2 (cU w t) := by
  refine TR.ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    refine Units.ext ?_
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [cU_val, Fo.at1, nU, gl, Matrix.SpecialLinearGroup.toGL, pInf_sInf]
  · rw [TR.pFin_infGL]
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Fo.at1, nU, gl, Matrix.SpecialLinearGroup.toGL, pFin_sInf]

private theorem character_placeEmbed_exp (w : InfinitePlace F) (t : ℝ) (q : A F) :
    ψ (Fo.at1 w t * q) = Complex.exp (Fo.cc * ((t : ℂ) * Fo.cw w q)) := by
  rw [(UpperTheory.ConvolutionTheory.R2.C.splitA F).2]
  have h2 : (Fo.at1 w t * q).2 = 0 := by
    change (0 : FiniteAdeleRing (𝓞 F) F) * q.2 = 0
    exact zero_mul _
  rw [h2, AddChar.map_zero_eq_one, Circle.coe_one, mul_one, Finset.prod_eq_single w]
  · simp [Fo.at1, Fo.cc, Fo.cw, pInf_sInf]
  · intro v _ hv
    simp [Fo.at1, pInf_sInf, hv]
  · simp

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.Ff.curveE :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (W : Weil D), CurveE O W := by
  intro F E _ _ _ _ _ _ _ D O W w
  refine ⟨fun t => nU (Fo.at1 w t), cU w, ⟨cU_add w, cU_der w⟩, unipotent_placeEmbed_gl w, fun φ t v => ?_⟩
  have he : (O.e D.δ w φ).1 v = Fo.cc * Fo.cw w (q4 D.δ v) * φ.1 v := by
    have a : ∀ i j (χ : S4 F), (O.x w i (O.x w j χ)).1 v = Fo.cw w (v i) * (Fo.cw w (v j) * χ.1 v) := fun i j χ => by
      rw [O.x_apply, O.x_apply]
    simp only [Fo.Ops.e, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply]
    change Fo.cc * (((O.x w 2 (O.x w 2 φ)).1 v - Fo.cw w (rt D.δ) * (O.x w 3 (O.x w 3 φ)).1 v) - (O.x w 1 (O.x w 0 φ)).1 v) = _
    rw [a, a, a]
    simp only [Fo.cw, q4, map_sub, map_mul, map_pow, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
    push_cast
    ring
  have e1 : (fun s => (W.Om (nU (Fo.at1 w s)) φ).1 v) =
      fun s : ℝ => Complex.exp (Fo.cc * ((s : ℂ) * Fo.cw w (q4 D.δ v))) * φ.1 v := by
    funext s
    rw [W.Om_n, character_placeEmbed_exp]
  simp only []
  rw [e1, W.Om_n, character_placeEmbed_exp, he]
  have h0 : HasDerivAt (fun s : ℝ => Fo.cc * ((s : ℂ) * Fo.cw w (q4 D.δ v))) (Fo.cc * Fo.cw w (q4 D.δ v)) t := by
    simpa using (((hasDerivAt_id t).ofReal_comp).mul_const (Fo.cw w (q4 D.δ v))).const_mul Fo.cc
  rw [← mul_assoc (Complex.exp _)]
  exact h0.cexp.mul_const (φ.1 v)
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.moveE :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), Fo.MoveE O W M π := by
  intro F E _ _ _ _ _ _ _ D O W M π f hf φ hφ w h
  obtain ⟨G, c, hc, hG, hd⟩ := curveE F E D O W w
  have hx := fun i ψ hψ => (opsFock F E D O w i ψ hψ).1
  have he : O.e D.δ w φ ∈ Fock D.δ :=
    Submodule.smul_mem _ _ (sub_mem (sub_mem (hx _ _ (hx _ _ hφ)) (Submodule.smul_mem _ _ (hx _ _ (hx _ _ hφ)))) (hx _ _ (hx _ _ hφ)))
  exact congrFun (mov F E D W M π f hf φ hφ _ he G c _ hc hG (hd φ)) h
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.LieLift
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.MoveH
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.CurveH
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.R2.Ff.OneParameterSubgroupCurves

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private def eR (w : InfinitePlace F) (t : ℝ) : TR.Rinf F := fun v => if v = w then Real.exp t else 1

private theorem eR_add (w : InfinitePlace F) (s t : ℝ) : eR w (s + t) = eR w s * eR w t := by
  funext v
  by_cases h : v = w <;> simp [eR, h, Real.exp_add]

private theorem eR_zero (w : InfinitePlace F) : eR w 0 = 1 := by
  funext v
  by_cases h : v = w <;> simp [eR, h]

private theorem hasDerivAt_eR (w : InfinitePlace F) : HasDerivAt (eR w) (Pi.single w 1 : TR.Rinf F) 0 := by
  refine hasDerivAt_pi.2 fun v => ?_
  by_cases h : v = w
  · subst h
    simpa [eR] using Real.hasDerivAt_exp 0
  · simpa [eR, h] using hasDerivAt_const (0 : ℝ) (1 : ℝ)

private def eU (w : InfinitePlace F) (t : ℝ) : (TR.Rinf F)ˣ :=
  ⟨eR w t, eR w (-t), by rw [← eR_add, add_neg_cancel, eR_zero], by rw [← eR_add, neg_add_cancel, eR_zero]⟩

private theorem eU_add (w : InfinitePlace F) (s t : ℝ) : eU w (s + t) = eU w s * eU w t :=
  Units.ext (eR_add w s t)

private def aI (w : InfinitePlace F) (t : ℝ) : (A F)ˣ := TR.infId F (eU w t)

private theorem aI_add (w : InfinitePlace F) (s t : ℝ) : aI w (s + t) = aI w s * aI w t := by
  rw [aI, eU_add, map_mul]; rfl

private theorem aI_zero (w : InfinitePlace F) : aI w 0 = 1 := by
  have h : eU w 0 = 1 := Units.ext (eR_zero w)
  rw [aI, h, map_one]

private theorem aI_neg (w : InfinitePlace F) (t : ℝ) : aI w (-t) = (aI w t)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← aI_add, neg_add_cancel, aI_zero])

private theorem aI_val (w : InfinitePlace F) (t : ℝ) :
    ((aI w t : (A F)ˣ) : A F) = 1 + TR.sInf F (eR w t - 1) := by
  change 1 - TR.sInf F 1 + TR.sInf F (eR w t) = _
  rw [map_sub]; abel

private theorem pInf_sInf (x : TR.Rinf F) : TR.pInf F (TR.sInf F x) = x := (TR.infEq F).symm_apply_apply x

private theorem pFin_sInf (x : TR.Rinf F) : pFin F (TR.sInf F x) = 0 := rfl

private theorem sInf_mul (x : TR.Rinf F) (a : A F) : TR.sInf F x * a = TR.sInf F (x * TR.pInf F a) := by
  refine TR.ad_ext ?_ ?_
  · rw [map_mul, pInf_sInf, pInf_sInf]
  · rw [map_mul, pFin_sInf, pFin_sInf, zero_mul]

private theorem pInf_aI (w : InfinitePlace F) (t : ℝ) : TR.pInf F (aI w t : (A F)ˣ) = eR w t := by
  rw [aI_val, map_add (f := _), pInf_sInf, map_one]; abel

private theorem pFin_aI (w : InfinitePlace F) (t : ℝ) : pFin F (aI w t : (A F)ˣ) = 1 := by
  rw [aI_val, map_add (f := _), pFin_sInf, map_one, add_zero]

private theorem ab_aI (w : InfinitePlace F) (t : ℝ) : ab (aI w t) = Real.exp t := by
  have h1 : ((aI w t : (A F)ˣ) : A F).1 = TR.infEq F (eR w t) := by
    change (1 : InfiniteAdeleRing F) - TR.infEq F 1 + TR.infEq F (eR w t) = _
    rw [map_one, sub_self, zero_add]
  have h2 : ((aI w t : (A F)ˣ) : A F).2 = 1 := by
    change (1 : Af F) - 0 + 0 = 1
    rw [sub_zero, add_zero]
  have h3 : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(1 : Af F) v‖ = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => by exact norm_one
  have h4 : ∀ v : InfinitePlace F, ‖(TR.infEq F (eR w t)) v‖ = |eR w t v| := fun v => by
    have h := (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.dist_eq (eR w t v) 0
    have h0 : ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm 0 : v.Completion) = 0 :=
      map_zero _
    rw [← dist_zero_right, ← Real.norm_eq_abs, ← dist_zero_right, ← h0]
    exact h
  unfold ab
  rw [IdeleGroup.ideleModule_eq, h1, h2, h3, mul_one]
  rw [Finset.prod_eq_single w]
  · rw [(IsTotallyReal.isReal w).mult_eq_one, pow_one, h4]
    simp [eR, abs_of_pos (Real.exp_pos t)]
  · intro v _ hv
    rw [(IsTotallyReal.isReal v).mult_eq_one, pow_one, h4]
    simp [eR, hv]
  · simp

private theorem h_apply (O : Fo.Ops F) (w : InfinitePlace F) (φ : S4 F) (v : V4 F) :
    (O.h w φ).1 v = (∑ i, Fo.cw w (v i) * (O.d w i φ).1 v) + 2 * φ.1 v := by
  have e : O.h w φ = (∑ i, O.x w i (O.d w i φ)) + (2 : ℂ) • φ := by
    simp [Fo.Ops.h, LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply, two_smul, two_mul]
  rw [e]
  change ((∑ i, O.x w i (O.d w i φ) : S4 F)).1 v + 2 * φ.1 v = _
  congr 1
  have : ((∑ i, O.x w i (O.d w i φ) : S4 F)).1 = ∑ i, (O.x w i (O.d w i φ)).1 :=
    AddSubmonoidClass.coe_finsetSum _ _
  rw [this, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => O.x_apply w i _ v

private theorem key (O : Fo.Ops F) (hS : SDiff O) (w : InfinitePlace F) (φ : S4 F) (v : V4 F) :
    HasDerivAt (fun r : ℝ => ((Real.exp (2 * r) : ℝ) : ℂ) * φ.1 fun i => ((aI w r : (A F)ˣ) : A F) * v i)
      ((O.h w φ).1 v) 0 := by
  let x : ℝ → Fin 4 → TR.Rinf F := fun r i => (eR w r - 1) * TR.pInf F (v i)
  let x' : Fin 4 → TR.Rinf F := fun i => (Pi.single w 1 : TR.Rinf F) * TR.pInf F (v i)
  have hx0 : x 0 = 0 := by funext i; simp [x, eR_zero]
  have hx : HasDerivAt x x' 0 := by
    refine hasDerivAt_pi.2 fun i => ?_
    exact ((hasDerivAt_eR w).sub_const 1).mul_const _
  have h1 := hS φ v x x' hx0 hx
  have h2 : (fun r : ℝ => φ.1 fun i => ((aI w r : (A F)ˣ) : A F) * v i) =
      fun r => φ.1 fun i => v i + TR.sInf F (x r i) := by
    funext r
    refine congrArg φ.1 (funext fun i => ?_)
    rw [aI_val, add_mul, one_mul, sInf_mul]
  rw [← h2] at h1
  have h3 : HasDerivAt (fun r : ℝ => ((Real.exp (2 * r) : ℝ) : ℂ)) (2 : ℂ) 0 := by
    have h : HasDerivAt (fun r : ℝ => Real.exp (2 * r)) 2 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul 2).exp
    simpa using h.ofReal_comp
  have h4 : HasDerivAt (fun r : ℝ => ((Real.exp (2 * r) : ℝ) : ℂ) * φ.1 fun i => ((aI w r : (A F)ˣ) : A F) * v i) _ 0 :=
    h3.mul h1
  refine h4.congr_deriv ?_
  have h5 : (∑ i, ∑ u, ((x' i u : ℝ) : ℂ) * (O.d u i φ).1 v) = ∑ i, Fo.cw w (v i) * (O.d w i φ).1 v := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single w]
    · simp [x', Fo.cw]
    · intro u _ hu
      simp [x', hu]
    · simp
  rw [h5, h_apply, aI_zero]
  simp [add_comm]

private theorem eR_mul_neg (w : InfinitePlace F) (t : ℝ) : eR w t * eR w (-t) = 1 := by
  rw [← eR_add, add_neg_cancel, eR_zero]

private theorem eR_neg_mul (w : InfinitePlace F) (t : ℝ) : eR w (-t) * eR w t = 1 := by
  rw [← eR_add, neg_add_cancel, eR_zero]

private theorem hasDerivAt_eR_neg (w : InfinitePlace F) :
    HasDerivAt (fun t => eR w (-t)) (-(Pi.single w 1 : TR.Rinf F)) 0 := by
  refine hasDerivAt_pi.2 fun v => ?_
  by_cases h : v = w
  · subst h
    simpa [eR] using (hasDerivAt_neg (0 : ℝ)).exp
  · simpa [eR, h] using hasDerivAt_const (0 : ℝ) (1 : ℝ)

private def cT (w : InfinitePlace F) (t : ℝ) : GL (Fin 2) (TR.Rinf F) :=
  ⟨!![eR w t, 0; 0, eR w (-t)], !![eR w (-t), 0; 0, eR w t],
    by simp [Matrix.mul_fin_two, Matrix.one_fin_two, eR_mul_neg, eR_neg_mul],
    by simp [Matrix.mul_fin_two, Matrix.one_fin_two, eR_mul_neg, eR_neg_mul]⟩

private theorem cT_add (w : InfinitePlace F) (s t : ℝ) : cT w (s + t) = cT w s * cT w t := by
  refine Units.ext ?_
  change !![eR w (s + t), 0; 0, eR w (-(s + t))] = !![eR w s, 0; 0, eR w (-s)] * !![eR w t, 0; 0, eR w (-t)]
  rw [Matrix.mul_fin_two, neg_add, eR_add, eR_add]
  simp

private theorem hasDerivAt_cT (w : InfinitePlace F) : HasDerivAt (fun t => TR.toL (cT w t).val)
    (TR.toL (Matrix.single 0 0 (Pi.single w 1)) - TR.toL (Matrix.single 1 1 (Pi.single w 1))) 0 := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  fin_cases i <;> fin_cases j
  · simpa [cT] using hasDerivAt_eR w
  · simpa [cT] using hasDerivAt_const (0 : ℝ) (0 : TR.Rinf F)
  · simpa [cT] using hasDerivAt_const (0 : ℝ) (0 : TR.Rinf F)
  · simpa [cT] using hasDerivAt_eR_neg w

private theorem gl_mD_aI (w : InfinitePlace F) (t : ℝ) : gl (mD (aI w t)) = TR.infGL F 2 (cT w t) := by
  have hn : ((aI w t)⁻¹ : (A F)ˣ) = aI w (-t) := (aI_neg w t).symm
  refine TR.ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    refine Units.ext (Matrix.ext fun i j => ?_)
    fin_cases i <;> fin_cases j
    · exact pInf_aI w t
    · exact map_zero (TR.pInf F)
    · exact map_zero (TR.pInf F)
    · change TR.pInf F (((aI w t)⁻¹ : (A F)ˣ) : A F) = eR w (-t)
      rw [hn]; exact pInf_aI w (-t)
  · rw [TR.pFin_infGL]
    refine Units.ext (Matrix.ext fun i j => ?_)
    fin_cases i <;> fin_cases j
    · exact pFin_aI w t
    · exact map_zero (pFin F)
    · exact map_zero (pFin F)
    · change pFin F (((aI w t)⁻¹ : (A F)ˣ) : A F) = 1
      rw [hn]; exact pFin_aI w (-t)

variable {E : Type} [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex E] {D : Dat F E}

private theorem om_aI (W : Weil D) (w : InfinitePlace F) (t : ℝ) (φ : S4 F) (v : V4 F) :
    (W.Om (mD (aI w t)) φ).1 v =
      ((Real.exp (2 * t) : ℝ) : ℂ) * φ.1 fun i => ((aI w t : (A F)ˣ) : A F) * v i := by
  have hη : W.η.1 (aI w t) = 1 := by
    have h : aI w t = aI w (t / 2) ^ 2 := by
      rw [pow_two, ← aI_add]
      congr 1
      ring
    rw [h, map_pow]
    exact W.η_sq _
  have he : Real.exp t ^ 2 = Real.exp (2 * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [W.Om_m, hη, ab_aI, he]
  simp

end UpperTheory.ConvolutionTheory.R2.Ff.OneParameterSubgroupCurves

end

open UpperTheory.ConvolutionTheory.R2.Ff.OneParameterSubgroupCurves in
theorem UpperTheory.ConvolutionTheory.R2.Ff.curveH :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (W : Weil D), CurveH O W := by
  intro F E _ _ _ _ _ _ _ D O W w
  have hS := sDiff F O
  refine ⟨fun t => mD (aI w t), cT w, ⟨cT_add w, hasDerivAt_cT w⟩, gl_mD_aI w, fun φ t v => ?_⟩
  have hk := key O hS w φ (fun i => ((aI w t : (A F)ˣ) : A F) * v i)
  have hk' : HasDerivAt (fun r : ℝ => ((Real.exp (2 * r) : ℝ) : ℂ) *
      φ.1 fun i => ((aI w r : (A F)ˣ) : A F) * (((aI w t : (A F)ˣ) : A F) * v i))
      ((O.h w φ).1 fun i => ((aI w t : (A F)ˣ) : A F) * v i) (t - t) := by
    rwa [sub_self]
  have h := (hk'.comp_sub_const t t).const_mul ((Real.exp (2 * t) : ℝ) : ℂ)
  have e : (fun s => (W.Om (mD (aI w s)) φ).1 v) = fun s => ((Real.exp (2 * t) : ℝ) : ℂ) *
      (((Real.exp (2 * (s - t)) : ℝ) : ℂ) *
        φ.1 fun i => ((aI w (s - t) : (A F)ˣ) : A F) * (((aI w t : (A F)ˣ) : A F) * v i)) := by
    funext s
    rw [om_aI W w s φ v, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    have h1 : 2 * t + 2 * (s - t) = 2 * s := by ring
    rw [h1]
    refine congrArg _ (congrArg φ.1 (funext fun i => ?_))
    rw [← mul_assoc, ← Units.val_mul, ← aI_add, sub_add_cancel]
  change HasDerivAt (fun s => (W.Om (mD (aI w s)) φ).1 v) ((W.Om (mD (aI w t)) (O.h w φ)).1 v) t
  rw [e, om_aI W w t (O.h w φ) v]
  exact h
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.moveH :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), MoveH O W M π := by
  intro F E _ _ _ _ _ _ _ D O W M π f hf φ hφ w h
  obtain ⟨G, c, hP, hG, hD⟩ := curveH F E D O W w
  have hF := opsFock F E D O
  have hh : O.h w φ ∈ Fock D.δ := by
    have h2 : O.h w φ = (∑ i, O.x w i (O.d w i φ)) + (2 : ℂ) • φ := by
      simp [Fo.Ops.h, LinearMap.sum_apply, two_smul, LinearMap.add_apply, Module.End.mul_apply, one_add_one_eq_two.symm, add_mul, Module.End.one_apply]
      rw [add_smul, one_smul]
    rw [h2]
    exact add_mem (sum_mem fun i _ => (hF w i _ (hF w i φ hφ).2).1) (Submodule.smul_mem _ _ hφ)
  have hm := congrFun (mov F E D W M π f hf φ hφ (O.h w φ) hh G c _ hP hG (hD φ)) h
  rw [hm, map_sub, LinearMap.sub_apply]
  rfl
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.lieLift :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), Fo.LieLift O W M π := by
  intro F E _ _ _ _ _ _ _ D O W M π f hf φ hφ Φ hΦ X h
  obtain ⟨Y, s, hY, rfl, hs⟩ := lieSplit X
  obtain ⟨hcen, hdadd, -, htr⟩ := dLCen F E D O
  obtain ⟨ladd, lsmul, radd, rsmul⟩ := lin F E D W M π
  have hL := lieL F E D O W M π f hf φ hφ Y hY Φ hΦ
  have hZ := lieZ F E D W M π f hf φ hφ s Φ hΦ
  have hH := moveH F E D O W M π f hf φ hφ
  have hE : ∀ (w : InfinitePlace F) (i j : Fin 2), TR.Eop w i j f ∈ π.V := fun w i j => π.stable (.lie _) f hf
  have h0 : lift W M (0 : GL (Fin 2) (A F) → ℂ) φ = 0 := by simpa using rsmul f.1 0 φ
  have hl0 : lift W M f.1 (0 : S4 F) = 0 := by simpa using lsmul f.1 0 φ
  have sumF : ∀ (S : Finset (E →+* ℂ)) (c : (E →+* ℂ) → ℂ) (g : (E →+* ℂ) → TR.Sm F 2), (∀ τ, g τ ∈ π.V) →
      lift W M (∑ τ ∈ S, c τ • g τ).1 φ = ∑ τ ∈ S, c τ • lift W M (g τ).1 φ := by
    intro S c g hg
    induction S using Finset.induction_on with
    | empty => simpa using h0
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        radd _ (π.V.smul_mem _ (hg a)) _ (sum_mem fun τ _ => π.V.smul_mem _ (hg τ)) φ hφ, ih]
      congr 1
      exact rsmul (g a).1 (c a) φ
  have sumP : ∀ (S : Finset (E →+* ℂ)) (c : (E →+* ℂ) → ℂ) (ψ : (E →+* ℂ) → S4 F), (∀ τ, ψ τ ∈ Fock D.δ) →
      lift W M f.1 (∑ τ ∈ S, c τ • ψ τ) = ∑ τ ∈ S, c τ • lift W M f.1 (ψ τ) := by
    intro S c ψ hψ
    induction S using Finset.induction_on with
    | empty => simpa using hl0
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        ladd f hf _ (Submodule.smul_mem _ _ (hψ a)) _ (sum_mem fun τ _ => Submodule.smul_mem _ _ (hψ τ)), ih,
        lsmul]
  have hh : ∀ w, O.h w φ ∈ Fock D.δ := by
    intro w
    have e : O.h w φ = ∑ i, O.x w i (O.d w i φ) + (φ + φ) := by
      have h2 : (2 : Module.End ℂ (S4 F)) = 1 + 1 := one_add_one_eq_two.symm
      simp [Fo.Ops.h, h2, LinearMap.sum_apply]
    rw [e]
    exact add_mem (sum_mem fun i _ => (opsFock F E D O w i _ (opsFock F E D O w i φ hφ).2).1) (add_mem hφ hφ)
  have hd := dLFock F E D O Y φ hφ
  have e1 : O.dL D (Y + zE s) φ = O.dL D Y φ + (-1 : ℂ) • ∑ τ : E →+* ℂ, coord τ s • O.h (Fo.pl F τ) φ := by
    rw [hdadd, (hcen s)]
    simp [LinearMap.sum_apply]
  have hS : ∑ τ : E →+* ℂ, coord τ s • O.h (Fo.pl F τ) φ ∈ Fock D.δ :=
    sum_mem fun τ _ => Submodule.smul_mem _ _ (hh _)
  have e2 : (TR.lie F 2 (zF (trI F s)) f) = ∑ τ : E →+* ℂ, coord τ s • (TR.Eop (Fo.pl F τ) 0 0 f + TR.Eop (Fo.pl F τ) 1 1 f) := by
    rw [htr s]
    simp [LinearMap.sum_apply]
  have ePlus : ∀ w, lift W M (TR.Eop w 0 0 f + TR.Eop w 1 1 f : TR.Sm F 2).1 φ =
      lift W M (TR.Eop w 0 0 f).1 φ + lift W M (TR.Eop w 1 1 f).1 φ := fun w =>
    radd _ (hE w 0 0) _ (hE w 1 1) φ hφ
  have eMinus : ∀ w, lift W M (TR.Eop w 0 0 f - TR.Eop w 1 1 f : TR.Sm F 2).1 φ =
      lift W M (TR.Eop w 0 0 f).1 φ - lift W M (TR.Eop w 1 1 f).1 φ := by
    intro w
    have e : (TR.Eop w 0 0 f - TR.Eop w 1 1 f : TR.Sm F 2) = TR.Eop w 0 0 f + (-1 : ℂ) • TR.Eop w 1 1 f := by
      rw [neg_one_smul, sub_eq_add_neg]
    rw [e, radd _ (hE w 0 0) _ (π.V.smul_mem _ (hE w 1 1)) φ hφ]
    have := rsmul (TR.Eop w 1 1 f).1 (-1) φ
    change _ + lift W M ((-1 : ℂ) • (TR.Eop w 1 1 f).1) φ = _
    rw [this, neg_one_smul, sub_eq_add_neg]
  have hlhs : (lie E 2 (Y + zE s) Φ).1 h = lift W M f.1 (O.dL D Y φ) h +
      lift W M (TR.lie F 2 (zF (trI F s)) f).1 φ h := by
    rw [map_add (f := _), LinearMap.add_apply]
    change (lie E 2 Y Φ).1 h + (lie E 2 (zE s) Φ).1 h = _
    rw [hL, hZ]
  rw [hlhs, e1, ladd f hf _ hd _ (Submodule.smul_mem _ _ hS), lsmul, sumP _ _ _ (fun τ => hh _), e2,
    sumF _ _ _ (fun τ => add_mem (hE _ 0 0) (hE _ 1 1)), hs]
  simp only [ePlus, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  have hHh : ∀ w, lift W M f.1 (O.h w φ) h =
      -(lift W M (TR.Eop w 0 0 f).1 φ h - lift W M (TR.Eop w 1 1 f).1 φ h) := fun w => by
    rw [hH w h, eMinus]; rfl
  simp only [hHh, map_add (f := _), add_mul, Finset.mul_sum]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  ring
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.cap :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Cap W M π :=
  fun F E _ _ _ _ _ _ _ D W M π =>
    Fo.capOf F E D W M π (fun O => Ff.lieLift F E D O W M π) fun O => Ff.moveE F E D O W M π
