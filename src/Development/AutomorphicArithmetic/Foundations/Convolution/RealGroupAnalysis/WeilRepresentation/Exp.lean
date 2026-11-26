module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Expand1
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.CharZero

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ThetaFourierCoeffZeroAndEqShiftedWhittaker
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.PtMove
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem conj_ne {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E)
    {ξ : Fin 2 → F} (hξ : ξ ≠ 0) : algebraMap F E (ξ 0) - algebraMap F E (ξ 1) * D.θ ≠ 0 := by
  intro h
  have hl := Fintype.linearIndependent_iff.1 D.b.linearIndependent ![ξ 0, -ξ 1] (by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, D.b0, D.b1, Algebra.smul_def, map_neg]
    simp only [Matrix.cons_val_fin_one, mul_one, map_neg]
    linear_combination h)
  apply hξ
  ext i
  fin_cases i
  · simpa using hl 0
  · simpa using hl 1

private theorem coe_al {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E)
    (ξ : Fin 2 → F) (h : algebraMap F E (ξ 0) - algebraMap F E (ξ 1) * D.θ ≠ 0) :
    ((al D ξ : (A E)ˣ) : A E) = D.mkE (rt (ξ 0)) (-rt (ξ 1)) := by
  have e := D.mkE_rt (ξ 0) (-ξ 1)
  have e' : -rt (ξ 1) = (rt (-ξ 1) : A F) := (map_neg _ _).symm
  rw [e', e, al, dite_eq_right h, IdeleGroup.coe_diagonal]
  simp [sub_eq_add_neg]

private theorem vcD {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) (x : G1 F) :
    (gl (cD t x)).val = !![x 0 0, x 0 1 * ((t⁻¹ : (A F)ˣ) : A F); (t : A F) * x 1 0, x 1 1] := rfl

private theorem vgl {F : Type} [Field F] [NumberField F] (x : G1 F) : (gl x).val = x.1 := rfl

private theorem vmD {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) :
    (gl (mD t)).val = !![(t : A F), 0; 0, ((t⁻¹ : (A F)ˣ) : A F)] := rfl

private theorem cD_dM {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) (x : G1 F) :
    gl (cD t x) * dM t = dM t * gl x := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, vcD, vgl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dM, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc] <;> ring

private theorem dM_mD {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) : dM t * gl (mD t) = aE t := by
  refine Units.ext ?_
  rw [Units.val_mul, vmD]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dM, aE, Matrix.mul_apply, Fin.sum_univ_two]

private theorem pt_move {F : Type} [Field F] [NumberField F] (t n : (A F)ˣ) (g : G1 F) :
    gl (cD t (mD t * g)) * dM (t * n) = aE t * (gl g * dM n) := by
  rw [UpperTheory.ConvolutionTheory.R2.dM_mul, ← mul_assoc, cD_dM, gl_mul, ← mul_assoc (dM t), dM_mD, mul_assoc]

theorem UpperTheory.ConvolutionTheory.R2.G.wxPt :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (ξ : Fin 2 → F), ξ ≠ 0 → ∃ t : Fˣ, ∀ f : GL (Fin 2) (A F) → ℂ, Pp.Lf f → ∀ φ h g,
    w1 W f φ (aE (al D ξ) * h) (cD (IdeleGroup.diagonal F t) (mD (IdeleGroup.diagonal F t) * g)) = wx W f φ h ξ g := by
  intro F E _ _ _ _ _ _ _ D W ξ hξ
  have hz := conj_ne D hξ
  have hα := coe_al D ξ hz
  set α := al D ξ with hαdef
  let t : Fˣ := Units.map (Algebra.norm F : E →* F) (Units.mk0 _ hz)
  have hT : ideleNorm F E α = IdeleGroup.diagonal F t := by
    rw [hαdef, al, dite_eq_right hz, ideleNorm_diagonal]
  have hco : D.co (α : A E) = ![rt (ξ 0), -rt (ξ 1)] := by rw [hα, D.co_mkE]
  have ht : (t : F) = ξ 0 ^ 2 - D.δ * ξ 1 ^ 2 := by
    haveI := AdeleBaseChange.nontrivial_adeleRing F
    apply (algebraMap F (A F)).injective
    have h1 := D.coe_ideleNorm α
    rw [hT, IdeleGroup.coe_diagonal, hco] at h1
    simpa using h1
  refine ⟨t, fun f hf φ h g => ?_⟩
  set T := IdeleGroup.diagonal F t with hTdef
  have hnu : nu F (aE α * h) = T * nu F h := by rw [nu_mul, nu_aE, hT]
  have hpoint : ![T * (0 : A F), ((T⁻¹ : (A F)ˣ) : A F) * ((ideleNorm F E α : (A F)ˣ) * 1),
      T * D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE 1 0) 0, T * D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE 1 0) 1] = pt ξ := by
    have hb : am E (T : A F) * ((α⁻¹ : (A E)ˣ) : A E) = D.mkE (rt (ξ 0)) (rt (ξ 1)) := by
      rw [← hT, D.am_ideleNorm, mul_comm (α : A E), mul_assoc, Units.mul_inv, mul_one, hα, D.bar_mkE, neg_neg]
    have hc := D.co_am_mul (T : A F) ((α⁻¹ : (A E)ˣ) : A E)
    rw [hb, D.co_mkE] at hc
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    simp only [Pi.smul_apply, smul_eq_mul] at h0 h1
    rw [D.mkE_one, mul_one, hT]
    simp [pt, ← h0, ← h1]
  have hhat : hat (W.Om (cD T (mD T * g)) (W.L (aE α * h) φ)).1 ![0, 1, 1, 0] = hat (W.Om g (W.L h φ)).1 (pt ξ) := by
    have hcm : W.Om (cD T (mD T * g)) (W.L (aE α) (W.L h φ)) = W.L (aE α) (W.Om (mD T * g) (W.L h φ)) := by
      have := W.comm (aE α) (mD T * g)
      rw [nu_aE, hT] at this
      exact (LinearMap.congr_fun this (W.L h φ)).symm
    rw [map_mul, Module.End.mul_apply, hcm]
    have hS := hatSt F E D W
    have e1 := hS.aE α (W.Om (mD T * g) (W.L h φ)) 0 1 1 0
    have e2 := hS.m T (W.Om g (W.L h φ))
    have e3 : ((W.η.1 T : ℂˣ) : ℂ) = 1 := by rw [← hT, W.η_norm]; rfl
    have e4 : ab T = 1 := ab_diagonal t
    rw [e1, map_mul, Module.End.mul_apply, e2, e3, e4]
    have hv := hpoint
    rw [← hv]
    simp
  have hw : ∫ b in fundamentalSet F, f (gl (nU b) * (gl g * dM (nu F h))) * ψ (rt (ξ 0 ^ 2 - D.δ * ξ 1 ^ 2) * b) ∂(adeleMeasure F) =
      Wf f (aE T * (gl g * dM (nu F h))) := by
    rw [← ht]
    exact Pp.wfT F f hf t _
  simp only [w1, wx]
  rw [hhat, hnu, pt_move, hw]
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem normOneIntegral_diagonal_invariant {F : Type} [Field F] [NumberField F] (M₀ : Meas F) (t : IdeleGroup F) (ht : ab t = 1)
    (v : G1 F → ℂ) : M₀.I0 (fun g => v (mD t * g)) = M₀.I0 v := by
  haveI := M₀.prob
  let e : (IdeleGroup F × G1 F) ≃ᵐ (IdeleGroup F × G1 F) :=
    (MeasurableEquiv.mulLeft t).prodCongr (MeasurableEquiv.refl _)
  have hp : MeasurePreserving e M₀.ν M₀.ν :=
    (measurePreserving_mul_left (ideleMeasure F) t).prod (MeasurePreserving.id M₀.κ)
  have hi := hp.integral_comp' (g := iw v)
  rw [Meas.I0, Meas.I0, ← hi]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  change iw (fun g => v (mD t * g)) p = iw v (t * p.1, p.2)
  simp only [iw]
  rw [M.ab_mul, ht, one_mul, M.mD_mul, mul_assoc]

theorem UpperTheory.ConvolutionTheory.R2.G.thetaFourierCoeff_zero_and_eq_shifted_whittaker :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ h, Wx W M f.1 φ h 0 = 0 ∧ Wx W M f.1 φ h ![1, 0] = W1 W M f.1 φ h ∧
    ∀ ξ, ξ ≠ 0 → Wx W M f.1 φ h ξ = W1 W M f.1 φ (aE (al D ξ) * h) := by
  intro F E _ _ _ _ _ _ _ D W M₀ π f hf φ hφ h
  obtain ⟨hL, hz⟩ := Pp.cuspZero F π f hf
  refine ⟨?_, ?_, fun ξ hξ => ?_⟩
  · have e : wx W f.1 φ h 0 = fun _ => 0 := by
      funext g
      have h1 : ∀ b : A F, ψ (rt ((0 : Fin 2 → F) 0 ^ 2 - D.δ * (0 : Fin 2 → F) 1 ^ 2) * b) = 1 := by
        intro b
        simp [ψ]
      simp only [wx, h1, mul_one, hz, zero_mul]
    simp [Wx, e, Meas.I0, iw]
  · have e : wx W f.1 φ h ![1, 0] = w1 W f.1 φ h := by
      funext g
      simp [wx, w1, Wf, pt]
    rw [Wx, e, W1]
  · obtain ⟨t, ht⟩ := wxPt F E D W ξ hξ
    obtain ⟨-, -, a1, a2, a3⟩ := UpperTheory.ConvolutionTheory.R2.conv F E D W M₀ π f hf φ hφ (aE (al D ξ) * h)
    have hc := ((UpperTheory.ConvolutionTheory.R2.inv F M₀ _ a1 a2 a3).2 (IdeleGroup.diagonal F t)).2
    have e : wx W f.1 φ h ξ = fun g => (fun g => w1 W f.1 φ (aE (al D ξ) * h) (cD (IdeleGroup.diagonal F t) g)) (mD (IdeleGroup.diagonal F t) * g) :=
      funext fun g => (ht f.1 hL φ h g).symm
    have hm := normOneIntegral_diagonal_invariant M₀ (IdeleGroup.diagonal F t) (ab_diagonal t)
      (fun g => w1 W f.1 φ (aE (al D ξ) * h) (cD (IdeleGroup.diagonal F t) g))
    rw [Wx, e, hm, hc, W1, ab_diagonal t]
    simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Exp
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.exp :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Exp W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ h
  have hδ : D.δ ≠ 0 := by
    intro h0
    have h := D.sq
    rw [h0, map_zero] at h
    exact D.b.ne_zero 1 (by rw [D.b1, (pow_eq_zero_iff two_ne_zero).1 h])
  have hO := G.orth F D.δ hδ (T0 W M f.1 φ h) (Wx W M f.1 φ h) (fun u => lift W M f.1 φ (nE D u * h))
    (G.expand1 F E D W M π f hf φ hφ h).1 fun u => by
      rw [(G.expand1 F E D W M π f hf φ hφ _).2, (G.transN F E D W M f.1 φ h u).1]
      simp only [(G.transN F E D W M f.1 φ h u).2]
  exact hO.2.2.2.trans (G.thetaFourierCoeff_zero_and_eq_shifted_whittaker F E D W M π f hf φ hφ h).2.1
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsBis
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.GoodLift
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem delta_ne {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (D : Dat F E) : D.δ ≠ 0 := by
  intro h0
  have hθ : D.θ = 0 := by
    have h := D.sq
    rw [h0, map_zero] at h
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h
  exact D.b.ne_zero 1 (by rw [D.b1, hθ])

theorem UpperTheory.ConvolutionTheory.R2.G.goodLift :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ThetaLiftTrivialOrbitTermsVanish W M π → ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, Good D (lift W M f.1 φ) := by
  intro F E _ _ _ _ _ _ _ D W M π hN f hf φ hφ
  have hδ : D.δ ≠ 0 := delta_ne D
  have hex := fun h => UpperTheory.ConvolutionTheory.R2.G.expand1 F E D W M π f hf φ hφ h
  have hw := fun h => UpperTheory.ConvolutionTheory.R2.G.thetaFourierCoeff_zero_and_eq_shifted_whittaker F E D W M π f hf φ hφ h
  have ho : ∀ h, _ := fun h => UpperTheory.ConvolutionTheory.R2.G.orth F D.δ hδ 0 (Wx W M f.1 φ h)
    (fun u => lift W M f.1 φ (nE D u * h)) (hex h).1 (fun u => by
      have e := (hex (nE D u * h)).2
      rw [hN f hf φ hφ (nE D u * h)] at e
      rw [e]
      congr 1
      refine tsum_congr fun ξ => ?_
      exact (UpperTheory.ConvolutionTheory.R2.G.transN F E D W M f.1 φ h u).2 ξ)
  have hWE : ∀ h, WE D (lift W M f.1 φ) h = W1 W M f.1 φ h := fun h => by
    have e : WE D (lift W M f.1 φ) h = Wx W M f.1 φ h ![1, 0] := (ho h).2.2.2
    rw [e, (hw h).2.1]
  refine
    { left := (UpperTheory.ConvolutionTheory.R2.equiv F E D W M π f hf φ).1
      int0 := fun h => (ho h).1
      int1 := fun h => (ho h).2.1
      zero := fun h => ?_
      sum := fun h => ?_ }
  · have e := (ho h).2.2.1
    rw [e, (hw h).1, add_zero]
  · have hs : HasSum (fun ξ => Wx W M f.1 φ h ξ) (lift W M f.1 φ h) := by
      have e := (hex h).2
      rw [hN f hf φ hφ h, zero_add] at e
      rw [e]
      exact (Summable.of_norm (hex h).1).hasSum
    have hsup : Function.support (fun ξ => Wx W M f.1 φ h ξ) ⊆ {ξ : Fin 2 → F | ξ ≠ 0} := by
      intro ξ hξ h0
      apply hξ
      have h0' : ξ = 0 := h0
      simpa [h0'] using (hw h).1
    have hs' := (hasSum_subtype_iff_of_support_subset hsup).2 hs
    have hs'' : HasSum (fun ξ : Rw F => Wx W M f.1 φ h ξ.1) (lift W M f.1 φ h) := hs'
    have e : (fun ξ : Rw F => WE D (lift W M f.1 φ) (aE (al D ξ.1) * h)) = fun ξ : Rw F => Wx W M f.1 φ h ξ.1 :=
      funext fun ξ => by
        rw [hWE]
        exact ((hw h).2.2 ξ.1 ξ.2).symm
    rw [e]
    exact hs''
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.CuspE
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors


open GroundTheory.Automorphic.FourierWhittaker in
private noncomputable def latE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) :
    vecLattice F (Fin 2) ≃ AdeleRing.principalSubgroup (𝓞 E) E where
  toFun g := ⟨D.coE.symm g.1, by
    obtain ⟨_, ξ, rfl⟩ := g
    refine ⟨algebraMap F E (ξ 0) + algebraMap F E (ξ 1) * D.θ, ?_⟩
    exact (D.mkE_rt (ξ 0) (ξ 1)).symm⟩
  invFun y := ⟨D.coE y.1, by
    obtain ⟨_, z, rfl⟩ := y
    exact mem_vecLattice.2 ⟨fun i => D.b.repr z i, funext fun i => (D.co_rt z i).symm⟩⟩
  left_inv g := Subtype.ext (D.coE.apply_symm_apply g.1)
  right_inv y := Subtype.ext (D.coE.symm_apply_apply y.1)

open GroundTheory.Automorphic.FourierWhittaker in
theorem UpperTheory.ConvolutionTheory.R2.G.cuspE :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (Φ : GL (Fin 2) (A E) → ℂ), (∀ γ h, Φ (ratGL E 2 γ * h) = Φ h) →
    (∀ h, ∫ u in FS2 F, Φ (nE D u * h) ∂(adeleMeasurePi F) = 0) → GlobalTheory.CuspRep.IsCuspidal Φ := by
  intro F E _ _ _ _ _ D Φ hl h0
  refine cuspOf E Φ hl fun h => ?_
  let β : (Fin 2 → A F) ≃ₜ+ A E := D.coE.symm
  let m := β.toHomeomorph.toMeasurableEquiv
  haveI : (adeleMeasurePi F (ι := Fin 2)).IsAddHaarMeasure := inferInstanceAs (Measure.pi fun _ : Fin 2 => adeleMeasure F).IsAddHaarMeasure
  haveI : ((adeleMeasurePi F (ι := Fin 2)).map m).IsAddHaarMeasure := β.isAddHaarMeasure_map (adeleMeasurePi F)
  have hF : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 E) E) (m '' FS2 F) ((adeleMeasurePi F (ι := Fin 2)).map m) :=
    (isAddFundamentalDomain_vecDomain (K := F) (ι := Fin 2)).image_of_equiv m.toEquiv
      (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving (latE D).symm
      fun y x => by
        change β (D.coE y.1 + x) = y.1 + β x
        rw [map_add (f := _)]
        congr 1
        exact D.coE.symm_apply_apply y.1
  have hF' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 E) E) (m '' FS2 F) (adeleMeasure E) :=
    hF.mono (Measure.absolutelyContinuous_isAddHaarMeasure _ _)
  have hper : ∀ (g : AdeleRing.principalSubgroup (𝓞 E) E) (x : A E),
      Φ (gl (nU (g +ᵥ x)) * h) = Φ (gl (nU x) * h) := by
    rintro ⟨_, k, rfl⟩ x
    obtain ⟨γ, hγ⟩ := Pp.rat_n k
    change Φ (gl (nU (rt k + x)) * h) = _
    rw [Pp.n_add, ← hγ, mul_assoc, hl]
  haveI : Countable (AdeleRing.principalSubgroup (𝓞 E) E) := (latE D).symm.injective.countable
  have h1 := (isAddFundamentalDomain_fundamentalSet E).setIntegral_eq hF' (f := fun x => Φ (gl (nU x) * h)) hper
  rw [h1, Measure.isAddLeftInvariant_eq_smul (adeleMeasure E) ((adeleMeasurePi F (ι := Fin 2)).map m), Measure.restrict_smul,
    integral_smul_nnreal_measure, m.measurableEmbedding.setIntegral_map, m.injective.preimage_image]
  have h3 : ∫ u in FS2 F, Φ (gl (nU (m u)) * h) ∂(adeleMeasurePi F) = 0 := h0 h
  rw [h3, smul_zero]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.GoodSpan
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.goodSpan :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E), Good D 0 ∧ (∀ Φ Φ', Good D Φ → Good D Φ' → Good D (Φ + Φ')) ∧ ∀ (c : ℂ) Φ, Good D Φ → Good D (c • Φ) := by
  intro F E _ _ _ _ _ D
  have hWE : ∀ (Φ : GL (Fin 2) (A E) → ℂ) h,
      WE D Φ h = ∫ u in FS2 F, Φ (nE D u * h) * ψ (2 * u 0) ∂(adeleMeasurePi F) := fun _ _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨fun _ _ => rfl, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun h => ?_⟩
    · simpa using (integrableOn_zero (μ := adeleMeasurePi F) (s := FS2 F))
    · simpa using (integrableOn_zero (μ := adeleMeasurePi F) (s := FS2 F))
    · simp
    · have : ∀ ξ : Rw F, WE D (0 : GL (Fin 2) (A E) → ℂ) (aE (al D ξ.1) * h) = 0 := by
        intro ξ
        rw [hWE]
        simp
      simp only [this]
      exact hasSum_zero
  · intro Φ Φ' h1 h2
    refine ⟨fun γ h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · simp only [Pi.add_apply, h1.left, h2.left]
    · exact (h1.int0 h).add (h2.int0 h)
    · have heq : (fun u => (Φ + Φ') (nE D u * h) * ψ (2 * u 0))
          = (fun u => Φ (nE D u * h) * ψ (2 * u 0)) + fun u => Φ' (nE D u * h) * ψ (2 * u 0) := by
        funext u
        simp only [Pi.add_apply, add_mul]
      rw [heq]
      exact (h1.int1 h).add (h2.int1 h)
    · simp only [Pi.add_apply]
      rw [integral_add (h1.int0 h) (h2.int0 h), h1.zero, h2.zero, add_zero]
    · have : ∀ ξ : Rw F, WE D (Φ + Φ') (aE (al D ξ.1) * h)
          = WE D Φ (aE (al D ξ.1) * h) + WE D Φ' (aE (al D ξ.1) * h) := by
        intro ξ
        simp only [hWE, Pi.add_apply, add_mul]
        exact integral_add (h1.int1 _) (h2.int1 _)
      simp only [this, Pi.add_apply]
      exact (h1.sum h).add (h2.sum h)
  · intro c Φ h1
    refine ⟨fun γ h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · simp only [Pi.smul_apply, h1.left]
    · exact (h1.int0 h).const_mul c
    · have heq : (fun u => (c • Φ) (nE D u * h) * ψ (2 * u 0))
          = fun u => c * (Φ (nE D u * h) * ψ (2 * u 0)) := by
        funext u
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
      rw [heq]
      exact (h1.int1 h).const_mul c
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [integral_const_mul, h1.zero, mul_zero]
    · have : ∀ ξ : Rw F, WE D (c • Φ) (aE (al D ξ.1) * h) = c * WE D Φ (aE (al D ξ.1) * h) := by
        intro ξ
        simp only [hWE, Pi.smul_apply, smul_eq_mul, mul_assoc]
        exact integral_const_mul _ _
      simp only [this, Pi.smul_apply, smul_eq_mul]
      exact (h1.sum h).mul_left c
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.cusp :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Cusp W M π := by
  intro F E _ _ _ _ _ _ _ D W M π h0 Φ hΦ
  have hG : Good D Φ.1 := by
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, φ, hφ, e⟩ := hx
      rw [e]
      exact G.goodLift F E D W M π h0 f hf φ hφ
    | zero => exact (G.goodSpan F E D).1
    | add x y _ _ hx hy => exact (G.goodSpan F E D).2.1 _ _ hx hy
    | smul c x _ hx => exact (G.goodSpan F E D).2.2 c _ hx
  refine ⟨G.cuspE F E D _ hG.left hG.zero, fun hW => Subtype.ext (funext fun h => ?_)⟩
  have hs := hG.sum h
  simp only [hW] at hs
  exact hs.unique hasSum_zero
end
