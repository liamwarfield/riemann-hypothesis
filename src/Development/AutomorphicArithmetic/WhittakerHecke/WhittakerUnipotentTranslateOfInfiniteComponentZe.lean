module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.FixTr

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.WhittakerUnipotentTranslateOfInfiniteComponentZe
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.whittaker_unipotent_translate_of_infinite_component_zero :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (φ : GL (Fin 2) (A E) → ℂ), Continuous φ → (∀ γ g, φ (ratGL E 2 γ * g) = φ g) → ∀ x : A ℚ, x.1 = 0 → ∀ (y : (A ℚ)ˣ) (X : GL (Fin 2) (Cinf E)), Wo D (fun g => φ (g * nu D x)) (em E (aE y) * infGL E 2 X) = ψ (-((y : A ℚ) * x)) * Wo D φ (em E (aE y) * infGL E 2 X) := by
  intro E _ _ _ D φ _ hL x hx y X
  have hfst : (AdeleBaseChange.adeleMap ℚ E x).1 = 0 := by
    obtain ⟨c1, c2⟩ := x
    obtain rfl : c1 = 0 := hx
    exact map_zero (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := ℚ) (L := E))
  have h0 : pInf E (D.mkE 0 x) = 0 := by
    have h1 : (D.mkE 0 x).1 = 0 := by
      have e : D.mkE 0 x = AdeleBaseChange.adeleMap ℚ E x * rt D.θ := by
        simp only [Dat.mkE, map_zero, zero_add]
      rw [e]
      change (AdeleBaseChange.adeleMap ℚ E x).1 * _ = 0
      rw [hfst, zero_mul]
    change (infEq E).symm (D.mkE 0 x).1 = 0
    rw [h1]
    exact map_zero _
  have hk : GeneralLinearGroup.map (pInf E) (Xg.nu D x) = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    change pInf E ((!![1, D.mkE 0 x; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) i j) = (1 : Matrix (Fin 2) (Fin 2) (Cinf E)) i j
    fin_cases i <;> fin_cases j <;> simp [h0]
  have hc : infGL E 2 X * Xg.nu D x = Xg.nu D x * infGL E 2 X := by
    have e := infGL_mul_finGL (Xg.nu D x)
    rw [hk, map_one, one_mul] at e
    rw [← e]
    exact infGL_comm X _
  rw [Nz.Wo_right, mul_assoc, hc, ← mul_assoc, Xg.nu, Nz.em_conj, mul_assoc, Nz.Wo_shift D hL]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.WhittakerUnipotentMulEqAdditiveCharMul
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.whittaker_unipotent_mul_eq_additiveChar_mul :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (f : GL (Fin 2) (A E) → ℂ), Pp.Lf f → ∀ (v : Fin 2 → A ℚ) (h : GL (Fin 2) (A E)),
        Wo D f (nE D v * h) = ψ (-(v 1)) * Wo D f h := by
  intro E _ _ D f hf v h
  have hadd : ∀ u w : Fin 2 → A ℚ, nE D (u + w) = nE D u * nE D w := fun u w => by
    simp only [nE, Pi.add_apply, D.mkE_add, Pp.n_add]
  let G : (Fin 2 → A ℚ) → ℂ := fun u => f (nE D u * h) * ψ (u 1)
  have hper : ∀ ξ ∈ GroundTheory.Automorphic.FourierWhittaker.vecLattice ℚ (Fin 2), ∀ x, G (ξ + x) = G x := by
    intro ξ hξ x
    obtain ⟨η, rfl⟩ := GroundTheory.Automorphic.FourierWhittaker.mem_vecLattice.1 hξ
    have e1 : D.mkE (rt (η 0) + x 0) (rt (η 1) + x 1) =
        rt (algebraMap ℚ E (η 0) + algebraMap ℚ E (η 1) * D.θ) + D.mkE (x 0) (x 1) := by
      rw [D.mkE_add, D.mkE_rt]
    change f (gl (nU (D.mkE (rt (η 0) + x 0) (rt (η 1) + x 1))) * h) * ψ (rt (η 1) + x 1) =
      f (gl (nU (D.mkE (x 0) (x 1))) * h) * ψ (x 1)
    rw [e1, hf.per, Pp.ψ_add, Pp.ψ_rt, one_mul]
  have key : ∫ u in FS2 ℚ, G (u + v) ∂(adeleMeasurePi ℚ) = ∫ u in FS2 ℚ, G u ∂(adeleMeasurePi ℚ) :=
    GroundTheory.Automorphic.FourierWhittaker.setIntegral_comp_add v hper
  have pt : ∀ u : Fin 2 → A ℚ, f (nE D u * (nE D v * h)) * ψ (u 1) = ψ (-(v 1)) * G (u + v) := by
    intro u
    have e2 : ψ (u 1) = ψ (-(v 1)) * ψ ((u + v) 1) := by
      rw [← Pp.ψ_add]
      congr 1
      simp only [Pi.add_apply]
      ring
    change _ = ψ (-(v 1)) * (f (nE D (u + v) * h) * ψ ((u + v) 1))
    rw [hadd, mul_assoc, e2]
    ring
  simp only [Wo, pt]
  rw [integral_const_mul]
  exact congrArg _ key
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.RealIdeleMulAbsContinuousAndUnitAbsEqOne
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private noncomputable def cu (y : ℝ) (h : y ≠ 0) : (TR.Rinf ℚ)ˣ :=
  ⟨fun _ => y, fun _ => y⁻¹, funext fun _ => mul_inv_cancel₀ h, funext fun _ => inv_mul_cancel₀ h⟩

private theorem iy_eq {y : ℝ} (h : y ≠ 0) : iy y = TR.infId ℚ (cu y h) := dif_neg h

private theorem nrm_unit {v : H.P ℚ} {x : H.Kv v} (h : Valued.v x = 1) : ‖x‖ = 1 :=
  le_antisymm ((Valued.toNormedField.norm_le_one_iff (x := x)).2 h.le)
    ((Valued.toNormedField.one_le_norm_iff (x := x)).2 h.ge)

theorem UpperTheory.realIdele_mul_abs_continuous_and_unit_abs_eq_one :
    (∀ y y' : ℝ, y ≠ 0 → y' ≠ 0 → iy (y * y') = iy y * iy y') ∧ (∀ y : ℝ, y ≠ 0 → ab (iy y) = |y|) ∧ Continuous (fun t : ℝ => iy (Real.exp t)) ∧ ∀ u ∈ UU, ab u = 1 := by
  refine ⟨fun y y' hy hy' => ?_, fun y hy => ?_, ?_, fun u hu => ?_⟩
  · rw [iy_eq (mul_ne_zero hy hy'), iy_eq hy, iy_eq hy', ← map_mul]
    congr 1
    exact Units.ext rfl
  · rw [iy_eq hy]
    show (IdeleGroup.ideleModule ℚ (TR.infId ℚ (cu y hy)) : ℝ) = |y|
    rw [GlobalTheory.HenQ.DetSplit.ideleModule_infId]
    simp [cu]
  · have hu : Continuous fun t : ℝ => cu (Real.exp t) (Real.exp_ne_zero t) := by
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · exact continuous_pi fun _ => Real.continuous_exp
      · exact continuous_pi fun _ => Real.continuous_exp.inv₀ Real.exp_ne_zero
    have he : (fun t : ℝ => iy (Real.exp t)) = fun t => TR.infId ℚ (cu (Real.exp t) (Real.exp_ne_zero t)) :=
      funext fun t => iy_eq (Real.exp_ne_zero t)
    rw [he]
    exact (TR.continuous_infId ℚ).comp hu
  · show (IdeleGroup.ideleModule ℚ u : ℝ) = 1
    rw [IdeleGroup.ideleModule_eq]
    have h1 : ((u : A ℚ)).1 = 1 := hu.1
    have h2 : ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), ‖((u : A ℚ)).2 v‖ = 1 :=
      finprod_eq_one_of_forall_eq_one fun v => nrm_unit (hu.2 v)
    rw [h1, h2, mul_one]
    exact Finset.prod_eq_one fun w _ => by
      rw [show (1 : InfiniteAdeleRing ℚ) w = 1 from rfl, norm_one, one_pow]
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.WhittakerPeriodAddSmulAndNormLe
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem volume_fundamental_domain_two : adeleMeasurePi (ι := Fin 2) ℚ (FS2 ℚ) = 1 :=
  GroundTheory.Automorphic.FourierWhittaker.vecMeasure_vecDomain

private theorem cont_nE {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) :
    Continuous (nE D : (Fin 2 → A ℚ) → GL (Fin 2) (A E)) :=
  UpperTheory.ConvolutionTheory.R2.Pp.cont_n.comp (D.continuous_mkE' (continuous_apply 0) (continuous_apply 1))

private theorem int_Wo {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) {f : GL (Fin 2) (A E) → ℂ}
    (hf : Continuous f) (h : GL (Fin 2) (A E)) :
    IntegrableOn (fun u : Fin 2 → A ℚ => f (nE D u * h) * ψ (u 1)) (FS2 ℚ) (adeleMeasurePi ℚ) := by
  have hg : Continuous fun u : Fin 2 → A ℚ => f (nE D u * h) * ψ (u 1) :=
    (hf.comp ((cont_nE D).mul continuous_const)).mul
      (UpperTheory.ConvolutionTheory.R2.Pp.cont_ψ.comp (continuous_apply 1))
  obtain ⟨C, hC, hs⟩ := UpperTheory.ConvolutionTheory.R2.Pp.exists_cpt (F := ℚ)
  have hK : IsCompact (Set.univ.pi fun _ : Fin 2 => C) := isCompact_univ_pi fun _ => hC
  have hsub : FS2 ℚ ⊆ Set.univ.pi fun _ : Fin 2 => C := Set.pi_mono fun _ _ => hs
  unfold adeleMeasurePi
  exact (hg.continuousOn.integrableOn_compact hK).mono_set hsub

theorem UpperTheory.whittakerPeriod_add_smul_and_norm_le :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E),
        (∀ f f' : GL (Fin 2) (A E) → ℂ, Continuous f → Continuous f' → ∀ h, Wo D (f + f') h = Wo D f h + Wo D f' h) ∧
        (∀ (c : ℂ) (f : GL (Fin 2) (A E) → ℂ) h, Wo D (c • f) h = c * Wo D f h) ∧
        ∀ (f : GL (Fin 2) (A E) → ℂ) (B : ℝ) h, (∀ g, ‖f g‖ ≤ B) → ‖Wo D f h‖ ≤ B := by
  intro E _ _ D
  refine ⟨fun f f' hf hf' h => ?_, fun c f h => ?_, fun f B h hB => ?_⟩
  · unfold Wo
    rw [← integral_add (int_Wo D hf h) (int_Wo D hf' h)]
    simp only [Pi.add_apply, add_mul]
  · unfold Wo
    rw [← integral_const_mul]
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  · have := norm_setIntegral_le_of_norm_le_const (μ := adeleMeasurePi (ι := Fin 2) ℚ) (s := FS2 ℚ)
      (f := fun u => f (nE D u * h) * ψ (u 1)) (C := B) (by rw [volume_fundamental_domain_two]; exact ENNReal.one_lt_top)
      fun u _ => by rw [norm_mul, UpperTheory.ConvolutionTheory.R2.Pp.norm_ψ, mul_one]; exact hB _
    rwa [measureReal_def, volume_fundamental_domain_two, ENNReal.toReal_one, mul_one] at this
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.ArchimedeanConjugateCurveOneParameterSubgroup
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem nC_zero' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] : nC (0 : Cinf E) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nC]

private theorem nC_add' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a b : Cinf E) :
    nC (a + b) = nC a * nC b := by
  apply Units.ext
  ext i j : 2
  fin_cases i <;> fin_cases j <;> simp [nC, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem nC_val' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (t : ℝ) (z : Cinf E) :
    (nC (t • z)).val = 1 + t • (!![0, z; 0, 0] : Matrix (Fin 2) (Fin 2) (Cinf E)) := by
  ext i j : 2
  fin_cases i <;> fin_cases j <;> simp [nC]

private theorem cv_val' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E)
    (k : GL (Fin 2) (A E)) (t : ℝ) : (cv D k t).val = 1 + t • XB D k := by
  have h : ((kInf k)⁻¹).val * (kInf k).val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [cv, XB, Units.val_mul, nC_val', mul_add, add_mul, mul_one, h, Matrix.mul_smul, Matrix.smul_mul]

theorem UpperTheory.archimedeanConjugateCurve_oneParameterSubgroup :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (k : GL (Fin 2) (A E)),
        cv D k 0 = 1 ∧ (∀ s t, cv D k (s + t) = cv D k s * cv D k t) ∧ HasDerivAt (fun t => toL (cv D k t).val) (toL (XB D k)) 0 ∧
        Continuous fun k : GL (Fin 2) (A E) => toL (XB D k) := by
  intro E _ _ _ D k
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [cv, nC_zero']
  · intro s t
    simp only [cv, add_smul, nC_add']
    group
  · have h : (fun t : ℝ => toL (cv D k t).val) =
        fun t : ℝ => toL (1 : Matrix (Fin 2) (Fin 2) (Cinf E)) + t • toL (XB D k) := by
      funext t
      rw [cv_val']
      rfl
    rw [h]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (toL (XB D k))).const_add
      (toL (1 : Matrix (Fin 2) (Fin 2) (Cinf E)))
  · have hK : Continuous fun k : GL (Fin 2) (A E) => kInf k := ContAut.continuous_map_pInf E 2
    have h1 : Continuous fun k : GL (Fin 2) (A E) => (kInf k).val := Units.continuous_val.comp hK
    have h2 : Continuous fun k : GL (Fin 2) (A E) => ((kInf k)⁻¹).val :=
      Units.continuous_val.comp hK.inv
    exact (h2.matrix_mul continuous_const).matrix_mul h1
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.EigAtCmDatumOperatorOfEigAt
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (Eig EigAt)
open scoped ComplexOrder

theorem UpperTheory.eigAt_cmDatumOperator_of_eigAt :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (φ : GL (Fin 2) (A E) → ℂ) (w : H.P E) (B : Multiset ℂˣ), Continuous φ → EigAt w B φ → EigAt w B (Wo D φ) := by
  intro E _ _ D φ w B hφ hB g
  have hnE : Continuous (nE D) := by
    have hmkE : Continuous fun x : Fin 2 → A ℚ => D.mkE (x 0) (x 1) :=
      (AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 0)).add
        ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 1)).mul continuous_const)
    exact (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp
      UpperTheory.ConvolutionTheory.R2.M.continuous_nU).comp hmkE
  have hψ : Continuous (ψ (F := ℚ)) := continuous_subtype_val.comp continuous_adelicChar
  have hi : ∀ h : GL (Fin 2) (A E),
      IntegrableOn (fun x : Fin 2 → A ℚ => φ (nE D x * h) * ψ (x 1)) (FS2 ℚ) (adeleMeasurePi ℚ) := by
    intro h
    obtain ⟨C, hC, hEC⟩ : ∃ C, IsCompact C ∧ fundamentalSet ℚ ⊆ C :=
      ⟨closure (fundamentalSetInfinite ℚ) ×ˢ _,
        (isCompact_closure_fundamentalSetInfinite ℚ).prod (isCompact_integralFiniteAdeles ℚ),
        fun x hx => ⟨subset_closure hx.1, hx.2⟩⟩
    have hK : IsCompact (Set.univ.pi fun _ : Fin 2 => C) := isCompact_univ_pi fun _ => hC
    have hc : Continuous fun x : Fin 2 → A ℚ => φ (nE D x * h) * ψ (x 1) :=
      (hφ.comp (hnE.mul continuous_const)).mul (hψ.comp (continuous_apply 1))
    exact (hc.continuousOn.integrableOn_compact hK).mono_set fun x hx i hi => hEC (hx i hi)
  let G (x : Fin 2 → A ℚ) (y : GL (Fin 2) (w.adicCompletion E)) :=
    φ (nE D x * (g * finGL E 2 (locGL E 2 w y)))
  have hG (x : Fin 2 → A ℚ) : Eig w B (G x) := by
    simpa only [G, mul_assoc] using hB (nE D x * g)
  have hGi (z : GL (Fin 2) (w.adicCompletion E)) :
      Integrable (fun x => G x z * ψ (x 1)) ((adeleMeasurePi ℚ).restrict (FS2 ℚ)) := hi _
  change Eig w B (fun y => ∫ x in FS2 ℚ, G x y * ψ (x 1) ∂(adeleMeasurePi ℚ))
  refine ⟨(hB 1).card, fun y k hk => by simp only [fun x => (hG x).inv y k hk],
    fun ϖ hϖ j hj y => ?_⟩
  have hf := Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm E w 2)
    (GlobalTheory.LFun.Tj_mem_hecke (n := 2) hϖ j).2
  have hs (f : GL (Fin 2) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := 2) → ℂ) :
      ∑ᶠ c, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out * f c =
        ∑ c ∈ hf.toFinset, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out * f c := by
    refine finsum_eq_sum_of_support_subset _ fun c hc => ?_
    rw [Set.Finite.coe_toFinset]
    exact left_ne_zero_of_mul hc
  rw [hs]
  simp only [← integral_const_mul]
  rw [← integral_finsetSum _ fun c _ => (hGi _).const_mul _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have e := (hG x).eig ϖ hϖ j hj y
  rw [hs] at e
  simp only [← mul_assoc, ← e, Finset.sum_mul]
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.HasDerivAtWhittakerPeriodOneParameter
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem cover : ∃ C : Set (Fin 2 → A ℚ), IsCompact C ∧ FS2 ℚ ⊆ C := by
  obtain ⟨C, hC, hEC⟩ : ∃ C, IsCompact C ∧ fundamentalSet ℚ ⊆ C :=
    ⟨closure (fundamentalSetInfinite ℚ) ×ˢ _,
      (isCompact_closure_fundamentalSetInfinite ℚ).prod (isCompact_integralFiniteAdeles ℚ),
      fun x hx => ⟨subset_closure hx.1, hx.2⟩⟩
  exact ⟨Set.univ.pi fun _ : Fin 2 => C, isCompact_univ_pi fun _ => hC, fun x hx i hi => hEC (hx i hi)⟩

private theorem cont_nE' {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) :
    Continuous fun u : Fin 2 → A ℚ => nE D u :=
  continuous_gl.comp (continuous_nU.comp ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 0)).add
    ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 1)).mul continuous_const)))

private theorem deriv_at {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (f : Sm E 2)
    (c : ℝ → GL (Fin 2) (Cinf E)) (X : Lie E 2) (x : GL (Fin 2) (A E)) (c0 : c 0 = 1)
    (cadd : ∀ s t, c (s + t) = c s * c t) (cd : HasDerivAt (fun t => toL (c t).val) X 0) (t : ℝ) :
    HasDerivAt (fun τ => f.1 (x * infGL E 2 (c τ))) ((lie E 2 X f).1 (x * infGL E 2 (c t))) t := by
  have h := hasDerivAt_curve f (x * infGL E 2 (c t)) c X c0 cd
  have h2 : HasDerivAt (fun s => f.1 (x * infGL E 2 (c t) * infGL E 2 (c s))) ((lie E 2 X f).1 (x * infGL E 2 (c t))) (t - t) := by
    rw [sub_self]; exact h
  have h3 := HasDerivAt.comp_sub_const t t h2
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun τ => ?_)
  have e : c τ = c t * c (τ - t) := by rw [← cadd]; congr 1; ring
  simp only [e, map_mul, mul_assoc]

theorem UpperTheory.hasDerivAt_whittakerPeriod_oneParameter :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (f : Sm E 2) (c : ℝ → GL (Fin 2) (Cinf E)) (X : Lie E 2)
        (g : GL (Fin 2) (A E)), c 0 = 1 → (∀ s t, c (s + t) = c s * c t) → HasDerivAt (fun t => toL (c t).val) X 0 →
        Continuous f.1 → Continuous (lie E 2 X f).1 → (∃ B : ℝ, ∀ g, ‖(lie E 2 X f).1 g‖ ≤ B) →
        HasDerivAt (fun t : ℝ => Wo D f.1 (g * infGL E 2 (c t))) (Wo D (lie E 2 X f).1 g) 0 := by
  intro E _ _ _ D f c X g c0 cadd cd hf hl ⟨B, hB⟩
  obtain ⟨C, hC, hsub⟩ := cover
  have hfin : adeleMeasurePi ℚ (FS2 ℚ) < ⊤ := (measure_mono hsub).trans_lt hC.measure_lt_top
  haveI : IsFiniteMeasure ((adeleMeasurePi ℚ).restrict (FS2 ℚ)) := ⟨by simpa using hfin⟩
  have hn := cont_nE' D
  have hψ : Continuous fun u : Fin 2 → A ℚ => ψ (u 1) := continuous_ψ.comp (continuous_apply 1)
  have hF : ∀ h : GL (Fin 2) (A E), Continuous fun u : Fin 2 → A ℚ => f.1 (nE D u * h) * ψ (u 1) :=
    fun h => (hf.comp (hn.mul continuous_const)).mul hψ
  have hF' : ∀ h : GL (Fin 2) (A E), Continuous fun u : Fin 2 → A ℚ => (lie E 2 X f).1 (nE D u * h) * ψ (u 1) :=
    fun h => (hl.comp (hn.mul continuous_const)).mul hψ
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (adeleMeasurePi ℚ).restrict (FS2 ℚ)) (x₀ := (0 : ℝ)) (s := Set.univ)
    (F := fun t u => f.1 (nE D u * (g * infGL E 2 (c t))) * ψ (u 1))
    (F' := fun t u => (lie E 2 X f).1 (nE D u * (g * infGL E 2 (c t))) * ψ (u 1))
    (bound := fun _ => B) Filter.univ_mem
    (Eventually.of_forall fun t => (hF _).aestronglyMeasurable)
    (((hF _).continuousOn.integrableOn_compact hC).mono_set hsub)
    (hF' _).aestronglyMeasurable
    (ae_of_all _ fun u t _ => by rw [norm_mul, norm_ψ, mul_one]; exact hB _)
    (integrable_const _)
    (ae_of_all _ fun u t _ => by
      have h := deriv_at f c X (nE D u * g) c0 cadd cd t
      simp only [mul_assoc] at h
      exact h.mul_const (ψ (u 1)))
  have h2 := key.2
  simp only [c0, map_one, mul_one] at h2
  exact h2
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.LintegralIdeleRatPolyDecayMulNormRpowLtTop
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem mult_eq_one (w : InfinitePlace ℚ) : w.mult = 1 := by
  simp [InfinitePlace.mult, IsTotallyReal.isReal w]

private theorem lint_real (w : InfinitePlace ℚ) {s : ℝ} (hs : 1 < s) :
    ∫⁻ z, ENNReal.ofReal ((1 + ‖z‖) ^ (-s)) ∂infinitePlaceMeasure w < ∞ := by
  have hw : w.IsReal := IsTotallyReal.isReal w
  have hm : Measurable fun z : w.Completion ↦ ENNReal.ofReal ((1 + ‖z‖) ^ (-s)) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_const.add continuous_norm).rpow_const fun z ↦
        Or.inl (add_pos_of_pos_of_nonneg one_pos (norm_nonneg z)).ne').measurable
  rw [infinitePlaceMeasure_of_isReal hw,
    lintegral_map hm (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous.measurable]
  have h : ∀ y : ℝ, ‖(InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm y‖ = ‖y‖ := fun y ↦ by
    rw [← norm_isometryEquivRealOfIsReal hw, IsometryEquiv.apply_symm_apply]
  simp_rw [h]
  exact finite_integral_one_add_norm (by simpa using hs)

private theorem int_place (w : InfinitePlace ℚ) {x : ℝ} (h1 : 1 < x) {r : ℕ} (hr : x < r) :
    Integrable (fun z : (w.Completion)ˣ ↦ ‖(z : w.Completion)‖ ^ x / (1 + ‖(z : w.Completion)‖) ^ r)
      (infinitePlaceUnitsMeasure w) := by
  have hG : Continuous fun z : w.Completion ↦ ‖z‖ ^ x / (1 + ‖z‖) ^ r :=
    (continuous_norm.rpow_const fun _ ↦ Or.inr (by linarith)).div
      ((continuous_const.add continuous_norm).pow r) fun _ ↦ by positivity
  refine ⟨(hG.comp Units.continuous_val).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z ↦ by positivity)]
  refine (lintegral_unitsMeasure_le (infinitePlaceMeasure w) w.mult
    (g := fun z ↦ ENNReal.ofReal (‖z‖ ^ x / (1 + ‖z‖) ^ r))
    (ENNReal.measurable_ofReal.comp hG.measurable)).trans_lt ?_
  refine lt_of_le_of_lt (lintegral_mono fun z ↦ ?_) (lint_real w (s := r - x + 1) (by linarith))
  rw [← ENNReal.ofReal_mul (by positivity), mult_eq_one, pow_one]
  refine ENNReal.ofReal_le_ofReal ?_
  set t := ‖z‖
  have ht : 0 ≤ t := norm_nonneg _
  have ha : 1 ≤ 1 + t := by linarith
  have hapos : 0 < 1 + t := by linarith
  rcases ht.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (by linarith), zero_div, mul_zero]
    positivity
  · have e1 : t⁻¹ * (t ^ x / (1 + t) ^ r) = t ^ (x - 1) * ((1 + t) ^ (r : ℝ))⁻¹ := by
      rw [← Real.rpow_natCast (1 + t) r, Real.rpow_sub hpos, Real.rpow_one, div_eq_mul_inv,
        div_eq_mul_inv]
      ring
    have e2 : (1 + t) ^ (-((r : ℝ) - x + 1)) = (1 + t) ^ (x - 1) * ((1 + t) ^ (r : ℝ))⁻¹ := by
      rw [← Real.rpow_neg hapos.le, ← Real.rpow_add hapos]
      congr 1
      ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow ht (by linarith) (by linarith)) (by positivity)

private noncomputable def hInf (x : ℝ) (r : ℕ) (a : (InfiniteAdeleRing ℚ)ˣ) : ℝ :=
  ∏ w : InfinitePlace ℚ, ‖(a : InfiniteAdeleRing ℚ) w‖ ^ x / (1 + ‖(a : InfiniteAdeleRing ℚ) w‖) ^ r

private theorem int_hInf {x : ℝ} (h1 : 1 < x) {r : ℕ} (hr : x < r) :
    Integrable (hInf x r) (infiniteIdeleMeasure ℚ) := by
  have h := Integrable.fintype_prod_dep (𝕜 := ℝ)
    (f := fun (w : InfinitePlace ℚ) (z : (w.Completion)ˣ) ↦
      ‖(z : w.Completion)‖ ^ x / (1 + ‖(z : w.Completion)‖) ^ r)
    (μ := fun w ↦ infinitePlaceUnitsMeasure w) fun w ↦ int_place w h1 hr
  rw [infiniteIdeleMeasure]
  refine (integrable_map_equiv (infiniteUnitsEquiv ℚ).symm.toHomeomorph.toMeasurableEquiv _).2 ?_
  exact h

private theorem abs_re (y : IdeleGroup ℚ) :
    |re (y : A ℚ)| = ‖((IdeleGroup.toInfinite ℚ y : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) Rat.infinitePlace‖ := by
  have hw : (Rat.infinitePlace).IsReal := IsTotallyReal.isReal _
  have e : re (y : A ℚ) = InfinitePlace.Completion.isometryEquivRealOfIsReal hw
      (((IdeleGroup.toInfinite ℚ y : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) Rat.infinitePlace) := rfl
  rw [e, ← Real.norm_eq_abs, norm_isometryEquivRealOfIsReal]

theorem UpperTheory.lintegral_idele_rat_polyDecay_mul_norm_rpow_lt_top :
    ∀ (K : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)), IsCompact K → ∀ x : ℝ, 1 < x → ∀ r : ℕ, x < r →
        ∫⁻ y : IdeleGroup ℚ, (if (y : A ℚ).2 ∈ K then ENNReal.ofReal (((1 + |re (y : A ℚ)|) ^ r)⁻¹ * ab y ^ x) else 0) ∂(ideleMeasure ℚ) < ⊤ := by
  intro K hK x hx r hr
  obtain ⟨L, hL⟩ := exists_subset_idealFiniteAdeles hK
  have hG : Integrable (fun y : IdeleGroup ℚ ↦
      hInf x r (IdeleGroup.toInfinite ℚ y) * finiteZetaBound L x (IdeleGroup.toFinite ℚ y))
      (ideleMeasure ℚ) := by
    have h := (int_hInf hx hr).mul_prod (integrable_finiteZetaBound L hx)
    exact ((measurePreserving_prodEquiv ℚ).integrable_comp_emb
      (IdeleGroup.prodEquiv ℚ).toHomeomorph.measurableEmbedding).2 h
  refine lt_of_le_of_lt (lintegral_mono fun y ↦ ?_) hG.lintegral_lt_top
  split_ifs with hy
  · refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have hb : ((IdeleGroup.toFinite ℚ y : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ idealFiniteAdeles L :=
      hL hy
    rw [finiteZetaBound, if_pos hb, hInf, ab, ideleModule_rpow_eq, abs_re,
      Fintype.prod_subsingleton _ Rat.infinitePlace, Fintype.prod_subsingleton _ Rat.infinitePlace,
      mult_eq_one]
    simp only [Nat.cast_one, one_mul]
    rw [div_eq_mul_inv]
    ring_nf
  · exact zero_le
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.RightInvariantBaseChangeUnipotentOfPlacesAboveFi
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private lemma nL_memK {K : Type} [Field K] [NumberField K] {v : H.P K} {c : H.Kv v} (hc : Valued.v c ≤ 1) :
    H.nL c ∈ GlobalTheory.LFun.KGL v (n := 2) := by
  have hc' : c ∈ v.adicCompletionIntegers K := hc
  have hn : -c ∈ v.adicCompletionIntegers K := neg_mem hc'
  rw [GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff]
  have h1 : (1 : H.Kv v) ∈ v.adicCompletionIntegers K := one_mem _
  have h0 : (0 : H.Kv v) ∈ v.adicCompletionIntegers K := zero_mem _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j
    · exact h1
    · exact hc'
    · exact h0
    · exact h1
  · fin_cases i <;> fin_cases j
    · exact h1
    · exact hn
    · exact h0
    · exact h1

private lemma fix_sum {K : Type} [Field K] [NumberField K] (φ : GL (Fin 2) (A K) → ℂ) (S : Finset (H.P K)) :
    (∀ w ∈ S, H.Fix w φ) → ∀ z : A K, z.1 = 0 → (∀ w, w ∉ S → H.cp w z = 0) → (∀ w, Valued.v (H.cp w z) ≤ 1) →
      ∀ g, φ (g * gl (nU z)) = φ g := by
  induction S using Finset.induction_on with
  | empty =>
    intro _ z h1 h2 _ g
    have hz : z = 0 := Prod.ext h1 (FiniteAdeleRing.ext K fun w => h2 w (Finset.notMem_empty w))
    have h : nU (0 : A K) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [nU]
    rw [hz, h, gl, map_one, mul_one]
  | insert w S hw ih =>
    intro hF z h1 h2 h3 g
    obtain ⟨-, -, hc, -, -, -, -, hs, -, -⟩ := H.sgLaws K w
    have hne : ∀ u, u ≠ w → H.cp u (H.sg w (H.cp w z)) = 0 := fun u hu => (hs _).2 u hu
    have e : z = (z - H.sg w (H.cp w z)) + H.sg w (H.cp w z) := (sub_add_cancel _ _).symm
    rw [e, nU_add, gl, map_mul, ← mul_assoc]
    have e2 : Matrix.SpecialLinearGroup.toGL (nU (H.sg w (H.cp w z))) = H.lc w (H.nL (H.cp w z)) :=
      ((H.lcLaws K w).1 _).symm
    rw [e2, hF w (Finset.mem_insert_self _ _) _ _ (nL_memK (h3 w))]
    refine ih (fun u hu => hF u (Finset.mem_insert_of_mem hu)) _ ?_ (fun u hu => ?_) (fun u => ?_) g
    · show z.1 - (H.sg w (H.cp w z)).1 = 0
      rw [h1, (hs _).1, sub_zero]
    · rw [map_sub]
      by_cases h : u = w
      · subst h
        rw [hc, sub_self]
      · rw [hne u h, sub_zero]
        exact h2 u (by simp [h, hu])
    · rw [map_sub]
      by_cases h : u = w
      · subst h
        rw [hc, sub_self, map_zero]
        exact zero_le'
      · rw [hne u h, sub_zero]
        exact h3 u

private lemma fin_over {E : Type} [Field E] [NumberField E] (v : H.P ℚ) :
    {w : H.P E | AdeleBaseChange.below ℚ w = v}.Finite := by
  have := v.isMaximal
  refine Set.Finite.of_finite_image (f := fun w : H.P E => w.asIdeal) ?_ fun a _ b _ h => HeightOneSpectrum.ext h
  refine (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).subset ?_
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w.isPrime, (AdeleBaseChange.below_eq_iff _ _).1 hw⟩

theorem UpperTheory.right_invariant_baseChangeUnipotent_of_places_above_fixed :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (φ : GL (Fin 2) (A E) → ℂ) (v : H.P ℚ), H.Gd D.δ v → (∀ w : H.P E, w.under (𝓞 ℚ) = v → H.Fix w φ) → ∀ c : H.Kv v, H.IsInt c → ∀ g, φ (g * Xg.nu D (H.sg v c)) = φ g := by
  intro E _ _ D φ v hG hF c hc g
  obtain ⟨-, -, hcp, -, -, -, -, hs, -, -⟩ := H.sgLaws ℚ v
  have hz : D.mkE 0 (H.sg v c) = AdeleBaseChange.adeleMap ℚ E (H.sg v c) * rt D.θ := by
    rw [Dat.mkE, map_zero, zero_add]
  have hoff : ∀ w : H.P E, AdeleBaseChange.below ℚ w ≠ v → H.cp w (D.mkE 0 (H.sg v c)) = 0 := fun w hw => by
    have h : H.cp w (AdeleBaseChange.adeleMap ℚ E (H.sg v c)) = 0 := by
      change SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w ((H.sg v c).2 (AdeleBaseChange.below ℚ w)) = 0
      rw [(hs c).2 _ hw, map_zero]
    rw [hz, map_mul, h, zero_mul]
  change φ (g * gl (nU (D.mkE 0 (H.sg v c)))) = φ g
  refine fix_sum φ (fin_over (E := E) v).toFinset (fun w hw => hF w ((fin_over v).mem_toFinset.1 hw)) _ ?_
    (fun w hw => hoff w fun h => hw ((fin_over v).mem_toFinset.2 h)) (fun w => ?_) g
  · rw [hz]
    change InfinitePlace.infiniteAdeleRingMap (H.sg v c).1 * _ = 0
    rw [(hs c).1, map_zero, zero_mul]
  · by_cases hw : AdeleBaseChange.below ℚ w = v
    · subst hw
      have hk : ∀ x : H.Kv (AdeleBaseChange.below ℚ w), Valued.v x ≤ 1 →
          Valued.v (SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w x) ≤ 1 := fun x hx => by
        rw [SemiLocal.valued_completionMap]
        exact pow_le_one' hx _
      have h1 : H.cp w (AdeleBaseChange.adeleMap ℚ E (H.sg _ c)) = SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w c :=
        congrArg (SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w) (hcp c)
      have h2 : H.cp w (rt D.θ) ^ 2 =
          SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w (D.δ : H.Kv (AdeleBaseChange.below ℚ w)) := by
        rw [← map_pow, ← map_pow, D.sq]
        have a := eq_ratCast (((H.cp w).comp (algebraMap E (A E))).comp (algebraMap ℚ E)) D.δ
        rw [map_ratCast]
        exact a
      have h3 : Valued.v (H.cp w (rt D.θ)) ≤ 1 := by
        have hd := hG.del
        rw [eq_ratCast] at hd
        have h := hk _ hd.le
        rw [← h2, map_pow] at h
        exact (pow_le_one_iff two_ne_zero).1 h
      rw [hz, map_mul, h1, map_mul]
      exact mul_le_one' (hk c hc) h3
    · rw [hoff w hw, map_zero]
      exact zero_le'
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.EigenformShintaniFormulaAtPlace
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private lemma dL_mul {K : Type} [Field K] [NumberField K] {v : H.P K} (a d a' d' : (H.Kv v)ˣ) :
    H.dL a d * H.dL a' d' = H.dL (a * a') (d * d') := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H.dL, Matrix.mul_apply, Fin.sum_univ_two]

private lemma dL_one {K : Type} [Field K] [NumberField K] {v : H.P K} : (H.dL (1 : (H.Kv v)ˣ) 1) = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H.dL]

private lemma dL_nL {K : Type} [Field K] [NumberField K] {v : H.P K} (a : (H.Kv v)ˣ) (b : H.Kv v) :
    H.dL a 1 * H.nL b = H.nL ((a : H.Kv v) * b) * H.dL a 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H.dL, H.nL, Matrix.mul_apply, Fin.sum_univ_two]

private lemma hs_succ (a b : ℂ) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1 + 1), a ^ i * b ^ (k + 1 - i) =
      b * ∑ i ∈ Finset.range (k + 1), a ^ i * b ^ (k - i) + a ^ (k + 1) := by
  rw [Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self, pow_zero, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have : k + 1 - i = (k - i) + 1 := by
    have := Finset.mem_range.1 hi
    omega
  rw [this]
  ring

private lemma tor_loc (K : Type) [Field K] [NumberField K] (v : H.P K) (ϖ : (H.Kv v)ˣ) (hϖ : H.IsU ϖ)
    (χ : H.Kv v → ℂ) (hχ : H.Good χ) (α β : ℂˣ) (W : GL (Fin 2) (H.Kv v) → ℂ)
    (hW : UpperTheory.V.Af.Smo.Eig v {α, β} W) (hn : ∀ b y, W (H.nL b * y) = χ b * W y) (k : ℕ) :
    (H.q v ^ (1 / 2 : ℂ)) ^ k * W (H.dL (ϖ ^ k) 1) =
      (∑ i ∈ Finset.range (k + 1), ((α : ℂ)) ^ i * ((β : ℂ)) ^ (k - i)) * W 1 := by
  obtain ⟨R, hcard, hRint, hR⟩ := UpperTheory.ConvolutionTheory.R2.H.heckeExpl K v ϖ hϖ
  have hsum := fun g => (hR α β W hW g).1
  have hcen := fun g => (hR α β W hW g).2
  obtain ⟨t1, -⟩ := UpperTheory.ConvolutionTheory.R2.H.whTorus K v ϖ hϖ χ hχ α β W hW hn
  have hint : ∀ c : H.Kv v, H.IsInt c → ∀ y, W (H.nL c * y) = W y := fun c hc y => by
    rw [hn, hχ.2.1 c hc, one_mul]
  have hϖint : H.IsInt (ϖ : H.Kv v) := by
    have h' : Valued.v (ϖ : H.Kv v) = _ := hϖ
    show Valued.v (ϖ : H.Kv v) ≤ 1
    rw [h']
    exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) ≤ 1)
  have hq0 : H.q v ≠ 0 := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    exact Nat.cast_ne_zero.2 this
  set s : ℂ := H.q v ^ (1 / 2 : ℂ) with hs
  have hss : s * s = H.q v := by
    rw [hs, ← Complex.cpow_add _ _ hq0]
    norm_num
  have hs0 : s ≠ 0 := fun h => hq0 (by rw [← hss, h, zero_mul])
  have hconst : ∀ x : ℂ, ∑ _b ∈ R, x = H.q v * x := fun x => by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    rfl
  have hrec : ∀ k : ℕ, s * ((α : ℂ) + β) * W (H.dL (ϖ ^ (k + 1)) 1) =
      H.q v * W (H.dL (ϖ ^ (k + 1 + 1)) 1) + (α : ℂ) * β * W (H.dL (ϖ ^ k) 1) := fun k => by
    have h2 := hsum (H.dL (ϖ ^ (k + 1)) 1)
    have t3 : ∀ b ∈ R, W (H.dL (ϖ ^ (k + 1)) 1 * H.nL b * H.dL ϖ 1) = W (H.dL (ϖ ^ (k + 1 + 1)) 1) := fun b hb => by
      rw [dL_nL, mul_assoc, hint _ ?_, dL_mul, mul_one, ← pow_succ]
      have hb' : ((ϖ : H.Kv v) ^ (k + 1)) * b ∈ v.adicCompletionIntegers K :=
        mul_mem (pow_mem (show (ϖ : H.Kv v) ∈ v.adicCompletionIntegers K from hϖint) _)
          (show b ∈ v.adicCompletionIntegers K from hRint b hb)
      rw [Units.val_pow_eq_pow_val]
      exact hb'
    rw [Finset.sum_congr rfl t3, hconst] at h2
    have t4 : W (H.dL (ϖ ^ (k + 1)) 1 * H.dL 1 ϖ) = (α : ℂ) * β * W (H.dL (ϖ ^ k) 1) := by
      have := hcen (H.dL (ϖ ^ k) 1)
      rw [dL_mul, one_mul, ← pow_succ] at this
      rw [dL_mul, mul_one, one_mul]
      exact this
    rw [t4] at h2
    exact h2
  have h3 : s * W (H.dL ϖ 1) = ((α : ℂ) + β) * W 1 := by
    refine mul_left_cancel₀ hs0 ?_
    rw [← mul_assoc, hss, ← mul_assoc]
    exact t1
  have key : ∀ k : ℕ, s ^ (k + 1) * W (H.dL (ϖ ^ (k + 1)) 1) =
      β * (s ^ k * W (H.dL (ϖ ^ k) 1)) + (α : ℂ) ^ (k + 1) * W 1 := by
    intro k
    induction k with
    | zero =>
      simp only [zero_add, pow_one, pow_zero, one_mul, dL_one]
      rw [h3]
      ring
    | succ k ih =>
      have h := hrec k
      rw [← hss] at h
      linear_combination (α : ℂ) * ih - s ^ k * h
  induction k with
  | zero => simp [dL_one]
  | succ k ih =>
    rw [key, ih, hs_succ]
    ring

theorem UpperTheory.eigenform_shintani_formula_at_place :
    ∀ (K : Type) [Field K] [NumberField K] (v : H.P K) (ϖ : (H.Kv v)ˣ), H.IsU ϖ → ∀ (χ : H.Kv v → ℂ), H.Good χ → ∀ (α β : ℂˣ) (f : GL (Fin 2) (A K) → ℂ),
          EigAt v {α, β} f → (∀ b h, f (H.lc v (H.nL b) * h) = χ b * f h) → ∀ g, H.KAt v g → ∀ k : ℕ,
          (H.q v ^ (1 / 2 : ℂ)) ^ k * f (aE (H.idl v ϖ ^ k) * g) = (∑ i ∈ Finset.range (k + 1), ((α : ℂ)) ^ i * ((β : ℂ)) ^ (k - i)) * f g := by
  intro K _ _ v ϖ hϖ χ hχ α β f hB hn g hg k
  have hE1 : UpperTheory.V.Af.Smo.Eig v {α, β} fun x => f (H.lc v x * g) := by
    have := (H.fixTr K v f g hg).2 _ hB 1
    simpa [H.lc] using this
  have hnl : ∀ b x, f (H.lc v (H.nL b * x) * g) = χ b * f (H.lc v x * g) := fun b x => by
    rw [map_mul, mul_assoc, hn]
  have h := tor_loc K v ϖ hϖ χ hχ α β _ hE1 hnl k
  have e : H.idl v (ϖ ^ k) = H.idl v ϖ ^ k := map_pow _ _ _
  beta_reduce at h
  rw [(H.lcLaws K v).2.2.2.1, e, map_one, one_mul] at h
  exact h
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.MeasurePreservingIdeleScaleAndConjOnMaximalCompa
section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.MaximalCompactMeasureMapConjDiagEq
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private lemma inv_mem_UU' {t : (A ℚ)ˣ} (ht : t ∈ UU) : t⁻¹ ∈ UU := by
  refine ⟨?_, fun v => ?_⟩
  · have h : (t : A ℚ).1 * ((t⁻¹ : (A ℚ)ˣ) : A ℚ).1 = 1 := congrArg Prod.fst (Units.mul_inv t)
    rw [ht.1, one_mul] at h
    exact h
  · have hm : H.cp v (t : A ℚ) * H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have := congrArg Valued.v hm
    rwa [map_mul, ht.2 v, one_mul, map_one] at this

private lemma cD_mem_KK {t : (A ℚ)ˣ} (ht : t ∈ UU) {k : G1 ℚ} (hk : k ∈ KK ℚ) : cD t k ∈ KK ℚ := by
  have hi := inv_mem_UU' ht
  have fm : ∀ a b : A ℚ, (a * b).1 = a.1 * b.1 := fun _ _ => rfl
  have fa : ∀ a b : A ℚ, (a + b).1 = a.1 + b.1 := fun _ _ => rfl
  have c00 : (cD t k) 0 0 = k 0 0 := rfl
  have c01 : (cD t k) 0 1 = k 0 1 * ((t⁻¹ : (A ℚ)ˣ) : A ℚ) := rfl
  have c10 : (cD t k) 1 0 = (t : A ℚ) * k 1 0 := rfl
  have c11 : (cD t k) 1 1 = k 1 1 := rfl
  have e1 : ∀ i j, ((cD t k) i j).1 = (k i j).1 := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact congrArg Prod.fst c00
    · show ((cD t k) 0 1).1 = (k 0 1).1
      rw [c01, fm, hi.1, mul_one]
    · show ((cD t k) 1 0).1 = (k 1 0).1
      rw [c10, fm, ht.1, one_mul]
    · exact congrArg Prod.fst c11
  refine ⟨fun i j => ?_, fun v i j => ?_⟩
  · have h := hk.1 i j
    rw [← h]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
    have e3 : ∀ a b c d a' b' c' d' : A ℚ, a.1 = a'.1 → b.1 = b'.1 → c.1 = c'.1 → d.1 = d'.1 →
        (a * b + c * d).1 = (a' * b' + c' * d').1 := by
      intro a b c d a' b' c' d' h1 h2 h3 h4
      rw [fa, fa, fm, fm, fm, fm, h1, h2, h3, h4]
    exact e3 _ _ _ _ _ _ _ _ (e1 _ _) (e1 _ _) (e1 _ _) (e1 _ _)
  · have ti : ((t : A ℚ)).2 v ∈ v.adicCompletionIntegers ℚ := (ht.2 v).le
    have tj : (((t⁻¹ : (A ℚ)ˣ) : A ℚ)).2 v ∈ v.adicCompletionIntegers ℚ := (hi.2 v).le
    fin_cases i <;> fin_cases j
    · exact hk.2 v 0 0
    · show ((cD t k) 0 1).2 v ∈ v.adicCompletionIntegers ℚ
      rw [c01]
      exact mul_mem (hk.2 v 0 1) tj
    · show ((cD t k) 1 0).2 v ∈ v.adicCompletionIntegers ℚ
      rw [c10]
      exact mul_mem ti (hk.2 v 1 0)
    · exact hk.2 v 1 1

theorem UpperTheory.maximalCompact_measure_map_conjDiag_eq :
    ∀ (M₀ : Meas ℚ) (t : IdeleGroup ℚ), t ∈ UU → M₀.κ.map (cD t) = M₀.κ := by
  intro m t ht
  haveI := m.prob
  have hm : Measurable (cD t : G1 ℚ → G1 ℚ) := (M.continuous_cD t).measurable
  have hae : ∀ᵐ y ∂m.κ, y ∈ KK ℚ := by
    rw [ae_iff]
    exact m.supp
  have right : ∀ f : G1 ℚ → ℝ≥0∞, Measurable f → ∀ k ∈ KK ℚ, ∫⁻ x, f (x * k) ∂m.κ = ∫⁻ x, f x ∂m.κ := by
    intro f hf k hk
    conv_rhs => rw [← m.κ_right k hk]
    rw [lintegral_map hf (measurable_mul_const k)]
  have left : ∀ f : G1 ℚ → ℝ≥0∞, Measurable f → ∀ k ∈ KK ℚ, ∫⁻ x, f (k * x) ∂m.κ = ∫⁻ x, f x ∂m.κ := by
    intro f hf k hk
    conv_rhs => rw [← m.κ_left k hk]
    rw [lintegral_map hf (measurable_const_mul k)]
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf hm]
  have hF : Measurable (fun p : G1 ℚ × G1 ℚ => f (p.1 * cD t p.2)) :=
    hf.comp (measurable_fst.mul (hm.comp measurable_snd))
  have hA : ∫⁻ y, ∫⁻ x, f (x * cD t y) ∂m.κ ∂m.κ = ∫⁻ x, f x ∂m.κ := by
    have h : ∀ᵐ y ∂m.κ, ∫⁻ x, f (x * cD t y) ∂m.κ = ∫⁻ x, f x ∂m.κ :=
      hae.mono fun y hy => right f hf _ (cD_mem_KK ht hy)
    rw [lintegral_congr_ae h, lintegral_const, measure_univ, mul_one]
  have hB : ∫⁻ x, ∫⁻ y, f (x * cD t y) ∂m.κ ∂m.κ = ∫⁻ y, f (cD t y) ∂m.κ := by
    have h : ∀ᵐ x ∂m.κ, ∫⁻ y, f (x * cD t y) ∂m.κ = ∫⁻ y, f (cD t y) ∂m.κ := by
      refine hae.mono fun x hx => ?_
      have hk : cD t⁻¹ x ∈ KK ℚ := cD_mem_KK (inv_mem_UU' ht) hx
      have ex : x = cD t (cD t⁻¹ x) := by rw [M.cD_cD, mul_inv_cancel, M.cD_one]
      have e : ∀ y, f (x * cD t y) = (f ∘ cD t) (cD t⁻¹ x * y) := by
        intro y
        rw [Function.comp_apply, M.cD_mul, ← ex]
      simp only [e]
      exact left (f ∘ cD t) (hf.comp hm) _ hk
    rw [lintegral_congr_ae h, lintegral_const, measure_univ, mul_one]
  rw [← hB, ← hA]
  exact lintegral_lintegral_swap hF.aemeasurable
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.measurePreserving_idele_scale_and_conj_on_maximalCompact :
    ∀ (M₀ : Meas ℚ) (t : ℝ) (u : IdeleGroup ℚ), u ∈ UU →
        MeasurePreserving (fun p : IdeleGroup ℚ × G1 ℚ => (Un.aa t u p.1, cD u p.2)) M₀.ν M₀.ν ∧
        MeasurableEmbedding (fun p : IdeleGroup ℚ × G1 ℚ => (Un.aa t u p.1, cD u p.2)) := by
  intro M₀ t u hu
  haveI := M₀.prob
  let c : IdeleGroup ℚ := (iy (Real.exp t) * u : (A ℚ)ˣ)
  have h1 : MeasurePreserving (fun z : IdeleGroup ℚ => c * z⁻¹) (ideleMeasure ℚ) (ideleMeasure ℚ) :=
    (measurePreserving_mul_left (ideleMeasure ℚ) c).comp (Measure.measurePreserving_inv (ideleMeasure ℚ))
  have h2 : MeasurePreserving (cD u : G1 ℚ → G1 ℚ) M₀.κ M₀.κ :=
    ⟨(M.continuous_cD u).measurable, UpperTheory.maximalCompact_measure_map_conjDiag_eq M₀ u hu⟩
  let e1 : IdeleGroup ℚ ≃ᵐ IdeleGroup ℚ := (MeasurableEquiv.inv (IdeleGroup ℚ)).trans (MeasurableEquiv.mulLeft c)
  let e2 : G1 ℚ ≃ᵐ G1 ℚ :=
    { toFun := cD u
      invFun := cD (u⁻¹ : (A ℚ)ˣ)
      left_inv := fun g => by rw [M.cD_cD, inv_mul_cancel, M.cD_one]
      right_inv := fun g => by rw [M.cD_cD, mul_inv_cancel, M.cD_one]
      measurable_toFun := (M.continuous_cD u).measurable
      measurable_invFun := (M.continuous_cD _).measurable }
  exact ⟨h1.prod h2, (e1.prodCongr e2).measurableEmbedding⟩
end
