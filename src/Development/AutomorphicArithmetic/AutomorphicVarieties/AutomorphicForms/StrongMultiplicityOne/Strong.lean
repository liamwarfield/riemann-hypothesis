module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.RowStep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.CentEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.LocStep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SphDict
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.EigOfSat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Vanish

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.CenSame
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.cenSame :
    UpperTheory.V.Af.Smo.CentEq → UpperTheory.V.Af.StrongMultiplicityOne.SetUp → UpperTheory.V.Af.StrongMultiplicityOne.CenSame := by
  intro hC hS E _ _ n U U' hU hs hc φ' hφ' s g'
  obtain ⟨φ, hφ, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  obtain ⟨S, B, hB, hk, hk'⟩ := hS E n U U' hs φ φ'
  have loc : ∀ w ∉ S, ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), InKS S (locGL E n w k) := by
    intro w hw k hkk
    refine ⟨fun x hx => GlobalTheory.CuspRep.pLoc_locGL_of_ne (show x ≠ w from fun e => hw (e ▸ hx)) _, fun x => ?_⟩
    by_cases e : x = w
    · subst e
      rw [GlobalTheory.CuspRep.pLoc_locGL]
      exact hkk
    · rw [GlobalTheory.CuspRep.pLoc_locGL_of_ne e]
      exact one_mem _
  have e := hC E n S B φ.1 φ'.1 φ.2.1.continuous φ'.2.1.continuous φ.2.1.isLeftInvariant φ'.2.1.isLeftInvariant
    (fun w hw => ⟨(hB w hw).2.1 φ hφ fun g k h => hk g _ (loc w hw k h),
      (hB w hw).2.2 φ' hφ' fun g k h => hk' g _ (loc w hw k h)⟩) hk hk'
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (Subtype.ext (funext h))
  obtain ⟨z, hz⟩ : ∃ z : (Ad E)ˣ, Reduction.centralSection E n s = GeneralLinearGroup.scalar (Fin n) z :=
    ⟨_, Units.ext rfl⟩
  have e1 := e z g g'
  rw [← hz, apply_mul_centralSection_of_mem (hc hφ)] at e1
  rw [Reduction.centralSection_mul_comm]
  exact (mul_left_cancel₀ hg e1).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.ConvFub
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.convFub :
    UpperTheory.V.Af.StrongMultiplicityOne.ChartCont → UpperTheory.V.Af.StrongMultiplicityOne.ConvFub := by
  classical
  intro hc E _ _ _ n f hf ⟨C, hC⟩ α X _ _ _ _ ν _ u a hu ha ⟨D, hD⟩ g
  have hS : MeasurableSet ((Set.univ : Set X) ×ˢ invSet E n) :=
    (isOpen_univ.prod GlobalTheory.CuspRep.isOpen_invSet).measurableSet
  have h1 : ContinuousOn (fun z : X × Lie E n => chart f (u z.1 * g) z.2) (Set.univ ×ˢ invSet E n) :=
    (hc E n f hf).1.comp (f := fun z : X × Lie E n => (u z.1 * g, z.2))
      (((hu.comp continuous_fst).mul continuous_const).prodMk continuous_snd).continuousOn
      fun z hz => ⟨trivial, hz.2⟩
  have h2 : Measurable fun z : X × Lie E n => chart f (u z.1 * g) z.2 := by
    have := h1.measurable_piecewise (g := fun _ => 0) continuousOn_const hS
    convert this using 1
    funext z
    by_cases hz : z ∈ (Set.univ : Set X) ×ˢ invSet E n
    · rw [Set.piecewise_eq_of_mem _ _ _ hz]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hz, chart]
      exact dif_neg fun h => hz ⟨trivial, h⟩
  have hb : ∀ g y, ‖chart f g y‖ ≤ C := fun g y => by
    unfold chart
    split_ifs
    · exact hC _
    · simpa using (norm_nonneg _).trans (hC 1)
  haveI : (volume : Measure (Fin n → Cinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hα : Integrable (fun y => α y) (volume : Measure (Lie E n)) := α.integrable
  have ha' : Integrable a ν := Integrable.of_bound ha.measurable.aestronglyMeasurable D (.of_forall hD)
  have hi : Integrable (fun z : X × Lie E n => chart f (u z.1 * g) z.2 * (a z.1 * α z.2)) (ν.prod volume) :=
    (ha'.mul_prod hα).bdd_mul h2.aestronglyMeasurable (.of_forall fun z => hb _ _)
  calc ∫ x, conv f α (u x * g) * a x ∂ν
      = ∫ x, (∫ y, chart f (u x * g) y * (a x * α y)) ∂ν := by
        refine integral_congr_ae (.of_forall fun x => ?_)
        simp only [conv]
        rw [← integral_mul_const]
        exact integral_congr_ae (.of_forall fun y => by ring)
    _ = ∫ y, ∫ x, chart f (u x * g) y * (a x * α y) ∂ν := integral_integral_swap hi
    _ = _ := by
        unfold conv
        refine integral_congr_ae (.of_forall fun y => ?_)
        simp only [chart]
        split_ifs with h
        · rw [← integral_mul_const]
          exact integral_congr_ae (.of_forall fun x => by simp only [mul_assoc])
        · simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.OrthConv
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

private theorem conv_left {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (f : GA E n → ℂ)
    (α : Lie E n → ℂ) (z : GA E n) (h : ∀ g, f (z * g) = f g) (g : GA E n) : Af.StrongMultiplicityOne.conv f α (z * g) = Af.StrongMultiplicityOne.conv f α g := by
  have e : chart f (z * g) = chart f g := by
    funext x
    unfold chart
    split_ifs with hx
    · rw [mul_assoc, h]
    · rfl
  unfold Af.StrongMultiplicityOne.conv
  rw [e]

private theorem zero_of_sq {E : Type} [Field E] [NumberField E] {n : ℕ} (μ : Measure (Reduction.normOneGL (K := E) (n := n)))
    [μ.IsHaarMeasure] (F : AdelicGLn.AdelicGL E n → ℂ) (hc : Continuous F) (C : ℝ) (hC : ∀ g, ‖F g‖ ≤ C)
    (h : IsLeftInvariant F)
    (h0 : ∫ q, starRingEnd ℂ (CuspidalSpectrum.cuspQuot h q) * CuspidalSpectrum.cuspQuot h q
      ∂(RightCosetSpace.quotientMeasure (Reduction.rationalGLOne (K := E) (n := n)) μ) = 0) :
    ∀ y ∈ Reduction.normOneGL (K := E) (n := n), F y = 0 := by
  have : OpensMeasurableSpace (RightCosetSpace (Reduction.rationalGLOne (K := E) (n := n))) := by
    set_option synthInstance.maxHeartbeats 200000 in
      infer_instance
  have := Reduction.isFiniteMeasure_quotientMeasure (K := E) (n := n) μ
  have hq := CuspidalSpectrum.continuous_cuspQuot h hc
  have hb : ∀ q, ‖CuspidalSpectrum.cuspQuot h q‖ ≤ C := fun q => by
    obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
    exact hC _
  have h1 : ∫ q, ‖CuspidalSpectrum.cuspQuot h q‖ ^ 2
      ∂(RightCosetSpace.quotientMeasure (Reduction.rationalGLOne (K := E) (n := n)) μ) = 0 := by
    rw [← Complex.ofReal_eq_zero, ← integral_complex_ofReal, ← h0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only [Complex.conj_mul', Complex.ofReal_pow]
  have hi : Integrable (fun q => ‖CuspidalSpectrum.cuspQuot h q‖ ^ 2)
      (RightCosetSpace.quotientMeasure (Reduction.rationalGLOne (K := E) (n := n)) μ) :=
    Integrable.of_bound (hq.norm.pow 2).aestronglyMeasurable (C ^ 2) (Filter.Eventually.of_forall fun q => by
      rw [norm_pow, norm_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb q) 2)
  have h2 := (integral_eq_zero_iff_of_nonneg (fun q => sq_nonneg _) hi).1 h1
  have h3 := MeasureTheory.QuasiMeasurePreserving.ae_eq_comp
    (RightCosetSpace.quasiMeasurePreserving_mk (Reduction.rationalGLOne (K := E) (n := n)) μ) h2
  have h4 := (Continuous.ae_eq_iff_eq μ (f := fun y : Reduction.normOneGL (K := E) (n := n) => ‖F y‖ ^ 2)
    ((hc.comp continuous_subtype_val).norm.pow 2) continuous_const).1 h3
  intro y hy
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (congrFun h4 ⟨y, hy⟩))

theorem UpperTheory.V.Af.StrongMultiplicityOne.orthConv :
    UpperTheory.V.Af.StrongMultiplicityOne.OrthStep → UpperTheory.V.Af.StrongMultiplicityOne.ConvCont → UpperTheory.V.Af.StrongMultiplicityOne.OrthConv := by
  intro hS hC E _ _ _ n μ _ φ φ' hφ hφ' ho β β' e
  obtain ⟨C, hb⟩ := exists_norm_le_of_mem_centralCuspForms hφ
  obtain ⟨C', hb'⟩ := exists_norm_le_of_mem_centralCuspForms hφ'
  have l : IsLeftInvariant (Af.StrongMultiplicityOne.conv φ.1 β) := fun γ g => conv_left _ _ _ (φ.2.1.isLeftInvariant γ) g
  have l' : IsLeftInvariant (Af.StrongMultiplicityOne.conv φ'.1 β') := fun γ g => conv_left _ _ _ (φ'.2.1.isLeftInvariant γ) g
  obtain ⟨hc, D, hD⟩ := hC E n φ'.1 φ'.2.1.continuous ⟨C', hb'⟩ β'
  have s1 : ∀ g, ∫ q, starRingEnd ℂ (quotTr φ g q) * CuspidalSpectrum.cuspQuot l' q
      ∂(RightCosetSpace.quotientMeasure (Reduction.rationalGLOne (K := E) (n := n)) μ) = 0 := fun g =>
    hS E n μ φ'.1 φ'.2.1.continuous ⟨C', hb'⟩ φ'.2.1.isLeftInvariant (fun q => starRingEnd ℂ (quotTr φ g q))
      (Complex.continuous_conj.comp (continuous_quotTr φ g))
      ⟨C, fun q => by
        obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
        rw [Complex.norm_conj]
        exact hb _⟩
      (fun g' _ => ho g g') β' l'
  have s2 := hS E n μ φ.1 φ.2.1.continuous ⟨C, hb⟩ φ.2.1.isLeftInvariant
    (fun q => starRingEnd ℂ (CuspidalSpectrum.cuspQuot l' q))
    (Complex.continuous_conj.comp (CuspidalSpectrum.continuous_cuspQuot l' hc))
    ⟨D, fun q => by
      obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
      rw [Complex.norm_conj]
      exact hD _⟩
    (fun g _ => by
      have h := congrArg (starRingEnd ℂ) (s1 g)
      rw [← integral_conj, map_zero] at h
      refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)) h
      simp only [map_mul, Complex.conj_conj]
      exact mul_comm _ _) β l
  have e' : CuspidalSpectrum.cuspQuot l = CuspidalSpectrum.cuspQuot l' :=
    CuspidalSpectrum.cuspQuot_surj_eq l l' fun y => congrFun e _
  rw [e'] at s2
  have z := zero_of_sq μ _ hc D hD l' s2
  rw [e]
  funext x
  obtain ⟨s, y, hy, rfl⟩ := CuspidalSpectrum.exists_centralSection_mul_mem_normOneGL x
  exact (conv_left _ _ _ (hφ' s) y).trans (z y hy)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Seed
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.seed :
    UpperTheory.V.Af.Smo.WhBasic → UpperTheory.V.Af.StrongMultiplicityOne.SeedConv → UpperTheory.V.Af.StrongMultiplicityOne.NiceOf → UpperTheory.V.Af.StrongMultiplicityOne.Seed := by
  intro hW hS hN E _ _ _ n U hU l sU
  have nice : ∀ φ ∈ U, Nice φ.1 := fun φ hφ => (hN E n φ).2 (l hφ)
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hU
  have N := nice φ hφ
  have hg : ∃ g, whittaker φ.1 g ≠ 0 := by
    by_contra h
    refine h0 (Subtype.ext (MultiplicityOne.eq_zero_of_whittaker_eq_zero N.cont N.left N.cusp ?_
      fun g => not_not.1 fun h' => h ⟨g, h'⟩))
    rw [Fb.finEmb_eq]
    exact N.level
  obtain ⟨g, hg⟩ := hg
  rw [← GlobalTheory.CuspRep.infGL_mul_finGL g] at hg
  generalize GeneralLinearGroup.map (pInf E) g = y at hg
  generalize GeneralLinearGroup.map (pFin E) g = k at hg
  have hφ' := sU.τ k φ hφ
  refine ⟨_, hφ', hS E n _ (hW E n _ (nice _ hφ')).1 y ?_⟩
  have e : (finRepCusp E n k φ).1 = fun x => φ.1 (x * finGL E n k) := by
    rw [← Fb.finEmb_eq]
    rfl
  rw [e]
  simpa only [whittaker, mul_assoc] using hg
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.EigMap
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

section

variable {E : Type} [Field E] [NumberField E] {n : ℕ} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}

private theorem sum_Tj {ϖ : w.adicCompletion E} (hϖ : Formalism.UG.IsUnifV E w ϖ) (j : ℕ) :
    ∃ s : Finset (GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n)),
      ∀ F : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n) → ℂ,
        ∑ᶠ c, Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j c.out * F c =
          ∑ c ∈ s, Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j c.out * F c := by
  have hf := Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm E w n) (GlobalTheory.LFun.Tj_mem_hecke (n := n) hϖ j).2
  refine ⟨hf.toFinset, fun F => finsum_eq_sum_of_support_subset _ fun c hc => ?_⟩
  rw [Set.Finite.coe_toFinset]
  exact left_ne_zero_of_mul hc

private theorem eig_zero (h : B.card = n) : Eig w B (fun _ : GL (Fin n) (w.adicCompletion E) => (0 : ℂ)) :=
  ⟨h, fun _ _ _ => rfl, fun _ _ _ _ _ => by simp⟩

private theorem eig_sub {W W' : GL (Fin n) (w.adicCompletion E) → ℂ} (h : Eig w B W) (h' : Eig w B W') :
    Eig w B (fun y => W y - W' y) := by
  refine ⟨h.card, fun g k hk => by simp only [h.inv g k hk, h'.inv g k hk], fun ϖ hϖ j hj g => ?_⟩
  obtain ⟨s, hs⟩ := sum_Tj (n := n) hϖ j
  have e := h.eig ϖ hϖ j hj g
  have e' := h'.eig ϖ hϖ j hj g
  rw [hs] at e e' ⊢
  simp only [mul_sub, Finset.sum_sub_distrib, e, e']

private theorem eig_int {X : Type} [MeasurableSpace X] (μ : Measure X) (hB : B.card = n)
    (F : X → GL (Fin n) (w.adicCompletion E) → ℂ) (a : X → ℂ) (h : ∀ x, Eig w B (F x))
    (hi : ∀ y, Integrable (fun x => F x y * a x) μ) : Eig w B (fun y => ∫ x, F x y * a x ∂μ) := by
  refine ⟨hB, fun g k hk => by simp only [fun x => (h x).inv g k hk], fun ϖ hϖ j hj g => ?_⟩
  obtain ⟨s, hs⟩ := sum_Tj (n := n) hϖ j
  rw [hs]
  simp only [← integral_const_mul]
  rw [← integral_finsetSum _ fun c _ => (hi _).const_mul _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have e := (h x).eig ϖ hϖ j hj g
  rw [hs] at e
  simp only [← mul_assoc, ← e, Finset.sum_mul]

end

open GroundTheory.Automorphic.FourierWhittaker in
theorem UpperTheory.V.Af.StrongMultiplicityOne.eigMap :
    UpperTheory.V.Af.StrongMultiplicityOne.ChartCont → UpperTheory.V.Af.StrongMultiplicityOne.EigMap := by
  intro hC E _ _ _ n w B f hf
  refine ⟨fun hN g => ?_, fun hN α g => ?_, fun f' hf' g => eig_sub (hf g) (hf' g)⟩
  · refine eig_int ((vecMeasure E (Pos n)).restrict (vecDomain E (Pos n))) (hf 1).card
      (fun X y => f (uGL X * (g * finGL E n (locGL E n w y))))
      (fun X => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ)) (fun X => ?_) fun y => ?_
    · simpa only [mul_assoc] using hf (uGL X * g)
    · have hc : Continuous fun X : Pos n → Ad E => f (uGL X * (g * finGL E n (locGL E n w y))) *
          (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
        (hN.cont.comp (continuous_uGL.mul continuous_const)).mul
          (continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_supSum 0).neg))
      exact (hc.continuousOn.integrableOn_compact isCompact_closure_vecDomain).mono_set subset_closure
  · refine eig_int volume (hf 1).card (fun x y => chart f (g * finGL E n (locGL E n w y)) x) α (fun x => ?_) fun y => ?_
    · by_cases hx : IsUnit (Matrix.of x)
      · have := hf (g * infGL E n hx.unit)
        simpa only [chart, dif_pos hx, mul_assoc, GlobalTheory.CuspRep.infGL_comm] using this
      · simpa only [chart, dif_neg hx] using eig_zero (w := w) (hf 1).card
    · obtain ⟨C, hC'⟩ := hN.bdd
      haveI : BorelSpace (Lie E n) := inferInstance
      haveI : (volume : Measure (Cinf E)).IsAddHaarMeasure := inferInstance
      haveI : (volume : Measure (Fin n → Cinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
      haveI : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
      refine α.integrable.bdd_mul (c := C) ((hC E n f hN.cont).2 _).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      unfold chart
      split_ifs
      · exact hC' _
      · simpa using (norm_nonneg _).trans (hC' 1)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.TrDual
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.trDual :
    UpperTheory.V.Af.StrongMultiplicityOne.TrDual := by
  classical
  intro E _ _
  let B : LinearMap.BilinForm ℝ (Cinf E) := (LinearMap.mul ℝ (Cinf E)).compr₂ (TG.tr E)
  have hl : ∀ x : Cinf E, (∀ y, B x y = 0) → x = 0 := fun x h => by
    have h1 : ∑ w, 2 * (x w * starRingEnd ℂ (x w)).re = 0 := h fun w => starRingEnd ℂ (x w)
    simp only [Complex.mul_conj, Complex.ofReal_re] at h1
    have b' := (Finset.sum_eq_zero_iff_of_nonneg fun w _ => mul_nonneg zero_le_two (Complex.normSq_nonneg (x w))).1 h1
    exact funext fun w => Complex.normSq_eq_zero.1 ((mul_eq_zero.1 (b' w (Finset.mem_univ _))).resolve_left two_ne_zero)
  have hB : B.Nondegenerate := ⟨hl, fun x h => hl x fun y => by
    have := h y
    change TG.tr E (_ * _) = 0 at this ⊢
    rwa [mul_comm]⟩
  let b := Module.finBasis ℝ (Cinf E)
  refine ⟨_, b, B.dualBasis hB b, fun x y => ?_⟩
  conv_lhs => rw [← b.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.BilinForm.dualBasis_repr_apply, mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.ArchStep
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private theorem of_lmul (a : Matrix (Fin n) (Fin n) (Cinf E)) (x : Lie E n) :
    lmul (toL a) x = toL (a * Matrix.of x) := rfl

private theorem lmul_one_add (a : Matrix (Fin n) (Fin n) (Cinf E)) (x : Lie E n) :
    lmul (toL (1 + a)) x = x + lmul (toL a) x := by
  rw [of_lmul, of_lmul, add_mul, one_mul]; rfl

private theorem exists_bil {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (L : V →ₗ[ℝ] Matrix (Fin n) (Fin n) (Cinf E)) :
    ∃ B : V →L[ℝ] Lie E n →L[ℝ] Lie E n, ∀ u x, B u x = lmul (toL (L u)) x := by
  let B0 : V →ₗ[ℝ] Lie E n →L[ℝ] Lie E n :=
    { toFun := fun u => lmul (toL (L u))
      map_add' := fun u v => by
        ext1 x
        rw [ContinuousLinearMap.add_apply, of_lmul, of_lmul, of_lmul, map_add (f := _), add_mul]; rfl
      map_smul' := fun c u => by
        ext1 x
        rw [ContinuousLinearMap.smul_apply, of_lmul, of_lmul, map_smul, smul_mul_assoc]; rfl }
  exact ⟨LinearMap.toContinuousLinearMap B0, fun _ _ => rfl⟩

private theorem isUnit_of_inj (a : Matrix (Fin n) (Fin n) (Cinf E)) (h : ∀ y : Lie E n, lmul (toL a) y = 0 → y = 0) :
    IsUnit a := by
  have hi : Function.Injective (LinearMap.mulLeft ℝ a) :=
    (injective_iff_map_eq_zero _).2 fun y hy => h (toL y) hy
  obtain ⟨b, hb⟩ := LinearMap.injective_iff_surjective.1 hi 1
  exact IsUnit.of_mul_eq_one b hb

variable {d : ℕ} (b : Module.Basis (Fin d) ℝ (Cinf E))

private noncomputable def crd (i : Fin n) : EuclideanSpace ℝ (Fin n × Fin d) →ₗ[ℝ] Cinf E where
  toFun u := b.equivFun.symm fun v => u (i, v)
  map_add' u v := map_add b.equivFun.symm (fun x => u (i, x)) fun x => v (i, x)
  map_smul' c u := map_smul b.equivFun.symm c fun x => u (i, x)

private noncomputable def colL (m : Fin n) : EuclideanSpace ℝ (Fin n × Fin d) →ₗ[ℝ] Matrix (Fin n) (Fin n) (Cinf E) where
  toFun u := Matrix.of fun i j => if i ≤ m ∧ j.val = m.val + 1 then crd b i u else 0
  map_add' u v := by
    ext1 i j
    simp only [Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> simp
  map_smul' c u := by
    ext1 i j
    simp only [Matrix.of_apply, Matrix.smul_apply]
    split_ifs <;> simp

private noncomputable def rowL (m : Fin n) : EuclideanSpace ℝ (Fin n × Fin d) →ₗ[ℝ] Matrix (Fin n) (Fin n) (Cinf E) where
  toFun u := Matrix.of fun i j => if i = m ∧ j ≤ m then -crd b j u else 0
  map_add' u v := by
    ext1 i j
    simp only [Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> simp [add_comm]
  map_smul' c u := by
    ext1 i j
    simp only [Matrix.of_apply, Matrix.smul_apply]
    split_ifs <;> simp

private noncomputable def eta (m : Fin n) (ξ : Fin n → Cinf E) : EuclideanSpace ℝ (Fin n × Fin d) :=
  WithLp.toLp 2 fun z => if z.1 ≤ m then -b.repr (ξ z.1) z.2 else 0

private theorem crd_eta (m : Fin n) (ξ : Fin n → Cinf E) {j : Fin n} (h : j ≤ m) : crd b j (eta b m ξ) = -ξ j := by
  change b.equivFun.symm _ = _
  rw [LinearEquiv.symm_apply_eq]
  funext v
  simp [eta, h]

private theorem repr_crd (j : Fin n) (u : EuclideanSpace ℝ (Fin n × Fin d)) (v : Fin d) :
    b.repr (crd b j u) v = u (j, v) :=
  congrFun (b.equivFun.apply_symm_apply fun v => u (j, v)) v

private theorem colL_sq (m : Fin n) (u : EuclideanSpace ℝ (Fin n × Fin d)) : colL b m u * colL b m u = 0 := by
  ext1 i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  simp only [colL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
  by_cases h : k ≤ m
  · rw [if_neg, zero_mul]
    rintro ⟨-, h'⟩
    rw [Fin.le_def] at h
    omega
  · rw [if_neg (fun h' : k ≤ m ∧ _ => h h'.1), mul_zero]

private theorem rowM_eq (m : Fin n) (ξ : Fin n → Cinf E) :
    rowM m ξ = 1 + rowL b m (eta b m ξ - eta b m ((1 : Matrix (Fin n) (Fin n) (Cinf E)) m)) := by
  ext1 i j
  simp only [rowM, rowL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Matrix.add_apply]
  split_ifs with h
  · obtain ⟨rfl, h⟩ := h
    rw [map_sub, crd_eta b _ _ h, crd_eta b _ _ h]
    ring
  · simp

private theorem inner_eta (b' : Module.Basis (Fin d) ℝ (Cinf E))
    (H : ∀ x y, TG.tr E (x * y) = ∑ i, b'.repr x i * b.repr y i) (m : Fin n) (ξ : Fin n → Cinf E)
    (u : EuclideanSpace ℝ (Fin n × Fin d)) :
    ⟪eta b' m ξ, u⟫ = -TG.tr E (dotLe m ξ fun j => crd b j u) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [PiLp.inner_apply, Fintype.sum_prod_type, dotLe, map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j ≤ m
  · rw [if_pos h, H, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [eta, h, repr_crd, mul_comm]
  · simp [eta, h]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Af.StrongMultiplicityOne.archStep :
    UpperTheory.V.Af.StrongMultiplicityOne.TrDual → UpperTheory.V.Af.Smo.SchTw → UpperTheory.V.Af.Smo.PftSch → UpperTheory.V.Af.Smo.BetaSch → UpperTheory.V.Af.Smo.BetaInt → UpperTheory.V.Af.StrongMultiplicityOne.ArchStep := by
  intro h0 h1 h2 h3 h4 E _ _ n m _
  obtain ⟨d, b, b', H⟩ := h0 E
  obtain ⟨B, hB⟩ := exists_bil (colL b m)
  obtain ⟨A, hA⟩ := exists_bil (rowL b' m)
  have hBB : ∀ u x, B u (B u x) = 0 := fun u x => by
    rw [hB, hB, of_lmul, of_lmul]
    change toL (colL b m u * (colL b m u * Matrix.of x)) = 0
    rw [← mul_assoc, colL_sq, zero_mul]; rfl
  obtain ⟨h, he, hu, hG⟩ := h1 _ _ A (eta b' m ((1 : Matrix (Fin n) (Fin n) (Cinf E)) m))
  have hrow : ∀ ξ y, y + A (eta b' m ξ - eta b' m ((1 : Matrix (Fin n) (Fin n) (Cinf E)) m)) y = lmul (toL (rowM m ξ)) y :=
    fun ξ y => by rw [rowM_eq b', lmul_one_add, hA]
  refine ⟨fun ξ => h (eta b' m ξ), he, fun ξ hξ => isUnit_of_inj _ fun y hy => hu _ hξ y (by rw [hrow, hy]), fun α => ?_⟩
  obtain ⟨G, hG⟩ := hG α
  obtain ⟨K, hK⟩ := h2 _ _ G
  obtain ⟨K', β, hK', hβ⟩ := h3 _ _ B hBB K
  refine ⟨β, fun w ξ hw hb hw' => ?_⟩
  haveI : (volume : Measure (Cinf E)).IsAddHaarMeasure := inferInstance
  haveI : (volume : Measure (Fin n → Cinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have := h4 _ _ (volume : Measure (Lie E n)) B hBB G K K' hK hK' w (eta b' m ξ) hw hb fun u x => by
    rw [hB, ← lmul_one_add, inner_eta b b' H]
    exact hw' (fun j => crd b j u) x
  simp only [hβ]
  rw [this, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hG, hrow]
  ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.SphAll
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

private theorem comm_loc {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (g : GA E n) (hg : cmp w (GeneralLinearGroup.map (pFin E) g) = 1) (y : GL (Fin n) (w.adicCompletion E)) :
    g * finGL E n (locGL E n w y) = finGL E n (locGL E n w y) * g := by
  refine GlobalTheory.CuspRep.ga_ext ?_ ?_
  · rw [map_mul, map_mul, GlobalTheory.CuspRep.pInf_finGL, mul_one, one_mul]
  · rw [map_mul, map_mul, GlobalTheory.CuspRep.pFin_finGL]
    refine cmp_ext fun v => ?_
    rw [map_mul, map_mul]
    by_cases h : v = w
    · subst h
      rw [hg, mul_one, one_mul]
    · have : cmp v (locGL E n w y) = 1 := GlobalTheory.CuspRep.pLoc_locGL_of_ne h y
      rw [this, mul_one, one_mul]

theorem UpperTheory.V.Af.StrongMultiplicityOne.sphAll :
    UpperTheory.V.Af.Smo.AwayInd → UpperTheory.V.Af.Smo.SphZero → UpperTheory.V.Af.StrongMultiplicityOne.EmbY → UpperTheory.V.Af.StrongMultiplicityOne.SphAll := by
  intro hA hZ hE E _ _ _ n S B W hW hS hK p hp h0
  refine hA E n S (fun k => W (p * finGL E n k) = 0) (fun k hk => (hK p k hk).trans h0) ?_
  intro w hw k _ hk hP y
  have hc : cmp w (GeneralLinearGroup.map (pFin E) (p * finGL E n k)) = 1 := by
    rw [map_mul, map_mul, GlobalTheory.CuspRep.pFin_finGL, hp w hw, hk, mul_one]
  obtain ⟨e1, e2, -, -⟩ := hE E n 0
  have hz := hZ E n w (psiL w) (hS w hw).1 (B w) _ ?_ ((hS w hw).2 (p * finGL E n k)) (by simpa using hP)
  · have := congrFun hz y
    simpa [mul_assoc] using this
  · intro ν hν g
    obtain ⟨a1, a2⟩ := e1 w ν hν
    obtain ⟨b1, b2⟩ := e2 _ a1
    have := hW _ b1 (p * finGL E n k * finGL E n (locGL E n w g))
    rw [b2, a2] at this
    show W _ = _
    rw [map_mul, map_mul, ← mul_assoc, comm_loc w _ hc ν, mul_assoc, this]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.ConvNice
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.convNice :
    UpperTheory.V.Af.StrongMultiplicityOne.ConvCont → UpperTheory.V.Af.StrongMultiplicityOne.ConvFub → UpperTheory.V.Af.StrongMultiplicityOne.ConvNice := by
  intro hc hf E _ _ _ n f hN α
  obtain ⟨h1, h2⟩ := hc E n f hN.cont hN.bdd α
  refine ⟨⟨h1, h2, ?_, ?_, ?_⟩, ?_⟩
  · intro γ g
    have e : chart f (AdelicGLn.diagonal E n γ * g) = chart f g := by
      funext x
      simp only [chart, mul_assoc, hN.left γ]
    simp only [conv, e]
  · intro r hr hrn g
    haveI : IsFiniteMeasure ((unipMeasure E n r).restrict (unipFundamentalDomain E n r)) := by
      obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := E) (n := n) (r := r)
      exact ⟨by
        rw [Measure.restrict_apply_univ]
        exact (measure_mono hDC).trans_lt hC.measure_lt_top⟩
    have h := hf E n f hN.cont hN.bdd α _ ((unipMeasure E n r).restrict (unipFundamentalDomain E n r))
      unipGL (fun _ => 1) continuous_unipGL continuous_const ⟨1, fun _ => by simp⟩ g
    simp only [mul_one] at h
    have e : (fun g' => ∫ x in unipFundamentalDomain E n r, f (unipGL x * g') ∂unipMeasure E n r) = fun _ => 0 :=
      funext fun g' => hN.cusp r hr hrn g'
    rw [constantTerm, h, e]
    simp [conv, chart]
  · obtain ⟨V, hV⟩ := hN.level
    refine ⟨V, fun g v hv => ?_⟩
    have e : (fun x => f (x * finGL E n v)) = f := funext fun x => hV x v hv
    rw [conv, ← GlobalTheory.CuspRep.chart_rt_fin, e, conv]
  · funext g
    haveI : IsFiniteMeasure ((FourierWhittaker.vecMeasure E (FourierWhittaker.Pos n)).restrict
        (FourierWhittaker.vecDomain E (FourierWhittaker.Pos n))) :=
      ⟨by rw [Measure.restrict_apply_univ, FourierWhittaker.vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
    exact hf E n f hN.cont hN.bdd α _ ((FourierWhittaker.vecMeasure E (FourierWhittaker.Pos n)).restrict
        (FourierWhittaker.vecDomain E (FourierWhittaker.Pos n))) FourierWhittaker.uGL
      (fun X => (GroundTheory.Global.adelicChar E (-FourierWhittaker.supSum 0 X) : ℂ)) FourierWhittaker.continuous_uGL
      (continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp
        (FourierWhittaker.continuous_supSum 0).neg)) ⟨1, fun _ => (Circle.norm_coe _).le⟩ g
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.InKSMono
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

private theorem inKS_mono {E : Type} [Field E] [NumberField E] {n : ℕ} {S T : Finset (HeightOneSpectrum (𝓞 E))}
    (h : S ⊆ T) {k : GL (Fin n) (Af E)} (hk : InKS T k) : InKS S k :=
  ⟨fun w hw => hk.1 w (h hw), hk.2⟩

theorem UpperTheory.V.Af.StrongMultiplicityOne.setUp :
    UpperTheory.V.Af.Smo.PsiLoc → UpperTheory.V.Af.Smo.LevelS → UpperTheory.V.Af.StrongMultiplicityOne.NiceOf → UpperTheory.V.Af.StrongMultiplicityOne.SetUp := by
  intro hP hL hN E _ _ n U U' hs φ φ'
  classical
  have lev : ∀ φ : cuspForms E n, ∃ S : Finset (HeightOneSpectrum (𝓞 E)),
      ∀ g k, InKS S k → φ.1 (g * finGL E n k) = φ.1 g := fun φ => by
    obtain ⟨V, hV⟩ := (hN E n φ).1
    obtain ⟨S, hS⟩ := hL E n V
    exact ⟨S, fun g k hk => hV g k (hS k hk)⟩
  obtain ⟨S₁, h₁⟩ := lev φ
  obtain ⟨S₂, h₂⟩ := lev φ'
  have hf := Filter.eventually_cofinite.1 ((hP E).2.and hs)
  have hB : ∀ w : HeightOneSpectrum (𝓞 E), ∃ B : Multiset ℂˣ, w ∉ hf.toFinset →
      GoodAt w (psiL w) ∧ Sat w B U ∧ Sat w B U' := fun w => by
    by_cases hw : w ∈ hf.toFinset
    · exact ⟨0, fun h => absurd hw h⟩
    · rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hw
      obtain ⟨hg, B, hB⟩ := hw
      exact ⟨B, fun _ => ⟨hg, hB⟩⟩
  choose B hB using hB
  refine ⟨hf.toFinset ∪ (S₁ ∪ S₂), B, fun w hw => hB w fun h => hw (Finset.mem_union_left _ h),
    fun g k hk => h₁ g k (inKS_mono ?_ hk), fun g k hk => h₂ g k (inKS_mono ?_ hk)⟩
  · exact Finset.subset_union_left.trans Finset.subset_union_right
  · exact Finset.subset_union_right.trans Finset.subset_union_right
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.ChartCont
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

private theorem cc_infGL (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (a : ℕ) :
    Continuous (infGL F a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf F : Cinf F → Ad F) := (GlobalTheory.CuspRep.continuous_infEq F).prodMk continuous_const
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

private theorem cc_unit (E : Type) [Field E] [NumberField E] (n : ℕ) {X : Type} [TopologicalSpace X]
    (u : X → GL (Fin n) (Cinf E)) (hu : Continuous fun x => (u x).val) : Continuous u := by
  refine Units.continuous_iff.2 ⟨hu, ?_⟩
  have e : (fun x => ((u x)⁻¹).val) = fun x => ((u x).val)⁻¹ := funext fun x => Matrix.coe_units_inv _
  rw [e]
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hd : IsUnit ((u x).val).det := (Matrix.isUnit_iff_isUnit_det _).1 (u x).isUnit
  obtain ⟨d, hd⟩ := hd
  refine ContinuousAt.comp (f := fun x => (u x).val) (continuousAt_matrix_inv _ ?_) hu.continuousAt
  rw [← hd]
  exact NormedRing.inverse_continuousAt d

theorem UpperTheory.V.Af.StrongMultiplicityOne.chartCont :
    UpperTheory.V.Af.StrongMultiplicityOne.ChartCont := by
  intro E _ _ _ n f hf
  have h1 : ContinuousOn (fun z : GA E n × Lie E n => chart f z.1 z.2) (Set.univ ×ˢ invSet E n) := by
    rw [continuousOn_iff_continuous_restrict]
    let u : ↥((Set.univ : Set (GA E n)) ×ˢ invSet E n) → GL (Fin n) (Cinf E) :=
      fun z => (show IsUnit (Matrix.of z.1.2) from z.2.2).unit
    have hu : Continuous u := cc_unit E n u (continuous_snd.comp continuous_subtype_val)
    have e : ((Set.univ : Set (GA E n)) ×ˢ invSet E n).domRestrict (fun z : GA E n × Lie E n => chart f z.1 z.2) =
        fun z => f (z.1.1 * infGL E n (u z)) := by
      funext z
      have h : IsUnit (Matrix.of z.1.2) := z.2.2
      change chart f z.1.1 z.1.2 = _
      rw [chart, dite_eq_left h]
    rw [e]
    exact hf.comp ((continuous_fst.comp continuous_subtype_val).mul ((cc_infGL E n).comp hu))
  refine ⟨h1, fun g => ?_⟩
  classical
  have h2 : ContinuousOn (chart f g) (invSet E n) :=
    h1.comp (f := fun x => (g, x)) (continuous_const.prodMk continuous_id).continuousOn
      fun x hx => ⟨Set.mem_univ _, hx⟩
  have h3 := h2.measurable_piecewise (g := fun _ => (0 : ℂ)) continuousOn_const GlobalTheory.CuspRep.isOpen_invSet.measurableSet
  convert h3 using 1
  funext x
  by_cases hx : x ∈ invSet E n
  · rw [Set.piecewise_eq_of_mem _ _ _ hx]
  · rw [Set.piecewise_eq_of_notMem _ _ _ hx, chart, dite_eq_right (show ¬ IsUnit (Matrix.of x) from hx)]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.FinKir
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

private theorem isY_map {R S : Type} [CommRing R] [CommRing S] {n m : ℕ} (f : R →+* S) {k : GL (Fin n) R}
    (h : IsY m k.val) : IsY m (GeneralLinearGroup.map f k).val := by
  intro i hi
  refine ⟨?_, fun j hj => ?_⟩
  · change f (k.val i i) = 1
    rw [(h i hi).1, map_one]
  · change f (k.val i j) = 0
    rw [(h i hi).2 j hj, map_zero]

private theorem isY_one {R : Type} [CommRing R] {n m : ℕ} : IsY m (1 : GL (Fin n) R).val := by
  intro i _
  exact ⟨by simp, fun j hj => by simp [Matrix.one_apply_ne hj.ne']⟩

private theorem isY_of_cmp {E : Type} [Field E] [NumberField E] {n m : ℕ} {k : GL (Fin n) (Af E)}
    (h : ∀ w, IsY m (cmp w k).val) : IsY m k.val := by
  intro i hi
  refine ⟨DFunLike.ext _ _ fun w => ?_, fun j hj => DFunLike.ext _ _ fun w => ?_⟩
  · exact (h w i hi).1
  · exact (h w i hi).2 j hj

private theorem loc_comm {E : Type} [Field E] [NumberField E] {n : ℕ} {w : HeightOneSpectrum (𝓞 E)}
    {k : GL (Fin n) (Af E)} (hk : cmp w k = 1) (y : GL (Fin n) (w.adicCompletion E)) :
    k * locGL E n w y = locGL E n w y * k := by
  refine cmp_ext fun v => ?_
  rw [map_mul, map_mul]
  by_cases hv : v = w
  · subst hv
    rw [hk, one_mul, mul_one]
  · rw [show cmp v (locGL E n w y) = 1 from GlobalTheory.CuspRep.pLoc_locGL_of_ne hv y, one_mul, mul_one]

private theorem supp_mul {E : Type} [Field E] [NumberField E] {n : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))}
    {a b : GL (Fin n) (Af E)} (ha : SuppIn S a) (hb : SuppIn S b) : SuppIn S (a * b) := fun w hw => by
  rw [map_mul, ha w hw, hb w hw, mul_one]

private theorem supp_loc {E : Type} [Field E] [NumberField E] {n : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))}
    {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ S) (y : GL (Fin n) (w.adicCompletion E)) :
    SuppIn S (locGL E n w y) := fun v hv =>
  GlobalTheory.CuspRep.pLoc_locGL_of_ne (fun e : v = w => hv (e ▸ hw)) y

private theorem comb_mapDomain {G G' : Type} [Group G] [Group G'] (f : G →* G') (c : G →₀ ℂ) (W : G' → ℂ)
    (g : G') (p : G) : comb (c.mapDomain f) W (g * f p) = comb c (fun y => W (g * f y)) p := by
  unfold comb
  rw [Finsupp.sum_mapDomain_index (by simp) (by intros; ring)]
  simp only [map_mul, mul_assoc]

theorem UpperTheory.V.Af.StrongMultiplicityOne.finKir :
    UpperTheory.V.Af.Smo.LocKir → UpperTheory.V.Af.Smo.PsiLoc → UpperTheory.V.Af.StrongMultiplicityOne.EmbY → UpperTheory.V.Af.StrongMultiplicityOne.FinKir := by
  classical
  intro hK hP hE E _ _ _ n hn S U
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨Finsupp.single 1 1, fun _ => 1, rfl, fun x hx => ?_, fun W _ _ p hp _ => ?_⟩
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hx)]
      exact fun w _ => map_one _
    · obtain rfl : p = 1 := cmp_ext fun w => (hp w (Finset.notMem_empty w)).trans (map_one _).symm
      unfold comb
      rw [Finsupp.sum_single_index (by simp), mul_one]
  | insert w S hw ih =>
    obtain ⟨c₁, H₁, h1, hs₁, hc₁⟩ := ih
    obtain ⟨hE1, -, -, hEc⟩ := hE E n 0
    obtain ⟨c₀, H₀, h0, hc₀⟩ := hK E w (psiL w) ((hP E).1 w).1 ((hP E).1 w).2 n (n - 1) (by omega)
      (U.comap (locGL E n w) (hEc w))
    obtain ⟨c, hs, hc⟩ := exists_comb_comb c₁ (c₀.mapDomain (locGL E n w))
    have mono : ∀ {k : GL (Fin n) (Af E)}, SuppIn S k → SuppIn (insert w S) k :=
      fun hk v hv => hk v fun h => hv (Finset.mem_insert_of_mem h)
    have hl : ∀ y, SuppIn (insert w S) (locGL E n w y) := supp_loc (Finset.mem_insert_self w S)
    refine ⟨c, fun p => H₀ (cmp w p) * H₁ (p * (locGL E n w (cmp w p))⁻¹), ?_, fun x hx => ?_,
      fun W hW hU p hp hY => ?_⟩
    · simp only [map_one, inv_one, mul_one, h0, h1]
    · obtain ⟨a, ha, b, hb, rfl⟩ := hs x hx
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hb)
      exact supp_mul (mono (hs₁ a ha)) (hl y)
    · have key : ∀ g, SuppIn S g → comb (c₀.mapDomain (locGL E n w)) W (g * locGL E n w (cmp w p))
          = H₀ (cmp w p) * W g := by
        intro g hg
        rw [comb_mapDomain, hc₀ (fun y => W (g * locGL E n w y)) ?_ ?_ _ (isY_map _ hY), map_one, mul_one]
        · intro ν hν y
          beta_reduce
          rw [map_mul, ← mul_assoc, loc_comm (hg w hw), mul_assoc,
            hW _ (hl ν) (hE1 w ν hν).1 _ (supp_mul (mono hg) (hl y)), (hE1 w ν hν).2]
          rfl
        · intro y u hu
          beta_reduce
          rw [map_mul, ← mul_assoc]
          exact hU _ (supp_mul (mono hg) (hl y)) _ hu (hl u)
      set p' := p * (locGL E n w (cmp w p))⁻¹ with hp'
      have e0 : cmp w p' = 1 := by
        rw [hp', map_mul, map_inv, show cmp w (locGL E n w (cmp w p)) = cmp w p from GlobalTheory.CuspRep.pLoc_locGL w _,
          mul_inv_cancel]
      have e1 : ∀ v, v ≠ w → cmp v p' = cmp v p := fun v hv => by
        rw [hp', map_mul, map_inv, show cmp v (locGL E n w (cmp w p)) = 1 from GlobalTheory.CuspRep.pLoc_locGL_of_ne hv _,
          inv_one, mul_one]
      have hS : SuppIn S p' := fun v hv => by
        by_cases h : v = w
        · subst h; exact e0
        · rw [e1 v h]
          exact hp v fun h' => (Finset.mem_insert.1 h').elim h hv
      have hY' : IsY (n - 1) p'.val := isY_of_cmp fun v => by
        by_cases h : v = w
        · subst h; rw [e0]; exact isY_one
        · rw [e1 v h]; exact isY_map _ hY
      have ep : p = p' * locGL E n w (cmp w p) := by rw [hp', inv_mul_cancel_right]
      have hI := hc₁ W (fun ν hν hy g hg => hW ν (mono hν) hy g (mono hg))
        (fun g hg u hu hu' => hU g (mono hg) u hu (mono hu')) p' hS hY'
      rw [hc, mul_assoc, ← hI]
      unfold comb at key ⊢
      rw [Finsupp.mul_sum]
      refine Finsupp.sum_congr fun x hx => ?_
      have e2 : p * x = p' * x * locGL E n w (cmp w p) := by
        rw [mul_assoc, loc_comm (hs₁ x hx w hw), ← mul_assoc, ← ep]
      rw [e2, key _ (supp_mul hS (hs₁ x hx))]
      ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.ConvCont
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.convCont :
    UpperTheory.V.Af.StrongMultiplicityOne.ChartCont → UpperTheory.V.Af.StrongMultiplicityOne.ConvCont := by
  intro hc E _ _ _ n f hf hb α
  obtain ⟨C, hC⟩ := hb
  obtain ⟨h1, h2⟩ := hc E n f hf
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
  have hch : ∀ g x, ‖chart f g x‖ ≤ C := by
    intro g x
    unfold GlobalTheory.CuspRep.chart
    split_ifs
    · exact hC _
    · simpa using hC0
  have hbd : ∀ g x, ‖chart f g x * α x‖ ≤ C * ‖α x‖ := by
    intro g x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hch g x) (norm_nonneg _)
  haveI i1 : (volume : Measure (Cinf E)).IsAddHaarMeasure := inferInstance
  haveI i2 : (volume : Measure (Fin n → Cinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI i3 : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hint : Integrable (fun x => C * ‖α x‖) := (α.integrable.norm).const_mul C
  haveI : FirstCountableTopology (GA E n) :=
    GroundTheory.Automorphic.FourierWhittaker.firstCountableTopology_adelicGL ..
  refine ⟨?_, ∫ x, C * ‖α x‖, fun g => ?_⟩
  · unfold conv
    refine continuous_of_dominated (bound := fun x => C * ‖α x‖) (fun g => ?_) (fun g => ?_) hint ?_
    · exact ((h2 g).mul α.continuous.measurable).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (hbd g)
    · refine Filter.Eventually.of_forall fun x => ?_
      refine Continuous.mul ?_ continuous_const
      by_cases hx : x ∈ invSet E n
      · exact h1.comp_continuous (f := fun g : GA E n => (g, x)) (by fun_prop) fun g => ⟨Set.mem_univ _, hx⟩
      · have : (fun g => chart f g x) = fun _ => 0 := by
          funext g
          unfold GlobalTheory.CuspRep.chart
          exact dif_neg hx
        rw [this]
        exact continuous_const
  · exact norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall (hbd g))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.PsiInf
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.psiInf :
    UpperTheory.V.Af.StrongMultiplicityOne.PsiInf := by
  intro E _ _ _ x
  have h : GroundTheory.Global.adelicChar E (sInf E x) = 𝐞 (-TG.tr E x) := by
    have e : sInf E x = GroundTheory.Global.infiniteAdeleInl (GlobalTheory.CuspRep.infEq E x) := rfl
    rw [e, GroundTheory.Global.adelicChar_infiniteAdeleInl, TG.tr_apply, ← Finset.sum_neg_distrib,
      GroundTheory.Global.addChar_map_finsetSum]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [GroundTheory.Global.infiniteAdelicChar_apply_of_isComplex (IsTotallyComplex.isComplex w)]
    have e2 : InfinitePlace.Completion.extensionEmbedding w (GlobalTheory.CuspRep.infEq E x w) = x w :=
      Cm.mixRing_snd x ⟨w, IsTotallyComplex.isComplex w⟩
    rw [e2]
  exact congrArg (fun z : Circle => (z : ℂ)) h
end

namespace UpperTheory.V.Af

theorem StrongMultiplicityOne.smoCentral : StrongMultiplicityOne.SmoCentral := by
  have hPft := Smo.pftSch_of Smo.schOfClosed Smo.pftDeriv Smo.pftMul
  have hStep := StrongMultiplicityOne.archStep StrongMultiplicityOne.trDual (Smo.schTw (Smo.schTensor Smo.schOfClosed)) hPft (Smo.betaSch hPft) Smo.betaInt
  have hArch := StrongMultiplicityOne.archKir Smo.colConj Smo.rowStep hStep StrongMultiplicityOne.linChange
  have hLoc := Smo.locKir Smo.colConj Smo.rowStep (Smo.locStep Smo.avgChar Smo.locDual)
  have hKill := StrongMultiplicityOne.killP hArch (StrongMultiplicityOne.finKir hLoc Smo.psiLoc StrongMultiplicityOne.embY) StrongMultiplicityOne.embY StrongMultiplicityOne.psiInf StrongMultiplicityOne.chartCont
  have hZero := Smo.sphZero Smo.sphDict (Smo.tjSet Smo.sphDict) Smo.centLoc
  have hMap := StrongMultiplicityOne.eigMap StrongMultiplicityOne.chartCont
  have hVan := StrongMultiplicityOne.vanish (StrongMultiplicityOne.sphAll Smo.awayInd hZero StrongMultiplicityOne.embY) Smo.injP Smo.denseAway Smo.whBasic hMap
  have hCont := StrongMultiplicityOne.convCont StrongMultiplicityOne.chartCont
  have hSet := StrongMultiplicityOne.setUp Smo.psiLoc Smo.levelS StrongMultiplicityOne.niceOf
  have hPair := StrongMultiplicityOne.pair (StrongMultiplicityOne.seed Smo.whBasic (StrongMultiplicityOne.seedConv StrongMultiplicityOne.chartCont) StrongMultiplicityOne.niceOf) hSet hKill hVan Smo.whBasic
    Smo.whLin (StrongMultiplicityOne.convNice hCont (StrongMultiplicityOne.convFub StrongMultiplicityOne.chartCont)) StrongMultiplicityOne.niceOf hMap
  exact StrongMultiplicityOne.smoCentral_of (StrongMultiplicityOne.cenSame (Smo.centEq Smo.centLoc Smo.awayInd Smo.denseAway) hSet) hPair StrongMultiplicityOne.compl
    (StrongMultiplicityOne.proj hMap) Smo.orthTr (StrongMultiplicityOne.orthConv (StrongMultiplicityOne.orthStep StrongMultiplicityOne.chartCont) hCont)

theorem strongMultOneC : StrongMultiplicityOne.StrongMultOneC :=
  StrongMultiplicityOne.strong_of StrongMultiplicityOne.smoCentral StrongMultiplicityOne.carrier StrongMultiplicityOne.eigOfSat StrongMultiplicityOne.normTwist

end UpperTheory.V.Af
