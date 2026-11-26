module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongRegularise
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceImmersiveGeneral
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsPiola

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

variable {n : ℕ}

instance isPrime_ker_eval (q : Fin n → ℂ) : (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime :=
  RingHom.ker_isPrime _

def curveLocalRing (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) : Type :=
  Localization.AtPrime (RingHom.ker (eval q)) ⧸
    I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))

instance (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) : CommRing (curveLocalRing I q) :=
  inferInstanceAs (CommRing (Localization.AtPrime (RingHom.ker (eval q)) ⧸
    I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))))

instance (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    Algebra (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) :=
  inferInstanceAs (Algebra (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)) ⧸
    I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))))

instance (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) : IsNoetherianRing (curveLocalRing I q) :=
  inferInstanceAs (IsNoetherianRing (Localization.AtPrime (RingHom.ker (eval q)) ⧸
    I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))))

def curveNormalisation (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) : Type :=
  ↥(integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q)))

instance (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) : CommRing (curveNormalisation I q) :=
  inferInstanceAs (CommRing ↥(integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))))

instance (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    Algebra (curveLocalRing I q) (curveNormalisation I q) :=
  inferInstanceAs
    (Algebra (curveLocalRing I q) ↥(integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))))

theorem isUnit_algebraMap_curveLocalRing (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (f : MvPolynomial (Fin n) ℂ) (hf : eval q f ≠ 0) :
    IsUnit (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f) := by
  have hu : IsUnit (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))) f) :=
    IsLocalization.map_units _ (⟨f, fun h ↦ hf (RingHom.mem_ker.1 h)⟩ : (RingHom.ker (eval q)).primeCompl)
  exact hu.map (Ideal.Quotient.mk _)

theorem curveLocalRing_subsingleton (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (hq : q ∉ zeroSet I) : Subsingleton (curveLocalRing I q) := by
  simp only [zeroSet, Set.mem_ofPred_eq, not_forall] at hq
  obtain ⟨g, hg, hgq⟩ := hq
  unfold curveLocalRing
  rw [Ideal.Quotient.subsingleton_iff]
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hg)
    (IsLocalization.map_units _ (⟨g, fun h ↦ hgq (RingHom.mem_ker.1 h)⟩ : (RingHom.ker (eval q)).primeCompl))

theorem algebraMap_curveNormalisation_injective (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    Function.Injective (algebraMap (curveLocalRing I q) (curveNormalisation I q)) := by
  intro a b h
  exact IsLocalization.injective (FractionRing (curveLocalRing I q)) le_rfl (congrArg Subtype.val h)

def CurveNormalisationLength.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
    algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f ∈ nonZeroDivisors (curveLocalRing I q) →
      (localMult (I ⊔ Ideal.span {f}) (RingHom.ker (eval q)) : ℕ∞) =
        ∑ᶠ P : MaximalSpectrum (curveNormalisation I q),
          Ring.ord (Localization.AtPrime P.asIdeal)
              (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
                (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                  (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) *
            Module.length (curveLocalRing I q) (curveNormalisation I q ⧸ P.asIdeal)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetOnlyNull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace SheetOnlyNull

variable {n d : ℕ}

theorem injective_iff_det_ne_zero (L : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) :
    Function.Injective L ↔ LinearMap.det (L : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) ≠ 0 := by
  rw [← isUnit_iff_ne_zero, ← LinearMap.isUnit_iff_isUnit_det, LinearMap.isUnit_iff_ker_eq_bot,
    LinearMap.ker_eq_bot]
  rfl

theorem finrank_real_fin_complex (d : ℕ) : Module.finrank ℝ (Fin d → ℂ) = 2 * d := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Complex.finrank_real_complex, smul_eq_mul, mul_comm]

theorem differentiableOn_mulVec {m : ℕ} (B : Matrix (Fin m) (Fin n) ℂ) {U : Set (Fin d → ℂ)}
    {s : (Fin d → ℂ) → Fin n → ℂ} (hs : DifferentiableOn ℂ s U) :
    DifferentiableOn ℂ (fun w => B *ᵥ s w) U :=
  (LinearMap.toContinuousLinearMap B.mulVecLin).differentiable.comp_differentiableOn hs

theorem analyticOnNhd_of_differentiableOn {m : ℕ} {U : Set (Fin d → ℂ)}
    {F : (Fin d → ℂ) → Fin m → ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    AnalyticOnNhd ℂ F U := fun w hw =>
  AnalyticAt.pi fun i => ReciprocityTheory.AnForm.Osgood.osgood d U (fun z => F z i) hU
    (differentiableOn_pi.1 hF i) w hw

theorem analyticOnNhd_det_jacC {U : Set (Fin d → ℂ)} {F : (Fin d → ℂ) → Fin d → ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    AnalyticOnNhd ℂ (fun w => (ReciprocityTheory.AnForm.A.jacC F w).det) U := by
  intro w hw
  have hF' := (analyticOnNhd_of_differentiableOn hU hF).fderiv w hw
  have hent : ∀ a k, AnalyticAt ℂ (fun z => ReciprocityTheory.AnForm.A.jacC F z a k) w := fun a k => by
    show AnalyticAt ℂ (fun z => fderiv ℂ F z (Pi.single k 1) a) w
    exact (((ContinuousLinearMap.proj a).comp
      (ContinuousLinearMap.apply ℂ (Fin d → ℂ) (Pi.single k (1 : ℂ)))).analyticAt _).comp hF'
  simp only [Matrix.det_apply']
  exact Finset.analyticAt_fun_sum _ fun σ _ => analyticAt_const.mul
    (Finset.analyticAt_fun_prod _ fun i _ => hent _ _)

theorem exists_sheet_nhds {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (x : Fin n → ℂ) :
    ∃ (s : (Fin d → ℂ) → Fin n → ℂ) (U : Set (Fin d → ℂ)) (W : Set (Fin n → ℂ)),
      IsOpen U ∧ IsOpen W ∧ DifferentiableOn ℂ s U ∧
      (∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ U ∧ IsSheetAt J A x' s) ∧
      ((∃ s, IsSheetAt J A x s) → x ∈ W) := by
  by_cases hx : ∃ s, IsSheetAt J A x s
  · obtain ⟨s, U, hU, hxU, hsd, hsx, hsec, V, hV, hVs⟩ := hx
    have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
    refine ⟨s, U, interior V ∩ (fun z => A *ᵥ z) ⁻¹' U, hU,
      isOpen_interior.inter (hU.preimage hAc), hsd, ?_, fun _ =>
        ⟨mem_interior_iff_mem_nhds.2 hV, hxU⟩⟩
    rintro x' ⟨hx'Z, hx'V, hx'U⟩
    have hx's : s (A *ᵥ x') = x' := (hVs x' ⟨hx'Z, interior_subset hx'V⟩ hx'U).symm
    exact ⟨hx'U, U, hU, hx'U, hsd, hx's, hsec, interior V, isOpen_interior.mem_nhds hx'V,
      fun x'' hx'' hAx'' => hVs x'' ⟨hx''.1, interior_subset hx''.2⟩ hAx''⟩
  · exact ⟨fun _ => x, ∅, ∅, isOpen_empty, isOpen_empty, differentiableOn_empty,
      by simp, fun h => absurd h hx⟩

theorem exists_sheet_of_det_ne_zero {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A A' : Matrix (Fin d) (Fin n) ℂ} {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ}
    (hs : IsSheetAt J A x s)
    (hdet : (ReciprocityTheory.AnForm.A.jacC (fun w => A' *ᵥ s w) (A *ᵥ x)).det ≠ 0) :
    ∃ s', IsSheetAt J A' x s' := by
  obtain ⟨U, hU, hyU, hsd, hsx, hsec, V, hV, hVs⟩ := hs
  set F : (Fin d → ℂ) → Fin d → ℂ := fun w => A' *ᵥ s w with hFdef
  have hFa := analyticOnNhd_of_differentiableOn hU (differentiableOn_mulVec A' hsd)
  set G : Set (Fin d → ℂ) := U ∩ (fun w => (ReciprocityTheory.AnForm.A.jacC F w).det) ⁻¹' {0}ᶜ with hGdef
  have hG : IsOpen G := (analyticOnNhd_det_jacC hU (differentiableOn_mulVec A' hsd)).continuousOn
    |>.isOpen_inter_preimage hU isOpen_compl_singleton
  have hinj : ∀ w, (ReciprocityTheory.AnForm.A.jacC F w).det ≠ 0 → Function.Injective (fderiv ℂ F w) :=
    fun w hw => (injective_iff_det_ne_zero _).2 (by rwa [← ReciprocityTheory.AnForm.A.det_jacC])
  have hequiv : ∀ w ∈ G, ∃ e : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ),
      HasStrictFDerivAt F (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) w := by
    intro w hw
    refine ⟨(LinearEquiv.ofInjectiveEndo _ (hinj w hw.2)).toContinuousLinearEquiv, ?_⟩
    exact (hFa w hw.1).hasStrictFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  obtain ⟨e, he⟩ := hequiv _ ⟨hyU, hdet⟩
  set φ := he.toOpenPartialHomeomorph F with hφdef
  have hφ : ∀ w, φ w = F w := fun w => by rw [hφdef, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
  have hysrc : A *ᵥ x ∈ φ.source := he.mem_toOpenPartialHomeomorph_source
  have hFx : F (A *ᵥ x) = A' *ᵥ x := by simp only [hFdef, hsx]
  have hsym : φ.symm (A' *ᵥ x) = A *ᵥ x := by rw [← hFx, ← hφ, φ.left_inv hysrc]
  refine ⟨s ∘ φ.symm, φ.target ∩ φ.symm ⁻¹' G, φ.isOpen_inter_preimage_symm hG,
    ⟨by rw [← hFx, ← hφ]; exact φ.map_source hysrc, by rw [Set.mem_preimage, hsym]; exact ⟨hyU, hdet⟩⟩,
    ?_, by simp only [Function.comp_apply, hsym, hsx], fun z hz => ⟨?_, (hsec _ hz.2.1).2⟩, ?_⟩
  · intro z ⟨hzT, hzG⟩
    obtain ⟨e', he'⟩ := hequiv _ hzG
    have hsymd : HasFDerivAt φ.symm _ z :=
      φ.hasFDerivAt_symm hzT (f' := e') (by
        have : (φ : (Fin d → ℂ) → Fin d → ℂ) = F := funext hφ
        rw [this]; exact he'.hasFDerivAt)
    exact ((hsd.differentiableAt (hU.mem_nhds hzG.1)).comp z
      hsymd.differentiableAt).differentiableWithinAt
  · show F (φ.symm z) = z
    rw [← hφ, φ.right_inv hz.1]
  · refine ⟨V ∩ (fun z => A *ᵥ z) ⁻¹' (φ.source ∩ U), inter_mem hV
      (((φ.open_source.inter hU).preimage (by fun_prop)).mem_nhds ⟨hysrc, hyU⟩), ?_⟩
    rintro x'' ⟨hx''Z, hx''V, hx''src, hx''U⟩ -
    have hx'' : x'' = s (A *ᵥ x'') := hVs x'' ⟨hx''Z, hx''V⟩ hx''U
    have hA' : A' *ᵥ x'' = φ (A *ᵥ x'') := by rw [hφ, hFdef]; exact congrArg _ hx''
    rw [Function.comp_apply, hA', φ.left_inv hx''src]
    exact hx''

theorem exists_det_ne_zero (h₁ : IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.Statement)
    (h₂ : IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.Statement) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A A' : Matrix (Fin d) (Fin n) ℂ} (hJ : J.IsPrime) (hA' : IsFiniteProjection J A')
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s)
    {W₀ : Set (Fin d → ℂ)} (hW₀ : IsOpen W₀) (hxW₀ : A *ᵥ x ∈ W₀) :
    ∃ w ∈ W₀, (ReciprocityTheory.AnForm.A.jacC (fun w => A' *ᵥ s w) w).det ≠ 0 := by
  obtain ⟨U, hU, hyU, hsd, hsx, hsec, V, hV, hVs⟩ := hs
  set F : (Fin d → ℂ) → Fin d → ℂ := fun w => A' *ᵥ s w with hFdef
  by_contra hall
  push Not at hall
  have hcrit : F '' (W₀ ∩ U) ⊆ F '' {w | w ∈ U ∧ ¬ Function.Injective (fderiv ℂ F w)} :=
    Set.image_mono fun w hw => ⟨hw.2, fun hinj => (injective_iff_det_ne_zero _).1 hinj
      (by rw [← ReciprocityTheory.AnForm.A.det_jacC]; exact hall w hw.1)⟩
  have hnull := measure_mono_null hcrit (h₂ d d U F hU (differentiableOn_mulVec A' hsd))
  have hxZ : x ∈ zeroSet J := hsx ▸ (hsec _ hyU).2
  have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
  have hnhds := h₁ n d J (linPoly A') hJ hA'.injective hA'.finite x hxZ
    (V ∩ (fun z => A *ᵥ z) ⁻¹' (W₀ ∩ U))
    (inter_mem hV (((hW₀.inter hU).preimage hAc).mem_nhds ⟨hxW₀, hyU⟩))
  have hev : ∀ z : Fin n → ℂ, (fun i => eval z (linPoly A' i)) = A' *ᵥ z := fun z => by
    ext i
    simp [linPoly, Matrix.mulVec, dotProduct]
  simp only [hev] at hnhds
  have hsub : (fun z => A' *ᵥ z) '' (IndefiniteRowSideFullHecke.ComplexSets.zeroLocus J ∩
      (V ∩ (fun z => A *ᵥ z) ⁻¹' (W₀ ∩ U))) ⊆ F '' (W₀ ∩ U) := by
    rintro _ ⟨z, ⟨hzZ, hzV, hzW⟩, rfl⟩
    refine ⟨A *ᵥ z, hzW, ?_⟩
    simp only [hFdef]
    rw [← hVs z ⟨hzZ, hzV⟩ hzW.2]
  have hpos := Measure.measure_pos_of_mem_nhds (μ := μH[(Module.finrank ℝ (Fin d → ℂ) : ℝ)])
    (Filter.mem_of_superset hnhds hsub)
  rw [finrank_real_fin_complex] at hpos
  exact hpos.ne' hnull

end SheetOnlyNull

theorem SheetOnlyNull.proof (h₁ : IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.Statement)
    (h₂ : IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.Statement) : SheetOnlyNull.Statement := by
  intro n d J A A' hJ _ _ hA'
  set B := {x | x ∈ zeroSet J ∧ (∃ s, IsSheetAt J A x s) ∧ ¬ ∃ s', IsSheetAt J A' x s'} with hBdef
  choose σ U W hU hW hσd hWsh hxW using
    fun x : Fin n → ℂ => SheetOnlyNull.exists_sheet_nhds (J := J) (A := A) x
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  have hpiece : ∀ i, volume ((fun x => A *ᵥ x) '' (B ∩ W i)) = 0 := by
    intro i
    apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
    rintro _ ⟨x, ⟨hxB, hxWi⟩, rfl⟩
    obtain ⟨hAx, hsh⟩ := hWsh i x ⟨hxB.1, hxWi⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hU i) _ hAx
    refine ⟨Metric.ball (A *ᵥ x) r, Metric.isOpen_ball, Metric.mem_ball_self hr,
      (convex_ball _ r).isPreconnected,
      fun w => (ReciprocityTheory.AnForm.A.jacC (fun v => A' *ᵥ σ i v) w).det,
      (SheetOnlyNull.analyticOnNhd_det_jacC (hU i)
        (SheetOnlyNull.differentiableOn_mulVec A' (hσd i))).mono hball,
      SheetOnlyNull.exists_det_ne_zero h₁ h₂ hJ hA' hsh Metric.isOpen_ball (Metric.mem_ball_self hr),
      ?_⟩
    rintro _ ⟨⟨x'', ⟨hx''B, hx''W⟩, rfl⟩, -⟩
    by_contra hne
    exact hx''B.2.2 (SheetOnlyNull.exists_sheet_of_det_ne_zero (hWsh i x'' ⟨hx''B.1, hx''W⟩).2 hne)
  refine measure_mono_null ?_ ((measure_biUnion_null_iff hTc).2 fun i _ => hpiece i)
  rintro _ ⟨x, hxB, rfl⟩
  have hx : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x hxB.2.1⟩
  obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 hx
  exact Set.mem_biUnion hiT ⟨x, ⟨hxB, hxi⟩, rfl⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.LogIntegrableOnOfLogIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Filter

noncomputable section

variable {n d : ℕ}

theorem lift_eval_comp_projHom (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    {x : Fin n → ℂ} (hx : x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J) :
    (Ideal.Quotient.lift J (MvPolynomial.eval x) fun q hq => hx q hq).comp
        (GroundTheory.Heights₂.Heights.ComplexSets.projHom J A).toRingHom =
      MvPolynomial.eval (A.mulVec x) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [GroundTheory.Heights₂.Heights.ComplexSets.projHom, GroundTheory.Heights₂.Heights.ComplexSets.pullback]
  · intro i
    simp [GroundTheory.Heights₂.Heights.ComplexSets.projHom, GroundTheory.Heights₂.Heights.ComplexSets.pullback,
      GroundTheory.Heights₂.Heights.ComplexSets.linPoly, Matrix.mulVec, dotProduct]

theorem fibre_finite {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A) (y : Fin d → ℂ) :
    (GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y).Finite := by
  classical
  have hint : ∀ j : Fin n, (GroundTheory.Heights₂.Heights.ComplexSets.projHom J A).toRingHom.IsIntegralElem
      (Ideal.Quotient.mk J (X j)) := fun j => hA.finite.to_isIntegral _
  choose p hpm hp using hint
  refine (Set.Finite.pi (t := fun j => {z : ℂ | ((p j).map (MvPolynomial.eval y)).IsRoot z})
    fun j => Polynomial.finite_setOfPred_isRoot ((hpm j).map _).ne_zero).subset ?_
  rintro x ⟨hx, hxy⟩ j -
  have h := congrArg (Ideal.Quotient.lift J (MvPolynomial.eval x) fun q hq => hx q hq) (hp j)
  rw [Polynomial.hom_eval₂, lift_eval_comp_projHom J A hx, hxy, map_zero] at h
  simpa [Polynomial.IsRoot, Polynomial.eval_map] using h

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

def SliceLength.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes →
      ∃ U : Set (Fin n → ℂ), IsOpen U ∧ zeroSet W ⊆ closure (zeroSet W ∩ U) ∧
        ∀ q ∈ zeroSet W ∩ U, Dense {L : Matrix (Fin d) (Fin n) ℂ |
          IsRadicalAt (sliceIdeal J L q) q ∧
            localMult (J ⊔ Ideal.span {linForm u}) W =
              localMult (sliceIdeal J L q ⊔ Ideal.span {linForm u}) (RingHom.ker (eval q))}

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongLimitAtBranches
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def LelongLimitAtBranches.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u q : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → VarBranch J (d + 1) q) (ord : Fin m → ℕ) (π : Matrix (Fin d) (Fin n) ℂ)
    (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes → q ∈ zeroSet W →
    (∀ i, SmoothNear (zeroSet J) (φ i)) →
    (∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → x ∈ zeroSet W) →
    (∃ N ∈ 𝓝 q, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) →
    (∃ N ∈ 𝓝 q, ∀ b, zeroSet W ∩ N ⊆ (γ b).slice) →
    (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) →
    (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) →
    (∀ b, Function.Bijective
      (fderiv ℂ (fun τ => vecCons (τ 0) (π *ᵥ (γ b).toFun τ)) (0 : Fin (d + 1) → ℂ))) →
      ∃ N ∈ 𝓝 q, ∀ f : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ N →
        Tendsto (fun ε => varInt J (d + 1) f (vecCons (logReg u ε) φ)) (𝓝[>] 0)
          (𝓝 (((∑ b, ord b : ℕ) : ℝ) * varInt W d f φ))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegLelongMono
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def euclBall {n : ℕ} (x : Fin n → ℂ) (ρ : ℝ) : Set (Fin n → ℂ) :=
  {y | Real.sqrt (euclPot (y - x)) < ρ}

theorem mem_euclBall_iff {n : ℕ} (x y : Fin n → ℂ) (ρ : ℝ) :
    y ∈ euclBall x ρ ↔ dist (WithLp.toLp 2 y : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 x) < ρ := by
  rw [EuclideanSpace.dist_eq]
  simp [euclBall, euclPot, dist_eq_norm]

theorem mem_euclBall_self {n : ℕ} (x : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) : x ∈ euclBall x ρ := by
  simp [euclBall, euclPot, hρ]

def RegLelongMono.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (u : Fin n → ℂ) (ε : ℝ) (x : Fin n → ℂ) (r s : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    0 < ε → 0 < r → r ≤ s →
      s ^ (2 * d) * ∫ y, chartDens J A ((euclBall x r).indicator fun _ => 1)
          (vecCons (logReg u ε) fun _ => euclPot) y ≤
        r ^ (2 * d) * ∫ y, chartDens J A ((euclBall x s).indicator fun _ => 1)
          (vecCons (logReg u ε) fun _ => euclPot) y

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVanishNearPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

theorem VanishNearPoint.proof (hOpen : FiniteMapOpen.Statement) : VanishNearPoint.Statement := by
  classical
  intro n J f x hJ hx hf
  by_contra hfJ
  have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ.ne_top
  obtain ⟨d, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ (MvPolynomial (Fin n) ℂ ⧸ J)
  choose p hp using fun i => Ideal.Quotient.mk_surjective (g (X i))
  have hg : g = (Ideal.Quotient.mkₐ ℂ J).comp (aeval p) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [hp]
  subst hg
  let _ := ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)).toRingHom.toAlgebra
  have hint : IsIntegral (MvPolynomial (Fin d) ℂ) (Ideal.Quotient.mk J f) :=
    RingHom.IsIntegral.of_finite hfin _
  have hf0 : Ideal.Quotient.mk J f ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨h, hh, hh0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ideal.comap_ne_bot_of_integral_mem hf0 (Ideal.mem_span_singleton_self _) hint)
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hh
  obtain ⟨a, ha⟩ := hh
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hJmem : aeval p h - q * f ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, sub_eq_zero]
    exact ha.symm

  have hval : ∀ z ∈ zeroLocus J, eval (fun i => eval z (p i)) h = eval z q * eval z f := by
    intro z hz
    have h1 := hz _ hJmem
    rw [map_sub, map_mul, sub_eq_zero] at h1
    rw [← h1]
    have h2 := DFunLike.congr_fun (MvPolynomial.comp_aeval (R := ℂ) (aeval z : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) (f := p)) h
    rw [AlgHom.comp_apply] at h2
    exact h2.symm
  have hV := hOpen n d J p hJ hinj hfin x hx _ hf
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  apply hh0
  refine MvPolynomial.funext_set (fun i => Metric.ball (eval x (p i)) ε)
    (fun i => infinite_of_mem_nhds _ (Metric.ball_mem_nhds _ hε)) fun w hw => ?_
  rw [← ball_pi _ hε] at hw
  obtain ⟨z, ⟨hz, hzU⟩, rfl⟩ := hball hw
  rw [hval z hz, hzU hz, mul_zero, map_zero]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalLocallyIrreducible
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

theorem zeroSetIn_subset_closure_diff (hvan : VanishNearPoint.Statement) {σ : Type} [Fintype σ]
    (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial σ ℂ) (hI : I.IsPrime) (hh : h ∉ I) :
    zeroSetIn I ⊆ closure (zeroSetIn I \ {z | eval z h = 0}) := by
  intro z hz
  rw [mem_closure_iff_nhds]
  intro t ht
  by_contra hne
  set e := Fintype.equivFin σ with he
  set J : Ideal (MvPolynomial (Fin (Fintype.card σ)) ℂ) := I.comap (rename e.symm) with hJ
  have hre : ∀ q : MvPolynomial (Fin (Fintype.card σ)) ℂ, rename e (rename e.symm q) = q := by
    intro q
    rw [rename_rename, show (⇑e ∘ ⇑e.symm) = id from funext e.apply_symm_apply, rename_id_apply]
  have hre' : ∀ p : MvPolynomial σ ℂ, rename e.symm (rename e p) = p := by
    intro p
    rw [rename_rename, show (⇑e.symm ∘ ⇑e) = id from funext e.symm_apply_apply, rename_id_apply]
  have hJp : J.IsPrime := Ideal.comap_isPrime _ _
  have hmemJ : ∀ y : Fin (Fintype.card σ) → ℂ, y ∘ e ∈ zeroSetIn I → y ∈ zeroLocus J := by
    intro y hy q hq
    rw [← hre q, eval_rename]
    exact hy _ hq
  have hJZ : ∀ y : Fin (Fintype.card σ) → ℂ, y ∈ zeroLocus J → y ∘ e ∈ zeroSetIn I := by
    intro y hy p hp
    have := hy (rename e p) (by rw [hJ, Ideal.mem_comap, hre']; exact hp)
    rwa [eval_rename] at this
  have hx : z ∘ e.symm ∈ zeroLocus J := hmemJ _ (by
    rw [Function.comp_assoc, show (⇑e.symm ∘ ⇑e) = id from funext e.symm_apply_apply]
    exact hz)
  have hcont : Continuous fun y : Fin (Fintype.card σ) → ℂ => y ∘ e :=
    continuous_pi fun i => continuous_apply _
  have hlim : Filter.Tendsto (fun y : Fin (Fintype.card σ) → ℂ => y ∘ e) (𝓝 (z ∘ e.symm)) (𝓝 z) := by
    have := hcont.tendsto (z ∘ e.symm)
    rwa [Function.comp_assoc, show (⇑e.symm ∘ ⇑e) = id from funext e.symm_apply_apply,
      Function.comp_id] at this
  have hev : ∀ᶠ y in 𝓝 (z ∘ e.symm), y ∈ zeroLocus J → eval y (rename e h) = 0 := by
    filter_upwards [hlim ht] with y hyt hyJ
    rw [eval_rename]
    by_contra hne'
    exact hne ⟨y ∘ e, hyt, hJZ y hyJ, hne'⟩
  have hmem := hvan _ J (rename e h) _ hJp hx hev
  apply hh
  rw [hJ, Ideal.mem_comap, hre'] at hmem
  exact hmem

theorem NormalLocallyIrreducible.proof (hvan : VanishNearPoint.Statement)
    (hcon : NormalComplementConnected.Statement) : NormalLocallyIrreducible.Statement := by
  intro σ _ I h w hI hnorm hh hw U hU
  obtain ⟨B, hBo, hwB, hBU, hpre⟩ := hcon σ I h w hI hnorm hh hw U hU
  refine ⟨B, hBo, hwB, hBU, hpre, ?_⟩
  rintro z ⟨hzZ, hzB⟩
  have h1 : z ∈ B ∩ closure (zeroSetIn I \ {z | eval z h = 0}) :=
    ⟨hzB, zeroSetIn_subset_closure_diff hvan I h hI hh hzZ⟩
  refine closure_mono ?_ (hBo.inter_closure h1)
  rintro y ⟨hyB, hyZ, hyh⟩
  exact ⟨⟨hyZ, hyB⟩, hyh⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongLimitOffZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def LelongLimitOffZero.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (f : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    ContDiff ℝ ∞ f → HasCompactSupport f → (∀ i, SmoothNear (zeroSet J) (φ i)) →
    Disjoint (tsupport f) (zeroSet J ∩ {x | linEval u x = 0}) →
      Tendsto (fun ε => varInt J (d + 1) f (vecCons (logReg u ε) φ)) (𝓝[>] 0) (𝓝 0)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveBranchLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets Filter Topology

noncomputable section

def CurveBranchLength.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (u q : Fin n → ℂ) (m : ℕ)
    (c : Fin m → VarBranch I 1 q) (ord : Fin m → ℕ),
    IsRadicalAt I q →
    (∃ N ∈ 𝓝 q, zeroSet I ∩ N ⊆ ⋃ b, (c b).image) →
    (∀ b b', b ≠ b' → (c b).image ∩ (c b').image ⊆ {x | linEval u x = 0}) →
    (∀ b, VanishesToOrder (fun t => linEval u ((c b).toFun t)) (c b).radius (ord b)) →
      localMult (I ⊔ Ideal.span {linForm u}) (RingHom.ker (eval q)) = ∑ b, ord b

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongLimit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def LelongLimit.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (f : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    ContDiff ℝ ∞ f → HasCompactSupport f → (∀ i, SmoothNear (zeroSet J) (φ i)) →
      Tendsto (fun ε => varInt J (d + 1) f (vecCons (logReg u ε) φ)) (𝓝[>] 0)
        (𝓝 (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
            (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
          (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d f φ))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegBallMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def RegBallMass.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (u : Fin n → ℂ) (K : Set (Fin n → ℂ)),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    linForm u ∉ J → IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ x ∈ K, ∀ r ∈ Set.Ioc (0 : ℝ) 1,
        Integrable (chartDens J A ((Metric.ball x r).indicator fun _ => 1)
            (vecCons (logReg u ε) fun _ => euclPot)) ∧
          ∫ y, chartDens J A ((Metric.ball x r).indicator fun _ => 1)
            (vecCons (logReg u ε) fun _ => euclPot) y ≤ C * r ^ (2 * d)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBranches
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets Filter Topology

noncomputable section

def SliceBranches.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u p : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → VarBranch J (d + 1) p) (ord : Fin m → ℕ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes → p ∈ zeroSet W →
    (∃ N ∈ 𝓝 p, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) →
    (∃ N ∈ 𝓝 p, ∀ b, zeroSet W ∩ N ⊆ (γ b).slice) →
    (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) →
    (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) →
    ∀ (U : Set (Fin n → ℂ)) (Λ : (Fin n → ℂ) → Set (Matrix (Fin d) (Fin n) ℂ)),
      IsOpen U → zeroSet W ⊆ closure (zeroSet W ∩ U) → (∀ q ∈ zeroSet W ∩ U, Dense (Λ q)) →
        ∃ q ∈ zeroSet W ∩ U, ∃ L ∈ Λ q, ∃ c : Fin m → VarBranch (sliceIdeal J L q) 1 q,
          (∃ N ∈ 𝓝 q, zeroSet (sliceIdeal J L q) ∩ N ⊆ ⋃ b, (c b).image) ∧
          (∀ b b', b ≠ b' → (c b).image ∩ (c b').image ⊆ {x | linEval u x = 0}) ∧
          ∀ b, VanishesToOrder (fun t => linEval u ((c b).toFun t)) (c b).radius (ord b)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHessCCompPluri
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm Filter Topology

noncomputable section

theorem HessCCompPluri.fderiv_fderiv_comp_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → ℝ} {L : E → ℝ} {z : E} (hF : ContDiffAt ℝ 2 F (L z)) (hL : ContDiffAt ℝ 2 L z)
    (v u : E) :
    fderiv ℝ (fderiv ℝ (fun w => F (L w))) z v u =
      deriv (deriv F) (L z) * (fderiv ℝ L z v * fderiv ℝ L z u) +
        deriv F (L z) * fderiv ℝ (fderiv ℝ L) z v u := by
  have hL2 : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 L w := hL.eventually (by simp)
  have hF2 : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 F (L w) :=
    hL.continuousAt.tendsto.eventually (hF.eventually (by simp))
  have heq : fderiv ℝ (fun w => F (L w)) =ᶠ[𝓝 z] fun w => deriv F (L w) • fderiv ℝ L w := by
    filter_upwards [hL2, hF2] with w hw hFw
    exact ((hFw.differentiableAt (by norm_num)).hasDerivAt.comp_hasFDerivAt w
      (hw.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hdF : DifferentiableAt ℝ (deriv F) (L z) := by
    have h1 := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    exact h1.clm_apply (differentiableAt_const (1 : ℝ))
  have hdL : DifferentiableAt ℝ (fderiv ℝ L) z :=
    (hL.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : HasFDerivAt (fun w => deriv F (L w)) (deriv (deriv F) (L z) • fderiv ℝ L z) z :=
    hdF.hasDerivAt.comp_hasFDerivAt z (hL.differentiableAt (by norm_num)).hasFDerivAt
  have hs : HasFDerivAt (fun w => deriv F (L w) • fderiv ℝ L w)
      (deriv F (L z) • fderiv ℝ (fderiv ℝ L) z +
        (deriv (deriv F) (L z) • fderiv ℝ L z).smulRight (fderiv ℝ L z)) z :=
    hc.smul hdL.hasFDerivAt
  rw [heq.fderiv_eq, hs.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

theorem HessCCompPluri.proof : HessCCompPluri.Statement := by
  intro D F L z hF hL h0
  have hQ : ContDiffAt ℝ 2 (fun t : ℝ => t ^ 2 / 2) (L z) :=
    ((contDiff_id.pow 2).div_const 2).contDiffAt
  have hd1 : deriv (fun t : ℝ => t ^ 2 / 2) = fun t => t := by
    funext t
    rw [((hasDerivAt_pow 2 t).div_const 2).deriv]
    norm_num
  have key := HessCCompPluri.fderiv_fderiv_comp_apply hF hL
  have keyQ := HessCCompPluri.fderiv_fderiv_comp_apply hQ hL
  simp only [hd1, deriv_id'', one_mul] at keyQ
  ext i j
  have hij := congrFun (congrFun h0 i) j
  simp only [hessC, Matrix.zero_apply, Matrix.smul_apply, smul_eq_mul] at hij ⊢
  simp only [key, keyQ]
  push_cast at hij ⊢
  linear_combination (((deriv F (L z) : ℝ) : ℂ) - ((deriv (deriv F) (L z) : ℝ) : ℂ) * ((L z : ℝ) : ℂ)) * hij

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMaDensLeibniz
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology

noncomputable section

namespace MaDensLeibniz

variable {D : ℕ}

theorem exists_open_contDiffOn (f g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hf : ContDiffAt ℝ 2 f z)
    (hg : ContDiffAt ℝ 2 g z) :
    ∃ U : Set (Fin D → ℂ), IsOpen U ∧ z ∈ U ∧ ContDiffOn ℝ 2 f U ∧ ContDiffOn ℝ 2 g U := by
  obtain ⟨U, hP, hU, hzU⟩ :=
    eventually_nhds_iff.mp ((hf.eventually (by simp)).and (hg.eventually (by simp)))
  exact ⟨U, hU, hzU, fun y hy => (hP y hy).1.contDiffWithinAt,
    fun y hy => (hP y hy).2.contDiffWithinAt⟩

theorem contDiffAt_cplx {f : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (hf : ContDiffAt ℝ 2 f z) :
    ContDiffAt ℝ 2 (cplx f) z := by
  have h : cplx f = fun y => Complex.ofRealCLM (f y) := by funext y; simp [cplx]
  rw [h]
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp z hf

theorem dzb_cplx_mul (k : Fin D) (f g : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    dzb k (cplx fun x => f x * g x) y = cplx f y * dzb k (cplx g) y + cplx g y * dzb k (cplx f) y := by
  rw [dzb_cplx_eq_star, dz_cplx_mul k f g y hf hg, dzb_cplx_eq_star, dzb_cplx_eq_star]
  simp [cplx, star_add]

theorem dzb_cplx_sq_half (k : Fin D) (f : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hf : DifferentiableAt ℝ f y) :
    dzb k (cplx fun x => f x ^ 2 / 2) y = cplx f y * dzb k (cplx f) y := by
  rw [dzb_cplx, dzb_cplx, fderiv_sq_half f y hf]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, cplx]
  push_cast
  ring

theorem hessC_mul (f g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hf : ContDiffAt ℝ 2 f z)
    (hg : ContDiffAt ℝ 2 g z) :
    hessC (fun y => f y * g y) z =
      (f z : ℂ) • hessC g z + (g z : ℂ) • hessC f z + gradMat f g z + gradMat g f z := by
  obtain ⟨U, hU, hzU, hfU, hgU⟩ := exists_open_contDiffOn f g z hf hg
  ext j k
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hessCDz_thm D _ U hU (hfU.mul hgU) z hzU j k, hessCDz_thm D f U hU hfU z hzU j k,
    hessCDz_thm D g U hU hgU z hzU j k]
  have hev : dzb k (cplx fun y => f y * g y) =ᶠ[𝓝 z]
      fun y => cplx f y * dzb k (cplx g) y + cplx g y * dzb k (cplx f) y := by
    filter_upwards [hU.mem_nhds hzU] with y hy
    exact dzb_cplx_mul k f g y ((hfU.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
      ((hgU.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
  have hF := (contDiffAt_cplx hf).differentiableAt (n := 2) (by norm_num)
  have hG := (contDiffAt_cplx hg).differentiableAt (n := 2) (by norm_num)
  have hF' := differentiableAt_dzb (j := k) (contDiffAt_cplx hf)
  have hG' := differentiableAt_dzb (j := k) (contDiffAt_cplx hg)
  rw [dz_congr hev, dz_add (hF.fun_mul hG') (hG.fun_mul hF'), dz_mul hF hG', dz_mul hG hF']
  simp only [gradMat, cplx]
  ring

theorem hessC_sq_half (f : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hf : ContDiffAt ℝ 2 f z) :
    hessC (fun y => f y ^ 2 / 2) z = (f z : ℂ) • hessC f z + gradMat f f z := by
  obtain ⟨U, hU, hzU, hfU, -⟩ := exists_open_contDiffOn f f z hf hf
  ext j k
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hessCDz_thm D _ U hU ((hfU.pow 2).div_const 2) z hzU j k, hessCDz_thm D f U hU hfU z hzU j k]
  have hev : dzb k (cplx fun y => f y ^ 2 / 2) =ᶠ[𝓝 z] fun y => cplx f y * dzb k (cplx f) y := by
    filter_upwards [hU.mem_nhds hzU] with y hy
    exact dzb_cplx_sq_half k f y ((hfU.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
  have hF := (contDiffAt_cplx hf).differentiableAt (n := 2) (by norm_num)
  have hF' := differentiableAt_dzb (j := k) (contDiffAt_cplx hf)
  rw [dz_congr hev, dz_mul hF hF']
  simp only [gradMat, cplx]
  ring

theorem mdisc_cons_add {n : ℕ} (A A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons (A + A') B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      mdisc (Fin.cons A B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) +
        mdisc (Fin.cons A' B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  simpa using mdisc_cons_smul_add 1 1 A A' B

theorem proof : MaDensLeibniz.Statement := by
  intro D φ f g z hf hg
  constructor
  · rw [maDens_cons_eq, maDens_cons_eq, maDens_cons_eq, hessC_mul f g z hf hg]
    unfold gradDens
    rw [mdisc_cons_add, mdisc_cons_add, mdisc_cons_smul_add]
    simp only [Complex.add_re, Complex.re_ofReal_mul]
    ring
  · rw [maDens_cons_eq, maDens_cons_eq, hessC_sq_half f z hf]
    unfold gradDens
    rw [mdisc_cons_add, mdisc_cons_smul_fst]
    simp only [Complex.add_re, Complex.re_ofReal_mul]
    ring

end MaDensLeibniz

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffTube
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def CutOffTube.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    P ≠ 0 → (∀ i, SmoothNear (zeroSet J) (φ i)) → Integrable (tubeDens J A P R φ)

end

end GroundTheory.Heights₂.Heights
end
