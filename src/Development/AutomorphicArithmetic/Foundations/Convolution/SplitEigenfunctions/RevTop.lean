module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.WtNonneg
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.MeanLaws
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.RatGl
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.DetCentralSection
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.Imports
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.CuspZero
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.MomKill
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.Fub3
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.SwapInt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.FormBd
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

private theorem dM_fin (t : (A ℚ)ˣ) (ht : (t : A ℚ).1 = 1) :
    finGL ℚ 2 (Matrix.GeneralLinearGroup.map (pFin ℚ) (dM t)) = dM t := by
  have h := TR.infGL_mul_finGL (dM t)
  have h1 : Matrix.GeneralLinearGroup.map (TR.pInf ℚ) (dM t) = 1 := by
    have ht' : TR.pInf ℚ (t : A ℚ) = 1 := by
      change (TR.infEq ℚ).symm (t : A ℚ).1 = 1
      rw [ht]; exact map_one _
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ht']
  rw [h1, map_one, one_mul] at h
  exact h

open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.formBd :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.FormBd := by
  intro π hπ f hf
  have hL := (UpperTheory.ConvolutionTheory.R2.Pp.cuspZero ℚ π f hf).1
  refine ⟨⟨hL.1, hL.2, ?_, fun s x => hπ f hf s x⟩, fun t ht => ?_⟩
  · obtain ⟨φ, hφ⟩ := LinearMap.mem_range.mp (Fb.mem_range_ofCusp.2 (π.cusp f hf))
    obtain ⟨B₀, hB₀⟩ := CuspidalSpectrum.exists_norm_le_of_mem_cuspForms φ.2
    subst hφ
    refine ⟨B₀, fun x => ?_⟩
    have h2 : (centralSection ℚ 2 (detModule ℚ 2 x))⁻¹ * x ∈ normOneGL (K := ℚ) (n := 2) := by
      rw [mem_normOneGL_iff_detModule, map_mul, map_inv, detModule_centralSection two_pos, inv_mul_cancel]
    have h3 := hπ _ hf (detModule ℚ 2 x) ((centralSection ℚ 2 (detModule ℚ 2 x))⁻¹ * x)
    rw [mul_inv_cancel_left] at h3
    rw [h3]
    exact hB₀ _ h2
  · have h := π.stable (.fin (Matrix.GeneralLinearGroup.map (pFin ℚ) (dM t))) f hf
    refine ⟨_, h, fun x => ?_⟩
    change f.1 (x * finGL ℚ 2 (Matrix.GeneralLinearGroup.map (pFin ℚ) (dM t))) = _
    rw [dM_fin t ht.1]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Dens
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical
open UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.dens :
    Dens := by
  intro M u hu hne
  obtain ⟨F, hF, he, hc⟩ := Cp.ext u hu
  have h1 : (1 : (A ℚ)ˣ) ∈ UU := ⟨rfl, fun v => by
    change Valued.v (1 : v.adicCompletion ℚ) = 1
    exact map_one _⟩
  have hF0 : F ≠ 0 := fun h => hne (funext fun g => by rw [← he g 1 h1, h]; rfl)
  obtain ⟨π, hπ, f, hf, hint⟩ := pairL Measure.haar F hF hF0 hc
  obtain ⟨hb, ht⟩ := formBd π hπ f hf
  refine ⟨π, hπ, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨B, hB⟩ := hb.bdd
  obtain ⟨B', hB'⟩ := hF.bdd
  refine hint (fibre M Measure.haar (fun x => f.1 x * F x) ⟨hb.cont.mul hF.cont, fun γ g => by rw [hb.left, hF.left],
    ⟨B * B', fun x => by rw [norm_mul]; exact mul_le_mul (hB x) (hB' x) (norm_nonneg _) ((norm_nonneg _).trans (hB x))⟩,
    fun s x => by rw [hb.cen, hF.cen]⟩ fun t htU => ?_)
  obtain ⟨f', hf', e⟩ := ht t htU
  simpa only [e, he _ t htU] using hcon f' hf'
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CoefPer
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical
open UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.coefPer :
    DecE → Maj → OrbS → MomKill → OrbFn → CoefPer := by
  intro _ _ _ momKill orbFn E _ _ _ D W M N P φ hφ h0 h
  haveI := N.haar
  obtain ⟨j, -, hj, -⟩ := reps E D
  obtain ⟨hp, hw, hi⟩ := yInt E D W M N P φ hφ
  have hδ : D.δ < 0 := by simpa using D.neg (Rat.castHom ℝ)
  haveI : SFinite (mY D.δ N) := by unfold mY; infer_instance
  have hU := perCont E D W M N P φ hφ
  set U : G1 E → ℂ := fun h : G1 E => UPer D M fun x => φ.1 (x * gl h) with hUd
  have key : ∀ c : G1 E → ℂ, Continuous c → HasCompactSupport c → ∫ y, c y * U y ∂N.μ = 0 := fun c hc hs => by
    obtain ⟨Ψ, hΨ, hΨ'⟩ := orbFn E D M j hj c hc hs
    obtain ⟨h1, h2⟩ := zAll E D W M N P φ hφ j hj c hc hs Ψ hΨ hΨ'
    rw [← h2]
    exact momKill D.δ hδ _ (mY D.δ N) (pY D) _ hp hw hi (fun ph hph => (yEq E D W M N P φ hφ ph hph).symm.trans (h0 ph hph)) Ψ hΨ h1
  by_contra hne
  obtain ⟨χ, h1, -, hs, h01⟩ := exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := h)) isClosed_empty
    (Set.disjoint_empty _)
  have h2 := key (fun y => (χ y : ℂ) * starRingEnd ℂ (U y))
    ((Complex.continuous_ofReal.comp χ.continuous).mul (Complex.continuous_conj.comp hU))
    ((hs.comp_left (g := Complex.ofReal) Complex.ofReal_zero).mul_right)
  have e : ∀ y, (χ y : ℂ) * starRingEnd ℂ (U y) * U y = ((χ y * ‖U y‖ ^ 2 : ℝ) : ℂ) := fun y => by
    rw [mul_assoc, Complex.conj_mul']
    push_cast
    rfl
  simp only [e, integral_complex_ofReal, Complex.ofReal_eq_zero] at h2
  refine (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := N.μ) (x := h) (χ.continuous.mul (hU.norm.pow 2))
    hs.mul_right (fun y => mul_nonneg (h01 y).1 (sq_nonneg ‖U y‖)) ?_).ne' h2
  have : χ h = 1 := h1 rfl
  change χ h * ‖U h‖ ^ 2 ≠ 0
  rw [this, one_mul]
  exact pow_ne_zero _ (norm_ne_zero_iff.2 hne)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThCont
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

private theorem om_L' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {D : Dat ℚ E} (W : Weil D)
    (g : G1 ℚ) (h : GL (Fin 2) (A E)) (hh : nu ℚ h = 1) (φ : S4 ℚ) :
    W.Om g (W.L h φ) = W.L h (W.Om g φ) := by
  have e := congrArg (fun T : Module.End ℂ (S4 ℚ) => T φ) (W.comm h g)
  simp only [Module.End.mul_apply, hh] at e
  rw [e, UpperTheory.ConvolutionTheory.R2.M.cD_one]

private theorem term_eq {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {D : Dat ℚ E} (W : Weil D)
    (g : G1 ℚ) (h : GL (Fin 2) (A E)) (hh : nu ℚ h = 1) (φ : S4 ℚ) (v : V4 ℚ) :
    (W.Om g (W.L h φ)).1 v = (W.Om g φ).1 (D.act h⁻¹ v) := by
  rw [om_L' W g h hh, W.L_apply, hh, ab_one]
  simp

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.thCont :
    ThCont := by
  intro E _ _ _ D W _ _ _ ph hph S p₀ hp₀
  obtain ⟨ρ, hρ, hact, -, -, -⟩ := actCont ℚ E D
  obtain ⟨n, hn⟩ := wtSum ℚ
  obtain ⟨S₁, hS₁, hm₁⟩ := exists_compact_mem_nhds p₀.1
  obtain ⟨S₂, hS₂, hm₂⟩ := exists_compact_mem_nhds p₀.2
  obtain ⟨K, hK, hb⟩ := lDom ℚ E D W (G1 ℚ) S₁ (fun g => W.Om g ph)
    (omCpt ℚ E D W ph hph S₁ hS₁) S₂ hS₂
  obtain ⟨B, hB⟩ := hb n
  obtain ⟨C, hC⟩ := hn K hK 1 one_pos
  obtain ⟨hs, -⟩ := hC 1 (by rw [ab_one])
  have e : (fun ξ : Fin 4 → ℚ => wt K n (sc (1 : (A ℚ)ˣ) ξ)) = fun ξ => wt K n (rp ξ) := by
    funext ξ
    congr 1
    funext i
    change ((1 : (A ℚ)ˣ) : A ℚ) * rt (ξ i) = rt (ξ i)
    rw [Units.val_one, one_mul]
  rw [e] at hs
  have key : ContinuousOn (fun p : G1 ℚ × GL (Fin 2) (A E) => ThOn S (W.Om p.1 (W.L p.2 ph)).1)
      ((S₁ ×ˢ S₂) ∩ {p | nu ℚ p.2 = 1}) := by
    unfold ThOn
    refine continuousOn_tsum (u := fun ξ : S => B * wt K n (rp ξ.1)) (fun ξ => ?_)
      ((hs.mul_left B).subtype (fun x => x ∈ S)) fun ξ p hp => ?_
    · have hc : Continuous fun p : G1 ℚ × GL (Fin 2) (A E) =>
          (W.Om p.1 ph).1 ((ρ p.2⁻¹).val *ᵥ rp ξ.1) :=
        (W.cont ph).comp (continuous_fst.prodMk
          ((Units.continuous_val.comp (hρ.comp (continuous_inv.comp continuous_snd))).matrix_mulVec
            continuous_const))
      refine hc.continuousOn.congr fun p hp => ?_
      rw [term_eq W p.1 p.2 hp.2, hact]
    · have hnorm := hB (p.2, p.1) ⟨hp.1.2, hp.1.1⟩ (rp ξ.1)
      have e' : (W.Om p.1 (W.L p.2 ph)).1 (rp ξ.1) = (W.L p.2 (W.Om p.1 ph)).1 (rp ξ.1) := by
        rw [om_L' W p.1 p.2 hp.2]
      rw [e']
      exact hnorm
  have hT : (S₁ ×ˢ S₂) ∩ {p : G1 ℚ × GL (Fin 2) (A E) | nu ℚ p.2 = 1} ∈
      𝓝[{p : G1 ℚ × GL (Fin 2) (A E) | nu ℚ p.2 = 1}] p₀ :=
    inter_mem (mem_nhdsWithin_of_mem_nhds (prod_mem_nhds hm₁ hm₂)) self_mem_nhdsWithin
  exact (key p₀ ⟨⟨mem_of_mem_nhds hm₁, mem_of_mem_nhds hm₂⟩, hp₀⟩).mono_of_mem_nhdsWithin hT
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.DMOne
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

private theorem swap3 {X Y Z : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) (ρ : Measure Z) [SFinite μ] [SFinite ν] [SFinite ρ]
    (H : X → Y → Z → ℂ) (hH : Integrable (fun p : X × Y × Z => H p.1 p.2.1 p.2.2) (μ.prod (ν.prod ρ))) :
    ∫ x, ∫ y, ∫ z, H x y z ∂ρ ∂ν ∂μ = ∫ y, ∫ z, ∫ x, H x y z ∂μ ∂ρ ∂ν := by
  have h1 : ∀ᵐ x ∂μ, ∫ y, ∫ z, H x y z ∂ρ ∂ν = ∫ q, H x q.1 q.2 ∂(ν.prod ρ) := by
    filter_upwards [hH.prod_right_ae] with x hx
    exact (integral_prod _ hx).symm
  rw [integral_congr_ae h1, ← integral_prod (fun p : X × Y × Z => H p.1 p.2.1 p.2.2) hH,
    integral_prod_symm _ hH]
  exact integral_prod (fun q : Y × Z => ∫ x, H x q.1 q.2 ∂μ) hH.integral_prod_right

private theorem dM_one' : dM (1 : (A ℚ)ˣ) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dM]

end UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.fub :
    Maj → ThCont → Fub := by
  intro hMaj hTh E _ _ _ D W M N P ph hph φ hφ π f hf
  obtain ⟨-, hsc, hnu, hnug, -⟩ := szLaws E D
  obtain ⟨c, hc, hred⟩ := UpperTheory.ConvolutionTheory.R2.red ℚ
  have hKc : IsCompact (KK ℚ) := (UpperTheory.ConvolutionTheory.R2.Ff.iwa ℚ).1
  have hC' : IsCompact (gl (F := ℚ) '' KK ℚ) := hKc.image continuous_gl
  obtain ⟨hfc, hdec⟩ := UpperTheory.ConvolutionTheory.R2.decay ℚ π f hf
  obtain ⟨B₂, hB₂⟩ := hdec _ hC' c hc 2
  set C : Set (GL (Fin 2) (A E)) :=
    (fun u : IdeleGroup.normOneSubgroup E => sZ D (u : IdeleGroup E)) '' closure (normOneFundamentalDomain E) with hCdef
  have hCc : IsCompact C :=
    (isCompact_closure_normOneFundamentalDomain E).image (hsc.comp continuous_subtype_val)
  have hCn : ∀ k ∈ C, nu ℚ k = 1 := by
    rintro _ ⟨u, -, rfl⟩
    exact hnu _
  obtain ⟨B₁, hB₁⟩ := hMaj E D W M N P ph hph φ hφ C hCc hCn c hc 0
  have hbound : ∀ (g : G1 ℚ) (h : G1 E), ∀ k ∈ C,
      ‖f.1 (gl g) * (Th (W.Om g (W.L (gl h * k) ph)).1 * φ.1 (gl h * k))‖ ≤ B₂ * B₁ := by
    intro g h k hk
    obtain ⟨γ, b, a, k', hk', hg, ha⟩ := hred g
    have hp : 0 < ab a := ab_pos a
    have e1 : f.1 (gl g) = f.1 (gl (nU b * mD a) * gl k') := by
      rw [← gl_mul, ← hg, gl_mul, gl_ratS, (π.cusp _ hf).1.left]
    have e2 : Th (W.Om g (W.L (gl h * k) ph)).1 = Th (W.Om (nU b * mD a * k') (W.L (gl h * k) ph)).1 := by
      rw [← hg]
      exact ((UpperTheory.ConvolutionTheory.R2.Ff.thMeas ℚ E D W (W.L (gl h * k) ph)).2.1 γ g).symm
    obtain ⟨hs, h2, -⟩ := hB₁ b a k' hk' ha h k hk
    have h1 := hB₂ b a (gl k') ⟨k', hk', rfl⟩ ha
    have h3 : ‖Th (W.Om (nU b * mD a * k') (W.L (gl h * k) ph)).1‖ ≤
        ∑' ξ : Fin 4 → ℚ, ‖(W.Om (nU b * mD a * k') (W.L (gl h * k) ph)).1 (rp ξ)‖ :=
      norm_tsum_le_tsum_norm hs
    rw [e1, e2, norm_mul, norm_mul]
    calc _ ≤ (B₂ * (ab a)⁻¹ ^ 2) * (B₁ * ab a ^ 2) :=
          mul_le_mul h1 ((mul_le_mul_of_nonneg_right h3 (norm_nonneg _)).trans h2)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ((norm_nonneg _).trans h1)
      _ = B₂ * B₁ := by field_simp
  have hφc : Continuous φ.1 := (UpperTheory.ConvolutionTheory.RankTwoDescent.decE E P φ hφ).1.1
  let H : G1 ℚ → IdeleGroup.normOneSubgroup E → G1 E → ℂ := fun g u h =>
    f.1 (gl g) * (Th (W.Om g (W.L (gl h * sZ D (u : IdeleGroup E)) ph)).1 * φ.1 (gl h * sZ D (u : IdeleGroup E)))
  have hx : Continuous fun p : G1 ℚ × IdeleGroup.normOneSubgroup E × G1 E =>
      gl p.2.2 * sZ D (p.2.1 : IdeleGroup E) :=
    (continuous_gl.comp (continuous_snd.comp continuous_snd)).mul
      (hsc.comp (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)))
  have hnux : ∀ (h : G1 E) (u : IdeleGroup.normOneSubgroup E), nu ℚ (gl h * sZ D (u : IdeleGroup E)) = 1 := by
    intro h u
    rw [nu_mul, hnug, hnu, one_mul]
  have hTc : Continuous fun p : G1 ℚ × IdeleGroup.normOneSubgroup E × G1 E =>
      Th (W.Om p.1 (W.L (gl p.2.2 * sZ D (p.2.1 : IdeleGroup E)) ph)).1 := by
    have h0 := hTh E D W M N P ph hph Set.univ
    have h1 : Continuous fun p : G1 ℚ × IdeleGroup.normOneSubgroup E × G1 E =>
        ((p.1, gl p.2.2 * sZ D (p.2.1 : IdeleGroup E)) : G1 ℚ × GL (Fin 2) (A E)) := continuous_fst.prodMk hx
    have h2 := h0.comp_continuous h1 (fun p => hnux _ _)
    refine h2.congr fun p => ?_
    exact tsum_univ (fun ξ : Fin 4 → ℚ => (W.Om p.1 (W.L (gl p.2.2 * sZ D (p.2.1 : IdeleGroup E)) ph)).1 (rp ξ))
  have hHc : Continuous fun p : G1 ℚ × IdeleGroup.normOneSubgroup E × G1 E => H p.1 p.2.1 p.2.2 :=
    (hfc.comp (continuous_gl.comp continuous_fst)).mul (hTc.mul (hφc.comp hx))
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using UpperTheory.ConvolutionTheory.R2.Ff.vol ℚ M⟩
  haveI : IsFiniteMeasure ((normOneMeasure E).restrict (normOneFundamentalDomain E)) :=
    ⟨by simpa using normOneMeasure_normOneFundamentalDomain_lt_top E⟩
  haveI : IsFiniteMeasure (N.μ.restrict N.D) := ⟨by simpa using UpperTheory.ConvolutionTheory.RankTwoDescent.volE E N⟩
  have hae : ∀ᵐ p ∂((M.μ.restrict M.D).prod (((normOneMeasure E).restrict (normOneFundamentalDomain E)).prod
      (N.μ.restrict N.D))), p.2.1 ∈ normOneFundamentalDomain E := by
    have h1 : ∀ᵐ u ∂((normOneMeasure E).restrict (normOneFundamentalDomain E)), u ∈ normOneFundamentalDomain E :=
      ae_restrict_mem (measurableSet_normOneFundamentalDomain E)
    exact Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_fst.ae h1)
  have hInt : Integrable (fun p : G1 ℚ × IdeleGroup.normOneSubgroup E × G1 E => H p.1 p.2.1 p.2.2)
      ((M.μ.restrict M.D).prod (((normOneMeasure E).restrict (normOneFundamentalDomain E)).prod (N.μ.restrict N.D))) := by
    refine Integrable.of_bound hHc.aestronglyMeasurable (B₂ * B₁) ?_
    filter_upwards [hae] with p hp
    exact hbound p.1 p.2.2 _ ⟨p.2.1, subset_closure hp, rfl⟩
  have hL : ∀ g : G1 ℚ, f.1 (gl g) * f0 W N ph φ.1 g =
      ∫ u in normOneFundamentalDomain E, ∫ h in N.D, H g u h ∂N.μ ∂normOneMeasure E := by
    intro g
    simp only [f0, J1, UI, mean, H]
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    exact (integral_const_mul _ _).symm
  have hR : (J1 D N fun x => lift W M f.1 ph x * φ.1 x) =
      ∫ u in normOneFundamentalDomain E, ∫ h in N.D, ∫ g in M.D, H g u h ∂M.μ ∂N.μ ∂normOneMeasure E := by
    simp only [J1, UI, mean]
    refine integral_congr_ae (ae_of_all _ fun u => integral_congr_ae (ae_of_all _ fun h => ?_))
    simp only [lift, H]
    rw [← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    simp only [hnux, dM_one', mul_one, mul_assoc]
  simp only [hL]
  rw [hR]
  exact swap3 _ _ _ H hInt
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPartAlt
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

private theorem tsum_split (δ : ℚ) (f : (Fin 4 → ℚ) → ℂ) (hf : Summable f) :
    ∑' ξ, f ξ = f 0 + (∑' ξ : ({ξ | ξ ≠ 0 ∧ qr δ ξ = 0} : Set (Fin 4 → ℚ)), f ξ) +
      ∑' ξ : ({ξ | qr δ ξ ≠ 0} : Set (Fin 4 → ℚ)), f ξ := by
  set R : Set (Fin 4 → ℚ) := {ξ | ξ ≠ 0 ∧ qr δ ξ = 0}
  set Q : Set (Fin 4 → ℚ) := {ξ | qr δ ξ ≠ 0}
  have h0 : qr δ 0 = 0 := by simp [qr]
  have hpt : ∀ ξ, f ξ = (({0} : Set (Fin 4 → ℚ)).indicator f ξ + R.indicator f ξ) + Q.indicator f ξ := by
    intro ξ
    by_cases hq : qr δ ξ = 0
    · by_cases hξ : ξ = 0
      · subst hξ
        simp [R, Q, h0]
      · simp [R, Q, hξ, hq]
    · have hξ : ξ ≠ 0 := fun e => hq (e ▸ h0)
      simp [R, Q, hξ, hq]
  have s0 := hf.indicator ({0} : Set (Fin 4 → ℚ))
  have sR := hf.indicator R
  have sQ := hf.indicator Q
  rw [tsum_subtype R f, tsum_subtype Q f]
  have e0 : ∑' ξ, ({0} : Set (Fin 4 → ℚ)).indicator f ξ = f 0 := by
    rw [← tsum_subtype]; simp
  rw [← e0, ← (s0.tsum_add sR), ← ((s0.add sR).tsum_add sQ)]
  exact tsum_congr hpt

private theorem cD_one (g : G1 ℚ) : cD 1 g = g := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cD]

private theorem ab_one' : ab (1 : (A ℚ)ˣ) = 1 := by
  simp [ab]

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {D : Dat ℚ E}

private theorem act_zero (h : GL (Fin 2) (A E)) : D.act h (0 : V4 ℚ) = 0 := by
  have e : D.herm (0 : V4 ℚ) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Dat.herm, Dat.mkE]
  have e2 : D.unherm (0 : Matrix (Fin 2) (Fin 2) (A E)) = 0 := by
    funext i
    fin_cases i <;> simp [Dat.unherm, Dat.co]
  simp [Dat.act, e, e2]

private theorem om_zero (W : Weil D) (g : G1 ℚ) (ph : S4 ℚ) (x : GL (Fin 2) (A E)) (hx : nu ℚ x = 1) :
    (W.Om g (W.L x ph)).1 (rp 0) = (W.Om g ph).1 (rp 0) := by
  have h1 := W.comm x g
  rw [hx, cD_one] at h1
  have h2 : W.Om g (W.L x ph) = W.L x (W.Om g ph) := by
    have := congrArg (fun T : Module.End ℂ (S4 ℚ) => T ph) h1
    simpa [Module.End.mul_apply] using this.symm
  have hz : rp (0 : Fin 4 → ℚ) = (0 : V4 ℚ) := by
    funext i; simp [rp]
  rw [h2, W.L_apply, hx, ab_one', hz, act_zero]
  simp

private theorem core (hMaj : Maj) (hTh : ThCont) (hMean : MeanZero) (hR1 : Rank1)
    (W : Weil D) (M : Meas ℚ) (N : MeasE E) (P : CuspSub E 2) (hV : N.μ N.D < ⊤)
    (ph : S4 ℚ) (hph : ph ∈ Fock D.δ) (φ : Sm E 2) (hφ : φ ∈ P.V) (g : G1 ℚ)
    (y : GL (Fin 2) (A E)) (hy : nu ℚ y = 1) (hgl : ∀ h : G1 E, nu ℚ (gl h) = 1) :
    (mean N fun x => Th (W.Om g (W.L (x * y) ph)).1 * φ.1 (x * y)) =
      mean N fun x => ThOn {ξ | qr D.δ ξ ≠ 0} (W.Om g (W.L (x * y) ph)).1 * φ.1 (x * y) := by
  obtain ⟨b, a, k', hk', hg⟩ := UpperTheory.ConvolutionTheory.R2.M.iwa ℚ g
  have hapos : 0 < ab a := (IdeleGroup.ideleModule ℚ a).2
  obtain ⟨B, hB⟩ := hMaj E D W M N P ph hph φ hφ {y} isCompact_singleton
    (by rintro k rfl; exact hy) (ab a) hapos 0
  have hB' : ∀ h : G1 E, (Summable fun ξ : Fin 4 → ℚ => ‖(W.Om g (W.L (gl h * y) ph)).1 (rp ξ)‖) ∧
      (∑' ξ : Fin 4 → ℚ, ‖(W.Om g (W.L (gl h * y) ph)).1 (rp ξ)‖) * ‖φ.1 (gl h * y)‖ ≤ B * ab a ^ 2 := by
    intro h
    have := hB b a k' hk' le_rfl h y rfl
    rw [← hg] at this
    exact ⟨this.1, this.2.1⟩
  have hnu : ∀ h : G1 E, nu ℚ (gl h * y) = 1 := fun h => by rw [nu_mul, hgl, hy, one_mul]
  have hcφ : Continuous φ.1 := GlobalTheory.T.automorphicForm_GL_continuous E 2 φ (P.cusp φ hφ).1
  have hcg : Continuous fun h : G1 E => gl h := by fun_prop
  have hcx : Continuous fun h : G1 E => gl h * y := hcg.mul continuous_const
  haveI : IsFiniteMeasure (N.μ.restrict N.D) := ⟨by simpa using hV⟩
  have hint : ∀ S : Set (Fin 4 → ℚ), IntegrableOn
      (fun h : G1 E => ThOn S (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y)) N.D N.μ := by
    intro S
    have hc1 : Continuous fun h : G1 E => ThOn S (W.Om g (W.L (gl h * y) ph)).1 :=
      (hTh E D W M N P ph hph S).comp_continuous (f := fun h : G1 E => (g, gl h * y))
        (continuous_const.prodMk hcx) (fun h => hnu h)
    have hc : Continuous fun h : G1 E => ThOn S (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) :=
      hc1.mul (hcφ.comp hcx)
    refine Integrable.of_bound hc.aestronglyMeasurable (B * ab a ^ 2) (Eventually.of_forall fun h => ?_)
    obtain ⟨hs, hb⟩ := hB' h
    have hle : ‖ThOn S (W.Om g (W.L (gl h * y) ph)).1‖ ≤
        ∑' ξ : Fin 4 → ℚ, ‖(W.Om g (W.L (gl h * y) ph)).1 (rp ξ)‖ := by
      have hsS := hs.subtype (fun x => x ∈ S)
      refine (norm_tsum_le_tsum_norm hsS).trans ?_
      exact tsum_comp_le_tsum_of_inj hs (fun _ => norm_nonneg _) Subtype.val_injective
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hle (norm_nonneg _)).trans hb
  set c : ℂ := (W.Om g ph).1 (rp 0)
  have hz : ∀ h : G1 E, ThOn {0} (W.Om g (W.L (gl h * y) ph)).1 = c := by
    intro h
    have e : ThOn {0} (W.Om g (W.L (gl h * y) ph)).1 = (W.Om g (W.L (gl h * y) ph)).1 (rp 0) := by
      simp [ThOn]
    rw [e]
    exact om_zero W g ph _ (hnu h)
  have hφi : IntegrableOn (fun h : G1 E => c * φ.1 (gl h * y)) N.D N.μ := by
    refine (hint {0}).congr (Eventually.of_forall fun h => ?_)
    simp only [hz]
  have hpt : ∀ h : G1 E, Th (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) =
      c * φ.1 (gl h * y) +
        ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) +
        ThOn {ξ | qr D.δ ξ ≠ 0} (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) := by
    intro h
    have hsp := tsum_split D.δ (fun ξ => (W.Om g (W.L (gl h * y) ph)).1 (rp ξ)) (hB' h).1.of_norm
    have e0 : (W.Om g (W.L (gl h * y) ph)).1 (rp 0) = c := om_zero W g ph _ (hnu h)
    have : Th (W.Om g (W.L (gl h * y) ph)).1 = c + ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl h * y) ph)).1 +
        ThOn {ξ | qr D.δ ξ ≠ 0} (W.Om g (W.L (gl h * y) ph)).1 := by
      rw [← e0]
      exact hsp
    rw [this]
    ring
  have z1 : ∫ h in N.D, φ.1 (gl h * y) ∂N.μ = 0 := hMean E D W M N P φ hφ y
  have z2 : ∫ h in N.D, ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) ∂N.μ = 0 :=
    hR1 E D W M N P ph hph φ hφ g y hy
  simp only [mean]
  simp only [hpt]
  have i1 : IntegrableOn (fun h : G1 E => c * φ.1 (gl h * y) +
      ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y)) N.D N.μ := hφi.add (hint _)
  rw [integral_add i1 (hint _), integral_add hφi (hint _), integral_const_mul, z1, z2]
  simp

end UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.f0Eq :
    Maj → ThCont → MeanZero → Rank1 → ThetaLiftEqAnisotropicPart := by
  intro hMaj hTh hMean hR1 E _ _ _ D W M N P ph hph φ hφ
  funext g
  have hS := szLaws E D
  simp only [f0, fOn, J1]
  refine congrArg (UI (E := E)) (funext fun z => ?_)
  exact core hMaj hTh hMean hR1 W M N P (UpperTheory.ConvolutionTheory.RankTwoDescent.volE E N) ph hph φ hφ g (sZ D z) (hS.2.2.1 z) hS.2.2.2.1
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftIsBoundedCuspidal
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.FundamentalDomainContinuity

private theorem cont_nested {X Z Y : Type} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Z] [SecondCountableTopology Z] [MeasurableSpace Z] [BorelSpace Z]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Z) (ν : Measure Y) (S : Set Z) (Dm : Set Y) (hS : MeasurableSet S) (hμ : μ S < ⊤) (hν : ν Dm < ⊤)
    (f : X → Z → Y → ℂ) (x₀ : X) (U : Set X) (hU : U ∈ 𝓝 x₀) (B : ℝ)
    (hb : ∀ x ∈ U, ∀ z ∈ closure S, ∀ y, ‖f x z y‖ ≤ B)
    (hc : ∀ y, Continuous fun p : X × Z => f p.1 p.2 y)
    (hy : ∀ x z, Continuous (f x z)) :
    ContinuousAt (fun x => ∫ z in S, ∫ y in Dm, f x z y ∂ν ∂μ) x₀ := by
  have hint : Integrable (fun _ : Y => B) (ν.restrict Dm) := integrableOn_const hν.ne
  have hG : ∀ x ∈ U, ContinuousOn (fun z => ∫ y in Dm, f x z y ∂ν) (closure S) := by
    intro x hx z₀ hz₀
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => B) ?_ ?_ hint ?_
    · exact Eventually.of_forall fun z => (hy x z).aestronglyMeasurable
    · exact eventually_nhdsWithin_of_forall fun z hz => Eventually.of_forall fun y => hb x hx z hz y
    · refine Eventually.of_forall fun y => ?_
      have h1 : Continuous fun z => f x z y := (hc y).comp (Continuous.prodMk_right x)
      exact h1.continuousWithinAt
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => B * ν.real Dm) ?_ ?_ (integrableOn_const hμ.ne) ?_
  · filter_upwards [hU] with x hx
    exact ((hG x hx).aestronglyMeasurable isClosed_closure.measurableSet).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  · filter_upwards [hU] with x hx
    refine ae_restrict_of_forall_mem hS fun z hz => ?_
    exact norm_setIntegral_le_of_norm_le_const hν fun y _ => hb x hx z (subset_closure hz) y
  · refine ae_restrict_of_forall_mem hS fun z hz => ?_
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => B) ?_ ?_ hint ?_
    · exact Eventually.of_forall fun x => (hy x z).aestronglyMeasurable
    · filter_upwards [hU] with x hx
      exact Eventually.of_forall fun y => hb x hx z (subset_closure hz) y
    · refine Eventually.of_forall fun y => ?_
      have h1 : Continuous fun x => f x z y := (hc y).comp (Continuous.prodMk_left z)
      exact h1.continuousAt

variable {E : Type} [Field E] [NumberField E]

private theorem norm_liftIntegral_le (D : Dat ℚ E) (N : MeasE E) (hV : N.μ N.D < ⊤) (Ψ : GL (Fin 2) (A E) → ℂ) (B : ℝ)
    (hB : ∀ z ∈ normOneFundamentalDomain E, ∀ h : G1 E, ‖Ψ (gl h * sZ D (z : IdeleGroup E))‖ ≤ B) :
    ‖J1 D N Ψ‖ ≤ B * N.μ.real N.D * (normOneMeasure E).real (normOneFundamentalDomain E) := by
  unfold J1 UI
  refine norm_setIntegral_le_of_norm_le_const (normOneMeasure_normOneFundamentalDomain_lt_top E) fun z hz => ?_
  unfold mean
  exact norm_setIntegral_le_of_norm_le_const hV fun h _ => hB z hz h

end UpperTheory.ConvolutionTheory.RankTwoDescent.FundamentalDomainContinuity

open UpperTheory.ConvolutionTheory.RankTwoDescent.FundamentalDomainContinuity in
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.thetaPairing_constantTerm_cuspidal :
    Maj → ThCont → ThetaLiftEqAnisotropicPart → Coef → ThetaLiftIsBoundedCuspidal := by
  intro hMaj hTh hF0 hCoef E _ _ _ D W M N P ph hph φ hφ
  obtain ⟨-, hsC, hsN, hgN, -, -, -, -, -, -, -⟩ := szLaws E D
  have hφc : Continuous φ.1 := IsAutForm.continuous (P.cusp φ hφ).1
  have hV : N.μ N.D < ⊤ := volE E N
  set Zc : Set ↥(IdeleGroup.normOneSubgroup E) := closure (normOneFundamentalDomain E) with hZc
  have hZcpt : IsCompact Zc := isCompact_closure_normOneFundamentalDomain E
  have hsz : Continuous fun z : ↥(IdeleGroup.normOneSubgroup E) => sZ D (z : IdeleGroup E) :=
    hsC.comp continuous_subtype_val
  set C : Set (GL (Fin 2) (A E)) := (fun z : ↥(IdeleGroup.normOneSubgroup E) => sZ D (z : IdeleGroup E)) '' Zc with hCdef
  have hC : IsCompact C := hZcpt.image hsz
  have hCn : ∀ k ∈ C, nu ℚ k = 1 := by
    rintro k ⟨z, -, rfl⟩
    exact hsN _
  have hzC : ∀ z ∈ Zc, sZ D (z : IdeleGroup E) ∈ C := fun z hz => ⟨z, hz, rfl⟩
  have hleft : LInv (f0 W N ph φ.1) := by
    intro γ g
    simp only [f0, map_mul, Module.End.mul_apply, W.th_Om]
  have hth := hTh E D W M N P ph hph Set.univ
  have eTh : ∀ u : V4 ℚ → ℂ, ThOn Set.univ u = Th u := fun u => tsum_univ (fun ξ : Fin 4 → ℚ => u (rp ξ))
  have hnu : ∀ (h : G1 E) (z : (A E)ˣ), (gl h * sZ D z) ∈ {x : GL (Fin 2) (A E) | nu ℚ x = 1} := by
    intro h z
    have a1 : ideleNorm ℚ E (Matrix.GeneralLinearGroup.det (gl h)) = 1 := hgN h
    have a2 : ideleNorm ℚ E (Matrix.GeneralLinearGroup.det (sZ D z)) = 1 := hsN z
    change ideleNorm ℚ E (Matrix.GeneralLinearGroup.det (gl h * sZ D z)) = 1
    rw [map_mul, map_mul, a1, a2, one_mul]
  refine ⟨?_, hleft, ?_, ?_⟩
  ·
    refine continuous_iff_continuousAt.2 fun g₀ => ?_
    obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds g₀
    obtain ⟨-, hIw⟩ := UpperTheory.ConvolutionTheory.R2.Ff.iwa ℚ
    obtain ⟨V, hVc, hVU⟩ := hIw U hUc
    have hab : Continuous (ab : (A ℚ)ˣ → ℝ) := UpperTheory.ConvolutionTheory.R2.continuous_ab
    have hpos : ∀ a : (A ℚ)ˣ, 0 < ab a := fun a => (IdeleGroup.ideleModule ℚ a).2
    obtain ⟨T, hT⟩ := hVc.exists_bound_of_continuousOn hab.continuousOn
    obtain ⟨T', hT'⟩ := hVc.exists_bound_of_continuousOn
      (f := fun a => (ab a)⁻¹) (hab.inv₀ fun a => (hpos a).ne').continuousOn
    have hc0 : 0 < (|T'| + 1)⁻¹ := inv_pos.2 (by positivity)
    obtain ⟨B, hB⟩ := hMaj E D W M N P ph hph φ hφ C hC hCn _ hc0 0
    refine cont_nested (normOneMeasure E) N.μ (normOneFundamentalDomain E) N.D
      (measurableSet_normOneFundamentalDomain E) (normOneMeasure_normOneFundamentalDomain_lt_top E) hV
      (fun g z h => Th (W.Om g (W.L (gl h * sZ D (z : IdeleGroup E)) ph)).1 * φ.1 (gl h * sZ D (z : IdeleGroup E)))
      g₀ U hU (|B| * T ^ 2) ?_ ?_ ?_
    · intro x hx z hz h
      obtain ⟨b, a, ha, k, hk, rfl⟩ := hVU x hx
      have hle : (|T'| + 1)⁻¹ ≤ ab a := by
        have h1 : (ab a)⁻¹ ≤ |T'| + 1 := by
          have := hT' a ha
          rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hpos a))] at this
          linarith [le_abs_self T']
        exact (inv_le_comm₀ (hpos a) (by positivity)).1 h1
      obtain ⟨h1, h2, -⟩ := hB b a k hk hle h _ (hzC z hz)
      have h3 : ab a ≤ T := by
        have := hT a ha
        rwa [Real.norm_eq_abs, abs_of_pos (hpos a)] at this
      rw [norm_mul]
      calc _ ≤ _ := mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm h1) (norm_nonneg _)
        _ ≤ _ := h2
        _ ≤ |B| * T ^ 2 := mul_le_mul (le_abs_self B)
          (pow_le_pow_left₀ (hpos a).le h3 2) (by have := hpos a; positivity) (abs_nonneg B)
    · intro y
      have hA : Continuous fun p : G1 ℚ × ↥(IdeleGroup.normOneSubgroup E) => (p.1, gl y * sZ D (p.2 : IdeleGroup E)) :=
        continuous_fst.prodMk (continuous_const.mul (hsz.comp continuous_snd))
      have h1 := hth.comp_continuous hA (fun p => hnu y _)
      simp only [eTh] at h1
      exact h1.mul (hφc.comp (continuous_const.mul (hsz.comp continuous_snd)))
    · intro x z
      have hA : Continuous fun h : G1 E => (x, gl h * sZ D (z : IdeleGroup E)) :=
        continuous_const.prodMk (UpperTheory.ConvolutionTheory.R2.continuous_gl.mul continuous_const)
      have h1 := hth.comp_continuous hA (fun h => hnu h _)
      simp only [eTh] at h1
      exact h1.mul (hφc.comp (UpperTheory.ConvolutionTheory.R2.continuous_gl.mul continuous_const))
  ·
    obtain ⟨c, hc, hred⟩ := red ℚ
    obtain ⟨B, hB⟩ := hMaj E D W M N P ph hph φ hφ C hC hCn c hc 0
    refine ⟨B * N.μ.real N.D * (normOneMeasure E).real (normOneFundamentalDomain E), fun g => ?_⟩
    obtain ⟨γ, b, a, k, hk, he, hle⟩ := hred g
    rw [← hleft γ g, he, hF0 E D W M N P ph hph φ hφ]
    refine norm_liftIntegral_le D N hV _ B fun z hz h => ?_
    obtain ⟨h1, -, h3⟩ := hB b a k hk hle h _ (hzC z (subset_closure hz))
    have h4 : ‖ThOn {ξ | qr D.δ ξ ≠ 0} (W.Om (nU b * mD a * k) (W.L (gl h * sZ D (z : IdeleGroup E)) ph)).1‖ ≤
        ∑' ξ : {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0},
          ‖(W.Om (nU b * mD a * k) (W.L (gl h * sZ D (z : IdeleGroup E)) ph)).1 (rp ξ.1)‖ :=
      norm_tsum_le_tsum_norm (h1.subtype _)
    rw [norm_mul]
    refine (mul_le_mul_of_nonneg_right h4 (norm_nonneg _)).trans ?_
    simpa using h3
  ·
    intro g
    have h := hCoef E D W M N P ph hph φ hφ 0 g
    have e0 : fOn W N {ξ | qr D.δ ξ ≠ 0 ∧ qr D.δ ξ = 0} ph φ.1 g = 0 := by
      have e : {ξ : Fin 4 → ℚ | qr D.δ ξ ≠ 0 ∧ qr D.δ ξ = 0} = ∅ := by
        ext ξ
        simp
      rw [e]
      simp [fOn, J1, UI, mean, ThOn]
    have e1 : ∀ b : A ℚ, ψ (-(b * UpperTheory.ConvolutionTheory.R2.rt (0 : ℚ))) = 1 := fun b => by simp [ψ, UpperTheory.ConvolutionTheory.R2.rt]
    rw [e0, mul_zero] at h
    simp only [e1, mul_one] at h
    rw [hF0 E D W M N P ph hph φ hφ]
    exact h
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharInt
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.UnitaryMatrixFamily

private theorem char_int (r : ℚ) (hr : r ≠ 0) :
    ∫ b in fundamentalSet ℚ, ψ (b * rt r) ∂(adeleMeasure ℚ) = 0 := by
  obtain ⟨x, hx⟩ : ∃ x : A ℚ, adelicChar ℚ x ≠ 1 := by
    by_contra h
    push_neg at h
    exact adelicChar_ne_one (K := ℚ) (DFunLike.ext _ _ fun x => by simpa using h x)
  have hx' : ψ x ≠ 1 := fun h => hx (Circle.ext (by simpa [ψ] using h))
  have hper : ∀ (k : ℚ) (y : A ℚ), ψ ((rt k + y) * rt r) = ψ (y * rt r) := by
    intro k y
    rw [add_mul, Pp.ψ_add, ← map_mul, Pp.ψ_rt, one_mul]
  have h := Pp.int_add (F := ℚ) (h := fun b => ψ (b * rt r)) hper (rt r⁻¹ * x)
  have hrr : rt r⁻¹ * rt r = (1 : A ℚ) := by rw [← map_mul, inv_mul_cancel₀ hr, map_one]
  have e : ∀ b : A ℚ, ψ ((b + rt r⁻¹ * x) * rt r) = ψ (b * rt r) * ψ x := by
    intro b
    rw [add_mul, Pp.ψ_add, mul_right_comm, hrr, one_mul]
  simp only [e] at h
  rw [integral_mul_const] at h
  have h1 : (∫ b in fundamentalSet ℚ, ψ (b * rt r) ∂(adeleMeasure ℚ)) * (ψ x - 1) = 0 := by
    rw [mul_sub, h, mul_one, sub_self]
  exact (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 hx')

private theorem vol_one : (adeleMeasure ℚ).real (fundamentalSet ℚ) = 1 := by
  rw [measureReal_def, adeleMeasure_fundamentalSet, ENNReal.toReal_one]

private theorem fourier (S T : Set (Fin 4 → ℚ)) (q : (Fin 4 → ℚ) → ℚ) (t : ℚ) (c : (Fin 4 → ℚ) → ℂ)
    (hT : ∀ ξ, ξ ∈ T ↔ ξ ∈ S ∧ q ξ = t) (hc : Summable fun ξ : S => ‖c ξ‖) :
    ∫ b in fundamentalSet ℚ, (∑' ξ : S, ψ (b * rt (q ξ)) * c ξ) * ψ (-(b * rt t)) ∂(adeleMeasure ℚ) =
      ∑' ξ : T, c ξ := by
  have hvol : ((adeleMeasure ℚ).restrict (fundamentalSet ℚ)) Set.univ = 1 := by
    rw [Measure.restrict_apply_univ, adeleMeasure_fundamentalSet]
  haveI : IsProbabilityMeasure ((adeleMeasure ℚ).restrict (fundamentalSet ℚ)) := ⟨hvol⟩
  set G : S → A ℚ → ℂ := fun ξ b => ψ (b * rt (q ξ - t)) * c ξ with hG
  have hGc : ∀ ξ, Continuous (G ξ) := fun ξ =>
    (Pp.cont_ψ.comp (continuous_id.mul continuous_const)).mul continuous_const
  have hGn : ∀ ξ b, ‖G ξ b‖ = ‖c ξ‖ := fun ξ b => by simp [hG, Pp.norm_ψ]
  have e : ∀ b : A ℚ, (∑' ξ : S, ψ (b * rt (q ξ)) * c ξ) * ψ (-(b * rt t)) = ∑' ξ, G ξ b := by
    intro b
    rw [← tsum_mul_right]
    refine tsum_congr fun ξ => ?_
    have h0 : rt (q ξ - t) = rt (q ξ) - rt t := map_sub (algebraMap ℚ (A ℚ)) _ _
    have : b * rt (q ξ - t) = b * rt (q ξ) + -(b * rt t) := by
      rw [h0, mul_sub, sub_eq_add_neg]
    simp only [hG, this, Pp.ψ_add]
    ring
  simp only [e]
  have hS := hasSum_integral_of_summable_integral_norm (μ := (adeleMeasure ℚ).restrict (fundamentalSet ℚ))
    (F := G) (fun ξ => Pp.intOn (hGc ξ)) (by
      simp only [hGn, integral_const, probReal_univ, one_smul]
      exact hc)
  rw [← hS.tsum_eq]
  have term : ∀ ξ : S, ∫ b in fundamentalSet ℚ, G ξ b ∂(adeleMeasure ℚ) = T.indicator c ξ := by
    intro ξ
    simp only [hG]
    rw [integral_mul_const]
    by_cases h : q ξ = t
    · have hm : (ξ : Fin 4 → ℚ) ∈ T := (hT _).2 ⟨ξ.2, h⟩
      simp [h, hm, Set.indicator_of_mem, measureReal_def, hvol]
    · have hm : (ξ : Fin 4 → ℚ) ∉ T := fun hm => h ((hT _).1 hm).2
      rw [char_int _ (sub_ne_zero.2 h), zero_mul, Set.indicator_of_notMem hm]
  simp only [term]
  rw [tsum_subtype S (T.indicator c), tsum_subtype T c]
  refine tsum_congr fun ξ => ?_
  by_cases h : ξ ∈ T
  · simp [h, ((hT _).1 h).1]
  · by_cases h' : ξ ∈ S <;> simp [h, h']

private theorem swap3 {B Z H : Type} [MeasurableSpace B] [MeasurableSpace Z] [MeasurableSpace H]
    (m : Measure B) (μ₁ : Measure Z) (μ₂ : Measure H) [IsFiniteMeasure m] [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (f : B → Z → H → ℂ) (hf : AEStronglyMeasurable (fun p : B × Z × H => f p.1 p.2.1 p.2.2) (m.prod (μ₁.prod μ₂)))
    (C : ℝ) (hb : ∀ᵐ z ∂μ₁, ∀ b h, ‖f b z h‖ ≤ C) :
    ∫ b, ∫ z, ∫ h, f b z h ∂μ₂ ∂μ₁ ∂m = ∫ z, ∫ h, ∫ b, f b z h ∂m ∂μ₂ ∂μ₁ := by
  have hae : ∀ᵐ p ∂(m.prod (μ₁.prod μ₂)), ‖f p.1 p.2.1 p.2.2‖ ≤ C := by
    have h1 : ∀ᵐ p ∂(μ₁.prod μ₂), ∀ b h, ‖f b p.1 h‖ ≤ C := Measure.quasiMeasurePreserving_fst.ae hb
    have h2 : ∀ᵐ p ∂(m.prod (μ₁.prod μ₂)), ∀ b h, ‖f b p.2.1 h‖ ≤ C := Measure.quasiMeasurePreserving_snd.ae h1
    exact h2.mono fun p hp => hp _ _
  have hF : Integrable (fun p : B × Z × H => f p.1 p.2.1 p.2.2) (m.prod (μ₁.prod μ₂)) :=
    Integrable.of_bound hf C hae
  have s1 : ∫ b, ∫ z, ∫ h, f b z h ∂μ₂ ∂μ₁ ∂m = ∫ b, ∫ p : Z × H, f b p.1 p.2 ∂(μ₁.prod μ₂) ∂m := by
    refine integral_congr_ae (hF.prod_right_ae.mono fun b hb' => ?_)
    exact (integral_prod _ hb').symm
  have s2 : ∫ b, ∫ p : Z × H, f b p.1 p.2 ∂(μ₁.prod μ₂) ∂m = ∫ p : Z × H, ∫ b, f b p.1 p.2 ∂m ∂(μ₁.prod μ₂) :=
    integral_integral_swap (f := fun b (p : Z × H) => f b p.1 p.2) hF
  rw [s1, s2]
  exact integral_prod (fun p : Z × H => ∫ b, f b p.1 p.2 ∂m) hF.integral_prod_right

end UpperTheory.ConvolutionTheory.RankTwoDescent.UnitaryMatrixFamily

open UpperTheory.ConvolutionTheory.RankTwoDescent.UnitaryMatrixFamily in
private theorem coefOf (hV : VolE) :
    Maj → ThCont → Coef := by
  intro hMaj hTh E _ _ _ D W M N P ph hph φ hφ t g
  obtain ⟨hs1, hsc, hnz, hng, -, -, -, -, -, -, hq⟩ := szLaws E D
  obtain ⟨b₀, a₀, k₀, hk₀, rfl⟩ := UpperTheory.ConvolutionTheory.R2.M.iwa ℚ g
  have hφc : Continuous φ.1 := by
    obtain ⟨ψ', hψ'⟩ := LinearMap.mem_range.mp (UpperTheory.V.Cm.mem_range_ofCusp.2 (P.cusp φ hφ))
    rw [← hψ']
    exact ψ'.2.1.continuous
  have hzc : Continuous fun u : IdeleGroup.normOneSubgroup E => sZ D (u : IdeleGroup E) :=
    hsc.comp continuous_subtype_val
  have hCc := (isCompact_closure_normOneFundamentalDomain E).image hzc
  have hCn : ∀ k ∈ (fun u : IdeleGroup.normOneSubgroup E => sZ D (u : IdeleGroup E)) '' closure (normOneFundamentalDomain E),
      nu ℚ k = 1 := by
    rintro _ ⟨u, -, rfl⟩
    exact hnz _
  have hapos : 0 < ab a₀ := (IdeleGroup.ideleModule ℚ a₀).2
  obtain ⟨B, hB⟩ := hMaj E D W M N P ph hph φ hφ _ hCc hCn (ab a₀) hapos 0
  set S : Set (Fin 4 → ℚ) := {ξ | qr D.δ ξ ≠ 0} with hS
  set T : Set (Fin 4 → ℚ) := {ξ | qr D.δ ξ ≠ 0 ∧ qr D.δ ξ = t} with hTd
  set g₀ : G1 ℚ := nU b₀ * mD a₀ * k₀ with hg₀
  let x : IdeleGroup.normOneSubgroup E → G1 E → GL (Fin 2) (A E) := fun z h => gl h * sZ D (z : IdeleGroup E)
  have hxc : Continuous fun p : IdeleGroup.normOneSubgroup E × G1 E => x p.1 p.2 := by
    have h1 : Continuous (gl : G1 E → GL (Fin 2) (A E)) := by fun_prop
    exact (h1.comp continuous_snd).mul (hzc.comp continuous_fst)
  have hnux : ∀ z h, nu ℚ (x z h) = 1 := fun z h => by
    have : nu ℚ (x z h) = nu ℚ (gl h) * nu ℚ (sZ D (z : IdeleGroup E)) := by simp [x, nu, map_mul]
    rw [this, hng, hnz, one_mul]
  let c : IdeleGroup.normOneSubgroup E → G1 E → (Fin 4 → ℚ) → ℂ := fun z h ξ => (W.Om g₀ (W.L (x z h) ph)).1 (rp ξ)
  have hterm : ∀ b z h ξ, (W.Om (nU b * g₀) (W.L (x z h) ph)).1 (rp ξ) = ψ (b * rt (qr D.δ ξ)) * c z h ξ := by
    intro b z h ξ
    rw [map_mul, Module.End.mul_apply, W.Om_n, hq]
  have hmaj := fun (b : A ℚ) (z : IdeleGroup.normOneSubgroup E) (hz : z ∈ normOneFundamentalDomain E) (h : G1 E) =>
    hB b a₀ k₀ hk₀ le_rfl h (sZ D (z : IdeleGroup E)) ⟨z, subset_closure hz, rfl⟩
  have hsum : ∀ z ∈ normOneFundamentalDomain E, ∀ h, Summable fun ξ : S => ‖c z h ξ‖ := fun z hz h =>
    (hmaj b₀ z hz h).1.subtype (fun ξ => ξ ∈ S)
  have hnU : ∀ b, nU (b + b₀) * mD a₀ * k₀ = nU b * g₀ := by
    intro b
    rw [UpperTheory.ConvolutionTheory.R2.M.nU_add]
    simp only [hg₀, mul_assoc]
  let T' : A ℚ → IdeleGroup.normOneSubgroup E → G1 E → ℂ := fun b z h =>
    ThOn S (W.Om (nU b * g₀) (W.L (x z h) ph)).1 * φ.1 (x z h)
  let f : A ℚ → IdeleGroup.normOneSubgroup E → G1 E → ℂ := fun b z h => T' b z h * ψ (-(b * rt t))
  have hbd : ∀ z ∈ normOneFundamentalDomain E, ∀ b h, ‖f b z h‖ ≤ B := by
    intro z hz b h
    have h1 := (hmaj (b + b₀) z hz h).1
    have h3 := (hmaj (b + b₀) z hz h).2.2
    simp only [hnU, pow_zero, mul_one] at h1 h3
    have h2 : ‖ThOn S (W.Om (nU b * g₀) (W.L (x z h) ph)).1‖ ≤
        ∑' ξ : {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0}, ‖(W.Om (nU b * g₀) (W.L (gl h * sZ D (z : IdeleGroup E)) ph)).1 (rp ξ.1)‖ :=
      norm_tsum_le_tsum_norm (h1.subtype (fun ξ => ξ ∈ S))
    calc ‖f b z h‖ = ‖ThOn S (W.Om (nU b * g₀) (W.L (x z h) ph)).1‖ * ‖φ.1 (x z h)‖ := by
          simp only [f, T', norm_mul, Pp.norm_ψ, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ ≤ B := h3
  have hNc : Continuous fun b : A ℚ => nU b := by
    refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
    fin_cases i <;> fin_cases j <;> simp [nU] <;> fun_prop
  have hcont : Continuous fun p : A ℚ × IdeleGroup.normOneSubgroup E × G1 E => f p.1 p.2.1 p.2.2 := by
    have hp : Continuous fun p : A ℚ × IdeleGroup.normOneSubgroup E × G1 E => (nU p.1 * g₀, x p.2.1 p.2.2) :=
      ((hNc.comp continuous_fst).mul continuous_const).prodMk (hxc.comp continuous_snd)
    have h1 := (hTh E D W M N P ph hph S).comp_continuous hp (fun p => hnux _ _)
    exact (h1.mul (hφc.comp (hxc.comp continuous_snd))).mul
      (Pp.cont_ψ.comp ((continuous_fst.mul continuous_const).neg))
  haveI : IsFiniteMeasure ((adeleMeasure ℚ).restrict (fundamentalSet ℚ)) :=
    ⟨by rw [Measure.restrict_apply_univ, adeleMeasure_fundamentalSet]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure ((normOneMeasure E).restrict (normOneFundamentalDomain E)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact normOneMeasure_normOneFundamentalDomain_lt_top E⟩
  haveI : IsFiniteMeasure (N.μ.restrict N.D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hV E N⟩
  have step : ∀ b, fOn W N S ph φ.1 (nU b * g₀) * ψ (-(b * rt t)) =
      ∫ z in normOneFundamentalDomain E, ∫ h in N.D, f b z h ∂N.μ ∂normOneMeasure E := by
    intro b
    change (∫ z in normOneFundamentalDomain E, ∫ h in N.D, T' b z h ∂N.μ ∂normOneMeasure E) * _ = _
    rw [← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    exact (integral_mul_const _ _).symm
  simp only [step]
  rw [swap3 _ _ _ f hcont.aestronglyMeasurable B
    (ae_restrict_of_forall_mem (measurableSet_normOneFundamentalDomain E) hbd), vol_one, Complex.ofReal_one, one_mul]
  change _ = ∫ z in normOneFundamentalDomain E, ∫ h in N.D, ThOn T (W.Om g₀ (W.L (x z h) ph)).1 * φ.1 (x z h) ∂N.μ ∂normOneMeasure E
  refine setIntegral_congr_fun (measurableSet_normOneFundamentalDomain E) fun z hz => ?_
  refine integral_congr_ae (ae_of_all _ fun h => ?_)
  have e : ∀ b, f b z h = ((∑' ξ : S, ψ (b * rt (qr D.δ ξ)) * c z h ξ) * ψ (-(b * rt t))) * φ.1 (x z h) := by
    intro b
    simp only [f, T', ThOn, hterm]
    ring
  simp only [e]
  rw [integral_mul_const, fourier S T (qr D.δ) t (c z h) (fun ξ => Iff.rfl) (hsum z hz h)]
  rfl

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.coef :
    Maj → ThCont → Coef :=
  coefOf volE
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Rev
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.rev :
    ThetaLiftEqAnisotropicPart → Coef → ThetaLiftIsBoundedCuspidal → Dens → Fub → CoefPer → Rev := by
  rintro hE hC hF hD hB hP E _ _ _ D W M N P ⟨φ, hφ, h, hne⟩
  obtain ⟨ph, hph, h0⟩ : ∃ ph ∈ Fock D.δ, f0 W N ph φ.1 ≠ 0 := by
    by_contra hn
    push Not at hn
    refine hne (hP E D W M N P φ hφ (fun ph hph => ?_) h)
    have h1 := hC E D W M N P ph hph φ hφ (qr D.δ X0) 1
    rw [← hE E D W M N P ph hph φ hφ, hn ph hph] at h1
    have hδ : qr D.δ X0 ≠ 0 := by
      have := D.neg (Rat.castHom ℝ)
      simp only [qr, X0, eq_ratCast, Rat.cast_lt_zero] at this ⊢
      simpa using this.ne
    have e : {ξ | qr D.δ ξ ≠ 0 ∧ qr D.δ ξ = qr D.δ X0} = {ξ | qr D.δ ξ = qr D.δ X0} :=
      Set.ext fun ξ => ⟨fun h => h.2, fun h => ⟨(show qr D.δ ξ = _ from h) ▸ hδ, h⟩⟩
    rw [e] at h1
    simp only [Pi.zero_apply, zero_mul, integral_zero] at h1
    refine (mul_eq_zero.1 h1.symm).resolve_left ?_
    simp [Measure.real, adeleMeasure_fundamentalSet]
  obtain ⟨π, hπ, f, hf, h2⟩ := hD M _ (hF E D W M N P ph hph φ hφ) h0
  exact ⟨π, hπ, f, hf, ph, hph, φ, hφ, hB E D W M N P ph hph φ hφ π f hf ▸ h2⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbFn
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.orbFn :
    OrbS → OrbFn := by
  intro hS E _ _ _ D M j hj c hc hcs
  have hstab := (hS E D).2.1
  haveI : PolishSpace (G1 E) := GroundTheory.Automorphic.polishSpace_of_locallyCompact
  haveI := M.haar
  haveI := M.right
  have hval : ∀ g : G1 ℚ, (j g).1 = g.1.map (AdeleBaseChange.adeleMap ℚ E) := fun g => by
    have := congrArg Units.val (hj g)
    simpa [em] using this
  have hjc : Continuous j := by
    refine continuous_induced_rng.2 ?_
    exact (continuous_subtype_val.matrix_map AdeleBaseChange.continuous_adeleMap).congr fun g => (hval g).symm
  set O : G1 E → V4 ℚ := fun h => D.act (gl h)⁻¹ (rp X0) with hO
  set cc : G1 E → ℂ := fun h => ∫ g, c (j g * h) ∂M.μ with hcc
  have hgl : Continuous fun h : G1 E => gl h := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    have e : ∀ h : G1 E, ((gl h)⁻¹ : GL (Fin 2) (A E)).val = (h⁻¹ : G1 E).1 := fun h => by
      have : (gl h)⁻¹ = gl h⁻¹ := by simp only [gl, map_inv]
      rw [this]; rfl
    have hi : Continuous fun h : G1 E => (h⁻¹ : G1 E).1 :=
      (continuous_subtype_val : Continuous fun g : G1 E => g.1).comp continuous_inv
    exact hi.congr fun h => (e h).symm
  have hglc : Continuous fun h : G1 E => (gl h)⁻¹ := hgl.inv
  have hOc : Continuous O := D.continuous_act' hglc continuous_const
  have hccm : Measurable cc := by
    have hF : StronglyMeasurable (Function.uncurry fun (h : G1 E) (g : G1 ℚ) => c (j g * h)) :=
      (hc.comp ((hjc.comp continuous_snd).mul continuous_fst)).stronglyMeasurable
    exact (hF.integral_prod_right (ν := M.μ)).measurable
  have hfac : Function.FactorsThrough cc O := by
    intro a b hab
    have h1 : D.act (gl (b * a⁻¹)) (rp X0) = rp X0 := by
      have hab' : D.act (gl a)⁻¹ (rp X0) = D.act (gl b)⁻¹ (rp X0) := hab
      have e : gl (b * a⁻¹) = gl b * (gl a)⁻¹ := by simp only [gl, map_mul, map_inv]
      rw [e, Dat.act_mul, hab', Dat.act_act_inv]
    obtain ⟨g0, hg0⟩ := (hstab (b * a⁻¹)).1 h1
    have h2 : b * a⁻¹ = j g0 := Matrix.SpecialLinearGroup.toGL_injective (hg0.trans (hj g0).symm)
    have h3 : b = j g0 * a := by rw [← h2]; group
    simp only [hcc]
    rw [h3]
    have := integral_mul_right_eq_self (μ := M.μ) (fun g => c (j g * a)) g0
    simp only [map_mul, mul_assoc] at this
    exact this.symm
  refine ⟨Function.extend O cc 0, ?_, fun h => hfac.extend_apply 0 h⟩
  have hR : MeasurableSet (Set.range O) := by
    obtain ⟨K, hK, hU⟩ := isSigmaCompact_range hOc
    rw [← hU]
    exact MeasurableSet.iUnion fun n => (hK n).measurableSet
  refine measurable_of_restrict_of_restrict_compl hR ?_ ?_
  · have hr : Measurable (Set.rangeFactorization O) := hOc.measurable.subtype_mk
    refine (Measurable.measurable_comp_iff_of_surjective hr Set.rangeFactorization_surjective).1 ?_
    have e : (Set.range O).domRestrict (Function.extend O cc 0) ∘ Set.rangeFactorization O = cc := by
      funext h
      exact hfac.extend_apply 0 h
    rw [e]
    exact hccm
  · have e : (Set.range O)ᶜ.domRestrict (Function.extend O cc 0) = fun _ => 0 := by
      funext x
      exact Function.extend_apply' cc (0 : V4 ℚ → ℂ) x.1 fun ⟨a, ha⟩ => x.2 ⟨a, ha⟩
    rw [e]
    exact measurable_const
end

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

theorem maj_holds : Maj := maj latSum decE

theorem meanZero_holds : MeanZero := meanZero decE

theorem thetaConstantTerm_eq : ThetaLiftEqAnisotropicPart := f0Eq maj_holds thCont meanZero_holds (rank1 decE maj_holds orb1)

theorem rev_holds : Rev :=
  rev thetaConstantTerm_eq (coef maj_holds thCont) (thetaPairing_constantTerm_cuspidal maj_holds thCont thetaConstantTerm_eq (coef maj_holds thCont)) dens (fub maj_holds thCont)
    (coefPer decE maj_holds orbS momKill (orbFn orbS))

end UpperTheory.ConvolutionTheory.RankTwoDescent
