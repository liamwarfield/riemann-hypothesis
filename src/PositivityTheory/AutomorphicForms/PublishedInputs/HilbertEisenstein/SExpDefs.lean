module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SExpDefs
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def gPt (x : UpperTheory.V.TR.Rinf F) (y : (UpperTheory.V.TR.Rinf F)ˣ) (yf : (Af F)ˣ) : GA F 2 :=
  UpperTheory.V.TR.infGL F 2 (aff y x) * finGL F 2 (aff yf 0)

def yAd (y : (UpperTheory.V.TR.Rinf F)ˣ) (yf : (Af F)ˣ) : Ad F :=
  ((UpperTheory.V.TR.infId F y * finId F yf : (Ad F)ˣ) : Ad F)

def tau (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) : IdeleGroup F :=
  moduleSection (w0 F) t * (u : IdeleGroup F)

def wt (ω : HChar F) (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) : ℂ :=
  ((ω.1 (tau t u) : ℂˣ) : ℂ)⁻¹ * ((t : ℝ) : ℂ)


variable (F) in
abbrev muE : Measure ({r : ℝ // 0 < r} × normOneSubgroup F) :=
  posRealMeasure.prod ((normOneMeasure F).restrict (normOneFundamentalDomain F))

def zeroRow (c : HeightOneSpectrum (𝓞 F) → ℕ) (τ : IdeleGroup F) : ℂ :=
  ∑' b : Fˣ, Phi c ![0, (τ : Ad F) * algebraMap F (Ad F) (b : F)]

def slice (c : HeightOneSpectrum (𝓞 F) → ℕ) (A : Ad F) (B : Ad F) : ℂ := Phi c ![A, B]

def kern (c : HeightOneSpectrum (𝓞 F) → ℕ) (Y : Ad F) (τ : IdeleGroup F) (ξ : F) : ℂ :=
  ((ideleModule F τ : ℝ)⁻¹ : ℂ) *
    adelicFourier F (slice c ((τ : Ad F) * Y)) (τ⁻¹ • algebraMap F (Ad F) ξ)

def coefK (c : HeightOneSpectrum (𝓞 F) → ℕ) (Y : Ad F) (τ : IdeleGroup F) (ξ : F) : ℂ :=
  ∑' a : Fˣ, kern c Y (τ * diagonal F a) ξ

def ex (ξ : F) (x : UpperTheory.V.TR.Rinf F) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v ξ : ℂ) * (x v : ℂ))


open Classical in
def kernF (c : HeightOneSpectrum (𝓞 F) → ℕ) (A Z : Ad F) : ℂ :=
  (∏ v, (((UpperTheory.V.TR.pInf F A v : ℂ) + (UpperTheory.V.TR.pInf F Z v : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * ((UpperTheory.V.TR.pInf F A v : ℂ) ^ 2 + (UpperTheory.V.TR.pInf F Z v : ℂ) ^ 2)))) *
    if (∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ))) ∧
        (∀ w, Valued.v (pLoc F w (pFin F Z)) ≤ WithZero.exp ((c w : ℤ) + dd w))
    then ((finiteAdelicChar F (pFin F Z) : Circle) : ℂ) else 0

def divS (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (𝔪 : Ideal (𝓞 F)) : ℂ :=
  ∑ᶠ 𝔯 ∈ {𝔯 | 𝔯 ∣ 𝔪}, chiI ω c 𝔯

def SKern : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (c : HeightOneSpectrum (𝓞 F) → ℕ),
  {w | c w ≠ 0}.Finite → ∃ κ : ℂ, κ ≠ 0 ∧ ∀ A Z : Ad F, adelicFourier F (slice c A) Z = κ * kernF c A Z

def SFin : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → {w | c w ≠ 0}.Finite

def SZero : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → Integrable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F => zeroRow c (tau p.1 p.2) * wt ω p.1 p.2) (muE F)

def SPoint : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → ∀ (x : UpperTheory.V.TR.Rinf F) (y : (UpperTheory.V.TR.Rinf F)ˣ), (∀ v, 0 < y.val v) → ∀ (yf : (Af F)ˣ) (τ : IdeleGroup F),
    thetaS (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) τ * gPt x y yf) =
      zeroRow c τ + coefK c (yAd y yf) τ 0 + ∑' ξ : Fˣ, ex (ξ : F) x * coefK c (yAd y yf) τ ξ

def SNull : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → ∀ (y : (UpperTheory.V.TR.Rinf F)ˣ) (yf : (Af F)ˣ) (t : {r : ℝ // 0 < r}),
    IntegrableOn (fun u => coefK c (yAd y yf) (tau t u) 0 * ((ω.1 (tau t u) : ℂˣ) : ℂ)⁻¹) (normOneFundamentalDomain F)
      (normOneMeasure F) →
    ∫ u in normOneFundamentalDomain F, coefK c (yAd y yf) (tau t u) 0 * ((ω.1 (tau t u) : ℂˣ) : ℂ)⁻¹ ∂normOneMeasure F = 0

def SAbs : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → ∀ (y : (UpperTheory.V.TR.Rinf F)ˣ), (∀ v, 0 < y.val v) → ∀ yf : (Af F)ˣ,
    (∀ ξ : F, AEStronglyMeasurable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F => coefK c (yAd y yf) (tau p.1 p.2) ξ) (muE F)) ∧
    (∀ p : {r : ℝ // 0 < r} × normOneSubgroup F, Summable fun ξ : Fˣ => ‖coefK c (yAd y yf) (tau p.1 p.2) ξ‖) ∧
    Integrable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F =>
      (∑' ξ : Fˣ, ‖coefK c (yAd y yf) (tau p.1 p.2) ξ‖) * (p.1 : ℝ)) (muE F)

def SUnfold : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → ∀ (Y : Ad F) (ξ : F),
    Integrable (fun τ : IdeleGroup F => kern c Y τ ξ * ((ω.1 τ : ℂˣ) : ℂ)⁻¹ * ((ideleModule F τ : ℝ) : ℂ)) (ideleMeasure F) →
    ∫ p, coefK c Y (tau p.1 p.2) ξ * wt ω p.1 p.2 ∂(muE F) =
      ∫ τ, kern c Y τ ξ * ((ω.1 τ : ℂˣ) : ℂ)⁻¹ * ((ideleModule F τ : ℝ) : ℂ) ∂ideleMeasure F

def SLocal : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → ∃ C₀ : ℂ, C₀ ≠ 0 ∧ ∀ (y : (UpperTheory.V.TR.Rinf F)ˣ), (∀ v, 0 < y.val v) → ∀ (yf : (Af F)ˣ) (ξ : Fˣ),
    Integrable (fun τ : IdeleGroup F => kern c (yAd y yf) τ ξ * ((ω.1 τ : ℂˣ) : ℂ)⁻¹ * ((ideleModule F τ : ℝ) : ℂ))
      (ideleMeasure F) ∧
    ∫ τ, kern c (yAd y yf) τ ξ * ((ω.1 τ : ℂˣ) : ℂ)⁻¹ * ((ideleModule F τ : ℝ) : ℂ) ∂ideleMeasure F =
      C₀ * if ∀ v, 0 < reAt v (ξ : F) then
        coefAt (divS ω c) (algebraMap F (Af F) (ξ : F) * (yf : Af F)) *
          Complex.exp (-(2 * Real.pi : ℂ) * ∑ v, (reAt v (ξ : F) : ℂ) * (y.val v : ℂ))
      else 0

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.PolyVHasTemperateGrowth
noncomputable section

open NumberField
open scoped SchwartzMap ContDiff

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

def curryE : (Fin 2 → UpperTheory.V.TR.Rinf F) ≃ₗ[ℝ] (Fin 2 × InfinitePlace F → ℝ) where
  toFun y p := y p.1 p.2
  invFun z i v := z (i, v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def euclE : (Fin 2 → UpperTheory.V.TR.Rinf F) ≃L[ℝ] EuclideanSpace ℝ (Fin 2 × InfinitePlace F) :=
  (curryE F).toContinuousLinearEquiv.trans (EuclideanSpace.equiv (Fin 2 × InfinitePlace F) ℝ).symm

omit [IsTotallyReal F] in
theorem norm_euclE_sq (y : Fin 2 → UpperTheory.V.TR.Rinf F) :
    ‖euclE F y‖ ^ 2 = ∑ v, ((y 0 v) ^ 2 + (y 1 v) ^ 2) := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, Fin.sum_univ_two,
    ← Finset.sum_add_distrib]
  rfl

def gaussV : 𝓢(Fin 2 → UpperTheory.V.TR.Rinf F, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclE F) (GroundTheory.Global.gaussianSchwartz _)

theorem gaussV_apply (y : Fin 2 → UpperTheory.V.TR.Rinf F) :
    gaussV F y = Complex.exp (-(Real.pi : ℂ) * ∑ v, (((y 0 v : ℝ) : ℂ) ^ 2 + ((y 1 v : ℝ) : ℂ) ^ 2)) := by
  simp only [gaussV, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GroundTheory.Global.gaussianSchwartz_apply, norm_euclE_sq]
  push_cast
  rfl

def coordV (i : Fin 2) (v : InfinitePlace F) : (Fin 2 → UpperTheory.V.TR.Rinf F) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : InfinitePlace F => ℝ) v).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => UpperTheory.V.TR.Rinf F) i)

def linV (v : InfinitePlace F) : (Fin 2 → UpperTheory.V.TR.Rinf F) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (coordV F 0 v) + Complex.I • Complex.ofRealCLM.comp (coordV F 1 v)

theorem linV_apply (v : InfinitePlace F) (y : Fin 2 → UpperTheory.V.TR.Rinf F) :
    linV F v y = ((y 0 v : ℝ) : ℂ) + Complex.I * ((y 1 v : ℝ) : ℂ) := by
  simp [linV, coordV]

def polyV (y : Fin 2 → UpperTheory.V.TR.Rinf F) : ℂ := ∏ v, linV F v y

theorem polyV_hasTemperateGrowth : (polyV F).HasTemperateGrowth := by
  classical
  have h : ∀ s : Finset (InfinitePlace F),
      (fun y : Fin 2 → UpperTheory.V.TR.Rinf F => ∏ v ∈ s, linV F v y).HasTemperateGrowth := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.prod_empty]; exact Function.HasTemperateGrowth.const (E := Fin 2 → UpperTheory.V.TR.Rinf F) (1 : ℂ)
    | insert a s ha ih =>
      have e : (fun y : Fin 2 → UpperTheory.V.TR.Rinf F => ∏ v ∈ insert a s, linV F v y) =
          (fun y => linV F a y) * (fun y => ∏ v ∈ s, linV F v y) := by
        funext y
        rw [Finset.prod_insert ha]
        rfl
      rw [e]
      exact (linV F a).hasTemperateGrowth.mul ih
  exact h Finset.univ

def archS : 𝓢(Fin 2 → UpperTheory.V.TR.Rinf F, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (polyV F) (gaussV F)

theorem archS_apply (y : Fin 2 → UpperTheory.V.TR.Rinf F) : archS F y = arch (y 0) (y 1) := by
  rw [archS, SchwartzMap.smulLeftCLM_apply_apply (polyV_hasTemperateGrowth F), gaussV_apply,
    smul_eq_mul, polyV, arch, Finset.prod_mul_distrib, Finset.mul_sum, Complex.exp_sum]
  simp only [linV_apply]

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.LibFresh
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.Fresh

variable {F : Type} [Field F] [NumberField F]

theorem ordI_mul_of_ne_bot (v : HeightOneSpectrum (𝓞 F)) {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    ordI v (I * J) = ordI v I + ordI v J := by
  unfold ordI
  rw [← Associates.mk_mul_mk]
  exact Associates.count_mul (Associates.mk_ne_zero.mpr hI) (Associates.mk_ne_zero.mpr hJ)
    v.associates_irreducible

theorem ordI_asIdeal_self (w : HeightOneSpectrum (𝓞 F)) : ordI w w.asIdeal = 1 := by
  unfold ordI
  exact Associates.count_self w.associates_irreducible

theorem hasDerivAt_chart_curve [IsTotallyReal F] (f : GA F 2 → ℂ) (g : GA F 2)
    (hd : DifferentiableAt ℝ (UpperTheory.V.TR.chart f g) (UpperTheory.V.TR.oneL F 2))
    (k : ℝ → GL (Fin 2) (UpperTheory.V.TR.Rinf F)) (X : UpperTheory.V.TR.Lie F 2) (h0 : k 0 = 1)
    (hk : HasDerivAt (fun t => UpperTheory.V.TR.toL (k t).val) X 0) :
    HasDerivAt (fun t => f (g * UpperTheory.V.TR.infGL F 2 (k t))) (UpperTheory.V.TR.lieD X f g) 0 := by
  unfold UpperTheory.V.TR.lieD
  have hf := hd.hasFDerivAt
  have hpt : UpperTheory.V.TR.oneL F 2 = (fun t => UpperTheory.V.TR.toL (k t).val) 0 := by
    simp only [h0, Units.val_one]
  rw [hpt] at hf
  have := hf.comp_hasDerivAt 0 hk
  rw [← hpt] at this
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  simp only [Function.comp_apply]
  exact (UpperTheory.V.TR.chart_val f g (k t)).symm

end UpperTheory.HilbertEisensteinWeightOne.Fresh
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SigmaFinitePosRealMeasure
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem absD_mul (g h : GA F 2) : absD (g * h) = absD g * absD h := by
  simp only [absD, map_mul, Positive.val_mul]

theorem absD_pos (g : GA F 2) : 0 < absD g := (IdeleGroup.ideleModule F _).2

theorem ideleModule_infId (d : (UpperTheory.V.TR.Rinf F)ˣ) :
    (IdeleGroup.ideleModule F (UpperTheory.V.TR.infId F d) : ℝ) = ∏ v, |(d : UpperTheory.V.TR.Rinf F) v| := by
  rw [ideleModule_apply]
  have h2 : finiteModule (UpperTheory.V.TR.infId F d) = 1 := by
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    change ‖(((1 : Ad F) - UpperTheory.V.TR.sInf F 1 + UpperTheory.V.TR.sInf F (d : UpperTheory.V.TR.Rinf F) : Ad F)).2 v‖ = 1
    change ‖((1 : Af F) - 0 + 0) v‖ = 1
    simp
  rw [h2, mul_one, infiniteModule]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hm : w.mult = 1 := by
    unfold InfinitePlace.mult; rw [if_pos (IsTotallyReal.isReal w)]
  rw [hm, pow_one]
  change ‖(((1 : Ad F) - UpperTheory.V.TR.sInf F 1 + UpperTheory.V.TR.sInf F (d : UpperTheory.V.TR.Rinf F) : Ad F)).1 w‖ = _
  change ‖((1 : InfiniteAdeleRing F) - UpperTheory.V.TR.infEq F 1 + UpperTheory.V.TR.infEq F (d : UpperTheory.V.TR.Rinf F)) w‖ = _
  rw [map_one, sub_self, zero_add]
  change ‖(InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm ((d : UpperTheory.V.TR.Rinf F) w)‖ = _
  set e := InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)
  have he : ∀ r, (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm r = e.symm r :=
    fun _ => rfl
  rw [he, ← dist_zero_right, ← Real.norm_eq_abs, ← dist_zero_right]
  have h0 : e.symm 0 = 0 := by
    rw [← he]; exact map_zero _
  rw [← h0, e.symm.dist_eq]

theorem absD_infGL (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    absD (UpperTheory.V.TR.infGL F 2 y) = ∏ v, |(Matrix.det (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F))) v| := by
  rw [absD, UpperTheory.V.TR.det_infGL, ideleModule_infId]
  rfl

theorem absD_scalar_mul (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) (g : GA F 2) :
    absD (Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) * g) =
      (t : ℝ) ^ 2 * absD g := by
  rw [absD_mul]
  congr 1
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2)
      (moduleSection (w0 F) t * (u : Ideles F))) = (moduleSection (w0 F) t * (u : Ideles F)) ^ 2 := by
    ext
    simp [sq]
    ring
  have hu : IdeleGroup.ideleModule F (u : Ideles F) = 1 := u.2
  rw [absD, hdet, map_pow, map_mul, ideleModule_moduleSection, hu, mul_one]
  rfl

theorem norm_hchar_of_finOrder {χ : HChar F} (hχ : IsOfFinOrder χ) (a : Ideles F) :
    ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, hn, hpow⟩ := hχ.exists_pow_eq_one
  have h1 : (χ.1 a) ^ n = 1 := by
    have := congrArg (fun ψ : HChar F => ψ.1 a) hpow
    simpa using this
  have h2 : ‖((χ.1 a : ℂˣ) : ℂ)‖ ^ n = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2

theorem measurableEmbedding_expPos : MeasurableEmbedding expPos :=
  expPosHomeomorph.measurableEmbedding

instance sigmaFinite_posRealMeasure : SigmaFinite posRealMeasure := by
  rw [posRealMeasure_eq_map_expPos]
  exact measurableEmbedding_expPos.sigmaFinite_map

theorem measurableSet_ge_one : MeasurableSet {t : {r : ℝ // 0 < r} | 1 ≤ (t : ℝ)} :=
  measurable_subtype_coe measurableSet_Ici

theorem measurableSet_lt_one : MeasurableSet {t : {r : ℝ // 0 < r} | (t : ℝ) < 1} :=
  measurable_subtype_coe measurableSet_Iio

theorem integrableOn_ge_one {r : ℕ} (hr : 2 ≤ r) :
    IntegrableOn (fun t : {r : ℝ // 0 < r} => ((t : ℝ) ^ r)⁻¹ * (t : ℝ)) {t | 1 ≤ (t : ℝ)} posRealMeasure := by
  rw [posRealMeasure_eq_map_expPos, IntegrableOn,
    measurableEmbedding_expPos.restrict_map, measurableEmbedding_expPos.integrable_map_iff]
  have hpre : expPos ⁻¹' {t : {r : ℝ // 0 < r} | 1 ≤ (t : ℝ)} = Set.Ici 0 := by
    ext x; simp [Real.one_le_exp_iff]
  rw [hpre]
  have hf : (fun t : {r : ℝ // 0 < r} => ((t : ℝ) ^ r)⁻¹ * (t : ℝ)) ∘ expPos =
      fun x => Real.exp ((1 - (r : ℝ)) * x) := by
    funext x
    simp only [Function.comp_apply, coe_expPos]
    rw [← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add]
    congr 1; ring
  rw [hf]
  have hneg : (1 - (r : ℝ)) < 0 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  exact (integrableOn_exp_mul_Ioi hneg 0).congr_set_ae Ioi_ae_eq_Ici.symm

theorem integrableOn_lt_one {r : ℕ} (hr : 2 ≤ r) :
    IntegrableOn (fun t : {r : ℝ // 0 < r} => (t : ℝ) ^ r * (t : ℝ)⁻¹) {t | (t : ℝ) < 1} posRealMeasure := by
  rw [posRealMeasure_eq_map_expPos, IntegrableOn,
    measurableEmbedding_expPos.restrict_map, measurableEmbedding_expPos.integrable_map_iff]
  have hpre : expPos ⁻¹' {t : {r : ℝ // 0 < r} | (t : ℝ) < 1} = Set.Iio 0 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, coe_expPos, Set.mem_Iio]
    rw [← Real.exp_zero, Real.exp_lt_exp]
  rw [hpre]
  have hf : (fun t : {r : ℝ // 0 < r} => (t : ℝ) ^ r * (t : ℝ)⁻¹) ∘ expPos =
      fun x => Real.exp (((r : ℝ) - 1) * x) := by
    funext x
    simp only [Function.comp_apply, coe_expPos]
    rw [← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add]
    congr 1; ring
  rw [hf]
  have hpos : 0 < ((r : ℝ) - 1) := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  exact (integrableOn_exp_mul_Iic hpos 0).mono_set Set.Iio_subset_Iic_self

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.CentralCharacterHolds
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne

namespace EisensteinCentralCharacter

variable {F : Type} [Field F] [NumberField F]

theorem thetaS_scalar_diagonal (Ψ : (Fin 2 → Ad F) → ℂ) (k : Fˣ) (h : GA F 2) :
    thetaS Ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) (diagonal F k : Ideles F) * h) = thetaS Ψ h := by
  unfold thetaS
  let e : {ξ : Fin 2 → F // ξ ≠ 0} ≃ {ξ : Fin 2 → F // ξ ≠ 0} :=
    { toFun := fun ξ => ⟨(k : F) • ξ.1, smul_ne_zero k.ne_zero ξ.2⟩
      invFun := fun ξ => ⟨((k⁻¹ : Fˣ) : F) • ξ.1, smul_ne_zero (k⁻¹).ne_zero ξ.2⟩
      left_inv := fun ξ => Subtype.ext (by simp [smul_smul])
      right_inv := fun ξ => Subtype.ext (by simp [smul_smul]) }
  have key : ∀ ξ : Fin 2 → F,
      rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) (diagonal F k : Ideles F) * h : GA F 2) :
        Matrix (Fin 2) (Fin 2) (Ad F)) = rowA ((k : F) • ξ) ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F)) := by
    intro ξ
    rw [Units.val_mul, ← Matrix.vecMul_vecMul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    congr 1
    funext i
    rw [Matrix.vecMul_diagonal]
    simp [rowA, coe_diagonal, mul_comm]
  refine Eq.trans ?_ (e.tsum_eq fun ξ => Ψ (rowA ξ.1 ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F))))
  exact tsum_congr fun ξ => by rw [key]; rfl

theorem hchar_diagonal (ω : HChar F) (k : Fˣ) : ω.1 (diagonal F k) = 1 := ω.2.2 k

theorem absD_nonneg (g : GA F 2) : 0 ≤ absD g := (IdeleGroup.ideleModule F _).2.le

theorem absD_scalar_mul (z : Ideles F) (g : GA F 2) :
    absD (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) =
      ((IdeleGroup.ideleModule F z : ℝ)) ^ 2 * absD g := by
  unfold absD
  rw [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_mul, map_pow]
  rfl

theorem eisInt_mul_diag [IsTotallyReal F] (ω : HChar F) (Ψ : (Fin 2 → Ad F) → ℂ) (g : GA F 2) (t : {r : ℝ // 0 < r})
    (u : normOneSubgroup F) (k : Fˣ) :
    eisInt ω Ψ g t (u * diagonalToNormOne F k) = eisInt ω Ψ g t u := by
  unfold eisInt
  have h : moduleSection (w0 F) t * ((u * diagonalToNormOne F k : normOneSubgroup F) : Ideles F) =
      diagonal F k * (moduleSection (w0 F) t * (u : Ideles F)) := by
    rw [Subgroup.coe_mul, coe_diagonalToNormOne]
    ac_rfl
  rw [h, map_mul (Matrix.GeneralLinearGroup.scalar (Fin 2)),
    mul_assoc (Matrix.GeneralLinearGroup.scalar (Fin 2) (diagonal F k)), thetaS_scalar_diagonal,
    map_mul ω.1, hchar_diagonal, one_mul]

theorem eisInt_scalar [IsTotallyReal F] (ω : HChar F) (Ψ : (Fin 2 → Ad F) → ℂ) (z : Ideles F) (g : GA F 2)
    (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) :
    eisInt ω Ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) t u =
      ((ω.1 z : ℂˣ) : ℂ) * eisInt ω Ψ g (t * (normOneSplitting (w0 F) z).2)
        (u * (normOneSplitting (w0 F) z).1) := by
  set p := normOneSplitting (w0 F) z with hp
  have hz : z = (p.1 : Ideles F) * moduleSection (w0 F) p.2 := by
    rw [← normOneSplitting_symm_apply, hp, ContinuousMulEquiv.symm_apply_apply]
  have ht0 : (p.2 : ℝ) = (IdeleGroup.ideleModule F z : ℝ) := rfl
  have hmul : moduleSection (w0 F) (t * p.2) * ((u * p.1 : normOneSubgroup F) : Ideles F) =
      (moduleSection (w0 F) t * (u : Ideles F)) * z := by
    rw [hz, map_mul, Subgroup.coe_mul]
    ac_rfl
  have hsc : Matrix.GeneralLinearGroup.scalar (Fin 2) ((moduleSection (w0 F) t * (u : Ideles F)) * z) * g =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) := by
    rw [map_mul, mul_assoc]
  have hω : ((ω.1 ((moduleSection (w0 F) t * (u : Ideles F)) * z) : ℂˣ) : ℂ) =
      ((ω.1 (moduleSection (w0 F) t * (u : Ideles F)) : ℂˣ) : ℂ) * ((ω.1 z : ℂˣ) : ℂ) := by
    rw [map_mul ω.1, Units.val_mul]
  have habs : ((IdeleGroup.ideleModule F z : ℝ) ^ 2 * absD g) ^ ((1 : ℝ) / 2) =
      (IdeleGroup.ideleModule F z : ℝ) * absD g ^ ((1 : ℝ) / 2) := by
    have h0 : 0 ≤ (IdeleGroup.ideleModule F z : ℝ) := (IdeleGroup.ideleModule F z).2.le
    rw [Real.mul_rpow (by positivity) (absD_nonneg g), ← Real.rpow_natCast,
      ← Real.rpow_mul h0]
    norm_num
  have hc : (((t * p.2 : {r : ℝ // 0 < r}) : ℝ) : ℂ) =
      ((t : ℝ) : ℂ) * ((IdeleGroup.ideleModule F z : ℝ) : ℂ) := by
    rw [← ht0, ← Complex.ofReal_mul]
    rfl
  unfold eisInt
  rw [hmul, hsc, absD_scalar_mul, habs, hω, hc]
  have hωz : ((ω.1 z : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hωA : ((ω.1 (moduleSection (w0 F) t * (u : Ideles F)) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  generalize thetaS Ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) *
    (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g)) = T
  generalize ((ω.1 z : ℂˣ) : ℂ) = a at hωz ⊢
  generalize ((ω.1 (moduleSection (w0 F) t * (u : Ideles F)) : ℂˣ) : ℂ) = b at hωA ⊢
  push_cast
  field_simp

theorem setIntegral_fd_mul (f : normOneSubgroup F → ℂ)
    (hf : ∀ (k : Fˣ) (u : normOneSubgroup F), f (u * diagonalToNormOne F k) = f u) (u0 : normOneSubgroup F) :
    ∫ u in normOneFundamentalDomain F, f (u * u0) ∂normOneMeasure F =
      ∫ u in normOneFundamentalDomain F, f u ∂normOneMeasure F := by
  have hE := isFundamentalDomain_normOneFundamentalDomain F (normOneMeasure F)
  have hE' : IsFundamentalDomain (diagonalNormOne F).op
      ((fun u => u * u0⁻¹) ⁻¹' normOneFundamentalDomain F) (normOneMeasure F) := by
    refine hE.preimage_of_equiv (e := id)
      (measurePreserving_mul_right (normOneMeasure F) u0⁻¹).quasiMeasurePreserving Function.bijective_id ?_
    intro γ x
    show (γ • x) * u0⁻¹ = γ • (x * u0⁻¹)
    simp only [Subgroup.smul_def, MulOpposite.smul_eq_mul_unop]
    exact mul_right_comm _ _ _
  have h1 : ∫ u in normOneFundamentalDomain F, f (u * u0) ∂normOneMeasure F =
      ∫ v in (fun u => u * u0⁻¹) ⁻¹' normOneFundamentalDomain F, f v ∂normOneMeasure F := by
    have := (measurePreserving_mul_right (normOneMeasure F) u0).setIntegral_preimage_emb
      (measurableEmbedding_mulRight u0) f ((fun u => u * u0⁻¹) ⁻¹' normOneFundamentalDomain F)
    rw [← this]
    congr 2
    ext x
    simp
  rw [h1]
  refine hE'.setIntegral_eq hE ?_
  intro γ x
  rw [Subgroup.smul_def, MulOpposite.smul_eq_mul_unop]
  have hm : ((γ : (normOneSubgroup F)ᵐᵒᵖ)).unop ∈ diagonalNormOne F := Subgroup.mem_op.1 γ.2
  obtain ⟨k, hk⟩ := Subgroup.mem_subgroupOf.1 hm
  have he : ((γ : (normOneSubgroup F)ᵐᵒᵖ)).unop = diagonalToNormOne F k := Subtype.ext hk.symm
  rw [he, hf]

end EisensteinCentralCharacter

open EisensteinCentralCharacter in
theorem central_character_holds : SPois → SInt → SSmooth → SCent := by
  intro _ _ _ F _ _ _ ω c _ z g
  have h1 : ∀ t : {r : ℝ // 0 < r},
      ∫ u in normOneFundamentalDomain F, eisInt ω (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) t u
        ∂normOneMeasure F =
      ((ω.1 z : ℂˣ) : ℂ) * ∫ u in normOneFundamentalDomain F,
        eisInt ω (Phi c) g (t * (normOneSplitting (w0 F) z).2) u ∂normOneMeasure F := by
    intro t
    simp only [eisInt_scalar ω (Phi c) z g t]
    rw [integral_const_mul, setIntegral_fd_mul _ (fun k u => eisInt_mul_diag ω (Phi c) g _ u k)]
  unfold Eis
  simp only [h1]
  rw [integral_const_mul]
  exact congrArg (((ω.1 z : ℂˣ) : ℂ) * ·) (integral_mul_right_eq_self
    (fun t => ∫ u in normOneFundamentalDomain F, eisInt ω (Phi c) g t u ∂normOneMeasure F)
    (normOneSplitting (w0 F) z).2)

end UpperTheory.HilbertEisensteinWeightOne
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.FiniteSupportOfHyp
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix nonZeroDivisors
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem finite_support_of_hyp {χ : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (H : Hyp χ c) :
    {w | c w ≠ 0}.Finite := by
  obtain ⟨m, hm, h⟩ := (isOfFinOrder_iff_pow_eq_one).mp H.fin
  have ho := GlobalTheory.HeckeGal.isOpen_ker_of_pow χ.1 χ.2.1 hm fun x => congrArg (fun ξ : HChar F => ξ.1 x) h
  obtain ⟨S, M, hS, key⟩ := GlobalTheory.OpenIdeleCongr.localIdele_mem_of_isOpen χ.1.ker ho
  refine hS.subset fun w hw => ?_
  by_contra hwS
  apply hw
  have h0 : (0 : ℕ) ∈ {n : ℕ | ∀ x : (w.adicCompletion F)ˣ, IsUnitAt w x →
      Valued.v ((x : w.adicCompletion F) - 1) ≤ WithZero.exp (-(n : ℤ)) → χ.loc w x = 1} := by
    intro x hx _
    exact key w x hx fun h => absurd h hwS
  exact Nat.le_zero.mp ((H.cond w).2 h0)

omit [IsTotallyReal F] in
theorem exists_int_of_val (x : F)
    (h : ∀ w : HeightOneSpectrum (𝓞 F), Valued.v (pLoc F w (algebraMap F (Af F) x)) ≤ 1) :
    ∃ s : 𝓞 F, x = (s : F) := by
  have h' : ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F x ≤ 1 := by
    intro w
    have := h w
    rwa [show pLoc F w (algebraMap F (Af F) x) = (x : w.adicCompletion F) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
  obtain ⟨s, hs⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F x h'
  exact ⟨s, hs.symm⟩


omit [IsTotallyReal F] in
theorem exists_den_compact {ι : Type} [Finite ι] {C : Set (Ideles F)} (hC : IsCompact C)
    (f : ι → Ideles F → Af F) (hf : ∀ i, Continuous (f i)) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ a ∈ C, ∀ i, ∀ w : HeightOneSpectrum (𝓞 F),
      Valued.v (pLoc F w (algebraMap F (Af F) (d : F) * f i a)) ≤ 1 := by
  have hS : IsCompact (⋃ i, f i '' C) := isCompact_iUnion fun i => hC.image (hf i)
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hS
  exact ⟨d, hd0, fun a ha i w => hd _ (Set.mem_iUnion.mpr ⟨i, a, ha, rfl⟩) w⟩

omit [IsTotallyReal F] in
theorem val_sum_two_le {w : HeightOneSpectrum (𝓞 F)} (x : Fin 2 → w.adicCompletion F)
    (h : ∀ j, Valued.v (x j) ≤ 1) : Valued.v (∑ j, x j) ≤ 1 := by
  rw [Fin.sum_univ_two]
  exact le_trans (Valuation.map_add _ _ _) (max_le (h 0) (h 1))

omit [IsTotallyReal F] in
theorem coe_Mcol_apply' (g : GA F 2) (a : Ideles F) (j i : Fin 2) :
    ((g⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) j i =
      ((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) j i * ((a⁻¹ : Ideles F) : Ad F) := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal]

omit [IsTotallyReal F] in
theorem coe_Mrow_apply' (g : GA F 2) (a : Ideles F) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * g : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) i j =
      ((a : Ideles F) : Ad F) * ((g : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) i j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal]

omit [IsTotallyReal F] in
theorem scalar_mul_mul_inv (g : GA F 2) (a : Ideles F) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * g : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *
      ((g⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) = 1 := by
  rw [← Units.val_mul]
  simp [mul_assoc]

omit [IsTotallyReal F] in
theorem pFin_algebraMap (x : F) : pFin F (algebraMap F (Ad F) x) = algebraMap F (Af F) x := rfl


theorem exists_den_row (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) {C : Set (Ideles F)} (hC : IsCompact C) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ a ∈ C, ∀ ξ : Fin 2 → F,
      (∀ w, Valued.v (pLoc F w (pFin F ((rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * g : GA F 2) :
          Matrix (Fin 2) (Fin 2) (Ad F))) 0))) ≤ WithZero.exp (-(c w : ℤ)) ∧
        Valued.v (pLoc F w (pFin F ((rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * g : GA F 2) :
          Matrix (Fin 2) (Fin 2) (Ad F))) 1)) - 1) ≤ WithZero.exp (-(c w : ℤ))) →
      ∀ i, ∃ s : 𝓞 F, (d : F) * ξ i = s := by
  obtain ⟨d, hd0, hd⟩ := exists_den_compact (ι := Fin 2 × Fin 2) hC
    (fun p a => pFin F (((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) p.1 p.2) *
      ((IdeleGroup.toFinite F a⁻¹ : (Af F)ˣ) : Af F))
    (fun p => continuous_const.mul (Units.continuous_val.comp
      ((IdeleGroup.continuous_toFinite (K := F)).comp continuous_inv)))
  refine ⟨d, hd0, fun a ha ξ hξ i => ?_⟩
  set row := rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * g : GA F 2) :
    Matrix (Fin 2) (Fin 2) (Ad F)) with hrow_def
  have hle1 : ∀ w : HeightOneSpectrum (𝓞 F), WithZero.exp (-(c w : ℤ)) ≤ 1 := fun w => by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hint : ∀ j w, Valued.v (pLoc F w (pFin F (row j))) ≤ 1 := by
    intro j w
    obtain ⟨h0, h1⟩ := hξ w
    fin_cases j
    · exact h0.trans (hle1 w)
    · have e : pLoc F w (pFin F (row 1)) = (pLoc F w (pFin F (row 1)) - 1) + 1 := by ring
      change Valued.v (pLoc F w (pFin F (row 1))) ≤ 1
      rw [e]
      exact Valuation.map_add_le _ (h1.trans (hle1 w)) (by rw [Valuation.map_one])
  have hrow : rowA ξ = row ᵥ* ((g⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F)) := by
    rw [hrow_def, Matrix.vecMul_vecMul, scalar_mul_mul_inv, Matrix.vecMul_one]
  have hx : algebraMap F (Af F) (ξ i) = ∑ j, pFin F (row j) *
      (pFin F (((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) j i) *
        ((IdeleGroup.toFinite F a⁻¹ : (Af F)ˣ) : Af F)) := by
    have h2 := congrArg (fun v => pFin F (v i)) hrow
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.vecMul, dotProduct, coe_Mcol_apply', map_sum, map_mul] at h2
    rw [← pFin_algebraMap]
    exact h2
  apply exists_int_of_val
  intro w
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, hx, Finset.mul_sum, map_sum]
  apply val_sum_two_le
  intro j
  rw [mul_left_comm, map_mul, Valuation.map_mul]
  exact mul_le_one' (hint j w) (hd a ha (j, i) w)

omit [IsTotallyReal F] in
theorem exists_elem_col (c : HeightOneSpectrum (𝓞 F) → ℕ) (hc : {w | c w ≠ 0}.Finite) :
    ∃ e : 𝓞 F, e ≠ 0 ∧ ∀ w : HeightOneSpectrum (𝓞 F),
      Valued.v (pLoc F w (algebraMap F (Af F) (e : F))) ≤ WithZero.exp (-((c w : ℤ) + dd w)) := by
  classical
  set Cfr : FractionalIdeal (𝓞 F)⁰ F :=
    ∏ᶠ w : HeightOneSpectrum (𝓞 F), (w.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ (c w : ℤ)
  set Dfr : FractionalIdeal (𝓞 F)⁰ F := ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
  have hexp : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, (c w : ℤ) = 0 := by
    rw [Filter.eventually_cofinite]
    refine hc.subset fun w hw => ?_
    simpa using hw
  have hD0 : differentIdeal ℤ (𝓞 F) ≠ 0 := _root_.differentIdeal_ne_bot
  have hDfr0 : Dfr ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hD0
  have hCfr0 : Cfr ≠ 0 := by
    apply finprod_induction (p := fun I : FractionalIdeal (𝓞 F)⁰ F => I ≠ 0)
    · exact one_ne_zero
    · exact fun x y hx hy => mul_ne_zero hx hy
    · exact fun w => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot)
  have hJ0 : Cfr * Dfr ≠ 0 := mul_ne_zero hCfr0 hDfr0
  have hcount : ∀ w : HeightOneSpectrum (𝓞 F), FractionalIdeal.count F w (Cfr * Dfr) = (c w : ℤ) + dd w := by
    intro w
    rw [FractionalIdeal.count_mul F w hCfr0 hDfr0, FractionalIdeal.count_finprod F w _ hexp,
      FractionalIdeal.count_coe F w hD0]
    rfl
  obtain ⟨k, hkJ, hk0⟩ : ∃ k ∈ Cfr * Dfr, k ≠ 0 := by
    have hne : ((Cfr * Dfr : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) ≠ ⊥ := by
      rw [Ne, FractionalIdeal.coeToSubmodule_eq_bot]
      exact hJ0
    exact Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hval : ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F k ≤ WithZero.exp (-((c w : ℤ) + dd w)) := fun w => by
    have h1 := valuation_le_of_mem_fractionalIdeal w hkJ
    rwa [hcount] at h1
  have hdd : ∀ w : HeightOneSpectrum (𝓞 F), 0 ≤ dd w := fun w => by unfold dd; positivity
  have hle1 : ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F k ≤ 1 := fun w =>
    (hval w).trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; have := hdd w; omega)
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F k hle1
  have hrk : (r : F) = k := hr
  refine ⟨r, ?_, fun w => ?_⟩
  · rintro rfl
    apply hk0
    rw [← hrk]
    rfl
  · change Valued.v ((r : F) : w.adicCompletion F) ≤ _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hrk]
    exact hval w

theorem exists_den_col (c : HeightOneSpectrum (𝓞 F) → ℕ) (hc : {w | c w ≠ 0}.Finite) (g : GA F 2)
    {C : Set (Ideles F)} (hC : IsCompact C) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ a ∈ C, ∀ ξ : Fin 2 → F,
      (∀ w, Valued.v (pLoc F w (pFin F ((((g⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ : GA F 2) :
          Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ) 0))) ≤ WithZero.exp ((c w : ℤ) + dd w) ∧
        Valued.v (pLoc F w (pFin F ((((g⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ : GA F 2) :
          Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ) 1))) ≤ WithZero.exp ((c w : ℤ) + dd w)) →
      ∀ i, ∃ s : 𝓞 F, (d : F) * ξ i = s := by
  obtain ⟨e, he0, he⟩ := exists_elem_col c hc
  obtain ⟨d, hd0, hd⟩ := exists_den_compact (ι := Fin 2 × Fin 2) hC
    (fun p a => ((IdeleGroup.toFinite F a : (Af F)ˣ) : Af F) *
      pFin F (((g : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) p.1 p.2))
    (fun p => (Units.continuous_val.comp (IdeleGroup.continuous_toFinite (K := F))).mul continuous_const)
  refine ⟨d * e, mul_ne_zero hd0 he0, fun a ha ξ hξ i => ?_⟩
  set col := ((g⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ : GA F 2) :
    Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ with hcol_def
  have hint : ∀ j w, Valued.v (pLoc F w (algebraMap F (Af F) (e : F) * pFin F (col j))) ≤ 1 := by
    intro j w
    obtain ⟨h0, h1⟩ := hξ w
    have hj : Valued.v (pLoc F w (pFin F (col j))) ≤ WithZero.exp ((c w : ℤ) + dd w) := by
      fin_cases j
      · exact h0
      · exact h1
    rw [map_mul, Valuation.map_mul]
    calc Valued.v (pLoc F w (algebraMap F (Af F) (e : F))) * Valued.v (pLoc F w (pFin F (col j)))
        ≤ WithZero.exp (-((c w : ℤ) + dd w)) * WithZero.exp ((c w : ℤ) + dd w) := mul_le_mul' (he w) hj
      _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
  have hcol : rowA ξ = ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * g : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ col := by
    rw [hcol_def, Matrix.mulVec_mulVec, scalar_mul_mul_inv, Matrix.one_mulVec]
  have hx : algebraMap F (Af F) (ξ i) = ∑ j, (((IdeleGroup.toFinite F a : (Af F)ˣ) : Af F) *
      pFin F (((g : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) i j)) * pFin F (col j) := by
    have h2 := congrArg (fun v => pFin F (v i)) hcol
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, coe_Mrow_apply', map_sum, map_mul] at h2
    rw [← pFin_algebraMap]
    exact h2
  apply exists_int_of_val
  intro w
  have e1 : algebraMap F (Af F) ((d : F) * (e : F) * ξ i) = ∑ j,
      (algebraMap F (Af F) (d : F) * (((IdeleGroup.toFinite F a : (Af F)ˣ) : Af F) *
        pFin F (((g : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) i j))) *
      (algebraMap F (Af F) (e : F) * pFin F (col j)) := by
    rw [map_mul, map_mul, hx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have e2 : (((d * e : 𝓞 F)) : F) = (d : F) * (e : F) := by push_cast; ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e2, e1, map_sum]
  apply val_sum_two_le
  intro j
  rw [map_mul, Valuation.map_mul]
  exact mul_le_one' (hd a ha (i, j) w) (hint j w)

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
end
end
