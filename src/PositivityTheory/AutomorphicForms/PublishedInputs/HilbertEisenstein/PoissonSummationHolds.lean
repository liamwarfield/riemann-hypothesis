module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Imports
noncomputable section

open NumberField NumberField.mixedEmbedding
open scoped Classical

namespace UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

def toR : mixedSpace F →ₗ[ℝ] UpperTheory.V.TR.Rinf F where
  toFun x v := x.1 ⟨v, IsTotallyReal.isReal v⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.IsProbabilityMeasureComplexPart
noncomputable section

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory GroundTheory.Global Complex
open scoped Classical FourierTransform

namespace UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic

def gP (a b : ℝ) : ℂ :=
  ((a : ℂ) + I * (b : ℂ)) * Complex.exp (-(Real.pi : ℂ) * ((a : ℂ) ^ 2 + (b : ℂ) ^ 2))

theorem gP_eq (a b : ℝ) :
    gP a b = (a : ℂ) * realGaussian a * realGaussian b +
      I * (realGaussian a * ((b : ℂ) * realGaussian b)) := by
  unfold gP realGaussian
  rw [show -(Real.pi : ℂ) * ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) =
      -(Real.pi : ℂ) * (a : ℂ) ^ 2 + -(Real.pi : ℂ) * (b : ℂ) ^ 2 by ring, Complex.exp_add]
  ring

theorem continuous_gP : Continuous fun p : ℝ × ℝ => gP p.1 p.2 := by
  unfold gP
  fun_prop

theorem continuous_charR (a : ℝ) : Continuous fun t : ℝ => ((𝐞 (-(t * a)) : Circle) : ℂ) :=
  continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))

theorem integrable_charR_mul {f : ℝ → ℂ} (hf : Integrable f) (a : ℝ) :
    Integrable (fun t : ℝ => ((𝐞 (-(t * a)) : Circle) : ℂ) * f t) := by
  refine hf.norm.mono' ((continuous_charR a).aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun t => by simp [Circle.norm_coe]

theorem integral_charR_even (a : ℝ) :
    ∫ t : ℝ, ((𝐞 (-(t * a)) : Circle) : ℂ) * realGaussian t = realGaussian a := by
  have h := congrFun fourier_realGaussian a
  rw [Real.fourier_real_eq] at h
  simpa only [Circle.smul_def, smul_eq_mul] using h

theorem integral_charR_odd (a : ℝ) :
    ∫ t : ℝ, ((𝐞 (-(t * a)) : Circle) : ℂ) * ((t : ℂ) * realGaussian t) =
      -I * ((a : ℂ) * realGaussian a) := by
  have h := congrFun fourier_realGaussianOdd a
  rw [Real.fourier_real_eq] at h
  simpa only [Circle.smul_def, smul_eq_mul, realGaussianOdd, realGaussian] using h

theorem integral_place (a b : ℝ) :
    ∫ p : ℝ × ℝ, ((𝐞 (-(p.1 * a + p.2 * b)) : Circle) : ℂ) * gP p.1 p.2 = -I * gP a b := by
  have hsplit : ∀ p : ℝ × ℝ, ((𝐞 (-(p.1 * a + p.2 * b)) : Circle) : ℂ) * gP p.1 p.2 =
      (((𝐞 (-(p.1 * a)) : Circle) : ℂ) * ((p.1 : ℂ) * realGaussian p.1)) *
          (((𝐞 (-(p.2 * b)) : Circle) : ℂ) * realGaussian p.2) +
        I * ((((𝐞 (-(p.1 * a)) : Circle) : ℂ) * realGaussian p.1) *
          (((𝐞 (-(p.2 * b)) : Circle) : ℂ) * ((p.2 : ℂ) * realGaussian p.2))) := by
    intro p
    rw [neg_add, AddChar.map_add_eq_mul, Circle.coe_mul, gP_eq]
    ring
  have hodd : Integrable (fun t : ℝ => (t : ℂ) * realGaussian t) := integrable_realGaussianOdd
  simp_rw [hsplit]
  rw [Measure.volume_eq_prod,
    integral_add ((integrable_charR_mul hodd a).mul_prod (integrable_charR_mul integrable_realGaussian b))
      (((integrable_charR_mul integrable_realGaussian a).mul_prod (integrable_charR_mul hodd b)).const_mul I),
    integral_const_mul,
    integral_prod_mul (fun t : ℝ => ((𝐞 (-(t * a)) : Circle) : ℂ) * ((t : ℂ) * realGaussian t))
      (fun t : ℝ => ((𝐞 (-(t * b)) : Circle) : ℂ) * realGaussian t),
    integral_prod_mul (fun t : ℝ => ((𝐞 (-(t * a)) : Circle) : ℂ) * realGaussian t)
      (fun t : ℝ => ((𝐞 (-(t * b)) : Circle) : ℂ) * ((t : ℂ) * realGaussian t)),
    integral_charR_even, integral_charR_even, integral_charR_odd, integral_charR_odd, gP_eq]
  ring

variable (F : Type) [Field F] [NumberField F]

theorem selfDualMeasure_eq_volume [IsTotallyReal F] : selfDualMeasure F = volume := by
  rw [selfDualMeasure, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, one_smul]

theorem isEmpty_complexPlaces [IsTotallyReal F] : IsEmpty {w : InfinitePlace F // IsComplex w} :=
  ⟨fun w => not_isComplex_iff_isReal.mpr (IsTotallyReal.isReal w.1) w.2⟩

theorem isProbabilityMeasure_complexPart [IsTotallyReal F] :
    IsProbabilityMeasure (volume : Measure ({w : InfinitePlace F // IsComplex w} → ℂ)) := by
  haveI := isEmpty_complexPlaces F
  have h : (volume : Measure ({w : InfinitePlace F // IsComplex w} → ℂ)) =
      Measure.dirac isEmptyElim := by
    rw [volume_pi, Measure.pi_of_empty]
  rw [h]
  infer_instance

def proj2 (x : Fin 2 → mixedSpace F) : {w : InfinitePlace F // IsReal w} → ℝ × ℝ :=
  fun w => ((x 0).1 w, (x 1).1 w)

theorem measurePreserving_proj2 [IsTotallyReal F] :
    MeasurePreserving (proj2 F) (GroundTheory.Automorphic.Adele2.mixedMeasure2 F) volume := by
  haveI := isProbabilityMeasure_complexPart F
  have h1 := measurePreserving_finTwoArrow (volume : Measure (mixedSpace F))
  have hf : MeasurePreserving (Prod.fst : mixedSpace F → ({w : InfinitePlace F // IsReal w} → ℝ))
      volume volume := by
    rw [Measure.volume_eq_prod]
    exact measurePreserving_fst
  have h2 := hf.prod hf
  have h3 := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ
    {w : InfinitePlace F // IsReal w}).symm
  have h : proj2 F = (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ
      {w : InfinitePlace F // IsReal w}).symm ∘ Prod.map Prod.fst Prod.fst ∘
      MeasurableEquiv.finTwoArrow := by
    funext x w
    rfl
  rw [h, GroundTheory.Automorphic.Adele2.mixedMeasure2, selfDualMeasure_eq_volume]
  exact h3.comp (h2.comp h1)

theorem arch_eq_prod [IsTotallyReal F] (x₀ x₁ : mixedSpace F) :
    arch (toR F x₀) (toR F x₁) = ∏ w : {w : InfinitePlace F // IsReal w}, gP (x₀.1 w) (x₁.1 w) :=
  (Fintype.prod_equiv (Equiv.subtypeUnivEquiv fun v => IsTotallyReal.isReal v) _ _
    fun _ => rfl).symm

theorem char_pairing_eq_prod [IsTotallyReal F] (x y : Fin 2 → mixedSpace F) :
    ((𝐞 (-GroundTheory.Automorphic.Adele2.mixedPairing2 F x y) : Circle) : ℂ) =
      ∏ w : {w : InfinitePlace F // IsReal w},
        ((𝐞 (-((x 0).1 w * (y 0).1 w + (x 1).1 w * (y 1).1 w)) : Circle) : ℂ) := by
  haveI := isEmpty_complexPlaces F
  rw [GroundTheory.Automorphic.Adele2.mixedPairing2, Fin.sum_univ_two, mixedTraceForm_apply',
    mixedTraceForm_apply']
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib, addChar_map_finsetSum]
  exact map_prod Circle.coeHom _ _

theorem mixedFourier2_arch [IsTotallyReal F] (y : Fin 2 → mixedSpace F) :
    GroundTheory.Automorphic.Adele2.mixedFourier2 F (fun u => arch (toR F (u 0)) (toR F (u 1))) y =
      (-Complex.I) ^ Fintype.card (InfinitePlace F) * arch (toR F (y 0)) (toR F (y 1)) := by
  set f : {w : InfinitePlace F // IsReal w} → ℝ × ℝ → ℂ := fun w p =>
    ((𝐞 (-(p.1 * (y 0).1 w + p.2 * (y 1).1 w)) : Circle) : ℂ) * gP p.1 p.2 with hfdef
  have hpt : ∀ x : Fin 2 → mixedSpace F,
      𝐞 (-GroundTheory.Automorphic.Adele2.mixedPairing2 F x y) • arch (toR F (x 0)) (toR F (x 1)) =
        ∏ w, f w (proj2 F x w) := by
    intro x
    rw [Circle.smul_def, smul_eq_mul, char_pairing_eq_prod, arch_eq_prod, ← Finset.prod_mul_distrib]
    rfl
  have hcont : Continuous fun z : {w : InfinitePlace F // IsReal w} → ℝ × ℝ => ∏ w, f w (z w) := by
    refine continuous_finsetProd _ fun w _ => ?_
    simp only [hfdef]
    refine Continuous.mul ?_ (continuous_gP.comp (continuous_apply w))
    exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  rw [GroundTheory.Automorphic.Adele2.mixedFourier2]
  simp_rw [hpt]
  rw [← integral_map (measurePreserving_proj2 F).aemeasurable hcont.aestronglyMeasurable,
    (measurePreserving_proj2 F).map_eq, integral_fintype_prod_volume_eq_prod f]
  simp only [hfdef, integral_place]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, arch_eq_prod,
    Fintype.card_congr (Equiv.subtypeUnivEquiv fun v : InfinitePlace F => IsTotallyReal.isReal v)]

end UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.ToRHomeomorphMixedSpace
noncomputable section

open NumberField NumberField.mixedEmbedding MeasureTheory GroundTheory.Global
open scoped FourierTransform Matrix Classical
open GlobalTheory.CuspRep

namespace UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic

theorem toR_homeomorphMixedSpace (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (x : Ad F) :
    toR F (homeomorphMixedSpace F x.1) = UpperTheory.V.TR.pInf F x := by
  funext v
  rfl

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

instance isEmpty_isComplex : IsEmpty {w : InfinitePlace F // InfinitePlace.IsComplex w} :=
  ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.2 w.2) (IsTotallyReal.isReal w.1)⟩

theorem norm_sq_mixedToEuclidean (u : mixedSpace F) :
    ‖mixedToEuclidean F u‖ ^ 2 = ∑ v, (toR F u v) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, mixedToEuclidean, ContinuousLinearEquiv.trans_apply,
    inner_toMixed_symm]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, mapComplexCoord_apply]
  rw [← Equiv.sum_comp (Equiv.subtypeUnivEquiv (fun v => IsTotallyReal.isReal v)).symm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [toR, sq]

theorem norm_sq_toEuclid2 (u : Fin 2 → mixedSpace F) :
    ‖GroundTheory.Automorphic.Adele2.toEuclid2 F u‖ ^ 2 = ∑ v, ((toR F (u 0) v) ^ 2 + (toR F (u 1) v) ^ 2) := by
  rw [GroundTheory.Automorphic.Adele2.toEuclid2_apply, WithLp.prod_norm_sq_eq_of_L2, Finset.sum_add_distrib,
    ← norm_sq_mixedToEuclidean, ← norm_sq_mixedToEuclidean]
  rfl

def coordCLM (i : Fin 2) (v : InfinitePlace F) : (Fin 2 → mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => toR F (u i) v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem coordCLM_apply (i : Fin 2) (v : InfinitePlace F) (u : Fin 2 → mixedSpace F) :
    coordCLM F i v u = toR F (u i) v := rfl

def lin (v : InfinitePlace F) : (Fin 2 → mixedSpace F) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (coordCLM F 0 v) + Complex.I • Complex.ofRealCLM.comp (coordCLM F 1 v)

theorem lin_apply (v : InfinitePlace F) (u : Fin 2 → mixedSpace F) :
    lin F v u = (toR F (u 0) v : ℂ) + Complex.I * (toR F (u 1) v : ℂ) := by
  simp [lin, coordCLM_apply]

theorem hasTemperateGrowth_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    (s : Finset ι) (f : ι → E → ℂ) (hf : ∀ i, (f i).HasTemperateGrowth) :
    (fun x => ∏ i ∈ s, f i x).HasTemperateGrowth := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h := (hf a).mul ih
    have e : (fun x => ∏ i ∈ insert a s, f i x) = (f a * fun x => ∏ i ∈ s, f i x) := by
      funext x
      simp [Finset.prod_insert ha]
    rw [e]
    exact h

def poly (u : Fin 2 → mixedSpace F) : ℂ := ∏ v, lin F v u

theorem hasTemperateGrowth_poly : (poly F).HasTemperateGrowth :=
  hasTemperateGrowth_prod _ (fun v u => lin F v u) fun v => (lin F v).hasTemperateGrowth

theorem exists_schwartz_arch :
    ∃ φ : SchwartzMap (Fin 2 → NumberField.mixedEmbedding.mixedSpace F) ℂ,
      ∀ u, φ u = arch (toR F (u 0)) (toR F (u 1)) := by
  refine ⟨SchwartzMap.smulLeftCLM ℂ (poly F)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (GroundTheory.Automorphic.Adele2.toEuclid2 F)
      (gaussianSchwartz _)), fun u => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_poly F)]
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    gaussianSchwartz_apply, smul_eq_mul]
  rw [norm_sq_toEuclid2, arch, Finset.prod_mul_distrib, poly]
  congr 1
  all_goals first
    | exact Finset.prod_congr rfl fun v _ => lin_apply F v u
    | (rw [← Complex.exp_sum, Complex.ofReal_exp]
       congr 1
       push_cast
       rw [Finset.mul_sum])

section Support

open Neutral.B1 hiding G IsPlaceOver Dec
open IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base

theorem finite_support_of_cond (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (hfin : IsOfFinOrder ω)
    (hc : ∀ w, UpperTheory.V.Sd.IsCondAt w ω (c w)) : {w | c w ≠ 0}.Finite := by
  obtain ⟨m, hm, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  have ho := GlobalTheory.HeckeGal.isOpen_ker_of_pow ω.1 ω.2.1 hm fun x => congrArg (fun ξ : HChar F => ξ.1 x) h
  obtain ⟨S, M, hS, key⟩ := GlobalTheory.OpenIdeleCongr.localIdele_mem_of_isOpen ω.1.ker ho
  refine hS.subset fun w hw => ?_
  by_contra hwS
  apply hw
  refine Nat.le_zero.1 ((hc w).2 ?_)
  simp only [Set.mem_ofPred_eq]
  intro x hu _
  exact key w x hu fun h => absurd h hwS

end Support

end UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic
end
end

noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open NumberField.mixedEmbedding MeasureTheory GroundTheory.Global GroundTheory.Automorphic.Adele2 UpperTheory.V.Sd UpperTheory.V.Published
open scoped Matrix Classical NumberField.AdeleRing nonZeroDivisors

namespace UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic

variable {F : Type} [Field F] [NumberField F]

def nId (c : HeightOneSpectrum (𝓞 F) → ℕ) : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  ∏ᶠ w, primeIdealUnit w ^ (c w : ℤ)

theorem count_nId {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite)
    (w : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F w ((nId c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) = c w :=
  count_finprod_primeIdealUnit_zpow _ (Filter.eventually_cofinite.2 (hc.subset fun v hv => by
    simp only [Set.mem_ofPred_eq] at hv ⊢
    exact_mod_cast hv)) w

theorem count_different (w : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F w ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = dd w := by
  rw [FractionalIdeal.count_coe F w differentIdeal_ne_bot]
  rfl

theorem mem_nId_iff {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (a : Af F) :
    (∀ w, Valued.v (pLoc F w a) ≤ WithZero.exp (-(c w : ℤ))) ↔ a ∈ idealFiniteAdeles (nId c) := by
  rw [mem_idealFiniteAdeles]
  refine forall_congr' fun w => ?_
  rw [count_nId hc]
  rfl

theorem mem_dual_iff {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (a : Af F) :
    (∀ w, Valued.v (pLoc F w a) ≤ WithZero.exp ((c w : ℤ) + dd w)) ↔
      a ∈ idealFiniteAdeles (traceDualIdeal F (nId c)) := by
  rw [mem_idealFiniteAdeles]
  refine forall_congr' fun w => ?_
  rw [count_traceDualIdeal, count_nId hc, count_different, neg_neg]
  rfl

theorem arch_zero [IsTotallyReal F] : arch (0 : UpperTheory.V.TR.Rinf F) 0 = 0 := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp)

def gFin (c : HeightOneSpectrum (𝓞 F) → ℕ) : (Fin 2 → Af F) → ℂ :=
  finiteTensor2 ![cosetIndicator (nId c) 0, cosetIndicator (nId c) 1]

theorem gFin_mem (c : HeightOneSpectrum (𝓞 F) → ℕ) : gFin c ∈ finiteSchwartzBruhat2 F :=
  finiteTensor2_mem fun i => by
    fin_cases i
    · exact cosetIndicator_mem_finiteSchwartzBruhat _ _
    · exact cosetIndicator_mem_finiteSchwartzBruhat _ _

variable [IsTotallyReal F]

theorem phi_eq {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite)
    (φ : SchwartzMap (Fin 2 → mixedSpace F) ℂ) (hφ : ∀ u, φ u = arch (toR F (u 0)) (toR F (u 1))) :
    Phi c = schwartzBruhatTensor2 φ (gFin c) := by
  funext x
  rw [schwartzBruhatTensor2, hφ, gFin, finiteTensor2_apply, Phi]
  simp only [infPart, finPart, toR_homeomorphMixedSpace, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, cosetIndicator_apply, sub_zero]
  congr 1
  have h0 := mem_nId_iff hc (pFin F (x 0))
  have h1 := mem_nId_iff hc (pFin F (x 1) - 1)
  simp only [map_sub, map_one] at h1
  by_cases a : (x 0).2 ∈ idealFiniteAdeles (nId c) <;> by_cases b : (x 1).2 - 1 ∈ idealFiniteAdeles (nId c)
  · rw [if_pos fun w => ⟨h0.2 a w, h1.2 b w⟩, if_pos a, if_pos b, mul_one]
  · rw [if_neg (fun h => b (h1.1 fun w => (h w).2)), if_neg b, mul_zero]
  · rw [if_neg (fun h => a (h0.1 fun w => (h w).1)), if_neg a, zero_mul]
  · rw [if_neg (fun h => a (h0.1 fun w => (h w).1)), if_neg a, zero_mul]

def cst (c : HeightOneSpectrum (𝓞 F) → ℕ) : ℂ :=
  (-Complex.I) ^ Fintype.card (InfinitePlace F) *
    (((finiteAdeleMeasure F (idealFiniteAdeles (nId c))).toReal : ℝ) : ℂ) ^ 2

theorem cst_ne_zero (c : HeightOneSpectrum (𝓞 F) → ℕ) : cst c ≠ 0 := by
  refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero)) (pow_ne_zero _ ?_)
  rw [Complex.ofReal_ne_zero]
  exact ENNReal.toReal_ne_zero.mpr ⟨(isOpen_idealFiniteAdeles _).measure_ne_zero _ ⟨0, zero_mem _⟩,
    finiteAdeleMeasure_idealFiniteAdeles_ne_top _⟩

theorem fourier_phi {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite)
    (φ : SchwartzMap (Fin 2 → mixedSpace F) ℂ) (hφ : ∀ u, φ u = arch (toR F (u 0)) (toR F (u 1)))
    (y : Fin 2 → Ad F) :
    adelicFourier2 F (Phi c) y = cst c * PhiH c y := by
  have hφ' : (⇑φ : (Fin 2 → mixedSpace F) → ℂ) = fun u => arch (toR F (u 0)) (toR F (u 1)) := funext hφ
  rw [phi_eq hc φ hφ, adelicFourier2_schwartzBruhatTensor2, schwartzBruhatTensor2,
    mixedFourier2Schwartz_apply, hφ', mixedFourier2_arch, gFin, finiteFourier2_finiteTensor2,
    finiteTensor2_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    finiteFourier_cosetIndicator, zero_mul, one_mul, AddChar.map_zero_eq_one, Circle.coe_one,
    infPart, finPart, toR_homeomorphMixedSpace, PhiH, cst]
  have h0 := mem_dual_iff hc (pFin F (y 0))
  have h1 := mem_dual_iff hc (pFin F (y 1))
  rw [show pFin F (y 1) = (y 1).2 from rfl]
  by_cases a : (y 0).2 ∈ idealFiniteAdeles (traceDualIdeal F (nId c)) <;>
    by_cases b : (y 1).2 ∈ idealFiniteAdeles (traceDualIdeal F (nId c))
  · rw [if_pos fun w => ⟨h0.2 a w, h1.2 b w⟩]
    simp only [Set.indicator_apply, SetLike.mem_coe, a, b, if_true, Pi.one_apply]
    ring
  · rw [if_neg (fun h => b (h1.1 fun w => (h w).2))]
    simp only [Set.indicator_apply, SetLike.mem_coe, a, b, if_true, if_false, Pi.one_apply]
    ring
  · rw [if_neg (fun h => a (h0.1 fun w => (h w).1))]
    simp only [Set.indicator_apply, SetLike.mem_coe, a, b, if_true, if_false, Pi.one_apply]
    ring
  · rw [if_neg (fun h => a (h0.1 fun w => (h w).1))]
    simp only [Set.indicator_apply, SetLike.mem_coe, a, b, if_true, if_false, Pi.one_apply]
    ring

theorem rowA_zero : rowA (0 : Fin 2 → F) = 0 := by
  funext i
  simp [rowA]

theorem phi_zero (c : HeightOneSpectrum (𝓞 F) → ℕ) : Phi c 0 = 0 := by
  simp [Phi, map_zero, arch_zero]

theorem phiH_zero (c : HeightOneSpectrum (𝓞 F) → ℕ) : PhiH c 0 = 0 := by
  simp [PhiH, map_zero, arch_zero]

end UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic

open UpperTheory.HilbertEisensteinWeightOne UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic in
theorem UpperTheory.HilbertEisensteinWeightOne.poisson_summation_holds : SPois := by
  intro F _ _ _ ω c hyp
  have hc := finite_support_of_cond F ω c hyp.fin hyp.cond
  obtain ⟨φ, hφ⟩ := exists_schwartz_arch F
  have hmem : Phi c ∈ schwartzBruhat2 F := by
    rw [phi_eq hc φ hφ]
    exact schwartzBruhatTensor2_mem φ (gFin_mem c)
  refine ⟨cst c, fun h => ?_⟩
  obtain ⟨S1, S2, E⟩ := poisson_rightTranslate hmem h
  have hF : ∀ ξ : Fin 2 → F, adelicFourier2 F (Phi c) ((fun i ↦ algebraMap F (Ad F) (ξ i)) ᵥ*
      ((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))ᵀ) =
      cst c * PhiH c (((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ) := by
    intro ξ
    rw [fourier_phi hc φ hφ, Matrix.vecMul_transpose]
    rfl
  simp only [hF, norm_mul] at S2 E
  have hsupp1 : Function.support (fun ξ : Fin 2 → F => Phi c (rowA ξ ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F)))) ⊆
      {ξ | ξ ≠ 0} := by
    intro ξ hξ
    rintro (rfl : ξ = 0)
    apply hξ
    dsimp only
    rw [rowA_zero, Matrix.zero_vecMul, phi_zero]
  have hsupp2 : Function.support (fun ξ : Fin 2 → F =>
      PhiH c (((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ)) ⊆ {ξ | ξ ≠ 0} := by
    intro ξ hξ
    rintro (rfl : ξ = 0)
    apply hξ
    dsimp only
    rw [rowA_zero, Matrix.mulVec_zero, phiH_zero]
  have hC : ‖cst c‖ ≠ 0 := norm_ne_zero_iff.mpr (cst_ne_zero c)
  refine ⟨?_, ?_, ?_⟩
  · exact (S1.subtype (fun ξ : Fin 2 → F => ξ ≠ 0) : _)
  · exact (((summable_mul_left_iff hC).mp S2).subtype (fun ξ : Fin 2 → F => ξ ≠ 0) : _)
  · rw [thetaS, thetaT]
    rw [show (∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, Phi c (rowA ξ.1 ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F)))) =
        ∑' ξ : ({ξ | ξ ≠ 0} : Set (Fin 2 → F)), Phi c (rowA (ξ : Fin 2 → F) ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F))) from rfl,
      tsum_subtype_eq_of_support_subset hsupp1,
      show (∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, PhiH c (((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ.1)) =
        ∑' ξ : ({ξ | ξ ≠ 0} : Set (Fin 2 → F)), PhiH c (((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA (ξ : Fin 2 → F)) from rfl,
      tsum_subtype_eq_of_support_subset hsupp2]
    change ∑' ξ : Fin 2 → F, Phi c ((fun i ↦ algebraMap F (Ad F) (ξ i)) ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F))) = _
    rw [E, tsum_mul_left, absD, Complex.ofReal_inv]
    ring
