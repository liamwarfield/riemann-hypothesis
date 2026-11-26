module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.PointwiseThetaExpansion
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.LocalExpansionHolds
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.AbsoluteConvergenceHolds

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.MixedFourierArchSchwartz
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix nonZeroDivisors
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L1

open NumberField.mixedEmbedding NumberField.InfinitePlace Function
open scoped SchwartzMap FourierTransform Real Classical

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem mem_units_of_isUnitAt (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) (hx : IsUnitAt w x) :
    x ∈ (Submonoid.ofClass (w.adicCompletionIntegers F)).units := by
  rw [Submonoid.mem_units_iff]
  have hx' : Valued.v (x : w.adicCompletion F) = 1 := hx
  refine ⟨?_, ?_⟩
  · change (x : w.adicCompletion F) ∈ w.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hx']
  · change ((x⁻¹ : (w.adicCompletion F)ˣ) : w.adicCompletion F) ∈ w.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hx', inv_one]

theorem integral_arch_one (a y : ℝ) :
    ∫ t : ℝ, ((𝐞 (-(t * y)) : Circle) : ℂ) *
        (((a : ℂ) + Complex.I * (t : ℂ)) * Complex.exp (-(π : ℂ) * ((a : ℂ) ^ 2 + (t : ℂ) ^ 2))) =
      ((a : ℂ) + (y : ℂ)) * Complex.exp (-(π : ℂ) * ((a : ℂ) ^ 2 + (y : ℂ) ^ 2)) := by
  set c1 : ℂ := (a : ℂ) * Complex.exp (-(π : ℂ) * (a : ℂ) ^ 2)
  set c2 : ℂ := Complex.I * Complex.exp (-(π : ℂ) * (a : ℂ) ^ 2)
  have hpt : ∀ t : ℝ, ((𝐞 (-(t * y)) : Circle) : ℂ) *
      (((a : ℂ) + Complex.I * (t : ℂ)) * Complex.exp (-(π : ℂ) * ((a : ℂ) ^ 2 + (t : ℂ) ^ 2))) =
      c1 * (((𝐞 (-(t * y)) : Circle) : ℂ) * realGaussian t) +
        c2 * (((𝐞 (-(t * y)) : Circle) : ℂ) * realGaussianOdd t) := by
    intro t
    simp only [c1, c2, realGaussian, realGaussianOdd]
    have : Complex.exp (-(π : ℂ) * ((a : ℂ) ^ 2 + (t : ℂ) ^ 2)) =
        Complex.exp (-(π : ℂ) * (a : ℂ) ^ 2) * Complex.exp (-(π : ℂ) * (t : ℂ) ^ 2) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [this]
    ring
  have hce : Continuous fun t : ℝ => ((𝐞 (-(t * y)) : Circle) : ℂ) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have hg : Continuous realGaussian := by unfold realGaussian; fun_prop
  have hgo : Continuous realGaussianOdd := by unfold realGaussianOdd; fun_prop
  have hi1 : Integrable fun t : ℝ => ((𝐞 (-(t * y)) : Circle) : ℂ) * realGaussian t :=
    integrable_realGaussian.norm.mono' (hce.mul hg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by rw [norm_mul, Circle.norm_coe, one_mul])
  have hi2 : Integrable fun t : ℝ => ((𝐞 (-(t * y)) : Circle) : ℂ) * realGaussianOdd t :=
    integrable_realGaussianOdd.norm.mono' (hce.mul hgo).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by rw [norm_mul, Circle.norm_coe, one_mul])
  have hf1 : 𝓕 realGaussian y = ∫ t : ℝ, ((𝐞 (-(t * y)) : Circle) : ℂ) * realGaussian t := by
    rw [Real.fourier_real_eq]; simp only [Circle.smul_def, smul_eq_mul]
  have hf2 : 𝓕 realGaussianOdd y = ∫ t : ℝ, ((𝐞 (-(t * y)) : Circle) : ℂ) * realGaussianOdd t := by
    rw [Real.fourier_real_eq]; simp only [Circle.smul_def, smul_eq_mul]
  simp only [hpt]
  rw [integral_add (hi1.const_mul c1) (hi2.const_mul c2), integral_const_mul, integral_const_mul, ← hf1, ← hf2,
    fourier_realGaussian, fourier_realGaussianOdd]
  simp only [c1, c2, realGaussian, realGaussianOdd]
  have : Complex.exp (-(π : ℂ) * ((a : ℂ) ^ 2 + (y : ℂ) ^ 2)) =
      Complex.exp (-(π : ℂ) * (a : ℂ) ^ 2) * Complex.exp (-(π : ℂ) * (y : ℂ) ^ 2) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [this]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem mixedFourier_archSchwartz (a : InfinitePlace F → ℝ) (Z : Ad F) :
    mixedFourier F (archSchwartz a) (homeomorphMixedSpace F Z.1) =
      ∏ v, (((a v : ℝ) : ℂ) + ((UpperTheory.V.TR.pInf F Z v : ℝ) : ℂ)) *
        Complex.exp (-(π : ℂ) * (((a v : ℝ) : ℂ) ^ 2 + ((UpperTheory.V.TR.pInf F Z v : ℝ) : ℂ) ^ 2)) := by
  haveI := isEmpty_complex (F := F)
  set m := homeomorphMixedSpace F Z.1
  set A : ∀ w : {w : InfinitePlace F // IsReal w}, ℝ → ℂ := fun w t => ((𝐞 (-(t * m.1 w)) : Circle) : ℂ) *
    ((((a w.1 : ℝ) : ℂ) + Complex.I * (t : ℂ)) * Complex.exp (-(π : ℂ) * (((a w.1 : ℝ) : ℂ) ^ 2 + (t : ℂ) ^ 2)))
  set B : ∀ w : {w : InfinitePlace F // IsComplex w}, ℂ → ℂ := fun _ _ => 1
  have hint : ∀ x : mixedSpace F, 𝐞 (-mixedTraceForm F x m) • archSchwartz a x =
      (∏ w, A w (x.1 w)) * ∏ w, B w (x.2 w) := by
    intro x
    rw [Circle.smul_def, smul_eq_mul, HeckeCharacter.fourierChar_neg_mixedTraceForm, archSchwartz_eq_prod]
    simp only [A, B, Finset.univ_eq_empty (α := {w : InfinitePlace F // IsComplex w}), Finset.prod_empty,
      mul_one, Finset.prod_mul_distrib]
  have hA : ∀ w : {w : InfinitePlace F // IsReal w}, ∫ t, A w t =
      (((a w.1 : ℝ) : ℂ) + ((UpperTheory.V.TR.pInf F Z w.1 : ℝ) : ℂ)) *
        Complex.exp (-(π : ℂ) * (((a w.1 : ℝ) : ℂ) ^ 2 + ((UpperTheory.V.TR.pInf F Z w.1 : ℝ) : ℂ) ^ 2)) :=
    fun w => integral_arch_one (a w.1) (m.1 w)
  rw [mixedFourier_apply, selfDualMeasure, integral_smul_measure, Measure.volume_eq_prod]
  simp only [hint]
  rw [integral_prod_mul (f := fun x : {w : InfinitePlace F // IsReal w} → ℝ ↦ ∏ w, A w (x w))
    (g := fun z : {w : InfinitePlace F // IsComplex w} → ℂ ↦ ∏ w, B w (z w)),
    integral_fintype_prod_volume_eq_prod, integral_fintype_prod_volume_eq_prod]
  simp only [hA, Finset.univ_eq_empty (α := {w : InfinitePlace F // IsComplex w}), Finset.prod_empty, mul_one,
    IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, ENNReal.toReal_one, one_smul]
  exact prod_real (fun v => (((a v : ℝ) : ℂ) + ((UpperTheory.V.TR.pInf F Z v : ℝ) : ℂ)) *
        Complex.exp (-(π : ℂ) * (((a v : ℝ) : ℂ) ^ 2 + ((UpperTheory.V.TR.pInf F Z v : ℝ) : ℂ) ^ 2)))

theorem adelicFourier_slice {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (A Z : Ad F) :
    adelicFourier F (slice c A) Z =
      ((finiteAdeleMeasure F (idealFiniteAdeles (levelIdeal c))).toReal : ℂ) * kernF c A Z := by
  classical
  rw [slice_eq hc A, adelicFourier_smul, Pi.smul_apply, adelicFourier_schwartzBruhatTensor, schwartzBruhatTensor,
    mixedFourierSchwartz_apply, finiteFourier_cosetIndicator, mixedFourier_archSchwartz, smul_eq_mul, one_mul]
  unfold kernF
  rw [Set.indicator_apply]
  simp only [SetLike.mem_coe, Pi.one_apply]
  rw [mem_dual_iff hc]
  have hZ : Z.2 = pFin F Z := rfl
  rw [hZ]
  by_cases h1 : ∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ))
  · by_cases h2 : ∀ w, Valued.v (pLoc F w (pFin F Z)) ≤ WithZero.exp ((c w : ℤ) + dd w)
    · simp only [h1, h2, and_self, implies_true, ↓reduceIte]; ring
    · simp only [h1, h2, implies_true, true_and, ↓reduceIte]; ring
  · simp only [h1, false_and, ↓reduceIte]; ring

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L1

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L1

theorem finite_expansion_holds : SFin := by
  intro F _ _ _ ω c H
  set χ : (FiniteAdeleRing (𝓞 F) F)ˣ →* ℂˣ := ω.1.comp IdeleGroup.ofFinite with hχdef
  have hχ : Continuous χ := ω.2.1.comp IdeleGroup.continuous_ofFinite
  refine (IdeleGroup.finite_support_conductorExponentAt Complex.units_noSmallSubgroups χ hχ).subset ?_
  intro w hw
  rw [Function.mem_support]
  intro h0
  apply hw
  have hk := (IdeleGroup.conductorExponentAt_eq_zero_iff Complex.units_noSmallSubgroups χ hχ w).1 h0
  have hmem : (0 : ℕ) ∈ {n : ℕ | ∀ x : (w.adicCompletion F)ˣ, IsUnitAt w x →
      Valued.v ((x : w.adicCompletion F) - 1) ≤ WithZero.exp (-(n : ℤ)) → ω.loc w x = 1} := by
    intro x hx _
    have h1 := hk (mem_units_of_isUnitAt w x hx)
    rw [MonoidHom.mem_ker] at h1
    exact h1
  exact Nat.le_zero.1 ((H.cond w).2 hmem)

theorem kernel_expansion_holds : SKern := by
  intro F _ _ _ c hc
  refine ⟨((finiteAdeleMeasure F (idealFiniteAdeles (levelIdeal c))).toReal : ℂ), ?_,
    fun A Z => adelicFourier_slice hc A Z⟩
  rw [Complex.ofReal_ne_zero, finiteAdeleMeasure_idealFiniteAdeles_toReal]
  refine mul_ne_zero (inv_ne_zero ?_) (inv_ne_zero ?_)
  · rw [Rat.cast_ne_zero, Ne, FractionalIdeal.absNorm_eq_zero_iff]
    exact (levelIdeal c).ne_zero
  · rw [NNReal.coe_ne_zero, Ne, NNReal.sqrt_eq_zero, nnnorm_eq_zero]
    exact_mod_cast NumberField.discr_ne_zero F

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.IdeleModuleFiniteEmbeddingUnit
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

namespace L7

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

open Classical in
theorem slice_congr (c : HeightOneSpectrum (𝓞 F) → ℕ) {A A' : Ad F}
    (h1 : UpperTheory.V.TR.pInf F A = UpperTheory.V.TR.pInf F A')
    (h2 : ∀ w, Valued.v (pLoc F w (pFin F A)) = Valued.v (pLoc F w (pFin F A'))) :
    slice c A = slice c A' := by
  funext B
  simp only [slice, Phi, Matrix.cons_val_zero, Matrix.cons_val_one, h1]
  congr 1
  exact if_congr (forall_congr' fun w => by rw [h2 w]) rfl rfl

theorem pInf_finiteEmbedding (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) :
    UpperTheory.V.TR.pInf F ((finiteEmbedding w x : IdeleGroup F) : Ad F) = 1 := by
  show (UpperTheory.V.TR.infEq F).symm ((finiteEmbedding w x : IdeleGroup F) : Ad F).1 = 1
  rw [coe_finiteEmbedding]
  exact map_one _

theorem valued_finiteEmbedding (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ)
    (hx : IsUnitAt w x) (w' : HeightOneSpectrum (𝓞 F)) :
    Valued.v (pLoc F w' (pFin F ((finiteEmbedding w x : IdeleGroup F) : Ad F))) = 1 := by
  show Valued.v ((((finiteEmbedding w x : IdeleGroup F) : Ad F).2) w') = 1
  rw [coe_finiteEmbedding]
  by_cases h : w' = w
  · subst h
    show Valued.v (finiteAdeleSingle w' (x : w'.adicCompletion F) w') = 1
    rw [finiteAdeleSingle_apply_self]
    exact hx
  · show Valued.v (finiteAdeleSingle w (x : w.adicCompletion F) w') = 1
    rw [finiteAdeleSingle_apply_of_ne h]
    exact map_one _

theorem norm_unit (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) (hx : IsUnitAt w x) :
    ‖(x : w.adicCompletion F)‖ = 1 := by
  have hx' : Valued.v ((x⁻¹ : (w.adicCompletion F)ˣ) : w.adicCompletion F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, show Valued.v (x : w.adicCompletion F) = 1 from hx, inv_one]
  refine IdeleGroup.norm_eq_one_of_mul_eq_one (b := ((x⁻¹ : (w.adicCompletion F)ˣ) : w.adicCompletion F))
    x.mul_inv ?_ ?_
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F w).2 (le_of_eq hx)
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F w).2 (le_of_eq hx')

theorem ideleModule_finiteEmbedding_unit (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ)
    (hx : IsUnitAt w x) : ideleModule F (finiteEmbedding w x) = 1 :=
  Subtype.ext (by rw [ideleModule_finiteEmbedding, norm_unit w x hx]; rfl)

theorem kern_mul_unit (c : HeightOneSpectrum (𝓞 F) → ℕ) (Y : Ad F) (σ : IdeleGroup F)
    (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) (hx : IsUnitAt w x) :
    kern c Y (σ * finiteEmbedding w x) 0 = kern c Y σ 0 := by
  have hs : slice c (((σ * finiteEmbedding w x : IdeleGroup F) : Ad F) * Y) = slice c ((σ : Ad F) * Y) := by
    refine slice_congr c ?_ ?_
    · rw [Units.val_mul, map_mul, map_mul, map_mul, pInf_finiteEmbedding, mul_one]
    · intro w'
      simp only [Units.val_mul, map_mul, valued_finiteEmbedding w x hx w', mul_one]
  unfold kern
  rw [hs, map_mul, ideleModule_finiteEmbedding_unit w x hx, mul_one, map_zero, smul_zero, smul_zero]

theorem omega_diagonal (ω : HChar F) (δ : Fˣ) : ω.1 (diagonal F δ) = 1 := ω.2.2 δ

theorem coefK_mul_diagonal (c : HeightOneSpectrum (𝓞 F) → ℕ) (Y : Ad F) (τ : IdeleGroup F) (δ : Fˣ) (ξ : F) :
    coefK c Y (τ * diagonal F δ) ξ = coefK c Y τ ξ := by
  unfold coefK
  have := (Equiv.mulLeft δ).tsum_eq (fun a => kern c Y (τ * diagonal F a) ξ)
  rw [← this]
  refine tsum_congr fun a => ?_
  rw [Equiv.coe_mulLeft, map_mul, mul_assoc]

theorem coefK_mul_unit (c : HeightOneSpectrum (𝓞 F) → ℕ) (Y : Ad F) (τ : IdeleGroup F)
    (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) (hx : IsUnitAt w x) :
    coefK c Y (τ * finiteEmbedding w x) 0 = coefK c Y τ 0 := by
  unfold coefK
  refine tsum_congr fun a => ?_
  rw [mul_right_comm, kern_mul_unit c Y _ w x hx]

theorem exists_unit (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (H : Hyp ω c) :
    ∃ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ), IsUnitAt w x ∧ ω.loc w x ≠ 1 := by
  obtain ⟨w, hw⟩ := H.ram
  refine ⟨w, ?_⟩
  by_contra hne
  push Not at hne
  have h0 : (0 : ℕ) ∈ {n : ℕ | ∀ x : (w.adicCompletion F)ˣ, IsUnitAt w x →
      Valued.v ((x : w.adicCompletion F) - 1) ≤ WithZero.exp (-(n : ℤ)) → ω.loc w x = 1} :=
    fun x hx _ => hne x hx
  exact hw (Nat.le_zero.1 ((H.cond w).2 h0))

theorem loc_eq (ω : HChar F) (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) :
    ω.1 (finiteEmbedding w x) = ω.loc w x := rfl

end L7

open L7 in
theorem null_term_holds : SFin → SKern → SNull := by
  intro _ _ F _ _ _ ω c H y yf t _
  set Y := yAd y yf
  obtain ⟨w, x, hx, hω⟩ := exists_unit ω c H
  set h : normOneSubgroup F → ℂ := fun u => coefK c Y (tau t u) 0 * ((ω.1 (tau t u) : ℂˣ) : ℂ)⁻¹ with hdef
  have hh : ∀ (δ : Fˣ) (u : normOneSubgroup F), h (u * diagonalToNormOne F δ) = h u := by
    intro δ u
    have e1 : tau t (u * diagonalToNormOne F δ) = tau t u * diagonal F δ := by
      simp only [tau, Subgroup.coe_mul, coe_diagonalToNormOne, mul_assoc]
    simp only [hdef, e1, coefK_mul_diagonal, map_mul, omega_diagonal, mul_one]
  have he1 : ideleModule F (finiteEmbedding w x) = 1 := ideleModule_finiteEmbedding_unit w x hx
  let e' : normOneSubgroup F := ⟨finiteEmbedding w x, by rw [normOneSubgroup, MonoidHom.mem_ker]; exact he1⟩
  have hshift : ∀ u, h (e' * u) = ((ω.1 (finiteEmbedding w x) : ℂˣ) : ℂ)⁻¹ * h u := by
    intro u
    have e2 : tau t (e' * u) = tau t u * finiteEmbedding w x := by
      simp only [tau, Subgroup.coe_mul, e']
      rw [mul_comm ((finiteEmbedding w x : IdeleGroup F)) (u : IdeleGroup F), mul_assoc]
    simp only [hdef, e2, coefK_mul_unit c Y _ w x hx, map_mul, Units.val_mul, mul_inv]
    ring
  have hI := setIntegral_mul_left_eq hh e'
  simp only [hshift] at hI
  rw [integral_const_mul] at hI
  have hne : ((ω.1 (finiteEmbedding w x) : ℂˣ) : ℂ)⁻¹ ≠ 1 := by
    rw [Ne, inv_eq_one, loc_eq]
    intro h1
    exact hω (Units.ext h1)
  have h3 : (((ω.1 (finiteEmbedding w x) : ℂˣ) : ℂ)⁻¹ - 1) *
      ∫ u in normOneFundamentalDomain F, h u ∂normOneMeasure F = 0 := by
    rw [sub_mul, one_mul, hI, sub_self]
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hne)

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.MeasurePreservingPhiA
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix ENNReal
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published Filter

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

namespace L6

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem omega_diagonal (ω : HChar F) (a : Fˣ) : ω.1 (diagonal F a) = 1 := ω.2.2 a

theorem module_tau_diag (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) (a : Fˣ) :
    (ideleModule F (tau t u * diagonal F a) : ℝ) = t := by
  have hu : ideleModule F (u : IdeleGroup F) = 1 := u.2
  rw [tau, map_mul, map_mul, ideleModule_diagonal, ideleModule_moduleSection, hu, mul_one, mul_one]

theorem G_unfold (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (Y : Ad F) (ξ : F) (t : {r : ℝ // 0 < r})
    (u : normOneSubgroup F) (a : Fˣ) :
    kern c Y (diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F)) ξ *
      ((ω.1 (diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F)) : ℂˣ) : ℂ)⁻¹ *
      ((ideleModule F (diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F)) : ℝ) : ℂ) =
    kern c Y (tau t u * diagonal F a) ξ * wt ω t u := by
  have he : diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F) = tau t u * diagonal F a := by
    rw [tau, mul_assoc, mul_comm]
  rw [he, module_tau_diag, map_mul, omega_diagonal, mul_one, wt, mul_assoc]

theorem tsum_G (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (Y : Ad F) (ξ : F) (t : {r : ℝ // 0 < r})
    (u : normOneSubgroup F) :
    ∑' a : Fˣ, kern c Y (diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F)) ξ *
      ((ω.1 (diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F)) : ℂˣ) : ℂ)⁻¹ *
      ((ideleModule F (diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F)) : ℝ) : ℂ) =
    coefK c Y (tau t u) ξ * wt ω t u := by
  simp_rw [G_unfold]
  rw [coefK, tsum_mul_right]

def phiA (a : Fˣ) (p : {r : ℝ // 0 < r} × normOneSubgroup F) : IdeleGroup F :=
  diagonal F a * moduleSection (w0 F) p.1 * (p.2 : IdeleGroup F)

theorem continuous_phiA (a : Fˣ) : Continuous (phiA (F := F) a) :=
  (continuous_const.mul ((continuous_moduleSection (w0 F)).comp continuous_fst)).mul
    (continuous_subtype_val.comp continuous_snd)

theorem measurePreserving_phiA (a : Fˣ) :
    MeasurePreserving (phiA (F := F) a) (posRealMeasure.prod (normOneMeasure F)) (ideleMeasure F) := by
  have h0 : MeasurePreserving (normOneSplitting (w0 F)).toHomeomorph.toMeasurableEquiv (ideleMeasure F)
      ((normOneMeasure F).prod posRealMeasure) := measurePreserving_normOneSplitting (w0 F)
  have h1 := (MeasurePreserving.symm _ h0).comp (Measure.measurePreserving_swap
    (μ := posRealMeasure) (ν := normOneMeasure F))
  have h3 := (measurePreserving_mul_left (ideleMeasure F) (diagonal F a)).comp h1
  convert h3 using 1
  funext p
  change diagonal F a * moduleSection (w0 F) p.1 * (p.2 : IdeleGroup F) =
    diagonal F a * ((p.2 : IdeleGroup F) * moduleSection (w0 F) p.1)
  rw [mul_assoc, mul_comm (moduleSection (w0 F) p.1)]

theorem muE_ac : muE F ≪ posRealMeasure.prod (normOneMeasure F) := by
  have h : muE F = (posRealMeasure.prod (normOneMeasure F)).restrict (Set.univ ×ˢ normOneFundamentalDomain F) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [h]
  exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self

theorem lintegral_unfold {g : IdeleGroup F → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p, ∑' a : Fˣ, g (phiA a p) ∂(muE F) = ∫⁻ x, g x ∂ideleMeasure F := by
  have hm : ∀ a : Fˣ, Measurable fun p => g (phiA a p) := fun a => hg.comp (continuous_phiA a).measurable
  have hin : ∀ t : {r : ℝ // 0 < r}, ∫⁻ u in normOneFundamentalDomain F, ∑' a : Fˣ, g (phiA a (t, u)) ∂normOneMeasure F
      = ∫⁻ u, g (phiA 1 (t, u)) ∂normOneMeasure F := by
    intro t
    have h𝓕 := isFundamentalDomain_normOneFundamentalDomain F (normOneMeasure F)
    let e : Fˣ ≃ (diagonalNormOne F).op := (diagonalNormOneEquiv F).trans (diagonalNormOne F).equivOp
    rw [lintegral_tsum (f := fun a u => g (phiA a (t, u))) (fun a => ((hm a).comp measurable_prodMk_left).aemeasurable),
      h𝓕.lintegral_eq_tsum'',
      ← e.tsum_eq]
    refine tsum_congr fun a => lintegral_congr fun u => ?_
    change g (phiA a (t, u)) = g (phiA 1 (t, u * diagonalToNormOne F a))
    simp only [phiA, map_one, one_mul, Subgroup.coe_mul, coe_diagonalToNormOne]
    congr 1
    ac_rfl
  rw [lintegral_prod _ (Measurable.tsum hm).aemeasurable]
  simp_rw [hin]
  rw [← (measurePreserving_phiA 1).lintegral_comp hg, lintegral_prod _ (hm 1).aemeasurable]

theorem integrable_unfold {G : IdeleGroup F → ℂ} (hG : Integrable G (ideleMeasure F)) :
    Integrable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F => ∑' a : Fˣ, G (phiA a p)) (muE F) := by
  set G' := hG.1.mk G
  have hG'm : StronglyMeasurable G' := hG.1.stronglyMeasurable_mk
  have hGG' : G =ᵐ[ideleMeasure F] G' := hG.1.ae_eq_mk
  have hae : ∀ᵐ p ∂(muE F), ∀ a : Fˣ, G (phiA a p) = G' (phiA a p) := by
    refine ae_all_iff.2 fun a => muE_ac.ae_le ?_
    exact (measurePreserving_phiA a).quasiMeasurePreserving.ae_eq_comp hGG'
  have hP' : Integrable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F => ∑' a : Fˣ, G' (phiA a p)) (muE F) := by
    refine ⟨(Measurable.tsum fun a => hG'm.measurable.comp (continuous_phiA a).measurable).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ p, ‖∑' a : Fˣ, G' (phiA a p)‖ₑ ∂(muE F)
        ≤ ∫⁻ p, ∑' a : Fˣ, ‖G' (phiA a p)‖ₑ ∂(muE F) := lintegral_mono fun p => enorm_tsum_le_tsum_enorm
      _ = ∫⁻ x, ‖G' x‖ₑ ∂ideleMeasure F := lintegral_unfold hG'm.measurable.enorm
      _ = ∫⁻ x, ‖G x‖ₑ ∂ideleMeasure F := lintegral_congr_ae (hGG'.fun_comp _).symm
      _ < ∞ := hG.2
  refine hP'.congr ?_
  filter_upwards [hae] with p hp
  exact tsum_congr fun a => (hp a).symm

end L6

open L6 in
theorem sUnfold_statement : SUnfold := by
  intro F _ _ _ ω c H Y ξ hG
  set G : IdeleGroup F → ℂ := fun τ => kern c Y τ ξ * ((ω.1 τ : ℂˣ) : ℂ)⁻¹ * ((ideleModule F τ : ℝ) : ℂ)
  have hP : ∀ p : {r : ℝ // 0 < r} × normOneSubgroup F,
      coefK c Y (tau p.1 p.2) ξ * wt ω p.1 p.2 = ∑' a : Fˣ, G (phiA a p) := fun p => (tsum_G ω c Y ξ p.1 p.2).symm
  simp_rw [hP]
  rw [integral_prod _ (integrable_unfold hG), integral_ideleMeasure_eq_integral_fundamentalDomain (w0 F) hG]
  rfl

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end

noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published Filter Topology

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem norm_omega {ω : HChar F} (hfin : IsOfFinOrder ω) (τ : IdeleGroup F) :
    ‖((ω.1 τ : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_iff_pow_eq_one).1 hfin
  have h : ((ω.1 τ : ℂˣ) : ℂ) ^ n = 1 := by
    have h1 : (ω ^ n).1 τ = 1 := by rw [hpow]; rfl
    rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, ← Subgroup.coe_pow, h1, Units.val_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 (by rw [← norm_pow, h, norm_one])

theorem norm_ex (ξ : F) (x : UpperTheory.V.TR.Rinf F) : ‖ex ξ x‖ = 1 := by
  have : 2 * Real.pi * Complex.I * ∑ v, (reAt v ξ : ℂ) * (x v : ℂ) =
      ((2 * Real.pi * ∑ v, reAt v ξ * x v : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [ex, this, Complex.norm_exp_ofReal_mul_I]

theorem norm_wt {ω : HChar F} (hfin : IsOfFinOrder ω) (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) :
    ‖wt ω t u‖ = (t : ℝ) := by
  rw [wt, norm_mul, norm_inv, norm_omega hfin, inv_one, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos t.2]

theorem continuous_wt (ω : HChar F) : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F => wt ω p.1 p.2 := by
  have hω : Continuous ω.1 := ω.2.1
  have ht : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F => tau p.1 p.2 :=
    ((continuous_moduleSection (w0 F)).comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have h1 : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F => ((ω.1 (tau p.1 p.2) : ℂˣ) : ℂ)⁻¹ := by
    have : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F => (((ω.1 (tau p.1 p.2))⁻¹ : ℂˣ) : ℂ) :=
      Units.continuous_val.comp ((hω.comp ht).inv)
    simpa using this
  exact h1.mul (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst))

theorem norm_infEq (r : UpperTheory.V.TR.Rinf F) (w : InfinitePlace F) : ‖UpperTheory.V.TR.infEq F r w‖ = |r w| := by
  have hv := IsTotallyReal.isReal w
  have h := (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.dist_eq (r w) 0
  have h0 : (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm 0 = 0 :=
    map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm
  rw [h0, dist_zero_right, dist_zero_right, Real.norm_eq_abs] at h
  exact h

theorem infId_val (y : (UpperTheory.V.TR.Rinf F)ˣ) :
    ((UpperTheory.V.TR.infId F y : (Ad F)ˣ) : Ad F) = (UpperTheory.V.TR.infEq F y.val, 1) := by
  change 1 - UpperTheory.V.TR.sInf F 1 + UpperTheory.V.TR.sInf F y.val = _
  refine Prod.ext ?_ ?_
  · change (1 : InfiniteAdeleRing F) - UpperTheory.V.TR.infEq F 1 + UpperTheory.V.TR.infEq F y.val = _
    rw [map_one, sub_self, zero_add]
  · change (1 : Af F) - 0 + 0 = 1
    rw [sub_zero, add_zero]

theorem finId_val (yf : (Af F)ˣ) : ((finId F yf : (Ad F)ˣ) : Ad F) = (1, (yf : Af F)) := by
  change 1 - sFin F 1 + sFin F yf.val = _
  refine Prod.ext ?_ ?_
  · change (1 : InfiniteAdeleRing F) - 0 + 0 = 1
    rw [sub_zero, add_zero]
  · change (1 : Af F) - 1 + (yf : Af F) = _
    rw [sub_self, zero_add]

theorem absD_gPt (x : UpperTheory.V.TR.Rinf F) (y : (UpperTheory.V.TR.Rinf F)ˣ) (hy : ∀ v, 0 < y.val v) (yf : (Af F)ˣ) :
    absD (gPt x y yf) = (∏ v, y.val v) * absF yf := by
  have hdet1 : Matrix.GeneralLinearGroup.det (aff y x) = y := by
    ext1
    simp [aff, Matrix.det_fin_two_of]
  have hdet2 : Matrix.GeneralLinearGroup.det (aff yf (0 : Af F)) = yf := by
    ext1
    simp [aff, Matrix.det_fin_two_of]
  unfold absD gPt
  rw [map_mul, UpperTheory.V.TR.det_infGL, UpperTheory.V.TR.det_finGL, hdet1, hdet2, map_mul]
  change (IdeleGroup.ideleModule F _ : ℝ) * (IdeleGroup.ideleModule F _ : ℝ) = _
  rw [ideleModule_eq, ideleModule_eq]
  simp only [infId_val, finId_val]
  have h1 : ∏ w : InfinitePlace F, ‖UpperTheory.V.TR.infEq F y.val w‖ ^ w.mult = ∏ v, y.val v := by
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [(IsTotallyReal.isReal w).mult_eq_one, pow_one, norm_infEq, abs_of_pos (hy w)]
  have h2 : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(1 : Af F) v‖ = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => by simp
  have h3 : ∏ w : InfinitePlace F, ‖(1 : InfiniteAdeleRing F) w‖ ^ w.mult = 1 :=
    Finset.prod_eq_one fun w _ => (by rw [norm_one, one_pow] : ‖(1 : w.Completion)‖ ^ w.mult = 1)
  rw [h1, h2, h3, mul_one, one_mul]
  rfl

theorem gPt_eq (x : UpperTheory.V.TR.Rinf F) (y : (UpperTheory.V.TR.Rinf F)ˣ) (yf : (Af F)ˣ) :
    UpperTheory.V.TR.infGL F 2 (aff y x) * finGL F 2 (aff yf 0) = gPt x y yf := rfl

theorem coefAt_const_mul (a : ℂ) (d : Ideal (𝓞 F) → ℂ) (z : Af F) :
    coefAt (fun 𝔪 => a * d 𝔪) z = a * coefAt d z := by
  unfold coefAt
  split_ifs <;> simp

theorem ne_zero_of_pos {ξ : F} (h : ∀ v, 0 < reAt v ξ) : ξ ≠ 0 := by
  rintro rfl
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  simpa [reAt] using h v

theorem sExp_assembly (hPt : SPoint) (hZ : SZero) (hNl : SNull) (hA : SAbs) (hU : SUnfold) (hL : SLocal) :
    SInt → SExp := by
  intro hI F _ _ _ ω c H
  obtain ⟨C₀, hC₀, hloc⟩ := hL F ω c H
  refine ⟨C₀, ∫ p, zeroRow c (tau p.1 p.2) * wt ω p.1 p.2 ∂(muE F), hC₀, ?_⟩
  intro x y hy yf
  set Y := yAd y yf
  set g := gPt x y yf
  set D : ℂ := ((absD g ^ ((1 : ℝ) / 2) : ℝ) : ℂ) with hDdef
  set A0 : {r : ℝ // 0 < r} × normOneSubgroup F → ℂ := fun p => zeroRow c (tau p.1 p.2) * wt ω p.1 p.2
  set N : {r : ℝ // 0 < r} × normOneSubgroup F → ℂ := fun p => coefK c Y (tau p.1 p.2) 0 * wt ω p.1 p.2
  set Sf : Fˣ → {r : ℝ // 0 < r} × normOneSubgroup F → ℂ :=
    fun ξ p => ex (ξ : F) x * coefK c Y (tau p.1 p.2) ξ * wt ω p.1 p.2
  set S : {r : ℝ // 0 < r} × normOneSubgroup F → ℂ := fun p => ∑' ξ : Fˣ, Sf ξ p
  obtain ⟨hmeas, hsum, hint⟩ := hA F ω c H y hy yf
  have hfin := H.fin

  have hpt : ∀ p : {r : ℝ // 0 < r} × normOneSubgroup F, eisInt ω (Phi c) g p.1 p.2 = (A0 p + N p + S p) * D := by
    intro p
    have h := hPt F ω c H x y hy yf (tau p.1 p.2)
    simp only [eisInt, A0, N, S, Sf]
    change thetaS (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) (tau p.1 p.2) * g) * _ * _ * _ = _
    rw [h, tsum_mul_right]
    simp only [wt, tau, hDdef]
    ring
  have hDpos : 0 < absD g := (IdeleGroup.ideleModule F _).2
  have hD0 : D ≠ 0 := by
    rw [hDdef, Complex.ofReal_ne_zero]
    exact (Real.rpow_pos_of_pos hDpos _).ne'

  have hT : Integrable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F => eisInt ω (Phi c) g p.1 p.2) (muE F) :=
    hI F ω c H g
  have hA0 : Integrable A0 (muE F) := hZ F ω c H
  have hSfm : ∀ ξ : Fˣ, AEStronglyMeasurable (Sf ξ) (muE F) := fun ξ =>
    (aestronglyMeasurable_const.mul (hmeas ξ)).mul (continuous_wt ω).aestronglyMeasurable
  have hSfb : ∀ ξ : Fˣ, ∀ p, ‖Sf ξ p‖ = ‖coefK c Y (tau p.1 p.2) ξ‖ * (p.1 : ℝ) := by
    intro ξ p
    simp only [Sf, norm_mul, norm_ex, norm_wt hfin, one_mul]
  have hSsum : ∀ p, HasSum (fun ξ : Fˣ => Sf ξ p) (S p) := by
    intro p
    refine Summable.hasSum (Summable.of_norm ?_)
    simp only [hSfb]
    exact (hsum p).mul_right _
  have hbound : Integrable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F =>
      ∑' ξ : Fˣ, ‖coefK c Y (tau p.1 p.2) ξ‖ * (p.1 : ℝ)) (muE F) := by
    simp only [tsum_mul_right]
    exact hint
  have hSint : HasSum (fun ξ : Fˣ => ∫ p, Sf ξ p ∂(muE F)) (∫ p, S p ∂(muE F)) :=
    hasSum_integral_of_dominated_convergence (fun ξ p => ‖coefK c Y (tau p.1 p.2) ξ‖ * (p.1 : ℝ)) hSfm
      (fun ξ => Eventually.of_forall fun p => (hSfb ξ p).le)
      (Eventually.of_forall fun p => (hsum p).mul_right _) hbound (Eventually.of_forall hSsum)
  have hSm : AEStronglyMeasurable S (muE F) := by
    refine aestronglyMeasurable_of_tendsto_ae (u := atTop) (f := fun s p => ∑ ξ ∈ s, Sf ξ p)
      (fun s => by
        have h := Finset.aestronglyMeasurable_sum (μ := muE F) s fun ξ _ => hSfm ξ
        convert h using 1
        funext p
        simp [Finset.sum_apply]) (Eventually.of_forall fun p => (hSsum p))
  have hS : Integrable S (muE F) := by
    refine hbound.mono' hSm (Eventually.of_forall fun p => ?_)
    rw [← (hSsum p).tsum_eq]
    refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
    · simp only [hSfb]; exact (hsum p).mul_right _
    · simp only [hSfb]
  have hN : Integrable N (muE F) := by
    have h1 : Integrable (fun p => eisInt ω (Phi c) g p.1 p.2 / D - A0 p - S p) (muE F) :=
      ((hT.div_const D).sub hA0).sub hS
    refine h1.congr (Eventually.of_forall fun p => ?_)
    simp only [hpt p]
    field_simp
    ring

  have hN0 : ∫ p, N p ∂(muE F) = 0 := by
    rw [integral_prod N hN]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hN.prod_right_ae] with t ht
    have h2 : IntegrableOn (fun u => coefK c Y (tau t u) 0 * ((ω.1 (tau t u) : ℂˣ) : ℂ)⁻¹)
        (normOneFundamentalDomain F) (normOneMeasure F) := by
      have h3 := ht.mul_const (((t : ℝ) : ℂ)⁻¹)
      refine h3.congr (Eventually.of_forall fun u => ?_)
      have ht0 : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 t.2.ne'
      simp only [N, wt]
      field_simp
    have h4 := hNl F ω c H y yf t h2
    simp only [Pi.zero_apply, N, wt]
    simp_rw [← mul_assoc]
    rw [integral_mul_const, h4, zero_mul]

  have hcoef : ∀ ξ : Fˣ, ∫ p, Sf ξ p ∂(muE F) = ex (ξ : F) x * (C₀ * if ∀ v, 0 < reAt v (ξ : F) then
        coefAt (divS ω c) (algebraMap F (Af F) (ξ : F) * (yf : Af F)) *
          Complex.exp (-(2 * Real.pi : ℂ) * ∑ v, (reAt v (ξ : F) : ℂ) * (y.val v : ℂ))
      else 0) := by
    intro ξ
    obtain ⟨hi, he⟩ := hloc y hy yf ξ
    simp only [Sf, mul_assoc]
    rw [integral_const_mul, hU F ω c H Y ξ hi, he]

  have htot : Eis ω (Phi c) g = (∫ p, A0 p ∂(muE F) + ∫ p, S p ∂(muE F)) * D := by
    have h1 : Eis ω (Phi c) g = ∫ p, eisInt ω (Phi c) g p.1 p.2 ∂(muE F) := by
      rw [Eis, integral_prod _ hT]
    rw [h1]
    simp only [hpt]
    rw [integral_mul_const, integral_add (f := fun a => A0 a + N a) (hA0.add hN) hS, integral_add hA0 hN, hN0,
      add_zero]
  have hDeq : D = ((((∏ v, y.val v) * absF yf) ^ (((1 : ℕ) : ℝ) / 2) : ℝ) : ℂ) := by
    rw [hDdef, absD_gPt x y hy yf]
    norm_num
  have hval : Eis ω (Phi c) (UpperTheory.V.TR.infGL F 2 (aff y x) * finGL F 2 (aff yf 0)) /
      ((((∏ v, y.val v) * absF yf) ^ (((1 : ℕ) : ℝ) / 2) : ℝ) : ℂ) - ∫ p, A0 p ∂(muE F) = ∫ p, S p ∂(muE F) := by
    rw [gPt_eq, ← hDeq, htot]
    field_simp
    ring
  rw [hval]
  let e : {ξ : F // ∀ v, 0 < reAt v ξ} → Fˣ := fun ξ => Units.mk0 ξ.1 (ne_zero_of_pos ξ.2)
  have he : Function.Injective e := fun a b h => Subtype.ext (congrArg Units.val h)
  have hout : ∀ ξ ∉ Set.range e, (fun ξ : Fˣ => ∫ p, Sf ξ p ∂(muE F)) ξ = 0 := by
    intro ξ hξ
    simp only [hcoef]
    rw [if_neg, mul_zero, mul_zero]
    intro hpos
    exact hξ ⟨⟨ξ, hpos⟩, Units.ext rfl⟩
  have h2 := (he.hasSum_iff hout).2 hSint
  convert h2 using 1
  funext ξ
  have hξ2 := ξ.2
  simp only [Function.comp_apply, hcoef, e, Units.val_mk0, hξ2, implies_true, ↓reduceIte]
  show coefAt (fun 𝔪 => C₀ * divS ω c 𝔪) _ * _ = _
  rw [coefAt_const_mul, ex]
  have hs : ∑ v, (reAt v ξ.1 : ℂ) * ((x v : ℂ) + Complex.I * (y.val v : ℂ)) =
      ∑ v, (reAt v ξ.1 : ℂ) * (x v : ℂ) + Complex.I * ∑ v, (reAt v ξ.1 : ℂ) * (y.val v : ℂ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  have hexp : Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v ξ.1 : ℂ) * ((x v : ℂ) + Complex.I * (y.val v : ℂ))) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v ξ.1 : ℂ) * (x v : ℂ)) *
        Complex.exp (-(2 * Real.pi : ℂ) * ∑ v, (reAt v ξ.1 : ℂ) * (y.val v : ℂ)) := by
    rw [← Complex.exp_add, hs]
    congr 1
    linear_combination (2 * (Real.pi : ℂ) * ∑ v, (reAt v ξ.1 : ℂ) * (y.val v : ℂ)) * Complex.I_sq
  rw [hexp]
  ring

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

namespace UpperTheory.HilbertEisensteinWeightOne

theorem fourier_expansion_holds : SPois → SInt → SSmooth → SExp := fun hP hI _ =>
  FourierExpansionEisenstein.sExp_assembly (FourierExpansionEisenstein.pointwise_theta_expansion hP FourierExpansionEisenstein.finite_expansion_holds FourierExpansionEisenstein.kernel_expansion_holds) FourierExpansionEisenstein.zero_term_holds
    (FourierExpansionEisenstein.null_term_holds FourierExpansionEisenstein.finite_expansion_holds FourierExpansionEisenstein.kernel_expansion_holds) (FourierExpansionEisenstein.absolute_convergence_holds FourierExpansionEisenstein.finite_expansion_holds FourierExpansionEisenstein.kernel_expansion_holds) FourierExpansionEisenstein.sUnfold_statement (FourierExpansionEisenstein.local_expansion_holds FourierExpansionEisenstein.finite_expansion_holds FourierExpansionEisenstein.kernel_expansion_holds) hI

end UpperTheory.HilbertEisensteinWeightOne
