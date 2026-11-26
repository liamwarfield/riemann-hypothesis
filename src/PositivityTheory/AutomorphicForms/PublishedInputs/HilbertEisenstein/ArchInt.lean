module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SExpDefs

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.ArchInt
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published GroundTheory.LocalField

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L4

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def rc (a : (InfiniteAdeleRing F)ˣ) (v : InfinitePlace F) : ℝ :=
  (UpperTheory.V.TR.infEq F).symm (a : InfiniteAdeleRing F) v

def archK (y : (UpperTheory.V.TR.Rinf F)ˣ) (ξ : F) (a : (InfiniteAdeleRing F)ˣ) : ℂ :=
  ∏ v, ((((rc a v * y.val v + (rc a v)⁻¹ * reAt v ξ : ℝ)) : ℂ) *
    Complex.exp (-(Real.pi : ℂ) * (((rc a v * y.val v) ^ 2 + ((rc a v)⁻¹ * reAt v ξ) ^ 2 : ℝ) : ℂ)))

def ωI (ω : HChar F) (a : (InfiniteAdeleRing F)ˣ) : ℂ := ((ω.1 (ofInfinite a) : ℂˣ) : ℂ)

def chiW (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (w : HeightOneSpectrum (𝓞 F)) : ℂ :=
  if c w = 0 then ((ω.val w : ℂˣ) : ℂ) else 0

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L4

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open L4

def ArchInt : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ), Hyp ω c → ∀ (y : (UpperTheory.V.TR.Rinf F)ˣ), (∀ v, 0 < y.val v) → ∀ ξ : Fˣ,
    Integrable (fun a => archK y (ξ : F) a * (ωI ω a)⁻¹) (infiniteIdeleMeasure F) ∧
      ∫ a, archK y (ξ : F) a * (ωI ω a)⁻¹ ∂infiniteIdeleMeasure F =
        if ∀ v, 0 < reAt v (ξ : F) then (2 : ℂ) ^ Fintype.card (InfinitePlace F) *
          Complex.exp (-(2 * Real.pi : ℂ) * ∑ v, (reAt v (ξ : F) : ℂ) * (y.val v : ℂ)) else 0

def CoefDiv : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ) (z : Af F) (m : HeightOneSpectrum (𝓞 F) → ℤ) (S : Finset (HeightOneSpectrum (𝓞 F))),
    (∀ w, Valued.v (pLoc F w z) = WithZero.exp (dd w - m w)) → (∀ w ∉ S, m w = 0) →
    coefAt (divS ω c) z =
      if ∀ w ∈ S, 0 ≤ m w then ∏ w ∈ S, ∑ j ∈ Finset.range ((m w).toNat + 1), chiW ω c w ^ j else 0

def LocRam : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ), Hyp ω c → ∀ w : HeightOneSpectrum (𝓞 F), c w ≠ 0 →
    (∀ k : ℤ, -((c w : ℤ) + dd w) < k →
      ∫ x in ordShell (w.adicCompletion F) k, ((ω.loc w x : ℂˣ) : ℂ) *
        (localAdelicChar F w (x : w.adicCompletion F) : ℂ) ∂multHaar (w.adicCompletion F) = 0) ∧
    ∫ x in ordShell (w.adicCompletion F) (-((c w : ℤ) + dd w)), ((ω.loc w x : ℂˣ) : ℂ) *
        (localAdelicChar F w (x : w.adicCompletion F) : ℂ) ∂multHaar (w.adicCompletion F) ≠ 0

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.RightBilinearApply
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap ContDiff
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

abbrev Vr (F : Type) [Field F] [NumberField F] : Type := Fin 2 → UpperTheory.V.TR.Rinf F

def Xi (F : Type) [Field F] : Type := {ξ : Fin 2 → F // ξ ≠ 0}

instance : MeasurableSpace (Xi F) := ⊤

instance : MeasurableSingletonClass (Xi F) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

instance : Countable F := (Module.finBasis ℚ F).equivFun.toEquiv.injective.countable

instance : Countable (Xi F) := inferInstanceAs (Countable {ξ : Fin 2 → F // ξ ≠ 0})

abbrev Pp (F : Type) [Field F] [NumberField F] : Type := {r : ℝ // 0 < r} × normOneSubgroup F

def av (p : Pp F) : Ideles F := moduleSection (w0 F) p.1 * (p.2 : Ideles F)

def μS (F : Type) [Field F] [NumberField F] (S : Set {r : ℝ // 0 < r}) : Measure (Pp F × Xi F) :=
  ((posRealMeasure.restrict S).prod ((normOneMeasure F).restrict (normOneFundamentalDomain F))).prod
    Measure.count

def Mrow (g : GA F 2) (a : Ideles F) : GA F 2 := Matrix.GeneralLinearGroup.scalar (Fin 2) a * g

def Mcol (g : GA F 2) (a : Ideles F) : GA F 2 := g⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹

def rowv (g : GA F 2) (a : Ideles F) (ξ : Fin 2 → F) : Fin 2 → Ad F :=
  rowA ξ ᵥ* ((Mrow g a : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))

def colv (g : GA F 2) (a : Ideles F) (ξ : Fin 2 → F) : Fin 2 → Ad F :=
  ((Mcol g a : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ


open Classical in
def finRow (c : HeightOneSpectrum (𝓞 F) → ℕ) (y : Fin 2 → Ad F) : ℂ :=
  if ∀ w, Valued.v (pLoc F w (pFin F (y 0))) ≤ WithZero.exp (-(c w : ℤ)) ∧
      Valued.v (pLoc F w (pFin F (y 1)) - 1) ≤ WithZero.exp (-(c w : ℤ)) then 1 else 0


open Classical in
def finCol (c : HeightOneSpectrum (𝓞 F) → ℕ) (y : Fin 2 → Ad F) : ℂ :=
  if ∀ w, Valued.v (pLoc F w (pFin F (y 0))) ≤ WithZero.exp ((c w : ℤ) + dd w) ∧
      Valued.v (pLoc F w (pFin F (y 1))) ≤ WithZero.exp ((c w : ℤ) + dd w)
  then ((finiteAdelicChar F (pFin F (y 1)) : Circle) : ℂ) else 0

def vInf (y : Fin 2 → Ad F) : Vr F := fun i => UpperTheory.V.TR.pInf F (y i)

def kap1 (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (q : Pp F × Xi F) : ℂ :=
  finRow c (rowv g (av q.1) q.2.1) * ((χ.1 (av q.1) : ℂˣ) : ℂ)⁻¹ * ((q.1.1 : ℝ) : ℂ)

def w1 (g : GA F 2) (q : Pp F × Xi F) : Vr F := vInf (rowv g (av q.1) q.2.1)

def kap2 (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (q : Pp F × Xi F) : ℂ :=
  finCol c (colv g (av q.1) q.2.1) * ((χ.1 (av q.1) : ℂˣ) : ℂ)⁻¹ * ((q.1.1 : ℝ) : ℂ)⁻¹

def w2 (g : GA F 2) (q : Pp F × Xi F) : Vr F := vInf (colv g (av q.1) q.2.1)

def B1lin : Vr F →ₗ[ℝ] UpperTheory.V.TR.Lie F 2 →ₗ[ℝ] Vr F :=
  LinearMap.mk₂ ℝ (fun w x => w ᵥ* Matrix.of x)
    (fun w w' x => Matrix.add_vecMul _ _ _) (fun r w x => Matrix.smul_vecMul _ _ _)
    (fun w x x' => by exact Matrix.vecMul_add _ _ _)
    (fun r w x => by exact Matrix.vecMul_smul (R := ℝ) _ _ _)

def B2lin : Vr F →ₗ[ℝ] UpperTheory.V.TR.Lie F 2 →ₗ[ℝ] Vr F :=
  LinearMap.mk₂ ℝ (fun w z => Matrix.of z *ᵥ w)
    (fun w w' z => Matrix.mulVec_add _ _ _) (fun r w z => Matrix.mulVec_smul _ _ _)
    (fun w z z' => by exact Matrix.add_mulVec _ _ _)
    (fun r w z => by exact Matrix.smul_mulVec (R := ℝ) _ _ _)

def B1 : Vr F →L[ℝ] UpperTheory.V.TR.Lie F 2 →L[ℝ] Vr F :=
  LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ B1lin)

def B2 : Vr F →L[ℝ] UpperTheory.V.TR.Lie F 2 →L[ℝ] Vr F :=
  LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ B2lin)

@[simp] theorem left_bilinear_apply (w : Vr F) (x : UpperTheory.V.TR.Lie F 2) : B1 w x = w ᵥ* Matrix.of x := rfl

@[simp] theorem right_bilinear_apply (w : Vr F) (z : UpperTheory.V.TR.Lie F 2) : B2 w z = Matrix.of z *ᵥ w := rfl

def invL (x : UpperTheory.V.TR.Lie F 2) : UpperTheory.V.TR.Lie F 2 := UpperTheory.V.TR.toL (Matrix.of x)⁻¹

def dl (g : GA F 2) (x : UpperTheory.V.TR.Lie F 2) : ℝ := absD g * ∏ v, (Matrix.det (Matrix.of x)) v

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.HasTemperateGrowthArchPoly
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

def levelIdeal (c : HeightOneSpectrum (𝓞 F) → ℕ) : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  ∏ᶠ w, primeIdealUnit w ^ (c w : ℤ)

theorem count_levelIdeal {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite)
    (w : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F w ((levelIdeal c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) = c w := by
  unfold levelIdeal
  rw [count_finprod_primeIdealUnit_zpow]
  refine Filter.eventually_cofinite.2 (hc.subset fun v hv => ?_)
  simp only [Set.mem_setOf_eq, Nat.cast_eq_zero] at hv ⊢
  exact hv

theorem mem_level_iff {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (B : Af F) :
    B ∈ idealFiniteAdeles (levelIdeal c) ↔ ∀ w, Valued.v (pLoc F w B) ≤ WithZero.exp (-(c w : ℤ)) := by
  rw [mem_idealFiniteAdeles]
  refine forall_congr' fun w => ?_
  rw [count_levelIdeal hc]
  rfl

theorem count_different (w : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F w ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = dd w := by
  rw [FractionalIdeal.count_coe F w (differentIdeal_ne_bot (A := ℤ))]
  rfl

theorem mem_dual_iff {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (Z : Af F) :
    Z ∈ idealFiniteAdeles (traceDualIdeal F (levelIdeal c)) ↔
      ∀ w, Valued.v (pLoc F w Z) ≤ WithZero.exp ((c w : ℤ) + dd w) := by
  rw [mem_idealFiniteAdeles]
  refine forall_congr' fun w => ?_
  rw [count_traceDualIdeal, count_levelIdeal hc, count_different, neg_neg]
  rfl

theorem isEmpty_complex : IsEmpty {w : InfinitePlace F // IsComplex w} :=
  ⟨fun w => (not_isComplex_iff_isReal.2 (IsTotallyReal.isReal w.1)) w.2⟩

theorem prod_real (f : InfinitePlace F → ℂ) : ∏ w : {w : InfinitePlace F // IsReal w}, f w.1 = ∏ v, f v :=
  (Equiv.subtypeUnivEquiv (fun w : InfinitePlace F => IsTotallyReal.isReal w)).prod_comp f

def archPoly (a : InfinitePlace F → ℝ) (x : mixedSpace F) : ℂ :=
  ∏ w : {w : InfinitePlace F // IsReal w},
    (((a w.1 : ℝ) : ℂ) + Complex.I * ((x.1 w : ℝ) : ℂ)) * Complex.exp (-(π : ℂ) * ((a w.1 : ℝ) : ℂ) ^ 2)

theorem hasTemperateGrowth_archPoly (a : InfinitePlace F → ℝ) : (archPoly (F := F) a).HasTemperateGrowth := by
  unfold archPoly
  refine hasTemperateGrowth_finsetProd _ fun w _ => ?_
  have hlin : (fun x : mixedSpace F => ((x.1 w : ℝ) : ℂ)).HasTemperateGrowth :=
    ((Complex.ofRealCLM.comp ((ContinuousLinearMap.proj w :
      ({w // IsReal w} → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ ({w // IsReal w} → ℝ)
        ({w // IsComplex w} → ℂ))) : mixedSpace F →L[ℝ] ℂ)).hasTemperateGrowth
  exact ((HasTemperateGrowth.const _).add ((HasTemperateGrowth.const Complex.I).mul hlin)).mul
    (HasTemperateGrowth.const _)

def archSchwartz (a : InfinitePlace F → ℝ) : 𝓢(mixedSpace F, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (archPoly a)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedToEuclidean F)
      (gaussianSchwartz (euclidean.mixedSpace F)))

theorem archSchwartz_apply (a : InfinitePlace F → ℝ) (x : mixedSpace F) :
    archSchwartz a x = archPoly a x * ((Real.exp (-π * (∑ w, x.1 w ^ 2 + 2 * ∑ w, ‖x.2 w‖ ^ 2)) : ℝ) : ℂ) := by
  rw [archSchwartz, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_archPoly a),
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, gaussianSchwartz_apply,
    norm_mixedToEuclidean_sq, smul_eq_mul]

theorem archSchwartz_eq_prod (a : InfinitePlace F → ℝ) (x : mixedSpace F) :
    archSchwartz a x = ∏ w : {w : InfinitePlace F // IsReal w},
      (((a w.1 : ℝ) : ℂ) + Complex.I * ((x.1 w : ℝ) : ℂ)) *
        Complex.exp (-(π : ℂ) * (((a w.1 : ℝ) : ℂ) ^ 2 + ((x.1 w : ℝ) : ℂ) ^ 2)) := by
  haveI := isEmpty_complex (F := F)
  rw [archSchwartz_apply, archPoly, Finset.univ_eq_empty (α := {w : InfinitePlace F // IsComplex w}),
    Finset.sum_empty, mul_zero, add_zero, Finset.mul_sum, Real.exp_sum, Complex.ofReal_prod,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem archSchwartz_homeo (A B : Ad F) :
    archSchwartz (UpperTheory.V.TR.pInf F A) (homeomorphMixedSpace F B.1) =
      arch (UpperTheory.V.TR.pInf F A) (UpperTheory.V.TR.pInf F B) := by
  rw [archSchwartz_eq_prod, arch]
  exact prod_real (fun v => (((UpperTheory.V.TR.pInf F A v : ℝ) : ℂ) + Complex.I * ((UpperTheory.V.TR.pInf F B v : ℝ) : ℂ)) *
    Complex.exp (-(π : ℂ) * (((UpperTheory.V.TR.pInf F A v : ℝ) : ℂ) ^ 2 + ((UpperTheory.V.TR.pInf F B v : ℝ) : ℂ) ^ 2)))

open Classical in
theorem slice_eq {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (A : Ad F) :
    slice c A = (if ∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ)) then (1 : ℂ) else 0) •
      schwartzBruhatTensor (archSchwartz (UpperTheory.V.TR.pInf F A)) (cosetIndicator (levelIdeal c) 1) := by
  funext B
  simp only [slice, Phi, Pi.smul_apply, smul_eq_mul, schwartzBruhatTensor, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [archSchwartz_homeo, cosetIndicator_apply, mem_level_iff hc]
  have hB : ∀ w, pLoc F w (B.2 - 1) = pLoc F w (pFin F B) - 1 := fun w => by
    rw [map_sub, map_one]; rfl
  simp only [hB]
  by_cases h1 : ∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ))
  · by_cases h2 : ∀ w, Valued.v (pLoc F w (pFin F B) - 1) ≤ WithZero.exp (-(c w : ℤ))
    · have h3 : ∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ)) ∧
          Valued.v (pLoc F w (pFin F B) - 1) ≤ WithZero.exp (-(c w : ℤ)) := fun w => ⟨h1 w, h2 w⟩
      simp only [forall_and, h1, h2, and_self, implies_true, ↓reduceIte, mul_one, one_mul]
    · have h3 : ¬ ∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ)) ∧
          Valued.v (pLoc F w (pFin F B) - 1) ≤ WithZero.exp (-(c w : ℤ)) := fun h => h2 fun w => (h w).2
      simp only [forall_and, h1, h2, true_and, and_false, ↓reduceIte, mul_zero, one_mul]
  · have h3 : ¬ ∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ)) ∧
        Valued.v (pLoc F w (pFin F B) - 1) ≤ WithZero.exp (-(c w : ℤ)) := fun h => h1 fun w => (h w).1
    simp only [forall_and, h1, false_and, ↓reduceIte, mul_zero, zero_mul]

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L1

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem slice_mem_sb {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (A : Ad F) :
    slice c A ∈ schwartzBruhat F := by
  rw [L1.slice_eq hc A]
  exact Submodule.smul_mem _ _ (schwartzBruhatTensor_mem _ (cosetIndicator_mem_finiteSchwartzBruhat _ _))

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end
