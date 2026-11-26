module

public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.VectorComplexifiedDerivativeCommutator
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactGeneratorRaisesPfil
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactArrFiniteDimensional
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero

@[expose] public section

section -- merged from Formalism.RealPlaceAnalysis.IsRightTranslationIsometric
open MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.REAL

structure HidaSetting (n : ℕ) (ε : Fin n → Bool) where
  E : Type
  [ng : NormedAddCommGroup E]
  [ips : InnerProductSpace ℂ E]
  [cs : CompleteSpace E]
  S : Subgroup (UJ ε)
  σ : S → E →ₗᵢ[ℂ] E
  ν : Measure (UJ ε)

attribute [instance] HidaSetting.ng HidaSetting.ips HidaSetting.cs

def Rs {n : ℕ} {ε : Fin n → Bool} {E : Type*} (h : UJ ε) (F : UJ ε → E) : UJ ε → E :=
  fun g => F (g * h)

end Formalism.REAL
end
end

namespace Formalism.REAL
theorem kHaar : KHaar := compact_haar_holds
theorem kExp : KExp := compact_exponential_surjective
theorem genExp : GenExp := genExp_of kExp
theorem rdExtV : RdExtV := vector_right_derivative_extends
theorem rdLeftV : RdLeftV := vector_right_derivative_left_invariant
theorem rdSmoothV : RdSmoothV := rdSmoothV_of rdExtV
theorem rdLinV : RdLinV := rdLinV_of rdExtV
theorem rdBracketV : RdBracketV := rdBracketV_of rdExtV rdSmoothV
theorem eabGlV : EabGlV := eabGlV_of rdLinV rdBracketV rdSmoothV
theorem rdVPair : RdVPair := rdVPair_of rdExtV
theorem ecSumV : EcSumV := ecSumV_of rdLinV
theorem kWtOrth : KWtOrth := compact_weight_orthogonal
theorem kLow : KLow := compact_lowering_holds
theorem kCasSpan : KCasSpan := compact_casimir_span_holds
theorem kOrth : KOrth := kOrth_of kLow kWtOrth
theorem kHiUniq : KHiUniq := kHiUniq_of kLow kWtOrth kOrth
theorem kHiExist : KHiExist := highestWeightExists_holds
theorem kIrr : KIrr := kIrr_of kHiExist kHiUniq
theorem kDecomp : KDecomp := kDecomp_of kHiExist kOrth
theorem kIsoSplit : KIsoSplit := kIsoSplit_of kDecomp kOrth
theorem kWtBound : KWtBound := kWtBound_of kCasSpan
theorem kCasBound : KCasBound := kCasBound_of kDecomp kCasSpan kOrth
theorem casOnCyc : CasOnCyc := casimir_on_cyclic_holds
theorem pfilFacts : PfilFacts := pfil_facts_hold
theorem arrModule : ArrModule := arr_module_facts
theorem thetaFil : ThetaFil := theta_filtration_holds
theorem hVCoeff : HVCoeff := hVCoeff_of kLow kWtOrth arrModule
theorem typesSplit : TypesSplit := typesSplit_of hVCoeff kIsoSplit arrModule
theorem casArr : CasArr := casArr_of kCasSpan
theorem omSymSlice : OmSymSlice := symmetricSliceMixedCasimir_holds
theorem nStable : NStable := positiveArraysInvariant_holds
theorem omPlus : OmPlus := omPlus_of kDecomp kOrth kCasSpan casArr arrModule
theorem nPos : NPos := nPos_of casArr omSymSlice omPlus
end Formalism.REAL
