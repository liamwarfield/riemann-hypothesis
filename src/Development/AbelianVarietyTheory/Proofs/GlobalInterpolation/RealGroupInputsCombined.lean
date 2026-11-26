module

public import Formalism.LocalToGlobal.FiniteTOf
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
public import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankIsotEqIsotL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceInputsImplyCuspidalTrace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealStableOfCharacters
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSeparationOfIwahoriTrace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoefficientSeparation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LengthFilterFinRange
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalOperatorsVanishingRadicalIntegralsUnitarStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalTraceMultiplicityGiven
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EventuallyConstructedPointHostSizeNumerical

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fc.RL.LamLinked

theorem evP_params : EvP fun _ K => ∀ β : BPt K, Nonempty (ParameterChoice' β.D β.O.L) := by
  refine EvP.of_ev ⟨1, one_pos, fun eps C8 he _ he52 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hStd _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := szRow_numAt eps he he52 C hStd
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, hN⟩ := hN ch hch
  refine ⟨x0, fun K h1 h2 h3 h4 hx β => ?_⟩
  have hsc : β.O.L.sc = K.s := β.sc
  have hv : Val C cD ch β.O.L := by
    rw [← h1, ← h2, ← h3]
    exact β.p.pt_val β.val
  obtain ⟨⟨N⟩, -, -⟩ := hN _ _ (by rw [hsc, h4]) (by rw [hsc]; exact hx) hv (GlobalTheory.Plug.hostArith_bpt β)
  exact ⟨N.params⟩


end GlobalTheory.Fc.RL.LamLinked

namespace GlobalTheory.Fc.RL


end GlobalTheory.Fc.RL
