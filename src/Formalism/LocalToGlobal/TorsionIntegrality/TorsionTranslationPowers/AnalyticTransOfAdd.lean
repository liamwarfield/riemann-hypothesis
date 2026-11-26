module

public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.FacShapeZero
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ExistsFinitePartOneIdeleSplitCongruenceQuotient
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ScaledTorsionPointNonsingular

@[expose] public section

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.OpUTh0RootOf
open scoped ComplexConjugate

namespace Formalism.L2.Th1.E

namespace OperatorUThetaLemmas

open Formalism.L2.Th1.F

theorem opU_const_mul (L : PeriodPair) (x a : ℂ) (f : ℂ → ℂ) :
    opU L x (fun z => a * f z) = fun z => a * opU L x f z := by
  funext z
  simp only [opU]
  ring

theorem altE_nat_mul (L : PeriodPair) (N : ℕ) (x y : ℂ) :
    altE L ((N : ℂ) * x) ((N : ℂ) * y) = (N : ℝ) ^ 2 * altE L x y := by
  have h : herm L ((N : ℂ) * x) ((N : ℂ) * y) = (((N : ℝ) ^ 2 : ℝ) : ℂ) * herm L x y := by
    simp only [herm, map_mul, Complex.conj_natCast]
    push_cast
    ring
  simp only [altE, h, Complex.im_ofReal_mul]

theorem exp_altE_pow (L : PeriodPair) (N : ℕ) (x y : ℂ)
    (hx : (N : ℂ) * x ∈ L.lattice) (hy : (N : ℂ) * y ∈ L.lattice) :
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE L x y : ℂ)) ^ (2 * N ^ 2) = 1 := by
  obtain ⟨k, hk⟩ := altEInt L _ _ hx hy
  rw [altE_nat_mul] at hk
  have hk' : ((N : ℂ)) ^ 2 * (altE L x y : ℂ) = (k : ℂ) := by
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hk
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  refine ⟨-k, ?_⟩
  push_cast
  rw [← hk']
  ring

end OperatorUThetaLemmas

open Formalism.L2.Th1.F in
theorem OpUTh0Root_of : OpUTh0Root := by
  intro L t t₀ N hN ht ht₀ _
  refine ⟨Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE L t t₀ : ℂ)), 2 * N ^ 2, by positivity,
    OperatorUThetaLemmas.exp_altE_pow L N t t₀ ht ht₀, ?_⟩
  have h0 : th0 L t₀ = fun z => (opU L t₀ (sgStar L) 0)⁻¹ * opU L t₀ (sgStar L) z := by
    funext z
    simp only [th0]
    rw [div_eq_mul_inv, mul_comm]
  rw [h0, OperatorUThetaLemmas.opU_const_mul]
  funext z
  rw [opUMul L t t₀ (sgStar L) z]
  ring

end Formalism.L2.Th1.E
end

namespace Formalism.L2.Th1.E

theorem generalIntOf : GeneralIntOf := general_integrality
theorem torsionIntegral : TorsionIntegral := torsion_integral
theorem ptOfZero : PtOfZero := PtOfZero_of
theorem wpBridge : WpBridge := AnaSys.wpBridge
theorem transWpBridge : TransWpBridge := AnaSys.transWpBridge
theorem analyticSys : AnalyticSys := AnalyticSys_of transWpBridge
theorem opUTh0Root : OpUTh0Root := OpUTh0Root_of

theorem ptOfInt_of_add (hA : PtOfAdd) : PtOfInt := PtOfInt_of hA ptOfZero torsionIntegral
theorem kernelPtInt_of_add (hA : PtOfAdd) : KernelPtInt := KernelPtInt_of (ptOfInt_of_add hA)
theorem cm4Int_of_add (hA : PtOfAdd) : CMIntegrality := cm_integrality_of_torsion_points (ptOfInt_of_add hA)
theorem analyticTrans_of_add (hA : PtOfAdd) : AnalyticTrans :=
  AnalyticTrans_of analyticSys hA ptOfZero (ptOfInt_of_add hA) transUnit
theorem th0Analytic_of_add (hA : PtOfAdd) : ThetaZeroAnalytic :=
  Th0Analytic_of analyticSys hA ptOfZero (ptOfInt_of_add hA) transUnit transGauss opUTh0Root

theorem ptOfAdd : PtOfAdd := PtOfAdd_of
theorem ptOfInt : PtOfInt := ptOfInt_of_add ptOfAdd
theorem kernelPtInt : KernelPtInt := kernelPtInt_of_add ptOfAdd
theorem cm4Int : CMIntegrality := cm4Int_of_add ptOfAdd
theorem analyticTrans : AnalyticTrans := analyticTrans_of_add ptOfAdd
theorem th0Analytic : ThetaZeroAnalytic := th0Analytic_of_add ptOfAdd

end Formalism.L2.Th1.E
