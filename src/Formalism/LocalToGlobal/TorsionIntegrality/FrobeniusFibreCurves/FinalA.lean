module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.EvalSecondZeroAtVariableZero
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.PderivZeroZeroWeierstrassDifference
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.BaseChangeCompatible

@[expose] public section

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.RestrictSecondZeroInVarOne
noncomputable section

namespace Formalism.L2.Th1.B.Add1

open Formalism.InvariantFactorPaths.G7 (at1)

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [CharZero K]

def at1H {ι : Type} (x : ι) : PowerSeries K →ₐ[K] MvPowerSeries ι K :=
  PowerSeries.substAlgHom (PowerSeries.HasSubst.X x)

theorem triple_lintegral_eq {ι : Type} (x : ι) (f : PowerSeries K) : at1 x f = at1H x f := by
  simp only [Formalism.InvariantFactorPaths.G7.at1, at1H, PowerSeries.coe_substAlgHom]

theorem inVarAlgHom_C {ι : Type} (x : ι) (c : K) :
    at1H x (PowerSeries.C c) = (MvPowerSeries.C c : MvPowerSeries ι K) := by
  rw [← triple_lintegral_eq]
  exact PowerSeries.subst_C c

theorem cc_psubst {ι : Type} {a : MvPowerSeries ι K} (ha : MvPowerSeries.constantCoeff a = 0)
    {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero ha f hf

theorem constantCoeff_inVar_eq_zero {ι : Type} (x : ι) {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (at1 x f) = 0 :=
  cc_psubst (MvPowerSeries.constantCoeff_X x) hf

theorem pd_mul {ι : Type} (i : ι) (x y : MvPowerSeries ι K) :
    pd i (x * y) = x * pd i y + y * pd i x := by
  simp only [Formalism.L2.Th1.B.pd, Derivation.leibniz, smul_eq_mul]

theorem pd_sub {ι : Type} (i : ι) (x y : MvPowerSeries ι K) : pd i (x - y) = pd i x - pd i y :=
  map_sub (MvPowerSeries.pderiv (R := K) i) x y

theorem fLog_one (h1 : ExpLogRules) {ι : Type} : fLog (1 : MvPowerSeries ι K) = 0 := by
  obtain ⟨hA, hB, -⟩ := h1 K ι
  have h0 : MvPowerSeries.constantCoeff (0 : MvPowerSeries ι K) = 0 := map_zero _
  have hsq : Formalism.L2.Th1.B.fExp (0 : MvPowerSeries ι K) * Formalism.L2.Th1.B.fExp 0 = Formalism.L2.Th1.B.fExp 0 * 1 := by
    rw [← hA 0 0 h0 h0, add_zero, mul_one]
  have hu : IsUnit (Formalism.L2.Th1.B.fExp (0 : MvPowerSeries ι K)) :=
    MvPowerSeries.isUnit_iff_constantCoeff.mpr (by rw [(hB 0 h0).1]; exact isUnit_one)
  have he : Formalism.L2.Th1.B.fExp (0 : MvPowerSeries ι K) = 1 := hu.mul_left_cancel hsq
  have hl := (hB 0 h0).2
  rw [he] at hl
  exact hl

end SlopeTestRemainingChoices


end Formalism.L2.Th1.B.Add1
end
end

namespace Formalism.L2.Th1.B

theorem expLogRules : ExpLogRules := by
  intro K _ _ ι
  exact ⟨fun f g hf hg => fExp_add hf hg, fun f hf => ⟨constantCoeff_fExp hf, fLog_fExp hf⟩,
    fun g hg => ⟨constantCoeff_fLog hg, fExp_fLog hg⟩⟩
theorem expLogDeriv : ExpLogDeriv := by
  intro K _ _ ι _ i
  exact ⟨fun f hf => pd_fExp i hf, fun g hg => mul_pd_fLog i hg⟩
theorem expLogSubst : ExpLogSubst := by
  intro K _ _ ι κ _ φ hφ
  exact ⟨fun f hf => subst_fExp hφ hf, fun g hg => subst_fLog hφ hg⟩
theorem primRules : PrimRules := by
  intro K _ _ f
  exact ⟨dz_prim f, constantCoeff_prim f⟩
theorem waveUnique : WaveUnique := wave_equation_unique
theorem waveKills : WaveKills := wave_operator_kills
theorem parCauchy : ParCauchy := parallelogram_cauchy_equation
theorem dqRule : DqRule := difference_quotient_rule_holds
theorem wpReduced : WpReduced := weierstrassReducedEquations
theorem wSecond : WSecond := invertedSecondDeriv
theorem wOfWp : WOfWp := shiftedReciprocalInverted
theorem addSigmaLog : AddSigmaLog :=
  AddSigmaLog_of expLogDeriv expLogSubst primRules waveUnique waveKills parCauchy wpReduced dqRule
theorem addSigma : AddSigma := AddSigma_of addSigmaLog expLogRules expLogSubst dqRule
theorem addSgStar : AddSgStar := AddSgStar_of addSigma expLogRules expLogSubst
theorem sigma1Sq : Sigma1Sq := Sq.sigmaOneSquare

end Formalism.L2.Th1.B
