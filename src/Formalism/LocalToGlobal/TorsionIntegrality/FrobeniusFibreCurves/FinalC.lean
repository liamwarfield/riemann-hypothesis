module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalB
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.TwoTorsionU
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementW
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementK
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementD

@[expose] public section

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalC
section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.NormHalfB2SubTwoTorsionLeOne
noncomputable section

namespace Formalism.L2.Th1.B.Crv

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
open Formalism.L2.Th1.A (fgl iSer logSer wpReg g₂ g₃ IntModel xS bridgeWp bridgeLaw bridgeCurve)

section Alg

variable {K : Type} [Field K] [CharZero K]

theorem kap_eq (W : WeierstrassCurve K) (xT yT : K) (h2 : 2 * yT + W.a₁ * xT + W.a₃ = 0) :
    kapW W xT = 3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT := by
  unfold kapW e1W g₂ WeierstrassCurve.c₄ WeierstrassCurve.b₂ WeierstrassCurve.b₄
  linear_combination (W.a₁ / 2) * h2

theorem two_torsion_x_root_of_cubic (W : WeierstrassCurve K) (xT yT : K) (hE : W.toAffine.Equation xT yT)
    (h2 : 2 * yT + W.a₁ * xT + W.a₃ = 0) :
    4 * e1W W xT ^ 3 - g₂ W * e1W W xT - g₃ W = 0 := by
  rw [WeierstrassCurve.Affine.equation_iff] at hE
  unfold e1W g₂ g₃ WeierstrassCurve.c₄ WeierstrassCurve.c₆ WeierstrassCurve.b₂
    WeierstrassCurve.b₄ WeierstrassCurve.b₆
  linear_combination (2 * yT + W.a₁ * xT + W.a₃) * h2 - 4 * hE

end Alg

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_add_le_one {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

theorem norm_sub_le_one {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact norm_add_le_one ha (by rwa [norm_neg])

theorem norm_mul_le_one' {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ ha (norm_nonneg b) hb

theorem norm_kap [CharZero K] (W : WeierstrassCurve K) (xT yT : K) (hW : IntModel W)
    (h2 : 2 * yT + W.a₁ * xT + W.a₃ = 0) (hx : ‖xT‖ ≤ 1) (hy : ‖yT‖ ≤ 1) :
    ‖kapW W xT‖ ≤ 1 := by
  obtain ⟨h1, h2', -, h4, -⟩ := hW
  rw [kap_eq W xT yT h2]
  have n3 : ‖(3 : K)‖ ≤ 1 := by exact_mod_cast IsUltrametricDist.norm_natCast_le_one K 3
  have n2 : ‖(2 : K)‖ ≤ 1 := by exact_mod_cast IsUltrametricDist.norm_natCast_le_one K 2
  have hxx : ‖xT ^ 2‖ ≤ 1 := by
    rw [pow_two]
    exact norm_mul_le_one' hx hx
  exact norm_sub_le_one
    (norm_add_le_one
      (norm_add_le_one (norm_mul_le_one' n3 hxx) (norm_mul_le_one' (norm_mul_le_one' n2 h2') hx))
      h4)
    (norm_mul_le_one' h1 hy)

end Norm

theorem curve_sigma_function_holds : CurveSigma := by
  intro K _ _ W s2
  obtain ⟨h0, h1⟩ := phODef K s2 (wpReg W) (logSer W) (Formalism.L2.Th1.A.ZSer.log_cc W)
    (Formalism.L2.Th1.A.ZSer.log_one W)
  exact ⟨h0, h1, addSgStar K (g₂ W) (g₃ W) s2 (wpReg W) (bridgeWp K W)⟩

theorem curve_formal_first_level_holds : WeierstrassBiadditiveModEquiv := by
  intro K _ _ _ W s2 hW h2
  obtain ⟨hF, hi, -⟩ := bridgeLaw K W hW
  exact f1O K (g₂ W) (g₃ W) s2 (W.b₂ / 12) (wpReg W) (logSer W) (iSer W) (xS W) (fgl W)
    (bridgeWp K W) hF hi (bridgeCurve K W hW) h2

end Formalism.L2.Th1.B.Crv
end
end

namespace Formalism.L2.Th1.B

theorem baseChange : BaseChange := Map.baseChangeCompatible
theorem curveSigma : CurveSigma := Crv.curve_sigma_function_holds
theorem weierstrass_biadditive_mod_equiv : WeierstrassBiadditiveModEquiv := Crv.curve_formal_first_level_holds

end Formalism.L2.Th1.B
end

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementI
section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.IsFibreCurve
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B

open Formalism.L2.Th1.C (wpShift HasSecondLogDeriv wTr)

section Alg

variable {K : Type} [Field K] [CharZero K]

abbrev phTw (g2 s2 c0 xT : K) (P l : PowerSeries K) : PowerSeries K :=
  phE s2 (xT + c0) (3 * (xT + c0) ^ 2 - g2 / 4) (wOf (xT + c0) P) l

abbrev thTw (g2 s2 c0 xT : K) (P : PowerSeries K) : PowerSeries K :=
  thZ s2 (xT + c0) (3 * (xT + c0) ^ 2 - g2 / 4) (wOf (xT + c0) P)

def IsFibreZ (P tr : PowerSeries K) {ι : Type} [Fintype ι] (c : ι → K)
    (wp wm : ι → PowerSeries K) (al S : K) : Prop :=
  (∀ Q, HasSecondLogDeriv (wpShift P (c Q)) (2 * P - wp Q - wm Q)) ∧
    PowerSeries.C (al ^ 2) * PowerSeries.rescale al tr = ∑ Q, (wp Q + wm Q) - PowerSeries.C S

end Alg

end Formalism.L2.Th1.B
end
end

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
open Formalism.G (unitBall)
open Formalism.L2.Th1.C (wpShift HasSecondLogDeriv wTr IsLogPair mulBy EndInt PhNormAt IsBinomScalar)
open Formalism.L2.Th1.A (fgl iSer logSer expSer wpReg g₂ g₃ IntModel)

def Th0Isogeny : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 s2 c0 xT al S : K) (P : PowerSeries K)
    (ι : Type) [Fintype ι] (c : ι → K) (wp wm : ι → PowerSeries K),
    IsWp g2 g3 P → 4 * (xT + c0) ^ 3 - g2 * (xT + c0) - g3 = 0 →
    IsFibreZ P (PowerSeries.C (xT + c0) +
      PowerSeries.C (3 * (xT + c0) ^ 2 - g2 / 4) * wOf (xT + c0) P) c wp wm al S →
    (al ^ 2 - 2 * (Fintype.card ι : K)) * s2 = S →
    PowerSeries.rescale al (thTw g2 s2 c0 xT P) * wpShift P (xT + c0) ^ Fintype.card ι =
      thTw g2 s2 c0 xT P ^ (2 * Fintype.card ι) * ∏ Q, wpShift P (c Q)

def PhENorm : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 s2 c0 xT al albar S : K)
    (P l linv i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K)
    (ι : Type) [Fintype ι] (xQ : ι → K) (wp wm : ι → PowerSeries K),
    IsWp g2 g3 P → 4 * (xT + c0) ^ 3 - g2 * (xT + c0) - g3 = 0 → IsLogPair l linv →
    CurveHyp F i l P ep c0 → ‖xT‖ ≤ 1 → (∀ Q, ‖xQ Q‖ ≤ 1) →
    IsFibreZ P (PowerSeries.C (xT + c0) +
      PowerSeries.C (3 * (xT + c0) ^ 2 - g2 / 4) * wOf (xT + c0) P)
      (fun Q => xQ Q + c0) wp wm al S →
    al * albar = 2 * (Fintype.card ι : K) → al * (al - albar) * s2 = S →
    PhNormAt (unitBall K) l linv (phTw g2 s2 c0 xT P l) al albar

def ThetaZeroVanishing : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K]
    (g2 g3 s2 c0 a1 a3 xT yT al albar S : K)
    (P l linv i ep : PowerSeries K) (F : MvPowerSeries (Fin 2) K)
    (ι : Type) [Fintype ι] (xQ : ι → K) (wp wm : ι → PowerSeries K),
    IsWp g2 g3 P → LawLog F l → IsInv l i → IsLogPair l linv → CurveHyp F i l P ep c0 →
    CurveHyp3 F l P ep a1 a3 → TwoHyp g2 g3 c0 a1 a3 xT yT → (∀ Q, ‖xQ Q‖ ≤ 1) →
    IsFibreZ P (PowerSeries.C (xT + c0) +
      PowerSeries.C (3 * (xT + c0) ^ 2 - g2 / 4) * wOf (xT + c0) P)
      (fun Q => xQ Q + c0) wp wm al S →
    al * albar = 2 * (Fintype.card ι : K) → al * (al - albar) * s2 = S →
    EndInt (unitBall K) l linv al → al ∈ closure (Set.range (fun n : ℤ => (n : K))) →
    al ≠ 0 → al ≠ albar → albar ≠ 1 →
    IsBinomScalar (unitBall K) (al * (al - albar))⁻¹ →
    IsBinomScalar (unitBall K) (al * (1 - albar))⁻¹ →
    Simeq (ι := Unit) (phTw g2 s2 c0 xT P l) 0 ∧
      PowerSeries.constantCoeff (PowerSeries.subst l (thTw g2 s2 c0 xT P)) = 1 ∧
      Integral (ι := Unit) (PowerSeries.subst l (thTw g2 s2 c0 xT P))

def TwoAdicScalars : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [NormedAlgebra ℚ_[2] K]
    (F : MvPowerSeries (Fin 2) K) (l linv : PowerSeries K) (b b' : ℤ_[2]),
    LawLog F l → IsLogPair l linv → ‖b‖ = 1 → ‖b'‖ < 1 →
    let al : K := algebraMap ℚ_[2] K (b : ℚ_[2])
    let albar : K := algebraMap ℚ_[2] K (b' : ℚ_[2])
    EndInt (unitBall K) l linv al ∧ al ∈ closure (Set.range (fun n : ℤ => (n : K))) ∧
      al ≠ 0 ∧ al ≠ albar ∧ albar ≠ 1 ∧
      IsBinomScalar (unitBall K) (al * (al - albar))⁻¹ ∧
      IsBinomScalar (unitBall K) (al * (1 - albar))⁻¹

end Formalism.L2.Th1.B
end
end
