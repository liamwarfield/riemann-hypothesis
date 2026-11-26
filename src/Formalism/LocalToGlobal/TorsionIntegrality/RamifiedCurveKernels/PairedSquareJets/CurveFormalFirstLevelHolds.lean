module

public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveSecondLogDerivative
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalB
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementK
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Hurwitz
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.HurwitzB
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.BridgeTwoMore
public import Formalism.GaussJetBounds.FinalB

@[expose] public section

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.CurveFormalFirstLevelHolds
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg xS xPlus)
open Formalism.G (unitBall)

namespace WeierstrassCurveSeries

theorem rescale_neg_one_of_even {K : Type} [Field K] (e : PowerSeries K)
    (h : ∀ n : ℕ, Odd n → PowerSeries.coeff n e = 0) : PowerSeries.rescale (-1 : K) e = e := by
  ext n
  rw [PowerSeries.coeff_rescale]
  rcases Nat.even_or_odd n with hn | hn
  · rw [hn.neg_one_pow, one_mul]
  · rw [h n hn, mul_zero]

theorem endoCurve_neg_one {K : Type} [Field K] [CharZero K] (W : WeierstrassCurve K) :
    IsEndoCurve W (id : Empty → Empty) (fun _ => (0 : K)) (fun _ => (0 : K)) (-1) := by
  refine ⟨fun P => P.elim, fun P => P.elim, fun P => P.elim, ?_⟩
  rw [rescale_neg_one_of_even _ (Formalism.L2.Th1.A.wpShape.{0} K W).2.2.1]
  simp

theorem inv_mem_unitBall {K : Type} [NormedField K] [IsUltrametricDist K] {x : K} (h : ‖x‖ = 1) :
    x⁻¹ ∈ unitBall K := by
  have h1 : ‖x⁻¹‖ ≤ 1 := by rw [norm_inv, h, inv_one]
  first
    | exact h1
    | simpa [Formalism.G.unitBall] using h1

theorem endInt_int {K : Type} [Field K] (R : Subring K) (l linv : PowerSeries K)
    (hl : IsLogPair l linv) (hF : FGInt R l linv) (n : ℤ) : EndInt R l linv (n : K) := by
  obtain ⟨-, -, h0, h1, hm, hadd, -⟩ := ptClosure K R l linv hl hF
  induction n using Int.induction_on with
  | zero => simpa using h0
  | succ i ih =>
    have := hadd _ _ ih h1
    simpa using this
  | pred i ih =>
    have := hadd _ _ ih hm
    simpa [sub_eq_add_neg] using this

end WeierstrassCurveSeries

open WeierstrassCurveSeries

theorem curve_neg_norm_holds : CurveNegNorm := by
  intro K _ _ R W hW h2 s2
  obtain ⟨hlp, hwp, hA, -, -⟩ := curveFrame K R W hW
  have hPh : IsPh (wpReg W) s2 (logSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) :=
    (phOIsPh K (wpReg W) (logSer W) s2 hlp.1 hlp.2.1).2
  have hm : (-1 : K) ∈ R := R.neg_mem R.one_mem
  have hE := curveEndoR K R W hW Empty id (fun _ => (0 : K)) (fun _ => (0 : K)) (-1) (-1)
    (endoCurve_neg_one W) (fun P => P.elim) (fun P => P.elim) (by simp) hm
    (by rw [inv_neg, inv_one]; exact hm) (by simp)
  exact phNormFromDatum K R (wpReg W) s2 (logSer W) (expSer W) _ (xS W) (W.b₂ / 12) Empty id _ _ _
    (-1) (-1) hlp hPh hwp hA h2 hE (by simp)

theorem curve_formal_first_level_holds : WeierstrassBiadditiveModEquiv := by
  intro K _ _ _ W hc h2 s2
  have hW : Formalism.L2.Th1.A.IntModel W := hc
  obtain ⟨hlp, -, -, -, -⟩ := curveFrame K (unitBall K) W hc
  have hph0 : PowerSeries.constantCoeff (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) = 0 :=
    (phOIsPh K (wpReg W) (logSer W) s2 hlp.1 hlp.2.1).2.1
  obtain ⟨hlaw, hinv, -⟩ := Formalism.L2.Th1.A.bridgeLaw K W hW
  have hu := (Formalism.L2.Th1.B.f1O K (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W) s2 (W.b₂ / 12) (wpReg W)
    (logSer W) (Formalism.L2.Th1.A.iSer W) (xS W) (Formalism.L2.Th1.A.fgl W) (Formalism.L2.Th1.A.bridgeWp K W) hlaw
    hinv (Formalism.L2.Th1.A.bridgeCurve K W hW) h2).2.2.1
  exact (first_level_from_universal_law K (Formalism.L2.Th1.A.fgl W) (logSer W) (expSer W) _ hlp hlaw hph0 hu).2.2

theorem CurveRamified_of (hR : RamifiedShape) (hA : AdjUnitNorm) (_hI : InvEndInt)
    (hN : CurveNegNorm) (hF : WeierstrassBiadditiveModEquiv) : CurveRamified := by
  intro K _ _ _ W hc h2 s2 al albar d t ι _ neg xP yP hE hx hy hNal hal ht hd hd0 hb hs
  obtain ⟨hlp, hwp, hAx, hFG, -⟩ := curveFrame K (unitBall K) W hc
  have hPh : IsPh (wpReg W) s2 (logSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) :=
    (phOIsPh K (wpReg W) (logSer W) s2 hlp.1 hlp.2.1).2
  have hFr : Frame (unitBall K) (logSer W) (expSer W)
      (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) := ⟨hlp, hFG, hPh.1⟩
  have h2R : (2 : K)⁻¹ ∈ unitBall K := inv_mem_unitBall h2
  have hal0 : al ≠ 0 := by
    intro h
    rw [h, norm_zero] at hal
    exact zero_ne_one hal
  have halR : al ∈ unitBall K := hal.le
  have halI : al⁻¹ ∈ unitBall K := inv_mem_unitBall hal
  have hDat := curveEndoR K (unitBall K) W hc ι neg xP yP al albar hE hx hy hNal halR halI hb
  have hEal : EndInt (unitBall K) (logSer W) (expSer W) al :=
    endIntFromDatum K (unitBall K) (wpReg W) (logSer W) (expSer W) (xS W) (W.b₂ / 12) ι neg xP _ _
      al albar hlp hwp hAx h2R hDat
  have hEbar : EndInt (unitBall K) (logSer W) (expSer W) albar := by
    obtain ⟨-, -, -, -, hm, hadd, hmul⟩ := ptClosure K (unitBall K) (logSer W) (expSer W) hlp hFG
    have h := hadd _ _ (endInt_int (unitBall K) _ _ hlp hFG t) (hmul _ _ hm hEal)
    have he : (t : K) + -1 * al = albar := by rw [← ht]; ring
    rwa [he] at h
  have hNorm : PhNormAt (unitBall K) (logSer W) (expSer W)
      (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) al albar :=
    phNormFromDatum K (unitBall K) (wpReg W) s2 (logSer W) (expSer W) _ (xS W) (W.b₂ / 12) ι neg xP
      _ _ al albar hlp hPh hwp hAx h2R hDat hs
  have hF1 := hF K W hc h2 s2
  have hAdj : AdjAt (unitBall K) (logSer W) (expSer W)
      (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) al albar :=
    hA K (unitBall K) (logSer W) (expSer W) _ al albar ((Fintype.card ι : ℤ) + 1) hFr hF1 hal0 halI
      hEal hEbar (by rw [hNal]; push_cast; ring) hNorm
  exact hR K (logSer W) (expSer W) _ al albar d hFr hF1 (hN K (unitBall K) W hc h2R s2) h2 hAdj hd
    hd0

theorem CurveRamified_of_shape (hR : RamifiedShape) (hA : AdjUnitNorm) (hI : InvEndInt) :
    CurveRamified := CurveRamified_of hR hA hI curve_neg_norm_holds curve_formal_first_level_holds

end Formalism.L2.Th1.G
end
end

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.ThetaZeroJetsCurveHolds
noncomputable section
open scoped BigOperators
open Finset

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg xPlus)
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair)

namespace GramFrameCompositionTwoFacts

section Even

variable {K : Type} [Field K] [CharZero K]

end Even

section abelian₂

variable {K : Type} [Field K] [CharZero K]

end abelian₂

section Hom

variable {K : Type} [Field K]

theorem mvSubst_subst {σ τ : Type} {a : σ → MvPowerSeries τ K} (ha : MvPowerSeries.HasSubst a)
    {g : MvPowerSeries σ K} (hg : MvPowerSeries.constantCoeff g = 0) (f : PowerSeries K) :
    MvPowerSeries.subst a (PowerSeries.subst g f) = PowerSeries.subst (MvPowerSeries.subst a g) f := by
  rw [PowerSeries.subst_def, PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hg).const ha]

theorem cc_zPt {n : Type} {linv : PowerSeries K} (h0 : PowerSeries.constantCoeff linv = 0) (i : n) :
    MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries n K) linv : MvPowerSeries n K) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) linv h0

theorem hasSubst_zPt {n : Type} [Finite n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) :
    MvPowerSeries.HasSubst (fun i : n =>
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries n K) linv : MvPowerSeries n K)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => cc_zPt h0 i

def toZHom {n : Type} [Finite n] {linv : PowerSeries K} (h0 : PowerSeries.constantCoeff linv = 0) :
    MvPowerSeries n K →ₐ[K] MvPowerSeries n K :=
  MvPowerSeries.substAlgHom (hasSubst_zPt h0)

theorem toZHom_apply {n : Type} [Finite n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) (f : MvPowerSeries n K) :
    toZHom h0 f = toZ linv f :=
  MvPowerSeries.substAlgHom_apply _ f

theorem toZ_subst_X {n : Type} [Finite n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) (f : PowerSeries K) (i : n) :
    toZ linv (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries n K) f) =
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries n K) (PowerSeries.subst linv f) := by
  unfold toZ
  rw [mvSubst_subst (hasSubst_zPt h0) (MvPowerSeries.constantCoeff_X i),
    MvPowerSeries.subst_X (hasSubst_zPt h0),
    PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' h0)
      (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i))]

theorem toZ_phSum {n : Type} [Fintype n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) (c : n → K) (ph : PowerSeries K) :
    toZ linv (phSum c ph) = phSum c (PowerSeries.subst linv ph) := by
  unfold phSum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← toZHom_apply h0, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, toZHom_apply, toZ_subst_X h0]

theorem cc_phSum {n : Type} [Fintype n] (c : n → K) {ph : PowerSeries K}
    (h0 : PowerSeries.constantCoeff ph = 0) : MvPowerSeries.constantCoeff (phSum c ph) = 0 := by
  unfold phSum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [MvPowerSeries.smul_eq_C_mul, map_mul,
    PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) ph h0, mul_zero]

theorem jetsIn_phSum [CharZero K] {R : Subring K} {n : Type} [Fintype n]
    {c : n → K} (hc : ∀ i, c i ∈ R) {f : PowerSeries K} (hf : JetsIn1 R f) :
    JetsIn R (phSum c f) := by
  unfold phSum
  refine jetsIn_sum _ _ fun i _ => ?_
  rw [MvPowerSeries.smul_eq_C_mul]
  exact jetsIn_mul (jetsIn_C (hc i))
    (jetsIn_subst_one hf (MvPowerSeries.constantCoeff_X i) (jetsIn_X i))

theorem jetsIn_toZ [CharZero K] {R : Subring K} {l linv : PowerSeries K}
    (h : IsLogPair l linv) (hl : IsOneUnit R (PowerSeries.derivative (R := K) l)) {n : Type} [Fintype n]
    {G : MvPowerSeries n K} (hG : IntMv R G) : JetsIn R (toZ linv G) :=
  IntMvZ_of (JetsSubst_of jets_ring_holds jets_div_pow_holds) integral_jets_holds jets_subst_one_holds
    jets_ring_holds K R l linv h hl n G hG

theorem toZ_mvExp [CharZero K] {n : Type} [Finite n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) {f : MvPowerSeries n K}
    (hf : MvPowerSeries.constantCoeff f = 0) : toZ linv (mvExp f) = mvExp (toZ linv f) :=
  mvSubst_mvExp hf (hasSubst_zPt h0)

end Hom

end GramFrameCompositionTwoFacts

open GramFrameCompositionTwoFacts

theorem kernel_two_holds : KernelTwo := by
  intro K _ _ _ l linv ph h hl hph hj n _ c hc G hG
  have hv : PowerSeries.constantCoeff linv = 0 := h.2.2.1
  have j0 : JetsIn1 (unitBall K) (PowerSeries.subst linv ph) := by
    refine (jets_of_dist_jets_holds K (unitBall K) l linv ph h).1 fun i => ?_
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      have : jet l ph 0 = 0 := hph
      rw [this]
      exact (unitBall K).zero_mem
    · exact hj i hi
  have cz : PowerSeries.constantCoeff (PowerSeries.subst linv ph) = 0 := by
    rw [JetSubstitutionLemmas.cc_subst1 hv, hph]
  have c1 : MvPowerSeries.constantCoeff (-(phSum c ph)) = 0 := by
    rw [map_neg, cc_phSum c hph, neg_zero]
  have c3 : MvPowerSeries.constantCoeff (-(phSum c (PowerSeries.subst linv ph))) = 0 := by
    rw [map_neg, cc_phSum c cz, neg_zero]
  have e : toZ linv (-(phSum c ph)) = -(phSum c (PowerSeries.subst linv ph)) := by
    rw [← toZHom_apply hv, map_neg, toZHom_apply, toZ_phSum hv]
  have key : JetsIntegral (toZ linv (mvExp (-(phSum c ph)) * G)) := by
    rw [← toZHom_apply hv, map_mul, toZHom_apply, toZHom_apply, toZ_mvExp hv c1, e]
    exact jetsIn_mul (R := unitBall K) (jetsIn_mvExp c3 (jetsIn_neg (jetsIn_phSum hc j0)))
      (jetsIn_toZ h hl hG)
  exact ⟨key, fun P hP => Formalism.DworkPowerSeriesWeights.intOp K n _ key P hP⟩

end Formalism.L2.Th1.G
end
end
