module

public import Formalism.GaussJetBounds.OneLetterGauss
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.GaussJetBounds.GaussJetProofs.OrbMul
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.WModel
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.EGaussK
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.CoboundaryCommutesHomomorphism
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.FrobeniusExtensionOnInclusion

@[expose] public section

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ThetaIntegerIsSSubstitution
section -- merged from Formalism.ThetaLogCoordinates.UniformThetaSubstitution.ThetaLogIsSubst
section -- merged from Formalism.ThetaLogCoordinates.UniformThetaSubstitution.KernelFromKOneK
namespace Formalism.InvariantFactorPaths.G7.Top

open Formalism.InvariantFactorPaths.G7

theorem kernel_from_k_one_k : KernelBoundsGeneric := kernel_bounds_generic

end Formalism.InvariantFactorPaths.G7.Top
end

section -- merged from Formalism.ThetaLogCoordinates.UniformThetaSubstitution.EdgeNoTrunc
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

def ThetaLogIsSubst : Prop :=
  ∀ (K : Type) [Field K] (ν r0 r1 : ℕ) [NeZero ν] (om oms : Fin ν → ZMod (2 * ν) → K) (ϖ : K)
    (μ : PowerSeries K) (Tht : MvPowerSeries (Bool × EV ν r0 r1) K),
    PowerSeries.constantCoeff μ = 0 →
    thetaLog om oms ϖ μ Tht = MvPowerSeries.subst (fun x => MvPowerSeries.subst
        (fun y => MvPowerSeries.C ϖ⁻¹ * (MvPowerSeries.X y : MvPowerSeries (ZV ν r0 r1) K))
        (MvPowerSeries.C ϖ * sSub om oms μ x)) Tht

end Formalism.InvariantFactorPaths.G7
end
end

namespace Formalism.InvariantFactorPaths.G7.Top

open Formalism.InvariantFactorPaths.G7

theorem thetaLogIsSubst : ThetaLogIsSubst := by
  intro K _ ν r0 r1 _ om oms ϖ μ Tht hμ

  have hz0 : ∀ x : Bool × EV ν r0 r1, MvPowerSeries.constantCoeff (zLin om oms x) = 0 := by
    intro x
    unfold zLin
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    apply Finset.sum_eq_zero
    intro s _
    split_ifs <;> simp
  have hz : ∀ x : Bool × EV ν r0 r1, PowerSeries.HasSubst (zLin om oms x) := fun x =>
    PowerSeries.HasSubst.of_constantCoeff_zero (hz0 x)

  have hs : ∀ x : Bool × EV ν r0 r1, MvPowerSeries.constantCoeff (sSub om oms μ x) = 0 := by
    intro x
    unfold sSub
    rw [PowerSeries.constantCoeff_subst (hz x)]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    rcases d with _ | d
    · simp [hμ]
    · simp [map_pow, hz0 x]
  have ha : MvPowerSeries.HasSubst (fun x : Bool × EV ν r0 r1 => MvPowerSeries.C ϖ * sSub om oms μ x) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun x => by simp [hs x])
  have hb : MvPowerSeries.HasSubst (fun y : ZV ν r0 r1 =>
      MvPowerSeries.C ϖ⁻¹ * (MvPowerSeries.X y : MvPowerSeries (ZV ν r0 r1) K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun y => by simp)
  exact MvPowerSeries.subst_comp_subst_apply ha hb Tht

end Formalism.InvariantFactorPaths.G7.Top
end

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp torus BHyp Unram entLog oneLog thetaZ thetaOne frameJet frameJetOne
  nablaO)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 UnrOK IsLawOfLog BetaHyp OmOK lamF thetaLog sSub zLin)

namespace CohomologyFunctoriality₂

theorem norm_iter {K0 : Type} [NormedField K0] [IsUltrametricDist K0] [CharZero K0] {l : ℕ}
    {σ : K0 →+* K0} (hU : UnrOK K0 l σ) {c : K0} (hc : ‖c‖ ≤ 1) (n : ℕ) : ‖σ^[n] c‖ ≤ 1 := by
  induction n with
  | zero => simpa using hc
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (frobSq K0 l σ hU).2 _ ih

theorem frob_step {K0 K : Type} [NormedField K0] [IsUltrametricDist K0] [CharZero K0]
    [NormedField K] {l d : ℕ} [NeZero d] {σ : K0 →+* K0} (j : K0 →+* K) (hU : UnrOK K0 l σ)
    (hj : ∀ a, ‖j a‖ = ‖a‖) {c : K0} (hc : ‖c‖ ≤ 1) (hfix : σ^[d] c = c) (s : ZMod d) :
    ‖j (σ^[(s + 1).val] c) - j (σ^[s.val] c) ^ l‖ ≤ (l : ℝ)⁻¹ := by
  have h := TranslateJetMomentLawAnyIdempotentLevel.iter_sub_one σ hfix (s + 1)
  rw [add_sub_cancel_right] at h
  rw [← h, ← map_pow, ← map_sub, hj]
  exact hU.2.2.2.2 _ (norm_iter hU hc _)

end CohomologyFunctoriality₂

theorem omega_integral_criterion : OmOKOf := by
  intro K0 K _ _ _ _ l ν _ σ j hU hj om oms hO hT
  refine ⟨fun r s => ?_, fun r s => ?_, fun a b hab => ?_⟩
  · unfold conjJ
    rw [hj, hj]
    exact ⟨CohomologyFunctoriality₂.norm_iter hU (hO.1 r).1 _, CohomologyFunctoriality₂.norm_iter hU (hO.1 r).2 _⟩
  · unfold conjJ
    exact ⟨CohomologyFunctoriality₂.frob_step j hU hj (hO.1 r).1 (hO.2 r).1 s,
      CohomologyFunctoriality₂.frob_step j hU hj (hO.1 r).2 (hO.2 r).2 s⟩
  · unfold conjJ
    have hE : Even (2 * ν) := even_two_mul ν
    have key : ∑ r, σ^[a.val] (oms r) * σ^[b.val] (om r) = if a = b then 1 else 0 := by
      by_cases ha : a.val % 2 = 0
      · have hb : b.val % 2 = 0 := by omega
        have h := TranslateJetMomentLawAnyIdempotentLevel.dual2 hE σ hO.2 hT b a
        rw [Fintype.sum_prod_type, Fintype.sum_bool] at h
        simp only [mXY, TranslateJetMomentLawAnyIdempotentLevel.pXY, ha, hb, if_true] at h
        simp only [Bool.true_eq_false, if_false, mul_zero, Finset.sum_const_zero, zero_add] at h
        have e : (if a = b then (1 : K0) else 0) = if b = a then 1 else 0 := by
          by_cases hab' : a = b
          · rw [if_pos hab', if_pos hab'.symm]
          · rw [if_neg hab', if_neg (fun h => hab' h.symm)]
        rw [e, ← h]
        exact Finset.sum_congr rfl fun r _ => mul_comm _ _
      · have hb : ¬ b.val % 2 = 0 := by omega
        have h := TranslateJetMomentLawAnyIdempotentLevel.dual2 hE σ hO.2 hT a b
        rw [Fintype.sum_prod_type, Fintype.sum_bool] at h
        simp only [mXY, TranslateJetMomentLawAnyIdempotentLevel.pXY, ha, hb, if_false] at h
        simp only [Bool.false_eq_true, if_false, mul_zero, Finset.sum_const_zero, add_zero,
          if_true] at h
        exact h
    have h2 := congrArg j key
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h2
    simp only [map_mul] at h2
    rw [h2]
    split_ifs <;> simp

theorem theta_integer_is_s_substitution : ThetaInZIsSSub := by
  intro K0 K _ _ l ν r0 r1 _ σ j om oms Tht
  unfold thetaInZ
  congr 1
  funext x
  unfold xOfZ Formalism.InvariantFactorPaths.G7.sSub Formalism.InvariantFactorPaths.G7.zLin conjJ
  congr 1
  by_cases h : x.1 = false
  · simp only [h, if_true]
  · simp only [h]
    refine Finset.sum_congr rfl fun s _ => ?_
    rcases Nat.mod_two_eq_zero_or_one s.val with h2 | h2 <;> simp [h2]

namespace CohomologyFunctoriality₂

open Formalism.InvariantFactorPaths.G7 Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution

theorem log_scale {K : Type} [Field K] (p : ℕ) (ϖ : K) (μ : PowerSeries K)
    (h0 : PowerSeries.constantCoeff μ = 0)
    (h1 : (PowerSeries.subst μ (lamF p ϖ) : PowerSeries K) = PowerSeries.X) :
    (PowerSeries.subst (PowerSeries.C ϖ * μ) (lgF K p) : PowerSeries K) =
      PowerSeries.C ϖ * PowerSeries.X := by
  have e1 := LogarithmEquivalence.subst_lgF_scale p ϖ
  have hμ : PowerSeries.HasSubst μ := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hX : PowerSeries.HasSubst (PowerSeries.C ϖ * PowerSeries.X : PowerSeries K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  have e2 := congrArg (fun f => (PowerSeries.subst μ f : PowerSeries K)) e1
  rw [PowerSeries.subst_comp_subst_apply hX hμ] at e2
  rw [← PowerSeries.coe_substAlgHom hμ, map_mul, map_mul, PowerSeries.coe_substAlgHom hμ, h1,
    PowerSeries.subst_X hμ] at e2
  have e3 : (PowerSeries.substAlgHom hμ) (PowerSeries.C ϖ : PowerSeries K) = PowerSeries.C ϖ := by
    have : (PowerSeries.C ϖ : PowerSeries K) = algebraMap K _ ϖ := rfl
    rw [this, AlgHom.commutes]
  rw [PowerSeries.coe_substAlgHom hμ] at e3
  rw [e3] at e2
  exact e2

theorem log_coord {K : Type} [Field K] (p ν r0 r1 : ℕ) [NeZero ν]
    (om oms : Fin ν → ZMod (2 * ν) → K) (ϖ : K) (μ : PowerSeries K) (x : Bool × EV ν r0 r1)
    (hϖ : ϖ ≠ 0) (hμ0 : PowerSeries.constantCoeff μ = 0)
    (hμ : (PowerSeries.subst μ (lamF p ϖ) : PowerSeries K) = PowerSeries.X) :
    PowerSeries.subst (MvPowerSeries.subst
        (fun y => MvPowerSeries.C ϖ⁻¹ * (MvPowerSeries.X y : MvPowerSeries (ZV ν r0 r1) K))
        (MvPowerSeries.C ϖ * sSub om oms μ x)) (lgF K p) = zLin om oms x := by
  have hb := hasSubst_scale (K := K) (ι := ZV ν r0 r1) ϖ⁻¹
  have hz : PowerSeries.HasSubst (zLin om oms x : MvPowerSeries (ZV ν r0 r1) K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_zLin om oms x)
  have hw : PowerSeries.HasSubst
      (MvPowerSeries.C ϖ⁻¹ * zLin om oms x : MvPowerSeries (ZV ν r0 r1) K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by rw [map_mul, constantCoeff_zLin, mul_zero])
  have hm : PowerSeries.HasSubst (PowerSeries.C ϖ * μ : PowerSeries K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by rw [map_mul, hμ0, mul_zero])
  have e1 : MvPowerSeries.subst
      (fun y => MvPowerSeries.C ϖ⁻¹ * (MvPowerSeries.X y : MvPowerSeries (ZV ν r0 r1) K))
      (MvPowerSeries.C ϖ * sSub om oms μ x) =
      PowerSeries.subst (MvPowerSeries.C ϖ⁻¹ * zLin om oms x) (PowerSeries.C ϖ * μ) := by
    rw [subst_C_mul hb, ps_subst_C_mul hw]
    unfold sSub
    rw [FormalGroupLaws.subst_subst hb hz, subst_scale_zLin]
  have e2 := congrArg (fun f => (PowerSeries.subst (MvPowerSeries.C ϖ⁻¹ * zLin om oms x) f :
    MvPowerSeries (ZV ν r0 r1) K)) (log_scale p ϖ μ hμ0 hμ)
  rw [PowerSeries.subst_comp_subst_apply hm hw, ps_subst_C_mul hw ϖ PowerSeries.X,
    PowerSeries.subst_X hw,
    ← mul_assoc, ← map_mul, mul_inv_cancel₀ hϖ, map_one, one_mul] at e2
  rw [e1]
  exact e2

end CohomologyFunctoriality₂

theorem theta_integer_is_theta_log : ThetaInZIsThetaLog := by
  intro K0 K _ _ l ν r0 r1 _ σ j om oms ϖ μ hl hϖ hμ0 hμ Tht
  rw [theta_integer_is_s_substitution, Formalism.InvariantFactorPaths.G7.Top.thetaLogIsSubst K ν r0 r1 _ _ ϖ μ Tht hμ0]
  congr 1
  funext x
  have hb := Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution.hasSubst_scale (K := K) (ι := Formalism.InvariantFactorPaths.G7.ZV ν r0 r1) ϖ⁻¹
  have hcc : MvPowerSeries.constantCoeff (MvPowerSeries.subst
      (fun y => MvPowerSeries.C ϖ⁻¹ *
        (MvPowerSeries.X y : MvPowerSeries (Formalism.InvariantFactorPaths.G7.ZV ν r0 r1) K))
      (MvPowerSeries.C ϖ * sSub (conjJ j σ om) (conjJ j σ oms) μ x)) = 0 := by
    refine MvPowerSeries.constantCoeff_subst_eq_zero hb (fun i => by simp) ?_
    have h : MvPowerSeries.constantCoeff (sSub (conjJ j σ om) (conjJ j σ oms) μ x) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero
        (Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution.constantCoeff_zLin _ _ x) μ hμ0
    rw [map_mul, h, mul_zero]
  have h := Pair.exp_log expSpec hl hcc
  rw [CohomologyFunctoriality₂.log_coord l ν r0 r1 _ _ ϖ μ x hϖ hμ0 hμ] at h
  exact h

namespace CohomologyFunctoriality₂

end CohomologyFunctoriality₂

theorem kernel_of_f : KernelOfF := by
  intro p _ K0 _ _ _ _ σ hU hζ F hF be hF1 hF2 K _ _ _ j ν r0 r1 _ hj hϖ om oms hO hT U0 Φ hU0 hΦ0
    hΦ TT colN hts hp I n
  obtain ⟨ϖ, hϖ⟩ := hϖ
  have hnp : ‖(p : K)‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast j, hj]
    exact hU.2.2.1
  have hpK : (p : K) ≠ 0 := by exact_mod_cast hU.1.ne_zero
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    apply hpK
    rw [← hϖ, zero_pow]
    have : 2 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hU.2.1.le 2
    omega
  obtain ⟨-, -, μ, hμ0, -, hμ, -, -⟩ := Formalism.InvariantFactorPaths.G7.Top.logRescale K p ϖ hU.1 hnp hϖ
  rw [theta_integer_is_theta_log K0 K p ν r0 r1 σ j om oms ϖ μ hU.1.two_le hϖ0 hμ0 hμ]
  exact Formalism.InvariantFactorPaths.G7.Top.kernel_from_k_one_k p K0 σ hU hζ F hF be (betaHypOfF K0 p σ hU F be hF1 hF2) K j
    ν r0 r1 hj _ _ ϖ μ U0 Φ hϖ (omega_integral_criterion K0 K p ν σ j hU hj om oms hO hT) hμ0 hμ hU0 hΦ0 hΦ
    TT colN hts hp I n

end Formalism.L2.Th1.D
end
end

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.TraceDualExists
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.InvariantFactorPaths.G7 (UnrOK)

namespace TraceDualSums

lemma sum_zmod {M : Type} [AddCommMonoid M] (d : ℕ) [NeZero d] (F : ℕ → M) :
    (∑ s : ZMod d, F s.val) = ∑ i ∈ Finset.range d, F i := by
  cases d with
  | zero => exact absurd rfl (NeZero.ne 0)
  | succ n =>
    rw [Finset.sum_range]
    rfl

lemma sum_range_even {M : Type} [AddCommMonoid M] (m : ℕ) (g : ℕ → M) :
    (∑ i ∈ Finset.range (2 * m), if i % 2 = 0 then g i else 0) =
      ∑ k ∈ Finset.range m, g (2 * k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    have h1 : (2 * m) % 2 = 0 := by omega
    have h2 : ¬ (2 * m + 1) % 2 = 0 := by omega
    rw [if_pos h1, if_neg h2, add_zero]

lemma norm_det_le {K : Type} [NormedField K] [IsUltrametricDist K] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) (h : ∀ i j, ‖M i j‖ ≤ 1) : ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro p _
  rw [Units.smul_def, zsmul_eq_mul, norm_mul, norm_prod]
  exact mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one K _)
    (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => h _ _)

lemma inv_shift {K : Type} [Field K] {m : ℕ} [NeZero m] (τ : K →+* K)
    (V P : Matrix (Fin m) (Fin m) K) (hVP : V * P = 1)
    (hV : ∀ k r, τ (V k r) = V (k + 1) r) : ∀ r k, τ (P r k) = P r (k + 1) := by
  have h1 : (V.map τ) * (P.map τ) = 1 := by
    rw [← Matrix.map_mul, hVP]
    exact Matrix.map_one τ (map_zero τ) (map_one τ)
  have h2 : V.map τ = V.submatrix (Equiv.addRight (1 : Fin m)) id := by
    ext k r
    exact hV k r
  have h3 : (V.submatrix (Equiv.addRight (1 : Fin m)) id) *
      (P.submatrix id (Equiv.addRight (1 : Fin m))) = 1 := by
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hVP, Matrix.submatrix_one_equiv]
  have h4 : P.map τ = P.submatrix id (Equiv.addRight (1 : Fin m)) := by
    rw [← Matrix.inv_eq_right_inv h1, h2, Matrix.inv_eq_right_inv h3]
  intro r k
  exact congrFun (congrFun h4 r) k

end TraceDualSums

open TraceDualSums Fin.NatCast in
theorem trace_dual_exists : TrDualExists := by
  intro K _ _ _ l d _ σ hU hd ζ hζ
  obtain ⟨m, rfl⟩ := hd
  have hd0 : m + m ≠ 0 := NeZero.ne (m + m)
  have hm0 : m ≠ 0 := by omega
  have hdm : (m + m) / 2 = m := by omega
  rw [hdm]
  have : NeZero m := ⟨hm0⟩
  have hp : l.Prime := hU.1
  have hl3 : 2 < l := hU.2.1
  have hlt : ‖(l : K)‖ < 1 := by
    rw [hU.2.2.1]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hpos : 1 ≤ l ^ (m + m) := Nat.one_le_pow _ _ hp.pos
  have hnd : ¬ l ∣ l ^ (m + m) - 1 := by
    intro h
    have h1 : l ∣ l ^ (m + m) := dvd_pow_self l hd0
    have h2 : l ∣ 1 := by
      have := (Nat.dvd_sub h1 h)
      rwa [Nat.sub_sub_self hpos] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  have hN : ‖((l ^ (m + m) - 1 : ℕ) : K)‖ = 1 :=
    Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd hp hlt hnd
  have hN0 : l ^ (m + m) - 1 ≠ 0 := by
    intro h
    rw [h] at hnd
    exact hnd (dvd_zero l)
  have nζ : ‖ζ‖ = 1 := FormalExponential.norm_eq_one_of_pow hN0 hζ.pow_eq_one
  have hσζ : σ ζ = ζ ^ l := teichSigma K l (m + m) σ hU (by omega) ζ hζ.pow_eq_one
  have hit : ∀ j, σ^[j] ζ = ζ ^ (l ^ j) := B4.iterate_of_pow hσζ
  have hper : σ^[m + m] ζ = ζ := by
    rw [hit, show l ^ (m + m) = (l ^ (m + m) - 1) + 1 by omega, pow_succ, hζ.pow_eq_one, one_mul]
  let τ : K →+* K := σ.comp σ
  have hτ : ∀ (k : ℕ) (a : K), τ^[k] a = σ^[2 * k] a := by
    intro k a
    rw [Function.iterate_mul]
    rfl
  have hper' : Function.IsPeriodicPt τ m ζ := by
    show τ^[m] ζ = ζ
    rw [hτ, two_mul]
    exact hper
  let x : Fin m → K := fun k => σ^[2 * k.val] ζ
  have hxn : ∀ j : ℕ, x (j : Fin m) = τ^[j] ζ := by
    intro j
    show σ^[2 * ((j : Fin m) : ℕ)] ζ = _
    rw [Fin.val_natCast, ← hτ, hper'.iterate_mod_apply]
  have hxs : ∀ k, τ (x k) = x (k + 1) := by
    intro k
    have h : k + 1 = ((k.val + 1 : ℕ) : Fin m) := by
      rw [Nat.cast_succ, Fin.cast_val_eq_self]
    rw [h, hxn, Function.iterate_succ_apply', ← hxn, Fin.cast_val_eq_self]
  let V : Matrix (Fin m) (Fin m) K := Matrix.vandermonde x
  have hVa : ∀ k r, V k r = x k ^ (r : ℕ) := fun k r => Matrix.vandermonde_apply x k r
  have hVs : ∀ k r, τ (V k r) = V (k + 1) r := by
    intro k r
    rw [hVa, hVa, map_pow, hxs]
  have hxpow : ∀ k, x k = ζ ^ (l ^ (2 * k.val)) := fun k => hit _
  have hxN : ∀ k, x k ^ (l ^ (m + m) - 1) = 1 := by
    intro k
    rw [hxpow, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have nx : ∀ k, ‖x k‖ = 1 := fun k => FormalExponential.norm_eq_one_of_pow hN0 (hxN k)
  have hsmall : ∀ k : Fin m, l ^ (2 * k.val) < l ^ (m + m) - 1 := by
    intro k
    have hk := k.2
    have h1 : l ^ (2 * k.val) ≤ l ^ (m + m - 1) := Nat.pow_le_pow_right hp.pos (by omega)
    have h2 : l ^ (m + m) = l ^ (m + m - 1) * l := by
      rw [← pow_succ]
      congr 1
      omega
    have h3 : 1 ≤ l ^ (m + m - 1) := Nat.one_le_pow _ _ hp.pos
    have h4 : l ^ (m + m - 1) * 3 ≤ l ^ (m + m - 1) * l := Nat.mul_le_mul_left _ hl3
    omega
  have hinj : Function.Injective x := by
    intro i j hij
    rw [hxpow, hxpow] at hij
    have h1 := hζ.pow_inj (hsmall i) (hsmall j) hij
    have h2 := Nat.pow_right_injective hp.two_le h1
    exact Fin.ext (by omega)
  have hdiff : ∀ i j, i ≠ j → ‖x j - x i‖ = 1 := by
    intro i j hij
    refine le_antisymm ?_ ?_
    · rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
      rw [norm_neg, nx, nx, max_self]
    · by_contra hlt'
      exact hij (hinj (FormalExponential.root_eq_of_norm_lt hN (hxN j) (hxN i) (not_le.1 hlt'))).symm
  have hdet : ‖V.det‖ = 1 := by
    rw [Matrix.det_vandermonde, norm_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [norm_prod]
    exact Finset.prod_eq_one fun j hj => hdiff i j (ne_of_lt (Finset.mem_Ioi.1 hj))
  have hdet0 : V.det ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdet
    exact zero_ne_one hdet
  let P : Matrix (Fin m) (Fin m) K := V⁻¹
  have hVP : V * P = 1 := Matrix.mul_nonsing_inv V (isUnit_iff_ne_zero.2 hdet0)
  have hPV : P * V = 1 := Matrix.nonsing_inv_mul V (isUnit_iff_ne_zero.2 hdet0)
  have hVint : ∀ k r, ‖V k r‖ ≤ 1 := by
    intro k r
    rw [hVa, norm_pow, nx, one_pow]
  have hPint : ∀ r k, ‖P r k‖ ≤ 1 := by
    intro r k
    show ‖(V⁻¹) r k‖ ≤ 1
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', norm_mul, norm_inv,
      hdet, inv_one, one_mul, Matrix.adjugate_apply]
    refine norm_det_le _ fun i j => ?_
    rw [Matrix.updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]
      split_ifs <;> simp
    · exact hVint i j
  have hPs := inv_shift τ V P hVP hVs
  have hPn : ∀ (r : Fin m) (j : ℕ), τ^[j] (P r 0) = P r (j : Fin m) := by
    intro r j
    induction j with
    | zero => simp
    | succ j ih => rw [Function.iterate_succ_apply', ih, hPs, Nat.cast_succ]
  refine ⟨fun r => ζ ^ (r : ℕ), fun r => P r 0,
    ⟨fun r => ⟨by rw [norm_pow, nζ, one_pow], hPint r 0⟩, fun r => ⟨?_, ?_⟩⟩, ⟨?_, ?_⟩⟩
  · show σ^[m + m] (ζ ^ (r : ℕ)) = ζ ^ (r : ℕ)
    rw [iterate_map_pow, hper]
  · show σ^[m + m] (P r 0) = P r 0
    rw [← two_mul, ← hτ, hPn, Fin.natCast_self]
  · rw [Fintype.card_fin, two_mul]
  · intro r r'
    show (∑ s : ZMod (m + m), if s.val % 2 = 0 then σ^[s.val] (ζ ^ (r : ℕ) * P r' 0) else 0) = _
    rw [sum_zmod (m + m) (fun i => if i % 2 = 0 then σ^[i] (ζ ^ (r : ℕ) * P r' 0) else 0),
      ← two_mul, sum_range_even m (fun i => σ^[i] (ζ ^ (r : ℕ) * P r' 0)), Finset.sum_range]
    have hterm : ∀ k : Fin m, σ^[2 * (k : ℕ)] (ζ ^ (r : ℕ) * P r' 0) = P r' k * V k r := by
      intro k
      rw [iterate_map_mul, iterate_map_pow, ← hτ k.val (P r' 0), hPn, Fin.cast_val_eq_self, hVa,
        mul_comm]
    rw [Finset.sum_congr rfl fun k _ => hterm k, ← Matrix.mul_apply, hPV, Matrix.one_apply]
    simp only [eq_comm]

end Formalism.L2.Th1.D
end
end

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.FrobeniusOnRingA
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

variable (l : ℕ) [Fact l.Prime]

def muSub : Submonoid ℂ_[l] where
  carrier := muPrime l
  one_mem' := ⟨1, one_pos, fun h => (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.mp h), by simp⟩
  mul_mem' := by
    rintro a b ⟨n, hn, hln, ha⟩ ⟨m, hm, hlm, hb⟩
    refine ⟨n * m, Nat.mul_pos hn hm, fun h => ?_, ?_⟩
    · rcases (Fact.out : l.Prime).dvd_mul.mp h with h | h
      exacts [hln h, hlm h]
    · rw [mul_pow, pow_mul, ha, one_pow, mul_comm n m, pow_mul, hb, one_pow, one_mul]

def evK (k : ℕ) : MonoidAlgebra ℤ (muSub l) →ₐ[ℤ] ℂ_[l] :=
  MonoidAlgebra.lift ℤ ℂ_[l] (muSub l) ((muSub l).subtype.comp (powMonoidHom k))

lemma evK_of (k : ℕ) (g : muSub l) :
    evK l k (MonoidAlgebra.of ℤ (muSub l) g) = (g : ℂ_[l]) ^ k := by
  simp [evK]

lemma evK_mem (k : ℕ) (r : MonoidAlgebra ℤ (muSub l)) : evK l k r ∈ ringA l := by
  induction r using MonoidAlgebra.induction_on with
  | of g =>
    rw [evK_of]
    exact Subring.pow_mem _ (Subring.subset_closure g.2) k
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact Subring.add_mem _ hx hy
  | smul a x hx =>
    rw [zsmul_eq_mul, map_mul, map_intCast]
    exact Subring.mul_mem _ (intCast_mem _ a) hx

lemma eval_pow_coprime {K : Type*} [Field K] [CharZero K] {n k : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hn : 0 < n) (hcop : Nat.Coprime k n) (P : Polynomial ℤ)
    (h : P.eval₂ (Int.castRingHom K) ζ = 0) : P.eval₂ (Int.castRingHom K) (ζ ^ k) = 0 := by
  have h1 : Polynomial.aeval ζ P = 0 := by
    rw [Polynomial.aeval_def]
    exact h
  have hd : minpoly ℤ ζ ∣ P := minpoly.isIntegrallyClosed_dvd (hζ.isIntegral hn) h1
  rw [hζ.minpoly_eq_pow_coprime hcop] at hd
  obtain ⟨Q, rfl⟩ := hd
  have h2 : Polynomial.aeval (ζ ^ k) (minpoly ℤ (ζ ^ k)) = 0 := minpoly.aeval _ _
  rw [Polynomial.aeval_def] at h2
  rw [Polynomial.eval₂_mul]
  exact mul_eq_zero_of_left h2 _

lemma exists_poly (r : MonoidAlgebra ℤ (muSub l)) :
    ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ∀ m : ℕ, n ∣ m → 0 < m → ∀ ζ : ℂ_[l], IsPrimitiveRoot ζ m →
      ∃ P : Polynomial ℤ, ∀ k : ℕ, P.eval₂ (Int.castRingHom ℂ_[l]) (ζ ^ k) = evK l k r := by
  induction r using MonoidAlgebra.induction_on with
  | of g =>
    obtain ⟨n, hn, hln, hg⟩ := g.2
    refine ⟨n, hn, hln, fun m hnm hm ζ hζ => ?_⟩
    have hgm : (g : ℂ_[l]) ^ m = 1 := by
      obtain ⟨c, rfl⟩ := hnm
      rw [pow_mul, hg, one_pow]
    have : NeZero m := ⟨hm.ne'⟩
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hgm
    refine ⟨Polynomial.X ^ i, fun k => ?_⟩
    rw [evK_of, ← hi, Polynomial.eval₂_pow, Polynomial.eval₂_X, ← pow_mul, ← pow_mul, mul_comm]
  | add x y hx hy =>
    obtain ⟨n, hn, hln, hP⟩ := hx
    obtain ⟨n', hn', hln', hP'⟩ := hy
    refine ⟨n * n', Nat.mul_pos hn hn', fun h => ?_, fun m hnm hm ζ hζ => ?_⟩
    · rcases (Fact.out : l.Prime).dvd_mul.mp h with h | h
      exacts [hln h, hln' h]
    · obtain ⟨P, hP⟩ := hP m (dvd_trans (dvd_mul_right _ _) hnm) hm ζ hζ
      obtain ⟨P', hP'⟩ := hP' m (dvd_trans (dvd_mul_left _ _) hnm) hm ζ hζ
      exact ⟨P + P', fun k => by rw [Polynomial.eval₂_add, map_add (f := _), hP, hP']⟩
  | smul a x hx =>
    obtain ⟨n, hn, hln, hP⟩ := hx
    refine ⟨n, hn, hln, fun m hnm hm ζ hζ => ?_⟩
    obtain ⟨P, hP⟩ := hP m hnm hm ζ hζ
    exact ⟨Polynomial.C a * P, fun k => by
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, hP, zsmul_eq_mul, map_mul, map_intCast, eq_intCast]⟩

lemma evK_ker (r : MonoidAlgebra ℤ (muSub l)) (h : evK l 1 r = 0) : evK l l r = 0 := by
  obtain ⟨n, hn, hln, hP⟩ := exists_poly l r
  have : NeZero n := ⟨hn.ne'⟩
  have : NeZero (n : ℂ_[l]) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[l] n
  obtain ⟨P, hP⟩ := hP n dvd_rfl hn ζ hζ
  have h1 : P.eval₂ (Int.castRingHom ℂ_[l]) ζ = 0 := by
    have := hP 1
    rw [pow_one] at this
    rw [this, h]
  have hcop : Nat.Coprime l n := ((Fact.out : l.Prime).coprime_iff_not_dvd).mpr hln
  rw [← hP l]
  exact eval_pow_coprime hζ hn hcop P h1

def evA (k : ℕ) : MonoidAlgebra ℤ (muSub l) →+* ringA l :=
  (evK l k).toRingHom.codRestrict (ringA l) (evK_mem l k)

lemma evA_coe (k : ℕ) (r : MonoidAlgebra ℤ (muSub l)) : ((evA l k r : ringA l) : ℂ_[l]) = evK l k r := rfl

lemma evA_of (k : ℕ) (g : muSub l) :
    evA l k (MonoidAlgebra.of ℤ (muSub l) g) = (⟨g, Subring.subset_closure g.2⟩ : ringA l) ^ k := by
  apply Subtype.ext
  rw [evA_coe, evK_of]
  rfl

lemma evA_surj : Function.Surjective (evA l 1) := by
  have hle : ringA l ≤ (evK l 1).toRingHom.range := by
    refine Subring.closure_le.mpr fun g hg => ?_
    refine ⟨MonoidAlgebra.of ℤ (muSub l) ⟨g, hg⟩, ?_⟩
    change evK l 1 _ = g
    rw [evK_of, pow_one]
  rintro ⟨x, hx⟩
  obtain ⟨r, hr⟩ := hle hx
  exact ⟨r, Subtype.ext hr⟩

lemma evA_ker : RingHom.ker (evA l 1) ≤ RingHom.ker (evA l l) := by
  intro r hr
  rw [RingHom.mem_ker] at hr ⊢
  apply Subtype.ext
  rw [evA_coe]
  exact evK_ker l r (by rw [← evA_coe, hr]; rfl)

lemma int_fermat (a : ℤ) : ∃ c : ℤ, a - a ^ l = (l : ℤ) * c := by
  have : ((a - a ^ l : ℤ) : ZMod l) = 0 := by
    push_cast
    rw [ZMod.pow_card, sub_self]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this

lemma evA_congr (r : MonoidAlgebra ℤ (muSub l)) :
    ∃ y : ringA l, evA l l r - evA l 1 r ^ l = (l : ringA l) * y := by
  induction r using MonoidAlgebra.induction_on with
  | of g =>
    refine ⟨0, ?_⟩
    rw [evA_of, evA_of, pow_one, sub_self, mul_zero]
  | add x y hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    obtain ⟨w, hw⟩ := exists_add_pow_prime_eq (Fact.out : l.Prime) (evA l 1 x) (evA l 1 y)
    refine ⟨u + v - evA l 1 x * evA l 1 y * w, ?_⟩
    rw [map_add (f := _), map_add (f := _), hw]
    linear_combination hu + hv
  | smul a x hx =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨c, hc⟩ := int_fermat l a
    have hc' : (a : ringA l) - (a : ringA l) ^ l = (l : ringA l) * (c : ringA l) := by
      exact_mod_cast congrArg (Int.cast : ℤ → ringA l) hc
    refine ⟨(a : ringA l) * u + (c : ringA l) * evA l 1 x ^ l, ?_⟩
    rw [zsmul_eq_mul, map_mul, map_mul, map_intCast, map_intCast, mul_pow]
    linear_combination (a : ringA l) * hu + (evA l 1 x ^ l) * hc'

theorem frobenius_on_ring_a : FrobA := by
  intro l _
  refine ⟨(evA l 1).liftOfSurjective (evA_surj l) ⟨evA l l, evA_ker l⟩, fun ζ hζ => ?_, fun x => ?_⟩
  · have h1 : evA l 1 (MonoidAlgebra.of ℤ (muSub l) ⟨ζ, hζ⟩) = ζ := by
      rw [evA_of, pow_one]
    conv_lhs => rw [← h1]
    rw [RingHom.liftOfSurjective_comp_apply]
    change evA l l _ = _
    rw [evA_of]
  · obtain ⟨r, rfl⟩ := evA_surj l x
    rw [RingHom.liftOfSurjective_comp_apply]
    exact evA_congr l r

end Formalism.L2.Th1.D
end
end

namespace Formalism.L2.Th1.D

theorem kernelOfF : KernelOfF := kernel_of_f
theorem sigmaIsom : SigmaIsom := sigma_isometry
theorem fixedIsLimit : FixedIsLimit := fixed_is_limit
theorem transport_first_level : CoboundaryCocycleTransportAlongHom := transport_first_level_holds
theorem transportNorm : TransportNorm := transport_norm_relation
theorem trDualExists : TrDualExists := trace_dual_exists
theorem frobA : FrobA := frobenius_on_ring_a

end Formalism.L2.Th1.D
