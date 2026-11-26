module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalD
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementE
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveJetsUnitBall

@[expose] public section

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.LinearCoeffLogShiftedWeierstrass
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B.Iso

open PowerSeries
open Formalism.L2.Th1.C (wpShift HasSecondLogDeriv)

variable {K : Type} [Field K] [CharZero K]

theorem dz_rescale (a : K) (f : PowerSeries K) :
    dz (rescale a f) = C a * rescale a (dz f) := by
  ext n
  rw [dz, coeff_derivative, coeff_rescale, coeff_C_mul, coeff_rescale, coeff_derivative]
  ring

theorem second_derivative_rescale (a : K) (f : PowerSeries K) :
    dz (dz (rescale a f)) = C (a ^ 2) * rescale a (dz (dz f)) := by
  rw [dz_rescale, dz_mul, dz_C, dz_rescale, map_pow]
  ring

theorem rescale_C' (a c : K) : rescale a (C c : PowerSeries K) = C c := by
  ext n
  rw [coeff_rescale, coeff_C]
  split_ifs with h
  · rw [h, pow_zero, one_mul]
  · rw [mul_zero]

theorem dz_nsmul (n : ℕ) (f : PowerSeries K) : dz (n • f) = n • dz f := map_nsmul _ n f

theorem second_derivative_nsmul (n : ℕ) (f : PowerSeries K) : dz (dz (n • f)) = n • dz (dz f) := by
  rw [dz_nsmul, dz_nsmul]

theorem fExp_zero : fExp (0 : PowerSeries K) = 1 := by
  have h : fExp (0 : PowerSeries K) * fExp (0 : PowerSeries K) = fExp (0 : PowerSeries K) := by
    rw [← fExp_add (map_zero _) (map_zero _), add_zero]
  have h1 : constantCoeff (fExp (0 : PowerSeries K)) = 1 := constantCoeff_fExp (map_zero _)
  have hne : fExp (0 : PowerSeries K) ≠ 0 := ne_zero_of_constantCoeff (by rw [h1]; exact one_ne_zero)
  exact mul_left_cancel₀ hne (by rw [h, mul_one])

theorem fExp_nsmul {f : PowerSeries K} (hf : constantCoeff f = 0) (n : ℕ) :
    fExp (n • f) = fExp f ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, fExp_zero]
  | succ m ih =>
    have hm : constantCoeff (m • f) = 0 := by rw [map_nsmul, hf, smul_zero]
    rw [succ_nsmul, fExp_add hm hf, ih, pow_succ]

theorem fExp_sum {ι : Type} (s : Finset ι) (f : ι → PowerSeries K)
    (hf : ∀ i, constantCoeff (f i) = 0) : fExp (∑ i ∈ s, f i) = ∏ i ∈ s, fExp (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, fExp_zero]
  | insert a s ha ih =>
    have hs : constantCoeff (∑ i ∈ s, f i) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]; exact Finset.sum_eq_zero fun i _ => hf i
    rw [Finset.sum_insert ha, Finset.prod_insert ha, fExp_add (hf a) hs, ih]

theorem second_derivative_formal_log {f g : PowerSeries K} (hf : constantCoeff f = 1) (h : HasSecondLogDeriv f g) :
    dz (dz (fLog f)) = g := by
  have hne : f ≠ 0 := ne_zero_of_constantCoeff (by rw [hf]; exact one_ne_zero)
  have hL1 : f * dz (fLog f) = dz f := Sq.mul_dz_fLog hf
  have hL2 : f * dz (dz (fLog f)) + dz (fLog f) * dz f = dz (dz f) := by
    have := congrArg dz hL1
    rwa [dz_mul] at this
  have h' : dz (dz f) * f - dz f ^ 2 = g * f ^ 2 := h
  apply mul_left_cancel₀ (pow_ne_zero 2 hne)
  linear_combination f * hL2 - dz f * hL1 + h'

theorem constantCoeff_wpShift (P : PowerSeries K) (c : K) : constantCoeff (wpShift P c) = 1 := by
  simp [wpShift]

theorem dz_X_sq : dz ((X : PowerSeries K) ^ 2) = 2 * X := by
  have := dz_X_pow (K := K) 1; push_cast at this; linear_combination this

theorem linear_coeff_log_shifted_weierstrass (P : PowerSeries K) (c : K) :
    constantCoeff (dz (fLog (wpShift P c))) = 0 := by
  have h := congrArg constantCoeff (Sq.mul_dz_fLog (constantCoeff_wpShift P c))
  rw [map_mul, constantCoeff_wpShift, one_mul] at h
  rw [h, wpShift, dz_add, dz_mul, dz_one, dz_X_sq]
  simp

theorem second_log_derivative_two_isogeny (g2 g3 e1 : K) (P : PowerSeries K) (hP : IsWp g2 g3 P)
    (he : 4 * e1 ^ 3 - g2 * e1 - g3 = 0) :
    HasSecondLogDeriv (wpShift P e1) (2 * P - 2 * (C e1 + C (3 * e1 ^ 2 - g2 / 4) * wOf e1 P)) := by
  obtain ⟨hF1, hF2⟩ := weierstrassReducedEquations K g2 g3 P hP
  have hZW : wpShift P e1 = 1 + X ^ 2 * P - C e1 * X ^ 2 := by rw [wpShift]; ring
  rw [hZW]
  set Ze : PowerSeries K := 1 + X ^ 2 * P - C e1 * X ^ 2 with hZe
  have hZ0 : constantCoeff Ze = 1 := by simp [hZe]
  have hZ0' : constantCoeff Ze ≠ 0 := by rw [hZ0]; exact one_ne_zero
  have hw : wOf e1 P * Ze = X ^ 2 := by
    unfold wOf
    rw [mul_assoc, PowerSeries.inv_mul_cancel _ hZ0', mul_one]
  have e2 : dz ((X : PowerSeries K) ^ 2) = 2 * X := dz_X_sq
  have hZ1 : dz Ze = X ^ 2 * dz P + P * (2 * X) - C e1 * (2 * X) := by
    rw [hZe]; simp only [dz_sub, dz_add, dz_mul, dz_one, dz_C, e2]; ring
  have hZ2 : dz (dz Ze) = X ^ 2 * dz (dz P) + 4 * X * dz P + 2 * P - 2 * C e1 := by
    rw [hZ1]; simp only [dz_sub, dz_add, dz_mul, dz_two, dz_X, dz_C, e2]; ring
  have c2 : 2 * (C (3 * e1 ^ 2 - g2 / 4) : PowerSeries K) = 6 * C e1 ^ 2 - C (g2 / 2) := by
    simp only [← map_ofNat (C (R := K)), ← map_mul, ← map_pow, ← map_sub]; congr 1; ring
  have c3 : 2 * C (g2 / 2) = (C g2 : PowerSeries K) := by
    rw [← map_ofNat (C (R := K)) 2, ← map_mul]; congr 1; ring
  have he' : 4 * (C e1 : PowerSeries K) ^ 3 - C g2 * C e1 - C g3 = 0 := by
    simp only [← map_ofNat (C (R := K)), ← map_mul, ← map_pow, ← map_sub]; rw [he, map_zero]
  generalize 3 * e1 ^ 2 - g2 / 4 = kap at c2 ⊢
  have hB : Ze * dz (dz Ze) - dz Ze ^ 2 =
      (2 * P - 2 * C e1) * Ze ^ 2 - 2 * C kap * X ^ 2 * Ze := by
    rw [hZ2, hZ1, hZe]
    linear_combination (-1 : PowerSeries K) * hF1 + (1 + X ^ 2 * P - C e1 * X ^ 2) * hF2 -
      X ^ 4 * he' + X ^ 2 * (1 + X ^ 2 * P - C e1 * X ^ 2) * c2 -
      X ^ 2 * (1 + X ^ 2 * P - C e1 * X ^ 2) * c3
  show dz (dz Ze) * Ze - dz Ze ^ 2 = _
  linear_combination hB + 2 * C kap * Ze * hw

theorem theta_zero_isogeny_holds : Th0Isogeny := by
  intro K _ _ g2 g3 s2 c0 xT al S P ι _ c wp wm hP he hF hS
  obtain ⟨hF1, hF2⟩ := hF
  have hD := second_log_derivative_two_isogeny g2 g3 (xT + c0) P hP he
  unfold thTw thZ sigma1
  generalize xT + c0 = e1 at *
  generalize 3 * e1 ^ 2 - g2 / 4 = kap at *
  generalize wOf e1 P = w at *
  set n : ℕ := Fintype.card ι with hn
  have hS1 : constantCoeff (sigmaOneSeries e1 kap w) = 0 := Sq.constantCoeff_sig1S _ _ _
  have hq : constantCoeff (-(C (s2 / 2) * X ^ 2) : PowerSeries K) = 0 := by simp
  rw [← fExp_add hS1 hq]
  set abelian₂ : PowerSeries K := sigmaOneSeries e1 kap w + -(C (s2 / 2) * X ^ 2) with hLam
  have hL0 : constantCoeff abelian₂ = 0 := by rw [hLam, map_add (f := _), hS1, hq, add_zero]
  have hL1 : dz abelian₂ = -prim (C e1 + C kap * w) - C s2 * X := by
    have c3 : 2 * C (s2 / 2) = (C s2 : PowerSeries K) := by
      rw [← map_ofNat (C (R := K)) 2, ← map_mul]; congr 1; ring
    rw [hLam, sigmaOneSeries]
    simp only [dz_add, dz_neg, dz_prim, dz_mul, dz_C, dz_X_sq]
    linear_combination (-X : PowerSeries K) * c3
  have hL2 : dz (dz abelian₂) = -(C e1 + C kap * w) - C s2 := by
    rw [hL1]
    simp only [dz_sub, dz_neg, dz_prim, dz_mul, dz_C, dz_X]
    ring
  have hL1c : constantCoeff (dz abelian₂) = 0 := by
    rw [hL1]; simp [constantCoeff_prim]
  have hR0 : constantCoeff (rescale al abelian₂) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_zero_eq_constantCoeff_apply, hL0,
      mul_zero]
  have hZ1 : ∀ a : K, constantCoeff (wpShift P a) = 1 := constantCoeff_wpShift P
  have hZl : ∀ a : K, constantCoeff (fLog (wpShift P a)) = 0 := fun a => constantCoeff_fLog (hZ1 a)
  clear_value abelian₂
  have key : rescale al abelian₂ + n • fLog (wpShift P e1) =
      (2 * n) • abelian₂ + ∑ Q, fLog (wpShift P (c Q)) := by
    refine derivative.ext (derivative.ext ?_ ?_) ?_
    · show dz (dz _) = dz (dz _)
      have hsum : dz (dz (∑ Q, fLog (wpShift P (c Q)))) = ∑ Q, (2 * P - wp Q - wm Q) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [dz, dz, map_sum, map_sum]
        exact Finset.sum_congr rfl fun Q _ => second_derivative_formal_log (hZ1 _) (hF1 Q)
      have hsum2 : ∑ Q, (2 * P - wp Q - wm Q) =
          (n : PowerSeries K) * (2 * P) - ∑ Q, (wp Q + wm Q) := by
        have : ∀ Q, 2 * P - wp Q - wm Q = 2 * P - (wp Q + wm Q) := fun Q => by ring
        rw [Finset.sum_congr rfl fun Q _ => this Q, Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul]
      have hSC : C (al ^ 2) * C s2 - 2 * (n : PowerSeries K) * C s2 = C S := by
        rw [← hS, ← map_natCast (C (R := K)) n, ← map_ofNat (C (R := K)) 2]
        simp only [← map_mul, ← map_sub]
        congr 1; ring
      rw [dz_add, dz_add, dz_add, dz_add, hsum, hsum2, second_derivative_rescale, hL2, second_derivative_nsmul, second_derivative_nsmul, hL2,
        second_derivative_formal_log (hZ1 _) hD, map_sub, map_neg, rescale_C', nsmul_eq_mul, nsmul_eq_mul]
      push_cast
      linear_combination (-1 : PowerSeries K) * hF2 - hSC
    · show constantCoeff (dz _) = constantCoeff (dz _)
      have hsum : constantCoeff (dz (∑ Q, fLog (wpShift P (c Q)))) = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [dz, map_sum, map_sum]
        exact Finset.sum_eq_zero fun Q _ => linear_coeff_log_shifted_weierstrass P _
      have hr : constantCoeff (rescale al (dz abelian₂)) = 0 := by
        rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_zero_eq_constantCoeff_apply,
          hL1c, mul_zero]
      rw [dz_add, dz_add, map_add (f := _), map_add (f := _), hsum, dz_rescale, map_mul, hr, dz_nsmul, dz_nsmul,
        map_nsmul, map_nsmul, linear_coeff_log_shifted_weierstrass, hL1c]
      simp
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [map_add (f := _), map_add (f := _), hR0, map_nsmul, map_nsmul, hZl, hL0, map_sum,
        Finset.sum_eq_zero fun Q _ => hZl _]
        simp
  rw [Sq.rescale_fExp al hL0]
  have e1' : wpShift P e1 ^ n = fExp (n • fLog (wpShift P e1)) := by
    rw [fExp_nsmul (hZl _), fExp_fLog (hZ1 _)]
  have e2' : ∏ Q, wpShift P (c Q) = fExp (∑ Q, fLog (wpShift P (c Q))) := by
    rw [fExp_sum _ _ (fun Q => hZl _)]
    exact Finset.prod_congr rfl fun Q _ => (fExp_fLog (hZ1 _)).symm
  have hn0 : constantCoeff (n • fLog (wpShift P e1)) = 0 := by rw [map_nsmul, hZl, smul_zero]
  have hn1 : constantCoeff ((2 * n) • abelian₂) = 0 := by rw [map_nsmul, hL0, smul_zero]
  have hn2 : constantCoeff (∑ Q, fLog (wpShift P (c Q))) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; exact Finset.sum_eq_zero fun Q _ => hZl _
  rw [e1', e2', ← fExp_nsmul hL0, ← fExp_add hR0 hn0, ← fExp_add hn1 hn2, key]

end Formalism.L2.Th1.B.Iso
end
end

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.AtVariableWeierstrassDerivative
noncomputable section

namespace Formalism.L2.Th1.B.GCob

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)

section One

open PowerSeries

variable {K : Type} [Field K] [CharZero K]

theorem wOf_mul (e1 : K) (P : PowerSeries K) :
    wOf e1 P * (1 + X ^ 2 * P - C e1 * X ^ 2) = X ^ 2 := by
  unfold wOf
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by simp), mul_one]

theorem dz_wOf (e1 : K) (P : PowerSeries K) :
    (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2 * dz (wOf e1 P) = -(X * (-2 + X ^ 3 * dz P)) := by
  have h1 := wOf_mul e1 P
  have e2 : dz ((X : PowerSeries K) ^ 2) = 2 * X := by
    have := dz_X_pow (K := K) 1; push_cast at this; linear_combination this
  have hd := congrArg dz h1
  simp only [dz_sub, dz_add, dz_mul, dz_one, dz_C, e2] at hd
  linear_combination (1 + X ^ 2 * P - C e1 * X ^ 2) * hd -
    (X ^ 2 * dz P + P * (2 * X) - C e1 * (2 * X)) * h1

theorem subst_wOf_mul (e1 : K) (P : PowerSeries K) {l : PowerSeries K}
    (hl : constantCoeff l = 0) :
    subst l (wOf e1 P) * (1 + l ^ 2 * subst l P - C e1 * l ^ 2) = l ^ 2 := by
  have hs : HasSubst l := HasSubst.of_constantCoeff_zero' hl
  have := congrArg (subst l) (wOf_mul e1 P)
  rw [← coe_substAlgHom hs] at this
  simp only [map_sub, map_mul, map_add (f := _), map_one, map_pow] at this
  rw [coe_substAlgHom hs, subst_X hs, subst_C] at this
  exact this

theorem subst_dz_wOf (e1 : K) (P : PowerSeries K) {l : PowerSeries K}
    (hl : constantCoeff l = 0) :
    (1 + l ^ 2 * subst l P - C e1 * l ^ 2) ^ 2 * subst l (dz (wOf e1 P)) =
      -(l * (-2 + l ^ 3 * subst l (dz P))) := by
  have hs : HasSubst l := HasSubst.of_constantCoeff_zero' hl
  have := congrArg (subst l) (dz_wOf e1 P)
  rw [← coe_substAlgHom hs] at this
  simp only [map_sub, map_mul, map_add (f := _), map_one, map_pow, map_neg, map_ofNat] at this
  rw [coe_substAlgHom hs, subst_X hs, subst_C] at this
  exact this

theorem wl_mul_g {c0 xT : K} {P l ep : PowerSeries K} (hl : constantCoeff l = 0) (hl0 : l ≠ 0)
    (hcv : X ^ 2 * (1 + l ^ 2 * subst l P) = l ^ 2 * (ep + C c0 * X ^ 2)) :
    subst l (wOf (xT + c0) P) * gT ep xT = X ^ 2 := by
  apply mul_right_cancel₀ (pow_ne_zero 2 hl0)
  unfold gT
  have hw' := subst_wOf_mul (xT + c0) P hl
  rw [map_add (f := _)] at hw'
  linear_combination X ^ 2 * hw' - subst l (wOf (xT + c0) P) * hcv

theorem constantCoeff_gT {ep : PowerSeries K} (xT : K) (hep : constantCoeff ep = 1) :
    constantCoeff (gT ep xT) = 1 := by
  simp [gT, hep]

theorem thT_mul {ep : PowerSeries K} (xT yT : K) (hep : constantCoeff ep = 1) :
    thT ep xT yT * gT ep xT = ep + C yT * X ^ 3 := by
  unfold thT
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by rw [constantCoeff_gT xT hep]; exact one_ne_zero),
    mul_one]

theorem wprime_core {c0 a1 a3 xT yT : K} {P l ep : PowerSeries K} (hl : constantCoeff l = 0)
    (hl0 : l ≠ 0) (hep : constantCoeff ep = 1)
    (hcv : X ^ 2 * (1 + l ^ 2 * subst l P) = l ^ 2 * (ep + C c0 * X ^ 2))
    (h3 : X ^ 3 * (-2 + l ^ 3 * subst l (dz P)) =
      l ^ 3 * (-2 * ep + C a1 * X * ep + C a3 * X ^ 3))
    (hT : 2 * yT + a1 * xT + a3 = 0) :
    X * subst l (dz (wOf (xT + c0) P)) =
      subst l (wOf (xT + c0) P) * (2 * thT ep xT yT - C a1 * X) := by
  have hWg := wl_mul_g (xT := xT) hl hl0 hcv
  have hth := thT_mul xT yT hep
  have hZ := subst_dz_wOf (xT + c0) P hl
  have hg0 : gT ep xT ≠ 0 :=
    ne_zero_of_constantCoeff (by rw [constantCoeff_gT xT hep]; exact one_ne_zero)
  have hT' : 2 * (C yT : PowerSeries K) + C a1 * C xT + C a3 = 0 := by
    simp only [← map_ofNat (C (R := K)), ← map_mul, ← map_add (f := _)]; rw [hT, map_zero]
  rw [map_add (f := _)] at hZ
  generalize subst l (dz (wOf (xT + c0) P)) = W' at hZ ⊢
  generalize subst l (wOf (xT + c0) P) = W at hWg ⊢
  generalize subst l (dz P) = B at hZ h3
  generalize subst l P = A at hZ hcv
  generalize thT ep xT yT = th at hth ⊢
  have hXZ : X ^ 2 * (1 + l ^ 2 * A - (C xT + C c0) * l ^ 2) = l ^ 2 * gT ep xT := by
    unfold gT; linear_combination hcv
  have hXZ2 : (X ^ 2 * (1 + l ^ 2 * A - (C xT + C c0) * l ^ 2)) ^ 2 = (l ^ 2 * gT ep xT) ^ 2 := by
    rw [hXZ]
  have step1 : W' * gT ep xT ^ 2 = X * (2 * ep - C a1 * X * ep - C a3 * X ^ 3) := by
    apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 4 hl0) (pow_ne_zero 3 (PowerSeries.X_ne_zero (R := K))))
    linear_combination -X ^ 3 * W' * hXZ2 + X ^ 7 * hZ - X ^ 4 * l * h3
  apply mul_left_cancel₀ (pow_ne_zero 2 hg0)
  simp only [gT] at hWg hth step1 ⊢
  linear_combination X * step1 -
    (2 * th * (ep - C xT * X ^ 2) - C a1 * X * (ep - C xT * X ^ 2)) * hWg - 2 * X ^ 2 * hth -
    X ^ 5 * hT'

end One

theorem ne_zero_of_law {K : Type} [NormedField K] {F : MvPowerSeries (Fin 2) K}
    {l : PowerSeries K} (hL : LawLog F l) : l ≠ 0 := by
  intro h
  have := hL.2.2.2.1
  rw [h] at this
  simp at this

theorem weierstrass_derivative_unit_holds : WPrimeU := by
  intro K _ _ _ g2 g3 c0 a1 a3 xT yT P l i ep F _ hL hC hC3 hT
  exact wprime_core hL.2.2.1 (ne_zero_of_law hL) hC.2.1 hC.2.2.1 hC3.1 hT

section Two

variable {K : Type} [Field K] [CharZero K]

theorem subst_wg {ι : Type} {U : MvPowerSeries ι K} (hU : MvPowerSeries.constantCoeff U = 0)
    {W g : PowerSeries K} (h : W * g = PowerSeries.X ^ 2) :
    PowerSeries.subst U W * PowerSeries.subst U g = U ^ 2 := by
  have hs : PowerSeries.HasSubst U := PowerSeries.HasSubst.of_constantCoeff_zero hU
  have := congrArg (PowerSeries.subst U) h
  rwa [PowerSeries.subst_mul hs, PowerSeries.subst_pow hs, PowerSeries.subst_X hs] at this

theorem at_variable_weierstrass_derivative {ι : Type} (x : ι) {W W' th : PowerSeries K} {a1 : K}
    (h : PowerSeries.X * W' = W * (2 * th - PowerSeries.C a1 * PowerSeries.X)) :
    MvPowerSeries.X x * at1 x W' =
      at1 x W * (2 * at1 x th - MvPowerSeries.C a1 * MvPowerSeries.X x) := by
  have hs : PowerSeries.HasSubst (MvPowerSeries.X x : MvPowerSeries ι K) := PowerSeries.HasSubst.X x
  have := congrArg (PowerSeries.subst (MvPowerSeries.X x : MvPowerSeries ι K)) h
  rw [← PowerSeries.coe_substAlgHom hs] at this
  simp only [map_sub, map_mul, map_ofNat] at this
  rw [PowerSeries.coe_substAlgHom hs, PowerSeries.subst_X hs, PowerSeries.subst_C] at this
  exact this

theorem hsL {l : PowerSeries K} (hl : PowerSeries.constantCoeff l = 0) :
    MvPowerSeries.HasSubst (![at1 (0 : Fin 2) l, at1 1 l] : Fin 2 → MvPowerSeries (Fin 2) K) := by
  have h0 : MvPowerSeries.constantCoeff (at1 (0 : Fin 2) l) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (by simp) l hl
  have h1 : MvPowerSeries.constantCoeff (at1 (1 : Fin 2) l) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (by simp) l hl
  exact Formalism.G.LogP.hs2 h0 h1

theorem X_ne {ι : Type} (j : ι) : (MvPowerSeries.X j : MvPowerSeries ι K) ≠ 0 := by
  intro h
  have h2 := congrArg (MvPowerSeries.pderiv (R := K) j) h
  rw [MvPowerSeries.pderiv_X_self, map_zero] at h2
  exact one_ne_zero h2

theorem four_ne {ι : Type} : (4 : MvPowerSeries ι K) ≠ 0 := by
  intro h
  have := congrArg MvPowerSeries.constantCoeff h
  rw [map_ofNat, map_zero] at this
  exact absurd this (by norm_num)

theorem subst_log_at_variable (f : PowerSeries K) (x : Fin 2) {l : PowerSeries K}
    (hl : PowerSeries.constantCoeff l = 0) :
    MvPowerSeries.subst ![at1 (0 : Fin 2) l, at1 1 l] (at1 x f) =
      at1 x (PowerSeries.subst l f) := by
  rw [subst_at_variable_eq_subst f x (hsL hl), ParE.subst_inVar x f hl]
  fin_cases x <;> rfl

theorem sub_atS (f : PowerSeries K) {l : PowerSeries K} {F : MvPowerSeries (Fin 2) K}
    (hl : PowerSeries.constantCoeff l = 0) (hF : MvPowerSeries.constantCoeff F = 0)
    (hFl : PowerSeries.subst F l = at1 0 l + at1 1 l) :
    MvPowerSeries.subst ![at1 (0 : Fin 2) l, at1 1 l] (atS f) =
      PowerSeries.subst F (PowerSeries.subst l f) := by
  rw [ParO.subst_atS f (hsL hl), PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' hl) (PowerSeries.HasSubst.of_constantCoeff_zero hF),
    hFl]
  rfl

theorem wadd_law {kap : K} {w l : PowerSeries K} {F : MvPowerSeries (Fin 2) K}
    (hl : PowerSeries.constantCoeff l = 0) (hF : MvPowerSeries.constantCoeff F = 0)
    (hFl : PowerSeries.subst F l = at1 0 l + at1 1 l)
    (h : 4 * at1 0 w * at1 1 w * (1 - MvPowerSeries.C kap * at1 0 w * at1 1 w) ^ 2 * atS w =
      (at1 0 w * at1 1 (dz w) + at1 1 w * at1 0 (dz w)) ^ 2) :
    4 * at1 0 (PowerSeries.subst l w) * at1 1 (PowerSeries.subst l w) *
        (1 - MvPowerSeries.C kap * at1 0 (PowerSeries.subst l w) *
          at1 1 (PowerSeries.subst l w)) ^ 2 * PowerSeries.subst F (PowerSeries.subst l w) =
      (at1 0 (PowerSeries.subst l w) * at1 1 (PowerSeries.subst l (dz w)) +
        at1 1 (PowerSeries.subst l w) * at1 0 (PowerSeries.subst l (dz w))) ^ 2 := by
  have hb := hsL hl
  have e := congrArg (MvPowerSeries.subst ![at1 (0 : Fin 2) l, at1 1 l]) h
  rw [← MvPowerSeries.coe_substAlgHom hb] at e
  simp only [map_sub, map_mul, map_one, map_pow, map_add (f := _), map_ofNat] at e
  rw [MvPowerSeries.coe_substAlgHom hb, MvPowerSeries.subst_C] at e
  simp only [subst_log_at_variable _ _ hl, sub_atS _ hl hF hFl] at e
  exact e

theorem alg_core {R : Type} [CommRing R] [NoZeroDivisors R] (h4' : (4 : R) ≠ 0)
    {a b c Wa Wb Va Vb ta tb ga gb WF gF Fv d : R}
    (E1 : 4 * Wa * Wb * d ^ 2 * WF = (Wa * Vb + Wb * Va) ^ 2)
    (Ha : a * Va = Wa * (2 * ta - c * a)) (Hb : b * Vb = Wb * (2 * tb - c * b))
    (Ga : Wa * ga = a ^ 2) (Gb : Wb * gb = b ^ 2) (GF : WF * gF = Fv ^ 2)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    gF * (b * ta + a * tb - c * a * b) ^ 2 = ga * gb * Fv ^ 2 * d ^ 2 := by
  have hWa : Wa ≠ 0 := by
    rintro rfl
    rw [zero_mul] at Ga
    exact pow_ne_zero 2 ha Ga.symm
  have hWb : Wb ≠ 0 := by
    rintro rfl
    rw [zero_mul] at Gb
    exact pow_ne_zero 2 hb Gb.symm
  have H : a * b * (Wa * Vb + Wb * Va) = 2 * Wa * Wb * (b * ta + a * tb - c * a * b) := by
    linear_combination Wa * a * Hb + Wb * b * Ha
  have H2 : (a * b * (Wa * Vb + Wb * Va)) ^ 2 =
      (2 * Wa * Wb * (b * ta + a * tb - c * a * b)) ^ 2 := by rw [H]
  have h4 : (4 : R) * Wa ^ 2 * Wb ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero h4' (pow_ne_zero 2 hWa)) (pow_ne_zero 2 hWb)
  apply mul_left_cancel₀ h4
  linear_combination -gF * H2 - gF * a ^ 2 * b ^ 2 * E1 + 4 * a ^ 2 * b ^ 2 * Wa * Wb * d ^ 2 * GF -
    4 * Wa * Wb * Fv ^ 2 * d ^ 2 * (Wb * gb * Ga + a ^ 2 * Gb)

end Two

theorem GCob_of (hW : WAdd) (hP : WPrimeU) : GCob := by
  intro K _ _ _ g2 g3 c0 a1 a3 xT yT P l i ep F hWp hL hC hC3 hT he
  have hl := hL.2.2.1
  have hIW := wOfWp K g2 g3 (xT + c0) P hWp he
  have E1 := wadd_law hl hL.1 (ParO.log_law hL) (hW K _ _ _ hIW)
  have hp := hP K g2 g3 c0 a1 a3 xT yT P l i ep F hWp hL hC hC3 hT
  have hg := wl_mul_g (xT := xT) hl (ne_zero_of_law hL) hC.2.2.1
  unfold LT
  exact alg_core four_ne E1 (at_variable_weierstrass_derivative 0 hp) (at_variable_weierstrass_derivative 1 hp)
    (subst_wg (MvPowerSeries.constantCoeff_X (0 : Fin 2)) hg)
    (subst_wg (MvPowerSeries.constantCoeff_X (1 : Fin 2)) hg) (subst_wg hL.1 hg)
    (X_ne 0) (X_ne 1)

end Formalism.L2.Th1.B.GCob
end
end

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.PhENormOf
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B.Nrm

open Formalism.G (unitBall)
open Formalism.L2.Th1.C (wpShift IsLogPair mulBy PhNormAt Cong LG IntMv IntPS mvExp IsOneUnit XIsWp)
open Formalism.L2.Th1.C.USideB

theorem PhENorm_of (hI : Th0Isogeny) : PhENorm := by
  intro K _ _ _ g2 g3 s2 c0 xT al albar S P l linv i ep F ι _ xQ wp wm hP hT hL hC hxT hxQ hZ hN hS
  have hl := hL.1
  have hsl := hs_of hl
  have hcv : PowerSeries.constantCoeff (mulBy l linv al) = 0 := cc_mulBy hL al
  have hsv := hs_of hcv
  have hS' : (al ^ 2 - 2 * (Fintype.card ι : K)) * s2 = S := by rw [← hN, ← hS]; ring
  have hF := hI K g2 g3 s2 c0 xT al S P ι (fun Q => xQ Q + c0) wp wm hP hT hZ hS'
  obtain ⟨hph0, hphd⟩ :=
    phEDef K s2 (xT + c0) (3 * (xT + c0) ^ 2 - g2 / 4) (wOf (xT + c0) P) l hl
  generalize hn : Fintype.card ι = n at *
  have hthl : PowerSeries.subst l (thTw g2 s2 c0 xT P) = mvExp (-(phTw g2 s2 c0 xT P l)) := hphd
  have hph0' : PowerSeries.constantCoeff (phTw g2 s2 c0 xT P l) = 0 := hph0
  generalize phTw g2 s2 c0 xT P l = ph at *
  generalize thTw g2 s2 c0 xT P = th at *
  set v := mulBy l linv al with hv
  have hnph : PowerSeries.constantCoeff (-ph) = 0 := by simp [hph0']
  have hphv : PowerSeries.constantCoeff (PowerSeries.subst v ph) = 0 := cc_subst hcv hph0'
  have hnphv : PowerSeries.constantCoeff (-(PowerSeries.subst v ph)) = 0 := by simp [hphv]
  have hX : XIsWp P l ep c0 := by
    unfold XIsWp
    rw [Formalism.L2.Th1.C.USideA.subst_wpShift_zero hsl, hC.2.2.1]
    ring

  have h1 : PowerSeries.subst l (PowerSeries.rescale al th) =
      mvExp (-(PowerSeries.subst v ph)) := by
    rw [subst_rescale hL, hthl, Formalism.L2.Th1.C.subst_mvExp hnph hcv]
    have h3 : PowerSeries.subst v (-ph) = -(PowerSeries.subst v ph) := by
      rw [← PowerSeries.coe_substAlgHom hsv, map_neg]
    rw [h3]

  have h4 := congrArg (PowerSeries.subst l) hF
  rw [PowerSeries.subst_mul hsl, PowerSeries.subst_pow hsl, PowerSeries.subst_mul hsl,
    PowerSeries.subst_pow hsl, h1, hthl] at h4
  have h6 : PowerSeries.subst l (∏ Q, wpShift P (xQ Q + c0)) =
      ∏ Q, PowerSeries.subst l (wpShift P (xQ Q + c0)) := by
    rw [← PowerSeries.coe_substAlgHom hsl, map_prod]
  rw [h6] at h4
  have h7 : PowerSeries.X ^ (2 * n) * ∏ Q, PowerSeries.subst l (wpShift P (xQ Q + c0)) =
      (∏ Q, (ep - PowerSeries.C (xQ Q) * PowerSeries.X ^ 2)) * l ^ (2 * n) := by
    rw [pow_mul, pow_mul, ← hn, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_const,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun Q _ => subst_wpShift hl hX (xQ Q)
  have h8 := subst_wpShift hl hX xT
  set B : PowerSeries K := ∏ Q, (ep - PowerSeries.C (xQ Q) * PowerSeries.X ^ 2) with hB
  set G : PowerSeries K := ep - PowerSeries.C xT * PowerSeries.X ^ 2 with hG
  have hl0 : l ^ (2 * n) ≠ 0 := pow_ne_zero _ (l_ne_zero hL)
  have h9 : (mvExp (-(PowerSeries.subst v ph)) : PowerSeries K) * G ^ n =
      mvExp (-ph) ^ (2 * n) * B := by
    apply mul_right_cancel₀ hl0
    calc (mvExp (-(PowerSeries.subst v ph)) : PowerSeries K) * G ^ n * l ^ (2 * n)
        = mvExp (-(PowerSeries.subst v ph)) * (G * l ^ 2) ^ n := by
          rw [mul_pow, ← pow_mul, mul_assoc]
      _ = (mvExp (-(PowerSeries.subst v ph)) *
            PowerSeries.subst l (wpShift P (xT + c0)) ^ n) * PowerSeries.X ^ (2 * n) := by
          rw [← h8]; ring
      _ = mvExp (-ph) ^ (2 * n) *
            (PowerSeries.X ^ (2 * n) * ∏ Q, PowerSeries.subst l (wpShift P (xQ Q + c0))) := by
          rw [h4]; ring
      _ = _ := by rw [h7]; ring

  have hepi : ep ∈ intSub (unitBall K) := fun k => hC.1 (Finsupp.single () k)
  have hBi : B ∈ intSub (unitBall K) :=
    Subring.prod_mem _ fun Q _ => Subring.sub_mem _ hepi
      (Subring.mul_mem _ (C_mem_intSub (hxQ Q)) (Subring.pow_mem _ (X_mem_intSub _) 2))
  have hGi : G ∈ intSub (unitBall K) :=
    Subring.sub_mem _ hepi
      (Subring.mul_mem _ (C_mem_intSub hxT) (Subring.pow_mem _ (X_mem_intSub _) 2))
  have hB1 : PowerSeries.constantCoeff B = 1 := by
    rw [hB, map_prod]
    apply Finset.prod_eq_one
    intro Q _
    simp [hC.2.1]
  have hNph : (al * albar) • ph = ((2 * n : ℕ) : K) • ph := by rw [hN]; push_cast; rfl
  have hNph0 : PowerSeries.constantCoeff (((2 * n : ℕ) : K) • ph) = 0 := by simp [hph0']
  have h10 : (mvExp (PowerSeries.subst v ph - (al * albar) • ph) : PowerSeries K) * B = G ^ n := by
    rw [hNph, Formalism.L2.Th1.C.mvExp_sub hphv hNph0, ← smul_neg,
      Formalism.L2.Th1.C.mvExp_smul_nat hnph, mul_assoc, ← h9, ← mul_assoc,
      Formalism.L2.Th1.C.mvExp_mul_neg hphv, one_mul]
  have h11 : IntPS (unitBall K) (mvExp (PowerSeries.subst v ph - (al * albar) • ph)) :=
    int_of_mul ⟨hB1, hBi⟩ (Subring.pow_mem _ hGi n) h10
  refine ⟨?_, intMv_of_intPS h11⟩
  have : PowerSeries.constantCoeff (PowerSeries.subst v ph - (al * albar) • ph) = 0 := by
    simp [hphv, hph0']
  exact this

end Formalism.L2.Th1.B.Nrm
end
end
