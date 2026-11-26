module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalA
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffSeriesAtVariable
public import Formalism.GL3MeanSquares.HookFormulaTorsion.ExpSeries
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.InVarAddInVarNeZero

@[expose] public section

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.WeierstrassSeriesIntegral
noncomputable section

namespace Formalism.L2.Th1.B.ParE

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence (integral_iff_lift integral_mul' integral_one' integral_of_mul_eq_one)

section Alg

variable {K : Type} [Field K] [CharZero K] {ι : Type}

theorem subst_inVar (x : ι) (f : PowerSeries K) {l : PowerSeries K}
    (hl : PowerSeries.constantCoeff l = 0) :
    at1 x (PowerSeries.subst l f) = PowerSeries.subst (at1 x l) f := by
  unfold at1
  exact PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hl)
    (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X x)) f

end Alg

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K] {ι : Type}

theorem integral_sub' {f g : MvPowerSeries ι K} (hf : Integral f) (hg : Integral g) :
    Integral (f - g) := by
  intro n
  rw [map_sub, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) ?_)
  rw [norm_neg]
  exact hg n

theorem integral_add' {f g : MvPowerSeries ι K} (hf : Integral f) (hg : Integral g) :
    Integral (f + g) := by
  intro n
  rw [map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) (hg n))

theorem integral_C' {c : K} (hc : ‖c‖ ≤ 1) : Integral (MvPowerSeries.C c : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_C]
  split_ifs
  · exact hc
  · simp

end Norm

theorem weierstrass_series_integral : WIntegral := by
  intro K _ _ _ c0 e1 P l i ep F hLL hCH hce
  obtain ⟨hepI, hep1, hcurve, -⟩ := hCH
  have hl0 : PowerSeries.constantCoeff l = 0 := hLL.2.2.1
  have hl1 : PowerSeries.coeff 1 l = 1 := hLL.2.2.2.1
  have ha : PowerSeries.HasSubst l := PowerSeries.HasSubst.of_constantCoeff_zero hl0
  have hlne : l ≠ 0 := by
    rintro rfl
    simp at hl1
  have hD0c : PowerSeries.constantCoeff
      (1 + PowerSeries.X ^ 2 * P - PowerSeries.C e1 * PowerSeries.X ^ 2 : PowerSeries K) ≠ 0 := by
    simp
  have hCe : PowerSeries.subst l (PowerSeries.C e1 : PowerSeries K) = (PowerSeries.C e1 : PowerSeries K) := by
    have h := (PowerSeries.substAlgHom ha).commutes e1
    rw [PowerSeries.coe_substAlgHom] at h
    simpa [MvPowerSeries.algebraMap_apply, PowerSeries.algebraMap_apply] using h
  have hw : wOf e1 P * (1 + PowerSeries.X ^ 2 * P - PowerSeries.C e1 * PowerSeries.X ^ 2) =
      PowerSeries.X ^ 2 := by
    unfold wOf
    rw [mul_assoc, PowerSeries.inv_mul_cancel _ hD0c, mul_one]
  have hWD : PowerSeries.subst l (wOf e1 P) *
      (1 + l ^ 2 * PowerSeries.subst l P - PowerSeries.C e1 * l ^ 2) = l ^ 2 := by
    have h := congrArg (PowerSeries.subst l) hw
    rw [← PowerSeries.coe_substAlgHom ha] at h
    simp only [map_add (f := _), map_sub, map_one, map_mul, map_pow] at h
    rw [PowerSeries.coe_substAlgHom ha, PowerSeries.subst_X ha, hCe] at h
    exact h
  have hkey : PowerSeries.subst l (wOf e1 P) * (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) * l ^ 2 =
      PowerSeries.X ^ 2 * l ^ 2 := by
    rw [map_sub]
    linear_combination (-PowerSeries.subst l (wOf e1 P)) * hcurve + PowerSeries.X ^ 2 * hWD
  have h1 : PowerSeries.subst l (wOf e1 P) * (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) =
      PowerSeries.X ^ 2 := mul_right_cancel₀ (pow_ne_zero 2 hlne) hkey
  refine ⟨h1, ?_⟩
  have hX : Integral (ι := Unit) (PowerSeries.X : PowerSeries K) := law_integral_X ()
  have hX2 : Integral (ι := Unit) (PowerSeries.X ^ 2 : PowerSeries K) := by
    rw [pow_two]
    exact integral_mul' hX hX
  have hEI : Integral (ι := Unit) (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) :=
    integral_add' hepI (integral_mul' (integral_C' hce) hX2)
  have hEc : MvPowerSeries.constantCoeff (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2 : PowerSeries K) = 1 := by
    have h : PowerSeries.constantCoeff (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) = 1 := by
      simp [hep1]
    exact h
  have hEc' : PowerSeries.constantCoeff (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) ≠ 0 := by
    simp [hep1]
  have hVI : Integral (ι := Unit) (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2)⁻¹ :=
    integral_of_mul_eq_one hEI hEc (PowerSeries.inv_mul_cancel _ hEc')
  have hWe : PowerSeries.subst l (wOf e1 P) =
      PowerSeries.X ^ 2 * (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2)⁻¹ := by
    calc PowerSeries.subst l (wOf e1 P)
        = PowerSeries.subst l (wOf e1 P) * ((ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) *
            (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2)⁻¹) := by
          rw [PowerSeries.mul_inv_cancel _ hEc', mul_one]
      _ = (PowerSeries.subst l (wOf e1 P) * (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2)) *
            (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2)⁻¹ := by
          rw [mul_assoc]
      _ = _ := by rw [h1]
  rw [hWe]
  exact integral_mul' hX2 hVI

end Formalism.L2.Th1.B.ParE
end
end

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.InvariantDerivationSubstLawThree
noncomputable section

namespace Formalism.L2.Th1.B.Jets

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3)
open Formalism.G.LogP (hs2 psubst_subst constantCoeff_subst_of_zero psubst_injective)

section Alg

variable {K : Type} [Field K] [CharZero K]

theorem cc_dz {l : PowerSeries K} (h1 : PowerSeries.coeff 1 l = 1) :
    PowerSeries.constantCoeff (dz l) = 1 := by
  have h := PowerSeries.coeff_derivative l 0
  simpa [h1] using h

theorem inv_mul_dz {l : PowerSeries K} (h1 : PowerSeries.coeff 1 l = 1) :
    (dz l)⁻¹ * dz l = 1 := PowerSeries.inv_mul_cancel _ (by rw [cc_dz h1]; exact one_ne_zero)

theorem ccX {ι : Type} (i : ι) :
    MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries ι K) = 0 := by
  exact MvPowerSeries.constantCoeff_X i

theorem inv_mul_dz_subst {ι : Type} {l : PowerSeries K} (h1 : PowerSeries.coeff 1 l = 1)
    {U : MvPowerSeries ι K} (hU : MvPowerSeries.constantCoeff U = 0) :
    PowerSeries.subst U (dz l)⁻¹ * PowerSeries.subst U (dz l) = 1 := by
  have hs : PowerSeries.HasSubst U := PowerSeries.HasSubst.of_constantCoeff_zero hU
  rw [← PowerSeries.coe_substAlgHom hs, ← map_mul, inv_mul_dz h1, map_one]

def Dj (l : PowerSeries K) (j : Fin 3) (g : MvPowerSeries (Fin 3) K) : MvPowerSeries (Fin 3) K :=
  at1 j (dz l)⁻¹ * pd j g

theorem Dj_sub (l : PowerSeries K) (j : Fin 3) (a b : MvPowerSeries (Fin 3) K) :
    Dj l j (a - b) = Dj l j a - Dj l j b := by
  simp only [Dj, pd, map_sub, mul_sub]

theorem Dj_psubst {l : PowerSeries K} (h1 : PowerSeries.coeff 1 l = 1) (j : Fin 3)
    (g : PowerSeries K) {U : MvPowerSeries (Fin 3) K} (hU : MvPowerSeries.constantCoeff U = 0) :
    Dj l j (PowerSeries.subst U g) =
      PowerSeries.subst U (Dinv l g) * (at1 j (dz l)⁻¹ * pd j (PowerSeries.subst U l)) := by
  have hinv := inv_mul_dz_subst h1 hU
  simp only [dz] at hinv
  simp only [Dj, pd, Dinv, dz]
  rw [Formalism.G.LogCR.pderiv_psubst hU, Formalism.G.LogCR.pderiv_psubst hU,
    PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero hU)]
  linear_combination (-(at1 j (PowerSeries.derivative (R := K) l)⁻¹ *
    PowerSeries.subst U (PowerSeries.derivative (R := K) g) * MvPowerSeries.pderiv (R := K) j U)) * hinv

theorem key {l : PowerSeries K} (h1 : PowerSeries.coeff 1 l = 1) (j k : Fin 3) :
    at1 j (dz l)⁻¹ * pd j (PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries (Fin 3) K) l) =
      if k = j then 1 else 0 := by
  have hX : MvPowerSeries.constantCoeff (MvPowerSeries.X k : MvPowerSeries (Fin 3) K) = 0 := ccX k
  simp only [pd]
  rw [Formalism.G.LogCR.pderiv_psubst hX]
  by_cases hkj : k = j
  · subst hkj
    rw [MvPowerSeries.pderiv_X_self, mul_one, if_pos rfl]
    exact inv_mul_dz_subst h1 hX
  · rw [MvPowerSeries.pderiv_X_of_ne hkj, mul_zero, mul_zero, if_neg hkj]

theorem cob_subst {ι : Type} {F : MvPowerSeries (Fin 2) K}
    (hF : MvPowerSeries.constantCoeff F = 0) (f : PowerSeries K) {A B : MvPowerSeries ι K}
    (hA : MvPowerSeries.constantCoeff A = 0) (hB : MvPowerSeries.constantCoeff B = 0) :
    MvPowerSeries.subst ![A, B] (cob F f) =
      PowerSeries.subst (MvPowerSeries.subst ![A, B] F) f - PowerSeries.subst A f -
        PowerSeries.subst B f := by
  have hAB : MvPowerSeries.HasSubst ![A, B] := hs2 hA hB
  simp only [cob, at1]
  rw [MvPowerSeries.subst_sub hAB, MvPowerSeries.subst_sub hAB, psubst_subst f hF hAB,
    psubst_subst f (MvPowerSeries.constantCoeff_X 0) hAB,
    psubst_subst f (MvPowerSeries.constantCoeff_X 1) hAB,
    MvPowerSeries.subst_X hAB, MvPowerSeries.subst_X hAB]
  simp

theorem law_subst {ι : Type} {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K}
    (hF : MvPowerSeries.constantCoeff F = 0) (hc : cob F l = 0) {A B : MvPowerSeries ι K}
    (hA : MvPowerSeries.constantCoeff A = 0) (hB : MvPowerSeries.constantCoeff B = 0) :
    PowerSeries.subst (MvPowerSeries.subst ![A, B] F) l =
      PowerSeries.subst A l + PowerSeries.subst B l := by
  have e := cob_subst hF l hA hB
  rw [hc, Formalism.G.LogP.subst_zero' (hs2 hA hB)] at e
  linear_combination -e

theorem cc_law {ι : Type} {F : MvPowerSeries (Fin 2) K}
    (hF : MvPowerSeries.constantCoeff F = 0) {A B : MvPowerSeries ι K}
    (hA : MvPowerSeries.constantCoeff A = 0) (hB : MvPowerSeries.constantCoeff B = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst ![A, B] F) = 0 := MvPowerSeries.constantCoeff_subst_eq_zero (hs2 hA hB)
    (fun i => by fin_cases i <;> simp [hA, hB]) hF

def U2 (F : MvPowerSeries (Fin 2) K) (a b : Fin 3) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst ![(MvPowerSeries.X a : MvPowerSeries (Fin 3) K), MvPowerSeries.X b] F

def U3 (F : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst ![U2 F 0 1, MvPowerSeries.X 2] F

theorem constantCoeff_law_pair {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (a b : Fin 3) : MvPowerSeries.constantCoeff (U2 F a b) = 0 := by
  unfold U2
  exact cc_law hF (ccX a) (ccX b)

theorem constantCoeff_law_three {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (U3 F) = 0 := by
  unfold U3
  exact cc_law hF (constantCoeff_law_pair hF 0 1) (ccX 2)

theorem coboundary_formal_add_biextension {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (f : PowerSeries K) :
    d1 F (cob F f) =
      PowerSeries.subst (U3 F) f - PowerSeries.subst (U2 F 0 1) f -
          PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) f -
        (PowerSeries.subst (U2 F 0 2) f -
          PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) f -
          PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) f) -
        (PowerSeries.subst (U2 F 1 2) f -
          PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K) f -
          PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) f) := by
  have e : in3 F = U2 F 0 1 := rfl
  simp only [d1]
  rw [e, cob_subst hF f (constantCoeff_law_pair hF 0 1) (ccX 2), cob_subst hF f (ccX 0) (ccX 2),
    cob_subst hF f (ccX 1) (ccX 2)]
  rfl

section Steps

variable {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K}

theorem Dj_X (h1 : PowerSeries.coeff 1 l = 1) (j k : Fin 3) (g : PowerSeries K) :
    Dj l j (PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries (Fin 3) K) g) =
      if k = j then PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries (Fin 3) K) (Dinv l g)
      else 0 := by
  rw [Dj_psubst h1 j g (ccX k), key h1 j k]
  split_ifs <;> simp

theorem invariant_derivation_subst_law_pair (hF : MvPowerSeries.constantCoeff F = 0) (hc : cob F l = 0)
    (h1 : PowerSeries.coeff 1 l = 1) (j a b : Fin 3) (hab : a ≠ b) (g : PowerSeries K) :
    Dj l j (PowerSeries.subst (U2 F a b) g) =
      if a = j ∨ b = j then PowerSeries.subst (U2 F a b) (Dinv l g) else 0 := by
  rw [Dj_psubst h1 j g (constantCoeff_law_pair hF a b)]
  have hl : PowerSeries.subst (U2 F a b) l =
      PowerSeries.subst (MvPowerSeries.X a : MvPowerSeries (Fin 3) K) l +
        PowerSeries.subst (MvPowerSeries.X b : MvPowerSeries (Fin 3) K) l :=
    law_subst hF hc (ccX a) (ccX b)
  have ka := key h1 j a
  have kb := key h1 j b
  simp only [pd] at ka kb
  rw [hl]
  simp only [pd, map_add (f := _), mul_add]
  rw [ka, kb]
  rcases eq_or_ne a j with ha | ha <;> rcases eq_or_ne b j with hb | hb
  · exact absurd (ha.trans hb.symm) hab
  · simp [ha, hb]
  · simp [ha, hb]
  · simp [ha, hb]

theorem invariant_derivation_subst_law_three (hF : MvPowerSeries.constantCoeff F = 0) (hc : cob F l = 0)
    (h1 : PowerSeries.coeff 1 l = 1) (j : Fin 3) (g : PowerSeries K) :
    Dj l j (PowerSeries.subst (U3 F) g) = PowerSeries.subst (U3 F) (Dinv l g) := by
  rw [Dj_psubst h1 j g (constantCoeff_law_three hF)]
  have e1 : PowerSeries.subst (U3 F) l =
      PowerSeries.subst (U2 F 0 1) l +
        PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) l := by
    unfold U3
    exact law_subst hF hc (constantCoeff_law_pair hF 0 1) (ccX 2)
  have e2 : PowerSeries.subst (U2 F 0 1) l =
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) l +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K) l :=
    law_subst hF hc (ccX 0) (ccX 1)
  have k0 := key h1 j 0
  have k1 := key h1 j 1
  have k2 := key h1 j 2
  simp only [pd] at k0 k1 k2
  rw [e1, e2]
  simp only [pd, map_add (f := _), mul_add]
  rw [k0, k1, k2]
  have hsum : ((if (0 : Fin 3) = j then 1 else 0) + (if (1 : Fin 3) = j then 1 else 0) +
      (if (2 : Fin 3) = j then 1 else 0) : MvPowerSeries (Fin 3) K) = 1 := by
    fin_cases j <;> simp
  rw [← mul_add, ← mul_add, hsum, mul_one]

theorem step2 (hF : MvPowerSeries.constantCoeff F = 0) (hc : cob F l = 0)
    (h1 : PowerSeries.coeff 1 l = 1) (f : PowerSeries K) :
    Dj l 2 (d1 F (cob F f)) =
      PowerSeries.subst (U3 F) (Dinv l f) - PowerSeries.subst (U2 F 0 2) (Dinv l f) -
        (PowerSeries.subst (U2 F 1 2) (Dinv l f) -
          PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) (Dinv l f)) := by
  rw [coboundary_formal_add_biextension hF f]
  simp only [Dj_sub, invariant_derivation_subst_law_three hF hc h1, Dj_X h1]
  rw [invariant_derivation_subst_law_pair hF hc h1 2 0 1 (by decide), invariant_derivation_subst_law_pair hF hc h1 2 0 2 (by decide),
    invariant_derivation_subst_law_pair hF hc h1 2 1 2 (by decide)]
  simp

theorem step1 (hF : MvPowerSeries.constantCoeff F = 0) (hc : cob F l = 0)
    (h1 : PowerSeries.coeff 1 l = 1) (g : PowerSeries K) :
    Dj l 1 (PowerSeries.subst (U3 F) g - PowerSeries.subst (U2 F 0 2) g -
        (PowerSeries.subst (U2 F 1 2) g -
          PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) g)) =
      PowerSeries.subst (U3 F) (Dinv l g) - PowerSeries.subst (U2 F 1 2) (Dinv l g) := by
  simp only [Dj_sub, invariant_derivation_subst_law_three hF hc h1, Dj_X h1]
  rw [invariant_derivation_subst_law_pair hF hc h1 1 0 2 (by decide), invariant_derivation_subst_law_pair hF hc h1 1 1 2 (by decide)]
  simp

theorem step0 (hF : MvPowerSeries.constantCoeff F = 0) (hc : cob F l = 0)
    (h1 : PowerSeries.coeff 1 l = 1) (g : PowerSeries K) :
    Dj l 0 (PowerSeries.subst (U3 F) g - PowerSeries.subst (U2 F 1 2) g) =
      PowerSeries.subst (U3 F) (Dinv l g) := by
  simp only [Dj_sub, invariant_derivation_subst_law_three hF hc h1]
  rw [invariant_derivation_subst_law_pair hF hc h1 0 1 2 (by decide)]
  simp

theorem chain (hF : MvPowerSeries.constantCoeff F = 0) (hc : cob F l = 0)
    (h1 : PowerSeries.coeff 1 l = 1) (f : PowerSeries K) (k : ℕ) :
    (Dj l 0)^[k] (Dj l 0 (Dj l 1 (Dj l 2 (d1 F (cob F f))))) =
      PowerSeries.subst (U3 F) ((Dinv l)^[k + 3] f) := by
  have base : Dj l 0 (Dj l 1 (Dj l 2 (d1 F (cob F f)))) =
      PowerSeries.subst (U3 F) ((Dinv l)^[3] f) := by
    rw [step2 hF hc h1 f, step1 hF hc h1, step0 hF hc h1]
    rfl
  induction k with
  | zero => exact base
  | succ k ih =>
    rw [Function.iterate_succ_apply' (Dj l 0), ih, invariant_derivation_subst_law_three hF hc h1]
    congr 1
    rw [show k + 1 + 3 = (k + 3) + 1 by omega]
    exact (Function.iterate_succ_apply' (Dinv l) (k + 3) f).symm

theorem constantCoeff_subst_law_three (hF : MvPowerSeries.constantCoeff F = 0) (g : PowerSeries K) :
    MvPowerSeries.constantCoeff (PowerSeries.subst (U3 F) g) = PowerSeries.constantCoeff g := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_law_three hF)
  have hg : g = PowerSeries.C (PowerSeries.constantCoeff g) +
      (g - PowerSeries.C (PowerSeries.constantCoeff g)) := by ring
  have h0 : PowerSeries.constantCoeff (g - PowerSeries.C (PowerSeries.constantCoeff g)) = 0 := by
    simp
  conv_lhs => rw [hg]
  rw [PowerSeries.subst_add hs, PowerSeries.subst_C, map_add (f := _), MvPowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_law_three hF) _ h0, add_zero]

theorem inv_dz_eq (hF : MvPowerSeries.constantCoeff F = 0) (hc : cob F l = 0)
    (h0 : PowerSeries.constantCoeff l = 0) (h1 : PowerSeries.coeff 1 l = 1) :
    (dz l)⁻¹ = ev0 (pd 1 F) := by
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries K) = 0 :=
    PowerSeries.constantCoeff_X
  have hz : MvPowerSeries.constantCoeff (0 : PowerSeries K) = 0 := map_zero _
  have hev : ev0 F = PowerSeries.X := by
    have hl := law_subst hF hc hX hz
    apply psubst_injective h0 h1 (cc_law hF hX hz) hX
    rw [hl,
      PowerSeries.subst_zero_of_constantCoeff_zero h0, add_zero]
  have hcob : PowerSeries.subst F l = at1 0 l + at1 1 l := by
    have e := hc
    simp only [cob] at e
    linear_combination e
  have hd := congrArg (MvPowerSeries.pderiv (R := K) 1) hcob
  simp only [at1] at hd
  rw [Formalism.G.LogCR.pderiv_psubst hF, map_add (f := _), Formalism.G.LogCR.pderiv_psubst (ccX (0 : Fin 2)),
    Formalism.G.LogCR.pderiv_psubst (ccX (1 : Fin 2)), MvPowerSeries.pderiv_X_of_ne (by decide),
    MvPowerSeries.pderiv_X_self, mul_zero, zero_add, mul_one] at hd
  have he := congrArg ev0 hd
  have w := restrictSecondZero_inVar_one (K := K) (dz l)
  have c1 := cc_dz h1
  simp only [at1, dz] at w c1
  rw [evalYZero_mul, evalYZero_subst _ hF, hev, w, c1, map_one] at he
  rw [PowerSeries.X_subst] at he
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by rw [cc_dz h1]; exact one_ne_zero)]
  simp only [pd, dz]
  rw [mul_comm]
  exact he

end Steps

end Alg

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem integral_pd {ι : Type} (j : ι) {f : MvPowerSeries ι K} (hf : Integral f) :
    Integral (pd j f) := by
  intro n
  simp only [pd]
  rw [MvPowerSeries.coeff_pderiv, norm_mul]
  have hn : ‖((n j : K) + 1)‖ ≤ 1 := by
    exact_mod_cast IsUltrametricDist.norm_natCast_le_one K (n j + 1)
  calc _ ≤ 1 * 1 := mul_le_mul (hf _) hn (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem integral_X {ι : Type} (x : ι) : Integral (MvPowerSeries.X x : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem integral_eval_second_zero {h : MvPowerSeries (Fin 2) K} (hh : Integral h) :
    Integral (ι := Unit) (ev0 h) := by
  intro n
  rw [Finsupp.unique_single n]
  show ‖PowerSeries.coeff (n default) (ev0 h)‖ ≤ 1
  rw [coeff_evalYZero]
  exact hh _

theorem integral_om {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    (j : Fin 3) : Integral (at1 j (dz l)⁻¹) := by
  rw [inv_dz_eq h.1 h.2.2.2.2 h.2.2.1 h.2.2.2.1]
  exact Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst'
    (φ := fun _ : Unit => (MvPowerSeries.X j : MvPowerSeries (Fin 3) K))
    (fun _ => ccX j) (fun _ => integral_X j) (integral_eval_second_zero (integral_pd 1 h.2.1))

theorem integral_Dj {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    (j : Fin 3) {g : MvPowerSeries (Fin 3) K} (hg : Integral (pd j g)) : Integral (Dj l j g) := Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' (integral_om h j) hg

theorem integral_pd_of_simeq {ι : Type} [Finite ι] {T : MvPowerSeries ι K} (hT : Simeq T 0)
    (j : ι) : Integral (pd j T) := by
  obtain ⟨hc0, hE⟩ := hT
  rw [sub_zero] at hc0 hE
  have hneg : MvPowerSeries.constantCoeff (-T) = 0 := by rw [map_neg, hc0, neg_zero]
  have hprod : mvExp (-T) * mvExp T = 1 := by
    have e := fExp_add hneg hc0
    rw [neg_add_cancel] at e
    change fExp (-T) * fExp T = 1
    rw [← e]
    exact Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.mvExp_zero'
  have hinvI : Integral (mvExp (-T)) :=
    Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_of_mul_eq_one hE (Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.constantCoeff_mvExp' hc0) hprod
  have hpdT : pd j T = mvExp (-T) * pd j (mvExp T) := by
    have hpd := pd_fExp j hc0
    change pd j T = fExp (-T) * pd j (fExp T)
    rw [hpd, ← mul_assoc]
    change pd j T = mvExp (-T) * mvExp T * pd j T
    rw [hprod, one_mul]
  rw [hpdT]
  exact Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' hinvI (integral_pd j hE)

theorem integral_chain {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    {T : MvPowerSeries (Fin 3) K} (hT : Simeq T 0) (k : ℕ) :
    Integral ((Dj l 0)^[k] (Dj l 0 (Dj l 1 (Dj l 2 T)))) := by
  have step : ∀ (j : Fin 3) (g : MvPowerSeries (Fin 3) K), Integral g → Integral (Dj l j g) :=
    fun j g hg => integral_Dj h j (integral_pd j hg)
  have base : Integral (Dj l 0 (Dj l 1 (Dj l 2 T))) :=
    step 0 _ (step 1 _ (integral_Dj h 2 (integral_pd_of_simeq hT 2)))
  induction k with
  | zero => exact base
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact step 0 _ ih

end Norm

theorem jets_three_variables_holds : JetsThree := by
  intro K _ _ _ F l f h hs n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hI := integral_chain h hs k
  rw [chain h.1 h.2.2.2.2 h.2.2.2.1 f k] at hI
  have e := hI 0
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_subst_law_three h.1] at e
  exact e

end Formalism.L2.Th1.B.Jets
end
end

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffEqZeroOfParallelogram
noncomputable section

namespace Formalism.L2.Th1.B

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3 swap2 DivAB equivalence_rules)
open Formalism.G.LogP (hs2 subst2_subst psubst_subst psubst_injective subst_zero')

section Alg

variable {K : Type} [Field K] [CharZero K] {ι : Type}

theorem subst_at_variable_one_eq (f : PowerSeries K) (x : Fin 2) {b : Fin 2 → MvPowerSeries ι K}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (at1 x f) = PowerSeries.subst (b x) f := by
  unfold at1
  rw [psubst_subst f (by simp) hb, MvPowerSeries.subst_X hb]

theorem constantCoeff_subst_two_variables (F : MvPowerSeries (Fin 2) K) (hF : MvPowerSeries.constantCoeff F = 0)
    (U V : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst ![U, V] F) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hs2 hU hV)
    (fun i => by fin_cases i <;> simpa) hF

theorem constantCoeff_subst_one_variable (g : PowerSeries K) (hg : PowerSeries.constantCoeff g = 0)
    (U : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst U g) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hU g hg

theorem cube_cob_subst (F : MvPowerSeries (Fin 2) K) (hF : MvPowerSeries.constantCoeff F = 0)
    (f : PowerSeries K) (U V : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) :
    MvPowerSeries.subst ![U, V] (cob F f) =
      PowerSeries.subst (MvPowerSeries.subst ![U, V] F) f - PowerSeries.subst U f -
        PowerSeries.subst V f := by
  have hb := hs2 hU hV
  unfold cob
  rw [← MvPowerSeries.coe_substAlgHom hb, map_sub, map_sub, MvPowerSeries.coe_substAlgHom hb,
    psubst_subst f hF hb, subst_at_variable_one_eq f 0 hb, subst_at_variable_one_eq f 1 hb]
  rfl

theorem cube_par_subst (F : MvPowerSeries (Fin 2) K) (hF : MvPowerSeries.constantCoeff F = 0)
    (i f : PowerSeries K) (hi : PowerSeries.constantCoeff i = 0) (U V : MvPowerSeries ι K)
    (hU : MvPowerSeries.constantCoeff U = 0) (hV : MvPowerSeries.constantCoeff V = 0) :
    MvPowerSeries.subst ![U, V] (par F i f) =
      PowerSeries.subst (MvPowerSeries.subst ![U, V] F) f +
        PowerSeries.subst (MvPowerSeries.subst ![U, PowerSeries.subst V i] F) f -
        2 * PowerSeries.subst U f - 2 * PowerSeries.subst V f := by
  have hb := hs2 hU hV
  have h1 : MvPowerSeries.constantCoeff (at1 (1 : Fin 2) i) = 0 := constantCoeff_subst_one_variable i hi _ (by simp)
  have hFI : MvPowerSeries.constantCoeff (FI F i) = 0 := constantCoeff_subst_two_variables F hF _ _ (by simp) h1
  unfold par
  rw [← MvPowerSeries.coe_substAlgHom hb, map_sub, map_sub, map_add (f := _), map_mul, map_mul, map_ofNat,
    MvPowerSeries.coe_substAlgHom hb, psubst_subst f hF hb, psubst_subst f hFI hb,
    subst_at_variable_one_eq f 0 hb, subst_at_variable_one_eq f 1 hb]
  unfold FI
  rw [subst2_subst F (by simp) h1 hb, MvPowerSeries.subst_X hb, subst_at_variable_one_eq i 1 hb]
  rfl

theorem two_mul_C_inv_two : (2 : MvPowerSeries ι K) * MvPowerSeries.C (2 : K)⁻¹ = 1 := by
  have e : (2 : MvPowerSeries ι K) = MvPowerSeries.C (2 : K) := (map_ofNat MvPowerSeries.C 2).symm
  rw [e, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]

end Alg

section Norm

variable {K : Type} [NormedField K] [CharZero K] {ι : Type}

theorem cube_log_add {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    (U V : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) :
    PowerSeries.subst (MvPowerSeries.subst ![U, V] F) l =
      PowerSeries.subst U l + PowerSeries.subst V l := by
  obtain ⟨hF, -, -, -, hc⟩ := h
  have e := cube_cob_subst F hF l U V hU hV
  rw [hc, subst_zero' (hs2 hU hV)] at e
  linear_combination -e

theorem cube_log_inv {l i : PowerSeries K} (hi : IsInv l i) (V : MvPowerSeries ι K)
    (hV : MvPowerSeries.constantCoeff V = 0) :
    PowerSeries.subst (PowerSeries.subst V i) l = -PowerSeries.subst V l := by
  have hVs : PowerSeries.HasSubst V := PowerSeries.HasSubst.of_constantCoeff_zero hV
  rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hi.1) hVs,
    hi.2.2, ← PowerSeries.coe_substAlgHom hVs, map_neg]

theorem cube_log_half {l hf : PowerSeries K} (hh : IsHalf l hf) (V : MvPowerSeries ι K)
    (hV : MvPowerSeries.constantCoeff V = 0) :
    2 * PowerSeries.subst (PowerSeries.subst V hf) l = PowerSeries.subst V l := by
  have hVs : PowerSeries.HasSubst V := PowerSeries.HasSubst.of_constantCoeff_zero hV
  rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hh.1) hVs,
    hh.2.2, PowerSeries.subst_mul hVs, PowerSeries.subst_C, ← mul_assoc, two_mul_C_inv_two, one_mul]

theorem cube_add_eq {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    (U V W : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) (hW : MvPowerSeries.constantCoeff W = 0)
    (e : PowerSeries.subst U l + PowerSeries.subst V l = PowerSeries.subst W l) :
    MvPowerSeries.subst ![U, V] F = W :=
  psubst_injective h.2.2.1 h.2.2.2.1 (constantCoeff_subst_two_variables F h.1 U V hU hV) hW
    ((cube_log_add h U V hU hV).trans e)

theorem cube_sub_eq {F : MvPowerSeries (Fin 2) K} {l i : PowerSeries K} (h : LawLog F l)
    (hi : IsInv l i) (U V W : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) (hW : MvPowerSeries.constantCoeff W = 0)
    (e : PowerSeries.subst U l - PowerSeries.subst V l = PowerSeries.subst W l) :
    MvPowerSeries.subst ![U, PowerSeries.subst V i] F = W :=
  cube_add_eq h U _ W hU (constantCoeff_subst_one_variable i hi.1 V hV) hW (by rw [cube_log_inv hi V hV, ← e]; ring)

theorem cube_identity {F : MvPowerSeries (Fin 2) K} {l i : PowerSeries K} (h : LawLog F l)
    (hi : IsInv l i) (f : PowerSeries K) (hf0 : PowerSeries.constantCoeff f = 0)
    (x0 x1 x2 A B C : MvPowerSeries ι K)
    (h0 : MvPowerSeries.constantCoeff x0 = 0) (h1 : MvPowerSeries.constantCoeff x1 = 0)
    (h2 : MvPowerSeries.constantCoeff x2 = 0) (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) (hC : MvPowerSeries.constantCoeff C = 0)
    (eA : PowerSeries.subst A l = PowerSeries.subst x0 l + PowerSeries.subst B l)
    (eB : 2 * PowerSeries.subst B l = PowerSeries.subst x1 l + PowerSeries.subst x2 l)
    (eC : 2 * PowerSeries.subst C l = PowerSeries.subst x1 l - PowerSeries.subst x2 l) :
    MvPowerSeries.subst ![A, B] (par F i f) - MvPowerSeries.subst ![A, C] (par F i f) +
        MvPowerSeries.subst ![B, C] (par F i f) - MvPowerSeries.subst ![B, B] (par F i f) =
      PowerSeries.subst (MvPowerSeries.subst ![MvPowerSeries.subst ![x0, x1] F, x2] F) f -
        PowerSeries.subst (MvPowerSeries.subst ![x0, x1] F) f -
        PowerSeries.subst (MvPowerSeries.subst ![x0, x2] F) f -
        PowerSeries.subst (MvPowerSeries.subst ![x1, x2] F) f +
        PowerSeries.subst x0 f + PowerSeries.subst x1 f + PowerSeries.subst x2 f := by
  have c01 := constantCoeff_subst_two_variables F h.1 x0 x1 h0 h1
  have c02 := constantCoeff_subst_two_variables F h.1 x0 x2 h0 h2
  have c12 := constantCoeff_subst_two_variables F h.1 x1 x2 h1 h2
  have c012 := constantCoeff_subst_two_variables F h.1 _ x2 c01 h2
  have l01 := cube_log_add h x0 x1 h0 h1
  have l02 := cube_log_add h x0 x2 h0 h2
  have l12 := cube_log_add h x1 x2 h1 h2
  have l012 := cube_log_add h _ x2 c01 h2
  have lz : PowerSeries.subst (0 : MvPowerSeries ι K) l = 0 :=
    PowerSeries.subst_zero_of_constantCoeff_zero h.2.2.1
  have fz : PowerSeries.subst (0 : MvPowerSeries ι K) f = 0 :=
    PowerSeries.subst_zero_of_constantCoeff_zero hf0
  have e1 : MvPowerSeries.subst ![A, B] F =
      MvPowerSeries.subst ![MvPowerSeries.subst ![x0, x1] F, x2] F :=
    cube_add_eq h A B _ hA hB c012 (by rw [l012, l01]; linear_combination eA + eB)
  have e2 : MvPowerSeries.subst ![A, PowerSeries.subst B i] F = x0 :=
    cube_sub_eq h hi A B _ hA hB h0 (by linear_combination eA)
  have hc := two_mul_C_inv_two (K := K) (ι := ι)
  have sBC : PowerSeries.subst B l + PowerSeries.subst C l = PowerSeries.subst x1 l := by
    linear_combination (MvPowerSeries.C (2 : K)⁻¹) * eB + (MvPowerSeries.C (2 : K)⁻¹) * eC -
      (PowerSeries.subst B l + PowerSeries.subst C l - PowerSeries.subst x1 l) * hc
  have dBC : PowerSeries.subst B l - PowerSeries.subst C l = PowerSeries.subst x2 l := by
    linear_combination (MvPowerSeries.C (2 : K)⁻¹) * eB - (MvPowerSeries.C (2 : K)⁻¹) * eC -
      (PowerSeries.subst B l - PowerSeries.subst C l - PowerSeries.subst x2 l) * hc
  have e3 : MvPowerSeries.subst ![A, C] F = MvPowerSeries.subst ![x0, x1] F :=
    cube_add_eq h A C _ hA hC c01 (by rw [l01]; linear_combination eA + sBC)
  have e4 : MvPowerSeries.subst ![A, PowerSeries.subst C i] F = MvPowerSeries.subst ![x0, x2] F :=
    cube_sub_eq h hi A C _ hA hC c02 (by rw [l02]; linear_combination eA + dBC)
  have e5 : MvPowerSeries.subst ![B, C] F = x1 := cube_add_eq h B C _ hB hC h1 sBC
  have e6 : MvPowerSeries.subst ![B, PowerSeries.subst C i] F = x2 :=
    cube_sub_eq h hi B C _ hB hC h2 dBC
  have e7 : MvPowerSeries.subst ![B, B] F = MvPowerSeries.subst ![x1, x2] F :=
    cube_add_eq h B B _ hB hB c12 (by rw [l12]; linear_combination eB)
  have e8 : MvPowerSeries.subst ![B, PowerSeries.subst B i] F = 0 :=
    cube_sub_eq h hi B B _ hB hB (by simp) (by rw [lz]; ring)
  rw [cube_par_subst F h.1 i f hi.1 A B hA hB, cube_par_subst F h.1 i f hi.1 A C hA hC,
    cube_par_subst F h.1 i f hi.1 B C hB hC, cube_par_subst F h.1 i f hi.1 B B hB hB,
    e1, e2, e3, e4, e5, e6, e7, e8, fz]
  ring

theorem parallelogram_coboundary_three_vars (F : MvPowerSeries (Fin 2) K) (hF : MvPowerSeries.constantCoeff F = 0)
    (f : PowerSeries K) :
    d1 F (cob F f) =
      PowerSeries.subst (MvPowerSeries.subst ![MvPowerSeries.subst
          ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] F,
          MvPowerSeries.X 2] F) f -
        PowerSeries.subst (MvPowerSeries.subst
          ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] F) f -
        PowerSeries.subst (MvPowerSeries.subst
          ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] F) f -
        PowerSeries.subst (MvPowerSeries.subst
          ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] F) f +
        PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) f +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K) f +
        PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) f := by
  unfold d1 in3
  rw [cube_cob_subst F hF f _ _ (constantCoeff_subst_two_variables F hF _ _ (by simp) (by simp)) (by simp),
    cube_cob_subst F hF f _ _ (by simp) (by simp), cube_cob_subst F hF f _ _ (by simp) (by simp)]
  ring

theorem cube_simeq_congr {f g f' g' : MvPowerSeries ι K} (h : f - g = f' - g')
    (hs : Simeq f g) : Simeq f' g' := by
  unfold Simeq at hs ⊢
  rw [← h]
  exact hs

theorem integral_mvPowerSeries_X (x : ι) : Integral (MvPowerSeries.X x : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem constantCoeff_eq_zero_of_parallelogram {F : MvPowerSeries (Fin 2) K} {l i f : PowerSeries K} (h : LawLog F l)
    (hi : IsInv l i) (hq : Simeq (par F i f) 0) : PowerSeries.constantCoeff f = 0 := by
  have h0 : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have e := Formalism.G.LogP.constantCoeff_subst_of_zero (par F i f)
    (b := ![(0 : MvPowerSeries (Fin 2) K), 0]) (fun j => by fin_cases j <;> simp)
  have hq0 : MvPowerSeries.constantCoeff (par F i f) = 0 := by simpa using hq.1
  have lz : PowerSeries.subst (0 : MvPowerSeries (Fin 2) K) l = 0 :=
    PowerSeries.subst_zero_of_constantCoeff_zero h.2.2.1
  rw [hq0, cube_par_subst F h.1 i f hi.1 0 0 h0 h0,
    cube_add_eq h 0 0 0 h0 h0 h0 (by rw [lz]; ring),
    cube_sub_eq h hi 0 0 0 h0 h0 h0 (by rw [lz]; ring),
    PowerSeries.subst_zero_eq_C_constantCoeff] at e
  have e' : PowerSeries.constantCoeff f + PowerSeries.constantCoeff f -
      2 * PowerSeries.constantCoeff f - 2 * PowerSeries.constantCoeff f = 0 := by
    have c2 : MvPowerSeries.constantCoeff (2 : MvPowerSeries (Fin 2) K) = 2 :=
      map_ofNat MvPowerSeries.constantCoeff 2
    simpa [c2] using e
  have e2 : (2 : K) * PowerSeries.constantCoeff f = 0 := by linear_combination -e'
  exact (mul_eq_zero.1 e2).resolve_left two_ne_zero

end Norm

section Ultra

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {ι : Type}

theorem integral_subst_two_variables {F : MvPowerSeries (Fin 2) K} (hF : Integral F) (U V : MvPowerSeries ι K)
    (hU : MvPowerSeries.constantCoeff U = 0) (hV : MvPowerSeries.constantCoeff V = 0)
    (iU : Integral U) (iV : Integral V) : Integral (MvPowerSeries.subst ![U, V] F) :=
  Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' (fun j => by fin_cases j <;> simpa)
    (fun j => by fin_cases j <;> simpa) hF

theorem integral_subst_one_variable {g : PowerSeries K} (hg : Integral (ι := Unit) g) (U : MvPowerSeries ι K)
    (hU : MvPowerSeries.constantCoeff U = 0) (iU : Integral U) :
    Integral (PowerSeries.subst U g) :=
  Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' (φ := fun _ : Unit => U) (fun _ => hU) (fun _ => iU) hg

theorem cube_simeq_subst2 {q : MvPowerSeries (Fin 2) K} (hq : Simeq q 0) (U V : MvPowerSeries ι K)
    (hU : MvPowerSeries.constantCoeff U = 0) (hV : MvPowerSeries.constantCoeff V = 0)
    (iU : Integral U) (iV : Integral V) : Simeq (MvPowerSeries.subst ![U, V] q) 0 := by
  have e := (equivalence_rules K (Fin 2)).2.2.2.2 ι q 0 ![U, V] (fun j => by fin_cases j <;> simpa)
    (fun j => by fin_cases j <;> simpa) hq
  rwa [subst_zero' (hs2 hU hV)] at e

end Ultra

theorem Cube_of (hH : HalfExists) (hI : SimeqInt) : Cube := by
  intro K _ _ _ F l i f h hi h2 hq
  obtain ⟨hf, hh⟩ := hH K F l h h2
  have hf0 := constantCoeff_eq_zero_of_parallelogram h hi hq
  have c0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) = 0 := by simp
  have c1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K) = 0 := by simp
  have c2 : MvPowerSeries.constantCoeff (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) = 0 := by simp
  have i0 := integral_mvPowerSeries_X (K := K) (0 : Fin 3)
  have i1 := integral_mvPowerSeries_X (K := K) (1 : Fin 3)
  have i2 := integral_mvPowerSeries_X (K := K) (2 : Fin 3)

  obtain ⟨S, hS⟩ : ∃ S, S = MvPowerSeries.subst
    ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] F := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K),
    PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) i] F := ⟨_, rfl⟩
  have cN := constantCoeff_subst_one_variable i hi.1 _ c2
  have iN := integral_subst_one_variable hi.2.1 _ c2 i2
  have cS : MvPowerSeries.constantCoeff S = 0 := hS ▸ constantCoeff_subst_two_variables F h.1 _ _ c1 c2
  have cD : MvPowerSeries.constantCoeff D = 0 := hD ▸ constantCoeff_subst_two_variables F h.1 _ _ c1 cN
  have iS : Integral S := hS ▸ integral_subst_two_variables h.2.1 _ _ c1 c2 i1 i2
  have iD : Integral D := hD ▸ integral_subst_two_variables h.2.1 _ _ c1 cN i1 iN
  have lS : PowerSeries.subst S l = PowerSeries.subst (MvPowerSeries.X 1) l +
      PowerSeries.subst (MvPowerSeries.X 2) l := hS ▸ cube_log_add h _ _ c1 c2
  have lD : PowerSeries.subst D l = PowerSeries.subst (MvPowerSeries.X 1) l -
      PowerSeries.subst (MvPowerSeries.X 2) l := by
    rw [hD, cube_log_add h _ _ c1 cN, cube_log_inv hi _ c2]; ring
  have cB := constantCoeff_subst_one_variable hf hh.1 S cS
  have cC := constantCoeff_subst_one_variable hf hh.1 D cD
  have iB := integral_subst_one_variable hh.2.1 S cS iS
  have iC := integral_subst_one_variable hh.2.1 D cD iD
  have cA := constantCoeff_subst_two_variables F h.1 _ _ c0 cB
  have iA := integral_subst_two_variables h.2.1 _ _ c0 cB i0 iB
  have key := cube_identity h hi f hf0 (MvPowerSeries.X 0) (MvPowerSeries.X 1) (MvPowerSeries.X 2)
    _ _ _ c0 c1 c2 cA cB cC (cube_log_add h _ _ c0 cB)
    ((cube_log_half hh S cS).trans lS) ((cube_log_half hh D cD).trans lD)
  rw [parallelogram_coboundary_three_vars F h.1 f, ← key]
  have qAB := cube_simeq_subst2 hq _ _ cA cB iA iB
  have qAC := cube_simeq_subst2 hq _ _ cA cC iA iC
  have qBC := cube_simeq_subst2 hq _ _ cB cC iB iC
  have qBB := cube_simeq_subst2 hq _ _ cB cB iB iB
  have s1 := (hI K (Fin 3) _ _ _ _ qAB qAC).1
  have s2 := (equivalence_rules K (Fin 3)).2.2.2.1 _ _ _ _ s1 qBC
  have s3 := (hI K (Fin 3) _ _ _ _ s2 qBB).1
  exact cube_simeq_congr (by ring) s3

end Formalism.L2.Th1.B
end
end

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.SimeqPadicIntegers
noncomputable section

namespace Formalism.L2.Th1.B.Sim

open Finset
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.HermitianLattices.ExpSeriesBivariate (InLam)
open Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition (inLam_zero inLam_add inLam_neg inLam_nsmul integral_of_mul_eq_one)

variable {K ι : Type} [NormedField K] [CharZero K]

theorem simeq_iff (f g : MvPowerSeries ι K) : Simeq f g ↔ InLam (f - g) := Iff.rfl

theorem inLam_zsmul [IsUltrametricDist K] {f : MvPowerSeries ι K} (hf : InLam f) (n : ℤ) :
    InLam (n • f) := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [natCast_zsmul]; exact inLam_nsmul hf m
  · rw [neg_zsmul, natCast_zsmul]; exact inLam_neg (inLam_nsmul hf m)

theorem inLam_fLog {g : MvPowerSeries ι K} (hg0 : MvPowerSeries.constantCoeff g = 1)
    (hg : Integral g) : InLam (fLog g) := by
  refine ⟨constantCoeff_fLog hg0, ?_⟩
  have e : fExp (fLog g) = g := fExp_fLog hg0
  have h : Integral (fExp (fLog g)) := by rw [e]; exact hg
  exact h

end Formalism.L2.Th1.B.Sim

namespace Formalism.L2.Th1.B.Sim

open Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition (inLam_add inLam_neg)

theorem simeq_integral_series : SimeqInt := by
  intro K ι _ _ _ f g f' g' h h'
  rw [simeq_iff] at h h'
  refine ⟨?_, ?_, fun n => ?_⟩
  · rw [simeq_iff]
    have e : f - f' - (g - g') = (f - g) + -(f' - g') := by ring
    rw [e]; exact inLam_add h (inLam_neg h')
  · rw [simeq_iff]
    have e : -f - -g = -(f - g) := by ring
    rw [e]; exact inLam_neg h
  · rw [simeq_iff]
    have e : (n : MvPowerSeries ι K) * f - n * g = n • (f - g) := by
      rw [zsmul_eq_mul]; ring
    rw [e]; exact inLam_zsmul h n

theorem simeq_formal_log : SimeqLog := by
  intro K ι _ _ _ g hg0 hg
  have h := inLam_fLog hg0 hg
  refine ⟨?_, ?_⟩
  · rw [simeq_iff, sub_zero]; exact h
  · rw [simeq_iff, sub_zero]; exact inLam_neg h

end Formalism.L2.Th1.B.Sim
end
end

namespace Formalism.L2.Th1.B

theorem halfExists : HalfExists := by
  exact formal_halving_exists
theorem cobRules : CobRules := by
  exact coboundary_rules_hold
theorem simeqInt : SimeqInt := by
  exact Sim.simeq_integral_series
theorem simeqLog : SimeqLog := by
  exact Sim.simeq_formal_log
theorem phODef : PhODef := by
  exact Ph.logSigmaPullbackSpec
theorem phEDef : PhEDef := by
  exact Ph.logSigmaOnePullbackSpec
theorem wIntegral : WIntegral := by
  exact ParE.weierstrass_series_integral
theorem parO : ParO := by
  exact ParO.ParO_of addSgStar phODef simeqLog
theorem diffPh : DiffPh := by
  exact ParO.DiffPh_of sigma1Sq simeqLog
theorem cube : Cube := by
  exact Cube_of halfExists simeqInt
theorem jetsThree : JetsThree := by
  exact Jets.jets_three_variables_holds

theorem f1O : LogSigmaPullbackCocycle := by
  intro K _ _ _ g2 g3 s2 c0 P l i ep F hP hF hi hC h2
  have hl := hF.2.2
  have h0 := (phODef K s2 P l hl.1 hl.2.1).1
  obtain ⟨hdiv, hsw⟩ := cobRules K F l (phO s2 P l) hF h0
  have hd := cube K F l i (phO s2 P l) hF hi h2 (parO K g2 g3 s2 c0 P l i ep F hP hF hi hC)
  exact ⟨hdiv, hsw, hd, by rw [hsw]; exact hd⟩

end Formalism.L2.Th1.B
