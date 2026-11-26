module

public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.CompInv
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.FlowThird
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.LogExp
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.FormalGroupEqWSeries

@[expose] public section

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.FlowTrans
universe u

namespace Formalism.L2.Th1.A

variable {A : Type u} [CommRing A]

theorem IsDer.exists_derivation {D : A → A} (h : IsDer D) :
    ∃ d : Derivation ℤ A A, ∀ a, D a = d a := by
  refine ⟨Derivation.mk' (AddMonoidHom.mk' D h.1).toIntLinearMap (fun a b => ?_), fun a => rfl⟩
  simp only [AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.mk'_apply, smul_eq_mul]
  exact h.2 a b

theorem der_mul (d : Derivation ℤ A A) (a b : A) : d (a * b) = a * d b + b * d a := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]

theorem der_sq (d : Derivation ℤ A A) (a : A) : d (a ^ 2) = 2 * a * d a := by
  rw [pow_two, der_mul]
  ring

theorem der_inv (d : Derivation ℤ A A) {t s : A} (ht : t * s = 1) : d t = -t ^ 2 * d s := by
  have h0 : t * d s + s * d t = 0 := by rw [← der_mul, ht, Derivation.map_one_eq_zero]
  have h1 : d t = t * s * d t := by rw [ht, one_mul]
  rw [h1]
  linear_combination t * h0

theorem chord_rel {a₁ a₂ a₃ a₄ a₆ x y xP yP t L : A}
    (hE : y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hEP : yP ^ 2 + a₁ * xP * yP + a₃ * yP = xP ^ 3 + a₂ * xP ^ 2 + a₄ * xP + a₆)
    (ht : t * (x - xP) = 1) (hL : L * (x - xP) = y - yP) :
    (a₄ - 2 * L * (y - L * x) - a₁ * (y - L * x) - a₃ * L)
        - (x * xP + (x + xP) * (L ^ 2 + a₁ * L - a₂ - x - xP)) = 0 ∧
      (a₆ - (y - L * x) ^ 2 - a₃ * (y - L * x))
        + x * xP * (L ^ 2 + a₁ * L - a₂ - x - xP) = 0 := by
  have hα : (a₄ - 2 * L * (y - L * x) - a₁ * (y - L * x) - a₃ * L)
      - (x * xP + (x + xP) * (L ^ 2 + a₁ * L - a₂ - x - xP)) = 0 := by
    linear_combination (-((a₄ - 2 * L * (y - L * x) - a₁ * (y - L * x) - a₃ * L)
      - (x * xP + (x + xP) * (L ^ 2 + a₁ * L - a₂ - x - xP)))) * ht - t * hE + t * hEP
      - t * (L * xP + (y - L * x) + yP + a₁ * xP + a₃) * hL
  refine ⟨hα, ?_⟩
  linear_combination (-1 : A) * hE - x * hα

theorem der_slope (W : WeierstrassCurve A) (d : Derivation ℤ A A) {x y xP yP t : A}
    (hE : W.toAffine.Equation x y) (hx : d x = 2 * y + W.a₁ * x + W.a₃)
    (hy : d y = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
    (hEP : W.toAffine.Equation xP yP) (hxP : d xP = 0) (hyP : d yP = 0)
    (ht : t * (x - xP) = 1) :
    d ((y - yP) * t) = x - W.toAffine.addX x xP ((y - yP) * t) := by
  have hE' := (WeierstrassCurve.Affine.equation_iff x y).1 hE
  have hEP' := (WeierstrassCurve.Affine.equation_iff xP yP).1 hEP
  have hL : ((y - yP) * t) * (x - xP) = y - yP := by linear_combination (y - yP) * ht
  obtain ⟨hα, -⟩ := chord_rel hE' hEP' ht hL
  have hdt : d t = -t ^ 2 * d (x - xP) := der_inv d ht
  have hdxs : d (x - xP) = d x := by rw [map_sub, hxP, sub_zero]
  rw [der_mul, map_sub, hyP, sub_zero, hdt, hdxs, hx, hy]
  simp only [WeierstrassCurve.Affine.addX]
  linear_combination (x - (((y - yP) * t) ^ 2 + W.a₁ * ((y - yP) * t) - W.a₂ - x - xP)) * ht + t * hα

theorem flowTranslation : FlowTranslate.{u} := by
  intro A _ W D x y xP yP t hD hC hF hEP hxP hyP ht
  obtain ⟨d, hd⟩ := hD.exists_derivation
  obtain ⟨hE, hx, hy⟩ := hF
  obtain ⟨c1, c2, c3, c4, c6⟩ := hC
  rw [hd] at hx hy hxP hyP c1 c2 c3 c4 c6
  have hDL := der_slope W d hE hx hy hEP hxP hyP ht
  have hE' := (WeierstrassCurve.Affine.equation_iff x y).1 hE
  have hEP' := (WeierstrassCurve.Affine.equation_iff xP yP).1 hEP
  have hL : ((y - yP) * t) * (x - xP) = y - yP := by linear_combination (y - yP) * ht
  obtain ⟨hα, hβ⟩ := chord_rel hE' hEP' ht hL
  set L := (y - yP) * t with hLdef
  have hDL' : d L = x - (L ^ 2 + W.a₁ * L - W.a₂ - x - xP) := hDL
  refine ⟨?_, ?_, ?_⟩
  · rw [WeierstrassCurve.Affine.equation_iff]
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX]
    linear_combination (-1 : A) * hβ - (L ^ 2 + W.a₁ * L - W.a₂ - x - xP) * hα
  · rw [hd]
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX, map_sub, map_add, der_sq, der_mul, c1, c2, hx, hxP, hDL']
    ring
  · rw [hd]
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX, map_neg, map_sub, map_add, der_sq, der_mul, c1, c2, c3, hx, hy, hxP, hDL']
    linear_combination (-2 : A) * hα

theorem flowLogDerivative : FlowLogDeriv.{u} := by
  intro A _ W D x y xP yP t hD hC hF hEP hxP hyP ht
  obtain ⟨d, hd⟩ := hD.exists_derivation
  obtain ⟨hE, hx, hy⟩ := hF
  obtain ⟨c1, c2, c3, c4, c6⟩ := hC
  rw [hd] at hx hy hxP hyP c1 c2 c3 c4 c6
  have hEQ : W.toAffine.Equation xP (W.toAffine.negY xP yP) :=
    (WeierstrassCurve.Affine.equation_neg xP yP).2 hEP
  have hyQ : d (W.toAffine.negY xP yP) = 0 := by
    simp only [WeierstrassCurve.Affine.negY, map_sub, map_neg, der_mul, hyP, hxP, c1, c3]
    ring
  have hP := der_slope W d hE hx hy hEP hxP hyP ht
  have hQ := der_slope W d hE hx hy hEQ hxP hyQ ht

  have hsplit : t * (2 * y + W.a₁ * x + W.a₃) =
      (y - yP) * t + (y - W.toAffine.negY xP yP) * t + W.a₁ * (t * (x - xP)) := by
    simp only [WeierstrassCurve.Affine.negY]
    ring
  simp only [hd]
  rw [hx, hsplit, map_add (f := _), map_add (f := _), hP, hQ, ht, mul_one, c1]
  ring

end Formalism.L2.Th1.A
end

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.ToLTDenMulInv
open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

namespace Plus

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (xP yP : R)

theorem tDen_cc : constantCoeff (tDen W xP) = 1 := by
  simp [tDen, xS, PowerSeries.constantCoeff_invOfUnit]

theorem tDen_mul_inv : tDen W xP * invOfUnit (tDen W xP) 1 = 1 := PowerSeries.mul_invOfUnit _ _ (by simpa using tDen_cc W xP)

theorem inv_cc : constantCoeff (invOfUnit (tDen W xP) 1) = 1 := by
  simp [PowerSeries.constantCoeff_invOfUnit]

theorem toL_tDen_mul_inv : toL (tDen W xP) * toL (invOfUnit (tDen W xP) 1) = 1 := by
  rw [← map_mul, tDen_mul_inv, map_one]

theorem toL_X_mul : (toL X : LaurentSeries R) * uPow (-1) = 1 := by
  simp [uPow, HahnSeries.ofPowerSeries_X, HahnSeries.single_mul_single, HahnSeries.single_zero_one]

theorem uPow_neg_two : (uPow (-2) : LaurentSeries R) = uPow (-1) ^ 2 := by
  simp only [uPow]
  rw [sq, HahnSeries.single_mul_single]
  norm_num

theorem uPow_neg_three : (uPow (-3) : LaurentSeries R) = uPow (-1) ^ 3 := by
  simp only [uPow]
  rw [pow_three, HahnSeries.single_mul_single, HahnSeries.single_mul_single]
  norm_num

theorem xL_eq : xL W = uPow (-1) ^ 2 * toL (xS W) := by
  rw [xL, uPow_neg_two]

theorem yL_eq : yL W = uPow (-1) ^ 3 * toL (yS W) := by
  rw [yL, uPow_neg_three]

theorem toL_tDen : toL (tDen W xP) = toL (xS W) - HahnSeries.C xP * toL X ^ 2 := by
  simp only [tDen, map_sub, map_mul, map_pow, HahnSeries.ofPowerSeries_C]

theorem toL_tS : toL (tS W xP) = toL X ^ 2 * toL (invOfUnit (tDen W xP) 1) := by
  simp only [tS, map_mul, map_pow]

theorem xL_sub : xL W - HahnSeries.C xP = uPow (-1) ^ 2 * toL (tDen W xP) := by
  rw [toL_tDen, xL_eq, mul_sub]
  have h : (uPow (-1) : LaurentSeries R) ^ 2 * (HahnSeries.C xP * toL X ^ 2) = HahnSeries.C xP := by
    rw [mul_left_comm, ← mul_pow, mul_comm (uPow (-1) : LaurentSeries R) (toL X), toL_X_mul,
      one_pow, mul_one]
  rw [h]

theorem yL_sub : yL W - HahnSeries.C yP = uPow (-1) ^ 3 * toL (yS W - C yP * X ^ 3) := by
  rw [yL_eq, map_sub, map_mul, map_pow, HahnSeries.ofPowerSeries_C, mul_sub]
  have h : (uPow (-1) : LaurentSeries R) ^ 3 * (HahnSeries.C yP * toL X ^ 3) = HahnSeries.C yP := by
    rw [mul_left_comm, ← mul_pow, mul_comm (uPow (-1) : LaurentSeries R) (toL X), toL_X_mul,
      one_pow, mul_one]
  rw [h]

theorem toL_tS_mul : toL (tS W xP) * (xL W - HahnSeries.C xP) = 1 := by
  rw [xL_sub, toL_tS]
  calc (toL X : LaurentSeries R) ^ 2 * toL (invOfUnit (tDen W xP) 1) * (uPow (-1) ^ 2 * toL (tDen W xP))
      = ((toL X : LaurentSeries R) * uPow (-1)) ^ 2
          * (toL (tDen W xP) * toL (invOfUnit (tDen W xP) 1)) := by ring
    _ = 1 := by rw [toL_X_mul, toL_tDen_mul_inv, one_pow, one_mul]

theorem coeff_two_tS : coeff 2 (tS W xP) = 1 := by
  simp [tS, PowerSeries.coeff_X_pow_mul', inv_cc]

theorem toL_nS : toL (nS W xP yP) =
    HahnSeries.C (W.a₄ - W.a₁ * yP + 2 * W.a₂ * xP + 3 * xP ^ 2) * toL X * toL (xS W)
      - HahnSeries.C (2 * yP + W.a₁ * xP + W.a₃) * toL (yS W)
      + HahnSeries.C (2 * W.a₆ + W.a₄ * xP - W.a₃ * yP - xP ^ 3) * toL X ^ 3 := by
  simp only [nS, map_add (f := _), map_sub, map_mul, map_pow, HahnSeries.ofPowerSeries_C]

theorem toL_xPlus : toL (xPlus W xP yP) = HahnSeries.C xP
    + toL X * toL (nS W xP yP) * toL (invOfUnit (tDen W xP) 1) ^ 2 := by
  simp only [xPlus, map_add (f := _), map_mul, map_pow, HahnSeries.ofPowerSeries_C]

theorem toL_yPlus : toL (yPlus W xP yP) =
    -(toL (yS W - C yP * X ^ 3) * toL (nS W xP yP) * toL (invOfUnit (tDen W xP) 1) ^ 3)
      - HahnSeries.C yP - HahnSeries.C W.a₁ * toL (xPlus W xP yP) - HahnSeries.C W.a₃ := by
  simp only [yPlus, map_add (f := _), map_sub, map_neg, map_mul, map_pow, HahnSeries.ofPowerSeries_C]

theorem inv_subst (hI : ISerSpec.{u}) :
    (invOfUnit (tDen W xP) 1).subst (iSer W) = iDen W ^ 2 * invOfUnit (tDen W xP) 1 := by
  obtain ⟨hs0, -, -, -, hx, -, -, -⟩ := hI R W
  have hS : HasSubst (iSer W) := HasSubst.of_constantCoeff_zero' hs0
  have hw0 : constantCoeff (wSer W) = 0 := (Formalism.ELL.wSeriesUnique R W).choose_spec.1.1
  have hB : iDen W * invOfUnit (iDen W) (-1) = 1 :=
    PowerSeries.mul_invOfUnit _ _ (by simp [iDen, hw0])
  have hC := tDen_mul_inv W xP
  have hCs : (C xP : R⟦X⟧).subst (iSer W) = C xP := by
    rw [← PowerSeries.coe_substAlgHom hS]
    exact (PowerSeries.substAlgHom hS).commutes xP
  have hT : (tDen W xP).subst (iSer W) = invOfUnit (iDen W) (-1) ^ 2 * tDen W xP := by
    rw [tDen, ← PowerSeries.coe_substAlgHom hS, map_sub, map_mul, map_pow, PowerSeries.coe_substAlgHom,
      PowerSeries.subst_X hS, hCs, hx, iSer]
    ring
  have hA : (tDen W xP).subst (iSer W) * (invOfUnit (tDen W xP) 1).subst (iSer W) = 1 := by
    rw [← PowerSeries.coe_substAlgHom hS, ← map_mul, hC, map_one]
  rw [hT] at hA
  linear_combination (-((invOfUnit (tDen W xP) 1).subst (iSer W) * (iDen W * invOfUnit (iDen W) (-1) + 1) * tDen W xP * invOfUnit (tDen W xP) 1)) * hB
    - (invOfUnit (tDen W xP) 1).subst (iSer W) * hC + iDen W ^ 2 * invOfUnit (tDen W xP) 1 * hA

theorem tS_subst (hI : ISerSpec.{u}) : (tS W xP).subst (iSer W) = tS W xP := by
  obtain ⟨hs0, -, -, -, -, -, -, -⟩ := hI R W
  have hS : HasSubst (iSer W) := HasSubst.of_constantCoeff_zero' hs0
  have hw0 : constantCoeff (wSer W) = 0 := (Formalism.ELL.wSeriesUnique R W).choose_spec.1.1
  have hB : iDen W * invOfUnit (iDen W) (-1) = 1 :=
    PowerSeries.mul_invOfUnit _ _ (by simp [iDen, hw0])
  rw [tS, ← PowerSeries.coe_substAlgHom hS, map_mul, map_pow, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X hS, inv_subst W xP hI, iSer]
  linear_combination (X ^ 2 * invOfUnit (tDen W xP) 1 * (iDen W * invOfUnit (iDen W) (-1) + 1)) * hB

theorem equation_C {xP yP : R} (hP : W.toAffine.Equation xP yP) :
    (curveL W).toAffine.Equation (HahnSeries.C xP) (HahnSeries.C yP) := by
  rw [WeierstrassCurve.Affine.equation_iff] at hP ⊢
  have h := congrArg (HahnSeries.C : R →+* LaurentSeries R) hP
  simpa using h

theorem chord (hFL : FlowL.{u}) {xP yP : R} (hP : W.toAffine.Equation xP yP) :
    toL (xPlus W xP yP) = (curveL W).toAffine.addX (xL W) (HahnSeries.C xP) (slopeL W xP yP) ∧
    toL (yPlus W xP yP)
      = (curveL W).toAffine.addY (xL W) (HahnSeries.C xP) (yL W) (slopeL W xP yP) := by
  obtain ⟨hX, hY⟩ := chordFormula _ (curveL W) (xL W) (yL W) (HahnSeries.C xP)
    (HahnSeries.C yP) (toL (tS W xP)) (hFL R W).1.1 (equation_C W hP) (toL_tS_mul W xP)
  have h : (toL X : LaurentSeries R) * uPow (-1) = 1 := toL_X_mul
  have hx : toL (xPlus W xP yP)
      = (curveL W).toAffine.addX (xL W) (HahnSeries.C xP) (slopeL W xP yP) := by
    rw [slopeL, hX, toL_xPlus, toL_nS, toL_tS, xL_eq, yL_eq]
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_add, map_sub, map_mul, map_pow,
      map_ofNat]
    generalize toL (invOfUnit (tDen W xP) 1) = v
    generalize toL (xS W) = xs
    generalize toL (yS W) = ys
    linear_combination (-(HahnSeries.C W.a₄ - HahnSeries.C W.a₁ * HahnSeries.C yP
        + 2 * HahnSeries.C W.a₂ * HahnSeries.C xP + 3 * HahnSeries.C xP ^ 2) * xs * v ^ 2
          * toL X ^ 2 * (toL X * uPow (-1) + 1)
      + (2 * HahnSeries.C yP + HahnSeries.C W.a₁ * HahnSeries.C xP + HahnSeries.C W.a₃) * ys
          * v ^ 2 * toL X * ((toL X * uPow (-1)) ^ 2 + toL X * uPow (-1) + 1)) * h
  refine ⟨hx, ?_⟩
  rw [slopeL] at hx ⊢
  rw [hY, ← hx, toL_yPlus, yL_sub, toL_tS]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
  rw [toL_xPlus]
  linear_combination (toL (yS W - C yP * X ^ 3) * toL (nS W xP yP)
    * toL (invOfUnit (tDen W xP) 1) ^ 3 * ((toL X * uPow (-1)) ^ 2 + toL X * uPow (-1) + 1)) * h

theorem isFlow_of_toL (hDL : DLSpec.{u}) {a b : R⟦X⟧}
    (h : IsFlow (curveL W) (DL W) (toL a) (toL b)) : IsFlow (curveS W) (D W) a b := by
  obtain ⟨hE, h1, h2⟩ := h
  obtain ⟨-, -, -, hD⟩ := hDL R W
  have inj : Function.Injective (toL : R⟦X⟧ →+* LaurentSeries R) := HahnSeries.ofPowerSeries_injective
  refine ⟨?_, ?_, ?_⟩
  · rw [WeierstrassCurve.Affine.equation_iff] at hE ⊢
    apply inj
    simpa using hE
  · apply inj
    rw [← hD]
    simpa [map_ofNat toL 2] using h1
  · apply inj
    rw [← hD]
    simpa [map_ofNat toL 2, map_ofNat toL 3] using h2

theorem nS_cc : constantCoeff (nS W xP yP) = 2 * yP + W.a₁ * xP + W.a₃ := by
  simp [nS, yS, xS, PowerSeries.constantCoeff_invOfUnit]

theorem xPlus_cc : constantCoeff (xPlus W xP yP) = xP := by
  simp [xPlus]

theorem yPlus_cc : constantCoeff (yPlus W xP yP) = yP := by
  simp [yPlus, yS, xS, xPlus_cc, nS_cc, PowerSeries.constantCoeff_invOfUnit] <;> ring

section Map

variable {S : Type v} [CommRing S] (φ : R →+* S)

theorem map_tDen : PowerSeries.map φ (tDen W xP) = tDen (W.map φ) (φ xP) := by
  simp only [tDen, map_sub, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X, CurveSer.map_xS]

theorem map_inv : PowerSeries.map φ (invOfUnit (tDen W xP) 1)
    = invOfUnit (tDen (W.map φ) (φ xP)) 1 := by
  have h1 : tDen (W.map φ) (φ xP) * PowerSeries.map φ (invOfUnit (tDen W xP) 1) = 1 := by
    rw [← Plus.map_tDen W xP φ, ← map_mul, tDen_mul_inv, map_one]
  have h2 := tDen_mul_inv (W.map φ) (φ xP)
  calc PowerSeries.map φ (invOfUnit (tDen W xP) 1)
      = (invOfUnit (tDen (W.map φ) (φ xP)) 1 * tDen (W.map φ) (φ xP))
          * PowerSeries.map φ (invOfUnit (tDen W xP) 1) := by
        rw [mul_comm (invOfUnit (tDen (W.map φ) (φ xP)) 1) (tDen (W.map φ) (φ xP)), h2, one_mul]
    _ = invOfUnit (tDen (W.map φ) (φ xP)) 1 := by rw [mul_assoc, h1, mul_one]

theorem map_tS : PowerSeries.map φ (tS W xP) = tS (W.map φ) (φ xP) := by
  simp only [tS, map_mul, map_pow, PowerSeries.map_X, Plus.map_inv W xP φ]

theorem map_nS : PowerSeries.map φ (nS W xP yP) = nS (W.map φ) (φ xP) (φ yP) := by
  simp only [nS, yS, map_add (f := _), map_sub, map_mul, map_neg, map_pow, PowerSeries.map_C, PowerSeries.map_X,
    CurveSer.map_xS, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_ofNat]

theorem map_xPlus : PowerSeries.map φ (xPlus W xP yP) = xPlus (W.map φ) (φ xP) (φ yP) := by
  simp only [xPlus, map_add (f := _), map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X,
    Plus.map_nS W xP yP φ, Plus.map_inv W xP φ]

theorem map_yPlus : PowerSeries.map φ (yPlus W xP yP) = yPlus (W.map φ) (φ xP) (φ yP) := by
  simp only [yPlus, yS, map_add (f := _), map_sub, map_neg, map_mul, map_pow, PowerSeries.map_C,
    PowerSeries.map_X, CurveSer.map_xS, Plus.map_nS W xP yP φ, Plus.map_inv W xP φ,
    Plus.map_xPlus W xP yP φ, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]

end Map

end Plus

open Plus

theorem tSpec_of (hI : ISerSpec.{u}) : TSpec.{u} := by
  intro R _ W xP
  exact ⟨Plus.tDen_cc W xP, Plus.tDen_mul_inv W xP, Plus.toL_tS_mul W xP, Plus.coeff_two_tS W xP,
    ⟨invOfUnit (tDen W xP) 1, rfl⟩, Plus.tS_subst W xP hI⟩

theorem plusChord_of (hFL : FlowL.{u}) : PlusChord.{u} := by
  intro R _ W xP yP hP
  exact Plus.chord W hFL hP

theorem plusFlow_of (hDL : DLSpec.{u}) (hFL : FlowL.{u}) : PlusFlow.{u} := by
  intro R _ W xP yP hP
  obtain ⟨hDer, hConst, hC, -⟩ := hDL R W
  obtain ⟨hx, hy⟩ := chord W hFL hP
  have h := flowTranslation _ (curveL W) (DL W) (xL W) (yL W) (HahnSeries.C xP)
    (HahnSeries.C yP) (toL (tS W xP)) hDer hConst (hFL R W).1 (equation_C W hP) (hC xP) (hC yP)
    (toL_tS_mul W xP)
  rw [slopeL] at hx hy
  rw [← hx, ← hy] at h
  exact ⟨isFlow_of_toL W hDL h, xPlus_cc W xP yP, yPlus_cc W xP yP⟩

theorem addition_map : PlusMap.{u, v} := by
  intro R S _ _ φ W xP yP
  exact ⟨Plus.map_tS W xP φ, Plus.map_xPlus W xP yP φ, Plus.map_yPlus W xP yP φ⟩

end Formalism.L2.Th1.A
end
end

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.ConstCurveDL
open PowerSeries

universe u

noncomputable section

namespace Formalism.L2.Th1.A

namespace Wp

variable {K : Type u} [Field K]

def sig {e : K⟦X⟧} (he : HasSubst e) : K⟦X⟧ →+* LaurentSeries K :=
  toL.comp (substAlgHom he : K⟦X⟧ →ₐ[K] K⟦X⟧).toRingHom

theorem sig_apply {e : K⟦X⟧} (he : HasSubst e) (f : K⟦X⟧) : sig he f = toL (f.subst e) := by
  simp [sig, PowerSeries.coe_substAlgHom]

theorem sig_X {e : K⟦X⟧} (he : HasSubst e) : sig he X = toL e := by
  rw [sig_apply, PowerSeries.subst_X he]

theorem sig_C {e : K⟦X⟧} (he : HasSubst e) (r : K) : sig he (C r) = HahnSeries.C r := by
  have h : (C r : K⟦X⟧).subst e = C r := by
    rw [← PowerSeries.coe_substAlgHom he]
    exact (PowerSeries.substAlgHom he).commutes r
  rw [sig_apply, h, HahnSeries.ofPowerSeries_C]

theorem isDer_dL' : IsDer (dL : LaurentSeries K → LaurentSeries K) := isDer_dL

theorem constCurve_dL (W : WeierstrassCurve K) : ConstCurve dL (curveL W) := by
  have h : ∀ c : K, dL (HahnSeries.C c : LaurentSeries K) = 0 := by
    intro c
    ext n
    simp [dL, HahnSeries.C_apply, HahnSeries.coeff_single]
  exact ⟨h _, h _, h _, h _, h _⟩

variable (W : WeierstrassCurve K) {e : K⟦X⟧} (he : HasSubst e)

theorem fwAt_sig : fwAt (curveL W) (sig he X) (sig he (wSer W)) = sig he (fw W) := by
  simp only [fwAt, fw, map_sub, map_mul, map_pow, map_one, map_ofNat, sig_C,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]

theorem fuAt_sig : fuAt (curveL W) (sig he X) (sig he (wSer W)) = sig he (fu W) := by
  simp only [fuAt, fu, map_add (f := _), map_mul, map_pow, map_ofNat, sig_C,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄]

theorem wEq_sig : WEq (curveL W) (sig he X) (sig he (wSer W)) := by
  have hw : wSer W = X ^ 3 + C W.a₁ * X * wSer W + C W.a₂ * X ^ 2 * wSer W + C W.a₃ * wSer W ^ 2
      + C W.a₄ * X * wSer W ^ 2 + C W.a₆ * wSer W ^ 3 :=
    (Formalism.ELL.wSeriesUnique K W).choose_spec.1.2
  have h := congrArg (sig he) hw
  simp only [map_add (f := _), map_mul, map_pow, sig_C] at h
  simp only [WEq, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  exact h

theorem isFlowUW_sig (hc : ∀ f : K⟦X⟧, derivative (f.subst e) = (D W f).subst e) :
    IsFlowUW (curveL W) dL (sig he X) (sig he (wSer W)) := by
  have hw : wSer W = X ^ 3 + C W.a₁ * X * wSer W + C W.a₂ * X ^ 2 * wSer W + C W.a₃ * wSer W ^ 2
      + C W.a₄ * X * wSer W ^ 2 + C W.a₆ * wSer W ^ 3 :=
    (Formalism.ELL.wSeriesUnique K W).choose_spec.1.2
  have hd := congrArg PowerSeries.derivative hw
  simp only [map_add (f := _), Derivation.leibniz, Derivation.leibniz_pow, PowerSeries.derivative_C,
    PowerSeries.derivative_X, smul_eq_mul, nsmul_eq_mul] at hd
  have hDw : D W (wSer W) = fu W := by
    rw [D, Derivation.smul_apply, smul_eq_mul, fw, fu]
    linear_combination hd
  have hDX : D W X = fw W := by
    rw [D, Derivation.smul_apply, smul_eq_mul, PowerSeries.derivative_X, mul_one]
  refine ⟨wEq_sig W he, ?_, ?_⟩
  · have h2 : dL (sig he X) = sig he (fw W) := by
      have h1 := hc X
      rw [PowerSeries.subst_X he, hDX] at h1
      rw [sig_X, sig_apply, dL_toL, h1]
    rw [h2, fwAt_sig]
  · have h2 : dL (sig he (wSer W)) = sig he (fu W) := by
      rw [sig_apply, sig_apply, dL_toL, hc (wSer W), hDw]
    rw [h2, fuAt_sig]

theorem inv_mul_sig (hne : toL e ≠ 0) :
    (toL e)⁻¹ ^ 3 * sig he (xS W) * sig he (wSer W) = 1 := by
  have h1 : sig he (wU W) * sig he (xS W) = 1 := by rw [← map_mul, CurveSer.wU_mul_xS, map_one]
  have h2 : (toL e)⁻¹ * toL e = 1 := inv_mul_cancel₀ hne
  rw [CurveSer.wSer_eq, map_mul, map_pow, sig_X]
  calc (toL e)⁻¹ ^ 3 * sig he (xS W) * (toL e ^ 3 * sig he (wU W))
      = ((toL e)⁻¹ * toL e) ^ 3 * (sig he (wU W) * sig he (xS W)) := by ring
    _ = 1 := by rw [h1, h2, one_pow, one_mul]

include he in
theorem isFlow_sig (hc : ∀ f : K⟦X⟧, derivative (f.subst e) = (D W f).subst e)
    (hne : toL e ≠ 0) :
    IsFlow (curveL W) dL ((toL e)⁻¹ ^ 2 * toL ((xS W).subst e))
      ((toL e)⁻¹ ^ 3 * toL ((yS W).subst e)) := by
  have h := chartFlowToFlow _ (curveL W) dL (sig he X) (sig he (wSer W))
    ((toL e)⁻¹ ^ 3 * sig he (xS W)) isDer_dL' (isFlowUW_sig W he hc) (inv_mul_sig W he hne)
  have h2 : (toL e)⁻¹ * toL e = 1 := inv_mul_cancel₀ hne
  have hx : sig he X * ((toL e)⁻¹ ^ 3 * sig he (xS W)) = (toL e)⁻¹ ^ 2 * toL ((xS W).subst e) := by
    rw [sig_X, sig_apply]
    linear_combination (toL e)⁻¹ ^ 2 * toL ((xS W).subst e) * h2
  have hy : -((toL e)⁻¹ ^ 3 * sig he (xS W)) = (toL e)⁻¹ ^ 3 * toL ((yS W).subst e) := by
    rw [← sig_apply he (yS W), yS, map_neg, mul_neg]
  rwa [hx, hy] at h

include he in
theorem mul_yZ_sig (hne : toL e ≠ 0) :
    toL e * ((toL e)⁻¹ ^ 3 * toL ((yS W).subst e)) = -((toL e)⁻¹ ^ 2 * toL ((xS W).subst e)) := by
  have hy : (yS W).subst e = -((xS W).subst e) := by
    rw [yS, ← PowerSeries.coe_substAlgHom he, map_neg]
  rw [hy, map_neg]
  have ht : toL e * (toL e)⁻¹ = 1 := mul_inv_cancel₀ hne
  calc toL e * ((toL e)⁻¹ ^ 3 * -toL ((xS W).subst e))
      = -((toL e * (toL e)⁻¹) * ((toL e)⁻¹ ^ 2 * toL ((xS W).subst e))) := by ring
    _ = -((toL e)⁻¹ ^ 2 * toL ((xS W).subst e)) := by rw [ht, one_mul]

end Wp

open Wp

theorem flowZ_of (hE : ExpSpec.{u}) (hC : ChainZ.{u}) : FlowZ.{u} := by
  intro K _ _ W
  obtain ⟨h0, h1, -, -, -⟩ := hE K W
  have he : HasSubst (expSer W) := HasSubst.of_constantCoeff_zero' h0
  have inj : Function.Injective (toL : K⟦X⟧ →+* LaurentSeries K) := HahnSeries.ofPowerSeries_injective
  have hne : toL (expSer W) ≠ 0 := by
    intro h
    have h' : expSer W = 0 := inj (by rw [h, map_zero])
    rw [h', map_zero] at h1
    exact zero_ne_one h1
  exact ⟨Wp.isFlow_sig W he (hC K W) hne, Wp.mul_yZ_sig W he hne⟩

theorem wpODE_of (hE : ExpSpec.{u}) (hC : ChainZ.{u}) : WpODE.{u} := by
  intro K _ _ W
  have hF := (flowZ_of hE hC K W).1
  have h6 : IsUnit (6 : LaurentSeries K) := by
    have h := (IsUnit.mk0 (6 : K) (by norm_num)).map (HahnSeries.C : K →+* LaurentSeries K)
    rwa [map_ofNat] at h
  have hb : 12 * (HahnSeries.C (W.b₂ / 12) : LaurentSeries K) = (curveL W).b₂ := by
    rw [WeierstrassCurve.map_b₂, ← map_ofNat (HahnSeries.C : K →+* LaurentSeries K) 12, ← map_mul]
    congr 1
    field_simp
  have hg2 : 12 * (HahnSeries.C (g₂ W) : LaurentSeries K) = (curveL W).c₄ := by
    rw [WeierstrassCurve.map_c₄, ← map_ofNat (HahnSeries.C : K →+* LaurentSeries K) 12, ← map_mul]
    congr 1
    rw [g₂]
    field_simp
  have hg3 : 216 * (HahnSeries.C (g₃ W) : LaurentSeries K) = (curveL W).c₆ := by
    rw [WeierstrassCurve.map_c₆, ← map_ofNat (HahnSeries.C : K →+* LaurentSeries K) 216, ← map_mul]
    congr 1
    rw [g₃]
    field_simp
  obtain ⟨h1, h2, h3⟩ := flowWeierstrassForm _ (curveL W) dL (xZ W) (yZ W) (HahnSeries.C (W.b₂ / 12))
    (HahnSeries.C (g₂ W)) (HahnSeries.C (g₃ W)) isDer_dL' (constCurve_dL W) hF h6 hb hg2 hg3
  refine ⟨?_, h2, ?_⟩
  · simpa only [wpL, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃] using h1
  · have hh : (HahnSeries.C (1 / 2 : K) : LaurentSeries K) * 2 = 1 := by
      rw [← map_ofNat (HahnSeries.C : K →+* LaurentSeries K) 2, ← map_mul, ← map_one HahnSeries.C]
      congr 1
      norm_num
    have hg : (HahnSeries.C (g₂ W / 2) : LaurentSeries K)
        = HahnSeries.C (1 / 2 : K) * HahnSeries.C (g₂ W) := by
      rw [← map_mul]
      congr 1
      ring
    rw [hg]
    change 2 * dL (dL (wpL W)) = 12 * wpL W ^ 2 - HahnSeries.C (g₂ W) at h3
    linear_combination HahnSeries.C (1 / 2 : K) * h3 - (dL (dL (wpL W)) - 6 * wpL W ^ 2) * hh

end Formalism.L2.Th1.A
end
end

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.CurveL
open PowerSeries

universe u

noncomputable section

namespace Formalism.L2.Th1.A

namespace CurveL

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem DL_apply (f : LaurentSeries R) : DL W f = toL (fw W) * dL f := rfl

theorem isDer_DL : IsDer (DL W) := by
  unfold IsDer
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · simp only [DL, map_add (f := _), mul_add]
  · simp only [DL, dL_mul]
    ring

theorem DL_C (r : R) : DL W (HahnSeries.C r) = 0 := by
  simp only [DL, dL_C, mul_zero]

theorem constCurve_DL : ConstCurve (DL W) (curveL W) := ⟨DL_C W _, DL_C W _, DL_C W _, DL_C W _, DL_C W _⟩

theorem DL_toL (f : R⟦X⟧) : DL W (toL f) = toL (D W f) := by
  rw [DL_apply, dL_toL, CurveSer.D_apply, map_mul]

theorem fwAt_toL : fwAt (curveL W) (toL X) (toL (wSer W)) = toL (fw W) := by
  have h2 : toL (2 : R⟦X⟧) = 2 := by
    rw [show (2 : R⟦X⟧) = ((2 : ℕ) : R⟦X⟧) by norm_num, map_natCast]
    norm_num
  have h3 : toL (3 : R⟦X⟧) = 3 := by
    rw [show (3 : R⟦X⟧) = ((3 : ℕ) : R⟦X⟧) by norm_num, map_natCast]
    norm_num
  unfold fwAt fw
  simp [h2, h3]

theorem fuAt_toL : fuAt (curveL W) (toL X) (toL (wSer W)) = toL (fu W) := by
  have h2 : toL (2 : R⟦X⟧) = 2 := by
    rw [show (2 : R⟦X⟧) = ((2 : ℕ) : R⟦X⟧) by norm_num, map_natCast]
    norm_num
  have h3 : toL (3 : R⟦X⟧) = 3 := by
    rw [show (3 : R⟦X⟧) = ((3 : ℕ) : R⟦X⟧) by norm_num, map_natCast]
    norm_num
  unfold fuAt fu
  simp [h2, h3]

theorem isFlowUW_toL : IsFlowUW (curveL W) (DL W) (toL X) (toL (wSer W)) := by
  unfold IsFlowUW
  refine ⟨?_, ?_, ?_⟩
  · unfold WEq
    conv_lhs => rw [(CurveSer.wSer_fixed W).2]
    simp
  · rw [DL_toL, CurveSer.D_apply, derivative_X, mul_one, fwAt_toL]
  · rw [DL_toL, CurveSer.D_apply, mul_comm (fw W), CurveSer.deriv_wSer_mul_fw, fuAt_toL]

theorem inv_mul_wSer : uPow (-3) * toL (xS W) * toL (wSer W) = 1 := by
  have e0 : toL (X ^ 3 : R⟦X⟧) = uPow 3 := by
    unfold uPow
    rw [HahnSeries.ofPowerSeries_X_pow]
    norm_num
  have e1 : uPow (-3) * toL (X ^ 3 : R⟦X⟧) = 1 := by
    rw [e0, ← uPow_add]
    show HahnSeries.single (-3 + 3 : ℤ) (1 : R) = 1
    rw [show (-3 + 3 : ℤ) = 0 by norm_num]
    first
      | rfl
      | simp
  have e2 : toL (wU W) * toL (xS W) = 1 := by
    rw [← map_mul, CurveSer.wU_mul_xS, map_one]
  rw [CurveSer.wSer_eq W, map_mul]
  linear_combination (toL (wU W) * toL (xS W)) * e1 + e2

theorem toL_X_mul_inv : toL X * (uPow (-3) * toL (xS W)) = xL W := by
  have e : toL (X : R⟦X⟧) * uPow (-3) = uPow (-2) := by
    have e0 : toL (X : R⟦X⟧) = uPow 1 := by
      unfold uPow
      exact HahnSeries.ofPowerSeries_X
    rw [e0, ← uPow_add]
    norm_num
  unfold xL
  rw [← mul_assoc, e]

theorem neg_inv : -(uPow (-3) * toL (xS W)) = yL W := by
  unfold yL yS
  rw [map_neg, mul_neg]

theorem isFlow_xL_yL : IsFlow (curveL W) (DL W) (xL W) (yL W) := by
  obtain ⟨hW, hDu, hDw⟩ := isFlowUW_toL W
  have hvw := inv_mul_wSer W
  have hD := isDer_DL W
  have h1 : DL W 1 = 0 := by simpa using DL_C W 1
  have hv := hD.2 (uPow (-3) * toL (xS W)) (toL (wSer W))
  rw [hvw, h1, hDw] at hv
  unfold fuAt at hv
  have hneg : ∀ f, DL W (-f) = -DL W f := fun f => by simp only [DL, map_neg, mul_neg]
  unfold IsFlow
  rw [← toL_X_mul_inv W, ← neg_inv W, hD.2, hDu, hneg]
  unfold fwAt
  unfold WEq at hW
  rw [WeierstrassCurve.Affine.equation_iff]
  set w := toL (wSer W) with hw
  set v := uPow (-3) * toL (xS W) with hv'
  set u := toL (X : R⟦X⟧) with hu
  set Dv := DL W v with hDv
  refine ⟨?_, ?_, ?_⟩
  · linear_combination v ^ 3 * hW + (-v ^ 2 + (curveL W).a₁ * u * v ^ 2
      + (curveL W).a₂ * u ^ 2 * v ^ 2 + (curveL W).a₃ * v * (w * v + 1)
      + (curveL W).a₄ * u * v * (w * v + 1) + (curveL W).a₆ * (w ^ 2 * v ^ 2 + w * v + 1)) * hvw
  · linear_combination 3 * v ^ 2 * hW + (-3 * v + 2 * (curveL W).a₁ * u * v
      + (curveL W).a₂ * u ^ 2 * v + (curveL W).a₃ * (3 * v * w + 1)
      + 2 * (curveL W).a₄ * u * v * w + 3 * (curveL W).a₆ * w * v * w - u * Dv) * hvw
      - u * v * hv
  · linear_combination ((curveL W).a₁ * v + 2 * (curveL W).a₂ * u * v
      + (curveL W).a₄ * (v * w + 1) + Dv) * hvw + v * hv

theorem toL_X_mul_yL : toL X * yL W = -xL W := by
  rw [← neg_inv W, ← toL_X_mul_inv W]
  ring

theorem toL_wSer_mul_yL : toL (wSer W) * yL W = -1 := by
  rw [← neg_inv W]
  linear_combination -(inv_mul_wSer W)

theorem toL_wSer_mul_xL : toL (wSer W) * xL W = toL X := by
  rw [← toL_X_mul_inv W]
  linear_combination toL (X : R⟦X⟧) * inv_mul_wSer W

end CurveL

open CurveL

theorem invariant_derivation_spec : DLSpec.{u} := by
  unfold DLSpec
  intro R _ W
  exact ⟨isDer_DL W, constCurve_DL W, DL_C W, DL_toL W⟩

theorem invariant_flow : FlowL.{u} := by
  unfold FlowL
  intro R _ W
  exact ⟨isFlow_xL_yL W, toL_X_mul_yL W, toL_wSer_mul_yL W, toL_wSer_mul_xL W⟩

end Formalism.L2.Th1.A
end
end

universe u v

namespace Formalism.L2.Th1.A

theorem compInvSpec : CompInvSpec.{u} := composition_inverse_spec
theorem compInvMap : CompInvMap.{u, v} := composition_inverse_map
theorem integSpec : IntegSpec.{u} := integration_spec

theorem flowNegUW : FlowNegUW.{u} := chartFlowNegation
theorem chordRegular : ChordRegular.{u} := chordFormula
theorem flowLogDeriv : FlowLogDeriv.{u} := flowLogDerivative
theorem flowTwoTorsion : FlowTwoTorsion.{u} := twoTorsionTranslation
theorem flowTwoTorsionWp : FlowTwoTorsionWp.{u} := twoTorsionTranslationWeierstrassForm

theorem wSerSpec : WSerSpec.{u} := w_series_spec
theorem wSerFactor : WSerFactor.{u} := w_series_factorization
theorem unitSpec : UnitSpec.{u} := invariant_differential_units
theorem seriesMap : SeriesMap.{u, v} := series_map
theorem flowU : FlowU.{u} := unit_flow
theorem dLSpec : DLSpec.{u} := invariant_derivation_spec
theorem flowL : FlowL.{u} := invariant_flow
theorem iSerSpec : ISerSpec.{u} := iSerSpec_of wSerSpec wSerFactor unitSpec flowU flowNegUW

theorem logSpec : LogSpec.{u} := logSpec_of integSpec unitSpec
theorem expSpec : ExpSpec.{u} := expSpec_of integSpec compInvSpec unitSpec
theorem chainZ : ChainZ.{u} := chainZ_of integSpec compInvSpec unitSpec
theorem logNeg : LogNeg.{u} := logNeg_of integSpec compInvSpec unitSpec iSerSpec
theorem flowZ : FlowZ.{u} := flowZ_of expSpec chainZ
theorem wpODE : WpODE.{u} := wpODE_of expSpec chainZ

theorem fglMap : FglMap.{u, v} := formal_group_map
theorem fglChord : FglChord.{u} := formal_group_chord
theorem fglSum : FglSum.{u} := formal_group_sum

theorem tSpec : TSpec.{u} := tSpec_of iSerSpec
theorem plusChord : PlusChord.{u} := plusChord_of flowL
theorem plusFlow : PlusFlow.{u} := plusFlow_of dLSpec flowL
theorem plusMap : PlusMap.{u, v} := addition_map

end Formalism.L2.Th1.A
