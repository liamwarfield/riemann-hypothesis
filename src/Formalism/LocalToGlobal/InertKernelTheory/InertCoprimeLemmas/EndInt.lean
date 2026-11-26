module

public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PadicNormTwoHundredSixteenEqOneOfFiveLe
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SigmaAlg
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.StmtTransInvHolds

@[expose] public section

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.VarChange
open PowerSeries

noncomputable section

namespace Formalism.L2.KerInert.VC

section Alg

variable {A : Type*} [CommRing A] (a1 a2 a3 a4 a6 U Ui r s t u w v : A)

theorem weq_vc (hw : w = u^3 + a1*u*w + a2*u^2*w + a3*w^2 + a4*u*w^2 + a6*w^3)
    (hv : v * (1 + s*u + (t - s*r)*w) = 1) (hU : U * Ui = 1) :
    (U^3*w*v) = (U*(u - r*w)*v)^3 + (Ui*(a1+2*s))*(U*(u - r*w)*v)*(U^3*w*v) + (Ui^2*(a2 - s*a1 + 3*r - s^2))*(U*(u - r*w)*v)^2*(U^3*w*v) + (Ui^3*(a3 + r*a1 + 2*t))*(U^3*w*v)^2 + (Ui^4*(a4 - s*a3 + 2*r*a2 - (t + r*s)*a1 + 3*r^2 - 2*s*t))*(U*(u - r*w)*v)*(U^3*w*v)^2 + (Ui^6*(a6 + r*a4 + r^2*a2 + r^3 - t*a3 - t^2 - r*t*a1))*(U^3*w*v)^3 := by
  linear_combination (U^3*v^3*(1)) * hw + (U^3*(v^3*((-a1*r*s*u*w^2 + a1*s*u^2*w + a1*t*u*w^2 - a2*u^2*w - a3*r*s*w^3 + a3*s*u*w^2 + a3*t*w^3 - a4*u*w^2 - a6*w^3 + r^2*s^2*w^3 - 2*r*s^2*u*w^2 - 2*r*s*t*w^3 + s^2*u^2*w + 2*s*t*u*w^2 + t^2*w^3 - u^3)*(1 + s*u + (t - s*r)*w)^0*((v*(1 + s*u + (t - s*r)*w))^0 + (v*(1 + s*u + (t - s*r)*w))^1 + (v*(1 + s*u + (t - s*r)*w))^2) + (-a1*u*w - a3*w^2 + 2*r*s*w^2 - 2*s*u*w - 2*t*w^2)*(1 + s*u + (t - s*r)*w)^1*((v*(1 + s*u + (t - s*r)*w))^0 + (v*(1 + s*u + (t - s*r)*w))^1) + (w)*(1 + s*u + (t - s*r)*w)^2*((v*(1 + s*u + (t - s*r)*w))^0)) - (-a1*r*s*u*v^3*w^2 + a1*s*u^2*v^3*w + a1*t*u*v^3*w^2 - a1*u*v^2*w - a2*u^2*v^3*w - a3*r*s*v^3*w^3 + a3*s*u*v^3*w^2 + a3*t*v^3*w^3 - a3*v^2*w^2 - a4*u*v^3*w^2 - a6*v^3*w^3 + r^2*s^2*v^3*w^3 - 2*r*s^2*u*v^3*w^2 - 2*r*s*t*v^3*w^3 + 2*r*s*v^2*w^2 + s^2*u^2*v^3*w + 2*s*t*u*v^3*w^2 - 2*s*u*v^2*w + t^2*v^3*w^3 - 2*t*v^2*w^2 - u^3*v^3 + v*w)*((v*(1 + s*u + (t - s*r)*w))^0 + (v*(1 + s*u + (t - s*r)*w))^1 + (v*(1 + s*u + (t - s*r)*w))^2))) * hv + (U^3*(a1*r*t*v^3*w^3 - a2*r^2*v^3*w^3 + a3*t*v^3*w^3 - a4*r*v^3*w^3 - a6*v^3*w^3 - r^3*v^3*w^3 + t^2*v^3*w^3)*((U*Ui)^0 + (U*Ui)^1 + (U*Ui)^2 + (U*Ui)^3 + (U*Ui)^4 + (U*Ui)^5) + U^3*(-a1*r^2*s*v^3*w^3 + a1*r*s*u*v^3*w^2 - a1*r*t*v^3*w^3 + a1*t*u*v^3*w^2 + 2*a2*r^2*v^3*w^3 - 2*a2*r*u*v^3*w^2 - a3*r*s*v^3*w^3 + a3*s*u*v^3*w^2 + a4*r*v^3*w^3 - a4*u*v^3*w^2 + 3*r^3*v^3*w^3 - 3*r^2*u*v^3*w^2 - 2*r*s*t*v^3*w^3 + 2*s*t*u*v^3*w^2)*((U*Ui)^0 + (U*Ui)^1 + (U*Ui)^2 + (U*Ui)^3) + U^3*(-a1*r*v^2*w^2 - a3*v^2*w^2 - 2*t*v^2*w^2)*((U*Ui)^0 + (U*Ui)^1 + (U*Ui)^2) + U^3*(a1*r^2*s*v^3*w^3 - 2*a1*r*s*u*v^3*w^2 + a1*s*u^2*v^3*w - a2*r^2*v^3*w^3 + 2*a2*r*u*v^3*w^2 - a2*u^2*v^3*w - 3*r^3*v^3*w^3 + r^2*s^2*v^3*w^3 + 6*r^2*u*v^3*w^2 - 2*r*s^2*u*v^3*w^2 - 3*r*u^2*v^3*w + s^2*u^2*v^3*w)*((U*Ui)^0 + (U*Ui)^1) + U^3*(a1*r*v^2*w^2 - a1*u*v^2*w + 2*r*s*v^2*w^2 - 2*s*u*v^2*w)*((U*Ui)^0)) * hU

theorem flow_vc (hw : w = u^3 + a1*u*w + a2*u^2*w + a3*w^2 + a4*u*w^2 + a6*w^3)
    (hv : v * (1 + s*u + (t - s*r)*w) = 1) (hU : U * Ui = 1) :
    U*(((1 - a1*u - a2*u^2 - 2*a3*w - 2*a4*u*w - 3*a6*w^2) - r*(3*u^2 + a1*w + 2*a2*u*w + a4*w^2))*v + (u - r*w)*(-v^2*(s*(1 - a1*u - a2*u^2 - 2*a3*w - 2*a4*u*w - 3*a6*w^2) + (t - s*r)*(3*u^2 + a1*w + 2*a2*u*w + a4*w^2)))) =
      U*(1 - (Ui*(a1+2*s))*(U*(u - r*w)*v) - (Ui^2*(a2 - s*a1 + 3*r - s^2))*(U*(u - r*w)*v)^2 - 2*(Ui^3*(a3 + r*a1 + 2*t))*(U^3*w*v) - 2*(Ui^4*(a4 - s*a3 + 2*r*a2 - (t + r*s)*a1 + 3*r^2 - 2*s*t))*(U*(u - r*w)*v)*(U^3*w*v) - 3*(Ui^6*(a6 + r*a4 + r^2*a2 + r^3 - t*a3 - t^2 - r*t*a1))*(U^3*w*v)^2) := by
  linear_combination (U^1*v^2*(3*t)) * hw + (U^1*(v^2*((-3*a1*t*u*w - 2*a2*r^2*s*u*w^2 + a2*r*s*u^2*w + 2*a2*r*t*u*w^2 + 2*a2*r*u*w + a2*s*u^3 - 2*a2*t*u^2*w + a2*u^2 - 3*a3*t*w^2 - a4*r^2*s*w^3 - a4*r*s*u*w^2 + a4*r*t*w^3 + a4*r*w^2 + 2*a4*s*u^2*w - a4*t*u*w^2 + 2*a4*u*w - 3*a6*r*s*w^3 + 3*a6*s*u*w^2 + 3*a6*w^2 - r^2*s^2*w^2 - 3*r^2*s*u^2*w + 2*r*s^2*u*w + 4*r*s*t*w^2 + 3*r*s*u^3 + r*s*w + 3*r*t*u^2*w + 3*r*u^2 - s^2*u^2 - 4*s*t*u*w - s*u - 3*t^2*w^2 - 3*t*u^3)*(1 + s*u + (t - s*r)*w)^0*((v*(1 + s*u + (t - s*r)*w))^0 + (v*(1 + s*u + (t - s*r)*w))^1) + (-2*a2*r*u*w - a2*u^2 - a4*r*w^2 - 2*a4*u*w - 3*a6*w^2 - 2*r*s*w - 3*r*u^2 + 2*s*u + 4*t*w + 1)*(1 + s*u + (t - s*r)*w)^1*((v*(1 + s*u + (t - s*r)*w))^0)) - (-3*a1*t*u*v^2*w - 2*a2*r^2*s*u*v^2*w^2 + a2*r*s*u^2*v^2*w + 2*a2*r*t*u*v^2*w^2 + 2*a2*r*u*v^2*w - 2*a2*r*u*v*w + a2*s*u^3*v^2 - 2*a2*t*u^2*v^2*w + a2*u^2*v^2 - a2*u^2*v - 3*a3*t*v^2*w^2 - a4*r^2*s*v^2*w^3 - a4*r*s*u*v^2*w^2 + a4*r*t*v^2*w^3 + a4*r*v^2*w^2 - a4*r*v*w^2 + 2*a4*s*u^2*v^2*w - a4*t*u*v^2*w^2 + 2*a4*u*v^2*w - 2*a4*u*v*w - 3*a6*r*s*v^2*w^3 + 3*a6*s*u*v^2*w^2 + 3*a6*v^2*w^2 - 3*a6*v*w^2 - r^2*s^2*v^2*w^2 - 3*r^2*s*u^2*v^2*w + 2*r*s^2*u*v^2*w + 4*r*s*t*v^2*w^2 + 3*r*s*u^3*v^2 + r*s*v^2*w - 2*r*s*v*w + 3*r*t*u^2*v^2*w + 3*r*u^2*v^2 - 3*r*u^2*v - s^2*u^2*v^2 - 4*s*t*u*v^2*w - s*u*v^2 + 2*s*u*v - 3*t^2*v^2*w^2 - 3*t*u^3*v^2 + 4*t*v*w + v - 1)*((v*(1 + s*u + (t - s*r)*w))^0 + (v*(1 + s*u + (t - s*r)*w))^1))) * hv + (U^1*(-3*a1*r*t*v^2*w^2 + 3*a2*r^2*v^2*w^2 - 3*a3*t*v^2*w^2 + 3*a4*r*v^2*w^2 + 3*a6*v^2*w^2 + 3*r^3*v^2*w^2 - 3*t^2*v^2*w^2)*((U*Ui)^0 + (U*Ui)^1 + (U*Ui)^2 + (U*Ui)^3 + (U*Ui)^4 + (U*Ui)^5) + U^1*(2*a1*r^2*s*v^2*w^2 - 2*a1*r*s*u*v^2*w + 2*a1*r*t*v^2*w^2 - 2*a1*t*u*v^2*w - 4*a2*r^2*v^2*w^2 + 4*a2*r*u*v^2*w + 2*a3*r*s*v^2*w^2 - 2*a3*s*u*v^2*w - 2*a4*r*v^2*w^2 + 2*a4*u*v^2*w - 6*r^3*v^2*w^2 + 6*r^2*u*v^2*w + 4*r*s*t*v^2*w^2 - 4*s*t*u*v^2*w)*((U*Ui)^0 + (U*Ui)^1 + (U*Ui)^2 + (U*Ui)^3) + U^1*(2*a1*r*v*w + 2*a3*v*w + 4*t*v*w)*((U*Ui)^0 + (U*Ui)^1 + (U*Ui)^2) + U^1*(-a1*r^2*s*v^2*w^2 + 2*a1*r*s*u*v^2*w - a1*s*u^2*v^2 + a2*r^2*v^2*w^2 - 2*a2*r*u*v^2*w + a2*u^2*v^2 + 3*r^3*v^2*w^2 - r^2*s^2*v^2*w^2 - 6*r^2*u*v^2*w + 2*r*s^2*u*v^2*w + 3*r*u^2*v^2 - s^2*u^2*v^2)*((U*Ui)^0 + (U*Ui)^1) + U^1*(-a1*r*v*w + a1*u*v - 2*r*s*v*w + 2*s*u*v)*((U*Ui)^0)) * hU

end Alg

open Formalism.L2.Th1.A

section Ring

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R)

def den : R⟦X⟧ := 1 + PowerSeries.C C.s * X + PowerSeries.C (C.t - C.s * C.r) * wSer W

def vv : R⟦X⟧ := invOfUnit (den W C) 1

def phi : R⟦X⟧ := PowerSeries.C (C.u : R) * (X - PowerSeries.C C.r * wSer W) * vv W C

def psi : R⟦X⟧ := PowerSeries.C ((C.u : R) ^ 3) * wSer W * vv W C

theorem den_cc : constantCoeff (den W C) = 1 := by
  simp [den, CurveSer.wSer_cc]

theorem den_mul_vv : den W C * vv W C = 1 :=
  mul_invOfUnit _ _ (by rw [den_cc]; simp)

theorem vv_cc : constantCoeff (vv W C) = 1 := by
  simp [vv]

theorem phi_cc : constantCoeff (phi W C) = 0 := by
  simp [phi, CurveSer.wSer_cc]

theorem psi_cc : constantCoeff (psi W C) = 0 := by
  simp [psi, CurveSer.wSer_cc]

theorem phi_eq : phi W C = X * (PowerSeries.C (C.u : R) * (1 - PowerSeries.C C.r * X ^ 2 * wU W) * vv W C) := by
  rw [phi, CurveSer.wSer_eq]; ring

theorem phi_coeff_one : coeff 1 (phi W C) = (C.u : R) := by
  rw [phi_eq, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  simp [vv_cc]

theorem hU_C : PowerSeries.C (C.u : R) * PowerSeries.C ((C.u⁻¹ : Rˣ) : R) = 1 := by
  rw [← map_mul, Units.mul_inv, map_one]

theorem hv_C : vv W C * (1 + PowerSeries.C C.s * X + (PowerSeries.C C.t - PowerSeries.C C.s * PowerSeries.C C.r) * wSer W) = 1 := by
  rw [mul_comm, ← map_mul, ← map_sub]; exact den_mul_vv W C

theorem weq_phi : psi W C = phi W C ^ 3 + PowerSeries.C (C • W).a₁ * phi W C * psi W C
    + PowerSeries.C (C • W).a₂ * phi W C ^ 2 * psi W C + PowerSeries.C (C • W).a₃ * psi W C ^ 2
    + PowerSeries.C (C • W).a₄ * phi W C * psi W C ^ 2 + PowerSeries.C (C • W).a₆ * psi W C ^ 3 := by
  have hw := (CurveSer.wSer_fixed W).2
  have h := weq_vc (PowerSeries.C W.a₁) (PowerSeries.C W.a₂) (PowerSeries.C W.a₃) (PowerSeries.C W.a₄)
    (PowerSeries.C W.a₆) (PowerSeries.C (C.u : R)) (PowerSeries.C ((C.u⁻¹ : Rˣ) : R)) (PowerSeries.C C.r)
    (PowerSeries.C C.s) (PowerSeries.C C.t) X (wSer W) (vv W C) hw (hv_C W C) (hU_C C)
  simp only [phi, psi, WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄, WeierstrassCurve.variableChange_a₆,
    map_mul, map_add, map_sub, map_pow, map_ofNat]
  linear_combination h

theorem wSer_phi : (wSer (C • W)).subst (phi W C) = psi W C :=
  (ISer.eq_wSer_subst wSerSpec (C • W) _ _ (phi_cc W C) (psi_cc W C) (weq_phi W C)).symm

theorem C_eq_algebraMap (a : R) : (PowerSeries.C a : R⟦X⟧) = algebraMap R R⟦X⟧ a := rfl

theorem D_C (a : R) : D W (PowerSeries.C a) = 0 := by
  rw [C_eq_algebraMap, Derivation.map_algebraMap]

theorem D_phi : D W (phi W C) = PowerSeries.C (C.u : R) * (fw (C • W)).subst (phi W C) := by
  obtain ⟨-, -, hFl, hfwAt, hfuAt, -⟩ := flowU R W
  obtain ⟨-, hDX, hDw⟩ := hFl
  rw [hfwAt] at hDX
  rw [hfuAt] at hDw
  have hs : HasSubst (phi W C) := HasSubst.of_constantCoeff_zero' (phi_cc W C)
  have hfwsub : (fw (C • W)).subst (phi W C) = 1 - PowerSeries.C (C • W).a₁ * phi W C
      - PowerSeries.C (C • W).a₂ * phi W C ^ 2 - 2 * PowerSeries.C (C • W).a₃ * psi W C
      - 2 * PowerSeries.C (C • W).a₄ * phi W C * psi W C - 3 * PowerSeries.C (C • W).a₆ * psi W C ^ 2 := by
    rw [← ISer.subHom_apply _ (phi_cc W C)]
    simp only [fw, map_sub, map_mul, map_pow, map_one, map_ofNat, ISer.subHom_X, ISer.subHom_C]
    rw [ISer.subHom_apply, wSer_phi]
  have hvD : D W (vv W C) = -(vv W C) ^ 2 * D W (den W C) := by
    have h1 : D W (den W C * vv W C) = 0 := by rw [den_mul_vv, Derivation.map_one_eq_zero]
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h1
    have h2 := den_mul_vv W C
    linear_combination (vv W C) * h1 - (D W (vv W C)) * h2
  have hdenD : D W (den W C) = PowerSeries.C C.s * D W X + PowerSeries.C (C.t - C.s * C.r) * D W (wSer W) := by
    simp only [den, map_add (f := _), Derivation.leibniz, smul_eq_mul, D_C, Derivation.map_one_eq_zero]
    ring
  have hphiD : D W (phi W C) = PowerSeries.C (C.u : R) * ((D W X - PowerSeries.C C.r * D W (wSer W)) * vv W C
      + (X - PowerSeries.C C.r * wSer W) * D W (vv W C)) := by
    simp only [phi, map_sub, Derivation.leibniz, smul_eq_mul, D_C]
    ring
  rw [hphiD, hvD, hdenD, hDX, hDw, hfwsub]
  have hw := (CurveSer.wSer_fixed W).2
  have h := flow_vc (PowerSeries.C W.a₁) (PowerSeries.C W.a₂) (PowerSeries.C W.a₃) (PowerSeries.C W.a₄)
    (PowerSeries.C W.a₆) (PowerSeries.C (C.u : R)) (PowerSeries.C ((C.u⁻¹ : Rˣ) : R)) (PowerSeries.C C.r)
    (PowerSeries.C C.s) (PowerSeries.C C.t) X (wSer W) (vv W C) hw (hv_C W C) (hU_C C)
  simp only [phi, psi, fw, fu, WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄, WeierstrassCurve.variableChange_a₆,
    map_mul, map_add, map_sub, map_pow, map_ofNat] at h ⊢
  linear_combination h

end Ring

section Subst

variable {R : Type} [CommRing R]

theorem cc_subst0 {f a : R⟦X⟧} (ha : constantCoeff a = 0) (hf : constantCoeff f = 0) :
    constantCoeff (f.subst a) = 0 :=
  constantCoeff_subst_eq_zero ha f hf

theorem subst_C' {s : R⟦X⟧} (hs0 : constantCoeff s = 0) (a : R) : (PowerSeries.C a).subst s = PowerSeries.C a := by
  rw [← ISer.subHom_apply _ hs0, ISer.subHom_C]

end Subst

section Field

variable {K : Type} [Field K] [CharZero K] (W : WeierstrassCurve K) (C : WeierstrassCurve.VariableChange K)

theorem derivative_C_mul' (a : K) (f : K⟦X⟧) :
    derivative (PowerSeries.C a * f) = PowerSeries.C a * derivative f := by
  rw [Derivation.leibniz, derivative_C, smul_eq_mul, smul_eq_mul, mul_zero, add_zero]

theorem log_phi : (logSer (C • W)).subst (phi W C) = PowerSeries.C (C.u : K) * logSer W := by
  have hs : HasSubst (phi W C) := HasSubst.of_constantCoeff_zero' (phi_cc W C)
  have h1 : derivative (phi W C) * fw W =
      PowerSeries.C (C.u : K) * (fw (C • W)).subst (phi W C) := by
    rw [← D_phi, CurveSer.D_apply, mul_comm]
  have h2 : (fw (C • W)).subst (phi W C) * (om (C • W)).subst (phi W C) = 1 := by
    rw [← subst_mul hs, CurveSer.fw_mul_om, ← coe_substAlgHom hs, map_one]
  have h3 := CurveSer.fw_mul_om W
  have hd : derivative ((logSer (C • W)).subst (phi W C)) = PowerSeries.C (C.u : K) * om W := by
    rw [derivative_subst hs, (logSpec K (C • W)).2.2.1]
    linear_combination (-((om (C • W)).subst (phi W C) * derivative (phi W C))) * h3
      + ((om (C • W)).subst (phi W C) * om W) * h1 + (PowerSeries.C (C.u : K) * om W) * h2
  have hc : constantCoeff ((logSer (C • W)).subst (phi W C)) = 0 :=
    cc_subst0 (phi_cc W C) (logSpec K (C • W)).1
  have hd2 : derivative (PowerSeries.C (C.u : K) * logSer W) = PowerSeries.C (C.u : K) * om W := by
    rw [derivative_C_mul', (logSpec K W).2.2.1]
  have hc2 : constantCoeff (PowerSeries.C (C.u : K) * logSer W) = 0 := by
    simp [(logSpec K W).1]
  rw [(integSpec K _).2.2 _ hc hd, (integSpec K _).2.2 _ hc2 hd2]

theorem cUi_cc : constantCoeff (PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * X) = 0 := by simp

theorem exp_eq : expSer (C • W) =
    (phi W C).subst ((expSer W).subst (PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * X)) := by
  have hm0 := cUi_cc C
  have hmS : HasSubst (PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * X) := HasSubst.of_constantCoeff_zero' hm0
  have he := expSpec K W
  have heS : HasSubst (expSer W) := HasSubst.of_constantCoeff_zero' he.1
  have hh0 : constantCoeff ((expSer W).subst (PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * X)) = 0 := cc_subst0 hm0 he.1
  have hhS := HasSubst.of_constantCoeff_zero' hh0
  have hs : HasSubst (phi W C) := HasSubst.of_constantCoeff_zero' (phi_cc W C)
  have hlog : (logSer (C • W)).subst ((phi W C).subst ((expSer W).subst (PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * X))) = X := by
    rw [← subst_comp_subst_apply hs hhS, log_phi, subst_mul hhS, subst_C' hh0,
      ← subst_comp_subst_apply heS hmS, he.2.2.1, subst_X hmS, ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
  have hl := logSpec K (C • W)
  have hsp := compInvSpec K (logSer (C • W)) hl.1 (by rw [hl.2.1]; exact isUnit_one)
  exact (hsp.2.2.2.2.1 _ (cc_subst0 hh0 (phi_cc W C)) hlog).symm

theorem mulBy_eq (c : K) : Formalism.L2.Th1.C.mulBy (logSer (C • W)) (expSer (C • W)) c =
    (phi W C).subst ((Formalism.L2.Th1.C.mulBy (logSer W) (expSer W) c).subst (compInv (phi W C))) := by
  have hs : HasSubst (phi W C) := HasSubst.of_constantCoeff_zero' (phi_cc W C)
  have hci := compInvSpec K (phi W C) (phi_cc W C) (by rw [phi_coeff_one]; exact Units.isUnit _)
  have hp0 : constantCoeff (compInv (phi W C)) = 0 := hci.1
  have hpS : HasSubst (compInv (phi W C)) := HasSubst.of_constantCoeff_zero' hp0
  have hl := logSpec K W
  have he := expSpec K W
  have heS : HasSubst (expSer W) := HasSubst.of_constantCoeff_zero' he.1
  have hl' : logSer (C • W) = PowerSeries.C (C.u : K) * (logSer W).subst (compInv (phi W C)) := by
    have h := congrArg (fun f : K⟦X⟧ => f.subst (compInv (phi W C))) (log_phi W C)
    rw [subst_comp_subst_apply hs hpS, hci.2.1, X_subst, subst_mul hpS, subst_C' hp0] at h
    exact h
  have hq0 : constantCoeff (PowerSeries.C c * logSer (C • W)) = 0 := by
    simp [(logSpec K (C • W)).1]
  have hqS : HasSubst (PowerSeries.C c * logSer (C • W)) := HasSubst.of_constantCoeff_zero' hq0
  have hm0 := cUi_cc C
  have hmS : HasSubst (PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * X) := HasSubst.of_constantCoeff_zero' hm0
  have hh0 : constantCoeff ((expSer W).subst (PowerSeries.C ((C.u⁻¹ : Kˣ) : K) * X)) = 0 := cc_subst0 hm0 he.1
  have hhS := HasSubst.of_constantCoeff_zero' hh0
  have hr0 : constantCoeff (PowerSeries.C c * logSer W) = 0 := by simp [hl.1]
  have hrS : HasSubst (PowerSeries.C c * logSer W) := HasSubst.of_constantCoeff_zero' hr0
  unfold Formalism.L2.Th1.C.mulBy
  rw [exp_eq, subst_comp_subst_apply hhS hqS, subst_comp_subst_apply hmS hqS, subst_mul hqS, subst_C' hq0,
    subst_X hqS, subst_comp_subst_apply hrS hpS, subst_mul hpS, subst_C' hp0, hl']
  congr 2
  rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, mul_comm (((C.u⁻¹ : Kˣ) : K)) c, mul_assoc c,
    Units.inv_mul, mul_one]

end Field

section Integral

open Formalism.L2.Th1.C

variable {K : Type} [Field K] [CharZero K] (R' : Subring K)

theorem intPS_C' {a : K} (ha : a ∈ R') : IntPS R' (PowerSeries.C a) := by
  intro n; rw [coeff_C]; split_ifs; exacts [ha, R'.zero_mem]

theorem intPS_X' : IntPS R' (X : K⟦X⟧) := by
  intro n; rw [coeff_X]; split_ifs; exacts [R'.one_mem, R'.zero_mem]

theorem intPS_add' {f g : K⟦X⟧} (hf : IntPS R' f) (hg : IntPS R' g) : IntPS R' (f + g) := by
  intro n; rw [map_add (f := _)]; exact R'.add_mem (hf n) (hg n)

theorem intPS_sub' {f g : K⟦X⟧} (hf : IntPS R' f) (hg : IntPS R' g) : IntPS R' (f - g) := by
  intro n; rw [map_sub]; exact R'.sub_mem (hf n) (hg n)

theorem intPS_mul' {f g : K⟦X⟧} (hf : IntPS R' f) (hg : IntPS R' g) : IntPS R' (f * g) := by
  intro n; rw [coeff_mul]; exact R'.sum_mem fun p _ => R'.mul_mem (hf _) (hg _)

theorem intPS_wSer {W : WeierstrassCurve K} (hW : CoeffIn R' W) : IntPS R' (wSer W) := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  let WS : WeierstrassCurve R' := ⟨⟨_, h1⟩, ⟨_, h2⟩, ⟨_, h3⟩, ⟨_, h4⟩, ⟨_, h6⟩⟩
  have e : WS.map R'.subtype = W := by ext <;> rfl
  intro n
  rw [← e, ← (seriesMap R' K R'.subtype WS).1, coeff_map]
  exact SetLike.coe_mem _

theorem intPS_subst' {f a : K⟦X⟧} (hf : IntPS R' f) (ha : IntPS R' a) (ha0 : constantCoeff a = 0) :
    IntPS R' (f.subst a) :=
  Pts.intPS_of_intMv (IntegralMvPolynomialLemmas.intMv_subst hf ⟨ha0, Pts.intMv_of_intPS ha⟩)

theorem intPS_compInv {f : K⟦X⟧} (hf : IntPS R' f) (h0 : constantCoeff f = 0) {u ui : K} (hui : ui ∈ R')
    (h1 : coeff 1 f = u) (huu : u * ui = 1) : IntPS R' (compInv f) := by
  let fS : R'⟦X⟧ := PowerSeries.mk fun n => ⟨coeff n f, hf n⟩
  have e : PowerSeries.map R'.subtype fS = f := by
    ext n; simp [fS]
  have h0S : constantCoeff fS = 0 := by
    apply Subtype.ext
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp [fS, h0]
  have hm : coeff 1 fS * ⟨ui, hui⟩ = 1 := Subtype.ext (by simp [fS, h1, huu])
  have h1S : IsUnit (coeff 1 fS) := ⟨⟨_, ⟨ui, hui⟩, hm, by rw [mul_comm]; exact hm⟩, rfl⟩
  intro n
  rw [← e, ← compInvMap R' K R'.subtype fS h0S h1S, coeff_map]
  exact SetLike.coe_mem _

variable {R'}

theorem intPS_phi (W : WeierstrassCurve K) (hW : CoeffIn R' W) (C : WeierstrassCurve.VariableChange K)
    (hu : ((C.u : Kˣ) : K) ∈ R') (hr : C.r ∈ R') (hs : C.s ∈ R') (ht : C.t ∈ R') : IntPS R' (phi W C) := by
  have hw := intPS_wSer R' hW
  have hden : IntPS R' (den W C) :=
    intPS_add' R' (intPS_add' R' (intPS_C' R' R'.one_mem) (intPS_mul' R' (intPS_C' R' hs) (intPS_X' R')))
      (intPS_mul' R' (intPS_C' R' (R'.sub_mem ht (R'.mul_mem hs hr))) hw)
  have hv : IntPS R' (vv W C) :=
    Pts.intPS_of_intMv (IntegralMvPolynomialLemmas.intMv_of_mul_eq_one (Pts.intMv_of_intPS hden) (den_cc W C) (den_mul_vv W C))
  exact intPS_mul' R' (intPS_mul' R' (intPS_C' R' hu) (intPS_sub' R' (intPS_X' R') (intPS_mul' R' (intPS_C' R' hr) hw))) hv

theorem endInt_varChange (W : WeierstrassCurve K) (hW : CoeffIn R' W) (C : WeierstrassCurve.VariableChange K)
    (hu : ((C.u : Kˣ) : K) ∈ R') (hu' : ((C.u⁻¹ : Kˣ) : K) ∈ R') (hr : C.r ∈ R') (hs : C.s ∈ R') (ht : C.t ∈ R')
    (c : K) (h : EndInt R' (logSer W) (expSer W) c) : EndInt R' (logSer (C • W)) (expSer (C • W)) c := by
  unfold EndInt at h ⊢
  rw [mulBy_eq]
  have hphi := intPS_phi W hW C hu hr hs ht
  have hci := compInvSpec K (phi W C) (phi_cc W C) (by rw [phi_coeff_one]; exact Units.isUnit _)
  have hpinv := intPS_compInv R' hphi (phi_cc W C) hu' (phi_coeff_one W C) (Units.mul_inv C.u)
  have hm0 : constantCoeff (Formalism.L2.Th1.C.mulBy (logSer W) (expSer W) c) = 0 :=
    cc_subst0 (by simp [(logSpec K W).1]) (expSpec K W).1
  exact intPS_subst' R' hphi (intPS_subst' R' h hpinv hci.1) (cc_subst0 hci.1 hm0)

end Integral

end Formalism.L2.KerInert.VC
end
end

noncomputable section

namespace Formalism.L2.KerInert.IwahoriBlocks

open NumberField Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

abbrev RB (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] := Formalism.G.unitBall ℂ_[p]

section Norms

variable {p : ℕ} [Fact p.Prime]

theorem norm_two_three (h5 : 5 ≤ p) : ‖(2 : ℂ_[p])‖ = 1 ∧ ‖(3 : ℂ_[p])‖ = 1 := by
  have hp : p.Prime := Fact.out
  have c2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
  have c3 : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).mpr (by omega)
  exact ⟨by simpa using Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.norm_nat_coprime p c2,
    by simpa using Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.norm_nat_coprime p c3⟩

theorem norm_u_of (C : WeierstrassCurve.VariableChange ℂ_[p]) (h : ‖((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ = 1) :
    ‖((C.u : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 := by
  have h1 : ‖((C.u : ℂ_[p]ˣ) : ℂ_[p])‖ * ‖((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 := by
    rw [← norm_mul, Units.mul_inv, norm_one]
  rw [h, mul_one] at h1
  exact h1

theorem vc_params (h5 : 5 ≤ p) (W0 : WeierstrassCurve ℂ_[p]) (h01 : W0.a₁ = 0) (h02 : W0.a₂ = 0) (h03 : W0.a₃ = 0)
    (hΔ0 : ‖W0.Δ‖ = 1) (C : WeierstrassCurve.VariableChange ℂ_[p]) (i1 : ‖(C • W0).a₁‖ ≤ 1)
    (i2 : ‖(C • W0).a₂‖ ≤ 1) (i3 : ‖(C • W0).a₃‖ ≤ 1) (hΔ : ‖(C • W0).Δ‖ = 1) :
    ‖((C.u : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 ∧ ‖((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 ∧ ‖C.r‖ ≤ 1 ∧ ‖C.s‖ ≤ 1 ∧ ‖C.t‖ ≤ 1 := by
  obtain ⟨h2, h3⟩ := norm_two_three h5
  have hv : ‖((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 := by
    have h12 := hΔ
    rw [WeierstrassCurve.variableChange_Δ, norm_mul, norm_pow, hΔ0, mul_one] at h12
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h12
  have hs : ‖C.s‖ ≤ 1 := by
    have h := i1
    rw [WeierstrassCurve.variableChange_a₁, h01, zero_add, norm_mul, norm_mul, hv, h2, one_mul,
      one_mul] at h
    exact h
  have ht : ‖C.t‖ ≤ 1 := by
    have h := i3
    simp only [WeierstrassCurve.variableChange_a₃, h03, h01, mul_zero, zero_add] at h
    rw [norm_mul, norm_pow, hv, one_pow, one_mul, norm_mul, h2, one_mul] at h
    exact h
  have hr : ‖C.r‖ ≤ 1 := by
    have ha2 : ‖3 * C.r - C.s ^ 2‖ ≤ 1 := by
      have h := i2
      simp only [WeierstrassCurve.variableChange_a₂, h02, h01, mul_zero, sub_zero, zero_add] at h
      rw [norm_mul, norm_pow, hv, one_pow, one_mul] at h
      exact h

    have h3r : ‖3 * C.r‖ ≤ 1 := by
      have e : 3 * C.r = (3 * C.r - C.s ^ 2) + C.s ^ 2 := by ring
      rw [e]
      refine (PadicComplex.isNonarchimedean p _ _).trans (max_le ha2 ?_)
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hs
    rwa [norm_mul, h3, one_mul] at h3r
  exact ⟨norm_u_of C hv, hv, hr, hs, ht⟩

end Norms

section G

variable {p : ℕ} [Fact p.Prime]

theorem mulBy_g (g : G1 p) (hOk : g.Ok) (c : ℂ_[p]) :
    (g.mulBy c (Xv ()) : MvPowerSeries Unit ℂ_[p]) =
      Formalism.L2.Th1.C.mulBy (Formalism.L2.Th1.A.logSer g.W) (Formalism.L2.Th1.A.expSer g.W) c := by
  have hl : g.l = Formalism.L2.Th1.A.logSer g.W := Formalism.L2.KerInert.Dict.formal_logarithm_agree p g.W g.wq hOk.2.1
  have he : g.ex = Formalism.L2.Th1.A.expSer g.W := Formalism.L2.KerInert.Dict.formal_exponential_agree p g hOk
  have hX : PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) g.l = g.l := by
    show PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[p]) g.l = g.l
    rw [← one_smul ℂ_[p] (PowerSeries.X : PowerSeries ℂ_[p]), ← PowerSeries.rescale_eq_subst,
      PowerSeries.rescale_one, RingHom.id_apply]
  unfold G1.mulBy G1.pt G1.lg Formalism.L2.Th1.C.mulBy
  rw [hX, hl, he]
  rfl

theorem coeffIn_g (g : G1 p) (hOk : g.Ok) : Formalism.L2.Th1.C.CoeffIn (RB p) g.W := by
  obtain ⟨⟨h1, h2, h3, h4, h6, -⟩, -⟩ := hOk
  exact ⟨h1, h2, h3, h4, h6⟩

theorem integralMv_of_endInt (g : G1 p) (hOk : g.Ok) (c : ℂ_[p])
    (h : Formalism.L2.Th1.C.EndInt (RB p) (Formalism.L2.Th1.A.logSer g.W) (Formalism.L2.Th1.A.expSer g.W) c) :
    IntegralMv (g.mulBy c (Xv ()) : MvPowerSeries Unit ℂ_[p]) := by
  rw [mulBy_g g hOk c]
  unfold Formalism.L2.Th1.C.EndInt Formalism.L2.Th1.C.IntPS at h
  unfold IntegralMv
  intro n
  have hn : n = Finsupp.single () (n ()) := Finsupp.ext fun u => by
    cases u
    simp
  rw [hn]
  exact h (n ())

end G

section Main

theorem endInt_omega (hInv : Formalism.L2.KerInert.Sigma.InvAlg) (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K))
    (δ : ℂ) (g : G1 p) (hAt : At D cc δ g) (h5 : 5 ≤ p) (hIn : InertK D p) (hOW : ModelOverW g.lam g.abelian₂ g.C) :
    ∃ ι : ℂ ≃+* ℂ_[p], Formalism.L2.KerInert.IotaExt g.lam ι ∧
      Formalism.L2.Th1.C.EndInt (RB p) (Formalism.L2.Th1.A.logSer g.W) (Formalism.L2.Th1.A.expSer g.W) (ι (Formalism.L2.Th1.CM.omegaK D.host.d)) := by
  obtain ⟨hcurve, -, hδ12, hLam, hOk⟩ := hAt
  have hcc : cc ≠ ⊥ := hcurve.1
  have hδ : δ ≠ 0 := by
    intro h0
    obtain ⟨⟨L1, hL1⟩, -⟩ := Formalism.L2.Th1.F2.lamOfLat D cc 1 hcc one_ne_zero
    obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L1 (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hL1)
    have hd := Formalism.L2.Th1.F.discNeZero L1
    apply hd
    have h12 := hδ12
    unfold Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice Formalism.MainNotions.TaylorLogMetric.discr at h12
    rw [h0, e2, e3] at h12
    rw [← h12]; norm_num
  obtain ⟨⟨L, hL⟩, hCM⟩ := Formalism.L2.Th1.F2.lamOfLat D cc δ hcc hδ
  have hLg : g.abelian₂ = L.lattice.toAddSubgroup := hLam.trans hL.symm
  obtain ⟨hg2, hg3⟩ := hInv D cc δ hcurve hδ12 L hL
  set a2 : Qbar := ⟨L.g₂, hg2⟩ with ha2
  set a3 : Qbar := ⟨L.g₃, hg3⟩ with ha3
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hLg.symm)
  have hp : p.Prime := Fact.out
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  have hd4 : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega
  have hns : ¬ IsSquare ((-(D.host.d : ℤ) : ℤ) : ZMod p) := ZMod.nonsquare_of_jacobiSym_eq_neg_one hIn
  have hsq' : ¬ ∃ a : ZMod p, a ^ 2 = -(D.host.d : ZMod p) := by
    rintro ⟨a, ha⟩; apply hns; exact ⟨a, by push_cast; rw [← ha]; ring⟩
  have hpd : ¬ p ∣ D.host.d := by
    intro h; apply hsq'; refine ⟨0, ?_⟩
    rw [(ZMod.natCast_eq_zero_iff _ _).2 h]; ring
  have hcmby : Formalism.L2.Th1.CM.HasCMBy D.host.d L := by
    intro ω hω
    have h1 := hCM ω (by rw [← hL]; exact hω)
    rw [← hL] at h1
    have e : Formalism.L2.Th1.CM.omegaK D.host.d = Formalism.L2.Th1.F.cmTheta 1 D.host.d := by
      unfold Formalism.L2.Th1.CM.omegaK Formalism.L2.Th1.F.cmTheta; push_cast; ring
    rw [e]; exact h1
  obtain ⟨ι, hι⟩ := Formalism.L2.KerInert.lamExt p g.lam
  have hιg2 : ι L.g₂ = g.lam a2 := hι a2
  have hιg3 : ι L.g₃ = g.lam a3 := hι a3

  have hwm : wModel g.lam g.abelian₂ = Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃) := by
    have e4 : lamC g.lam (-(g2 g.abelian₂) / 4) = -(g.lam a2) / 4 := by
      have : -(g2 g.abelian₂) / 4 = ((-a2 / 4 : Qbar) : ℂ) := by rw [e2]; push_cast; rfl
      rw [this, Formalism.L2.KerInert.Sigma.lamC_coe, map_div₀, map_neg, map_ofNat]
    have e6 : lamC g.lam (-(g3 g.abelian₂) / 4) = -(g.lam a3) / 4 := by
      have : -(g3 g.abelian₂) / 4 = ((-a3 / 4 : Qbar) : ℂ) := by rw [e3]; push_cast; rfl
      rw [this, Formalism.L2.KerInert.Sigma.lamC_coe, map_div₀, map_neg, map_ofNat]
    rw [hιg2, hιg3]
    ext <;> simp [wModel, Formalism.L2.Th1.A.shortW, e4, e6]

  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε
  have hεne : ε ≠ 0 := Units.ne_zero _
  set g2' : ℂ_[p] := ε ^ 4 * ι L.g₂ with hg2'
  set g3' : ℂ_[p] := ε ^ 6 * ι L.g₃ with hg3'
  let Cε : WeierstrassCurve.VariableChange ℂ_[p] := ⟨g.C.u, 0, 0, 0⟩
  have hW0 : Cε • Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃) = Formalism.L2.Th1.A.shortW g2' g3' := by
    ext <;> simp [Cε, Formalism.L2.Th1.A.shortW, WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄, WeierstrassCurve.variableChange_a₆, hg2', hg3', hε] <;> ring
  have hgW : g.W = (g.C * Cε⁻¹) • Formalism.L2.Th1.A.shortW g2' g3' := by
    rw [G1.W, hwm, mul_smul, ← hW0, inv_smul_smul]
  obtain ⟨i1, i2, i3, i4, i6, hΔ⟩ := hOk.1
  obtain ⟨w1, w2, w3, w4, w6⟩ := hOW
  obtain ⟨k2, k3, n2, n3, nd⟩ := Formalism.L2.KerInert.Sigma.inv_good g.W h5 i1 i2 i3 i4 i6 hΔ w1 w2 w3 w4 w6
  have hW0' := Formalism.L2.KerInert.Sigma.wModel_g g.lam g.abelian₂ a2 a3 e2 e3
  obtain ⟨c2, c3⟩ := Formalism.L2.KerInert.Sigma.g_change g.C (wModel g.lam g.abelian₂)
  have gW2 : Formalism.L2.Th1.A.g₂ g.W = g2' := by
    rw [hg2', hιg2, ← hW0'.1]; exact c2
  have gW3 : Formalism.L2.Th1.A.g₃ g.W = g3' := by
    rw [hg3', hιg3, ← hW0'.2]; exact c3
  rw [gW2] at k2 n2
  rw [gW3] at k3 n3
  rw [gW2, gW3] at nd
  have hgood : Formalism.L2.Th1.CM.IsGoodModel p L ι g2' g3' := ⟨k2, k3, n2, n3, nd, ε, hεne, rfl, rfl⟩
  have hEnd0 := ReciprocityTheory.ChartRestriction.L1.end_integral D.host.d L hd4 hcmby p h5 hpd hsq' ι g2' g3' hgood
  rw [ReciprocityTheory.ChartRestriction.L1.lgS_eq_logSer, Formalism.L2.Th1.A.uSerEq ℂ_[p] g2' g3'] at hEnd0
  have hE0 : Formalism.L2.Th1.C.EndInt (RB p) (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW g2' g3'))
      (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW g2' g3')) (ι (Formalism.L2.Th1.CM.omegaK D.host.d)) := fun n => hEnd0 n

  obtain ⟨t2, -⟩ := norm_two_three (p := p) h5
  have t4 : ‖(4 : ℂ_[p])‖ = 1 := by
    rw [show (4 : ℂ_[p]) = 2 * 2 by norm_num, norm_mul, t2, one_mul]
  have hΔ0 : ‖(Formalism.L2.Th1.A.shortW g2' g3').Δ‖ = 1 := by
    have e : (Formalism.L2.Th1.A.shortW g2' g3').Δ = g2' ^ 3 - 27 * g3' ^ 2 := by
      simp only [Formalism.L2.Th1.A.shortW, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    rw [e]; exact nd
  have hcoef0 : Formalism.L2.Th1.C.CoeffIn (RB p) (Formalism.L2.Th1.A.shortW g2' g3') := by
    refine ⟨(RB p).zero_mem, (RB p).zero_mem, (RB p).zero_mem, ?_, ?_⟩
    · show ‖-g2' / 4‖ ≤ 1
      rw [norm_div, norm_neg, t4, div_one]; exact n2
    · show ‖-g3' / 4‖ ≤ 1
      rw [norm_div, norm_neg, t4, div_one]; exact n3
  have j1 : ‖((g.C * Cε⁻¹) • Formalism.L2.Th1.A.shortW g2' g3').a₁‖ ≤ 1 := by rw [← hgW]; exact i1
  have j2 : ‖((g.C * Cε⁻¹) • Formalism.L2.Th1.A.shortW g2' g3').a₂‖ ≤ 1 := by rw [← hgW]; exact i2
  have j3 : ‖((g.C * Cε⁻¹) • Formalism.L2.Th1.A.shortW g2' g3').a₃‖ ≤ 1 := by rw [← hgW]; exact i3
  have jΔ : ‖((g.C * Cε⁻¹) • Formalism.L2.Th1.A.shortW g2' g3').Δ‖ = 1 := by rw [← hgW]; exact hΔ
  obtain ⟨hu, hui, hr, hs, ht⟩ := vc_params h5 (Formalism.L2.Th1.A.shortW g2' g3') rfl rfl rfl hΔ0 (g.C * Cε⁻¹) j1 j2 j3 jΔ
  refine ⟨ι, hι, ?_⟩
  rw [hgW]
  exact Formalism.L2.KerInert.VC.endInt_varChange _ hcoef0 _ hu.le hui.le hr hs ht _ hE0


open Formalism.L2.Th1.C.Pts in
theorem endInt_OK (D : D7) (p : ℕ) [Fact p.Prime] (g : G1 p) (hOk : g.Ok) (ι : ℂ ≃+* ℂ_[p])
    (hι : Formalism.L2.KerInert.IotaExt g.lam ι)
    (hEg : Formalism.L2.Th1.C.EndInt (RB p) (Formalism.L2.Th1.A.logSer g.W) (Formalism.L2.Th1.A.expSer g.W)
      (ι (Formalism.L2.Th1.CM.omegaK D.host.d))) (a : 𝓞 D.host.K) :
    Formalism.L2.Th1.C.EndInt (RB p) (Formalism.L2.Th1.A.logSer g.W) (Formalism.L2.Th1.A.expSer g.W) (tauK D g.lam (a : D.host.K)) := by
  obtain ⟨hLP, -, -, hFG, -⟩ := Formalism.L2.Th1.C.curveFrame ℂ_[p] (RB p) g.W (coeffIn_g g hOk)
  have hint : ∀ m : ℤ, Formalism.L2.Th1.C.EndInt (RB p) (Formalism.L2.Th1.A.logSer g.W) (Formalism.L2.Th1.A.expSer g.W) (m : ℂ_[p]) := by
    intro m
    induction m using Int.induction_on with
    | zero => simpa using endInt_zero (R := RB p) hLP
    | succ i ih => push_cast; exact endInt_add hLP hFG ih (endInt_one hLP)
    | pred i ih =>
      have e : ((-(i : ℤ) - 1 : ℤ) : ℂ_[p]) = ((-(i : ℤ) : ℤ) : ℂ_[p]) + -1 := by push_cast; ring
      rw [e]; exact endInt_add hLP hFG ih (endInt_neg hLP hFG (endInt_one hLP))
  obtain ⟨ω, hω, hspan⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.covA_span D.host.K D.host.d (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.discriminant_mod_four D)
    ⟨D.host.sqrtMinusD, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_sqrt_mem D⟩ (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_sqrt_sq D)
    (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_finrank_K D)
  have hρι : ∀ x : D.host.K, Formalism.MainNotions.Ext.tauKp D g.lam x = ι (D.host.φ₀ (x : D.host.E)) := by
    intro x
    rw [Formalism.MainNotions.Ext.tauKp_apply]
    exact (Formalism.L2.KerInert.lamCIota p g.lam ι hι).1 _ (Formalism.MainNotions.Ext.test_vector_mem_schwartz_bruhat D _)
  set xs : D.host.K := ⟨D.host.sqrtMinusD, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_sqrt_mem D⟩ with hxs
  have hx2 : (D.host.φ₀ (xs : D.host.E)) ^ 2 = -(D.host.d : ℂ) := by
    have h := congrArg (fun y : D.host.K => D.host.φ₀ (y : D.host.E)) (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_sqrt_sq D)
    rw [← hxs] at h
    push_cast at h
    rw [map_pow] at h
    rw [h, map_neg, map_natCast]
  have hom : (2 * Formalism.L2.Th1.CM.omegaK D.host.d - 1) ^ 2 = -(D.host.d : ℂ) := by
    unfold Formalism.L2.Th1.CM.omegaK
    have hsq : ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 = (D.host.d : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; rfl
    linear_combination (-1 : ℂ) * hsq + (((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2) * Complex.I_sq
  have h2E : ((2 : D.host.K) : D.host.E) = 2 := by
    rw [show (2 : D.host.K) = 1 + 1 by norm_num]; push_cast; norm_num
  have hωφ : D.host.φ₀ ((ω : D.host.K) : D.host.E) = (1 + D.host.φ₀ (xs : D.host.E)) / 2 := by
    rw [hω]; push_cast; simp only [map_div₀, map_add (f := _), map_one]; rw [h2E, map_ofNat]
  have hρω : Formalism.L2.Th1.C.EndInt (RB p) (Formalism.L2.Th1.A.logSer g.W) (Formalism.L2.Th1.A.expSer g.W)
      (Formalism.MainNotions.Ext.tauKp D g.lam (ω : D.host.K)) := by
    rw [hρι, hωφ]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hx2.trans hom.symm) with h | h
    · have e : (1 + D.host.φ₀ (xs : D.host.E)) / 2 = Formalism.L2.Th1.CM.omegaK D.host.d := by
        rw [h]; ring
      rw [e]; exact hEg
    · have e : ι ((1 + D.host.φ₀ (xs : D.host.E)) / 2) = 1 + -ι (Formalism.L2.Th1.CM.omegaK D.host.d) := by
        have e' : (1 + D.host.φ₀ (xs : D.host.E)) / 2 = 1 - Formalism.L2.Th1.CM.omegaK D.host.d := by
          rw [h]; ring
        rw [e', map_sub, map_one]; ring
      rw [e]; exact endInt_add hLP hFG (endInt_one hLP) (endInt_neg hLP hFG hEg)
  have hc : ∀ k : ℤ, ((k : 𝓞 D.host.K) : D.host.K) = (k : D.host.K) := fun k => by
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, map_intCast]
  have htau : tauK D g.lam (a : D.host.K) = Formalism.MainNotions.Ext.tauKp D g.lam (a : D.host.K) :=
    (Formalism.MainNotions.Ext.tauKp_apply D g.lam _).symm
  rw [htau]
  obtain ⟨m, n, rfl⟩ := hspan a
  have e : (((m : 𝓞 D.host.K) + (n : 𝓞 D.host.K) * ω : 𝓞 D.host.K) : D.host.K) =
      (m : D.host.K) + (n : D.host.K) * (ω : D.host.K) := by
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, map_add (f := _), map_mul, map_intCast, map_intCast,
      ← NumberField.RingOfIntegers.coe_eq_algebraMap]
  rw [e, map_add (f := _), map_mul, map_intCast, map_intCast]
  exact endInt_add hLP hFG (hint m) (endInt_mul hLP (hint n) hρω)

theorem endIntInert_of (hInv : Formalism.L2.KerInert.Sigma.InvAlg) : EndIntInert := by
  intro D p _ cc δ g hAt h5 hIn hOW α hα
  have hOk : g.Ok := hAt.2.2.2.2
  obtain ⟨ι, hι, hEg⟩ := endInt_omega hInv D p cc δ g hAt h5 hIn hOW
  obtain ⟨hLP, -, -, -, -⟩ := Formalism.L2.Th1.C.curveFrame ℂ_[p] (RB p) g.W (coeffIn_g g hOk)
  have hRB : IsClosed ((RB p : Subring ℂ_[p]) : Set ℂ_[p]) :=
    isClosed_le continuous_norm continuous_const
  have hcl := Formalism.L2.Th1.C.endIntClosed ℂ_[p] (RB p) hRB (Formalism.L2.Th1.A.logSer g.W) (Formalism.L2.Th1.A.expSer g.W) hLP.1
  have hmaps : Set.MapsTo Prod.fst (Set.range fun a : 𝓞 D.host.K =>
      (tauK D g.lam (a : D.host.K), tauKc D g.lam (a : D.host.K)))
      {c : ℂ_[p] | Formalism.L2.Th1.C.EndInt (RB p) (Formalism.L2.Th1.A.logSer g.W) (Formalism.L2.Th1.A.expSer g.W) c} := by
    rintro _ ⟨a, rfl⟩
    exact endInt_OK D p g hOk ι hι hEg a
  exact integralMv_of_endInt g hOk α.1 (hcl.closure_subset (map_mem_closure continuous_fst hα hmaps))

end Main

end Formalism.L2.KerInert.IwahoriBlocks

namespace Formalism.L2.KerInert

theorem endomorphisms_integral_inert : EndIntInert := by
  exact IwahoriBlocks.endIntInert_of Sigma.invAlg'

end Formalism.L2.KerInert
