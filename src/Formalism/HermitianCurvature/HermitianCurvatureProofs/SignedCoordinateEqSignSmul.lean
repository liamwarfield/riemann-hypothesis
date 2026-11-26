module

public import Formalism.HermitianCurvature.TopDensNonnegOfKappa
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftMemMatrixAlgebra
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstNormRealNonneg
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RecursionWithDensities
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PoissonSummationDecay
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelSizesJointMean
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualCovolumeChangeOfVariables
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SignedCoordinateEqSignSmul
open MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

theorem signed_coordinate_eq_sign_smul (P : M.Par) (l : ℕ) (Y : ℂ) :
    (fun ρ => M.x0 P l ρ Y) = M.sgn P l • fun ρ => M.xC P ρ Y := by
  funext ρ
  simp only [Pi.smul_apply, smul_eq_mul, M.x0, M.sgn, M.xC]

theorem xKappaOfNF : XKappaOfNF := by
  intro hNF hPos Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hD
  obtain ⟨hPl, -, hL, hQQ, -, hinv, -, hLS⟩ := hD
  obtain ⟨d, hdL, hdS, hdR, hdQ⟩ := hNF Wp Wq P z z' π π' hPl X
  have hfn : ∀ i j : Fin 6,
      (∀ x ∈ DomR P.k P.r z z', fnVal P.k P.r z z' i x.2 * fnVal P.k P.r z z' j x.2 = 1) →
      X.fn i * X.fn j = 1 := by
    intro i j hij
    refine LinearMap.ext fun Φ => Subtype.ext (funext fun c => funext fun g => ?_)
    rw [Module.End.mul_apply, Module.End.one_apply]
    by_cases hx : (c, g) ∈ DomR P.k P.r z z'
    · have e1 := X.fn_apply i (X.fn j Φ) (c, g) hx
      have e2 := X.fn_apply j Φ (c, g) hx
      dsimp only at e1 e2
      rw [e1, e2, smul_smul, hij (c, g) hx, one_smul]
    · have e1 := (X.fn i (X.fn j Φ)).2.1 (c, g) hx
      have e2 := Φ.2.1 (c, g) hx
      dsimp only at e1 e2
      rw [e1, e2]
  have hG : ∀ x ∈ DomR P.k P.r z z', fnVal P.k P.r z z' 5 x.2 * fnVal P.k P.r z z' 4 x.2 = 1 := by
    intro x hx
    simp only [fnVal]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hx.2.2.ne')
  have hG' : ∀ x ∈ DomR P.k P.r z z', fnVal P.k P.r z z' 4 x.2 * fnVal P.k P.r z z' 5 x.2 = 1 := by
    intro x hx
    simp only [fnVal]
    exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hx.2.2.ne')
  have hGinv : L.GGi * L.GG = 1 := by
    rw [hL.2.2.2.2.2.2.2.2.2.2.1, hL.2.2.2.2.2.2.2.2.2.2.2.1]
    refine Prod.ext ?_ ?_
    · show X.fn 5 * X.fn 4 = 1
      exact hfn 5 4 hG
    · show MulOpposite.op (X.fn 5) * MulOpposite.op (X.fn 4) = MulOpposite.op 1
      rw [← MulOpposite.op_mul, hfn 4 5 hG']
  have hGG : L.GG = d.L.GG := hL.2.2.2.2.2.2.2.2.2.2.1.trans hdL.2.2.2.2.2.2.2.2.2.2.1.symm
  have hx : ∀ Y, st.x Y = d.κ fun ρ => M.x0 P l0 ρ Y := by
    intro Y
    have h1 := hLS.tau Y
    have h2 : d.QQ Y 1 1 = d.L.GG * d.x Y := by simp [NFData.QQ]
    rw [hQQ Y, hdQ Y, Matrix.smul_apply, h2, ← hGG, ← mul_smul_comm] at h1
    have h3 : st.x Y = M.sgn P l0 • d.x Y := by
      calc st.x Y = L.GGi * (L.GG * st.x Y) := by rw [← mul_assoc, hGinv, one_mul]
        _ = L.GGi * (L.GG * (M.sgn P l0 • d.x Y)) := by rw [← h1]
        _ = _ := by rw [← mul_assoc, hGinv, one_mul]
    rw [h3, NFData.x, signed_coordinate_eq_sign_smul, map_smul]
  have hxi : ∀ Y ∈ st.inv, st.xi Y = d.κ fun ρ => (M.x0 P l0 ρ Y)⁻¹ := by
    intro Y hY
    have hne : ∀ ρ, M.x0 P l0 ρ Y ≠ 0 := by
      intro ρ
      have hY' := hY
      rw [hinv] at hY'
      have e := congrFun (signed_coordinate_eq_sign_smul P l0 Y) ρ
      simp only [Pi.smul_apply, smul_eq_mul] at e
      rw [e]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (hY' ρ)
    have hprod : (d.κ fun ρ => M.x0 P l0 ρ Y) * (d.κ fun ρ => (M.x0 P l0 ρ Y)⁻¹) = 1 := by
      rw [← map_mul, ← map_one d.κ]
      congr 1
      funext ρ
      simp [hne ρ]
    calc st.xi Y
        = st.xi Y * ((d.κ fun ρ => M.x0 P l0 ρ Y) * (d.κ fun ρ => (M.x0 P l0 ρ Y)⁻¹)) := by
          rw [hprod, mul_one]
      _ = (st.xi Y * st.x Y) * (d.κ fun ρ => (M.x0 P l0 ρ Y)⁻¹) := by rw [hx Y, mul_assoc]
      _ = _ := by rw [(hLS.x_xi Y hY).2, one_mul]
  exact ⟨d.κ, hx, hxi, hPos Wp Wq P z z' π π' hPl X d hdL hdS hdR hdQ⟩

end Formalism.FourierDecayAlt.P5
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarScaling
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.HaarScaling

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem haar_smul {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) (c : ℝ≥0) (hc : 0 < c) :
    IsHaarOn U (c • μ) := _root_.Formalism.FourierDecayAlt.P.SettingConstruction.haar_smul (k := k) (r := r) (U := U) (μ := μ) h c hc

section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def scaleG (D : RealPlaceData k r Wp Wq) (c : ℝ≥0) (hc : 0 < c) : RealPlaceData k r Wp Wq :=
  { D with μG := c • D.μG, haarG := haar_smul D.haarG c hc }

theorem iteratedDeriv_two_const_mul (c : ℂ) (f : ℝ → ℂ) :
    iteratedDeriv 2 (fun x => c * f x) = fun x => c * iteratedDeriv 2 f x := by
  have h2 : ∀ g : ℝ → ℂ, iteratedDeriv 2 g = deriv (deriv g) := by
    intro g
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2, h2, deriv_const_mul_field', deriv_const_mul_field']

theorem oneMinusDD_const_mul (c : ℂ) (h : ℝ → ℝ → ℂ) (t₁ t₂ : ℝ) :
    oneMinusDD (fun a b => c * h a b) t₁ t₂ = c * oneMinusDD h t₁ t₂ := by
  simp only [oneMinusDD, iteratedDeriv_two_const_mul, ← mul_sub]

variable [FiniteDimensional ℂ Wq]

theorem ph_scale (D : RealPlaceData k r Wp Wq) (c : ℝ≥0) (hc : 0 < c) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (p : SS k r) :
    Ph (scaleG D c hc) F F' p = ((c : ℝ) : ℂ) * Ph D F F' p := by
  have hμ : (scaleG D c hc).μG = c • D.μG := rfl
  unfold Ph
  rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  rfl

theorem betaInf_scale (D : RealPlaceData k r Wp Wq) (c : ℝ≥0) (hc : 0 < c) (F F' : Mat k r → (Wq →L[ℂ] Wp)) :
    betaInf (scaleG D c hc) F F' = ((c : ℝ) : ℂ) * betaInf D F F' := by
  have hreg : ∀ p, regBracket (scaleG D c hc) F F' p =
      fun a b => ((c : ℝ) : ℂ) * regBracket D F F' p a b := by
    intro p
    funext a b
    have hχ : (scaleG D c hc).χ = D.χ := rfl
    simp only [regBracket]
    rw [ph_scale, hχ]
    ring
  have hz : (scaleG D c hc).z = D.z := rfl
  have hz' : (scaleG D c hc).z' = D.z' := rfl
  have hS : (scaleG D c hc).μSS = D.μSS := rfl
  unfold betaInf betaInfTau
  simp only [hreg, hz, hz', hS, oneMinusDD_const_mul, mul_assoc, integral_const_mul]
  rw [← integral_const_mul]
  congr 1
  funext p
  ring

theorem beta_scale (D : RealPlaceData k r Wp Wq) (c : ℝ≥0) (hc : 0 < c) (F F' : Mat k r → (Wq →L[ℂ] Wp)) :
    beta (scaleG D c hc) F F' = beta D F F' := rfl

end

end Formalism.FourierDecayAlt.P.HaarScaling

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.HaarScaling

theorem lemma_b_normalised_of_parts : Formalism.FourierDecayAlt.B2.LemmaBNormFromParts := by
  intro hC hJ hD hI k r Wp Wq _ _ _ _ _ _ D A hA hF
  exact hC k r Wp Wq D A hA hF (hJ k r Wp Wq D) (hD k r Wp Wq D) (hI k r Wp Wq D A hA)

theorem lemma_b_any_measure_from_normalised : Formalism.FourierDecayAlt.B2.LemmaBAnyFromNorm := by
  intro hN hB k r Wp Wq _ _ _ _ _ _ D A hA
  obtain ⟨c, ⟨hc, hF⟩, -⟩ := hB k r Wp Wq D
  have hF' : IntFormula (scaleG D c hc) := hF
  obtain ⟨h1, h2, h3, h4⟩ := hN k r Wp Wq (scaleG D c hc) A hA hF'
  refine ⟨c, hc, hF, h1, ?_, ?_, h4⟩
  · intro F F' hF1 hF2
    rw [← beta_scale D c hc F F', h2 F F' hF1 hF2, betaInf_scale]
  · intro UU Θ hU hS hC F F' hF1 hF2 hs1 hs2 hI1 hI2 hI3 hI4 hIC
    exact h3 UU Θ hU hS hC F F' hF1 hF2 hs1 hs2 hI1 hI2 hI3 hI4
      (fun p hp T hT i j hij hj => (hIC p hp T hT i j hij hj).smul_measure_nnreal)

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.HaarScaling

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

end Formalism.FourierDecayAlt.P.HaarScaling
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HsInnerAddSmulRight
open MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

section HS

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsInner_add_smul_left (A A' C : Wq →L[ℂ] Wp) (a : ℂ) :
    B.hsInner (A + a • A') C = B.hsInner A C + a * B.hsInner A' C := by
  simp only [B.hsInner, B.hsVec, PiLp.inner_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, inner_add_right, inner_smul_right, Finset.sum_add_distrib, Finset.mul_sum]

theorem hsInner_add_smul_right (A C C' : Wq →L[ℂ] Wp) (a : ℂ) :
    B.hsInner A (C + a • C') = B.hsInner A C + conj a * B.hsInner A C' := by
  simp only [B.hsInner, B.hsVec, PiLp.inner_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, inner_add_left, inner_smul_left, Finset.sum_add_distrib, Finset.mul_sum]

end HS

section Forms

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem act_add_smul (M : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (x x' : Ix S → RadSp k r z z' π π') (a : ℂ) :
    act M (x + a • x') = act M x + a • act M x' := by
  funext e
  simp only [act, Pi.add_apply, Pi.smul_apply, map_add (f := _), map_smul, Finset.sum_add_distrib, Finset.smul_sum]

theorem pairAt_add_smul_left (μ : Measure (Mt k r)) (Φ Φ' Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) (a : ℂ)
    (h1 : Integrable (fun g : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) μ)
    (h2 : Integrable (fun g : Mt k r => B.hsInner ((Φ' : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) μ) :
    pairAt μ (Φ + a • Φ') Ψ c = pairAt μ Φ Ψ c + a * pairAt μ Φ' Ψ c := by
  unfold pairAt
  simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, hsInner_add_smul_left]
  rw [integral_add h1 (h2.const_mul a), integral_const_mul]

theorem pairAt_add_smul_right (μ : Measure (Mt k r)) (Φ Ψ Ψ' : RadSp k r z z' π π') (c : Fin r → ℂ) (a : ℂ)
    (h1 : Integrable (fun g : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) μ)
    (h2 : Integrable (fun g : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((Ψ' : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) μ) :
    pairAt μ Φ (Ψ + a • Ψ') c = pairAt μ Φ Ψ c + conj a * pairAt μ Φ Ψ' c := by
  unfold pairAt
  simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, hsInner_add_smul_right]
  rw [integral_add h1 (h2.const_mul (conj a)), integral_const_mul]

theorem form_add_smul_left (μ : Measure (Mt k r)) (i : Fin (r + 1)) (u u' y : Ix S → RadSp k r z z' π π')
    (c : Fin r → ℂ) (a : ℂ)
    (hin : ∀ (c' : Cf r i) (b : Ix S), Integrable (fun g : Mt k r =>
      B.hsInner ((u b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))
        ((y b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))) μ)
    (hin' : ∀ (c' : Cf r i) (b : Ix S), Integrable (fun g : Mt k r =>
      B.hsInner ((u' b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))
        ((y b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))) μ)
    (hout : Integrable (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ b, pairAt μ (u b) (y b) (glue i c c')))
    (hout' : Integrable (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ b, pairAt μ (u' b) (y b) (glue i c c'))) :
    form μ i (u + a • u') y c = form μ i u y c + a * form μ i u' y c := by
  unfold form
  have hpt : (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ b, pairAt μ ((u + a • u') b) (y b) (glue i c c')) =
      fun c' => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (u b) (y b) (glue i c c') +
        a * (((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (u' b) (y b) (glue i c c')) := by
    funext c'
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [Finset.sum_congr rfl fun b _ => pairAt_add_smul_left μ (u b) (u' b) (y b) _ a (hin c' b) (hin' c' b),
      Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hpt, integral_add hout (hout'.const_mul a), integral_const_mul]

theorem form_add_smul_right (μ : Measure (Mt k r)) (i : Fin (r + 1)) (u y y' : Ix S → RadSp k r z z' π π')
    (c : Fin r → ℂ) (a : ℂ)
    (hin : ∀ (c' : Cf r i) (b : Ix S), Integrable (fun g : Mt k r =>
      B.hsInner ((u b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))
        ((y b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))) μ)
    (hin' : ∀ (c' : Cf r i) (b : Ix S), Integrable (fun g : Mt k r =>
      B.hsInner ((u b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))
        ((y' b : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))) μ)
    (hout : Integrable (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ b, pairAt μ (u b) (y b) (glue i c c')))
    (hout' : Integrable (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ b, pairAt μ (u b) (y' b) (glue i c c'))) :
    form μ i u (y + a • y') c = form μ i u y c + conj a * form μ i u y' c := by
  unfold form
  have hpt : (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ b, pairAt μ (u b) ((y + a • y') b) (glue i c c')) =
      fun c' => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (u b) (y b) (glue i c c') +
        conj a * (((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (u b) (y' b) (glue i c c')) := by
    funext c'
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [Finset.sum_congr rfl fun b _ => pairAt_add_smul_right μ (u b) (y b) (y' b) _ a (hin c' b) (hin' c' b),
      Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hpt, integral_add hout (hout'.const_mul (conj a)), integral_const_mul]

end Forms

theorem formSesqOfInt : FormSesqOfInt := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' μ L st l0 K hI w hw i c hc x hx x' hx' y hy a
  have hK : ∀ v : Ix S → RadSp P.k P.r z z' π π', v ∈ Submodule.pi Set.univ (fun _ : Ix S => K i) → InK (K i) v :=
    fun v hv b => (Submodule.mem_pi.mp hv) b (Set.mem_univ b)
  have h1 := hI w hw i c hc x y (hK x hx) (hK y hy)
  have h2 := hI w hw i c hc x' y (hK x' hx') (hK y hy)
  have h3 := hI w hw i c hc y x (hK y hy) (hK x hx)
  have h4 := hI w hw i c hc y x' (hK y hy) (hK x' hx')
  constructor
  · show form μ i (act (RRi L st i w) (x + a • x')) y c =
      form μ i (act (RRi L st i w) x) y c + a * form μ i (act (RRi L st i w) x') y c
    rw [act_add_smul]
    exact form_add_smul_left μ i _ _ y c a h1.1 h2.1 h1.2 h2.2
  · show form μ i (act (RRi L st i w) y) (x + a • x') c =
      form μ i (act (RRi L st i w) y) x c + conj a * form μ i (act (RRi L st i w) y) x' c
    exact form_add_smul_right μ i _ x x' c a h3.1 h4.1 h3.2 h4.2

end Formalism.FourierDecayAlt.P5
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ConcreteBoundOfRecursion
namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C

noncomputable section

theorem real_inputs_by_parts : C.RealInputsConcreteOfParts := by
  intro hEmb hEF hTD hLG hGram hWP hWave hPI hLift hBlock hE hCut E _ _ _ Wp Wq _ _ _ _ S jv H _ _ Vt C₄ hg1 hg2 hP hG hI hP1 hP23 hT hLE hPG Kr hK0 Th e
  exact ⟨hGram E Wp Wq S hP hG Kr hK0 Th e, hWP E Wp Wq S hG Kr hK0 Th e, hWave E Wp Wq S hG hI hP1 Kr hK0 Th e,
    hPI hEmb hEF hTD hLG E Wp Wq S hg1 hg2 hP hG hI Kr hK0 Th e, hLift E Wp Wq S hP23 Kr hK0 Th e,
    hBlock E Wp Wq S C₄ hT Kr hK0 Th e, hE E Wp Wq S jv hG hLE Kr hK0 Th e,
    hCut E Wp Wq S H Vt hPG Kr hK0 Th e⟩

theorem real_inputs_concrete_holds : C.RealInputsConcrete :=
  real_inputs_by_parts embedding_facts euclidean_frame trace_dual_alt
    lattice_facts_general gram_positive_semidefinite words_pos_of_parts wave_estimate_of_integral
    poisson_input_of_parts lift_estimate_of_base block_estimate_of_base level_zero_estimate_product
    cutoff_of_parts

end

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.QxPIRttLevel
theorem Formalism.FourierDecayAlt.P.rtt_level_from_upper : Formalism.FourierDecayAlt.Q.RTTLevelFromUpper := by
  intro hU hLT hGI hFF _ k r i
  induction i using Fin.cases with
  | succ l => exact hU k r l
  | zero =>
    intro Wp Wq _ _ _ _ z z' π π' D hz hz' hD J hJ g hg u v a b c d
    obtain ⟨π₁, π₁', D₁, f, hw, hw', hD₁, hf, hfJ⟩ := hFF Wp Wq k r z z' π π' D hz hz' hD J hJ
    have key : ∀ (Y Y' : ℂ) (p q p' q' : Fin 2),
        Formalism.FourierDecayAlt.Q.tL k (1 + r) (Formalism.QuantumDeterminants.liftVec k 1 r z) (Formalism.QuantumDeterminants.liftVec k 1 r z') ⟨1, by omega⟩
                  Y p q (Formalism.FourierDecayAlt.Q.tL k (1 + r) (Formalism.QuantumDeterminants.liftVec k 1 r z) (Formalism.QuantumDeterminants.liftVec k 1 r z')
                    ⟨1, by omega⟩ Y' p' q' f) (Formalism.QuantumDeterminants.ιLev k 1 r g) =
          Formalism.FourierDecayAlt.Q.tL k r z z' 0 Y p q (Formalism.FourierDecayAlt.Q.tL k r z z' 0 Y' p' q' J) g := by
      intro Y Y' p q p' q'
      rw [hLT (Wq →L[ℂ] Wp) k 1 r z z' Y p q _ g hg.1.1]
      refine (Formalism.FourierDecayAlt.P.Qx2.ll_tL (i := 0) hD.1 z z' Y p q).loc _ _ ?_ g hg
      intro x hx
      rw [hLT (Wq →L[ℂ] Wp) k 1 r z z' Y' p' q' f x hx.1.1]
      refine (Formalism.FourierDecayAlt.P.Qx2.ll_tL (i := 0) hD.1 z z' Y' p' q').loc _ _ ?_ x hx
      intro y hy
      exact (hfJ y hy.1.1).2
    have hιg : Formalism.QuantumDeterminants.ιLev k 1 r g ∈ Formalism.FourierDecayAlt.Q.Glev k (1 + r) ⟨1, by omega⟩ ∩ D₁ := by
      refine ⟨?_, (hfJ g hg.1.1).1.mpr hg.2⟩
      rw [hGI k 1 r]
      exact ⟨g, hg.1.1, rfl⟩
    have h1 : Formalism.FourierDecayAlt.Q.RTTAt k (1 + r) ⟨1, by omega⟩ := hU k (1 + r) ⟨0, by omega⟩
    have h := h1 Wp Wq _ _ π₁ π₁' D₁ hw hw' hD₁ f hf _ hιg u v a b c d
    simp only [key] at h
    exact h
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ThirdPolynomialExpansion
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3

theorem succAbove_val {n : ℕ} (p : Fin (n + 1)) (l : Fin n) :
    (p.succAbove l).val = if l.val < p.val then l.val else l.val + 1 := by
  unfold Fin.succAbove
  split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def] <;> omega

private theorem sgnW_succ' (s : ℕ) : sgnW (s + 1) = (-1) ^ s * sgnW s := by
  unfold sgnW
  rw [← pow_add]
  congr 1
  cases s with
  | zero => rfl
  | succ k =>
    have e : (k + 1 + 1) * (k + 1 + 1 - 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1) := by
      simp only [Nat.add_sub_cancel]
      ring
    rw [e, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
    ring

theorem zb_det (i0 s : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) :
    (Matrix.of fun a b : Fin (i0 + s) => Zb i0 s h t a.val b.val).det = h.det * t ^ s * sgnW s := by
  induction s with
  | zero =>
    have hs : sgnW 0 = 1 := by simp [sgnW]
    rw [hs, pow_zero, mul_one, mul_one]
    show Matrix.det (Matrix.of fun a b : Fin i0 => Zb i0 0 h t a.val b.val) = _
    congr 1
    ext a b
    simp [Zb, a.isLt, b.isLt]
  | succ s ih =>
    rw [Matrix.det_succ_row _ (⟨i0, by omega⟩ : Fin (i0 + s + 1)), Finset.sum_eq_single (Fin.last _)]
    · have hsub : (Matrix.of fun a b : Fin (i0 + (s + 1)) => Zb i0 (s + 1) h t a.val b.val).submatrix
          (⟨i0, by omega⟩ : Fin (i0 + s + 1)).succAbove (Fin.last (i0 + s)).succAbove =
          Matrix.of fun a b : Fin (i0 + s) => Zb i0 s h t a.val b.val := by
        ext a b
        simp only [Matrix.submatrix_apply, Matrix.of_apply, succAbove_val, Fin.succAbove_last,
          Fin.coe_castSucc]
        have hb := b.isLt
        by_cases ha : (a : ℕ) < i0
        · simp only [ha, if_true]
          unfold Zb
          split_ifs <;> first | rfl | omega
        · simp only [ha, if_false]
          unfold Zb
          split_ifs <;> first | rfl | omega
      rw [hsub, ih, sgnW_succ']
      have he : Zb i0 (s + 1) h t i0 (i0 + s) = t := by
        simp only [Zb]
        rw [dite_eq_right (lt_irrefl _), if_pos (by omega)]
      simp only [Matrix.of_apply, Fin.val_last]
      rw [he]
      rw [show i0 + (i0 + s) = 2 * i0 + s by ring, pow_add, pow_mul]
      norm_num
      ring
    · intro j _ hj
      have hj' : (j : ℕ) ≠ i0 + s := fun e => hj (Fin.ext (by simp [e]))
      have he : Zb i0 (s + 1) h t i0 j = 0 := by
        have := j.isLt
        simp only [Zb]
        rw [dite_eq_right (lt_irrefl _), if_neg (by omega)]
      simp only [Matrix.of_apply]
      rw [he, mul_zero, zero_mul]
    · intro hn
      exact absurd (Finset.mem_univ _) hn

theorem derivative_leading_zb : DleadZb := by
  intro i0 s h t
  refine ⟨?_, zb_det i0 s h t⟩
  unfold Dlead
  congr 1
  ext a b
  simp [Zb, a.isLt, b.isLt]

theorem minors_first_case : MinorsFirstCase := by
  intro i0 s' h t c
  by_cases hc : c.val = i0
  · rw [if_pos hc, ← zb_det i0 s' h t]
    congr 1
    ext a l
    simp only [Matrix.of_apply, succAbove_val, hc]
    have hl := l.isLt
    by_cases hl0 : (l : ℕ) < i0
    · simp only [hl0, if_true]
      unfold Zb
      split_ifs <;> first | rfl | omega
    · simp only [hl0, if_false]
      unfold Zb
      split_ifs <;> first | rfl | omega
  · rw [if_neg hc]
    have hne : (⟨i0, by omega⟩ : Fin (i0 + s' + 1)) ≠ c := fun e => hc (by rw [← e])
    obtain ⟨l0, hl0⟩ := Fin.exists_succAbove_eq hne
    apply Matrix.det_eq_zero_of_column_eq_zero l0
    intro a
    simp only [Matrix.of_apply, hl0]
    have ha := a.isLt
    unfold Zb
    split_ifs <;> first | rfl | omega

theorem third_polynomial_expansion : MinorsThirdCase := by
  intro i0 s'' h t
  rw [← zb_det i0 s'' h t]
  congr 1
  ext a b
  simp only [Matrix.of_apply, succAbove_val]
  have ha := a.isLt
  have hb := b.isLt
  by_cases ha0 : (a : ℕ) < i0 <;> by_cases hb0 : (b : ℕ) < i0 <;>
    simp only [ha0, hb0, if_true, if_false] <;>
    unfold Zb <;> split_ifs <;> first | rfl | omega

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselScaling
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.BesselScaling

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem haar_smul {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) (c : ℝ≥0) (hc : 0 < c) :
    IsHaarOn U (c • μ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [smul_apply, h.conc, smul_zero]
  · intro a ha
    have hcont : Continuous (lmulM a : Mt k r → Mt k r) := by
      unfold lmulM
      exact (continuous_const (y := a)).matrix_mul (continuous_id (X := Mat k r))
    rw [Measure.map_smul c hcont.measurable.aemeasurable, h.left a ha]
  · intro a ha
    have hcont : Continuous (rmulF a) := by
      unfold rmulF
      exact (continuous_id (X := Mat k r)).matrix_mul continuous_const
    rw [Measure.map_smul c hcont.measurable.aemeasurable, h.right a ha]
  · intro K hK
    rw [smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (h.finite_compact K hK)
  · intro h0
    apply h.ne_zero
    have h1 : (c • μ) Set.univ = 0 := by rw [h0]; rfl
    rw [smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd (by exact_mod_cast h2 : c = 0) hc.ne'
    · exact Measure.measure_univ_eq_zero.mp h2

section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def scaleG (D : RealPlaceData k r Wp Wq) (c : ℝ≥0) (hc : 0 < c) : RealPlaceData k r Wp Wq :=
  { D with μG := c • D.μG, haarG := haar_smul D.haarG c hc }

theorem iteratedDeriv_two_const_mul (c : ℂ) (f : ℝ → ℂ) :
    iteratedDeriv 2 (fun x => c * f x) = fun x => c * iteratedDeriv 2 f x := by
  have h2 : ∀ g : ℝ → ℂ, iteratedDeriv 2 g = deriv (deriv g) := by
    intro g
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2, h2, deriv_const_mul_field', deriv_const_mul_field']

theorem oneMinusDD_const_mul (c : ℂ) (h : ℝ → ℝ → ℂ) (t₁ t₂ : ℝ) :
    oneMinusDD (fun a b => c * h a b) t₁ t₂ = c * oneMinusDD h t₁ t₂ := by
  simp only [oneMinusDD, iteratedDeriv_two_const_mul, ← mul_sub]

variable [FiniteDimensional ℂ Wq]

theorem ph_scale (D : RealPlaceData k r Wp Wq) (c : ℝ≥0) (hc : 0 < c) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (p : SS k r) :
    Ph (scaleG D c hc) F F' p = ((c : ℝ) : ℂ) * Ph D F F' p := by
  have hμ : (scaleG D c hc).μG = c • D.μG := rfl
  unfold Ph
  rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  try rfl

theorem betaInf_scale (D : RealPlaceData k r Wp Wq) (c : ℝ≥0) (hc : 0 < c) (F F' : Mat k r → (Wq →L[ℂ] Wp)) :
    betaInf (scaleG D c hc) F F' = ((c : ℝ) : ℂ) * betaInf D F F' := by
  have hreg : ∀ p, regBracket (scaleG D c hc) F F' p =
      fun a b => ((c : ℝ) : ℂ) * regBracket D F F' p a b := by
    intro p
    funext a b
    have hχ : (scaleG D c hc).χ = D.χ := rfl
    simp only [regBracket]
    rw [ph_scale, hχ]
    ring
  have hz : (scaleG D c hc).z = D.z := rfl
  have hz' : (scaleG D c hc).z' = D.z' := rfl
  have hS : (scaleG D c hc).μSS = D.μSS := rfl
  unfold betaInf betaInfTau
  simp only [hreg, hz, hz', hS, oneMinusDD_const_mul, mul_assoc, integral_const_mul]
  rw [← integral_const_mul]
  congr 1
  funext p
  ring
end

theorem anyFromNorm : LemmaBNorm → IntNormB → LemmaBAny := by
  intro hN hB k r Wp Wq _ _ _ _ _ _ D A hA
  obtain ⟨c, ⟨hc, hF⟩, -⟩ := hB k r Wp Wq D
  have hF' : IntFormula (scaleG D c hc) := hF
  obtain ⟨h1, h2, h3, h4⟩ := hN k r Wp Wq (scaleG D c hc) A hA hF'
  refine ⟨c, hc, hF, h1, ?_, ?_, h4⟩
  · intro F F' hF1 hF2
    have hb : beta (scaleG D c hc) F F' = beta D F F' := rfl
    rw [← hb, h2 F F' hF1 hF2, betaInf_scale]
  · intro UU Θ hU hS hC F F' hF1 hF2 hs1 hs2 hI1 hI2 hI3 hI4 hIC
    exact h3 UU Θ hU hS hC F F' hF1 hF2 hs1 hs2 hI1 hI2 hI3 hI4
      (fun p hp T hT i j hij hj => (hIC p hp T hT i j hij hj).smul_measure_nnreal)

end Formalism.FourierDecayAlt.P.BesselScaling

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem lemma_b_from_xi_of_parts : Formalism.FourierDecayAlt.B2.LemmaBFromXiFromParts := by
  intro hC hJ hD hI hB hX
  have hN : LemmaBNorm := by
    intro k r Wp Wq _ _ _ _ _ _ D A hA hF
    exact hC hX k r Wp Wq D A hA hF (hJ k r Wp Wq D) (hD k r Wp Wq D) (hI k r Wp Wq D A hA)
  exact ⟨hN, Formalism.FourierDecayAlt.P.BesselScaling.anyFromNorm hN hB⟩

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.BesselScaling

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem lemmaBFromXi_of : ConjInvAll → DilJacAll → CCIntAll → IntNormB → LemmaBFromXi :=
  Formalism.FourierDecayAlt.P.lemma_b_from_xi_of_parts (fun hX => Formalism.FourierDecayAlt.P.bessel_lemma_closed_form hX Formalism.FourierDecayAlt.P.lemma_B_of_components
            Formalism.FourierDecayAlt.P.clause_of_regularized_limit Formalism.FourierDecayAlt.P.adjointness_polynomially_bounded)

end Formalism.FourierDecayAlt.P.BesselScaling
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.TopDensNonnegOfKappa
open Matrix MeasureTheory
open scoped ComplexOrder ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

namespace WordTransvectionCongruences

section Frames

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

theorem ofWord_x_congr (L : R.LevelData A r) (st st' : Fr.Start A) (hx : st'.x = st.x) (w : List (Letter ℂ S)) :
    (Fr.ofWord L st' w).x = (Fr.ofWord L st w).x := by
  induction w with
  | nil => simp [Fr.ofWord, Fr.Start.frame, hx]
  | cons l w ih =>
    simp only [Fr.ofWord]
    split_ifs <;> simp [Fr.FrameData.plus, Fr.FrameData.minus, ih, hx]

theorem ofWord_q_congr (L : R.LevelData A r) (st st' : Fr.Start A) (hq : st'.q = st.q) (w : List (Letter ℂ S)) :
    (Fr.ofWord L st' w).q = (Fr.ofWord L st w).q := by
  induction w with
  | nil => simp [Fr.ofWord, Fr.Start.frame, hq]
  | cons l w ih =>
    simp only [Fr.ofWord]
    split_ifs <;> simp [Fr.FrameData.plus, Fr.FrameData.minus, ih, hq]

theorem ofWord_xi_congr (L : R.LevelData A r) (st st' : Fr.Start A) (w : List (Letter ℂ S)) (Y : ℂ)
    (hY : st'.xi Y = st.xi Y) : (Fr.ofWord L st' w).xi Y = (Fr.ofWord L st w).xi Y := by
  induction w with
  | nil => simp [Fr.ofWord, Fr.Start.frame, hY]
  | cons l w ih =>
    simp only [Fr.ofWord]
    split_ifs <;> simp [Fr.FrameData.plus, Fr.FrameData.minus, ih, hY]

theorem ofWord_N (L : R.LevelData A r) (st : Fr.Start A) (w : List (Letter ℂ S)) :
    (Fr.ofWord L st w).N = w.length := by
  induction w with
  | nil => simp [Fr.ofWord, Fr.Start.frame]
  | cons l w ih =>
    simp only [Fr.ofWord]
    split_ifs <;> simp [Fr.FrameData.plus, Fr.FrameData.minus, ih]

theorem ofWord_c_congr (L : R.LevelData A r) (st st' : Fr.Start A) (hx : st'.x = st.x) (hq : st'.q = st.q)
    (w : List (Letter ℂ S))
    (hw : ∀ l ∈ w, st'.xi (l.pt + 1) = st.xi (l.pt + 1) ∧ st'.xi (l.pt - 1) = st.xi (l.pt - 1)) :
    (Fr.ofWord L st' w).c = (Fr.ofWord L st w).c := by
  induction w with
  | nil => simp [Fr.ofWord, Fr.Start.frame, hx, hq]
  | cons l w ih =>
    have ih' := ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    have hl := hw l List.mem_cons_self
    have hxw := ofWord_x_congr L st st' hx w
    have hqw := ofWord_q_congr L st st' hq w
    have hxi1 := ofWord_xi_congr L st st' w (l.pt + 1) hl.1
    have hxi2 := ofWord_xi_congr L st st' w (l.pt - 1) hl.2
    simp only [Fr.ofWord]
    split_ifs <;> simp [Fr.FrameData.plus, Fr.FrameData.minus, ih', hxw, hqw, hxi1, hxi2]

end Frames

section Act

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem act_diagonal (D : Ix S → Pr (RadSp k r z z' π π')) (x : Ix S → RadSp k r z z' π π') (a : Ix S) :
    act (Matrix.diagonal D) x a = (D a).1 (x a) := by
  unfold act
  rw [Finset.sum_eq_single a]
  · simp only [Matrix.diagonal_apply_eq]
  · intro b _ hb
    simp only [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
    first
      | rfl
      | simp [Pr]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem pow_apply (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hAL : IsActualLevel X L) (n : ℕ) (Φ : RadSp k r z z' π π') (p : (Fin r → ℂ) × Mx k r)
    (hp : p ∈ DomR k r z z') :
    ((((L.ζ * L.ζb * L.GGi) ^ n).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) p.1 p.2 =
      (fnVal k r z z' 0 p.2 * fnVal k r z z' 2 p.2 * fnVal k r z z' 5 p.2) ^ n •
        (Φ : Fn k r (Wq →L[ℂ] Wp)) p.1 p.2 := by
  obtain ⟨-, -, -, -, -, -, hz, -, hzb, -, -, hgi, -⟩ := hAL
  induction n generalizing Φ with
  | zero => simp only [pow_zero, one_smul]; rfl
  | succ n ih =>
    rw [pow_succ, pr_fst_mul, Module.End.mul_apply, ih, pr_fst_mul, pr_fst_mul, Module.End.mul_apply,
      Module.End.mul_apply, hz, hzb, hgi]
    simp only [mkP]
    rw [X.fn_apply 0 _ p hp, X.fn_apply 2 _ p hp, X.fn_apply 5 _ p hp, smul_smul, smul_smul, smul_smul, pow_succ]
    ring_nf

end Act

theorem hsInner_zero_left {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (V : Wq →L[ℂ] Wp) : B.hsInner 0 V = 0 := by
  unfold B.hsInner
  have h0 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
    unfold B.hsVec
    ext i
    simp
  rw [h0, inner_zero_right]

end WordTransvectionCongruences

open WordTransvectionCongruences in
theorem topDensNonnegOfKappa : TopDensNonnegOfKappa := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 K hD hl1 hlk hK
  obtain ⟨κ, hκx, hκxi, hκpos⟩ := hK
  obtain ⟨hPl, -, hAL, -, hq, -, -, -⟩ := hD
  intro w hw x _ c _ g

  let st' : Fr.Start (Pr (RadSp P.k P.r z z' π π')) :=
    { st with xi := fun Y => κ fun ρ => (M.x0 P l0 ρ Y)⁻¹ }
  have hCD := (Formalism.FourierDecayAlt.P.c_diagonal (Pr (RadSp P.k P.r z z' π π')) S P.r L st' (M.Ty P) κ
    (fun ρ Y => M.x0 P l0 ρ Y) hκx (fun Y => rfl) w).2.2
  have hc : (Fr.ofWord L st w).c = Matrix.diagonal fun e => κ fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) w e := by
    rw [← ofWord_c_congr L st st' rfl rfl w, hCD]
    · rw [← hq]
    · intro l hl
      have h := hw.1.2.2.1 l hl
      exact ⟨(hκxi _ h.2.1).symm, (hκxi _ h.2.2.1).symm⟩

  have hpos : ∀ (e : Ix S) (ρ : M.Ty P), 0 < Fr.cs (M.x0 P l0 ρ) (M.qC P) w e := by
    intro e ρ
    have h := Formalism.FourierDecayAlt.P.c_pos_truncated Formalism.FourierDecayAlt.P.interlacing_sign Formalism.FourierDecayAlt.P.q_positive_interlacing
      Formalism.FourierDecayAlt.P.q_positive_shift Formalism.FourierDecayAlt.P.cPos_true S P.k P.u P.u' (M.rho P ρ) l0 P.T P.T' w hl1 hlk
      (Formalism.FourierDecayAlt.P.types_interlace P hPl.1 ρ) hPl.1.T_pos hPl.1.T'_pos hw.2.1 hw.2.2 e
    rw [Complex.lt_def]
    exact ⟨h.1, h.2.symm⟩
  unfold topDens
  refine Finset.sum_nonneg fun e _ => ?_
  have hd : (Fr.ofWord L st w).d L = io ((L.ζ * L.ζb * L.GGi) ^ (Fr.ofWord L st w).N) *
      Matrix.diagonal fun e => κ fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) w e := by
    rw [Fr.FrameData.d, hc, Fr.wt, io, io, map_pow]
  rw [act_mul, hd, act_mul, act_io, act_diagonal]
  set Φ := act (Fr.ofWord L st w).F x e
  by_cases hp : (c, g) ∈ DomR P.k P.r z z'
  · have := pow_apply X L hAL (Fr.ofWord L st w).N ((κ fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) w e).1 Φ) (c, g) hp
    simp only at this
    rw [this, hsInner_smul_left]
    refine mul_nonneg ?_ (hκpos _ (hpos e) Φ c g)
    obtain ⟨-, -, hGG⟩ := hp
    have hre : fnVal P.k P.r z z' 0 g * fnVal P.k P.r z z' 2 g * fnVal P.k P.r z z' 5 g =
        ((Complex.normSq (zetaL P.k P.r z z' (Fin.last P.r) g) * (GGl P.k P.r z z' g)⁻¹ : ℝ) : ℂ) := by
      simp only [fnVal, Complex.ofReal_mul, Complex.ofReal_inv, ← Complex.mul_conj]
      rfl
    rw [hre, ← Complex.ofReal_pow]
    exact Complex.zero_le_real.mpr (pow_nonneg (mul_nonneg (Complex.normSq_nonneg _) (inv_nonneg.mpr hGG.le)) _)
  · have h0 := ((((L.ζ * L.ζb * L.GGi) ^ (Fr.ofWord L st w).N).1
      ((κ fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) w e).1 Φ)).2).1 (c, g) hp
    simp only at h0
    rw [h0, hsInner_zero_left]

end Formalism.FourierDecayAlt.P5
end
end
