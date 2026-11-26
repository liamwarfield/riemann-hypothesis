module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeightedL2BoundedMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Markov
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwistedIsRealOrderLattice

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.DegreeOfProdLinearLe
namespace Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset

open MvPolynomial

end Formalism.FourierDecayAlt.P.LEx2
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ShiftBound
namespace Formalism.FourierDecayAlt.P.LEx2.A
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section

theorem dS_zero (B : Base) {A A' : Type} (T : Fn B A → Fn B A') (u : Fn B A) : dS B T u 0 = T u := by
  funext ω a
  have h : mulF B (fun _ : ℝ => (1:ℝ)) u = u := by funext ω a; simp [mulF]
  simp [dS, conjS, h]

theorem ds_zero {B : Base} (S : Step B) (Y : ℝ) : S.ds Y 0 = S.gX Y := dS_zero B _ _

theorem meas_iterDeriv {Ω : Type} [MeasurableSpace Ω] (F : ℝ → Ω → ℂ)
    (hsm : ∀ ω, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s => F s ω)) (hm : ∀ s, Measurable (F s)) :
    ∀ (p : ℕ) (s : ℝ), Measurable (fun ω => iteratedDeriv p (fun s => F s ω) s) := _root_.Formalism.FourierDecayAlt.P.LEx2.A3.meas_iterDeriv (Ω := Ω) F hsm hm

theorem dsMeas : DsMeas := by
  intro B S hMeas hI4 Y hY p k
  obtain ⟨c, hc⟩ := hI4 Y hY
  have := meas_iterDeriv (fun s ω => S.gs Y s ω k) (fun ω => by
      have : (fun s : ℝ => S.gs Y s ω k) = fun s : ℝ => ∑ q ∈ range (S.r + 1 + 1), (s : ℂ) ^ q * c q ω k := by
        funext s; exact hc s ω k
      rw [this]
      apply ContDiff.sum
      intro q _
      exact (Complex.ofRealCLM.contDiff.pow q).mul contDiff_const)
    (fun s => (hMeas.2.2 Y hY).2 s k) p 0
  exact this

theorem stepClaimFromSteps (hDs : DsMeas) : StepClaimFromSteps := by
  intro hCauchy hMarkovV hTF hTR hTS hTB hTL hCT hLeib hTZ hCI hAdj hEF hCS hSh hMk hTermB hGeom hES hAbs hUB hFat hDom
  intro B S c σ CR Cd CP h4 hCR hCd hCP hL hLbig hImp hInt Y hY
  have hImp' := hImp
  obtain ⟨hMeas, hWPos, hPReg, hI3, hAdjB, hJet, hI4, hI4', hI5a, hRes, hWR, hPR⟩ := hImp
  have hσ : (0:ℝ) ≤ σ := by linarith
  have hStar : S.Star σ := hAdj hCauchy hLeib hCT hCI hTS hTR B S c σ h4 hMeas hWPos hI3 hAdjB hJet hI4 hI4' hInt
  have hUni : Uniform B S σ CR Cd CP :=
    hUB hAdj hTermB hES hAbs hEF hSh hMk hCS hCI hTZ hGeom hTR hTS hTB hLeib hCT hCauchy hMarkovV
      B S c σ CR Cd CP h4 hCR hCd hCP hL hLbig hImp' hInt
  have hCoef : S.CoefInt σ := hCI B S σ hσ hMeas hWPos hI4 hI4'
  have hF : ∀ p : ℕ, Integrable (LE.sq B (S.d Y) (S.ds Y p)) B.μ := by
    intro p
    exact (hFat hTR hTL B (Bool × S.ι) (S.d Y) (S.ds Y p) σ _ hσ (fun ω a => (hWPos.2 Y hY ω a).le)
      (fun a => (hMeas.2.2 Y hY).1 a) (fun a => hDs B S hMeas hI4 Y hY p a)
      (fun ε hε => hCoef ε hε Y hY p) (fun ε hε => hUni ε hε Y hY p)).1
  refine ⟨?_, hDom hTR hTL hTB hTZ hCauchy B S σ h4 hMeas hWPos hI4 hStar hInt Y hY hF⟩
  have := hF 0
  rwa [ds_zero] at this

theorem en_le_esup {B : Base} (S : Step B) (ε σ : ℝ) (hb : BddAbove (S.Eset ε σ)) (hP : S.PReg) (Y : ℝ) (hY : Y ∈ S.J) :
    S.En ε σ Y ≤ S.Esup ε σ * |S.P Y| := by
  have h1 : S.En ε σ Y / |S.P Y| ≤ S.Esup ε σ := le_csSup hb ⟨Y, hY, rfl⟩
  have hpos : 0 < |S.P Y| := abs_pos.mpr (hP.2 Y hY)
  rwa [div_le_iff₀ hpos] at h1

theorem termBound : TermBound := by
  intro hCS hSh hMk hCI hEF hTB hCauchy hMarkovV B S c σ ε CR Cd CP h4 hε hCR hCd hCP hL hImp Y hY p
  obtain ⟨hMeas, hWPos, hPReg, hI3, hAdjB, hJet, hI4, hI4', hI5a, hRes, hWR, hPR⟩ := hImp
  have hσ : (0:ℝ) ≤ σ := by linarith
  have hb := hEF B S σ ε hε hPReg hI4'
  have hCoef : S.CoefInt σ := hCI B S σ hσ hMeas hWPos hI4 hI4'
  have h1 := hCS hTB hCauchy B S σ ε h4 hε hMeas hWPos hI4 hI4' hCoef Y hY p
  have h2 := hSh B S σ ε CR Cd CP hσ hε hCR hCd hCP hMeas hWPos hPReg hI4' hI5a hRes hWR hPR hb
  have h3 := hMk hMarkovV B S σ ε (C7 CR Cd CP * S.Esup ε σ * |S.P Y|) hσ hε hL hMeas hWPos hI4 hI4' Y hY
    (fun s hs => h2 Y s hY hs) p
  have h4' := en_le_esup S ε σ hb hPReg Y hY
  have hEn0 : 0 ≤ S.En ε σ Y := by
    apply integral_nonneg
    intro ω
    apply mul_nonneg
    · exact Real.rpow_nonneg (div_nonneg (B.G_pos ω).le (by have := B.G_pos ω; linarith)) _
    · exact Finset.sum_nonneg (fun a _ => mul_nonneg (hWPos.2 Y hY ω a).le (by positivity))
  set Q := S.Esup ε σ * |S.P Y| with hQ
  have hQ0 : 0 ≤ Q := le_trans hEn0 h4'
  have hC7 : 0 ≤ C7 CR Cd CP := by unfold C7; positivity
  set m := 2 * ((S.r : ℝ) + 1) ^ 2 / S.L with hm
  have hm0 : 0 ≤ m := by rw [hm]; positivity
  have e1 : √(S.En ε σ Y) ≤ √Q := Real.sqrt_le_sqrt h4'
  have e2 : √(S.Dn ε σ Y p) ≤ m ^ p * (√(C7 CR Cd CP) * √Q) := by
    have : S.Dn ε σ Y p ≤ (m ^ p) ^ 2 * (C7 CR Cd CP * Q) := by
      have e : (m ^ p) ^ 2 * (C7 CR Cd CP * Q) = m ^ (2 * p) * (C7 CR Cd CP * S.Esup ε σ * |S.P Y|) := by
        rw [hQ, ← pow_mul, mul_comm p 2]; ring
      rw [e]; exact h3
    calc √(S.Dn ε σ Y p) ≤ √((m ^ p) ^ 2 * (C7 CR Cd CP * Q)) := Real.sqrt_le_sqrt this
      _ = m ^ p * (√(C7 CR Cd CP) * √Q) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), Real.sqrt_mul hC7]
  have hpre : 0 ≤ Real.exp 1 * (4 * σ) ^ p := by positivity
  calc ‖S.term ε σ Y p‖ ≤ Real.exp 1 * (4 * σ) ^ p * √(S.En ε σ Y) * √(S.Dn ε σ Y p) := h1
    _ ≤ Real.exp 1 * (4 * σ) ^ p * √Q * (m ^ p * (√(C7 CR Cd CP) * √Q)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left e1 hpre) e2 (Real.sqrt_nonneg _) (by positivity)
    _ = Real.exp 1 * √(C7 CR Cd CP) * (√Q * √Q) * ((4 * σ) * m) ^ p := by rw [mul_pow]; ring
    _ = Real.exp 1 * √(C7 CR Cd CP) * S.Esup ε σ * |S.P Y| * (8 * σ * ((S.r : ℝ) + 1) ^ 2 / S.L) ^ p := by
        rw [Real.mul_self_sqrt hQ0, hQ, hm]
        have : 4 * σ * (2 * ((S.r : ℝ) + 1) ^ 2 / S.L) = 8 * σ * ((S.r : ℝ) + 1) ^ 2 / S.L := by ring
        rw [this]; ring

theorem absorb : Absorb := by
  intro B S σ ε A hL hb h
  have hne : (S.Eset ε σ).Nonempty := ⟨_, S.a, ⟨le_refl _, by linarith⟩, rfl⟩
  have : S.Esup ε σ ≤ A + S.Esup ε σ / 2 := by
    apply csSup_le hne
    rintro _ ⟨Y, hY, rfl⟩
    exact h Y hY
  linarith

theorem uniformBound : UniformBound := by
  intro hAdj hTermB hES hAbs hEF hSh hMk hCS hCI hTZ hGeom hTR hTS hTB hLeib hCT hCauchy hMarkovV
  intro B S c σ CR Cd CP h4 hCR hCd hCP hL hLbig hImp hInt ε hε Y hY p
  have hImp' := hImp
  obtain ⟨hMeas, hWPos, hPReg, hI3, hAdjB, hJet, hI4, hI4', hI5a, hRes, hWR, hPR⟩ := hImp
  have hσ : (0:ℝ) ≤ σ := by linarith
  have hStar : S.Star σ := hAdj hCauchy hLeib hCT hCI hTS hTR B S c σ h4 hMeas hWPos hI3 hAdjB hJet hI4 hI4' hInt
  have hb := hEF B S σ ε hε hPReg hI4'
  have hT := hTermB hCS hSh hMk hCI hEF hTB hCauchy hMarkovV B S c σ ε CR Cd CP h4 hε hCR hCd hCP hL hImp'
  have hE := hES hTZ hGeom hTR B S c σ ε CR Cd CP h4 hε hCR hCd hCP hL hLbig hImp' hInt hStar hT
  have hA := hAbs B S σ ε S.A0 hL.le hb hE
  have h2 := hSh B S σ ε CR Cd CP hσ hε hCR hCd hCP hMeas hWPos hPReg hI4' hI5a hRes hWR hPR hb
  have h3 := hMk hMarkovV B S σ ε (C7 CR Cd CP * S.Esup ε σ * |S.P Y|) hσ hε hL hMeas hWPos hI4 hI4' Y hY
    (fun s hs => h2 Y s hY hs) p
  have hC7 : 0 ≤ C7 CR Cd CP := by unfold C7; positivity
  refine le_trans h3 ?_
  have hm : 0 ≤ (2 * ((S.r : ℝ) + 1) ^ 2 / S.L) ^ (2 * p) := by positivity
  have : C7 CR Cd CP * S.Esup ε σ * |S.P Y| ≤ C7 CR Cd CP * (2 * S.A0) * |S.P Y| := by
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    exact mul_le_mul_of_nonneg_left hA hC7
  calc _ ≤ (2 * ((S.r : ℝ) + 1) ^ 2 / S.L) ^ (2 * p) * (C7 CR Cd CP * (2 * S.A0) * |S.P Y|) :=
        mul_le_mul_of_nonneg_left this hm
    _ = _ := by ring

theorem geom_sum_mul_pred (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1/2) (R : ℕ) : ∑ p ∈ Icc 1 R, x ^ p ≤ 2 * x - 2 * x ^ (R + 1) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h1 : 0 ≤ x ^ (R + 1) := by positivity
    have h2 : x ^ (R + 1 + 1) = x ^ (R + 1) * x := pow_succ _ _
    nlinarith

theorem geomSum : GeomSum := by
  intro c x R hc hx0 hx
  set K := Real.exp 1 * √c with hK
  have hK0 : 0 ≤ K := by positivity
  have hden : 0 < 2 * (1 + 2 * Real.exp 1 * √c) := by positivity
  have hx2 : x ≤ 1 / 2 := by
    refine le_trans hx ?_
    rw [div_le_div_iff₀ hden (by norm_num)]
    nlinarith
  have h1 := geom_sum_mul_pred x hx0 hx2 R
  have h2 : 0 ≤ x ^ (R + 1) := by positivity
  have h3 : ∑ p ∈ Icc 1 R, x ^ p ≤ 2 * x := by linarith
  rw [← Finset.mul_sum]
  have h4 : x * (2 * (1 + 2 * K)) ≤ 1 := by
    have := hx
    rw [le_div_iff₀ hden] at this
    simpa [hK, mul_assoc] using this
  calc K * ∑ p ∈ Icc 1 R, x ^ p ≤ K * (2 * x) := mul_le_mul_of_nonneg_left h3 hK0
    _ ≤ 1 / 2 := by nlinarith

theorem termZero : TermZero := by
  intro B S ε σ Y
  unfold Step.term Step.En
  rw [ds_zero]
  simp only [Nat.factorial_zero, Nat.cast_one, div_one]
  rw [← integral_complex_ofReal]
  congr 1
  funext ω
  have hG := B.G_pos ω
  simp only [ld, iteratedDeriv_zero, Real.exp_log hG, pr, LE.sq]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem sum_Icc_one (f : ℕ → ℝ) (R : ℕ) : ∑ p ∈ Icc 1 R, f p = ∑ i ∈ range R, f (i + 1) := by
  induction R with
  | zero => simp
  | succ R ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem th_nonneg (B : Base) (ε σ : ℝ) (hε : 0 < ε) (ω : B.Ω) : 0 ≤ th ε σ (B.G ω) :=
  Real.rpow_nonneg (div_nonneg (B.G_pos ω).le (by have := B.G_pos ω; linarith)) _

theorem energyStep : EnergyStep := by
  intro hTZ hGeom hTR B S c σ ε CR Cd CP h4 hε hCR hCd hCP hL hLbig hImp hInt hStar hT Y hY
  obtain ⟨hMeas, hWPos, hPReg, hI3, hAdjB, hJet, hI4, hI4', hI5a, hRes, hWR, hPR⟩ := hImp
  have hσ : (0:ℝ) ≤ σ := by linarith
  have hP : 0 < |S.P Y| := abs_pos.mpr (hPReg.2 Y hY)
  have hC7 : 0 ≤ C7 CR Cd CP := by unfold C7; positivity
  have hsq0 : ∀ ω, 0 ≤ LE.sq B S.dw S.X ω := fun ω =>
    Finset.sum_nonneg (fun a _ => mul_nonneg (hWPos.1 ω a).le (by positivity))
  have hAth : S.Ath ε σ ≤ S.A0 := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun ω => mul_nonneg (th_nonneg B ε σ hε ω) (hsq0 ω))
    · exact hInt
    · exact Filter.Eventually.of_forall (fun ω => by
        have := (hTR ε σ (B.G ω) hε hσ (B.G_pos ω)).2
        simpa using mul_le_mul_of_nonneg_right this (hsq0 ω))
  have hE0 : 0 ≤ S.Esup ε σ := by
    apply Real.sSup_nonneg
    rintro _ ⟨Y', hY', rfl⟩
    apply div_nonneg _ (abs_nonneg _)
    apply integral_nonneg
    intro ω
    exact mul_nonneg (th_nonneg B ε σ hε ω)
      (Finset.sum_nonneg (fun a _ => mul_nonneg (hWPos.2 Y' hY' ω a).le (by positivity)))
  set x := 8 * σ * ((S.r : ℝ) + 1) ^ 2 / S.L with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hden : 0 < 2 * (1 + 2 * Real.exp 1 * √(C7 CR Cd CP)) := by positivity
  have hx1 : x ≤ 1 / (2 * (1 + 2 * Real.exp 1 * √(C7 CR Cd CP))) := by
    rw [le_div_iff₀ hden, hx, div_mul_eq_mul_div, div_le_one hL]
    linarith
  have hG := hGeom (C7 CR Cd CP) x (S.r + 1) hC7 hx0 hx1
  rw [sum_Icc_one] at hG
  have hs := hStar ε hε Y hY
  rw [Finset.sum_range_succ', hTZ] at hs
  have hnorm : ‖∑ i ∈ range (S.r + 1), S.term ε σ Y (i + 1)‖ ≤ S.Esup ε σ * |S.P Y| / 2 := by
    calc _ ≤ ∑ i ∈ range (S.r + 1), ‖S.term ε σ Y (i + 1)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ range (S.r + 1), (S.Esup ε σ * |S.P Y|) * (Real.exp 1 * √(C7 CR Cd CP) * x ^ (i + 1)) := by
          apply Finset.sum_le_sum
          intro i _
          have := hT Y hY (i + 1)
          calc _ ≤ _ := this
            _ = _ := by ring
      _ = (S.Esup ε σ * |S.P Y|) * ∑ i ∈ range (S.r + 1), (Real.exp 1 * √(C7 CR Cd CP) * x ^ (i + 1)) := by
          rw [Finset.mul_sum]
      _ ≤ (S.Esup ε σ * |S.P Y|) * (1 / 2) := mul_le_mul_of_nonneg_left hG (by positivity)
      _ = _ := by ring
  have hre : S.En ε σ Y = |S.P Y| * S.Ath ε σ - (∑ i ∈ range (S.r + 1), S.term ε σ Y (i + 1)).re := by
    have := congrArg Complex.re hs
    simp only [Complex.ofReal_re, Complex.add_re] at this
    linarith
  have hre2 : -(∑ i ∈ range (S.r + 1), S.term ε σ Y (i + 1)).re ≤ S.Esup ε σ * |S.P Y| / 2 := by
    have := Complex.abs_re_le_norm (∑ i ∈ range (S.r + 1), S.term ε σ Y (i + 1))
    have h2 := neg_abs_le (∑ i ∈ range (S.r + 1), S.term ε σ Y (i + 1)).re
    linarith
  rw [div_le_iff₀ hP]
  nlinarith

theorem eFinite : EFinite := by
  intro B S σ ε hε hP hI
  have hc : ContinuousOn (fun Y => S.En ε σ Y / |S.P Y|) S.J :=
    (hI ε hε).2.div (hP.1.abs) (fun Y hY => abs_ne_zero.mpr (hP.2 Y hY))
  exact (isCompact_Icc.image_of_continuousOn hc).bddAbove

theorem norm_add_sq_le (x y : ℂ) (c : ℝ) (hc : 0 ≤ c) : c * ‖x + y‖ ^ 2 ≤ c * (1 + c) * ‖x‖ ^ 2 + (1 + c) * ‖y‖ ^ 2 := by
  have h1 : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
  have h2 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := by
    apply pow_le_pow_left₀ (norm_nonneg _) h1
  have h3 : 0 ≤ (c * ‖x‖ - ‖y‖) ^ 2 := sq_nonneg _
  have h4 : c * ‖x + y‖ ^ 2 ≤ c * (‖x‖ + ‖y‖) ^ 2 := mul_le_mul_of_nonneg_left h2 hc
  nlinarith

theorem shift_pt {B : Base} (S : Step B) (CR Cd : ℝ) (hCR : 0 ≤ CR) (hCd : 0 ≤ Cd) (hW : S.WPos) (h5 : S.ShiftFormula)
    (hRes : S.Residues CR) (hWR : S.WeightRatio Cd) (Y s : ℝ) (hY : Y ∈ S.J) (hYs : Y + s ∈ S.J) (ω : B.Ω) :
    LE.sq B (S.d Y) (S.gs Y s) ω ≤ (1 + CR) ^ 2 * (Cd * LE.sq B (S.d (Y + s)) (S.gX (Y + s)) ω) := by
  set u1 : S.ι → ℂ := fun i => S.gX (Y + s) ω (false, i) with hu1
  set u2 : S.ι → ℂ := fun i => S.gX (Y + s) ω (true, i) with hu2
  set t : S.ι → ℂ := fun i => ∑ j, (S.ee Y ω i j - S.ee (Y + s) ω i j) * u1 j with ht
  set A := ∑ i, S.d Y ω (false, i) * ‖u1 i‖ ^ 2 with hA
  set Bq := ∑ i, S.d Y ω (true, i) * ‖u2 i‖ ^ 2 with hBq
  set Tq := ∑ i, S.d Y ω (true, i) * ‖t i‖ ^ 2 with hTq
  set V := ∑ i, S.d Y ω (true, i) * ‖u2 i + t i‖ ^ 2 with hV
  have hd : ∀ k, 0 ≤ S.d Y ω k := fun k => (hW.2 Y hY ω k).le
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun i _ => mul_nonneg (hd _) (by positivity))
  have hB0 : 0 ≤ Bq := Finset.sum_nonneg (fun i _ => mul_nonneg (hd _) (by positivity))
  have hT : Tq ≤ CR ^ 2 * A := hRes Y s hY hYs ω u1
  have hL : LE.sq B (S.d Y) (S.gs Y s) ω = V + A := by
    unfold LE.sq
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    congr 1
    · apply Finset.sum_congr rfl; intro i _; rw [(h5 Y s hY hYs ω i).2]
    · apply Finset.sum_congr rfl; intro i _; rw [(h5 Y s hY hYs ω i).1]
  have hR : Bq + A ≤ Cd * LE.sq B (S.d (Y + s)) (S.gX (Y + s)) ω := by
    unfold LE.sq
    rw [Fintype.sum_prod_type, Fintype.sum_bool, mul_add, Finset.mul_sum, Finset.mul_sum]
    apply add_le_add
    · apply Finset.sum_le_sum; intro i _
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hWR Y s hY hYs ω _) (by positivity)
    · apply Finset.sum_le_sum; intro i _
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hWR Y s hY hYs ω _) (by positivity)
  have hVb : CR * V ≤ CR * (1 + CR) * Bq + (1 + CR) * Tq := by
    rw [hV, hBq, hTq, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro i _
    have := mul_le_mul_of_nonneg_left (norm_add_sq_le (u2 i) (t i) CR hCR) (hd (true, i))
    nlinarith
  have key : V + A ≤ (1 + CR) ^ 2 * (Bq + A) := by
    rcases hCR.eq_or_lt with h0 | hpos
    · have hT0 : Tq ≤ 0 := by rw [← h0] at hT; simpa using hT
      have hz : ∀ i ∈ (Finset.univ : Finset S.ι), S.d Y ω (true, i) * ‖t i‖ ^ 2 = 0 := by
        apply (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hd _) (by positivity))).1
        exact le_antisymm hT0 (Finset.sum_nonneg (fun i _ => mul_nonneg (hd _) (by positivity)))
      have hVB : V = Bq := by
        apply Finset.sum_congr rfl; intro i hi
        have h1 := hz i hi
        have h2 : t i = 0 := by
          rcases mul_eq_zero.1 h1 with h | h
          · exact absurd h (hW.2 Y hY ω _).ne'
          · simpa using h
        rw [h2, add_zero]
      rw [hVB, ← h0]; simp
    · have : CR * V ≤ CR * ((1 + CR) * Bq + (1 + CR) * CR * A) := by nlinarith
      have hV2 : V ≤ (1 + CR) * Bq + (1 + CR) * CR * A := le_of_mul_le_mul_left this hpos
      nlinarith
  rw [hL]
  exact le_trans key (mul_le_mul_of_nonneg_left hR (by positivity))

theorem gs_zero {B : Base} (S : Step B) (Y : ℝ) : S.gs Y 0 = S.gX Y := by
  funext ω a
  have h : mulF B (fun _ : ℝ => (1:ℝ)) S.X = S.X := by funext ω a; simp [mulF]
  simp [Step.gs, Step.gX, conjS, h]

theorem shiftBound : ShiftBound := by
  intro B S σ ε CR Cd CP hσ hε hCR hCd hCP hMeas hW hP hI4' h5 hRes hWR hPR hb Y s hY hYs
  have hint : Integrable (fun ω => th ε σ (B.G ω) * LE.sq B (S.d (Y + s)) (S.gX (Y + s)) ω) B.μ := by
    have := (hI4' ε hε).1 (Y + s) hYs 0
    rwa [gs_zero] at this
  have h1 : S.Ens ε σ Y s ≤ (1 + CR) ^ 2 * Cd * S.En ε σ (Y + s) := by
    unfold Step.Ens Step.En
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun ω => mul_nonneg (th_nonneg B ε σ hε ω)
        (Finset.sum_nonneg (fun a _ => mul_nonneg (hW.2 Y hY ω a).le (by positivity))))
    · exact hint.const_mul _
    · exact Filter.Eventually.of_forall (fun ω => by
        have := mul_le_mul_of_nonneg_left (shift_pt S CR Cd hCR hCd hW h5 hRes hWR Y s hY hYs ω) (th_nonneg B ε σ hε ω)
        simp only
        calc _ ≤ _ := this
          _ = _ := by ring)
  have h2 : S.En ε σ (Y + s) / |S.P (Y + s)| ≤ S.Esup ε σ := le_csSup hb ⟨Y + s, hYs, rfl⟩
  have hpos : 0 < |S.P (Y + s)| := abs_pos.mpr (hP.2 _ hYs)
  rw [div_le_iff₀ hpos] at h2
  have hEn0 : 0 ≤ S.En ε σ (Y + s) := integral_nonneg (fun ω => mul_nonneg (th_nonneg B ε σ hε ω)
        (Finset.sum_nonneg (fun a _ => mul_nonneg (hW.2 _ hYs ω a).le (by positivity))))
  have hE0 : 0 ≤ S.Esup ε σ := by
    by_contra h
    push_neg at h
    nlinarith
  have h3 : S.Esup ε σ * |S.P (Y + s)| ≤ S.Esup ε σ * (CP * |S.P Y|) := mul_le_mul_of_nonneg_left (hPR Y s hY hYs) hE0
  have hk : 0 ≤ (1 + CR) ^ 2 * Cd := by positivity
  calc S.Ens ε σ Y s ≤ (1 + CR) ^ 2 * Cd * S.En ε σ (Y + s) := h1
    _ ≤ (1 + CR) ^ 2 * Cd * (S.Esup ε σ * (CP * |S.P Y|)) := mul_le_mul_of_nonneg_left (le_trans h2 h3) hk
    _ = C7 CR Cd CP * S.Esup ε σ * |S.P Y| := by unfold C7; ring

theorem stepClaimFromSteps_full : StepClaimFromSteps := stepClaimFromSteps dsMeas

end
end Formalism.FourierDecayAlt.P.LEx2.A
end

namespace Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE

theorem stepClaim (hC : E.CauchyTheta) (hMV : E.MarkovVector) : StepClaim :=
  A.stepClaimFromSteps_full hC hMV thetaForm thetaRange thetaSmooth thetaBound thetaLimit cutTheta
    leibniz A.termZero coefIntegrable adj A.eFinite csTerm A.shiftBound markovTerm A.termBound
    A.geomSum A.energyStep A.absorb A.uniformBound fatouStep domConv

private theorem onBoxes_ofFn_of_mem_box (S : Formalism.FourierDecayAlt.LE.Sys) : ∀ (N : ℕ) (Y : Fin N → ℝ),
    (∀ a : Fin N, Y a ∈ S.box (N - 1 - (a : ℕ))) → S.OnBoxes (List.ofFn Y) := by
  intro N
  induction N with
  | zero =>
    intro Y _
    rw [List.ofFn_zero]
    exact trivial
  | succ N ih =>
    intro Y hY
    rw [List.ofFn_succ]
    show Y 0 ∈ S.box (List.ofFn fun i => Y i.succ).length ∧ S.OnBoxes (List.ofFn fun i => Y i.succ)
    refine ⟨?_, ih _ (fun i => ?_)⟩
    · convert hY 0 using 2
      simp only [List.length_ofFn, Fin.val_zero]
      omega
    · convert hY i.succ using 2
      simp only [Fin.val_succ]
      omega

private theorem mem_box_of_onBoxes_ofFn (S : Formalism.FourierDecayAlt.LE.Sys) : ∀ (N : ℕ) (Y : Fin N → ℝ),
    S.OnBoxes (List.ofFn Y) → ∀ a : Fin N, Y a ∈ S.box (N - 1 - (a : ℕ)) := by
  intro N
  induction N with
  | zero =>
    intro Y _ a
    exact a.elim0
  | succ N ih =>
    intro Y hY a
    rw [List.ofFn_succ] at hY
    have hY' : Y 0 ∈ S.box (List.ofFn fun i => Y i.succ).length ∧
        S.OnBoxes (List.ofFn fun i => Y i.succ) := hY
    induction a using Fin.cases with
    | zero =>
      convert hY'.1 using 2
      simp only [List.length_ofFn, Fin.val_zero]
      omega
    | succ i =>
      convert ih _ hY'.2 i using 2
      simp only [Fin.val_succ]
      omega

private theorem degreeOf_prod_le_sum_degreeOf {σ ι : Type} (i : σ) (s : Finset ι) (f : ι → MvPolynomial σ ℝ) :
    MvPolynomial.degreeOf i (∏ j ∈ s, f j) ≤ ∑ j ∈ s, MvPolynomial.degreeOf i (f j) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty, ← MvPolynomial.C_1, MvPolynomial.degreeOf_C]
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (Nat.add_le_add_left ih _)

private theorem degreeOf_C_mul_prod_X_add_C_le (N m : ℕ) (c : ℝ) (lam : Fin m → ℝ) (i : Fin N) :
    MvPolynomial.degreeOf i (MvPolynomial.C c *
      ∏ a : Fin N, ∏ s : Fin m, (MvPolynomial.X a + MvPolynomial.C (lam s))) ≤ m := by
  classical
  refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
  rw [MvPolynomial.degreeOf_C, zero_add]
  refine (degreeOf_prod_le_sum_degreeOf i _ _).trans ?_
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have h1 : ∑ a ∈ Finset.univ.erase i,
      MvPolynomial.degreeOf i (∏ s : Fin m, (MvPolynomial.X a + MvPolynomial.C (lam s))) = 0 := by
    refine Finset.sum_eq_zero (fun a ha => ?_)
    have hai : a ≠ i := Finset.ne_of_mem_erase ha
    refine Nat.eq_zero_of_le_zero ((degreeOf_prod_le_sum_degreeOf i _ _).trans (le_of_eq (Finset.sum_eq_zero (fun s _ => ?_))))
    refine Nat.eq_zero_of_le_zero ((MvPolynomial.degreeOf_add_le _ _ _).trans ?_)
    rw [MvPolynomial.degreeOf_X, MvPolynomial.degreeOf_C, if_neg (Ne.symm hai)]
    simp
  rw [h1, zero_add]
  refine (degreeOf_prod_le_sum_degreeOf i _ _).trans ?_
  calc ∑ s : Fin m, MvPolynomial.degreeOf i (MvPolynomial.X i + MvPolynomial.C (lam s))
      ≤ ∑ _s : Fin m, 1 := Finset.sum_le_sum (fun s _ => by
        refine (MvPolynomial.degreeOf_add_le _ _ _).trans ?_
        rw [MvPolynomial.degreeOf_X, MvPolynomial.degreeOf_C, if_pos rfl]
        simp)
    _ = m := by simp

private theorem le_constants_proof : Formalism.FourierDecayAlt.LE.Constants := by
  intro k r N C₂ C₆ I hN hC₂ hC₆ hI
  have hNr : (r:ℝ) + 1 ≤ N := by exact_mod_cast hN
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg _
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
  have hQ0 : (0:ℝ) ≤ ((r:ℝ) + 1) ^ 2 := by positivity
  have hkNQ : (0:ℝ) ≤ (k:ℝ) * N * ((r:ℝ) + 1) ^ 2 := by positivity
  have hN2Q : (0:ℝ) ≤ (N:ℝ) ^ 2 * ((r:ℝ) + 1) ^ 2 := by positivity
  have h26 : C₂ ≤ C₆ := by linarith
  have hC6 : 0 ≤ C₆ := by linarith
  have e1 : C₂ * ((k:ℝ) * N * ((r:ℝ) + 1) ^ 2) ≤ C₆ * ((k:ℝ) * N * ((r:ℝ) + 1) ^ 2) :=
    mul_le_mul_of_nonneg_right h26 hkNQ
  have e2 : (6 * C₂) * ((N:ℝ) ^ 2 * ((r:ℝ) + 1) ^ 2) ≤ C₆ * ((N:ℝ) ^ 2 * ((r:ℝ) + 1) ^ 2) :=
    mul_le_mul_of_nonneg_right hC₆ hN2Q
  have e3 : ((r:ℝ) + 1) * (N * ((r:ℝ) + 1) ^ 2) ≤ (N:ℝ) * (N * ((r:ℝ) + 1) ^ 2) :=
    mul_le_mul_of_nonneg_right hNr (by positivity)
  have e4 : C₂ * (((r:ℝ) + 1) * (N * ((r:ℝ) + 1) ^ 2)) ≤ C₂ * ((N:ℝ) * (N * ((r:ℝ) + 1) ^ 2)) :=
    mul_le_mul_of_nonneg_left e3 hC₂.le
  have e5 : 0 ≤ C₂ * ((N:ℝ) * ((r:ℝ) + 1) ^ 2) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · push_cast
    nlinarith
  · nlinarith

private theorem le_constSign_proof : Formalism.FourierDecayAlt.LE.ConstSign := by
  intro n lam α β h
  classical
  by_cases hab : α ≤ β
  · refine ⟨∏ s, (if -lam s < α then (1:ℝ) else -1), ?_, ?_⟩
    · refine Finset.prod_induction _ (fun x : ℝ => x = 1 ∨ x = -1) ?_ ?_ ?_
      · rintro a b (rfl | rfl) (rfl | rfl) <;> norm_num
      · left; rfl
      · intro s _
        split_ifs <;> simp
    · intro Y hY
      rw [Finset.abs_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun s _ => ?_)
      have hs := h s
      split_ifs with hlt
      · rw [abs_of_pos (by linarith [hY.1])]
        ring
      · have hb : β < -lam s := by
          by_contra hc
          push_neg at hc
          exact hs ⟨not_lt.mp hlt, hc⟩
        rw [abs_of_neg (by linarith [hY.2])]
        ring
  · exact ⟨1, Or.inl rfl, fun Y hY => absurd (le_trans hY.1 hY.2) hab⟩

private theorem le_boxesFit_proof : Formalism.FourierDecayAlt.LE.BoxesFit := by
  intro S hL hfit
  have hL0 : 0 < S.L := by linarith
  have hN0 : (0:ℝ) ≤ S.Ntot := Nat.cast_nonneg _
  have hαβ : S.α ≤ S.β := by nlinarith [mul_nonneg hN0 hL0.le]
  have hmid : ∀ a, a < S.Ntot →
      S.box a ⊆ Set.Icc (S.α + (S.β - S.α) / 3) (S.β - (S.β - S.α) / 3) := by
    intro a ha x hx
    have ha1 : a + 1 ≤ S.Ntot := ha
    have ha' : (a:ℝ) + 1 ≤ S.Ntot := by exact_mod_cast ha1
    have ha0 : (0:ℝ) ≤ a := Nat.cast_nonneg _
    obtain ⟨hx1, hx2⟩ := hx
    have h1 : 0 ≤ 2 * (a:ℝ) * S.L := by positivity
    have h2 := mul_le_mul_of_nonneg_right ha' hL0.le
    constructor
    · linarith
    · nlinarith
  have hsep : ∀ a b, a < b → ∀ x ∈ S.box a, ∀ y ∈ S.box b, S.L ≤ y - x := by
    intro a b hab x hx y hy
    have hab1 : a + 1 ≤ b := hab
    have hab' : (a:ℝ) + 1 ≤ b := by exact_mod_cast hab1
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    nlinarith [mul_le_mul_of_nonneg_right hab' hL0.le]
  refine ⟨hmid, hsep, ?_⟩
  have hmem : ∀ w : List ℝ, S.OnBoxes w → ∀ Z ∈ w, ∃ j, j < w.length ∧ Z ∈ S.box j := by
    intro w
    induction w with
    | nil =>
      intro _ Z hZ
      simp at hZ
    | cons Y w ih =>
      intro hOn Z hZ
      have hOn' : Y ∈ S.box w.length ∧ S.OnBoxes w := hOn
      rcases List.mem_cons.mp hZ with rfl | hZ'
      · exact ⟨w.length, by simp only [List.length_cons]; omega, hOn'.1⟩
      · obtain ⟨j, hj, hZj⟩ := ih hOn'.2 Z hZ'
        exact ⟨j, by simp only [List.length_cons]; omega, hZj⟩
  have hin : ∀ j, j < S.Ntot → ∀ x ∈ S.box j, x ∈ Set.Icc S.α S.β := by
    intro j hj x hx
    have hx' := hmid j hj hx
    exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  intro w
  induction w with
  | nil =>
    intro _ _
    refine ⟨fun x hx => ?_, List.Pairwise.nil⟩
    simp [Formalism.FourierDecayAlt.LE.plus] at hx
  | cons Y w ih =>
    intro hOn hlen
    have hOn' : Y ∈ S.box w.length ∧ S.OnBoxes w := hOn
    have hlen' : w.length < S.Ntot := by
      simp only [List.length_cons] at hlen
      omega
    obtain ⟨ih1, ih2⟩ := ih hOn'.2 (by omega)
    show (∀ x ∈ (true, Y) :: Formalism.FourierDecayAlt.LE.plus w, x.2 ∈ Set.Icc S.α S.β) ∧
      ((true, Y) :: Formalism.FourierDecayAlt.LE.plus w).Pairwise fun x y => 2 < |x.2 - y.2|
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hin _ hlen' _ hOn'.1
      · exact ih1 x hx'
    · refine List.Pairwise.cons ?_ ih2
      intro z hz
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.mp hz
      obtain ⟨j, hj, hZj⟩ := hmem w hOn'.2 Z hZ
      have hd := hsep j w.length hj Z hZj Y hOn'.1
      show 2 < |Y - Z|
      rw [abs_of_pos (by linarith)]
      linarith

private theorem le_claimAll_proof : Formalism.FourierDecayAlt.LE.ClaimAll := by
  intro hStep hInd S σ CR Cd CP hσ hCR hCd hCP hL hbig hJL2 hImp
  refine hInd S hJL2 ?_
  intro w Y hOn hlen hint
  have hOn' : Y ∈ S.box w.length ∧ S.OnBoxes w := hOn
  have hY : Y ∈ (S.step w).J := by
    show Y ∈ Set.Icc (S.step w).a ((S.step w).a + (S.step w).L)
    rw [S.step_a, S.step_L]
    exact hOn'.1
  have hst := hStep S.B (S.step w) S.c σ CR Cd CP hσ hCR hCd hCP (by rw [S.step_L]; exact hL)
    (by rw [S.step_r, S.step_L]; exact hbig) (hImp w hOn'.2 hlen) hint Y hY
  have hfun : S.dens (Y :: w) = fun ω => Formalism.FourierDecayAlt.LE.sq S.B ((S.step w).d Y) ((S.step w).gX Y) ω :=
    funext (S.step_new w Y)
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hst.1
  · calc ∫ ω, S.dens (Y :: w) ω ∂S.B.μ
        = ∫ ω, Formalism.FourierDecayAlt.LE.sq S.B ((S.step w).d Y) ((S.step w).gX Y) ω ∂S.B.μ := by rw [hfun]
      _ = |(S.step w).P Y| * (S.step w).A0 := hst.2
      _ = |S.P Y| * ∫ ω, S.dens w ω ∂S.B.μ := by
        rw [S.step_P]
        rfl

private theorem le_claimInduction_proof : Formalism.FourierDecayAlt.LE.ClaimInduction := by
  intro S hJL2 hstep w
  induction w with
  | nil =>
    intro _ _
    refine ⟨hJL2, ?_⟩
    simp only [Formalism.FourierDecayAlt.LE.Sys.size, Formalism.FourierDecayAlt.LE.plus, List.map_nil, List.prod_nil, one_mul]
    rfl
  | cons Y w ih =>
    intro hOn hlen
    have hOn' : Y ∈ S.box w.length ∧ S.OnBoxes w := hOn
    have hlen' : w.length < S.Ntot := by
      simp only [List.length_cons] at hlen
      omega
    obtain ⟨hi, he⟩ := ih hOn'.2 hlen'.le
    have h := hstep w Y hOn hlen' hi
    refine ⟨h.1, ?_⟩
    rw [h.2, he]
    simp only [Formalism.FourierDecayAlt.LE.Sys.size, Formalism.FourierDecayAlt.LE.plus, List.map_cons, List.prod_cons]
    ring

private theorem le_eFromConstituents_proof : Formalism.FourierDecayAlt.LE.LemmaEFromSteps := by
  intro hConst hRed hGrid hSign hFit hAll hStep hInd hBL hLB hLA hLL2 hPL hCL2 hLeib hCut
  intro CR Cd CP hCR hCd hCP C₂ hC₂ C₆ hC₆ S hN hL hI hRO hI1 hJL2 hThm hImp hFam
  have hC₂64 : 64 ≤ C₂ :=
    le_trans (le_mul_of_one_le_right (by norm_num) (le_add_of_nonneg_right (by positivity))) hC₂
  have hN1' : 1 ≤ S.Ntot := by omega
  have hN1 : (1:ℝ) ≤ S.Ntot := by exact_mod_cast hN1'
  have hr0 : (0:ℝ) ≤ S.r := Nat.cast_nonneg _
  have hQ : (1:ℝ) ≤ ((S.r:ℝ) + 1) ^ 2 := by nlinarith
  have hNQ : (1:ℝ) ≤ (S.Ntot:ℝ) * ((S.r:ℝ) + 1) ^ 2 := by nlinarith
  have hNQ0 : (0:ℝ) ≤ (S.Ntot:ℝ) * ((S.r:ℝ) + 1) ^ 2 := by linarith
  have hL64 : 64 ≤ S.L := by
    rw [hL]
    nlinarith [mul_le_mul hC₂64 hNQ (by norm_num) (by linarith)]
  have hL2 : 2 < S.L := by linarith
  have hL0 : 0 < S.L := by linarith
  obtain ⟨-, -, h6⟩ := hConst S.k S.r S.Ntot C₂ C₆ (S.β - S.α) hN (by linarith) hC₆ hI
  have hfit : 6 * (S.Ntot:ℝ) * S.L ≤ S.β - S.α := by
    rw [hL]
    linarith
  have hσ : (4:ℝ) ≤ 4 * (S.Ntot:ℝ) := by linarith
  have hclaims := hAll hStep hInd S (4 * (S.Ntot:ℝ)) CR Cd CP hσ hCR hCd hCP hL0
    (by rw [hL]; nlinarith [mul_le_mul_of_nonneg_right hC₂ hNQ0]) hJL2 hImp
  have hBox := hBL hLB hLA hLL2 hPL hCL2 hLeib hCut S hL0 hFam hThm hclaims
  exact hRed hGrid hSign hFit S hL2 hfit hRO hI1 hBox

private theorem le_reduceToBoxes_proof : Formalism.FourierDecayAlt.LE.ReduceToBoxes := by
  intro hGrid hSign hFit S hL hfit hRO hI1 hBox w hw hlen
  classical
  obtain ⟨sg0, -, hsg⟩ := hSign (S.k + 2 * S.r + 1) S.lam S.α S.β hRO
  obtain ⟨hmid, -, hadm⟩ := hFit S hL hfit
  have hL0 : 0 < S.L := by linarith
  suffices h : ∀ (N : ℕ) (sg : Fin N → Bool) (Y : Fin N → ℝ),
      S.admitted (List.ofFn fun a => (sg a, Y a)) → N ≤ S.Ntot →
      Filter.Tendsto (fun ε : ℝ => S.principalHermitianLattice ε (List.ofFn fun a => (sg a, Y a))) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (S.size (List.ofFn fun a => (sg a, Y a)) * S.jn)) by
    have hwe : (List.ofFn fun a : Fin w.length => ((w.get a).1, (w.get a).2)) = w := by
      simp only [Prod.mk.eta]
      exact List.ofFn_get w
    have h' := h w.length (fun a => (w.get a).1) (fun a => (w.get a).2) (by rw [hwe]; exact hw) hlen
    rw [hwe] at h'
    exact h'
  intro N sg Y hadmY hN
  have hex : ∀ ε : ℝ, ∃ Q : MvPolynomial (Fin N) ℝ,
      (∀ a, Q.degreeOf a ≤ S.k + 2 * S.r + 1) ∧
      (0 < ε → ∀ (sg' : Fin N → Bool) (Y' : Fin N → ℝ), S.admitted (List.ofFn fun a => (sg' a, Y' a)) →
        S.principalHermitianLattice ε (List.ofFn fun a => (sg' a, Y' a)) = MvPolynomial.eval Y' Q) := by
    intro ε
    by_cases hε : 0 < ε
    · obtain ⟨Q, hQ1, hQ2⟩ := hI1 ε hε N hN
      exact ⟨Q, hQ1, fun _ => hQ2⟩
    · exact ⟨0, fun a => by simp, fun h => absurd h hε⟩
  choose Qf hQf using hex
  set Q₀ : MvPolynomial (Fin N) ℝ := MvPolynomial.C (sg0 ^ N * S.jn) *
    ∏ a : Fin N, ∏ s : Fin (S.k + 2 * S.r + 1), (MvPolynomial.X a + MvPolynomial.C (S.lam s)) with hQ₀
  have hdeg0 : ∀ a, Q₀.degreeOf a ≤ S.k + 2 * S.r + 1 := fun a => degreeOf_C_mul_prod_X_add_C_le _ _ _ _ a
  have hval : ∀ Y' : Fin N → ℝ, (∀ a, Y' a ∈ Set.Icc S.α S.β) → ∀ sg' : Fin N → Bool,
      S.size (List.ofFn fun a => (sg' a, Y' a)) * S.jn = MvPolynomial.eval Y' Q₀ := by
    intro Y' hY' sg'
    have habs : ∀ a, |S.P (Y' a)| = sg0 * ∏ s, (Y' a + S.lam s) := fun a => hsg (Y' a) (hY' a)
    simp only [Formalism.FourierDecayAlt.LE.Sys.size, List.map_ofFn, List.prod_ofFn, Function.comp_apply]
    rw [hQ₀]
    simp only [map_mul, map_prod, map_add (f := _), MvPolynomial.eval_C, MvPolynomial.eval_X]
    simp only [habs, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  have hc : (0:ℝ) < ((S.k + 2 * S.r + 1 : ℕ) : ℝ) + 1 := by positivity
  let grid : Fin N → Finset ℝ := fun a => (Finset.range (S.k + 2 * S.r + 1 + 1)).image
    (fun i : ℕ => S.α + (S.β - S.α) / 3 + 2 * ((N - 1 - (a : ℕ) : ℕ) : ℝ) * S.L +
      (i : ℝ) * (S.L / (((S.k + 2 * S.r + 1 : ℕ) : ℝ) + 1)))
  have hcard : ∀ a, (grid a).card = S.k + 2 * S.r + 1 + 1 := by
    intro a
    rw [Finset.card_image_of_injective _ (fun i j hij => by
      have hq : (0:ℝ) < S.L / (((S.k + 2 * S.r + 1 : ℕ) : ℝ) + 1) := div_pos hL0 hc
      have h2 := add_left_cancel hij
      exact_mod_cast mul_right_cancel₀ hq.ne' h2)]
    exact Finset.card_range _
  have hconv : ∀ Y' : Fin N → ℝ, (∀ a, Y' a ∈ grid a) →
      Filter.Tendsto (fun t => MvPolynomial.eval Y' (Qf t)) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (MvPolynomial.eval Y' Q₀)) := by
    intro Y' hY'
    have hbox : ∀ a : Fin N, Y' a ∈ S.box (N - 1 - (a : ℕ)) := by
      intro a
      obtain ⟨i, hi, hiY⟩ := Finset.mem_image.mp (hY' a)
      rw [← hiY]
      have hi' : (i:ℝ) ≤ ((S.k + 2 * S.r + 1 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      have h0 : 0 ≤ (i:ℝ) * (S.L / (((S.k + 2 * S.r + 1 : ℕ) : ℝ) + 1)) :=
        mul_nonneg (Nat.cast_nonneg _) (div_nonneg hL0.le hc.le)
      have h1 : (i:ℝ) * (S.L / (((S.k + 2 * S.r + 1 : ℕ) : ℝ) + 1)) ≤ S.L := by
        rw [mul_div_assoc', div_le_iff₀ hc]
        nlinarith [mul_le_mul_of_nonneg_right hi' hL0.le]
      constructor
      · linarith
      · linarith
    have hOnY : S.OnBoxes (List.ofFn Y') := onBoxes_ofFn_of_mem_box S N Y' hbox
    have hb := hBox (List.ofFn Y') hOnY (by rw [List.length_ofFn]; exact hN)
    have hplus : Formalism.FourierDecayAlt.LE.plus (List.ofFn Y') = List.ofFn fun a => (true, Y' a) := by
      simp only [Formalism.FourierDecayAlt.LE.plus, List.map_ofFn]
      rfl
    have hIcc : ∀ a, Y' a ∈ Set.Icc S.α S.β := fun a => by
      have ha := a.isLt
      have hm := hmid (N - 1 - (a : ℕ)) (by omega) (hbox a)
      have hαβ : S.α ≤ S.β := by linarith [hm.1, hm.2]
      exact ⟨by linarith [hm.1], by linarith [hm.2]⟩
    rw [hplus, hval Y' hIcc (fun _ => true)] at hb
    refine hb.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hA := hadm (List.ofFn Y') hOnY (by rw [List.length_ofFn]; exact hN)
    rw [hplus] at hA
    exact (hQf ε).2 hε (fun _ => true) Y' hA
  have hlim := hGrid N (S.k + 2 * S.r + 1) ℝ (nhdsWithin 0 (Set.Ioi 0)) Qf Q₀ grid
    (fun t a => (hQf t).1 a) hdeg0 hcard hconv Y
  obtain ⟨hA1, -⟩ := id hadmY
  have hIcc : ∀ a, Y a ∈ Set.Icc S.α S.β := fun a =>
    hA1 (sg a, Y a) (by simp only [List.mem_ofFn]; exact ⟨a, rfl⟩)
  rw [hval Y hIcc sg]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact ((hQf ε).2 hε sg Y hadmY).symm

private theorem le_boxLimitFromClaim_proof : Formalism.FourierDecayAlt.LE.BoxLimitFromClaim := by
  intro hLB hLA hLL2 hPL hCL2 hLeib hCut S hL0 hFam hThm hClaim w hw hlen
  suffices h : ∀ (N : ℕ) (Y : Fin N → ℝ), S.OnBoxes (List.ofFn Y) → N ≤ S.Ntot →
      Filter.Tendsto (fun ε : ℝ => S.principalHermitianLattice ε (Formalism.FourierDecayAlt.LE.plus (List.ofFn Y))) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (S.size (Formalism.FourierDecayAlt.LE.plus (List.ofFn Y)) * S.jn)) by
    have h' := h w.length w.get (by rw [List.ofFn_get]; exact hw) hlen
    rw [List.ofFn_get] at h'
    exact h'
  intro N Y hOn hN
  have hInt : ∀ Y' : Fin N → ℝ, (S.fam N).On Y' →
      MeasureTheory.Integrable
        (Formalism.FourierDecayAlt.LE.sq S.B ((S.fam N).dw Y') ((S.fam N).gw Y' (S.fam N).u)) S.B.μ := by
    intro Y' hY'
    have hOn' : S.OnBoxes (List.ofFn Y') := onBoxes_ofFn_of_mem_box S N Y' (fun a => by
      have h := hY' a
      rw [S.fam_J] at h
      exact h)
    have hc := (hClaim (List.ofFn Y') hOn' (by rw [List.length_ofFn]; exact hN)).1
    have hfun : S.dens (List.ofFn Y') =
        fun ω => Formalism.FourierDecayAlt.LE.sq S.B ((S.fam N).dw Y') ((S.fam N).gw Y' (S.fam N).u) ω :=
      funext (S.fam_dens N Y')
    rw [hfun] at hc
    exact hc
  have hJinf : ∀ a, ((S.fam N).J a).Infinite := by
    intro a
    rw [S.fam_J]
    exact Set.Icc_infinite (by linarith)
  have hOnF : ∀ a, Y a ∈ (S.fam N).J a := by
    intro a
    have h := mem_box_of_onBoxes_ofFn S N Y hOn a
    rw [S.fam_J]
    exact h
  have hlim := hLB hLA hLL2 hPL hCL2 hLeib hCut S.B N (S.fam N) S.c hJinf (hFam N hN) hInt Y hOnF
  have hval : S.size (Formalism.FourierDecayAlt.LE.plus (List.ofFn Y)) * S.jn =
      ∫ ω, Formalism.FourierDecayAlt.LE.sq S.B ((S.fam N).dw Y) ((S.fam N).gw Y (S.fam N).u) ω ∂S.B.μ := by
    rw [← (hClaim (List.ofFn Y) hOn (by rw [List.length_ofFn]; exact hN)).2]
    exact congrArg (MeasureTheory.integral S.B.μ) (funext fun ω => S.fam_dens N Y ω)
  rw [hval]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hThm N Y hN hOn ε hε).symm

theorem lemmaE (hC : E.CauchyTheta) (hMV : E.MarkovVector) : LemmaE :=
  le_eFromConstituents_proof le_constants_proof le_reduceToBoxes_proof gridConvergence le_constSign_proof le_boxesFit_proof
    le_claimAll_proof (stepClaim hC hMV) le_claimInduction_proof le_boxLimitFromClaim_proof limitB limitA limit_L2
    pairLimit coefficient_L2 leibniz cutBound

theorem lemmaE_closed : LemmaE :=
  lemmaE Formalism.FourierDecayAlt.P.cauchy_theta_identity Formalism.FourierDecayAlt.P.markov_inequality_vector

end Formalism.FourierDecayAlt.P.LEx2

theorem Formalism.FourierDecayAlt.P.ratio_middle_range : Formalism.FourierDecayAlt.LE.PRatioMiddle := by
  intro n lam α β L Y s hαβ hroot hL hnL hs hY1 hY2 hYs1 hYs2
  set D := (β - α) / 3 with hD
  have hD0 : 0 < D := by rw [hD]; linarith
  have hfac : ∀ t, D ≤ |Y + s + lam t| := by
    intro t
    have ht := hroot t
    by_cases h : -lam t ≤ α
    · rw [abs_of_pos (by linarith)]
      linarith
    · push_neg at h
      have hb : β ≤ -lam t := by
        by_contra hc
        push_neg at hc
        exact ht ⟨h, hc⟩
      rw [abs_of_neg (by linarith)]
      linarith
  have hrat : ∀ t, |Y + lam t| ≤ (1 + L / D) * |Y + s + lam t| := by
    intro t
    have h1 := abs_sub_abs_le_abs_sub (Y + lam t) (Y + s + lam t)
    have h1' : (Y + lam t) - (Y + s + lam t) = -s := by ring
    rw [h1', abs_neg] at h1
    have h2 : L ≤ L / D * |Y + s + lam t| := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hD0]
      exact mul_le_mul_of_nonneg_left (hfac t) hL
    nlinarith
  have hprod : |∏ t, (Y + lam t)| ≤ (1 + L / D) ^ n * |∏ t, (Y + s + lam t)| := by
    rw [Finset.abs_prod, Finset.abs_prod]
    calc ∏ t, |Y + lam t| ≤ ∏ t, ((1 + L / D) * |Y + s + lam t|) :=
          Finset.prod_le_prod₀ (fun t _ => abs_nonneg _) (fun t _ => hrat t)
      _ = (1 + L / D) ^ n * ∏ t, |Y + s + lam t| := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hx : 1 + L / D ≤ Real.exp (L / D) := by linarith [Real.add_one_le_exp (L / D)]
  have hexp : (1 + L / D) ^ n ≤ Real.exp 3 := by
    calc (1 + L / D) ^ n ≤ (Real.exp (L / D)) ^ n := by gcongr <;> exact hx
      _ = Real.exp (n * (L / D)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp 3 := by
          apply Real.exp_le_exp.mpr
          have he : (n:ℝ) * (L / D) = (n * L) / D := by ring
          rw [he, div_le_iff₀ hD0]
          linarith
  calc |∏ t, (Y + lam t)| ≤ (1 + L / D) ^ n * |∏ t, (Y + s + lam t)| := hprod
    _ ≤ Real.exp 3 * |∏ t, (Y + s + lam t)| := mul_le_mul_of_nonneg_right hexp (abs_nonneg _)
theorem Formalism.FourierDecayAlt.P.constants_choice : Formalism.FourierDecayAlt.LE.Constants := Formalism.FourierDecayAlt.P.LEx2.le_constants_proof
theorem Formalism.FourierDecayAlt.P.boxes_fit : Formalism.FourierDecayAlt.LE.BoxesFit := Formalism.FourierDecayAlt.P.LEx2.le_boxesFit_proof
theorem Formalism.FourierDecayAlt.P.imported_results_hold : Formalism.FourierDecayAlt.LE.PImportsHold := by
  intro hPR hFit S hL hfit hnL hRO w hlen
  have hL0 : 0 < S.L := by linarith
  have hN1 : (1:ℝ) ≤ S.Ntot := by
    have : 1 ≤ S.Ntot := by omega
    exact_mod_cast this
  have hαβ : S.α < S.β := by nlinarith
  have hmid := (hFit S hL hfit).1 w.length hlen
  have hJ : ∀ Y ∈ (S.step w).J,
      Y ∈ Set.Icc (S.α + (S.β - S.α) / 3) (S.β - (S.β - S.α) / 3) := by
    intro Y hY
    apply hmid
    have hY' : Y ∈ Set.Icc (S.step w).a ((S.step w).a + (S.step w).L) := hY
    rw [S.step_a, S.step_L] at hY'
    exact hY'
  have hPfun : (S.step w).P = fun Y => ∏ s, (Y + S.lam s) := funext (S.step_P w)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hPfun]
    exact (continuous_finsetProd Finset.univ
      (fun s _ => continuous_id.add continuous_const)).continuousOn
  · intro Y hY
    rw [S.step_P]
    refine Finset.prod_ne_zero_iff.mpr (fun s _ => ?_)
    intro h0
    have hYm := hJ Y hY
    apply hRO s
    refine ⟨?_, ?_⟩ <;> nlinarith [hYm.1, hYm.2]
  · intro Y s hY hYs
    have hYm := hJ Y hY
    have hYsm := hJ (Y + s) hYs
    have hY' : Y ∈ Set.Icc (S.step w).a ((S.step w).a + (S.step w).L) := hY
    have hYs' : Y + s ∈ Set.Icc (S.step w).a ((S.step w).a + (S.step w).L) := hYs
    rw [S.step_L] at hY' hYs'
    have key := hPR (S.k + 2 * S.r + 1) S.lam S.α S.β S.L (Y + s) (-s) hαβ
      (fun t ht => hRO t ⟨ht.1.le, ht.2.le⟩) hL0.le hnL
      (by rw [abs_neg]; exact abs_le.mpr ⟨by linarith [hY'.1, hY'.2, hYs'.1, hYs'.2], by linarith [hY'.1, hY'.2, hYs'.1, hYs'.2]⟩)
      hYsm.1 hYsm.2 (by linarith [hYm.1]) (by linarith [hYm.2])
    simp only [add_neg_cancel_right] at key
    rw [S.step_P, S.step_P]
    exact key
theorem Formalism.FourierDecayAlt.P.le_E_proof : Formalism.FourierDecayAlt.LE.LemmaE := Formalism.FourierDecayAlt.P.LEx2.lemmaE_closed
