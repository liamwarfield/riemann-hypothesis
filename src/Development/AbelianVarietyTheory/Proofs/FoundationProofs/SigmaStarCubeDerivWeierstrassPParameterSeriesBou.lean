module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.InvOmega

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeDerivWeierstrassPParameterSeriesBou
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeDerivWeierstrassPParameterSeriesBou
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl

noncomputable section

namespace GlobalTheory.ThetaTransl.CubeSer

open PowerSeries

theorem taylorCoeffAtZero_deriv (F : ℂ → ℂ) (n : ℕ) : coef1 (deriv F) n = ((n : ℂ) + 1) * coef1 F (n + 1) := by
  simp only [coef1]
  rw [← iteratedDeriv_succ', Nat.factorial_succ]
  push_cast
  have h : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h' : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  field_simp

theorem algEnt_deriv {F : ℂ → ℂ} (hF : AlgEnt F) : AlgEnt (deriv F) := by
  refine ⟨?_, fun n => ?_⟩
  · have h := (hF.1.contDiff (n := 2)).differentiable_iteratedDeriv 1 (by norm_num)
    simpa [iteratedDeriv_one] using h
  · rw [taylorCoeffAtZero_deriv]
    exact mul_mem (add_mem (natCast_mem _ n) (one_mem _)) (hF.2 _)

variable {p : ℕ} [Fact p.Prime]

theorem padicTaylorSeries_deriv_eq_derivative (lam : Qbar →+* ℂ_[p]) {F : ℂ → ℂ} (hF : AlgEnt F) :
    GL3Theta.ser1 lam (deriv F) = d⁄dX (GL3Theta.ser1 lam F) := by
  ext n
  rw [coeff_derivative, GlobalTheory.SerTransport.coeff_padicTransportSeries, GlobalTheory.SerTransport.coeff_padicTransportSeries, taylorCoeffAtZero_deriv]
  obtain ⟨a, ha⟩ := GlobalTheory.SerTransport.exists_coef hF
  rw [ha]
  have e : ((n : ℂ) + 1) * (a (n + 1) : ℂ) = ((((n : Qbar) + 1) * a (n + 1) : Qbar) : ℂ) := by
    push_cast; rfl
  rw [e, GlobalTheory.SerTransport.lamC_coe, GlobalTheory.SerTransport.lamC_coe, map_mul, map_add (f := _), map_natCast, map_one,
    mul_comm]

theorem atU_deriv (g : GL3Theta.G1 p) {F : ℂ → ℂ} (hF : AlgEnt F) :
    d⁄dX (g.atU F) =
      g.atU (deriv F) * (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * d⁄dX g.l) := by
  have hs := HasSubst.of_constantCoeff_zero' (GlobalTheory.SerTransport.const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  rw [GlobalTheory.SerTransport.atU_eq, GlobalTheory.SerTransport.atU_eq, derivative_subst hs, padicTaylorSeries_deriv_eq_derivative g.lam hF,
    Derivation.leibniz, derivative_C, smul_zero, add_zero, smul_eq_mul]

theorem bddSer_derivative {f : PowerSeries ℂ_[p]} (hf : BddSer f) : BddSer (d⁄dX f) := by
  obtain ⟨B, hB⟩ := hf
  refine ⟨B, fun n => ?_⟩
  rw [coeff_derivative, norm_mul]
  have h1 : ‖((n : ℂ_[p]) + 1)‖ ≤ 1 := by
    exact_mod_cast IsUltrametricDist.norm_natCast_le_one ℂ_[p] (n + 1)
  calc _ ≤ B * 1 := mul_le_mul (hB _) h1 (norm_nonneg _) ((norm_nonneg _).trans (hB 0))
    _ = B := mul_one B

end GlobalTheory.ThetaTransl.CubeSer

namespace GlobalTheory.ThetaTransl.CubeSer

open PowerSeries

theorem sqThD_atU : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar →
    g3 g.abelian₂ ∈ Qbar → TaylorLogMetric.discr g.abelian₂ = 1 → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar →
      AlgEnt (sqThD g.abelian₂ v) ∧ ∃ w : PowerSeries ℂ_[p], BddSer w ∧
        g.atU (sqThD g.abelian₂ v) = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 * w := by
  intro p _ g hOk hL h2 h3 hd hσ v hv hw
  obtain ⟨-, hwi, -, -, hA⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hOk hL h2 h3 hd
  have hq : IsWq g.W g.wq := hOk.2.1
  obtain ⟨hS, hB⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hq hL h2 h3 hσ v hv hw
  obtain ⟨hmul, hconst, -, -⟩ := GlobalTheory.SerTransport.transport p g
  obtain ⟨i1, i2, i3, i4, i6, -⟩ := hOk.1
  obtain ⟨vI, hvI, hvl⟩ := PI.JetsPhW.Inv.inverse_omega_holds p g.W g.wq i1 i2 i3 i4 i6 hq
  rw [PI.JetsPhW.Inv.dX_eq_derivative] at hvl
  change vI * d⁄dX g.l = 1 at hvl
  have hσd := algEnt_deriv hσ
  have hSd := algEnt_deriv hS
  have hm2 : (((-2 : Qbar)) : ℂ) = -2 := by push_cast; rfl
  have hc := hconst (((-2 : Qbar)) : ℂ) (-2 : Qbar).2
  have hl2 : lamC g.lam (((-2 : Qbar)) : ℂ) = -2 := by
    rw [GlobalTheory.SerTransport.lamC_coe, map_neg, map_ofNat]
  have k1 := (hmul (sgStar g.abelian₂) (deriv (sqTh g.abelian₂ v)) hσ hSd).1
  have k2 := (hmul (deriv (sgStar g.abelian₂)) (sqTh g.abelian₂ v) hσd hS).1
  have k3 := (hmul (fun _ => (((-2 : Qbar)) : ℂ)) (fun z => deriv (sgStar g.abelian₂) z * sqTh g.abelian₂ v z)
    hc.1 k2.1).1
  have k4 := (hmul (fun z => sgStar g.abelian₂ z * deriv (sqTh g.abelian₂ v) z)
    (fun z => (((-2 : Qbar)) : ℂ) * (deriv (sgStar g.abelian₂) z * sqTh g.abelian₂ v z)) k1.1 k3.1).2
  have hT : sqThD g.abelian₂ v = fun z => sgStar g.abelian₂ z * deriv (sqTh g.abelian₂ v) z +
      (((-2 : Qbar)) : ℂ) * (deriv (sgStar g.abelian₂) z * sqTh g.abelian₂ v z) := by
    funext z
    rw [hm2]
    simp only [sqThD]
    ring
  refine ⟨hT ▸ k4.1, ?_⟩
  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε
  set e := ePhi1 g.lam g.abelian₂ g.C g.wq with he
  set L := lineSer g.wq⁻¹ (xAt g v) with hL'
  obtain ⟨-, hbdd, hCb, hX, -⟩ := SerRing.series_ring_laws p
  refine ⟨vI * (X * d⁄dX L - 2 * L), ?_, ?_⟩
  · have hX2 : BddSer (X ^ 2 : PowerSeries ℂ_[p]) := by
      rw [pow_two]; exact (hbdd _ _ ⟨1, hX⟩ ⟨1, hX⟩).2.2
    have hLb : BddSer L := by
      rw [hL', lineSer]; exact (hbdd _ _ ⟨1, hwi⟩ (hbdd _ _ (hCb _).1 hX2).2.2).2.1
    have h2b : BddSer (2 : PowerSeries ℂ_[p]) := by
      rw [show (2 : PowerSeries ℂ_[p]) = C 2 from (map_ofNat C 2).symm]; exact (hCb 2).1
    refine (hbdd _ _ ⟨1, fun n => hvI n⟩ (hbdd _ _ ((hbdd _ _ ⟨1, hX⟩ (bddSer_derivative hLb)).2.2)
      ((hbdd _ _ h2b hLb).2.2)).2.1).2.2
  · have dA := atU_deriv g hσ
    have dB := atU_deriv g hS
    rw [hA] at dA
    rw [hB] at dB
    have hDA : d⁄dX (C ε * X * e) = C ε * (e + X * d⁄dX e) := by
      simp only [Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul]
      ring
    have hDB : d⁄dX (e ^ 2 * L) =
        2 * e * d⁄dX e * L + e ^ 2 * d⁄dX L := by
      simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    rw [hDA] at dA
    rw [hDB] at dB
    have F4 : C ε * C ε⁻¹ = (1 : PowerSeries ℂ_[p]) := by
      rw [← map_mul, mul_inv_cancel₀ (Units.ne_zero _), map_one]
    set a1 := g.atU (deriv (sgStar g.abelian₂))
    set b1 := g.atU (deriv (sqTh g.abelian₂ v))
    set x := C ε
    set y := C ε⁻¹
    set l' := d⁄dX g.l
    set E' := d⁄dX e
    set L'' := d⁄dX L
    have ha1 : a1 = (e + X * E') * vI := by
      linear_combination (-a1) * F4 + (-a1 * x * y) * hvl + (-y * vI) * dA + ((e + X * E') * vI) * F4
    have hb1 : b1 = y * (2 * e * E' * L + e ^ 2 * L'') * vI := by
      linear_combination (-b1) * F4 + (-b1 * x * y) * hvl + (-y * vI) * dB
    have hT' : g.atU (sqThD g.abelian₂ v) = x * X * e * b1 + C (-2) * (a1 * (e ^ 2 * L)) := by
      rw [← hA, ← hB, ← hl2]
      calc g.atU (sqThD g.abelian₂ v) = g.atU (fun z => sgStar g.abelian₂ z * deriv (sqTh g.abelian₂ v) z +
            (((-2 : Qbar)) : ℂ) * (deriv (sgStar g.abelian₂) z * sqTh g.abelian₂ v z)) := by rw [← hT]
        _ = _ := by rw [k4.2, k1.2, k3.2, k2.2, hc.2]
    rw [hT', show (C (-2) : PowerSeries ℂ_[p]) = -2 by rw [map_neg, map_ofNat]]
    linear_combination (x * X * e) * hb1 - (2 * e ^ 2 * L) * ha1 +
      (X * e * (2 * e * E' * L + e ^ 2 * L'') * vI) * F4

end GlobalTheory.ThetaTransl.CubeSer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeDerivWeierstrassPParameterSeriesBouStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sigmaStarCubeDerivWeierstrassP_parameterSeries_bounded : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar →
    g3 g.abelian₂ ∈ Qbar → TaylorLogMetric.discr g.abelian₂ = 1 → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar →
      AlgEnt (sqThD g.abelian₂ v) ∧ ∃ w : PowerSeries ℂ_[p], BddSer w ∧
        g.atU (sqThD g.abelian₂ v) = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 * w := by
  first | exact @GlobalTheory.ThetaTransl.CubeSer.sqThD_atU | exact GlobalTheory.ThetaTransl.CubeSer.sqThD_atU | (intros; apply GlobalTheory.ThetaTransl.CubeSer.sqThD_atU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LamBallULe
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LamBallULe
noncomputable section
namespace GlobalTheory.CartanInt.LamBall
open Formalism.BasicNotions Matrix MeasureTheory

theorem pow_self_le_factorial_sq (n : ℕ) : n ^ n ≤ n.factorial ^ 2 := by
  have h1 : ∏ k ∈ Finset.range n, (k + 1) = n.factorial := Finset.prod_range_add_one_eq_factorial n
  have h2 : ∏ k ∈ Finset.range n, (n - k) = n.factorial := by
    calc ∏ k ∈ Finset.range n, (n - k) = ∏ k ∈ Finset.range n, ((n - 1 - k) + 1) :=
          Finset.prod_congr rfl fun k hk => by have := Finset.mem_range.1 hk; omega
      _ = ∏ k ∈ Finset.range n, (k + 1) := Finset.prod_range_reflect (fun k => k + 1) n
      _ = n.factorial := h1
  calc n ^ n = ∏ _k ∈ Finset.range n, n := by rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ k ∈ Finset.range n, ((k + 1) * (n - k)) := by
        apply Finset.prod_le_prod'
        intro k hk
        have hk := Finset.mem_range.1 hk
        obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 := ⟨n - k - 1, by omega⟩
        have hn : n = k + m + 1 := by omega
        rw [hm, hn]
        nlinarith
    _ = n.factorial ^ 2 := by rw [Finset.prod_mul_distrib, h1, h2, sq]

theorem two_mul_pow_le_factorial (N : ℕ) : (2 * N) ^ N ≤ (2 * N).factorial := by
  have h := pow_self_le_factorial_sq (2 * N)
  rw [pow_mul'] at h
  exact (Nat.pow_le_pow_iff_left two_ne_zero).1 h

theorem volume_l1_ball_le {ι : Type} [Fintype ι] (a : ℕ) (ha : Fintype.card ι = a ^ 2) (r : ℝ)
    (hr : 0 < r) : (volume : Measure (ι → ℂ)) {z | ∑ i, ‖z i‖ < 2 * r} ≤
      ENNReal.ofReal ((18 / 5 * r / (a : ℝ)) ^ (a ^ 2)) ^ 2 := by
  classical
  rcases Nat.eq_zero_or_pos a with rfl | ha0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.1 (by simpa using ha)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, pow_zero,
      ENNReal.ofReal_one, one_pow]
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty]
    exact prob_le_one
  · have hnpos : (0 : ℝ) < Fintype.card ι := by rw [ha]; push_cast; positivity
    have : Nonempty ι := Fintype.card_pos_iff.1 (by rw [ha]; positivity)
    have hset : {z : ι → ℂ | ∑ i, ‖z i‖ < 2 * r} =
        {z | (∑ i, ‖z i‖ ^ (1 : ℝ)) ^ (1 / (1 : ℝ)) < 2 * r} := by
      simp only [Real.rpow_one, div_one]
    have hG3 : Real.Gamma (2 / 1 + 1) = 2 := by
      have := Real.Gamma_nat_eq_factorial 2
      norm_num at this ⊢
    have hGn : Real.Gamma (2 * (Fintype.card ι : ℝ) / 1 + 1) = ((2 * Fintype.card ι).factorial : ℝ) := by
      rw [div_one, ← Real.Gamma_nat_eq_factorial]
      push_cast
      ring_nf
    rw [hset, Complex.volume_sum_rpow_lt ι le_rfl, hG3, hGn, ← ha,
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_pow (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    set n := Fintype.card ι with hn
    have hfac : ((2 : ℝ) * n) ^ n ≤ ((2 * n).factorial : ℝ) := by
      exact_mod_cast two_mul_pow_le_factorial n
    have han : (a : ℝ) ^ 2 = n := by exact_mod_cast ha.symm
    calc (2 * r) ^ (2 * n) * ((Real.pi * 2) ^ n / ((2 * n).factorial : ℝ))
        = (8 * Real.pi * r ^ 2) ^ n / ((2 * n).factorial : ℝ) := by
          rw [pow_mul, ← mul_div_assoc, ← mul_pow]
          congr 2
          ring
      _ ≤ (8 * Real.pi * r ^ 2) ^ n / ((2 : ℝ) * n) ^ n :=
          div_le_div_of_nonneg_left (by positivity) (pow_pos (by positivity) n) hfac
      _ = (4 * Real.pi * r ^ 2 / n) ^ n := by
          rw [← div_pow]
          congr 1
          field_simp
          ring
      _ ≤ (324 / 25 * r ^ 2 / n) ^ n := by
          apply pow_le_pow_left₀ (by positivity)
          gcongr
          linarith [Real.pi_lt_d2]
      _ = ((18 / 5 * r / a) ^ 2) ^ n := by
          congr 1
          rw [div_pow, han]
          ring
      _ = ((18 / 5 * r / a) ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

theorem lam_ballU_le (p q : ℕ) (lam : Measure (lieU p q)) (h : IsOmegaLeb lam) (r : ℝ) (hr : 0 < r) :
    lam (ballU p q r) ≤ ENNReal.ofReal ((18 / 5 * r / ((p + q : ℕ) : ℝ)) ^ ((p + q) ^ 2)) := by
  classical
  obtain ⟨hHaar, hmap⟩ := h
  have : BorelSpace (lieU p q) := ⟨rfl⟩
  have hcont : Continuous fun X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ =>
      Xᴴ * Formalism.UG.Jpq p q + Formalism.UG.Jpq p q * X :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).add
      (continuous_const.matrix_mul continuous_id)
  have hcl : IsClosed (lieU p q : Set (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) :=
    isClosed_eq hcont continuous_const
  have : LocallyCompactSpace (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin p ⊕ Fin q → Fin p ⊕ Fin q → ℂ))
  have : SecondCountableTopology (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin p ⊕ Fin q → Fin p ⊕ Fin q → ℂ))
  have : LocallyCompactSpace (lieU p q) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (lieU p q) :=
    hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  have : OpensMeasurableSpace (lieU p q × lieU p q) := inferInstance
  have : IsLocallyFiniteMeasure lam := inferInstance
  have : SigmaFinite lam := inferInstance
  have hc : Continuous fun ab : lieU p q × lieU p q =>
      (ab.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :=
    have h1 : Continuous fun ab : lieU p q × lieU p q =>
        (ab.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := continuous_subtype_val.comp continuous_fst
    have h2 : Continuous fun ab : lieU p q × lieU p q =>
        (ab.2 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := continuous_subtype_val.comp continuous_snd
    h1.add (h2.const_smul Complex.I)
  have hΦ : Measurable fun ab : lieU p q × lieU p q =>
      Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) :=
    (continuous_pi fun ij : (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) => hc.matrix_elem ij.1 ij.2).measurable
  have hS : MeasurableSet {z : (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) → ℂ | ∑ i, ‖z i‖ < 2 * r} :=
    (isOpen_lt (continuous_finsetSum _ fun i _ => (continuous_apply i).norm)
      continuous_const).measurableSet
  have hsub : ballU p q r ×ˢ ballU p q r ⊆ (fun ab : lieU p q × lieU p q =>
      Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ))) ⁻¹'
      {z | ∑ i, ‖z i‖ < 2 * r} := by
    rintro ⟨X, Y⟩ ⟨hX, hY⟩
    simp only [ballU, Set.mem_ofPred_eq] at hX hY
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Formalism.BasicNotions.entries, Fintype.sum_prod_type]
    calc ∑ i, ∑ j, ‖((X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) +
          Complex.I • (Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) i j‖
        ≤ ∑ i, ∑ j, (‖(X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖ +
          ‖(Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
          calc _ ≤ _ := norm_add_le _ _
            _ = _ := by rw [norm_mul, Complex.norm_I, one_mul]
      _ = (∑ i, ∑ j, ‖(X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖) +
          ∑ i, ∑ j, ‖(Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖ := by
          simp only [Finset.sum_add_distrib]
      _ < r + r := add_lt_add hX hY
      _ = 2 * r := by ring
  have hvol := volume_l1_ball_le (ι := (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q)) (p + q)
    (by simp [Fintype.card_prod, Fintype.card_sum, sq]) r hr
  have key : lam (ballU p q r) ^ 2 ≤
      ENNReal.ofReal ((18 / 5 * r / ((p + q : ℕ) : ℝ)) ^ ((p + q) ^ 2)) ^ 2 := by
    calc lam (ballU p q r) ^ 2 = (lam.prod lam) (ballU p q r ×ˢ ballU p q r) := by
          rw [Measure.prod_prod, sq]
      _ ≤ (lam.prod lam) ((fun ab : lieU p q × lieU p q =>
            Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) +
              Complex.I • (ab.2 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ))) ⁻¹'
            {z | ∑ i, ‖z i‖ < 2 * r}) := measure_mono hsub
      _ = ((lam.prod lam).map (fun ab : lieU p q × lieU p q =>
            Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) +
              Complex.I • (ab.2 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ))))
            {z | ∑ i, ‖z i‖ < 2 * r} := (Measure.map_apply hΦ hS).symm
      _ = volume {z : (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) → ℂ | ∑ i, ‖z i‖ < 2 * r} := by
          rw [hmap]
      _ ≤ _ := hvol
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 key

end GlobalTheory.CartanInt.LamBall
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LamBallULeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lam_ballU_le_ofReal_pow : ∀ (p q : ℕ) (lam : Measure (lieU p q)), IsOmegaLeb lam → ∀ r : ℝ, 0 < r → lam (ballU p q r) ≤ ENNReal.ofReal ((18 / 5 * r / ((p + q : ℕ) : ℝ)) ^ ((p + q) ^ 2)) := by
  first | exact @GlobalTheory.CartanInt.LamBall.lam_ballU_le | exact GlobalTheory.CartanInt.LamBall.lam_ballU_le | (intros; apply GlobalTheory.CartanInt.LamBall.lam_ballU_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsometricChartBlockHermitian
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsometricChartBlockHermitian
noncomputable section
namespace GlobalTheory.CartanInt.HermChart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

def herm {n : Type} (S : n → n → ℝ) : Matrix n n ℂ :=
  Matrix.of fun i j => (⟨(S i j + S j i) / 2, (S i j - S j i) / 2⟩ : ℂ)

theorem herm_apply {n : Type} (S : n → n → ℝ) (i j : n) :
    herm S i j = (⟨(S i j + S j i) / 2, (S i j - S j i) / 2⟩ : ℂ) := rfl

theorem herm_conjTranspose {n : Type} (S : n → n → ℝ) : (herm S)ᴴ = herm S := by
  ext i j
  rw [Matrix.conjTranspose_apply, herm_apply, herm_apply]
  apply Complex.ext
  · simp only [Complex.star_def, Complex.conj_re]; ring
  · simp only [Complex.star_def, Complex.conj_im]; ring

theorem continuous_herm_entry {X n : Type} [TopologicalSpace X] {f : X → n → n → ℝ}
    (hf : ∀ i j, Continuous fun x => f x i j) (i j : n) : Continuous fun x => herm (f x) i j := by
  have e : (fun x => herm (f x) i j) = fun x => (((f x i j + f x j i) / 2 : ℝ) : ℂ) +
      (((f x i j - f x j i) / 2 : ℝ) : ℂ) * Complex.I := by
    funext x
    rw [herm_apply, Complex.mk_eq_add_mul_I]
  rw [e]
  have h1 := hf i j
  have h2 := hf j i
  fun_prop

theorem sum_norm_sq_herm_sub {n : Type} [Fintype n] (S T : n → n → ℝ) :
    ∑ i, ∑ j, ‖herm S i j - herm T i j‖ ^ 2 = ∑ i, ∑ j, (S i j - T i j) ^ 2 := by
  have h : ∀ i j, ‖herm S i j - herm T i j‖ ^ 2 =
      (S i j - T i j) ^ 2 / 2 + (S j i - T j i) ^ 2 / 2 := by
    intro i j
    rw [Complex.sq_norm, Complex.normSq_apply, herm_apply, herm_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  simp only [h, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => (S j i - T j i) ^ 2 / 2), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem herm_re_add_im {n : Type} (H : n → n → ℂ) (hH : ∀ i j, star (H j i) = H i j) (i j : n) :
    herm (fun i j => (H i j).re + (H i j).im) i j = H i j := by
  have h1 := congrArg Complex.re (hH i j)
  have h2 := congrArg Complex.im (hH i j)
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im] at h1 h2
  rw [herm_apply]
  apply Complex.ext
  · show _ / (2 : ℝ) = _
    linarith
  · show _ / (2 : ℝ) = _
    linarith

theorem abs_re_add_im_le {z : ℂ} (hz : ‖z‖ ≤ Real.pi) : |z.re + z.im| ≤ 89 / 20 := by
  have h1 : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by rw [Complex.sq_norm, Complex.normSq_apply]
  have h2 : ‖z‖ ≤ 3.1416 := hz.trans Real.pi_lt_d4.le
  have h3 : ‖z‖ ^ 2 ≤ 3.1416 ^ 2 := pow_le_pow_left₀ (norm_nonneg z) h2 2
  refine abs_le_of_sq_le_sq' ?_ (by norm_num) |> abs_le.2
  nlinarith [sq_nonneg (z.re - z.im)]

theorem exists_chart : ∀ (p q : ℕ), ∃ Φ : ((Fin p × Fin p) ⊕ (Fin q × Fin q) → ℝ) → Mat p q,
    Continuous Φ ∧ (∀ R, (Φ R)ᴴ = Φ R ∧ IsKC (Φ R)) ∧
    (∀ R R', ∑ a, ∑ b, ‖(Φ R - Φ R') a b‖ ^ 2 = ∑ i, (R i - R' i) ^ 2) ∧
    ∀ H : Mat p q, Hᴴ = H → IsKC H → (∀ a b, ‖H a b‖ ≤ Real.pi) →
      ∃ R, Φ R = H ∧ ∀ i, |R i| ≤ 89 / 20 := by
  intro p q
  refine ⟨fun R => Matrix.fromBlocks (herm fun i j => R (Sum.inl (i, j))) 0 0
    (herm fun i j => R (Sum.inr (i, j))), ?_, fun R => ⟨?_, isKC_fromBlocks _ _⟩, fun R R' => ?_,
    fun H hH hK hb => ?_⟩
  · refine continuous_matrix fun a b => ?_
    rcases a with a | a <;> rcases b with b | b
    · exact continuous_herm_entry (f := fun (R : (Fin p × Fin p) ⊕ (Fin q × Fin q) → ℝ) i j =>
        R (Sum.inl (i, j))) (fun i j => continuous_apply _) a b
    · exact continuous_const
    · exact continuous_const
    · exact continuous_herm_entry (f := fun (R : (Fin p × Fin p) ⊕ (Fin q × Fin q) → ℝ) i j =>
        R (Sum.inr (i, j))) (fun i j => continuous_apply _) a b
  · simp only [Matrix.fromBlocks_conjTranspose, herm_conjTranspose, Matrix.conjTranspose_zero]
  · rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type,
      ← sum_norm_sq_herm_sub (fun i j => R (Sum.inl (i, j))) (fun i j => R' (Sum.inl (i, j))),
      ← sum_norm_sq_herm_sub (fun i j => R (Sum.inr (i, j))) (fun i j => R' (Sum.inr (i, j)))]
    simp [Fintype.sum_sum_type]
  · have hs : ∀ a b, star (H b a) = H a b := fun a b => by
      rw [← Matrix.conjTranspose_apply, hH]
    refine ⟨Sum.elim (fun x => (H (Sum.inl x.1) (Sum.inl x.2)).re + (H (Sum.inl x.1) (Sum.inl x.2)).im)
      (fun x => (H (Sum.inr x.1) (Sum.inr x.2)).re + (H (Sum.inr x.1) (Sum.inr x.2)).im), ?_, ?_⟩
    · ext a b
      rcases a with a | a <;> rcases b with b | b
      · exact herm_re_add_im (fun i j => H (Sum.inl i) (Sum.inl j)) (fun i j => hs _ _) a b
      · exact (hK _ _ (by simp [sameBlock])).symm
      · exact (hK _ _ (by simp [sameBlock])).symm
      · exact herm_re_add_im (fun i j => H (Sum.inr i) (Sum.inr j)) (fun i j => hs _ _) a b
    · rintro (x | x)
      · exact abs_re_add_im_le (hb _ _)
      · exact abs_re_add_im_le (hb _ _)

end GlobalTheory.CartanInt.HermChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsometricChartBlockHermitianStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isometric_chart_blockHermitian : ∀ (p q : ℕ), ∃ Φ : ((Fin p × Fin p) ⊕ (Fin q × Fin q) → ℝ) → Mat p q, Continuous Φ ∧ (∀ R, (Φ R)ᴴ = Φ R ∧ IsKC (Φ R)) ∧ (∀ R R', ∑ a, ∑ b, ‖(Φ R - Φ R') a b‖ ^ 2 = ∑ i, (R i - R' i) ^ 2) ∧ ∀ H : Mat p q, Hᴴ = H → IsKC H → (∀ a b, ‖H a b‖ ≤ Real.pi) → ∃ R, Φ R = H ∧ ∀ i, |R i| ≤ 89 / 20 := by
  first | exact @GlobalTheory.CartanInt.HermChart.exists_chart | exact GlobalTheory.CartanInt.HermChart.exists_chart | (intros; apply GlobalTheory.CartanInt.HermChart.exists_chart <;> assumption)
end
end
