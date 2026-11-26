module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.AnalyticTransOfAdd
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CurveIntegerMultiplicationSeries
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionSetSubgroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeierstrassPIntegralOfMulIntegralGoodReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeierstrassPIntegralOfMulIntegralGoodReduction
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory.Honda

theorem integral_of_mul_integral : ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]), ‖ι L.g₂‖ ≤ 1 → ‖ι L.g₃‖ ≤ 1 → ‖ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2‖ = 1 → ∀ (z : ℂ) (N : ℕ), (N : ℂ) * z ∉ L.lattice → ‖ι (L.weierstrassP (N * z))‖ ≤ 1 → ‖ι (L.weierstrassP z)‖ ≤ 1 := by
  intro L l _ hl ι h2 h3 hd z N hN hP
  have hg : GlobalTheory.Klein.Good ι L 0 := by
    refine ⟨by omega, by simp, ?_, ?_, ?_⟩
    · simpa using h2
    · simpa using h3
    · simpa [map_sub, map_mul, map_pow, map_ofNat] using hd
  obtain ⟨-, -, -, G, hG, -⟩ := GlobalTheory.Klein.not_red_addSubgroup l ι L 0 hg
  by_contra hc
  have hz : z ∈ G := by
    rw [hG]; intro h; exact hc (by simpa using h.2)
  have hNz : (N : ℂ) * z ∈ G := by
    have := G.nsmul_mem hz N
    simpa [nsmul_eq_mul] using this
  rw [hG] at hNz
  exact hNz ⟨hN, by simpa using hP⟩

end GlobalTheory.Honda
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeierstrassPIntegralOfMulIntegralGoodReductionStatement
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassP_integral_of_mul_integral_good_reduction : ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]), ‖ι L.g₂‖ ≤ 1 → ‖ι L.g₃‖ ≤ 1 → ‖ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2‖ = 1 → ∀ (z : ℂ) (N : ℕ), (N : ℂ) * z ∉ L.lattice → ‖ι (L.weierstrassP (N * z))‖ ≤ 1 → ‖ι (L.weierstrassP z)‖ ≤ 1 := by
  first | exact @GlobalTheory.Honda.integral_of_mul_integral | exact GlobalTheory.Honda.integral_of_mul_integral | (intros; apply GlobalTheory.Honda.integral_of_mul_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeierstrassPOddMulSubTwoTorsionProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeierstrassPOddMulSubTwoTorsionProduct
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

noncomputable section

namespace GlobalTheory.OddHalfProduct

open Formalism.L2.Th1.F

def qf (L : PeriodPair) (y ω : ℂ) : ℂ :=
  semiChar L ω * Complex.exp ((Real.pi : ℂ) * herm L y ω + (Real.pi : ℂ) * herm L ω ω / 2)

lemma sg_quasi (L : PeriodPair) {ω : ℂ} (hω : ω ∈ L.lattice) (y : ℂ) :
    sgStar L (y + ω) = qf L y ω * sgStar L y := by
  rw [sgStarQuasi L ω y hω]; rfl

lemma qf_ne (L : PeriodPair) (y ω : ℂ) : qf L y ω ≠ 0 := by
  unfold qf semiChar
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  split_ifs <;> norm_num

lemma qf_shift (L : PeriodPair) (y z ω : ℂ) :
    qf L (y + z) ω = qf L y ω * Complex.exp ((Real.pi : ℂ) * herm L z ω) := by
  unfold qf
  have : (Real.pi : ℂ) * herm L (y + z) ω + (Real.pi : ℂ) * herm L ω ω / 2
      = ((Real.pi : ℂ) * herm L y ω + (Real.pi : ℂ) * herm L ω ω / 2) + (Real.pi : ℂ) * herm L z ω := by
    unfold herm; ring
  rw [this, Complex.exp_add]; ring

lemma sg_ne (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) : sgStar L z ≠ 0 :=
  fun h => hz (((sgStarBasic L).2.2.1 z).1 h)

lemma sg_zero (L : PeriodPair) {z : ℂ} (hz : z ∈ L.lattice) : sgStar L z = 0 :=
  ((sgStarBasic L).2.2.1 z).2 hz

lemma sg_neg (L : PeriodPair) (z : ℂ) : sgStar L (-z) = -sgStar L z := (sgStarBasic L).2.1 z

lemma iso_prod (L : PeriodPair) (n : ℕ) (S : Finset ℂ) (hn : (n : ℂ) ≠ 0) (hst : MulStable L n)
    (hS : IsKerReps L n S) (hev : Even S.card) (w : ℂ) :
    (∏ P ∈ S, sgStar L P ^ 2) * sgStar L (n * w) ^ 2
      = (n : ℂ) ^ 2 * (sgStar L w ^ 2 * ∏ P ∈ S, (sgStar L (w + P) * sgStar L (w - P))) := by
  by_cases hw : w ∈ L.lattice
  · rw [sg_zero L (hst w hw), sg_zero L hw]; ring
  · have hI := isogenySigma L n S hn hst hS w hw
    have h2 : ∏ P ∈ S, (sgStar L (w + P) * sgStar L (w - P))
        = ∏ P ∈ S, ((-1) * (sgStar L w ^ 2 * sgStar L P ^ 2 * (L.weierstrassP w - L.weierstrassP P))) :=
      Finset.prod_congr rfl (fun P hP => by rw [sgStarAdd L w P hw (hS.1 P hP).2]; ring)
    rw [h2]
    simp only [Finset.prod_mul_distrib, Finset.prod_const, hev.neg_one_pow]
    rw [hI]; ring

lemma sigma_id (L : PeriodPair) (n m : ℕ) (hnC : (n : ℂ) = 2 * m + 1) (S : Finset ℂ) (t : ℂ)
    (hn : (n : ℂ) ≠ 0) (hst : MulStable L n) (hS : IsKerReps L n S) (hev : Even S.card)
    (hcard : (S.card : ℂ) + 1 = (n : ℂ) ^ 2)
    (ht : t ∉ L.lattice) (h2t : 2 * t ∈ L.lattice) (z : ℂ) :
    (∏ P ∈ S, sgStar L (t + P) ^ 2) * (sgStar L (n * z + t) * sgStar L (n * z - t))
      = sgStar L (z + t) * sgStar L (z - t)
        * ∏ P ∈ S, (sgStar L (z + t + P) * sgStar L (z - t - P)) := by
  have h2mt : (m : ℂ) * (2 * t) ∈ L.lattice := by rw [← nsmul_eq_mul]; exact nsmul_mem h2t m
  let Φ₁ : ℂ → ℂ := fun z => qf L (z - t) (2 * t) * ∏ P ∈ S, qf L (z - t - P) (2 * t)
  let Φ₂ : ℂ → ℂ := fun z => qf L (n * z + t) (m * (2 * t)) ^ 2 * qf L (n * z - t) (2 * t)
  let G : ℂ → ℂ := fun z => sgStar L (z + t) * sgStar L (z - t)
    * ∏ P ∈ S, (sgStar L (z + t + P) * sgStar L (z - t - P))
  let F : ℂ → ℂ := fun z => sgStar L (n * z + t) * sgStar L (n * z - t)
  let D : ℂ := ∏ P ∈ S, sgStar L (t + P) ^ 2
  let C : ℂ := ∏ P ∈ S, sgStar L P ^ 2
  have hG : ∀ z, sgStar L (z + t) ^ 2 * ∏ P ∈ S, (sgStar L (z + t + P) * sgStar L (z + t - P))
      = Φ₁ z * G z := by
    intro z
    have e1 : sgStar L (z + t) = qf L (z - t) (2 * t) * sgStar L (z - t) := by
      rw [← sg_quasi L h2t]; congr 1; ring
    have e2 : ∀ P, sgStar L (z + t + P) * sgStar L (z + t - P)
        = qf L (z - t - P) (2 * t) * (sgStar L (z + t + P) * sgStar L (z - t - P)) := by
      intro P; rw [show z + t - P = (z - t - P) + 2 * t by ring, sg_quasi L h2t]; ring
    rw [Finset.prod_congr rfl (fun P _ => e2 P), Finset.prod_mul_distrib]
    show _ = (qf L (z - t) (2 * t) * ∏ P ∈ S, qf L (z - t - P) (2 * t))
      * (sgStar L (z + t) * sgStar L (z - t) * ∏ P ∈ S, (sgStar L (z + t + P) * sgStar L (z - t - P)))
    linear_combination (sgStar L (z + t) * (∏ P ∈ S, qf L (z - t - P) (2 * t))
      * ∏ P ∈ S, (sgStar L (z + t + P) * sgStar L (z - t - P))) * e1
  have hF : ∀ z, sgStar L (n * (z + t)) ^ 2 = Φ₂ z * F z := by
    intro z
    have e1 : sgStar L (n * (z + t)) = qf L (n * z + t) (m * (2 * t)) * sgStar L (n * z + t) := by
      rw [← sg_quasi L h2mt]; congr 1; rw [hnC]; ring
    have e2 : sgStar L (n * z + t) = qf L (n * z - t) (2 * t) * sgStar L (n * z - t) := by
      rw [← sg_quasi L h2t]; congr 1; ring
    rw [e1]
    show _ = (qf L (n * z + t) (m * (2 * t)) ^ 2 * qf L (n * z - t) (2 * t))
      * (sgStar L (n * z + t) * sgStar L (n * z - t))
    linear_combination (qf L (n * z + t) (m * (2 * t)) ^ 2 * sgStar L (n * z + t)) * e2
  have hΦ : ∀ z, Φ₁ z * Φ₂ 0 = Φ₁ 0 * Φ₂ z := by
    intro z
    have a0 : qf L (z - t) (2 * t) = qf L (0 - t) (2 * t) * Complex.exp ((Real.pi : ℂ) * herm L z (2 * t)) := by
      rw [show z - t = (0 - t) + z by ring, qf_shift]
    have a1 : ∀ P, qf L (z - t - P) (2 * t)
        = qf L (0 - t - P) (2 * t) * Complex.exp ((Real.pi : ℂ) * herm L z (2 * t)) := by
      intro P; rw [show z - t - P = (0 - t - P) + z by ring, qf_shift]
    have b0 : qf L (n * z + t) (m * (2 * t))
        = qf L (n * 0 + t) (m * (2 * t)) * Complex.exp ((Real.pi : ℂ) * herm L (n * z) (m * (2 * t))) := by
      rw [show (n : ℂ) * z + t = (n * 0 + t) + n * z by ring, qf_shift]
    have b1 : qf L (n * z - t) (2 * t)
        = qf L (n * 0 - t) (2 * t) * Complex.exp ((Real.pi : ℂ) * herm L (n * z) (2 * t)) := by
      rw [show (n : ℂ) * z - t = (n * 0 - t) + n * z by ring, qf_shift]
    have hE : Complex.exp ((Real.pi : ℂ) * herm L z (2 * t)) ^ (S.card + 1)
        = Complex.exp ((Real.pi : ℂ) * herm L (n * z) (m * (2 * t))) ^ 2
          * Complex.exp ((Real.pi : ℂ) * herm L (n * z) (2 * t)) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      rw [hcard, hnC]
      simp only [herm, map_mul, map_natCast, map_ofNat]
      ring
    show (qf L (z - t) (2 * t) * ∏ P ∈ S, qf L (z - t - P) (2 * t)) * Φ₂ 0
      = Φ₁ 0 * (qf L (n * z + t) (m * (2 * t)) ^ 2 * qf L (n * z - t) (2 * t))
    rw [a0, Finset.prod_congr rfl (fun P _ => a1 P), Finset.prod_mul_distrib, Finset.prod_const, b0, b1]
    show _ = (qf L (0 - t) (2 * t) * ∏ P ∈ S, qf L (0 - t - P) (2 * t))
      * ((qf L (n * 0 + t) (m * (2 * t)) * _) ^ 2 * (qf L (n * 0 - t) (2 * t) * _))
    rw [show ∀ a b c d e : ℂ, a * e * (b * e ^ S.card) * (c ^ 2 * d) = a * b * (c ^ 2 * d) * e ^ (S.card + 1)
      from fun a b c d e => by ring, hE]
    ring
  have star : ∀ z, (n : ℂ) ^ 2 * Φ₁ z * G z = C * Φ₂ z * F z := by
    intro z
    have h1 := iso_prod L n S hn hst hS hev (z + t)
    have h2 := hG z
    have h3 := hF z
    linear_combination (-1 : ℂ) * h1 - (n : ℂ) ^ 2 * h2 + C * h3
  have k1 : ∀ z, (n : ℂ) ^ 2 * Φ₁ 0 * G z = C * Φ₂ 0 * F z := by
    intro z
    have hne : Φ₂ z ≠ 0 := mul_ne_zero (pow_ne_zero 2 (qf_ne _ _ _)) (qf_ne _ _ _)
    apply mul_right_cancel₀ hne
    linear_combination Φ₂ 0 * star z - (n : ℂ) ^ 2 * G z * hΦ z
  have hF0 : F 0 = -sgStar L t ^ 2 := by
    show sgStar L (n * 0 + t) * sgStar L (n * 0 - t) = _
    rw [mul_zero, zero_add, zero_sub, sg_neg]; ring
  have hF0ne : F 0 ≠ 0 := by rw [hF0]; exact neg_ne_zero.mpr (pow_ne_zero 2 (sg_ne L ht))
  have hG0 : G 0 = D * F 0 := by
    have e : ∀ P, sgStar L (0 + t + P) * sgStar L (0 - t - P) = (-1) * sgStar L (t + P) ^ 2 := by
      intro P; rw [zero_add, show (0 : ℂ) - t - P = -(t + P) by ring, sg_neg]; ring
    rw [hF0]
    show sgStar L (0 + t) * sgStar L (0 - t) * ∏ P ∈ S, (sgStar L (0 + t + P) * sgStar L (0 - t - P)) = _
    rw [Finset.prod_congr rfl (fun P _ => e P), Finset.prod_mul_distrib, Finset.prod_const,
      hev.neg_one_pow, zero_add, zero_sub, sg_neg]
    ring
  have hC : C * Φ₂ 0 = (n : ℂ) ^ 2 * Φ₁ 0 * D := by
    apply mul_right_cancel₀ hF0ne
    have := k1 0
    rw [hG0] at this
    linear_combination -this
  have hne : (n : ℂ) ^ 2 * Φ₁ 0 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hn)
      (mul_ne_zero (qf_ne _ _ _) (Finset.prod_ne_zero_iff.mpr (fun P _ => qf_ne _ _ _)))
  show D * F z = G z
  apply mul_left_cancel₀ hne
  linear_combination -(k1 z) - F z * hC

theorem wp_odd_mul_sub_half_prod : ∀ (L : PeriodPair) (n : ℕ) (S : Finset ℂ) (t : ℂ), Odd n →
    Formalism.L2.Th1.F.IsKerReps L (n : ℂ) S → t ∉ L.lattice → 2 * t ∈ L.lattice → ∀ z, (n : ℂ) * z ∉ L.lattice →
    (n : ℂ) ^ 2 * (L.weierstrassP (n * z) - L.weierstrassP t) * ∏ P ∈ S, (L.weierstrassP z - L.weierstrassP P)
      = (L.weierstrassP z - L.weierstrassP t) * ∏ P ∈ S, (L.weierstrassP z - L.weierstrassP (t + P)) := by
  intro L n S t hodd hS ht h2t z hnz
  obtain ⟨m, hm⟩ := hodd
  have hnC : (n : ℂ) = 2 * m + 1 := by rw [hm]; push_cast; ring
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hst : MulStable L n := fun ω hω => by rw [← nsmul_eq_mul]; exact nsmul_mem hω n
  have hcardR := kerRepsCard L n S hn hst hS
  have hcardN : S.card + 1 = n ^ 2 := by
    have : Complex.normSq (n : ℂ) = (n : ℝ) ^ 2 := by rw [Complex.normSq_apply]; simp; ring
    rw [this] at hcardR; exact_mod_cast hcardR
  have hcard : (S.card : ℂ) + 1 = (n : ℂ) ^ 2 := by exact_mod_cast hcardN
  have hS4 : S.card = 4 * (m * m + m) :=
    Nat.add_right_cancel (by rw [hcardN, hm]; ring : S.card + 1 = 4 * (m * m + m) + 1)
  have hev : Even S.card := ⟨2 * (m * m + m), by rw [hS4]; ring⟩
  have hzL : z ∉ L.lattice := fun h => hnz (by rw [← nsmul_eq_mul]; exact nsmul_mem h n)
  have htP : ∀ P ∈ S, t + P ∉ L.lattice := by
    intro P hP h
    have hnP := (hS.1 P hP).1
    have h2P : 2 * P ∈ L.lattice := by
      have := sub_mem (nsmul_mem h 2) h2t
      convert this using 1; rw [nsmul_eq_mul]; push_cast; ring
    have hPL : P ∈ L.lattice := by
      have := sub_mem hnP (nsmul_mem h2P m)
      convert this using 1; rw [nsmul_eq_mul, hnC]; ring
    exact (hS.1 P hP).2 hPL
  have hsig := sigma_id L n m hnC S t hn hst hS hev hcard ht h2t z
  have hD : ∏ P ∈ S, sgStar L (t + P) ^ 2 ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun P hP => pow_ne_zero 2 (sg_ne L (htP P hP)))
  have hM : sgStar L z ^ (2 * (S.card + 1)) * sgStar L t ^ 2 * ∏ P ∈ S, sgStar L (t + P) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (sg_ne L hzL)) (pow_ne_zero 2 (sg_ne L ht))) hD
  apply mul_right_cancel₀ hM
  have hI := isogenySigma L n S hn hst hS z hzL
  have hadd1 := sgStarAdd L (n * z) t hnz ht
  have hadd2 := sgStarAdd L z t hzL ht
  have hprod : ∏ P ∈ S, (sgStar L (z + t + P) * sgStar L (z - t - P))
      = (sgStar L z ^ 2) ^ S.card * (∏ P ∈ S, sgStar L (t + P) ^ 2)
        * ∏ P ∈ S, (L.weierstrassP z - L.weierstrassP (t + P)) := by
    have e : ∀ P ∈ S, sgStar L (z + t + P) * sgStar L (z - t - P)
        = (-1) * (sgStar L z ^ 2 * sgStar L (t + P) ^ 2 * (L.weierstrassP z - L.weierstrassP (t + P))) := by
      intro P hP
      rw [show z + t + P = z + (t + P) by ring, show z - t - P = z - (t + P) by ring,
        sgStarAdd L z (t + P) hzL (htP P hP)]
      ring
    rw [Finset.prod_congr rfl e]
    simp only [Finset.prod_mul_distrib, Finset.prod_const, hev.neg_one_pow]
    ring
  linear_combination (-((L.weierstrassP (n * z) - L.weierstrassP t) * sgStar L t ^ 2
      * ∏ P ∈ S, sgStar L (t + P) ^ 2)) * hI
    + (∏ P ∈ S, sgStar L (t + P) ^ 2) * hadd1 - hsig
    - (∏ P ∈ S, (sgStar L (z + t + P) * sgStar L (z - t - P))) * hadd2
    + (sgStar L z ^ 2 * sgStar L t ^ 2 * (L.weierstrassP z - L.weierstrassP t)) * hprod

end GlobalTheory.OddHalfProduct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeierstrassPOddMulSubTwoTorsionProductStatement
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassP_odd_mul_sub_twoTorsion_product : ∀ (L : PeriodPair) (n : ℕ) (S : Finset ℂ) (t : ℂ), Odd n → Formalism.L2.Th1.F.IsKerReps L (n : ℂ) S → t ∉ L.lattice → 2 * t ∈ L.lattice → ∀ z, (n : ℂ) * z ∉ L.lattice → (n : ℂ) ^ 2 * (L.weierstrassP (n * z) - L.weierstrassP t) * ∏ P ∈ S, (L.weierstrassP z - L.weierstrassP P) = (L.weierstrassP z - L.weierstrassP t) * ∏ P ∈ S, (L.weierstrassP z - L.weierstrassP (t + P)) := by
  first | exact @GlobalTheory.OddHalfProduct.wp_odd_mul_sub_half_prod | exact GlobalTheory.OddHalfProduct.wp_odd_mul_sub_half_prod | (intros; apply GlobalTheory.OddHalfProduct.wp_odd_mul_sub_half_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormWeierstrassPSubEqOneOfGood
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory.Honda

theorem norm_weierstrassP_sub_eq_one_of_good :
    ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]), ‖ι L.g₂‖ ≤ 1 → ‖ι L.g₃‖ ≤ 1 →
      ‖ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2‖ = 1 → ∀ u v : ℂ, u ∉ L.lattice → v ∉ L.lattice → u + v ∉ L.lattice →
      u - v ∉ L.lattice → ‖ι (L.weierstrassP u)‖ ≤ 1 → ‖ι (L.weierstrassP v)‖ ≤ 1 →
      ‖ι (L.weierstrassP (u + v))‖ ≤ 1 → ‖ι (L.weierstrassP (u - v))‖ ≤ 1 →
      ‖ι (L.weierstrassP u) - ι (L.weierstrassP v)‖ = 1 := by
  intro L l _ hl ι hg2 hg3 hD u v hu hv huv hmuv hpu hpv hpuv hpmuv
  have hgood : GlobalTheory.Klein.Good ι L 0 := by
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · simp
    · simpa using hg2
    · simpa using hg3
    · rw [map_sub, map_pow, map_mul, map_pow, map_ofNat]; exact hD
  have hred : ∀ z, z ∉ L.lattice → ‖ι (L.weierstrassP z)‖ ≤ 1 → GlobalTheory.Klein.Red ι L 0 z :=
    fun z hz hp => ⟨hz, by simpa using hp⟩
  have h := GlobalTheory.Klein.norm_weierstrassP_sub_eq_one l ι L 0 hgood u v (hred u hu hpu) (hred v hv hpv)
    (hred _ huv hpuv) (hred _ hmuv hpmuv)
  simpa [map_sub] using h

end GlobalTheory.Honda
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicationSeriesUnitCoeffNormLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicationSeriesUnitCoeffNormLe
noncomputable section

namespace GlobalTheory.Honda

open PowerSeries

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem htform_norm_sum_lt {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ j ∈ s, ‖f j‖ < 1) :
    ‖∑ j ∈ s, f j‖ < 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _)
      (max_lt (h a (by simp)) (ih fun j hj => h j (by simp [hj])))

theorem htform_norm_sum_le {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ j ∈ s, ‖f j‖ ≤ 1) :
    ‖∑ j ∈ s, f j‖ ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (IsUltrametricDist.norm_add_le_max _ _)
      (max_le (h a (by simp)) (ih fun j hj => h j (by simp [hj])))

def HtSmallTo (N : ℕ) (f : K⟦X⟧) : Prop := CoefLe 1 f ∧ ∀ n < N, ‖coeff n f‖ < 1

theorem HtSmallTo.mul {a b : ℕ} {f g : K⟦X⟧} (hf : HtSmallTo a f) (hg : HtSmallTo b g) :
    HtSmallTo (a + b) (f * g) := by
  constructor
  · intro n
    rw [coeff_mul]
    apply htform_norm_sum_le
    rintro ⟨i, j⟩ _
    rw [norm_mul]
    exact mul_le_one₀ (hf.1 i) (norm_nonneg _) (hg.1 j)
  · intro n hn
    rw [coeff_mul]
    apply htform_norm_sum_lt
    rintro ⟨i, j⟩ hij
    have hs : i + j = n := by simpa using hij
    rw [norm_mul]
    by_cases hi : i < a
    · exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (hf.2 i hi) (hg.1 j)
    · have hj : j < b := by omega
      exact mul_lt_one_of_nonneg_of_lt_one_right (hf.1 i) (norm_nonneg _) (hg.2 j hj)

theorem htSmallTo_zero_iff (f : K⟦X⟧) : HtSmallTo 0 f ↔ CoefLe 1 f :=
  ⟨fun h => h.1, fun h => ⟨h, fun n hn => absurd hn (Nat.not_lt_zero _)⟩⟩

theorem htSmallTo_one : HtSmallTo 0 (1 : K⟦X⟧) := by
  rw [htSmallTo_zero_iff]
  intro n
  rw [coeff_one]
  split_ifs <;> simp

theorem htSmallTo_pow {f : K⟦X⟧} (hf : HtSmallTo 0 f) (d : ℕ) : HtSmallTo 0 (f ^ d) := by
  induction d with
  | zero => simpa using htSmallTo_one
  | succ d ih => simpa [pow_succ] using ih.mul hf

theorem htSmallTo_X_pow (k : ℕ) : HtSmallTo 0 ((X : K⟦X⟧) ^ k) := by
  rw [htSmallTo_zero_iff]
  intro n
  rw [coeff_X_pow]
  split_ifs <;> simp

theorem htSmallTo_C_mul {c : K} (hc : ‖c‖ ≤ 1) {f : K⟦X⟧} (hf : HtSmallTo 0 f) :
    HtSmallTo 0 (C c * f) := by
  rw [htSmallTo_zero_iff]
  intro n
  rw [coeff_C_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) (hf.1 n)

theorem htSmallTo_sum {ι : Type} (s : Finset ι) (f : ι → K⟦X⟧) (h : ∀ j ∈ s, HtSmallTo 0 (f j)) :
    HtSmallTo 0 (∑ j ∈ s, f j) := by
  rw [htSmallTo_zero_iff]
  intro n
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact htform_norm_sum_le _ _ fun j hj => (h j hj).1 n

theorem htSmallTo_sub {f g : K⟦X⟧} (hf : HtSmallTo 0 f) (hg : HtSmallTo 0 g) : HtSmallTo 0 (f - g) := by
  rw [htSmallTo_zero_iff]
  intro n
  rw [map_sub, sub_eq_add_neg]
  exact le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le (hf.1 n) (by rw [norm_neg]; exact hg.1 n))

theorem htSmallTo_inv {B : K⟦X⟧} (hB : CoefLe 1 B) (h0 : constantCoeff B = 1) : HtSmallTo 0 B⁻¹ := by
  rw [htSmallTo_zero_iff]
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rw [coeff_inv]
  split_ifs with hn
  · simp [h0]
  · rw [h0, inv_one, neg_mul, one_mul, norm_neg]
    apply htform_norm_sum_le
    rintro ⟨i, j⟩ _
    dsimp only
    split_ifs with hj
    · rw [norm_mul]
      exact mul_le_one₀ (hB i) (norm_nonneg _) (ih j hj)
    · simp

theorem htform_coeff_vpow_eq_zero {v : K⟦X⟧} (h0 : constantCoeff v = 0) {n d : ℕ} (h : n < d) :
    coeff n (v ^ d) = 0 := by
  obtain ⟨w, rfl⟩ := X_dvd_iff.mpr h0
  rw [mul_pow, coeff_X_pow_mul', if_neg (by omega)]

theorem htform_coeff_subst (A v : K⟦X⟧) (h0 : constantCoeff v = 0) (n : ℕ) :
    coeff n (A.subst v) = ∑ d ∈ Finset.range (n + 1), coeff d A * coeff n (v ^ d) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' h0)]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1))]
  · simp [smul_eq_mul]
  · intro d hd
    simp only [Function.mem_support] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    exact hd (by rw [htform_coeff_vpow_eq_zero h0 (by omega), smul_zero])

theorem htSmallTo_subst {A v : K⟦X⟧} (hA : CoefLe 1 A) (hv : CoefLe 1 v) (h0 : constantCoeff v = 0) :
    HtSmallTo 0 (A.subst v) := by
  rw [htSmallTo_zero_iff]
  intro n
  rw [htform_coeff_subst A v h0]
  apply htform_norm_sum_le
  intro d _
  rw [norm_mul]
  exact mul_le_one₀ (hA d) (norm_nonneg _) ((htSmallTo_pow ((htSmallTo_zero_iff v).2 hv) d).1 n)

theorem htform_constantCoeff_subst (A v : K⟦X⟧) (h0 : constantCoeff v = 0) :
    constantCoeff (A.subst v) = constantCoeff A := by
  rw [← coeff_zero_eq_constantCoeff_apply, htform_coeff_subst A v h0]
  simp

theorem htform_unit_coeff_le : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (A v : K⟦X⟧) (e e' : K) (M : ℕ) (Dp Np : Polynomial K), CoefLe 1 A → constantCoeff A = 1 → CoefLe 1 v → constantCoeff v = 0 → ‖e‖ ≤ 1 → ‖e'‖ ≤ 1 → Np.Monic → Np.natDegree = M + 1 → (∀ i, ‖Np.coeff i‖ ≤ 1) → Dp.natDegree ≤ M → ‖Dp.eval e'‖ = 1 → (A.subst v - C e * v ^ 2) * (∑ i ∈ Finset.range (M + 1), C (Dp.coeff i) * A ^ i * X ^ (2 * (M - i))) * X ^ 2 = v ^ 2 * ∑ i ∈ Finset.range (M + 2), C (Np.coeff i) * A ^ i * X ^ (2 * (M + 1 - i)) → ∃ n, n ≤ M + 1 ∧ ‖coeff n v‖ = 1 := by
  intro K _ _ _ A v e e' M Dp Np hA hA0 hv hv0 he he' _ _ hNc hDdeg hDe heq
  by_contra hcon
  push_neg at hcon
  have hvs : HtSmallTo (M + 2) v := ⟨hv, fun n hn => lt_of_le_of_ne (hv n) (hcon n (by omega))⟩
  have hA' : HtSmallTo 0 A := (htSmallTo_zero_iff A).2 hA
  have hB : HtSmallTo 0 (A.subst v - C e * v ^ 2) :=
    htSmallTo_sub (htSmallTo_subst hA hv hv0) (htSmallTo_C_mul he (htSmallTo_pow ((htSmallTo_zero_iff v).2 hv) 2))
  have hB0 : constantCoeff (A.subst v - C e * v ^ 2) = 1 := by
    rw [map_sub, htform_constantCoeff_subst A v hv0, hA0, map_mul, map_pow, hv0]
    simp
  have hH : HtSmallTo 0 (∑ i ∈ Finset.range (M + 2), C (Np.coeff i) * A ^ i * X ^ (2 * (M + 1 - i))) :=
    htSmallTo_sum _ _ fun i _ => by
      simpa using (htSmallTo_C_mul (hNc i) (htSmallTo_pow hA' i)).mul (htSmallTo_X_pow (K := K) (2 * (M + 1 - i)))
  have h1 := ((hvs.mul hvs).mul hH)
  rw [← pow_two, ← heq] at h1
  set G := ∑ i ∈ Finset.range (M + 1), C (Dp.coeff i) * A ^ i * X ^ (2 * (M - i)) with hG
  set B := A.subst v - C e * v ^ 2 with hBdef
  have h2 : HtSmallTo (M + 2 + (M + 2)) (G * X ^ 2) := by
    have := (htSmallTo_inv hB.1 hB0).mul h1
    have hBB : B⁻¹ * (B * G * X ^ 2) = G * X ^ 2 := by
      rw [mul_assoc, ← mul_assoc B⁻¹, PowerSeries.inv_mul_cancel _ (by rw [hB0]; exact one_ne_zero), one_mul]
    rw [hBB, zero_add, add_zero] at this
    exact this
  have h3 : ∀ n < 2 * M + 2, ‖coeff n G‖ < 1 := by
    intro n hn
    have := h2.2 (n + 2) (by omega)
    rwa [coeff_mul_X_pow] at this
  have hterm : ∀ k i, coeff (2 * k) (C (Dp.coeff i) * A ^ i * X ^ (2 * (M - i))) =
      Dp.coeff i * (if 2 * (M - i) ≤ 2 * k then coeff (2 * k - 2 * (M - i)) (A ^ i) else 0) := by
    intro k i
    rw [mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  have hsmall : ∀ k, k ≤ M → ‖Dp.coeff (M - k)‖ < 1 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro hk
    have hc := h3 (2 * k) (by omega)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hG, map_sum] at hc
    simp_rw [hterm k] at hc
    have hmem : M - k ∈ Finset.range (M + 1) := Finset.mem_range.2 (by omega)
    rw [← Finset.add_sum_erase _ _ hmem] at hc
    have hself : Dp.coeff (M - k) * (if 2 * (M - (M - k)) ≤ 2 * k then coeff (2 * k - 2 * (M - (M - k))) (A ^ (M - k)) else 0)
        = Dp.coeff (M - k) := by
      rw [if_pos (by omega), show 2 * k - 2 * (M - (M - k)) = 0 by omega, coeff_zero_eq_constantCoeff_apply,
        map_pow, hA0, one_pow, mul_one]
    rw [hself] at hc
    have hrest : ‖∑ i ∈ (Finset.range (M + 1)).erase (M - k),
        Dp.coeff i * (if 2 * (M - i) ≤ 2 * k then coeff (2 * k - 2 * (M - i)) (A ^ i) else 0)‖ < 1 := by
      apply htform_norm_sum_lt
      intro i hi
      rw [Finset.mem_erase, Finset.mem_range] at hi
      split_ifs with hle
      · have hlt : M - i < k := by omega
        have := ih (M - i) hlt (by omega)
        rw [show M - (M - i) = i by omega] at this
        rw [norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) this ((htSmallTo_pow hA' i).1 _)
      · simp
    have hd : Dp.coeff (M - k) = (Dp.coeff (M - k) + ∑ i ∈ (Finset.range (M + 1)).erase (M - k),
        Dp.coeff i * (if 2 * (M - i) ≤ 2 * k then coeff (2 * k - 2 * (M - i)) (A ^ i) else 0)) +
        -(∑ i ∈ (Finset.range (M + 1)).erase (M - k),
        Dp.coeff i * (if 2 * (M - i) ≤ 2 * k then coeff (2 * k - 2 * (M - i)) (A ^ i) else 0)) := by ring
    rw [hd]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hc (by rw [norm_neg]; exact hrest))
  have hev : ‖Dp.eval e'‖ < 1 := by
    rw [Polynomial.eval_eq_sum_range' (n := M + 1) (by omega)]
    apply htform_norm_sum_lt
    intro i hi
    rw [Finset.mem_range] at hi
    have := hsmall (M - i) (by omega)
    rw [show M - (M - i) = i by omega] at this
    rw [norm_mul, norm_pow]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) this (pow_le_one₀ (norm_nonneg _) he')
  rw [hDe] at hev
  exact lt_irrefl _ hev

end GlobalTheory.Honda
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicationSeriesUnitCoeffNormLeStatement
open PowerSeries GlobalTheory.Honda
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplication_series_unit_coeff_norm_le : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (A v : K⟦X⟧) (e e' : K) (M : ℕ) (Dp Np : Polynomial K), CoefLe 1 A → constantCoeff A = 1 → CoefLe 1 v → constantCoeff v = 0 → ‖e‖ ≤ 1 → ‖e'‖ ≤ 1 → Np.Monic → Np.natDegree = M + 1 → (∀ i, ‖Np.coeff i‖ ≤ 1) → Dp.natDegree ≤ M → ‖Dp.eval e'‖ = 1 → (A.subst v - C e * v ^ 2) * (∑ i ∈ Finset.range (M + 1), C (Dp.coeff i) * A ^ i * X ^ (2 * (M - i))) * X ^ 2 = v ^ 2 * ∑ i ∈ Finset.range (M + 2), C (Np.coeff i) * A ^ i * X ^ (2 * (M + 1 - i)) → ∃ n, n ≤ M + 1 ∧ ‖coeff n v‖ = 1 := by
  first | exact @GlobalTheory.Honda.htform_unit_coeff_le | exact GlobalTheory.Honda.htform_unit_coeff_le | (intros; apply GlobalTheory.Honda.htform_unit_coeff_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FormalGroupHeightLeTwoGoodReduction
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

noncomputable section

namespace GlobalTheory.HeightTwo

open Formalism.L2.Th1.F Formalism.L2.Th1.F.Taylor Formalism.L2.Th1.C Formalism.L2.Th1.C.USideB Formalism.L2.Th1.C.WeierstrassCurveSeries

def shiftFn (L : PeriodPair) (c z : ℂ) : ℂ := 1 + z * z * (L.weierstrassPExcept 0 z + -c)

theorem analyticAt_shiftFn (L : PeriodPair) (c : ℂ) : AnalyticAt ℂ (shiftFn L c) 0 := by
  have h := L.analyticAt_weierstrassPExcept 0
  unfold shiftFn
  fun_prop

theorem taylor0_shiftFn (L : PeriodPair) (c : ℂ) : taylor0 (shiftFn L c) = wpShift (pSeries L) c := by
  have h := L.analyticAt_weierstrassPExcept 0
  unfold shiftFn
  rw [taylor0_add (by fun_prop) (by fun_prop), taylor0_mul (by fun_prop) (by fun_prop),
    taylor0_mul (by fun_prop) (by fun_prop), taylor0_add h (by fun_prop), taylor0_const, taylor0_const, taylor0_id]
  unfold wpShift pSeries
  simp only [map_one, map_neg]
  ring

theorem shiftFn_eq (L : PeriodPair) (c z : ℂ) (hz : z ≠ 0) :
    shiftFn L c z = z ^ 2 * (L.weierstrassP z - c) := by
  have h := L.weierstrassPExcept_add 0 z
  simp only [ZeroMemClass.coe_zero, sub_zero] at h
  unfold shiftFn
  rw [← h]
  field_simp
  ring

theorem taylor0_prod_shiftFn (L : PeriodPair) (S : Finset ℂ) (a : ℂ → ℂ) :
    AnalyticAt ℂ (fun z => ∏ P ∈ S, shiftFn L (a P) z) 0 ∧
      taylor0 (fun z => ∏ P ∈ S, shiftFn L (a P) z) = ∏ P ∈ S, wpShift (pSeries L) (a P) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact ⟨analyticAt_const, by rw [taylor0_const, map_one]⟩
  | insert P S hP ih =>
    simp only [Finset.prod_insert hP]
    exact ⟨(analyticAt_shiftFn L _).mul ih.1,
      by rw [taylor0_mul (analyticAt_shiftFn L _) ih.1, ih.2, taylor0_shiftFn]⟩

theorem weierstrassP_nat_mul_product_series_identity (L : PeriodPair) (n e : ℂ) (hn : n ≠ 0) (S : Finset ℂ) (a b : ℂ → ℂ)
    (h : ∀ z, n * z ∉ L.lattice →
      n ^ 2 * (L.weierstrassP (n * z) - e) * ∏ P ∈ S, (L.weierstrassP z - a P) =
        (L.weierstrassP z - e) * ∏ P ∈ S, (L.weierstrassP z - b P)) :
    rescale n (wpShift (pSeries L) e) * ∏ P ∈ S, wpShift (pSeries L) (a P) =
      wpShift (pSeries L) e * ∏ P ∈ S, wpShift (pSeries L) (b P) := by
  have hc : Filter.Tendsto (fun z : ℂ => n * z) (nhds 0) (nhds 0) := by
    have : Continuous fun z : ℂ => n * z := by fun_prop
    simpa using this.tendsto 0
  have ha : AnalyticAt ℂ (fun z => shiftFn L e (n * z)) 0 :=
    AnalyticAt.comp_of_eq (g := shiftFn L e) (f := fun z : ℂ => n * z) (analyticAt_shiftFn L e) (by fun_prop) (by simp)
  rw [← (taylor0_prod_shiftFn L S a).2, ← (taylor0_prod_shiftFn L S b).2, ← taylor0_shiftFn,
    ← taylor0_rescale n (analyticAt_shiftFn L e), ← taylor0_mul ha (taylor0_prod_shiftFn L S a).1,
    ← taylor0_mul (analyticAt_shiftFn L e) (taylor0_prod_shiftFn L S b).1]
  apply taylor0_congr
  filter_upwards [hc.eventually (L.compl_lattice_sdiff_singleton_mem_nhds 0)] with z hz
  by_cases h0 : z = 0
  · simp [h0, shiftFn]
  have hnz : n * z ≠ 0 := mul_ne_zero hn h0
  have h1 : n * z ∉ L.lattice := fun hm => hz ⟨hm, hnz⟩
  simp only [shiftFn_eq L _ _ h0, shiftFn_eq L _ _ hnz, Finset.prod_mul_distrib]
  linear_combination (z ^ 2 * ∏ P ∈ S, z ^ 2) * h z h1

section Formal

variable {K : Type} [Field K]

theorem map_wpShift {K' : Type} [Field K'] (φ : K →+* K') (p : K⟦X⟧) (c : K) :
    PowerSeries.map φ (wpShift p c) = wpShift (PowerSeries.map φ p) (φ c) := by
  simp [wpShift]

theorem map_rescale' {K' : Type} [Field K'] (φ : K →+* K') (p : K⟦X⟧) (c : K) :
    PowerSeries.map φ (rescale c p) = rescale (φ c) (PowerSeries.map φ p) := by
  ext n
  simp [coeff_rescale]

theorem series_u {σ : Type} {p l linv A : K⟦X⟧} (hL : IsLogPair l linv) (hX : XIsWp p l A 0) (n e : K)
    (S : Finset σ) (a b : σ → K)
    (h : rescale n (wpShift p e) * ∏ P ∈ S, wpShift p (a P) = wpShift p e * ∏ P ∈ S, wpShift p (b P)) :
    (A.subst (mulBy l linv n) - C e * mulBy l linv n ^ 2) * (C (n ^ 2) * ∏ P ∈ S, (A - C (a P) * X ^ 2)) * X ^ 2 =
      mulBy l linv n ^ 2 * ((A - C e * X ^ 2) * ∏ P ∈ S, (A - C (b P) * X ^ 2)) := by
  set v := mulBy l linv n with hv
  have hsl := hs_of hL.1
  have hsv : HasSubst v := hs_of (cc_mulBy hL n)
  have h1 : ∀ x : K, X ^ 2 * subst l (wpShift p x) = (A - C x * X ^ 2) * l ^ 2 := fun x => by
    simpa using subst_wpShift hL.1 hX x
  have h2 := congrArg (substAlgHom hsl) h
  simp only [map_mul, map_prod, coe_substAlgHom] at h2
  rw [subst_rescale hL, ← hv] at h2
  have h3 : v ^ 2 * subst v (subst l (wpShift p e)) = (A.subst v - C e * v ^ 2) * (C n * l) ^ 2 := by
    have := congrArg (subst v) (h1 e)
    have hC : subst v (C e : K⟦X⟧) = (C e : K⟦X⟧) := subst_C _
    rwa [subst_mul hsv, subst_mul hsv, subst_sub hsv, subst_mul hsv, subst_pow hsv, subst_pow hsv, subst_X hsv,
      hC, hv, subst_mulBy_l hL, ← hv] at this
  have h4 : ∀ c : σ → K, (∏ _P ∈ S, (X : K⟦X⟧) ^ 2) * ∏ P ∈ S, subst l (wpShift p (c P)) =
      (∏ P ∈ S, (A - C (c P) * X ^ 2)) * ∏ _P ∈ S, l ^ 2 := fun c => by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun P _ => h1 _
  have hl0 : l ^ 2 * ∏ _P ∈ S, l ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (l_ne_zero hL)) (Finset.prod_ne_zero_iff.2 fun _ _ => pow_ne_zero _ (l_ne_zero hL))
  apply mul_right_cancel₀ hl0
  have ha := h4 a
  have hb := h4 b
  have he := h1 e
  rw [map_pow]
  set T := ∏ _P ∈ S, (X : K⟦X⟧) ^ 2
  set Sa := ∏ P ∈ S, subst l (wpShift p (a P))
  set Sb := ∏ P ∈ S, subst l (wpShift p (b P))
  linear_combination (v ^ 2 * X ^ 2 * T) * h2 - X ^ 2 * T * Sa * h3
    - X ^ 2 * ((A.subst v - C e * v ^ 2) * (C n * l) ^ 2) * ha + v ^ 2 * T * Sb * he
    + v ^ 2 * ((A - C e * X ^ 2) * l ^ 2) * hb

theorem homog_field {F : Type} [Field F] (φ : K →+* F) (q : Polynomial K) (m : ℕ) (hq : q.natDegree ≤ m) (a y : F)
    (hy : y ≠ 0) :
    ∑ i ∈ Finset.range (m + 1), φ (q.coeff i) * a ^ i * y ^ (m - i) = y ^ m * q.eval₂ φ (a / y) := by
  rw [Polynomial.eval₂_eq_sum_range' φ (Nat.lt_succ_of_le hq), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [pow_sub₀ _ hy hi', div_pow]
  field_simp

theorem homog_prod {σ : Type} (S : Finset σ) (d : K) (c : σ → K) (A : K⟦X⟧) (m : ℕ) (hm : S.card = m) :
    ∑ i ∈ Finset.range (m + 1),
        C ((Polynomial.C d * ∏ P ∈ S, (Polynomial.X - Polynomial.C (c P))).coeff i) * A ^ i * X ^ (2 * (m - i)) =
      C d * ∏ P ∈ S, (A - C (c P) * X ^ 2) := by
  let ψ := algebraMap K⟦X⟧ (FractionRing K⟦X⟧)
  have hψ : Function.Injective ψ := IsFractionRing.injective _ _
  have hy : ψ (X ^ 2) ≠ 0 := (map_ne_zero_iff ψ hψ).2 (pow_ne_zero _ X_ne_zero)
  have hd : (Polynomial.C d * ∏ P ∈ S, (Polynomial.X - Polynomial.C (c P))).natDegree ≤ m := by
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card, hm]
  have := homog_field (ψ.comp C) _ m hd (ψ A) _ hy
  apply hψ
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_pow, map_prod, map_sub, pow_mul]
  simp only [RingHom.comp_apply, map_pow] at this
  rw [this, Polynomial.eval₂_mul, Polynomial.eval₂_finsetProd, Polynomial.eval₂_C, ← hm, ← Finset.prod_const,
    mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun P _ => ?_
  rw [map_pow] at hy
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, RingHom.comp_apply]
  rw [mul_sub, mul_div_cancel₀ _ hy, mul_comm]

end Formal

theorem coeff_prod_le {K : Type} [NormedField K] [IsUltrametricDist K] {σ : Type} (S : Finset σ) (c : σ → K)
    (hc : ∀ P ∈ S, ‖c P‖ ≤ 1) (i : ℕ) : ‖(∏ P ∈ S, (Polynomial.X - Polynomial.C (c P))).coeff i‖ ≤ 1 := by
  classical
  change _ ∈ Formalism.G.unitBall K
  induction S using Finset.induction_on generalizing i with
  | empty =>
    rw [Finset.prod_empty, Polynomial.coeff_one]
    split_ifs
    exacts [one_mem _, zero_mem _]
  | insert P S hP ih =>
    rw [Finset.prod_insert hP, Polynomial.coeff_mul]
    refine Subring.sum_mem _ fun x _ => mul_mem ?_ (ih (fun Q hQ => hc Q (Finset.mem_insert_of_mem hQ)) _)
    have h : c P ∈ Formalism.G.unitBall K := hc P (Finset.mem_insert_self _ _)
    rw [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
    refine sub_mem ?_ ?_ <;> split_ifs
    exacts [one_mem _, zero_mem _, h, zero_mem _]

theorem norm_two (l : ℕ) [Fact l.Prime] (hl : 5 ≤ l) : ‖(2 : ℂ_[l])‖ = 1 := by
  have h1 : ‖((2 : ℕ) : ℚ_[l])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff, Nat.coprime_primes Fact.out Nat.prime_two]
    omega
  have h2 : (2 : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] ((2 : ℕ) : ℚ_[l]) := by simp [map_ofNat]
  rw [h2, norm_algebraMap', h1]

theorem mulBy_eq_zSer {K : Type} [Field K] [CharZero K] (W : WeierstrassCurve K) (n : ℕ) :
    mulBy (Formalism.L2.Th1.A.logSer W) (Formalism.L2.Th1.A.expSer W) (n : K) = Formalism.L2.Th1.A.zSer W (n : ℤ) := by
  have hL := logPair W
  have h0 := ((Formalism.L2.Th1.A.zSerSpec K W).1 (n : ℤ)).1
  have h1 := Formalism.L2.Th1.A.zSerLog K W (n : ℤ)
  rw [Int.cast_natCast] at h1
  unfold mulBy
  rw [← h1, ← subst_comp_subst_apply (hs_of hL.1) (hs_of h0), hL.2.2.2.1, subst_X (hs_of h0)]

theorem odd_mul_sub_mem (L : PeriodPair) {k : ℕ} (hk : Odd k) {s P : ℂ} (hs : 2 * s ∈ L.lattice)
    (hP : (k : ℂ) * P ∈ L.lattice) : (k : ℂ) * (s + P) - s ∈ L.lattice := by
  obtain ⟨j, rfl⟩ := hk
  have : ((2 * j + 1 : ℕ) : ℂ) * (s + P) - s = (j : ℤ) • (2 * s) + ((2 * j + 1 : ℕ) : ℂ) * P := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [this]
  exact add_mem (Submodule.smul_mem _ _ hs) hP

theorem wp_congr (L : PeriodPair) {z w : ℂ} (h : z - w ∈ L.lattice) : L.weierstrassP z = L.weierstrassP w := by
  have := L.weierstrassP_add_coe w ⟨z - w, h⟩
  simpa using this

theorem nat_mul_mem (L : PeriodPair) (k : ℕ) {z : ℂ} (h : z ∈ L.lattice) : (k : ℂ) * z ∈ L.lattice := by
  simpa [zsmul_eq_mul] using L.lattice.smul_mem (k : ℤ) h

theorem height_le_two (L : PeriodPair) (l : ℕ) [Fact l.Prime] (hl : 5 ≤ l) (ι : ℂ ≃+* ℂ_[l])
    (h2 : ‖ι L.g₂‖ ≤ 1) (h3 : ‖ι L.g₃‖ ≤ 1) (hΔ : ‖ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2‖ = 1) :
    ∃ n, n ≤ l ^ 2 ∧ ‖coeff n (Formalism.L2.Th1.C.mulBy (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃)))
      (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (l : ℂ_[l]))‖ = 1 := by
  classical
  set W := Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃) with hW
  have hodd : Odd l := (Fact.out : l.Prime).odd_of_ne_two (by omega)
  have hl0 : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h4 : ‖(4 : ℂ_[l])‖ = 1 := by
    rw [show (4 : ℂ_[l]) = 2 * 2 by norm_num, norm_mul, norm_two l hl, mul_one]
  have ha4 : ‖W.a₄‖ ≤ 1 := by
    change ‖-ι L.g₂ / 4‖ ≤ 1
    rwa [norm_div, norm_neg, h4, div_one]
  have ha6 : ‖W.a₆‖ ≤ 1 := by
    change ‖-ι L.g₃ / 4‖ ≤ 1
    rwa [norm_div, norm_neg, h4, div_one]
  have hz : ‖(0 : ℂ_[l])‖ ≤ 1 := by simp
  obtain ⟨hb2, -, -, hD⟩ := Formalism.L2.Th1.A.shortInv ℂ_[l] (ι L.g₂) (ι L.g₃)
  have hInt : Formalism.L2.Th1.E.IntCurve (Formalism.L2.Th1.E.curveL l L ι) :=
    ⟨hz, hz, hz, ha4, ha6, by rw [← hΔ, ← hD]; rfl⟩
  obtain ⟨-, hx, -, -, -, -, -, hzs, -⟩ := Formalism.L2.Th1.A.coeffMem.{0} ℂ_[l] W (Formalism.G.unitBall ℂ_[l]) hz hz hz ha4 ha6

  have key : ∀ s P : ℂ, s ∉ L.lattice → 2 * s ∈ L.lattice → (l : ℂ) * P ∈ L.lattice →
      s + P ∉ L.lattice ∧ ‖ι (L.weierstrassP (s + P))‖ ≤ 1 := by
    intro s P hs h2s hP
    have hm := odd_mul_sub_mem L hodd h2s hP
    have hn : (l : ℂ) * (s + P) ∉ L.lattice := fun h => hs (by simpa using sub_mem h hm)
    refine ⟨fun h => hn (nat_mul_mem L l h), GlobalTheory.T.weierstrassP_integral_of_mul_integral_good_reduction L l hl ι h2 h3 hΔ _ l hn ?_⟩
    rw [wp_congr L hm, ← Formalism.L2.Th1.E.AnaSys.px_ptOf l L ι s hs]
    exact (Formalism.L2.Th1.E.ptOfInt l L ι hInt s 2 two_pos (fun h => by have := Nat.le_of_dvd two_pos h; omega)
      (by simpa using h2s) hs).1
  set t := L.ω₁ / 2 with ht
  set t' := L.ω₂ / 2 with ht'
  have ht0 : t ∉ L.lattice := L.ω₁_div_two_notMem_lattice
  have ht0' : t' ∉ L.lattice := L.ω₂_div_two_notMem_lattice
  have ht2 : 2 * t ∈ L.lattice := by rw [ht, mul_div_cancel₀ _ two_ne_zero]; exact L.ω₁_mem_lattice
  have ht2' : 2 * t' ∈ L.lattice := by rw [ht', mul_div_cancel₀ _ two_ne_zero]; exact L.ω₂_mem_lattice
  have hp0 : t' + t ∉ L.lattice := fun h => by
    have := (PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice (L := L) (α := 1 / 2) (β := 1 / 2)).1
      (by convert h using 1; rw [ht, ht']; push_cast; ring)
    norm_num at this
  have hm0 : t' - t ∉ L.lattice := fun h => hp0 (by convert add_mem h ht2 using 1; ring)
  have hp2 : 2 * (t' + t) ∈ L.lattice := by rw [mul_add]; exact add_mem ht2' ht2
  have hm2 : 2 * (t' - t) ∈ L.lattice := by rw [mul_sub]; exact sub_mem ht2' ht2
  have hk0 : (l : ℂ) * 0 ∈ L.lattice := by simp
  have unit : ∀ P : ℂ, (l : ℂ) * P ∈ L.lattice → ‖ι (L.weierstrassP t') - ι (L.weierstrassP (t + P))‖ = 1 := by
    intro P hP
    have k1 := key t' 0 ht0' ht2' hk0
    have k2 := key t P ht0 ht2 hP
    have k3 := key _ P hp0 hp2 hP
    have k4 := key _ (-P) hm0 hm2 (by simpa using hP)
    rw [add_zero] at k1
    rw [add_assoc] at k3
    rw [show t' - t + -P = t' - (t + P) by ring] at k4
    exact GlobalTheory.Honda.norm_weierstrassP_sub_eq_one_of_good L l hl ι h2 h3 hΔ _ _ k1.1 k2.1 k3.1 k4.1 k1.2 k2.2 k3.2 k4.2
  have hst : MulStable L l := fun ω h => nat_mul_mem L l h
  obtain ⟨S, hS⟩ := kerRepsExist L l hl0 hst
  have hcard : S.card + 1 = l ^ 2 := by
    have := kerRepsCard L l S hl0 hst hS
    rw [Complex.normSq_natCast, ← sq] at this
    exact_mod_cast this
  have h0S : (0 : ℂ) ∉ S := fun h => (hS.1 0 h).2 (zero_mem _)
  have hprod := GlobalTheory.T.weierstrassP_odd_mul_sub_twoTorsion_product L l S t hodd hS ht0 ht2
  have hins : ∀ P ∈ insert (0 : ℂ) S, (l : ℂ) * P ∈ L.lattice := by
    intro P hP
    rcases Finset.mem_insert.1 hP with rfl | hP
    exacts [hk0, (hS.1 P hP).1]

  have hzser := congrArg (PowerSeries.map (ι : ℂ →+* ℂ_[l])) (weierstrassP_nat_mul_product_series_identity L l _ hl0 S _ _ hprod)
  have hbr : Formalism.L2.Th1.A.wpReg W = PowerSeries.map (ι : ℂ →+* ℂ_[l]) (pSeries L) := Formalism.L2.Th1.E.wpBridge l L ι
  simp only [map_mul, map_prod, map_rescale', map_wpShift, ← hbr, map_natCast] at hzser
  have hX : XIsWp (Formalism.L2.Th1.A.wpReg W) (Formalism.L2.Th1.A.logSer W) (Formalism.L2.Th1.A.xS W) 0 := by
    have := xIsWp W
    rwa [hb2, zero_div] at this
  have hu := series_u (logPair W) hX _ _ S _ _ hzser
  rw [← hcard]
  refine GlobalTheory.T.multiplication_series_unit_coeff_norm_le ℂ_[l] (Formalism.L2.Th1.A.xS W) _ (ι (L.weierstrassP t)) (ι (L.weierstrassP t')) S.card
    (Polynomial.C ((l : ℂ_[l]) ^ 2) * ∏ P ∈ S, (Polynomial.X - Polynomial.C (ι (L.weierstrassP P))))
    (Polynomial.C 1 * ∏ P ∈ insert 0 S, (Polynomial.X - Polynomial.C (ι (L.weierstrassP (t + P)))))
    hx (Formalism.L2.Th1.A.wSerFactor ℂ_[l] W).2.2.2.1 ?_ (cc_mulBy (logPair W) _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [mulBy_eq_zSer]; exact hzs l
  · simpa using (key t 0 ht0 ht2 hk0).2
  · simpa using (key t' 0 ht0' ht2' hk0).2
  · rw [map_one, one_mul]; exact Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _
  · rw [map_one, one_mul, Polynomial.natDegree_finsetProd_X_sub_C_eq_card, Finset.card_insert_of_notMem h0S]
  · rw [map_one, one_mul]
    exact coeff_prod_le _ _ fun P hP => (key t P ht0 ht2 (hins P hP)).2
  · refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
  · have hm := odd_mul_sub_mem L hodd ht2' hk0
    rw [add_zero] at hm
    have h := congrArg ι (hprod t' fun h => ht0' (by simpa using sub_mem h hm))
    rw [wp_congr L hm] at h
    simp only [map_mul, map_sub, map_prod, map_pow, map_natCast] at h
    have hu0 := unit 0 hk0
    rw [add_zero] at hu0
    have hne : ι (L.weierstrassP t') - ι (L.weierstrassP t) ≠ 0 := fun h => by simp [h] at hu0
    rw [mul_right_comm, mul_comm] at h
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X]
    rw [mul_left_cancel₀ hne h, norm_prod]
    exact Finset.prod_eq_one fun P hP => unit P (hS.1 P hP).1
  · rw [homog_prod S _ _ _ _ rfl, homog_prod (insert 0 S) _ _ _ (S.card + 1) (Finset.card_insert_of_notMem h0S),
      Finset.prod_insert h0S, add_zero, map_one, one_mul]
    exact hu

end GlobalTheory.HeightTwo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FormalGroupHeightLeTwoGoodReductionStatement
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroup_height_le_two_good_reduction : ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]), ‖ι L.g₂‖ ≤ 1 → ‖ι L.g₃‖ ≤ 1 → ‖ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2‖ = 1 → ∃ n, n ≤ l ^ 2 ∧ ‖coeff n (Formalism.L2.Th1.C.mulBy (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (l : ℂ_[l]))‖ = 1 := by
  first | exact @GlobalTheory.HeightTwo.height_le_two | exact GlobalTheory.HeightTwo.height_le_two | (intros; apply GlobalTheory.HeightTwo.height_le_two <;> assumption)
end
