module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingEquivTranscendental
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeightTwoFormalGroupUnramifiedMultiplier
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FormalGroupHeightLeTwoGoodReduction
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ExistsMemIdealInvariants
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CmCurveGoodOutsidePrimePremises
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundSingleLiftOfDefinitions
public import ReciprocityTheory.ClassFieldTheory.GlobalClassField.IsFrobAtMulOfMemInertiaGroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneSubTwoOmegaSq
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHomotheticPeriodPairLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHomotheticPeriodPairLattice
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory

theorem homotheticLattice : ∀ (L : PeriodPair) (c : ℂ), c ≠ 0 → ∃ L' : PeriodPair,
    (∀ z, z ∈ L'.lattice ↔ c * z ∈ L.lattice) ∧ L'.g₂ = c ^ 4 * L.g₂ ∧ L'.g₃ = c ^ 6 * L.g₃ ∧
    (∀ z, L'.weierstrassP z = c ^ 2 * L.weierstrassP (c * z) ∧
      L'.derivWeierstrassP z = c ^ 3 * L.derivWeierstrassP (c * z)) ∧
    ∀ d, HasCMBy d L → HasCMBy d L' := by
  intro L c hc
  have hc' : c⁻¹ ≠ 0 := inv_ne_zero hc
  obtain ⟨hmem, -, -, hwp, -, -, -, -, -, hg2, hg3⟩ := Formalism.L2.Th1.F.homogeneity L c⁻¹ hc'
  refine ⟨Formalism.L2.Th1.F.scalePair L c⁻¹ hc', ?_, ?_, ?_, ?_, ?_⟩
  · intro z; rw [hmem, inv_inv]
  · rw [hg2, inv_pow, inv_inv]
  · rw [hg3, inv_pow, inv_inv]
  · intro z
    constructor
    · have := hwp (c * z)
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul, inv_pow, inv_inv] at this
      exact this
    · unfold PeriodPair.derivWeierstrassP
      rw [Formalism.L2.Th1.F.Homog.tsum_scale L c⁻¹ hc' (fun l => 2 / (z - l) ^ 3), mul_neg,
        ← tsum_mul_left]
      congr 1
      refine tsum_congr fun l => ?_
      have : z - c⁻¹ * (l : ℂ) = c⁻¹ * (c * z - l) := by field_simp
      rw [this, mul_pow, inv_pow, div_eq_mul_inv, div_eq_mul_inv, mul_inv, inv_inv]
      ring
  · intro d hd
    exact Formalism.L2.Th1.F.hasCMByScale d L c⁻¹ hc' hd

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHomotheticPeriodPairLatticeStatement
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homothetic_periodPair_lattice : ∀ (L : PeriodPair) (c : ℂ), c ≠ 0 → ∃ L' : PeriodPair, (∀ z, z ∈ L'.lattice ↔ c * z ∈ L.lattice) ∧ L'.g₂ = c ^ 4 * L.g₂ ∧ L'.g₃ = c ^ 6 * L.g₃ ∧ (∀ z, L'.weierstrassP z = c ^ 2 * L.weierstrassP (c * z) ∧ L'.derivWeierstrassP z = c ^ 3 * L.derivWeierstrassP (c * z)) ∧ ∀ d, HasCMBy d L → HasCMBy d L' := by
  first | exact @GlobalTheory.homotheticLattice | exact GlobalTheory.homotheticLattice | (intros; apply GlobalTheory.homotheticLattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmMultiplierIntegralSeriesAtInertPrimeProof
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FormalGroupMulByIntegralOfKernelPrimeToL
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FormalGroupMulByIntegralOfKernelPrimeToL
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory.Honda


open Formalism.L2.Th1 in
theorem mulBy_coefLe_of_kernel_prime_to :
    ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]), ‖ι L.g₂‖ ≤ 1 → ‖ι L.g₃‖ ≤ 1 → ‖ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2‖ = 1 → ∀ (β : ℂ) (N : ℕ), Formalism.L2.Th1.F.MulStable L β → ‖ι β‖ = 1 → 0 < N → ¬ l ∣ N → (∀ z, β * z ∈ L.lattice → (N : ℂ) * z ∈ L.lattice) → CoefLe 1 (Formalism.L2.Th1.C.mulBy (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (ι β)) := by
  intro L l _ hl ι h2 h3 hD β N hst hβ hN hlN hker
  have hβp : ι β ≠ 0 := by
    intro h
    rw [h, norm_zero] at hβ
    exact zero_ne_one hβ
  have hβ0 : β ≠ 0 := by
    intro h
    rw [h, map_zero] at hβp
    exact hβp rfl
  have hW : E.IntCurve (E.curveL l L ι) := E.ScaledModelNorms.intCurve_short l hl _ _ h2 h3 hD
  have hΔ : (E.curveL l L ι).Δ ≠ 0 := by
    intro h
    have := hW.2.2.2.2.2
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have htwo := E.ScaledModelNorms.norm_two l hl
  have hC : C.CoeffIn (Formalism.G.unitBall ℂ_[l]) (E.curveL l L ι) :=
    ⟨hW.1, hW.2.1, hW.2.2.1, hW.2.2.2.1, hW.2.2.2.2.1⟩
  obtain ⟨S, hS⟩ := F.kerRepsExist L β hβ0 hst
  obtain ⟨neg, -, hE⟩ := F.endoZInstance L β S hβ0 hst hS
  have hb2 : (E.curveL l L ι).b₂ = 0 := (A.shortInv ℂ_[l] _ _).1
  have hEp := D.CurveNormEndomorphisms.isEndoZ_map (ι : ℂ →+* ℂ_[l]) hE
  rw [← E.wpBridge l L ι] at hEp
  have hEp' : C.IsEndoZ (A.wpReg (E.curveL l L ι)) neg
      (fun P : S => ι (L.weierstrassP (P : ℂ)) + (E.curveL l L ι).b₂ / 12)
      (fun P : S => PowerSeries.map (ι : ℂ →+* ℂ_[l])
        (F.taylor0 (fun z => L.weierstrassP (z + (P : ℂ))))) (ι β) := by
    rw [hb2]
    simpa using hEp
  have hint : ∀ P : S, ‖ι (L.weierstrassP (P : ℂ))‖ ≤ 1 ∧ ‖ι (L.derivWeierstrassP (P : ℂ))‖ ≤ 1 := by
    intro P
    have := E.cm4Int L l hl ι 1 one_ne_zero (by simpa using h2) (by simpa using h3) (by simpa using hD)
      (P : ℂ) N hN hlN (hker _ (hS.1 P P.2).1) (hS.1 P P.2).2
    simpa using this
  obtain ⟨hLP, hXW, hA, -, -⟩ := C.curveFrame ℂ_[l] (Formalism.G.unitBall ℂ_[l]) (E.curveL l L ι) hC
  have hinv : ∀ x : ℂ_[l], ‖x‖ = 1 → x⁻¹ ∈ Formalism.G.unitBall ℂ_[l] := by
    intro x hx
    show ‖x⁻¹‖ ≤ 1
    rw [norm_inv, hx, inv_one]
  have hM := A.coeffMem.{0} ℂ_[l] (E.curveL l L ι) (Formalism.G.unitBall ℂ_[l]) hC.1 hC.2.1 hC.2.2.1 hC.2.2.2.1
    hC.2.2.2.2
  have key := C.endIntFromDatum ℂ_[l] (Formalism.G.unitBall ℂ_[l]) (A.wpReg (E.curveL l L ι))
    (A.logSer (E.curveL l L ι)) (A.expSer (E.curveL l L ι)) (A.xS (E.curveL l L ι))
    ((E.curveL l L ι).b₂ / 12) S neg (fun P : S => ι (L.weierstrassP (P : ℂ)))
    (fun P : S => PowerSeries.map (ι : ℂ →+* ℂ_[l])
        (F.taylor0 (fun z => L.weierstrassP (z + (P : ℂ)))))
    (fun P : S => E.xT (E.curveL l L ι) (E.ptOf l L ι (P : ℂ))) (ι β)
    ((ι β)⁻¹ * ((Fintype.card S : ℂ_[l]) + 1)) hLP hXW hA (hinv _ htwo)
    ⟨hEp', by rw [← mul_assoc, mul_inv_cancel₀ hβp, one_mul], ?_, ?_, fun P => (hint P).1, hβ.le,
      hinv _ hβ, by rw [hb2, zero_div, mul_zero]; exact zero_mem _⟩
  · exact fun n => key n
  · intro P
    rw [hb2, zero_div, map_zero, add_zero]
    exact E.transWpBridge l L ι (P : ℂ) (hS.1 P P.2).2
  · intro P n
    unfold E.xT
    beta_reduce
    rw [E.ScaledModelNorms.px_ptOf l L ι hΔ _ (hS.1 P P.2).2, E.ScaledModelNorms.py_ptOf l L ι hΔ _ (hS.1 P P.2).2]
    refine (hM.2.2.2.2.2.2.2.2.2.2 _ (hint P).1 _ ?_ n).1
    show ‖ι (L.derivWeierstrassP (P : ℂ)) / 2‖ ≤ 1
    rw [norm_div, htwo, div_one]
    exact (hint P).2

end GlobalTheory.Honda
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FormalGroupMulByIntegralOfKernelPrimeToLStatement
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroup_mulBy_integral_of_kernel_prime_to_l : ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]), ‖ι L.g₂‖ ≤ 1 → ‖ι L.g₃‖ ≤ 1 → ‖ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2‖ = 1 → ∀ (β : ℂ) (N : ℕ), Formalism.L2.Th1.F.MulStable L β → ‖ι β‖ = 1 → 0 < N → ¬ l ∣ N → (∀ z, β * z ∈ L.lattice → (N : ℂ) * z ∈ L.lattice) → CoefLe 1 (Formalism.L2.Th1.C.mulBy (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (ι β)) := by
  first | exact @GlobalTheory.Honda.mulBy_coefLe_of_kernel_prime_to | exact GlobalTheory.Honda.mulBy_coefLe_of_kernel_prime_to | (intros; apply GlobalTheory.Honda.mulBy_coefLe_of_kernel_prime_to <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmegaKSqSubSelfAddEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmegaKSqSubSelfAddEqZero
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory

theorem omegaK_quadratic : ∀ d : ℕ, d % 4 = 3 → omegaK d ^ 2 - omegaK d + (((d + 1) / 4 : ℕ) : ℂ) = 0 := by
  intro d hd
  have h4 : 4 ∣ d + 1 := by omega
  obtain ⟨k, hk⟩ := h4
  have hk' : (d + 1) / 4 = k := by omega
  rw [hk']
  have hdk : (d : ℂ) = 4 * k - 1 := by
    have : ((d + 1 : ℕ) : ℂ) = ((4 * k : ℕ) : ℂ) := by rw [hk]
    push_cast at this
    linear_combination this
  have hs : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  unfold omegaK
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (-(1:ℂ)/4) * hs + ((Real.sqrt d : ℝ) : ℂ) ^ 2 / 4 * hI - (1/4 : ℂ) * hdk
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmegaKSqSubSelfAddEqZeroStatement
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.omegaK_sq_sub_self_add_eq_zero : ∀ d : ℕ, d % 4 = 3 → omegaK d ^ 2 - omegaK d + (((d + 1) / 4 : ℕ) : ℂ) = 0 := by
  first | exact @GlobalTheory.omegaK_quadratic | exact GlobalTheory.omegaK_quadratic | (intros; apply GlobalTheory.omegaK_quadratic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmMultiplierIntegralSeriesAtInertPrimeProof
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory.Honda

theorem norm_eq_one_of_quad_root {l : ℕ} [Fact l.Prime] (x : ℂ_[l]) (N : ℕ) (hN : ¬ l ∣ N)
    (hx : x ^ 2 - x + (N : ℂ_[l]) = 0) : ‖x‖ = 1 := by
  have hNn : ‖(N : ℂ_[l])‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] ℂ_[l]), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hN
  have hle : ∀ y : ℂ_[l], y ^ 2 - y + (N : ℂ_[l]) = 0 → ‖y‖ ≤ 1 := by
    intro y hy
    by_contra h
    push_neg at h
    have h1 : y ^ 2 = y - N := by linear_combination hy
    have h2 : ‖y - (N : ℂ_[l])‖ ≤ max ‖y‖ ‖(N : ℂ_[l])‖ := by
      rw [sub_eq_add_neg, ← norm_neg (N : ℂ_[l])]
      exact IsUltrametricDist.norm_add_le_max _ _
    rw [hNn, max_eq_left h.le] at h2
    have h3 : ‖y‖ ^ 2 ≤ ‖y‖ := by rw [← norm_pow, h1]; exact h2
    nlinarith
  have h1 := hle x hx
  have h2 := hle (1 - x) (by linear_combination hx)
  have hprod : x * (1 - x) = N := by linear_combination -hx
  have h4 : ‖x‖ * ‖1 - x‖ = 1 := by rw [← norm_mul, hprod, hNn]
  refine le_antisymm h1 ?_
  calc (1 : ℝ) = ‖x‖ * ‖1 - x‖ := h4.symm
    _ ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg x)
    _ = ‖x‖ := mul_one _

theorem endOmega_holds : EndOmega := by
  intro d L hd hL l _ hl5 hld hsq ι g2 g3 hG n
  obtain ⟨-, -, h2, h3, hΔ, lam, hlam, rfl, rfl⟩ := hG
  have hc0 : ι.symm lam ≠ 0 := by simpa using hlam
  obtain ⟨L', -, hg2, hg3, -, hCM⟩ := GlobalTheory.T.exists_homothetic_periodPair_lattice L (ι.symm lam) hc0
  have hιc : ι (ι.symm lam) = lam := ι.apply_symm_apply lam
  have e2 : ι L'.g₂ = lam ^ 4 * ι L.g₂ := by rw [hg2, map_mul, map_pow, hιc]
  have e3 : ι L'.g₃ = lam ^ 6 * ι L.g₃ := by rw [hg3, map_mul, map_pow, hιc]
  have hL' : HasCMBy d L' := hCM d hL
  have hq := GlobalTheory.T.omegaK_sq_sub_self_add_eq_zero d hd
  set N := (d + 1) / 4 with hNdef
  have hN0 : 0 < N := by omega
  have hlN : ¬ l ∣ N := by
    intro h
    apply hsq
    refine ⟨1, ?_⟩
    have h4 : 4 * N = d + 1 := by omega
    have h5 : ((4 * N : ℕ) : ZMod l) = 0 := by
      rw [Nat.cast_mul, (ZMod.natCast_eq_zero_iff N l).mpr h, mul_zero]
    rw [h4] at h5
    push_cast at h5
    linear_combination h5
  have hιβ : ‖ι (omegaK d)‖ = 1 := by
    apply norm_eq_one_of_quad_root _ N hlN
    have := congrArg ι hq
    simpa using this
  have hNz : ∀ z, omegaK d * z ∈ L'.lattice → (N : ℂ) * z ∈ L'.lattice := by
    intro z hz
    have hz2 : omegaK d * (omegaK d * z) ∈ L'.lattice := hL' _ hz
    have e : (N : ℂ) * z = omegaK d * z - omegaK d * (omegaK d * z) := by linear_combination z * hq
    rw [e]
    exact sub_mem hz hz2
  have key := GlobalTheory.T.formalGroup_mulBy_integral_of_kernel_prime_to_l L' l hl5 ι (by rw [e2]; exact h2) (by rw [e3]; exact h3)
    (by rw [e2, e3]; exact hΔ) (omegaK d) N hL' hιβ hN0 hlN hNz
  rw [e2, e3] at key
  rw [Formalism.L2.Th1.A.uSerEq ℂ_[l]]
  exact key n

end GlobalTheory.Honda
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmMultiplierIntegralSeriesAtInertPrimeProofStatement
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmMultiplierIntegralSeriesAtInertPrime_proof : EndOmega := by
  first | exact @GlobalTheory.Honda.endOmega_holds | exact GlobalTheory.Honda.endOmega_holds | (intros; apply GlobalTheory.Honda.endOmega_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MaxUnramifiedResidueAlgClosedAndFrobeniusLift
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnramifiedNearIntegralComplexPadic
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnramifiedNearIntegralComplexPadic
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

noncomputable section

namespace GlobalTheory.ResidueUnr

open Polynomial

variable {l : ℕ} [Fact l.Prime]

theorem norm_algebraMap_padicInt (z : ℤ_[l]) : ‖algebraMap ℤ_[l] (PadicAlgCl l) z‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), PadicAlgCl.norm_extends]
  exact z.norm_le_one

theorem norm_aeval_le (x : PadicAlgCl l) (hx : ‖x‖ ≤ 1) (g : ℤ_[l][X]) : ‖aeval x g‖ ≤ 1 := by
  rw [aeval_eq_sum_range]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
  intro i _
  rw [Algebra.smul_def, norm_mul, norm_pow]
  exact mul_le_one₀ (norm_algebraMap_padicInt _) (pow_nonneg (norm_nonneg _) _) (pow_le_one₀ (norm_nonneg _) hx)

theorem norm_aeval_lt (x : PadicAlgCl l) (hx : ‖x‖ ≤ 1) (g : ℤ_[l][X])
    (hg : g.map (PadicInt.toZMod (p := l)) = 0) : ‖aeval x g‖ < 1 := by
  have hd : ∀ n, (Polynomial.C (l : ℤ_[l])) ∣ Polynomial.C (g.coeff n) := by
    intro n
    have h0 : PadicInt.toZMod (g.coeff n) = 0 := by
      have := congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f n) hg
      simpa [Polynomial.coeff_map] using this
    have hm : g.coeff n ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
      rw [← PadicInt.ker_toZMod]; exact h0
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hm
    exact map_dvd Polynomial.C hm
  obtain ⟨h, rfl⟩ : (Polynomial.C (l : ℤ_[l])) ∣ g := (Polynomial.C_dvd_iff_dvd_coeff _ _).2
    (fun n => by simpa using (Polynomial.C_dvd_iff_dvd_coeff _ _).1 (hd n) 0)
  rw [map_mul, aeval_C, norm_mul]
  have hl : ‖algebraMap ℤ_[l] (PadicAlgCl l) (l : ℤ_[l])‖ < 1 := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) l, PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  calc _ ≤ ‖algebraMap ℤ_[l] (PadicAlgCl l) (l : ℤ_[l])‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_aeval_le x hx h) (norm_nonneg _)
    _ < 1 := by rw [mul_one]; exact hl

theorem exists_monic (x : PadicAlgCl l) (hx : ‖x‖ ≤ 1) : ∃ q : ℤ_[l][X], q.Monic ∧ aeval x q = 0 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hi)] at hx
  have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, hx n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hi)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

theorem exists_pow_near_one (x : PadicAlgCl l) (hx : ‖x‖ = 1) :
    ∃ m : ℕ, 0 < m ∧ ‖x ^ m - 1‖ < 1 := by
  obtain ⟨q, hqm, hq⟩ := exists_monic x hx.le
  have hq1 : q ≠ 1 := by rintro rfl; simp at hq
  set d := q.natDegree
  let r : ℕ → ℤ_[l][X] := fun k => (Polynomial.X ^ k) %ₘ q
  have hr : ∀ k, aeval x (r k) = x ^ k := by
    intro k
    have h := congrArg (aeval x) (modByMonic_add_div (Polynomial.X ^ k : ℤ_[l][X]) q)
    simpa [hq] using h
  have hdeg : ∀ k, (r k).natDegree < d := fun k => natDegree_modByMonic_lt _ hqm hq1
  let F : ℕ → (Fin d → ZMod l) := fun k i => PadicInt.toZMod ((r k).coeff i)
  obtain ⟨i, j, hij, hF⟩ := Finite.exists_ne_map_eq_of_infinite F
  have key : ∀ a b : ℕ, F a = F b → a < b → ∃ m : ℕ, 0 < m ∧ ‖x ^ m - 1‖ < 1 := by
    intro a b hab hlt
    have hsm : ‖x ^ b - x ^ a‖ < 1 := by
      rw [← hr b, ← hr a, ← map_sub]
      apply norm_aeval_lt x hx.le
      ext n
      rw [Polynomial.coeff_map, Polynomial.coeff_sub, map_sub, Polynomial.coeff_zero]
      by_cases hn : n < d
      · have := congrFun hab ⟨n, hn⟩
        rw [sub_eq_zero]
        exact this.symm
      · rw [coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hdeg b) (not_lt.1 hn)),
          coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hdeg a) (not_lt.1 hn))]
        simp
    refine ⟨b - a, Nat.sub_pos_of_lt hlt, ?_⟩
    have e : x ^ b - x ^ a = x ^ a * (x ^ (b - a) - 1) := by
      rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hlt.le, mul_one]
    rw [e, norm_mul, norm_pow, hx, one_pow, one_mul] at hsm
    exact hsm
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j hF h
  · exact key j i hF.symm h

theorem frob_inj (z : PadicAlgCl l) (hz : ‖z‖ ≤ 1) (h : ‖z ^ l - 1‖ < 1) : ‖z - 1‖ < 1 := by
  have hp := (Fact.out : l.Prime)
  have hpoly : (((Polynomial.X - 1) ^ l - (Polynomial.X ^ l - 1) : ℤ_[l][X])).map (PadicInt.toZMod (p := l)) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_sub,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one, sub_pow_char, one_pow, sub_self]
  have h1 := norm_aeval_lt z hz _ hpoly
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one] at h1
  have h2 : ‖(z - 1) ^ l‖ < 1 := by
    have e : (z - 1) ^ l = ((z - 1) ^ l - (z ^ l - 1)) + (z ^ l - 1) := by ring
    rw [e]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h1 h)
  rw [norm_pow] at h2
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hp.ne_zero).1 h2

theorem frob_pow (a : ℕ) : ∀ z : PadicAlgCl l, ‖z‖ ≤ 1 → ‖z ^ (l ^ a) - 1‖ < 1 → ‖z - 1‖ < 1 := by
  induction a with
  | zero => intro z _ h; simpa using h
  | succ a ih =>
    intro z hz h
    apply frob_inj z hz
    apply ih (z ^ l) (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz)
    rw [← pow_mul, ← pow_succ']
    exact h

theorem one_le_norm_prod (s : Multiset ℂ_[l]) (h : ∀ a ∈ s, 1 ≤ ‖a‖) : 1 ≤ ‖s.prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, norm_mul]
    have h1 := h a (Multiset.mem_cons_self a s)
    have h2 := ih fun b hb => h b (Multiset.mem_cons_of_mem hb)
    nlinarith

theorem exists_root_near (x : ℂ_[l]) (m : ℕ) (hm : 0 < m) (h : ‖x ^ m - 1‖ < 1) :
    ∃ ζ : ℂ_[l], ζ ^ m = 1 ∧ ‖x - ζ‖ < 1 := by
  set P : ℂ_[l][X] := Polynomial.X ^ m - Polynomial.C 1
  have hPm : P.Monic := by
    simpa [P] using (monic_X_pow_sub_C (1 : ℂ_[l]) hm.ne')
  have hcard : Multiset.card P.roots = P.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPm hcard
  have hev := congrArg (eval x) hprod
  rw [eval_multiset_prod, Multiset.map_map] at hev
  by_contra hne
  push_neg at hne
  have hall : ∀ a ∈ P.roots, 1 ≤ ‖x - a‖ := by
    intro a ha
    apply hne a _
    have := (mem_roots hPm.ne_zero).1 ha
    simpa [P, sub_eq_zero] using this
  have := one_le_norm_prod (P.roots.map fun a => x - a) (by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hb
    exact hall a ha)
  have e : (Multiset.map (eval x ∘ fun a => Polynomial.X - Polynomial.C a) P.roots).prod = (P.roots.map fun a => x - a).prod := by
    congr 1
    exact Multiset.map_congr rfl (fun a _ => by simp)
  rw [e] at hev
  rw [hev] at this
  simp [P] at this
  linarith

theorem exists_near_kur : ∀ (l : ℕ) [Fact l.Prime] (x : ℂ_[l]), ‖x‖ ≤ 1 →
    ∃ y ∈ MaximalUnramifiedExtension l, ‖y‖ ≤ 1 ∧ ‖x - y‖ < 1 := by
  intro l _ x hx
  obtain ⟨x', hx'⟩ := (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl l)).exists_dist_lt x one_pos
  rw [dist_eq_norm] at hx'
  set X0 : ℂ_[l] := (x' : ℂ_[l]) with hX0
  have hn' : ‖X0‖ ≤ 1 := by
    have e : X0 = (X0 - x) + x := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by rw [norm_sub_rev]; exact hx'.le) hx)
  by_cases h0 : ‖X0‖ < 1
  · refine ⟨0, zero_mem _, by simp, ?_⟩
    rw [sub_zero]
    have e : x = (x - X0) + X0 := by ring
    rw [e]; exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx' h0)
  have h1 : ‖x'‖ = 1 := by rw [← PadicComplex.norm_extends]; exact le_antisymm hn' (not_lt.1 h0)
  obtain ⟨m0, hm0, hsm⟩ := exists_pow_near_one x' h1
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0.ne' l (Fact.out : l.Prime).ne_one
  have hz : ‖x' ^ m - 1‖ < 1 :=
    frob_pow a (x' ^ m) (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) h1.le) (by rw [← pow_mul, mul_comm]; exact hsm)
  have hmpos : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hm0)
  have hz' : ‖X0 ^ m - 1‖ < 1 := by
    have e : X0 ^ m - 1 = ((x' ^ m - 1 : PadicAlgCl l) : ℂ_[l]) := by simp [hX0, PadicComplex.coe_eq]
    rw [e, PadicComplex.norm_extends]; exact hz
  obtain ⟨ζ, hζ, hd⟩ := exists_root_near X0 m hmpos hz'
  refine ⟨ζ, ?_, ?_, ?_⟩
  · unfold MaximalUnramifiedExtension
    exact Subfield.le_topologicalClosure _ (Subfield.subset_closure ⟨m, hmpos, hm, hζ⟩)
  · have : ‖ζ‖ ^ m = 1 := by rw [← norm_pow, hζ, norm_one]
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg ζ) hmpos.ne').1 this).le
  · have e : x - ζ = (x - X0) + (X0 - ζ) := by ring
    rw [e]; exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx' hd)

end GlobalTheory.ResidueUnr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnramifiedNearIntegralComplexPadicStatement
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramified_near_integral_complexPadic : ∀ (l : ℕ) [Fact l.Prime] (x : ℂ_[l]), ‖x‖ ≤ 1 → ∃ y ∈ MaximalUnramifiedExtension l, ‖y‖ ≤ 1 ∧ ‖x - y‖ < 1 := by
  first | exact @GlobalTheory.ResidueUnr.exists_near_kur | exact GlobalTheory.ResidueUnr.exists_near_kur | (intros; apply GlobalTheory.ResidueUnr.exists_near_kur <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MaxUnramifiedResidueAlgClosedAndFrobeniusLift
noncomputable section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory.Honda.KurUnr

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_pow_sub_pow_le {y z : K} (hy : ‖y‖ ≤ 1) (hz : ‖z‖ ≤ 1) (i : ℕ) :
    ‖y ^ i - z ^ i‖ ≤ ‖y - z‖ := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : y ^ (i + 1) - z ^ (i + 1) = y * (y ^ i - z ^ i) + (y - z) * z ^ i := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖y‖ * ‖y ^ i - z ^ i‖ ≤ 1 * ‖y - z‖ :=
            mul_le_mul hy ih (norm_nonneg _) zero_le_one
        _ = ‖y - z‖ := one_mul _
    · rw [norm_mul, norm_pow]
      calc ‖y - z‖ * ‖z‖ ^ i ≤ ‖y - z‖ * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hz) (norm_nonneg _)
        _ = ‖y - z‖ := mul_one _

theorem norm_eval_sub_eval_le (f : Polynomial K) (hf : ∀ n, ‖f.coeff n‖ ≤ 1) {y z : K}
    (hy : ‖y‖ ≤ 1) (hz : ‖z‖ ≤ 1) : ‖f.eval y - f.eval z‖ ≤ ‖y - z‖ := by
  rw [Polynomial.eval_eq_sum_range y, Polynomial.eval_eq_sum_range z, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
  rw [← mul_sub, norm_mul]
  calc ‖f.coeff i‖ * ‖y ^ i - z ^ i‖ ≤ 1 * ‖y - z‖ :=
        mul_le_mul (hf i) (norm_pow_sub_pow_le hy hz i) (norm_nonneg _) zero_le_one
    _ = ‖y - z‖ := one_mul _

theorem norm_root_le_one (f : Polynomial K) (hm : f.Monic) (hf : ∀ n, ‖f.coeff n‖ ≤ 1) {z : K}
    (hz : f.eval z = 0) : ‖z‖ ≤ 1 := by
  by_contra h
  push_neg at h
  set n := f.natDegree
  have e := hm.as_sum
  have h0 : z ^ n = -∑ i ∈ Finset.range n, f.coeff i * z ^ i := by
    have := congrArg (Polynomial.eval z) e
    rw [hz] at this
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C] at this
    linear_combination -this
  have hz0 : (0 : ℝ) ≤ ‖z‖ ^ (n - 1) := by positivity
  have hb : ‖∑ i ∈ Finset.range n, f.coeff i * z ^ i‖ ≤ ‖z‖ ^ (n - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hz0 fun i hi => ?_
    rw [norm_mul, norm_pow]
    have hi' : i ≤ n - 1 := by
      have := Finset.mem_range.mp hi
      omega
    calc ‖f.coeff i‖ * ‖z‖ ^ i ≤ 1 * ‖z‖ ^ (n - 1) :=
          mul_le_mul (hf i) (pow_le_pow_right₀ h.le hi') (by positivity) zero_le_one
      _ = ‖z‖ ^ (n - 1) := one_mul _
  rw [← norm_neg, ← h0, norm_pow] at hb
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn] at h0
  · have : ‖z‖ ^ (n - 1) < ‖z‖ ^ n := pow_lt_pow_right₀ h (by omega)
    linarith

theorem unr_of_unrOK (l : ℕ) (σ : K →+* K) (h : Formalism.InvariantFactorPaths.G7.UnrOK K l σ) : Unr K l σ := by
  obtain ⟨hp, hl2, hnl, hval, hfr⟩ := h
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hlinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hlK : (l : K) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnl
    exact (inv_pos.mpr hl0).ne' hnl.symm

  have hiso : ∀ a : K, ‖σ a‖ = ‖a‖ := by
    intro a
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    obtain ⟨k, hk⟩ := hval a ha
    set u := a * (l : K) ^ k with hu
    have hc : ‖((l : K) ^ k)‖ = (l : ℝ)⁻¹ ^ k := by rw [norm_zpow, hnl]
    have hun : ‖u‖ = 1 := by
      rw [hu, norm_mul, hc, hk, inv_zpow', ← zpow_add₀ hl0.ne', add_neg_cancel, zpow_zero]
    have hsu : ‖σ u‖ = 1 := by
      have h1 := hfr u hun.le
      have hup : ‖u ^ l‖ = 1 := by rw [norm_pow, hun, one_pow]
      have hne : ‖σ u - u ^ l‖ ≠ ‖u ^ l‖ := by rw [hup]; linarith
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
      rw [sub_add_cancel, hup, max_eq_right (by linarith)] at this
      exact this
    have hσu : σ u = σ a * (l : K) ^ k := by rw [hu, map_mul, map_zpow₀, map_natCast]
    have hcne : ‖((l : K) ^ k)‖ ≠ 0 := by rw [norm_ne_zero_iff]; exact zpow_ne_zero _ hlK
    have e1 : ‖σ a‖ * ‖((l : K) ^ k)‖ = ‖a‖ * ‖((l : K) ^ k)‖ := by
      rw [← norm_mul, ← norm_mul, ← hσu, ← hu, hsu, hun]
    exact mul_right_cancel₀ hcne e1
  refine ⟨hp, hl2, by rw [hnl]; exact hlinv, ?_, hiso, ?_⟩
  · intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    obtain ⟨k, hk⟩ := hval x hx0
    rw [hnl, hk]
    have hkneg : k ≤ -1 := by
      by_contra hk1
      push_neg at hk1
      have : (1 : ℝ) ≤ (l : ℝ) ^ k := one_le_zpow₀ hl1.le (by omega)
      rw [← hk] at this
      linarith
    calc (l : ℝ) ^ k ≤ (l : ℝ) ^ (-1 : ℤ) := zpow_le_zpow_right₀ hl1.le hkneg
      _ = (l : ℝ)⁻¹ := zpow_neg_one _
  · intro x hx
    exact (hfr x hx).trans_lt hlinv

end GlobalTheory.Honda.KurUnr


open GlobalTheory.Honda.KurUnr in
theorem GlobalTheory.Honda.kur_resAlg_unr : ∀ (l : ℕ) [Fact l.Prime], 2 < l →
    ResAlg (MaximalUnramifiedExtension l) ∧ ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, Formalism.InvariantFactorPaths.G7.UnrOK (MaximalUnramifiedExtension l) l σ → Unr (MaximalUnramifiedExtension l) l σ := by
  intro l _ _
  refine ⟨?_, fun σ hσ => unr_of_unrOK l σ hσ⟩
  intro f hm hdeg hf
  set g : Polynomial ℂ_[l] := f.map (MaximalUnramifiedExtension l).subtype with hg
  have hgm : g.Monic := hm.map _
  have hgdeg : g.natDegree = f.natDegree := Polynomial.natDegree_map _
  have hgc : ∀ n, ‖g.coeff n‖ ≤ 1 := fun n => by
    rw [hg, Polynomial.coeff_map]
    exact hf n
  have hdg : g.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hgm.ne_zero, hgdeg]
    exact_mod_cast hdeg.ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root g hdg
  have hz1 : ‖z‖ ≤ 1 := norm_root_le_one g hgm hgc hz
  obtain ⟨y, hyK, hy1, hzy⟩ := GlobalTheory.T.exists_unramified_near_integral_complexPadic l z hz1
  refine ⟨⟨y, hyK⟩, hy1, ?_⟩
  have hev : ((f.eval ⟨y, hyK⟩ : MaximalUnramifiedExtension l) : ℂ_[l]) = g.eval y := by
    rw [hg, Polynomial.eval_map]
    exact (Polynomial.eval₂_hom (MaximalUnramifiedExtension l).subtype ⟨y, hyK⟩).symm
  change ‖((f.eval ⟨y, hyK⟩ : MaximalUnramifiedExtension l) : ℂ_[l])‖ < 1
  rw [hev, ← sub_zero (g.eval y), ← hz]
  calc ‖g.eval y - g.eval z‖ ≤ ‖y - z‖ := norm_eval_sub_eval_le g hgc hy1 hz1
    _ = ‖z - y‖ := norm_sub_rev _ _
    _ < 1 := hzy
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MaxUnramifiedResidueAlgClosedAndFrobeniusLiftStatement
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxUnramified_residueAlgClosed_and_frobeniusLift : ∀ (l : ℕ) [Fact l.Prime], 2 < l → ResAlg (MaximalUnramifiedExtension l) ∧ ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, Formalism.InvariantFactorPaths.G7.UnrOK (MaximalUnramifiedExtension l) l σ → Unr (MaximalUnramifiedExtension l) l σ := by
  first | exact @GlobalTheory.Honda.kur_resAlg_unr | exact GlobalTheory.Honda.kur_resAlg_unr | (intros; apply GlobalTheory.Honda.kur_resAlg_unr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsIntegralHondaLogarithmPairShortWeierstrass
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsIntegralHondaLogarithmPairShortWeierstrass
open PowerSeries GlobalTheory.Honda

namespace GlobalTheory.Honda

theorem intLog_shortW (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 : K)
    (h2 : ‖(2 : K)‖ = 1) (hg2 : ‖g2‖ ≤ 1) (hg3 : ‖g3‖ ≤ 1) :
    IntLog (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW g2 g3))
      (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW g2 g3)) := by
  set W := Formalism.L2.Th1.A.shortW g2 g3 with hW
  have h4 : ‖(4 : K)‖ = 1 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this, norm_mul, h2, one_mul]
  have hmem : ∀ x : K, ‖x‖ ≤ 1 → x ∈ Formalism.G.unitBall K := fun x hx => hx
  have ha4 : W.a₄ ∈ Formalism.G.unitBall K := by
    apply hmem
    show ‖-g2 / 4‖ ≤ 1
    rw [norm_div, norm_neg, h4, div_one]; exact hg2
  have ha6 : W.a₆ ∈ Formalism.G.unitBall K := by
    apply hmem
    show ‖-g3 / 4‖ ≤ 1
    rw [norm_div, norm_neg, h4, div_one]; exact hg3
  have h0 : (0 : K) ∈ Formalism.G.unitBall K := (Formalism.G.unitBall K).zero_mem
  have hcm := Formalism.L2.Th1.A.coeffMem K W (Formalism.G.unitBall K) h0 h0 h0 ha4 ha6
  obtain ⟨hl0, hl1, hlom, -⟩ := Formalism.L2.Th1.A.logSpec K W
  obtain ⟨he0, -, hle, hel, -⟩ := Formalism.L2.Th1.A.expSpec K W
  obtain ⟨-, hfgl⟩ := Formalism.L2.Th1.A.fglLog K W
  refine ⟨⟨hl0, hl1, he0, hel, hle⟩, ?_, ?_⟩
  · intro n
    rw [hlom]
    exact hcm.2.2.2.2.1 n
  · intro n
    unfold Formalism.L2.Th1.C.fadd
    rw [← hfgl]
    exact hcm.2.2.2.2.2.2.1 n

end GlobalTheory.Honda
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsIntegralHondaLogarithmPairShortWeierstrassStatement
open PowerSeries GlobalTheory.Honda
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegralHondaLogarithmPair_shortWeierstrass : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 : K), ‖(2 : K)‖ = 1 → ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 → IntLog (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW g2 g3)) (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW g2 g3)) := by
  first | exact @GlobalTheory.Honda.intLog_shortW | exact GlobalTheory.Honda.intLog_shortW | (intros; apply GlobalTheory.Honda.intLog_shortW <;> assumption)
end
end

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

noncomputable section
namespace GlobalTheory.HondaCM3

theorem shortW_map {K L : Type} [Field K] [Field L] (φ : K →+* L) (g2 g3 : K) :
    (Formalism.L2.Th1.A.shortW g2 g3).map φ = Formalism.L2.Th1.A.shortW (φ g2) (φ g3) := by
  ext <;> simp [Formalism.L2.Th1.A.shortW, map_div₀, map_neg, map_ofNat]

theorem ltLog_map {K L : Type} [Field K] [Field L] (φ : K →+* L) (l : ℕ) :
    PowerSeries.map φ (ltLog K l) = ltLog L l := by
  ext n
  simp only [coeff_map, ltLog, coeff_mk]
  split_ifs <;> simp [map_inv₀, map_pow, map_natCast]

theorem constantCoeff_ltLog {K : Type} [Field K] (l : ℕ) (hl : 2 ≤ l) :
    constantCoeff (ltLog K l) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, ltLog, coeff_mk, dite_eq_right]
  rintro ⟨j, hj⟩
  have : 0 < (l ^ 2) ^ j := pow_pos (pow_pos (by omega) 2) j
  omega

theorem map_subst_of {K L : Type} [CommRing K] [CommRing L] (φ : K →+* L) (f s : K⟦X⟧)
    (hs : constantCoeff s = 0) :
    PowerSeries.map φ (f.subst s) = (PowerSeries.map φ f).subst (PowerSeries.map φ s) :=
  Formalism.L2.Th1.A.More.map_subst' φ (HasSubst.of_constantCoeff_zero hs) f

theorem norm_natCast_eq_one {K : Type} [NormedField K] [IsUltrametricDist K] (l n : ℕ)
    (hl : ‖(l : K)‖ < 1) (hcop : Nat.Coprime n l) : ‖(n : K)‖ = 1 := by
  have hb := Nat.gcd_eq_gcd_ab n l
  rw [hcop] at hb
  have h1 : (1 : K) = (n : K) * (n.gcdA l : K) + (l : K) * (n.gcdB l : K) := by
    have := congrArg (fun z : ℤ => (z : K)) hb
    push_cast at this
    exact this
  have hle : ‖(n : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K n
  refine le_antisymm hle ?_
  by_contra hlt
  push_neg at hlt
  have ha : ‖(n.gcdA l : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one K _
  have hb' : ‖(n.gcdB l : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one K _
  have e1 : ‖(n : K) * (n.gcdA l : K)‖ < 1 := by
    rw [norm_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) ha) hlt
  have e2 : ‖(l : K) * (n.gcdB l : K)‖ < 1 := by
    rw [norm_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hb') hl
  have := IsUltrametricDist.norm_add_le_max ((n : K) * (n.gcdA l : K)) ((l : K) * (n.gcdB l : K))
  rw [← h1, norm_one] at this
  exact absurd this (not_le.2 (max_lt e1 e2))

end GlobalTheory.HondaCM3

namespace GlobalTheory.HondaCM3

theorem one_sub_two_omega_sq (d : ℕ) : (1 - 2 * omegaK d) ^ 2 = -(d : ℂ) := by
  have h : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; rfl
  rw [omegaK]
  have : (1 : ℂ) - 2 * ((1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2) = -(Complex.I * ((Real.sqrt d : ℝ) : ℂ)) := by
    ring
  rw [this, neg_sq, mul_pow, Complex.I_sq, h]; ring

theorem cm3 : CM3 := by
  intro d L hsq hd hCM l _ hl5 hld hinert ι g2 g3 hG
  have hG' := hG
  obtain ⟨hg2K, hg3K, hg2n, hg3n, hdisc, lam, hlam0, hg2, hg3⟩ := hG
  haveI : CompleteSpace (MaximalUnramifiedExtension l) := Formalism.L2.Th1.D.kurComplete l
  have hl2 : 2 < l := by omega
  obtain ⟨σ, hσ, -⟩ := Formalism.L2.Th1.D.kurFrob l hl2
  obtain ⟨hRes, hUnr⟩ := GlobalTheory.T.maxUnramified_residueAlgClosed_and_frobeniusLift l hl2
  have hU := hUnr σ hσ
  set φ : MaximalUnramifiedExtension l →+* ℂ_[l] := (MaximalUnramifiedExtension l).subtype with hφ
  have hnφ : ∀ x : MaximalUnramifiedExtension l, ‖φ x‖ = ‖x‖ := fun x => rfl
  set a2 : MaximalUnramifiedExtension l := ⟨g2, hg2K⟩ with ha2
  set a3 : MaximalUnramifiedExtension l := ⟨g3, hg3K⟩ with ha3
  have hφa2 : φ a2 = g2 := rfl
  have hφa3 : φ a3 = g3 := rfl
  set f := Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW a2 a3) with hf
  set e := Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW a2 a3) with he
  have hZ := Formalism.L2.Th1.A.zMap (MaximalUnramifiedExtension l) ℂ_[l] φ (Formalism.L2.Th1.A.shortW a2 a3)
  rw [shortW_map, hφa2, hφa3] at hZ
  have hmf : PowerSeries.map φ f = Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW g2 g3) := hZ.1
  have hme : PowerSeries.map φ e = uSer g2 g3 := by
    rw [hZ.2.1, Formalism.L2.Th1.A.uSerEq ℂ_[l] g2 g3]
  have hf0 : constantCoeff f = 0 := (Formalism.L2.Th1.A.logSpec (MaximalUnramifiedExtension l) _).1

  have hlK : ‖(l : MaximalUnramifiedExtension l)‖ < 1 := hU.2.2.1
  have h2 : ‖(2 : MaximalUnramifiedExtension l)‖ = 1 := by
    have := norm_natCast_eq_one (K := MaximalUnramifiedExtension l) l 2 hlK
      ((Nat.coprime_primes Nat.prime_two (Fact.out)).2 (by omega))
    simpa using this
  have hInt : IntLog f e := GlobalTheory.T.isIntegralHondaLogarithmPair_shortWeierstrass (MaximalUnramifiedExtension l) a2 a3 h2 hg2n hg3n

  obtain ⟨hωK, hσω⟩ := Formalism.L2.Th1.D.sqrtKur d hsq hd l hl5 hinert ι
  set w : MaximalUnramifiedExtension l := ⟨ι (omegaK d), hωK⟩ with hw
  have hσw : σ w = 1 - w := hσω σ hσ w rfl
  have hσσ : σ (σ w) = w := by rw [hσw, map_sub, map_one, hσw]; ring
  have hsq' : (1 - 2 * w) ^ 2 = -((d : ℕ) : MaximalUnramifiedExtension l) := by
    apply (MaximalUnramifiedExtension l).subtype_injective
    have := congrArg ι (one_sub_two_omega_sq d)
    simp only [map_pow, map_sub, map_one, map_mul, map_ofNat, map_neg, map_natCast] at this
    rw [map_pow, map_sub, map_one, map_mul, map_ofNat, map_neg, map_natCast]
    exact this
  have hd1 : ‖((d : ℕ) : MaximalUnramifiedExtension l)‖ = 1 :=
    norm_natCast_eq_one (K := MaximalUnramifiedExtension l) l d hlK
      ((Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hld)))
  have hnorm : ‖σ w - w‖ = 1 := by
    have e1 : σ w - w = 1 - 2 * w := by rw [hσw]; ring
    rw [e1]
    have : ‖1 - 2 * w‖ ^ 2 = 1 := by rw [← norm_pow, hsq', norm_neg, hd1]
    nlinarith [norm_nonneg (1 - 2 * w), sq_nonneg (‖1 - 2 * w‖ - 1)]

  have hCf : ∀ a : MaximalUnramifiedExtension l, constantCoeff (C a * f) = 0 := fun a => by
    rw [map_mul, hf0, mul_zero]
  have hmapMul : ∀ a : MaximalUnramifiedExtension l, PowerSeries.map φ (Formalism.L2.Th1.C.mulBy f e a) =
      Formalism.L2.Th1.C.mulBy (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW g2 g3)) (uSer g2 g3) (φ a) := by
    intro a
    rw [Formalism.L2.Th1.C.mulBy, Formalism.L2.Th1.C.mulBy, map_subst_of φ e _ (hCf a), hme, map_mul, map_C, hmf]
  have hCoef : CoefLe 1 (Formalism.L2.Th1.C.mulBy f e w) := by
    intro n
    have := GlobalTheory.T.cmMultiplierIntegralSeriesAtInertPrime_proof d L hd hCM l hl5 hld hinert ι g2 g3 hG' n
    rw [← hnφ, ← coeff_map, hmapMul]
    exact this

  have hht : ∃ n, n ≤ l ^ 2 ∧ ‖coeff n (Formalism.L2.Th1.C.mulBy f e (l : MaximalUnramifiedExtension l))‖ = 1 := by
    have hc : ι.symm lam ≠ 0 := by simpa using hlam0
    obtain ⟨L', -, hL2, hL3, -, -⟩ := GlobalTheory.T.exists_homothetic_periodPair_lattice L (ι.symm lam) hc
    have e2 : ι L'.g₂ = g2 := by rw [hL2, map_mul, map_pow, RingEquiv.apply_symm_apply, hg2]
    have e3 : ι L'.g₃ = g3 := by rw [hL3, map_mul, map_pow, RingEquiv.apply_symm_apply, hg3]
    obtain ⟨n, hn, h1⟩ := GlobalTheory.T.formalGroup_height_le_two_good_reduction L' l hl5 ι (by rw [e2]; exact hg2n) (by rw [e3]; exact hg3n)
      (by rw [e2, e3]; exact hdisc)
    refine ⟨n, hn, ?_⟩
    rw [← hnφ, ← coeff_map, hmapMul, map_natCast]
    rw [e2, e3, ← Formalism.L2.Th1.A.uSerEq ℂ_[l] g2 g3] at h1
    exact h1
  obtain ⟨ε, hε1, hεC⟩ := GlobalTheory.T.heightTwo_formalGroup_unramified_multiplier (MaximalUnramifiedExtension l) l σ hU hRes f e hInt w hCoef hσσ hnorm hht
  refine ⟨φ ε, ε.2, hε1, fun n => ?_⟩
  have hs0 : constantCoeff (C ε * ltLog (MaximalUnramifiedExtension l) l) = 0 := by
    rw [map_mul, constantCoeff_ltLog l (by omega), mul_zero]
  have hEq : (uSer g2 g3).subst (C (φ ε) * ltLog ℂ_[l] l) =
      PowerSeries.map φ (e.subst (C ε * ltLog (MaximalUnramifiedExtension l) l)) := by
    rw [map_subst_of φ e _ hs0, hme, map_mul, map_C, ltLog_map]
  rw [hEq, coeff_map]
  exact ⟨(coeff n (e.subst (C ε * ltLog (MaximalUnramifiedExtension l) l))).2, by rw [hnφ]; exact hεC n⟩

end GlobalTheory.HondaCM3
end
end

namespace GlobalTheory.TwV.Lt

theorem curveEx_of_cm (h2 : Formalism.L2.Th1.CM.CM2) (h3 : Formalism.L2.Th1.CM.CM3) : CurveEx := by
  intro D cc δ B χ hc hd hχ p _ hcop h5 hIn lam
  obtain ⟨g, hgl, hAt, hM, hLT⟩ :=
    GlobalTheory.InertGenusOne.datum_exists_coprime h2 h3 D cc δ hc hd p hcop h5 hIn lam
  exact ⟨g, hLT, h5, hAt, hIn, hM, hc, hd, hχ, hgl.symm, hAt.2.2.2.1⟩

theorem exists_genusOne_formal_iso_of_unramified_good_reduction (h : Formalism.L2.Th1.CM.CM2) : CurveEx :=
  curveEx_of_cm h GlobalTheory.HondaCM3.cm3

end GlobalTheory.TwV.Lt
