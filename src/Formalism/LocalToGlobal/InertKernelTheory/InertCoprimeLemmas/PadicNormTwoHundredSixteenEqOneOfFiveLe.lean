module

public import Formalism.LocalToGlobal.InertKernelTheory.DefsSigma
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FormalExponentialAgree
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PowerSeriesEmbedding
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PFamily
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SigmaStarUniq
public import Formalism.LocalToGlobal.GlobalTheory.NormSqLatticeFunctionEq
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.LogQdLeRd
public import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LamConjTheta0
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CmAll
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.HomotheticLatticeIntegralOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormTwoHundredSixteenEqOneOfFiveLe

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GlobalTheory.GL3.ExistsTorsionPointOfLattice
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestA

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical Formalism.MainNotions
open Formalism.L2.Th1 (F2.IsLat F2.HasCM)

theorem sgStar_spec (L : PeriodPair) :
    Differentiable ℂ (Formalism.L2.Th1.F.sgStar L) ∧ deriv (Formalism.L2.Th1.F.sgStar L) 0 = 1 ∧
      (∀ z, Formalism.L2.Th1.F.sgStar L (-z) = -Formalism.L2.Th1.F.sgStar L z) ∧
      ∀ ω ∈ L.lattice.toAddSubgroup, ∀ z, Formalism.MainNotions.TaylorLogMetric.U1 L.lattice.toAddSubgroup ω (Formalism.L2.Th1.F.sgStar L) z =
        (if ω / 2 ∈ L.lattice.toAddSubgroup then 1 else -1) * Formalism.L2.Th1.F.sgStar L z := by
  obtain ⟨h1, h2, -, h4, -⟩ := Formalism.L2.Th1.F.sgStarBasic L
  refine ⟨h1, h4, h2, fun ω hω z => ?_⟩
  rw [Formalism.L2.GlobalTheoryTheory.taylorLogMetric_U1_eq_U1, Formalism.L2.Th1.F2.thetaTranslationOperator_apply]
  have hfix := Formalism.L2.Th1.F.sgStarFixed L ω z hω
  by_cases h : ω / 2 ∈ L.lattice
  · have hs : Formalism.L2.Th1.F.semiChar L ω = 1 := by unfold Formalism.L2.Th1.F.semiChar; simp [h]
    have h' : ω / 2 ∈ L.lattice.toAddSubgroup := h
    rw [if_pos h', one_mul, ← hfix, hs, one_mul]
  · have hs : Formalism.L2.Th1.F.semiChar L ω = -1 := by unfold Formalism.L2.Th1.F.semiChar; simp [h]
    have h' : ω / 2 ∉ L.lattice.toAddSubgroup := h
    rw [if_neg h', ← hfix, hs]
    ring

theorem sgStar_eq (L : PeriodPair) : Formalism.MainNotions.TaylorLogMetric.sgStar L.lattice.toAddSubgroup = Formalism.L2.Th1.F.sgStar L := by
  have hlat : L.lattice.toAddSubgroup = PI.lat2 L.ω₁ L.ω₂ := Submodule.span_int_eq_addSubgroupClosure _
  have hIm : ((starRingEnd ℂ) L.ω₁ * L.ω₂).im ≠ 0 := by
    have := Formalism.L2.Th1.F.areaPos L
    unfold Formalism.L2.Th1.F.area at this
    exact abs_pos.mp this
  have hF := sgStar_spec L
  have hE := Classical.epsilon_spec (p := fun G : ℂ → ℂ => Differentiable ℂ G ∧ deriv G 0 = 1 ∧ (∀ z, G (-z) = -G z) ∧
    ∀ ω ∈ L.lattice.toAddSubgroup, ∀ z, Formalism.MainNotions.TaylorLogMetric.U1 L.lattice.toAddSubgroup ω G z =
      (if ω / 2 ∈ L.lattice.toAddSubgroup then 1 else -1) * G z) ⟨_, hF⟩
  have huniq : ∀ G G' : ℂ → ℂ,
      (Differentiable ℂ G ∧ deriv G 0 = 1 ∧ (∀ z, G (-z) = -G z) ∧
        ∀ ω ∈ L.lattice.toAddSubgroup, ∀ z, Formalism.MainNotions.TaylorLogMetric.U1 L.lattice.toAddSubgroup ω G z =
          (if ω / 2 ∈ L.lattice.toAddSubgroup then 1 else -1) * G z) →
      (Differentiable ℂ G' ∧ deriv G' 0 = 1 ∧ (∀ z, G' (-z) = -G' z) ∧
        ∀ ω ∈ L.lattice.toAddSubgroup, ∀ z, Formalism.MainNotions.TaylorLogMetric.U1 L.lattice.toAddSubgroup ω G' z =
          (if ω / 2 ∈ L.lattice.toAddSubgroup then 1 else -1) * G' z) → G = G' := by
    intro G G' hG hG'
    rw [hlat] at hG hG'
    exact sigma_star_unique L.ω₁ L.ω₂ hIm G G' hG hG'
  unfold Formalism.MainNotions.TaylorLogMetric.sgStar
  exact huniq _ _ hE hF





end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestA

end
end

noncomputable section

namespace Formalism.L2.KerInert.Sigma

open NumberField Formalism.BasicNotions

theorem lamC_coe {p : ℕ} [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (a : Formalism.MainNotions.TaylorLogMetric.Qbar) :
    Formalism.MainNotions.TaylorLogMetric.lamC lam (a : ℂ) = lam a := by
  unfold Formalism.MainNotions.TaylorLogMetric.lamC
  rw [dite_eq_left a.2]

theorem taylor_sgStar_map (L : PeriodPair) (a2 a3 s0 : Formalism.MainNotions.TaylorLogMetric.Qbar) (h2 : L.g₂ = a2) (h3 : L.g₃ = a3)
    (hs : Formalism.L2.Th1.F.s2 L = s0) :
    Formalism.L2.Th1.F.taylor0 (Formalism.L2.Th1.F.sgStar L) =
      PowerSeries.map (algebraMap Formalism.MainNotions.TaylorLogMetric.Qbar ℂ) (Formalism.L2.Th1.B.sgStar s0 (Formalism.L2.Th1.F.pOf a2 a3)) := by
  rw [Formalism.L2.Th1.F.taylorSgStar L, Formalism.L2.Th1.F.pOfLattice L, h2, h3, hs]
  have hm := Formalism.L2.Th1.F.seriesMap Formalism.MainNotions.TaylorLogMetric.Qbar ℂ (algebraMap Formalism.MainNotions.TaylorLogMetric.Qbar ℂ) a2 a3 s0
    (Formalism.L2.Th1.F.pOf a2 a3)
  rw [hm.2.2.2.2.2, hm.2.2.1]
  rfl

theorem sgSer_eq {p : ℕ} [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (L : PeriodPair)
    (a2 a3 s0 : Formalism.MainNotions.TaylorLogMetric.Qbar) (h2 : L.g₂ = a2) (h3 : L.g₃ = a3) (hs : Formalism.L2.Th1.F.s2 L = s0) :
    Formalism.MainNotions.TaylorLogMetric.sgSer lam L.lattice.toAddSubgroup =
      Formalism.L2.Th1.B.sgStar (lam s0) (Formalism.L2.Th1.F.pOf (lam a2) (lam a3)) := by
  have hT := taylor_sgStar_map L a2 a3 s0 h2 h3 hs
  have e : Formalism.MainNotions.TaylorLogMetric.sgSer lam L.lattice.toAddSubgroup =
      PowerSeries.map lam (Formalism.L2.Th1.B.sgStar s0 (Formalism.L2.Th1.F.pOf a2 a3)) := by
    ext n
    have hn := congrArg (PowerSeries.coeff n) hT
    unfold Formalism.L2.Th1.F.taylor0 at hn
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_map] at hn
    unfold Formalism.MainNotions.TaylorLogMetric.sgSer
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_map, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestA.sgStar_eq L, hn]
    exact lamC_coe lam _
  have hm := Formalism.L2.Th1.F.seriesMap Formalism.MainNotions.TaylorLogMetric.Qbar ℂ_[p] lam a2 a3 s0 (Formalism.L2.Th1.F.pOf a2 a3)
  rw [e, hm.2.2.2.2.2, hm.2.2.1]

theorem wModel_g {p : ℕ} [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (a2 a3 : Formalism.MainNotions.TaylorLogMetric.Qbar) (h2 : Formalism.MainNotions.TaylorLogMetric.g2 Λ = a2) (h3 : Formalism.MainNotions.TaylorLogMetric.g3 Λ = a3) :
    Formalism.L2.Th1.A.g₂ (Formalism.MainNotions.TaylorLogMetric.wModel lam Λ) = lam a2 ∧ Formalism.L2.Th1.A.g₃ (Formalism.MainNotions.TaylorLogMetric.wModel lam Λ) = lam a3 := by
  have e4 : Formalism.MainNotions.TaylorLogMetric.lamC lam (-(Formalism.MainNotions.TaylorLogMetric.g2 Λ) / 4) = -(lam a2) / 4 := by
    have : -(Formalism.MainNotions.TaylorLogMetric.g2 Λ) / 4 = ((-a2 / 4 : Formalism.MainNotions.TaylorLogMetric.Qbar) : ℂ) := by rw [h2]; push_cast; rfl
    rw [this, lamC_coe, map_div₀, map_neg, map_ofNat]
  have e6 : Formalism.MainNotions.TaylorLogMetric.lamC lam (-(Formalism.MainNotions.TaylorLogMetric.g3 Λ) / 4) = -(lam a3) / 4 := by
    have : -(Formalism.MainNotions.TaylorLogMetric.g3 Λ) / 4 = ((-a3 / 4 : Formalism.MainNotions.TaylorLogMetric.Qbar) : ℂ) := by rw [h3]; push_cast; rfl
    rw [this, lamC_coe, map_div₀, map_neg, map_ofNat]
  simp only [Formalism.L2.Th1.A.g₂, Formalism.L2.Th1.A.g₃, WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, Formalism.MainNotions.TaylorLogMetric.wModel, e4, e6]
  constructor <;> ring

theorem g_change {p : ℕ} [Fact p.Prime] (C : WeierstrassCurve.VariableChange ℂ_[p]) (W : WeierstrassCurve ℂ_[p]) :
    Formalism.L2.Th1.A.g₂ (C • W) = ((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 4 * Formalism.L2.Th1.A.g₂ W ∧
      Formalism.L2.Th1.A.g₃ (C • W) = ((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 6 * Formalism.L2.Th1.A.g₃ W := by
  simp only [Formalism.L2.Th1.A.g₂, Formalism.L2.Th1.A.g₃, WeierstrassCurve.variableChange_c₄, WeierstrassCurve.variableChange_c₆]
  constructor <;> ring

theorem wpReg_eq {K : Type} [Field K] [CharZero K] (W : WeierstrassCurve K) :
    Formalism.L2.Th1.A.wpReg W = Formalism.L2.Th1.F.pOf (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W) :=
  Formalism.L2.Th1.F.isWpUnique K _ _ _ _ (Formalism.L2.Th1.A.bridgeWp K W) (Formalism.L2.Th1.F.pOfIsWp K _ _)

section Int

variable {p : ℕ} [Fact p.Prime]

theorem wp_sub_kur (x : ℂ_[p]) (hx : x ∈ Formalism.MainNotions.GL3Theta.Wp p) : x ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p := by
  have hp : p.Prime := Fact.out
  have hle : Subring.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1} ≤
      (Subfield.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ ¬ p ∣ n ∧ ζ ^ n = 1}).toSubring := by
    rw [Subring.closure_le]
    rintro ζ ⟨n, hn, hc, hz⟩
    exact Subfield.subset_closure ⟨n, hn, (Nat.Prime.coprime_iff_not_dvd hp).1 hc.symm, hz⟩
  have hsub : ((Subring.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1} : Subring ℂ_[p]) :
      Set ℂ_[p]) ⊆ ((Subfield.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ ¬ p ∣ n ∧ ζ ^ n = 1} : Subfield ℂ_[p]) :
      Set ℂ_[p]) := fun y hy => hle hy
  exact closure_mono hsub hx

theorem nadd {x y : ℂ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x + y‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

theorem nmul {x y : ℂ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ ≤ 1 := by
  rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

theorem nsub {x y : ℂ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x - y‖ ≤ 1 := by
  rw [sub_eq_add_neg]; exact nadd hx (by rwa [norm_neg])

theorem nnat (n : ℕ) : ‖(n : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one ℂ_[p] n

theorem nofNat (n : ℕ) [n.AtLeastTwo] : ‖(OfNat.ofNat n : ℂ_[p])‖ ≤ 1 := by
  have := nnat (p := p) (OfNat.ofNat n); rwa [Nat.cast_ofNat] at this

theorem not_dvd_23 (hp : p.Prime) (h5 : 5 ≤ p) (a b : ℕ) : ¬ p ∣ 2 ^ a * 3 ^ b := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega

theorem padic_norm_twelve_eq_one_of_five_le (h5 : 5 ≤ p) : ‖(12 : ℂ_[p])‖ = 1 := by
  have hp : p.Prime := Fact.out
  have := Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd (K := ℂ_[p]) hp (Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one p)
    (not_dvd_23 hp h5 2 1)
  norm_num at this
  exact this

theorem padicNorm_twoHundredSixteen_eq_one_of_five_le (h5 : 5 ≤ p) : ‖(216 : ℂ_[p])‖ = 1 := by
  have hp : p.Prime := Fact.out
  have := Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd (K := ℂ_[p]) hp (Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one p)
    (not_dvd_23 hp h5 3 3)
  norm_num at this
  exact this

theorem inv_good (W : WeierstrassCurve ℂ_[p]) (h5 : 5 ≤ p) (i1 : ‖W.a₁‖ ≤ 1) (i2 : ‖W.a₂‖ ≤ 1)
    (i3 : ‖W.a₃‖ ≤ 1) (i4 : ‖W.a₄‖ ≤ 1) (i6 : ‖W.a₆‖ ≤ 1) (hΔ : ‖W.Δ‖ = 1)
    (w1 : W.a₁ ∈ Formalism.MainNotions.GL3Theta.Wp p) (w2 : W.a₂ ∈ Formalism.MainNotions.GL3Theta.Wp p) (w3 : W.a₃ ∈ Formalism.MainNotions.GL3Theta.Wp p)
    (w4 : W.a₄ ∈ Formalism.MainNotions.GL3Theta.Wp p) (w6 : W.a₆ ∈ Formalism.MainNotions.GL3Theta.Wp p) :
    Formalism.L2.Th1.A.g₂ W ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧ Formalism.L2.Th1.A.g₃ W ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧
      ‖Formalism.L2.Th1.A.g₂ W‖ ≤ 1 ∧ ‖Formalism.L2.Th1.A.g₃ W‖ ≤ 1 ∧
      ‖Formalism.L2.Th1.A.g₂ W ^ 3 - 27 * Formalism.L2.Th1.A.g₃ W ^ 2‖ = 1 := _root_.GlobalTheory.CurveDictionary.inv_good W h5 i1 i2 i3 i4 i6 hΔ w1 w2 w3 w4 w6

end Int

theorem s2_in_unramified_closure (dK : ℕ) (L : PeriodPair) (hsq : Squarefree dK) (h4 : dK % 4 = 3)
    (hcm : Formalism.L2.Th1.CM.HasCMBy dK L) (l : ℕ) [Fact l.Prime] (hl5 : 5 ≤ l) (hld : ¬ l ∣ dK)
    (ι : ℂ ≃+* ℂ_[l]) (lam : ℂ_[l]) (hlam : lam ≠ 0)
    (k2 : lam ^ 4 * ι L.g₂ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l) (k3 : lam ^ 6 * ι L.g₃ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l)
    (n2 : ‖lam ^ 4 * ι L.g₂‖ ≤ 1) (n3 : ‖lam ^ 6 * ι L.g₃‖ ≤ 1)
    (nd : ‖(lam ^ 4 * ι L.g₂) ^ 3 - 27 * (lam ^ 6 * ι L.g₃) ^ 2‖ = 1) :
    lam ^ 2 * ι (Formalism.L2.Th1.F.s2 L) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l := by
  have hlp : l.Prime := Fact.out
  have hd0 : 0 < dK := by omega
  obtain ⟨S, hS, -, -, hsum⟩ := Formalism.L2.Th1.F.hasCMByIsogeny dK L hcm (-1) 2 (by simp) hd0
  obtain ⟨hst, hns⟩ := Formalism.L2.Th1.F.hasCMByStable dK L hcm (-1) 2
  rw [Formalism.L2.Th1.D.HomotheticLatticeIntegrality.alpha_sq, hns] at hsum
  have hsum' : -(2 * (dK : ℂ)) * Formalism.L2.Th1.F.s2 L = ∑ P ∈ S, L.weierstrassP P := by
    rw [← hsum]; push_cast; ring
  have hP : ∀ P ∈ S, lam ^ 2 * ι (L.weierstrassP P) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l := by
    intro P hPS
    obtain ⟨h1, h2⟩ := hS.1 P hPS
    have h3 : (dK : ℂ) * P ∈ L.lattice := by
      have h4' := hst _ h1
      have h5 : (dK : ℂ) * P
          = -((((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK dK)
              * ((((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK dK) * P)) := by
        rw [← mul_assoc, ← sq, Formalism.L2.Th1.D.HomotheticLatticeIntegrality.alpha_sq]; ring
      rw [h5]; exact neg_mem h4'
    exact (Formalism.L2.Th1.CM.cm4 dK L hsq h4 hcm l hl5 hld ι lam hlam k2 k3 n2 n3 nd P dK hd0 hld h3 h2).1
  have hn : ¬ l ∣ 2 * dK := by
    intro h
    rcases (Nat.Prime.dvd_mul hlp).1 h with h | h
    · have := Nat.le_of_dvd (by norm_num) h; omega
    · exact hld h
  have hN : ‖((2 * dK : ℕ) : ℂ_[l])‖ = 1 :=
    Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd hlp (Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one l) hn
  have hN0 : ((2 * dK : ℕ) : ℂ_[l]) ≠ 0 := by
    intro h; rw [h, norm_zero] at hN; exact zero_ne_one hN
  have key : lam ^ 2 * ι (Formalism.L2.Th1.F.s2 L)
      = -(((2 * dK : ℕ) : ℂ_[l])⁻¹ * ∑ P ∈ S, lam ^ 2 * ι (L.weierstrassP P)) := by
    have h := congrArg ι hsum'
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_neg, map_mul, map_sum, map_ofNat, map_natCast] at h
    rw [← Finset.mul_sum, ← h]
    push_cast
    push_cast at hN0
    have hd : (dK : ℂ_[l]) ≠ 0 := right_ne_zero_of_mul hN0
    field_simp
  rw [key]
  exact neg_mem (mul_mem (inv_mem (natCast_mem _ _)) (sum_mem fun P hPS => hP P hPS))

theorem sigmaCurveInert_of (hInv : InvAlg) (hS2 : SecondEisensteinAlgebraic) : Formalism.L2.KerInert.Dict.SigmaCurveInert := by
  intro D p _ cc δ g hAt h5 hIn hOW
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
  have hs := hS2 D cc δ hcurve hδ12 L hL
  set a2 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨L.g₂, hg2⟩ with ha2
  set a3 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨L.g₃, hg3⟩ with ha3
  set s0 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨Formalism.L2.Th1.F.s2 L, hs⟩ with hs0
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hLg.symm)

  have hser : Formalism.MainNotions.TaylorLogMetric.sgSer g.lam g.abelian₂ =
      Formalism.L2.Th1.B.sgStar (g.lam s0) (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3)) := by
    rw [hLg]; exact sgSer_eq g.lam L a2 a3 s0 rfl rfl rfl
  have hW0 := wModel_g g.lam g.abelian₂ a2 a3 e2 e3
  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε
  have hεne : ε ≠ 0 := Units.ne_zero _
  obtain ⟨c2, c3⟩ := g_change g.C (Formalism.MainNotions.TaylorLogMetric.wModel g.lam g.abelian₂)
  have gW2 : Formalism.L2.Th1.A.g₂ g.W = ε ^ 4 * g.lam a2 := by rw [← hW0.1]; exact c2
  have gW3 : Formalism.L2.Th1.A.g₃ g.W = ε ^ 6 * g.lam a3 := by rw [← hW0.2]; exact c3
  have hwp : Formalism.L2.Th1.A.wpReg g.W =
      PowerSeries.C (ε ^ 2) * PowerSeries.rescale ε (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3)) := by
    rw [wpReg_eq, gW2, gW3]
    exact (Formalism.L2.Th1.F.seriesScale ℂ_[p] (g.lam a2) (g.lam a3) ε).2.2.2.1
  refine ⟨ε ^ 2 * g.lam s0, ?_, ?_⟩
  ·
    obtain ⟨ι, hι⟩ := Formalism.L2.KerInert.lamExt p g.lam
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
    have hιg2 : ι L.g₂ = g.lam a2 := hι a2
    have hιg3 : ι L.g₃ = g.lam a3 := hι a3
    have hιs : ι (Formalism.L2.Th1.F.s2 L) = g.lam s0 := hι s0
    obtain ⟨i1, i2, i3, i4, i6, hΔ⟩ := hOk.1
    obtain ⟨w1, w2, w3, w4, w6⟩ := hOW
    obtain ⟨k2, k3, n2, n3, nd⟩ := inv_good g.W h5 i1 i2 i3 i4 i6 hΔ w1 w2 w3 w4 w6
    rw [gW2, ← hιg2] at k2 n2
    rw [gW3, ← hιg3] at k3 n3
    rw [gW2, gW3, ← hιg2, ← hιg3] at nd
    rw [← hιs]
    exact s2_in_unramified_closure D.host.d L hdp.squarefree hd4 hcmby p h5 hpd ι ε hεne k2 k3 n2 n3 nd
  ·
    unfold Formalism.L2.Th1.B.sgW
    rw [hser, hwp]
    exact ((Formalism.L2.Th1.F.sigmaScale ℂ_[p] (Formalism.L2.Th1.F.pOf (g.lam a2) (g.lam a3)) (g.lam s0) ε).2).symm

end Formalism.L2.KerInert.Sigma
