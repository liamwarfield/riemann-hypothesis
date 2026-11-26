module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBoundMeansPosLogAreaNormalisedTheta

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeTranslateHalfPeriodSigmaStarPowEightMulEq
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeTranslateHalfPeriodSigmaStarPowEightMulEq
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.HalfPeriodValue

open Filter Topology

theorem U1_sgStar_pow_eight : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t : ℂ, t ∉ Λ → 2 * t ∈ Λ →
    U1 Λ t (sgStar Λ) 0 ^ 8 * ((wpF Λ t ^ 2 + g2 Λ / 4) ^ 2 + 2 * g3 Λ * wpF Λ t) = 1 := by
  intro Λ hΛ t ht h2t
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hΛ
  have laws := GlobalTheory.OddTheta.sgStar_laws Λ hΛ
  have hd : Differentiable ℂ (sgStar Λ) := laws.1.1
  have hd0 : deriv (sgStar Λ) 0 = 1 := laws.1.2.1
  have hz0 : sgStar Λ 0 = 0 := (laws.2.1 0).2 Λ.zero_mem
  have hzw : sgStar Λ (2 * t) = 0 := (laws.2.1 _).2 h2t
  have htL : t ∉ L.lattice := fun h => ht ((hL t).2 h)
  have hD0 : L.derivWeierstrassP t = 0 :=
    (GlobalTheory.derivWeierstrassP_eq_zero_iff L htL).2 (by rw [← two_mul]; exact (hL _).1 h2t)

  have hA : HasDerivAt (fun z => sgStar Λ (2 * z)) (deriv (sgStar Λ) (2 * t) * 2) t := by
    have := (hd (2 * t)).hasDerivAt.comp t ((hasDerivAt_id t).const_mul (2 : ℂ))
    rw [mul_one] at this
    exact this
  have hB : HasDerivAt (fun z => -(L.derivWeierstrassP z) * sgStar Λ z ^ 4)
      (-(6 * L.weierstrassP t ^ 2 - L.g₂ / 2) * sgStar Λ t ^ 4 +
        -(L.derivWeierstrassP t) * ((4 : ℕ) * sgStar Λ t ^ (4 - 1) * deriv (sgStar Λ) t)) t :=
    (GlobalTheory.hasDerivAt_derivWeierstrassP L htL).neg.mul ((hd t).hasDerivAt.pow 4)
  have hev : (fun z => sgStar Λ (2 * z)) =ᶠ[𝓝 t] (fun z => -(L.derivWeierstrassP z) * sgStar Λ z ^ 4) := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds htL] with z hz
    have hz' : z ∉ Λ := fun h => hz ((hL z).1 h)
    rw [GlobalTheory.SigmaDuplication.sgStar_two_mul hΛ hz', GlobalTheory.LatticeInvariants.wpD_eq hL z]
  have hu := hA.unique (hB.congr_of_eventuallyEq hev)
  rw [hD0] at hu

  set s : ℂ := if 2 * t / 2 ∈ Λ then 1 else -1 with hs
  have hfun : U1 Λ (2 * t) (sgStar Λ) = fun z => s * sgStar Λ z := funext (hΛ.sg_law h2t)
  have hE : Differentiable ℂ (fun z : ℂ => Complex.exp (-(Real.pi : ℂ) * z * (starRingEnd ℂ) (2 * t) / (area Λ : ℂ) -
      (Real.pi : ℂ) * (2 * t) * (starRingEnd ℂ) (2 * t) / (2 * (area Λ : ℂ)))) := by fun_prop
  have hC : HasDerivAt (U1 Λ (2 * t) (sgStar Λ))
      (deriv (sgStar Λ) (0 + 2 * t) * Complex.exp (-(Real.pi : ℂ) * 0 * (starRingEnd ℂ) (2 * t) / (area Λ : ℂ) -
      (Real.pi : ℂ) * (2 * t) * (starRingEnd ℂ) (2 * t) / (2 * (area Λ : ℂ))) +
        sgStar Λ (0 + 2 * t) * deriv (fun z : ℂ => Complex.exp (-(Real.pi : ℂ) * z * (starRingEnd ℂ) (2 * t) / (area Λ : ℂ) -
      (Real.pi : ℂ) * (2 * t) * (starRingEnd ℂ) (2 * t) / (2 * (area Λ : ℂ)))) 0) 0 :=
    ((hd _).hasDerivAt.comp_add_const 0 (2 * t)).mul (hE 0).hasDerivAt
  have hC' : HasDerivAt (U1 Λ (2 * t) (sgStar Λ)) (s * 1) 0 := by
    rw [hfun, ← hd0]; exact (hd 0).hasDerivAt.const_mul s
  have hv := hC.unique hC'
  rw [zero_add, hzw] at hv
  have hs2 : s ^ 2 = 1 := by rw [hs]; split_ifs <;> norm_num
  have hU : U1 Λ t (sgStar Λ) 0 = sgStar Λ t * Complex.exp (-(Real.pi : ℂ) * t * (starRingEnd ℂ) t / (2 * (area Λ : ℂ))) := by
    simp only [U1, zero_add]
    congr 1
    congr 1
    ring
  have hexp : Complex.exp (-(Real.pi : ℂ) * 0 * (starRingEnd ℂ) (2 * t) / (area Λ : ℂ) -
      (Real.pi : ℂ) * (2 * t) * (starRingEnd ℂ) (2 * t) / (2 * (area Λ : ℂ))) =
      Complex.exp (-(Real.pi : ℂ) * t * (starRingEnd ℂ) t / (2 * (area Λ : ℂ))) ^ 4 := by
    rw [← Complex.exp_nat_mul, map_mul, map_ofNat]
    congr 1
    push_cast
    ring
  rw [hexp] at hv
  have key : U1 Λ t (sgStar Λ) 0 ^ 4 * (6 * L.weierstrassP t ^ 2 - L.g₂ / 2) = -2 * s := by
    rw [hU, mul_pow]
    linear_combination (Complex.exp (-(Real.pi : ℂ) * t * (starRingEnd ℂ) t / (2 * (area Λ : ℂ))) ^ 4) * hu - 2 * hv

  have hcub : 4 * L.weierstrassP t ^ 3 - L.g₂ * L.weierstrassP t - L.g₃ = 0 := by
    have := L.derivWeierstrassP_sq t htL
    rw [hD0] at this
    linear_combination -this
  obtain ⟨hg2, hg3, -, -, hw, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L Λ hL
  rw [hg2, hg3, (hw t ht).1]
  linear_combination (1 / 4 : ℂ) * (U1 Λ t (sgStar Λ) 0 ^ 4 * (6 * L.weierstrassP t ^ 2 - L.g₂ / 2) - 2 * s) * key
    + hs2 - 2 * L.weierstrassP t * U1 Λ t (sgStar Λ) 0 ^ 8 * hcub

end GlobalTheory.HalfPeriodValue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeTranslateHalfPeriodSigmaStarPowEightMulEqStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeTranslate_halfPeriod_sigmaStar_pow_eight_mul_eq_one : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t : ℂ, t ∉ Λ → 2 * t ∈ Λ → U1 Λ t (sgStar Λ) 0 ^ 8 * ((wpF Λ t ^ 2 + g2 Λ / 4) ^ 2 + 2 * g3 Λ * wpF Λ t) = 1 := by
  first | exact @GlobalTheory.HalfPeriodValue.U1_sgStar_pow_eight | exact GlobalTheory.HalfPeriodValue.U1_sgStar_pow_eight | (intros; apply GlobalTheory.HalfPeriodValue.U1_sgStar_pow_eight <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DuplicationFormulaMaxNormEqCpUnitDiscriminant
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DuplicationFormulaMaxNormEqCpUnitDiscriminant
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.DupNorm

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem i_add {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

theorem i_sub {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 :=
  by rw [sub_eq_add_neg]; exact i_add ha (by rwa [norm_neg])

theorem i_mul {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb

theorem i_pow {a : K} (ha : ‖a‖ ≤ 1) (n : ℕ) : ‖a ^ n‖ ≤ 1 := by
  rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha

theorem i_ofNat (n : ℕ) [n.AtLeastTwo] : ‖(OfNat.ofNat n : K)‖ ≤ 1 := by
  have := IsUltrametricDist.norm_natCast_le_one K (OfNat.ofNat n)
  rwa [Nat.cast_ofNat] at this

theorem i_neg {a : K} (ha : ‖a‖ ≤ 1) : ‖-a‖ ≤ 1 := by rwa [norm_neg]

theorem i_one : ‖(1 : K)‖ ≤ 1 := by simp

theorem b_le (W : WeierstrassCurve K) (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1) (h3 : ‖W.a₃‖ ≤ 1)
    (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1) :
    ‖W.b₂‖ ≤ 1 ∧ ‖W.b₄‖ ≤ 1 ∧ ‖W.b₆‖ ≤ 1 ∧ ‖W.b₈‖ ≤ 1 := by
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  repeat' first | exact i_ofNat _ | exact i_one | assumption | apply i_add | apply i_sub | apply i_mul | apply i_pow | apply i_neg

theorem delta_eq (W : WeierstrassCurve K) (x : K) :
    W.Δ = (-48 * x ^ 2 - 8 * W.b₂ * x + (W.b₂ ^ 2 - 32 * W.b₄)) *
        (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) +
      (12 * x ^ 3 - W.b₂ * x ^ 2 - 10 * W.b₄ * x + (W.b₂ * W.b₄ - 27 * W.b₆)) *
        (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

theorem max_norm_eq (W : WeierstrassCurve K) (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1) (h3 : ‖W.a₃‖ ≤ 1)
    (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1) (hΔ : ‖W.Δ‖ = 1) (x : K) :
    max ‖x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈‖ ‖4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆‖ =
      max 1 ‖x‖ ^ 4 := by
  obtain ⟨b2, b4, b6, b8⟩ := b_le W h1 h2 h3 h4 h6
  rcases le_or_gt ‖x‖ 1 with hx | hx
  · have hp : ‖x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈‖ ≤ 1 := by repeat' first | exact i_ofNat _ | exact i_one | assumption | apply i_add | apply i_sub | apply i_mul | apply i_pow | apply i_neg
    have hq : ‖4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆‖ ≤ 1 := by repeat' first | exact i_ofNat _ | exact i_one | assumption | apply i_add | apply i_sub | apply i_mul | apply i_pow | apply i_neg
    rw [max_eq_left hx, one_pow]
    refine le_antisymm (max_le hp hq) ?_
    rw [← hΔ, delta_eq W x]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ ?_) <;> rw [norm_mul] <;>
      refine mul_le_of_le_one_left (norm_nonneg _) ?_ <;> repeat' first | exact i_ofNat _ | exact i_one | assumption | apply i_add | apply i_sub | apply i_mul | apply i_pow | apply i_neg
  · have hR1 : 1 ≤ ‖x‖ := hx.le
    have bd : ∀ {c : K}, ‖c‖ ≤ 1 → ∀ {k m : ℕ}, k ≤ m → ‖c * x ^ k‖ ≤ ‖x‖ ^ m := by
      intro c hc k m hkm
      rw [norm_mul, norm_pow]
      calc ‖c‖ * ‖x‖ ^ k ≤ 1 * ‖x‖ ^ m :=
            mul_le_mul hc (pow_le_pow_right₀ hR1 hkm) (by positivity) zero_le_one
        _ = ‖x‖ ^ m := one_mul _
    have hφ : x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ =
        x ^ 4 + -(W.b₄ * x ^ 2 + (2 * W.b₆) * x ^ 1 + W.b₈ * x ^ 0) := by ring
    have hψ : 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ =
        4 * x ^ 3 + W.b₂ * x ^ 2 + (2 * W.b₄) * x ^ 1 + W.b₆ * x ^ 0 := by ring
    have hr : ‖W.b₄ * x ^ 2 + (2 * W.b₆) * x ^ 1 + W.b₈ * x ^ 0‖ ≤ ‖x‖ ^ 2 :=
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
        ((IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le (bd b4 le_rfl) (bd (i_mul (i_ofNat 2) b6) (by norm_num)))) (bd b8 (by norm_num)))
    have hs : ‖4 * x ^ 3 + W.b₂ * x ^ 2 + (2 * W.b₄) * x ^ 1 + W.b₆ * x ^ 0‖ ≤ ‖x‖ ^ 3 :=
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
        ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le
          ((IsUltrametricDist.norm_add_le_max _ _).trans
            (max_le (bd (i_ofNat 4) le_rfl) (bd b2 (by norm_num))))
          (bd (i_mul (i_ofNat 2) b4) (by norm_num)))) (bd b6 (by norm_num)))
    have h24 : ‖x‖ ^ 2 < ‖x‖ ^ 4 := pow_lt_pow_right₀ hx (by norm_num)
    have h34 : ‖x‖ ^ 3 < ‖x‖ ^ 4 := pow_lt_pow_right₀ hx (by norm_num)
    have hne : ‖x ^ 4‖ ≠ ‖-(W.b₄ * x ^ 2 + (2 * W.b₆) * x ^ 1 + W.b₈ * x ^ 0)‖ := by
      rw [norm_neg, norm_pow]; exact (hr.trans_lt h24).ne'
    rw [hφ, hψ, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_neg, norm_pow,
      max_eq_left (hr.trans h24.le), max_eq_left (hs.trans h34.le), max_eq_right hR1]

theorem max_norm_eq_padicComplex : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]),
    ‖W.a₁‖ ≤ 1 → ‖W.a₂‖ ≤ 1 → ‖W.a₃‖ ≤ 1 → ‖W.a₄‖ ≤ 1 → ‖W.a₆‖ ≤ 1 → ‖W.Δ‖ = 1 →
      ∀ x : ℂ_[p], max ‖x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈‖
        ‖4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆‖ = max 1 ‖x‖ ^ 4 :=
  fun _ _ W h1 h2 h3 h4 h6 hΔ x => max_norm_eq W h1 h2 h3 h4 h6 hΔ x

end GlobalTheory.DupNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DuplicationFormulaMaxNormEqCpUnitDiscriminantStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.duplicationFormula_maxNorm_eq_cp_unitDiscriminant : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]), ‖W.a₁‖ ≤ 1 → ‖W.a₂‖ ≤ 1 → ‖W.a₃‖ ≤ 1 → ‖W.a₄‖ ≤ 1 → ‖W.a₆‖ ≤ 1 → ‖W.Δ‖ = 1 → ∀ x : ℂ_[p], max ‖x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈‖ ‖4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆‖ = max 1 ‖x‖ ^ 4 := by
  first | exact @GlobalTheory.DupNorm.max_norm_eq_padicComplex | exact GlobalTheory.DupNorm.max_norm_eq_padicComplex | (intros; apply GlobalTheory.DupNorm.max_norm_eq_padicComplex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionPointLocalHeightEqOne
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section
namespace GlobalTheory.TorsionHeight

theorem setup (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p)
    (hg : GL3Theta.At D cc δ g) :
    IsLat g.abelian₂ ∧ g2 g.abelian₂ ∈ Qbar ∧ g3 g.abelian₂ ∈ Qbar ∧ TaylorLogMetric.discr g.abelian₂ = 1 ∧
      (∀ t, InRationalLattice g.abelian₂ t → t ∉ g.abelian₂ → wpF g.abelian₂ t ∈ Qbar ∧ wpD g.abelian₂ t ∈ Qbar) ∧
      (∀ t, InRationalLattice g.abelian₂ t → U1 g.abelian₂ t (sgStar g.abelian₂) 0 ∈ Qbar) ∧ g.Ok := by
  obtain ⟨hcc, -, hδ, hΛ, hok⟩ := hg
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -, hdisc, -, -⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  obtain ⟨⟨-, h2, h3⟩, hwp⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  simp only [tor0] at h2 h3
  rw [← hΛ] at hlat hdisc h2 h3 huse hwp
  refine ⟨hlat, h2, h3, hdisc, hwp, fun t ht => ?_, hok⟩
  have := huse t ht 0
  simpa [coef1] using this

theorem lamC_eq {p : ℕ} [Fact p.Prime] {lam : Qbar →+* ℂ_[p]} {ι : ℂ ≃+* ℂ_[p]}
    (hι : ∀ x : Qbar, ι (x : ℂ) = lam x) {x : ℂ} (hx : x ∈ Qbar) : lamC lam x = ι x := by
  rw [lamC, dite_eq_left hx]; exact (hι ⟨x, hx⟩).symm

theorem model_polys {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (A B P : ℂ_[p])
    (hA : lamC g.lam (-(g2 g.abelian₂) / 4) = -A / 4) (hB : lamC g.lam (-(g3 g.abelian₂) / 4) = -B / 4) :
    4 * (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * (P - g.C.r)) ^ 3 +
        g.W.b₂ * (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * (P - g.C.r)) ^ 2 +
        2 * g.W.b₄ * (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * (P - g.C.r)) + g.W.b₆ =
      ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 6 * (4 * P ^ 3 - A * P - B) ∧
    (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * (P - g.C.r)) ^ 4 -
        g.W.b₄ * (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * (P - g.C.r)) ^ 2 -
        2 * g.W.b₆ * (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * (P - g.C.r)) - g.W.b₈ =
      ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 8 *
        (((P ^ 2 + A / 4) ^ 2 + 2 * B * P) - g.C.r * (4 * P ^ 3 - A * P - B)) := by
  rw [GL3Theta.G1.W, WeierstrassCurve.variableChange_b₂, WeierstrassCurve.variableChange_b₄,
    WeierstrassCurve.variableChange_b₆, WeierstrassCurve.variableChange_b₈]
  simp only [WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈, wModel, hA, hB]
  constructor <;> ring

theorem lattice_torsion_two_mul {Λ : AddSubgroup ℂ} {v : ℂ} (hv : InRationalLattice Λ v) : InRationalLattice Λ (2 * v) := by
  obtain ⟨m, hm, hmv⟩ := hv
  exact ⟨m, hm, by rw [show (m : ℂ) * (2 * v) = (m * v) + (m * v) by ring]; exact add_mem hmv hmv⟩

theorem sigmaStarTranslate_zero_ne_zero_off_lattice {Λ : AddSubgroup ℂ} (h : IsLat Λ) {v : ℂ} (hv : v ∉ Λ) :
    U1 Λ v (sgStar Λ) 0 ≠ 0 := by
  simp only [U1, zero_add]
  exact mul_ne_zero ((h.sg_eq_zero v).not.2 hv) (Complex.exp_ne_zero _)

theorem dbl_complex {Λ : AddSubgroup ℂ} (h : IsLat Λ) {v : ℂ} (hv : v ∉ Λ) (h2v : 2 * v ∉ Λ) :
    wpF Λ (2 * v) * (4 * wpF Λ v ^ 3 - g2 Λ * wpF Λ v - g3 Λ) =
      (wpF Λ v ^ 2 + g2 Λ / 4) ^ 2 + 2 * g3 Λ * wpF Λ v := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  obtain ⟨e2, e3, -, -, hw, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L Λ hL
  rw [e2, e3, (hw _ h2v).1, (hw _ hv).1, two_mul]
  exact GlobalTheory.TorsionIntegral.dbl L (fun h' => hv ((hL v).2 h')) (fun h' => h2v ((hL _).2 (by rwa [two_mul])))

theorem mu_double (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p)
    (hg : GL3Theta.At D cc δ g) (v : ℂ) (hv : InRationalLattice g.abelian₂ v) (hv0 : v ∉ g.abelian₂) (h2v : 2 * v ∉ g.abelian₂) :
    ‖GlobalTheory.ThetaTransl.cval g (2 * v)‖ ^ 2 * max 1 ‖xAt g (2 * v)‖ =
      (‖GlobalTheory.ThetaTransl.cval g v‖ ^ 2 * max 1 ‖xAt g v‖) ^ 4 := by
  obtain ⟨hlat, h2, h3, hdisc, hwp, hU, hok⟩ := setup D p cc δ g hg
  obtain ⟨ι, hι⟩ := GlobalTheory.PadicComplexIso.exists_ringEquiv_extending p g.lam
  have hv2 := lattice_torsion_two_mul hv
  obtain ⟨hP, hD⟩ := hwp v hv hv0
  obtain ⟨hP2, -⟩ := hwp (2 * v) hv2 h2v
  have hdup := GlobalTheory.T.translate_modifiedSigma_two_mul_at_zero g.abelian₂ hlat v hv0
  have hsq := GlobalTheory.ThetaPar.ModelPoint.wpD_sq hlat hv0
  have hdbl := dbl_complex hlat hv0 h2v
  obtain ⟨hε, -⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat h2 h3 hdisc
  obtain ⟨⟨ha1, ha2, ha3, ha4, ha6, hΔ⟩, -⟩ := hok
  have key := GlobalTheory.T.duplicationFormula_maxNorm_eq_cp_unitDiscriminant p g.W ha1 ha2 ha3 ha4 ha6 hΔ (xAt g v)
  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hεdef
  have hA : lamC g.lam (-(g2 g.abelian₂) / 4) = -(ι (g2 g.abelian₂)) / 4 := by
    rw [GlobalTheory.ThetaPar.ModelPoint.lamC_neg_div_four _ h2, lamC_eq hι h2]
  have hB : lamC g.lam (-(g3 g.abelian₂) / 4) = -(ι (g3 g.abelian₂)) / 4 := by
    rw [GlobalTheory.ThetaPar.ModelPoint.lamC_neg_div_four _ h3, lamC_eq hι h3]
  obtain ⟨hψ, hφ⟩ := model_polys g (ι (g2 g.abelian₂)) (ι (g3 g.abelian₂)) (ι (wpF g.abelian₂ v)) hA hB
  have hx : xAt g v = ε ^ 2 * (ι (wpF g.abelian₂ v) - g.C.r) := by
    rw [xAt, lamC_eq hι hP]
  have hx2 : xAt g (2 * v) = ε ^ 2 * (ι (wpF g.abelian₂ (2 * v)) - g.C.r) := by
    rw [xAt, lamC_eq hι hP2]
  have hc : GlobalTheory.ThetaTransl.cval g v = ι (U1 g.abelian₂ v (sgStar g.abelian₂) 0) := by
    rw [GlobalTheory.ThetaTransl.cval, lamC_eq hι (hU v hv)]
  have hc2 : GlobalTheory.ThetaTransl.cval g (2 * v) = -(ι (wpD g.abelian₂ v)) * ι (U1 g.abelian₂ v (sgStar g.abelian₂) 0) ^ 4 := by
    rw [GlobalTheory.ThetaTransl.cval, lamC_eq hι (hU _ hv2), hdup, map_mul, map_neg, map_pow]
  have hsqι := congrArg ι hsq
  have hdblι := congrArg ι hdbl
  simp only [map_mul, map_pow, map_sub, map_add (f := _), map_ofNat, map_div₀] at hsqι hdblι
  rw [← hx] at hψ hφ
  set P := ι (wpF g.abelian₂ v)
  set P₂ := ι (wpF g.abelian₂ (2 * v))
  set Q := ι (wpD g.abelian₂ v)
  set c := ι (U1 g.abelian₂ v (sgStar g.abelian₂) 0)
  set A := ι (g2 g.abelian₂)
  set B := ι (g3 g.abelian₂)
  set x := xAt g v
  set ψ := 4 * x ^ 3 + g.W.b₂ * x ^ 2 + 2 * g.W.b₄ * x + g.W.b₆
  set φ := x ^ 4 - g.W.b₄ * x ^ 2 - 2 * g.W.b₆ * x - g.W.b₈
  have hxψ : xAt g (2 * v) * ψ = φ := by
    rw [hx2, hψ, hφ]
    linear_combination ε ^ 8 * hdblι
  have hQ : ‖Q‖ ^ 2 = ‖ψ‖ := by
    rw [hψ, norm_mul, norm_pow, hε, one_pow, one_mul, ← norm_pow, hsqι]
  rw [hc2, hc, norm_mul, norm_neg, norm_pow, mul_pow, ← pow_mul, hQ, mul_pow (‖c‖ ^ 2), ← pow_mul, ← key]
  have e1 : ‖ψ‖ * max 1 ‖xAt g (2 * v)‖ = max ‖φ‖ ‖ψ‖ := by
    rw [mul_max_of_nonneg _ _ (norm_nonneg _), mul_one, ← norm_mul, mul_comm ψ, hxψ, max_comm]
  calc ‖ψ‖ * ‖c‖ ^ (4 * 2) * max 1 ‖xAt g (2 * v)‖ = ‖c‖ ^ (4 * 2) * (‖ψ‖ * max 1 ‖xAt g (2 * v)‖) := by ring
    _ = _ := by rw [e1]

theorem mu_two_tors (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p)
    (hg : GL3Theta.At D cc δ g) (v : ℂ) (hv : InRationalLattice g.abelian₂ v) (hv0 : v ∉ g.abelian₂) (h2v : 2 * v ∈ g.abelian₂) :
    (‖GlobalTheory.ThetaTransl.cval g v‖ ^ 2 * max 1 ‖xAt g v‖) ^ 4 = 1 := by
  obtain ⟨hlat, h2, h3, hdisc, hwp, hU, hok⟩ := setup D p cc δ g hg
  obtain ⟨ι, hι⟩ := GlobalTheory.PadicComplexIso.exists_ringEquiv_extending p g.lam
  obtain ⟨hP, hD⟩ := hwp v hv hv0
  have hdup := GlobalTheory.T.translate_modifiedSigma_two_mul_at_zero g.abelian₂ hlat v hv0
  have hsq := GlobalTheory.ThetaPar.ModelPoint.wpD_sq hlat hv0
  have h8 := GlobalTheory.T.latticeTranslate_halfPeriod_sigmaStar_pow_eight_mul_eq_one g.abelian₂ hlat v hv0 h2v
  have h0 : U1 g.abelian₂ (2 * v) (sgStar g.abelian₂) 0 = 0 := by
    rw [hlat.sg_law h2v 0, (hlat.sg_eq_zero 0).2 (zero_mem _), mul_zero]
  have hD0 : wpD g.abelian₂ v = 0 := by
    rw [h0] at hdup
    have hne := pow_ne_zero 4 (sigmaStarTranslate_zero_ne_zero_off_lattice hlat hv0)
    have : wpD g.abelian₂ v * U1 g.abelian₂ v (sgStar g.abelian₂) 0 ^ 4 = 0 := by linear_combination hdup
    exact (mul_eq_zero.1 this).resolve_right hne
  have hf : 4 * wpF g.abelian₂ v ^ 3 - g2 g.abelian₂ * wpF g.abelian₂ v - g3 g.abelian₂ = 0 := by
    rw [← hsq, hD0]; ring
  obtain ⟨hε, -⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat h2 h3 hdisc
  obtain ⟨⟨ha1, ha2, ha3, ha4, ha6, hΔ⟩, -⟩ := hok
  have key := GlobalTheory.T.duplicationFormula_maxNorm_eq_cp_unitDiscriminant p g.W ha1 ha2 ha3 ha4 ha6 hΔ (xAt g v)
  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hεdef
  have hA : lamC g.lam (-(g2 g.abelian₂) / 4) = -(ι (g2 g.abelian₂)) / 4 := by
    rw [GlobalTheory.ThetaPar.ModelPoint.lamC_neg_div_four _ h2, lamC_eq hι h2]
  have hB : lamC g.lam (-(g3 g.abelian₂) / 4) = -(ι (g3 g.abelian₂)) / 4 := by
    rw [GlobalTheory.ThetaPar.ModelPoint.lamC_neg_div_four _ h3, lamC_eq hι h3]
  obtain ⟨hψ, hφ⟩ := model_polys g (ι (g2 g.abelian₂)) (ι (g3 g.abelian₂)) (ι (wpF g.abelian₂ v)) hA hB
  have hx : xAt g v = ε ^ 2 * (ι (wpF g.abelian₂ v) - g.C.r) := by
    rw [xAt, lamC_eq hι hP]
  have hc : GlobalTheory.ThetaTransl.cval g v = ι (U1 g.abelian₂ v (sgStar g.abelian₂) 0) := by
    rw [GlobalTheory.ThetaTransl.cval, lamC_eq hι (hU v hv)]
  have hfι := congrArg ι hf
  have h8ι := congrArg ι h8
  simp only [map_mul, map_pow, map_sub, map_add (f := _), map_ofNat, map_div₀, map_zero, map_one] at hfι h8ι
  rw [← hx] at hψ hφ
  rw [hfι, mul_zero] at hψ
  rw [hfι, mul_zero, sub_zero] at hφ
  rw [hψ, norm_zero, max_eq_left (norm_nonneg _), hφ] at key
  rw [hc, mul_pow, ← pow_mul, ← key, norm_mul, norm_pow, hε, one_pow, one_mul, ← norm_pow, ← norm_mul, h8ι,
    norm_one]

def mu {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (v : ℂ) : ℝ :=
  if v ∈ g.abelian₂ then 1 else ‖GlobalTheory.ThetaTransl.cval g v‖ ^ 2 * max 1 ‖xAt g v‖

theorem mu_add (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p)
    (hg : GL3Theta.At D cc δ g) (v ω : ℂ) (hv : InRationalLattice g.abelian₂ v) (hω : ω ∈ g.abelian₂) : mu g (v + ω) = mu g v := by
  obtain ⟨hlat, -⟩ := setup D p cc δ g hg
  by_cases hv0 : v ∈ g.abelian₂
  · rw [mu, mu, if_pos (add_mem hv0 hω), if_pos hv0]
  · have h1 : v + ω ∉ g.abelian₂ := fun h => hv0 (by simpa using sub_mem h hω)
    rw [mu, mu, if_neg h1, if_neg hv0, GlobalTheory.ThetaTransl.cval_norm_periodic D p cc δ g hg v ω hv hω]
    congr 3
    rw [xAt, xAt, hlat.wpF_add_of_mem hω]

theorem mu_two (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p)
    (hg : GL3Theta.At D cc δ g) (v : ℂ) (hv : InRationalLattice g.abelian₂ v) : mu g (2 * v) = mu g v ^ 4 := by
  by_cases hv0 : v ∈ g.abelian₂
  · have h2 : 2 * v ∈ g.abelian₂ := by rw [two_mul]; exact add_mem hv0 hv0
    rw [mu, mu, if_pos h2, if_pos hv0, one_pow]
  by_cases h2v : 2 * v ∈ g.abelian₂
  · rw [mu, mu, if_pos h2v, if_neg hv0, mu_two_tors D p cc δ g hg v hv hv0 h2v]
  · rw [mu, mu, if_neg h2v, if_neg hv0, mu_double D p cc δ g hg v hv hv0 h2v]

theorem mu_pow_two (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p)
    (hg : GL3Theta.At D cc δ g) (v : ℂ) (hv : InRationalLattice g.abelian₂ v) (k : ℕ) :
    mu g ((2 : ℂ) ^ k * v) = mu g v ^ (4 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : InRationalLattice g.abelian₂ ((2 : ℂ) ^ k * v) := by
      obtain ⟨m, hm, hmv⟩ := hv
      refine ⟨m, hm, ?_⟩
      rw [show (m : ℂ) * ((2 : ℂ) ^ k * v) = ((2 ^ k : ℕ) : ℤ) • ((m : ℂ) * v) by push_cast; ring]
      exact zsmul_mem hmv _
    rw [pow_succ, mul_comm ((2 : ℂ) ^ k) 2, mul_assoc, mu_two D p cc δ g hg _ hk, ih, ← pow_mul, pow_succ]

theorem mu_pos (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p)
    (hg : GL3Theta.At D cc δ g) (v : ℂ) (hv : InRationalLattice g.abelian₂ v) : 0 < mu g v := by
  obtain ⟨hlat, -, -, -, -, hU, -⟩ := setup D p cc δ g hg
  obtain ⟨ι, hι⟩ := GlobalTheory.PadicComplexIso.exists_ringEquiv_extending p g.lam
  unfold mu
  split_ifs with hv0
  · exact one_pos
  · have hc : GlobalTheory.ThetaTransl.cval g v ≠ 0 := by
      rw [GlobalTheory.ThetaTransl.cval, lamC_eq hι (hU v hv)]
      exact (map_ne_zero ι).2 (sigmaStarTranslate_zero_ne_zero_off_lattice hlat hv0)
    exact mul_pos (pow_pos (norm_pos_iff.2 hc) 2) (lt_of_lt_of_le one_pos (le_max_left _ _))

theorem eq_one_of_pow_eq {a : ℝ} (ha : 0 < a) {m n : ℕ} (hmn : m < n) (h : a ^ m = a ^ n) : a = 1 := by
  by_contra hne
  exact hmn.ne (pow_right_injective₀ ha hne h)

theorem height_one : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → ∀ v : ℂ, InRationalLattice g.abelian₂ v → v ∉ g.abelian₂ →
      ‖GlobalTheory.ThetaTransl.cval g v‖ ^ 2 * max 1 ‖xAt g v‖ = 1 := by
  intro D p _ cc δ g hg v hv hv0
  obtain ⟨m, hm, hmv⟩ := hv
  have hv' : InRationalLattice g.abelian₂ v := ⟨m, hm, hmv⟩
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => (2 : ZMod m) ^ k)
  have step : ∀ a b : ℕ, a < b → (2 : ZMod m) ^ a = (2 : ZMod m) ^ b → mu g v = 1 := by
    intro a b hlt hpow
    have hdvd : (m : ℤ) ∣ 2 ^ b - 2 ^ a := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hpow, sub_self]
    obtain ⟨c, hc⟩ := hdvd
    have hmem : (2 : ℂ) ^ b * v = (2 : ℂ) ^ a * v + c • ((m : ℂ) * v) := by
      have hc' : ((2 : ℂ) ^ b - 2 ^ a) = (m : ℂ) * c := by exact_mod_cast hc
      rw [zsmul_eq_mul]
      linear_combination v * hc'
    have hva : InRationalLattice g.abelian₂ ((2 : ℂ) ^ a * v) := by
      refine ⟨m, hm, ?_⟩
      rw [show (m : ℂ) * ((2 : ℂ) ^ a * v) = ((2 ^ a : ℕ) : ℤ) • ((m : ℂ) * v) by push_cast; ring]
      exact zsmul_mem hmv _
    have h1 := mu_add D p cc δ g hg _ _ hva (zsmul_mem hmv c)
    rw [← hmem, mu_pow_two D p cc δ g hg v hv', mu_pow_two D p cc δ g hg v hv'] at h1
    exact eq_one_of_pow_eq (mu_pos D p cc δ g hg v hv')
      (Nat.pow_lt_pow_right (by norm_num) hlt) h1.symm
  have h : mu g v = 1 := by
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · exact step a b hlt he
    · exact step b a hlt he.symm
  rwa [mu, if_neg hv0] at h

end GlobalTheory.TorsionHeight
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionPointLocalHeightEqOneStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPoint_localHeight_eq_one : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p), GL3Theta.At D cc δ g → ∀ v : ℂ, InRationalLattice g.abelian₂ v → v ∉ g.abelian₂ → ‖GlobalTheory.ThetaTransl.cval g v‖ ^ 2 * max 1 ‖xAt g v‖ = 1 := by
  first | exact @GlobalTheory.TorsionHeight.height_one | exact GlobalTheory.TorsionHeight.height_one | (intros; apply GlobalTheory.TorsionHeight.height_one <;> assumption)
end
