module

public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapExistsFunctional
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthPageFirstZetaFactorEqPrimePower
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupMomentClosure

@[expose] public section

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ExistsFamilyFunctionals
section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ExistsFamilyFunctionals
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem GlobalTheory.exists_sideFam_both_sides : HypsG → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r), Num P.k P.r lam P.u b bv ga h q0 → IsFamG lam q0 R → ∃ (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ), (haveI := FiniteDimensional.complete ℂ Wp; SideFam p.T.base.z p.T.base.π p.T.base.μW p.T.base.μN p.T.base.μG q0 R l dg) ∧ (haveI := FiniteDimensional.complete ℂ Wq; SideFam p.T.base.z' p.T.base.π' p.T.base.μW' p.T.base.μN p.T.base.μG q0 R l' dg) := by
  intro hH P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R hN hF
  have := FiniteDimensional.complete ℂ Wp
  have := FiniteDimensional.complete ℂ Wq
  obtain ⟨-, -, -, -, -, hu, hu'⟩ := p.hP
  obtain ⟨νq, νq', hS, hS'⟩ := GlobalTheory.T.besselDatum_both_sides_are_sides P.k P.r Wp Wq p.T.base P.u P.u' hu hu'
  obtain ⟨⟨-, -, -, -, hG⟩, hν⟩ := GlobalTheory.NumFam.num_fam P.k P.r lam P.u b bv ga h q0 hN
  obtain ⟨c, hc, hd⟩ := GlobalTheory.BesselDegree.schur_fdeg hH P.k P.r (PI.BesselPeriodGGP.eps48 P.k P.r) p.T.base.μG
    hS.2.2.2.2.2.2.1
  have h1 : ∀ ν, ∃ l : (R ν).H → Wp, n1 ν ≤ q0 →
      IsBeL (R ν) p.T.base.z p.T.base.π p.T.base.μW p.T.base.μN l := by
    intro ν
    by_cases hq : n1 ν ≤ q0
    · obtain ⟨l, hl⟩ := GlobalTheory.T.bessel_gap_exists_functional hH P.k P.r _ _ (h / 2) (R ν) Wp _ _ _ _ _ _ _ (hF ν hq) (hν ν hq).2.2.1 hG hS
      exact ⟨l, fun _ => hl⟩
    · exact ⟨0, fun h' => absurd h' hq⟩
  have h2 : ∀ ν, ∃ l : (R ν).H → Wq, n1 ν ≤ q0 →
      IsBeL (R ν) p.T.base.z' p.T.base.π' p.T.base.μW' p.T.base.μN l := by
    intro ν
    by_cases hq : n1 ν ≤ q0
    · obtain ⟨l, hl⟩ := GlobalTheory.T.bessel_gap_exists_functional hH P.k P.r _ _ (h / 2) (R ν) Wq _ _ _ _ _ _ _ (hF ν hq) (hν ν hq).2.2.1 hG hS'
      exact ⟨l, fun _ => hl⟩
    · exact ⟨0, fun h' => absurd h' hq⟩
  choose l hl using h1
  choose l' hl' using h2
  have hp : ∀ ν, n1 ν ≤ q0 → 0 < c * Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)) := fun ν hq =>
    mul_pos hc (GlobalTheory.FamilyDegreeRatio.degree_ratios P.k P.r lam P.u b bv ga h q0 hN ν hq).1
  exact ⟨l, l', fun ν => c * Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)),
    fun ν hq => ⟨hl ν hq, hp ν hq, (hd _ _ (hF ν hq)).1⟩,
    fun ν hq => ⟨hl' ν hq, hp ν hq, (hd _ _ (hF ν hq)).1⟩⟩
end Gp91
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ExistsFamilyFunctionalsStatement
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.exists_family_functionals : HypsG → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r), Num P.k P.r lam P.u b bv ga h q0 → IsFamG lam q0 R → ∃ (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ), (haveI := FiniteDimensional.complete ℂ Wp; SideFam p.T.base.z p.T.base.π p.T.base.μW p.T.base.μN p.T.base.μG q0 R l dg) ∧ (haveI := FiniteDimensional.complete ℂ Wq; SideFam p.T.base.z' p.T.base.π' p.T.base.μW' p.T.base.μN p.T.base.μG q0 R l' dg) := by
  first | exact @GlobalTheory.exists_sideFam_both_sides | exact GlobalTheory.exists_sideFam_both_sides | (intros; apply GlobalTheory.exists_sideFam_both_sides <;> assumption)
end Gp91
end
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HsqNonneg
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SupTau

theorem hsq_nonneg (r : ℕ) (T b : ℝ) : 0 ≤ Hsq r T b := by
  show 0 ≤ max 1 T * b ^ (20 * (r + 1))
  have h1 : 0 ≤ max 1 T := le_trans zero_le_one (le_max_left _ _)
  have h2 : 0 ≤ b ^ (20 * (r + 1)) := by
    rw [pow_mul]
    exact pow_nonneg (by positivity) _
  exact mul_nonneg h1 h2

theorem arith (a a' d e A A' : ℝ) (n : ℕ) (ha : 0 ≤ a) (ha' : 0 ≤ a') (hd : 0 < d) (he : 0 < e) (hA : 0 ≤ A)
    (hA' : 0 ≤ A') (h : a ^ 2 * d / e ≤ A ^ n) (h' : a' ^ 2 * d / e ≤ A' ^ n) :
    a' * a * d / e ≤ Real.sqrt (A * A') ^ n := by
  have he0 : e ≠ 0 := ne_of_gt he
  have hsq : (Real.sqrt (A * A') ^ n) ^ 2 = A ^ n * A' ^ n := by
    rw [← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt (mul_nonneg hA hA'), mul_pow]
  have hprod : (a' * a * d / e) ^ 2 = (a ^ 2 * d / e) * (a' ^ 2 * d / e) := by
    field_simp <;> ring
  have key : (a' * a * d / e) ^ 2 ≤ (Real.sqrt (A * A') ^ n) ^ 2 := by
    rw [hprod, hsq]
    exact mul_le_mul h h' (by positivity) (pow_nonneg hA n)
  have hl : 0 ≤ a' * a * d / e := by positivity
  have hr : 0 ≤ Real.sqrt (A * A') ^ n := pow_nonneg (Real.sqrt_nonneg _) n
  calc a' * a * d / e = Real.sqrt ((a' * a * d / e) ^ 2) := (Real.sqrt_sq hl).symm
    _ ≤ Real.sqrt ((Real.sqrt (A * A') ^ n) ^ 2) := Real.sqrt_le_sqrt key
    _ = Real.sqrt (A * A') ^ n := Real.sqrt_sq hr

end GlobalTheory.SupTau
end Gp91
end
