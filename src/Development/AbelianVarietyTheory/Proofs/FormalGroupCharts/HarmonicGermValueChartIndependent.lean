module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqChart
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.EvalSinglePointId
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.HarmInvPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpGauge
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Counterexamples.JetSurvey.FrTruncFixIff
section -- merged from Development.AbelianVarietyTheory.Counterexamples.JetSurvey.BalancedPairs
set_option autoImplicit false

namespace GlobalTheory.ChartJoints

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem emb_bar (H : Host E) (τ : E →+* ℂ) (a : 𝓞 E) :
    τ ((H.bar a : 𝓞 E) : E) = ComplexEmbedding.conjugate τ (a : E) := by
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
  rfl

theorem balanced_pairs (H : Host E) {l : Level H} (c : Coeff l) {S : Type} [CommRing S] [Algebra c.F S]
    (τ τ' : E →+* ℂ) (v : S)
    (hv : ∀ a : 𝓞 E, algebraMap c.F S (embK c τ a) * v = algebraMap c.F S (embK c τ' (H.bar a)) * v)
    (hne : τ ≠ ComplexEmbedding.conjugate τ') : v = 0 := by
  have : ∃ a : 𝓞 E, embK c τ a ≠ embK c τ' (H.bar a) := by
    by_contra hcon
    push_neg at hcon
    apply hne
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
    ext a
    have := congrArg (fun z : c.F => (z : ℂ)) (hcon a)
    simp only [embK_coe] at this
    rw [emb_bar] at this
    exact this
  obtain ⟨a, ha⟩ := this
  have hu : IsUnit (algebraMap c.F S (embK c τ a - embK c τ' (H.bar a))) :=
    (IsUnit.mk0 _ (sub_ne_zero.2 ha)).map _
  apply hu.mul_left_cancel
  rw [map_sub, sub_mul, hv a, sub_self, mul_zero]

end GlobalTheory.ChartJoints
end

set_option autoImplicit false

namespace GlobalTheory.BalancedTwist

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem pairing_eq {S : Type} [CommRing S] {d : ℕ} (M : Fin d → Fin d → S) (v w : Fin d → S) :
    ∑ i, ∑ j, M i j * v i * w j = v ⬝ᵥ (Matrix.of M *ᵥ w) := by
  simp only [dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem balanced_iff (c : Coeff l) {S : Type} [CommRing S] [Algebra c.F S] {d : ℕ}
    (A : 𝓞 E → Matrix (Fin d) (Fin d) S) (u : Lt1 Dw → Fin d → S)
    (heig : ∀ (a : 𝓞 E) (ℓ : Lt1 Dw), A a *ᵥ u ℓ = algebraMap c.F S (embK c ℓ.1 a) • u ℓ)
    (hsp : ∀ v : Fin d → S, ∃ a : Lt1 Dw → S, ∀ j, ∑ ℓ, a ℓ * u ℓ j = v j)
    (M : Fin d → Fin d → S) :
    (∀ a, (A a)ᵀ * Matrix.of M = Matrix.of M * A (H.bar a)) ↔
      ∀ ℓ ℓ' : Lt1 Dw, ∑ i, ∑ j, M i j * u ℓ i * u ℓ' j ≠ 0 → ℓ'.1 = ComplexEmbedding.conjugate ℓ.1 := by
  have eL : ∀ a ℓ ℓ', u ℓ ⬝ᵥ (((A a)ᵀ * Matrix.of M) *ᵥ u ℓ') =
      algebraMap c.F S (embK c ℓ.1 a) * (u ℓ ⬝ᵥ (Matrix.of M *ᵥ u ℓ')) := by
    intro a ℓ ℓ'
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, heig, smul_dotProduct, smul_eq_mul]
  have eR : ∀ a ℓ ℓ', u ℓ ⬝ᵥ ((Matrix.of M * A a) *ᵥ u ℓ') =
      algebraMap c.F S (embK c ℓ'.1 a) * (u ℓ ⬝ᵥ (Matrix.of M *ᵥ u ℓ')) := by
    intro a ℓ ℓ'
    rw [← mulVec_mulVec, heig, mulVec_smul, dotProduct_smul, smul_eq_mul]
  have cc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ => by
    ext x; simp [ComplexEmbedding.conjugate]
  constructor
  · intro h ℓ ℓ' hne
    by_contra hc
    apply hne
    rw [pairing_eq]
    refine GlobalTheory.ChartJoints.balanced_pairs H c ℓ.1 ℓ'.1 _ (fun a => ?_) (fun h' => hc ?_)
    · rw [← eL, ← eR, h]
    · rw [h', cc]
  · intro h a
    set N := (A a)ᵀ * Matrix.of M - Matrix.of M * A (H.bar a) with hN
    have h0 : ∀ ℓ ℓ', u ℓ ⬝ᵥ (N *ᵥ u ℓ') = 0 := by
      intro ℓ ℓ'
      rw [hN, sub_mulVec, dotProduct_sub, eL, eR]
      by_cases hz : ∑ i, ∑ j, M i j * u ℓ i * u ℓ' j = 0
      · rw [← pairing_eq, hz]; simp
      · have hb : embK c ℓ'.1 (H.bar a) = embK c ℓ.1 a := by
          apply Subtype.ext
          rw [embK_coe, embK_coe, GlobalTheory.ChartJoints.emb_bar, h ℓ ℓ' hz, cc]
        rw [hb, sub_self]
    have hv : ∀ v : Fin d → S, ∃ a : Lt1 Dw → S, v = ∑ ℓ, a ℓ • u ℓ := by
      intro v
      obtain ⟨a, ha⟩ := hsp v
      exact ⟨a, funext fun j => by simp [← ha j, Finset.sum_apply]⟩
    have h1 : ∀ v w : Fin d → S, v ⬝ᵥ (N *ᵥ w) = 0 := by
      intro v w
      obtain ⟨a, rfl⟩ := hv v
      obtain ⟨b, rfl⟩ := hv w
      simp [sum_dotProduct, mulVec_sum, dotProduct_sum, mulVec_smul, h0]
    rw [← sub_eq_zero]
    ext i j
    have := h1 (Pi.single i 1) (Pi.single j 1)
    have h2 : N i j = 0 := by simpa using this
    exact h2

theorem frTruncFix_iff : FrTruncFixSt ↔ FrTruncFixBSt := by
  have key : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
      (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y)
      (M : Fin C.d → Fin C.d → S),
      (∀ a, (TB.dLin (C.B.A.act a))ᵀ * Matrix.of M = Matrix.of M * TB.dLin (C.B.A.act (H.bar a))) ↔
      ∀ ℓ ℓ' : Lt1 Dw, ∑ i, ∑ j, M i j * C.uvec ℓ i * C.uvec ℓ' j ≠ 0 →
        ℓ'.1 = ComplexEmbedding.conjugate ℓ.1 := by
    intro E _ _ _ H Dw l Xo c _ S _ _ _ y C M
    refine balanced_iff c (fun a => TB.dLin (C.B.A.act a)) C.uvec (fun a ℓ => ?_)
      (fun v => (C.chart.basis v).exists) M
    funext i
    exact GlobalTheory.EigDir.linEig_holds E H Dw l Xo c S y C a ℓ i
  constructor
  · intro h E _ _ _ H Dw l Xo c _ hs S _ _ _ y C
    obtain ⟨e', hfr, hrig, cc, h1, h2, h3, h4, h5⟩ := h E H Dw l Xo c hs S y C
    exact ⟨e', hfr, hrig, cc, h1, h2, h3, fun m => (key E H Dw l Xo c S y C (cc m)).1 (h4 m), h5⟩
  · intro h E _ _ _ H Dw l Xo c _ hs S _ _ _ y C
    obtain ⟨e', hfr, hrig, cc, h1, h2, h3, h4, h5⟩ := h E H Dw l Xo c hs S y C
    exact ⟨e', hfr, hrig, cc, h1, h2, h3, fun m => (key E H Dw l Xo c S y C (cc m)).2 (h4 m), h5⟩

end GlobalTheory.BalancedTwist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicGermValueChartIndependent
namespace GlobalTheory

open Formalism.MainNotions.ModuliIntegralCharts.H1

theorem harmonicValue_chart_independent : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 := by
  have hAct : ExpActOfSt := by
    refine expActOf_of_eig ?_
    intro E _ _ _ H Dw l Xo c _ S _ _ _ y C a ℓ i
    exact EigDir.linEig_holds E H Dw l Xo c S y C a ℓ i
  refine chartIndep2_verb ?_ (GlobalTheory.BalancedTwist.frTruncFix_iff.mp frTruncFix_holds) germFix_holds (harmInv_of hAct)
  refine chartIndepTrunc_of (expChartOf_of hAct) (ExpGauge.expGaugeOf_of hAct) tie_holds ExpUniqChart.expUniqTan
    (gaugeUniq_of_global globalFns_holds) (killAddVal_of ?_)
  intro E _ _ _ H
  exact psiCover_holds H

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicGermValueChartIndependentStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_germ_value_chart_independent : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 := by
  first | exact @GlobalTheory.harmonicValue_chart_independent | exact GlobalTheory.harmonicValue_chart_independent | (intros; apply GlobalTheory.harmonicValue_chart_independent <;> assumption)
end
