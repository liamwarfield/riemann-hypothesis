module

public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicGermValueChartIndependent
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightsBelow
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeExpOfLogLe
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormFamiliesComplexCombinationOfReadings
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmFamilyFunctionalsDetectLowCoefficients
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FourierJacobiCoeffLinearBoundedSections
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GamAtOfLawsJ

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.VanishingLowCoefficientReadingsSpanModels
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumFunctionalKillsComplexCombinations
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SumCmArcFunctionalVanishesLowFourierJacobi
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CoeffEqZeroOfVanishOnInvertibleLetterBlocks
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CoeffEqZeroOfVanishOnInvertibleLetterBlocks
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.ArcCM
open Formalism.L2.Pj hiding Unf GoodEmb

namespace GlobalTheory.ArcDense

theorem eq_zero_of_eval_off {σ : Type} (D P : MvPolynomial σ ℂ) (hD : D ≠ 0)
    (h : ∀ x : σ → ℂ, MvPolynomial.eval x D ≠ 0 → MvPolynomial.eval x P = 0) : P = 0 := by
  have h0 : D * P = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero]
    by_cases hx : MvPolynomial.eval x D = 0
    · rw [hx, zero_mul]
    · rw [h x hx, mul_zero]
  exact (mul_eq_zero.mp h0).resolve_left hD

noncomputable def coefPoly {σ K : Type} [Field K] (ι : K →+* ℂ) (j : ℤ) (Q : MvPolynomial σ (LaurentSeries K)) :
    MvPolynomial σ ℂ :=
  ∑ μ ∈ Q.support, MvPolynomial.monomial μ (ι ((Q.coeff μ).coeff j))

theorem coeff_coefPoly {σ K : Type} [Field K] (ι : K →+* ℂ) (j : ℤ) (Q : MvPolynomial σ (LaurentSeries K))
    (ν : σ →₀ ℕ) : (coefPoly ι j Q).coeff ν = ι ((Q.coeff ν).coeff j) := by
  classical
  rw [coefPoly, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h]; simp

theorem eval_coefPoly {σ K : Type} [Field K] (ι : K →+* ℂ) (j : ℤ) (Q : MvPolynomial σ (LaurentSeries K))
    (x : σ → ℂ) : MvPolynomial.eval x (coefPoly ι j Q) =
      ∑ μ ∈ Q.support, ι ((Q.coeff μ).coeff j) * ∏ v ∈ μ.support, x v ^ μ v := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coefPoly, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.eval_monomial]
  rfl

theorem coeff_eq_zero_of_vanish_on_invBl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (ι : K₁ →+* ℂ) (m : ℕ) (a : Fin m → ℂ) (F : Fin m → Rul Xo c), (∀ x : ArcLt Dw → ℂ, GlobalTheory.ArcQ.InvBl x → ∑ i, a i * ajAt d ι (F i) x = 0) → ∀ μ : ArcLt Dw →₀ ℕ, ∑ i, a i * ι (cfOf d.yF μ d.jj (F i)) = 0 := by
  intro E _ _ _ H Dw l Xo c K₁ _ _ d ι m a F h μ
  classical
  let D : MvPolynomial (ArcLt Dw) ℂ :=
    ∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => (MvPolynomial.X ⟨τ, (i, k)⟩ : MvPolynomial (ArcLt Dw) ℂ)).det
  have hDe : ∀ x : ArcLt Dw → ℂ, MvPolynomial.eval x D =
      ∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => x ⟨τ, (i, k)⟩).det := by
    intro x
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [RingHom.map_det]
    congr 1
    ext i k
    simp
  have hD : D ≠ 0 := by
    intro h0
    have h1 := hDe (fun v => if v.2.1 = v.2.2 then 1 else 0)
    rw [h0, map_zero] at h1
    have h2 : ∀ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => (if i = k then (1 : ℂ) else 0)).det = 1 := by
      intro τ
      have : (Matrix.of fun i k : Fin (Dw.mult τ) => (if i = k then (1 : ℂ) else 0)) = 1 := by
        ext i k
        simp [Matrix.one_apply]
      rw [this, Matrix.det_one]
    simp only [h2, Finset.prod_const_one] at h1
    exact zero_ne_one h1
  let P : MvPolynomial (ArcLt Dw) ℂ :=
    ∑ i, MvPolynomial.C (a i) * coefPoly ι d.jj (arcNum (evR Xo c (F i) d.yF))
  have hP : P = 0 := by
    refine eq_zero_of_eval_off D P hD fun x hx => ?_
    rw [hDe] at hx
    have hx' : InvBl x := fun τ => (Finset.prod_ne_zero_iff.mp hx) τ (Finset.mem_univ τ)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h x hx', map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPolynomial.eval_C, eval_coefPoly]
    rfl
  have := congrArg (AddMonoidAlgebra.coeff · μ) hP
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at this
  change (∑ i, (MvPolynomial.C (a i) * coefPoly ι d.jj (arcNum (evR Xo c (F i) d.yF))).coeff μ) = 0 at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.coeff_C_mul, coeff_coefPoly]
  rfl

end GlobalTheory.ArcDense
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CoeffEqZeroOfVanishOnInvertibleLetterBlocksStatement
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.ArcCM
open Formalism.L2.Pj hiding Unf GoodEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_eq_zero_of_vanish_on_invertibleLetterBlocks : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (ι : K₁ →+* ℂ) (m : ℕ) (a : Fin m → ℂ) (F : Fin m → Rul Xo c), (∀ x : ArcLt Dw → ℂ, GlobalTheory.ArcQ.InvBl x → ∑ i, a i * ajAt d ι (F i) x = 0) → ∀ μ : ArcLt Dw →₀ ℕ, ∑ i, a i * ι (cfOf d.yF μ d.jj (F i)) = 0 := by
  first | exact @GlobalTheory.ArcDense.coeff_eq_zero_of_vanish_on_invBl | exact GlobalTheory.ArcDense.coeff_eq_zero_of_vanish_on_invBl | (intros; apply GlobalTheory.ArcDense.coeff_eq_zero_of_vanish_on_invBl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SumCmArcFunctionalVanishesLowFourierJacobi
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.ArcCM
open Formalism.L2.Pj hiding Unf GoodEmb

namespace GlobalTheory.ArcKill

theorem sum_cfOf_eq_zero : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (ι : K₁ →+* ℂ) (r : ℕ) (U : Unf Xo c (ι.comp (algebraMap c.F K₁)) r) (a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (La c₁ : ℝ), GoodEmb c (ι.comp (algebraMap c.F K₁)) → IsUnf U → Fam n' La c₁ d → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ (m : ℕ) (a : Fin m → ℂ) (F : Fin m → Rul Xo c) (f : ∀ k : U.Comp, Frame (U.X k).Ψ r → ℂ), (∀ i, F i ∈ sec Xo c a' n) → (∀ i k, (U.X k).IsBddSec (laU U a' n k) (rdU U (F i) k)) → (∀ k, f k ∈ (U.X k).SSgt (laU U a' n k) c₁) → (∀ k, ∀ x ∈ (U.X k).dom, f k x = ∑ i, a i * rdU U (F i) k x) → ∀ μ : ArcLt Dw →₀ ℕ, ∑ i, a i * ι (cfOf d.yF μ d.jj (F i)) = 0 := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d ι r U a' n n' La c₁ hG hU hFam hDom hT m a F f hF hB hf hfe
  obtain ⟨⟨hob, -, hpush⟩, ⟨s⟩⟩ := hFam
  obtain ⟨k, ξ', fr, u₁, κ, hu, hiso, -, hfr, hid⟩ :=
    GlobalTheory.T.arcDatum_sectionValue_coeff_eq_fourierJacobi hK.laws hK.laws2 hK.ubc hK.laws5 hK.n5 E H Dw l Xo c K₁ d ι r U s.ξ s.ν₀ a' n
      (hK.ev E H Dw l Xo c) hG hU hob s.tan hpush s.rk s.ξ_ne s.beta hDom hT
  refine GlobalTheory.T.coeff_eq_zero_of_vanish_on_invertibleLetterBlocks E H Dw l Xo c K₁ d ι m a F fun x hx => ?_
  have hlin := GlobalTheory.T.fourierJacobi_coeff_linear_bounded_sections E r (U.X k) (laU U a' n k) m a (fun i => rdU U (F i) k) (f k) (fun i => hB i k)
    (hfe k) ξ' hiso (fun τ => (τ.1 s.ν₀).re) (fr x) (hfr x hx)
  have htr : ∑ τ : (U.X k).Ψ, (τ.1 s.ν₀).re ≤ c₁ := by
    rw [GlobalTheory.sum_re_cmType_eq_half_trace E r (U.X k) s.ν₀]
    exact s.tr
  have h0 := (hf k).2 ξ' hiso (fun τ => (τ.1 s.ν₀).re) htr (fr x) (hfr x hx)
  have hz : u₁ ^ d.jj ≠ 0 := zpow_ne_zero _ hu
  refine (mul_eq_zero.mp ?_).resolve_right hz
  rw [h0] at hlin
  rw [Finset.sum_mul]
  have : ∀ i, a i * ajAt d ι (F i) x * u₁ ^ d.jj =
      κ x * (a i * (U.X k).fj (laU U a' n k) ξ' (fun τ => (τ.1 s.ν₀).re) (rdU U (F i) k) (fr x)) := by
    intro i
    rw [mul_assoc, hid (F i) (hF i) (hB i k) x hx]
    ring
  rw [Finset.sum_congr rfl fun i _ => this i, ← Finset.mul_sum, ← hlin, mul_zero]

end GlobalTheory.ArcKill
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SumCmArcFunctionalVanishesLowFourierJacobiStatement
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.ArcCM
open Formalism.L2.Pj hiding Unf GoodEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_cmArcFunctional_vanishes_low_fourierJacobi : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (ι : K₁ →+* ℂ) (r : ℕ) (U : Unf Xo c (ι.comp (algebraMap c.F K₁)) r) (a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (La c₁ : ℝ), GoodEmb c (ι.comp (algebraMap c.F K₁)) → IsUnf U → Fam n' La c₁ d → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ (m : ℕ) (a : Fin m → ℂ) (F : Fin m → Rul Xo c) (f : ∀ k : U.Comp, Frame (U.X k).Ψ r → ℂ), (∀ i, F i ∈ sec Xo c a' n) → (∀ i k, (U.X k).IsBddSec (laU U a' n k) (rdU U (F i) k)) → (∀ k, f k ∈ (U.X k).SSgt (laU U a' n k) c₁) → (∀ k, ∀ x ∈ (U.X k).dom, f k x = ∑ i, a i * rdU U (F i) k x) → ∀ μ : ArcLt Dw →₀ ℕ, ∑ i, a i * ι (cfOf d.yF μ d.jj (F i)) = 0 := by
  first | exact @GlobalTheory.ArcKill.sum_cfOf_eq_zero | exact GlobalTheory.ArcKill.sum_cfOf_eq_zero | (intros; apply GlobalTheory.ArcKill.sum_cfOf_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumFunctionalKillsComplexCombinations
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ArcCM

section Free

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ

theorem kill_comb_over (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁]
    [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (ι : K₁ →+* ℂ) (σ : c.F →+* ℂ) (hσ : ι.comp (algebraMap c.F K₁) = σ)
    (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (La c₁ : ℝ)
    (hg : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hd : Fam n' La c₁ d) (hD : Dom a' n)
    (hP : GlobalTheory.FrameNorm.HasPrinc U l.M)
    (hχ : ∀ k, ∀ gm ∈ (U.X k).Γ, (U.X k).χ (Formalism.L2.PjFree.laU U a' n k) gm = 1)
    (m : ℕ) (a : Fin m → ℂ) (F : Fin m → Rul Xo c) (f : ∀ k : U.Comp, Frame (U.X k).Ψ r → ℂ)
    (hF : ∀ i, F i ∈ sec Xo c a' n)
    (hB : ∀ i k, (U.X k).IsBddSec (Formalism.L2.PjFree.laU U a' n k) (Formalism.L2.PjFree.rdU U (F i) k))
    (hf : ∀ k, f k ∈ (U.X k).SSgt (Formalism.L2.PjFree.laU U a' n k) c₁)
    (he : ∀ k, ∀ x ∈ (U.X k).dom, f k x = ∑ i, a i * Formalism.L2.PjFree.rdU U (F i) k x) (μ : ArcLt Dw →₀ ℕ) :
    ∑ i, a i * ι (cfOf d.yF μ d.jj (F i)) = 0 := by
  subst hσ
  exact GlobalTheory.T.sum_cmArcFunctional_vanishes_low_fourierJacobi GlobalTheory.ArcCM.known_holds E H Dw l Xo c K₁ d ι r U a' n n' La c₁ hg hU hd hD
    (GlobalTheory.TransvPrinc.transvIn_of_hasPrinc E H Dw l Xo c _ r U a' n hP hχ) m a F f hF hB hf he μ

end Free

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions GlobalTheory.ArcCM GlobalTheory.Shares

theorem kill_comb_rec : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ), InR D j → ∀ (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁), FamQ T.toCore j ka CR Tt cc K₁ d → ∀ σ₁ : K₁ →+* ℂ, σ₁.comp (algebraMap T.Q.c.F K₁) = T.σ₀ → ∀ (m : ℕ) (a : Fin m → ℂ) (F : Fin m → (recB h.toLawsCore).Cusp j ka) (f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ), (∀ k, f k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j ka k) (WeightFamilies.c1 D CR Tt cc j)) → (∀ k, ∀ x ∈ ((T.U j T.σ₀).X k).dom, f k x = ∑ i, a i * rdR h j (F i) k x) → ∑ i, a i * σ₁ (cfOf d.yF d.μ d.jj (F i).1) = 0 := by
  intro D T h j hj ka CR Tt cc K₁ _ _ _ d hd σ₁ hσ m a F f hf he
  exact kill_comb_over _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d σ₁ T.σ₀ hσ D.R.r (Formalism.L2.PjFree.Unf.ofPj (T.U j T.σ₀))
    (wtA ka) ka.n _ _ _ T.good_σ₀ (h.unf j hj _ T.good_σ₀) hd (dom_wtA ka)
    (GlobalTheory.RunIn.gamAt_of_lawsM D T.toCore h.toLawsCore.toLawsM j hj _ T.good_σ₀)
    (h.chiTriv j hj _ T.good_σ₀ _ _ (dom_wtA ka)) m a (fun i => (F i).1) f
    (fun i => cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) _ _ (cutR_le T.C j _ (F i).2))
    (fun i k => ((GlobalTheory.CuspFormsCompare.mem_holSub_iff_forall_SS _ _ _).1
      (((mem_cusp (T.Q.Xo j) T.Q.c (T.U j) _ _ _).1 (cutR_le T.C j _ (F i).2)).2 _ T.good_σ₀) k).1) hf he d.μ

end GlobalTheory.ArcCM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumFunctionalKillsComplexCombinationsStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions GlobalTheory.ArcCM GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcDatum_functional_kills_complexCombinations : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ), InR D j → ∀ (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁), FamQ T.toCore j ka CR Tt cc K₁ d → ∀ σ₁ : K₁ →+* ℂ, σ₁.comp (algebraMap T.Q.c.F K₁) = T.σ₀ → ∀ (m : ℕ) (a : Fin m → ℂ) (F : Fin m → (recB h.toLawsCore).Cusp j ka) (f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ), (∀ k, f k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j ka k) (WeightFamilies.c1 D CR Tt cc j)) → (∀ k, ∀ x ∈ ((T.U j T.σ₀).X k).dom, f k x = ∑ i, a i * rdR h j (F i) k x) → ∑ i, a i * σ₁ (cfOf d.yF d.μ d.jj (F i).1) = 0 := by
  first | exact @GlobalTheory.ArcCM.kill_comb_rec | exact GlobalTheory.ArcCM.kill_comb_rec | (intros; apply GlobalTheory.ArcCM.kill_comb_rec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormsVanishingLowCoeffSpannedByRational
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfForallEmbeddingSumEqZero
namespace GlobalTheory

theorem eq_zero_of_forall_embedding_sum_eq_zero :
    ∀ (K K₁ : Type) [Field K] [CharZero K] [Field K₁] [Algebra K K₁] [FiniteDimensional K K₁] (σ₀ : K →+* ℂ) (n : ℕ) (e : Fin n → ℂ) (y : Fin n → K₁), (∀ c : Fin n → K, ∑ b, σ₀ (c b) * e b = 0 → c = 0) → (∀ σ₁ : K₁ →+* ℂ, σ₁.comp (algebraMap K K₁) = σ₀ → ∑ b, e b * σ₁ (y b) = 0) → y = 0 := by
  intro K K₁ _ _ _ _ _ σ₀ n e y hind hrel
  classical
  letI : Algebra K ℂ := σ₀.toAlgebra
  have hσ : ∀ x : K, algebraMap K ℂ x = σ₀ x := fun _ => rfl
  let ω := Module.finBasis K K₁
  have hcard : Fintype.card (Fin (Module.finrank K K₁)) = Fintype.card (K₁ →ₐ[K] ℂ) := by
    rw [AlgHom.card, Fintype.card_fin]
  let ε : Fin (Module.finrank K K₁) ≃ (K₁ →ₐ[K] ℂ) := Fintype.equivOfCardEq hcard
  have hd := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two K ℂ ω ε
  have hd0 : Algebra.discr K ω ≠ 0 := Algebra.discr_not_zero_of_basis K ω
  have hdet : (Algebra.embeddingsMatrixReindex K ℂ ω ε).det ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero] at hd
    exact hd0 ((algebraMap K ℂ).injective (by rw [hd, map_zero]))
  let u : Fin (Module.finrank K K₁) → ℂ := fun s => ∑ b, σ₀ (ω.repr (y b) s) * e b
  have hu : u = 0 := by
    apply Matrix.eq_zero_of_vecMul_eq_zero hdet
    funext j
    have h1 := hrel (ε j : K₁ →+* ℂ) (by
      ext x
      simp [hσ])
    have h2 : ∀ b, (ε j : K₁ →+* ℂ) (y b) = ∑ s, σ₀ (ω.repr (y b) s) * ε j (ω s) := by
      intro b
      conv_lhs => rw [← ω.sum_repr (y b)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [RingHom.coe_coe, map_sum, Algebra.smul_def, map_mul, AlgHom.commutes, hσ]
    simp only [h2, Finset.mul_sum] at h1
    rw [Finset.sum_comm] at h1
    simp only [Matrix.vecMul, dotProduct, u, Finset.sum_mul, Pi.zero_apply]
    rw [← h1]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun b _ => ?_
    have : Algebra.embeddingsMatrixReindex K ℂ ω ε s j = ε j (ω s) := by
      simp [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]
    rw [this]; ring
  funext b
  apply ω.repr.injective
  ext s
  have := congrFun (hind (fun b => ω.repr (y b) s) (congrFun hu s)) b
  simpa using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsBasisOverEmbedding
namespace GlobalTheory

theorem exists_basis_over_embedding (K : Type) [Field K] (σ₀ : K →+* ℂ) (m : ℕ)
    (a : Fin m → ℂ) :
    ∃ (n : ℕ) (e : Fin n → ℂ) (c : Fin m → Fin n → K),
      (∀ t : Fin n → K, ∑ b, σ₀ (t b) * e b = 0 → t = 0) ∧
        ∀ i, a i = ∑ b, σ₀ (c i b) * e b := by
  letI : Algebra K ℂ := σ₀.toAlgebra
  have hs : ∀ (k : K) (z : ℂ), k • z = σ₀ k * z := fun k z => rfl
  let V : Submodule K ℂ := Submodule.span K (Set.range a)
  haveI : FiniteDimensional K V := FiniteDimensional.span_of_finite K (Set.finite_range a)
  let B := Module.finBasis K V
  have ha : ∀ i, a i ∈ V := fun i => Submodule.subset_span ⟨i, rfl⟩
  refine ⟨Module.finrank K V, fun b => (B b : ℂ), fun i b => B.repr ⟨a i, ha i⟩ b, ?_, ?_⟩
  · intro t ht
    have hli := Fintype.linearIndependent_iff.1 B.linearIndependent t
    funext b
    refine hli ?_ b
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, hs, Submodule.coe_zero]
    exact ht
  · intro i
    have h := congrArg (Subtype.val : V → ℂ) (B.sum_repr ⟨a i, ha i⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, hs] at h
    exact h.symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormsVanishingLowCoeffSpannedByRational
noncomputable section

namespace GlobalTheory.ArcCM

theorem exists_regroup_vectors {K : Type} [Field K] (σ₀ : K →+* ℂ) {M : Type} [AddCommGroup M] [Module K M] {m : ℕ}
    (a : Fin m → ℂ) (F : Fin m → M) :
    ∃ (n : ℕ) (e : Fin n → ℂ) (G : Fin n → M),
      (∀ r : M → ℂ, (∀ x y, r (x + y) = r x + r y) → (∀ (c : K) x, r (c • x) = σ₀ c * r x) →
        ∑ i, a i * r (F i) = ∑ b, e b * r (G b)) ∧
      ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra K K₁] (y : Fin n → K₁),
        (∀ σ₁ : K₁ →+* ℂ, σ₁.comp (algebraMap K K₁) = σ₀ → ∑ b, e b * σ₁ (y b) = 0) → ∀ b, y b = 0 := by
  obtain ⟨n, e, c, hind, ha⟩ := GlobalTheory.exists_basis_over_embedding K σ₀ m a
  refine ⟨n, e, fun b => ∑ i, c i b • F i, ?_, ?_⟩
  · intro r hadd hsm
    have hs : ∀ b, r (∑ i, c i b • F i) = ∑ i, σ₀ (c i b) * r (F i) := fun b => by
      have := map_sum (AddMonoidHom.mk' r hadd) (fun i => c i b • F i) Finset.univ
      simp only [AddMonoidHom.mk'_apply, hsm] at this
      exact this
    simp only [hs, ha, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring
  · intro K₁ _ _ _ y hy b
    haveI : CharZero K := σ₀.charZero
    haveI : FiniteDimensional K K₁ := Module.Finite.of_restrictScalars_finite ℚ K K₁
    exact congrFun (GlobalTheory.eq_zero_of_forall_embedding_sum_eq_zero K K₁ σ₀ n e y hind hy) b

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions GlobalTheory.Shares


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem mggOnto_of_detect_fun : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (Fm : ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁], ((recB h.toLawsCore).Cusp j ka → K₁) → Prop), (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (φ : (recB h.toLawsCore).Cusp j ka → K₁), Fm K₁ φ → ∀ σ₁ : K₁ →+* ℂ, σ₁.comp (algebraMap T.Q.c.F K₁) = T.σ₀ → ∀ (m : ℕ) (a : Fin m → ℂ) (F : Fin m → (recB h.toLawsCore).Cusp j ka) (f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ), (∀ k, f k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j ka k) (WeightFamilies.c1 D CR Tt cc j)) → (∀ k, ∀ x ∈ ((T.U j T.σ₀).X k).dom, f k x = ∑ i, a i * rdR h j (F i) k x) → ∑ i, a i * σ₁ (φ (F i)) = 0) → (∀ F : (recB h.toLawsCore).Cusp j ka, (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (φ : (recB h.toLawsCore).Cusp j ka → K₁), Fm K₁ φ → φ F = 0) → F ∈ WeightFamilies.MggK (recB h.toLawsCore) CR Tt cc j ka) → RdOnto h j ka → MggOnto h j CR Tt cc ka := by
  intro D T h j ka CR Tt cc Fm hkill hdet hon f hf
  obtain ⟨m, a, F, -, hF⟩ := hon f fun k => (hf k).1
  obtain ⟨n, e, G, h1, h2⟩ := exists_regroup_vectors (K := T.Q.c.F) T.σ₀ a F
  have hG : ∀ k, ∀ x ∈ ((T.U j T.σ₀).X k).dom, f k x = ∑ b, e b * rdR h j (G b) k x := by
    intro k x hx
    rw [hF k x hx]
    refine h1 (fun P => rdR h j P k x) (fun P Q => ?_) (fun c P => ?_)
    · exact congrFun (congrFun (map_add (rdU (T.U j T.σ₀)) P.1 Q.1) k) x
    · exact congrFun (congrFun (map_smulₛₗ (rdU (T.U j T.σ₀)) c P.1) k) x
  refine ⟨n, e, G, fun b => hdet (G b) ?_, hG⟩
  intro K₁ _ _ _ d hd
  exact h2 K₁ (fun b => d (G b))
    (fun σ₁ hσ => hkill K₁ d hd σ₁ hσ n e G f hf hG) b


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem mggOnto_of_detect : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (Fm : ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁], ((recB h.toLawsCore).Cusp j ka → K₁) → Prop), (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (φ : (recB h.toLawsCore).Cusp j ka → K₁), Fm K₁ φ → IsLinearMap T.Q.c.F φ ∧ ∀ σ₁ : K₁ →+* ℂ, σ₁.comp (algebraMap T.Q.c.F K₁) = T.σ₀ → ∀ (m : ℕ) (a : Fin m → ℂ) (F : Fin m → (recB h.toLawsCore).Cusp j ka) (f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ), (∀ k, f k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j ka k) (WeightFamilies.c1 D CR Tt cc j)) → (∀ k, ∀ x ∈ ((T.U j T.σ₀).X k).dom, f k x = ∑ i, a i * rdR h j (F i) k x) → ∑ i, a i * σ₁ (φ (F i)) = 0) → (∀ F : (recB h.toLawsCore).Cusp j ka, (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (φ : (recB h.toLawsCore).Cusp j ka → K₁), Fm K₁ φ → φ F = 0) → F ∈ WeightFamilies.MggK (recB h.toLawsCore) CR Tt cc j ka) → RdOnto h j ka → MggOnto h j CR Tt cc ka :=
  fun D T h j ka CR Tt cc Fm hkill =>
    mggOnto_of_detect_fun D T h j ka CR Tt cc Fm fun K₁ _ _ _ φ hφ => (hkill K₁ φ hφ).2

end GlobalTheory.ArcCM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormsVanishingLowCoeffSpannedByRationalStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.forms_vanishing_low_coeff_spanned_by_rational : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (Fm : ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁], ((recB h.toLawsCore).Cusp j ka → K₁) → Prop), (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (φ : (recB h.toLawsCore).Cusp j ka → K₁), Fm K₁ φ → IsLinearMap T.Q.c.F φ ∧ ∀ σ₁ : K₁ →+* ℂ, σ₁.comp (algebraMap T.Q.c.F K₁) = T.σ₀ → ∀ (m : ℕ) (a : Fin m → ℂ) (F : Fin m → (recB h.toLawsCore).Cusp j ka) (f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ), (∀ k, f k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j ka k) (WeightFamilies.c1 D CR Tt cc j)) → (∀ k, ∀ x ∈ ((T.U j T.σ₀).X k).dom, f k x = ∑ i, a i * rdR h j (F i) k x) → ∑ i, a i * σ₁ (φ (F i)) = 0) → (∀ F : (recB h.toLawsCore).Cusp j ka, (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (φ : (recB h.toLawsCore).Cusp j ka → K₁), Fm K₁ φ → φ F = 0) → F ∈ WeightFamilies.MggK (recB h.toLawsCore) CR Tt cc j ka) → RdOnto h j ka → MggOnto h j CR Tt cc ka := by
  exact @GlobalTheory.ArcCM.mggOnto_of_detect
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.VanishingLowCoefficientReadingsSpanModels
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions GlobalTheory.ArcCM GlobalTheory.Shares

namespace GlobalTheory.ConjKill


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem isLinearMap_cfOf {D : D7} {T : Core D} (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j)
    (K₁ : Type) [Field K₁] [Algebra T.Q.c.F K₁] (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁) :
    IsLinearMap T.Q.c.F fun F : (recB h).Cusp j ka => cfOf d.yF d.μ d.jj F.1 := by
  obtain ⟨φ, hφ⟩ := (GlobalTheory.T.arcDatum_coefficientFunctional_linear_degree GlobalTheory.T.arithmeticCMKnownTheorems_proof _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d (wtA ka) ka.n).1
  have hle : ∀ F : (recB h).Cusp j ka, F.1 ∈ sec (T.Q.Xo j) T.Q.c (wtA ka) ka.n := fun F =>
    cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) _ _ (cutR_le T.C j ka F.2)
  have e : ∀ F : (recB h).Cusp j ka, cfOf d.yF d.μ d.jj F.1 = φ ⟨F.1, hle F⟩ := fun F => (hφ ⟨F.1, hle F⟩).symm
  refine ⟨fun F G => ?_, fun a F => ?_⟩
  · rw [e, e, e, ← map_add (f := _)]; rfl
  · rw [e, e, ← map_smul]; rfl


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem mggOnto_of_rdOnto : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ), InR D j → ∀ (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ), (j < D.R.m → DetectQ h.toLawsCore j ka CR Tt cc) → RdOnto h j ka → MggOnto h j CR Tt cc ka := by
  intro D T h j hj ka CR Tt cc hD hR
  by_cases hlt : j < D.R.m
  · refine GlobalTheory.T.forms_vanishing_low_coeff_spanned_by_rational D T h j ka CR Tt cc
      (fun K₁ _ _ _ φ => ∃ d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁, FamQ T.toCore j ka CR Tt cc K₁ d ∧
        φ = fun F => cfOf d.yF d.μ d.jj F.1) ?_ ?_ hR
    · rintro K₁ _ _ _ φ ⟨d, hd, rfl⟩
      exact ⟨isLinearMap_cfOf h.toLawsCore j ka K₁ d, GlobalTheory.T.arcDatum_functional_kills_complexCombinations D T h j hj ka CR Tt cc K₁ d hd⟩
    · intro F hF
      exact hD hlt F fun K₁ _ _ _ d hd => hF K₁ _ ⟨d, hd, rfl⟩
  · have hρ : WeightFamilies.rho D j = 0 := by
      unfold WeightFamilies.rho Ranks.sigW
      exact Nat.sub_eq_zero_of_le (not_lt.1 hlt)
    intro f hf
    obtain ⟨m, a, F, -, hF⟩ := hR f fun k => (hf k).1
    refine ⟨m, a, F, fun i => ?_, hF⟩
    rw [SetLike.mem_coe, Formalism.MainNotions.Gaps.EtaleWeightGaps.MggK_eq_top_of_rho hρ]
    trivial

end GlobalTheory.ConjKill
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.VanishingLowCoefficientReadingsSpanModelsStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions GlobalTheory.ArcCM GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vanishing_low_coefficient_readings_span_models : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ), InR D j → ∀ (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ), (j < D.R.m → DetectQ h.toLawsCore j ka CR Tt cc) → RdOnto h j ka → MggOnto h j CR Tt cc ka := by
  first | exact @GlobalTheory.ConjKill.mggOnto_of_rdOnto | exact GlobalTheory.ConjKill.mggOnto_of_rdOnto | (intros; apply GlobalTheory.ConjKill.mggOnto_of_rdOnto <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CuspReadingsSpanModelFormsShiftedWeights
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem onto_of_page : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (EX : ErrX D) (p : ℕ), ParOK T EX p j → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → (∀ k : ℕ, GlobalTheory.Shares.RdOnto h j (addL wF wL k)) ∧ GlobalTheory.Shares.MggOnto h j 7 Tn (cc D large₂ C2 A2 7 wL) ka := by
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 EX p hPar hPage
  have hG : GlobalTheory.RunIn.GamAt T.toCore := GlobalTheory.RunIn.gamAt_of_lawsCore D T.toCore h.toLawsCore
  obtain ⟨hA, hB, -, -⟩ := GlobalTheory.RunWeights.weights_below D _ _ j (recPJ h j hj) large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0
    hj.1 hPage.hyp
  have key : ∀ u : WeightFamilies.Wt D j, 8 * D.R.f * D.R.r + 4 ≤ u.n → u.LastPos → GlobalTheory.Shares.RdOnto h j u := fun u hn hl =>
    GlobalTheory.T.cuspForm_families_complex_combination_of_readings GlobalTheory.T.harmonic_germ_value_chart_independent D T h j hj hPar.sh hG hPar.bad hPar.same u hn
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj u hl)
  refine ⟨fun k => key _ ?_ ?_, ?_⟩
  · have h1 := hB wF (by simp)
    have e : (addL wF wL k).n = wF.n + k * wL.n := rfl
    omega
  · intro τ i hi
    have h1 := (hA wF (by simp)).2.2.2 τ i hi
    have e : (addL wF wL k).aP τ i = wF.aP τ i + k * wL.aP τ i := rfl
    omega
  · refine GlobalTheory.T.vanishing_low_coefficient_readings_span_models D T h j hj ka 7 Tn _ ?_
      (key ka (hB ka (by simp)) (hA ka (by simp)).2.2.2)
    intro hlt
    obtain ⟨t1, t2, t3, t4, t5, t6⟩ := hPage.tie
    have ht : TieC ⟨1, 2, 1, 2, 1, 2, 1, 4, 7⟩ H 1 4 0 11 C2 A2 7 :=
      ⟨t1, t2, t3, t4, t5, rfl, rfl, t6, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
    obtain ⟨hc, -, -, -, -, h2, h11⟩ := GlobalTheory.ExtraWeight.numbers D _ _ j (recPJ h j hj) _ _ _ _ _ large₂ H C2 A2 7 CT ka wL wF
      Tn nP nW h0 hPage.hyp ht hPage.page hlt hj.1 (le_trans (by norm_num) hPage.df)
    have hT : 0 < Tn := by nlinarith
    exact GlobalTheory.T.cmFamilyFunctionals_detect_lowCoefficients
      GlobalTheory.T.arithmeticCMKnownTheorems_proof D T.toCore h.toLawsCore j ka 7 Tn _ hG hj hlt
      (le_trans (by norm_num) hPage.r8) (by exact_mod_cast hT) hc

end GlobalTheory.RunJoin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CuspReadingsSpanModelFormsShiftedWeightsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspReadings_span_model_forms_shifted_weights : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (EX : ErrX D) (p : ℕ), ParOK T EX p j → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → (∀ k : ℕ, GlobalTheory.Shares.RdOnto h j (addL wF wL k)) ∧ GlobalTheory.Shares.MggOnto h j 7 Tn (cc D large₂ C2 A2 7 wL) ka := by
  first | exact @GlobalTheory.RunJoin.onto_of_page | exact GlobalTheory.RunJoin.onto_of_page | (intros; apply GlobalTheory.RunJoin.onto_of_page <;> assumption)
end
