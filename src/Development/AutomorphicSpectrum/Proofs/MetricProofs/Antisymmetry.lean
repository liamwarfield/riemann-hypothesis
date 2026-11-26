module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SquareSystemPolarVanishing
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XSqLimit
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralParametrizedCover
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineMongeAmpereIntegralStatement
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XSqDens
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XThmaAlg
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AgreementPositive
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Proportional
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.GapEqWeightSubNextStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProportionalStatement

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.XTsgSmul
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.tsg_smul

theorem toWt_inj (Ψ : Type) (N : ℕ) :
    Function.Injective (toWt : MvPolynomial (Ψ × Fin N) ℝ → MvPolynomial (Ψ × Fin N) ℝ) := by
  classical
  let S : Ψ × Fin N → MvPolynomial (Ψ × Fin N) ℝ := fun p => ∑ k ∈ Finset.Ici p.2, X (p.1, k)
  have key : ∀ p, aeval S (gapX p) = X p := by
    intro p
    obtain ⟨a, i⟩ := p
    have h1 : Finset.Ici i = insert i (Finset.Ioi i) := (Finset.Ioi_insert i).symm
    simp only [gapX]
    split_ifs with h
    · have h2 : Finset.Ioi i = Finset.Ici (⟨i.1 + 1, h⟩ : Fin N) := by
        ext k
        simp only [Finset.mem_Ioi, Finset.mem_Ici, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val, Fin.val_mk]
        omega
      have hn : i ∉ Finset.Ici (⟨i.1 + 1, h⟩ : Fin N) := by
        simp only [Finset.mem_Ici, Fin.le_iff_val_le_val, Fin.val_mk]
        omega
      simp only [S, map_sub, aeval_X, h1, h2]
      rw [Finset.sum_insert hn]
      ring
    · have h2 : Finset.Ioi i = ∅ := by
        ext k
        constructor
        · intro hk
          rw [Finset.mem_Ioi, Fin.lt_iff_val_lt_val] at hk
          have := k.isLt
          exfalso
          omega
        · intro hk
          simp at hk
      simp only [S, map_sub, map_zero, aeval_X, h1, h2, sub_zero]
      simp
  have hcomp : (aeval S).comp (toWt : MvPolynomial (Ψ × Fin N) ℝ →ₐ[ℝ] _) = AlgHom.id ℝ _ := by
    apply MvPolynomial.algHom_ext
    intro p
    rw [AlgHom.comp_apply, AlgHom.id_apply]
    show aeval S (aeval gapX (X p)) = X p
    rw [aeval_X, key]
  have e : ∀ q, aeval S (toWt q) = q := fun q => by
    simpa using AlgHom.congr_fun hcomp q
  intro f g hfg
  rw [← e f, ← e g, hfg]

end PositivityTheory.Xgp.tsg_smul

theorem PositivityTheory.Xgp.t_tsg_smul : (∀ (D : ℕ) (κ : ℕ → ℝ) (v : ℝ) (Q : Polynomial ℝ), tsgPoly D κ (Polynomial.C v * Q) = Polynomial.C v * tsgPoly D κ Q) ∧ (∀ (σ : Type) (c : σ → ℝ) (e : σ → ℤ) (v : ℝ) (Q : MvPolynomial σ ℝ), linePoly c e (C v * Q) = Polynomial.C v * linePoly c e Q) ∧ ∀ (Ψ : Type) (N : ℕ), Function.Injective (toWt : MvPolynomial (Ψ × Fin N) ℝ → MvPolynomial (Ψ × Fin N) ℝ) := by
  refine ⟨?_, ?_, fun Ψ N => PositivityTheory.Xgp.tsg_smul.toWt_inj Ψ N⟩
  · intro D κ v Q
    by_cases hv : v = 0
    · subst hv
      simp [tsgPoly]
    · simp only [tsgPoly, Polynomial.natDegree_C_mul hv, Polynomial.coeff_C_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      split_ifs
      · simp only [Polynomial.C_mul]
        ring
      · simp
  · intro σ c e v Q
    simp [linePoly, Polynomial.algebraMap_eq]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticSquareRegularizedConvergence
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticSquareRegularizedConvergence
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.analytic_square_regularized_convergence : Inputs → ∀ (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (a₀ : σ) (ε : σ → ℤ) (Q : AnSq SY a₀ ε) (w : Fin (d + 2) → Option σ), MIntegrable Q.SW.A (fun r => Q.SW.potH (w r)) Q.gH ∧ Tendsto (fun t => mInt Q.SW.A (fun r => Q.SW.potT (w r) t) (Q.gT t)) (𝓝[>] 0) (𝓝 (mInt Q.SW.A (fun r => Q.SW.potH (w r)) Q.gH)) := by
  intro hI d σ _ SY a₀ ε Q w
  classical
  have hCS : ConvergenceSignedStatement := hI.1.2.1
  have ht0 : 0 < Q.SW.t₀ := (Q.SW.reg none).1
  let mm : σ × Fin 2 → Option σ := fun i => if i.2 = 0 then some i.1 else if i.1 = a₀ then none else some i.1
  let c : σ × Fin 2 → ℝ := fun i => 1 / 2 * (ε i.1 : ℝ)
  have hph : ∀ x, 1 / 2 * ∑ a : σ, (ε a : ℝ) * (SY.ph a (Q.q 0 x) + SY.ph a (Q.q 1 x)) = ∑ i : σ × Fin 2, c i * Q.SW.ph (mm i) x := by
    intro x
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fin.sum_univ_two]
    have e0 : Q.SW.ph (mm (a, 0)) x = SY.ph a (Q.q 0 x) := by simp [mm, Q.ph0]
    have e1 : Q.SW.ph (mm (a, 1)) x = SY.ph a (Q.q 1 x) := by
      by_cases ha : a = a₀
      · subst ha
        simp [mm, Q.ph1]
      · simp [mm, ha, Q.ph0]
        exact congrFun (Q.base_ph a ha) x
    rw [e0, e1]
    simp only [c]
    ring
  have hphT : ∀ t x, 1 / 2 * ∑ a : σ, (ε a : ℝ) * (SY.phT a t (Q.q 0 x) + SY.phT a t (Q.q 1 x)) = ∑ i : σ × Fin 2, c i * Q.SW.phT (mm i) t x := by
    intro t x
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fin.sum_univ_two]
    have e0 : Q.SW.phT (mm (a, 0)) t x = SY.phT a t (Q.q 0 x) := by simp [mm, Q.phase_some_eq_comp_first_projection]
    have e1 : Q.SW.phT (mm (a, 1)) t x = SY.phT a t (Q.q 1 x) := by
      by_cases ha : a = a₀
      · subst ha
        simp [mm, Q.phase_none_eq_comp_second_projection]
      · simp [mm, ha, Q.phase_some_eq_comp_first_projection]
        exact congrFun (Q.base_phT a ha t) x
    rw [e0, e1]
    simp only [c]
    ring
  have hgH : Q.gH = fun x => logNormSec Q.L' Q.v x + (Q.cst + ∑ i, c i * Q.SW.ph (mm i) x) := by
    funext x
    simp only [AnSq.gH]
    rw [hph]
    ring
  have hgT : ∀ t, Q.gT t = fun x => logNormSec Q.L' Q.v x + (Q.cst + ∑ i, c i * Q.SW.phT (mm i) t x) := by
    intro t
    funext x
    simp only [AnSq.gT]
    rw [hphT]
    ring
  obtain ⟨hsI, hsE, hsT⟩ := PositivityTheory.Xgp.sq_limit.singular_part hI Q w
  obtain ⟨hrI, hrT⟩ := PositivityTheory.Xgp.sq_limit.regular hCS Q.SW w mm c Q.cst ht0
  refine ⟨?_, ?_⟩
  · rw [hgH]
    exact PositivityTheory.Xgp.sq_limit.mIntegrable_add' _ _ hsI hrI
  · rw [hgH, PositivityTheory.Xgp.sq_limit.mInt_add' _ _ hsI hrI]
    have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), mInt Q.SW.A (fun r => Q.SW.potT (w r) t) (logNormSec Q.L' Q.v) + mInt Q.SW.A (fun r => Q.SW.potT (w r) t) (fun x => Q.cst + ∑ i, c i * Q.SW.phT (mm i) t x) = mInt Q.SW.A (fun r => Q.SW.potT (w r) t) (Q.gT t) := by
      filter_upwards [hsE, Ioo_mem_nhdsGT ht0] with t ht htt
      rw [hgT t]
      refine (PositivityTheory.Xgp.sq_limit.mInt_add' _ _ ht ?_).symm
      apply PositivityTheory.Xgp.sq_limit.mIntegrable_of_continuous
      · intro i
        exact ReciprocityTheory.AnForm.M.isPotentialAdd _ _ _ (Q.SW.sing (w i)).1 (ReciprocityTheory.AnForm.M.isPotential_ofFun _ _ ((Q.SW.reg (w i)).2.2 t htt.1 htt.2.le).1)
      · exact continuous_const.add (continuous_finsetSum _ fun i _ => continuous_const.mul (ReciprocityTheory.AnForm.M.projLine_continuous_of_smooth _ ((Q.SW.reg (mm i)).2.2 t htt.1 htt.2.le).1))
    exact (hsT.add hrT).congr' hev
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticSquareRegularizedConvergenceStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_square_regularized_convergence : Inputs → ∀ (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (a₀ : σ) (ε : σ → ℤ) (Q : AnSq SY a₀ ε) (w : Fin (d + 2) → Option σ), MIntegrable Q.SW.A (fun r => Q.SW.potH (w r)) Q.gH ∧ Tendsto (fun t => mInt Q.SW.A (fun r => Q.SW.potT (w r) t) (Q.gT t)) (𝓝[>] 0) (𝓝 (mInt Q.SW.A (fun r => Q.SW.potH (w r)) Q.gH)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.analytic_square_regularized_convergence | exact GlobalTheory.CompanionTheory.Relay.analytic_square_regularized_convergence | (intros; apply GlobalTheory.CompanionTheory.Relay.analytic_square_regularized_convergence <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdjacentSwapHeightPolynomialRelation
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HeightPolynomialReflectionSum
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SquarePolarIntegralIdentity
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SquareParametrizedDensityFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SquareParametrizedDensityFormula
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.square_parametrized_density_formula : ∀ (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (a₀ : σ) (ε : σ → ℤ) (Q : AnSq SY a₀ ε) (c : σ → ℝ), c a₀ = 0 → ∀ (n k : ℕ), 1 ≤ k → 2 * k ≤ d + 2 → (∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Q.U n → paramDens (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (Q.ΦY n) z = maDens (fun (r : Fin (d + 1)) (z' : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (Q.G n (Fin.tail z')) (z' 0) else ∑ a, c a * Q.α n a (Fin.tail z')) z) ∧ ∀ i < k, ∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Q.U n → paramDens (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) (Q.ΦW n) z = maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; fun (r : Fin (d + 2)) (z' : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 0) + u r 1 * xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 1) else ∑ a, c a * Q.α n a (Fin.tail (Fin.tail z'))) z := by
  intro d σ _ SY a₀ ε Q c hc n k hk _
  exact ⟨fun z hz => PositivityTheory.Xgp.sq_dens.part1 Q c hc n k z hz, fun i hi z hz => PositivityTheory.Xgp.sq_dens.part2 Q c hc n k hk i hi z hz⟩
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SquareParametrizedDensityFormulaStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_parametrized_density_formula : ∀ (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (a₀ : σ) (ε : σ → ℤ) (Q : AnSq SY a₀ ε) (c : σ → ℝ), c a₀ = 0 → ∀ (n k : ℕ), 1 ≤ k → 2 * k ≤ d + 2 → (∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Q.U n → paramDens (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (Q.ΦY n) z = maDens (fun (r : Fin (d + 1)) (z' : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (Q.G n (Fin.tail z')) (z' 0) else ∑ a, c a * Q.α n a (Fin.tail z')) z) ∧ ∀ i < k, ∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Q.U n → paramDens (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) (Q.ΦW n) z = maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; fun (r : Fin (d + 2)) (z' : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 0) + u r 1 * xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 1) else ∑ a, c a * Q.α n a (Fin.tail (Fin.tail z'))) z := by
  first | exact @GlobalTheory.CompanionTheory.Relay.square_parametrized_density_formula | exact GlobalTheory.CompanionTheory.Relay.square_parametrized_density_formula | (intros; apply GlobalTheory.CompanionTheory.Relay.square_parametrized_density_formula <;> assumption)
end
end

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace SqFubini

def eY (d : ℕ) : ((Fin d → ℂ) × ℂ) ≃ᵐ (Fin (d + 1) → ℂ) :=
  MeasurableEquiv.prodComm.trans (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0).symm

theorem eY_apply {d : ℕ} (x : (Fin d → ℂ) × ℂ) : eY d x = Fin.cons x.2 x.1 := by
  first | rfl | (simp [eY, MeasurableEquiv.prodComm, MeasurableEquiv.piFinSuccAbove, Fin.consEquiv]; done) | (simp [eY, MeasurableEquiv.piFinSuccAbove]; rfl)

theorem eY_measurePreserving (d : ℕ) : MeasurePreserving (eY d) volume volume :=
  (Measure.measurePreserving_swap).trans
    (volume_preserving_piFinSuccAbove (fun _ => ℂ) 0).symm

def eW (d : ℕ) : ((Fin d → ℂ) × (ℂ × ℂ)) ≃ᵐ (Fin (d + 2) → ℂ) :=
  (MeasurableEquiv.prodComm.trans MeasurableEquiv.prodAssoc).trans
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℂ)
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0).symm).trans
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0).symm)

theorem eW_apply {d : ℕ} (x : (Fin d → ℂ) × (ℂ × ℂ)) :
    eW d x = Fin.cons x.2.1 (Fin.cons x.2.2 x.1) := by
  first | rfl | (simp [eW, MeasurableEquiv.prodComm, MeasurableEquiv.prodAssoc, MeasurableEquiv.prodCongr, MeasurableEquiv.piFinSuccAbove, Fin.consEquiv]; done) | (simp [eW, MeasurableEquiv.piFinSuccAbove]; rfl)

theorem eW_measurePreserving (d : ℕ) : MeasurePreserving (eW d) volume volume :=
  ((Measure.measurePreserving_swap).trans (measurePreserving_prodAssoc volume volume volume)).trans
    (((MeasurePreserving.id volume).prod
      (volume_preserving_piFinSuccAbove (fun _ => ℂ) 0).symm).trans
      (volume_preserving_piFinSuccAbove (fun _ => ℂ) 0).symm)

theorem fubini_piece {Y P Z : Type*} [MeasurableSpace Y] [MeasurableSpace P] [MeasurableSpace Z]
    (μ : Measure Y) (ν : Measure P) (ρ : Measure Z) [SFinite μ] [SFinite ν]
    (e : (Y × P) ≃ᵐ Z) (he : MeasurePreserving e (μ.prod ν) ρ) (B : Set Y) (S : Set Z)
    (hS : e ⁻¹' S = B ×ˢ Set.univ) (F : Z → ℝ) (hF : IntegrableOn F S ρ) :
    IntegrableOn (fun y => ∫ p, F (e (y, p)) ∂ν) B μ ∧
      ∫ z in S, F z ∂ρ = ∫ y in B, ∫ p, F (e (y, p)) ∂ν ∂μ := by
  have h1 : IntegrableOn (F ∘ e) (B ×ˢ Set.univ) (μ.prod ν) := by
    rw [← hS]
    exact (he.integrableOn_comp_preimage e.measurableEmbedding).2 hF
  have h2 : ∫ z in S, F z ∂ρ = ∫ x in B ×ˢ Set.univ, F (e x) ∂(μ.prod ν) := by
    rw [← hS]
    exact (he.setIntegral_preimage_emb e.measurableEmbedding F S).symm
  constructor
  · have h3 : Integrable (F ∘ e) ((μ.restrict B).prod (ν.restrict Set.univ)) := by
      rw [Measure.prod_restrict]
      exact h1
    simpa [IntegrableOn, Function.comp_def] using h3.integral_prod_left
  · rw [h2]
    simpa [Function.comp_def] using setIntegral_prod (F ∘ e) h1

theorem fibre_sum {d k : ℕ} (B : Set (Fin d → ℂ)) (F : ℕ → (Fin (d + 2) → ℂ) → ℝ)
    (H : (Fin (d + 1) → ℂ) → ℝ) (κ : ℝ)
    (hF : ∀ i < k, IntegrableOn (F i) {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ B})
    (hH : IntegrableOn H {z : Fin (d + 1) → ℂ | Fin.tail z ∈ B})
    (hpt : ∀ y ∈ B, ∑ i ∈ Finset.range k, ∫ p : ℂ × ℂ, F i (Fin.cons p.1 (Fin.cons p.2 y)) =
      κ * ∫ a : ℂ, H (Fin.cons a y))
    (hB : MeasurableSet B) :
    ∑ i ∈ Finset.range k, ∫ z in {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ B}, F i z =
      κ * ∫ z in {z : Fin (d + 1) → ℂ | Fin.tail z ∈ B}, H z := by
  have hSW : (eW d) ⁻¹' {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ B} = B ×ˢ Set.univ := by
    ext x
    simp [eW_apply]
  have hSY : (eY d) ⁻¹' {z : Fin (d + 1) → ℂ | Fin.tail z ∈ B} = B ×ˢ Set.univ := by
    ext x
    simp [eY_apply]
  have hW := fun i (hi : i < k) => fubini_piece volume volume volume (eW d) (eW_measurePreserving d) B _ hSW
    (F i) (hF i hi)
  have hY := fubini_piece volume volume volume (eY d) (eY_measurePreserving d) B _ hSY H hH
  simp only [eW_apply, eY_apply] at hW hY
  rw [hY.2, Finset.sum_congr rfl fun i hi => (hW i (Finset.mem_range.1 hi)).2,
    ← integral_finsetSum _ fun i hi => (hW i (Finset.mem_range.1 hi)).1, ← integral_const_mul]
  exact setIntegral_congr_fun hB fun y hy => hpt y hy

theorem ae_ne (d : ℕ) : ∀ᵐ z : Fin (d + 2) → ℂ, z 0 ≠ z 1 := by
  let L : (Fin (d + 2) → ℂ) →ₗ[ℝ] ℂ :=
    (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 2) => ℂ) 0) -
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 2) => ℂ) 1)
  have hs : LinearMap.ker L ≠ ⊤ := by
    intro h
    have h1 : (Pi.single 0 1 : Fin (d + 2) → ℂ) ∈ LinearMap.ker L := by rw [h]; trivial
    simp [L, LinearMap.mem_ker, Pi.single_apply] at h1
  have h0 := Measure.addHaar_submodule (volume : Measure (Fin (d + 2) → ℂ)) (LinearMap.ker L) hs
  refine measure_mono_null ?_ h0
  intro z hz
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hz
  simp [L, LinearMap.mem_ker, hz]

theorem isC2At_sumPot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {σ : Type} [Fintype σ]
    (c : σ → ℝ) (P : σ → LocPot X) (x : X) (h : ∀ a, IsTwiceDifferentiableAt A (P a) x) : IsTwiceDifferentiableAt A (sumPot c P) x := by
  intro j hj
  have : (sumPot c P).φ x ∘ (A.chart j).symm =
      fun y => ∑ a, c a * ((P a).φ x ∘ (A.chart j).symm) y := rfl
  rw [this]
  exact ContDiffAt.sum fun a _ => contDiffAt_const.mul (h a j hj)

end SqFubini

namespace SqFubini

def EW {d : ℕ} (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (α : (Fin d → ℂ) → ℝ) (k i : ℕ) :
    Fin (d + 2) → (Fin (d + 2) → ℂ) → ℝ :=
  let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i
  fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z))

def EY {d : ℕ} (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (α : (Fin d → ℂ) → ℝ) (k : ℕ) :
    Fin (d + 1) → (Fin (d + 1) → ℂ) → ℝ :=
  fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)

end SqFubini


open SqFubini in
theorem AnSq.sum_polar_gH_eq : Inputs → GroundTheory.Heights₂.Heights.Inter.FibreLocal.Statement → ∀ (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (a₀ : σ) (ε : σ → ℤ) (Q : AnSq SY a₀ ε) (c : σ → ℝ), c a₀ = 0 → ∀ k : ℕ, 1 ≤ k → 2 * k ≤ d + 2 → ∑ i ∈ Finset.range k, polar (d + 2) (fun w => mInt Q.SW.A (fun r => Q.SW.potH (w r)) Q.gH) (Q.wcoef c k i) = 2 * kappa k * polar (d + 1) SY.degNum (mix (2 * k - 1) (fun a => (ε a : ℝ)) c) := by
  intro hI hF d σ _ SY a₀ ε Q c hc k hk1 hk2
  have hlim := GlobalTheory.T.analytic_square_regularized_convergence hI d σ SY a₀ ε Q
  obtain ⟨-, hnW, hC2W, -, -⟩ := anSys_open_basics (d + 2) (Option σ) Q.SW
  obtain ⟨-, hnY, hC2Y, -, -⟩ := anSys_open_basics (d + 1) σ SY
  have hhom := AnSys.mIntegrable_potH_and_mInt_eq_degNum hI.convergenceSigned (d + 1) σ SY

  have hexW := fun i => mInt_sumPot_expand (d + 2) Q.SW.X Q.SW.A (Option σ) Q.SW.open' Q.SW.potH
    (Q.wcoef c k i) Q.gH hnW hC2W fun w => (hlim w).1
  have hexY := mInt_sumPot_expand (d + 1) SY.X SY.A σ SY.open' SY.potH
    (mix (2 * k - 1) (fun a => (ε a : ℝ)) c) (fun _ => 1) hnY hC2Y fun w => (hhom w).1
  have hpolW : ∀ i, polar (d + 2) (fun w => mInt Q.SW.A (fun r => Q.SW.potH (w r)) Q.gH) (Q.wcoef c k i) =
      mInt Q.SW.A (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) Q.gH := fun i => (hexW i).2.symm
  have hpolY : polar (d + 1) SY.degNum (mix (2 * k - 1) (fun a => (ε a : ℝ)) c) =
      mInt SY.A (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (fun _ => 1) := by
    rw [hexY.2]
    exact Finset.sum_congr rfl fun w _ => by rw [(hhom w).2]

  have hoW : ∀ n (z : Fin (d + 2) → ℂ), Fin.tail (Fin.tail z) ∈ Q.U n → Q.ΦW n z ∈ Q.SW.open' := by
    intro n z hz
    rw [Q.bdry_eq 0, Set.mem_preimage, Q.first_projection_chart_compat n z hz]
    exact Q.ΦY_open n _ (by simpa using hz)

  have hcW := fun i => integrableOn_hasSum_paramCover (d + 2) Q.SW.X Q.SW.A _ _ Q.ΦW
    (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) Q.gH Q.coverW
    (fun n z hz r => isC2At_sumPot _ _ _ _ fun a => hC2W a _ (hoW n z (Q.B_meas n |>.2 hz)))
    (hexW i).1
  have hcY := integrableOn_hasSum_paramCover (d + 1) SY.X SY.A _ _ Q.ΦY
    (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (fun _ => 1) Q.coverY
    (fun n z hz r => isC2At_sumPot _ _ _ _ fun a => hC2Y a _ (Q.ΦY_open n z (Q.B_meas n |>.2 hz)))
    hexY.1

  have key : ∀ n, ∑ i ∈ Finset.range k, ∫ z in {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ Q.B n},
      Q.gH (Q.ΦW n z) * paramDens (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) (Q.ΦW n) z =
      2 * kappa k * ∫ z in {z : Fin (d + 1) → ℂ | Fin.tail z ∈ Q.B n},
        (fun _ => (1 : ℝ)) (Q.ΦY n z) * paramDens
          (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (Q.ΦY n) z := by
    intro n
    let α : (Fin d → ℂ) → ℝ := fun y => ∑ a, c a * Q.α n a y
    have hd := GlobalTheory.T.square_parametrized_density_formula d σ SY a₀ ε Q c hc n k hk1 hk2
    have hmW : MeasurableSet {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ Q.B n} := (Q.coverW.2.1 n).1
    have hmY : MeasurableSet {z : Fin (d + 1) → ℂ | Fin.tail z ∈ Q.B n} := (Q.coverY.2.1 n).1
    let F : ℕ → (Fin (d + 2) → ℂ) → ℝ := fun i z =>
      logSin (Q.G n (Fin.tail (Fin.tail z))) (z 0) (z 1) * maDens (EW (Q.G n) α k i) z
    have hae : ∀ i < k, ∀ᵐ z ∂(volume.restrict {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ Q.B n}),
        Q.gH (Q.ΦW n z) * paramDens (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) (Q.ΦW n) z = F i z := by
      intro i hi
      filter_upwards [ae_restrict_of_ae (ae_ne d), ae_restrict_mem hmW] with z hne hz
      have hU : Fin.tail (Fin.tail z) ∈ Q.U n := (Q.B_meas n).2 hz
      have h1 : Q.gH (Q.ΦW n z) = logSin (Q.G n (Fin.tail (Fin.tail z))) (z 0) (z 1) :=
        Q.norm_hom n z hU hne
      have h2 : paramDens (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) (Q.ΦW n) z =
          maDens (EW (Q.G n) α k i) z := hd.2 i hi z hU
      rw [h1, h2]
    have hH : ∀ z ∈ {z : Fin (d + 1) → ℂ | Fin.tail z ∈ Q.B n},
        (fun _ => (1 : ℝ)) (Q.ΦY n z) * paramDens
          (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (Q.ΦY n) z =
        maDens (EY (Q.G n) α k) z := by
      intro z hz
      have h2 : paramDens (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (Q.ΦY n) z =
          maDens (EY (Q.G n) α k) z := hd.1 z ((Q.B_meas n).2 hz)
      rw [h2, one_mul]
    have hFint : ∀ i < k, IntegrableOn (F i) {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ Q.B n} :=
      fun i hi => ((hcW i).1 n).congr (hae i hi)
    have hHint : IntegrableOn (maDens (EY (Q.G n) α k)) {z : Fin (d + 1) → ℂ | Fin.tail z ∈ Q.B n} :=
      (integrableOn_congr_fun hH hmY).1 (hcY.1 n)
    have hpt : ∀ y ∈ Q.B n, ∑ i ∈ Finset.range k, ∫ p : ℂ × ℂ, F i (Fin.cons p.1 (Fin.cons p.2 y)) =
        (2 * kappa k) * ∫ a : ℂ, maDens (EY (Q.G n) α k) (Fin.cons a y) := by
      intro y hy
      have hyU : y ∈ Q.U n := (Q.B_meas n).2 hy
      have hnh : Q.U n ∈ 𝓝 y := (Q.U_open n).mem_nhds hyU
      have h2 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := ENat.LEInfty.out
      exact GlobalTheory.T.log_sine_monge_ampere_integral hF d k hk1 hk2 (Q.G n) α y
        (by filter_upwards [hnh] with y' hy' using Q.G_pos n y' hy')
        (fun p q => ((Q.G_smooth n p q).contDiffAt hnh).of_le h2)
        (ContDiffAt.sum fun a _ => contDiffAt_const.mul (((Q.α_smooth n a).contDiffAt hnh).of_le h2))
    rw [Finset.sum_congr rfl fun i hi => integral_congr_ae (hae i (Finset.mem_range.1 hi)),
      setIntegral_congr_fun hmY hH]
    exact fibre_sum (Q.B n) F _ _ hFint hHint hpt (Q.B_meas n).1
  have hsW : HasSum (fun n => ∑ i ∈ Finset.range k, ∫ z in {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ Q.B n},
      Q.gH (Q.ΦW n z) * paramDens (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) (Q.ΦW n) z)
      (∑ i ∈ Finset.range k, mInt Q.SW.A (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) Q.gH) :=
    hasSum_sum fun i _ => (hcW i).2
  rw [funext key] at hsW
  rw [Finset.sum_congr rfl fun i _ => hpolW i, hpolY]
  exact hsW.unique (hcY.2.mul_left _)

end GlobalTheory.CompanionTheory.Ar.PB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PolarIdentityFromSymmetricForms
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PolarIdentityFromSymmetricForms
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem coefficient_identities_give_operator_identity : ∀ (σ : Type) [Fintype σ] (D : ℕ) (a : (Fin (D + 1) → σ) → ℝ) (b : (Fin D → σ) → ℝ) (κ : ℕ → ℝ) (ε : σ → ℤ) (a₀ : σ), (∀ (π : Equiv.Perm (Fin (D + 1))) w, a (w ∘ π) = a w) → (∀ (π : Equiv.Perm (Fin D)) w, b (w ∘ π) = b w) → (∀ n : σ → ℤ, n a₀ = 0 → polar (D + 1) a (fun _ x => (n x : ℝ)) = 0 ∧ ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D + 1 → polar (D + 1) a (mix (2 * k) (fun x => (ε x : ℝ)) fun x => (n x : ℝ)) = -(2 * κ k) * polar D b (mix (2 * k - 1) (fun x => (ε x : ℝ)) fun x => (n x : ℝ))) → ∀ (c : σ → ℝ), c a₀ = 0 → ∀ u : ℝ, eval (fun x => c x - u / 2 * ε x) (formPoly (D + 1) a) + eval (fun x => c x + u / 2 * ε x) (formPoly (D + 1) a) = (tsgPoly D κ (linePoly c ε (formPoly D b))).eval u :=
  @PositivityTheory.Xgp.t_thma_alg

end GlobalTheory.CompanionTheory.Ar.PB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PolarIdentityFromSymmetricFormsStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polar_identity_from_symmetric_forms : ∀ (σ : Type) [Fintype σ] (D : ℕ) (a : (Fin (D + 1) → σ) → ℝ) (b : (Fin D → σ) → ℝ) (κ : ℕ → ℝ) (ε : σ → ℤ) (a₀ : σ), (∀ (π : Equiv.Perm (Fin (D + 1))) w, a (w ∘ π) = a w) → (∀ (π : Equiv.Perm (Fin D)) w, b (w ∘ π) = b w) → (∀ n : σ → ℤ, n a₀ = 0 → polar (D + 1) a (fun _ x => (n x : ℝ)) = 0 ∧ ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D + 1 → polar (D + 1) a (mix (2 * k) (fun x => (ε x : ℝ)) fun x => (n x : ℝ)) = -(2 * κ k) * polar D b (mix (2 * k - 1) (fun x => (ε x : ℝ)) fun x => (n x : ℝ))) → ∀ (c : σ → ℝ), c a₀ = 0 → ∀ u : ℝ, eval (fun x => c x - u / 2 * ε x) (formPoly (D + 1) a) + eval (fun x => c x + u / 2 * ε x) (formPoly (D + 1) a) = (tsgPoly D κ (linePoly c ε (formPoly D b))).eval u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.coefficient_identities_give_operator_identity | exact GlobalTheory.CompanionTheory.Ar.PB.coefficient_identities_give_operator_identity | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.coefficient_identities_give_operator_identity <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HeightPolynomialReflectionSum
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem tendsto_polar {σ : Type} [Fintype σ] {n : ℕ} {α : Type} {l : Filter α} {f : α → (Fin n → σ) → ℝ}
    {a : (Fin n → σ) → ℝ} (c : Fin n → σ → ℝ) (h : ∀ w, Tendsto (fun t => f t w) l (𝓝 (a w))) :
    Tendsto (fun t => polar n (f t) c) l (𝓝 (polar n a c)) := by
  unfold polar
  exact tendsto_finsetSum _ fun w _ => (h w).const_mul _

theorem Realis.limNum_perm {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {D : ℕ} {σ : Type}
    {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) {II : IntersectionSystem}
    (hII : IsFullIntersectionSystem II) (hpos : 0 < S.t₀) (π : Equiv.Perm (Fin (D + 1)))
    (w : Fin (D + 1) → σ) : Re.limNum II (w ∘ π) = Re.limNum II w := by
  have hev : (fun t => Re.num II t (w ∘ π)) =ᶠ[𝓝[>] 0] fun t => Re.num II t w := by
    filter_upwards [Ioc_mem_nhdsGT hpos] with t ht
    have h := (hII.1 K ι).1 P (D + 1) (fun j => Re.line (w j) t) π Re.arith
      fun j => Re.line_smooth _ t ht.1 ht.2
    unfold Realis.num
    exact congrArg (· / (Re.deg : ℝ)) h
  unfold Realis.limNum limUnder
  rw [Filter.map_congr hev]

theorem AnSys.degNum_perm {e : ℕ} {σ : Type} (S : AnSys e σ) (π : Equiv.Perm (Fin e)) (w : Fin e → σ) :
    S.degNum (w ∘ π) = S.degNum w :=
  ReciprocityTheory.AnForm.M.mIntSymm S.A (fun j => S.th (w j)) π fun _ => 1

theorem thmA_limit : Inputs → GroundTheory.Heights₂.Heights.Inter.FibreLocal.Statement → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (P : Ideal (MRing ι)) (Re : Realis SY P) (a₀ : σ) (ε : σ → ℤ) (Q : SqSys Re a₀ ε) (c : σ → ℝ), c a₀ = 0 → ∀ u : ℝ, eval (fun x => c x - u / 2 * ε x) (Re.PB II) + eval (fun x => c x + u / 2 * ε x) (Re.PB II) = (tsgPoly (d + 1) kappa (linePoly c ε SY.degPoly)).eval u := by
  intro hI hF II hII K _ ι _ d σ _ SY P Re a₀ ε Q c hc u
  have hpos : 0 < SY.t₀ := (SY.reg a₀).1
  have hposW : 0 < Q.an.SW.t₀ := (Q.an.SW.reg none).1
  obtain ⟨C₃, s₀, -, hAg⟩ := GlobalTheory.T.agreement_positive hI (d + 1) σ SY 0 hpos
  have hlim := (hAg II hII K ι P Re).1
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t ≤ Q.an.SW.t₀ := by
    filter_upwards [Ioc_mem_nhdsGT hposW] with t ht using ⟨ht.1, ht.2⟩
  refine GlobalTheory.T.polar_identity_from_symmetric_forms σ (d + 1) (Re.limNum II) SY.degNum kappa ε a₀ (Re.limNum_perm hII hpos)
    SY.degNum_perm (fun n hn => ?_) c hc u
  have hsq := GlobalTheory.T.square_system_polar_vanishing hI II hII K ι d σ SY P Re a₀ ε Q n hn
  refine ⟨?_, fun k hk hk2 => ?_⟩
  · have h1 := tendsto_polar (fun _ (x : σ) => (n x : ℝ)) hlim
    have h2 : Tendsto (fun t => polar (d + 2) (Re.num II t) fun _ (x : σ) => (n x : ℝ)) (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (hev.mono fun t ht => (hsq t ht.1 ht.2).1.symm)
    exact tendsto_nhds_unique h1 h2
  · have h1 := tendsto_polar (mix (2 * k) (fun a => (ε a : ℝ)) fun a => (n a : ℝ)) hlim
    have h2 : Tendsto (fun t => -∑ i ∈ Finset.range k, polar (d + 2)
          (fun w => mInt Q.an.SW.A (fun r => Q.an.SW.potT (w r) t) (Q.an.gT t))
          (Q.an.wcoef (fun a => (n a : ℝ)) k i)) (𝓝[>] 0)
        (𝓝 (-∑ i ∈ Finset.range k, polar (d + 2)
          (fun w => mInt Q.an.SW.A (fun r => Q.an.SW.potH (w r)) Q.an.gH)
          (Q.an.wcoef (fun a => (n a : ℝ)) k i))) :=
      (tendsto_finsetSum _ fun i _ => tendsto_polar _ fun w =>
        (GlobalTheory.T.analytic_square_regularized_convergence hI d σ SY a₀ ε Q.an w).2).neg
    have h3 := tendsto_nhds_unique (h1.congr' (hev.mono fun t ht => (hsq t ht.1 ht.2).2 k hk hk2)) h2
    let square := Q.an
    let coeff : σ → ℝ := fun a => (n a : ℝ)
    have hcoeff : coeff a₀ = 0 := by simp [coeff, hn]
    have hIntegralIdentity :
        ∑ i ∈ Finset.range k, polar (d + 2)
          (fun w => mInt square.SW.A (fun r => square.SW.potH (w r)) square.gH)
          (square.wcoef coeff k i) =
        2 * kappa k * polar (d + 1) SY.degNum (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff) := by
      have hSquareLim :=
        GlobalTheory.T.analytic_square_regularized_convergence hI d σ SY a₀ ε square
      obtain ⟨-, hnW, hC2W, -, -⟩ := anSys_open_basics (d + 2) (Option σ) square.SW
      obtain ⟨-, hnY, hC2Y, -, -⟩ := anSys_open_basics (d + 1) σ SY
      have hhom (w : Fin (d + 1) → σ) :
          MIntegrable SY.A (fun i => SY.potH (w i)) (fun _ => 1) ∧
            mInt SY.A (fun i => SY.potH (w i)) (fun _ => 1) = SY.degNum w := by
        let : MeasurableSpace SY.X := borel SY.X
        have : BorelSpace SY.X := ⟨rfl⟩
        have hlim := hI.convergenceSigned SY.A SY.Θ SY.L SY.s SY.m SY.W
          SY.potΘ SY.posΘ SY.potL SY.sec SY.snc SY.norm_le
          (fun i => SY.th (w i)) (fun i => SY.ph (w i)) (fun i => SY.phT (w i)) SY.C₅ SY.C SY.t₀
          (fun i => SY.sing (w i)) (fun i => SY.reg (w i)) (fun i => SY.c2 (w i))
          (fun _ => 1) (fun _ _ => 1) 1 (fun _ => continuousOn_const)
          (fun _ y _ => SY.abs_one_le_log_rW y)
          (TendstoUniformlyOn.tendstoLocallyUniformlyOn (by
            refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
            exact Filter.Eventually.of_forall fun _ _ _ => by simpa using hε))
        refine ⟨hlim.1, ?_⟩
        have hDegree : Tendsto (fun t => mInt SY.A (fun i => SY.potT (w i) t) (fun _ => 1))
            (𝓝[>] 0) (𝓝 (SY.degNum w)) :=
          tendsto_const_nhds.congr' (by
            filter_upwards [Ioc_mem_nhdsGT hpos] with t ht
            exact (ReciprocityTheory.AnForm.M.massIndep SY.A (fun i => SY.th (w i))
              (fun i => SY.phT (w i) t) (fun i => (SY.sing (w i)).1)
              (fun i => ((SY.reg (w i)).2.2 t ht.1 ht.2).1)).symm)
        exact tendsto_nhds_unique hlim.2 hDegree

      have hexW := fun i => mInt_sumPot_expand (d + 2) square.SW.X square.SW.A (Option σ) square.SW.open' square.SW.potH
        (square.wcoef coeff k i) square.gH hnW hC2W fun w => (hSquareLim w).1
      have hexY := mInt_sumPot_expand (d + 1) SY.X SY.A σ SY.open' SY.potH
        (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff) (fun _ => 1) hnY hC2Y fun w => (hhom w).1
      have hpolW : ∀ i, polar (d + 2) (fun w => mInt square.SW.A (fun r => square.SW.potH (w r)) square.gH) (square.wcoef coeff k i) =
          mInt square.SW.A (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) square.gH := fun i => (hexW i).2.symm
      have hpolY : polar (d + 1) SY.degNum (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff) =
          mInt SY.A (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff r) SY.potH) (fun _ => 1) := by
        rw [hexY.2]
        exact Finset.sum_congr rfl fun w _ => by rw [(hhom w).2]

      have hoW : ∀ n (z : Fin (d + 2) → ℂ), Fin.tail (Fin.tail z) ∈ square.U n → square.ΦW n z ∈ square.SW.open' := by
        intro n z hz
        rw [square.bdry_eq 0, Set.mem_preimage, square.first_projection_chart_compat n z hz]
        exact square.ΦY_open n _ (by simpa using hz)

      have hcW := fun i => integrableOn_hasSum_paramCover (d + 2) square.SW.X square.SW.A _ _ square.ΦW
        (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) square.gH square.coverW
        (fun n z hz r => SqFubini.isC2At_sumPot _ _ _ _ fun a => hC2W a _ (hoW n z (square.B_meas n |>.2 hz)))
        (hexW i).1
      have hcY := integrableOn_hasSum_paramCover (d + 1) SY.X SY.A _ _ square.ΦY
        (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff r) SY.potH) (fun _ => 1) square.coverY
        (fun n z hz r => SqFubini.isC2At_sumPot _ _ _ _ fun a => hC2Y a _ (square.ΦY_open n z (square.B_meas n |>.2 hz)))
        hexY.1

      have hFibreIntegral : ∀ n, ∑ i ∈ Finset.range k,
          ∫ z in {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ square.B n},
          square.gH (square.ΦW n z) * paramDens (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) (square.ΦW n) z =
          2 * kappa k * ∫ z in {z : Fin (d + 1) → ℂ | Fin.tail z ∈ square.B n},
            (fun _ => (1 : ℝ)) (square.ΦY n z) * paramDens
              (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff r) SY.potH) (square.ΦY n) z := by
        intro n
        let α : (Fin d → ℂ) → ℝ := fun y => ∑ a, coeff a * square.α n a y
        have hd := GlobalTheory.T.square_parametrized_density_formula d σ SY a₀ ε square coeff hcoeff n k hk hk2
        have hmW : MeasurableSet {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ square.B n} := (square.coverW.2.1 n).1
        have hmY : MeasurableSet {z : Fin (d + 1) → ℂ | Fin.tail z ∈ square.B n} := (square.coverY.2.1 n).1
        let F : ℕ → (Fin (d + 2) → ℂ) → ℝ := fun i z =>
          logSin (square.G n (Fin.tail (Fin.tail z))) (z 0) (z 1) * maDens (SqFubini.EW (square.G n) α k i) z
        have hae : ∀ i < k, ∀ᵐ z ∂(volume.restrict {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ square.B n}),
            square.gH (square.ΦW n z) * paramDens (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) (square.ΦW n) z = F i z := by
          intro i hi
          filter_upwards [ae_restrict_of_ae (SqFubini.ae_ne d), ae_restrict_mem hmW] with z hne hz
          have hU : Fin.tail (Fin.tail z) ∈ square.U n := (square.B_meas n).2 hz
          have h1 : square.gH (square.ΦW n z) = logSin (square.G n (Fin.tail (Fin.tail z))) (z 0) (z 1) :=
            square.norm_hom n z hU hne
          have h2 : paramDens (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) (square.ΦW n) z =
              maDens (SqFubini.EW (square.G n) α k i) z := hd.2 i hi z hU
          rw [h1, h2]
        have hH : ∀ z ∈ {z : Fin (d + 1) → ℂ | Fin.tail z ∈ square.B n},
            (fun _ => (1 : ℝ)) (square.ΦY n z) * paramDens
              (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff r) SY.potH) (square.ΦY n) z =
            maDens (SqFubini.EY (square.G n) α k) z := by
          intro z hz
          have h2 : paramDens (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) coeff r) SY.potH) (square.ΦY n) z =
              maDens (SqFubini.EY (square.G n) α k) z := hd.1 z ((square.B_meas n).2 hz)
          rw [h2, one_mul]
        have hFint : ∀ i < k, IntegrableOn (F i) {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ square.B n} :=
          fun i hi => ((hcW i).1 n).congr (hae i hi)
        have hHint : IntegrableOn (maDens (SqFubini.EY (square.G n) α k)) {z : Fin (d + 1) → ℂ | Fin.tail z ∈ square.B n} :=
          (integrableOn_congr_fun hH hmY).1 (hcY.1 n)
        have hpt : ∀ y ∈ square.B n, ∑ i ∈ Finset.range k, ∫ p : ℂ × ℂ, F i (Fin.cons p.1 (Fin.cons p.2 y)) =
            (2 * kappa k) * ∫ a : ℂ, maDens (SqFubini.EY (square.G n) α k) (Fin.cons a y) := by
          intro y hy
          have hyU : y ∈ square.U n := (square.B_meas n).2 hy
          have hnh : square.U n ∈ 𝓝 y := (square.U_open n).mem_nhds hyU
          have h2 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := ENat.LEInfty.out
          exact GlobalTheory.T.log_sine_monge_ampere_integral hF d k hk hk2 (square.G n) α y
            (by filter_upwards [hnh] with y' hy' using square.G_pos n y' hy')
            (fun p q => ((square.G_smooth n p q).contDiffAt hnh).of_le h2)
            (ContDiffAt.sum fun a _ => contDiffAt_const.mul (((square.α_smooth n a).contDiffAt hnh).of_le h2))
        rw [Finset.sum_congr rfl fun i hi => integral_congr_ae (hae i (Finset.mem_range.1 hi)),
          setIntegral_congr_fun hmY hH]
        exact SqFubini.fibre_sum (square.B n) F _ _ hFint hHint hpt (square.B_meas n).1
      have hsW : HasSum (fun n => ∑ i ∈ Finset.range k, ∫ z in {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ square.B n},
          square.gH (square.ΦW n z) * paramDens (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) (square.ΦW n) z)
          (∑ i ∈ Finset.range k, mInt square.SW.A (fun r => sumPot (square.wcoef coeff k i r) square.SW.potH) square.gH) :=
        hasSum_sum fun i _ => (hcW i).2
      rw [funext hFibreIntegral] at hsW
      rw [Finset.sum_congr rfl fun i _ => hpolW i, hpolY]
      exact hsW.unique (hcY.2.mul_left _)
    rw [h3, hIntegralIdentity]
    ring

end GlobalTheory.CompanionTheory.Ar.PB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HeightPolynomialReflectionSumStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_polynomial_reflection_sum : Inputs → GroundTheory.Heights₂.Heights.Inter.FibreLocal.Statement → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (P : Ideal (MRing ι)) (Re : Realis SY P) (a₀ : σ) (ε : σ → ℤ) (Q : SqSys Re a₀ ε) (c : σ → ℝ), c a₀ = 0 → ∀ u : ℝ, eval (fun x => c x - u / 2 * ε x) (Re.PB II) + eval (fun x => c x + u / 2 * ε x) (Re.PB II) = (tsgPoly (d + 1) kappa (linePoly c ε SY.degPoly)).eval u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.thmA_limit | exact GlobalTheory.CompanionTheory.Ar.PB.thmA_limit | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.thmA_limit <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.EtaleAwayOfIsEtaleAtOffSubmonoid
open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem gap_eq_weight_sub_next {Ψ : Type} {N : ℕ} (lam : Ψ × Fin N → ℝ) (p : Ψ × Fin N) :
    gap lam p = lam p - if h : (p.2 : ℕ) + 1 < N then lam (p.1, ⟨(p.2 : ℕ) + 1, h⟩) else 0 := by
  unfold gap gapX
  split_ifs <;> simp

theorem gap_comp_swap {Ψ : Type} [DecidableEq Ψ] {N : ℕ} (τ : Ψ) (a b : Fin N) (hb : (b : ℕ) = a + 1)
    (lam : Ψ × Fin N → ℝ) (p : Ψ × Fin N) :
    gap (lam ∘ Equiv.swap (τ, a) (τ, b)) p = gap lam p + gap lam (τ, a) * (xiCoef τ a p : ℝ) := by
  have hab : (a : ℕ) + 1 < N := hb ▸ b.2
  have hbe : (⟨(a : ℕ) + 1, hab⟩ : Fin N) = b := Fin.ext hb.symm
  have hu : gap lam (τ, a) = lam (τ, a) - lam (τ, b) := by
    rw [gap_eq_weight_sub_next]; simp only [hab, dif_pos, hbe]
  have hsw : ∀ q : Ψ × Fin N, (lam ∘ Equiv.swap (τ, a) (τ, b)) q =
      lam q + (if q.1 = τ then (if (q.2 : ℕ) = a + 1 then 1 else 0) - (if (q.2 : ℕ) = a then 1 else 0) else 0)
        * (lam (τ, a) - lam (τ, b)) := by
    rintro ⟨σ, i⟩
    by_cases h1 : (σ, i) = (τ, a)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
      simp
    by_cases h2 : (σ, i) = (τ, b)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
      simp [hb]
    rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
    by_cases hσ : σ = τ
    · subst hσ
      have e1 : (i : ℕ) ≠ a := fun h => h1 (by rw [Fin.ext h])
      have e2 : (i : ℕ) ≠ a + 1 := fun h => h2 (by rw [Fin.ext (h.trans hb.symm)])
      simp [e1, e2]
    · simp [hσ]
  obtain ⟨σ, i⟩ := p
  rw [hu, gap_eq_weight_sub_next, gap_eq_weight_sub_next]
  simp only [hsw, xiCoef, Fin.ext_iff]
  have hi := i.2
  split_ifs <;> first | omega | (push_cast; ring)

theorem gap_swap_decomp : ∀ (Ψ : Type) [DecidableEq Ψ] (N : ℕ) (τ : Ψ) (a b : Fin N), (b : ℕ) = a + 1 → ∀ lam : Ψ × Fin N → ℝ, let u := gap lam (τ, a); let c := fun p => gap lam p + u / 2 * (xiCoef τ a p : ℝ); c (τ, a) = 0 ∧ (∀ p, gap lam p = c p - u / 2 * (xiCoef τ a p : ℝ)) ∧ ∀ p, gap (lam ∘ Equiv.swap (τ, a) (τ, b)) p = c p + u / 2 * (xiCoef τ a p : ℝ) := by
  intro Ψ _ N τ a b hb lam u c
  refine ⟨?_, fun p => ?_, fun p => ?_⟩
  · simp only [c, u, xiCoef]
    simp
  · simp only [c]; ring
  · rw [gap_comp_swap τ a b hb]
    simp only [c, u]; ring

end GlobalTheory.CompanionTheory.Ar.PB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdjacentSwapHeightPolynomialRelation
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem thmA_swap : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N d : ℕ) (S : AnSys (d + 1) (Ψ × Fin N)) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Re : Realis S P) (τ : Ψ) (a b : Fin N), (b : ℕ) = a + 1 → SqSys Re (τ, a) (xiCoef τ a) → ∀ lam : Ψ × Fin N → ℝ, eval lam (toWt (Re.PB II)) + eval (lam ∘ Equiv.swap (τ, a) (τ, b)) (toWt (Re.PB II)) = (tsgPoly (d + 1) kappa (linePoly (fun p => gap lam p + gap lam (τ, a) / 2 * (xiCoef τ a p : ℝ)) (xiCoef τ a) S.degPoly)).eval (gap lam (τ, a)) := by
  intro hI II hII Ψ _ _ N d S K _ ι _ P Re τ a b hb Q lam
  obtain ⟨h0, h1, h2⟩ := gap_swap_decomp Ψ N τ a b hb lam
  have key := GlobalTheory.T.height_polynomial_reflection_sum hI GroundTheory.Heights₂.Heights.Inter.FibreLocal.proof II hII K ι d (Ψ × Fin N) S P Re (τ, a) (xiCoef τ a) Q
    (fun p => gap lam p + gap lam (τ, a) / 2 * (xiCoef τ a p : ℝ)) h0 (gap lam (τ, a))
  rw [eval_toWt_gap, eval_toWt_gap, ← key]
  exact congrArg₂ (· + ·) (congrArg (fun f => eval f (Re.PB II)) (_root_.funext h1))
    (congrArg (fun f => eval f (Re.PB II)) (_root_.funext h2))

end GlobalTheory.CompanionTheory.Ar.PB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdjacentSwapHeightPolynomialRelationStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjacent_swap_height_polynomial_relation : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N d : ℕ) (S : AnSys (d + 1) (Ψ × Fin N)) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Re : Realis S P) (τ : Ψ) (a b : Fin N), (b : ℕ) = a + 1 → SqSys Re (τ, a) (xiCoef τ a) → ∀ lam : Ψ × Fin N → ℝ, eval lam (toWt (Re.PB II)) + eval (lam ∘ Equiv.swap (τ, a) (τ, b)) (toWt (Re.PB II)) = (tsgPoly (d + 1) kappa (linePoly (fun p => gap lam p + gap lam (τ, a) / 2 * (xiCoef τ a p : ℝ)) (xiCoef τ a) S.degPoly)).eval (gap lam (τ, a)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.thmA_swap | exact GlobalTheory.CompanionTheory.Ar.PB.thmA_swap | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.thmA_swap <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightTransformInjectiveLinear
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightTransformInjectiveLinear
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem tsgPoly_linePoly_smul_toWt_injective :
    (∀ (D : ℕ) (κ : ℕ → ℝ) (v : ℝ) (Q : Polynomial ℝ), tsgPoly D κ (Polynomial.C v * Q) = Polynomial.C v * tsgPoly D κ Q) ∧ (∀ (σ : Type) (c : σ → ℝ) (e : σ → ℤ) (v : ℝ) (Q : MvPolynomial σ ℝ), linePoly c e (C v * Q) = Polynomial.C v * linePoly c e Q) ∧ ∀ (Ψ : Type) (N : ℕ), Function.Injective (toWt : MvPolynomial (Ψ × Fin N) ℝ → MvPolynomial (Ψ × Fin N) ℝ) :=
  PositivityTheory.Xgp.t_tsg_smul

end GlobalTheory.CompanionTheory.Ar.PB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightTransformInjectiveLinearStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_transform_injective_linear : (∀ (D : ℕ) (κ : ℕ → ℝ) (v : ℝ) (Q : Polynomial ℝ), tsgPoly D κ (Polynomial.C v * Q) = Polynomial.C v * tsgPoly D κ Q) ∧ (∀ (σ : Type) (c : σ → ℝ) (e : σ → ℤ) (v : ℝ) (Q : MvPolynomial σ ℝ), linePoly c e (C v * Q) = Polynomial.C v * linePoly c e Q) ∧ ∀ (Ψ : Type) (N : ℕ), Function.Injective (toWt : MvPolynomial (Ψ × Fin N) ℝ → MvPolynomial (Ψ × Fin N) ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.tsgPoly_linePoly_smul_toWt_injective | exact GlobalTheory.CompanionTheory.Ar.PB.tsgPoly_linePoly_smul_toWt_injective | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.tsgPoly_linePoly_smul_toWt_injective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.EtaleLocalizationAtPrimeTensorOfEtaleAway
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open MvPolynomial GroundTheory.Heights₂.Heights

theorem mem_antisymSpace_of_pointwise :
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (R : MvPolynomial (Ψ × Fin N) ℝ),
      R.IsHomogeneous (antisymDegree Ψ N + 1) →
      (∀ (τ : Ψ) (a b : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) →
        ∀ lam : Ψ × Fin N → ℝ, eval lam R + eval (lam ∘ Equiv.swap (τ, a) (τ, b)) R = 0) →
      R ∈ antisymSpace Ψ N j := by
  intro Ψ _ _ N j R hR h
  refine ⟨(mem_homogeneousSubmodule _ _).2 hR, ?_⟩
  rintro σ ⟨τ, a, b, hab, hblock, rfl⟩
  refine MvPolynomial.funext fun lam => ?_
  rw [eval_rename, map_neg]
  exact eq_neg_of_add_eq_zero_right (h τ a b hab hblock lam)

end GlobalTheory.CompanionTheory.Ar.PB
end
end

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB.Top

theorem antisymmetry : Antisymmetry := by
  intro hIn II hII Ψ _ _ _ N j d hN S K _ ι _ P Re hF
  obtain ⟨d₀, S₀, Re₀, hd₀, hdeg₀, href₀, hline₀, ⟨hF₀⟩⟩ := GlobalTheory.T.flag_variety_analytic_system_exists hIn Ψ N hN
  have hdim : d + 1 = antisymDegree Ψ N := hF.dim
  obtain rfl : d = d₀ := by omega
  have hS := ((GlobalTheory.T.proportional' hIn Ψ N j hN hF.j_le).2 (d + 1) S hdim hF.unif).2
  have hpot := GlobalTheory.T.realisation_potential_degree_compatibility hIn.2.1.1 (FlBlock Ψ N) (FlIdx Ψ N) (d + 1) (Ψ × Fin N) S₀ (PFl Ψ N) Re₀
  have harith : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) := by
    rw [← hdim]; exact Re₀.arith
  have hfl := flLines_polys hIn II hII Ψ N hN harith

  have hdeg0 : toWt S₀.degPoly = degFlPoly Ψ N := by
    have h2 := hfl.2
    rw [← hdim] at h2
    rw [h2]
    congr 1
    unfold AnSys.degPoly
    congr 1
    funext w
    have h3 := hpot.2.1 w
    simp only [href₀, hdeg₀, Nat.cast_one, one_mul] at h3
    exact h3.symm

  have hPB0 : toWt (Re₀.PB II) = hFlPoly Ψ N II := by
    have h1 := hfl.1
    rw [← hdim] at h1
    rw [h1]
    congr 1
    unfold Realis.PB
    congr 1
    funext w
    unfold Realis.limNum Realis.num
    simp only [hline₀, hdeg₀, Nat.cast_one, div_one]
    exact tendsto_const_nhds.limUnder_eq

  have hdegS : S.degPoly = C (volOf S) * S₀.degPoly := by
    apply (GlobalTheory.T.weight_transform_injective_linear).2.2 Ψ N
    rw [hS, map_mul, hdeg0]
    congr 1
    simp [toWt, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

  obtain ⟨Cst, hC⟩ := GlobalTheory.T.weighted_polynomial_homogeneous_coeff_bound Ψ N (antisymDegree Ψ N + 1)
  have hhomT : (toWt (Re.PB II)).IsHomogeneous (antisymDegree Ψ N + 1) := by
    refine (hC.1 _ 0 ?_).1
    rw [← hdim]
    exact (formPoly_isHomogeneous_and_eval (Ψ × Fin N) (d + 1 + 1) (Re.limNum II)).1
  have hhomH : (hFlPoly Ψ N II).IsHomogeneous (antisymDegree Ψ N + 1) :=
    (formPoly_isHomogeneous_and_eval (Ψ × Fin N) _ _).1
  have hhom : (toWt (Re.PB II) - volOf S • hFlPoly Ψ N II).IsHomogeneous (antisymDegree Ψ N + 1) := by
    have hm := (homogeneousSubmodule (Ψ × Fin N) ℝ (antisymDegree Ψ N + 1)).sub_mem
      ((mem_homogeneousSubmodule _ _).2 hhomT)
      (Submodule.smul_mem _ (volOf S) ((mem_homogeneousSubmodule _ _).2 hhomH))
    exact (mem_homogeneousSubmodule _ _).1 hm
  refine mem_antisymSpace_of_pointwise Ψ N j _ hhom ?_
  intro τ a b hab hj lam
  have e1 := GlobalTheory.T.adjacent_swap_height_polynomial_relation hIn II hII Ψ N d S K ι P Re τ a b hab (hF.sq τ a b hab hj) lam
  have e0 := GlobalTheory.T.adjacent_swap_height_polynomial_relation hIn II hII Ψ N d S₀ (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) Re₀ τ a b hab
    (hF₀.sq τ a b hab (Or.inl b.isLt)) lam
  rw [hPB0] at e0
  rw [hdegS, (GlobalTheory.T.weight_transform_injective_linear).2.1, (GlobalTheory.T.weight_transform_injective_linear).1, Polynomial.eval_mul, Polynomial.eval_C, ← e0] at e1
  simp only [map_sub, smul_eval]
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.Top
