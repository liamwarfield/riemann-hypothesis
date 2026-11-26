module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicCoefficientsInFrame
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsResolution
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularWeightMonotoneRegularization
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsBaseMetric
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsDimension

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoByTwoMinorGramIdentity
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoByTwoMinorGramIdentity
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem xiCoef_self {Ψ : Type} [DecidableEq Ψ] {N : ℕ} (τ : Ψ) (a i : Fin N) :
    xiCoef τ a (τ, i) = xiCoef () a ((), i) := by
  simp [xiCoef]

theorem xiCoef_ne {Ψ : Type} [DecidableEq Ψ] {N : ℕ} {τ τ' : Ψ} (h : τ' ≠ τ) (a i : Fin N) :
    xiCoef τ a (τ', i) = 0 := by
  simp [xiCoef, h]

theorem xi_sum_potentials : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (τ : Ψ) (a b ca cb : Fin N) (Gf hf : Ψ → Matrix (Fin N) (Fin N) ℂ) (u : Ψ × Fin N → ℝ) (t : ℂ) (G₂ : Matrix (Fin 2) (Fin 2) ℂ), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsBlockDiag j (Gf τ) → (Gf τ).PosDef → IsBlockDiag j (hf τ) → (hf τ).det ≠ 0 → (∀ r s : Fin 2, G₂ r s = minorIJ ((hf τ)ᴴ * Gf τ * hf τ) (insert (![ca, cb] r) ((stepCols N j a).erase ca)) (insert (![ca, cb] s) ((stepCols N j a).erase ca)) / minorIJ ((hf τ)ᴴ * Gf τ * hf τ) ((stepCols N j a).erase ca) ((stepCols N j a).erase ca)) → ∑ p, (xiCoef τ a p : ℝ) * (blockPot j p.2 (Gf p.1) (if p.1 = τ then hf τ * (1 + Matrix.single cb ca t) else hf p.1) - u p) = xiPot G₂ t - ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((if IsProperStep N j i then 0 else Real.log ‖facOf N j a (hf τ) i‖) + u (τ, i)) := by
  intro Ψ _ _ N j τ a b ca cb Gf hf u t G₂ hj hb hcase hca hcb hG hGp hh hdet hG₂
  obtain ⟨G₃, -, e3, key⟩ := norm_three_steps N j a b ca cb (Gf τ) (hf τ) hj hb hcase hca hcb hG hGp hh hdet
  have hGG : G₃ = G₂ := Matrix.ext fun r s => (e3 r s).trans (hG₂ r s).symm
  subst hGG
  have hsum : ∑ p, (xiCoef τ a p : ℝ) * (blockPot j p.2 (Gf p.1) (if p.1 = τ then hf τ * (1 + Matrix.single cb ca t) else hf p.1) - u p) =
      ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * (blockPot j i (Gf τ) (hf τ * (1 + Matrix.single cb ca t)) - u (τ, i)) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
    · simp
    · intro τ' _ hne
      simp [xiCoef_ne hne]
    · simp
  rw [hsum, ← key t, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [xiCoef_self]
  simp only [facOf]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoByTwoMinorGramIdentityStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_by_two_minor_gram_identity : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (τ : Ψ) (a b ca cb : Fin N) (Gf hf : Ψ → Matrix (Fin N) (Fin N) ℂ) (u : Ψ × Fin N → ℝ) (t : ℂ) (G₂ : Matrix (Fin 2) (Fin 2) ℂ), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsBlockDiag j (Gf τ) → (Gf τ).PosDef → IsBlockDiag j (hf τ) → (hf τ).det ≠ 0 → (∀ r s : Fin 2, G₂ r s = minorIJ ((hf τ)ᴴ * Gf τ * hf τ) (insert (![ca, cb] r) ((stepCols N j a).erase ca)) (insert (![ca, cb] s) ((stepCols N j a).erase ca)) / minorIJ ((hf τ)ᴴ * Gf τ * hf τ) ((stepCols N j a).erase ca) ((stepCols N j a).erase ca)) → ∑ p, (xiCoef τ a p : ℝ) * (blockPot j p.2 (Gf p.1) (if p.1 = τ then hf τ * (1 + Matrix.single cb ca t) else hf p.1) - u p) = xiPot G₂ t - ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((if IsProperStep N j i then 0 else Real.log ‖facOf N j a (hf τ) i‖) + u (τ, i)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.xi_sum_potentials | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.xi_sum_potentials | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.xi_sum_potentials <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsLogResolution
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartSeventh
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartSeventh
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem fibre_base_member : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ p, p ≠ (τ, a) → ∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Un → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ((FA.S.comap some).potH p).φ (ΦYn z) (ΦYn z') = alphaOf BM l H bp p (Fin.tail z') + (Hh z').re := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb hb hst hca hcb X q Un Gn ΦYn ΦWn l H bp hU hD p hp z hz
  obtain ⟨Hh, hHh, hev⟩ := GlobalTheory.T.two_point_fibre_chart_fifth K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hst hca hcb X q Un Gn
    ΦYn ΦWn l H bp hU hD p z hz
  refine ⟨Hh, hHh, ?_⟩
  filter_upwards [hev] with z' h
  rw [h]
  congr 1
  unfold alphaOf potAt
  congr 1
  by_cases hτ : p.1 = τ
  · have hpa : p.2 ≠ a := fun e => hp (Prod.ext hτ e)
    have hs := (GlobalTheory.T.elementary_factor_properties N j a b ca cb (z' 0) M.j_le hb hst hca hcb).2.2.2
      (BM.G l p.1 (bp (Fin.tail z'))) (H τ (Fin.tail z')) p.2 hpa
    simp only [flagAt, if_pos hτ]
    rw [hs, hτ]
  · simp only [flagAt, if_neg hτ]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartSeventhStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_point_fibre_chart_seventh : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ p, p ≠ (τ, a) → ∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Un → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ((FA.S.comap some).potH p).φ (ΦYn z) (ΦYn z') = alphaOf BM l H bp p (Fin.tail z') + (Hh z').re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.fibre_base_member | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.fibre_base_member | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.fibre_base_member <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartSixth
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartSixth
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem analyticAt_fin_tail {d : ℕ} (z : Fin (d + 1) → ℂ) :
    AnalyticAt ℂ (Fin.tail : (Fin (d + 1) → ℂ) → Fin d → ℂ) z := by
  have : (Fin.tail : (Fin (d + 1) → ℂ) → Fin d → ℂ) =
      ⇑(ContinuousLinearMap.pi fun i : Fin d =>
        (ContinuousLinearMap.proj i.succ : (Fin (d + 1) → ℂ) →L[ℂ] ℂ)) := by
    funext u i
    rfl
  rw [this]
  exact ContinuousLinearMap.analyticAt _ z

theorem analyticAt_minorIJ {e N : ℕ} (A : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ) (z : Fin e → ℂ)
    (hA : ∀ r s, AnalyticAt ℂ (fun u => A u r s) z) (I J : Finset (Fin N)) :
    AnalyticAt ℂ (fun u => minorIJ (A u) I J) z := by
  unfold minorIJ
  by_cases h : I.card = J.card
  · simp only [h, dite_true, Matrix.det_apply, Matrix.submatrix_apply]
    refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
    simp only [Units.smul_def, zsmul_eq_mul]
    exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => hA _ _)
  · simp only [h, dite_false]
    exact analyticAt_const

theorem analyticAt_facOf {e N : ℕ} (j : ℕ) (a i : Fin N) (A : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ) (z : Fin e → ℂ)
    (hA : ∀ r s, AnalyticAt ℂ (fun u => A u r s) z) :
    AnalyticAt ℂ (fun u => facOf N j a (A u) i) z := by
  unfold facOf
  by_cases h₁ : (i : ℕ) + 1 = j
  · by_cases h₂ : (a : ℕ) < j
    · simp only [h₁, h₂, if_true]
      exact analyticAt_minorIJ A z hA _ _
    · simp only [h₁, h₂, if_true, if_false]
      exact analyticAt_const
  · simp only [h₁, if_false]
    exact analyticAt_minorIJ A z hA _ _

theorem fibre_xi_potential : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Un → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).potH p).φ (ΦYn z) (ΦYn z') = xiPot (Gn (Fin.tail z')) (z' 0) + (Hh z').re := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb hb hab hca hcb X q Un Gn ΦYn ΦWn l H bp hUn hD z hz
  have hD' := hD
  obtain ⟨hH, hbc, hbk, hpt, hG, -, -⟩ := hD'
  choose Hp hPa hPe using fun p => GlobalTheory.T.two_point_fibre_chart_fifth K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hab hca hcb X q Un Gn ΦYn
    ΦWn l H bp hUn hD p z hz
  have htail : ∀ᶠ z' : Fin (d + 1) → ℂ in 𝓝 z, Fin.tail z' ∈ Un :=
    (analyticAt_fin_tail z).continuousAt.preimage_mem_nhds (hUn.mem_nhds hz)
  have hHa : ∀ τ' r s, AnalyticAt ℂ (fun u => H τ' (Fin.tail u) r s) z := fun τ' r s =>
    AnalyticAt.comp (g := fun w => H τ' w r s) (hH τ' r s _ hz) (analyticAt_fin_tail z)
  have hfac : ∀ i : Fin N, ∃ A : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ A z ∧ ∀ᶠ z' in 𝓝 z,
      (if IsProperStep N j i then 0 else Real.log ‖facOf N j a (H τ (Fin.tail z')) i‖) = (A z').re := by
    intro i
    by_cases hp : IsProperStep N j i
    · exact ⟨fun _ => 0, analyticAt_const, Eventually.of_forall fun z' => by simp [hp]⟩
    · obtain ⟨A, hA, hAe⟩ := GlobalTheory.T.log_norm_nonvanishing_analytic_harmonic (d + 1) (fun u => facOf N j a (H τ (Fin.tail u)) i) z
        (analyticAt_facOf j a i (fun u => H τ (Fin.tail u)) z (hHa τ))
        (GlobalTheory.T.step_factor_ne_zero N j a i _ ((hpt _ hz).2 τ).1 ((hpt _ hz).2 τ).2)
      exact ⟨A, hA, hAe.mono fun z' h => by simpa [hp] using h⟩
  have hups : ∀ i : Fin N, ∃ A : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ A z ∧ ∀ᶠ z' in 𝓝 z,
      upsLogAt BM l (τ, i) (bp (Fin.tail z')) = (A z').re := by
    intro i
    by_cases hp : M.blk (τ, i) = none
    · have hO : bp (Fin.tail z) ∈ BM.O l := (hpt _ hz).1.1
      have hreg := ((BM.good l _ hO).2.2 (τ, i) hp).2.1
      have hv := GlobalTheory.T.regular_function_analytic_on_chart (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x ((BM.F l).υ (τ, i)) d n BM.Rb Un bp (Fin.tail z)
        hUn hz hbc hbk hreg
      have hf : AnalyticAt ℂ (fun u => upsVal BM l (τ, i) (bp (Fin.tail u))) z :=
        AnalyticAt.comp (g := fun w => valAt M.x ((BM.F l).υ (τ, i)) (BM.Rb.lift (bp w) (bp w))) hv
          (analyticAt_fin_tail z)
      obtain ⟨A, hA, hAe⟩ := GlobalTheory.T.log_norm_nonvanishing_analytic_harmonic (d + 1) _ z hf
        (GlobalTheory.T.unipotent_value_ne_zero K ι Φ y Ψ N j M n d BM l (τ, i) _ hO hp)
      exact ⟨A, hA, hAe.mono fun z' h => by simpa [upsLogAt, hp] using h⟩
    · exact ⟨fun _ => 0, analyticAt_const, Eventually.of_forall fun z' => by simp [upsLogAt, hp]⟩
  choose Lf hLa hLe using hfac
  choose Uf hUa hUe using hups
  refine ⟨fun u => ∑ p, ((xiCoef τ a p : ℝ) : ℂ) * Hp p u -
    ∑ i, ((xiCoef τ a (τ, i) : ℝ) : ℂ) * (Lf i u + Uf i u), ?_, ?_⟩
  · refine AnalyticAt.sub (Finset.analyticAt_fun_sum _ fun p _ => analyticAt_const.mul (hPa p))
      (Finset.analyticAt_fun_sum _ fun i _ => analyticAt_const.mul ((hLa i).add (hUa i)))
  · filter_upwards [htail, eventually_all.2 hPe, eventually_all.2 hLe, eventually_all.2 hUe] with z' hw h1 h2 h3
    have hs : ∑ p, (xiCoef τ a p : ℝ) * potAt BM l p (bp (Fin.tail z')) (flagAt H τ ca cb (z' 0) (Fin.tail z') p.1) =
        xiPot (Gn (Fin.tail z')) (z' 0) - ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) *
          ((if IsProperStep N j i then 0 else Real.log ‖facOf N j a (H τ (Fin.tail z')) i‖) +
            upsLogAt BM l (τ, i) (bp (Fin.tail z'))) :=
      GlobalTheory.T.two_by_two_minor_gram_identity Ψ N j τ a b ca cb (fun τ' => BM.G l τ' (bp (Fin.tail z'))) (fun τ' => H τ' (Fin.tail z'))
        (fun p => upsLogAt BM l p (bp (Fin.tail z'))) (z' 0) (Gn (Fin.tail z')) M.j_le hb hab hca hcb
        (BM.G_pos l τ _ (hpt _ hw).1).1 (BM.G_pos l τ _ (hpt _ hw).1).2 ((hpt _ hw).2 τ).1 ((hpt _ hw).2 τ).2
        (hG _ hw)
    have e1 : ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).potH p).φ (ΦYn z) (ΦYn z') =
        ∑ p, (xiCoef τ a p : ℝ) * potAt BM l p (bp (Fin.tail z')) (flagAt H τ ca cb (z' 0) (Fin.tail z') p.1) +
          ∑ p, (xiCoef τ a p : ℝ) * (Hp p z').re := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun p _ => by rw [h1 p, mul_add]
    have e3 : ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) *
          ((if IsProperStep N j i then 0 else Real.log ‖facOf N j a (H τ (Fin.tail z')) i‖) +
            upsLogAt BM l (τ, i) (bp (Fin.tail z'))) =
        ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((Lf i z').re + (Uf i z').re) :=
      Finset.sum_congr rfl fun i _ => by rw [h2 i, h3 i]
    rw [e1, hs, e3]
    simp only [Complex.sub_re, Complex.re_sum, Complex.re_ofReal_mul, Complex.add_re]
    ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartSixthStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_point_fibre_chart_sixth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Un → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).potH p).φ (ΦYn z) (ΦYn z') = xiPot (Gn (Fin.tail z')) (z' 0) + (Hh z').re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.fibre_xi_potential | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.fibre_xi_potential | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.fibre_xi_potential <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreTwistedResolution
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineFormula
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.LogSin

theorem hermitian_pair_one_coordinates (G : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℂ) :
    herm2 G ![1, a] ![1, b] =
      G 0 0 + G 0 1 * b + (starRingEnd ℂ) a * G 1 0 + (starRingEnd ℂ) a * G 1 1 * b := by
  simp [herm2, dotProduct, mulVec, Fin.sum_univ_two]
  ring

theorem gram_identity (G : Matrix (Fin 2) (Fin 2) ℂ) (hG : G.IsHermitian) (a₀ a₁ : ℂ) :
    (herm2 G ![1, a₀] ![1, a₀]).re * (herm2 G ![1, a₁] ![1, a₁]).re - ‖herm2 G ![1, a₀] ![1, a₁]‖ ^ 2 =
      G.det.re * ‖a₁ - a₀‖ ^ 2 := by
  have h10 : G 1 0 = (starRingEnd ℂ) (G 0 1) := (hG.apply 1 0).symm
  have h00 : (G 0 0).im = 0 := Complex.conj_eq_iff_im.mp (hG.apply 0 0)
  have h11 : (G 1 1).im = 0 := Complex.conj_eq_iff_im.mp (hG.apply 1 1)
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, Matrix.det_fin_two,
    hermitian_pair_one_coordinates, hermitian_pair_one_coordinates, hermitian_pair_one_coordinates, h10]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, h00, h11]
  ring

theorem hermitian_pair_one_re_pos (G : Matrix (Fin 2) (Fin 2) ℂ) (hG : G.PosDef) (a : ℂ) :
    0 < (herm2 G ![1, a] ![1, a]).re := by
  have hne : (![1, a] : Fin 2 → ℂ) ≠ 0 := fun h => by simpa using congrFun h 0
  have h := hG.dotProduct_mulVec_pos hne
  exact (Complex.lt_def.mp h).1

theorem det_re_pos (G : Matrix (Fin 2) (Fin 2) ℂ) (hG : G.PosDef) : 0 < G.det.re :=
  (Complex.lt_def.mp hG.det_pos).1

theorem logSin_eq_log_add_xiPot (G : Matrix (Fin 2) (Fin 2) ℂ) (a₀ a₁ : ℂ) (hG : G.PosDef) (hne : a₀ ≠ a₁) :
    logSin G a₀ a₁ = Real.log ‖a₁ - a₀‖ + (1 / 2) * (xiPot G a₀ + xiPot G a₁) := by
  have hA := hermitian_pair_one_re_pos G hG a₀
  have hB := hermitian_pair_one_re_pos G hG a₁
  have hD := det_re_pos G hG
  have hn : 0 < ‖a₁ - a₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  have hid := gram_identity G hG.1 a₀ a₁
  unfold logSin xiPot
  set A := (herm2 G ![1, a₀] ![1, a₀]).re
  set B := (herm2 G ![1, a₁] ![1, a₁]).re
  set C := ‖herm2 G ![1, a₀] ![1, a₁]‖
  set D := G.det.re
  set n := ‖a₁ - a₀‖
  have harg : 1 - C ^ 2 / (A * B) = D * n ^ 2 / (A * B) := by
    rw [← hid]
    field_simp
  rw [harg, Real.log_div (by positivity) (by positivity), Real.log_mul hD.ne' (by positivity),
    Real.log_mul hA.ne' hB.ne', Real.log_pow]
  push_cast
  ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.LogSin
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineFormulaStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_sine_formula : ∀ (G : Matrix (Fin 2) (Fin 2) ℂ) (a₀ a₁ : ℂ), G.PosDef → a₀ ≠ a₁ → logSin G a₀ a₁ = Real.log ‖a₁ - a₀‖ + (1 / 2) * (xiPot G a₀ + xiPot G a₁) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.LogSin.logSin_eq_log_add_xiPot | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.LogSin.logSin_eq_log_add_xiPot | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.LogSin.logSin_eq_log_add_xiPot <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormProductFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormProductFormula
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem log_norm_mul_prod_ite_zpow (N : ℕ) (P : Fin N → Prop) (t : ℂ) (v f : Fin N → ℂ)
    (e : Fin N → ℤ) (ht : t ≠ 0) (h : ∀ i, ¬ P i → v i ≠ 0 ∧ f i ≠ 0) :
    Real.log ‖t * ∏ i : Fin N, (if P i then 1 else v i * f i) ^ e i‖ =
      Real.log ‖t‖ + ∑ i : Fin N, (e i : ℝ) *
        (if P i then 0 else Real.log ‖v i‖ + Real.log ‖f i‖) := by
  have hne : ∀ i, (if P i then (1 : ℂ) else v i * f i) ≠ 0 := by
    intro i
    split_ifs with hp
    · exact one_ne_zero
    · exact mul_ne_zero (h i hp).1 (h i hp).2
  have hfac : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      ‖(if P i then (1 : ℂ) else v i * f i) ^ e i‖ ≠ 0 :=
    fun i _ => norm_ne_zero_iff.mpr (zpow_ne_zero _ (hne i))
  have hprod : ∏ i : Fin N, ‖(if P i then (1 : ℂ) else v i * f i) ^ e i‖ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hfac
  rw [norm_mul, norm_prod, Real.log_mul (norm_ne_zero_iff.mpr ht) hprod, Real.log_prod hfac]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_zpow, Real.log_zpow]
  split_ifs with hp
  · simp
  · rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (h i hp).1)
      (norm_ne_zero_iff.mpr (h i hp).2)]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormProductFormulaStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_norm_product_formula : ∀ (N : ℕ) (P : Fin N → Prop) (t : ℂ) (v f : Fin N → ℂ) (e : Fin N → ℤ), t ≠ 0 → (∀ i, ¬ P i → v i ≠ 0 ∧ f i ≠ 0) → Real.log ‖t * ∏ i : Fin N, (if P i then 1 else v i * f i) ^ e i‖ = Real.log ‖t‖ + ∑ i : Fin N, (e i : ℝ) * (if P i then 0 else Real.log ‖v i‖ + Real.log ‖f i‖) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_norm_mul_prod_ite_zpow | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_norm_mul_prod_ite_zpow | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_norm_mul_prod_ite_zpow <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreTwistedResolution
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.NormFib

theorem shear_mul {N : ℕ} {ca cb : Fin N} (hne : ca ≠ cb) (s t : ℂ) :
    (1 + Matrix.single cb ca s : Matrix (Fin N) (Fin N) ℂ) * (1 + Matrix.single cb ca t) =
      1 + Matrix.single cb ca (s + t) := by
  rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, Matrix.single_mul_single_of_ne _ _ _ _ hne,
    Matrix.single_add]
  abel

theorem logNorm_add_weights_eq_logSin : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (k₀ : K), M.blk (τ, a) = some k₀ → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → ∀ f : RW.X → ℝ, IsNormFn M τ a k₀ ca cb RW f → ∀ (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → RW.X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Un → z 0 ≠ z 1 → f (ΦWn z) + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).ph p (q 0 (ΦWn z)) + (FA.S.comap some).ph p (q 1 (ΦWn z))) = logSin (Gn (Fin.tail (Fin.tail z))) (z 0) (z 1) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb hb hstep hca hcb k₀ hk₀ RW q h0 h1 f hf Un Gn ΦYn ΦWn l H bp hUn hD z hz hne
  have hPos := GlobalTheory.T.two_point_fibre_chart_second K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hstep hca hcb RW.X q Un Gn ΦYn ΦWn l H bp hUn hD _ hz
  obtain ⟨-, -, -, hbase, hG, hex, hq⟩ := hD
  have hπ := GlobalTheory.T.realisation_bijective_degree_one K ι (d + 1) _ FA.S (mCoordIdeal y) FA.Re FA.deg_one FA.br_empty
  obtain ⟨hq0, hq1⟩ := hq z hz
  generalize hw : Fin.tail (Fin.tail z) = w at hz hPos hq0 ⊢
  obtain ⟨hbO, hH⟩ := hbase w hz
  have hcab : ca ≠ cb := fun e => by
    have : (ca : ℕ) = cb := congrArg Fin.val e
    omega
  have shear := fun s : ℂ => GlobalTheory.T.elementary_factor_properties N j a b ca cb s M.j_le hb hstep hca hcb
  have hflag : ∀ (s : ℂ) (τ' : Ψ), IsBlockDiag j (flagAt H τ ca cb s w τ') ∧ (flagAt H τ ca cb s w τ').det ≠ 0 := by
    intro s τ'
    unfold flagAt
    split_ifs with e
    · refine ⟨(hH τ).1.mul (shear s).1, ?_⟩
      rw [Matrix.det_mul, (shear s).2.1, mul_one]
      exact (hH τ).2
    · exact hH τ'
  obtain ⟨x₀, hx₀⟩ := hπ.2 (q 0 (ΦWn z))
  obtain ⟨x₁, hx₁⟩ := hπ.2 (q 1 (ΦWn z))
  have t0 : Fin.tail (Fin.cons (z 0) w : Fin (d + 1) → ℂ) = w := Fin.tail_cons _ _
  obtain ⟨z₀, o0, b0, ex0⟩ := hex (Fin.cons (z 0) w) (by rw [t0]; exact hz) x₀ (hx₀.trans hq0)
  obtain ⟨z₁, o1, b1, ex1⟩ := hex (Fin.tail z) (by rw [hw]; exact hz) x₁ (hx₁.trans hq1)
  rw [t0] at b0 ex0
  rw [hw] at b1 ex1
  have c0 : (Fin.cons (z 0) w : Fin (d + 1) → ℂ) 0 = z 0 := rfl
  have c1 : (Fin.tail z : Fin (d + 1) → ℂ) 0 = z 1 := rfl
  rw [c0] at ex0
  rw [c1] at ex1

  have L0 : ∀ p, Real.log ((fsHerm ι (M.dy p)).h z₀) + FA.S.ph (some p) (q 0 (ΦWn z)) =
      potAt BM l p (bp w) (flagAt H τ ca cb (z 0) w p.1) := fun p => by
    rw [← hx₀]
    exact GlobalTheory.T.flag_analytic_orbit_off_boundary K ι Φ y Ψ N j M n d BM FA l x₀ z₀ (bp w) p _ hbO o0 b0 (ex0 p.1 p.2) (hflag _ _).1 (hflag _ _).2
  have L1 : ∀ p, Real.log ((fsHerm ι (M.dy p)).h z₁) + FA.S.ph (some p) (q 1 (ΦWn z)) =
      potAt BM l p (bp w) (flagAt H τ ca cb (z 1) w p.1) := fun p => by
    rw [← hx₁]
    exact GlobalTheory.T.flag_analytic_orbit_off_boundary K ι Φ y Ψ N j M n d BM FA l x₁ z₁ (bp w) p _ hbO o1 b1 (ex1 p.1 p.2) (hflag _ _).1 (hflag _ _).2

  have S : ∀ s : ℂ, ∑ p, (xiCoef τ a p : ℝ) * potAt BM l p (bp w) (flagAt H τ ca cb s w p.1) =
      xiPot (Gn w) s - ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((if IsProperStep N j i then 0 else
        Real.log ‖facOf N j a (H τ w) i‖) + upsLogAt BM l (τ, i) (bp w)) := fun s =>
    GlobalTheory.T.two_by_two_minor_gram_identity Ψ N j τ a b ca cb (fun τ' => BM.G l τ' (bp w)) (fun τ' => H τ' w)
      (fun p => upsLogAt BM l p (bp w)) s (Gn w) M.j_le hb hstep hca hcb (BM.G_pos l τ _ hbO).1
      (BM.G_pos l τ _ hbO).2 (hH τ).1 (hH τ).2 (hG w hz)

  have ht : z 1 - z 0 ≠ 0 := sub_ne_zero.2 fun e => hne e.symm
  have hz0 : ∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) (BM.F l) (τ, i) z₀ (H τ w * (1 + Matrix.single cb ca (z 0))) := fun i => by
    have := ex0 τ i
    rwa [flagAt, if_pos rfl] at this
  have hz1 : ∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) (BM.F l) (τ, i) z₁ (H τ w * (1 + Matrix.single cb ca (z 0)) *
      (1 + Matrix.single cb ca (z 1 - z 0))) := fun i => by
    have := ex1 τ i
    rwa [flagAt, if_pos rfl, show z 1 = z 0 + (z 1 - z 0) by ring, ← shear_mul hcab, ← Matrix.mul_assoc] at this
  have hgood : M.GoodAt (BM.F l) (mCoordIdeal (basePart M.blk z₀)) := by
    rw [CovMap.mCoordIdeal_eq_of_sameOrbit b0]
    exact BM.good l _ hbO.1
  have hfx := hf (ΦWn z) z₀ z₁ (BM.F l) (H τ w * (1 + Matrix.single cb ca (z 0))) (z 1 - z 0) (BM.isFrame l) hgood
    (orbit_trans (orbit_symm o0) (h0 _ x₀ hx₀)) (orbit_trans (orbit_symm o1) (h1 _ x₁ hx₁))
    ((hH τ).1.mul (shear _).1) (by rw [Matrix.det_mul, (shear _).2.1, mul_one]; exact (hH τ).2) ht hz0 hz1

  have hval : ∀ i, ¬ IsProperStep N j i → valAt M.x ((BM.F l).υ (τ, i)) (basePart M.blk z₀) = upsVal BM l (τ, i) (bp w) := by
    intro i _
    exact (GlobalTheory.T.value_constant_on_orbit _ _ M.Ω M.x _ _ _ (BM.Rb.mem _ _ (BM.Rb.mem_U _)) (orbit_symm b0)).symm
  have hfac : ∀ i, facOf N j a (H τ w * (1 + Matrix.single cb ca (z 0))) i = facOf N j a (H τ w) i :=
    (shear (z 0)).2.2.1 (H τ w)
  have hlog := GlobalTheory.T.log_norm_product_formula N (IsProperStep N j) (z 1 - z 0)
    (fun i => valAt M.x ((BM.F l).υ (τ, i)) (basePart M.blk z₀))
    (fun i => facOf N j a (H τ w * (1 + Matrix.single cb ca (z 0))) i) (fun i => xiCoef τ a (τ, i)) ht
    (fun i hi => by
      refine ⟨?_, GlobalTheory.T.step_factor_ne_zero N j a i _ ((hH τ).1.mul (shear _).1)
        (by rw [Matrix.det_mul, (shear _).2.1, mul_one]; exact (hH τ).2)⟩
      rw [hval i hi]
      exact GlobalTheory.T.unipotent_value_ne_zero K ι Φ y Ψ N j M n d BM l (τ, i) (bp w) hbO.1 ((M.blk_none _).2 hi))
  have hC : ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * (if IsProperStep N j i then 0 else
        Real.log ‖valAt M.x ((BM.F l).υ (τ, i)) (basePart M.blk z₀)‖ +
          Real.log ‖facOf N j a (H τ w * (1 + Matrix.single cb ca (z 0))) i‖) =
      ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((if IsProperStep N j i then 0 else
        Real.log ‖facOf N j a (H τ w) i‖) + upsLogAt BM l (τ, i) (bp w)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    by_cases hp : IsProperStep N j i
    · have hn : M.blk (τ, i) ≠ none := fun e => (M.blk_none _).1 e hp
      simp [hp, upsLogAt, hn]
    · have hn : M.blk (τ, i) = none := (M.blk_none _).2 hp
      simp only [hp, if_false, upsLogAt, hn, if_true, hval i hp, hfac i]
      ring
  have hsin := GlobalTheory.T.log_sine_formula (Gn w) (z 0) (z 1) hPos hne
  have hL : normRhs M τ a (BM.F l) z₀ z₁ (H τ w * (1 + Matrix.single cb ca (z 0))) (z 1 - z 0) -
      (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) + Real.log ((fsHerm ι (M.dy p)).h z₁)) =
      Real.log ‖z 1 - z 0‖ + ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * (if IsProperStep N j i then 0 else
        Real.log ‖valAt M.x ((BM.F l).υ (τ, i)) (basePart M.blk z₀)‖ +
          Real.log ‖facOf N j a (H τ w * (1 + Matrix.single cb ca (z 0))) i‖) := by
    unfold normRhs
    rw [add_sub_cancel_right]
    exact hlog
  have T : ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).ph p (q 0 (ΦWn z)) + (FA.S.comap some).ph p (q 1 (ΦWn z))) +
      ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) + Real.log ((fsHerm ι (M.dy p)).h z₁)) =
      (xiPot (Gn w) (z 0) - ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((if IsProperStep N j i then 0 else
        Real.log ‖facOf N j a (H τ w) i‖) + upsLogAt BM l (τ, i) (bp w))) +
      (xiPot (Gn w) (z 1) - ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((if IsProperStep N j i then 0 else
        Real.log ‖facOf N j a (H τ w) i‖) + upsLogAt BM l (τ, i) (bp w))) := by
    rw [← S (z 0), ← S (z 1), ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    have e0 : (FA.S.comap some).ph p (q 0 (ΦWn z)) = FA.S.ph (some p) (q 0 (ΦWn z)) := rfl
    have e1 : (FA.S.comap some).ph p (q 1 (ΦWn z)) = FA.S.ph (some p) (q 1 (ΦWn z)) := rfl
    rw [e0, e1, ← L0 p, ← L1 p]
    ring
  rw [hfx, hsin]
  rw [hC] at hL
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.NormFib
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreTwistedResolutionStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_point_fibre_twisted_resolution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (k₀ : K), M.blk (τ, a) = some k₀ → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → ∀ f : RW.X → ℝ, IsNormFn M τ a k₀ ca cb RW f → ∀ (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → RW.X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Un → z 0 ≠ z 1 → f (ΦWn z) + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).ph p (q 0 (ΦWn z)) + (FA.S.comap some).ph p (q 1 (ΦWn z))) = logSin (Gn (Fin.tail (Fin.tail z))) (z 0) (z 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.NormFib.logNorm_add_weights_eq_logSin | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.NormFib.logNorm_add_weights_eq_logSin | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.NormFib.logNorm_add_weights_eq_logSin <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartFourth
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartFourth
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem contDiffOn_alphaOf : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ p, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (alphaOf BM l H bp p) Un := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb hab hj hca hcb X q Un Gn ΦYn ΦWn l H bp hUn hF p
  obtain ⟨hH, hbpc, hchart, hpt, -⟩ := hF
  intro w hw
  have hbw : bp w ∈ BM.O l \ ReciprocityTheory.AnForm.P.bdry BM.s := (hpt w hw).1
  have hA : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u => GlobalTheory.CompanionTheory.Ar.PB.blockPot j p.2 (BM.G l p.1 (bp u)) (H p.1 u)) w := by
    refine GlobalTheory.CompanionTheory.Ar.PB.CWeight.contDiffAt_blockPot j p.2 ?_ ?_ ?_ ?_
    · intro r s
      exact (GlobalTheory.T.base_chart_flag_analytic_map K ι Φ y Ψ N j M n d BM l p.1 Un bp hUn hbpc hchart
        (fun w' hw' => (hpt w' hw').1) r s).contDiffAt (hUn.mem_nhds hw)
    · intro r s
      exact (hH p.1 r s w hw).contDiffAt.restrict_scalars ℝ
    · exact (BM.G_pos l p.1 (bp w) hbw).2
    · exact ((hpt w hw).2 p.1).2
  have hB : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u => GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt BM l p (bp u)) w := by
    by_cases hb : M.blk p = none
    · have hreg := ((BM.good l (bp w) hbw.1).2.2 p hb).2.1
      have han := GlobalTheory.T.regular_function_analytic_on_chart _ _ _ M.x ((BM.F l).υ p) d n BM.Rb Un bp w hUn hw hbpc hchart hreg
      have hne : GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsVal BM l p (bp w) ≠ 0 :=
        GlobalTheory.T.unipotent_value_ne_zero K ι Φ y Ψ N j M n d BM l p (bp w) hbw.1 hb
      obtain ⟨Hh, hHh, hev⟩ := GlobalTheory.T.log_norm_nonvanishing_analytic_harmonic d _ w han hne
      have hre0 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Complex.reCLM (Hh z)) w :=
        Complex.reCLM.contDiff.contDiffAt.comp w (hHh.contDiffAt.restrict_scalars ℝ)
      have hre : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (Hh z).re) w := by
        simpa using hre0
      refine hre.congr_of_eventuallyEq ?_
      filter_upwards [hev] with z hz
      show GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt BM l p (bp z) = (Hh z).re
      unfold GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt
      rw [if_pos hb]
      exact hz
    · have hz : (fun u => GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt BM l p (bp u)) = fun _ => (0 : ℝ) := by
        funext u
        unfold GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt
        rw [if_neg hb]
      rw [hz]
      exact contDiffAt_const
  have he : GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.alphaOf BM l H bp p = fun u =>
      GlobalTheory.CompanionTheory.Ar.PB.blockPot j p.2 (BM.G l p.1 (bp u)) (H p.1 u) -
        GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.upsLogAt BM l p (bp u) := rfl
  rw [he]
  exact (hA.sub hB).contDiffWithinAt

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartFourthStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_point_fibre_chart_fourth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ p, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (alphaOf BM l H bp p) Un := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.contDiffOn_alphaOf | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.contDiffOn_alphaOf | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.contDiffOn_alphaOf <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartThird
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartThird
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.GramPlane

theorem contDiffOn_conj_mul_mul {e N : ℕ} {Un : Set (Fin e → ℂ)} (hUn : IsOpen Un) (A G : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (hA : ∀ r s, AnalyticOnNhd ℂ (fun w => A w r s) Un)
    (hG : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => G w r s) Un) (r s : Fin N) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => ((A w)ᴴ * G w * A w) r s) Un := by
  have hA' : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => A w r s) Un := fun r s =>
    ((hA r s).contDiffOn hUn.uniqueDiffOn).restrict_scalars ℝ
  have hAc : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => star (A w r s)) Un := fun r s => by
    first
      | exact ContDiffOn.star (hA' r s)
      | exact (Complex.conjCLE.contDiff.comp_contDiffOn (hA' r s))
      | (have h := Complex.conjCLE.contDiff.comp_contDiffOn (hA' r s)
         simpa [Function.comp_def] using h)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine ContDiffOn.sum fun k _ => ?_
  refine ContDiffOn.mul ?_ (hA' k s)
  refine ContDiffOn.sum fun i _ => ?_
  exact (hAc i r).mul (hG i k)

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.GramPlane

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem contDiffOn_gram_plane : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => Gn w r s) Un := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb _ _ _ _ X q Un Gn ΦYn ΦWn l H bp hUn hF r s
  obtain ⟨hH, hbp, hch, hO, hGn, -, -⟩ := hF
  have hGs : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => BM.G l τ (bp w) r s) Un :=
    GlobalTheory.T.base_chart_flag_analytic_map K ι Φ y Ψ N j M n d BM l τ Un bp hUn hbp hch (fun w hw => (hO w hw).1)
  have hMs : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w) r s) Un :=
    GramPlane.contDiffOn_conj_mul_mul hUn (H τ) (fun w => BM.G l τ (bp w)) (hH τ) hGs
  have hnum := MinorSmooth.contDiffOn_minorIJ N d Un (fun w => (H τ w)ᴴ * BM.G l τ (bp w) * H τ w)
    (insert (![ca, cb] r) ((stepCols N j a).erase ca)) (insert (![ca, cb] s) ((stepCols N j a).erase ca)) hMs
  have hden := MinorSmooth.contDiffOn_minorIJ N d Un (fun w => (H τ w)ᴴ * BM.G l τ (bp w) * H τ w)
    ((stepCols N j a).erase ca) ((stepCols N j a).erase ca) hMs
  have hne : ∀ w ∈ Un, minorIJ ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w)
      ((stepCols N j a).erase ca) ((stepCols N j a).erase ca) ≠ 0 := by
    intro w hw
    have hGp := (BM.G_pos l τ (bp w) (hO w hw).1).2
    have hdet := ((hO w hw).2 τ).2
    have hinj : Function.Injective (H τ w).mulVec := by
      rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.mpr hdet
    exact (SchurCalc.minor_pos (hGp.conjTranspose_mul_mul_same hinj) _).ne'
  have hq := hnum.mul (hden.inv hne)
  refine hq.congr fun w hw => ?_
  have e := hGn w hw r s
  clear * - e
  simp only [e, div_eq_mul_inv, Pi.inv_apply]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartThirdStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_point_fibre_chart_third : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => Gn w r s) Un := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.contDiffOn_gram_plane | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.contDiffOn_gram_plane | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.contDiffOn_gram_plane <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsLogResolution
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

theorem GlobalTheory.CompanionTheory.Ar.PB.WSq.fibre_potentials : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → ∀ (L' : LocPot RW.X) (v : RW.X → RW.X → ℂ) (cst : ℝ), IsNormFn M τ a k₀ ca cb RW (fun x => logNormSec L' v x + cst) → ∀ (U : ℕ → Set (Fin d → ℂ)) (G : ℕ → (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦY : ℕ → (Fin (d + 1) → ℂ) → FA.S.X) (ΦW : ℕ → (Fin (d + 2) → ℂ) → RW.X), (∀ m, IsOpen (U m)) → (∀ m, IsFibreChart FA τ a ca cb q (U m) (G m) (ΦY m) (ΦW m)) → ∃ α : ℕ → Ψ × Fin N → (Fin d → ℂ) → ℝ, (∀ m, ∀ w ∈ U m, (G m w).PosDef) ∧ (∀ m r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => G m w r s) (U m)) ∧ (∀ m p, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (α m p) (U m)) ∧ (∀ m (z : Fin (d + 1) → ℂ), Fin.tail z ∈ U m → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).potH p).φ (ΦY m z) (ΦY m z') = xiPot (G m (Fin.tail z')) (z' 0) + (Hh z').re) ∧ (∀ m p, p ≠ (τ, a) → ∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ U m → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ((FA.S.comap some).potH p).φ (ΦY m z) (ΦY m z') = α m p (Fin.tail z') + (Hh z').re) ∧ ∀ m (z : Fin (d + 2) → ℂ), Fin.tail (Fin.tail z) ∈ U m → z 0 ≠ z 1 → logNormSec L' v (ΦW m z) + cst + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).ph p (q 0 (ΦW m z)) + (FA.S.comap some).ph p (q 1 (ΦW m z))) = logSin (G m (Fin.tail (Fin.tail z))) (z 0) (z 1) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hb hcase hblk hca hcb RW q hq h0 h1 L' v cst hnorm U G ΦY ΦW hU hC
  have hC' := fun m => (isFibreChart_iff FA τ a ca cb q (U m) (G m) (ΦY m) (ΦW m)).1 (hC m)
  choose l H bp hD using hC'
  refine ⟨fun m => alphaOf BM (l m) (H m) (bp m), fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_⟩
  · exact GlobalTheory.T.two_point_fibre_chart_second K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact GlobalTheory.T.two_point_fibre_chart_third K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact GlobalTheory.T.two_point_fibre_chart_fourth K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact GlobalTheory.T.two_point_fibre_chart_sixth K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact GlobalTheory.T.two_point_fibre_chart_seventh K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb _ q (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
  · exact GlobalTheory.T.two_point_fibre_twisted_resolution K ι Φ y Ψ N j M n d BM FA τ a b ca cb hb hcase hca hcb k₀ hblk RW q h0 h1 _ hnorm (U m) (G m) (ΦY m) (ΦW m) (l m) (H m) (bp m) (hU m) (hD m)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsLogResolutionStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_rows_log_resolution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → ∀ (L' : LocPot RW.X) (v : RW.X → RW.X → ℂ) (cst : ℝ), IsNormFn M τ a k₀ ca cb RW (fun x => logNormSec L' v x + cst) → ∀ (U : ℕ → Set (Fin d → ℂ)) (G : ℕ → (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦY : ℕ → (Fin (d + 1) → ℂ) → FA.S.X) (ΦW : ℕ → (Fin (d + 2) → ℂ) → RW.X), (∀ m, IsOpen (U m)) → (∀ m, IsFibreChart FA τ a ca cb q (U m) (G m) (ΦY m) (ΦW m)) → ∃ α : ℕ → Ψ × Fin N → (Fin d → ℂ) → ℝ, (∀ m, ∀ w ∈ U m, (G m w).PosDef) ∧ (∀ m r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => G m w r s) (U m)) ∧ (∀ m p, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (α m p) (U m)) ∧ (∀ m (z : Fin (d + 1) → ℂ), Fin.tail z ∈ U m → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).potH p).φ (ΦY m z) (ΦY m z') = xiPot (G m (Fin.tail z')) (z' 0) + (Hh z').re) ∧ (∀ m p, p ≠ (τ, a) → ∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ U m → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ((FA.S.comap some).potH p).φ (ΦY m z) (ΦY m z') = α m p (Fin.tail z') + (Hh z').re) ∧ ∀ m (z : Fin (d + 2) → ℂ), Fin.tail (Fin.tail z) ∈ U m → z 0 ≠ z 1 → logNormSec L' v (ΦW m z) + cst + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * ((FA.S.comap some).ph p (q 0 (ΦW m z)) + (FA.S.comap some).ph p (q 1 (ΦW m z))) = logSin (G m (Fin.tail (Fin.tail z))) (z 0) (z 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.fibre_potentials | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.fibre_potentials | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.fibre_potentials <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoMapPullbackEnergy
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoMapPullbackEnergy
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.SysPull

theorem finite_bound {ι : Type} [Finite ι] (f : ι → ℝ) : ∃ M : ℝ, ∀ a, f a ≤ M := by
  obtain ⟨M, hM⟩ := (Set.finite_range f).bddAbove
  exact ⟨M, fun a => hM ⟨a, rfl⟩⟩

theorem finite_scale {ι : Type} [Finite ι] (f : ι → ℝ) (hf : ∀ a, 0 < f a) : ∃ t : ℝ, 0 < t ∧ ∀ a, t ≤ f a := by
  obtain ⟨M, hM⟩ := finite_bound fun a => (f a)⁻¹
  by_cases he : Nonempty ι
  · obtain ⟨a₀⟩ := he
    have hM0 : 0 < M := lt_of_lt_of_le (inv_pos.2 (hf a₀)) (hM a₀)
    exact ⟨M⁻¹, inv_pos.2 hM0, fun a => inv_le_of_inv_le₀ (hf a) (hM a)⟩
  · exact ⟨1, one_pos, fun a => absurd ⟨a⟩ he⟩

theorem pullback_common : ∀ (e e' : ℕ) (σ : Type) [Fintype σ] (S : AnSys e σ) (X' : Type) [TopologicalSpace X'] [CompactSpace X'] [T2Space X'] (A' : FinHolAtlas e' X') (Θ' L' : LocPot X') (s' : X' → X' → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X') (q : Fin 2 → X' → S.X) (hq : ∀ i, HoloMap A' S.A (q i)), PullbackStatement → IsPotential A' Θ' → IsPosPot A' Θ' → IsPotential A' L' → IsSection A' L' s' → IsSNC A' L' s' m W → (∀ y, logNormSec L' s' y ≤ 0) → (∀ i, S.L.pullback (q i) (hq i).1 = L') → (∀ i, (fun x y => S.s (q i x) (q i y)) = s') → ∃ C₅ C t₀ : ℝ, t₀ ≤ S.t₀ ∧ ∀ (i : Fin 2) (a : σ), IsSingWeight A' L' s' ((S.th a).pullback (q i) (hq i).1) (S.ph a ∘ q i) C₅ ∧ IsRegFamily A' Θ' L' s' ((S.th a).pullback (q i) (hq i).1) (S.ph a ∘ q i) (fun t => S.phT a t ∘ q i) C t₀ ∧ IsRegFamilyC2 A' s' (S.ph a ∘ q i) (fun t => S.phT a t ∘ q i) := by
  intro e e' σ _ S X' _ _ _ A' Θ' L' s' nb m W q hq hP pΘ' posΘ' pL' sec' snc' nrm hL hs
  have key : ∀ p : Fin 2 × σ, ∃ C' t' : ℝ,
      IsSingWeight A' L' s' ((S.th p.2).pullback (q p.1) (hq p.1).1) (S.ph p.2 ∘ q p.1) S.C₅ ∧
      IsRegFamily A' Θ' L' s' ((S.th p.2).pullback (q p.1) (hq p.1).1) (S.ph p.2 ∘ q p.1)
        (fun t => S.phT p.2 t ∘ q p.1) C' t' ∧
      IsRegFamilyC2 A' s' (S.ph p.2 ∘ q p.1) (fun t => S.phT p.2 t ∘ q p.1) := by
    rintro ⟨i, a⟩
    have snc_i : IsSNC A' (S.L.pullback (q i) (hq i).1) (fun x y => S.s (q i x) (q i y)) m W := by
      rw [hL i, hs i]
      exact snc'
    obtain ⟨C', t', h1, h2, h3⟩ := hP S.A A' (q i) (hq i) S.Θ S.L Θ' S.s S.m S.W m W S.potΘ S.posΘ pΘ' posΘ'
      S.potL S.sec S.snc S.norm_le snc_i (S.th a) (S.ph a) (S.phT a) S.C₅ S.C S.t₀ (S.sing a) (S.reg a) (S.c2 a)
    rw [hL i, hs i] at h1 h2
    rw [hs i] at h3
    exact ⟨C', t', h1, h2, h3⟩
  choose C' t' h1 h2 h3 using key
  by_cases hσ : Nonempty σ
  · obtain ⟨a₀⟩ := hσ
    obtain ⟨D, hD⟩ := finite_bound fun p => |C' p|
    obtain ⟨T₀, hT₀, hT⟩ := finite_scale t' fun p => (h2 p).1
    have hS : 0 < S.t₀ := (S.reg a₀).1
    refine ⟨S.C₅, D, min (min T₀ S.t₀) (Real.exp (-1)),
      (min_le_left _ _).trans (min_le_right _ _), fun i a => ⟨h1 (i, a), ?_, h3 (i, a)⟩⟩
    exact (GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members e' X' A' Θ' L' s' nb m W pL' sec' snc' nrm pΘ' posΘ').2.1 _ _ _ _ _ _ _ (hD (i, a))
      (lt_min (lt_min hT₀ hS) (Real.exp_pos _)) ((min_le_left _ _).trans ((min_le_left _ _).trans (hT (i, a))))
      (min_le_right _ _) (h2 (i, a)) (h1 (i, a)).1
  · exact ⟨0, 0, S.t₀, le_rfl, fun _ a => absurd ⟨a⟩ hσ⟩

end GlobalTheory.CompanionTheory.Ar.PB.SysPull
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoMapPullbackEnergyStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_map_pullback_energy : ∀ (e e' : ℕ) (σ : Type) [Fintype σ] (S : AnSys e σ) (X' : Type) [TopologicalSpace X'] [CompactSpace X'] [T2Space X'] (A' : FinHolAtlas e' X') (Θ' L' : LocPot X') (s' : X' → X' → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X') (q : Fin 2 → X' → S.X) (hq : ∀ i, HoloMap A' S.A (q i)), PullbackStatement → IsPotential A' Θ' → IsPosPot A' Θ' → IsPotential A' L' → IsSection A' L' s' → IsSNC A' L' s' m W → (∀ y, logNormSec L' s' y ≤ 0) → (∀ i, S.L.pullback (q i) (hq i).1 = L') → (∀ i, (fun x y => S.s (q i x) (q i y)) = s') → ∃ C₅ C t₀ : ℝ, t₀ ≤ S.t₀ ∧ ∀ (i : Fin 2) (a : σ), IsSingWeight A' L' s' ((S.th a).pullback (q i) (hq i).1) (S.ph a ∘ q i) C₅ ∧ IsRegFamily A' Θ' L' s' ((S.th a).pullback (q i) (hq i).1) (S.ph a ∘ q i) (fun t => S.phT a t ∘ q i) C t₀ ∧ IsRegFamilyC2 A' s' (S.ph a ∘ q i) (fun t => S.phT a t ∘ q i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.SysPull.pullback_common | exact GlobalTheory.CompanionTheory.Ar.PB.SysPull.pullback_common | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.SysPull.pullback_common <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentSwapSquareSystem
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem ansq_exists : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2) → ∃ (Q : AnSq (FA.S.comap some) (τ, a) (xiCoef τ a)) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (e : RW.X → Q.SW.X), HoloMap RW.A Q.SW.A e ∧ IsDegreeOff Q.SW.A RW.A e 1 ∅ ∧ (∀ x x₀, FA.Re.π x₀ = Q.q 0 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) fun p => RW.lift x x ⟨some p.1, p.2⟩) ∧ (∀ x x₀, FA.Re.π x₀ = Q.q 1 (e x) → ∃ z₁, SameOrbit (FA.Re.R.lift x₀ x₀) z₁ ∧ (∀ p : (Σ k, ι k), p.1 ≠ k₀ → z₁ p = RW.lift x x ⟨some p.1, p.2⟩) ∧ ∀ m : ι k₀, z₁ ⟨k₀, m⟩ = RW.lift x x ⟨none, m⟩) ∧ (Function.Injective fun w => (Q.q 0 w, Q.q 1 w)) ∧ ∀ x (z₀ z₁ : (Σ k, ι k) → ℂ) F (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), M.IsFrame F → M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → (∀ x₀, FA.Re.π x₀ = Q.q 0 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) z₀) → (∀ x₀, FA.Re.π x₀ = Q.q 1 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) z₁) → IsBlockDiag j h → h.det ≠ 0 → t ≠ 0 → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₀ h) → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) → logNormSec Q.L' Q.v (e x) + Q.cst = Real.log ‖t * ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) * (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ h (wIdx N j) (wIdx N j) else 1) else minorIJ h (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)‖ + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) + Real.log ((fsHerm ι (M.dy p)).h z₁)) := by
  intro hin K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb har
  have hdim := GlobalTheory.T.flag_analytic_dimension_count K ι Φ y Ψ N j M n d BM FA
  obtain ⟨RW, pr, hpr, hbase, hch⟩ := GlobalTheory.T.flag_adjacent_rows_resolution K ι Φ y Ψ N j M n d BM.Rb τ a b k₀ ca cb hb hs hk hca hcb har hdim
  obtain ⟨q, hq, hpq, hl0, hl1, hinj, hbp⟩ :=
    GlobalTheory.T.flag_adjacent_rows_analytic K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb har RW pr hpr hbase
  have hch' : ∀ x, ∃ (ψ : OpenPartialHomeomorph RW.X (Fin (d + 2) → ℂ)) (kb : Fin BM.Rb.A.n) (σ : Fin n ↪ Fin (d + 2)),
      IsCompatChart RW.A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (BM.Rb.A.chart kb).source ∧
        ∀ i, BM.Rb.A.chart kb (pr x') i = ψ x' (σ i)) := fun x => by
    obtain ⟨ψ, kb, σ, i₀, F, H, hx, h1, -, -, h4, -⟩ := hch x
    exact ⟨ψ, kb, σ, h1, hx, h4⟩
  obtain ⟨pL, sL, nL, -⟩ := GlobalTheory.T.snc_adapted_atlas_projection (d + 2) n RW.X BM.Rb.X RW.A BM.Rb.A BM.Bat pr hpr BM.L BM.s BM.nb BM.m BM.W
    BM.potL BM.sec BM.snc BM.norm_le hch'
  obtain ⟨hA, hfs, hΘ⟩ := GlobalTheory.T.log_resolution_fubini_study_positive (Option K) (fun o => ι (o.getD k₀)) _ (d + 2) RW
  have hL : ∀ i, (FA.S.comap some).L.pullback (q i) (hq i).1 = BM.L.pullback pr hpr.1 := fun i => by
    show FA.S.L.pullback (q i) (hq i).1 = _
    have e := FA.L_eq
    revert e
    generalize FA.S.L = LL
    intro e
    subst e
    exact pullback_pullback _ _ _ _ _ _ _ (hpq i)
  have hs' : ∀ i, (fun x y => (FA.S.comap some).s (q i x) (q i y)) = fun x y => BM.s (pr x) (pr y) := fun i => by
    funext x y
    show FA.S.s (q i x) (q i y) = _
    rw [FA.s_eq]
    show BM.s ((FA.pr ∘ q i) x) ((FA.pr ∘ q i) y) = _
    rw [hpq i]
  obtain ⟨C₅, C, t₀, ht₀, hmem⟩ := GlobalTheory.T.two_map_pullback_energy (d + 1) (d + 2) (Ψ × Fin N) (FA.S.comap some) RW.X RW.A
    (potOf RW (fsHerm _ fun _ => 1)) (BM.L.pullback pr hpr.1) (fun x y => BM.s (pr x) (pr y)) BM.nb BM.m
    (fun k => pr ⁻¹' BM.W k) q hq hin.pullback (hA _ hfs) hΘ pL sL nL (fun x => BM.norm_le (pr x)) hL hs'
  obtain ⟨L', v, Dg, cst, potL', secv, sncv, sncsv, normv, hN⟩ :=
    GlobalTheory.T.flag_adjacent_rows_base_metric K ι Φ y Ψ N j M n d BM τ a b k₀ ca cb hb hs hk hca hcb har RW pr hpr.1 ⟨hpr, hbase, hch⟩
  obtain ⟨U, B, G, ΦY, ΦW, U_open, B_meas, coverY, coverW, ΦY_open, hfc⟩ :=
    GlobalTheory.T.flag_adjacent_rows_dimension K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb hdim RW q hq hl0 hl1 hinj
  obtain ⟨α, G_pos, G_smooth, α_smooth, xi_pot, base_pot, norm_hom⟩ :=
    GlobalTheory.T.flag_adjacent_rows_log_resolution K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb RW q hq hl0 hl1 L' v cst hN U G ΦY ΦW U_open hfc
  let SW : AnSys (d + 2) (Option (Ψ × Fin N)) :=
    { X := RW.X
      A := RW.A
      Θ := potOf RW (fsHerm _ fun _ => 1)
      L := BM.L.pullback pr hpr.1
      s := fun x y => BM.s (pr x) (pr y)
      nb := BM.nb
      m := BM.m
      W := fun k => pr ⁻¹' BM.W k
      potΘ := hA _ hfs
      posΘ := hΘ
      potL := pL
      sec := sL
      snc := nL
      norm_le := fun x => BM.norm_le (pr x)
      th := fun o => o.elim (((FA.S.comap some).th (τ, a)).pullback (q 1) (hq 1).1)
        fun p => ((FA.S.comap some).th p).pullback (q 0) (hq 0).1
      ph := fun o => o.elim ((FA.S.comap some).ph (τ, a) ∘ q 1) fun p => (FA.S.comap some).ph p ∘ q 0
      phT := fun o => o.elim (fun t => (FA.S.comap some).phT (τ, a) t ∘ q 1)
        fun p t => (FA.S.comap some).phT p t ∘ q 0
      C₅ := C₅
      C := C
      t₀ := t₀
      sing := fun o => by
        cases o with
        | none => exact (hmem 1 (τ, a)).1
        | some p => exact (hmem 0 p).1
      reg := fun o => by
        cases o with
        | none => exact (hmem 1 (τ, a)).2.1
        | some p => exact (hmem 0 p).2.1
      c2 := fun o => by
        cases o with
        | none => exact (hmem 1 (τ, a)).2.2
        | some p => exact (hmem 0 p).2.2 }
  have hsame : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P : LocPot X), SamePot A Set.univ P P :=
    fun A P x _ => ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, fun _ _ _ => analyticAt_const, fun y _ => by simp⟩
  let Q : AnSq (FA.S.comap some) (τ, a) (xiCoef τ a) :=
    { eps_a₀ := by simp [xiCoef]
      SW := SW
      q := q
      holo := hq
      bdry_eq := fun i => by
        ext x
        show BM.s (pr x) (pr x) ≠ 0 ↔ FA.S.s (q i x) (q i x) ≠ 0
        rw [FA.s_eq]
        show _ ↔ BM.s ((FA.pr ∘ q i) x) ((FA.pr ∘ q i) x) ≠ 0
        rw [hpq i]
      t₀_le := ht₀
      th0 := fun p => hsame _ _
      th1 := hsame _ _
      ph0 := fun _ => rfl
      ph1 := rfl
      phase_some_eq_comp_first_projection := fun _ _ => rfl
      phase_none_eq_comp_second_projection := fun _ => rfl
      base_ph := fun p hp => (hbp p hp).1
      base_phT := fun p hp t => (hbp p hp).2 t
      L' := L'
      v := v
      Dg := Dg
      cst := cst
      potL' := potL'
      secv := secv
      sncv := sncv
      sncsv := sncsv
      normv := normv
      U := U
      B := B
      G := G
      α := α
      ΦY := ΦY
      ΦW := ΦW
      U_open := U_open
      B_meas := B_meas
      G_pos := G_pos
      G_smooth := G_smooth
      α_smooth := fun m p => α_smooth m p
      coverY := coverY
      coverW := coverW
      ΦY_open := ΦY_open
      first_projection_chart_compat := fun m z hz => by
        obtain ⟨l, H, bp, -, -, -, -, -, -, h⟩ := hfc m
        exact (h z hz).1
      second_projection_chart_compat := fun m z hz => by
        obtain ⟨l, H, bp, -, -, -, -, -, -, h⟩ := hfc m
        exact (h z hz).2
      xi_pot := xi_pot
      base_pot := base_pot
      norm_hom := norm_hom }
  have hsurj : ∀ w, ∃ x₀, FA.Re.π x₀ = w := fun w => by
    have hd := FA.Re.degree
    rw [FA.deg_one, FA.br_empty] at hd
    obtain ⟨x₀, hx₀⟩ := Set.ncard_eq_one.1 (hd.2.2.2.2.1 w (Set.notMem_empty w))
    exact ⟨x₀, (hx₀ ▸ Set.mem_singleton x₀ : x₀ ∈ FA.Re.π ⁻¹' {w})⟩
  refine ⟨Q, RW, id, ⟨continuous_id, fun j k => RW.A.holo j k⟩, isDegreeOff_id RW.A, hl0, ?_, hinj, ?_⟩
  · intro x x₀ hx
    refine ⟨sndPt k₀ (RW.lift x x), hl1 x x₀ hx, fun p hp => ?_, fun m => ?_⟩
    · show RW.lift x x (v₁ k₀ p) = _
      rw [v₁_ne hp]
    · show RW.lift x x (v₁ k₀ ⟨k₀, m⟩) = _
      rw [v₁_self]
  · intro x z₀ z₁ F h t hF hG h0 h1 hh hd ht hE0 hE1
    obtain ⟨x₀, hx₀⟩ := hsurj (q 0 x)
    obtain ⟨x₁, hx₁⟩ := hsurj (q 1 x)
    exact hN x z₀ z₁ F h t hF hG (orbit_trans (orbit_symm (h0 x₀ hx₀)) (hl0 x x₀ hx₀)) (orbit_trans (orbit_symm (h1 x₁ hx₁)) (hl1 x x₁ hx₁))
      hh hd ht hE0 hE1

end GlobalTheory.CompanionTheory.Ar.PB.WSq
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentSwapSquareSystemStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_swap_square_system : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2) → ∃ (Q : AnSq (FA.S.comap some) (τ, a) (xiCoef τ a)) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (e : RW.X → Q.SW.X), HoloMap RW.A Q.SW.A e ∧ IsDegreeOff Q.SW.A RW.A e 1 ∅ ∧ (∀ x x₀, FA.Re.π x₀ = Q.q 0 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) fun p => RW.lift x x ⟨some p.1, p.2⟩) ∧ (∀ x x₀, FA.Re.π x₀ = Q.q 1 (e x) → ∃ z₁, SameOrbit (FA.Re.R.lift x₀ x₀) z₁ ∧ (∀ p : (Σ k, ι k), p.1 ≠ k₀ → z₁ p = RW.lift x x ⟨some p.1, p.2⟩) ∧ ∀ m : ι k₀, z₁ ⟨k₀, m⟩ = RW.lift x x ⟨none, m⟩) ∧ (Function.Injective fun w => (Q.q 0 w, Q.q 1 w)) ∧ ∀ x (z₀ z₁ : (Σ k, ι k) → ℂ) F (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), M.IsFrame F → M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → (∀ x₀, FA.Re.π x₀ = Q.q 0 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) z₀) → (∀ x₀, FA.Re.π x₀ = Q.q 1 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) z₁) → IsBlockDiag j h → h.det ≠ 0 → t ≠ 0 → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₀ h) → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) → logNormSec Q.L' Q.v (e x) + Q.cst = Real.log ‖t * ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) * (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ h (wIdx N j) (wIdx N j) else 1) else minorIJ h (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)‖ + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) + Real.log ((fsHerm ι (M.dy p)).h z₁)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.ansq_exists | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.ansq_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.ansq_exists <;> assumption)
end
