module

public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.EmbEquivSymmApply
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.MetricLocal
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.KillNoneFormPoly
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodMatrixLocalTrivialization
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.WeilBound.CoreStatements.FlagImmersions.IntersectionMultilinearExpansion

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjection
section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.RiemannLatticeEigenProjections
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace LevelTowerAlt

theorem riemann_lattice_eigen_projections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ), Function.Injective R.P ∧ Submodule.span ℝ (Set.range R.P) = ⊤ ∧ (∀ s : 𝓞 E →+* ℂ, (∀ x, eigComp R.B s x ∈ eigSp R.B s) ∧ (∀ x ∈ eigSp R.B s, eigComp R.B s x = x) ∧ (∀ (c : ℂ) x y, eigComp R.B s (c • x + y) = c • eigComp R.B s x + eigComp R.B s y) ∧ ∀ a x, eigComp R.B s (R.B a x) = s a • eigComp R.B s x) ∧ (∀ x, ∑ s : E →+* ℂ, eigComp R.B (s.comp (algebraMap (𝓞 E) E)) x = x) ∧ ∀ s s' : 𝓞 E →+* ℂ, s ≠ s' → ∀ x ∈ eigSp R.B s, ∀ y ∈ eigSp R.B s', R.ip x y = 0 := by
  intro E _ _ _ g Λ _ _ Ψ _ R
  refine ⟨LevelTowerAlt.precomp_injective R, LevelTowerAlt.span_top R,
    fun s => ⟨fun x => ?_, fun x hx => ?_, fun c x y => ?_, fun a x => ?_⟩, fun x => ?_,
    fun s s' hss' x hx y hy => LevelTowerAlt.ip_orth R hss' hx hy⟩
  · rw [LevelTowerAlt.eigComp_eq]
    exact LevelTowerAlt.proj_mem _ _ _
  · rw [LevelTowerAlt.eigComp_eq]
    exact LevelTowerAlt.proj_eig_self hx
  · simp only [LevelTowerAlt.eigComp_eq, map_add (f := _), map_smul]
  · simp only [LevelTowerAlt.eigComp_eq]
    exact LevelTowerAlt.proj_act _ _ _ _
  · simp only [LevelTowerAlt.eigComp_eq]
    conv_rhs => rw [← LevelTowerAlt.sum_proj R.B x]
    exact Fintype.sum_equiv (LevelTowerAlt.embEquiv E) _ _ (fun _ => rfl)

end LevelTowerAlt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjection
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.riemann_lattice_eigen_projection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ), Function.Injective R.P ∧ Submodule.span ℝ (Set.range R.P) = ⊤ ∧ (∀ s : 𝓞 E →+* ℂ, (∀ x, eigComp R.B s x ∈ eigSp R.B s) ∧ (∀ x ∈ eigSp R.B s, eigComp R.B s x = x) ∧ (∀ (c : ℂ) x y, eigComp R.B s (c • x + y) = c • eigComp R.B s x + eigComp R.B s y) ∧ ∀ a x, eigComp R.B s (R.B a x) = s a • eigComp R.B s x) ∧ (∀ x, ∑ s : E →+* ℂ, eigComp R.B (s.comp (algebraMap (𝓞 E) E)) x = x) ∧ ∀ s s' : 𝓞 E →+* ℂ, s ≠ s' → ∀ x ∈ eigSp R.B s, ∀ y ∈ eigSp R.B s', R.ip x y = 0 := by
  first | exact @LevelTowerAlt.riemann_lattice_eigen_projections | exact LevelTowerAlt.riemann_lattice_eigen_projections
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_lattice_eigen_projection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ), Function.Injective R.P ∧ Submodule.span ℝ (Set.range R.P) = ⊤ ∧ (∀ s : 𝓞 E →+* ℂ, (∀ x, eigComp R.B s x ∈ eigSp R.B s) ∧ (∀ x ∈ eigSp R.B s, eigComp R.B s x = x) ∧ (∀ (c : ℂ) x y, eigComp R.B s (c • x + y) = c • eigComp R.B s x + eigComp R.B s y) ∧ ∀ a x, eigComp R.B s (R.B a x) = s a • eigComp R.B s x) ∧ (∀ x, ∑ s : E →+* ℂ, eigComp R.B (s.comp (algebraMap (𝓞 E) E)) x = x) ∧ ∀ s s' : 𝓞 E →+* ℂ, s ≠ s' → ∀ x ∈ eigSp R.B s, ∀ y ∈ eigSp R.B s', R.ip x y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.riemann_lattice_eigen_projection | exact GlobalTheory.CompanionTheory.Relay.riemann_lattice_eigen_projection | (intros; apply GlobalTheory.CompanionTheory.Relay.riemann_lattice_eigen_projection <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxComp

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt
open ReciprocityTheory.AnForm.R (conePts)

abbrev cxIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) :
    Ideal (MRingOver ℂ ι) :=
  P.map (map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι)

def cxPosDens {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ) : ℝ :=
  ∑ᶠ w ∈ setFibre S Ψ y, max (setSheetDensity S Ψ φ g y w) 0

end GlobalTheory.CompanionTheory.Ar.Pub.CxComp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeOfIsIntersectionSystem
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem degree_of_isIntersectionSystem (II : IntersectionSystem) (hII : IsIntersectionSystem II) :
    ReciprocityTheory.ChartRestriction.G.Geo.DegreeStatement :=
  GroundTheory.Heights₂.Heights.Inter.Conservation.conservation_iff_degree_statement.mp
    (GroundTheory.Heights₂.Heights.Inter.Conservation.conservation_degree_form_of_existence ⟨II, hII⟩
      GroundTheory.Heights₂.Heights.Inter.Conservation.statement_holds)

theorem degree_of_system :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.Geo.DegreeStatement :=
  fun ⟨II, hII⟩ => degree_of_isIntersectionSystem II hII.1

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicEigencomponentConjugateForm
section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.EigenProjectionConjugateInner
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace LevelTowerAlt

theorem eigen_projection_conjugate_inner : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (I : Submodule (𝓞 E) Λ), IsIsoSub R.form I → ∀ s : 𝓞 E →+* ℂ, (∀ v ∈ I, ∀ w ∈ I, R.ip (eigComp R.B ((starRingEnd ℂ).comp s) (R.P v)) (eigComp R.B ((starRingEnd ℂ).comp s) (R.P w)) = starRingEnd ℂ (R.ip (eigComp R.B s (R.P v)) (eigComp R.B s (R.P w)))) ∧ ∀ (r : ℕ) (v : Fin r → Λ), (∀ a, v a ∈ I) → LinearIndependent (𝓞 E) v → LinearIndependent ℂ fun a => eigComp R.B s (R.P (v a)) := by
  intro E _ _ _ g Λ _ _ Ψ _ R I hI s
  simp only [LevelTowerAlt.eigComp_eq]
  exact ⟨fun v hv w hw => gram_conj R hI s hv hw, fun r v hv hli => proj_indep R hI s hv hli⟩

end LevelTowerAlt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicEigencomponentConjugateForm
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.isotropic_eigencomponent_conjugate_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (I : Submodule (𝓞 E) Λ), IsIsoSub R.form I → ∀ s : 𝓞 E →+* ℂ, (∀ v ∈ I, ∀ w ∈ I, R.ip (eigComp R.B ((starRingEnd ℂ).comp s) (R.P v)) (eigComp R.B ((starRingEnd ℂ).comp s) (R.P w)) = starRingEnd ℂ (R.ip (eigComp R.B s (R.P v)) (eigComp R.B s (R.P w)))) ∧ ∀ (r : ℕ) (v : Fin r → Λ), (∀ a, v a ∈ I) → LinearIndependent (𝓞 E) v → LinearIndependent ℂ fun a => eigComp R.B s (R.P (v a)) := by
  first | exact @LevelTowerAlt.eigen_projection_conjugate_inner | exact LevelTowerAlt.eigen_projection_conjugate_inner
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicEigencomponentConjugateFormStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_eigencomponent_conjugate_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (I : Submodule (𝓞 E) Λ), IsIsoSub R.form I → ∀ s : 𝓞 E →+* ℂ, (∀ v ∈ I, ∀ w ∈ I, R.ip (eigComp R.B ((starRingEnd ℂ).comp s) (R.P v)) (eigComp R.B ((starRingEnd ℂ).comp s) (R.P w)) = starRingEnd ℂ (R.ip (eigComp R.B s (R.P v)) (eigComp R.B s (R.P w)))) ∧ ∀ (r : ℕ) (v : Fin r → Λ), (∀ a, v a ∈ I) → LinearIndependent (𝓞 E) v → LinearIndependent ℂ fun a => eigComp R.B s (R.P (v a)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.isotropic_eigencomponent_conjugate_form | exact GlobalTheory.CompanionTheory.Relay.isotropic_eigencomponent_conjugate_form | (intros; apply GlobalTheory.CompanionTheory.Relay.isotropic_eigencomponent_conjugate_form <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MetricLocal
namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem metricLocal : ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement :=
  GroundTheory.Heights₂.Heights.MetricLocalB.full

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodsSubframeDetBounds
open Matrix Metric GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

open scoped ComplexOrder

theorem frame_rank_of_gram_det_ne_zero {g k : ℕ} (M : Matrix (Fin g) (Fin k) ℂ)
    (h : (Mᵀ * M.map star).det ≠ 0) : M.rank = k := by
  have hu : IsUnit (Mᵀ * M.map star) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  have h1 := Matrix.rank_of_isUnit _ hu
  simp only [Fintype.card_fin] at h1
  have h2 := Matrix.rank_mul_le_left Mᵀ (M.map star)
  rw [Matrix.rank_transpose] at h2
  have h3 := M.rank_le_width
  omega

theorem frame_compact_nhd {g k : ℕ} (M₀ : Matrix (Fin g) (Fin k) ℂ) (h : M₀.rank = k) :
    ∃ S : Set (Matrix (Fin g) (Fin k) ℂ), IsCompact S ∧ S ∈ nhds M₀ ∧ ∀ M ∈ S, M.rank = k := by
  have hP : (M₀.map star)ᴴ = M₀ᵀ := by
    ext i j
    simp
  have hpos : 0 < ((M₀ᵀ * M₀.map star).det).re := by
    have := GlobalTheory.re_det_pos_of_posDef (subframe_gram_posDef M₀ h)
    rw [hP] at this
    exact this
  have hU : IsOpen {M : Matrix (Fin g) (Fin k) ℂ | 0 < ((Mᵀ * M.map star).det).re} :=
    isOpen_lt continuous_const subframe_continuous_det
  haveI : LocallyCompactSpace (Matrix (Fin g) (Fin k) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin g → Fin k → ℂ))
  obtain ⟨S, hS, hSU, hSc⟩ := local_compact_nhds (hU.mem_nhds hpos)
  refine ⟨S, hSc, hS, fun M hM => frame_rank_of_gram_det_ne_zero M ?_⟩
  intro h0
  have := hSU hM
  rw [Set.mem_setOf_eq, h0] at this
  simp at this

theorem continuousAt_matrix_inv {X : Type*} [TopologicalSpace X] {g : ℕ}
    (A : X → Matrix (Fin g) (Fin g) ℂ) (x : X) (hA : ContinuousAt A x) (h : (A x).det ≠ 0) :
    ContinuousAt (fun y => (A y)⁻¹) x := by
  have hd : ContinuousAt (fun y => (A y).det) x :=
    (continuous_id.matrix_det).continuousAt.comp hA
  have ha : ContinuousAt (fun y => (A y).adjugate) x :=
    (continuous_id.matrix_adjugate).continuousAt.comp hA
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact (hd.inv₀ h).smul ha

theorem chartRadius_le_log_sum {n a : ℕ} (h : a ≤ n) (z : Fin n → ℂ) (h1 : ∀ k, ‖z k‖ < 1)
    (h0 : ∀ i : Fin n, i.val < a → z i ≠ 0) :
    1 ≤ chartRadius h z ∧ chartRadius h z ≤ (Real.exp 1 + 2) *
      (1 + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖|) := by
  have hsum : ∑ j : Fin a, |Real.log ‖z (Fin.castLE h j)‖| =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| := by
    refine Finset.sum_bij (fun j _ => Fin.castLE h j) ?_ ?_ ?_ ?_
    · intro j _
      simp
    · intro j _ j' _ e
      exact Fin.castLE_injective h e
    · intro i hi
      have hi' : i.val < a := by simpa using hi
      exact ⟨⟨i.val, hi'⟩, Finset.mem_univ _, by ext; simp⟩
    · intro j _
      rfl
  have hterm : ∀ j : Fin a, Real.log (‖cuspCoord h z j‖ ^ 2)⁻¹ =
      2 * |Real.log ‖z (Fin.castLE h j)‖| := by
    intro j
    have hc : cuspCoord h z j = z (Fin.castLE h j) := rfl
    have hn : 0 ≤ ‖z (Fin.castLE h j)‖ := norm_nonneg _
    rw [hc, Real.log_inv, Real.log_pow, abs_of_nonpos (Real.log_nonpos hn (h1 _).le)]
    push_cast
    ring
  have hr : chartRadius h z = Real.exp 1 + 2 *
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| := by
    rw [chartRadius, ← hsum, Finset.mul_sum]
    simp only [hterm]
  have hS : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  rw [hr]
  constructor
  · linarith
  · nlinarith

theorem logPeriods_subframe_det_bounds : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : LogPeriods n a g Λ) (k : ℕ) (F : (Fin n → ℂ) → Matrix (Fin k) (Fin g) ℂ), ContinuousAt F 0 → (F 0).rank = k → ∃ (ρ K : ℝ) (N : ℕ), 0 < ρ ∧ ρ ≤ 1 ∧ ∀ z ∈ ball (0 : Fin n → ℂ) ρ, (∀ i : Fin n, i.val < a → z i ≠ 0) → ‖(F z * L.H z * (F z)ᴴ).det‖ ≤ K ∧ 1 ≤ K * (1 + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖|) ^ N * ‖(F z * L.H z * (F z)ᴴ).det‖ := by
  intro n a g Λ _ L k F hF hrk
  obtain ⟨Q, A, hAd, hA0, hAH⟩ := GlobalTheory.T.period_matrix_local_trivialization n a g Λ L
  obtain ⟨ρ₁, c, C, hρ₁, hρ₁1, hc, hb⟩ :=
    (ImTauBounds.cond RiemannExtensionSlices.proof PuncturedExpOrder.proof LogCoverDescent.proof) n a g Q
  have hAc : ContinuousAt A 0 := by
    have : ContinuousOn A (ball 0 1) :=
      continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hAd i j).continuousOn
    exact this.continuousAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))
  have hAi := continuousAt_matrix_inv A 0 hAc hA0
  have hc2 : Continuous (fun p : Matrix (Fin k) (Fin g) ℂ × Matrix (Fin g) (Fin g) ℂ => p.1 * p.2) :=
    continuous_fst.matrix_mul continuous_snd
  have hmul : ContinuousAt (fun z => F z * (A z)⁻¹) 0 :=
    ContinuousAt.comp (g := fun p : Matrix (Fin k) (Fin g) ℂ × Matrix (Fin g) (Fin g) ℂ => p.1 * p.2)
      (f := fun z => (F z, (A z)⁻¹)) hc2.continuousAt (hF.prodMk hAi)
  have hG : ContinuousAt (fun z => (F z * (A z)⁻¹)ᵀ) 0 :=
    (continuous_id.matrix_transpose.continuousAt).comp hmul
  have hM0 : ((F 0 * (A 0)⁻¹)ᵀ).rank = k := by
    have hu : IsUnit ((A 0)⁻¹).det := Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 hA0)
    rw [Matrix.rank_transpose, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hu, hrk]
  obtain ⟨S, hS, hSn, hSr⟩ := frame_compact_nhd _ hM0
  obtain ⟨C', hC', hd⟩ := subframe_det_log_growth g k (Matrix (Fin g) (Fin k) ℂ) S hS id
    continuousOn_id hSr c C hc
  have hdet : ContinuousAt (fun z => (A z).det) 0 :=
    (continuous_id.matrix_det).continuousAt.comp hAc
  have hev : ∀ᶠ z in nhds (0 : Fin n → ℂ), (F z * (A z)⁻¹)ᵀ ∈ S ∧ (A z).det ≠ 0 :=
    (hG.eventually_mem hSn).and (hdet.eventually_ne hA0)
  obtain ⟨ρ₂, hρ₂, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have he : 0 < Real.exp 1 + 2 := by positivity
  refine ⟨min (min ρ₁ ρ₂) 1, C' * (Real.exp 1 + 2) ^ k, k, lt_min (lt_min hρ₁ hρ₂) one_pos,
    min_le_right _ _, fun z hz hz0 => ?_⟩
  have hzρ : ‖z‖ < min (min ρ₁ ρ₂) 1 := by simpa [dist_zero_right] using hz
  have hz1n : ‖z‖ < 1 := lt_of_lt_of_le hzρ (min_le_right _ _)
  have hz1 : ∀ k, ‖z k‖ < 1 := fun k => lt_of_le_of_lt (norm_le_pi_norm z k) hz1n
  have hzρ₁ : z ∈ closedBall (0 : Fin n → ℂ) ρ₁ := by
    have : ‖z‖ ≤ ρ₁ := hzρ.le.trans ((min_le_left _ _).trans (min_le_left _ _))
    simpa [dist_zero_right] using this
  have hzρ₂ : z ∈ ball (0 : Fin n → ℂ) ρ₂ := by
    have : ‖z‖ < ρ₂ := lt_of_lt_of_le hzρ ((min_le_left _ _).trans (min_le_right _ _))
    simpa [dist_zero_right] using this
  obtain ⟨hGS, hAz⟩ := hball z hzρ₂
  have hcusp : ∀ j : Fin a, cuspCoord L.a_le z j ≠ 0 := fun j => hz0 _ (by simp)
  have hzp : z ∈ puncturedChart L.a_le (ball (0 : Fin n → ℂ) 1) :=
    ⟨by simpa [dist_zero_right] using hz1n, hcusp⟩
  have hw := HodgeDerivative.logLift_mem L.a_le hzp
  have hexp := HodgeDerivative.expCover_logLift L.a_le hcusp
  have hAHz := hAH _ hw
  rw [hexp] at hAHz
  obtain ⟨hb1, hb2⟩ := hb _ hw (by rw [hexp]; exact hzρ₁)
  rw [hexp] at hb2
  obtain ⟨hr1, hr2⟩ := chartRadius_le_log_sum L.a_le z hz1 hz0
  have hx := hd _ hGS ((Q.τ (logLift a z)).map Complex.im) (chartRadius L.a_le z) hr1 hb1 hb2
  set Y := (Q.τ (logLift a z)).map Complex.im with hY
  set S' := ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| with hS'
  have hAu : IsUnit (A z).det := isUnit_iff_ne_zero.2 hAz
  have hinv1 : (A z)⁻¹ * A z = 1 := Matrix.nonsing_inv_mul _ hAu
  have hinv2 : (A z)ᴴ * ((A z)⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hinv1, Matrix.conjTranspose_one]
  have hkey : F z * L.H z * (F z)ᴴ = (F z * (A z)⁻¹) * (Y⁻¹).map Complex.ofReal * (F z * (A z)⁻¹)ᴴ := by
    rw [← hAHz, Matrix.conjTranspose_mul]
    have e : F z * (A z)⁻¹ * (A z * L.H z * (A z)ᴴ) * (((A z)⁻¹)ᴴ * (F z)ᴴ) =
        F z * ((A z)⁻¹ * A z) * L.H z * ((A z)ᴴ * ((A z)⁻¹)ᴴ) * (F z)ᴴ := by
      simp only [Matrix.mul_assoc]
    rw [e, hinv1, hinv2]
    simp
  have hd1 : ((F z * L.H z * (F z)ᴴ).det).re ≤ C' := by
    rw [hkey]
    exact hx.1
  have hd2 : 1 ≤ C' * chartRadius L.a_le z ^ k * ((F z * L.H z * (F z)ᴴ).det).re := by
    rw [hkey]
    exact hx.2
  have hpsd : (F z * L.H z * (F z)ᴴ).PosSemidef := by
    rw [hkey]
    have hYp : Y.PosDef := Q.im_posDef _ hw
    exact (subframe_map_posSemidef hYp.inv.posSemidef).mul_mul_conjTranspose_same _
  have hD := hpsd.det_nonneg
  obtain ⟨D, hDdef⟩ : ∃ D, D = (F z * L.H z * (F z)ᴴ).det := ⟨_, rfl⟩
  rw [← hDdef] at hd1 hd2 hD ⊢
  have hnorm : ‖D‖ = D.re := by
    obtain ⟨h1, h2⟩ := Complex.nonneg_iff.1 hD
    have e : D = (D.re : ℂ) := by
      apply Complex.ext <;> simp [h2.symm]
    rw [e, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re, abs_of_nonneg h1]
  rw [hnorm]
  have hre : 0 ≤ D.re := (Complex.nonneg_iff.1 hD).1
  have hS0 : 0 ≤ S' := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hE1 : 1 ≤ (Real.exp 1 + 2) ^ k := one_le_pow₀ (by linarith [Real.exp_pos 1])
  constructor
  · calc D.re ≤ C' := hd1
      _ ≤ C' * (Real.exp 1 + 2) ^ k := le_mul_of_one_le_right hC'.le hE1
  · have hpow : chartRadius L.a_le z ^ k ≤ ((Real.exp 1 + 2) * (1 + S')) ^ k :=
      pow_le_pow_left₀ (by linarith) hr2 k
    calc (1 : ℝ) ≤ C' * chartRadius L.a_le z ^ k * D.re := hd2
      _ ≤ C' * ((Real.exp 1 + 2) * (1 + S')) ^ k * D.re := by gcongr
      _ = C' * (Real.exp 1 + 2) ^ k * (1 + S') ^ k * D.re := by rw [mul_pow]; ring

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArithmeticIntersectionMultilinearPolar
section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.XReComb
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

private theorem isSmoothHerm_combLine' {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {σ : Type}
    [Fintype σ] (A : σ → HermLine ι) (hA : ∀ a, IsSmoothHerm (A a)) (d : σ → ℤ) :
    IsSmoothHerm (combLine A d) := by
  classical
  unfold IsSmoothHerm
  have hfun : (combLine A d).h = fun z => ∏ x : σ, (A x).h z ^ d x := funext (combLine_h A d)
  rw [hfun]
  apply contDiffOn_prod
  intro x _
  rcases Int.eq_nat_or_neg (d x) with ⟨m, hm | hm⟩
  · simp_rw [hm, zpow_natCast]
    exact (hA x).pow m
  · simp_rw [hm, zpow_neg, zpow_natCast]
    exact ((hA x).pow m).inv (fun z hz => pow_ne_zero _ ((A x).pos z hz).ne')

private theorem II_update_combLine (hML : MetricLocalStatement) (II : IntersectionSystem)
    (hII : IsFullIntersectionSystem II) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (σ : Type) [Fintype σ] (P : Ideal (MRing ι)) (n : ℕ) (A : σ → HermLine ι)
    (hA : ∀ a, IsSmoothHerm (A a)) (hP : IsArithVar P n) (L : Fin n → HermLine ι)
    (hL : ∀ r, IsSmoothHerm (L r)) (j : Fin n) (d : σ → ℤ) :
    II K ι P n (Function.update L j (combLine A d)) =
      ∑ a, (d a : ℝ) * II K ι P n (Function.update L j (A a)) := by
  classical
  have hsm : ∀ (M : HermLine ι), IsSmoothHerm M → ∀ r, IsSmoothHerm (Function.update L j M r) := by
    intro M hM r
    by_cases h : r = j
    · subst h
      simpa using hM
    · simpa [Function.update_of_ne h] using hL r
  have hloc : ∀ M M' : HermLine ι, IsSmoothHerm M → IsSmoothHerm M' → M.a = M'.a →
      (∀ z ∈ mcPts P, M.h z = M'.h z) →
      II K ι P n (Function.update L j M) = II K ι P n (Function.update L j M') := by
    intro M M' hM hM' ha hh
    apply hML K ι (II K ι) (hII.1 K ι) P n _ _ hP (hsm M hM) (hsm M' hM')
    · intro r
      by_cases h : r = j
      · subst h
        simp [ha]
      · simp [Function.update_of_ne h]
    · intro r z hz
      by_cases h : r = j
      · subst h
        simpa using hh z hz
      · simp [Function.update_of_ne h]
  let G : (σ → ℤ) → ℝ := fun d => II K ι P n (Function.update L j (combLine A d))
  have hadd : ∀ d d', G (d + d') = G d + G d' := by
    intro d d'
    have h1 : G (d + d') =
        II K ι P n (Function.update L j ((combLine A d).tensor (combLine A d'))) := by
      apply hloc _ _ (isSmoothHerm_combLine' A hA _)
        (by unfold IsSmoothHerm; exact (isSmoothHerm_combLine' A hA d).mul (isSmoothHerm_combLine' A hA d'))
      · funext k
        show (combLine A (d + d')).a k = (combLine A d).a k + (combLine A d').a k
        rw [combLine_a, combLine_a, combLine_a, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [Pi.add_apply]
        ring
      · intro z hz
        show (combLine A (d + d')).h z = (combLine A d).h z * (combLine A d').h z
        rw [combLine_h, combLine_h, combLine_h, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun x _ => ?_
        exact zpow_add₀ ((A x).pos z hz.1).ne' _ _
    rw [h1]
    exact hII.2.1 K ι P n L j _ _ hP hL (isSmoothHerm_combLine' A hA d) (isSmoothHerm_combLine' A hA d')
  have hsingle : ∀ a, G (Pi.single a 1) = II K ι P n (Function.update L j (A a)) := by
    intro a
    apply hloc _ _ (isSmoothHerm_combLine' A hA _) (hA a)
    · funext k
      rw [combLine_a]
      simp [Pi.single_apply]
    · intro z _
      rw [combLine_h, Finset.prod_eq_single a]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · simp
  let Gh : (σ → ℤ) →+ ℝ := AddMonoidHom.mk' G hadd
  have hd : d = ∑ a, d a • Pi.single a (1 : ℤ) := by
    funext x
    simp [Finset.sum_apply, Pi.single_apply]
  show G d = _
  calc G d = Gh d := rfl
    _ = Gh (∑ a, d a • Pi.single a (1 : ℤ)) := by rw [← hd]
    _ = ∑ a, (d a : ℝ) * G (Pi.single a 1) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_zsmul, zsmul_eq_mul]
      rfl
    _ = _ := by simp_rw [hsingle]

private theorem II_combLine_eq_polar (hML : MetricLocalStatement) (II : IntersectionSystem)
    (hII : IsFullIntersectionSystem II) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (σ : Type) [Fintype σ] (P : Ideal (MRing ι)) (n : ℕ) (A : σ → HermLine ι) (c : Fin n → σ → ℤ)
    (hP : IsArithVar P n) (hA : ∀ a, IsSmoothHerm (A a)) :
    II K ι P n (fun r => combLine A (c r)) =
      polar n (fun w => II K ι P n fun r => A (w r)) (fun r a => (c r a : ℝ)) := by
  classical
  unfold polar
  rcases isEmpty_or_nonempty σ with hσ | ⟨⟨a0⟩⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Fintype.sum_unique]
      simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
      congr 1
      funext r
      exact r.elim0
    · obtain ⟨j⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      haveI : IsEmpty (Fin n → σ) := ⟨fun w => hσ.elim (w j)⟩
      have e : (fun r => combLine A (c r)) =
          Function.update (fun r => combLine A (c r)) j (combLine A (c j)) := by simp
      rw [e, II_update_combLine hML II hII K ι σ P n A hA hP _ (fun r => isSmoothHerm_combLine' A hA (c r)) j (c j)]
      simp [Finset.univ_eq_empty]
  · let t : Finset (Fin n) → Fin n → Finset σ := fun S r => if r ∈ S then Finset.univ else {a0}
    let line : Finset (Fin n) → (Fin n → σ) → Fin n → HermLine ι :=
      fun S w r => if r ∈ S then A (w r) else combLine A (c r)
    have hsm : ∀ S w r, IsSmoothHerm (line S w r) := by
      intro S w r
      simp only [line]
      split_ifs
      · exact hA _
      · exact isSmoothHerm_combLine' A hA _
    have key : ∀ S : Finset (Fin n), II K ι P n (fun r => combLine A (c r)) =
        ∑ w ∈ Fintype.piFinset (t S), (∏ r ∈ S, (c r (w r) : ℝ)) * II K ι P n (line S w) := by
      intro S
      refine Finset.induction_on S ?_ ?_
      · have h0 : Fintype.piFinset (t ∅) = {fun _ => a0} := by
          ext w
          simp [t, Fintype.mem_piFinset, funext_iff]
        rw [h0, Finset.sum_singleton]
        simp [line]
      · intro j S hj ih
        rw [ih]
        have hexp : ∀ w ∈ Fintype.piFinset (t S),
            (∏ r ∈ S, (c r (w r) : ℝ)) * II K ι P n (line S w) =
              ∑ a, (∏ r ∈ insert j S, (c r (Function.update w j a r) : ℝ)) *
                II K ι P n (line (insert j S) (Function.update w j a)) := by
          intro w _
          have hl : line S w = Function.update (line S w) j (combLine A (c j)) := by
            funext r
            by_cases h : r = j
            · subst h
              simp [line, hj]
            · simp [Function.update_of_ne h]
          rw [hl, II_update_combLine hML II hII K ι σ P n A hA hP _ (hsm S w) j (c j), Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          have hupd : Function.update (line S w) j (A a) = line (insert j S) (Function.update w j a) := by
            funext r
            by_cases h : r = j
            · subst h
              simp [line]
            · simp [line, Function.update_of_ne h, Finset.mem_insert, h]
          rw [hupd, Finset.prod_insert hj, Function.update_self]
          have hprod : ∏ r ∈ S, (c r (Function.update w j a r) : ℝ) = ∏ r ∈ S, (c r (w r) : ℝ) :=
            Finset.prod_congr rfl fun r hr => by
              have hrj : r ≠ j := fun h => hj (h ▸ hr)
              rw [Function.update_of_ne hrj]
          rw [hprod]
          ring
        rw [Finset.sum_congr rfl hexp, ← Finset.sum_product']
        apply Finset.sum_nbij' (fun p => Function.update p.1 j p.2) (fun w => (Function.update w j a0, w j))
        · rintro ⟨w, a⟩ hp
          simp only [Finset.mem_coe, Finset.mem_product, Fintype.mem_piFinset] at hp ⊢
          intro r
          by_cases h : r = j
          · subst h
            simp [t]
          · rw [Function.update_of_ne h]
            have := hp.1 r
            simpa [t, Finset.mem_insert, h] using this
        · intro w hw
          simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_univ, and_true, Fintype.mem_piFinset] at hw ⊢
          intro r
          by_cases h : r = j
          · subst h
            simp [t, hj]
          · rw [Function.update_of_ne h]
            have := hw r
            simpa [t, Finset.mem_insert, h] using this
        · rintro ⟨w, a⟩ hp
          simp only [Finset.mem_coe, Finset.mem_product, Fintype.mem_piFinset] at hp
          have hwj : w j = a0 := by simpa [t, hj] using hp.1 j
          simp [Function.update_idem, ← hwj]
        · intro w _
          simp [Function.update_idem]
        · intro p _
          rfl
    rw [key Finset.univ]
    have hu : Fintype.piFinset (t Finset.univ) = Finset.univ := by
      ext w
      simp [t]
    rw [hu]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [line]

theorem PositivityTheory.Xgp.t_re_comb : MetricLocalStatement → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) [Fintype σ] (P : Ideal (MRing ι)) (n : ℕ) (A : σ → HermLine ι) (c : Fin n → σ → ℤ), IsArithVar P n → (∀ a, IsSmoothHerm (A a)) → (∀ r, IsSmoothHerm (combLine A (c r))) ∧ II K ι P n (fun r => combLine A (c r)) = polar n (fun w => II K ι P n fun r => A (w r)) (fun r a => (c r a : ℝ)) := by
  intro hML II hII K _ ι _ σ _ P n A c hP hA
  exact ⟨fun r => isSmoothHerm_combLine' A hA (c r), II_combLine_eq_polar hML II hII K ι σ P n A c hP hA⟩
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArithmeticIntersectionMultilinearPolar
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem combLine_intersection : MetricLocalStatement → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) [Fintype σ] (P : Ideal (MRing ι)) (n : ℕ) (A : σ → HermLine ι) (c : Fin n → σ → ℤ), IsArithVar P n → (∀ a, IsSmoothHerm (A a)) → (∀ r, IsSmoothHerm (combLine A (c r))) ∧ II K ι P n (fun r => combLine A (c r)) = polar n (fun w => II K ι P n fun r => A (w r)) (fun r a => (c r a : ℝ)) :=
  @PositivityTheory.Xgp.t_re_comb

end GlobalTheory.CompanionTheory.Ar.PB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArithmeticIntersectionMultilinearPolarStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_intersection_multilinear_polar : MetricLocalStatement → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) [Fintype σ] (P : Ideal (MRing ι)) (n : ℕ) (A : σ → HermLine ι) (c : Fin n → σ → ℤ), IsArithVar P n → (∀ a, IsSmoothHerm (A a)) → (∀ r, IsSmoothHerm (combLine A (c r))) ∧ II K ι P n (fun r => combLine A (c r)) = polar n (fun w => II K ι P n fun r => A (w r)) (fun r a => (c r a : ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.combLine_intersection | exact GlobalTheory.CompanionTheory.Ar.PB.combLine_intersection | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.combLine_intersection <;> assumption)
end
end
