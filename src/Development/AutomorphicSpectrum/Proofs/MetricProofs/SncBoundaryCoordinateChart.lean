module

public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncBoundaryCoordinateChart
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncBoundaryCoordinateChart
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric

theorem bdry_snc_chart :
    ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X)
      (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X),
      IsSection A L s → IsSNC A L s m W → ∀ x,
        ∃ ψ : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ ∧ x ∈ ψ.source ∧
          ∃ S : Finset (Fin e), ∀ y ∈ ψ.source, (y ∈ bdry s ↔ ∃ i ∈ S, ψ y i = 0) := by
  classical
  intro e X _ A L s nb m W hs hsnc x
  obtain ⟨ψ, hψ, hx, hsub, σ, -, -, u, -, hu, hfac⟩ := hsnc x
  refine ⟨ψ, hψ, hx, Finset.univ.filter (fun i => ∃ k, σ k = some i ∧ m k ≠ 0), ?_⟩
  intro y hy
  have hglue := hs.2 x y y ⟨hsub hy, L.mem_U y⟩
  have hzero : s y y = 0 ↔ s x y = 0 := by
    have e1 : Real.exp (-L.φ x y) ≠ 0 := (Real.exp_pos _).ne'
    have e2 : Real.exp (-L.φ y y) ≠ 0 := (Real.exp_pos _).ne'
    constructor
    · intro h
      rw [h, norm_zero, zero_mul] at hglue
      exact norm_eq_zero.mp ((mul_eq_zero.mp hglue).resolve_right e1)
    · intro h
      rw [h, norm_zero, zero_mul] at hglue
      exact norm_eq_zero.mp ((mul_eq_zero.mp hglue.symm).resolve_right e2)
  have hmem : y ∈ bdry s ↔ s y y = 0 := Iff.rfl
  rw [hmem, hzero, hfac y hy, mul_eq_zero, or_iff_right (hu y hy), Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    cases hσ : σ k with
    | none => simp [hσ] at hk
    | some i =>
      simp only [hσ] at hk
      have hm : m k ≠ 0 := by
        intro h
        rw [h, pow_zero] at hk
        exact one_ne_zero hk
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, k, hσ, hm⟩, pow_eq_zero_iff hm |>.mp hk⟩
  · rintro ⟨i, hi, h0⟩
    obtain ⟨k, hk, hm⟩ := (Finset.mem_filter.mp hi).2
    refine ⟨k, Finset.mem_univ k, ?_⟩
    simp only [hk]
    rw [h0, zero_pow hm]

end GlobalTheory.CompanionTheory.Metric
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncBoundaryCoordinateChartStatement
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_boundary_coordinate_chart : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsSection A L s → IsSNC A L s m W → ∀ x, ∃ ψ : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ ∧ x ∈ ψ.source ∧ ∃ S : Finset (Fin e), ∀ y ∈ ψ.source, (y ∈ bdry s ↔ ∃ i ∈ S, ψ y i = 0) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.bdry_snc_chart | exact GlobalTheory.CompanionTheory.Metric.bdry_snc_chart | (intros; apply GlobalTheory.CompanionTheory.Metric.bdry_snc_chart <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothOnOfChartComposition
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothOnOfChartComposition
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric

theorem smoothOn_comp_compatChart (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (O : Set (Fin e → ℂ)) (G : (Fin e → ℂ) → ℝ)
    (hψ : IsCompatChart A ψ) (hO : IsOpen O) (_hOt : O ⊆ ψ.target)
    (hG : ContDiffOn ℝ ∞ G O) : A.SmoothOn (ψ.source ∩ ψ ⁻¹' O) (G ∘ ψ) := by
  intro j y hy
  obtain ⟨hyt, hys, hyO⟩ := hy
  have han : AnalyticAt ℂ (ψ ∘ (A.chart j).symm) y := (hψ j).1 y ⟨hyt, hys⟩
  have hτ : ContDiffAt ℝ ∞ (ψ ∘ (A.chart j).symm) y :=
    (han.restrictScalars (𝕜 := ℝ)).contDiffAt.of_le le_top
  have hGat : ContDiffAt ℝ ∞ G ((ψ ∘ (A.chart j).symm) y) :=
    hG.contDiffAt (hO.mem_nhds hyO)
  exact (hGat.comp y hτ).contDiffWithinAt

theorem smoothOn_comp_compatChart' : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (O : Set (Fin e → ℂ)) (G : (Fin e → ℂ) → ℝ), IsCompatChart A ψ → IsOpen O → O ⊆ ψ.target → ContDiffOn ℝ ∞ G O → A.SmoothOn (ψ.source ∩ ψ ⁻¹' O) (G ∘ ψ) :=
  fun e X _ A ψ O G h1 h2 h3 h4 => smoothOn_comp_compatChart e X A ψ O G h1 h2 h3 h4

end GlobalTheory.CompanionTheory.Metric
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothOnOfChartCompositionStatement
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOn_of_chart_composition : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (O : Set (Fin e → ℂ)) (G : (Fin e → ℂ) → ℝ), IsCompatChart A ψ → IsOpen O → O ⊆ ψ.target → ContDiffOn ℝ ∞ G O → A.SmoothOn (ψ.source ∩ ψ ⁻¹' O) (G ∘ ψ) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.smoothOn_comp_compatChart' | exact GlobalTheory.CompanionTheory.Metric.smoothOn_comp_compatChart' | (intros; apply GlobalTheory.CompanionTheory.Metric.smoothOn_comp_compatChart' <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviFlatSeparatelyHarmonic
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviFlatSeparatelyHarmonic
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric

theorem harmonicAt_update_of_levi_eq_zero :
    ∀ (n : ℕ) (φ : (Fin n → ℂ) → ℝ) (O : Set (Fin n → ℂ)), IsOpen O → ContDiffOn ℝ ∞ φ O →
      (∀ z ∈ O, ∀ w, levi φ z w = 0) → ∀ z ∈ O, ∀ i,
        InnerProductSpace.HarmonicAt (fun t : ℂ => φ (Function.update z i t)) (z i) := by
  intro n φ O hO hφ hl z hz i
  set e : Fin n → ℂ := Pi.single i 1 with he
  let L : ℂ →L[ℝ] (Fin n → ℂ) := ((ContinuousLinearMap.id ℂ ℂ).smulRight e).restrictScalars ℝ
  have hLw : ∀ w : ℂ, L w = w • e := fun _ => rfl
  set z0 : Fin n → ℂ := Function.update z i 0 with hz0
  have hupd : ∀ t : ℂ, Function.update z i t = z0 + t • e := by
    intro t
    funext j
    by_cases h : j = i
    · subst h
      simp [hz0, he]
    · simp [hz0, he, h]
  have hline : ∀ t : ℂ, HasFDerivAt (fun w : ℂ => z0 + w • e) L t := fun t =>
    L.hasFDerivAt.const_add z0
  have hcont : Continuous (fun t : ℂ => z0 + t • e) := by fun_prop
  have hU : IsOpen ((fun t : ℂ => z0 + t • e) ⁻¹' O) := hO.preimage hcont
  have hzU : z i ∈ (fun t : ℂ => z0 + t • e) ⁻¹' O := by
    show z0 + z i • e ∈ O
    rw [← hupd]
    simpa using hz
  have hφ2 : ∀ y ∈ O, ContDiffAt ℝ 2 φ y := fun y hy =>
    ((hφ y hy).contDiffAt (hO.mem_nhds hy)).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | simp)
  have hlap : ∀ t ∈ (fun t : ℂ => z0 + t • e) ⁻¹' O,
      Laplacian.laplacian (fun t : ℂ => φ (z0 + t • e)) t = 0 := by
    intro t ht
    have hy : z0 + t • e ∈ O := ht
    have h1 : fderiv ℝ (fun w : ℂ => φ (z0 + w • e)) =ᶠ[𝓝 t]
        fun w : ℂ => (fderiv ℝ φ (z0 + w • e)).comp L := by
      filter_upwards [hU.mem_nhds ht] with w hw
      exact (((hφ2 _ hw).differentiableAt (by simp)).hasFDerivAt.comp w (hline w)).fderiv
    have hD : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) (z0 + t • e)) (z0 + t • e) :=
      (((hφ2 _ hy).fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt
    have h2 := ((hD.comp t (hline t)).clm_comp (hasFDerivAt_const L t)).fderiv
    simp only [Function.comp_def] at h2
    have hle := hl _ hy e
    unfold levi at hle
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
    simp only [iteratedFDeriv_two_apply]
    rw [h1.fderiv_eq, h2]
    simp [hLw]
    linarith
  rw [show (fun t : ℂ => φ (Function.update z i t)) = fun t : ℂ => φ (z0 + t • e) from
    funext fun t => by rw [hupd]]
  refine ⟨?_, ?_⟩
  · have hA : ContDiffAt ℝ 2 (fun t : ℂ => z0 + t • e) (z i) := by
      have : ContDiff ℝ 2 (fun t : ℂ => z0 + L t) := contDiff_const.add L.contDiff
      exact this.contDiffAt
    exact (hφ2 _ hzU).comp (z i) hA
  · filter_upwards [hU.mem_nhds hzU] with t ht
    simpa using hlap t ht

end GlobalTheory.CompanionTheory.Metric
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviFlatSeparatelyHarmonicStatement
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_flat_separately_harmonic : ∀ (n : ℕ) (φ : (Fin n → ℂ) → ℝ) (O : Set (Fin n → ℂ)), IsOpen O → ContDiffOn ℝ ∞ φ O → (∀ z ∈ O, ∀ w, levi φ z w = 0) → ∀ z ∈ O, ∀ i, InnerProductSpace.HarmonicAt (fun t : ℂ => φ (Function.update z i t)) (z i) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.harmonicAt_update_of_levi_eq_zero | exact GlobalTheory.CompanionTheory.Metric.harmonicAt_update_of_levi_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Metric.harmonicAt_update_of_levi_eq_zero <;> assumption)
end
end
