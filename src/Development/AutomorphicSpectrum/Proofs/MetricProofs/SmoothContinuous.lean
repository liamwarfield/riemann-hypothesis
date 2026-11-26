module

public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XAnConj
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularWeightMonotoneRegularization
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HoloOnDivCongr

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugationInvariantSingularPotential
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugationInvariantSingularPotential
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem an_conj_symmetrise : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Θ : LocPot X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → IsPotential A Θ → IsPosPot A Θ → ∀ (c : X → X), Continuous c → (∀ x, c (c x) = x) → (∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z)))) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source))) → (∀ y, c y ∈ bdry s ↔ y ∈ bdry s) → (∀ y, rW L s (c y) = rW L s y) → ∀ (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C t₀ : ℝ), IsPotential A th → (∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, th.φ (c x) (c y) - th.φ x y = (G y).re) → (∀ y ∉ bdry s, ph (c y) = ph y) → IsRegFamily A Θ L s th ph phT C t₀ → IsRegFamilyC2 A s ph phT → ∃ C' t₀' : ℝ, IsRegFamily A Θ L s th ph (fun t y => (phT t y + phT t (c y)) / 2) C' t₀' ∧ IsRegFamilyC2 A s ph fun t y => (phT t y + phT t (c y)) / 2 :=
  @PositivityTheory.Xgp.t_an_conj

end GlobalTheory.CompanionTheory.Ar.PB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugationInvariantSingularPotentialStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugation_invariant_singular_potential : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Θ : LocPot X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → IsPotential A Θ → IsPosPot A Θ → ∀ (c : X → X), Continuous c → (∀ x, c (c x) = x) → (∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z)))) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source))) → (∀ y, c y ∈ bdry s ↔ y ∈ bdry s) → (∀ y, rW L s (c y) = rW L s y) → ∀ (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C t₀ : ℝ), IsPotential A th → (∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, th.φ (c x) (c y) - th.φ x y = (G y).re) → (∀ y ∉ bdry s, ph (c y) = ph y) → IsRegFamily A Θ L s th ph phT C t₀ → IsRegFamilyC2 A s ph phT → ∃ C' t₀' : ℝ, IsRegFamily A Θ L s th ph (fun t y => (phT t y + phT t (c y)) / 2) C' t₀' ∧ IsRegFamilyC2 A s ph fun t y => (phT t y + phT t (c y)) / 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.an_conj_symmetrise | exact GlobalTheory.CompanionTheory.Ar.PB.an_conj_symmetrise | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.an_conj_symmetrise <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftSystemRealStructure
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftSystemRealStructure
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj

section Holo

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

theorem pot_holoOn_mono {V W : Set X} {g : X → ℂ} (h : A.HoloOn V g) (hW : W ⊆ V) :
    A.HoloOn W g :=
  fun j w hw => h j w ⟨hw.1, hW hw.2⟩

theorem pot_holoOn_continuousOn {V : Set X} (hV : IsOpen V) {g : X → ℂ} (h : A.HoloOn V g) :
    ContinuousOn g V := by
  intro y hy
  obtain ⟨j, hj⟩ := A.cover y
  have hw : A.chart j y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' V :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hy⟩
  have h1 := (h j _ hw).continuousAt
  have h2 : ContinuousAt (A.chart j) y := (A.chart j).continuousAt hj
  have h3 : ContinuousAt (fun y' => (g ∘ (A.chart j).symm) (A.chart j y')) y :=
    ContinuousAt.comp (g := g ∘ (A.chart j).symm) h1 h2
  refine (h3.congr ?_).continuousWithinAt
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y' hy'
  simp [(A.chart j).left_inv hy']

theorem pot_holoOn_sub_add {V : Set X} {g₁ g₂ g₃ : X → ℂ} (h₁ : A.HoloOn V g₁)
    (h₂ : A.HoloOn V g₂) (h₃ : A.HoloOn V g₃) :
    A.HoloOn V (fun y => g₁ y - g₂ y + g₃ y) :=
  fun j w hw => ((h₁ j w hw).sub (h₂ j w hw)).add (h₃ j w hw)

theorem pot_holoOn_div {V : Set X} {g₁ g₂ : X → ℂ} (h₁ : A.HoloOn V g₁) (h₂ : A.HoloOn V g₂)
    (hne : ∀ y ∈ V, g₂ y ≠ 0) : A.HoloOn V (fun y => g₁ y / g₂ y) :=
  fun j w hw => (h₁ j w hw).div (h₂ j w hw) (hne _ hw.2)

theorem pot_holoOn_sum_log {K : Type} [Fintype K] {V : Set X} {g : K → X → ℂ} (m : K → ℤ)
    (r : K → ℝ) (h : ∀ k, A.HoloOn V (g k)) (hs : ∀ k, ∀ y ∈ V, g k y ∈ Complex.slitPlane) :
    A.HoloOn V (fun y => ∑ k, (m k : ℂ) * (Complex.log (g k y) + (r k : ℂ))) := by
  intro j w hw
  have : ∀ k, AnalyticAt ℂ (fun z => (m k : ℂ) *
      (Complex.log (g k ((A.chart j).symm z)) + (r k : ℂ))) w := fun k =>
    analyticAt_const.mul ((AnalyticAt.clog (h k j w hw) (hs k _ hw.2)).add analyticAt_const)
  exact Finset.analyticAt_fun_sum _ fun k _ => this k

end Holo

theorem pot_re_sum_log {K : Type} [Fintype K] (m : K → ℤ) (u v : K → ℂ) (hu : ∀ k, u k ≠ 0)
    (hv : ∀ k, v k ≠ 0) :
    (∑ k, (m k : ℂ) * (Complex.log (u k / v k) + ((Real.log ‖v k‖ : ℝ) : ℂ))).re =
      ∑ k, (m k : ℝ) * Real.log ‖u k‖ := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : (Complex.log (u k / v k) + ((Real.log ‖v k‖ : ℝ) : ℂ)).re = Real.log ‖u k‖ := by
    rw [Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
      Real.log_div (norm_ne_zero_iff.2 (hu k)) (norm_ne_zero_iff.2 (hv k))]
    ring
  simp [Complex.mul_re, h1]

theorem pot_log_h_conj {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (f : HermLine ι)
    (hf : IsConjInvariantH f) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) {a : K → ℂ}
    (ha : ∀ k, a k ≠ 0) :
    Real.log (f.h (fun p => a p.1 * cj z p)) - Real.log (f.h z) =
      ∑ k, (f.a k : ℝ) * Real.log ‖a k‖ := by
  have hP : ∀ k ∈ (Finset.univ : Finset K), ‖a k‖ ^ f.a k ≠ 0 := fun k _ =>
    (zpow_pos (norm_pos_iff.mpr (ha k)) _).ne'
  have hP' : (∏ k, ‖a k‖ ^ f.a k) ≠ 0 := Finset.prod_ne_zero_iff.2 hP
  rw [f.smul a (cj z) ha, show f.h (cj z) = f.h z from hf z,
    Real.log_mul hP' (f.pos z hz).ne', Real.log_prod hP]
  simp [Real.log_zpow]

theorem pot_conj_pluriharmonic : ∀ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {P : Ideal (MRing ι)} {U : X → Set X} {lift : X → X → (Σ k, ι k) → ℂ}, IsLiftSys A P U lift → ∀ (c : X → X), (∀ x, SameOrbit (lift (c x) (c x)) (cj (lift x x))) → Continuous c → (∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z)))) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source))) → ∀ (f : HermLine ι), IsConjInvariantH f → ∀ (th : LocPot X), (∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, Real.log (f.h (lift x y)) - th.φ x y = (G y).re) → ∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, th.φ (c x) (c y) - th.φ x y = (G y).re := by
  intro K _ ι _ e X _ A P U lift hL c horb hcc hanti f hf th hth x
  obtain ⟨hUo, hUm, hUh, hUpts, hUor, -, -, -⟩ := hL
  choose i hi using (hUpts x x (hUm x)).1
  obtain ⟨V₁, hV₁o, hxV₁, G₁, hG₁, hφ₁⟩ := hth x
  obtain ⟨V₂, hV₂o, hxV₂, G₂, hG₂, hφ₂⟩ := hth (c x)

  have horbit : ∀ y ∈ U x, c y ∈ U (c x) → ∃ a : K → ℂ, (∀ k, a k ≠ 0) ∧
      lift (c x) (c y) = fun p => a p.1 * cj (lift x y) p := fun y hy hcy =>
    sameOrbit_trans (sameOrbit_trans (hUor (c x) (c y) (c y) ⟨hcy, hUm (c y)⟩) (horb y))
      (sameOrbit_cj (hUor y x y ⟨hUm y, hy⟩))

  let b : K → X → ℂ := fun k y =>
    starRingEnd ℂ (lift (c x) (c y) ⟨k, i k⟩) / lift x y ⟨k, i k⟩
  let D : K → Set X := fun k => U x ∩ (fun y => lift x y ⟨k, i k⟩) ⁻¹' {0}ᶜ
  have hDo : ∀ k, IsOpen (D k) := fun k =>
    (pot_holoOn_continuousOn (hUo x) (hUh x _)).isOpen_inter_preimage (hUo x) isOpen_compl_singleton
  let W₁ : Set X := (U x ∩ c ⁻¹' U (c x)) ∩ ⋂ k, D k
  have hW₁o : IsOpen W₁ :=
    ((hUo x).inter ((hUo (c x)).preimage hcc)).inter (isOpen_iInter_of_finite hDo)
  have hxW₁ : x ∈ W₁ :=
    ⟨⟨hUm x, hUm (c x)⟩, Set.mem_iInter.2 fun k => ⟨hUm x, hi k⟩⟩
  have hden : ∀ y ∈ W₁, ∀ k, lift x y ⟨k, i k⟩ ≠ 0 := fun y hy k =>
    (Set.mem_iInter.1 hy.2 k).2

  have hba : ∀ y ∈ W₁, ∀ a : K → ℂ, lift (c x) (c y) = (fun p => a p.1 * cj (lift x y) p) →
      ∀ k, b k y = starRingEnd ℂ (a k) := fun y hy a ha k => by
    change starRingEnd ℂ (lift (c x) (c y) ⟨k, i k⟩) / lift x y ⟨k, i k⟩ = _
    rw [ha]
    simp only [cj, map_mul, Complex.conj_conj]
    exact mul_div_cancel_right₀ _ (hden y hy k)
  have hbne : ∀ y ∈ W₁, ∀ k, b k y ≠ 0 := fun y hy k => by
    obtain ⟨a, ha, hl⟩ := horbit y hy.1.1 hy.1.2
    rw [hba y hy a hl k]
    simpa using ha k
  have hbH : ∀ k, A.HoloOn W₁ (b k) := fun k =>
    pot_holoOn_div
      (pot_holoOn_mono (GlobalTheory.T.holomorphic_conjugate_pullback c hcc hanti (hUh (c x) ⟨k, i k⟩)) fun y hy => hy.1.2)
      (pot_holoOn_mono (hUh x ⟨k, i k⟩) fun y hy => hy.1.1) fun y hy => hden y hy k
  have hqH : ∀ k, A.HoloOn W₁ (fun y => b k y / b k x) := fun k =>
    pot_holoOn_div (hbH k) (fun j w _ => analyticAt_const) fun _ _ => hbne x hxW₁ k
  let B : K → Set X := fun k => W₁ ∩ (fun y => b k y / b k x) ⁻¹' Metric.ball 1 1
  have hBo : ∀ k, IsOpen (B k) := fun k =>
    (pot_holoOn_continuousOn hW₁o (hqH k)).isOpen_inter_preimage hW₁o Metric.isOpen_ball
  let W₂ : Set X := W₁ ∩ ⋂ k, B k
  let V : Set X := (W₂ ∩ V₁) ∩ c ⁻¹' V₂
  have hVo : IsOpen V :=
    ((hW₁o.inter (isOpen_iInter_of_finite hBo)).inter hV₁o).inter (hV₂o.preimage hcc)
  have hVW : V ⊆ W₁ := fun y hy => hy.1.1.1
  have hxV : x ∈ V := by
    refine ⟨⟨⟨hxW₁, Set.mem_iInter.2 fun k => ⟨hxW₁, ?_⟩⟩, hxV₁⟩, hxV₂⟩
    simp [div_self (hbne x hxW₁ k)]
  have hslit : ∀ k, ∀ y ∈ V, b k y / b k x ∈ Complex.slitPlane := fun k y hy => by
    have h1 : b k y / b k x ∈ Metric.ball (1 : ℂ) 1 := (Set.mem_iInter.1 hy.1.1.2 k).2
    have h2 : ‖b k y / b k x - 1‖ < 1 := by simpa [dist_eq_norm] using h1
    simpa using Complex.mem_slitPlane_of_norm_lt_one h2
  refine ⟨V, hVo, hxV,
    fun y => G₁ y - starRingEnd ℂ (G₂ (c y)) +
      ∑ k, (f.a k : ℂ) * (Complex.log (b k y / b k x) + ((Real.log ‖b k x‖ : ℝ) : ℂ)), ?_, ?_⟩
  · refine pot_holoOn_sub_add (pot_holoOn_mono hG₁ fun y hy => hy.1.2)
      (pot_holoOn_mono (GlobalTheory.T.holomorphic_conjugate_pullback c hcc hanti hG₂) fun y hy => hy.2) ?_
    exact pot_holoOn_sum_log f.a _ (fun k => pot_holoOn_mono (hqH k) hVW) fun k => hslit k
  · intro y hy
    have hyW := hVW hy
    obtain ⟨a, ha, hl⟩ := horbit y hyW.1.1 hyW.1.2
    have e₁ := hφ₁ y hy.1.2
    have e₂ := hφ₂ (c y) hy.2
    have e₃ := pot_log_h_conj f hf (hUpts x y hyW.1.1).1 ha
    rw [← hl] at e₃
    have e₄ := pot_re_sum_log f.a (fun k => b k y) (fun k => b k x) (hbne y hyW) (hbne x hxW₁)
    have e₅ : ∑ k, (f.a k : ℝ) * Real.log ‖b k y‖ = ∑ k, (f.a k : ℝ) * Real.log ‖a k‖ :=
      Finset.sum_congr rfl fun k _ => by rw [hba y hyW a hl k, RCLike.norm_conj]
    simp only [Complex.add_re, Complex.sub_re, Complex.conj_re]
    rw [e₄, e₅, ← e₃]
    linarith

end GlobalTheory.CompanionTheory.Ar.PB.Cj
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftSystemRealStructureStatement
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_system_real_structure : ∀ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {P : Ideal (MRing ι)} {U : X → Set X} {lift : X → X → (Σ k, ι k) → ℂ}, IsLiftSys A P U lift → ∀ (c : X → X), (∀ x, SameOrbit (lift (c x) (c x)) (cj (lift x x))) → Continuous c → (∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z)))) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source))) → ∀ (f : HermLine ι), IsConjInvariantH f → ∀ (th : LocPot X), (∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, Real.log (f.h (lift x y)) - th.φ x y = (G y).re) → ∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, th.φ (c x) (c y) - th.φ x y = (G y).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Cj.pot_conj_pluriharmonic | exact GlobalTheory.CompanionTheory.Ar.PB.Cj.pot_conj_pluriharmonic | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Cj.pot_conj_pluriharmonic <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugationAntiholomorphicCharts
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticOfImmersionComposition
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticOfImmersionComposition
namespace GlobalTheory.CompanionTheory.Metric.Rigid

theorem analyticAt_of_comp_immersion {e : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (F : (Fin e → ℂ) → Fin e → ℂ) (ψ : (Fin e → ℂ) → V)
    (H : (Fin e → ℂ) → V) (y₀ : Fin e → ℂ) (hψ : AnalyticAt ℂ ψ (F y₀))
    (hker : (fderiv ℂ ψ (F y₀)).ker = ⊥) (hH : AnalyticAt ℂ H y₀) (hF : ContinuousAt F y₀)
    (hEq : ∀ᶠ y in nhds y₀, ψ (F y) = H y) : AnalyticAt ℂ F y₀ := by
  classical
  obtain ⟨P₀, hP₀⟩ := ((fderiv ℂ ψ (F y₀) : (Fin e → ℂ) →L[ℂ] V) :
    (Fin e → ℂ) →ₗ[ℂ] V).exists_leftInverse_of_injective hker
  let P : V →L[ℂ] (Fin e → ℂ) := LinearMap.toContinuousLinearMap P₀
  have hPL : P.comp (fderiv ℂ ψ (F y₀)) = ContinuousLinearMap.id ℂ _ := by
    ext1 v
    exact LinearMap.congr_fun hP₀ v
  have hψd : HasFDerivAt ψ (fderiv ℂ ψ (F y₀)) (F y₀) := hψ.differentiableAt.hasFDerivAt
  have hgd : HasFDerivAt (fun x => P (ψ x))
      ((ContinuousLinearEquiv.refl ℂ (Fin e → ℂ) : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ))) (F y₀) := by
    have h1 := P.hasFDerivAt.comp (F y₀) hψd
    rw [hPL] at h1
    simpa using h1
  have hga : AnalyticAt ℂ (fun x => P (ψ x)) (F y₀) := (P.analyticAt _).comp hψ
  have hgc : ContDiffAt ℂ (⊤ : WithTop ℕ∞) (fun x => P (ψ x)) (F y₀) := hga.contDiffAt
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  have hφa := (hgc.to_localInverse hgd hn).analyticAt
  have hleft := (hgc.hasStrictFDerivAt' hgd hn).eventually_left_inverse
  have hH0 : ψ (F y₀) = H y₀ := hEq.self_of_nhds
  have hev : (fun y => hgc.localInverse hgd hn (P (H y))) =ᶠ[nhds y₀] F := by
    filter_upwards [hF.tendsto.eventually hleft, hEq] with y h1 h2
    rw [← h2]
    exact h1
  have hcomp : AnalyticAt ℂ (fun y => hgc.localInverse hgd hn (P (H y))) y₀ := by
    have h0 : AnalyticAt ℂ (hgc.localInverse hgd hn) (P (H y₀)) := by
      rw [← hH0]
      exact hφa
    have hPH : AnalyticAt ℂ (fun y => P (H y)) y₀ := (P.analyticAt (H y₀)).comp hH
    exact h0.comp_of_eq hPH rfl
  exact hcomp.congr hev

end GlobalTheory.CompanionTheory.Metric.Rigid
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticOfImmersionCompositionStatement
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_of_immersion_composition : ∀ {e : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (F : (Fin e → ℂ) → Fin e → ℂ) (ψ : (Fin e → ℂ) → V) (H : (Fin e → ℂ) → V) (y₀ : Fin e → ℂ), AnalyticAt ℂ ψ (F y₀) → (fderiv ℂ ψ (F y₀)).ker = ⊥ → AnalyticAt ℂ H y₀ → ContinuousAt F y₀ → (∀ᶠ y in nhds y₀, ψ (F y) = H y) → AnalyticAt ℂ F y₀ := by
  first | exact @GlobalTheory.CompanionTheory.Metric.Rigid.analyticAt_of_comp_immersion | exact GlobalTheory.CompanionTheory.Metric.Rigid.analyticAt_of_comp_immersion | (intros; apply GlobalTheory.CompanionTheory.Metric.Rigid.analyticAt_of_comp_immersion <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugationAntiholomorphicCharts
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj

section Helpers

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem affCoord_eq_of_orbit (p : (k : K) → ι k) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    affCoord p z = affCoord p z' := by
  obtain ⟨c, hc, rfl⟩ := h
  funext q
  simp only [affCoord]
  exact mul_div_mul_left _ _ (hc q.1)

theorem affCoord_cj (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) :
    affCoord p (cj z) = cj (affCoord p z) := by
  funext q
  simp [affCoord, cj, map_div₀]

theorem ne_zero_of_orbit_cj {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z (cj z')) {q : Σ k, ι k}
    (hq : z q ≠ 0) : z' q ≠ 0 := by
  obtain ⟨c, -, rfl⟩ := h
  intro h0
  exact hq (by simp [cj, h0])

theorem analyticAt_affCoord {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → (Σ k, ι k) → ℂ} {a : E} (p : (k : K) → ι k)
    (hf : ∀ q, AnalyticAt ℂ (fun y => f y q) a) (h0 : ∀ k, f a ⟨k, p k⟩ ≠ 0) :
    AnalyticAt ℂ (fun y => affCoord p (f y)) a := by
  rw [analyticAt_pi_iff]
  intro q
  exact (hf q).div (hf ⟨q.1, p q.1⟩) (h0 q.1)

theorem analyticAt_star_comp {e : ℕ} {ψ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {w : Fin e → ℂ}
    (h : AnalyticAt ℂ ψ w) : AnalyticAt ℂ (star ∘ ψ ∘ star) (star w) := by
  refine GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 ?_
  have hs : Filter.Tendsto (star : (Fin e → ℂ) → Fin e → ℂ) (𝓝 (star w)) (𝓝 w) := by
    simpa using (continuous_star.tendsto (star w))
  filter_upwards [hs.eventually h.eventually_analyticAt] with v hv
  simpa using hv.differentiableAt.star_star

theorem ker_fderiv_star_comp {e : ℕ} {ψ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {w : Fin e → ℂ}
    (h : DifferentiableAt ℂ ψ w) (hk : (fderiv ℂ ψ w).ker = ⊥) :
    (fderiv ℂ (star ∘ ψ ∘ star) (star w)).ker = ⊥ := by
  rw [h.hasFDerivAt.star_star.fderiv, eq_bot_iff]
  intro v hv
  have hv' : star (fderiv ℂ ψ w (star v)) = 0 := by simpa using hv
  have h1 : fderiv ℂ ψ w (star v) = 0 := by simpa using hv'
  have h2 : star v ∈ (fderiv ℂ ψ w).ker := by simpa using h1
  rw [hk] at h2
  have h3 : star v = 0 := by simpa using h2
  simpa using h3

end Helpers

theorem conj_analytic : ∀ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {P : Ideal (MRing ι)} {U : X → Set X} {lift : X → X → (Σ k, ι k) → ℂ}, IsLiftSys A P U lift → ∀ (c : X → X), (∀ x, SameOrbit (lift (c x) (c x)) (cj (lift x x))) → Continuous c → ∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z)))) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source)) := by
  intro K _ ι _ e X _ A P U lift hL c hc hcc j k w hw
  obtain ⟨hUo, hUm, hH, hM, hCp, -, -, hIm⟩ := hL
  obtain ⟨hw1, hw2⟩ := hw
  have hw2' : c ((A.chart j).symm w) ∈ (A.chart k).source := hw2
  generalize hx₀ : (A.chart j).symm w = x₀ at hw2'
  generalize hx₁ : c x₀ = x₁ at hw2'
  choose p hp using (hM x₁ x₁ (hUm x₁)).1
  have hp0 : ∀ b, lift x₀ x₀ ⟨b, p b⟩ ≠ 0 := fun b =>
    ne_zero_of_orbit_cj (hx₁ ▸ hc x₀) (by subst hx₁; exact hp b)
  have hsym₁ : (A.chart k).symm (A.chart k x₁) = x₁ := (A.chart k).left_inv hw2'
  have hψ : AnalyticAt ℂ (fun w' => affCoord p (lift x₁ ((A.chart k).symm w'))) (A.chart k x₁) := by
    refine analyticAt_affCoord p (fun q => ?_) (fun b => ?_)
    · exact hH x₁ q k (A.chart k x₁) ⟨(A.chart k).map_source hw2', by simpa [hsym₁] using hUm x₁⟩
    · simpa [hsym₁] using hp b
  have hker := hIm x₁ p hp k hw2'
  have hHa : AnalyticAt ℂ (fun y => affCoord p (lift x₀ ((A.chart j).symm y))) w := by
    refine analyticAt_affCoord p (fun q => ?_) (fun b => ?_)
    · exact hH x₀ q j w ⟨hw1, by simpa [Set.mem_preimage, hx₀] using hUm x₀⟩
    · simpa [hx₀] using hp0 b
  have hsc : ContinuousAt (A.chart j).symm w := (A.chart j).continuousAt_symm hw1
  have hcs : ContinuousAt (fun y => c ((A.chart j).symm y)) w := hcc.continuousAt.comp hsc
  have hFc : ContinuousAt (fun z => star (A.chart k (c ((A.chart j).symm z)))) w := by
    have h1 : ContinuousAt (A.chart k) (c ((A.chart j).symm w)) := by
      rw [hx₀, hx₁]; exact (A.chart k).continuousAt hw2'
    exact continuous_star.continuousAt.comp (ContinuousAt.comp (f := fun y => c ((A.chart j).symm y)) h1 hcs)
  have hFw : star (A.chart k (c ((A.chart j).symm w))) = star (A.chart k x₁) := by
    rw [hx₀, hx₁]
  have e1 : ∀ᶠ y in 𝓝 w, (A.chart j).symm y ∈ U x₀ :=
    hsc ((hUo x₀).mem_nhds (by rw [hx₀]; exact hUm x₀))
  have e2 : ∀ᶠ y in 𝓝 w, c ((A.chart j).symm y) ∈ (A.chart k).source ∩ U x₁ :=
    hcs (((A.chart k).open_source.inter (hUo x₁)).mem_nhds (by
      change c ((A.chart j).symm w) ∈ _
      rw [hx₀, hx₁]; exact ⟨hw2', hUm x₁⟩))
  refine GlobalTheory.T.analytic_of_immersion_composition (fun z => star (A.chart k (c ((A.chart j).symm z))))
    (star ∘ (fun w' => affCoord p (lift x₁ ((A.chart k).symm w'))) ∘ star)
    (fun y => affCoord p (lift x₀ ((A.chart j).symm y))) w ?_ ?_ hHa hFc ?_
  · rw [hFw]; exact analyticAt_star_comp hψ
  · rw [hFw]; exact ker_fderiv_star_comp hψ.differentiableAt hker
  · filter_upwards [e1, e2] with y h1 h2
    obtain ⟨h2s, h2u⟩ := h2
    generalize hy' : (A.chart j).symm y = y' at h1 h2s h2u
    have ho1 : SameOrbit (lift x₁ (c y')) (lift (c y') (c y')) := hCp _ _ _ ⟨h2u, hUm _⟩
    have ho2 : SameOrbit (lift y' y') (lift x₀ y') := hCp _ _ _ ⟨hUm _, h1⟩
    have ho : SameOrbit (lift x₁ (c y')) (cj (lift x₀ y')) :=
      sameOrbit_trans ho1 (sameOrbit_trans (hc y') (sameOrbit_cj ho2))
    have hst : (star : ((Σ k, ι k) → ℂ) → _) (cj (affCoord p (lift x₀ y'))) = affCoord p (lift x₀ y') := by
      funext q; simp [cj]
    simp only [Function.comp, star_star, hy', (A.chart k).left_inv h2s]
    rw [affCoord_eq_of_orbit p ho, affCoord_cj, hst]

end GlobalTheory.CompanionTheory.Ar.PB.Cj
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugationAntiholomorphicChartsStatement
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugation_antiholomorphic_charts : ∀ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {P : Ideal (MRing ι)} {U : X → Set X} {lift : X → X → (Σ k, ι k) → ℂ}, IsLiftSys A P U lift → ∀ (c : X → X), (∀ x, SameOrbit (lift (c x) (c x)) (cj (lift x x))) → Continuous c → ∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z)))) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Cj.conj_analytic | exact GlobalTheory.CompanionTheory.Ar.PB.Cj.conj_analytic | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Cj.conj_analytic <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftSystemComplexConjugation
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftSystemComplexConjugation
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj

open Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem sameOrbit_cross {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (k : K) (a b : ι k) :
    z ⟨k, a⟩ * z' ⟨k, b⟩ = z ⟨k, b⟩ * z' ⟨k, a⟩ := by
  obtain ⟨c, -, rfl⟩ := h
  simp only
  ring

theorem sameOrbit_of_cross {z z' : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0)
    (h : ∀ (k : K) (a b : ι k), z ⟨k, a⟩ * z' ⟨k, b⟩ = z ⟨k, b⟩ * z' ⟨k, a⟩) :
    SameOrbit z z' := by
  choose j hj using hz'
  refine ⟨fun k => z ⟨k, j k⟩ / z' ⟨k, j k⟩, fun k => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hz k
    refine div_ne_zero (fun h0 => ?_) (hj k)
    have := h k i (j k)
    rw [h0, zero_mul] at this
    exact (mul_ne_zero hi (hj k)) this
  · funext ⟨k, a⟩
    have := h k a (j k)
    have hjk := hj k
    simp only
    field_simp
    linear_combination this

theorem continuousAt_of_holo {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g) {y : X} (hy : y ∈ U) : ContinuousAt g y := by
  obtain ⟨j, hj⟩ := A.cover y
  have h1 : ContinuousAt ((g ∘ (A.chart j).symm) ∘ A.chart j) y :=
    ContinuousAt.comp (g := g ∘ (A.chart j).symm)
      (hg j _ ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hy⟩).continuousAt
      ((A.chart j).continuousAt hj)
  refine h1.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
  simp [Function.comp, (A.chart j).left_inv hz]

theorem exists_conj_of_isLiftSys {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] {A : FinHolAtlas e X} {P : Ideal (MRing ι)} {U : X → Set X}
    {lift : X → X → (Σ k, ι k) → ℂ} (hS : IsLiftSys A P U lift) :
    ∃ c : X → X, (∀ x, SameOrbit (lift (c x) (c x)) (cj (lift x x))) ∧ Continuous c ∧
      ∀ x, c (c x) = x := by
  obtain ⟨hU, hmem, hholo, hlift, hcompat, hsurj, hinj, -⟩ := hS
  choose c hc using fun x => hsurj _ (cj_mem_mcPts (hlift x x (hmem x)))
  refine ⟨c, hc, ?_, fun x => ?_⟩
  · refine continuous_iff_ultrafilter.2 fun x F hF => ?_
    obtain ⟨x', -, hx'⟩ := isCompact_univ.ultrafilter_le_nhds (F.map c) (by simp)
    have hcF : Tendsto c F (𝓝 x') := hx'
    have hev : ∀ᶠ y in (F : Filter X), y ∈ U x ∧ c y ∈ U x' :=
      Filter.Eventually.and (hF ((hU x).mem_nhds (hmem x))) (hcF ((hU x').mem_nhds (hmem x')))
    have horb : ∀ᶠ y in (F : Filter X), SameOrbit (lift x' (c y)) (cj (lift x y)) := by
      filter_upwards [hev] with y hy
      exact sameOrbit_trans (hcompat x' (c y) (c y) ⟨hy.2, hmem _⟩)
        (sameOrbit_trans (hc y) (sameOrbit_cj (hcompat y x y ⟨hmem y, hy.1⟩)))
    have hl1 : ∀ p, Tendsto (fun y => lift x' (c y) p) F (𝓝 (lift x' x' p)) := fun p =>
      (continuousAt_of_holo A (hholo x' p) (hmem x')).tendsto.comp hcF
    have hl2 : ∀ p, Tendsto (fun y => cj (lift x y) p) F (𝓝 (cj (lift x x) p)) := fun p =>
      (Complex.continuous_conj.tendsto _).comp
        ((continuousAt_of_holo A (hholo x p) (hmem x)).tendsto.mono_left hF)
    have hcross : ∀ (k : K) (a b : ι k),
        lift x' x' ⟨k, a⟩ * cj (lift x x) ⟨k, b⟩ = lift x' x' ⟨k, b⟩ * cj (lift x x) ⟨k, a⟩ :=
      fun k a b => tendsto_nhds_unique_of_eventuallyEq
        ((hl1 ⟨k, a⟩).mul (hl2 ⟨k, b⟩)) ((hl1 ⟨k, b⟩).mul (hl2 ⟨k, a⟩))
        (horb.mono fun y hy => sameOrbit_cross hy k a b)
    have horb' : SameOrbit (lift x' x') (cj (lift x x)) :=
      sameOrbit_of_cross (hlift x' x' (hmem x')).1 (cj_nonzero (hlift x x (hmem x)).1) hcross
    have hxx : x' = c x := hinj _ _ (sameOrbit_trans horb' (sameOrbit_symm (hc x)))
    exact hxx ▸ hcF
  · refine hinj _ _ (sameOrbit_trans (hc (c x)) ?_)
    have := sameOrbit_cj (hc x)
    rwa [cj_cj] at this

end GlobalTheory.CompanionTheory.Ar.PB.Cj
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftSystemComplexConjugationStatement
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_system_complex_conjugation : ∀ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] {A : FinHolAtlas e X} {P : Ideal (MRing ι)} {U : X → Set X} {lift : X → X → (Σ k, ι k) → ℂ}, IsLiftSys A P U lift → ∃ c : X → X, (∀ x, SameOrbit (lift (c x) (c x)) (cj (lift x x))) ∧ Continuous c ∧ ∀ x, c (c x) = x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Cj.exists_conj_of_isLiftSys | exact GlobalTheory.CompanionTheory.Ar.PB.Cj.exists_conj_of_isLiftSys | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Cj.exists_conj_of_isLiftSys <;> assumption)
end
end

open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.Cj
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem fs_conj (a : K → ℤ) : IsConjInvariantH (fsHerm ι a) := fun z => by
  simp [fsHerm_h, refNorm]

theorem not_mem_top {P : Ideal (MRing ι)} (hP : P = ⊤) (z : (Σ k, ι k) → ℂ) : z ∉ mcPts P := by
  subst hP
  intro h
  have := h.2 1 trivial
  simp at this

theorem sameOrbit_base {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem smooth_continuous {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {f : X → ℝ}
    (hf : A.Smooth f) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x) := by
    have hm : (A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ ∈ nhds (A.chart j x) := by
      simpa using (A.chart j).open_target.mem_nhds ((A.chart j).map_source hj)
    exact ((hf j).contDiffAt hm).continuousAt
  have h2 := h1.comp ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [Function.comp, (A.chart j).left_inv hy]

def clampT (T t : ℝ) : ℝ := if 0 < t ∧ t ≤ T then t else T

theorem clampT_pos {T : ℝ} (hT : 0 < T) (t : ℝ) : 0 < clampT T t := by
  unfold clampT; split_ifs with h
  · exact h.1
  · exact hT

theorem clampT_le {T : ℝ} (t : ℝ) : clampT T t ≤ T := by
  unfold clampT; split_ifs with h
  · exact h.2
  · exact le_rfl

theorem clampT_eq {T t : ℝ} (h0 : 0 < t) (h1 : t ≤ T) : clampT T t = t := by
  unfold clampT; rw [if_pos ⟨h0, h1⟩]

def avgSys {e : ℕ} {σ : Type} (S : AnSys e σ) (c : S.X → S.X) (C T : ℝ)
    (hreg : ∀ a, IsRegFamily S.A S.Θ S.L S.s (S.th a) (S.ph a)
      (fun t y => (S.phT a t y + S.phT a t (c y)) / 2) C T)
    (hc2 : ∀ a, IsRegFamilyC2 S.A S.s (S.ph a) (fun t y => (S.phT a t y + S.phT a t (c y)) / 2)) :
    AnSys e σ :=
  { S with
    phT := fun a t y => (S.phT a t y + S.phT a t (c y)) / 2
    C := C
    t₀ := T
    reg := hreg
    c2 := hc2 }

def avgLine {D : ℕ} {σ : Type} {S : AnSys D (Option σ)} {P : Ideal (MRing ι)} (Re : Realis S P) (T : ℝ) :
    Option σ → ℝ → HermLine ι
  | none, t => Re.line none t
  | some p, t => conjAvg (Re.line (some p) (clampT T t))

def avgRe {D : ℕ} {σ : Type} {S : AnSys D (Option σ)} {P : Ideal (MRing ι)} (Re : Realis S P)
    (c : S.X → S.X) (C T : ℝ)
    (hreg : ∀ a, IsRegFamily S.A S.Θ S.L S.s (S.th a) (S.ph a)
      (fun t y => (S.phT a t y + S.phT a t (c y)) / 2) C T)
    (hc2 : ∀ a, IsRegFamilyC2 S.A S.s (S.ph a) (fun t y => (S.phT a t y + S.phT a t (c y)) / 2))
    (hT0 : 0 < T) (hT : T ≤ S.t₀)
    (hline : ∀ a t, 0 < t → t ≤ T → ∀ x,
      Real.log ((avgLine Re T a t).h (Re.R.lift x x)) = Real.log ((Re.ref a).h (Re.R.lift x x)) +
        (S.phT a t (Re.π x) + S.phT a t (c (Re.π x))) / 2) :
    Realis (avgSys S c C T hreg hc2) P :=
  { Re with
    line := avgLine Re T
    line_deg := fun a t => by
      cases a with
      | none => exact Re.line_deg none t
      | some p => exact Re.line_deg (some p) _
    line_smooth := fun a t h0 h1 => by
      cases a with
      | none => exact Re.line_smooth none t h0 (le_trans h1 hT)
      | some p => exact conjAvg_smooth (Re.line_smooth (some p) _ (clampT_pos hT0 t) ((clampT_le t).trans hT))
    line_eq := hline }

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ}

theorem onStep_conjAvg (M : FlagModel y Ψ N j) {p : Ψ × Fin N} {A : HermLine ι} (hA : M.OnStep p A) :
    M.OnStep p (conjAvg A) := by
  intro z z' hb hk
  change Real.sqrt |A.h z * A.h (cj z)| = Real.sqrt |A.h z' * A.h (cj z')|
  rw [hA z z' hb hk, hA (cj z) (cj z') ?_ ?_]
  · funext q
    exact congrArg (starRingEnd ℂ) (congrFun hb q)
  · intro k hk' m
    exact congrArg (starRingEnd ℂ) (hk k hk' m)

theorem conj_of_flagAn [Fintype Ψ] {M : FlagModel y Ψ N j} {n d : ℕ} {BM : BaseMetric M n}
    (FA : FlagAn BM d)
    (h1 : ∀ x x', SameOrbit (BM.Rb.lift x' x') (fun q => starRingEnd ℂ (BM.Rb.lift x x q)) →
      (x' ∈ bdry BM.s ↔ x ∈ bdry BM.s) ∧ rW BM.L BM.s x' = rW BM.L BM.s x)
    (h2 : ∀ p, ∀ z ∈ mcPts (mCoordIdeal y), ∀ x, x ∉ bdry BM.s → SameOrbit (basePart M.blk z) (BM.Rb.lift x x) →
      (BM.hom p).h (fun q => starRingEnd ℂ (z q)) = (BM.hom p).h z) :
    ∃ FA' : FlagAn BM d, ∀ a t, IsConjInvariantH (FA'.Re.line a t) := by
  have hdeg : IsDegreeOff FA.S.A FA.Re.R.A FA.Re.π 1 ∅ := by
    have := FA.Re.degree
    rwa [FA.deg_one, FA.br_empty] at this
  obtain ⟨g, hgπ, hπg, hgh⟩ := GlobalTheory.T.holomorphic_degree_one_biholomorphism FA.S.A FA.Re.R.A FA.Re.π FA.Re.holo hdeg
  have hsys := GlobalTheory.T.biholomorphic_lift_system FA.J_top FA.Re.R FA.S.A g FA.Re.π hgπ hπg hgh FA.Re.holo
  obtain ⟨c, hspec, hcont, hinv⟩ := GlobalTheory.T.lift_system_complex_conjugation hsys
  have hanal := GlobalTheory.T.conjugation_antiholomorphic_charts hsys c hspec hcont
  have hmem : ∀ r, FA.Re.R.lift r r ∈ mcPts (mCoordIdeal y) := fun r =>
    FA.Re.R.mem r r (FA.Re.R.mem_U r)

  have hbase : ∀ x, SameOrbit (BM.Rb.lift (FA.pr (c x)) (FA.pr (c x)))
      (cj (BM.Rb.lift (FA.pr x) (FA.pr x))) := by
    intro x
    have e1 := FA.pr_eq (g (c x))
    have e2 := FA.pr_eq (g x)
    rw [hπg] at e1 e2
    have e3 := sameOrbit_base M.blk (hspec x)
    refine sameOrbit_trans (sameOrbit_symm e1) (sameOrbit_trans e3 ?_)
    exact sameOrbit_cj e2
  have hs_eq : ∀ x, FA.S.s x x = BM.s (FA.pr x) (FA.pr x) := fun x => by rw [FA.s_eq]
  have hbd : ∀ x, x ∈ bdry FA.S.s ↔ FA.pr x ∈ bdry BM.s := fun x => by
    change FA.S.s x x = 0 ↔ BM.s (FA.pr x) (FA.pr x) = 0
    rw [hs_eq]
  have hrW : ∀ x, rW FA.S.L FA.S.s x = rW BM.L BM.s (FA.pr x) := fun x => by
    unfold rW logNormSec
    rw [hs_eq, FA.L_eq]
    rfl
  have hcb : ∀ x, c x ∈ bdry FA.S.s ↔ x ∈ bdry FA.S.s := fun x => by
    rw [hbd, hbd]; exact (h1 _ _ (hbase x)).1
  have hcr : ∀ x, rW FA.S.L FA.S.s (c x) = rW FA.S.L FA.S.s x := fun x => by
    rw [hrW, hrW]; exact (h1 _ _ (hbase x)).2

  have href : ∀ a, IsConjInvariantH (FA.Re.ref a) := fun a => by
    cases a with
    | none => rw [FA.ref_none]; exact fs_conj _
    | some p => rw [FA.ref_some]; exact fs_conj _
  have hth : ∀ a x, ∃ V : Set FA.S.X, IsOpen V ∧ x ∈ V ∧ ∃ G : FA.S.X → ℂ, FA.S.A.HoloOn V G ∧
      ∀ y' ∈ V, (FA.S.th a).φ (c x) (c y') - (FA.S.th a).φ x y' = (G y').re := fun a =>
    GlobalTheory.T.lift_system_real_structure hsys c hspec hcont hanal (FA.Re.ref a) (href a) (FA.S.th a) fun x => by
      obtain ⟨V, hV, hxV, G, hG, hGe⟩ := FA.Re.ref_pot a (g x) (Set.mem_univ _)
      refine ⟨g ⁻¹' V, hV.preimage hgh.1, hxV, G ∘ g, holoOn_comp hgh hG, fun y' hy' => ?_⟩
      have := hGe (g y') hy'
      simp only [potOf, LocPot.pullback, hπg] at this
      exact this

  have hph : ∀ p, ∀ x ∉ bdry FA.S.s, FA.S.ph (some p) (c x) = FA.S.ph (some p) x := by
    intro p x hx
    have hx' : c x ∉ bdry FA.S.s := fun h => hx ((hcb x).1 h)
    have e1 := FA.hom_eq p (g x) (by rw [hπg]; exact hx)
    have e2 := FA.hom_eq p (g (c x)) (by rw [hπg]; exact hx')
    rw [hπg] at e1 e2
    have hpx : FA.pr x ∉ bdry BM.s := fun h => hx ((hbd x).2 h)
    have hzz := FA.pr_eq (g x)
    rw [hπg] at hzz
    have hinvh : (BM.hom p).h (cj (FA.Re.R.lift (g x) (g x))) = (BM.hom p).h (FA.Re.R.lift (g x) (g x)) :=
      h2 p _ (hmem (g x)) (FA.pr x) hpx hzz
    have ho := log_sub_orbit (BM.hom p) (FA.Re.ref (some p)) (by rw [BM.hom_deg, FA.ref_some]; rfl)
      (cj_nonzero (hmem (g x)).1) (hspec x)
    have hr : (FA.Re.ref (some p)).h (cj (FA.Re.R.lift (g x) (g x))) =
        (FA.Re.ref (some p)).h (FA.Re.R.lift (g x) (g x)) := href (some p) _
    rw [hinvh, hr] at ho
    linarith
  have hphall : ∀ a, ∀ x ∉ bdry FA.S.s, FA.S.ph a (c x) = FA.S.ph a x := fun a => by
    cases a with
    | none => intro x _; rw [FA.ph_none.1]; rfl
    | some p => exact hph p

  have hreg : ∀ a, ∃ C' t' : ℝ, IsRegFamily FA.S.A FA.S.Θ FA.S.L FA.S.s (FA.S.th a) (FA.S.ph a)
        (fun t y' => (FA.S.phT a t y' + FA.S.phT a t (c y')) / 2) C' t' ∧
      IsRegFamilyC2 FA.S.A FA.S.s (FA.S.ph a) fun t y' => (FA.S.phT a t y' + FA.S.phT a t (c y')) / 2 :=
    fun a => GlobalTheory.T.conjugation_invariant_singular_potential (d + 1) FA.S.X FA.S.A FA.S.Θ FA.S.L FA.S.s FA.S.nb FA.S.m FA.S.W FA.S.potL FA.S.sec
      FA.S.snc FA.S.norm_le FA.S.potΘ FA.S.posΘ c hcont hinv hanal hcb hcr (FA.S.th a) (FA.S.ph a) (FA.S.phT a)
      FA.S.C FA.S.t₀ (FA.S.sing a).1 (hth a) (hphall a) (FA.S.reg a) (FA.S.c2 a)
  choose Cf tf hregf hc2f using hreg
  have hne : (Finset.univ : Finset (Option (Ψ × Fin N))).Nonempty := ⟨none, Finset.mem_univ _⟩
  set T : ℝ := min (min (Finset.univ.inf' hne tf) FA.S.t₀) (Real.exp (-1)) with hTdef
  have ht00 : 0 < FA.S.t₀ := (FA.S.reg none).1
  have hT0 : 0 < T := by
    refine lt_min (lt_min ?_ ht00) (Real.exp_pos _)
    rw [Finset.lt_inf'_iff]
    exact fun a _ => (hregf a).1
  have hTS : T ≤ FA.S.t₀ := (min_le_left _ _).trans (min_le_right _ _)
  have hTf : ∀ a, T ≤ tf a := fun a =>
    ((min_le_left _ _).trans (min_le_left _ _)).trans (Finset.inf'_le _ (Finset.mem_univ a))
  have hTe : T ≤ Real.exp (-1) := min_le_right _ _
  set Cs : ℝ := ∑ a, |Cf a| with hCs
  have hCle : ∀ a, |Cf a| ≤ Cs := fun a =>
    Finset.single_le_sum (f := fun a => |Cf a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
  have hreg' : ∀ a, IsRegFamily FA.S.A FA.S.Θ FA.S.L FA.S.s (FA.S.th a) (FA.S.ph a)
      (fun t y' => (FA.S.phT a t y' + FA.S.phT a t (c y')) / 2) Cs T := fun a =>
    (GlobalTheory.T.singular_weight_monotone_regularization (d + 1) FA.S.X FA.S.A FA.S.Θ FA.S.L FA.S.s FA.S.nb FA.S.m FA.S.W FA.S.potL FA.S.sec
      FA.S.snc FA.S.norm_le FA.S.potΘ FA.S.posΘ).2.1 _ _ _ _ _ _ _ (hCle a) hT0 (hTf a) hTe (hregf a) (FA.S.sing a).1

  have hline : ∀ a t, 0 < t → t ≤ T → ∀ x,
      Real.log ((avgLine FA.Re T a t).h (FA.Re.R.lift x x)) =
        Real.log ((FA.Re.ref a).h (FA.Re.R.lift x x)) +
        (FA.S.phT a t (FA.Re.π x) + FA.S.phT a t (c (FA.Re.π x))) / 2 := by
    intro a t h0 ht x
    cases a with
    | none =>
      have e := FA.Re.line_eq none t h0 (ht.trans hTS) x
      change Real.log ((FA.Re.line none t).h (FA.Re.R.lift x x)) = _
      rw [e, FA.ph_none.2 t]
      simp
    | some p =>
      change Real.log ((conjAvg (FA.Re.line (some p) (clampT T t))).h (FA.Re.R.lift x x)) = _
      rw [clampT_eq h0 ht, conjAvg_log _ (hmem x).1]
      have e1 := FA.Re.line_eq (some p) t h0 (ht.trans hTS) x
      have e2 := FA.Re.line_eq (some p) t h0 (ht.trans hTS) (g (c (FA.Re.π x)))
      rw [hπg] at e2
      have hsp := hspec (FA.Re.π x)
      rw [hgπ] at hsp
      have ho := log_sub_orbit (FA.Re.line (some p) t) (FA.Re.ref (some p)) (FA.Re.line_deg _ _)
        (cj_nonzero (hmem x).1) hsp
      have hr : (FA.Re.ref (some p)).h (cj (FA.Re.R.lift x x)) = (FA.Re.ref (some p)).h (FA.Re.R.lift x x) :=
        href (some p) _
      rw [hr] at ho
      linarith
  have hpot : ∀ a t, (∀ y', FA.S.phT a t (c y') = FA.S.phT a t y') →
      (avgSys FA.S c Cs T hreg' hc2f).potT a t = FA.S.potT a t := by
    intro a t h
    have e : (fun y' => (FA.S.phT a t y' + FA.S.phT a t (c y')) / 2) = FA.S.phT a t := by
      funext y'
      rw [h y']
      ring
    change FA.S.th a + LocPot.ofFun (fun y' => (FA.S.phT a t y' + FA.S.phT a t (c y')) / 2) =
      FA.S.th a + LocPot.ofFun (FA.S.phT a t)
    rw [e]
  refine ⟨{ S := avgSys FA.S c Cs T hreg' hc2f
            Re := avgRe FA.Re c Cs T hreg' hc2f hT0 hTS hline
            J_top := FA.J_top
            deg_one := FA.deg_one
            br_empty := FA.br_empty
            ref_some := FA.ref_some
            ref_none := FA.ref_none
            line_none := FA.line_none
            ph_none := ⟨FA.ph_none.1, fun t => ?_⟩
            pos_none := ?_
            pr := FA.pr
            pr_holo := FA.pr_holo
            pr_eq := FA.pr_eq
            L_eq := FA.L_eq
            s_eq := FA.s_eq
            hom_eq := FA.hom_eq
            step := fun p t => onStep_conjAvg M (FA.step p _)
            step_ph := ?_
            flat := ?_ }, ?_⟩
  · change (fun y' => (FA.S.phT none t y' + FA.S.phT none t (c y')) / 2) = 0
    rw [FA.ph_none.2 t]
    funext y'
    simp
  · obtain ⟨c₀, hc₀, hp⟩ := FA.pos_none
    refine ⟨c₀, hc₀, fun t => ?_⟩
    rw [hpot none t fun y' => by rw [FA.ph_none.2 t]; rfl]
    exact hp t
  · refine fun p (x : FA.Re.R.X) (x' : FA.Re.R.X) hpr hblk => ?_
    obtain ⟨hph0, hpt⟩ := FA.step_ph p x x' hpr hblk
    refine ⟨hph0, fun t => ?_⟩
    change (FA.S.phT (some p) t (FA.Re.π x) + FA.S.phT (some p) t (c (FA.Re.π x))) / 2 =
      (FA.S.phT (some p) t (FA.Re.π x') + FA.S.phT (some p) t (c (FA.Re.π x'))) / 2
    have hinj : FA.pr (c (FA.Re.π x)) = FA.pr (c (FA.Re.π x')) := by
      refine BM.Rb.inj _ _ (not_mem_top rfl _) (sameOrbit_trans (hbase (FA.Re.π x)) ?_)
      have hpr' : FA.pr (FA.Re.π x) = FA.pr (FA.Re.π x') := hpr
      rw [hpr']
      exact sameOrbit_symm (hbase (FA.Re.π x'))
    have hb : ∀ k, M.blk p = some k → ∃ a : ℂ, ∀ m : ι k,
        FA.Re.R.lift (g (c (FA.Re.π x))) (g (c (FA.Re.π x))) ⟨k, m⟩ =
          a * FA.Re.R.lift (g (c (FA.Re.π x'))) (g (c (FA.Re.π x'))) ⟨k, m⟩ := by
      intro k hk
      obtain ⟨a, ha⟩ := hblk k hk
      have hs1 := hspec (FA.Re.π x)
      have hs2 := hspec (FA.Re.π x')
      rw [hgπ] at hs1 hs2
      obtain ⟨b, hb0, hbe⟩ := hs1
      obtain ⟨b', hb0', hbe'⟩ := hs2
      refine ⟨b k * starRingEnd ℂ a * (b' k)⁻¹, fun m => ?_⟩
      have e1 := congrFun hbe ⟨k, m⟩
      have e2 := congrFun hbe' ⟨k, m⟩
      rw [e1, e2]
      have e3 : FA.Re.R.lift x x ⟨k, m⟩ = a * FA.Re.R.lift x' x' ⟨k, m⟩ := ha m
      simp only [cj]
      rw [e3, map_mul]
      have := hb0' k
      field_simp
    have hlast := (FA.step_ph p (g (c (FA.Re.π x))) (g (c (FA.Re.π x')))
      (by rw [hπg, hπg]; exact hinj) hb).2 t
    rw [hπg, hπg] at hlast
    rw [hpt t, hlast]
  · intro p hp t
    have hs : FA.S.A.Smooth (FA.S.ph (some p)) := by
      have h0 := ((FA.S.reg (some p)).2.2 FA.S.t₀ ht00 le_rfl).1
      rwa [(FA.flat p hp FA.S.t₀).2.2] at h0
    have hc1 := smooth_continuous hs
    have hd : Dense (bdry FA.S.s)ᶜ :=
      interior_eq_empty_iff_dense_compl.1 (LeviFormBoundaryTopology.interior_bdry_eq_empty FA.S.sec FA.S.snc)
    have hcp : ∀ y', FA.S.ph (some p) (c y') = FA.S.ph (some p) y' :=
      congrFun (Continuous.ext_on hd (hc1.comp hcont) hc1 fun y' hy' => hph p y' hy')
    obtain ⟨f1, f2, f3⟩ := FA.flat p hp t
    have hpt : ∀ y', FA.S.phT (some p) t (c y') = FA.S.phT (some p) t y' := by
      rw [f3]; exact hcp
    have e := hpot (some p) t hpt
    refine ⟨?_, ?_, ?_⟩
    · rw [e]; exact f1
    · rw [e]; exact f2
    · change (fun y' => (FA.S.phT (some p) t y' + FA.S.phT (some p) t (c y')) / 2) = FA.S.ph (some p)
      funext y'
      rw [hpt y', f3]
      ring
  · intro a t
    cases a with
    | none =>
      change IsConjInvariantH (FA.Re.line none t)
      rw [FA.line_none]
      exact fs_conj _
    | some p => exact conjAvg_conj _

end GlobalTheory.CompanionTheory.Ar.PB.Cj

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem flagAn_conj : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n), Nonempty (FlagAn BM d) → (∀ x x', SameOrbit (BM.Rb.lift x' x') (fun q => starRingEnd ℂ (BM.Rb.lift x x q)) → (x' ∈ bdry BM.s ↔ x ∈ bdry BM.s) ∧ rW BM.L BM.s x' = rW BM.L BM.s x) → (∀ p, ∀ z ∈ mcPts (mCoordIdeal y), ∀ x, x ∉ bdry BM.s → SameOrbit (basePart M.blk z) (BM.Rb.lift x x) → (BM.hom p).h (fun q => starRingEnd ℂ (z q)) = (BM.hom p).h z) → ∃ FA : FlagAn BM d, ∀ a t, IsConjInvariantH (FA.Re.line a t) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM hFA h1 h2
  obtain ⟨FA⟩ := hFA
  exact Cj.conj_of_flagAn FA h1 h2

end GlobalTheory.CompanionTheory.Ar.PB
