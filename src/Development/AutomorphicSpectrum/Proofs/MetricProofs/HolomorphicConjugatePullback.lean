module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
public import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicConjugatePullback
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicConjugatePullback
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj

theorem analyticAt_conj_comp_star {e : ℕ} {h : (Fin e → ℂ) → ℂ} {u : Fin e → ℂ}
    (hh : AnalyticAt ℂ h (star u)) :
    AnalyticAt ℂ (fun v => starRingEnd ℂ (h (star v))) u := by
  have hc : ContinuousAt (star : (Fin e → ℂ) → (Fin e → ℂ)) u := continuous_star.continuousAt
  refine GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 ?_
  filter_upwards [hc.eventually hh.eventually_analyticAt] with q hq
  simpa [Function.comp_def] using hq.differentiableAt.star_star

theorem holoOn_conj_comp {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} (c : X → X)
    (hc : Continuous c)
    (hanti : ∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z))))
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source)))
    {V : Set X} {g : X → ℂ} (hg : A.HoloOn V g) :
    A.HoloOn (c ⁻¹' V) (fun y => starRingEnd ℂ (g (c y))) := by
  intro j w hw
  obtain ⟨k, hk⟩ := A.cover (c ((A.chart j).symm w))
  have hw' : w ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source) := ⟨hw.1, hk⟩
  have h1 := hanti j k w hw'
  have h2 : AnalyticAt ℂ (g ∘ (A.chart k).symm) (A.chart k (c ((A.chart j).symm w))) := by
    refine hg k _ ⟨(A.chart k).map_source hk, ?_⟩
    simp only [Set.mem_preimage, (A.chart k).left_inv hk]
    exact hw.2
  have h3 : AnalyticAt ℂ (fun v => starRingEnd ℂ ((g ∘ (A.chart k).symm) (star v)))
      (star (A.chart k (c ((A.chart j).symm w)))) :=
    analyticAt_conj_comp_star (by simpa using h2)
  have h4 := AnalyticAt.comp (g := fun v => starRingEnd ℂ ((g ∘ (A.chart k).symm) (star v)))
    (f := fun z => star (A.chart k (c ((A.chart j).symm z)))) (x := w) h3 h1
  refine h4.congr ?_
  have hcc : ContinuousAt (c ∘ (A.chart j).symm) w :=
    hc.continuousAt.comp ((A.chart j).continuousAt_symm hw.1)
  filter_upwards [hcc ((A.chart k).open_source.mem_nhds hk)] with w' hw''
  have hw3 : c ((A.chart j).symm w') ∈ (A.chart k).source := hw''
  simp [Function.comp, (A.chart k).left_inv hw3]

end GlobalTheory.CompanionTheory.Ar.PB.Cj
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicConjugatePullbackStatement
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_conjugate_pullback : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} (c : X → X), Continuous c → (∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z)))) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source))) → ∀ {V : Set X} {g : X → ℂ}, A.HoloOn V g → A.HoloOn (c ⁻¹' V) (fun y => starRingEnd ℂ (g (c y))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Cj.holoOn_conj_comp | exact GlobalTheory.CompanionTheory.Ar.PB.Cj.holoOn_conj_comp | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Cj.holoOn_conj_comp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SumSqCompBlockMap
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

theorem sum_sq_comp_blockMap {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]
    {Kk : Type} {ιk : Kk → Type} [∀ k, Fintype (ιk k)]
    {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)} (hv : IsBlockMap κ v)
    (z : (Σ k, ι k) → ℂ) (k' : Kk) :
    ∑ m, ‖(z ∘ v) ⟨k', m⟩‖ ^ 2 = ∑ i, ‖z ⟨κ k', i⟩‖ ^ 2 := by
  obtain ⟨hκ, hvi, hblk, hsurj⟩ := hv
  have key : ∀ m : ιk k', ∃ i : ι (κ k'), v ⟨k', m⟩ = ⟨κ k', i⟩ := by
    intro m
    have h := hblk ⟨k', m⟩
    rcases hh : v ⟨k', m⟩ with ⟨c, i⟩
    rw [hh] at h
    simp only at h
    subst h
    exact ⟨i, rfl⟩
  choose g hg using key
  have hinj : Function.Injective g := by
    intro m m' hmm
    have h : v ⟨k', m⟩ = v ⟨k', m'⟩ := by rw [hg, hg, hmm]
    have h' := hvi h
    simpa using h'
  have hsur : Function.Surjective g := by
    intro i
    obtain ⟨⟨k'', m⟩, hp⟩ := hsurj ⟨κ k', i⟩ ⟨k', rfl⟩
    have h := hblk ⟨k'', m⟩
    rw [hp] at h
    have hk : k'' = k' := (hκ h).symm
    subst hk
    refine ⟨m, ?_⟩
    rw [hg] at hp
    simpa using hp
  have hbij : Function.Bijective g := ⟨hinj, hsur⟩
  rw [← hbij.sum_comp (fun i => ‖z ⟨κ k', i⟩‖ ^ 2)]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Function.comp_apply, hg]

theorem fsHerm_h_blockMap : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (a : K → ℤ) (z : (Σ k, ι k) → ℂ), IsBlockMap κ v → (∀ k, a k ≠ 0 → k ∈ Set.range κ) → (fsHerm ι a).h z = (fsHerm ιk fun k => a (κ k)).h (z ∘ v) := by
  intro K _ ι _ Kk _ ιk _ κ v a z hv ha
  rw [fsHerm_h, fsHerm_h]
  unfold refNorm
  symm
  refine Fintype.prod_of_injective κ hv.1 _ _ ?_ ?_
  · intro k hk
    have h0 : a k = 0 := by
      by_contra h
      exact hk (ha k h)
    simp [h0]
  · intro k'
    rw [sum_sq_comp_blockMap hv z k']

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviPullEq
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PshPull

open scoped ContDiff

theorem levi_pull_eq {e e' : ℕ} {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z] (A : FinHolAtlas e X)
    (A' : FinHolAtlas e' Z) (h : X → Z) (hh : HoloMap A A' h) (th : LocPot X) (th' : LocPot Z) (u : Z → ℝ)
    (hth : IsPotential A th) (hth' : IsPotential A' th') (hu : A'.Smooth u)
    (hs : SamePot A Set.univ th (th'.pullback h hh.1)) (c : ℝ) (x : X) (j : Fin A.n) (y : Fin e → ℂ)
    (hy : y ∈ (A.chart j).target) (hyU : (A.chart j).symm y ∈ th.U x) (w : Fin e → ℂ) :
    ∃ (j' : Fin A'.n) (y' v : Fin e' → ℂ), y' ∈ (A'.chart j').target ∧
      (A'.chart j').symm y' = h ((A.chart j).symm y) ∧
      levi (fun t => c * (th.φ x ((A.chart j).symm t) + u (h ((A.chart j).symm t)))) y w =
        levi (fun s => c * (th'.φ (h ((A.chart j).symm y)) ((A'.chart j').symm s) + u ((A'.chart j').symm s))) y' v := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ :=
    WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
  obtain ⟨p, hp⟩ : ∃ p, p = (A.chart j).symm y := ⟨_, rfl⟩
  rw [← hp] at hyU ⊢
  obtain ⟨j', hj'⟩ := A'.cover (h p)
  obtain ⟨W₁, hW₁o, hpW₁, G₁, hG₁, hE₁⟩ := hth.2 x p p ⟨hyU, th.mem_U p⟩
  obtain ⟨W₂, hW₂o, hpW₂, G₂, hG₂, hE₂⟩ := hs p (Set.mem_univ p)
  have hτ : AnalyticAt ℂ (A'.chart j' ∘ h ∘ (A.chart j).symm) y :=
    hh.2 j j' y ⟨hy, by simpa [← hp] using hj'⟩
  have hGa : AnalyticAt ℂ (fun t => G₁ ((A.chart j).symm t) + G₂ ((A.chart j).symm t)) y :=
    AnalyticAt.add (hG₁ j y ⟨hy, by simpa [← hp] using hpW₁⟩) (hG₂ j y ⟨hy, by simpa [← hp] using hpW₂⟩)
  have hτy : (A'.chart j' ∘ h ∘ (A.chart j).symm) y = A'.chart j' (h p) := by simp [← hp]
  have hy' : A'.chart j' (h p) ∈ (A'.chart j').target := (A'.chart j').map_source hj'
  have hsy' : (A'.chart j').symm (A'.chart j' (h p)) = h p := (A'.chart j').left_inv hj'

  have hψ₁ : ContDiffAt ℝ 2 (th'.φ (h p) ∘ (A'.chart j').symm) (A'.chart j' (h p)) := by
    have hO : IsOpen ((A'.chart j').target ∩ (A'.chart j').symm ⁻¹' th'.U (h p)) :=
      (A'.chart j').isOpen_inter_preimage_symm (th'.isOpen_U _)
    have hm : A'.chart j' (h p) ∈ (A'.chart j').target ∩ (A'.chart j').symm ⁻¹' th'.U (h p) :=
      ⟨hy', by simpa [hsy'] using th'.mem_U (h p)⟩
    exact (((hth'.1 (h p) j').contDiffAt (hO.mem_nhds hm))).of_le h2
  have hψ₂ : ContDiffAt ℝ 2 (u ∘ (A'.chart j').symm) (A'.chart j' (h p)) := by
    have hO : IsOpen ((A'.chart j').target ∩ (A'.chart j').symm ⁻¹' Set.univ) := by
      simpa using (A'.chart j').open_target
    have hm : A'.chart j' (h p) ∈ (A'.chart j').target ∩ (A'.chart j').symm ⁻¹' Set.univ :=
      ⟨hy', Set.mem_univ _⟩
    exact ((hu j').contDiffAt (hO.mem_nhds hm)).of_le h2
  have hψ : ContDiffAt ℝ 2 (fun s => c * (th'.φ (h p) ((A'.chart j').symm s) + u ((A'.chart j').symm s)))
      (A'.chart j' (h p)) :=
    contDiffAt_const.mul (hψ₁.add hψ₂)
  have hψτ : ContDiffAt ℝ 2 (fun s => c * (th'.φ (h p) ((A'.chart j').symm s) + u ((A'.chart j').symm s)))
      ((A'.chart j' ∘ h ∘ (A.chart j).symm) y) := by rwa [hτy]
  have hτ2 : ContDiffAt ℝ 2 (A'.chart j' ∘ h ∘ (A.chart j).symm) y :=
    (hτ.restrictScalars (𝕜 := ℝ)).contDiffAt
  have hf : ContDiffAt ℝ 2 ((fun s => c * (th'.φ (h p) ((A'.chart j').symm s) + u ((A'.chart j').symm s))) ∘
      (A'.chart j' ∘ h ∘ (A.chart j).symm)) y := hψτ.comp y hτ2
  have hg : ContDiffAt ℝ 2 (fun t => (G₁ ((A.chart j).symm t) + G₂ ((A.chart j).symm t)).re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt

  have hev : (fun t => c * (th.φ x ((A.chart j).symm t) + u (h ((A.chart j).symm t)))) =ᶠ[𝓝 y]
      fun t => ((fun s => c * (th'.φ (h p) ((A'.chart j').symm s) + u ((A'.chart j').symm s))) ∘
        (A'.chart j' ∘ h ∘ (A.chart j).symm)) t + c * (G₁ ((A.chart j).symm t) + G₂ ((A.chart j).symm t)).re := by
    have hcs : ContinuousAt (A.chart j).symm y := (A.chart j).continuousAt_symm hy
    have hOx : ∀ᶠ t in 𝓝 y, (A.chart j).symm t ∈ W₁ ∩ W₂ ∩ th.U x ∩ th.U p ∩ h ⁻¹' (A'.chart j').source := by
      apply hcs.eventually_mem
      rw [← hp]
      refine IsOpen.mem_nhds ?_ ⟨⟨⟨⟨hpW₁, hpW₂⟩, hyU⟩, th.mem_U p⟩, hj'⟩
      exact (((hW₁o.inter hW₂o).inter (th.isOpen_U x)).inter (th.isOpen_U p)).inter
        ((A'.chart j').open_source.preimage hh.1)
    filter_upwards [hOx] with t ht
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := ht
    have e1 := hE₁ _ ⟨⟨h1, h3⟩, h4⟩
    have e2 : th.φ p ((A.chart j).symm t) - th'.φ (h p) (h ((A.chart j).symm t)) =
      (G₂ ((A.chart j).symm t)).re := hE₂ _ h2
    have e3 : (A'.chart j').symm (A'.chart j' (h ((A.chart j).symm t))) = h ((A.chart j).symm t) :=
      (A'.chart j').left_inv h5
    simp only [Function.comp_apply, e3, Complex.add_re]
    rw [← e1, ← e2]
    ring
  refine ⟨j', A'.chart j' (h p), fderiv ℂ (A'.chart j' ∘ h ∘ (A.chart j).symm) y w, hy', hsy', ?_⟩
  rw [levi_congr hev w, levi_add_smul c hf hg w, levi_comp w hτ hψτ, levi_re_analytic hGa w, hτy]
  ring

theorem isPsh_pull : ∀ (e e' : ℕ) (X Z : Type) [TopologicalSpace X] [TopologicalSpace Z] (A : FinHolAtlas e X)
    (A' : FinHolAtlas e' Z) (h : X → Z) (hh : HoloMap A A' h) (th : LocPot X) (th' : LocPot Z) (u : Z → ℝ),
    IsPotential A th → IsPotential A' th' → A'.Smooth u → SamePot A Set.univ th (th'.pullback h hh.1) →
    (IsPsh A' (th' + LocPot.ofFun u) → IsPsh A (th + LocPot.ofFun (u ∘ h))) ∧
      (IsPsh A' ((th' + LocPot.ofFun u).rsmul (-1)) → IsPsh A ((th + LocPot.ofFun (u ∘ h)).rsmul (-1))) := by
  intro e e' X Z _ _ A A' h hh th th' u hth hth' hu hs
  refine ⟨fun H x j y hy w => ?_, fun H x j y hy w => ?_⟩
  · obtain ⟨j', y', v, hy', hsy, hl⟩ := levi_pull_eq A A' h hh th th' u hth hth' hu hs 1 x j y hy.1 hy.2.1 w
    have hH := H (h ((A.chart j).symm y)) j' y' ⟨hy', by
      rw [Set.mem_preimage, hsy]; exact LocPot.mem_U _ _⟩ v
    simp only [one_mul] at hl
    exact hl ▸ hH
  · obtain ⟨j', y', v, hy', hsy, hl⟩ := levi_pull_eq A A' h hh th th' u hth hth' hu hs (-1) x j y hy.1 hy.2.1 w
    have hH := H (h ((A.chart j).symm y)) j' y' ⟨hy', by
      rw [Set.mem_preimage, hsy]; exact LocPot.mem_U _ _⟩ v
    exact hl ▸ hH

end GlobalTheory.CompanionTheory.Ar.PB.PshPull
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryFactorCommutation
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryFactorCommutation
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.MoveTransvection

theorem exists_conj : ∀ (L : Type) [Field L] (N j : ℕ) (ca cb : Fin N) (U : Matrix (Fin N) (Fin N) L) (X' s : L), (cb : ℕ) = ca + 1 → ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) → IsBlockDiag j U → U.BlockTriangular id → (∀ c, U c c ≠ 0) → U ca ca + s * U ca cb ≠ 0 → X' * (U ca ca + s * U ca cb) = s * U cb cb → ∃ V : Matrix (Fin N) (Fin N) L, IsBlockDiag j V ∧ V.BlockTriangular id ∧ (∀ c, c ≠ cb → V c c ≠ 0) ∧ (1 + Matrix.single cb ca X') * V = U * (1 + Matrix.single cb ca s) := by
  intro L _ N j ca cb U X' s hcb hblk hU hT hd hne hX
  have hlt : ca < cb := by rw [Fin.lt_def]; omega
  have hne' : cb ≠ ca := hlt.ne'
  have hR : ∀ (M : Matrix (Fin N) (Fin N) L) (t : L) (r c : Fin N),
      (M * Matrix.single cb ca t) r c = if c = ca then M r cb * t else 0 := by
    intro M t r c
    by_cases h : c = ca
    · subst h; simp [Matrix.mul_apply, Matrix.single_apply]
    · simp [Matrix.mul_apply, h, Ne.symm h]
  have hL : ∀ (M : Matrix (Fin N) (Fin N) L) (t : L) (r c : Fin N),
      (Matrix.single cb ca t * M) r c = if r = cb then t * M ca c else 0 := by
    intro M t r c
    by_cases h : r = cb
    · subst h; simp [Matrix.mul_apply, Matrix.single_apply]
    · simp [Matrix.mul_apply, h, Ne.symm h]
  have hW : ∀ r c : Fin N, ((1 + Matrix.single cb ca (-X')) * U) r c
      = U r c + if r = cb then -X' * U ca c else 0 := by
    intro r c
    rw [add_mul, one_mul, Matrix.add_apply, hL]
  have hV : ∀ r c : Fin N,
      ((1 + Matrix.single cb ca (-X')) * U * (1 + Matrix.single cb ca s)) r c
      = U r c + (if r = cb then -X' * U ca c else 0)
        + if c = ca then (U r cb + if r = cb then -X' * U ca cb else 0) * s else 0 := by
    intro r c
    rw [mul_add, mul_one, Matrix.add_apply, hR, hW, hW]
  have hTv : ∀ t : L, IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) L) := by
    intro t a b h
    have hab : a ≠ b := by
      rintro rfl
      exact h Iff.rfl
    rw [Matrix.add_apply, Matrix.one_apply_ne hab, Matrix.single_apply, zero_add]
    rw [if_neg]
    rintro ⟨rfl, rfl⟩
    exact h hblk.symm
  refine ⟨(1 + Matrix.single cb ca (-X')) * U * (1 + Matrix.single cb ca s),
    ((hTv _).mul hU).mul (hTv _), ?_, ?_, ?_⟩
  · intro r c hrc
    have hrc' : c < r := hrc
    rw [hV]
    by_cases hc : c = ca
    · subst hc
      by_cases hr : r = cb
      · subst hr
        have h0 : U r c = 0 := hT hrc
        simp only [if_true, h0]
        linear_combination -hX
      · have hcr : cb < r := by
          rw [Fin.lt_def] at hrc' ⊢
          have : (r : ℕ) ≠ cb := fun h => hr (Fin.ext h)
          omega
        have h0 : U r c = 0 := hT hrc
        have h1 : U r cb = 0 := hT hcr
        simp [hr, h0, h1]
    · by_cases hr : r = cb
      · subst hr
        have hcca : c < ca := by
          rw [Fin.lt_def] at hrc' ⊢
          have : (c : ℕ) ≠ ca := fun h => hc (Fin.ext h)
          omega
        have h0 : U r c = 0 := hT hrc
        have h1 : U ca c = 0 := hT hcca
        simp [hc, h0, h1]
      · have h0 : U r c = 0 := hT hrc
        simp [hc, hr, h0]
  · intro c hc
    rw [hV]
    by_cases hca : c = ca
    · subst hca
      simp only [if_true, if_neg hc, add_zero]
      intro h
      apply hne
      linear_combination h
    · simpa [hc, hca] using hd c
  · have hinv : (1 + Matrix.single cb ca X') * (1 + Matrix.single cb ca (-X'))
        = (1 : Matrix (Fin N) (Fin N) L) := by
      have h0 : Matrix.single cb ca X' * Matrix.single cb ca (-X')
          = (0 : Matrix (Fin N) (Fin N) L) := by
        ext r c
        rw [hL, Matrix.single_apply]
        simp [hne']
      rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, h0, add_zero, add_assoc,
        ← Matrix.single_add]
      simp
    rw [← mul_assoc, ← mul_assoc, hinv, one_mul]

end GlobalTheory.CompanionTheory.Ar.PB.MoveTransvection
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryFactorCommutationStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elementary_factor_commutation : ∀ (L : Type) [Field L] (N j : ℕ) (ca cb : Fin N) (U : Matrix (Fin N) (Fin N) L) (X' s : L), (cb : ℕ) = ca + 1 → ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) → IsBlockDiag j U → U.BlockTriangular id → (∀ c, U c c ≠ 0) → U ca ca + s * U ca cb ≠ 0 → X' * (U ca ca + s * U ca cb) = s * U cb cb → ∃ V : Matrix (Fin N) (Fin N) L, IsBlockDiag j V ∧ V.BlockTriangular id ∧ (∀ c, c ≠ cb → V c c ≠ 0) ∧ (1 + Matrix.single cb ca X') * V = U * (1 + Matrix.single cb ca s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.MoveTransvection.exists_conj | exact GlobalTheory.CompanionTheory.Ar.PB.MoveTransvection.exists_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.MoveTransvection.exists_conj <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BiholomorphicLiftSystem
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BiholomorphicLiftSystem
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj.ResTop

theorem not_mem_mcPts_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (z : (Σ k, ι k) → ℂ) : z ∉ mcPts (⊤ : Ideal (MRing ι)) := by
  intro hz
  have h := hz.2 1 Submodule.mem_top
  simp at h

theorem fderiv_injective_of_leftInv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {τ : E → F} {σ : F → E} {a : E}
    (hτ : DifferentiableAt ℂ τ a) (hσ : DifferentiableAt ℂ σ (τ a))
    (h : σ ∘ τ =ᶠ[nhds a] id) : Function.Injective (fderiv ℂ τ a) := by
  have h1 : fderiv ℂ (σ ∘ τ) a = (fderiv ℂ σ (τ a)).comp (fderiv ℂ τ a) :=
    fderiv_comp a hσ hτ
  have h2 : fderiv ℂ (σ ∘ τ) a = ContinuousLinearMap.id ℂ E := by
    rw [h.fderiv_eq]; exact fderiv_id
  intro u v huv
  have hu : (fderiv ℂ (σ ∘ τ) a) u = u := by rw [h2]; rfl
  have hv : (fderiv ℂ (σ ∘ τ) a) v = v := by rw [h2]; rfl
  rw [← hu, ← hv, h1]
  simp [huv]

theorem differentiableAt_affCoord {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) (x : R.X) (p : (k : K) → ι k)
    (hp : ∀ k, R.lift x x ⟨k, p k⟩ ≠ 0) (k : Fin R.A.n) (hk : x ∈ (R.A.chart k).source) :
    DifferentiableAt ℂ (fun w => affCoord p (R.lift x ((R.A.chart k).symm w)))
      (R.A.chart k x) := by
  have hmem : R.A.chart k x ∈ (R.A.chart k).target ∩ (R.A.chart k).symm ⁻¹' R.U x :=
    ⟨(R.A.chart k).map_source hk, by
      simpa only [Set.mem_preimage, (R.A.chart k).left_inv hk] using R.mem_U x⟩
  rw [differentiableAt_pi]
  intro q
  have hn : AnalyticAt ℂ ((fun y => R.lift x y q) ∘ (R.A.chart k).symm) (R.A.chart k x) :=
    R.holo x q k _ hmem
  have hd : AnalyticAt ℂ ((fun y => R.lift x y ⟨q.1, p q.1⟩) ∘ (R.A.chart k).symm)
      (R.A.chart k x) := R.holo x ⟨q.1, p q.1⟩ k _ hmem
  have hne : ((fun y => R.lift x y ⟨q.1, p q.1⟩) ∘ (R.A.chart k).symm) (R.A.chart k x) ≠ 0 := by
    simp only [Function.comp, (R.A.chart k).left_inv hk]
    exact hp q.1
  exact (hn.div hd hne).differentiableAt

theorem isLiftSys_of_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P J : Ideal (MRing ι)} (hJ : J = ⊤) {e : ℕ} (R : AnLogRes P J e) {X : Type}
    [TopologicalSpace X] (A : FinHolAtlas e X) (g : X → R.X) (h : R.X → X)
    (hgh : ∀ y, g (h y) = y) (hhg : ∀ x, h (g x) = x) (hg : HoloMap A R.A g)
    (hh : HoloMap R.A A h) :
    IsLiftSys A P (fun x => g ⁻¹' R.U (g x)) (fun x y => R.lift (g x) (g y)) := by
  subst hJ
  refine ⟨fun x => (R.isOpen_U (g x)).preimage hg.1, fun x => R.mem_U (g x),
    fun x p => holoOn_comp hg (R.holo (g x) p), fun x y hy => R.mem _ _ hy,
    fun x x' y hy => R.compat _ _ _ hy, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨y, hy⟩ := R.surj z hz (not_mem_mcPts_top z)
    exact ⟨h y, by simpa only [hgh] using hy⟩
  · intro x x' hs
    have := R.inj (g x) (g x') (not_mem_mcPts_top _) hs
    rw [← hhg x, ← hhg x', this]
  · intro x p hp j hj
    obtain ⟨k, hk⟩ := R.A.cover (g x)
    set a := A.chart j with ha
    set c := R.A.chart k with hc
    have hax : a.symm (a x) = x := a.left_inv hj
    have hcx : c.symm (c (g x)) = g x := c.left_inv hk
    set τ : (Fin e → ℂ) → (Fin e → ℂ) := c ∘ g ∘ a.symm with hτdef
    set σ : (Fin e → ℂ) → (Fin e → ℂ) := a ∘ h ∘ c.symm with hσdef
    have hτx : τ (a x) = c (g x) := by simp only [hτdef, Function.comp, hax]
    have hτ : AnalyticAt ℂ τ (a x) := hg.2 j k (a x)
      ⟨a.map_source hj, show g (a.symm (a x)) ∈ c.source by rw [hax]; exact hk⟩
    have hσ : AnalyticAt ℂ σ (c (g x)) := hh.2 k j (c (g x))
      ⟨c.map_source hk, show h (c.symm (c (g x))) ∈ a.source by rw [hcx, hhg]; exact hj⟩

    have hcont : ContinuousAt (g ∘ a.symm) (a x) :=
      hg.1.continuousAt.comp (a.continuousAt_symm (a.map_source hj))
    have hnear : ∀ᶠ y in nhds (a x), g (a.symm y) ∈ c.source ∧ y ∈ a.target := by
      refine (hcont.eventually_mem (c.open_source.mem_nhds ?_)).and
        (a.open_target.mem_nhds (a.map_source hj))
      simpa only [Function.comp, hax] using hk
    have hleft : σ ∘ τ =ᶠ[nhds (a x)] id := by
      filter_upwards [hnear] with y hy
      simp only [hσdef, hτdef, Function.comp, c.left_inv hy.1, hhg, id, a.right_inv hy.2]
    have hinj := fderiv_injective_of_leftInv hτ.differentiableAt
      (by rw [hτx]; exact hσ.differentiableAt) hleft
    have hF := differentiableAt_affCoord R (g x) p hp k hk
    have himm := R.immersion (g x) (not_mem_mcPts_top _) p hp k hk
    set F : (Fin e → ℂ) → (Σ k, ι k) → ℂ :=
      fun w => affCoord p (R.lift (g x) ((R.A.chart k).symm w)) with hFdef
    have hcomp : (fun y => affCoord p (R.lift (g x) (g (a.symm y)))) =ᶠ[nhds (a x)] F ∘ τ := by
      filter_upwards [hnear] with y hy
      simp only [hFdef, hτdef, Function.comp, ← hc, c.left_inv hy.1]
    have hder : fderiv ℂ (fun y => affCoord p (R.lift (g x) (g (a.symm y)))) (a x) =
        (fderiv ℂ F (c (g x))).comp (fderiv ℂ τ (a x)) := by
      rw [hcomp.fderiv_eq, fderiv_comp (a x) (by rw [hτx]; exact hF) hτ.differentiableAt, hτx]
    show (fderiv ℂ (fun y => affCoord p (R.lift (g x) (g (a.symm y)))) (a x)).ker = ⊥
    rw [hder, eq_bot_iff]
    intro v hv
    have h1 : (fderiv ℂ F (c (g x))) ((fderiv ℂ τ (a x)) v) = 0 := by simpa using hv
    have h2 : (fderiv ℂ τ (a x)) v ∈ (fderiv ℂ F (c (g x))).ker := by simpa using h1
    rw [himm] at h2
    have h3 : (fderiv ℂ τ (a x)) v = 0 := by simpa using h2
    have h4 : v = 0 := hinj (h3.trans (map_zero _).symm)
    simp [h4]

end GlobalTheory.CompanionTheory.Ar.PB.Cj.ResTop
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BiholomorphicLiftSystemStatement
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.biholomorphic_lift_system : ∀ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}, J = ⊤ → ∀ {e : ℕ} (R : AnLogRes P J e) {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (g : X → R.X) (h : R.X → X), (∀ y, g (h y) = y) → (∀ x, h (g x) = x) → HoloMap A R.A g → HoloMap R.A A h → IsLiftSys A P (fun x => g ⁻¹' R.U (g x)) (fun x y => R.lift (g x) (g y)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Cj.ResTop.isLiftSys_of_top | exact GlobalTheory.CompanionTheory.Ar.PB.Cj.ResTop.isLiftSys_of_top | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Cj.ResTop.isLiftSys_of_top <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.DomCellLogNormMeasurableInvariant
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.DomCellLogNormMeasurableInvariant
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

section Weight

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem eval_blockScale {s : MRingOver ℂ ι} {a : K → ℕ} (hs : IsMultiHomog s a) (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) :
    eval (fun p : Σ k, ι k => c p.1 * z p) s = (∏ k, c k ^ a k) * eval z s := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h1 : ∏ q : (Σ k, ι k), (c q.1 * z q) ^ m q =
      (∏ k, c k ^ a k) * ∏ q : (Σ k, ι k), z q ^ m q := by
    simp_rw [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hs m hm k]
  rw [h1]; ring

theorem logNormC_blockScale (A : HermLine ι) {s : MRingOver ℂ ι} {a : K → ℕ}
    (hA : ∀ k, A.a k = a k) (hs : IsMultiHomog s a) {c : K → ℂ} (hc : ∀ k, c k ≠ 0)
    (z : (Σ k, ι k) → ℂ) : logNormC A s (fun p => c p.1 * z p) = logNormC A s z := by
  unfold logNormC
  rw [eval_blockScale hs c z]
  have hh : A.h (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ A.a k) * A.h z := A.smul c z hc
  have hpos : 0 < ∏ k, ‖c k‖ ^ A.a k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hc k)) _
  have hn : ‖∏ k, c k ^ a k‖ = ∏ k, ‖c k‖ ^ A.a k := by
    rw [norm_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_pow, hA k, zpow_natCast]
  rw [hh, norm_mul, hn, mul_div_mul_left _ _ hpos.ne']

theorem segre_blockScale (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (i : (k : K) → ι k) :
    segre (fun p : Σ k, ι k => c p.1 * z p) i = (∏ k, c k) * segre z i := by
  simp only [segre, Finset.prod_mul_distrib]

theorem isClosed_domCell (i : (k : K) → ι k) : IsClosed (domCell i) := by
  have hc : ∀ j : (k : K) → ι k, Continuous fun z : (Σ k, ι k) → ℂ => ‖segre z j‖ := fun j => by
    have h : Continuous fun z : (Σ k, ι k) → ℂ => ∏ k, z ⟨k, j k⟩ :=
      continuous_finsetProd _ fun k _ => continuous_apply (⟨k, j k⟩ : Σ k, ι k)
    exact h.norm
  have : domCell i = ⋂ j, {z : (Σ k, ι k) → ℂ | ‖segre z j‖ ≤ ‖segre z i‖} := by
    ext z; simp [domCell]
  rw [this]
  exact isClosed_iInter fun j => isClosed_le (hc j) (hc i)

theorem blockScale_mem_domCell {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ)
    (i : (k : K) → ι k) : (fun p : Σ k, ι k => c p.1 * z p) ∈ domCell i ↔ z ∈ domCell i := by
  have hpos : 0 < ‖∏ k, c k‖ :=
    norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => hc k)
  simp only [domCell, Set.mem_setOf_eq, segre_blockScale, norm_mul]
  exact forall_congr' fun j =>
    ⟨fun h => le_of_mul_le_mul_left h hpos, fun h => mul_le_mul_of_nonneg_left h hpos.le⟩

theorem measurable_absLogNorm (A : HermLine ι) (hA : IsSmoothHerm A) (s : MRingOver ℂ ι) :
    Measurable (absLogNorm A s) := by
  classical
  set T : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} with hT
  have hTm : MeasurableSet T := isOpen_blockNonzero.measurableSet
  have hh : Measurable (T.piecewise A.h 1) :=
    hA.continuousOn.measurable_piecewise continuousOn_const hTm
  have heq : absLogNorm A s =
      T.piecewise (fun z => |Real.log (‖eval z s‖ / T.piecewise A.h 1 z)|) 0 := by
    funext z
    by_cases hz : z ∈ T
    · have hz' : ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0 := hz
      rw [Set.piecewise_eq_of_mem _ _ _ hz, Set.piecewise_eq_of_mem _ _ _ hz]
      simp only [absLogNorm, if_pos hz', logNormC]
    · have hz' : ¬ ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0 := hz
      rw [Set.piecewise_eq_of_notMem _ _ _ hz]
      simp only [absLogNorm, if_neg hz', Pi.zero_apply]
  rw [heq]
  refine Measurable.piecewise hTm ?_ measurable_const
  exact continuous_abs.measurable.comp
    (Real.measurable_log.comp ((MvPolynomial.continuous_eval s).norm.measurable.div hh))

theorem absLogNorm_blockScale (A : HermLine ι) {s : MRingOver ℂ ι} {a : K → ℕ}
    (hAa : ∀ k, A.a k = a k) (hs : IsMultiHomog s a) {c : K → ℂ} (hc : ∀ k, c k ≠ 0)
    (z : (Σ k, ι k) → ℂ) : absLogNorm A s (fun p => c p.1 * z p) = absLogNorm A s z := by
  have hmem : (∀ k, ∃ j, c k * z ⟨k, j⟩ ≠ 0) ↔ ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, hc, false_or]
  by_cases hz : ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0
  · simp only [absLogNorm, if_pos hz, if_pos (hmem.2 hz), logNormC_blockScale A hAa hs hc z]
  · simp only [absLogNorm, if_neg hz, if_neg (mt hmem.1 hz)]

end Weight

theorem cutWeight_measurable_invariant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ) (i : (k : K) → ι k),
    IsSmoothHerm A → (∀ k, A.a k = a k) → IsMultiHomog s a →
    Measurable ((domCell i).indicator (absLogNorm A s)) ∧
    ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      (domCell i).indicator (absLogNorm A s) (fun p => c p.1 * z p) =
        (domCell i).indicator (absLogNorm A s) z := by
  intro K _ ι _ A s a i hA hAa hs
  refine ⟨(measurable_absLogNorm A hA s).indicator (isClosed_domCell i).measurableSet, ?_⟩
  intro c z hc
  by_cases hz : z ∈ domCell i
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((blockScale_mem_domCell hc z i).2 hz),
      absLogNorm_blockScale A hAa hs hc z]
  · rw [Set.indicator_of_notMem hz,
      Set.indicator_of_notMem (mt (blockScale_mem_domCell hc z i).1 hz)]

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.DomCellLogNormMeasurableInvariantStatement
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.domCell_logNorm_measurable_invariant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ) (i : (k : K) → ι k),
    IsSmoothHerm A → (∀ k, A.a k = a k) → IsMultiHomog s a →
    Measurable ((domCell i).indicator (absLogNorm A s)) ∧
    ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      (domCell i).indicator (absLogNorm A s) (fun p => c p.1 * z p) =
        (domCell i).indicator (absLogNorm A s) z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cutWeight_measurable_invariant | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cutWeight_measurable_invariant | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cutWeight_measurable_invariant <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalDensityInclusionExclusion
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalDensityInclusionExclusion
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

noncomputable section

theorem locDens_expand_ofFun : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X) (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (Θ : LocPot X), IsOpen U → (∀ i, IsPotential A (P i)) → IsPotential A Θ → (∀ i, A.SmoothOn U (f i)) → ∀ j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U, locDens A (fun i => P i + LocPot.ofFun (f i)) j y = ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) * locDens A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) + LocPot.ofFun (if i ∈ T then f i else 0) + Θ) j y := by
  intro e X _ A U P f Θ hU hPot hΘ hf j y hy
  classical
  unfold ReciprocityTheory.AnForm.M.IsPotential at hPot hΘ
  have smooth_at : ∀ (g : X → ℝ) (W : Set X), IsOpen W → A.SmoothOn W g →
      y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W →
      ContDiffAt ℝ 2 (fun y' => g ((A.chart j).symm y')) y := by
    intro g W hW hg hyW
    have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) :=
      (A.chart j).isOpen_inter_preimage_symm hW
    have h1 := (hg j).contDiffAt (hopen.mem_nhds hyW)
    exact h1.of_le (by first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤) | decide | simp)
  have hsP : ∀ k, ContDiffAt ℝ 2
      (fun y' => (P k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := fun k =>
    smooth_at ((P k).φ ((A.chart j).symm y)) ((P k).U ((A.chart j).symm y)) ((P k).isOpen_U _)
      ((hPot k).1 _) ⟨hy.1, (P k).mem_U _⟩
  have hsf : ∀ k, ContDiffAt ℝ 2 (fun y' => f k ((A.chart j).symm y')) y := fun k =>
    smooth_at (f k) U hU (hf k) hy
  have hsΘ : ContDiffAt ℝ 2 (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y :=
    smooth_at (Θ.φ ((A.chart j).symm y)) (Θ.U ((A.chart j).symm y)) (Θ.isOpen_U _)
      (hΘ.1 _) ⟨hy.1, Θ.mem_U _⟩
  have hessAdd : ∀ φ ψ : (Fin e → ℂ) → ℝ, ContDiffAt ℝ 2 φ y → ContDiffAt ℝ 2 ψ y →
      hessC (fun w => φ w + ψ w) y = hessC φ y + hessC ψ y := by
    intro φ ψ hφ hψ
    have hev : ∀ χ : (Fin e → ℂ) → ℝ, ContDiffAt ℝ 2 χ y → ∀ᶠ w in 𝓝 y, DifferentiableAt ℝ χ w := by
      intro χ hχ
      obtain ⟨f', u, hu, -, hder⟩ :=
        contDiffAt_one_iff.1 (hχ.of_le (by first | norm_num | exact one_le_two))
      exact Filter.mem_of_superset hu fun w hw => (hder w hw).differentiableAt
    have hd2 : ∀ χ : (Fin e → ℂ) → ℝ, ContDiffAt ℝ 2 χ y → DifferentiableAt ℝ (fderiv ℝ χ) y := by
      intro χ hχ
      exact (hχ.fderiv_right (m := 1) (by first | norm_num | exact le_of_eq one_add_one_eq_two)).differentiableAt one_ne_zero
    have hfd : fderiv ℝ (fun w => φ w + ψ w) =ᶠ[𝓝 y] fun w => fderiv ℝ φ w + fderiv ℝ ψ w := by
      filter_upwards [hev φ hφ, hev ψ hψ] with w h1 h2
      exact fderiv_add h1 h2
    have h2 : fderiv ℝ (fderiv ℝ (fun w => φ w + ψ w)) y =
        fderiv ℝ (fderiv ℝ φ) y + fderiv ℝ (fderiv ℝ ψ) y := by
      rw [hfd.fderiv_eq]
      exact fderiv_add (hd2 φ hφ) (hd2 ψ hψ)
    ext a b
    simp only [ReciprocityTheory.AnForm.hessC, h2, Matrix.add_apply, ContinuousLinearMap.add_apply,
      Complex.ofReal_add, Complex.ofReal_sub]
    ring
  have hL : ∀ k, hessC (fun y' => (P k + LocPot.ofFun (f k)).φ ((A.chart j).symm y) ((A.chart j).symm y')) y =
      hessC (fun y' => (P k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y +
        hessC (fun y' => f k ((A.chart j).symm y')) y := fun k =>
    hessAdd (fun y' => (P k).φ ((A.chart j).symm y) ((A.chart j).symm y'))
      (fun y' => f k ((A.chart j).symm y')) (hsP k) (hsf k)
  have hR : ∀ (T : Finset (Fin e)) (k : Fin e),
      hessC (fun y' => ((if k ∈ T then P k else LocPot.ofFun 0) + LocPot.ofFun (if k ∈ T then f k else 0) + Θ).φ
        ((A.chart j).symm y) ((A.chart j).symm y')) y =
        if k ∈ T then hessC (fun y' => (P k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y +
            hessC (fun y' => f k ((A.chart j).symm y')) y +
            hessC (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y
        else hessC (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
    intro T k
    by_cases hk : k ∈ T
    · simp only [hk, ↓reduceIte]
      rw [← hL k]
      exact hessAdd (fun y' => (P k + LocPot.ofFun (f k)).φ ((A.chart j).symm y) ((A.chart j).symm y'))
        (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) ((hsP k).add (hsf k)) hsΘ
    · simp only [hk, ↓reduceIte]
      congr 1
      funext y'
      show (0 : X → ℝ) ((A.chart j).symm y') + (0 : X → ℝ) ((A.chart j).symm y') +
          Θ.φ ((A.chart j).symm y) ((A.chart j).symm y') = Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')
      simp
  have hPE : ∀ x z : Fin e → ℂ, ∑ T : Finset (Fin e), (-1 : ℂ) ^ (e - T.card) *
      ∏ k, (if k ∈ T then x k + z k else z k) = ∏ k, x k := by
    intro x z
    have hadd := Finset.prod_add (fun k => x k + z k) (fun k => -z k) (Finset.univ : Finset (Fin e))
    simp only [add_neg_cancel_right, Finset.powerset_univ] at hadd
    rw [hadd]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.prod_neg, Finset.card_univ_diff, Fintype.card_fin]
    rw [show (∏ k, if k ∈ T then x k + z k else z k) = ∏ k, T.piecewise (fun k => x k + z k) z k from rfl,
      Finset.prod_piecewise, Finset.univ_inter]
    ring
  have hK : ∀ c : Fin e → Fin e, ∑ S : Finset (Fin e), (-1 : ℂ) ^ (e - S.card) *
      (if ∀ i, c i ∈ S then (1 : ℂ) else 0) = if Function.Surjective c then 1 else 0 := by
    intro c
    have hterm : ∀ S : Finset (Fin e), (if ∀ i, c i ∈ S then (1 : ℂ) else 0) =
        ∏ k, (if k ∈ S then (if k ∈ Set.range c then (1 : ℂ) else 0) + (if k ∈ Set.range c then 0 else 1)
          else (if k ∈ Set.range c then 0 else 1)) := by
      intro S
      by_cases h : ∀ i, c i ∈ S
      · rw [if_pos h]
        symm
        refine Finset.prod_eq_one fun k _ => ?_
        by_cases hkS : k ∈ S
        · rw [if_pos hkS]
          split_ifs <;> simp
        · have hkr : k ∉ Set.range c := by
            rintro ⟨i, rfl⟩
            exact hkS (h i)
          rw [if_neg hkS, if_neg hkr]
      · push_neg at h
        obtain ⟨i, hi⟩ := h
        rw [if_neg (fun h' => hi (h' i))]
        symm
        refine Finset.prod_eq_zero (Finset.mem_univ (c i)) ?_
        rw [if_neg hi, if_pos (Set.mem_range_self i)]
    simp only [hterm]
    rw [hPE, Finset.prod_boole]
    by_cases hs : Function.Surjective c
    · rw [if_pos hs, if_pos (show ∀ i ∈ Finset.univ, i ∈ Set.range c from fun k _ => hs k)]
    · rw [if_neg hs, if_neg (show ¬ ∀ i ∈ Finset.univ, i ∈ Set.range c from fun h => hs fun k => h k (Finset.mem_univ k))]
  have hE : ∀ B : Fin e → Matrix (Fin e) (Fin e) ℂ,
      ∑ S : Finset (Fin e), (-1 : ℂ) ^ (e - S.card) * (∑ k ∈ S, B k).det =
        ∑ σ : Equiv.Perm (Fin e), ∑ c : Fin e → Fin e,
          (if Function.Surjective c then (1 : ℂ) else 0) *
            (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, B (c i) (σ i) i) := by
    intro B
    have h1 : ∀ S : Finset (Fin e), (∑ k ∈ S, B k).det = ∑ σ : Equiv.Perm (Fin e), ∑ c : Fin e → Fin e,
        (if ∀ i, c i ∈ S then (1 : ℂ) else 0) * (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, B (c i) (σ i) i) := by
      intro S
      rw [Matrix.det_apply']
      refine Finset.sum_congr rfl fun σ _ => ?_
      have hs : ∀ i, (∑ k ∈ S, B k) (σ i) i = ∑ k, if k ∈ S then B k (σ i) i else 0 := by
        intro i
        rw [Matrix.sum_apply, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
      simp only [hs]
      rw [Fintype.prod_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases h : ∀ i, c i ∈ S
      · rw [if_pos h, one_mul, Finset.prod_congr rfl fun i _ => if_pos (h i)]
      · push_neg at h
        obtain ⟨i, hi⟩ := h
        rw [if_neg (fun h' => hi (h' i)), zero_mul, Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi),
          mul_zero]
    simp only [h1, Finset.mul_sum]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Finset (Fin e))))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Finset (Fin e))))]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← hK c, Finset.sum_mul]
    refine Finset.sum_congr rfl fun S _ => ?_
    ring
  have hT : ∀ (B : Fin e → Matrix (Fin e) (Fin e) ℂ) (C : Matrix (Fin e) (Fin e) ℂ)
      (σ : Equiv.Perm (Fin e)) (c : Fin e → Fin e), Function.Surjective c →
      ∑ T : Finset (Fin e), (-1 : ℂ) ^ (e - T.card) * ∏ i, (if c i ∈ T then B (c i) + C else C) (σ i) i =
        ∏ i, B (c i) (σ i) i := by
    intro B C σ c hc
    obtain ⟨E, rfl⟩ : ∃ E : Fin e ≃ Fin e, ⇑E = c :=
      ⟨Equiv.ofBijective c ⟨Finite.injective_iff_surjective.2 hc, hc⟩, rfl⟩
    have hre : ∀ T : Finset (Fin e), ∏ i, (if E i ∈ T then B (E i) + C else C) (σ i) i =
        ∏ k, (if k ∈ T then B k (σ (E.symm k)) (E.symm k) + C (σ (E.symm k)) (E.symm k)
          else C (σ (E.symm k)) (E.symm k)) := by
      intro T
      refine Fintype.prod_equiv E _ _ fun i => ?_
      simp only [Equiv.symm_apply_apply]
      split_ifs <;> rfl
    simp only [hre]
    rw [hPE]
    exact (Fintype.prod_equiv E _ _ fun i => by simp only [Equiv.symm_apply_apply]).symm
  have hKey : ∀ (B : Fin e → Matrix (Fin e) (Fin e) ℂ) (C : Matrix (Fin e) (Fin e) ℂ),
      mdisc B = ∑ T : Finset (Fin e), (-1 : ℂ) ^ (e - T.card) *
        mdisc (fun k => if k ∈ T then B k + C else C) := by
    intro B C
    unfold ReciprocityTheory.AnForm.mdisc
    simp only [hE]
    have hterm : ∀ (σ : Equiv.Perm (Fin e)) (c : Fin e → Fin e),
        (if Function.Surjective c then (1 : ℂ) else 0) * (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, B (c i) (σ i) i) =
          ∑ T : Finset (Fin e), (-1 : ℂ) ^ (e - T.card) * ((if Function.Surjective c then (1 : ℂ) else 0) *
            (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, (if c i ∈ T then B (c i) + C else C) (σ i) i)) := by
      intro σ c
      by_cases hc : Function.Surjective c
      · rw [if_pos hc, ← hT B C σ c hc, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun T _ => ?_
        ring
      · simp only [if_neg hc, zero_mul, mul_zero, Finset.sum_const_zero]
    rw [Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun c _ => hterm σ c]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Finset (Fin e))))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Finset (Fin e))))]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun T _ => ?_
    ring
  unfold ReciprocityTheory.AnForm.M.locDens ReciprocityTheory.AnForm.maDens
  simp only [hL, hR]
  rw [hKey (fun k => hessC (fun y' => (P k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y +
      hessC (fun y' => f k ((A.chart j).symm y')) y)
    (hessC (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y)]
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [show ((-1 : ℂ) ^ (e - T.card)) = (((-1 : ℝ) ^ (e - T.card) : ℝ) : ℂ) by norm_num,
    Complex.re_ofReal_mul]
  ring

end

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalDensityInclusionExclusionStatement
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_density_inclusion_exclusion : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X) (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (Θ : LocPot X), IsOpen U → (∀ i, IsPotential A (P i)) → IsPotential A Θ → (∀ i, A.SmoothOn U (f i)) → ∀ j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U, locDens A (fun i => P i + LocPot.ofFun (f i)) j y = ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) * locDens A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) + LocPot.ofFun (if i ∈ T then f i else 0) + Θ) j y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.locDens_expand_ofFun | exact GlobalTheory.CompanionTheory.Ar.Giv.locDens_expand_ofFun | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.locDens_expand_ofFun <;> assumption)
end
end
