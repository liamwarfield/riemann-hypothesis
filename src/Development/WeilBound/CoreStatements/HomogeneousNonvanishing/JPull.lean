module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.ContinuousAtOfClosedRel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedC

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.JPull
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

theorem j_pull : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k), IsBlockMap κ v → (∀ A : HermLine ι, ∃! A' : HermLine ι', IsPullHerm κ v A A') ∧ (∀ (A : HermLine ι) (A' : HermLine ι'), IsPullHerm κ v A A' → IsSmoothHerm A → IsSmoothHerm A') ∧ (∀ (P' : Ideal (MRing ι')), ∀ z ∈ mcPts P', (fun p => z (v p)) ∈ mcPts (imageZ v P')) ∧ ∀ (z : (Σ k, ι' k) → ℂ) (f : MRing ι), evC z (rename v f) = evC (fun p => z (v p)) f := by
  intro K _ ι _ K' _ ι' _ κ v hv
  obtain ⟨hκ, hvi, hv1, hv2⟩ := hv
  have hnz : ∀ z : (Σ k, ι' k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∀ k, ∃ i, z (v ⟨k, i⟩) ≠ 0 := by
    intro z hz k
    obtain ⟨i', hi'⟩ := hz (κ k)
    obtain ⟨⟨k', i⟩, hp⟩ := hv2 ⟨κ k, i'⟩ ⟨k, rfl⟩
    have h1 : κ k' = κ k := by
      have := hv1 ⟨k', i⟩
      rw [hp] at this
      exact this.symm
    obtain rfl := hκ h1
    exact ⟨i, by rwa [hp]⟩
  have hev : ∀ (z : (Σ k, ι' k) → ℂ) (f : MRing ι), evC z (rename v f) = evC (fun p => z (v p)) f := by
    intro z f
    unfold evC
    rw [map_rename, eval_rename]
    rfl
  refine ⟨fun A => ⟨⟨pullDeg κ A.a, fun z => A.h fun p => z (v p), fun z hz => A.pos _ (hnz z hz), fun c z hc => ?_⟩,
    ⟨rfl, fun _ => rfl⟩, ?_⟩, fun A A' h hA => ?_, fun P' z hz => ⟨hnz z hz.1, fun f hf => ?_⟩, hev⟩
  · have h1 := A.smul (fun k => c (κ k)) (fun p => z (v p)) fun k => hc _
    simp only [hv1]
    rw [h1]
    congr 1
    refine Finset.prod_of_injOn κ hκ.injOn (fun _ _ => Finset.mem_univ _) (fun k' _ hk' => ?_) fun k _ => ?_
    · unfold pullDeg
      rw [Function.extend_apply' _ _ _ (by simpa using hk')]
      simp
    · unfold pullDeg
      rw [hκ.extend_apply]
  · rintro ⟨a, h, _, _⟩ ⟨h1, h2⟩
    obtain rfl : a = pullDeg κ A.a := h1
    obtain rfl : h = fun z => A.h fun p => z (v p) := funext h2
    rfl
  · unfold IsSmoothHerm
    rw [show A'.h = A.h ∘ fun z p => z (v p) from funext h.2]
    exact ContDiffOn.comp hA (contDiffOn_pi.mpr fun p => (contDiff_apply ℝ (fun _ => ℂ) (v p)).contDiffOn) fun z hz => hnz z hz
  · exact (hev z f).symm.trans (hz.2 _ hf)

end PositivityTheory.UnitarySelfGeneration
end

section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.IAlgebra
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

theorem ialg_one {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  have : m = 0 := by
    by_contra h
    rw [mem_support_iff, coeff_one, if_neg (Ne.symm h)] at hm
    exact hm rfl
  simp [this]

theorem ialg_mul {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {f g : MRing ι} {a b : K → ℕ}
    (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.1 (support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m₁ h₁ k, hg m₂ h₂ k]

theorem ialg_rename {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {κ : K → K'}
    {v : (Σ k, ι k) → Σ k, ι' k} (hv : IsBlockMap κ v) {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    IsMultiHomog (rename v f : MRing ι') (Function.extend κ a 0) := by
  classical
  intro m' hm' k'
  rw [support_rename_of_injective hv.2.1] at hm'
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hm'
  by_cases hk : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := hk
    rw [hv.1.extend_apply, ← hf m hm k]
    have hc : ∀ i : ι k, ∃ j : ι' (κ k), v ⟨k, i⟩ = ⟨κ k, j⟩ := by
      intro i
      have h1 := hv.2.2.1 ⟨k, i⟩
      generalize v ⟨k, i⟩ = q at h1
      obtain ⟨k₁, j⟩ := q
      obtain rfl : k₁ = κ k := h1
      exact ⟨j, rfl⟩
    choose e he using hc
    have hb : Function.Bijective e := by
      constructor
      · intro i i' h
        have : v ⟨k, i⟩ = v ⟨k, i'⟩ := by rw [he, he, h]
        exact sigma_mk_injective (β := ι) (hv.2.1 this)
      · intro j
        obtain ⟨⟨k₀, i⟩, hq⟩ := hv.2.2.2 ⟨κ k, j⟩ ⟨k, rfl⟩
        have hk : κ k₀ = κ k := by
          have := hv.2.2.1 ⟨k₀, i⟩
          rw [hq] at this
          exact this.symm
        obtain rfl := hv.1 hk
        exact ⟨i, sigma_mk_injective (β := ι') ((he i).symm.trans hq)⟩
    refine (Fintype.sum_bijective e hb _ _ fun i => ?_).symm
    rw [← he, Finsupp.mapDomain_apply_of_injective hv.2.1]
  · rw [Function.extend_apply' _ _ _ hk]
    refine Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨p, hp⟩
    refine hk ⟨p.1, ?_⟩
    rw [← hv.2.2.1 p, hp]

theorem i_algebra : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)), IsMultiProjPrime P → (∀ a, IsLineIso P a a 1 1) ∧ (∀ a b f g, IsLineIso P a b f g → IsLineIso P b a g f) ∧ (∀ a b c f g f' g', IsLineIso P a b f g → IsLineIso P b c f' g' → IsLineIso P a c (f * f') (g * g')) ∧ (∀ a b a' b' f g f' g', IsLineIso P a b f g → IsLineIso P a' b' f' g' → IsLineIso P (a + a') (b + b') (f * f') (g * g')) ∧ ∀ (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (P' : Ideal (MRing ι')), IsBlockMap κ v → imageZ v P' = P → ∀ a b f g, IsLineIso P a b f g → IsLineIso P' (pullDeg κ a) (pullDeg κ b) (rename v f) (rename v g) := by
  intro K _ ι _ P hP
  have hp : P.IsPrime := hP.1
  have tens : ∀ f g f' g' : MRing ι, UnitRatio P f g → UnitRatio P f' g' → UnitRatio P (f * f') (g * g') := by
    rintro f g f' g' ⟨hf, hg, h⟩ ⟨hf', hg', h'⟩
    refine ⟨fun hh => (hp.mem_or_mem hh).elim hf hf', fun hh => (hp.mem_or_mem hh).elim hg hg',
      fun W hW hPW hr => ?_⟩
    obtain ⟨u, v, hu, hv, huv⟩ := h W hW hPW hr
    obtain ⟨u', v', hu', hv', huv'⟩ := h' W hW hPW hr
    refine ⟨u * u', v * v', fun hh => (hW.mem_or_mem hh).elim hu hu', fun hh => (hW.mem_or_mem hh).elim hv hv', ?_⟩
    have := P.add_mem (P.mul_mem_left (u' * f') huv) (P.mul_mem_left (v * g) huv')
    convert this using 1
    ring
  refine ⟨fun a => ⟨⟨0, 0, ialg_one, ialg_one, by simp⟩, ?_⟩, ?_, ?_, ?_, ?_⟩
  · have h1 : (1 : MRing ι) ∉ P := (Ideal.ne_top_iff_one P).1 hp.ne_top
    exact ⟨h1, h1, fun W hW _ _ => ⟨1, 1, (Ideal.ne_top_iff_one W).1 hW.ne_top,
      (Ideal.ne_top_iff_one W).1 hW.ne_top, by simp⟩⟩
  · rintro a b f g ⟨⟨α, γ, h1, h2, h3⟩, hf, hg, h⟩
    refine ⟨⟨γ, α, h2, h1, fun k => by linarith [h3 k]⟩, hg, hf, fun W hW hPW hr => ?_⟩
    obtain ⟨u, v, hu, hv, huv⟩ := h W hW hPW hr
    exact ⟨v, u, hv, hu, by simpa using P.neg_mem huv⟩
  · rintro a b c f g f' g' ⟨⟨α, γ, h1, h2, h3⟩, h⟩ ⟨⟨α', γ', h1', h2', h3'⟩, h'⟩
    refine ⟨⟨α + α', γ + γ', ialg_mul h1 h1', ialg_mul h2 h2', fun k => ?_⟩, tens _ _ _ _ h h'⟩
    simp only [Pi.add_apply, Nat.cast_add]
    linarith [h3 k, h3' k]
  · rintro a b a' b' f g f' g' ⟨⟨α, γ, h1, h2, h3⟩, h⟩ ⟨⟨α', γ', h1', h2', h3'⟩, h'⟩
    refine ⟨⟨α + α', γ + γ', ialg_mul h1 h1', ialg_mul h2 h2', fun k => ?_⟩, tens _ _ _ _ h h'⟩
    simp only [Pi.add_apply, Nat.cast_add]
    linarith [h3 k, h3' k]
  · rintro K' _ ι' _ κ v P' hv rfl a b f g ⟨⟨α, γ, h1, h2, h3⟩, hf, hg, h⟩
    refine ⟨⟨Function.extend κ α 0, Function.extend κ γ 0, ialg_rename hv h1, ialg_rename hv h2, fun k' => ?_⟩,
      hf, hg, fun W hW hPW hr => ?_⟩
    · unfold pullDeg
      by_cases hk : ∃ k, κ k = k'
      · obtain ⟨k, rfl⟩ := hk
        simp only [hv.1.extend_apply]
        exact h3 k
      · simp only [Function.extend_apply' _ _ _ hk]
        simp
    · have hr' : IsRelevant (imageZ v W) := by
        intro k
        obtain ⟨i, hi⟩ := hr (κ k)
        obtain ⟨⟨k₀, j⟩, hq⟩ := hv.2.2.2 ⟨κ k, i⟩ ⟨k, rfl⟩
        have hk : κ k₀ = κ k := by
          have := hv.2.2.1 ⟨k₀, j⟩
          rw [hq] at this
          exact this.symm
        obtain rfl := hv.1 hk
        refine ⟨j, fun hh => hi ?_⟩
        have : rename v (X ⟨k₀, j⟩ : MRing ι) ∈ W := hh
        rwa [rename_X, hq] at this
      obtain ⟨u, w, hu, hw, huw⟩ := h (imageZ v W) (Ideal.comap_isPrime _ W) (Ideal.comap_mono hPW) hr'
      refine ⟨rename v u, rename v w, hu, hw, ?_⟩
      have : rename v (u * f - w * g) ∈ P' := huw
      simpa using this

end PositivityTheory.UnitarySelfGeneration
end

section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.IsOpenHoloPreimage
namespace PositivityTheory.UnitarySelfGeneration.HolomorphicMinorCharts

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology Set
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap)

set_option linter.unusedSectionVars false

section Charts

variable {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem holo_comp {A : FinHolAtlas e X} {B : FinHolAtlas e' Y} {ρ : Y → X} {N : Set Y} {V : Set X} {g : X → ℂ}
    (hg : A.HoloOn V g) (hN : ∀ y ∈ N, ρ y ∈ V) (hc : ∀ y ∈ N, ContinuousAt ρ y)
    (ha : ∀ y ∈ N, ∀ j k, y ∈ (B.chart j).source → ρ y ∈ (A.chart k).source →
      AnalyticAt ℂ (A.chart k ∘ ρ ∘ (B.chart j).symm) (B.chart j y)) : B.HoloOn N fun y => g (ρ y) := by
  intro j w hw
  obtain ⟨k, hk⟩ := A.cover (ρ ((B.chart j).symm w))
  have h1 := ha _ hw.2 j k ((B.chart j).map_target hw.1) hk
  rw [(B.chart j).right_inv hw.1] at h1
  refine (AnalyticAt.comp (f := A.chart k ∘ ρ ∘ (B.chart j).symm) (holo_analyticAt hg k hk (hN _ hw.2)) h1).congr ?_
  filter_upwards [((hc _ hw.2).comp ((B.chart j).continuousAt_symm hw.1)) ((A.chart k).open_source.mem_nhds hk)]
    with v hv
  simp only [Function.comp_apply]
  exact congrArg g ((A.chart k).left_inv hv)

theorem holo_comp_map {A : FinHolAtlas e X} {B : FinHolAtlas e' Y} {ρ : Y → X} (h : HoloMap B A ρ) {V : Set X}
    {g : X → ℂ} (hg : A.HoloOn V g) : B.HoloOn (ρ ⁻¹' V) fun y => g (ρ y) :=
  holo_comp hg (fun _ hy => hy) (fun _ _ => h.1.continuousAt) fun y _ j k hj hk =>
    h.2 j k _ ⟨(B.chart j).map_source hj, by rwa [mem_preimage, (B.chart j).left_inv hj]⟩

theorem holo_mono {A : FinHolAtlas e X} {U V : Set X} {g : X → ℂ} (hg : A.HoloOn V g) (h : U ⊆ V) : A.HoloOn U g :=
  fun j => (hg j).mono fun _ hw => ⟨hw.1, h hw.2⟩

theorem isOpen_holo_preimage {A : FinHolAtlas e X} {N : Set X} (hN : IsOpen N) {q : X → ℂ} (hq : A.HoloOn N q)
    {T : Set ℂ} (hT : IsOpen T) : IsOpen (N ∩ q ⁻¹' T) :=
  ContinuousOn.isOpen_inter_preimage (fun _ hy => (holo_continuousAt hq hy).continuousWithinAt) hN hT

theorem exists_log {A : FinHolAtlas e X} {N : Set X} (hN : IsOpen N) {q : X → ℂ} (hq : A.HoloOn N q) {x : X}
    (hx : x ∈ N) (h0 : q x ≠ 0) : ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ⊆ N ∧ ∃ G : X → ℂ, A.HoloOn W G ∧
      ∀ y ∈ W, Real.log ‖q y‖ = (G y).re := by
  have hq' : A.HoloOn N fun y => q y / q x := fun j w hw => (hq j w hw).div_const
  refine ⟨N ∩ (fun y => q y / q x) ⁻¹' Complex.slitPlane, isOpen_holo_preimage hN hq' Complex.isOpen_slitPlane,
    ⟨hx, by simp [h0]⟩, inter_subset_left, fun y => Complex.log (q y / q x) + (Real.log ‖q x‖ : ℝ),
    fun j w hw => ((hq' j w ⟨hw.1, hw.2.1⟩).clog hw.2.2).add analyticAt_const, fun y hy => ?_⟩
  have h1 : q y ≠ 0 := fun h => Complex.slitPlane_ne_zero hy.2 (by simp [h])
  rw [Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
    Real.log_div (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h0)]
  ring

end Charts

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem log_h_orbit (L : HermLine ι) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (L.h fun p => c p.1 * z p) = Real.log ‖∏ k, c k ^ L.a k‖ + Real.log (L.h z) := by
  rw [L.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k)))
    (L.pos z hz).ne']
  simp only [norm_prod, norm_zpow]

theorem orbit_re {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} (L : HermLine ι) {N : Set X}
    (hN : IsOpen N) {lam mu : X → (Σ k, ι k) → ℂ} (hl : ∀ p, A.HoloOn N fun y => lam y p)
    (hm : ∀ p, A.HoloOn N fun y => mu y p) (hnz : ∀ y ∈ N, ∀ k, ∃ i, mu y ⟨k, i⟩ ≠ 0)
    (hso : ∀ y ∈ N, SameOrbit (lam y) (mu y)) {x : X} (hx : x ∈ N) :
    ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ⊆ N ∧ ∃ G : X → ℂ, A.HoloOn W G ∧
      ∀ y ∈ W, Real.log (L.h (lam y)) - Real.log (L.h (mu y)) = (G y).re := by
  choose p hp using hnz x hx
  have hN' : IsOpen (N ∩ ⋂ k, (N ∩ (fun y => mu y ⟨k, p k⟩) ⁻¹' {0}ᶜ)) :=
    hN.inter (isOpen_iInter_of_finite fun k => isOpen_holo_preimage hN (hm _) isOpen_compl_singleton)
  have hne : ∀ y ∈ N ∩ ⋂ k, (N ∩ (fun y => mu y ⟨k, p k⟩) ⁻¹' {0}ᶜ), ∀ k, mu y ⟨k, p k⟩ ≠ 0 :=
    fun y hy k => (mem_iInter.mp hy.2 k).2
  obtain ⟨W, hW, hxW, hWN, G, hG, hE⟩ := exists_log (A := A) hN'
    (q := fun y => ∏ k, (lam y ⟨k, p k⟩ / mu y ⟨k, p k⟩) ^ L.a k) (x := x)
    (fun j w hw => Finset.analyticAt_fun_prod _ fun k _ =>
      ((hl ⟨k, p k⟩ j w ⟨hw.1, hw.2.1⟩).fun_div (hm ⟨k, p k⟩ j w ⟨hw.1, hw.2.1⟩) (hne _ hw.2 k)).fun_zpow
        (div_ne_zero ((ne_zero_so (hso _ hw.2.1) _).mpr (hne _ hw.2 k)) (hne _ hw.2 k)))
    ⟨hx, mem_iInter.mpr fun k => ⟨hx, hp k⟩⟩
    (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (div_ne_zero ((ne_zero_so (hso _ hx) _).mpr (hp k)) (hp k)))
  refine ⟨W, hW, hxW, fun y hy => (hWN hy).1, G, hG, fun y hy => ?_⟩
  rw [← hE y hy]
  obtain ⟨c, hc, h⟩ := hso y (hWN hy).1
  rw [h, log_h_orbit L hc (hnz y (hWN hy).1)]
  simp only [fun k => mul_div_cancel_right₀ (c k) (hne y (hWN hy) k)]
  ring

theorem eval_ne_so {g : MRing ι} {a : K → ℕ} (hg : IsMultiHomog g a) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    eval z (map (Int.castRingHom ℂ) g) = 0 ↔ eval z' (map (Int.castRingHom ℂ) g) = 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [eval_smul_homog g a hg, mul_eq_zero]
  exact or_iff_right (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k))

theorem isOpen_nonvan {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) {g : MRing ι} {a : K → ℕ}
    (hg : IsMultiHomog g a) : IsOpen {x | eval (R.lift x x) (map (Int.castRingHom ℂ) g) ≠ 0} := by
  refine isOpen_iff_mem_nhds.mpr fun x hx => ?_
  filter_upwards [(holo_continuousAt (holoOn_eval_lift R x g) (R.mem_U x)).eventually_ne hx,
    (R.isOpen_U x).mem_nhds (R.mem_U x)] with y h1 h2 h3
  exact h1 ((eval_ne_so hg (R.compat x y y ⟨h2, R.mem_U y⟩)).mpr h3)

theorem exists_homog_not_mem {P J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) (h : ¬ J ≤ P) :
    ∃ f a, f ∈ J ∧ f ∉ P ∧ IsMultiHomog f a := by
  obtain ⟨S, hS, rfl⟩ := hJ
  rw [Ideal.span_le] at h
  obtain ⟨f, h1, h2⟩ := Set.not_subset.mp h
  obtain ⟨a, ha⟩ := hS f h1
  exact ⟨f, a, Ideal.subset_span h1, h2, ha⟩

variable {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem so_pull {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hv : IsBlockMap κ v) {z z' : (Σ k, ι' k) → ℂ}
    (h : SameOrbit z z') : SameOrbit (fun p => z (v p)) fun p => z' (v p) := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c (κ k), fun k => hc _, funext fun p => by simp only [hv.2.2.1]⟩

theorem homog_rename {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hv : IsBlockMap κ v) {f : MRing ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) : ∃ b, IsMultiHomog (rename v f) b := by
  classical
  refine ⟨fun k' => ∑ k, if κ k = k' then a k else 0, fun m hm k' => ?_⟩
  obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero v f m (mem_support_iff.mp hm)
  have h1 : ∀ m : (Σ k, ι' k) →₀ ℕ, ∑ i, m ⟨k', i⟩ = m.sum fun q n => if q.1 = k' then n else 0 := fun m => by
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, Finset.sum_eq_single k']
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  rw [h1, Finsupp.sum_mapDomain_index (by simp) (fun _ _ _ => by split_ifs <;> simp),
    Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hv.2.2.1]
  split_ifs
  · exact hf u (mem_support_iff.mpr hu) k
  · simp

end PositivityTheory.UnitarySelfGeneration.HolomorphicMinorCharts
end
