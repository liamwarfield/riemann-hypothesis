module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsReferenceGeometrySameGeneric
public import Development.WeilBound.CoreStatements.CentralCharts.ReferenceGeometryHolomorphicInverse
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsEffectiveWeightSection
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AmpleOfSingleCoordBlock
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGoodPrimesFinite
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCoordsOverField
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TriangularSpanCoeffRatio

@[expose] public section

attribute [-instance] GlobalTheory.CompHt.fintypePsi

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsHolomorphicSectionOfAnalytic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_section_of_analytic : Top.Given → Flat.FlatLineGenerator → Flat.FlatLineGeneratorComponent → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), Top.IsGlobal Xo l c Y → SplitComps Y → 1 ≤ D.p → 1 ≤ D.q → ∀ G : RefGeo Y, ∃ A : G.An, (∃ inv : A.Sys.X → A.Re.R.X, ReciprocityTheory.AnForm.M.HoloMap A.Sys.A A.Re.R.A inv ∧ ∀ x, inv (A.Re.π x) = x) := by
  first | exact @AnalyticReference.reference_geometry_holomorphic_inverse | exact AnalyticReference.reference_geometry_holomorphic_inverse | (intros; apply AnalyticReference.reference_geometry_holomorphic_inverse <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EffectiveScaledWeightOfRetraction
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SameOrbitOfProportionalCoords
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SameOrbitOfProportionalCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.OrbitBlock

theorem aeval_smul_of_homog {σ A : Type} [Fintype σ] [CommRing A] [Algebra ℤ A] {n : ℕ}
    {F : MvPolynomial σ ℤ} (hF : F.IsHomogeneous n) (t : A) (b : σ → A) :
    MvPolynomial.aeval (fun i => t * b i) F = t ^ n * MvPolynomial.aeval b F := by
  classical
  simp only [MvPolynomial.aeval_def]
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = n := by
    have h := hF (MvPolynomial.mem_support_iff.1 hd)
    rw [← h, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]

theorem mConeMap_rename_block {n : ℕ} (y : (Σ k, J k) → Ω) (k₀ : K)
    {F : MvPolynomial (J k₀) ℤ} (hF : F.IsHomogeneous n) :
    mConeMap y (MvPolynomial.rename (Sigma.mk k₀) F) =
      MvPolynomial.X k₀ ^ n *
        MvPolynomial.C (MvPolynomial.aeval (fun i : J k₀ => y ⟨k₀, i⟩) F) := by
  have h1 : mConeMap y (MvPolynomial.rename (Sigma.mk k₀) F) =
      MvPolynomial.aeval (fun i : J k₀ => (MvPolynomial.X k₀ : MvPolynomial K Ω) *
        MvPolynomial.C (y ⟨k₀, i⟩)) F := by
    rw [mConeMap, MvPolynomial.aeval_rename]
    congr 2
    funext i
    simp [mul_comm]
  rw [h1, aeval_smul_of_homog hF]
  congr 1
  exact (MvPolynomial.comp_aeval_apply (fun i : J k₀ => y ⟨k₀, i⟩)
    (IsScalarTower.toAlgHom ℤ Ω (MvPolynomial K Ω)) F).symm

theorem relation_at {n : ℕ} (y : (Σ k, J k) → Ω) (k₀ k : K) (c j : J k)
    {Fj Fc : MvPolynomial (J k₀) ℤ} (hj : Fj.IsHomogeneous n) (hc : Fc.IsHomogeneous n)
    (h : MvPolynomial.aeval (fun i : J k₀ => y ⟨k₀, i⟩) Fj * y ⟨k, c⟩ =
      MvPolynomial.aeval (fun i : J k₀ => y ⟨k₀, i⟩) Fc * y ⟨k, j⟩)
    {w : (Σ k, J k) → ℂ} (hw : w ∈ mcPts (mCoordIdeal y)) :
    MvPolynomial.aeval (fun i : J k₀ => w ⟨k₀, i⟩) Fj * w ⟨k, c⟩ =
      MvPolynomial.aeval (fun i : J k₀ => w ⟨k₀, i⟩) Fc * w ⟨k, j⟩ := by
  set G : MRing J := MvPolynomial.rename (Sigma.mk k₀) Fj * MvPolynomial.X ⟨k, c⟩ -
    MvPolynomial.rename (Sigma.mk k₀) Fc * MvPolynomial.X ⟨k, j⟩ with hG
  have hmem : G ∈ mCoordIdeal y := by
    rw [mCoordIdeal, RingHom.mem_ker, hG, map_sub, map_mul, map_mul,
      mConeMap_rename_block y k₀ hj, mConeMap_rename_block y k₀ hc]
    have hx : ∀ p : Σ k, J k, mConeMap y (MvPolynomial.X p) =
        MvPolynomial.C (y p) * MvPolynomial.X p.1 := fun p => by
      simp [mConeMap]
    rw [hx, hx]
    have h' := congrArg (MvPolynomial.C : Ω →+* MvPolynomial K Ω) h
    simp only [map_mul] at h'
    linear_combination (MvPolynomial.X k₀ ^ n * MvPolynomial.X k) * h'
  have hv := hw.2 G hmem
  have hv' : MvPolynomial.aeval w G = 0 := by
    rw [← hv, MvPolynomial.eval_map]
    rfl
  rw [hG, map_sub, map_mul, map_mul, MvPolynomial.aeval_rename, MvPolynomial.aeval_rename,
    MvPolynomial.aeval_X, MvPolynomial.aeval_X] at hv'
  exact sub_eq_zero.1 hv'

theorem sameOrbit_of_block : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → ∀ w ∈ mcPts (mCoordIdeal y), ∀ w' ∈ mcPts (mCoordIdeal y), ∀ u : ℂ, (∀ i : J k₀, w ⟨k₀, i⟩ = u * w' ⟨k₀, i⟩) → SameOrbit w w' := by
  intro X Ω _ _ ξ K _ J _ y k₀ hT hE w hw w' hw' u hu
  have hpts : w ∈ Small.ptsOver ℂ (mCoordIdeal y) := by
    refine ⟨hw.1, fun f hf => ?_⟩
    rw [← hw.2 f hf, MvPolynomial.eval_map]
    rfl
  obtain ⟨i, hi⟩ := hw.1 k₀
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hi (by rw [hu i, zero_mul])
  have key : ∀ k, ∃ s : ℂ, s ≠ 0 ∧ ∀ j, w ⟨k, j⟩ = s * w' ⟨k, j⟩ := by
    intro k
    obtain ⟨c, hc⟩ := hw.1 k
    obtain ⟨n, F, hF, hrel, hne⟩ :=
      GlobalTheory.T.small_points_coord_ratio_bound X Ω ξ K J y k₀ hT hE ℂ w hpts i k c hi hc
    have hscale : ∀ t, MvPolynomial.aeval (fun i' : J k₀ => w ⟨k₀, i'⟩) (F t) =
        u ^ n * MvPolynomial.aeval (fun i' : J k₀ => w' ⟨k₀, i'⟩) (F t) := by
      intro t
      rw [← aeval_smul_of_homog (hF t)]
      congr 2
      funext i'
      exact hu i'
    have hne' : MvPolynomial.aeval (fun i' : J k₀ => w' ⟨k₀, i'⟩) (F c) ≠ 0 := by
      intro h0
      exact hne (by rw [hscale, h0, mul_zero])
    have r := fun j => relation_at y k₀ k c j (hF j) (hF c) (hrel j) hw
    have r' := fun j => relation_at y k₀ k c j (hF j) (hF c) (hrel j) hw'
    have hc' : w' ⟨k, c⟩ ≠ 0 := by
      intro h0
      obtain ⟨j, hj⟩ := hw'.1 k
      have := r' j
      rw [h0, mul_zero] at this
      exact (mul_ne_zero hne' hj) this.symm
    refine ⟨w ⟨k, c⟩ / w' ⟨k, c⟩, div_ne_zero hc hc', fun j => ?_⟩
    have e1 := r j
    have e2 := r' j
    rw [hscale, hscale] at e1
    have hun : u ^ n ≠ 0 := pow_ne_zero n hu0
    have e3 : MvPolynomial.aeval (fun i' : J k₀ => w' ⟨k₀, i'⟩) (F j) * w ⟨k, c⟩ =
        MvPolynomial.aeval (fun i' : J k₀ => w' ⟨k₀, i'⟩) (F c) * w ⟨k, j⟩ :=
      mul_left_cancel₀ hun (by linear_combination e1)
    apply mul_left_cancel₀ hne'
    have e4 : w ⟨k, c⟩ / w' ⟨k, c⟩ * w' ⟨k, c⟩ = w ⟨k, c⟩ := div_mul_cancel₀ _ hc'
    linear_combination (-1 : ℂ) * e3 + (w ⟨k, c⟩ / w' ⟨k, c⟩) * e2 -
      MvPolynomial.aeval (fun i' : J k₀ => w' ⟨k₀, i'⟩) (F j) * e4
  choose s hs0 hs using key
  exact ⟨s, hs0, funext fun p => by
    obtain ⟨k, j⟩ := p
    exact hs k j⟩

end GlobalTheory.CompanionTheory.Ar.OrbitBlock
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SameOrbitOfProportionalCoordsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.same_orbit_of_proportional_coords : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → ∀ w ∈ mcPts (mCoordIdeal y), ∀ w' ∈ mcPts (mCoordIdeal y), ∀ u : ℂ, (∀ i : J k₀, w ⟨k₀, i⟩ = u * w' ⟨k₀, i⟩) → SameOrbit w w' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrbitBlock.sameOrbit_of_block | exact GlobalTheory.CompanionTheory.Ar.OrbitBlock.sameOrbit_of_block | (intros; apply GlobalTheory.CompanionTheory.Ar.OrbitBlock.sameOrbit_of_block <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicInverseChartValue
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicInverseChartValue
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ImmersionBiholo


open Topology in
theorem ker_fderiv_comp_biholo : ∀ (e : ℕ) (X₁ X₂ V : Type) [TopologicalSpace X₁] [TopologicalSpace X₂] [NormedAddCommGroup V] [NormedSpace ℂ V] (A₁ : ReciprocityTheory.AnForm.M.FinHolAtlas e X₁) (A₂ : ReciprocityTheory.AnForm.M.FinHolAtlas e X₂) (π : X₁ → X₂) (inv : X₂ → X₁), ReciprocityTheory.AnForm.M.HoloMap A₁ A₂ π → ReciprocityTheory.AnForm.M.HoloMap A₂ A₁ inv → Function.Bijective π → (∀ x, inv (π x) = x) → ∀ (Φ : X₁ → V) (x : X₂) (j₁ : Fin A₁.n) (j₂ : Fin A₂.n), inv x ∈ (A₁.chart j₁).source → x ∈ (A₂.chart j₂).source → DifferentiableAt ℂ (fun v => Φ ((A₁.chart j₁).symm v)) (A₁.chart j₁ (inv x)) → (fderiv ℂ (fun v => Φ ((A₁.chart j₁).symm v)) (A₁.chart j₁ (inv x))).ker = ⊥ → (fderiv ℂ (fun v => Φ (inv ((A₂.chart j₂).symm v))) (A₂.chart j₂ x)).ker = ⊥ := by
  intro e X₁ X₂ V _ _ _ _ A₁ A₂ π inv hπ hinv hbij hleft Φ x j₁ j₂ hx₁ hx₂ hdiff hker
  have hright : ∀ y, π (inv y) = y := fun y => by
    obtain ⟨w, rfl⟩ := hbij.2 y
    rw [hleft]
  have hy : A₂.chart j₂ x ∈ (A₂.chart j₂).target := (A₂.chart j₂).map_source hx₂
  have hsy : (A₂.chart j₂).symm (A₂.chart j₂ x) = x := (A₂.chart j₂).left_inv hx₂
  have hz : A₁.chart j₁ (inv x) ∈ (A₁.chart j₁).target := (A₁.chart j₁).map_source hx₁
  have hsz : (A₁.chart j₁).symm (A₁.chart j₁ (inv x)) = inv x := (A₁.chart j₁).left_inv hx₁
  have hτ : DifferentiableAt ℂ (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x) := by
    have hmem : A₂.chart j₂ x ∈ (A₂.chart j₂).target ∩
        ⇑(A₂.chart j₂).symm ⁻¹' (inv ⁻¹' (A₁.chart j₁).source) := by
      refine ⟨hy, ?_⟩
      show inv ((A₂.chart j₂).symm (A₂.chart j₂ x)) ∈ (A₁.chart j₁).source
      rw [hsy]
      exact hx₁
    exact (hinv.2 j₂ j₁ _ hmem).differentiableAt
  have hσ : DifferentiableAt ℂ (⇑(A₂.chart j₂) ∘ π ∘ ⇑(A₁.chart j₁).symm) (A₁.chart j₁ (inv x)) := by
    have hmem : A₁.chart j₁ (inv x) ∈ (A₁.chart j₁).target ∩
        ⇑(A₁.chart j₁).symm ⁻¹' (π ⁻¹' (A₂.chart j₂).source) := by
      refine ⟨hz, ?_⟩
      show π ((A₁.chart j₁).symm (A₁.chart j₁ (inv x))) ∈ (A₂.chart j₂).source
      rw [hsz, hright]
      exact hx₂
    exact (hπ.2 j₁ j₂ _ hmem).differentiableAt
  have hev : ∀ᶠ v in 𝓝 (A₂.chart j₂ x),
      v ∈ (A₂.chart j₂).target ∧ inv ((A₂.chart j₂).symm v) ∈ (A₁.chart j₁).source := by
    refine Filter.Eventually.and ((A₂.chart j₂).open_target.mem_nhds hy) ?_
    have hc : ContinuousAt (inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x) :=
      hinv.1.continuousAt.comp ((A₂.chart j₂).continuousAt_symm hy)
    have hs : (A₁.chart j₁).source ∈ 𝓝 ((inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x)) := by
      rw [Function.comp_apply, hsy]
      exact (A₁.chart j₁).open_source.mem_nhds hx₁
    exact hc.preimage_mem_nhds hs
  have hτz : (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x) = A₁.chart j₁ (inv x) := by
    simp only [Function.comp_apply, hsy]
  have hσ' : DifferentiableAt ℂ (⇑(A₂.chart j₂) ∘ π ∘ ⇑(A₁.chart j₁).symm)
      ((⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x)) := by
    rw [hτz]
    exact hσ
  have hid : (⇑(A₂.chart j₂) ∘ π ∘ ⇑(A₁.chart j₁).symm) ∘ (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm)
      =ᶠ[𝓝 (A₂.chart j₂ x)] id := by
    filter_upwards [hev] with v hv
    simp only [Function.comp_apply, id_eq]
    rw [(A₁.chart j₁).left_inv hv.2, hright, (A₂.chart j₂).right_inv hv.1]
  have hcomp : (fderiv ℂ (⇑(A₂.chart j₂) ∘ π ∘ ⇑(A₁.chart j₁).symm)
      ((⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x))).comp
      (fderiv ℂ (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x))
      = ContinuousLinearMap.id ℂ (Fin e → ℂ) := by
    rw [← fderiv_comp _ hσ' hτ, hid.fderiv_eq, fderiv_id]
  have hτinj : ∀ w, fderiv ℂ (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x) w = 0 → w = 0 := by
    intro w hw
    have h := congrArg (fun L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ) => L w) hcomp
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hw, map_zero] at h
    exact h.symm
  have hdiff' : DifferentiableAt ℂ (fun v => Φ ((A₁.chart j₁).symm v))
      ((⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x)) := by
    rw [hτz]
    exact hdiff
  have hker' : (fderiv ℂ (fun v => Φ ((A₁.chart j₁).symm v))
      ((⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x))).ker = ⊥ := by
    rw [hτz]
    exact hker
  have hfeq : (fun v => Φ (inv ((A₂.chart j₂).symm v))) =ᶠ[𝓝 (A₂.chart j₂ x)]
      (fun v => Φ ((A₁.chart j₁).symm v)) ∘ (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) := by
    filter_upwards [hev] with v hv
    simp only [Function.comp_apply]
    rw [(A₁.chart j₁).left_inv hv.2]
  rw [hfeq.fderiv_eq, fderiv_comp _ hdiff' hτ, eq_bot_iff]
  intro w hw
  rw [Submodule.mem_bot]
  apply hτinj
  have h1 : fderiv ℂ (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x) w ∈
      (fderiv ℂ (fun v => Φ ((A₁.chart j₁).symm v))
        ((⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x))).ker := hw
  rw [hker'] at h1
  exact h1

end GlobalTheory.CompanionTheory.Ar.ImmersionBiholo
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicInverseChartValueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_inverse_chart_value : ∀ (e : ℕ) (X₁ X₂ V : Type) [TopologicalSpace X₁] [TopologicalSpace X₂] [NormedAddCommGroup V] [NormedSpace ℂ V] (A₁ : ReciprocityTheory.AnForm.M.FinHolAtlas e X₁) (A₂ : ReciprocityTheory.AnForm.M.FinHolAtlas e X₂) (π : X₁ → X₂) (inv : X₂ → X₁), ReciprocityTheory.AnForm.M.HoloMap A₁ A₂ π → ReciprocityTheory.AnForm.M.HoloMap A₂ A₁ inv → Function.Bijective π → (∀ x, inv (π x) = x) → ∀ (Φ : X₁ → V) (x : X₂) (j₁ : Fin A₁.n) (j₂ : Fin A₂.n), inv x ∈ (A₁.chart j₁).source → x ∈ (A₂.chart j₂).source → DifferentiableAt ℂ (fun v => Φ ((A₁.chart j₁).symm v)) (A₁.chart j₁ (inv x)) → (fderiv ℂ (fun v => Φ ((A₁.chart j₁).symm v)) (A₁.chart j₁ (inv x))).ker = ⊥ → (fderiv ℂ (fun v => Φ (inv ((A₂.chart j₂).symm v))) (A₂.chart j₂ x)).ker = ⊥ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ImmersionBiholo.ker_fderiv_comp_biholo | exact GlobalTheory.CompanionTheory.Ar.ImmersionBiholo.ker_fderiv_comp_biholo | (intros; apply GlobalTheory.CompanionTheory.Ar.ImmersionBiholo.ker_fderiv_comp_biholo <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicConstantsInRange
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicConstantsInRange
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagConst

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem exists_C_eq_of_isAlgebraic {k I : Type} [Field k] (P : MvPolynomial I k) (h : IsAlgebraic k P) :
    ∃ p : k, MvPolynomial.C p = P := by
  by_cases h0 : P = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨r, hr, hd⟩ := h.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero h0)
  have hu : IsUnit P := isUnit_of_dvd_unit hd ((IsUnit.mk0 r hr).map (algebraMap k _))
  obtain ⟨p, -, hp⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 hu
  exact ⟨p, hp.symm⟩

theorem mem_range_of_isAlgebraic {k L I : Type} [Field k] [Field L] [Algebra k L] (x : I → L)
    (hx : AlgebraicIndependent k x) (ht : IntermediateField.adjoin k (Set.range x) = ⊤) (a : L)
    (ha : IsAlgebraic k a) : a ∈ (algebraMap k L).range := by
  let g : MvPolynomial I k →ₐ[k] L := MvPolynomial.aeval x
  have hg : Function.Injective g := hx
  letI : Algebra (MvPolynomial I k) L := g.toRingHom.toAlgebra
  have hmap : ∀ P : MvPolynomial I k, algebraMap (MvPolynomial I k) L P = g P := fun _ => rfl
  haveI : IsScalarTower k (MvPolynomial I k) L := IsScalarTower.of_algebraMap_eq fun r => (g.commutes r).symm
  haveI : FaithfulSMul (MvPolynomial I k) L := (faithfulSMul_iff_algebraMap_injective _ _).2 hg
  haveI : IsFractionRing (MvPolynomial I k) L := by
    refine IsFractionRing.of_field _ _ fun z => ?_
    have hz : z ∈ IntermediateField.adjoin k (Set.range x) := ht ▸ IntermediateField.mem_top
    obtain ⟨r, s, e⟩ := (IntermediateField.mem_adjoin_range_iff k x z).1 hz
    exact ⟨r, s, e⟩
  have hi : IsIntegral (MvPolynomial I k) a := (ha.isIntegral).tower_top
  obtain ⟨P, hP⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  have hPa : IsAlgebraic k P := by
    rw [← isAlgebraic_algHom_iff g hg, ← hmap, hP]
    exact ha
  obtain ⟨p, rfl⟩ := exists_C_eq_of_isAlgebraic P hPa
  refine ⟨p, ?_⟩
  rw [← hP, hmap]
  exact (g.commutes p).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem exists_cst₀ {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K]
    {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) :
    ∃ cst₀ : c.F →+* 𝔐.Ω₀, 𝔐.fn.comp cst₀ = 𝔐.cst ∧
      𝔐.ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F)) := by
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := {}
  let b₀ : 𝓞 c.F →+* 𝔐.Ω₀ := (Spec.preimage (𝔐.ξ₀ ≫ Y.s)).hom
  have hb : 𝔐.ξ₀ ≫ Y.s = spMap b₀ := (Spec.map_preimage _).symm
  have hc : 𝔐.fn.comp b₀ = 𝔐.cst.comp (algebraMap (𝓞 c.F) c.F) := by
    have hsp : spMap (𝔐.fn.comp b₀) = spMap (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      have hd : 𝔐.ξ ≫ 𝔐.f = spMap 𝔐.fn ≫ 𝔐.ξ₀ := 𝔐.fn_over
      have hm : spMap (𝔐.fn.comp b₀) = spMap 𝔐.fn ≫ spMap b₀ := by
        rw [← Spec.map_comp]; rfl
      rw [hm, ← hb, ← 𝔐.cst_over, ← Category.assoc, ← Category.assoc, hd]
    have := CommRingCat.hom_ext_iff.1 (Spec.map_injective hsp)
    simpa using this
  have hinj : Function.Injective b₀ := by
    intro u v huv
    have h := congrArg 𝔐.fn huv
    have hu : ∀ w, 𝔐.fn (b₀ w) = 𝔐.cst (algebraMap (𝓞 c.F) c.F w) := fun w => RingHom.congr_fun hc w
    rw [hu, hu] at h
    exact IsFractionRing.injective (𝓞 c.F) c.F (𝔐.cst.injective h)
  let cst₀ : c.F →+* 𝔐.Ω₀ := IsFractionRing.lift hinj
  have hl : cst₀.comp (algebraMap (𝓞 c.F) c.F) = b₀ := by
    ext w
    exact IsFractionRing.lift_algebraMap hinj w
  refine ⟨cst₀, ?_, by rw [hl, hb]⟩
  refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) ?_
  rw [RingHom.comp_assoc, hl, hc]

theorem isAlgebraic_mem_cst_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag), SplitComps Y → Fl.deg = 1 → ∀ a : Ω, IsAlgebraic ℤ a → a ∈ 𝔐.cst.range := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 Fl hS hdeg a ha
  obtain ⟨cst₀, h1, h2⟩ := exists_cst₀ 𝔐
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  letI : Algebra 𝔐.Ω₀ Ω := 𝔐.fn.toAlgebra
  obtain ⟨-, u, -, -, -, -, hdiag, hup, -, hind, -, hfin⟩ := Fl.generic
  rw [hdeg] at hfin
  let x : (Σ q : CMType H ⊕ CMType H, {lk : Fin (labelRk D q) × Fin (labelRk D q) // lk.2 < lk.1}) → Ω :=
    fun q => u q.1 q.2.1.1 q.2.1.2
  let A := IntermediateField.adjoin 𝔐.Ω₀
    (Set.range fun q : Σ σ, Fin (labelRk D σ) × Fin (labelRk D σ) => u q.1 q.2.1 q.2.2)
  have hA : A = ⊤ := by
    have hb := Subalgebra.bot_eq_top_of_finrank_eq_one hfin
    refine eq_top_iff.2 fun z _ => ?_
    have hz : z ∈ (⊥ : Subalgebra A Ω) := hb ▸ Algebra.mem_top
    obtain ⟨w, rfl⟩ := Algebra.mem_bot.1 hz
    exact w.2
  have ht : IntermediateField.adjoin 𝔐.Ω₀ (Set.range x) = ⊤ := by
    refine eq_top_iff.2 (hA ▸ ?_)
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨⟨σ, l', k⟩, rfl⟩
    rcases lt_trichotomy l' k with h | h | h
    · show u σ l' k ∈ _
      rw [hup σ l' k h]
      exact zero_mem _
    · subst h
      show u σ l' l' ∈ _
      rw [hdiag σ l']
      exact one_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨σ, ⟨(l', k), h⟩⟩, rfl⟩
  have hal : IsAlgebraic 𝔐.Ω₀ a := by
    haveI : CharZero 𝔐.Ω₀ := charZero_of_injective_ringHom cst₀.injective
    exact ha.extendScalars (RingHom.injective_int _)
  obtain ⟨a₀, rfl⟩ := mem_range_of_isAlgebraic x hind ht a hal
  have ha₀ : IsAlgebraic ℤ a₀ :=
    (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom ℤ 𝔐.Ω₀ Ω) (algebraMap 𝔐.Ω₀ Ω).injective).1 ha
  obtain ⟨k, rfl⟩ := hS 𝔐.Ω₀ 𝔐.ξ₀ cst₀ 𝔐.gen₀ h2 a₀ ha₀
  exact ⟨k, (RingHom.congr_fun h1 k).symm⟩

end GlobalTheory.CompanionTheory.Ar.FlagConst
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicConstantsInRangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_constants_in_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag), SplitComps Y → Fl.deg = 1 → ∀ a : Ω, IsAlgebraic ℤ a → a ∈ 𝔐.cst.range := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagConst.isAlgebraic_mem_cst_range | exact GlobalTheory.CompanionTheory.Ar.FlagConst.isAlgebraic_mem_cst_range | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagConst.isAlgebraic_mem_cst_range <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EffectiveScaledWeightOfRetraction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RefRoot

section Step

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem Iic_pred {N : ℕ} (i : Fin N) (hi : 0 < (i : ℕ)) :
    Finset.Iic i = insert i (Finset.Iic (⟨(i : ℕ) - 1, by omega⟩ : Fin N)) := by
  ext k
  simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_def, Fin.ext_iff]
  omega

theorem Iic_zero {N : ℕ} (i : Fin N) (hi : (i : ℕ) = 0) : Finset.Iic i = {i} := by
  ext k
  simp only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_def, Fin.ext_iff]
  omega

theorem not_mem_Iic_pred {N : ℕ} (i : Fin N) (hi : 0 < (i : ℕ)) :
    i ∉ Finset.Iic (⟨(i : ℕ) - 1, by omega⟩ : Fin N) := by
  simp only [Finset.mem_Iic, Fin.le_def]
  omega

theorem sum_Iic_step {N : ℕ} {M : Type} [AddCommGroup M] (f g : Fin N → M)
    (h0 : ∀ i : Fin N, (i : ℕ) = 0 → g i = - f i)
    (hs : ∀ (i : Fin N) (hi : 0 < (i : ℕ)), g i = f ⟨(i : ℕ) - 1, by omega⟩ - f i) :
    ∀ i : Fin N, ∑ k ∈ Finset.Iic i, g k = - f i := by
  intro i
  obtain ⟨n, hn⟩ := i
  induction n with
  | zero => rw [Iic_zero _ rfl, Finset.sum_singleton]; exact h0 _ rfl
  | succ n ih =>
    have hi : 0 < ((⟨n + 1, hn⟩ : Fin N) : ℕ) := Nat.succ_pos n
    have h1 : g ⟨n + 1, hn⟩ = f ⟨n, by omega⟩ - f ⟨n + 1, hn⟩ := hs _ hi
    have h2 : ∑ k ∈ Finset.Iic (⟨(⟨n + 1, hn⟩ : Fin N) - 1, by simp; omega⟩ : Fin N), g k = - f ⟨n, by omega⟩ :=
      ih (by omega)
    rw [Iic_pred _ hi, Finset.sum_insert (not_mem_Iic_pred _ hi), h1, h2]
    abel

def prevLine {G : RefGeo Y} (A : G.An) (t : ℝ) (r : RootIx D) : HermLine G.J :=
  if h : (r.2 : ℕ) = 0 then Top.trivLine G.J
  else A.Re.line (some (r.1, ⟨(r.2 : ℕ) - 1, by have := r.2.2; omega⟩)) t

def stepLine {G : RefGeo Y} (A : G.An) (t : ℝ) (r : RootIx D) : HermLine G.J :=
  PB.combLine ![prevLine A t r, A.Re.line (some r) t] ![1, -1]

theorem stepLine_h {G : RefGeo Y} (A : G.An) (t : ℝ) (r : RootIx D) (z : (Σ k, G.J k) → ℂ) :
    (stepLine A t r).h z = (prevLine A t r).h z / (A.Re.line (some r) t).h z := by
  simp [stepLine, PB.combLine_h, Fin.prod_univ_two, div_eq_mul_inv]

theorem stepLine_a {G : RefGeo Y} (A : G.An) (t : ℝ) (r : RootIx D) :
    (stepLine A t r).a = G.xdeg r := by
  funext b
  obtain ⟨τ, i⟩ := r
  have hl : ∀ i' : Fin (D.p + D.q), (A.Re.line (some (τ, i')) t).a b = -∑ k ∈ Finset.Iic i', G.xdeg (τ, k) b := by
    intro i'
    rw [A.Re.line_deg, A.fund_deg]
    simp [Finset.sum_apply]
  simp only [stepLine, PB.combLine_a, Fin.sum_univ_two]
  by_cases h : (i : ℕ) = 0
  · simp only [prevLine, dif_pos h]
    simp [Top.trivLine, hl, Iic_zero i h]
  · have hi : 0 < (i : ℕ) := Nat.pos_of_ne_zero h
    simp only [prevLine, dif_neg h]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hl]
    rw [Iic_pred i hi, Finset.sum_insert (not_mem_Iic_pred i hi)]
    simp

theorem stepLine_smooth {G : RefGeo Y} (A : G.An) (t : ℝ) (r : RootIx D) : IsSmoothHerm (stepLine A t r) := by
  have hp : IsSmoothHerm (prevLine A t r) := by
    unfold prevLine
    split_ifs with h
    · exact contDiffOn_const
    · exact (A.conj _ t).1
  have hl := (A.conj (some r) t).1
  have e : (stepLine A t r).h = fun z => (prevLine A t r).h z / (A.Re.line (some r) t).h z :=
    funext (stepLine_h A t r)
  show ContDiffOn _ _ (stepLine A t r).h _
  rw [e]
  exact ContDiffOn.div hp hl fun z hz => ((A.Re.line (some r) t).pos z hz).ne'

theorem stepLine_conj {G : RefGeo Y} (A : G.An) (t : ℝ) (r : RootIx D) : IsConjInvariantH (stepLine A t r) := by
  have hp : IsConjInvariantH (prevLine A t r) := by
    unfold prevLine
    split_ifs with h
    · intro z; rfl
    · exact (A.conj _ t).2
  intro z
  rw [stepLine_h, stepLine_h, hp z, (A.conj (some r) t).2 z]

theorem log_line_eq {G : RefGeo Y} (A : G.An) (t : ℝ) (τ : CMType H) (i : Fin (D.p + D.q))
    (z : (Σ k, G.J k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log ((A.Re.line (some (τ, i)) t).h z) =
      -∑ k ∈ Finset.Iic i, Real.log ((stepLine A t (τ, k)).h z) := by
  have := sum_Iic_step (fun i' : Fin (D.p + D.q) => Real.log ((A.Re.line (some (τ, i')) t).h z))
    (fun k => Real.log ((stepLine A t (τ, k)).h z)) (fun k hk => by
      simp only [stepLine_h, prevLine, dif_pos hk, Top.trivLine]
      rw [Real.log_div one_ne_zero ((A.Re.line _ t).pos z hz).ne']
      simp) (fun k hk => by
      simp only [stepLine_h, prevLine, dif_neg hk.ne']
      rw [Real.log_div ((A.Re.line _ t).pos z hz).ne' ((A.Re.line _ t).pos z hz).ne']) i
  rw [this, neg_neg]

end Step

section Build

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

@[reducible] def refModel {G : RefGeo Y} (A : G.An) (hb : Birational G.y) (k : ℕ) (hk : 0 < k) (δ : ℕ) (hδ : 0 < δ) :
    Top.RootModel (CMType H) (D.p + D.q) where
  K := G.K
  «ι» := G.J
  Ω := G.Ω
  y := G.y
  arith := A.Re.arith
  birational := hb
  xdeg := G.xdeg
  x t r := stepLine A t r
  x_deg t r := stepLine_a A t r
  x_smooth t r := stepLine_smooth A t r
  x_conj t r := stepLine_conj A t r
  kA := k
  kA_pos := hk
  A := A.Re.ref none
  A_smooth := A.Re.ref_smooth none
  A_conj := fun z => by
    rw [A.none_h, A.none_h]
    simp only [RCLike.norm_conj]
  δ := δ
  δ_pos := hδ

@[reducible] def refFixed {G : RefGeo Y} (A : G.An) (Mf : LieModel Y.t.G (G.𝔐.ξ ≫ G.𝔐.f) G.𝔐.Li) (m : ℕ)
    (ix : Fin (m + 1) ≃ G.J G.k₀)
    (gen : Subfield.closure (Set.range fun ij : Fin (m + 1) × Fin (m + 1) =>
      G.y ⟨G.k₀, ix ij.1⟩ / G.y ⟨G.k₀, ix ij.2⟩) = ⊤)
    (pt : A.Sys.X → Fin (m + 1) → ℂ) (pt_ne : ∀ x, pt x ≠ 0) (pt_inj : ∀ x x' (a : ℂ), pt x = a • pt x' → x = x')
    (k q' : ℕ) (hq : 0 < q') (n : RootIx D → ℤ) (s : G.Ω) (hs : s ≠ 0) : FixedData Y A.Sys where
  Ωf := G.Ω
  ξf := G.𝔐.ξ ≫ G.𝔐.f
  Lif := G.𝔐.Li
  Mf := Mf
  bf := G.Fl.b
  m := m
  yf i := G.y ⟨G.k₀, ix i⟩
  generate := gen
  hf u := Real.sqrt (∑ i, ‖u i‖ ^ 2)
  kA := k
  pt := pt
  pt_ne := pt_ne
  pt_inj := pt_inj
  pos := A.pos
  ph_none := A.ph_none
  q' := q'
  q'_pos := hq
  n := n
  sE := s
  sE_ne := hs

theorem spMap_dualMap_id (R : Type) [CommRing R] : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
  have : dualMap (RingHom.id R) = RingHom.id _ := by
    ext a <;> simp [dualMap]
  rw [this]
  simp [spMap]

def refOrigin {G : RefGeo Y} (A : G.An) (hb : Birational G.y) (k : ℕ) (hk : 0 < k) (hδ : 0 < Module.finrank ℚ c.F * G.Fl.deg)
    (Mf : LieModel Y.t.G (G.𝔐.ξ ≫ G.𝔐.f) G.𝔐.Li)
    (hMf : ∀ e, (Mf.pt e).left = (G.𝔐.M.pt e).left ≫ G.𝔐.m.φ) (m : ℕ)
    (ix : Fin (m + 1) ≃ G.J G.k₀)
    (gen : Subfield.closure (Set.range fun ij : Fin (m + 1) × Fin (m + 1) =>
      G.y ⟨G.k₀, ix ij.1⟩ / G.y ⟨G.k₀, ix ij.2⟩) = ⊤)
    (pt : A.Sys.X → Fin (m + 1) → ℂ) (pt_ne : ∀ x, pt x ≠ 0) (pt_inj : ∀ x x' (a : ℂ), pt x = a • pt x' → x = x')
    (hpt : ∀ x, ∃ a : ℂ, (fun i => A.Re.R.lift x x ⟨G.k₀, ix i⟩) = a • pt (A.Re.π x))
    (q' : ℕ) (hq : 0 < q') (n : RootIx D → ℤ) (s : G.Ω) (hs : s ≠ 0)
    (hconst : ∀ a : G.Ω, IsAlgebraic ℤ a → a ∈ G.𝔐.cst.range) (heff : G.IsEff n q' s) :
    RootOrigin Y ∅ (refModel A hb k hk _ hδ) (refFixed A Mf m ix gen pt pt_ne pt_inj k q' hq n s hs) where
  𝔐 := G.𝔐
  Fl := G.Fl
  g := RingHom.id G.Ω
  g_over := by
    show G.𝔐.ξ ≫ G.𝔐.f = spMap (RingHom.id G.Ω) ≫ G.𝔐.ξ ≫ G.𝔐.f
    simp [spMap]
  g_flag s i := by
    show (G.𝔐.M.pt (G.Fl.b s i)).left ≫ G.𝔐.m.φ = spMap (dualMap (RingHom.id G.Ω)) ≫ (Mf.pt (G.Fl.b s i)).left
    rw [spMap_dualMap_id, hMf]
    exact (Category.id_comp _).symm
  g_deg := (Module.finrank_self G.Ω).trans G.deg_one.symm
  g_const a ha := hconst a ha
  δ_eq := rfl
  e := G.e
  lines := G.lines
  sing := A.sing
  sing_deg := A.sing_deg
  hodge := A.hodge
  k₀ := G.k₀
  ix := ix
  y_eq i := rfl
  kA_eq := rfl
  A_deg := A.none_deg
  A_h z hz := by
    show (A.Re.ref none).h z = Real.sqrt (∑ i, ‖z ⟨G.k₀, ix i⟩‖ ^ 2)
    rw [A.none_h]
    congr 1
    exact (Equiv.sum_comp ix fun i => ‖z ⟨G.k₀, i⟩‖ ^ 2).symm
  eff p hp i t hi ht := heff p hp (ix i) t
    ⟨hi.1, fun c' => by simpa using hi.2 (ix.symm c')⟩ ht
  Re := A.Re
  Re_deg := A.deg_one.trans G.deg_one.symm
  π_pt := hpt
  interior := A.interior
  fund_deg := A.fund_deg
  fund_sing := A.fund_sing
  fund_reg τ i t h0 h1 z hz := log_line_eq A t τ i z hz.1
  ref_none := ⟨rfl, fun _ _ => rfl⟩

end Build

section Gen

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

def genCpt (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩

theorem mem_regAt_genCpt (h : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ (genCpt ξ) := by
  obtain ⟨s, rfl⟩ := h.bij.2 a
  refine ⟨s, ?_⟩
  simp only [genMap, genCpt, TopCat.Presheaf.stalkSpecializes_refl]
  exact congrArg (fun f : X.presheaf.stalk (genPt ξ) ⟶ _ => f.hom s) (Category.id_comp (Scheme.stalkClosedPointTo ξ))

theorem EmbedsGeneric.exists_closure {κ : Type} {x : κ → Ω} (h : IsCptGen ξ) (he : EmbedsGeneric ξ x) :
    Nonempty κ ∧ Subfield.closure (Set.range fun ij : κ × κ => x ij.1 / x ij.2) = ⊤ := by
  have hc : ∀ r : ℕ, r.Prime → ¬ InFibre ξ r (genCpt ξ) := fun r hr hf =>
    hf ⟨Nat.cast_ne_zero.2 hr.ne_zero, mem_regAt_genCpt h _, mem_regAt_genCpt h _⟩
  obtain ⟨⟨i, hi⟩, h2⟩ := he (genCpt ξ) hc
  refine ⟨⟨i⟩, ?_⟩
  rw [eq_top_iff]
  intro a _
  obtain ⟨s, hs, hu, hsa⟩ := (h2 i hi).1 a (mem_regAt_genCpt h a)
  have hle : ∀ b ∈ Algebra.adjoin ℚ (Set.range fun j => x j / x i),
      b ∈ Subfield.closure (Set.range fun ij : κ × κ => x ij.1 / x ij.2) := by
    intro b hb
    induction hb using Algebra.adjoin_induction with
    | mem b hb =>
      obtain ⟨j, rfl⟩ := hb
      exact Subfield.subset_closure ⟨(j, i), rfl⟩
    | algebraMap r =>
      rw [eq_ratCast]
      exact SubfieldClass.ratCast_mem _ r
    | add _ _ _ _ h1 h2 => exact add_mem h1 h2
    | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2
  have e : a = s * a / s := by rw [mul_div_cancel_left₀ _ hu.1]
  rw [e]
  exact div_mem (hle _ hsa) (hle _ hs)

end Gen

section Main

theorem genPt_comp_spMap {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] (i : Ω →+* Ω')
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) : genPt (spMap i ≫ ξ) = genPt ξ := by
  have h : ∀ P : Sp Ω', (spMap i ≫ ξ) P = ξ (spMap i P) := fun P => by simp
  exact (h _).trans (congrArg ξ (@Subsingleton.elim (PrimeSpectrum Ω) _ _ _))

theorem holoOn_comp {e e' : ℕ} {M M' : Type} [TopologicalSpace M] [TopologicalSpace M']
    {A : ReciprocityTheory.AnForm.M.FinHolAtlas e M} {B : ReciprocityTheory.AnForm.M.FinHolAtlas e' M'} {h : M' → M}
    (hh : ReciprocityTheory.AnForm.M.HoloMap B A h) {V : Set M} {g : M → ℂ} (hg : A.HoloOn V g) :
    B.HoloOn (h ⁻¹' V) (g ∘ h) := by
  intro j z hz
  obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm z))
  have h1 := hh.2 j k z ⟨hz.1, hk⟩
  have h2 := hg k ((A.chart k) (h ((B.chart j).symm z)))
    ⟨(A.chart k).map_source hk, by
      simpa [(A.chart k).left_inv hk] using hz.2⟩
  have h3 := h2.comp_of_eq h1 rfl
  refine h3.congr ?_
  have hc : ContinuousAt (h ∘ (B.chart j).symm) z :=
    hh.1.continuousAt.comp ((B.chart j).continuousAt_symm hz.1)
  filter_upwards [hc.preimage_mem_nhds ((A.chart k).open_source.mem_nhds hk)] with w hw
  exact congrArg g ((A.chart k).left_inv hw)

end Main

theorem refRoot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (G : RefGeo Y) (A : G.An) (ν : RootIx D → ℤ) (k q' : ℕ) (s : G.Ω), (∃ inv : A.Sys.X → A.Re.R.X, ReciprocityTheory.AnForm.M.HoloMap A.Sys.A A.Re.R.A inv ∧ ∀ x, inv (A.Re.π x) = x) → SplitComps Y → 0 < k → 0 < q' → s ≠ 0 → G.IsEff (fun r => (k * q' : ℕ) * ν r) q' s → ∃ (Fx : FixedData Y A.Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y ∅ R Fx), genPt Fx.ξf = genPt G.𝔐.ξ₀ ∧ Fx.kA = k ∧ Fx.q' = q' ∧ (∀ r, Fx.n r = (k * q' : ℕ) * ν r) ∧ o.Fl.deg = 1 ∧ o.Re.J = ⊤ ∧ Ht.AmpleQ R.y R.A.a ∧ Cmp.IsEmbedded o.Re.R.A R.P o.Re.R.U o.Re.R.lift ∧ Function.Bijective o.Re.π ∧ (∀ x : A.Sys.X, ∃ (U : Set A.Sys.X) (lam : A.Sys.X → Fin (Fx.m + 1) → ℂ), IsOpen U ∧ x ∈ U ∧ (∀ i, A.Sys.A.HoloOn U fun y => lam y i) ∧ (∀ y ∈ U, ∃ a₀ : ℂ, a₀ ≠ 0 ∧ lam y = a₀ • Fx.pt y) ∧ ∀ p, lam x p ≠ 0 → ∀ j, x ∈ (A.Sys.A.chart j).source → (fderiv ℂ (fun z i => lam ((A.Sys.A.chart j).symm z) i / lam ((A.Sys.A.chart j).symm z) p) (A.Sys.A.chart j x)).ker = ⊥) := by
  intro E _ _ _ H D l Xo c Y G A ν k q' s ⟨inv, hinvH, hinv⟩ hsplit hk hq hs heff
  classical
  obtain ⟨hne, hclos⟩ := EmbedsGeneric.exists_closure (x := fun i : G.J G.k₀ => G.y ⟨G.k₀, i⟩) G.𝔐.tie.gen G.embeds
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card (G.J G.k₀) = m + 1 :=
    ⟨Fintype.card (G.J G.k₀) - 1, by have := Fintype.card_pos (α := G.J G.k₀); omega⟩
  let ix : Fin (m + 1) ≃ G.J G.k₀ := (Fintype.equivFinOfCardEq hm).symm
  have gen : Subfield.closure (Set.range fun ij : Fin (m + 1) × Fin (m + 1) =>
      G.y ⟨G.k₀, ix ij.1⟩ / G.y ⟨G.k₀, ix ij.2⟩) = ⊤ := by
    rw [← hclos]
    congr 1
    ext a
    constructor
    · rintro ⟨ij, rfl⟩
      exact ⟨(ix ij.1, ix ij.2), rfl⟩
    · rintro ⟨ij, rfl⟩
      exact ⟨(ix.symm ij.1, ix.symm ij.2), by simp⟩
  obtain ⟨Mf, hMf⟩ := GlobalTheory.T.lie_model_push_along_map E H _ _ G.𝔐.t Y.t G.𝔐.f G.𝔐.m G.Ω G.𝔐.ξ G.𝔐.Li G.𝔐.M
  haveI : Nonempty G.K := ⟨G.k₀⟩
  have hb : Birational G.y := (GlobalTheory.T.hodge_cpt_birational_arith_var E H D l Xo c (𝓞 c.F) (algebraMap _ _) Y ∅ G.Ω G.K G.J G.y G.𝔐 G.Fl
    (RingOfIntegers.coe_injective)).1
  have hδ : 0 < Module.finrank ℚ c.F * G.Fl.deg := by
    rw [G.deg_one, _root_.mul_one]
    haveI := c.fin
    exact Module.finrank_pos
  have hcov : ∀ x : A.Sys.X, A.Re.π (inv x) = x := fun x => by
    obtain ⟨u, rfl⟩ := A.π_bij.2 x
    rw [hinv]
  let pt : A.Sys.X → Fin (m + 1) → ℂ := fun x i => A.Re.R.lift (inv x) (inv x) ⟨G.k₀, ix i⟩
  have hmem : ∀ x, A.Re.R.lift x x ∈ mcPts (mCoordIdeal G.y) := fun x =>
    A.embedded.mem x x (A.embedded.mem_U x)
  have pt_ne : ∀ x, pt x ≠ 0 := fun x h => by
    obtain ⟨i, hi⟩ := (hmem (inv x)).1 G.k₀
    exact hi (by simpa [pt] using congrFun h (ix.symm i))
  have pt_inj : ∀ x x' (a : ℂ), pt x = a • pt x' → x = x' := fun x x' a h => by
    have ho := GlobalTheory.T.same_orbit_of_proportional_coords G.𝔐.X G.Ω G.𝔐.ξ G.K G.J G.y G.k₀ G.𝔐.tie G.embeds _ (hmem (inv x)) _ (hmem (inv x')) a
      (fun i => by simpa [pt] using congrFun h (ix.symm i))
    have := A.embedded.inj _ _ ho
    rw [← hcov x, this, hcov]
  have hpt : ∀ x, ∃ a : ℂ, (fun i => A.Re.R.lift x x ⟨G.k₀, ix i⟩) = a • pt (A.Re.π x) := fun x =>
    ⟨1, by simp [pt, hinv]⟩
  have hconst := GlobalTheory.T.algebraic_constants_in_range E H D l Xo c Y ∅ G.Ω G.K G.J G.y G.𝔐 G.Fl hsplit G.deg_one
  refine ⟨refFixed A Mf m ix gen pt pt_ne pt_inj k q' hq (fun r => (k * q' : ℕ) * ν r) s hs,
    refModel A hb k hk _ hδ,
    refOrigin A hb k hk hδ Mf hMf m ix gen pt pt_ne pt_inj hpt q' hq _ s hs hconst heff,
    ?_, rfl, rfl, fun _ => rfl, G.deg_one, A.J_top, ?_, A.embedded, A.π_bij, ?_⟩
  · show genPt (G.𝔐.ξ ≫ G.𝔐.f) = _
    have e : G.𝔐.ξ ≫ G.𝔐.f = spMap G.𝔐.fn ≫ G.𝔐.ξ₀ := G.𝔐.fn_over
    rw [e]
    exact genPt_comp_spMap _ _
  · exact GlobalTheory.T.ample_of_single_coord_block G.𝔐.X G.Ω G.𝔐.ξ G.K G.J G.y G.k₀ _ G.𝔐.tie G.embeds A.none_deg.1 A.none_deg.2
  · intro x
    have hx₁ := A.Re.R.mem_U (inv x)
    refine ⟨inv ⁻¹' A.Re.R.U (inv x), fun y i => A.Re.R.lift (inv x) (inv y) ⟨G.k₀, ix i⟩,
      (A.Re.R.isOpen_U _).preimage hinvH.1, hx₁, fun i => holoOn_comp hinvH (A.Re.R.holo (inv x) _), ?_, ?_⟩
    · intro y hy
      obtain ⟨c', hc', e⟩ := A.embedded.compat (inv x) (inv y) (inv y) ⟨hy, A.Re.R.mem_U _⟩
      exact ⟨c' G.k₀, hc' _, funext fun i => congrFun e ⟨G.k₀, ix i⟩⟩
    · intro p hp j hj
      obtain ⟨j₁, hj₁⟩ := A.Re.R.A.cover (inv x)
      obtain ⟨h1, h2⟩ := GlobalTheory.T.holomorphic_atlas_coord_compat G.𝔐.X G.Ω G.𝔐.ξ G.K G.J G.y G.k₀ G.𝔐.tie G.embeds _ _ A.Re.R.A _ _ A.embedded
        (Fin (m + 1)) ix (inv x) p hp j₁ hj₁
      exact GlobalTheory.T.holomorphic_inverse_chart_value _ _ _ _ A.Re.R.A A.Sys.A A.Re.π inv A.Re.holo hinvH A.π_bij hinv
        (fun y i => A.Re.R.lift (inv x) y ⟨G.k₀, ix i⟩ / A.Re.R.lift (inv x) y ⟨G.k₀, ix p⟩) x j₁ j hj₁ hj h1 h2

end GlobalTheory.CompanionTheory.Ar.RefRoot
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EffectiveScaledWeightOfRetractionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.effective_scaled_weight_of_retraction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (G : RefGeo Y) (A : G.An) (ν : RootIx D → ℤ) (k q' : ℕ) (s : G.Ω), (∃ inv : A.Sys.X → A.Re.R.X, ReciprocityTheory.AnForm.M.HoloMap A.Sys.A A.Re.R.A inv ∧ ∀ x, inv (A.Re.π x) = x) → SplitComps Y → 0 < k → 0 < q' → s ≠ 0 → G.IsEff (fun r => (k * q' : ℕ) * ν r) q' s → ∃ (Fx : FixedData Y A.Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y ∅ R Fx), genPt Fx.ξf = genPt G.𝔐.ξ₀ ∧ Fx.kA = k ∧ Fx.q' = q' ∧ (∀ r, Fx.n r = (k * q' : ℕ) * ν r) ∧ o.Fl.deg = 1 ∧ o.Re.J = ⊤ ∧ Ht.AmpleQ R.y R.A.a ∧ Cmp.IsEmbedded o.Re.R.A R.P o.Re.R.U o.Re.R.lift ∧ Function.Bijective o.Re.π ∧ (∀ x : A.Sys.X, ∃ (U : Set A.Sys.X) (lam : A.Sys.X → Fin (Fx.m + 1) → ℂ), IsOpen U ∧ x ∈ U ∧ (∀ i, A.Sys.A.HoloOn U fun y => lam y i) ∧ (∀ y ∈ U, ∃ a₀ : ℂ, a₀ ≠ 0 ∧ lam y = a₀ • Fx.pt y) ∧ ∀ p, lam x p ≠ 0 → ∀ j, x ∈ (A.Sys.A.chart j).source → (fderiv ℂ (fun z i => lam ((A.Sys.A.chart j).symm z) i / lam ((A.Sys.A.chart j).symm z) p) (A.Sys.A.chart j x)).ker = ⊥) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RefRoot.refRoot | exact GlobalTheory.CompanionTheory.Ar.RefRoot.refRoot | (intros; apply GlobalTheory.CompanionTheory.Ar.RefRoot.refRoot <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TopTower

theorem comp_data (hG : Top.Given) (hA0 : Flat.FlatLineGenerator) (hA1 : Flat.FlatLineGeneratorComponent)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l)
    (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
    (hgl : Top.IsGlobal Xo l c Y) (hsp : SplitComps Y) (hp : 1 ≤ D.p) (hq : 1 ≤ D.q)
    (x : Y.X) (hx : ∀ x' : Y.X, x' ⤳ x → x' = x) :
    ∃ (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys)
      (R : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y ∅ R Fx),
      genPt Fx.ξf = x ∧
      (∀ r : RootIx D, (Fx.n r : ℝ) = ((Fx.kA * Fx.q' : ℕ) : ℝ) * (-((r.2 : ℕ) : ℝ))) ∧
      o.Fl.deg = 1 ∧ o.Re.J = ⊤ ∧ Ht.AmpleQ R.y R.A.a ∧
      Cmp.IsEmbedded o.Re.R.A R.P o.Re.R.U o.Re.R.lift ∧ Function.Bijective o.Re.π ∧
      (∀ τ (i : Fin (D.p + D.q)), (i : ℕ) + 1 = D.p + D.q → ∀ t,
        ReciprocityTheory.AnForm.M.IsPsh Sys.A ((Sys.potT (some (τ, i)) t).rsmul (-1)) ∧
          ReciprocityTheory.AnForm.M.IsPsh Sys.A (Sys.potT (some (τ, i)) t)) ∧
      (∀ x : Sys.X, ∃ (U : Set Sys.X) (lam : Sys.X → Fin (Fx.m + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
        (∀ i, Sys.A.HoloOn U fun y => lam y i) ∧ (∀ y ∈ U, ∃ a₀ : ℂ, a₀ ≠ 0 ∧ lam y = a₀ • Fx.pt y) ∧
        ∀ p, lam x p ≠ 0 → ∀ j, x ∈ (Sys.A.chart j).source →
          (fderiv ℂ (fun z i => lam ((Sys.A.chart j).symm z) i / lam ((Sys.A.chart j).symm z) p)
            (Sys.A.chart j x)).ker = ⊥) := by
  have hdom : ∀ x, IsDomain (Y.X.presheaf.stalk x) := fun x => (Y.normal x).1
  have hcg := GlobalTheory.T.isCptGen_residue_field_generic Y.X hdom x hx
  obtain ⟨G, hG0⟩ := GlobalTheory.T.exists_reference_geometry_same_generic hG.2.2.2.2.1 E H D l (Xo l) c Y _ (Y.X.fromSpecResidueField x) hcg
  obtain ⟨A, hinv⟩ := GlobalTheory.T.exists_holomorphic_section_of_analytic hG hA0 hA1 E H D Xo l c Y hgl hsp hp hq G
  let ν : RootIx D → ℤ := fun r => -((r.2 : ℕ) : ℤ)
  have hν : ∀ τ (i k : Fin (D.p + D.q)), i < k → ν (τ, k) < ν (τ, i) := by
    intro τ i k hik
    simp only [ν, neg_lt_neg_iff]
    exact_mod_cast hik
  obtain ⟨k, q', s, hk, hq', hs, heff⟩ := GlobalTheory.T.exists_effective_weight_section hG E H D Xo l c Y hgl hp hq G ⟨A⟩ ν hν
  obtain ⟨Fx, R, o, hgen, hkA, hq'', hn, hdeg, hJ, hamp, hemb, hbij, hlam⟩ :=
    GlobalTheory.T.effective_scaled_weight_of_retraction E H D l (Xo l) c Y G A ν k q' s hinv hsp hk hq' hs heff
  refine ⟨A.Sys, Fx, R, o, ?_, ?_, hdeg, hJ, hamp, hemb, hbij, A.flat, hlam⟩
  · rw [hgen, hG0]
    exact Scheme.fromSpecResidueField_apply x _
  · intro r
    rw [hn r, hkA, hq'']
    simp [ν]

theorem level_data (hG : Top.Given) (hW : Out.WeilSt)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
    {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} (Fx : FixedData Y Sys)
    (R : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y ∅ R Fx)
    (hdeg : o.Fl.deg = 1) (hemb : Cmp.IsEmbedded o.Re.R.A R.P o.Re.R.U o.Re.R.lift)
    (hbij : Function.Bijective o.Re.π)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) :
    ∃ (RM : Top.RootModel (CMType H) (D.p + D.q)) (o' : RootOrigin Y S RM Fx), o'.𝔐.OmVB ∧
      (∀ p ∈ S, o'.𝔐.R p = 4) ∧ o'.Re.J = ⊤ ∧ ∃ _ : Algebra ℚ RM.Ω, SmoothGenericFibreM RM.y := by
  obtain ⟨Ω, _, _, K, _, J, _, y, bk, bx, i, 𝔐, h, Fl, xdeg, e, hbk, hy, hd, hf, hcst, hfl, hfin, hlines,
    hom, hsm, hR⟩ := GlobalTheory.T.root_origin_good_primes_finite hG hW E H D l Xo c Y Sys Fx R o S hS hdisc hdeg
  obtain ⟨RM, o', h1, h2, h3, h4⟩ := GlobalTheory.T.root_origin_coords_over_field hG E H D l Xo c Y Sys Fx R o S Ω K J y bk bx i 𝔐 h Fl
    xdeg e hdeg hemb hbij hbk hy hd hf hcst hfl hfin hlines hom hsm
  refine ⟨RM, o', h1, fun p hp => ?_, h3, h4⟩
  rw [h2]
  exact hR p hp

theorem exists_good_tower : Top.Given → Out.WeilSt → Flat.FlatLineGenerator → Flat.FlatLineGeneratorComponent → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)], Top.IsGlobal Xo l c Y → SplitComps Y → 1 ≤ D.p → 1 ≤ D.q → ∃ (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T), (∀ a, (∀ x : (o.Sys a).X, ∃ (U : Set (o.Sys a).X) (lam : (o.Sys a).X → Fin ((o.Fx a).m + 1) → ℂ), IsOpen U ∧ x ∈ U ∧ (∀ i, (o.Sys a).A.HoloOn U fun y => lam y i) ∧ (∀ y ∈ U, ∃ a₀ : ℂ, a₀ ≠ 0 ∧ lam y = a₀ • (o.Fx a).pt y) ∧ ∀ p, lam x p ≠ 0 → ∀ j, x ∈ ((o.Sys a).A.chart j).source → (fderiv ℂ (fun z i => lam (((o.Sys a).A.chart j).symm z) i / lam (((o.Sys a).A.chart j).symm z) p) ((o.Sys a).A.chart j x)).ker = ⊥)) ∧ ∀ B a, ∀ p ∈ o.S B, (o.Or B a).𝔐.R p = 4 := by
  intro hG hW hA0 hA1 E _ _ _ H D Xo l c Y _ hgl hsp hp hq
  obtain ⟨hfin, hne⟩ := GlobalTheory.T.generic_points_finite_nonempty hG E H D l (Xo l) c Y
  let Smax : Set Y.X := {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}
  haveI : Fintype Smax := Set.Finite.fintype hfin
  haveI : Nonempty Smax := hne.to_subtype
  choose Sys Fx R o hgen hnu hdeg hJ hamp hemb hbij hflat hlam using
    fun a : Smax => comp_data hG hA0 hA1 Xo l c Y hgl hsp hp hq a.1 a.2
  have hM' : l.M' ≠ 0 := by
    show Nat.lcm l.M l.A ≠ 0
    exact Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  have hn0 : 2 * (discr E).natAbs * l.M' ≠ 0 := by
    exact Nat.mul_ne_zero (Nat.mul_ne_zero two_ne_zero (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero E))) hM'
  let bad : Finset ℕ := (2 * (discr E).natAbs * l.M').primeFactors
  have hbad : ∀ r : ℕ, r ∈ bad ↔ r.Prime ∧ (r : ℤ) ∣ 2 * discr E * l.M' := by
    intro r
    simp only [bad, Nat.mem_primeFactors, Int.natCast_dvd, Int.natAbs_mul]
    simp [hn0]
  let SB : ℕ → Finset ℕ := fun B => (Finset.range (B + 1)).filter Nat.Prime ∪ bad
  have hSB : ∀ B r, r ∈ SB B ↔ r.Prime ∧ (r ≤ B ∨ r ∈ bad) := by
    intro B r
    simp only [SB, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro (⟨h1, h2⟩ | h)
      · exact ⟨h2, Or.inl (by omega)⟩
      · exact ⟨((hbad r).1 h).1, Or.inr h⟩
    · rintro ⟨h1, h2 | h2⟩
      · exact Or.inl ⟨by omega, h1⟩
      · exact Or.inr h2
  have hSBp : ∀ B, ∀ p ∈ SB B, p.Prime := fun B p hp => ((hSB B p).1 hp).1
  have hSBd : ∀ B, ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ SB B := by
    intro B p hp hd
    refine (hSB B p).2 ⟨hp, Or.inr ((hbad p).2 ⟨hp, ?_⟩)⟩
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hd 2) _
  choose RM o' hom hR hJ' hsm using fun (B : ℕ) (a : Smax) =>
    level_data hG hW Y (Fx a) (R a) (o a) (hdeg a) (hemb a) (hbij a) (SB B) (hSBp B) (hSBd B)
  let T : Top.RootTower (CMType H) (D.p + D.q) :=
    { j := D.p
      j_pos := hp
      j_lt := by omega
      Comp := Smax
      bad := bad
      two_mem := (hbad 2).2 ⟨Nat.prime_two, Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl _) _) _⟩
      nu := fun _ i => -((i : ℕ) : ℝ)
      nu_rat := fun _ i => ⟨-((i : ℕ) : ℚ), by push_cast; rfl⟩
      M := RM }
  let tor : TowerOrigin Y T :=
    { j_eq := rfl
      bad_iff := hbad
      S := SB
      S_iff := hSB
      Sys := Sys
      Fx := Fx
      comp_inj := fun a a' h => Subtype.ext (by rw [← hgen a, ← hgen a']; exact h)
      comp_onto := fun x hx => ⟨⟨x, hx⟩, hgen _⟩
      nu_eq := fun a r => hnu a r
      Or := o' }
  let go : Top.GoodOrigin Y T :=
    { toTowerOrigin := tor
      omVB := hom
      smooth := fun B a => ⟨hJ' B a, hsm B a⟩
      flat := hflat
      R := R
      refOr := o
      ref_deg := hdeg
      ref_top := hJ
      ample := hamp }
  exact ⟨T, go, fun a => hlam a, fun B a p hp => hR B a p hp⟩

end GlobalTheory.CompanionTheory.Ar.TopTower
