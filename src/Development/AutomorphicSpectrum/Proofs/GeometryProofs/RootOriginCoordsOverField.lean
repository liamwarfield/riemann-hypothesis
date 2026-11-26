module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothFunctionAsDegreeZeroMetric
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogResolutionReindexed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeLatticeComparison
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothGenericFibreOfSnc
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStableEigenTangents
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PolarizedDataFieldExtension

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugationInvariantHermitianMetric
section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.X_line_conj
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem PositivityTheory.Xgp.t_line_conj : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : HermLine ι), IsSmoothHerm A → ∃ B : HermLine ι, B.a = A.a ∧ IsSmoothHerm B ∧ IsConjInvariantH B ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → Real.log (B.h z) = (Real.log (A.h z) + Real.log (A.h fun p => starRingEnd ℂ (z p))) / 2 := by
  intro K _ ι _ A hA
  have hne : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      ∀ k, ∃ i, (fun p => starRingEnd ℂ (z p)) ⟨k, i⟩ ≠ 0 := by
    intro z hz k
    obtain ⟨i, hi⟩ := hz k
    exact ⟨i, by simpa using hi⟩
  refine ⟨⟨A.a, fun z => Real.sqrt (A.h z * A.h fun p => starRingEnd ℂ (z p)), ?_, ?_⟩, rfl, ?_, ?_, ?_⟩
  · intro z hz
    exact Real.sqrt_pos.2 (mul_pos (A.pos z hz) (A.pos _ (hne z hz)))
  · intro c z hc
    have h1 := A.smul (fun k => starRingEnd ℂ (c k)) (fun p => starRingEnd ℂ (z p)) (fun k => by simpa using hc k)
    simp only [RCLike.norm_conj] at h1
    simp only [map_mul]
    rw [h1, A.smul c z hc]
    have h0 : 0 ≤ ∏ k, ‖c k‖ ^ A.a k := Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _
    rw [mul_mul_mul_comm, Real.sqrt_mul (mul_nonneg h0 h0), Real.sqrt_mul_self h0]
  · have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => fun p => starRingEnd ℂ (z p)) := by
      refine contDiff_pi.2 fun p => ?_
      exact Complex.conjCLE.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) p)
    refine ContDiffOn.sqrt (ContDiffOn.mul hA (hA.comp hc.contDiffOn fun z hz => hne z hz)) ?_
    intro z hz
    exact (mul_pos (A.pos z hz) (A.pos _ (hne z hz))).ne'
  · intro z
    simp only [Complex.conj_conj, mul_comm]
  · intro z hz
    show Real.log (Real.sqrt _) = _
    rw [Real.log_sqrt (mul_pos (A.pos z hz) (A.pos _ (hne z hz))).le,
      Real.log_mul (A.pos z hz).ne' (A.pos _ (hne z hz)).ne']
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugationInvariantHermitianMetric
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem exists_conjInvariant_line_averaged : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : HermLine ι), IsSmoothHerm A → ∃ B : HermLine ι, B.a = A.a ∧ IsSmoothHerm B ∧ IsConjInvariantH B ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → Real.log (B.h z) = (Real.log (A.h z) + Real.log (A.h fun p => starRingEnd ℂ (z p))) / 2 :=
  @PositivityTheory.Xgp.t_line_conj

end GlobalTheory.CompanionTheory.Ar.PB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugationInvariantHermitianMetricStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugation_invariant_hermitian_metric : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : HermLine ι), IsSmoothHerm A → ∃ B : HermLine ι, B.a = A.a ∧ IsSmoothHerm B ∧ IsConjInvariantH B ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → Real.log (B.h z) = (Real.log (A.h z) + Real.log (A.h fun p => starRingEnd ℂ (z p))) / 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.exists_conjInvariant_line_averaged | exact GlobalTheory.CompanionTheory.Ar.PB.exists_conjInvariant_line_averaged | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.exists_conjInvariant_line_averaged <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentThird
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentThird
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg

theorem normPull_of_stalks : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (j : 𝔐₀.Li →+ 𝔐.Li), CharZero Ω → (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ (a : Ω₀) e, j (a • e) = i a • j e) → (∀ (n : ℕ) (b : Fin n → 𝔐₀.Li), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) → (∀ s a, j (Fl₀.b s a) = Fl.b s a) → (∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.V s (pushCpt hd q) : Set 𝔐₀.Li))) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐₀.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), 𝔐₀.M.GramAt 𝔐₀.t.PP.L (z ≫ h) b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z (fun k => j (b k)) Γ) → NormPull Fl₀ Fl i h := by
  intro E _ _ _ H D l Xo c O _ β Y S₀ S Ω₀ Ω _ _ K₀ K _ _ J₀ J _ _ y₀ y 𝔐₀ 𝔐 i h hd Fl₀ Fl j hc hreg hsl hli hfl hst hgr
    z s a t₀ ν hN
  obtain ⟨hh, b, Γ, hfs, hfr, hb, hG, hP, rfl⟩ := hN
  have hq : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  have hbase : Fl.b s = fun k => j (Fl₀.b s k) := funext fun k => (hfl s k).symm
  have hnf : ∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r ⟨centre z, hq⟩ := fun r hr => not_inFibre 𝔐.ξ z hq hr
  have hV := hst ⟨centre z, hq⟩ hnf s
  have hpush : (⟨centre (z ≫ h), hh⟩ : Cpt 𝔐₀.ξ) = pushCpt hd ⟨centre z, hq⟩ :=
    Subtype.ext (Scheme.Hom.comp_apply z h _)
  have hfr' : (𝔐₀.V s).IsFrameAt b (pushCpt hd ⟨centre z, hq⟩) := hpush ▸ hfr
  refine ⟨hq, fun k => j (b k), Γ, fun s' => ?_, ⟨hli _ b hfr.1, ?_⟩, ?_, hgr z _ b Γ hG, hP, rfl⟩
  · rw [hbase]
    exact FlagPull.flagStep_map_eq hsl hfs s'
  · rw [hV]
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨e, he, rfl⟩
      have he' : e ∈ 𝔐₀.V s (pushCpt hd ⟨centre z, hq⟩) := he
      rw [hfr'.2] at he'
      clear he
      show j e ∈ Submodule.span (regAt 𝔐.ξ ⟨centre z, hq⟩) (Set.range fun k => j (b k))
      induction he' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        exact Submodule.subset_span ⟨k, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul u x _ hx =>
        have e1 : j (u • x) = (⟨i u, hreg _ _ u.2⟩ : regAt 𝔐.ξ ⟨centre z, hq⟩) • j x := hsl (u : Ω₀) x
        rw [e1]
        exact Submodule.smul_mem _ _ hx
    · rintro _ ⟨k, rfl⟩
      refine Submodule.subset_span ⟨b k, ?_, rfl⟩
      show b k ∈ 𝔐₀.V s (pushCpt hd ⟨centre z, hq⟩)
      rw [hfr'.2]
      exact Submodule.subset_span ⟨k, rfl⟩
  · have hm := FlagPull.map_mem_flagStep hsl (Fl₀.b s) a hb
    rw [map_sub, hsl, hfl, ← hbase] at hm
    exact hm

end GlobalTheory.CompanionTheory.Ar.Chg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentThirdStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_descent_third : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (j : 𝔐₀.Li →+ 𝔐.Li), CharZero Ω → (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ (a : Ω₀) e, j (a • e) = i a • j e) → (∀ (n : ℕ) (b : Fin n → 𝔐₀.Li), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) → (∀ s a, j (Fl₀.b s a) = Fl.b s a) → (∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.V s (pushCpt hd q) : Set 𝔐₀.Li))) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐₀.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), 𝔐₀.M.GramAt 𝔐₀.t.PP.L (z ≫ h) b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z (fun k => j (b k)) Γ) → NormPull Fl₀ Fl i h := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.normPull_of_stalks | exact GlobalTheory.CompanionTheory.Ar.Chg.normPull_of_stalks | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.normPull_of_stalks <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PositiveHomogeneousPotential
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PositiveHomogeneousPotential
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg.FlatExt

open Filter Topology Set

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem isOpen_blockNz : IsOpen {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have e : {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [e]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem conj_mem_mcPts {P : Ideal (MRing J)} {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts P) :
    (fun p => starRingEnd ℂ (z p)) ∈ mcPts P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, by simpa using hi⟩
  · have h := hz.2 f hf
    rw [MvPolynomial.eval_map] at h ⊢
    have e := MvPolynomial.eval₂_comp_left (starRingEnd ℂ) (Int.castRingHom ℂ) z f
    rw [h, map_zero, Subsingleton.elim ((starRingEnd ℂ).comp (Int.castRingHom ℂ)) (Int.castRingHom ℂ)] at e
    exact e.symm

theorem continuousOn_of_holoOn {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {U : Set X}
    {g : X → ℂ} (h : A.HoloOn U g) : ContinuousOn g U := by
  intro y hy
  obtain ⟨j, hj⟩ := A.cover y
  have hc := (A.chart j).continuousAt hj
  have hsy : (A.chart j).symm (A.chart j y) = y := (A.chart j).left_inv hj
  have han : ContinuousAt (g ∘ (A.chart j).symm) (A.chart j y) :=
    (h j _ ⟨(A.chart j).map_source hj, by simpa [hsy] using hy⟩).continuousAt
  have hcomp : ContinuousAt ((g ∘ (A.chart j).symm) ∘ (A.chart j)) y := ContinuousAt.comp han hc
  refine (hcomp.congr ?_).continuousWithinAt
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with w hw
  simp [(A.chart j).left_inv hw]

theorem analyticAt_lift {P Jd : Ideal (MRing J)} {D : ℕ} (R : AnLogRes P Jd D) (x : R.X) (j : Fin R.A.n)
    {t : Fin D → ℂ} (ht : t ∈ (R.A.chart j).target) (hx : (R.A.chart j).symm t ∈ R.U x) :
    AnalyticAt ℂ (fun t' => R.lift x ((R.A.chart j).symm t')) t :=
  AnalyticAt.pi fun p => R.holo x p j t ⟨ht, hx⟩

theorem ratio_eq {P Jd : Ideal (MRing J)} {D : ℕ} (R : AnLogRes P Jd D) {a : K → ℤ}
    {φ : ((Σ k, J k) → ℂ) → ℝ}
    (hsm : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ a k) * φ z)
    (H : HermLine J) (hHa : H.a = a) {x y : R.X} (hy : y ∈ R.U x) :
    φ (R.lift y y) / H.h (R.lift y y) = φ (R.lift x y) / H.h (R.lift x y) := by
  obtain ⟨c, hc, e⟩ := R.compat y x y ⟨R.mem_U y, hy⟩
  have hne : (∏ k, ‖c k‖ ^ a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  rw [e, hsm _ (R.mem x y hy) c hc, H.smul c _ hc, hHa, mul_div_mul_left _ _ hne]

theorem smooth_ratio {P Jd : Ideal (MRing J)} {D : ℕ} (R : AnLogRes P Jd D) {a : K → ℤ}
    {φ : ((Σ k, J k) → ℂ) → ℝ}
    (hsm : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ a k) * φ z)
    (hloc : ∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧
      AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts P, F z' ≠ 0 ∧ φ z' = ‖F z'‖)
    (H : HermLine J) (hHa : H.a = a) (hH : IsSmoothHerm H) :
    R.A.Smooth fun x => Real.log (φ (R.lift x x) / H.h (R.lift x x)) := by
  intro j t ht
  have ht : t ∈ (R.A.chart j).target := ht.1
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ = (R.A.chart j).symm t := ⟨_, rfl⟩
  have hm₀ : R.lift x₀ x₀ ∈ mcPts P := R.mem _ _ (R.mem_U _)
  obtain ⟨V, F, hV, hzV, hF, hFφ⟩ := hloc _ hm₀
  have hγ : AnalyticAt ℂ (fun t' => R.lift x₀ ((R.A.chart j).symm t')) t :=
    analyticAt_lift R x₀ j ht (hx₀ ▸ R.mem_U _)
  have hγt : R.lift x₀ ((R.A.chart j).symm t) = R.lift x₀ x₀ := by rw [hx₀]
  have hsc : ContinuousAt (R.A.chart j).symm t := (R.A.chart j).continuousAt_symm ht
  have hev : ∀ᶠ t' in 𝓝 t, (R.A.chart j).symm t' ∈ R.U x₀ ∧
      R.lift x₀ ((R.A.chart j).symm t') ∈ V := by
    refine (hsc.eventually ((R.isOpen_U x₀).mem_nhds (hx₀ ▸ R.mem_U _))).and
      (hγ.continuousAt.eventually (hV.mem_nhds ?_))
    show R.lift x₀ ((R.A.chart j).symm t) ∈ V
    rw [hγt]
    exact hzV
  have hne : F (R.lift x₀ ((R.A.chart j).symm t)) ≠ 0 := by
    rw [hγt]
    exact (hFφ _ ⟨hzV, hm₀⟩).1
  have hFa : AnalyticAt ℂ (fun t' => F (R.lift x₀ ((R.A.chart j).symm t'))) t :=
    AnalyticAt.fun_comp (hF _ (by rw [hγt]; exact hzV)) hγ
  have e1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t' => F (R.lift x₀ ((R.A.chart j).symm t'))) t :=
    hFa.contDiffAt.restrict_scalars ℝ
  have e2 := (e1.norm ℝ hne).log (norm_ne_zero_iff.2 hne)
  have hγr : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t' => R.lift x₀ ((R.A.chart j).symm t')) t :=
    hγ.contDiffAt.restrict_scalars ℝ
  have hmem : R.lift x₀ ((R.A.chart j).symm t) ∈ {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    rw [hγt]
    exact hm₀.1
  have e3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t' => H.h (R.lift x₀ ((R.A.chart j).symm t'))) t :=
    ContDiffAt.comp t (hH.contDiffAt (isOpen_blockNz.mem_nhds hmem)) hγr
  have e4 := e3.log (H.pos _ hmem).ne'
  refine ((e2.sub e4).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hev] with t' ht'
  obtain ⟨h1, h2⟩ := ht'
  have hm := R.mem _ _ h1
  obtain ⟨h0, hφ⟩ := hFφ _ ⟨h2, hm⟩
  show Real.log (φ (R.lift _ _) / H.h (R.lift _ _)) = _
  rw [ratio_eq R hsm H hHa h1, hφ, Real.log_div (norm_ne_zero_iff.2 h0) (H.pos _ hm.1).ne']

theorem isFlatOn_of_local {P Jd : Ideal (MRing J)} {D : ℕ} (R : AnLogRes P Jd D) (T : HermLine J)
    {φ : ((Σ k, J k) → ℂ) → ℝ} (hT : ∀ z ∈ mcPts P, T.h z = φ z)
    (hloc : ∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧
      AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts P, F z' ≠ 0 ∧ φ z' = ‖F z'‖) :
    IsFlatOn R T := by
  intro x _
  have hm₀ : R.lift x x ∈ mcPts P := R.mem _ _ (R.mem_U _)
  obtain ⟨V, F, hV, hzV, hF, hFφ⟩ := hloc _ hm₀
  have hcl : ContinuousOn (R.lift x) (R.U x) :=
    continuousOn_pi.2 fun p => continuousOn_of_holoOn R.A (R.holo x p)
  have hW₁ : IsOpen (R.U x ∩ R.lift x ⁻¹' V) := hcl.isOpen_inter_preimage (R.isOpen_U x) hV
  have hf0 : F (R.lift x x) ≠ 0 := (hFφ _ ⟨hzV, hm₀⟩).1
  have hfc : ContinuousOn (fun y => F (R.lift x y) / F (R.lift x x)) (R.U x ∩ R.lift x ⁻¹' V) :=
    (hF.continuousOn.comp (hcl.mono inter_subset_left) fun y hy => hy.2).div_const _
  have hW := hfc.isOpen_inter_preimage hW₁ Complex.isOpen_slitPlane
  refine ⟨_, hW, ⟨⟨R.mem_U x, hzV⟩, by simp [hf0]⟩,
    fun y => Complex.log (F (R.lift x y) / F (R.lift x x)) + (Real.log ‖F (R.lift x x)‖ : ℂ), ?_, ?_⟩
  · intro j t ht
    have hγ := analyticAt_lift R x j ht.1 ht.2.1.1
    have hFa : AnalyticAt ℂ (fun t' => F (R.lift x ((R.A.chart j).symm t'))) t :=
      AnalyticAt.fun_comp (hF _ ht.2.1.2) hγ
    have hga : AnalyticAt ℂ (fun t' => F (R.lift x ((R.A.chart j).symm t')) / F (R.lift x x)) t :=
      hFa.div analyticAt_const hf0
    exact (hga.clog ht.2.2).add analyticAt_const
  · intro y hy
    have hm : R.lift x y ∈ V ∩ mcPts P := ⟨hy.1.2, R.mem x y hy.1.1⟩
    obtain ⟨h0, h1⟩ := hFφ _ hm
    show Real.log (T.h (R.lift x y)) - 0 = _
    rw [hT _ hm.2, h1, Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
      Real.log_div (norm_ne_zero_iff.2 h0) (norm_ne_zero_iff.2 hf0)]
    ring

theorem exists_flat_line : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (D : ℕ) (R : AnLogRes P ⊤ D) (a : K → ℤ) (φ : ((Σ k, J k) → ℂ) → ℝ), (∀ z ∈ mcPts P, 0 < φ z) → (∀ z ∈ mcPts P, φ (fun p => starRingEnd ℂ (z p)) = φ z) → (∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ a k) * φ z) → (∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts P, F z' ≠ 0 ∧ φ z' = ‖F z'‖) → ∃ T : HermLine J, T.a = a ∧ IsSmoothHerm T ∧ IsConjInvariantH T ∧ (∀ z ∈ mcPts P, T.h z = φ z) ∧ IsFlatOn R T := by
  intro K _ J _ P D R a φ hpos hconj hsm hloc
  have hHs : IsSmoothHerm (GroundTheory.Heights₂.Heights.LowerBoundFree.fsHerm J a) :=
    GroundTheory.Heights₂.Heights.LowerBoundFree.FsInvPow.isSmoothHerm_fsHerm a
  obtain ⟨H, hHdef⟩ : ∃ H, H = GroundTheory.Heights₂.Heights.LowerBoundFree.fsHerm J a := ⟨_, rfl⟩
  have hHa : H.a = a := by rw [hHdef]; rfl
  rw [← hHdef] at hHs
  obtain ⟨B, hBa, hBs, hB⟩ := GlobalTheory.T.smooth_function_as_degree_zero_metric K J P D R _ (smooth_ratio R hsm hloc H hHa hHs)
  have hT₀s : IsSmoothHerm (H.tensor B) := ContDiffOn.mul hHs hBs
  have hT₀a : (H.tensor B).a = a := by
    show H.a + B.a = a
    rw [hHa, hBa, add_zero]
  have hpt : ∀ x, (H.tensor B).h (R.lift x x) = φ (R.lift x x) := by
    intro x
    have hm := R.mem x x (R.mem_U x)
    have hHp := H.pos _ hm.1
    have hBp := B.pos _ hm.1
    have hq : 0 < φ (R.lift x x) / H.h (R.lift x x) := div_pos (hpos _ hm) hHp
    have e := Real.log_injOn_pos (Set.mem_Ioi.2 hBp) (Set.mem_Ioi.2 hq) (hB x)
    show H.h _ * B.h _ = _
    rw [e]
    field_simp
  have hT₀ : ∀ z ∈ mcPts P, (H.tensor B).h z = φ z := by
    intro z hz
    have hnt : z ∉ mcPts (⊤ : Ideal (MRing J)) := fun h => by
      have h1 := h.2 1 trivial
      simp at h1
    obtain ⟨x, c, hc, e⟩ := R.surj z hz hnt
    have hne : (∏ k, ‖c k‖ ^ a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
    have h1 := hpt x
    rw [e, (H.tensor B).smul c z hc, hT₀a, hsm z hz c hc] at h1
    exact mul_left_cancel₀ hne h1
  obtain ⟨T, hTa, hTs, hTc, hT⟩ := GlobalTheory.T.conjugation_invariant_hermitian_metric K J (H.tensor B) hT₀s
  have hTφ : ∀ z ∈ mcPts P, T.h z = φ z := by
    intro z hz
    have hc := conj_mem_mcPts hz
    have e := hT z hz.1
    rw [hT₀ z hz, hT₀ _ hc, hconj z hz, add_self_div_two] at e
    exact Real.log_injOn_pos (Set.mem_Ioi.2 (T.pos z hz.1)) (Set.mem_Ioi.2 (hpos z hz)) e
  exact ⟨T, hTa.trans hT₀a, hTs, hTc, hTφ, isFlatOn_of_local R T hTφ hloc⟩

end GlobalTheory.CompanionTheory.Ar.Chg.FlatExt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PositiveHomogeneousPotentialStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_homogeneous_potential : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (D : ℕ) (R : AnLogRes P ⊤ D) (a : K → ℤ) (φ : ((Σ k, J k) → ℂ) → ℝ), (∀ z ∈ mcPts P, 0 < φ z) → (∀ z ∈ mcPts P, φ (fun p => starRingEnd ℂ (z p)) = φ z) → (∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ a k) * φ z) → (∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts P, F z' ≠ 0 ∧ φ z' = ‖F z'‖) → ∃ T : HermLine J, T.a = a ∧ IsSmoothHerm T ∧ IsConjInvariantH T ∧ (∀ z ∈ mcPts P, T.h z = φ z) ∧ IsFlatOn R T := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.FlatExt.exists_flat_line | exact GlobalTheory.CompanionTheory.Ar.Chg.FlatExt.exists_flat_line | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.FlatExt.exists_flat_line <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DegreeReindexedCoords
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DegreeReindexedCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg.Ratio

open MvPolynomial

variable {K₀ K : Type} [Fintype K₀] [Fintype K] {J₀ : K₀ → Type} {J : K → Type} [∀ k, Fintype (J₀ k)]
  [∀ k, Fintype (J k)] {Ω Ω₀ : Type} [Field Ω] [Field Ω₀]

theorem prod_comp_zpow {G : Type} [CommGroupWithZero G] {bk : K₀ → K} (hbk : Function.Injective bk) (c : K → G)
    (a₀ : K₀ → ℤ) : ∏ k, c (bk k) ^ a₀ k = ∏ k, c k ^ pullDeg bk a₀ k := by
  classical
  have h1 : ∏ k, c k ^ pullDeg bk a₀ k = ∏ k ∈ Finset.univ.image bk, c k ^ pullDeg bk a₀ k := by
    refine (Finset.prod_subset (Finset.subset_univ _) fun k _ hk => ?_).symm
    have : ¬ ∃ x, bk x = k := fun ⟨x, hx⟩ => hk (Finset.mem_image.2 ⟨x, Finset.mem_univ _, hx⟩)
    simp [pullDeg, Function.extend_apply' _ _ _ this]
  rw [h1, Finset.prod_image fun _ _ _ _ h => hbk h]
  exact Finset.prod_congr rfl fun k _ => by simp [pullDeg, hbk.extend_apply]

def cmpFn (i : Ω₀ →+* Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀)
    (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k) : Ω :=
  i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, c k⟩ ^ a k) * e)

def cmpVal (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (a : K → ℤ) (a₀ : K₀ → ℤ) (w : (Σ k, J k) → ℂ)
    (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k) (u : ℂ) : ℂ :=
  u * (∏ k, w ⟨k, c k⟩ ^ a k) / ∏ k, w (blkV bk bx ⟨k, c₀ k⟩) ^ a₀ k

def IsCmp (i : Ω₀ →+* Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k))
    (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀) (w : (Σ k, J k) → ℂ) (t : ℂ) : Prop :=
  ∃ (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k) (u : ℂ), (∀ k, w ⟨k, c k⟩ ≠ 0) ∧
    (∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) ∧ u ≠ 0 ∧
    GroundTheory.Heights₂.Heights.LowerBoundFree.IsValueAt y (cmpFn i y₀ y a a₀ e e₀ c c₀) w u ∧
    t = cmpVal bk bx a a₀ w c c₀ u

theorem cmpVal_ne_zero {bk : K₀ → K} {bx : ∀ k, J₀ k ≃ J (bk k)} {a : K → ℤ} {a₀ : K₀ → ℤ} {w : (Σ k, J k) → ℂ}
    {c : (k : K) → J k} {c₀ : (k : K₀) → J₀ k} {u : ℂ} (h1 : ∀ k, w ⟨k, c k⟩ ≠ 0)
    (h2 : ∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) (hu : u ≠ 0) : cmpVal bk bx a a₀ w c c₀ u ≠ 0 :=
  div_ne_zero (mul_ne_zero hu (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h1 k)))
    (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h2 k))

section Val

variable {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of ℂ) ⟶ X}

theorem valAt_prod_zpow {I : Type} [Fintype I] {f : I → Ω} {r : I → ℂ} (hz : genPt ξ ⤳ centre z)
    (h : ∀ k, ValAt ξ z (f k) (r k)) (h0 : ∀ k, r k ≠ 0) (n : I → ℤ) :
    ValAt ξ z (∏ k, f k ^ n k) (∏ k, r k ^ n k) := by
  classical
  have hp : ∀ s : Finset I, ValAt ξ z (∏ k ∈ s, f k ^ n k) (∏ k ∈ s, r k ^ n k) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using CxVal.one hz
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.prod_insert hk]
      exact CxVal.mul (CxVal.zpow (h k) (h0 k) _) ih
  exact hp Finset.univ

theorem cmpVal_eq {i : Ω₀ →+* Ω} {y₀ : (Σ k, J₀ k) → Ω₀} {y : (Σ k, J k) → Ω} {bk : K₀ → K}
    {bx : ∀ k, J₀ k ≃ J (bk k)} {a : K → ℤ} {a₀ : K₀ → ℤ} {e : Ω} {e₀ : Ω₀} {w : (Σ k, J k) → ℂ}
    (hy : ∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w)
    {c c' : (k : K) → J k} {c₀ c₀' : (k : K₀) → J₀ k} (h1 : ∀ k, w ⟨k, c k⟩ ≠ 0) (h1' : ∀ k, w ⟨k, c' k⟩ ≠ 0)
    (h2 : ∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) (h2' : ∀ k, w (blkV bk bx ⟨k, c₀' k⟩) ≠ 0) {u u' : ℂ}
    (hu : ValAt ξ z (cmpFn i y₀ y a a₀ e e₀ c c₀) u) (hu' : ValAt ξ z (cmpFn i y₀ y a a₀ e e₀ c' c₀') u') :
    cmpVal bk bx a a₀ w c c₀ u = cmpVal bk bx a a₀ w c' c₀' u' := by
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k (c k) (IsUnit.mk0 _ (h1 k))).1
  have hyc' : ∀ k, y ⟨k, c' k⟩ ≠ 0 := fun k => (hw.2 k (c' k) (IsUnit.mk0 _ (h1' k))).1
  have hyv : ∀ k, y (blkV bk bx ⟨k, c₀ k⟩) ≠ 0 := fun k => (hw.2 (bk k) (bx k (c₀ k)) (IsUnit.mk0 _ (h2 k))).1
  have hyv' : ∀ k, y (blkV bk bx ⟨k, c₀' k⟩) ≠ 0 := fun k => (hw.2 (bk k) (bx k (c₀' k)) (IsUnit.mk0 _ (h2' k))).1
  choose r hr hr' using fun k => (hw.2 k (c' k) (IsUnit.mk0 _ (h1' k))).2 (c k)
  choose q hq hq' using fun k => (hw.2 (bk k) (bx k (c₀ k)) (IsUnit.mk0 _ (h2 k))).2 (bx k (c₀' k))
  have hr0 : ∀ k, r k ≠ 0 := fun k h => h1 k (by rw [hr', h, zero_mul])
  have hq0 : ∀ k, q k ≠ 0 := fun k h => h2' k (by
    show w ⟨bk k, bx k (c₀' k)⟩ = 0
    rw [hq', h, zero_mul])
  have e1 := valAt_prod_zpow hz hr hr0 a
  have e2 := valAt_prod_zpow hz hq hq0 a₀
  have hM : ∀ c₁ : (k : K₀) → J₀ k, i (∏ k, y₀ ⟨k, c₁ k⟩ ^ a₀ k) = ∏ k, y (blkV bk bx ⟨k, c₁ k⟩) ^ a₀ k := by
    intro c₁
    rw [map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_zpow₀]
    show _ = y ⟨bk k, bx k (c₁ k)⟩ ^ a₀ k
    rw [hy]
  have key : cmpFn i y₀ y a a₀ e e₀ c' c₀' = cmpFn i y₀ y a a₀ e e₀ c c₀ *
      (∏ k, (y ⟨bk k, bx k (c₀' k)⟩ / y ⟨bk k, bx k (c₀ k)⟩) ^ a₀ k) *
      ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ a k := by
    simp only [cmpFn, map_mul, hM, div_zpow, Finset.prod_div_distrib]
    have n1 : (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyc k)
    have n2 : (∏ k, y ⟨k, c' k⟩ ^ a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyc' k)
    have n3 : (∏ k, y ⟨bk k, bx k (c₀ k)⟩ ^ a₀ k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyv k)
    have e3 : ∀ c₁ : (k : K₀) → J₀ k, (∏ k, y (blkV bk bx ⟨k, c₁ k⟩) ^ a₀ k) = ∏ k, y ⟨bk k, bx k (c₁ k)⟩ ^ a₀ k :=
      fun _ => rfl
    rw [e3, e3]
    by_cases he : e = 0
    · simp [he]
    · field_simp
  have hu2 := CxVal.unique hu' (key ▸ CxVal.mul (CxVal.mul hu e2) e1)
  have w1 : (∏ k, w ⟨k, c k⟩ ^ a k) = (∏ k, r k ^ a k) * ∏ k, w ⟨k, c' k⟩ ^ a k := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [hr' k, mul_zpow]
  have w2 : (∏ k, w (blkV bk bx ⟨k, c₀' k⟩) ^ a₀ k) =
      (∏ k, q k ^ a₀ k) * ∏ k, w (blkV bk bx ⟨k, c₀ k⟩) ^ a₀ k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    show w ⟨bk k, bx k (c₀' k)⟩ ^ a₀ k = _
    rw [hq' k, mul_zpow]
    rfl
  have n4 : (∏ k, w (blkV bk bx ⟨k, c₀ k⟩) ^ a₀ k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h2 k)
  have n5 : (∏ k, q k ^ a₀ k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hq0 k)
  simp only [cmpVal]
  rw [w1, w2, hu2]
  field_simp

end Val

section Points

open GroundTheory.Heights₂.Heights.LowerBoundFree (IsValueAt)

variable {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {i : Ω₀ →+* Ω} {y₀ : (Σ k, J₀ k) → Ω₀}
  {y : (Σ k, J k) → Ω} {bk : K₀ → K} {bx : ∀ k, J₀ k ≃ J (bk k)} {a : K → ℤ} {a₀ : K₀ → ℤ} {e : Ω} {e₀ : Ω₀}
  {w : (Σ k, J k) → ℂ}

theorem isCmp_unique (hT : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    (hy : ∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) (hm : w ∈ mcPts (mCoordIdeal y)) {t t' : ℂ}
    (h : IsCmp i y₀ y bk bx a a₀ e e₀ w t) (h' : IsCmp i y₀ y bk bx a a₀ e e₀ w t') : t = t' := by
  obtain ⟨z, hz, hw⟩ := (GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT w).1 hm
  obtain ⟨c, c₀, u, h1, h2, -, hv, rfl⟩ := h
  obtain ⟨c', c₀', u', h1', h2', -, hv', rfl⟩ := h'
  exact cmpVal_eq hy hz hw h1 h1' h2 h2' ((GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w hz hw _ _).2 hv)
    ((GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w hz hw _ _).2 hv')

theorem IsCmp.ne_zero {t : ℂ} (h : IsCmp i y₀ y bk bx a a₀ e e₀ w t) : t ≠ 0 := by
  obtain ⟨c, c₀, u, h1, h2, hu, -, rfl⟩ := h
  exact cmpVal_ne_zero h1 h2 hu

theorem IsCmp.smul (hT : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    (hm : w ∈ mcPts (mCoordIdeal y)) {t : ℂ} (h : IsCmp i y₀ y bk bx a a₀ e e₀ w t) {s : K → ℂ}
    (hs : ∀ k, s k ≠ 0) :
    (fun p => s p.1 * w p) ∈ mcPts (mCoordIdeal y) ∧
    IsCmp i y₀ y bk bx a a₀ e e₀ (fun p => s p.1 * w p)
      ((∏ k, s k ^ a k) / (∏ k, s (bk k) ^ a₀ k) * t) := by
  obtain ⟨z, hz, hw⟩ := (GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT w).1 hm
  have hw' : CoordsAt ξ y z (fun p => s p.1 * w p) := coordsAt_orbit hw ⟨s, hs, rfl⟩
  refine ⟨(GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT _).2 ⟨z, hz, hw'⟩, ?_⟩
  obtain ⟨c, c₀, u, h1, h2, hu, hv, rfl⟩ := h
  refine ⟨c, c₀, u, fun k => mul_ne_zero (hs _) (h1 k), fun k => mul_ne_zero (hs _) (h2 k), hu,
    (GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z _ hz hw' _ _).1 ((GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w hz hw _ _).2 hv), ?_⟩
  have n1 : (∏ k, s (bk k) ^ a₀ k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hs _)
  have n2 : (∏ k, w (blkV bk bx ⟨k, c₀ k⟩) ^ a₀ k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h2 k)
  have e1 : (∏ k, (s (blkV bk bx ⟨k, c₀ k⟩).1 * w (blkV bk bx ⟨k, c₀ k⟩)) ^ a₀ k) =
      (∏ k, s (bk k) ^ a₀ k) * ∏ k, w (blkV bk bx ⟨k, c₀ k⟩) ^ a₀ k := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => mul_zpow _ _ _
  have e2 : (∏ k, (s k * w ⟨k, c k⟩) ^ a k) = (∏ k, s k ^ a k) * ∏ k, w ⟨k, c k⟩ ^ a k := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => mul_zpow _ _ _
  simp only [cmpVal]
  rw [e1, e2]
  field_simp

theorem eval_conj {σ : Type} (g : MvPolynomial σ ℤ) (w : σ → ℂ) :
    eval (fun p => starRingEnd ℂ (w p)) (map (Int.castRingHom ℂ) g) =
      starRingEnd ℂ (eval w (map (Int.castRingHom ℂ) g)) := by
  induction g using MvPolynomial.induction_on with
  | C n => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp => simp only [map_mul, hp, map_X, eval_X]

theorem conj_mem_mcPts (hm : w ∈ mcPts (mCoordIdeal y)) :
    (fun p => starRingEnd ℂ (w p)) ∈ mcPts (mCoordIdeal y) := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨x, hx⟩ := hm.1 k
    exact ⟨x, by simpa using hx⟩
  · rw [eval_conj, hm.2 f hf, map_zero]

theorem IsCmp.conj {t : ℂ} (h : IsCmp i y₀ y bk bx a a₀ e e₀ w t) :
    IsCmp i y₀ y bk bx a a₀ e e₀ (fun p => starRingEnd ℂ (w p)) (starRingEnd ℂ t) := by
  obtain ⟨c, c₀, u, h1, h2, hu, ⟨d, g, h, hg, hh, hy0, heq, hz0, rfl⟩, rfl⟩ := h
  refine ⟨c, c₀, _, fun k => by simpa using h1 k, fun k => by simpa using h2 k, ?_,
    ⟨d, g, h, hg, hh, hy0, heq, ?_, rfl⟩, ?_⟩
  · rw [eval_conj, eval_conj, ← map_div₀]
    simpa using hu
  · rw [eval_conj]
    simpa using hz0
  · simp only [cmpVal, map_div₀, map_mul, map_prod, map_zpow₀, eval_conj]

end Points

theorem exists_isRatio : ∀ (X : Scheme.{0}) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (i : Ω₀ →+* Ω) (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ q : X, genPt ξ ⤳ q) → Function.Injective bk → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → ∀ (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k), (∀ k, w ⟨k, c k⟩ ≠ 0) → (∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) → ∃ u : ℂ, u ≠ 0 ∧ ValAt ξ z (i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, c k⟩ ^ a k) * e)) u) → ∃ φ : ((Σ k, J k) → ℂ) → ℝ, (∀ z ∈ mcPts (mCoordIdeal y), 0 < φ z) ∧ (∀ z ∈ mcPts (mCoordIdeal y), φ (fun p => starRingEnd ℂ (z p)) = φ z) ∧ (∀ z ∈ mcPts (mCoordIdeal y), ∀ c : K → ℂ, (∀ k, c k ≠ 0) → φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ (a - pullDeg bk a₀) k) * φ z) ∧ (∀ z ∈ mcPts (mCoordIdeal y), ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts (mCoordIdeal y), F z' ≠ 0 ∧ φ z' = ‖F z'‖) ∧ IsRatio ξ y y₀ bk bx i a a₀ e e₀ φ := by
  intro X Ω Ω₀ _ _ ξ i K₀ K _ _ J₀ J _ _ y₀ y bk bx a a₀ e e₀ hT hall hbk hy hU
  classical
  have hval : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w →
      ∀ (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k), (∀ k, w ⟨k, c k⟩ ≠ 0) → (∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) →
      ∃ u : ℂ, u ≠ 0 ∧ ValAt ξ z (cmpFn i y₀ y a a₀ e e₀ c c₀) u ∧
        IsCmp i y₀ y bk bx a a₀ e e₀ w (cmpVal bk bx a a₀ w c c₀ u) := by
    intro z w hw c c₀ h1 h2
    obtain ⟨u, hu, hv⟩ := hU z w hw c c₀ h1 h2
    exact ⟨u, hu, hv, c, c₀, u, h1, h2, hu,
      (GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w (hall _) hw _ _).1 hv, rfl⟩
  have hex : ∀ w ∈ mcPts (mCoordIdeal y), ∃ t, IsCmp i y₀ y bk bx a a₀ e e₀ w t := by
    intro w hm
    obtain ⟨z, -, hw⟩ := (GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT w).1 hm
    choose c hc using hw.1
    choose c₀ hc₀ using restr_ne (isBlockMap_blkV bx hbk) hm.1
    obtain ⟨u, -, -, h⟩ := hval z w hw c c₀ (fun k => (hc k).ne_zero) hc₀
    exact ⟨_, h⟩
  let ψ : ((Σ k, J k) → ℂ) → ℂ := fun w =>
    if h : ∃ t, IsCmp i y₀ y bk bx a a₀ e e₀ w t then h.choose else 1
  have hψ : ∀ w ∈ mcPts (mCoordIdeal y), ∀ t, IsCmp i y₀ y bk bx a a₀ e e₀ w t → ψ w = t := by
    intro w hm t ht
    have h : ∃ t, IsCmp i y₀ y bk bx a a₀ e e₀ w t := ⟨t, ht⟩
    simp only [ψ, dif_pos h]
    exact isCmp_unique hT hy hm h.choose_spec ht
  refine ⟨fun w => ‖ψ w‖, fun w hm => ?_, fun w hm => ?_, fun w hm s hs => ?_, fun w hm => ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hex w hm
    simpa [hψ w hm t ht] using ht.ne_zero
  · obtain ⟨t, ht⟩ := hex w hm
    show ‖ψ _‖ = ‖ψ w‖
    rw [hψ w hm t ht, hψ _ (conj_mem_mcPts hm) _ ht.conj, Complex.norm_conj]
  · obtain ⟨t, ht⟩ := hex w hm
    obtain ⟨hm', ht'⟩ := ht.smul hT hm hs
    show ‖ψ _‖ = _ * ‖ψ w‖
    have n : ∀ k, ‖s k‖ ≠ 0 := fun k => norm_ne_zero_iff.2 (hs k)
    rw [hψ w hm t ht, hψ _ hm' _ ht', norm_mul, norm_div, norm_prod, norm_prod]
    congr 1
    simp only [norm_zpow, Pi.sub_apply, zpow_sub₀ (n _), Finset.prod_div_distrib]
    rw [prod_comp_zpow hbk (fun k => ‖s k‖) a₀]
  · obtain ⟨t, c, c₀, u, h1, h2, -, ⟨d, g, h, hg, hh, hy0, heq, hz0, -⟩, -⟩ := hex w hm
    let G : ((Σ k, J k) → ℂ) → ℂ := fun x => eval x (map (Int.castRingHom ℂ) g)
    let H : ((Σ k, J k) → ℂ) → ℂ := fun x => eval x (map (Int.castRingHom ℂ) h)
    have aG : AnalyticOnNhd ℂ G Set.univ := AnalyticOnNhd.eval_mvPolynomial _
    have aH : AnalyticOnNhd ℂ H Set.univ := AnalyticOnNhd.eval_mvPolynomial _
    have cH : Continuous H := MvPolynomial.continuous_eval _
    let V : Set ((Σ k, J k) → ℂ) := {x | H x ≠ 0} ∩ ((⋂ k, {x | x ⟨k, c k⟩ ≠ 0}) ∩
      ⋂ k, {x | x (blkV bk bx ⟨k, c₀ k⟩) ≠ 0})
    have oV : IsOpen V := by
      refine (isOpen_ne_fun cH continuous_const).inter ((isOpen_iInter_of_finite fun k => ?_).inter
        (isOpen_iInter_of_finite fun k => ?_))
      · exact isOpen_ne_fun (continuous_apply _) continuous_const
      · exact isOpen_ne_fun (continuous_apply _) continuous_const
    have mV : ∀ x ∈ V, H x ≠ 0 ∧ (∀ k, x ⟨k, c k⟩ ≠ 0) ∧ ∀ k, x (blkV bk bx ⟨k, c₀ k⟩) ≠ 0 := by
      intro x hx
      exact ⟨hx.1, fun k => Set.mem_iInter.1 hx.2.1 k, fun k => Set.mem_iInter.1 hx.2.2 k⟩
    refine ⟨V, fun x => cmpVal bk bx a a₀ x c c₀ (G x / H x), oV, ?_, ?_, ?_⟩
    · exact ⟨hz0, Set.mem_iInter.2 h1, Set.mem_iInter.2 h2⟩
    · intro x hx
      obtain ⟨x1, x2, x3⟩ := mV x hx
      have pr1 : ∀ p : Σ k, J k, AnalyticAt ℂ (fun x : (Σ k, J k) → ℂ => x p) x := fun p =>
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Σ k, J k => ℂ) p).analyticAt x
      refine ((((aG x (Set.mem_univ _)).fun_div (aH x (Set.mem_univ _)) x1).fun_mul
        (Finset.analyticAt_fun_prod _ fun k _ => ?_)).fun_div
        (Finset.analyticAt_fun_prod _ fun k _ => ?_) ?_)
      · exact (pr1 _).zpow (x2 k)
      · exact (pr1 _).zpow (x3 k)
      · exact Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (x3 k)
    · rintro x ⟨hx, hxm⟩
      obtain ⟨x1, x2, x3⟩ := mV x hx
      obtain ⟨z, hz, hw⟩ := (GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT x).1 hxm
      have hv : GroundTheory.Heights₂.Heights.LowerBoundFree.IsValueAt y (cmpFn i y₀ y a a₀ e e₀ c c₀) x (G x / H x) :=
        ⟨d, g, h, hg, hh, hy0, heq, x1, rfl⟩
      obtain ⟨u, hu, hu', hc⟩ := hval z x hw c c₀ x2 x3
      have e1 : u = G x / H x :=
        CxVal.unique hu' ((GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z x hz hw _ _).2 hv)
      rw [e1] at hc hu
      exact ⟨hc.ne_zero, by show ‖ψ x‖ = _; rw [hψ x hxm _ hc]⟩
  · intro z w hw c c₀ h1 h2
    have hm : w ∈ mcPts (mCoordIdeal y) := (GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT w).2 ⟨z, hall _, hw⟩
    obtain ⟨u, hu, hv, hc⟩ := hval z w hw c c₀ h1 h2
    refine ⟨u, hu, hv, ?_⟩
    have n : (∏ k, ‖w (blkV bk bx ⟨k, c₀ k⟩)‖ ^ a₀ k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (h2 k))
    show ‖ψ w‖ * _ = _
    rw [hψ w hm _ hc]
    simp only [cmpVal, norm_div, norm_mul, norm_prod, norm_zpow]
    field_simp

end GlobalTheory.CompanionTheory.Ar.Chg.Ratio
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DegreeReindexedCoordsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_reindexed_coords : ∀ (X : Scheme.{0}) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (i : Ω₀ →+* Ω) (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ q : X, genPt ξ ⤳ q) → Function.Injective bk → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → ∀ (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k), (∀ k, w ⟨k, c k⟩ ≠ 0) → (∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) → ∃ u : ℂ, u ≠ 0 ∧ ValAt ξ z (i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, c k⟩ ^ a k) * e)) u) → ∃ φ : ((Σ k, J k) → ℂ) → ℝ, (∀ z ∈ mcPts (mCoordIdeal y), 0 < φ z) ∧ (∀ z ∈ mcPts (mCoordIdeal y), φ (fun p => starRingEnd ℂ (z p)) = φ z) ∧ (∀ z ∈ mcPts (mCoordIdeal y), ∀ c : K → ℂ, (∀ k, c k ≠ 0) → φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ (a - pullDeg bk a₀) k) * φ z) ∧ (∀ z ∈ mcPts (mCoordIdeal y), ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts (mCoordIdeal y), F z' ≠ 0 ∧ φ z' = ‖F z'‖) ∧ IsRatio ξ y y₀ bk bx i a a₀ e e₀ φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.Ratio.exists_isRatio | exact GlobalTheory.CompanionTheory.Ar.Chg.Ratio.exists_isRatio | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.Ratio.exists_isRatio <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatOnLogResolutionCorr
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatOnLogResolutionCorr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

namespace GlobalTheory.CompanionTheory.Ar.Chg

theorem isFlatOn_corr : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P Jd : Ideal (MRing J)) (D : ℕ) (R : AnLogRes P Jd D) (Ψ : Type) (N : ℕ) (T : Ψ × Fin N → HermLine J), (∀ r, IsFlatOn R (T r)) → ∀ a, IsFlatOn R (corr T a) := by
  intro K _ J _ P Jd D R Ψ N T hT a x _
  cases a with
  | none =>
    refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => 0, fun j => analyticOnNhd_const, fun y _ => ?_⟩
    simp [potOf, corr, Top.trivLine, LocPot.ofFun]
  | some r =>
    choose V hVo hxV G hG hE using fun k : Fin N => hT (r.1, k) x (Set.mem_univ x)
    refine ⟨R.U x ∩ ⋂ k, V k, (R.isOpen_U x).inter (isOpen_iInter_of_finite hVo),
      ⟨R.mem_U x, Set.mem_iInter.2 hxV⟩, fun y => -∑ k ∈ Finset.Iic r.2, G k y, fun j w hw => ?_, fun y hy => ?_⟩
    · have hs : ∀ k ∈ Finset.Iic r.2, AnalyticAt ℂ (G k ∘ (R.A.chart j).symm) w := fun k _ =>
        hG k j w ⟨hw.1, Set.mem_iInter.1 hw.2.2 k⟩
      exact (Finset.analyticAt_fun_sum _ hs).neg
    · have hm := (R.mem x y hy.1).1
      have e : (potOf R (corr T (some r))).φ x y = -∑ k ∈ Finset.Iic r.2, Real.log ((T (r.1, k)).h (R.lift x y)) :=
        log_stepLine (fun k => T (r.1, k)) r.2 hm
      have e' : ∀ k, Real.log ((T (r.1, k)).h (R.lift x y)) = (G k y).re := fun k => by
        simpa [potOf, LocPot.ofFun] using hE k y (Set.mem_iInter.1 hy.2 k)
      simp [e, e', LocPot.ofFun]

end GlobalTheory.CompanionTheory.Ar.Chg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatOnLogResolutionCorrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_on_log_resolution_corr : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P Jd : Ideal (MRing J)) (D : ℕ) (R : AnLogRes P Jd D) (Ψ : Type) (N : ℕ) (T : Ψ × Fin N → HermLine J), (∀ r, IsFlatOn R (T r)) → ∀ a, IsFlatOn R (corr T a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.isFlatOn_corr | exact GlobalTheory.CompanionTheory.Ar.Chg.isFlatOn_corr | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.isFlatOn_corr <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCoordsOverField
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

theorem root_model_on_cover : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y ∅ R Fx) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (bk : R.K → K) (bx : ∀ k, R.ι k ≃ J (bk k)) (i : R.Ω →+* Ω) (𝔐 : HodgeCpt Y S y) (h : 𝔐.X ⟶ o.𝔐.X) (Fl : 𝔐.Flag) (xdeg : RootIx D → K → ℤ) (e : RootIx D → Ω), o.Fl.deg = 1 → Cmp.IsEmbedded o.Re.R.A R.P o.Re.R.U o.Re.R.lift → Function.Bijective o.Re.π → Function.Injective bk → (∀ k a, y ⟨bk k, bx k a⟩ = i (R.y ⟨k, a⟩)) → GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ o.𝔐.ξ h i → 𝔐.f = h ≫ o.𝔐.f → 𝔐.cst = i.comp o.𝔐.cst → (∀ s a, (𝔐.M.pt (Fl.b s a)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (o.𝔐.M.pt (o.Fl.b s a)).left ≫ o.𝔐.m.φ) → (letI := i.toAlgebra; Module.finrank R.Ω Ω = Fl.deg) → Fl.RootLines xdeg e → 𝔐.OmVB → SmoothGenericFibreM y → ∃ (RM : Top.RootModel (CMType H) (D.p + D.q)) (o' : RootOrigin Y S RM Fx), o'.𝔐.OmVB ∧ o'.𝔐.R = 𝔐.R ∧ o'.Re.J = ⊤ ∧ ∃ _ : Algebra ℚ RM.Ω, SmoothGenericFibreM RM.y := by
  intro hG E _ _ _ H D l Xo c Y Sys Fx R o S Ω _ _ K _ J _ y bk bx i 𝔐 h Fl xdeg e hdeg1 hemb hbij hbk hy hd hf hcst
    hfl hfin hlines hom hsm
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  have hv := isBlockMap_blkV bx hbk
  haveI : Nonempty K := ⟨bk o.k₀⟩
  obtain ⟨hbir, harith⟩ := GlobalTheory.T.hodge_cpt_birational_arith_var E H D l Xo c _ _ Y S Ω K J y 𝔐 Fl hβ
  have harith' : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (Top.dimFl (CMType H) (D.p + D.q) + 1) := harith
  obtain ⟨R'⟩ := GlobalTheory.T.exists_analytic_log_resolution K J Ω y _ harith' hsm
  have hP₀ : ¬ (⊤ : Ideal (MRing R.ι)) ≤ mCoordIdeal R.y := fun h' =>
    R.arith.2.1.1.ne_top (top_le_iff.1 h')
  have hle : mCoordIdeal R.y ≤ imageZ (blkV bk bx) (mCoordIdeal y) := mCoordIdeal_le_imageZ i bx hy
  let R₀ : AnLogRes (mCoordIdeal R.y) ⊤ (Top.dimFl (CMType H) (D.p + D.q)) := withTop o.Re.R hP₀ hemb
  obtain ⟨hh, hholo, horb⟩ := GlobalTheory.T.log_resolution_functorial_holomorphic R.K R.ι K J bk (blkV bk bx) (mCoordIdeal R.y) (mCoordIdeal y) ⊤ _ _ R₀ R' hv hle
  have hdpos : 0 < Fl.deg := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h0, -⟩ := Fl.generic
    exact h0
  obtain ⟨br₀, hdeg₀⟩ := GlobalTheory.T.log_resolution_reindexed R.K K R.ι J R.Ω Ω R.y y bk bx i _ Fl.deg R₀ R' hh hbk hy R.arith harith'
    R.birational hbir hholo horb hfin hdpos
  obtain ⟨hholoπ, hdeg⟩ := GlobalTheory.T.holomorphic_degree_composition _ Fl.deg Sys.X o.Re.R.X R'.X Sys.A o.Re.R.A R'.A o.Re.π hh br₀ o.Re.holo hbij
    hholo hdeg₀
  obtain ⟨hreg, hrefl, hval⟩ := GlobalTheory.T.dominating_regular_push 𝔐.X o.𝔐.X Ω R.Ω 𝔐.ξ o.𝔐.ξ h i hd 𝔐.tie.gen
  have hval' : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (a : R.Ω) (r : ℂ), ValAt o.𝔐.ξ (z ≫ h) a r → ValAt 𝔐.ξ z (i a) r :=
    fun z a r => hval z a r (𝔐.all _)
  have hco := GlobalTheory.T.dominating_coords_reindexed 𝔐.X o.𝔐.X Ω R.Ω 𝔐.ξ o.𝔐.ξ h i R.K K R.ι J R.y y bk bx hd o.𝔐.tie 𝔐.all hy hval'
  have hcov : IsCovOf o.𝔐 𝔐 i h := ⟨hd, hf, hcst⟩
  obtain ⟨j, hj1, hj2, hj3, hj4, hj5⟩ := GlobalTheory.T.hodge_comp_descent_first E H D l Xo c _ _ Y ∅ S R.Ω Ω R.K K R.ι J R.y y o.𝔐 𝔐 i h hd o.Fl Fl hβ hcov hfl
  have hgen : GenPull o.Fl Fl i hd :=
    GlobalTheory.T.hodge_comp_descent_second E H D l Xo c _ _ Y ∅ S R.Ω Ω R.K K R.ι J R.y y o.𝔐 𝔐 i h hd o.Fl Fl j hreg hj1 hj2 hj3 hj4
  have hnorm : NormPull o.Fl Fl i h :=
    GlobalTheory.T.hodge_comp_descent_third E H D l Xo c _ _ Y ∅ S R.Ω Ω R.K K R.ι J R.y y o.𝔐 𝔐 i h hd o.Fl Fl j inferInstance hreg hj1 hj2 hj3 hj4 hj5
  have hab := mem_abLocus_iff o.𝔐 𝔐 h hf
  have hT : ∀ r : RootIx D, ∃ T : HermLine J, T.a = xdeg r - pullDeg bk (R.xdeg r) ∧ IsSmoothHerm T ∧
      IsConjInvariantH T ∧ IsFlatOn R' T ∧ IsRatio 𝔐.ξ y R.y bk bx i (xdeg r) (R.xdeg r) (e r) (o.e r) T.h := by
    intro r
    have hu := GlobalTheory.T.hodge_comp_descent_fourth E H D l Xo c _ _ Y ∅ S R.Ω Ω R.K K R.ι J R.y y o.𝔐 𝔐 i h hd o.Fl Fl bk bx (xdeg r) (R.xdeg r)
      (e r) (o.e r) r hβ inferInstance hy hgen (o.lines r) (hlines r) hrefl hreg hco
    obtain ⟨φ, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.degree_reindexed_coords 𝔐.X Ω R.Ω 𝔐.ξ i R.K K R.ι J R.y y bk bx (xdeg r) (R.xdeg r) (e r) (o.e r)
      𝔐.tie 𝔐.all hbk hy hu
    obtain ⟨T, t1, t2, t3, t4, t5⟩ := GlobalTheory.T.positive_homogeneous_potential K J _ _ R' _ φ h1 h2 h3 h4
    refine ⟨T, t1, t2, t3, t5, fun z w hw c c₀ hc hc₀ => ?_⟩
    have hm : w ∈ mcPts (mCoordIdeal y) := (GlobalTheory.T.complex_points_iff_centres 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie w).2 ⟨z, 𝔐.all _, hw⟩
    rw [t4 w hm]
    exact h5 z w hw c c₀ hc hc₀
  choose T hTa hTs hTc hTf hTr using hT
  have hmem : ∀ z ∈ mcPts (mCoordIdeal y), (fun p => z (blkV bk bx p)) ∈ mcPts (mCoordIdeal R.y) :=
    fun z hz => mem_mcPts_restr hv hle hz
  have hlift : ∀ x, ∀ k, ∃ a, R'.lift x x ⟨k, a⟩ ≠ 0 := fun x => (R'.mem x x (R'.mem_U x)).1
  have hlift₀ : ∀ x k, ∃ a, R'.lift x x (blkV bk bx ⟨k, a⟩) ≠ 0 := fun x => restr_ne hv (hlift x)
  have horb' : ∀ x, SameOrbit (o.Re.R.lift (hh x) (hh x)) (fun p => R'.lift x x (blkV bk bx p)) := horb
  let RM : Top.RootModel (CMType H) (D.p + D.q) :=
    { K := K, «ι» := J, Ω := Ω, y := y, arith := harith', birational := hbir, xdeg := xdeg
      x := fun t r => (pullHerm hv (R.x t r)).tensor (T r)
      x_deg := fun t r => by
        show pullDeg bk (R.x t r).a + (T r).a = xdeg r
        rw [R.x_deg, hTa]
        abel
      x_smooth := fun t r => isSmoothHerm_tensor (isSmoothHerm_pull hv (R.x_smooth t r)) (hTs r)
      x_conj := fun t r => isConj_tensor (isConj_pull hv (R.x_conj t r)) (hTc r)
      kA := R.kA, kA_pos := R.kA_pos
      A := pullHerm hv R.A
      A_smooth := isSmoothHerm_pull hv R.A_smooth
      A_conj := isConj_pull hv R.A_conj
      δ := Module.finrank ℚ c.F * Fl.deg
      δ_pos := Nat.mul_pos (Nat.pos_of_ne_zero fun h0 => by
        have h1 := R.δ_pos
        rw [o.δ_eq, h0, zero_mul] at h1
        exact lt_irrefl _ h1) hdpos }
  let Re' : PB.Realis Sys (mCoordIdeal y) :=
    { arith := harith', J := ⊤, R := R', π := o.Re.π ∘ hh, holo := hholoπ, deg := Fl.deg, deg_pos := hdpos
      br := o.Re.π '' br₀, degree := hdeg
      ref := fun a => (pullHerm hv (o.Re.ref a)).tensor (corr T a)
      ref_smooth := fun a => isSmoothHerm_tensor (isSmoothHerm_pull hv (o.Re.ref_smooth a)) (isSmoothHerm_corr hTs a)
      ref_pot := fun a => GlobalTheory.T.log_resolution_potential_pullback R.K K R.ι J bk (blkV bk bx) _ _ _ _ _ o.Re.R R' Sys.X Sys.A (Sys.th a) (o.Re.ref a)
        (corr T a) o.Re.π o.Re.holo hh hv hholoπ.1 hholo horb' (o.Re.ref_pot a) (GlobalTheory.T.flat_on_log_resolution_corr K J _ _ _ R' _ _ T hTf a)
      line := fun a t => (pullHerm hv (o.Re.line a t)).tensor (corr T a)
      line_deg := fun a t => by
        show pullDeg bk (o.Re.line a t).a + (corr T a).a = pullDeg bk (o.Re.ref a).a + (corr T a).a
        rw [o.Re.line_deg]
      line_smooth := fun a t h0 h1 => isSmoothHerm_tensor (isSmoothHerm_pull hv (o.Re.line_smooth a t h0 h1))
        (isSmoothHerm_corr hTs a)
      line_eq := fun a t h0 h1 x => by
        have e1 := o.Re.line_eq a t h0 h1 (hh x)
        have e2 := log_sub_orbit (o.Re.line_deg a t) (horb' x) (hlift₀ x)
        rw [log_tensor_pull hv _ _ (hlift x), log_tensor_pull hv _ _ (hlift x)]
        show _ = _ + Sys.phT a t (o.Re.π (hh x))
        linarith }
  have hsing : ∀ r, ((pullHerm hv (o.sing r)).tensor (T r)).a = xdeg r := fun r => by
    show pullDeg bk (o.sing r).a + (T r).a = xdeg r
    rw [o.sing_deg, hTa]
    abel
  have hInt : ∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, 𝔐.Interior z ↔ o.𝔐.Interior (z ≫ h) := fun z => hab (centre z)
  let o' : RootOrigin Y S RM Fx :=
    { 𝔐 := 𝔐, Fl := Fl, g := i.comp o.g
      g_over := by
        have hd' : 𝔐.ξ ≫ h = spMap i ≫ o.𝔐.ξ := hd
        rw [hf, ← Category.assoc, hd', Category.assoc, o.g_over, spMap_comp', Category.assoc]
      g_flag := fun s a => by
        rw [hfl s a, o.g_flag s a, dualMap_comp', spMap_comp', Category.assoc]
      g_deg := by
        have e1 := finrank_comp' o.g i
        have e2 := o.g_deg
        rw [hdeg1] at e2
        rw [e2, _root_.one_mul] at e1
        exact e1.trans hfin
      g_const := fun a ha => by
        obtain ⟨b, hb⟩ := o.g_const a ha
        exact ⟨b, by rw [hcst]; simp [hb]⟩
      δ_eq := rfl
      e := e, lines := hlines
      sing := fun r => (pullHerm hv (o.sing r)).tensor (T r)
      sing_deg := hsing
      hodge := fun r => GlobalTheory.T.hodge_comp_descent_fifth E H D l Xo c _ _ Y ∅ S R.Ω Ω R.K K R.ι J R.y y o.𝔐 𝔐 i h hd o.Fl Fl bk bx hv r (xdeg r)
        (R.xdeg r) (e r) (o.e r) (o.sing r) (T r) hβ inferInstance hy hgen hnorm hval' hco (fun z => (hInt z).1) (hlines r).1
        (o.sing_deg r) (hTa r) (hTr r) (o.hodge r)
      k₀ := bk o.k₀
      ix := o.ix.trans (bx o.k₀)
      y_eq := fun a => by
        show y ⟨bk o.k₀, bx o.k₀ (o.ix a)⟩ = i (o.g (Fx.yf a))
        rw [hy, o.y_eq]
      kA_eq := o.kA_eq
      A_deg := by
        constructor
        · show pullDeg bk R.A.a (bk o.k₀) = 1
          rw [pullDeg, hbk.extend_apply]
          exact o.A_deg.1
        · intro k hk
          show pullDeg bk R.A.a k = 0
          by_cases h' : ∃ a, bk a = k
          · obtain ⟨a, rfl⟩ := h'
            rw [pullDeg, hbk.extend_apply]
            exact o.A_deg.2 a fun e' => hk (by rw [e'])
          · rw [pullDeg, Function.extend_apply' _ _ _ h']
            rfl
      A_h := fun z hz => o.A_h _ (hmem z hz)
      eff := GlobalTheory.T.root_origin_coord_field E H D l Xo c _ _ Y Sys Fx R ∅ S o Ω K J y bk bx 𝔐 i h hd Fl xdeg e hy hgen hlines hrefl hreg hab
      Re := Re', Re_deg := rfl
      π_pt := fun x => by
        obtain ⟨a₀, ha₀⟩ := o.π_pt (hh x)
        obtain ⟨c', hc', hw⟩ := horb' x
        refine ⟨(c' o.k₀)⁻¹ * a₀, funext fun i' => ?_⟩
        have e1 := congrFun ha₀ i'
        simp only [Pi.smul_apply, smul_eq_mul] at e1
        rw [hw] at e1
        have e2 : c' o.k₀ * R'.lift x x ⟨bk o.k₀, bx o.k₀ (o.ix i')⟩ = a₀ * Fx.pt (o.Re.π (hh x)) i' := e1
        show R'.lift x x ⟨bk o.k₀, bx o.k₀ (o.ix i')⟩ = (c' o.k₀)⁻¹ * a₀ * Fx.pt (o.Re.π (hh x)) i'
        rw [_root_.mul_assoc, ← e2, inv_mul_cancel_left₀ (hc' o.k₀)]
      interior := fun x z hz => by
        have h1 : CoordsAt o.𝔐.ξ R.y (z ≫ h) (o.Re.R.lift (hh x) (hh x)) := coordsAt_orbit (hco z _ hz) (horb' x)
        exact (hInt z).trans (o.interior (hh x) (z ≫ h) h1)
      fund_deg := fun τ a => by
        show pullDeg bk (o.Re.ref (some (τ, a))).a + (stepLine (fun k => T (τ, k)) a).a = -∑ k ∈ Finset.Iic a, xdeg (τ, k)
        rw [o.fund_deg, pullDeg_neg_sum hbk]
        funext k
        simp only [stepLine, hTa, Pi.add_apply, Pi.neg_apply, Finset.sum_apply, Pi.sub_apply, Finset.sum_sub_distrib]
        show _ = -∑ k' ∈ Finset.Iic a, xdeg (τ, k') k
        ring
      fund_sing := fun τ a x hx => by
        have e1 := o.fund_sing τ a (hh x) hx
        have hab' : (o.Re.ref (some (τ, a))).a = -∑ k ∈ Finset.Iic a, (o.sing (τ, k)).a := by
          rw [o.fund_deg]
          simp only [o.sing_deg]
        have e2 := log_sum_orbit (Finset.Iic a) hab' (horb' x) (hlift₀ x)
        show Real.log (((pullHerm hv (o.Re.ref (some (τ, a)))).tensor (stepLine (fun k => T (τ, k)) a)).h (R'.lift x x)) +
            Sys.ph (some (τ, a)) (o.Re.π (hh x)) =
          -∑ k ∈ Finset.Iic a, Real.log (((pullHerm hv (o.sing (τ, k))).tensor (T (τ, k))).h (R'.lift x x))
        rw [log_tensor_pull hv _ _ (hlift x), log_stepLine _ _ (hlift x)]
        simp only [log_tensor_pull hv _ _ (hlift x), Finset.sum_add_distrib]
        linarith
      fund_reg := fun τ a t h0 h1 z hz => by
        have hz' : z ∈ mcPts (mCoordIdeal y) := hz
        have e1 := o.fund_reg τ a t h0 h1 _ (hmem z hz')
        show Real.log (((pullHerm hv (o.Re.line (some (τ, a)) t)).tensor (stepLine (fun k => T (τ, k)) a)).h z) =
          -∑ k ∈ Finset.Iic a, Real.log (((pullHerm hv (R.x t (τ, k))).tensor (T (τ, k))).h z)
        rw [log_tensor_pull hv _ _ hz'.1, log_stepLine _ _ hz'.1]
        simp only [log_tensor_pull hv _ _ hz'.1, Finset.sum_add_distrib]
        linarith
      ref_none := by
        refine ⟨?_, fun z hz => ?_⟩
        · show pullDeg bk (o.Re.ref none).a + 0 = pullDeg bk R.A.a
          rw [o.ref_none.1, add_zero]
        · show (o.Re.ref none).h (fun p => z (blkV bk bx p)) * 1 = R.A.h fun p => z (blkV bk bx p)
          rw [_root_.mul_one]
          exact o.ref_none.2 _ (hmem z hz) }
  exact ⟨RM, o', hom, rfl, rfl, inferInstance, hsm⟩

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCoordsOverFieldStatement
alias _root_.GlobalTheory.T.root_origin_coords_over_field :=
  GlobalTheory.CompanionTheory.Ar.root_model_on_cover
end
