module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormSheetEq

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EtalePolynomialBaseChangeIff
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EtalePolynomialBaseChangeIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.EtaleCoord

theorem etale_of_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S)
    (g : S →+* T) (hf : f.Etale) (h : (g.comp f).Etale) : g.Etale := by
  algebraize [f, g, g.comp f]
  exact Algebra.Etale.of_restrictScalars R S T

theorem etale_eval₂Hom_iff_int : ∀ (k A : Type) [CommRing k] [CommRing A] (N : ℕ), (Int.castRingHom (Localization.Away (N : k))).Etale → ∀ (φ : k →+* A), IsUnit (N : A) → ∀ (D : ℕ) (x : Fin D → A), (MvPolynomial.eval₂Hom φ x).Etale ↔ (MvPolynomial.eval₂Hom (Int.castRingHom A) x).Etale := by
  intro k A _ _ N hN φ hu D x
  let ι : k →+* Localization.Away (N : k) := algebraMap k _
  have hφN : IsUnit (φ (N : k)) := by simpa using hu
  let ψ : Localization.Away (N : k) →+* A := IsLocalization.Away.lift (N : k) hφN
  have hψ : ψ.comp ι = φ := by
    ext a
    simp [ψ, ι]
  have hι : ι.Etale := by
    rw [RingHom.etale_algebraMap]
    exact Algebra.Etale.of_isLocalizationAway (N : k)
  have ha : (MvPolynomial.map (σ := Fin D) ι).Etale := etale_mvPolynomial_map_of_etale ι hι
  have hb : (MvPolynomial.map (σ := Fin D) (Int.castRingHom (Localization.Away (N : k)))).Etale :=
    etale_mvPolynomial_map_of_etale _ hN
  let Θ := MvPolynomial.eval₂Hom ψ x
  have e1 : MvPolynomial.eval₂Hom φ x = Θ.comp (MvPolynomial.map ι) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [Θ, ← hψ]
    · intro j
      simp [Θ]
  have e2 : MvPolynomial.eval₂Hom (Int.castRingHom A) x =
      Θ.comp (MvPolynomial.map (Int.castRingHom (Localization.Away (N : k)))) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [Θ]
    · intro j
      simp [Θ]
  rw [e1, e2]
  exact ⟨fun h => RingHom.Etale.stableUnderComposition _ _ hb (etale_of_comp _ _ ha h),
    fun h => RingHom.Etale.stableUnderComposition _ _ ha (etale_of_comp _ _ hb h)⟩

end GlobalTheory.CompanionTheory.Ar.EtaleCoord
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EtalePolynomialBaseChangeIffStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_polynomial_base_change_iff : ∀ (k A : Type) [CommRing k] [CommRing A] (N : ℕ), (Int.castRingHom (Localization.Away (N : k))).Etale → ∀ (φ : k →+* A), IsUnit (N : A) → ∀ (D : ℕ) (x : Fin D → A), (MvPolynomial.eval₂Hom φ x).Etale ↔ (MvPolynomial.eval₂Hom (Int.castRingHom A) x).Etale := by
  first | exact @GlobalTheory.CompanionTheory.Ar.EtaleCoord.etale_eval₂Hom_iff_int | exact GlobalTheory.CompanionTheory.Ar.EtaleCoord.etale_eval₂Hom_iff_int | (intros; apply GlobalTheory.CompanionTheory.Ar.EtaleCoord.etale_eval₂Hom_iff_int <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EtaleOverIntegersLocalization
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EtaleOverIntegersLocalization
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.CommAlg.OrderEtale

theorem formallyUnramified_fractionRing (k K : Type) [CommRing k] [IsDomain k] [CharZero k]
    [Module.Finite ℤ k] [Field K] [Algebra k K] [IsFractionRing k K] [Algebra ℤ K] :
    Algebra.FormallyUnramified ℤ K := by
  have hinj : Function.Injective (algebraMap k K) := IsFractionRing.injective k K
  haveI : CharZero K := charZero_of_injective_algebraMap hinj
  letI : Algebra ℚ K := DivisionRing.toRatAlgebra
  haveI := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ℚ) (A := K) (RingHom.ext_int _ _)
  haveI := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := k) (A := K) (RingHom.ext_int _ _)
  haveI : Algebra.IsIntegral ℤ k := Algebra.IsIntegral.of_finite ℤ k
  have hint : ∀ a : k, IsIntegral ℚ (algebraMap k K a) := fun a =>
    IsIntegral.tower_top (A := ℚ)
      ((Algebra.IsIntegral.isIntegral (R := ℤ) a).algebraMap (B := K))
  haveI : Algebra.IsAlgebraic ℚ K := by
    constructor
    intro x
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := k) x
    rw [div_eq_mul_inv]
    have hb : IsIntegral ℚ (algebraMap k K b)⁻¹ :=
      (IsAlgebraic.inv_iff.mpr (hint b).isAlgebraic).isIntegral
    exact ((hint a).mul hb).isAlgebraic
  haveI : Algebra.FormallyUnramified ℚ K := Algebra.FormallyUnramified.of_isSeparable ℚ K
  haveI : Algebra.FormallyUnramified ℤ ℚ := Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors ℤ)
  exact Algebra.FormallyUnramified.comp ℤ ℚ K

theorem isUnramifiedAt_bot (k : Type) [CommRing k] [IsDomain k] [CharZero k]
    [Module.Finite ℤ k] : Algebra.IsUnramifiedAt ℤ (⊥ : Ideal k) := by
  have hM : (⊥ : Ideal k).primeCompl = nonZeroDivisors k := by
    ext x
    simp [Ideal.mem_primeCompl_iff, mem_nonZeroDivisors_iff_ne_zero]
  haveI : IsFractionRing k (Localization.AtPrime (⊥ : Ideal k)) := by
    unfold IsFractionRing
    rw [← hM]
    infer_instance
  letI : Field (Localization.AtPrime (⊥ : Ideal k)) := IsFractionRing.toField k
  exact formallyUnramified_fractionRing k (Localization.AtPrime (⊥ : Ideal k))

theorem exists_etale_away (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] :
    ∃ N : ℕ, N ≠ 0 ∧ (Int.castRingHom (Localization.Away (N : k))).Etale := by
  have hU : IsOpen (Algebra.unramifiedLocus ℤ k) := Algebra.isOpen_unramifiedLocus
  have hbot : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) ∈ Algebra.unramifiedLocus ℤ k :=
    isUnramifiedAt_bot k
  obtain ⟨V, ⟨f, rfl⟩, hfV, hVU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hbot hU
  have hf0 : f ≠ 0 := by
    intro h
    simp [h] at hfV
  have hint : Algebra.IsIntegral ℤ k := Algebra.IsIntegral.of_finite ℤ k
  have hne : Ideal.comap (algebraMap ℤ k) (Ideal.span {f}) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hf0 (Ideal.subset_span rfl) (Algebra.IsIntegral.isIntegral f)
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, eq_intCast] at hm
  have hmN : (m : k) ∣ ((m.natAbs : ℤ) : k) := map_dvd (Int.castRingHom k) (Int.dvd_natAbs.mpr dvd_rfl)
  have hfN : f ∣ ((m.natAbs : ℕ) : k) := by
    have := hm.trans hmN
    simpa using this
  obtain ⟨g, hg⟩ := hfN
  refine ⟨m.natAbs, Int.natAbs_ne_zero.mpr hm0, ?_⟩
  have hS : Algebra.FormallyUnramified ℤ (Localization.Away ((m.natAbs : ℕ) : k)) := by
    rw [← Algebra.basicOpen_subset_unramifiedLocus_iff]
    refine subset_trans ?_ hVU
    rw [hg]
    exact PrimeSpectrum.basicOpen_mul_le_left f g
  have hfree : Module.Free ℤ k := Module.free_of_finite_type_torsion_free'
  have hflat : Module.Flat ℤ (Localization.Away ((m.natAbs : ℕ) : k)) := by
    have := IsLocalization.flat (Localization.Away ((m.natAbs : ℕ) : k))
      (Submonoid.powers ((m.natAbs : ℕ) : k))
    exact Module.Flat.trans ℤ k _
  have hfp : Algebra.FinitePresentation ℤ (Localization.Away ((m.natAbs : ℕ) : k)) := by
    have : Algebra.FinitePresentation ℤ k := Algebra.FinitePresentation.of_finiteType.mp inferInstance
    have := IsLocalization.Away.finitePresentation (S := Localization.Away ((m.natAbs : ℕ) : k))
      ((m.natAbs : ℕ) : k)
    exact Algebra.FinitePresentation.trans ℤ k _
  have hE : Algebra.Etale ℤ (Localization.Away ((m.natAbs : ℕ) : k)) :=
    Algebra.Etale.of_formallyUnramified_of_flat
  have h2 : Int.castRingHom (Localization.Away ((m.natAbs : ℕ) : k)) =
      algebraMap ℤ (Localization.Away ((m.natAbs : ℕ) : k)) := RingHom.ext_int _ _
  rw [h2, RingHom.etale_algebraMap]
  exact hE

end GlobalTheory.CompanionTheory.CommAlg.OrderEtale
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EtaleOverIntegersLocalizationStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_over_integers_localization : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k], ∃ N : ℕ, N ≠ 0 ∧ (Int.castRingHom (Localization.Away (N : k))).Etale := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.OrderEtale.exists_etale_away | exact GlobalTheory.CompanionTheory.CommAlg.OrderEtale.exists_etale_away | (intros; apply GlobalTheory.CompanionTheory.CommAlg.OrderEtale.exists_etale_away <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChernIntegrableOnIffSheets
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChernPartSheetImageEq
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAlgChartOverIntegers
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAlgChartOverIntegers
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

private theorem valR_restrict_eq_valR {A : Type} [CommRing A] {X : Scheme.{0}} (y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A ⟶ X)
    {U V : X.Opens} (hVU : V ≤ U) (h : ⊤ ≤ (TopologicalSpace.Opens.map y.base).obj V)
    (f : X.presheaf.obj (Opposite.op U)) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR y V ((X.presheaf.map (homOfLE hVU).op).hom f) =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR y U f := by
  have hU : ⊤ ≤ (TopologicalSpace.Opens.map y.base).obj U := h.trans (fun z hz => hVU hz)
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR
  rw [dite_eq_left h, dite_eq_left hU]
  congr 1
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, AlgebraicGeometry.Scheme.Hom.map_appLE]

private theorem isUnit_natCast_sp_complex_sections (N : ℕ) (hN : N ≠ 0) (W : (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ).Opens) :
    IsUnit (N : (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ).presheaf.obj (Opposite.op W)) := by
  have h1 : IsUnit (N : ℂ) := IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hN)
  have h2 := h1.map
    (((ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom.comp
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom)
  simpa only [map_natCast] using h2

private theorem etale_eval2Hom_basicOpen {k : Type} [CommRing k] {X : Scheme.{0}} {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) (N : ℕ)
    (hNet : (Int.castRingHom (Localization.Away (N : k))).Etale)
    (φ : k →+* X.presheaf.obj (Opposite.op U)) {D : ℕ} (x : Fin D → X.presheaf.obj (Opposite.op U))
    (hx : (MvPolynomial.eval₂Hom φ x).Etale) :
    (MvPolynomial.eval₂Hom
      (Int.castRingHom (X.presheaf.obj (Opposite.op (X.basicOpen (N : X.presheaf.obj (Opposite.op U))))))
      (fun a => algebraMap (X.presheaf.obj (Opposite.op U))
        (X.presheaf.obj (Opposite.op (X.basicOpen (N : X.presheaf.obj (Opposite.op U))))) (x a))).Etale := by
  haveI := hU.isLocalization_basicOpen (N : X.presheaf.obj (Opposite.op U))
  have hres : (algebraMap (X.presheaf.obj (Opposite.op U))
      (X.presheaf.obj (Opposite.op (X.basicOpen (N : X.presheaf.obj (Opposite.op U)))))).Etale :=
    RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway (N : X.presheaf.obj (Opposite.op U)))
  have hcomp : ((algebraMap (X.presheaf.obj (Opposite.op U))
      (X.presheaf.obj (Opposite.op (X.basicOpen (N : X.presheaf.obj (Opposite.op U)))))).comp
        (MvPolynomial.eval₂Hom φ x)).Etale :=
    RingHom.Etale.stableUnderComposition (MvPolynomial.eval₂Hom φ x) (algebraMap _ _) hx hres
  rw [MvPolynomial.comp_eval₂Hom] at hcomp
  have hunit : IsUnit
      ((N : X.presheaf.obj (Opposite.op (X.basicOpen (N : X.presheaf.obj (Opposite.op U)))))) := by
    simpa only [map_natCast] using
      IsLocalization.Away.algebraMap_isUnit
        (S := X.presheaf.obj (Opposite.op (X.basicOpen (N : X.presheaf.obj (Opposite.op U)))))
        (N : X.presheaf.obj (Opposite.op U))
  exact (GlobalTheory.T.etale_polynomial_base_change_iff k _ N hNet _ hunit D _).mp hcomp

theorem algChart_toZ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) (D : ℕ) (c : AlgChart p σ D) :
    ∃ c' : AlgChart t τ D, c'.e.source = sheet t τ '' c.e.source ∧ ∀ y ∈ c.e.source, c'.e (sheet t τ y) = c.e y := by
  classical
  obtain ⟨N, hN0, hNet⟩ := GlobalTheory.T.etale_over_integers_localization k
  obtain ⟨hemb, -⟩ := GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ
  haveI : Nonempty (GlobalTheory.CxPts p σ) := ⟨c.e.symm (0 : EuclideanSpace ℂ (Fin D))⟩
  obtain ⟨E, hE, hEs, hEt⟩ : ∃ E : OpenPartialHomeomorph (GlobalTheory.CxPts p σ) (GlobalTheory.CxPts t τ),
      ⇑E = sheet t τ ∧ E.source = Set.univ ∧ E.target = Set.range (sheet t τ) :=
    ⟨_, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply _ hemb,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source _ hemb,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target _ hemb⟩
  have hleft : ∀ y : GlobalTheory.CxPts p σ, E.symm (sheet t τ y) = y := by
    intro y
    have h := E.left_inv (x := y) (by rw [hEs]; trivial)
    rwa [hE] at h
  have hsrc : (E.symm.trans c.e).source = sheet t τ '' c.e.source := by
    ext z
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, hEt]
    constructor
    · rintro ⟨⟨y, rfl⟩, hy⟩
      exact ⟨y, by simpa [Set.mem_preimage, hleft] using hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, rfl⟩, by simpa [Set.mem_preimage, hleft] using hy⟩
  have hin : ∀ y ∈ c.e.source, ⊤ ≤ (TopologicalSpace.Opens.map (y.1).base).obj
      (X.basicOpen (N : X.presheaf.obj (Opposite.op c.U))) := by
    intro y hy
    rw [AlgebraicGeometry.Scheme.preimage_basicOpen, AlgebraicGeometry.Scheme.basicOpen_of_isUnit]
    · exact c.source_subset hy
    · rw [map_natCast]
      exact isUnit_natCast_sp_complex_sections N hN0 _
  have het := etale_eval2Hom_basicOpen c.affine N hNet (algX p c.U) c.x c.etale
  refine ⟨⟨E.symm.trans c.e, X.basicOpen (N : X.presheaf.obj (Opposite.op c.U)),
      c.affine.basicOpen _, fun a => algebraMap (X.presheaf.obj (Opposite.op c.U)) _ (c.x a),
      ?_, ?_, ?_, ?_⟩, hsrc, ?_⟩
  · have hZ : algX t (X.basicOpen (N : X.presheaf.obj (Opposite.op c.U))) =
        Int.castRingHom _ := RingHom.ext_int _ _
    rw [hZ]
    exact het
  · intro z hz
    rw [hsrc] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact hin y hy
  · intro z hz a
    rw [hsrc] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hleft, c.apply_eq y hy a]
    exact (valR_restrict_eq_valR y.1 (X.basicOpen_le _) (hin y hy) (c.x a)).symm
  · intro W f
    rw [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.coe_trans_symm,
      OpenPartialHomeomorph.symm_symm, hE, OpenPartialHomeomorph.symm_target, hEs]
    refine ((c.holo W f).mono ?_).congr ?_
    · rintro v ⟨⟨hv1, -⟩, hv2⟩
      exact ⟨hv1, hv2⟩
    · intro v _
      rfl
  · intro y hy
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hleft]

end GlobalTheory.CompanionTheory.Ar.BaseZ
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAlgChartOverIntegersStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algChart_over_integers : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) (D : ℕ) (c : AlgChart p σ D), ∃ c' : AlgChart t τ D, c'.e.source = sheet t τ '' c.e.source ∧ ∀ y ∈ c.e.source, c'.e (sheet t τ y) = c.e y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BaseZ.algChart_toZ | exact GlobalTheory.CompanionTheory.Ar.BaseZ.algChart_toZ | (intros; apply GlobalTheory.CompanionTheory.Ar.BaseZ.algChart_toZ <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAlgChartFromIntegers
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAlgChartFromIntegers
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.CompanionTheory.Ar.BaseZ.ChartDown

theorem etale_res_int {X : Scheme.{0}} (t : X ⟶ Sp ℤ) {U : X.Opens} (hU : IsAffineOpen U) (n : Γ(X, U))
    {D : ℕ} (x : Fin D → Γ(X, U)) (h : (MvPolynomial.eval₂Hom (algX t U) x).Etale) :
    (MvPolynomial.eval₂Hom (Int.castRingHom Γ(X, X.basicOpen n))
      fun a => resG X (X.basicOpen_le n) (x a)).Etale := by
  have hloc := hU.isLocalization_basicOpen n
  have hres : (resG X (X.basicOpen_le n)).Etale :=
    RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway n)
  have hcomp := RingHom.Etale.stableUnderComposition _ _ h hres
  rw [MvPolynomial.comp_eval₂Hom] at hcomp
  rwa [show (resG X (X.basicOpen_le n)).comp (algX t U) = Int.castRingHom _ from RingHom.ext_int _ _] at hcomp

theorem isUnit_natCast_basicOpen {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (N : ℕ) :
    IsUnit (N : Γ(X, X.basicOpen (N : Γ(X, U)))) := by
  have hloc := hU.isLocalization_basicOpen (N : Γ(X, U))
  have := IsLocalization.Away.algebraMap_isUnit (S := Γ(X, X.basicOpen (N : Γ(X, U)))) (N : Γ(X, U))
  simpa using this

theorem mem_ptsIn_basicOpen_natCast {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {U : X.Opens} {N : ℕ} (hN : N ≠ 0) {y : CxPts p σ} (hy : y ∈ ptsIn p σ U) :
    y ∈ ptsIn p σ (X.basicOpen (N : Γ(X, U))) := by
  refine (mem_ptsIn_basicOpen hy _).2 ?_
  have h := ev_algX hy (N : k)
  rw [map_natCast, map_natCast] at h
  rw [h]
  exact_mod_cast hN

end GlobalTheory.CompanionTheory.Ar.BaseZ.ChartDown


open GlobalTheory.CompanionTheory.Ar.BaseZ.ChartDown in
theorem GlobalTheory.CompanionTheory.Ar.BaseZ.exists_chart_sheet : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) (D : ℕ) (c' : AlgChart t τ D), Nonempty (CxPts p σ) → ∃ c : AlgChart p σ D, c.e.source = sheet t τ ⁻¹' c'.e.source ∧ ∀ y ∈ c.e.source, c'.e (sheet t τ y) = c.e y := by
  intro k _ _ _ _ X p t τ σ D c' hne
  obtain ⟨N, hN0, hN⟩ := GlobalTheory.T.etale_over_integers_localization k
  obtain ⟨hemb, -⟩ := GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ
  have hle := X.basicOpen_le (N : Γ(X, c'.U))
  have hetZ := etale_res_int t c'.affine (N : Γ(X, c'.U)) c'.x c'.etale
  have hetk := (GlobalTheory.T.etale_polynomial_base_change_iff k _ N hN (algX p (X.basicOpen (N : Γ(X, c'.U))))
    (isUnit_natCast_basicOpen c'.affine N) D _).2 hetZ
  let s := IsOpenEmbedding.toOpenPartialHomeomorph (sheet t τ : CxPts p σ → CxPts t τ) hemb
  have hs : (s : CxPts p σ → CxPts t τ) = sheet t τ := IsOpenEmbedding.toOpenPartialHomeomorph_apply _ hemb
  have hss : s.source = Set.univ := IsOpenEmbedding.toOpenPartialHomeomorph_source _ hemb
  have hst : s.target = Set.range (sheet t τ : CxPts p σ → CxPts t τ) :=
    IsOpenEmbedding.toOpenPartialHomeomorph_target _ hemb
  have hsrc : (s.trans c'.e).source = sheet t τ ⁻¹' c'.e.source := by
    rw [OpenPartialHomeomorph.trans_source, hss, Set.univ_inter, hs]
  have happ : ∀ y, (s.trans c'.e) y = c'.e (sheet t τ y) := fun y => by
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hs]
  have hsym : ∀ v ∈ (s.trans c'.e).target, sheet t τ ((s.trans c'.e).symm v) = c'.e.symm v := by
    intro v hv
    rw [OpenPartialHomeomorph.trans_target] at hv
    have h2 : c'.e.symm v ∈ s.target := hv.2
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.coe_trans,
      Function.comp_apply, ← hs]
    exact s.right_inv h2
  refine ⟨{ e := s.trans c'.e
            U := X.basicOpen (N : Γ(X, c'.U))
            affine := c'.affine.basicOpen _
            x := fun a => resG X hle (c'.x a)
            etale := hetk
            source_subset := ?_
            apply_eq := ?_
            holo := ?_ }, hsrc, fun y _ => (happ y).symm⟩
  · intro y hy
    rw [hsrc] at hy
    have h1 : sheet t τ y ∈ ptsIn t τ c'.U := c'.source_subset hy
    exact mem_ptsIn_basicOpen_natCast hN0 (show y ∈ ptsIn p σ c'.U from h1)
  · intro y hy a
    rw [hsrc] at hy
    have h1 : sheet t τ y ∈ ptsIn t τ c'.U := c'.source_subset hy
    have hB := mem_ptsIn_basicOpen_natCast hN0 (show y ∈ ptsIn p σ c'.U from h1)
    rw [happ, c'.apply_eq _ hy a, ev_res hle hB]
    rfl
  · intro W f
    refine ((c'.holo W f).mono ?_).congr ?_
    · rintro v ⟨hv, hw⟩
      refine ⟨?_, ?_⟩
      · rw [OpenPartialHomeomorph.trans_target] at hv
        exact hv.1
      · show c'.e.symm v ∈ ptsIn t τ W
        rw [← hsym v hv]
        exact hw
    · rintro v ⟨hv, -⟩
      show ev p σ W f _ = ev t τ W f (c'.e.symm v)
      rw [← hsym v hv]
      rfl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAlgChartFromIntegersStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algChart_from_integers : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) (D : ℕ) (c' : AlgChart t τ D), Nonempty (CxPts p σ) → ∃ c : AlgChart p σ D, c.e.source = sheet t τ ⁻¹' c'.e.source ∧ ∀ y ∈ c.e.source, c'.e (sheet t τ y) = c.e y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BaseZ.exists_chart_sheet | exact GlobalTheory.CompanionTheory.Ar.BaseZ.exists_chart_sheet | (intros; apply GlobalTheory.CompanionTheory.Ar.BaseZ.exists_chart_sheet <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChernDensitySheetEq
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChernDensitySheetEq
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ZDens

theorem chernDens_sheet : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) (D : ℕ) (B : LB X) (φ : ∀ σ : k →+* ℂ, Weight p σ B) (ψ : Weight t τ B), WOver φ ψ → (∀ σ, (φ σ).IsCInf) → ψ.IsCInf → ∀ (c : AlgChart p σ D) (c' : AlgChart t τ D), (∀ y ∈ c.e.source, sheet t τ y ∈ c'.e.source ∧ c'.e (sheet t τ y) = c.e y) → ∀ y ∈ c.e.source, c'.chernDens ψ (sheet t τ y) = c.chernDens (φ σ) y := by
  intro k _ _ _ _ X p t τ σ D B φ ψ hW hφ hψ c c' hm y hy
  obtain ⟨hy', he⟩ := hm y hy
  have hi := GlobalTheory.CxPts.mem_pick (φ σ).isLB y
  set i := GlobalTheory.CxPts.pick (φ σ).isLB y
  have hi' : sheet t τ y ∈ ptsIn t τ (B.U i) := hi
  rw [c'.chernDens_eq hψ hy' hi', c.chernDens_eq (hφ σ) hy hi, AlgChart.hess, AlgChart.hess, he]
  have ho := GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i))
  have hmem := GlobalTheory.ChartGlue.mem_over c.e hy hi
  have e : (fun v => ((ψ.φ i (c'.e.symm v) : ℝ) : ℂ)) =ᶠ[𝓝 (c.e y)]
      fun v => (((φ σ).φ i (c.e.symm v) : ℝ) : ℂ) := by
    filter_upwards [ho.mem_nhds hmem] with v hv
    have hw := c.e.map_target hv.1
    obtain ⟨h₁, h₂⟩ := hm _ hw
    have hs : c'.e.symm v = sheet t τ (c.e.symm v) := by
      rw [← c'.e.left_inv h₁, h₂, c.e.right_inv hv.1]
    rw [hs, hW σ i _ hv.2]
  rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e]

end GlobalTheory.CompanionTheory.Ar.ZDens
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChernDensitySheetEqStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernDensity_sheet_eq : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) (D : ℕ) (B : LB X) (φ : ∀ σ : k →+* ℂ, Weight p σ B) (ψ : Weight t τ B), WOver φ ψ → (∀ σ, (φ σ).IsCInf) → ψ.IsCInf → ∀ (c : AlgChart p σ D) (c' : AlgChart t τ D), (∀ y ∈ c.e.source, sheet t τ y ∈ c'.e.source ∧ c'.e (sheet t τ y) = c.e y) → ∀ y ∈ c.e.source, c'.chernDens ψ (sheet t τ y) = c.chernDens (φ σ) y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ZDens.chernDens_sheet | exact GlobalTheory.CompanionTheory.Ar.ZDens.chernDens_sheet | (intros; apply GlobalTheory.CompanionTheory.Ar.ZDens.chernDens_sheet <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChernPartSheetImageEq
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem GlobalTheory.CompanionTheory.Ar.BaseZ.chernPart_sheet : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ), IsProjOver p → ∀ (σ : k →+* ℂ) (D : ℕ) (B : LB X) (φ : ∀ σ : k →+* ℂ, Weight p σ B) (ψ : Weight t τ B), WOver φ ψ → (∀ σ, (φ σ).IsCInf) → ψ.IsCInf → ∀ (ε : ℤˣ) (S : Set (CxPts p σ)), MeasurableSet S → ψ.chernPart D ε (sheet t τ '' S) = (φ σ).chernPart D ε S := by
  intro k _ _ _ _ X p t τ hp σ D B φ ψ hW hφ hψ ε S hS
  have hSC : ∀ σ' : k →+* ℂ, SecondCountableTopology (CxPts p σ') := by
    obtain ⟨N, i, hi, hpe⟩ := hp
    intro σ'
    haveI := hi
    subst hpe
    exact GlobalTheory.CxPts.secondCountableTopology _ σ'
  haveI hscp : SecondCountableTopology (CxPts p σ) := hSC σ
  haveI hsct : SecondCountableTopology (CxPts t τ) := by
    haveI : Finite (k →+* ℂ) := Sheet.finite_ringHom k
    have hopen : ∀ σ' : k →+* ℂ, IsOpen (Set.range (sheet t τ : CxPts p σ' → CxPts t τ)) :=
      fun σ' => (GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ').1.isOpen_range
    haveI : ∀ σ' : k →+* ℂ,
        SecondCountableTopology (Set.range (sheet t τ : CxPts p σ' → CxPts t τ)) := by
      intro σ'
      haveI := hSC σ'
      exact (GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ').1.isEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
    refine TopologicalSpace.secondCountableTopology_of_countable_cover hopen ?_
    exact Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 ⟨emb p y, unsheet p y, sheet_unsheet p y⟩
  have hemb : Topology.IsOpenEmbedding (sheet t τ : CxPts p σ → CxPts t τ) :=
    (GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ).1
  have hme : MeasurableEmbedding (sheet t τ : CxPts p σ → CxPts t τ) :=
    hemb.measurableEmbedding
  have key : ∀ (c : AlgChart p σ D) (A : Set (CxPts p σ)), MeasurableSet A → A ⊆ c.e.source →
      ψ.chernPart D ε (sheet t τ '' A) = (φ σ).chernPart D ε A := by
    intro c A hA hAc
    obtain ⟨c', hc's, hc'e⟩ := GlobalTheory.T.exists_algChart_over_integers k X p t τ σ D c
    have hcomp : ∀ y ∈ c.e.source, sheet t τ y ∈ c'.e.source ∧ c'.e (sheet t τ y) = c.e y :=
      fun y hy => ⟨hc's ▸ Set.mem_image_of_mem _ hy, hc'e y hy⟩
    have hdens := GlobalTheory.T.chernDensity_sheet_eq k X p t τ σ D B φ ψ hW hφ hψ c c' hcomp
    have hA' : sheet t τ '' A ⊆ c'.e.source := by
      rintro _ ⟨y, hy, rfl⟩
      exact (hcomp y (hAc hy)).1
    rw [GlobalTheory.Weight.chernPart_apply hψ ε c' (hme.measurableSet_image' hA) hA',
      GlobalTheory.Weight.chernPart_apply (hφ σ) ε c hA hAc]
    have himg : c'.e '' (sheet t τ '' A) = c.e '' A := by
      rw [Set.image_image]
      exact Set.image_congr fun y hy => (hcomp y (hAc hy)).2
    rw [himg]
    refine MeasureTheory.setLIntegral_congr_fun (GlobalTheory.ChartGlue.measurableSet_image c.e hA hAc) ?_
    rintro _ ⟨y, hy, rfl⟩
    dsimp only
    have h1 : c.e.symm (c.e y) = y := c.e.left_inv (hAc hy)
    have h2 : c'.e.symm (c.e y) = sheet t τ y := by
      rw [← (hcomp y (hAc hy)).2]
      exact c'.e.left_inv (hcomp y (hAc hy)).1
    rw [h1, h2, hdens y (hAc hy)]
  have hμA : ∀ A : Set (CxPts p σ),
      Measure.comap (sheet t τ) (ψ.chernPart D ε) A = ψ.chernPart D ε (sheet t τ '' A) :=
    fun A => hme.comap_apply _ A
  have hUo : IsOpen (⋃ c : AlgChart p σ D, c.e.source) := isOpen_iUnion fun c => c.e.open_source
  have hUm : MeasurableSet (⋃ c : AlgChart p σ D, c.e.source) := hUo.measurableSet
  have hzν : ((φ σ).chernPart D ε).restrict (⋃ c : AlgChart p σ D, c.e.source)ᶜ = 0 := by
    refine Measure.restrict_eq_zero.2 (GlobalTheory.Weight.chernPart_eq_zero ε hUm.compl fun c => ?_)
    rw [Set.disjoint_left]
    intro y hy hy'
    exact hy' (Set.mem_iUnion.2 ⟨c, hy⟩)
  have hzμ : (Measure.comap (sheet t τ) (ψ.chernPart D ε)).restrict
      (⋃ c : AlgChart p σ D, c.e.source)ᶜ = 0 := by
    refine Measure.restrict_eq_zero.2 ?_
    rw [hμA]
    refine GlobalTheory.Weight.chernPart_eq_zero ε (hme.measurableSet_image' hUm.compl) fun c' => ?_
    rw [Set.disjoint_left]
    rintro _ hz ⟨y, hy, rfl⟩
    obtain ⟨c, hcs, -⟩ := GlobalTheory.T.exists_algChart_from_integers k X p t τ σ D c' ⟨y⟩
    exact hy (Set.mem_iUnion.2 ⟨c, by rw [hcs]; exact hz⟩)
  have hU : (Measure.comap (sheet t τ) (ψ.chernPart D ε)).restrict
      (⋃ c : AlgChart p σ D, c.e.source) = ((φ σ).chernPart D ε).restrict
      (⋃ c : AlgChart p σ D, c.e.source) := by
    obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun c : AlgChart p σ D => c.e.source) fun c => c.e.open_source
    have hU' : (⋃ c : AlgChart p σ D, c.e.source) = ⋃ c : T, (c : AlgChart p σ D).e.source := by
      rw [Set.iUnion_subtype]
      exact hTU.symm
    haveI : Countable T := hTc.to_subtype
    rw [hU', Measure.restrict_iUnion_congr]
    intro c
    ext A hA
    have hAm : MeasurableSet (A ∩ (c : AlgChart p σ D).e.source) :=
      hA.inter (c : AlgChart p σ D).e.open_source.measurableSet
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA, hμA]
    exact key c _ hAm Set.inter_subset_right
  have hμν : Measure.comap (sheet t τ) (ψ.chernPart D ε) = (φ σ).chernPart D ε := by
    calc Measure.comap (sheet t τ) (ψ.chernPart D ε)
        = (Measure.comap (sheet t τ) (ψ.chernPart D ε)).restrict (⋃ c : AlgChart p σ D, c.e.source)
          + (Measure.comap (sheet t τ) (ψ.chernPart D ε)).restrict
            (⋃ c : AlgChart p σ D, c.e.source)ᶜ := (Measure.restrict_add_restrict_compl hUm).symm
      _ = ((φ σ).chernPart D ε).restrict (⋃ c : AlgChart p σ D, c.e.source)
          + ((φ σ).chernPart D ε).restrict (⋃ c : AlgChart p σ D, c.e.source)ᶜ := by
        rw [hU, hzμ, hzν]
      _ = (φ σ).chernPart D ε := Measure.restrict_add_restrict_compl hUm
  rw [← hμA, hμν]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChernPartSheetImageEqStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernPart_sheet_image_eq : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ), IsProjOver p → ∀ (σ : k →+* ℂ) (D : ℕ) (B : LB X) (φ : ∀ σ : k →+* ℂ, Weight p σ B) (ψ : Weight t τ B), WOver φ ψ → (∀ σ, (φ σ).IsCInf) → ψ.IsCInf → ∀ (ε : ℤˣ) (S : Set (CxPts p σ)), MeasurableSet S → ψ.chernPart D ε (sheet t τ '' S) = (φ σ).chernPart D ε S := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BaseZ.chernPart_sheet | exact GlobalTheory.CompanionTheory.Ar.BaseZ.chernPart_sheet | (intros; apply GlobalTheory.CompanionTheory.Ar.BaseZ.chernPart_sheet <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegrableOnAndSetIntegralOfEmbeddings
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Metric

theorem measure_eq_sum_map_of_embeddings {α : Type} [Fintype α] {Y : Type} [MeasurableSpace Y]
    {Z : α → Type} [∀ a, MeasurableSpace (Z a)] {s : ∀ a, Z a → Y}
    (hs : ∀ a, MeasurableEmbedding (s a)) (hu : ∀ y, ∃! a, y ∈ Set.range (s a))
    {ν : Measure Y} {μ : ∀ a, Measure (Z a)}
    (hν : ∀ a (S : Set (Z a)), MeasurableSet S → ν (s a '' S) = μ a S) :
    ν = ∑ a, Measure.map (s a) (μ a) := by
  ext T hT
  rw [Measure.finsetSum_apply]
  have hcover : T = ⋃ a, T ∩ Set.range (s a) := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hy
      obtain ⟨a, ha, -⟩ := hu y
      exact ⟨a, hy, ha⟩
    · rintro ⟨a, hy, -⟩
      exact hy
  have hdisj : Pairwise (Function.onFun Disjoint fun a => T ∩ Set.range (s a)) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    rintro y ⟨-, hya⟩ ⟨-, hyb⟩
    obtain ⟨a', -, ha'⟩ := hu y
    exact hab ((ha' a hya).trans (ha' b hyb).symm)
  have hmeas : ∀ a, MeasurableSet (T ∩ Set.range (s a)) := fun a =>
    hT.inter (hs a).measurableSet_range
  rw [show ν T = ν (⋃ a, T ∩ Set.range (s a)) by rw [← hcover], measure_iUnion hdisj hmeas,
    tsum_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [(hs a).map_apply, ← hν a _ ((hs a).measurable hT), Set.image_preimage_eq_inter_range]

theorem integrableOn_and_setIntegral_of_embeddings :
    ∀ (α : Type) [Finite α] (Y : Type) [MeasurableSpace Y] (Z : α → Type)
      [∀ a, MeasurableSpace (Z a)] (s : ∀ a, Z a → Y), (∀ a, MeasurableEmbedding (s a)) →
      (∀ y, ∃! a, y ∈ Set.range (s a)) → ∀ (ν : Measure Y) (μ : ∀ a, Measure (Z a)),
      (∀ a (S : Set (Z a)), MeasurableSet S → ν (s a '' S) = μ a S) →
      ∀ (S : Set Y), MeasurableSet S → ∀ f : Y → ℝ,
      (IntegrableOn f S ν ↔ ∀ a, IntegrableOn (fun z => f (s a z)) (s a ⁻¹' S) (μ a)) ∧
      (IntegrableOn f S ν →
        ∫ y in S, f y ∂ν = ∑ᶠ a, ∫ z in s a ⁻¹' S, f (s a z) ∂(μ a)) := by
  intro α _ Y _ Z _ s hs hu ν μ hν S hS f
  haveI := Fintype.ofFinite α
  have hνeq := measure_eq_sum_map_of_embeddings hs hu hν
  have hres : ν.restrict S = ∑ a, (Measure.map (s a) (μ a)).restrict S := by
    ext T hT
    rw [hνeq, Measure.restrict_apply hT, Measure.finsetSum_apply, Measure.finsetSum_apply]
    simp only [Measure.restrict_apply hT]
  have hint : IntegrableOn f S ν ↔ ∀ a, IntegrableOn (fun z => f (s a z)) (s a ⁻¹' S) (μ a) := by
    rw [IntegrableOn, hres, integrable_finsetSum_measure]
    simp only [Finset.mem_univ, forall_const]
    exact forall_congr' fun a => (hs a).integrableOn_map_iff
  refine ⟨hint, fun hf => ?_⟩
  have hf' : ∀ a ∈ Finset.univ, Integrable f ((Measure.map (s a) (μ a)).restrict S) := fun a _ =>
    (hs a).integrableOn_map_iff.mpr (hint.mp hf a)
  rw [finsum_eq_sum_of_fintype, hres, integral_finsetSum_measure hf']
  exact Finset.sum_congr rfl fun a _ => (hs a).setIntegral_map _ _

end GlobalTheory.CompanionTheory.Metric
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChernIntegrableOnIffSheets
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Metric

theorem chernInt_eq_finsum_sheets : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ), IsProjOver p → ∀ (D : ℕ) (B : LB X) (φ : ∀ σ : k →+* ℂ, Weight p σ B) (ψ : Weight t τ B), WOver φ ψ → (∀ σ, (φ σ).IsCInf) → ψ.IsCInf → ∀ (S : Set (CxPts t τ)), MeasurableSet S → ∀ f : CxPts t τ → ℝ, (ψ.ChernIntegrableOn D S f ↔ ∀ σ, (φ σ).ChernIntegrableOn D (sheet t τ ⁻¹' S) (fun z => f (sheet t τ z))) ∧ (ψ.ChernIntegrableOn D S f → ψ.chernInt D S f = ∑ᶠ σ, (φ σ).chernInt D (sheet t τ ⁻¹' S) (fun z => f (sheet t τ z))) := by
  intro k _ _ _ _ X p t τ hP D B φ ψ hW hφ hψ S hS f
  have hemb : ∀ σ : k →+* ℂ, MeasurableEmbedding (sheet (p := p) (σ := σ) t τ) := fun σ =>
    (GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ).1.measurableEmbedding
  have huniq : ∀ y : CxPts t τ, ∃! σ : k →+* ℂ, y ∈ Set.range (sheet (p := p) (σ := σ) t τ) := by
    intro y
    refine ⟨emb p y, ?_, ?_⟩
    · show y ∈ Set.range (sheet (p := p) (σ := emb p y) t τ)
      rw [(GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ _).2]
      rfl
    · intro σ hσ
      rw [(GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ).2] at hσ
      exact hσ.symm
  have hfin : Finite (k →+* ℂ) := Sheet.finite_ringHom k
  have key := fun ε : ℤˣ => integrableOn_and_setIntegral_of_embeddings (k →+* ℂ) (CxPts t τ)
    (fun σ => CxPts p σ) (fun σ => sheet (p := p) (σ := σ) t τ) hemb huniq (ψ.chernPart D ε)
    (fun σ => (φ σ).chernPart D ε) (fun σ S' hS' => GlobalTheory.T.chernPart_sheet_image_eq k X p t τ hP σ D B φ ψ hW hφ hψ ε S' hS') S hS f
  obtain ⟨h1, h1'⟩ := key 1
  obtain ⟨h2, h2'⟩ := key (-1)
  refine ⟨?_, ?_⟩
  · simp only [GlobalTheory.Weight.ChernIntegrableOn]
    rw [h1, h2]
    exact forall_and.symm
  · intro hI
    simp only [GlobalTheory.Weight.chernInt]
    rw [h1' hI.1, h2' hI.2, finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)]

end GlobalTheory.CompanionTheory.Metric
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChernIntegrableOnIffSheetsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernIntegrableOn_iff_sheets : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ), IsProjOver p → ∀ (D : ℕ) (B : LB X) (φ : ∀ σ : k →+* ℂ, Weight p σ B) (ψ : Weight t τ B), WOver φ ψ → (∀ σ, (φ σ).IsCInf) → ψ.IsCInf → ∀ (S : Set (CxPts t τ)), MeasurableSet S → ∀ f : CxPts t τ → ℝ, (ψ.ChernIntegrableOn D S f ↔ ∀ σ, (φ σ).ChernIntegrableOn D (sheet t τ ⁻¹' S) (fun z => f (sheet t τ z))) ∧ (ψ.ChernIntegrableOn D S f → ψ.chernInt D S f = ∑ᶠ σ, (φ σ).chernInt D (sheet t τ ⁻¹' S) (fun z => f (sheet t τ z))) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.chernInt_eq_finsum_sheets | exact GlobalTheory.CompanionTheory.Metric.chernInt_eq_finsum_sheets | (intros; apply GlobalTheory.CompanionTheory.Metric.chernInt_eq_finsum_sheets <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchIntegrableIffOverIntegers
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

private theorem chernIntegrableOn_and_chernInt_congr {k : Type} [CommRing k] {Y : Scheme} {q : Y ⟶ Sp k} {σ : k →+* ℂ}
    {B : ReciprocityTheory.ChartRestriction.G.Semi.LB Y} (φ : GlobalTheory.Weight q σ B) (d : ℕ) {S : Set (GlobalTheory.CxPts q σ)}
    (hS : MeasurableSet S) {f g : GlobalTheory.CxPts q σ → ℝ} (h : Set.EqOn f g S) :
    (φ.ChernIntegrableOn d S f ↔ φ.ChernIntegrableOn d S g) ∧ φ.chernInt d S f = φ.chernInt d S g := by
  refine ⟨?_, ?_⟩
  · unfold GlobalTheory.Weight.ChernIntegrableOn
    rw [integrableOn_congr_fun h hS, integrableOn_congr_fun h hS]
  · unfold GlobalTheory.Weight.chernInt
    rw [setIntegral_congr_fun hS h, setIntegral_congr_fun hS h]

theorem archInt_over_int : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (D : ℕ), IsArithVar p D → ∀ (N M : HermLB p) (ψ : Weight t τ N.B) (ν : Weight t τ M.B), WOver N.φ ψ → WOver M.φ ν → ψ.IsCInf → ∀ (e : ℕ) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), (ψ.ChernIntegrableOn e (offSupp t τ (M.div hr)) (logNorm ν r) ↔ N.ArchIntegrable M e hr) ∧ (N.ArchIntegrable M e hr → ψ.chernInt e (offSupp t τ (M.div hr)) (logNorm ν r) = N.archInt M e hr) := by
  intro k _ X _ p t τ D hX N M ψ ν hψN hνM hψ e r hr
  by_cases hσ : Nonempty (k →+* ℂ)
  · obtain ⟨σ₀⟩ := hσ
    haveI : CharZero k := σ₀.charZero
    haveI := hX.isDomain
    haveI := hX.finite
    have hS : MeasurableSet (offSupp t τ (M.div hr)) := (GlobalTheory.CxPts.isOpen_ptsIn _).measurableSet
    obtain ⟨h1, h2⟩ := GlobalTheory.T.chernIntegrableOn_iff_sheets k X p t τ hX.isProjOver e N.B N.φ ψ hψN N.cInf hψ _ hS (logNorm ν r)
    have hmeas : ∀ σ : k →+* ℂ, MeasurableSet (offSupp p σ (M.div hr)) :=
      fun σ => (GlobalTheory.CxPts.isOpen_ptsIn _).measurableSet
    have hEq : ∀ σ : k →+* ℂ, Set.EqOn (fun z => logNorm ν r (GlobalTheory.CompanionTheory.Ar.BaseZ.sheet t τ z))
        (logNorm (M.φ σ) r) (offSupp p σ (M.div hr)) :=
      fun σ y hy => GlobalTheory.T.logNorm_sheet_eq k X p t τ M.B M.φ ν hνM r hr σ y hy
    have hiff : ψ.ChernIntegrableOn e (offSupp t τ (M.div hr)) (logNorm ν r) ↔ N.ArchIntegrable M e hr := by
      rw [h1]
      unfold GlobalTheory.HermLB.ArchIntegrable
      exact forall_congr' fun σ => (chernIntegrableOn_and_chernInt_congr (N.φ σ) e (hmeas σ) (hEq σ)).1
    refine ⟨hiff, fun hInt => ?_⟩
    rw [h2 (hiff.mpr hInt)]
    unfold GlobalTheory.HermLB.archInt
    exact finsum_congr fun σ => (chernIntegrableOn_and_chernInt_congr (N.φ σ) e (hmeas σ) (hEq σ)).2
  · have hE : IsEmpty (k →+* ℂ) := not_nonempty_iff.mp hσ
    haveI : IsEmpty (GlobalTheory.CxPts t τ) := ⟨fun y => hE.false (Spec.preimage (Subtype.val y ≫ p)).hom⟩
    have hS0 : offSupp t τ (M.div hr) = ∅ := Set.eq_empty_of_isEmpty _
    have hA : N.ArchIntegrable M e hr := by
      unfold GlobalTheory.HermLB.ArchIntegrable
      intro σ
      exact hE.elim σ
    refine ⟨⟨fun _ => hA, fun _ => ?_⟩, fun _ => ?_⟩
    · unfold GlobalTheory.Weight.ChernIntegrableOn
      rw [hS0]
      exact ⟨integrableOn_empty, integrableOn_empty⟩
    · unfold GlobalTheory.HermLB.archInt GlobalTheory.Weight.chernInt
      rw [hS0, finsum_of_isEmpty]
      simp

end GlobalTheory.CompanionTheory.Ar.BaseZ
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchIntegrableIffOverIntegersStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archIntegrable_iff_over_integers : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (D : ℕ), IsArithVar p D → ∀ (N M : HermLB p) (ψ : Weight t τ N.B) (ν : Weight t τ M.B), WOver N.φ ψ → WOver M.φ ν → ψ.IsCInf → ∀ (e : ℕ) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), (ψ.ChernIntegrableOn e (offSupp t τ (M.div hr)) (logNorm ν r) ↔ N.ArchIntegrable M e hr) ∧ (N.ArchIntegrable M e hr → ψ.chernInt e (offSupp t τ (M.div hr)) (logNorm ν r) = N.archInt M e hr) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BaseZ.archInt_over_int | exact GlobalTheory.CompanionTheory.Ar.BaseZ.archInt_over_int | (intros; apply GlobalTheory.CompanionTheory.Ar.BaseZ.archInt_over_int <;> assumption)
end
