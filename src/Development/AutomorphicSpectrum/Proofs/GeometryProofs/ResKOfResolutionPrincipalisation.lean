module

public import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.PrincipalizationOfPrincipalisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualTangentVectorsGenericFibreDetEqDetOmegaTrans

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSncCoordsOfLocal
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothLocalRingFreeDifferentials
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothLocalRingFreeDifferentials
noncomputable section

namespace GlobalTheory.CompanionTheory.ResKCoords

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

theorem kaehler_atPrime_of_away (K A : Type) [Field K] [CommRing A] [Algebra K A] (D : ℕ) (s : Set A)
    (hs : Ideal.span s = ⊤)
    (h : ∀ t ∈ s, Algebra.IsStandardSmoothOfRelativeDimension D K (Localization.Away t))
    (P : Ideal A) [P.IsPrime] :
    Module.Free (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
      Module.Finite (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
      Module.finrank (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] = D := by
  obtain ⟨t, ht, htP⟩ : ∃ t ∈ s, t ∉ P := by
    by_contra hc
    push_neg at hc
    exact (‹P.IsPrime›).ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 hc))
  have hle : Submonoid.powers t ≤ P.primeCompl := by
    rintro _ ⟨n, rfl⟩
    exact fun hm => htP (‹P.IsPrime›.mem_of_pow_mem n hm)
  letI : Algebra (Localization.Away t) (Localization.AtPrime P) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers t) P.primeCompl hle
  haveI : IsScalarTower A (Localization.Away t) (Localization.AtPrime P) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  haveI : IsScalarTower K (Localization.Away t) (Localization.AtPrime P) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply K A (Localization.Away t),
        ← IsScalarTower.algebraMap_apply A (Localization.Away t) (Localization.AtPrime P),
        ← IsScalarTower.algebraMap_apply K A (Localization.AtPrime P)]
  haveI := IsLocalization.isLocalization_of_submonoid_le (Localization.Away t) (Localization.AtPrime P)
    (Submonoid.powers t) P.primeCompl hle
  haveI : Algebra.FormallyEtale (Localization.Away t) (Localization.AtPrime P) :=
    Algebra.FormallyEtale.of_isLocalization
      (P.primeCompl.map (algebraMap A (Localization.Away t)))
  haveI := h t ht
  haveI : Nontrivial (Localization.Away t) :=
    (algebraMap (Localization.Away t) (Localization.AtPrime P)).domain_nontrivial
  haveI : Algebra.IsStandardSmooth K (Localization.Away t) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth D
  have r := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := K)
    (S := Localization.Away t) D
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (Localization.Away t)
    (Localization.AtPrime P)
  refine ⟨.of_equiv e, .equiv e, ?_⟩
  rw [← e.finrank_eq, Module.finrank_baseChange, Module.finrank, r]
  simp

theorem finitePresentation_of_away (K A : Type) [Field K] [CommRing A] [Algebra K A] (D : ℕ) (s : Set A)
    (hs : Ideal.span s = ⊤)
    (h : ∀ t ∈ s, Algebra.IsStandardSmoothOfRelativeDimension D K (Localization.Away t)) :
    Algebra.FinitePresentation K A := by
  refine RingHom.finitePresentation_algebraMap.1
    (RingHom.finitePresentation_ofLocalizationSpanTarget (algebraMap K A) s hs fun r => ?_)
  haveI := h r.1 r.2
  haveI : Algebra.IsStandardSmooth K (Localization.Away r.1) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth D
  rw [← IsScalarTower.algebraMap_eq K A (Localization.Away r.1)]
  exact (RingHom.finitePresentation_algebraMap).2 inferInstance

theorem finitePresentation_and_kaehler_atPrime :
    ∀ (K : Type) [Field K] (D : ℕ) (Y : Scheme.{0}) (g : Y ⟶ Sp K), SmoothOfRelativeDimension D g →
      ∀ (U : Y.affineOpens) (P : Ideal Γ(Y, U.1)) [P.IsPrime],
      letI := secAlgebra g U.1
      Algebra.FinitePresentation K Γ(Y, U.1) ∧
        Module.Free (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
        Module.Finite (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
        Module.finrank (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] = D := by
  intro K _ D Y g hg U P _
  letI := secAlgebra g U.1
  obtain ⟨s, hs, h'⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) g hg
    ⟨⊤, isAffineOpen_top _⟩ U (fun _ _ => trivial)
  have key : ∀ t ∈ s, Algebra.IsStandardSmoothOfRelativeDimension D K (Localization.Away t) := by
    intro t ht
    have h2 := (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := D)).2
      _ (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv (h' t ht)
    rw [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    rw [IsScalarTower.algebraMap_eq K Γ(Y, U.1) (Localization.Away t)]
    exact h2
  exact ⟨finitePresentation_of_away K _ D s hs key, kaehler_atPrime_of_away K _ D s hs key P⟩

end GlobalTheory.CompanionTheory.ResKCoords
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothLocalRingFreeDifferentialsStatement
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_local_ring_free_differentials : ∀ (K : Type) [Field K] (D : ℕ) (Y : Scheme.{0}) (g : Y ⟶ Sp K), SmoothOfRelativeDimension D g → ∀ (U : Y.affineOpens) (P : Ideal Γ(Y, U.1)) [P.IsPrime], letI := secAlgebra g U.1; Algebra.FinitePresentation K Γ(Y, U.1) ∧ Module.Free (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧ Module.Finite (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧ Module.finrank (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] = D := by
  first | exact @GlobalTheory.CompanionTheory.ResKCoords.finitePresentation_and_kaehler_atPrime | exact GlobalTheory.CompanionTheory.ResKCoords.finitePresentation_and_kaehler_atPrime | (intros; apply GlobalTheory.CompanionTheory.ResKCoords.finitePresentation_and_kaehler_atPrime <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.KaehlerBasisOnLocalizationAway
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.KaehlerBasisOnLocalizationAway
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

namespace GlobalTheory.CompanionTheory.Glob.ResKCoords

theorem isCoords_basicOpen_of_away :
    ∀ (K : Type) [Field K] (Y : Scheme.{0}) (g : Y ⟶ Sp K) (U : Y.affineOpens) (s : Γ(Y, U.1)) {n : ℕ}
      (x : Fin n → Γ(Y, U.1)),
      (letI := secAlgebra g U.1;
        ∀ (B : Type) [CommRing B] [Algebra Γ(Y, U.1) B] [Algebra K B] [IsScalarTower K Γ(Y, U.1) B]
          [IsLocalization.Away s B],
          LinearIndependent B (fun i => KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) ∧
            Submodule.span B (Set.range fun i =>
              KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) = ⊤) →
        IsCoords g (Y.basicOpen s) (fun i => Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op (x i)) := by
  intro K _ Y g U s n x h
  letI aU : Algebra K Γ(Y, U.1) := secAlgebra g U.1
  letI aB : Algebra K Γ(Y, Y.basicOpen s) := secAlgebra g (Y.basicOpen s)
  letI aUB : Algebra Γ(Y, U.1) Γ(Y, Y.basicOpen s) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op).hom.toAlgebra
  haveI tower : IsScalarTower K Γ(Y, U.1) Γ(Y, Y.basicOpen s) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appLE ⊤ (Y.basicOpen s) (fun _ _ => trivial)).hom = _
    have e : g.appLE ⊤ U.1 (fun _ _ => trivial) ≫ Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op =
        g.appLE ⊤ (Y.basicOpen s) (fun _ _ => trivial) := by
      exact Scheme.Hom.appLE_map _ _ _
    rw [← e]
    rfl
  haveI loc : IsLocalization.Away s Γ(Y, Y.basicOpen s) := U.2.isLocalization_basicOpen s
  exact h Γ(Y, Y.basicOpen s)

end GlobalTheory.CompanionTheory.Glob.ResKCoords
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.KaehlerBasisOnLocalizationAwayStatement
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_basis_on_localization_away : ∀ (K : Type) [Field K] (Y : Scheme.{0}) (g : Y ⟶ Sp K) (U : Y.affineOpens) (s : Γ(Y, U.1)) {n : ℕ} (x : Fin n → Γ(Y, U.1)), (letI := secAlgebra g U.1; ∀ (B : Type) [CommRing B] [Algebra Γ(Y, U.1) B] [Algebra K B] [IsScalarTower K Γ(Y, U.1) B] [IsLocalization.Away s B], LinearIndependent B (fun i => KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) ∧ Submodule.span B (Set.range fun i => KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) = ⊤) → IsCoords g (Y.basicOpen s) (fun i => Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op (x i)) := by
  first | exact @GlobalTheory.CompanionTheory.Glob.ResKCoords.isCoords_basicOpen_of_away | exact GlobalTheory.CompanionTheory.Glob.ResKCoords.isCoords_basicOpen_of_away | (intros; apply GlobalTheory.CompanionTheory.Glob.ResKCoords.isCoords_basicOpen_of_away <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RegularSequenceGermsRegularLocal
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RegularSequenceGermsRegularLocal
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

namespace GlobalTheory.CompanionTheory.ResKCoords

theorem map_maximalIdeal_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (e : R ≃+* S) :
    Ideal.map e (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S := by
  ext x
  rw [← Ideal.comap_symm, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, not_iff_not]
  exact isUnit_map_iff e.symm x

theorem rsp_of_ringEquiv {R S : Type} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (e : R ≃+* S) (m : ℕ) (r : Fin m → R) (h : FinalTheorems.Rsp R m r) :
    FinalTheorems.Rsp S m (fun i => e (r i)) := by
  refine ⟨?_, h.2.trans (ringKrullDim_eq_of_ringEquiv e)⟩
  have h1 : Set.range (fun i => e (r i)) = (e : R → S) '' Set.range r := by
    rw [← Set.range_comp]; rfl
  rw [h1, ← map_maximalIdeal_of_ringEquiv e, ← h.1]
  exact (Ideal.map_span e (Set.range r)).symm

theorem stalk_to_localization : ∀ (Y : Scheme.{0}) (U : Y.affineOpens) (y : Y) (hy : y ∈ U.1),
    IsRegularLocalRing (Y.presheaf.stalk y) → ∀ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
    FinalTheorems.Rsp (Y.presheaf.stalk y) m (fun i => Y.presheaf.germ U.1 y hy (f i)) →
    IsRegularLocalRing (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) ∧
    FinalTheorems.Rsp (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) m
      (fun i => algebraMap Γ(Y, U.1) _ (f i)) ∧
    ∀ s : Γ(Y, U.1), y ∈ Y.basicOpen s ↔ s ∉ (U.2.primeIdealOf ⟨y, hy⟩).asIdeal := by
  intro Y U y hy hreg m f hr
  letI := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨y, hy⟩ : U.1)
  haveI hloc : IsLocalization.AtPrime (Y.presheaf.stalk y) (U.2.primeIdealOf ⟨y, hy⟩).asIdeal :=
    U.2.isLocalization_stalk ⟨y, hy⟩
  let e : Y.presheaf.stalk y ≃+* Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal :=
    (IsLocalization.algEquiv (U.2.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Y.presheaf.stalk y)
      (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal)).toRingEquiv
  have he : ∀ a : Γ(Y, U.1), e (Y.presheaf.germ U.1 y hy a) = algebraMap Γ(Y, U.1) _ a := fun a =>
    (IsLocalization.algEquiv (U.2.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Y.presheaf.stalk y)
      (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal)).commutes a
  refine ⟨IsRegularLocalRing.of_ringEquiv e, ?_, fun s => ?_⟩
  · have h := rsp_of_ringEquiv e m _ hr
    simpa only [he] using h
  · rw [Scheme.mem_basicOpen Y s y hy]
    have h := IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk y)
      (U.2.primeIdealOf ⟨y, hy⟩).asIdeal s
    exact h.trans Iff.rfl

end GlobalTheory.CompanionTheory.ResKCoords
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RegularSequenceGermsRegularLocalStatement
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_sequence_germs_regular_local : ∀ (Y : Scheme.{0}) (U : Y.affineOpens) (y : Y) (hy : y ∈ U.1), IsRegularLocalRing (Y.presheaf.stalk y) → ∀ (m : ℕ) (f : Fin m → Γ(Y, U.1)), FinalTheorems.Rsp (Y.presheaf.stalk y) m (fun i => Y.presheaf.germ U.1 y hy (f i)) → IsRegularLocalRing (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) ∧ FinalTheorems.Rsp (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) m (fun i => algebraMap Γ(Y, U.1) _ (f i)) ∧ ∀ s : Γ(Y, U.1), y ∈ Y.basicOpen s ↔ s ∉ (U.2.primeIdealOf ⟨y, hy⟩).asIdeal := by
  first | exact @GlobalTheory.CompanionTheory.ResKCoords.stalk_to_localization | exact GlobalTheory.CompanionTheory.ResKCoords.stalk_to_localization | (intros; apply GlobalTheory.CompanionTheory.ResKCoords.stalk_to_localization <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.KaehlerBasisSpreadsToNeighbourhood
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.KaehlerBasisSpreadsToNeighbourhood
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

namespace GlobalTheory.CompanionTheory.KaehlerSpread

open KaehlerDifferential

noncomputable abbrev diffMap (K : Type) {A : Type} [Field K] [CommRing A] [Algebra K A] {n : ℕ}
    (x : Fin n → A) : (Fin n →₀ A) →ₗ[A] Ω[A⁄K] :=
  Finsupp.linearCombination A fun i => D K A (x i)

theorem map_diffMap_eq (K : Type) {A : Type} [Field K] [CommRing A] [Algebra K A] {n : ℕ}
    (x : Fin n → A) (S : Submonoid A) (B : Type) [CommRing B] [Algebra A B] [Algebra K B]
    [IsScalarTower K A B] [IsLocalization S B] :
    (IsLocalizedModule.mapExtendScalars S
      (Finsupp.mapRange.linearMap (Algebra.linearMap A B) : (Fin n →₀ A) →ₗ[A] (Fin n →₀ B))
      (map K K A B) B (diffMap K x)) =
      Finsupp.linearCombination B fun i => D K B (algebraMap A B (x i)) := by
  refine Finsupp.lhom_ext' fun i => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  have h1 : (Finsupp.single i (1 : B) : Fin n →₀ B) =
      Finsupp.mapRange.linearMap (Algebra.linearMap A B) (Finsupp.single i (1 : A)) := by
    simp
  rw [h1, IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_apply]
  simp [diffMap]

theorem bijective_linearCombination_iff {B M ι : Type} [CommRing B] [AddCommGroup M] [Module B M]
    (v : ι → M) :
    Function.Bijective (Finsupp.linearCombination B v) ↔
      LinearIndependent B v ∧ Submodule.span B (Set.range v) = ⊤ := by
  rw [Function.Bijective, ← LinearMap.range_eq_top, Finsupp.range_linearCombination]
  rfl

theorem spread : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Algebra.FinitePresentation K A] (P : Ideal A) [P.IsPrime] {n : ℕ} (x : Fin n → A), (LinearIndependent (Localization.AtPrime P) (fun i => KaehlerDifferential.D K (Localization.AtPrime P) (algebraMap A _ (x i))) ∧ Submodule.span (Localization.AtPrime P) (Set.range fun i => KaehlerDifferential.D K (Localization.AtPrime P) (algebraMap A _ (x i))) = ⊤) → ∃ s ∉ P, ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra K B] [IsScalarTower K A B] [IsLocalization.Away s B], LinearIndependent B (fun i => KaehlerDifferential.D K B (algebraMap A B (x i))) ∧ Submodule.span B (Set.range fun i => KaehlerDifferential.D K B (algebraMap A B (x i))) = ⊤ := by
  intro K A _ _ _ _ P _ n x hP
  classical
  let l₁ : (Fin n →₀ A) →ₗ[A] (Fin n →₀ Localization.AtPrime P) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A (Localization.AtPrime P))
  let l₂ : Ω[A⁄K] →ₗ[A] Ω[Localization.AtPrime P⁄K] :=
    KaehlerDifferential.map K K A (Localization.AtPrime P)
  have hP' : Function.Bijective (IsLocalizedModule.map P.primeCompl l₁ l₂ (diffMap K x)) := by
    have h := (bijective_linearCombination_iff _).mpr hP
    rw [← map_diffMap_eq K x P.primeCompl (Localization.AtPrime P)] at h
    exact h
  obtain ⟨s, hs, hbij⟩ :=
    Module.FinitePresentation.exists_notMem_bijective (diffMap K x) P l₁ l₂ hP'
  refine ⟨s, hs, ?_⟩
  intro B _ _ _ _ _
  rw [← bijective_linearCombination_iff, ← map_diffMap_eq K x (Submonoid.powers s) B]
  exact (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective
    (Finsupp.mapRange.linearMap (Algebra.linearMap A B)) (KaehlerDifferential.map K K A B)).mpr hbij

end GlobalTheory.CompanionTheory.KaehlerSpread
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.KaehlerBasisSpreadsToNeighbourhoodStatement
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_basis_spreads_to_neighbourhood : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Algebra.FinitePresentation K A] (P : Ideal A) [P.IsPrime] {n : ℕ} (x : Fin n → A), (LinearIndependent (Localization.AtPrime P) (fun i => KaehlerDifferential.D K (Localization.AtPrime P) (algebraMap A _ (x i))) ∧ Submodule.span (Localization.AtPrime P) (Set.range fun i => KaehlerDifferential.D K (Localization.AtPrime P) (algebraMap A _ (x i))) = ⊤) → ∃ s ∉ P, ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra K B] [IsScalarTower K A B] [IsLocalization.Away s B], LinearIndependent B (fun i => KaehlerDifferential.D K B (algebraMap A B (x i))) ∧ Submodule.span B (Set.range fun i => KaehlerDifferential.D K B (algebraMap A B (x i))) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.KaehlerSpread.spread | exact GlobalTheory.CompanionTheory.KaehlerSpread.spread | (intros; apply GlobalTheory.CompanionTheory.KaehlerSpread.spread <;> assumption)
end
end

noncomputable section
namespace GlobalTheory.CompanionTheory.Geo.SncCoords
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

theorem relDim_of_dense {X S : Scheme.{0}} (f : X ⟶ S) [Smooth f] (D : ℕ) (W : X.Opens)
    (hW : Dense (W : Set X)) (hWD : SmoothOfRelativeDimension D (W.ι ≫ f)) :
    SmoothOfRelativeDimension D f := by
  choose n V hV hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim f
  have two : ∀ (A B : X.Opens) (a b : ℕ), SmoothOfRelativeDimension a (A.ι ≫ f) →
      SmoothOfRelativeDimension b (B.ι ≫ f) → ∀ x, x ∈ A → x ∈ B → a = b := by
    intro A B a b ha hb x hA hB
    have e₁ : SmoothOfRelativeDimension (0 + a) ((A ⊓ B).ι ≫ f) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_left : A ⊓ B ≤ A), Category.assoc]; infer_instance
    have e₂ : SmoothOfRelativeDimension (0 + b) ((A ⊓ B).ι ≫ f) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_right : A ⊓ B ≤ B), Category.assoc]; infer_instance
    simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ e₁ e₂ ⟨x, hA, hB⟩
  have hc : IsLocallyConstant n := (IsLocallyConstant.iff_exists_open n).2 fun x =>
    ⟨V x, (V x).isOpen, hV x, fun y hy => two _ _ _ _ (hd y) (hd x) y (hV y) hy⟩
  have hWsub : (W : Set X) ⊆ n ⁻¹' {D} := fun x hx => two _ _ _ _ (hd x) hWD x (hV x) hx
  have hall : ∀ x, n x = D := by
    have hcl : IsClosed (n ⁻¹' {D}) := (hc.isClopen_fiber D).isClosed
    have := hcl.closure_subset_iff.2 hWsub
    rw [hW.closure_eq] at this
    exact fun x => this (Set.mem_univ x)
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension D) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension D) V
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hV x⟩) fun x => ?_
  rw [← hall x]; exact hd x

theorem basis_spread (K A : Type) [Field K] [CommRing A] [Algebra K A] [Algebra.FinitePresentation K A]
    (P : Ideal A) [P.IsPrime] {n : ℕ} (x : Fin n → A)
    (hx : LinearIndependent (Localization.AtPrime P)
        (fun i => KaehlerDifferential.D K (Localization.AtPrime P) (algebraMap A _ (x i))) ∧
      Submodule.span (Localization.AtPrime P)
        (Set.range fun i => KaehlerDifferential.D K (Localization.AtPrime P) (algebraMap A _ (x i))) = ⊤) :
    ∃ s ∉ P, ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra K B] [IsScalarTower K A B]
      [IsLocalization.Away s B],
      LinearIndependent B (fun i => KaehlerDifferential.D K B (algebraMap A B (x i))) ∧
        Submodule.span B (Set.range fun i => KaehlerDifferential.D K B (algebraMap A B (x i))) = ⊤ := GlobalTheory.T.kaehler_basis_spreads_to_neighbourhood K A P x hx

theorem omega_free (K : Type) [Field K] (D : ℕ) (Y : Scheme.{0}) (g : Y ⟶ Sp K)
    (hD : SmoothOfRelativeDimension D g) (U : Y.affineOpens) (P : Ideal Γ(Y, U.1)) [P.IsPrime] :
    letI := secAlgebra g U.1
    Algebra.FinitePresentation K Γ(Y, U.1) ∧
      Module.Free (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
      Module.Finite (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
      Module.finrank (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] = D := GlobalTheory.T.smooth_local_ring_free_differentials K D Y g hD U P

theorem stalk_transfer (Y : Scheme.{0}) (U : Y.affineOpens) (y : Y) (hy : y ∈ U.1)
    (hreg : IsRegularLocalRing (Y.presheaf.stalk y)) (m : ℕ) (f : Fin m → Γ(Y, U.1))
    (hf : FinalTheorems.Rsp (Y.presheaf.stalk y) m (fun i => Y.presheaf.germ U.1 y hy (f i))) :
    IsRegularLocalRing (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) ∧
      FinalTheorems.Rsp (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) m
        (fun i => algebraMap Γ(Y, U.1) _ (f i)) ∧
      ∀ s : Γ(Y, U.1), y ∈ Y.basicOpen s ↔ s ∉ (U.2.primeIdealOf ⟨y, hy⟩).asIdeal := GlobalTheory.T.regular_sequence_germs_regular_local Y U y hy hreg m f hf

theorem isCoords_basicOpen (K : Type) [Field K] (Y : Scheme.{0}) (g : Y ⟶ Sp K) (U : Y.affineOpens)
    (s : Γ(Y, U.1)) {n : ℕ} (x : Fin n → Γ(Y, U.1))
    (h : letI := secAlgebra g U.1
      ∀ (B : Type) [CommRing B] [Algebra Γ(Y, U.1) B] [Algebra K B] [IsScalarTower K Γ(Y, U.1) B]
        [IsLocalization.Away s B],
        LinearIndependent B (fun i => KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) ∧
          Submodule.span B (Set.range fun i => KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) = ⊤) :
    IsCoords g (Y.basicOpen s) (fun i => Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op (x i)) := GlobalTheory.T.kaehler_basis_on_localization_away K Y g U s x h

theorem coords_at_point (K : Type) [Field K] [CharZero K] (D : ℕ) (Y : Scheme.{0}) (g : Y ⟶ Sp K)
    (hD : SmoothOfRelativeDimension D g) (U : Y.affineOpens) (y : Y) (hy : y ∈ U.1)
    (hreg : IsRegularLocalRing (Y.presheaf.stalk y)) (m : ℕ) (f : Fin m → Γ(Y, U.1))
    (hf : FinalTheorems.Rsp (Y.presheaf.stalk y) m (fun i => Y.presheaf.germ U.1 y hy (f i))) :
    ∃ (s : Γ(Y, U.1)) (x : Fin D → Γ(Y, U.1)) (e : Fin m ↪ Fin D), y ∈ Y.basicOpen s ∧
      (∀ j, x (e j) = f j) ∧
      IsCoords g (Y.basicOpen s) (fun i => Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op (x i)) := by
  let _ := secAlgebra g U.1
  obtain ⟨hregP, hrspP, hmem⟩ := stalk_transfer Y U y hy hreg m f hf
  obtain ⟨hfp, hfree, hfin, hrank⟩ := omega_free K D Y g hD U (U.2.primeIdealOf ⟨y, hy⟩).asIdeal
  obtain ⟨x, e, hxe, bs, hbs⟩ := GlobalTheory.exists_coords_extending_regularParams K Γ(Y, U.1)
    (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) (U.2.primeIdealOf ⟨y, hy⟩).asIdeal D hrank m f hrspP
  have hb : (fun i => KaehlerDifferential.D K (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal)
      (algebraMap Γ(Y, U.1) _ (x i))) = bs := funext fun i => (hbs i).symm
  obtain ⟨s, hs, hspread⟩ := basis_spread K Γ(Y, U.1) (U.2.primeIdealOf ⟨y, hy⟩).asIdeal x
    ⟨by rw [hb]; exact bs.linearIndependent, by rw [hb]; exact bs.span_eq⟩
  exact ⟨s, x, e, (hmem s).2 hs, hxe, isCoords_basicOpen K Y g U s x hspread⟩

theorem exists_perm_first {D : ℕ} (E : Finset (Fin D)) :
    ∃ σ : Fin D ≃ Fin D, ∀ i : Fin D, (i : ℕ) < E.card ↔ σ i ∈ E := by
  classical
  have hk : E.card ≤ D := by simpa using E.card_le_univ
  have h1 : Fintype.card {i : Fin D // (i : ℕ) < E.card} = Fintype.card {b : Fin D // b ∈ E} := by
    rw [Fintype.card_coe]
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun i : Fin D => (i : ℕ) < E.card) = (Finset.range E.card).attachFin (fun _ h => by simp at h; omega) := by
      ext i; simp
    rw [this, Finset.card_attachFin, Finset.card_range]
  have h2 : Fintype.card {i : Fin D // ¬ (i : ℕ) < E.card} = Fintype.card {b : Fin D // ¬ b ∈ E} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]
  let σ := Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2)
  refine ⟨σ, fun i => ?_⟩
  by_cases hi : (i : ℕ) < E.card
  · have : σ i = ((Fintype.equivOfCardEq h1) ⟨i, hi⟩ : Fin D) := by
      simp only [σ, Equiv.subtypeCongr, Equiv.trans_apply]
      rw [Equiv.sumCompl_symm_apply_of_pos (p := fun x : Fin D => (x : ℕ) < E.card) hi]; rfl
    rw [this]
    exact iff_of_true hi ((Fintype.equivOfCardEq h1) ⟨i, hi⟩).2
  · have : σ i = ((Fintype.equivOfCardEq h2) ⟨i, hi⟩ : Fin D) := by
      simp only [σ, Equiv.subtypeCongr, Equiv.trans_apply]
      rw [Equiv.sumCompl_symm_apply_of_neg (p := fun x : Fin D => (x : ℕ) < E.card) hi]; rfl
    rw [this]
    exact iff_of_false hi ((Fintype.equivOfCardEq h2) ⟨i, hi⟩).2

theorem isCoords_comp_equiv {K : Type} [Field K] {Y : Scheme.{0}} (g : Y ⟶ Sp K) (V : Y.Opens) {D : ℕ}
    (z : Fin D → Γ(Y, V)) (σ : Fin D ≃ Fin D) (h : IsCoords g V z) : IsCoords g V (z ∘ σ) := by
  letI := secAlgebra g V
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · exact h1.comp σ σ.injective
  · have : (Set.range fun i => KaehlerDifferential.D K Γ(Y, V) ((z ∘ σ) i)) =
        Set.range fun i => KaehlerDifferential.D K Γ(Y, V) (z i) :=
      σ.surjective.range_comp (fun i => KaehlerDifferential.D K Γ(Y, V) (z i))
    rw [this]; exact h2

theorem mem_basicOpen_prod {ι : Type} {Y : Scheme.{0}} {U : Y.Opens} (J : Finset ι) (f : ι → Γ(Y, U)) (w : Y) :
    w ∈ Y.basicOpen (∏ j ∈ J, f j) ↔ w ∈ U ∧ ∀ j ∈ J, w ∈ Y.basicOpen (f j) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [Scheme.basicOpen_one]
  | insert a J ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul]
    simp only [TopologicalSpace.Opens.mem_inf, ih, Finset.mem_insert, forall_eq_or_imp]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3⟩
    · rintro ⟨h2, h1, h3⟩; exact ⟨h1, h2, h3⟩

theorem inter_eq_of_ideal {Y : Scheme.{0}} (T : Set Y) (hT : IsClosed T) (U : Y.affineOpens) (p : Γ(Y, U.1))
    (h : (Scheme.IdealSheafData.vanishingIdeal ⟨T, hT⟩).ideal U = Ideal.span {p}) :
    ((U.1 : Y.Opens) : Set Y) ∩ T = {x | x ∈ U.1 ∧ x ∉ Y.basicOpen p} := by
  have hsupp : ∀ x, x ∈ (Scheme.IdealSheafData.vanishingIdeal ⟨T, hT⟩).support ↔ x ∈ T := fun x => by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  ext x
  constructor
  · rintro ⟨hU, hx⟩
    refine ⟨hU, ?_⟩
    have hs := (hsupp x).2 hx
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hU, h, Scheme.mem_zeroLocus_iff] at hs
    exact hs p (Ideal.subset_span rfl)
  · rintro ⟨hU, hx⟩
    refine ⟨hU, (hsupp x).1 ?_⟩
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hU, h, Scheme.mem_zeroLocus_iff]
    intro q hq hqx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hq
    rw [Scheme.basicOpen_mul] at hqx
    exact hx hqx.2

theorem point_coords (K : Type) [Field K] [CharZero K] (D : ℕ) (Y : Scheme.{0}) (g : Y ⟶ Sp K)
    (T : Set Y) (hT : IsClosed T) (hD : SmoothOfRelativeDimension D g)
    (hsnc : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal ⟨T, hT⟩)) (y : Y) :
    ∃ (V : Y.affineOpens) (z : Fin D → Γ(Y, V.1)) (k : ℕ), y ∈ V.1 ∧ k ≤ D ∧ IsCoords g V.1 z ∧
      ((V.1 : Y.Opens) : Set Y) ∩ T = {x | x ∈ V.1 ∧ ∃ i : Fin D, (i : ℕ) < k ∧ x ∉ Y.basicOpen (z i)} := by
  classical
  obtain ⟨hreg, U, hy, m, f, J, hrsp, hid⟩ := hsnc y
  obtain ⟨s, x, e, hys, hxe, hco⟩ := coords_at_point K D Y g hD U y hy hreg m f hrsp
  obtain ⟨σ, hσ⟩ := exists_perm_first (J.map e)
  let r : Fin D → Γ(Y, Y.basicOpen s) := fun i => Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op (x i)
  have hr : ∀ i w, w ∈ Y.basicOpen s → (w ∈ Y.basicOpen (r i) ↔ w ∈ Y.basicOpen (x i)) := fun i w hw => by
    simp only [r, Scheme.basicOpen_res, TopologicalSpace.Opens.mem_inf, hw, true_and]
  have hset := inter_eq_of_ideal T hT U _ hid
  refine ⟨⟨Y.basicOpen s, U.2.basicOpen s⟩, r ∘ σ, (J.map e).card, hys,
    by simpa using (J.map e).card_le_univ, isCoords_comp_equiv g _ r σ hco, ?_⟩
  ext w
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Function.comp_apply]
  constructor
  · rintro ⟨hw, hwT⟩
    have hwU : w ∈ U.1 := Y.basicOpen_le s hw
    have h1 : w ∉ Y.basicOpen (∏ j ∈ J, f j) := (hset.subset ⟨hwU, hwT⟩).2
    rw [mem_basicOpen_prod] at h1
    push_neg at h1
    obtain ⟨j, hj, hwj⟩ := h1 hwU
    refine ⟨hw, σ.symm (e j), (hσ _).2 (by rw [Equiv.apply_symm_apply]; exact Finset.mem_map_of_mem e hj), ?_⟩
    rw [Equiv.apply_symm_apply, hr _ _ hw, hxe]; exact hwj
  · rintro ⟨hw, i, hi, hwi⟩
    have hwU : w ∈ U.1 := Y.basicOpen_le s hw
    refine ⟨hw, (hset.superset ⟨hwU, ?_⟩).2⟩
    obtain ⟨j, hj, hje⟩ := Finset.mem_map.1 ((hσ i).1 hi)
    rw [mem_basicOpen_prod]
    rintro ⟨-, hall⟩
    rw [hr _ _ hw, ← hje, hxe] at hwi
    exact hwi (hall j hj)

theorem hasSncCoords_of_local {K : Type} [Field K] (D : ℕ) {Y : Scheme.{0}} [CompactSpace Y] (g : Y ⟶ Sp K)
    (T : Set Y)
    (h : ∀ y : Y, ∃ (V : Y.affineOpens) (z : Fin D → Γ(Y, V.1)) (k : ℕ), y ∈ V.1 ∧ k ≤ D ∧ IsCoords g V.1 z ∧
      ((V.1 : Y.Opens) : Set Y) ∩ T = {x | x ∈ V.1 ∧ ∃ i : Fin D, (i : ℕ) < k ∧ x ∉ Y.basicOpen (z i)}) :
    HasSncCoords g D T := by
  classical
  choose V z k hy hk hz hT using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => ((V y).1 : Set Y)) (fun y => (V y).1.isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨y, hy y⟩)
  refine ⟨t.card, fun j => V (t.equivFin.symm j), fun y => ?_, fun j => ⟨z _, k _, hk _, hz _, hT _⟩⟩
  obtain ⟨a, ha, h⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  exact ⟨t.equivFin ⟨a, ha⟩, by simpa using h⟩

theorem coordsStatement : CoordsStatement := by
  intro K _ _ D Y g W T hT hc hs hW hWD hsnc
  have hD : SmoothOfRelativeDimension D g := relDim_of_dense g D W hW hWD
  exact ⟨hD, hasSncCoords_of_local D g T (point_coords K D Y g T hT hD hsnc)⟩

end GlobalTheory.CompanionTheory.Geo.SncCoords
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsStatement
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

namespace GlobalTheory.CompanionTheory.Geo.SncCoordsSide

theorem coordsStatement_side : ReciprocityTheory.ChartRestriction.G.Geo.ResK.CoordsStatement :=
  GlobalTheory.CompanionTheory.Geo.SncCoords.coordsStatement

end GlobalTheory.CompanionTheory.Geo.SncCoordsSide
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsStatementStatement
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_statement : ReciprocityTheory.ChartRestriction.G.Geo.ResK.CoordsStatement := by
  first | exact @GlobalTheory.CompanionTheory.Geo.SncCoordsSide.coordsStatement_side | exact GlobalTheory.CompanionTheory.Geo.SncCoordsSide.coordsStatement_side | (intros; apply GlobalTheory.CompanionTheory.Geo.SncCoordsSide.coordsStatement_side <;> assumption)
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.ResK ReciprocityTheory.AnForm.R

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide

theorem le_smoothLocus {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] (U : X.Opens)
    [Smooth (U.ι ≫ f)] : U ≤ f.smoothLocus := by
  intro x hx
  have := (U.ι ≫ f).smoothLocus_eq_top.ge (Set.mem_univ (⟨x, hx⟩ : U))
  rw [← Scheme.Hom.preimage_smoothLocus_eq] at this
  exact this

theorem dense_preimage {X Y : Scheme.{0}} (f : X ⟶ Y) {U V : Y.Opens} [IsIso (f ∣_ V)]
    (hV : Dense ((f ⁻¹ᵁ V : X.Opens) : Set X)) (hU : Dense (U : Set Y)) :
    Dense ((f ⁻¹ᵁ U : X.Opens) : Set X) := by
  rw [dense_iff_inter_open]
  intro O hO hne
  obtain ⟨p, hpO, hpV⟩ := hV.inter_open_nonempty O hO hne
  let O' : Set (f ⁻¹ᵁ V) := (f ⁻¹ᵁ V).ι.base ⁻¹' O
  have hO' : IsOpen O' := hO.preimage (f ⁻¹ᵁ V).ι.base.hom.continuous
  have hopen : IsOpen (V.ι.base '' ((f ∣_ V).base '' O')) :=
    V.ι.isOpenEmbedding.isOpenMap _ ((f ∣_ V).isOpenEmbedding.isOpenMap _ hO')
  have hp' : (⟨p, hpV⟩ : f ⁻¹ᵁ V) ∈ O' := hpO
  obtain ⟨y, ⟨q, ⟨p', hp'O, rfl⟩, rfl⟩, hyU⟩ := hU.inter_open_nonempty _ hopen ⟨_, _, ⟨_, hp', rfl⟩, rfl⟩
  refine ⟨(f ⁻¹ᵁ V).ι p', hp'O, ?_⟩
  show f ((f ⁻¹ᵁ V).ι p') ∈ U
  rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply]
  exact hyU

theorem relDim_preimage {X Y S : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ S) (U : Y.Opens) [IsIso (f ∣_ U)] {D : ℕ}
    (h : SmoothOfRelativeDimension D (U.ι ≫ g)) : SmoothOfRelativeDimension D ((f ⁻¹ᵁ U).ι ≫ f ≫ g) := by
  have : SmoothOfRelativeDimension (0 + D) ((f ∣_ U) ≫ U.ι ≫ g) := inferInstance
  rw [zero_add] at this
  rw [← morphismRestrict_ι_assoc]
  exact this

theorem relDim_of_dense {Y S : Scheme.{0}} (g : Y ⟶ S) [Smooth g] (W : Y.Opens) (hW : Dense (W : Set Y)) {D : ℕ}
    (h : SmoothOfRelativeDimension D (W.ι ≫ g)) : SmoothOfRelativeDimension D g := by
  choose n W' hW' hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim g
  have key : ∀ x, n x = D := by
    intro x
    obtain ⟨y, hyW', hyW⟩ := hW.inter_open_nonempty (W' x) (W' x).isOpen ⟨x, hW' x⟩
    have := hd x
    have e₁ : SmoothOfRelativeDimension (0 + n x) ((W' x ⊓ W).ι ≫ g) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_left : W' x ⊓ W ≤ W' x), Category.assoc]; infer_instance
    have e₂ : SmoothOfRelativeDimension (0 + D) ((W' x ⊓ W).ι ≫ g) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_right : W' x ⊓ W ≤ W), Category.assoc]; infer_instance
    simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ e₁ e₂ ⟨y, hyW', hyW⟩
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension D) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension D) W'
    (top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hW' x⟩) fun x => ?_
  rw [← key x]; exact hd x

theorem isProper_of_isProjOver {K : Type} [Field K] {Y : Scheme.{0}} {h : Y ⟶ Sp K} (hp : IsProjOver h) :
    IsProper h := by
  obtain ⟨N, i, hi, rfl⟩ := hp
  have : IsProper (PSpace.str K N) := isProper_str K N
  infer_instance

end GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide

theorem resK_of_resolution_principalisation (H₁ : ResolutionCharZero) (H₂ : PrincipalisationCharZero) :
    ResKStatement := by
  intro K _ _ M D X i U ⟨hi, hred, hdense, hU⟩
  have hproj : IsProjOver (i ≫ PSpace.str K M) := ⟨M, i, hi, rfl⟩
  have hP : IsProper (i ≫ PSpace.str K M) := isProper_of_isProjOver hproj
  obtain ⟨X₁, s, hs, hproj₁, hsm₁, hiso₁, hsnc₁⟩ := H₁.projective (i ≫ PSpace.str K M) hproj
  have : Smooth (U.ι ≫ i ≫ PSpace.str K M) := hU.smooth D _
  have hUs : U ≤ (i ≫ PSpace.str K M).smoothLocus := le_smoothLocus _ U
  have : IsIso (s ∣_ U) := isIso_morphismRestrict_of_le s hUs
  have hd₁ : Dense ((s ⁻¹ᵁ U : X₁.Opens) : Set X₁) := by
    refine dense_preimage s (V := (i ≫ PSpace.str K M).smoothLocus) ?_ hdense
    simpa using dense_compl_of_snc _ hsnc₁
  have hP₁ : IsProper (s ≫ i ≫ PSpace.str K M) := isProper_of_isProjOver hproj₁
  have hD₁ : SmoothOfRelativeDimension D (s ≫ i ≫ PSpace.str K M) :=
    relDim_of_dense _ _ hd₁ (relDim_preimage s _ U hU)
  let I : X₁.IdealSheafData := preRed s (U : Set X)ᶜ U.isOpen.isClosed_compl
  have hIs : (I.support : Set X₁) = s.base ⁻¹' (U : Set X)ᶜ := by
    simp [I, preRed]
  have : CompactSpace X₁ := by
    first
    | exact QuasiCompact.compactSpace_of_compactSpace (s ≫ i ≫ PSpace.str K M)
    | exact (quasiCompact_over_affine_iff (s ≫ i ≫ PSpace.str K M)).mp inferInstance
  have : IsLocallyNoetherian X₁ := by
    first
    | exact LocallyOfFiniteType.isLocallyNoetherian (s ≫ i ≫ PSpace.str K M)
    | infer_instance
  have : IsNoetherian X₁ := by first | infer_instance | exact ⟨⟩
  have : NoetherianSpace X₁ := inferInstance
  have hI : ∀ C ∈ irreducibleComponents X₁, ¬ C ⊆ (I.support : Set X₁) := by
    refine SncBlowup.not_subset_of_dense_compl ?_
    rw [hIs]; simpa using hd₁
  obtain ⟨X₂, t, E', hseq, hsm₂, hcart, hsnc₂, hiso₂⟩ :=
    H₂ K D X₁ (s ≫ i ≫ PSpace.str K M) hD₁ inferInstance inferInstance I ⊥ hI (fun x hx => hx.elim)
  have hsupp : ((I.comap t).support : Set X₂) = (t ≫ s).base ⁻¹' (U : Set X)ᶜ := by
    rw [Scheme.IdealSheafData.support_comap]
    simp [hIs] <;> rfl
  have hUc : I.support.compl = s ⁻¹ᵁ U := by
    ext x
    simp [hIs]
  rw [hUc] at hiso₂
  have hiso : IsIso ((t ≫ s) ∣_ U) := by rw [morphismRestrict_comp]; exact @IsIso.comp_isIso _ _ _ _ _ _ _ hiso₂ (isIso_morphismRestrict_of_le s hUs)
  have hT : IsClosed ((t ≫ s).base ⁻¹' (U : Set X)ᶜ) :=
    U.isOpen.isClosed_compl.preimage (t ≫ s).base.hom.continuous
  have hsncT : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal ⟨_, hT⟩) := by
    have e : (I.comap t).support = ⟨_, hT⟩ := Closeds.ext hsupp
    rwa [e] at hsnc₂
  have hd₂ : Dense (((t ≫ s) ⁻¹ᵁ U : X₂.Opens) : Set X₂) := by
    exact Dense.mono (fun x hx => by simpa using hx) (dense_compl_of_snc _ hsncT)
  have hproj₂ : IsProjOver (t ≫ s ≫ i ≫ PSpace.str K M) :=
    (Resolution.IsBlowupSeq.of_smooth hseq.isSmoothBlowupSeq).isProjOver hproj₁
  have hP₂ := isProper_of_isProjOver hproj₂
  have : CompactSpace X₂ := by
    first
    | exact QuasiCompact.compactSpace_of_compactSpace (t ≫ s ≫ i ≫ PSpace.str K M)
    | exact (quasiCompact_over_affine_iff (t ≫ s ≫ i ≫ PSpace.str K M)).mp inferInstance
  have hsm : Smooth ((t ≫ s) ≫ i ≫ PSpace.str K M) := by simpa using hsm₂
  obtain ⟨hDim, hC⟩ := GlobalTheory.T.coords_statement K D X₂ ((t ≫ s) ≫ i ≫ PSpace.str K M) ((t ≫ s) ⁻¹ᵁ U) _ hT inferInstance hsm hd₂
    (relDim_preimage (t ≫ s) _ U hU) hsncT
  obtain ⟨r, j, hj, e⟩ := exists_closed_in_prod ((t ≫ s) ≫ i) (by simpa using hproj₂)
  exact ⟨r, X₂, j, t ≫ s, hj, e, hDim, hiso, hd₂, hC⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide
