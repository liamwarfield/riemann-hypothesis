module

public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KawamataViehwegModPSquared
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncChartBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumberFieldToModPSquared
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeCrystalReducesToDeRhamSqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfPreservesFullLattice
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FinrankKaehlerAffineChart

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KawamataViehwegSpreading
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CohomologyVanishingSpecializes
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.SemicontLB

open GlobalTheory.AbLaw GlobalTheory.Adelic

theorem nonempty_cechLB_homology_equiv_coh {X : Scheme.{0}} {R : Type} [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) {M : LB X} (hM : M.IsLB) {κ : Type} [LinearOrder κ] [Finite κ]
    {D : κ → X.Opens} (hc : ⨆ i, D i = ⊤) (hD : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i))
    (n : ℕ) : Nonempty ((cechLB f M D).homology n ≃ coh (LB.toMod M) n) := by
  haveI : SheafOfModules.IsQuasicoherent (LB.toMod M) := GlobalTheory.LB.isQuasicoherent_toMod hM
  letI : Algebra R Γ(X, ⊤) := algebraΓOfHom f
  exact ⟨(((HomologicalComplex.homologyFunctor _ _ n).mapIso
    (FieldChangeInter.cechIso f M D)).toLinearEquiv.toEquiv).trans
    (cechHEquivCoh R hc hD (LB.toMod M) n).toEquiv⟩

private theorem affine_cover_preimage_of_isAffineHom {X Y : Scheme.{0}} (π : Y ⟶ X) [IsAffineHom π] {ι : Type}
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (hint : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) :
    (⨆ i, π ⁻¹ᵁ U i = ⊤) ∧ ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, π ⁻¹ᵁ U i) := by
  classical
  have key : ∀ s : Finset ι, ⨅ i ∈ s, π ⁻¹ᵁ U i = π ⁻¹ᵁ (⨅ i ∈ s, U i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.iInf_insert, Finset.iInf_insert, ih]; rfl
  refine ⟨?_, fun s hs => ?_⟩
  · rw [← Scheme.Hom.preimage_iSup, hU]; rfl
  · rw [key s]; exact (hint s hs).preimage π

private theorem fibre_lemma_2 {R : Type} [CommRing R] (K : CochainComplex (ModuleCat.{0} R) ℕ) (q : ℕ)
    (hV : ∀ p : PrimeSpectrum R, Module.Finite p.asIdeal.ResidueField
      ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).homology q))
    {κ : Type} [Field κ] (g : R →+* κ) :
    Subsingleton ((((ModuleCat.extendScalars g).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).homology q) ↔
      Module.finrank (⟨RingHom.ker g, RingHom.ker_isPrime g⟩ : PrimeSpectrum R).asIdeal.ResidueField
        ((((ModuleCat.extendScalars (algebraMap R
          (⟨RingHom.ker g, RingHom.ker_isPrime g⟩ : PrimeSpectrum R).asIdeal.ResidueField)).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj K).homology q) = 0 := by
  let P : PrimeSpectrum R := ⟨RingHom.ker g, RingHom.ker_isPrime g⟩
  change _ ↔ Module.finrank P.asIdeal.ResidueField
    ((((ModuleCat.extendScalars (algebraMap R P.asIdeal.ResidueField)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).homology q) = 0
  haveI := hV P
  have hunit : P.asIdeal.primeCompl ≤ Submonoid.comap g (IsUnit.submonoid κ) := by
    intro x hx
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
    exact isUnit_iff_ne_zero.2 fun h => hx (RingHom.mem_ker.2 h)
  let φ : P.asIdeal.ResidueField →+* κ := Ideal.ResidueField.lift P.asIdeal g le_rfl hunit
  have hcomp : φ.comp (algebraMap R P.asIdeal.ResidueField) = g :=
    RingHom.ext fun r => Ideal.ResidueField.lift_algebraMap _ _ le_rfl hunit r
  letI : Algebra P.asIdeal.ResidueField κ := φ.toAlgebra
  obtain ⟨e⟩ := FieldChangeInter.nonempty_homology_equiv κ
    (((ModuleCat.extendScalars (algebraMap R P.asIdeal.ResidueField)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K) q
  have e2 := ((HomologicalComplex.homologyFunctor _ _ q).mapIso
    ((Functor.mapHomologicalComplexCompIso
      (ModuleCat.extendScalarsComp (algebraMap R P.asIdeal.ResidueField) φ).symm
        (ComplexShape.up ℕ)).app K)).toLinearEquiv
  have e3 : (↑((((ModuleCat.extendScalars (φ.comp (algebraMap R P.asIdeal.ResidueField))).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).homology q) : Type) =
      (↑((((ModuleCat.extendScalars g).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).homology q) : Type) := by rw [hcomp]
  rw [← Module.finrank_baseChange (R := κ), Module.finrank_zero_iff]
  exact (((Equiv.cast e3).symm.trans e2.symm.toEquiv).trans e.toEquiv).subsingleton_congr

theorem subsingleton_coh_pull_of_ker_le : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0})
    (f : X ⟶ Sp R) [IsProper f] [Flat f] (M : LB X), M.IsLB → ∀ (κ₁ κ₂ : Type) [Field κ₁] [Field κ₂]
    (g₁ : R →+* κ₁) (g₂ : R →+* κ₂) (X₁ X₂ : Scheme.{0}) (f₁ : X₁ ⟶ Sp κ₁) (f₂ : X₂ ⟶ Sp κ₂) (π₁ : X₁ ⟶ X)
    (π₂ : X₂ ⟶ X), IsPullback π₁ f₁ f (spMap g₁) → IsPullback π₂ f₂ f (spMap g₂) →
    RingHom.ker g₂ ≤ RingHom.ker g₁ → ∀ q : ℕ, Subsingleton (coh (LB.toMod (M.pull π₁)) q) →
    Subsingleton (coh (LB.toMod (M.pull π₂)) q) := by
  intro R _ _ X f _ _ M hM κ₁ κ₂ _ _ g₁ g₂ X₁ X₂ f₁ f₂ π₁ π₂ h₁ h₂ hker q hsub
  haveI : CompactSpace X := by
    have : QuasiCompact f := inferInstance
    exact ⟨(QuasiCompact.isCompact_preimage (f := f) _ isOpen_univ isCompact_univ)⟩
  obtain ⟨ι, _, U, hU, hUtop⟩ :=
    GlobalTheory.QCoh.exists_finite_affine_cover_of_isCompact (X := X) (W := ⊤) isCompact_univ
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have hsep : X.IsSeparated := by
    have e : terminal.from X = f ≫ terminal.from _ := terminal.hom_ext _ _
    exact ⟨by rw [e]; infer_instance⟩
  have hint : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i) :=
    (GlobalTheory.cech_computes_coh_of_affine_cover.{0, 0, 0} X ℤ).1 (Or.inl hsep) ι U hU
  have hcov : ⨆ i, U i = ⊤ := hUtop.symm
  haveI : IsAffineHom π₁ := MorphismProperty.of_isPullback h₁.flip inferInstance
  haveI : IsAffineHom π₂ := MorphismProperty.of_isPullback h₂.flip inferInstance
  obtain ⟨hc₁, hi₁⟩ := affine_cover_preimage_of_isAffineHom π₁ U hcov hint
  obtain ⟨hc₂, hi₂⟩ := affine_cover_preimage_of_isAffineHom π₂ U hcov hint
  haveI : SheafOfModules.IsQuasicoherent (LB.toMod M) := GlobalTheory.LB.isQuasicoherent_toMod hM
  haveI : IsFiniteQC (LB.toMod M) :=
    GlobalTheory.QCoh.isFiniteQC_iff_isFiniteType.2 ⟨inferInstance, GlobalTheory.LB.isFiniteType_toMod hM⟩
  have hfin : ∀ p : ℕ, Module.Finite R ((cechLB f M U).homology p) := by
    intro p
    letI : Algebra R Γ(X, ⊤) := algebraΓOfHom f
    have e := ((HomologicalComplex.homologyFunctor _ _ p).mapIso
      (FieldChangeInter.cechIso f M U)).toLinearEquiv.trans (cechHEquivCoh R hcov hint (LB.toMod M) p)
    haveI := GlobalTheory.ProperFinite.finite_coh_of_isProper f (LB.toMod M) p
    exact Module.Finite.equiv e.symm
  obtain ⟨K, φ, hKz, hKfin, -, hKproj, -, -, hKq⟩ :=
    exists_finite_projective_complex_quasiIso (cechLB f M U) (Fintype.card ι)
      (fun p hp => GlobalTheory.AbLaw.isZero_cechLB_X f M U hp.le)
      (fun p => GlobalTheory.AbLaw.flat_cechLB_X f hM hint p) hfin
  haveI : ∀ i, Module.Finite R (K.X i) := hKfin
  haveI : ∀ i, Module.Projective R (K.X i) := hKproj
  have hsemi := GlobalTheory.semicontinuity_finite_projective_complex K (Fintype.card ι) hKz
  have hV := fun p => hsemi.1 q p
  have hus := hsemi.2.1 q
  have step : ∀ {κ : Type} [Field κ] (g : R →+* κ) (Y : Scheme.{0}) (fY : Y ⟶ Sp κ) (π : Y ⟶ X),
      IsPullback π fY f (spMap g) → (⨆ i, π ⁻¹ᵁ U i = ⊤) →
      (∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, π ⁻¹ᵁ U i)) →
      (Subsingleton (coh (LB.toMod (M.pull π)) q) ↔
        Subsingleton ((((ModuleCat.extendScalars g).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K).homology q)) := by
    intro κ _ g Y fY π h hc hi
    obtain ⟨e1⟩ := nonempty_cechLB_homology_equiv_coh fY (LB.isLB_pull hM π) hc hi q
    have e2 := (HomologicalComplex.homologyFunctor _ _ q).mapIso
      (GlobalTheory.AbLaw.cechLBBaseChangeIso hM h hint)
    letI : Algebra R κ := g.toAlgebra
    haveI : QuasiIso (((ModuleCat.extendScalars g).mapHomologicalComplex
      (ComplexShape.up ℕ)).map φ) := hKq κ
    have e3 := asIso (HomologicalComplex.homologyMap (((ModuleCat.extendScalars g).mapHomologicalComplex
      (ComplexShape.up ℕ)).map φ) q)
    exact ((e3.toLinearEquiv.toEquiv.trans e2.toLinearEquiv.toEquiv).trans e1).subsingleton_congr.symm
  have k1 := (fibre_lemma_2 K q hV g₁).1 ((step g₁ X₁ f₁ π₁ h₁ hc₁ hi₁).1 hsub)
  refine (step g₂ X₂ f₂ π₂ h₂ hc₂ hi₂).2 ((fibre_lemma_2 K q hV g₂).2 ?_)
  have hspec : (⟨RingHom.ker g₂, RingHom.ker_isPrime g₂⟩ : PrimeSpectrum R) ⤳
      (⟨RingHom.ker g₁, RingHom.ker_isPrime g₁⟩ : PrimeSpectrum R) :=
    (PrimeSpectrum.le_iff_specializes _ _).1 hker
  have h0 : (fun p : PrimeSpectrum R => Module.finrank p.asIdeal.ResidueField
      ↑((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).homology q)) ⟨RingHom.ker g₁, RingHom.ker_isPrime g₁⟩ < 1 := by
    simp only [k1]; exact Nat.zero_lt_one
  have hlt := ((hus _ 1 h0).filter_mono hspec.nhds_le_nhds).self_of_nhds
  exact Nat.lt_one_iff.1 hlt

end GlobalTheory.SemicontLB
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RelativeSncBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem relSnc_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), IsPullback π f' f (spMap φ) → RelSnc f d L σ → RelSnc f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π) := by
  intro R R' _ _ φ X X' f f' π d s L σ hpb h
  refine ⟨fun i => ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull (h.isLB i) π, fun x => ?_⟩
  obtain ⟨C, hC⟩ := h.chart (π.base x)
  obtain ⟨C', hC'⟩ := sncChart_baseChange R R' φ X X' f f' π d s L σ C hpb
  exact ⟨C', by rw [hC']; exact hC⟩

end GlobalTheory.LogPair
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FiniteTypeToModPSquared
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.NumberFieldToModPSquared
open scoped TensorProduct Polynomial
theorem _root_.GlobalTheory.T.number_field_to_mod_p_squared : ∀ (K : Type) [Field K] [NumberField K] (S : Finset K) (n : ℕ), ∃ p : ℕ, p.Prime ∧ n < p ∧ Nonempty (Subring.closure (S : Set K) →+* ZMod (p ^ 2)) := by
  first | exact @_root_.GlobalTheory.exists_prime_sq_ringHom_of_closure | exact _root_.GlobalTheory.exists_prime_sq_ringHom_of_closure | (intros; apply _root_.GlobalTheory.exists_prime_sq_ringHom_of_closure <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FiniteTypeToNumberField
open scoped TensorProduct Polynomial
theorem _root_.GlobalTheory.T.finite_type_to_number_field : ∀ (A : Type) [CommRing A] [IsDomain A] [CharZero A], Algebra.FiniteType ℤ A → ∀ a : A, a ≠ 0 → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (χ : A →+* K), χ a ≠ 0 := by
  first | exact @_root_.GlobalTheory.exists_numberField_point_ne_zero | exact _root_.GlobalTheory.exists_numberField_point_ne_zero | (intros; apply _root_.GlobalTheory.exists_numberField_point_ne_zero <;> assumption)
end

open scoped TensorProduct Polynomial

namespace GlobalTheory

theorem exists_ringHom_zmod_prime_sq_isUnit_of_finiteType :
    ∀ (A : Type) [CommRing A] [IsDomain A] [CharZero A], Algebra.FiniteType ℤ A → ∀ a : A, a ≠ 0 → ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ χ : A →+* ZMod (p ^ 2), IsUnit (χ a) := by
  intro A _ _ _ hA a ha n
  classical
  obtain ⟨K, _, _, χ₀, hχ⟩ := GlobalTheory.T.finite_type_to_number_field A hA a ha
  obtain ⟨s, hs⟩ := hA.out
  obtain ⟨p, hp, hn, ⟨ψ⟩⟩ := GlobalTheory.T.number_field_to_mod_p_squared K (insert (χ₀ a)⁻¹ (s.image χ₀)) n
  set R := Subring.closure ((insert (χ₀ a)⁻¹ (s.image χ₀) : Finset K) : Set K) with hR
  have hmem : ∀ x : A, χ₀ x ∈ R := by
    intro x
    have hx : x ∈ Algebra.adjoin ℤ (s : Set A) := by rw [hs]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      apply Subring.subset_closure
      simp only [Finset.coe_insert, Finset.coe_image]
      exact Set.mem_insert_of_mem _ ⟨y, hy, rfl⟩
    | algebraMap r => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact R.add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact R.mul_mem hx hy
  have hinv : (χ₀ a)⁻¹ ∈ R := by
    apply Subring.subset_closure
    simp
  refine ⟨p, hp, hn, ψ.comp (χ₀.codRestrict R hmem), ?_⟩
  rw [RingHom.comp_apply]
  apply IsUnit.map
  refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ ?_
  apply Subtype.ext
  simp [hχ]

end GlobalTheory
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KawamataViehwegSpreading
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory

theorem vanishing_charZero_fibre_of_finiteType : ∀ (R k : Type) [CommRing R] [Field k] [CharZero k] (φ : R →+* k) (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) (d : ℕ) [SmoothOfRelativeDimension d f] [IsProper f], Algebra.FiniteType ℤ R → Function.Injective φ → IsPullback π f' f (spMap φ) → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : RelSnc f d L σ) (K : CanonLB f d) (M A : LB X) (hM : M.IsLB) (hA : A.IsLB) (r : ℕ) (b : Fin s → ℕ), IsAmpleLB (A.pull π) → 0 < r → (∀ i, b i < r) → r • cls M hM = r • cls K.bundle K.isLB + ∑ i, b i • cls (L i) (h.isLB i) + cls A hA → ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod (M.pull π)) q) := by
  intro R k _ _ _ φ X X' f f' π d _ _ hR hφ hpb s L σ h K M A hM hA r b hAmp hr hb hrel q hq
  haveI : IsDomain R := Function.Injective.isDomain φ hφ
  haveI : CharZero R := (RingHom.charZero_iff hφ).mpr inferInstance
  haveI := hR
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  haveI hstab := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  haveI : Smooth f := SmoothOfRelativeDimension.smooth d f
  haveI : Flat f := inferInstance
  let KR := FractionRing R
  let ι : KR →+* k := IsFractionRing.lift hφ
  have hφι : φ = ι.comp (algebraMap R KR) := by
    ext x
    simp [ι, IsFractionRing.lift_algebraMap]
  have hsp : spMap φ = spMap ι ≫ spMap (algebraMap R KR) := by
    rw [hφι]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  haveI : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) hpb ‹IsProper f›
  have hAπ : (A.pull π).IsLB := LB.isLB_pull hA π
  have hrelK' : Out.RelAmple (Over.mk f') (A.pull π) :=
    haveI : IsProper (Over.mk f').hom := (inferInstance : IsProper f')
    (relAmple_iff_isAmpleLB_of_isAffine (Over.mk f') hAπ).mpr hAmp
  have hgenPb := IsPullback.of_hasPullback f (spMap (algebraMap R KR))
  have hA1 : (A.pull (pullback.fst f (spMap (algebraMap R KR)))).IsLB := LB.isLB_pull hA _
  have hgen : Out.RelAmple (Over.mk (pullback.snd f (spMap (algebraMap R KR))))
      (A.pull (pullback.fst f (spMap (algebraMap R KR)))) :=
    FibreAmple.relAmple_of_fieldExtension hA ι hgenPb (hsp ▸ hpb) hA1 ((cls_eq_iff hA1 hA1).mp rfl) hrelK'
  obtain ⟨a, ha, hspread⟩ := AmpleSpread.relAmple_spread R KR (Over.mk f) A ‹IsProper f› hA hgen
  obtain ⟨p, hp, hdp, χ, hχ⟩ := exists_ringHom_zmod_prime_sq_isUnit_of_finiteType R hR a ha d
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  let c : ZMod (p ^ 2) →+* ZMod p := ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)
  have hY := IsPullback.of_hasPullback f (spMap χ)
  haveI : SmoothOfRelativeDimension d (pullback.snd f (spMap χ)) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d) hY inferInstance
  have h1 := IsPullback.of_hasPullback (pullback.snd f (spMap χ)) (spMap c)
  haveI : SmoothOfRelativeDimension d (pullback.snd (pullback.snd f (spMap χ)) (spMap c)) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d) h1 inferInstance
  haveI : IsProper (pullback.snd (pullback.snd f (spMap χ)) (spMap c)) := inferInstance
  have hsp2 : spMap c ≫ spMap χ = spMap (c.comp χ) := by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have hρ : IsPullback (pullback.fst (pullback.snd f (spMap χ)) (spMap c) ≫ pullback.fst f (spMap χ))
      (pullback.snd (pullback.snd f (spMap χ)) (spMap c)) f (spMap (c.comp χ)) :=
    hsp2 ▸ h1.paste_horiz hY
  set ρ := pullback.fst (pullback.snd f (spMap χ)) (spMap c) ≫ pullback.fst f (spMap χ) with hρdef
  set f₁ := pullback.snd (pullback.snd f (spMap χ)) (spMap c) with hf₁
  have hspec := hspread (ZMod p) (c.comp χ) (hχ.map c)
  have hid : spMap (RingHom.id (ZMod p)) ≫ spMap (c.comp χ) = spMap (c.comp χ) := by
    simp [spMap]
  have hAρ : (A.pull ρ).IsLB := LB.isLB_pull hA ρ
  have hamp1 : Out.RelAmple (Over.mk f₁) (A.pull ρ) :=
    FibreAmple.relAmple_of_fieldExtension hA (RingHom.id (ZMod p)) hρ
      (hid.symm ▸ IsPullback.of_hasPullback f (spMap (c.comp χ))) hAρ ((cls_eq_iff hAρ hAρ).mp rfl) hspec
  haveI : IsProper (Over.mk f₁).hom := (inferInstance : IsProper f₁)
  have hampX : IsAmpleLB (A.pull ρ) := (relAmple_iff_isAmpleLB_of_isAffine (Over.mk f₁) hAρ).mp hamp1
  have hproj : IsProjOver f₁ := (isProjOver_iff_isProper_and_exists_isAmpleLB f₁).mpr ⟨inferInstance, _, hampX⟩
  have hL := LogPair.relSnc_baseChange R (ZMod (p ^ 2)) χ X _ f _ _ d s L σ hY h
  let K₁ : CanonLB f₁ d := CanonLB.baseChange hρ K
  have hMρ : (M.pull ρ).IsLB := LB.isLB_pull hM ρ
  have hrel1 : r • cls (M.pull ρ) hMρ = r • cls K₁.bundle K₁.isLB +
      ∑ i, b i • pull (pullback.fst (pullback.snd f (spMap χ)) (spMap c))
        (cls ((L i).pull (pullback.fst f (spMap χ))) (LB.isLB_pull (h.isLB i) _)) + cls (A.pull ρ) hAρ := by
    have e := congrArg (pull ρ) hrel
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_nsmul, map_sum] at e
    have eK : cls K₁.bundle K₁.isLB = pull ρ (cls K.bundle K.isLB) := cls_pull K.isLB ρ K₁.isLB
    rw [cls_pull hM ρ, eK, cls_pull hA ρ]
    convert e using 4
    rw [cls_pull (h.isLB _) _, ← pull_comp]
  have hvan := charp_vanishing_liftable p _ _ (pullback.snd f (spMap χ)) f₁
    (pullback.fst (pullback.snd f (spMap χ)) (spMap c)) d h1 hproj hdp s
    (fun i => (L i).pull (pullback.fst f (spMap χ))) (fun i => Cartier.secPull (σ i) _) hL K₁
    (M.pull ρ) (A.pull ρ) hMρ hampX r b hr hb hrel1 q hq
  have hker : RingHom.ker φ ≤ RingHom.ker (c.comp χ) := by
    rw [(RingHom.injective_iff_ker_eq_bot φ).mp hφ]
    exact bot_le
  exact SemicontLB.subsingleton_coh_pull_of_ker_le R X f M hM (ZMod p) k (c.comp χ) φ _ X' f₁ f' ρ π hρ hpb hker q hvan

end GlobalTheory
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KawamataViehwegSpreadingStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.kawamata_viehweg_spreading : ∀ (R k : Type) [CommRing R] [Field k] [CharZero k] (φ : R →+* k) (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) (d : ℕ) [SmoothOfRelativeDimension d f] [IsProper f], Algebra.FiniteType ℤ R → Function.Injective φ → IsPullback π f' f (spMap φ) → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : RelSnc f d L σ) (K : CanonLB f d) (M A : LB X) (hM : M.IsLB) (hA : A.IsLB) (r : ℕ) (b : Fin s → ℕ), IsAmpleLB (A.pull π) → 0 < r → (∀ i, b i < r) → r • cls M hM = r • cls K.bundle K.isLB + ∑ i, b i • cls (L i) (h.isLB i) + cls A hA → ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod (M.pull π)) q) := by
  first | exact @_root_.GlobalTheory.vanishing_charZero_fibre_of_finiteType | exact _root_.GlobalTheory.vanishing_charZero_fibre_of_finiteType | (intros; apply _root_.GlobalTheory.vanishing_charZero_fibre_of_finiteType <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutRelativeSnc
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RelativeSncGenericSpread
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncChartDescends
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EtaleCoordinatesDifferentials
open scoped TensorProduct Polynomial
theorem _root_.GlobalTheory.T.etale_coordinates_differentials : ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K] (d : ℕ) (t : Fin d → B), (MvPolynomial.eval₂Hom (algebraMap R B) t).Etale → Module.finrank K (K ⊗[B] Ω[B⁄R]) = d ∧ ∀ (ι : Type) (e : ι ↪ Fin d) (u : ι → Bˣ), (∀ i, algebraMap B K (t (e i)) = 0) → LinearIndependent K (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B ((u i : B) * t (e i))) := by
  first | exact @_root_.GlobalTheory.EtaleCoordRank.finrank_and_linearIndependent_D_unit_mul | exact _root_.GlobalTheory.EtaleCoordRank.finrank_and_linearIndependent_D_unit_mul | (intros; apply _root_.GlobalTheory.EtaleCoordRank.finrank_and_linearIndependent_D_unit_mul <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncChartDescends
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.ChartDesc

theorem resG_etale (X : Scheme.{0}) (U W : X.Opens) (h : W ≤ U) (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) : (resG X h).Etale := by
  have := HasRingHomProperty.appLE (P := @Etale) (𝟙 X) (inferInstanceAs (Etale (𝟙 X))) ⟨U, hU⟩
    ⟨W, hW⟩ (by simpa using h)
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp] at this
  exact this

theorem chart_desc : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) [Smooth f] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (C' : SncChart f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π)) (y : X'), IsPullback π f' f (spMap φ) → y ∈ C'.U → ∃ C : SncChart f d L σ, π y ∈ C.U := by
  intro R R' _ _ φ X X' f f' π _ d s L σ C' y H hy
  let c : ∀ i, (L i).ι := fun i => C'.c i ⟨⟩
  have hyc : ∀ i, π y ∈ (L i).U (c i) := fun i => by
    exact (Cartier.pull_U (L i) π (C'.c i)).le (C'.le i hy)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_iInter.2 hyc) (isOpen_iInter_of_finite fun i => ((L i).U (c i)).isOpen)
  have hc : ∀ i, (U : X.Opens) ≤ (L i).U (c i) := fun i _ hz => Set.mem_iInter.1 (hUle hz) i
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWle⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ ((C'.U ⊓ π ⁻¹ᵁ U : X'.Opens) : Set X') from ⟨hy, hxU⟩) (C'.U ⊓ π ⁻¹ᵁ U).isOpen
  have hWC : (W : X'.Opens) ≤ C'.U := fun _ hz => (hWle hz).1
  have hWU : (W : X'.Opens) ≤ π ⁻¹ᵁ U := fun _ hz => (hWle hz).2

  have hA : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  have hU' : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := π ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have po' : IsPushout (Qcqs.baseRingHom f U) (CommRingCat.ofHom φ) (π.app U)
      (Qcqs.baseRingHom f' (π ⁻¹ᵁ U)) := by
    refine po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [Qcqs.baseRingHom]
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · simp [Scheme.Hom.app_eq_appLE]
    · simp [Qcqs.baseRingHom]
  let K := X'.residueField y
  letI : Algebra R R' := φ.toAlgebra
  letI : Algebra R Γ(X, U) := (cstOn f U).toAlgebra
  letI : Algebra R' Γ(X', π ⁻¹ᵁ U) := (cstOn f' (π ⁻¹ᵁ U)).toAlgebra
  letI : Algebra Γ(X, U) Γ(X', π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra
  letI : Algebra R Γ(X', π ⁻¹ᵁ U) := ((cstOn f' (π ⁻¹ᵁ U)).comp φ).toAlgebra
  letI : Algebra Γ(X', π ⁻¹ᵁ U) Γ(X', W) := (resG X' hWU).toAlgebra
  letI : Algebra R' Γ(X', W) := (cstOn f' W).toAlgebra
  letI : Algebra Γ(X', W) K := (X'.evaluation W y hyW).hom.toAlgebra
  letI : Algebra Γ(X, U) K :=
    ((X'.evaluation W y hyW).hom.comp ((resG X' hWU).comp (π.app U).hom)).toAlgebra
  haveI : IsScalarTower R R' Γ(X', π ⁻¹ᵁ U) := .of_algebraMap_eq fun r ↦ rfl
  have e2 : ∀ r : R, (π.app U).hom (cstOn f U r) = cstOn f' (π ⁻¹ᵁ U) (φ r) := fun r => by
    have h1 := Qcqs.app_baseRingHom π f U r
    have h2 : Qcqs.baseRingHom (π ≫ f) (π ⁻¹ᵁ U) r = Qcqs.baseRingHom f' (π ⁻¹ᵁ U) (φ r) := by
      rw [H.w, Qcqs.baseRingHom_comp_SpecMap]; rfl
    exact h1.trans h2
  haveI : IsScalarTower R Γ(X, U) Γ(X', π ⁻¹ᵁ U) := .of_algebraMap_eq fun r ↦ (e2 r).symm
  haveI : Algebra.IsPushout R R' Γ(X, U) Γ(X', π ⁻¹ᵁ U) := by
    have po'' : IsPushout (CommRingCat.ofHom (algebraMap R Γ(X, U))) (CommRingCat.ofHom (algebraMap R R'))
        (CommRingCat.ofHom (algebraMap Γ(X, U) Γ(X', π ⁻¹ᵁ U)))
        (CommRingCat.ofHom (algebraMap R' Γ(X', π ⁻¹ᵁ U))) := po'
    exact (CommRingCat.isPushout_iff_isPushout.mp po'').symm
  haveI : IsScalarTower R' Γ(X', π ⁻¹ᵁ U) Γ(X', W) := .of_algebraMap_eq fun r ↦
    (Qcqs.baseRingHom_res f' hWU r).symm
  haveI : Algebra.FormallyEtale Γ(X', π ⁻¹ᵁ U) Γ(X', W) := by
    haveI : Algebra.Etale Γ(X', π ⁻¹ᵁ U) Γ(X', W) := resG_etale X' _ _ hWU hU' hW
    infer_instance

  let t : Fin d → Γ(X', W) := fun a => resG X' hWC (C'.t a)
  have ht : IsEtCoord f' W t := GlobalTheory.T.isEtaleCoordinatesOnOpen_restrict_affineOpen R' X' f' C'.U W hWC d C'.t C'.affine hW C'.etale
  have hbasis := GlobalTheory.T.etale_coordinates_differentials R' Γ(X', W) K d t ht
  obtain ⟨ebc, hebc⟩ := GlobalTheory.T.exists_kaehler_fibre_equiv_D_compat R R' Γ(X, U) Γ(X', π ⁻¹ᵁ U) Γ(X', W) K (fun _ => rfl)
  have key : ∀ i, algebraMap Γ(X', π ⁻¹ᵁ U) Γ(X', W)
      (algebraMap Γ(X, U) Γ(X', π ⁻¹ᵁ U) (resG X (hc i) ((σ i).f (c i)))) =
      ((Units.map (resG X' hWC).toMonoidHom (C'.u i) : Γ(X', W)ˣ) : Γ(X', W)) *
        resG X' hWC ((C'.e i).elim 1 C'.t) := by
    intro i
    have e := congrArg (resG X' hWC) (C'.eq i)
    rw [map_mul] at e
    refine Eq.trans ?_ e
    show resG X' hWU ((π.app U).hom (resG X (hc i) ((σ i).f (c i)))) =
      resG X' hWC (resG X' (C'.le i) (resG X' _ ((π.app _).hom ((σ i).f (C'.c i ⟨⟩)))))
    rw [Cartier.app_resG, Cartier.resG_resG, Cartier.resG_resG, Cartier.resG_resG]
  have hunit : ∀ v : Γ(X', W)ˣ, algebraMap Γ(X', W) K v ≠ 0 := fun v =>
    (v.isUnit.map (algebraMap Γ(X', W) K)).ne_zero
  have hres : ∀ a : Γ(X, U), algebraMap Γ(X, U) K a ≠ 0 ↔ π y ∈ X.basicOpen a := by
    intro a
    change (X'.evaluation W y hyW).hom (resG X' hWU ((π.app U).hom a)) ≠ 0 ↔ _
    rw [Ne, Scheme.evaluation_eq_zero_iff_notMem_basicOpen, not_not]
    change y ∈ X'.basicOpen ((X'.presheaf.map (homOfLE hWU).op).hom _) ↔ _
    rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
    exact ⟨fun h => h.2, fun h => ⟨hyW, h⟩⟩
  have hrank : Module.finrank K (K ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R]) = d :=
    ebc.finrank_eq.trans hbasis.1
  have hvan : ∀ i : {i : Fin s // algebraMap Γ(X, U) K (resG X (hc i) ((σ i).f (c i))) = 0},
      ∃ a, C'.e i.1 = some a ∧ algebraMap Γ(X', W) K (t a) = 0 := by
    rintro ⟨i, hi⟩
    have h0 : algebraMap Γ(X', W) K (algebraMap Γ(X', π ⁻¹ᵁ U) Γ(X', W)
        (algebraMap Γ(X, U) Γ(X', π ⁻¹ᵁ U) (resG X (hc i) ((σ i).f (c i))))) = 0 := hi
    rw [key i, map_mul] at h0
    rcases hE : C'.e i with _ | a
    · rw [hE] at h0
      simp only [Option.elim, map_one, mul_one] at h0
      exact absurd h0 (hunit _)
    · refine ⟨a, rfl, ?_⟩
      rw [hE] at h0
      exact (mul_eq_zero.1 h0).resolve_left (hunit _)
  choose g hg hg0 using hvan
  let emb : {i : Fin s // algebraMap Γ(X, U) K (resG X (hc i) ((σ i).f (c i))) = 0} ↪ Fin d :=
    ⟨g, fun i j hij => Subtype.ext (C'.inj i.1 j.1 (g i) (hg i) (by rw [hij]; exact hg j))⟩
  let u : {i : Fin s // algebraMap Γ(X, U) K (resG X (hc i) ((σ i).f (c i))) = 0} → Γ(X', W)ˣ :=
    fun i => Units.map (resG X' hWC).toMonoidHom (C'.u i.1)
  have hli := hbasis.2 _ emb u hg0
  have hfam : ∀ i : {i : Fin s // algebraMap Γ(X, U) K (resG X (hc i) ((σ i).f (c i))) = 0},
      ebc ((1 : K) ⊗ₜ[Γ(X, U)] KaehlerDifferential.D R Γ(X, U) (resG X (hc i.1) ((σ i.1).f (c i.1)))) =
      (1 : K) ⊗ₜ[Γ(X', W)] KaehlerDifferential.D R' Γ(X', W) ((u i : Γ(X', W)) * t (emb i)) := by
    intro i
    rw [hebc, key i.1, hg i]
    rfl
  have hlin : LinearIndependent K (fun i : {i : Fin s // algebraMap Γ(X, U) K
      (resG X (hc i) ((σ i).f (c i))) = 0} =>
      (1 : K) ⊗ₜ[Γ(X, U)] KaehlerDifferential.D R Γ(X, U) (resG X (hc i.1) ((σ i.1).f (c i.1)))) := by
    refine LinearIndependent.of_comp ebc.toLinearMap ?_
    convert hli using 1
    funext i
    exact hfam i
  exact GlobalTheory.T.finrank_kaehler_affine_chart R X f d s L σ U c hc (π y) K hU hxU hres ⟨hrank, hlin⟩

end GlobalTheory.ChartDesc
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncChartDescendsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.snc_chart_descends : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) [Smooth f] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (C' : SncChart f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π)) (y : X'), IsPullback π f' f (spMap φ) → y ∈ C'.U → ∃ C : SncChart f d L σ, π y ∈ C.U := by
  first | exact @_root_.GlobalTheory.ChartDesc.chart_desc | exact _root_.GlobalTheory.ChartDesc.chart_desc | (intros; apply _root_.GlobalTheory.ChartDesc.chart_desc <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RelativeSncGenericSpread
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

theorem GlobalTheory.LogPair.relSnc_spread : ∀ (R k : Type) [CommRing R] [Field k] (φ : R →+* k) (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) [Smooth f] [IsProper f] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), IsPullback π f' f (spMap φ) → (∀ i, (L i).IsLB) → RelSnc f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π) → ∃ a : R, φ a ≠ 0 ∧ ∀ (T : Type) [CommRing T] (χ : R →+* T), IsUnit (χ a) → ∀ (Z : Scheme.{0}) (g : Z ⟶ Sp T) (ρ : Z ⟶ X), IsPullback ρ g f (spMap χ) → RelSnc g d (fun i => (L i).pull ρ) (fun i => Cartier.secPull (σ i) ρ) := by
  intro R k _ _ φ X X' f f' π _ _ d s L σ hpb hL hrel
  let W : X.Opens := ⨆ C : SncChart f d L σ, C.U
  have hW : π ⁻¹ᵁ W = ⊤ := by
    refine top_unique fun y _ => ?_
    obtain ⟨C', hC'⟩ := hrel.chart y
    obtain ⟨C, hC⟩ := GlobalTheory.T.snc_chart_descends R k φ X X' f f' π d s L σ C' y hpb hC'
    show π y ∈ W
    exact (Opens.mem_iSup).2 ⟨C, hC⟩
  obtain ⟨a, ha, h⟩ := GlobalTheory.T.universallyClosed_open_containing_fibre_contains_nearby R k φ X X' f f' π W hpb hW
  refine ⟨a, ha, fun T _ χ hχ Z g ρ hρ => ?_⟩
  have hZ := h T χ hχ Z g ρ hρ
  refine ⟨fun i => LB.isLB_pull (hL i) ρ, fun z => ?_⟩
  have hz : ρ z ∈ W := by
    have : z ∈ ρ ⁻¹ᵁ W := by rw [hZ]; trivial
    exact this
  obtain ⟨C, hC⟩ := (Opens.mem_iSup).1 hz
  obtain ⟨C', hC'⟩ := GlobalTheory.T.snc_chart_base_change R T χ X Z f g ρ d s L σ C hρ
  refine ⟨C', ?_⟩
  rw [hC']
  exact hC
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RelativeSncGenericSpreadStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.relative_snc_generic_spread : ∀ (R k : Type) [CommRing R] [Field k] (φ : R →+* k) (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) [Smooth f] [IsProper f] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), IsPullback π f' f (spMap φ) → (∀ i, (L i).IsLB) → RelSnc f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π) → ∃ a : R, φ a ≠ 0 ∧ ∀ (T : Type) [CommRing T] (χ : R →+* T), IsUnit (χ a) → ∀ (Z : Scheme.{0}) (g : Z ⟶ Sp T) (ρ : Z ⟶ X), IsPullback ρ g f (spMap χ) → RelSnc g d (fun i => (L i).pull ρ) (fun i => Cartier.secPull (σ i) ρ) := by
  first | exact @_root_.GlobalTheory.LogPair.relSnc_spread | exact _root_.GlobalTheory.LogPair.relSnc_spread | (intros; apply _root_.GlobalTheory.LogPair.relSnc_spread <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutSmoothProper
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutMorphism
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutLineBundle
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FlatBaseChangeSections
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.flat_base_change_sections : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) [QuasiCompact f] [IsSeparated f] (L : LB X), φ.Flat → IsPullback π f' f (spMap φ) → L.IsLB → ∀ σ : (L.pull π).Sec, ∃ (n : ℕ) (c : Fin n → R') (τ : Fin n → L.Sec), ∀ i, σ.f i = ∑ a, cstOn f' _ (c a) * (Cartier.secPull (τ a) π).f i := by
  first | exact @_root_.GlobalTheory.SecFlatBC.exists_sum_secPull | exact _root_.GlobalTheory.SecFlatBC.exists_sum_secPull | (intros; apply _root_.GlobalTheory.SecFlatBC.exists_sum_secPull <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutLineBundle
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem subring_subtype_flat {k : Type} [Field k] (R : Subring k) : R.subtype.Flat := by
  have : FaithfulSMul R k := (faithfulSMul_iff_algebraMap_injective R k).2 R.subtype_injective
  let _ := FractionRing.liftAlgebra R k
  have := FractionRing.isScalarTower_liftAlgebra R k
  have h1 : Module.Flat R (FractionRing R) := IsLocalization.flat _ (nonZeroDivisors R)
  have h2 : Module.Flat R k := Module.Flat.trans R (FractionRing R) k
  exact (RingHom.flat_algebraMap_iff (R := R) (S := k)).2 h2

theorem resG_cstOn_const {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (h : V ≤ U) (c : R) : resG X h (cstOn p U c) = cstOn p V c := by
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ U le_top ≫
    X.presheaf.map (homOfLE h).op).hom c = _
  erw [Scheme.Hom.appLE_map]
  rfl

theorem app_cstOn_const {R : Type} [CommRing R] {X Y : Scheme.{0}} (p : X ⟶ Sp R) (j : Y ⟶ X)
    {U : X.Opens} {V : Y.Opens} (h : V ≤ j ⁻¹ᵁ U) (c : R) :
    resG Y h ((j.app U).hom (cstOn p U c)) = cstOn (j ≫ p) V c := by
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ U le_top ≫ j.appLE U V h).hom c = _
  exact congrArg (fun g => ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g).hom c)
    (Scheme.Hom.appLE_comp_appLE j p ⊤ U V le_top h)

theorem cstOn_comp_spMap_const {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X : Scheme.{0}}
    (p : X ⟶ Sp R') (U : X.Opens) (c : R) : cstOn (p ≫ spMap φ) U c = cstOn p U (φ c) := by
  have e : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (p ≫ spMap φ).appLE ⊤ U le_top =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫ p.appLE ⊤ U le_top := by
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    erw [Scheme.Hom.comp_appLE]
    rfl
  exact congrArg (fun g => g.hom c) e

def secComb {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X} {n : ℕ}
    (c : Fin n → R) (τ : Fin n → L.Sec) : L.Sec where
  f i := ∑ a, cstOn p _ (c a) * (τ a).f i
  compat i j := by
    change resG X _ _ = _ * resG X _ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, map_mul, resG_cstOn_const, resG_cstOn_const, mul_left_comm]
    exact congrArg _ ((τ a).compat i j)

theorem resG_comb_pull {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X X₁ X₀ : Scheme.{0}}
    (f : X ⟶ Sp R') (f₁ : X₁ ⟶ Sp R) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁) (hf : j ≫ f₁ = f ≫ spMap φ)
    {n : ℕ} (c : Fin n → R) {U₀ : X₀.Opens} (t : Fin n → Γ(X₀, U₀)) {U₁ : X₁.Opens} {V V' W : X.Opens}
    (h₁ : U₁ ≤ π₁ ⁻¹ᵁ U₀) (hV : V ≤ j ⁻¹ᵁ U₁) (hV' : V' ≤ (j ≫ π₁) ⁻¹ᵁ U₀) (hW' : W ≤ V') (hW : W ≤ V) :
    resG X hW' (∑ a, cstOn f V' (φ (c a)) * resG X hV' (((j ≫ π₁).app U₀).hom (t a))) =
      resG X hW (resG X hV ((j.app U₁).hom
        (∑ a, cstOn f₁ U₁ (c a) * resG X₁ h₁ ((π₁.app U₀).hom (t a))))) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Cartier.resG_resG, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, map_mul, map_mul, app_cstOn_const, resG_cstOn_const, hf, cstOn_comp_spMap_const,
    Cartier.app_resG, Cartier.resG_resG, Cartier.resG_resG]
  rfl

theorem exists_finset_sec_descends : ∀ (k : Type) [Field k] (R₀ : Subring k) (X X₀ : Scheme.{0}) (f : X ⟶ Sp k) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [IsProper f₀] (L : LB X₀) (σ : (L.pull π).Sec), IsPullback π f f₀ (spMap R₀.subtype) → L.IsLB → ∃ F : Finset k, ∀ (R₁ : Subring k) (hR : R₀ ≤ R₁), (F : Set k) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion hR)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ τ : (L.pull π₁).Sec, SameDiv σ (Cartier.secPull τ j) := by
  classical
  intro k _ R₀ X X₀ f f₀ π _ L σ hπ hL
  obtain ⟨n, c, τ, hσ⟩ := GlobalTheory.T.flat_base_change_sections R₀ k R₀.subtype X₀ X f₀ f π L (subring_subtype_flat R₀) hπ hL σ
  refine ⟨Finset.univ.image c, fun R₁ hR hF X₁ f₁ π₁ j _ hj hf => ?_⟩
  subst hj
  let c₁ : Fin n → R₁ := fun a => ⟨c a, hF (by simp)⟩
  refine ⟨secComb f₁ c₁ fun a => Cartier.secPull (τ a) π₁, fun x => ?_⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ ((j ≫ π₁) x)))
  have h1 : (j ≫ π₁) ⁻¹ᵁ L.U i ≤ (L.pull (j ≫ π₁)).U fun _ => i := (Cartier.pull_U L _ fun _ => i).ge
  have h2 : (j ≫ π₁) ⁻¹ᵁ L.U i ≤ ((L.pull π₁).pull j).U fun _ _ => i :=
    (j.preimage_mono (Cartier.pull_U L π₁ fun _ => i).ge).trans
      (Cartier.pull_U (L.pull π₁) j fun _ _ => i).ge
  refine ⟨(j ≫ π₁) ⁻¹ᵁ L.U i, fun _ => i, fun _ _ => i, h1, h2, 1, hi, ?_⟩
  refine Eq.trans ?_ (one_mul _).symm
  refine (congrArg (resG X h1) (hσ fun _ => i)).trans ?_
  exact resG_comb_pull R₁.subtype f f₁ π₁ j hf c₁ (fun a => (τ a).f i)
    (Cartier.pull_U L π₁ fun _ => i).le (Cartier.pull_U (L.pull π₁) j fun _ _ => i).le
    (Cartier.pull_U L (j ≫ π₁) fun _ => i).le h1 h2

end GlobalTheory.LogPair
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutLineBundleStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.spread_out_line_bundle : ∀ (k : Type) [Field k] (R₀ : Subring k) (X X₀ : Scheme.{0}) (f : X ⟶ Sp k) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [IsProper f₀] (L : LB X₀) (σ : (L.pull π).Sec), IsPullback π f f₀ (spMap R₀.subtype) → L.IsLB → ∃ F : Finset k, ∀ (R₁ : Subring k) (hR : R₀ ≤ R₁), (F : Set k) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion hR)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ τ : (L.pull π₁).Sec, SameDiv σ (Cartier.secPull τ j) := by
  first | exact @_root_.GlobalTheory.LogPair.exists_finset_sec_descends | exact _root_.GlobalTheory.LogPair.exists_finset_sec_descends | (intros; apply _root_.GlobalTheory.LogPair.exists_finset_sec_descends <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SameDivisorTrans
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.same_divisor_trans : ∀ (X : Scheme.{0}) (L M N : LB X) (σ : L.Sec) (τ : M.Sec) (υ : N.Sec), M.IsLB → SameDiv σ τ → SameDiv τ υ → SameDiv σ υ := by
  first | exact @_root_.GlobalTheory.LogPair.SameDiv.trans_of_isLB | exact _root_.GlobalTheory.LogPair.SameDiv.trans_of_isLB | (intros; apply _root_.GlobalTheory.LogPair.SameDiv.trans_of_isLB <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutMorphism
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.SecDescent

theorem lbSec_descends_to_subring : ∀ (k : Type) [Field k] (R₀ : Subring k) (X X₀ : Scheme.{0}) (f : X ⟶ Sp k) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [IsProper f₀] (L : LB X) (hL : L.IsLB) (σ : L.Sec), IsPullback π f f₀ (spMap R₀.subtype) → ∃ F : Finset k, ∀ (R₁ : Subring k) (hR : R₀ ≤ R₁), (F : Set k) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion hR)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ (L₁ : LB X₁) (h₁ : L₁.IsLB) (σ₁ : L₁.Sec), cls L hL = CechPic.pull j (cls L₁ h₁) ∧ SameDiv σ (Cartier.secPull σ₁ j) := by
  intro k _ R₀ X X₀ f f₀ π _ L hL σ hp
  classical
  obtain ⟨S, hS⟩ := GlobalTheory.LBLimit.lb_descends_to_fg_subring k R₀ X X₀ f f₀ π L hp hL
  let R' : Subring k := R₀ ⊔ Subring.closure (S : Set k)
  have h' : R₀ ≤ R' := le_sup_left
  have hs' : (S : Set k) ⊆ R' := fun x hx => (le_sup_right : _ ≤ R') (Subring.subset_closure hx)
  let a : Sp R' ⟶ Sp R₀ := spMap (Subring.inclusion h')
  have e₁ : spMap R'.subtype ≫ a = spMap R₀.subtype := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have PX' := IsPullback.of_hasPullback f₀ a
  let j' : X ⟶ pullback f₀ a := PX'.lift π (f ≫ spMap R'.subtype) (by rw [Category.assoc, e₁, hp.w])
  have hj₁ : j' ≫ pullback.fst f₀ a = π := PX'.lift_fst _ _ _
  have hj₂ : j' ≫ pullback.snd f₀ a = f ≫ spMap R'.subtype := PX'.lift_snd _ _ _
  obtain ⟨L', hL', hI⟩ := hS R' h' hs' _ _ _ j' PX' hj₁ hj₂
  have hLj : (L'.pull j').IsLB := LB.isLB_pull hL' j'
  obtain ⟨τ, hστ⟩ := GlobalTheory.T.exists_sectionsHaveSameZeroScheme_of_lineBundleIso X L (L'.pull j') σ hL hLj hI
  have QX : IsPullback j' f (pullback.snd f₀ a) (spMap R'.subtype) :=
    IsPullback.of_right (by rw [hj₁, e₁]; exact hp) hj₂ PX'
  obtain ⟨F₂, hF₂⟩ := GlobalTheory.T.spread_out_line_bundle k R' X (pullback f₀ a) f (pullback.snd f₀ a) j' L' τ QX hL'
  refine ⟨S ∪ F₂, fun R₁ hR hs X₁ f₁ π₁ j hp₁ hjπ hjf => ?_⟩
  rw [Finset.coe_union, Set.union_subset_iff] at hs
  have hle : R' ≤ R₁ := sup_le hR (Subring.closure_le.2 hs.1)
  let b : Sp R₁ ⟶ Sp R' := spMap (Subring.inclusion hle)
  have e₂ : b ≫ a = spMap (Subring.inclusion hR) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have e₃ : spMap R₁.subtype ≫ b = spMap R'.subtype := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let q : X₁ ⟶ pullback f₀ a := PX'.lift π₁ (f₁ ≫ b) (by rw [Category.assoc, e₂, hp₁.w])
  have hq₁ : q ≫ pullback.fst f₀ a = π₁ := PX'.lift_fst _ _ _
  have hq₂ : q ≫ pullback.snd f₀ a = f₁ ≫ b := PX'.lift_snd _ _ _
  have QX₁ : IsPullback q f₁ (pullback.snd f₀ a) b :=
    IsPullback.of_right (by rw [hq₁, e₂]; exact hp₁) hq₂ PX'
  have hjq : j ≫ q = j' := by
    apply PX'.hom_ext
    · rw [Category.assoc, hq₁, hjπ, hj₁]
    · rw [Category.assoc, hq₂, reassoc_of% hjf, e₃, hj₂]
  obtain ⟨τ₁, hτ₁⟩ := hF₂ R₁ hle hs.2 X₁ f₁ q j QX₁ hjq hjf
  refine ⟨L'.pull q, LB.isLB_pull hL' q, τ₁, ?_, GlobalTheory.T.same_divisor_trans X L (L'.pull j') _ σ τ _ hLj hστ hτ₁⟩
  rw [(CechPic.cls_eq_iff hL hLj).2 hI, CechPic.cls_pull hL' j' hLj, CechPic.cls_pull hL' q, ← hjq,
    CechPic.pull_comp]

end GlobalTheory.SecDescent
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutMorphismStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.spread_out_line_bundle_section : ∀ (k : Type) [Field k] (R₀ : Subring k) (X X₀ : Scheme.{0}) (f : X ⟶ Sp k) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [IsProper f₀] (L : LB X) (hL : L.IsLB) (σ : L.Sec), IsPullback π f f₀ (spMap R₀.subtype) → ∃ F : Finset k, ∀ (R₁ : Subring k) (hR : R₀ ≤ R₁), (F : Set k) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion hR)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ (L₁ : LB X₁) (h₁ : L₁.IsLB) (σ₁ : L₁.Sec), cls L hL = CechPic.pull j (cls L₁ h₁) ∧ SameDiv σ (Cartier.secPull σ₁ j) := by
  first | exact @_root_.GlobalTheory.SecDescent.lbSec_descends_to_subring | exact _root_.GlobalTheory.SecDescent.lbSec_descends_to_subring | (intros; apply _root_.GlobalTheory.SecDescent.lbSec_descends_to_subring <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutSmoothProper
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem exists_finiteType_subring_ge_finset {k : Type} [CommRing k] (R₀ : Subring k)
    (h : Algebra.FiniteType ℤ R₀) (F : Finset k) :
    ∃ R : Subring k, R₀ ≤ R ∧ (F : Set k) ⊆ R ∧ Algebra.FiniteType ℤ R := by
  have h0 : (subalgebraOfSubring R₀).FG := (Subalgebra.fg_iff_finiteType _).2 h
  have h1 : (subalgebraOfSubring R₀ ⊔ Algebra.adjoin ℤ (F : Set k)).FG :=
    h0.sup (Subalgebra.fg_adjoin_finset F)
  refine ⟨(subalgebraOfSubring R₀ ⊔ Algebra.adjoin ℤ (F : Set k)).toSubring, ?_, ?_,
    (Subalgebra.fg_iff_finiteType _).1 h1⟩
  · intro x hx
    exact (le_sup_left : subalgebraOfSubring R₀ ≤ _) hx
  · intro x hx
    exact (le_sup_right : Algebra.adjoin ℤ (F : Set k) ≤ _) (Algebra.subset_adjoin hx)

theorem exists_model_with_sections : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k), Smooth f → IsProper f → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : ∀ i, (L i).IsLB) (M : LB X) (hM : M.IsLB), ∃ (R : Subring k) (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R) (π : X ⟶ X₁) (L₁ : Fin s → LB X₁) (σ₁ : ∀ i, (L₁ i).Sec) (h₁ : ∀ i, (L₁ i).IsLB) (M₁ : LB X₁) (hM₁ : M₁.IsLB), Algebra.FiniteType ℤ R ∧ Smooth f₁ ∧ IsProper f₁ ∧ IsPullback π f f₁ (spMap R.subtype) ∧ (∀ i, cls (L i) (h i) = CechPic.pull π (cls (L₁ i) (h₁ i))) ∧ (∀ i, SameDiv (σ i) (Cartier.secPull (σ₁ i) π)) ∧ cls M hM = CechPic.pull π (cls M₁ hM₁) := by
  classical
  intro k _ X f hsm hpr s L σ h M hM
  obtain ⟨R₀, X₀, f₀, π₀, hft, hsm₀, hpr₀, hpb⟩ := GlobalTheory.T.exists_smooth_proper_model_finitelyGenerated_subring k X f hsm hpr
  choose F hF using fun i => GlobalTheory.T.spread_out_line_bundle_section k R₀ X X₀ f f₀ π₀ (L i) (h i) (σ i) hpb
  obtain ⟨G, hG⟩ := GlobalTheory.T.spread_out_line_bundle_section k R₀ X X₀ f f₀ π₀ M hM 0 hpb
  obtain ⟨R, hR, hFR, hRft⟩ :=
    exists_finiteType_subring_ge_finset R₀ hft (G ∪ Finset.univ.biUnion F)
  have hsp : spMap R.subtype ≫ spMap (Subring.inclusion hR) = spMap R₀.subtype := by
    simp only [spMap]
    rw [← Spec.map_comp]
    rfl
  have P := IsPullback.of_hasPullback f₀ (spMap (Subring.inclusion hR))
  let j : X ⟶ pullback f₀ (spMap (Subring.inclusion hR)) :=
    pullback.lift π₀ (f ≫ spMap R.subtype) (by rw [Category.assoc, hsp, hpb.w])
  have hj1 : j ≫ pullback.fst _ _ = π₀ := pullback.lift_fst _ _ _
  have hj2 : j ≫ pullback.snd _ _ = f ≫ spMap R.subtype := pullback.lift_snd _ _ _
  have hGR : (G : Set k) ⊆ R := fun x hx => hFR (by
    simp only [Finset.coe_union, Set.mem_union]; exact Or.inl hx)
  have hFi : ∀ i, (F i : Set k) ⊆ R := fun i x hx => hFR (by
    rw [Finset.mem_coe, Finset.mem_union]
    exact Or.inr (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hx⟩))
  choose L₁ h₁ σ₁ hc hd using fun i => hF i R hR (hFi i) _ _ _ j P hj1 hj2
  obtain ⟨M₁, hM₁, -, hMc, -⟩ := hG R hR hGR _ _ _ j P hj1 hj2
  refine ⟨R, _, pullback.snd f₀ (spMap (Subring.inclusion hR)), j, L₁, σ₁, h₁, M₁, hM₁, hRft,
    inferInstance, inferInstance, ?_, hc, hd, hMc⟩
  exact IsPullback.of_right (by rw [hj1, hsp]; exact hpb) hj2 P

end GlobalTheory.LogPair
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutSmoothProperStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.spread_out_smooth_proper : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k), Smooth f → IsProper f → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : ∀ i, (L i).IsLB) (M : LB X) (hM : M.IsLB), ∃ (R : Subring k) (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R) (π : X ⟶ X₁) (L₁ : Fin s → LB X₁) (σ₁ : ∀ i, (L₁ i).Sec) (h₁ : ∀ i, (L₁ i).IsLB) (M₁ : LB X₁) (hM₁ : M₁.IsLB), Algebra.FiniteType ℤ R ∧ Smooth f₁ ∧ IsProper f₁ ∧ IsPullback π f f₁ (spMap R.subtype) ∧ (∀ i, cls (L i) (h i) = CechPic.pull π (cls (L₁ i) (h₁ i))) ∧ (∀ i, SameDiv (σ i) (Cartier.secPull (σ₁ i) π)) ∧ cls M hM = CechPic.pull π (cls M₁ hM₁) := by
  first | exact @_root_.GlobalTheory.LogPair.exists_model_with_sections | exact _root_.GlobalTheory.LogPair.exists_model_with_sections | (intros; apply _root_.GlobalTheory.LogPair.exists_model_with_sections <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RelativeSncSameDivisor
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.relative_snc_same_divisor : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (L' : Fin s → LB X) (σ' : ∀ i, (L' i).Sec), RelSnc f d L σ → (∀ i, (L' i).IsLB) → (∀ i, SameDiv (σ i) (σ' i)) → RelSnc f d L' σ' := by
  first | exact @_root_.GlobalTheory.LogPair.relSnc_of_sameDiv | exact _root_.GlobalTheory.LogPair.relSnc_of_sameDiv | (intros; apply _root_.GlobalTheory.LogPair.relSnc_of_sameDiv <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutRelativeSnc
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ModelSnc

def adjInv {k : Type} [Field k] (R : Subring k) (a : k) : Subring k :=
  (Polynomial.eval₂RingHom R.subtype a⁻¹).range

def toAdjInv {k : Type} [Field k] (R : Subring k) (a : k) : R →+* adjInv R a :=
  (Polynomial.eval₂RingHom R.subtype a⁻¹).rangeRestrict.comp Polynomial.C

theorem subtype_comp_toAdjInv {k : Type} [Field k] (R : Subring k) (a : k) :
    (adjInv R a).subtype.comp (toAdjInv R a) = R.subtype := by
  ext r
  change Polynomial.eval₂ R.subtype a⁻¹ (Polynomial.C r) = (r : k)
  simp

theorem isUnit_toAdjInv {k : Type} [Field k] (R : Subring k) (a : R) (ha : (a : k) ≠ 0) :
    IsUnit (toAdjInv R (a : k) a) := by
  refine IsUnit.of_mul_eq_one ((Polynomial.eval₂RingHom R.subtype (a : k)⁻¹).rangeRestrict Polynomial.X) ?_
  apply Subtype.ext
  change Polynomial.eval₂ R.subtype (a : k)⁻¹ (Polynomial.C a) * Polynomial.eval₂ R.subtype (a : k)⁻¹ Polynomial.X = 1
  simp [ha]

theorem finiteType_adjInv {k : Type} [Field k] (R : Subring k) (hR : Algebra.FiniteType ℤ R) (a : k) :
    Algebra.FiniteType ℤ (adjInv R a) := by
  haveI := hR
  have hP : Algebra.FiniteType ℤ (Polynomial R) := inferInstance
  exact @Algebra.FiniteType.of_surjective _ _ _ _ _ _ _ _ hP
    (Polynomial.eval₂RingHom R.subtype a⁻¹).rangeRestrict.toIntAlgHom
    (Polynomial.eval₂RingHom R.subtype a⁻¹).rangeRestrict_surjective

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

end GlobalTheory.ModelSnc

end

namespace GlobalTheory.ModelSnc

theorem exists_model_relSnc : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k) (d : ℕ), IsProper f → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : RelSnc f d L σ) (M : LB X) (hM : M.IsLB), ∃ (R : Subring k) (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R) (π : X ⟶ X₁) (L₁ : Fin s → LB X₁) (σ₁ : ∀ i, (L₁ i).Sec) (h₁ : RelSnc f₁ d L₁ σ₁) (M₁ : LB X₁) (hM₁ : M₁.IsLB), Algebra.FiniteType ℤ R ∧ IsProper f₁ ∧ IsPullback π f f₁ (spMap R.subtype) ∧ (∀ i, cls (L i) (h.isLB i) = CechPic.pull π (cls (L₁ i) (h₁.isLB i))) ∧ cls M hM = CechPic.pull π (cls M₁ hM₁) := by
  intro k _ X f d hf s L σ h M hM
  haveI : SmoothOfRelativeDimension d f := GlobalTheory.T.smoothOfRelativeDimension_of_relSncDivisor k X f d s L σ h
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth d f
  obtain ⟨R, X₁, f₁, π, L₁, σ₁, h₁, M₁, hM₁, hR, hsm₁, hpr₁, hpb, hcl, hsame, hclM⟩ :=
    GlobalTheory.T.spread_out_smooth_proper k X f hsm hf s L σ h.isLB M hM
  have hX : RelSnc f d (fun i => (L₁ i).pull π) (fun i => Cartier.secPull (σ₁ i) π) :=
    GlobalTheory.T.relative_snc_same_divisor k X f d s L σ _ _ h (fun i => pull_isLB (h₁ i) π) hsame
  haveI := hsm₁
  haveI := hpr₁
  obtain ⟨a, ha, hsp⟩ := GlobalTheory.T.relative_snc_generic_spread R k R.subtype X₁ X f₁ f π d s L₁ σ₁ hpb h₁ hX
  set R' := adjInv R (a : k)
  set χ := toAdjInv R (a : k)
  have hχ : IsUnit (χ a) := isUnit_toAdjInv R a ha
  let g : pullback f₁ (spMap χ) ⟶ Sp R' := pullback.snd f₁ (spMap χ)
  let ρ : pullback f₁ (spMap χ) ⟶ X₁ := pullback.fst f₁ (spMap χ)
  have hρ : IsPullback ρ g f₁ (spMap χ) := IsPullback.of_hasPullback f₁ (spMap χ)
  have hZ := hsp R' χ hχ _ g ρ hρ
  have hcomp : spMap R.subtype = spMap R'.subtype ≫ spMap χ := by
    rw [← spMap_comp, subtype_comp_toAdjInv]
  have hw : π ≫ f₁ = (f ≫ spMap R'.subtype) ≫ spMap χ := by
    rw [Category.assoc, ← hcomp]; exact hpb.w
  let π' : X ⟶ pullback f₁ (spMap χ) := pullback.lift π (f ≫ spMap R'.subtype) hw
  have hπ' : π' ≫ ρ = π := pullback.lift_fst _ _ _
  have hg' : π' ≫ g = f ≫ spMap R'.subtype := pullback.lift_snd _ _ _
  have hpb' : IsPullback π' f g (spMap R'.subtype) := by
    refine IsPullback.of_right ?_ hg' hρ
    rw [hπ', ← hcomp]; exact hpb
  haveI : IsProper g := inferInstance
  refine ⟨R', pullback f₁ (spMap χ), g, π', fun i => (L₁ i).pull ρ, fun i => Cartier.secPull (σ₁ i) ρ, hZ,
    M₁.pull ρ, pull_isLB hM₁ ρ, finiteType_adjInv R hR _, inferInstance, hpb', fun i => ?_, ?_⟩
  · rw [hcl i, ← hπ', pull_comp]; rfl
  · rw [hclM, ← hπ', pull_comp]; rfl

end GlobalTheory.ModelSnc
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutRelativeSncStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.spread_out_relative_snc : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k) (d : ℕ), IsProper f → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : RelSnc f d L σ) (M : LB X) (hM : M.IsLB), ∃ (R : Subring k) (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R) (π : X ⟶ X₁) (L₁ : Fin s → LB X₁) (σ₁ : ∀ i, (L₁ i).Sec) (h₁ : RelSnc f₁ d L₁ σ₁) (M₁ : LB X₁) (hM₁ : M₁.IsLB), Algebra.FiniteType ℤ R ∧ IsProper f₁ ∧ IsPullback π f f₁ (spMap R.subtype) ∧ (∀ i, cls (L i) (h.isLB i) = CechPic.pull π (cls (L₁ i) (h₁.isLB i))) ∧ cls M hM = CechPic.pull π (cls M₁ hM₁) := by
  first | exact @_root_.GlobalTheory.ModelSnc.exists_model_relSnc | exact _root_.GlobalTheory.ModelSnc.exists_model_relSnc | (intros; apply _root_.GlobalTheory.ModelSnc.exists_model_relSnc <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair

namespace GlobalTheory.Div

theorem vanishing_ample_snc_charZero : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) (f : X ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d f], IsProjOver f → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : RelSnc f d L σ), ∀ (K : CanonLB f d) (M A : LB X) (hM : M.IsLB) (hA : IsAmpleLB A) (r : ℕ) (b : Fin s → ℕ), 0 < r → (∀ i, b i < r) → r • cls M hM = r • cls K.bundle K.isLB + ∑ i, b i • cls (L i) (h.isLB i) + cls A hA.isLB → ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod M) q) := by
  intro k _ _ X f d _ hproj s L σ h K M A hM hA r b hr hb hcls q hq
  have hprop : IsProper f := GlobalTheory.SchemeWords.isProper_of_isProjOver hproj
  obtain ⟨R, X₁, f₁, π, L₁, σ₁, h₁, M₁, hM₁, hft, hprop₁, hpb, hL, hMc⟩ :=
    GlobalTheory.T.spread_out_relative_snc k X f d hprop s L σ h M hM
  haveI : SmoothOfRelativeDimension d f₁ := GlobalTheory.T.smoothOfRelativeDimension_of_relSncDivisor R X₁ f₁ d s L₁ σ₁ h₁
  haveI : IsProper f₁ := hprop₁
  obtain ⟨K₁⟩ := (CanonLB.nonempty : Nonempty (CanonLB f₁ d))
  obtain ⟨A₁, hA₁, hA₁c⟩ := cls_surj (r • cls M₁ hM₁ - r • cls K₁.bundle K₁.isLB -
    ∑ i, b i • cls (L₁ i) (h₁.isLB i))
  have hK : cls K.bundle K.isLB = CechPic.pull π (cls K₁.bundle K₁.isLB) :=
    GlobalTheory.T.cechPicardClass_canonicalBundle_baseChange R k R.subtype X₁ X f₁ f π d K₁ K hpb
  have hApull : cls (A₁.pull π) (pull_isLB hA₁ π) = cls A hA.isLB := by
    have e : cls A hA.isLB = r • cls M hM - r • cls K.bundle K.isLB - ∑ i, b i • cls (L i) (h.isLB i) := by
      rw [hcls]; abel
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, cls_pull hA₁, hA₁c, map_sub, map_sub, map_nsmul, map_nsmul, map_sum, ← hMc, ← hK]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_nsmul, ← hL i]
  have hAamp : IsAmpleLB (A₁.pull π) :=
    IsAmpleLB.of_lbIso hA (pull_isLB hA₁ π) ((cls_eq_iff _ _).1 hApull)
  have hcls₁ : r • cls M₁ hM₁ = r • cls K₁.bundle K₁.isLB + ∑ i, b i • cls (L₁ i) (h₁.isLB i) +
      cls A₁ hA₁ := by
    rw [hA₁c]; abel
  have hv := GlobalTheory.T.kawamata_viehweg_spreading R k R.subtype X₁ X f₁ f π d hft Subtype.coe_injective hpb s L₁ σ₁ h₁ K₁
    M₁ A₁ hM₁ hA₁ r b hAamp hr hb hcls₁ q hq
  have hMM : cls (M₁.pull π) (pull_isLB hM₁ π) = cls M hM := by rw [cls_pull hM₁, hMc]
  exact GlobalTheory.T.cohomology_subsingleton_of_cechPicardClass_eq X (M₁.pull π) M _ hM hMM q hv

end GlobalTheory.Div
