module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtProps
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.RelDim
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.NormLtOneOfIrreducible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianSemidefiniteNullRadical
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemistableSpecialFibreProperty

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.CompGood
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.CompSm
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.ConnectedSpacePullbackOfIsIntegral
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.IsOpenConnectedComponentOfNoetherianSpace
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace CrystallineSemistableComparison

theorem isOpen_connectedComponent_of_noetherianSpace {X : Type*} [TopologicalSpace X] [NoetherianSpace X]
    (x : X) : IsOpen (connectedComponent x) := by
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
  have h : (connectedComponent x)ᶜ =
      ⋃ Z ∈ {Z ∈ irreducibleComponents X | ¬ Z ⊆ connectedComponent x}, Z := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hy
      obtain ⟨Z, hZ, hyZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {y}
        isIrreducible_singleton
      refine ⟨Z, ⟨hZ, fun hsub ↦ hy (hsub (hyZ rfl))⟩, hyZ rfl⟩
    · rintro ⟨Z, ⟨hZ, hnot⟩, hyZ⟩ hy
      apply hnot
      have h1 : Z ⊆ connectedComponent y :=
        IsPreconnected.subset_connectedComponent (IsPreirreducible.isPreconnected hZ.1.2) hyZ
      rwa [← connectedComponent_eq hy] at h1
  have hc : IsClosed (connectedComponent x)ᶜ := by
    rw [h]
    exact (hfin.subset (by exact fun Z hZ ↦ hZ.1)).isClosed_biUnion fun Z hZ ↦ isClosed_of_mem_irreducibleComponents Z hZ.1
  exact isClosed_compl_iff.mp hc

theorem finite_connectedComponents_of_noetherianSpace (X : Type*) [TopologicalSpace X] [NoetherianSpace X] :
    Finite (_root_.ConnectedComponents X) := by
  have : DiscreteTopology (_root_.ConnectedComponents X) := by
    rw [discreteTopology_iff_isOpen_singleton]
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [← ConnectedComponents.isQuotientMap_coe.isOpen_preimage, connectedComponents_preimage_singleton]
    exact isOpen_connectedComponent_of_noetherianSpace x
  have : CompactSpace (_root_.ConnectedComponents X) := inferInstance
  exact finite_of_compact_of_discrete

theorem exists_isSum_components (X : Scheme.{0}) [NoetherianSpace X] :
    ∃ (r : ℕ) (U : Fin r → X.Opens), IsSum (fun a ↦ (U a).ι) ∧ ∀ a, ConnectedSpace (U a).toScheme := by
  have := finite_connectedComponents_of_noetherianSpace X
  let e := Finite.equivFin (_root_.ConnectedComponents X)
  have hopen : ∀ c : _root_.ConnectedComponents X, IsOpen (_root_.ConnectedComponents.mk ⁻¹' {c} : Set X) := by
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [connectedComponents_preimage_singleton]
    exact isOpen_connectedComponent_of_noetherianSpace x
  let U : Fin (Nat.card (_root_.ConnectedComponents X)) → X.Opens := fun a ↦ ⟨_, hopen (e.symm a)⟩
  refine ⟨_, U, ⟨fun a ↦ inferInstance, fun x ↦ ⟨e (_root_.ConnectedComponents.mk x), ?_⟩, fun a b hab ↦ ?_⟩, fun a ↦ ?_⟩
  · rw [Scheme.Opens.range_ι]
    show _root_.ConnectedComponents.mk x = e.symm (e (_root_.ConnectedComponents.mk x))
    simp
  · rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    refine Set.disjoint_left.mpr fun y hy hy' ↦ hab (e.symm.injective ?_)
    exact (hy : _root_.ConnectedComponents.mk y = _).symm.trans hy'
  · obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (e.symm a)
    have hU : ((U a : X.Opens) : Set X) = connectedComponent x := by
      show _root_.ConnectedComponents.mk ⁻¹' {e.symm a} = _
      rw [← hx, connectedComponents_preimage_singleton]
    have : ConnectedSpace ((U a : X.Opens) : Set X) := by
      rw [hU]; exact isConnected_iff_connectedSpace.mp isConnected_connectedComponent
    exact this

end CrystallineSemistableComparison
end
end

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace CrystallineSemistableComparison

theorem connectedSpace_pullback_of_isIntegral {O : Type} [CommRing O] [IsDomain O] {X T : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of O)) (j : T ⟶ Spec (CommRingCat.of O)) [IsOpenImmersion j] [Nonempty T]
    [IsIntegral X] (hp : GeneralizingMap p) : ConnectedSpace ↥(pullback p j) := by
  have hne : Nonempty ↥(pullback p j) := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have hη : genericPoint (Spec (CommRingCat.of O)) ⤳ p x := genericPoint_specializes _
    obtain ⟨x', -, hx'⟩ := hp hη
    have hmem : genericPoint (Spec (CommRingCat.of O)) ∈ Set.range j := by
      obtain ⟨t⟩ := (inferInstance : Nonempty T)
      exact ((genericPoint_spec (Spec (CommRingCat.of O))).mem_open_set_iff j.isOpenEmbedding.isOpen_range).mpr
        ⟨j t, trivial, t, rfl⟩
    obtain ⟨t, ht⟩ := hmem
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback x' t (hx'.trans ht.symm)
    exact ⟨z⟩
  have hirr : IsPreirreducible (Set.univ : Set ↥(pullback p j)) := by
    have h := (IrreducibleSpace.isIrreducible_univ X).2.preimage (pullback.fst p j).isOpenEmbedding
    simpa using h
  have : PreirreducibleSpace ↥(pullback p j) := ⟨hirr⟩
  have : IrreducibleSpace ↥(pullback p j) := ⟨hne⟩
  infer_instance

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

abbrev Model.sub (M : Model l K) (U : M.X.Opens) : Model l K := ⟨U.toScheme, U.ι ≫ M.p⟩

theorem compM_of (G : Model l K → Prop)
    (hj : IsOpenImmersion (Spec.map (CommRingCat.ofHom (OK l K).subtype)))
    (hsub : ∀ M, G M → ∀ U : M.X.Opens, IsClosed (U : Set M.X) → G (M.sub U))
    (hN : ∀ M, G M → NoetherianSpace M.X)
    (hF : ∀ M, G M → GlobalTheory.IsNormalScheme M.X ∧ IsLocallyNoetherian M.X ∧ GeneralizingMap M.p ∧ Smooth M.q) :
    CompM G := by
  intro M hM
  have := hN M hM
  obtain ⟨r, U, hU, hc⟩ := exists_isSum_components M.X
  have hcl : ∀ a, IsClosed (U a : Set M.X) := by
    intro a
    have hrange := hU.2.1

    have : (U a : Set M.X)ᶜ = ⋃ b ∈ {b | b ≠ a}, (U b : Set M.X) := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
      constructor
      · intro hx
        obtain ⟨b, hb⟩ := hU.2.1 x
        rw [Scheme.Opens.range_ι] at hb
        exact ⟨b, fun h ↦ hx (h ▸ hb), hb⟩
      · rintro ⟨b, hba, hb⟩ hx
        have := hU.2.2 b a hba
        rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι] at this
        exact Set.disjoint_left.mp this hb hx
    rw [← isOpen_compl_iff, this]
    exact isOpen_biUnion fun b _ ↦ (U b).isOpen
  have hG : ∀ a, G (M.sub (U a)) := fun a ↦ hsub M hM (U a) (hcl a)
  have hconn : ∀ a, ∃ d, (M.sub (U a)).Conn d := by
    intro a
    obtain ⟨hnorm, hnoeth, hgen, hsm⟩ := hF _ (hG a)
    have : ConnectedSpace (M.sub (U a)).X := hc a
    have : IsIntegral (M.sub (U a)).X := GlobalTheory.IsNormalScheme.isIntegral_of_connectedSpace _
    have : ConnectedSpace (M.sub (U a)).gen :=
      connectedSpace_pullback_of_isIntegral (M.sub (U a)).p _ hgen
    obtain ⟨d, hd⟩ := exists_smoothOfRelativeDimension (M.sub (U a)).q
    exact ⟨d, inferInstance, hd⟩
  choose d hd using hconn
  exact ⟨r, fun a ↦ M.sub (U a), d, fun a ↦ (U a).ι, fun a ↦ rfl, hU, fun a ↦ ⟨hG a, hd a⟩⟩

end CrystallineSemistableComparison
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.IsStrictlySemistableCompOpenImmersion
noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace CrystallineSemistableComparison

set_option maxHeartbeats 800000 in
theorem isStrictlySemistable_comp_openImmersion {O : Type} [CommRing O] (ϖ : O) {X Y : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of O)) (h : GlobalTheory.Et.IsStrictlySemistable ϖ p) (f : Y ⟶ X) [IsOpenImmersion f] :
    GlobalTheory.Et.IsStrictlySemistable ϖ (f ≫ p) := by
  intro y
  obtain ⟨U, hU, hxU, m, r, h1r, hrm, ψ, hψ, hcomp⟩ := h (f.base y)
  obtain ⟨g, hg, hyg⟩ := hU.exists_basicOpen_le (V := f.opensRange) ⟨f.base y, y, rfl⟩ hxU
  haveI := hU.isLocalization_basicOpen g
  haveI : IsIso (f.app (X.basicOpen g)) := f.isIso_app _ hg
  refine ⟨(Opens.map f.base).obj (X.basicOpen g), (hU.basicOpen g).preimage_of_isOpenImmersion f hg, hyg,
    m, r, h1r, hrm,
    (f.app (X.basicOpen g)).hom.comp ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.comp ψ), ?_, ?_⟩
  · have hL : (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.Etale :=
      RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway g)
    have h2 := RingHom.Etale.stableUnderComposition _ _ hψ hL
    exact (RingHom.Etale.respectsIso.cancel_right_isIso (CommRingCat.ofHom _) (f.app (X.basicOpen g))).mpr h2
  · rw [RingHom.comp_assoc, RingHom.comp_assoc, hcomp, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
    congr 1
    have key : ∀ e₁ e₂, p.appLE ⊤ U e₁ ≫ X.presheaf.map (homOfLE (X.basicOpen_le g)).op ≫
        f.app (X.basicOpen g) = (f ≫ p).appLE ⊤ ((Opens.map f.base).obj (X.basicOpen g)) e₂ := by
      intro e₁ e₂
      rw [← Category.assoc, Scheme.Hom.appLE_map, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    exact congrArg (fun t => (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ t) (key _ _)

end CrystallineSemistableComparison
end
end

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem Model.good_sub (M : Model l K) (hM : M.Good) (U : M.X.Opens) (hU : IsClosed (U : Set M.X)) :
    (M.sub U).Good := by
  obtain ⟨⟨N, i, hi, hcomp⟩, ϖ, hϖ, hss⟩ := hM
  have : IsClosedImmersion U.ι := .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hU)
  refine ⟨⟨N, U.ι ≫ i, inferInstance, by rw [Category.assoc, hcomp]⟩, ϖ, hϖ, ?_⟩
  exact isStrictlySemistable_comp_openImmersion ϖ M.p hss U.ι

theorem Model.sm_sub (M : Model l K) (hM : M.Sm) (U : M.X.Opens) (hU : IsClosed (U : Set M.X)) :
    (M.sub U).Sm := by
  have := hM.2
  exact ⟨M.good_sub hM.1 U hU, inferInstanceAs (Smooth (U.ι ≫ M.p))⟩

theorem Model.noetherianSpace [FiniteDimensional ℚ_[l] K] (M : Model l K) (hM : M.Good) :
    NoetherianSpace M.X := by
  have := OK_dvr (l := l) (K := K)
  obtain ⟨⟨N, i, hi, hcomp⟩, -⟩ := hM
  have : IsProper (PSpace.str (OK l K) N) := isProper_str _ N
  have : IsLocallyNoetherian M.X := by
    exact LocallyOfFiniteType.isLocallyNoetherian (i ≫ PSpace.str (OK l K) N)
  have : CompactSpace M.X := by
    exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str (OK l K) N)
  have : IsNoetherian M.X := {}
  infer_instance

theorem isOpenImmersion_gen [FiniteDimensional ℚ_[l] K] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (OK l K).subtype)) := by
  have := OK_dvr (l := l) (K := K)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (OK l K)
  have := OK_away hϖ
  exact IsOpenImmersion.of_isLocalization (S := K) ϖ

theorem compSm : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
    CompM (Model.Sm (l := l) (K := K)) := by
  intro l _ K _
  have := OK_dvr (l := l) (K := K)
  refine compM_of _ isOpenImmersion_gen (fun M hM U hU ↦ M.sm_sub hM U hU) (fun M hM ↦ M.noetherianSpace hM.1) ?_
  intro M hM
  have := hM.2
  have hS : GlobalTheory.IsNormalScheme (Spec (CommRingCat.of (OK l K))) := inferInstance
  refine ⟨GlobalTheory.isNormalScheme_of_smooth M.p, LocallyOfFiniteType.isLocallyNoetherian M.p,
    Flat.generalizingMap M.p, inferInstance⟩

end CrystallineSemistableComparison
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.SsModelAlgebraMapInjective
noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace CrystallineSemistableComparison

section Ring

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ)
  (m r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ m)

include hϖ h1 h2 in
theorem ssModel_isDomain : IsDomain (GlobalTheory.Et.ssModel O ϖ m r) := GlobalTheory.T.semistable_model_ring_isDomain O ϖ hϖ m r h1 h2

include hϖ h1 h2 in
theorem ssModel_algebraMap_ne_zero : algebraMap O (GlobalTheory.Et.ssModel O ϖ m r) ϖ ≠ 0 := by
  haveI := ssModel_isDomain O ϖ hϖ m r h1 h2
  intro h
  have h0 : ϖ ∈ nonZeroDivisors O := mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero
  have := GlobalTheory.LogCris.model_mul_eq_zero ϖ h0 (1 : GlobalTheory.Et.ssModel O ϖ m r) (by rw [h, zero_mul])
  exact one_ne_zero this

include hϖ h1 h2 in
theorem ssModel_algebraMap_injective : Function.Injective (algebraMap O (GlobalTheory.Et.ssModel O ϖ m r)) := by
  haveI := ssModel_isDomain O ϖ hϖ m r h1 h2
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  by_contra hc0
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 hϖ
  rw [map_mul, map_pow] at hc
  rcases mul_eq_zero.1 hc with h | h
  · exact (u.isUnit.map (algebraMap O _)).ne_zero h
  · exact ssModel_algebraMap_ne_zero O ϖ hϖ m r h1 h2 (pow_eq_zero_iff'.1 h).1

include hϖ h1 h2 in
theorem ssModel_normal (F : Type) [Field F] [Algebra O F] [IsLocalization.Away ϖ F] :
    IsDomain (GlobalTheory.Et.ssModel O ϖ m r) ∧ IsIntegrallyClosed (GlobalTheory.Et.ssModel O ϖ m r) := by
  have hd := ssModel_isDomain O ϖ hϖ m r h1 h2
  refine ⟨hd, ?_⟩
  have ht := ssModel_algebraMap_ne_zero O ϖ hϖ m r h1 h2
  have hred := GlobalTheory.T.semistable_special_fibre_property O ϖ hϖ m r h1 h2
  have hs := GlobalTheory.T.semistable_generic_fibre_localization O ϖ hϖ m r h1 h2 F
  haveI : Smooth (Spec.map (CommRingCat.ofHom (IsLocalization.Away.map F
      (Localization.Away (algebraMap O (GlobalTheory.Et.ssModel O ϖ m r) ϖ)) (algebraMap O (GlobalTheory.Et.ssModel O ϖ m r)) ϖ))) :=
    HasRingHomProperty.Spec_iff.mpr hs
  have hn := GlobalTheory.isNormalScheme_of_smooth (Spec.map (CommRingCat.ofHom (IsLocalization.Away.map F
      (Localization.Away (algebraMap O (GlobalTheory.Et.ssModel O ϖ m r) ϖ)) (algebraMap O (GlobalTheory.Et.ssModel O ϖ m r)) ϖ)))
  haveI : IsDomain (Localization.Away (algebraMap O (GlobalTheory.Et.ssModel O ϖ m r) ϖ)) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ht)
  have hic := (GlobalTheory.IsNormalScheme.spec_iff_of_isDomain
    (CommRingCat.of (Localization.Away (algebraMap O (GlobalTheory.Et.ssModel O ϖ m r) ϖ)))).mp hn
  exact GlobalTheory.T.isIntegrallyClosed_of_reduced_quotient_localization _ _ ht hred hic

include hϖ h1 h2 in
theorem ssModel_flat : Module.Flat O (GlobalTheory.Et.ssModel O ϖ m r) := by
  haveI := ssModel_isDomain O ϖ hϖ m r h1 h2
  have hi := ssModel_algebraMap_injective O ϖ hϖ m r h1 h2
  haveI : Module.IsTorsionFree O (GlobalTheory.Et.ssModel O ϖ m r) := Module.isTorsionFree_iff_algebraMap_injective.mpr hi
  infer_instance

end Ring

section Scheme

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} [FiniteDimensional ℚ_[l] K]

theorem good_isNormalScheme (M : Model l K) (hM : M.Good) : GlobalTheory.IsNormalScheme M.X := by
  haveI := OK_dvr (l := l) (K := K)
  obtain ⟨-, ϖ, hϖ, hss⟩ := hM
  haveI := OK_away hϖ
  refine GlobalTheory.IsNormalScheme.of_forall_exists_opens fun x => ?_
  obtain ⟨U, hU, hx, m, r, h1, h2, ψ, hψ, -⟩ := hss x
  refine ⟨U, hx, ?_⟩
  rw [GlobalTheory.IsNormalScheme.iff_spec_of_isAffineOpen hU]
  obtain ⟨hd, hic⟩ := ssModel_normal (OK l K) ϖ hϖ m r h1 h2 K
  haveI : Etale (Spec.map (CommRingCat.ofHom ψ)) := HasRingHomProperty.Spec_iff.mpr hψ
  exact GlobalTheory.isNormalScheme_of_smooth (Spec.map (CommRingCat.ofHom ψ))

theorem good_isLocallyNoetherian (M : Model l K) (hM : M.Good) : IsLocallyNoetherian M.X := by
  haveI := OK_dvr (l := l) (K := K)
  obtain ⟨-, ϖ, hϖ, hss⟩ := hM
  choose U hU hx m r h1 h2 ψ hψ _hc using hss
  refine isLocallyNoetherian_of_affine_cover (S := fun x => ⟨U x, hU x⟩) ?_ fun x => ?_
  · refine top_le_iff.mp fun y _ => ?_
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hx y⟩
  · letI := (ψ x).toAlgebra
    haveI : Algebra.Etale _ _ := hψ x
    exact Algebra.FiniteType.isNoetherianRing (GlobalTheory.Et.ssModel (OK l K) ϖ (m x) (r x)) Γ(M.X, U x)

theorem good_flat (M : Model l K) (hM : M.Good) : Flat M.p := by
  haveI := OK_dvr (l := l) (K := K)
  obtain ⟨-, ϖ, hϖ, hss⟩ := hM
  choose U hU hx m r h1 h2 ψ hψ hc using hss
  refine HasRingHomProperty.of_iSup_eq_top (P := @Flat) (U := fun x => ⟨U x, hU x⟩) ?_ fun x => ?_
  · refine top_le_iff.mp fun y _ => ?_
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hx y⟩
  · have e : (M.p.appLE ⊤ (U x) le_top) = (Scheme.ΓSpecIso (CommRingCat.of (OK l K))).hom ≫
        CommRingCat.ofHom ((ψ x).comp (algebraMap (OK l K) _)) := by
      rw [hc x]; simp
    show RingHom.Flat (M.p.appLE ⊤ (U x) le_top).hom
    rw [e, CommRingCat.hom_comp]
    refine RingHom.Flat.comp (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)) ?_
    haveI : Etale (Spec.map (CommRingCat.ofHom (ψ x))) := HasRingHomProperty.Spec_iff.mpr (hψ x)
    have hf : RingHom.Flat (ψ x) := HasRingHomProperty.Spec_iff.mp (inferInstance : Flat (Spec.map (CommRingCat.ofHom (ψ x))))
    refine RingHom.Flat.comp ?_ hf
    exact RingHom.flat_algebraMap_iff.mpr (ssModel_flat (OK l K) ϖ hϖ (m x) (r x) (h1 x) (h2 x))

end Scheme

end CrystallineSemistableComparison
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.SmoothSndOfIsStrictlySemistable
noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace CrystallineSemistableComparison

set_option maxHeartbeats 1000000 in
theorem smooth_snd_of_isStrictlySemistable {O K : Type} [CommRing O] [CommRing K] [Algebra O K] (ϖ : O)
    [IsLocalization.Away ϖ K] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O))
    (hss : GlobalTheory.Et.IsStrictlySemistable ϖ p)
    (hsm : ∀ m r : ℕ, 1 ≤ r → r ≤ m →
      (IsLocalization.Away.map K (Localization.Away (algebraMap O (GlobalTheory.Et.ssModel O ϖ m r) ϖ))
        (algebraMap O (GlobalTheory.Et.ssModel O ϖ m r)) ϖ).Smooth) :
    Smooth (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap O K)))) := by
  have : IsZariskiLocalAtSource @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
  set j := Spec.map (CommRingCat.ofHom (algebraMap O K))
  have hgen := IsPullback.of_hasPullback p j
  choose W hW hxW m r h1 h2 ψ hψe hψ using hss
  refine IsZariskiLocalAtSource.of_iSup_eq_top (fun x : X ↦ (pullback.fst p j) ⁻¹ᵁ W x) ?_ ?_
  · rw [eq_top_iff]
    intro z _
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨pullback.fst p j z, hxW _⟩
  intro x
  set B := GlobalTheory.Et.ssModel O ϖ (m x) (r x)
  set s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of O) := Spec.map (CommRingCat.ofHom (algebraMap O B))
  set φ : (W x).toScheme ⟶ Spec (CommRingCat.of B) := (hW x).isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (ψ x))
  have hφ : (W x).ι ≫ p = φ ≫ s := by
    have e1 : (W x).ι = (hW x).isoSpec.hom ≫ (hW x).fromSpec := by
      rw [← (hW x).isoSpec_inv_ι, Iso.hom_inv_id_assoc]
    have e2 := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top (Spec (CommRingCat.of O))) (hW x) le_top
    rw [e1, Category.assoc, ← e2]
    simp only [φ, s, Category.assoc, ← Spec.map_comp]
    congr 2
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact (hψ x).symm
  set Bϖ := Localization.Away (algebraMap O B ϖ)
  set σ : K →+* Bϖ := IsLocalization.Away.map K Bϖ (algebraMap O B) ϖ
  have hH : σ.comp (algebraMap O K) = (algebraMap B Bϖ).comp (algebraMap O B) := by
    simp only [σ, IsLocalization.Away.map]
    exact IsLocalization.map_comp _
  have : IsLocalization ((Submonoid.powers ϖ).map (algebraMap O B)) Bϖ := by
    rw [Submonoid.map_powers]; infer_instance
  have hpush := CommRingCat.isPushout_of_isLocalization (algebraMap O B) σ hH (Submonoid.powers ϖ)
  have hbot := isPullback_SpecMap_of_isPushout _ _ _ _ hpush
  have hout := (isPullback_morphismRestrict (pullback.fst p j) (W x)).paste_vert hgen
  rw [hφ] at hout
  have hw : ((pullback.fst p j ∣_ W x) ≫ φ) ≫ s =
      (((pullback.fst p j) ⁻¹ᵁ W x).ι ≫ pullback.snd p j) ≫ j := by
    rw [Category.assoc]; exact hout.w
  set t := hbot.lift _ _ hw
  have ht1 : t ≫ Spec.map (CommRingCat.ofHom (algebraMap B Bϖ)) = (pullback.fst p j ∣_ W x) ≫ φ :=
    hbot.lift_fst _ _ hw
  have ht2 : t ≫ Spec.map (CommRingCat.ofHom σ) = ((pullback.fst p j) ⁻¹ᵁ W x).ι ≫ pullback.snd p j :=
    hbot.lift_snd _ _ hw
  rw [← ht2] at hout
  have hleft := IsPullback.of_bot hout ht1.symm hbot
  have : Etale (Spec.map (CommRingCat.ofHom (ψ x))) := HasRingHomProperty.Spec_iff.mpr (hψe x)
  have : Etale φ := inferInstance
  have : Etale t := MorphismProperty.of_isPullback hleft ‹Etale φ›
  have : Smooth (Spec.map (CommRingCat.ofHom σ)) := HasRingHomProperty.Spec_iff.mpr (hsm _ _ (h1 x) (h2 x))
  rw [← ht2]
  infer_instance

end CrystallineSemistableComparison
end
end

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem Model.smooth_q [FiniteDimensional ℚ_[l] K] (M : Model l K) (hM : M.Good) : Smooth M.q := by
  obtain ⟨-, ϖ, hϖ, hss⟩ := hM
  have := OK_away hϖ
  have := OK_dvr (l := l) (K := K)
  exact smooth_snd_of_isStrictlySemistable ϖ M.p hss
    (fun m r h1 h2 ↦ GlobalTheory.T.semistable_generic_fibre_localization (OK l K) ϖ hϖ m r h1 h2 K)

theorem compGood : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
    CompM (Model.Good (l := l) (K := K)) := by
  intro l _ K _
  refine compM_of _ isOpenImmersion_gen (fun M hM U hU ↦ M.good_sub hM U hU) (fun M hM ↦ M.noetherianSpace hM) ?_
  intro M hM
  have := good_flat M hM
  exact ⟨good_isNormalScheme M hM, good_isLocallyNoetherian M hM, Flat.generalizingMap M.p, M.smooth_q hM⟩

end CrystallineSemistableComparison
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.CompactSpaceOfIsProjOver
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.IsOpenConnectedComponent
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.ExistsGalMapApply
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.IsOpenStabilizer
noncomputable section

open TensorProduct

namespace CrystallineSemistableComparison.GeoA

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Type) [CommRing R] [Algebra k R]

def act (σ : Ω ≃ₐ[k] Ω) : (Ω ⊗[k] R) ≃ₐ[k] (Ω ⊗[k] R) := Algebra.TensorProduct.congr σ AlgEquiv.refl

@[simp] theorem act_tmul (σ : Ω ≃ₐ[k] Ω) (a : Ω) (r : R) : act R σ (a ⊗ₜ r) = σ a ⊗ₜ r := rfl

theorem smul_eq_act (σ : Ω ≃ₐ[k] Ω) (x : Ω ⊗[k] R) : σ • x = act R σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a r => rw [TensorProduct.smul_tmul', act_tmul, AlgEquiv.smul_def]
  | add x y hx hy => rw [smul_add, hx, hy, map_add (f := _)]

scoped instance instAct : MulSemiringAction (Ω ≃ₐ[k] Ω) (Ω ⊗[k] R) :=
  { TensorProduct.leftDistribMulAction with
    smul_one := fun σ => by rw [smul_eq_act, map_one]
    smul_mul := fun σ x y => by rw [smul_eq_act, smul_eq_act, smul_eq_act, map_mul] }

theorem smul_def (σ : Ω ≃ₐ[k] Ω) (x : Ω ⊗[k] R) : σ • x = act R σ x := smul_eq_act R σ x

attribute [local instance] Algebra.TensorProduct.rightAlgebra

scoped instance smulComm : SMulCommClass (Ω ≃ₐ[k] Ω) R (Ω ⊗[k] R) where
  smul_comm σ r x := by
    rw [Algebra.smul_def, Algebra.smul_def, smul_def, smul_def, map_mul]
    congr 1
    change act R σ (1 ⊗ₜ r) = 1 ⊗ₜ r
    simp

theorem repr_act {ι : Type} (b : Module.Basis ι k R) (σ : Ω ≃ₐ[k] Ω) (x : Ω ⊗[k] R) (i : ι) :
    (Algebra.TensorProduct.basis Ω b).repr (act R σ x) i = σ ((Algebra.TensorProduct.basis Ω b).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a r =>
    simp only [act_tmul, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul, map_mul, AlgEquiv.commutes]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

variable [IsGalois k Ω]

open Classical in
theorem isInvariant : Algebra.IsInvariant R (Ω ⊗[k] R) (Ω ≃ₐ[k] Ω) where
  isInvariant x hx := by
    let b := Module.Free.chooseBasis k R
    let B := Algebra.TensorProduct.basis Ω b
    have hc : ∀ i, ∃ c : k, algebraMap k Ω c = B.repr x i := fun i =>
      (InfiniteGalois.mem_range_algebraMap_iff_fixed (B.repr x i)).2 fun σ => by
        rw [← repr_act R b σ x]
        exact congrArg (fun y => B.repr y i) (hx σ)
    let φ : Ω → k := fun ω => if h : ∃ c : k, algebraMap k Ω c = ω then h.choose else 0
    have hφ0 : φ 0 = 0 := by
      simp only [φ]
      split_ifs with h
      · exact (algebraMap k Ω).injective (h.choose_spec.trans (map_zero _).symm)
      · rfl
    have hφ : ∀ i, algebraMap k Ω (φ (B.repr x i)) = B.repr x i := fun i => by
      simp only [φ, dif_pos (hc i)]
      exact (hc i).choose_spec
    let f : Module.Free.ChooseBasisIndex k R →₀ k := Finsupp.mapRange φ hφ0 (B.repr x)
    refine ⟨b.repr.symm f, B.repr.injective ?_⟩
    ext i
    change B.repr (1 ⊗ₜ (b.repr.symm f)) i = _
    rw [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply, Module.Basis.repr_symm_apply,
      Module.Basis.repr_linearCombination]
    exact hφ i

omit [IsGalois k Ω] in
theorem isOpen_stabilizer [Algebra.IsIntegral k Ω] (x : Ω ⊗[k] R) :
    IsOpen (MulAction.stabilizer (Ω ≃ₐ[k] Ω) x : Set (Ω ≃ₐ[k] Ω)) := by
  induction x using TensorProduct.induction_on with
  | zero =>
    refine Subgroup.isOpen_mono (H₁ := ⊤) (fun σ _ => by rw [MulAction.mem_stabilizer_iff, smul_zero]) ?_
    rw [Subgroup.coe_top]; exact isOpen_univ
  | tmul a r =>
    refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer (Ω ≃ₐ[k] Ω) a) ?_ (stabilizer_isOpen_of_isIntegral a)
    intro σ hσ
    rw [MulAction.mem_stabilizer_iff] at hσ ⊢
    rw [smul_def, act_tmul]
    exact congrArg (· ⊗ₜ[k] r) hσ
  | add x y hx hy =>
    refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer (Ω ≃ₐ[k] Ω) x ⊓ MulAction.stabilizer (Ω ≃ₐ[k] Ω) y)
      ?_ (by rw [Subgroup.coe_inf]; exact hx.inter hy)
    intro σ hσ
    rw [MulAction.mem_stabilizer_iff]
    rw [smul_add, MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hσ).1,
      MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hσ).2]

theorem exists_comap_eq (P Q : Ideal (Ω ⊗[k] R)) [P.IsPrime] [Q.IsPrime]
    (h : P.comap (Algebra.TensorProduct.includeRight : R →ₐ[k] Ω ⊗[k] R).toRingHom =
      Q.comap (Algebra.TensorProduct.includeRight : R →ₐ[k] Ω ⊗[k] R).toRingHom) :
    ∃ σ : Ω ≃ₐ[k] Ω, Q = P.comap (act R σ).toRingEquiv.toRingHom := by
  let _ : TopologicalSpace (Ω ⊗[k] R) := ⊥
  have : DiscreteTopology (Ω ⊗[k] R) := ⟨rfl⟩
  have : ContinuousSMul (Ω ≃ₐ[k] Ω) (Ω ⊗[k] R) := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    exact isOpen_stabilizer R
  have := isInvariant (k := k) (Ω := Ω) R
  have := smulComm (k := k) (Ω := Ω) R
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := R) (G := Ω ≃ₐ[k] Ω) P Q h
  refine ⟨g⁻¹, ?_⟩
  rw [hg, Ideal.pointwise_smul_eq_comap]
  ext x
  simp only [Ideal.mem_comap]
  have e : (MulSemiringAction.toRingAut (Ω ≃ₐ[k] Ω) (Ω ⊗[k] R) g).symm x = act R g⁻¹ x := by
    rw [← smul_def]; rfl
  rw [e]; rfl

end CrystallineSemistableComparison.GeoA
end
end

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison.GeoB

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k))

theorem exists_galMap_apply [IsGalois k Ω] (y z : GlobalTheory.Et.geom Ω p)
    (h : pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) y =
      pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) z) :
    ∃ σ : Ω ≃ₐ[k] Ω, GlobalTheory.Et.galMap Ω p σ y = z := by
  set ψ := Spec.map (CommRingCat.ofHom (algebraMap k Ω)) with hψ
  obtain ⟨R, f, hf, x₀, hx₀⟩ := Scheme.exists_Spec_apply_eq (pullback.fst p ψ y)
  let κ : CommRingCat.of k ⟶ R := Spec.preimage (f ≫ p)
  let _ : Algebra k R := κ.hom.toAlgebra
  let iΩ : CommRingCat.of Ω ⟶ CommRingCat.of (Ω ⊗[k] R) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let iR : R ⟶ CommRingCat.of (Ω ⊗[k] R) := CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  have hout : IsPullback (Spec.map iΩ) (Spec.map iR) ψ (f ≫ p) := by
    have := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct k Ω R)
    rw [← Spec.map_preimage (f ≫ p)]
    exact this
  have t : IsPullback (pullback.snd p ψ) (pullback.fst p ψ) ψ p := (IsPullback.of_hasPullback p ψ).flip
  have L := IsPullback.of_right' hout t
  set Φ := t.lift (Spec.map iΩ) (Spec.map iR ≫ f) (by rw [hout.w, Category.assoc]) with hΦ
  have hΦs : Φ ≫ pullback.snd p ψ = Spec.map iΩ := t.lift_fst _ _ _
  have hΦf : Φ ≫ pullback.fst p ψ = Spec.map iR ≫ f := t.lift_snd _ _ _
  have hrange : ∀ w : GlobalTheory.Et.geom Ω p, pullback.fst p ψ w ∈ Set.range f → ∃ P, Φ P = w := by
    intro w hw
    have : w ∈ Set.range (pullback.fst (pullback.fst p ψ) f) := by
      rw [Scheme.Pullback.range_fst]; exact hw
    obtain ⟨v, rfl⟩ := this
    refine ⟨L.isoPullback.inv v, ?_⟩
    rw [← Scheme.Hom.comp_apply, L.isoPullback_inv_fst]
  obtain ⟨P, rfl⟩ := hrange y ⟨x₀, hx₀⟩
  obtain ⟨Q, rfl⟩ := hrange z ⟨x₀, hx₀.trans h⟩
  have hfst : ∀ P, pullback.fst p ψ (Φ P) = f (Spec.map iR P) := fun P => by
    rw [← Scheme.Hom.comp_apply, hΦf, Scheme.Hom.comp_apply]
  have hPQ : Spec.map iR P = Spec.map iR Q := f.isOpenEmbedding.injective (by rw [← hfst, ← hfst, h])
  have hPQ' : P.asIdeal.comap iR.hom = Q.asIdeal.comap iR.hom := congrArg PrimeSpectrum.asIdeal hPQ
  have : P.asIdeal.IsPrime := P.2
  have : Q.asIdeal.IsPrime := Q.2
  obtain ⟨σ, hσ⟩ := GeoA.exists_comap_eq (k := k) (Ω := Ω) R P.asIdeal Q.asIdeal hPQ'
  refine ⟨σ, ?_⟩
  let T : CommRingCat.of (Ω ⊗[k] R) ⟶ CommRingCat.of (Ω ⊗[k] R) :=
    CommRingCat.ofHom (GeoA.act R σ).toRingEquiv.toRingHom
  have hTR : iR ≫ T = iR := by
    ext r
    change GeoA.act R σ (1 ⊗ₜ r) = 1 ⊗ₜ r
    simp
  have hTΩ : iΩ ≫ T = CommRingCat.ofHom (σ : Ω →+* Ω) ≫ iΩ := by
    ext a
    change GeoA.act R σ (a ⊗ₜ 1) = σ a ⊗ₜ 1
    simp
  have heq : Spec.map T ≫ Φ = Φ ≫ GlobalTheory.Et.galMap Ω p σ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, GlobalTheory.Et.galMap_fst, hΦf, ← Category.assoc, ← Spec.map_comp, hTR]
    · rw [Category.assoc, Category.assoc, GlobalTheory.Et.galMap_snd, hΦs, ← Category.assoc, hΦs, ← Spec.map_comp,
        ← Spec.map_comp, hTΩ]
  have hTP : Spec.map T P = Q := PrimeSpectrum.ext (by rw [Spec.map_apply]; exact hσ.symm)
  rw [← hTP, ← Scheme.Hom.comp_apply, ← heq, Scheme.Hom.comp_apply]

end CrystallineSemistableComparison.GeoB
end
end

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Topology TopologicalSpace

namespace CrystallineSemistableComparison.GeoC

theorem isOpen_connectedComponent {X : Type*} [TopologicalSpace X] [NoetherianSpace X] (x : X) :
    IsOpen (connectedComponent x) := by
  have h : (connectedComponent x)ᶜ =
      ⋃ Z ∈ {Z ∈ irreducibleComponents X | ¬ Z ⊆ connectedComponent x}, Z := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hy
      exact ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y,
        fun h => hy (h mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩
    · rintro ⟨Z, ⟨hZ, hZ'⟩, hy⟩ hyx
      apply hZ'
      rw [connectedComponent_eq hyx]
      exact hZ.1.isConnected.subset_connectedComponent hy
  rw [← isClosed_compl_iff, h]
  refine Set.Finite.isClosed_biUnion
    (NoetherianSpace.finite_irreducibleComponents.subset (by exact fun Z hZ => hZ.1)) fun Z hZ => ?_
  exact isClosed_of_mem_irreducibleComponents Z hZ.1

theorem image_connectedComponent {X : Type*} [TopologicalSpace X] (h : X ≃ₜ X) (x : X) :
    h '' connectedComponent x = connectedComponent (h x) := by
  refine (h.continuous.image_connectedComponent_subset x).antisymm ?_
  intro y hy
  refine ⟨h.symm y, ?_, h.apply_symm_apply y⟩
  have := h.symm.continuous.image_connectedComponent_subset (h x) ⟨y, hy, rfl⟩
  rwa [h.symm_apply_apply] at this

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k))

theorem galMap_comp_inv (σ : Ω ≃ₐ[k] Ω) : GlobalTheory.Et.galMap Ω p σ ≫ GlobalTheory.Et.galMap Ω p σ⁻¹ = 𝟙 _ := by
  rw [← GlobalTheory.EtC.galMap_mul, mul_inv_cancel, GlobalTheory.EtC.galMap_one]

theorem galMap_inv_comp (σ : Ω ≃ₐ[k] Ω) : GlobalTheory.Et.galMap Ω p σ⁻¹ ≫ GlobalTheory.Et.galMap Ω p σ = 𝟙 _ := by
  rw [← GlobalTheory.EtC.galMap_mul, inv_mul_cancel, GlobalTheory.EtC.galMap_one]

instance (σ : Ω ≃ₐ[k] Ω) : IsIso (GlobalTheory.Et.galMap Ω p σ) :=
  ⟨⟨GlobalTheory.Et.galMap Ω p σ⁻¹, galMap_comp_inv p σ, galMap_inv_comp p σ⟩⟩

def galHomeo (σ : Ω ≃ₐ[k] Ω) : GlobalTheory.Et.geom Ω p ≃ₜ GlobalTheory.Et.geom Ω p where
  toFun := GlobalTheory.Et.galMap Ω p σ
  invFun := GlobalTheory.Et.galMap Ω p σ⁻¹
  left_inv x := by rw [← Scheme.Hom.comp_apply, galMap_comp_inv]; rfl
  right_inv x := by rw [← Scheme.Hom.comp_apply, galMap_inv_comp]; rfl
  continuous_toFun := (GlobalTheory.Et.galMap Ω p σ).continuous
  continuous_invFun := (GlobalTheory.Et.galMap Ω p σ⁻¹).continuous

theorem galMap_mul_apply (σ τ : Ω ≃ₐ[k] Ω) (y : GlobalTheory.Et.geom Ω p) :
    GlobalTheory.Et.galMap Ω p (σ * τ) y = GlobalTheory.Et.galMap Ω p τ (GlobalTheory.Et.galMap Ω p σ y) := by
  rw [GlobalTheory.EtC.galMap_mul, Scheme.Hom.comp_apply]

theorem galMap_one_apply (y : GlobalTheory.Et.geom Ω p) : GlobalTheory.Et.galMap Ω p 1 y = y := by
  rw [GlobalTheory.EtC.galMap_one]; rfl

theorem exists_components [IsGalois k Ω] [Smooth p] [ConnectedSpace X] [CompactSpace X] :
    ∃ (r : ℕ) (U : Fin r → (GlobalTheory.Et.geom Ω p).Opens),
      (∀ s, IsIntegral (U s).toScheme) ∧ (∀ y, ∃ s, y ∈ U s) ∧
      (∀ s s', s ≠ s' → Disjoint (U s : Set (GlobalTheory.Et.geom Ω p)) (U s')) ∧
      (∀ (σ : Ω ≃ₐ[k] Ω) s, ∃ s', GlobalTheory.Et.galMap Ω p σ '' (U s : Set (GlobalTheory.Et.geom Ω p)) = U s') ∧
      (∀ s s', ∃ σ : Ω ≃ₐ[k] Ω, GlobalTheory.Et.galMap Ω p σ '' (U s : Set (GlobalTheory.Et.geom Ω p)) = U s') := by
  set ψ := Spec.map (CommRingCat.ofHom (algebraMap k Ω)) with hψ
  set Y := GlobalTheory.Et.geom Ω p
  have : QuasiCompact p := quasiCompact_of_compactSpace p
  have : CompactSpace Y := by dsimp only [Y, GlobalTheory.Et.geom]; infer_instance
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (pullback.snd p ψ)
  have : IsNoetherian Y := {}
  have hopen : ∀ y : Y, IsOpen (connectedComponent y) := isOpen_connectedComponent
  have : DiscreteTopology (_root_.ConnectedComponents Y) := ConnectedComponents.discreteTopology_iff.2 hopen
  have : Finite (_root_.ConnectedComponents Y) := finite_of_compact_of_discrete
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin (_root_.ConnectedComponents Y)
  let C : Fin r → Set Y := fun s => ConnectedComponents.mk ⁻¹' {e.symm s}
  have hC : ∀ y : Y, C (e (ConnectedComponents.mk y)) = connectedComponent y := fun y => by
    simp only [C, Equiv.symm_apply_apply, connectedComponents_preimage_singleton]
  have hCrep : ∀ s, ∃ y : Y, C s = connectedComponent y := fun s => by
    obtain ⟨y, hy⟩ := ConnectedComponents.surjective_coe (e.symm s)
    exact ⟨y, by rw [← hC y, hy, Equiv.apply_symm_apply]⟩
  have hCopen : ∀ s, IsOpen (C s) := fun s => by
    obtain ⟨y, hy⟩ := hCrep s; rw [hy]; exact hopen y
  let U : Fin r → Y.Opens := fun s => ⟨C s, hCopen s⟩
  have hg : ∀ (σ : Ω ≃ₐ[k] Ω) (y : Y),
      GlobalTheory.Et.galMap Ω p σ '' connectedComponent y = connectedComponent (GlobalTheory.Et.galMap Ω p σ y) :=
    fun σ y => image_connectedComponent (galHomeo p σ) y
  refine ⟨r, U, fun s => ?_, fun y => ⟨e (ConnectedComponents.mk y), ?_⟩, fun s s' hss' => ?_,
    fun σ s => ?_, fun s s' => ?_⟩
  · obtain ⟨y, hy⟩ := hCrep s
    have : ConnectedSpace (U s).toScheme := by
      change ConnectedSpace (C s)
      rw [hy]
      exact isConnected_iff_connectedSpace.1 isConnected_connectedComponent
    exact GlobalTheory.isIntegral_of_smooth_field ((U s).ι ≫ pullback.snd p ψ)
  · change y ∈ C _
    rw [hC]; exact mem_connectedComponent
  · change Disjoint (C s) (C s')
    refine Set.disjoint_left.2 fun y h1 h2 => hss' ?_
    simp only [C, Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
    exact e.symm.injective (h1.symm.trans h2)
  · obtain ⟨y, hy⟩ := hCrep s
    refine ⟨e (ConnectedComponents.mk (GlobalTheory.Et.galMap Ω p σ y)), ?_⟩
    change _ '' C s = C _
    rw [hy, hC, hg]
  · obtain ⟨y₀, hy₀⟩ := hCrep s
    obtain ⟨y₁, hy₁⟩ := hCrep s'

    let Z : Set Y := {y | ∃ σ : Ω ≃ₐ[k] Ω, y ∈ connectedComponent (GlobalTheory.Et.galMap Ω p σ y₀)}
    have hZstab : ∀ (τ : Ω ≃ₐ[k] Ω) y, y ∈ Z → GlobalTheory.Et.galMap Ω p τ y ∈ Z := by
      rintro τ y ⟨σ, hσ⟩
      refine ⟨σ * τ, ?_⟩
      rw [galMap_mul_apply, ← hg]
      exact ⟨y, hσ, rfl⟩
    have hZo : IsOpen Z := by
      have : Z = ⋃ σ : Ω ≃ₐ[k] Ω, connectedComponent (GlobalTheory.Et.galMap Ω p σ y₀) := by
        ext y; simp [Z]
      rw [this]; exact isOpen_iUnion fun σ => hopen _
    have hZc : IsOpen Zᶜ := by
      rw [isOpen_iff_forall_mem_open]
      intro y hy
      refine ⟨connectedComponent y, fun w hw hwZ => hy ?_, hopen y, mem_connectedComponent⟩
      obtain ⟨σ, hσ⟩ := hwZ
      refine ⟨σ, ?_⟩
      rw [connectedComponent_eq hσ, ← connectedComponent_eq hw]
      exact mem_connectedComponent
    have hy₀Z : y₀ ∈ Z := ⟨1, by rw [galMap_one_apply]; exact mem_connectedComponent⟩
    have hZ : Z = Set.univ := by
      by_contra hne
      obtain ⟨b, hb⟩ := (Set.ne_univ_iff_exists_notMem Z).1 hne
      have : Algebra.IsIntegral k Ω := inferInstance
      have : IsIntegralHom ψ := IsIntegralHom.SpecMap_iff.2 (fun x => Algebra.IsIntegral.isIntegral x)
      have : Surjective ψ := ⟨fun _ => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
      have hcl := (pullback.fst p ψ).isClosedMap
      have hsurj := (pullback.fst p ψ).surjective
      set A := pullback.fst p ψ '' Z
      set B := pullback.fst p ψ '' Zᶜ
      have hAB : A = Bᶜ := by
        ext x
        constructor
        · rintro ⟨a, ha, rfl⟩ ⟨c, hc, hca⟩
          obtain ⟨σ, hσ⟩ := GeoB.exists_galMap_apply p a c hca.symm
          exact hc (hσ ▸ hZstab σ a ha)
        · intro hx
          obtain ⟨a, rfl⟩ := hsurj x
          by_cases ha : a ∈ Z
          · exact ⟨a, ha, rfl⟩
          · exact absurd ⟨a, ha, rfl⟩ hx
      have hAcl : IsClopen A :=
        ⟨hcl _ (isOpen_compl_iff.1 hZc), hAB ▸ (hcl _ hZo.isClosed_compl).isOpen_compl⟩
      rcases isClopen_iff.1 hAcl with h | h
      · exact (Set.eq_empty_iff_forall_notMem.1 h) _ ⟨y₀, hy₀Z, rfl⟩
      · have : pullback.fst p ψ b ∈ A := h ▸ Set.mem_univ _
        rw [hAB] at this
        exact this ⟨b, hb, rfl⟩
    have : y₁ ∈ Z := hZ ▸ Set.mem_univ _
    obtain ⟨σ, hσ⟩ := this
    refine ⟨σ, ?_⟩
    change _ '' C s = C s'
    rw [hy₀, hy₁, hg, connectedComponent_eq hσ]

end CrystallineSemistableComparison.GeoC
end
end

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison

namespace GeoD


attribute [local instance] MvPolynomial.gradedAlgebra in
theorem isProper_pspace (R : Type) [CommRing R] (N : ℕ) : IsProper (PSpace.str R N) := by
  have : IsScalarTower R (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) (MvPolynomial (Fin (N + 1)) R) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) (MvPolynomial (Fin (N + 1)) R) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R _ _
  have : IsClosedImmersion (spMap (algebraMap R (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0))) := by
    apply IsClosedImmersion.spec_of_surjective
    rintro ⟨p, hp⟩
    have h0 : p.totalDegree = 0 := Nat.le_zero.1 (MvPolynomial.IsHomogeneous.totalDegree_le hp)
    exact ⟨p.coeff 0, Subtype.ext (MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 h0).symm⟩
  unfold PSpace.str
  infer_instance

theorem compactSpace_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have := isProper_pspace R N
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R N)

end GeoD

theorem geoMain : GeometricGenericComponents := by
  intro l _ K M hM d hC
  obtain ⟨hconn, hsm⟩ := hC
  have : Smooth M.q := SmoothOfRelativeDimension.smooth d M.q
  have : CompactSpace M.X := GeoD.compactSpace_of_isProjOver hM.1
  have : QuasiCompact M.p := quasiCompact_of_compactSpace M.p
  have : CompactSpace M.gen := inferInstance
  obtain ⟨r, U, hint, hcov, hdisj, hperm, htrans⟩ := GeoC.exists_components (Ω := PadicAlgCl l) M.q
  have hne : ∀ s, (U s : Set (GlobalTheory.Et.geom (PadicAlgCl l) M.q)).Nonempty := fun s => by
    obtain ⟨⟨y, hy⟩⟩ := (hint s).nonempty
    exact ⟨y, hy⟩
  refine ⟨r, fun s => (U s).toScheme, fun s => (U s).ι, ⟨fun s => inferInstance, fun y => ?_, fun s s' h => ?_⟩,
    hint, fun σ => ?_, fun s s' => ?_⟩
  · obtain ⟨s, hs⟩ := hcov y
    exact ⟨s, by rw [Scheme.Opens.range_ι]; exact hs⟩
  · rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact hdisj s s' h
  · set g := GlobalTheory.Et.galMap (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K σ)
    choose f hf using hperm (IntermediateField.fixingSubgroupEquiv K σ)
    have hginj : Function.Injective g := (GeoC.galHomeo M.q (IntermediateField.fixingSubgroupEquiv K σ)).injective
    have hinj : Function.Injective f := by
      intro s s' hss'
      by_contra h
      have h1 : (U s : Set _) = U s' :=
        Set.image_injective.2 hginj ((hf s).trans (hss' ▸ (hf s').symm))
      obtain ⟨y, hy⟩ := hne s
      exact Set.disjoint_left.1 (hdisj s s' h) hy (h1 ▸ hy)
    let π := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj)
    have hr : ∀ s, Set.range ((U s).ι ≫ g) = Set.range (U (π s)).ι := fun s => by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
      exact hf s
    exact ⟨π, fun s => IsOpenImmersion.isoOfRangeEq ((U s).ι ≫ g) (U (π s)).ι (hr s),
      fun s => (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).symm⟩
  · obtain ⟨τ, hτ⟩ := htrans s s'
    refine ⟨(IntermediateField.fixingSubgroupEquiv K).symm τ, ?_⟩
    rw [MulEquiv.apply_symm_apply]
    have hr : Set.range ((U s).ι ≫ GlobalTheory.Et.galMap (PadicAlgCl l) M.q τ) = Set.range (U s').ι := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
      exact hτ
    exact ⟨(IsOpenImmersion.isoOfRangeEq _ _ hr).hom, (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).symm⟩

end CrystallineSemistableComparison
end
end

noncomputable section

namespace CrystallineSemistableComparison

theorem comp : ModelComponents := fun l _ K _ ↦ ⟨compSm l K, compGood l K⟩

theorem geo : GeometricGenericComponents := geoMain

end CrystallineSemistableComparison
