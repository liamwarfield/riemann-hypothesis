module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsProperIntegralModel

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinear
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinear
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieBaseChange

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieTangent

theorem existsUnique_semilinear_lifts :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R R' : Type) [CommRing R] [CommRing R'] (c : R →+* R')
      (x : Sp R ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (E' : Type) [AddCommGroup E'] [Module R' E']
      (M : LieModel G x E) (M' : LieModel G (spMap c ≫ x) E'),
      ∃! j : E →ₛₗ[c] E', ∀ e, ((M'.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (M.pt e).left) := by
  intro S G _ R R' _ _ c x E _ _ E' _ _ M M'
  have hc : Spec.map (CommRingCat.ofHom c) ≫ x = spMap c ≫ x := rfl
  have h : ∀ e, ∃ e', M'.pt e' = epsBase c hc ≫ M.pt e :=
    fun e => M'.onto _ (isTanAt_base c hc (M.tan e))
  choose a ha using h
  refine ⟨{ toFun := a, map_add' := ?_, map_smul' := ?_ }, ?_, ?_⟩
  · intro e e'
    apply M'.inj
    rw [M'.add, ha, ha, ha, M.add, MonObj.comp_mul]
  · intro r e
    apply M'.inj
    rw [M'.pt_smul, ha, ha, M.pt_smul, ← Category.assoc, base_scale, Category.assoc]
  · intro e
    change (M'.pt (a e)).left ≫ 𝟙 G.left = spMap (dualMap c) ≫ (M.pt e).left
    rw [Category.comp_id, ha]
    rfl
  · intro j hj
    ext e
    refine M'.inj ((?_ : M'.pt (j e) = epsBase c hc ≫ M.pt e).trans (ha e).symm)
    apply Over.OverMorphism.ext
    have := hj e
    change _ ≫ _ = _ ≫ _ at this
    rw [Category.comp_id] at this
    exact this

end GlobalTheory.CompanionTheory.Ar.LieBaseChange
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinearStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
alias GlobalTheory.T.lie_model_existsUnique_semilinear := GlobalTheory.CompanionTheory.Ar.LieBaseChange.existsUnique_semilinear_lifts
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToGermTop
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ZmodTorsorBaseChangeTransportPoint
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ar

theorem unitAt_iff_of_isCptGen {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) (p : Cpt ξ) (a : Ω) :
    unitAt ξ p a ↔ ∃ u, IsUnit u ∧ genMap ξ p u = a := by
  constructor
  · rintro ⟨h0, ⟨u, rfl⟩, ⟨v, hv⟩⟩
    refine ⟨u, IsUnit.of_mul_eq_one v (h.inj p ?_), rfl⟩
    rw [map_mul, hv, map_one, mul_inv_cancel₀ h0]
  · rintro ⟨u, ⟨w, rfl⟩, rfl⟩
    refine ⟨(w.isUnit.map _).ne_zero, ⟨_, rfl⟩, ⟨(w⁻¹ : _ˣ), ?_⟩⟩
    exact map_units_inv _ w

end GlobalTheory.CompanionTheory.Ar
end

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.ConstReg

theorem stalkClosedPointTo_germ_top {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (t : Γ(X, ⊤)) :
    (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ ⊤ (genPt ξ) trivial).hom t) =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (ξ.appTop.hom t) := by
  have h : X.presheaf.germ ⊤ (genPt ξ) trivial ≫ Scheme.stalkClosedPointTo ξ =
      ξ.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom := by
    refine (Scheme.germ_stalkClosedPointTo ξ ⊤ trivial).trans ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appTop]
    congr 1
  exact congrArg (fun q => q.hom t) h

theorem genMap_germ_const {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) {O : Type} [CommRing O] [Algebra O Ω]
    (s : X ⟶ Spec (CommRingCat.of O))
    (hs : ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω))) (p : Cpt ξ) (o : O) :
    genMap ξ p ((X.presheaf.germ ⊤ p.1 trivial).hom
        (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) = algebraMap O Ω o := by
  have h1 : genMap ξ p ((X.presheaf.germ ⊤ p.1 trivial).hom
        (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) =
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ ⊤ (genPt ξ) trivial).hom
        (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) :=
    congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_stalkSpecializes_apply (show p.1 ∈ (⊤ : X.Opens) from trivial) p.2 _)
  rw [h1, stalkClosedPointTo_germ_top]
  have h2 : ξ.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)) =
      (Spec.map (CommRingCat.ofHom (algebraMap O Ω))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o) := by
    rw [← hs]; simp only [Scheme.Hom.comp_appTop]; rfl
  rw [h2]
  have h3 := congrArg (fun q => q.hom o)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap O Ω)))
  have h3' : (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (algebraMap O Ω o) =
      (Spec.map (CommRingCat.ofHom (algebraMap O Ω))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o) := h3
  rw [← h3']
  simp

theorem isUnit_germ_const_iff {X : Scheme.{0}} {O : Type} [CommRing O]
    (s : X ⟶ Spec (CommRingCat.of O)) (x : X) (o : O) :
    IsUnit ((X.presheaf.germ ⊤ x trivial).hom
        (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) ↔ o ∉ (s x).asIdeal := by
  rw [← Scheme.mem_basicOpen_top, ← Scheme.preimage_basicOpen_top, Scheme.Hom.mem_preimage,
    basicOpen_eq_of_affine (R := CommRingCat.of O) o]
  exact Iff.rfl

theorem regular_const : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)), ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → ∀ (p : Cpt ξ) (o : O), algebraMap O Ω o ∈ regAt ξ p ∧ (IsCptGen ξ → (unitAt ξ p (algebraMap O Ω o) ↔ o ∉ (s p.1).asIdeal)) := by
  intro X Ω _ ξ O _ _ _ s hs p o
  have hg := genMap_germ_const ξ s hs p o
  refine ⟨⟨_, hg⟩, fun hc => ?_⟩
  rw [← isUnit_germ_const_iff s p.1 o]
  constructor
  · intro hu
    obtain ⟨u, hu, e⟩ := (unitAt_iff_of_isCptGen ξ hc p _).1 hu
    rwa [← hc.inj p (e.trans hg.symm)]
  · intro hu
    rw [← hg]
    exact RegAtMono.unitAt_of_isUnit ξ p hu

end GlobalTheory.CompanionTheory.Ar.Flat.ConstReg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializesOfSpecializes
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar TopologicalSpace

theorem isOpen_of_isClosed_of_generizing {α : Type*} [TopologicalSpace α] [NoetherianSpace α] [QuasiSober α]
    (S : Set α) (hc : IsClosed S) (hs : ∀ x y : α, x ⤳ y → y ∈ S → x ∈ S) : IsOpen S := by
  have hfin : (irreducibleComponents α).Finite := NoetherianSpace.finite_irreducibleComponents
  have hT : IsClosed (⋃₀ {C ∈ irreducibleComponents α | Disjoint C S}) := by
    rw [Set.sUnion_eq_biUnion]
    exact (hfin.subset fun C (h : C ∈ {C ∈ irreducibleComponents α | Disjoint C S}) => h.1).isClosed_biUnion
      fun C h => isClosed_of_mem_irreducibleComponents C h.1
  have e : Sᶜ = ⋃₀ {C ∈ irreducibleComponents α | Disjoint C S} := by
    ext x
    constructor
    · intro hx
      refine ⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents x, ?_⟩,
        mem_irreducibleComponent⟩
      rw [Set.disjoint_left]
      intro s hsC hsS
      have hC := isIrreducible_irreducibleComponent (x := x)
      have hcl : IsClosed (irreducibleComponent x) := isClosed_irreducibleComponent
      obtain ⟨c, hcg⟩ := QuasiSober.sober hC hcl
      have hcs : c ∈ S := hs c s (hcg.specializes hsC) hsS
      exact hx (hc.closure_subset_iff.2 (Set.singleton_subset_iff.2 hcs) (by
        rw [hcg.def]; exact mem_irreducibleComponent))
    · rintro ⟨C, ⟨-, hd⟩, hx⟩ hxS
      exact Set.disjoint_left.1 hd hx hxS
  rw [← isClosed_compl_iff, e]
  exact hT

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem genPt_specializes_of_specializes (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) {p y : X}
    (hp : genPt ξ ⤳ p) (hy : y ⤳ p) : genPt ξ ⤳ y := by
  haveI := CptInh.dom ξ h ⟨p, hp⟩
  haveI : IsDomain (X.presheaf.stalk p) := this
  obtain ⟨a, ha⟩ : genPt ξ ∈ Set.range (X.fromSpecStalk p) := by
    rwa [Scheme.range_fromSpecStalk]
  obtain ⟨b, hb⟩ : y ∈ Set.range (X.fromSpecStalk p) := by
    rwa [Scheme.range_fromSpecStalk]
  let o : Spec (CommRingCat.of (X.presheaf.stalk p)) :=
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (X.presheaf.stalk p))
  have hoc : ∀ c : Spec (CommRingCat.of (X.presheaf.stalk p)), o ⤳ c := fun c =>
    (PrimeSpectrum.le_iff_specializes (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (X.presheaf.stalk p)) c).1 bot_le
  have h1 : X.fromSpecStalk p o ⤳ genPt ξ := by
    rw [← ha]; exact (hoc a).map (X.fromSpecStalk p).continuous
  have h2 : X.fromSpecStalk p o ⤳ y := by
    rw [← hb]; exact (hoc b).map (X.fromSpecStalk p).continuous
  rwa [CptInh.nogen ξ h _ h1] at h2

theorem isOpen_closure_genPt (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X] (h : IsCptGen ξ) :
    IsOpen (closure {genPt ξ}) := by
  rw [isOpen_iff_forall_mem_open]
  intro p hp
  obtain ⟨W, hpW⟩ : ∃ W : X.affineOpens, p ∈ W.1 := by
    obtain ⟨W, hW, hpW, -⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := ⊤) trivial
    exact ⟨⟨W, hW⟩, hpW⟩
  haveI : IsNoetherianRing Γ(X, W.1) := IsLocallyNoetherian.component_noetherian W
  haveI : NoetherianSpace (W.1 : X.Opens) := noetherianSpace_of_isAffineOpen W.1 W.2
  haveI : QuasiSober (W.1 : X.Opens) := inferInstanceAs (QuasiSober (W.1 : X.Opens).toScheme)
  have ho : IsOpen (Subtype.val ⁻¹' (closure {genPt ξ}) : Set (W.1 : X.Opens)) :=
    isOpen_of_isClosed_of_generizing _ (isClosed_closure.preimage continuous_subtype_val)
      fun x y hxy hy => by
        have hy' : genPt ξ ⤳ y.1 := specializes_iff_mem_closure.2 hy
        exact specializes_iff_mem_closure.1
          (genPt_specializes_of_specializes ξ h hy' (hxy.map continuous_subtype_val))
  refine ⟨Subtype.val '' (Subtype.val ⁻¹' (closure {genPt ξ}) : Set (W.1 : X.Opens)), ?_,
    W.1.isOpen.isOpenMap_subtype_val _ ho, ⟨⟨p, hpW⟩, hp, rfl⟩⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hx

theorem cpt_open_integral : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    [IsLocallyNoetherian X], IsCptGen ξ → ∃ U : X.Opens, (∀ q : X, q ∈ U ↔ genPt ξ ⤳ q) ∧
      IsClosed (U : Set X) ∧ IsIntegral U.toScheme := by
  intro X Ω _ ξ _ h
  let U : X.Opens := ⟨closure {genPt ξ}, isOpen_closure_genPt ξ h⟩
  have hU : ∀ q : X, q ∈ U ↔ genPt ξ ⤳ q := fun q => specializes_iff_mem_closure.symm
  refine ⟨U, hU, isClosed_closure, ?_⟩
  haveI : IrreducibleSpace U.toScheme :=
    Subtype.irreducibleSpace (isIrreducible_singleton (x := genPt ξ)).closure
  haveI : ∀ x : U.toScheme, _root_.IsReduced (U.toScheme.presheaf.stalk x) := fun x => by
    haveI := CptInh.dom ξ h ⟨U.ι x, (hU _).1 x.2⟩
    have e := (asIso (U.ι.stalkMap x)).commRingCatIsoToRingEquiv
    exact isReduced_of_injective e.symm.toRingHom e.symm.injective
  haveI : IsReduced U.toScheme := isReduced_of_isReduced_stalk _
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermStalkClosedPointToBaseChange
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.PullReg

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {Ω' : Type} [Field Ω']

theorem germ_stalkClosedPointTo_baseChange (ξ : Spec (CommRingCat.of Ω) ⟶ X) (i : Ω →+* Ω')
    (ζ : Spec (CommRingCat.of Ω') ⟶ X) (hζ : ζ = Spec.map (CommRingCat.ofHom i) ≫ ξ) (U : X.Opens)
    (hU : ζ (IsLocalRing.closedPoint (CommRingCat.of Ω')) ∈ U) (hU' : genPt ξ ∈ U) :
    X.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo ζ =
      X.presheaf.germ U (genPt ξ) hU' ≫ Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i := by
  have e : ζ = Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫
      X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω)) := by
    rw [hζ, Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have hl : IsLocalHom (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i).hom := by
    refine ⟨fun a ha => ?_⟩
    have h1 : IsUnit (i ((Scheme.stalkClosedPointTo ξ).hom a)) := ha
    have h2 : IsUnit ((Scheme.stalkClosedPointTo ξ).hom a : Ω) :=
      isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at h1
    exact isUnit_of_map_unit (Scheme.stalkClosedPointTo ξ).hom a h2
  subst e
  exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk _ U hU

theorem stalkMap_comp_genMap {X' : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'} (hD : Dominates ξ' ξ f i)
    (p' : Cpt ξ') (h : genPt ξ ⤳ f p'.1) (s : X.presheaf.stalk (f p'.1)) :
    genMap ξ' p' ((f.stalkMap p'.1).hom s) = i (genMap ξ ⟨f p'.1, h⟩ s) := by
  have key : f.stalkMap p'.1 ≫ X'.presheaf.stalkSpecializes p'.2 ≫ Scheme.stalkClosedPointTo ξ' =
      X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i := by
    refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
    have hg : genPt ξ ∈ U := h.mem_open U.2 hU
    have hg' : (ξ' ≫ f) (IsLocalRing.closedPoint (CommRingCat.of Ω')) ∈ U := by
      have : (ξ' ≫ f) (IsLocalRing.closedPoint (CommRingCat.of Ω')) = genPt ξ :=
        (Scheme.Hom.comp_apply ξ' f _).trans hD.map_genPt
      rw [this]; exact hg
    have e := germ_stalkClosedPointTo_baseChange ξ i (ξ' ≫ f) hD U hg' hg
    rw [Scheme.stalkClosedPointTo_comp] at e
    have e3 : f.stalkMap p'.1 ≫ X'.presheaf.stalkSpecializes p'.2 ≫ Scheme.stalkClosedPointTo ξ' =
        X.presheaf.stalkSpecializes (p'.2.map f.continuous) ≫ f.stalkMap (genPt ξ') ≫
          Scheme.stalkClosedPointTo ξ' :=
      (Scheme.Hom.stalkSpecializes_stalkMap_assoc f _ _ p'.2 _).symm
    rw [e3, TopCat.Presheaf.germ_stalkSpecializes_assoc, TopCat.Presheaf.germ_stalkSpecializes_assoc]
    exact e
  exact congrArg (fun φ => φ.hom s) key

end GlobalTheory.CompanionTheory.Ar.Flat.PullReg

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem pull_reg_and_gen : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0})
    (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'),
    Dominates ξ' ξ f i → ∀ p' : Cpt ξ', ∃ h : genPt ξ ⤳ f p'.1,
      (∀ a ∈ regAt ξ ⟨f p'.1, h⟩, i a ∈ regAt ξ' p') ∧
        ∀ (L : Lat ξ Ω) (t : Ω), L.IsGenAt ⟨f p'.1, h⟩ t →
          (L.pull ξ' f i.toAddMonoidHom).IsGenAt p' (i t) := by
  intro X Ω _ ξ X' Ω' _ ξ' f i hD p'
  have h := hD.specializes p'
  have hreg : ∀ a ∈ regAt ξ ⟨f p'.1, h⟩, i a ∈ regAt ξ' p' := by
    rintro _ ⟨s, rfl⟩
    exact ⟨_, PullReg.stalkMap_comp_genMap hD p' h s⟩
  refine ⟨h, hreg, fun L t ht => ⟨(map_ne_zero i).2 ht.1, ?_⟩⟩
  rw [Lat.pull_apply L hD]
  have hL : L ⟨f p'.1, hD.specializes p'⟩ = Submodule.span (regAt ξ ⟨f p'.1, h⟩) {t} := ht.2
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨e, he, rfl⟩
    have he' : e ∈ Submodule.span (regAt ξ ⟨f p'.1, h⟩) {t} := by
      rw [← hL]; exact he
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 he'
    refine Submodule.mem_span_singleton.2 ⟨⟨i r, hreg _ r.2⟩, ?_⟩
    show i (r : Ω) * i t = i ((r : Ω) * t)
    rw [map_mul]
  · rw [Submodule.span_singleton_le_iff_mem]
    refine Submodule.subset_span ⟨t, ?_, rfl⟩
    show t ∈ (L ⟨f p'.1, hD.specializes p'⟩ : Set Ω)
    rw [hL]
    exact Submodule.mem_span_singleton_self t

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdUpdateDiv
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

open AlgebraicGeometry CategoryTheory

def locSub {F : Type} [Field F] (R : Subring F) (a : F) : Subring F :=
  Subring.closure ((R : Set F) ∪ {a⁻¹})

theorem le_locSub {F : Type} [Field F] (R : Subring F) (a : F) : R ≤ locSub R a :=
  fun _ h => Subring.subset_closure (Or.inl h)

theorem inv_mem_locSub {F : Type} [Field F] (R : Subring F) (a : F) : a⁻¹ ∈ locSub R a :=
  Subring.subset_closure (Or.inr rfl)

theorem mem_locSub_iff {F : Type} [Field F] {R : Subring F} {a : F} (ha : a ∈ R) (h0 : a ≠ 0) (b : F) :
    b ∈ locSub R a ↔ ∃ k : ℕ, a ^ k * b ∈ R := by
  constructor
  · intro hb
    induction hb using Subring.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact ⟨0, by simpa using hx⟩
      · rw [Set.mem_singleton_iff.1 hx]
        exact ⟨1, by simpa [h0] using R.one_mem⟩
    | zero => exact ⟨0, by simp⟩
    | one => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨k, hk⟩ := hx
      obtain ⟨l, hl⟩ := hy
      refine ⟨k + l, ?_⟩
      have e : a ^ (k + l) * (x + y) = a ^ l * (a ^ k * x) + a ^ k * (a ^ l * y) := by ring
      rw [e]
      exact R.add_mem (R.mul_mem (R.pow_mem ha _) hk) (R.mul_mem (R.pow_mem ha _) hl)
    | neg x _ hx =>
      obtain ⟨k, hk⟩ := hx
      exact ⟨k, by simpa using R.neg_mem hk⟩
    | mul x y _ _ hx hy =>
      obtain ⟨k, hk⟩ := hx
      obtain ⟨l, hl⟩ := hy
      refine ⟨k + l, ?_⟩
      have e : a ^ (k + l) * (x * y) = (a ^ k * x) * (a ^ l * y) := by ring
      rw [e]
      exact R.mul_mem hk hl
  · rintro ⟨k, hk⟩
    have e : b = (a⁻¹) ^ k * (a ^ k * b) := by
      rw [inv_pow, ← _root_.mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ h0), _root_.one_mul]
    rw [e]
    exact (locSub R a).mul_mem ((locSub R a).pow_mem (inv_mem_locSub R a) _) (le_locSub R a hk)

structure IsPiece {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens)
    (R : Subring Ω) : Prop where
  affine : IsAffineOpen U
  spec : ∀ q : X, q ∈ U → genPt ξ ⤳ q
  ring : ∀ a : Ω, a ∈ R ↔ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q

def stepMinor {F : Type} [CommRing F] {n r : ℕ} (A : Matrix (Fin n) (Fin r) F) (i : Fin r)
    (J : Fin ((i : ℕ) + 1) → Fin n) : F :=
  (A.submatrix J (Fin.castLE i.2)).det

variable {Ω : Type} [Field Ω] {S : Type} {r n : S → ℕ}

def flagB (M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω) (T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (s : S) :
    Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r) :=
  (M s * T s).map (algebraMap Ω (GenField Ω r)) * genU Ω r s

def ratioRing (R : Subring Ω) (B : ∀ s, Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r))
    (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) : Subring (GenField Ω r) :=
  Subring.closure (((R.map (algebraMap Ω (GenField Ω r)) : Subring _) : Set (GenField Ω r)) ∪
    {a | ∃ (q : Σ s, Fin (r s)) (J' : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)),
      a = stepMinor (B q.1) q.2 J' / stepMinor (B q.1) q.2 (J q)})

def chartSub {F : Type} [Field F] {κ : Type} (x : κ → F) (c : κ) : Subring F :=
  (Algebra.adjoin ℤ (Set.range fun j => x j / x c)).toSubring

theorem stepMinor_smul {F : Type} [CommRing F] {n r : ℕ} (b : F) (A : Matrix (Fin n) (Fin r) F) (i : Fin r)
    (J : Fin ((i : ℕ) + 1) → Fin n) : stepMinor (b • A) i J = b ^ ((i : ℕ) + 1) * stepMinor A i J := by
  unfold stepMinor
  rw [Matrix.submatrix_smul]
  simp [Matrix.det_smul]

theorem flagMat_eq {E : Type} [AddCommGroup E] [Module Ω E] {m : S → ℕ}
    {φ : ∀ s, Fin (n s) → Module.Dual Ω E} {cc : ∀ s, Fin (r s) → E}
    {M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω} {T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω} {a : Ω}
    (h : ∀ s j l, φ s j (cc s l) = a ^ m s * (M s * T s) j l) (s : S) :
    flagMat φ cc s = (algebraMap Ω (GenField Ω r) a ^ m s) • flagB M T s := by
  unfold flagMat flagB
  rw [← Matrix.smul_mul]
  congr 1
  ext j l
  simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, h, map_mul, map_pow, smul_eq_mul]

theorem flagCoord_eq [Fintype S] {E : Type} [AddCommGroup E] [Module Ω E] {κ : Type} (x : κ → Ω) {m : S → ℕ}
    {φ : ∀ s, Fin (n s) → Module.Dual Ω E} {cc : ∀ s, Fin (r s) → E}
    {M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω} {T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω} {a : Ω}
    (h : ∀ s j l, φ s j (cc s l) = a ^ m s * (M s * T s) j l) (k : κ)
    (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) :
    flagCoord κ x φ cc (k, J) = algebraMap Ω (GenField Ω r) (x k) *
      ∏ q : (Σ s, Fin (r s)), ((algebraMap Ω (GenField Ω r) a ^ m q.1) ^ ((q.2 : ℕ) + 1) *
        stepMinor (flagB M T q.1) q.2 (J q)) := by
  unfold flagCoord
  congr 1
  refine Finset.prod_congr rfl fun q _ => ?_
  have := stepMinor_smul (algebraMap Ω (GenField Ω r) a ^ m q.1) (flagB M T q.1) q.2 (J q)
  rw [← this, ← flagMat_eq h q.1]
  rfl

theorem prod_update_div {ι : Type} [Fintype ι] [DecidableEq ι] {β : ι → Type} {F : Type} [Field F]
    (f : ∀ q, β q → F) (J : ∀ q, β q) (h : ∀ q, f q (J q) ≠ 0) (q : ι) (b : β q) :
    (∏ q', f q' (Function.update J q b q')) / (∏ q', f q' (J q')) = f q b / f q (J q) := by
  have h1 : ∏ q', f q' (Function.update J q b q') =
      f q b * ∏ q' ∈ Finset.univ.erase q, f q' (J q') := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q)]
    simp only [Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun q' hq' => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hq')]
  have h2 : ∏ q', f q' (J q') = f q (J q) * ∏ q' ∈ Finset.univ.erase q, f q' (J q') :=
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q)).symm
  have h3 : ∏ q' ∈ Finset.univ.erase q, f q' (J q') ≠ 0 := Finset.prod_ne_zero_iff.2 fun q' _ => h q'
  rw [h1, h2]
  field_simp [h q, h3]

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldRatioGenerators
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldRatioGenerators
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart

theorem exists_eq_div_adjoin (X : Scheme.{0}) (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω) (c : κ)
    (hT : CoordTie ℤ ξ x) (hc : x c ≠ 0) (a : Ω) :
    ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), h ≠ 0 ∧ a = g / h := by
  obtain ⟨U, hU, hUc⟩ := hT.affine c hc
  have hreg0 : ∀ b : Ω, b ∈ regAt ξ ⟨genPt ξ, specializes_refl _⟩ := by
    intro b
    obtain ⟨s, hs⟩ := hT.gen.bij.2 b
    show b ∈ (genMap ξ _).range
    refine RingHom.mem_range.mpr ⟨s, ?_⟩
    simp only [genMap, TopCat.Presheaf.stalkSpecializes_refl]
    exact hs
  have hgU : genPt ξ ∈ U :=
    (hUc (genPt ξ)).mpr ⟨specializes_refl _, And.intro hc fun _ => hreg0 _⟩
  let φ : Γ(X, U) →+* Ω := (X.presheaf.germ U (genPt ξ) hgU ≫ Scheme.stalkClosedPointTo ξ).hom
  have key : ∀ r : Γ(X, U), φ r ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
    intro r
    refine (hT.ring c hc (φ r)).mpr fun p hp => ?_
    have hpU : p.1 ∈ U := (hUc p.1).mpr ⟨p.2, hp⟩
    show φ r ∈ (genMap ξ p).range
    refine RingHom.mem_range.mpr ⟨(X.presheaf.germ U p.1 hpU).hom r, ?_⟩
    have e0 : X.presheaf.germ U p.1 hpU ≫ X.presheaf.stalkSpecializes p.2 =
        X.presheaf.germ U (genPt ξ) hgU := by
      simp
    show (X.presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo ξ).hom
        ((X.presheaf.germ U p.1 hpU).hom r) = φ r
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp]
    exact congrArg (fun (m : Γ(X, U) ⟶ CommRingCat.of Ω) => CommRingCat.Hom.hom m r)
        ((reassoc_of% e0) (Scheme.stalkClosedPointTo ξ))
  have gres : ∀ {W W' : X.Opens} (hle : W ≤ W') (hw : genPt ξ ∈ W) (z : Γ(X, W')),
      (X.presheaf.germ W (genPt ξ) hw).hom ((X.presheaf.map (homOfLE hle).op).hom z) =
        (X.presheaf.germ W' (genPt ξ) (hle hw)).hom z := by
    intro W W' hle hw z
    have e : X.presheaf.map (homOfLE hle).op ≫ X.presheaf.germ W (genPt ξ) hw =
        X.presheaf.germ W' (genPt ξ) (hle hw) := by
      simp
    exact congrArg (fun m => m.hom z) e
  obtain ⟨s0, hs0⟩ : ∃ s0 : X.presheaf.stalk (genPt ξ), (Scheme.stalkClosedPointTo ξ).hom s0 = a :=
    hT.gen.bij.2 a
  obtain ⟨V, hV, f, rfl⟩ := TopCat.Presheaf.germ_exist X.presheaf s0
  obtain ⟨t, htV, hgt⟩ := hU.exists_basicOpen_le ⟨genPt ξ, hV⟩ hgU
  have hD : genPt ξ ∈ X.basicOpen t := hgt
  obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen X U hU t
    ((X.presheaf.map (homOfLE htV).op).hom f)
  have hy' : (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom y =
      ((X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom t) ^ n *
        (X.presheaf.map (homOfLE htV).op).hom f := hy
  have h2 : (X.presheaf.germ U (genPt ξ) hgU).hom y =
      ((X.presheaf.germ U (genPt ξ) hgU).hom t) ^ n * (X.presheaf.germ V (genPt ξ) hV).hom f := by
    have h2' := congrArg (X.presheaf.germ (X.basicOpen t) (genPt ξ) hD).hom hy'
    simp only [map_mul, map_pow, gres] at h2'
    exact h2'
  let ψ : X.presheaf.stalk (genPt ξ) →+* Ω := (Scheme.stalkClosedPointTo ξ).hom
  have hφ : ∀ r, φ r = ψ ((X.presheaf.germ U (genPt ξ) hgU).hom r) := by
    intro r
    rfl
  have hs0' : ψ ((X.presheaf.germ V (genPt ξ) hV).hom f) = a := hs0
  have h3 : φ y = φ t ^ n * a := by
    rw [hφ, hφ, h2, map_mul, map_pow, hs0']
  have hunit : IsUnit ((X.presheaf.germ U (genPt ξ) hgU).hom t) :=
    (X.mem_basicOpen t (genPt ξ) hgU).mp hD
  have hφt : φ t ≠ 0 := by
    rw [hφ]
    exact (hunit.map ψ).ne_zero
  refine ⟨φ y, key y, φ (t ^ n), key (t ^ n), ?_, ?_⟩
  · rw [map_pow]
    exact pow_ne_zero _ hφt
  · rw [map_pow]
    exact eq_div_of_mul_eq (pow_ne_zero _ hφt) (by rw [h3]; ring)

end GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldRatioGeneratorsStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
alias GlobalTheory.T.function_field_ratio_generators := GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart.exists_eq_div_adjoin
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModelNonempty
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModelNonempty
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem nonempty_pModel_of_chart : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ]
    (x : κ → Ω), (∃ c, x c ≠ 0 ∧ ∀ a : Ω, ∃ u ∈ chRing o x c, ∃ v ∈ chRing o x c, a = u / v) →
    Nonempty (PModel o x) := by
  intro o _ Ω _ _ κ _ x ⟨c, hc, h⟩
  have h' : ∀ a : Ω, ∃ g ∈ Algebra.adjoin o (Set.range fun j => x j / x c),
      ∃ k ∈ Algebra.adjoin o (Set.range fun j => x j / x c), k ≠ 0 ∧ a = g / k := by
    intro a
    obtain ⟨u, hu, v, hv, rfl⟩ := h a
    by_cases hv0 : v = 0
    · exact ⟨0, zero_mem _, 1, one_mem _, one_ne_zero, by simp [hv0]⟩
    · exact ⟨u, hu, v, hv, hv0, rfl⟩
  obtain ⟨X, ξ, s, tie, all, -, -, hover⟩ := GlobalTheory.T.exists_proper_integral_model Ω o κ x c hc h'
  exact ⟨{ X := X, ξ := ξ, s := s, hover := hover, all := all, tie := tie }⟩

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModelNonemptyStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
alias GlobalTheory.T.projective_model_nonempty := GlobalTheory.CompanionTheory.Ar.nonempty_pModel_of_chart
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLatticeGenerator
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLatticeGenerator
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem ιMulti_ne_zero {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {r : ℕ} {b : Fin r → E}
    (hb : LinearIndependent Ω b) : exteriorPower.ιMulti Ω r b ≠ 0 := by
  classical
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (Module.Basis.span hb).equivFun.toLinearMap
  have hφb : ∀ j, φ (b j) = Pi.single j 1 := by
    intro j
    have h2 : φ (b j) = (Module.Basis.span hb).equivFun (Module.Basis.span hb j) := by
      rw [Module.Basis.span_apply hb j]
      exact LinearMap.congr_fun hφ ⟨b j, Submodule.subset_span ⟨j, rfl⟩⟩
    rw [h2]
    ext k
    rw [Module.Basis.equivFun_self]
    simp [Pi.single_apply, eq_comm]
  intro h0
  have h1 := congrArg (exteriorPower.alternatingMapLinearEquiv
    ((Matrix.detRowAlternating (n := Fin r) (R := Ω)).compLinearMap φ)) h0
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, map_zero] at h1
  have h2 : (fun i => φ (b i)) = (1 : Matrix (Fin r) (Fin r) Ω) := by
    ext i j
    simp [hφb, Matrix.one_apply, Pi.single_apply, eq_comm]
  have h3 : Matrix.det (fun i => φ (b i) : Matrix (Fin r) (Fin r) Ω) = 0 := h1
  rw [h2, Matrix.det_one] at h3
  exact one_ne_zero h3

theorem ιMulti_mem_span {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] (R : Subring Ω) {r : ℕ} (b c : Fin r → E)
    (hc : ∀ i, c i ∈ Submodule.span R (Set.range b)) :
    exteriorPower.ιMulti Ω r c ∈ Submodule.span R {exteriorPower.ιMulti Ω r b} := by
  classical
  choose m hm using fun i => (Submodule.mem_span_range_iff_exists_fun R).1 (hc i)
  have hc' : c = fun i => ∑ j, ((m i j : R) : Ω) • b j := by
    funext i
    rw [← hm i]
    rfl
  have hsum : exteriorPower.ιMulti Ω r (fun i => ∑ j, ((m i j : R) : Ω) • b j) =
      ∑ σ : Fin r → Fin r, exteriorPower.ιMulti Ω r (fun i => ((m i (σ i) : R) : Ω) • b (σ i)) :=
    (exteriorPower.ιMulti Ω r).toMultilinearMap.map_sum (fun i j => ((m i j : R) : Ω) • b j)
  rw [hc', hsum]
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hsm : exteriorPower.ιMulti Ω r (fun i => ((m i (σ i) : R) : Ω) • b (σ i)) =
      (∏ i, ((m i (σ i) : R) : Ω)) • exteriorPower.ιMulti Ω r (b ∘ σ) :=
    (exteriorPower.ιMulti Ω r).toMultilinearMap.map_smul_univ _ _
  have hR : (∏ i, ((m i (σ i) : R) : Ω)) ∈ R := prod_mem fun i _ => (m i (σ i)).2
  rw [hsm]
  by_cases hσ : Function.Injective σ
  · have hperm := (exteriorPower.ιMulti Ω r).map_perm b (Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσ))
    have hco : b ∘ (Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσ)) = b ∘ σ := rfl
    rw [hco] at hperm
    rw [hperm]
    refine Submodule.smul_mem _ (⟨_, hR⟩ : R) ?_
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσ))) with h | h
    · rw [h, one_smul]
      exact Submodule.mem_span_singleton_self _
    · rw [h, Units.neg_smul, one_smul]
      exact neg_mem (Submodule.mem_span_singleton_self _)
  · have h0 : exteriorPower.ιMulti Ω r (b ∘ σ) = 0 :=
      (exteriorPower.ιMulti Ω r).map_eq_zero_of_not_injective _ fun h => hσ h.of_comp
    rw [h0, smul_zero]
    exact zero_mem _

theorem wedge_eq_span_ιMulti : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (b : Fin r → E) (p : Cpt ξ), L.IsFrameAt b p → L.wedge r p = Submodule.span (regAt ξ p) {exteriorPower.ιMulti Ω r b} ∧ exteriorPower.ιMulti Ω r b ≠ 0 := by
  intro X Ω _ ξ E _ _ L r b p ⟨hb, hL⟩
  refine ⟨le_antisymm ?_ ?_, ιMulti_ne_zero hb⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨c, hc, rfl⟩
    exact ιMulti_mem_span (regAt ξ p) b c (fun i => hL ▸ hc i)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.subset_span ⟨b, fun i => by rw [hL]; exact Submodule.subset_span ⟨i, rfl⟩, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLatticeGeneratorStatement
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
alias GlobalTheory.T.wedge_lattice_generator := GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame.wedge_eq_span_ιMulti
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalIsoOfIntegrallyClosed
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalIsoOfIntegrallyClosed
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem NormAt.isoAt_of_integrallyClosed : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (p : Cpt ξ),
    NormAt ξ' f (RingHom.id Ω) p → (∀ a : Ω, IsIntegral (regAt ξ p) a → a ∈ regAt ξ p) →
      IsoAt ξ' f (RingHom.id Ω) p := by
  intro X Ω _ ξ X' ξ' f p hN hp
  have e : (integralClosure ((regAt ξ p).map (RingHom.id Ω)) Ω).toSubring = regAt ξ p := by
    rw [Subring.map_id]
    ext a
    exact ⟨hp a, fun ha => isIntegral_algebraMap (x := (⟨a, ha⟩ : regAt ξ p))⟩
  have loc : IsLocalRing (integralClosure ((regAt ξ p).map (RingHom.id Ω)) Ω).toSubring := by
    rw [e]
    exact NormAt.isLocalRing_regAt p
  have hr : ∀ q : Cpt ξ', f q.1 = p.1 →
      regAt ξ' q = (integralClosure ((regAt ξ p).map (RingHom.id Ω)) Ω).toSubring := fun q hq => by
    obtain ⟨P, hP, h⟩ := hN.exists_max q hq
    exact h.trans (NormAt.ofPrime_of_isLocalRing _ P hP)
  refine ⟨?_, fun q hq => ?_, hN.dom⟩
  · obtain ⟨q, hq, hu⟩ := hN.existsUnique _ (IsLocalRing.maximalIdeal.isMaximal _)
    exact ⟨q, hq.1, fun q' hq' => hu q' ⟨hq', (hr q' hq').trans
      (NormAt.ofPrime_of_isLocalRing _ _ (IsLocalRing.maximalIdeal.isMaximal _)).symm⟩⟩
  · rw [hr q hq, e, Subring.map_id]

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalIsoOfIntegrallyClosedStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
alias GlobalTheory.T.normal_iso_of_integrally_closed := GlobalTheory.CompanionTheory.Ar.NormAt.isoAt_of_integrallyClosed
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueSection
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.RegSection

theorem section_eq {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ)
    (U : X.Opens) (hU : ∀ q ∈ U, genPt ξ ⤳ q) (s t : Γ(X, U))
    (e : ∀ q (hq : q ∈ U), genMap ξ ⟨q, hU q hq⟩ (X.presheaf.germ U q hq s) =
      genMap ξ ⟨q, hU q hq⟩ (X.presheaf.germ U q hq t)) : s = t :=
  TopCat.Presheaf.section_ext X.sheaf U s t fun q hq => h.inj ⟨q, hU q hq⟩ (e q hq)

theorem existsUnique_section : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X], IsCptGen ξ → ∀ (U : X.Opens) (hU : ∀ q ∈ U, genPt ξ ⤳ q) (a : Ω), (U : Set X).Nonempty → (∀ q (hq : q ∈ U), a ∈ regAt ξ ⟨q, hU q hq⟩) → ∃! g : Γ(X, U), ∀ q (hq : q ∈ U), genMap ξ ⟨q, hU q hq⟩ (X.presheaf.germ U q hq g) = a := by
  intro X Ω _ ξ _ h U hU a _ ha
  have loc : ∀ x : U, ∃ (W : X.Opens) (_ : W ≤ U) (hx : x.1 ∈ W) (t : Γ(X, W)),
      genMap ξ ⟨x.1, hU x.1 x.2⟩ (X.presheaf.germ W x.1 hx t) = a := by
    intro x
    obtain ⟨g, hg⟩ := ha x.1 x.2
    obtain ⟨W, hx, t, rfl⟩ := X.presheaf.exists_germ_eq g
    refine ⟨W ⊓ U, inf_le_right, ⟨hx, x.2⟩, X.presheaf.map (homOfLE inf_le_left).op t, ?_⟩
    exact (congrArg (genMap ξ ⟨x.1, hU x.1 x.2⟩) (TopCat.Presheaf.germ_res_apply X.presheaf
      (homOfLE inf_le_left : W ⊓ U ⟶ W) x.1 ⟨hx, x.2⟩ t)).trans hg
  choose W hWU hx t ht using loc
  have val : ∀ (x : U) (y : X) (hy : y ∈ W x),
      genMap ξ ⟨y, hU y (hWU x hy)⟩ (X.presheaf.germ (W x) y hy (t x)) = a := fun x y hy =>
    (genMap_germ_eq_genMap_germ ξ (W x) ⟨y, hU y (hWU x hy)⟩ ⟨x.1, hU x.1 x.2⟩ hy (hx x) (t x)).trans (ht x)
  have compat : TopCat.Presheaf.IsCompatible X.sheaf.obj W t := by
    intro i j
    apply TopCat.Presheaf.section_ext X.sheaf (W i ⊓ W j)
    rintro y ⟨hi, hj⟩
    apply h.inj ⟨y, hU y (hWU i hi)⟩
    exact (congrArg (genMap ξ ⟨y, hU y (hWU i hi)⟩) (TopCat.Presheaf.germ_res_apply X.presheaf
      (TopologicalSpace.Opens.infLELeft (W i) (W j)) y ⟨hi, hj⟩ (t i))).trans
      ((val i y hi).trans ((val j y hj).symm.trans
        (congrArg (genMap ξ ⟨y, hU y (hWU i hi)⟩) (TopCat.Presheaf.germ_res_apply X.presheaf
          (TopologicalSpace.Opens.infLERight (W i) (W j)) y ⟨hi, hj⟩ (t j))).symm))
  have hcov : U ≤ iSup W := fun y hy =>
    TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hx ⟨y, hy⟩⟩
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W U (fun i => homOfLE (hWU i)) hcov t compat
  have spec : ∀ q (hq : q ∈ U), genMap ξ ⟨q, hU q hq⟩ (X.presheaf.germ U q hq s) = a := by
    intro q hq
    have e := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (hWU ⟨q, hq⟩)) q (hx ⟨q, hq⟩) s
    have e2 : (X.presheaf.map (homOfLE (hWU ⟨q, hq⟩)).op).hom s = t ⟨q, hq⟩ := hs ⟨q, hq⟩
    exact (congrArg (genMap ξ ⟨q, hU q hq⟩) e).symm.trans
      ((congrArg (fun z => genMap ξ ⟨q, hU q hq⟩ ((X.presheaf.germ (W ⟨q, hq⟩) q (hx ⟨q, hq⟩)).hom z)) e2).trans
        (ht ⟨q, hq⟩))
  exact ⟨s, spec, fun s' hs' => section_eq h U hU s' s fun q hq => (hs' q hq).trans (spec q hq).symm⟩

end GlobalTheory.CompanionTheory.Ar.Flat.RegSection
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameCoeffsRegularInChart
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameCoeffsRegularInChart
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory

theorem twist_left_inverse : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type)
    [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (m n r : ℕ) (φ : Fin n → Module.Dual Ω E),
    IsTwistGen ξ x L m φ → ∀ (p : Cpt ξ) (c₁ : κ), InChart ξ x c₁ p → ∀ β : Fin r → E, L.IsFrameAt β p →
    ∃ B : Matrix (Fin r) (Fin n) Ω, (∀ a j, B a j ∈ regAt ξ p) ∧ (∀ j a, φ j (β a) / x c₁ ^ m ∈ regAt ξ p) ∧
      B * Matrix.of (fun j a => φ j (β a) / x c₁ ^ m) = 1 := by
  intro X Ω _ ξ E _ _ κ x L m n r φ hT p c₁ hc β hβ
  have hβmem : ∀ a, β a ∈ L p := fun a => by
    rw [hβ.2]
    exact Submodule.subset_span ⟨a, rfl⟩
  have hw : ∀ a : Fin r, ∃ w : Module.Dual Ω E, ∀ b, w (β b) = if a = b then 1 else 0 := by
    intro a
    obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span hβ.1).coord a)
    refine ⟨g, fun b => ?_⟩
    have h1 : g (β b) = ((Module.Basis.span hβ.1).coord a) ((Module.Basis.span hβ.1) b) := by
      rw [← hg, LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.span_apply]
    rw [h1, Module.Basis.coord_apply, Module.Basis.repr_self]
    by_cases h : a = b
    · subst h
      simp
    · simp [Finsupp.single_apply, h, Ne.symm h]
  choose w hw using hw
  have hwR : ∀ a, ∀ e ∈ L p, w a e ∈ regAt ξ p := by
    intro a e he
    rw [hβ.2] at he
    induction he using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      rw [hw]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    | zero =>
      rw [map_zero]
      exact zero_mem _
    | add y z _ _ hy hz =>
      rw [map_add (f := _)]
      exact add_mem hy hz
    | smul s y _ hy =>
      rw [Subring.smul_def, map_smul, smul_eq_mul]
      exact mul_mem s.2 hy
  have hg := fun a => hT.2 p c₁ hc (w a) (hwR a)
  choose g hgR hgw using hg
  refine ⟨Matrix.of fun a j => g a j, fun a j => hgR a j, fun j a => hT.1 j p c₁ hc (β a) (hβmem a), ?_⟩
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.of_apply]
  rw [← hgw a (β b) (hβmem b), hw]

end GlobalTheory.CompanionTheory.Ar.FlagBun
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameCoeffsRegularInChartStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
alias GlobalTheory.T.frame_coeffs_regular_in_chart := GlobalTheory.CompanionTheory.Ar.FlagBun.twist_left_inverse
end
end
