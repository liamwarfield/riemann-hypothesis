module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HenselianAlgClosedResidue

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GenericPointOpenImmersion
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GenericPointOpenImmersion
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.ValGeneric

theorem exists_pow_mem_of_ne_zero (R : Type) [CommRing R] [IsDomain R] [ValuationRing R]
    [Ring.DimensionLEOne R] :
    ∃ π : R, π ≠ 0 ∧ ∀ b : R, b ≠ 0 → ∃ (n : ℕ) (c : R), π ^ n = b * c := by
  by_cases hm : IsLocalRing.maximalIdeal R = ⊥
  · refine ⟨1, one_ne_zero, fun b hb => ?_⟩
    have hu : IsUnit b := by
      by_contra h
      have hbm : b ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal b).2 h
      rw [hm] at hbm
      exact hb (by simpa using hbm)
    obtain ⟨u, rfl⟩ := hu
    exact ⟨0, ((u⁻¹ : Rˣ) : R), by simp⟩
  · obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
    refine ⟨π, hπ0, fun b hb => ?_⟩
    by_cases hu : IsUnit b
    · obtain ⟨u, rfl⟩ := hu
      exact ⟨0, ((u⁻¹ : Rˣ) : R), by simp⟩
    have hrad : π ∈ (Ideal.span {b}).radical := by
      rw [Ideal.radical_eq_sInf]
      refine Ideal.mem_sInf.2 ?_
      rintro J ⟨hbJ, hJ⟩
      have hbJ' : b ∈ J := hbJ (Ideal.mem_span_singleton_self b)
      have hJ0 : J ≠ ⊥ := fun h => hb (by simpa [h] using hbJ')
      have hmax := Ring.DimensionLEOne.maximalOfPrime hJ0 hJ
      rw [IsLocalRing.eq_maximalIdeal hmax]
      exact hπ
    obtain ⟨n, hn⟩ := hrad
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
    exact ⟨n, c, by rw [← hc, mul_comm]⟩

theorem isOpenImmersion_spMap_fraction :
    ∀ (C : Type) [Field C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    [Algebra R C] [IsFractionRing R C], IsOpenImmersion (spMap (algebraMap R C)) := by
  intro C _ R _ _ _ _ _ _
  obtain ⟨π, hπ0, h⟩ := exists_pow_mem_of_ne_zero R
  have inj := IsFractionRing.injective R C
  haveI : IsLocalization.Away π C := by
    refine IsLocalization.Away.mk π ?_ ?_ ?_
    · exact ((map_ne_zero_iff _ inj).2 hπ0).isUnit
    · intro s
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) s
      obtain ⟨n, c, hc⟩ := h b (nonZeroDivisors.ne_zero hb)
      refine ⟨n, a * c, ?_⟩
      have hb' : algebraMap R C b ≠ 0 :=
        (map_ne_zero_iff _ inj).2 (nonZeroDivisors.ne_zero hb)
      rw [← map_pow, hc, map_mul, map_mul]
      field_simp
    · intro a b hab
      exact ⟨0, by rw [inj hab]⟩
  exact IsOpenImmersion.of_isLocalization π

end GlobalTheory.CompanionTheory.ValGeneric
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GenericPointOpenImmersionStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_point_open_immersion : ∀ (C : Type) [Field C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    [Algebra R C] [IsFractionRing R C], IsOpenImmersion (spMap (algebraMap R C)) := by
  first | exact @GlobalTheory.CompanionTheory.ValGeneric.isOpenImmersion_spMap_fraction | exact GlobalTheory.CompanionTheory.ValGeneric.isOpenImmersion_spMap_fraction | (intros; apply GlobalTheory.CompanionTheory.ValGeneric.isOpenImmersion_spMap_fraction <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PicardMayerVietorisExtend
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PicardMayerVietorisExtend
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.CechMV

theorem exists_extend_of_pull_inf_eq_zero (X : Scheme.{0}) (W V : X.Opens) (p : Pic W.toScheme)
    (hp : pull (X.homOfLE (inf_le_left : W ⊓ V ≤ W)) p = 0) :
    ∃ q : Pic (W ⊔ V).toScheme, pull (X.homOfLE (le_sup_left : W ≤ W ⊔ V)) q = p := by
  obtain ⟨N, hN, rfl⟩ := cls_surj p
  have sq : IsPullback (X.homOfLE (inf_le_left : W ⊓ V ≤ W)) (X.homOfLE (inf_le_right : W ⊓ V ≤ V))
      (X.homOfLE (le_sup_left : W ≤ W ⊔ V)) (X.homOfLE (le_sup_right : V ≤ W ⊔ V)) :=
    isPullback_opens_inf_le le_sup_left le_sup_right
  have hcov : Set.range (X.homOfLE (le_sup_left : W ≤ W ⊔ V)) ∪
      Set.range (X.homOfLE (le_sup_right : V ≤ W ⊔ V)) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    rcases x.2 with h | h
    · refine Or.inl ⟨⟨x.1, h⟩, ?_⟩
      exact Subtype.ext (by simp [Scheme.homOfLE_apply])
    · refine Or.inr ⟨⟨x.1, h⟩, ?_⟩
      exact Subtype.ext (by simp [Scheme.homOfLE_apply])
  have hT := LB.isLB_triv V.toScheme
  have iso : LBIso (N.pull (X.homOfLE (inf_le_left : W ⊓ V ≤ W)))
      ((LB.triv V.toScheme).pull (X.homOfLE (inf_le_right : W ⊓ V ≤ V))) := by
    refine (cls_eq_iff (pull_isLB hN _) (pull_isLB hT _)).1 ?_
    rw [cls_pull hN _ (pull_isLB hN _), cls_pull hT _ (pull_isLB hT _), hp]
    exact (map_zero (pull (X.homOfLE (inf_le_right : W ⊓ V ≤ V)))).symm
  obtain ⟨L, hL, e, -⟩ := GlobalTheory.GlueTwoLB.glue _ _ _ _ _ _ _ _ N (LB.triv V.toScheme) inferInstance inferInstance
    sq hcov hN hT iso
  exact ⟨cls L hL, ((cls_eq_iff hN (pull_isLB hL _)).2 e).symm⟩

end GlobalTheory.CompanionTheory.CechMV
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PicardMayerVietorisExtendStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.picard_mayer_vietoris_extend : ∀ (X : Scheme.{0}) (W V : X.Opens) (p : Pic W.toScheme),
    pull (X.homOfLE (inf_le_left : W ⊓ V ≤ W)) p = 0 →
    ∃ q : Pic (W ⊔ V).toScheme, pull (X.homOfLE (le_sup_left : W ≤ W ⊔ V)) q = p := by
  first | exact @GlobalTheory.CompanionTheory.CechMV.exists_extend_of_pull_inf_eq_zero | exact GlobalTheory.CompanionTheory.CechMV.exists_extend_of_pull_inf_eq_zero | (intros; apply GlobalTheory.CompanionTheory.CechMV.exists_extend_of_pull_inf_eq_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PicardGenericFibreInjective
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PicardGenericFibreInjective
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.CompanionTheory.ValFibre

theorem isUnit_of_basicOpen_eq_top' {Y : Scheme.{0}} (a : Γ(Y, ⊤)) (h : Y.basicOpen a = ⊤) :
    IsUnit a := by
  have key : ∀ (g : Opposite.op (⊤ : Y.Opens) ⟶ Opposite.op (Y.basicOpen a))
      (g' : Opposite.op (Y.basicOpen a) ⟶ Opposite.op ⊤),
      (Y.presheaf.map g').hom ((Y.presheaf.map g).hom a) = a := by
    intro g g'
    rw [← CommRingCat.comp_apply, ← Functor.map_comp, Subsingleton.elim (g ≫ g') (𝟙 _),
      CategoryTheory.Functor.map_id, CommRingCat.id_apply]
  have u := (Y.toRingedSpace.isUnit_res_basicOpen a).map
    (Y.presheaf.map (homOfLE (le_of_eq h.symm)).op).hom
  convert u using 1
  exact (key _ _).symm

theorem point_cases (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    (r : Sp R) : r.asIdeal = ⊥ ∨ r = IsLocalRing.closedPoint R := by
  by_cases h : r.asIdeal = ⊥
  · exact .inl h
  · refine .inr (PrimeSpectrum.ext ?_)
    have := Ring.DimensionLEOne.maximalOfPrime h r.isPrime
    exact IsLocalRing.eq_maximalIdeal this

theorem exists_factor (R C : Type) [CommRing R] [IsDomain R] [Field C] [Algebra R C] [IsFractionRing R C]
    {Y : Scheme.{0}} (f : Y ⟶ Sp R) (hf : ∀ y : Y, (f y).asIdeal = ⊥) :
    ∃ g : Y ⟶ Sp C, g ≫ spMap (algebraMap R C) = f := by
  let ψ : R →+* Γ(Y, ⊤) := (f.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have hu : ∀ r : nonZeroDivisors R, IsUnit (ψ r) := by
    intro r
    refine isUnit_of_basicOpen_eq_top' _ (top_unique fun y _ => ?_)
    show y ∈ Y.basicOpen (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r.1))
    rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
    show r.1 ∉ (f y).asIdeal
    rw [hf y]
    exact nonZeroDivisors.ne_zero r.2
  let φ : C →+* Γ(Y, ⊤) := IsLocalization.lift (M := nonZeroDivisors R) hu
  have hφ : φ.comp (algebraMap R C) = ψ := IsLocalization.lift_comp hu
  refine ⟨Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ), ?_⟩
  have e : (Sp R).toSpecΓ = Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    rw [← Scheme.isoSpec_hom, Scheme.isoSpec_Spec_hom]
  have h1 : CommRingCat.ofHom (algebraMap R C) ≫ CommRingCat.ofHom φ =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop := by
    rw [← CommRingCat.ofHom_comp, hφ]
    rfl
  rw [Category.assoc, spMap, ← Spec.map_comp, h1, Spec.map_comp, ← Category.assoc,
    ← Scheme.toSpecΓ_naturality, Category.assoc, e, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.comp_id]

theorem geometricallyIntegral_open {X S : Scheme.{0}} (p : X ⟶ S) [GeometricallyIntegral p] (Y : X.Opens)
    (hY : ∀ s : S, ∃ y : X, y ∈ Y ∧ p y = s) : GeometricallyIntegral (Y.ι ≫ p) := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  let g : Z ⟶ pullback p y := pullback.lift (fst ≫ Y.ι) snd (by simpa using h.w)
  have hg : IsPullback fst g Y.ι (pullback.fst p y) :=
    IsPullback.of_bot (by simpa [g] using h) (by simp [g]) (IsPullback.of_hasPullback p y)
  have : IsOpenImmersion g := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hg inferInstance
  have : IsIntegral (pullback p y) :=
    GeometricallyIntegral.geometrically_isIntegral y _ _ (IsPullback.of_hasPullback p y)
  have : Nonempty Z := by
    obtain ⟨x, hx, hxs⟩ := hY (y (IsLocalRing.closedPoint K))
    obtain ⟨z, hz, hz'⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := Y.ι ≫ p) (g := y) (⟨x, hx⟩ : Y) (IsLocalRing.closedPoint K) (by simpa using hxs)
    exact ⟨h.isoPullback.inv z⟩
  exact isIntegral_of_isOpenImmersion g

theorem eq_zero_of_pull_generic_eq_zero : ∀ (C : Type) [Field C] [IsAlgClosed C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    [Algebra R C] [IsFractionRing R C] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ Y : A.left.Opens, IsCompact (Y : Set A.left) →
    ∀ q : Pic Y.toScheme, pull (pullback.fst A.hom (spMap (algebraMap R C)) ∣_ Y) q = 0 → q = 0 := by
  intro C _ _ R _ _ _ _ _ _ A _ hA Y hY q hq
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have hGI : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected
  have hsq : IsPullback (pullback.fst A.hom (spMap (algebraMap R C)) ∣_ Y)
      ((pullback.fst A.hom (spMap (algebraMap R C)) ⁻¹ᵁ Y).ι ≫ pullback.snd A.hom (spMap (algebraMap R C)))
      (Y.ι ≫ A.hom) (spMap (algebraMap R C)) :=
    IsPullback.paste_vert (isPullback_morphismRestrict _ _) (IsPullback.of_hasPullback _ _)
  by_cases hc : ∃ x : A.left, x ∈ Y ∧ A.hom x = IsLocalRing.closedPoint R
  · obtain ⟨x, hxY, hx⟩ := hc
    have hgen : ∀ r : Sp R, ∃ y : A.left, y ∈ Y ∧ A.hom y = r := by
      intro r
      have hs : r ⤳ A.hom x := by
        rw [hx]
        exact IsLocalRing.specializes_closedPoint r
      obtain ⟨y, hy, hyr⟩ := (Flat.generalizingMap A.hom) hs
      exact ⟨y, hy.mem_open Y.isOpen hxY, hyr⟩
    have : GeometricallyIntegral (Y.ι ≫ A.hom) := geometricallyIntegral_open _ _ hgen
    have : CompactSpace Y.toScheme := isCompact_iff_compactSpace.1 hY
    have : QuasiCompact (Y.ι ≫ A.hom) := (quasiCompact_iff_compactSpace _).2 inferInstance
    obtain ⟨M, hM, rfl⟩ := cls_surj q
    refine (cls_eq_zero_iff hM).2 ?_
    refine GlobalTheory.ValGenExtend.triv_of_triv_generic R C _ _ (Y.ι ≫ A.hom) _ _ hsq inferInstance inferInstance
      inferInstance M hM ?_
    exact (cls_eq_zero_iff (pull_isLB hM _)).1 hq
  · have hall : ∀ y : Y.toScheme, ((Y.ι ≫ A.hom) y).asIdeal = ⊥ := by
      intro y
      refine (point_cases R _).resolve_right fun h => hc ⟨y.1, y.2, ?_⟩
      simpa using h
    obtain ⟨g, hg⟩ := exists_factor R C (Y.ι ≫ A.hom) hall
    have e := hsq.lift_fst (𝟙 _) g (by simpa using hg.symm)
    have := pull_comp (hsq.lift (𝟙 _) g (by simpa using hg.symm))
      (pullback.fst A.hom (spMap (algebraMap R C)) ∣_ Y) q
    rw [e, pull_id, hq, map_zero] at this
    exact this

end GlobalTheory.CompanionTheory.ValFibre
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PicardGenericFibreInjectiveStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.picard_generic_fibre_injective : ∀ (C : Type) [Field C] [IsAlgClosed C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    [Algebra R C] [IsFractionRing R C] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ Y : A.left.Opens, IsCompact (Y : Set A.left) →
    ∀ q : Pic Y.toScheme, pull (pullback.fst A.hom (spMap (algebraMap R C)) ∣_ Y) q = 0 → q = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ValFibre.eq_zero_of_pull_generic_eq_zero | exact GlobalTheory.CompanionTheory.ValFibre.eq_zero_of_pull_generic_eq_zero | (intros; apply GlobalTheory.CompanionTheory.ValFibre.eq_zero_of_pull_generic_eq_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SectionThroughClosedPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SectionThroughClosedPoint
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CompanionTheory.Sections

theorem exists_section_fibre {R : Type} [CommRing R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] (X : Over (Sp R)) (hX : Smooth X.hom)
    (y : ↥(pullback X.hom (spMap (IsLocalRing.residue R)))) (hy : IsClosed {y}) :
    ∃ s : 𝟙_ (Over (Sp R)) ⟶ X, s.left (IsLocalRing.closedPoint R) =
      pullback.fst X.hom (spMap (IsLocalRing.residue R)) y := by
  let x₀ := pointOfClosedPoint (pullback.snd X.hom (spMap (IsLocalRing.residue R))) y hy
  obtain ⟨⟨s, hs⟩, e⟩ := GlobalTheory.reducePoint_residue_surjective X.hom R (𝟙 _)
    ⟨x₀ ≫ pullback.fst _ _, by
      rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc, Category.comp_id]⟩
  have e' : spMap (IsLocalRing.residue R) ≫ s = x₀ ≫ pullback.fst _ _ := congrArg Subtype.val e
  refine ⟨Over.homMk s hs, ?_⟩
  have e2 : s (PrimeSpectrum.comap (IsLocalRing.residue R) (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) =
      pullback.fst X.hom (spMap (IsLocalRing.residue R)) (x₀ (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) :=
    congr($e' (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)))
  rw [IsLocalRing.comap_closedPoint] at e2
  exact e2.trans (congrArg _ (pointOfClosedPoint_apply _ y hy _))

theorem exists_section_closed {R : Type} [CommRing R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] (X : Over (Sp R)) (hX : Smooth X.hom) {z : X.left}
    (hz : X.hom z = IsLocalRing.closedPoint R) (hc : IsClosed {z}) :
    ∃ s : 𝟙_ (Over (Sp R)) ⟶ X, s.left (IsLocalRing.closedPoint R) = z := by
  have : IsClosedImmersion (spMap (IsLocalRing.residue R)) :=
    .spec_of_surjective _ IsLocalRing.residue_surjective
  obtain ⟨y, rfl⟩ : z ∈ Set.range (pullback.fst X.hom (spMap (IsLocalRing.residue R))) := by
    rw [GlobalTheory.range_fst_residue]; exact hz
  refine exists_section_fibre X hX y ?_
  have := hc.preimage (pullback.fst X.hom (spMap (IsLocalRing.residue R))).continuous
  rwa [← Set.image_singleton, Set.preimage_image_eq _
    (pullback.fst X.hom (spMap (IsLocalRing.residue R))).isClosedEmbedding.injective] at this

theorem exists_section_open {R : Type} [CommRing R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] (X : Over (Sp R)) (hX : Smooth X.hom)
    {U : Set X.left} (hU : IsOpen U) {z : X.left} (hzU : z ∈ U)
    (hz : X.hom z = IsLocalRing.closedPoint R) :
    ∃ s : 𝟙_ (Over (Sp R)) ⟶ X, s.left (IsLocalRing.closedPoint R) ∈ U := by
  have : IsClosedImmersion (spMap (IsLocalRing.residue R)) :=
    .spec_of_surjective _ IsLocalRing.residue_surjective
  obtain ⟨y, rfl⟩ : z ∈ Set.range (pullback.fst X.hom (spMap (IsLocalRing.residue R))) := by
    rw [GlobalTheory.range_fst_residue]; exact hz
  have : JacobsonSpace ↥(pullback X.hom (spMap (IsLocalRing.residue R))) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd X.hom (spMap (IsLocalRing.residue R)))
  obtain ⟨c, hc, hc'⟩ := nonempty_inter_closedPoints
    (Z := pullback.fst X.hom (spMap (IsLocalRing.residue R)) ⁻¹' U) ⟨y, hzU⟩
    (hU.preimage (pullback.fst X.hom (spMap (IsLocalRing.residue R))).continuous).isLocallyClosed
  obtain ⟨s, hs⟩ := exists_section_fibre X hX c hc'
  exact ⟨s, hs ▸ hc⟩

theorem exists_section :
    ∀ (R : Type) [CommRing R] [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)] (X : Over (Sp R)), Smooth X.hom →
    (∀ z : X.left, IsClosed {z} → X.hom z = IsLocalRing.closedPoint R →
      ∃ s : 𝟙_ (Over (Sp R)) ⟶ X, s.left (IsLocalRing.closedPoint R) = z) ∧
    (∀ U : X.left.Opens, (∃ z ∈ U, X.hom z = IsLocalRing.closedPoint R) →
      ∃ s : 𝟙_ (Over (Sp R)) ⟶ X, s.left (IsLocalRing.closedPoint R) ∈ U) := by
  intro R _ _ _ X hX
  refine ⟨fun z hc hz => exists_section_closed X hX hz hc, ?_⟩
  rintro U ⟨z, hzU, hz⟩
  exact exists_section_open X hX U.isOpen hzU hz

end GlobalTheory.CompanionTheory.Sections
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SectionThroughClosedPointStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_through_closed_point : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)] (X : Over (Sp R)), Smooth X.hom →
    (∀ z : X.left, IsClosed {z} → X.hom z = IsLocalRing.closedPoint R →
      ∃ s : 𝟙_ (Over (Sp R)) ⟶ X, s.left (IsLocalRing.closedPoint R) = z) ∧
    (∀ U : X.left.Opens, (∃ z ∈ U, X.hom z = IsLocalRing.closedPoint R) →
      ∃ s : 𝟙_ (Over (Sp R)) ⟶ X, s.left (IsLocalRing.closedPoint R) ∈ U) := by
  first | exact @GlobalTheory.CompanionTheory.Sections.exists_section | exact GlobalTheory.CompanionTheory.Sections.exists_section | (intros; apply GlobalTheory.CompanionTheory.Sections.exists_section <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RelAmpleOfSamePolarization
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RelAmpleOfSamePolarization
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.AmpleForm

theorem relAmple_of_lam_eq : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B →
    ∀ (M L : LB B.left) (hM : M.IsLB) (hL : L.IsLB), Out.RelAmple B L → Out.KTriv B L →
    lam (cls M hM) (fst B B) (snd B B) = lam (cls L hL) (fst B B) (snd B B) → Out.RelAmple B M := by
  intro K _ _ B _ hB M L hM hL ha hk hlam
  have := hB.comm
  obtain ⟨O, hO, eO⟩ := CechPic.cls_surj (cls M hM - cls L hL)
  have hlam0 : lam (cls O hO) (fst B B) (snd B B) = 0 := by
    rw [eO, PrimitiveOverField.lam_sub, hlam, sub_self]
  obtain ⟨x, hx⟩ := GlobalTheory.PointTranslate.exists_point_cls_eq_lam K B hB L hL hk O hO hlam0
  have hN : (RigidTranslate.rigTransl L x).IsLB := DVR.linComb_isLB _ hL _ _
  have hA := RigidTranslate.relAmple_rigTransl_point K B hB L hL x ha
  have e1 := PrimitiveOverField.lam_const (cls L hL) x (𝟙 B)
  have e2 : ((toUnit B ≫ x) * 𝟙 B) = PolTranslate.transl x := by
    rw [PolTranslate.transl, _root_.mul_comm]
  have e3 : CechPic.pull (toUnit B ≫ x).left (cls L hL) = 0 := by
    rw [Over.comp_left, CechPic.pull_comp, ThetaExtend.pic_local (CechPic.pull x.left (cls L hL)), map_zero]
  have e : cls M hM = cls _ hN := by
    rw [CechPic.cls_linComb hL, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, e3, neg_zero, add_zero]
    rw [e2, Over.id_left, CechPic.pull_id] at e1
    exact sub_left_inj.1 (eO.symm.trans (hx.trans e1))
  have hN' := pull_isLB hN (𝟙 _)
  have e' : cls M hM = cls _ hN' := by
    rw [CechPic.cls_pull hN, CechPic.pull_id]; exact e
  obtain ⟨w, hw⟩ := (CechPic.cls_eq_iff hM hN').1 e'
  exact relAmple_pull (A' := B) (A := B) (φ := 𝟙 _) (f := 𝟙 _)
    (IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩) hN hM ((isGen_iff w).1 hw) ⊤
    (isAffineOpen_top _) (fun _ => trivial) hA

end GlobalTheory.CompanionTheory.AmpleForm
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RelAmpleOfSamePolarizationStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rel_ample_of_same_polarization : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B →
    ∀ (M L : LB B.left) (hM : M.IsLB) (hL : L.IsLB), Out.RelAmple B L → Out.KTriv B L →
    lam (cls M hM) (fst B B) (snd B B) = lam (cls L hL) (fst B B) (snd B B) → Out.RelAmple B M := by
  first | exact @GlobalTheory.CompanionTheory.AmpleForm.relAmple_of_lam_eq | exact GlobalTheory.CompanionTheory.AmpleForm.relAmple_of_lam_eq | (intros; apply GlobalTheory.CompanionTheory.AmpleForm.relAmple_of_lam_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ValuationIntegersRankOne
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ValuationIntegersRankOne
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin

theorem integers_valuationRing_dimensionLEOne_isFractionRing :
    ∀ (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R →
    ∃ (_ : IsDomain R), ValuationRing R ∧ Ring.DimensionLEOne R ∧ IsFractionRing R C := by
  intro C _ _ v R _ _ hv
  haveI hdom : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj
  haveI hval : ValuationRing R := ValuationRing.of_integers v hv
  refine ⟨hdom, hval, ⟨?_⟩, ?_⟩
  · intro p hp0 hp
    have hle : IsLocalRing.maximalIdeal R ≤ p := by
      intro x hx
      by_cases hx0 : x = 0
      · rw [hx0]; exact p.zero_mem
      obtain ⟨y, hyp, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp0
      have hxu : ¬ IsUnit x := by
        simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hx
      have hvx : v (algebraMap R C x) < 1 :=
        lt_of_le_of_ne (hv.map_le_one x) fun e => hxu (hv.isUnit_iff_valuation_eq_one.2 e)
      have hvy : 0 < v (algebraMap R C y) := by
        rw [zero_lt_iff, Valuation.ne_zero_iff]
        exact fun e => hy0 (hv.hom_inj (by rw [e, map_zero]))
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hvy hvx
      have hdvd : y ∣ x ^ n := by
        rw [hv.dvd_iff_le, map_pow, map_pow]
        exact hn.le
      exact hp.mem_of_pow_mem n (p.mem_of_dvd hdvd hyp)
    have heq : p = IsLocalRing.maximalIdeal R :=
      le_antisymm (IsLocalRing.le_maximalIdeal hp.ne_top) hle
    rw [heq]
    exact IsLocalRing.maximalIdeal.isMaximal R
  · haveI : FaithfulSMul R C := (faithfulSMul_iff_algebraMap_injective R C).2 hv.hom_inj
    refine IsFractionRing.of_field R C fun z => ?_
    by_cases hz0 : z = 0
    · exact ⟨0, 1, by simp [hz0]⟩
    rcases le_total (v z) 1 with h | h
    · obtain ⟨a, ha⟩ := hv.exists_of_le_one h
      exact ⟨a, 1, by simp [ha]⟩
    · have h' : v z⁻¹ ≤ 1 := by
        rw [map_inv₀]
        exact inv_le_one_of_one_le₀ h
      obtain ⟨a, ha⟩ := hv.exists_of_le_one h'
      exact ⟨1, a, by simp [ha]⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ValuationIntegersRankOneStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_integers_rank_one : ∀ (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R →
    ∃ (_ : IsDomain R), ValuationRing R ∧ Ring.DimensionLEOne R ∧ IsFractionRing R C := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.integers_valuationRing_dimensionLEOne_isFractionRing | exact GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.integers_valuationRing_dimensionLEOne_isFractionRing | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.integers_valuationRing_dimensionLEOne_isFractionRing <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PicardGenericTrivialNearSpecial
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PicardGenericTrivialNearSpecial
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.NearZero


open GlobalTheory.PrimSec in
theorem exists_open_pull_eq_zero {O K : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Ring.DimensionLEOne O]
    [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] {X XK : Scheme.{0}} {f : X ⟶ Sp O} {j : XK ⟶ X}
    {fK : XK ⟶ Sp K} (H : IsPullback j fK f (spMap (algebraMap O K))) [Smooth f] [GeometricallyIntegral f]
    {x : X} (hfx : f x = IsLocalRing.closedPoint O) (l : Pic XK) :
    ∃ V : X.Opens, (∃ y ∈ V, f y = IsLocalRing.closedPoint O) ∧ pull (j ⁻¹ᵁ V).ι l = 0 := by
  haveI : IsIntegral XK := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
  obtain ⟨V, hV, hxV, -, n, φ, hφ, hφ'⟩ := exists_etale_chart f (U := ⊤) (x := x) trivial
  have hp := isPrime_map f hV hxV hfx
  have hinj := app_injective H V
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hne : Nonempty (j ⁻¹ᵁ V) :=
    nonempty_of_ne_zero (a := 1) fun h => one_ne_zero (hinj ((map_one _).trans (h.trans (map_zero _).symm)))
  haveI : IsDomain Γ(X, V) := hinj.isDomain _
  obtain ⟨⟨p, hpV⟩⟩ := id hne
  obtain ⟨W, hpW, hW⟩ := exists_pull_eq_zero l p
  have hjV : IsAffineOpen (j ⁻¹ᵁ V) := by
    haveI : IsAffineHom j := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
    exact hV.preimage j
  obtain ⟨σ, hσW, hpσ⟩ := hjV.exists_basicOpen_le (V := W) ⟨p, hpW⟩ hpV
  obtain ⟨π, b, hπ, hb⟩ := exists_numerator H hV σ
  have hπ' : algebraMap O K π ≠ 0 := fun h => hπ (IsFractionRing.injective O K (h.trans (map_zero _).symm))
  have hc : ∀ c : K, c ≠ 0 → ∀ z ∈ j ⁻¹ᵁ V, z ∈ XK.basicOpen (AbLaw.cst fK (j ⁻¹ᵁ V) c) := fun c hc z hz =>
    (mem_basicOpen_cst fK _ c hz).2 fun h => hc (by
      haveI := (fK z).isPrime
      have e : (fK z).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
      rw [e] at h
      exact h)
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hb
    have h0 : p ∈ XK.basicOpen (0 : Γ(XK, j ⁻¹ᵁ V)) := by
      rw [hb, Scheme.basicOpen_mul]
      exact ⟨hc _ hπ' p hpV, hpσ⟩
    rw [Scheme.basicOpen_zero] at h0
    exact h0
  letI := (AbLaw.cst f V).toAlgebra
  letI := φ.toAlgebra
  haveI : IsScalarTower O (MvPolynomial (Fin n) O) Γ(X, V) := .of_algebraMap_eq' hφ.symm
  haveI : Algebra.Etale (MvPolynomial (Fin n) O) Γ(X, V) := hφ'
  obtain ⟨ρ, b', e, hb'⟩ := GlobalTheory.etale_mvPolynomial_exists_content O K n Γ(X, V) hp b hb0
  obtain ⟨y, hy⟩ := hV.isoSpec.hom.surjective
    (⟨(IsLocalRing.maximalIdeal O).map (AbLaw.cst f V), hp⟩ : PrimeSpectrum Γ(X, V))
  have hy' : (hV.primeIdealOf y).asIdeal = (IsLocalRing.maximalIdeal O).map (AbLaw.cst f V) :=
    congrArg PrimeSpectrum.asIdeal hy
  refine ⟨X.basicOpen b', ⟨y.1, (mem_basicOpen_iff hV y b').2 (hy' ▸ hb'), ?_⟩,
    pull_eq_zero_of_mem W _ (fun z => ?_) hW⟩
  · refine PrimeSpectrum.ext (((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (f y.1).isPrime.ne_top
      fun a ha => ?_).symm)
    by_contra h
    exact (mem_basicOpen_iff hV y _).1 ((mem_basicOpen_cst f V a y.2).2 h) (hy' ▸ Ideal.mem_map_of_mem _ ha)
  · have hz : j z.1 ∈ X.basicOpen b' := z.2
    have hzV : z.1 ∈ j ⁻¹ᵁ V := X.basicOpen_le b' hz
    have hz' : z.1 ∈ XK.basicOpen ((j.app V).hom b') := by
      rw [← Scheme.preimage_basicOpen]
      exact hz
    have hρ : algebraMap O K ρ ≠ 0 := fun h => hb0 (by
      rw [e, IsFractionRing.injective O K (h.trans (map_zero _).symm), map_zero, zero_mul])
    have e' : (j.app V).hom b = AbLaw.cst fK (j ⁻¹ᵁ V) (algebraMap O K ρ) * (j.app V).hom b' := by
      rw [e, map_mul]
      change (j.app V).hom (AbLaw.cst f V ρ) * _ = _
      rw [app_cst H.w]
    have h1 : z.1 ∈ XK.basicOpen ((j.app V).hom b) := by
      rw [e', Scheme.basicOpen_mul]
      exact ⟨hc _ hρ _ hzV, hz'⟩
    rw [hb, Scheme.basicOpen_mul] at h1
    exact hσW h1.2

theorem near_zero : ∀ (C : Type) [Field C] [IsAlgClosed C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    [Algebra R C] [IsFractionRing R C] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ l : Pic (pullback A.hom (spMap (algebraMap R C))),
      ∃ V : A.left.Opens, (∃ y ∈ V, A.hom y = IsLocalRing.closedPoint R) ∧
        pull (pullback.fst A.hom (spMap (algebraMap R C)) ⁻¹ᵁ V).ι l = 0 := by
  intro C _ _ R _ _ _ _ _ _ A _ hA l
  have := hA.smooth
  have := hA.geomConnected
  have := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ A
  obtain ⟨x, hx⟩ := A.hom.surjective (IsLocalRing.closedPoint R)
  exact exists_open_pull_eq_zero (IsPullback.of_hasPullback A.hom (spMap (algebraMap R C))) hx l

end GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.NearZero
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PicardGenericTrivialNearSpecialStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.picard_generic_trivial_near_special : ∀ (C : Type) [Field C] [IsAlgClosed C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    [Algebra R C] [IsFractionRing R C] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ l : Pic (pullback A.hom (spMap (algebraMap R C))),
      ∃ V : A.left.Opens, (∃ y ∈ V, A.hom y = IsLocalRing.closedPoint R) ∧
        pull (pullback.fst A.hom (spMap (algebraMap R C)) ⁻¹ᵁ V).ι l = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.NearZero.near_zero | exact GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.NearZero.near_zero | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.NearZero.near_zero <;> assumption)
end
end

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.SymB

theorem pic_inj {C : Type} [Field C] [IsAlgClosed C] {R : Type} [CommRing R] [IsDomain R] [ValuationRing R]
    [Ring.DimensionLEOne R] [Algebra R C] [IsFractionRing R C] {X XK : Scheme.{0}} {f : X ⟶ Sp R} {j : XK ⟶ X}
    {fK : XK ⟶ Sp C} (H : IsPullback j fK f (spMap (algebraMap R C))) (h₁ : Smooth f) (h₂ : QuasiCompact f)
    (h₃ : GeometricallyIntegral f) (q : Pic X) (h : pull j q = 0) : q = 0 := by
  obtain ⟨M, hM, rfl⟩ := cls_surj q
  exact (cls_eq_zero_iff hM).2 (GlobalTheory.ValGenExtend.triv_of_triv_generic R C X XK f j fK H h₁ h₂ h₃ M hM
    ((cls_eq_zero_iff (pull_isLB hM j)).1 h))

theorem pull_sq_lam {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (s : S' ⟶ S) (p : Pic A.left) :
    pull (sqToBase A s) (lam p (fst A A) (snd A A)) =
      lam (pull (pullback.fst A.hom s) p) (fst _ _) (snd _ _) := by
  have h := isGrpPullback_pullback A s
  rw [sqToBase, pull_lam, lift_fst, lift_snd, lam_pull_of_isGrpPullback h]
  rfl

theorem sq_fst {S S' : Scheme.{0}} (A : Over S) (s : S' ⟶ S) : sqToBase A s ≫ (fst A A).left =
    (fst ((Over.pullback s).obj A) ((Over.pullback s).obj A)).left ≫ pullback.fst A.hom s :=
  congrArg (fun z ↦ z.left) (lift_fst (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (fst _ _)) (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (snd _ _)))

theorem sq_snd {S S' : Scheme.{0}} (A : Over S) (s : S' ⟶ S) : sqToBase A s ≫ (snd A A).left =
    (snd ((Over.pullback s).obj A) ((Over.pullback s).obj A)).left ≫ pullback.fst A.hom s :=
  congrArg (fun z ↦ z.left) (lift_snd (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (fst _ _)) (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (snd _ _)))

theorem isPullback_sq {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (s : S' ⟶ S) :
    IsPullback (sqToBase A s) ((Over.pullback s).obj A ⊗ (Over.pullback s).obj A).hom (A ⊗ A).hom s :=
  have hg := isGrpPullback_pullback A s
  isPullback_prod hg.1 hg.1 (sq_fst A s) (sq_snd A s)

theorem inv_pull {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (s : S' ⟶ S) :
    pullback.fst A.hom s ≫ (GrpObj.inv : A ⟶ A).left =
      (GrpObj.inv : (Over.pullback s).obj A ⟶ (Over.pullback s).obj A).left ≫ pullback.fst A.hom s := by
  have h := isGrpPullback_pullback A s
  have e := map_inv (pushHom h ((Over.pullback s).obj A)) (𝟙 _)
  have e' := congrArg (fun q ↦ q.left) e
  simpa [pushHom, Hom.inv_def, pushPt] using e'.symm

abbrev jj {S S' : Scheme.{0}} (A : Over S) (s : S' ⟶ S) : ((Over.pullback s).obj A).left ⟶ A.left := pullback.fst A.hom s

theorem transl_id {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (s : S' ⟶ S) (hS : ∀ c : Pic S', c = 0)
    (c : Pic (A ⊗ A).left) (l : Pic ((Over.pullback s).obj A).left)
    (h : pull (sqToBase A s) c = lam l (fst _ _) (snd _ _)) (d : 𝟙_ (Over S) ⟶ A) :
    ∃ τ : ((Over.pullback s).obj A).left ⟶ ((Over.pullback s).obj A).left,
      τ ≫ jj A s = jj A s ≫ (GlobalTheory.PolTranslate.transl d).left ∧
      l = pull τ l - pull (jj A s) (pull (lift (𝟙 A) (toUnit A ≫ d)).left c) := by
  have hg := isGrpPullback_pullback A s
  let B := (Over.pullback s).obj A
  let j : B.left ⟶ A.left := pullback.fst A.hom s
  have sq : (s ≫ d.left) ≫ A.hom = 𝟙 S' ≫ s := by
    have := Over.w d
    simp only [Category.assoc, Category.id_comp]
    rw [show d.left ≫ A.hom = (𝟙_ (Over S)).hom from this]
    exact Category.comp_id s
  let u : S' ⟶ B.left := hg.1.lift (s ≫ d.left) (𝟙 S') sq
  have hu₂ : u ≫ B.hom = 𝟙 S' := hg.1.lift_snd _ _ sq
  let t : B ⟶ B := Over.homMk (B.hom ≫ u) (by rw [Category.assoc, hu₂, Category.comp_id])
  have ht : t.left ≫ j = j ≫ (toUnit A ≫ d).left := by
    have e : (toUnit A ≫ d).left = A.hom ≫ d.left := rfl
    have e₀ : t.left = B.hom ≫ u := rfl
    have e₁ : u ≫ j = s ≫ d.left := hg.1.lift_fst _ _ sq
    rw [e, e₀, Category.assoc, e₁, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ d.left) (hg.1.w).symm
  let x₀ : Over.mk (B.hom ≫ s) ⟶ A := Over.homMk j hg.1.w
  let y₀ : Over.mk (B.hom ≫ s) ⟶ A := Over.homMk (j ≫ (toUnit A ≫ d).left) (by
    rw [Category.assoc, Over.w]; exact hg.1.w)
  have hτ : (𝟙 B * t).left ≫ j = j ≫ (GlobalTheory.PolTranslate.transl d).left := by
    have e := hg.2 B (𝟙 B) t x₀ y₀ (by simp [x₀, j]) (by simp only [y₀, Over.homMk_left]; exact ht.symm)
    rw [← e]
    have : x₀ * y₀ = x₀ ≫ GlobalTheory.PolTranslate.transl d := by
      rw [GlobalTheory.PolTranslate.transl, MonObj.comp_mul, Category.comp_id]
      congr 1
    rw [this]
    rfl
  refine ⟨(𝟙 B * t).left, hτ, ?_⟩
  have hlift : (lift (𝟙 B) t).left ≫ sqToBase A s = j ≫ (lift (𝟙 A) (toUnit A ≫ d)).left := by
    have a₁ : (lift (𝟙 B) t).left ≫ (fst B B).left = 𝟙 _ := congrArg (fun q ↦ q.left) (lift_fst (𝟙 B) t)
    have a₂ : (lift (𝟙 B) t).left ≫ (snd B B).left = t.left := congrArg (fun q ↦ q.left) (lift_snd (𝟙 B) t)
    have b₁ : (lift (𝟙 A) (toUnit A ≫ d)).left ≫ (fst A A).left = 𝟙 _ :=
      congrArg (fun q ↦ q.left) (lift_fst (𝟙 A) (toUnit A ≫ d))
    have b₂ : (lift (𝟙 A) (toUnit A ≫ d)).left ≫ (snd A A).left = (toUnit A ≫ d).left :=
      congrArg (fun q ↦ q.left) (lift_snd (𝟙 A) (toUnit A ≫ d))
    refine pullback.hom_ext ?_ ?_
    · change _ ≫ (fst A A).left = _ ≫ (fst A A).left
      rw [Category.assoc, Category.assoc, b₁, sq_fst, ← Category.assoc, a₁]
      simp [j]
    · change _ ≫ (snd A A).left = _ ≫ (snd A A).left
      rw [Category.assoc, Category.assoc, b₂, sq_snd, ← Category.assoc, a₂]
      exact ht
  have h₀ : ∀ u : S' ⟶ B.left, pull (B.hom ≫ u) l = 0 := fun u ↦ by
    rw [pull_comp, hS (pull u l), map_zero]
  have e₁ : pull t.left l = 0 := h₀ u
  have e₂ : pull (1 : B ⟶ B).left l = 0 := by
    have : (1 : B ⟶ B).left = B.hom ≫ (η[B]).left := by rw [Hom.one_def]; rfl
    rw [this]; exact h₀ _
  have e₃ : pull (jj A s) (pull (lift (𝟙 A) (toUnit A ≫ d)).left c) = lam l (𝟙 B) t := by
    rw [← pull_comp]
    have : jj A s ≫ (lift (𝟙 A) (toUnit A ≫ d)).left = (lift (𝟙 B) t).left ≫ sqToBase A s := hlift.symm
    rw [this, pull_comp, h, pull_lam, lift_fst, lift_snd]
  rw [e₃, lam, e₁, e₂, Over.id_left, pull_id]
  abel

theorem near : ∀ (C : Type) [Field C] [IsAlgClosed C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    [Algebra R C] [IsFractionRing R C] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (c : Pic (A ⊗ A).left)
    (l : Pic ((Over.pullback (spMap (algebraMap R C))).obj A).left),
    pull (sqToBase A (spMap (algebraMap R C))) c = lam l (fst _ _) (snd _ _) →
    ∀ y : A.left, IsClosed {y} → A.hom y = IsLocalRing.closedPoint R →
      ∃ V : A.left.Opens, y ∈ V ∧ pull (jj A (spMap (algebraMap R C)) ⁻¹ᵁ V).ι l = 0 := by
  intro C _ _ R _ _ _ _ _ _ A _ hA c l h y hy hyc
  obtain ⟨hH, hk⟩ := GlobalTheory.T.henselian_alg_closed_residue C R
  haveI := hA.comm
  have hs₀ := hA.smooth
  obtain ⟨V₀, hV₀, e₀⟩ := GlobalTheory.T.picard_generic_trivial_near_special C R A hA l
  obtain ⟨b₀, hb₀⟩ := (GlobalTheory.T.section_through_closed_point R A hs₀).2 V₀ hV₀
  obtain ⟨b, hb⟩ := (GlobalTheory.T.section_through_closed_point R A hs₀).1 y hy hyc
  let d : 𝟙_ (Over (Sp R)) ⟶ A := b⁻¹ * b₀
  obtain ⟨τ, hτ, hl⟩ := transl_id A (spMap (algebraMap R C)) (fun c ↦ GlobalTheory.ThetaExtend.pic_local c) c l h d
  have hbd : b ≫ GlobalTheory.PolTranslate.transl d = b₀ := by
    rw [GlobalTheory.PolTranslate.transl, MonObj.comp_mul, Category.comp_id, ← Category.assoc,
      toUnit_unique (b ≫ toUnit A) (𝟙 _), Category.id_comp, mul_inv_cancel_left]
  obtain ⟨V₂, hy₂, e₂⟩ := exists_pull_eq_zero (pull (lift (𝟙 A) (toUnit A ≫ d)).left c) y
  refine ⟨(GlobalTheory.PolTranslate.transl d).left ⁻¹ᵁ V₀ ⊓ V₂, ⟨?_, hy₂⟩, ?_⟩
  · show (GlobalTheory.PolTranslate.transl d).left y ∈ V₀
    have e : (GlobalTheory.PolTranslate.transl d).left (b.left (IsLocalRing.closedPoint R)) =
        (b ≫ GlobalTheory.PolTranslate.transl d).left (IsLocalRing.closedPoint R) := by
      rw [Over.comp_left]; rfl
    rw [← hb, e, hbd]
    exact hb₀
  · set W := jj A (spMap (algebraMap R C)) ⁻¹ᵁ ((GlobalTheory.PolTranslate.transl d).left ⁻¹ᵁ V₀ ⊓ V₂) with hW
    have t₁ : pull W.ι (pull τ l) = 0 := by
      rw [← pull_comp]
      refine pull_eq_zero_of_mem (jj A (spMap (algebraMap R C)) ⁻¹ᵁ V₀) (W.ι ≫ τ) (fun z ↦ ?_) e₀
      show jj A (spMap (algebraMap R C)) ((W.ι ≫ τ) z) ∈ V₀
      rw [← Scheme.Hom.comp_apply, Category.assoc, hτ, ← Category.assoc, Scheme.Hom.comp_apply]
      exact (show _ ∈ (GlobalTheory.PolTranslate.transl d).left ⁻¹ᵁ V₀ ⊓ V₂ from z.2).1
    have t₂ : pull W.ι (pull (jj A (spMap (algebraMap R C))) (pull (lift (𝟙 A) (toUnit A ≫ d)).left c)) = 0 := by
      rw [← pull_comp]
      exact pull_eq_zero_of_mem V₂ (W.ι ≫ jj A (spMap (algebraMap R C)))
        (fun z ↦ (show _ ∈ (GlobalTheory.PolTranslate.transl d).left ⁻¹ᵁ V₀ ⊓ V₂ from z.2).2) e₂
    calc pull W.ι l = pull W.ι (pull τ l - pull (jj A (spMap (algebraMap R C)))
          (pull (lift (𝟙 A) (toUnit A ≫ d)).left c)) := congrArg _ hl
      _ = 0 := by rw [map_sub, t₁, t₂, sub_zero]

theorem extend : ∀ (C : Type) [Field C] [IsAlgClosed C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    [Algebra R C] [IsFractionRing R C] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ l : Pic ((Over.pullback (spMap (algebraMap R C))).obj A).left,
    (∀ y : A.left, IsClosed {y} → A.hom y = IsLocalRing.closedPoint R →
      ∃ V : A.left.Opens, y ∈ V ∧ pull (jj A (spMap (algebraMap R C)) ⁻¹ᵁ V).ι l = 0) →
    ∃ p : Pic A.left, pull (jj A (spMap (algebraMap R C))) p = l := by
  intro C _ _ R _ _ _ _ _ _ A _ hA l hn
  have hp₀ := hA.proper
  have hio := GlobalTheory.T.generic_point_open_immersion C R
  let j := jj A (spMap (algebraMap R C))
  have hjo : IsOpenImmersion j := by
    show IsOpenImmersion (pullback.fst A.hom (spMap (algebraMap R C)))
    infer_instance
  let U₀ : A.left.Opens := j.opensRange
  let Q : A.left.Opens → Prop := fun W ↦ IsCompact (W : Set A.left) ∧
    ∃ (r : ((Over.pullback (spMap (algebraMap R C))).obj A).left ⟶ W.toScheme) (p : Pic W.toScheme), r ≫ W.ι = j ∧ pull r p = l
  have hcA : CompactSpace A.left := by
    exact QuasiCompact.compactSpace_of_compactSpace A.hom
  have hcK : CompactSpace ((Over.pullback (spMap (algebraMap R C))).obj A).left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd A.hom (spMap (algebraMap R C)))
  have hqs : QuasiSeparatedSpace A.left := quasiSeparatedSpace_of_quasiSeparated A.hom
  have base : Q U₀ := by
    refine ⟨?_, j.isoOpensRange.hom, pull j.isoOpensRange.inv l, by simp [U₀], ?_⟩
    · have : (U₀ : Set A.left) = Set.range j := Scheme.Hom.coe_opensRange j
      rw [this]
      exact isCompact_range j.continuous
    · rw [← pull_comp, Iso.hom_inv_id, pull_id]
  have step : ∀ (W V : A.left.Opens), Q W → IsCompact (V : Set A.left) → pull (j ⁻¹ᵁ V).ι l = 0 → Q (W ⊔ V) := by
    rintro W V ⟨hW, r, p, hr, hp⟩ hV hl
    have hz : pull (A.left.homOfLE (inf_le_left : W ⊓ V ≤ W)) p = 0 := by
      refine GlobalTheory.T.picard_generic_fibre_injective C R A hA (W ⊓ V) ?_ _ ?_
      · exact QuasiSeparatedSpace.inter_isCompact _ _ W.isOpen hW V.isOpen hV
      · have e : (pullback.fst A.hom (spMap (algebraMap R C)) ∣_ (W ⊓ V)) ≫ A.left.homOfLE (inf_le_left : W ⊓ V ≤ W) =
            (j ⁻¹ᵁ (W ⊓ V)).ι ≫ r := by
          rw [← cancel_mono W.ι, Category.assoc, Category.assoc, hr, Scheme.homOfLE_ι]
          exact morphismRestrict_ι _ _
        rw [← pull_comp, e, pull_comp, hp]
        exact pull_eq_zero_of_mem (j ⁻¹ᵁ V) (j ⁻¹ᵁ (W ⊓ V)).ι (fun z ↦ (show _ ∈ W ⊓ V from z.2).2) hl
    obtain ⟨q, hq⟩ := GlobalTheory.T.picard_mayer_vietoris_extend A.left W V p hz
    refine ⟨hW.union hV, r ≫ A.left.homOfLE le_sup_left, q, by simp [hr], ?_⟩
    rw [pull_comp, hq, hp]
  have hN : ∀ z : A.left, ∃ N : A.left.Opens, z ∈ N ∧ ∀ W, Q W → Q (W ⊔ N) := fun z ↦ by
    obtain ⟨y, hyz, hy⟩ := (isClosed_closure (s := {z})).exists_closed_singleton ⟨z, subset_closure rfl⟩
    have hyc : A.hom y = IsLocalRing.closedPoint R := by
      have h₁ := A.hom.isClosedMap _ hy
      rw [Set.image_singleton] at h₁
      have h₂ := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).1 h₁
      exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal h₂)
    obtain ⟨V, hyV, hV⟩ := hn y hy hyc
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUV⟩ := A.left.isBasis_affineOpens.exists_subset_of_mem_open hyV V.isOpen
    replace hU : IsAffineOpen U := hU
    refine ⟨U, (specializes_iff_mem_closure.2 hyz).mem_open U.isOpen hyU, fun W hW ↦ step W U hW hU.isCompact ?_⟩
    exact pull_eq_zero_of_mem (j ⁻¹ᵁ V) (j ⁻¹ᵁ U).ι (fun z ↦ hUV z.2) hV
  choose N hz hN using hN
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover (fun z ↦ (N z : Set A.left)) (fun z ↦ (N z).isOpen.mem_nhds (hz z))
  have key : ∀ t : Finset A.left, Q (U₀ ⊔ t.sup N) := fun t ↦ by
    classical
    induction t using Finset.induction_on with
    | empty => simpa using base
    | insert a s _ ih =>
      have := hN a _ ih
      rwa [Finset.sup_insert, sup_comm (N a), ← sup_assoc]
  have htop : U₀ ⊔ t.sup N = ⊤ := by
    refine top_le_iff.1 fun z _ ↦ ?_
    have hz' : z ∈ ⋃ x ∈ t, (N x : Set A.left) := by rw [ht]; trivial
    obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.1 hz'
    exact Or.inr (Finset.le_sup (f := N) hx hzx)
  have hQ := key t
  rw [htop] at hQ
  obtain ⟨-, r, p, hr, hp⟩ := hQ
  refine ⟨pull A.left.topIso.inv p, ?_⟩
  have e : j ≫ A.left.topIso.inv = r := by
    rw [← hr, Category.assoc]
    have : (⊤ : A.left.Opens).ι = A.left.topIso.hom := rfl
    rw [this, Iso.hom_inv_id, Category.comp_id]
  rw [← pull_comp]
  exact (congrArg (fun q ↦ pull q p) e).trans hp

theorem relAmple_of_cls {K : Type} [CommRing K] (B : Over (Sp K)) {M N : LB B.left} (hM : M.IsLB) (hN : N.IsLB)
    (e : cls M hM = cls N hN) (h : Out.RelAmple B N) : Out.RelAmple B M := by
  obtain ⟨w, hw⟩ := (cls_eq_iff hM (pull_isLB hN (𝟙 _))).1 (e.trans (by rw [cls_pull hN, pull_id]))
  exact relAmple_pull (IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩) hN hM
    ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ ↦ trivial) h

theorem symmetricBundle (hD : GlobalTheory.Published.DualAbelianScheme) (hC : GlobalTheory.Published.CubeTheorem) : SymmetricBundleSt := by
  intro C _ _ v R _ _ hv A _ hA c hc
  obtain ⟨_, _, _, _⟩ := GlobalTheory.T.valuation_integers_rank_one C v R hv
  obtain ⟨hH, hk⟩ := GlobalTheory.T.henselian_alg_closed_residue C R
  haveI := hA.comm
  have hs₀ := hA.smooth
  have hp₀ := hA.proper
  have hc₀ := hA.geomConnected
  have hg := isGrpPullback_pullback A (spMap (algebraMap R C))
  have hB := PolPull.isAbelianScheme_of_isGrpPullback hA hg
  obtain ⟨L₀, hL₀, ha₀, hk₀, e₀⟩ := hc.2.2 C (spMap (algebraMap R C))
  obtain ⟨L', hL', -, hs', ha', -, hl'⟩ := RiemannExists.exists_sym_translate C _ hB L₀ hL₀ ha₀ hk₀
  have eK : pull (sqToBase A (spMap (algebraMap R C))) c = lam (cls L' hL') (fst _ _) (snd _ _) := e₀.trans hl'.symm
  obtain ⟨p, hp⟩ := extend C R A hA (cls L' hL') (near C R A hA c (cls L' hL') eK)
  obtain ⟨L, hL, rfl⟩ := cls_surj p

  have s₂ : Smooth (A ⊗ A).hom := by
    change Smooth (pullback.fst A.hom A.hom ≫ A.hom); infer_instance
  have p₂ : IsProper (A ⊗ A).hom := by
    change IsProper (pullback.fst A.hom A.hom ≫ A.hom); infer_instance
  have c₂ : GeometricallyConnected (A ⊗ A).hom := by
    change GeometricallyConnected (pullback.fst A.hom A.hom ≫ A.hom)
    exact GeometricallyConnected.comp _ _
  have gi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
  have hsq := isPullback_sq A (spMap (algebraMap R C))
  have hlam : lam (cls L hL) (fst A A) (snd A A) = c := by
    rw [← sub_eq_zero]
    refine pic_inj hsq s₂ inferInstance (gi _ _ _ s₂ c₂) _ ?_
    rw [map_sub, pull_sq_lam, hp, eK, sub_self]
  have hsym : Out.Sym A L := by
    refine GlobalTheory.RigSymSubring.sym_of_cls hL ?_
    rw [← sub_eq_zero]
    refine pic_inj hg.1 hs₀ inferInstance (gi _ _ _ hs₀ hc₀) _ ?_
    have e := inv_pull A (spMap (algebraMap R C))
    rw [map_sub, ← pull_comp, e, pull_comp, hp, GlobalTheory.RigSymSubring.cls_of_sym hL' hs', sub_self]
  obtain ⟨P, hP, ePc, hPd⟩ := GlobalTheory.AbDual.principalPol_selfDual hD hC _ A hA c hc
  have hkt : Out.KTriv A L := by
    refine GlobalTheory.ThetaExtend.kTriv_of_lam hL hP (ePc.trans hlam.symm) fun T x hx ↦ ?_
    have ev : ∀ {Y : Over (Sp R)} (a b : Y ⟶ A), evc hP a b = lam (cls L hL) a b := fun a b ↦ by
      rw [evc, ePc, ← hlam, pull_lam, lift_fst, lift_snd]
    refine hPd.eq_one x ((triv_ev_iff hP _ _).2 ?_)
    rw [ev, lam_comm, ← ev]
    exact (triv_ev_iff hP _ _).1 hx
  refine ⟨L, hL, (GlobalTheory.RigSymSubring.rigidified_iff hL).2 (GlobalTheory.ThetaExtend.pic_local _), hsym, ?_, hkt, hlam.symm⟩
  have hLaws : Out.Laws := GlobalTheory.firstFiveLaws.1
  refine GlobalTheory.FibreAmple.relAmple_of_fibres hLaws R C A hA L hL ?_ ?_
  · exact relAmple_of_cls _ (pull_isLB hL _) hL' ((cls_pull hL _ _).trans hp) ha'
  · obtain ⟨L₁, hL₁, a₁, k₁, e₁⟩ := hc.2.2 (IsLocalRing.ResidueField R) (spMap (IsLocalRing.residue R))
    have hB' := PolPull.isAbelianScheme_of_isGrpPullback hA (isGrpPullback_pullback A (spMap (IsLocalRing.residue R)))
    refine GlobalTheory.T.rel_ample_of_same_polarization _ _ hB' _ L₁ (pull_isLB hL _) hL₁ a₁ k₁ ?_
    rw [cls_pull hL, ← pull_sq_lam, hlam, e₁]

end GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.SymB
