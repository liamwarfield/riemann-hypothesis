module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomIffOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GroupSchemeMorphismDescends
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GroupSchemeMorphismDescends
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GrpFlatDesc

open GrpDense MorphismProperty

variable {Z U : Scheme.{0}}

theorem hom_ext_of_points (j : U ⟶ Z) [Flat j] [Surjective j] {X Y : Over Z} {f g : X ⟶ Y}
    (h : ∀ (T : Over U) (t : Over.mk (T.hom ≫ j) ⟶ X), t ≫ f = t ≫ g) : f = g := by
  have := Flat.epi_of_flat_of_surjective (pullback.fst X.hom j)
  apply Over.OverMorphism.ext
  rw [← cancel_epi (pullback.fst X.hom j)]
  exact congrArg (fun z => z.left) (h (Over.mk (pullback.snd X.hom j))
    (Over.homMk (pullback.fst X.hom j) (by simpa using pullback.condition)))

set_option backward.isDefEq.respectTransparency.types false in
theorem isProper_of_isPullback {A G : Scheme.{0}} {φ : A ⟶ G} {f : A ⟶ U} {g : G ⟶ Z} {j : U ⟶ Z}
    [Flat j] [Surjective j] [QuasiCompact j] (h : IsPullback φ f g j) [IsProper f] : IsProper g := by
  have hj : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) j :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have h₁ : UniversallyClosed g :=
    of_isPullback_of_descendsAlong (P := @UniversallyClosed) h.flip hj inferInstance
  have h₂ : LocallyOfFiniteType g :=
    of_isPullback_of_descendsAlong (P := @LocallyOfFiniteType) h.flip hj inferInstance
  have : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}).IsStableUnderBaseChange :=
    @IsStableUnderBaseChange.inf _ _ _ _ (@IsStableUnderBaseChange.inf _ _ _ _ inferInstance inferInstance)
      inferInstance
  have : MorphismProperty.RespectsIso (C := Scheme.{0}) @UniversallyClosed := universallyClosed_respectsIso
  have h₃ : UniversallyClosed (pullback.diagonal g) :=
    of_isPullback_of_descendsAlong (P := MorphismProperty.diagonal @UniversallyClosed) h.flip hj
      (show UniversallyClosed (pullback.diagonal f) from inferInstance)
  have h₄ : IsSeparated g :=
    ⟨IsClosedImmersion.of_isPreimmersion _ (pullback.diagonal g).isClosedMap.isClosed_range⟩
  exact {}

theorem geometricallyConnected_of_isPullback {A G : Scheme.{0}} {φ : A ⟶ G} {f : A ⟶ U} {g : G ⟶ Z} {j : U ⟶ Z}
    [Surjective j] (h : IsPullback φ f g j) [hf : GeometricallyConnected f] : GeometricallyConnected g := by
  refine ⟨fun K _ y W a b hW => ?_⟩

  obtain ⟨p, -⟩ := (pullback.fst y j).surjective (Classical.arbitrary _)
  let r := (Limits.pullback y j).fromSpecResidueField p
  let s := r ≫ pullback.fst y j
  let t := r ≫ pullback.snd y j
  have hst : t ≫ j = s ≫ y := by simp only [t, s, Category.assoc, pullback.condition]
  have hs : Surjective s := inferInstance

  have hc : ConnectedSpace ↥(Limits.pullback f t) := pullback_of_geometrically hf.1 _ t

  have hout : IsPullback (pullback.fst f t ≫ φ) (pullback.snd f t) g (s ≫ y) := by
    rw [← hst]
    exact (IsPullback.of_hasPullback f t).paste_horiz h
  let q : Limits.pullback f t ⟶ W :=
    hW.lift (pullback.fst f t ≫ φ) (pullback.snd f t ≫ s) (by simpa only [Category.assoc] using hout.w)
  have hq : IsPullback q (pullback.snd f t) b s :=
    IsPullback.of_right (by rwa [hW.lift_fst]) (hW.lift_snd _ _ _) hW
  have hqs : Surjective q := MorphismProperty.of_isPullback hq.flip hs
  exact hqs.surj.connectedSpace q.continuous

theorem grpObj_of_flat_cover (j : U ⟶ Z) [Flat j] [Surjective j] (G : Over Z) (A : Over U) [GrpObj A]
    [IsCommMonObj A] (φ : A.left ⟶ G.left) (h : IsPullback φ A.hom G.hom j) (m : G ⊗ G ⟶ G) (i : G ⟶ G)
    (e : 𝟙_ (Over Z) ⟶ G)
    (hm : ∀ φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ)
    (hi : φ ≫ i.left = (ι[A]).left ≫ φ) (he : j ≫ e.left = (η[A]).left ≫ φ) :
    ∃ _ : GrpObj G, μ[G] = m ∧ η[G] = e ∧ ι[G] = i ∧ IsCommMonObj G ∧ IsGrpPullback A G j φ := by
  have hM := fun {T : Over U} => pushPt_mul h.w hm (T := T)
  have hI := fun {T : Over U} => pushPt_inv h.w hi (T := T)
  have hE := pushPt_one h.w he
  letI : MonObj G :=
    { one := e
      mul := m
      one_mul := GrpFlatDesc.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ snd _ _)
        obtain rfl : t = lift (toUnit _) (pushPt h.w x) :=
          CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) (by rw [lift_snd, hx])
        rw [lift_whiskerRight_assoc, hE, hM, _root_.one_mul, lift_leftUnitor_hom]
      mul_one := GrpFlatDesc.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ fst _ _)
        obtain rfl : t = lift (pushPt h.w x) (toUnit _) :=
          CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, hx]) (toUnit_unique _ _)
        rw [lift_whiskerLeft_assoc, hE, hM, _root_.mul_one, lift_rightUnitor_hom]
      mul_assoc := GrpFlatDesc.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ fst _ _ ≫ fst _ _)
        obtain ⟨y, hy⟩ := pushPt_surjective h T (t ≫ fst _ _ ≫ snd _ _)
        obtain ⟨z, hz⟩ := pushPt_surjective h T (t ≫ snd _ _)
        obtain rfl : t = lift (lift (pushPt h.w x) (pushPt h.w y)) (pushPt h.w z) := by
          ext <;> simp [hx, hy, hz]
        rw [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc, hM, hM, hM, hM,
          _root_.mul_assoc] }
  letI : GrpObj G :=
    { inv := i
      left_inv := GrpFlatDesc.hom_ext_of_points j fun T t => by
        obtain ⟨x, rfl⟩ := pushPt_surjective h T t
        change _ ≫ _ ≫ m = _ ≫ _ ≫ e
        rw [comp_lift_assoc, Category.comp_id, hI, hM, inv_mul_cancel, comp_toUnit_assoc, hE]
      right_inv := GrpFlatDesc.hom_ext_of_points j fun T t => by
        obtain ⟨x, rfl⟩ := pushPt_surjective h T t
        change _ ≫ _ ≫ m = _ ≫ _ ≫ e
        rw [comp_lift_assoc, Category.comp_id, hI, hM, mul_inv_cancel, comp_toUnit_assoc, hE] }
  refine ⟨inferInstance, rfl, rfl, rfl, ⟨GrpFlatDesc.hom_ext_of_points j fun T t => ?_⟩, h, fun T x y x₀ y₀ hx hy => ?_⟩
  · obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ fst _ _)
    obtain ⟨y, hy⟩ := pushPt_surjective h T (t ≫ snd _ _)
    obtain rfl : t = lift (pushPt h.w x) (pushPt h.w y) := by ext <;> simp [hx, hy]
    change _ ≫ _ ≫ m = _ ≫ m
    rw [lift_braiding_hom_assoc, hM, hM, _root_.mul_comm]
  · obtain rfl : x₀ = pushPt h.w x := Over.OverMorphism.ext hx
    obtain rfl : y₀ = pushPt h.w y := Over.OverMorphism.ext hy
    exact congrArg (fun z => z.left) (hM x y)

theorem isAbelianScheme_of_flat_cover (j : U ⟶ Z) [Flat j] [Surjective j] [QuasiCompact j] (G : Over Z) (A : Over U)
    [GrpObj A] (hA : IsAbelianScheme A) (φ : A.left ⟶ G.left) (h : IsPullback φ A.hom G.hom j) (m : G ⊗ G ⟶ G)
    (i : G ⟶ G) (e : 𝟙_ (Over Z) ⟶ G) (φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left) (h₂ : IsSquare φ φ₂)
    (hm : φ₂ ≫ m.left = (μ[A]).left ≫ φ)
    (hi : φ ≫ i.left = (ι[A]).left ≫ φ) (he : j ≫ e.left = (η[A]).left ≫ φ) :
    ∃ _ : GrpObj G, IsAbelianScheme G ∧ IsGrpPullback A G j φ := by
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  obtain ⟨_, -, -, -, hc, hp⟩ := grpObj_of_flat_cover j G A φ h m i e (fun ψ hψ => by
    obtain rfl : ψ = φ₂ := Over.tensorObj_ext _ _ (hψ.1.trans h₂.1.symm) (hψ.2.trans h₂.2.symm)
    exact hm) hi he
  have hj : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) j :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  exact ⟨inferInstance, ⟨hc, of_isPullback_of_descendsAlong (P := @Smooth) h.flip hj hA.smooth,
    isProper_of_isPullback h, geometricallyConnected_of_isPullback h⟩, hp⟩

end GlobalTheory.GrpFlatDesc

namespace GlobalTheory

theorem isAbelianScheme_descends_subfield :
    ∀ (k K : Type) [Field k] [Field K] (β : k →+* K) (B : Over (Sp K)) [GrpObj B] (B₀ : Over (Sp k)) (φ : B.left ⟶ B₀.left), IsAbelianScheme B → IsPullback φ B.hom B₀.hom (spMap β) → ∀ (m : B₀ ⊗ B₀ ⟶ B₀) (i : B₀ ⟶ B₀) (e : 𝟙_ (Over (Sp k)) ⟶ B₀) (φ₂ : (B ⊗ B).left ⟶ (B₀ ⊗ B₀).left), φ₂ ≫ (fst B₀ B₀).left = (fst B B).left ≫ φ → φ₂ ≫ (snd B₀ B₀).left = (snd B B).left ≫ φ → φ₂ ≫ m.left = (μ[B]).left ≫ φ → φ ≫ i.left = (ι[B]).left ≫ φ → spMap β ≫ e.left = (η[B]).left ≫ φ → ∃ _ : GrpObj B₀, IsAbelianScheme B₀ ∧ IsGrpPullback B B₀ (spMap β) φ := by
  intro k K _ _ β B _ B₀ φ hB h m i e φ₂ h₁ h₂ hm hi he
  have : Flat (spMap β) := by
    algebraize [β]
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (inferInstance : Module.Flat k K)
  have : Surjective (spMap β) := ⟨fun _ => ⟨default, Subsingleton.elim _ _⟩⟩
  exact GrpFlatDesc.isAbelianScheme_of_flat_cover (spMap β) B₀ B hB φ h m i e φ₂ ⟨h₁, h₂⟩ hm hi he

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GroupSchemeMorphismDescendsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.group_structure_descends_along_pullback : ∀ (k K : Type) [Field k] [Field K] (β : k →+* K) (B : Over (Sp K)) [GrpObj B] (B₀ : Over (Sp k)) (φ : B.left ⟶ B₀.left), IsAbelianScheme B → IsPullback φ B.hom B₀.hom (spMap β) → ∀ (m : B₀ ⊗ B₀ ⟶ B₀) (i : B₀ ⟶ B₀) (e : 𝟙_ (Over (Sp k)) ⟶ B₀) (φ₂ : (B ⊗ B).left ⟶ (B₀ ⊗ B₀).left), φ₂ ≫ (fst B₀ B₀).left = (fst B B).left ≫ φ → φ₂ ≫ (snd B₀ B₀).left = (snd B B).left ≫ φ → φ₂ ≫ m.left = (μ[B]).left ≫ φ → φ ≫ i.left = (ι[B]).left ≫ φ → spMap β ≫ e.left = (η[B]).left ≫ φ → ∃ _ : GrpObj B₀, IsAbelianScheme B₀ ∧ IsGrpPullback B B₀ (spMap β) φ := by
  first | exact @GlobalTheory.isAbelianScheme_descends_subfield | exact GlobalTheory.isAbelianScheme_descends_subfield | (intros; apply GlobalTheory.isAbelianScheme_descends_subfield <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomPairDescendsToFinite
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.HomPairDescent

open GlobalTheory.Spread

theorem id_pow_left_comm {S S' : Scheme.{0}} {j : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G j φ) (m : ℕ) :
    (𝟙 G' ^ m : G' ⟶ G').left ≫ φ = φ ≫ (𝟙 G ^ m : G ⟶ G).left := by
  have e₁ := congrArg (fun a => a.left) (map_pow (pushHom h G') (𝟙 G') m)
  have e₂ := congrArg (fun a => a.left) (MonObj.comp_pow (𝟙 G) m (pushHom h G' (𝟙 G')))
  rw [Category.comp_id] at e₂
  refine e₁.trans (e₂.symm.trans ?_)
  change (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem isGrpPullback_bcMap {k R S : Type} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (A : Over (Sp k)) [GrpObj A] (ρ : R →ₐ[k] S) :
    IsGrpPullback ((Over.pullback (spMap (algebraMap k S))).obj A) ((Over.pullback (spMap (algebraMap k R))).obj A)
      (spMap ρ.toRingHom) (bcMap A.hom ρ) :=
  (isGrpPullback_pullback A _).cancel
    ((isGrpPullback_pullback A _).congr (spMap_algHom_comp ρ).symm (bcMap_fst A.hom ρ).symm) (bcMap_snd A.hom ρ)

theorem exists_descend {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A B : Over (Sp K))
    [QuasiCompact A.hom] [QuasiSeparated A.hom] [LocallyOfFinitePresentation B.hom]
    (f : (Over.pullback (spMap (algebraMap K Ω))).obj A ⟶ (Over.pullback (spMap (algebraMap K Ω))).obj B) :
    ∃ s : Finset Ω, ∀ L : IntermediateField K Ω, (s : Set Ω) ⊆ L →
      ∃ g : (Over.pullback (spMap (algebraMap K L))).obj A ⟶ (Over.pullback (spMap (algebraMap K L))).obj B,
        bcMap A.hom L.val ≫ g.left = f.left ≫ bcMap B.hom L.val := by
  have hfw : f.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w f
  obtain ⟨R, ψ, ⟨s, rfl⟩, hψ, hψf⟩ := exists_fg_comp_eq A.hom B.hom (f.left ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ _) hfw)
  refine ⟨s, fun L hL => ?_⟩
  have hle : Algebra.adjoin K (s : Set Ω) ≤ L.toSubalgebra := Algebra.adjoin_le hL
  let ρ : Algebra.adjoin K (s : Set Ω) →ₐ[K] L := Subalgebra.inclusion hle
  have hw : (bcMap A.hom ρ ≫ ψ) ≫ B.hom = pullback.snd _ _ ≫ spMap (algebraMap K L) := by
    rw [Category.assoc, hψ, bcMap_fst_assoc, pullback.condition]
  let g₀ : pullback A.hom (spMap (algebraMap K L)) ⟶ pullback B.hom (spMap (algebraMap K L)) :=
    pullback.lift (bcMap A.hom ρ ≫ ψ) (pullback.snd _ _) hw
  let f₀ : pullback A.hom (spMap (algebraMap K Ω)) ⟶ pullback B.hom (spMap (algebraMap K Ω)) := f.left
  have hf₀ : f₀ ≫ pullback.snd _ _ = pullback.snd _ _ := hfw
  have hψ₀ : bcMap A.hom (Algebra.adjoin K (s : Set Ω)).val ≫ ψ = f₀ ≫ pullback.fst _ _ := hψf
  refine ⟨Over.homMk g₀ (pullback.lift_snd _ _ _), ?_⟩
  change bcMap A.hom L.val ≫ g₀ = f₀ ≫ bcMap B.hom L.val
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, bcMap_fst, pullback.lift_fst,
      bcMap_comp_of_eq_assoc A.hom ρ L.val (Algebra.adjoin K (s : Set Ω)).val fun _ ↦ rfl, hψ₀]
  · rw [Category.assoc, Category.assoc, bcMap_snd, pullback.lift_snd, bcMap_snd, reassoc_of% hf₀]

theorem comp_eq_pow_of_epi {S S' : Scheme.{0}} {j : S' ⟶ S} {G H : Over S} [GrpObj G] {G' H' : Over S'}
    [GrpObj G'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (h : IsGrpPullback G' G j φ) [Epi φ]
    {a' : G' ⟶ H'} {b' : H' ⟶ G'} {a : G ⟶ H} {b : H ⟶ G}
    (ha : φ ≫ a.left = a'.left ≫ ψ) (hb : ψ ≫ b.left = b'.left ≫ φ) (m : ℕ)
    (e : a' ≫ b' = 𝟙 _ ^ m) : a ≫ b = 𝟙 _ ^ m := by
  apply Over.OverMorphism.ext
  rw [← cancel_epi φ, ← id_pow_left_comm h m, ← e, Over.comp_left, Over.comp_left, reassoc_of% ha, hb,
    Category.assoc]

end GlobalTheory.HomPairDescent

namespace GlobalTheory

open HomPairDescent Spread

theorem homPair_descends_to_finite : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (A B : Over (Sp K)) [GrpObj A] [GrpObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ (i : (Over.pullback (spMap (algebraMap K Ω))).obj A ⟶ (Over.pullback (spMap (algebraMap K Ω))).obj B) (r : (Over.pullback (spMap (algebraMap K Ω))).obj B ⟶ (Over.pullback (spMap (algebraMap K Ω))).obj A), IsMonHom i → IsMonHom r → ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L) (i' : (Over.pullback (spMap (algebraMap K L))).obj A ⟶ (Over.pullback (spMap (algebraMap K L))).obj B) (r' : (Over.pullback (spMap (algebraMap K L))).obj B ⟶ (Over.pullback (spMap (algebraMap K L))).obj A), IsMonHom i' ∧ IsMonHom r' ∧ ∀ m : ℕ, (i ≫ r = 𝟙 _ ^ m → i' ≫ r' = 𝟙 _ ^ m) ∧ (r ≫ i = 𝟙 _ ^ m → r' ≫ i' = 𝟙 _ ^ m) := by
  classical
  intro K Ω _ _ _ _ A B _ _ hA hB i r hi hr
  have := hA.proper
  have := hB.proper
  have := hA.smooth
  have := hB.smooth
  obtain ⟨s, hs⟩ := exists_descend A B i
  obtain ⟨t, ht⟩ := exists_descend B A r
  let L : IntermediateField K Ω := IntermediateField.adjoin K ((s ∪ t : Finset Ω) : Set Ω)
  have hL : ((s ∪ t : Finset Ω) : Set Ω) ⊆ L := IntermediateField.subset_adjoin _ _
  obtain ⟨i', hi'⟩ := hs L ((Finset.coe_subset.2 Finset.subset_union_left).trans hL)
  obtain ⟨r', hr'⟩ := ht L ((Finset.coe_subset.2 Finset.subset_union_right).trans hL)
  have hfin : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have gA := isGrpPullback_bcMap A L.val
  have gB := isGrpPullback_bcMap B L.val
  obtain ⟨hepi, hmon⟩ := FieldBaseChange.epi_and_isMonHom_iff L Ω L.val.toRingHom
  have eA := (hepi _ _ _ _ _ gA.1).1
  have eB := (hepi _ _ _ _ _ gB.1).1
  exact ⟨L, hfin, i', r', (hmon _ _ _ _ _ _ i' i gA gB hi').1 hi, (hmon _ _ _ _ _ _ r' r gB gA hr').1 hr,
    fun m => ⟨comp_eq_pow_of_epi gA hi' hr' m, comp_eq_pow_of_epi gB hr' hi' m⟩⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusExtensionDescends
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusExtensionDescends
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ExtDescent

variable {S S₀ : Scheme.{0}} {f : S ⟶ S₀}

theorem hom_ext_of_points [Flat f] [Surjective f] {X Y : Over S₀} {a b : X ⟶ Y}
    (h : ∀ (T : Over S) (t : Over.mk (T.hom ≫ f) ⟶ X), t ≫ a = t ≫ b) : a = b := by
  apply Over.OverMorphism.ext
  haveI := Flat.epi_of_flat_of_surjective (pullback.fst X.hom f)
  rw [← cancel_epi (pullback.fst X.hom f)]
  exact congrArg (fun z => z.left) (h (Over.mk (pullback.snd X.hom f))
    (Over.homMk (pullback.fst X.hom f) (by simpa using pullback.condition)))

theorem isMonHom_of_grpPullback [Flat f] [Surjective f] {X Y : Over S} {X₀ Y₀ : Over S₀}
    [GrpObj X] [GrpObj Y] [GrpObj X₀] [GrpObj Y₀] {φ : X.left ⟶ X₀.left} {ψ : Y.left ⟶ Y₀.left}
    (hX : IsGrpPullback X X₀ f φ) (hY : IsGrpPullback Y Y₀ f ψ) (g : X ⟶ Y) (g₀ : X₀ ⟶ Y₀)
    (w : φ ≫ g₀.left = g.left ≫ ψ) [IsMonHom g] : IsMonHom g₀ := by
  have pa : ∀ {T : Over S} (x : T ⟶ X), pushHom hX T x ≫ g₀ = pushHom hY T (x ≫ g) := fun x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, w, Category.assoc])
  have hm : μ[X₀] ≫ g₀ = (g₀ ⊗ₘ g₀) ≫ μ := by
    refine hom_ext_of_points (f := f) fun T t => ?_
    obtain ⟨x, hx⟩ := GrpDense.pushPt_surjective hX.1 T (t ≫ fst _ _)
    obtain ⟨y, hy⟩ := GrpDense.pushPt_surjective hX.1 T (t ≫ snd _ _)
    obtain rfl : t = lift (pushHom hX T x) (pushHom hX T y) :=
      CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst]; exact hx.symm)
        (by rw [lift_snd]; exact hy.symm)
    rw [← Category.assoc, ← Hom.mul_def, ← map_mul, pa, lift_map_assoc, ← Hom.mul_def, pa, pa,
      ← map_mul, MonObj.mul_comp]
  refine ⟨?_, hm⟩
  have e : (η[X₀] ≫ g₀) * (η[X₀] ≫ g₀) = η[X₀] ≫ g₀ := by
    rw [Hom.mul_def, ← lift_map, Category.assoc, ← hm, ← Category.assoc]
    congr 1
    simpa [Hom.mul_def, Hom.one_def] using _root_.mul_one (1 : 𝟙_ (Over S₀) ⟶ X₀)
  have e' : η[X₀] ≫ g₀ = 1 := by simpa using e
  rw [e', Hom.one_def]; simp

theorem unit_comm {X : Over S} {X₀ : Over S₀} [GrpObj X] [GrpObj X₀] {φ : X.left ⟶ X₀.left}
    (h : IsGrpPullback X X₀ f φ) : f ≫ (η[X₀]).left = (η[X]).left ≫ φ := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S))))
  have e₁ : (1 : 𝟙_ (Over S) ⟶ X) = η[X] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine Eq.symm (e.trans ?_)
  show (toUnit _ ≫ η[X₀]).left = _
  simp

theorem fpqc_of_isPullback [Flat f] [Surjective f] [QuasiCompact f] {X X₀ : Scheme.{0}} {p : X ⟶ X₀}
    {s : X ⟶ S} {s₀ : X₀ ⟶ S₀} (h : IsPullback p s s₀ f) :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) p :=
  ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) h.flip ‹_›,
    MorphismProperty.of_isPullback (P := @Flat) h.flip ‹_›⟩,
    MorphismProperty.of_isPullback (P := @QuasiCompact) h.flip ‹_›⟩

theorem isPullback_of_baseChange [Flat f] [Surjective f] [QuasiCompact f] {T G B T₀ G₀ B₀ : Scheme.{0}}
    {i : T ⟶ G} {t : T ⟶ S} {q : G ⟶ B} {e : S ⟶ B} (H : IsPullback i t q e)
    {i₀ : T₀ ⟶ G₀} {t₀ : T₀ ⟶ S₀} {q₀ : G₀ ⟶ B₀} {e₀ : S₀ ⟶ B₀}
    {τ : T ⟶ T₀} {g : G ⟶ G₀} {φ : B ⟶ B₀} (hτ : IsPullback τ t t₀ f) (hγ : IsPullback g q q₀ φ)
    (hi : τ ≫ i₀ = i ≫ g) (he : f ≫ e₀ = e ≫ φ) : IsPullback i₀ t₀ q₀ e₀ := by
  haveI : Flat τ := (fpqc_of_isPullback hτ).1.2
  haveI : Surjective τ := (fpqc_of_isPullback hτ).1.1
  haveI := Flat.epi_of_flat_of_surjective τ
  have w : i₀ ≫ q₀ = t₀ ≫ e₀ := by
    rw [← cancel_epi τ, reassoc_of% hi, hγ.w, reassoc_of% H.w, reassoc_of% hτ.w, he]
  let c : T₀ ⟶ pullback q₀ e₀ := pullback.lift i₀ t₀ w
  have c₁ : c ≫ pullback.fst q₀ e₀ = i₀ := pullback.lift_fst _ _ _
  have c₂ : c ≫ pullback.snd q₀ e₀ = t₀ := pullback.lift_snd _ _ _
  have hp : IsPullback (τ ≫ c) t (pullback.snd q₀ e₀) f := by
    refine IsPullback.of_right ?_ (by rw [Category.assoc, c₂, hτ.w]) (IsPullback.of_hasPullback q₀ e₀)
    rw [Category.assoc, c₁, hi, he]
    exact H.paste_horiz hγ
  have hc : IsPullback τ (𝟙 T) c (τ ≫ c) := by
    refine IsPullback.of_bot ?_ (by simp) hp
    rw [c₂, Category.id_comp]
    exact hτ
  haveI : IsIso c := MorphismProperty.of_isPullback_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme.{0})
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hc.flip
    (fpqc_of_isPullback hp) (inferInstanceAs (IsIso (𝟙 T)))
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso c) c₁ c₂

end GlobalTheory.ExtDescent

namespace GlobalTheory

open ExtDescent

theorem splitTorus_extension_descends :
    ∀ (k K : Type) [Field k] [Field K] (β : k →+* K) (G B : Over (Sp K)) [GrpObj G] [GrpObj B] (G₀ B₀ : Over (Sp k)) [GrpObj G₀] [GrpObj B₀] (X : Type) [AddCommGroup X] (φG : G.left ⟶ G₀.left) (φ : B.left ⟶ B₀.left), IsGrpPullback G G₀ (spMap β) φG → IsGrpPullback B B₀ (spMap β) φ → ∀ (q : G ⟶ B) (i : splitTorus (Sp K) X ⟶ G) (q₀ : G₀ ⟶ B₀) (i₀ : splitTorus (Sp k) X ⟶ G₀), φG ≫ q₀.left = q.left ≫ φ → GlobalTheory.SplitTorus.bcMap (spMap β) X ≫ i₀.left = i.left ≫ φG → IsMonHom q → Flat q.left → Surjective q.left → QuasiCompact q.left → IsMonHom i → IsPullback i (toUnit _) q (η[B] : 𝟙_ _ ⟶ B) → IsMonHom q₀ ∧ Flat q₀.left ∧ Surjective q₀.left ∧ QuasiCompact q₀.left ∧ IsMonHom i₀ ∧ IsPullback i₀ (toUnit _) q₀ (η[B₀] : 𝟙_ _ ⟶ B₀) := by
  intro k K _ _ β G B _ _ G₀ B₀ _ _ X _ φG φ hG hB q i q₀ i₀ wq wi hq hfl hsu hqc hi H
  haveI h₁ : Flat (spMap β) := inferInstance
  haveI h₂ : Surjective (spMap β) := inferInstance
  haveI h₃ : QuasiCompact (spMap β) := inferInstance
  have hγ : IsPullback φG q.left q₀.left φ := by
    refine IsPullback.of_bot ?_ wq hB.1
    rw [Over.w, Over.w]
    exact hG.1
  have hφ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) φ :=
    fpqc_of_isPullback hB.1
  haveI := flat_descendsAlong_fpqc
  haveI := quasiCompact_descendsAlong_fpqc.{0}
  have hT := SplitTorus.isGrpPullback_bcMap (spMap β) X
  refine ⟨isMonHom_of_grpPullback hG hB q q₀ wq,
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat) hγ.flip hφ hfl,
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Surjective) hγ.flip hφ hsu,
    MorphismProperty.of_isPullback_of_descendsAlong (P := @QuasiCompact) hγ.flip hφ hqc,
    isMonHom_of_grpPullback hT hG i i₀ wi, ?_⟩
  have H' : IsPullback i.left (splitTorus (Sp K) X).hom q.left (η[B]).left :=
    H.map (Over.forget _)
  have H₀ := isPullback_of_baseChange H' hT.1 hγ wi (unit_comm hB)
  exact IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext H₀.w) H₀

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusExtensionDescendsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.splitTorus_extension_descends_alt : ∀ (k K : Type) [Field k] [Field K] (β : k →+* K) (G B : Over (Sp K)) [GrpObj G] [GrpObj B] (G₀ B₀ : Over (Sp k)) [GrpObj G₀] [GrpObj B₀] (X : Type) [AddCommGroup X] (φG : G.left ⟶ G₀.left) (φ : B.left ⟶ B₀.left), IsGrpPullback G G₀ (spMap β) φG → IsGrpPullback B B₀ (spMap β) φ → ∀ (q : G ⟶ B) (i : splitTorus (Sp K) X ⟶ G) (q₀ : G₀ ⟶ B₀) (i₀ : splitTorus (Sp k) X ⟶ G₀), φG ≫ q₀.left = q.left ≫ φ → GlobalTheory.SplitTorus.bcMap (spMap β) X ≫ i₀.left = i.left ≫ φG → IsMonHom q → Flat q.left → Surjective q.left → QuasiCompact q.left → IsMonHom i → IsPullback i (toUnit _) q (η[B] : 𝟙_ _ ⟶ B) → IsMonHom q₀ ∧ Flat q₀.left ∧ Surjective q₀.left ∧ QuasiCompact q₀.left ∧ IsMonHom i₀ ∧ IsPullback i₀ (toUnit _) q₀ (η[B₀] : 𝟙_ _ ⟶ B₀) := by
  first | exact @GlobalTheory.splitTorus_extension_descends | exact GlobalTheory.splitTorus_extension_descends | (intros; apply GlobalTheory.splitTorus_extension_descends <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MulqLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MulqLaws
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex

section Cube
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

theorem cub_rot (h : IsCub θ) (x y z : A) : θ x y z = θ z x y := by rw [h.s12, h.s01]

theorem cub_four (h : IsCub θ) (p q r s z : A) :
    θ (p * q) (r * s) z * θ p q z * θ r s z = θ (p * r) (q * s) z * θ p r z * θ q s z := by
  have a := h.coc (p * q) r s z
  have b := h.coc (p * r) q s z
  have c := h.coc q p r z
  rw [mul_right_comm p r q] at b
  rw [mul_comm q p, h.s01 q p, h.s01 q (p * r)] at c
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  replace c := congrArg Additive.ofMul c
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at a b c ⊢
  linear_combination (norm := abel) b - a + c

theorem cubN_mul_point (h : IsCub θ) (a : ℕ) (x y z : A) :
    cubN θ a 1 (x * y) z * θ x y z ^ a = cubN θ a 1 x z * cubN θ a 1 y z * θ (x ^ a) (y ^ a) z := by
  induction a with
  | zero => simp [cubN, h.face]
  | succ a ih =>
    have f := cub_four h (x ^ a) (y ^ a) x y z
    simp only [CubeBalance.cubN_succ, mul_pow, pow_succ]
    replace ih := congrArg Additive.ofMul ih
    replace f := congrArg Additive.ofMul f
    apply Additive.ofMul.injective
    simp only [ofMul_mul] at ih f ⊢
    linear_combination (norm := abel) ih + f

theorem mulq_succ (θ : A → A → A → U) (σ : A → U) (n : ℕ) (x : A) :
    mulq θ σ (n + 1) x = mulq θ σ n x * (cubN θ n 1 x x / dbl θ σ x ^ n) := by
  rw [mulq, Finset.prod_range_succ, mulq]

theorem mulq_add (h : IsCub θ) (σ : A → U) (m n : ℕ) (x : A) :
    mulq θ σ (m + n) x * dbl θ σ x ^ (m * n) =
      mulq θ σ m x * mulq θ σ n x * (cubN θ m 1 x (x ^ n) * cubN θ n 1 x x ^ m) := by
  induction m with
  | zero => simp [mulq, cubN]
  | succ m ih =>
    have c := CubeBalance.cubN_add h m n x x
    rw [h.s12] at c
    rw [Nat.add_right_comm, mulq_succ, mulq_succ, CubeBalance.cubN_succ]
    replace ih := congrArg Additive.ofMul ih
    replace c := congrArg Additive.ofMul c
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow] at ih c ⊢
    linear_combination (norm := module) ih + c

end Cube

namespace NumB
variable {O : Type} [CommRing O] (B : NumB O)

theorem θ_mul_inv_inv (x y : B.A) : B.θ (x * y) x⁻¹ y⁻¹ * B.θ x x⁻¹ y = B.θ y y⁻¹ x⁻¹ := by
  have a := B.cub.coc x y y⁻¹ x⁻¹
  rwa [mul_inv_cancel, B.cub.face₂, one_mul, B.cub.s12, B.cub.s12 x y] at a

theorem σ_mul_symm (x y : B.A) : B.σ (x * y) * B.θ (x * y) x⁻¹ y⁻¹ = B.σ x * B.σ y := by
  have a := B.θ_mul_inv_inv y x
  have b := B.σ_mul x y
  rw [mul_comm y x, B.cub.s12] at a
  rw [← a, ← mul_assoc] at b
  exact mul_right_cancel b

theorem dbl_mul (x y : B.A) :
    dbl B.θ B.σ (x * y) * (B.θ (x * y) x y * B.θ x x y * B.θ y x y) =
      dbl B.θ B.σ x * dbl B.θ B.σ y := by
  have c := B.cub.coc x y (x * y)⁻¹ (x * y)
  have d := B.cub.coc y y⁻¹ x⁻¹ (x * y)
  rw [show y * (x * y)⁻¹ = x⁻¹ by rw [mul_inv, mul_comm, inv_mul_cancel_right], cub_rot B.cub x y] at c
  rw [mul_inv_cancel, B.cub.face, mul_comm y⁻¹, ← mul_inv, B.cub.s01 y⁻¹, cub_rot B.cub x⁻¹ y⁻¹] at d
  have a := B.cub.compat x x⁻¹ x y
  have b := B.cub.compat y y⁻¹ x y
  rw [mul_inv_cancel, B.cub.face, B.cub.s01 x⁻¹ x y] at a
  rw [mul_inv_cancel, B.cub.face, B.cub.s12 y⁻¹ x y, B.cub.s01 y⁻¹ y x] at b
  have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
  have a := E a; have b := E b; have c := E c; have d := E d; have s := E (B.σ_mul_symm x y)
  apply Additive.ofMul.injective
  simp only [dbl, ofMul_mul, ofMul_div, ofMul_one] at a b c d s ⊢
  linear_combination (norm := abel) c - d - a - b - s

theorem dbl_pow (a : ℕ) (x : B.A) :
    dbl B.θ B.σ (x ^ a) * (cubN B.θ a 1 x (x ^ a) * cubN B.θ a 1 x x ^ a) =
      dbl B.θ B.σ x ^ (a ^ 2) * mulq B.θ B.σ a x ^ 2 := by
  induction a with
  | zero => simp [dbl, mulq, cubN, B.cub.face, B.σ_one]
  | succ a ih =>
    have d := B.dbl_mul (x ^ a) x
    rw [B.cub.s01 x (x ^ a), ← cub_rot B.cub (x ^ a) x] at d
    have n := B.cub.N_add a 1 x (x ^ a) x
    rw [B.cub.face, mul_one, one_mul, B.cub.s01 x (x ^ a)] at n
    rw [mulq_succ, CubeBalance.cubN_succ, CubeBalance.cubN_succ, pow_succ x]
    have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
    have ih := E ih; have d := E d; have n := E n
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow] at ih d n ⊢
    linear_combination (norm := module) ih + d + n

theorem mulq_mul (a b : ℕ) (x : B.A) :
    mulq B.θ B.σ (a * b) x = mulq B.θ B.σ a (x ^ b) * mulq B.θ B.σ b x ^ (a ^ 2) := by
  induction a with
  | zero => simp [mulq]
  | succ a ih =>
    have m := mulq_add B.cub B.σ (a * b) b x
    have c := CubeBalance.cubN_mul B.cub a b x (x ^ b)
    have d := B.dbl_pow b x
    rw [Nat.succ_mul, mulq_succ]
    have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
    have ih := E ih; have m := E m; have c := E c; have d := E d
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow] at ih m c d ⊢
    linear_combination (norm := module) ih + m + c + a • d

theorem mulq_mul_point (a : ℕ) (x y : B.A) :
    mulq B.θ B.σ a (x * y) = mulq B.θ B.σ a x * mulq B.θ B.σ a y *
      (cubN B.θ a 1 x (y ^ a) * cubN B.θ a 1 y x ^ a) := by
  induction a with
  | zero => simp [mulq, cubN]
  | succ a ih =>
    have d := B.dbl_mul x y
    have f := cubN_mul_point B.cub a x y (x * y)
    have n₁ := B.cub.N_add a 1 x x y
    have n₂ := B.cub.N_add a 1 y x y
    have n₃ := B.cub.N_add a 1 x (y ^ a) y
    rw [B.cub.face, mul_one, one_mul] at n₁ n₂ n₃
    rw [cub_rot B.cub x y] at f
    rw [← cub_rot B.cub (y ^ a) y x] at n₃
    have c₁ := B.cub.compat (x ^ a) (y ^ a) x y
    have c₂ := B.cub.coc (x ^ a) (y ^ a) y x
    rw [B.cub.s12 (x ^ a * y ^ a), B.cub.s12 (x ^ a) (y ^ a * y)] at c₂
    rw [mulq_succ, mulq_succ, mulq_succ, CubeBalance.cubN_succ, CubeBalance.cubN_succ, pow_succ y]
    have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
    have ih := E ih; have d := E d; have f := E f; have n₁ := E n₁; have n₂ := E n₂; have n₃ := E n₃
    have c₁ := E c₁; have c₂ := E c₂
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow] at ih d f n₁ n₂ n₃ c₁ c₂ ⊢
    linear_combination (norm := module) ih + f + n₁ + n₂ - n₃ - a • d - c₁ + c₂

theorem cubN_inv_inv (a : ℕ) (x : B.A) :
    cubN B.θ a 1 x⁻¹ x⁻¹ * B.θ x x⁻¹ x ^ a * (B.σ x * B.σ (x ^ a)) =
      cubN B.θ a 1 x x * B.θ x⁻¹ x x⁻¹ ^ a * B.σ (x ^ a * x) := by
  induction a with
  | zero => simp [cubN, B.σ_one]
  | succ a ih =>
    have s := B.σ_cub (x ^ a) x x
    have t := B.σ_cub x x x⁻¹
    have u := B.σ_inv x
    rw [inv_inv, mul_inv_cancel, mul_inv_cancel_right, B.σ_one, B.cub.s12 x⁻¹, B.cub.s12 x] at t
    rw [CubeBalance.cubN_succ, CubeBalance.cubN_succ, inv_pow, pow_succ x]
    have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
    have ih := E ih; have s := E s; have t := E t; have u := E u
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_one] at ih s t u ⊢
    linear_combination (norm := module) ih + s - t - u

theorem mulq_inv (a : ℕ) (x : B.A) :
    mulq B.θ B.σ a x⁻¹ * B.σ x ^ (a ^ 2) = mulq B.θ B.σ a x * B.σ (x ^ a) := by
  induction a with
  | zero => simp [mulq, B.σ_one]
  | succ a ih =>
    have g := B.cubN_inv_inv a x
    have u := B.σ_inv x
    rw [mulq_succ, mulq_succ, pow_succ x]
    have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
    have ih := E ih; have g := E g; have u := E u
    apply Additive.ofMul.injective
    simp only [dbl, inv_inv, ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at ih g u ⊢
    linear_combination (norm := module) ih + g + a • u

end NumB

theorem mulq_laws : ∀ (O : Type) [CommRing O] (B : NumB O) (a b : ℕ) (x y : B.A), mulq B.θ B.σ (a * b) x = mulq B.θ B.σ a (x ^ b) * mulq B.θ B.σ b x ^ (a ^ 2) ∧ mulq B.θ B.σ a (x * y) = mulq B.θ B.σ a x * mulq B.θ B.σ a y * (cubN B.θ a 1 x (y ^ a) * cubN B.θ a 1 y x ^ a) ∧ dbl B.θ B.σ (x ^ a) * (cubN B.θ a 1 x (x ^ a) * cubN B.θ a 1 x x ^ a) = dbl B.θ B.σ x ^ (a ^ 2) * mulq B.θ B.σ a x ^ 2 ∧ mulq B.θ B.σ a x⁻¹ * B.σ x ^ (a ^ 2) = mulq B.θ B.σ a x * B.σ (x ^ a) :=
  fun _ _ B a b x y => ⟨B.mulq_mul a b x, B.mulq_mul_point a x y, B.dbl_pow a x, B.mulq_inv a x⟩

end GlobalTheory.Ex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MulqLawsStatement
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mulq_dbl_cubN_relations : ∀ (O : Type) [CommRing O] (B : NumB O) (a b : ℕ) (x y : B.A), mulq B.θ B.σ (a * b) x = mulq B.θ B.σ a (x ^ b) * mulq B.θ B.σ b x ^ (a ^ 2) ∧ mulq B.θ B.σ a (x * y) = mulq B.θ B.σ a x * mulq B.θ B.σ a y * (cubN B.θ a 1 x (y ^ a) * cubN B.θ a 1 y x ^ a) ∧ dbl B.θ B.σ (x ^ a) * (cubN B.θ a 1 x (x ^ a) * cubN B.θ a 1 x x ^ a) = dbl B.θ B.σ x ^ (a ^ 2) * mulq B.θ B.σ a x ^ 2 ∧ mulq B.θ B.σ a x⁻¹ * B.σ x ^ (a ^ 2) = mulq B.θ B.σ a x * B.σ (x ^ a) := by
  first | exact @GlobalTheory.Ex.mulq_laws | exact GlobalTheory.Ex.mulq_laws | (intros; apply GlobalTheory.Ex.mulq_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTerms
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTerms
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
namespace GlobalTheory.Ex
namespace NumD
variable {O : Type} [CommRing O] (N : NumD O)

theorem Form.div_add_left {N : NumD O} {k : ℕ} (β : N.Form k) {j : ℕ} (hj : j ∣ k) (x y z : N.X) :
    β.be (x + y) z / j = β.be x z / j + β.be y z / j := by
  rw [β.symm, β.div_add hj, β.symm z, β.symm z]

theorem Form.div_add_nsmul {N : NumD O} {k : ℕ} (β : N.Form k) {j : ℕ} (hj : j ∣ k) (x y z : N.X) :
    β.be (x + j • y) z / j = β.be x z / j + β.be y z := by
  rcases eq_or_ne j 0 with rfl | h
  · obtain rfl : k = 0 := Nat.eq_zero_of_zero_dvd hj
    have h0 : β.be y z = 0 := by simpa using β.dvd y z
    simp [h0]
  · rw [β.div_add_left hj, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul,
      Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.2 h)]

theorem Form.div_nsmul {N : NumD O} {k : ℕ} (β : N.Form k) {j : ℕ} (hj : j ∣ k) (m : ℕ) (x y : N.X) :
    β.be x (m • y) / j = β.be x y / j * m := by
  induction m with
  | zero => simp
  | succ m ih => rw [succ_nsmul, β.div_add hj, ih]; push_cast; ring

theorem Form.exp_count {N : NumD O} {k : ℕ} (β : N.Form k) {m : ℕ} (hm : m ^ 2 ∣ k) (ho : Odd m) (y χ : N.X) :
    β.be (y + m • χ) (y + m • χ) / (2 * m ^ 2) =
      β.be y y / 2 - β.be y y / (m ^ 2 : ℕ) * ((m ^ 2 - 1) / 2 : ℕ) + β.be χ χ / 2 + β.be y χ / (m ^ 2 : ℕ) * m := by
  have hd : ∀ x z, (2 * (m : ℤ) ^ 2) ∣ β.be x z := fun x z =>
    (mul_dvd_mul_left 2 (by exact_mod_cast hm)).trans (β.dvd x z)
  obtain ⟨a, ha⟩ := hd y y
  obtain ⟨b, hb⟩ := hd y χ
  obtain ⟨c, hc⟩ := hd χ χ
  obtain ⟨t, ht⟩ := ho.pow (n := 2)
  have hm0 : (m : ℤ) ^ 2 ≠ 0 := pow_ne_zero _ (Int.natCast_ne_zero.2 ho.pos.ne')
  have h1 : (m ^ 2 - 1) / 2 = t := by omega
  have h2 : (m : ℤ) ^ 2 = 2 * t + 1 := by exact_mod_cast ht
  have e : β.be (y + m • χ) (y + m • χ) = 2 * m ^ 2 * (a + 2 * m * b + m ^ 2 * c) := by
    simp only [map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, β.symm χ y, ha, hb, hc]
    ring
  have d1 : ∀ x : ℤ, 2 * (m : ℤ) ^ 2 * x / 2 = m ^ 2 * x := fun x => by
    rw [mul_assoc, Int.mul_ediv_cancel_left _ two_ne_zero]
  have d2 : ∀ x : ℤ, 2 * (m : ℤ) ^ 2 * x / (m ^ 2 : ℕ) = 2 * x := fun x => by
    rw [Nat.cast_pow, mul_right_comm, Int.mul_ediv_cancel _ hm0]
  rw [e, h1, ha, hb, hc, d1, d1, d2, d2, Int.mul_ediv_cancel_left _ (mul_ne_zero two_ne_zero hm0)]
  linear_combination (-a) * h2

theorem twist_wQ {k : ℕ} (β : N.Form k) (u : Oˣ) {j : ℕ} (hj : j ∣ k) (p : N.QT j) :
    (N.twist β u).wQ (N.twQ β u hj p) =
      u ^ (β.be p.1.1.toAdd p.1.1.toAdd / 2 - β.be p.1.1.toAdd p.1.1.toAdd / j * ((j - 1) / 2 : ℕ)) * N.wQ p := by
  show N.ψ p.1.1.toAdd * u ^ (β.be p.1.1.toAdd p.1.1.toAdd / 2) * mulq N.θ N.σ j p.1.2.b /
      (p.1.2.s p.1.1.toAdd * u ^ (β.be p.1.1.toAdd p.1.1.toAdd / j) * cubN N.θ j 1 p.1.2.b p.1.2.b /
        dbl N.θ N.σ p.1.2.b ^ j) ^ ((j - 1) / 2) = _ * (N.ψ p.1.1.toAdd * mulq N.θ N.σ j p.1.2.b /
      (p.1.2.s p.1.1.toAdd * cubN N.θ j 1 p.1.2.b p.1.2.b / dbl N.θ N.σ p.1.2.b ^ j) ^ ((j - 1) / 2))
  rw [zpow_sub, zpow_mul, zpow_natCast, mul_right_comm (p.1.2.s _), mul_div_right_comm _ (u ^ _), mul_pow]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv]; abel

theorem twist_vt {k : ℕ} (β : N.Form k) (u : Oˣ) (g : N.Gt) (l : N.X → ℤ) (hl : ∀ a b, l (a + b) = l a + l b)
    (m : ℕ) (χ : N.X) :
    (N.twist β u).vt (N.twG β u g l hl ^ m) χ = (u ^ (β.be χ χ / 2 + l χ * m) : Oˣ) * N.vt (g ^ m) χ := by
  obtain ⟨h1, h2⟩ := N.twG_pow β u g l hl m
  show ((N.ψ χ * u ^ (β.be χ χ / 2) * (N.twG β u g l hl ^ m).s χ : Oˣ) : O) *
    N.th (N.c χ * (show N.A from (N.twG β u g l hl ^ m).b)) = _ * (((N.ψ χ * (g ^ m).s χ : Oˣ) : O) * N.th (N.c χ * (g ^ m).b))
  rw [h1, h2, ← mul_assoc (_ : O), ← Units.val_mul, zpow_add]
  congr 2
  apply Additive.ofMul.injective
  simp only [ofMul_mul]; abel

theorem twG_mul {k : ℕ} (β : N.Form k) (u : Oˣ) (g g' : N.Gt) (l l' : N.X → ℤ) (hl : ∀ a b, l (a + b) = l a + l b)
    (hl' : ∀ a b, l' (a + b) = l' a + l' b) :
    N.twG β u g l hl * N.twG β u g' l' hl' =
      N.twG β u (g * g') (fun z => l z + l' z) (fun a b => by rw [hl, hl']; ring) := by
  refine NumD.Gt.ext rfl (funext fun (z : N.X) => ?_)
  show g.s z * u ^ l z * (g'.s z * u ^ l' z) / N.θ (N.c z) g.b g'.b =
    g.s z * g'.s z / N.θ (N.c z) g.b g'.b * u ^ (l z + l' z)
  rw [zpow_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]; abel

theorem twG_congr {k : ℕ} (β : N.Form k) (u : Oˣ) (g : N.Gt) (l l' : N.X → ℤ) (hl : ∀ a b, l (a + b) = l a + l b)
    (hl' : ∀ a b, l' (a + b) = l' a + l' b) (h : ∀ z, l z = l' z) : N.twG β u g l hl = N.twG β u g l' hl' := by
  obtain rfl : l = l' := funext h
  rfl

theorem twG_inj {k : ℕ} (β : N.Form k) (u : Oˣ) (g g' : N.Gt) (l : N.X → ℤ) (hl : ∀ a b, l (a + b) = l a + l b)
    (h : N.twG β u g l hl = N.twG β u g' l hl) : g = g' :=
  NumD.Gt.ext (congrArg (fun x : (N.twist β u).Gt => x.b) h)
    (funext fun z => mul_right_cancel (congrArg (fun x : (N.twist β u).Gt => x.s z) h))

theorem twist_io {k : ℕ} (β : N.Form k) (u : Oˣ) (y : N.X) :
    (N.twist β u).io y = N.twG β u (N.io y) (fun z => β.be y z) (fun a b => map_add _ a b) :=
  NumD.Gt.ext rfl (funext fun (z : N.X) => N.twist_τ β u y z)

theorem twist_txT {k : ℕ} (β : N.Form k) (u : Oˣ) (m : ℕ) (hm : m ^ 2 ∣ k) (ho : Odd m) (p : N.QT (m ^ 2)) (χ : N.X) :
    (N.twist β u).txT m (N.twQ β u hm p) χ =
      (u ^ (β.be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2)) : Oˣ) * N.txT m p χ := by
  show (((N.twist β u).wQ (N.twQ β u hm p) / mulq N.θ N.σ m p.1.2.b : Oˣ) : O) *
    (N.twist β u).vt (N.twG β u p.1.2 _ (β.div_add hm p.1.1.toAdd) ^ m) χ =
      _ * (((N.wQ p / mulq N.θ N.σ m p.1.2.b : Oˣ) : O) * N.vt (p.1.2 ^ m) χ)
  rw [twist_wQ, twist_vt, β.exp_count hm ho, ← mul_assoc, ← mul_assoc, ← Units.val_mul, ← Units.val_mul]
  congr 2
  simp only [zpow_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]; abel

theorem twist_evT {k : ℕ} (β : N.Form k) (u : Oˣ) (m : ℕ) (hm : m ^ 2 ∣ k) (ho : Odd m) (p : N.QT (m ^ 2)) (χ : N.X)
    {j : ℕ} (hj : j ∣ k) (q : N.QT j) :
    (N.twist β u).evT m (N.twQ β u hm p) (N.twQ β u hj q).1.2 χ =
      (u ^ (β.be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2) +
        β.be q.1.1.toAdd (p.1.1.toAdd + m • χ) / j) : Oˣ) * N.evT m p q.1.2 χ := by
  show ((q.1.2.s p.1.1.toAdd * u ^ (β.be q.1.1.toAdd p.1.1.toAdd / j) * cubN N.θ (m ^ 2) 1 p.1.2.b q.1.2.b *
    (N.twist β u).wQ (N.twQ β u hm p) / mulq N.θ N.σ m (q.1.2.b * p.1.2.b) : Oˣ) : O) *
    (N.twist β u).vt ((N.twG β u q.1.2 _ (β.div_add hj q.1.1.toAdd) *
      N.twG β u p.1.2 _ (β.div_add hm p.1.1.toAdd)) ^ m) χ =
      _ * (((q.1.2.s p.1.1.toAdd * cubN N.θ (m ^ 2) 1 p.1.2.b q.1.2.b *
        N.wQ p / mulq N.θ N.σ m (q.1.2.b * p.1.2.b) : Oˣ) : O) * N.vt ((q.1.2 * p.1.2) ^ m) χ)
  rw [twG_mul, twist_wQ, twist_vt, β.exp_count hm ho, β.div_add hj, β.div_nsmul hj, ← mul_assoc (_ : O), ← mul_assoc (_ : O),
    ← Units.val_mul, ← Units.val_mul]
  congr 2
  simp only [add_mul, zpow_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]; abel

theorem twist_wp {k : ℕ} (β : N.Form k) (u : Oˣ) {j : ℕ} (hj : j ∣ k) (q q' : N.QT j) :
    (N.twist β u).wp (N.twQ β u hj q) (N.twQ β u hj q') = N.wp q q' := by
  show q.1.2.s q'.1.1.toAdd * u ^ (β.be q.1.1.toAdd q'.1.1.toAdd / j) * cubN N.θ j 1 q'.1.2.b q.1.2.b /
    (q'.1.2.s q.1.1.toAdd * u ^ (β.be q'.1.1.toAdd q.1.1.toAdd / j) * cubN N.θ j 1 q.1.2.b q'.1.2.b) =
    q.1.2.s q'.1.1.toAdd * cubN N.θ j 1 q'.1.2.b q.1.2.b / (q'.1.2.s q.1.1.toAdd * cubN N.θ j 1 q.1.2.b q'.1.2.b)
  rw [β.symm q'.1.1.toAdd]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]; abel

theorem twQ_mul {k : ℕ} (β : N.Form k) (u : Oˣ) {j : ℕ} (hj : j ∣ k) (q q' : N.QT j) :
    N.twQ β u hj (q * q') = N.twQ β u hj q * N.twQ β u hj q' := by
  refine Subtype.ext (Prod.ext rfl ?_)
  show N.twG β u (q.1.2 * q'.1.2) _ (β.div_add hj (q.1.1.toAdd + q'.1.1.toAdd)) =
    N.twG β u q.1.2 _ (β.div_add hj q.1.1.toAdd) * N.twG β u q'.1.2 _ (β.div_add hj q'.1.1.toAdd)
  rw [twG_mul]
  exact N.twG_congr β u _ _ _ _ _ fun z => β.div_add_left hj _ _ z

theorem twist_qEq {k : ℕ} (β : N.Form k) (u : Oˣ) {j : ℕ} (hj : j ∣ k) (q q' : N.QT j) :
    N.QEq q q' ↔ (N.twist β u).QEq (N.twQ β u hj q) (N.twQ β u hj q') := by
  refine exists_congr fun (z : N.X) => and_congr_right fun (h : q'.1.1.toAdd = q.1.1.toAdd + j • z) => ?_
  show _ ↔ N.twG β u q'.1.2 _ (β.div_add hj q'.1.1.toAdd) =
    N.twG β u q.1.2 _ (β.div_add hj q.1.1.toAdd) * (N.twist β u).io z
  rw [twist_io, twG_mul, ← N.twG_congr β u (q.1.2 * N.io z) (fun x => β.be q'.1.1.toAdd x / j)
    (fun x => β.be q.1.1.toAdd x / j + β.be z x) (β.div_add hj q'.1.1.toAdd) _
    fun x => by rw [h, β.div_add_nsmul hj]]
  exact ⟨fun e => by rw [e], N.twG_inj β u _ _ _ _⟩

end NumD

theorem twist_terms : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (k : ℕ) (β : N.Form k) (u : Oˣ) (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∀ (p : N.QT (m ^ 2)) (χ : N.X), (N.twist β u).txT m (N.twQ β u hm p) χ = (u ^ (β.be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2)) : Oˣ) * N.txT m p χ ∧ (∀ (j : ℕ) (hj : j ∣ k) (q : N.QT j), j ≠ 0 → (N.twist β u).evT m (N.twQ β u hm p) (N.twQ β u hj q).1.2 χ = (u ^ (β.be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2) + β.be q.1.1.toAdd (p.1.1.toAdd + m • χ) / j) : Oˣ) * N.evT m p q.1.2 χ) ∧ ∀ (j : ℕ) (hj : j ∣ k) (q q' : N.QT j), (N.twist β u).wp (N.twQ β u hj q) (N.twQ β u hj q') = N.wp q q' ∧ N.twQ β u hj (q * q') = N.twQ β u hj q * N.twQ β u hj q' ∧ (N.QEq q q' ↔ (N.twist β u).QEq (N.twQ β u hj q) (N.twQ β u hj q')) :=
  fun _ _ N _ β u m hm ho p χ => ⟨N.twist_txT β u m hm ho p χ, fun _ hj q _ => N.twist_evT β u m hm ho p χ hj q,
    fun _ hj q q' => ⟨N.twist_wp β u hj q q', N.twQ_mul β u hj q q', N.twist_qEq β u hj q q'⟩⟩
end GlobalTheory.Ex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTermsStatement
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
theorem _root_.GlobalTheory.T.twist_terms_alt : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (k : ℕ) (β : N.Form k) (u : Oˣ) (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∀ (p : N.QT (m ^ 2)) (χ : N.X), (N.twist β u).txT m (N.twQ β u hm p) χ = (u ^ (β.be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2)) : Oˣ) * N.txT m p χ ∧ (∀ (j : ℕ) (hj : j ∣ k) (q : N.QT j), j ≠ 0 → (N.twist β u).evT m (N.twQ β u hm p) (N.twQ β u hj q).1.2 χ = (u ^ (β.be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2) + β.be q.1.1.toAdd (p.1.1.toAdd + m • χ) / j) : Oˣ) * N.evT m p q.1.2 χ) ∧ ∀ (j : ℕ) (hj : j ∣ k) (q q' : N.QT j), (N.twist β u).wp (N.twQ β u hj q) (N.twQ β u hj q') = N.wp q q' ∧ N.twQ β u hj (q * q') = N.twQ β u hj q * N.twQ β u hj q' ∧ (N.QEq q q' ↔ (N.twist β u).QEq (N.twQ β u hj q) (N.twQ β u hj q')) := by
  first | exact @GlobalTheory.Ex.twist_terms | exact GlobalTheory.Ex.twist_terms | (intros; apply GlobalTheory.Ex.twist_terms <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SummableVtQT
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SummableVtQT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.NumD.Int
variable {C : Type} [NormedField C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}

theorem norm_vt_QT_le (h : N.Int q) {k : ℕ} (hk : k ≠ 0) (p : N.QT k) (χ : N.X) :
    ‖N.vt p.1.2 χ‖ ≤ Real.exp (-((q (p.1.1.toAdd + k • χ) - q p.1.1.toAdd) / (k : ℝ) ^ 2)) := by
  rw [NumD.vt]
  simp only [Units.val_mul, norm_mul, h.ψ, h.norm_rep_generators_eq_exp p hk]
  refine (mul_le_of_le_one_right (by positivity) (h.th _)).trans (le_of_eq ?_)
  rw [← Real.exp_add]
  congr 1
  have e : q (p.1.1.toAdd + k • χ) =
      q p.1.1.toAdd + (k : ℝ) ^ 2 * q χ + k * QuadraticMap.polar q p.1.1.toAdd χ := by
    have a : QuadraticMap.polar q p.1.1.toAdd (k • χ) = k * QuadraticMap.polar q p.1.1.toAdd χ := by
      rw [← natCast_zsmul, QuadraticMap.polar_smul_right, zsmul_eq_mul, Int.cast_natCast]
    have b : q (k • χ) = (k : ℝ) ^ 2 * q χ := by
      rw [← natCast_zsmul, QuadraticMap.map_smul, zsmul_eq_mul]
      push_cast
      ring
    rw [← a, ← b, QuadraticMap.polar]
    ring
  have : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  rw [e]
  field_simp
  ring

theorem tendsto_vt_QT (h : N.Int q) {k : ℕ} (hk : k ≠ 0) (p : N.QT k) :
    Filter.Tendsto (N.vt p.1.2) Filter.cofinite (nhds 0) := by
  have inj : Function.Injective fun χ : N.X => p.1.1.toAdd + k • χ := fun a b e => by
    have e' : k • a = k • b := add_left_cancel e
    rw [← natCast_zsmul, ← natCast_zsmul] at e'
    exact smul_right_injective N.X (Int.natCast_ne_zero.2 hk) e'
  have t₁ := h.pos.comp inj.tendsto_cofinite
  have kp : (0 : ℝ) < (k : ℝ) ^ 2 := pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)) 2
  have t₂ := (Filter.tendsto_atTop_add_const_right _ (-q p.1.1.toAdd) t₁).atTop_div_const kp
  have t₃ := Real.tendsto_exp_neg_atTop_nhds_zero.comp t₂
  refine squeeze_zero_norm (h.norm_vt_QT_le hk p) ?_
  simpa only [Function.comp_def, sub_eq_add_neg] using t₃

end GlobalTheory.Ex.NumD.Int

namespace GlobalTheory.Ex

theorem summable_vt_QT : ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ), N.Int q → ∀ (k : ℕ), k ≠ 0 → ∀ p : N.QT k, Summable (N.vt p.1.2) :=
  fun _ _ _ _ _ _ h _ hk p =>
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (h.tendsto_vt_QT hk p)
end GlobalTheory.Ex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SummableVtQTStatement
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_vt_of_int : ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ), N.Int q → ∀ (k : ℕ), k ≠ 0 → ∀ p : N.QT k, Summable (N.vt p.1.2) := by
  first | exact @GlobalTheory.Ex.summable_vt_QT | exact GlobalTheory.Ex.summable_vt_QT | (intros; apply GlobalTheory.Ex.summable_vt_QT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAffineHomOfIsAffineHomPullbackSndOfFpqc
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory

theorem _root_.GlobalTheory.isAffineHom_of_isAffineHom_pullback_snd_of_fpqc :
    ∀ (X Y Y' : Scheme.{0}) (f : X ⟶ Y) (g : Y' ⟶ Y), Surjective g → Flat g → QuasiCompact g →
      IsAffineHom (pullback.snd f g) → IsAffineHom f := by
  intro X Y Y' f g hs hf hq h
  haveI := _root_.GlobalTheory.isAffineHom_descendsAlong_fpqc
  exact MorphismProperty.DescendsAlong.of_isPullback (P := @IsAffineHom)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (IsPullback.of_hasPullback f g).flip
    ⟨⟨hs, hf⟩, hq⟩ h

end GlobalTheory
end
