module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfRangeSubset
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteOfIsClosedOfFiniteInterClosedPoints

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyQuasiFiniteOfCubicalPowIsoPull
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedStabiliser
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Stabiliser

theorem comp_eq_iff_range_subset {S : Scheme.{0}} {T X Z : Over S} [IsReduced T.left]
    [IsSeparated Z.hom] (f g : X ⟶ Z) (x : T ⟶ X) :
    x ≫ f = x ≫ g ↔ Set.range x.left ⊆ Set.range (equalizer.ι f g).left := by
  constructor
  · intro h
    rintro _ ⟨t, rfl⟩
    refine ⟨(equalizer.lift x h).left t, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι]
  · intro h
    have hs : Surjective (pullback.fst x.left (equalizer.ι f g).left) := by
      refine ⟨Set.range_eq_univ.1 ?_⟩
      rw [Scheme.Pullback.range_fst]
      exact Set.eq_univ_of_forall fun t => h ⟨t, rfl⟩
    have hc : (equalizer.ι f g).left ≫ f.left = (equalizer.ι f g).left ≫ g.left :=
      congrArg CommaMorphism.left (equalizer.condition f g)
    refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated Z.hom
      ((Over.w _).trans (Over.w _).symm) (pullback.fst x.left (equalizer.ι f g).left) ?_)
    rw [Over.comp_left, Over.comp_left, pullback.condition_assoc, pullback.condition_assoc, hc]

def stab {S : Scheme.{0}} {B Z : Over S} [GrpObj B] (φ : B ⟶ Z) : Subgroup (𝟙_ (Over S) ⟶ B) :=
  have key : ∀ a b : 𝟙_ (Over S) ⟶ B, (toUnit B ≫ (b * a)) * 𝟙 B =
      ((toUnit B ≫ a) * 𝟙 B) ≫ ((toUnit B ≫ b) * 𝟙 B) := fun a b => by
    rw [MonObj.comp_mul, MonObj.comp_mul, Category.comp_id, ← Category.assoc,
      toUnit_unique (_ ≫ toUnit B) (toUnit B), _root_.mul_assoc]
  have one : (toUnit B ≫ (1 : 𝟙_ (Over S) ⟶ B)) * 𝟙 B = 𝟙 B := by
    rw [MonObj.comp_one, _root_.one_mul]
  { carrier := {x | ((toUnit B ≫ x) * 𝟙 B) ≫ φ = φ}
    mul_mem' := fun {a b} ha hb => by
      rw [Set.mem_ofPred_eq] at ha hb ⊢
      rw [key, Category.assoc, ha, hb]
    one_mem' := by rw [Set.mem_ofPred_eq, one, Category.id_comp]
    inv_mem' := fun {a} ha => by
      rw [Set.mem_ofPred_eq] at ha ⊢
      conv_lhs => rw [← ha]
      rw [← Category.assoc, ← key, mul_inv_cancel, one, Category.id_comp] }

theorem exists_closed_stabiliser : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (Z : Over (Spec (CommRingCat.of K))) [IsSeparated Z.hom] (φ : B ⟶ Z), ∃ (C : Subgroup (𝟙_ _ ⟶ B)) (W : Set B.left), IsClosed W ∧ (∀ x, x ∈ C ↔ ((toUnit B ≫ x) * 𝟙 B) ≫ φ = φ) ∧ ∀ x, x ∈ C ↔ Set.range x.left ⊆ W := by
  intro K _ _ B _ _ hB Z _ φ
  have := hB.smooth
  have : IsReduced B.left := GlobalTheory.isReduced_of_smooth_of_isReduced B.hom
  have : IsReduced (𝟙_ (Over (Spec (CommRingCat.of K)))).left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of K)))
  refine ⟨stab φ, ⋂ z : 𝟙_ _ ⟶ B, Set.range
    (equalizer.ι ((𝟙 B * (toUnit B ≫ z)) ≫ φ) (toUnit B ≫ z ≫ φ)).left,
    isClosed_iInter fun z => (Scheme.Hom.isClosedEmbedding _).isClosed_range,
    fun _ => Iff.rfl, fun x => ?_⟩
  have e₁ : ∀ z : 𝟙_ _ ⟶ B, x ≫ (𝟙 B * (toUnit B ≫ z)) ≫ φ = z ≫ ((toUnit B ≫ x) * 𝟙 B) ≫ φ := by
    intro z
    simp only [← Category.assoc, MonObj.comp_mul, Category.comp_id]
    rw [toUnit_unique (x ≫ toUnit B) (𝟙 _), toUnit_unique (z ≫ toUnit B) (𝟙 _),
      Category.id_comp, Category.id_comp]
  have e₂ : ∀ z : 𝟙_ _ ⟶ B, x ≫ toUnit B ≫ z ≫ φ = z ≫ φ := by
    intro z
    rw [← Category.assoc, toUnit_unique (x ≫ toUnit B) (𝟙 _), Category.id_comp]
  rw [Set.subset_iInter_iff]
  simp only [← comp_eq_iff_range_subset, e₁, e₂]
  refine ⟨fun h z => congrArg (z ≫ ·) h, fun h => ?_⟩
  refine Over.OverMorphism.ext (GlobalTheory.ComplexPoints.hom_ext_of_points B.hom Z.hom
    ((Over.w _).trans (Over.w _).symm) fun y hy => ?_)
  exact congrArg CommaMorphism.left (h (Over.homMk y hy))

end GlobalTheory.Stabiliser
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyQuasiFiniteOfFiniteStabiliser
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteStabiliser

theorem apply_eq_of_range_subset_affine {K : Type} [Field K] {F Z : Scheme.{0}} [IsIntegral F]
    (q : F ⟶ Spec (.of K)) [UniversallyClosed q] (h : F ⟶ Z) {W : Z.Opens} (hW : IsAffineOpen W)
    (hh : ∀ a, h a ∈ W) (a b : F) : h a = h b := by
  have hr : Set.range h ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨c, rfl⟩
    exact hh c
  have : IsAffine W := hW
  let l := IsOpenImmersion.lift W.ι h hr
  have e : l ≫ W.ι = h := IsOpenImmersion.lift_fac _ _ _
  have e' : l = F.toSpecΓ ≫ Spec.map l.appTop ≫ W.toScheme.isoSpec.inv := by
    rw [← Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  letI := (isField_of_universallyClosed K q).toField
  have hab : F.toSpecΓ a = F.toSpecΓ b :=
    Subsingleton.elim (α := PrimeSpectrum Γ(F, ⊤)) _ _
  rw [← e, e']
  simp only [Scheme.Hom.comp_apply, hab]

theorem slice_eq {K : Type} [Field K] [IsAlgClosed K] {F B Z : Over (Spec (CommRingCat.of K))}
    [IsIntegral F.left] [UniversallyClosed F.hom] [IsIntegral B.left] [LocallyOfFiniteType B.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] (g : F ⊗ B ⟶ Z) (b : 𝟙_ _ ⟶ B) (z : Z.left)
    (hz : ∀ a, (lift (𝟙 F) (toUnit F ≫ b) ≫ g).left a = z) (f f' : 𝟙_ _ ⟶ F) :
    lift (toUnit B ≫ f) (𝟙 B) ≫ g = lift (toUnit B ≫ f') (𝟙 B) ≫ g := by
  have huc : UniversallyClosed (snd F B).left := by
    change UniversallyClosed (pullback.snd F.hom B.hom); infer_instance
  let j : (𝟙_ _ ⟶ B) → (F ⟶ F ⊗ B) := fun x ↦ lift (𝟙 F) (toUnit F ≫ x)
  have hpb (x : 𝟙_ _ ⟶ B) : IsPullback (j x).left F.hom (snd F B).left x.left := by
    have hw : x.left ≫ B.hom = 𝟙 _ := Over.w x
    have hr : IsPullback (fst F B).left (snd F B).left F.hom B.hom := .of_hasPullback F.hom B.hom
    refine IsPullback.of_right ?_ ?_ hr
    · have : (j x).left ≫ (fst F B).left = 𝟙 F.left := by
        rw [← Over.comp_left, lift_fst, Over.id_left]
      rw [this, hw]
      exact IsPullback.of_id_fst
    · rw [← Over.comp_left, lift_snd, Over.comp_left]
      rfl
  obtain ⟨_, ⟨W, hW, rfl⟩, hzW, -⟩ :=
    Z.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have hcl : IsClosed ((snd F B).left '' ((g.left ⁻¹ᵁ W : (F ⊗ B).left.Opens) : Set _)ᶜ) :=
    (snd F B).left.isClosedMap _ (g.left ⁻¹ᵁ W).isOpen.isClosed_compl
  let pt : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  have hlft : LocallyOfFiniteType ((lift (toUnit B ≫ f) (𝟙 B) ≫ g).left ≫ Z.hom) := by
    rw [Over.w]; infer_instance
  refine Over.OverMorphism.ext (ext_of_apply_eq (K := K) Z.hom _ hcl.isOpen_compl.isLocallyClosed
    (hcl.isOpen_compl.dense ⟨b.left pt, ?_⟩) (fun x hxV hx ↦ ?_) (by rw [Over.w, Over.w]))
  · rintro ⟨w, hw, hwb⟩
    obtain ⟨a, rfl, -⟩ := Scheme.exists_preimage_of_isPullback (hpb b) w pt hwb
    apply hw
    change g.left ((j b).left a) ∈ W
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hz]
    exact hzW
  · let p : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ B :=
      Over.homMk (pointOfClosedPoint (K := K) B.hom x hx)
        (pointOfClosedPoint_comp (K := K) B.hom x hx)
    have hp (s) : p.left s = x := pointOfClosedPoint_apply (K := K) B.hom x hx s
    have hin (a : F.left) : (j p ≫ g).left a ∈ W := by
      by_contra hn
      refine hxV ⟨(j p).left a, ?_, ?_⟩
      · rw [Over.comp_left, Scheme.Hom.comp_apply] at hn
        exact hn
      · rw [← Scheme.Hom.comp_apply, (hpb p).w, Scheme.Hom.comp_apply, hp]
    have key (u : 𝟙_ _ ⟶ F) :
        (lift (toUnit B ≫ u) (𝟙 B) ≫ g).left x = (j p ≫ g).left (u.left pt) := by
      have e : p ≫ lift (toUnit B ≫ u) (𝟙 B) ≫ g = u ≫ j p ≫ g := by
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        ext1
        · simp [j, toUnit_unique (toUnit _) (𝟙 _)]
        · simp [j, toUnit_unique (toUnit _) (𝟙 _)]
      rw [← hp pt, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left,
        ← Over.comp_left, e]
    rw [key, key]
    exact apply_eq_of_range_subset_affine (K := K) F.hom _ hW hin _ _

theorem finite_closedPoints_of_contracted {K : Type} [Field K] [IsAlgClosed K]
    {B Z : Over (Spec (CommRingCat.of K))} [GrpObj B] [IsIntegral B.left] [IsProper B.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] (φ : B ⟶ Z)
    (hφ : {x : 𝟙_ _ ⟶ B | ((toUnit B ≫ x) * 𝟙 B) ≫ φ = φ}.Finite)
    (S : TopologicalSpace.Closeds B.left) (hS : IsIrreducible (S : Set B.left)) (z : Z.left)
    (hz : ∀ y ∈ S, φ.left y = z) : ((S : Set B.left) ∩ closedPoints B.left).Finite := by
  let I := Scheme.IdealSheafData.vanishingIdeal S
  have hrange : Set.range I.subschemeι = S := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp [I]
  let F : Over (Spec (CommRingCat.of K)) := Over.mk (I.subschemeι ≫ B.hom)
  let i : F ⟶ B := Over.homMk I.subschemeι rfl
  have hemb := I.subschemeι.isClosedEmbedding
  have : IsReduced F.left := ReducedSubgroup.isReduced_subscheme_vanishingIdeal S
  have : IrreducibleSpace F.left := by
    have : IrreducibleSpace (Set.range I.subschemeι) := by
      rw [hrange]; exact Subtype.irreducibleSpace hS
    exact hemb.isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr this
  have : IsIntegral F.left := isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsProper F.hom := by change IsProper (I.subschemeι ≫ B.hom); infer_instance
  let pt : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  have hpt (y : B.left) (hy : y ∈ (S : Set B.left) ∩ closedPoints B.left) :
      ∃ u : 𝟙_ _ ⟶ F, (u ≫ i).left pt = y := by
    obtain ⟨a, rfl⟩ : y ∈ Set.range I.subschemeι := hrange ▸ hy.1
    have ha : IsClosed ({a} : Set F.left) := by
      refine hemb.isClosed_iff_image_isClosed.mpr ?_
      rw [Set.image_singleton]
      exact hy.2
    refine ⟨Over.homMk (pointOfClosedPoint (K := K) F.hom a ha)
      (pointOfClosedPoint_comp (K := K) F.hom a ha), ?_⟩
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact congrArg I.subschemeι (pointOfClosedPoint_apply (K := K) F.hom a ha pt)
  rcases ((S : Set B.left) ∩ closedPoints B.left).eq_empty_or_nonempty with h | ⟨y₀, hy₀⟩
  · rw [h]; exact Set.finite_empty
  obtain ⟨u₀, -⟩ := hpt y₀ hy₀
  refine (hφ.image fun s ↦ (s * (u₀ ≫ i)).left pt).subset fun y hy ↦ ?_
  obtain ⟨u, rfl⟩ := hpt y hy
  refine ⟨(u ≫ i) * (u₀ ≫ i)⁻¹, ?_, by simp only [inv_mul_cancel_right]⟩
  have key := slice_eq (((fst F B ≫ i) * snd F B) ≫ φ) (1 : 𝟙_ _ ⟶ B) z (fun a ↦ by
    rw [← Category.assoc, MonObj.comp_mul, lift_fst_assoc, lift_snd, MonObj.comp_one,
      _root_.mul_one, Category.id_comp, Over.comp_left, Scheme.Hom.comp_apply]
    exact hz _ (hrange.le ⟨a, rfl⟩)) u u₀
  have key' := congrArg (fun t ↦ ((toUnit B ≫ u₀ ≫ i)⁻¹ * 𝟙 B) ≫ t) key
  have hu (t : B ⟶ B) : t ≫ toUnit B = toUnit B := toUnit_unique _ _
  simp only [← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd, hu, Category.comp_id,
    mul_inv_cancel_left, Category.id_comp] at key'
  change (toUnit B ≫ ((u ≫ i) * (u₀ ≫ i)⁻¹) * 𝟙 B) ≫ φ = φ
  simp only [MonObj.comp_mul, GrpObj.comp_inv, _root_.mul_assoc, ← Category.assoc]
  exact key'

theorem locallyQuasiFinite_of_finite_stabiliser :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (Z : Over (Spec (CommRingCat.of K))) [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] (φ : B ⟶ Z), {x : 𝟙_ _ ⟶ B | ((toUnit B ≫ x) * 𝟙 B) ≫ φ = φ}.Finite → LocallyQuasiFinite φ.left := by
  intro K _ _ B _ _ hB Z _ _ φ hφ
  have := hB.proper
  have := hB.smooth
  have := hB.geomConnected
  have : GeometricallyIntegral B.hom := geometricallyIntegral_of_smooth B.hom
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have : IsProper (φ.left ≫ Z.hom) := by rw [Over.w]; infer_instance
  have : IsProper φ.left := .of_comp _ Z.hom
  have : JacobsonSpace B.left := LocallyOfFiniteType.jacobsonSpace B.hom
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : IsNoetherian B.left := {}
  refine locallyQuasiFinite_of_finite_fibres_closedPoints φ.left fun y hy ↦ ?_
  have hc : IsClosed (φ.left ⁻¹' {φ.left y}) := by
    refine IsClosed.preimage φ.left.continuous ?_
    simpa using φ.left.isClosedMap _ hy
  refine finite_of_isClosed_of_finite_inter_closedPoints hc ?_
  obtain ⟨T, hT, hTc, hTi, hTU⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hc
  rw [hTU, Set.sUnion_eq_biUnion, Set.iUnion₂_inter]
  refine hT.biUnion fun S hS ↦ ?_
  refine finite_closedPoints_of_contracted φ hφ ⟨S, hTc S hS⟩ (hTi S hS) (φ.left y) fun w hw ↦ ?_
  exact hTU.ge ⟨S, hS, hw⟩

end GlobalTheory.FiniteStabiliser
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyQuasiFiniteOfCubicalPowIsoPull
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CubicalQuasiFinite

theorem triv_translDiff_of_fixes {S : Scheme.{0}} {B Z : Over S} [GrpObj B] (φ : B ⟶ Z) {M : LB B.left}
    {H : LB Z.left} (hM : M.IsLB) (hH : H.IsLB) (hw : LBIso M (H.pull φ.left)) (x : 𝟙_ (Over S) ⟶ B)
    (hx : ((toUnit B ≫ x) * 𝟙 B) ≫ φ = φ) : Triv (translDiff B M x) := by
  obtain ⟨w, hw⟩ := hw
  replace hw := (isGen_iff w).1 hw
  have e : translPt B x ≫ φ = snd _ B ≫ φ := by
    have e₀ : translPt B x = snd _ B ≫ ((toUnit B ≫ x) * 𝟙 B) := by
      rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
        toUnit_unique (snd _ B ≫ toUnit B) (fst _ B)]
      rfl
    rw [e₀, Category.assoc, hx]
  have e' : (translPt B x).left ≫ φ.left = (snd _ B).left ≫ φ.left := congrArg CommaMorphism.left e
  obtain ⟨c, hc, -⟩ := exists_gen hH
    (φ' := fun k : Fin 2 => (![(translPt B x).left, (snd _ B).left] : Fin 2 → _) k ≫ φ.left) (ε' := ![1, -1])
    (fun U _ f => (Fintype.prod_empty _).trans (by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, e', zpow_one, zpow_neg,
        mul_inv_cancel])) (LB.oneGen H (Y := (𝟙_ (Over S) ⊗ B).left))
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
      (_root_.mul_one _)).symm)
  exact exists_down hw hH hM c hc

theorem locallyQuasiFinite_of_pow_iso_pull : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (L : RigLB B) (_ : CubicalStr B L) (r n : ℕ), n.Prime → (n : K) ≠ 0 → ¬ n ∣ r → (∀ x : baseOver _ ⟶ B, x ^ n = 1 → Triv (translDiff B L.L x) → x = 1) → ∀ (Z : Over (Spec (CommRingCat.of K))) [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] (φ : B ⟶ Z) (H : LB Z.left), H.IsLB → LBIso (pw L.L r) (H.pull φ.left) → LocallyQuasiFinite φ.left := by
  intro hcount K _ _ B _ _ hB L c r n hn hnK hnr hK Z _ _ φ H hH hw
  obtain ⟨C, W, hW, hC, hCW⟩ := GlobalTheory.Stabiliser.exists_closed_stabiliser K B hB Z φ
  have hfin : Finite C := by
    refine GlobalTheory.AbelianSubgroupFinite.finite_of_no_torsion hcount K B n hB hn hnK C W hW hCW fun x hx hxn => ?_
    have h₁ : Triv (translDiff B L.L (x ^ r)) :=
      ((GlobalTheory.Square.square_of_cubical _ B L c K (𝟙 _)).2 r x).1
        (triv_translDiff_of_fixes φ (isLB_pw L.isLB r) hH hw x ((hC x).1 hx))
    have h₂ : x ^ r = 1 := hK (x ^ r) (by
      change (x ^ r) ^ n = 1
      rw [← pow_mul, _root_.mul_comm, pow_mul, hxn, one_pow]) h₁
    have h₃ := pow_gcd_eq_one.2 ⟨hxn, h₂⟩
    rwa [(Nat.Prime.coprime_iff_not_dvd hn).2 hnr, pow_one] at h₃
  refine GlobalTheory.FiniteStabiliser.locallyQuasiFinite_of_finite_stabiliser K B hB Z φ ?_
  have e : {x : 𝟙_ _ ⟶ B | ((toUnit B ≫ x) * 𝟙 B) ≫ φ = φ} = (C : Set _) := Set.ext fun x => (hC x).symm
  rw [e]
  exact Set.toFinite _

end GlobalTheory.CubicalQuasiFinite
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyQuasiFiniteOfCubicalPowIsoPullStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.locallyQuasiFinite_of_cubical_pow_iso_pull : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (L : RigLB B) (_ : CubicalStr B L) (r n : ℕ), n.Prime → (n : K) ≠ 0 → ¬ n ∣ r → (∀ x : baseOver _ ⟶ B, x ^ n = 1 → Triv (translDiff B L.L x) → x = 1) → ∀ (Z : Over (Spec (CommRingCat.of K))) [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] (φ : B ⟶ Z) (H : LB Z.left), H.IsLB → LBIso (pw L.L r) (H.pull φ.left) → LocallyQuasiFinite φ.left := by
  first | exact @GlobalTheory.CubicalQuasiFinite.locallyQuasiFinite_of_pow_iso_pull | exact GlobalTheory.CubicalQuasiFinite.locallyQuasiFinite_of_pow_iso_pull | (intros; apply GlobalTheory.CubicalQuasiFinite.locallyQuasiFinite_of_pow_iso_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCoverNonzeroLocus
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CubeFree

section General
variable {X Y : Scheme.{0}} {L : LB X}

theorem gs_g_single (φ : Y ⟶ X) (n : ℤ) (j j' : Fin 1 → L.ι) (y : Y)
    (h : y ∈ LB.wchart L (fun _ : Fin 1 => φ) j) (h' : y ∈ LB.wchart L (fun _ : Fin 1 => φ) j') :
    (trF (L := L) (fun _ : Fin 1 => φ) (fun _ => n) (𝟙 Y) y j j').val =
      gs (𝟙 Y ≫ φ) y (L.U (j 0) ⊓ L.U (j' 0)) ((pw L n).g (j 0) (j' 0)).val := by
  have hm : (𝟙 Y ≫ φ) y ∈ L.U (j 0) ⊓ L.U (j' 0) := ⟨Set.mem_iInter.1 h 0, Set.mem_iInter.1 h' 0⟩
  refine Eq.trans ?_ (gs_unit _ y _ hm _).symm
  rw [trF, Fin.prod_univ_one]
  exact congrArg Units.val (map_zpow _ _ n).symm

theorem unitAt_of_pw {n : ℤ} (s : LB.Sec (pw L n)) (φ : Y ⟶ X) (y : Y) (i : L.ι)
    (h : φ y ∈ X.basicOpen (s.f i)) : UnitAt L (K := Fin 1) (fun _ => φ) (fun _ => n) y := by
  have l : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => φ) j ≤ φ ⁻¹ᵁ L.U (j 0) :=
    fun j => LB.wchart_le L _ j 0
  have v : ∀ (j : Fin 1 → L.ι) (z : Y), z ∈ LB.wchart L (fun _ : Fin 1 => φ) j →
      gs (𝟙 Y) z _ ((Y.presheaf.map (homOfLE (l j)).op).hom ((φ.app _).hom (s.f (j 0)))) =
        gs (𝟙 Y ≫ φ) z (L.U (j 0)) (s.f (j 0)) := fun j z hj =>
    (gs_res _ z _ hj _).trans (gs_pull _ φ z _ (l j hj) _)
  let s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => n)) :=
    { f := fun j => (Y.presheaf.map (homOfLE (l j)).op).hom ((φ.app _).hom (s.f (j 0)))
      compat := fun j j' => fn_ext fun z hz => by
        have hm : (𝟙 Y ≫ φ) z ∈ L.U (j 0) ⊓ L.U (j' 0) := ⟨l j hz.1, l j' hz.2⟩
        refine ((gs_res (𝟙 Y) z _ hz _).trans (v j z hz.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) z _ hz _ _).trans
          (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) z _ hz _).trans
            ((congrArg Units.val (gm_linComb L _ _ (𝟙 Y) z j j' hz.1 hz.2)).trans
              (gs_g_single φ n j j' z hz.1 hz.2))) ((gs_res (𝟙 Y) z _ hz _).trans (v j' z hz.2)))).symm)
        exact (gs_res _ z _ hm _).symm.trans ((congrArg (gs _ z _) (s.compat (j 0) (j' 0))).trans
          ((gs_mul _ z _ hm _ _).trans (congrArg _ (gs_res _ z _ hm _)))) }
  refine ⟨s', fun J hJ => isUnit_sval s' (𝟙 Y) y hJ (fun _ => i) ?_⟩
  have hi : y ∈ LB.wchart L (fun _ : Fin 1 => φ) (fun _ => i) :=
    Set.mem_iInter.2 fun _ => X.basicOpen_le _ h
  change y ∈ Y.basicOpen ((Y.presheaf.map (homOfLE (l fun _ => i)).op).hom ((φ.app _).hom (s.f i)))
  rw [Scheme.basicOpen_res]
  exact ⟨hi, (SetLike.ext_iff.1 (Scheme.preimage_basicOpen φ (s.f i)) y).1 h⟩

theorem exists_sec_of_unitAt (hL : L.IsLB) {n : ℤ} {x : X}
    (h : UnitAt L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => n) x) :
    ∃ t : LB.Sec (pw L n), x ∈ nonzeroLocus t := by
  obtain ⟨s, hs⟩ := h
  have l : ∀ i : L.ι, L.U i ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) :=
    fun i _ hy => Set.mem_iInter.2 fun _ => hy
  let t : LB.Sec (pw L n) :=
    { f := fun i => (X.presheaf.map (homOfLE (l i)).op).hom (s.f fun _ => i)
      compat := fun i i' => fn_ext fun z hz => by
        refine ((gs_res (𝟙 X) z _ hz _).trans (gs_res (𝟙 X) z (l i) hz.1 _)).trans (Eq.trans ?_
          ((gs_mul (𝟙 X) z _ hz _ _).trans (congrArg _
            ((gs_res (𝟙 X) z _ hz _).trans (gs_res (𝟙 X) z (l i') hz.2 _)))).symm)
        refine (sec_trans s (𝟙 X) z (l i hz.1) (l i' hz.2)).trans ?_
        rw [gs_g_single (𝟙 X) n _ _ z (l i hz.1) (l i' hz.2), Category.id_comp]
        rfl }
  obtain ⟨i, hi⟩ := exists_chart hL x
  refine ⟨t, TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩⟩
  obtain ⟨J, hJ, e⟩ := sval_trans hL s x (fun _ => i) (l i hi)
  have u : IsUnit (gs (𝟙 X) x (L.U i) (t.f i)) :=
    (congrArg IsUnit ((gs_res _ x (l i) hi _).trans e)).mpr ((Units.isUnit _).mul (hs J hJ))
  exact (X.mem_basicOpen _ x hi).2 ((congrArg IsUnit (gs_eq (𝟙 X) x _ hi _)).mp u)

theorem unitAt_of_triv (hL : L.IsLB) {I : Type} [Fintype I] {φ : I → (Y ⟶ X)} {ε : I → ℤ}
    (h : Triv (LB.LinComb L φ ε)) {Y' : Scheme.{0}} (e : Y' ⟶ Y) (k : ℕ) (y : Y') :
    UnitAt L (fun i => e ≫ φ i) (fun i => k * ε i) y := by
  obtain ⟨t, ht⟩ := h
  refine UnitAt.congr hL ?_ ⟨powSec (I := Fin k) fun _ => pullSec (genSec t ht) e, fun J hJ => ?_⟩
  · refine formEq_of_add fun U _ hh => ?_
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_smul, natCast_zsmul]
  · rw [sval_powSec _ _ _ hJ]
    refine IsUnit.prod_univ_iff.2 fun _ => ?_
    rw [sval_pullSec _ _ _ _ hJ, sval_genSec _ _ _ _ hJ]
    exact Units.isUnit _

end General

theorem exists_cover_nonzeroLocus : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (L : RigLB B) (_ : CubicalStr B L) (k : ℕ) (s : LB.Sec (pw L.L k)), (∃ j, s.f j ≠ 0) → ∃ (n : ℕ) (t : Fin (n + 1) → LB.Sec (pw L.L (2 * k : ℕ))), ⨆ i, nonzeroLocus (t i) = ⊤ := by
  intro K _ _ B _ _ hB L c k s ⟨j, hj⟩
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have : GeometricallyIntegral B.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ inferInstance inferInstance
  let T : Over (Spec (CommRingCat.of K)) := Over.mk (𝟙 _)
  have : IsIntegral (T ⊗ B).left :=
    GeometricallyIntegral.geometrically_isIntegral (𝟙 _) _ _ (IsPullback.of_hasPullback (𝟙 _) B.hom).flip
  have : IsIntegral B.left :=
    GeometricallyIntegral.geometrically_isIntegral (f := B.hom) (𝟙 _) _ _ (IsPullback.id_horiz B.hom)
  let q : B ⟶ T := Over.homMk B.hom (Category.comp_id _)
  let e : B ⟶ T ⊗ B := lift q (𝟙 B)
  have he : e ≫ snd T B = 𝟙 B := lift_snd _ _
  have hD : ((((snd T B).left ⁻¹ᵁ B.left.basicOpen (s.f j)) : (T ⊗ B).left.Opens) : Set (T ⊗ B).left).Nonempty := by
    obtain ⟨d, hd⟩ : ((B.left.basicOpen (s.f j) : B.left.Opens) : Set B.left).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      exact hj ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
    refine ⟨e.left d, ?_⟩
    show (snd T B).left (e.left d) ∈ B.left.basicOpen (s.f j)
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, he]
    exact hd
  have key : ∀ (x : T ⟶ B) (p : T.left), ∃ t : LB.Sec (pw L.L (2 * k : ℕ)), x.left p ∈ nonzeroLocus t := by
    intro x p
    have hq : x ≫ q = 𝟙 T := Over.OverMorphism.ext (Over.w x)
    have good : ∀ a : T ⟶ B, (ptSecT B (a * x)).left p ∈ (snd T B).left ⁻¹ᵁ B.left.basicOpen (s.f j) →
        UnitAt L.L (K := Fin 1) (fun _ => e.left ≫ (translPt B a).left) (fun _ => (k : ℤ)) (x.left p) := by
      intro a ha
      refine unitAt_of_pw s _ _ j ?_
      have E : x ≫ e ≫ translPt B a = ptSecT B (a * x) ≫ snd T B := by
        simp [e, ptSecT, NoBasePoint.translPt_eq, MonObj.comp_mul, reassoc_of% hq]
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left, E]
      exact ha
    obtain ⟨a, h₁, h₂⟩ := NoBasePoint.exists_two_points (𝟙 _) _ hD x x
    have sq := unitAt_of_triv L.isLB (Square.triv_square c a a⁻¹) e.left k (x.left p)
    have e1 : translPt B (1 : T ⟶ B) = snd _ _ := by
      rw [NoBasePoint.translPt_eq, MonObj.comp_one, _root_.one_mul]
    have e2 : e.left ≫ (snd T B).left = 𝟙 _ := by rw [← Over.comp_left, he]; rfl
    refine exists_sec_of_unitAt L.isLB (UnitAt.congr L.isLB (formEq_of_add fun U _ hh => ?_)
      (((good a (h₁ p)).mul (good a⁻¹ (h₂ p))).mul sq))
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_one, Fin.sum_univ_four,
      Matrix.cons_val, _root_.mul_inv_cancel]
    rw [e1, e2]
    push_cast
    module
  have top : ⨆ t : LB.Sec (pw L.L (2 * k : ℕ)), nonzeroLocus t = ⊤ := by
    have : JacobsonSpace B.left := LocallyOfFiniteType.jacobsonSpace B.hom
    by_contra h
    have hne : ((⨆ t : LB.Sec (pw L.L (2 * k : ℕ)), nonzeroLocus t : B.left.Opens) : Set B.left)ᶜ.Nonempty :=
      Set.nonempty_compl.2 fun h' => h (SetLike.coe_injective h')
    obtain ⟨z, hz, hc⟩ := nonempty_inter_closedPoints hne
      (TopologicalSpace.Opens.isOpen _).isClosed_compl.isLocallyClosed
    obtain ⟨t, ht⟩ := key (Over.homMk (pointOfClosedPoint B.hom z hc) (pointOfClosedPoint_comp B.hom z hc))
      (IsLocalRing.closedPoint K)
    exact hz (TopologicalSpace.Opens.mem_iSup.2 ⟨t,
      (congrArg (· ∈ nonzeroLocus t) (pointOfClosedPoint_apply B.hom z hc _)).mp ht⟩)
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun t : LB.Sec (pw L.L (2 * k : ℕ)) => (nonzeroLocus t : Set B.left)) (fun t => (nonzeroLocus t).isOpen)
    (fun z _ => by
      have : z ∈ (⨆ t : LB.Sec (pw L.L (2 * k : ℕ)), nonzeroLocus t) := by rw [top]; trivial
      exact Set.mem_iUnion.2 (TopologicalSpace.Opens.mem_iSup.1 this))
  refine ⟨F.card, Fin.cons (secZero _) (fun i => (F.equivFin.symm i).1), top_unique fun z _ => ?_⟩
  obtain ⟨t, ht, hz⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ z))
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨(F.equivFin ⟨t, ht⟩).succ, ?_⟩
  rw [Fin.cons_succ, Equiv.symm_apply_apply]
  exact hz

end GlobalTheory.CubeFree
end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AmpleCrit

variable {X X' : Scheme.{0}}

theorem pull_pw_eq (M : LB X) (π : X' ⟶ X) (t : ℤ) :
    (AbLaw.pw M t).pull π = AbLaw.pw (M.pull π) t := by
  refine congrArg (LB.mk (M.pull π).ι (M.pull π).U) ?_
  funext j j'
  change ∏ _k : PUnit, _ = (∏ _k : PUnit, _) ^ t
  refine Eq.trans ?_ (Finset.prod_zpow
    (G := Γ(X', LB.wchart M (fun _ : PUnit => π) j ⊓ LB.wchart M (fun _ : PUnit => π) j')ˣ) _ _ t)
  refine Finset.prod_congr rfl fun k _ => ?_
  refine (zpow_one _).trans (Eq.trans ?_ (congrArg (· ^ t) (zpow_one _)).symm)
  exact (congrArg (res _) (map_zpow (pullU π _) (M.g (j k) (j' k)) t)).trans (map_zpow (res _) _ t)

theorem pw_pw_eq (M : LB X) (a b : ℤ) : AbLaw.pw (AbLaw.pw M a) b = AbLaw.pw M (a * b) := by
  simp only [AbLaw.pw, zpow_mul]
  rfl

theorem injective_stalkMap (π : X' ⟶ X) [Flat π] (z : X') : Function.Injective (π.stalkMap z).hom := by
  algebraize [(π.stalkMap z).hom]
  have : Module.Flat (X.presheaf.stalk (π z)) (X'.presheaf.stalk z) := Flat.stalkMap π z
  have : IsLocalHom (algebraMap (X.presheaf.stalk (π z)) (X'.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (π.stalkMap z).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := X.presheaf.stalk (π z)) (B := X'.presheaf.stalk z)
  exact FaithfulSMul.algebraMap_injective _ _

theorem gs_zero' (π : X' ⟶ X) (z : X') (U : X.Opens) (h : π z ∈ U) : gs π z U 0 = 0 := by
  rw [gs_eq π z U h, map_zero, map_zero]

theorem exists_sec_pull_ne_zero (π : X' ⟶ X) [Flat π] [Surjective π] {M : LB X} (hM : M.IsLB)
    (s : LB.Sec M) (hs : ∃ j, s.f j ≠ 0) : ∃ s' : LB.Sec (M.pull π), ∃ j, s'.f j ≠ 0 := by
  have hM' := pull_isLB hM π
  obtain ⟨⟨s', hs', -⟩, -⟩ := SecPullIso.section_pull X X' π M (M.pull π) _ hM hM'
    (CubePf.idIsoL_isGen hM') s
  refine ⟨s', ?_⟩
  by_contra h
  push Not at h
  obtain ⟨j, hj⟩ := hs
  refine hj (fn_ext fun x hx => ?_)
  obtain ⟨z, rfl⟩ := π.surjective x
  have hz : z ∈ (M.pull π).U (fun _ => j) := mem_pull.2 hx
  have e := hs' z j (fun _ => j) hx hz
  have e₀ : gs (𝟙 X') z ((M.pull π).U fun _ => j) (s'.f fun _ => j) = 0 :=
    (congrArg (gs (𝟙 X') z _) (h fun _ => j)).trans (gs_zero' _ z _ hz)
  replace e := e.trans ((congrArg _ e₀).trans (mul_zero _))
  rw [gs_stalkMap π z _ hx] at e
  rw [gs_zero' (𝟙 X) (π z) _ hx]
  exact injective_stalkMap π z (e.trans (map_zero _).symm)

def zeroSec (M : LB X) : LB.Sec M := ⟨fun _ => 0, fun _ _ => by rw [map_zero, map_zero, mul_zero]⟩

theorem exists_cover_of_pull {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (hg : g.Flat)
    [CompactSpace X] [QuasiSeparatedSpace X] (f : X ⟶ Spec (CommRingCat.of R)) (π : X' ⟶ X)
    (f' : X' ⟶ Spec (CommRingCat.of R')) (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    [Surjective π] {M : LB X} (hM : M.IsLB) {n : ℕ} (t : Fin (n + 1) → LB.Sec (M.pull π))
    (ht : ⨆ i, nonzeroLocus (t i) = ⊤) :
    ∃ (m : ℕ) (u : Fin (m + 1) → LB.Sec M), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  choose m c u hu using fun i => FlatSec.exists_comb_of_flat R R' g hg X f X' π f' h M hM (t i)
  let I := Σ i, Fin (m i)
  let e : Option I ≃ Fin (Fintype.card I + 1) := Fintype.equivFinOfCardEq Fintype.card_option
  let v : Option I → LB.Sec M := fun o => o.elim (zeroSec M) fun q => u q.1 q.2
  refine ⟨Fintype.card I, fun a => v (e.symm a), top_le_iff.1 fun x _ => ?_⟩
  obtain ⟨z, rfl⟩ := π.surjective x
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show z ∈ ⨆ i, nonzeroLocus (t i) by rw [ht]; trivial)
  obtain ⟨J, hJ, hun⟩ := (mem_nonzeroLocus _ _).1 hi
  have hk : π z ∈ M.U (J PUnit.unit) := mem_pull.1 hJ
  have e₁ := hu i z (J PUnit.unit) hk
  have hun' := (congrArg IsUnit e₁).mp hun
  obtain ⟨a, -, ha⟩ := IsLocalRing.exists_of_isUnit_sum hun'
  have ha' := isUnit_of_mul_isUnit_right ha
  rw [gs_stalkMap π z _ hk] at ha'
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨e (some ⟨i, a⟩), ?_⟩
  beta_reduce
  rw [Equiv.symm_apply_apply]
  exact (mem_nonzeroLocus _ _).2 ⟨_, hk, (isUnit_map_iff (π.stalkMap z).hom _).1 ha'⟩

theorem exists_map {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) {M : LB X} (hM : M.IsLB)
    {n : ℕ} (t : Fin (n + 1) → LB.Sec M) (ht : ⨆ i, nonzeroLocus (t i) = ⊤) :
    ∃ (P : Scheme.{0}) (q : P ⟶ Spec (CommRingCat.of R)) (H : LB P) (φ : X ⟶ P), IsProper q ∧ H.IsLB ∧
      φ ≫ q = f ∧ LBIso M (H.pull φ) ∧
      ∀ i, ∃ V : P.Opens, IsAffineOpen V ∧ nonzeroLocus (t i) = φ ⁻¹ᵁ V := by
  obtain ⟨P, q, H, s, hH, hva, heq⟩ := ProjQuot.exists_veryAmpleBy_of_ideal R n ⊥ (fun F hF d => by
    rw [Ideal.mem_bot] at hF ⊢
    rw [hF, map_zero])
  obtain ⟨φ, w, hφ, hw, hs⟩ := exists_hom_of_veryAmpleBy R P q H n s hH hva X f M t hM ht (fun d F hF h0 k => by
    obtain ⟨a, ha⟩ := (heq d F hF).1 h0 0
    rw [Ideal.mem_bot] at ha
    have : F = 0 := ((MvPolynomial.isRegular_X (n := (0 : Fin (n + 1))) (R := R)).pow a).left
      (ha.trans (mul_zero _).symm)
    rw [this, map_zero])
  exact ⟨P, q, H, φ, isProper_of_isProjBy R P q ⟨H, hH, n, s, hva⟩, hH, hφ, ⟨w, hw⟩, fun i =>
    ⟨_, (hva.2 i).1, (SecPullIso.section_pull P X φ H M w hH hM hw (s i)).2 (t i) (hs i)⟩⟩

theorem triv_translDiff_push {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) {L : LB A.left} (hL : L.IsLB) {T' : Over S'}
    (x : T' ⟶ A') (hx : Triv (translDiff A' (L.pull φ) x)) : Triv (translDiff A L (pushPt h.1.w x)) := by
  obtain ⟨c, hc⟩ := hx
  have hL' := pull_isLB hL φ
  let T : Over S := Over.mk (T'.hom ≫ f)
  let T₂ : Over S' := Over.mk ((fst T A).left ≫ T'.hom)
  have sq : (snd T A).left ≫ A.hom = ((fst T A).left ≫ T'.hom) ≫ f :=
    pullback.condition.symm.trans (Category.assoc _ _ _).symm
  let a : T₂ ⟶ T' := Over.homMk (fst T A).left rfl
  let b : T₂ ⟶ A' := Over.homMk (h.1.lift _ _ sq) (h.1.lift_snd _ _ _)
  have hb : b.left ≫ φ = (snd T A).left := h.1.lift_fst _ _ _
  have k₂ : (lift a b).left ≫ (snd T' A').left ≫ φ = (snd T A).left :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ φ) (lift_snd a b)).trans hb)
  have k₃ : (lift a b).left ≫ ((fst T' A' ≫ x) * snd T' A').left ≫ φ =
      ((fst T A ≫ pushPt h.1.w x) * snd T A).left := by
    have e : lift a b ≫ ((fst T' A' ≫ x) * snd T' A') = (a ≫ x) * b := by
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
    let j : Over.mk (T₂.hom ≫ f) ⟶ T ⊗ A := Over.homMk (𝟙 _) ((Category.id_comp _).trans
      ((Over.w (snd T A)).symm.trans sq))
    have e₁ := h.2 T₂ (a ≫ x) b (j ≫ fst T A ≫ pushPt h.1.w x) (j ≫ snd T A)
      ((Category.id_comp _).trans (Category.assoc _ _ _).symm) ((Category.id_comp _).trans hb.symm)
    rw [← MonObj.comp_mul, ← e] at e₁
    exact (Category.assoc _ _ _).symm.trans (e₁.symm.trans (Category.id_comp _))
  obtain ⟨c₂, h₂, -⟩ := exists_up ((isGen_iff _).1 (CubePf.idIsoL_isGen hL')) hL hL' c hc
  refine gen_chartPull (chartPullSame L _ _ _ (lift a b).left fun k => ?_) c₂ h₂
  fin_cases k
  exacts [k₃.symm, k₂.symm]

theorem relAmple_of_effective : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → ∀ (R : Type) [CommRing R], IsField R → ∀ (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (L : RigLB B) (_ : CubicalStr B L) (k : ℕ) (s : LB.Sec (pw L.L k)), 1 ≤ k → (∃ j, s.f j ≠ 0) → ∀ (K : Type) [Field K] [IsAlgClosed K] (p : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (n : ℕ), n.Prime → (n : K) ≠ 0 → ¬ n ∣ 2 * k → (∀ x : Over.mk p ⟶ B, x ^ n = 1 → Triv (translDiff B L.L x) → x = 1) → RelAmple B L.L := by
  intro hcount R _ hR B _ _ hB L c k s hk hs K _ _ p n hn hnK hnk hx
  obtain ⟨g, rfl⟩ : ∃ g : R →+* K, p = Spec.map (CommRingCat.ofHom g) :=
    ⟨(Spec.preimage p).hom, (Spec.map_preimage p).symm⟩
  have hg : g.Flat := RingHom.Flat.of_isField hR g
  set p := Spec.map (CommRingCat.ofHom g) with hp
  have : Flat p := (HasRingHomProperty.Spec_iff (P := @Flat)).2 hg
  have : Surjective p := ⟨fun y => by
    let := hR.toField
    have : Subsingleton (Spec (CommRingCat.of R)) := inferInstanceAs (Subsingleton (PrimeSpectrum R))
    exact ⟨(default : PrimeSpectrum K), Subsingleton.elim _ _⟩⟩
  have := hB.proper
  let B' : Over (Spec (CommRingCat.of K)) := (Over.pullback p).obj B
  let π : B'.left ⟶ B.left := pullback.fst B.hom p
  have h : IsGrpPullback B' B p π := isGrpPullback_pullback B p
  have : IsCommMonObj B' := PolPull.isCommMonObj_of_isGrpPullback h
  have hB' : IsAbelianScheme B' := by
    have := hB.comm
    exact
      { comm := PolPull.isCommMonObj_of_isGrpPullback h
        smooth := MorphismProperty.of_isPullback (P := @Smooth) h.1 hB.smooth
        proper := MorphismProperty.of_isPullback (P := @IsProper) h.1 hB.proper
        geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hB.geomConnected }
  have : Flat π := MorphismProperty.of_isPullback (P := @Flat) h.1.flip inferInstance
  have : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) h.1.flip inferInstance
  obtain ⟨hL', hr, ⟨c', -⟩, -⟩ := CubePf.cubePull _ _ B B' (cubeMapOf h) L c

  have hsec : ∃ s' : LB.Sec (AbLaw.pw (L.L.pull π) k), ∃ j, s'.f j ≠ 0 :=
    pull_pw_eq L.L π k ▸ exists_sec_pull_ne_zero π (isLB_pw L.isLB k) s hs
  obtain ⟨s', hs'⟩ := hsec
  have hcov : ∃ (m : ℕ) (t : Fin (m + 1) → LB.Sec ((AbLaw.pw L.L (2 * k : ℕ)).pull π)),
      ⨆ i, nonzeroLocus (t i) = ⊤ := by
    rw [pull_pw_eq]
    exact CubeFree.exists_cover_nonzeroLocus K B' hB' ((cubeMapOf h).rigLB L hL' hr) c' k s' hs'
  obtain ⟨m', t', ht'⟩ := hcov
  have hM := isLB_pw L.isLB (2 * k : ℕ)
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : QuasiSeparatedSpace B.left := quasiSeparatedSpace_of_quasiSeparated B.hom
  obtain ⟨m, t, ht⟩ := exists_cover_of_pull g hg B.hom π B'.hom h.1 hM t' ht'
  obtain ⟨P, q, H, φ, hq, hH, hφ, hiso, hloc⟩ := exists_map B.hom hM t ht

  let Z : Over (Spec (CommRingCat.of K)) := Over.mk (pullback.snd q p)
  let ρ : Z.left ⟶ P := pullback.fst q p
  let φ' : B' ⟶ Z := Over.homMk (pullback.lift (π ≫ φ) B'.hom (by rw [Category.assoc, hφ]; exact h.1.w))
    (pullback.lift_snd _ _ _)
  have hφ' : φ'.left ≫ ρ = π ≫ φ := pullback.lift_fst _ _ _
  have hZ : IsPullback ρ Z.hom q p := IsPullback.of_hasPullback q p
  have hsq : IsPullback π φ'.left φ ρ := by
    refine IsPullback.of_bot ?_ hφ'.symm hZ
    rw [Over.w φ', hφ]
    exact h.1
  have : IsProper Z.hom := MorphismProperty.of_isPullback (P := @IsProper) hZ hq
  have : Surjective ρ := MorphismProperty.of_isPullback (P := @Surjective) hZ.flip inferInstance
  have hqf' : LocallyQuasiFinite φ'.left := by
    refine GlobalTheory.T.locallyQuasiFinite_of_cubical_pow_iso_pull hcount K B' hB' ((cubeMapOf h).rigLB L hL' hr) c' (2 * k) n hn hnK hnk
      (fun x hxn htr => ?_) Z φ' (H.pull ρ) (pull_isLB hH ρ) ?_
    · have key : ∀ p' : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R), p' = p →
          ∀ y : Over.mk p' ⟶ B, y ^ n = 1 → Triv (translDiff B L.L y) → y = 1 := by
        rintro _ rfl
        exact hx
      have e : pushHom h _ x = 1 := key _ (Category.id_comp p) (pushHom h _ x)
        (by rw [← map_pow, hxn, map_one]) (triv_translDiff_push h L.isLB x htr)
      have e' := e.trans (map_one (pushHom h (baseOver _))).symm
      exact Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e') (by rw [Over.w, Over.w]))
    · show LBIso (AbLaw.pw (L.L.pull π) (2 * k : ℕ)) ((H.pull ρ).pull φ'.left)
      rw [← pull_pw_eq]
      exact LBIso.chartPull (Geo.Tor.chartPullPull _ π π rfl)
        (chartPullLinComb H ρ (fun _ => φ'.left) (fun _ => φ) (fun _ => 1) π fun _ => hφ') hiso
  have : IsProper (φ ≫ q) := hφ ▸ hB.proper
  have : IsProper φ := IsProper.of_comp φ q
  have : LocallyQuasiFinite φ := Unif.locallyQuasiFinite_of_isPullback_surjective _ _ _ _ φ φ'.left π ρ hsq
    inferInstance inferInstance inferInstance hqf'
  have : IsFinite φ := IsFinite.of_isProper_of_locallyQuasiFinite φ
  have hva := veryAmpleBy_pw_of_affine_loci R B.left B.hom _ m t hM ht fun i => by
    obtain ⟨V, hV, e⟩ := hloc i
    rw [e]
    exact hV.preimage φ
  obtain ⟨d, hd, hva⟩ := hva
  rw [pw_pw_eq, ← Nat.cast_mul] at hva
  exact (Unif.relAmple_iff_veryAmpleBy R B L.L L.isLB).2
    ⟨2 * k * d, Nat.mul_pos (by omega) hd, hva⟩

end GlobalTheory.AmpleCrit
