module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRingHomComplexCompEqOfCountable
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUnifExpUnique

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingHenselianAndSmoothPointsLift
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingHenselianAndSmoothPointsLift
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem splits_of_monic_of_valuationRing_of_isAlgClosed (O K : Type*) [CommRing O] [IsDomain O]
    [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K]
    {f : Polynomial O} (hf : f.Monic) : f.Splits := by
  refine Polynomial.Splits.of_splits_map_of_injective (IsFractionRing.injective O K)
    (IsAlgClosed.splits _) fun a ha => ?_
  have hroot : Polynomial.eval₂ (algebraMap O K) a f = 0 := by
    rw [Polynomial.mem_roots (hf.map _).ne_zero, Polynomial.IsRoot, Polynomial.eval_map] at ha
    exact ha
  have hint : IsIntegral O a := ⟨f, hf, hroot⟩
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  exact ⟨b, hb⟩

theorem henselianLocalRing_of_valuationRing_of_isAlgClosed (O K : Type*) [CommRing O] [IsDomain O]
    [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] :
    HenselianLocalRing O where
  is_henselian f hf a₀ h₁ _ := by
    have hs := splits_of_monic_of_valuationRing_of_isAlgClosed O K hf
    rw [hs.eval_eq_prod_roots_of_monic hf a₀,
      (IsLocalRing.maximalIdeal.isMaximal O).isPrime.multiset_prod_mem_iff_exists_mem] at h₁
    obtain ⟨c, hc, hcm⟩ := h₁
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hc
    refine ⟨r, (Polynomial.mem_roots hf.ne_zero).mp hr, ?_⟩
    rw [← neg_sub]
    exact neg_mem hcm

theorem isAlgClosed_residueField_of_valuationRing_of_isAlgClosed (O K : Type*) [CommRing O]
    [IsDomain O] [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] :
    IsAlgClosed (IsLocalRing.ResidueField O) := by
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  obtain ⟨g, hg, hdeg, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.map_surjective _ IsLocalRing.residue_surjective p) hp
  have hs := splits_of_monic_of_valuationRing_of_isAlgClosed O K hgm
  have hd : g.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hgm.ne_zero, hdeg]
    exact_mod_cast (Irreducible.natDegree_pos hirr).ne'
  obtain ⟨r, hr⟩ := hs.exists_eval_eq_zero hd
  exact ⟨IsLocalRing.residue O r, by rw [← hg, Polynomial.eval_map, Polynomial.eval₂_at_apply, hr, map_zero]⟩

theorem valuationRing_henselian_and_lift_of_isAlgClosed :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K], HenselianLocalRing O ∧ IsAlgClosed (IsLocalRing.ResidueField O) ∧ ∀ (X : Scheme.{0}) (f : X ⟶ Sp O), Smooth f → ∀ x : Sp (IsLocalRing.ResidueField O) ⟶ X, x ≫ f = spMap (IsLocalRing.residue O) → ∃ y : Sp O ⟶ X, y ≫ f = 𝟙 _ ∧ spMap (IsLocalRing.residue O) ≫ y = x := by
  intro O K _ _ _ _ _ _ _
  have := henselianLocalRing_of_valuationRing_of_isAlgClosed O K
  refine ⟨inferInstance, isAlgClosed_residueField_of_valuationRing_of_isAlgClosed O K, ?_⟩
  intro X f hf x hx
  have := hf
  obtain ⟨⟨y, hy⟩, hy'⟩ := reducePoint_residue_surjective f O (𝟙 _) ⟨x, by simpa using hx⟩
  refine ⟨y, hy, ?_⟩
  exact congrArg Subtype.val hy'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingHenselianAndSmoothPointsLiftStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.valuationRing_henselian_and_smooth_points_lift : ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K], HenselianLocalRing O ∧ IsAlgClosed (IsLocalRing.ResidueField O) ∧ ∀ (X : Scheme.{0}) (f : X ⟶ Sp O), Smooth f → ∀ x : Sp (IsLocalRing.ResidueField O) ⟶ X, x ≫ f = spMap (IsLocalRing.residue O) → ∃ y : Sp O ⟶ X, y ≫ f = 𝟙 _ ∧ spMap (IsLocalRing.residue O) ≫ y = x := by
  first | exact @GlobalTheory.valuationRing_henselian_and_lift_of_isAlgClosed | exact GlobalTheory.valuationRing_henselian_and_lift_of_isAlgClosed | (intros; apply GlobalTheory.valuationRing_henselian_and_lift_of_isAlgClosed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeOfIsPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkSetPull

theorem range_of_isPullback {P X Y Z : Scheme.{0}} {a : P ⟶ X} {b : P ⟶ Y} {c : X ⟶ Z} {d : Y ⟶ Z}
    (h : IsPullback a b c d) : Set.range a = c ⁻¹' Set.range d := by
  rw [← AlgebraicGeometry.Scheme.Pullback.range_fst c d]
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨h.isoPullback.hom q, by rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]⟩
  · rintro ⟨q, rfl⟩
    exact ⟨h.isoPullback.inv q, by rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst]⟩

theorem exists_equiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    ∃ ρ : (T ⟶ G') ≃* (Over.mk (T.hom ≫ f) ⟶ G), ∀ x, (ρ x).left = x.left ≫ φ := by
  refine ⟨{ toFun := fun x => Over.homMk (x.left ≫ φ) (by rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x]; rfl)
            invFun := fun y => Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _)
            left_inv := fun x => by
              apply Over.OverMorphism.ext
              apply h.1.hom_ext
              · exact h.1.lift_fst _ _ _
              · exact (h.1.lift_snd _ _ _).trans (Over.w x).symm
            right_inv := fun y => by
              apply Over.OverMorphism.ext
              exact h.1.lift_fst _ _ _
            map_mul' := fun x y => by
              apply Over.OverMorphism.ext
              exact (h.2 T x y _ _ rfl rfl).symm }, fun x => rfl⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}} {t : SAB H S}
  {t' : SAB H S'} {f : S' ⟶ S}

theorem heckeKer_iff (D : Datum H) (P : Ideal (𝓞 E)) (p i : ℕ) (m : SABMap t' t f) (T : Over S')
    (C' : Subgroup (T ⟶ t'.G)) (C : Subgroup (Over.mk (T.hom ≫ f) ⟶ t.G))
    (h : ∀ (u : T ⟶ t'.G) (v : Over.mk (T.hom ≫ f) ⟶ t.G), v.left = u.left ≫ m.φ → (u ∈ C' ↔ v ∈ C)) :
    t'.HeckeKer T D P p i C' ↔ t.HeckeKer (Over.mk (T.hom ≫ f)) D P p i C := by
  obtain ⟨ρ, hρ⟩ := exists_equiv m.cart T
  have hC : ∀ u, u ∈ C' ↔ ρ u ∈ C := fun u => h u (ρ u) (hρ u)
  have hact : ∀ u a, ρ (u ≫ t'.act.act a) = ρ u ≫ t.act.act a := by
    intro u a
    apply Over.OverMorphism.ext
    rw [hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, Category.assoc]
    exact congrArg (u.left ≫ ·) (m.act a)
  have htors : ∀ I u, u ∈ t'.tors T I ↔ ρ u ∈ t.tors (Over.mk (T.hom ≫ f)) I := by
    intro I u
    simp only [SAB.tors, Set.mem_ofPred_eq]
    refine forall₂_congr fun a _ => ?_
    rw [← hact, map_eq_one_iff ρ ρ.injective]
  have hL : LBIso t'.PP.L (t.PP.L.pull m.φ) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hW : ∀ u v, Out.WeilIs t'.G t'.PP.L ((p : ℤ) ^ 2) u v 1 ↔ Out.WeilIs t.G t.PP.L ((p : ℤ) ^ 2) (ρ u) (ρ v) 1 :=
    fun u v => GlobalTheory.weilIs_iff_of_isGrpPullback_comm S S' t.G t'.G f m.φ t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB m.cart hL
      T _ u v (ρ u) (ρ v) 1 (hρ u) (hρ v)
  have cC : Nat.card C' = Nat.card C := Nat.card_congr (ρ.toEquiv.subtypeEquiv hC)
  have cT : ∀ I, Nat.card (t'.tors T I) = Nat.card (t.tors (Over.mk (T.hom ≫ f)) I) :=
    fun I => Nat.card_congr (ρ.toEquiv.subtypeEquiv (htors I))
  have cI : ∀ I, Nat.card ((C' : Set (T ⟶ t'.G)) ∩ t'.tors T I : Set (T ⟶ t'.G)) =
      Nat.card ((C : Set (Over.mk (T.hom ≫ f) ⟶ t.G)) ∩ t.tors (Over.mk (T.hom ≫ f)) I : Set (Over.mk (T.hom ≫ f) ⟶ t.G)) :=
    fun I => Nat.card_congr (ρ.toEquiv.subtypeEquiv fun u => (hC u).and (htors I u))
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx a
      obtain ⟨u, rfl⟩ := ρ.surjective x
      rw [← hact]
      exact (hC _).mp (h1 u ((hC u).mpr hx) a)
    · intro J hJ x hx
      obtain ⟨u, rfl⟩ := ρ.surjective x
      exact (hC u).mp (h2 J hJ ((htors J u).mpr hx))
    · intro x hx
      obtain ⟨u, rfl⟩ := ρ.surjective x
      exact (htors _ u).mp (h3 ((hC u).mpr hx))
    · intro x hx y hy
      obtain ⟨u, rfl⟩ := ρ.surjective x
      obtain ⟨v, rfl⟩ := ρ.surjective y
      exact (hW u v).mp (h4 u ((hC u).mpr hx) v ((hC v).mpr hy))
    · rw [← cC]
      exact h5
    · rw [← cT, ← cI]
      exact h6
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu a
      rw [hC, hact]
      exact h1 _ ((hC u).mp hu) a
    · intro J hJ u hu
      exact (hC u).mpr (h2 J hJ ((htors J u).mp hu))
    · intro u hu
      exact (htors _ u).mpr (h3 ((hC u).mp hu))
    · intro u hu v hv
      exact (hW u v).mpr (h4 _ ((hC u).mp hu) _ ((hC v).mp hv))
    · rw [cC]
      exact h5
    · rw [cT, cI]
      exact h6

theorem heckeSet_pull (D : Datum H) (P : Ideal (𝓞 E)) (p i : ℕ) (m : SABMap t' t f) (K : Set t.G.left)
    (hK : HeckeSet D t P p i K) : HeckeSet D t' P p i (m.φ ⁻¹' K) := by
  intro k _ _ x
  obtain ⟨C, hCK, hC⟩ := hK k (x ≫ f)
  obtain ⟨ρ, hρ⟩ := exists_equiv m.cart (Over.mk x)
  refine ⟨C.comap ρ.toMonoidHom, fun z => ?_, ?_⟩
  · show ρ z ∈ C ↔ _
    rw [hCK, hρ]
    simp only [Set.range_subset_iff, Set.mem_preimage, Scheme.Hom.comp_apply]
    exact Iff.rfl
  · refine (heckeKer_iff D P p i m (Over.mk x) _ C ?_).mpr hC
    intro u v huv
    obtain rfl : v = ρ u := Over.OverMorphism.ext (huv.trans (hρ u).symm)
    exact Iff.rfl

theorem etSet_pull {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left} (h : IsPullback φ G'.hom G.hom f)
    (K : Set G.left) (hK : EtSet G K) : EtSet G' (φ ⁻¹' K) := by
  obtain ⟨C, j, hfin, het, hcl, hCK⟩ := hK
  have w : (pullback.fst C.hom f ≫ j.left) ≫ G.hom = pullback.snd C.hom f ≫ f := by
    rw [Category.assoc, Over.w j, pullback.condition]
  let j' : Over.mk (pullback.snd C.hom f) ⟶ G' :=
    Over.homMk (h.lift (pullback.fst C.hom f ≫ j.left) (pullback.snd C.hom f) w) (h.lift_snd _ _ _)
  have sq : IsPullback (pullback.fst C.hom f) j'.left j.left φ := by
    refine IsPullback.of_bot (v₂₁ := G'.hom) (v₂₂ := G.hom) (h₃₁ := f) ?_ (h.lift_fst _ _ _).symm h
    have e : j'.left ≫ G'.hom = pullback.snd C.hom f := h.lift_snd _ _ _
    rw [e, Over.w j]
    exact IsPullback.of_hasPullback C.hom f
  refine ⟨Over.mk (pullback.snd C.hom f), j', ?_, ?_, ?_, ?_⟩
  · show IsFinite (pullback.snd C.hom f)
    infer_instance
  · show Etale (pullback.snd C.hom f)
    infer_instance
  · exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq hcl
  · rw [range_of_isPullback sq.flip, hCK]

theorem lists_pull {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (K : Set G.left) (N n : ℕ) (σ : Fin n → (𝟙_ (Over S) ⟶ G)) (hK : Lists N σ K) :
    ∃ σ' : Fin n → (𝟙_ (Over S') ⟶ G'), (∀ j, (σ' j).left ≫ φ = f ≫ (σ j).left) ∧ Lists N σ' (φ ⁻¹' K) := by
  obtain ⟨ρ, hρ⟩ := exists_equiv h (𝟙_ (Over S'))
  let σ' : Fin n → (𝟙_ (Over S') ⟶ G') := fun j => ρ.symm (toUnit _ ≫ σ j)
  have key : ∀ j, (σ' j).left ≫ φ = f ≫ (σ j).left := by
    intro j
    rw [← hρ, MulEquiv.apply_symm_apply, Over.comp_left, Over.toUnit_left]
    simp [Over.tensorUnit_hom]
  have sq : ∀ j, IsPullback (σ' j).left f φ (σ j).left := by
    intro j
    refine (IsPullback.of_bot (v₂₁ := G'.hom) (v₂₂ := G.hom) (h₃₁ := f) ?_ (key j).symm h.1).flip
    rw [Over.w (σ' j), Over.w (σ j)]
    simp only [Over.tensorUnit_hom]
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  refine ⟨σ', key, ?_, ?_, ?_⟩
  · intro j
    apply ρ.injective
    rw [map_pow, MulEquiv.apply_symm_apply, ← MonObj.comp_pow, hK.1 j, MonObj.comp_one, map_one]
  · rw [hK.2.1, Set.preimage_iUnion]
    exact Set.iUnion_congr fun j => (range_of_isPullback (sq j)).symm
  · intro k _ _ x i j hij
    apply hK.2.2 k (x ≫ f)
    have e := congrArg (· ≫ φ) hij
    simp only [Category.assoc, key] at e
    simpa only [Category.assoc] using e

end GlobalTheory.HkSetPull

theorem GlobalTheory.heckeSets_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f), IsProper t.G.hom → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S') (C' : Subgroup (Over.mk x ⟶ t'.G)) (C : Subgroup (Over.mk (x ≫ f) ⟶ t.G)), (∀ (u : Over.mk x ⟶ t'.G) (v : Over.mk (x ≫ f) ⟶ t.G), v.left = u.left ≫ m.φ → (u ∈ C' ↔ v ∈ C)) → (t'.HeckeKer (Over.mk x) D 𝔓 p i C' ↔ t.HeckeKer (Over.mk (x ≫ f)) D 𝔓 p i C)) ∧ ∀ K : Set t.G.left, (HeckeSet D t 𝔓 p i K → HeckeSet D t' 𝔓 p i (m.φ ⁻¹' K)) ∧ (EtSet t.G K → EtSet t'.G (m.φ ⁻¹' K)) ∧ ∀ (N n : ℕ) (σ : Fin n → (𝟙_ (Over S) ⟶ t.G)), Lists N σ K → ∃ σ' : Fin n → (𝟙_ (Over S') ⟶ t'.G), (∀ j, (σ' j).left ≫ m.φ = f ≫ (σ j).left) ∧ Lists N σ' (m.φ ⁻¹' K) := by
  intro E _ _ _ H D 𝔓 p i S S' t t' f m _
  exact ⟨fun k _ _ x C' C h => GlobalTheory.HkSetPull.heckeKer_iff D 𝔓 p i m (Over.mk x) C' C h,
    fun K => ⟨fun hK => GlobalTheory.HkSetPull.heckeSet_pull D 𝔓 p i m K hK,
      fun hK => GlobalTheory.HkSetPull.etSet_pull m.cart.1 K hK,
      fun N n σ hK => GlobalTheory.HkSetPull.lists_pull m.cart K N n σ hK⟩⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FlatOfIsFiniteOfFinitePresentationOfFlatGeometri
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace FinitePresFibreFlat

open TensorProduct IsLocalRing FiniteFibreFlat

section Algebra

theorem free_of_flat_reduction {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsLocalRing A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Flat R M]
    [Module.FinitePresentation A M] (p : Ideal R) (hp : p.map (algebraMap R A) ≤ maximalIdeal A)
    [Module.Flat (A ⧸ p.map (algebraMap R A)) ((A ⧸ p.map (algebraMap R A)) ⊗[A] M)] :
    Module.Free A M := by
  set I := p.map (algebraMap R A) with hI
  have hrel : LocalFlat.RelationsLift I M :=
    LocalFlat.relationsLift_of_flat (C := A ⧸ I) Ideal.Quotient.mk_surjective Ideal.mk_ker
      (TensorProduct.mk A (A ⧸ I) M 1) (TensorProduct.mk_surjective A M (A ⧸ I)
        Ideal.Quotient.mk_surjective) (LinearMap.ker_tensorProductMk M)
  apply Module.free_of_maximalIdeal_rTensor_injective
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj, injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hrel (maximalIdeal A) (maximalIdeal A).subtype x (by rw [hx]; simp)
  let e := Submodule.comapSubtypeEquivOfLe hp
  have hy : I.subtype.lTensor M (e.toLinearMap.lTensor M y) = 0 := by
    rw [← hx, ← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply]
    rfl
  rw [map_eq_zero_iff _ (lTensor_map_injective p)] at hy
  have : y = 0 := (LinearEquiv.lTensor M e).injective (hy.trans (map_zero _).symm)
  rw [this, map_zero]

theorem flat_of_flat_fibres {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Module.FinitePresentation A B]
    [Module.Flat R B]
    (H : ∀ (k C : Type) [Field k] [CommRing C] [Algebra A C] (t : R →+* k) (h : k →+* C),
      (algebraMap A C).comp (algebraMap R A) = h.comp t → Module.Flat C (C ⊗[A] B)) :
    Module.Flat A B := by
  refine Module.flat_of_isLocalized_maximal A B (fun P _ => Localization.AtPrime P ⊗[A] B)
    (fun P _ => TensorProduct.mk A (Localization.AtPrime P) B 1) fun P _ => ?_
  let A' := Localization.AtPrime P
  let p : Ideal R := (maximalIdeal A').comap (algebraMap R A')
  let I := p.map (algebraMap R A')
  have h1 : Module.Flat R (B ⊗[A] A') := Module.Flat.trans R B (B ⊗[A] A')
  have h2 : Module.Flat R (A' ⊗[A] B) :=
    Module.Flat.of_linearEquiv
      ((Algebra.TensorProduct.comm A A' B).restrictScalars R).toLinearEquiv
  have h3 : Module.Flat (A' ⧸ I) ((A' ⧸ I) ⊗[A] B) := by
    let ψ : R →+* A' ⧸ I := (Ideal.Quotient.mk I).comp (algebraMap R A')
    have hψ₁ : p ≤ RingHom.ker ψ := fun r hr =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)
    have hψ₂ : p.primeCompl ≤ (IsUnit.submonoid (A' ⧸ I)).comap ψ := by
      intro r hr
      have : IsUnit (algebraMap R A' r) := by
        by_contra h
        exact hr h
      exact this.map (Ideal.Quotient.mk I)
    refine H p.ResidueField (A' ⧸ I) (algebraMap R _) (Ideal.ResidueField.lift p ψ hψ₁ hψ₂) ?_
    ext r
    exact (Ideal.ResidueField.lift_algebraMap p ψ hψ₁ hψ₂ r).symm
  have h4 : Module.Flat (A' ⧸ I) ((A' ⧸ I) ⊗[A'] (A' ⊗[A] B)) :=
    Module.Flat.of_linearEquiv
      (AlgebraTensorModule.cancelBaseChange A A' (A' ⧸ I) (A' ⧸ I) B)
  have h5 : Module.Free A' (A' ⊗[A] B) :=
    free_of_flat_reduction p Ideal.map_comap_le
  have h6 : Module.Flat A' (A' ⊗[A] B) := Module.Flat.of_free
  exact Module.Flat.trans A A' (A' ⊗[A] B)

end Algebra

open FibreFlat

set_option backward.isDefEq.respectTransparency false in
theorem flat_of_flatOver_fields {X Y S : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ S)
    (hY : LocallyOfFinitePresentation g) (h0 : LocallyOfFinitePresentation (f ≫ g))
    (h1 : Flat (f ≫ g)) (h2 : IsFinite f)
    (H : ∀ (k : Type) [Field k] (t : Spec (CommRingCat.of k) ⟶ S), FlatOver f g t) :
    Flat f := by
  wlog hS : ∃ R, S = Spec R generalizing X Y S
  · refine IsZariskiLocalAtTarget.of_openCover (S.affineCover.pullback₁ g) fun i => ?_
    let u := S.affineCover.f i
    have sq := IsPullback.of_hasPullback f (pullback.fst g u)
    have sq' := IsPullback.of_hasPullback g u
    refine this (pullback.snd f (pullback.fst g u)) (pullback.snd g u)
      inferInstance (MorphismProperty.of_isPullback (sq.paste_vert sq') h0)
      (MorphismProperty.of_isPullback (sq.paste_vert sq') h1) inferInstance
      (fun k _ t => flatOver_of_comp_base (u := u) ?_) ⟨_, rfl⟩
    rw [← pullback.condition]
    exact (H k _).target sq
  obtain ⟨R, rfl⟩ := hS
  wlog hA : ∃ A, Y = Spec A generalizing X Y
  · refine IsZariskiLocalAtTarget.of_openCover Y.affineCover fun i => ?_
    have sq := IsPullback.of_hasPullback f (Y.affineCover.f i)
    have e : pullback.snd f (Y.affineCover.f i) ≫ Y.affineCover.f i ≫ g =
        pullback.fst f (Y.affineCover.f i) ≫ f ≫ g := by
      rw [← Category.assoc, ← sq.w, Category.assoc]
    exact this (pullback.snd f (Y.affineCover.f i)) inferInstance (Y.affineCover.f i ≫ g)
      inferInstance (by rw [e]; infer_instance) (by rw [e]; infer_instance)
      (fun k _ t => (H k t).target sq) ⟨_, rfl⟩
  obtain ⟨A, rfl⟩ := hA
  wlog hX : ∃ B, X = Spec B generalizing X
  · haveI hX' : IsAffine X := isAffine_of_isAffineHom f
    rw [← MorphismProperty.cancel_left_of_respectsIso @Flat X.isoSpec.inv]
    exact this (X.isoSpec.inv ≫ f) inferInstance (by rw [Category.assoc]; infer_instance)
      (by rw [Category.assoc]; infer_instance)
      (fun k _ t => (H k t).source _) ⟨_, rfl⟩
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  rw [← Spec.map_comp] at h1 h0
  rw [Flat.SpecMap_iff] at h1 ⊢
  rw [IsFinite.SpecMap_iff] at h2
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)] at hY h0
  letI : Algebra R A := g.hom.toAlgebra
  letI : Algebra A B := f.hom.toAlgebra
  letI : Algebra R B := (g ≫ f).hom.toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Flat R B := h1
  haveI : Module.Finite A B := h2
  haveI : Algebra.FinitePresentation R A := hY
  haveI : Algebra.FinitePresentation R B := h0
  haveI : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R A B
  haveI : Module.FinitePresentation A B :=
    Module.FinitePresentation.of_finite_of_finitePresentation A B
  refine flat_of_flat_fibres (R := R) (A := A) (B := B) fun k C _ _ _ t h e => ?_
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A C B)
  have := H k (Spec.map (CommRingCat.ofHom t)) _ _ _ (Spec.map (CommRingCat.ofHom h)) sq.flip
    (by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext1
      exact e)
  rw [Flat.SpecMap_iff] at this
  exact RingHom.flat_algebraMap_iff.mp this

end FinitePresFibreFlat

theorem flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres :
    ∀ (S : Scheme.{0}) (X Y : Over S) (f : X ⟶ Y), Flat X.hom → LocallyOfFinitePresentation X.hom → LocallyOfFinitePresentation Y.hom → IsFinite f.left → (∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ S), Flat ((Over.pullback t).map f).left) → Flat f.left := by
  intro S X Y f h1 h0 h2 h3 H
  refine FinitePresFibreFlat.flat_of_flatOver_fields f.left Y.hom h2 (by rwa [Over.w])
    (by rwa [Over.w]) h3 fun k _ t => ?_
  exact FiniteFibreFlat.flatOver_descend
    (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
    (FibreFlat.flatOver_of_pullback f _ (H _ _))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalStrOfTrivTheta
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.Moduli

theorem cubicalStr_of_triv_theta : Out.Laws → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : LB A.left, M.IsLB → Out.Rigidified A M → Triv (Theta A M) → ∃ L : RigLB A, L.L = M ∧ Nonempty (CubicalStr A L) := by
  intro hL S A _ _ hA M hM hR hT
  obtain ⟨t, ht⟩ := hT
  obtain ⟨r, hr⟩ := hR
  obtain ⟨t', ht', hn⟩ := GlobalTheory.AbLaw.Cube.exists_normalised hM t ht
  exact ⟨⟨M, r, hM, hr⟩, rfl, ⟨GlobalTheory.AbLaw.Cube.cubicalOfNormalised
    (by cases hL; assumption) hA ⟨M, r, hM, hr⟩ t' ht' hn⟩⟩

end GlobalTheory.Moduli
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PadicIntermediateFieldIntRingCompleteDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PadicIntermediateFieldIntRingCompleteDvr
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem lift_mem_valuationSubring_iff {K L : Type*} [Field K] [Field L] (A : ValuationSubring L) (i : K →+* L)
    (h : Function.Injective (i.comp (A.comap i).subtype)) (x : FractionRing (A.comap i)) :
    IsFractionRing.lift (A := A.comap i) (K := FractionRing (A.comap i)) h x ∈ A ↔
      x ∈ Set.range (algebraMap (A.comap i) (FractionRing (A.comap i))) := by
  let f := FractionRing.algEquiv (A.comap i) K
  have hf : IsFractionRing.lift (A := A.comap i) (K := FractionRing (A.comap i)) h =
      i.comp f.toRingEquiv.toRingHom := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (A.comap i)) (RingHom.ext fun a => ?_)
    refine (IsFractionRing.lift_algebraMap h a).trans ?_
    exact congrArg i (f.commutes a).symm
  rw [hf]
  refine ⟨fun hx => ⟨⟨f x, hx⟩, f.injective (f.commutes _)⟩, ?_⟩
  rintro ⟨v, rfl⟩
  rw [← hf, IsFractionRing.lift_algebraMap]
  exact v.2

theorem intRing_complete_dvr : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → IsDiscreteValuationRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ∧ IsAdicComplete (IsLocalRing.maximalIdeal (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ∧ ∀ x : FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K), ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) (FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K))) := by
  intro p _ K hK
  have hmem : ∀ x : K, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K ↔ ‖(x : PadicAlgCl p)‖ ≤ 1 := fun x => mem_OO_iff _
  let e : integralClosure ℤ_[p] K ≃+* GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K :=
    { toFun := fun x => ⟨x.1, (hmem _).2 ((mem_integralClosure_padicInt_iff K _).1 x.2)⟩
      invFun := fun x => ⟨x.1, (mem_integralClosure_padicInt_iff K _).2 ((hmem _).1 x.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  have hc := CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[p] (integralClosure ℤ_[p] K)
  refine ⟨IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e, ?_, fun x => ?_⟩
  · have := (IsAdicComplete.congr_ringEquiv (IsLocalRing.maximalIdeal _) e).2 hc
    rwa [IsLocalRing.map_ringEquiv_maximalIdeal] at this
  · rw [← mem_OO_iff]
    exact lift_mem_valuationSubring_iff (OO p) (algebraMap K (PadicAlgCl p))
      (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing_injective K) x

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PadicIntermediateFieldIntRingCompleteDvrStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicIntermediateFieldIntRing_complete_dvr : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → IsDiscreteValuationRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ∧ IsAdicComplete (IsLocalRing.maximalIdeal (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ∧ ∀ x : FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K), ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) (FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K))) := by
  first | exact @GlobalTheory.intRing_complete_dvr | exact GlobalTheory.intRing_complete_dvr | (intros; apply GlobalTheory.intRing_complete_dvr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPELPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELPull

theorem lbIso_pull {X Y Y' : Scheme.{0}} {A : LB Y} {L : LB X} {φ : Y ⟶ X} (H : LBIso A (L.pull φ)) (h : Y' ⟶ Y)
    {F : Y' ⟶ X} (e : F = h ≫ φ) : LBIso (A.pull h) (L.pull F) :=
  H.chartPull (chartPullPull A h h rfl)
    (chartPullSame L (fun _ : PUnit => F) (fun _ : PUnit => φ) (fun _ => 1) h fun _ => e)

theorem isPEL_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g k : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (o : Type) [CommRing o] (b : TBase o k) (ρ : o) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s) (t' : TObj g k J b s') (τ : SAB H S), f ≫ s = s' → TMap t' t f → IsPEL D a bas ρ t τ → ∃ τ' : SAB H S', IsPEL D a bas ρ t' τ' := by
  intro E _ _ _ H D g k J a bas o _ b ρ S S' s s' f t t' τ hs ⟨ψ, hψ, hψL, hpt, hact⟩ ⟨φ, hφ, hφL, hφa, hgeom⟩
  obtain ⟨τ', ⟨m⟩⟩ : ∃ τ' : SAB H S', Nonempty (SABMap τ' τ f) := by
    have hC := Out.CubePf.cubePull
    have hsemi : IsSemiAbelian ((Over.pullback f).obj τ.G) := by
      refine { comm := ?_, smooth := ?_, separated := ?_, quasiCompact := ?_, geomConnected := ?_, fibres := ?_ }
      · have := τ.semi.comm
        infer_instance
      · have := τ.semi.smooth
        change Smooth (pullback.snd τ.G.hom f)
        infer_instance
      · have := τ.semi.separated
        change IsSeparated (pullback.snd τ.G.hom f)
        infer_instance
      · have := τ.semi.quasiCompact
        change QuasiCompact (pullback.snd τ.G.hom f)
        infer_instance
      · have := τ.semi.geomConnected
        change GeometricallyConnected (pullback.snd τ.G.hom f)
        infer_instance
      · intro Ω _ _ q
        obtain ⟨A⟩ := τ.semi.fibres Ω (q ≫ f)
        exact ⟨torusExtOfIso (pullCompIso q f τ.G) A⟩
    have hp : ∃ (PP' : RigLB ((Over.pullback f).obj τ.G)) (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric) (adj : _) (prim : _)
        (m : SABMap ⟨(Over.pullback f).obj τ.G, hsemi, OAct.pullback f τ.G τ.act, PP', cub,
          sym, adj, prim⟩ τ f), m.φ = pullback.fst τ.G.hom f := by
      have h := isGrpPullback_pullback τ.G f
      obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := hC S S' τ.G _ (cubeMapOf h) τ.PP τ.cub
      have hact : ∀ a, ((OAct.pullback f τ.G τ.act).act a).left ≫ pullback.fst τ.G.hom f =
          pullback.fst τ.G.hom f ≫ (τ.act.act a).left := fun a => pullback.lift_fst _ _ _
      have pa : ∀ {T : Over S'} (x : T ⟶ (Over.pullback f).obj τ.G) a,
          pushPt h.1.w (x ≫ (OAct.pullback f τ.G τ.act).act a) = pushPt h.1.w x ≫ τ.act.act a := fun x a =>
        Over.OverMorphism.ext (by
          show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
          rw [Category.assoc, hact, Category.assoc])
      refine ⟨(cubeMapOf h).rigLB τ.PP hL hr, c', hs τ.sym, fun a => ?_, ?_, ⟨cubeMapOf h, h, rfl, hact, hc'⟩, rfl⟩
      · let U := lift (pushPt h.1.w (fst ((Over.pullback f).obj τ.G) ((Over.pullback f).obj τ.G)))
          (pushPt h.1.w (snd ((Over.pullback f).obj τ.G) ((Over.pullback f).obj τ.G)))
        refine LBIso.chartPull (chartPullLinComb τ.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
          (chartPullLinComb τ.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (τ.adj a)
        · fin_cases i
          · exact (pa _ a).trans (by simp [U])
          · simp [U]
        · fin_cases i
          · simp [U]
          · exact (pa _ _).trans (by simp [U])
      · let U := pushPt h.1.w (𝟙 ((Over.pullback f).obj τ.G))
        refine LBIso.chartPull (chartPullPull τ.PP.L _ U.left (Category.id_comp _))
          (chartPullLinComb τ.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) τ.prim
        fin_cases i
        · simp [U]
        · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
    obtain ⟨_, _, _, _, _, m, -⟩ := hp
    exact ⟨_, ⟨m⟩⟩
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → (F : Y ⟶ X) → (L.pull F).IsLB := by
    intro X Y L hL F
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)

  have hL : LBIso τ'.PP.L (τ.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hc : IsGrpPullback τ'.G t.A f (m.cm.F ≫ φ.hom.left) :=
    (IsGrpPullback.comp m.cart (isGrpPullback_of_iso φ)).congr (Category.comp_id f) rfl
  obtain ⟨e, he, heF⟩ := grpPullback_iso hc hψ
  refine ⟨τ', e, he, ?_, fun j => ?_, fun K _ _ _ x β hx => ?_⟩
  · exact (hL.trans τ'.PP.isLB (pull_isLB τ.PP.isLB _) (pull_isLB t.isLB _) (lbIso_pull hφL m.cm.F rfl)).trans
      τ'.PP.isLB (pull_isLB t.isLB _) (pull_isLB t'.isLB _) (lbIso_pull hψL e.hom.left heF.symm).symm
  · apply Over.OverMorphism.ext
    apply hψ.1.hom_ext
    · have h₁ : (τ.act.act (a j)).left ≫ φ.hom.left = φ.hom.left ≫ (t.act j).left :=
        congrArg (fun z => z.left) (hφa j)
      have h₂ : (τ'.act.act (a j)).left ≫ m.cm.F = m.cm.F ≫ (τ.act.act (a j)).left := m.act _
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, heF, hact, ← Category.assoc, h₂,
        Category.assoc, h₁, ← Category.assoc, ← heF, Category.assoc]
    · rw [Over.w, Over.w]
  · obtain ⟨hdet, I, hI, hA⟩ := hgeom K (x ≫ f) β (by rw [Category.assoc, hs, hx])
    refine ⟨fun σ => ?_, GlobalTheory.ObjPull.tateMove (GlobalTheory.ObjPull.pushEquiv m.cart (Over.mk x)) (fun c y => ?_)
      (fun n y y' c hc => ?_) I, hI, fun i => ?_⟩
    · rw [GlobalTheory.LiePull.lieMult_pull _ S S' τ.G τ'.G f m.cm.F τ.act τ'.act m.cart m.act K x σ,
        GlobalTheory.LiePull.lieMult_pull _ S S' τ.G τ'.G f m.cm.F τ.act τ'.act m.cart m.act K x σ]
      exact hdet σ
    · apply Over.OverMorphism.ext
      show (y.left ≫ _) ≫ _ = (y.left ≫ _) ≫ _
      rw [Category.assoc, m.act, Category.assoc]
    · exact (GlobalTheory.weilIs_grpPullback_of_comm S S' τ.G τ'.G f m.cm.F τ.PP.L τ'.PP.L τ.PP.isLB τ'.PP.isLB m.cart hL
        (Over.mk x) n y y' _ _ _ rfl rfl).2 hc
    · apply Over.OverMorphism.ext
      apply hψ.1.hom_ext
      · have h₁ : (I.ev k (bas (Pi.single i 1))).left ≫ φ.hom.left = (x ≫ f) ≫ (t.pt i).left :=
          congrArg (fun z => z.left) (hA i)
        have h₂ := GlobalTheory.ObjPull.pushEquiv_symm_left m.cart (Over.mk x) (I.ev k (bas (Pi.single i 1)))
        show (((GlobalTheory.ObjPull.pushEquiv m.cart (Over.mk x)).symm (I.ev k (bas (Pi.single i 1)))).left ≫ e.hom.left) ≫ ψ =
          (x ≫ (t'.pt i).left) ≫ ψ
        rw [Category.assoc, heF, Category.assoc, hpt]
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ.hom.left) h₂).trans (h₁.trans (Category.assoc _ _ _)))
      · rw [Over.w, Over.w]

end GlobalTheory.PELPull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EpsPtScaleZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.PointUnif

section Deriv

open GlobalTheory.TangentOrigin GlobalTheory.LieEtale

variable {g g' : ℕ} {X Y : Scheme.{0}}

theorem evalPt_comp {R : Type} [CommRing R] (x : Sp R ⟶ X) (φ : X ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U) (f : Γ(Y, U)) :
    evalPt (x ≫ φ) U h f = evalPt x (φ ⁻¹ᵁ U) h ((φ.app U).hom f) := by
  have := Scheme.Hom.appLE_comp_appLE x φ U (φ ⁻¹ᵁ U) ⊤ le_rfl h
  unfold evalPt
  rw [← this, Scheme.Hom.app_eq_appLE]
  rfl

theorem valAt'_comp (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' (x ≫ φ) U f = valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) := by
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · rw [valAt'_eq_evalPt _ _ h, valAt'_eq_evalPt x (φ ⁻¹ᵁ U) h, evalPt_comp]
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U := h
    unfold valAt'
    rw [dite_eq_right h, dite_eq_right h']

theorem isHolTo_comp {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} (he : IsHolTo Set.univ e) (φ : X ⟶ Y) :
    IsHolTo Set.univ fun z => e z ≫ φ := by
  intro U f
  simp only [valAt'_comp]
  exact he (φ ⁻¹ᵁ U) ((φ.app U).hom f)

theorem isHolTo_linear {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} (he : IsHolTo Set.univ e)
    (F : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) : IsHolTo Set.univ fun z => e (F z) := by
  intro U f
  have hF : Differentiable ℂ F := F.toContinuousLinearMap.differentiable
  exact ⟨(he U f).1.preimage hF.continuous, (he U f).2.comp hF.differentiableOn fun z hz => hz⟩

theorem isDerivAt0_iff {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ X} :
    IsDerivAt0 e w v ↔ spMap fstC ≫ v = e 0 ∧ ∀ (U : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)),
      (evalPt v U h f).snd = fderiv ℂ (fun z => valAt' (e z) U f) 0 w := Iff.rfl

theorem deriv_comp {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ X}
    (h : IsDerivAt0 e w v) (φ : X ⟶ Y) : IsDerivAt0 (fun z => e z ≫ φ) w (v ≫ φ) := by
  rw [isDerivAt0_iff] at h ⊢
  refine ⟨by rw [← h.1, Category.assoc], fun U hU f => ?_⟩
  simp only [valAt'_comp]
  rw [evalPt_comp]
  exact h.2 _ _ _

theorem deriv_unique {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v v' : Sp (DualNumber ℂ) ⟶ X}
    (h : IsDerivAt0 e w v) (h' : IsDerivAt0 e w v') : v = v' := by
  rw [isDerivAt0_iff] at h h'
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (e 0 (default : PrimeSpectrum ℂ))) isOpen_univ
  have h0 : ⊤ ≤ e 0 ⁻¹ᵁ U := fun q _ => by
    rw [Subsingleton.elim (α := PrimeSpectrum ℂ) q default]; exact hx
  have hv : ⊤ ≤ v ⁻¹ᵁ U := (top_le_preimage_iff v U).2 (h.1 ▸ h0)
  have hv' : ⊤ ≤ v' ⁻¹ᵁ U := (top_le_preimage_iff v' U).2 (h'.1 ▸ h0)
  refine ext_evalPt hU hv hv' (RingHom.ext fun f => TrivSqZeroExt.ext ?_ ((h.2 U hv f).trans (h'.2 U hv' f).symm))
  have key : ∀ (u : Sp (DualNumber ℂ) ⟶ X) (hu : ⊤ ≤ u ⁻¹ᵁ U) (y : Sp ℂ ⟶ X) (hy : ⊤ ≤ y ⁻¹ᵁ U),
      spMap fstC ≫ u = y → (evalPt u U hu f).fst = evalPt y U hy f := by
    rintro u hu y hy rfl
    exact (evalPt_spMap_comp fstC u U hu hy f).symm
  exact (key v hv _ h0 h.1).trans (key v' hv' _ h0 h'.1).symm

theorem deriv_linear {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} (he : IsHolTo Set.univ e)
    (F : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) {w : Fin g' → ℂ} {v : Sp (DualNumber ℂ) ⟶ X} :
    IsDerivAt0 (fun z => e (F z)) w v ↔ IsDerivAt0 e (F w) v := by
  rw [isDerivAt0_iff, isDerivAt0_iff, map_zero]
  refine and_congr_right fun h0 => forall₃_congr fun U hU f => ?_
  have hU0 : ⊤ ≤ e 0 ⁻¹ᵁ U := h0 ▸ (top_le_preimage_iff v U).1 hU
  have hd : DifferentiableAt ℂ (fun z => valAt' (e z) U f) (F.toContinuousLinearMap 0) := by
    rw [map_zero]
    exact (he U f).2.differentiableAt ((he U f).1.mem_nhds ⟨trivial, hU0⟩)
  have := (hd.hasFDerivAt.comp 0 F.toContinuousLinearMap.hasFDerivAt).fderiv
  rw [map_zero] at this
  have e2 : fderiv ℂ (fun z => valAt' (e (F z)) U f) 0 = _ := this
  rw [e2]
  rfl

theorem deriv_smul {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ X}
    (h : IsDerivAt0 e w v) (c : ℂ) : IsDerivAt0 e (c • w) (spMap (epsScale c) ≫ v) := by
  rw [isDerivAt0_iff] at h ⊢
  have e0 : spMap fstC ≫ spMap (epsScale c) ≫ v = spMap fstC ≫ v := by
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun r => TrivSqZeroExt.fst_map _ r
  refine ⟨e0.trans h.1, fun U hU f => ?_⟩
  have hv : ⊤ ≤ v ⁻¹ᵁ U := (top_le_preimage_iff v U).2 (e0 ▸ (top_le_preimage_iff _ U).1 hU)
  rw [evalPt_spMap_comp _ v U hv hU, map_smul, ← h.2 U hv f]
  simp [epsScale]

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S}

abbrev epsTwo (y : Sp ℂ ⟶ S) : Over S := Over.mk (spMap (algebraMap ℂ (TrivSqZeroExt ℂ (ℂ × ℂ))) ≫ y)

def toTwo (y : Sp ℂ ⟶ S) (l : ℂ →ₗ[ℂ] ℂ × ℂ) : epsTwo y ⟶ epsPt y :=
  Over.homMk (spMap (TrivSqZeroExt.map l).toRingHom) (by
    change _ ≫ _ ≫ y = _ ≫ y
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun r => (TrivSqZeroExt.map l).commutes r)

def ofTwo (y : Sp ℂ ⟶ S) (l : ℂ × ℂ →ₗ[ℂ] ℂ) : epsPt y ⟶ epsTwo y :=
  Over.homMk (spMap (TrivSqZeroExt.map l).toRingHom) (by
    change _ ≫ _ ≫ y = _ ≫ y
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun r => (TrivSqZeroExt.map l).commutes r)

theorem ofTwo_toTwo (l : ℂ →ₗ[ℂ] ℂ × ℂ) (l' : ℂ × ℂ →ₗ[ℂ] ℂ) :
    ofTwo y l' ≫ toTwo y l = epsPtScale y (l' (l 1)) := by
  refine Over.OverMorphism.ext ?_
  change spMap _ ≫ spMap _ = spMap _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun x => ?_
  have : l' (l x.snd) = l' (l 1) * x.snd := by
    rw [mul_comm, ← smul_eq_mul, ← map_smul, ← map_smul, smul_eq_mul, _root_.mul_one]
  ext <;> simp [this, epsScale]

theorem epsPtScale_one : epsPtScale y 1 = 𝟙 _ := by
  refine Over.OverMorphism.ext ?_
  change spMap _ = 𝟙 _
  rw [← Spec.map_id]
  congr 1
  ext x <;> simp [epsScale]

theorem epsPtScale_zero {v : epsPt y ⟶ G} (hv : epsPtZero y ≫ v = 1) : epsPtScale y 0 ≫ v = 1 := by
  let s : epsPt y ⟶ Over.mk y := Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl
  have : epsPtScale y 0 = s ≫ epsPtZero y := by
    refine Over.OverMorphism.ext ?_
    change spMap _ = spMap _ ≫ spMap _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun x => ?_
    ext <;> simp [epsScale, TrivSqZeroExt.algebraMap_eq_inl]
  rw [this, Category.assoc, hv, MonObj.comp_one]

theorem deriv_mul {e : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)} {w w' : Fin g → ℂ} {v v' : epsPt y ⟶ G}
    (h0 : e 0 = (1 : Over.mk y ⟶ G).left)
    (h : IsDerivAt0 e w v.left) (h' : IsDerivAt0 e w' v'.left) : IsDerivAt0 e (w + w') (v * v').left := by
  have hv : epsPtZero y ≫ v = 1 := Over.OverMorphism.ext (h.1.trans h0)
  have hv' : epsPtZero y ≫ v' = 1 := Over.OverMorphism.ext (h'.1.trans h0)
  have hm : epsPtZero y ≫ (v * v') = 1 := by rw [MonObj.comp_mul, hv, hv', _root_.mul_one]
  have hm' : spMap fstC ≫ (v * v').left = e 0 := (congrArg (·.left) hm).trans h0.symm
  rw [isDerivAt0_iff] at h h' ⊢
  refine ⟨hm', fun U hU f => ?_⟩
  let u : epsTwo y ⟶ G := (toTwo y (LinearMap.inl ℂ ℂ ℂ) ≫ v) * (toTwo y (LinearMap.inr ℂ ℂ ℂ) ≫ v')
  have hu : ∀ l, ofTwo y l ≫ u = (epsPtScale y (l (1, 0)) ≫ v) * (epsPtScale y (l (0, 1)) ≫ v') := fun l => by
    simp only [u, MonObj.comp_mul, ← Category.assoc, ofTwo_toTwo]
    rfl
  have h1 : ofTwo y (LinearMap.fst ℂ ℂ ℂ) ≫ u = v := by
    rw [hu, LinearMap.fst_apply, LinearMap.fst_apply, epsPtScale_one, epsPtScale_zero hv', _root_.mul_one, Category.id_comp]
  have h2 : ofTwo y (LinearMap.snd ℂ ℂ ℂ) ≫ u = v' := by
    rw [hu, LinearMap.snd_apply, LinearMap.snd_apply, epsPtScale_one, epsPtScale_zero hv, _root_.one_mul, Category.id_comp]
  have h3 : ofTwo y (LinearMap.fst ℂ ℂ ℂ + LinearMap.snd ℂ ℂ ℂ) ≫ u = v * v' := by
    rw [hu]; simp [epsPtScale_one]
  have hU0 : ⊤ ≤ e 0 ⁻¹ᵁ U := hm' ▸ (top_le_preimage_iff _ U).1 hU
  have hU1 : ⊤ ≤ v.left ⁻¹ᵁ U := (top_le_preimage_iff _ U).2 (h.1 ▸ hU0)
  have hU2 : ⊤ ≤ v'.left ⁻¹ᵁ U := (top_le_preimage_iff _ U).2 (h'.1 ▸ hU0)
  have hsub : ∀ p q : PrimeSpectrum (TrivSqZeroExt ℂ (ℂ × ℂ)), p = q := by
    have k : ∀ z : PrimeSpectrum (TrivSqZeroExt ℂ (ℂ × ℂ)), ∀ a, a ∈ z.asIdeal ↔ a.fst = 0 := fun z a => by
      constructor
      · intro ha
        by_contra h0
        exact z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
      · intro ha
        refine z.2.mem_of_pow_mem 2 ?_
        rw [show a ^ 2 = 0 by ext <;> simp [pow_two, ha]]
        exact z.asIdeal.zero_mem
    intro p q
    ext a
    rw [k, k]
  have hUu : ⊤ ≤ u.left ⁻¹ᵁ U := fun p _ => by
    let q : (epsPt y).left := spMap fstC (default : PrimeSpectrum ℂ)
    have hq : v.left q ∈ U := hU1 (Set.mem_univ q)
    rw [← h1] at hq
    rw [hsub p ((ofTwo y (LinearMap.fst ℂ ℂ ℂ)).left q)]
    exact hq
  have key : ∀ (l : ℂ × ℂ →ₗ[ℂ] ℂ) (x : epsPt y ⟶ G) (hx : ⊤ ≤ x.left ⁻¹ᵁ U), ofTwo y l ≫ u = x →
      (evalPt (R := DualNumber ℂ) x.left U hx f).snd =
        l (evalPt (R := TrivSqZeroExt ℂ (ℂ × ℂ)) u.left U hUu f).snd := by
    rintro l x hx rfl
    exact (congrArg TrivSqZeroExt.snd (evalPt_spMap_comp (TrivSqZeroExt.map l).toRingHom u.left U hUu hx f)).trans
      (TrivSqZeroExt.snd_map _ _)
  rw [map_add (f := _), ← h.2 U hU1 f, ← h'.2 U hU2 f, key _ _ hU h3, key _ _ hU1 h1, key _ _ hU2 h2]
  rfl

end Deriv

end GlobalTheory.PointUnif
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfSurjectiveAppTopOfSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

theorem eq_one_of_surjective_appTop_of_section {X S : Scheme.{0}} (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
    (hs : Function.Surjective p.appTop.hom) (a : Γ(X, ⊤)) (ha : o.appTop.hom a = 1) : a = 1 := by
  obtain ⟨b, rfl⟩ := hs a
  have e : o.appTop.hom (p.appTop.hom b) = b := by
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, ho, Scheme.Hom.id_appTop]
    rfl
  rw [e.symm.trans ha, map_one]

theorem exists_sabMap_of_isProper_of_lbIso : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (φ : t'.G.left ⟶ t.G.left), IsProper t.G.hom → IsGrpPullback t'.G t.G f φ → LBIso t'.PP.L (t.PP.L.pull φ) → (∀ a, (t'.act.act a).left ≫ φ = φ ≫ (t.act.act a).left) → ∃ m : SABMap t' t f, m.φ = φ := by
  intro hG E _ _ _ H S S' t t' f φ hp gp ⟨w, hw⟩ hact
  obtain ⟨w', hw', Hr⟩ := TripleMap.exists_rigidified t.PP.isLB t'.PP.isLB w ((isGen_iff w).1 hw) (eSec t.G)
    (eSec t'.G) t'.G.hom (Over.w _) f (cubeMapOf gp).e_comm t.PP.rig t.PP.rigGen t'.PP.rig t'.PP.rigGen
  have hp' : IsProper t'.G.hom := MorphismProperty.of_isPullback gp.1 hp
  have hA := AbelianSchemeGerms.isAbelianScheme_of_proper t'.G t'.semi
  have hA₃ := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA)
  refine ⟨⟨cubeMapOf gp, gp, rfl, hact, (isPullCubical_iff _ _ _).2 ⟨w', hw', Hr,
    TripleMap.pmaps_cubical gp t.cub t'.cub hw' fun a ha => ?_⟩⟩, rfl⟩
  let o := lift (1 : 𝟙_ (Over S') ⟶ t'.G) (lift (1 : 𝟙_ (Over S') ⟶ t'.G) (1 : 𝟙_ (Over S') ⟶ t'.G))
  have h₁ : pullU o.left ⊤ a = 1 := unit_ext fun y _ =>
    (gm_pull (𝟙 _) o.left y ⊤ trivial a).trans ((congrArg (fun q => gm q y ⊤ a) (Category.id_comp _)).trans
      ((ha y).trans (map_one _).symm))
  exact Units.ext (eq_one_of_surjective_appTop_of_section (G3 t'.G).hom o.left (Over.w o) (hG _ _ hA₃).2 a.val
    (congrArg Units.val h₁))

end GlobalTheory
end
