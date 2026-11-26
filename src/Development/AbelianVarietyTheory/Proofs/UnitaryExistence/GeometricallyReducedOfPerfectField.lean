module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EqZeroOfForallLTensorEqZero
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteOfIsClosedTorusZariskiOfPowEqOne
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ReducedSubgroup

section Cat

variable {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞]

theorem exists_grpObj_of_mono {N B : 𝒞} [GrpObj B] (ν : N ⟶ B) [Mono ν] (e : 𝟙_ 𝒞 ⟶ N)
    (m : N ⊗ N ⟶ N) (i : N ⟶ N) (he : e ≫ ν = η[B]) (hm : m ≫ ν = (ν ⊗ₘ ν) ≫ μ[B])
    (hi : i ≫ ν = ν ≫ GrpObj.inv) : ∃ _ : GrpObj N, IsMonHom ν := by
  have hl : ∀ {T : 𝒞} (a b : T ⟶ N), lift a b ≫ m ≫ ν = (a ≫ ν) * (b ≫ ν) := by
    intro T a b
    rw [hm, lift_map_assoc, Hom.mul_def]
  have hm' : m ≫ ν = (fst N N ≫ ν) * (snd N N ≫ ν) := by
    rw [← hl, lift_fst_snd, Category.id_comp]
  have he' : ∀ {T : 𝒞} (a : T ⟶ 𝟙_ 𝒞), a ≫ e ≫ ν = 1 := by
    intro T a
    rw [he, Hom.one_def, toUnit_unique a (toUnit T)]
  have hi' : i ≫ ν = ν⁻¹ := by rw [hi, Hom.inv_def]
  letI M : MonObj N :=
    { one := e
      mul := m
      one_mul := by
        rw [← cancel_mono ν, Category.assoc, hm', comp_mul, whiskerRight_fst_assoc,
          whiskerRight_snd_assoc, he', _root_.one_mul, leftUnitor_hom]
      mul_one := by
        rw [← cancel_mono ν, Category.assoc, hm', comp_mul, whiskerLeft_fst_assoc,
          whiskerLeft_snd_assoc, he', _root_.mul_one, rightUnitor_hom]
      mul_assoc := by
        rw [← cancel_mono ν]
        simp only [Category.assoc]
        conv_lhs => rw [hm', comp_mul, whiskerRight_fst_assoc, whiskerRight_snd_assoc, hm',
          comp_mul]
        conv_rhs => rw [hm', comp_mul, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, hm',
          comp_mul, comp_mul, comp_mul]
        simp [_root_.mul_assoc] }
  refine ⟨{ inv := i, left_inv := ?_, right_inv := ?_ }, ⟨he, hm⟩⟩
  · rw [← cancel_mono ν, Category.assoc, Category.assoc]
    exact (hl i (𝟙 N)).trans (by rw [hi', Category.id_comp, inv_mul_cancel]; exact (he' _).symm)
  · rw [← cancel_mono ν, Category.assoc, Category.assoc]
    exact (hl (𝟙 N) i).trans (by rw [hi', Category.id_comp, mul_inv_cancel]; exact (he' _).symm)

end Cat

section Reduced

universe u


open Scheme.IdealSheafData in
theorem isReduced_subscheme_vanishingIdeal {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X) :
    IsReduced (vanishingIdeal Z).subscheme := by
  have : ∀ U, IsReduced ((vanishingIdeal Z).subschemeCover.openCover.X U) := fun U => by
    refine (affine_isReduced_iff (.of (Γ(X, U.1) ⧸ (vanishingIdeal Z).ideal U))).mpr ?_
    refine (Ideal.isRadical_iff_quotient_reduced _).mp ?_
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  exact IsReduced.of_openCover _ (vanishingIdeal Z).subschemeCover.openCover


open Scheme.IdealSheafData in
theorem vanishingIdeal_le_ker {T X : Scheme.{u}} [IsReduced T] (g : T ⟶ X)
    (Z : TopologicalSpace.Closeds X) (h : Set.range g ⊆ Z) : vanishingIdeal Z ≤ g.ker := by
  refine le_ofIdeals_iff.mpr fun U a ha => ?_
  rw [RingHom.mem_ker, ← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen, eq_bot_iff]
  intro t ht
  have h1 : g t ∈ (vanishingIdeal Z).support := h ⟨t, rfl⟩
  have h2 := ((coe_support_inter (vanishingIdeal Z) U).le
    ⟨h1, X.basicOpen_le a ht⟩).1
  exact ((Scheme.mem_zeroLocus_iff _ _ _).mp h2 a ha ht).elim

theorem geometricallyReduced_of_perfectField {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsReduced X] (f : X ⟶ Spec (.of k)) : GeometricallyReduced f := by
  refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr fun K _ _ => ?_⟩
  let 𝒰 := Scheme.Pullback.openCoverOfLeft X.affineOpenCover.openCover f
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have : ∀ i, IsReduced (𝒰.X i) := fun i => by
    have := X.affineOpenCover.map_prop i
    have h0 : IsReduced (Spec (X.affineOpenCover.X i)) :=
      isReduced_of_isOpenImmersion (X.affineOpenCover.f i)
    have h1 := (affine_isReduced_iff _).mp h0
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.affineOpenCover.f i ≫ f)
    change IsReduced (pullback (X.affineOpenCover.f i ≫ f) _)
    rw [← hφ]
    letI : Algebra k (X.affineOpenCover.X i) := φ.hom.toAlgebra
    have h2 := ReducedAlg.isReduced_tensor (k := k) (X.affineOpenCover.X i) K
    have h3 := (affine_isReduced_iff
      (.of (TensorProduct k (X.affineOpenCover.X i) K))).mpr h2
    exact isReduced_of_isOpenImmersion (pullbackSpecIso k (X.affineOpenCover.X i) K).hom
  exact IsReduced.of_openCover _ 𝒰

end Reduced

theorem range_subset_of_points {k : Type} [Field k] [IsAlgClosed k] {T B : Over (Sp k)}
    [LocallyOfFiniteType T.hom] (g : T ⟶ B) {Z : Set B.left} (hZ : IsClosed Z)
    (h : ∀ x : 𝟙_ (Over (Sp k)) ⟶ T, Set.range (x ≫ g).left ⊆ Z) : Set.range g.left ⊆ Z := by
  have := LocallyOfFiniteType.jacobsonSpace T.hom
  rintro _ ⟨t, rfl⟩
  by_contra ht
  obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints (Z := (g.left ⁻¹' Z)ᶜ) ⟨t, ht⟩
    (hZ.preimage g.left.continuous).isOpen_compl.isLocallyClosed
  let x' : 𝟙_ (Over (Sp k)) ⟶ T :=
    Over.homMk (pointOfClosedPoint T.hom x hxc) (pointOfClosedPoint_comp T.hom x hxc)
  refine hx (h x' ⟨IsLocalRing.closedPoint k, ?_⟩)
  exact congrArg g.left (pointOfClosedPoint_apply T.hom x hxc _)


open Scheme.IdealSheafData in
theorem exists_smooth_closed_subgroup (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k))
    [GrpObj B] (hB : LocallyOfFiniteType B.hom) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B))
    (Z : Set B.left) (hZ : IsClosed Z) (hC : ∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) :
    ∃ (N : Over (Sp k)) (_ : GrpObj N) (ν : N ⟶ B), IsMonHom ν ∧ IsClosedImmersion ν.left ∧
      Smooth N.hom ∧ Set.range ν.left = Z := by
  let I : B.left.IdealSheafData := vanishingIdeal ⟨Z, hZ⟩
  let N : Over (Sp k) := Over.mk (I.subschemeι ≫ B.hom)
  let ν : N ⟶ B := Over.homMk I.subschemeι rfl
  have hν : IsClosedImmersion ν.left := inferInstanceAs (IsClosedImmersion I.subschemeι)
  have hr : Set.range ν.left = Z := by
    change Set.range I.subschemeι = Z
    rw [range_subschemeι]
    rfl
  have : Mono ν := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono ν.left))
  have hred : IsReduced N.left := isReduced_subscheme_vanishingIdeal _
  have hft : LocallyOfFiniteType N.hom :=
    inferInstanceAs (LocallyOfFiniteType (I.subschemeι ≫ B.hom))
  have hgr : GeometricallyReduced N.hom := geometricallyReduced_of_perfectField N.hom
  have hnoeth : IsLocallyNoetherian N.left := LocallyOfFiniteType.isLocallyNoetherian N.hom
  have hlift : ∀ {T : Over (Sp k)} [IsReduced T.left] [LocallyOfFiniteType T.hom] (g : T ⟶ B),
      (∀ x : 𝟙_ (Over (Sp k)) ⟶ T, x ≫ g ∈ C) → ∃ l : T ⟶ N, l ≫ ν = g := by
    intro T _ _ g hg
    have h1 := range_subset_of_points g hZ fun x => (hC _).mp (hg x)
    have h2 : I.subschemeι.ker ≤ g.left.ker := by
      rw [ker_subschemeι]
      exact vanishingIdeal_le_ker g.left ⟨Z, hZ⟩ h1
    have h3 := IsClosedImmersion.lift_fac I.subschemeι g.left h2
    refine ⟨Over.homMk (IsClosedImmersion.lift I.subschemeι g.left h2) ?_, ?_⟩
    · change _ ≫ I.subschemeι ≫ B.hom = _
      rw [← Category.assoc, h3, Over.w]
    · ext1
      exact h3
  have hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, x ≫ ν ∈ C := fun x => by
    rw [hC, ← hr]
    rintro _ ⟨t, rfl⟩
    exact ⟨x.left t, rfl⟩
  have : IsReduced (𝟙_ (Over (Sp k))).left := inferInstanceAs (IsReduced (Sp k))
  have : LocallyOfFiniteType (𝟙_ (Over (Sp k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Sp k)))
  have : IsReduced (N ⊗ N).left := inferInstanceAs (IsReduced (pullback N.hom N.hom))
  have : LocallyOfFiniteType (N ⊗ N).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst N.hom N.hom ≫ N.hom))
  obtain ⟨e, he⟩ := hlift η[B] fun x => by
    rw [toUnit_unique x (toUnit _), ← Hom.one_def]
    exact C.one_mem
  obtain ⟨m, hm⟩ := hlift ((ν ⊗ₘ ν) ≫ μ[B]) fun x => by
    have : x ≫ (ν ⊗ₘ ν) ≫ μ[B] = ((x ≫ fst N N) ≫ ν) * ((x ≫ snd N N) ≫ ν) := by
      rw [Hom.mul_def, ← lift_map, Category.assoc, ← comp_lift, lift_fst_snd, Category.comp_id]
    rw [this]
    exact C.mul_mem (hmem _) (hmem _)
  obtain ⟨i, hi⟩ := hlift (ν ≫ GrpObj.inv) fun x => by
    rw [← Category.assoc, ← Hom.inv_def]
    exact C.inv_mem (hmem _)
  obtain ⟨G, hG⟩ := exists_grpObj_of_mono ν e m i he hm hi
  refine ⟨N, G, ν, hG, hν, ?_, hr⟩
  letI : GrpObj (Over.mk N.hom) := G
  exact smooth_of_grpObj N.hom

end GlobalTheory.ReducedSubgroup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem finite_of_finite_sections {Ω : Type} [Field Ω] [IsAlgClosed Ω] {P : Scheme.{0}}
    (s : P ⟶ Spec (.of Ω)) [LocallyOfFiniteType s]
    (h : Finite {x : Spec (.of Ω) ⟶ P // x ≫ s = 𝟙 _}) : Finite P := by
  have hJ : JacobsonSpace P := LocallyOfFiniteType.jacobsonSpace s
  have hc : (closedPoints P).Finite := by
    have : Finite (closedPoints P) := Finite.of_equiv _ (pointEquivClosedPoint s)
    exact Set.toFinite _
  have hcl : IsClosed (closedPoints P) := by
    rw [← Set.biUnion_of_singleton (closedPoints P)]
    exact hc.isClosed_biUnion fun x hx ↦ hx
  have hu : closedPoints P = Set.univ := by
    have := JacobsonSpace.closure_inter_closedPoints (X := P) isClosed_univ
    rwa [Set.univ_inter, hcl.closure_eq] at this
  exact Set.finite_univ_iff.mp (hu ▸ hc)

theorem locallyQuasiFinite_of_finite_geometric_points {X Y : Scheme.{0}} (f : X ⟶ Y)
    [LocallyOfFiniteType f]
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y),
      Finite {x : Spec (.of Ω) ⟶ X // x ≫ f = y}) : LocallyQuasiFinite f := by
  refine LocallyQuasiFinite.of_finite_preimage_singleton f fun y ↦ ?_
  let Ω := AlgebraicClosure (Y.residueField y)
  let y' : Spec (.of Ω) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)) ≫ Y.fromSpecResidueField y
  have hy : y ∈ Set.range y' := by
    obtain ⟨z⟩ : Nonempty ↥(Spec (.of Ω)) := inferInstance
    exact ⟨z, (Scheme.Hom.comp_apply _ _ z).trans (Scheme.fromSpecResidueField_apply y _)⟩
  clear_value y'
  have := h Ω y'
  have hP : Finite ↥(pullback f y') := by
    refine finite_of_finite_sections (pullback.snd f y') ?_
    refine Finite.of_injective (β := {x : Spec (.of Ω) ⟶ X // x ≫ f = y'})
      (fun x ↦ ⟨x.1 ≫ pullback.fst f y', by
        rw [Category.assoc, pullback.condition, ← Category.assoc, x.2, Category.id_comp]⟩) ?_
    intro a b hab
    apply Subtype.ext
    apply pullback.hom_ext
    · exact congrArg Subtype.val hab
    · rw [a.2, b.2]
  refine (Set.finite_range (pullback.fst f y')).subset ?_
  rw [Scheme.Pullback.range_fst]
  exact Set.preimage_mono (Set.singleton_subset_iff.mpr hy)

theorem finite_fiber_of_finite_ker {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {Ga G T : C} [GrpObj Ga] [GrpObj G] (p : Ga ⟶ G) [IsMonHom p]
    (h : Finite {x : T ⟶ Ga // x ≫ p = 1}) (y : T ⟶ G) :
    Finite {x : T ⟶ Ga // x ≫ p = y} := by
  rcases isEmpty_or_nonempty {x : T ⟶ Ga // x ≫ p = y} with he | ⟨⟨x₀, hx₀⟩⟩
  · infer_instance
  refine Finite.of_injective (β := {x : T ⟶ Ga // x ≫ p = 1})
    (fun x ↦ ⟨x₀⁻¹ * x.1, by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hx₀, x.2, inv_mul_cancel]⟩) ?_
  intro a b hab
  exact Subtype.ext (mul_left_cancel (congrArg Subtype.val hab))

theorem locallyQuasiFinite_of_finite_geometric_ker :
    ∀ (S : Scheme.{0}) (Ga G : Over S) [GrpObj Ga] [GrpObj G] (p : Ga ⟶ G), IsMonHom p →
      LocallyOfFiniteType p.left → QuasiCompact p.left →
      (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S),
        Finite {x : Over.mk t ⟶ Ga // x ≫ p = 1}) → LocallyQuasiFinite p.left := by
  intro S Ga G _ _ p hp hft _ h
  refine locallyQuasiFinite_of_finite_geometric_points p.left fun Ω _ _ y ↦ ?_
  let y' : Over.mk (y ≫ G.hom) ⟶ G := Over.homMk y rfl
  have := finite_fiber_of_finite_ker p (h Ω (y ≫ G.hom)) y'
  refine Finite.of_injective (β := {x : Over.mk (y ≫ G.hom) ⟶ Ga // x ≫ p = y'})
    (fun x ↦ ⟨Over.homMk x.1 (by
      change x.1 ≫ Ga.hom = y ≫ G.hom
      rw [← Over.w p, ← Category.assoc, x.2]), Over.OverMorphism.ext x.2⟩) ?_
  intro a b hab
  exact Subtype.ext (congrArg (fun z ↦ z.1.left) hab)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOneOfPowEqOneOfCompEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.KernelNoTorsion

theorem eq_of_isSchemeTheoreticallyDominant {X S Y Z : Scheme.{0}} (f : X ⟶ S) [IsSeparated f]
    {a b : Y ⟶ X} (hab : a ≫ f = b ≫ f) (j : Z ⟶ Y) [IsSchemeTheoreticallyDominant j]
    (hj : j ≫ a = j ≫ b) : a = b := by
  have := GlobalTheory.isClosedImmersion_equalizer_ι_of_isSeparated f hab
  have hk : (equalizer.ι a b).ker = ⊥ := by
    have h := Scheme.Hom.le_ker_comp (equalizer.lift j hj) (equalizer.ι a b)
    rw [equalizer.lift_ι, j.ker_eq_bot] at h
    exact le_bot_iff.mp h
  have : IsIso (equalizer.ι a b) := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hk
  rw [← cancel_epi (equalizer.ι a b), equalizer.condition]

theorem eq_of_generic (T K : Type) [CommRing T] [IsDomain T] [Field K] [Algebra T K]
    [IsFractionRing T K] {Y X : Over (Sp T)} [Flat Y.hom] [IsSeparated X.hom] {a b : Y ⟶ X}
    (h : (Over.pullback (spMap (algebraMap T K))).map a =
      (Over.pullback (spMap (algebraMap T K))).map b) : a = b := by
  have : IsDominant (spMap (algebraMap T K)) := by
    rw [isDominant_iff]
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap T K)).mpr ?_
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective T K)]
    exact bot_le
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap T K))
  apply Over.OverMorphism.ext
  refine eq_of_isSchemeTheoreticallyDominant X.hom ((Over.w a).trans (Over.w b).symm)
    (pullback.fst Y.hom (spMap (algebraMap T K))) ?_
  have h' := congr(($h).left ≫ pullback.fst X.hom (spMap (algebraMap T K)))
  exact (pullback.lift_fst _ _ _).symm.trans (h'.trans (pullback.lift_fst _ _ _))

theorem comp_mulN {S : Scheme.{0}} {Y G : Over S} [GrpObj G] (x : Y ⟶ G) (n : ℕ) :
    x ≫ mulN G n = x ^ n := by
  induction n with
  | zero => rw [pow_zero, mulN, Hom.one_def, comp_toUnit_assoc]
  | succ n ih => rw [pow_succ, mulN, Hom.mul_def, comp_lift_assoc, ih, Category.comp_id]

noncomputable def torsionLift {S : Scheme.{0}} {Y G : Over S} [GrpObj G] {n : ℕ} (x : Y ⟶ G)
    (hx : x ^ n = 1) : Y ⟶ torsion G n :=
  pullback.lift x (toUnit Y) (by rw [comp_mulN, hx, Hom.one_def])

theorem torsionLift_ι {S : Scheme.{0}} {Y G : Over S} [GrpObj G] {n : ℕ} (x : Y ⟶ G)
    (hx : x ^ n = 1) : torsionLift x hx ≫ torsion.ι G n = x :=
  pullback.lift_fst _ _ _

theorem torsion_hom_ext {S : Scheme.{0}} {Y G : Over S} [GrpObj G] {n : ℕ}
    {a b : Y ⟶ torsion G n} (h : a ≫ torsion.ι G n = b ≫ torsion.ι G n) : a = b :=
  pullback.hom_ext h (toUnit_unique _ _)

theorem torsionι_pow {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) :
    torsion.ι G n ^ n = 1 := by
  rw [← comp_mulN, Hom.one_def]
  refine (pullback.condition).trans ?_
  congr 1
  exact toUnit_unique _ _

theorem eq_one_of_pow_eq_one_of_comp_eq_one :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (Ga G : Over (Sp T)) [GrpObj Ga] [GrpObj G] [IsCommMonObj Ga] [IsCommMonObj G] (p : Ga ⟶ G) (n : ℕ), IsMonHom p → IsSeparated Ga.hom → Etale (torsion Ga n).hom → Etale (torsion G n).hom → IsIso ((Over.pullback (spMap (algebraMap T K))).map p) → ∀ (Y : Over (Sp T)) (x : Y ⟶ Ga), x ^ n = 1 → x ≫ p = 1 → x = 1 := by
  intro T K _ _ _ _ _ _ Ga G _ _ _ _ p n hp hsep hA hB hiso Y x hx hxp
  have hq : (torsion.ι Ga n ≫ p) ^ n = 1 := by
    rw [← MonObj.pow_comp, torsionι_pow, MonObj.one_comp]
  let q : torsion Ga n ⟶ torsion G n := torsionLift _ hq
  let e : torsion Ga n ⟶ torsion G n := torsionLift 1 (one_pow n)
  have hopen := GlobalTheory.isOpenImmersion_equalizer_ι_left_of_unramified q e
  have hflat : Flat (equalizer q e).hom := by
    rw [← Over.w (equalizer.ι q e)]
    infer_instance
  have h1 : (equalizer.ι q e ≫ torsion.ι Ga n) ≫ p = (1 : equalizer q e ⟶ Ga) ≫ p := by
    have := equalizer.condition q e =≫ torsion.ι G n
    rw [Category.assoc, Category.assoc, torsionLift_ι, torsionLift_ι, MonObj.comp_one] at this
    rw [Category.assoc, this, MonObj.one_comp]
  have h2 : equalizer.ι q e ≫ torsion.ι Ga n = 1 := by
    apply eq_of_generic T K
    rw [← cancel_mono ((Over.pullback (spMap (algebraMap T K))).map p), ← Functor.map_comp,
      ← Functor.map_comp, h1]
  have h3 : torsionLift x hx ≫ q = torsionLift x hx ≫ e := by
    apply torsion_hom_ext
    rw [Category.assoc, Category.assoc, torsionLift_ι, torsionLift_ι, MonObj.comp_one,
      ← Category.assoc, torsionLift_ι, hxp]
  rw [← torsionLift_ι x hx, ← equalizer.lift_ι (torsionLift x hx) h3, Category.assoc, h2,
    MonObj.comp_one]

end GlobalTheory.KernelNoTorsion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfSchemeTheoreticallyDominant
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_lift_of_schemeTheoreticallyDominant {W Y X Z : Scheme.{0}} (φ : W ⟶ Y)
    [IsSchemeTheoreticallyDominant φ] (i : Z ⟶ X) [IsClosedImmersion i] (a : Y ⟶ X) (c : W ⟶ Z)
    (h : c ≫ i = φ ≫ a) : ∃ b : Y ⟶ Z, b ≫ i = a := by
  have H : i.ker ≤ a.ker := by
    have h1 : i.ker ≤ (c ≫ i).ker := Scheme.Hom.le_ker_comp c i
    rwa [h, ← Scheme.IdealSheafData.map_ker, φ.ker_eq_bot, Scheme.IdealSheafData.map_bot] at h1
  exact ⟨IsClosedImmersion.lift i a H, IsClosedImmersion.lift_fac i a H⟩

theorem over_ext_of_schemeTheoreticallyDominant {S W : Scheme.{0}} {Y X : Over S}
    [IsSeparated X.hom] (φ : W ⟶ Y.left) [IsSchemeTheoreticallyDominant φ] {a b : Y ⟶ X}
    (h : φ ≫ a.left = φ ≫ b.left) : a = b := by
  have hY : a.left ≫ X.hom = b.left ≫ X.hom := by rw [Over.w a, Over.w b]
  let e : Y.left ⟶ pullback X.hom X.hom := pullback.lift a.left b.left hY
  have he1 : e ≫ pullback.fst X.hom X.hom = a.left := pullback.lift_fst _ _ _
  have he2 : e ≫ pullback.snd X.hom X.hom = b.left := pullback.lift_snd _ _ _
  have hc : (φ ≫ a.left) ≫ pullback.diagonal X.hom = φ ≫ e := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [pullback.diagonal_fst, he1, Category.comp_id]
    · simp only [Category.assoc]
      rw [pullback.diagonal_snd, he2, Category.comp_id, h]
  have hs2 : pullback.lift (φ ≫ a.left) φ hc ≫ pullback.snd (pullback.diagonal X.hom) e = φ :=
    pullback.lift_snd _ _ _
  obtain ⟨s, hs⟩ := exists_lift_of_schemeTheoreticallyDominant φ
    (pullback.snd (pullback.diagonal X.hom) e) (𝟙 _) (pullback.lift _ _ hc)
    (by rw [hs2, Category.comp_id])
  have key : ∀ g : pullback X.hom X.hom ⟶ X.left, e ≫ g =
      s ≫ pullback.fst (pullback.diagonal X.hom) e ≫ pullback.diagonal X.hom ≫ g := by
    intro g
    rw [pullback.condition_assoc, ← Category.assoc s, hs, Category.id_comp]
  have ha := key (pullback.fst X.hom X.hom)
  have hb := key (pullback.snd X.hom X.hom)
  rw [he1, pullback.diagonal_fst, Category.comp_id] at ha
  rw [he2, pullback.diagonal_snd, Category.comp_id] at hb
  exact Over.OverMorphism.ext (ha.trans hb.symm)

section

variable {S S' : Scheme.{0}} (f : S' ⟶ S) [IsSchemeTheoreticallyDominant f] [QuasiCompact f]

theorem pullback_map_injective_of_flat {Y X : Over S} [Flat Y.hom] [IsSeparated X.hom]
    {a b : Y ⟶ X} (h : (Over.pullback f).map a = (Over.pullback f).map b) : a = b := by
  apply over_ext_of_schemeTheoreticallyDominant (pullback.fst Y.hom f)
  have ka : ((Over.pullback f).map a).left ≫ pullback.fst X.hom f = pullback.fst Y.hom f ≫ a.left :=
    pullback.lift_fst _ _ _
  have kb : ((Over.pullback f).map b).left ≫ pullback.fst X.hom f = pullback.fst Y.hom f ≫ b.left :=
    pullback.lift_fst _ _ _
  rw [← ka, ← kb, h]

theorem existsUnique_lift_of_flat {Y X Z : Over S} (i : Z ⟶ X) (a : Y ⟶ X)
    (a' : (Over.pullback f).obj Y ⟶ (Over.pullback f).obj Z) [Flat Y.hom]
    [IsClosedImmersion i.left] (h : a' ≫ (Over.pullback f).map i = (Over.pullback f).map a) :
    ∃! b : Y ⟶ Z, b ≫ i = a ∧ (Over.pullback f).map b = a' := by
  have ki : ((Over.pullback f).map i).left ≫ pullback.fst X.hom f = pullback.fst Z.hom f ≫ i.left :=
    pullback.lift_fst _ _ _
  have ka : ((Over.pullback f).map a).left ≫ pullback.fst X.hom f = pullback.fst Y.hom f ≫ a.left :=
    pullback.lift_fst _ _ _
  have hc : (a'.left ≫ pullback.fst Z.hom f) ≫ i.left = pullback.fst Y.hom f ≫ a.left := by
    rw [Category.assoc, ← ki, ← ka, ← h, Over.comp_left, Category.assoc]
  obtain ⟨b₀, hb₀⟩ := exists_lift_of_schemeTheoreticallyDominant (pullback.fst Y.hom f) i.left
    a.left (a'.left ≫ pullback.fst Z.hom f) hc
  have hw : b₀ ≫ Z.hom = Y.hom := by
    rw [← Over.w i, ← Category.assoc, hb₀, Over.w a]
  have kb1 : ((Over.pullback f).map (Over.homMk b₀ hw)).left ≫ pullback.fst Z.hom f =
      pullback.fst Y.hom f ≫ b₀ := pullback.lift_fst _ _ _
  have kb2 : ((Over.pullback f).map (Over.homMk b₀ hw)).left ≫ pullback.snd Z.hom f =
      pullback.snd Y.hom f := pullback.lift_snd _ _ _
  have h3 : a'.left ≫ pullback.snd Z.hom f = pullback.snd Y.hom f := Over.w a'
  refine ⟨Over.homMk b₀ hw, ⟨Over.OverMorphism.ext hb₀, ?_⟩, ?_⟩
  · apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [← cancel_mono i.left, kb1, Category.assoc, Category.assoc, hb₀, ← hc, Category.assoc]
    · rw [kb2, h3]
  · rintro b ⟨hb, -⟩
    apply Over.OverMorphism.ext
    rw [← cancel_mono i.left]
    have hb' := congrArg CommaMorphism.left hb
    exact hb'.trans hb₀.symm

theorem isMonHom_of_pullback_of_flat {G G' : Over S} [MonObj G] [MonObj G'] (F : G ⟶ G')
    [Flat G.hom] [IsSeparated G'.hom] [h : IsMonHom ((Over.pullback f).map F)] : IsMonHom F := by
  have h1 : Flat (𝟙_ (Over S)).hom := by
    change Flat (𝟙 S)
    infer_instance
  have h2 : Flat (G ⊗ G).hom := by
    change Flat (pullback.fst G.hom G.hom ≫ G.hom)
    infer_instance
  constructor
  · apply pullback_map_injective_of_flat f
    have := IsMonHom.one_hom ((Over.pullback f).map F)
    simp only [Functor.obj.η_def, Category.assoc] at this
    rw [Functor.map_comp]
    exact (cancel_epi _).1 this
  · apply pullback_map_injective_of_flat f
    have := IsMonHom.mul_hom ((Over.pullback f).map F)
    simp only [Functor.obj.μ_def, Category.assoc] at this
    rw [Functor.LaxMonoidal.μ_natural_assoc] at this
    rw [Functor.map_comp, Functor.map_comp]
    exact (cancel_epi _).1 this

end

theorem schemeTheoreticallyDominant_fractionField (T K : Type) [CommRing T] [IsDomain T] [Field K]
    [Algebra T K] [IsFractionRing T K] :
    IsSchemeTheoreticallyDominant (spMap (algebraMap T K)) := by
  have hinj : Function.Injective (algebraMap T K) := IsFractionRing.injective T K
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap T K))
  have h : Function.Injective (spMap (algebraMap T K)).appTop := by
    intro x y hxy
    have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom hxy
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, e] at h2
    simp only at h2
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of T)).hom).1 (hinj h2)
  refine ⟨Scheme.IdealSheafData.ext_of_isAffine ?_⟩
  rw [Scheme.Hom.ker_apply _ ⟨⊤, isAffineOpen_top _⟩]
  simp only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  exact (RingHom.injective_iff_ker_eq_bot _).1 h

theorem flat_dvr_generic_fibre :
    (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (Y X : Over (Sp T)), Flat Y.hom → IsSeparated X.hom → ∀ a b : Y ⟶ X, (Over.pullback (spMap (algebraMap T K))).map a = (Over.pullback (spMap (algebraMap T K))).map b → a = b) ∧ (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (Y X Ga : Over (Sp T)) (io : Ga ⟶ X) (a : Y ⟶ X) (a' : (Over.pullback (spMap (algebraMap T K))).obj Y ⟶ (Over.pullback (spMap (algebraMap T K))).obj Ga), Flat Y.hom → IsClosedImmersion io.left → a' ≫ (Over.pullback (spMap (algebraMap T K))).map io = (Over.pullback (spMap (algebraMap T K))).map a → ∃! b : Y ⟶ Ga, b ≫ io = a ∧ (Over.pullback (spMap (algebraMap T K))).map b = a') ∧ (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'] (F : G ⟶ G'), Flat G.hom → IsSeparated G'.hom → IsMonHom ((Over.pullback (spMap (algebraMap T K))).map F) → IsMonHom F) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T K _ _ _ _ _ _ Y X hY hX a b h
    have := schemeTheoreticallyDominant_fractionField T K
    exact pullback_map_injective_of_flat (spMap (algebraMap T K)) h
  · intro T K _ _ _ _ _ _ Y X Ga io a a' hY hio h
    have := schemeTheoreticallyDominant_fractionField T K
    exact existsUnique_lift_of_flat (spMap (algebraMap T K)) io a a' h
  · intro T K _ _ _ _ _ _ G G' _ _ F hG hG' hF
    have := schemeTheoreticallyDominant_fractionField T K
    exact isMonHom_of_pullback_of_flat (spMap (algebraMap T K)) F

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RingHomFlatCodescendsAlongFaithfullyFlat
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem ringHom_flat_codescendsAlong_faithfullyFlat :
    RingHom.CodescendsAlong.{0} RingHom.Flat RingHom.FaithfullyFlat := by
  refine .mk _ RingHom.Flat.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [RingHom.flat_algebraMap_iff] at h' ⊢
  rw [RingHom.faithfullyFlat_algebraMap_iff] at h
  exact .of_flat_tensorProduct R T S

theorem flat_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@Flat : MorphismProperty Scheme.{0})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat ringHom_flat_codescendsAlong_faithfullyFlat

theorem isPullback_overPullback_map_left {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S}
    (φ : X ⟶ Y) :
    IsPullback ((Over.pullback f).map φ).left (pullback.fst X.hom f) (pullback.fst Y.hom f)
      φ.left := by
  refine IsPullback.flip (IsPullback.of_bot (v₂₁ := pullback.snd Y.hom f) (v₂₂ := Y.hom) (h₃₁ := f)
    ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback Y.hom f))
  have h₁ : ((Over.pullback f).map φ).left ≫ pullback.snd Y.hom f = pullback.snd X.hom f :=
    pullback.lift_snd _ _ _
  rw [h₁, Over.w φ]
  exact IsPullback.of_hasPullback X.hom f

theorem flat_of_flat_fieldBaseChange (k k' : Type) [Field k] [Field k'] (σ : k →+* k')
    (X Y : Over (Sp k)) (φ : X ⟶ Y)
    (h : Flat ((Over.pullback (spMap σ)).map φ).left) : Flat φ.left := by
  haveI := flat_descendsAlong_fpqc
  have h₁ : Flat (spMap σ) := inferInstance
  have h₂ : Surjective (spMap σ) := inferInstance
  have h₃ : QuasiCompact (spMap σ) := inferInstance
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (isPullback_overPullback_map_left (spMap σ) φ)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlatOfIsSchemeTheoreticallyDominantOfFractionRing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem ringHom_flat_of_injective_of_isUnit {T A B : Type*} [CommRing T] [IsDomain T] [IsBezout T]
    [CommRing A] [CommRing B] (φ : T →+* A) (ψ : A →+* B) (hψ : Function.Injective ψ)
    (h : ∀ t : T, t ≠ 0 → IsUnit (ψ (φ t))) : φ.Flat := by
  letI := φ.toAlgebra
  change Module.Flat T A
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro a ⟨⟨t, ht⟩, hta⟩
  have h1 : φ t * a = 0 := hta
  have h2 : ψ (φ t) * ψ a = 0 := by rw [← map_mul, h1, map_zero]
  have h3 : ψ a = 0 := (h t (nonZeroDivisors.ne_zero ht)).mul_right_eq_zero.mp h2
  exact hψ (by rw [h3, map_zero])

theorem isSchemeTheoreticallyDominant_toImage {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] :
    IsSchemeTheoreticallyDominant f.toImage := by
  rw [isSchemeTheoreticallyDominant_iff]
  have : QuasiCompact (f.toImage ≫ f.imageι) := by rw [f.toImage_imageι]; infer_instance
  have : QuasiCompact f.toImage := QuasiCompact.of_comp f.toImage f.imageι
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens ↦ ⟨f.imageι ⁻¹ᵁ U.1, U.2.preimage f.imageι⟩) ?_ ?_
  · have := f.imageι.preimage_iSup (fun U : Y.affineOpens ↦ U.1)
    rw [← this, iSup_affineOpens_eq_top]
    simp
  · intro U
    rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
      ← RingHom.injective_iff_ker_eq_bot]
    exact f.toImage_app_injective U

theorem flat_of_isSchemeTheoreticallyDominant_of_fractionRing (T K : Type) [CommRing T]
    [IsDomain T] [IsBezout T] [Field K] [Algebra T K] [IsFractionRing T K] {Z G : Scheme.{0}}
    (p : Z ⟶ G) [QuasiCompact p] [IsSchemeTheoreticallyDominant p] (s : G ⟶ Sp T) (z : Z ⟶ Sp K)
    (w : p ≫ s = z ≫ spMap (algebraMap T K)) : Flat s := by
  refine HasRingHomProperty.of_iSup_eq_top (P := @Flat) (fun U : G.affineOpens ↦ U)
    (iSup_affineOpens_eq_top G) fun U ↦ ?_
  have key : ((Scheme.ΓSpecIso (.of T)).inv ≫ s.appLE ⊤ U le_top) ≫ p.app U =
      CommRingCat.ofHom (algebraMap T K) ≫ (Scheme.ΓSpecIso (.of K)).inv ≫
        z.appLE ⊤ (p ⁻¹ᵁ U) le_top := by
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, Category.assoc, p.app_eq_appLE,
      Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    congr 1
    refine (Scheme.Hom.appLE_comp_appLE p s ⊤ U (p ⁻¹ᵁ U) _ _).trans
      (Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE z (spMap (algebraMap T K)) ⊤ ⊤ (p ⁻¹ᵁ U) _ _).symm)
    congr 1
  have hfl : ((Scheme.ΓSpecIso (.of T)).inv ≫ s.appLE ⊤ U le_top).hom.Flat := by
    refine ringHom_flat_of_injective_of_isUnit (T := T) _ (p.app U).hom (p.app_injective U) ?_
    intro t ht
    have h1 : IsUnit (algebraMap T K t) :=
      IsUnit.mk0 _ (by simpa using ht)
    have h2 := h1.map ((Scheme.ΓSpecIso (.of K)).inv ≫ z.appLE ⊤ (p ⁻¹ᵁ U) le_top).hom
    have h3 := congrArg (fun φ ↦ CommRingCat.Hom.hom φ t) key
    exact h3 ▸ h2
  exact (RingHom.Flat.respectsIso.cancel_left_isIso _ _).mp hfl

theorem exists_flat_closure : ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (X : Over (Sp T)) (Z : Over (Sp K)) (i : Z ⟶ (Over.pullback (spMap (algebraMap T K))).obj X), IsClosedImmersion i.left → ∃ (Ga : Over (Sp T)) (io : Ga ⟶ X) (e : (Over.pullback (spMap (algebraMap T K))).obj Ga ≅ Z), IsClosedImmersion io.left ∧ Flat Ga.hom ∧ e.hom ≫ i = (Over.pullback (spMap (algebraMap T K))).map io := by
  intro T K _ _ _ _ _ _ X Z i hi
  let j : Sp K ⟶ Sp T := spMap (algebraMap T K)
  have hjp : IsPreimmersion j := IsPreimmersion.of_isLocalization (nonZeroDivisors T)
  have hjf : Flat j := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors T))
  let i' : Z.left ⟶ pullback X.hom j := i.left
  have hi' : IsClosedImmersion i' := hi
  have hw : i' ≫ pullback.snd X.hom j = Z.hom := Over.w i
  let f : Z.left ⟶ X.left := i' ≫ pullback.fst X.hom j
  have hqc : QuasiCompact f := inferInstance
  have : QuasiCompact (f.toImage ≫ f.imageι) := by rw [f.toImage_imageι]; infer_instance
  have : QuasiCompact f.toImage := QuasiCompact.of_comp f.toImage f.imageι
  have hdom := isSchemeTheoreticallyDominant_toImage f
  have hsq : f.toImage ≫ (f.imageι ≫ X.hom) = Z.hom ≫ j := by
    rw [f.toImage_imageι_assoc, Category.assoc, pullback.condition, reassoc_of% hw]
  let Ga : Over (Sp T) := Over.mk (f.imageι ≫ X.hom)
  let io : Ga ⟶ X := Over.homMk f.imageι rfl
  let t : Z.left ⟶ pullback (f.imageι ≫ X.hom) j := pullback.lift f.toImage Z.hom hsq
  let m : pullback (f.imageι ≫ X.hom) j ⟶ pullback X.hom j :=
    pullback.map _ _ _ _ f.imageι (𝟙 _) (𝟙 _) (by simp) (by simp)
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion.{0} :=
    ⟨fun f g hf hg ↦ @IsClosedImmersion.comp _ _ _ f g hf hg⟩
  have hm : IsClosedImmersion m :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion.{0}) inferInstance inferInstance rfl (by simp)
  have htm : t ≫ m = i' := by
    apply pullback.hom_ext
    · simp [t, m, f, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp [t, m, hw, pullback.lift_snd]
  have : IsClosedImmersion (t ≫ m) := htm ▸ hi'
  have ht : IsClosedImmersion t := IsClosedImmersion.of_comp_isClosedImmersion t m
  have hpb : IsPullback (𝟙 Z.left) t f.toImage (pullback.fst (f.imageι ≫ X.hom) j) :=
    IsPullback.of_horiz_isIso_mono ⟨by simp [t, pullback.lift_fst]⟩
  have htd : IsSchemeTheoreticallyDominant t := .of_isPullback hpb
  have : IsIso t := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr t.ker_eq_bot
  refine ⟨Ga, io, (Over.isoMk (f := Z) (g := (Over.pullback j).obj Ga) (asIso t) ?_).symm,
    inferInstanceAs (IsClosedImmersion f.imageι),
    flat_of_isSchemeTheoreticallyDominant_of_fractionRing T K f.toImage _ Z.hom hsq, ?_⟩
  · exact pullback.lift_snd _ _ _
  · rw [Iso.symm_hom, Iso.inv_comp_eq]
    apply Over.OverMorphism.ext
    change i' = t ≫ _
    rw [← htm]
    congr 1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsClosedImageOfIsClosedSubgroup
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Topology

namespace GlobalTheory

namespace RationalPoint

variable {k : Type} [Field k]

noncomputable def pt {X : Over (Sp k)} (y : 𝟙_ (Over (Sp k)) ⟶ X) : X.left :=
  y.left (IsLocalRing.closedPoint k)

theorem range_left_subset_iff {X : Over (Sp k)} (y : 𝟙_ (Over (Sp k)) ⟶ X) (Z : Set X.left) :
    Set.range y.left ⊆ Z ↔ pt y ∈ Z := by
  refine ⟨fun h => h ⟨_, rfl⟩, fun h => ?_⟩
  rintro _ ⟨a, rfl⟩
  have : a = IsLocalRing.closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
  rw [this]
  exact h

theorem pt_comp {X Y : Over (Sp k)} (y : 𝟙_ (Over (Sp k)) ⟶ X) (f : X ⟶ Y) :
    pt (y ≫ f) = f.left (pt y) := rfl

@[reducible] noncomputable def zariski (X : Over (Sp k)) :
    TopologicalSpace (𝟙_ (Over (Sp k)) ⟶ X) :=
  TopologicalSpace.induced pt inferInstance

theorem continuous_comp {X Y : Over (Sp k)} (f : X ⟶ Y) :
    Continuous[zariski X, zariski Y] fun y => y ≫ f := by
  letI := zariski X
  letI := zariski Y
  exact continuous_induced_rng.2 (f.left.continuous.comp continuous_induced_dom)

theorem separatelyContinuousMul (B : Over (Sp k)) [GrpObj B] :
    @SeparatelyContinuousMul (𝟙_ (Over (Sp k)) ⟶ B) (zariski B) _ := by
  letI := zariski B
  have h : ∀ g y : 𝟙_ (Over (Sp k)) ⟶ B, y ≫ toUnit B ≫ g = g := fun g y => by
    rw [← Category.assoc, toUnit_unique (y ≫ toUnit B) (𝟙 _), Category.id_comp]
  refine ⟨fun {g} => ?_, fun {g} => ?_⟩
  · convert continuous_comp ((toUnit B ≫ g) * 𝟙 B) using 2 with y
    rw [MonObj.comp_mul, h, Category.comp_id]
  · convert continuous_comp (𝟙 B * (toUnit B ≫ g)) using 2 with y
    rw [MonObj.comp_mul, h, Category.comp_id]

theorem continuousInv (B : Over (Sp k)) [GrpObj B] :
    @ContinuousInv (𝟙_ (Over (Sp k)) ⟶ B) (zariski B) _ := by
  letI := zariski B
  refine ⟨?_⟩
  convert continuous_comp (𝟙 B)⁻¹ using 2 with y
  rw [GrpObj.comp_inv, Category.comp_id]

variable [IsAlgClosed k]

theorem isClosed_pt {X : Over (Sp k)} [LocallyOfFiniteType X.hom] (y : 𝟙_ (Over (Sp k)) ⟶ X) :
    IsClosed {pt y} :=
  (pointEquivClosedPoint X.hom ⟨y.left, Over.w y⟩).2

theorem pt_injective {X : Over (Sp k)} [LocallyOfFiniteType X.hom] :
    Function.Injective (pt : (𝟙_ (Over (Sp k)) ⟶ X) → X.left) := fun x y h =>
  Over.OverMorphism.ext (ext_of_apply_closedPoint_eq X.hom (Over.w x) (Over.w y) h)

theorem exists_pt_mem {X : Over (Sp k)} [LocallyOfFiniteType X.hom] {Z : Set X.left}
    (hZ : IsClosed Z) (hne : Z.Nonempty) : ∃ x : 𝟙_ (Over (Sp k)) ⟶ X, pt x ∈ Z := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨c, hcZ, hc⟩ := nonempty_inter_closedPoints hne hZ.isLocallyClosed
  replace hc : IsClosed {c} := hc
  refine ⟨Over.homMk (pointOfClosedPoint X.hom c hc) (pointOfClosedPoint_comp X.hom c hc), ?_⟩
  have : pt (Over.homMk (pointOfClosedPoint X.hom c hc) (pointOfClosedPoint_comp X.hom c hc) :
      𝟙_ (Over (Sp k)) ⟶ X) = c := pointOfClosedPoint_apply X.hom c hc _
  rwa [this]

theorem pt_mem_image_iff {X Y : Over (Sp k)} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) {Z : Set X.left} (hZ : IsClosed Z)
    (y : 𝟙_ (Over (Sp k)) ⟶ Y) :
    pt y ∈ f.left '' Z ↔ ∃ x : 𝟙_ (Over (Sp k)) ⟶ X, pt x ∈ Z ∧ x ≫ f = y := by
  constructor
  · rintro ⟨z, hz, hzy⟩
    obtain ⟨x, hx, hxy⟩ := exists_pt_mem (Z := Z ∩ f.left ⁻¹' {pt y})
      (hZ.inter ((isClosed_pt y).preimage f.left.continuous)) ⟨z, hz, hzy⟩
    exact ⟨x, hx, pt_injective hxy⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨pt x, hx, rfl⟩


omit [IsAlgClosed k] in
theorem isConstructible_image_of_isClosed {X Y : Over (Sp k)} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (f : X ⟶ Y)
    {Z : Set X.left} (hZ : IsClosed Z) : IsConstructible (f.left '' Z) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsNoetherian X.left := {}
  have : IsNoetherian Y.left := {}
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  have : LocallyOfFinitePresentation f.left := inferInstance
  have : QuasiCompact f.left := inferInstance
  refine f.left.isConstructible_image ?_
  exact ((TopologicalSpace.NoetherianSpace.isCompact Zᶜ).isConstructible hZ.isOpen_compl).of_compl

end RationalPoint


open RationalPoint in
theorem exists_isClosed_image_of_isClosed_subgroup :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (G B : Over (Sp k)) [GrpObj G] [GrpObj B] (q : G ⟶ B), IsMonHom q → LocallyOfFiniteType G.hom → QuasiCompact G.hom → LocallyOfFiniteType B.hom → QuasiCompact B.hom → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)) (Z : Set G.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → ∃ Z' : Set B.left, IsClosed Z' ∧ ∀ y : (𝟙_ (Over (Sp k)) ⟶ B), (∃ x ∈ C, x ≫ q = y) ↔ Set.range y.left ⊆ Z' := by
  intro k _ _ G B _ _ q _ _ _ _ _ C Z hZ hC
  letI := RationalPoint.zariski B
  haveI := RationalPoint.separatelyContinuousMul B
  haveI := RationalPoint.continuousInv B
  let φ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ B) :=
    MonoidHom.mk' (fun x => x ≫ q) fun x y => MonObj.mul_comp x y q
  have hcl : IsClosed (C.map φ : Set (𝟙_ (Over (Sp k)) ⟶ B)) := by
    refine isClosed_subgroup_of_eq_preimage_isConstructible _ (f := RationalPoint.pt)
      continuous_induced_dom (RationalPoint.isConstructible_image_of_isClosed q hZ) ?_
    ext y
    rw [Set.mem_preimage, RationalPoint.pt_mem_image_iff q hZ]
    simp only [← RationalPoint.range_left_subset_iff, ← hC]
    rfl
  obtain ⟨Z', hZ', h⟩ := isClosed_induced_iff.1 hcl
  refine ⟨Z', hZ', fun y => ?_⟩
  rw [RationalPoint.range_left_subset_iff, ← Set.mem_preimage, h]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralAndIsNormalSchemeOfSmoothDvr
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem isDominant_spMap_of_isFractionRing (T K : Type) [CommRing T] [IsDomain T] [Field K]
    [Algebra T K] [IsFractionRing T K] : IsDominant (spMap (algebraMap T K)) := by
  refine ⟨?_⟩
  change DenseRange (PrimeSpectrum.comap (algebraMap T K))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective T K)]
  exact bot_le

theorem isDominant_genericFibre_of_flat (T K : Type) [CommRing T] [IsDomain T] [Field K]
    [Algebra T K] [IsFractionRing T K] {X : Scheme.{0}} (f : X ⟶ Sp T) [Flat f] :
    IsDominant (pullback.fst f (spMap (algebraMap T K))) := by
  have := isDominant_spMap_of_isFractionRing T K
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap T K))
  infer_instance

theorem connectedSpace_of_flat_of_genericFibre (T K : Type) [CommRing T] [IsDomain T] [Field K]
    [Algebra T K] [IsFractionRing T K] {X : Scheme.{0}} (f : X ⟶ Sp T) [Flat f]
    [ConnectedSpace ↥(pullback f (spMap (algebraMap T K)))] : ConnectedSpace X := by
  have := isDominant_genericFibre_of_flat T K f
  let g := pullback.fst f (spMap (algebraMap T K))
  have h : _root_.IsConnected (closure (Set.range g)) := (isConnected_range g.continuous).closure
  rw [g.denseRange.closure_range] at h
  exact connectedSpace_iff_univ.mpr h

theorem isIntegral_and_isNormalScheme_of_smooth (T K : Type) [CommRing T] [IsDomain T]
    [IsNoetherianRing T] [IsIntegrallyClosed T] [Field K] [Algebra T K] [IsFractionRing T K]
    {X : Scheme.{0}} (f : X ⟶ Sp T) [Smooth f]
    [ConnectedSpace ↥(pullback f (spMap (algebraMap T K)))] :
    IsIntegral X ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X := by
  have hT : GlobalTheory.IsNormalScheme (Sp T) := inferInstance
  have hX : GlobalTheory.IsNormalScheme X := (isNormalScheme_iff X).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth f ((isNormalScheme_iff _).mp hT))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := connectedSpace_of_flat_of_genericFibre T K f
  exact ⟨IsNormalScheme.isIntegral_of_connectedSpace X, hX.pred X⟩

theorem isIntegral_and_isNormalScheme_of_smooth_dvr :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
      [IsFractionRing T K] (G : Over (Sp T)), Smooth G.hom →
      ConnectedSpace ((Over.pullback (spMap (algebraMap T K))).obj G).left →
      IsIntegral G.left ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme G.left := by
  intro T K _ _ _ _ _ _ G hG hc
  have : ConnectedSpace ↥(pullback G.hom (spMap (algebraMap T K))) := hc
  exact isIntegral_and_isNormalScheme_of_smooth T K G.hom

end GlobalTheory
end
