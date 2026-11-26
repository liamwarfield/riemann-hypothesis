module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlatOfFormallyUnramifiedGrpEnd
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlatOfFlatFibresDvr
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsUnitNatCastSections
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace MulEtaleDvr

variable {S : Scheme.{0}}

theorem mulN_eq_pow (G : Over S) [GrpObj G] (n : ℕ) : mulN G n = 𝟙 G ^ n := by
  rw [← MulUnramified.comp_mulN, Category.id_comp]

theorem isMonHom_mulN (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) : IsMonHom (mulN G n) := by
  constructor
  · rw [MulUnramified.comp_mulN, one_eq_one, one_pow]
  · simp only [MulUnramified.comp_mulN, MonObj.mul_eq_mul, MonObj.comp_mul,
      tensorHom_fst, tensorHom_snd, mul_pow]

theorem pullback_map_mulN {S' : Scheme.{0}} (p : S' ⟶ S) (G : Over S) [GrpObj G] (n : ℕ) :
    (Over.pullback p).map (mulN G n) = mulN ((Over.pullback p).obj G) n := by
  rw [mulN_eq_pow, mulN_eq_pow, ← (Over.pullback p).map_id]
  exact map_pow (Over.pullback p).homMonoidHom _ _

theorem isPullback_torsion (G : Over S) [GrpObj G] (n : ℕ) :
    IsPullback (torsion.ι G n).left (torsion G n).hom (mulN G n).left η[G].left := by
  have h := (IsPullback.of_hasPullback (mulN G n) (η : 𝟙_ (Over S) ⟶ G)).map (Over.forget S)
  have e : (pullback.snd (mulN G n) (η : 𝟙_ (Over S) ⟶ G)).left = (torsion G n).hom :=
    (Category.comp_id _).symm.trans (Over.w (pullback.snd (mulN G n) (η : 𝟙_ (Over S) ⟶ G)))
  exact e ▸ h

theorem isUnit_natCast_sections {R : Type} [CommRing R] {n : ℕ} (hn : IsUnit (n : R)) :
    IsUnit (n : Γ(Sp R, ⊤)) := by
  simpa using hn.map (Scheme.ΓSpecIso (.of R)).inv.hom

theorem flat_mulN_field (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (n : ℕ)
    (hn : IsUnit (n : k)) (hG : LocallyOfFiniteType G.hom) : Flat (mulN G n).left := by
  refine flat_of_flat_fieldBaseChange k (AlgebraicClosure k) (algebraMap _ _) G G _ ?_
  rw [pullback_map_mulN]
  refine flat_of_formallyUnramified_grpEnd _ _ _ ?_ (isMonHom_mulN _ n)
    (formallyUnramified_mulN _ _ n (isUnit_natCast_sections ?_))
  · exact inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom _))
  · simpa using hn.map (algebraMap k (AlgebraicClosure k))

theorem flat_pullback_mulN {T k : Type} [CommRing T] [Field k] (σ : T →+* k) (G : Over (Sp T))
    [GrpObj G] [IsCommMonObj G] (n : ℕ) (hn : IsUnit (n : T)) (hG : LocallyOfFiniteType G.hom) :
    Flat ((Over.pullback (spMap σ)).map (mulN G n)).left := by
  rw [pullback_map_mulN]
  refine flat_mulN_field k _ n (by simpa using hn.map σ) ?_
  exact inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom _))

end MulEtaleDvr


open MulEtaleDvr in
theorem etale_mulN_torsion_dvr :
    ∀ (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] (G : Over (Sp T)) [GrpObj G]
      [IsCommMonObj G] (n : ℕ), IsUnit (n : T) → Flat G.hom → LocallyOfFiniteType G.hom →
      Etale (mulN G n).left ∧ Etale (torsion G n).hom := by
  intro T _ _ _ G _ _ n hn hf hG
  have h1 : Flat (mulN G n).left :=
    flat_of_flat_fibres_dvr T (FractionRing T) G G _ hf hf hG hG
      (MulEtaleDvr.flat_pullback_mulN _ G n hn hG) (MulEtaleDvr.flat_pullback_mulN _ G n hn hG)
  have h2 := formallyUnramified_mulN _ G n (MulEtaleDvr.isUnit_natCast_sections hn)
  have h3 : LocallyOfFiniteType ((mulN G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have h4 := locallyOfFiniteType_of_comp (mulN G n).left G.hom
  have h5 : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have h6 : LocallyOfFinitePresentation (mulN G n).left := inferInstance
  have h : Etale (mulN G n).left := Etale.of_formallyUnramified_of_flat _
  exact ⟨h, MorphismProperty.of_isPullback (P := @Etale) (MulEtaleDvr.isPullback_torsion G n) h⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenImmersionSpMapOfIsDiscreteValuationRing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem isOpenImmersion_spMap_of_isDiscreteValuationRing (T K : Type) [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] :
    IsOpenImmersion (spMap (algebraMap T K)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T
  have : IsLocalization.Away π K := by
    refine IsLocalization.Away.mk π (IsUnit.mk0 _ (by simpa using hπ.ne_zero)) (fun s => ?_)
      (fun a b hab => ⟨0, by simpa using IsFractionRing.injective T K hab⟩)
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := T) s
    obtain ⟨n, v, rfl⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hπ
    refine ⟨n, a * (v⁻¹ : Tˣ), ?_⟩
    have h1 : algebraMap T K π ≠ 0 := by simpa using hπ.ne_zero
    have h2 : algebraMap T K v ≠ 0 := by simp
    simp only [map_mul, map_pow, map_units_inv]
    field_simp
  exact IsOpenImmersion.of_isLocalization π

theorem isIntegral_of_flat_of_isIntegral_genericFibre (T K : Type) [CommRing T] [IsDomain T]
    [Field K] [Algebra T K] [IsFractionRing T K] {X : Scheme.{0}} (f : X ⟶ Sp T) [Flat f]
    [IsIntegral (pullback f (spMap (algebraMap T K)))] : IsIntegral X := by
  have := isDominant_spMap_of_isFractionRing T K
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap T K))
  let g := pullback.fst f (spMap (algebraMap T K))
  have : IsReduced X := IsSchemeTheoreticallyDominant.isReduced g
  have : IsDominant g := inferInstance
  have h : IsIrreducible (closure (Set.range g)) := by
    rw [← Set.image_univ]
    exact ((IrreducibleSpace.isIrreducible_univ _).image g g.continuous.continuousOn).closure
  rw [g.denseRange.closure_range] at h
  have : IrreducibleSpace X := (irreducibleSpace_def X).mpr h
  exact isIntegral_of_irreducibleSpace_of_isReduced X

theorem isIso_of_quasiFinite_of_isIso_genericFibre_dvr :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
      [IsFractionRing T K] (Ga G : Over (Sp T)) [GrpObj Ga] [GrpObj G] (p : Ga ⟶ G), IsMonHom p →
      Flat Ga.hom → IsSeparated p.left → LocallyOfFiniteType p.left → QuasiCompact p.left →
      LocallyQuasiFinite p.left → Smooth G.hom → GeometricallyConnected G.hom →
      IsIso ((Over.pullback (spMap (algebraMap T K))).map p) → IsIso p := by
  intro T K _ _ _ _ _ _ Ga G _ _ p _ _ _ _ _ _ _ _ _
  let t := spMap (algebraMap T K)
  have : IsOpenImmersion t := isOpenImmersion_spMap_of_isDiscreteValuationRing T K
  have hc : ConnectedSpace ((Over.pullback t).obj G).left :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback G.hom t)
  obtain ⟨hG, hN⟩ := isIntegral_and_isNormalScheme_of_smooth_dvr T K G ‹_› hc
  let q : pullback Ga.hom t ⟶ pullback G.hom t := ((Over.pullback t).map p).left
  have : IsIso q := inferInstanceAs (IsIso ((Over.forget _).map ((Over.pullback t).map p)))
  have e : q ≫ pullback.fst G.hom t = pullback.fst Ga.hom t ≫ p.left := pullback.lift_fst _ _ _
  have : ConnectedSpace ↥(pullback G.hom t) := hc
  have : IsIntegral (pullback G.hom t) := isIntegral_of_isOpenImmersion (pullback.fst G.hom t)
  have : Nonempty ↥(pullback Ga.hom t) := ⟨inv q (Classical.arbitrary _)⟩
  have : IsIntegral (pullback Ga.hom t) := isIntegral_of_isOpenImmersion q
  have : IsIntegral Ga.left := isIntegral_of_flat_of_isIntegral_genericFibre T K Ga.hom
  let j := pullback.fst Ga.hom t
  have : IsOpenImmersion (j.opensRange.ι ≫ p.left) := by
    rw [← j.isoOpensRange_inv_comp, Category.assoc, ← e]
    infer_instance
  have : IsOpenImmersion p.left :=
    isOpenImmersion_of_quasiFinite_of_isOpenImmersion_restrict p.left (fun y ↦ (hN y).2)
      j.opensRange ⟨⟨j (Classical.arbitrary _), _, rfl⟩⟩
  exact isIso_of_isOpenImmersion_of_geometricallyConnected _ Ga G p ‹_› ‹_› inferInstance ‹_›

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGrpObjOfFlatClosed
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

section

universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

theorem exists_grpObj_of_mono {H G : C} [GrpObj G] (j : H ⟶ G) [Mono j]
    (o : 𝟙_ C ⟶ H) (m : H ⊗ H ⟶ H) (n : H ⟶ H) (ho : o ≫ j = η[G])
    (hm : m ≫ j = (j ⊗ₘ j) ≫ μ[G]) (hn : n ≫ j = j ≫ GrpObj.inv) :
    ∃ _ : GrpObj H, IsMonHom j := by
  letI M : MonObj H :=
    { one := o
      mul := m
      one_mul := by
        rw [← cancel_mono j, Category.assoc, hm, ← tensorHom_id, tensorHom_comp_tensorHom_assoc, ho,
          Category.id_comp, tensorHom_def', Category.assoc, MonObj.one_mul, leftUnitor_naturality]
      mul_one := by
        rw [← cancel_mono j, Category.assoc, hm, ← id_tensorHom, tensorHom_comp_tensorHom_assoc, ho,
          Category.id_comp, MonoidalCategory.tensorHom_def, Category.assoc, MonObj.mul_one, rightUnitor_naturality]
      mul_assoc := by
        rw [← cancel_mono j]
        simp only [Category.assoc, hm]
        rw [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
          tensorHom_comp_tensorHom_assoc, hm, Category.id_comp]
        have h1 : ((j ⊗ₘ j) ≫ μ[G] ⊗ₘ j) = ((j ⊗ₘ j) ⊗ₘ j) ≫ μ[G] ▷ G := by
          rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
        have h2 : (j ⊗ₘ (j ⊗ₘ j) ≫ μ[G]) = (j ⊗ₘ (j ⊗ₘ j)) ≫ G ◁ μ[G] := by
          rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
        rw [h1, h2, Category.assoc, Category.assoc, MonObj.mul_assoc, associator_naturality_assoc] }
  refine ⟨{ inv := n, left_inv := ?_, right_inv := ?_ }, ⟨ho, hm⟩⟩
  · rw [← cancel_mono j]
    change (lift n (𝟙 H) ≫ m) ≫ j = (toUnit H ≫ o) ≫ j
    rw [Category.assoc, hm, lift_map_assoc, hn, Category.assoc, ho, Category.id_comp]
    have := j ≫= GrpObj.left_inv G
    rw [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc] at this
    exact this
  · rw [← cancel_mono j]
    change (lift (𝟙 H) n ≫ m) ≫ j = (toUnit H ≫ o) ≫ j
    rw [Category.assoc, hm, lift_map_assoc, hn, Category.assoc, ho, Category.id_comp]
    have := j ≫= GrpObj.right_inv G
    rw [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc] at this
    exact this

theorem isMonHom_of_comp_mono {A B D : C} [MonObj A] [MonObj B] [MonObj D] (e : A ⟶ B) (i : B ⟶ D)
    [Mono i] [IsMonHom i] [h : IsMonHom (e ≫ i)] : IsMonHom e := by
  constructor
  · rw [← cancel_mono i, Category.assoc, h.one_hom, IsMonHom.one_hom]
  · rw [← cancel_mono i, Category.assoc, h.mul_hom, Category.assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc]

theorem isCommMonObj_of_mono [BraidedCategory C] {H G : C} [MonObj H] [MonObj G] (j : H ⟶ G)
    [Mono j] [IsMonHom j] [IsCommMonObj G] : IsCommMonObj H := by
  constructor
  rw [← cancel_mono j, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
    IsCommMonObj.mul_comm]

end

theorem exists_grpObj_of_flat_closed {S S' : Scheme.{0}} (f : S' ⟶ S)
    [IsSchemeTheoreticallyDominant f] [QuasiCompact f] (P Ga : Over S) [GrpObj P] (io : Ga ⟶ P)
    (Z : Over S') [GrpObj Z] (i : Z ⟶ (Over.pullback f).obj P) (e : (Over.pullback f).obj Ga ≅ Z)
    [IsClosedImmersion io.left] [Flat Ga.hom] [hi : IsMonHom i]
    (h : e.hom ≫ i = (Over.pullback f).map io) :
    ∃ _ : GrpObj Ga, IsMonHom io ∧ IsMonHom e.hom ∧ (IsCommMonObj P → IsCommMonObj Ga) := by
  have h1 : Flat (𝟙_ (Over S)).hom := inferInstanceAs (Flat (𝟙 S))
  have h2 : Flat (Ga ⊗ Ga).hom := inferInstanceAs (Flat (pullback.fst Ga.hom Ga.hom ≫ Ga.hom))
  have hm : Mono io := (Over.forget S).mono_of_mono_map (inferInstanceAs (Mono io.left))
  have hm' : Mono ((Over.pullback f).map io) := inferInstance
  have h' : e.inv ≫ (Over.pullback f).map io = i := by rw [← h, e.inv_hom_id_assoc]
  have hmi : Mono i := by rw [← h']; infer_instance
  obtain ⟨o, ⟨ho, -⟩, -⟩ := existsUnique_lift_of_flat f io η[P]
    (Functor.OplaxMonoidal.η (Over.pullback f) ≫ η[Z] ≫ e.inv) (by
      rw [Category.assoc, Category.assoc, h', hi.one_hom, Functor.obj.η_def,
        Functor.Monoidal.η_ε_assoc])
  obtain ⟨m, ⟨hm, -⟩, -⟩ := existsUnique_lift_of_flat f io ((io ⊗ₘ io) ≫ μ[P])
    (Functor.OplaxMonoidal.δ (Over.pullback f) Ga Ga ≫ (e.hom ⊗ₘ e.hom) ≫ μ[Z] ≫ e.inv) (by
      simp only [Category.assoc]
      rw [h', hi.mul_hom, tensorHom_comp_tensorHom_assoc, h, Functor.obj.μ_def,
        Functor.LaxMonoidal.μ_natural_assoc, Functor.Monoidal.δ_μ_assoc, Functor.map_comp])
  obtain ⟨n, ⟨hn, -⟩, -⟩ := existsUnique_lift_of_flat f io (io ≫ GrpObj.inv)
    (e.hom ≫ GrpObj.inv ≫ e.inv) (by
      simp only [Category.assoc]
      rw [h', GrpObj.inv_hom, ← Category.assoc, h, Functor.obj.ι_def, Functor.map_comp])
  obtain ⟨G, hG⟩ := exists_grpObj_of_mono io o m n ho hm hn
  refine ⟨G, hG, ?_, fun _ => isCommMonObj_of_mono io⟩
  have : IsMonHom (e.hom ≫ i) := by rw [h]; infer_instance
  exact isMonHom_of_comp_mono e.hom i

theorem flat_closure_subgroup :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (P Ga : Over (Sp T)) [GrpObj P] (io : Ga ⟶ P) (Z : Over (Sp K)) [GrpObj Z] (i : Z ⟶ (Over.pullback (spMap (algebraMap T K))).obj P) (e : (Over.pullback (spMap (algebraMap T K))).obj Ga ≅ Z), IsClosedImmersion io.left → Flat Ga.hom → IsMonHom i → e.hom ≫ i = (Over.pullback (spMap (algebraMap T K))).map io → ∃ _ : GrpObj Ga, IsMonHom io ∧ IsMonHom e.hom ∧ (IsCommMonObj P → IsCommMonObj Ga) := by
  intro T K _ _ _ _ _ _ P Ga _ io Z _ i e _ _ _ h
  have := schemeTheoreticallyDominant_fractionField T K
  exact exists_grpObj_of_flat_closed _ P Ga io Z i e h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteOfIsClosedTorusExtensionOfPowEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem map_eq_one_of_pow_eq_one_of_finite_ker {H B : Type*} [Group H] [Group B] (φ : H →* B)
    [Finite φ.ker] {n : ℕ} (hn : n.Prime) (h : ∀ x : H, x ^ n = 1 → x = 1) (y : H)
    (hy : φ y ^ n = 1) : φ y = 1 := by
  have hmem : y ^ n ∈ φ.ker := by rw [MonoidHom.mem_ker, map_pow, hy]
  have h1 : IsOfFinOrder (y ^ n) :=
    φ.ker.subtype.isOfFinOrder (isOfFinOrder_of_finite (⟨y ^ n, hmem⟩ : φ.ker))
  have h2 : IsOfFinOrder y := h1.of_pow hn.ne_zero
  have h3 : ¬ n ∣ orderOf y := by
    rintro ⟨m, hm⟩
    have h4 : y ^ m = 1 := h _ (by rw [← pow_mul, mul_comm, ← hm, pow_orderOf_eq_one])
    have h5 := orderOf_dvd_of_pow_eq_one h4
    have h6 := h2.orderOf_pos
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp [hm] at h6)
    have h7 := Nat.le_of_dvd hm0 h5
    have h8 := hn.two_le
    nlinarith
  have h9 : orderOf (φ y) ∣ Nat.gcd n (orderOf y) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hy) (orderOf_map_dvd φ y)
  rw [(hn.coprime_iff_not_dvd.2 h3).gcd_eq_one] at h9
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h9)


open RationalPoint in
theorem finite_of_isClosed_torusExtension_of_pow_eq_one :
    (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (n : ℕ), IsAbelianScheme B → n.Prime → (n : k) ≠ 0 → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C) → ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (n : ℕ), LocallyOfFiniteType G.hom → QuasiCompact G.hom → Nonempty (TorusExtension G) → n.Prime → (n : k) ≠ 0 → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)) (Z : Set G.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C := by
  intro hab k _ _ G _ _ n _ _ ⟨E⟩ hp hn C Z hZ hC htors
  letI := E.addCommGroup
  letI := E.free
  letI := E.finite
  letI := E.grpB
  haveI := E.q_hom
  haveI := E.i_hom
  haveI := E.isAbelian.proper
  let φ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ E.B) :=
    MonoidHom.mk' (fun x => x ≫ E.q) fun x y => MonObj.mul_comp x y E.q
  let j : (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) E.X) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    MonoidHom.mk' (fun x => x ≫ E.i) fun x y => MonObj.mul_comp x y E.i
  have hj : Function.Injective j := fun x y hxy =>
    E.isKernel.hom_ext hxy (toUnit_unique _ _)
  have hker : ∀ x, φ x = 1 → ∃ t, j t = x := fun x hx =>
    ⟨E.isKernel.lift x (toUnit _) hx, E.isKernel.lift_fst _ _ _⟩
  have hT : Finite (C.comap j) := by
    refine finite_of_isClosed_splitTorus_of_pow_eq_one k E.X n hp hn _ (E.i.left ⁻¹' Z)
      (hZ.preimage E.i.left.continuous) (fun x => ?_) fun x hx h1 => ?_
    · rw [Subgroup.mem_comap, hC, range_left_subset_iff, range_left_subset_iff]
      rfl
    · exact hj (by rw [map_one]; exact htors _ hx (by rw [← map_pow, h1, map_one]))
  let ψ : C →* (𝟙_ (Over (Sp k)) ⟶ E.B) := φ.comp C.subtype
  have hK : Finite ψ.ker := by
    choose s hs using fun x : ψ.ker => hker x.1.1 x.2
    refine Finite.of_injective
      (fun x : ψ.ker => (⟨s x, by rw [Subgroup.mem_comap, hs]; exact x.1.2⟩ : C.comap j))
      fun x y hxy => ?_
    have := congrArg (fun t : C.comap j => j t.1) hxy
    simp only [hs] at this
    exact Subtype.ext (Subtype.ext this)
  obtain ⟨Z', hZ', h'⟩ := exists_isClosed_image_of_isClosed_subgroup k G E.B E.q inferInstance
    inferInstance inferInstance inferInstance inferInstance C Z hZ hC
  have hR : Finite ψ.range := by
    refine hab k E.B n E.isAbelian hp hn _ Z' hZ' (fun y => ?_) ?_
    · rw [← h']
      exact ⟨fun ⟨x, hx⟩ => ⟨x.1, x.2, hx⟩, fun ⟨x, hx, hy⟩ => ⟨⟨x, hx⟩, hy⟩⟩
    · rintro _ ⟨y, rfl⟩ hy
      exact map_eq_one_of_pow_eq_one_of_finite_ker ψ hp
        (fun x hx => Subtype.ext (htors x.1 x.2 (congrArg Subtype.val hx))) y hy
  exact (MonoidHom.finite_iff_finite_ker_range ψ).2 ⟨hK, hR⟩

end GlobalTheory
end
