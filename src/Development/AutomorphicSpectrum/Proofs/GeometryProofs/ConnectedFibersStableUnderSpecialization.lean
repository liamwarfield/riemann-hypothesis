module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExpDerivativeLie

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedOfGenericFiberSmoothProper
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedOfCommGroupNsmulSurjective
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConnectedSpaceOfDivisible
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem eq_one_of_divisible {P Q : Type*} [CommGroup P] [Finite Q] (c : P → Q)
    (hc : ∀ a b t : P, c a = c b → c (a * t) = c (b * t))
    (hd : ∀ n : ℕ, n ≠ 0 → ∀ x : P, ∃ y : P, y ^ n = x) (x : P) : c x = c 1 := by
  let H : Subgroup P :=
    { carrier := {a | c a = c 1}
      one_mem' := rfl
      mul_mem' := fun {a b} ha hb => by
        have := hc a 1 b ha
        rw [_root_.one_mul] at this
        exact this.trans hb
      inv_mem' := fun {a} ha => by
        have := hc a 1 a⁻¹ ha
        rw [_root_.mul_inv_cancel, _root_.one_mul] at this
        exact this.symm }
  have hinj : Function.Injective (fun q : P ⧸ H => c q.out) := by
    intro q r hqr
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' r, QuotientGroup.eq]
    have := hc _ _ (q.out)⁻¹ hqr
    simp only [mul_inv_cancel] at this
    change c _ = c 1
    rw [mul_comm, this.symm]
  have : Finite (P ⧸ H) := Finite.of_injective _ hinj
  have hi : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain ⟨y, rfl⟩ := hd _ hi x
  exact Subgroup.pow_index_mem H y

theorem connectedSpace_of_divisible : ∀ (K : Type) [Field K] [IsAlgClosed K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G], LocallyOfFiniteType G.hom → QuasiCompact G.hom → (∀ n : ℕ, n ≠ 0 → ∀ x : 𝟙_ (Over (Sp K)) ⟶ G, ∃ y : 𝟙_ (Over (Sp K)) ⟶ G, y ^ n = x) → ConnectedSpace G.left := by
  intro K _ _ G _ _ hl hq hd
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : IsNoetherian G.left := {}
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  let pt : (𝟙_ (Over (Sp K))).left := IsLocalRing.closedPoint K
  let F : (𝟙_ (Over (Sp K)) ⟶ G) → G.left := fun x => x.left pt
  have hopen : ∀ x : G.left, IsOpen (connectedComponent x) :=
    fun x => isOpen_connectedComponent_of_noetherianSpace x
  have : DiscreteTopology (_root_.ConnectedComponents G.left) :=
    ConnectedComponents.discreteTopology_iff.2 hopen
  have : Finite (_root_.ConnectedComponents G.left) := finite_of_compact_of_discrete
  let c : (𝟙_ (Over (Sp K)) ⟶ G) → _root_.ConnectedComponents G.left := fun x => F x
  have htr : ∀ a t : 𝟙_ (Over (Sp K)) ⟶ G,
      F (a * t) = (GrpObj.mulRight t).hom.left (F a) := by
    intro a t
    have h : a ≫ (GrpObj.mulRight t).hom = a * t := by
      simp [comp_lift_assoc, Hom.mul_def]
    simp only [F, ← h, Over.comp_left, Scheme.Hom.comp_apply]
  have hc : ∀ a b t, c a = c b → c (a * t) = c (b * t) := by
    intro a b t hab
    have := congrArg (Continuous.connectedComponentsMap (GrpObj.mulRight t).hom.left.continuous) hab
    simpa [c, htr] using this
  have hall := eq_one_of_divisible c hc hd
  have hsurj : ∀ x : G.left, IsClosed {x} → ∃ a, F a = x := by
    intro x hx
    refine ⟨Over.homMk (pointOfClosedPoint G.hom x hx) (pointOfClosedPoint_comp G.hom x hx), ?_⟩
    exact pointOfClosedPoint_apply G.hom x hx _
  have huniv : connectedComponent (F 1) = Set.univ := by
    by_contra hne
    obtain ⟨x, hx, hcl⟩ := nonempty_inter_closedPoints (Set.nonempty_compl.2 hne)
      (IsOpen.isLocallyClosed isClosed_connectedComponent.isOpen_compl)
    obtain ⟨a, rfl⟩ := hsurj x hcl
    apply hx
    have h1 : connectedComponent (F a) = connectedComponent (F 1) :=
      ConnectedComponents.coe_eq_coe.1 (hall a)
    rw [← h1]
    exact mem_connectedComponent
  exact connectedSpace_iff_connectedComponent.2 ⟨F 1, huniv⟩

end GlobalTheory.CompanionTheory.Ar.Approx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedOfCommGroupNsmulSurjective
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem exists_section_of_nonempty {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    (f : X ⟶ Sp K) [LocallyOfFiniteType f] [Nonempty X] : ∃ s : Sp K ⟶ X, s ≫ f = 𝟙 _ := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, -, hc⟩ := nonempty_inter_closedPoints (Set.univ_nonempty (α := X))
    isClosed_univ.isLocallyClosed
  exact ⟨pointOfClosedPoint (K := K) f x hc, pointOfClosedPoint_comp (K := K) f x hc⟩

theorem exists_comp_eq_of_surjective {K : Type} [Field K] [IsAlgClosed K] (H : Over (Sp K))
    [LocallyOfFiniteType H.hom] (m : H ⟶ H) [Surjective m.left] (x : 𝟙_ (Over (Sp K)) ⟶ H) :
    ∃ y : 𝟙_ (Over (Sp K)) ⟶ H, y ≫ m = x := by
  have h1 : LocallyOfFiniteType (m.left ≫ H.hom) := by rw [Over.w m]; infer_instance
  have h2 : LocallyOfFiniteType m.left := locallyOfFiniteType_of_comp m.left H.hom
  let q : pullback m.left x.left ⟶ Sp K := pullback.snd m.left x.left
  have h3 : LocallyOfFiniteType q := inferInstanceAs (LocallyOfFiniteType (pullback.snd m.left x.left))
  have h4 : Surjective q := inferInstanceAs (Surjective (pullback.snd m.left x.left))
  have h5 : Nonempty ↥(pullback m.left x.left) := by
    obtain ⟨w, -⟩ := q.surjective (default : PrimeSpectrum K)
    exact ⟨w⟩
  obtain ⟨s, hs⟩ := exists_section_of_nonempty q
  refine ⟨Over.homMk (s ≫ pullback.fst m.left x.left) ?_, ?_⟩
  · have hx : x.left ≫ H.hom = 𝟙 _ := Over.w x
    have hm := Over.w m
    calc (s ≫ pullback.fst m.left x.left) ≫ H.hom
        = s ≫ pullback.fst m.left x.left ≫ m.left ≫ H.hom := by rw [hm]; simp
      _ = s ≫ q ≫ x.left ≫ H.hom := by
          rw [← Category.assoc (pullback.fst m.left x.left), pullback.condition]; simp [q]
      _ = 𝟙 _ := by
          rw [hx]
          change s ≫ q ≫ 𝟙 (Sp K) = _
          rw [Category.comp_id]; exact hs
  · ext1
    change (s ≫ pullback.fst m.left x.left) ≫ m.left = x.left
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (s ≫ q) ≫ x.left = x.left
    rw [hs]
    exact Category.id_comp _

theorem geometricallyConnected_of_surjective_pow : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], LocallyOfFiniteType G.hom → QuasiCompact G.hom → (∀ n : ℕ, n ≠ 0 → Surjective ((𝟙 G) ^ n : G ⟶ G).left) → GeometricallyConnected G.hom := by
  intro S G _ _ hl hq hn
  refine ⟨fun k _ y Z a b hZ => ?_⟩
  let L := AlgebraicClosure k
  let j : Sp L ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let t : Sp L ⟶ S := j ≫ y
  let H : Over (Sp L) := (Over.pullback t).obj G
  have hlH : LocallyOfFiniteType H.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom t))
  have hqH : QuasiCompact H.hom := inferInstanceAs (QuasiCompact (pullback.snd G.hom t))
  have hconn : ConnectedSpace H.left := by
    refine GlobalTheory.CompanionTheory.Ar.Approx.connectedSpace_of_divisible L H hlH hqH fun n hn0 x => ?_
    have e : (Over.pullback t).map ((𝟙 G) ^ n) = (𝟙 H) ^ n := by
      have := map_pow (Over.pullback t).homMonoidHom (𝟙 G) n
      simpa using this
    have hs : Surjective ((𝟙 H) ^ n : H ⟶ H).left := by
      have hG := hn n hn0
      have sq : IsPullback ((Over.pullback t).map ((𝟙 G) ^ n)).left (pullback.fst G.hom t)
          (pullback.fst G.hom t) ((𝟙 G) ^ n : G ⟶ G).left := by
        have hA : ((Over.pullback t).map ((𝟙 G) ^ n)).left ≫ pullback.fst G.hom t =
            pullback.fst G.hom t ≫ ((𝟙 G) ^ n : G ⟶ G).left := pullback.lift_fst _ _ _
        have hB : ((Over.pullback t).map ((𝟙 G) ^ n)).left ≫ pullback.snd G.hom t =
            pullback.snd G.hom t := Over.w ((Over.pullback t).map ((𝟙 G) ^ n))
        have rect : IsPullback (((Over.pullback t).map ((𝟙 G) ^ n)).left ≫ pullback.snd G.hom t)
            (pullback.fst G.hom t) t (((𝟙 G) ^ n : G ⟶ G).left ≫ G.hom) := by
          rw [hB, Over.w ((𝟙 G) ^ n : G ⟶ G)]
          exact (IsPullback.of_hasPullback _ _).flip
        exact IsPullback.of_right rect hA (IsPullback.of_hasPullback _ _).flip
      rw [← e]
      exact MorphismProperty.of_isPullback (P := @Surjective) sq.flip hG
    obtain ⟨w, hw⟩ := exists_comp_eq_of_surjective H ((𝟙 H) ^ n) x
    refine ⟨w, ?_⟩
    rw [← hw, MonObj.comp_pow, Category.comp_id]
  have hj : Surjective j := ⟨fun z => ⟨default, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
  have big : IsPullback (pullback.fst b j ≫ a) (pullback.snd b j) G.hom t :=
    (IsPullback.of_hasPullback b j).paste_horiz hZ
  have hc' : ConnectedSpace ↥(pullback G.hom t) := hconn
  have hsurj : Surjective (big.isoPullback.inv ≫ pullback.fst b j) := inferInstance
  exact (big.isoPullback.inv ≫ pullback.fst b j).surjective.connectedSpace
    (big.isoPullback.inv ≫ pullback.fst b j).continuous

end GlobalTheory.CompanionTheory.Ar.Approx
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedOfCommGroupNsmulSurjectiveStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyConnected_of_commGroup_nsmul_surjective : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], LocallyOfFiniteType G.hom → QuasiCompact G.hom → (∀ n : ℕ, n ≠ 0 → Surjective ((𝟙 G) ^ n : G ⟶ G).left) → GeometricallyConnected G.hom := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_of_surjective_pow | exact GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_of_surjective_pow | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_of_surjective_pow <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedOfGenericFiberSmoothProper
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem dense_range_fst_generic (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {X : Scheme.{0}} (p : X ⟶ Sp R) (hp : IsOpenMap p) :
    Dense (Set.range (pullback.fst p (spMap (algebraMap R K)))) := by
  classical
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  let y : PrimeSpectrum K := ⟨⊥, Ideal.isPrime_bot⟩
  have hy : ∀ z : PrimeSpectrum R, PrimeSpectrum.comap (algebraMap R K) y ⤳ z := by
    intro z
    rw [← PrimeSpectrum.le_iff_specializes]
    intro a ha
    have h0 : algebraMap R K a = 0 := ha
    have : a = 0 := hinj (by rw [h0, map_zero])
    rw [this]
    exact z.asIdeal.zero_mem
  have hyy : (spMap (algebraMap R K)) y = PrimeSpectrum.comap (algebraMap R K) y := rfl
  rw [Scheme.Pullback.range_fst, dense_iff_inter_open]
  rintro U hU ⟨x, hx⟩
  have hmem : (spMap (algebraMap R K)) y ∈ p '' U := by
    rw [hyy]
    exact (hy (p x)).mem_open (hp U hU) ⟨x, hx, rfl⟩
  obtain ⟨x', hx'U, hx'⟩ := hmem
  exact ⟨x', hx'U, ⟨y, hx'.symm⟩⟩

theorem geometricallyConnected_of_generic : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsProper G.hom → GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap R K))) → GeometricallyConnected G.hom := by
  intro R K _ _ _ _ _ G _ _ hsm hpr hgc
  set f := spMap (algebraMap R K) with hf
  let F := Over.pullback f
  let GK := F.obj G
  have hab : IsAbelianScheme GK := by
    refine IsAbelianScheme.mk inferInstance ?_ ?_ hgc
    · show Smooth (pullback.snd G.hom f)
      infer_instance
    · show IsProper (pullback.snd G.hom f)
      infer_instance
  refine GlobalTheory.T.geometricallyConnected_of_commGroup_nsmul_surjective (Sp R) G inferInstance inferInstance ?_
  intro n hn
  have hK := GlobalTheory.T.abelianScheme_nsmul_surjective K GK hab n hn
  have hmap : F.map (𝟙 G ^ n) = 𝟙 GK ^ n := by
    rw [← F.map_id]
    exact (Functor.homMonoidHom F (X := G) (M := G)).map_pow _ n
  set φ := (𝟙 G ^ n).left with hφ
  have hsq : (𝟙 GK ^ n).left ≫ pullback.fst G.hom f = pullback.fst G.hom f ≫ φ := by
    rw [← hmap]
    simp [F, φ] <;> exact pullback.lift_fst _ _ _
  have hw : φ ≫ G.hom = G.hom := Over.w (𝟙 G ^ n)
  have hcomp : IsProper (φ ≫ G.hom) := by rw [hw]; exact hpr
  have hsep : IsSeparated G.hom := inferInstance
  have hprop : UniversallyClosed φ := by
    first
    | exact (MorphismProperty.of_postcomp (W := @IsProper) (W' := @IsSeparated) φ G.hom hsep hcomp).toUniversallyClosed
    | exact MorphismProperty.of_postcomp (W := @UniversallyClosed) (W' := @IsSeparated) φ G.hom hsep inferInstance
    | exact UniversallyClosed.of_comp_of_isSeparated φ G.hom
    | exact (IsProper.of_comp φ G.hom).toUniversallyClosed
  have hcl : IsClosed (Set.range φ) := φ.isClosedMap.isClosed_range
  have hop : IsOpenMap G.hom := G.hom.isOpenMap
  have hdense := dense_range_fst_generic R K G.hom hop
  have hsub : Set.range (pullback.fst G.hom f) ⊆ Set.range φ := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨w, rfl⟩ := hK.surj z
    refine ⟨pullback.fst G.hom f w, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply]
  have huniv : Set.range φ = Set.univ :=
    (hdense.mono hsub).closure_eq ▸ hcl.closure_eq.symm
  exact ⟨fun x => by
    have : x ∈ Set.range φ := huniv ▸ Set.mem_univ x
    exact this⟩

end GlobalTheory.CompanionTheory.Ar.Approx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedOfGenericFiberSmoothProperStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
theorem _root_.GlobalTheory.T.geometricallyConnected_of_generic_fiber_smooth_proper : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsProper G.hom → GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap R K))) → GeometricallyConnected G.hom := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_of_generic | exact GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_of_generic | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_of_generic <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConnectedFibersStableUnderSpecialization
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem geometricallyConnected_snd_snd_iff {X S S' S'' : Scheme.{0}} (g : X ⟶ S) (f : S' ⟶ S)
    (b : S'' ⟶ S') :
    GeometricallyConnected (pullback.snd (pullback.snd g f) b) ↔
      GeometricallyConnected (pullback.snd g (b ≫ f)) := by
  haveI : MorphismProperty.RespectsIso @GeometricallyConnected :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [← pullbackLeftPullbackSndIso_hom_snd g f b]
  exact MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected _ _

private theorem spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) : spMap g ≫ spMap f = spMap (g.comp f) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem stableUnderSpecialization_geometricallyConnected :
    ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G],
      Smooth G.hom → IsProper G.hom →
      StableUnderSpecialization {x : PrimeSpectrum k | GeometricallyConnected
        (pullback.snd G.hom (spMap (algebraMap k x.asIdeal.ResidueField)))} := by
  intro k _ _ G _ _ hsm hpr x y hxy hx
  haveI := hsm
  haveI := hpr
  have hle : x.asIdeal ≤ y.asIdeal := (PrimeSpectrum.le_iff_specializes x y).mpr hxy
  have hs' : Smooth ((Over.pullback (spMap (algebraMap k (k ⧸ x.asIdeal)))).obj G).hom := by
    show Smooth (pullback.snd G.hom (spMap (algebraMap k (k ⧸ x.asIdeal))))
    infer_instance
  have hp' : IsProper ((Over.pullback (spMap (algebraMap k (k ⧸ x.asIdeal)))).obj G).hom := by
    show IsProper (pullback.snd G.hom (spMap (algebraMap k (k ⧸ x.asIdeal))))
    infer_instance
  have hgen : GeometricallyConnected (pullback.snd
      ((Over.pullback (spMap (algebraMap k (k ⧸ x.asIdeal)))).obj G).hom
      (spMap (algebraMap (k ⧸ x.asIdeal) x.asIdeal.ResidueField))) := by
    show GeometricallyConnected (pullback.snd (pullback.snd G.hom (spMap (algebraMap k (k ⧸ x.asIdeal))))
      (spMap (algebraMap (k ⧸ x.asIdeal) x.asIdeal.ResidueField)))
    rw [geometricallyConnected_snd_snd_iff, spMap_comp_moduli_spaces, ← IsScalarTower.algebraMap_eq]
    exact hx
  have hG' : GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k (k ⧸ x.asIdeal)))) :=
    GlobalTheory.T.geometricallyConnected_of_generic_fiber_smooth_proper (k ⧸ x.asIdeal) x.asIdeal.ResidueField
      ((Over.pullback (spMap (algebraMap k (k ⧸ x.asIdeal)))).obj G) hs' hp' hgen
  have hker : ∀ a ∈ x.asIdeal, algebraMap k y.asIdeal.ResidueField a = 0 := fun a ha =>
    Ideal.algebraMap_residueField_eq_zero.mpr (hle ha)
  have hφ : (Ideal.Quotient.lift x.asIdeal (algebraMap k y.asIdeal.ResidueField) hker).comp
      (algebraMap k (k ⧸ x.asIdeal)) = algebraMap k y.asIdeal.ResidueField := by
    rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.lift_comp_mk _ _ _
  show GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k y.asIdeal.ResidueField)))
  rw [← hφ, ← spMap_comp_moduli_spaces, ← geometricallyConnected_snd_snd_iff]
  infer_instance

end GlobalTheory.CompanionTheory.Ar.Approx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConnectedFibersStableUnderSpecializationStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
theorem _root_.GlobalTheory.T.connected_fibers_stableUnderSpecialization : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsProper G.hom → StableUnderSpecialization {x : PrimeSpectrum k | GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k x.asIdeal.ResidueField)))} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.stableUnderSpecialization_geometricallyConnected | exact GlobalTheory.CompanionTheory.Ar.Approx.stableUnderSpecialization_geometricallyConnected | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.stableUnderSpecialization_geometricallyConnected <;> assumption)
end
