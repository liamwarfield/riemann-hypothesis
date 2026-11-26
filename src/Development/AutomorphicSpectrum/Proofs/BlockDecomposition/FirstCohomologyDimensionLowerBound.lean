module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.AbelianSchemeSpreadsOverLocalization

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedFibreStructureCohomologyFinite
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedFibreStructureCohomologyFinite
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.FlatFibre

theorem closed_fibre_first_cohomology_finite : FlatBCSt → ∀ (k : Type) [Field k] (A : Over (Sp k)) [IsSeparated A.hom] [QuasiCompact A.hom],
    Module.Finite k (HO1 A.hom) → ∀ (R : Type) [CommRing R] [IsLocalRing R] (t : Sp R ⟶ Sp k)
    (X' : Scheme.{0}) (s' : X' ⟶ Sp (IsLocalRing.ResidueField R)) (φ : X' ⟶ (A ⊗ Over.mk t).left),
    IsPullback φ s' (snd A (Over.mk t)).left (spMap (algebraMap R (IsLocalRing.ResidueField R))) →
    Module.Finite (IsLocalRing.ResidueField R) (HO1 s') ∧
      Module.finrank (IsLocalRing.ResidueField R) (HO1 s') ≤ Module.finrank k (HO1 A.hom) := by
  intro hBC k _ A _ _ hfin R _ _ t X' s' φ h
  let u : Sp (IsLocalRing.ResidueField R) ⟶ Sp k :=
    spMap (algebraMap R (IsLocalRing.ResidueField R)) ≫ t
  let σ : k →+* IsLocalRing.ResidueField R := (Spec.preimage u).hom
  have hσ : spMap σ = u := Spec.map_preimage u
  let _ : Algebra k (IsLocalRing.ResidueField R) := σ.toAlgebra
  have hsq : IsPullback (fst A (Over.mk t)).left (snd A (Over.mk t)).left A.hom t := by
    simpa using IsPullback.of_hasPullback A.hom t
  have hp : IsPullback (φ ≫ (fst A (Over.mk t)).left) s' A.hom
      (spMap (algebraMap k (IsLocalRing.ResidueField R))) := by
    have h2 := IsPullback.paste_horiz h hsq
    have h3 : spMap (algebraMap k (IsLocalRing.ResidueField R)) = u := hσ
    rw [h3]
    exact h2
  obtain ⟨e, -⟩ := hBC k (IsLocalRing.ResidueField R) A.left X' A.hom s' _ hp inferInstance inferInstance
  refine ⟨Module.Finite.equiv e, ?_⟩
  rw [← e.finrank_eq, Module.finrank_baseChange]

end GlobalTheory.CompanionTheory.FlatFibre
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedFibreStructureCohomologyFiniteStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_fibre_structure_cohomology_finite : FlatBCSt → ∀ (k : Type) [Field k] (A : Over (Sp k)) [IsSeparated A.hom] [QuasiCompact A.hom], Module.Finite k (HO1 A.hom) → ∀ (R : Type) [CommRing R] [IsLocalRing R] (t : Sp R ⟶ Sp k) (X' : Scheme.{0}) (s' : X' ⟶ Sp (IsLocalRing.ResidueField R)) (φ : X' ⟶ (A ⊗ Over.mk t).left), IsPullback φ s' (snd A (Over.mk t)).left (spMap (algebraMap R (IsLocalRing.ResidueField R))) → Module.Finite (IsLocalRing.ResidueField R) (HO1 s') ∧ Module.finrank (IsLocalRing.ResidueField R) (HO1 s') ≤ Module.finrank k (HO1 A.hom) := by
  first | exact @GlobalTheory.CompanionTheory.FlatFibre.closed_fibre_first_cohomology_finite | exact GlobalTheory.CompanionTheory.FlatFibre.closed_fibre_first_cohomology_finite | (intros; apply GlobalTheory.CompanionTheory.FlatFibre.closed_fibre_first_cohomology_finite <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StalkIdealRepresentsClosedSubscheme
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StalkIdealRepresentsClosedSubscheme
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.StalkIdeal

theorem exists_stalk_ideal : ∀ (X Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (x : X), x ∈ Set.range i → (∀ z : Z, IsClosed ({z} : Set Z)) → ∃ I : Ideal (X.presheaf.stalk x), I ≠ ⊤ ∧ (∀ q : Ideal (X.presheaf.stalk x), q.IsPrime → I ≤ q → q = IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ∧ ∀ J : Ideal (X.presheaf.stalk x), (∃ z : Sp (X.presheaf.stalk x ⧸ J) ⟶ Z, z ≫ i = spMap (Ideal.Quotient.mk J) ≫ X.fromSpecStalk x) ↔ I ≤ J := by
  intro X Z i _ x hx hcl
  have hq : IsClosedImmersion (pullback.snd i (X.fromSpecStalk x)) := inferInstance
  obtain ⟨I, e, he⟩ := IsClosedImmersion.Spec_iff.1 hq
  have hpt : ∀ p : ↥(pullback i (X.fromSpecStalk x)),
      X.fromSpecStalk x (pullback.snd i (X.fromSpecStalk x) p) =
        i (pullback.fst i (X.fromSpecStalk x) p) := by
    intro p
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have hsnd : ∀ s : ↥(Spec (CommRingCat.of (X.presheaf.stalk x ⧸ I))),
      pullback.snd i (X.fromSpecStalk x) (e.inv s) = PrimeSpectrum.comap (Ideal.Quotient.mk I) s := by
    intro s
    rw [he, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply e.inv e.hom, Iso.inv_hom_id]
    rfl
  refine ⟨I, ?_, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hx
    obtain ⟨p, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := i) (g := X.fromSpecStalk x)
      z (IsLocalRing.closedPoint _) (by rw [Scheme.fromSpecStalk_closedPoint, hz])
    have hs : (show PrimeSpectrum (X.presheaf.stalk x ⧸ I) from e.hom p).asIdeal.IsPrime :=
      PrimeSpectrum.isPrime _
    rw [← Ideal.Quotient.nontrivial_iff]
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    exact hs.ne_top (Subsingleton.elim _ _)
  · intro q hq hIq
    have hQ : (Ideal.map (Ideal.Quotient.mk I) q).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
    let Q0 : PrimeSpectrum (X.presheaf.stalk x ⧸ I) := ⟨_, hQ⟩
    let Q : ↥(Spec (CommRingCat.of (X.presheaf.stalk x ⧸ I))) := Q0
    let P : PrimeSpectrum (X.presheaf.stalk x) := ⟨q, hq⟩
    have hPQ : PrimeSpectrum.comap (Ideal.Quotient.mk I) Q = P := by
      ext1
      show Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) q) = q
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.2 hIq]
    have h1 : X.fromSpecStalk x P = i (pullback.fst i (X.fromSpecStalk x) (e.inv Q)) := by
      rw [← hPQ, ← hsnd, hpt]
    have hspec : P ⤳ IsLocalRing.closedPoint (X.presheaf.stalk x) := by
      rw [← PrimeSpectrum.le_iff_specializes, ← PrimeSpectrum.asIdeal_le_asIdeal]
      exact IsLocalRing.le_maximalIdeal hq.ne_top
    have h2 : X.fromSpecStalk x P ⤳ x := by
      have := hspec.map (X.fromSpecStalk x).continuous
      rwa [Scheme.fromSpecStalk_closedPoint] at this
    have hclosed : IsClosed ({i (pullback.fst i (X.fromSpecStalk x) (e.inv Q))} : Set X) := by
      rw [← Set.image_singleton]
      exact i.isClosedEmbedding.isClosedMap _ (hcl _)
    have h3 : x = X.fromSpecStalk x P := by
      have := h2.mem_closed hclosed (by rw [h1]; exact Set.mem_singleton _)
      rw [Set.mem_singleton_iff] at this
      exact this.trans h1.symm
    have h4 : P = IsLocalRing.closedPoint (X.presheaf.stalk x) :=
      (X.fromSpecStalk x).isEmbedding.injective (by rw [Scheme.fromSpecStalk_closedPoint]; exact h3.symm)
    exact congrArg PrimeSpectrum.asIdeal h4
  · intro J
    constructor
    · rintro ⟨z, hz⟩
      have hw := pullback.lift_snd z (spMap (Ideal.Quotient.mk J)) hz
      rw [he, ← Category.assoc] at hw
      have h2 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) ≫
          Spec.preimage (S := CommRingCat.of (X.presheaf.stalk x ⧸ J))
            (pullback.lift z (spMap (Ideal.Quotient.mk J)) hz ≫ e.hom)) =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
        rw [Spec.map_comp, Spec.map_preimage]
        exact hw
      rw [Spec.map_inj] at h2
      intro a ha
      have h3 := congrArg (fun g => g.hom a) h2
      have h4 : Ideal.Quotient.mk I a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 ha
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, h4, map_zero] at h3
      exact Ideal.Quotient.eq_zero_iff_mem.1 h3.symm
    · intro hIJ
      refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hIJ)) ≫ e.inv ≫
        pullback.fst i (X.fromSpecStalk x), ?_⟩
      rw [Category.assoc, Category.assoc, pullback.condition, he, Category.assoc, Iso.inv_hom_id_assoc,
        ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]

end GlobalTheory.CompanionTheory.StalkIdeal
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StalkIdealRepresentsClosedSubschemeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalk_ideal_represents_closed_subscheme : ∀ (X Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (x : X), x ∈ Set.range i → (∀ z : Z, IsClosed ({z} : Set Z)) → ∃ I : Ideal (X.presheaf.stalk x), I ≠ ⊤ ∧ (∀ q : Ideal (X.presheaf.stalk x), q.IsPrime → I ≤ q → q = IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ∧ ∀ J : Ideal (X.presheaf.stalk x), (∃ z : Sp (X.presheaf.stalk x ⧸ J) ⟶ Z, z ≫ i = spMap (Ideal.Quotient.mk J) ≫ X.fromSpecStalk x) ↔ I ≤ J := by
  first | exact @GlobalTheory.CompanionTheory.StalkIdeal.exists_stalk_ideal | exact GlobalTheory.CompanionTheory.StalkIdeal.exists_stalk_ideal | (intros; apply GlobalTheory.CompanionTheory.StalkIdeal.exists_stalk_ideal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitelyManySectionsPointsClosed
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitelyManySectionsPointsClosed
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.ClosedPts

theorem isClosed_singleton_of_finite_points : ∀ (k : Type) [Field k] [IsAlgClosed k] (Z : Scheme.{0}) (s : Z ⟶ Sp k) [LocallyOfFiniteType s], Set.Finite {σ : Sp k ⟶ Z | σ ≫ s = 𝟙 _} → ∀ z : Z, IsClosed ({z} : Set Z) := by
  intro k _ _ Z s _ hfin z
  haveI : JacobsonSpace (Sp k) :=
    (PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace (R := k)).mp inferInstance
  haveI : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace s
  let pt : Sp k := IsLocalRing.closedPoint (CommRingCat.of k)
  have hsec : ∀ x : Z, IsClosed ({x} : Set Z) →
      x ∈ (fun σ : Sp k ⟶ Z => σ pt) '' {σ : Sp k ⟶ Z | σ ≫ s = 𝟙 _} := by
    intro x hx
    haveI := (isClosed_singleton_iff_locallyOfFiniteType (x := x)).mp hx
    obtain ⟨g, hg⟩ : ∃ g : CommRingCat.of k ⟶ Z.residueField x,
        Spec.map g = Z.fromSpecResidueField x ≫ s :=
      ⟨Spec.preimage (Z.fromSpecResidueField x ≫ s), Spec.map_preimage _⟩
    have hlft : LocallyOfFiniteType (Spec.map g) := by rw [hg]; infer_instance
    have hft : g.hom.FiniteType := HasRingHomProperty.Spec_iff.mp hlft
    letI : Algebra k (Z.residueField x) := g.hom.toAlgebra
    haveI : Algebra.FiniteType k (Z.residueField x) := hft
    haveI : Module.Finite k (Z.residueField x) := finite_of_finite_type_of_isJacobsonRing k _
    have hbij : Function.Bijective (algebraMap k (Z.residueField x)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e := RingEquiv.ofBijective (algebraMap k (Z.residueField x)) hbij
    let φ : Z.residueField x ⟶ CommRingCat.of k := CommRingCat.ofHom e.symm.toRingHom
    have hgφ : g ≫ φ = 𝟙 _ := by
      ext a
      exact e.symm_apply_apply a
    refine ⟨Spec.map φ ≫ Z.fromSpecResidueField x, ?_, ?_⟩
    · have h1 : (Spec.map φ ≫ Z.fromSpecResidueField x) ≫ s = Spec.map (g ≫ φ) := by
        rw [Category.assoc, ← hg]
        exact (Spec.map_comp _ _).symm
      rw [hgφ, Spec.map_id] at h1
      exact h1
    · simp [Scheme.fromSpecResidueField_apply]
  have hcp : (closedPoints Z).Finite :=
    (hfin.image (fun σ : Sp k ⟶ Z => σ pt)).subset (fun x hx => hsec x hx)
  have hT : (closure ({z} : Set Z) ∩ closedPoints Z).Finite :=
    hcp.subset Set.inter_subset_right
  have hTc : IsClosed (closure ({z} : Set Z) ∩ closedPoints Z) := by
    rw [← Set.biUnion_of_singleton (closure ({z} : Set Z) ∩ closedPoints Z)]
    exact hT.isClosed_biUnion (fun t ht => ht.2)
  have heq : closure (closure ({z} : Set Z) ∩ closedPoints Z) = closure ({z} : Set Z) :=
    JacobsonSpace.closure_inter_closedPoints isClosed_closure
  have hz : z ∈ closure ({z} : Set Z) ∩ closedPoints Z := by
    rw [← hTc.closure_eq, heq]
    exact subset_closure (Set.mem_singleton z)
  exact hz.2

end GlobalTheory.CompanionTheory.ClosedPts
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitelyManySectionsPointsClosedStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitely_many_sections_points_closed : ∀ (k : Type) [Field k] [IsAlgClosed k] (Z : Scheme.{0}) (s : Z ⟶ Sp k) [LocallyOfFiniteType s], Set.Finite {σ : Sp k ⟶ Z | σ ≫ s = 𝟙 _} → ∀ z : Z, IsClosed ({z} : Set Z) := by
  first | exact @GlobalTheory.CompanionTheory.ClosedPts.isClosed_singleton_of_finite_points | exact GlobalTheory.CompanionTheory.ClosedPts.isClosed_singleton_of_finite_points | (intros; apply GlobalTheory.CompanionTheory.ClosedPts.isClosed_singleton_of_finite_points <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrivialLocusRepresentsTriviality
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrivialLocusRepresentsTriviality
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.TrivPull

theorem isPullback_fst_snd {S : Scheme.{0}} (A T : Over S) :
    IsPullback (fst A T).left (snd A T).left A.hom T.hom := by
  rw [Over.fst_left, Over.snd_left]
  exact IsPullback.of_hasPullback A.hom T.hom

theorem isPullback_whisker {S : Scheme.{0}} (A T : Over S) {B : Scheme.{0}} (b : B ⟶ T.left) :
    IsPullback (A ◁ (Over.homMk b rfl : Over.mk (b ≫ T.hom) ⟶ T)).left
      (snd A (Over.mk (b ≫ T.hom))).left (snd A T).left b := by
  have h1 := isPullback_fst_snd A T
  have h2 := isPullback_fst_snd A (Over.mk (b ≫ T.hom))
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, CartesianMonoidalCategory.whiskerLeft_fst]
    exact h2
  · rw [← Over.comp_left, CartesianMonoidalCategory.whiskerLeft_snd, Over.comp_left]
    rfl

theorem pull_iso_eq_zero_iff {X Y : Scheme.{0}} (θ : Y ≅ X) (c : Pic X) :
    CechPic.pull θ.hom c = 0 ↔ c = 0 := by
  constructor
  · intro h
    have h' := congrArg (CechPic.pull θ.inv) h
    rwa [← pull_comp, θ.inv_hom_id, pull_id, map_zero] at h'
  · intro h
    rw [h, map_zero]

theorem triv_pull_iff {S : Scheme.{0}} (A Y Z : Over S) (N : LB (A ⊗ Y).left) (hN : N.IsLB) (i : Z ⟶ Y)
    (h : PositivityTheory.ObstructionTrivialLocus.IsTrivLocus A N i) (T : Over S) (y : T ⟶ Y) {B : Scheme.{0}} (b : B ⟶ T.left) :
    Triv ((ev N (fst A T) (snd A T ≫ y)).pull (pullback.fst (snd A T).left b)) ↔
      ∃ z : B ⟶ Z.left, z ≫ i.left = b ≫ y.left := by
  obtain ⟨-, h2⟩ := h
  obtain ⟨g, hg⟩ : ∃ g : Over.mk (b ≫ T.hom) ⟶ T, g = Over.homMk b rfl := ⟨_, rfl⟩
  have hW := isPullback_whisker A T b
  rw [← hg] at hW
  have hθ : hW.isoPullback.hom ≫ pullback.fst (snd A T).left b = (A ◁ g).left :=
    hW.isoPullback_hom_fst
  have hlift : lift (fst A (Over.mk (b ≫ T.hom))) (snd A (Over.mk (b ≫ T.hom)) ≫ g ≫ y) =
      (A ◁ g) ≫ lift (fst A T) (snd A T ≫ y) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have hF := pull_isLB hN (lift (fst A T) (snd A T ≫ y)).left
  have hP := pull_isLB hF (pullback.fst (snd A T).left b)
  have hE := pull_isLB hN (lift (fst A (Over.mk (b ≫ T.hom))) (snd A (Over.mk (b ≫ T.hom)) ≫ g ≫ y)).left
  have e3 : cls _ hE = CechPic.pull hW.isoPullback.hom (cls _ hP) := by
    rw [cls_pull hN _ hE, cls_pull hF _ hP, cls_pull hN _ hF, ← pull_comp, ← pull_comp,
      hlift, Over.comp_left, hθ]
  have hg' : g.left = b := by
    rw [hg]
    rfl
  calc Triv ((ev N (fst A T) (snd A T ≫ y)).pull (pullback.fst (snd A T).left b))
      ↔ cls _ hP = 0 := (cls_eq_zero_iff hP).symm
    _ ↔ CechPic.pull hW.isoPullback.hom (cls _ hP) = 0 := (pull_iso_eq_zero_iff _ _).symm
    _ ↔ cls _ hE = 0 := by rw [e3]
    _ ↔ Triv (ev N (fst A (Over.mk (b ≫ T.hom))) (snd A (Over.mk (b ≫ T.hom)) ≫ g ≫ y)) :=
      cls_eq_zero_iff hE
    _ ↔ ∃ z, z ≫ i = g ≫ y := h2 _ _
    _ ↔ ∃ z : B ⟶ Z.left, z ≫ i.left = b ≫ y.left := by
      constructor
      · rintro ⟨z, hz⟩
        refine ⟨z.left, ?_⟩
        have hz' : (z ≫ i).left = (g ≫ y).left := by rw [hz]
        rw [Over.comp_left, Over.comp_left, hg'] at hz'
        exact hz'
      · rintro ⟨z, hz⟩
        have hzw : z ≫ Z.hom = (Over.mk (b ≫ T.hom)).hom := by
          show z ≫ Z.hom = b ≫ T.hom
          rw [← Over.w i, ← Category.assoc, hz, Category.assoc, Over.w y]
        refine ⟨Over.homMk z hzw, ?_⟩
        apply Over.OverMorphism.ext
        rw [Over.comp_left, Over.comp_left, hg']
        exact hz

end GlobalTheory.CompanionTheory.TrivPull
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrivialLocusRepresentsTrivialityStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivial_locus_represents_triviality : ∀ {S : Scheme.{0}} (A Y Z : Over S) (N : LB (A ⊗ Y).left), N.IsLB → ∀ (i : Z ⟶ Y), PositivityTheory.ObstructionTrivialLocus.IsTrivLocus A N i → ∀ (T : Over S) (y : T ⟶ Y) {B : Scheme.{0}} (b : B ⟶ T.left), Triv ((ev N (fst A T) (snd A T ≫ y)).pull (pullback.fst (snd A T).left b)) ↔ ∃ z : B ⟶ Z.left, z ≫ i.left = b ≫ y.left := by
  first | exact @GlobalTheory.CompanionTheory.TrivPull.triv_pull_iff | exact GlobalTheory.CompanionTheory.TrivPull.triv_pull_iff | (intros; apply GlobalTheory.CompanionTheory.TrivPull.triv_pull_iff <;> assumption)
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.CompanionTheory.FirstCohomologyLowerBound

theorem dim_le (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (g n : ℕ) (hg : ringKrullDim R = g)
    (I : Ideal R) (hne : I ≠ ⊤) (hI : ∀ q : Ideal R, q.IsPrime → I ≤ q → q = IsLocalRing.maximalIdeal R)
    (f : Fin n → R) (hf : Ideal.span (Set.range f) = I) : g ≤ n := by
  have hm : IsLocalRing.maximalIdeal R ∈ I.minimalPrimes := by
    obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hne
    rwa [← hI p hp.1.1 hp.1.2]
  have h1 := Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes I _ hm
  have h2 : Submodule.spanRank I ≤ n := by
    rw [← hf]
    refine (Submodule.spanRank_span_le_card (R := R) (Set.range f)).trans (Cardinal.mk_range_le.trans ?_)
    simp
  have h3 : (IsLocalRing.maximalIdeal R).height ≤ n := by
    refine h1.trans ?_
    simpa using Cardinal.toENat.monotone' h2
  have h4 : (((IsLocalRing.maximalIdeal R).height : ℕ∞) : WithBot ℕ∞) = ((g : ℕ∞) : WithBot ℕ∞) :=
    (IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)).trans hg
  rw [WithBot.coe_inj.1 h4] at h3
  exact_mod_cast h3

theorem exists_ample (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (hA : IsAbelianScheme A) :
    ∃ L : LB A.left, L.IsLB ∧ Out.RelAmple A L := by
  haveI := hA.proper
  obtain ⟨M, hM⟩ := GlobalTheory.exists_isAmpleLB_of_isProjOver (PositivityTheory.Xgn.AbelianSchemeSpreading.isProjOver_abelian k A hA)
  exact ⟨M, hM.isLB, (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A hM.isLB).2 hM⟩

theorem evc_lam' {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hP : (abelian₂ A L).IsLB)
    {Y : Over S} (a b : Y ⟶ A) : evc hP a b = lam (cls L hL) a b := by
  rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
    lift_snd]

theorem triv_lam_one {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (hL : L.IsLB) :
    Triv (ev (abelian₂ A L) (1 : A ⟶ A) (𝟙 A)) := by
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  rw [triv_ev_iff hP, evc_lam' hL, lam_one_left]

theorem one_mem_locus {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (hL : L.IsLB)
    (Z : Over S) (i : Z ⟶ A) (h : PositivityTheory.ObstructionTrivialLocus.IsTrivLocus A (abelian₂ A L) i) (T : Over S) :
    ∃ z : T ⟶ Z, z ≫ i = 1 := by
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  refine (h.2 T 1).1 ?_
  rw [triv_ev_iff hP, evc_lam' hL, MonObj.comp_one, lam_one_right]

theorem snd_smooth_proper {S : Scheme.{0}} (A T : Over S) [Smooth A.hom] [IsProper A.hom] :
    Smooth (snd A T).left ∧ IsProper (snd A T).left := by
  have h : IsPullback (fst A T).left (snd A T).left A.hom T.hom := IsPullback.of_hasPullback _ _
  exact ⟨MorphismProperty.of_isPullback h inferInstance, MorphismProperty.of_isPullback h inferInstance⟩

theorem lam_triv_left {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB)
    {T : Over S} (x : T ⟶ A) (h : Triv (ev (abelian₂ A L) (fst A T) (snd A T ≫ x))) :
    Triv (ev (abelian₂ A L) (fst T A ≫ x) (snd T A)) := by
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  rw [triv_ev_iff hP] at h ⊢
  have e := congrArg (CechPic.pull (lift (snd T A) (fst T A)).left) h
  rw [pull_evc, map_zero, lift_fst, lift_snd_assoc, evc_lam' hL, lam_comm] at e
  rwa [evc_lam' hL]

theorem finite_sections (hK : PositivityTheory.ObstructionTrivialLocus.KFinite) (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A]
    (hA : IsAbelianScheme A) (L : LB A.left) (hL : L.IsLB) (hamp : Out.RelAmple A L) (Z : Over (Sp k)) (i : Z ⟶ A)
    (h : PositivityTheory.ObstructionTrivialLocus.IsTrivLocus A (abelian₂ A L) i) : Set.Finite {σ : Sp k ⟶ Z.left | σ ≫ Z.hom = 𝟙 _} := by
  haveI := hA.comm
  haveI : IsClosedImmersion i.left := h.1
  have hF := hK (Sp k) A hA L hL hamp k (𝟙 _)
  refine Set.Finite.of_finite_image (f := fun σ ↦ σ ≫ i.left) ((hF.image fun x ↦ x.left).subset ?_)
    (fun a _ b _ e ↦ (cancel_mono i.left).1 e)
  rintro _ ⟨σ, hσ, rfl⟩
  let z : Over.mk (𝟙 (Sp k)) ⟶ Z := Over.homMk σ hσ
  refine ⟨z ≫ i, lam_triv_left hL _ ((h.2 _ _).2 ⟨z, rfl⟩), rfl⟩

theorem stalk_local (X : Scheme.{0}) (x : X) : IsLocalRing (X.presheaf.stalk x) := inferInstance

theorem stalk_noeth (X : Scheme.{0}) [IsLocallyNoetherian X] (x : X) : IsNoetherianRing (X.presheaf.stalk x) :=
  inferInstance

theorem core (hFew : FewEqSt) (hFB : FlatBCSt) (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] [Smooth A.hom]
    [IsProper A.hom] (hfin : Module.Finite k (HO1 A.hom)) (N : LB (A ⊗ A).left) (hN : N.IsLB) (Z : Over (Sp k))
    (i : Z ⟶ A) (hi : PositivityTheory.ObstructionTrivialLocus.IsTrivLocus A N i) (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (y₀ : Sp R ⟶ A.left) (g : ℕ) (hdim : ringKrullDim R = g) (I : Ideal R) (hne : I ≠ ⊤)
    (hrad : ∀ q : Ideal R, q.IsPrime → I ≤ q → q = IsLocalRing.maximalIdeal R)
    (hJ : ∀ J : Ideal R, (∃ z : Sp (R ⧸ J) ⟶ Z.left, z ≫ i.left = spMap (Ideal.Quotient.mk J) ≫ y₀) ↔ I ≤ J) :
    g ≤ Module.finrank k (HO1 A.hom) := by
  let T : Over (Sp k) := Over.mk (y₀ ≫ A.hom)
  let y : T ⟶ A := Over.homMk y₀ rfl
  have hs := snd_smooth_proper A T
  obtain ⟨f, hf⟩ := hFew R (A ⊗ T).left (snd A T).left (Module.finrank k (HO1 A.hom))
    hs.1 hs.2 (fun X' s' φ h ↦ GlobalTheory.T.closed_fibre_structure_cohomology_finite hFB k A hfin R _ X' s' φ h)
    (ev N (fst A T) (snd A T ≫ y)) (pull_isLB hN _) I hne
    (fun J ↦ (GlobalTheory.T.trivial_locus_represents_triviality A A Z N hN i hi T y (spMap (Ideal.Quotient.mk J))).trans (hJ J))
  exact dim_le R g _ hdim I hne hrad f hf

theorem first_cohomology_dimension_lower_bound : PositivityTheory.ObstructionTrivialLocus.TrivLocus → PositivityTheory.ObstructionTrivialLocus.KFinite → FlatBCSt → FewEqSt → StalkDimSt → H1DimGeAbelianDim := by
  intro hTL hKF hFB hFew hSD k _ _ A _ g hA hsm hfin
  obtain ⟨L, hL, hamp⟩ := exists_ample k A hA
  haveI := hA.comm
  haveI := hA.smooth
  haveI := hA.proper
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  haveI hnoeth : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  obtain ⟨Z, i, hi⟩ := hTL (Sp k) A A hA hnoeth (abelian₂ A L) hP (triv_lam_one A L hL)
  haveI : IsClosedImmersion i.left := hi.1
  haveI : LocallyOfFiniteType Z.hom := by
    rw [← Over.w i]
    infer_instance
  have hcl := GlobalTheory.T.finitely_many_sections_points_closed k Z.left Z.hom (finite_sections hKF k A hA L hL hamp Z i hi)
  let e : Sp k ⟶ A.left := (1 : Over.mk (𝟙 (Sp k)) ⟶ A).left
  have he : e ≫ A.hom = 𝟙 _ := Over.w (1 : Over.mk (𝟙 (Sp k)) ⟶ A)
  let p : Sp k := IsLocalRing.closedPoint k
  obtain ⟨z, hz⟩ := one_mem_locus A L hL Z i hi (Over.mk (𝟙 (Sp k)))
  have hx : e.base p ∈ Set.range i.left := ⟨z.left.base p, by
    have : z.left ≫ i.left = e := congrArg (fun q ↦ q.left) hz
    rw [← this]; rfl⟩
  have hd := hSD k A.left A.hom e g he hsm p
  generalize (e.base p : A.left) = x at hx hd
  obtain ⟨I, hne, hrad, hJ⟩ := GlobalTheory.T.stalk_ideal_represents_closed_subscheme A.left Z.left i.left x hx hcl
  exact @core hFew hFB k _ A _ _ _ hfin (abelian₂ A L) hP Z i hi (A.left.presheaf.stalk x) _ (stalk_local A.left x)
    (stalk_noeth A.left x) (A.left.fromSpecStalk x) g hd I hne hrad hJ

end GlobalTheory.CompanionTheory.FirstCohomologyLowerBound
