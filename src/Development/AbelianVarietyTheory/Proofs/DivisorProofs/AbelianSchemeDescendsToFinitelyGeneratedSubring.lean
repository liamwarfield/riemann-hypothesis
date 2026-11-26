module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversallyClosedOfIsClosedRange
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetAbelianLocusOfGoodReduction
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.QuasiCompactIffLocallyOfFinitePresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFormsEqKilledByGroupAlgebra
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFormsFiniteStabilisers

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubring
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubring
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.AbelianLimit


open RationalPoint in
theorem connectedSpace_of_surjective_pow {k : Type} [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G]
    [IsCommMonObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (h : ∀ n : ℕ, 1 ≤ n → Surjective ((𝟙 G) ^ n : G ⟶ G).left) : ConnectedSpace G.left := by
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : IsNoetherian G.left := {}
  have key (f : G ⟶ G) {x y : 𝟙_ (Over (Sp k)) ⟶ G} (hx : pt x ∈ connectedComponent (pt y)) :
      pt (x ≫ f) ∈ connectedComponent (pt (y ≫ f)) :=
    f.left.continuous.image_connectedComponent_subset (pt y) ⟨_, hx, rfl⟩
  have tr (x z : 𝟙_ (Over (Sp k)) ⟶ G) : x ≫ (𝟙 G * (toUnit G ≫ z)) = x * z := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (x ≫ toUnit G) (𝟙 _), Category.id_comp]
  have key' (z : 𝟙_ (Over (Sp k)) ⟶ G) {x y : 𝟙_ (Over (Sp k)) ⟶ G} (hx : pt x ∈ connectedComponent (pt y)) :
      pt (x * z) ∈ connectedComponent (pt (y * z)) := by
    simpa only [tr] using key (𝟙 G * (toUnit G ≫ z)) hx
  let H : Subgroup (𝟙_ (Over (Sp k)) ⟶ G) :=
    { carrier := {x | pt x ∈ connectedComponent (pt (1 : 𝟙_ (Over (Sp k)) ⟶ G))}
      one_mem' := mem_connectedComponent
      mul_mem' := fun {x y} hx hy => by
        have := key' y hx
        rw [_root_.one_mul, ← connectedComponent_eq hy] at this
        exact this
      inv_mem' := fun {x} hx => by
        have := key (𝟙 G)⁻¹ hx
        rwa [GrpObj.comp_inv, GrpObj.comp_inv, Category.comp_id, Category.comp_id, inv_one] at this }
  have : H.Normal := ⟨fun x hx g => by rwa [_root_.mul_comm g x, mul_inv_cancel_right]⟩
  have : DiscreteTopology (_root_.ConnectedComponents G.left) :=
    ConnectedComponents.discreteTopology_iff.2 isOpen_connectedComponent_of_noetherianSpace
  have : Finite (_root_.ConnectedComponents G.left) := finite_of_compact_of_discrete
  have : Finite ((𝟙_ (Over (Sp k)) ⟶ G) ⧸ H) := by
    refine Finite.of_injective (fun q => ConnectedComponents.mk (pt q.out)) fun q q' e => ?_
    rw [← q.out_eq, ← q'.out_eq]
    refine QuotientGroup.eq.2 ?_
    have := key' q.out⁻¹ (ConnectedComponents.coe_eq_coe'.1 e.symm)
    rwa [mul_inv_cancel, _root_.mul_comm] at this
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have all (x : 𝟙_ (Over (Sp k)) ⟶ G) : x ∈ H := by
    have := h H.index (Nat.one_le_iff_ne_zero.2 Subgroup.FiniteIndex.index_ne_zero)
    obtain ⟨z, hz⟩ := ((𝟙 G) ^ H.index : G ⟶ G).left.surjective (pt x)
    obtain ⟨y, -, rfl⟩ := (pt_mem_image_iff ((𝟙 G) ^ H.index) isClosed_univ x).1 ⟨z, trivial, hz⟩
    rw [MonObj.comp_pow, Category.comp_id]
    exact H.pow_index_mem y
  have hu : connectedComponent (pt (1 : 𝟙_ (Over (Sp k)) ⟶ G)) = Set.univ := by
    by_contra hne
    obtain ⟨x, hx⟩ := exists_pt_mem (isOpen_connectedComponent_of_noetherianSpace _).isClosed_compl
      (Set.nonempty_compl.2 hne)
    exact hx (all x)
  exact connectedSpace_iff_connectedComponent.2 ⟨_, hu⟩

theorem pow_comm {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (n : ℕ) :
    ((𝟙 G') ^ n : G' ⟶ G').left ≫ φ = φ ≫ ((𝟙 G) ^ n : G ⟶ G).left := by
  have e := congrArg (fun q => q.left) (map_pow (pushHom h G') (𝟙 G') n)
  have e' (x : Over.mk (G'.hom ≫ f) ⟶ G) : x ^ n = x ≫ (𝟙 G) ^ n := by
    rw [MonObj.comp_pow, Category.comp_id]
  rw [e'] at e
  refine Eq.trans e ?_
  change (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem isPullback_pow {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (n : ℕ) :
    IsPullback φ ((𝟙 G') ^ n : G' ⟶ G').left ((𝟙 G) ^ n : G ⟶ G).left φ := by
  refine IsPullback.of_bot ?_ (pow_comm h n).symm h.1
  rw [Over.w, Over.w]
  exact h.1

theorem surjective_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) (n : ℕ) (hn : 1 ≤ n) :
    Surjective ((𝟙 A) ^ n : A ⟶ A).left := by
  refine ⟨fun x => ?_⟩
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  let K := AlgebraicClosure (S.residueField (A.hom x))
  let t : Sp K ⟶ S := spMap (algebraMap (S.residueField (A.hom x)) K) ≫ S.fromSpecResidueField (A.hom x)
  have ht : A.hom x = t (IsLocalRing.closedPoint K) := by
    exact (Scheme.fromSpecResidueField_apply _ _).symm
  let B := (Over.pullback t).obj A
  have hB : IsAbelianScheme B :=
    { comm := inferInstance
      smooth := inferInstanceAs (Smooth (pullback.snd A.hom t))
      proper := inferInstanceAs (IsProper (pullback.snd A.hom t))
      geomConnected := inferInstanceAs (GeometricallyConnected (pullback.snd A.hom t)) }
  have hm : IsMonHom ((𝟙 B) ^ n : B ⟶ B) := by
    have := hB.comm
    clear hn
    induction n with
    | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (toUnit B ≫ η[B]))
    | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift ((𝟙 B) ^ n) (𝟙 B) ≫ μ[B]))
  have hs := (flat_and_surjective_of_isFinite_abelianEnd
    (fun _ _ f _ _ => (geometricallyIntegral_of_smooth_of_geometricallyConnected.1 f).1) K B hB ((𝟙 B) ^ n)
    hm (MulFiniteAny.isFinite_mulA K B hB n hn)).2
  obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback (.of_hasPullback A.hom t) x _ ht
  obtain ⟨z, rfl⟩ := ((𝟙 B) ^ n : B ⟶ B).left.surjective y
  exact ⟨pullback.fst A.hom t z, (congrArg (fun g => g z) (pow_comm (isGrpPullback_pullback A t) n)).symm.trans hy⟩

theorem isAbelianScheme_of_isDominant {S S' : Scheme.{0}} {B : Over S} {A : Over S'} [GrpObj B] [GrpObj A]
    [IsCommMonObj B] [Smooth B.hom] [IsProper B.hom] {f : S' ⟶ S} [IsDominant f] {φ : A.left ⟶ B.left}
    (h : IsGrpPullback A B f φ) (hA : IsAbelianScheme A) : IsAbelianScheme B := by
  have hd : DenseRange φ := by
    rw [DenseRange, ProperLimit.range_eq_of_isPullback h.1.flip]
    exact f.denseRange.preimage B.hom.isOpenMap
  have hs (n : ℕ) (hn : 1 ≤ n) : Surjective ((𝟙 B) ^ n : B ⟶ B).left := by
    have := surjective_pow A hA n hn
    have : IsProper (((𝟙 B) ^ n : B ⟶ B).left ≫ B.hom) := by rw [Over.w]; infer_instance
    have : IsProper ((𝟙 B) ^ n : B ⟶ B).left := IsProper.of_comp _ B.hom
    refine ⟨Set.range_eq_univ.1 ?_⟩
    rw [← ((𝟙 B) ^ n : B ⟶ B).left.isClosedMap.isClosed_range.closure_eq]
    refine (Dense.mono ?_ hd).closure_eq
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := ((𝟙 A) ^ n : A ⟶ A).left.surjective y
    exact ⟨φ z, (congrArg (fun g => g z) (pow_comm h n)).symm⟩
  refine ⟨‹_›, ‹_›, ‹_›, SemiAbelianCompare.geometricallyConnected_of_isAlgClosed _ fun k _ _ s => ?_⟩
  have : LocallyOfFiniteType ((Over.pullback s).obj B).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd B.hom s))
  have : QuasiCompact ((Over.pullback s).obj B).hom := inferInstanceAs (QuasiCompact (pullback.snd B.hom s))
  exact connectedSpace_of_surjective_pow ((Over.pullback s).obj B) fun n hn =>
    MorphismProperty.of_isPullback (isPullback_pow (isGrpPullback_pullback B s) n) (hs n hn)

theorem abelianScheme_descends_to_fg_subring :
    ∀ (R : Type) [CommRing R] (g : ℕ) (A : Over (Sp R)) [GrpObj A] (F : Finset R), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (φ : A.left ⟶ B.left), (F : Set R) ⊆ S ∧ Algebra.FiniteType ℤ S ∧
      IsAbelianScheme B ∧ SmoothOfRelativeDimension g B.hom ∧ IsGrpPullback A B (spMap S.subtype) φ := by
  intro R _ g A _ F hA hg
  have := hA.comm
  have := hA.proper
  obtain ⟨k, A₀, _, _, φ₀, hF, hk, _, _, _, h₀⟩ :=
    smooth_grpScheme_descends_to_fg_subring R A F hA.smooth inferInstance inferInstance
  have : IsNoetherianRing k := Algebra.FiniteType.isNoetherianRing ℤ k
  have h₁ : IsPullback φ₀ A.hom A₀.hom (spMap (algebraMap k R)) := h₀.1
  have : UniversallyClosed (pullback.snd A₀.hom (spMap (algebraMap k R))) := by
    rw [← h₁.isoPullback_inv_snd]
    infer_instance
  obtain ⟨s, hs⟩ := ProperLimit.exists_finset_isProper k R A₀.hom
  let S : Subalgebra k R := Algebra.adjoin k (s : Set R)
  let t : Sp S.toSubring ⟶ Sp k := spMap (algebraMap k S)
  have e : spMap S.toSubring.subtype ≫ t = spMap k.subtype := Spread.spMap_algHom_comp S.val
  obtain ⟨φ, hφ⟩ := GoodVal.exists_isGrpPullback_of_comp A₀ t (spMap S.toSubring.subtype) (e ▸ h₀)
  have hsm : Smooth ((Over.pullback t).obj A₀).hom := inferInstanceAs (Smooth (pullback.snd A₀.hom t))
  have : IsProper ((Over.pullback t).obj A₀).hom := hs
  have hd : IsDominant (spMap S.toSubring.subtype) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical S.toSubring.subtype).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]
      exact bot_le)⟩
  exact ⟨S.toSubring, (Over.pullback t).obj A₀, inferInstance, φ, fun x hx => S.algebraMap_mem ⟨x, hF hx⟩,
    SpreadGroup.finiteType_of_fg hk (Subalgebra.fg_adjoin_finset s), isAbelianScheme_of_isDominant hφ hA,
    smoothOfRelativeDimension_of_isPullback_isDominant _ _ _ _ _ _ _ _ g hφ.1 hd hsm hg, hφ⟩

end GlobalTheory.AbelianLimit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubringStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_descends_to_finitelyGenerated_subring : ∀ (R : Type) [CommRing R] (g : ℕ) (A : Over (Sp R)) [GrpObj A] (F : Finset R), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (φ : A.left ⟶ B.left), (F : Set R) ⊆ S ∧ Algebra.FiniteType ℤ S ∧
      IsAbelianScheme B ∧ SmoothOfRelativeDimension g B.hom ∧ IsGrpPullback A B (spMap S.subtype) φ := by
  first | exact @GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring | exact GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring | (intros; apply GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCompatFiniteIsometry
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.HeckeTrans

section Abstract

variable {R : Type} [CommRing R] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem mulVec_mem (S : Subring R) (u : Matrix m m S) (x : m → R) (hx : ∀ i, x i ∈ S) (i : m) :
    (u.map S.subtype).mulVec x i ∈ S := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  exact S.sum_mem fun k _ => S.mul_mem (u i k).2 (hx k)

theorem frame_inv (S : Subring R) (β : GL n R) (β' : GL m R) (c : n ≃ m) (U : GL m R) (u u' : Matrix m m S)
    (hu : U.val = u.map S.subtype) (hu' : (U⁻¹).val = u'.map S.subtype) (j : Matrix m n R)
    (hj : j * β.val = (β' * U).val.submatrix id c) :
    (∃ j' : Matrix n m R, j * j' = 1 ∧ j' * j = 1) ∧
      ∀ x : n → R, (∀ i, (β⁻¹).val.mulVec x i ∈ S) ↔ ∀ i, (β'⁻¹).val.mulVec (j.mulVec x) i ∈ S := by
  have hj2 : j = (β' * U).val.submatrix id c * (β⁻¹).val := by
    rw [← hj, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  refine ⟨⟨β.val * ((β' * U)⁻¹).val.submatrix c id, ?_, ?_⟩, fun x => ?_⟩
  · rw [← Matrix.mul_assoc, hj, Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_id_id]
  · have h1 : ((β' * U)⁻¹).val.submatrix c id * (β' * U).val.submatrix id c = 1 := by
      have := Matrix.submatrix_mul_equiv ((β' * U)⁻¹).val (β' * U).val c (Equiv.refl m) c
      rw [Units.inv_mul, Matrix.submatrix_one_equiv] at this
      exact this
    rw [hj2, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.submatrix _ _ _), h1, Matrix.one_mul, Units.mul_inv]
  · have h1 : j.mulVec x = (β' * U).val.mulVec ((β⁻¹).val.mulVec x ∘ c.symm) := by
      rw [hj2, ← Matrix.mulVec_mulVec, Matrix.submatrix_mulVec_equiv]
      rfl
    have h2 : (β'⁻¹).val.mulVec (j.mulVec x) = U.val.mulVec ((β⁻¹).val.mulVec x ∘ c.symm) := by
      rw [h1, Matrix.mulVec_mulVec, Units.val_mul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [h2]
    constructor
    · intro h i
      rw [hu]
      exact mulVec_mem S u _ (fun k => h _) i
    · intro h i
      have h3 := mulVec_mem S u' _ h (c i)
      rw [← hu', Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Function.comp_apply, Equiv.symm_apply_apply] at h3
      exact h3

variable {f : R} {J : Matrix m n R} {J' : Matrix n m R} {M : Matrix n n R} {M' : Matrix m m R}

omit [DecidableEq n] in
theorem conj_eq (h1 : J * J' = 1) (hc : M' * J = J * M) : M' = J * M * J' := by
  rw [← hc, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem conj_inv (h1 : J * J' = 1) (h2 : J' * J = 1) (hc : M' * J = J * M) : M * J' = J' * M' := by
  rw [conj_eq h1 hc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem supp_conj (h1 : J * J' = 1) (hc : M' * J = J * M) (hs : f • (M - 1) = M - 1) : f • (M' - 1) = M' - 1 := by
  have hs2 : M' - 1 = J * (M - 1) * J' := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1, ← conj_eq h1 hc]
  rw [hs2, ← Matrix.smul_mul, ← Matrix.mul_smul, hs]

theorem det_conj (h1 : J * J' = 1) (h2 : J' * J = 1) (hc : M' * J = J * M) : M'.det = M.det := by
  rw [conj_eq h1 hc]
  exact Matrix.det_conj_of_mul_eq_one h1 h2

variable {L : AddSubgroup (n → R)} {L' : AddSubgroup (m → R)}

omit [DecidableEq n] in
theorem lat_inv (h1 : J * J' = 1) (hL : ∀ y, f • y ∈ L ↔ f • J.mulVec y ∈ L') (y : m → R) :
    f • y ∈ L' ↔ f • J'.mulVec y ∈ L := by
  rw [hL, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

omit [DecidableEq n] in
theorem stab_conj (hf : f * f = f) (h1 : J * J' = 1) (hc : M' * J = J * M) (hL : ∀ y, f • y ∈ L ↔ f • J.mulVec y ∈ L')
    (loc' : ∀ y ∈ L', f • y ∈ L') (ha : ∀ y ∈ L, f • M.mulVec y ∈ L) : ∀ y ∈ L', f • M'.mulVec y ∈ L' := by
  intro y hy
  have h3 := ha _ ((lat_inv h1 hL y).1 (loc' y hy))
  rw [hL, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_smul, hf, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ← conj_eq h1 hc] at h3
  exact h3

omit [DecidableEq n] in
theorem cont_conj {p : R} (hf : f * f = f) (h1 : J * J' = 1) (hc : M' * J = J * M) (hL : ∀ y, f • y ∈ L ↔ f • J.mulVec y ∈ L')
    (loc : ∀ y ∈ L, f • y ∈ L) (loc' : ∀ y ∈ L', f • y ∈ L') (hb : ∀ y ∈ L, ∃ z ∈ L, f • p • y = f • M.mulVec z) :
    ∀ y ∈ L', ∃ z ∈ L', f • p • y = f • M'.mulVec z := by
  intro y hy
  obtain ⟨z, hz, h3⟩ := hb _ ((lat_inv h1 hL y).1 (loc' y hy))
  refine ⟨f • J.mulVec z, (hL z).1 (loc z hz), ?_⟩
  have h4 := congrArg J.mulVec h3
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, h1,
    Matrix.one_mulVec, Matrix.mulVec_mulVec, ← hc, smul_comm p, smul_smul, hf] at h4
  rw [h4, Matrix.mulVec_smul, smul_smul, hf, Matrix.mulVec_mulVec]

variable {R' : Type} [CommRing R']

omit [Fintype n] in
theorem supp_map_iff (φ : R' →+* R) (g : R') (A : Matrix n n R') :
    φ g • (A.map φ - 1) = A.map φ - 1 ↔ ∀ i j, φ (g * (A - 1) i j) = φ ((A - 1) i j) := by
  have h : ∀ i j, φ ((A - 1) i j) = (A.map φ - 1) i j := by
    intro i j
    rw [← Matrix.map_one φ φ.map_zero φ.map_one]
    simp only [Matrix.sub_apply, Matrix.map_apply, map_sub]
  simp only [map_mul, h]
  rw [← Matrix.ext_iff]
  rfl

omit [DecidableEq m] in
theorem map_mul_one (φ : R' →+* R) {A : Matrix n m R'} {B : Matrix m n R'} (h : A * B = 1) : A.map φ * B.map φ = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ φ.map_zero φ.map_one]

omit [DecidableEq m] [DecidableEq n] in
theorem map_conj (φ : R' →+* R) {A : Matrix m m R'} {B : Matrix m n R'} {C : Matrix n n R'} (h : A * B = B * C) :
    A.map φ * B.map φ = B.map φ * C.map φ := by
  rw [← Matrix.map_mul, ← Matrix.map_mul, h]

omit [DecidableEq m] [DecidableEq n] [Fintype m] in
theorem mulVec_map_inv (φ : R' →+* R) (ψ : R →+* R') (h : ∀ x, ψ (φ x) = x) (j : Matrix m n R') (y : n → R) :
    (j.mulVec fun a => ψ (f * y a)) = fun a => ψ (f * (j.map φ).mulVec y a) := by
  funext a
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum, map_sum, map_mul, h]
  exact Finset.sum_congr rfl fun b _ => mul_left_comm _ _ _

theorem map_mul_det (φ : R' →+* R) (e : R') (A : Matrix m m R') (B : Matrix n n R') (h : (A.map φ).det = (B.map φ).det) :
    φ (e * A.det) = φ (e * B.det) := by
  rw [map_mul, map_mul, RingHom.map_det, RingHom.map_det]
  exact congrArg (φ e * ·) h

end Abstract

variable {D : D7}

theorem finMat_eq (V : HSp D) (g : GA D V) : finMat D.sp.cm.sig V.gram g = (mt V g).map (finPart D) := rfl

theorem inf_eq {V : HSp D} {g : GA D V} (hg : g ∈ GfC V) : (mt V g).map (infPart D) = 1 :=
  congrArg Units.val (MonoidHom.mem_ker.1 hg)

theorem idem_det {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {m n : ℕ} (A : Matrix (Fin m) (Fin m) (Formalism.L2.Theta.AE D))
    (B : Matrix (Fin n) (Fin n) (Formalism.L2.Theta.AE D)) (h : (A.map (finPart D)).det = (B.map (finPart D)).det) :
    e * A.det = e * B.det := by
  refine GlobalTheory.SplitScalar.adele_ext ?_ (map_mul_det (finPart D) e A B h)
  simp only [RingHom.map_mul, GlobalTheory.SplitScalar.infPart_splitIdem he, zero_mul]

theorem suppAt_iff (e : Formalism.L2.Theta.AE D) {V : HSp D} {α : GA D V} (hα : α ∈ GfC V) :
    SuppAt e V α ↔ finPart D (e + cA D e) • (finMat D.sp.cm.sig V.gram α - 1) = finMat D.sp.cm.sig V.gram α - 1 := by
  rw [finMat_eq, supp_map_iff]
  refine ⟨fun hs i j => congrArg (finPart D) (hs i j), fun hs i j => ?_⟩
  have hs4 := (supp_map_iff (infPart D) (e + cA D e) (mt V α)).1 (by rw [inf_eq hα, sub_self, smul_zero])
  exact GlobalTheory.SplitScalar.adele_ext (hs4 i j) (hs i j)

theorem transfer {V V' : HSp D} {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e)
    (J : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))
    (J' : Matrix (Fin V.rank) (Fin V'.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))
    (h1 : HMul.hMul J J' = 1) (h2 : HMul.hMul J' J = 1) {α : GA D V} {α' : GA D V'} (hα' : α' ∈ GfC V')
    (hc : HMul.hMul (finMat D.sp.cm.sig V'.gram α') J = HMul.hMul J (finMat D.sp.cm.sig V.gram α))
    (hL : ∀ y, finPart D e • y ∈ Formalism.L2.NTheta.LamHat V ↔ finPart D e • J.mulVec y ∈ Formalism.L2.NTheta.LamHat V')
    (loc : ∀ y ∈ Formalism.L2.NTheta.LamHat V, finPart D e • y ∈ Formalism.L2.NTheta.LamHat V)
    (loc' : ∀ y ∈ Formalism.L2.NTheta.LamHat V', finPart D e • y ∈ Formalism.L2.NTheta.LamHat V')
    {ϖ : D.host.E} {k : ℕ} (h : Formalism.L2.NTheta.IsHeckeElt V e ϖ k α) : Formalism.L2.NTheta.IsHeckeElt V' e ϖ k α' := by
  obtain ⟨hα, hs, ha, hb, u, u', hu, hu', huu, hd⟩ := h
  have hf : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, he.1]
  refine ⟨hα', ?_, stab_conj hf h1 hc hL loc' ha, cont_conj hf h1 hc hL loc loc' hb, u, u', hu, hu', huu, ?_⟩
  · exact (suppAt_iff e hα').2 (supp_conj h1 hc ((suppAt_iff e hα).1 hs))
  · exact (idem_det he _ _ (det_conj h1 h2 hc)).trans hd

def unswap (D : D7) : EAf D →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).symm.toAlgHom.toRingHom

theorem unswap_swap (x) : unswap D (swapAE D x) = x :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).symm_apply_apply x

theorem swap_unswap (x) : swapAE D (unswap D x) = x :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).apply_symm_apply x

theorem finE_unswap (V : HSp D) (g : GA D V) : (finE V g).val.map (unswap D) = finMat D.sp.cm.sig V.gram g := by
  ext i j
  exact unswap_swap _

end GlobalTheory.HeckeTrans

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormNegOnOrthogonalOfPositiveIndexOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormNegOnOrthogonalOfPositiveIndexOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.SignatureOneForms

theorem form_re_eq_sum {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (v : Fin n → ℂ) :
    (star v ⬝ᵥ A *ᵥ v).re = ∑ i, hA.eigenvalues i *
      Complex.normSq ((star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) i) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set d : Fin n → ℂ := RCLike.ofReal ∘ hA.eigenvalues with hd
  set c := star U *ᵥ v with hc
  have hspec : A = U * diagonal d * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, hU, hd]
  have h0 := congrArg (fun M => star v ⬝ᵥ M *ᵥ v) hspec
  have h1 : star v ⬝ᵥ A *ᵥ v = star c ⬝ᵥ (diagonal d *ᵥ c) := by
    rw [h0, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, hc, star_mulVec]
    simp [Matrix.star_eq_conjTranspose]
  rw [h1]
  simp only [dotProduct, mulVec_diagonal, Complex.re_sum, hd, Function.comp_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem form_re_neg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hdet : A.det ≠ 0)
    (i₀ : Fin n) (hpos : ∀ i, 0 < hA.eigenvalues i → i = i₀) (v : Fin n → ℂ) (hv : v ≠ 0)
    (hv0 : (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) i₀ = 0) :
    (star v ⬝ᵥ A *ᵥ v).re < 0 := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set c := star U *ᵥ v with hc
  have hne : ∀ i, hA.eigenvalues i ≠ 0 := by
    intro i hi
    apply hdet
    rw [hA.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have hcne : c ≠ 0 := by
    intro h0
    apply hv
    have : U *ᵥ c = v := by
      rw [hc, mulVec_mulVec, hU, Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2, one_mulVec]
    rw [← this, h0, mulVec_zero]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hcne
  have hji : j ≠ i₀ := by
    rintro rfl
    exact hj hv0
  have hjneg : hA.eigenvalues j < 0 :=
    lt_of_le_of_ne (not_lt.mp fun h => hji (hpos j h)) (hne j)
  rw [form_re_eq_sum hA v]
  have key : ∑ i, hA.eigenvalues i * Complex.normSq (c i) < ∑ _i : Fin n, (0 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro i _
      by_cases hi : i = i₀
      · subst hi
        simp [hv0]
      · have : hA.eigenvalues i ≤ 0 := not_lt.mp fun h => hi (hpos i h)
        nlinarith [Complex.normSq_nonneg (c i)]
    · refine ⟨j, Finset.mem_univ j, ?_⟩
      exact mul_neg_of_neg_of_pos hjneg (Complex.normSq_pos.mpr hj)
  simpa using key

end GlobalTheory.SignatureOneForms

namespace GlobalTheory

theorem re_form_neg_of_orth_of_sigPosH_eq_one : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian), A.det ≠ 0 → sigPosH hA = 1 → ∀ x y : Fin n → ℂ, 0 < (star x ⬝ᵥ A *ᵥ x).re → star x ⬝ᵥ A *ᵥ y = 0 → y ≠ 0 → (star y ⬝ᵥ A *ᵥ y).re < 0 := by
  intro n A hA hdet hsig x y hx hxy hy
  unfold sigPosH at hsig
  obtain ⟨⟨i₀, hi₀⟩, huniq⟩ := Fintype.card_eq_one_iff.mp hsig
  have hpos : ∀ i, 0 < hA.eigenvalues i → i = i₀ := fun i h => congrArg Subtype.val (huniq ⟨i, h⟩)
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hyx : star y ⬝ᵥ A *ᵥ x = 0 := by
    have h := congrArg star hxy
    rw [star_zero] at h
    rw [← h, star_dotProduct, star_mulVec, hA.eq, ← dotProduct_mulVec]
  by_contra hQ
  push_neg at hQ
  set a₀ := (star U *ᵥ x) i₀ with ha₀
  set b₀ := (star U *ᵥ y) i₀ with hb₀
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  by_cases ha : a₀ = 0
  · exact absurd (GlobalTheory.SignatureOneForms.form_re_neg hA hdet i₀ hpos x hx0 ha) (not_lt.mpr hx.le)
  set w := b₀ • x - a₀ • y with hw
  have hw0 : (star U *ᵥ w) i₀ = 0 := by
    simp only [hw, mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← ha₀, ← hb₀]
    ring
  have hQw : star w ⬝ᵥ A *ᵥ w = (Complex.normSq b₀ : ℂ) * (star x ⬝ᵥ A *ᵥ x)
      + (Complex.normSq a₀ : ℂ) * (star y ⬝ᵥ A *ᵥ y) := by
    simp only [hw, star_sub, star_smul, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, hxy, hyx, smul_eq_mul, Complex.normSq_eq_conj_mul_self]
    simp only [RCLike.star_def]
    ring
  by_cases hw' : w = 0
  · have h1 : star x ⬝ᵥ A *ᵥ w = b₀ * (star x ⬝ᵥ A *ᵥ x) := by
      simp [hw, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hxy]
    rw [hw', mulVec_zero, dotProduct_zero] at h1
    have hQx : star x ⬝ᵥ A *ᵥ x ≠ 0 := fun h => by rw [h] at hx; simp at hx
    have hb : b₀ = 0 := by
      rcases mul_eq_zero.mp h1.symm with h | h
      · exact h
      · exact absurd h hQx
    have : a₀ • y = 0 := by
      have hw2 : b₀ • x - a₀ • y = 0 := hw ▸ hw'
      rw [hb, zero_smul, zero_sub, neg_eq_zero] at hw2
      exact hw2
    exact hy ((smul_eq_zero.mp this).resolve_left ha)
  · have hneg := GlobalTheory.SignatureOneForms.form_re_neg hA hdet i₀ hpos w hw' hw0
    rw [hQw, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul] at hneg
    nlinarith [Complex.normSq_nonneg a₀, Complex.normSq_nonneg b₀,
      mul_nonneg (Complex.normSq_nonneg b₀) hx.le, mul_nonneg (Complex.normSq_nonneg a₀) hQ]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormNegOnOrthogonalOfPositiveIndexOneStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianForm_neg_on_orthogonal_of_positiveIndex_one : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian), A.det ≠ 0 → sigPosH hA = 1 → ∀ x y : Fin n → ℂ, 0 < (star x ⬝ᵥ A *ᵥ x).re → star x ⬝ᵥ A *ᵥ y = 0 → y ≠ 0 → (star y ⬝ᵥ A *ᵥ y).re < 0 := by
  first | exact @GlobalTheory.re_form_neg_of_orth_of_sigPosH_eq_one | exact GlobalTheory.re_form_neg_of_orth_of_sigPosH_eq_one | (intros; apply GlobalTheory.re_form_neg_of_orth_of_sigPosH_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceHalfHeisenbergInvariantForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceHalfHeisenbergInvariantForm
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfCoinv

section Abstract

variable {G M : Type} [AddCommGroup G] [AddCommGroup M] [Module ℂ M] {Y : AddSubgroup G} {ρ : G → M →ₗ[ℂ] M}

theorem exists_sum_eq_zero (hadd : ∀ x ∈ Y, ∀ x' ∈ Y, ∀ f, ρ x (ρ x' f) = ρ (x + x') f) (h0 : ∀ f, ρ 0 f = f) {Θ : Set M}
    (hsm : ∀ u ∈ Y, ∀ g ∈ Θ, ∃ k : ℕ, 0 < k ∧ ρ (k • u) g = g) {m : M}
    (hm : m ∈ Submodule.span ℂ {m | ∃ u ∈ Y, ∃ g ∈ Θ, m = ρ u g - g}) :
    ∃ (ι : Type) (s : Finset ι) (y : ι → G), (∀ i, y i ∈ Y) ∧ (∃ i ∈ s, y i = 0) ∧ ∑ i ∈ s, ρ (y i) m = 0 := by
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨u, hu, g, hg, rfl⟩ := hm
    obtain ⟨k, hk, h⟩ := hsm u hu g hg
    refine ⟨ℕ, Finset.range k, fun j => j • u, fun j => Y.nsmul_mem hu j,
      ⟨0, Finset.mem_range.2 hk, zero_smul _ _⟩, ?_⟩
    have e : ∀ j : ℕ, ρ (j • u) (ρ u g - g) = ρ ((j + 1) • u) g - ρ (j • u) g := fun j => by
      rw [map_sub, hadd _ (Y.nsmul_mem hu j) _ hu, succ_nsmul]
    simp only [e]
    rw [Finset.sum_range_sub (fun j : ℕ => ρ (j • u) g), h, zero_smul, h0, sub_self]
  | zero => exact ⟨Unit, Finset.univ, fun _ => 0, fun _ => Y.zero_mem, ⟨(), Finset.mem_univ _, rfl⟩, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨ι, s, y, hy, ⟨i, hi, hi0⟩, h⟩ := ha
    obtain ⟨κ, t, z, hz, ⟨j, hj, hj0⟩, h'⟩ := hb
    refine ⟨ι × κ, s ×ˢ t, fun p => y p.1 + z p.2, fun p => Y.add_mem (hy _) (hz _),
      ⟨(i, j), Finset.mem_product.2 ⟨hi, hj⟩, by simp only [hi0, hj0, add_zero]⟩, ?_⟩
    simp only [map_add (f := _), Finset.sum_add_distrib]
    have e1 : ∑ p ∈ s ×ˢ t, ρ (y p.1 + z p.2) a = 0 := by
      rw [Finset.sum_product_right]
      refine Finset.sum_eq_zero fun q _ => ?_
      have : ∀ p, ρ (y p + z q) a = ρ (z q) (ρ (y p) a) := fun p => by rw [hadd _ (hz _) _ (hy _), add_comm]
      simp only [this]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, h, map_zero]
    have e2 : ∑ p ∈ s ×ˢ t, ρ (y p.1 + z p.2) b = 0 := by
      rw [Finset.sum_product]
      refine Finset.sum_eq_zero fun p _ => ?_
      have : ∀ q, ρ (y p + z q) b = ρ (y p) (ρ (z q) b) := fun q => by rw [hadd _ (hy _) _ (hz _)]
      simp only [this]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, h', map_zero]
    rw [e1, e2, add_zero]
  | smul c a _ ha =>
    obtain ⟨ι, s, y, hy, hi, h⟩ := ha
    refine ⟨ι, s, y, hy, hi, ?_⟩
    simp only [map_smul]
    rw [← Finset.smul_sum, h, smul_zero]

theorem exists_separating {B : G → G → ℂ} (hcomm : ∀ u y f, ρ u (ρ y f) = B u y • ρ y (ρ u f)) {f₀ : M} (hf : f₀ ≠ 0)
    (hd : ∀ y ∈ Y, ρ y f₀ = f₀ ∨ ∃ u, ρ u f₀ = f₀ ∧ B u y ≠ 1) {ι : Type} (s : Finset ι) {y : ι → G}
    (hy : ∀ i, y i ∈ Y) : ∃ P : M →ₗ[ℂ] M, P f₀ ≠ 0 ∧ ∀ i ∈ s, ρ (y i) f₀ = f₀ ∨ P (ρ (y i) f₀) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨LinearMap.id, hf, fun _ h => absurd h (Finset.notMem_empty _)⟩
  | insert j s _ ih =>
    obtain ⟨P, hP, h⟩ := ih
    rcases hd _ (hy j) with h1 | ⟨u, hu, hB⟩
    · exact ⟨P, hP, fun i hi => (Finset.mem_insert.1 hi).elim (fun e => Or.inl (e ▸ h1)) (h i)⟩
    · refine ⟨P ∘ₗ (ρ u - B u (y j) • LinearMap.id), ?_, fun i hi => ?_⟩
      · have : (ρ u - B u (y j) • (LinearMap.id : M →ₗ[ℂ] M)) f₀ = (1 - B u (y j)) • f₀ := by
          rw [LinearMap.sub_apply, hu, sub_smul, one_smul]; rfl
        rw [LinearMap.comp_apply, this, map_smul]
        exact smul_ne_zero (sub_ne_zero.2 hB.symm) hP
      · have : (ρ u - B u (y j) • (LinearMap.id : M →ₗ[ℂ] M)) (ρ (y i) f₀) =
            (B u (y i) - B u (y j)) • ρ (y i) f₀ := by
          rw [LinearMap.sub_apply, hcomm, hu, sub_smul]; rfl
        rw [LinearMap.comp_apply, this, map_smul]
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact Or.inr (by rw [sub_self, zero_smul])
        · exact (h i hi).imp_right fun e => by rw [e, smul_zero]

theorem exists_form {B : G → G → ℂ} (hadd : ∀ x ∈ Y, ∀ x' ∈ Y, ∀ f, ρ x (ρ x' f) = ρ (x + x') f) (h0 : ∀ f, ρ 0 f = f)
    (hcomm : ∀ u y f, ρ u (ρ y f) = B u y • ρ y (ρ u f)) {Θ : Set M}
    (hsm : ∀ u ∈ Y, ∀ g ∈ Θ, ∃ k : ℕ, 0 < k ∧ ρ (k • u) g = g) {f₀ : M} (hf : f₀ ≠ 0)
    (hd : ∀ y ∈ Y, ρ y f₀ = f₀ ∨ ∃ u, ρ u f₀ = f₀ ∧ B u y ≠ 1) :
    ∃ ℓ : M →ₗ[ℂ] ℂ, (∀ u ∈ Y, ∀ g ∈ Θ, ℓ (ρ u g) = ℓ g) ∧ ℓ f₀ ≠ 0 := by
  classical
  have hn : f₀ ∉ Submodule.span ℂ {m | ∃ u ∈ Y, ∃ g ∈ Θ, m = ρ u g - g} := fun hm => by
    obtain ⟨ι, s, y, hy, ⟨i, hi, hi0⟩, h⟩ := exists_sum_eq_zero hadd h0 hsm hm
    obtain ⟨P, hP, hs⟩ := exists_separating hcomm hf hd s hy
    have e : ∑ j ∈ s, P (ρ (y j) f₀) = ∑ j ∈ s with ρ (y j) f₀ = f₀, P f₀ := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun j hj => ?_
      split_ifs with h1
      · rw [h1]
      · exact (hs j hj).resolve_left h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, h, map_zero, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ] at e
    refine smul_ne_zero (Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨i, ?_⟩)) hP e.symm
    exact Finset.mem_filter.2 ⟨hi, by rw [hi0, h0]⟩
  obtain ⟨ℓ, h1, h2⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  refine ⟨ℓ, fun u hu g hg => ?_, h1⟩
  have : ℓ (ρ u g - g) ∈ (⊥ : Submodule ℂ ℂ) :=
    h2 ▸ Submodule.mem_map_of_mem (Submodule.subset_span ⟨u, hu, g, hg, rfl⟩)
  rwa [Submodule.mem_bot, map_sub, sub_eq_zero] at this

end Abstract

open GlobalTheory.PlaceModel

theorem exists_invariant_form : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (e : AE D), IsSplitIdem D e → ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧ ∃ f, IsThetaFunO ψ S T f ∧ ℓ f ≠ 0 := by
  intro D ψ hψ S T e hs
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have hc : ∀ (V : HSp D) τ, ∃ s, IsCartanInv (gramAt D V τ) s := fun V τ =>
    GlobalTheory.Mem.ThetaNonzero.exists_isCartanInv (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ)
      (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)
  choose s hcs using hc
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ S T (s S) (s T) (hcs S) (hcs T) _ _
    (isSelfDualC_latFrame S) (isSelfDualC_latFrame T)
  obtain ⟨hth, hvac, -⟩ := hf 1
  simp only [one_mul] at hth hvac
  have hs' := GlobalTheory.SplitScalar.isSplitIdem_conj hs
  obtain ⟨he, hec, v, ε, hε, heq⟩ := id hs
  have he' : cA D e * cA D e = cA D e := hs'.1
  have heε : algebraMap (AF D.host.F) (AE D) ε * e = e := by rw [← heq]; linear_combination he + hec
  have heε' : algebraMap (AF D.host.F) (AE D) ε * cA D e = cA D e := by rw [← heq]; linear_combination he' + hec
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ (isSelfDualC_latFrame S)
    (isSelfDualC_latFrame T)).1
  have c2 : cA D (cA D e) * cA D e = 0 := by rw [GlobalTheory.LatVac.cA_cA, hec]
  obtain ⟨ℓ, h1, h2⟩ := exists_form (Y := half S T (cA D e)) (ρ := heisL S T ψ)
    (B := fun x y => ψ (symplO S T x y)) (Θ := {g | IsThetaFunO ψ S T g}) (heisL_half S T ψ c2)
    (GlobalTheory.SplitScalar.heisO_zero ψ S T) (heisL_comm S T ψ) (fun u hu g hg => by
      obtain ⟨U, hU, h⟩ := hg.level
      obtain ⟨k, hk, hkU⟩ := GlobalTheory.SplitScalar.exists_nsmul_mem U hU (infPart_half hε heε' hu)
      exact ⟨k, hk, h _ hkU (infPart_half hε heε' ((half S T (cA D e)).nsmul_mem hu k))⟩) f0 (fun y hy => by
      by_cases h : ∀ u ∈ (latO S T (latFrame S) (latFrame T) fun w => w = v) ⊓ half S T e, ψ (symplO S T u y) = 1
      · have := mem_of_dual hε hdual he' heε' (by rwa [GlobalTheory.LatVac.cA_cA]) y hy fun u hu => by
          rw [GlobalTheory.LatVac.cA_cA] at hu
          rw [symplO_skew, AddChar.map_neg_eq_inv, h u hu, inv_one]
        exact Or.inl (hvac.2 _ hs' y (latO_le_top _ this.1) ((isHalf_iff S T).2 hy))
      · push_neg at h
        obtain ⟨u, hu, h⟩ := h
        exact Or.inr ⟨u, hvac.2 _ hs u (latO_le_top _ hu.1) ((isHalf_iff S T).2 hu.2), h⟩)
  exact ⟨ℓ, fun u hu g hg => h1 u ((isHalf_iff S T).1 hu) g hg, f, hth, h2⟩

end GlobalTheory.HalfCoinv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceHalfHeisenbergInvariantFormStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_split_place_half_heisenberg_invariant_form : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (e : AE D), IsSplitIdem D e → ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧ ∃ f, IsThetaFunO ψ S T f ∧ ℓ f ≠ 0 := by
  first | exact @GlobalTheory.HalfCoinv.exists_invariant_form | exact GlobalTheory.HalfCoinv.exists_invariant_form | (intros; apply GlobalTheory.HalfCoinv.exists_invariant_form <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedConjugatePlaceUniformiser
open IsDedekindDomain NumberField

namespace GlobalTheory.FixedPrime

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem le_of_under_le (P : Ideal (𝓞 E)) [hP : P.IsPrime]
    (h : ∀ x : 𝓞 E, IsCMField.ringOfIntegersComplexConj E x ∈ P → x ∈ P) (Q : Ideal (𝓞 E))
    (hQ : Q.under (𝓞 (maximalRealSubfield E)) ≤ P.under (𝓞 (maximalRealSubfield E))) : Q ≤ P := by
  intro y hy
  obtain ⟨s, hs⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff E
    (y * IsCMField.ringOfIntegersComplexConj E y)).1 (by
      rw [map_mul, mul_comm]
      congr 1
      ext; simp)
  have h1 : s ∈ Q.under (𝓞 (maximalRealSubfield E)) := by
    rw [Ideal.under_def, Ideal.mem_comap, hs]
    exact Q.mul_mem_right _ hy
  have h2 := hQ h1
  rw [Ideal.under_def, Ideal.mem_comap, hs] at h2
  exact (hP.mem_or_mem h2).elim id (h y)

theorem isInertAt_under [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (P : HeightOneSpectrum (𝓞 E))
    (h : ∀ x : 𝓞 E, IsCMField.ringOfIntegersComplexConj E x ∈ P.asIdeal → x ∈ P.asIdeal) :
    Formalism.UG.IsInertAt (maximalRealSubfield E) E (P.under (𝓞 (maximalRealSubfield E))) P := by
  classical
  haveI := P.isPrime
  haveI : Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) P.asIdeal :=
    Algebra.unramified_iff_forall.1 inferInstance ⟨P.asIdeal, P.isPrime⟩
  set v := P.under (𝓞 (maximalRealSubfield E)) with hv
  have hva : v.asIdeal = P.asIdeal.under (𝓞 (maximalRealSubfield E)) := rfl
  have hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective _ _
  unfold Formalism.UG.IsInertAt
  rw [hva]
  have hle : (P.asIdeal.under (𝓞 (maximalRealSubfield E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≤ P.asIdeal := Ideal.map_comap_le
  have h1 : Ideal.ramificationIdx' (P.asIdeal.under (𝓞 (maximalRealSubfield E))) P.asIdeal = 1 := by
    letI := Localization.AtPrime.algebraOfLiesOver (P.asIdeal.under (𝓞 (maximalRealSubfield E))) P.asIdeal
    exact (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff P.ne_bot hle).2
      ((Algebra.isUnramifiedAt_iff_map_eq (𝓞 (maximalRealSubfield E))
        (P.asIdeal.under (𝓞 (maximalRealSubfield E))) P.asIdeal).1 ‹_›).2
  have h2 : ¬ (P.asIdeal.under (𝓞 (maximalRealSubfield E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≤ P.asIdeal ^ 2 :=
    fun h => (Ideal.ramificationIdx'_ne_one_iff hle).2 h h1
  set I := Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))
    (P.asIdeal.under (𝓞 (maximalRealSubfield E))) with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.map_eq_bot_iff_of_injective hinj]
    exact v.ne_bot
  have hfac : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors I, p = P.asIdeal := by
    intro p hp
    obtain ⟨hpp, hpl⟩ := (Ideal.mem_normalizedFactors_iff hI0).1 hp
    have hp0 : p ≠ ⊥ := fun h0 => hI0 (le_bot_iff.1 (h0 ▸ hpl))
    refine (hpp.isMaximal hp0).eq_of_le P.isPrime.ne_top (le_of_under_le P.asIdeal h p ?_)
    exact (v.isMaximal.eq_of_le (Ideal.comap_ne_top _ hpp.ne_top)
      (Ideal.map_le_iff_le_comap.1 hpl)).ge
  obtain ⟨n, hn⟩ : ∃ n, I = P.asIdeal ^ n := by
    refine ⟨Multiset.card (UniqueFactorizationMonoid.normalizedFactors I), ?_⟩
    conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI0]
    rw [Multiset.eq_replicate_card.2 hfac, Multiset.prod_replicate, Multiset.card_replicate]
  rcases n with _ | _ | n
  · exfalso
    rw [hn, pow_zero, Ideal.one_eq_top, top_le_iff] at hle
    exact P.isPrime.ne_top hle
  · simpa using hn
  · exact absurd (hn ▸ Ideal.pow_le_pow_right (by omega)) h2

theorem exists_isUnramInv [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : HeightOneSpectrum (𝓞 E))
    (h : Formalism.UG.IsInertAt (maximalRealSubfield E) E v P) :
    ∃ (σ : P.adicCompletion E →+* P.adicCompletion E) (ϖ : P.adicCompletion E),
      (∀ x : E, σ (algebraMap E (P.adicCompletion E) x) =
        algebraMap E (P.adicCompletion E) (IsCMField.complexConj E x)) ∧
      Formalism.UG.IsUnramInv ϖ σ (Ideal.absNorm v.asIdeal) := by
  obtain ⟨σ, ϖ, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.InertConj.exists_conj_completion E v P h
  refine ⟨σ, ϖ, h1, h2, h3, h5, h6, h4, ?_, ?_⟩
  · have a : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    have b : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    omega
  · have hN : Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
      rw [← show Ideal.map _ v.asIdeal = P.asIdeal from h, Ideal.absNorm_algebraMap,
        ← Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E]
      congr 1
      exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)
        (𝓞 E) E).symm
    rw [← hN]
    exact Formalism.UG.P.tjcosets_card_residue P

end CM

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Formalism.IndefR.Links GlobalTheory.SphPar
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.FixedPrime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairHermitianFormInvertibleSimilitude
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairHermitianFormInvertibleSimilitude
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem pair_form_laws : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F),
    (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)).IsHermitian ∧
    (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)).det ≠ 0 ∧
    (G.psi v P.γ)ᴴ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) * G.psi v P.γ =
      ((P.c : ℚ) : ℂ) • (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G P v
  have hgu : IsUnit (G.gram v).det := isUnit_iff_ne_zero.mpr (G.gram_det v)
  have hgg : G.gram v * (G.gram v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  have hgg' : (G.gram v)⁻¹ * G.gram v = 1 := Matrix.nonsing_inv_mul _ hgu

  have hH : ∀ x : G.C, (G.psi v x)ᴴ = G.gram v * G.psi v (sh G x) * (G.gram v)⁻¹ := by
    intro x
    have e : G.psi v (sh G x) = (G.gram v)⁻¹ * (G.psi v x)ᴴ * G.gram v := G.psi_star v x
    rw [e, ← mul_assoc, ← mul_assoc, hgg, one_mul, mul_assoc, hgg, mul_one]

  have hshb : sh G ((P.β⁻¹ : G.Cˣ) : G.C) = ((P.β⁻¹ : G.Cˣ) : G.C) := by
    have h1 : sh G ((P.β⁻¹ : G.Cˣ) : G.C) * sh G (P.β : G.C) = 1 := by
      simp only [sh]
      rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]
    rw [P.sym] at h1
    calc sh G ((P.β⁻¹ : G.Cˣ) : G.C)
        = sh G ((P.β⁻¹ : G.Cˣ) : G.C) * (P.β : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h1, one_mul]

  have hu : sh G (P.γ : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ =
      algebraMap ℚ G.C (P.c : ℚ) * ((P.β⁻¹ : G.Cˣ) : G.C) := by
    apply (Units.mul_right_inj (P.γ * P.β)).mp
    rw [Units.val_mul, ← Algebra.smul_def]
    calc (P.γ : G.C) * P.β * (sh G (P.γ : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ)
        = ((P.γ : G.C) * P.β * sh G (P.γ : G.C)) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ := by
          simp only [mul_assoc]
      _ = (P.c : ℚ) • ((P.β : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ) := by
          rw [P.sim, ← Algebra.smul_def]; simp only [smul_mul_assoc]
      _ = (P.c : ℚ) • ((P.γ : G.C) * P.β * ((P.β⁻¹ : G.Cˣ) : G.C)) := by
          rw [Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [mul_smul_comm, mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  ·
    change (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C))ᴴ = _
    rw [conjTranspose_mul, (G.gram_herm v).eq, hH, hshb, mul_assoc, hgg', mul_one]
  ·
    have hb : IsUnit (G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := (Units.isUnit _).map (G.psi v)
    rw [det_mul]
    exact mul_ne_zero (G.gram_det v) ((Matrix.isUnit_iff_isUnit_det _).mp hb).ne_zero
  ·
    rw [hH]
    calc G.gram v * G.psi v (sh G (P.γ : G.C)) * (G.gram v)⁻¹ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) *
          G.psi v P.γ
        = G.gram v * (G.psi v (sh G (P.γ : G.C)) * ((G.gram v)⁻¹ * G.gram v) *
            G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) * G.psi v P.γ) := by simp only [mul_assoc]
      _ = G.gram v * G.psi v (sh G (P.γ : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ) := by
          rw [hgg', mul_one, map_mul, map_mul]
      _ = G.gram v * ((P.c : ℚ) • G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
          rw [hu, map_mul, RingHom.map_rat_algebraMap, ← Algebra.smul_def]
      _ = _ := by rw [mul_smul_comm, Rat.cast_smul_eq_qsmul]

end GlobalTheory.LKMid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairHermitianFormInvertibleSimilitudeStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitudePair_hermitianForm_invertible_similitude : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F), (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)).IsHermitian ∧ (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)).det ≠ 0 ∧ (G.psi v P.γ)ᴴ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) * G.psi v P.γ = ((P.c : ℚ) : ℂ) • (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
  first | (exact @GlobalTheory.LKMid.pair_form_laws) | (exact GlobalTheory.LKMid.pair_form_laws) | (intros; apply GlobalTheory.LKMid.pair_form_laws  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenLevelGroupFiniteAdelic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.LevelOpen

theorem isOpen_levG : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank), IsOpen {g : GfC V | (g : GA D V) ∈ levG V β L} := by
  intro D V β L
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  obtain ⟨U, hU, hle⟩ := GlobalTheory.GoodFiniteDim.exists_open_subgroup V β L
  have h1 : IsOpen ((U.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) := hU.preimage continuous_subtype_val
  exact Subgroup.isOpen_mono (H₂ := (levG V β L).subgroupOf (GfC V)) (fun g hg => (hle g.1 hg g.2).1) h1

end GlobalTheory.LevelOpen
end
