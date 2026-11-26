module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTorsionAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechCohomologyFinrank
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SumExtendByZeroLeSum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRing
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRing
namespace GlobalTheory

theorem homExtension_semiAbelian_dvr : GlobalTheory.LN.HomExtSt :=
  GlobalTheory.existsUnique_hom_extension_semiAbelian_dvr
    (GlobalTheory.AbelianSubgroupFinite.finite_of_no_torsion GlobalTheory.card_torsion_abelianVariety)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homExtension_semiAbelian_discreteValuationRing : GlobalTheory.LN.HomExtSt := by
  first | exact @GlobalTheory.homExtension_semiAbelian_dvr | exact GlobalTheory.homExtension_semiAbelian_dvr | (intros; apply GlobalTheory.homExtension_semiAbelian_dvr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteTorsionSemiAbelian
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteTorsionSemiAbelianOfAbelian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorsionFinite

theorem finite_torsion_semiAbelian_of_abelian :
    (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, 1 ≤ n → Finite {x : 𝟙_ (Over (Sp K)) ⟶ B // x ^ n = 1}) → ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], IsSemiAbelian G → ∀ n : ℕ, 0 < n → Finite {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ n = 1} := by
  intro hB k _ _ G _ hG n hn
  haveI := hG.comm
  let t : Sp k ⟶ Sp k := 𝟙 _
  have h := (semiAbelian_torsion_finite_and_closedPoint_finiteOrder hB).1 k
    ((Over.pullback t).obj G) (hG.fibres k t) n hn
  have hp := isGrpPullback_pullback G t
  have hbij : Function.Bijective (pushHom hp (𝟙_ (Over (Sp k)))) := by
    constructor
    · intro x y hxy
      have e : x.left ≫ pullback.fst G.hom t = y.left ≫ pullback.fst G.hom t :=
        congrArg (fun z => z.left) hxy
      exact Over.OverMorphism.ext (hp.1.hom_ext e ((Over.w x).trans (Over.w y).symm))
    · intro y
      refine ⟨Over.homMk (hp.1.lift y.left (𝟙_ (Over (Sp k))).hom (Over.w y))
        (hp.1.lift_snd _ _ _), ?_⟩
      exact Over.OverMorphism.ext (hp.1.lift_fst _ _ _)
  let e := MulEquiv.ofBijective _ hbij
  have h2 : Finite {x : Over.mk ((𝟙_ (Over (Sp k))).hom ≫ t) ⟶ G // x ^ n = 1} := by
    refine Finite.of_equiv _ (e.toEquiv.subtypeEquiv (p := fun x => x ^ n = 1) fun x => ?_)
    show x ^ n = 1 ↔ e x ^ n = 1
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  have h3 : (𝟙_ (Over (Sp k))).hom ≫ t = t := Category.id_comp t
  rw [h3] at h2
  exact h2

end GlobalTheory.TorsionFinite
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem finite_torsion_semiAbelian :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], IsSemiAbelian G → ∀ n : ℕ, 0 < n → Finite {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ n = 1} :=
  TorsionFinite.finite_torsion_semiAbelian_of_abelian AbTorsionFinite.finite_torsion

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePointsOfIsOpenImmersion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open Topology TopologicalSpace

namespace GlobalTheory.TorsionDense

open RationalPoint

theorem nonempty_torusExtension {k : Type} [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G]
    (hG : IsSemiAbelian G) : Nonempty (TorusExtension G) := by
  obtain ⟨E⟩ := hG.fibres k (𝟙 _)
  let e : (Over.pullback (𝟙 (Sp k))).mapMon.obj (Mon.mk G) ≅ Mon.mk G :=
    (Functor.mapMonNatIso (Over.pullbackId (X := Sp k)) ≪≫ Functor.mapMonIdIso).app (Mon.mk G)
  let e' : (Over.pullback (𝟙 (Sp k))).obj G ≅ G := (Mon.forget _).mapIso e
  have : IsMonHom e'.hom := by
    change IsMonHom e.hom.hom
    infer_instance
  exact ⟨torusExtOfIso e' E⟩

theorem noetherianSpace_zariski {k : Type} [Field k] (X : Over (Sp k)) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] : @NoetherianSpace _ (zariski X) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  letI := zariski X
  exact (IsInducing.induced pt).noetherianSpace

theorem finite_points_of_isOpenImmersion {k : Type} [Field k] [IsAlgClosed k] {N₀ N : Over (Sp k)}
    [GrpObj N₀] [GrpObj N] [LocallyOfFiniteType N.hom] [QuasiCompact N.hom] (ν : N₀ ⟶ N)
    [IsMonHom ν] [IsOpenImmersion ν.left] [Finite (𝟙_ (Over (Sp k)) ⟶ N₀)] :
    Finite (𝟙_ (Over (Sp k)) ⟶ N) := by
  letI := zariski N
  haveI := separatelyContinuousMul N
  haveI := noetherianSpace_zariski N
  have : LocallyOfFiniteType N₀.hom := by rw [← ν.w]; infer_instance
  let φ : (𝟙_ (Over (Sp k)) ⟶ N₀) →* (𝟙_ (Over (Sp k)) ⟶ N) :=
    MonoidHom.mk' (fun x => x ≫ ν) fun x y => MonObj.mul_comp x y ν
  have ho : IsOpen (φ.range : Set (𝟙_ (Over (Sp k)) ⟶ N)) := by
    refine isOpen_induced_iff.2 ⟨Set.range ν.left, ν.left.isOpenMap.isOpen_range, ?_⟩
    ext y
    rw [Set.mem_preimage, ← Set.image_univ, pt_mem_image_iff ν isClosed_univ]
    exact ⟨fun ⟨x, _, hx⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨x, trivial, hx⟩⟩
  have hfin : (φ.range : Set (𝟙_ (Over (Sp k)) ⟶ N)).Finite := Set.finite_range φ
  obtain ⟨t, ht⟩ := (NoetherianSpace.isCompact (Set.univ : Set (𝟙_ (Over (Sp k)) ⟶ N))).elim_finite_subcover
    (fun g : 𝟙_ (Over (Sp k)) ⟶ N => (fun y => g * y) ⁻¹' (φ.range : Set _))
    (fun g => ho.preimage (continuous_const_mul g))
    (fun y _ => Set.mem_iUnion.2 ⟨y⁻¹, Set.mem_preimage.2 (by rw [inv_mul_cancel]; exact φ.range.one_mem)⟩)
  refine Set.finite_univ_iff.1 (Set.Finite.subset ?_ ht)
  exact t.finite_toSet.biUnion fun g _ => hfin.preimage (mul_right_injective g).injOn

theorem finite_of_isClosed_abelian
    (hno : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A →
      ∀ n : ℕ, 2 ≤ n → (n : k) ≠ 0 → (∀ x : 𝟙_ (Over (Sp k)) ⟶ A, x ^ n = 1 → x = 1) →
      Finite (𝟙_ (Over (Sp k)) ⟶ A)) :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (n : ℕ), IsAbelianScheme B → n.Prime → (n : k) ≠ 0 → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C := by
  intro k _ _ B _ n hB hn hnk C Z hZ hC htor
  have := hB.smooth
  have := hB.proper
  have := hB.comm
  obtain ⟨N, _, ν, hν, hνc, hNs, hr⟩ :=
    GlobalTheory.ReducedSubgroup.exists_smooth_closed_subgroup k B inferInstance C Z hZ hC
  have hNp : IsProper N.hom := by rw [← ν.w]; infer_instance
  obtain ⟨N₀, _, ν₀, g, hν₀, hν₀o, hν₀c, hgc, hg, -⟩ :=
    GlobalTheory.exists_neutralComponent k N hNs inferInstance
  have : IsClosedImmersion (ν₀ ≫ ν).left := by rw [Over.comp_left]; infer_instance
  have : Mono (ν₀ ≫ ν) := Over.mono_of_mono_left _
  have hA : IsAbelianScheme N₀ :=
    { comm := AbelianSubgroupFinite.isCommMonObj_of_mono (ν₀ ≫ ν)
      smooth := SmoothOfRelativeDimension.smooth g N₀.hom
      proper := by rw [← ν₀.w]; infer_instance
      geomConnected := hgc }
  have hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, x ≫ ν ∈ C := fun x => by
    rw [hC, ← hr]
    rintro _ ⟨t, rfl⟩
    exact ⟨x.left t, rfl⟩
  have h1 : Finite (𝟙_ (Over (Sp k)) ⟶ N₀) := by
    refine hno k N₀ hA n hn.two_le hnk fun x hx => ?_
    have h2 : x ≫ ν₀ ≫ ν = 1 := by
      refine htor _ (by rw [← Category.assoc]; exact hmem _) ?_
      rw [← MonObj.pow_comp, hx, MonObj.one_comp]
    rw [← cancel_mono (ν₀ ≫ ν), h2, MonObj.one_comp]
  have := finite_points_of_isOpenImmersion ν₀
  refine Finite.of_surjective (fun x : 𝟙_ (Over (Sp k)) ⟶ N => (⟨x ≫ ν, hmem x⟩ : C)) ?_
  rintro ⟨x, hx⟩
  have : IsReduced (𝟙_ (Over (Sp k))).left := inferInstanceAs (IsReduced (Sp k))
  obtain ⟨l, hl⟩ := AbelianSubgroupFinite.exists_lift_of_range_subset x.left ν.left
    (hr ▸ (hC x).1 hx)
  refine ⟨Over.homMk l ?_, Subtype.ext (Over.OverMorphism.ext hl)⟩
  rw [← ν.w, ← Category.assoc, hl, x.w]

theorem exists_pow_stable {k : Type} [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G]
    [IsCommMonObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] (l : ℕ)
    (K : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)) (Z : Set G.left) (hZ : IsClosed Z)
    (hK : ∀ x, x ∈ K ↔ Set.range x.left ⊆ Z) :
    ∃ a : ℕ, ∀ x ∈ K, ∃ y ∈ K, y ^ (l ^ (a + 1)) = x ^ (l ^ a) := by
  letI := zariski G
  haveI := noetherianSpace_zariski G
  have hpow : ∀ n : ℕ, IsMonHom (𝟙 G ^ n) := fun n => by
    induction n with
    | zero =>
      rw [pow_zero]
      exact inferInstanceAs (IsMonHom (toUnit G ≫ η[G]))
    | succ n ih =>
      rw [pow_succ]
      exact inferInstanceAs (IsMonHom (lift (𝟙 G ^ n) (𝟙 G) ≫ μ[G]))
  have hcl : ∀ n : ℕ, IsClosed {z : 𝟙_ (Over (Sp k)) ⟶ G | ∃ y ∈ K, y ^ n = z} := fun n => by
    obtain ⟨Z', hZ', h⟩ := exists_isClosed_image_of_isClosed_subgroup k G G (𝟙 G ^ n)
      (hpow n) inferInstance inferInstance inferInstance inferInstance K Z hZ hK
    refine isClosed_induced_iff.2 ⟨Z', hZ', ?_⟩
    ext z
    rw [Set.mem_preimage, ← range_left_subset_iff, ← h]
    simp only [MonObj.comp_pow, Category.comp_id, Set.mem_setOf_eq]
  let F : ℕ → Closeds (𝟙_ (Over (Sp k)) ⟶ G) := fun a => ⟨_, hcl (l ^ a)⟩
  obtain ⟨_, ⟨a, rfl⟩, hmin⟩ := (wellFounded_lt (α := Closeds (𝟙_ (Over (Sp k)) ⟶ G))).has_min
    (Set.range F) ⟨_, 0, rfl⟩
  have hle : F (a + 1) ≤ F a := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y ^ l, K.pow_mem hy l, by rw [← pow_mul, ← pow_succ']⟩
  have heq : F (a + 1) = F a := hle.eq_of_not_lt (hmin _ ⟨_, rfl⟩)
  refine ⟨a, fun x hx => ?_⟩
  have : x ^ (l ^ a) ∈ F (a + 1) := by
    rw [heq]
    exact ⟨x, hx, rfl⟩
  exact this

theorem eq_one_of_finite_range {k : Type} [Field k] [IsAlgClosed k] {G G' : Over (Sp k)} [GrpObj G]
    [GrpObj G'] [IsIntegral G.left] [LocallyOfFiniteType G.hom] [LocallyOfFiniteType G'.hom]
    (f : G ⟶ G') [IsMonHom f]
    (h : (Set.range fun x : 𝟙_ (Over (Sp k)) ⟶ G => x ≫ f).Finite) : f = 1 := by
  let e : 𝟙_ (Over (Sp k)) ⟶ G' := 1
  let S : Set G'.left := ⋃ y ∈ (Set.range fun x : 𝟙_ (Over (Sp k)) ⟶ G => x ≫ f) \ {e}, {pt y}
  have hS : IsClosed S := (h.subset Set.diff_subset).isClosed_biUnion fun y _ => isClosed_pt y
  have hsub : Set.range f.left ⊆ {pt e} ∪ S := by
    refine ReducedSubgroup.range_subset_of_points f ((isClosed_pt e).union hS) fun x => ?_
    rw [range_left_subset_iff]
    by_cases hx : x ≫ f = e
    · exact Or.inl (by rw [hx]; rfl)
    · exact Or.inr (Set.mem_biUnion (x := x ≫ f) ⟨⟨x, rfl⟩, hx⟩ rfl)
  have heS : pt e ∉ S := by
    intro he
    obtain ⟨y, hy, hey⟩ := Set.mem_iUnion₂.1 he
    exact hy.2 (pt_injective hey).symm
  have hc : _root_.IsPreconnected (Set.range f.left) := isPreconnected_range f.left.continuous
  have he : pt e ∈ Set.range f.left := ⟨pt (1 : 𝟙_ (Over (Sp k)) ⟶ G), by
    rw [← pt_comp, MonObj.one_comp]⟩
  have hsub' : Set.range f.left ⊆ {pt e} := by
    rcases isPreconnected_iff_subset_of_disjoint_closed.1 hc _ _ (isClosed_pt e) hS hsub
      (by rw [Set.singleton_inter_eq_empty.2 heS, Set.inter_empty]) with h1 | h1
    · exact h1
    · exact absurd (h1 he) heS
  have : Subsingleton (𝟙_ (Over (Sp k))).left := inferInstanceAs (Subsingleton (Sp k))
  have : IsClosedImmersion e.left := isClosedImmersion_of_comp_eq_id _ _ e.w
  obtain ⟨t, ht⟩ := AbelianSubgroupFinite.exists_lift_of_range_subset f.left e.left
    (hsub'.trans (by rintro _ rfl; exact ⟨_, rfl⟩))
  have ht' : t = G.hom := by
    rw [← f.w, ← ht, Category.assoc, e.w]
    exact (Category.comp_id _).symm
  have : f = toUnit G ≫ e := Over.OverMorphism.ext (by rw [← ht, ht']; rfl)
  rw [this, MonObj.comp_one]

theorem eq_one_of_torsion_comp_eq_one : ∀ (k : Type) [Field k] [IsAlgClosed k] (G G' : Over (Sp k)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (l : ℕ), l.Prime → (l : k) ≠ 0 → ∀ f : G ⟶ G', IsMonHom f → (∀ (x : 𝟙_ (Over (Sp k)) ⟶ G), x ^ l = 1 → ∀ y : 𝟙_ (Over (Sp k)) ⟶ G, ∀ a : ℕ, y ^ (l ^ a) = 1 → y ≫ f = 1) → f = 1 := by
  intro k _ _ G G' _ _ hG hG' l hl hlk f hf htor
  replace htor := htor 1 (one_pow l)
  have := hG.comm
  have := hG.smooth
  have := hG.quasiCompact
  have := hG'.comm
  have := hG'.smooth
  have := hG'.quasiCompact
  have := isIntegral_left_of_isSemiAbelian G
  let φ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ G') :=
    MonoidHom.mk' (fun x => x ≫ f) fun x y => MonObj.mul_comp x y f
  obtain ⟨a, ha⟩ := exists_pow_stable G l φ.ker (f.left ⁻¹' {pt (1 : 𝟙_ (Over (Sp k)) ⟶ G')})
    ((isClosed_pt _).preimage f.left.continuous) fun x => by
      rw [range_left_subset_iff, Set.mem_preimage, ← pt_comp, Set.mem_singleton_iff,
        pt_injective.eq_iff]
      rfl
  obtain ⟨Z', hZ', h'⟩ := exists_isClosed_image_of_isClosed_subgroup k G G' f hf inferInstance
    inferInstance inferInstance inferInstance ⊤ Set.univ isClosed_univ (by simp)
  have hfin : Finite φ.range := by
    refine finite_of_isClosed_torusExtension_of_pow_eq_one
      (finite_of_isClosed_abelian GlobalTheory.T.finite_points_abelianVariety_of_no_torsion) k G' l inferInstance inferInstance
      (nonempty_torusExtension G' hG') hl hlk _ Z' hZ' (fun y => ?_) ?_
    · rw [← h']
      exact ⟨fun ⟨x, hx⟩ => ⟨x, trivial, hx⟩, fun ⟨x, _, hx⟩ => ⟨x, hx⟩⟩
    · rintro _ ⟨g, rfl⟩ hg
      obtain ⟨y, hy, hyg⟩ := ha (g ^ l) (by rw [MonoidHom.mem_ker, map_pow, hg])
      have h1 : φ (g / y) = 1 := htor (g / y) (a + 1) (by
        rw [div_pow, hyg, ← pow_mul, ← pow_succ', div_self'])
      rwa [map_div, MonoidHom.mem_ker.1 hy, div_one] at h1
  exact eq_one_of_finite_range f hfin

end GlobalTheory.TorsionDense
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTorsionMulCardToricTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

namespace SemiAbTorsionCount

theorem card_pow_eq_one_of_extension {T G B : Type} [Group T] [CommGroup G] [Group B]
    (i : T →* G) (q : G →* B) (hi : Function.Injective i) (hk : ∀ x, q x = 1 ↔ ∃ t, i t = x)
    (hq : Function.Surjective q) (n : ℕ) (hT : ∀ t : T, ∃ s : T, s ^ n = t) :
    Nat.card {x : G // x ^ n = 1} =
      Nat.card {b : B // b ^ n = 1} * Nat.card {t : T // t ^ n = 1} := by
  let K : Subgroup G := (powMonoidHom n : G →* G).ker
  let f : K →* B := q.comp K.subtype
  have h0 : Nat.card {x : G // x ^ n = 1} = Nat.card K := rfl
  have h1 : Nat.card {b : B // b ^ n = 1} = Nat.card f.range := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun b => ⟨fun hb => ?_, ?_⟩)
    · obtain ⟨x, rfl⟩ := hq b
      obtain ⟨t, ht⟩ := (hk (x ^ n)).1 (by rw [map_pow, hb])
      obtain ⟨s, rfl⟩ := hT t
      refine ⟨⟨x / i s, ?_⟩, ?_⟩
      · change (x / i s) ^ n = 1
        rw [div_pow, ← map_pow, ht, div_self']
      · change q (x / i s) = q x
        rw [map_div, (hk _).2 ⟨s, rfl⟩, div_one]
    · rintro ⟨x, rfl⟩
      have hx : x.1 ^ n = 1 := x.2
      change q x.1 ^ n = 1
      rw [← map_pow, hx, map_one]
  have h2 : Nat.card {t : T // t ^ n = 1} = Nat.card f.ker := by
    refine Nat.card_eq_of_bijective (fun t => ⟨⟨i t.1, ?_⟩, (hk _).2 ⟨t.1, rfl⟩⟩) ⟨?_, ?_⟩
    · change i t.1 ^ n = 1
      rw [← map_pow, t.2, map_one]
    · intro a b h
      exact Subtype.ext (hi (congrArg (fun z : f.ker => z.1.1) h))
    · rintro ⟨⟨x, hx⟩, hx'⟩
      obtain ⟨t, rfl⟩ := (hk x).1 hx'
      have hx₁ : i t ^ n = 1 := hx
      exact ⟨⟨t, hi (by rw [map_pow, hx₁, map_one])⟩, rfl⟩
  rw [h0, h1, h2, Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]

theorem nonempty_hom_mulEquiv_pi (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (M : Type) [CommGroup M] :
    Nonempty ((Multiplicative X →* M) ≃* (Fin (Module.finrank ℤ X) → M)) := by
  let b := Module.finBasis ℤ X
  let ev : (Multiplicative X →* M) →* (Fin (Module.finrank ℤ X) → M) :=
    { toFun := fun t j => t (Multiplicative.ofAdd (b j))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨MulEquiv.ofBijective ev ⟨fun s t h => ?_, fun v => ?_⟩⟩
  · have : (MonoidHom.toAdditiveRight s).toIntLinearMap = (MonoidHom.toAdditiveRight t).toIntLinearMap :=
      b.ext fun j => congrArg Additive.ofMul (congrFun h j)
    ext x
    exact congrArg Additive.toMul (DFunLike.congr_fun this x)
  · refine ⟨AddMonoidHom.toMultiplicativeLeft
      (b.constr ℤ (fun j => Additive.ofMul (v j))).toAddMonoidHom, funext fun j => ?_⟩
    exact congrArg Additive.toMul (b.constr_basis ℤ (fun j => Additive.ofMul (v j)) j)

theorem nonempty_torus_points_mulEquiv (k : Type) [Field k] (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] :
    Nonempty ((𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) ≃* (Fin (Module.finrank ℤ X) → kˣ)) := by
  obtain ⟨e₂⟩ := nonempty_hom_mulEquiv_pi X Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ
  let e₃ : Γ((𝟙_ (Over (Sp k))).left, ⊤) ≃+* k :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  exact ⟨((splitTorusPointsEquiv (Sp k) X (𝟙_ (Over (Sp k)))).trans e₂).trans
    (MulEquiv.piCongrRight fun _ => Units.mapEquiv e₃.toMulEquiv)⟩

theorem divisible_and_card {k : Type} [Field k] [IsAlgClosed k] {T : Type} [Group T] {t : ℕ}
    (e : T ≃* (Fin t → kˣ)) (N : ℕ) (hN : (N : k) ≠ 0) :
    (∀ x : T, ∃ s : T, s ^ N = x) ∧ Nat.card {x : T // x ^ N = 1} = N ^ t := by
  have hN0 : N ≠ 0 := by rintro rfl; exact hN Nat.cast_zero
  haveI : NeZero N := ⟨hN0⟩
  haveI : NeZero (N : k) := ⟨hN⟩
  constructor
  · intro x
    have : ∀ u : kˣ, ∃ s : kˣ, s ^ N = u := fun u => by
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : k) (Nat.pos_of_ne_zero hN0)
      have hz0 : z ≠ 0 := by
        rintro rfl
        rw [zero_pow hN0] at hz
        exact u.ne_zero hz.symm
      exact ⟨Units.mk0 z hz0, Units.ext hz⟩
    choose r hr using this
    refine ⟨e.symm fun j => r (e x j), e.injective ?_⟩
    rw [map_pow, e.apply_symm_apply]
    exact funext fun j => hr _
  · have h1 : Nat.card {x : T // x ^ N = 1} = Nat.card (Fin t → rootsOfUnity N k) := by
      refine Nat.card_congr ((e.toEquiv.subtypeEquiv (q := fun v => ∀ j, v j ∈ rootsOfUnity N k)
        fun x => ?_).trans Equiv.subtypePiEquivPi)
      rw [← e.map_eq_one_iff, map_pow, funext_iff]
      rfl
    rw [h1, Nat.card_fun, HasEnoughRootsOfUnity.natCard_rootsOfUnity, Nat.card_eq_fintype_card,
      Fintype.card_fin]

theorem dim_eq {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] (E : TorusExtension G) (g g' : ℕ)
    (dG : SmoothOfRelativeDimension g G.hom) (dB : SmoothOfRelativeDimension g' E.B.hom) :
    g = g' + @Module.finrank ℤ E.X _ E.addCommGroup.toAddCommMonoid _ := by
  letI := E.addCommGroup
  letI := E.grpB
  have := E.free
  have := E.finite
  obtain ⟨y⟩ : Nonempty ↥(Sp k) := inferInstance
  have := E.i_hom
  have := (GlobalTheory.torusExtension_smooth_geometricallyConnected G E).1
  obtain ⟨m, W, hW, d₁⟩ := H1.exists_dim E.q.left (eSec G y)
  have g₂ : m = Module.finrank ℤ E.X :=
    H1.dim_base (E.isKernel.map (Over.forget _)) d₁ (H1.torus_dim (Sp k) E.X) (eSec _ y)
      ((congrArg (fun f => f.left y ∈ W) (IsMonHom.one_hom E.i)).mpr hW)
  have d₂ : SmoothOfRelativeDimension (m + g') (W.ι ≫ G.hom) := by
    rw [← Over.w E.q, ← Category.assoc]; infer_instance
  have d₃ : SmoothOfRelativeDimension (0 + g) (W.ι ≫ G.hom) := inferInstance
  have := H1.dim_unique _ d₂ d₃ ⟨_, hW⟩
  omega

end SemiAbTorsionCount

open SemiAbTorsionCount

theorem card_torsion_mul_card_toric_torsion : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (T : TorusExtension G) (g N : ℕ), IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (N : k) ≠ 0 → Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ N = 1} * Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ N = 1 ∧ ∃ y, x = y ≫ T.i} = N ^ (2 * g) := by
  intro k _ _ G _ E g N hG dG hN
  letI := E.addCommGroup
  letI := E.grpB
  haveI := E.free
  haveI := E.finite
  haveI := E.q_hom
  haveI := E.i_hom
  haveI := hG.comm
  haveI := E.q_surjective
  haveI := (GlobalTheory.torusExtension_smooth_geometricallyConnected G E).1
  have hk := E.isKernel
  obtain ⟨g', dB⟩ := GlobalTheory.AbelianDim.exists_relDim k E.B E.isAbelian
  have hg := dim_eq G E g g' dG dB
  obtain ⟨e⟩ := nonempty_torus_points_mulEquiv k E.X
  obtain ⟨hdiv, hcard⟩ := divisible_and_card e N hN
  have hB := GlobalTheory.T.card_torsion_eq_pow_two_mul_dim k E.B g' N E.isAbelian dB hN
  let i := IsMonHom.monoidHom E.i (𝟙_ (Over (Sp k)))
  have hi : Function.Injective i := fun a b h => hk.hom_ext h (toUnit_unique _ _)
  have h1 := card_pow_eq_one_of_extension i (IsMonHom.monoidHom E.q (𝟙_ (Over (Sp k)))) hi
    (fun x => ⟨fun hx => ?_, ?_⟩) (fun x => ?_) N hdiv
  · have h2 : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ N = 1 ∧ ∃ y, x = y ≫ E.i} =
        N ^ Module.finrank ℤ E.X := by
      rw [← hcard]
      refine (Nat.card_eq_of_bijective
        (fun t => ⟨i t.1, by rw [← map_pow, t.2, map_one], t.1, rfl⟩) ⟨?_, ?_⟩).symm
      · intro a b h
        exact Subtype.ext (hi (congrArg Subtype.val h))
      · rintro ⟨x, hx, t, rfl⟩
        have hx₁ : i t ^ N = 1 := hx
        exact ⟨⟨t, hi (by rw [map_pow, hx₁, map_one])⟩, rfl⟩
    rw [h2, h1, hB, hcard, hg]
    ring
  · have hx' : x ≫ E.q = 1 := hx
    exact ⟨hk.lift x (toUnit _) (by rw [hx', Hom.one_def]), hk.lift_fst _ _ _⟩
  · rintro ⟨t, rfl⟩
    change (t ≫ E.i) ≫ E.q = 1
    rw [Category.assoc, hk.w, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  · obtain ⟨p, hp⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective (Ω := k) E.q.left x.left
    refine ⟨Over.homMk p ?_, Over.OverMorphism.ext hp.symm⟩
    rw [← Over.w E.q, ← Category.assoc, ← hp]
    exact Over.w x

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoPolarisedAbelianSchemesDvrOfFieldExtens
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoPolarisedAbelianSchemesDvrOfFieldExtens
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.IsoOverField

theorem eSec_pullback_fst {S S' : Scheme.{0}} (p : S' ⟶ S) (G : Over S) [GrpObj G] :
    eSec ((Over.pullback p).obj G) ≫ pullback.fst G.hom p = p ≫ eSec G := by
  rw [eSec, eSec, Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq]
  erw [ExtUnique.pullback_map_left_fst, ← Category.assoc, ← pullback.condition]
  simp

theorem isAbelianScheme_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S) [GrpObj A]
    (hA : IsAbelianScheme A) : IsAbelianScheme ((Over.pullback f).obj A) :=
  { comm := by have := hA.comm; infer_instance
    smooth := by have := hA.smooth; show Smooth (pullback.snd _ _); infer_instance
    proper := by have := hA.proper; show IsProper (pullback.snd _ _); infer_instance
    geomConnected := by have := hA.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }

variable {U' U S : Scheme.{0}} (k : U' ⟶ U) (j : U ⟶ S)

noncomputable def toBase (A : Over S) : (Over.mk (k ≫ j) ⊗ A).left ⟶ pullback A.hom j :=
  pullback.lift (snd (Over.mk (k ≫ j)) A).left ((fst (Over.mk (k ≫ j)) A).left ≫ k)
    (by rw [Over.w, Category.assoc]; exact (Over.w (fst (Over.mk (k ≫ j)) A)).symm)

theorem toBase_fst (A : Over S) : toBase k j A ≫ pullback.fst A.hom j = (snd (Over.mk (k ≫ j)) A).left :=
  pullback.lift_fst _ _ _

theorem toBase_snd (A : Over S) : toBase k j A ≫ pullback.snd A.hom j = (fst (Over.mk (k ≫ j)) A).left ≫ k :=
  pullback.lift_snd _ _ _

theorem isPullback_snd (T A : Over S) : IsPullback (snd T A).left (fst T A).left A.hom T.hom :=
  (IsPullback.of_hasPullback T.hom A.hom).flip

theorem isPullback_toBase (A : Over S) :
    IsPullback (toBase k j A) (fst (Over.mk (k ≫ j)) A).left (pullback.snd A.hom j) k := by
  refine IsPullback.of_right ?_ (toBase_snd k j A) (IsPullback.of_hasPullback A.hom j)
  rw [toBase_fst]
  exact isPullback_snd (Over.mk (k ≫ j)) A

theorem exists_iso_over [Flat k] [Surjective k] [QuasiCompact k] [Mono j] (A B : Over S) [GrpObj A] [GrpObj B]
    (φ : Over.mk (k ≫ j) ⊗ A ≅ Over.mk (k ≫ j) ⊗ B) (hφ : φ.hom ≫ fst _ _ = fst _ _)
    (h₁ : lift (𝟙 (Over.mk (k ≫ j))) (1 : Over.mk (k ≫ j) ⟶ A) ≫ φ.hom ≫ snd _ _ = 1)
    (κ : Over.mk (k ≫ j) ⟶ Over.mk j) (g : Over.mk j ⊗ A ⟶ B) (hg : κ ▷ A ≫ g = φ.hom ≫ snd _ _) :
    ∃ f : (Over.pullback j).obj A ≅ (Over.pullback j).obj B,
      η[(Over.pullback j).obj A] ≫ f.hom = η[(Over.pullback j).obj B] ∧
      toBase k j A ≫ f.hom.left ≫ pullback.fst B.hom j = (φ.hom ≫ snd _ _).left := by
  have hκ : κ.left = k := (cancel_mono j).1 (Over.w κ)
  let s : pullback A.hom j ⟶ (Over.mk j ⊗ A).left := (pullbackSymmetry A.hom j).hom
  have s₁ : s ≫ (fst (Over.mk j) A).left = pullback.snd A.hom j := pullbackSymmetry_hom_comp_fst _ _
  have s₂ : s ≫ (snd (Over.mk j) A).left = pullback.fst A.hom j := pullbackSymmetry_hom_comp_snd _ _
  have hs : toBase k j A ≫ s = (κ ▷ A).left := by
    refine (isPullback_snd (Over.mk j) A).hom_ext ?_ ?_
    · rw [Category.assoc, s₂, toBase_fst, ← Over.comp_left, whiskerRight_snd]
    · rw [Category.assoc, s₁, toBase_snd, ← Over.comp_left, whiskerRight_fst, Over.comp_left, hκ]
  have hw : (s ≫ g.left) ≫ B.hom = pullback.snd A.hom j ≫ j := by
    rw [Category.assoc, Over.w, ← s₁, Category.assoc]
    exact congrArg (s ≫ ·) (Over.w (fst (Over.mk j) A)).symm
  let f : (Over.pullback j).obj A ⟶ (Over.pullback j).obj B :=
    Over.homMk (pullback.lift (s ≫ g.left) (pullback.snd A.hom j) hw) (pullback.lift_snd _ _ _)
  have f₁ : f.left ≫ pullback.fst B.hom j = s ≫ g.left := pullback.lift_fst _ _ _
  have f₂ : f.left ≫ pullback.snd B.hom j = pullback.snd A.hom j := pullback.lift_snd _ _ _
  have key : toBase k j A ≫ f.left ≫ pullback.fst B.hom j = (φ.hom ≫ snd _ _).left := by
    rw [f₁, ← Category.assoc, hs, ← Over.comp_left, hg]
  have hφ' : φ.hom.left ≫ (fst (Over.mk (k ≫ j)) B).left = (fst (Over.mk (k ≫ j)) A).left := by
    rw [← Over.comp_left, hφ]
  have sq : toBase k j A ≫ f.left = φ.hom.left ≫ toBase k j B := by
    apply pullback.hom_ext
    · rw [Category.assoc, key, Category.assoc, toBase_fst, Over.comp_left]
    · rw [Category.assoc, f₂, Category.assoc, toBase_snd, toBase_snd, ← Category.assoc, hφ']
  have pb : IsPullback (toBase k j A) φ.hom.left f.left (toBase k j B) := by
    refine IsPullback.of_bot ?_ sq (isPullback_toBase k j B)
    rw [hφ', f₂]
    exact isPullback_toBase k j A
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (toBase k j B) :=
    MorphismProperty.of_isPullback (isPullback_toBase k j B).flip
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hi : IsIso f.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme.{0}) pb.flip hQ
      (inferInstanceAs (IsIso ((Over.forget S).map φ.hom)))
  have : IsIso ((Over.forget U).map f) := hi
  have : IsIso f := isIso_of_reflects_iso f (Over.forget U)
  refine ⟨asIso f, ?_, key⟩
  have : Epi k := Flat.epi_of_flat_of_surjective _
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have one : ∀ (G : Over S) [GrpObj G], (1 : Over.mk (k ≫ j) ⟶ G).left = (k ≫ j) ≫ eSec G := fun G _ => by
      rw [Hom.one_def, Over.comp_left]
      congr 1
    have e : (lift (𝟙 (Over.mk (k ≫ j))) (1 : Over.mk (k ≫ j) ⟶ A)).left ≫ toBase k j A =
        k ≫ eSec ((Over.pullback j).obj A) := by
      apply pullback.hom_ext
      · rw [Category.assoc, toBase_fst, ← Over.comp_left, lift_snd, one, Category.assoc, Category.assoc]
        exact congrArg (k ≫ ·) (eSec_pullback_fst j A).symm
      · rw [Category.assoc, toBase_snd, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc]
        exact (Category.id_comp _).trans ((Category.comp_id k).symm.trans
          (congrArg (k ≫ ·) (Over.w η[(Over.pullback j).obj A]).symm))
    refine (cancel_epi k).1 ?_
    change k ≫ (eSec ((Over.pullback j).obj A) ≫ f.left) ≫ pullback.fst B.hom j =
      k ≫ eSec ((Over.pullback j).obj B) ≫ pullback.fst B.hom j
    rw [eSec_pullback_fst, Category.assoc, ← Category.assoc k, ← e, Category.assoc, key, ← Over.comp_left, h₁,
      one, Category.assoc]
  · exact (Over.w _).trans (Over.w _).symm

theorem exists_iso_over_dvr : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (P P' : PolAV (Sp V)) (C : Type) [Field C] [Algebra (FractionRing V) C] (φ : TF (R := V) C ⊗ P.A ≅ TF (R := V) C ⊗ P'.A), φ.hom ≫ fst _ _ = fst _ _ → lift (𝟙 (TF (R := V) C)) (1 : TF (R := V) C ⟶ P.A) ≫ φ.hom ≫ snd _ _ = 1 → LBIso (P.L.pull (snd (TF (R := V) C) P.A).left) (P'.L.pull (φ.hom ≫ snd (TF (R := V) C) P'.A).left) → ∀ (κ : TF (R := V) C ⟶ TK V) (g : TK V ⊗ P.A ⟶ P'.A), κ ▷ P.A ≫ g = φ.hom ≫ snd _ _ → ∃ Ψ : P.A ≅ P'.A, IsMonHom Ψ.hom ∧ φ.hom ≫ snd _ _ = snd _ _ ≫ Ψ.hom ∧ LBIso P.L (P'.L.pull Ψ.hom.left) := by
  intro hl _ V _ _ _ P P' C _ _ φ hφ h₁ hL κ g hg
  have : Flat (jFK (R := V) C) := FieldBaseChange.flat_spMap (algebraMap (FractionRing V) C)
  have : Surjective (jFK (R := V) C) := FieldBaseChange.surjective_spMap (algebraMap (FractionRing V) C)
  have : QuasiCompact (jFK (R := V) C) := by
    have : IsAffine (TK V).left := inferInstanceAs (IsAffine (Spec _))
    infer_instance
  have : Mono (jK V) := by
    have : IsPreimmersion (jK V) := IsPreimmersion.of_isLocalization (nonZeroDivisors V)
    infer_instance
  obtain ⟨f, hf₁, hf⟩ := exists_iso_over (jFK (R := V) C) (jK V) P.A P'.A φ hφ h₁ κ g hg
  have hm : IsMonHom f.hom := hl.rigidity _ _ _ (isAbelianScheme_pullback _ _ P.isAb)
    (isAbelianScheme_pullback _ _ P'.isAb) f.hom hf₁
  have hm' : IsMonHom f.inv := inferInstance
  have semi_of_ab {S : Scheme.{0}} (B : Over S) [GrpObj B] (h : IsAbelianScheme B) : IsSemiAbelian B := by
    have := h.proper
    refine ⟨h.comm, h.smooth, inferInstance, inferInstance, h.geomConnected, ?_⟩
    intro Ω _ _ p
    have hab := isAbelianScheme_pullback p B h
    refine ⟨{ X := PUnit, B := _, isAbelian := hab, q := 𝟙 _, q_hom := inferInstance
              q_flat := ?_, q_surjective := ?_, q_quasiCompact := ?_
              i := toUnit _ ≫ η, i_hom := ?_, isKernel := ?_ }⟩
    · rw [Over.id_left]; infer_instance
    · rw [Over.id_left]; infer_instance
    · rw [Over.id_left]; infer_instance
    · have := hab.comm; infer_instance
    · have hident : 𝟙 (splitTorus (Spec (CommRingCat.of Ω)) PUnit) = 1 := by
        rw [← Diag.diagMap_id, ← Diag.diagMap_zero]
        congr 1
      have : IsIso (toUnit (splitTorus (Spec (CommRingCat.of Ω)) PUnit)) := ⟨η, hident.symm, toUnit_unique _ _⟩
      exact IsPullback.of_vert_isIso ⟨Category.comp_id _⟩
  have hs := semi_of_ab P.A P.isAb
  have hs' := semi_of_ab P'.A P'.isAb
  obtain ⟨F, ⟨hF, eF⟩, -⟩ := homExtension_semiAbelian_dvr_unconditional V (FractionRing V) P.A P'.A hs hs' f.hom hm
  obtain ⟨G, ⟨-, eG⟩, -⟩ := homExtension_semiAbelian_dvr_unconditional V (FractionRing V) P'.A P.A hs' hs f.inv hm'
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing V (FractionRing V)
  have := P.isAb.smooth
  have := P.isAb.proper
  have := P'.isAb.smooth
  have := P'.isAb.proper
  have : IsIso F := ExtUnique.isIso_of_pullback (jK V) f F G eF eG
  have e : φ.hom ≫ snd _ _ = snd _ _ ≫ F := by
    apply Over.OverMorphism.ext
    rw [← hf, ← eF, Over.comp_left, ← toBase_fst (jFK (R := V) C) (jK V) P.A, Category.assoc]
    exact congrArg (_ ≫ ·) (ExtUnique.pullback_map_left_fst (jK V) F)
  refine ⟨asIso F, hF, e, ?_⟩
  have pull_isLB {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : Y ⟶ X) : (L.pull F).IsLB := by
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
  have hN := pull_isLB P'.isLB F.left
  have hβ : jFK (R := V) C ≫ jK V =
      spMap ((algebraMap (FractionRing V) C).comp (algebraMap V (FractionRing V))) := (Spec.map_comp _ _).symm
  refine IsoDescent.lbIso_of_field V C ((algebraMap (FractionRing V) C).comp (algebraMap V (FractionRing V)))
    ((algebraMap (FractionRing V) C).injective.comp (IsFractionRing.injective V (FractionRing V))) P.A P.isAb _
    (snd (TF (R := V) C) P.A).left (fst (TF (R := V) C) P.A).left (hβ ▸ isPullback_snd (TF (R := V) C) P.A)
    P.L (P'.L.pull F.left) P.isLB hN ?_ ?_
  all_goals
    obtain ⟨Pic, groups, cl, pl, iso_iff, gen_iff, -, comp, linComb, -⟩ := CechPicMul.exists_picardGroup
    let _ := groups
    have pull_class {S T : Scheme.{0}} (f : T ⟶ S) {L : LB S} (hL : L.IsLB) :
        (L.pull f).IsLB ∧ cl (L.pull f) = pl f (cl L) := by
      simpa only [Fintype.prod_unique, zpow_one] using
        linComb S T L hL PUnit (fun _ => f) (fun _ => 1)
  · have eF' : eSec P.A ≫ F.left = eSec P'.A := congrArg (·.left) (IsMonHom.one_hom F)
    apply (iso_iff _ _ _ (pull_isLB P.isLB _) (pull_isLB hN _)).1
    rw [(gen_iff _ _ (pull_isLB P.isLB _)).2 P.rigid,
      (pull_class _ hN).2, (pull_class _ P'.isLB).2, ← comp, eF',
      ← (pull_class _ P'.isLB).2, (gen_iff _ _ (pull_isLB P'.isLB _)).2 P'.rigid]
  · apply (iso_iff _ _ _ (pull_isLB P.isLB _) (pull_isLB hN _)).1
    have hL' := (iso_iff _ _ _ (pull_isLB P.isLB _) (pull_isLB P'.isLB _)).2 hL
    rw [(pull_class _ P'.isLB).2, e] at hL'
    rw [hL', (pull_class _ hN).2, (pull_class _ P'.isLB).2, ← comp, Over.comp_left]

end GlobalTheory.IsoOverField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoPolarisedAbelianSchemesDvrOfFieldExtensStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iso_polarisedAbelianSchemes_dvr_of_fieldExtension : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (P P' : PolAV (Sp V)) (C : Type) [Field C] [Algebra (FractionRing V) C] (φ : TF (R := V) C ⊗ P.A ≅ TF (R := V) C ⊗ P'.A), φ.hom ≫ fst _ _ = fst _ _ → lift (𝟙 (TF (R := V) C)) (1 : TF (R := V) C ⟶ P.A) ≫ φ.hom ≫ snd _ _ = 1 → LBIso (P.L.pull (snd (TF (R := V) C) P.A).left) (P'.L.pull (φ.hom ≫ snd (TF (R := V) C) P'.A).left) → ∀ (κ : TF (R := V) C ⟶ TK V) (g : TK V ⊗ P.A ⟶ P'.A), κ ▷ P.A ≫ g = φ.hom ≫ snd _ _ → ∃ Ψ : P.A ≅ P'.A, IsMonHom Ψ.hom ∧ φ.hom ≫ snd _ _ = snd _ _ ≫ Ψ.hom ∧ LBIso P.L (P'.L.pull Ψ.hom.left) := by
  first | exact @GlobalTheory.IsoOverField.exists_iso_over_dvr | exact GlobalTheory.IsoOverField.exists_iso_over_dvr | (intros; apply GlobalTheory.IsoOverField.exists_iso_over_dvr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapeOfGenericPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapeOfGenericPoint
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ShapeGeneric

section Bundles

variable {X X' Y Y' : Scheme.{0}}

theorem iso_linComb_pull {L : LB X} {L' : LB X'} {F : X' ⟶ X} (H : LBIso L' (L.pull F)) {K : Type} [Fintype K]
    (ψ' : K → (Y' ⟶ X')) (ψ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) (e : ∀ k, ψ' k ≫ F = h ≫ ψ k) :
    LBIso (LB.LinComb L' ψ' ε) ((LB.LinComb L ψ ε).pull h) := by
  obtain ⟨w, hw⟩ := H
  exact LBIso.chartPull (chartPullId _) (chartPullOut L ψ ε h _ e) (iso_linComb ((isGen_iff w).1 hw) ψ' ε)

end Bundles

section Group

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
  (h : IsGrpPullback G' G f φ)

variable {T : Over S} {T' : Over S'} (U : Over.mk (T'.hom ≫ f) ⟶ T)

theorem push_linComb {n : ℕ} {x' : Fin n → (T' ⟶ G')} {x : Fin n → (T ⟶ G)} (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i)
    (a : Fin n → ℕ) : pushPt h.1.w (Out.linComb x' a) = U ≫ Out.linComb x a := by
  refine (map_list_prod (pushHom h T') _).trans (Eq.trans ?_ (map_list_prod (preHom (G := G) U) _).symm)
  rw [List.map_ofFn, List.map_ofFn]
  refine congrArg (fun z => (List.ofFn z).prod) (funext fun i => ?_)
  exact (map_pow (pushHom h T') _ _).trans ((congrArg (· ^ a i) (hx i)).trans (map_pow (preHom (G := G) U) _ _).symm)

theorem push_comp {x' : T' ⟶ G'} {x : T ⟶ G} (hx : pushPt h.1.w x' = U ≫ x) {a' : G' ⟶ G'} {a : G ⟶ G}
    (ha : a'.left ≫ φ = φ ≫ a.left) : pushPt h.1.w (x' ≫ a') = U ≫ x ≫ a := by
  rw [← Category.assoc, ← hx]
  refine Over.OverMorphism.ext ?_
  show (x'.left ≫ _) ≫ _ = (x'.left ≫ _) ≫ _
  rw [Category.assoc, ha, Category.assoc]

end Group

def baseMap {S S' : Scheme.{0}} (f : S' ⟶ S) : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ Out.baseOver S :=
  Over.homMk f ((Category.comp_id _).trans (Category.id_comp _).symm)

end GlobalTheory.ShapeGeneric

namespace GlobalTheory

open ShapeGeneric

theorem relAmple_chosen_pullback {S S' : Scheme.{0}} {A : Over S} [IsProper A.hom] {A' : Over S'} {x : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (H : IsPullback φ A'.hom A.hom x) {M : LB A.left} {M' : LB A'.left} (hM : M.IsLB)
    (hM' : M'.IsLB) (a : LBIso M' (M.pull φ)) (c : Out.RelAmple A' M') :
    Out.RelAmple ((Over.pullback x).obj A) (M.pull (pullback.fst A.hom x)) := by
  have : IsProper A'.hom := MorphismProperty.of_isPullback (P := @IsProper) H ‹_›
  have P : IsPullback (pullback.fst A.hom x) (pullback.snd A.hom x) A.hom (𝟙 S' ≫ x) :=
    (Category.id_comp x).symm ▸ IsPullback.of_hasPullback A.hom x
  let ψ : pullback A.hom x ⟶ A'.left := H.lift (pullback.fst _ _) (pullback.snd _ _ ≫ 𝟙 S')
    (P.w.trans (Category.assoc _ _ _).symm)
  have hψ : ψ ≫ φ = pullback.fst _ _ := H.lift_fst _ _ _
  have Q : IsPullback ψ (pullback.snd A.hom x) A'.hom (𝟙 S') :=
    IsPullback.of_right (hψ ▸ P) (H.lift_snd _ _ _) H
  have R := AmpleBaseChange.relAmple_of_isPullback hM' c Q
  have e : LBIso (M'.pull ψ) (M.pull (pullback.fst A.hom x)) :=
    a.chartPull (GlobalTheory.chartPullPull M' ψ) (chartPullSame M _ _ _ ψ fun _ => hψ.symm)
  have pr : IsProper (Over.mk (pullback.snd A.hom x)).hom := inferInstanceAs (IsProper (pullback.snd A.hom x))
  have h₁ := LB.isLB_pull hM' ψ
  have h₂ := LB.isLB_pull hM (pullback.fst A.hom x)
  exact (relAmple_iff_isAmpleLB (Over.mk (pullback.snd A.hom x)) h₂).2 fun U hU =>
    ((relAmple_iff_isAmpleLB (Over.mk (pullback.snd A.hom x)) h₁).1 R U hU).of_lbIso (LB.isLB_pull h₂ _)
      (LBIso.chartPull (GlobalTheory.chartPullPull _ _) (GlobalTheory.chartPullPull _ _) e.symm)

theorem shape_of_generic : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) Mat κ (S : Scheme.{0}) [IsLocallyNoetherian S] [IsIntegral S] (s : S ⟶ Sp o) (t : TObj g k J b s) (K : Type) [Field K] (x : Sp K ⟶ S) (s' : Sp K ⟶ Sp o) (tK : TObj g k J b s'), Set.range x = {genericPoint S} → TMap tK t x → tK.Shape Mat κ → t.Shape Mat κ := by
  intro l₁ l₂ o _ g k J b Mat κ S _ _ s t K _ x s' t' hx ⟨φ, h, hL, hpt, hact⟩ H j
  have := t.ab.proper
  have dom : IsDominant x := ⟨by
    rw [DenseRange, hx]
    exact dense_iff_closure_eq.2 (genericPoint_closure S)⟩
  have lb : ∀ {X Y : Scheme.{0}} {L : LB X} (_ : L.IsLB) {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (ε : K → ℤ),
      (LB.LinComb L ψ ε).IsLB := fun hL _ _ _ _ => DVR.linComb_isLB _ hL _ _
  have pt : ∀ i, pushPt h.1.w (t'.pt i) = baseMap x ≫ t.pt i := fun i => Over.OverMorphism.ext (hpt i)
  have p₁ := fun i => push_comp h _ (pt i) (hact j)
  have p₂ : ∀ a, pushPt h.1.w (t'.lab a) = baseMap x ≫ t.lab a := fun a => push_linComb h _ pt _
  have i₁ : LBIso (LB.LinComb t'.L (K := Fin 2) ![𝟙 t'.A.left, (t'.act j).left] ![(κ : ℤ), -1])
      ((LB.LinComb t.L (K := Fin 2) ![𝟙 t.A.left, (t.act j).left] ![(κ : ℤ), -1]).pull φ) :=
    iso_linComb_pull hL _ _ _ φ fun i => by
      fin_cases i
      exacts [(Category.id_comp _).trans (Category.comp_id _).symm, hact j]
  refine ⟨fun i => ?_, GlobalTheory.AmpleSpecialisation.relAmple_of_genericFibre l₁ l₂ S t.pol _ K x (lb t.isLB _ _) hx
    (relAmple_chosen_pullback h.1 (lb t.isLB _ _) (lb t'.isLB _ _) i₁ (H j).2)⟩
  have e := (p₁ i).symm.trans (((H j).1 i).symm ▸ p₂ _)
  refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := S) t.A.hom ?_ x
    (congrArg (fun q => q.left) e))
  exact (Over.w _).trans (Over.w _).symm

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapeOfGenericPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLevelShape_of_generic_point : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) Mat κ (S : Scheme.{0}) [IsLocallyNoetherian S] [IsIntegral S] (s : S ⟶ Sp o) (t : TObj g k J b s) (K : Type) [Field K] (x : Sp K ⟶ S) (s' : Sp K ⟶ Sp o) (tK : TObj g k J b s'), Set.range x = {genericPoint S} → TMap tK t x → tK.Shape Mat κ → t.Shape Mat κ := by
  first | exact @GlobalTheory.shape_of_generic | exact GlobalTheory.shape_of_generic | (intros; apply GlobalTheory.shape_of_generic <;> assumption)
end
end
