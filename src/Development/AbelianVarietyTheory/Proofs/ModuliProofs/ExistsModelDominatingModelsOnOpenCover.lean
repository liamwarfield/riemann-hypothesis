module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieComb
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsUniquePairIff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimilitudeOfAutModLevelIdeal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyMorphismFromVeryDenseGraphs
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GraphInversionEndomorphismCutBoundedDegree

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelDominatingModelsOnOpenCover
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelDominatingModelsOnOpenCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

namespace ModelJoin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem comp_of_eq {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {h : S'' ⟶ S} (m : SABMap t' t f) (m' : SABMap t'' t' g) (e : g ≫ f = h) :
    ∃ n : SABMap t'' t h, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabComp pullCubComp E H _ _ _ t t' t'' f g m m'

theorem cancel_of_eq {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {h : S'' ⟶ S} (m : SABMap t' t f) (n : SABMap t'' t h) (e : g ≫ f = h) :
    ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabCancel pullCubCancel E H _ _ _ t t' t'' f g m n

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
    ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

theorem isOpenImmersion_away {O R : Type} [CommRing O] [CommRing R] (a : O) (b : O →+* R)
    (h : @IsLocalization.Away O _ a R _ b.toAlgebra) : IsOpenImmersion (spMap b) := by
  letI := b.toAlgebra
  exact IsOpenImmersion.of_isLocalization (R := O) (S := R) a

theorem mem_range_away {O R : Type} [CommRing O] [CommRing R] (a : O) (b : O →+* R)
    (h : @IsLocalization.Away O _ a R _ b.toAlgebra) (x : Sp O) (hx : a ∉ x.asIdeal) :
    x ∈ Set.range (spMap b) := by
  letI := b.toAlgebra
  have := PrimeSpectrum.localization_away_comap_range R a
  have h2 : (x : PrimeSpectrum O) ∈ Set.range (PrimeSpectrum.comap (algebraMap O R)) := by
    rw [this]; exact hx
  exact h2

theorem arith_base (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Algebra.FiniteType ℤ O] :
    LocallyOfFiniteType (spMap (algebraMap ℤ O)) ∧ Flat (spMap (algebraMap ℤ O)) := by
  constructor
  · rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  · rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance

end ModelJoin

open ModelJoin

theorem exists_join_of_models : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (I : Type) [Finite I] [Nonempty I] (R : I → Type) [∀ i, CommRing (R i)] (a : I → O) (b : ∀ i, O →+* R i) (ω : ∀ i, R i →+* F) (C : ∀ i, Cpt c t (ω i)), IsDedFrac β → (∀ i, IsDedFrac (ω i) ∧ (ω i).comp (b i) = β ∧ @IsLocalization.Away O _ (a i) (R i) _ (b i).toAlgebra) → Ideal.span (Set.range a) = ⊤ → Algebra.FiniteType ℤ O → IsProper t.G.hom → ∃ C' : Cpt c t β, ∀ i, ∃ (f : pullback C'.s (spMap (b i)) ⟶ (C i).X) (t₁ : SAB H (pullback C'.s (spMap (b i)))) (m₁ : SABMap t₁ C'.t (pullback.fst _ _)) (m₂ : SABMap t₁ (C i).t f), f ≫ (C i).s = pullback.snd _ _ ∧ (∀ g : U ⟶ pullback C'.s (spMap (b i)), g ≫ pullback.fst _ _ = C'.j → g ≫ f = (C i).j) ∧ ∀ y : t.G.left ⟶ t₁.G.left, y ≫ m₁.φ = C'.m.φ → y ≫ m₂.φ = (C i).m.φ := by
  intro hext E _ _ _ H U F O _ _ c t β I _ _ R _ a b ω C hβ hω hspan hft hprop
  obtain ⟨⟨hdom, hded⟩, hchar, hfrac⟩ := id hβ
  obtain ⟨X, s, jQ, f, hn, hproj, hflat, hover, hopen, hdense, hf⟩ :=
    GlobalTheory.T.exists_join_normal_projective_models E H U F O c t β I R a b ω C hβ hω hspan hchar
  have hpo : IsPreimmersion (jQ ≫ pullback.fst s (spMap β)) ∧ Flat (jQ ≫ pullback.fst s (spMap β)) ∧
      IsDominant (jQ ≫ pullback.fst s (spMap β)) ∧ QuasiCompact (jQ ≫ pullback.fst s (spMap β)) := by
    letI := β.toAlgebra
    exact (genericPart_dense_proOpen O F X U s jQ hflat hproj hopen hdense).2.2.2
  have hβp : IsPreimmersion (spMap β) := by
    letI := β.toAlgebra
    exact IsPreimmersion.of_isLocalization (R := CommRingCat.of O) (S := F) (nonZeroDivisors O)
  have hfp : IsPreimmersion (pullback.fst s (spMap β)) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hβp
  have hb : ∀ i, IsOpenImmersion (spMap (b i)) := fun i => isOpenImmersion_away (a i) (b i) (hω i).2.2
  have hβe : ∀ i, spMap β = spMap (ω i) ≫ spMap (b i) := fun i => by
    rw [← (hω i).2.1]; exact Spec.map_comp (CommRingCat.ofHom (b i)) (CommRingCat.ofHom (ω i))
  have hsp : IsProper s := projProper O X s hproj
  let V : I → X.Opens := fun i => (pullback.fst s (spMap (b i))).opensRange
  let e : ∀ i, pullback s (spMap (b i)) ≅ (V i).toScheme := fun i =>
    (pullback.fst s (spMap (b i))).isoOpensRange
  have he : ∀ i, (e i).hom ≫ (V i).ι = pullback.fst s (spMap (b i)) := fun i =>
    Scheme.Hom.isoOpensRange_hom_ι _
  have hcov' : ∀ x : X, ∃ i, x ∈ Set.range (pullback.fst s (spMap (b i))) := by
    intro x
    have : ∃ i, a i ∉ (s x).asIdeal := by
      by_contra hc
      push Not at hc
      refine (s x).isPrime.ne_top (top_le_iff.mp ?_)
      rw [← hspan, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hc i
    obtain ⟨i, hi⟩ := this
    refine ⟨i, ?_⟩
    rw [Scheme.Pullback.range_fst]
    exact mem_range_away (a i) (b i) (hω i).2.2 _ hi
  have hcov : ⨆ i, V i = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    obtain ⟨i, hi⟩ := hcov' x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  have hw : ∀ i, (jQ ≫ pullback.fst s (spMap β)) ≫ s = (c ≫ spMap (ω i)) ≫ spMap (b i) := fun i => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hover, Category.assoc, ← hβe]
  let g : ∀ i, U ⟶ pullback s (spMap (b i)) := fun i => pullback.lift _ _ (hw i)
  have hg : ∀ i, g i ≫ pullback.fst _ _ = jQ ≫ pullback.fst s (spMap β) := fun i => pullback.lift_fst _ _ _
  choose tV mV using fun i => exists_pull ((e i).inv ≫ f i) (C i).t
  replace mV := fun i => (mV i).some
  choose t₁ k using fun i => exists_pull (e i).hom (tV i)
  replace k := fun i => (k i).some
  choose aV haV using fun i => cancel_of_eq (g := g i ≫ (e i).hom) (mV i) (C i).m (by
    rw [Category.assoc, Iso.hom_inv_id_assoc]; exact (hf i).2.1 _ (hg i))
  obtain ⟨hz₁, hz₂⟩ := arith_base O
  obtain ⟨t', a', n, hn'⟩ := GlobalTheory.T.exists_semiAbelianTriple_glue_common_genericPart hext E H X U (jQ ≫ pullback.fst s (spMap β)) t I V
    (fun i => g i ≫ (e i).hom) tV aV inferInstance
    ⟨hn, s ≫ spMap (algebraMap ℤ O), inferInstance, inferInstance⟩ hpo.1 hpo.2.1 hpo.2.2.1 hpo.2.2.2 hprop hcov
    (fun i => by rw [Category.assoc, he, hg])
  choose m₁ hm₁ using fun i => comp_of_eq (n i) (k i) (he i)
  choose m₂ hm₂ using fun i => comp_of_eq (h := f i) (mV i) (k i) (Iso.hom_inv_id_assoc _ _)
  have hab : pullback.fst s (spMap β) ⁻¹' abLocus t'.G = Set.range jQ := by
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨i, w, hw'⟩ := hcov' (pullback.fst s (spMap β) z)
      have h1 : w ∈ abLocus (t₁ i).G :=
        (abLocus_pullback abLocusOne t'.semi (m₁ i).cart.1 w).1 (by rw [hw']; exact hz)
      have h2 : f i w ∈ abLocus (C i).t.G :=
        (abLocus_pullback abLocusOne (C i).t.semi (m₂ i).cart.1 w).2 h1
      have h3 : f i w ∈ Set.range (pullback.fst (C i).s (spMap (ω i))) := by
        rw [Scheme.Pullback.range_fst]
        refine ⟨pullback.snd s (spMap β) z, (spMap (b i)).isOpenEmbedding.injective ?_⟩
        rw [← Scheme.Hom.comp_apply, ← hβe, ← Scheme.Hom.comp_apply, ← pullback.condition,
          ← Scheme.Hom.comp_apply (f i), (hf i).1, ← Scheme.Hom.comp_apply, ← pullback.condition,
          Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hw']
      obtain ⟨z', hz'⟩ := h3
      have h4 : z' ∈ Set.range (C i).jQ := by
        rw [← (C i).ab_gen]
        show _ ∈ abLocus (C i).t.G
        rw [hz']; exact h2
      obtain ⟨u, hu⟩ := h4
      obtain ⟨u', hu'⟩ := (hf i).2.2 w ⟨u, by rw [Cpt.j, Scheme.Hom.comp_apply, hu, hz']⟩
      refine ⟨u', (pullback.fst s (spMap β)).isEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hu', hw']
    · rintro _ ⟨u, rfl⟩
      exact range_subset_abLocus_of_isProper t'.semi a'.cart.1 ⟨u, Scheme.Hom.comp_apply _ _ _⟩
  refine ⟨⟨X, s, hn, hproj, hflat, jQ, hover, hopen, hdense, t', a', hab⟩, fun i => ?_⟩
  refine ⟨f i, t₁ i, m₁ i, m₂ i, (hf i).1, (hf i).2.1, fun y hy => ?_⟩
  have hmono : IsOpenImmersion (n i).φ :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (n i).cart.1.flip inferInstance
  have hy' : y ≫ (k i).φ = (aV i).φ := by
    rw [← cancel_mono (n i).φ, Category.assoc, ← hm₁, hn']; exact hy
  rw [hm₂, ← Category.assoc, hy', haV]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelDominatingModelsOnOpenCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_model_dominating_models_on_open_cover : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (I : Type) [Finite I] [Nonempty I] (R : I → Type) [∀ i, CommRing (R i)] (a : I → O) (b : ∀ i, O →+* R i) (ω : ∀ i, R i →+* F) (C : ∀ i, Cpt c t (ω i)), IsDedFrac β → (∀ i, IsDedFrac (ω i) ∧ (ω i).comp (b i) = β ∧ @IsLocalization.Away O _ (a i) (R i) _ (b i).toAlgebra) → Ideal.span (Set.range a) = ⊤ → Algebra.FiniteType ℤ O → IsProper t.G.hom → ∃ C' : Cpt c t β, ∀ i, ∃ (f : pullback C'.s (spMap (b i)) ⟶ (C i).X) (t₁ : SAB H (pullback C'.s (spMap (b i)))) (m₁ : SABMap t₁ C'.t (pullback.fst _ _)) (m₂ : SABMap t₁ (C i).t f), f ≫ (C i).s = pullback.snd _ _ ∧ (∀ g : U ⟶ pullback C'.s (spMap (b i)), g ≫ pullback.fst _ _ = C'.j → g ≫ f = (C i).j) ∧ ∀ y : t.G.left ⟶ t₁.G.left, y ≫ m₁.φ = C'.m.φ → y ≫ m₂.φ = (C i).m.φ := by
  first | exact @GlobalTheory.exists_join_of_models | exact GlobalTheory.exists_join_of_models | (intros; apply GlobalTheory.exists_join_of_models <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePartImageGeneric
noncomputable section

namespace GlobalTheory.FinitePartGeneric

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

theorem exists_normal_factor (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R]
    (hR : AdmBase R (maximalIdeal R)) (F : Type) [Field F] [Algebra (FractionRing R) F] (A : Type) [CommRing A]
    [Algebra R A] [Module.Finite R A] (ψ : A →+* F)
    (hψ : ∀ r, ψ (algebraMap R A r) = algebraMap (FractionRing R) F (algebraMap R _ r)) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (_ : Algebra (FractionRing R') F)
      (a : A →+* R'), AdmBase R' (maximalIdeal R') ∧
      (maximalIdeal R).map (a.comp (algebraMap R A)) ≤ maximalIdeal R' ∧
      ∀ y, algebraMap (FractionRing R') F (algebraMap R' _ (a y)) = ψ y := by
  obtain ⟨h₁, -, h₃, h₄⟩ := hR
  letI : Algebra R F := ((algebraMap (FractionRing R) F).comp (algebraMap R _)).toAlgebra
  have : IsScalarTower R (FractionRing R) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ψ' : A →ₐ[R] F := { ψ with commutes' := hψ }
  have hi : ∀ y, IsIntegral R (ψ y) := fun y => (Algebra.IsIntegral.isIntegral (R := R) y).map ψ'
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := A)
  let L := IntermediateField.adjoin (FractionRing R) (ψ '' s)
  have : Finite (ψ '' s) := (s.finite_toSet.image ψ).to_subtype
  have : FiniteDimensional (FractionRing R) L :=
    IntermediateField.finiteDimensional_adjoin (by rintro _ ⟨y, -, rfl⟩; exact (hi y).tower_top)
  have hm : ∀ y, ψ y ∈ L := fun y => by
    have hy : y ∈ Submodule.span R (s : Set A) := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul r y _ hy => rw [Algebra.smul_def, map_mul, hψ]; exact mul_mem (L.algebraMap_mem _) hy
  obtain ⟨f₁, f₂, f₃, f₄, -⟩ := integralClosure_finite_local_of_isAdicComplete R h₄ L
  have : IsScalarTower R L F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let j : integralClosure R L →+* F := (algebraMap L F).comp (algebraMap _ L)
  have hj : Function.Injective j := Subtype.val_injective.comp Subtype.val_injective
  let a : A →+* integralClosure R L := (ψ.codRestrict L hm).codRestrict (integralClosure R L) fun y =>
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom R L F) Subtype.val_injective).1 (hi y)
  have ha : a.comp (algebraMap R A) = algebraMap R _ := RingHom.ext fun r => hj (hψ r)
  refine ⟨integralClosure R L, inferInstance, inferInstance, f₂, (IsFractionRing.lift (g := j) hj).toAlgebra, a,
    ⟨f₃, inferInstance, f₄, CompleteFiniteExtension.isAdicComplete_of_finite_local R _⟩, ?_,
    fun y => IsFractionRing.lift_algebraMap (g := j) hj _⟩
  rw [ha]
  exact ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.map_maximalIdeal_le_maximal (R := R) _ _ inferInstance

theorem exists_normal_point (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R]
    (hR : AdmBase R (maximalIdeal R)) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : Over (Sp R))
    [IsFinite N.hom] (x : Sp F ⟶ N.left) (hx : x ≫ N.hom = jFK (R := R) F ≫ jK R) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (_ : Algebra (FractionRing R') F)
      (φ : R →+* R') (ξ : Sp R' ⟶ N.left), AdmBase R' (maximalIdeal R') ∧
      (maximalIdeal R).map φ ≤ maximalIdeal R' ∧ ArcPull.Compat φ F ∧ ξ ≫ N.hom = spMap φ ∧
      (jFK (R := R') F ≫ jK R') ≫ ξ = x := by
  have : IsAffine N.left := isAffine_of_isAffineHom N.hom
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (N.left.isoSpec.inv ≫ N.hom)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (x ≫ N.left.isoSpec.hom)
  have hf : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  rw [IsFinite.SpecMap_iff] at hf
  letI : Algebra R Γ(N.left, ⊤) := φ.hom.toAlgebra
  have : Module.Finite R Γ(N.left, ⊤) := hf
  have e : φ ≫ ψ = CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫
      CommRingCat.ofHom (algebraMap (FractionRing R) F) := Spec.map_injective (by
    rw [Spec.map_comp, Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc, hx])
  have e' : ∀ r, ψ.hom (φ.hom r) = algebraMap (FractionRing R) F (algebraMap R _ r) := fun r =>
    congrArg (fun q => q.hom r) e
  obtain ⟨R', i₁, i₂, i₃, i₄, a, h₁, h₂, h₃⟩ := exists_normal_factor R hR F Γ(N.left, ⊤) ψ.hom e'
  refine ⟨R', i₁, i₂, i₃, i₄, a.comp φ.hom, Spec.map (CommRingCat.ofHom a) ≫ N.left.isoSpec.inv, h₁, h₂,
    fun r => (e' r).symm.trans (h₃ _).symm, ?_, ?_⟩
  · rw [Category.assoc, ← hφ, ← Spec.map_comp]; rfl
  · rw [← Category.assoc, Iso.comp_inv_eq, ← hψ, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext h₃))

section Transport

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ConstLin GlobalTheory.FormalPoint
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}

theorem isPointOf_thru {I : Ideal R} {I' : Ideal R'} {D : DegData R I} {D' : DegData R' I'}
    {hD : IsPullDeg φ D.toPre D'.toPre} {A : PolAV (Sp (FractionRing R))} {A' : PolAV (Sp (FractionRing R'))}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G']
    {bc : G' ≅ (Over.pullback (specOf φ)).obj G} {U : Unif I D A G} {U' : Unif I' D' A' G'}
    (hU : IsPullUnif φ hD bc U U') {T : Over (Sp R)} {T' : Over (Sp R')} {h : T'.left ⟶ T.left}
    {g₀ : GtPt D.toPre T} {g : GtPt D'.toPre T'} (H : Thru hD.w hD.xe h g₀ g) {x₀ : T ⟶ G} {x : T' ⟶ G'}
    (hx : x.left ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = h ≫ x₀.left)
    (h₀ : IsPointOf U.toUnifPre g₀ x₀) : IsPointOf U'.toUnifPre g x := by
  intro e Z r y hy
  obtain ⟨wL, -, he, -, HU⟩ := (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U U').1 hU
  obtain ⟨k, hf, hpt, -⟩ := HU e
  have gp := pull_grp hD
  obtain ⟨cb, cv⟩ := (hasCoords_iff _ _ _ _ _).1 (h₀ e Z (r ≫ h) (y ≫ k) (by
    rw [Category.assoc, hf, ← Category.assoc, hy, Category.assoc, hx, Category.assoc]))
  have hy' : y ≫ ((Over.map (thick R' I' e)).obj (thickObj R' I' e G')).hom = r ≫ T'.hom := by
    rw [← Over.w (fstG I' e G'), ← Category.assoc, hy, Category.assoc, Over.w]
  let y' : Over.mk (r ≫ T'.hom) ⟶ (Over.map (thick R' I' e)).obj (thickObj R' I' e G') := Over.homMk y hy'
  let r' : Over.mk (r ≫ T'.hom) ⟶ T' := Over.homMk r rfl
  have hb : y ≫ (U'.gt e).pG.left = r ≫ g.b.left := gp.1.hom_ext
    ((Category.assoc _ _ _).trans ((congrArg (y ≫ ·) hpt.1).trans ((Category.assoc _ _ _).symm.trans (cb.trans
      ((Category.assoc _ _ _).trans ((congrArg (r ≫ ·) ((H 0).1 2).symm).trans (Category.assoc _ _ _).symm))))))
    (by rw [Category.assoc, Category.assoc, Over.w, Over.w]; exact hy')
  refine (hasCoords_iff _ _ _ _ _).2 ⟨hb, fun χ z J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := ConstFam.exists_good' D.toPre.P.isLB z
  have v := ConstFam.pmaps_val (hpt.2 χ).1 (hpt.2 χ).2 y hJ hJ'
  have eP : ∏ i, ConstFam.wVal hD.w z J J' (y ≫ D'.toPre.Oφ (U'.gt e).pG χ i) ^ Oinvε i =
      ∏ i, ConstFam.wVal hD.w z J J' (r ≫ DegPre.gtφT D'.toPre T' g.b χ i) ^ DegPre.gtε i :=
    Finset.prod_congr rfl fun i _ => congrArg (fun q => ConstFam.wVal hD.w z J J' q ^ DegPre.gtε i)
      (comp_Oφ y' r' _ _ (Over.OverMorphism.ext hb) χ i)
  rw [eP] at v
  exact mul_left_cancel (v.symm.trans ((cv _ z J hJ).trans ((H χ).2 _ r z J J' hJ hJ')))

theorem isPullGtF_thru {D : DegPre R} {D' : DegPre R'} {hD : IsPullDeg φ D D'} {T : Over (Sp R)} {T' : Over (Sp R')}
    {h : T'.left ⟶ T.left} {g₀ : GtPt D T} {g : GtPt D' T'} (H : Thru hD.w hD.xe h g₀ g) {F : Type} [Field F]
    [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] {σ : Sp F ⟶ T'.left} {q : GtPtF D F}
    {q' : GtPtF D' F} (hq : GtPt.IsPullF F (σ ≫ h) g₀ q) (hq' : GtPt.IsPullF F σ g q') : IsPullGtF φ hD F q q' := by
  have m := FieldRestrictionTest.maps_eq hq
  have m' := FieldRestrictionTest.maps_eq hq'
  have hψ : ∀ χ i, DegPre.gtφ D' F q'.b χ i ≫ proj hD = 𝟙 _ ≫ DegPre.gtφ D F q.b (hD.xe χ) i := fun χ i => by
    rw [m, m', Category.id_comp]
    exact (Category.assoc _ _ _).trans ((congrArg (σ ≫ ·) ((H χ).1 i)).trans (Category.assoc _ _ _).symm)
  refine ⟨(hψ 0 2).trans (Category.id_comp _), fun χ => ⟨hψ χ, maps_of_good ((isGen_iff _).1 hD.w_gen) D.P.isLB
    D'.P.isLB _ (q'.isGen χ) _ (q.isGen _) (hψ χ) fun y J J' hJ hJ' => ?_⟩⟩
  have a := (val_corr hJ (hq.2 (hD.xe χ)) (𝟙 _)).trans (val_pull hJ _ _ _)
  have a' := (val_corr hJ' (hq'.2 χ) (𝟙 _)).trans (val_pull hJ' _ _ _)
  rw [Category.id_comp] at a a'
  refine a.trans (((H χ).2 _ σ y J J' hJ hJ').trans (congrArg₂ (· * ·) ?_ a'.symm))
  exact Finset.prod_congr rfl fun i _ => congrArg (fun q => ConstFam.wVal hD.w y J J' q ^ DegPre.gtε i) (m' χ i).symm

end Transport

theorem main : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∀ (N : Over (Sp R)) (g₀ : GtPt P.D.toPre N) (x₀ : N ⟶ t.G), IsFinitePart P.U.toUnifPre k N g₀ x₀ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : Sp F ⟶ N.left), OverGen F N x → ∀ q : QkPt P.D.toPre F k, q.y = 0 → GtPt.IsPullF F x g₀ q.g → IsImage P F k q (x ≫ x₀.left) := by
  intro E _ _ _ H R _ _ _ _ hR t P W _ _ ψW k hk N g₀ x₀ hN F _ _ _ x hx q hq hg
  have hL := firstFiveLaws
  have := hN.finite
  obtain ⟨R', _, _, _, _, φ, ξ, hR', hI, hF, hξ, rfl⟩ := exists_normal_point R hR F N x hx
  have hφ : Function.Injective φ := fun a b e => IsFractionRing.injective R (FractionRing R)
    ((algebraMap (FractionRing R) F).injective (by rw [hF a, hF b, e]))
  obtain ⟨D', hD, A', U', hU⟩ := UT.EndBaseChange.exists_pull hL.1.polBaseChange hL.2.2.2.1.unifBaseChange
    hL.2.2.2.2.psiOnExists hR hR' φ hφ hI t.semi P.U
  have hh : ξ ≫ N.hom = (𝟙_ (Over (Sp R'))).hom ≫ spMap φ := hξ.trans (Category.id_comp _).symm
  obtain ⟨gp, hgp⟩ : ∃ gp : GtPt D'.toPre (𝟙_ (Over (Sp R'))), ConstLin.Thru hD.w hD.xe (T' := 𝟙_ _) ξ g₀ gp :=
    ConstPoint.exists_gtPt_through hL.1.globalFns (pull_grp hD) hD.w_gen hD.xe.toAddMonoidHom hD.c_pr
      (T' := 𝟙_ _) ξ hh g₀
  let x₁ : 𝟙_ (Over (Sp R')) ⟶ (Over.pullback (specOf φ)).obj t.G :=
    Over.homMk (pullback.lift (ξ ≫ x₀.left) (𝟙_ (Over (Sp R'))).hom (by rw [Category.assoc, Over.w]; exact hh))
      (pullback.lift_snd _ _ _)
  have e₁ : x₁.left ≫ pullback.fst t.G.hom (specOf φ) = ξ ≫ x₀.left := pullback.lift_fst _ _ _
  have e₂ : x₁.left ≫ (Iso.refl ((Over.pullback (specOf φ)).obj t.G)).hom.left ≫ pullback.fst t.G.hom (specOf φ) =
      ξ ≫ x₀.left := (congrArg (x₁.left ≫ ·) (Category.id_comp _)).trans e₁
  have gG := isGrpPullback_pullback t.G (spMap φ)
  have hk₁ : x₁ ^ k = 1 := ConstGrp.push_injective gG _ (by
    let ρ : Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap φ) ⟶ N := Over.homMk ξ hh
    have e : pushHom gG _ x₁ = ρ ≫ x₀ := Over.OverMorphism.ext e₁
    rw [map_pow, map_one, e, ← MonObj.comp_pow, hN.g_tors, MonObj.comp_one])
  have hp := isPointOf_thru hU hgp e₂ ((TorsionFormCompare.formalEq_iff _ _ _).1 hN.formal)
  obtain ⟨g', hg'⟩ := FieldRestrictionTest.exists_isPullF (toUnit (TF (R := R') F)) gp
  let y : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj t.G :=
    Over.homMk (pullback.lift (((jFK (R := R') F ≫ jK R') ≫ ξ) ≫ x₀.left) (jFK (R := R) F)
      (by rw [Category.assoc, Over.w]; exact hx)) (pullback.lift_snd _ _ _)
  have hy : (y ≫ P.U.gen.hom).left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) =
      ((jFK (R := R') F ≫ jK R') ≫ ξ) ≫ x₀.left := by
    rw [← Category.assoc, ← Over.comp_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact pullback.lift_fst _ _ _
  refine ⟨_, hy, FiniteTorsionExt.main hL.1 R R' _ _ hR hR' φ P.D P.A t.G P.U _ (Iso.refl _)
    (by show IsMonHom (𝟙 _); infer_instance) A' D' hD U' hU (maximalIdeal.isMaximal R').ne_top F hF k hk x₁ gp hk₁
    (fun e => ?_) q g' _ hq (isPullGtF_thru hgp hg hg') hg' ?_⟩
  · let xe : Over.mk (thick R' (maximalIdeal R') e) ⟶ (Over.map (thick R' (maximalIdeal R') e)).obj
        (thickObj R' (maximalIdeal R') e ((Over.pullback (specOf φ)).obj t.G)) :=
      Over.homMk (pullback.lift (toUnit (Over.mk (thick R' (maximalIdeal R') e)) ≫ x₁).left (𝟙 _)
        ((Over.w _).trans (Category.id_comp _).symm))
        (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (pullback.lift_snd _ _ _))).trans (Category.id_comp _))
    have hxe : xe ≫ fstG _ e _ = toUnit _ ≫ x₁ := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    have c := hp e _ (toUnit (Over.mk (thick R' (maximalIdeal R') e))).left xe.left (congrArg (·.left) hxe)
    exact ⟨xe, hxe, Over.OverMorphism.ext c.1, c.2⟩
  · rw [hy, Over.comp_left, Category.assoc (toUnit (TF (R := R') F)).left, e₂]
    exact Category.assoc _ _ _

end GlobalTheory.FinitePartGeneric
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTransferPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

open GlobalTheory.HeckePoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem exists_transfer_pts {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'} {X S : Scheme.{0}}
    {sX : X ⟶ Sp B} {s : S ⟶ Sp B'} {u : Obj D l b sX} {o : Obj D l b' s} {f : S ⟶ X} (m : ObjMap o u f)
    {k : Type} [Field k] (z : Sp k ⟶ S) :
    ∃ ρ : (Over.mk z ⟶ o.t.G) ≃* (Over.mk (z ≫ f) ⟶ u.t.G),
      (∀ x, (ρ x).left = x.left ≫ m.toSABMap.φ) ∧
      (∀ a x, ρ (x ≫ o.t.act.act a) = ρ x ≫ u.t.act.act a) ∧
      (∀ (n : ℤ) x x' (c : kˣ), Out.WeilIs o.t.G o.t.PP.L n x x' (unitOn c) ↔
        Out.WeilIs u.t.G u.t.PP.L n (ρ x) (ρ x') (unitOn c)) ∧
      (∀ a, ρ (toUnit _ ≫ o.eta a) = toUnit _ ≫ u.eta a) ∧ ∀ a, ρ (toUnit _ ≫ o.etaA a) = toUnit _ ≫ u.etaA a := by
  obtain ⟨ρ, hρ⟩ := exists_ptsEquiv m.cart (Over.mk z) (z ≫ f) rfl
  obtain ⟨w, hw, -⟩ := m.lin
  have tu : (toUnit (Over.mk z)).left = z := by simp
  have tv : (toUnit (Over.mk (z ≫ f))).left = z ≫ f := by simp
  refine ⟨ρ, hρ, fun a x => Over.OverMorphism.ext ?_,
    fun n x x' c => GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ f m.cm.F _ _ u.t.PP.isLB o.t.PP.isLB m.cart ⟨w, hw⟩
      (Over.mk z) n x x' _ _ _ (hρ x) (hρ x'), fun a => Over.OverMorphism.ext ?_,
    fun a => Over.OverMorphism.ext ?_⟩
  · rw [hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, m.act, Category.assoc]
  · rw [hρ, Over.comp_left, Over.comp_left, tu, tv, Category.assoc, m.eta a, Category.assoc]
  · rw [hρ, Over.comp_left, Over.comp_left, tu, tv, Category.assoc, m.etaA a, Category.assoc]

theorem pointQuot_snd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo 𝔓 p i), admitted l 𝔓 p → ∀ (k : Type) [Field k] [IsAlgClosed k] (z : Sp k ⟶ Z.Hk) (y : Sp k ⟶ Xo.X) (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G)), Z.toKerScheme.Carries z y C → PointQuot Xo p y (z ≫ Z.π₂) C := by
  intro E _ _ _ H D l Xo 𝔓 p i Z hA k _ _ z y C hC
  obtain ⟨rfl, hC⟩ := hC
  have hp : p.Prime := hA.2.2.1
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨⟨hom, hfin, het, hsur, hlin, hiso⟩, hlev⟩ := Z.isog
  have := Xo.smooth
  have := Z.et₁
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  have : IsLocallyNoetherian Z.Hk := LocallyOfFiniteType.isLocallyNoetherian Z.π₁
  obtain ⟨ρ, e₂, e₃, e₄, e₅, e₆⟩ := exists_transfer_pts Z.m₁ z
  obtain ⟨ρ₁, f₂, f₃, f₄, f₅, f₆⟩ := exists_transfer_pts Z.m₂ z
  let σ : (Over.mk z ⟶ Z.o₁.t.G) →* (Over.mk z ⟶ Z.o₂.t.G) :=
    MonoidHom.mk' (fun x => x ≫ Z.ψ) fun a c => MonObj.mul_comp a c Z.ψ
  let ψp := ρ₁.toMonoidHom.comp (σ.comp ρ.symm.toMonoidHom)
  have hψ : ∀ x, ψp (ρ x) = ρ₁ (x ≫ Z.ψ) := fun x => congrArg (fun u => ρ₁ (u ≫ Z.ψ)) (ρ.symm_apply_apply x)
  have c₁ := Z.m₁.cart.1
  have c₂ := Z.m₂.cart.1
  let α : pullback Xo.univ.t.G.hom (z ≫ Z.π₁) ⟶ Z.o₁.t.G.left :=
    c₁.lift (pullback.fst _ _) (pullback.snd _ _ ≫ z) (by rw [pullback.condition, Category.assoc])
  have α₁ : α ≫ Z.m₁.cm.F = pullback.fst _ _ := c₁.lift_fst _ _ _
  have α₂ : α ≫ Z.o₁.t.G.hom = pullback.snd _ _ ≫ z := c₁.lift_snd _ _ _
  have hα : ∀ x, fibPt _ (ρ x) ≫ α = x.left := fun x => c₁.hom_ext
    (by rw [Category.assoc, α₁, fibPt, pullback.lift_fst, e₂])
    (by rw [Category.assoc, α₂, fibPt, pullback.lift_snd_assoc, Over.w x]; exact Category.id_comp _)
  refine ⟨by rw [Category.assoc, Category.assoc, Z.base₂], pullback.lift (α ≫ Z.ψ.left ≫ Z.m₂.cm.F) (pullback.snd _ _)
    (by rw [Category.assoc, Category.assoc, c₂.w, Over.w_assoc, reassoc_of% α₂]), ψp, pullback.lift_snd _ _ _,
    fun x => ?_, fun a x => ?_, fun v => ?_, Subgroup.ext fun x => ?_, fun n x x' c hn h => ?_, fun p' hp' a => ?_⟩
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, reassoc_of% hα x, hψ, fibPt, pullback.lift_fst, f₂, Over.comp_left,
        Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, fibPt, fibPt, pullback.lift_snd, pullback.lift_snd]
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    rw [← e₃, hψ, hψ, ← f₃, Category.assoc, hlin, Category.assoc]
  · obtain ⟨v, rfl⟩ := ρ₁.surjective v
    obtain ⟨x, rfl⟩ := exists_lift_pt Z.ψ z v
    exact ⟨ρ x, hψ x⟩
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    rw [MonoidHom.mem_ker, hψ, map_eq_one_iff _ ρ₁.injective, Z.ker k z x, hC x _ (e₂ x)]
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    obtain ⟨x', rfl⟩ := ρ.surjective x'
    rw [hψ, hψ]
    refine (f₄ _ _ _ _).1 ?_
    replace h := (e₄ _ _ _ _).2 h
    let P := polOf Z.o₁.t Z.o₁.proper Z.o₁.ample Z.o₁.ktriv (ObjDim.smoothOfRelativeDimension Z.o₁)
    let P' := polOf Z.o₂.t Z.o₂.proper Z.o₂.ample Z.o₂.ktriv (ObjDim.smoothOfRelativeDimension Z.o₂)
    have hn₀ : 0 < n := Nat.pos_of_ne_zero (by
      rintro rfl
      exact hp.one_lt.ne' ((Nat.coprime_zero_left p).1 hn))
    have : Unique (Over.mk z).left := inferInstanceAs (Unique (PrimeSpectrum k))
    obtain ⟨t₁, t₂⟩ := pow_eq_one_of_weilIs hL.kerPow P hn₀ h
    obtain ⟨c', hc', -⟩ := (hL.weil _ P' n _).1 (x ≫ Z.ψ) (x' ≫ Z.ψ)
      (by rw [← MonObj.pow_comp, t₁, MonObj.one_comp]) (by rw [← MonObj.pow_comp, t₂, MonObj.one_comp])
    have e := (weilIs_along_hom hL.globalFns _ _ _ Z.ψ _ _ (p ^ 2) n _ x x' _ _ P.isAb P'.isAb P.isLB P'.isLB hom hiso
      hc').2 h
    rw [unitOn_pow]
    exact e ▸ hc'
  · rw [← e₅, ← e₆, hψ, hψ, Category.assoc, Category.assoc, (hlev p' hp' a).1, (hlev p' hp' a).2, f₅, f₆]
    exact ⟨rfl, rfl⟩

end GlobalTheory.HkFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelChangeExtendsBaseModel
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelChangeLiftKeepingEtaA
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelChangeLiftKeepingEtaA
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem GlobalTheory.LiftAut.exists_lift_keeping_etaA :
    Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ∀ (l₀ l₁ : Level H) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (r₀ : (Xo l₀).X ≅ (Xo l₀).X) (ν₀ : SABMap (Xo l₀).univ.t (Xo l₀).univ.t r₀.hom) (g : D.La →ₗ[𝓞 E] D.La), l₀.A = 1 → l₁.M = l₀.M → l₁.Mb = l₀.Mb → l₁.A.Coprime l₁.M → LevComp (Xo l₁).univ (Xo l₀).univ r ν → (∃ k : KA l₀ →+* KA l₁, IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k ∧ r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k) → r₀.hom ≫ (Xo l₀).s = (Xo l₀).s → (∀ x, ((Xo l₀).univ.eta (g x)).left ≫ ν₀.φ = r₀.hom ≫ ((Xo l₀).univ.eta x).left) → ∃ (r₁ : (Xo l₁).X ≅ (Xo l₁).X) (ν₁ : SABMap (Xo l₁).univ.t (Xo l₁).univ.t r₁.hom), r₁.hom ≫ (Xo l₁).s = (Xo l₁).s ∧ r₁.hom ≫ r = r ≫ r₀.hom ∧ ν₁.φ ≫ ν.φ = ν.φ ≫ ν₀.φ ∧ ∀ x, ((Xo l₁).univ.etaA x).left ≫ ν₁.φ = r₁.hom ≫ ((Xo l₁).univ.etaA x).left :=
  GlobalTheory.LiftAut.lift_of_unique_of_similitude GlobalTheory.LevUniq.map_to_univ_unique GlobalTheory.exists_sim_of_aut_mod
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelChangeLiftKeepingEtaAStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_change_lift_keeping_etaA : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ∀ (l₀ l₁ : Level H) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (r₀ : (Xo l₀).X ≅ (Xo l₀).X) (ν₀ : SABMap (Xo l₀).univ.t (Xo l₀).univ.t r₀.hom) (g : D.La →ₗ[𝓞 E] D.La), l₀.A = 1 → l₁.M = l₀.M → l₁.Mb = l₀.Mb → l₁.A.Coprime l₁.M → LevComp (Xo l₁).univ (Xo l₀).univ r ν → (∃ k : KA l₀ →+* KA l₁, IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k ∧ r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k) → r₀.hom ≫ (Xo l₀).s = (Xo l₀).s → (∀ x, ((Xo l₀).univ.eta (g x)).left ≫ ν₀.φ = r₀.hom ≫ ((Xo l₀).univ.eta x).left) → ∃ (r₁ : (Xo l₁).X ≅ (Xo l₁).X) (ν₁ : SABMap (Xo l₁).univ.t (Xo l₁).univ.t r₁.hom), r₁.hom ≫ (Xo l₁).s = (Xo l₁).s ∧ r₁.hom ≫ r = r ≫ r₀.hom ∧ ν₁.φ ≫ ν.φ = ν.φ ≫ ν₀.φ ∧ ∀ x, ((Xo l₁).univ.etaA x).left ≫ ν₁.φ = r₁.hom ≫ ((Xo l₁).univ.etaA x).left := by
  first | exact @GlobalTheory.LiftAut.exists_lift_keeping_etaA | exact GlobalTheory.LiftAut.exists_lift_keeping_etaA | (intros; apply GlobalTheory.LiftAut.exists_lift_keeping_etaA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelChangeExtendsBaseModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {U U' : Scheme.{0}} {F F' : Type} [Field F] [Field F'] {c : U ⟶ Sp F} {c' : U' ⟶ Sp F'} {t₀ : SAB H U}
  {t₀' : SAB H U'} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* F} {β' : O' →+* F'}

theorem Cpt.basic_of_isDedFrac (C : Cpt c t₀ β) (hβ : IsDedFrac β) :
    IsLocallyNoetherian C.X ∧ IsReduced C.X ∧ IsProper C.s ∧ IsPreimmersion C.j ∧ Flat C.j ∧ IsDominant C.j ∧
      QuasiCompact C.j ∧ C.j ≫ C.s = c ≫ spMap β := by
  obtain ⟨⟨_, _⟩, -, hfr⟩ := hβ
  letI := β.toAlgebra
  obtain ⟨h1, -, -, h2, h3, h4, h5⟩ :=
    GlobalTheory.genericPart_dense_proOpen O F C.X U C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  refine ⟨h1, ?_, ?_, h2, h3, h4, h5, ?_⟩
  · have : ∀ x : C.X, _root_.IsReduced (C.X.presheaf.stalk x) := fun x => by
      have := (C.normal x).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  · obtain ⟨N, i, hi, e⟩ := C.proj
    have := isProper_str O N
    rw [← e]; infer_instance
  · rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]

theorem Cpt.exists_extension_of_above (C : Cpt c t₀ β) (C' : Cpt c' t₀' β') (hβ : IsDedFrac β) (hβ' : IsDedFrac β')
    {b : O →+* O'} {r : U' ⟶ U} {ν : SABMap t₀' t₀ r} (A : C'.Above C b r ν) (hb : IsFinite (spMap b))
    (hr : Surjective r) {R : Type} [CommRing R] {Z : Scheme.{0}} (sZ : Z ⟶ Sp R) (b' : R →+* O') (q : C'.X ⟶ Z)
    (hq : q ≫ sZ = C'.s ≫ spMap b') (hfin : IsFinite (pullback.lift q C'.s hq))
    (e : U ⟶ U) (e' : U' ⟶ U') (he : e ≫ c = c) (he' : e' ≫ c' = c') (hee : e' ≫ r = r ≫ e)
    (hqe : e' ≫ C'.j ≫ q = C'.j ≫ q) :
    ∃ ρ : C.X ⟶ C.X, ρ ≫ C.s = C.s ∧ C.j ≫ ρ = e ≫ C.j := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := C.basic_of_isDedFrac hβ
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8⟩ := C'.basic_of_isDedFrac hβ'
  obtain ⟨ρ', ⟨h1, h2⟩, -⟩ := GlobalTheory.existsUnique_lift_of_densePart C'.X U' _ C'.X C'.j C'.normal m4 m5 m6 m7
    (pullback.lift q C'.s hq) (pullback.lift q C'.s hq) (e' ≫ C'.j) inferInstance (by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, hqe]
      · simp only [Category.assoc, pullback.lift_snd, m8, reassoc_of% he'])
  have h3 : ρ' ≫ C'.s = C'.s := by
    have := congrArg (· ≫ pullback.snd sZ (spMap b')) h2
    simpa only [Category.assoc, pullback.lift_snd] using this
  have hπf : IsFinite A.π := by
    have h4 := A.fin
    have h5 : IsFinite (pullback.fst C.s (spMap b)) := inferInstance
    have h6 : A.π = pullback.lift A.π C'.s A.π_over ≫ pullback.fst C.s (spMap b) := (pullback.lift_fst _ _ _).symm
    rw [h6]; infer_instance
  have hπd : IsDominant A.π := by
    have : IsDominant (C'.j ≫ A.π) := by rw [A.j_comm]; infer_instance
    exact IsDominant.of_comp C'.j A.π
  have hπs : Surjective A.π := surjective_of_isDominant_of_isClosed_range A.π A.π.isClosedMap.isClosed_range
  obtain ⟨ρ, h7, h8⟩ := GlobalTheory.exists_desc_of_isFinite_of_densePart (Sp O) C'.X C.X U' U C.X A.π C'.j C.j r C.s C.s
    (ρ' ≫ A.π) (e ≫ C.j) C.normal m2 hπf hπs hr m6 m7 n4 n5 n6 n7 inferInstance inferInstance A.j_comm
    (by rw [reassoc_of% h1, A.j_comm, reassoc_of% hee])
    (by rw [Category.assoc, A.π_over, reassoc_of% h3])
    (by rw [Category.assoc, n8, reassoc_of% he])
  refine ⟨ρ, ext_of_isDominant C.j ?_, h7⟩
  rw [reassoc_of% h7, n8, reassoc_of% he]

end

theorem extendsAut_of_above : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), 1 ≤ D.p + D.q → ∀ (l₀ l₁ : Level H) (h : l₁.A = N) (O₀ O₁ : Type) [CommRing O₀] [CommRing O₁] (β₀ : O₀ →+* KA l₀) (β₁ : O₁ →+* KA l₁) (C : Cpt (Xo l₀).s (Xo l₀).univ.t β₀) (C₁ : Cpt (Xo l₁).s (Xo l₁).univ.t β₁) (b : O₀ →+* O₁) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (_ : C₁.Above C b r ν) (b' : RZ H n N →+* O₁) (q : C₁.X ⟶ T.Z) (hq : q ≫ T.s = C₁.s ≫ spMap b'), IsDedFrac β₀ → IsDedFrac β₁ → Algebra.FiniteType ℤ O₀ → IsFinite (spMap b) → IsFinite (pullback.lift q C₁.s hq) → C₁.j ≫ q = T.a l₁ h → l₀.A = 1 → l₁.M = l₀.M → l₁.Mb = l₀.Mb → N.Coprime l₁.M → LevComp (Xo l₁).univ (Xo l₀).univ r ν → Surjective r → (∃ k : KA l₀ →+* KA l₁, IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k ∧ r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k ∧ β₁.comp b = k.comp β₀) → ∀ (r₀ : (Xo l₀).X ≅ (Xo l₀).X) (ν₀ : SABMap (Xo l₀).univ.t (Xo l₀).univ.t r₀.hom) (g : D.La →ₗ[𝓞 E] D.La), r₀.hom ≫ (Xo l₀).s = (Xo l₀).s → (∀ x, ((Xo l₀).univ.eta (g x)).left ≫ ν₀.φ = r₀.hom ≫ ((Xo l₀).univ.eta x).left) → C.ExtendsAut r₀ ν₀ := by
  intro hext L1 L2 L3 E _ _ _ H D Xo n N T hpq l₀ l₁ h O₀ O₁ _ _ β₀ β₁ C C₁ b r ν A b' q hq hβ₀ hβ₁ hft hb hfin hjq
    hA hM hMb hcop hlev hr hk r₀ ν₀ g hr₀ hη
  obtain ⟨k, hk1, hk2, -⟩ := hk
  obtain ⟨r₁, ν₁, h1, h2, -, h4⟩ := GlobalTheory.T.exists_level_change_lift_keeping_etaA L1 L2 L3 E H D Xo hpq l₀ l₁ r ν r₀ ν₀ g hA hM hMb (h ▸ hcop) hlev
    ⟨k, hk1, hk2⟩ hr₀ hη
  have h5 : r₁.hom ≫ T.a l₁ h = T.a l₁ h := (T.compat l₁ l₁ h h r₁.hom ν₁ (RingHom.id _) (fun _ => rfl) (by
    rw [h1]
    exact (Category.comp_id _).symm.trans (congrArg _ (Spec.map_id (CommRingCat.of (KA l₁))).symm)) h4).1
  obtain ⟨ρ, hρ1, hρ2⟩ := C.exists_extension_of_above C₁ hβ₀ hβ₁ A hb hr T.s b' q hq hfin r₀.hom r₁.hom hr₀ h1 h2
    (by rw [hjq, h5])
  obtain ⟨ρ', hρ1', hρ2'⟩ := C.exists_extension_of_above C₁ hβ₀ hβ₁ A hb hr T.s b' q hq hfin r₀.inv r₁.inv
    (by rw [Iso.inv_comp_eq, hr₀]) (by rw [Iso.inv_comp_eq, h1])
    (by rw [Iso.inv_comp_eq, reassoc_of% h2, Iso.hom_inv_id, Category.comp_id])
    (by rw [hjq, Iso.inv_comp_eq, h5])
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := C.basic_of_isDedFrac hβ₀
  let σ : C.X ≅ C.X :=
    { hom := ρ
      inv := ρ'
      hom_inv_id := ext_of_isDominant_of_isSeparated C.s (by rw [Category.assoc, hρ1', hρ1, Category.id_comp]) C.j
        (by rw [reassoc_of% hρ2, hρ2', Iso.hom_inv_id_assoc, Category.comp_id])
      inv_hom_id := ext_of_isDominant_of_isSeparated C.s (by rw [Category.assoc, hρ1, hρ1', Category.id_comp]) C.j
        (by rw [reassoc_of% hρ2', hρ2, Iso.inv_hom_id_assoc, Category.comp_id]) }
  obtain ⟨mu, hmu⟩ := exists_sabMap_extending hext E H _ _ _ _ _ β₀ _ _ _ _ _ β₀ C C r₀.hom ν₀ ρ hβ₀ hft
    (Xo l₀).univ.proper hρ2
  exact ⟨σ, mu, hρ1, hρ2, hmu⟩

end GlobalTheory.Models
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelChangeExtendsBaseModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelChange_extends_base_model : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), 1 ≤ D.p + D.q → ∀ (l₀ l₁ : Level H) (h : l₁.A = N) (O₀ O₁ : Type) [CommRing O₀] [CommRing O₁] (β₀ : O₀ →+* KA l₀) (β₁ : O₁ →+* KA l₁) (C : Cpt (Xo l₀).s (Xo l₀).univ.t β₀) (C₁ : Cpt (Xo l₁).s (Xo l₁).univ.t β₁) (b : O₀ →+* O₁) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (_ : C₁.Above C b r ν) (b' : RZ H n N →+* O₁) (q : C₁.X ⟶ T.Z) (hq : q ≫ T.s = C₁.s ≫ spMap b'), IsDedFrac β₀ → IsDedFrac β₁ → Algebra.FiniteType ℤ O₀ → IsFinite (spMap b) → IsFinite (pullback.lift q C₁.s hq) → C₁.j ≫ q = T.a l₁ h → l₀.A = 1 → l₁.M = l₀.M → l₁.Mb = l₀.Mb → N.Coprime l₁.M → LevComp (Xo l₁).univ (Xo l₀).univ r ν → Surjective r → (∃ k : KA l₀ →+* KA l₁, IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k ∧ r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k ∧ β₁.comp b = k.comp β₀) → ∀ (r₀ : (Xo l₀).X ≅ (Xo l₀).X) (ν₀ : SABMap (Xo l₀).univ.t (Xo l₀).univ.t r₀.hom) (g : D.La →ₗ[𝓞 E] D.La), r₀.hom ≫ (Xo l₀).s = (Xo l₀).s → (∀ x, ((Xo l₀).univ.eta (g x)).left ≫ ν₀.φ = r₀.hom ≫ ((Xo l₀).univ.eta x).left) → C.ExtendsAut r₀ ν₀ := by
  first | exact @GlobalTheory.Models.extendsAut_of_above | exact GlobalTheory.Models.extendsAut_of_above | (intros; apply GlobalTheory.Models.extendsAut_of_above <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsInversionEndomorphismsThetaLevelFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsInversionEndomorphismsThetaLevelFamily
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.EndBuild

theorem pow_val_natCast {A : Type} [Monoid A] {k : ℕ} (y : A) (hy : y ^ k = 1) (m : ℕ) :
    y ^ ((m : ZMod k)).val = y ^ m := by
  rw [ZMod.val_natCast, ← pow_eq_pow_mod m hy]

def labMap {g : ℕ} {J : Type} (k : ℕ) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (i : Option J) (h : Ix g k) : Ix g k :=
  i.elim (-h) (fun j i' => ((∑ c, (Mat j i' c : ZMod k).val * (h c).val : ℕ) : ZMod k))

theorem linComb_eq_prod {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {r : ℕ}
    (y : Fin r → (T ⟶ A)) (a : Fin r → ℕ) : Out.linComb y a = ∏ i, y i ^ a i := by
  rw [Out.linComb, List.prod_ofFn]

theorem lab_comp {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} [NeZero k] {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
    (t : TObj g k J b s) {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ} (ht : t.Shape Mat κ)
    (i : Option J) (h : Ix g k) :
    t.lab h ≫ (i.elim (𝟙 t.A)⁻¹ t.act : t.A ⟶ t.A) = t.lab (labMap k Mat i h) := by
  haveI := t.ab.comm
  cases i with
  | none =>
    simp only [Option.elim, labMap]
    rw [GrpObj.comp_inv, Category.comp_id]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [TObj.lab, TObj.lab, linComb_eq_prod, linComb_eq_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun c _ => ?_
    rw [← pow_add, ← pow_val_natCast _ (t.torsion c)]
    simp
  | some j =>
    simp only [Option.elim, labMap]
    haveI := t.hom j
    have e : t.lab h ≫ t.act j = ∏ c, (t.pt c ≫ t.act j) ^ (h c).val := by
      rw [TObj.lab, linComb_eq_prod]
      have := map_prod (IsMonHom.monoidHom (t.act j) (Out.baseOver S)) (fun c => t.pt c ^ (h c).val) Finset.univ
      simp only [map_pow] at this
      exact this
    rw [e, TObj.lab, linComb_eq_prod]
    simp only [(ht j).1, TObj.lab, linComb_eq_prod, ← Finset.prod_pow, ← pow_mul]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [pow_val_natCast _ (t.torsion c), Finset.prod_pow_eq_pow_sum]

theorem graphIdeal_le {R σ₁ σ₂ : Type} [CommRing R] {Y Y' X₁ X₂ X₁' X₂' : Scheme.{0}} (s : Y ⟶ Sp R) (s' : Y' ⟶ Sp R)
    (M₁ : LB X₁) (th₁ : σ₁ → M₁.Sec) (a₁ : Y ⟶ X₁) (M₂ : LB X₂) (th₂ : σ₂ → M₂.Sec) (a₂ : Y ⟶ X₂)
    (M₁' : LB X₁') (th₁' : σ₁ → M₁'.Sec) (a₁' : Y' ⟶ X₁') (M₂' : LB X₂') (th₂' : σ₂ → M₂'.Sec) (a₂' : Y' ⟶ X₂')
    (e : Y ⟶ Y') (he : e ≫ s' = s)
    (h₁ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (w : σ₁ → T),
      SecCoord M₁ th₁ (y ≫ a₁) w → SecCoord M₁' th₁' (y ≫ e ≫ a₁') w)
    (h₂ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (w : σ₂ → T),
      SecCoord M₂ th₂ (y ≫ a₂) w → SecCoord M₂' th₂' (y ≫ e ≫ a₂') w) :
    graphIdeal s' M₁' th₁' a₁' M₂' th₂' a₂' ≤ graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂ := by
  unfold graphIdeal
  refine le_iInf fun T => le_iInf fun _ => le_iInf fun β => le_iInf fun y => le_iInf fun v₁ => le_iInf fun v₂ =>
    le_iInf fun hy => ?_
  refine iInf_le_of_le T <| iInf_le_of_le inferInstance <| iInf_le_of_le β <| iInf_le_of_le (y ≫ e) <|
    iInf_le_of_le v₁ <| iInf_le_of_le v₂ <| iInf_le_of_le ⟨?_, ?_, ?_⟩ le_rfl
  · rw [Category.assoc, he, hy.1]
  · rw [Category.assoc]; exact h₁ _ _ _ hy.2.1
  · rw [Category.assoc]; exact h₂ _ _ _ hy.2.2

theorem graphIdeal_eq {R σ₁ σ₂ : Type} [CommRing R] {Y Y' X₁ X₂ X₁' X₂' : Scheme.{0}} (s : Y ⟶ Sp R) (s' : Y' ⟶ Sp R)
    (M₁ : LB X₁) (th₁ : σ₁ → M₁.Sec) (a₁ : Y ⟶ X₁) (M₂ : LB X₂) (th₂ : σ₂ → M₂.Sec) (a₂ : Y ⟶ X₂)
    (M₁' : LB X₁') (th₁' : σ₁ → M₁'.Sec) (a₁' : Y' ⟶ X₁') (M₂' : LB X₂') (th₂' : σ₂ → M₂'.Sec) (a₂' : Y' ⟶ X₂')
    (e : Y ⟶ Y') [IsIso e] (he : e ≫ s' = s)
    (h₁ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (w : σ₁ → T),
      SecCoord M₁ th₁ (y ≫ a₁) w ↔ SecCoord M₁' th₁' (y ≫ e ≫ a₁') w)
    (h₂ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (w : σ₂ → T),
      SecCoord M₂ th₂ (y ≫ a₂) w ↔ SecCoord M₂' th₂' (y ≫ e ≫ a₂') w) :
    graphIdeal s' M₁' th₁' a₁' M₂' th₂' a₂' = graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂ := by
  refine le_antisymm (graphIdeal_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ e he (fun T _ y w => (h₁ T y w).1)
    (fun T _ y w => (h₂ T y w).1)) (graphIdeal_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ (inv e) (by rw [← he, IsIso.inv_hom_id_assoc])
    (fun T _ y w hw => ?_) (fun T _ y w hw => ?_))
  · rw [← Category.assoc, h₁]; simpa using hw
  · rw [← Category.assoc, h₂]; simpa using hw

theorem cut_fibre {o R K : Type} [CommRing o] [CommRing R] [Field K] {g N m : ℕ} [NeZero (N ^ 2)] {J : Type}
    {b : TBase o (N ^ 2)} {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ} (i : Option J) (Q : Polynomial ℚ) (d : ℕ)
    {s : Sp K ⟶ Sp o} (t : TObj g (N ^ 2) J b s) (ht : t.Shape Mat κ)
    (σ : Ix g (N ^ 2) → LB.Sec (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 _))))
    (hcut : ∀ (p q : Ix g (N ^ 2) → Ix g (N ^ 2) → K) (f : t.A ⟶ t.A), f = i.elim (𝟙 t.A)⁻¹ t.act →
      (∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ N)).left (p h) ∧
        SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) ((t.lab h ≫ f) ^ N)).left (q h)) →
      CutBy (graphIdeal (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _) _ σ
        (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ f)).left) Q d (fun h i => p h i.1 * q h i.2))
    (Z : Over (Sp R)) (M : LB Z.left) (hM : M.IsLB) (th : Ix g (N ^ 2) → M.Sec)
    (sc : Ix g (N ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g (N ^ 2) → Ix g (N ^ 2) → R)
    (hp : ∀ h, SecCoord M th (sc h).left (p h)) (x : R →+* K) (φ : t.A.left ⟶ Z.left)
    (hφ : IsPullback φ t.A.hom Z.hom (spMap x))
    (hσ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t.A).left) (w : Ix g (N ^ 2) → T),
      SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t.A).left ≫ φ) w)
    (hl : ∀ h, (t.lab h ^ N).left ≫ φ = spMap x ≫ (sc h).left) :
    CutBy (graphIdeal (pullback.snd Z.hom (spMap x)) M th (pullback.fst _ _) M th
      (hφ.isoPullback.inv ≫ (i.elim (𝟙 t.A)⁻¹ t.act : t.A ⟶ t.A).left ≫ φ)) Q d
      (fun h c => x (p h c.1 * p (labMap (N ^ 2) Mat i h) c.2)) := by
  have hpt : ∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ N)).left (fun a => x (p h a)) := by
    intro h
    refine (hσ K _ _).2 ?_
    have e : (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ N)).left ≫ (snd (Over.mk (𝟙 (Sp K))) t.A).left ≫ φ =
        spMap x ≫ (sc h).left := by
      rw [← hl h, ← Category.assoc, ← Over.comp_left, lift_snd]
    have := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ M _ th R (sc h).left (p h) hM (hp h)).1 K x
    exact e ▸ this
  have H := hcut (fun h a => x (p h a)) (fun h a => x (p (labMap (N ^ 2) Mat i h) a)) _ rfl
    (fun h => ⟨hpt h, by rw [lab_comp t ht]; exact hpt _⟩)
  haveI : IsIso (snd (Over.mk (𝟙 (Sp K))) t.A).left :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 (Sp K)) t.A.hom))
  have hs : (snd (Over.mk (𝟙 (Sp K))) t.A).left ≫ t.A.hom = (fst (Over.mk (𝟙 (Sp K))) t.A).left :=
    (pullback.condition (f := 𝟙 (Sp K)) (g := t.A.hom)).symm.trans (Category.comp_id _)
  rw [graphIdeal_eq (fst (Over.mk (𝟙 (Sp K))) t.A).left (pullback.snd Z.hom (spMap x)) _ σ (𝟙 _) _ σ
    (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ (i.elim (𝟙 t.A)⁻¹ t.act : t.A ⟶ t.A))).left M th _ M th _
    ((snd (Over.mk (𝟙 (Sp K))) t.A).left ≫ hφ.isoPullback.hom)]
  · simpa only [map_mul] using H
  · rw [Category.assoc, IsPullback.isoPullback_hom_snd]; exact hs
  · intro T _ y w
    rw [hσ, Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst, Category.id_comp]
  · intro T _ y w
    rw [hσ, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc _ _ φ,
      ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc]

theorem exists_endomorphisms : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (I : Ideal (MvPolynomial (Ix g ((n ^ j) ^ 2)) R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R), VeryDense (objPrimes b Mat κ β v) → (ProjRep I Z.hom M th ∧ SmoothOfRelativeDimension g Z.hom ∧ GeometricallyConnected Z.hom ∧ (∀ h, SecCoord M th (sc h).left (p h))) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ φ : t'.A.left ⟶ Z.left, (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left)) → ∃ F : Option J → (Z ⟶ Z), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), t'.Shape Mat κ → (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ i : Option J, φ ≫ (F i).left = (i.elim (𝟙 t'.A)⁻¹ t'.act : t'.A ⟶ t'.A).left ≫ φ) := by
  intro hL hL2 g J _ Mat κ n hn hodd
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.graph_inversion_endomorphism_cut_bounded_degree hL hL2 g J Mat κ n hn hodd
  refine ⟨j₀, fun j hj o _ b R _ _ _ β v Z I M th sc p hvd hPF hfib => ?_⟩
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  obtain ⟨hrep, hsm, -, hp⟩ := hPF
  have hprop := (GlobalTheory.T.isProj_proper_relAmple_of_projectiveCoordinateRep R _ I Z M th hrep).2.1
  have hsm' : Smooth Z.hom := SmoothOfRelativeDimension.smooth g _
  have key : ∀ i : Option J, ∃ F : Z ⟶ Z, ∀ (K : Type) [Field K] (x : R →+* K) (f : pullback Z.hom (spMap x) ⟶ Z.left),
      (∃ (_ : IsAlgClosed K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left)
        (hφ : IsPullback φ t'.A.hom Z.hom (spMap x)), t'.Shape Mat κ ∧
        (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧
        (∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) ∧
        f = hφ.isoPullback.inv ≫ (i.elim (𝟙 t'.A)⁻¹ t'.act : t'.A ⟶ t'.A).left ≫ φ) →
      f = pullback.fst _ _ ≫ F.left := by
    intro i
    obtain ⟨Q, d, hQ⟩ := hj₀ j hj o b i
    refine GlobalTheory.T.exists_family_morphism_from_veryDense_graphs R _ _ (Ix g ((n ^ j) ^ 2)) Z Z I I M M th th p (fun h => p (labMap _ Mat i h)) Q d _
      hrep hrep hprop hprop hsm' ?_ ?_
    · rintro K _ x f ⟨_, t', φ, hφ, ht, ⟨σ, hE, hσ⟩, hl, rfl⟩
      refine ⟨?_, cut_fibre (m := n ^ 2) i Q d t' ht σ ?_ Z M hrep.1 th sc p hp x φ hφ hσ hl⟩
      · rw [Category.assoc, Category.assoc, hφ.w, ← Category.assoc (Option.elim _ _ _ : t'.A ⟶ t'.A).left, Over.w,
          ← Category.assoc, IsPullback.isoPullback_inv_snd]
      · have e : spMap x ≫ spMap β = spMap (x.comp β) := by rw [← Spec.map_comp]; rfl
        clear hσ hl hφ φ
        generalize spMap x ≫ spMap β = s at e t' ht σ hE
        subst e
        exact fun p' q' f hf h => hQ K (x.comp β) t' σ p' q' f ht hf hE h
    · intro q r hq hr
      obtain ⟨P, ⟨K, _, _, x, t', hx, ht, hth⟩, hP⟩ := hvd q r hq hr
      obtain ⟨φ, hφ, hσ, -, hl⟩ := hfib K x t' ht hth
      exact ⟨P, ⟨K, _, x, _, hx, inferInstance, t', φ, hφ, ht, hσ, hl, rfl⟩, hP⟩
  choose F hF using key
  refine ⟨F, fun K _ _ x t' φ ht hfb i => ?_⟩
  obtain ⟨hφ, hσ, -, hl⟩ := hfb
  have := hF i K x _ ⟨inferInstance, t', φ, hφ, ht, hσ, hl, rfl⟩
  rw [Iso.inv_comp_eq, IsPullback.isoPullback_hom_fst_assoc] at this
  exact this.symm

end GlobalTheory.ZM.EndBuild
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsInversionEndomorphismsThetaLevelFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inversion_endomorphisms_thetaLevelFamily : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (I : Ideal (MvPolynomial (Ix g ((n ^ j) ^ 2)) R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R), VeryDense (objPrimes b Mat κ β v) → (ProjRep I Z.hom M th ∧ SmoothOfRelativeDimension g Z.hom ∧ GeometricallyConnected Z.hom ∧ (∀ h, SecCoord M th (sc h).left (p h))) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ φ : t'.A.left ⟶ Z.left, (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left)) → ∃ F : Option J → (Z ⟶ Z), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), t'.Shape Mat κ → (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ i : Option J, φ ≫ (F i).left = (i.elim (𝟙 t'.A)⁻¹ t'.act : t'.A ⟶ t'.A).left ≫ φ) := by
  first | exact @GlobalTheory.ZM.EndBuild.exists_endomorphisms | exact GlobalTheory.ZM.EndBuild.exists_endomorphisms | (intros; apply GlobalTheory.ZM.EndBuild.exists_endomorphisms <;> assumption)
end
end
