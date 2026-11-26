module

public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmConnIdempotentSplits
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOpenNonzeroLocusOfUniversallyClosed
public import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionTranslateZerosLt
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsClosedEmbeddingOfAffine

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperOfPowerSeriesArcsOverAlgClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperOfPowerSeriesArcsOverAlgClosed
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.ArcProper

theorem exists_isOpenImmersion_isProper {R : Type} [CommRing R] {U : Scheme.{0}} [IsAffine U]
    (s : U ⟶ Sp R) [LocallyOfFiniteType s] :
    ∃ (P : Scheme.{0}) (t : P ⟶ Sp R) (j : U ⟶ P), IsProper t ∧ IsOpenImmersion j ∧ j ≫ t = s := by
  obtain ⟨N, i, _, _, e⟩ := (isAmpleLB_of_isAffine (LB.isLB_triv U)).isQProjOver s
  have := isProper_str R N
  exact ⟨i.image, i.imageι ≫ PSpace.str R N, i.toImage, inferInstance, inferInstance,
    by rw [i.toImage_imageι_assoc, e]⟩

theorem exists_isProper_factor {S U : Scheme.{0}} {J : Type} (P : J → Scheme.{0})
    (t : ∀ i, P i ⟶ S) (ht : ∀ i, IsProper (t i)) (u : U ⟶ S) (φ : ∀ i, U ⟶ P i)
    (h : ∀ i, φ i ≫ t i = u) (T : Finset J) :
    ∃ (Q : Scheme.{0}) (q : Q ⟶ S) (ψ : U ⟶ Q), IsProper q ∧ ψ ≫ q = u ∧
      ∀ i ∈ T, ∃ p : Q ⟶ P i, p ≫ t i = q ∧ ψ ≫ p = φ i := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨S, 𝟙 S, u, inferInstance, Category.comp_id _, by simp⟩
  | insert a T _ ih =>
    obtain ⟨Q, q, ψ, _, e, H⟩ := ih
    refine ⟨pullback q (t a), pullback.fst _ _ ≫ q, pullback.lift ψ (φ a) (e.trans (h a).symm),
      inferInstance, by rw [pullback.lift_fst_assoc, e], fun i hi ↦ ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact ⟨pullback.snd _ _, pullback.condition.symm, pullback.lift_snd _ _ _⟩
    · obtain ⟨p, hp, hp'⟩ := H i hi
      exact ⟨pullback.fst _ _ ≫ p, by rw [Category.assoc, hp], by rw [pullback.lift_fst_assoc, hp']⟩

theorem exists_extension_of_cover {S Z X W : Scheme.{0}} [IsIntegral Z] [Nonempty W] (z : Z ⟶ S)
    (s : X ⟶ S) [IsSeparated s] (j : W ⟶ Z) [IsOpenImmersion j] (u : W ⟶ X) {J : Type}
    (V : J → Z.Opens) (hV : TopologicalSpace.IsOpenCover V) (m : ∀ i, (V i).toScheme ⟶ X)
    (hm : ∀ i, m i ≫ s = (V i).ι ≫ z)
    (hu : ∀ (i : J) (T : Scheme.{0}) (a : T ⟶ W) (b : T ⟶ V i), a ≫ j = b ≫ (V i).ι →
      b ≫ m i = a ≫ u) :
    ∃ g : Z ⟶ X, g ≫ s = z ∧ Set.range u ⊆ Set.range g := by
  let 𝒰 := Z.openCoverOfIsOpenCover V hV
  have hd : Dense (Set.range j) := j.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)
  have hc : ∀ i i', pullback.fst (V i).ι (V i').ι ≫ m i = pullback.snd (V i).ι (V i').ι ≫ m i' := by
    intro i i'
    let r := pullback.fst (V i).ι (V i').ι ≫ (V i).ι
    have : IsReduced (pullback (V i).ι (V i').ι) := isReduced_of_isOpenImmersion r
    have : IsDominant (pullback.fst r j) := ⟨by
      rw [DenseRange, Scheme.Pullback.range_fst]
      exact hd.preimage r.isOpenEmbedding.isOpenMap⟩
    refine ext_of_isDominant_of_isSeparated s ?_ (pullback.fst r j) ?_
    · rw [Category.assoc, Category.assoc, hm, hm, pullback.condition_assoc]
    · rw [← Category.assoc, ← Category.assoc, hu i _ (pullback.snd r j), hu i' _ (pullback.snd r j)]
      · rw [Category.assoc, ← pullback.condition, ← pullback.condition]
      · rw [Category.assoc, ← pullback.condition]
  have hg : ∀ i, (V i).ι ≫ 𝒰.glueMorphisms m hc = m i := fun i ↦ 𝒰.ι_glueMorphisms m hc i
  refine ⟨𝒰.glueMorphisms m hc, 𝒰.hom_ext _ _ fun i ↦ ?_, ?_⟩
  · exact ((reassoc_of% hg i) s).trans (hm i)
  · rintro _ ⟨w, rfl⟩
    obtain ⟨i, hi⟩ := hV.exists_mem (j w)
    have : w ∈ Set.range (pullback.fst j (V i).ι) := by
      rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]; exact hi
    obtain ⟨v, rfl⟩ := this
    refine ⟨(pullback.snd j (V i).ι ≫ (V i).ι) v, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Category.assoc, hg,
      hu i _ _ _ pullback.condition]

theorem exists_arc (k : Type) [Field k] [IsAlgClosed k] {Z : Scheme.{0}} [IsIntegral Z]
    (s : Z ⟶ Sp k) [LocallyOfFiniteType s] (z : Z) (hz : IsClosed ({z} : Set Z)) (W : Set Z)
    (hW : IsOpen W) (hW' : W.Nonempty) :
    ∃ c : Sp (PowerSeries k) ⟶ Z, c ≫ s = spMap (algebraMap k (PowerSeries k)) ∧
      c (IsLocalRing.closedPoint (PowerSeries k)) = z ∧
      Set.range (spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))) ≫ c) ⊆ W := by
  obtain ⟨B, g, _, y, rfl⟩ := Z.exists_Spec_apply_eq z
  have : Nonempty (Spec B) := ⟨y⟩
  have : IsIntegral (Spec B) := isIntegral_of_isOpenImmersion g
  have : IsDomain B := (affine_isIntegral_iff B).mp this
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (g ≫ s)
  have hft : ψ.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map ψ) := by rw [hψ]; infer_instance
    exact HasRingHomProperty.Spec_iff.1 this
  let _ : Algebra k B := ψ.hom.toAlgebra
  have : Algebra.FiniteType k B := hft
  have hy : y.asIdeal.IsMaximal := by
    refine (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).1 ?_
    have := hz.preimage g.continuous
    rwa [← Set.image_singleton, Set.preimage_image_eq _ g.isOpenEmbedding.injective] at this
  obtain ⟨w, hw⟩ : (g ⁻¹' W).Nonempty := by
    obtain ⟨_, hw, w, rfl⟩ := (g.isOpenEmbedding.isOpen_range.dense
      (Set.range_nonempty _)).inter_open_nonempty W hW hW'
    exact ⟨w, hw⟩
  obtain ⟨_, ⟨f, rfl⟩, hwf, hf⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hw
      (hW.preimage g.continuous)
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hwf w.asIdeal.zero_mem
  obtain ⟨φ, hφ, hφm⟩ := GlobalTheory.ArcAvoid.exists_algHom_powerSeries_ne_zero k B y.asIdeal hy f hf0
  refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ g, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← hψ, ← Spec.map_comp]
    congr 1
    ext1
    exact φ.comp_algebraMap
  · refine congrArg g (PrimeSpectrum.ext (Ideal.ext fun b ↦ ?_))
    change φ b ∈ IsLocalRing.maximalIdeal (PowerSeries k) ↔ _
    rw [hφm, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff,
      isUnit_iff_ne_zero, not_not]
  · rintro _ ⟨p, rfl⟩
    refine hf ?_
    change algebraMap (PowerSeries k) (FractionRing (PowerSeries k)) (φ f) ∉ p.asIdeal
    intro h
    refine p.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsUnit.mk0 _ ?_))
    simpa using hφ

theorem isProper_of_arcs_extend (k : Type) [Field k] [IsAlgClosed k] {Y : Scheme.{0}} [IsIntegral Y]
    (s : Y ⟶ Sp k) [IsSeparated s] [LocallyOfFiniteType s] [QuasiCompact s]
    (H : ∀ a : Sp (FractionRing (PowerSeries k)) ⟶ Y,
      a ≫ s = spMap (algebraMap k (FractionRing (PowerSeries k))) → ∃ b : Sp (PowerSeries k) ⟶ Y,
        spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))) ≫ b = a) :
    IsProper s := by
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have hA : ∀ y : Y, ∃ A : Y.Opens, IsAffineOpen A ∧ y ∈ A := fun y ↦ by
    obtain ⟨A, h₁, h₂, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
    exact ⟨A, h₁, h₂⟩
  choose A₀ hA₀ hyA using hA
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun y ↦ (A₀ y : Set Y))
    (fun y ↦ (A₀ y).isOpen) (fun y _ ↦ Set.mem_iUnion.2 ⟨y, hyA y⟩)
  let A : T → Y.Opens := fun i ↦ A₀ i
  have hcov : ∀ y : Y, ∃ i : T, y ∈ A i := fun y ↦ by
    obtain ⟨i, hi, h⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ y))
    exact ⟨⟨i, hi⟩, h⟩
  have hP := fun i : T ↦ (have : IsAffine (A i).toScheme := hA₀ i
    exists_isOpenImmersion_isProper ((A i).ι ≫ s))
  choose P t j ht hj hjt using hP
  let U : Y.Opens := Finset.univ.inf A
  have hUA : ∀ i, U ≤ A i := fun i ↦ Finset.inf_le (Finset.mem_univ i)
  have hU : genericPoint Y ∈ U := by
    have : ∀ i, genericPoint Y ∈ A i := fun i ↦
      ((genericPoint_spec Y).mem_open_set_iff (A i).isOpen).2 ⟨i, trivial, hyA i⟩
    refine Finset.inf_induction (p := fun V : Y.Opens ↦ genericPoint Y ∈ V) trivial
      (fun _ h _ h' ↦ ⟨h, h'⟩) fun i _ ↦ this i
  have : Nonempty U.toScheme := ⟨⟨_, hU⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  obtain ⟨Q, q, ψ, _, hψ, hp⟩ := exists_isProper_factor P t ht (U.ι ≫ s)
    (fun i ↦ Y.homOfLE (hUA i) ≫ j i) (fun i ↦ by rw [Category.assoc, hjt, Y.homOfLE_ι_assoc])
    Finset.univ
  choose p hpt hψp using fun i ↦ hp i (Finset.mem_univ i)
  obtain ⟨i₀, -⟩ := hcov (genericPoint Y)
  have : IsImmersion (ψ ≫ p i₀) := by rw [hψp]; infer_instance
  have : IsImmersion ψ := IsImmersion.of_comp ψ (p i₀)
  have : QuasiCompact (ψ ≫ q) := by rw [hψ]; infer_instance
  have : QuasiCompact ψ := QuasiCompact.of_comp ψ q
  have : IsIntegral ψ.image := isIntegral_image ψ
  let z : ψ.image ⟶ Sp k := ψ.imageι ≫ q
  have hz : ψ.toImage ≫ z = U.ι ≫ s := by rw [ψ.toImage_imageι_assoc, hψ]
  let V : T → ψ.image.Opens := fun i ↦ (ψ.imageι ≫ p i) ⁻¹ᵁ (j i).opensRange
  have hinj : Function.Injective
      (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))) := IsFractionRing.injective _ _
  have : IsDominant (spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)))) := by
    refine ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_⟩
    exact ((RingHom.injective_iff_ker_eq_bot _).mp hinj).le.trans bot_le
  have key : ∀ x : ψ.image, IsClosed ({x} : Set ψ.image) → ∃ i, x ∈ V i := by
    intro x hx
    obtain ⟨c, hc, hcx, hcU⟩ := exists_arc k z x hx _ ψ.toImage.isOpenEmbedding.isOpen_range
      (Set.range_nonempty _)
    obtain ⟨l, hl⟩ : ∃ l, l ≫ ψ.toImage = _ := ⟨_, IsOpenImmersion.lift_fac ψ.toImage _ hcU⟩
    have hls : (l ≫ U.ι) ≫ s = spMap (algebraMap k (FractionRing (PowerSeries k))) := by
      rw [Category.assoc, ← hz, reassoc_of% hl, hc, ← Spec.map_comp]
      rfl
    obtain ⟨b, hb⟩ := H (l ≫ U.ι) hls
    have hbs : b ≫ s = spMap (algebraMap k (PowerSeries k)) := by
      refine ext_of_isDominant (spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)))) ?_
      rw [← Category.assoc, hb, hls, ← Spec.map_comp]
      rfl
    obtain ⟨i, hi⟩ := hcov (b (IsLocalRing.closedPoint (PowerSeries k)))
    have hr : Set.range b ⊆ Set.range (A i).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨v, rfl⟩
      exact ((IsLocalRing.specializes_closedPoint v).map b.continuous).mem_open (A i).isOpen hi
    obtain ⟨b', hb'⟩ : ∃ b', b' ≫ (A i).ι = b := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
    have e : b' ≫ j i = c ≫ ψ.imageι ≫ p i := by
      refine ext_of_isDominant_of_isSeparated (t i) ?_
        (spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)))) ?_
      · rw [Category.assoc, hjt, reassoc_of% hb', hbs, Category.assoc, Category.assoc, hpt, hc]
      · rw [← reassoc_of% hl, ψ.toImage_imageι_assoc, hψp, ← Category.assoc, ← Category.assoc]
        congr 1
        rw [← cancel_mono (A i).ι, Category.assoc, hb', hb, Category.assoc, Y.homOfLE_ι]
    refine ⟨i, b' (IsLocalRing.closedPoint (PowerSeries k)), ?_⟩
    have e' : (b' ≫ j i) (IsLocalRing.closedPoint (PowerSeries k)) =
        (c ≫ ψ.imageι ≫ p i) (IsLocalRing.closedPoint (PowerSeries k)) := by rw [e]
    exact e'.trans (congrArg (ψ.imageι ≫ p i) hcx)
  have : CompactSpace ψ.image := QuasiCompact.compactSpace_of_compactSpace z
  have hV : TopologicalSpace.IsOpenCover V := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro x _
    obtain ⟨x', hx', hc⟩ := (isClosed_closure (s := {x})).exists_closed_singleton
      (Set.singleton_nonempty x).closure
    obtain ⟨i, hi⟩ := key x' hc
    exact TopologicalSpace.Opens.mem_iSup.2
      ⟨i, (specializes_iff_mem_closure.2 hx').mem_open (V i).isOpen hi⟩
  have hm : ∀ i, ∃ m : (V i).toScheme ⟶ A i, m ≫ j i = (V i).ι ≫ ψ.imageι ≫ p i := fun i ↦
    ⟨_, IsOpenImmersion.lift_fac (j i) _ (by rintro _ ⟨v, rfl⟩; exact v.2)⟩
  choose m hm using hm
  obtain ⟨g, hg, hgU⟩ := exists_extension_of_cover z s ψ.toImage U.ι V hV
    (fun i ↦ m i ≫ (A i).ι)
    (fun i ↦ by rw [Category.assoc, ← hjt, reassoc_of% hm, hpt])
    (fun i T a b e ↦ by
      rw [← Y.homOfLE_ι (hUA i), ← Category.assoc, ← Category.assoc]
      congr 1
      rw [← cancel_mono (j i), Category.assoc, hm, ← reassoc_of% e, ψ.toImage_imageι_assoc, hψp,
        Category.assoc])
  have : IsProper (g ≫ s) := by rw [hg]; infer_instance
  have : IsProper g := IsProper.of_comp g s
  have : IsDominant g := ⟨(U.isOpen.dense ⟨_, hU⟩).mono (by rwa [Scheme.Opens.range_ι] at hgU)⟩
  have : Surjective g := surjective_of_isDominant_of_isClosed_range g g.isClosedMap.isClosed_range
  have : UniversallyClosed s := .of_comp_surjective g s
  exact {}

theorem isProper_of_arcs : ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Over (Sp k)) [IsIntegral X.left], IsSeparated X.hom → LocallyOfFiniteType X.hom → QuasiCompact X.hom → (∀ a : Sp (FractionRing (PowerSeries k)) ⟶ X.left, a ≫ X.hom = spMap (algebraMap k (FractionRing (PowerSeries k))) → ∃ b : Sp (PowerSeries k) ⟶ X.left, spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))) ≫ b = a) → IsProper X.hom :=
  fun k _ _ X _ _ _ _ H ↦ isProper_of_arcs_extend k X.hom H

end GlobalTheory.ArcProper
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperOfPowerSeriesArcsOverAlgClosedStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_powerSeries_arcs_over_algClosed : ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Over (Sp k)) [IsIntegral X.left], IsSeparated X.hom → LocallyOfFiniteType X.hom → QuasiCompact X.hom → (∀ a : Sp (FractionRing (PowerSeries k)) ⟶ X.left, a ≫ X.hom = spMap (algebraMap k (FractionRing (PowerSeries k))) → ∃ b : Sp (PowerSeries k) ⟶ X.left, spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))) ≫ b = a) → IsProper X.hom := by
  first | exact @GlobalTheory.ArcProper.isProper_of_arcs | exact GlobalTheory.ArcProper.isProper_of_arcs | (intros; apply GlobalTheory.ArcProper.isProper_of_arcs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsValuationSubringIntegralClosureCompleteDVR
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsValuationSubringIntegralClosureCompleteDVR
namespace GlobalTheory.LN

open IsLocalRing

theorem isIntegral_or_isIntegral_inv (O : Type) [CommRing O] [IsDomain O] [CharZero O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    (F : Type) [Field F] [Algebra (FractionRing O) F] [Algebra O F]
    [IsScalarTower O (FractionRing O) F] [Algebra.IsAlgebraic (FractionRing O) F] (x : F) :
    IsIntegral O x ∨ IsIntegral O x⁻¹ := by
  let K := FractionRing O
  let L : IntermediateField K F := IntermediateField.adjoin K {x}
  haveI : FiniteDimensional K L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  haveI : CharZero K := inferInstance
  haveI : Module.Finite O (integralClosure O L) := IsIntegralClosure.finite O K L _
  haveI : IsDiscreteValuationRing (integralClosure O L) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr O K L
  haveI : IsFractionRing (integralClosure O L) L :=
    integralClosure.isFractionRing_of_finite_extension K L
  let y : L := ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩
  let f : L →ₐ[O] F := (IntermediateField.val L).restrictScalars O
  rcases ValuationRing.isInteger_or_isInteger (integralClosure O L) y with ⟨z, hz⟩ | ⟨z, hz⟩
  · left
    have h : IsIntegral O y := hz ▸ z.2
    exact h.map f
  · right
    have h : IsIntegral O y⁻¹ := hz ▸ z.2
    have h' := h.map f
    rwa [map_inv₀] at h'

theorem exists_valuationSubring_isIntegral : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (ϖ : O), GlobalTheory.LN.ArcBase O ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing O) F] [Algebra O F] [IsScalarTower O (FractionRing O) F] [Algebra.IsAlgebraic (FractionRing O) F], ∃ S : ValuationSubring F, ∀ x, x ∈ S ↔ IsIntegral O x := by
  intro O _ _ _ ϖ h F _ _ _ _ _
  rcases h with ⟨hF, -⟩ | ⟨hd, hirr, hc⟩
  · refine ⟨⊤, fun x => ⟨fun _ => ?_, fun _ => trivial⟩⟩
    have ha : IsAlgebraic O x :=
      (IsFractionRing.isAlgebraic_iff O (FractionRing O) F).2 (Algebra.IsAlgebraic.isAlgebraic x)
    letI := hF.toField
    exact ha.isIntegral
  · haveI : IsAdicComplete (maximalIdeal O) O := hirr.maximalIdeal_eq ▸ hc
    exact ⟨⟨(integralClosure O F).toSubring, fun x => isIntegral_or_isIntegral_inv O F x⟩,
      fun x => Iff.rfl⟩

end GlobalTheory.LN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsValuationSubringIntegralClosureCompleteDVRStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuationSubring_integral_closure_completeDVR : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (ϖ : O), GlobalTheory.LN.ArcBase O ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing O) F] [Algebra O F] [IsScalarTower O (FractionRing O) F] [Algebra.IsAlgebraic (FractionRing O) F], ∃ S : ValuationSubring F, ∀ x, x ∈ S ↔ IsIntegral O x := by
  first | exact @GlobalTheory.LN.exists_valuationSubring_isIntegral | exact GlobalTheory.LN.exists_valuationSubring_isIntegral | (intros; apply GlobalTheory.LN.exists_valuationSubring_isIntegral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInvertibleMatrixChangeOfSpanEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInvertibleMatrixChangeOfSpanEq
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.ZH

theorem mul_inv_apply_mem_of_span_le {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    {J : Type} [Fintype J] [DecidableEq J] {b B c : Matrix J J Ω}
    (h : Submodule.span R (Set.range b) ≤ Submodule.span R (Set.range B)) (hc : B * c = 1) (i j : J) :
    (b * c) i j ∈ R := by
  have h1 : ∀ i, ∃ n : J → R, ∑ k, n k • B k = b i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun R).1 (h (Submodule.subset_span ⟨i, rfl⟩))
  choose n hn using h1
  have e : b = (Matrix.of fun i k => (n i k : Ω)) * B := by
    ext i k
    rw [← hn i, Matrix.mul_apply, Finset.sum_apply]
    rfl
  rw [e, Matrix.mul_assoc, hc, Matrix.mul_one]
  exact (n i j).2

theorem exists_mul_eq_one_of_span_le {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    {J : Type} [Fintype J] [DecidableEq J] {b B c : Matrix J J Ω}
    (h : Submodule.span R (Set.range B) ≤ Submodule.span R (Set.range b)) (hc : c * B = 1) :
    ∃ d : Matrix J J Ω, b * d = 1 := by
  have h1 : ∀ i, ∃ n : J → R, ∑ k, n k • b k = B i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun R).1 (h (Submodule.subset_span ⟨i, rfl⟩))
  choose n hn using h1
  have e : B = (Matrix.of fun i k => (n i k : Ω)) * b := by
    ext i k
    rw [← hn i, Matrix.mul_apply, Finset.sum_apply]
    rfl
  refine ⟨c * Matrix.of fun i k => (n i k : Ω), mul_eq_one_comm.1 ?_⟩
  rw [Matrix.mul_assoc, ← e, hc]

theorem RatModel.exists_matrix_map_valF {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    {J : Type} {U : M.Z.Opens} (hU : (U : Set M.Z).Nonempty) (n : Matrix J J Ω)
    (h : ∀ z ∈ U, ∀ i j, n i j ∈ M.O z) : ∃ m : Matrix J J Γ(M.Z, U), m.map (M.res U hU) = n := by
  choose m hm using fun i j =>
    (RatModel.mem_ringOn_iff_exists hU).1 (RatModel.mem_ringOn.2 fun z hz => h z hz i j)
  refine ⟨Matrix.of m, ?_⟩
  ext i j
  exact (M.res_apply U hU _).trans (hm i j)

theorem exists_matrix_mul_eq_one_of_span_eq : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (J : Type) [Fintype J] [DecidableEq J] (W W' : M.Z.Opens) (b B : Matrix J J Ω) (c : Matrix J J Γ(M.Z, W')), (∀ z ∈ W ⊓ W', Submodule.span (M.O z) (Set.range b) = Submodule.span (M.O z) (Set.range B)) → c.map (valF M.pt W') * B = 1 → ∃ m m' : Matrix J J Γ(M.Z, W ⊓ W'), m * m' = 1 ∧ (((W ⊓ W' : M.Z.Opens) : Set M.Z).Nonempty → m.map (valF M.pt (W ⊓ W')) = b * c.map (valF M.pt W')) := by
  intro o Ω _ _ _ M J _ _ W W' b B c h hc
  by_cases hne : ((W ⊓ W' : M.Z.Opens) : Set M.Z).Nonempty
  swap
  · exact ⟨1, 1, Matrix.mul_one _, fun h' => absurd h' hne⟩
  obtain ⟨z₀, hz₀⟩ := id hne
  have hc' : B * c.map (valF M.pt W') = 1 := mul_eq_one_comm.1 hc
  obtain ⟨d, hd⟩ := exists_mul_eq_one_of_span_le (M.O z₀) (h z₀ hz₀).ge hc
  obtain ⟨m, hm⟩ := M.exists_matrix_map_valF hne (b * c.map (valF M.pt W')) fun z hz =>
    mul_inv_apply_mem_of_span_le (M.O z) (h z hz).le hc'
  obtain ⟨m', hm'⟩ := M.exists_matrix_map_valF hne (B * d) fun z hz =>
    mul_inv_apply_mem_of_span_le (M.O z) (h z hz).ge hd
  refine ⟨m, m', ?_, fun _ => ?_⟩
  · apply Matrix.map_injective (M.res_injective _ hne)
    dsimp only
    rw [Matrix.map_mul, hm, hm', Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_assoc,
      ← Matrix.mul_assoc _ B, hc, Matrix.one_mul, hd]
  · rw [← hm]
    ext i j
    exact (M.res_apply _ hne _).symm

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInvertibleMatrixChangeOfSpanEqStatement
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invertible_matrix_change_of_span_eq : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (J : Type) [Fintype J] [DecidableEq J] (W W' : M.Z.Opens) (b B : Matrix J J Ω) (c : Matrix J J Γ(M.Z, W')), (∀ z ∈ W ⊓ W', Submodule.span (M.O z) (Set.range b) = Submodule.span (M.O z) (Set.range B)) → c.map (valF M.pt W') * B = 1 → ∃ m m' : Matrix J J Γ(M.Z, W ⊓ W'), m * m' = 1 ∧ (((W ⊓ W' : M.Z.Opens) : Set M.Z).Nonempty → m.map (valF M.pt (W ⊓ W')) = b * c.map (valF M.pt W')) := by
  first | exact @GlobalTheory.ZH.exists_matrix_mul_eq_one_of_span_eq | exact GlobalTheory.ZH.exists_matrix_mul_eq_one_of_span_eq | (intros; apply GlobalTheory.ZH.exists_matrix_mul_eq_one_of_span_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDVRResidueGaloisAutomorphisms
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDVRResidueGaloisAutomorphisms
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory

namespace ResidueGalois

theorem galois_of_isInvariant (A B G : Type) [CommRing A] [CommRing B] [Algebra A B] [Group G]
    [Finite G] [MulSemiringAction G B] [Algebra.IsInvariant A B G] [SMulCommClass G A B]
    (k K : Type) [Field k] [Field K] [Algebra k K] [CharZero k] (p : A →+* k) (q : B →+* K)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (h : ∀ x, algebraMap k K (p x) = q (algebraMap A B x)) :
    FiniteDimensional k K ∧ IsGalois k K ∧
      ∀ τ : K ≃ₐ[k] K, ∃ σ : G, ∀ x, q (σ • x) = τ (q x) := by
  let P : Ideal A := RingHom.ker p
  let Q : Ideal B := RingHom.ker q
  have : P.IsPrime := RingHom.ker_isPrime p
  have : Q.IsPrime := RingHom.ker_isPrime q
  have : Q.LiesOver P := ⟨by
    ext x
    simp only [P, Q, Ideal.under, Ideal.mem_comap, RingHom.mem_ker, ← h, map_eq_zero]⟩
  let _ : Algebra (A ⧸ P) k := (RingHom.kerLift p).toAlgebra
  let _ : Algebra (B ⧸ Q) K := (RingHom.kerLift q).toAlgebra
  let _ : Algebra (A ⧸ P) K := ((algebraMap k K).comp (RingHom.kerLift p)).toAlgebra
  have : IsScalarTower (A ⧸ P) k K := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (A ⧸ P) (B ⧸ Q) K := .of_algebraMap_eq fun x => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact h x
  have : FaithfulSMul (A ⧸ P) k :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective p)
  have : FaithfulSMul (B ⧸ Q) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective q)
  have : IsFractionRing (A ⧸ P) k := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨x, rfl⟩ := hp z
    exact ⟨Ideal.Quotient.mk P x, 1, by rw [map_one, div_one]; rfl⟩
  have : IsFractionRing (B ⧸ Q) K := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨x, rfl⟩ := hq z
    exact ⟨Ideal.Quotient.mk Q x, 1, by rw [map_one, div_one]; rfl⟩
  have hn : Normal k K := Ideal.IsFractionRing.normal G P Q k K
  have hs : Algebra.IsSeparable k K := inferInstance
  refine ⟨Ideal.IsFractionRing.finite_of_isInvariant G P Q k K, { }, fun τ => ?_⟩
  obtain ⟨σ, rfl⟩ := IsFractionRing.stabilizerHom_surjective G P Q k K τ
  exact ⟨σ.1, fun x => (IsFractionRing.stabilizerHom_apply_apply_mk G P Q k K σ x).symm⟩

theorem map_maximalIdeal_le {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (f : A →+* B) (hf : f.IsIntegral) :
    (IsLocalRing.maximalIdeal A).map f ≤ IsLocalRing.maximalIdeal B := by
  have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hf (IsLocalRing.maximalIdeal B)
  rw [Ideal.map_le_iff_le_comap, IsLocalRing.eq_maximalIdeal this]

end ResidueGalois

theorem exists_cDvr_residue_galois : ∀ (V V' : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'], CDvr V → CDvr V' → (∀ n : ℕ, n ≠ 0 → IsUnit (n : V)) → ∀ g : V →+* V', Function.Injective g → g.Finite → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (j : V' →+* W), CDvr W ∧ Function.Injective j ∧ (IsLocalRing.maximalIdeal V').map j ≤ IsLocalRing.maximalIdeal W ∧ (IsLocalRing.maximalIdeal V).map (j.comp g) ≤ IsLocalRing.maximalIdeal W ∧ ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (p : V →+* k) (q : W →+* K), Function.Surjective p → Function.Surjective q → (∀ x, algebraMap k K (p x) = q (j (g x))) → FiniteDimensional k K ∧ IsGalois k K ∧ ∀ τ : K ≃ₐ[k] K, ∃ σ : W ≃+* W, (∀ x, σ (j (g x)) = j (g x)) ∧ ∀ x, q (σ x) = τ (q x) := by
  intro V V' _ _ _ _ _ _ hV _ hu g hg hfin
  obtain ⟨hd, hc, h0⟩ := (cDvr_iff V).1 hV
  let _ : Algebra V V' := g.toAlgebra
  have : Module.Finite V V' := hfin
  have : FaithfulSMul V V' := (faithfulSMul_iff_algebraMap_injective _ _).2 hg
  let K := FractionRing V
  let K' := FractionRing V'
  let _ : Algebra K K' := FractionRing.liftAlgebra V K'
  have : IsScalarTower V K K' := FractionRing.isScalarTower_liftAlgebra V K'
  have : FiniteDimensional K K' := inferInstance
  have : CharZero K := IsFractionRing.charZero_of_isFractionRing V
  let L := IntermediateField.normalClosure K K' (AlgebraicClosure K')
  have : FiniteDimensional K L := inferInstance
  have : IsGalois K L := inferInstance
  let W := integralClosure V L
  have hB : Module.Finite V W := IsIntegralClosure.finite V K L _
  have hBd : IsDiscreteValuationRing W := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr V K L
  have : IsFractionRing W L := IsIntegralClosure.isFractionRing_of_finite_extension V K L W
  let i : V' →ₐ[V] L :=
    ((IsScalarTower.toAlgHom K K' L).restrictScalars V).comp (IsScalarTower.toAlgHom V V' K')
  have hi : Function.Injective i :=
    (algebraMap K' L).injective.comp (IsFractionRing.injective V' K')
  let j : V' →ₐ[V] W := i.codRestrict W fun x => (Algebra.IsIntegral.isIntegral x).map i
  have hj : Function.Injective j := fun x y h => hi (congrArg Subtype.val h)
  have hjg : ∀ x, j (g x) = algebraMap V W x := fun x => j.commutes x
  have hjg' : (j : V' →+* W).comp g = algebraMap V W := RingHom.ext hjg
  have hint : ((j : V' →+* W).comp g).IsIntegral := by
    rw [hjg']
    exact fun x => Algebra.IsIntegral.isIntegral x
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  refine ⟨W, inferInstance, inferInstance, inferInstance, (j : V' →+* W),
    (cDvr_iff W).2 ⟨hBd, CompleteFiniteExtension.isAdicComplete_of_finite_local V W,
      inferInstance⟩, hj,
    ResidueGalois.map_maximalIdeal_le _ (RingHom.IsIntegral.tower_top g _ hint),
    ResidueGalois.map_maximalIdeal_le _ hint, ?_⟩
  intro k K₁ _ _ _ p q hp hq h
  have : CharZero k := ⟨fun m n hmn => by
    by_contra hne
    wlog hlt : m < n generalizing m n
    · exact this n m hmn.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
    have := ((hu (n - m) (by omega)).map p).ne_zero
    rw [map_natCast, Nat.cast_sub hlt.le, hmn, sub_self] at this
    exact this rfl⟩
  have : Algebra.IsInvariant V W (W ≃ₐ[V] W) := Algebra.isInvariant_of_isGalois' V K L W
  have : Finite (W ≃ₐ[V] W) := Finite.of_equiv _ (galRestrict V K L W).toEquiv
  obtain ⟨h₁, h₂, h₃⟩ := ResidueGalois.galois_of_isInvariant V W (W ≃ₐ[V] W) k K₁ p q hp hq
    fun x => (h x).trans (congrArg q (hjg x))
  refine ⟨h₁, h₂, fun τ => ?_⟩
  obtain ⟨σ, hσ⟩ := h₃ τ
  refine ⟨σ.toRingEquiv, fun x => ?_, hσ⟩
  change σ (j (g x)) = j (g x)
  rw [hjg, AlgEquiv.commutes]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDVRResidueGaloisAutomorphismsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completeDVR_residue_galois_automorphisms : ∀ (V V' : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'], CDvr V → CDvr V' → (∀ n : ℕ, n ≠ 0 → IsUnit (n : V)) → ∀ g : V →+* V', Function.Injective g → g.Finite → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (j : V' →+* W), CDvr W ∧ Function.Injective j ∧ (IsLocalRing.maximalIdeal V').map j ≤ IsLocalRing.maximalIdeal W ∧ (IsLocalRing.maximalIdeal V).map (j.comp g) ≤ IsLocalRing.maximalIdeal W ∧ ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (p : V →+* k) (q : W →+* K), Function.Surjective p → Function.Surjective q → (∀ x, algebraMap k K (p x) = q (j (g x))) → FiniteDimensional k K ∧ IsGalois k K ∧ ∀ τ : K ≃ₐ[k] K, ∃ σ : W ≃+* W, (∀ x, σ (j (g x)) = j (g x)) ∧ ∀ x, q (σ x) = τ (q x) := by
  first | exact @GlobalTheory.exists_cDvr_residue_galois | exact GlobalTheory.exists_cDvr_residue_galois | (intros; apply GlobalTheory.exists_cDvr_residue_galois <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibrewiseNonzeroSectionProdAndBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibrewiseNonzeroSectionProdAndBaseChange
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section
namespace GlobalTheory.FibreNonzero

def pullOne {X Y : Scheme.{0}} {L : LB X} (θ : L.Sec) (h : Y ⟶ X) :
    LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => h) (fun _ => ((1 : ℕ) : ℤ))) :=
  LBGerm.secOfGerm (fun j => (Y.presheaf.map (homOfLE (LB.wchart_le L (fun _ : Fin 1 => h) j 0)).op).hom
      ((h.app (L.U (j 0))).hom (θ.f (j 0)))) fun y i j hi hj => by
    have hi' : (𝟙 Y ≫ h) y ∈ L.U (i 0) := Set.mem_iInter.1 hi 0
    have hj' : (𝟙 Y ≫ h) y ∈ L.U (j 0) := Set.mem_iInter.1 hj 0
    refine ((gs_res _ y _ hi _).trans (gs_pull (𝟙 Y) h y _ hi' _)).trans ((gs_compat θ _ y hi' hj').trans
      (congrArg₂ (· * ·) (congrArg Units.val ?_) ((gs_res _ y _ hj _).trans (gs_pull (𝟙 Y) h y _ hj' _)).symm))
    refine Eq.trans ?_ (gm_linComb L (fun _ : Fin 1 => h) (fun _ => ((1 : ℕ) : ℤ)) (𝟙 Y) y i j hi hj).symm
    simp

theorem mem_nonzeroLocus_pullOne {X Y : Scheme.{0}} {L : LB X} (θ : L.Sec) (h : Y ⟶ X) (y : Y) (i : L.ι)
    (hy : h y ∈ X.basicOpen (θ.f i)) : y ∈ nonzeroLocus (pullOne θ h) := by
  have hi' : (𝟙 Y ≫ h) y ∈ L.U i := X.basicOpen_le _ hy
  have hi : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun _ : Fin 1 => h) (fun _ => i) := Set.mem_iInter.2 fun _ => hi'
  refine (mem_nonzeroLocus_iff_isUnit (pullOne θ h) (k := fun _ => i) hi).2 ?_
  have e := (gs_res (𝟙 Y) y (LB.wchart_le L (fun _ : Fin 1 => h) (fun _ => i) 0) hi _).trans
    (gs_pull (𝟙 Y) h y _ hi' (θ.f i))
  exact e ▸ (LBGerm.isUnit_gs_iff _ y _ hi' _).2 hy

theorem isIso_snd_left {S : Scheme.{0}} (G : Over S) : IsIso (snd (𝟙_ (Over S)) G).left := by
  have : IsIso (snd (𝟙_ (Over S)) G) := by
    rw [← leftUnitor_hom]; infer_instance
  exact inferInstanceAs (IsIso ((Over.forget S).map (snd (𝟙_ (Over S)) G)))

end GlobalTheory.FibreNonzero


open GlobalTheory.FibreNonzero in
theorem GlobalTheory.fibNZ_prod_and_baseChange : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (A' : PolAV (Sp (FractionRing V))) (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C : Cmp φ U U' F), (ThetaNZ G U.P.L.L → ∃ σ : U.SecGT (𝟙_ _) 1, FibNZ (𝟙_ _ ⊗ G).hom σ) ∧ ∀ (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (σ' : U'.SecGT (𝟙_ _) k), (∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left), r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' → sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))).val ^ k * sval σ' r' z J') → FibNZ (𝟙_ _ ⊗ G).hom σ → FibNZ (𝟙_ _ ⊗ G').hom σ' := by
  intro R V _ _ _ _ I I' φ D D' A G _ _ A' G' _ _ U U' F C
  have := isIso_snd_left G
  have := isIso_snd_left G'
  refine ⟨fun ⟨θ, hθ⟩ => ⟨pullOne θ _, fun y => ?_⟩, fun k σ σ' h hσ y' => ?_⟩
  · obtain ⟨g, i, hg, hi⟩ := hθ y
    obtain ⟨z, rfl⟩ := (snd (𝟙_ _) G).left.surjective g
    refine ⟨z, ?_, mem_nonzeroLocus_pullOne θ _ z i hi⟩
    rw [← Over.w (snd (𝟙_ _) G), Scheme.Hom.comp_apply, hg]
  · obtain ⟨z, hz, hzσ⟩ := hσ (spMap φ y')
    rw [← Over.w (snd (𝟙_ _) G), Scheme.Hom.comp_apply] at hz
    obtain ⟨g', hg₁, hg₂⟩ := Scheme.exists_preimage_of_isPullback C.pb.1 _ y' hz
    obtain ⟨z', rfl⟩ := (snd (𝟙_ _) G').left.surjective g'
    refine ⟨z', by rw [← Over.w (snd (𝟙_ _) G'), Scheme.Hom.comp_apply, hg₂], ?_⟩
    let r : (𝟙_ _ ⊗ G').left ⟶ (𝟙_ _ ⊗ G).left := (snd (𝟙_ _) G').left ≫ F ≫ inv (snd (𝟙_ _) G).left
    have hr : r ≫ (snd _ G).left = 𝟙 _ ≫ (snd _ G').left ≫ F := by simp [r]
    have hrz : r z' = z := by
      apply (snd (𝟙_ _) G).left.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hr, Category.id_comp, Scheme.Hom.comp_apply, hg₁]
    obtain ⟨J, hJ⟩ := exists_good_pt U.P.L.isLB z'
    obtain ⟨J', hJ'⟩ := exists_good_pt U'.P.L.isLB z'
    have u := (MulPullSec.mem_nonzeroLocus_iff σ r z' hJ).1 (hrz ▸ hzσ)
    rw [h _ (𝟙 _) r hr z' J J' hJ hJ'] at u
    exact (MulPullSec.mem_nonzeroLocus_iff σ' (𝟙 _) z' hJ').2 (isUnit_of_mul_isUnit_right u)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibrewiseNonzeroSectionProdAndBaseChangeStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibrewiseNonzeroSection_prod_and_baseChange : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (A' : PolAV (Sp (FractionRing V))) (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C : Cmp φ U U' F), (ThetaNZ G U.P.L.L → ∃ σ : U.SecGT (𝟙_ _) 1, FibNZ (𝟙_ _ ⊗ G).hom σ) ∧ ∀ (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (σ' : U'.SecGT (𝟙_ _) k), (∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left), r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' → sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))).val ^ k * sval σ' r' z J') → FibNZ (𝟙_ _ ⊗ G).hom σ → FibNZ (𝟙_ _ ⊗ G').hom σ' := by
  first | exact @GlobalTheory.fibNZ_prod_and_baseChange | exact GlobalTheory.fibNZ_prod_and_baseChange | (intros; apply GlobalTheory.fibNZ_prod_and_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NatCastNeZeroOfIsUnit
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.FewAtTest

open GlobalTheory.CechPic

theorem pic_eq_zero_of_generic {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {H : Scheme.{0}}
    (p : H ⟶ Sp V) (e : Sp V ⟶ H) (hs : Smooth p) (hi : GeometricallyIntegral p) (he : e ≫ p = 𝟙 _) (c : Pic H)
    (h₁ : pull (pullback.fst p (Out.jK V)) c = 0) (h₂ : pull e c = 0) : c = 0 := by
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  let eK : Sp (FractionRing V) ⟶ pullback p (Out.jK V) := pullback.lift (Out.jK V ≫ e) (𝟙 _) (by
    rw [Category.assoc, he, Category.id_comp]; exact Category.comp_id _)
  have heK : eK ≫ pullback.fst p (Out.jK V) = Out.jK V ≫ e := pullback.lift_fst _ _ _
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff (pull_isLB hM (pullback.fst p (Out.jK V) ≫ 𝟙 H))).1 (by
    rw [cls_pull hM, pull_comp, pull_id, h₁])
  obtain ⟨ρ, hρ⟩ := (cls_eq_zero_iff (pull_isLB hM (e ≫ 𝟙 H))).1 (by
    rw [cls_pull hM, pull_comp, pull_id, h₂])
  obtain ⟨u, hu, cu⟩ := DVR.exists_normalized_to hM _ _ t ht (pullback.snd p (Out.jK V)) eK
    (pullback.lift_snd _ _ _) _ _ (LB.pullGen M _ _ ρ (Out.jK V)) (DVR.pullGen_isGen _ _ _ _ hρ _) (by
      congr 1
      funext k
      rw [← Category.assoc, heK, Category.assoc])
  obtain ⟨s, ⟨hs₁, -⟩, -⟩ := GenExtend.existsUnique_gen_extend V (FractionRing V) H H p e hs hi he eK heK M hM
    PUnit (fun _ => 𝟙 H) (fun _ => 1) u ρ hu hρ cu
  have := (cls_eq_zero_iff (pull_isLB hM (𝟙 H))).2 ⟨s, hs₁⟩
  rwa [cls_pull hM, pull_id] at this

theorem lbIso_of_generic {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {G : Over (Sp V)}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (L M : RigLB G)
    (h : LBIso (L.L.pull (pullback.fst G.hom (Out.jK V))) (M.L.pull (pullback.fst G.hom (Out.jK V)))) :
    LBIso L.L M.L := by
  refine (cls_eq_iff L.isLB M.isLB).1 (sub_eq_zero.1 (pic_eq_zero_of_generic G.hom (eSec G) hG.smooth
    (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hG.smooth hG.geomConnected)
    (Over.w η[G]) _ ?_ ?_))
  · rw [map_sub, sub_eq_zero]
    exact (cls_eq_iff (pull_isLB L.isLB _) (pull_isLB M.isLB _)).2 h
  · have a := (cls_eq_zero_iff (pull_isLB L.isLB (eSec G))).2 ⟨L.rig, L.rigGen⟩
    have b := (cls_eq_zero_iff (pull_isLB M.isLB (eSec G))).2 ⟨M.rig, M.rigGen⟩
    rw [cls_pull L.isLB] at a
    rw [cls_pull M.isLB] at b
    exact (map_sub _ _ _).trans (sub_eq_zero.2 (a.trans b.symm))

theorem natCast_ne_zero_of_isUnit {Z : Scheme.{0}} {K : Type} [Field K] (x : Sp K ⟶ Z) {n : ℕ}
    (h : IsUnit (n : Γ(Z, ⊤))) : (n : K) ≠ 0 := by
  have := (h.map x.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
  rw [map_natCast, map_natCast] at this
  exact this.ne_zero

theorem range_rPt {p : ℕ} [Fact p.Prime] {V : Type} [CommRing V] [IsLocalRing V] (j : V →+* OO p) [IsLocalHom j] :
    Set.range (rPt p ≫ spMap j : Sp (kb p) ⟶ Sp V) = {IsLocalRing.closedPoint V} := by
  have key : ∀ x : Sp (kb p), (rPt p ≫ spMap j : Sp (kb p) ⟶ Sp V) x = IsLocalRing.closedPoint V := fun x => by
    have hx : x = IsLocalRing.closedPoint (kb p) := Subsingleton.elim (α := PrimeSpectrum (kb p)) _ _
    subst hx
    exact (congrArg (PrimeSpectrum.comap j) (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))).trans
      (IsLocalRing.comap_closedPoint j)
  ext x
  exact ⟨fun ⟨a, ha⟩ => ha ▸ key a, fun h => ⟨IsLocalRing.closedPoint (kb p), (key _).trans h.symm⟩⟩

end GlobalTheory.FewAtTest

namespace GlobalTheory.ZJ

open GlobalTheory.FewAtTest

theorem theta_few : GlobalTheory.ZH.ThmUSt → Out.Laws → Out.Laws2 → ∀ (C : Core) (T : C.Theta), Out.RelAmple C.A T.L.L → Out.KTriv C.A T.L.L → T.L.IsSymmetric → GlobalTheory.ZH.HypS C.A T.L.L → ∀ N n : ℕ, 4 ≤ N → IsUnit (n : Γ(C.Z, ⊤)) → 6 * (N ^ C.g * C.g.factorial) < n ^ 2 → T.Few n := by
  intro hU laws laws₂ C T hA hK hs hS N n hN hn hlt p _ y τ E c
  obtain ⟨-, h0, hG⟩ := (core_basic C).2.2.2.2.2.2.2.2.2.2.2.2 p y τ
  have hL := pull_isLB T.L.isLB τ.φ
  have hi := PolBaseChange.lbIso_refl hL
  obtain ⟨hab, hamp, hkt⟩ := pol_pull _ _ C.A ((Over.pullback (Out.jK τ.V)).obj τ.H) τ.yK τ.φ T.L.L (T.L.L.pull τ.φ)
    T.L.isLB hL C.ab τ.φ_cart hi
  let A : Out.PolAV (Sp (FractionRing τ.V)) :=
    { A := (Over.pullback (Out.jK τ.V)).obj τ.H
      isAb := hab
      g := C.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback τ.φ_cart.1 C.dim
      L := T.L.L.pull τ.φ
      isLB := hL
      rigid := PolBaseChange.rigidified_pull τ.φ_cart ⟨T.L.rig, T.L.rigGen⟩
      sym := PolBaseChange.sym_pull τ.φ_cart (CechPic.sym_of_isSymmetric T.L hs)
      ample := hamp hA
      ktriv := hkt hK }
  have := hab.comm
  have hS' := SymBaseChange.hypS_baseChange _ _ C.A ((Over.pullback (Out.jK τ.V)).obj τ.H) τ.yK τ.φ T.L.L
    (T.L.L.pull τ.φ) T.L.isLB hL τ.φ_cart hi hS
  obtain ⟨D, U, hgen⟩ := hU τ.V τ.complete A τ.H hG τ.split hS' (Iso.refl _)
    (inferInstanceAs (IsMonHom (𝟙 ((Over.pullback (Out.jK τ.V)).obj τ.H))))
  have e₁ : LBIso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst τ.H.hom (Out.jK τ.V))) := U.ext
  rw [hgen] at e₁
  have e₂ : LBIso (E.L.L.pull (pullback.fst τ.H.hom (Out.jK τ.V))) (A.L.pull (𝟙 _)) :=
    LBIso.trans (pull_isLB E.L.isLB _) hL (pull_isLB hL _) (LBIso.symm ⟨E.w, E.w_gen⟩)
      (CechPic.iso_of_chart hL (Geo.Tor.chartPullPull _ _ _ rfl)).symm
  have e := lbIso_of_generic hG E.L U.LG
    (LBIso.trans (pull_isLB E.L.isLB _) (pull_isLB hL _) (pull_isLB U.LG.isLB _) e₂ e₁)
  have := isAlgClosed_kb (p := p)
  have := τ.j_loc
  exact GlobalTheory.FewZeros.card_torsion_translate_zeros_lt laws laws₂ τ.V τ.complete D A τ.H U E.L.L E.θ E.L.isLB e E.θ_ne (kb p) (rPt p ≫ spMap τ.j) N n
    (range_rPt τ.j) hN (natCast_ne_zero_of_isUnit (rPt p ≫ y) hn) hlt c

end GlobalTheory.ZJ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowPointIntegralPadicGroupScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowPointIntegralPadicGroupScheme
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Topology Filter GlobalTheory.Points

namespace GlobalTheory.IntegralPower

theorem eventually_extends {V C : Type} [CommRing V] [IsLocalRing V] [CommRing C] [TopologicalSpace C]
    (σ : V →+* C) (hσ : Function.Injective σ) (ho : IsOpen (Set.range σ)) {X : Scheme.{0}} (q : X ⟶ Sp V)
    [LocallyOfFiniteType q] (y : Sp V ⟶ X) :
    ∀ᶠ x : Sp C ⟶ X in 𝓝 (spMap σ ≫ y), x ≫ q = spMap σ →
      ∃ z : Sp V ⟶ X, z ≫ q = 𝟙 _ ∧ spMap σ ≫ z = x := by
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_le y (le_preimage_top _)
  have hy' : ⊤ ≤ (spMap σ ≫ y) ⁻¹ᵁ U := le_preimage_comp _ y hy (le_preimage_top _)
  let c : V →+* Γ(X, U) := (q.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
  have hc : ∀ a, c a = constFn q U a := fun _ => rfl
  have hft : c.FiniteType := (q.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).inv).2)
  letI := c.toAlgebra
  obtain ⟨s, hs⟩ := (show Algebra.FiniteType V Γ(X, U) from hft).out
  have h1 : ∀ᶠ x : Sp C ⟶ X in 𝓝 (spMap σ ≫ y), ∀ f ∈ s, valR x U f ∈ Set.range σ := by
    refine (eventually_all_finset s).2 fun f _ => (continuousAt_valR f hy').eventually (ho.mem_nhds ?_)
    exact ⟨_, (valR_spMap_comp σ y U hy f).symm⟩
  filter_upwards [h1, (isOpen_setOf_le_preimage U).mem_nhds hy'] with x hx hxU hxq
  have h2 : ∀ f, (valMap x U hxU).hom f ∈ σ.range := by
    intro f
    have hf : f ∈ Algebra.adjoin V (s : Set Γ(X, U)) := hs ▸ Algebra.mem_top
    induction hf using Algebra.adjoin_induction with
    | mem f hf =>
      rw [← valR_eq]
      exact hx f hf
    | algebraMap a =>
      rw [← valR_eq]
      exact ⟨a, (valR_constFn_of_over q σ x hxq U hxU a).symm⟩
    | add f g _ _ hf hg =>
      rw [map_add (f := _)]
      exact add_mem hf hg
    | mul f g _ _ hf hg =>
      rw [map_mul]
      exact mul_mem hf hg
  let e : V ≃+* σ.range := RingEquiv.ofBijective σ.rangeRestrict
    ⟨fun a b h => hσ (congrArg Subtype.val h), σ.rangeRestrict_surjective⟩
  let ψ : Γ(X, U) →+* V := e.symm.toRingHom.comp ((valMap x U hxU).hom.codRestrict σ.range h2)
  have hψ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom σ = valMap x U hxU := by
    ext f
    exact congrArg Subtype.val (e.apply_symm_apply ⟨_, h2 f⟩)
  have hz : spMap σ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec = x := by
    rw [← Category.assoc, ← Spec.map_comp, hψ, specMap_valMap_fromSpec]
  refine ⟨_, ?_, hz⟩
  rw [← hz, Category.assoc] at hxq
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec) ≫ q)
  rw [← hφ, ← Spec.map_comp] at hxq
  rw [← hφ, ← Spec.map_id]
  congr 1
  ext a
  exact hσ (congrArg (fun u => u.hom a) (Spec.map_injective hxq))

section Group

variable {C : Type} [CommRing C] [TopologicalSpace C] {S : Scheme.{0}} (t : Sp C ⟶ S)


omit [TopologicalSpace C] in
abbrev leftPt {A : Over S} (x : Over.mk t ⟶ A) : Sp C ⟶ A.left := x.left

abbrev ptTopology (A : Over S) : TopologicalSpace (Over.mk t ⟶ A) :=
  TopologicalSpace.induced (leftPt t) (topology C A.left)

attribute [local instance] ptTopology

theorem isEmbedding_leftPt (A : Over S) : IsEmbedding (leftPt t (A := A)) :=
  ⟨⟨rfl⟩, fun _ _ h => Over.OverMorphism.ext h⟩

theorem compactSpace_of_ptsOver (A : Over S) [CompactSpace (PtsOver A.hom t)] :
    CompactSpace (Over.mk t ⟶ A) :=
  Function.Surjective.compactSpace (f := fun x : PtsOver A.hom t => (Over.homMk x.1 x.2 : Over.mk t ⟶ A))
    ((isEmbedding_leftPt t A).continuous_iff.2 continuous_subtype_val) fun x => ⟨⟨x.left, Over.w x⟩, rfl⟩

theorem continuous_comp_over {A B : Over S} (g : A ⟶ B) : Continuous fun x : Over.mk t ⟶ A => x ≫ g :=
  (isEmbedding_leftPt t B).continuous_iff.2 ((continuous_comp g.left).comp (isEmbedding_leftPt t A).continuous)

variable [IsTopologicalRing C] [IsLocalRing C] [IsOpenUnits C]

theorem continuous_lift (A B : Over S) :
    Continuous fun q : (Over.mk t ⟶ A) × (Over.mk t ⟶ B) => lift q.1 q.2 := by
  refine (isEmbedding_leftPt t _).continuous_iff.2 ?_
  refine (isEmbedding_of_isPullback (C := C) (IsPullback.of_hasPullback A.hom B.hom)).continuous_iff.2 ?_
  refine ((isEmbedding_leftPt t A).continuous.prodMap (isEmbedding_leftPt t B).continuous).congr fun q => ?_
  exact Prod.ext (congrArg (·.left) (lift_fst q.1 q.2)).symm (congrArg (·.left) (lift_snd q.1 q.2)).symm

theorem isTopologicalGroup (G : Over S) [GrpObj G] : IsTopologicalGroup (Over.mk t ⟶ G) := {
  continuous_mul := (continuous_comp_over t (μ[G])).comp (continuous_lift t G G)
  toContinuousInv :=
    ⟨by simpa only [Hom.inv_def] using continuous_comp_over t (GrpObj.inv (X := G))⟩ }

end Group


attribute [local instance] ptTopology in
theorem exists_pow_extends {V F : Type} [CommRing V] [IsLocalRing V] [NormedField F] [ProperSpace F]
    (σ : V →+* F) (hσ : Function.Injective σ) (ho : IsOpen (Set.range σ)) (G : Over (Sp V)) [GrpObj G]
    [LocallyOfFiniteType G.hom] (h : IsProjOver (pullback.snd G.hom (spMap σ))) (a : Over.mk (spMap σ) ⟶ G) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ g : 𝟙_ (Over (Sp V)) ⟶ G, toUnit _ ≫ g = a ^ k := by
  have h1 : CompactSpace (Pts (pullback.snd G.hom (spMap σ))) := PtsOver.compactSpace h _
  have h2 := (PtsOver.baseChangeHomeomorph (IsPullback.of_hasPullback G.hom (spMap σ))).compactSpace
  have h3 := compactSpace_of_ptsOver (spMap σ) G
  have h4 := isTopologicalGroup (spMap σ) G
  let r : (𝟙_ (Over (Sp V)) ⟶ G) →* (Over.mk (spMap σ) ⟶ G) :=
    MonoidHom.mk' (fun g => toUnit _ ≫ g) fun g g' => comp_mul _ g g'
  have hr : ∀ g, leftPt _ (r g) = spMap σ ≫ g.left := fun g => by
    have : (toUnit (Over.mk (spMap σ))).left = spMap σ := (Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk (spMap σ))))
    exact congrArg (· ≫ g.left) this
  have hopen : IsOpen (r.range : Set (Over.mk (spMap σ) ⟶ G)) := by
    refine r.range.isOpen_of_mem_nhds (g := r 1) ?_
    have h5 := eventually_extends σ hσ ho G.hom (1 : 𝟙_ (Over (Sp V)) ⟶ G).left
    rw [← hr] at h5
    filter_upwards [(isEmbedding_leftPt _ G).continuous.continuousAt.eventually h5] with x hx
    obtain ⟨z, hz, hzx⟩ := hx (Over.w x)
    exact ⟨Over.homMk z hz, (isEmbedding_leftPt _ G).injective ((hr _).trans hzx)⟩
  have h6 : Finite (_ ⧸ r.range) := r.range.quotient_finite_of_isOpen hopen
  obtain ⟨k, hk, -, g, hg⟩ := r.range.exists_pow_mem_of_index_ne_zero Subgroup.index_ne_zero_of_finite a
  exact ⟨k, hk, g, hg⟩

theorem exists_pow_integral : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (G : Over (Sp (integralClosure ℤ_[p] K))) [GrpObj G] [LocallyOfFiniteType G.hom] [IsSeparated G.hom], IsProjOver (pullback.snd G.hom (spMap (algebraMap (integralClosure ℤ_[p] K) K))) → ∀ a : Over.mk (spMap (algebraMap (integralClosure ℤ_[p] K) K)) ⟶ G, ∃ k : ℕ, 1 ≤ k ∧ ∃ g : 𝟙_ (Over (Sp (integralClosure ℤ_[p] K))) ⟶ G, toUnit _ ≫ g = a ^ k := by
  intro p _ K _ G _ _ _ h a
  letI : NormedField K := inferInstanceAs (NormedField K.toSubfield)
  letI : NormedSpace ℚ_[p] K := ⟨fun c x => norm_smul_le c (x : PadicAlgCl p)⟩
  haveI : ProperSpace K := FiniteDimensional.proper ℚ_[p] K
  haveI : IsUltrametricDist K := ⟨fun x y z => IsUltrametricDist.dist_triangle_max (x : PadicAlgCl p) y z⟩
  refine exists_pow_extends _ Subtype.val_injective ?_ G h a
  convert IsUltrametricDist.isOpen_closedBall (0 : K) one_ne_zero using 1
  ext x
  rw [mem_closedBall_zero_iff]
  exact (Set.ext_iff.1 Subtype.range_val x).trans (mem_integralClosure_padicInt_iff K x)

end GlobalTheory.IntegralPower
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowPointIntegralPadicGroupSchemeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_point_integral_padic_groupScheme : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (G : Over (Sp (integralClosure ℤ_[p] K))) [GrpObj G] [LocallyOfFiniteType G.hom] [IsSeparated G.hom], IsProjOver (pullback.snd G.hom (spMap (algebraMap (integralClosure ℤ_[p] K) K))) → ∀ a : Over.mk (spMap (algebraMap (integralClosure ℤ_[p] K) K)) ⟶ G, ∃ k : ℕ, 1 ≤ k ∧ ∃ g : 𝟙_ (Over (Sp (integralClosure ℤ_[p] K))) ⟶ G, toUnit _ ≫ g = a ^ k := by
  first | exact @GlobalTheory.IntegralPower.exists_pow_integral | exact GlobalTheory.IntegralPower.exists_pow_integral | (intros; apply GlobalTheory.IntegralPower.exists_pow_integral <;> assumption)
end
end
