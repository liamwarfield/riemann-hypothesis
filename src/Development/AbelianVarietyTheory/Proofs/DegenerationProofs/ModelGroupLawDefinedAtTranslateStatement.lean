module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelGroupLawDefinedAtTranslate
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GlueModelsOverSubfield
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelGroupLawDefinedAtTranslateStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelGroupLaw_definedAt_translate : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, Strict M → ∀ z : (M.prod M).Y.left, ∃ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso M M (transl a).hom ∧ DefAt (M.prod M) (M.twist (transl a)) (μ[A]) z := by
  first | exact @GlobalTheory.SS.defAt_mul_twist | exact GlobalTheory.SS.defAt_mul_twist | (intros; apply GlobalTheory.SS.defAt_mul_twist <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSchemeModelOfAffineSmoothChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSchemeModelOfAffineSmoothChart
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.ChartModel

set_option backward.isDefEq.respectTransparency false

noncomputable def twoCover {X U V : Scheme.{0}} (u : U ⟶ X) (v : V ⟶ X) [IsOpenImmersion u] [IsOpenImmersion v]
    (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v) : X.OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun i => Bool.rec U V i)
    (fun i => Bool.rec (motive := fun i => (Bool.rec U V i : Scheme.{0}) ⟶ X) u v i) (fun x => by
    rcases hc x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩) (fun i => by cases i <;> assumption)

theorem isClosedImmersion_snd_diagonal {U Y S : Scheme.{0}} (g : U ⟶ Y) (f : Y ⟶ S) [Mono g]
    [IsSeparated (g ≫ f)] :
    IsClosedImmersion (pullback.snd (pullback.diagonal f)
      (pullback.map (g ≫ f) (g ≫ f) f f g g (𝟙 _) (Category.comp_id _) (Category.comp_id _))) := by
  have H := pullback_map_diagonal_isPullback g g f
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion H.isoPullback.hom,
    H.isoPullback_hom_snd, ← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion (pullback.diagonal g)]
  convert (inferInstance : IsClosedImmersion (pullback.diagonal (g ≫ f)))
  ext : 1 <;> simp

theorem isSeparated_of_two {U V Y S : Scheme.{0}} (u : U ⟶ Y) (v : V ⟶ Y) (f : Y ⟶ S) [IsOpenImmersion u]
    [IsOpenImmersion v] [IsSeparated (u ≫ f)] [IsSeparated (v ≫ f)]
    (h : ∀ x y : Y, f x = f y → (x ∈ Set.range u ∧ y ∈ Set.range u) ∨ (x ∈ Set.range v ∧ y ∈ Set.range v)) :
    IsSeparated f := by
  constructor
  refine IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) (twoCover
    (pullback.map (u ≫ f) (u ≫ f) f f u u (𝟙 _) (Category.comp_id _) (Category.comp_id _))
    (pullback.map (v ≫ f) (v ≫ f) f f v v (𝟙 _) (Category.comp_id _) (Category.comp_id _)) ?_) ?_
  · intro z
    rw [Scheme.Pullback.range_map, Scheme.Pullback.range_map]
    exact h _ _ (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition])
  · rintro (_ | _)
    · exact isClosedImmersion_snd_diagonal u f
    · exact isClosedImmersion_snd_diagonal v f

theorem exists_glue_chart {S T A X W : Scheme.{0}} (i : T ⟶ S) [IsOpenImmersion i] (a : A ⟶ T) (c : X ⟶ S)
    {p : W ⟶ X} {w : W ⟶ T} (hW : IsPullback p w c i) (u : W ⟶ A) [IsOpenImmersion u] (hu : u ≫ a = w)
    [Smooth a] [IsSeparated a] [Smooth c] [IsSeparated c] [CompactSpace A] [CompactSpace X] :
    ∃ (Y : Scheme.{0}) (f : Y ⟶ S) (g : X ⟶ Y) (j : A ⟶ Y), IsOpenImmersion g ∧ IsPullback j a f i ∧ g ≫ f = c ∧
      p ≫ g = u ≫ j ∧ Smooth f ∧ IsSeparated f ∧ CompactSpace Y ∧ ∀ y, f y ∉ Set.range i → y ∈ Set.range g := by
  have : IsOpenImmersion p := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hW.flip ‹_›
  have := GlueModels.isOpenImmersion_inl p u
  have := GlueModels.isOpenImmersion_inr p u
  have hc := GlueModels.pushout_cover p u
  let f : pushout p u ⟶ S := pushout.desc c (a ≫ i) (by rw [hW.w, ← Category.assoc, hu])
  have h1 : pushout.inl p u ≫ f = c := pushout.inl_desc _ _ _
  have h2 : pushout.inr p u ≫ f = a ≫ i := pushout.inr_desc _ _ _
  have e1 (x : X) : f (pushout.inl p u x) = c x := congrArg (fun g => g x) h1
  have e2 (x : A) : f (pushout.inr p u x) = i (a x) := congrArg (fun g => g x) h2
  have e3 (x : W) : pushout.inl p u (p x) = pushout.inr p u (u x) :=
    congrArg (fun g => g x) (pushout.condition (f := p) (g := u))
  have hin (y) (hy : f y ∈ Set.range i) : y ∈ Set.range (pushout.inr p u) := by
    rcases hc y with ⟨x, rfl⟩ | hy
    · obtain ⟨t, ht⟩ := hy
      obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hW x t ((e1 x).symm.trans ht.symm)
      exact ⟨u z, (e3 z).symm⟩
    · exact hy
  have hout (y) (hy : f y ∉ Set.range i) : y ∈ Set.range (pushout.inl p u) := by
    rcases hc y with h | ⟨x, rfl⟩
    · exact h
    · exact absurd ⟨a x, (e2 x).symm⟩ hy
  refine ⟨_, f, pushout.inl p u, pushout.inr p u, inferInstance, ?_, h1, pushout.condition, ?_, ?_, ?_, hout⟩
  · refine (IsOpenImmersion.isPullback _ _ _ _ h2 ?_).flip
    ext y
    constructor
    · exact hin y
    · rintro ⟨x, rfl⟩
      exact ⟨a x, (e2 x).symm⟩
  · refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) (twoCover _ _ hc) ?_
    rintro (_ | _)
    · change Smooth (pushout.inl p u ≫ f)
      rw [h1]; infer_instance
    · change Smooth (pushout.inr p u ≫ f)
      rw [h2]; infer_instance
  · have : IsSeparated (pushout.inl p u ≫ f) := by rw [h1]; infer_instance
    have : IsSeparated (pushout.inr p u ≫ f) := by rw [h2]; infer_instance
    refine isSeparated_of_two (pushout.inl p u) (pushout.inr p u) f fun x y hxy => ?_
    by_cases hx : f x ∈ Set.range i
    · exact Or.inr ⟨hin x hx, hin y (hxy ▸ hx)⟩
    · exact Or.inl ⟨hout x hx, hout y (hxy ▸ hx)⟩
  · refine ⟨?_⟩
    rw [← Set.eq_univ_of_forall (s := Set.range (pushout.inl p u) ∪ Set.range (pushout.inr p u)) hc]
    exact (isCompact_range (pushout.inl p u).continuous).union (isCompact_range (pushout.inr p u).continuous)

theorem exists_model_of_chart : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)), Smooth A.hom → IsSeparated A.hom → QuasiCompact A.hom → ∀ (C : Type) [CommRing C] [Algebra R C], Algebra.Smooth R C → ∀ u : Sp (TensorProduct R K C) ⟶ A.left, IsOpenImmersion u → u ≫ A.hom = spMap (algebraMap K (TensorProduct R K C)) → ∃ (M : Model R A) (g : Sp C ⟶ M.Y.left), IsOpenImmersion g ∧ g ≫ M.Y.hom = spMap (algebraMap R C) ∧ spMap (Algebra.TensorProduct.includeRight : C →ₐ[R] TensorProduct R K C).toRingHom ≫ g = u ≫ M.j ∧ M.sp ⊆ Set.range g := by
  intro R K _ _ _ _ _ _ A hA hs hq C _ _ hC u hu hua
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hloc : IsLocalization.Away π K := by
    refine (IsLocalization.iff_of_le_of_exists_dvd (S := K) (M := Submonoid.powers π) (nonZeroDivisors R)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero) fun r hr => ?_).2 inferInstance
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero hr) hπ
    exact ⟨π ^ n, ⟨n, rfl⟩, hn.dvd⟩
  have hi : IsOpenImmersion (spMap (algebraMap R K)) := IsOpenImmersion.of_isLocalization π
  have hW : IsPullback (spMap (Algebra.TensorProduct.includeRight : C →ₐ[R] TensorProduct R K C).toRingHom)
      (spMap (algebraMap K (TensorProduct R K C))) (spMap (algebraMap R C)) (spMap (algebraMap R K)) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R K C)).flip
  have : Smooth (spMap (algebraMap R C)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr hC
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨Y, f, g, j, hg, hj, hgf, hp, h1, h2, h3, h4⟩ :=
    exists_glue_chart (spMap (algebraMap R K)) A.hom (spMap (algebraMap R C)) hW u hua
  refine ⟨⟨Over.mk f, Over.isoMk hj.isoPullback.symm hj.isoPullback_inv_snd, h1, h2,
    (inferInstance : QuasiCompact f)⟩, g, hg, hgf, ?_, fun y hy => h4 y ?_⟩
  · exact hp.trans (congrArg (u ≫ ·) hj.isoPullback_hom_fst.symm)
  · rintro ⟨t, ht⟩
    have ht' : spMap (algebraMap R K) t = IsLocalRing.closedPoint R := ht.trans hy
    have h5 : π ∈ (spMap (algebraMap R K) t).asIdeal := by
      rw [ht']; exact hπ.not_isUnit
    exact t.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (show algebraMap R K π ∈ t.asIdeal from h5)
      (IsLocalization.Away.algebraMap_isUnit π))

end GlobalTheory.ChartModel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSchemeModelOfAffineSmoothChartStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scheme_model_of_affine_smooth_chart : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)), Smooth A.hom → IsSeparated A.hom → QuasiCompact A.hom → ∀ (C : Type) [CommRing C] [Algebra R C], Algebra.Smooth R C → ∀ u : Sp (TensorProduct R K C) ⟶ A.left, IsOpenImmersion u → u ≫ A.hom = spMap (algebraMap K (TensorProduct R K C)) → ∃ (M : Model R A) (g : Sp C ⟶ M.Y.left), IsOpenImmersion g ∧ g ≫ M.Y.hom = spMap (algebraMap R C) ∧ spMap (Algebra.TensorProduct.includeRight : C →ₐ[R] TensorProduct R K C).toRingHom ≫ g = u ≫ M.j ∧ M.sp ⊆ Set.range g := by
  first | exact @GlobalTheory.ChartModel.exists_model_of_chart | exact GlobalTheory.ChartModel.exists_model_of_chart | (intros; apply GlobalTheory.ChartModel.exists_model_of_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoverModelIrreducibleSpecialFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoverModelIrreducibleSpecialFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.IrrSplit

section
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A : Over (Sp K)}

theorem isPullback_lift (M : Model R A) (U : M.Y.left.Opens)
    (hU : Set.range (pullback.fst M.Y.hom (spMap (algebraMap R K))) ⊆ Set.range U.ι) :
    IsPullback (IsOpenImmersion.lift U.ι (pullback.fst M.Y.hom (spMap (algebraMap R K))) hU)
      (pullback.snd M.Y.hom (spMap (algebraMap R K))) (U.ι ≫ M.Y.hom) (spMap (algebraMap R K)) := by
  refine ⟨⟨by rw [IsOpenImmersion.lift_fac_assoc, pullback.condition]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c => pullback.lift (c.fst ≫ U.ι) c.snd (by simpa using c.condition)) ?_ ?_ ?_⟩⟩
  · intro c
    rw [← cancel_mono U.ι, Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
  · intro c
    rw [pullback.lift_snd]
  · intro c m h₁ h₂
    apply pullback.hom_ext
    · rw [pullback.lift_fst, ← h₁, Category.assoc, IsOpenImmersion.lift_fac]
    · rw [pullback.lift_snd, h₂]

def restrictModel (M : Model R A) (U : M.Y.left.Opens) [QuasiCompact U.ι]
    (hU : Set.range (pullback.fst M.Y.hom (spMap (algebraMap R K))) ⊆ Set.range U.ι) : Model R A where
  Y := Over.mk (U.ι ≫ M.Y.hom)
  e := Over.isoMk (g := (Over.pullback (spMap (algebraMap R K))).obj M.Y) (isPullback_lift M U hU).isoPullback.symm
    ((isPullback_lift M U hU).isoPullback_inv_snd) ≪≫ M.e
  smooth := by have := M.smooth; show Smooth (U.ι ≫ M.Y.hom); infer_instance
  sep := by have := M.sep; show IsSeparated (U.ι ≫ M.Y.hom); infer_instance
  qc := by have := M.qc; show QuasiCompact (U.ι ≫ M.Y.hom); infer_instance

theorem restrictModel_j (M : Model R A) (U : M.Y.left.Opens) [QuasiCompact U.ι]
    (hU : Set.range (pullback.fst M.Y.hom (spMap (algebraMap R K))) ⊆ Set.range U.ι) :
    (restrictModel M U hU).j ≫ U.ι = M.j := by
  have h := (isPullback_lift M U hU).isoPullback_hom_fst
  show ((M.e.inv.left ≫ (isPullback_lift M U hU).isoPullback.hom) ≫
    pullback.fst (U.ι ≫ M.Y.hom) (spMap (algebraMap R K))) ≫ U.ι = _
  rw [Category.assoc, Category.assoc, reassoc_of% h, IsOpenImmersion.lift_fac]
  rfl

end

theorem exists_cover_irr : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) (M : Model R A), ∃ (n : ℕ) (N : Fin n → Model R A) (g : ∀ i, (N i).Y ⟶ M.Y), (∀ i, (N i).Irr ∧ IsOpenImmersion (g i).left ∧ (N i).j ≫ (g i).left = M.j) ∧ ∀ y ∈ M.sp, ∃ i, y ∈ Set.range (g i).left := by
  intro R K _ _ _ _ _ _ A M
  have := M.smooth
  have := M.qc
  let f : M.Y.left ⟶ Sp R := M.Y.hom
  let c : Sp R := IsLocalRing.closedPoint R
  have : IsLocallyNoetherian M.Y.left := LocallyOfFiniteType.isLocallyNoetherian f
  have hf : Smooth f := M.smooth
  have hf' : QuasiCompact f := M.qc
  have hs : Smooth (f.fiberToSpecResidueField c) :=
    inferInstanceAs (Smooth (pullback.snd f ((Sp R).fromSpecResidueField c)))
  obtain ⟨-, hn, hl⟩ := GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field
    ((Sp R).residueField c) (f.fiber c) (f.fiberToSpecResidueField c) hs
  have hn' : GlobalTheory.IsNormalScheme (f.fiber c) := hn
  have : CompactSpace (f.fiber c) := inferInstance
  have : IsNoetherian (f.fiber c) := {}
  have hfin : (irreducibleComponents (f.fiber c)).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hr : Set.range (f.fiberι c) = M.sp := f.range_fiberι c
  have hcl : Topology.IsClosedEmbedding (f.fiberι c) := by
    refine ⟨(f.fiberι c).isEmbedding, ?_⟩
    rw [f.range_fiberι]
    exact (IsLocalRing.isClosed_singleton_closedPoint R).preimage f.continuous
  have : Finite (irreducibleComponents (f.fiber c)) := hfin
  obtain ⟨n, ⟨σ⟩⟩ := Finite.exists_equiv_fin (irreducibleComponents (f.fiber c))
  let U : Fin n → M.Y.left.Opens := fun i => ⟨(f.fiberι c '' (σ.symm i).1ᶜ)ᶜ,
    (hcl.isClosedMap _ (GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents
      (σ.symm i).2).isClosed_compl).isOpen_compl⟩
  have hU : ∀ i, Set.range (pullback.fst M.Y.hom (spMap (algebraMap R K))) ⊆ Set.range (U i).ι := by
    rintro i _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    rintro ⟨z, -, hz⟩
    have h1 : pullback.fst M.Y.hom (spMap (algebraMap R K)) x ∈ M.sp := hr ▸ ⟨z, hz⟩
    have h2 : M.Y.hom (pullback.fst M.Y.hom (spMap (algebraMap R K)) x) =
        spMap (algebraMap R K) (pullback.snd M.Y.hom (spMap (algebraMap R K)) x) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    have h3 := h2.symm.trans h1
    generalize pullback.snd M.Y.hom (spMap (algebraMap R K)) x = p at h3
    have h4 : Ideal.comap (algebraMap R K) p.asIdeal = IsLocalRing.maximalIdeal R :=
      congrArg PrimeSpectrum.asIdeal h3
    have h5 : p.asIdeal = ⊥ := (Ideal.eq_bot_or_top (K := K) p.asIdeal).resolve_right p.isPrime.ne_top
    rw [h5, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)] at h4
    exact IsDiscreteValuationRing.not_a_field R h4.symm
  have hmem : ∀ i z, f.fiberι c z ∈ U i ↔ z ∈ (σ.symm i).1 := by
    intro i z
    show f.fiberι c z ∉ f.fiberι c '' (σ.symm i).1ᶜ ↔ _
    rw [hcl.injective.mem_set_image]
    simp
  refine ⟨n, fun i => restrictModel M (U i) (hU i), fun i => Over.homMk (U i).ι rfl,
    fun i => ⟨?_, inferInstanceAs (IsOpenImmersion (U i).ι), restrictModel_j M (U i) (hU i)⟩, ?_⟩
  · have hi : IsIrreducible (f.fiberι c '' (σ.symm i).1) :=
      (σ.symm i).2.1.image _ (f.fiberι c).continuous.continuousOn
    have he : (restrictModel M (U i) (hU i)).sp = (U i).ι ⁻¹' (f.fiberι c '' (σ.symm i).1) := by
      ext y
      constructor
      · intro hy
        have : (U i).ι y ∈ M.sp := hy
        rw [← hr] at this
        obtain ⟨z, hz⟩ := this
        refine ⟨z, (hmem i z).1 ?_, hz⟩
        rw [hz]; exact y.2
      · rintro ⟨z, -, hz⟩
        have : (U i).ι y ∈ M.sp := hr ▸ ⟨z, hz⟩
        exact this
    show IsIrreducible _
    rw [he]
    refine ⟨?_, hi.2.preimage (U i).ι.isOpenEmbedding⟩
    obtain ⟨z, hz⟩ := (σ.symm i).2.1.1
    exact ⟨⟨_, (hmem i z).2 hz⟩, z, hz, rfl⟩
  · intro y hy
    rw [← hr] at hy
    obtain ⟨z, rfl⟩ := hy
    refine ⟨σ ⟨_, irreducibleComponent_mem_irreducibleComponents z⟩, ⟨_, (hmem _ z).2 ?_⟩, rfl⟩
    rw [Equiv.symm_apply_apply]
    exact mem_irreducibleComponent

end GlobalTheory.SS.IrrSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoverModelIrreducibleSpecialFibreStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cover_model_irreducible_specialFibre : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) (M : Model R A), ∃ (n : ℕ) (N : Fin n → Model R A) (g : ∀ i, (N i).Y ⟶ M.Y), (∀ i, (N i).Irr ∧ IsOpenImmersion (g i).left ∧ (N i).j ≫ (g i).left = M.j) ∧ ∀ y ∈ M.sp, ∃ i, y ∈ Set.range (g i).left := by
  first | exact @GlobalTheory.SS.IrrSplit.exists_cover_irr | exact GlobalTheory.SS.IrrSplit.exists_cover_irr | (intros; apply GlobalTheory.SS.IrrSplit.exists_cover_irr <;> assumption)
end
end
