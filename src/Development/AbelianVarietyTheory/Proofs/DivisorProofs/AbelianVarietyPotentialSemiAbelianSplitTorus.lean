module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianVarietyPotentialSemiAbelianModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLocalIntegralPointsMemOpenSubgroupDefi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFourierRealisesWeylElement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteDvrTorusExtensionSpecialFibreStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyPotentialSemiAbelianSplitTorus
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GroupSchemeModelFiniteRingExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GroupSchemeModelFiniteRingExtension
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.SS

theorem baseChange_iso_tower (K K' V' V'' L : Type) [CommRing K] [CommRing K'] [CommRing V'] [CommRing V''] [CommRing L]
    [Algebra K K'] [Algebra V' K'] [Algebra V' V''] [Algebra V'' L] [Algebra K L] (j : K' →+* L)
    (t : j.comp (algebraMap V' K') = (algebraMap V'' L).comp (algebraMap V' V''))
    (e₂ : algebraMap K L = j.comp (algebraMap K K'))
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A] (G : Over (Spec (CommRingCat.of V'))) [GrpObj G]
    (e : baseChange V' K' G ≅ baseChange K K' A) (he : IsMonHom e.hom) :
    ∃ e : baseChange V'' L (baseChange V' V'' G) ≅ baseChange K L A, IsMonHom e.hom := by
  have s₁ : specMap V'' L ≫ specMap V' V'' = spMap j ≫ specMap V' K' := by
    show spMap (algebraMap V'' L) ≫ spMap (algebraMap V' V'') = spMap j ≫ spMap (algebraMap V' K')
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, t]
  have s₂ : spMap j ≫ 𝟙 _ ≫ specMap K K' = specMap K L := by
    show spMap j ≫ 𝟙 _ ≫ spMap (algebraMap K K') = spMap (algebraMap K L)
    rw [Category.id_comp, e₂, ← Spec.map_comp]; rfl
  have p₁ := ((isGrpPullback_pullback (baseChange V' V'' G) (specMap V'' L)).comp
    (isGrpPullback_pullback G (specMap V' V''))).congr s₁ rfl
  have p₂ := (isGrpPullback_pullback (baseChange V' K' G) (spMap j)).comp
    (isGrpPullback_pullback G (specMap V' K'))
  have p₃ := ((isGrpPullback_pullback (baseChange V' K' G) (spMap j)).comp
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback A (specMap K K')))).congr s₂ rfl
  obtain ⟨i₁, hi₁, -⟩ := grpPullback_iso p₁ p₂
  obtain ⟨i₂, hi₂, -⟩ := grpPullback_iso p₃ (isGrpPullback_pullback A (specMap K L))
  refine ⟨i₁ ≪≫ i₂, ?_⟩
  rw [Iso.trans_hom]; infer_instance

theorem exists_finite_frac (V' K' V'' L : Type) [CommRing V'] [IsDomain V'] [Field K'] [Algebra V' K'] [IsFractionRing V' K']
    [CommRing V''] [IsDomain V''] [Algebra V' V''] [Field L] [Algebra V'' L] [IsFractionRing V'' L]
    (hf : Module.Finite V' V'') (hi : Function.Injective (algebraMap V' V'')) :
    ∃ j : K' →+* L, j.Finite ∧ j.comp (algebraMap V' K') = (algebraMap V'' L).comp (algebraMap V' V'') := by
  have : FaithfulSMul V' V'' := (faithfulSMul_iff_algebraMap_injective V' V'').2 hi
  have hinj : Function.Injective ((algebraMap V'' L).comp (algebraMap V' V'')) :=
    (IsFractionRing.injective V'' L).comp hi
  obtain ⟨j, t⟩ : ∃ j : K' →+* L, j.comp (algebraMap V' K') = (algebraMap V'' L).comp (algebraMap V' V'') :=
    ⟨IsFractionRing.lift (K := K') hinj, RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x⟩
  let a₁ : Algebra V' L := ((algebraMap V'' L).comp (algebraMap V' V'')).toAlgebra
  let a₂ : Algebra K' L := j.toAlgebra
  have : IsScalarTower V' V'' L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower V' K' L := IsScalarTower.of_algebraMap_eq' t.symm
  have : IsLocalization (Algebra.algebraMapSubmonoid V'' (nonZeroDivisors V')) L := inferInstance
  have h : Module.Finite K' L := Module.Finite.of_isLocalization V' V'' (nonZeroDivisors V')
  exact ⟨j, h, t⟩

theorem model_finite_ext : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A] (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (V' : Type) [CommRing V'] [IsDomain V'] [Algebra V V'] [Algebra V' K'] [IsFractionRing V' K'], (algebraMap V' K').comp (algebraMap V V') = (algebraMap K K').comp (algebraMap V K) → ∀ (G : Over (Spec (CommRingCat.of V'))) [GrpObj G], (∃ e : baseChange V' K' G ≅ baseChange K K' A, IsMonHom e.hom) → ∀ (V'' : Type) [CommRing V''] [IsDomain V''] [Algebra V' V''], Module.Finite V' V'' → Function.Injective (algebraMap V' V'') → ∃ (_ : Algebra K (FractionRing V'')) (_ : FiniteDimensional K (FractionRing V'')), (algebraMap V'' (FractionRing V'')).comp ((algebraMap V' V'').comp (algebraMap V V')) = (algebraMap K (FractionRing V'')).comp (algebraMap V K) ∧ ∃ e : baseChange V'' (FractionRing V'') (baseChange V' V'' G) ≅ baseChange K (FractionRing V'') A, IsMonHom e.hom := by
  intro V _ _ _ K _ _ _ A _ K' _ _ hK V' _ _ _ _ _ hc G _ ⟨e, he⟩ V'' _ _ _ hf hi
  obtain ⟨j, hj, t⟩ := exists_finite_frac V' K' V'' (FractionRing V'') hf hi
  let aK : Algebra K (FractionRing V'') := (j.comp (algebraMap K K')).toAlgebra
  have e₂ : algebraMap K (FractionRing V'') = j.comp (algebraMap K K') := rfl
  refine ⟨aK, hj.comp (RingHom.finite_algebraMap.2 hK), ?_, baseChange_iso_tower K K' V' V'' _ j t e₂ A G e he⟩
  rw [e₂, ← RingHom.comp_assoc, ← t, RingHom.comp_assoc, hc, RingHom.comp_assoc]

end GlobalTheory.SS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GroupSchemeModelFiniteRingExtensionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupScheme_model_finite_ring_extension : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A] (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (V' : Type) [CommRing V'] [IsDomain V'] [Algebra V V'] [Algebra V' K'] [IsFractionRing V' K'], (algebraMap V' K').comp (algebraMap V V') = (algebraMap K K').comp (algebraMap V K) → ∀ (G : Over (Spec (CommRingCat.of V'))) [GrpObj G], (∃ e : baseChange V' K' G ≅ baseChange K K' A, IsMonHom e.hom) → ∀ (V'' : Type) [CommRing V''] [IsDomain V''] [Algebra V' V''], Module.Finite V' V'' → Function.Injective (algebraMap V' V'') → ∃ (_ : Algebra K (FractionRing V'')) (_ : FiniteDimensional K (FractionRing V'')), (algebraMap V'' (FractionRing V'')).comp ((algebraMap V' V'').comp (algebraMap V V')) = (algebraMap K (FractionRing V'')).comp (algebraMap V K) ∧ ∃ e : baseChange V'' (FractionRing V'') (baseChange V' V'' G) ≅ baseChange K (FractionRing V'') A, IsMonHom e.hom := by
  first | exact @GlobalTheory.SS.model_finite_ext | exact GlobalTheory.SS.model_finite_ext | (intros; apply GlobalTheory.SS.model_finite_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableReductionZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableOfPotentialSemiAbelianModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianTorusExtensionOfPotentialModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianTorusExtensionOfPotentialModel
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem exists_semiAbelian_model_torusExtension_of_potModel : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (K : Type) [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G) → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : IsAdicComplete (IsLocalRing.maximalIdeal V') V') (_ : Algebra V V') (_ : Algebra V' K') (_ : IsFractionRing V' K'), Module.Finite V V' ∧ Function.Injective (algebraMap V V') ∧ (algebraMap V' K').comp (algebraMap V V') = (algebraMap K K').comp (algebraMap V K) ∧ ∃ (G : Over (Spec (CommRingCat.of V'))) (_ : GrpObj G), IsSemiAbelian G ∧ (∃ e : baseChange V' K' G ≅ baseChange K K' A, IsMonHom e.hom) ∧ Nonempty (TorusExtension (specialFibre V' G)) := by
  intro V _ _ _ _ K _ _ _ _ A _ hP
  obtain ⟨W, L, _, _, _, _, _, _, _, _, e, hfin, -, hW, G, _, hmod, hG⟩ := hP
  have hinj : Function.Injective (algebraMap V W) := by
    have h : Function.Injective ((algebraMap W L).comp (algebraMap V W)) := by
      rw [e]; exact (algebraMap K L).injective.comp (IsFractionRing.injective V K)
    exact Function.Injective.of_comp (f := algebraMap W L) h
  haveI hKL : FiniteDimensional K L := by
    letI : Algebra V L := ((algebraMap W L).comp (algebraMap V W)).toAlgebra
    haveI : IsScalarTower V W L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq' e
    haveI : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).2 hinj
    exact Module.Finite.of_isLocalization V W (nonZeroDivisors V)
  obtain ⟨W', _, _, _, hW', _, hfin', hinj', -, hG', hT⟩ := GlobalTheory.T.exists_finite_dvr_torusExtension_specialFibre' W G hG
  obtain ⟨_, hK', e', hmod'⟩ := GlobalTheory.T.groupScheme_model_finite_ring_extension V K A L W e G hmod W' hfin' hinj'
  letI : Algebra V W' := ((algebraMap W W').comp (algebraMap V W)).toAlgebra
  haveI : IsScalarTower V W W' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨FractionRing W', inferInstance, inferInstance, hK', W', inferInstance, inferInstance, inferInstance, hW',
    inferInstance, inferInstance, inferInstance, Module.Finite.trans W W', hinj'.comp hinj, e',
    baseChange W W' G, inferInstance, hG', hmod', hT⟩

end GlobalTheory.SS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianTorusExtensionOfPotentialModelStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelian_torusExtension_of_potentialModel : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (K : Type) [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G) → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : IsAdicComplete (IsLocalRing.maximalIdeal V') V') (_ : Algebra V V') (_ : Algebra V' K') (_ : IsFractionRing V' K'), Module.Finite V V' ∧ Function.Injective (algebraMap V V') ∧ (algebraMap V' K').comp (algebraMap V V') = (algebraMap K K').comp (algebraMap V K) ∧ ∃ (G : Over (Spec (CommRingCat.of V'))) (_ : GrpObj G), IsSemiAbelian G ∧ (∃ e : baseChange V' K' G ≅ baseChange K K' A, IsMonHom e.hom) ∧ Nonempty (TorusExtension (specialFibre V' G)) := by
  first | exact @GlobalTheory.SS.exists_semiAbelian_model_torusExtension_of_potModel | exact GlobalTheory.SS.exists_semiAbelian_model_torusExtension_of_potModel | (intros; apply GlobalTheory.SS.exists_semiAbelian_model_torusExtension_of_potModel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyTorusExtOfSplit
universe u

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SplitExtTorus

theorem isTorus_splitTorus (k : Type u) [Field k] (X : Type u) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] : IsTorus (splitTorus (Spec (CommRingCat.of k)) X) :=
  ⟨GlobalTheory.Diag.isCommMonObj _ X, inferInstance, inferInstance,
    ⟨k, inferInstance, inferInstance, X, inferInstance, inferInstance, inferInstance,
      GlobalTheory.Diag.baseChangeIso _ X, GlobalTheory.Diag.baseChangeIso_isMonHom _ X⟩⟩

def torusExtOfSplit {k : Type u} [Field k] {G : Over (Spec (CommRingCat.of k))} [GrpObj G]
    (E : TorusExtension G) : TorusExt G :=
  letI := E.addCommGroup
  letI := E.free
  letI := E.finite
  letI := E.grpB
  { B := E.B
    isAbelian := E.isAbelian
    q := E.q
    q_hom := E.q_hom
    q_flat := E.q_flat
    q_surjective := E.q_surjective
    q_quasiCompact := E.q_quasiCompact
    T₀ := splitTorus (Spec (CommRingCat.of k)) E.X
    isTorus := isTorus_splitTorus k E.X
    i := E.i
    i_hom := E.i_hom
    isKernel := E.isKernel }

theorem nonempty_torusExt_of_split : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G], Nonempty (TorusExtension G) → Nonempty (TorusExt G) :=
  fun _ _ _ _ h => h.map torusExtOfSplit

end GlobalTheory.SplitExtTorus
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableOfPotentialSemiAbelianModel
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem semistable_of_potModel_semiAbelian : (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (K : Type) [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A → PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G)) → SemistableReductionZero ∧ SemistableCompleteSplit := by
  intro h
  refine ⟨?_, ?_⟩
  · intro V _ _ _ _ K _ _ _ _ A _ hA
    obtain ⟨K', i1, i2, i3, V', i4, i5, i6, i7, i8, i9, i10, h1, h2, h3, G, i11, hG, he, hT⟩ :=
      GlobalTheory.T.exists_semiAbelian_torusExtension_of_potentialModel V K A (h V K A hA)
    exact ⟨K', i1, i2, i3, V', i4, i5, i6, i8, i9, i10, h1, h2, h3, G, i11,
      hG.comm, hG.smooth, hG.separated, hG.quasiCompact, he, GlobalTheory.SplitExtTorus.nonempty_torusExt_of_split _ _ hT⟩
  · intro V _ _ _ _ K _ _ _ _ A _ hA
    obtain ⟨K', i1, i2, i3, V', i4, i5, i6, i7, i8, i9, i10, h1, h2, h3, G, i11, hG, he, hT⟩ :=
      GlobalTheory.T.exists_semiAbelian_torusExtension_of_potentialModel V K A (h V K A hA)
    exact ⟨K', i1, i2, i3, V', i4, i5, i6, i7, i8, i9, i10, inferInstance, h3, G, i11, hG, he, hT⟩

end GlobalTheory.SS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableOfPotentialSemiAbelianModelStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistable_of_potential_semiAbelian_model : (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (K : Type) [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A → PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G)) → SemistableReductionZero ∧ SemistableCompleteSplit := by
  first | exact @GlobalTheory.SS.semistable_of_potModel_semiAbelian | exact GlobalTheory.SS.semistable_of_potModel_semiAbelian | (intros; apply GlobalTheory.SS.semistable_of_potModel_semiAbelian <;> assumption)
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem semistableReduction_zero : SemistableReductionZero := (GlobalTheory.T.semistable_of_potential_semiAbelian_model GlobalTheory.T.abelianVariety_potential_semiAbelian_model).1

end GlobalTheory.SS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyPotentialSemiAbelianSplitTorus
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory.SS

theorem potModel_semiAbelian_torusExtension : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G ∧ Nonempty (TorusExtension (GlobalTheory.SS.spFibre G))) := by
  intro V K _ _ _ _ _ _ _ _ A _ hA
  obtain ⟨K', _, _, _, V', _, _, _, _, _, _, hfin, hinj, hcomm, G, _, hc, hsm, hsep, hqc, he, hT⟩ :=
    GlobalTheory.SS.semistableReduction_zero V K A hA
  obtain ⟨hloc, hcpl⟩ := GlobalTheory.isLocalHom_and_isAdicComplete_of_finite_dvr V V' hfin hinj
  haveI := hcpl
  have hA' : IsAbelianScheme (baseChange K K' A) := Out.TLinPf.isAb_pullback _ A hA
  have hG : IsSemiAbelian G :=
    GlobalTheory.SS.isSemiAbelian_of_abelian_generic_of_torusExt V' K' (baseChange K K' A) hA' G hc hsm hsep hqc he hT
  obtain ⟨V'', _, _, _, hcpl', _, hfin', hinj', hloc', hG', hT'⟩ :=
    GlobalTheory.exists_finite_dvr_torusExtension_specialFibre V' G hG
  obtain ⟨alg, hfd, hcomm', he'⟩ := GlobalTheory.SS.model_finite_ext V K A K' V' hcomm G he V'' hfin' hinj'
  let : Algebra V V'' := ((algebraMap V' V'').comp (algebraMap V V')).toAlgebra
  have : IsScalarTower V V' V'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hfinV : Module.Finite V V'' := Module.Finite.trans V' V''
  have hlocV : IsLocalHom (algebraMap V V'') := by
    haveI := hloc; haveI := hloc'
    exact (inferInstance : IsLocalHom ((algebraMap V' V'').comp (algebraMap V V')))
  exact ⟨V'', FractionRing V'', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, alg, inferInstance, hcomm', hfinV, hlocV, hcpl', baseChange V' V'' G, inferInstance, he', hG', hT'⟩

end GlobalTheory.SS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyPotentialSemiAbelianSplitTorusStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_potential_semiAbelian_splitTorus : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G ∧ Nonempty (TorusExtension (GlobalTheory.SS.spFibre G))) := by
  first | exact @GlobalTheory.SS.potModel_semiAbelian_torusExtension | exact GlobalTheory.SS.potModel_semiAbelian_torusExtension | (intros; apply GlobalTheory.SS.potModel_semiAbelian_torusExtension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicEisensteinSeriesRationalPointsPermuteTe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivReps
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightFunctionScalingParabolic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightFunctionCompactLevelContinuous
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightFunctionCompactLevelContinuous
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)

noncomputable section

open Pointwise

namespace GlobalTheory.ResLine.HtCont

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

omit [NumberField E] in
theorem inv_eigen {x : Matrix (Fin n) (Fin 1) E} {p : GAd σ J} {l : (AF F ⊗[F] E)ˣ}
    (hp : (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x) :
    (matHom _ σ J p⁻¹).1 * adMat F x = (l⁻¹).1 • adMat F x := by
  have h1 : (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have h2 : l.1 • ((matHom _ σ J p⁻¹).1 * adMat F x) = adMat F x := by
    rw [← Matrix.mul_smul, ← hp, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  calc _ = ((l⁻¹).1 * l.1) • ((matHom _ σ J p⁻¹).1 * adMat F x) := by rw [Units.inv_mul, one_smul]
    _ = _ := by rw [← smul_smul, h2]

omit [NumberField F] in
theorem exists_col_ne {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hW : IsWittFrame σ J X Y) :
    ∃ i, col X i 0 ≠ 0 := by
  by_contra hc
  push Not at hc
  have h0 : ∀ j, X j 0 = 0 := fun j => hc j
  have := congrFun (congrFun hW.xy 0) 0
  simp [Matrix.mul_apply, Formalism.UG.cT, h0] at this

set_option linter.style.haveILetI false in
theorem isCompact_and_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), Data σ J X Y L a h →
    IsCompact (levelAll σ J L a : Set (GAd σ J)) ∧ Continuous h := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hS
  obtain ⟨hCM, -, -, hW, hA, hI1, hI2⟩ := hS
  let _ : Submodule.IsFullLattice E L := hA.lat
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  have hK : IsCompact (levelAll σ J L a : Set (GAd σ J)) := GlobalTheory.Doubling.isCompact_levelAll hCM J L a
  refine ⟨hK, ?_⟩
  obtain ⟨i, hi⟩ := exists_col_ne hW
  set x := col X with hx
  have hm : Continuous fun g : GAd σ J => (matHom _ σ J g).1 :=
    Units.continuous_val.comp (isEmbedding_matHom _ σ J).continuous
  let Λ : GAd σ J → AF F ⊗[F] E := fun g =>
    ((matHom _ σ J g).1 * adMat F x) i 0 * inclR (F := F) (AF F) (x i 0)⁻¹
  have hΛ : Continuous Λ := ((hm.matrix_mul continuous_const).matrix_elem i 0).mul continuous_const
  have key : ∀ p (l : (AF F ⊗[F] E)ˣ), (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x → l.1 = Λ p := by
    intro p l hl
    have e := congrFun (congrFun hl i) 0
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply] at e
    simp only [Λ, e, mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, mul_one]
  let P : Set (GAd σ J) := {p | (matHom _ σ J p).1 * adMat F x = Λ p • adMat F x ∧ Λ p * Λ p⁻¹ = 1}
  have memP : ∀ p, (∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x) → p ∈ P := by
    rintro p ⟨l, hl⟩
    have e1 := key p l hl
    have e2 := key p⁻¹ l⁻¹ (inv_eigen hl)
    exact ⟨by rw [← e1]; exact hl, by rw [← e1, ← e2, Units.mul_inv]⟩
  have hPc : IsClosed P :=
    (isClosed_eq (hm.matrix_mul continuous_const) (hΛ.smul continuous_const)).inter
      (isClosed_eq (hΛ.mul (hΛ.comp continuous_inv)) continuous_const)
  let u : P → (AF F ⊗[F] E)ˣ := fun p => ⟨Λ p, Λ p.1⁻¹, p.2.2, by rw [mul_comm]; exact p.2.2⟩
  have hu : Continuous u := Units.continuous_iff.2
    ⟨hΛ.comp continuous_subtype_val, (hΛ.comp continuous_inv).comp continuous_subtype_val⟩
  let f : P → ℝ := fun p => (absE F E (u p) : ℝ)
  have hf : Continuous f := NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp hu)
  have hval : ∀ p : P, ∀ k ∈ levelAll σ J L a, h (p.1 * k) = f p := fun p k hk =>
    hI2 p.1 (u p) p.2.1 k hk
  rw [continuous_iff_isClosed]
  intro s hs
  have hpre : h ⁻¹' s = (Subtype.val '' (f ⁻¹' s)) * (levelAll σ J L a : Set (GAd σ J)) := by
    ext g; constructor
    · intro hg
      obtain ⟨p, l, hl, k, hk, rfl⟩ := hI1 g
      have hp : p ∈ P := memP p ⟨l, hl⟩
      refine ⟨p, ⟨⟨p, hp⟩, ?_, rfl⟩, k, hk, rfl⟩
      show f ⟨p, hp⟩ ∈ s
      rw [← hval ⟨p, hp⟩ k hk]; exact hg
    · rintro ⟨_, ⟨p, hp, rfl⟩, k, hk, rfl⟩
      show h (p.1 * k) ∈ s
      rw [hval p k hk]; exact hp
  rw [hpre]
  exact (hPc.isClosedEmbedding_subtypeVal.isClosedMap _ (hs.preimage hf)).mul_right_of_isCompact hK

end GlobalTheory.ResLine.HtCont

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightFunctionCompactLevelContinuousStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_function_compact_level_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), Data σ J X Y L a h → IsCompact (levelAll σ J L a : Set (GAd σ J)) ∧ Continuous h := by
  first | exact @GlobalTheory.ResLine.HtCont.isCompact_and_continuous | exact GlobalTheory.ResLine.HtCont.isCompact_and_continuous | (intros; apply GlobalTheory.ResLine.HtCont.isCompact_and_continuous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightFunctionScalingParabolic
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem Scales.mul_scales {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {x : Matrix (Fin n) (Fin 1) E}
    {a b : GAd σ J} {l l' : (AF F ⊗[F] E)ˣ} (e : Scales σ J x a l) (e' : Scales σ J x b l') :
    Scales σ J x (a * b) (l * l') := by
  unfold Scales at *
  rw [map_mul, Units.val_mul, Matrix.mul_assoc, e', Matrix.mul_smul, e, smul_smul, Units.val_mul, mul_comm]

theorem iwasawaHeight_isHt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), Data σ J X Y L a h → IsHt (levelAll σ J L a) h ∧ ∀ p l, Scales σ J (col X) p l → ∀ g, h (p * g) = absE F E l * h g := by
  intro F E _ _ _ _ _ σ n J r X Y L a h D
  have law : ∀ p l, Scales σ J (col X) p l → ∀ g, h (p * g) = absE F E l * h g := by
    intro p l e g
    obtain ⟨p', l', e', k, hk, rfl⟩ := D.iwa g
    rw [← mul_assoc, D.ht _ _ (e.mul_scales e') k hk, D.ht _ _ e' k hk, map_mul, NNReal.coe_mul]
  refine ⟨⟨fun g => ?_, (GlobalTheory.T.height_function_compact_level_continuous F E σ n J r X Y L a h D).2, fun k hk => ?_, fun g => ?_⟩, law⟩
  · obtain ⟨p, l, e, k, hk, rfl⟩ := D.iwa g
    rw [D.ht _ _ e k hk]
    have h1 : absE F E l * absE F E l⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one h1))
  · have := D.ht 1 1 (by simp [Scales]) k hk
    simpa using this
  · obtain ⟨p, l, e, k, hk, rfl⟩ := D.iwa g
    refine ⟨k, hk, fun x => ?_⟩
    rw [mul_assoc, law p l e, D.ht _ _ e k hk]

end GlobalTheory.ResLine
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightFunctionScalingParabolicStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_function_scaling_parabolic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), Data σ J X Y L a h → IsHt (levelAll σ J L a) h ∧ ∀ p l, Scales σ J (col X) p l → ∀ g, h (p * g) = absE F E l * h g := by
  first | exact @GlobalTheory.ResLine.iwasawaHeight_isHt | exact GlobalTheory.ResLine.iwasawaHeight_isHt | (intros; apply GlobalTheory.ResLine.iwasawaHeight_isHt <;> assumption)
end
end

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResLine

theorem exists_equiv_reps {G : Type} [Group G] (Γ Λ : Subgroup G) (T : Set Γ)
    (hT : ∀ γ : Γ, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : Γ) : G) ∈ Λ) (γ : Γ) :
    ∃ π : T ≃ T, ∀ i : T, ((i.1 * γ * (π i).1⁻¹ : Γ) : G) ∈ Λ := by
  choose ρ hρ hu using hT
  have key : ∀ (a b : Γ), a * b = 1 → ∀ i : T, ρ (ρ (i.1 * a) * b) = i.1 := by
    intro a b hab i
    symm
    refine hu _ _ ⟨i.2, ?_⟩
    have := Λ.inv_mem (hρ (i.1 * a)).2
    have e : ρ (i.1 * a) * b * i.1⁻¹ = (i.1 * a * (ρ (i.1 * a))⁻¹)⁻¹ := by
      rw [eq_inv_of_mul_eq_one_right hab]; group
    rw [e, Subgroup.coe_inv]
    exact this
  exact ⟨⟨fun i => ⟨ρ (i.1 * γ), (hρ _).1⟩, fun i => ⟨ρ (i.1 * γ⁻¹), (hρ _).1⟩,
    fun i => Subtype.ext (key γ γ⁻¹ (mul_inv_cancel _) i), fun i => Subtype.ext (key γ⁻¹ γ (inv_mul_cancel _) i)⟩,
    fun i => (hρ _).2⟩

theorem reps_perm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), Data σ J X Y L a h → ∀ T, IsReps σ J (col X) T → (∀ γ ∈ ratPts σ J, ∃ π : T ≃ T, ∀ (i : T) g, h (i.1.1 * (γ * g)) = h ((π i).1.1 * g)) ∧ (∃ i : T, ∀ g, h (i.1.1 * g) = h g) ∧ (∀ γ ∈ (ratPts σ J ⊓ lineGrp σ J (col X)), ∀ g, h (γ * g) = h g) ∧ ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : ratPts σ J) : GAd σ J) ∈ (ratPts σ J ⊓ lineGrp σ J (col X)) := by
  intro F E _ _ _ _ _ σ n J r X Y L a h D T hT
  have h3 : ∀ γ ∈ (ratPts σ J ⊓ lineGrp σ J (col X)), ∀ g, h (γ * g) = h g := by
    rintro γ ⟨hγ, l, hl⟩ g
    rw [(GlobalTheory.T.height_function_scaling_parabolic F E σ n J r X Y L a h D).2 γ l hl g,
      (GlobalTheory.T.levi_normalizes_unipotent_radical_bis F E σ n J r X Y D.cm D.herm D.witt).2.2.2.2.2 γ hγ l hl]
    simp
  have h4 : ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : ratPts σ J) : GAd σ J) ∈ (ratPts σ J ⊓ lineGrp σ J (col X)) := by
    intro γ
    obtain ⟨t, ⟨ht, hl⟩, hu⟩ := hT γ
    exact ⟨t, ⟨ht, (γ * t⁻¹).2, hl⟩, fun s hs => hu s ⟨hs.1, hs.2.2⟩⟩
  refine ⟨fun γ hγ => ?_, ?_, h3, h4⟩
  · obtain ⟨π, hπ⟩ := exists_equiv_reps _ _ T h4 ⟨γ, hγ⟩
    refine ⟨π, fun i g => ?_⟩
    rw [← h3 _ (hπ i) ((π i).1.1 * g)]
    congr 1
    simp [mul_assoc]
  · obtain ⟨t, ⟨ht, hl⟩, -⟩ := h4 1
    refine ⟨⟨t, ht⟩, fun g => ?_⟩
    rw [← h3 _ hl (t.1 * g)]
    congr 1
    simp

end GlobalTheory.ResLine
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicEisensteinSeriesRationalPointsPermuteTe
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResidueEisenstein

theorem reps_perm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ T, IsRepsJ σ J X T → (∀ γ ∈ ratPts σ J, ∃ π : T ≃ T, ∀ (i : T) g, h (i.1.1 * (γ * g)) = h ((π i).1.1 * g)) ∧ (∃ i : T, ∀ g, h (i.1.1 * g) = h g) ∧ (∀ γ ∈ (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤), ∀ g, h (γ * g) = h g) ∧ ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : ratPts σ J) : GAd σ J) ∈ (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤) := by
  intro F E _ _ _ _ _ σ n J r X Y L a h D T hT
  have hrat := (GlobalTheory.T.wittFrameLevi_normalizes_radical_properties F E σ n J r X Y D.cm D.herm D.witt).2.2.2.2.1
  have h3 : ∀ γ ∈ (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤), ∀ g, h (γ * g) = h g := by
    rintro γ ⟨hγ, B, -, hB⟩ g
    obtain ⟨p, β, hp, k, hk, rfl⟩ := D.iwa g
    have hs : ScalesBy σ J X (γ * p) (B * β) := by
      unfold ScalesBy at hp ⊢
      rw [map_mul, Units.val_mul, Matrix.mul_assoc, hp, ← Matrix.mul_assoc, hB, Matrix.mul_assoc, Units.val_mul]
    rw [← mul_assoc, D.ht _ _ hs k hk, D.ht _ _ hp k hk, map_mul, map_mul, hrat γ hγ B hB, one_mul]
  have h4 : ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : ratPts σ J) : GAd σ J) ∈ (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤) := by
    intro γ
    obtain ⟨t, ⟨ht, β, hβ⟩, hu⟩ := hT γ
    exact ⟨t, ⟨ht, (γ * t⁻¹).2, β, trivial, hβ⟩, fun s hs => hu s ⟨hs.1, let ⟨β, _, e⟩ := hs.2.2; ⟨β, e⟩⟩⟩
  refine ⟨fun γ hγ => ?_, ?_, h3, h4⟩
  · obtain ⟨π, hπ⟩ := exists_equiv_reps _ _ T h4 ⟨γ, hγ⟩
    refine ⟨π, fun i g => ?_⟩
    rw [← h3 _ (hπ i) ((π i).1.1 * g)]
    congr 1
    simp [mul_assoc]
  · obtain ⟨t, ⟨ht, hl⟩, -⟩ := h4 1
    refine ⟨⟨t, ht⟩, fun g => ?_⟩
    rw [← h3 _ hl (t.1 * g)]
    congr 1
    simp

end GlobalTheory.ResidueEisenstein
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicEisensteinSeriesRationalPointsPermuteTeStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicEisensteinSeries_rationalPoints_permute_terms : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ T, IsRepsJ σ J X T → (∀ γ ∈ ratPts σ J, ∃ π : T ≃ T, ∀ (i : T) g, h (i.1.1 * (γ * g)) = h ((π i).1.1 * g)) ∧ (∃ i : T, ∀ g, h (i.1.1 * g) = h g) ∧ (∀ γ ∈ (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤), ∀ g, h (γ * g) = h g) ∧ ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : ratPts σ J) : GAd σ J) ∈ (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤) := by
  first | exact @GlobalTheory.ResidueEisenstein.reps_perm | exact GlobalTheory.ResidueEisenstein.reps_perm | (intros; apply GlobalTheory.ResidueEisenstein.reps_perm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalProductActsOfAdelicProductActsFirst
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalProductActsOfAdelicProductActsFirst
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BoxAct

theorem tens_boxFun {F : Type} [Field F] [NumberField F] {R κ κ' : Type} (ev : AF F → R)
    (φ₁ : (κ → R) → ℂ) (φ₂ : (κ' → R) → ℂ) (r₁ : (κ → AF F) → ℂ) (r₂ : (κ' → AF F) → ℂ) :
    tens ev (boxFun φ₁ φ₂) (boxFun r₁ r₂) = boxFun (tens ev φ₁ r₁) (tens ev φ₂ r₂) := by
  funext x
  simp only [tens, boxFun, Function.comp_def]
  ring

theorem boxFun_acts : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ κ' : Type) [Fintype κ] [Fintype κ']
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (Td : ((κ ⊕ κ' → AF F) → ℂ) → (κ ⊕ κ' → AF F) → ℂ),
    (∀ Φ₁ ∈ schA F κ, ∀ Φ₂ ∈ schA F κ', Td (boxFun Φ₁ Φ₂) = boxFun (T Φ₁) Φ₂) →
    ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ' → Fv F v), ∀ (φ₁' : (κ → Fv F v) → ℂ) (Φ' : (κ ⊕ κ' → Fv F v) → ℂ),
      Acts (evFin F v) T φ₁ φ₁' → Acts (evFin F v) Td (boxFun φ₁ φ₂) Φ' → Φ' = boxFun φ₁' φ₂ := by
  intro F _ _ v κ κ' _ _ T Td hT φ₁ hφ₁ φ₂ hφ₂ φ₁' Φ' h₁ hd
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  obtain ⟨R', hR0', hR'⟩ := GlobalTheory.RestWitness.exists_rest κ' v
  have r₁ := hR φ₁ hφ₁
  have r₂ := hR' φ₂ hφ₂
  have hRest : Rest (evFin F v) (boxFun φ₁ φ₂) (boxFun R R') := by
    refine ⟨fun x z hz => ?_, ?_⟩
    · have hz₁ : At (evFin F v) (z ∘ Sum.inl) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inl i)
      have hz₂ : At (evFin F v) (z ∘ Sum.inr) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inr i)
      have e₁ := r₁.1 (x ∘ Sum.inl) (z ∘ Sum.inl) hz₁
      have e₂ := r₂.1 (x ∘ Sum.inr) (z ∘ Sum.inr) hz₂
      simp only [boxFun]
      have a₁ : (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl := rfl
      have a₂ : (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr := rfl
      rw [a₁, a₂, e₁, e₂]
    · rw [tens_boxFun]
      exact GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ' _ r₁.2 _ r₂.2
  have key : tens (evFin F v) Φ' (boxFun R R') = tens (evFin F v) (boxFun φ₁' φ₂) (boxFun R R') := by
    rw [← hd _ hRest, tens_boxFun, hT _ r₁.2 _ r₂.2, h₁ R r₁, tens_boxFun]
  funext y
  let z : κ ⊕ κ' → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
  have hz : ∀ (ι : Type) (w : ι → κ ⊕ κ'), At (evFin F v) (z ∘ w) := by
    intro ι w u hu
    funext i
    exact GlobalTheory.LatVac.at_liftV v (y (w i)) u hu
  have hRz : boxFun R R' z = R 0 * R' 0 := by
    have e₁ := (hR φ₁ hφ₁).1 0 (z ∘ Sum.inl) (hz κ Sum.inl)
    have e₂ := (hR' φ₂ hφ₂).1 0 (z ∘ Sum.inr) (hz κ' Sum.inr)
    rw [zero_add] at e₁ e₂
    simp only [boxFun]
    rw [e₁, e₂]
  have hev : (fun i => evFin F v (z i)) = y := by
    funext i; exact GlobalTheory.LatVac.evFin_liftV v (y i)
  have e := congrFun key z
  simp only [tens, hev, hRz] at e
  exact mul_right_cancel₀ (mul_ne_zero hR0 hR0') e

end GlobalTheory.BoxAct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalProductActsOfAdelicProductActsFirstStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localProduct_acts_of_adelicProduct_acts_first : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ κ' : Type) [Fintype κ] [Fintype κ']
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (Td : ((κ ⊕ κ' → AF F) → ℂ) → (κ ⊕ κ' → AF F) → ℂ),
    (∀ Φ₁ ∈ schA F κ, ∀ Φ₂ ∈ schA F κ', Td (boxFun Φ₁ Φ₂) = boxFun (T Φ₁) Φ₂) →
    ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ' → Fv F v), ∀ (φ₁' : (κ → Fv F v) → ℂ) (Φ' : (κ ⊕ κ' → Fv F v) → ℂ),
      Acts (evFin F v) T φ₁ φ₁' → Acts (evFin F v) Td (boxFun φ₁ φ₂) Φ' → Φ' = boxFun φ₁' φ₂ := by
  first | exact @GlobalTheory.BoxAct.boxFun_acts | exact GlobalTheory.BoxAct.boxFun_acts | (intros; apply GlobalTheory.BoxAct.boxFun_acts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatPartialEvaluation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatPartialEvaluation
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SliceSB

theorem continuous_sumElim {k : Type} [TopologicalSpace k] {κ κ' : Type} :
    Continuous (fun p : (κ → k) × (κ' → k) => (Sum.elim p.1 p.2 : κ ⊕ κ' → k)) := by
  refine continuous_pi fun i => ?_
  cases i with
  | inl i => exact (continuous_apply i).comp continuous_fst
  | inr i => exact (continuous_apply i).comp continuous_snd

theorem slice_mem : ∀ (k : Type) [TopologicalSpace k] [T2Space k] (κ κ' : Type) [Fintype κ] [Fintype κ'], ∀ f ∈ SB (κ ⊕ κ' → k),
    (∀ x₁ : κ → k, (fun x₂ : κ' → k => f (Sum.elim x₁ x₂)) ∈ SB (κ' → k)) ∧
      ∀ l : ((κ' → k) → ℂ) →ₗ[ℂ] ℂ, (fun x₁ : κ → k => l fun x₂ => f (Sum.elim x₁ x₂)) ∈ SB (κ → k) := by
  intro k _ _ κ κ' _ _ f hf
  obtain ⟨hlc, hcs⟩ := hf
  have hΦ := continuous_sumElim (k := k) (κ := κ) (κ' := κ')
  refine ⟨fun x₁ => ?_, fun l => ?_⟩
  · have he : Continuous (fun x₂ : κ' → k => (Sum.elim x₁ x₂ : κ ⊕ κ' → k)) :=
      hΦ.comp (Continuous.prodMk continuous_const continuous_id)
    have hli : Function.LeftInverse (fun z : κ ⊕ κ' → k => z ∘ Sum.inr) (fun x₂ : κ' → k => (Sum.elim x₁ x₂ : κ ⊕ κ' → k)) :=
      fun x₂ => rfl
    have hce : Topology.IsClosedEmbedding (fun x₂ : κ' → k => (Sum.elim x₁ x₂ : κ ⊕ κ' → k)) :=
      hli.isClosedEmbedding (continuous_pi fun i => continuous_apply _) he
    exact ⟨hlc.comp_continuous he, hcs.comp_isClosedEmbedding hce⟩
  · set K := (fun z : κ ⊕ κ' → k => z ∘ Sum.inr) '' tsupport f
    have hK : IsCompact K := hcs.isCompact.image (continuous_pi fun i => continuous_apply _)
    have hloc : IsLocallyConstant (fun x₁ : κ → k => fun x₂ : κ' → k => f (Sum.elim x₁ x₂)) := by
      rw [IsLocallyConstant.iff_eventually_eq _]
      intro x₀
      have hF : IsLocallyConstant (fun p : (κ → k) × (κ' → k) => f (Sum.elim p.1 p.2)) := hlc.comp_continuous hΦ
      have h1 : ∀ y ∈ K, ∀ᶠ z : (κ → k) × (κ' → k) in nhds (x₀, y),
          (fun x y => f (Sum.elim x y) = f (Sum.elim x₀ y)) z.1 z.2 := by
        intro y _
        have h0 := (IsLocallyConstant.iff_eventually_eq _).mp hF (x₀, y)
        have hc : Continuous (fun z : (κ → k) × (κ' → k) => (x₀, z.2)) := continuous_const.prodMk continuous_snd
        have h3 : ∀ᶠ z : (κ → k) × (κ' → k) in nhds (x₀, y), f (Sum.elim x₀ z.2) = f (Sum.elim x₀ y) :=
          (hc.tendsto (x₀, y)).eventually h0
        filter_upwards [h0, h3] with z hz hz'
        exact hz.trans hz'.symm
      have h2 := hK.eventually_forall_of_forall_eventually (P := fun x y => f (Sum.elim x y) = f (Sum.elim x₀ y)) h1
      filter_upwards [h2] with x hx
      funext y
      by_cases hy : y ∈ K
      · exact hx y hy
      · have hz : ∀ x', f (Sum.elim x' y) = 0 := by
          intro x'
          by_contra hne
          exact hy ⟨Sum.elim x' y, subset_tsupport f hne, rfl⟩
        rw [hz, hz]
    refine ⟨(hloc.comp l), ?_⟩
    refine HasCompactSupport.intro (hcs.isCompact.image (f := fun z : κ ⊕ κ' → k => z ∘ Sum.inl) (continuous_pi fun i => continuous_apply _)) ?_
    intro x hx
    have : (fun x₂ : κ' → k => f (Sum.elim x x₂)) = 0 := by
      funext x₂
      by_contra hne
      exact hx ⟨Sum.elim x x₂, subset_tsupport f hne, rfl⟩
    simp only [this, map_zero]

end GlobalTheory.SliceSB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatPartialEvaluationStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_partial_evaluation : ∀ (k : Type) [TopologicalSpace k] [T2Space k] (κ κ' : Type) [Fintype κ] [Fintype κ'], ∀ f ∈ SB (κ ⊕ κ' → k),
    (∀ x₁ : κ → k, (fun x₂ : κ' → k => f (Sum.elim x₁ x₂)) ∈ SB (κ' → k)) ∧
      ∀ l : ((κ' → k) → ℂ) →ₗ[ℂ] ℂ, (fun x₁ : κ → k => l fun x₂ => f (Sum.elim x₁ x₂)) ∈ SB (κ → k) := by
  first | exact @GlobalTheory.SliceSB.slice_mem | exact GlobalTheory.SliceSB.slice_mem | (intros; apply GlobalTheory.SliceSB.slice_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementRealisedByFourierTransforms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementRealisedByFourierTransforms
open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexConjugate
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

noncomputable section

namespace GlobalTheory.TowU.WeylModel

variable {F : Type} [Field F] [NumberField F]

theorem act_weyl {κ : Type} [Fintype κ] [DecidableEq κ] (w : (κ → AF F) × (κ → AF F)) :
    AdelicSvN.act (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) w = (w.2, -w.1) := by
  simp [AdelicSvN.act, Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec, Matrix.map_neg, Matrix.neg_mulVec]

theorem conj_psi {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (t : AF F) : conj (ψ t) = ψ (-t) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (GlobalTheory.StdCharFromIsStd.norm_psi hψ t)]

end GlobalTheory.TowU.WeylModel


open GlobalTheory.TowU.WeylModel in
theorem GlobalTheory.TowU.realised_weyl2 : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ], ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F)) S S' := by
  intro F _ _ ψ hψ κ _ _
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI : MeasurableSpace (κ ⊕ κ → AF F) := borel _
  haveI : BorelSpace (κ ⊕ κ → AF F) := ⟨rfl⟩
  let μ : Measure (κ → AF F) := Measure.addHaar
  let E : (κ → AF F) × (κ → AF F) ≃+ (κ ⊕ κ → AF F) :=
    { toFun := fun p => Sum.elim p.1 p.2
      invFun := fun x => (x ∘ Sum.inl, x ∘ Sum.inr)
      left_inv := fun p => by simp
      right_inv := fun x => by simp
      map_add' := fun p q => by funext i; cases i <;> rfl }
  have hc : Continuous E := (Homeomorph.sumArrowHomeomorphProdArrow (X := AF F) (ι := κ) (ι' := κ)).symm.continuous
  have hc' : Continuous E.symm := (Homeomorph.sumArrowHomeomorphProdArrow (X := AF F) (ι := κ) (ι' := κ)).continuous
  let H : (κ → AF F) × (κ → AF F) ≃ₜ (κ ⊕ κ → AF F) :=
    { toEquiv := E.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  let ν : Measure (κ ⊕ κ → AF F) := Measure.map E (μ.prod μ)
  haveI : ν.IsAddHaarMeasure := E.isAddHaarMeasure_map _ hc hc'
  let ε₁ : κ → ℤˣ := fun _ => 1
  let ε₂ : κ ⊕ κ → ℤˣ := Sum.elim (fun _ => 1) (fun _ => -1)
  obtain ⟨S, S', hS, hSf⟩ := GlobalTheory.T.adelicFourier_realises_weylElement F ψ hψ κ μ inferInstance ε₁
  obtain ⟨Sd, Sd', hSd, hSdf⟩ := GlobalTheory.T.adelicFourier_realises_weylElement F ψ hψ (κ ⊕ κ) ν inferInstance ε₂
  refine ⟨S, S', ?_, Sd, Sd', ?_, fun φ₁ h₁ φ₂ h₂ => ?_⟩
  · convert hS using 1
    funext w
    rw [act_weyl]
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [ε₁]
  · convert hSd using 1
    funext w
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> rcases i with i | i <;>
      simp [dblAct, act_weyl, ε₂]
  · funext y
    have hν : ν = Measure.map H.toMeasurableEquiv (μ.prod μ) := rfl
    have e₂ : star (S (star φ₂)) (y ∘ Sum.inr) =
        ∫ x, φ₂ x * ψ (-(∑ i, ((ε₁ i : ℤ) : AF F) * x i * (y ∘ Sum.inr) i)) ∂μ := by
      rw [Pi.star_apply, hSf (star φ₂) (GlobalTheory.ConjSch.star_mem_schA κ φ₂ h₂), Complex.star_def, ← integral_conj]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      beta_reduce
      rw [map_mul, conj_psi hψ, Pi.star_apply, Complex.star_def, Complex.conj_conj]
    rw [hSdf _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ φ₁ h₁ φ₂ h₂), hν, integral_map_equiv]
    change _ = S φ₁ (y ∘ Sum.inl) * star (S (star φ₂)) (y ∘ Sum.inr)
    rw [e₂, hSf φ₁ h₁, ← integral_prod_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    change φ₁ p.1 * φ₂ p.2 * ψ (∑ i, ((ε₂ i : ℤ) : AF F) * Sum.elim p.1 p.2 i * y i) = _
    have es : ∑ i, ((ε₂ i : ℤ) : AF F) * Sum.elim p.1 p.2 i * y i =
        ∑ i, ((ε₁ i : ℤ) : AF F) * p.1 i * (y ∘ Sum.inl) i +
          -(∑ i, ((ε₁ i : ℤ) : AF F) * p.2 i * (y ∘ Sum.inr) i) := by
      simp [Fintype.sum_sum_type, ε₁, ε₂]
    rw [es, AddChar.map_add_eq_mul]
    ring

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementRealisedByFourierTransformsStatement
open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylElement_realised_by_fourierTransforms : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ], ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F)) S S' := by
  first | exact @GlobalTheory.TowU.realised_weyl2 | exact GlobalTheory.TowU.realised_weyl2 | (intros; apply GlobalTheory.TowU.realised_weyl2 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMeasureEqRelIndexSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMeasureEqRelIndexSmul
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelIndexMeasure

theorem measure_eq_relIndex_smul : ∀ {D : D7} (V : HSp D) (n : ℕ) (ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V) (J J₀ : Subgroup (Formalism.MainNotions.StandardLatticesGL3.GA D n))
  (K K₀ : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (μ μ₀ : Measure (GA D V)), ι.range = GfC V → J ≤ J₀ → J.relIndex J₀ ≠ 0 →
  IsOpenCompactLevel V K → IsOpenCompactLevel V K₀ → (∀ x, Lev.finE V (ι x) ∈ K ↔ x ∈ J) → (∀ x, Lev.finE V (ι x) ∈ K₀ ↔ x ∈ J₀) →
  Lev.IsMeasLevDef V K μ → Lev.IsMeasLevDef V K₀ μ₀ → μ = (J.relIndex J₀ : ENNReal) • μ₀ := by
  intro D V n ι J J₀ K K₀ μ μ₀ hι hJ hJi hK hK₀ hJK hJK₀ hμ hμ₀
  obtain ⟨hLC, hSC, hT2, hB, hTG, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hB; haveI := hTG
  haveI : μ.IsHaarMeasure := hμ.1
  haveI : μ₀.IsHaarMeasure := hμ₀.1

  have hfin : ∀ g : GA D V, ∃ x, Lev.finE V (ι x) = Lev.finE V g := by
    intro g
    obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue V 1 _ (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V g)
    have hk : k ∈ ι.range := by
      rw [hι]
      exact MonoidHom.mem_ker.2 k1
    obtain ⟨x, rfl⟩ := hk
    refine ⟨x, ?_⟩
    show Formalism.UG.bc (Lev.swapAE D) (finHom V (ι x)) = Formalism.UG.bc (Lev.swapAE D) (finHom V g)
    rw [k2]
  have hHH : K.comap (Lev.finE V) ≤ K₀.comap (Lev.finE V) := by
    intro g hg
    obtain ⟨x, hx⟩ := hfin g
    change Lev.finE V g ∈ K at hg
    show Lev.finE V g ∈ K₀
    rw [← hx] at hg ⊢
    exact (hJK₀ x).2 (hJ ((hJK x).1 hg))
  have e1 : J = K.comap ((Lev.finE V).comp ι) := by
    ext x
    exact (hJK x).symm
  have e2 : (J₀.map ι).map (Lev.finE V) = (K₀.comap (Lev.finE V)).map (Lev.finE V) := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨ι x, (hJK₀ x).2 hx, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨x, hx⟩ := hfin g
      refine ⟨ι x, ⟨x, (hJK₀ x).1 ?_, rfl⟩, hx⟩
      rw [hx]
      exact hg
  have hidx : (K.comap (Lev.finE V)).relIndex (K₀.comap (Lev.finE V)) = J.relIndex J₀ := by
    rw [e1, Subgroup.relIndex_comap, Subgroup.relIndex_comap, ← Subgroup.map_map, e2]
  haveI : ((K.comap (Lev.finE V)).subgroupOf (K₀.comap (Lev.finE V))).FiniteIndex := ⟨hidx.trans_ne hJi⟩
  have hm := Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure _ _ hHH hK.1.measurableSet μ
  rw [hidx, GlobalTheory.Mass.Levels.measure_comap_finE hμ, mul_one] at hm
  have h0 : μ₀ (K₀.comap (Lev.finE V)) = 1 := GlobalTheory.Mass.Levels.measure_comap_finE hμ₀
  have heq := Measure.isMulLeftInvariant_eq_smul μ μ₀
  have hc : ((Measure.haarScalarFactor μ μ₀ : NNReal) : ENNReal) = (J.relIndex J₀ : ENNReal) := by
    have := congrArg (fun m : Measure (GA D V) => m ((K₀.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V))) heq
    simp only [Measure.smul_apply, h0, ← hm] at this
    rw [this, ENNReal.smul_def, smul_eq_mul, mul_one]
  ext s hs
  rw [heq, Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, hc]

end GlobalTheory.LevelIndexMeasure
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMeasureEqRelIndexSmulStatement
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelMeasure_eq_relIndex_smul : ∀ {D : D7} (V : HSp D) (n : ℕ) (ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V) (J J₀ : Subgroup (Formalism.MainNotions.StandardLatticesGL3.GA D n))
  (K K₀ : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (μ μ₀ : Measure (GA D V)), ι.range = GfC V → J ≤ J₀ → J.relIndex J₀ ≠ 0 →
  IsOpenCompactLevel V K → IsOpenCompactLevel V K₀ → (∀ x, Lev.finE V (ι x) ∈ K ↔ x ∈ J) → (∀ x, Lev.finE V (ι x) ∈ K₀ ↔ x ∈ J₀) →
  Lev.IsMeasLevDef V K μ → Lev.IsMeasLevDef V K₀ μ₀ → μ = (J.relIndex J₀ : ENNReal) • μ₀ := by
  first | exact @GlobalTheory.LevelIndexMeasure.measure_eq_relIndex_smul | exact GlobalTheory.LevelIndexMeasure.measure_eq_relIndex_smul | (intros; apply GlobalTheory.LevelIndexMeasure.measure_eq_relIndex_smul <;> assumption)
end
end
