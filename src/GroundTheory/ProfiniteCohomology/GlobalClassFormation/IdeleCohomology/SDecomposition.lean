module

public import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.Decomposition
public import GroundTheory.GlobalFields.IdeleGroups.LocalHerbrandInfinite
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.Unramified

@[expose] public section

section -- merged from GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.ExistsSIdelesCohomologyEqZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IsDedekindDomain NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
  GroundTheory.Global.AdeleBaseChange

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

noncomputable abbrev ideleRep : Rep ℤ Gal(L/K) :=
  Rep.ofMulDistribMulAction Gal(L/K) (IdeleGroup L)

noncomputable def sIdelesSubmodule (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Submodule ℤ (ideleRep K L) :=
  (Subgroup.toAddSubgroup (sIdeles (placesAbove L (S : Set (HeightOneSpectrum (𝓞 K)))))).toIntSubmodule

omit [NumberField K] in
variable {K L} in
theorem mem_sIdelesSubmodule {S : Finset (HeightOneSpectrum (𝓞 K))} {a : ideleRep K L} :
    a ∈ sIdelesSubmodule K L S ↔
      a.toMul ∈ sIdeles (placesAbove L (S : Set (HeightOneSpectrum (𝓞 K)))) :=
  Iff.rfl


omit [NumberField K] in
theorem sIdelesSubmodule_mono : Monotone (sIdelesSubmodule K L) := fun _ _ h _ ha =>
  sIdeles_mono (placesAbove_mono (Finset.coe_subset.2 h)) ha


omit [NumberField K] in
theorem sIdelesSubmodule_stable (S : Finset (HeightOneSpectrum (𝓞 K))) (g : Gal(L/K)) :
    sIdelesSubmodule K L S ≤ (sIdelesSubmodule K L S).comap ((ideleRep K L).ρ g) := fun _ ha =>
  smul_mem_sIdeles_placesAbove _ g ha


omit [NumberField K] in
theorem exists_mem_sIdelesSubmodule (a : ideleRep K L) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), a ∈ sIdelesSubmodule K L S := by
  have hfin : (below K '' {w : HeightOneSpectrum (𝓞 L) | ord w a.toMul ≠ 0}).Finite :=
    (Filter.eventually_cofinite.1 (eventually_ord_eq_zero a.toMul)).image _
  refine ⟨hfin.toFinset, fun w hw => ?_⟩
  by_contra h
  exact hw (by
    rw [mem_placesAbove, Set.Finite.coe_toFinset]
    exact ⟨w, h, rfl⟩)

variable [IsGalois K L]

theorem exists_sIdeles_cohomology_eq (n : ℕ) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (x : cohomology (ideleRep K L) n) :
    ∃ S, S₀ ⊆ S ∧ ∃ y : cohomology ((ideleRep K L).subrepresentation (sIdelesSubmodule K L S)
        (sIdelesSubmodule_stable K L S)) n,
      (cohomologyMap (Rep.subtype (ideleRep K L) (sIdelesSubmodule K L S)
        (sIdelesSubmodule_stable K L S)) n).hom y = x := by
  classical
  obtain ⟨S, y, hy⟩ := exists_cohomologyMap_subtype_eq (ideleRep K L) (sIdelesSubmodule K L)
    (sIdelesSubmodule_mono K L) (sIdelesSubmodule_stable K L) (exists_mem_sIdelesSubmodule K L) n x
  have h : S ≤ S ∪ S₀ := Finset.subset_union_left
  refine ⟨S ∪ S₀, Finset.subset_union_right, (cohomologyMap (subrepInclusion (ideleRep K L)
    (sIdelesSubmodule K L) (sIdelesSubmodule_mono K L) (sIdelesSubmodule_stable K L) h) n).hom y,
    ?_⟩
  have e := subrepInclusion_comp_subtype (ideleRep K L) (sIdelesSubmodule K L)
    (sIdelesSubmodule_mono K L) (sIdelesSubmodule_stable K L) h
  rw [← hy, ← ModuleCat.comp_apply, ← cohomologyMap_comp, e]

end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.Finite
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits IsDedekindDomain NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
  GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange

open scoped Pointwise

section PiUnits

variable {G X : Type} [Group G] {U : X → Type} [∀ x, CommGroup (U x)]
  [MulDistribMulAction G (∀ x, U x)]

noncomputable def piUnitsRep : Representation ℤ G (∀ x, Additive (U x)) where
  toFun g := AddMonoidHom.toIntLinearMap
    { toFun := fun y x => Additive.ofMul ((g • fun x => (y x).toMul) x)
      map_zero' := funext fun x => congrArg (fun f : ∀ x, U x => Additive.ofMul (f x)) (smul_one g)
      map_add' := fun y z => funext fun x =>
        congrArg (fun f : ∀ x, U x => Additive.ofMul (f x))
          (smul_mul' g (fun x => (y x).toMul) (fun x => (z x).toMul)) }
  map_one' := LinearMap.ext fun y => funext fun x =>
    congrArg (fun f : ∀ x, U x => Additive.ofMul (f x)) (one_smul G fun x => (y x).toMul)
  map_mul' g h := LinearMap.ext fun y => funext fun x =>
    congrArg (fun f : ∀ x, U x => Additive.ofMul (f x)) (mul_smul g h fun x => (y x).toMul)

theorem piUnitsRep_apply (g : G) (y : ∀ x, Additive (U x)) (x : X) :
    piUnitsRep g y x = Additive.ofMul ((g • fun x => (y x).toMul) x) :=
  rfl

end PiUnits

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

section Representation


variable (L) in
noncomputable abbrev finiteUnitsAboveRep :
    Representation ℤ Gal(L/K) (∀ w : PlacesOver L v, Additive (w.1.adicCompletion L)ˣ) :=
  piUnitsRep

theorem finiteUnitsAbove_smul_apply_of_eq (σ : Gal(L/K))
    (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) (w w' : PlacesOver L v)
    (h : w' = σ • w) :
    (((σ • y) w' : (w'.1.adicCompletion L)ˣ) : w'.1.adicCompletion L) =
      galEquiv v σ w.1 w'.1 (by rw [h]; rfl) (y w) := by
  subst h
  exact finiteUnitsAbove_smul_apply v σ y w

theorem permutesFactors_finiteUnitsAboveRep : PermutesFactors (finiteUnitsAboveRep L v) := by
  intro σ f w hf
  apply Additive.toMul.injective
  apply Units.ext
  change (((σ • fun x => (f x).toMul) (σ • w) : ((σ • w).1.adicCompletion L)ˣ) :
    (σ • w).1.adicCompletion L) = 1
  rw [finiteUnitsAbove_smul_apply, hf]
  exact map_one _

noncomputable def finiteProjAboveRep : ideleRep K L ⟶ Rep.of (finiteUnitsAboveRep L v) :=
  Rep.ofHom ⟨AddMonoidHom.toIntLinearMap
    { toFun := fun x w => Additive.ofMul (finiteProjAbove v x.toMul w)
      map_zero' := by
        funext w
        change Additive.ofMul (finiteProjAbove v 1 w) = 0
        rw [map_one]
        rfl
      map_add' := fun x y => by
        funext w
        change Additive.ofMul (finiteProjAbove v (x.toMul * y.toMul) w) = _
        rw [map_mul]
        rfl },
    fun σ => LinearMap.ext fun x => by
      funext w
      change Additive.ofMul (finiteProjAbove v (σ • x.toMul) w) = _
      rw [finiteProjAbove_smul]
      rfl⟩

noncomputable def finiteEmbedAboveRep : Rep.of (finiteUnitsAboveRep L v) ⟶ ideleRep K L :=
  Rep.ofHom ⟨AddMonoidHom.toIntLinearMap
    { toFun := fun y => Additive.ofMul (finiteEmbedAbove v fun w => (y w).toMul)
      map_zero' := by
        change Additive.ofMul (finiteEmbedAbove v 1) = 0
        rw [map_one]
        rfl
      map_add' := fun y z => by
        change Additive.ofMul (finiteEmbedAbove v ((fun w => (y w).toMul) * fun w => (z w).toMul)) = _
        rw [map_mul]
        rfl },
    fun σ => LinearMap.ext fun y => by
      change Additive.ofMul (finiteEmbedAbove v (σ • fun w => (y w).toMul)) = _
      rw [finiteEmbedAbove_smul]
      rfl⟩

theorem finiteEmbedAboveRep_comp_finiteProjAboveRep :
    finiteEmbedAboveRep (L := L) v ≫ finiteProjAboveRep (L := L) v = 𝟙 _ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro y
  funext w
  change Additive.ofMul (finiteProjAbove v (finiteEmbedAbove v fun w => (y w).toMul) w) = y w
  rw [finiteProjAbove_finiteEmbedAbove]
  rfl

theorem finiteEmbedAboveRep_comp_finiteProjAboveRep_of_ne {v v' : HeightOneSpectrum (𝓞 K)}
    (h : v' ≠ v) : finiteEmbedAboveRep (L := L) v ≫ finiteProjAboveRep (L := L) v' = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro y
  funext w
  change Additive.ofMul (finiteProjAbove v' (finiteEmbedAbove v fun w => (y w).toMul) w) = 0
  rw [finiteProjAbove_finiteEmbedAbove_of_ne h]
  rfl

end Representation

section Decomposition

variable (w : PlacesOver L v)


omit [NumberField K] [NumberField L] in
theorem mem_stabilizer_iff_smul_eq (σ : Gal(L/K)) :
    σ ∈ MulAction.stabilizer Gal(L/K) w.1.asIdeal ↔ σ • w = w := by
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff, coe_smul_placesOver,
    HeightOneSpectrum.ext_iff, smul_asIdeal]


omit [NumberField K] in
theorem galHom_eq_decomposition (σ : MulAction.stabilizer Gal(L/K) w.1.asIdeal)
    (h : w.1 = (σ : Gal(L/K)) • w.1) (x : w.1.adicCompletion L) :
    galHom (σ : Gal(L/K)) w.1 w.1 h x = σ • x := by
  rw [decomposition_smul_def]
  exact congrFun (congrArg DFunLike.coe (ringHom_ext_adicCompletion w.1 (continuous_galHom _ _ _ h)
    (continuous_adicCompletionRingHomOf _ _) fun y => by
      rw [galHom_algebraMap, adicCompletionRingHomOf_algebraMap])) x

theorem stabRep_finiteUnitsAboveRep (σ : MulAction.stabilizer Gal(L/K) w.1.asIdeal)
    (a : Additive (w.1.adicCompletion L)ˣ) :
    stabRep (finiteUnitsAboveRep L v) (permutesFactors_finiteUnitsAboveRep v) w
        (MulAction.stabilizer Gal(L/K) w.1.asIdeal) (mem_stabilizer_iff_smul_eq v w) σ a =
      Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.1.asIdeal)
        (w.1.adicCompletion L)ˣ σ a := by
  classical
  rw [stabRep_apply]
  apply Additive.toMul.injective
  apply Units.ext
  have hw : w = (σ : Gal(L/K)) • w := ((mem_stabilizer_iff_smul_eq v w σ).1 σ.2).symm
  simp only [piUnitsRep_apply, toMul_ofMul]
  rw [finiteUnitsAbove_smul_apply_of_eq v (σ : Gal(L/K)) _ w w hw, galEquiv_apply,
    galHom_eq_decomposition]
  simp only [Pi.single_eq_same]
  rfl

noncomputable def stabRepFiniteIso :
    Rep.of (stabRep (finiteUnitsAboveRep L v) (permutesFactors_finiteUnitsAboveRep v) w
        (MulAction.stabilizer Gal(L/K) w.1.asIdeal) (mem_stabilizer_iff_smul_eq v w)) ≅
      Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.1.asIdeal)
        (w.1.adicCompletion L)ˣ :=
  Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℤ _) fun σ =>
    LinearMap.ext fun a => stabRep_finiteUnitsAboveRep v w σ a)

variable [IsGalois K L]

noncomputable def finiteShapiroIso (n : ℕ) :
    cohomology (Rep.of (finiteUnitsAboveRep L v)) n ≅
      cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.1.asIdeal)
        (w.1.adicCompletion L)ˣ) n :=
  orbitShapiroIso (permutesFactors_finiteUnitsAboveRep v)
      ⟨MulAction.stabilizer Gal(L/K) w.1.asIdeal, isOpen_discrete _⟩
      (mem_stabilizer_iff_smul_eq v w) n ≪≫
    cohomologyIsoOfIso (stabRepFiniteIso v w) n

end Decomposition

end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.Infinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
  GroundTheory.Global.AdeleBaseChange

open scoped NumberField.LiesOver

section Maps

variable {M : Type} [Field M]

noncomputable def completionCongr {u u' : InfinitePlace M} (h : u = u') :
    u.Completion ≃+* u'.Completion :=
  h ▸ RingEquiv.refl _

theorem continuous_completionCongr {u u' : InfinitePlace M} (h : u = u') :
    Continuous (completionCongr h) := by
  subst h
  exact continuous_id

theorem completionCongr_algebraMap {u u' : InfinitePlace M} (h : u = u') (x : M) :
    completionCongr h (algebraMap M u.Completion x) = algebraMap M u'.Completion x := by
  subst h
  rfl

theorem continuous_infiniteCompletionMap {M' : Type} [Field M'] [NumberField M] [NumberField M']
    (τ : M ≃+* M') (w' : InfinitePlace M') : Continuous (infiniteCompletionMap τ w') := by
  let _ : Algebra M M' := (τ : M →+* M').toAlgebra
  exact continuous_algebraMap (w'.comap (algebraMap M M')).Completion w'.Completion

end Maps

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : InfinitePlace K)

section Representation


variable (L) in
noncomputable abbrev infiniteUnitsAboveRep :
    Representation ℤ Gal(L/K) (∀ w : v.placesOver L, Additive (w.1.Completion)ˣ) :=
  piUnitsRep

theorem infiniteUnitsAbove_smul_apply_of_eq (σ : Gal(L/K))
    (y : (w : v.placesOver L) → (w.1.Completion)ˣ) (u w : v.placesOver L)
    (h : u.1 = w.1.comap ((σ : L ≃+* L) : L →+* L)) :
    (((σ • y) w : (w.1.Completion)ˣ) : w.1.Completion) =
      infiniteCompletionMap (σ : L ≃+* L) w.1 (completionCongr h (y u)) := by
  obtain rfl : u = ⟨w.1.comap ((σ : L ≃+* L) : L →+* L), comap_mem_placesOver v σ w⟩ :=
    Subtype.ext h
  exact infiniteUnitsAbove_smul_apply v σ y w

omit [NumberField K] [NumberField L] in
theorem comap_smul_placesOver (σ : Gal(L/K)) (w : v.placesOver L) :
    w.1 = (σ • w).1.comap ((σ : L ≃+* L) : L →+* L) := by
  rw [comap_eq_inv_smul, InfinitePlace.coe_smul_placesOver, inv_smul_smul]

theorem permutesFactors_infiniteUnitsAboveRep : PermutesFactors (infiniteUnitsAboveRep L v) := by
  intro σ f w hf
  apply Additive.toMul.injective
  apply Units.ext
  change (((σ • fun x => (f x).toMul) (σ • w) : ((σ • w).1.Completion)ˣ) :
    (σ • w).1.Completion) = 1
  rw [infiniteUnitsAbove_smul_apply_of_eq v σ _ w (σ • w) (comap_smul_placesOver v σ w)]
  rw [hf]
  change infiniteCompletionMap _ _ (completionCongr _ 1) = 1
  rw [map_one, map_one]

noncomputable def infiniteProjAboveRep : ideleRep K L ⟶ Rep.of (infiniteUnitsAboveRep L v) :=
  Rep.ofHom ⟨AddMonoidHom.toIntLinearMap
    { toFun := fun x w => Additive.ofMul (infiniteProjAbove v x.toMul w)
      map_zero' := by
        funext w
        change Additive.ofMul (infiniteProjAbove v 1 w) = 0
        rw [map_one]
        rfl
      map_add' := fun x y => by
        funext w
        change Additive.ofMul (infiniteProjAbove v (x.toMul * y.toMul) w) = _
        rw [map_mul]
        rfl },
    fun σ => LinearMap.ext fun x => by
      funext w
      change Additive.ofMul (infiniteProjAbove v (σ • x.toMul) w) = _
      rw [infiniteProjAbove_smul]
      rfl⟩

noncomputable def infiniteEmbedAboveRep : Rep.of (infiniteUnitsAboveRep L v) ⟶ ideleRep K L :=
  Rep.ofHom ⟨AddMonoidHom.toIntLinearMap
    { toFun := fun y => Additive.ofMul (infiniteEmbedAbove v fun w => (y w).toMul)
      map_zero' := by
        change Additive.ofMul (infiniteEmbedAbove v 1) = 0
        rw [map_one]
        rfl
      map_add' := fun y z => by
        change Additive.ofMul
          (infiniteEmbedAbove v ((fun w => (y w).toMul) * fun w => (z w).toMul)) = _
        rw [map_mul]
        rfl },
    fun σ => LinearMap.ext fun y => by
      change Additive.ofMul (infiniteEmbedAbove v (σ • fun w => (y w).toMul)) = _
      rw [infiniteEmbedAbove_smul]
      rfl⟩

theorem infiniteEmbedAboveRep_comp_infiniteProjAboveRep :
    infiniteEmbedAboveRep (L := L) v ≫ infiniteProjAboveRep (L := L) v = 𝟙 _ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro y
  funext w
  change Additive.ofMul (infiniteProjAbove v (infiniteEmbedAbove v fun w => (y w).toMul) w) = y w
  rw [infiniteProjAbove_infiniteEmbedAbove]
  rfl

theorem infiniteEmbedAboveRep_comp_infiniteProjAboveRep_of_ne {v v' : InfinitePlace K}
    (h : v' ≠ v) : infiniteEmbedAboveRep (L := L) v ≫ infiniteProjAboveRep (L := L) v' = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro y
  funext w
  change Additive.ofMul (infiniteProjAbove v' (infiniteEmbedAbove v fun w => (y w).toMul) w) = 0
  rw [infiniteProjAbove_infiniteEmbedAbove_of_ne h]
  rfl

theorem infiniteEmbedAboveRep_comp_finiteProjAboveRep (v' : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    infiniteEmbedAboveRep (L := L) v ≫ finiteProjAboveRep (L := L) v' = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro y
  funext w
  change Additive.ofMul (finiteProjAbove v' (infiniteEmbedAbove v fun w => (y w).toMul) w) = 0
  rw [finiteProjAbove_infiniteEmbedAbove]
  rfl

theorem finiteEmbedAboveRep_comp_infiniteProjAboveRep (v' : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    finiteEmbedAboveRep (L := L) v' ≫ infiniteProjAboveRep (L := L) v = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro y
  funext w
  change Additive.ofMul (infiniteProjAbove v (finiteEmbedAbove v' fun w => (y w).toMul) w) = 0
  rw [infiniteProjAbove_finiteEmbedAbove]
  rfl

end Representation

section Decomposition

variable (w : v.placesOver L)


omit [NumberField K] [NumberField L] in
theorem mem_stabilizer_iff_smul_eq_infinite (σ : Gal(L/K)) :
    σ ∈ MulAction.stabilizer Gal(L/K) w.1 ↔ σ • w = w := by
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff, InfinitePlace.coe_smul_placesOver]


omit [NumberField K] in
theorem infiniteCompletionMap_eq_decomposition (σ : MulAction.stabilizer Gal(L/K) w.1)
    (h : w.1 = w.1.comap (((σ : Gal(L/K)) : L ≃+* L) : L →+* L)) (x : w.1.Completion) :
    infiniteCompletionMap ((σ : Gal(L/K)) : L ≃+* L) w.1 (completionCongr h x) = σ • x := by
  rw [infiniteDecomposition_smul_def]
  have := ringHom_ext_completion w.1
    (f := (infiniteCompletionMap ((σ : Gal(L/K)) : L ≃+* L) w.1).comp (completionCongr h).toRingHom)
    ((continuous_infiniteCompletionMap _ _).comp (continuous_completionCongr h))
    (continuous_completionRingHomOf σ.2) fun y => by
      rw [completionRingHomOf_coe]
      have hy (y : WithAbs w.1.1) : (y : w.1.Completion) = algebraMap L w.1.Completion y.ofAbs := by
        rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
        rfl
      rw [hy y, hy (withAbsMapOf w.1 (σ : Gal(L/K)) y)]
      change infiniteCompletionMap _ w.1 (completionCongr h (algebraMap L w.1.Completion y.ofAbs)) =
        algebraMap L w.1.Completion (withAbsMapOf w.1 (σ : Gal(L/K)) y).ofAbs
      rw [completionCongr_algebraMap, infiniteCompletionMap_algebraMap, ofAbs_withAbsMapOf]
      rfl
  exact congrFun (congrArg DFunLike.coe this) x

theorem stabRep_infiniteUnitsAboveRep (σ : MulAction.stabilizer Gal(L/K) w.1)
    (a : Additive (w.1.Completion)ˣ) :
    stabRep (infiniteUnitsAboveRep L v) (permutesFactors_infiniteUnitsAboveRep v) w
        (MulAction.stabilizer Gal(L/K) w.1) (mem_stabilizer_iff_smul_eq_infinite v w) σ a =
      Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.1)
        (w.1.Completion)ˣ σ a := by
  classical
  rw [stabRep_apply]
  apply Additive.toMul.injective
  apply Units.ext
  have hw : w = (σ : Gal(L/K)) • w := ((mem_stabilizer_iff_smul_eq_infinite v w σ).1 σ.2).symm
  have h : w.1 = w.1.comap (((σ : Gal(L/K)) : L ≃+* L) : L →+* L) := by
    have h' := comap_smul_placesOver v (σ : Gal(L/K)) w
    rwa [← hw] at h'
  simp only [piUnitsRep_apply, toMul_ofMul]
  rw [infiniteUnitsAbove_smul_apply_of_eq v (σ : Gal(L/K)) _ w w h,
    infiniteCompletionMap_eq_decomposition]
  simp only [Pi.single_eq_same]
  rfl

noncomputable def stabRepInfiniteIso :
    Rep.of (stabRep (infiniteUnitsAboveRep L v) (permutesFactors_infiniteUnitsAboveRep v) w
        (MulAction.stabilizer Gal(L/K) w.1) (mem_stabilizer_iff_smul_eq_infinite v w)) ≅
      Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.1) (w.1.Completion)ˣ :=
  Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℤ _) fun σ =>
    LinearMap.ext fun a => stabRep_infiniteUnitsAboveRep v w σ a)

variable [IsGalois K L]

noncomputable def infiniteShapiroIso (n : ℕ) :
    cohomology (Rep.of (infiniteUnitsAboveRep L v)) n ≅
      cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.1)
        (w.1.Completion)ˣ) n :=
  orbitShapiroIso (permutesFactors_infiniteUnitsAboveRep v)
      ⟨MulAction.stabilizer Gal(L/K) w.1, isOpen_discrete _⟩
      (mem_stabilizer_iff_smul_eq_infinite v w) n ≪≫
    cohomologyIsoOfIso (stabRepInfiniteIso v w) n

end Decomposition

end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.Integral
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits IsDedekindDomain NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
  GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange

open scoped Pointwise

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))


variable (L) in
noncomputable abbrev integerUnitsAboveRep :
    Representation ℤ Gal(L/K) (∀ w : PlacesOver L v, Additive (w.1.adicCompletionIntegers L)ˣ) :=
  piUnitsRep

theorem integerUnitsAbove_smul_apply_of_eq (σ : Gal(L/K))
    (z : (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) (w w' : PlacesOver L v)
    (h : w' = σ • w) :
    ((((σ • z) w' : (w'.1.adicCompletionIntegers L)ˣ) : w'.1.adicCompletionIntegers L) :
      w'.1.adicCompletion L) =
      galEquiv v σ w.1 w'.1 (by rw [h]; rfl) ((z w : w.1.adicCompletionIntegers L) :
        w.1.adicCompletion L) := by
  subst h
  exact integerUnitsAbove_smul_apply v σ z w

theorem permutesFactors_integerUnitsAboveRep : PermutesFactors (integerUnitsAboveRep L v) := by
  intro σ f w hf
  apply Additive.toMul.injective
  apply Units.ext
  apply Subtype.ext
  change ((((σ • fun x => (f x).toMul) (σ • w) : ((σ • w).1.adicCompletionIntegers L)ˣ) :
    (σ • w).1.adicCompletionIntegers L) : (σ • w).1.adicCompletion L) = 1
  rw [integerUnitsAbove_smul_apply, hf]
  exact map_one _

section Decomposition

variable (w : PlacesOver L v)

theorem stabRep_integerUnitsAboveRep (σ : MulAction.stabilizer Gal(L/K) w.1.asIdeal)
    (a : Additive (w.1.adicCompletionIntegers L)ˣ) :
    stabRep (integerUnitsAboveRep L v) (permutesFactors_integerUnitsAboveRep v) w
        (MulAction.stabilizer Gal(L/K) w.1.asIdeal) (mem_stabilizer_iff_smul_eq v w) σ a =
      Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.1.asIdeal)
        (w.1.adicCompletionIntegers L)ˣ σ a := by
  classical
  rw [stabRep_apply]
  apply Additive.toMul.injective
  apply Units.ext
  apply Subtype.ext
  have hw : w = (σ : Gal(L/K)) • w := ((mem_stabilizer_iff_smul_eq v w σ).1 σ.2).symm
  simp only [piUnitsRep_apply, toMul_ofMul]
  rw [integerUnitsAbove_smul_apply_of_eq v (σ : Gal(L/K)) _ w w hw, galEquiv_apply,
    galHom_eq_decomposition]
  simp only [Pi.single_eq_same]
  rfl

noncomputable def stabRepIntegralIso :
    Rep.of (stabRep (integerUnitsAboveRep L v) (permutesFactors_integerUnitsAboveRep v) w
        (MulAction.stabilizer Gal(L/K) w.1.asIdeal) (mem_stabilizer_iff_smul_eq v w)) ≅
      Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.1.asIdeal)
        (w.1.adicCompletionIntegers L)ˣ :=
  Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℤ _) fun σ =>
    LinearMap.ext fun a => stabRep_integerUnitsAboveRep v w σ a)

variable [IsGalois K L]

noncomputable def integralShapiroIso (n : ℕ) :
    cohomology (Rep.of (integerUnitsAboveRep L v)) n ≅
      cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.1.asIdeal)
        (w.1.adicCompletionIntegers L)ˣ) n :=
  orbitShapiroIso (permutesFactors_integerUnitsAboveRep v)
      ⟨MulAction.stabilizer Gal(L/K) w.1.asIdeal, isOpen_discrete _⟩
      (mem_stabilizer_iff_smul_eq v w) n ≪≫
    cohomologyIsoOfIso (stabRepIntegralIso v w) n

theorem isZero_cohomology_integerUnitsAboveRep (he : w.1.asIdeal.ramificationIdx (𝓞 K) = 1)
    {n : ℕ} (hn : 1 ≤ n) : IsZero (cohomology (Rep.of (integerUnitsAboveRep L v)) n) :=
  (isZero_cohomology_decomposition_integerUnits v w.1 he hn).of_iso (integralShapiroIso v w n)

end Decomposition

end GroundTheory.ProfCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits IsDedekindDomain NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
  GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange

universe u

section Generic

variable {k G : Type u} [CommRing k] [Monoid G]

def homToSubrep (A : Rep.{u} k G) (W : Submodule k A) (hW : ∀ g, W ≤ W.comap (A.ρ g))
    {B : Rep.{u} k G} (f : B ⟶ A) (hf : ∀ b, f.hom b ∈ W) : B ⟶ A.subrepresentation W hW :=
  Rep.ofHom ⟨LinearMap.codRestrict W f.hom.toLinearMap hf, fun g => LinearMap.ext fun b =>
    Subtype.ext (Rep.hom_comm_apply f g b)⟩

end Generic

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 K)))


variable (K L) in
noncomputable abbrev sIdeleRep : Rep ℤ Gal(L/K) :=
  (ideleRep K L).subrepresentation (sIdelesSubmodule K L S) (sIdelesSubmodule_stable K L S)


variable (K) in
abbrev SIndex : Type :=
  InfinitePlace K ⊕ ((S : Set (HeightOneSpectrum (𝓞 K))) ⊕ ↥(S : Set (HeightOneSpectrum (𝓞 K)))ᶜ)


variable (L) in
noncomputable def sComp : SIndex K S → Rep ℤ Gal(L/K)
  | .inl v => Rep.of (infiniteUnitsAboveRep L v)
  | .inr (.inl v) => Rep.of (finiteUnitsAboveRep L v.1)
  | .inr (.inr v) => Rep.of (integerUnitsAboveRep L v.1)

def toSIdele (a : ↥(sIdelesSubmodule K L S)) :
    sIdeles (placesAbove L (S : Set (HeightOneSpectrum (𝓞 K)))) :=
  ⟨a.1.toMul, mem_sIdelesSubmodule.1 a.2⟩




omit [NumberField K] in
theorem toSIdele_bijective : Function.Bijective (toSIdele (L := L) S) :=
  ⟨fun a b h => Subtype.ext (by
      have := congrArg (fun x : sIdeles (placesAbove L (S : Set (HeightOneSpectrum (𝓞 K)))) =>
        Additive.ofMul (x : IdeleGroup L)) h
      exact this),
    fun x => ⟨⟨Additive.ofMul (x : IdeleGroup L), mem_sIdelesSubmodule.2 x.2⟩, rfl⟩⟩

noncomputable def sIntegerProj (v : ↥(S : Set (HeightOneSpectrum (𝓞 K)))ᶜ) :
    sIdeleRep K L S ⟶ Rep.of (integerUnitsAboveRep L v.1) :=
  Rep.ofHom ⟨AddMonoidHom.toIntLinearMap
    { toFun := fun a w => Additive.ofMul (sIdelesIntegerPart _ (toSIdele S a) v w)
      map_zero' := by
        funext w
        change Additive.ofMul (sIdelesIntegerPart _ 1 v w) = 0
        rw [map_one]
        rfl
      map_add' := fun a b => by
        funext w
        change Additive.ofMul (sIdelesIntegerPart _ (toSIdele S a * toSIdele S b) v w) = _
        rw [map_mul]
        rfl },
    fun σ => LinearMap.ext fun a => by
      funext w
      change Additive.ofMul (sIdelesIntegerPart _ (σ • toSIdele S a) v w) = _
      have h := congrArg (fun p : SIdelesProduct L (S : Set (HeightOneSpectrum (𝓞 K))) => p.2.2 v)
        (sIdelesToProduct_smul _ σ (toSIdele S a))
      simp only [sIdelesToProduct_snd_snd] at h
      rw [h]
      rfl⟩

theorem integerUnitsAboveIncl_sIntegerProj (v : ↥(S : Set (HeightOneSpectrum (𝓞 K)))ᶜ)
    (a : ↥(sIdelesSubmodule K L S)) :
    integerUnitsAboveIncl v.1 (fun w => ((sIntegerProj S v).hom a w).toMul) =
      finiteProjAbove v.1 a.1.toMul :=
  integerUnitsAboveIncl_sIdelesIntegerPart _ (toSIdele S a) v

noncomputable def sProj : ∀ i : SIndex K S, sIdeleRep K L S ⟶ sComp L S i
  | .inl v => Rep.subtype _ _ _ ≫ infiniteProjAboveRep v
  | .inr (.inl v) => Rep.subtype _ _ _ ≫ finiteProjAboveRep v.1
  | .inr (.inr v) => sIntegerProj S v

omit [NumberField K] in
theorem mem_sIdeles_of_mem_standardOpenSubgroup {x : IdeleGroup L}
    (hx : x ∈ standardOpenSubgroup L) : x ∈ sIdeles (placesAbove L (S : Set (HeightOneSpectrum (𝓞 K)))) :=
  standardOpenSubgroup_le_sIdeles _ hx

omit [NumberField K] in
theorem infiniteEmbedAbove_mem_standardOpenSubgroup (v : InfinitePlace K)
    (y : (w : v.placesOver L) → (w.1.Completion)ˣ) :
    infiniteEmbedAbove v y ∈ standardOpenSubgroup L := by
  refine (mem_standardOpenSubgroup L).2 fun w => ?_
  rw [← map_inv, coe_infiniteEmbedAbove_snd, coe_infiniteEmbedAbove_snd]
  exact ⟨(w.adicCompletionIntegers L).one_mem, (w.adicCompletionIntegers L).one_mem⟩

theorem finiteEmbedAbove_mem_sIdeles (v : (S : Set (HeightOneSpectrum (𝓞 K))))
    (y : (w : PlacesOver L v.1) → (w.1.adicCompletion L)ˣ) :
    finiteEmbedAbove v.1 y ∈ sIdeles (placesAbove L (S : Set (HeightOneSpectrum (𝓞 K)))) := by
  intro w hw
  have h : ¬ w.asIdeal.LiesOver v.1.asIdeal := fun h =>
    hw (by rw [mem_placesAbove, (below_eq_iff w v.1).2 h]; exact v.2)
  rw [ord_eq_zero_iff, ← map_inv, coe_finiteEmbedAbove_snd_of_not v.1 _ h,
    coe_finiteEmbedAbove_snd_of_not v.1 _ h]
  exact ⟨(w.adicCompletionIntegers L).one_mem, (w.adicCompletionIntegers L).one_mem⟩

noncomputable def integerEmbedAboveRep (v : HeightOneSpectrum (𝓞 K)) :
    Rep.of (integerUnitsAboveRep L v) ⟶ ideleRep K L :=
  Rep.ofHom ⟨AddMonoidHom.toIntLinearMap
    { toFun := fun z => Additive.ofMul (finiteEmbedAbove v (integerUnitsAboveIncl v
        fun w => (z w).toMul))
      map_zero' := by
        change Additive.ofMul (finiteEmbedAbove v (integerUnitsAboveIncl v 1)) = 0
        rw [map_one, map_one]
        rfl
      map_add' := fun y z => by
        change Additive.ofMul (finiteEmbedAbove v (integerUnitsAboveIncl v
          ((fun w => (y w).toMul) * fun w => (z w).toMul))) = _
        rw [map_mul, map_mul]
        rfl },
    fun σ => LinearMap.ext fun z => by
      change Additive.ofMul (finiteEmbedAbove v (integerUnitsAboveIncl v
        (σ • fun w => (z w).toMul))) = _
      rw [integerUnitsAboveIncl_smul, finiteEmbedAbove_smul]
      rfl⟩

noncomputable def sEmbInf (v : InfinitePlace K) : Rep.of (infiniteUnitsAboveRep L v) ⟶ sIdeleRep K L S :=
  homToSubrep _ _ _ (infiniteEmbedAboveRep v) fun _ =>
    mem_sIdeles_of_mem_standardOpenSubgroup S (infiniteEmbedAbove_mem_standardOpenSubgroup v _)

noncomputable def sEmbFin (v : (S : Set (HeightOneSpectrum (𝓞 K)))) :
    Rep.of (finiteUnitsAboveRep L v.1) ⟶ sIdeleRep K L S :=
  homToSubrep _ _ _ (finiteEmbedAboveRep v.1) fun _ => finiteEmbedAbove_mem_sIdeles S v _

noncomputable def sEmbInt (v : ↥(S : Set (HeightOneSpectrum (𝓞 K)))ᶜ) :
    Rep.of (integerUnitsAboveRep L v.1) ⟶ sIdeleRep K L S :=
  homToSubrep _ _ _ (integerEmbedAboveRep v.1) fun _ =>
    mem_sIdeles_of_mem_standardOpenSubgroup S (finiteEmbedAbove_integerUnitsAboveIncl_mem v.1 _)

noncomputable def sEmb : ∀ i : SIndex K S, sComp L S i ⟶ sIdeleRep K L S
  | .inl v => sEmbInf S v
  | .inr (.inl v) => sEmbFin S v
  | .inr (.inr v) => sEmbInt S v

theorem sEmbInf_comp_subtype (v : InfinitePlace K) :
    sEmbInf (L := L) S v ≫ Rep.subtype _ _ _ = infiniteEmbedAboveRep v :=
  rfl

theorem sEmbFin_comp_subtype (v : (S : Set (HeightOneSpectrum (𝓞 K)))) :
    sEmbFin (L := L) S v ≫ Rep.subtype _ _ _ = finiteEmbedAboveRep v.1 :=
  rfl

def productToFamily (p : SIdelesProduct L (S : Set (HeightOneSpectrum (𝓞 K)))) :
    ∀ i : SIndex K S, sComp L S i
  | .inl v => fun w => Additive.ofMul (p.1 v w)
  | .inr (.inl v) => fun w => Additive.ofMul (p.2.1 v w)
  | .inr (.inr v) => fun w => Additive.ofMul (p.2.2 v w)

theorem productToFamily_bijective : Function.Bijective (productToFamily (L := L) S) := by
  constructor
  · intro p q h
    refine Prod.ext (funext fun v => funext fun w => ?_)
      (Prod.ext (funext fun v => funext fun w => ?_) (funext fun v => funext fun w => ?_))
    · exact congrArg Additive.toMul (congrFun (congrFun h (.inl v)) w)
    · exact congrArg Additive.toMul (congrFun (congrFun h (.inr (.inl v))) w)
    · exact congrArg Additive.toMul (congrFun (congrFun h (.inr (.inr v))) w)
  · intro F
    refine ⟨(fun v w => (F (.inl v) w).toMul, fun v w => (F (.inr (.inl v)) w).toMul,
      fun v w => (F (.inr (.inr v)) w).toMul), funext fun i => ?_⟩
    rcases i with v | v | v <;> rfl

theorem sProj_eq_productToFamily (a : ↥(sIdelesSubmodule K L S)) (i : SIndex K S) :
    (sProj S i).hom a = productToFamily S (sIdelesToProduct _ (toSIdele S a)) i := by
  rcases i with v | v | v <;> rfl

theorem sProj_bijective :
    Function.Bijective fun (a : sIdeleRep K L S) (i : SIndex K S) => (sProj S i).hom a := by
  have e : (fun (a : ↥(sIdelesSubmodule K L S)) (i : SIndex K S) => (sProj S i).hom a) =
      productToFamily (L := L) S ∘ sIdelesToProduct _ ∘ toSIdele (L := L) S :=
    funext fun a => funext fun i => sProj_eq_productToFamily S a i
  have hb := (productToFamily_bijective (L := L) S).comp
    ((sIdelesEquivProduct _ (S.finite_toSet)).bijective.comp (toSIdele_bijective (L := L) S))
  rw [show ⇑(sIdelesEquivProduct (L := L) ((S : Set (HeightOneSpectrum (𝓞 K)))) S.finite_toSet) =
    sIdelesToProduct _ from rfl, ← e] at hb
  exact hb

noncomputable def integerInclRep (v : HeightOneSpectrum (𝓞 K)) :
    Rep.of (integerUnitsAboveRep L v) ⟶ Rep.of (finiteUnitsAboveRep L v) :=
  Rep.ofHom ⟨AddMonoidHom.toIntLinearMap
    { toFun := fun z w => Additive.ofMul (integerUnitsAboveIncl v (fun w => (z w).toMul) w)
      map_zero' := by
        funext w
        change Additive.ofMul (integerUnitsAboveIncl v 1 w) = 0
        rw [map_one]
        rfl
      map_add' := fun y z => by
        funext w
        change Additive.ofMul (integerUnitsAboveIncl v
          ((fun w => (y w).toMul) * fun w => (z w).toMul) w) = _
        rw [map_mul]
        rfl },
    fun σ => LinearMap.ext fun z => by
      funext w
      change Additive.ofMul (integerUnitsAboveIncl v (σ • fun w => (z w).toMul) w) = _
      rw [integerUnitsAboveIncl_smul]
      rfl⟩

instance mono_integerInclRep (v : HeightOneSpectrum (𝓞 K)) : Mono (integerInclRep (L := L) v) := by
  rw [Rep.mono_iff_injective]
  intro y z h
  have h' : integerUnitsAboveIncl v (fun w => (y w).toMul) =
      integerUnitsAboveIncl v (fun w => (z w).toMul) :=
    funext fun w => congrArg Additive.toMul (congrFun h w)
  have := integerUnitsAboveIncl_injective v h'
  funext w
  exact congrArg Additive.ofMul (congrFun this w)

theorem sIntegerProj_comp_integerInclRep (v : ↥(S : Set (HeightOneSpectrum (𝓞 K)))ᶜ) :
    sIntegerProj (L := L) S v ≫ integerInclRep v.1 =
      Rep.subtype _ _ _ ≫ finiteProjAboveRep v.1 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  funext w
  exact congrArg (fun f => Additive.ofMul (f w)) (integerUnitsAboveIncl_sIntegerProj S v a)

theorem sEmbInt_comp_subtype (v : ↥(S : Set (HeightOneSpectrum (𝓞 K)))ᶜ) :
    sEmbInt (L := L) S v ≫ Rep.subtype _ _ _ = integerInclRep v.1 ≫ finiteEmbedAboveRep v.1 :=
  rfl

theorem eq_zero_of_comp_integerInclRep {v : HeightOneSpectrum (𝓞 K)} {X : Rep ℤ Gal(L/K)}
    (f : X ⟶ Rep.of (integerUnitsAboveRep L v)) (hf : f ≫ integerInclRep v = 0) : f = 0 := by
  rw [← cancel_mono (integerInclRep v), hf, Limits.zero_comp]

theorem sEmbInt_comp_sIntegerProj (v : ↥(S : Set (HeightOneSpectrum (𝓞 K)))ᶜ) :
    sEmbInt (L := L) S v ≫ sIntegerProj S v = 𝟙 _ := by
  rw [← cancel_mono (integerInclRep v.1), Category.assoc, sIntegerProj_comp_integerInclRep,
    ← Category.assoc, sEmbInt_comp_subtype, Category.assoc,
    finiteEmbedAboveRep_comp_finiteProjAboveRep, Category.comp_id, Category.id_comp]

theorem sEmbInf_comp_sIntegerProj (v : InfinitePlace K)
    (v' : ↥(S : Set (HeightOneSpectrum (𝓞 K)))ᶜ) : sEmbInf (L := L) S v ≫ sIntegerProj S v' = 0 := by
  refine eq_zero_of_comp_integerInclRep _ ?_
  rw [Category.assoc, sIntegerProj_comp_integerInclRep, ← Category.assoc, sEmbInf_comp_subtype]
  exact infiniteEmbedAboveRep_comp_finiteProjAboveRep v v'.1

theorem sEmbFin_comp_sIntegerProj (v : (S : Set (HeightOneSpectrum (𝓞 K))))
    (v' : ↥(S : Set (HeightOneSpectrum (𝓞 K)))ᶜ) : sEmbFin (L := L) S v ≫ sIntegerProj S v' = 0 := by
  refine eq_zero_of_comp_integerInclRep _ ?_
  rw [Category.assoc, sIntegerProj_comp_integerInclRep, ← Category.assoc, sEmbFin_comp_subtype]
  exact finiteEmbedAboveRep_comp_finiteProjAboveRep_of_ne fun (e : v'.1 = v.1) => v'.2 (e ▸ v.2)

theorem sEmbInt_comp_sIntegerProj_of_ne {v v' : ↥(S : Set (HeightOneSpectrum (𝓞 K)))ᶜ}
    (h : v ≠ v') : sEmbInt (L := L) S v ≫ sIntegerProj S v' = 0 := by
  refine eq_zero_of_comp_integerInclRep _ ?_
  rw [Category.assoc, sIntegerProj_comp_integerInclRep, ← Category.assoc, sEmbInt_comp_subtype,
    Category.assoc, finiteEmbedAboveRep_comp_finiteProjAboveRep_of_ne
      (fun e => h (Subtype.ext e.symm)), Limits.comp_zero]

theorem sEmbInt_comp_infinite (v : ↥(S : Set (HeightOneSpectrum (𝓞 K)))ᶜ) (v' : InfinitePlace K) :
    sEmbInt (L := L) S v ≫ Rep.subtype _ _ _ ≫ infiniteProjAboveRep v' = 0 := by
  rw [← Category.assoc, sEmbInt_comp_subtype, Category.assoc,
    finiteEmbedAboveRep_comp_infiniteProjAboveRep, Limits.comp_zero]

theorem sEmbInt_comp_finite (v : ↥(S : Set (HeightOneSpectrum (𝓞 K)))ᶜ)
    (v' : (S : Set (HeightOneSpectrum (𝓞 K)))) :
    sEmbInt (L := L) S v ≫ Rep.subtype _ _ _ ≫ finiteProjAboveRep v'.1 = 0 := by
  rw [← Category.assoc, sEmbInt_comp_subtype, Category.assoc,
    finiteEmbedAboveRep_comp_finiteProjAboveRep_of_ne (fun (e : v'.1 = v.1) => v.2 (e ▸ v'.2)),
    Limits.comp_zero]

theorem sEmb_comp_sProj (i : SIndex K S) : sEmb (L := L) S i ≫ sProj S i = 𝟙 _ := by
  rcases i with v | v | v
  · exact infiniteEmbedAboveRep_comp_infiniteProjAboveRep v
  · exact finiteEmbedAboveRep_comp_finiteProjAboveRep v.1
  · exact sEmbInt_comp_sIntegerProj S v

theorem sEmb_comp_sProj_of_ne (i j : SIndex K S) (h : i ≠ j) :
    sEmb (L := L) S i ≫ sProj S j = 0 := by
  rcases i with v | v | v <;> rcases j with v' | v' | v'
  · exact infiniteEmbedAboveRep_comp_infiniteProjAboveRep_of_ne fun e => h (by rw [e])
  · exact infiniteEmbedAboveRep_comp_finiteProjAboveRep v v'.1
  · exact sEmbInf_comp_sIntegerProj S v v'
  · exact finiteEmbedAboveRep_comp_infiniteProjAboveRep v' v.1
  · exact finiteEmbedAboveRep_comp_finiteProjAboveRep_of_ne fun e => h (by rw [Subtype.ext e])
  · exact sEmbFin_comp_sIntegerProj S v v'
  · exact sEmbInt_comp_infinite S v v'
  · exact sEmbInt_comp_finite S v v'
  · exact sEmbInt_comp_sIntegerProj_of_ne S fun e => h (by rw [e])

end GroundTheory.ProfCoh
