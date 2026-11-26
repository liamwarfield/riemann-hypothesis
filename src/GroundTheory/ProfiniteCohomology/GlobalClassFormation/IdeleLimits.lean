module

public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.Sequence
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.Colimit
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.InfRange

@[expose] public section

section -- merged from GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.InfColimit
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IsDedekindDomain NumberField IntermediateField GroundTheory.Global
  GroundTheory.Global.SemiLocal FiniteSubfield

open scoped Pointwise NumberField.LiesOver

noncomputable section

variable {K : FiniteSubfield} {v : NumberField.InfinitePlace K.1}
  (ι : AlgebraicClosure ℚ →ₐ[K.1] AlgebraicClosure v.Completion)

section Level

variable (F : FiniteSubfield) [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

abbrev infLocalLevelRep :
    Rep ℤ (MulAction.stabilizer Gal(F.1/K.1) (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1)) :=
  Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(F.1/K.1) (infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1))
    ((infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion)ˣ

abbrev infLocalCochainsInfl :
    cochainsComplex (infLocalLevelRep ι F) ⟶
      cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) :=
  cochainsMapAlong (infLocalDecompHom ι F) (continuous_infLocalDecompHom ι F) (infLocalUnitsMor ι F)

theorem infLocalUnitsMor_injective : Function.Injective (infLocalUnitsMor ι F).hom := by
  intro a b h
  have h' := congrArg (fun u ↦ ((Additive.toMul u :
    (AlgebraicClosure v.Completion)ˣ) : AlgebraicClosure v.Completion)) h
  simp only at h'
  exact congrArg Additive.ofMul (Units.ext ((infCompletionEmbedding ι F).toRingHom.injective h'))

theorem infLocalCochains_injective (m : ℕ) : Function.Injective ((infLocalCochainsInfl ι F).f m).hom := by
  intro y y' h
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι (infLocalLevelRep ι F)).f m)).1 inferInstance
  funext τ
  obtain ⟨σ, rfl⟩ : ∃ σ : Fin m → Gal(AlgebraicClosure v.Completion/v.Completion),
      (fun i ↦ infLocalDecompHom ι F (σ i)) = τ :=
    ⟨fun i ↦ Function.surjInv (infLocalDecompHom_surjective ι F) (τ i),
      funext fun i ↦ Function.surjInv_eq (infLocalDecompHom_surjective ι F) (τ i)⟩
  have h1 := congrFun (congrArg (fun c ↦ ((cochainsComplexι
    (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).f m).hom c) h) σ
  exact infLocalUnitsMor_injective ι F h1

end Level

theorem exists_infLevel_factor (m : ℕ)
    (f : (Fin m → Gal(AlgebraicClosure v.Completion/v.Completion)) →
      Additive (AlgebraicClosure v.Completion)ˣ) :
    ∃ (p : GLevel K) (z : (Fin m → MulAction.stabilizer Gal(p.1.1/K.1)
      (infPlaceOfEmbedding ι p.1 : NumberField.InfinitePlace p.1.1)) →
        ((infPlaceOfEmbedding ι p.1 : NumberField.InfinitePlace p.1.1).Completion)ˣ),
      ∀ g, infCompletionEmbedding ι p.1 (z fun i ↦ infLocalDecompHom ι p.1 (g i)) =
        ((Additive.toMul (f g) : (AlgebraicClosure v.Completion)ˣ) :
          AlgebraicClosure v.Completion) := by
  have hp := exists_level_infCompletionEmbedding_surjective ι
  obtain ⟨p, hp⟩ := hp
  have hsurj := hp p le_rfl
  have hinj := infLocalDecompHom_injective ι p.1 hsurj
  have hval : ∀ g, ∃ z : ((infPlaceOfEmbedding ι p.1 : NumberField.InfinitePlace p.1.1).Completion)ˣ,
      infCompletionEmbedding ι p.1 z = ((Additive.toMul (f g) :
        (AlgebraicClosure v.Completion)ˣ) : AlgebraicClosure v.Completion) := by
    intro g
    have hy := hsurj ((Additive.toMul (f g) : (AlgebraicClosure v.Completion)ˣ) :
      AlgebraicClosure v.Completion)
    obtain ⟨y, hy⟩ := hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy
      exact (Additive.toMul (f g) : (AlgebraicClosure v.Completion)ˣ).ne_zero hy.symm
    exact ⟨Units.mk0 y hy0, by rw [Units.val_mk0, hy]⟩
  choose z hz using hval
  refine ⟨p, fun τ ↦ z fun i ↦ Function.surjInv (infLocalDecompHom_surjective ι p.1) (τ i),
    fun g ↦ ?_⟩
  have hg : (fun i ↦ Function.surjInv (infLocalDecompHom_surjective ι p.1)
      (infLocalDecompHom ι p.1 (g i))) = g :=
    funext fun i ↦ hinj (Function.surjInv_eq (infLocalDecompHom_surjective ι p.1) _)
  change infCompletionEmbedding ι p.1 (z fun i ↦ Function.surjInv
    (infLocalDecompHom_surjective ι p.1) (infLocalDecompHom ι p.1 (g i))) = _
  rw [hg]
  exact hz g

theorem exists_infLocalCochains_eq (m : ℕ)
    (x : (cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).X m) :
    ∃ (p : GLevel K) (y : (cochainsComplex (infLocalLevelRep ι p.1)).X m),
      ((infLocalCochainsInfl ι p.1).f m).hom y = x := by
  have hfac := exists_infLevel_factor ι m (((cochainsComplexι (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).f m).hom x)
  obtain ⟨p, z, hz⟩ := hfac
  refine ⟨p, ⟨fun τ ↦ Additive.ofMul (z τ), IsLocallyConstant.of_discrete _⟩, ?_⟩
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).f m)).1 inferInstance
  funext g
  exact congrArg Additive.ofMul (Units.ext ((infLocalUnitsMor_hom_apply ι p.1 _).trans (hz g)))

section Transition

variable {F E : FiniteSubfield} [Fact (K ≤ F)] [Fact (K ≤ E)] [Fact (F ≤ E)]
  [F.1.fixingSubgroup.Normal] [E.1.fixingSubgroup.Normal]

theorem infDecompRestrict_infLocalDecompHom
    (σ : Gal(AlgebraicClosure v.Completion/v.Completion)) :
    infDecompRestrict (w := infPlaceOfEmbedding ι F) (w' := infPlaceOfEmbedding ι E)
      (infLocalDecompHom ι E σ) = infLocalDecompHom ι F σ := by
  apply Subtype.ext
  rw [coe_infDecompRestrict, coe_infLocalDecompHom]
  refine ((decompHom_eq_iff (infEmbedLevel ι F) σ _).2 fun x ↦ ?_).symm
  rw [infEmbedLevel_apply, infEmbedLevel_apply]
  have h1 := coe_levelRestrict_apply (K := K) (F := F) (E := E)
    (infLocalDecompHom ι E σ : Gal(E.1/K.1)) x
  have h2 := ι_infLocalDecompHom_apply ι E σ (algebraMap F.1 E.1 x)
  rw [← h1] at h2
  exact h2

theorem infLocalUnitsMor_infCompletionUnitsRep (a : Additive ((infPlaceOfEmbedding ι F : NumberField.InfinitePlace F.1).Completion)ˣ) :
    (infLocalUnitsMor ι E).hom ((infCompletionUnitsRep (w := infPlaceOfEmbedding ι F)
      (w' := infPlaceOfEmbedding ι E)).hom a) = (infLocalUnitsMor ι F).hom a :=
  congrArg Additive.ofMul (Units.ext (infCompletionEmbedding_completionMap ι _))

theorem infLocalCochains_comp :
    cochainsMapAlong (infDecompRestrict (w := infPlaceOfEmbedding ι F) (w' := infPlaceOfEmbedding ι E))
      continuous_of_discreteTopology infCompletionUnitsRep ≫ infLocalCochainsInfl ι E =
      infLocalCochainsInfl ι F := by
  rw [← cochainsMapAlong_comp]
  ext m x : 3
  apply Subtype.ext
  funext g
  have hfun : (fun i ↦ infDecompRestrict (w := infPlaceOfEmbedding ι F) (w' := infPlaceOfEmbedding ι E)
      (infLocalDecompHom ι E (g i))) = fun i ↦ infLocalDecompHom ι F (g i) :=
    funext fun i ↦ infDecompRestrict_infLocalDecompHom ι (g i)
  exact (infLocalUnitsMor_infCompletionUnitsRep ι _).trans
    (congrArg (fun τ ↦ (infLocalUnitsMor ι F).hom
      (((cochainsComplexι (infLocalLevelRep ι F)).f m).hom x τ)) hfun)

theorem infLocalTransition_comp_infLocalInfl (n : ℕ) :
    infLocalTransition K F E (infPlaceOfEmbedding ι F) (infPlaceOfEmbedding ι E) n ≫ infLocalInfl ι E n =
      infLocalInfl ι F n := by
  have h := congrArg (fun φ ↦ HomologicalComplex.homologyMap φ n)
    (infLocalCochains_comp ι (F := F) (E := E))
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact h

end Transition

section Generic

variable (F : FiniteSubfield) [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]


set_option maxHeartbeats 4000000 in
theorem exists_infLocalInfl_eq_homologyπ (n : ℕ)
    (z : (cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).cycles n)
    (y₀ : (cochainsComplex (infLocalLevelRep ι F)).X n)
    (hy₀ : ((infLocalCochainsInfl ι F).f n).hom y₀ = ((cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).iCycles n).hom z) :
    ∃ y : cohomology (infLocalLevelRep ι F) n, (infLocalInfl ι F n).hom y =
      ((cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).homologyπ n).hom z := by
  have hd : ((cochainsComplex (infLocalLevelRep ι F)).d n (n + 1)).hom y₀ = 0 := by
    apply infLocalCochains_injective ι F (n + 1)
    rw [map_zero, hom_f_d_apply, hy₀]
    exact iCycles_d_apply _ n (n + 1) z
  obtain ⟨w, hw⟩ := exists_iCycles_eq_of_d_eq_zero _ n y₀ hd
  refine ⟨((cochainsComplex (infLocalLevelRep ι F)).homologyπ n).hom w,
    (homologyMap_homologyπ_apply (infLocalCochainsInfl ι F) n w).trans (congrArg _ ?_)⟩
  apply (ModuleCat.mono_iff_injective ((cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).iCycles n)).1 inferInstance
  rw [iCycles_cyclesMap_apply, hw, hy₀]


set_option maxHeartbeats 4000000 in
theorem exists_d_eq_of_infLocalInfl_eq_zero (n : ℕ) (w : (cochainsComplex (infLocalLevelRep ι F)).cycles n)
    (hy : (infLocalInfl ι F n).hom (((cochainsComplex (infLocalLevelRep ι F)).homologyπ n).hom w) = 0) :
    ∃ u : (cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).X ((ComplexShape.up ℕ).prev n),
      ((cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).d _ n).hom u =
        ((infLocalCochainsInfl ι F).f n).hom (((cochainsComplex (infLocalLevelRep ι F)).iCycles n).hom w) := by
  have hy' := (homologyMap_homologyπ_apply (infLocalCochainsInfl ι F) n w).symm.trans hy
  obtain ⟨u, hu⟩ := (homologyπ_eq_zero_iff _ _).1 hy'
  rw [iCycles_cyclesMap_apply] at hu
  exact ⟨u, hu⟩

end Generic

section GenericTransition

variable {F M E : FiniteSubfield} [Fact (K ≤ F)] [Fact (K ≤ M)] [Fact (K ≤ E)] [Fact (F ≤ E)]
  [Fact (M ≤ E)] [F.1.fixingSubgroup.Normal] [M.1.fixingSubgroup.Normal] [E.1.fixingSubgroup.Normal]


set_option maxHeartbeats 4000000 in
theorem infLocalTransition_homologyπ_eq_zero (n : ℕ) (w : (cochainsComplex (infLocalLevelRep ι F)).cycles n)
    (u' : (cochainsComplex (infLocalLevelRep ι M)).X ((ComplexShape.up ℕ).prev n))
    (hu : ((cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).d _ n).hom (((infLocalCochainsInfl ι M).f _).hom u') =
        ((infLocalCochainsInfl ι F).f n).hom (((cochainsComplex (infLocalLevelRep ι F)).iCycles n).hom w)) :
    (infLocalTransition K F E (infPlaceOfEmbedding ι F) (infPlaceOfEmbedding ι E) n).hom
      (((cochainsComplex (infLocalLevelRep ι F)).homologyπ n).hom w) = 0 := by
  refine (homologyMap_homologyπ_apply (cochainsMapAlong (infDecompRestrict (w := infPlaceOfEmbedding ι F)
    (w' := infPlaceOfEmbedding ι E)) continuous_of_discreteTopology infCompletionUnitsRep) n w).trans
    ((homologyπ_eq_zero_iff _ _).2 ⟨((cochainsMapAlong (infDecompRestrict (w := infPlaceOfEmbedding ι M)
      (w' := infPlaceOfEmbedding ι E)) continuous_of_discreteTopology infCompletionUnitsRep).f _).hom u',
      ?_⟩)
  rw [iCycles_cyclesMap_apply]
  apply infLocalCochains_injective ι E n
  rw [hom_f_d_apply]
  have e1 := congrArg (fun φ ↦ (φ.f _).hom u') (infLocalCochains_comp ι (F := M) (E := E))
  have e2 := congrArg (fun φ ↦ (φ.f n).hom (((cochainsComplex (infLocalLevelRep ι F)).iCycles n).hom w))
    (infLocalCochains_comp ι (F := F) (E := E))
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at e1 e2
  exact (congrArg (fun c ↦ ((cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).d _ n).hom c) e1).trans (hu.trans e2.symm)

end GenericTransition


set_option maxHeartbeats 4000000 in
theorem exists_infLocalInfl_eq (n : ℕ)
    (x : cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) n) :
    ∃ (p : GLevel K) (y : cohomology (infLocalLevelRep ι p.1) n), (infLocalInfl ι p.1 n).hom y = x := by
  have hz := (ModuleCat.epi_iff_surjective ((cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).homologyπ n)).1 inferInstance x
  obtain ⟨z, rfl⟩ := hz
  have hc := exists_infLocalCochains_eq ι n (((cochainsComplex (galUnitsZ v.Completion (AlgebraicClosure v.Completion))).iCycles n).hom z)
  obtain ⟨p, y₀, hy₀⟩ := hc
  have hy := exists_infLocalInfl_eq_homologyπ ι p.1 n z y₀ hy₀
  obtain ⟨y, hy⟩ := hy
  exact ⟨p, y, hy⟩


set_option maxHeartbeats 4000000 in
theorem exists_infLocalTransition_eq_zero (n : ℕ) (p : GLevel K) (y : cohomology (infLocalLevelRep ι p.1) n)
    (hy : (infLocalInfl ι p.1 n).hom y = 0) :
    ∃ (q : GLevel K) (h : p ≤ q), (haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
      (infLocalTransition K p.1 q.1 (infPlaceOfEmbedding ι p.1) (infPlaceOfEmbedding ι q.1) n).hom y) = 0 := by
  have hw := (ModuleCat.epi_iff_surjective
    ((cochainsComplex (infLocalLevelRep ι p.1)).homologyπ n)).1 inferInstance y
  obtain ⟨w, rfl⟩ := hw
  have hu := exists_d_eq_of_infLocalInfl_eq_zero ι p.1 n w hy
  obtain ⟨u, hu⟩ := hu
  have hq := exists_infLocalCochains_eq ι _ u
  obtain ⟨q, u', hu'⟩ := hq
  have hr := GLevel.exists_ge p q
  obtain ⟨r, hpr, hqr⟩ := hr
  have : Fact (p.1 ≤ r.1) := ⟨hpr⟩
  have : Fact (q.1 ≤ r.1) := ⟨hqr⟩
  exact ⟨r, hpr, infLocalTransition_homologyπ_eq_zero ι (M := q.1) n w u' (by rw [hu', hu])⟩

end

end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.Places
section -- merged from GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.Components
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField IsDedekindDomain GroundTheory.Global
  GroundTheory.Global.AdeleBaseChange FiniteSubfield IdeleLimit SemiLocal GroundTheory.Global.IdeleGroup

open scoped Pointwise NumberField.LiesOver NumberField.AdeleRing

noncomputable section

set_option synthInstance.maxHeartbeats 200000

variable {K F : FiniteSubfield} [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

section Finite

variable {v : HeightOneSpectrum (𝓞 K.1)} (w : PlacesOver F.1 v)

theorem finiteProj_smul_of_mem_stabilizer (σ : MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal)
    (x : IdeleGroup F.1) :
    finiteProj w.1 ((σ : F.1 ≃ₐ[K.1] F.1) • x) = σ • finiteProj w.1 x := by
  apply Units.ext
  have h : w.1 = (σ : F.1 ≃ₐ[K.1] F.1) • w.1 :=
    (congrArg Subtype.val ((mem_stabilizer_iff_smul_eq v w σ).1 σ.2)).symm
  rw [coe_finiteProj, coe_smul_idele, smul_snd_eq_galHom _ _ w.1 w.1 h, galHom_eq_decomposition]
  rfl

def finiteComponentRep :
    Rep.res (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal).subtype (ideleRep K.1 F.1) ⟶
      Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal)
        (w.1.adicCompletion F.1)ˣ :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (finiteProj w.1)).toIntLinearMap, fun σ => LinearMap.ext fun x =>
    congrArg Additive.ofMul (finiteProj_smul_of_mem_stabilizer w σ x.toMul)⟩

def finiteComponent (n : ℕ) :
    cohomology (ideleRep K.1 F.1) n ⟶
      cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal)
        (w.1.adicCompletion F.1)ˣ) n :=
  cohomologyMapAlong (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal).subtype
    continuous_of_discreteTopology (finiteComponentRep w) n


set_option maxHeartbeats 4000000 in
theorem placeProj_comp_finiteShapiroIso (n : ℕ) :
    cohomologyMap (finiteProjAboveRep (K := K.1) (L := F.1) v) n ≫ (finiteShapiroIso v w n).hom =
      finiteComponent w n := by
  change HomologicalComplex.homologyMap (cochainsMap (finiteProjAboveRep (K := K.1) (L := F.1) v)) n ≫
      (HomologicalComplex.homologyMap (cochainsMapAlong _ (continuous_subgroup_subtype _)
        (orbitProj (permutesFactors_finiteUnitsAboveRep v)
          (mem_stabilizer_iff_smul_eq v w))) n ≫
      HomologicalComplex.homologyMap (cochainsMap (stabRepFiniteIso v w).hom) n) = _
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  congr 1


omit [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal] in
theorem ideleEmbedding_snd_of_below_eq {E : FiniteSubfield} [Algebra F.1 E.1]
    (w' : HeightOneSpectrum (𝓞 E.1)) (u : HeightOneSpectrum (𝓞 F.1)) (hu : below F.1 w' = u)
    [w'.asIdeal.LiesOver u.asIdeal] (x : IdeleGroup F.1) :
    ((ideleEmbedding F.1 E.1 x : IdeleGroup E.1) : 𝔸[E.1]).2 w' =
      SemiLocal.completionMap u w' ((x : 𝔸[F.1]).2 u) := by
  subst hu
  rfl

variable {E : FiniteSubfield} [Fact (K ≤ E)] [Fact (F ≤ E)] [E.1.fixingSubgroup.Normal]


set_option maxHeartbeats 2000000 in
theorem levelTransition_comp_finiteComponent (w' : PlacesOver E.1 v)
    [w'.1.asIdeal.LiesOver w.1.asIdeal] (n : ℕ) :
    levelTransition K F E n ≫ finiteComponent w' n =
      finiteComponent w n ≫ localTransition K F E w w' n := by
  unfold levelTransition finiteComponent localTransition cohomologyMapAlong
  refine (HomologicalComplex.homologyMap_comp _ _ n).symm.trans ?_
  refine Eq.trans ?_ (HomologicalComplex.homologyMap_comp _ _ n)
  congr 1
  ext m x : 3
  apply Subtype.ext
  funext g
  apply Additive.toMul.injective
  apply Units.ext
  change ((ideleEmbedding F.1 E.1 _ : IdeleGroup E.1) : 𝔸[E.1]).2 w'.1 =
    SemiLocal.completionMap w.1 w'.1 _
  exact ideleEmbedding_snd_of_below_eq w'.1 w.1 ((below_eq_iff w'.1 w.1).2 inferInstance) _

end Finite

section Infinite

variable {v : InfinitePlace K.1} (w : v.placesOver F.1)

omit [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal] in
theorem fst_eq_completionCongr (a : 𝔸[F.1]) {u u' : InfinitePlace F.1} (h : u = u') :
    a.1 u' = completionCongr h (a.1 u) := by
  subst h
  rfl

omit [F.1.fixingSubgroup.Normal] in
theorem eq_comap_of_mem_stabilizer (σ : MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1) :
    w.1 = w.1.comap (((σ : F.1 ≃ₐ[K.1] F.1) : F.1 ≃+* F.1) : F.1 →+* F.1) := by
  rw [comap_eq_inv_smul]
  exact (MulAction.mem_stabilizer_iff.1 (inv_mem σ.2)).symm

theorem infiniteProj_smul_of_mem_stabilizer (σ : MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1)
    (x : IdeleGroup F.1) :
    infiniteProj w.1 ((σ : F.1 ≃ₐ[K.1] F.1) • x) = σ • infiniteProj w.1 x := by
  apply Units.ext
  rw [coe_infiniteProj, coe_smul_idele, smul_fst,
    fst_eq_completionCongr _ (eq_comap_of_mem_stabilizer w σ), infiniteCompletionMap_eq_decomposition]
  rfl

def infiniteComponentRep :
    Rep.res (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1).subtype (ideleRep K.1 F.1) ⟶
      Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1) (w.1.Completion)ˣ :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (infiniteProj w.1)).toIntLinearMap, fun σ => LinearMap.ext fun x =>
    congrArg Additive.ofMul (infiniteProj_smul_of_mem_stabilizer w σ x.toMul)⟩

def infiniteComponent (n : ℕ) :
    cohomology (ideleRep K.1 F.1) n ⟶
      cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1)
        (w.1.Completion)ˣ) n :=
  cohomologyMapAlong (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1).subtype
    continuous_of_discreteTopology (infiniteComponentRep w) n


set_option maxHeartbeats 2000000 in
theorem placeProj_comp_infiniteShapiroIso (n : ℕ) :
    cohomologyMap (infiniteProjAboveRep (K := K.1) (L := F.1) v) n ≫ (infiniteShapiroIso v w n).hom =
      infiniteComponent w n := by
  change HomologicalComplex.homologyMap (cochainsMap (infiniteProjAboveRep (K := K.1) (L := F.1) v)) n ≫
      (HomologicalComplex.homologyMap (cochainsMapAlong _ (continuous_subgroup_subtype _)
        (orbitProj (permutesFactors_infiniteUnitsAboveRep v)
          (mem_stabilizer_iff_smul_eq_infinite v w))) n ≫
      HomologicalComplex.homologyMap (cochainsMap (stabRepInfiniteIso v w).hom) n) = _
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  congr 1


omit [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal] in
theorem ideleEmbedding_fst_of_comap_eq {E : FiniteSubfield} [Algebra F.1 E.1]
    (w' : InfinitePlace E.1) (u : InfinitePlace F.1) (hu : w'.comap (algebraMap F.1 E.1) = u)
    [w'.LiesOver u] (x : IdeleGroup F.1) :
    ((ideleEmbedding F.1 E.1 x : IdeleGroup E.1) : 𝔸[E.1]).1 w' =
      AbsoluteValue.Completion.map u.1 w'.1 ((x : 𝔸[F.1]).1 u) := by
  subst hu
  exact (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply (x : 𝔸[F.1]).1 w').trans
    (AbsoluteValue.Completion.algebraMap_apply_of_liesOver
      (w'.comap (algebraMap F.1 E.1)).1 w'.1 _)

variable {E : FiniteSubfield} [Fact (K ≤ E)] [Fact (F ≤ E)] [E.1.fixingSubgroup.Normal]


set_option maxHeartbeats 2000000 in
theorem levelTransition_comp_infiniteComponent (w' : v.placesOver E.1) [w'.1.LiesOver w.1] (n : ℕ) :
    levelTransition K F E n ≫ infiniteComponent w' n =
      infiniteComponent w n ≫ infLocalTransition K F E w w' n := by
  unfold levelTransition infiniteComponent infLocalTransition cohomologyMapAlong
  refine (HomologicalComplex.homologyMap_comp _ _ n).symm.trans ?_
  refine Eq.trans ?_ (HomologicalComplex.homologyMap_comp _ _ n)
  congr 1
  ext m x : 3
  apply Subtype.ext
  funext g
  apply Additive.toMul.injective
  apply Units.ext
  change ((ideleEmbedding F.1 E.1 _ : IdeleGroup E.1) : 𝔸[E.1]).1 w'.1 =
    AbsoluteValue.Completion.map w.1.1 w'.1.1 _
  exact ideleEmbedding_fst_of_comap_eq w'.1 w.1 (InfinitePlace.LiesOver.comap_eq w'.1 w.1) _

end Infinite

end

end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.Assembly
section -- merged from GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.LevelsTrans
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global GroundTheory.Global.AdeleBaseChange
  FiniteSubfield IdeleLimit

noncomputable section

variable {K F E M : FiniteSubfield} [Fact (K ≤ F)] [Fact (K ≤ E)] [Fact (K ≤ M)] [Fact (F ≤ E)]
  [Fact (E ≤ M)] [Fact (F ≤ M)] [F.1.fixingSubgroup.Normal] [E.1.fixingSubgroup.Normal]
  [M.1.fixingSubgroup.Normal]

theorem levelRestrict_levelRestrict (τ : M.1 ≃ₐ[K.1] M.1) :
    levelRestrict K F E (levelRestrict K E M τ) = levelRestrict K F M τ := by
  ext x
  have h1 := congrArg Subtype.val (coe_levelRestrict_apply (K := K) (F := F) (E := E)
    (levelRestrict K E M τ) x)
  have h2 := congrArg Subtype.val (coe_levelRestrict_apply (K := K) (F := E) (E := M) τ
    (algebraMap F.1 E.1 x))
  have h3 := congrArg Subtype.val (coe_levelRestrict_apply (K := K) (F := F) (E := M) τ x)
  exact h1.trans (h2.trans h3.symm)


set_option maxHeartbeats 2000000 in
theorem levelTransition_comp_levelTransition (n : ℕ) :
    levelTransition K F E n ≫ levelTransition K E M n = levelTransition K F M n := by
  unfold levelTransition cohomologyMapAlong
  refine (HomologicalComplex.homologyMap_comp _ _ n).symm.trans ?_
  congr 1
  ext m x : 3
  apply Subtype.ext
  funext g
  change Additive.ofMul (ideleMap (Fact.out : E ≤ M) (ideleMap (Fact.out : F ≤ E)
      ((x.1 fun i => levelRestrict K F E (levelRestrict K E M (g i))).toMul))) =
    Additive.ofMul (ideleMap (Fact.out : F ≤ M) ((x.1 fun i => levelRestrict K F M (g i)).toMul))
  have hfun : (fun i => levelRestrict K F E (levelRestrict K E M (g i))) =
      fun i => levelRestrict K F M (g i) := funext fun i => levelRestrict_levelRestrict (g i)
  refine (congrArg Additive.ofMul (ideleMap_ideleMap (Fact.out : F ≤ E) (Fact.out : E ≤ M) _)).trans ?_
  rw [hfun]

end

end GroundTheory.ProfCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField GroundTheory.Global FiniteSubfield IdeleLimit DirectSum

noncomputable section

variable {K : FiniteSubfield} (n : ℕ)

abbrev levelTransitionG {p q : GLevel K} (h : p ≤ q) :
    cohomology (ideleRep K.1 p.1.1) n ⟶ cohomology (ideleRep K.1 q.1.1) n :=
  haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
  levelTransition K p.1 q.1 n

theorem levelTransitionG_comp_levelInfl {p q : GLevel K} (h : p ≤ q) (y : cohomology (ideleRep K.1 p.1.1) n) :
    (levelInfl K q.1 n).hom ((levelTransitionG n h).hom y) = (levelInfl K p.1 n).hom y := by
  haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
  exact congrArg (fun φ => φ.hom y) (levelTransition_comp_levelInfl (K := K) (F := p.1) (E := q.1) n)

theorem levelTransitionG_trans {p q r : GLevel K} (h₁ : p ≤ q) (h₂ : q ≤ r)
    (y : cohomology (ideleRep K.1 p.1.1) n) :
    (levelTransitionG n h₂).hom ((levelTransitionG n h₁).hom y) =
      (levelTransitionG n (h₁.trans h₂)).hom y := by
  haveI : Fact (p.1 ≤ q.1) := ⟨h₁⟩
  haveI : Fact (q.1 ≤ r.1) := ⟨h₂⟩
  haveI : Fact (p.1 ≤ r.1) := ⟨h₁.trans h₂⟩
  exact congrArg (fun φ => φ.hom y)
    (levelTransition_comp_levelTransition (K := K) (F := p.1) (E := q.1) (M := r.1) n)


variable (K) in
structure LevelDecomposition where

  L : Place K.1 → GLevel K → Type
  [grp : ∀ v p, AddCommGroup (L v p)]

  e : ∀ v (p : GLevel K), cohomology (placeRep p.1.1 v) n ≃+ L v p

  lt : ∀ v {p q : GLevel K}, p ≤ q → L v p →+ L v q

  compat : ∀ v {p q : GLevel K} (h : p ≤ q) (y : cohomology (ideleRep K.1 p.1.1) n),
    e v q ((cohomologyMap (placeProj v) n).hom ((levelTransitionG n h).hom y)) =
      lt v h (e v p ((cohomologyMap (placeProj v) n).hom y))

attribute [instance] LevelDecomposition.grp

structure LocalLimit {n : ℕ} (D : LevelDecomposition K n) where

  T : Place K.1 → Type
  [grp : ∀ v, AddCommGroup (T v)]

  infl : ∀ v (p : GLevel K), D.L v p →+ T v
  infl_compat : ∀ v {p q : GLevel K} (h : p ≤ q) (z : D.L v p), infl v q (D.lt v h z) = infl v p z
  exists_infl : ∀ v (t : T v), ∃ (p : GLevel K) (z : D.L v p), infl v p z = t
  exists_lt_eq_zero : ∀ v (p : GLevel K) (z : D.L v p), infl v p z = 0 →
    ∃ (q : GLevel K) (h : p ≤ q), D.lt v h z = 0

attribute [instance] LocalLimit.grp

variable {n} (D : LevelDecomposition K n) (T : LocalLimit D) (hn : 1 ≤ n)


include hn in
def levelSum (p : GLevel K) : cohomology (ideleRep K.1 p.1.1) n →+ ⨁ v : Place K.1, T.T v :=
  (DFinsupp.mapRange.addMonoidHom fun v => (T.infl v p).comp (D.e v p).toAddMonoidHom).comp
    (idelesCohomologyEquiv hn).symm.toAddMonoidHom

theorem levelSum_apply (p : GLevel K) (y : cohomology (ideleRep K.1 p.1.1) n) (v : Place K.1) :
    levelSum D T hn p y v = T.infl v p (D.e v p ((cohomologyMap (placeProj v) n).hom y)) := by
  change T.infl v p (D.e v p ((idelesCohomologyEquiv hn).symm y v)) = _
  rw [idelesCohomologyEquiv_symm_apply]

theorem levelSum_levelTransition {p q : GLevel K} (h : p ≤ q) (y : cohomology (ideleRep K.1 p.1.1) n) :
    levelSum D T hn q ((levelTransitionG n h).hom y) = levelSum D T hn p y := by
  ext v
  rw [levelSum_apply, levelSum_apply, D.compat, T.infl_compat]

theorem levelSum_eq_of_levelInfl_eq {p q : GLevel K} (y : cohomology (ideleRep K.1 p.1.1) n)
    (y' : cohomology (ideleRep K.1 q.1.1) n)
    (h : (levelInfl K p.1 n).hom y = (levelInfl K q.1 n).hom y') :
    levelSum D T hn p y = levelSum D T hn q y' := by
  obtain ⟨r, hpr, hqr⟩ := GLevel.exists_ge p q
  have hz : (levelInfl K r.1 n).hom
      ((levelTransitionG n hpr).hom y - (levelTransitionG n hqr).hom y') = 0 := by
    rw [map_sub, levelTransitionG_comp_levelInfl, levelTransitionG_comp_levelInfl, h, sub_self]
  obtain ⟨s, hrs, hs⟩ := exists_levelTransition_eq_zero n r _ hz
  have hs' : (levelTransitionG n hrs).hom
      ((levelTransitionG n hpr).hom y - (levelTransitionG n hqr).hom y') = 0 := hs
  rw [map_sub, sub_eq_zero] at hs'
  rw [← levelSum_levelTransition D T hn hpr, ← levelSum_levelTransition D T hn hrs, hs',
    levelSum_levelTransition, levelSum_levelTransition]

def pick (x : cohomology (limitRep K) n) : Σ p : GLevel K, cohomology (ideleRep K.1 p.1.1) n :=
  ⟨(exists_levelInfl_eq n x).choose, (exists_levelInfl_eq n x).choose_spec.choose⟩

theorem levelInfl_pick (x : cohomology (limitRep K) n) :
    (levelInfl K (pick x).1.1 n).hom (pick x).2 = x :=
  (exists_levelInfl_eq n x).choose_spec.choose_spec

def limitCohomologyFun (x : cohomology (limitRep K) n) : ⨁ v : Place K.1, T.T v :=
  levelSum D T hn (pick x).1 (pick x).2

theorem limitCohomologyFun_eq (p : GLevel K) (y : cohomology (ideleRep K.1 p.1.1) n)
    (x : cohomology (limitRep K) n) (h : (levelInfl K p.1 n).hom y = x) :
    limitCohomologyFun D T hn x = levelSum D T hn p y :=
  levelSum_eq_of_levelInfl_eq D T hn (pick x).2 y ((levelInfl_pick x).trans h.symm)

set_option maxHeartbeats 4000000 in
theorem limitCohomologyFun_add (x₁ x₂ : cohomology (limitRep K) n) :
    limitCohomologyFun D T hn (x₁ + x₂) = limitCohomologyFun D T hn x₁ + limitCohomologyFun D T hn x₂ := by
  obtain ⟨p₁, y₁, rfl⟩ := exists_levelInfl_eq n x₁
  obtain ⟨p₂, y₂, rfl⟩ := exists_levelInfl_eq n x₂
  obtain ⟨r, h1r, h2r⟩ := GLevel.exists_ge p₁ p₂
  have hsum : (levelInfl K r.1 n).hom ((levelTransitionG n h1r).hom y₁ +
      (levelTransitionG n h2r).hom y₂) = (levelInfl K p₁.1 n).hom y₁ + (levelInfl K p₂.1 n).hom y₂ := by
    rw [map_add (f := _), levelTransitionG_comp_levelInfl, levelTransitionG_comp_levelInfl]
  rw [limitCohomologyFun_eq D T hn p₁ y₁ _ rfl, limitCohomologyFun_eq D T hn p₂ y₂ _ rfl,
    limitCohomologyFun_eq D T hn r _ _ hsum, map_add, levelSum_levelTransition, levelSum_levelTransition]

def limitCohomologyHom : cohomology (limitRep K) n →+ ⨁ v : Place K.1, T.T v :=
  AddMonoidHom.mk' (limitCohomologyFun D T hn) (limitCohomologyFun_add D T hn)

theorem limitCohomologyHom_levelInfl (p : GLevel K) (y : cohomology (ideleRep K.1 p.1.1) n) :
    limitCohomologyHom D T hn ((levelInfl K p.1 n).hom y) = levelSum D T hn p y :=
  limitCohomologyFun_eq D T hn p y _ rfl

theorem eq_zero_of_forall_placeProj {n : ℕ} (hn : 1 ≤ n) (p : GLevel K) (y : cohomology (ideleRep K.1 p.1.1) n)
    (h : ∀ v : Place K.1, (cohomologyMap (placeProj v) n).hom y = 0) : y = 0 := by
  apply (idelesCohomologyEquiv hn).symm.injective
  rw [map_zero]
  ext v
  rw [idelesCohomologyEquiv_symm_apply, h v]
  rfl

theorem limitCohomologyHom_injective : Function.Injective (limitCohomologyHom D T hn) := by
  classical
  refine (injective_iff_map_eq_zero (limitCohomologyHom D T hn)).2 fun x hx => ?_
  obtain ⟨p, y, rfl⟩ := exists_levelInfl_eq n x
  rw [limitCohomologyHom_levelInfl] at hx
  have hv : ∀ v, T.infl v p (D.e v p ((cohomologyMap (placeProj v) n).hom y)) = 0 := fun v => by
    have := congrArg (fun ζ : ⨁ v : Place K.1, T.T v => ζ v) hx
    rw [levelSum_apply] at this
    exact this
  choose q hpq hq using fun v => T.exists_lt_eq_zero v p _ (hv v)
  obtain ⟨r, hr⟩ := Finset.exists_le (insert p (((idelesCohomologyEquiv hn).symm y).support.image q))
  have hpr : p ≤ r := hr _ (Finset.mem_insert_self _ _)
  have hzero : (levelTransitionG n hpr).hom y = 0 := by
    refine eq_zero_of_forall_placeProj hn r _ fun v => (D.e v r).injective ?_
    rw [map_zero]
    by_cases hvS : v ∈ ((idelesCohomologyEquiv hn).symm y).support
    · have hqr : q v ≤ r := hr _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hvS))
      rw [← levelTransitionG_trans n (hpq v) hqr, D.compat, D.compat, hq v, map_zero]
    · have h0 : (cohomologyMap (placeProj v) n).hom y = 0 := by
        rw [← idelesCohomologyEquiv_symm_apply hn]
        exact DFinsupp.notMem_support_iff.1 hvS
      rw [D.compat, h0, map_zero, map_zero]
  rw [← levelTransitionG_comp_levelInfl n hpr, hzero, map_zero]

theorem limitCohomologyHom_surjective : Function.Surjective (limitCohomologyHom D T hn) := by
  classical
  intro ζ
  choose p z hz using fun v => T.exists_infl v (ζ v)
  obtain ⟨p₀⟩ := (inferInstance : Nonempty (GLevel K))
  obtain ⟨r, hr⟩ := Finset.exists_le (insert p₀ (ζ.support.image p))
  have hpr : ∀ v ∈ ζ.support, p v ≤ r := fun v hv =>
    hr _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hv))
  let ξ : ⨁ v : Place K.1, cohomology (placeRep r.1.1 v) n :=
    DFinsupp.mk ζ.support fun v => (D.e v.1 r).symm (D.lt v.1 (hpr v.1 v.2) (z v.1))
  refine ⟨(levelInfl K r.1 n).hom (idelesCohomologyEquiv hn ξ), ?_⟩
  rw [limitCohomologyHom_levelInfl]
  ext v
  rw [levelSum_apply, ← idelesCohomologyEquiv_symm_apply hn, AddEquiv.symm_apply_apply]
  by_cases hv : v ∈ ζ.support
  · have : ξ v = (D.e v r).symm (D.lt v (hpr v hv) (z v)) := by
      simp only [ξ, DFinsupp.mk_apply, dif_pos hv]
    rw [this, AddEquiv.apply_symm_apply, T.infl_compat, hz]
  · have : ξ v = 0 := by
      simp only [ξ, DFinsupp.mk_apply, dif_neg hv]
    rw [this, map_zero, map_zero, DFinsupp.notMem_support_iff.1 hv]

def limitCohomologyEquiv : cohomology (limitRep K) n ≃+ ⨁ v : Place K.1, T.T v :=
  AddEquiv.ofBijective (limitCohomologyHom D T hn)
    ⟨limitCohomologyHom_injective D T hn, limitCohomologyHom_surjective D T hn⟩

theorem limitCohomologyEquiv_levelInfl (p : GLevel K) (y : cohomology (ideleRep K.1 p.1.1) n)
    (v : Place K.1) :
    limitCohomologyEquiv D T hn ((levelInfl K p.1 n).hom y) v =
      T.infl v p (D.e v p ((cohomologyMap (placeProj v) n).hom y)) := by
  change limitCohomologyHom D T hn _ v = _
  rw [limitCohomologyHom_levelInfl, levelSum_apply]

end

end GroundTheory.ProfCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField IsDedekindDomain GroundTheory.Global FiniteSubfield
  IdeleLimit SemiLocal

open scoped Pointwise NumberField.LiesOver

noncomputable section

variable (K : FiniteSubfield)

structure CompatiblePlaces where

  fin : ∀ (v : HeightOneSpectrum (𝓞 K.1)) (p : GLevel K), PlacesOver p.1.1 v
  fin_liesOver : ∀ v {p q : GLevel K} (h : p ≤ q),
    haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
    (fin v q).1.asIdeal.LiesOver (fin v p).1.asIdeal

  inf : ∀ (v : InfinitePlace K.1) (p : GLevel K), v.placesOver p.1.1
  inf_liesOver : ∀ v {p q : GLevel K} (h : p ≤ q),
    haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
    (inf v q).1.LiesOver (inf v p).1

namespace CompatiblePlaces

variable {K} (P : CompatiblePlaces K) (n : ℕ)

def localGroup : Place K.1 → GLevel K → Type
  | .inl v, p => cohomology (Rep.ofMulDistribMulAction
      (MulAction.stabilizer (p.1.1 ≃ₐ[K.1] p.1.1) (P.inf v p).1) ((P.inf v p).1.Completion)ˣ) n
  | .inr v, p => cohomology (Rep.ofMulDistribMulAction
      (MulAction.stabilizer (p.1.1 ≃ₐ[K.1] p.1.1) (P.fin v p).1.asIdeal)
      ((P.fin v p).1.adicCompletion p.1.1)ˣ) n

instance (v : Place K.1) (p : GLevel K) : AddCommGroup (P.localGroup n v p) := by
  rcases v with v | v <;> exact inferInstanceAs (AddCommGroup (cohomology _ n))

def shapiro : ∀ (v : Place K.1) (p : GLevel K), cohomology (placeRep p.1.1 v) n ≃+ P.localGroup n v p
  | .inl v, p => (infiniteShapiroIso v (P.inf v p) n).toLinearEquiv.toAddEquiv
  | .inr v, p => (finiteShapiroIso v (P.fin v p) n).toLinearEquiv.toAddEquiv

def transition : ∀ (v : Place K.1) {p q : GLevel K}, p ≤ q → P.localGroup n v p →+ P.localGroup n v q
  | .inl v, p, q, h =>
    haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
    haveI := P.inf_liesOver v h
    (infLocalTransition K p.1 q.1 (P.inf v p) (P.inf v q) n).hom.toAddMonoidHom
  | .inr v, p, q, h =>
    haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
    haveI := P.fin_liesOver v h
    (localTransition K p.1 q.1 (P.fin v p) (P.fin v q) n).hom.toAddMonoidHom

set_option maxHeartbeats 4000000 in
theorem shapiro_placeProj_inr (v : HeightOneSpectrum (𝓞 K.1)) (p : GLevel K)
    (y : cohomology (ideleRep K.1 p.1.1) n) :
    P.shapiro n (.inr v) p ((cohomologyMap (placeProj (.inr v)) n).hom y) =
      (finiteComponent (P.fin v p) n).hom y := by
  change (finiteShapiroIso v (P.fin v p) n).hom.hom
    ((cohomologyMap (finiteProjAboveRep (K := K.1) (L := p.1.1) v) n).hom y) = _
  rw [← placeProj_comp_finiteShapiroIso (P.fin v p) n]
  rfl

set_option maxHeartbeats 4000000 in
theorem shapiro_placeProj_inl (v : InfinitePlace K.1) (p : GLevel K)
    (y : cohomology (ideleRep K.1 p.1.1) n) :
    P.shapiro n (.inl v) p ((cohomologyMap (placeProj (.inl v)) n).hom y) =
      (infiniteComponent (P.inf v p) n).hom y := by
  change (infiniteShapiroIso v (P.inf v p) n).hom.hom
    ((cohomologyMap (infiniteProjAboveRep (K := K.1) (L := p.1.1) v) n).hom y) = _
  rw [← placeProj_comp_infiniteShapiroIso (P.inf v p) n]
  rfl


set_option maxHeartbeats 8000000 in
def levelDecomposition : LevelDecomposition K n where
  L := P.localGroup n
  e := P.shapiro n
  lt := P.transition n
  compat v p q h y := by
    rcases v with v | v
    · haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
      haveI := P.inf_liesOver v h
      rw [shapiro_placeProj_inl, shapiro_placeProj_inl]
      exact congrArg (fun φ => φ.hom y)
        (levelTransition_comp_infiniteComponent (P.inf v p) (P.inf v q) n)
    · haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
      haveI := P.fin_liesOver v h
      rw [shapiro_placeProj_inr, shapiro_placeProj_inr]
      exact congrArg (fun φ => φ.hom y)
        (levelTransition_comp_finiteComponent (P.fin v p) (P.fin v q) n)

end CompatiblePlaces

end

end GroundTheory.ProfCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField IsDedekindDomain GroundTheory.Global FiniteSubfield
  IdeleLimit DirectSum

open scoped Pointwise NumberField.LiesOver

noncomputable section

variable (K : FiniteSubfield)

structure LocalEmbeddings where

  fin : ∀ v : HeightOneSpectrum (𝓞 K.1), AlgebraicClosure ℚ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1)

  inf : ∀ v : InfinitePlace K.1, AlgebraicClosure ℚ →ₐ[K.1] AlgebraicClosure v.Completion

theorem nonempty_localEmbeddings : Nonempty (LocalEmbeddings K) :=
  ⟨⟨fun _ => Classical.choice nonempty_algHom_of_isSepClosed,
    fun _ => Classical.choice nonempty_algHom_of_isSepClosed⟩⟩

variable {K}

namespace LocalEmbeddings

variable (ι : LocalEmbeddings K)

def places : CompatiblePlaces K where
  fin v p := placeOfEmbedding (ι.fin v) p.1
  fin_liesOver v {p q} h := by
    haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
    exact liesOver_placeOfEmbedding (ι.fin v)
  inf v p := infPlaceOfEmbedding (ι.inf v) p.1
  inf_liesOver v {p q} h := by
    haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
    exact liesOver_infPlaceOfEmbedding (ι.inf v)

end LocalEmbeddings


variable (K) in
def localGaloisCohomology (n : ℕ) : Place K.1 → Type
  | .inl v => cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) n
  | .inr v => cohomology (galUnitsZ (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) n

instance (n : ℕ) (v : Place K.1) : AddCommGroup (localGaloisCohomology K n v) := by
  rcases v with v | v <;> exact inferInstanceAs (AddCommGroup (cohomology _ n))

namespace LocalEmbeddings

variable (ι : LocalEmbeddings K) (n : ℕ)

def localInflHom : ∀ (v : Place K.1) (p : GLevel K),
    (ι.places.levelDecomposition n).L v p →+ localGaloisCohomology K n v
  | .inl v, p => (infLocalInfl (ι.inf v) p.1 n).hom.toAddMonoidHom
  | .inr v, p => (localInfl (ι.fin v) p.1 n).hom.toAddMonoidHom


set_option maxHeartbeats 8000000 in
def localLimit : LocalLimit (ι.places.levelDecomposition n) where
  T := localGaloisCohomology K n
  infl := ι.localInflHom n
  infl_compat v p q h z := by
    rcases v with v | v
    · haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
      exact congrArg (fun φ => φ.hom z) (infLocalTransition_comp_infLocalInfl (ι.inf v) (F := p.1) (E := q.1) n)
    · haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
      exact congrArg (fun φ => φ.hom z) (localTransition_comp_localInfl (ι.fin v) (F := p.1) (E := q.1) n)
  exists_infl v t := by
    rcases v with v | v
    · have h := exists_infLocalInfl_eq (ι.inf v) n t
      obtain ⟨p, y, hy⟩ := h
      exact ⟨p, y, hy⟩
    · have h := exists_localInfl_eq (ι.fin v) n t
      obtain ⟨p, y, hy⟩ := h
      exact ⟨p, y, hy⟩
  exists_lt_eq_zero v p z hz := by
    rcases v with v | v
    · have h := exists_infLocalTransition_eq_zero (ι.inf v) n p z hz
      obtain ⟨q, hpq, hq⟩ := h
      exact ⟨q, hpq, hq⟩
    · have h := exists_localTransition_eq_zero (ι.fin v) n p z hz
      obtain ⟨q, hpq, hq⟩ := h
      exact ⟨q, hpq, hq⟩

end LocalEmbeddings

def idelesLimitCohomologyEquiv (ι : LocalEmbeddings K) {n : ℕ} (hn : 1 ≤ n) :
    cohomology (limitRep K) n ≃+ ⨁ v : Place K.1, localGaloisCohomology K n v :=
  limitCohomologyEquiv (ι.places.levelDecomposition n) (ι.localLimit n) hn

theorem idelesLimitCohomologyEquiv_levelInfl (ι : LocalEmbeddings K) {n : ℕ} (hn : 1 ≤ n) (p : GLevel K)
    (y : cohomology (ideleRep K.1 p.1.1) n) (v : Place K.1) :
    idelesLimitCohomologyEquiv ι hn ((levelInfl K p.1 n).hom y) v =
      ι.localInflHom n v p (ι.places.shapiro n v p ((cohomologyMap (placeProj v) n).hom y)) :=
  limitCohomologyEquiv_levelInfl _ _ hn p y v

end

end GroundTheory.ProfCoh
