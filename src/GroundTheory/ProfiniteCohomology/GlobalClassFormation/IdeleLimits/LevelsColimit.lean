module

public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.Levels
public import GroundTheory.ProfiniteCohomology.InflationRestriction.DegreeOne

@[expose] public section

section -- merged from GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.LevelsColimit
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global GroundTheory.Global.AdeleBaseChange
  FiniteSubfield IdeleLimit

noncomputable section

variable (K : FiniteSubfield)

instance compactSpace_fixingSubgroup : CompactSpace K.1.fixingSubgroup :=
  isCompact_iff_compactSpace.1 K.1.fixingSubgroup_isClosed.isCompact

variable {K}

abbrev levelCochainsInfl (p : GLevel K) :
    cochainsComplex (ideleRep K.1 p.1.1) ⟶ cochainsComplex (limitRep K) :=
  cochainsMapAlong restrictHom continuous_restrictHom (levelMor K p.1)

abbrev levelCochainsMap {p q : GLevel K} (h : p ≤ q) :
    cochainsComplex (ideleRep K.1 p.1.1) ⟶ cochainsComplex (ideleRep K.1 q.1.1) :=
  haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
  cochainsMapAlong (levelRestrict K p.1 q.1) continuous_levelRestrict (levelMap K p.1 q.1)

theorem levelCochainsMap_comp_levelCochainsInfl {p q : GLevel K} (h : p ≤ q) :
    levelCochainsMap h ≫ levelCochainsInfl q = levelCochainsInfl p :=
  haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
  levelCochains_comp

theorem levelCochains_injective (p : GLevel K) (m : ℕ) :
    Function.Injective ((levelCochainsInfl p).f m).hom := by
  intro y y' h
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι (ideleRep K.1 p.1.1)).f m)).1 inferInstance
  funext τ
  let σ : Fin m → K.1.fixingSubgroup := fun i =>
    Function.surjInv (restrictHom_surjective (F := K) (E := p.1)) (τ i)
  have hσ : (fun i => restrictHom (E := p.1) (σ i)) = τ :=
    funext fun i => Function.surjInv_eq (restrictHom_surjective (F := K) (E := p.1)) (τ i)
  have h1 := congrFun (congrArg (fun c => ((cochainsComplexι (limitRep K)).f m).hom c) h) σ
  simp only [cochainsComplexι_cochainsMapAlong_apply] at h1
  change Additive.ofMul (of p.1 (((cochainsComplexι _).f m).hom y
      (fun i => restrictHom (E := p.1) (σ i))).toMul) =
    Additive.ofMul (of p.1 (((cochainsComplexι _).f m).hom y'
      (fun i => restrictHom (E := p.1) (σ i))).toMul) at h1
  rw [hσ] at h1
  exact congrArg Additive.ofMul (of_injective p.1 (congrArg Additive.toMul h1))

theorem exists_levelCochains_eq (m : ℕ) (x : (cochainsComplex (limitRep K)).X m) :
    ∃ (p : GLevel K) (y : (cochainsComplex (ideleRep K.1 p.1.1)).X m),
      ((levelCochainsInfl p).f m).hom y = x := by
  classical
  have hx : IsLocallyConstant (((cochainsComplexι (limitRep K)).f m).hom x :
      (Fin m → K.1.fixingSubgroup) → limitRep K) :=
    (show locallyConstantCochains (limitRep K) m from x).2
  set f := ((cochainsComplexι (limitRep K)).f m).hom x with hf
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_fin_of_isLocallyConstant hx
  obtain ⟨t, ht, htU⟩ := isOpen_induced_iff.1 U.isOpen
  have h1t : (1 : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) ∈ t := by
    have : (1 : K.1.fixingSubgroup) ∈ Subtype.val ⁻¹' t := by
      rw [htU]
      exact U.one_mem
    exact this
  obtain ⟨E₀, hE₀fin, hE₀⟩ := (krullTopology_mem_nhds_one_iff ℚ (AlgebraicClosure ℚ) t).1 (ht.mem_nhds h1t)
  have hfin : (Set.range f).Finite := hx.range_finite
  choose idx x' hx' using fun a : limitRep K => exists_of (Additive.toMul a)
  choose lev hlev using fun E : FiniteSubfield => GLevel.exists_le (K := K) E
  obtain ⟨p, hp⟩ := Finset.exists_le ((hfin.toFinset.image fun a => lev (idx a)) ∪
    {lev ⟨E₀, hE₀fin⟩})
  have hpE₀ : E₀ ≤ p.1.1 := (hlev ⟨E₀, hE₀fin⟩).trans
    (hp _ (Finset.mem_union_right _ (Finset.mem_singleton_self _)))
  have hker : ∀ g : K.1.fixingSubgroup, restrictHom (E := p.1) g = 1 → g ∈ U := by
    intro g hg
    have hg' : g ∈ p.1.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup := by
      rw [← ker_restrictHom, MonoidHom.mem_ker]
      exact hg
    rw [Subgroup.mem_subgroupOf] at hg'
    have : g ∈ Subtype.val ⁻¹' t := hE₀ (IntermediateField.fixingSubgroup_le hpE₀ hg')
    rw [htU] at this
    exact this
  have hval : ∀ g, ∃ z : IdeleGroup p.1.1, of p.1 z = Additive.toMul (f g) := by
    intro g
    have hmem : f g ∈ hfin.toFinset := by simp
    have hle : idx (f g) ≤ p.1 := (hlev (idx (f g))).trans
      (hp _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hmem)))
    exact ⟨ideleMap hle (x' (f g)), by rw [of_ideleMap]; exact hx' _⟩
  choose z hz using hval
  let lift : (Fin m → (p.1.1 ≃ₐ[K.1] p.1.1)) → Fin m → K.1.fixingSubgroup := fun τ i =>
    Function.surjInv (restrictHom_surjective (F := K) (E := p.1)) (τ i)
  refine ⟨p, ⟨fun τ => Additive.ofMul (z (lift τ)), IsLocallyConstant.of_discrete _⟩, ?_⟩
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι (limitRep K)).f m)).1 inferInstance
  funext g
  change Additive.ofMul (of p.1 (z (lift fun i => restrictHom (E := p.1) (g i)))) = f g
  rw [hz]
  refine hU _ _ fun i => hker _ ?_
  rw [map_mul, map_inv, Function.surjInv_eq (restrictHom_surjective (F := K) (E := p.1)),
    inv_mul_cancel]

theorem exists_levelInfl_eq (n : ℕ) (x : cohomology (limitRep K) n) :
    ∃ (p : GLevel K) (y : cohomology (ideleRep K.1 p.1.1) n), (levelInfl K p.1 n).hom y = x := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((cochainsComplex (limitRep K)).homologyπ n)).1 inferInstance x
  obtain ⟨p, y₀, hy₀⟩ := exists_levelCochains_eq n (((cochainsComplex (limitRep K)).iCycles n).hom z)
  have hd : ((cochainsComplex (ideleRep K.1 p.1.1)).d n (n + 1)).hom y₀ = 0 := by
    apply levelCochains_injective p (n + 1)
    rw [map_zero, hom_f_d_apply, hy₀]
    exact iCycles_d_apply _ n (n + 1) z
  obtain ⟨w, hw⟩ := exists_iCycles_eq_of_d_eq_zero _ n y₀ hd
  refine ⟨p, ((cochainsComplex (ideleRep K.1 p.1.1)).homologyπ n).hom w, ?_⟩
  refine (homologyMap_homologyπ_apply (levelCochainsInfl p) n w).trans (congrArg _ ?_)
  apply (ModuleCat.mono_iff_injective ((cochainsComplex (limitRep K)).iCycles n)).1 inferInstance
  rw [iCycles_cyclesMap_apply, hw, hy₀]


set_option maxHeartbeats 1600000 in
theorem exists_levelTransition_eq_zero (n : ℕ) (p : GLevel K) (y : cohomology (ideleRep K.1 p.1.1) n)
    (hy : (levelInfl K p.1 n).hom y = 0) :
    ∃ (q : GLevel K) (h : p ≤ q),
      (HomologicalComplex.homologyMap (levelCochainsMap h) n).hom y = 0 := by
  obtain ⟨w, hw⟩ : ∃ w, ((cochainsComplex (ideleRep K.1 p.1.1)).homologyπ n).hom w = y :=
    (ModuleCat.epi_iff_surjective ((cochainsComplex (ideleRep K.1 p.1.1)).homologyπ n)).1
      inferInstance y
  subst hw
  have hy' := (homologyMap_homologyπ_apply (levelCochainsInfl p) n w).symm.trans hy
  obtain ⟨u, hu⟩ := (homologyπ_eq_zero_iff _ _).1 hy'
  rw [iCycles_cyclesMap_apply] at hu
  obtain ⟨q, u', hu'⟩ := exists_levelCochains_eq _ u
  obtain ⟨r, hpr, hqr⟩ := GLevel.exists_ge p q
  refine ⟨r, hpr, (homologyMap_homologyπ_apply (levelCochainsMap hpr) n w).trans
    ((homologyπ_eq_zero_iff _ _).2 ⟨((levelCochainsMap hqr).f _).hom u', ?_⟩)⟩
  rw [iCycles_cyclesMap_apply]
  apply levelCochains_injective r n
  rw [hom_f_d_apply]
  have e1 := congrArg (fun φ => (φ.f _).hom u') (levelCochainsMap_comp_levelCochainsInfl hqr)
  have e2 := congrArg (fun φ => (φ.f n).hom (((cochainsComplex (ideleRep K.1 p.1.1)).iCycles n).hom w))
    (levelCochainsMap_comp_levelCochainsInfl hpr)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at e1 e2
  rw [e1, e2, hu', hu]

end

end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.LocalTransition
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField IsDedekindDomain GroundTheory.Global
  GroundTheory.Global.AdeleBaseChange FiniteSubfield IdeleLimit SemiLocal

open scoped Pointwise

noncomputable section

variable {K F E : FiniteSubfield} [Fact (K ≤ F)] [Fact (K ≤ E)] [Fact (F ≤ E)]
  [F.1.fixingSubgroup.Normal] [E.1.fixingSubgroup.Normal]

section Finite

variable {v : HeightOneSpectrum (𝓞 K.1)} (w : PlacesOver F.1 v) (w' : PlacesOver E.1 v)
  [hw : w'.1.asIdeal.LiesOver w.1.asIdeal]

theorem algebraMap_levelRestrict_integers (σ : E.1 ≃ₐ[K.1] E.1) (x : 𝓞 F.1) :
    algebraMap (𝓞 F.1) (𝓞 E.1) (levelRestrict K F E σ • x) = σ • algebraMap (𝓞 F.1) (𝓞 E.1) x :=
  RingOfIntegers.ext (coe_levelRestrict_apply σ (x : F.1))


include hw in
theorem levelRestrict_mem_stabilizer {σ : E.1 ≃ₐ[K.1] E.1}
    (hσ : σ ∈ MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1.asIdeal) :
    levelRestrict K F E σ ∈ MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal := by
  rw [MulAction.mem_stabilizer_iff] at hσ ⊢
  have hover : w.1.asIdeal = w'.1.asIdeal.comap (algebraMap (𝓞 F.1) (𝓞 E.1)) := hw.over
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, hover, Ideal.mem_comap, Ideal.mem_comap,
    ← map_inv, algebraMap_levelRestrict_integers, ← Ideal.mem_pointwise_smul_iff_inv_smul_mem, hσ]


variable {w w'} in
def decompRestrict :
    MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1.asIdeal →*
      MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal where
  toFun σ := ⟨levelRestrict K F E σ, levelRestrict_mem_stabilizer w w' σ.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' σ τ := Subtype.ext (map_mul _ _ _)

@[simp]
theorem coe_decompRestrict (σ : MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1.asIdeal) :
    ((decompRestrict (w := w) σ : MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal) :
      F.1 ≃ₐ[K.1] F.1) = levelRestrict K F E σ :=
  rfl

theorem completionMap_decomposition_smul (σ : MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1.asIdeal)
    (a : w.1.adicCompletion F.1) :
    completionMap w.1 w'.1 (decompRestrict (w := w) σ • a) = σ • completionMap w.1 w'.1 a := by
  have h1 := MulAction.mem_stabilizer_iff.1 (decompRestrict (w := w) σ).2
  have h2 := MulAction.mem_stabilizer_iff.1 σ.2
  have := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F.1) (K := F.1) w.1).equalizer
    ((continuous_completionMap w.1 w'.1).comp (continuous_adicCompletionRingHomOf _ h1))
    ((continuous_adicCompletionRingHomOf _ h2).comp (continuous_completionMap w.1 w'.1))
    (funext fun x => by
      simp only [Function.comp_apply]
      rw [adicCompletionRingHomOf_algebraMap, completionMap_algebraMap, completionMap_algebraMap]
      simp only [IsScalarTower.algebraMap_apply F.1 E.1 (w'.1.adicCompletion E.1)]
      rw [adicCompletionRingHomOf_algebraMap, coe_decompRestrict, coe_levelRestrict_apply])
  exact congrFun this a


variable {w w'} in
def completionUnitsRep :
    Rep.res (decompRestrict (w := w) (w' := w'))
        (Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal)
          (w.1.adicCompletion F.1)ˣ) ⟶
      Rep.ofMulDistribMulAction (MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1.asIdeal)
        (w'.1.adicCompletion E.1)ˣ :=
  Rep.ofHom ⟨(MonoidHom.toAdditive
      (Units.map (completionMap w.1 w'.1 : w.1.adicCompletion F.1 →* w'.1.adicCompletion E.1))).toIntLinearMap,
    fun σ => LinearMap.ext fun a => congrArg Additive.ofMul (Units.ext
      (completionMap_decomposition_smul w w' σ
        (Additive.toMul (α := (w.1.adicCompletion F.1)ˣ) a : w.1.adicCompletion F.1)))⟩


variable (K F E) in
def localTransition (n : ℕ) :
    cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal)
        (w.1.adicCompletion F.1)ˣ) n ⟶
      cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1.asIdeal)
        (w'.1.adicCompletion E.1)ˣ) n :=
  cohomologyMapAlong decompRestrict continuous_of_discreteTopology completionUnitsRep n

end Finite

section Infinite

variable {v : InfinitePlace K.1} (w : v.placesOver F.1) (w' : v.placesOver E.1) [hw : w'.1.LiesOver w.1]


include hw in
theorem levelRestrict_mem_stabilizer_infinite {σ : E.1 ≃ₐ[K.1] E.1}
    (hσ : σ ∈ MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1) :
    levelRestrict K F E σ ∈ MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1 := by
  rw [MulAction.mem_stabilizer_iff] at hσ ⊢
  have hover : w'.1.comap (algebraMap F.1 E.1) = w.1 := InfinitePlace.LiesOver.comap_eq w'.1 w.1
  have key : ∀ y : E.1, w'.1 (σ.symm y) = w'.1 y := fun y => by
    conv_rhs => rw [← hσ]
    rfl
  rw [← hover]
  refine InfinitePlace.ext _ _ fun x => ?_
  rw [InfinitePlace.smul_apply, InfinitePlace.comap_apply, InfinitePlace.comap_apply]
  have h1 : (levelRestrict K F E σ).symm x = levelRestrict K F E σ⁻¹ x := by
    rw [map_inv]
    rfl
  rw [h1, coe_levelRestrict_apply]
  exact key _


variable {w w'} in
def infDecompRestrict :
    MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1 →* MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1 where
  toFun σ := ⟨levelRestrict K F E σ, levelRestrict_mem_stabilizer_infinite w w' σ.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' σ τ := Subtype.ext (map_mul _ _ _)

@[simp]
theorem coe_infDecompRestrict (σ : MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1) :
    ((infDecompRestrict (w := w) σ : MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1) :
      F.1 ≃ₐ[K.1] F.1) = levelRestrict K F E σ :=
  rfl

theorem infCompletionMap_decomposition_smul (σ : MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1)
    (a : w.1.Completion) :
    AbsoluteValue.Completion.map w.1.1 w'.1.1 (infDecompRestrict (w := w) σ • a) =
      σ • AbsoluteValue.Completion.map w.1.1 w'.1.1 a := by
  have := (AbsoluteValue.Completion.denseRange_coe w.1.1).equalizer
    ((AbsoluteValue.Completion.continuous_map w.1.1 w'.1.1).comp
      (continuous_completionRingHomOf (infDecompRestrict (w := w) σ).2))
    ((continuous_completionRingHomOf σ.2).comp
      (AbsoluteValue.Completion.continuous_map w.1.1 w'.1.1))
    (funext fun y => by
      simp only [Function.comp_apply]
      rw [completionRingHomOf_coe, AbsoluteValue.Completion.map_coe,
        AbsoluteValue.Completion.map_coe, completionRingHomOf_coe]
      refine congrArg (fun z : WithAbs w'.1.1 => (z : w'.1.Completion))
        (WithAbs.ofAbs_injective _ ?_)
      change algebraMap F.1 E.1 ((infDecompRestrict (w := w) σ : F.1 ≃ₐ[K.1] F.1) y.ofAbs) =
        (σ : E.1 ≃ₐ[K.1] E.1) (algebraMap F.1 E.1 y.ofAbs)
      rw [coe_infDecompRestrict, coe_levelRestrict_apply])
  exact congrFun this a


variable {w w'} in
def infCompletionUnitsRep :
    Rep.res (infDecompRestrict (w := w) (w' := w'))
        (Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1) (w.1.Completion)ˣ) ⟶
      Rep.ofMulDistribMulAction (MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1) (w'.1.Completion)ˣ :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (Units.map (AbsoluteValue.Completion.map w.1.1 w'.1.1 :
      w.1.Completion →* w'.1.Completion))).toIntLinearMap,
    fun σ => LinearMap.ext fun a => congrArg Additive.ofMul (Units.ext
      (infCompletionMap_decomposition_smul w w' σ
        (Additive.toMul (α := (w.1.Completion)ˣ) a : w.1.Completion)))⟩


variable (K F E) in
def infLocalTransition (n : ℕ) :
    cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1)
        (w.1.Completion)ˣ) n ⟶
      cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1)
        (w'.1.Completion)ˣ) n :=
  cohomologyMapAlong infDecompRestrict continuous_of_discreteTopology infCompletionUnitsRep n

end Infinite

end

end GroundTheory.ProfCoh
end
