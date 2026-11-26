module

public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ExistsUnitsToIdelesEqOfIdelesSumInvEqZero
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.OpenSubgroups
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleInvariants.LocalInf
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.SubsingletonCohomologyThreeInfiniteDecomposition

@[expose] public section

section -- merged from GroundTheory.ProfiniteCohomology.GlobalClassFormation.ClassFormationGlobal
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain

open scoped DirectSum

noncomputable section

def SumInvRestriction : Prop :=
  ∀ (K F : FiniteSubfield) [Fact (K ≤ F)] (ιK : LocalEmbeddings K) (ιF : LocalEmbeddings F)
    (y : cohomology (limitRep K) 2),
    idelesSumInv ιF ((idelesResField K F 2).hom y) = Module.finrank K.1 F.1 • idelesSumInv ιK y

theorem idelesToClasses_unitsToIdeles (K : FiniteSubfield) (x : cohomology (unitsLimitRep K) 2) :
    (idelesToClasses K 2).hom ((unitsToIdeles K 2).hom x) = 0 := by
  have h := cohomologyMap_f_comp_g (S := idelesShortComplexRes K) 2
  exact congrArg (fun f => f.hom x) h

section Split

variable (K F : FiniteSubfield) [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

theorem classResField_classLevelInfl (y : cohomology (ideleClassRep K.1 F.1) 2) :
    (classResField K F 2).hom ((classLevelInfl K F 2).hom y) = 0 := by
  have : IsGalois K.1 F.1 := isGalois_of_normal
  have hle : F.1.fixingSubgroup ≤ K.1.fixingSubgroup :=
    IntermediateField.fixingSubgroup_le (Fact.out : K ≤ F)
  have : DiscreteTopology (K.1.fixingSubgroup ⧸ F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) :=
    QuotientGroup.discreteTopology (F.1.fixingSubgroup_isOpen.preimage continuous_subtype_val)
  have hfac : classLevelInfl K F 2 =
      cohomologyMapAlong (quotGalEquiv K F).toMonoidHom continuous_of_discreteTopology (classInvMor K F) 2 ≫
        cohomologyInfl (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 2 := by
    rw [classLevelInfl, cohomologyInfl_eq, ← cohomologyMapAlong_comp]
    exact cohomologyMapAlong_congr _ _ _ _ (MonoidHom.ext fun g => rfl) (fun _ => rfl) 2
  have h0 : (cohomologyRes (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 2).hom
      ((classLevelInfl K F 2).hom y) = 0 := by
    have h : cohomologyInfl (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 2 ≫
        cohomologyRes (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 2 = 0 :=
      cohomologyInfl_comp_cohomologyRes (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 1
    rw [hfac, ModuleCat.hom_comp, LinearMap.comp_apply]
    show ((cohomologyInfl (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 2 ≫
        cohomologyRes (classLimitRep K) (F.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup) 2).hom _) = 0
    rw [h]
    rfl
  exact (cohomologyResLE_apply_eq_zero_iff hle classRep 2 _).2 h0

end Split

variable (hR : SumInvRestriction)


include hR in
theorem idelesToClasses_surjective_of (K : FiniteSubfield) (ι : LocalEmbeddings K) :
    Function.Surjective (idelesToClasses K 2).hom := by
  classical
  intro c
  obtain ⟨p, z, rfl⟩ := exists_classLevelInfl_eq 2 c
  have : IsGalois K.1 p.1.1 := isGalois_of_normal
  obtain ⟨ιF⟩ := nonempty_localEmbeddings p.1
  set N := Module.finrank K.1 p.1.1 with hN
  have hN0 : N ≠ 0 := Module.finrank_pos.ne'
  have hM : Nat.card (LinearMap.ker (classResField K p.1 2).hom) ∣ N := natCard_ker_classResField_dvd K p.1
  obtain ⟨D, hD⟩ := sumPlaceInv_surjective K (QZ.mk (1 / N))
  set Y := (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).symm D with hYdef
  have hY : idelesSumInv ι Y = QZ.mk (1 / N) := by
    rw [idelesSumInv_apply, hYdef, AddEquiv.apply_symm_apply, hD]
  have hT : ∀ k : ℕ, idelesSumInv ι (k • Y) = QZ.mk ((k : ℚ) / N) := by
    intro k
    rw [map_nsmul, hY, ← QZ.mk_nsmul, nsmul_eq_mul, mul_one_div]
  have hmem : ∀ k : ℕ, (idelesToClasses K 2).hom (k • Y) ∈ LinearMap.ker (classResField K p.1 2).hom := by
    intro k
    rw [LinearMap.mem_ker, ← idelesToClasses_idelesResField]
    have hres : idelesSumInv ιF ((idelesResField K p.1 2).hom (k • Y)) = 0 := by
      rw [hR K p.1 ι ιF, hT, ← QZ.mk_nsmul, nsmul_eq_mul, QZ.mk_eq_zero_iff]
      refine ⟨k, ?_⟩
      have : (N : ℚ) ≠ 0 := by exact_mod_cast hN0
      rw [← hN]
      field_simp
      push_cast
      ring
    obtain ⟨x, hx⟩ := exists_unitsToIdeles_eq_of_idelesSumInv_eq_zero ιF _ hres
    rw [← hx, idelesToClasses_unitsToIdeles]
  let f : Fin N → LinearMap.ker (classResField K p.1 2).hom := fun k =>
    ⟨(idelesToClasses K 2).hom ((k : ℕ) • Y), hmem k⟩
  have finj : Function.Injective f := by
    intro k k' hkk
    have h1 : (idelesToClasses K 2).hom ((k : ℕ) • Y) = (idelesToClasses K 2).hom ((k' : ℕ) • Y) :=
      congrArg Subtype.val hkk
    have key : ∀ a b : Fin N, (b : ℕ) ≤ a →
        (idelesToClasses K 2).hom ((a : ℕ) • Y) = (idelesToClasses K 2).hom ((b : ℕ) • Y) → a = b := by
      intro a b hba hab
      have hw : (idelesToClasses K 2).hom (((a : ℕ) - b) • Y) = 0 := by
        rw [sub_nsmul _ hba, ← sub_eq_add_neg, map_sub, hab, sub_self]
      have h2 := idelesSumInv_eq_zero_of_idelesToClasses_eq_zero ι _ hw
      rw [hT] at h2
      have := eq_zero_of_mk_div_eq_zero (lt_of_le_of_lt (Nat.sub_le _ _) a.2) (by exact_mod_cast h2)
      exact Fin.ext (by omega)
    rcases le_total (k' : ℕ) k with h | h
    · exact key k k' h h1
    · exact (key k' k h h1.symm).symm
  have hfin : Finite (LinearMap.ker (classResField K p.1 2).hom) :=
    Nat.finite_of_card_ne_zero (fun h0 => hN0 (by rw [h0, zero_dvd_iff] at hM; exact hM))
  have hcardFin : Nat.card (Fin N) = N := Nat.card_eq_fintype_card.trans (Fintype.card_fin N)
  have fsurj := (finj.bijective_of_nat_card_le (by
    rw [hcardFin]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hM)).2
  obtain ⟨k, hk⟩ := fsurj ⟨(classLevelInfl K p.1 2).hom z, classResField_classLevelInfl K p.1 z⟩
  exact ⟨(k : ℕ) • Y, congrArg Subtype.val hk⟩

def classInv (K : FiniteSubfield) (ι : LocalEmbeddings K) : cohomology (classLimitRep K) 2 →+ QZ :=
  (QuotientAddGroup.lift (idelesToClasses K 2).hom.toAddMonoidHom.ker (idelesSumInv ι)
    fun y hy => idelesSumInv_eq_zero_of_idelesToClasses_eq_zero ι y hy).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective (idelesToClasses K 2).hom.toAddMonoidHom
      (idelesToClasses_surjective_of hR K ι)).symm.toAddMonoidHom

theorem classInv_idelesToClasses (K : FiniteSubfield) (ι : LocalEmbeddings K) (y : cohomology (limitRep K) 2) :
    classInv hR K ι ((idelesToClasses K 2).hom y) = idelesSumInv ι y := by
  have h : (QuotientAddGroup.quotientKerEquivOfSurjective (idelesToClasses K 2).hom.toAddMonoidHom
      (idelesToClasses_surjective_of hR K ι)).symm ((idelesToClasses K 2).hom y) =
      (QuotientAddGroup.mk y : _ ⧸ (idelesToClasses K 2).hom.toAddMonoidHom.ker) := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  simp only [classInv, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h]
  rfl

theorem classInv_bijective (K : FiniteSubfield) (ι : LocalEmbeddings K) : Function.Bijective (classInv hR K ι) := by
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun c hc => ?_
    obtain ⟨y, rfl⟩ := idelesToClasses_surjective_of hR K ι c
    rw [classInv_idelesToClasses] at hc
    obtain ⟨x, rfl⟩ := exists_unitsToIdeles_eq_of_idelesSumInv_eq_zero ι y hc
    exact idelesToClasses_unitsToIdeles K x
  · intro q
    obtain ⟨D, hD⟩ := sumPlaceInv_surjective K q
    refine ⟨(idelesToClasses K 2).hom ((idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).symm D), ?_⟩
    rw [classInv_idelesToClasses, idelesSumInv_apply, AddEquiv.apply_symm_apply, hD]

theorem classInv_classResField (K F : FiniteSubfield) [Fact (K ≤ F)] (ιK : LocalEmbeddings K)
    (ιF : LocalEmbeddings F) (c : cohomology (classLimitRep K) 2) :
    classInv hR F ιF ((classResField K F 2).hom c) = Module.finrank K.1 F.1 • classInv hR K ιK c := by
  obtain ⟨y, rfl⟩ := idelesToClasses_surjective_of hR K ιK c
  rw [← idelesToClasses_idelesResField, classInv_idelesToClasses, classInv_idelesToClasses, hR K F ιK ιF]

def globalClassFormationOf (K : FiniteSubfield) : ClassFormation (classLimitRep K) where
  inv U := (classInv hR (fieldOf U) (Classical.choice (nonempty_localEmbeddings _))).comp
    (classOpenIso U 2).hom.hom.toAddMonoidHom
  isZero_H1_open_subgroups U := (isZero_cohomology_one_classLimitRep (fieldOf U)).of_iso (classOpenIso U 1)
  inv_res U V h x := by
    have : Fact (fieldOf U ≤ fieldOf V) := ⟨fieldOf_le_fieldOf h⟩
    have hsq := congrArg (fun f => f.hom x) (cohomologyResLE_classOpenIso h 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hsq
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe]
    rw [hsq, classInv_classResField, relIndex_eq_finrank_fieldOf h]
  inv_bijective U := (classInv_bijective hR _ _).comp
    ⟨(ModuleCat.mono_iff_injective _).1 inferInstance, (ModuleCat.epi_iff_surjective _).1 inferInstance⟩

end

end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleInvariants
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain IdeleLimit
  GroundTheory.Global.SemiLocal

open scoped NumberField.LiesOver DirectSum

noncomputable section

variable {K E : FiniteSubfield} [Fact (K ≤ E)] (ι : LocalEmbeddings K) (ιE : LocalEmbeddings E)

section Places


set_option maxHeartbeats 4000000 in
theorem placeInv_idelesResField_inr (y : cohomology (limitRep K) 2) (v : HeightOneSpectrum (𝓞 K.1))
    (w : PlacesOver E.1 v) :
    placeInv (.inr w.1) (idelesLimitCohomologyEquiv ιE (by norm_num : 1 ≤ 2) ((idelesResField K E 2).hom y) (.inr w.1)) =
      Module.finrank (v.adicCompletion K.1) (w.1.adicCompletion E.1) •
        placeInv (.inr v) (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) y (.inr v)) := by
  rw [idelesLimitCohomologyEquiv_apply_inr, idelesLimitCohomologyEquiv_apply_inr]
  obtain ⟨ι', hι'⟩ := exists_placeOfEmbedding_eq w
  have key : ∀ u : PlacesOver E.1 v, placeOfEmbedding ι' E = u →
      placeInv (K := E) (.inr u.1) ((idelesLocalRes (ιE.fin u.1) 2).hom ((idelesResField K E 2).hom y)) =
        Module.finrank (v.adicCompletion K.1) (u.1.adicCompletion E.1) •
          placeInv (K := K) (.inr v) ((idelesLocalRes (ι.fin v) 2).hom y) := by
    rintro u rfl
    rw [idelesLocalRes_eq_of_algHom ι' (ι.fin v)]
    exact brauerInvZOfIsSepClosure_idelesLocalRes_idelesResField v ι' (ιE.fin _) y
  exact key w hι'


set_option maxHeartbeats 4000000 in
theorem placeInv_idelesResField_inl (y : cohomology (limitRep K) 2) (v : InfinitePlace K.1) (w : v.placesOver E.1) :
    placeInv (.inl (w : InfinitePlace E.1))
        (idelesLimitCohomologyEquiv ιE (by norm_num : 1 ≤ 2) ((idelesResField K E 2).hom y) (.inl w)) =
      Module.finrank v.Completion (w : InfinitePlace E.1).Completion •
        placeInv (.inl v) (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) y (.inl v)) := by
  rw [idelesLimitCohomologyEquiv_apply_inl, idelesLimitCohomologyEquiv_apply_inl]
  by_cases hw : (w : InfinitePlace E.1).IsComplex
  · have h0 : placeInv (K := E) (.inl (w : InfinitePlace E.1))
        ((infIdelesLocalRes (ιE.inf (w : InfinitePlace E.1)) 2).hom ((idelesResField K E 2).hom y)) = 0 := by
      have : Subsingleton (cohomology (galUnitsZ (w : InfinitePlace E.1).Completion
          (AlgebraicClosure (w : InfinitePlace E.1).Completion)) 2) :=
        subsingleton_cohomology_two_of_isComplex _ hw
      exact (congrArg _ (Subsingleton.elim _ 0)).trans (map_zero _)
    rw [h0]
    by_cases hv : v.IsReal
    · rw [(InfinitePlace.finrank_completion_eq_two_iff (w : InfinitePlace E.1)).2 ⟨hv, hw⟩]
      rcases placeInv_inl_eq_zero_or_eq_half v ((infIdelesLocalRes (ι.inf v) 2).hom y) with h | h
      · rw [h, smul_zero]
      · rw [h, two_nsmul, QZ.mk_half_add_mk_half]
    · have h0 : placeInv (K := K) (.inl v) ((infIdelesLocalRes (ι.inf v) 2).hom y) = 0 := by
        have : Subsingleton (cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) 2) :=
          subsingleton_cohomology_two_of_isComplex v (InfinitePlace.not_isReal_iff_isComplex.1 hv)
        exact (congrArg _ (Subsingleton.elim _ 0)).trans (map_zero _)
      rw [h0, smul_zero]
  · have h1 : Module.finrank v.Completion (w : InfinitePlace E.1).Completion = 1 :=
      (InfinitePlace.finrank_completion_eq_one_iff (w : InfinitePlace E.1)).2 fun h => hw h.2
    rw [h1, one_smul]
    obtain ⟨ι', hι'⟩ := exists_infPlaceOfEmbedding_eq w
    have key : ∀ u : v.placesOver E.1, infPlaceOfEmbedding ι' E = u →
        Module.finrank v.Completion (u : InfinitePlace E.1).Completion = 1 →
        placeInv (K := E) (.inl (u : InfinitePlace E.1))
            ((infIdelesLocalRes (ιE.inf (u : InfinitePlace E.1)) 2).hom ((idelesResField K E 2).hom y)) =
          placeInv (K := K) (.inl v) ((infIdelesLocalRes (ι.inf v) 2).hom y) := by
      rintro u rfl hu
      rw [infIdelesLocalRes_eq_of_algHom ι' (ι.inf v)]
      exact quadraticInv_infIdelesLocalRes_idelesResField_of_finrank_eq_one ι' (ιE.inf _) y hu
    exact key w hι' h1

end Places

section Sum

theorem sumPlaceInv_eq_sum (D : ⨁ w : Place E.1, localGaloisCohomology E 2 w) (S : Finset (Place E.1))
    (hS : ∀ w ∉ S, D w = 0) : sumPlaceInv E D = ∑ w ∈ S, placeInv w (D w) := by
  classical
  have hD : D = ∑ w ∈ S, DirectSum.of _ w (D w) := by
    refine DFinsupp.ext fun w => ?_
    rw [DFinsupp.finsetSum_apply]
    by_cases hw : w ∈ S
    · rw [Finset.sum_eq_single w (fun b _ hb => DirectSum.of_eq_of_ne _ _ _ (Ne.symm hb))
        (fun h => absurd hw h), DirectSum.of_eq_same]
    · rw [hS w hw, Finset.sum_eq_zero fun b hb => DirectSum.of_eq_of_ne _ _ _ (by rintro rfl; exact hw hb)]
  conv_lhs => rw [hD]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun w _ => sumPlaceInv_of w (D w)


set_option maxHeartbeats 4000000 in
open Classical in
theorem idelesSumInv_idelesResField_of (u : Place K.1) (t : localGaloisCohomology K 2 u) :
    idelesSumInv ιE ((idelesResField K E 2).hom
        ((idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).symm (DirectSum.of _ u t))) =
      Module.finrank K.1 E.1 •
        idelesSumInv ι ((idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).symm (DirectSum.of _ u t)) := by
  set_option synthInstance.maxHeartbeats 200000 in
    classical
    set y := (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).symm (DirectSum.of _ u t) with hy_def
    have hy : idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) y = DirectSum.of _ u t :=
      AddEquiv.apply_symm_apply _ _
    set D := idelesLimitCohomologyEquiv ιE (by norm_num : 1 ≤ 2) ((idelesResField K E 2).hom y) with hD_def
    rw [idelesSumInv_apply, idelesSumInv_apply, hy, sumPlaceInv_of]
  
    have hinl : ∀ w : InfinitePlace E.1, placeInv (.inl w) (D (.inl w)) =
        Module.finrank (w.comap (algebraMap K.1 E.1)).Completion w.Completion •
          placeInv (.inl (w.comap (algebraMap K.1 E.1)))
            (DirectSum.of (localGaloisCohomology K 2) u t (.inl (w.comap (algebraMap K.1 E.1)))) := fun w => by
      rw [← hy]
      exact placeInv_idelesResField_inl ι ιE y (w.comap (algebraMap K.1 E.1)) ⟨w, ⟨rfl⟩⟩
    have hinr : ∀ w : HeightOneSpectrum (𝓞 E.1), placeInv (.inr w) (D (.inr w)) =
        Module.finrank ((AdeleBaseChange.below K.1 w).adicCompletion K.1) (w.adicCompletion E.1) •
          placeInv (.inr (AdeleBaseChange.below K.1 w))
            (DirectSum.of (localGaloisCohomology K 2) u t (.inr (AdeleBaseChange.below K.1 w))) := fun w => by
      rw [← hy]
      exact placeInv_idelesResField_inr ι ιE y (AdeleBaseChange.below K.1 w) ⟨w, AdeleBaseChange.liesOver_below w⟩
    rcases u with v | v
    ·
      let S : Finset (Place E.1) := Finset.univ.map ⟨fun w : v.placesOver E.1 => (.inl (w : InfinitePlace E.1) :
        Place E.1), fun a b h => Subtype.ext (Sum.inl_injective h)⟩
      have hS : ∀ w ∉ S, D w = 0 := by
        intro w hw
        apply placeInv_injective w
        rw [map_zero]
        rcases w with w | w
        · rw [hinl]
          by_cases hv : w.comap (algebraMap K.1 E.1) = v
          · exact absurd (Finset.mem_map.2 ⟨(⟨w, by subst hv; exact ⟨rfl⟩⟩ : v.placesOver E.1), Finset.mem_univ _, rfl⟩) hw
          · rw [DirectSum.of_eq_of_ne _ _ _ (fun h => hv (Sum.inl_injective h)), map_zero, smul_zero]
        · rw [hinr, DirectSum.of_eq_of_ne _ _ _ Sum.inr_ne_inl, map_zero, smul_zero]
      rw [sumPlaceInv_eq_sum D S hS, Finset.sum_map]
      change ∑ w : v.placesOver E.1, placeInv (.inl (w : InfinitePlace E.1)) (D (.inl (w : InfinitePlace E.1))) = _
      have hw : ∀ w : v.placesOver E.1, placeInv (.inl (w : InfinitePlace E.1)) (D (.inl (w : InfinitePlace E.1))) =
          Module.finrank v.Completion (w : InfinitePlace E.1).Completion • placeInv (.inl v) t := fun w => by
        rw [hD_def, placeInv_idelesResField_inl ι ιE y v w, hy, DirectSum.of_eq_same]
      rw [Finset.sum_congr rfl fun w _ => hw w, ← Finset.sum_smul,
        GroundTheory.Global.InfinitePlace.sum_finrank_completion (L := E.1) v]
    ·
      let S : Finset (Place E.1) := Finset.univ.map ⟨fun w : PlacesOver E.1 v => (.inr w.1 : Place E.1),
        fun a b h => Subtype.ext (Sum.inr_injective h)⟩
      have hS : ∀ w ∉ S, D w = 0 := by
        intro w hw
        apply placeInv_injective w
        rw [map_zero]
        rcases w with w | w
        · rw [hinl, DirectSum.of_eq_of_ne _ _ _ Sum.inl_ne_inr, map_zero, smul_zero]
        · rw [hinr]
          by_cases hv : AdeleBaseChange.below K.1 w = v
          · refine absurd (Finset.mem_map.2 ⟨(⟨w, ?_⟩ : PlacesOver E.1 v), Finset.mem_univ _, rfl⟩) hw
            rw [← hv]
            exact AdeleBaseChange.liesOver_below w
          · rw [DirectSum.of_eq_of_ne _ _ _ (fun h => hv (Sum.inr_injective h)), map_zero, smul_zero]
      rw [sumPlaceInv_eq_sum D S hS, Finset.sum_map]
      change ∑ w : PlacesOver E.1 v, placeInv (.inr w.1) (D (.inr w.1)) = _
      have hw : ∀ w : PlacesOver E.1 v, placeInv (.inr w.1) (D (.inr w.1)) =
          Module.finrank (v.adicCompletion K.1) (w.1.adicCompletion E.1) • placeInv (.inr v) t := fun w => by
        rw [hD_def, placeInv_idelesResField_inr ι ιE y v w, hy, DirectSum.of_eq_same]
      rw [Finset.sum_congr rfl fun w _ => hw w, ← Finset.sum_smul, sum_finrank_eq E.1 v]

theorem idelesSumInv_idelesResField (y : cohomology (limitRep K) 2) :
    idelesSumInv ιE ((idelesResField K E 2).hom y) = Module.finrank K.1 E.1 • idelesSumInv ι y := by
  classical
  set Φ := idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)
  obtain ⟨D, rfl⟩ := Φ.symm.surjective y
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← DirectSum.sum_support_of D, map_sum, map_sum, map_sum, map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun u _ => idelesSumInv_idelesResField_of ι ιE u (D u)

end Sum

end

end GroundTheory.ProfCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain

noncomputable section

theorem sumInvRestriction : SumInvRestriction :=
  fun _ _ _ ιK ιF y => idelesSumInv_idelesResField ιK ιF y

theorem idelesToClasses_surjective (K : FiniteSubfield) : Function.Surjective (idelesToClasses K 2).hom :=
  idelesToClasses_surjective_of sumInvRestriction K (Classical.choice (nonempty_localEmbeddings K))

def globalClassFormation (K : FiniteSubfield) : ClassFormation (classLimitRep K) :=
  globalClassFormationOf sumInvRestriction K

theorem subsingleton_cohomology_three_unitsLimitRep (K : FiniteSubfield) :
    Subsingleton (cohomology (unitsLimitRep K) 3) := by
  have h3 := subsingleton_cohomology_three_limitRep (K := K)
  refine ⟨fun x x' => ?_⟩
  have hz : ∀ x : cohomology (unitsLimitRep K) 3, x = 0 := by
    intro x
    obtain ⟨c, rfl⟩ := exists_classesToUnits_eq K 2 x (Subsingleton.elim _ _)
    obtain ⟨y, rfl⟩ := idelesToClasses_surjective K c
    exact congrArg (fun f => f.hom y) (comp_δ (idelesShortComplexRes_shortExact K) 2 3 rfl)
  rw [hz x, hz x']

end

end GroundTheory.ProfCoh
