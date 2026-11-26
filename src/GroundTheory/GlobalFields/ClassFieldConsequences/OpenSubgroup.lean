module

public import GroundTheory.GlobalFields.ClassFieldConsequences.CongruenceSubgroupLeStandardOpenSubgroup

@[expose] public section

section -- merged from GroundTheory.GlobalFields.ClassFieldConsequences.OpenSubgroup
open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing

namespace GroundTheory.Global

noncomputable section

theorem Subgroup.subset_of_isPreconnected {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (hH : IsOpen (H : Set G)) {s : Set G}
    (hs : IsPreconnected s) (h1 : (1 : G) ∈ s) : s ⊆ H :=
  hs.subset_isClopen ⟨H.isClosed_of_isOpen hH, hH⟩ ⟨1, h1, H.one_mem⟩

theorem Subgroup.mem_of_isOpen_of_pos (H : Subgroup ℝˣ) (hH : IsOpen (H : Set ℝˣ)) {r : ℝˣ}
    (hr : 0 < (r : ℝ)) : r ∈ H := by
  let f : ℝ → ℝˣ := fun t ↦ Units.mk0 (Real.exp t) (Real.exp_ne_zero t)
  have hf : Continuous f := Units.isEmbedding_val₀.isInducing.continuous_iff.2 Real.continuous_exp
  have hsub := Subgroup.subset_of_isPreconnected H hH (isPreconnected_range hf)
    ⟨0, Units.ext (by simp [f])⟩
  exact hsub ⟨Real.log r, Units.ext (Real.exp_log hr)⟩

theorem Subgroup.mem_of_isOpen_complexUnits (H : Subgroup ℂˣ) (hH : IsOpen (H : Set ℂˣ)) (z : ℂˣ) :
    z ∈ H :=
  Subgroup.subset_of_isPreconnected H hH isPreconnected_univ (Set.mem_univ 1) (Set.mem_univ z)

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

theorem infiniteEmbedding_mem_of_isOpen_of_isReal (H : Subgroup (IdeleGroup K))
    (hH : IsOpen (H : Set (IdeleGroup K))) {w : InfinitePlace K} (hw : w.IsReal)
    {a : (w.Completion)ˣ}
    (ha : 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (a : w.Completion)) :
    infiniteEmbedding w a ∈ H := by
  let Hr : Subgroup ℝˣ := (H.comap (infiniteEmbedding w)).comap (realUnitsHom hw).toMonoidHom
  have hopen : IsOpen (Hr : Set ℝˣ) :=
    (hH.preimage (continuous_infiniteEmbedding w)).preimage (realUnitsHom hw).continuous
  let r : ℝˣ := Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw :
    w.Completion →+* ℝ).toMonoidHom a
  have hr : 0 < (r : ℝ) := by
    change 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw (a : w.Completion)
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
    exact ha
  have hmem : r ∈ Hr := Subgroup.mem_of_isOpen_of_pos Hr hopen hr
  rw [← realUnitsHom_surjective hw a]
  exact hmem

theorem infiniteEmbedding_mem_of_isOpen_of_isComplex (H : Subgroup (IdeleGroup K))
    (hH : IsOpen (H : Set (IdeleGroup K))) {w : InfinitePlace K} (hw : w.IsComplex)
    (a : (w.Completion)ˣ) : infiniteEmbedding w a ∈ H := by
  let Hc : Subgroup ℂˣ := (H.comap (infiniteEmbedding w)).comap (complexUnitsHom hw).toMonoidHom
  have hopen : IsOpen (Hc : Set ℂˣ) :=
    (hH.preimage (continuous_infiniteEmbedding w)).preimage (complexUnitsHom hw).continuous
  have hmem := Subgroup.mem_of_isOpen_complexUnits Hc hopen
    (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw :
      w.Completion →+* ℂ).toMonoidHom a)
  rw [← complexUnitsHom_surjective hw a]
  exact hmem

theorem Modulus.exists_congruenceSubgroup_le (H : Subgroup (IdeleGroup K))
    (hH : IsOpen (H : Set (IdeleGroup K))) :
    ∃ 𝔪 : Modulus K, 𝔪.real = Set.univ ∧ 𝔪.congruenceSubgroup ≤ H := by
  classical
  have hWf : (H.comap ofFinite : Set (FiniteAdeleRing (𝓞 K) K)ˣ) ∈ 𝓝 1 :=
    (hH.preimage continuous_ofFinite).mem_nhds (by simp [H.one_mem])
  obtain ⟨S, n, -, hn0, hsub⟩ := exists_finiteLevel_subset hWf
  have hsupp : (support n).Finite :=
    S.finite_toSet.subset fun v hv ↦ by
      by_contra h
      exact hv (hn0 v h)
  let 𝔪 : Modulus K := ⟨∏ᶠ v, v.asIdeal ^ n v, finprod_asIdeal_pow_ne_bot n, Set.univ⟩
  have hle (v : HeightOneSpectrum (𝓞 K)) : n v ≤ 𝔪.exponent v := by
    rw [exponent, ite_eq_left (FiniteMultiplicity.of_prime_left v.prime 𝔪.ideal_ne_bot)]
    exact (finprod_asIdeal_pow_dvd_iff hsupp (finprod_asIdeal_pow_ne_bot n)).mp dvd_rfl v
  refine ⟨𝔪, rfl, fun x hx ↦ ?_⟩
  obtain ⟨hf, hi⟩ := 𝔪.mem_congruenceSubgroup.1 hx
  rw [← ofFinite_mul_ofInfinite x]
  refine H.mul_mem ?_ ?_
  · have : toFinite K x ∈ finiteLevel n := mem_finiteLevel.2 fun v ↦ by
      rw [finiteComponent_toFinite]
      exact unitsLevel_antitone v (hle v) (hf v)
    exact hsub this
  · rw [ofInfinite_eq_prod]
    refine Subgroup.prod_mem H fun w _ ↦ ?_
    rcases w.isReal_or_isComplex with hw | hw
    · exact infiniteEmbedding_mem_of_isOpen_of_isReal H hH hw (hi ⟨w, hw⟩ (Set.mem_univ _))
    · exact infiniteEmbedding_mem_of_isOpen_of_isComplex H hH hw _

theorem IdeleClassGroup.exists_map_congruenceSubgroup_le (H : Subgroup (IdeleClassGroup K))
    (hH : IsOpen (H : Set (IdeleClassGroup K))) :
    ∃ 𝔪 : Modulus K, 𝔪.real = Set.univ ∧ 𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) ≤ H := by
  obtain ⟨𝔪, h𝔪, hle⟩ := Modulus.exists_congruenceSubgroup_le (H.comap (IdeleClassGroup.mk K))
    (hH.preimage (IdeleClassGroup.continuous_mk K))
  exact ⟨𝔪, h𝔪, Subgroup.map_le_iff_le_comap.2 hle⟩

theorem Modulus.isOpen_map_congruenceSubgroup (𝔪 : Modulus K) :
    IsOpen (𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) : Set (IdeleClassGroup K)) := by
  rw [Subgroup.coe_map]
  exact IdeleClassGroup.isOpenMap_mk K _ 𝔪.isOpen_congruenceSubgroup

end

end GroundTheory.Global
end

section -- merged from GroundTheory.GlobalFields.ClassFieldConsequences.RayClass
open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

namespace Modulus

variable (𝔪 : Modulus K)

def rayGroup : Subgroup (IdeleGroup K) :=
  (diagonal K).range ⊔ 𝔪.congruenceSubgroup

abbrev RayClassGroup : Type _ :=
  IdeleGroup K ⧸ 𝔪.rayGroup

theorem diagonal_range_le_rayGroup : (diagonal K).range ≤ 𝔪.rayGroup :=
  le_sup_left

theorem map_rayGroup :
    𝔪.rayGroup.map (QuotientGroup.mk' (diagonal K).range) =
      𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) := by
  rw [rayGroup, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  rfl

instance : (𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K)).Normal :=
  ⟨fun n hn g ↦ by rwa [mul_comm g n, mul_inv_cancel_right]⟩

def quotientMapCongruenceEquiv :
    IdeleClassGroup K ⧸ 𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) ≃* 𝔪.RayClassGroup :=
  (QuotientGroup.quotientMulEquivOfEq 𝔪.map_rayGroup.symm).trans
    (QuotientGroup.quotientQuotientEquivQuotient _ _ 𝔪.diagonal_range_le_rayGroup)

@[simp]
theorem quotientMapCongruenceEquiv_mk (x : IdeleGroup K) :
    𝔪.quotientMapCongruenceEquiv (QuotientGroup.mk (IdeleClassGroup.mk K x)) =
      (QuotientGroup.mk x : 𝔪.RayClassGroup) :=
  rfl

theorem map_idealLevel_sup_le :
    (idealLevel 𝔪.ideal).map ofFinite ⊔ (infinitePositive K).map ofInfinite ≤
      𝔪.congruenceSubgroup := by
  refine sup_le ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    refine 𝔪.mem_congruenceSubgroup.2 ⟨fun v ↦ ?_, fun w _ ↦ ?_⟩
    · rw [← finiteComponent_toFinite, toFinite_ofFinite]
      have hfinite := FiniteMultiplicity.of_prime_left v.prime 𝔪.ideal_ne_bot
      simpa only [exponent, ite_eq_left hfinite] using mem_finiteLevel.1 hy v
    · change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
        ((toInfinite K (ofFinite y) : InfiniteAdeleRing K) w.1)
      rw [toInfinite_ofFinite]
      change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (1 : w.1.Completion)
      rw [map_one]
      exact one_pos
  · rintro _ ⟨z, hz, rfl⟩
    refine 𝔪.mem_congruenceSubgroup.2 ⟨fun v ↦ ?_, fun w _ ↦ ?_⟩
    · rw [← finiteComponent_toFinite, toFinite_ofInfinite, map_one]
      exact one_mem _
    · have h : ((infiniteProj w.1 (ofInfinite z) : (w.1.Completion)ˣ) : w.1.Completion) =
          (toInfinite K (ofInfinite z) : InfiniteAdeleRing K) w.1 := rfl
      rw [h, toInfinite_ofInfinite]
      exact hz w.1 w.2

theorem rayGroup_ideal_le : IdeleGroup.rayGroup K 𝔪.ideal ≤ 𝔪.rayGroup := by
  rw [IdeleGroup.rayGroup, sup_assoc]
  exact sup_le_sup_left 𝔪.map_idealLevel_sup_le _

theorem RayClassGroup.finite : Finite 𝔪.RayClassGroup := by
  have : Finite (_root_.GroundTheory.Global.RayClassGroup K 𝔪.ideal) :=
    _root_.GroundTheory.Global.RayClassGroup.finite 𝔪.ideal_ne_bot
  have : (IdeleGroup.rayGroup K 𝔪.ideal).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have : 𝔪.rayGroup.FiniteIndex := Subgroup.finiteIndex_of_le 𝔪.rayGroup_ideal_le
  exact Subgroup.finite_quotient_of_finiteIndex

instance : Finite 𝔪.RayClassGroup :=
  RayClassGroup.finite 𝔪

theorem finiteIndex_map_congruenceSubgroup :
    (𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K)).FiniteIndex := by
  have : Finite (IdeleClassGroup K ⧸ 𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K)) :=
    Finite.of_equiv _ 𝔪.quotientMapCongruenceEquiv.symm.toEquiv
  exact Subgroup.finiteIndex_of_finite_quotient

end Modulus

end

end GroundTheory.Global
end
