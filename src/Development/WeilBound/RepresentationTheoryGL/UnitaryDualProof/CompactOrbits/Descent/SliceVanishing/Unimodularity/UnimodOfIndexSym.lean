module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.OpenSlices.OpenSlice

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.Unimodularity.ModularCharacterFunEqOne
noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

namespace PositivityTheory.RgUd.T.Desc.SLF.Un2

theorem measure_subgroup_eq {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsMulLeftInvariant μ] (H K : Subgroup G)
    (hKH : K ≤ H) (hH : IsOpen (H : Set G)) (hK : IsOpen (K : Set G)) (hfin : K.relIndex H ≠ 0) :
    μ H = K.relIndex H * μ K := by
  classical
  haveI : (K.subgroupOf H).FiniteIndex := ⟨hfin⟩
  letI : Fintype (H ⧸ K.subgroupOf H) := Fintype.ofFinite _
  have hcover : (H : Set G) =
      ⋃ q : H ⧸ K.subgroupOf H, (fun y => ((q.out : H) : G)⁻¹ * y) ⁻¹' (K : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · intro hx
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (K.subgroupOf H) (⟨x, hx⟩ : H)
      refine ⟨(QuotientGroup.mk (⟨x, hx⟩ : H) : H ⧸ K.subgroupOf H), ?_⟩
      rw [hh]
      have hk : (((h⁻¹ : K.subgroupOf H) : H) : G) ∈ K := Subgroup.mem_subgroupOf.mp (h⁻¹).2
      simpa [mul_assoc] using hk
    · rintro ⟨q, hq⟩
      have := H.mul_mem (q.out).2 (hKH hq)
      simpa using this
  have hdisj : Pairwise (Function.onFun Disjoint
      fun q : H ⧸ K.subgroupOf H => (fun y => ((q.out : H) : G)⁻¹ * y) ⁻¹' (K : Set G)) := by
    intro q q' hqq'
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    simp only [Set.mem_preimage, SetLike.mem_coe] at hx hx'
    apply hqq'
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have hm := K.mul_mem hx (K.inv_mem hx')
    simpa [mul_assoc] using hm
  rw [hcover, measure_iUnion hdisj
    (fun q => (hK.preimage (continuous_const_mul _)).measurableSet)]
  simp only [measure_preimage_mul, tsum_fintype, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]

theorem modularCharacterFun_eq_one {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] (g : G) (K K₂ K' : Subgroup G) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) (hK'o : IsOpen (K' : Set G)) (hK₂ : ∀ x, x ∈ K₂ ↔ g⁻¹ * x * g ∈ K)
    (h1 : K' ≤ K) (h2 : K' ≤ K₂) (h3 : K'.relIndex K₂ = K'.relIndex K) (h4 : K'.relIndex K ≠ 0) :
    modularCharacterFun g = 1 := by
  borelize G
  let μ : Measure G := haar
  have hKcl : closure (K : Set G) = K := (Subgroup.isClosed_of_isOpen K hKo).closure_eq
  have hc := measure_isMulInvariant_eq_smul_of_isCompact_closure (map (· * g) μ) μ
    (s := (K : Set G)) (by rw [hKcl]; exact hKc)
  rw [← modularCharacterFun_eq_haarScalarFactor μ g] at hc
  have hK₂set : (K₂ : Set G) = (fun x => g⁻¹ * x * g) ⁻¹' (K : Set G) := by
    ext x
    exact hK₂ x
  have hK₂o : IsOpen (K₂ : Set G) := by
    rw [hK₂set]
    exact hKo.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  have hmap : map (· * g) μ K = μ K₂ := by
    rw [map_apply (measurable_mul_const g) hKo.measurableSet]
    have : (fun x => x * g) ⁻¹' (K : Set G) = (fun y => g * y) ⁻¹' (K₂ : Set G) := by
      ext x
      simp only [Set.mem_preimage, SetLike.mem_coe, hK₂, mul_assoc, inv_mul_cancel_left]
    rw [this, measure_preimage_mul]
  have hK₂eq : μ K₂ = μ K := by
    rw [measure_subgroup_eq μ K₂ K' h2 hK₂o hK'o (h3 ▸ h4),
      measure_subgroup_eq μ K K' h1 hKo hK'o h4, h3]
  have hpos : μ K ≠ 0 := hKo.measure_ne_zero μ ⟨1, K.one_mem⟩
  have hfin : μ K ≠ ∞ := hKc.measure_lt_top.ne
  rw [hmap, hK₂eq, ENNReal.smul_def, smul_eq_mul] at hc
  have h' : (1 : ℝ≥0∞) * μ K = (modularCharacterFun g : ℝ≥0∞) * μ K := by
    rw [one_mul]
    exact hc
  have := (ENNReal.mul_left_inj hpos hfin).mp h'
  exact_mod_cast this.symm

end PositivityTheory.RgUd.T.Desc.SLF.Un2
end
end

noncomputable section

open MeasureTheory MeasureTheory.Measure GroundTheory.Automorphic

namespace PositivityTheory.RgUd.T.Desc.SLF.Un2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc.SLF PositivityTheory.RgUd.T.Desc.SLT

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem lc_le {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (m : ℕ) : Lc Z m ≤ GzS Z := inf_le_left

theorem coe_lc_subgroupOf {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (m : ℕ) :
    (((Lc Z m).subgroupOf (GzS Z) : Subgroup (GzS Z)) : Set (GzS Z)) =
      Subtype.val ⁻¹' (GLnLocal.congruenceSubgroup k n m : Set (GL (Fin n) k)) := by
  ext x
  simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage, Lc, Subgroup.mem_inf]
  exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩

theorem isOpen_lc {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (m : ℕ) :
    IsOpen (((Lc Z m).subgroupOf (GzS Z) : Subgroup (GzS Z)) : Set (GzS Z)) := by
  rw [coe_lc_subgroupOf]
  exact (GLnLocal.isOpen_congruenceSubgroup k n m).preimage continuous_subtype_val

theorem isCompact_lc {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (m : ℕ) :
    IsCompact (((Lc Z m).subgroupOf (GzS Z) : Subgroup (GzS Z)) : Set (GzS Z)) := by
  rw [Subtype.isCompact_iff]
  have e : Subtype.val '' (((Lc Z m).subgroupOf (GzS Z) : Subgroup (GzS Z)) : Set (GzS Z)) =
      (GzS Z : Set (GL (Fin n) k)) ∩ (GLnLocal.congruenceSubgroup k n m : Set (GL (Fin n) k)) := by
    ext x
    simp only [Set.mem_image, SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_inter_iff, Lc, Subgroup.mem_inf]
    exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ hy, fun hx => ⟨⟨x, hx.1⟩, hx, rfl⟩⟩
  rw [e]
  exact (GLnLocal.isCompact_congruenceSubgroup k n m).inter_left (isClosed_GzS Z)

theorem unimod_of_indexSym (hI : IndexSym (k := k)) : Unimod (k := k) := by
  intro n Z hZ g
  change modularCharacterFun g = 1
  obtain ⟨c, hc⟩ := hI n Z hZ g.1 g.2
  obtain ⟨hle, heq, hne⟩ := hc c le_rfl (c + c) le_rfl
  have hmap : (Lc Z c).map (MulAut.conj g.1).toMonoidHom ≤ GzS Z := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (GzS Z).mul_mem ((GzS Z).mul_mem g.2 (lc_le Z c hy)) ((GzS Z).inv_mem g.2)
  refine modularCharacterFun_eq_one g ((Lc Z c).subgroupOf (GzS Z))
    (((Lc Z c).map (MulAut.conj g.1).toMonoidHom).subgroupOf (GzS Z)) ((Lc Z (c + c)).subgroupOf (GzS Z))
    (isCompact_lc Z c) (isOpen_lc Z c) (isOpen_lc Z (c + c)) ?_ ?_ ?_ ?_ ?_
  · intro x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, Subgroup.coe_mul,
      Subgroup.coe_inv]
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (hle hx).1
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (hle hx).2
  · rw [Subgroup.relIndex_subgroupOf hmap, Subgroup.relIndex_subgroupOf (lc_le Z c)]
    exact heq
  · rw [Subgroup.relIndex_subgroupOf (lc_le Z c)]
    exact hne

end PositivityTheory.RgUd.T.Desc.SLF.Un2
