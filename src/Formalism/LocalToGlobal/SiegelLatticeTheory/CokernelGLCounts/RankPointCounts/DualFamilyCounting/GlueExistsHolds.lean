module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueExistsOfLastDual
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SmulMemLocFOfSP

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NormUnits
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DetUnitOfSelfdual
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LinIndOrth
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DualFormInverse
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DualFLeOfInv
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.DualFormInverse

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases Formalism.L2.SG.Pf.UnitPairSolutions

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_one {ι : Type} [Fintype ι] [DecidableEq ι] {S : Subring K} {p : ι} {α : K}
    (hα : α ∈ S) (g : ι → ι → K) :
    ∃ κ : ι → K, (∀ t, κ t ∈ S) ∧ ∀ s, ∑ t, κ t * g s t = α * g s p := by
  refine ⟨fun t => if t = p then α else 0, fun t => ?_, fun s => ?_⟩
  · dsimp only
    split_ifs
    · exact hα
    · exact S.zero_mem
  · rw [Fintype.sum_eq_single p]
    · simp
    · intro t ht
      simp [ht]

theorem exists_two {ι : Type} [Fintype ι] [DecidableEq ι] {S : Subring K} {p q : ι} (hpq : p ≠ q)
    {α β : K} (hα : α ∈ S) (hβ : β ∈ S) (g : ι → ι → K) :
    ∃ κ : ι → K, (∀ t, κ t ∈ S) ∧ ∀ s, ∑ t, κ t * g s t = α * g s p + β * g s q := by
  refine ⟨fun t => if t = p then α else if t = q then β else 0, fun t => ?_, fun s => ?_⟩
  · dsimp only
    split_ifs
    exacts [hα, hβ, S.zero_mem]
  · rw [Fintype.sum_eq_add p q hpq]
    · simp [hpq.symm]
    · rintro t ⟨h1, h2⟩
      simp [h1, h2]

theorem dualF_le_of_inv {ι : Type} [Fintype ι] [DecidableEq ι] {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hnd : Nondeg h) {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (G : ι → V)
    (hG : Submodule.span K (Set.range G) = ⊤)
    (hinv : ∀ u, ∃ κ : ι → K, (∀ t, κ t ∈ SP K 𝔭) ∧
      ∀ s, ∑ t, κ t * h (G s) (G t) = if s = u then 1 else 0) :
    dualF h 𝔭 (locF 𝔭 (Submodule.span (𝓞 K) (Set.range G))) ≤
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range G)) := by
  choose κ hκS hκ using hinv
  intro x hx
  have hX : ∀ u, h (G u) x ∈ SP K 𝔭 := fun u => by
    rw [mem_SP_iff_locF]
    exact hx (G u) (LocF.le_locF 𝔭 _ (Submodule.subset_span ⟨u, rfl⟩))
  have hyx : ∀ s, h (G s) (x - ∑ t, (∑ u, κ u t * h (G u) x) • G t) = 0 := by
    intro s
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum]
    simp only [form_smul_right]
    have e : ∀ t, (∑ u, κ u t * h (G u) x) * h (G s) (G t) =
        ∑ u, h (G u) x * (κ u t * h (G s) (G t)) := fun t => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [Finset.sum_congr rfl fun t _ => e t, Finset.sum_comm]
    simp only [← Finset.mul_sum, hκ]
    simp
  have hxy := eq_zero_of_orth hs hnd G hG hyx
  rw [sub_eq_zero] at hxy
  rw [hxy]
  refine Submodule.sum_mem _ fun t _ => smul_mem_locF_of_SP ?_ (Submodule.subset_span ⟨t, rfl⟩)
  exact (SP K 𝔭).sum_mem fun u _ => (SP K 𝔭).mul_mem (hκS u t) (hX u)

end Formalism.L2.SG.Pf.DualFormInverse
end
end

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.L2.SG.Pf.GluingBases Formalism.L2.SG.Pf.UnitPairSolutions Formalism.L2.SG.Pf.GluedFormOrthogonality
  Formalism.L2.SG.Pf.DualFormInverse

theorem family_dual_holds : FamDual := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  have := h𝔭.isPrime
  have hTop := family_top_holds K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  obtain ⟨hbU, -, hbo, hbn, ha0⟩ := hba
  obtain ⟨hwW, hwo, hwn, hτ, ⟨s₀, hu⟩, hcong, hunit⟩ := hg
  have hwn1 : ∀ j, h (w j) (w j) = algebraMap F K (c j) := fun j => (hwn j).1
  have hbw : ∀ i j, h (b i) (w j) = 0 := fun i j => form_U_orth (hbU i) (hwW j)
  have hwb : ∀ i j, h (w j) (b i) = 0 := fun i j => form_orth_U hs (hbU i) (hwW j)
  have hq0 : algebraMap F K (π : F) ≠ 0 := by
    rw [← jι_eq']; exact jι_ne_zero hu.ne_zero
  have hqS : algebraMap F K (π : F) ∈ SP K 𝔭 := by
    have := (isLocUnif (K := K) hK hF h𝔭 hu).mem
    rwa [jι_eq'] at this
  have hA0 : ∀ i, algebraMap F K ((a i : 𝓞 F) : F) ≠ 0 := fun i => by
    rw [← jι_eq']; exact jι_ne_zero (ha0 i)
  have hC0 : ∀ j, algebraMap F K (c j) ≠ 0 := fun j => (map_ne_zero _).2 (hwn j).2
  have hGr : ∀ j, glueFam K 𝔭 b a π w τ (Sum.inr j) = w j := fun j => rfl
  have hGl : ∀ i, vF 𝔭 (a i) ≠ 0 → glueFam K 𝔭 b a π w τ (Sum.inl i) =
      (algebraMap F K (π : F))⁻¹ ^ vF 𝔭 (a i) • (b i + w (τ i)) := fun i hi => by
    simp only [glueFam, Sum.elim_inl, if_neg hi]
  have hGl0 : ∀ i, vF 𝔭 (a i) = 0 → glueFam K 𝔭 b a π w τ (Sum.inl i) = b i := fun i hi => by
    simp only [glueFam, Sum.elim_inl, if_pos hi]
  have key_ii : ∀ i, h (b i + w (τ i)) (b i + w (τ i)) =
      algebraMap F K ((a i : 𝓞 F) : F) + algebraMap F K (c (τ i)) := by
    intro i
    simp only [map_add (f := _), LinearMap.add_apply, hbw, hwb, hbn, hwn1]
    ring

  have hgg : ∀ i, vF 𝔭 (a i) ≠ 0 →
      h (glueFam K 𝔭 b a π w τ (Sum.inl i)) (glueFam K 𝔭 b a π w τ (Sum.inl i)) =
        (algebraMap F K (π : F) ^ vF 𝔭 (a i))⁻¹ ^ 2 *
          (algebraMap F K ((a i : 𝓞 F) : F) + algebraMap F K (c (τ i))) := by
    intro i hi
    rw [hGl i hi, form_smul_smul, star_inv_pow hF, inv_pow (algebraMap F K (π : F)), key_ii]
    ring
  have hgw : ∀ i, vF 𝔭 (a i) ≠ 0 →
      h (glueFam K 𝔭 b a π w τ (Sum.inl i)) (glueFam K 𝔭 b a π w τ (Sum.inr (τ i))) =
        (algebraMap F K (π : F) ^ vF 𝔭 (a i))⁻¹ * algebraMap F K (c (τ i)) := by
    intro i hi
    rw [hGl i hi, hGr, form_smul_left, star_inv_pow hF, inv_pow (algebraMap F K (π : F)), map_add (f := _),
      LinearMap.add_apply, hbw, hwn1, zero_add]
  have hwg : ∀ i, vF 𝔭 (a i) ≠ 0 →
      h (glueFam K 𝔭 b a π w τ (Sum.inr (τ i))) (glueFam K 𝔭 b a π w τ (Sum.inl i)) =
        (algebraMap F K (π : F) ^ vF 𝔭 (a i))⁻¹ * algebraMap F K (c (τ i)) := by
    intro i hi
    rw [hGl i hi, hGr, form_smul_right, inv_pow (algebraMap F K (π : F)), map_add (f := _), hwb, hwn1, zero_add]
  have hww : ∀ j, h (glueFam K 𝔭 b a π w τ (Sum.inr j)) (glueFam K 𝔭 b a π w τ (Sum.inr j)) =
      algebraMap F K (c j) := fun j => by rw [hGr, hwn1]
  have hdiag0 : ∀ i, vF 𝔭 (a i) = 0 →
      h (glueFam K 𝔭 b a π w τ (Sum.inl i)) (glueFam K 𝔭 b a π w τ (Sum.inl i)) =
        algebraMap F K ((a i : 𝓞 F) : F) := fun i hi => by rw [hGl0 i hi, hbn]

  have hoff0 : ∀ i, vF 𝔭 (a i) = 0 → ∀ s, s ≠ Sum.inl i →
      h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ (Sum.inl i)) = 0 := by
    intro i hi s hs'
    rcases s with i' | j
    · exact glue_inl_inl hs hbU hbo hwW hwo hτ (fun e => hs' (congrArg Sum.inl e))
    · exact hs.eq_iff.1 (glue_inl_w hbU hwW hwo (fun h1 => absurd hi h1))
  have hoff : ∀ i, vF 𝔭 (a i) ≠ 0 → ∀ s, s ≠ Sum.inl i → s ≠ Sum.inr (τ i) →
      h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ (Sum.inl i)) = 0 ∧
        h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ (Sum.inr (τ i))) = 0 := by
    intro i hi s h1 h2
    rcases s with i' | j
    · have hii : i' ≠ i := fun e => h1 (congrArg Sum.inl e)
      exact ⟨glue_inl_inl hs hbU hbo hwW hwo hτ hii,
        glue_inl_w hbU hwW hwo (fun h3 e => hii (hτ i' i h3 hi e))⟩
    · have hj : j ≠ τ i := fun e => h2 (congrArg Sum.inr e)
      exact ⟨hs.eq_iff.1 (glue_inl_w hbU hwW hwo (fun _ e => hj e.symm)), hwo j (τ i) hj⟩
  have hoffw : ∀ j, (∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ j) → ∀ s, s ≠ Sum.inr j →
      h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ (Sum.inr j)) = 0 := by
    intro j hj s hs'
    rcases s with i | j'
    · exact glue_inl_w hbU hwW hwo (fun h3 => hj i h3)
    · exact hwo j' j (fun e => hs' (congrArg Sum.inr e))

  have hpair : ∀ i, vF 𝔭 (a i) ≠ 0 → ∀ X Y : K, X ∈ SP K 𝔭 → Y ∈ SP K 𝔭 →
      ∃ κ : Fin (finrank K U) ⊕ Fin (finrank K (orthK h U)) → K, (∀ t, κ t ∈ SP K 𝔭) ∧
        ∀ s, ∑ t, κ t * h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ t) =
          if s = Sum.inl i then X else if s = Sum.inr (τ i) then Y else 0 := by
    intro i hi X Y hX hY
    obtain ⟨r, hr, hre⟩ := (mem_noncompactPart_iff hu _ _).1 (hcong i hi)
    rw [jι_eq', map_add (f := _)] at hre
    have hre' : algebraMap F K ((a i : 𝓞 F) : F) + algebraMap F K (c (τ i)) =
        (algebraMap F K (π : F) ^ vF 𝔭 (a i)) ^ 2 * r := by
      rw [hre]; ring
    have hc := unit_part_c hK hF h𝔭 hu (ha0 i) hi (hcong i hi)
    obtain ⟨e1, e2⟩ := pair_solve (X := X) (Y := Y) (pow_ne_zero (vF 𝔭 (a i)) hq0) (hA0 i) hc.1 hre'
    obtain ⟨m1, m2⟩ := pair_coeffs_mem (𝔭 := 𝔭) (X := X) (Y := Y) ((SP K 𝔭).pow_mem hqS _)
      (unit_part hK hF h𝔭 hu (ha0 i)) hc.2 hr hX hY
    obtain ⟨κ, hκS, hκ⟩ := exists_two (Sum.inl_ne_inr (a := i) (b := τ i)) m1 m2
      (fun s t => h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ t))
    refine ⟨κ, hκS, fun s => ?_⟩
    rw [hκ s]
    by_cases h1 : s = Sum.inl i
    · subst h1
      rw [if_pos rfl, hgg i hi, hgw i hi]
      linear_combination e1
    · by_cases h2 : s = Sum.inr (τ i)
      · subst h2
        rw [if_neg h1, if_pos rfl, hwg i hi, hww]
        linear_combination e2
      · rw [if_neg h1, if_neg h2, (hoff i hi s h1 h2).1, (hoff i hi s h1 h2).2]
        ring
  refine dualF_le_of_inv hs hnd _ hTop ?_
  intro u
  rcases u with i | j
  · by_cases hi : vF 𝔭 (a i) = 0
    · have hAi : (algebraMap F K ((a i : 𝓞 F) : F))⁻¹ ∈ SP K 𝔭 := by
        have := unit_part hK hF h𝔭 hu (ha0 i)
        rwa [hi, pow_zero, mul_one] at this
      obtain ⟨κ, hκS, hκ⟩ := exists_one (p := Sum.inl i) hAi
        (fun s t => h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ t))
      refine ⟨κ, hκS, fun s => ?_⟩
      rw [hκ s]
      by_cases h1 : s = Sum.inl i
      · subst h1
        rw [if_pos rfl, hdiag0 i hi, inv_mul_cancel₀ (hA0 i)]
      · rw [if_neg h1, hoff0 i hi s h1, mul_zero]
    · obtain ⟨κ, hκS, hκ⟩ := hpair i hi 1 0 (SP K 𝔭).one_mem (SP K 𝔭).zero_mem
      refine ⟨κ, hκS, fun s => ?_⟩
      rw [hκ s]
      by_cases h1 : s = Sum.inl i <;> simp [h1]
  · by_cases hj : ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j
    · obtain ⟨i, hi, rfl⟩ := hj
      obtain ⟨κ, hκS, hκ⟩ := hpair i hi 0 1 (SP K 𝔭).zero_mem (SP K 𝔭).one_mem
      refine ⟨κ, hκS, fun s => ?_⟩
      rw [hκ s]
      by_cases h1 : s = Sum.inl i <;> simp [h1]
    · simp only [not_exists, not_and] at hj
      have hCj : (algebraMap F K (c j))⁻¹ ∈ SP K 𝔭 := by
        have := (hunit j hj).2
        rwa [map_inv₀] at this
      obtain ⟨κ, hκS, hκ⟩ := exists_one (p := Sum.inr j) hCj
        (fun s t => h (glueFam K 𝔭 b a π w τ s) (glueFam K 𝔭 b a π w τ t))
      refine ⟨κ, hκS, fun s => ?_⟩
      rw [hκ s]
      by_cases h1 : s = Sum.inr j
      · subst h1
        rw [if_pos rfl, hww, inv_mul_cancel₀ (hC0 j)]
      · rw [if_neg h1, hoffw j hj s h1, mul_zero]

end Formalism.L2.SG.Pf.Cnt
end
end

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.NormUnitsOrthogonality

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases Formalism.L2.SG.Pf.UnitPairSolutions

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

def NU (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (x : K) : Prop :=
  ∃ l : K, l ≠ 0 ∧ x * (l * star l) ∈ SP K 𝔭 ∧ (x * (l * star l))⁻¹ ∈ SP K 𝔭

variable {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime]

theorem NU.of_unit {u : K} (h1 : u ∈ SP K 𝔭) (h2 : u⁻¹ ∈ SP K 𝔭) : NU 𝔭 u :=
  ⟨1, one_ne_zero, by simpa using h1, by simpa using h2⟩

theorem NU.mul {x y : K} (hx : NU 𝔭 x) (hy : NU 𝔭 y) : NU 𝔭 (x * y) := by
  obtain ⟨a, ha, ha1, ha2⟩ := hx
  obtain ⟨b, hb, hb1, hb2⟩ := hy
  have e : x * y * (a * b * star (a * b)) = (x * (a * star a)) * (y * (b * star b)) := by
    rw [star_mul']
    ring
  refine ⟨a * b, mul_ne_zero ha hb, ?_, ?_⟩
  · rw [e]
    exact (SP K 𝔭).mul_mem ha1 hb1
  · rw [e, mul_inv]
    exact (SP K 𝔭).mul_mem ha2 hb2

theorem NU.inv {x : K} (hx : NU 𝔭 x) : NU 𝔭 x⁻¹ := by
  obtain ⟨a, ha, h1, h2⟩ := hx
  have hs : star a⁻¹ = (star a)⁻¹ := by
    first | exact star_inv₀ a | exact star_inv' a | simp
  have e : x⁻¹ * (a⁻¹ * star a⁻¹) = (x * (a * star a))⁻¹ := by
    rw [hs, mul_inv, mul_inv]
  refine ⟨a⁻¹, inv_ne_zero ha, ?_, ?_⟩
  · rw [e]
    exact h2
  · rw [e, inv_inv]
    exact h1

theorem NU.of_mul_left {x y : K} (hxy : NU 𝔭 (x * y)) (hy : NU 𝔭 y) (hy0 : y ≠ 0) : NU 𝔭 x := by
  have h := NU.mul hxy (NU.inv hy)
  rwa [mul_assoc, mul_inv_cancel₀ hy0, mul_one] at h

theorem NU.norm_mul {u z : K} (h1 : u ∈ SP K 𝔭) (h2 : u⁻¹ ∈ SP K 𝔭) (hz : z ≠ 0) :
    NU 𝔭 (star z * u * z) := by
  have hs : star z⁻¹ = (star z)⁻¹ := by
    first | exact star_inv₀ z | exact star_inv' z | simp
  have hsz : star z ≠ 0 := by
    first | exact star_ne_zero.2 hz | simpa using hz
  have e : star z * u * z * (z⁻¹ * star z⁻¹) = u := by
    rw [hs]
    calc star z * u * z * (z⁻¹ * (star z)⁻¹) = u * (z * z⁻¹) * (star z * (star z)⁻¹) := by ring
      _ = u := by rw [mul_inv_cancel₀ hz, mul_inv_cancel₀ hsz, mul_one, mul_one]
  refine ⟨z⁻¹, inv_ne_zero hz, ?_, ?_⟩
  · rw [e]
    exact h1
  · rw [e]
    exact h2

theorem NU.prod {ι : Type} (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, NU 𝔭 (f i)) :
    NU 𝔭 (∏ i ∈ s, f i) :=
  Finset.prod_induction f (NU 𝔭) (fun _ _ ha hb => NU.mul ha hb)
    (NU.of_unit (SP K 𝔭).one_mem (by rw [inv_one]; exact (SP K 𝔭).one_mem)) hf

theorem NU.pair {A C : K} (hA : A ≠ 0) (hAs : star A = A) (h1 : C * A⁻¹ ∈ SP K 𝔭)
    (h2 : A * C⁻¹ ∈ SP K 𝔭) : NU 𝔭 (A * C) := by
  have hs : star A⁻¹ = (star A)⁻¹ := by
    first | exact star_inv₀ A | exact star_inv' A | simp
  have e : A * C * (A⁻¹ * star A⁻¹) = C * A⁻¹ := by
    rw [hs, hAs]
    calc A * C * (A⁻¹ * A⁻¹) = C * A⁻¹ * (A * A⁻¹) := by ring
      _ = C * A⁻¹ := by rw [mul_inv_cancel₀ hA, mul_one]
  refine ⟨A⁻¹, inv_ne_zero hA, ?_, ?_⟩
  · rw [e]
    exact h1
  · rw [e, mul_inv, inv_inv, mul_comm]
    exact h2

section Vec

variable {V : Type} [AddCommGroup V] [Module K V]

theorem linInd_orth {ι : Type} {h : V →ₗ⋆[K] V →ₗ[K] K} (g : ι → V)
    (ho : ∀ s t, s ≠ t → h (g s) (g t) = 0) (hn : ∀ s, h (g s) (g s) ≠ 0) : LinearIndependent K g := by
  rw [linearIndependent_iff']
  intro s c hs i hi
  have key := congrArg (h (g i)) hs
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero, Finset.sum_eq_single i] at key
  · rw [map_smul, smul_eq_mul] at key
    exact (mul_eq_zero.1 key).resolve_right (hn i)
  · intro j _ hji
    rw [map_smul, ho i j (Ne.symm hji), smul_zero]
  · intro hi'
    exact absurd hi hi'

end Vec

end Formalism.L2.SG.Pf.NormUnitsOrthogonality
end
end

open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.NormUnitsOrthogonality

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.HermitianLattices.Ext.L3.integralBasisSpans Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases
  Formalism.L2.SG.Pf.UnitPairSolutions

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem det_mem_SP {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {G : Matrix κ κ K} (hG : Ent (SP K 𝔭) G) :
    G.det ∈ SP K 𝔭 := by
  have e : G.det = (SP K 𝔭).subtype
      (Matrix.det (Matrix.of fun i j => (⟨G i j, hG i j⟩ : SP K 𝔭))) := by
    rw [RingHom.map_det]; rfl
  rw [e]
  exact SetLike.coe_mem _

theorem gram_det_ne_zero {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h) (β : Basis κ K V) :
    (gramK h β).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv
  have hy : ∀ x, h x (β.equivFun.symm v) = 0 := by
    intro x
    rw [form_repr h β, LinearEquiv.apply_symm_apply, hGv]
    simp
  have h0 : β.equivFun.symm v = 0 := by
    apply hnd
    intro y
    have := hs.eq y (β.equivFun.symm v)
    rw [← this, hy y, map_zero]
  exact β.equivFun.symm.injective (by rw [h0, map_zero])

private lemma mem_locF_lemma (𝔭 : Ideal (𝓞 F)) (L : Submodule (𝓞 K) K) (x : K) :
    x ∈ locF 𝔭 L ↔ ∃ s ∈ Submonoid.closure
      {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}, s • x ∈ L := Iff.rfl

private lemma star_fix_lemma_2 (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} {s : 𝓞 K}
    (hs : s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}) :
    star (algebraMap (𝓞 K) K s) = algebraMap (𝓞 K) K s := by
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨t, -, rfl⟩ := hx
    exact (hF _).mpr ⟨(t : F), rfl⟩
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul, star_mul', hx, hy]

private lemma star_mem_SP' (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {a : K}
    (ha : a ∈ SP K 𝔭) : star a ∈ SP K 𝔭 := by
  rw [mem_SP_iff_locF] at ha ⊢
  obtain ⟨s, hs', hsa⟩ := (mem_locF_lemma 𝔭 _ a).mp ha
  obtain ⟨z, hz⟩ := Submodule.mem_one.mp hsa
  obtain ⟨r, hr⟩ := Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range z
  refine (mem_locF_lemma 𝔭 _ _).mpr ⟨s, hs', Submodule.mem_one.mpr ⟨r, ?_⟩⟩
  rw [hr, hz, Algebra.smul_def, Algebra.smul_def, star_mul', star_fix_lemma_2 hF hs']

theorem det_unit_of_selfdual (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hnd : Nondeg h) (β : Basis κ K V) {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime]
    (hsd : dualF h 𝔭 (locF 𝔭 (spanO β)) = locF 𝔭 (spanO β)) :
    (gramK h β).det ∈ SP K 𝔭 ∧ (gramK h β).det⁻¹ ∈ SP K 𝔭 := by
  have hdet := gram_det_ne_zero hs hnd β
  have hunit : IsUnit (gramK h β).det := isUnit_iff_ne_zero.mpr hdet
  have hmemL : ∀ x, x ∈ locF 𝔭 (spanO β) ↔ ∀ i, β.equivFun x i ∈ SP K 𝔭 :=
    fun x => mem_locF_iff_repr β x
  have hβ : ∀ i, β i ∈ locF 𝔭 (spanO β) := fun i => by
    simpa using smul_basis_mem β (SP K 𝔭).one_mem i
  have hdual : ∀ x ∈ locF 𝔭 (spanO β), ∀ y ∈ locF 𝔭 (spanO β),
      h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
    intro x hx
    rw [← hsd] at hx
    exact hx
  have hG : Ent (SP K 𝔭) (gramK h β) := fun i j =>
    mem_SP_iff_locF.mpr (hdual _ (hβ j) _ (hβ i))
  have hinv : gramK h β * (gramK h β)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hunit
  have hcol : ∀ k l, (gramK h β)⁻¹ l k ∈ SP K 𝔭 := by
    intro k l
    obtain ⟨x, hxdef⟩ : ∃ x : V, β.equivFun x = (gramK h β)⁻¹ *ᵥ Pi.single k (1 : K) :=
      ⟨_, LinearEquiv.apply_symm_apply _ _⟩
    have hx : x ∈ locF 𝔭 (spanO β) := by
      rw [← hsd]
      change ∀ y ∈ locF 𝔭 (spanO β), h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
      intro y hy
      rw [← mem_SP_iff_locF, form_repr h β, hxdef, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      convert star_mem_SP' hF ((hmemL y).mp hy k) using 1
      simp [dotProduct, Pi.single_apply]
    have hc := (hmemL x).mp hx l
    rw [hxdef] at hc
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hc
  have hdi : ((gramK h β)⁻¹).det = (gramK h β).det⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  refine ⟨det_mem_SP hG, ?_⟩
  rw [← hdi]
  exact det_mem_SP fun l k => hcol k l

theorem gram_change (h : V →ₗ⋆[K] V →ₗ[K] K) (β γ : Basis κ K V) :
    gramK h γ = (β.toMatrix γ)ᴴ * gramK h β * β.toMatrix γ := by
  ext i j
  have e : gramK h γ i j = h (γ i) (γ j) := rfl
  rw [e, form_repr h β, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
    Basis.toMatrix_apply, Basis.equivFun_apply, Pi.star_apply]

theorem gram_det_change (h : V →ₗ⋆[K] V →ₗ[K] K) (β γ : Basis κ K V) :
    (gramK h γ).det = star (β.toMatrix γ).det * (gramK h β).det * (β.toMatrix γ).det := by
  rw [gram_change h β γ, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]

theorem gram_det_orth (h : V →ₗ⋆[K] V →ₗ[K] K) (γ : Basis κ K V)
    (ho : ∀ s t, s ≠ t → h (γ s) (γ t) = 0) : (gramK h γ).det = ∏ s, h (γ s) (γ s) := by
  have e : gramK h γ = Matrix.diagonal fun s => h (γ s) (γ s) := by
    ext s t
    by_cases hst : s = t
    · subst hst; simp [gramK]
    · simp [gramK, Matrix.diagonal_apply_ne _ hst, ho s t hst]
  rw [e, Matrix.det_diagonal]

end Formalism.L2.SG.Pf.NormUnitsOrthogonality
end
end

open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.HermitianLattices.Ext.L3.integralBasisSpans Formalism.L2.SG.Pf.GluingBases Formalism.L2.SG.Pf.UnitPairSolutions
  Formalism.L2.SG.Pf.GluedFormOrthogonality Formalism.L2.SG.Pf.NormUnitsOrthogonality

theorem last_unit_holds : LastUnit := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hCM hFix h hS hN U hUc _ hΛ M _ _ 𝔭 h𝔭 b a hJ _ π w c τ hG j hj
  classical
  haveI : 𝔭.IsPrime := h𝔭.isPrime
  obtain ⟨hwU, hwo, hwn, hτinj, ⟨s₀, hU0⟩, hpair, hτlt, hfree⟩ := hG
  obtain ⟨hbU, hbloc, hbo, hbn, ha0⟩ := hJ
  obtain ⟨Λ₀, hΛlat, hΛu⟩ := hΛ
  have hA0 : ∀ i, algebraMap F K (a i : F) ≠ 0 := fun i => by
    rw [map_ne_zero]
    exact_mod_cast ha0 i
  have hC0 : ∀ k, algebraMap F K (c k) ≠ 0 := fun k => by
    rw [map_ne_zero]
    exact (hwn k).2
  have hπ0 : π ≠ 0 := fun e => hU0.notMem (e ▸ Submodule.zero_mem _)
  have hP0 : algebraMap F K (π : F) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast hπ0
  have hSPπ : algebraMap F K (π : F) ∈ SP K 𝔭 := by
    have := mem_SP_of_inP (K := K) hU0 (inP_of_mem_pow (K := K) (k := 0) (t := π) (by simp))
    simpa using this
  have hcard : Fintype.card (Fin (finrank K U) ⊕ Fin (finrank K (orthK h U))) = finrank K V := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Submodule.finrank_add_eq_of_isCompl hUc]
  haveI : Nonempty (Fin (finrank K U) ⊕ Fin (finrank K (orthK h U))) := ⟨Sum.inr j⟩
  let g : Fin (finrank K U) ⊕ Fin (finrank K (orthK h U)) → V := Sum.elim b w
  have horth : ∀ s t, s ≠ t → h (g s) (g t) = 0 := by
    rintro (i|i) (k|k) hst
    · exact hbo i k (fun e => hst (congrArg Sum.inl e))
    · exact form_U_orth (hbU i) (hwU k)
    · exact form_orth_U hS (hbU k) (hwU i)
    · exact hwo i k (fun e => hst (congrArg Sum.inr e))
  have hnorm : ∀ s, h (g s) (g s) ≠ 0 := by
    rintro (i|i)
    · show h (b i) (b i) ≠ 0
      rw [hbn i]
      exact hA0 i
    · show h (w i) (w i) ≠ 0
      rw [(hwn i).1]
      exact hC0 i
  have hli : LinearIndependent K g := linInd_orth g horth hnorm
  let γ := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hγ : ∀ s, γ s = g s := fun s =>
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli hcard) s
  have hdetγ : (gramK h γ).det =
      (∏ i, algebraMap F K (a i : F)) * ∏ k, algebraMap F K (c k) := by
    rw [gram_det_orth h γ (fun s t hst => by rw [hγ, hγ]; exact horth s t hst), Fintype.prod_sum_type]
    congr 1
    · exact Finset.prod_congr rfl (fun i _ => by rw [hγ]; exact hbn i)
    · exact Finset.prod_congr rfl (fun k _ => by rw [hγ]; exact (hwn k).1)
  have hfull : Submodule.IsFullLattice K Λ₀ := by
    refine { toIsLattice := hΛlat, span_eq_top := ?_ }
    obtain ⟨S, hS⟩ := hΛlat.fg
    obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset
      (nonZeroDivisors (𝓞 K)) (Finset.image (fun p : V × _ => h p.1 (γ p.2)) (S ×ˢ Finset.univ))
    have hdK : algebraMap (𝓞 K) K d ≠ 0 := by
      exact fun e => (nonZeroDivisors.ne_zero hd) (IsFractionRing.injective (𝓞 K) K (by simpa using e))
    have hmem : ∀ i, d • γ i ∈ Λ₀ := by
      intro i
      rw [← hΛu]
      simp only [HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf,
        Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
      intro y hy
      have key : ∀ y ∈ Submodule.span (𝓞 K) (S : Set V),
          ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = h y (d • γ i) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨r, hr⟩ := hint (h y (γ i)) (Finset.mem_image.mpr ⟨(y, i), Finset.mem_product.mpr ⟨hy, Finset.mem_univ _⟩, rfl⟩)
          refine ⟨r, ?_⟩
          rw [← algebraMap_smul K d, LinearMap.map_smul, smul_eq_mul]
          exact hr
        | zero => exact ⟨0, by simp⟩
        | add x y _ _ hx hy =>
          obtain ⟨a, ha⟩ := hx
          obtain ⟨b, hb⟩ := hy
          exact ⟨a + b, by simp only [map_add, LinearMap.add_apply, ha, hb]⟩
        | smul a x _ hx =>
          obtain ⟨b, hb⟩ := hx
          obtain ⟨a', ha'⟩ := Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range a
          refine ⟨a' * b, ?_⟩
          rw [map_mul, ha', hb, ← algebraMap_smul K a x, LinearMap.map_smulₛₗ₂]
          simp only [LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul]
      exact key y (by rw [hS]; exact hy)
    rw [eq_top_iff]
    intro x _
    rw [← γ.sum_repr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hi : γ i ∈ Submodule.span K (Λ₀ : Set V) := by
      have : γ i = (algebraMap (𝓞 K) K d)⁻¹ • (d • γ i) := by
        rw [← algebraMap_smul K d, smul_smul, inv_mul_cancel₀ hdK, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (hmem i))
    exact Submodule.smul_mem _ _ hi
  obtain ⟨β, -, hβ⟩ := LocalSpans.exists_basis_locF hfull h𝔭
  let e : Fin (finrank K V) ≃ Fin (finrank K U) ⊕ Fin (finrank K (orthK h U)) :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, hcard])
  let β' := β.reindex e
  have hsp : spanO β' = Submodule.span (𝓞 K) (Set.range β) := by
    show Submodule.span (𝓞 K) (Set.range ⇑(β.reindex e)) = _
    rw [Basis.range_reindex]
  have hsd : dualF h 𝔭 (locF 𝔭 (spanO β')) = locF 𝔭 (spanO β') := by
    rw [hsp, hβ, ← G7.locF_dual hFix h hΛlat.fg h𝔭.isPrime, (hΛu : HermitianLatticesTheory.dual h Λ₀ = Λ₀)]
  obtain ⟨hu1, hu2⟩ := det_unit_of_selfdual hFix hS hN β' hsd
  have hd : (β'.toMatrix γ).det ≠ 0 :=
    Matrix.det_ne_zero_of_right_inverse (Basis.toMatrix_mul_toMatrix_flip β' γ)
  have hNUγ : NU 𝔭 (gramK h γ).det := by
    rw [gram_det_change h β' γ]
    exact NU.norm_mul hu1 hu2 hd
  have hunitA : ∀ i, vF 𝔭 (a i) = 0 → NU 𝔭 (algebraMap F K (a i : F)) := by
    intro i hv
    apply NU.of_unit
    · have := mem_SP_of_inP (K := K) hU0 (inP_vF (K := K) h𝔭 (ha0 i))
      rw [hv] at this
      simpa using this
    · have := unit_part hCM hFix h𝔭 hU0 (ha0 i)
      rw [hv] at this
      simpa using this
  have hunitC : ∀ k : Fin (finrank K (orthK h U)), (k : ℕ) + 1 < finrank K (orthK h U) →
      (∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ k) → NU 𝔭 (algebraMap F K (c k)) := by
    intro k hk hk'
    obtain ⟨h1, h2⟩ := hfree k hk hk'
    apply NU.of_unit
    · simpa using mem_SP_of_inP (K := K) hU0 h1
    · simpa using mem_SP_of_inP (K := K) hU0 h2
  have hpairNU : ∀ i, vF 𝔭 (a i) ≠ 0 →
      NU 𝔭 (algebraMap F K (a i : F) * algebraMap F K (c (τ i))) := by
    intro i hv
    obtain ⟨-, hCu⟩ := unit_part_c hCM hFix h𝔭 hU0 (ha0 i) hv (hpair i hv)
    have hAu := unit_part hCM hFix h𝔭 hU0 (ha0 i)
    have hAd := mem_SP_of_inP (K := K) hU0 (inP_vF (K := K) h𝔭 (ha0 i))
    have hs := mem_SP_of_inP (K := K) hU0 (hpair i hv)
    rw [map_add (f := _)] at hs
    set A := algebraMap F K (a i : F)
    set C := algebraMap F K (c (τ i))
    set P := algebraMap F K (π : F)
    set v := vF 𝔭 (a i)
    have e1 : P ^ v * P⁻¹ ^ v = 1 := by rw [← mul_pow, mul_inv_cancel₀ hP0, one_pow]
    have hCd : P⁻¹ ^ v * C ∈ SP K 𝔭 := by
      have e2 : P⁻¹ ^ v * C = P ^ v * (P⁻¹ ^ (2 * v) * (A + C)) - P⁻¹ ^ v * A := by
        rw [two_mul, pow_add]
        linear_combination (-(P⁻¹ ^ v * (A + C))) * e1
      rw [e2]
      exact sub_mem (mul_mem (pow_mem hSPπ _) hs) hAd
    apply NU.pair (hA0 i) (star_fix hFix _)
    · have e3 : C * A⁻¹ = (P⁻¹ ^ v * C) * (A⁻¹ * P ^ v) := by
        linear_combination (-(C * A⁻¹)) * e1
      rw [e3]
      exact mul_mem hCd hAu
    · have e3 : A * C⁻¹ = (P⁻¹ ^ v * A) * (C⁻¹ * P ^ v) := by
        linear_combination (-(A * C⁻¹)) * e1
      rw [e3]
      exact mul_mem hAd hCu
  let T := Finset.univ.filter (fun i => vF 𝔭 (a i) ≠ 0)
  let S := T.image τ
  have hSj : S ⊆ Finset.univ.erase j := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro e
    have := hτlt i (Finset.mem_filter.mp hi).2
    rw [e] at this
    omega
  have hinjT : Set.InjOn τ T := fun i hi k hk e =>
    hτinj i k (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hk).2 e
  have hCprod : ∏ k, algebraMap F K (c k) = algebraMap F K (c j) *
      ((∏ i ∈ T, algebraMap F K (c (τ i))) * ∏ k ∈ (Finset.univ.erase j) \ S, algebraMap F K (c k)) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun k => algebraMap F K (c k)) (Finset.mem_univ j),
      ← Finset.prod_sdiff hSj, Finset.prod_image hinjT]
    ring
  have hAprod : ∏ i, algebraMap F K (a i : F) = (∏ i ∈ T, algebraMap F K (a i : F)) *
      ∏ i ∈ Finset.univ.filter (fun i => ¬ vF 𝔭 (a i) ≠ 0), algebraMap F K (a i : F) :=
    (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
  have htot : (gramK h γ).det = algebraMap F K (c j) *
      ((∏ i ∈ T, algebraMap F K (a i : F) * algebraMap F K (c (τ i))) *
        (∏ i ∈ Finset.univ.filter (fun i => ¬ vF 𝔭 (a i) ≠ 0), algebraMap F K (a i : F)) *
        ∏ k ∈ (Finset.univ.erase j) \ S, algebraMap F K (c k)) := by
    rw [hdetγ, hAprod, hCprod, Finset.prod_mul_distrib]
    ring
  have hX : NU 𝔭 ((∏ i ∈ T, algebraMap F K (a i : F) * algebraMap F K (c (τ i))) *
        (∏ i ∈ Finset.univ.filter (fun i => ¬ vF 𝔭 (a i) ≠ 0), algebraMap F K (a i : F)) *
        ∏ k ∈ (Finset.univ.erase j) \ S, algebraMap F K (c k)) := by
    refine NU.mul (NU.mul ?_ ?_) ?_
    · exact NU.prod _ _ fun i hi => hpairNU i (Finset.mem_filter.mp hi).2
    · exact NU.prod _ _ fun i hi => hunitA i (by simpa using (Finset.mem_filter.mp hi).2)
    · refine NU.prod _ _ fun k hk => ?_
      obtain ⟨hk1, hk2⟩ := Finset.mem_sdiff.mp hk
      have hkj : k ≠ j := (Finset.mem_erase.mp hk1).1
      apply hunitC k
      · have h1 := k.isLt
        have h2 := Fin.val_ne_of_ne hkj
        omega
      · intro i hi e
        exact hk2 (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, e⟩)
  have hX0 : (∏ i ∈ T, algebraMap F K (a i : F) * algebraMap F K (c (τ i))) *
        (∏ i ∈ Finset.univ.filter (fun i => ¬ vF 𝔭 (a i) ≠ 0), algebraMap F K (a i : F)) *
        ∏ k ∈ (Finset.univ.erase j) \ S, algebraMap F K (c k) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_ <;> refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    · exact mul_ne_zero (hA0 i) (hC0 _)
    · exact hA0 i
    · exact hC0 i
  rw [htot] at hNUγ
  exact NU.of_mul_left hNUγ hX hX0

end Formalism.L2.SG.Pf.Cnt
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueExistsOfLast
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FamilyDualHolds
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

theorem form_sum_orth {ι' : Type} [Fintype ι'] [DecidableEq ι'] (h : V →ₗ⋆[K] V →ₗ[K] K) (v : ι' → V)
    (hvo : ∀ i k, i ≠ k → h (v i) (v k) = 0) (i : ι') (x : ι' → K) :
    h (v i) (∑ k, x k • v k) = x i * h (v i) (v i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  exact Finset.sum_eq_single i (fun k _ hk => by rw [hvo i k (Ne.symm hk), mul_zero]) (by simp)

theorem form_sum_zero {ι' : Type} [Fintype ι'] (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) (v : ι' → V)
    (h0 : ∀ k, h u (v k) = 0) (x : ι' → K) : h u (∑ k, x k • v k) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, smul_eq_mul, h0, mul_zero, Finset.sum_const_zero]

theorem family_dual_holds : FamDual := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  have hp := h𝔭.isPrime
  have htop := family_top_holds K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  obtain ⟨hbU, hbL, hbo, hbn, ha0⟩ := hba
  obtain ⟨hwW, hwo, hwn, hτ, ⟨s₀, hu⟩, hcong, hunit⟩ := hg
  have hbw : ∀ i j, h (b i) (w j) = 0 := fun i j => GluedFormOrthogonality.form_U_orth (hbU i) (hwW j)
  have hwb : ∀ i j, h (w j) (b i) = 0 := fun i j => GluedFormOrthogonality.form_orth_U hs (hbU i) (hwW j)
  have hϖ0 : algebraMap F K (π : F) ≠ 0 := by rw [← jι_eq']; exact jι_ne_zero hu.ne_zero
  set L := Submodule.span (𝓞 K) (Set.range (glueFam K 𝔭 b a π w τ)) with hL
  have hGi : ∀ s, glueFam K 𝔭 b a π w τ s ∈ L := fun s => Submodule.subset_span ⟨s, rfl⟩
  have hGw : ∀ j, w j ∈ L := fun j => hGi (Sum.inr j)
  have hg1 : ∀ i, vF 𝔭 (a i) ≠ 0 → glueFam K 𝔭 b a π w τ (Sum.inl i) =
      (algebraMap F K (π : F))⁻¹ ^ vF 𝔭 (a i) • (b i + w (τ i)) := fun i hi => by
    simp only [glueFam, Sum.elim_inl, if_neg hi]
  have hg0 : ∀ i, vF 𝔭 (a i) = 0 → glueFam K 𝔭 b a π w τ (Sum.inl i) = b i := fun i hi => by
    simp only [glueFam, Sum.elim_inl, if_pos hi]
  have hGb : ∀ i, b i ∈ L := by
    intro i
    by_cases hi : vF 𝔭 (a i) = 0
    · rw [← hg0 i hi]; exact hGi _
    · have e : b i = (algebraMap (𝓞 F) (𝓞 K) π ^ vF 𝔭 (a i)) • glueFam K 𝔭 b a π w τ (Sum.inl i)
          - w (τ i) := by
        rw [hg1 i hi, ← algebraMap_smul K, smul_smul, map_pow, jι_eq', ← mul_pow,
          mul_inv_cancel₀ hϖ0, one_pow, one_smul, add_sub_cancel_right]
      rw [e]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (hGi _)) (hGw _)
  intro x hx
  have hX : ∀ z ∈ L, h z x ∈ SP K 𝔭 := fun z hz => by
    rw [mem_SP_iff_locF]; exact hx z (LocF.le_locF 𝔭 _ hz)
  have hbw_top : Submodule.span K (Set.range (Sum.elim b w)) = ⊤ := by
    rw [eq_top_iff, ← htop, Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    rcases s with i | j
    · by_cases hi : vF 𝔭 (a i) = 0
      · rw [hg0 i hi]; exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
      · rw [hg1 i hi]
        exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.subset_span ⟨Sum.inl i, rfl⟩)
          (Submodule.subset_span ⟨Sum.inr (τ i), rfl⟩))
    · exact Submodule.subset_span ⟨Sum.inr j, rfl⟩
  have hxmem : x ∈ Submodule.span K (Set.range (Sum.elim b w)) := by
    rw [hbw_top]; exact Submodule.mem_top
  obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hxmem
  rw [Fintype.sum_sum_type] at hf
  simp only [Sum.elim_inl, Sum.elim_inr] at hf
  have hbx : ∀ i, h (b i) x = f (Sum.inl i) * algebraMap F K (a i : F) := by
    intro i
    rw [← hf, map_add (f := _), form_sum_orth h b hbo i, form_sum_zero h (b i) w (hbw i), hbn, add_zero]
  have hwx : ∀ j, h (w j) x = f (Sum.inr j) * algebraMap F K (c j) := by
    intro j
    rw [← hf, map_add (f := _), form_sum_orth h w hwo j, form_sum_zero h (w j) b (fun i => hwb i j),
      (hwn j).1, zero_add]
  have hα : ∀ i, f (Sum.inl i) * algebraMap F K (a i : F) ∈ SP K 𝔭 := fun i => by
    rw [← hbx]; exact hX _ (hGb i)
  have hγ : ∀ j, f (Sum.inr j) * algebraMap F K (c j) ∈ SP K 𝔭 := fun j => by
    rw [← hwx]; exact hX _ (hGw j)
  have hσ : ∀ i, vF 𝔭 (a i) ≠ 0 → (algebraMap F K (π : F))⁻¹ ^ vF 𝔭 (a i) *
      (f (Sum.inl i) * algebraMap F K (a i : F) + f (Sum.inr (τ i)) * algebraMap F K (c (τ i))) ∈
        SP K 𝔭 := by
    intro i hi
    have h1 := hX _ (hGi (Sum.inl i))
    rwa [hg1 i hi, form_smul_left, star_inv_pow hF, map_add, LinearMap.add_apply, hbx, hwx] at h1
  have hA0 : ∀ i, algebraMap F K (a i : F) ≠ 0 := fun i => by
    rw [← jι_eq']; exact jι_ne_zero (ha0 i)

  have cf0 : ∀ i, vF 𝔭 (a i) = 0 → f (Sum.inl i) ∈ SP K 𝔭 := by
    intro i hi
    have hu' := UnitPairSolutions.unit_part hK hF h𝔭 hu (ha0 i)
    rw [hi, pow_zero, mul_one] at hu'
    have e : f (Sum.inl i) = (f (Sum.inl i) * algebraMap F K (a i : F)) *
        (algebraMap F K (a i : F))⁻¹ := by field_simp [hA0 i]
    rw [e]; exact (SP K 𝔭).mul_mem (hα i) hu'
  have cf1 : ∀ i, vF 𝔭 (a i) ≠ 0 →
      f (Sum.inl i) * algebraMap F K (π : F) ^ vF 𝔭 (a i) ∈ SP K 𝔭 := by
    intro i hi
    have hu' := UnitPairSolutions.unit_part hK hF h𝔭 hu (ha0 i)
    have e : f (Sum.inl i) * algebraMap F K (π : F) ^ vF 𝔭 (a i) =
        (f (Sum.inl i) * algebraMap F K (a i : F)) *
          ((algebraMap F K (a i : F))⁻¹ * algebraMap F K (π : F) ^ vF 𝔭 (a i)) := by
      field_simp [hA0 i]
    rw [e]; exact (SP K 𝔭).mul_mem (hα i) hu'
  have cf2 : ∀ i, vF 𝔭 (a i) ≠ 0 → f (Sum.inr (τ i)) - f (Sum.inl i) ∈ SP K 𝔭 := by
    intro i hi
    obtain ⟨hC0, huc⟩ := UnitPairSolutions.unit_part_c hK hF h𝔭 hu (ha0 i) hi (hcong i hi)
    have hua := UnitPairSolutions.unit_part hK hF h𝔭 hu (ha0 i)
    have hr := mem_SP_of_inP hu (hcong i hi)
    have hq0 : algebraMap F K (π : F) ^ vF 𝔭 (a i) ≠ 0 := pow_ne_zero _ hϖ0
    have e : f (Sum.inr (τ i)) - f (Sum.inl i) =
        ((algebraMap F K (π : F))⁻¹ ^ vF 𝔭 (a i) *
          (f (Sum.inl i) * algebraMap F K (a i : F) + f (Sum.inr (τ i)) * algebraMap F K (c (τ i)))) *
          ((algebraMap F K (c (τ i)))⁻¹ * algebraMap F K (π : F) ^ vF 𝔭 (a i)) -
        ((algebraMap F K (π : F))⁻¹ ^ (2 * vF 𝔭 (a i)) * algebraMap F K ((a i : F) + c (τ i))) *
          (f (Sum.inl i) * algebraMap F K (a i : F)) *
          ((algebraMap F K (a i : F))⁻¹ * algebraMap F K (π : F) ^ vF 𝔭 (a i)) *
          ((algebraMap F K (c (τ i)))⁻¹ * algebraMap F K (π : F) ^ vF 𝔭 (a i)) := by
      rw [map_add (f := _), inv_pow, inv_pow, pow_mul]
      field_simp [hA0 i, hC0, hϖ0]
      ring
    rw [e]
    exact (SP K 𝔭).sub_mem ((SP K 𝔭).mul_mem (hσ i hi) huc)
      ((SP K 𝔭).mul_mem ((SP K 𝔭).mul_mem ((SP K 𝔭).mul_mem hr (hα i)) hua) huc)
  classical
  set P := Finset.univ.filter (fun i => vF 𝔭 (a i) ≠ 0) with hP
  let z : Fin (finrank K (orthK h U)) → K := fun j =>
    f (Sum.inr j) - ∑ i ∈ P.filter (fun i => τ i = j), f (Sum.inl i)
  have hz : ∀ j, z j ∈ SP K 𝔭 := by
    intro j
    by_cases hj : ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j
    · obtain ⟨i, hi, rfl⟩ := hj
      have e : ∑ i' ∈ P.filter (fun i' => τ i' = τ i), f (Sum.inl i') = f (Sum.inl i) := by
        apply Finset.sum_eq_single_of_mem
        · simp [hP, hi]
        · intro i' hi' hne
          simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hi'
          exact absurd (hτ i' i hi'.1 hi hi'.2) hne
      show f (Sum.inr (τ i)) - _ ∈ _
      rw [e]; exact cf2 i hi
    · have e : ∑ i' ∈ P.filter (fun i' => τ i' = j), f (Sum.inl i') = 0 := by
        apply Finset.sum_eq_zero
        intro i' hi'
        simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hi'
        exact absurd ⟨i', hi'.1, hi'.2⟩ hj
      show f (Sum.inr j) - _ ∈ _
      rw [e, sub_zero]
      have h1 := (hunit j (fun i hi e' => hj ⟨i, hi, e'⟩)).2
      rw [map_inv₀] at h1
      have e2 : f (Sum.inr j) = (f (Sum.inr j) * algebraMap F K (c j)) * (algebraMap F K (c j))⁻¹ := by
        field_simp [(map_ne_zero _).2 (hwn j).2]
      rw [e2]; exact (SP K 𝔭).mul_mem (hγ j) h1
  let coef : Fin (finrank K U) → K := fun i => if vF 𝔭 (a i) = 0 then f (Sum.inl i) else
    f (Sum.inl i) * algebraMap F K (π : F) ^ vF 𝔭 (a i)
  have hcoef : ∀ i, coef i ∈ SP K 𝔭 := fun i => by
    simp only [coef]; split_ifs with hi
    · exact cf0 i hi
    · exact cf1 i hi
  have hterm : ∀ i, coef i • glueFam K 𝔭 b a π w τ (Sum.inl i) =
      f (Sum.inl i) • b i + (if vF 𝔭 (a i) ≠ 0 then f (Sum.inl i) • w (τ i) else 0) := by
    intro i
    by_cases hi : vF 𝔭 (a i) = 0
    · simp only [coef, if_pos hi]
      rw [hg0 i hi, if_neg (fun h' => h' hi), add_zero]
    · simp only [coef, if_neg hi]
      rw [hg1 i hi, if_pos hi, smul_smul, mul_assoc, ← mul_pow, mul_inv_cancel₀ hϖ0, one_pow,
        mul_one, smul_add]
  have hfib : ∑ j, (∑ i ∈ P.filter (fun i => τ i = j), f (Sum.inl i)) • w j =
      ∑ i ∈ P, f (Sum.inl i) • w (τ i) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := P) (t := Finset.univ) (g := τ)
      (fun i _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]
  have hdec : x = ∑ i, coef i • glueFam K 𝔭 b a π w τ (Sum.inl i) + ∑ j, z j • w j := by
    simp only [hterm, Finset.sum_add_distrib, z, sub_smul, Finset.sum_sub_distrib, hfib]
    rw [← Finset.sum_filter]
    conv_lhs => rw [← hf]
    abel
  rw [hdec]
  exact Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => UnitPairSolutions.smul_mem_locF_of_SP (hcoef i) (hGi _))
    (Submodule.sum_mem _ fun j _ => UnitPairSolutions.smul_mem_locF_of_SP (hz j) (hGw j))

end Formalism.L2.SG.Pf.GluingBases
end
end

namespace Formalism.L2.SG.Pf.Cnt

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem glueExists_of_last (hL : Formalism.L2.SG.Pf.GluingBases.LastUnit) : GlueExists :=
  glueExists_of_last_dual hL Formalism.L2.SG.Pf.GluingBases.family_dual_holds

end Formalism.L2.SG.Pf.Cnt
end

namespace Formalism.L2.SG.Pf.Cnt

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem glueExists_holds : GlueExists :=
  glueExists_of_last last_unit_holds

end Formalism.L2.SG.Pf.Cnt
