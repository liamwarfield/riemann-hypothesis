module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGF

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGSO
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S
open Classical ValuativeRel

theorem isIntegral_iff_mem_integer (F : Type) [Field F] [ValuativeRel F] (a : F) :
    IsIntegral 𝒪[F] a ↔ a ∈ 𝒪[F] := by
  constructor
  · intro h
    exact (Valuation.integer.integers _).mem_of_integral h
  · intro h
    have e : a = algebraMap 𝒪[F] F ⟨a, h⟩ := rfl
    rw [e]
    exact isIntegral_algebraMap

theorem integral_split_count : OSplit := by
  intro F E _ _ _ _ _ _ L _ e x
  rw [L.O_def]
  have key : IsIntegral 𝒪[F] x ↔ IsIntegral 𝒪[F] (e x) := by
    constructor
    · intro h
      exact h.map ((e : E →ₐ[F] F × F).restrictScalars 𝒪[F])
    · intro h
      have h' := h.map ((e.symm : F × F →ₐ[F] E).restrictScalars 𝒪[F])
      simpa using h'
  rw [key]
  constructor
  · intro h
    exact ⟨(isIntegral_iff_mem_integer F _).1 (h.map (AlgHom.fst 𝒪[F] F F)),
      (isIntegral_iff_mem_integer F _).1 (h.map (AlgHom.snd 𝒪[F] F F))⟩
  · rintro ⟨h1, h2⟩
    exact IsIntegral.pair ((isIntegral_iff_mem_integer F _).2 h1) ((isIntegral_iff_mem_integer F _).2 h2)

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGFL
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S Polynomial
open ValuativeRel

theorem fl_cj_mem {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.9] at hx ⊢
  exact hx.map ((L.1 : E →ₐ[F] E).restrictScalars 𝒪[F])

theorem fl_mem_int {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hinj : Function.Injective (algebraMap F E))
    {a : F} (ha : algebraMap F E a ∈ L.O) : a ∈ 𝒪[F] := by
  have h1 : IsIntegral 𝒪[F] (algebraMap F E a) := (L.9 _).1 ha
  letI : FaithfulSMul F E := (faithfulSMul_iff_algebraMap_injective F E).2 hinj
  have h2 : IsIntegral 𝒪[F] a := isIntegral_algebraMap_iff.1 h1
  exact (Valuation.integer.integers _).mem_of_integral h2

theorem fl_int_mem {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (a : 𝒪[F]) : algebraMap F E a ∈ L.O := by
  rw [L.9]
  have h : IsIntegral 𝒪[F] (algebraMap 𝒪[F] E a) := isIntegral_algebraMap
  rwa [IsScalarTower.algebraMap_apply 𝒪[F] F E] at h

theorem fl_fix_int {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hinj : Function.Injective (algebraMap F E))
    {y : E} (hy : y ∈ L.O) (hc : L.cj y = y) : ∃ a : 𝒪[F], algebraMap F E a = y := by
  obtain ⟨a, ha⟩ := (L.3 y).1 hc
  have haO : a ∈ 𝒪[F] := fl_mem_int L hinj (ha ▸ hy)
  exact ⟨⟨a, haO⟩, ha⟩

theorem fl_norm {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hinj : Function.Injective (algebraMap F E))
    {x : E} (hx : x ∈ L.O) : ∃ n : 𝒪[F], algebraMap F E n = x * L.cj x := by
  refine fl_fix_int L hinj (L.O.mul_mem hx (fl_cj_mem L hx)) ?_
  rw [map_mul, L.2, mul_comm]

theorem fl_trace {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hinj : Function.Injective (algebraMap F E))
    {x : E} (hx : x ∈ L.O) : ∃ t : 𝒪[F], algebraMap F E t = x + L.cj x := by
  refine fl_fix_int L hinj (L.O.add_mem hx (fl_cj_mem L hx)) ?_
  rw [map_add (f := _), L.2, add_comm]

theorem fl_den_F {F : Type} [Field F] [ValuativeRel F] (a : F) :
    ∃ c : 𝒪[F], c ≠ 0 ∧ (c : F) * a ∈ 𝒪[F] := by
  by_cases ha : a ∈ 𝒪[F]
  · exact ⟨1, one_ne_zero, by simpa using ha⟩
  · have ha0 : a ≠ 0 := by
      rintro rfl
      exact ha (zero_mem _)
    have hv : 1 < ValuativeRel.valuation F a := by
      rw [Valuation.mem_integer_iff, not_le] at ha
      exact ha
    have hmem : a⁻¹ ∈ 𝒪[F] := by
      rw [Valuation.mem_integer_iff, map_inv₀]
      exact inv_le_one_of_one_le₀ hv.le
    refine ⟨⟨a⁻¹, hmem⟩, ?_, ?_⟩
    · intro h
      have h' := congrArg Subtype.val h
      simp [ha0] at h'
    · simp [ha0]

theorem fl_den {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (x : E) :
    ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ L.O := by
  obtain ⟨t, ht⟩ := (L.3 (x + L.cj x)).1 (by rw [map_add (f := _), L.2, add_comm])
  obtain ⟨m, hm⟩ := (L.3 (x * L.cj x)).1 (by rw [map_mul, L.2, mul_comm])
  obtain ⟨c1, hc1, ht1⟩ := fl_den_F t
  obtain ⟨c2, hc2, hm2⟩ := fl_den_F m
  refine ⟨c1 * c2, mul_ne_zero hc1 hc2, ?_⟩
  rw [L.9]
  have key : ∀ z : 𝒪[F], algebraMap 𝒪[F] E z = algebraMap F E (z : F) :=
    fun z => IsScalarTower.algebraMap_apply 𝒪[F] F E z
  have hx2 : x * x = algebraMap F E t * x - algebraMap F E m := by rw [ht, hm]; ring
  refine ⟨X ^ 2 - C (c2 * ⟨(c1 : F) * t, ht1⟩) * X + C (c1 ^ 2 * c2 * ⟨(c2 : F) * m, hm2⟩), by monicity!, ?_⟩
  simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_X_pow, eval₂_C, eval₂_X, key]
  push_cast
  try simp only [map_mul, map_pow]
  linear_combination (algebraMap F E c1 * algebraMap F E c2) ^ 2 * hx2

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.FlbHZeroRight
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S Module
open ValuativeRel

theorem flb_int_mem {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (a : 𝒪[F]) : algebraMap F E a ∈ L.O := by
  exact (L.O_def _).2 isIntegral_algebraMap

theorem flb_cj_mem {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  exact (L.O_def _).2 (((L.O_def x).1 hx).map ((L.cj : E →ₐ[F] E).restrictScalars 𝒪[F]))

theorem flb_pid {E : Type} [CommRing E] (S : Subring E) (p : E) (hp : p ∈ S)
    (hfac : ∀ x ∈ S, x ≠ 0 → ∃ k : ℕ, ∃ u ∈ S, (∃ w ∈ S, u * w = 1) ∧ x = p ^ k * u) :
    IsPrincipalIdealRing S := by
  classical
  refine ⟨fun I => ?_⟩
  have hget : ∀ x : S, x ∈ I → ∀ (j : ℕ) (u : E), u ∈ S → (∃ w ∈ S, u * w = 1) →
      (x : E) = p ^ j * u → (⟨p, hp⟩ : S) ^ j ∈ I := by
    rintro x hxI j u hu ⟨w, hw, huw⟩ hxe
    have h : (⟨p, hp⟩ : S) ^ j = x * ⟨w, hw⟩ := by
      apply Subtype.ext
      simp only [SubmonoidClass.coe_pow, Subring.coe_mul, hxe]
      rw [mul_assoc, huw, mul_one]
    rw [h]
    exact I.mul_mem_right _ hxI
  by_cases hI : ∃ x ∈ I, x ≠ 0
  · have hex : ∃ k : ℕ, (⟨p, hp⟩ : S) ^ k ∈ I := by
      obtain ⟨x, hxI, hx0⟩ := hI
      obtain ⟨k, u, hu, huw, hxe⟩ := hfac x x.2 (fun h => hx0 (Subtype.ext h))
      exact ⟨k, hget x hxI k u hu huw hxe⟩
    refine ⟨⟨(⟨p, hp⟩ : S) ^ Nat.find hex, ?_⟩⟩
    apply le_antisymm
    · intro x hxI
      by_cases hx0 : x = 0
      · rw [hx0]
        exact Submodule.zero_mem _
      obtain ⟨j, u, hu, huw, hxe⟩ := hfac x x.2 (fun h => hx0 (Subtype.ext h))
      have hkj : Nat.find hex ≤ j := Nat.find_min' hex (hget x hxI j u hu huw hxe)
      rw [Ideal.submodule_span_eq, Ideal.mem_span_singleton']
      refine ⟨(⟨p, hp⟩ : S) ^ (j - Nat.find hex) * ⟨u, hu⟩, ?_⟩
      apply Subtype.ext
      simp only [SubmonoidClass.coe_pow, Subring.coe_mul, hxe]
      rw [mul_comm, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hkj]
    · rw [Ideal.submodule_span_eq, Ideal.span_le, Set.singleton_subset_iff]
      exact Nat.find_spec hex
  · push Not at hI
    refine ⟨⟨0, ?_⟩⟩
    rw [Submodule.span_singleton_eq_bot.mpr rfl]
    exact (Submodule.eq_bot_iff I).mpr hI

section Herm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem flb_h_add_right {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add (f := _), ← H.h_herm, ← H.h_herm]

theorem flb_h_smul_right {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) (x : V) (a : E) (y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm]

theorem flb_h_sum_right {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) {ι : Type} [Fintype ι] (x : V) (c : ι → E) (v : ι → V) :
    H.h x (∑ i, c i • v i) = ∑ i, M.L.cj (c i) * H.h x (v i) := by
  have hs := map_sum (AddMonoidHom.mk' (H.h x) (flb_h_add_right H x)) (fun i => c i • v i) Finset.univ
  simp only [AddMonoidHom.mk'_apply] at hs
  rw [hs]
  exact Finset.sum_congr rfl fun i _ => flb_h_smul_right H x (c i) (v i)

theorem flb_h_sum_left {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) {ι : Type} [Fintype ι] (y : V) (c : ι → E) (v : ι → V) :
    H.h (∑ i, c i • v i) y = ∑ i, c i * H.h (v i) y := by
  have hs := map_sum (AddMonoidHom.mk' (fun z => H.h z y) (fun a b => H.h_add_left a b y))
    (fun i => c i • v i) Finset.univ
  simp only [AddMonoidHom.mk'_apply] at hs
  rw [hs]
  exact Finset.sum_congr rfl fun i _ => H.h_smul_left (c i) (v i) y

end Herm

end PI.UnitaryGroupMassFormula.CntFormula
end
end
