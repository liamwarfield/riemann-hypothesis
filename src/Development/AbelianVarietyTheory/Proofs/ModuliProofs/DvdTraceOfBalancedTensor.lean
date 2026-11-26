module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DvdTraceOfBalancedTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DvdTraceOfBalancedTensor
open scoped TensorProduct

namespace GlobalTheory

theorem exists_common_eigenvector_mem {K V ι : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (T : ι → V →ₗ[K] V)
    (hT : ∀ i j v, T i (T j v) = T j (T i v)) (W : Submodule K V) (hW : W ≠ ⊥)
    (hs : ∀ i, ∀ v ∈ W, T i v ∈ W) :
    ∃ v ∈ W, v ≠ 0 ∧ ∀ i, ∃ l : K, T i v = l • v := by
  obtain ⟨U, ⟨hUW, hU0, hUs⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule K V)).has_min
      {U | U ≤ W ∧ U ≠ ⊥ ∧ ∀ i, ∀ v ∈ U, T i v ∈ U} ⟨W, le_rfl, hW, hs⟩
  obtain ⟨v, hvU, hv0⟩ := (Submodule.ne_bot_iff U).1 hU0
  refine ⟨v, hUW hvU, hv0, fun i => ?_⟩
  haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.2 hU0
  obtain ⟨l, hl⟩ := Module.End.exists_eigenvalue ((T i).restrict (hUs i))
  obtain ⟨w, hw⟩ := hl.exists_hasEigenvector
  have hw1 : T i w = l • (w : V) := congrArg Subtype.val hw.apply_eq_smul
  have hw0 : (w : V) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  let U' : Submodule K V := U ⊓ LinearMap.ker (T i - l • LinearMap.id)
  have hmem : ∀ x, x ∈ U' ↔ x ∈ U ∧ T i x = l • x := by
    intro x
    simp [U', sub_eq_zero]
  have hU' : U' = U := by
    by_contra hne
    refine hmin U' ⟨le_trans inf_le_left hUW, ?_, ?_⟩ (lt_of_le_of_ne inf_le_left hne)
    · exact (Submodule.ne_bot_iff _).2 ⟨w, (hmem _).2 ⟨w.2, hw1⟩, hw0⟩
    · intro j x hx
      obtain ⟨h1, h2⟩ := (hmem x).1 hx
      exact (hmem _).2 ⟨hUs j x h1, by rw [hT, h2, map_smul]⟩
  exact ⟨l, ((hmem v).1 (hU'.symm ▸ hvU)).2⟩

section
variable {O H : Type*} [CommRing O] [CommRing H] [Algebra O H]

theorem lTensor_comp_mulLeft_of_balanced {N : Type*} [AddCommGroup N] [Module O N]
    (Θ : H ⊗[O] H) (hΘ : ∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ)
    (α : H →ₗ[O] N) (h : H) :
    LinearMap.lTensor H (α ∘ₗ LinearMap.mulLeft O h) Θ = h • LinearMap.lTensor H α Θ := by
  have h1 : ∀ t : H ⊗[O] H, LinearMap.lTensor H (α ∘ₗ LinearMap.mulLeft O h) t
      = LinearMap.lTensor H α (((1 : H) ⊗ₜ[O] h) * t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add (f := _), mul_add, hx, hy]
  have h2 : ∀ t : H ⊗[O] H, h • LinearMap.lTensor H α t
      = LinearMap.lTensor H α ((h ⊗ₜ[O] (1 : H)) * t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add (f := _), mul_add, smul_add, hx, hy]
  rw [h1, h2, hΘ]

noncomputable def contractRight (Θ : H ⊗[O] H) : Module.Dual O H →ₗ[O] H where
  toFun α := TensorProduct.rid O H (LinearMap.lTensor H α Θ)
  map_add' a b := by simp [LinearMap.lTensor_add]
  map_smul' c a := by simp [LinearMap.lTensor_smul]

theorem contractRight_apply (Θ : H ⊗[O] H) (α : Module.Dual O H) :
    contractRight Θ α = TensorProduct.rid O H (LinearMap.lTensor H α Θ) := rfl

theorem sum_contractRight_coord_tmul {ι : Type*} [Fintype ι] (b : Module.Basis ι O H)
    (Θ : H ⊗[O] H) : ∑ j, contractRight Θ (b.coord j) ⊗ₜ[O] b j = Θ := by
  induction Θ using TensorProduct.induction_on with
  | zero => simp [contractRight_apply]
  | tmul x y =>
    simp only [contractRight_apply, LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
      TensorProduct.smul_tmul, ← TensorProduct.tmul_sum, Module.Basis.coord_apply, b.sum_repr]
  | add x y hx hy =>
    simp only [contractRight_apply, map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib] at *
    rw [hx, hy]

theorem contractRight_trace {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι O H)
    (Θ : H ⊗[O] H) (hΘ : ∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ) :
    contractRight Θ (Algebra.trace O H) = Algebra.TensorProduct.lmul' O Θ := by
  have htr : Algebra.trace O H = ∑ j, (b.coord j) ∘ₗ LinearMap.mulLeft O (b j) := by
    ext y
    rw [Algebra.trace_eq_matrix_trace b]
    simp [Matrix.trace, Algebra.leftMulMatrix_eq_repr_mul, mul_comm]
  have hr : ∀ (h : H) (t : H ⊗[O] O),
      TensorProduct.rid O H (h • t) = h * TensorProduct.rid O H t := by
    intro h t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add (f := _), mul_add, smul_add, hx, hy]
  conv_rhs => rw [← sum_contractRight_coord_tmul b Θ]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [htr, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [contractRight_apply, lTensor_comp_mulLeft_of_balanced Θ hΘ, hr, ← contractRight_apply]
  simp [mul_comm]

theorem eq_zero_of_lTensor_eq_zero_of_balanced [Module.Free O H] [Module.Finite O H]
    (Θ : H ⊗[O] H) (hΘ : ∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ)
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra O K]
    (hK : ∀ ga : H →ₐ[O] K, Algebra.TensorProduct.map (AlgHom.id O H) ga Θ ≠ 0)
    (α : H →ₗ[O] K) (hα : LinearMap.lTensor H α Θ = 0) : α = 0 := by
  classical
  by_contra hne
  let b := Module.Free.chooseBasis O H
  haveI : FiniteDimensional K (H →ₗ[O] K) := Module.Finite.equiv (b.constr K)
  have hsm : ∀ (l : K) (a : H →ₗ[O] K), LinearMap.lTensor H a Θ = 0 →
      LinearMap.lTensor H (l • a) Θ = 0 := by
    intro l a ha
    have : l • a = LinearMap.mulLeft O l ∘ₗ a := by ext; simp
    rw [this, LinearMap.lTensor_comp, LinearMap.comp_apply, ha, map_zero]
  let W : Submodule K (H →ₗ[O] K) :=
    { carrier := {a | LinearMap.lTensor H a Θ = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        simp [LinearMap.lTensor_add, ha, hb]
      zero_mem' := by simp
      smul_mem' := fun l a ha => hsm l a ha }
  let T : H → (H →ₗ[O] K) →ₗ[K] (H →ₗ[O] K) := fun h =>
    { toFun := fun a => a ∘ₗ LinearMap.mulLeft O h
      map_add' := fun a b => by ext; simp
      map_smul' := fun l a => by ext; simp }
  obtain ⟨v, hvW, hv0, hv⟩ := exists_common_eigenvector_mem T
    (fun i j a => by ext; simp [T, mul_left_comm]) W
    ((Submodule.ne_bot_iff _).2 ⟨α, hα, hne⟩)
    (fun h a ha => by
      change LinearMap.lTensor H (a ∘ₗ LinearMap.mulLeft O h) Θ = 0
      rw [lTensor_comp_mulLeft_of_balanced Θ hΘ, show LinearMap.lTensor H a Θ = 0 from ha,
        smul_zero])
  choose l hl using hv
  have hl' : ∀ h x, v (h * x) = l h * v x := fun h x => by
    simpa [T] using LinearMap.congr_fun (hl h) x
  have hv1 : v 1 ≠ 0 := by
    intro h0
    apply hv0
    ext x
    simpa [h0] using hl' x 1
  let ga : H →ₐ[O] K := AlgHom.ofLinearMap ((v 1)⁻¹ • v) (by simp [hv1]) (by
    intro x y
    have h1 := hl' x y
    have h2 := hl' x 1
    rw [mul_one] at h2
    simp only [LinearMap.smul_apply, smul_eq_mul, h1, h2]
    field_simp)
  apply hK ga
  have : ∀ t : H ⊗[O] H, Algebra.TensorProduct.map (AlgHom.id O H) ga t
      = LinearMap.lTensor H ((v 1)⁻¹ • v) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [ga]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [this]
  exact hsm _ _ hvW

end

theorem dvd_trace_of_balanced_tensor :
    ∀ (O H : Type) [CommRing O] [IsLocalRing O] [CommRing H] [Algebra O H] [Module.Free O H] [Module.Finite O H] (Θ : H ⊗[O] H) (c : O), ((∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ) ∧ Algebra.TensorProduct.lmul' O Θ = algebraMap O H c ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra O K], (∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O K a = 0) → ∀ ga : H →ₐ[O] K, Algebra.TensorProduct.map (AlgHom.id O H) ga Θ ≠ 0) → ∀ h : H, c ∣ Algebra.trace O H h := by
  intro O H _ _ _ _ _ _ Θ c ⟨hΘ, hc, hK⟩ h
  classical
  let b := Module.Free.chooseBasis O H
  let K := AlgebraicClosure (IsLocalRing.ResidueField O)
  have hm : ∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O K a = 0 := by
    intro a ha
    rw [IsScalarTower.algebraMap_apply O (IsLocalRing.ResidueField O) K,
      IsLocalRing.ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff a).2 ha, map_zero]
  have hdet : IsUnit (LinearMap.toMatrix b.dualBasis b (contractRight Θ)).det := by
    by_contra hnu
    have h0 := hm _ ((IsLocalRing.mem_maximalIdeal _).2 hnu)
    rw [RingHom.map_det] at h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hv0
    have : b.constr O v = 0 := by
      apply eq_zero_of_lTensor_eq_zero_of_balanced Θ hΘ K (hK K hm)
      have hv' : ∀ i, ∑ j, b.repr (contractRight Θ (b.coord j)) i • v j = 0 := by
        intro i
        have := congrFun hv i
        simpa [Matrix.mulVec, dotProduct, LinearMap.toMatrix_apply, Algebra.smul_def,
          Module.Basis.coe_dualBasis] using this
      have e : LinearMap.lTensor H (b.constr O v) Θ
          = ∑ j, contractRight Θ (b.coord j) ⊗ₜ[O] v j := by
        conv_lhs => rw [← sum_contractRight_coord_tmul b Θ]
        set_option synthInstance.maxHeartbeats 100000 in
          simp [map_sum]
      rw [e]
      calc ∑ j, contractRight Θ (b.coord j) ⊗ₜ[O] v j
          = ∑ j, ∑ i, b i ⊗ₜ[O] (b.repr (contractRight Θ (b.coord j)) i • v j) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            conv_lhs => rw [← b.sum_repr (contractRight Θ (b.coord j))]
            simp only [TensorProduct.sum_tmul, TensorProduct.smul_tmul]
        _ = 0 := by
            rw [Finset.sum_comm]
            simp only [← TensorProduct.tmul_sum, hv', TensorProduct.tmul_zero,
              Finset.sum_const_zero]
    exact (b.constr O).injective (by rw [this, map_zero])
  let e := LinearEquiv.ofIsUnitDet hdet
  have he : ∀ a, e a = contractRight Θ a := fun a => rfl
  have : Algebra.trace O H = c • e.symm 1 := by
    apply e.injective
    rw [map_smul, e.apply_symm_apply, he, contractRight_trace b Θ hΘ, hc, Algebra.algebraMap_eq_smul_one]
  rw [this]
  exact Dvd.intro _ rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DvdTraceOfBalancedTensorStatement
open scoped TensorProduct
theorem _root_.GlobalTheory.T.dvd_trace_of_tensor_lmul_eq : ∀ (O H : Type) [CommRing O] [IsLocalRing O] [CommRing H] [Algebra O H] [Module.Free O H] [Module.Finite O H] (Θ : H ⊗[O] H) (c : O), ((∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ) ∧ Algebra.TensorProduct.lmul' O Θ = algebraMap O H c ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra O K], (∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O K a = 0) → ∀ ga : H →ₐ[O] K, Algebra.TensorProduct.map (AlgHom.id O H) ga Θ ≠ 0) → ∀ h : H, c ∣ Algebra.trace O H h := by
  first | exact @GlobalTheory.dvd_trace_of_balanced_tensor | exact GlobalTheory.dvd_trace_of_balanced_tensor | (intros; apply GlobalTheory.dvd_trace_of_balanced_tensor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAlgClosedJoinOfTwoFieldExtensions
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCommonAlgClosedExtension
namespace GlobalTheory.CommonAlgClosedExtension

open scoped TensorProduct

theorem exists_common_algClosed_extension (K₀ K K' : Type) [Field K₀] [Field K] [Field K']
    (i : K₀ →+* K) (i' : K₀ →+* K') :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (j : K →+* Ω) (j' : K' →+* Ω),
      RingHom.comp j i = RingHom.comp j' i' := by
  letI : Algebra K₀ K := i.toAlgebra
  letI : Algebra K₀ K' := i'.toAlgebra
  haveI : Nontrivial (K ⊗[K₀] K') := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[K₀] K')
  letI : Field ((K ⊗[K₀] K') ⧸ m) := Ideal.Quotient.field m
  let φ : (K ⊗[K₀] K') →+* AlgebraicClosure ((K ⊗[K₀] K') ⧸ m) :=
    (algebraMap ((K ⊗[K₀] K') ⧸ m) _).comp (Ideal.Quotient.mk m)
  refine ⟨AlgebraicClosure ((K ⊗[K₀] K') ⧸ m), inferInstance, inferInstance,
    φ.comp (Algebra.TensorProduct.includeLeft (R := K₀) (S := K₀) (A := K) (B := K')).toRingHom,
    φ.comp (Algebra.TensorProduct.includeRight (R := K₀) (A := K) (B := K')).toRingHom, ?_⟩
  ext x
  have h1 := (Algebra.TensorProduct.includeLeft (R := K₀) (S := K₀) (A := K) (B := K')).commutes x
  have h2 := (Algebra.TensorProduct.includeRight (R := K₀) (A := K) (B := K')).commutes x
  exact congrArg φ (h1.trans h2.symm)

end GlobalTheory.CommonAlgClosedExtension
end

open scoped TensorProduct

namespace GlobalTheory

theorem exists_algClosed_join_of_two_field_extensions
    (K₀ K K' : Type) [Field K₀] [Field K] [Field K'] (i : K₀ →+* K) (i' : K₀ →+* K') :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (j : K →+* Ω) (j' : K' →+* Ω),
      j.comp i = j'.comp i' := by
  apply _root_.GlobalTheory.CommonAlgClosedExtension.exists_common_algClosed_extension <;> assumption

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingOfFlatOfFormallyUnramified
open scoped TensorProduct

namespace GlobalTheory

theorem isBezout_of_flat_of_formallyUnramified (W B : Type) [CommRing W] [IsDomain W] [IsBezout W]
    [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra W B] [Module.Flat W B]
    [Algebra.EssFiniteType W B] [Algebra.FormallyUnramified W B] : IsBezout B := by
  refine ⟨fun J hJ => ?_⟩
  have hfin : Module.Finite B J := Module.Finite.iff_fg.2 hJ
  have htB : Submodule.torsion W B = ⊥ :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.1 inferInstance
  have hW : Module.Flat W J := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro x ⟨a, ha⟩
    have hx : (x : B) ∈ Submodule.torsion W B := ⟨a, congrArg Subtype.val ha⟩
    rw [htB, Submodule.mem_bot] at hx
    exact (Submodule.mem_bot W).2 (Subtype.ext hx)
  have hB : Module.Flat B J := Algebra.FormallyUnramified.flat_of_restrictScalars W B J
  have hfree : Module.Free B J := Module.free_of_flat_of_isLocalRing
  rw [← Submodule.rank_le_one_iff_isPrincipal]
  exact (Submodule.rank_le J).trans (Module.rank_self B).le

theorem isAlgebraic_of_flat_of_formallyUnramified (W B : Type) [CommRing W] [IsDomain W]
    [CommRing B] [Algebra W B] [Module.Flat W B]
    [Algebra.EssFiniteType W B] [Algebra.FormallyUnramified W B] : Algebra.IsAlgebraic W B := by
  let K := FractionRing W
  have hfin : Module.Finite K (K ⊗[W] B) := Algebra.FormallyUnramified.finite_of_free K _
  have halg : Algebra.IsAlgebraic K (K ⊗[W] B) := inferInstance
  have hK : Algebra.IsAlgebraic W K := IsLocalization.isAlgebraic K (nonZeroDivisors W)
  have halgW : Algebra.IsAlgebraic W (K ⊗[W] B) := Algebra.IsAlgebraic.trans W K _
  exact Algebra.IsAlgebraic.of_injective
    (Algebra.TensorProduct.includeRight (R := W) (A := K) (B := B))
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective W K))

theorem valuationRing_of_flat_of_formallyUnramified :
    ∀ (W B : Type) [CommRing W] [IsDomain W] [ValuationRing W] [CommRing B] [IsDomain B]
      [IsLocalRing B] [Algebra W B] [Module.Flat W B] [Algebra.EssFiniteType W B]
      [Algebra.FormallyUnramified W B], ValuationRing B ∧ Algebra.IsAlgebraic W B := by
  intro W B _ _ _ _ _ _ _ _ _ _
  have := isBezout_of_flat_of_formallyUnramified W B
  exact ⟨inferInstance, isAlgebraic_of_flat_of_formallyUnramified W B⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EntireAntilinearLatticePeriodsConst
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EntireAntilinearLatticePeriodsConst
open Complex Matrix
open scoped ContDiff BigOperators Real

namespace GlobalTheory

theorem eq_zero_of_norm_real_mul_le {c : ℂ} {C : ℝ} (h : ∀ r : ℝ, ‖(r : ℂ) * c‖ ≤ C) : c = 0 := by
  by_contra hc
  have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have h0 : 0 ≤ C := (norm_nonneg _).trans (h 0)
  have key := h ((C + 1) / ‖c‖)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (by linarith) hpos.le), div_mul_cancel₀ _ hpos.ne'] at key
  linarith

theorem entire_sub_conj_bounded_const {φ : ℂ → ℂ} {b : ℂ} {C : ℝ} (hφ : Differentiable ℂ φ)
    (h : ∀ s, ‖φ s - (starRingEnd ℂ) s * b‖ ≤ C) : b = 0 ∧ ∀ s, φ s = φ 0 := by

  have hshift : ∀ a s, φ (s + a) - φ s = φ a - φ 0 := by
    intro a
    have hd : Differentiable ℂ (fun s => φ (s + a) - φ s) :=
      (hφ.comp (differentiable_id.add_const a)).sub hφ
    have hbd : Bornology.IsBounded (Set.range (fun s => φ (s + a) - φ s)) := by
      rw [isBounded_iff_forall_norm_le]
      refine ⟨2 * C + ‖(starRingEnd ℂ) a * b‖, ?_⟩
      rintro _ ⟨s, rfl⟩
      show ‖φ (s + a) - φ s‖ ≤ _
      have e : φ (s + a) - φ s = ((φ (s + a) - (starRingEnd ℂ) (s + a) * b)
          - (φ s - (starRingEnd ℂ) s * b)) + (starRingEnd ℂ) a * b := by
        rw [map_add (f := _)]; ring
      rw [e]
      calc _ ≤ ‖(φ (s + a) - (starRingEnd ℂ) (s + a) * b) - (φ s - (starRingEnd ℂ) s * b)‖
            + ‖(starRingEnd ℂ) a * b‖ := norm_add_le _ _
        _ ≤ (‖φ (s + a) - (starRingEnd ℂ) (s + a) * b‖ + ‖φ s - (starRingEnd ℂ) s * b‖)
            + ‖(starRingEnd ℂ) a * b‖ := by gcongr; exact norm_sub_le _ _
        _ ≤ _ := by linarith [h (s + a), h s]
    intro s
    simpa [zero_add] using hd.apply_eq_apply_of_bounded hbd s 0

  have hderiv : ∀ s, deriv φ s = deriv φ 0 := by
    intro s
    have e1 : (fun x => φ (x + s)) = fun x => φ x + (φ s - φ 0) := by
      funext x
      linear_combination hshift s x
    have e2 := congrArg (fun f => deriv f 0) e1
    simp only [deriv_comp_add_const, deriv_add_const, zero_add] at e2
    exact e2

  obtain ⟨β, hlin⟩ : ∃ β : ℂ, ∀ s, φ s = φ 0 + β * s := by
    refine ⟨deriv φ 0, fun s => ?_⟩
    have hd : Differentiable ℂ (fun s => φ s - deriv φ 0 * s) :=
      hφ.sub (differentiable_id.const_mul _)
    have hz : ∀ x, deriv (fun s => φ s - deriv φ 0 * s) x = 0 := by
      intro x
      have hx : HasDerivAt (fun s => φ s - deriv φ 0 * s) (deriv φ x - deriv φ 0 * 1) x :=
        (hφ x).hasDerivAt.sub ((hasDerivAt_id' x).const_mul _)
      rw [hx.deriv, hderiv x]
      ring
    have := is_const_of_deriv_eq_zero hd hz s 0
    linear_combination this

  have hB : ∀ s, ‖β * s - (starRingEnd ℂ) s * b‖ ≤ C + ‖φ 0‖ := by
    intro s
    have e : β * s - (starRingEnd ℂ) s * b = (φ s - (starRingEnd ℂ) s * b) - φ 0 := by
      rw [hlin s]; ring
    rw [e]
    exact (norm_sub_le _ _).trans (by linarith [h s])
  have h1 : β - b = 0 := eq_zero_of_norm_real_mul_le (C := C + ‖φ 0‖) fun r => by
    have hr := hB r
    rw [Complex.conj_ofReal] at hr
    calc ‖(r : ℂ) * (β - b)‖ = ‖β * (r : ℂ) - (r : ℂ) * b‖ := by congr 1; ring
      _ ≤ _ := hr
  have h2 : Complex.I * (β + b) = 0 := eq_zero_of_norm_real_mul_le (C := C + ‖φ 0‖) fun r => by
    have hr := hB (r * Complex.I)
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I] at hr
    calc ‖(r : ℂ) * (Complex.I * (β + b))‖
        = ‖β * ((r : ℂ) * Complex.I) - (r : ℂ) * -Complex.I * b‖ := by congr 1; ring
      _ ≤ _ := hr
  have h3 : β + b = 0 := (mul_eq_zero.mp h2).resolve_left Complex.I_ne_zero
  have hβ : β = 0 := by linear_combination (h1 + h3) / 2
  refine ⟨by linear_combination (h3 - h1) / 2, fun s => ?_⟩
  rw [hlin s, hβ, zero_mul, add_zero]

theorem entire_antilinear_periods_const :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∀ (v : (Fin g → ℂ) → ℂ) (t : (Fin g → ℂ)), Differentiable ℂ v →
        (∀ (l : Λ) z, v (z + l) = v z + t ⬝ᵥ star (l : (Fin g → ℂ))) →
        t = 0 ∧ ∀ z, v z = v 0 := by
  intro g Λ hdisc hspan v t hv hper
  have : IsZLattice ℝ Λ := ⟨hspan⟩

  have hcont : Continuous (fun z => v z - t ⬝ᵥ star z) :=
    hv.continuous.sub (continuous_const.dotProduct continuous_star)
  have hperw : ∀ z w, w ∈ Λ → (fun z => v z - t ⬝ᵥ star z) (z + w) = (fun z => v z - t ⬝ᵥ star z) z := by
    intro z w hw
    simp only
    rw [hper ⟨w, hw⟩ z, star_add, dotProduct_add]
    ring
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp
    (IsZLattice.isCompact_range_of_periodic Λ _ hcont hperw).isBounded

  have hline : ∀ d : Fin g → ℂ, t ⬝ᵥ star d = 0 ∧ ∀ s : ℂ, v (s • d) = v 0 := by
    intro d
    have hd : Differentiable ℂ (fun s : ℂ => v (s • d)) :=
      hv.comp (differentiable_id.smul_const d)
    have hb : ∀ s : ℂ, ‖v (s • d) - (starRingEnd ℂ) s * (t ⬝ᵥ star d)‖ ≤ M := by
      intro s
      have e : (starRingEnd ℂ) s * (t ⬝ᵥ star d) = t ⬝ᵥ star (s • d) := by
        rw [star_smul, dotProduct_smul, smul_eq_mul, starRingEnd_apply]
      rw [e]
      exact hM _ ⟨s • d, rfl⟩
    obtain ⟨h1, h2⟩ := entire_sub_conj_bounded_const hd hb
    exact ⟨h1, fun s => by simpa using h2 s⟩
  refine ⟨?_, fun z => by simpa using (hline z).2 1⟩
  funext i
  have hi := (hline (Pi.single i 1)).1
  rw [← Pi.single_star, star_one, dotProduct_single, mul_one] at hi
  simpa using hi

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EntireAntilinearLatticePeriodsConstStatement
open Complex Matrix
open scoped ContDiff BigOperators Real
theorem _root_.GlobalTheory.T.entire_antilinear_lattice_periods_const : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (v : (Fin g → ℂ) → ℂ) (t : (Fin g → ℂ)), Differentiable ℂ v → (∀ (l : Λ) z, v (z + l) = v z + t ⬝ᵥ star (l : (Fin g → ℂ))) → t = 0 ∧ ∀ z, v z = v 0 := by
  first | exact @GlobalTheory.entire_antilinear_periods_const | exact GlobalTheory.entire_antilinear_periods_const | (intros; apply GlobalTheory.entire_antilinear_periods_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmoothPeriodicPartitionOfUnity
open Complex Matrix
open scoped ContDiff BigOperators Real Topology Pointwise Manifold

namespace GlobalTheory.PeriodicPartition

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem _root_.GlobalTheory.PeriodicPartition.locallyFinite_support_translate (Λ : Submodule ℤ E) [DiscreteTopology Λ] (φ : E → ℝ)
    (hφ : HasCompactSupport φ) :
    LocallyFinite fun l : Λ => Function.support fun z : E => φ (z + l) := by
  intro x
  refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, ?_⟩
  have hclosed : IsClosed (Λ : Set E) :=
    (Λ.toAddSubgroup).isClosed_of_discreteTopology
  have hfin : ((tsupport φ - Metric.closedBall x 1) ∩ (Λ : Set E)).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      (hφ.isBounded.sub Metric.isBounded_closedBall) hclosed
  refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
  rintro l ⟨z, hz, hzb⟩
  refine ⟨?_, l.2⟩
  have hmem := Set.sub_mem_sub (subset_tsupport φ (show z + (l : E) ∈ Function.support φ from hz)) hzb
  rwa [add_sub_cancel_left] at hmem

theorem _root_.GlobalTheory.PeriodicPartition.exists_finite_subcover (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {κ : Type} (V : κ → Set E) (hV : ∀ k, IsOpen (V k))
    (hper : ∀ k (l : Λ) z, z ∈ V k → z + l ∈ V k) (hcov : ∀ z, ∃ k, z ∈ V k) :
    ∃ t : Finset κ, ∀ z, ∃ k ∈ t, z ∈ V k := by
  classical
  let b := Module.Free.chooseBasis ℤ Λ
  let b' := b.ofZLatticeBasis ℝ Λ
  have hK : IsCompact (closure (ZSpan.fundamentalDomain b')) :=
    (ZSpan.fundamentalDomain_isBounded b').isCompact_closure
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover V hV (fun z _ => Set.mem_iUnion.2 (hcov z))
  refine ⟨t, fun z => ?_⟩
  obtain ⟨k, hk, hz⟩ := Set.mem_iUnion₂.1 (ht (subset_closure (ZSpan.fract_mem_fundamentalDomain b' z)))
  have hmem : (ZSpan.floor b' z : E) ∈ Λ := by
    exact (b.ofZLatticeBasis_span ℝ Λ).le (ZSpan.floor b' z).2
  refine ⟨k, hk, ?_⟩
  simpa [ZSpan.fract_apply] using hper k ⟨_, hmem⟩ _ hz

end GlobalTheory.PeriodicPartition

namespace GlobalTheory

section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem hasFiniteSupport_lattice_translate (Λ : Submodule ℤ E) [DiscreteTopology Λ] (φ : E → ℝ)
    (hφ : HasCompactSupport φ) (z : E) :
    Function.HasFiniteSupport fun l : Λ => φ (z + l) :=
  (_root_.GlobalTheory.PeriodicPartition.locallyFinite_support_translate Λ φ hφ).point_finite z

private theorem contDiff_finsum_of_locallyFinite_support {ι : Type} {f : ι → E → ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hlf : LocallyFinite fun i => Function.support (f i)) :
    ContDiff ℝ ∞ fun x => ∑ᶠ i, f i x := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨s, hs⟩ := finsum_eventually_eq_sum hlf x
  exact (ContDiff.sum fun i _ => hf i).contDiffAt.congr_of_eventuallyEq hs

private theorem contDiff_finsum_lattice_translate (Λ : Submodule ℤ E) [DiscreteTopology Λ] (φ : E → ℝ)
    (hφ : HasCompactSupport φ) (hs : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ fun z => ∑ᶠ l : Λ, φ (z + l) :=
  contDiff_finsum_of_locallyFinite_support (fun l => hs.comp (contDiff_id.add contDiff_const))
    (_root_.GlobalTheory.PeriodicPartition.locallyFinite_support_translate Λ φ hφ)

private theorem finsum_lattice_translate_add (Λ : Submodule ℤ E) (φ : E → ℝ) (l : Λ) (z : E) :
    ∑ᶠ m : Λ, φ (z + l + m) = ∑ᶠ m : Λ, φ (z + m) := by
  rw [← finsum_comp_equiv (Equiv.addLeft l) (f := fun m : Λ => φ (z + m))]
  simp [add_assoc]

private theorem tsupport_finsum_lattice_translate_subset (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (φ : E → ℝ) (hφ : HasCompactSupport φ) (U : Set E) (hU : tsupport φ ⊆ U)
    (hper : ∀ (l : Λ) z, z ∈ U → z + l ∈ U) :
    tsupport (fun z => ∑ᶠ l : Λ, φ (z + l)) ⊆ U := by
  have hlf := _root_.GlobalTheory.PeriodicPartition.locallyFinite_support_translate Λ φ hφ
  have h1 : Function.support (fun z => ∑ᶠ l : Λ, φ (z + l)) ⊆
      ⋃ l : Λ, Function.support fun z => φ (z + l) := by
    intro z hz
    by_contra h
    simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at h
    exact hz (by simp [h])
  intro z hz
  have hz' := closure_mono h1 hz
  rw [hlf.closure_iUnion] at hz'
  obtain ⟨l, hl⟩ := Set.mem_iUnion.1 hz'
  have hl' : z + l ∈ tsupport φ := tsupport_comp_subset_preimage φ (continuous_add_const (l : E)) hl
  simpa using hper (-l) _ (hU hl')
end

theorem _root_.GlobalTheory.exists_smooth_periodic_partition_of_unity :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (ι : Type) (U : ι → Set (Fin g → ℂ)), (∀ i, IsOpen (U i)) → (∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i) → (∀ z, ∃ i, z ∈ U i) → ∃ (s : Finset ι) (ρ : ι → (Fin g → ℂ) → ℝ), (∀ i, ContDiff ℝ ∞ (ρ i) ∧ (∀ (l : Λ) z, ρ i (z + l) = ρ i z) ∧ tsupport (ρ i) ⊆ U i) ∧ ∀ z, ∑ i ∈ s, ρ i z = 1 := by
  intro g Λ hdisc hspan ι U hU hper hcov
  haveI := hdisc
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.PeriodicPartition.exists_finite_subcover Λ
    (fun x : Fin g → ℂ => {z | ∃ l : Λ, z + (l : Fin g → ℂ) ∈ Metric.ball x 1})
    (fun x => by
      have hset : {z | ∃ l : Λ, z + (l : Fin g → ℂ) ∈ Metric.ball x 1} =
          ⋃ l : Λ, (· + (l : Fin g → ℂ)) ⁻¹' Metric.ball x 1 := by
        ext z; simp
      rw [hset]
      exact isOpen_iUnion fun l => Metric.isOpen_ball.preimage (continuous_add_const _))
    (fun x l z ⟨m, hm⟩ => ⟨m - l, by
      have hzm : z + (l : Fin g → ℂ) + ((m - l : Λ) : Fin g → ℂ) = z + m := by push_cast; abel
      rw [hzm]
      exact hm⟩)
    (fun z => ⟨z, 0, by simp⟩)
  let β : (Fin g → ℂ) → (Fin g → ℂ) → ℝ := fun x => ⇑(⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump x)
  let θ : (Fin g → ℂ) → ℝ := fun z => ∑ x ∈ t, β x z
  have hθs : ContDiff ℝ ∞ θ := ContDiff.sum fun x _ => ContDiffBump.contDiff _
  have hθc : HasCompactSupport θ := by
    have hθeq : θ = ∑ x ∈ t, β x := by
      funext z
      simp [θ, Finset.sum_apply]
    rw [hθeq]
    exact HasCompactSupport.finset_sum fun x _ => ContDiffBump.hasCompactSupport _
  have hθn : ∀ z, 0 ≤ θ z := fun z => Finset.sum_nonneg fun x _ => ContDiffBump.nonneg _
  have hθ1 : ∀ x ∈ t, ∀ y ∈ Metric.ball x 1, 1 ≤ θ y := by
    intro x hx y hy
    have h := Finset.single_le_sum (f := fun x => β x y) (fun x _ => ContDiffBump.nonneg _) hx
    have h1 : β x y = 1 := ContDiffBump.one_of_mem_closedBall _ (Metric.ball_subset_closedBall hy)
    show 1 ≤ ∑ x ∈ t, β x y
    linarith
  obtain ⟨p, hp⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Fin g → ℂ) isClosed_univ U hU
    (fun z _ => Set.mem_iUnion.2 (hcov z))
  have hps : ∀ i, ContDiff ℝ ∞ (p i) := fun i => contMDiff_iff_contDiff.1 (p i).contMDiff
  have hsfin := p.locallyFinite.finite_nonempty_inter_compact hθc
  let s := hsfin.toFinset
  have hkey : ∀ y, θ y * ∑ i ∈ s, p i y = θ y := by
    intro y
    by_cases hy : θ y = 0
    · simp [hy]
    · have hsum : ∑ᶠ i, p i y = ∑ i ∈ s, p i y := by
        apply finsum_eq_sum_of_support_subset
        intro i hi
        simp only [s, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
        exact ⟨y, hi, subset_tsupport _ hy⟩
      rw [← hsum, p.sum_eq_one (Set.mem_univ y), mul_one]
  let a : ι → (Fin g → ℂ) → ℝ := fun i z => θ z * p i z
  have has : ∀ i, ContDiff ℝ ∞ (a i) := fun i => hθs.mul (hps i)
  have hac : ∀ i, HasCompactSupport (a i) := fun i => hθc.mul_right
  have hat : ∀ i, tsupport (a i) ⊆ U i := fun i => tsupport_mul_subset_right.trans (hp i)
  let Θ : (Fin g → ℂ) → ℝ := fun z => ∑ᶠ l : Λ, θ (z + l)
  have hΘpos : ∀ z, 0 < Θ z := by
    intro z
    obtain ⟨x, hx, l, hl⟩ := ht z
    exact lt_of_lt_of_le one_pos ((hθ1 x hx _ hl).trans
      (single_le_finsum l (hasFiniteSupport_lattice_translate Λ θ hθc z) fun m => hθn _))
  have hΘs : ContDiff ℝ ∞ Θ := contDiff_finsum_lattice_translate Λ θ hθc hθs
  refine ⟨s, fun i z => (∑ᶠ l : Λ, a i (z + l)) / Θ z, fun i => ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (contDiff_finsum_lattice_translate Λ (a i) (hac i) (has i)).div hΘs fun z => (hΘpos z).ne'
  · intro l z
    simp only [Θ]
    rw [finsum_lattice_translate_add, finsum_lattice_translate_add]
  · show tsupport (fun z => (∑ᶠ l : Λ, a i (z + l)) / Θ z) ⊆ U i
    have hfun : (fun z => (∑ᶠ l : Λ, a i (z + l)) / Θ z) =
        fun z => (∑ᶠ l : Λ, a i (z + l)) * (Θ z)⁻¹ := by
      ext z; rw [div_eq_mul_inv]
    rw [hfun]
    exact tsupport_mul_subset_left.trans
      (tsupport_finsum_lattice_translate_subset Λ (a i) (hac i) (U i) (hat i) (hper i))
  · intro z
    show ∑ i ∈ s, (∑ᶠ l : Λ, a i (z + l)) / Θ z = 1
    rw [← Finset.sum_div, div_eq_one_iff_eq (hΘpos z).ne',
      ← finsum_sum_comm s (fun (l : Λ) i => a i (z + l))
        (fun i _ => hasFiniteSupport_lattice_translate Λ (a i) (hac i) z)]
    apply finsum_congr
    intro l
    simp only [a]
    rw [← Finset.mul_sum]
    exact hkey _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TracePowerSumModEq
open Polynomial

namespace GlobalTheory.TraceAeval

open Module

theorem trace_aeval_of_isNilpotent {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (g : Module.End ℂ V) (μ : ℂ) (h : IsNilpotent (g - algebraMap ℂ _ μ)) (p : ℂ[X]) :
    LinearMap.trace ℂ V (aeval g p) = (finrank ℂ V : ℂ) * p.eval μ := by
  have hk : ∀ k : ℕ, LinearMap.trace ℂ V (g ^ k) = (finrank ℂ V : ℂ) * μ ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent μ
        ((Commute.refl g).pow_left k) h
      rw [pow_succ, Module.End.mul_eq_comp, this, ih]; ring
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), hp, hq, eval_add]; ring
  | monomial k a =>
    rw [aeval_monomial, ← Algebra.smul_def, map_smul, hk, eval_monomial, smul_eq_mul]; ring

theorem coe_aeval_restrict {V : Type*} [AddCommGroup V] [Module ℂ V] (f : Module.End ℂ V)
    (N : Submodule ℂ V) (hf : ∀ x ∈ N, f x ∈ N) (p : ℂ[X]) (x : N) :
    ((aeval (f.restrict hf) p x : N) : V) = aeval f p x := by
  have hk : ∀ (k : ℕ) (x : N), ((((f.restrict hf) ^ k) x : N) : V) = (f ^ k) x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => intro x; simp [pow_succ, ih]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial k a => simp [aeval_monomial, hk]

theorem trace_aeval_end {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (f : Module.End ℂ V) (p : ℂ[X]) :
    LinearMap.trace ℂ V (aeval f p) = (f.charpoly.roots.map fun z => p.eval z).sum := by
  classical
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    f.independent_maxGenEigenspace (Module.End.iSup_maxGenEigenspace_eq_top f)
  have h_fin : {μ | f.maxGenEigenspace μ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep f.independent_maxGenEigenspace
  have hf : ∀ μ, ∀ x ∈ f.maxGenEigenspace μ, f x ∈ f.maxGenEigenspace μ :=
    fun μ => f.mapsTo_maxGenEigenspace_of_comm (Commute.refl _) μ
  have hp : ∀ μ, Set.MapsTo (aeval f p) (f.maxGenEigenspace μ) (f.maxGenEigenspace μ) := by
    intro μ x hx
    rw [show aeval f p x = _ from (coe_aeval_restrict f _ (hf μ) p ⟨x, hx⟩).symm]
    exact Subtype.mem _
  rw [LinearMap.trace_eq_sum_trace_restrict' hds h_fin hp]
  have h1 : ∀ μ, LinearMap.trace ℂ _ ((aeval f p).restrict (hp μ))
      = (f.charpoly.rootMultiplicity μ : ℂ) * p.eval μ := by
    intro μ
    have e : (aeval f p).restrict (hp μ) = aeval (f.restrict (hf μ)) p := by
      ext x
      rw [coe_aeval_restrict]; rfl
    have hn := f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ
    have e2 : f.restrict (hf μ) - algebraMap ℂ _ μ = (f - algebraMap ℂ _ μ).restrict
        (f.mapsTo_maxGenEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ) := by
      ext x
      rfl
    rw [e, trace_aeval_of_isNilpotent _ μ (e2 ▸ hn), LinearMap.finrank_maxGenEigenspace_eq]
  simp_rw [h1]
  rw [Finset.sum_multiset_map_count]
  have hs : h_fin.toFinset = f.charpoly.roots.toFinset := by
    ext μ
    rw [Set.Finite.mem_toFinset, Multiset.mem_toFinset, Set.mem_setOf_eq,
      ← Multiset.count_ne_zero, count_roots, ← LinearMap.finrank_maxGenEigenspace_eq,
      Ne, Ne, Submodule.finrank_eq_zero]
  rw [hs]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [count_roots, nsmul_eq_mul]

theorem trace_aeval_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (p : ℂ[X]) :
    (aeval A p).trace = (A.charpoly.roots.map fun z => p.eval z).sum := by
  rw [← Matrix.charpoly_toLin', ← trace_aeval_end, ← Matrix.trace_toLin'_eq]
  congr 1
  exact (aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin n)) A p).symm

noncomputable def powMat {R : Type*} [CommRing R] (n : ℕ) (ψ : R[X]) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => ((X ^ ((j : ℕ) + 1)) %ₘ ψ).coeff i

theorem _root_.GlobalTheory.TraceAeval.powMat_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (n : ℕ) {ψ : R[X]} (h : ψ.Monic) :
    (_root_.GlobalTheory.TraceAeval.powMat n ψ).map f = _root_.GlobalTheory.TraceAeval.powMat n (ψ.map f) := by
  ext i j
  simp only [_root_.GlobalTheory.TraceAeval.powMat, Matrix.map_apply, Matrix.of_apply]
  rw [← Polynomial.coeff_map, Polynomial.map_modByMonic f h, Polynomial.map_pow,
    Polynomial.map_X]

theorem charpoly_powMat {ψ : ℂ[X]} (h : ψ.Monic) : (powMat ψ.natDegree ψ).charpoly = ψ := by
  have h1 := charpoly_leftMulMatrix (AdjoinRoot.powerBasis' h)
  have h2 : minpoly ℂ (AdjoinRoot.powerBasis' h).gen = ψ := by
    rw [AdjoinRoot.powerBasis'_gen, AdjoinRoot.minpoly_root h.ne_zero, h.leadingCoeff]
    simp
  rw [h2] at h1
  refine Eq.trans ?_ h1
  congr 1
  ext i j
  refine Eq.trans ?_ (Algebra.leftMulMatrix_eq_repr_mul _ _ i j).symm
  have h3 := (AdjoinRoot.powerBasis' h).basis_eq_pow j
  refine Eq.trans ?_ (congrArg (fun t => (AdjoinRoot.powerBasis' h).basis.repr
    ((AdjoinRoot.powerBasis' h).gen * t) i) h3).symm
  simp only [← pow_succ']
  change _ = (AdjoinRoot.powerBasisAux' h).repr ((AdjoinRoot.root ψ) ^ ((j : ℕ) + 1)) i
  rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun, ← AdjoinRoot.mk_X, ← map_pow,
    AdjoinRoot.modByMonicHom_mk]
  rfl

end GlobalTheory.TraceAeval
end
