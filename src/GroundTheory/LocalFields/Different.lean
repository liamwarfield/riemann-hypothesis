module

public import GroundTheory.LocalFields.Unramified
public import GroundTheory.LocalFields.LocalFourierHaar
public import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz

@[expose] public section

section -- merged from GroundTheory.LocalFields.Different
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Polynomial

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

attribute [local instance high] FaithfulSMul.to_isTorsionFree

section DVR

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem span_singleton_eq_maximalIdeal_pow {a : R} (ha : a ≠ 0) {n : ℕ} (hn : addVal R a = n) :
    Ideal.span {a} = IsLocalRing.maximalIdeal R ^ n := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨m, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hϖ
  have hm : m = n := by
    rw [addVal_mul, addVal_pow, addVal_uniformizer hϖ, addVal_eq_zero_of_unit, zero_add,
      nsmul_eq_mul, mul_one] at hn
    exact_mod_cast hn
  rw [← hm, Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
    hϖ.maximalIdeal_eq]

theorem prime_maximalIdeal : Prime (IsLocalRing.maximalIdeal R) :=
  Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field R) inferInstance

theorem maximalIdeal_pow_dvd_pow_iff {m n : ℕ} :
    IsLocalRing.maximalIdeal R ^ m ∣ IsLocalRing.maximalIdeal R ^ n ↔ m ≤ n :=
  pow_dvd_pow_iff (prime_maximalIdeal (R := R)).ne_zero (prime_maximalIdeal (R := R)).not_isUnit

theorem maximalIdeal_pow_injective :
    Function.Injective (fun n : ℕ ↦ IsLocalRing.maximalIdeal R ^ n) := by
  intro m n h
  exact le_antisymm (maximalIdeal_pow_dvd_pow_iff.mp (dvd_of_eq h))
    (maximalIdeal_pow_dvd_pow_iff.mp (dvd_of_eq h.symm))

end DVR

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]

instance isSeparable_fractionRing_integer [Algebra.IsSeparable K L] :
    Algebra.IsSeparable (FractionRing 𝒪[K]) (FractionRing 𝒪[L]) := by
  have H : RingHom.comp (algebraMap (FractionRing 𝒪[K]) (FractionRing 𝒪[L]))
      ↑(FractionRing.algEquiv 𝒪[K] K).symm.toRingEquiv =
        RingHom.comp ↑(FractionRing.algEquiv 𝒪[L] L).symm.toRingEquiv (algebraMap K L) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors 𝒪[K])
    ext
    simp only [RingHom.coe_comp, RingHom.coe_coe,
      AlgEquiv.coe_ringEquiv, Function.comp_apply, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply 𝒪[K] 𝒪[L] L, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
  exact Algebra.IsSeparable.of_equiv_equiv _ _ H

def differentExponent : ℕ := multiplicity (𝓂[L]) (differentIdeal 𝒪[K] 𝒪[L])

variable [FiniteDimensional K L]

section Separable

variable [Algebra.IsSeparable K L]

theorem differentIdeal_eq_maximalIdeal_pow :
    differentIdeal 𝒪[K] 𝒪[L] = 𝓂[L] ^ differentExponent K L := by
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal 𝒪[L]
    (IsPrincipalIdealRing.principal _) _ (differentIdeal_ne_bot (A := 𝒪[K]) (B := 𝒪[L]))
  rw [differentExponent, hn, multiplicity_pow_self_of_prime prime_maximalIdeal]

theorem differentExponent_eq_iff {d : ℕ} :
    differentExponent K L = d ↔ differentIdeal 𝒪[K] 𝒪[L] = 𝓂[L] ^ d := by
  rw [differentIdeal_eq_maximalIdeal_pow]
  exact ⟨fun h ↦ by rw [h], fun h ↦ maximalIdeal_pow_injective h⟩

end Separable

variable {K L}

theorem adjoin_eq_top_of_integer_adjoin_eq_top {x : 𝒪[L]} (hx : Algebra.adjoin 𝒪[K] {x} = ⊤) :
    Algebra.adjoin K {algebraMap 𝒪[L] L x} = ⊤ := by
  have hle : ∀ z : 𝒪[L], (z : L) ∈ Algebra.adjoin K {algebraMap 𝒪[L] L x} := by
    intro z
    have hz : z ∈ Algebra.adjoin 𝒪[K] {x} := by rw [hx]; trivial
    induction hz using Algebra.adjoin_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff.mp hy]
      exact Algebra.subset_adjoin rfl
    | algebraMap r =>
      rw [coe_algebraMap_integer]
      exact Subalgebra.algebraMap_mem _ _
    | add y z _ _ hy hz =>
      rw [Subring.coe_add]
      exact add_mem hy hz
    | mul y z _ _ hy hz =>
      rw [Subring.coe_mul]
      exact mul_mem hy hz
  have := isLocalization_integer K L
  rw [eq_top_iff]
  intro y _
  obtain ⟨⟨z, s⟩, hzs⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid 𝒪[L]
    (nonZeroDivisors 𝒪[K])) y
  obtain ⟨c, hc, hcs⟩ := s.2
  have hc0 : (c : K) ≠ 0 := by
    have : c ≠ 0 := nonZeroDivisors.ne_zero hc
    exact_mod_cast this
  have hy : y = (c : K)⁻¹ • (z : L) := by
    have h2 : ((s : 𝒪[L]) : L) = algebraMap K L c := by
      rw [← hcs]
      rfl
    simp only at hzs
    rw [Algebra.smul_def, map_inv₀, ← h2, eq_inv_mul_iff_mul_eq₀]
    · rw [mul_comm]; exact hzs
    · rw [h2]; exact (_root_.map_ne_zero _).mpr hc0
  rw [hy]
  exact Subalgebra.smul_mem _ (hle z) _

section Separable

variable [Algebra.IsSeparable K L]

theorem differentIdeal_eq_span_aeval_derivative {x : 𝒪[L]} (hx : Algebra.adjoin 𝒪[K] {x} = ⊤) :
    differentIdeal 𝒪[K] 𝒪[L] = Ideal.span {aeval x (derivative (minpoly 𝒪[K] x))} := by
  rw [← conductor_mul_differentIdeal 𝒪[K] K L x (adjoin_eq_top_of_integer_adjoin_eq_top hx),
    conductor_eq_top_of_adjoin_eq_top hx, Ideal.top_mul]

theorem aeval_derivative_ne_zero {x : 𝒪[L]} (hx : Algebra.adjoin 𝒪[K] {x} = ⊤) :
    aeval x (derivative (minpoly 𝒪[K] x)) ≠ 0 := by
  intro h
  have := differentIdeal_eq_span_aeval_derivative hx
  rw [h, Ideal.span_singleton_eq_bot.mpr rfl] at this
  exact differentIdeal_ne_bot this

theorem differentExponent_eq_addVal {x : 𝒪[L]} (hx : Algebra.adjoin 𝒪[K] {x} = ⊤) :
    (differentExponent K L : ℕ∞) = IsDiscreteValuationRing.addVal 𝒪[L] (aeval x (derivative (minpoly 𝒪[K] x))) := by
  have h0 := aeval_derivative_ne_zero hx
  obtain ⟨k, hk⟩ := exists_addVal_eq_coe h0
  rw [hk, Nat.cast_inj, differentExponent_eq_iff, differentIdeal_eq_span_aeval_derivative hx]
  exact span_singleton_eq_maximalIdeal_pow h0 hk

variable (K L)

end Separable

section Tower

variable (K L M : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [ValuativeExtension K L] [ValuativeExtension L M] [ValuativeExtension K M]
  [FiniteDimensional K L] [FiniteDimensional L M] [Algebra.IsSeparable K M]

theorem differentIdeal_tower :
    differentIdeal 𝒪[K] 𝒪[M] =
      differentIdeal 𝒪[L] 𝒪[M] * (differentIdeal 𝒪[K] 𝒪[L]).map (algebraMap 𝒪[L] 𝒪[M]) := by
  have : FiniteDimensional K M := Module.Finite.trans L M
  exact differentIdeal_eq_differentIdeal_mul_differentIdeal 𝒪[K] 𝒪[L] 𝒪[M]

theorem differentExponent_tower :
    differentExponent K M = (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation M))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) * differentExponent K L +
      differentExponent L M := by
  have : FiniteDimensional K M := Module.Finite.trans L M
  have : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L M
  have : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  rw [differentExponent_eq_iff, differentIdeal_tower K L M, differentIdeal_eq_maximalIdeal_pow L M,
    differentIdeal_eq_maximalIdeal_pow K L, Ideal.map_pow, map_maximalIdeal L M, ← pow_mul,
    ← pow_add]
  congr 1
  ring

end Tower

section Discriminant

theorem ord_eq_of_addVal_eq {a : 𝒪[K]} (ha : a ≠ 0) {n : ℕ}
    (hn : IsDiscreteValuationRing.addVal 𝒪[K] a = n) : ord (a : K) = n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hm : m = n := by
    rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ,
      IsDiscreteValuationRing.addVal_eq_zero_of_unit, zero_add, nsmul_eq_mul, mul_one] at hn
    exact_mod_cast hn
  have hu0 : ((u : 𝒪[K]) : K) ≠ 0 := by
    intro h
    exact u.ne_zero (Subtype.ext h)
  have hϖ0 : (ϖ : K) ≠ 0 := by
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  rw [Subring.coe_mul, Subring.coe_pow, ord_mul hu0 (pow_ne_zero _ hϖ0), ord_unit,
    ord_pow hϖ0, ord_uniformizer hϖ, ← hm]
  simp

variable [Algebra.IsSeparable K L]

variable (K L)

end Discriminant

end GroundTheory.LocalField
end
end

section -- merged from GroundTheory.LocalFields.LowerIndex
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing IsDiscreteValuationRing Polynomial

theorem range_restrictScalarsHom {K L : Type*} [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L) :
    (AlgEquiv.restrictScalarsHom K : (L ≃ₐ[M] L) →* (L ≃ₐ[K] L)).range = M.fixingSubgroup := by
  ext σ
  rw [MonoidHom.mem_range, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · rintro ⟨τ, rfl⟩ m hm
    exact τ.commutes ⟨m, hm⟩
  · intro h
    refine ⟨{ σ with commutes' := fun m ↦ h m m.2 }, ?_⟩
    ext x
    rfl

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

def lowerIndex (σ : L ≃ₐ[K] L) : ℕ∞ :=
  ⨅ x : 𝒪[L], addVal 𝒪[L] (integerAlgEquiv K L σ x - x)

variable {K L}

theorem le_lowerIndex_iff {σ : L ≃ₐ[K] L} {n : ℕ∞} :
    n ≤ lowerIndex K L σ ↔ ∀ x : 𝒪[L], n ≤ addVal 𝒪[L] (integerAlgEquiv K L σ x - x) :=
  le_iInf_iff

theorem lowerIndex_le (σ : L ≃ₐ[K] L) (x : 𝒪[L]) :
    lowerIndex K L σ ≤ addVal 𝒪[L] (integerAlgEquiv K L σ x - x) :=
  iInf_le _ x

theorem mem_lowerRamificationGroup_iff_lowerIndex {i : ℤ} {σ : L ≃ₐ[K] L} :
    σ ∈ lowerRamificationGroup K L i ↔ (((i + 1).toNat : ℕ) : ℕ∞) ≤ lowerIndex K L σ := by
  rw [mem_lowerRamificationGroup_iff, le_lowerIndex_iff]
  simp only [mem_maximalIdeal_pow_iff_le_addVal]

theorem mem_lowerRamificationGroup_natCast_iff_lowerIndex {n : ℕ} {σ : L ≃ₐ[K] L} :
    σ ∈ lowerRamificationGroup K L n ↔ ((n + 1 : ℕ) : ℕ∞) ≤ lowerIndex K L σ := by
  rw [mem_lowerRamificationGroup_natCast_iff, le_lowerIndex_iff]
  simp only [mem_maximalIdeal_pow_iff_le_addVal]

@[simp]
theorem lowerIndex_one : lowerIndex K L 1 = ⊤ := by
  simp [lowerIndex]

theorem lowerIndex_eq_top_iff {σ : L ≃ₐ[K] L} : lowerIndex K L σ = ⊤ ↔ σ = 1 := by
  constructor
  · intro h
    apply algEquiv_eq_one_of_forall_integer
    intro x
    have := lowerIndex_le σ x
    rwa [h, top_le_iff, addVal_eq_top_iff, sub_eq_zero] at this
  · rintro rfl
    exact lowerIndex_one

theorem lowerIndex_ne_top {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) : lowerIndex K L σ ≠ ⊤ :=
  fun h ↦ hσ (lowerIndex_eq_top_iff.mp h)

theorem one_le_lowerIndex_iff {σ : L ≃ₐ[K] L} :
    1 ≤ lowerIndex K L σ ↔ σ ∈ lowerRamificationGroup K L 0 := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, mem_lowerRamificationGroup_natCast_iff_lowerIndex]
  simp

theorem lowerIndex_eq_zero_iff {σ : L ≃ₐ[K] L} :
    lowerIndex K L σ = 0 ↔ σ ∉ lowerRamificationGroup K L 0 := by
  rw [← one_le_lowerIndex_iff, not_le, Order.lt_one_iff]

theorem min_le_lowerIndex_mul (σ τ : L ≃ₐ[K] L) :
    min (lowerIndex K L σ) (lowerIndex K L τ) ≤ lowerIndex K L (σ * τ) := by
  rw [le_lowerIndex_iff]
  intro x
  have h : integerAlgEquiv K L (σ * τ) x - x =
      (integerAlgEquiv K L σ (integerAlgEquiv K L τ x) - integerAlgEquiv K L τ x) +
        (integerAlgEquiv K L τ x - x) := by
    rw [map_mul, AlgEquiv.mul_apply]; ring
  rw [h]
  exact le_trans (min_le_min (lowerIndex_le σ _) (lowerIndex_le τ x)) ((addVal 𝒪[L]).map_add _ _)

theorem lowerIndex_le_lowerIndex_inv (σ : L ≃ₐ[K] L) : lowerIndex K L σ ≤ lowerIndex K L σ⁻¹ := by
  rw [le_lowerIndex_iff]
  intro x
  have h : integerAlgEquiv K L σ⁻¹ x - x =
      -(integerAlgEquiv K L σ (integerAlgEquiv K L σ⁻¹ x) - integerAlgEquiv K L σ⁻¹ x) := by
    rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply]
    ring
  rw [h, AddValuation.map_neg]
  exact lowerIndex_le σ _

@[simp]
theorem lowerIndex_inv (σ : L ≃ₐ[K] L) : lowerIndex K L σ⁻¹ = lowerIndex K L σ :=
  le_antisymm (by simpa using lowerIndex_le_lowerIndex_inv σ⁻¹) (lowerIndex_le_lowerIndex_inv σ)

theorem lowerIndex_mul_of_lt {σ τ : L ≃ₐ[K] L} (h : lowerIndex K L τ < lowerIndex K L σ) :
    lowerIndex K L (σ * τ) = lowerIndex K L τ := by
  refine le_antisymm ?_ ((min_eq_right h.le).symm.le.trans (min_le_lowerIndex_mul σ τ))
  have h1 := min_le_lowerIndex_mul σ⁻¹ (σ * τ)
  rw [inv_mul_cancel_left, lowerIndex_inv] at h1
  by_contra h2
  rw [not_le] at h2
  exact (lt_min h h2).not_ge h1

theorem lowerIndex_eq_addVal_of_adjoin_eq_top {x : 𝒪[L]} (hx : Algebra.adjoin 𝒪[K] {x} = ⊤)
    (σ : L ≃ₐ[K] L) : lowerIndex K L σ = addVal 𝒪[L] (integerAlgEquiv K L σ x - x) := by
  refine le_antisymm (lowerIndex_le σ x) ?_
  rw [le_lowerIndex_iff]
  intro z
  have hz : z ∈ Algebra.adjoin 𝒪[K] {x} := hx ▸ trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hz
  obtain ⟨p, rfl⟩ := hz
  rw [addVal_le_iff_dvd]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← aeval_algHom_apply, ← eval_map_algebraMap, ← eval_map_algebraMap]
  exact sub_dvd_eval_sub _ _ _

section Subgroup

variable (M : IntermediateField K L)

@[simp]
theorem lowerIndex_restrictScalars (σ : L ≃ₐ[M] L) :
    lowerIndex K L (σ.restrictScalars K) = lowerIndex M L σ :=
  rfl

theorem lowerRamificationGroup_comap_restrictScalars (i : ℤ) :
    (lowerRamificationGroup K L i).comap (AlgEquiv.restrictScalarsHom K) =
      lowerRamificationGroup M L i := by
  ext σ
  rw [Subgroup.mem_comap, AlgEquiv.restrictScalarsHom_apply, mem_lowerRamificationGroup_iff_lowerIndex,
    mem_lowerRamificationGroup_iff_lowerIndex, lowerIndex_restrictScalars]

theorem lowerRamificationGroup_map_restrictScalars (i : ℤ) :
    (lowerRamificationGroup M L i).map (AlgEquiv.restrictScalarsHom K) =
      lowerRamificationGroup K L i ⊓ M.fixingSubgroup := by
  rw [← lowerRamificationGroup_comap_restrictScalars M, Subgroup.map_comap_eq,
    range_restrictScalarsHom, inf_comm]

theorem lowerRamificationGroup_map_fixedField [IsGalois K L] (H : Subgroup (L ≃ₐ[K] L)) (i : ℤ) :
    (lowerRamificationGroup (IntermediateField.fixedField H) L i).map
        (AlgEquiv.restrictScalarsHom K) = lowerRamificationGroup K L i ⊓ H := by
  rw [lowerRamificationGroup_map_restrictScalars, IntermediateField.fixingSubgroup_fixedField]

end Subgroup


variable (K L) in
theorem card_lowerRamificationGroup_zero [IsGalois K L] :
    Nat.card (lowerRamificationGroup K L 0) = (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) := by
  rw [lowerRamificationGroup_zero]
  exact card_inertiaSubgroup K L

end GroundTheory.LocalField
end
end

section -- merged from GroundTheory.LocalFields.LocalFourierChar
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Topology Filter
open scoped WithZero Pointwise

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Basis

theorem hasBasis_nhds_zero_valBall :
    (𝓝 (0 : K)).HasBasis (fun _ : ℤ => True) (fun n => (valBall (K := K) n : Set K)) := by
  have hballs := tendsto_zero_iff_valBall.mp (tendsto_id (x := 𝓝 (0 : K)))
  refine ⟨fun t => ⟨fun ht => ?_, fun ⟨n, _, hn⟩ => Filter.mem_of_superset (hballs n) hn⟩⟩
  by_contra h
  have h' : ∀ n : ℤ, ¬ (valBall (K := K) n : Set K) ⊆ t := fun n hn => h ⟨n, trivial, hn⟩
  have hex : ∀ k : ℕ, ∃ x : K, x ∈ valBall (K := K) k ∧ x ∉ t := fun k => by
    have := h' k
    rw [Set.not_subset] at this
    exact this
  choose x hx hxt using hex
  have hlim : Tendsto x atTop (𝓝 0) := by
    rw [tendsto_zero_iff_valBall]
    intro N
    filter_upwards [eventually_ge_atTop N.toNat] with k hk
    have hval : normalizedValuation K (x k) ≤ WithZero.exp (-(k : ℤ)) := hx k
    exact hval.trans (WithZero.exp_le_exp.mpr (by omega))
  obtain ⟨k, hk⟩ := (hlim.eventually ht).exists
  exact hxt k hk

end Basis

section Characters


omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem eq_one_of_forall_norm_sub_one_lt (χ : AddChar K Circle) (H : AddSubgroup K)
    (h : ∀ x ∈ H, ‖(χ x : ℂ) - 1‖ < 1 / 2) {x : K} (hx : x ∈ H) : χ x = 1 := by
  have := GroundTheory.Global.eq_one_of_sq_mem (s := (fun y => (χ y : ℂ)) '' (H : Set K)) ?_ ?_
    ⟨x, hx, rfl⟩
  · exact Circle.coe_eq_one.mp this
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨y + y, H.add_mem hy hy, ?_⟩
    simp [AddChar.map_add_eq_mul, sq]
  · rintro _ ⟨y, hy, rfl⟩
    exact h y hy

theorem setOf_norm_sub_one_lt_mem_nhds :
    {z : Circle | ‖(z : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (1 : Circle) := by
  have hc : Continuous fun z : Circle ↦ ‖(z : ℂ) - 1‖ :=
    (continuous_subtype_val.sub continuous_const).norm
  exact (isOpen_lt hc continuous_const).mem_nhds (by simp)

variable (ψ : AddChar K Circle)

def IsTrivialOn (n : ℤ) : Prop := ∀ x ∈ valBall (K := K) n, ψ x = 1

variable {ψ} in
theorem IsTrivialOn.mono {m n : ℤ} (h : IsTrivialOn ψ m) (hmn : m ≤ n) : IsTrivialOn ψ n :=
  fun x hx => by
    have hval : normalizedValuation K x ≤ WithZero.exp (-n) := hx
    exact h x (hval.trans (WithZero.exp_le_exp.mpr (by omega)))

theorem exists_isTrivialOn (hψ : Continuous ψ) : ∃ n, IsTrivialOn ψ n := by
  have : ψ ⁻¹' {z : Circle | ‖(z : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (0 : K) := by
    apply hψ.continuousAt.preimage_mem_nhds
    rw [AddChar.map_zero_eq_one]
    exact setOf_norm_sub_one_lt_mem_nhds
  obtain ⟨n, -, hn⟩ := hasBasis_nhds_zero_valBall.mem_iff.mp this
  exact ⟨n, fun x hx => eq_one_of_forall_norm_sub_one_lt ψ (valBall (K := K) n) (fun y hy => hn hy) hx⟩

theorem exists_le_of_isTrivialOn (hψ1 : ψ ≠ 1) : ∃ N, ∀ n, IsTrivialOn ψ n → N ≤ n := by
  obtain ⟨x, hx⟩ : ∃ x, ψ x ≠ 1 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hψ1 (DFunLike.ext _ _ fun a => (h a).trans (one_apply a).symm)
  refine ⟨ord x + 1, fun n hn => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  exact hx (hn.mono (by omega : n ≤ ord x) x mem_valBall_ord)

def addCharConductor : ℤ := sInf {n : ℤ | IsTrivialOn ψ n}

variable {ψ} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ hψ1

omit hψ in
theorem bddBelow_isTrivialOn : BddBelow {n : ℤ | IsTrivialOn ψ n} := by
  obtain ⟨N, hN⟩ := exists_le_of_isTrivialOn ψ hψ1
  exact ⟨N, fun m hm => hN m hm⟩

theorem isTrivialOn_addCharConductor : IsTrivialOn ψ (addCharConductor ψ) := by
  obtain ⟨n, hn⟩ := exists_isTrivialOn ψ hψ
  exact Int.csInf_mem ⟨n, hn⟩ (bddBelow_isTrivialOn hψ1)

theorem isTrivialOn_iff (n : ℤ) : IsTrivialOn ψ n ↔ addCharConductor ψ ≤ n :=
  ⟨fun h => csInf_le (bddBelow_isTrivialOn hψ1) h,
    fun h => (isTrivialOn_addCharConductor hψ hψ1).mono h⟩

omit hψ hψ1 in
theorem isTrivialOn_mulShift_iff {a : K} (ha : a ≠ 0) (n : ℤ) :
    IsTrivialOn (ψ.mulShift a) n ↔ IsTrivialOn ψ (n + ord a) := by
  constructor
  · intro h y hy
    have hy' : y ∈ a • (valBall (K := K) n : Set K) := by
      rw [smul_valBall ha]
      exact hy
    obtain ⟨x, hx, rfl⟩ := hy'
    have := h x hx
    rwa [AddChar.mulShift_apply] at this
  · intro h x hx
    rw [AddChar.mulShift_apply]
    apply h
    have : a • x ∈ a • (valBall (K := K) n : Set K) := Set.smul_mem_smul_set hx
    rw [smul_valBall ha] at this
    exact this

theorem isTrivialOn_mulShift_iff_mem (a : K) (n : ℤ) :
    IsTrivialOn (ψ.mulShift a) n ↔ a ∈ valBall (K := K) (addCharConductor ψ - n) := by
  by_cases ha : a = 0
  · simp [ha, IsTrivialOn]
  rw [isTrivialOn_mulShift_iff ha, isTrivialOn_iff hψ hψ1, mem_valBall_iff_le_ord ha]
  omega

omit hψ1 in
theorem continuous_mulShift (a : K) : Continuous (ψ.mulShift a) := by
  have : (ψ.mulShift a : K → Circle) = fun x => ψ (a * x) := by
    ext x
    rw [AddChar.mulShift_apply]
  rw [this]
  exact hψ.comp (continuous_const_mul a)

omit hψ [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem mulShift_ne_one {a : K} (ha : a ≠ 0) : ψ.mulShift a ≠ 1 :=
  AddChar.IsPrimitive.of_ne_one hψ1 ha


theorem addCharConductor_mulShift {a : K} (ha : a ≠ 0) :
    addCharConductor (ψ.mulShift a) = addCharConductor ψ - ord a := by
  have hc := continuous_mulShift hψ a
  have h1 := mulShift_ne_one hψ1 ha
  have key : ∀ n, addCharConductor (ψ.mulShift a) ≤ n ↔ addCharConductor ψ - ord a ≤ n := fun n => by
    rw [← isTrivialOn_iff hc h1, isTrivialOn_mulShift_iff ha, isTrivialOn_iff hψ hψ1]
    omega
  exact le_antisymm ((key _).mpr le_rfl) ((key _).mp le_rfl)

end Characters

section Residue

end Residue

section Duality

variable {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ hψ1

end Duality

section SelfDual

variable {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)


end SelfDual

end GroundTheory.LocalField
end
end
