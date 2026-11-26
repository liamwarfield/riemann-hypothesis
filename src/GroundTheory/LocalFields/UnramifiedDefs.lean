module

public import GroundTheory.LocalFields.Integers

@[expose] public section

section -- merged from GroundTheory.LocalFields.UnramifiedDefs
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel

class IsUnramified (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L] [ValuativeExtension K L] : Prop where

  ramificationIndex_eq_one : (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1

section Algebraic

variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

theorem isUnramified_iff : IsUnramified K L ↔ (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1 :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩

end Algebraic

section Topological

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem isUnramified_iff_residueDegree_eq_finrank :
    IsUnramified K L ↔ ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) = Module.finrank K L := by
  rw [isUnramified_iff, ← ramificationIndex_mul_residueDegree K L]
  change ramificationIndex K L = 1 ↔ _
  have h := residueDegree_pos K L
  constructor
  · intro h1
    rw [h1, one_mul]
  · intro h1
    have : (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) * ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) = 1 * ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) := by
      rw [one_mul]
      exact h1.symm
    exact Nat.eq_of_mul_eq_mul_right h this

theorem isUnramified_iff_finrank_residueField :
    IsUnramified K L ↔ Module.finrank 𝓀[K] 𝓀[L] = Module.finrank K L := by
  rw [isUnramified_iff_residueDegree_eq_finrank, residueDegree_eq_finrank]

theorem IsUnramified.residueDegree_eq_finrank [IsUnramified K L] :
    ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) = Module.finrank K L :=
  (isUnramified_iff_residueDegree_eq_finrank K L).1 inferInstance

theorem IsUnramified.finrank_residueField [IsUnramified K L] :
    Module.finrank 𝓀[K] 𝓀[L] = Module.finrank K L :=
  (isUnramified_iff_finrank_residueField K L).1 inferInstance

end Topological

section Tower

variable (K L M : Type*) [Field K] [ValuativeRel K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [ValuativeExtension K L] [ValuativeExtension L M] [ValuativeExtension K M]
  [FiniteDimensional L M]

theorem isUnramified_tower_iff :
    IsUnramified K M ↔ IsUnramified K L ∧ IsUnramified L M := by
  simp only [isUnramified_iff, ramificationIndex_tower K L M, mul_eq_one]

end Tower

end GroundTheory.LocalField
end
end

section -- merged from GroundTheory.LocalFields.UnramifiedRootsOfUnity
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Polynomial

section RootsOfUnity

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

theorem exists_pow_eq_one_residue_eq {m : ℕ} (hm : (m : 𝓀[L]) ≠ 0) {a : 𝓀[L]} (ha : a ^ m = 1) :
    ∃ x : 𝒪[L], x ^ m = 1 ∧ IsLocalRing.residue 𝒪[L] x = a := by
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective a
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hmon : (X ^ m - C (1 : 𝒪[L])).Monic := monic_X_pow_sub_C 1 hm0
  have hev : (X ^ m - C (1 : 𝒪[L])).eval a₀ ∈ 𝓂[L] := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    simp [ha]
  have hder : IsUnit (Ideal.Quotient.mk 𝓂[L] ((X ^ m - C (1 : 𝒪[L])).derivative.eval a₀)) := by
    have ha0 : IsLocalRing.residue 𝒪[L] a₀ ≠ 0 := by
      rintro h
      rw [h, zero_pow hm0] at ha
      exact zero_ne_one ha
    change IsUnit (IsLocalRing.residue 𝒪[L] _)
    rw [isUnit_iff_ne_zero]
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_pow,
      eval_X, eval_natCast, map_mul, map_pow, map_natCast]
    exact mul_ne_zero hm (pow_ne_zero _ ha0)
  let := IsTopologicalAddGroup.rightUniformSpace L
  have := isUniformAddGroup_of_addCommGroup (G := L)
  obtain ⟨x, hx, hxa⟩ := HenselianRing.is_henselian _ hmon a₀ hev hder
  refine ⟨x, ?_, ?_⟩
  · simpa [sub_eq_zero] using hx
  · rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hxa

theorem eq_of_pow_eq_one_of_residue_eq {m : ℕ} (hm : (m : 𝓀[L]) ≠ 0) {x y : 𝒪[L]}
    (hx : x ^ m = 1) (hy : y ^ m = 1)
    (h : IsLocalRing.residue 𝒪[L] x = IsLocalRing.residue 𝒪[L] y) : x = y := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hxu : IsUnit x := (isUnit_pow_iff hm0).mp (hx ▸ isUnit_one)
  refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := X ^ m - C 1)
    (by simp [hx]) (by simp [hy]) ?_ ?_
  · rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff,
      map_sub, h, sub_self]
  · simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul,
      eval_pow, eval_X]
    refine IsUnit.mul ?_ (hxu.pow _)
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    simpa using hm


omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
theorem mem_integer_of_pow_eq_one {m : ℕ} (hm : m ≠ 0) {x : L} (hx : x ^ m = 1) : x ∈ 𝒪[L] := by
  rw [Valuation.mem_integer_iff]
  have h : valuation L x ^ m = 1 := by rw [← map_pow, hx, map_one]
  refine le_of_not_gt fun h1 ↦ ?_
  have := one_lt_pow₀ h1 hm
  rw [h] at this
  exact this.false

theorem exists_isPrimitiveRoot_card_residueField_sub_one :
    ∃ ζ : 𝒪[L], IsPrimitiveRoot ζ (Nat.card 𝓀[L] - 1) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := 𝓀[L]ˣ)
  have hpg : IsPrimitiveRoot (g : 𝓀[L]) (Nat.card 𝓀[L] - 1) := by
    rw [← Nat.card_units, ← orderOf_eq_card_of_forall_mem_zpowers hg, ← orderOf_units]
    exact IsPrimitiveRoot.orderOf _
  obtain ⟨x, hx, hxg⟩ :=
    exists_pow_eq_one_residue_eq (natCast_card_residueField_sub_one_ne_zero L) hpg.pow_eq_one
  refine ⟨x, hx, fun l hl ↦ hpg.dvd_of_pow_eq_one l ?_⟩
  rw [← hxg, ← map_pow, hl, map_one]

end RootsOfUnity

section Degree

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem natDegree_minpoly_residue_le (x : 𝒪[L]) :
    (minpoly 𝓀[K] (IsLocalRing.residue 𝒪[L] x)).natDegree ≤ (minpoly K (x : L)).natDegree := by
  have hx : IsIntegral 𝒪[K] (x : L) := (isIntegral_iff K L x).mpr x.2
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hx, (minpoly.monic hx).natDegree_map]
  set g := minpoly 𝒪[K] (x : L)
  have hg0 : aeval x g = 0 := by
    apply Subtype.val_injective
    rw [ZeroMemClass.coe_zero, ← minpoly.aeval 𝒪[K] (x : L)]
    exact (aeval_algebraMap_apply L x g).symm
  have hmon : (g.map (algebraMap 𝒪[K] 𝓀[K])).Monic := (minpoly.monic hx).map _
  refine (natDegree_le_natDegree (minpoly.min 𝓀[K] _ hmon ?_)).trans
    ((minpoly.monic hx).natDegree_map _).le
  rw [aeval_map_algebraMap, ← IsLocalRing.ResidueField.algebraMap_eq, aeval_algebraMap_apply, hg0,
    map_zero]

end Degree

end GroundTheory.LocalField
end
end

section -- merged from GroundTheory.LocalFields.Ramification
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

section Action

variable {K L}

theorem integerAlgEquiv_mem_maximalIdeal_pow_iff (σ : L ≃ₐ[K] L) (n : ℕ) (x : 𝒪[L]) :
    integerAlgEquiv K L σ x ∈ 𝓂[L] ^ n ↔ x ∈ 𝓂[L] ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have hσϖ : Irreducible (integerAlgEquiv K L σ ϖ) :=
    (MulEquiv.irreducible_iff (f := (integerAlgEquiv K L σ : 𝒪[L] ≃* 𝒪[L]))).mpr hϖ
  rw [mem_maximalIdeal_pow_iff hσϖ, mem_maximalIdeal_pow_iff hϖ, ← map_pow,
    map_dvd_iff (integerAlgEquiv K L σ)]

theorem algEquiv_eq_one_of_forall_integer {σ : L ≃ₐ[K] L}
    (h : ∀ x : 𝒪[L], integerAlgEquiv K L σ x = x) : σ = 1 := by
  ext y
  rw [AlgEquiv.one_apply]
  by_cases hy : valuation L y ≤ 1
  · exact congrArg Subtype.val (h ⟨y, hy⟩)
  · have hy0 : y ≠ 0 := by rintro rfl; simp at hy
    have hinv : valuation L y⁻¹ ≤ 1 := by
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp hy))
    have := congrArg Subtype.val (h ⟨y⁻¹, hinv⟩)
    simp only [coe_integerAlgEquiv_apply, map_inv₀] at this
    exact inv_injective this

end Action

def lowerRamificationGroup (i : ℤ) : Subgroup (L ≃ₐ[K] L) where
  carrier := {σ | ∀ x : 𝒪[L], integerAlgEquiv K L σ x - x ∈ 𝓂[L] ^ (i + 1).toNat}
  one_mem' x := by simp
  mul_mem' {σ τ} hσ hτ x := by
    have h : integerAlgEquiv K L (σ * τ) x - x =
        (integerAlgEquiv K L σ (integerAlgEquiv K L τ x) - integerAlgEquiv K L τ x) +
          (integerAlgEquiv K L τ x - x) := by
      rw [map_mul, AlgEquiv.mul_apply]; ring
    rw [h]
    exact add_mem (hσ _) (hτ x)
  inv_mem' {σ} hσ x := by
    have h := hσ (integerAlgEquiv K L σ⁻¹ x)
    rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply] at h
    rw [← neg_sub]
    exact neg_mem h

variable {K L}

theorem mem_lowerRamificationGroup_iff {i : ℤ} {σ : L ≃ₐ[K] L} :
    σ ∈ lowerRamificationGroup K L i ↔
      ∀ x : 𝒪[L], integerAlgEquiv K L σ x - x ∈ 𝓂[L] ^ (i + 1).toNat :=
  Iff.rfl

theorem mem_lowerRamificationGroup_natCast_iff {n : ℕ} {σ : L ≃ₐ[K] L} :
    σ ∈ lowerRamificationGroup K L n ↔
      ∀ x : 𝒪[L], integerAlgEquiv K L σ x - x ∈ 𝓂[L] ^ (n + 1) := by
  rw [mem_lowerRamificationGroup_iff]
  have : ((n : ℤ) + 1).toNat = n + 1 := by omega
  rw [this]

variable (K L)

theorem lowerRamificationGroup_antitone : Antitone (lowerRamificationGroup K L) := by
  intro i j hij σ hσ x
  exact Ideal.pow_le_pow_right (by omega) (hσ x)

theorem lowerRamificationGroup_eq_top {i : ℤ} (hi : i ≤ -1) :
    lowerRamificationGroup K L i = ⊤ := by
  refine eq_top_iff.mpr fun σ _ x ↦ ?_
  have : (i + 1).toNat = 0 := by omega
  rw [this, pow_zero, Ideal.one_eq_top]
  exact Submodule.mem_top

instance lowerRamificationGroup_normal (i : ℤ) : (lowerRamificationGroup K L i).Normal where
  conj_mem σ hσ τ x := by
    set y := integerAlgEquiv K L τ⁻¹ x
    have hx : x = integerAlgEquiv K L τ y := by
      rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply]
    have h : integerAlgEquiv K L (τ * σ * τ⁻¹) x - x =
        integerAlgEquiv K L τ (integerAlgEquiv K L σ y - y) := by
      rw [map_sub, map_mul, map_mul, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← hx]
    rw [h, integerAlgEquiv_mem_maximalIdeal_pow_iff]
    exact hσ y

variable {K L}

theorem mem_maximalIdeal_pow_iff_normalizedValuation (n : ℕ) (y : 𝒪[L]) :
    y ∈ 𝓂[L] ^ n ↔ normalizedValuation L (y : L) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have hv : normalizedValuation L ((ϖ ^ n : 𝒪[L]) : L) = WithZero.exp (-(n : ℤ)) := by
    rw [SubmonoidClass.coe_pow, map_pow, normalizedValuation_uniformizer hϖ, ← WithZero.exp_nsmul]
    simp
  rw [mem_maximalIdeal_pow_iff hϖ, (Valuation.integer.integers (valuation L)).dvd_iff_le, ← hv,
    normalizedValuation_le_iff]
  rfl

theorem mem_lowerRamificationGroup_iff_valuation {i : ℤ} {σ : L ≃ₐ[K] L} :
    σ ∈ lowerRamificationGroup K L i ↔
      ∀ x ∈ 𝒪[L], normalizedValuation L (σ x - x) ≤ WithZero.exp (-(i + 1)) := by
  rw [mem_lowerRamificationGroup_iff]
  refine ⟨fun h x hx ↦ ?_, fun h x ↦ ?_⟩
  · have := (mem_maximalIdeal_pow_iff_normalizedValuation _ _).mp (h ⟨x, hx⟩)
    have hc : ((integerAlgEquiv K L σ ⟨x, hx⟩ - ⟨x, hx⟩ : 𝒪[L]) : L) = σ x - x := rfl
    rw [hc] at this
    refine this.trans ?_
    rw [WithZero.exp_le_exp]
    omega
  · rcases le_or_gt (i + 1) 0 with hi | hi
    · have : (i + 1).toNat = 0 := by omega
      rw [this, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    · rw [mem_maximalIdeal_pow_iff_normalizedValuation]
      have h' := h x x.2
      have he : ((i + 1).toNat : ℤ) = i + 1 := by omega
      rw [he]
      simpa using h'

variable (K L)

theorem lowerRamificationGroup_zero : lowerRamificationGroup K L 0 = (residueAlgEquiv K L).ker := by
  ext σ
  rw [MonoidHom.mem_ker, AlgEquiv.ext_iff]
  have : ((0 : ℤ) + 1).toNat = 1 := rfl
  rw [mem_lowerRamificationGroup_iff, this, pow_one]
  refine ⟨fun h r ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := residue_surjective r
    rw [residueAlgEquiv_residue, AlgEquiv.one_apply, ← sub_eq_zero, ← map_sub,
      residue_eq_zero_iff]
    exact h x
  · have := h (residue 𝒪[L] x)
    rwa [residueAlgEquiv_residue, AlgEquiv.one_apply, ← sub_eq_zero, ← map_sub,
      residue_eq_zero_iff] at this

theorem residue_integerAlgEquiv_of_mem_zero {σ : L ≃ₐ[K] L} (hσ : σ ∈ lowerRamificationGroup K L 0)
    (x : 𝒪[L]) : residue 𝒪[L] (integerAlgEquiv K L σ x) = residue 𝒪[L] x := by
  rw [lowerRamificationGroup_zero, MonoidHom.mem_ker] at hσ
  rw [← residueAlgEquiv_residue, hσ, AlgEquiv.one_apply]

theorem exists_lowerRamificationGroup_eq_bot :
    ∃ n : ℕ, ∀ i : ℤ, n ≤ i → lowerRamificationGroup K L i = ⊥ := by
  have key : ∀ σ : L ≃ₐ[K] L, ∃ m : ℕ, σ ≠ 1 → σ ∉ lowerRamificationGroup K L m := by
    intro σ
    by_cases hσ : σ = 1
    · exact ⟨0, fun h ↦ (h hσ).elim⟩
    obtain ⟨x, hx⟩ : ∃ x : 𝒪[L], integerAlgEquiv K L σ x ≠ x := by
      by_contra! h
      exact hσ (algEquiv_eq_one_of_forall_integer h)
    have hd : integerAlgEquiv K L σ x - x ≠ 0 := sub_ne_zero.mpr hx
    have hinf := Ideal.iInf_pow_eq_bot_of_isLocalRing (𝓂[L]) (Ideal.IsPrime.ne_top')
    obtain ⟨m, hm⟩ : ∃ m : ℕ, integerAlgEquiv K L σ x - x ∉ 𝓂[L] ^ m := by
      by_contra! h
      exact hd (by
        have : integerAlgEquiv K L σ x - x ∈ ⨅ m : ℕ, 𝓂[L] ^ m := Submodule.mem_iInf _ |>.mpr h
        rwa [hinf, Ideal.mem_bot] at this)
    refine ⟨m, fun _ hmem ↦ hm ?_⟩
    exact Ideal.pow_le_pow_right (Nat.le_succ m) (mem_lowerRamificationGroup_natCast_iff.mp hmem x)
  choose f hf using key
  obtain ⟨N, hN⟩ := Finite.exists_le f
  refine ⟨N, fun i hi ↦ eq_bot_iff.mpr fun σ hσ ↦ ?_⟩
  by_contra h
  exact hf σ h (lowerRamificationGroup_antitone K L (by have := hN σ; omega) hσ)

end GroundTheory.LocalField
end
end
