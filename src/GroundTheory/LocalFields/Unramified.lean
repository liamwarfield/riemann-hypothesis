module

public import GroundTheory.LocalFields.UnramifiedHensel
public import GroundTheory.LocalFields.UnramifiedGalois
public import GroundTheory.LocalFields.CompleteTrivialLocal
public import GroundTheory.LocalFields.PadicLogHom

@[expose] public section

section -- merged from GroundTheory.LocalFields.Unramified
noncomputable section

open ValuativeRel IsLocalRing Polynomial
open scoped _root_.IntermediateField

namespace GroundTheory.LocalField

section Generator

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem isUnit_aeval_derivative_of_separable (P : 𝒪[K][X])
    (hP : (P.map (residue 𝒪[K])).Separable) (x : 𝒪[L]) (hx : aeval x P = 0) :
    IsUnit (aeval x (derivative P)) := by
  rw [← residue_ne_zero_iff_isUnit, residue_aeval K L (fun _ ↦ rfl), ← derivative_map]
  refine hP.aeval_derivative_ne_zero ?_
  rw [← residue_aeval K L (fun _ ↦ rfl), hx, map_zero]

theorem IsUnramified.exists_generator [IsUnramified K L] :
    ∃ (β : 𝒪[L]) (P : 𝒪[K][X]), P.Monic ∧ aeval β P = 0 ∧ (P.map (residue 𝒪[K])).Separable ∧
      IsUnit (aeval β (derivative P)) ∧ K⟮(β : L)⟯ = ⊤ := by
  obtain ⟨β, P, hPm, hβ, hsep, -, hdeg, -⟩ := exists_unramified_adjoin K L
  refine ⟨β, P, hPm, hβ, hsep, isUnit_aeval_derivative_of_separable K L P hsep β hβ, ?_⟩
  refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
  rw [hdeg, IntermediateField.finrank_top', IsUnramified.residueDegree_eq_finrank K L]

end Generator

section Etale

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem map_maximalIdeal_eq_iff :
    (maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] 𝒪[L]) = maximalIdeal 𝒪[L] ↔ IsUnramified K L := by
  rw [map_maximalIdeal K L, isUnramified_iff]
  change maximalIdeal 𝒪[L] ^ ramificationIndex K L = maximalIdeal 𝒪[L] ↔
    ramificationIndex K L = 1
  constructor
  · intro h
    have hpos := ramificationIndex_pos K L
    by_contra hne
    have h2 : 2 ≤ ramificationIndex K L := by omega
    have hL : maximalIdeal 𝒪[L] ≠ ⊥ := maximalIdeal_ne_bot L
    have hlt := Ideal.pow_succ_lt_pow hL 1
    have hle : maximalIdeal 𝒪[L] ^ 1 ≤ maximalIdeal 𝒪[L] ^ (1 + 1) :=
      calc maximalIdeal 𝒪[L] ^ 1 = maximalIdeal 𝒪[L] ^ ramificationIndex K L := by
            rw [pow_one, h]
        _ ≤ maximalIdeal 𝒪[L] ^ (1 + 1) := Ideal.pow_le_pow_right h2
    exact absurd hle (not_le_of_gt hlt)
  · intro h
    rw [h, pow_one]

end Etale

section Maximal

variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

def maximalUnramified : IntermediateField K L :=
  sSup {E : IntermediateField K L | IsUnramified K E}

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [FiniteDimensional K L]


theorem exists_generator_of_isUnramified (E : IntermediateField K L) [IsUnramified K E] :
    ∃ (γ : 𝒪[L]) (P : 𝒪[K][X]), P.Monic ∧ aeval γ P = 0 ∧ IsUnit (aeval γ (derivative P)) ∧
      E = K⟮(γ : L)⟯ := by
  obtain ⟨β, P, hPm, hβ, -, hd, htop⟩ := IsUnramified.exists_generator K E
  refine ⟨algebraMap 𝒪[E] 𝒪[L] β, P, hPm, ?_, ?_, ?_⟩
  · rw [aeval_algebraMap_apply, hβ, map_zero]
  · rw [aeval_algebraMap_apply]
    exact hd.map _
  · have := congrArg (IntermediateField.map E.val) htop
    rw [IntermediateField.adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val] at this
    exact this.symm

theorem exists_maximalUnramified_eq :
    ∃ (β : 𝒪[L]) (P : 𝒪[K][X]), P.Monic ∧ aeval β P = 0 ∧ IsUnit (aeval β (derivative P)) ∧
      maximalUnramified K L = K⟮(β : L)⟯ ∧ IsUnramified K K⟮(β : L)⟯ ∧
      Module.finrank K K⟮(β : L)⟯ = ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) ∧ ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K⟮(β : L)⟯])) = 1 := by
  obtain ⟨β, P, hPm, hβ, hsep, hunr, hdeg, h1⟩ := exists_unramified_adjoin K L
  refine ⟨β, P, hPm, hβ, isUnit_aeval_derivative_of_separable K L P hsep β hβ, ?_, hunr, hdeg, h1⟩
  refine le_antisymm (sSup_le fun E hE ↦ ?_) (le_sSup hunr)
  have : IsUnramified K E := hE
  obtain ⟨γ, Q, hQ, hγ, hd, hE'⟩ := exists_generator_of_isUnramified K L E
  rw [hE']
  exact IntermediateField.adjoin_simple_le_iff.2 (mem_of_residueDegree_eq_one K L _ h1 Q hQ γ hγ hd)

theorem finrank_maximalUnramified :
    Module.finrank K (maximalUnramified K L) = ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) := by
  obtain ⟨β, P, -, -, -, heq, -, hdeg, -⟩ := exists_maximalUnramified_eq K L
  rw [heq]
  exact hdeg

end Maximal

section BaseChange

variable (K K' L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field K'] [ValuativeRel K'] [TopologicalSpace K']
  [IsNonarchimedeanLocalField K'] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K K'] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
  [ValuativeExtension K K'] [ValuativeExtension K' L] [ValuativeExtension K L]
  [FiniteDimensional K L]

end BaseChange

section Galois

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

def inertiaSubgroup : Subgroup (L ≃ₐ[K] L) := (residueAlgEquiv K L).ker

theorem inertiaSubgroup_apply_eq (σ : L ≃ₐ[K] L) (hσ : σ ∈ inertiaSubgroup K L) (P : 𝒪[K][X])
    (γ : 𝒪[L]) (hγ : aeval γ P = 0) (hd : IsUnit (aeval γ (derivative P))) : σ γ = γ := by
  set γσ := integerAlgEquiv K L σ γ
  have h0 : aeval γσ P = 0 := by
    have := aeval_algHom_apply (integerAlgEquiv K L σ : 𝒪[L] →ₐ[𝒪[K]] 𝒪[L]) γ P
    rw [hγ, map_zero] at this
    exact this
  have hres : residue 𝒪[L] γσ = residue 𝒪[L] γ := by
    have h1 : residueAlgEquiv K L σ = 1 := hσ
    rw [← residueAlgEquiv_residue, h1]
    rfl
  have heq : γ = γσ := by
    refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := P.map (algebraMap 𝒪[K] 𝒪[L]))
      (by rw [eval_map_algebraMap]; exact hγ) (by rw [eval_map_algebraMap]; exact h0) ?_ ?_
    · rw [← mem_nonunits_iff, ← mem_maximalIdeal, ← residue_eq_zero_iff, map_sub, hres, sub_self]
    · rw [derivative_map, eval_map_algebraMap]
      exact hd
  rw [← coe_integerAlgEquiv_apply]
  exact congrArg Subtype.val heq.symm

theorem maximalUnramified_le_fixedField :
    maximalUnramified K L ≤ IntermediateField.fixedField (inertiaSubgroup K L) := by
  obtain ⟨β, P, -, hβ, hd, heq, -, -, -⟩ := exists_maximalUnramified_eq K L
  rw [heq, IntermediateField.adjoin_simple_le_iff]
  exact fun σ ↦ inertiaSubgroup_apply_eq K L σ σ.2 P β hβ hd

variable [IsGalois K L]

theorem inertiaSubgroup_counting :
    Nat.card (inertiaSubgroup K L) = (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) ∧
      Nat.card (residueAlgEquiv K L).range = ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) ∧
      Module.finrank K (IntermediateField.fixedField (inertiaSubgroup K L)) = ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) := by
  set I := inertiaSubgroup K L
  set F := IntermediateField.fixedField I
  have hn := ramificationIndex_mul_residueDegree K L
  have hf := residueDegree_pos K L
  have he := ramificationIndex_pos K L
  have hFL : Module.finrank F L = Nat.card I := IntermediateField.finrank_fixedField_eq_card I
  have hG : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  have hIdx : Nat.card I * I.index = Nat.card (L ≃ₐ[K] L) := Subgroup.card_mul_index I
  have hind : I.index = Nat.card (residueAlgEquiv K L).range := Subgroup.index_ker _
  have hrange : Nat.card (residueAlgEquiv K L).range ≤ ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) := by
    calc Nat.card (residueAlgEquiv K L).range ≤ Nat.card (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) :=
          Subgroup.card_le_card_group _
      _ = Module.finrank 𝓀[K] 𝓀[L] := IsGalois.card_aut_eq_finrank _ _
      _ = ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) := (residueDegree_eq_finrank K L).symm
  have hFK : Module.finrank K F * Module.finrank F L = Module.finrank K L :=
    Module.finrank_mul_finrank K F L
  have hTF : ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) ≤ Module.finrank K F := by
    rw [← finrank_maximalUnramified K L]
    exact IntermediateField.finrank_le_of_le_right (maximalUnramified_le_fixedField K L)
  set a := Nat.card I
  set r := Nat.card (residueAlgEquiv K L).range
  set e := (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K)))
  set f := ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K]))
  set d := Module.finrank K F
  rw [hind, hG, ← hn] at hIdx
  rw [hFL, ← hn] at hFK
  have h1 : a ≤ e := by
    refine Nat.le_of_mul_le_mul_left ?_ hf
    calc f * a ≤ d * a := Nat.mul_le_mul_right _ hTF
      _ = e * f := hFK
      _ = f * e := mul_comm _ _
  have h2 : e ≤ a := by
    refine Nat.le_of_mul_le_mul_right ?_ hf
    calc e * f = a * r := hIdx.symm
      _ ≤ a * f := Nat.mul_le_mul_left _ hrange
  have hae : a = e := le_antisymm h1 h2
  refine ⟨hae, ?_, ?_⟩
  · rw [hae] at hIdx
    exact (Nat.eq_of_mul_eq_mul_left he hIdx)
  · rw [hae, mul_comm e f] at hFK
    exact Nat.eq_of_mul_eq_mul_right he hFK

theorem card_inertiaSubgroup : Nat.card (inertiaSubgroup K L) = (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) :=
  (inertiaSubgroup_counting K L).1

end Galois

end GroundTheory.LocalField
end
end

section -- merged from GroundTheory.LocalFields.UnramifiedExistence
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel _root_.IntermediateField

section Card

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem card_residueField_of_unramified (h : (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1) :
    Nat.card 𝓀[L] = Nat.card 𝓀[K] ^ Module.finrank K L := by
  have := Fintype.ofFinite 𝓀[K]
  have := Fintype.ofFinite 𝓀[L]
  rw [← residueDegree_eq_finrank_of_unramified K L h, residueDegree_eq_finrank,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := 𝓀[K]) (V := 𝓀[L])]

end Card

section SeparableClosure

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ksep : Type*} [Field Ksep] [Algebra K Ksep]


omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem adjoin_gen_eq_top (α : Ksep) : K⟮AdjoinSimple.gen K α⟯ = ⊤ := by
  apply map_injective K⟮α⟯.val
  rw [adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map, fieldRange_val]
  exact congrArg (fun x ↦ K⟮x⟯) (AdjoinSimple.coe_gen K α)

def IsUnramifiedSubextension (E : IntermediateField K Ksep) : Prop :=
  FiniteDimensional K E ∧
    ∀ (_ : ValuativeRel E) (_ : TopologicalSpace E) (_ : IsNonarchimedeanLocalField E)
      (_ : ValuativeExtension K E), (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation E))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1

theorem isUnramifiedSubextension_iff_exists (E : IntermediateField K Ksep) :
    IsUnramifiedSubextension E ↔ FiniteDimensional K E ∧
      ∃ (_ : ValuativeRel E) (_ : TopologicalSpace E) (_ : IsNonarchimedeanLocalField E)
        (_ : ValuativeExtension K E), (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation E))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1 := by
  constructor
  · rintro ⟨hfin, h⟩
    exact ⟨hfin, (finiteExtensionStructure K E).rel, (finiteExtensionStructure K E).top,
      finiteExtensionStructure_isNonarchimedeanLocalField K E,
      finiteExtensionStructure_valuativeExtension K E,
      h (finiteExtensionStructure K E).rel (finiteExtensionStructure K E).top
        (finiteExtensionStructure_isNonarchimedeanLocalField K E)
        (finiteExtensionStructure_valuativeExtension K E)⟩
  · rintro ⟨hfin, v₁, t₁, h₁, e₁, h⟩
    refine ⟨hfin, fun v₂ t₂ h₂ e₂ ↦ ?_⟩
    obtain rfl := valuativeRel_unique K h₁ h₂ e₁ e₂
    exact h


omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem IsUnramifiedSubextension.ramificationIndex_eq_one {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [ValuativeExtension K E] : (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation E))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1 :=
  hE.2 inferInstance inferInstance inferInstance inferInstance

theorem IsUnramifiedSubextension.isGalois {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) : IsGalois K E := by
  have := hE.1
  let := (finiteExtensionStructure K E).rel
  let := (finiteExtensionStructure K E).top
  have := finiteExtensionStructure_isNonarchimedeanLocalField K E
  have := finiteExtensionStructure_valuativeExtension K E
  exact isGalois_of_unramified K E hE.ramificationIndex_eq_one

theorem IsUnramifiedSubextension.isCyclic {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) : IsCyclic (E ≃ₐ[K] E) := by
  have := hE.1
  let := (finiteExtensionStructure K E).rel
  let := (finiteExtensionStructure K E).top
  have := finiteExtensionStructure_isNonarchimedeanLocalField K E
  have := finiteExtensionStructure_valuativeExtension K E
  exact isCyclic_of_unramified K E hE.ramificationIndex_eq_one

theorem IsUnramifiedSubextension.card_algEquiv {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) : Nat.card (E ≃ₐ[K] E) = Module.finrank K E := by
  have := hE.1
  have := hE.isGalois
  exact IsGalois.card_aut_eq_finrank K E

theorem exists_isPrimitiveRoot_card_pow_sub_one [IsSepClosed Ksep] {n : ℕ} (hn : n ≠ 0) :
    ∃ ζ : Ksep, IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1) := by
  have hK := natCast_ne_zero_of_residueField (natCast_card_pow_sub_one_ne_zero (K := K) hn)
  have : NeZero ((Nat.card 𝓀[K] ^ n - 1 : ℕ) : Ksep) := ⟨by
    rw [← map_natCast (algebraMap K Ksep)]
    exact (map_ne_zero_iff _ (algebraMap K Ksep).injective).mpr hK⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ksep _

theorem isUnramifiedSubextension_adjoin {n : ℕ} (hn : n ≠ 0) {ζ : Ksep}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) :
    IsUnramifiedSubextension K⟮ζ⟯ ∧ Module.finrank K K⟮ζ⟯ = n := by
  have hm := natCast_card_pow_sub_one_ne_zero (K := K) hn
  have hpos : 0 < Nat.card 𝓀[K] ^ n - 1 := by
    have := Nat.one_lt_pow hn (one_lt_card_residueField K)
    omega
  have hint : IsIntegral K ζ := (hζ.isIntegral hpos).tower_top
  have hfin : FiniteDimensional K K⟮ζ⟯ := adjoin.finiteDimensional hint
  have hζ' : IsPrimitiveRoot (AdjoinSimple.gen K ζ) (Nat.card 𝓀[K] ^ n - 1) :=
    hζ.of_map_of_injective (f := K⟮ζ⟯.val) Subtype.val_injective
  have htop := adjoin_gen_eq_top (K := K) ζ
  refine ⟨⟨hfin, fun _ _ _ _ ↦ ramificationIndex_eq_one_of_adjoin_eq_top hζ' hm htop⟩, ?_⟩
  let := (finiteExtensionStructure K K⟮ζ⟯).rel
  let := (finiteExtensionStructure K K⟮ζ⟯).top
  have := finiteExtensionStructure_isNonarchimedeanLocalField K K⟮ζ⟯
  have := finiteExtensionStructure_valuativeExtension K K⟮ζ⟯
  exact finrank_eq_of_adjoin_eq_top hn hζ' htop

theorem IsUnramifiedSubextension.eq_adjoin {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) {n : ℕ} (hEn : Module.finrank K E = n) (hn : n ≠ 0) {ζ : Ksep}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) : E = K⟮ζ⟯ := by
  have := hE.1
  let := (finiteExtensionStructure K E).rel
  let := (finiteExtensionStructure K E).top
  have := finiteExtensionStructure_isNonarchimedeanLocalField K E
  have := finiteExtensionStructure_valuativeExtension K E
  have h := hE.ramificationIndex_eq_one
  obtain ⟨ξ, hξ, -⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified K E h
  rw [card_residueField_of_unramified K E h, hEn] at hξ
  have hξ' : IsPrimitiveRoot (ξ : Ksep) (Nat.card 𝓀[K] ^ n - 1) :=
    hξ.map_of_injective (f := E.val) Subtype.val_injective
  have : NeZero (Nat.card 𝓀[K] ^ n - 1) := ⟨by
    have := Nat.one_lt_pow hn (one_lt_card_residueField K)
    omega⟩
  obtain ⟨i, -, hi⟩ := hξ'.eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hζE : ζ ∈ E := hi ▸ pow_mem ξ.2 i
  have hle : K⟮ζ⟯ ≤ E := adjoin_simple_le_iff.mpr hζE
  refine (eq_of_le_of_finrank_eq hle ?_).symm
  rw [(isUnramifiedSubextension_adjoin hn hζ).2, hEn]

theorem existsUnique_isUnramifiedSubextension [IsSepClosed Ksep] {n : ℕ} (hn : n ≠ 0) :
    ∃! E : IntermediateField K Ksep, IsUnramifiedSubextension E ∧ Module.finrank K E = n := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_card_pow_sub_one (K := K) (Ksep := Ksep) hn
  exact ⟨K⟮ζ⟯, isUnramifiedSubextension_adjoin hn hζ,
    fun E ⟨hE, hEn⟩ ↦ hE.eq_adjoin hEn hn hζ⟩

theorem isUnramifiedSubextension_adjoin_spec {n : ℕ} (hn : n ≠ 0) {ζ : Ksep}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) :
    IsUnramifiedSubextension K⟮ζ⟯ ∧ Module.finrank K K⟮ζ⟯ = n ∧ IsGalois K K⟮ζ⟯ ∧
      IsCyclic (K⟮ζ⟯ ≃ₐ[K] K⟮ζ⟯) ∧ Nat.card (K⟮ζ⟯ ≃ₐ[K] K⟮ζ⟯) = n ∧
      ∀ E : IntermediateField K Ksep, IsUnramifiedSubextension E → Module.finrank K E = n →
        E = K⟮ζ⟯ := by
  obtain ⟨hE, hEn⟩ := isUnramifiedSubextension_adjoin hn hζ
  exact ⟨hE, hEn, hE.isGalois, hE.isCyclic, hE.card_algEquiv.trans hEn,
    fun E hE' hE'n ↦ hE'.eq_adjoin hE'n hn hζ⟩

variable {E : IntermediateField K Ksep} (hE : IsUnramifiedSubextension E)
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [ValuativeExtension K E]
include hE

end SeparableClosure

end GroundTheory.LocalField
end
end

section -- merged from GroundTheory.LocalFields.HerbrandLocal
namespace GroundTheory.LocalField

open ValuativeRel GroundTheory.GroupCoh GroundTheory.Global

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]


omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra K L]
  [ValuativeExtension K L] [FiniteDimensional K L] in
theorem finiteIndex_of_isOpen_integerUnits {V : Subgroup 𝒪[L]ˣ} (h : IsOpen (V : Set 𝒪[L]ˣ)) :
    V.FiniteIndex := by
  have : Finite (𝒪[L]ˣ ⧸ V) := Subgroup.quotient_finite_of_isOpen V h
  exact Subgroup.finiteIndex_of_finite_quotient

variable [IsGalois K L] {σ : L ≃ₐ[K] L}

theorem cycHerbrand_integerUnits_eq_one (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ = 1 := by
  obtain ⟨-, -, -, -, -, -, -, V, hV, -, hopen, hT⟩ :=
    exists_openSubgroup_units_tateTrivial (K := K) (L := L)
  let := stableUnitsAction V hV
  have := finiteIndex_of_isOpen_integerUnits hopen
  have := hT.1
  have := hT.2
  exact cycHerbrand_integerUnits_eq_one_of_subgroup hσ V
    fun g v => Units.ext (Subtype.ext (unitVal_smul V hV g v))

theorem cycHerbrand_units_eq_finrank (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ =
        Module.finrank K L := by
  obtain ⟨hA, h1⟩ := cycHerbrand_integerUnits_eq_one hσ
  obtain ⟨hB, h2⟩ := cycHerbrand_units_eq_mul hσ hA
  refine ⟨hB, ?_⟩
  rw [h2, h1, one_mul, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]

variable [IsCyclic (L ≃ₐ[K] L)]


omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [IsGalois K L] in
theorem natCard_tateNegOne_units : Nat.card (TateNegOne (L ≃ₐ[K] L) Lˣ) = 1 := by
  have := subsingleton_tateNegOne_units (K := K) (L := L)
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

theorem natCard_tateZero_units :
    Nat.card (TateZero (L ≃ₐ[K] L) Lˣ) = Module.finrank K L := by
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  have h := (cycHerbrand_units_eq_finrank hτ).2
  rw [cycHerbrand_ofMulDistribMulAction hτ, natCard_tateNegOne_units, Nat.cast_one, div_one] at h
  exact_mod_cast h

theorem natCard_units_quotient_range_normUnits :
    Nat.card (Kˣ ⧸ (normUnits K L).range) = Module.finrank K L := by
  rw [← natCard_tateZero_units_eq]
  exact natCard_tateZero_units

end GroundTheory.LocalField
end

section -- merged from GroundTheory.LocalFields.UnramifiedNorms
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem coe_tateNorm_integerUnits [IsGalois K L] (u : 𝒪[L]ˣ) :
    (((tateNorm (L ≃ₐ[K] L) 𝒪[L]ˣ u : 𝒪[L]ˣ) : 𝒪[L]) : L) =
      algebraMap K L (Algebra.norm K ((u : 𝒪[L]) : L)) := by
  rw [Algebra.norm_eq_prod_automorphisms, tateNorm_apply, Units.coe_prod]
  push_cast
  rfl

theorem exists_eq_of_forall_smul_eq [IsGalois K L] {x : 𝒪[L]ˣ}
    (hx : ∀ σ : L ≃ₐ[K] L, σ • x = x) :
    ∃ w : 𝒪[K]ˣ, algebraMap K L ((w : 𝒪[K]) : K) = ((x : 𝒪[L]) : L) := by
  have hfix : ((x : 𝒪[L]) : L) ∈ (⊥ : IntermediateField K L) :=
    (IsGalois.mem_bot_iff_fixed _).2 fun σ ↦ by
      have := congrArg (fun u : 𝒪[L]ˣ ↦ ((u : 𝒪[L]) : L)) (hx σ)
      change σ ((x : 𝒪[L]) : L) = ((x : 𝒪[L]) : L) at this
      exact this
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 hfix
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact (Units.ne_zero x) (by exact_mod_cast hc.symm)
  have h1 : c ∈ 𝒪[K] := (algebraMap_mem_integer_iff K L c).1 (hc ▸ (x : 𝒪[L]).2)
  have h2 : c⁻¹ ∈ 𝒪[K] := by
    refine (algebraMap_mem_integer_iff K L c⁻¹).1 ?_
    have e : algebraMap K L c⁻¹ = (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) := by
      rw [map_inv₀, hc, eq_comm, ← mul_eq_one_iff_eq_inv₀ (by exact_mod_cast (Units.ne_zero x))]
      exact_mod_cast congrArg (fun u : 𝒪[L] ↦ (u : L)) x.inv_mul
    rw [e]
    exact (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L])).2
  refine ⟨⟨⟨c, h1⟩, ⟨c⁻¹, h2⟩, ?_, ?_⟩, hc⟩
  · ext
    simp [hc0]
  · ext
    simp [hc0]

theorem subsingleton_tateZero_integerUnits [IsGalois K L] [IsUnramified K L] :
    Subsingleton (TateZero (L ≃ₐ[K] L) 𝒪[L]ˣ) := by
  rw [subsingleton_tateZero_iff]
  intro x hx
  obtain ⟨w, hw⟩ := exists_eq_of_forall_smul_eq (K := K) (L := L) hx
  obtain ⟨v, rfl⟩ := normIntegerUnits_surjective (K := K) (L := L) w
  refine ⟨v, Units.ext (Subtype.ext ?_)⟩
  rw [coe_tateNorm_integerUnits, ← hw, ← coe_norm_integer, coe_normIntegerUnits_eq]

theorem subsingleton_tateNegOne_integerUnits [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    [IsUnramified K L] :
    Subsingleton (TateNegOne (L ≃ₐ[K] L) 𝒪[L]ˣ) := by
  rw [subsingleton_tateNegOne_iff]
  intro x hx
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  have hxL : tateNorm (L ≃ₐ[K] L) Lˣ (unitsIncl L x) = 1 := by
    rw [tateNorm_apply]
    simp_rw [← unitsIncl_smul]
    rw [← map_prod, ← tateNorm_apply, hx, map_one]
  obtain ⟨y, hy⟩ := exists_smul_div_eq_of_tateNorm_eq_one hg hxL
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖL := irreducible_algebraMap_of_isUnramified (L := L) hϖ
  obtain ⟨⟨m, v⟩, rfl⟩ := (unitsOfIntProd_bijective hϖL).2 y
  have hπ : g • uniformizerUnit hϖL = uniformizerUnit hϖL := by
    ext
    change g ((uniformizerUnit hϖL : Lˣ) : L) = _
    rw [coe_uniformizerUnit, coe_algebraMap_integer, AlgEquiv.commutes]
  have hx' : x = g • v / v := by
    apply unitsIncl_injective (K := L)
    rw [← hy, unitsOfIntProd_eq, _root_.map_div, unitsIncl_smul, smul_mul', smul_zpow', hπ,
      mul_div_mul_left_eq_div]
  rw [hx']
  exact Subgroup.subset_closure ⟨g, v, rfl⟩

end GroundTheory.LocalField
end
end

section -- merged from GroundTheory.LocalFields.PadicExp
namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section ExpLog

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

omit [ValuativeRel K] [IsNonarchimedeanLocalField K] [CharZero K] in
theorem expSeries_zero : expSeries (0 : K) = 1 := by
  rw [expSeries, tsum_eq_single 0]
  · simp
  · intro k hk
    simp [zero_pow hk]

theorem expSeries_nsmul {a : ℤ} {x : K} (hx : x ∈ valBall (K := K) a)
    (ha : (absRamificationIndex (K := K) : ℤ) < (p - 1 : ℤ) * a) (m : ℕ) :
    expSeries (m • x) = expSeries x ^ m := by
  induction m with
  | zero => simp [expSeries_zero]
  | succ m ih =>
    rw [succ_nsmul, expSeries_add p (nsmul_mem hx m) hx ha, ih, pow_succ]

theorem expSeries_mul_sub_one_sub_mem {a d : ℤ} {x c : K} (hx : x ∈ valBall (K := K) a)
    (ha : (absRamificationIndex (K := K) : ℤ) < (p - 1 : ℤ) * a) (hc : c ∈ valBall (K := K) d) (hd : 0 ≤ d) :
    expSeries (c * x) - 1 - c * x ∈ valBall (K := K) (2 * d + a + 1) := by
  have hcx : c * x ∈ valBall (K := K) a := by
    simpa using valBall_antitone (by omega : a ≤ d + a) (mul_mem_valBall hc hx)
  have hs := summable_expSeries p hcx ha
  rw [expSeries, hs.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, zero_add, pow_one,
    Nat.factorial_one]
  have : ∀ t : K, 1 + (c * x + t) - 1 - c * x = t := fun t ↦ by ring
  rw [this]
  refine tsum_mem_valBall fun k ↦ ?_
  have h1 : (c * x) ^ (k + 1 + 1) / ((k + 1 + 1).factorial : K) =
      c ^ (k + 1 + 1) * (x ^ (k + 1 + 1) / ((k + 1 + 1).factorial : K)) := by
    rw [mul_pow, mul_div_assoc]
  rw [h1]
  have hxk := expTerm_mem p hx (k + 1 + 1)
  have hck := pow_mem_valBall hc (k + 1 + 1)
  refine valBall_antitone ?_ (mul_mem_valBall hck hxk)
  have h0 := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega : k + 1 + 1 ≠ 0)
  set v := padicValNat p (k + 1 + 1).factorial
  set e := absRamificationIndex (K := K)
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    rw [Nat.cast_sub hp.out.one_le]; simp
  have h0' : (((p - 1) * v : ℕ) : ℤ) < k + 1 + 1 := by exact_mod_cast (by simpa only [v, Nat.padicValNat_def] using h0)
  push_cast [hp1] at h0'
  have he : (0 : ℤ) ≤ e := by positivity
  have h0'' : ((p : ℤ) - 1) * v ≤ k + 1 := by linarith
  have ha' : (e : ℤ) + 1 ≤ ((p : ℤ) - 1) * a := by linarith
  have hk : (0 : ℤ) ≤ k + 1 := by positivity
  have hkd : (0 : ℤ) ≤ k * d := by positivity
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left h0'' he, mul_le_mul_of_nonneg_left ha' hk]

theorem logSeries_expSeries_sub_one {a : ℤ} {x : K} (hx : x ∈ valBall (K := K) a)
    (ha : (absRamificationIndex (K := K) : ℤ) < (p - 1 : ℤ) * a) :
    logSeries (expSeries x - 1) = x := by
  have ha1 := one_le_of_lt_sub_one_mul p ha
  have hy : expSeries x - 1 ∈ valBall (K := K) 1 :=
    valBall_antitone ha1 (expSeries_sub_one_mem p hx ha)
  have h1 := tendsto_logSeries p hy
  simp only [add_sub_cancel] at h1
  refine tendsto_nhds_unique h1 ?_
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_valBall]
  intro N
  rw [eventually_atTop]
  set e := absRamificationIndex (K := K)
  have he := one_le_absRamificationIndex (K := K) p
  refine ⟨N.toNat, fun k hk ↦ ?_⟩
  have hm0 : p ^ k ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have hm : ((p ^ k : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  have heq : (expSeries x ^ (p ^ k) - 1) / ((p ^ k : ℕ) : K) - x =
      (expSeries (((p ^ k : ℕ) : K) * x) - 1 - ((p ^ k : ℕ) : K) * x) / ((p ^ k : ℕ) : K) := by
    rw [← expSeries_nsmul p hx ha, nsmul_eq_mul]
    field_simp
  rw [heq]
  have hmem := expSeries_mul_sub_one_sub_mem p hx ha (natCast_prime_pow_mem_valBall p k)
    (by positivity)
  have hdiv := div_natCast_mem_valBall p hmem hm0
  refine valBall_antitone ?_ hdiv
  rw [Nat.padicValNat_def, Nat.multiplicity_prime_pow]
  have h2 : N ≤ (N.toNat : ℤ) := Int.self_le_toNat N
  have h3 : (N.toNat : ℤ) ≤ k := by exact_mod_cast hk
  have he' : (1 : ℤ) ≤ e := by exact_mod_cast he
  nlinarith

end ExpLog

section Iso

theorem mem_maximalIdeal_pow_iff_valBall {n : ℕ} {y : 𝒪[K]} :
    y ∈ 𝓂[K] ^ n ↔ (y : K) ∈ valBall (K := K) n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hset := hϖ.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (v := valuation K) n
  have : y ∈ 𝓂[K] ^ n ↔ y ∈ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) := Iff.rfl
  rw [this, hset, mem_valBall]
  show valuation K (y : K) ≤ valuation K (ϖ : K) ^ n ↔ _
  rw [← map_pow, ← normalizedValuation_le_iff, map_pow, normalizedValuation_uniformizer hϖ,
    ← WithZero.exp_nsmul]
  simp

theorem mem_integer_of_mem_valBall {n : ℤ} (hn : 0 ≤ n) {x : K} (hx : x ∈ valBall (K := K) n) :
    x ∈ 𝒪[K] := by
  rw [← normalizedValuation_le_one_iff]
  exact hx.trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)


variable (K) in
noncomputable def valBallEquivMaximalIdealPow (n : ℕ) :
    valBall (K := K) n ≃ₜ+ (𝓂[K] ^ n : Ideal 𝒪[K]) where
  toFun x := ⟨⟨x, mem_integer_of_mem_valBall (by positivity) x.2⟩,
    mem_maximalIdeal_pow_iff_valBall.mpr x.2⟩
  invFun y := ⟨((y : 𝒪[K]) : K), mem_maximalIdeal_pow_iff_valBall.mp y.2⟩
  left_inv x := rfl
  right_inv y := rfl
  map_add' x y := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

theorem one_le_of_lt_sub_one_mul_nat {n : ℕ}
    (hn : (absRamificationIndex (K := K) : ℤ) < (p - 1 : ℤ) * n) : 1 ≤ n := by
  have := one_le_of_lt_sub_one_mul p hn
  omega

omit [CharZero K] in
theorem sub_one_mem_valBall_of_mem {n : ℕ} (hn1 : 1 ≤ n) (u : unitFiltrationUnits K n) :
    ((u : Kˣ) : K) - 1 ∈ valBall (K := K) n :=
  (mem_unitFiltrationUnits_iff_valBall hn1).mp u.2

noncomputable def logValBallHom (n : ℕ) (hn : (absRamificationIndex (K := K) : ℤ) < (p - 1 : ℤ) * n) :
    Additive (unitFiltrationUnits K n) →+ valBall (K := K) n where
  toFun u := ⟨logSeries ((((Additive.toMul u : unitFiltrationUnits K n) : Kˣ) : K) - 1),
    logSeries_mem_valBall p
      (sub_one_mem_valBall_of_mem (one_le_of_lt_sub_one_mul_nat p hn) (Additive.toMul u)) hn⟩
  map_zero' := Subtype.ext (by simp [logSeries])
  map_add' u w := by
    have h := (padicLog K).map_add
      (Additive.ofMul ⟨((Additive.toMul u : unitFiltrationUnits K n) : Kˣ),
        unitFiltrationUnits_antitone (one_le_of_lt_sub_one_mul_nat p hn) (Additive.toMul u).2⟩)
      (Additive.ofMul ⟨((Additive.toMul w : unitFiltrationUnits K n) : Kˣ),
        unitFiltrationUnits_antitone (one_le_of_lt_sub_one_mul_nat p hn) (Additive.toMul w).2⟩)
    exact Subtype.ext h

theorem coe_logValBallHom (n : ℕ) (hn : (absRamificationIndex (K := K) : ℤ) < (p - 1 : ℤ) * n)
    (u : Additive (unitFiltrationUnits K n)) :
    (logValBallHom p n hn u : K) =
      logSeries ((((Additive.toMul u : unitFiltrationUnits K n) : Kˣ) : K) - 1) := rfl

theorem logValBallHom_injective (n : ℕ) (hn : (absRamificationIndex (K := K) : ℤ) < (p - 1 : ℤ) * n) :
    Function.Injective (logValBallHom p n hn) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro u hu
  have h := congrArg Subtype.val hu
  rw [coe_logValBallHom] at h
  have hx := eq_zero_of_logSeries_eq_zero p hn
    (sub_one_mem_valBall_of_mem (one_le_of_lt_sub_one_mul_nat p hn) (Additive.toMul u)) h
  apply Additive.toMul.injective
  ext
  simpa [sub_eq_zero] using hx

omit [CharZero K] in
theorem expSeries_ne_zero {n : ℕ} (hn1 : 1 ≤ n) {x : K} (hx : expSeries x - 1 ∈ valBall (K := K) n) :
    expSeries x ≠ 0 := by
  intro h
  rw [h, zero_sub, mem_valBall, Valuation.map_neg, map_one, ← WithZero.exp_zero,
    WithZero.exp_le_exp] at hx
  omega

noncomputable def expUnit (n : ℕ) (hn : (absRamificationIndex (K := K) : ℤ) < (p - 1 : ℤ) * n)
    (x : valBall (K := K) n) : unitFiltrationUnits K n :=
  ⟨Units.mk0 (expSeries (x : K))
    (expSeries_ne_zero (one_le_of_lt_sub_one_mul_nat p hn) (expSeries_sub_one_mem p x.2 hn)),
    (mem_unitFiltrationUnits_iff_valBall (one_le_of_lt_sub_one_mul_nat p hn)).mpr
      (expSeries_sub_one_mem p x.2 hn)⟩

theorem logValBallHom_expUnit (n : ℕ) (hn : (absRamificationIndex (K := K) : ℤ) < (p - 1 : ℤ) * n)
    (x : valBall (K := K) n) : logValBallHom p n hn (Additive.ofMul (expUnit p n hn x)) = x :=
  Subtype.ext (logSeries_expSeries_sub_one p x.2 hn)

theorem continuous_expSeries_valBall (n : ℕ)
    (hn : (absRamificationIndex (K := K) : ℤ) < (p - 1 : ℤ) * n) :
    Continuous fun x : valBall (K := K) n ↦ expSeries (x : K) := by
  rw [continuous_iff_continuousAt]
  intro x0
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_valBall]
  intro N
  set r : ℤ := max N n
  have hr : (absRamificationIndex (K := K) : ℤ) < (p - 1 : ℤ) * r :=
    sub_one_le_of_lt p hn (le_max_right _ _)
  have hopen := (isOpen_valBall r).preimage
    (continuous_subtype_val.sub continuous_const : Continuous fun x : valBall (K := K) n ↦ (x : K) - x0)
  filter_upwards [hopen.mem_nhds (by simp)] with x hx
  have hx' : (x : K) - x0 ∈ valBall (K := K) r := hx
  have hxn : (x : K) - x0 ∈ valBall (K := K) n := valBall_antitone (le_max_right _ _) hx'
  have heq : expSeries (x : K) = expSeries (x0 : K) * expSeries ((x : K) - x0) := by
    rw [← expSeries_add p x0.2 hxn hn, add_sub_cancel]
  have h0 : expSeries (x0 : K) ∈ valBall (K := K) 0 := by
    have h1 := valBall_antitone (by positivity : (0 : ℤ) ≤ n) (expSeries_sub_one_mem p x0.2 hn)
    have h2 : (1 : K) ∈ valBall (K := K) 0 := by simp [mem_valBall]
    simpa using add_mem h1 h2
  rw [heq, show expSeries (x0 : K) * expSeries ((x : K) - x0) - expSeries (x0 : K) =
    expSeries (x0 : K) * (expSeries ((x : K) - x0) - 1) by ring]
  have hNr : N ≤ 0 + r := by rw [zero_add]; exact le_max_left _ _
  refine valBall_antitone hNr (mul_mem_valBall h0 ?_)
  exact expSeries_sub_one_mem p hx' hr

noncomputable def logValBallEquiv (n : ℕ) (hn : (absRamificationIndex (K := K) : ℤ) < (p - 1 : ℤ) * n) :
    Additive (unitFiltrationUnits K n) ≃ₜ+ valBall (K := K) n where
  toFun := logValBallHom p n hn
  invFun x := Additive.ofMul (expUnit p n hn x)
  left_inv u := logValBallHom_injective p n hn (logValBallHom_expUnit p n hn _)
  right_inv x := logValBallHom_expUnit p n hn x
  map_add' := map_add _
  continuous_toFun := by
    have hι : Continuous fun u : Additive (unitFiltrationUnits K n) ↦
        (Additive.ofMul (⟨((Additive.toMul u : unitFiltrationUnits K n) : Kˣ),
          unitFiltrationUnits_antitone (one_le_of_lt_sub_one_mul_nat p hn)
            (Additive.toMul u).2⟩ : unitFiltrationUnits K 1)) :=
      continuous_ofMul.comp ((continuous_subtype_val.comp continuous_toMul).subtype_mk _)
    exact (continuous_padicLog.comp hι).subtype_mk _
  continuous_invFun := by
    refine continuous_ofMul.comp (Continuous.subtype_mk ?_ _)
    rw [Units.isEmbedding_val₀.continuous_iff]
    exact continuous_expSeries_valBall p n hn

theorem expSeries_logSeries {n : ℕ} (hn : (absRamificationIndex (K := K) : ℤ) < (p - 1 : ℤ) * n)
    (u : unitFiltrationUnits K n) :
    expSeries (logSeries (((u : Kˣ) : K) - 1)) = ((u : Kˣ) : K) := by
  have := congrArg (fun v ↦ (((Additive.toMul v : unitFiltrationUnits K n) : Kˣ) : K))
    ((logValBallEquiv p n hn).symm_apply_apply (Additive.ofMul u))
  exact this

end Iso

end GroundTheory.LocalField
end
