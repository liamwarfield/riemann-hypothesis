module

public import GroundTheory.LocalFields.Interface
public import GroundTheory.LocalFields.UnitsBasic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsRootOfAdicComplete

@[expose] public section

section -- merged from GroundTheory.LocalFields.Uniqueness
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Topology Filter

section Topology

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

theorem t2Space_of_isNonarchimedeanLocalField : T2Space L := by
  let := IsTopologicalAddGroup.rightUniformSpace L
  have := isUniformAddGroup_of_addCommGroup (G := L)
  infer_instance

@[instance_reducible]
def nontriviallyNormedField : NontriviallyNormedField K :=
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  Valued.toNontriviallyNormedField K (ValueGroupWithZero K)

theorem completeSpace_nontriviallyNormedField :
    @CompleteSpace K (nontriviallyNormedField K).toUniformSpace := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  exact (inferInstance : CompleteSpace K)

variable [Algebra K L] [ValuativeExtension K L]

theorem isModuleTopology [FiniteDimensional K L] : IsModuleTopology K L := by
  let := nontriviallyNormedField K
  have := completeSpace_nontriviallyNormedField K
  have := t2Space_of_isNonarchimedeanLocalField L
  exact isModuleTopologyOfFiniteDimensional

end Topology

section Nilpotent

variable {F : Type*} [Field F] [ValuativeRel F]

theorem vle_iff_not_valuation_div_lt_one {x : F} (hx : x ≠ 0) (y : F) :
    x ≤ᵥ y ↔ ¬ valuation F (y / x) < 1 := by
  have hx' : 0 < valuation F x := by
    rw [zero_lt_iff]
    simpa using hx
  rw [(valuation F).vle_iff_le, map_div₀, div_lt_one₀ hx', not_lt]

theorem vle_map_iff_of_valuation_lt_one_iff {F' : Type*} [Field F'] [ValuativeRel F']
    (f : F →+* F') (hf : ∀ z, valuation F' (f z) < 1 ↔ valuation F z < 1) (x y : F) :
    f x ≤ᵥ f y ↔ x ≤ᵥ y := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [map_zero]
    exact ⟨fun _ ↦ ValuativeRel.zero_vle y, fun _ ↦ ValuativeRel.zero_vle (f y)⟩
  · rw [vle_iff_not_valuation_div_lt_one hx, vle_iff_not_valuation_div_lt_one
      ((map_ne_zero f).mpr hx), ← map_div₀, hf]

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem tendsto_pow_atTop_nhds_zero_iff (x : F) :
    Tendsto (fun n : ℕ ↦ x ^ n) atTop (𝓝 0) ↔ valuation F x < 1 := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero F).tendsto_right_iff]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (h 1 trivial).exists
    simp only [Set.mem_ofPred_eq, map_pow, Units.val_one] at hn
    by_contra hx
    exact (one_le_pow₀ (not_lt.mp hx)).not_gt hn
  · intro hx γ _
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hx γ
    filter_upwards [eventually_ge_atTop n] with m hm
    simp only [map_pow]
    exact (pow_le_pow_of_le_one zero_le hx.le hm).trans_lt hn

end Nilpotent

section Maps

variable {K L M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M]

theorem continuous_algHom (f : L →ₐ[K] M) : Continuous f := by
  have := isModuleTopology K L
  exact IsModuleTopology.continuous_of_linearMap (R := K) f.toLinearMap

theorem isClosedEmbedding_algHom (f : L →ₐ[K] M) : IsClosedEmbedding f := by
  let := nontriviallyNormedField K
  have := completeSpace_nontriviallyNormedField K
  have := t2Space_of_isNonarchimedeanLocalField L
  have := t2Space_of_isNonarchimedeanLocalField M
  exact LinearMap.isClosedEmbedding_of_injective (f := f.toLinearMap)
    (LinearMap.ker_eq_bot.mpr f.toRingHom.injective)

theorem valuation_map_lt_one_iff (f : L →ₐ[K] M) (x : L) :
    valuation M (f x) < 1 ↔ valuation L x < 1 := by
  rw [← tendsto_pow_atTop_nhds_zero_iff, ← tendsto_pow_atTop_nhds_zero_iff,
    (isClosedEmbedding_algHom f).isInducing.tendsto_nhds_iff, ← map_zero f]
  simp only [Function.comp_def, map_pow]

theorem vle_map_iff (f : L →ₐ[K] M) (x y : L) : f x ≤ᵥ f y ↔ x ≤ᵥ y :=
  vle_map_iff_of_valuation_lt_one_iff f.toRingHom (valuation_map_lt_one_iff f) x y

theorem vlt_map_iff (f : L →ₐ[K] M) (x y : L) : f x <ᵥ f y ↔ x <ᵥ y := by
  rw [← not_vle, vle_map_iff, not_vle]

theorem valuativeExtension_algHom (f : L →ₐ[K] M) :
    @ValuativeExtension L M _ _ _ _ f.toRingHom.toAlgebra :=
  letI := f.toRingHom.toAlgebra
  ⟨fun {a b} => vle_map_iff f a b⟩

end Maps

section Uniqueness

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]

theorem topologicalSpace_eq_moduleTopology [ValuativeRel L] [t : TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [ValuativeExtension K L] : t = moduleTopology K L :=
  have := isModuleTopology K L
  eq_moduleTopology K L

theorem topologicalSpace_unique {v₁ v₂ : ValuativeRel L} {t₁ t₂ : TopologicalSpace L}
    (h₁ : @IsNonarchimedeanLocalField L _ v₁ t₁) (h₂ : @IsNonarchimedeanLocalField L _ v₂ t₂)
    (e₁ : @ValuativeExtension K L _ _ _ v₁ _) (e₂ : @ValuativeExtension K L _ _ _ v₂ _) :
    t₁ = t₂ :=
  (@topologicalSpace_eq_moduleTopology K _ _ _ _ L _ _ _ v₁ t₁ h₁ e₁).trans
    (@topologicalSpace_eq_moduleTopology K _ _ _ _ L _ _ _ v₂ t₂ h₂ e₂).symm

theorem valuativeRel_unique {v₁ v₂ : ValuativeRel L} {t₁ t₂ : TopologicalSpace L}
    (h₁ : @IsNonarchimedeanLocalField L _ v₁ t₁) (h₂ : @IsNonarchimedeanLocalField L _ v₂ t₂)
    (e₁ : @ValuativeExtension K L _ _ _ v₁ _) (e₂ : @ValuativeExtension K L _ _ _ v₂ _) :
    v₁ = v₂ := by
  have ht := topologicalSpace_unique K h₁ h₂ e₁ e₂
  subst ht
  have hlt (z : L) : @valuation L _ v₂ z < 1 ↔ @valuation L _ v₁ z < 1 := by
    rw [← @tendsto_pow_atTop_nhds_zero_iff L _ v₁ t₁ h₁,
      ← @tendsto_pow_atTop_nhds_zero_iff L _ v₂ t₁ h₂]
  ext x y
  exact (@vle_map_iff_of_valuation_lt_one_iff L _ v₁ L _ v₂ (RingHom.id L) hlt x y).symm

end Uniqueness

section Galois

variable {K L M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M]

theorem valuation_map_le_iff (f : L →ₐ[K] M) (x y : L) :
    valuation M (f x) ≤ valuation M (f y) ↔ valuation L x ≤ valuation L y := by
  rw [← (valuation M).vle_iff_le, ← (valuation L).vle_iff_le, vle_map_iff]

theorem valuation_map_lt_iff (f : L →ₐ[K] M) (x y : L) :
    valuation M (f x) < valuation M (f y) ↔ valuation L x < valuation L y := by
  rw [← (valuation M).vlt_iff_lt, ← (valuation L).vlt_iff_lt, vlt_map_iff]

theorem map_mem_integer_iff (f : L →ₐ[K] M) (x : L) : f x ∈ 𝒪[M] ↔ x ∈ 𝒪[L] := by
  simp only [Valuation.mem_integer_iff]
  rw [← map_one (valuation M), ← map_one f, valuation_map_le_iff, map_one]

def integerAlgHom (f : L →ₐ[K] M) : 𝒪[L] →ₐ[𝒪[K]] 𝒪[M] where
  toFun x := ⟨f x, (map_mem_integer_iff f x).mpr x.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp
  commutes' r := by ext; simp

def residueAlgHom (f : L →ₐ[K] M) : 𝓀[L] →ₐ[𝓀[K]] 𝓀[M] :=
  letI : IsLocalHom (integerAlgHom f) :=
    ⟨fun x => by
      rw [← not_imp_not, Valuation.Integer.not_isUnit_iff_valuation_lt_one,
        Valuation.Integer.not_isUnit_iff_valuation_lt_one]
      exact (valuation_map_lt_one_iff f x).mpr⟩
  IsLocalRing.ResidueField.mapAlgHom' (integerAlgHom f)

variable (K L)

theorem valuation_algEquiv_apply (σ : L ≃ₐ[K] L) (x : L) : valuation L (σ x) = valuation L x := by

  have key : ∀ (τ : L ≃ₐ[K] L) (y : L), ¬ valuation L (τ y) < valuation L y := by
    intro τ y h
    have hpow : ∀ m : ℕ, valuation L ((τ ^ (m + 1)) y) < valuation L y := by
      intro m
      induction m with
      | zero => simpa using h
      | succ m ih =>
        rw [pow_succ', AlgEquiv.mul_apply]
        exact ((valuation_map_lt_iff τ.toAlgHom _ _).mpr ih).trans h
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (orderOf_pos τ).ne'
    have := hpow m
    rw [← Nat.succ_eq_add_one, ← hm, pow_orderOf_eq_one, AlgEquiv.one_apply] at this
    exact this.false
  rcases lt_trichotomy (valuation L (σ x)) (valuation L x) with h | h | h
  · exact (key σ x h).elim
  · exact h
  · refine (key σ.symm (σ x) ?_).elim
    simpa using h

def integerAlgEquiv : (L ≃ₐ[K] L) →* (𝒪[L] ≃ₐ[𝒪[K]] 𝒪[L]) where
  toFun σ := AlgEquiv.ofAlgHom (integerAlgHom σ.toAlgHom) (integerAlgHom σ.symm.toAlgHom)
    (AlgHom.ext fun x => Subtype.ext (σ.apply_symm_apply (x : L)))
    (AlgHom.ext fun x => Subtype.ext (σ.symm_apply_apply (x : L)))
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

@[simp]
theorem coe_integerAlgEquiv_apply (σ : L ≃ₐ[K] L) (x : 𝒪[L]) :
    (integerAlgEquiv K L σ x : L) = σ x :=
  rfl

def residueAlgEquiv : (L ≃ₐ[K] L) →* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) where
  toFun σ := IsLocalRing.ResidueField.mapAlgEquiv' (integerAlgEquiv K L σ)
  map_one' := by
    ext x
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    simp
  map_mul' σ τ := by
    ext x
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    simp

@[simp]
theorem residueAlgEquiv_residue (σ : L ≃ₐ[K] L) (x : 𝒪[L]) :
    residueAlgEquiv K L σ (IsLocalRing.residue 𝒪[L] x) =
      IsLocalRing.residue 𝒪[L] (integerAlgEquiv K L σ x) :=
  rfl

end Galois

end GroundTheory.LocalField
end
end

section -- merged from GroundTheory.LocalFields.UnitsPowers
namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing Polynomial
open scoped WithZero

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem isAdicComplete_integer : IsAdicComplete 𝓂[K] 𝒪[K] := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

variable {K}

theorem isUnit_unit_add {η : 𝒪[K]ˣ} {x : 𝒪[K]} (hx : x ∈ 𝓂[K]) : IsUnit ((η : 𝒪[K]) + x) := by
  have h1 : IsUnit (1 + (η⁻¹ : 𝒪[K]ˣ) * x) := by
    simpa using isUnit_one_sub_self_of_mem_nonunits (-(((η⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * x))
      ((IsLocalRing.mem_maximalIdeal _).mp (neg_mem (Ideal.mul_mem_left _ _ hx)))
  have : (η : 𝒪[K]) + x = η * (1 + (η⁻¹ : 𝒪[K]ˣ) * x) := by
    rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]
  rw [this]
  exact η.isUnit.mul h1

theorem exists_root_of_dvd {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (f : 𝒪[K][X]) (a : 𝒪[K]) (k : ℕ)
    (ε : 𝒪[K]ˣ) (hd : f.derivative.eval a = ϖ ^ k * ε) (hf : ϖ ^ (2 * k + 1) ∣ f.eval a) :
    ∃ b, f.eval b = 0 ∧ ϖ ^ (k + 1) ∣ b - a :=
  _root_.UpperTheory.Reformulated.B.AdicCompleteRootExistence.exists_root_of_dvd hϖ f a k ε hd hf

theorem eq_one_of_pow_eq_one {m : ℕ} (hm : (m : 𝓀[K]) ≠ 0) {u : 𝒪[K]ˣ}
    (hu : u ∈ unitFiltration K 1) (h : u ^ m = 1) : u = 1 := by
  have hres : residue 𝒪[K] (u : 𝒪[K]) = 1 := by
    have := (residue_eq_zero_iff _).mpr (by have := mem_unitFiltration.mp hu; rwa [pow_one] at this)
    rwa [map_sub, map_one, sub_eq_zero] at this
  have hgeom := geom_sum_mul (u : 𝒪[K]) m
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one, sub_self] at hgeom
  have hS : IsUnit (∑ i ∈ Finset.range m, (u : 𝒪[K]) ^ i) := by
    rw [← residue_ne_zero_iff_isUnit]
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, hres] using hm
  have := (hS.mul_right_eq_zero).mp hgeom
  ext
  simpa [sub_eq_zero] using this

section Teichmuller

variable (K)

theorem one_lt_card_residueField : 1 < Nat.card 𝓀[K] := Finite.one_lt_card

theorem natCast_card_residueField_sub_one_ne_zero : ((Nat.card 𝓀[K] - 1 : ℕ) : 𝓀[K]) ≠ 0 := by
  have : Fintype 𝓀[K] := Fintype.ofFinite _
  have hq : ((Nat.card 𝓀[K] : ℕ) : 𝓀[K]) = 0 := by
    rw [Nat.card_eq_fintype_card]; exact FiniteField.cast_card_eq_zero _
  rw [Nat.cast_sub (one_lt_card_residueField K).le, hq, Nat.cast_one, zero_sub]
  exact neg_ne_zero.mpr one_ne_zero

variable {K}

theorem exists_teichmuller_lift (ζ : 𝓀[K]ˣ) :
    ∃ u : 𝒪[K]ˣ, u ^ (Nat.card 𝓀[K] - 1) = 1 ∧ unitsToResidue K u = ζ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  set n := Nat.card 𝓀[K] - 1 with hn
  have hn0 : n ≠ 0 := by have := one_lt_card_residueField K; omega
  obtain ⟨a, ha⟩ := residue_surjective (ζ : 𝓀[K])
  have hζ : ζ ^ n = 1 := by
    rw [hn, ← Nat.card_units]; exact pow_card_eq_one'
  set f : 𝒪[K][X] := X ^ n - 1
  have hfa : f.eval a ∈ 𝓂[K] := by
    rw [← residue_eq_zero_iff]
    simp [f, ha, ← Units.val_pow_eq_pow_val, hζ]
  have hd : IsUnit (f.derivative.eval a) := by
    rw [← residue_ne_zero_iff_isUnit]
    simp only [f, derivative_sub, derivative_X_pow, derivative_one, sub_zero, eval_mul,
      eval_pow, eval_X, eval_natCast, map_mul, map_natCast, map_pow, ha]
    exact mul_ne_zero (natCast_card_residueField_sub_one_ne_zero K) (pow_ne_zero _ ζ.ne_zero)
  obtain ⟨b, hb, hba⟩ := exists_root_of_dvd hϖ f a 0 hd.unit (by simp)
    (by simpa using (mem_maximalIdeal_iff_dvd hϖ).mp hfa)
  have hbn : b ^ n = 1 := by simpa [f, sub_eq_zero] using hb
  have hbu : IsUnit b := (isUnit_pow_iff hn0).mp (hbn ▸ isUnit_one)
  refine ⟨hbu.unit, ?_, ?_⟩
  · ext; simp [hbn]
  · ext
    rw [coe_unitsToResidue, IsUnit.unit_spec, ← ha, ← sub_eq_zero, ← map_sub,
      residue_eq_zero_iff, mem_maximalIdeal_iff_dvd hϖ]
    simpa using hba

theorem eq_of_pow_card_sub_one {u w : 𝒪[K]ˣ} (hu : u ^ (Nat.card 𝓀[K] - 1) = 1)
    (hw : w ^ (Nat.card 𝓀[K] - 1) = 1) (h : unitsToResidue K u = unitsToResidue K w) :
    u = w := by
  have hmem : u * w⁻¹ ∈ unitFiltration K 1 := by
    rw [← ker_unitsToResidue, MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  have := eq_one_of_pow_eq_one (natCast_card_residueField_sub_one_ne_zero K) hmem
    (by rw [mul_pow, inv_pow, hu, hw, inv_one, mul_one])
  rwa [mul_inv_eq_one] at this

variable (K)

noncomputable def teichmuller : 𝓀[K]ˣ →* 𝒪[K]ˣ where
  toFun ζ := (exists_teichmuller_lift ζ).choose
  map_one' := eq_of_pow_card_sub_one (exists_teichmuller_lift 1).choose_spec.1 (one_pow _)
    (by rw [(exists_teichmuller_lift 1).choose_spec.2, map_one])
  map_mul' ζ η := eq_of_pow_card_sub_one (exists_teichmuller_lift (ζ * η)).choose_spec.1
    (by rw [mul_pow, (exists_teichmuller_lift ζ).choose_spec.1,
      (exists_teichmuller_lift η).choose_spec.1, one_mul])
    (by rw [(exists_teichmuller_lift (ζ * η)).choose_spec.2, map_mul,
      (exists_teichmuller_lift ζ).choose_spec.2, (exists_teichmuller_lift η).choose_spec.2])

variable {K}

@[simp]
theorem unitsToResidue_teichmuller (ζ : 𝓀[K]ˣ) : unitsToResidue K (teichmuller K ζ) = ζ :=
  (exists_teichmuller_lift ζ).choose_spec.2

theorem teichmuller_pow_card_sub_one (ζ : 𝓀[K]ˣ) :
    teichmuller K ζ ^ (Nat.card 𝓀[K] - 1) = 1 :=
  (exists_teichmuller_lift ζ).choose_spec.1

theorem unitsMulInvTeichmuller_mem (u : 𝒪[K]ˣ) :
    u * (teichmuller K (unitsToResidue K u))⁻¹ ∈ unitFiltration K 1 := by
  rw [← ker_unitsToResidue, MonoidHom.mem_ker, map_mul, map_inv, unitsToResidue_teichmuller,
    mul_inv_cancel]

variable (K)

end Teichmuller

section Powers

theorem exists_pow_eq_of_mem {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {m k : ℕ} (hm : m ≠ 0)
    {ε : 𝒪[K]ˣ} (hmk : (m : 𝒪[K]) = ϖ ^ k * ε) {w : 𝒪[K]ˣ}
    (hw : w ∈ unitFiltration K (2 * k + 1)) : ∃ x : 𝒪[K]ˣ, x ^ m = w := by
  set f : 𝒪[K][X] := X ^ m - C (w : 𝒪[K])
  obtain ⟨b, hb, -⟩ := exists_root_of_dvd hϖ f 1 k ε
    (by
      simp only [f, derivative_sub, derivative_C, sub_zero, derivative_X_pow, eval_mul,
        eval_C, eval_pow, eval_X, one_pow, mul_one]
      exact hmk)
    (by
      have := (mem_maximalIdeal_pow_iff hϖ).mp (mem_unitFiltration.mp hw)
      have e : f.eval 1 = -((w : 𝒪[K]) - 1) := by simp [f]
      rw [e, dvd_neg]
      exact this)
  have hbm : b ^ m = w := by simpa [f, sub_eq_zero] using hb
  have hbu : IsUnit b := (isUnit_pow_iff hm).mp (hbm ▸ w.isUnit)
  exact ⟨hbu.unit, by ext; simp [hbm]⟩

theorem exists_unitFiltration_le_range_pow {m : ℕ} (hm : (m : K) ≠ 0) :
    ∃ N, unitFiltration K N ≤ (powMonoidHom m : 𝒪[K]ˣ →* 𝒪[K]ˣ).range := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hm' : (m : 𝒪[K]) ≠ 0 := fun h ↦ hm (by have := congrArg Subtype.val h; simpa using this)
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  obtain ⟨k, ε, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hm' hϖ
  refine ⟨2 * k + 1, fun w hw ↦ ?_⟩
  obtain ⟨x, hx⟩ := exists_pow_eq_of_mem hϖ hm0 (ε := ε) (by rw [hk, mul_comm]) hw
  exact ⟨x, hx⟩

theorem finite_quotient_range_pow {m : ℕ} (hm : (m : K) ≠ 0) :
    Finite (Kˣ ⧸ (powMonoidHom m : Kˣ →* Kˣ).range) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨N, hN⟩ := exists_unitFiltration_le_range_pow hm
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  set H := (powMonoidHom m : Kˣ →* Kˣ).range
  set ψ : 𝒪[K]ˣ →* Kˣ ⧸ H := (QuotientGroup.mk' H).comp (unitsIncl K)
  have hle : unitFiltration K N ≤ ψ.ker := by
    intro w hw
    obtain ⟨x, rfl⟩ := hN hw
    rw [MonoidHom.mem_ker]
    simp only [ψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨unitsIncl K x, by simp⟩
  set ψ' := QuotientGroup.lift _ ψ hle
  set π := uniformizerUnit hϖ
  let g : Fin m × (𝒪[K]ˣ ⧸ unitFiltration K N) → Kˣ ⧸ H :=
    fun p ↦ (QuotientGroup.mk π : Kˣ ⧸ H) ^ (p.1 : ℕ) * ψ' p.2
  refine Finite.of_surjective g ?_
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  set p := unitsEquivIntProd hϖ x
  have hx : x = unitsOfIntProd hϖ p := by
    rw [← unitsEquivIntProd_symm_apply, MulEquiv.symm_apply_apply]
  set n := Multiplicative.toAdd p.1
  have hmpos : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  set r := n % (m : ℤ)
  set q := n / (m : ℤ)
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hmpos.ne'
  have hrm : r < m := Int.emod_lt_of_pos _ hmpos
  have hnrq : n = r + m * q := by have := Int.mul_ediv_add_emod n m; linarith
  refine ⟨(⟨r.toNat, by omega⟩, QuotientGroup.mk p.2), ?_⟩
  have hπ : π ^ n = π ^ r.toNat * (π ^ q) ^ m := by
    rw [← zpow_natCast, ← zpow_natCast (π ^ q) m, ← zpow_mul, ← zpow_add, Int.toNat_of_nonneg hr0,
      hnrq, mul_comm]
  have hxπ : x = π ^ n * unitsIncl K p.2 := by
    rw [hx]
    rfl
  simp only [g, ψ', QuotientGroup.lift_mk, ψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  rw [hxπ, hπ, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  refine ⟨π ^ q, ?_⟩
  rw [powMonoidHom_apply, mul_right_comm (π ^ r.toNat), inv_mul_cancel_left]

theorem finite_quotient_range_pow_of_charZero [CharZero K] {m : ℕ} (hm : m ≠ 0) :
    Finite (Kˣ ⧸ (powMonoidHom m : Kˣ →* Kˣ).range) :=
  finite_quotient_range_pow (Nat.cast_ne_zero.mpr hm)

end Powers

end GroundTheory.LocalField
end

section -- merged from GroundTheory.LocalFields.FiniteExtension
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel

section Base

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

@[instance_reducible]
def normedField : NontriviallyNormedField K :=
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  Valued.toNontriviallyNormedField K (ValueGroupWithZero K)

theorem normedField_norm_le_norm_iff (x y : K) :
    letI := normedField K
    ‖x‖ ≤ ‖y‖ ↔ x ≤ᵥ y := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  let : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  rw [(valuation K).vle_iff_le]
  exact Valued.toNormedField.norm_le_iff

theorem normedField_isUltrametricDist :
    letI := normedField K
    IsUltrametricDist K := by
  let := normedField K
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => ?_
  rcases vle_add_cases x y with h | h
  · exact ((normedField_norm_le_norm_iff K _ _).2 h).trans (le_max_left _ _)
  · exact ((normedField_norm_le_norm_iff K _ _).2 h).trans (le_max_right _ _)

theorem normedField_completeSpace :
    letI := normedField K
    CompleteSpace K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  exact (inferInstance : CompleteSpace K)

theorem normedField_properSpace :
    letI := normedField K
    ProperSpace K := by
  let := normedField K
  exact .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K

end Base

section Extension

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

@[instance_reducible]
def spectralNormedField : NontriviallyNormedField L :=
  letI := normedField K
  haveI := normedField_isUltrametricDist K
  haveI := normedField_completeSpace K
  spectralNorm.nontriviallyNormedField K L

theorem spectralNormedField_isUltrametricDist :
    letI := spectralNormedField K L
    IsUltrametricDist L := by
  let := normedField K
  have := normedField_isUltrametricDist K
  have := normedField_completeSpace K
  let := spectralNormedField K L
  exact IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := K) (L := L))

theorem spectralNormedField_norm_algebraMap (a : K) :
    letI := normedField K
    letI := spectralNormedField K L
    ‖algebraMap K L a‖ = ‖a‖ := by
  let := normedField K
  exact spectralNorm_extends a

structure LocalFieldStructure (L : Type*) [Field L] where

  rel : ValuativeRel L

  top : TopologicalSpace L

@[instance_reducible]
def finiteExtensionStructure : LocalFieldStructure L :=
  letI := spectralNormedField K L
  haveI := spectralNormedField_isUltrametricDist K L
  { rel := ValuativeRel.ofValuation (NormedField.valuation (K := L))
    top := inferInstance }

theorem finiteExtensionStructure_vle_iff (x y : L) :
    letI := normedField K
    letI := spectralNormedField K L
    letI := (finiteExtensionStructure K L).rel
    x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := Iff.rfl

theorem finiteExtensionStructure_valuativeExtension :
    letI := (finiteExtensionStructure K L).rel
    ValuativeExtension K L := by
  let := (finiteExtensionStructure K L).rel
  constructor
  intro a b
  rw [finiteExtensionStructure_vle_iff, spectralNormedField_norm_algebraMap,
    spectralNormedField_norm_algebraMap, normedField_norm_le_norm_iff]

theorem finiteExtensionStructure_isNonarchimedeanLocalField :
    letI := (finiteExtensionStructure K L).rel
    letI := (finiteExtensionStructure K L).top
    IsNonarchimedeanLocalField L := by
  let := normedField K
  have := normedField_isUltrametricDist K
  have := normedField_completeSpace K
  have := normedField_properSpace K
  let := spectralNormedField K L
  have := spectralNormedField_isUltrametricDist K L
  let := (finiteExtensionStructure K L).rel
  have hc : (NormedField.valuation (K := L)).Compatible := Valuation.Compatible.ofValuation _
  refine { toIsValuativeTopology := ?_, toLocallyCompactSpace := ?_, toIsNontrivial := ?_ }
  · exact IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := L))
      (fun {s} => (NormedField.toValued (K := L)).is_topological_valuation s)
  · let : NormedSpace K L := spectralNorm.normedSpace K L
    have : ProperSpace L := FiniteDimensional.proper K L
    infer_instance
  · rw [isNontrivial_iff_isNontrivial (NormedField.valuation (K := L))]
    infer_instance

theorem exists_isNonarchimedeanLocalField_valuativeExtension :
    ∃ (_ : ValuativeRel L) (_ : TopologicalSpace L),
      IsNonarchimedeanLocalField L ∧ ValuativeExtension K L :=
  ⟨(finiteExtensionStructure K L).rel, (finiteExtensionStructure K L).top,
    finiteExtensionStructure_isNonarchimedeanLocalField K L,
    finiteExtensionStructure_valuativeExtension K L⟩

end Extension

end GroundTheory.LocalField
end
end

section -- merged from GroundTheory.LocalFields.ExamplesLaurent
open scoped LaurentSeries

namespace GroundTheory.LocalField

open ValuativeRel Polynomial IsLocalRing Topology Filter WithZero HahnSeries

namespace EqualChar

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

def ballIdeal (γ : (ValueGroupWithZero K)ˣ) : Ideal 𝒪[K] where
  carrier := {x | valuation K (x : K) < γ}
  add_mem' {a b} ha hb := by
    change valuation K ((a : K) + (b : K)) < γ
    exact lt_of_le_of_lt ((valuation K).map_add _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' c x hx := by
    change valuation K ((c : K) * (x : K)) < γ
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((Valuation.mem_integer_iff _ _).mp c.2)) hx

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem mem_ballIdeal {γ : (ValueGroupWithZero K)ˣ} {x : 𝒪[K]} :
    x ∈ ballIdeal K γ ↔ valuation K (x : K) < γ := Iff.rfl

theorem hasBasis_nhds_zero_integer :
    (𝓝 (0 : 𝒪[K])).HasBasis (fun _ => True)
      fun γ : (ValueGroupWithZero K)ˣ => ((ballIdeal K γ : Ideal 𝒪[K]) : Set 𝒪[K]) := by
  rw [nhds_subtype_eq_comap, ZeroMemClass.coe_zero]
  refine ((IsValuativeTopology.hasBasis_nhds_zero K).comap Subtype.val).congr
    (fun _ => Iff.rfl) fun γ _ => ?_
  ext x
  simp [mem_ballIdeal]

instance : IsLinearTopology 𝒪[K] 𝒪[K] :=
  IsLinearTopology.mk_of_hasBasis' 𝒪[K] (hasBasis_nhds_zero_integer K)
    fun I r _ hx => I.mul_mem_left r hx

variable (p : ℕ) [Fact p.Prime] [CharP K p]

section Uniform

end Uniform


end EqualChar

end GroundTheory.LocalField
end

section -- merged from GroundTheory.LocalFields.ExamplesCharZero
namespace GroundTheory.LocalField

open ValuativeRel WithZero Topology

namespace CharZero

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

instance fact_prime_ringChar : Fact (ringChar 𝓀[K]).Prime :=
  ⟨CharP.char_is_prime 𝓀[K] (ringChar 𝓀[K])⟩

variable (p : ℕ) [CharP 𝓀[K] p]


omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem valuation_intCast_le_one (n : ℤ) : valuation K (n : K) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).mp (intCast_mem _ n)

theorem valuation_intCast_eq_one_iff (n : ℤ) : valuation K (n : K) = 1 ↔ ¬ (p : ℤ) ∣ n := by
  have hres : IsLocalRing.residue 𝒪[K] (n : 𝒪[K]) = (n : 𝓀[K]) := map_intCast _ n
  rw [← CharP.intCast_eq_zero_iff 𝓀[K] p n, ← hres, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  push_cast
  constructor
  · intro h
    simp [h]
  · intro h
    exact le_antisymm (valuation_intCast_le_one K n) (not_lt.mp h)

variable [Fact p.Prime]


omit [Fact p.Prime] in
theorem valuation_p_lt_one : valuation K (p : K) < 1 := by
  refine lt_of_le_of_ne (by exact_mod_cast valuation_intCast_le_one K p) fun h => ?_
  have := (valuation_intCast_eq_one_iff K p p).mp (by exact_mod_cast h)
  exact this dvd_rfl

variable [CharZero K]

theorem valuation_ratCast_le_one_iff (q : ℚ) : valuation K (q : K) ≤ 1 ↔ ¬ p ∣ q.den := by
  have hden : (q.den : K) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hq : (q : K) = (q.num : K) / (q.den : K) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have hvden : valuation K (q.den : K) ≠ 0 := by simp
  rw [hq, map_div₀, div_le_one₀ (zero_lt_iff.mpr hvden)]
  constructor
  · intro h hp
    have hnum : ¬ (p : ℤ) ∣ q.num := by
      intro hn
      rw [Int.natCast_dvd] at hn
      exact Nat.not_coprime_of_dvd_of_dvd (Nat.Prime.one_lt Fact.out) hn hp q.reduced
    have h1 := (valuation_intCast_eq_one_iff K p q.num).mpr hnum
    obtain ⟨m, hm⟩ := hp
    have h2 : valuation K (q.den : K) < 1 := by
      rw [hm, Nat.cast_mul, map_mul]
      calc valuation K (p : K) * valuation K (m : K)
          ≤ valuation K (p : K) * 1 := by
            gcongr
            exact_mod_cast valuation_intCast_le_one K m
        _ < 1 := by simp [valuation_p_lt_one K p]
    rw [h1] at h
    exact absurd h (not_le.mpr h2)
  · intro hp
    have h1 : valuation K (q.den : K) = 1 := by
      have := (valuation_intCast_eq_one_iff K p q.den).mpr (by exact_mod_cast hp)
      exact_mod_cast this
    rw [h1]
    exact valuation_intCast_le_one K q.num

theorem isEquiv_comap_ratCast :
    ((valuation K).comap (Rat.castHom K)).IsEquiv (Rat.padicValuation p) :=
  Valuation.isEquiv_of_val_le_one fun q => by
    simp [valuation_ratCast_le_one_iff K p, Rat.padicValuation_le_one_iff]

section Embedding

noncomputable abbrev ratHom : WithVal (Rat.padicValuation p) →+* K :=
  (Rat.castHom K).comp (WithVal.equiv (Rat.padicValuation p)).toRingHom

theorem continuousAt_ratHom : ContinuousAt (ratHom K p) 0 := by
  rw [ContinuousAt, map_zero]
  refine ((IsValuativeTopology.hasBasis_nhds_zero' _).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero' K)).mpr fun γ hγ => ?_
  obtain ⟨n, hn⟩ := exists_pow_lt₀ (valuation_p_lt_one K p) (Units.mk0 γ hγ)
  set v := Rat.padicValuation p
  set t : WithVal v := (WithVal.equiv v).symm ((p : ℚ) ^ n)
  refine ⟨valuation (WithVal v) t, ?_, fun x hx => ?_⟩
  · simp [t, Nat.Prime.ne_zero Fact.out]
  · simp only [Set.mem_ofPred_eq] at hx ⊢
    have h1 := (ValuativeRel.isEquiv (valuation (WithVal v)) (WithVal.valuation v)).lt_iff_lt.mp hx
    have h2 : v (WithVal.equiv v x) < v ((p : ℚ) ^ n) := by simpa [t] using h1
    have h3 := (isEquiv_comap_ratCast K p).lt_iff_lt.mpr h2
    simp only [Valuation.comap_apply, Rat.coe_castHom] at h3
    calc valuation K (ratHom K p x) = valuation K ((WithVal.equiv v x : ℚ) : K) := rfl
      _ < valuation K (((p : ℚ) ^ n : ℚ) : K) := h3
      _ = valuation K (p : K) ^ n := by simp
      _ < γ := hn

section Uniform

local instance uniformSpaceK : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K

local instance isUniformAddGroupK : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup

theorem uniformContinuous_ratHom : UniformContinuous (ratHom K p) :=
  uniformContinuous_of_continuousAt_zero (ratHom K p) (continuousAt_ratHom K p)

noncomputable def padicHom : ℚ_[p] →+* K :=
  IsDenseInducing.extendRingHom Padic.isUniformInducing_cast_withVal
    Padic.isDenseInducing_cast_withVal.dense (uniformContinuous_ratHom K p)

theorem continuous_padicHom : Continuous (padicHom K p) :=
  (uniformContinuous_uniformly_extend Padic.isUniformInducing_cast_withVal
    Padic.isDenseInducing_cast_withVal.dense (uniformContinuous_ratHom K p)).continuous

end Uniform

theorem valuation_padicHom_padicInt_le_one (x : ℤ_[p]) :
    valuation K (padicHom K p (x : ℚ_[p])) ≤ 1 := by
  refine PadicInt.denseRange_intCast.induction_on x ?_ fun n => ?_
  · exact (Valuation.isClosed_integer (v := valuation K)).preimage
      ((continuous_padicHom K p).comp continuous_subtype_val)
  · simpa using valuation_intCast_le_one K n

theorem valuation_padicHom_le_one_iff (x : ℚ_[p]) :
    valuation K (padicHom K p x) ≤ 1 ↔ ‖x‖ ≤ 1 := by
  refine ⟨fun hv => ?_, fun hx => valuation_padicHom_padicInt_le_one K p ⟨x, hx⟩⟩
  by_contra hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.Prime.ne_zero Fact.out)
  set y : ℚ_[p] := ((p : ℚ_[p]) * x)⁻¹
  have hxinv : ‖x⁻¹‖ ≤ (p : ℝ) ^ (-1 : ℤ) := by
    have : ‖x⁻¹‖ < (p : ℝ) ^ (0 : ℤ) := by
      rw [norm_inv, zpow_zero]
      exact inv_lt_one_of_one_lt₀ (not_le.mp hx)
    simpa using (Padic.norm_lt_pow_iff_norm_le_pow_sub_one x⁻¹ 0).mp this
  have hy : ‖y‖ ≤ 1 := by
    have hp : (0 : ℝ) < p := by exact_mod_cast (Nat.Prime.pos Fact.out)
    simp only [y, mul_inv, norm_mul, norm_inv, Padic.norm_p, inv_inv] at hxinv ⊢
    rw [zpow_neg_one] at hxinv
    calc (p : ℝ) * ‖x‖⁻¹ ≤ p * (p : ℝ)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hp.ne'
  have hvy := valuation_padicHom_padicInt_le_one K p ⟨y, hy⟩
  simp only at hvy
  have hone : padicHom K p x * padicHom K p y * padicHom K p p = 1 := by
    rw [← map_mul, ← map_mul]
    simp [y, hx0, hp0]
  have hvp : valuation K (padicHom K p p) < 1 := by
    simpa using valuation_p_lt_one K p
  have := congrArg (valuation K) hone
  rw [map_mul, map_mul, map_one] at this
  have h1 : valuation K (padicHom K p x) * valuation K (padicHom K p y) ≤ 1 :=
    mul_le_one' hv hvy
  have h2 := (mul_le_of_le_one_left' h1 : _ ≤ valuation K (padicHom K p p))
  exact absurd (this ▸ h2) (not_le.mpr hvp)

theorem isEquiv_comap_padicHom :
    ((valuation K).comap (padicHom K p)).IsEquiv Padic.mulValuation :=
  Valuation.isEquiv_of_val_le_one fun x => by
    rw [Valuation.comap_apply, valuation_padicHom_le_one_iff]
    simpa using (GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le p x 1).symm

theorem padicHom_vle_iff (a b : ℚ_[p]) : padicHom K p a ≤ᵥ padicHom K p b ↔ a ≤ᵥ b := by
  rw [Valuation.Compatible.vle_iff_le (v := valuation K),
    Valuation.Compatible.vle_iff_le (v := Padic.mulValuation)]
  simpa using (isEquiv_comap_padicHom K p).le_iff_le (x := a) (y := b)

theorem finiteDimensional_padicHom :
    letI := (padicHom K p).toAlgebra
    FiniteDimensional ℚ_[p] K := by
  let := (padicHom K p).toAlgebra
  have : T2Space K := by
    let := IsTopologicalAddGroup.rightUniformSpace K
    have := isUniformAddGroup_of_addCommGroup (G := K)
    infer_instance
  have : ContinuousSMul ℚ_[p] K :=
    ⟨((continuous_padicHom K p).comp continuous_fst).mul continuous_snd⟩
  exact FiniteDimensional.of_locallyCompactSpace ℚ_[p]

end Embedding

end CharZero

end GroundTheory.LocalField
end
