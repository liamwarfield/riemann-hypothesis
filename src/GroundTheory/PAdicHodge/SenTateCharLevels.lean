module

public import GroundTheory.LocalFields.LocalArtinCompletion
public import GroundTheory.PAdicHodge.FieldOfNormsCyclBase

@[expose] public section

section -- merged from GroundTheory.PAdicHodge.SenTateCharTower
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace SenTateChar

open CyclNorms GroundTheory.LocalField ValuativeRel

variable {p : ℕ} [hp : Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

instance isAlgClosure_padicAlgCl : IsAlgClosure K (PadicAlgCl p) :=
  ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) K⟩

variable {K} (η : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ)

def charTowerGal (k : ℕ) : Subgroup Gal(PadicAlgCl p/K) := (unitsOneAdd p k).comap η

theorem mem_charTowerGal {k : ℕ} {σ : Gal(PadicAlgCl p/K)} : σ ∈ charTowerGal η k ↔ η σ ∈ unitsOneAdd p k :=
  Iff.rfl

instance charTowerGal_normal (k : ℕ) : (charTowerGal η k).Normal :=
  Subgroup.Normal.comap (Subgroup.normal_of_isMulCommutative _) η

theorem charTowerGal_antitone : Antitone (charTowerGal η) := fun _ _ h =>
  Subgroup.comap_mono (unitsOneAdd_antitone h)

variable {η}

theorem isOpen_charTowerGal (hη : Continuous η) (k : ℕ) : IsOpen (charTowerGal η k : Set Gal(PadicAlgCl p/K)) :=
  (isOpen_unitsOneAdd k).preimage hη

theorem isClosed_charTowerGal (hη : Continuous η) (k : ℕ) :
    IsClosed (charTowerGal η k : Set Gal(PadicAlgCl p/K)) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_charTowerGal hη k)

variable (η)

def charTower (k : ℕ) : IntermediateField K (PadicAlgCl p) :=
  _root_.IntermediateField.fixedField (charTowerGal η k)

theorem charTower_mono : Monotone (charTower η) := fun _ _ h =>
  _root_.IntermediateField.fixedField_antitone (charTowerGal_antitone η h)

variable {η}

theorem fixingSubgroup_charTower (hη : Continuous η) (k : ℕ) :
    (charTower η k).fixingSubgroup = charTowerGal η k :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨charTowerGal η k, isClosed_charTowerGal hη k⟩

theorem finiteDimensional_charTower (hη : Continuous η) (k : ℕ) : FiniteDimensional K (charTower η k) := by
  have h := isOpen_charTowerGal hη k
  rw [← fixingSubgroup_charTower hη k] at h
  exact (InfiniteGalois.isOpen_iff_finite _).1 h

theorem isGalois_charTower (hη : Continuous η) (k : ℕ) : IsGalois K (charTower η k) := by
  rw [← InfiniteGalois.normal_iff_isGalois, fixingSubgroup_charTower hη]
  infer_instance

theorem restrictNormalHom_charTower_eq_one_iff (hη : Continuous η) (k : ℕ)
    [Normal K (charTower η k)] (σ : Gal(PadicAlgCl p/K)) :
    AlgEquiv.restrictNormalHom (charTower η k) σ = 1 ↔ η σ ∈ unitsOneAdd p k := by
  rw [← MonoidHom.mem_ker, (charTower η k).restrictNormalHom_ker, fixingSubgroup_charTower hη]
  rfl

theorem isAbelianGalois_charTower (hη : Continuous η) (k : ℕ) : IsAbelianGalois K (charTower η k) := by
  have := isGalois_charTower hη k
  refine { toIsGalois := inferInstance, toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩ }
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := charTower η k)
    (E := PadicAlgCl p) a
  obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := charTower η k)
    (E := PadicAlgCl p) b
  rw [← map_mul, ← map_mul, ← div_eq_one, ← map_div]
  rw [restrictNormalHom_charTower_eq_one_iff hη, map_div, map_mul, map_mul, mul_comm (η σ), div_self']
  exact one_mem _

theorem map_mem_charTower (hη : Continuous η) {k : ℕ} (σ : Gal(PadicAlgCl p/K)) {y : PadicAlgCl p}
    (hy : y ∈ charTower η k) : σ y ∈ charTower η k := by
  have := isGalois_charTower hη k
  have h : σ y = ((σ.restrictNormal (charTower η k) ⟨y, hy⟩ : charTower η k) : PadicAlgCl p) :=
    (AlgEquiv.restrictNormal_commutes σ (charTower η k) ⟨y, hy⟩).symm
  rw [h]
  exact SetLike.coe_mem _

section CFT

local instance : ValuativeExtension ℚ_[p] (PadicAlgCl p) := by
  refine ⟨fun {a b} ↦ ?_⟩
  rw [vle_iff_norm_le, PadicAlgCl.norm_extends, PadicAlgCl.norm_extends,
    Valuation.Compatible.vle_iff_le (v := Padic.mulValuation),
    GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le]

variable (K) [FiniteDimensional ℚ_[p] K]

def artinGal (n : ℕ) : Subgroup Gal(PadicAlgCl p/K) :=
  ((unitFiltrationUnits K n).map (localArtinMap K (PadicAlgCl p))).comap
    (AlgEquiv.restrictNormalHom (maximalAbelianExtension K (PadicAlgCl p)))


variable (η) in
def artinImage (n : ℕ) : Subgroup ℤ_[p]ˣ := (artinGal K n).map η

variable {K}

theorem artinGal_antitone : Antitone (artinGal K) := fun _ _ h =>
  Subgroup.comap_mono (Subgroup.map_mono (unitFiltrationUnits_antitone h))

variable (η) in
theorem artinImage_antitone : Antitone (artinImage K η) := fun _ _ h =>
  Subgroup.map_mono (artinGal_antitone h)


omit [FiniteDimensional ℚ_[p] K] in
theorem restrictAb_restrictNormalHom (E : IntermediateField K (PadicAlgCl p)) [Normal K E]
    (h : E ≤ maximalAbelianExtension K (PadicAlgCl p)) (ρ : Gal(PadicAlgCl p/K)) :
    restrictAb E h (AlgEquiv.restrictNormalHom (maximalAbelianExtension K (PadicAlgCl p)) ρ) =
      AlgEquiv.restrictNormalHom E ρ := by
  ext x
  rw [restrictAb_apply, AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]


omit [FiniteDimensional ℚ_[p] K] in
theorem eq_one_of_mem_fixingSubgroup_maximalAbelianExtension (hη : Continuous η)
    {ρ : Gal(PadicAlgCl p/K)}
    (hρ : ρ ∈ (maximalAbelianExtension K (PadicAlgCl p)).fixingSubgroup) : η ρ = 1 := by
  rw [fixingSubgroup_maximalAbelianExtension] at hρ
  have hker : (commutator Gal(PadicAlgCl p/K)).topologicalClosure ≤ η.ker := by
    refine Subgroup.topologicalClosure_minimal _ (Group.Abelianization.commutator_le_ker η) ?_
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage hη
  exact hker hρ

theorem restrictNormalHom_mem_upperRamificationGroup_iff (hη : Continuous η) (k n : ℕ)
    [FiniteDimensional K (charTower η k)] [IsAbelianGalois K (charTower η k)]
    (σ : Gal(PadicAlgCl p/K)) :
    AlgEquiv.restrictNormalHom (charTower η k) σ ∈ upperRamificationGroup K (charTower η k) n ↔
      η σ ∈ artinImage K η n ⊔ unitsOneAdd p k := by
  set M := charTower η k
  set Lab := maximalAbelianExtension K (PadicAlgCl p)
  have hM := le_maximalAbelianExtension M
  rw [← map_unitFiltrationUnits_restrictAb_localArtinMap M n, Subgroup.mem_sup]
  constructor
  · rintro ⟨u, hu, huσ⟩
    obtain ⟨ρ, hρ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := Lab)
      (E := PadicAlgCl p) (localArtinMap K (PadicAlgCl p) u)
    have hρA : ρ ∈ artinGal K n := ⟨u, hu, hρ.symm⟩
    refine ⟨η ρ, ⟨ρ, hρA, rfl⟩, η (ρ⁻¹ * σ), ?_, by rw [map_mul, map_inv, mul_inv_cancel_left]⟩
    have h1 : AlgEquiv.restrictNormalHom M (ρ⁻¹ * σ) = 1 := by
      rw [map_mul, map_inv, ← huσ, MonoidHom.comp_apply, ← hρ, restrictAb_restrictNormalHom,
        inv_mul_cancel]
    exact (restrictNormalHom_charTower_eq_one_iff hη k _).1 h1
  · rintro ⟨a, ⟨ρ, hρA, rfl⟩, b, hb, hab⟩
    obtain ⟨u, hu, hu'⟩ := hρA
    refine ⟨u, hu, ?_⟩
    have h1 : AlgEquiv.restrictNormalHom M (ρ⁻¹ * σ) = 1 := by
      refine (restrictNormalHom_charTower_eq_one_iff hη k _).2 ?_
      rw [map_mul, map_inv, ← hab, inv_mul_cancel_left]
      exact hb
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    rw [MonoidHom.comp_apply, hu', restrictAb_restrictNormalHom, h1]

theorem artinImage_add_eq_map_pow (hη : Continuous η) {n e : ℕ}
    (h : (unitFiltrationUnits K n).map (powMonoidHom p) = unitFiltrationUnits K (n + e)) :
    artinImage K η (n + e) = (artinImage K η n).map (powMonoidHom p) := by
  set Lab := maximalAbelianExtension K (PadicAlgCl p)
  ext a
  constructor
  · rintro ⟨ρ, ⟨u, hu, hu'⟩, rfl⟩
    rw [← h] at hu
    obtain ⟨w, hw, rfl⟩ := hu
    obtain ⟨ρw, hρw⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := Lab)
      (E := PadicAlgCl p) (localArtinMap K (PadicAlgCl p) w)
    refine ⟨η ρw, ⟨ρw, ⟨w, hw, hρw.symm⟩, rfl⟩, ?_⟩
    have hfix : ρ⁻¹ * ρw ^ p ∈ Lab.fixingSubgroup := by
      rw [← Lab.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv, map_pow, hρw, ← hu',
        powMonoidHom_apply, map_pow, inv_mul_cancel]
    have h1 := eq_one_of_mem_fixingSubgroup_maximalAbelianExtension hη hfix
    rw [map_mul, map_inv, inv_mul_eq_one, map_pow] at h1
    rw [powMonoidHom_apply, h1]
  · rintro ⟨b, ⟨ρ, ⟨w, hw, hw'⟩, rfl⟩, rfl⟩
    refine ⟨ρ ^ p, ⟨w ^ p, ?_, ?_⟩, ?_⟩
    · rw [← h]; exact ⟨w, hw, rfl⟩
    · rw [map_pow, map_pow, hw']
    · rw [map_pow, powMonoidHom_apply]

theorem artinImage_le_of_conductor_le (hη : Continuous η) [FiniteDimensional K (charTower η 2)]
    [IsAbelianGalois K (charTower η 2)] {n : ℕ} (hn : conductor (charTower η 2) ≤ n) :
    artinImage K η n ≤ unitsOneAdd p 2 := by
  rintro _ ⟨ρ, hρ, rfl⟩
  have h1 := (restrictNormalHom_mem_upperRamificationGroup_iff hη 2 n ρ).2
    (Subgroup.mem_sup_left ⟨ρ, hρ, rfl⟩)
  rw [(upperRamificationGroup_natCast_eq_bot_iff (charTower η 2) n).2 hn, Subgroup.mem_bot] at h1
  exact (restrictNormalHom_charTower_eq_one_iff hη 2 ρ).1 h1

end CFT

end SenTateChar

end GroundTheory.PAdicHodge
end
end

section -- merged from GroundTheory.PAdicHodge.SenTateCharUnitPow
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace SenTateChar

open GroundTheory.LocalField ValuativeRel IsLocalRing

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Powers

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

theorem natCast_prime_mem_valBall : (p : K) ∈ valBall K (absRamificationIndex K) := by
  rw [mem_valBall, normalizedValuation_natCast_prime p]

theorem div_natCast_prime_mem_valBall {a : ℤ} {x : K}
    (hx : x ∈ valBall K (a + absRamificationIndex K)) : x / p ∈ valBall K a := by
  have h := div_natCast_mem_valBall p hx hp.out.ne_zero
  rw [Nat.padicValNat_def, Nat.Prime.multiplicity_self, Nat.cast_one, mul_one, add_sub_cancel_right] at h
  exact h

theorem map_pow_unitFiltrationUnits {n : ℕ}
    (hn : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * n) :
    (unitFiltrationUnits K n).map (powMonoidHom p) =
      unitFiltrationUnits K (n + absRamificationIndex K) := by
  set e := absRamificationIndex K
  have hn1 : 1 ≤ n := one_le_of_lt_sub_one_mul_nat p hn
  have hp1 : (1 : ℤ) ≤ (p - 1 : ℤ) := by have := hp.out.two_le; omega
  have hn' : (e : ℤ) < (p - 1 : ℤ) * ((n + e : ℕ) : ℤ) := by
    have : (p - 1 : ℤ) * n ≤ (p - 1 : ℤ) * ((n + e : ℕ) : ℤ) :=
      mul_le_mul_of_nonneg_left (by push_cast; omega) (by omega)
    omega
  have hne : (n : ℤ) + e = ((n + e : ℕ) : ℤ) := by push_cast; ring

  have hlogpow : ∀ u : unitFiltrationUnits K n,
      logSeries (((u ^ p : unitFiltrationUnits K n) : Kˣ) - 1 : K) =
        p * logSeries ((((u : unitFiltrationUnits K n) : Kˣ) : K) - 1) := by
    intro u
    have h := map_nsmul (logValBallHom p n hn) p (Additive.ofMul u)
    have h' := congrArg Subtype.val h
    rw [← ofMul_pow] at h'
    rw [coe_logValBallHom] at h'
    simpa [coe_logValBallHom, nsmul_eq_mul] using h'
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    set U : unitFiltrationUnits K n := ⟨u, hu⟩
    have hU : ((U ^ p : unitFiltrationUnits K n) : Kˣ) = powMonoidHom p u := rfl

    have hlog : logSeries ((((U ^ p : unitFiltrationUnits K n) : Kˣ) : K) - 1) ∈
        valBall K ((n + e : ℕ) : ℤ) := by
      rw [hlogpow U, ← hne, add_comm]
      exact mul_mem_valBall (natCast_prime_mem_valBall p)
        (logSeries_mem_valBall p (sub_one_mem_valBall_of_mem hn1 U) hn)
    have hexp := expSeries_logSeries p hn (U ^ p)
    have hmem := expSeries_sub_one_mem p hlog hn'
    rw [hexp] at hmem
    rw [← hU]
    exact (mem_unitFiltrationUnits_iff_valBall (by omega)).2 hmem
  · intro w hw
    have hwn : w ∈ unitFiltrationUnits K n := unitFiltrationUnits_antitone (by omega) hw
    set W : unitFiltrationUnits K n := ⟨w, hwn⟩
    have hy : logSeries (((w : Kˣ) : K) - 1) ∈ valBall K (n + e) := by
      rw [hne]
      exact logSeries_mem_valBall p ((mem_unitFiltrationUnits_iff_valBall (by omega)).1 hw) hn'
    have hz : logSeries (((w : Kˣ) : K) - 1) / p ∈ valBall K n := div_natCast_prime_mem_valBall p hy
    set u := expUnit p n hn ⟨_, hz⟩
    refine ⟨(u : Kˣ), u.property, ?_⟩
    have hinj := logValBallHom_injective p n hn
    have key : logValBallHom p n hn (Additive.ofMul (u ^ p)) =
        logValBallHom p n hn (Additive.ofMul W) := by
      apply Subtype.ext
      rw [coe_logValBallHom, coe_logValBallHom]
      change logSeries (((u ^ p : unitFiltrationUnits K n) : Kˣ) - 1 : K) = _
      rw [hlogpow u]
      have hu := congrArg Subtype.val (logValBallHom_expUnit p n hn ⟨_, hz⟩)
      rw [coe_logValBallHom, toMul_ofMul] at hu
      have hu' : logSeries ((((u : unitFiltrationUnits K n) : Kˣ) : K) - 1) =
          logSeries (((w : Kˣ) : K) - 1) / p := hu
      rw [hu', toMul_ofMul]
      have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
      field_simp
      rfl
    have := congrArg (fun v => ((Additive.toMul v : unitFiltrationUnits K n) : Kˣ)) (hinj key)
    exact this

theorem exists_map_pow_unitFiltrationUnits :
    ∃ n₀, ∀ n ≥ n₀, (unitFiltrationUnits K n).map (powMonoidHom p) =
      unitFiltrationUnits K (n + absRamificationIndex K) := by
  refine ⟨absRamificationIndex K + 1, fun n hn => map_pow_unitFiltrationUnits p ?_⟩
  have hp1 : (1 : ℤ) ≤ (p - 1 : ℤ) := by have := hp.out.two_le; omega
  have : (n : ℤ) ≤ (p - 1 : ℤ) * n := le_mul_of_one_le_left (by omega) hp1
  omega

end Powers

section Residue

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p]


omit hp in
theorem not_dvd_card_residueField_sub_one : ¬ p ∣ Nat.card 𝓀[K] - 1 := by
  intro h
  apply natCast_card_residueField_sub_one_ne_zero K
  exact (CharP.cast_eq_zero_iff 𝓀[K] p _).2 h

theorem pow_card_sub_one_mem_unitFiltration (v : 𝒪[K]ˣ) :
    v ^ (Nat.card 𝓀[K] - 1) ∈ unitFiltration K 1 := by
  have h := pow_mem (unitsMulInvTeichmuller_mem v) (Nat.card 𝓀[K] - 1)
  rwa [mul_pow, inv_pow, teichmuller_pow_card_sub_one, inv_one, mul_one] at h

theorem pow_prime_pow_mem_unitFiltrationUnits {x : Kˣ} (hx : x ∈ unitFiltrationUnits K 1) (n : ℕ) :
    x ^ p ^ n ∈ unitFiltrationUnits K (n + 1) := by
  have h := nsmul_prime_pow_mem_principalFiltration p
    (u := Additive.ofMul (⟨x, hx⟩ : unitFiltrationUnits K 1))
    (by rw [principalFiltration_zero]; exact AddSubgroup.mem_top _) n
  rw [zero_add, mem_principalFiltration, toMul_nsmul, toMul_ofMul] at h
  rw [mem_unitFiltrationUnits_iff_valBall (by omega)]
  exact_mod_cast h

theorem exists_pow_mem_unitFiltrationUnits (n : ℕ) :
    ∃ c j : ℕ, ¬ p ∣ c ∧ ∀ u ∈ unitFiltrationUnits K 0, u ^ (c * p ^ j) ∈ unitFiltrationUnits K n := by
  refine ⟨Nat.card 𝓀[K] - 1, n, not_dvd_card_residueField_sub_one p, fun u hu => ?_⟩
  obtain ⟨v, -, rfl⟩ := hu
  have h1 : unitsIncl K (v ^ (Nat.card 𝓀[K] - 1)) ∈ unitFiltrationUnits K 1 :=
    ⟨_, pow_card_sub_one_mem_unitFiltration v, rfl⟩
  have h2 := pow_prime_pow_mem_unitFiltrationUnits p h1 n
  rw [map_pow, ← pow_mul] at h2
  exact unitFiltrationUnits_antitone (by omega) h2

end Residue

section Norm

variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [Algebra K Ω] [ValuativeExtension K Ω]
  [Algebra.IsAlgebraic K Ω]

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

theorem nrm_natCast_prime_eq :
    nrm K (p : Ω) = baseUnifNrm K Ω ^ absRamificationIndex K := by
  have hirr := (IsDiscreteValuationRing.exists_irreducible 𝒪[K]).choose_spec
  have hv : normalizedValuation K (p : K) =
      normalizedValuation K (((baseUnif K : 𝒪[K]) : K) ^ absRamificationIndex K) := by
    rw [normalizedValuation_natCast_prime p, map_pow, baseUnif, normalizedValuation_uniformizer hirr,
      ← WithZero.exp_nsmul]
    simp
  have key : ∀ a b : K, normalizedValuation K a = normalizedValuation K b →
      nrm K (algebraMap K Ω a) = nrm K (algebraMap K Ω b) := by
    intro a b hab
    have h1 : a ≤ᵥ b := (Valuation.vle_iff_le (valuation K)).2 (normalizedValuation_le_iff.1 hab.le)
    have h2 : b ≤ᵥ a := (Valuation.vle_iff_le (valuation K)).2 (normalizedValuation_le_iff.1 hab.ge)
    exact le_antisymm ((nrm_le_nrm_iff _ _).2 ((ValuativeExtension.vle_iff_vle).2 h1))
      ((nrm_le_nrm_iff _ _).2 ((ValuativeExtension.vle_iff_vle).2 h2))
  have h := key _ _ hv
  rw [map_natCast] at h
  rw [h, map_pow, nrm_pow]
  rfl

end Norm

section ResidueChar

variable (p : ℕ) [hp : Fact p.Prime]

theorem charP_residueField_of_valuativeExtension (F : Type*) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra ℚ_[p] F]
    [ValuativeExtension ℚ_[p] F] : CharP 𝓀[F] p := by
  refine (CharP.charP_iff_prime_eq_zero hp.out).mpr ?_
  rw [← map_natCast (IsLocalRing.residue 𝒪[F]), IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  have hq : ¬ ((1 : ℚ_[p]) ≤ᵥ (p : ℚ_[p])) := by
    rw [Valuation.Compatible.vle_iff_le (v := Padic.mulValuation),
      GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le, norm_one, Padic.norm_p]
    exact not_le.2 (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt))
  have hF : ¬ ((1 : F) ≤ᵥ (p : F)) := by
    intro h
    apply hq
    rw [← ValuativeExtension.vle_iff_vle (A := ℚ_[p]) (B := F), map_one, map_natCast]
    exact h
  have e : (((p : 𝒪[F]) : F)) = (p : F) := by push_cast; rfl
  rw [e, ← map_one (valuation F)]
  exact lt_of_not_ge fun h => hF ((Valuation.vle_iff_le (valuation F)).2 h)

end ResidueChar

end SenTateChar

end GroundTheory.PAdicHodge
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace SenTateChar

open CyclNorms GroundTheory.LocalField ValuativeRel

variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
  [FiniteDimensional ℚ_[p] K] {η : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ}

instance valuativeExtension_charTower (k : ℕ) : ValuativeExtension K (charTower η k) :=
  GroundTheory.LocalField.intermediateField_valuativeExtension_left _


variable (K η) in
def artinLevel (n : ℕ) : ℕ := sInf {k | ¬ artinImage K η n ≤ unitsOneAdd p (k + 1)}

theorem artinLevel_spec {n : ℕ} (h : artinImage K η n ≠ ⊥) :
    artinImage K η n ≤ unitsOneAdd p (artinLevel K η n) ∧
      ∃ a ∈ artinImage K η n, a ∉ unitsOneAdd p (artinLevel K η n + 1) := by
  have hne : {k | ¬ artinImage K η n ≤ unitsOneAdd p (k + 1)}.Nonempty := by
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h
    obtain ⟨s, -, hs'⟩ := exists_level (p := p) (a := (a : ℤ_[p]ˣ)) (fun h' => ha1 (Subtype.ext h'))
    exact ⟨s, fun hle => hs' (hle a.2)⟩
  have hmem := Nat.sInf_mem hne
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_eq_succ_pred (artinLevel K η n) with h0 | h0
    · rw [h0, unitsOneAdd_zero]; exact le_top
    · have hlt : Nat.pred (artinLevel K η n) < artinLevel K η n := by omega
      have := Nat.notMem_of_lt_sInf hlt
      simp only [Set.mem_ofPred_eq, not_not] at this
      rw [h0]
      exact this
  · have hmem' : ¬ artinImage K η n ≤ unitsOneAdd p (artinLevel K η n + 1) := hmem
    exact IsConcreteLE.not_le_iff_exists.1 hmem'

theorem artinLevel_mono (hA : ∀ n, artinImage K η n ≠ ⊥) : Monotone (artinLevel K η) := by
  intro n n' hnn'
  obtain ⟨-, a, ha, ha'⟩ := artinLevel_spec (hA n')
  have h1 := (artinLevel_spec (hA n)).1 (artinImage_antitone η hnn' ha)
  by_contra hlt
  push Not at hlt
  exact ha' (unitsOneAdd_antitone (by omega) h1)

theorem artinLevel_add (hη : Continuous η) (hA : ∀ n, artinImage K η n ≠ ⊥) {n e : ℕ}
    (h2 : 2 ≤ artinLevel K η n)
    (hpow : (unitFiltrationUnits K n).map (powMonoidHom p) = unitFiltrationUnits K (n + e)) :
    artinLevel K η (n + e) = artinLevel K η n + 1 := by
  have heq := artinImage_add_eq_map_pow hη hpow
  obtain ⟨hle, a, ha, ha'⟩ := artinLevel_spec (hA n)
  obtain ⟨hle', b, hb, hb'⟩ := artinLevel_spec (hA (n + e))
  apply le_antisymm
  ·
    have hap : a ^ p ∈ artinImage K η (n + e) := by rw [heq]; exact ⟨a, ha, rfl⟩
    have hap' : a ^ p ∉ unitsOneAdd p (artinLevel K η n + 2) := fun h =>
      ha' (((pow_prime_mem_iff h2 (hle ha)).2).1 h)
    by_contra hlt
    push Not at hlt
    exact hap' (unitsOneAdd_antitone (by omega) (hle' hap))
  ·
    have hle2 : artinImage K η (n + e) ≤ unitsOneAdd p (artinLevel K η n + 1) := by
      rw [heq]
      rintro _ ⟨c, hc, rfl⟩
      exact (pow_prime_mem_iff h2 (hle hc)).1
    by_contra hlt
    push Not at hlt
    exact hb' (unitsOneAdd_antitone (by omega) (hle2 hb))

theorem artinImage_sup_unitsOneAdd {n : ℕ} (hA : artinImage K η n ≠ ⊥) (h2 : 2 ≤ artinLevel K η n)
    (k : ℕ) : artinImage K η n ⊔ unitsOneAdd p k = unitsOneAdd p (min (artinLevel K η n) k) := by
  obtain ⟨hle, a, ha, ha'⟩ := artinLevel_spec hA
  apply le_antisymm
  · exact sup_le (hle.trans (unitsOneAdd_antitone (min_le_left _ _)))
      (unitsOneAdd_antitone (min_le_right _ _))
  · intro b hb
    rcases le_total k (artinLevel K η n) with hk | hk
    · rw [min_eq_right hk] at hb
      exact Subgroup.mem_sup_right hb
    · rw [min_eq_left hk] at hb
      obtain ⟨j, hj⟩ := exists_mul_inv_pow_mem h2 (hle ha) ha' hb k
      have e : b = a ^ j * (b * (a ^ j)⁻¹) := by rw [mul_comm, inv_mul_cancel_right]
      rw [e]
      exact Subgroup.mul_mem_sup (pow_mem ha j) hj

theorem restrictNormalHom_mem_upperRamificationGroup_iff_level (hη : Continuous η) {k n : ℕ}
    (hA : artinImage K η n ≠ ⊥) (h2 : 2 ≤ artinLevel K η n)
    [FiniteDimensional K (charTower η k)] [IsAbelianGalois K (charTower η k)]
    (σ : Gal(PadicAlgCl p/K)) :
    AlgEquiv.restrictNormalHom (charTower η k) σ ∈ upperRamificationGroup K (charTower η k) n ↔
      η σ ∈ unitsOneAdd p (min (artinLevel K η n) k) := by
  rw [restrictNormalHom_mem_upperRamificationGroup_iff hη, artinImage_sup_unitsOneAdd hA h2]

theorem upperRamificationGroup_charTower_eq_map (hη : Continuous η) {k n : ℕ}
    (hA : artinImage K η n ≠ ⊥) (h2 : 2 ≤ artinLevel K η n)
    [FiniteDimensional K (charTower η k)] [IsAbelianGalois K (charTower η k)] :
    upperRamificationGroup K (charTower η k) n =
      (charTowerGal η (min (artinLevel K η n) k)).map
        (AlgEquiv.restrictNormalHom (charTower η k)) := by
  ext g
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := charTower η k)
    (E := PadicAlgCl p) g
  rw [restrictNormalHom_mem_upperRamificationGroup_iff_level hη hA h2]
  constructor
  · intro h
    exact ⟨σ, h, rfl⟩
  · rintro ⟨σ', hσ', heq⟩
    have h1 : AlgEquiv.restrictNormalHom (charTower η k) (σ'⁻¹ * σ) = 1 := by
      rw [map_mul, map_inv, heq, inv_mul_cancel]
    have h2' := (restrictNormalHom_charTower_eq_one_iff hη k _).1 h1
    have e : η σ = η σ' * η (σ'⁻¹ * σ) := by rw [map_mul, map_inv, mul_inv_cancel_left]
    rw [e]
    exact mul_mem hσ' (unitsOneAdd_antitone (min_le_right _ _) h2')


omit [FiniteDimensional ℚ_[p] K] in
theorem relIndex_charTowerGal {s t : ℕ} (hs : 2 ≤ s) (hst : s ≤ t) {a : ℤ_[p]ˣ} (haR : a ∈ η.range)
    (ha : a ∈ unitsOneAdd p s) (ha' : a ∉ unitsOneAdd p (s + 1)) :
    (charTowerGal η t).relIndex (charTowerGal η s) = p ^ (t - s) := by
  rw [charTowerGal, charTowerGal, Subgroup.relIndex_comap, Subgroup.map_comap_eq,
    ← Subgroup.inf_relIndex_right, inf_comm η.range, ← inf_assoc,
    inf_eq_left.2 (unitsOneAdd_antitone hst)]
  have h := relIndex_unitsOneAdd_inf hs η.range haR ha ha' (t - s)
  rwa [Nat.add_sub_cancel' hst] at h

theorem relIndex_upperRamificationGroup_charTower (hη : Continuous η)
    (hA : ∀ n, artinImage K η n ≠ ⊥) {k n' j : ℕ} (hn'j : n' ≤ j) (h2 : 2 ≤ artinLevel K η n')
    (hjk : artinLevel K η j ≤ k)
    [FiniteDimensional K (charTower η k)] [IsAbelianGalois K (charTower η k)] :
    (upperRamificationGroup K (charTower η k) j).relIndex
        (upperRamificationGroup K (charTower η k) n') =
      p ^ (artinLevel K η j - artinLevel K η n') := by
  have hmono := artinLevel_mono hA hn'j
  have h2j : 2 ≤ artinLevel K η j := h2.trans hmono
  rw [upperRamificationGroup_charTower_eq_map hη (hA j) h2j,
    upperRamificationGroup_charTower_eq_map hη (hA n') h2, Subgroup.relIndex_map_map,
    (charTower η k).restrictNormalHom_ker, fixingSubgroup_charTower hη, min_eq_left hjk,
    min_eq_left (hmono.trans hjk), sup_eq_left.2 (charTowerGal_antitone η hjk),
    sup_eq_left.2 (charTowerGal_antitone η (hmono.trans hjk))]
  obtain ⟨hle, a, ha, ha'⟩ := artinLevel_spec (hA n')
  exact relIndex_charTowerGal h2 hmono (Subgroup.map_le_range η _ ha) (hle ha) ha'

theorem card_upperRamificationGroup_charTower (hη : Continuous η)
    (hA : ∀ n, artinImage K η n ≠ ⊥) {k n' : ℕ} (h2 : 2 ≤ artinLevel K η n')
    (hk : artinLevel K η n' ≤ k)
    [FiniteDimensional K (charTower η k)] [IsAbelianGalois K (charTower η k)] :
    Nat.card (upperRamificationGroup K (charTower η k) n') = p ^ (k - artinLevel K η n') := by
  rw [upperRamificationGroup_charTower_eq_map hη (hA n') h2, min_eq_left hk,
    ← Subgroup.relIndex_bot_left, ← Subgroup.relIndex_comap, MonoidHom.comap_bot,
    (charTower η k).restrictNormalHom_ker, fixingSubgroup_charTower hη]
  obtain ⟨hle, a, ha, ha'⟩ := artinLevel_spec (hA n')
  exact relIndex_charTowerGal h2 hk (Subgroup.map_le_range η _ ha) (hle ha) ha'

theorem integral_eq_sum_of_eq_ceil {f : ℝ → ℝ} (hf : ∀ w, f w = f (⌈w⌉ : ℝ))
    (hint : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b) (N : ℕ) :
    ∫ w in (0 : ℝ)..N, f w = ∑ j ∈ Finset.Ioc 0 N, f j := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le N), ← ih,
      ← intervalIntegral.integral_add_adjacent_intervals (hint 0 N) (hint N ((N + 1 : ℕ) : ℝ))]
    congr 1
    have hc : ∫ w in (N : ℝ)..((N + 1 : ℕ) : ℝ), f w =
        ∫ _ in (N : ℝ)..((N + 1 : ℕ) : ℝ), f ((N + 1 : ℕ) : ℝ) := by
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun w hw => ?_)
      have hle : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ N
      rw [Set.uIoc_of_le hle] at hw
      rw [hf w]
      congr 1
      have : ⌈w⌉ = ((N + 1 : ℕ) : ℤ) := by
        rw [Int.ceil_eq_iff]
        push_cast at hw ⊢
        constructor <;> linarith [hw.1, hw.2]
      rw [this]
      norm_cast
    rw [Nat.cast_succ] at hc ⊢
    rw [hc, intervalIntegral.integral_const, smul_eq_mul]
    ring

theorem sum_zpow_block_le (μ : ℕ → ℕ) (hμ : Monotone μ) {e n₀ : ℕ}
    (hper : ∀ n, n₀ ≤ n → μ (n + e) = μ n + 1) {N k : ℕ} (hN : k + 1 ≤ μ (N + 1)) {b : ℝ}
    (hb : 1 ≤ b) : ∀ q : ℕ, n₀ + e * q ≤ N →
      (e : ℝ) * ∑ i ∈ Finset.range q, b ^ ((k : ℤ) - i) ≤
        ∑ j ∈ Finset.Ioc (N - e * q) N, b ^ (μ j : ℤ)
  | 0, _ => by simp
  | q + 1, hq => by
    rw [show e * (q + 1) = e * q + e by ring] at hq ⊢
    have ih := sum_zpow_block_le μ hμ hper hN hb q (by omega)

    have hiter : ∀ i j, n₀ ≤ j → μ (j + e * i) = μ j + i := by
      intro i
      induction i with
      | zero => simp
      | succ i ihi =>
        intro j hj
        rw [mul_add, mul_one, ← add_assoc, hper _ (by omega), ihi j hj, add_assoc]
    have hsplit : Finset.Ioc (N - (e * q + e)) N =
        Finset.Ioc (N - (e * q + e)) (N - e * q) ∪ Finset.Ioc (N - e * q) N := by
      rw [Finset.Ioc_union_Ioc_eq_Ioc (by omega) (by omega)]
    have hdisj : Disjoint (Finset.Ioc (N - (e * q + e)) (N - e * q)) (Finset.Ioc (N - e * q) N) :=
      Finset.Ioc_disjoint_Ioc_of_le le_rfl
    rw [hsplit, Finset.sum_union hdisj, Finset.sum_range_succ, mul_add, add_comm]
    refine add_le_add ?_ ih

    have hcard : (Finset.Ioc (N - (e * q + e)) (N - e * q)).card = e := by
      rw [Nat.card_Ioc]; omega
    have hconst : (∑ _j ∈ Finset.Ioc (N - (e * q + e)) (N - e * q), b ^ ((k : ℤ) - q)) =
        (e : ℝ) * b ^ ((k : ℤ) - q) := by
      rw [Finset.sum_const, hcard, nsmul_eq_mul]
    have hpoint : ∀ j ∈ Finset.Ioc (N - (e * q + e)) (N - e * q),
        b ^ ((k : ℤ) - q) ≤ b ^ (μ j : ℤ) := by
      intro j hj
      rw [Finset.mem_Ioc] at hj
      refine zpow_le_zpow_right₀ hb ?_
      have h1 : μ (j + e * q) = μ j + q := hiter q j (by omega)
      have h2 : k + 1 ≤ μ (j + e * q + e) := hN.trans (hμ (by omega))
      rw [hper _ (by omega), h1] at h2
      omega
    rw [← hconst]
    exact Finset.sum_le_sum hpoint

theorem artinLevel_add_mul {n₀ e : ℕ}
    (hper : ∀ n, n₀ ≤ n → artinLevel K η (n + e) = artinLevel K η n + 1) (i : ℕ) :
    artinLevel K η (n₀ + e * i) = artinLevel K η n₀ + i := by
  induction i with
  | zero => simp
  | succ i ih => rw [mul_add, mul_one, ← add_assoc, hper _ (by omega), ih, add_assoc]

theorem exists_last_artinLevel_le (hA : ∀ n, artinImage K η n ≠ ⊥) {n₀ e : ℕ}
    (hper : ∀ n, n₀ ≤ n → artinLevel K η (n + e) = artinLevel K η n + 1) {k : ℕ}
    (hk : artinLevel K η n₀ ≤ k) :
    ∃ N, artinLevel K η N ≤ k ∧ k + 1 ≤ artinLevel K η (N + 1) ∧
      n₀ + e * (k - artinLevel K η n₀) ≤ N := by
  have hmono := artinLevel_mono hA
  have hiter := artinLevel_add_mul hper
  have hex : ∃ n, k < artinLevel K η n :=
    ⟨n₀ + e * (k - artinLevel K η n₀ + 1), by rw [hiter]; omega⟩
  classical
  have hF : k < artinLevel K η (Nat.find hex) := Nat.find_spec hex
  have hF0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hF
    have := hmono (Nat.zero_le n₀)
    omega
  obtain ⟨N, hNF⟩ : ∃ N, N + 1 = Nat.find hex := ⟨Nat.find hex - 1, by omega⟩
  refine ⟨N, ?_, by rw [hNF]; exact hF, ?_⟩
  · have := Nat.find_min hex (show N < Nat.find hex by omega)
    omega
  · by_contra hlt
    push Not at hlt
    have := hmono (show Nat.find hex ≤ n₀ + e * (k - artinLevel K η n₀) by omega)
    rw [hiter] at this
    omega

theorem le_herbrandPsi_div_ramificationIndex (hη : Continuous η) (hA : ∀ n, artinImage K η n ≠ ⊥)
    {n' n₀ e : ℕ} (hn' : n' ≤ n₀) (h2 : 2 ≤ artinLevel K η n')
    (hper : ∀ n, n₀ ≤ n → artinLevel K η (n + e) = artinLevel K η n + 1)
    {k N : ℕ} (hNk : artinLevel K η N ≤ k) (hN1 : k + 1 ≤ artinLevel K η (N + 1))
    (hNq : n₀ + e * (k - artinLevel K η n₀) ≤ N)
    [FiniteDimensional K (charTower η (k + 1))] [IsAbelianGalois K (charTower η (k + 1))] :
    (e : ℝ) / p * ∑ i ∈ Finset.range (k - artinLevel K η n₀), (p : ℝ) ^ (-(i : ℤ)) ≤
      herbrandPsi K (charTower η (k + 1)) N / ramificationIndex K (charTower η (k + 1)) := by
  have hmono := artinLevel_mono hA
  have hn'N : n' ≤ N := le_trans hn' (le_trans (Nat.le_add_right _ _) hNq)
  have hsk : artinLevel K η n' ≤ k := (hmono hn'N).trans hNk

  have hn'0 : upperRamificationGroup K (charTower η (k + 1)) n' ≤
      lowerRamificationGroup K (charTower η (k + 1)) 0 := by
    rw [← upperRamificationGroup_zero]
    exact upperRamificationGroup_antitone K _ (Nat.cast_nonneg n')
  obtain ⟨c, hc⟩ : ∃ c, (upperRamificationGroup K (charTower η (k + 1)) n').relIndex
      (lowerRamificationGroup K (charTower η (k + 1)) 0) = c := ⟨_, rfl⟩
  have hE : ramificationIndex K (charTower η (k + 1)) = c * p ^ (k + 1 - artinLevel K η n') := by
    have hcard : Nat.card (lowerRamificationGroup K (charTower η (k + 1)) 0) =
        ramificationIndex K (charTower η (k + 1)) :=
      card_lowerRamificationGroup_zero K (charTower η (k + 1))
    rw [← hcard, ← Subgroup.relIndex_bot_left,
      ← Subgroup.relIndex_mul_relIndex _ _ _ bot_le hn'0, Subgroup.relIndex_bot_left,
      card_upperRamificationGroup_charTower hη hA h2 (by omega), hc, mul_comm]

  have hψsum : herbrandPsi K (charTower η (k + 1)) N =
      ∑ j ∈ Finset.Ioc 0 N, (upperIndex K (charTower η (k + 1)) j : ℝ) := by
    rw [herbrandPsi_eq_integral (Nat.cast_nonneg N)]
    refine integral_eq_sum_of_eq_ceil (fun w => ?_) (fun a b => intervalIntegrable_upperIndex a b) N
    simp only [upperIndex]
    rw [upperRamificationGroup_eq_ceil (L := charTower η (k + 1)) w]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  have hterm : ∀ j ∈ Finset.Ioc (N - e * (k - artinLevel K η n₀)) N,
      (upperIndex K (charTower η (k + 1)) j : ℝ) =
        (c : ℝ) * (p : ℝ) ^ (-(artinLevel K η n' : ℤ)) * (p : ℝ) ^ (artinLevel K η j : ℤ) := by
    intro j hj
    rw [Finset.mem_Ioc] at hj
    have hn'j : n' ≤ j := by omega
    have hjk : artinLevel K η j ≤ k + 1 := by have := hmono hj.2; omega
    have hsj : artinLevel K η n' ≤ artinLevel K η j := hmono hn'j
    rw [upperIndex, ← Subgroup.relIndex_mul_relIndex _ _ _
      (upperRamificationGroup_antitone K _ (by exact_mod_cast hn'j)) hn'0,
      relIndex_upperRamificationGroup_charTower hη hA hn'j h2 hjk, hc]
    push_cast
    rw [← zpow_natCast, Nat.cast_sub hsj, zpow_sub₀ hp0.ne', zpow_neg]
    ring
  have hψlow : (c : ℝ) * (p : ℝ) ^ (-(artinLevel K η n' : ℤ)) *
      ((e : ℝ) * ∑ i ∈ Finset.range (k - artinLevel K η n₀), (p : ℝ) ^ ((k : ℤ) - i)) ≤
        herbrandPsi K (charTower η (k + 1)) N := by
    rw [hψsum]
    calc (c : ℝ) * (p : ℝ) ^ (-(artinLevel K η n' : ℤ)) *
          ((e : ℝ) * ∑ i ∈ Finset.range (k - artinLevel K η n₀), (p : ℝ) ^ ((k : ℤ) - i))
        ≤ (c : ℝ) * (p : ℝ) ^ (-(artinLevel K η n' : ℤ)) *
            ∑ j ∈ Finset.Ioc (N - e * (k - artinLevel K η n₀)) N, (p : ℝ) ^ (artinLevel K η j : ℤ) :=
          mul_le_mul_of_nonneg_left
            (sum_zpow_block_le (artinLevel K η) hmono hper hN1 hp1 _ hNq) (by positivity)
      _ = ∑ j ∈ Finset.Ioc (N - e * (k - artinLevel K η n₀)) N,
            (upperIndex K (charTower η (k + 1)) j : ℝ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j hj => (hterm j hj).symm
      _ ≤ ∑ j ∈ Finset.Ioc 0 N, (upperIndex K (charTower η (k + 1)) j : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_left (Nat.zero_le _))
            (fun _ _ _ => Nat.cast_nonneg _)
  have hE0 : (0 : ℝ) < ramificationIndex K (charTower η (k + 1)) := by
    exact_mod_cast ramificationIndex_pos K (charTower η (k + 1))
  rw [le_div_iff₀ hE0]
  refine le_trans (le_of_eq ?_) hψlow
  rw [hE]
  push_cast
  have hsum : ∑ i ∈ Finset.range (k - artinLevel K η n₀), (p : ℝ) ^ ((k : ℤ) - i) =
      (p : ℝ) ^ (k : ℤ) * ∑ i ∈ Finset.range (k - artinLevel K η n₀), (p : ℝ) ^ (-(i : ℤ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← zpow_add₀ hp0.ne']
    ring_nf
  rw [hsum, ← zpow_natCast (p : ℝ) (k + 1 - artinLevel K η n'), Nat.cast_sub (by omega),
    zpow_sub₀ hp0.ne', zpow_neg]
  push_cast
  rw [zpow_add₀ hp0.ne', zpow_one]
  field_simp

theorem nrm_sub_le_of_mem_unitsOneAdd (hη : Continuous η) (hA : ∀ n, artinImage K η n ≠ ⊥)
    {n' n₀ e : ℕ} (hn' : n' ≤ n₀) (h2 : 2 ≤ artinLevel K η n')
    (hper : ∀ n, n₀ ≤ n → artinLevel K η (n + e) = artinLevel K η n + 1)
    {k : ℕ} (hk : artinLevel K η n₀ ≤ k) {σ : Gal(PadicAlgCl p/K)} (hσ : η σ ∈ unitsOneAdd p k)
    {y : PadicAlgCl p} (hy : y ∈ charTower η (k + 1)) :
    nrm K (σ y - y) ≤ baseUnifNrm K (PadicAlgCl p) ^ ((e : ℝ) / p *
      ∑ i ∈ Finset.range (k - artinLevel K η n₀), (p : ℝ) ^ (-(i : ℤ))) * nrm K y := by
  have : FiniteDimensional K (charTower η (k + 1)) := finiteDimensional_charTower hη (k + 1)
  have : IsAbelianGalois K (charTower η (k + 1)) := isAbelianGalois_charTower hη (k + 1)
  have hmono := artinLevel_mono hA
  obtain ⟨N, hNk, hN1, hNq⟩ := exists_last_artinLevel_le hA hper hk
  have hn'N : n' ≤ N := le_trans hn' (le_trans (Nat.le_add_right _ _) hNq)
  have h2N : 2 ≤ artinLevel K η N := h2.trans (hmono hn'N)
  have hσN : AlgEquiv.restrictNormalHom (charTower η (k + 1)) σ ∈
      upperRamificationGroup K (charTower η (k + 1)) N := by
    rw [restrictNormalHom_mem_upperRamificationGroup_iff_level hη (hA N) h2N,
      min_eq_left (by omega)]
    exact unitsOneAdd_antitone hNk hσ
  have hψ0 : 0 ≤ herbrandPsi K (charTower η (k + 1)) N := by
    rw [← herbrandPsi_zero (K := K) (L := charTower η (k + 1))]
    exact herbrandPsi_strictMono.monotone (Nat.cast_nonneg N)
  obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = ⌈herbrandPsi K (charTower η (k + 1)) N⌉ :=
    ⟨_, Int.toNat_of_nonneg (Int.ceil_nonneg hψ0)⟩
  have hmem : AlgEquiv.restrictNormalHom (charTower η (k + 1)) σ ∈
      lowerRamificationGroup K (charTower η (k + 1)) (i : ℤ) := by
    rw [hi]
    exact hσN
  have h1 := nrm_sub_le_of_mem_lowerRamificationGroup (charTower η (k + 1)) hmem ⟨y, hy⟩
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (nrm_nonneg _))
  have hX := le_herbrandPsi_div_ramificationIndex hη hA hn' h2 hper hNk hN1 hNq
  have hu0 : 0 < unifNrm (charTower η (k + 1)) := unifNrm_pos _
  have hu1 : unifNrm (charTower η (k + 1)) < 1 := unifNrm_lt_one _
  have huE : unifNrm (charTower η (k + 1)) ^ ramificationIndex K (charTower η (k + 1)) =
      baseUnifNrm K (PadicAlgCl p) := unifNrm_pow_ramificationIndex _
  have hE0 : (0 : ℝ) < ramificationIndex K (charTower η (k + 1)) := by
    exact_mod_cast ramificationIndex_pos K (charTower η (k + 1))
  calc unifNrm (charTower η (k + 1)) ^ i = unifNrm (charTower η (k + 1)) ^ (i : ℝ) :=
        (Real.rpow_natCast _ i).symm
    _ ≤ unifNrm (charTower η (k + 1)) ^ herbrandPsi K (charTower η (k + 1)) N := by
        refine Real.rpow_le_rpow_of_exponent_ge hu0 hu1.le ?_
        have : ((⌈herbrandPsi K (charTower η (k + 1)) N⌉ : ℤ) : ℝ) = (i : ℝ) := by
          rw [← hi]; norm_cast
        rw [← this]
        exact Int.le_ceil _
    _ = baseUnifNrm K (PadicAlgCl p) ^
          (herbrandPsi K (charTower η (k + 1)) N / ramificationIndex K (charTower η (k + 1))) := by
        rw [← huE, ← Real.rpow_natCast, ← Real.rpow_mul hu0.le]
        congr 1
        field_simp
    _ ≤ baseUnifNrm K (PadicAlgCl p) ^ ((e : ℝ) / p *
          ∑ i ∈ Finset.range (k - artinLevel K η n₀), (p : ℝ) ^ (-(i : ℤ))) :=
        Real.rpow_le_rpow_of_exponent_ge baseUnifNrm_pos
          (by rw [← huE]; exact pow_le_one₀ hu0.le hu1.le) hX

end SenTateChar

end GroundTheory.PAdicHodge
