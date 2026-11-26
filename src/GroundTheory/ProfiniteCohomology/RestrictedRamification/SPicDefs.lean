module

public import Mathlib

@[expose] public section

section -- merged from GroundTheory.ProfiniteCohomology.RestrictedRamification.SPicDefs
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {F : Type*} [Field F] [NumberField F]

noncomputable def ordAt (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) : ℤ :=
  -Multiplicative.toAdd (v.valuationOfNeZero x)

theorem ordAt_mul (v : HeightOneSpectrum (𝓞 F)) (x y : Fˣ) :
    ordAt v (x * y) = ordAt v x + ordAt v y := by
  simp only [ordAt, map_mul, toAdd_mul, neg_add]

theorem ordAt_one (v : HeightOneSpectrum (𝓞 F)) : ordAt v (1 : Fˣ) = 0 := by
  simp [ordAt]

theorem ordAt_inv (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) : ordAt v x⁻¹ = -ordAt v x := by
  simp [ordAt]

theorem ordAt_eq_zero_iff (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) :
    ordAt v x = 0 ↔ v.valuation F (x : F) = 1 := by
  rw [ordAt, neg_eq_zero, ← valuationOfNeZero_eq, ← WithZero.coe_one, WithZero.coe_inj,
    ← toAdd_one]
  exact Multiplicative.toAdd.injective.eq_iff

theorem valuation_eq_exp_neg_ordAt (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) :
    v.valuation F (x : F) = WithZero.exp (-ordAt v x) := by
  rw [ordAt, neg_neg, ← valuationOfNeZero_eq]
  rfl

theorem finite_ordAt_ne_zero (x : Fˣ) : {v : HeightOneSpectrum (𝓞 F) | ordAt v x ≠ 0}.Finite := by
  refine ((Support.finite (𝓞 F) (x : F)).union (Support.finite (𝓞 F) ((x⁻¹ : Fˣ) : F))).subset ?_
  intro v hv
  have hv' : v.valuation F (x : F) ≠ 1 := fun h => hv ((ordAt_eq_zero_iff v x).2 h)
  rcases lt_or_gt_of_ne hv' with h | h
  · right
    change 1 < v.valuation F ((x⁻¹ : Fˣ) : F)
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact one_lt_inv₀ (lt_of_le_of_ne zero_le (((map_ne_zero (v.valuation F)).2 x.ne_zero)).symm)
      |>.2 h
  · left
    exact h

variable (S : Set (HeightOneSpectrum (𝓞 F)))

abbrev sDivisor := {v : HeightOneSpectrum (𝓞 F) // v ∉ S} →₀ ℤ

noncomputable def divS : Additive Fˣ →+ sDivisor S where
  toFun x := Finsupp.ofSupportFinite (fun v => ordAt v.1 (Additive.toMul x)) (by
    refine ((finite_ordAt_ne_zero (Additive.toMul x)).preimage
      Subtype.val_injective.injOn).subset ?_
    intro v hv
    exact hv)
  map_zero' := by
    ext v
    simp [Finsupp.ofSupportFinite_coe, ordAt_one]
  map_add' x y := by
    ext v
    simp [Finsupp.ofSupportFinite_coe, toMul_add, ordAt_mul]

theorem divS_apply (x : Additive Fˣ) (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) :
    divS S x v = ordAt v.1 (Additive.toMul x) :=
  rfl

abbrev sPic := sDivisor S ⧸ (divS S).range

noncomputable abbrev sPicMk : sDivisor S →+ sPic S := QuotientAddGroup.mk' (divS S).range

theorem sPicMk_eq_zero_iff (D : sDivisor S) : sPicMk S D = 0 ↔ ∃ x : Fˣ, divS S (Additive.ofMul x) = D := by
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range]
  exact ⟨fun ⟨x, hx⟩ => ⟨Additive.toMul x, hx⟩, fun ⟨x, hx⟩ => ⟨Additive.ofMul x, hx⟩⟩

end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.RestrictedRamification.MaxUnramifiedOutside
namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain

variable {F : Type*} [Field F]

section Places

variable {L : Type*} [Field L] [Algebra F L]

def placesOver (S : Set (HeightOneSpectrum (𝓞 F))) : Set (HeightOneSpectrum (𝓞 L)) :=
  {w | ∃ v ∈ S, w.asIdeal.LiesOver v.asIdeal}

end Places

variable {Ω : Type*} [Field Ω] [Algebra F Ω]

def IsUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 F))) (E : IntermediateField F Ω) : Prop :=
  ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal


variable (F Ω) in
noncomputable def maxUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 F))) :
    IntermediateField F Ω :=
  ⨆ (E : IntermediateField F Ω) (_ : FiniteDimensional F E) (_ : IsUnramifiedOutside S E), E


variable (F Ω) in
abbrev galUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 F))) :=
  Gal(maxUnramifiedOutside (F := F) (Ω := Ω) S / F)

end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.RestrictedRamification.Ramification
namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain

section Tower

variable {F L M : Type*} [Field F] [Field L] [Field M] [NumberField F] [NumberField L]
  [NumberField M] [Algebra F L] [Algebra L M] [Algebra F M] [IsScalarTower F L M]

theorem isUnramifiedAt_tower_iff (Q : Ideal (𝓞 M)) [Q.IsPrime] :
    Algebra.IsUnramifiedAt (𝓞 F) Q ↔
      Algebra.IsUnramifiedAt (𝓞 F) (Q.under (𝓞 L)) ∧ Algebra.IsUnramifiedAt (𝓞 L) Q := by
  rw [← Ideal.ramificationIdx_eq_one_iff, ← Ideal.ramificationIdx_eq_one_iff,
    ← Ideal.ramificationIdx_eq_one_iff, Ideal.ramificationIdx_tower (q := Q.under (𝓞 L))]
  exact mul_eq_one

end Tower

section Inertia

variable {F E M : Type*} [Field F] [Field E] [Field M] [Algebra F E] [Algebra E M] [Algebra F M]
  [IsScalarTower F E M]

theorem restrictScalars_mem_inertia_iff (Q : Ideal (𝓞 M)) (σ : Gal(M/E)) :
    AlgEquiv.restrictScalarsHom F σ ∈ Q.inertia Gal(M/F) ↔ σ ∈ Q.inertia Gal(M/E) :=
  Iff.rfl

theorem mem_range_restrictScalarsHom_iff (σ : Gal(M/F)) :
    σ ∈ (AlgEquiv.restrictScalarsHom F : Gal(M/E) →* Gal(M/F)).range ↔
      ∀ x : E, σ (algebraMap E M x) = algebraMap E M x := by
  constructor
  · rintro ⟨τ, rfl⟩ x
    exact τ.commutes x
  · intro h
    exact ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) h, AlgEquiv.ext fun _ => rfl⟩

variable [NumberField F] [NumberField E] [NumberField M] [IsGalois F M]

theorem isUnramifiedAt_under_iff_inertia (Q : Ideal (𝓞 M)) [Q.IsPrime] :
    Algebra.IsUnramifiedAt (𝓞 F) (Q.under (𝓞 E)) ↔
      ∀ σ ∈ Q.inertia Gal(M/F), ∀ x : E, σ (algebraMap E M x) = algebraMap E M x := by
  have : IsGaloisGroup Gal(M/F) (𝓞 F) (𝓞 M) := IsGaloisGroup.of_isFractionRing _ _ _ F M
  have : IsGalois E M := IsGalois.tower_top_of_isGalois F E M
  have : IsGaloisGroup Gal(M/E) (𝓞 E) (𝓞 M) := IsGaloisGroup.of_isFractionRing _ _ _ E M
  have cF : Nat.card (Q.inertia Gal(M/F)) = Q.ramificationIdx (𝓞 F) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (Q.under (𝓞 F)) Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under (𝓞 F)) Q Gal(M/F)]
  have cE : Nat.card (Q.inertia Gal(M/E)) = Q.ramificationIdx (𝓞 E) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (Q.under (𝓞 E)) Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under (𝓞 E)) Q Gal(M/E)]
  have htow : Q.ramificationIdx (𝓞 F) =
      (Q.under (𝓞 E)).ramificationIdx (𝓞 F) * Q.ramificationIdx (𝓞 E) :=
    Ideal.ramificationIdx_tower (q := Q.under (𝓞 E)) (r := Q)
  set φ : Gal(M/E) →* Gal(M/F) := AlgEquiv.restrictScalarsHom F with hφ
  have hinj : Function.Injective φ := AlgEquiv.restrictScalarsHom_injective F
  have hmap : (Q.inertia Gal(M/E)).map φ = Q.inertia Gal(M/F) ⊓ φ.range := by
    ext σ
    simp only [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range]
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      exact ⟨(restrictScalars_mem_inertia_iff Q τ).2 hτ, τ, rfl⟩
    · rintro ⟨hσ, τ, rfl⟩
      exact ⟨τ, (restrictScalars_mem_inertia_iff Q τ).1 hσ, rfl⟩
  have hcardmap : Nat.card ((Q.inertia Gal(M/E)).map φ) = Nat.card (Q.inertia Gal(M/E)) :=
    Subgroup.card_map_of_injective hinj
  have hpos : 0 < Nat.card (Q.inertia Gal(M/E)) := Nat.card_pos
  rw [← Ideal.ramificationIdx_eq_one_iff]
  constructor
  · intro h1 σ hσ
    have hc : Nat.card (Q.inertia Gal(M/F) ⊓ φ.range : Subgroup Gal(M/F)) ≥
        Nat.card (Q.inertia Gal(M/F)) := by
      rw [← hmap, hcardmap, cF, cE, htow, h1, one_mul]
    have heq := Subgroup.eq_of_le_of_card_ge (inf_le_left : Q.inertia Gal(M/F) ⊓ φ.range ≤ _) hc
    have hσ' : σ ∈ Q.inertia Gal(M/F) ⊓ φ.range := by rw [heq]; exact hσ
    exact (mem_range_restrictScalarsHom_iff σ).1 hσ'.2
  · intro h
    have hle : Q.inertia Gal(M/F) ≤ φ.range := fun σ hσ =>
      (mem_range_restrictScalarsHom_iff σ).2 (h σ hσ)
    have hmap' : (Q.inertia Gal(M/E)).map φ = Q.inertia Gal(M/F) := by
      rw [hmap, inf_eq_left.2 hle]
    have hc : (Q.under (𝓞 E)).ramificationIdx (𝓞 F) * Q.ramificationIdx (𝓞 E) =
        1 * Q.ramificationIdx (𝓞 E) := by
      rw [← htow, ← cF, ← cE, ← hmap', hcardmap, one_mul]
    exact Nat.eq_of_mul_eq_mul_right (cE ▸ hpos) hc

end Inertia

end GroundTheory.ProfCoh
end
