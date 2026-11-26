module

public import GroundTheory.LocalFields.AbstractLocalReciprocity.NormFormula
public import GroundTheory.LocalFields.AbstractLocalReciprocity.Frobenius

@[expose] public section

section -- merged from GroundTheory.LocalFields.AbstractLocalReciprocity.Reciprocity
section -- merged from GroundTheory.LocalFields.AbstractLocalReciprocity.Unramified
namespace GroundTheory.LocalField.Abstract

section Unramified

variable {G : Type*} [Group G] (d : G →* Multiplicative ℤ̂)

def IsUnramified (K L : Subgroup G) : Prop :=
  relRamificationIndex d K L = 1

variable {d}

theorem isUnramified_iff {K L : Subgroup G} : IsUnramified d K L ↔ K ⊓ d.ker ≤ L := by
  rw [IsUnramified, relRamificationIndex, Subgroup.relIndex_eq_one, inf_comm]

theorem relIndex_eq_relInertiaDegree {K L : Subgroup G} (hLK : L ≤ K) (hu : K ⊓ d.ker ≤ L) :
    L.relIndex K = relInertiaDegree d K L := by
  rw [relIndex_eq_mul (d := d) hLK, (isUnramified_iff.2 hu : relRamificationIndex d K L = 1), one_mul]

theorem mem_iff_map_mem_of_unramified {K L : Subgroup G} (hLK : L ≤ K) (hu : K ⊓ d.ker ≤ L)
    {σ : G} (hσ : σ ∈ K) : σ ∈ L ↔ d σ ∈ L.map d := by
  refine ⟨fun h => ⟨σ, h, rfl⟩, ?_⟩
  rintro ⟨τ, hτ, hτσ⟩
  have h : τ⁻¹ * σ ∈ L := hu (Subgroup.mem_inf.2 ⟨K.mul_mem (K.inv_mem (hLK hτ)) hσ,
    MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, hτσ, inv_mul_cancel])⟩)
  simpa using L.mul_mem hτ h

theorem normal_of_unramified {K L : Subgroup G} (hLK : L ≤ K) (hu : K ⊓ d.ker ≤ L) :
    (L.subgroupOf K).Normal := by
  have h : L.subgroupOf K = (L.map d).comap (d.comp K.subtype) := by
    ext σ
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact mem_iff_map_mem_of_unramified hLK hu σ.2
  rw [h]
  exact Subgroup.Normal.comap inferInstance _

end Unramified

namespace ClassFieldData

open ProfiniteInteger

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A] (D : ClassFieldData G A)

section Frobenius

variable {K L : OpenSubgroup G}

theorem exists_pow_mul_mem_of_unramified (hLK : L ≤ K) (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    {φ : (K : Subgroup G)} (hφ : D.relDeg K φ = Multiplicative.ofAdd 1) (τ : (K : Subgroup G)) :
    ∃ m : ℕ, ((φ ^ m)⁻¹ * τ : G) ∈ (L : Subgroup G) := by
  set n : ℕ+ := ⟨relInertiaDegree D.deg K L, Nat.pos_of_ne_zero (D.relInertiaDegree_ne_zero hLK)⟩
  set x : ℤ̂ := Multiplicative.toAdd (D.relDeg K τ)
  set m : ℕ := (proj n x).val
  have hx : x - (m : ℤ̂) ∈ multiples n := by
    rw [← proj_eq_zero_iff, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨w, hw⟩ := mem_multiples.1 hx
  obtain ⟨ρ, hρ, hρw⟩ := (D.mem_map_relDeg_iff hLK).2 ⟨Multiplicative.ofAdd w, rfl⟩
  refine ⟨m, ?_⟩
  have hdeg : D.relDeg K (ρ⁻¹ * ((φ ^ m)⁻¹ * τ)) = 1 := by
    rw [map_mul, map_mul, map_inv, map_inv, map_pow, hφ, hρw]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_inv, toAdd_pow, toAdd_ofAdd, toAdd_one]
    have hw' : relInertiaDegree D.deg K L • w = x - m := hw.symm
    rw [hw', nsmul_one]
    abel
  have hker : ((ρ⁻¹ * ((φ ^ m)⁻¹ * τ) : (K : Subgroup G)) : G) ∈ (K : Subgroup G) ⊓ D.deg.ker := by
    refine Subgroup.mem_inf.2 ⟨Subtype.coe_prop _, MonoidHom.mem_ker.2 ?_⟩
    rw [← relDeg_pow, hdeg, one_pow]
  have h := (L : Subgroup G).mul_mem (Subgroup.mem_subgroupOf.1 hρ) (hu hker)
  simpa using h

theorem zpowers_eq_top_of_unramified (hLK : L ≤ K) (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    [((L : Subgroup G).subgroupOf K).Normal]
    {φ : (K : Subgroup G)} (hφ : D.relDeg K φ = Multiplicative.ofAdd 1) :
    Subgroup.zpowers ((φ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) = ⊤ := by
  refine eq_top_iff.2 fun q _ => ?_
  induction q using QuotientGroup.induction_on with
  | H τ =>
    obtain ⟨m, hm⟩ := D.exists_pow_mul_mem_of_unramified hLK hu hφ τ
    refine ⟨m, ?_⟩
    change ((φ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) ^ (m : ℤ) = τ
    rw [zpow_natCast, ← QuotientGroup.mk_pow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hm

theorem isCyclic_of_unramified (hLK : L ≤ K) (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    [((L : Subgroup G).subgroupOf K).Normal] :
    IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
  obtain ⟨φ, hφ⟩ := D.relDeg_surjective K (Multiplicative.ofAdd 1)
  exact isCyclic_iff_exists_zpowers_eq_top.2 ⟨_, D.zpowers_eq_top_of_unramified hLK hu hφ⟩

end Frobenius

section TateZero

variable {K L : OpenSubgroup G}

noncomputable def valuationMod (K : OpenSubgroup G) (n : ℕ+) :
    fixedModule A (K : Subgroup G) →* Multiplicative (ZMod n) :=
  (AddMonoidHom.toMultiplicative (proj n).toAddMonoidHom).comp (D.valuation K)

theorem valuationMod_apply (K : OpenSubgroup G) (n : ℕ+) (a : fixedModule A (K : Subgroup G)) :
    D.valuationMod K n a = Multiplicative.ofAdd (proj n (Multiplicative.toAdd (D.valuation K a))) :=
  rfl

theorem valuationMod_surjective (K : OpenSubgroup G) (n : ℕ+) :
    Function.Surjective (D.valuationMod K n) := by
  intro z
  have h : Multiplicative.ofAdd ((Multiplicative.toAdd z).val : ℤ̂) ∈ (D.valuation K).range := by
    rw [range_valuation]
    exact_mod_cast D.intCast_mem_range_val ((Multiplicative.toAdd z).val : ℤ)
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ?_⟩
  rw [valuationMod_apply, ha, toAdd_ofAdd, map_natCast, ZMod.natCast_zmod_val, ofAdd_toAdd]

noncomputable def relInertiaDegreePNat (hLK : L ≤ K) : ℕ+ :=
  ⟨relInertiaDegree D.deg K L, Nat.pos_of_ne_zero (D.relInertiaDegree_ne_zero hLK)⟩

@[simp] theorem coe_relInertiaDegreePNat (hLK : L ≤ K) :
    (D.relInertiaDegreePNat hLK : ℕ) = relInertiaDegree D.deg K L :=
  rfl

theorem range_norm_le_ker_valuationMod (hLK : L ≤ K) :
    (norm A (K : Subgroup G) (L : Subgroup G)).range ≤
      (D.valuationMod K (D.relInertiaDegreePNat hLK)).ker := by
  rintro _ ⟨a, rfl⟩
  rw [MonoidHom.mem_ker, valuationMod_apply, D.valuation_norm hLK, toAdd_pow, map_nsmul,
    nsmul_eq_mul]
  change Multiplicative.ofAdd (((D.relInertiaDegreePNat hLK : ℕ) : ZMod (D.relInertiaDegreePNat hLK)) *
    _) = 1
  rw [ZMod.natCast_self, zero_mul, ofAdd_zero]

noncomputable def tateZeroVal (hLK : L ≤ K) :
    tateZero A (K : Subgroup G) (L : Subgroup G) →*
      Multiplicative (ZMod (D.relInertiaDegreePNat hLK)) :=
  QuotientGroup.lift _ (D.valuationMod K (D.relInertiaDegreePNat hLK))
    (D.range_norm_le_ker_valuationMod hLK)

theorem tateZeroVal_mk (hLK : L ≤ K) (a : fixedModule A (K : Subgroup G)) :
    D.tateZeroVal hLK (a : tateZero A (K : Subgroup G) (L : Subgroup G)) =
      D.valuationMod K (D.relInertiaDegreePNat hLK) a :=
  rfl

theorem tateZeroVal_surjective (hLK : L ≤ K) : Function.Surjective (D.tateZeroVal hLK) := by
  intro z
  obtain ⟨a, ha⟩ := D.valuationMod_surjective K (D.relInertiaDegreePNat hLK) z
  exact ⟨a, ha⟩

theorem tateZeroVal_bijective (hax : ClassFieldAxiom G A) (hLK : L ≤ K)
    (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L) : Function.Bijective (D.tateZeroVal hLK) := by
  have := normal_of_unramified (d := D.deg) hLK hu
  have hcyc := D.isCyclic_of_unramified hLK hu
  have hcard := (hax K L hLK hcyc).1
  rw [relIndex_eq_relInertiaDegree hLK hu] at hcard
  have : Finite (tateZero A (K : Subgroup G) (L : Subgroup G)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact D.relInertiaDegree_ne_zero hLK)
  refine (D.tateZeroVal_surjective hLK).bijective_of_nat_card_le ?_
  rw [hcard, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, coe_relInertiaDegreePNat]

end TateZero

section Units

variable {K L : OpenSubgroup G}

theorem norm_mem_units (hLK : L ≤ K) {a : fixedModule A (L : Subgroup G)} (ha : a ∈ D.units L) :
    norm A (K : Subgroup G) (L : Subgroup G) a ∈ D.units K := by
  rw [D.mem_units, D.valuation_norm hLK, D.mem_units.1 ha, one_pow]

theorem units_eq_map_norm (hax : ClassFieldAxiom G A) (hLK : L ≤ K)
    (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L) :
    D.units K = (D.units L).map (norm A (K : Subgroup G) (L : Subgroup G)) := by
  refine le_antisymm ?_ ?_
  · intro u hU
    have h1 : D.tateZeroVal hLK (u : tateZero A (K : Subgroup G) (L : Subgroup G)) = 1 := by
      rw [tateZeroVal_mk, valuationMod_apply, D.mem_units.1 hU, toAdd_one, map_zero, ofAdd_zero]
    have h2 : (u : tateZero A (K : Subgroup G) (L : Subgroup G)) = 1 :=
      (D.tateZeroVal_bijective hax hLK hu).1 (by rw [h1, map_one])
    obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff u).1 h2
    refine ⟨x, ?_, hx⟩
    show x ∈ D.units L
    rw [D.mem_units]
    have h3 := D.valuation_norm hLK x
    rw [hx, D.mem_units.1 hU] at h3
    exact (ProfiniteInteger.pow_left_inj (D.relInertiaDegree_ne_zero hLK)).1
      (by rw [one_pow]; exact h3.symm)
  · rintro _ ⟨x, hx, rfl⟩
    exact D.norm_mem_units hLK hx

theorem exists_eq_smul_div_of_mem_augmentation (hLK : L ≤ K) (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    {φ : (K : Subgroup G)} (hφ : D.relDeg K φ = Multiplicative.ofAdd 1) {x : A}
    (hx : x ∈ augmentation A (K : Subgroup G) (L : Subgroup G)) :
    ∃ b ∈ fixedModule A (L : Subgroup G), x = (φ : G) • b / b := by
  have := normal_of_unramified (d := D.deg) hLK hu

  let S : Subgroup A :=
    { carrier := {y | ∃ b ∈ fixedModule A (L : Subgroup G), y = (φ : G) • b / b}
      one_mem' := ⟨1, Subgroup.one_mem _, by rw [smul_one, div_one]⟩
      mul_mem' := by
        rintro _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩
        exact ⟨b * c, Subgroup.mul_mem _ hb hc, by rw [smul_mul', mul_div_mul_comm]⟩
      inv_mem' := by
        rintro _ ⟨b, hb, rfl⟩
        exact ⟨b⁻¹, Subgroup.inv_mem _ hb, by rw [smul_inv', inv_div_inv, inv_div]⟩ }

  let T : Subgroup (K : Subgroup G) :=
    { carrier := {g | ∀ a ∈ fixedModule A (L : Subgroup G), (g : G) • a / a ∈ S}
      one_mem' := fun a _ => by
        rw [OneMemClass.coe_one, one_smul, div_self']
        exact S.one_mem
      mul_mem' := by
        intro g h hg hh a ha
        have hha : (h : G) • a ∈ fixedModule A (L : Subgroup G) :=
          smul_mem_fixedModule_of_normal (L := (L : Subgroup G)) hLK h.2 ha
        have e : ((g * h : (K : Subgroup G)) : G) • a / a =
            ((g : G) • ((h : G) • a) / ((h : G) • a)) * ((h : G) • a / a) := by
          rw [Subgroup.coe_mul, mul_smul]
          simp only [div_eq_mul_inv, mul_assoc, inv_mul_cancel_left]
        rw [e]
        exact S.mul_mem (hg _ hha) (hh a ha)
      inv_mem' := by
        intro g hg a ha
        have hga : ((g⁻¹ : (K : Subgroup G)) : G) • a ∈ fixedModule A (L : Subgroup G) :=
          smul_mem_fixedModule_of_normal (L := (L : Subgroup G)) hLK (g⁻¹).2 ha
        have e : ((g⁻¹ : (K : Subgroup G)) : G) • a / a =
            ((g : G) • (((g⁻¹ : (K : Subgroup G)) : G) • a) / (((g⁻¹ : (K : Subgroup G)) : G) • a))⁻¹ := by
          rw [smul_smul, InvMemClass.coe_inv, mul_inv_cancel, one_smul, inv_div]
        rw [e]
        exact S.inv_mem (hg _ hga) }
  have hφT : φ ∈ T := fun a ha => ⟨a, ha, rfl⟩
  have hLT : ∀ ρ : (K : Subgroup G), (ρ : G) ∈ (L : Subgroup G) → ρ ∈ T := fun ρ hρ a ha => by
    rw [ha ρ hρ, div_self']
    exact S.one_mem
  have hTop : ∀ g : (K : Subgroup G), g ∈ T := by
    intro g
    obtain ⟨m, hm⟩ := D.exists_pow_mul_mem_of_unramified hLK hu hφ g
    have hg : g = φ ^ m * ((φ ^ m)⁻¹ * g) := by group
    rw [hg]
    exact T.mul_mem (T.pow_mem hφT m) (hLT _ (by simpa using hm))
  have hle : augmentation A (K : Subgroup G) (L : Subgroup G) ≤ S := by
    rw [augmentation, Subgroup.closure_le]
    rintro _ ⟨g, hg, a, ha, rfl⟩
    exact hTop ⟨g, hg⟩ a ha
  exact hle hx

theorem exists_units_eq_smul_div (hax : ClassFieldAxiom G A) (hLK : L ≤ K)
    (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L) {φ : (K : Subgroup G)}
    (hφ : D.relDeg K φ = Multiplicative.ofAdd 1) {u : fixedModule A (L : Subgroup G)}
    (hN : norm A (K : Subgroup G) (L : Subgroup G) u = 1) :
    ∃ ε ∈ D.units L, (u : A) = (φ : G) • (ε : A) / ε := by
  have := normal_of_unramified (d := D.deg) hLK hu
  have hcard := (hax K L hLK (D.isCyclic_of_unramified hLK hu)).2
  have hsub := (Nat.card_eq_one_iff_unique.1 hcard).1

  have haug : (u : A) ∈ augmentation A (K : Subgroup G) (L : Subgroup G) := by
    have h := (QuotientGroup.eq_one_iff
      (N := (augmentation A (K : Subgroup G) (L : Subgroup G)).comap
        ((fixedModule A (L : Subgroup G)).subtype.comp
          (norm A (K : Subgroup G) (L : Subgroup G)).ker.subtype))
      (⟨u, hN⟩ : (norm A (K : Subgroup G) (L : Subgroup G)).ker)).1 (Subsingleton.elim _ _)
    exact h
  obtain ⟨b, hb, hub⟩ := D.exists_eq_smul_div_of_mem_augmentation hLK hu hφ haug

  have hval : D.valuation L ⟨b, hb⟩ ∈ (D.valuation K).range := by
    rw [range_valuation, ← D.range_valuation L]
    exact ⟨_, rfl⟩
  obtain ⟨c, hc⟩ := hval
  have he : relRamificationIndex D.deg K L = 1 := isUnramified_iff.2 hu
  refine ⟨⟨b, hb⟩ / ⟨c, fixedModule_anti hLK c.2⟩, ?_, ?_⟩
  · rw [D.mem_units, map_div, D.valuation_of_mem hLK c.2, he, pow_one]
    change D.valuation L ⟨b, hb⟩ / D.valuation K c = 1
    rw [hc, div_self']
  · have hφc : (φ : G) • (c : A) = c := c.2 φ φ.2
    change (u : A) = (φ : G) • ((b : A) / c) / (b / c)
    rw [smul_div', hφc, div_div_div_cancel_right, hub]

end Units

end ClassFieldData

end GroundTheory.LocalField.Abstract
end

namespace GroundTheory.LocalField.Abstract

open ProfiniteInteger

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  (D : ClassFieldData G A)

structure FrobeniusLift (K : OpenSubgroup G) where

  elt : G
  mem : elt ∈ (K : Subgroup G)

  deg : ℕ
  deg_pos : 0 < deg
  deg_eq : D.deg elt = Multiplicative.ofAdd ((deg * inertiaDegree D.deg K : ℕ) : ℤ̂)

variable {D} {K L : OpenSubgroup G}

namespace FrobeniusLift

omit [TotallyDisconnectedSpace G] in
theorem degree_ne_zero (s : D.FrobeniusLift K) : s.deg * inertiaDegree D.deg K ≠ 0 :=
  mul_ne_zero s.deg_pos.ne' (D.inertiaDegree_ne_zero K)

omit [TotallyDisconnectedSpace G] in
theorem mem_normalizer (hLK : L ≤ K) [hN : ((L : Subgroup G).subgroupOf K).Normal] {σ : G}
    (hσ : σ ∈ (K : Subgroup G)) :
    σ ∈ Subgroup.normalizer (((L : Subgroup G) ⊓ D.deg.ker : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hconj : ∀ g ∈ (K : Subgroup G), ∀ x ∈ (L : Subgroup G), g * x * g⁻¹ ∈ (L : Subgroup G) := by
    intro g hg x hx
    have := hN.conj_mem ⟨x, hLK hx⟩ (by simpa [Subgroup.mem_subgroupOf] using hx) ⟨g, hg⟩
    simpa [Subgroup.mem_subgroupOf] using this
  simp only [Subgroup.mem_inf, MonoidHom.mem_ker, map_mul, map_inv]
  constructor
  · rintro ⟨hL, hk⟩
    refine ⟨hconj σ hσ h hL, ?_⟩
    rw [hk, mul_one, mul_inv_cancel]
  · rintro ⟨hL, hk⟩
    refine ⟨?_, ?_⟩
    · have := hconj σ⁻¹ (K.inv_mem hσ) _ hL
      simpa [mul_assoc] using this
    · have := hk
      rwa [mul_comm (D.deg σ), mul_assoc, mul_inv_cancel, mul_one] at this

variable (L) in
noncomputable def field (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
    (s : D.FrobeniusLift K) : OpenSubgroup G where
  toSubgroup := frobeniusClosure D.deg L s.elt
  isOpen' := isOpen_frobeniusClosure D.continuous_deg L.isOpen (mem_normalizer hLK s.mem)
    s.degree_ne_zero s.deg_eq

variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal] (s : D.FrobeniusLift K)

theorem coe_field : ((s.field L hLK : OpenSubgroup G) : Subgroup G) =
    frobeniusClosure D.deg L s.elt :=
  rfl

theorem field_le : s.field L hLK ≤ K := by
  intro x hx
  exact frobeniusClosure_le K.isClosed s.mem (inf_le_left.trans hLK) hx

theorem elt_mem_field : s.elt ∈ ((s.field L hLK : OpenSubgroup G) : Subgroup G) :=
  mem_frobeniusClosure_self

theorem field_inf_ker :
    ((s.field L hLK : OpenSubgroup G) : Subgroup G) ⊓ D.deg.ker = (L : Subgroup G) ⊓ D.deg.ker :=
  frobeniusClosure_inf_ker D.continuous_deg L.isOpen (mem_normalizer hLK s.mem) s.degree_ne_zero
    s.deg_eq

theorem inertiaDegree_field :
    inertiaDegree D.deg ((s.field L hLK : OpenSubgroup G) : Subgroup G) =
      s.deg * inertiaDegree D.deg K :=
  inertiaDegree_frobeniusClosure D.continuous_deg (mem_normalizer hLK s.mem) s.degree_ne_zero
    s.deg_eq

theorem relDeg_field :
    D.relDeg (s.field L hLK) ⟨s.elt, s.elt_mem_field hLK⟩ = Multiplicative.ofAdd 1 := by
  refine (ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero (s.field L hLK))).1 ?_
  rw [D.relDeg_pow, inertiaDegree_field, ← ofAdd_nsmul, nsmul_one]
  exact s.deg_eq

end FrobeniusLift

omit [TotallyDisconnectedSpace G] in
theorem exists_prime (K : OpenSubgroup G) :
    ∃ π : fixedModule A (K : Subgroup G), D.valuation K π = Multiplicative.ofAdd 1 := by
  have h := D.intCast_mem_range_val 1
  rw [← D.range_valuation K, Int.cast_one] at h
  exact h

section PrimeNorm

variable (K L) in
noncomputable def primeNorm (S : OpenSubgroup G) : tateZero A (K : Subgroup G) (L : Subgroup G) :=
  QuotientGroup.mk (norm A (K : Subgroup G) (S : Subgroup G) (D.exists_prime S).choose)

omit [TotallyDisconnectedSpace G] in
theorem norm_mem_range_of_mem_units (hax : ClassFieldAxiom G A) {S : OpenSubgroup G} (hSK : S ≤ K)
    (hLK : L ≤ K) (hu : (S : Subgroup G) ⊓ D.deg.ker ≤ L) {u : fixedModule A (S : Subgroup G)}
    (hu' : u ∈ D.units S) :
    norm A (K : Subgroup G) (S : Subgroup G) u ∈ (norm A (K : Subgroup G) (L : Subgroup G)).range := by
  set M : OpenSubgroup G := L ⊓ S with hMdef
  have hMS : M ≤ S := inf_le_right
  have hML : M ≤ L := inf_le_left
  have hMu : (S : Subgroup G) ⊓ D.deg.ker ≤ M := fun x hx => ⟨hu hx, hx.1⟩
  rw [D.units_eq_map_norm hax hMS hMu] at hu'
  obtain ⟨w, -, rfl⟩ := hu'
  rw [norm_norm (fun x hx => hMS hx) (fun x hx => hSK hx) w]
  exact ⟨norm A (L : Subgroup G) (M : Subgroup G) w,
    norm_norm (fun x hx => hML hx) (fun x hx => hLK hx) w⟩

omit [TotallyDisconnectedSpace G] in
theorem mk_norm_eq_primeNorm (hax : ClassFieldAxiom G A) {S : OpenSubgroup G} (hSK : S ≤ K)
    (hLK : L ≤ K) (hu : (S : Subgroup G) ⊓ D.deg.ker ≤ L) {π : fixedModule A (S : Subgroup G)}
    (hπ : D.valuation S π = Multiplicative.ofAdd 1) :
    (QuotientGroup.mk (norm A (K : Subgroup G) (S : Subgroup G) π) :
      tateZero A (K : Subgroup G) (L : Subgroup G)) = D.primeNorm K L S := by
  set π0 := (D.exists_prime S).choose with hπ0
  have h0 : D.valuation S π0 = Multiplicative.ofAdd 1 := (D.exists_prime S).choose_spec
  have hu' : π * π0⁻¹ ∈ D.units S := by
    rw [D.mem_units, map_mul, map_inv, hπ, h0, mul_inv_cancel]
  obtain ⟨b, hb⟩ := D.norm_mem_range_of_mem_units hax hSK hLK hu hu'
  rw [primeNorm, ← hπ0, QuotientGroup.eq]
  have : (norm A (K : Subgroup G) (S : Subgroup G) π)⁻¹ * norm A (K : Subgroup G) (S : Subgroup G) π0 =
      (norm A (K : Subgroup G) (S : Subgroup G) (π * π0⁻¹))⁻¹ := by
    rw [map_mul, map_inv, mul_inv_rev, inv_inv, mul_comm]
  rw [this]
  exact Subgroup.inv_mem _ ⟨b, hb⟩

end PrimeNorm

section RecFrob

variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]

variable (L) in
noncomputable def recFrob (s : D.FrobeniusLift K) : tateZero A (K : Subgroup G) (L : Subgroup G) :=
  D.primeNorm K L (s.field L hLK)

theorem mk_norm_eq_recFrob (hax : ClassFieldAxiom G A) (s : D.FrobeniusLift K)
    {π : fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G)}
    (hπ : D.valuation (s.field L hLK) π = Multiplicative.ofAdd 1) :
    (QuotientGroup.mk (norm A (K : Subgroup G) ((s.field L hLK : OpenSubgroup G) : Subgroup G) π) :
      tateZero A (K : Subgroup G) (L : Subgroup G)) = D.recFrob L hLK s :=
  D.mk_norm_eq_primeNorm hax (s.field_le hLK) hLK (fun x hx => by
    have := (s.field_inf_ker hLK).le hx
    exact this.1) hπ

end RecFrob

end ClassFieldData

end GroundTheory.LocalField.Abstract
end

namespace GroundTheory.LocalField.Abstract

open ProfiniteInteger

variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]

theorem coe_norm_eq_prod_smul_norm (d : G →* Multiplicative ℤ̂) {K S J : Subgroup G} {f n : ℕ}
    (hn : 0 < n) (hf : 0 < f) (hSK : S ≤ K)
    (hdS : ∀ s ∈ S, Multiplicative.toAdd (d s) ∈ multiples (n * f))
    (hsurj : ∀ k ∈ K, Multiplicative.toAdd (d k) ∈ multiples (n * f) → ∃ s ∈ S, d s = d k)
    (hdK : ∀ k ∈ K, Multiplicative.toAdd (d k) ∈ multiples f)
    (hJ : ∀ q ∈ K ⊓ d.ker, q ∈ S ↔ q ∈ J)
    {φ : G} (hφK : φ ∈ K) (hdφ : d φ = Multiplicative.ofAdd (f : ℤ̂))
    [(S.subgroupOf K).FiniteIndex] [(J.subgroupOf (K ⊓ d.ker)).FiniteIndex]
    (a : fixedModule A S) (ha : (a : A) ∈ fixedModule A J) :
    (norm A K S a : A) =
      ∏ ν : Fin n, φ ^ (ν : ℕ) • (norm A (K ⊓ d.ker) J ⟨a, ha⟩ : A) := by
  classical
  set Q := K ⊓ d.ker with hQ
  have hQK : Q ≤ K := inf_le_left

  let incl : Q ⧸ J.subgroupOf Q → K ⧸ S.subgroupOf K :=
    Quotient.map' (fun q : Q => (⟨q, hQK q.2⟩ : K)) fun q q' h => by
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at h ⊢
      have hq : ((q⁻¹ * q' : Q) : G) ∈ Q := (q⁻¹ * q').2
      simpa using (hJ _ hq).2 h
  let φK : K := ⟨φ, hφK⟩
  let F : Fin n × (Q ⧸ J.subgroupOf Q) → K ⧸ S.subgroupOf K := fun p => (φK ^ (p.1 : ℕ)) • incl p.2
  have hFmk : ∀ (ν : Fin n) (q : Q), F (ν, (q : Q ⧸ J.subgroupOf Q)) =
      ((φK ^ (ν : ℕ) * ⟨q, hQK q.2⟩ : K) : K ⧸ S.subgroupOf K) := fun _ _ => rfl

  have hdeg : ∀ (m : ℤ) (q : G), q ∈ Q →
      Multiplicative.toAdd (d (φ ^ m * q)) = ((m * f : ℤ) : ℤ̂) := by
    intro m q hq
    rw [map_mul, map_zpow, hdφ, (MonoidHom.mem_ker).1 hq.2, mul_one, ← ofAdd_zsmul, toAdd_ofAdd,
      zsmul_eq_mul]
    push_cast
    ring
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨ν, x⟩ ⟨μ, y⟩ hxy
      induction x using QuotientGroup.induction_on with
      | H q =>
      induction y using QuotientGroup.induction_on with
      | H q' =>
        rw [hFmk, hFmk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hxy
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubmonoidClass.coe_pow] at hxy

        have hx : ((φ ^ (ν : ℕ) * (q : G))⁻¹ * (φ ^ (μ : ℕ) * q') : G) =
            (q : G)⁻¹ * (φ ^ ((μ : ℤ) - ν) * q') := by
          rw [zpow_sub, zpow_natCast, zpow_natCast]
          group
        have hdq : Multiplicative.toAdd (d ((q : G)⁻¹ * (φ ^ ((μ : ℤ) - ν) * q'))) =
            ((((μ : ℤ) - ν) * f : ℤ) : ℤ̂) := by
          rw [map_mul, map_inv, (MonoidHom.mem_ker).1 q.2.2, inv_one, one_mul]
          exact hdeg _ _ q'.2
        have hmem := hdS _ hxy
        rw [hx, hdq] at hmem
        have hdvd := (intCast_mem_multiples_iff (Nat.mul_pos hn hf)).1 hmem
        push_cast at hdvd
        have hdvd' : (n : ℤ) ∣ (μ : ℤ) - ν :=
          (mul_dvd_mul_iff_right (by exact_mod_cast hf.ne')).1 hdvd
        have hνμ : ν = μ := by
          have hμ := μ.2
          have hν := ν.2
          have h0 : ((μ : ℤ) - ν) = 0 :=
            Int.eq_zero_of_abs_lt_dvd hdvd' (abs_sub_lt_iff.2 ⟨by omega, by omega⟩)
          exact Fin.ext (by omega)
        subst hνμ
        have hqq : (q : G)⁻¹ * q' ∈ S := by simpa [mul_assoc] using hxy
        have hqQ : (q : G)⁻¹ * q' ∈ Q := Q.mul_mem (Q.inv_mem q.2) q'.2
        refine Prod.ext rfl ?_
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa using (hJ _ hqQ).1 hqq
    · intro y
      induction y using QuotientGroup.induction_on with
      | H k =>
        obtain ⟨w, hw⟩ := mem_multiples.1 (hdK k k.2)
        set N : ℕ+ := ⟨n, hn⟩ with hNdef
        set ν : ℕ := (proj N w).val with hνdef
        have hνn : ν < n := ZMod.val_lt _
        have hw' : w - (ν : ℤ̂) ∈ multiples n := by
          have := (proj_eq_zero_iff (n := N) (x := w - (ν : ℤ̂))).1 (by
            rw [map_sub, map_natCast, hνdef, ZMod.natCast_zmod_val, sub_self])
          simpa [hNdef] using this
        obtain ⟨z, hz⟩ := mem_multiples.1 hw'
        have hdk : Multiplicative.toAdd (d (φ ^ (-(ν : ℤ)) * k)) ∈ multiples (n * f) := by
          rw [map_mul, map_zpow, hdφ, ← ofAdd_zsmul, toAdd_mul, toAdd_ofAdd, hw]
          refine mem_multiples.2 ⟨z, ?_⟩
          have : w = (ν : ℤ̂) + n • z := by rw [← hz]; ring
          rw [this]
          simp only [nsmul_eq_mul, zsmul_eq_mul]
          push_cast
          ring
        obtain ⟨s, hs, hds⟩ := hsurj _ (K.mul_mem (K.zpow_mem hφK _) k.2) hdk
        set q : G := φ ^ (-(ν : ℤ)) * k * s⁻¹ with hqdef
        have hqQ : q ∈ Q := by
          refine ⟨K.mul_mem (K.mul_mem (K.zpow_mem hφK _) k.2) (K.inv_mem (hSK hs)), ?_⟩
          show d q = 1
          rw [hqdef, map_mul, map_inv, ← hds, mul_inv_cancel]
        refine ⟨(⟨ν, hνn⟩, ((⟨q, hqQ⟩ : Q) : Q ⧸ J.subgroupOf Q)), ?_⟩
        rw [hFmk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubmonoidClass.coe_pow, hqdef]
        have : ((φ ^ ν * (φ ^ (-(ν : ℤ)) * (k : G) * s⁻¹))⁻¹ * k : G) = s := by
          rw [zpow_neg, zpow_natCast]
          group
        rw [this]
        exact hs
  rw [coe_norm, ← finprod_comp_equiv (Equiv.ofBijective F hF)]
  let _ := Fintype.ofFinite (Q ⧸ J.subgroupOf Q)
  rw [finprod_eq_prod_of_fintype, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun ν _ => ?_
  rw [coe_norm, finprod_eq_prod_of_fintype, Finset.smul_prod']
  refine Finset.prod_congr rfl fun x _ => ?_
  induction x using QuotientGroup.induction_on with
  | H q =>
    rw [Equiv.ofBijective_apply, hFmk, cosetSMul_mk, cosetSMul_mk, smul_smul]
    rfl

namespace ClassFieldData

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}


omit [TotallyDisconnectedSpace G] in
instance finiteIndex_inf_ker (d : G →* Multiplicative ℤ̂) (K L : OpenSubgroup G) :
    (((L : Subgroup G) ⊓ d.ker).subgroupOf ((K : Subgroup G) ⊓ d.ker)).FiniteIndex := by
  have h : ((L : Subgroup G) ⊓ d.ker).subgroupOf ((K : Subgroup G) ⊓ d.ker) =
      (L : Subgroup G).subgroupOf ((K : Subgroup G) ⊓ d.ker) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, and_iff_left_iff_imp]
    exact fun _ => x.2.2
  rw [h]
  infer_instance


omit [TotallyDisconnectedSpace G] in
theorem toAdd_deg_mem_multiples (K : OpenSubgroup G) {k : G} (hk : k ∈ (K : Subgroup G)) :
    Multiplicative.toAdd (D.deg k) ∈ multiples (inertiaDegree D.deg K) := by
  obtain ⟨y, hy⟩ := (D.mem_map_deg_iff K).1 ⟨k, hk, rfl⟩
  refine mem_multiples.2 ⟨Multiplicative.toAdd y, ?_⟩
  rw [← hy, toAdd_pow]

variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal] (s : D.FrobeniusLift K)

theorem coe_norm_field_eq {φ : G} (hφK : φ ∈ (K : Subgroup G))
    (hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂))
    (a : fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G)) :
    (norm A (K : Subgroup G) (s.field L hLK : Subgroup G) a : A) =
      ∏ ν : Fin s.deg, φ ^ (ν : ℕ) •
        (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
          ⟨a, fixedModule_anti le_frobeniusClosure a.2⟩ : A) := by
  have hnormalizer := FrobeniusLift.mem_normalizer (D := D) hLK s.mem
  have hmap := map_frobeniusClosure D.continuous_deg hnormalizer s.deg_eq (L := (L : Subgroup G))
  have hfield_le : (s.field L hLK : Subgroup G) ≤ (K : Subgroup G) :=
    frobeniusClosure_le K.isClosed s.mem (inf_le_left.trans hLK)
  have hfield_inf_ker :
      (s.field L hLK : Subgroup G) ⊓ D.deg.ker = (L : Subgroup G) ⊓ D.deg.ker :=
    frobeniusClosure_inf_ker D.continuous_deg L.isOpen hnormalizer
      (mul_ne_zero s.deg_pos.ne' (D.inertiaDegree_ne_zero K)) s.deg_eq
  refine coe_norm_eq_prod_smul_norm D.deg s.deg_pos (Nat.pos_of_ne_zero (D.inertiaDegree_ne_zero K))
    hfield_le ?_ ?_ (fun k hk => toAdd_deg_mem_multiples K hk) ?_ hφK hdφ a _
  · intro x hx
    have : D.deg x ∈ (frobeniusClosure D.deg L s.elt).map D.deg := ⟨x, hx, rfl⟩
    rw [hmap] at this
    exact this
  · intro k _ hk
    have : D.deg k ∈ AddSubgroup.toSubgroup (multiples (s.deg * inertiaDegree D.deg K)) := hk
    rw [← hmap] at this
    obtain ⟨x, hx, hxk⟩ := this
    exact ⟨x, hx, hxk⟩
  · intro q hq
    constructor
    · intro hqS
      exact hfield_inf_ker.le ⟨hqS, hq.2⟩
    · intro hqJ
      exact le_frobeniusClosure hqJ

end ClassFieldData

end GroundTheory.LocalField.Abstract
