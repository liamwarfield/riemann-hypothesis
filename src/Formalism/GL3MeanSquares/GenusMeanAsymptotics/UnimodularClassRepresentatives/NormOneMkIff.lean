module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoMeanAlphaN

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SmulGenMemIff
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DiscrIdealLeIff
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem map_mem_extP {𝔭 : Ideal (𝓞 F)} {k : ℕ} {s : 𝓞 F} (hs : s ∈ 𝔭 ^ k) :
    algebraMap (𝓞 F) (𝓞 K) s ∈ extP K 𝔭 ^ k := by
  rw [← Ideal.mem_comap, MeanB.comap_extP_pow]
  exact hs

theorem mem_extP_of_mul {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {t : 𝓞 F} (ht : t ∉ 𝔭) {k : ℕ}
    {z : 𝓞 K} (hz : algebraMap (𝓞 F) (𝓞 K) t * z ∈ extP K 𝔭 ^ k) : z ∈ extP K 𝔭 ^ k := by
  obtain ⟨u, hu⟩ := MeanA.exists_mul_sub_one_mem_pow h𝔭 ht k
  have e : z = algebraMap (𝓞 F) (𝓞 K) u * (algebraMap (𝓞 F) (𝓞 K) t * z) -
      algebraMap (𝓞 F) (𝓞 K) (u * t - 1) * z := by
    rw [map_sub, map_mul, map_one]
    ring
  rw [e]
  exact sub_mem (Ideal.mul_mem_left _ _ hz) (Ideal.mul_mem_right _ _ (map_mem_extP hu))

theorem conjO_mem_extP (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) {z : 𝓞 K}
    (hz : z ∈ extP K 𝔭 ^ k) : conjO K z ∈ extP K 𝔭 ^ k := by
  obtain ⟨z', hz', e⟩ := MeanB.star_mem_extP hF 𝔭 k hz
  have : conjO K z = z' := RingOfIntegers.ext e.symm
  rw [this]
  exact hz'

theorem ne_bot_of_isMaximal {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 𝔭 ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField F)

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def IsGen (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (e : V) : Prop :=
  e ∈ L ∧ e ≠ 0 ∧ ∀ x ∈ L, ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ a : 𝓞 K, algebraMap (𝓞 F) (𝓞 K) t • x = a • e

theorem exists_isGen {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L)
    (h1 : finrank K V = 1) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : ∃ e, IsGen L 𝔭 e := by
  obtain ⟨b, hb, hloc⟩ := LocalSpans.exists_basis_locF hL h𝔭
  have hsub : Subsingleton (Fin (finrank K V)) := by
    rw [h1]
    infer_instance
  let i0 : Fin (finrank K V) := ⟨0, by omega⟩
  refine ⟨b i0, hb i0, b.ne_zero i0, fun x hx => ?_⟩
  have hx' : x ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) := by
    rw [hloc]
    exact LocF.le_locF 𝔭 L hx
  obtain ⟨t, ht, hm⟩ := (LocF.mem_locF_iff h𝔭.isPrime _ _).1 hx'
  have hr : Set.range b = {b i0} := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      rw [Subsingleton.elim i i0]
      rfl
    · rintro rfl
      exact ⟨i0, rfl⟩
  rw [hr, Submodule.mem_span_singleton] at hm
  obtain ⟨a, ha⟩ := hm
  exact ⟨t, ht, a, ha.symm⟩

theorem discrIdeal_le_iff (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (h1 : finrank K V = 1) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {e : V} (he : IsGen L 𝔭 e)
    {n : 𝓞 F} (hn : h e e = algebraMap F K (n : F)) (j : ℕ) :
    discrIdeal h L ≤ extP K 𝔭 ^ j ↔ n ∈ 𝔭 ^ j := by
  have hsub : Subsingleton (Fin (finrank K V)) := by
    rw [h1]
    infer_instance
  let i0 : Fin (finrank K V) := ⟨0, by omega⟩
  constructor
  · intro hle
    rw [← MeanB.comap_extP_pow (K := K), Ideal.mem_comap]
    apply hle
    refine Ideal.subset_span ⟨fun _ => e, fun _ => he.1, ?_⟩
    rw [Matrix.det_eq_elem_of_subsingleton _ i0, Matrix.of_apply, hn]
    rfl
  · intro hnj
    unfold discrIdeal
    rw [Ideal.span_le]
    rintro z ⟨x, hx, hz⟩
    rw [Matrix.det_eq_elem_of_subsingleton _ i0, Matrix.of_apply] at hz
    obtain ⟨t, ht, a, ha⟩ := he.2.2 (x i0) (hx i0)
    apply mem_extP_of_mul h𝔭 ht
    apply mem_extP_of_mul h𝔭 ht
    have : algebraMap (𝓞 F) (𝓞 K) t * (algebraMap (𝓞 F) (𝓞 K) t * z) =
        conjO K a * a * algebraMap (𝓞 F) (𝓞 K) n := by
      apply RingOfIntegers.coe_injective
      have e1 : h (algebraMap (𝓞 F) (𝓞 K) t • x i0) (algebraMap (𝓞 F) (𝓞 K) t • x i0) =
          h (a • e) (a • e) := by rw [ha]
      rw [Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right,
        Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right, hn, ← hz,
        MeanB.algebraMap_comp, MeanB.star_algebraMap hF] at e1
      simp only [map_mul]
      rw [MeanB.algebraMap_comp, MeanB.algebraMap_comp]
      change _ = star (algebraMap (𝓞 K) K a) * _ * _
      rw [e1]
      ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (map_mem_extP hnj)

theorem vd_spec (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h)
    {L : Submodule (𝓞 K) V} (h1 : finrank K V = 1) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {e : V}
    (he : IsGen L 𝔭 e) {n : 𝓞 F} (hn : h e e = algebraMap F K (n : F)) :
    n ∈ 𝔭 ^ vd h L 𝔭 ∧ n ∉ 𝔭 ^ (vd h L 𝔭 + 1) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply he.2.1
    apply LocF.aniso_of_totPosDef hd
    rw [hn]
    simp
  have hset : {j : ℕ | discrIdeal h L ≤ extP K 𝔭 ^ j} = {j : ℕ | n ∈ 𝔭 ^ j} := by
    ext j
    exact discrIdeal_le_iff hF h1 h𝔭 he hn j
  have hinf : (⨅ j : ℕ, 𝔭 ^ j) = ⊥ := Ideal.iInf_pow_eq_bot_of_isDomain 𝔭 h𝔭.ne_top
  obtain ⟨j0, hj0⟩ : ∃ j0, n ∉ 𝔭 ^ j0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    apply hn0
    have : n ∈ (⨅ j : ℕ, 𝔭 ^ j) := (Submodule.mem_iInf _).2 hcon
    rwa [hinf] at this
  have hbdd : BddAbove {j : ℕ | n ∈ 𝔭 ^ j} := by
    refine ⟨j0, fun j hj => ?_⟩
    by_contra hlt
    exact hj0 (Ideal.pow_le_pow_right (not_le.1 hlt).le hj)
  have hne : {j : ℕ | n ∈ 𝔭 ^ j}.Nonempty := ⟨0, by simp⟩
  unfold vd
  rw [hset]
  refine ⟨Nat.sSup_mem hne hbdd, fun hcon => ?_⟩
  have := le_csSup hbdd (show sSup {j : ℕ | n ∈ 𝔭 ^ j} + 1 ∈ {j : ℕ | n ∈ 𝔭 ^ j} from hcon)
  omega

end Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals
end
end

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.EndomorphismScalars

open Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

abbrev Qk (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) : Type :=
  ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)

variable {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {e : V}

private theorem exists_mul_sub_one_mem_pow_of_not_mem_maximal (h𝔭 : 𝔭.IsMaximal) {t : 𝓞 F} (ht : t ∉ 𝔭) (k : ℕ) :
    ∃ s : 𝓞 F, s * t - 1 ∈ 𝔭 ^ k := by
  obtain ⟨y, i, hi, hyi⟩ := h𝔭.exists_inv ht
  refine ⟨y * ∑ l ∈ Finset.range k, i ^ l, ?_⟩
  have h1 : y * t = 1 - i := by rw [← hyi]; ring
  have h2 : y * (∑ l ∈ Finset.range k, i ^ l) * t - 1 = -(i ^ k) := by
    rw [mul_right_comm, h1, mul_neg_geom_sum]; ring
  rw [h2]
  exact (Submodule.neg_mem_iff _).mpr (Ideal.pow_mem_pow hi k)

private theorem algebraMap_mem_extP_pow_of_mem_pow {k : ℕ} {a : 𝓞 F} (ha : a ∈ 𝔭 ^ k) :
    algebraMap (𝓞 F) (𝓞 K) a ∈ extP K 𝔭 ^ k := by
  rw [extP, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ha

theorem mk_eq_smul (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) (x : ↥L) :
    ∃ a : 𝓞 K, (Submodule.Quotient.mk x : Qk L 𝔭 k) = a • Submodule.Quotient.mk ⟨e, he.1⟩ := by
  obtain ⟨t, ht, a, hta⟩ := he.2.2 x x.2
  obtain ⟨s, hs⟩ := exists_mul_sub_one_mem_pow_of_not_mem_maximal h𝔭 ht k
  refine ⟨algebraMap (𝓞 F) (𝓞 K) s * a, ?_⟩
  have hmem : (algebraMap (𝓞 F) (𝓞 K) (s * t - 1)) • x ∈
      ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L) :=
    Submodule.smul_mem_smul (algebraMap_mem_extP_pow_of_mem_pow hs) Submodule.mem_top
  have hL : (algebraMap (𝓞 F) (𝓞 K) t) • x = a • (⟨e, he.1⟩ : ↥L) :=
    Subtype.ext (by rw [Submodule.coe_smul, Submodule.coe_smul]; exact hta)
  have hx : x = (algebraMap (𝓞 F) (𝓞 K) s * a) • (⟨e, he.1⟩ : ↥L) -
      (algebraMap (𝓞 F) (𝓞 K) (s * t - 1)) • x := by
    rw [map_sub, map_mul, map_one, sub_smul, one_smul, mul_smul, mul_smul, hL]
    abel
  conv_lhs => rw [hx]
  rw [Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero _).mpr hmem, sub_zero,
    Submodule.Quotient.mk_smul]

theorem smul_top_spec (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) {w : ↥L}
    (hw : w ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) :
    ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ c ∈ extP K 𝔭 ^ k, algebraMap (𝓞 F) (𝓞 K) t • (w : V) = c • e := by
  refine Submodule.smul_induction_on
    (p := fun w : ↥L => ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ c ∈ extP K 𝔭 ^ k,
      algebraMap (𝓞 F) (𝓞 K) t • (w : V) = c • e) hw ?_ ?_
  · intro r hr n _
    obtain ⟨t, ht, a, hta⟩ := he.2.2 n n.2
    refine ⟨t, ht, r * a, Ideal.mul_mem_right _ _ hr, ?_⟩
    rw [Submodule.coe_smul, smul_comm, hta, smul_smul]
  · rintro x y ⟨t1, ht1, c1, hc1, h1⟩ ⟨t2, ht2, c2, hc2, h2⟩
    refine ⟨t1 * t2, fun h => (h𝔭.isPrime.mem_or_mem h).elim ht1 ht2,
      algebraMap (𝓞 F) (𝓞 K) t2 * c1 + algebraMap (𝓞 F) (𝓞 K) t1 * c2,
      Ideal.add_mem _ (Ideal.mul_mem_left _ _ hc1) (Ideal.mul_mem_left _ _ hc2), ?_⟩
    have e1 : algebraMap (𝓞 F) (𝓞 K) (t1 * t2) • (x : V) = algebraMap (𝓞 F) (𝓞 K) t2 • (c1 • e) := by
      rw [map_mul, mul_comm (algebraMap (𝓞 F) (𝓞 K) t1), mul_smul, h1]
    have e2 : algebraMap (𝓞 F) (𝓞 K) (t1 * t2) • (y : V) = algebraMap (𝓞 F) (𝓞 K) t1 • (c2 • e) := by
      rw [map_mul, mul_smul, h2]
    rw [Submodule.coe_add, smul_add, e1, e2, add_smul, mul_smul, mul_smul]

theorem smul_gen_mem_iff (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) (b : 𝓞 K) :
    b • (⟨e, he.1⟩ : ↥L) ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L) ↔ b ∈ extP K 𝔭 ^ k := by
  constructor
  · intro hb
    obtain ⟨t, ht, c, hc, htc⟩ := smul_top_spec h𝔭 he k hb
    have h1 : (algebraMap (𝓞 F) (𝓞 K) t * b) • e = c • e := by
      rw [Submodule.coe_smul] at htc
      rw [mul_smul]
      exact htc
    have h2 : algebraMap (𝓞 F) (𝓞 K) t * b = c := by
      rw [← algebraMap_smul K _ e, ← algebraMap_smul K c e] at h1
      exact IsFractionRing.injective (𝓞 K) K (smul_left_injective K he.2.1 h1)
    obtain ⟨s, hs⟩ := exists_mul_sub_one_mem_pow_of_not_mem_maximal h𝔭 ht k
    have hb' : b = algebraMap (𝓞 F) (𝓞 K) s * c -
        algebraMap (𝓞 F) (𝓞 K) (s * t - 1) * b := by
      rw [← h2, map_sub, map_mul, map_one]; ring
    rw [hb']
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hc) (Ideal.mul_mem_right _ _ (algebraMap_mem_extP_pow_of_mem_pow hs))
  · intro hb
    exact Submodule.smul_mem_smul hb Submodule.mem_top

theorem end_surj (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ)
    (X : Module.End (𝓞 K) (Qk L 𝔭 k)) :
    ∃ b : 𝓞 K, algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)) b = X := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (X (Submodule.Quotient.mk ⟨e, he.1⟩))
  obtain ⟨a, ha⟩ := mk_eq_smul h𝔭 he k y
  refine ⟨a, LinearMap.ext fun z => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨ax, hax⟩ := mk_eq_smul h𝔭 he k x
  rw [Module.algebraMap_end_apply, hax, map_smul, ← hy, ha, smul_comm]

theorem end_eq_zero_iff (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) (b : 𝓞 K) :
    algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)) b = 0 ↔ b ∈ extP K 𝔭 ^ k := by
  constructor
  · intro h0
    have := LinearMap.congr_fun h0 (Submodule.Quotient.mk ⟨e, he.1⟩)
    rw [Module.algebraMap_end_apply, LinearMap.zero_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero] at this
    exact (smul_gen_mem_iff h𝔭 he k b).mp this
  · intro hb
    refine LinearMap.ext fun z => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [Module.algebraMap_end_apply, LinearMap.zero_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hb Submodule.mem_top

def endHom (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) :
    (𝓞 K ⧸ extP K 𝔭 ^ k) →+* Module.End (𝓞 K) (Qk L 𝔭 k) :=
  Ideal.Quotient.lift _ (algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)))
    fun b hb => (end_eq_zero_iff h𝔭 he k b).2 hb

theorem endHom_mk (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) (b : 𝓞 K) :
    endHom h𝔭 he k (Ideal.Quotient.mk _ b) =
      algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)) b := Ideal.Quotient.lift_mk _ _ _

theorem endHom_bijective (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) :
    Function.Bijective (endHom h𝔭 he k) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [endHom_mk, end_eq_zero_iff h𝔭 he k] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hz
  · intro X
    obtain ⟨b, hb⟩ := end_surj h𝔭 he k X
    exact ⟨Ideal.Quotient.mk _ b, by rw [endHom_mk, hb]⟩

end Formalism.HermitianLattices.Ext.L3.EndomorphismScalars
end
end

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.NormOneGroup

open Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals Formalism.HermitianLattices.Ext.L3.EndomorphismScalars

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {e : V} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem cond_of_mem (hF : IsFixF K F) (hs : h.IsSymm) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) {n : 𝓞 F} (hn : h e e = algebraMap F K (n : F))
    {v k : ℕ} (hv : n ∈ 𝔭 ^ v) (hvk : v ≤ k) {b : 𝓞 K}
    (hc : conjO K b * b - 1 ∈ extP K 𝔭 ^ (k - v)) (x y x' y' : ↥L)
    (hx : x' - b • x ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L))
    (hy : y' - b • y ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) :
    CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V)) := by
  have e3 : ∀ c : 𝓞 K, algebraMap (𝓞 K) K (conjO K c) = star (algebraMap (𝓞 K) K c) :=
    fun _ => rfl
  have eφ : ∀ a : 𝓞 F, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a) = algebraMap F K (a : F) :=
    fun _ => rfl
  have hψ : ∀ a c : 𝓞 F, algebraMap F K ((a * c : 𝓞 F) : F) =
      algebraMap F K (a : F) * algebraMap F K (c : F) := fun a c => by
    rw [show ((a * c : 𝓞 F) : F) = (a : F) * (c : F) from rfl, map_mul]
  have hfix : ∀ a : 𝓞 F, star (algebraMap F K (a : F)) = algebraMap F K (a : F) :=
    fun a => (hF _).mpr ⟨_, rfl⟩
  have hsmul1 : ∀ (c : 𝓞 K) (u w : V), h (c • u) w = star (algebraMap (𝓞 K) K c) * h u w :=
    fun c u w => by rw [← algebraMap_smul K c u, LinearMap.map_smulₛₗ₂, smul_eq_mul, starRingEnd_apply]
  have hsmul2 : ∀ (c : 𝓞 K) (u w : V), h u (c • w) = algebraMap (𝓞 K) K c * h u w :=
    fun c u w => by rw [← algebraMap_smul K c w, map_smul, smul_eq_mul]
  have hA : ∀ w ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L), ∀ u : ↥L,
      (∃ z ∈ extP K 𝔭 ^ k, algebraMap (𝓞 K) K z = h (w : V) (u : V)) ∧
      (∃ z ∈ extP K 𝔭 ^ k, algebraMap (𝓞 K) K z = h (u : V) (w : V)) := by
    intro w hw u
    refine Submodule.smul_induction_on hw ?_ ?_
    · intro c hc m _
      obtain ⟨r1, hr1⟩ := Submodule.mem_one.mp (hLi m m.2 u u.2)
      obtain ⟨r2, hr2⟩ := Submodule.mem_one.mp (hLi u u.2 m m.2)
      refine ⟨⟨conjO K c * r1, Ideal.mul_mem_right _ _ (conjO_mem_extP hF 𝔭 k hc), ?_⟩,
        ⟨c * r2, Ideal.mul_mem_right _ _ hc, ?_⟩⟩
      · rw [map_mul, e3, hr1, Submodule.coe_smul, hsmul1]
      · rw [map_mul, hr2, Submodule.coe_smul, hsmul2]
    · intro w1 w2 h1 h2
      obtain ⟨⟨z1, hz1, ez1⟩, ⟨z1', hz1', ez1'⟩⟩ := h1
      obtain ⟨⟨z2, hz2, ez2⟩, ⟨z2', hz2', ez2'⟩⟩ := h2
      refine ⟨⟨z1 + z2, add_mem hz1 hz2, ?_⟩, ⟨z1' + z2', add_mem hz1' hz2', ?_⟩⟩
      · rw [map_add (f := _), ez1, ez2, Submodule.coe_add, map_add (f := _), LinearMap.add_apply]
      · rw [map_add (f := _), ez1', ez2', Submodule.coe_add, map_add (f := _)]
  have hB : ∀ u w : ↥L, ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ r ∈ extP K 𝔭 ^ v,
      algebraMap (𝓞 K) K r = algebraMap F K (t : F) * h (u : V) (w : V) := by
    intro u w
    obtain ⟨t1, ht1, a1, ha1⟩ := he.2.2 u u.2
    obtain ⟨t2, ht2, a2, ha2⟩ := he.2.2 w w.2
    refine ⟨t1 * t2, fun hm => (h𝔭.isPrime.mem_or_mem hm).elim ht1 ht2,
      conjO K a1 * a2 * algebraMap (𝓞 F) (𝓞 K) n, Ideal.mul_mem_left _ _ (map_mem_extP hv), ?_⟩
    have h1 := congrArg₂ (fun p q => h p q) ha1 ha2
    simp only [hsmul1, hsmul2, hn, eφ, hfix] at h1
    rw [map_mul, map_mul, e3, eφ, hψ]
    linear_combination -h1
  obtain ⟨⟨z1, hz1, ez1⟩, -⟩ := hA (x' - b • x) hx y'
  obtain ⟨-, ⟨z2, hz2, ez2⟩⟩ := hA (y' - b • y) hy (b • x)
  obtain ⟨t, ht, r, hr, er⟩ := hB x y
  refine ⟨t, ht, algebraMap (𝓞 F) (𝓞 K) t * (z1 + z2) + (conjO K b * b - 1) * r, ?_, ?_⟩
  · refine add_mem (Ideal.mul_mem_left _ _ (add_mem hz1 hz2)) ?_
    have hpow : extP K 𝔭 ^ k = extP K 𝔭 ^ (k - v) * extP K 𝔭 ^ v := by
      rw [← pow_add, Nat.sub_add_cancel hvk]
    rw [hpow]
    exact Ideal.mul_mem_mul hc hr
  · rw [map_add (f := _), map_mul, map_mul, map_add (f := _), ez1, ez2, er, map_sub, map_mul, map_one, e3, eφ]
    simp only [Submodule.coe_sub, Submodule.coe_smul, map_sub, LinearMap.sub_apply, hsmul1, hsmul2]
    ring

theorem mem_of_cond (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F}
    (hn : h e e = algebraMap F K (n : F)) {v k : ℕ} (hv : n ∈ 𝔭 ^ v) (hv' : n ∉ 𝔭 ^ (v + 1))
    {b : 𝓞 K} (H : CongrP 𝔭 k (h (b • e) (b • e)) (h e e)) :
    conjO K b * b - 1 ∈ extP K 𝔭 ^ (k - v) := by
  obtain ⟨t, ht, z, hz, hzeq⟩ := H
  have e1 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := rfl
  have e2 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) n) = algebraMap F K (n : F) := rfl
  have e3 : algebraMap (𝓞 K) K (conjO K b) = star (algebraMap (𝓞 K) K b) := rfl
  have hbe : h (b • e) (b • e) = star (algebraMap (𝓞 K) K b) * algebraMap (𝓞 K) K b * h e e := by
    rw [← algebraMap_smul K b e, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul,
      starRingEnd_apply, mul_assoc]
  have hz' : z = algebraMap (𝓞 F) (𝓞 K) t * algebraMap (𝓞 F) (𝓞 K) n * (conjO K b * b - 1) := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [hzeq, hbe, hn, map_mul, map_mul, map_sub, map_mul, map_one, e1, e2, e3]
    ring
  rcases le_or_gt k v with hkv | hvk
  · rw [Nat.sub_eq_zero_of_le hkv, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  have hne : 𝔭 ≠ ⊥ := ne_bot_of_isMaximal h𝔭
  have hcop : ∀ I : Ideal (𝓞 F), ¬ I ≤ 𝔭 → 𝔭 ⊔ I = ⊤ := fun I hI => by
    by_contra hne'
    exact hI (le_sup_right.trans (h𝔭.eq_of_le hne' le_sup_left).ge)
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hv)
  have hJp : ¬ J ≤ 𝔭 := by
    intro hle
    apply hv'
    rw [← Ideal.span_singleton_le_iff_mem, hJ, pow_succ]
    exact Ideal.mul_mono_right hle
  have htp : ¬ Ideal.span {t} ≤ 𝔭 := fun hle => ht ((Ideal.span_singleton_le_iff_mem _).mp hle)
  have hcopF : IsCoprime 𝔭 (Ideal.span {t} * J) :=
    (Ideal.isCoprime_iff_sup_eq.mpr (hcop _ htp)).mul_right (Ideal.isCoprime_iff_sup_eq.mpr (hcop _ hJp))
  have hX : IsCoprime (extP K 𝔭) ((Ideal.span {t} * J).map (algebraMap (𝓞 F) (𝓞 K))) := by
    rw [Ideal.isCoprime_iff_sup_eq] at hcopF ⊢
    rw [extP, ← Ideal.map_sup, hcopF, Ideal.map_top]
  have hspan : Ideal.span {z} = extP K 𝔭 ^ v * Ideal.span {conjO K b * b - 1} *
      (Ideal.span {t} * J).map (algebraMap (𝓞 F) (𝓞 K)) := by
    have hn' : Ideal.span {algebraMap (𝓞 F) (𝓞 K) n} =
        Ideal.map (algebraMap (𝓞 F) (𝓞 K)) (𝔭 ^ v) * Ideal.map (algebraMap (𝓞 F) (𝓞 K)) J := by
      rw [← Ideal.map_mul, ← hJ, Ideal.map_span, Set.image_singleton]
    rw [hz', ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
      Ideal.map_mul, extP, ← Ideal.map_pow, hn', Ideal.map_span, Set.image_singleton]
    ring
  have hdvd : extP K 𝔭 ^ k ∣ extP K 𝔭 ^ v * Ideal.span {conjO K b * b - 1} *
      (Ideal.span {t} * J).map (algebraMap (𝓞 F) (𝓞 K)) := by
    rw [← hspan]
    exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hz)
  have hdvd2 := (hX.pow_left (m := k)).dvd_of_dvd_mul_right hdvd
  have hP0 : extP K 𝔭 ^ v ≠ 0 := by
    apply pow_ne_zero
    rw [extP, Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]
    exact hne
  rw [show k = v + (k - v) by omega, pow_add] at hdvd2
  have h3 := (mul_dvd_mul_iff_left hP0).mp hdvd2
  exact (Ideal.span_singleton_le_iff_mem _).mp (Ideal.dvd_iff_le.mp h3)

theorem cond_iff (hF : IsFixF K F) (hs : h.IsSymm) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) {n : 𝓞 F} (hn : h e e = algebraMap F K (n : F))
    {v k : ℕ} (hv : n ∈ 𝔭 ^ v) (hv' : n ∉ 𝔭 ^ (v + 1)) (hvk : v ≤ k) (b : 𝓞 K) :
    (∀ x y x' y' : ↥L,
      (Submodule.Quotient.mk x' : Qk L 𝔭 k) =
        algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)) b (Submodule.Quotient.mk x) →
      (Submodule.Quotient.mk y' : Qk L 𝔭 k) =
        algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)) b (Submodule.Quotient.mk y) →
      CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V))) ↔
      conjO K b * b - 1 ∈ extP K 𝔭 ^ (k - v) := by
  constructor
  · intro H
    apply mem_of_cond hF h𝔭 hn hv hv'
    have h1 : (Submodule.Quotient.mk (b • (⟨e, he.1⟩ : ↥L)) : Qk L 𝔭 k) =
        algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)) b (Submodule.Quotient.mk ⟨e, he.1⟩) := by
      rw [Module.algebraMap_end_apply, Submodule.Quotient.mk_smul]
    exact H _ _ _ _ h1 h1
  · intro hc x y x' y' hx hy
    rw [Module.algebraMap_end_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hx hy
    exact cond_of_mem hF hs hLi h𝔭 he hn hv hvk hc x y x' y' hx hy

def NormOne (Q : Ideal (𝓞 K)) (z : 𝓞 K ⧸ Q) : Prop :=
  ∃ y : 𝓞 K, Ideal.Quotient.mk Q y = z ∧
    Ideal.Quotient.mk Q (conjO K y * y) = Ideal.Quotient.mk Q 1

theorem normOne_mk_iff (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (j : ℕ) (b : 𝓞 K) :
    NormOne (extP K 𝔭 ^ j) (Ideal.Quotient.mk _ b) ↔ conjO K b * b - 1 ∈ extP K 𝔭 ^ j := by
  constructor
  · rintro ⟨y, hy, h1⟩
    rw [Ideal.Quotient.eq] at hy h1
    have hyb : conjO K (y - b) ∈ extP K 𝔭 ^ j := conjO_mem_extP hF 𝔭 j hy
    have e : conjO K b * b - 1 =
        (conjO K y * y - 1) - (conjO K y * (y - b) + conjO K (y - b) * b) := by
      rw [map_sub]
      ring
    rw [e]
    exact sub_mem h1 (add_mem (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_right _ _ hyb))
  · intro h
    exact ⟨b, rfl, Ideal.Quotient.eq.mpr h⟩

theorem card_normOne (Q : Ideal (𝓞 K)) :
    Nat.card {z : 𝓞 K ⧸ Q // NormOne Q z} = normRepCount K Q 1 1 := by
  unfold normRepCount
  refine Nat.card_congr ((Equiv.funUnique (Fin 1) (𝓞 K ⧸ Q)).symm.subtypeEquiv ?_)
  intro z
  constructor
  · rintro ⟨y, h1, h2⟩
    exact ⟨fun _ => y, fun i => by simpa using h1, by simpa using h2⟩
  · rintro ⟨y, h1, h2⟩
    exact ⟨y 0, by simpa using h1 0, by simpa using h2⟩

end Formalism.HermitianLattices.Ext.L3.NormOneGroup
