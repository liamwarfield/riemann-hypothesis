module

public import Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.FiniteDimensionalOfOrtho

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.ExistsNormOneOfPair
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L3.WA

variable {K : Type*} [Field K] [StarRing K]

def IsUnitIn (S : Subring K) (a : K) : Prop := a ≠ 0 ∧ a ∈ S ∧ a⁻¹ ∈ S

structure IsHermSemilocal (S : Subring K) : Prop where
  star_mem : ∀ a ∈ S, star a ∈ S
  frac : ∀ a : K, ∃ t ∈ S, t ≠ 0 ∧ t * a ∈ S
  unram : ∃ θ ∈ S, IsUnitIn S (θ - star θ)
  principal : ∀ A : AddSubgroup K, (∀ s ∈ S, ∀ a ∈ A, s * a ∈ A) → (∃ a ∈ A, a ≠ 0) →
    (∃ t : K, t ≠ 0 ∧ ∀ a ∈ A, t * a ∈ S) → ∃ α ∈ A, α ≠ 0 ∧ ∀ a ∈ A, a * α⁻¹ ∈ S
  unit_or : ∀ a ∈ S, ∀ κ ∈ S, ∀ μ : K, a⁻¹ ∉ S → IsUnitIn S μ →
    IsUnitIn S (1 - κ * a) ∨ IsUnitIn S (1 - (κ + μ) * a)

variable {S : Subring K}

theorem exists_trace_eq (hS : IsHermSemilocal S) {s : K} (hs : s ∈ S) (hss : star s = s) :
    ∃ c ∈ S, c + star c = s := by
  obtain ⟨θ, hθ, hμ0, -, hμi⟩ := hS.unram
  refine ⟨s * θ * (θ - star θ)⁻¹, S.mul_mem (S.mul_mem hs hθ) hμi, ?_⟩
  have h2 : star θ - θ ≠ 0 := by
    intro h
    apply hμ0
    rw [← neg_sub, h, neg_zero]
  simp only [star_mul', star_inv₀, star_sub, star_star, hss]
  have h3 : (star θ - θ)⁻¹ = -(θ - star θ)⁻¹ := by
    rw [← neg_sub, neg_inv]
  rw [h3]
  field_simp
  ring

theorem exists_norm_one_mul_mem (hS : IsHermSemilocal S) {a : K} (ha : star a * a ∈ S) :
    ∃ b : K, star b * b = 1 ∧ a * b ∈ S := by
  let A : AddSubgroup K :=
    { carrier := {z | ∃ x ∈ S, ∃ y ∈ S, z = x + y * a}
      zero_mem' := ⟨0, S.zero_mem, 0, S.zero_mem, by simp⟩
      add_mem' := by
        rintro _ _ ⟨x, hx, y, hy, rfl⟩ ⟨x', hx', y', hy', rfl⟩
        exact ⟨x + x', S.add_mem hx hx', y + y', S.add_mem hy hy', by ring⟩
      neg_mem' := by
        rintro _ ⟨x, hx, y, hy, rfl⟩
        exact ⟨-x, S.neg_mem hx, -y, S.neg_mem hy, by ring⟩ }
  have h1A : (1 : K) ∈ A := ⟨1, S.one_mem, 0, S.zero_mem, by simp⟩
  have haA : a ∈ A := ⟨0, S.zero_mem, 1, S.one_mem, by simp⟩
  have hAS : ∀ s ∈ S, ∀ z ∈ A, s * z ∈ A := by
    rintro s hs _ ⟨x, hx, y, hy, rfl⟩
    exact ⟨s * x, S.mul_mem hs hx, s * y, S.mul_mem hs hy, by ring⟩
  obtain ⟨t, htS, ht0, hta⟩ := hS.frac a
  have htA : ∀ z ∈ A, t * z ∈ S := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    have : t * (x + y * a) = t * x + y * (t * a) := by ring
    rw [this]
    exact S.add_mem (S.mul_mem htS hx) (S.mul_mem hy hta)
  obtain ⟨δ, ⟨x, hx, y, hy, hδ⟩, hδ0, hdiv⟩ :=
    hS.principal A hAS ⟨1, h1A, one_ne_zero⟩ ⟨t, ht0, htA⟩
  have hsS : δ⁻¹ ∈ S := by simpa using hdiv 1 h1A
  have hrS : a * δ⁻¹ ∈ S := hdiv a haA
  generalize hsdef : δ⁻¹ = s at hsS hrS
  have hs0 : s ≠ 0 := by rw [← hsdef]; exact inv_ne_zero hδ0
  have h1 : x * s + y * (a * s) = 1 := by
    rw [← mul_assoc, ← add_mul, ← hδ, ← hsdef]
    exact mul_inv_cancel₀ hδ0
  have hss0 : star s ≠ 0 := star_ne_zero.mpr hs0
  refine ⟨s / star s, ?_, ?_⟩
  · rw [star_div₀, star_star]
    field_simp
  · have hq : (x * star (a * s) + y * (star a * a) * star s) * s = star (a * s) := by
      calc (x * star (a * s) + y * (star a * a) * star s) * s
          = star (a * s) * (x * s + y * (a * s)) := by rw [star_mul']; ring
        _ = star (a * s) := by rw [h1, mul_one]
    have : a * (s / star s) = star (x * star (a * s) + y * (star a * a) * star s) := by
      rw [← mul_div_assoc, div_eq_iff hss0, ← star_mul', hq, star_star]
    rw [this]
    exact hS.star_mem _ (S.add_mem (S.mul_mem hx (hS.star_mem _ hrS))
      (S.mul_mem (S.mul_mem hy ha) (hS.star_mem _ hsS)))

variable {V : Type*} [AddCommGroup V] [Module K V]

theorem exists_norm_one_of_pair (hS : IsHermSemilocal S) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    {y w : V} {a : K} (ha : a ∈ S) (ha0 : a ≠ 0) (hy : h y y = star a * a) (hyw : h y w = 1)
    (hw : h w w ∈ S) :
    ∃ c ∈ S, ∃ d ∈ S, h (c • w + d • y) (c • w + d • y) = 1 := by
  have hwy : h w y = 1 := by
    have := hs.eq y w
    rw [hyw, map_one] at this
    exact this.symm
  have hH : star (h w w) = h w w := hs.eq w w
  have key : ∀ c d : K, h (c • w + d • y) (c • w + d • y) =
      star c * c * h w w + star c * d + star d * c + star d * d * (star a * a) := by
    intro c d
    simp only [map_add (f := _), LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, hy, hyw, hwy, starRingEnd_apply, RingHom.id_apply]
    ring
  by_cases hu : a⁻¹ ∈ S
  · refine ⟨0, S.zero_mem, a⁻¹, hu, ?_⟩
    have hsa : star a ≠ 0 := star_ne_zero.mpr ha0
    rw [key, star_inv₀]
    field_simp
    simp
  · obtain ⟨θ, hθ, hμ⟩ := hS.unram
    have h1a : 1 + a ∈ S := S.add_mem S.one_mem ha
    obtain ⟨κ, hκ, hκt⟩ : ∃ κ ∈ S, κ + star κ = star (1 + a) * (1 + a) * h w w - 1 := by
      apply exists_trace_eq hS
      · exact S.sub_mem (S.mul_mem (S.mul_mem (hS.star_mem _ h1a) h1a) hw) S.one_mem
      · simp only [star_sub, star_mul', star_star, hH, star_one]
        ring
    have fin : ∀ κ' ∈ S, κ' + star κ' = star (1 + a) * (1 + a) * h w w - 1 →
        IsUnitIn S (1 - κ' * a) →
        ∃ c ∈ S, ∃ d ∈ S, h (c • w + d • y) (c • w + d • y) = 1 := by
      rintro κ' hκ' ht ⟨h0, -, h2⟩
      refine ⟨star (1 + a) * (1 - κ' * a)⁻¹, S.mul_mem (hS.star_mem _ h1a) h2,
        -κ' * (1 - κ' * a)⁻¹, S.mul_mem (S.neg_mem hκ') h2, ?_⟩
      have h0' : star (1 - κ' * a) ≠ 0 := star_ne_zero.mpr h0
      have hb : star (1 + a) * (1 + a) * h w w = κ' + star κ' + 1 := by rw [ht]; ring
      rw [key]
      have e : star (star (1 + a) * (1 - κ' * a)⁻¹) * (star (1 + a) * (1 - κ' * a)⁻¹) * h w w +
          star (star (1 + a) * (1 - κ' * a)⁻¹) * (-κ' * (1 - κ' * a)⁻¹) +
          star (-κ' * (1 - κ' * a)⁻¹) * (star (1 + a) * (1 - κ' * a)⁻¹) +
          star (-κ' * (1 - κ' * a)⁻¹) * (-κ' * (1 - κ' * a)⁻¹) * (star a * a) =
          (star (1 - κ' * a))⁻¹ * (1 - κ' * a)⁻¹ * (star (1 + a) * (1 + a) * h w w
            - (1 + a) * κ' - star κ' * star (1 + a) + star κ' * κ' * (star a * a)) := by
        simp only [star_mul', star_inv₀, star_star, star_neg]
        ring
      rw [e, hb]
      have e2 : κ' + star κ' + 1 - (1 + a) * κ' - star κ' * star (1 + a) +
          star κ' * κ' * (star a * a) = star (1 - κ' * a) * (1 - κ' * a) := by
        simp only [star_sub, star_add, star_mul', star_one]
        ring
      rw [e2]
      field_simp
    rcases hS.unit_or a ha κ hκ (θ - star θ) hu hμ with h1 | h1
    · exact fin κ hκ hκt h1
    · refine fin (κ + (θ - star θ)) (S.add_mem hκ hμ.2.1) ?_ h1
      rw [← hκt]
      simp only [star_add, star_sub, star_star]
      ring

end ReciprocityTheory.ChartRestriction.L3.WA
end
end

section -- merged from Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.IsHermSemilocalLocRing
section -- merged from Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.AlgebraMapNeZeroOfMemHcompl
section -- merged from Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.ExistsSqAbsNormOfInert
open NumberField Module

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L3

section NoF

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem conjO_coe (x : 𝓞 K) : ((conjO K x : 𝓞 K) : K) = star (x : K) := rfl

theorem conjO_conjO (x : 𝓞 K) : conjO K (conjO K x) = x := by
  apply RingOfIntegers.ext
  simp only [conjO_coe, star_star]

theorem conjIdeal_eq_comap (P : Ideal (𝓞 K)) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P.comap (conjO K) := by
  apply le_antisymm
  · rw [Formalism.HermitianLatticesTheory.conjIdeal, Ideal.span_le]
    rintro r ⟨s, hs, h⟩
    show conjO K r ∈ P
    have hrs : conjO K r = s := by
      apply RingOfIntegers.ext
      rw [conjO_coe]
      exact (congrArg star h).trans (star_star _)
    rw [hrs]
    exact hs
  · intro r hr
    rw [Formalism.HermitianLatticesTheory.conjIdeal]
    apply Ideal.subset_span
    refine ⟨conjO K r, hr, ?_⟩
    show (r : K) = star ((conjO K r : 𝓞 K) : K)
    rw [conjO_coe, star_star]

theorem exists_sub_conjO_notMem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    ∃ θ : 𝓞 K, θ - conjO K θ ∉ P := by
  obtain ⟨-, -, h3⟩ := hK
  obtain ⟨θ, t, ht, hθ⟩ := h3 P hP
  refine ⟨θ, ?_⟩
  have htθ : conjO K θ = t := by
    apply RingOfIntegers.ext
    rw [conjO_coe]
    exact ht.symm
  rw [htθ]
  exact hθ

end NoF

section WithF

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

end WithF

end ReciprocityTheory.ChartRestriction.L3
end
end

open NumberField

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L3.WA

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem algebraMap_conjO (r : 𝓞 K) :
    algebraMap (𝓞 K) K (conjO K r) = star (algebraMap (𝓞 K) K r) := rfl

theorem conjO_conjO (r : 𝓞 K) : conjO K (conjO K r) = r := ReciprocityTheory.ChartRestriction.L3.conjO_conjO r

theorem mem_conjIdeal_iff (p : Ideal (𝓞 K)) (r : 𝓞 K) :
    r ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) p ↔ conjO K r ∈ p := by
  rw [ReciprocityTheory.ChartRestriction.L3.conjIdeal_eq_comap, Ideal.mem_comap]

theorem conjIdeal_isPrime {p : Ideal (𝓞 K)} (hp : p.IsPrime) :
    (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p).IsPrime := by
  haveI := hp
  rw [ReciprocityTheory.ChartRestriction.L3.conjIdeal_eq_comap]
  infer_instance

theorem hcompl_eq_closure (p : Ideal (𝓞 K)) :
    Formalism.HermitianLatticesTheory.hcompl (K := K) p = Submonoid.closure {s : 𝓞 K | s ∉ p ∧ conjO K s ∉ p} := by
  unfold Formalism.HermitianLatticesTheory.hcompl
  congr 1
  ext s
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun _ => ⟨fun h => h _ (algebraMap_conjO s), fun h t ht => ?_⟩
  have e : t = conjO K s := IsFractionRing.injective (𝓞 K) K (ht.trans (algebraMap_conjO s).symm)
  rw [e]
  exact h

theorem mem_hcompl_iff {p : Ideal (𝓞 K)} (hp : p.IsPrime) (s : 𝓞 K) :
    s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p ↔ s ∉ p ∧ s ∉ Formalism.HermitianLatticesTheory.conjIdeal (K := K) p := by
  rw [hcompl_eq_closure, mem_conjIdeal_iff]
  constructor
  · intro hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact hx
    | one =>
      refine ⟨fun h => hp.ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
      rw [map_one]
      exact fun h => hp.ne_top ((Ideal.eq_top_iff_one _).2 h)
    | mul x y _ _ hx hy =>
      refine ⟨fun h => (hp.mem_or_mem h).elim hx.1 hy.1, ?_⟩
      rw [map_mul]
      exact fun h => (hp.mem_or_mem h).elim hx.2 hy.2
  · intro h
    exact Submonoid.subset_closure h

theorem conjO_mem_hcompl {p : Ideal (𝓞 K)} {s : 𝓞 K} (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) :
    conjO K s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
  rw [hcompl_eq_closure] at hs ⊢
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    refine Submonoid.subset_closure ⟨hx.2, ?_⟩
    rw [ReciprocityTheory.ChartRestriction.L3.conjO_conjO]
    exact hx.1
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem algebraMap_ne_zero_of_mem_hcompl {p : Ideal (𝓞 K)} (hp : p.IsPrime) {s : 𝓞 K}
    (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) : algebraMap (𝓞 K) K s ≠ 0 := by
  intro h
  have hs0 : s = 0 := IsFractionRing.injective (𝓞 K) K (by rw [h, map_zero])
  exact ((mem_hcompl_iff hp s).1 hs).1 (by rw [hs0]; exact p.zero_mem)

theorem mem_locR_iff {p : Ideal (𝓞 K)} (hp : p.IsPrime) (a : K) :
    a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p ↔
      ∃ r : 𝓞 K, ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p,
        a = algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s := by
  rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
  constructor
  · rintro ⟨s, hs, hr⟩
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 hr
    refine ⟨r, s, hs, ?_⟩
    rw [eq_div_iff (algebraMap_ne_zero_of_mem_hcompl hp hs), hr, mul_comm]
  · rintro ⟨r, s, hs, rfl⟩
    have hne := algebraMap_ne_zero_of_mem_hcompl hp hs
    refine ⟨s, hs, Submodule.mem_one.2 ⟨r, ?_⟩⟩
    field_simp

def locRing (p : Ideal (𝓞 K)) : Subring K where
  carrier := {a | a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p}
  mul_mem' := by
    intro a b ha hb
    change a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p at ha
    change b ∈ Formalism.HermitianLatticesTheory.locR (K := K) p at hb
    change a * b ∈ Formalism.HermitianLatticesTheory.locR (K := K) p
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR] at ha hb ⊢
    obtain ⟨s, hs, h1⟩ := ha
    obtain ⟨t, ht, h2⟩ := hb
    refine ⟨s * t, mul_mem hs ht, ?_⟩
    have e : algebraMap (𝓞 K) K (s * t) * (a * b) =
        (algebraMap (𝓞 K) K s * a) * (algebraMap (𝓞 K) K t * b) := by
      rw [map_mul]; ring
    rw [e]
    exact Formalism.HermitianLatticesTheory.locDual_one_mul h1 h2
  one_mem' := by
    change (1 : K) ∈ Formalism.HermitianLatticesTheory.locR (K := K) p
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
    exact ⟨1, one_mem _, by rw [map_one, mul_one]; exact Submodule.one_le.mp le_rfl⟩
  add_mem' := fun ha hb => (Formalism.HermitianLatticesTheory.locR (K := K) p).add_mem ha hb
  zero_mem' := (Formalism.HermitianLatticesTheory.locR (K := K) p).zero_mem
  neg_mem' := fun ha => (Formalism.HermitianLatticesTheory.locR (K := K) p).neg_mem ha

theorem mem_locRing (p : Ideal (𝓞 K)) (a : K) :
    a ∈ locRing p ↔ a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := Iff.rfl

theorem algebraMap_mem_locRing (p : Ideal (𝓞 K)) (r : 𝓞 K) :
    algebraMap (𝓞 K) K r ∈ locRing p := by
  rw [mem_locRing, Formalism.HermitianLatticesTheory.locDual_mem_locR]
  refine ⟨1, one_mem _, ?_⟩
  rw [map_one, one_mul]
  exact Submodule.mem_one.2 ⟨r, rfl⟩

theorem frac_locRing (p : Ideal (𝓞 K)) (a : K) : ∃ t ∈ locRing p, t ≠ 0 ∧ t * a ∈ locRing p := by
  obtain ⟨xd, hxd⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) a
  refine ⟨algebraMap (𝓞 K) K xd.2, algebraMap_mem_locRing p _, ?_, ?_⟩
  · exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 (nonZeroDivisors.coe_ne_zero xd.2)
  · rw [mul_comm, hxd]
    exact algebraMap_mem_locRing p _

theorem star_mem_locRing {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K} (ha : a ∈ locRing p) :
    star a ∈ locRing p := by
  rw [mem_locRing, mem_locR_iff hp] at ha ⊢
  obtain ⟨r, s, hs, rfl⟩ := ha
  refine ⟨conjO K r, conjO K s, conjO_mem_hcompl hs, ?_⟩
  rw [star_div₀, algebraMap_conjO, algebraMap_conjO]

theorem isUnitIn_div_iff {p : Ideal (𝓞 K)} (hp : p.IsPrime) (r : 𝓞 K) {s : 𝓞 K}
    (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) :
    IsUnitIn (locRing p) (algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s) ↔
      r ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
  have hsne := algebraMap_ne_zero_of_mem_hcompl hp hs
  unfold IsUnitIn
  constructor
  · rintro ⟨hne, -, hinv⟩
    have hrne : algebraMap (𝓞 K) K r ≠ 0 := fun h => hne (by rw [h, zero_div])
    rw [inv_div, mem_locRing, mem_locR_iff hp] at hinv
    obtain ⟨r', s', hs', he⟩ := hinv
    have hs'ne := algebraMap_ne_zero_of_mem_hcompl hp hs'
    rw [div_eq_div_iff hrne hs'ne] at he
    have he' : s * s' = r' * r := IsFractionRing.injective (𝓞 K) K (by rw [map_mul, map_mul, he])
    have hm : s * s' ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := mul_mem hs hs'
    rw [mem_hcompl_iff hp, he'] at hm
    rw [mem_hcompl_iff hp]
    exact ⟨fun h => hm.1 (Ideal.mul_mem_left _ _ h), fun h => hm.2 (Ideal.mul_mem_left _ _ h)⟩
  · intro hr
    have hrne := algebraMap_ne_zero_of_mem_hcompl hp hr
    refine ⟨div_ne_zero hrne hsne, ?_, ?_⟩
    · rw [mem_locRing, mem_locR_iff hp]
      exact ⟨r, s, hs, rfl⟩
    · rw [inv_div, mem_locRing, mem_locR_iff hp]
      exact ⟨s, r, hr, rfl⟩

theorem unram_locRing (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {p : Ideal (𝓞 K)} (hp : p.IsMaximal) :
    ∃ θ ∈ locRing p, IsUnitIn (locRing p) (θ - star θ) := by
  obtain ⟨θ, hθ⟩ := ReciprocityTheory.ChartRestriction.L3.exists_sub_conjO_notMem hK hp
  have hpr := hp.isPrime
  have hx : θ - conjO K θ ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
    rw [mem_hcompl_iff hpr, mem_conjIdeal_iff]
    refine ⟨hθ, ?_⟩
    rw [map_sub, ReciprocityTheory.ChartRestriction.L3.conjO_conjO]
    intro h
    exact hθ (by rw [← neg_sub]; exact neg_mem h)
  refine ⟨algebraMap (𝓞 K) K θ, algebraMap_mem_locRing p θ, ?_⟩
  have hu := (isUnitIn_div_iff hpr (θ - conjO K θ) (one_mem _)).2 hx
  rwa [map_one, div_one, map_sub, algebraMap_conjO] at hu

end ReciprocityTheory.ChartRestriction.L3.WA
end
end

open NumberField

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L3.WA

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace BE

theorem exists_gen {R : Type*} [CommRing R] [IsDedekindDomain R] {I P Q : Ideal R} (hI : I ≠ ⊥)
    (hP : P.IsPrime) (hQ : Q.IsPrime) :
    ∃ r ∈ I, r ≠ 0 ∧ ∃ s : R, s ∉ P ∧ s ∉ Q ∧ ∀ x ∈ I, ∃ y : R, s * x = r * y := by
  have key : ∀ P : Ideal R, P.IsPrime → ¬ I ≤ I * P := by
    intro P hP hle
    have h1 : I * P = I * ⊤ := by
      rw [Ideal.mul_top]; exact le_antisymm Ideal.mul_le_left hle
    exact hP.ne_top (mul_left_cancel₀ hI h1)
  have h1 : ¬ ((I : Set R) ⊆ (I * P : Ideal R) ∪ (I * Q : Ideal R)) := by
    intro h
    rcases Ideal.subset_union.1 h with h | h
    · exact key P hP h
    · exact key Q hQ h
  obtain ⟨r, hrI, hr⟩ := Set.not_subset.1 h1
  have hrP : r ∉ I * P := fun h => hr (Or.inl h)
  have hrQ : r ∉ I * Q := fun h => hr (Or.inr h)
  have hr0 : r ≠ 0 := fun h => hrP (h ▸ Ideal.zero_mem _)
  have hle : Ideal.span {r} ≤ I := (Ideal.span_singleton_le_iff_mem I).2 hrI
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hmem : r ∈ I * J := hJ ▸ Ideal.mem_span_singleton_self r
  have h2 : ¬ ((J : Set R) ⊆ (P : Ideal R) ∪ (Q : Ideal R)) := by
    intro h
    rcases Ideal.subset_union.1 h with h | h
    · exact hrP (Ideal.mul_mono_right h hmem)
    · exact hrQ (Ideal.mul_mono_right h hmem)
  obtain ⟨s, hsJ, hs⟩ := Set.not_subset.1 h2
  refine ⟨r, hrI, hr0, s, fun h => hs (Or.inl h), fun h => hs (Or.inr h), fun x hx => ?_⟩
  have h3 : x * s ∈ Ideal.span {r} := hJ ▸ Ideal.mul_mem_mul hx hsJ
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h3
  exact ⟨y, by rw [mul_comm s x, ← hy, mul_comm]⟩

theorem avoid_two {R : Type*} [CommRing R] {P Q : Ideal R} (hQ : Q.IsPrime) {a s m : R} (k : R)
    (ha : a ∈ P) (hsP : s ∉ P) (hsQ : s ∉ Q) (hm : m ∉ Q) :
    (s - k * a ∉ P ∧ s - k * a ∉ Q) ∨ (s - (k + m) * a ∉ P ∧ s - (k + m) * a ∉ Q) := by
  have hP : ∀ c : R, s - c * a ∉ P := by
    intro c h
    apply hsP
    have := P.add_mem h (P.mul_mem_left c ha)
    simpa using this
  by_cases h1 : s - k * a ∈ Q
  · right
    refine ⟨hP _, fun h2 => ?_⟩
    have h3 : m * a ∈ Q := by
      have := Q.sub_mem h1 h2
      have e : s - k * a - (s - (k + m) * a) = m * a := by ring
      rwa [e] at this
    rcases hQ.mem_or_mem h3 with h | h
    · exact hm h
    · apply hsQ
      have := Q.add_mem h1 (Q.mul_mem_left k h)
      simpa using this
  · exact Or.inl ⟨hP _, h1⟩

end BE

theorem principal_locRing (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {p : Ideal (𝓞 K)} (hp : p.IsMaximal)
    (A : AddSubgroup K) (hA : ∀ s ∈ locRing p, ∀ a ∈ A, s * a ∈ A) (h0 : ∃ a ∈ A, a ≠ 0)
    (ht : ∃ t : K, t ≠ 0 ∧ ∀ a ∈ A, t * a ∈ locRing p) :
    ∃ α ∈ A, α ≠ 0 ∧ ∀ a ∈ A, a * α⁻¹ ∈ locRing p := by
  obtain ⟨t, ht0, ht⟩ := ht
  have hpp := hp.isPrime
  let I : Ideal (𝓞 K) :=
    { carrier := {r | algebraMap (𝓞 K) K r * t⁻¹ ∈ A}
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq, map_add (f := _), add_mul] at *
        exact A.add_mem hx hy
      zero_mem' := by simp
      smul_mem' := by
        intro c x hx
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, mul_assoc] at *
        exact hA _ (algebraMap_mem_locRing p c) _ hx }
  have hmemI : ∀ r : 𝓞 K, r ∈ I ↔ algebraMap (𝓞 K) K r * t⁻¹ ∈ A := fun r => Iff.rfl

  have hrep : ∀ a ∈ A, ∃ x ∈ I, ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p,
      a = algebraMap (𝓞 K) K x / (algebraMap (𝓞 K) K s * t) := by
    intro a ha
    obtain ⟨x, s, hs, hx⟩ := (mem_locR_iff hpp _).1 ((mem_locRing p _).1 (ht a ha))
    have hs0 := algebraMap_ne_zero_of_mem_hcompl hpp hs
    have e : algebraMap (𝓞 K) K x = algebraMap (𝓞 K) K s * (t * a) := by
      rw [hx]; field_simp
    refine ⟨x, ?_, s, hs, ?_⟩
    · rw [hmemI, e]
      have : algebraMap (𝓞 K) K s * (t * a) * t⁻¹ = algebraMap (𝓞 K) K s * a := by field_simp
      rw [this]
      exact hA _ (algebraMap_mem_locRing p s) _ ha
    · rw [e]; field_simp
  have hI : I ≠ ⊥ := by
    obtain ⟨a, ha, ha0⟩ := h0
    obtain ⟨x, hx, s, hs, e⟩ := hrep a ha
    intro hbot
    rw [hbot, Ideal.mem_bot] at hx
    apply ha0
    rw [e, hx]; simp
  obtain ⟨r, hrI, hr0, s, hsP, hsQ, hgen⟩ := BE.exists_gen hI hpp (conjIdeal_isPrime hpp)
  have hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := (mem_hcompl_iff hpp s).2 ⟨hsP, hsQ⟩
  have hs0 := algebraMap_ne_zero_of_mem_hcompl hpp hs
  have hr0' : algebraMap (𝓞 K) K r ≠ 0 := by
    intro h
    exact hr0 ((map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).1 h)
  refine ⟨algebraMap (𝓞 K) K r * t⁻¹, (hmemI r).1 hrI, mul_ne_zero hr0' (inv_ne_zero ht0), ?_⟩
  intro a ha
  obtain ⟨x, hx, s', hs', e⟩ := hrep a ha
  have hs0' := algebraMap_ne_zero_of_mem_hcompl hpp hs'
  obtain ⟨y, hy⟩ := hgen x hx
  have hy' : algebraMap (𝓞 K) K s * algebraMap (𝓞 K) K x
      = algebraMap (𝓞 K) K r * algebraMap (𝓞 K) K y := by
    rw [← map_mul, ← map_mul, hy]
  rw [mem_locRing, mem_locR_iff hpp]
  refine ⟨y, s * s', mul_mem hs hs', ?_⟩
  rw [e, map_mul]
  field_simp
  linear_combination hy'

theorem unit_or_locRing {p : Ideal (𝓞 K)} (hp : p.IsPrime) (a : K) (ha : a ∈ locRing p)
    (κ : K) (hκ : κ ∈ locRing p) (μ : K) (hna : a⁻¹ ∉ locRing p) (hμ : IsUnitIn (locRing p) μ) :
    IsUnitIn (locRing p) (1 - κ * a) ∨ IsUnitIn (locRing p) (1 - (κ + μ) * a) := by
  obtain ⟨a₁, s₁, hs₁, ea⟩ := (mem_locR_iff hp _).1 ((mem_locRing p _).1 ha)
  obtain ⟨k₁, s₂, hs₂, ek⟩ := (mem_locR_iff hp _).1 ((mem_locRing p _).1 hκ)
  obtain ⟨m₁, s₃, hs₃, em⟩ := (mem_locR_iff hp _).1 ((mem_locRing p _).1 hμ.2.1)
  have h1 := algebraMap_ne_zero_of_mem_hcompl hp hs₁
  have h2 := algebraMap_ne_zero_of_mem_hcompl hp hs₂
  have h3 := algebraMap_ne_zero_of_mem_hcompl hp hs₃
  have hm₁ : m₁ ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := (isUnitIn_div_iff hp m₁ hs₃).1 (em ▸ hμ)
  have ha₁ : a₁ ∉ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
    intro h
    have := (isUnitIn_div_iff hp a₁ hs₁).2 h
    rw [← ea] at this
    exact hna this.2.2
  have hQ := conjIdeal_isPrime hp
  set S : 𝓞 K := s₁ * s₂ * s₃ with hS
  have hSm : S ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := mul_mem (mul_mem hs₁ hs₂) hs₃
  have hS' := (mem_hcompl_iff hp S).1 hSm
  have hM : m₁ * s₂ ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := mul_mem hm₁ hs₂
  have hM' := (mem_hcompl_iff hp _).1 hM
  have e1 : (1 - κ * a) = algebraMap (𝓞 K) K (S - (k₁ * s₃) * a₁) / algebraMap (𝓞 K) K S := by
    rw [ea, ek, hS]; simp only [map_sub, map_mul]; field_simp
  have e2 : (1 - (κ + μ) * a)
      = algebraMap (𝓞 K) K (S - (k₁ * s₃ + m₁ * s₂) * a₁) / algebraMap (𝓞 K) K S := by
    rw [ea, ek, em, hS]; simp only [map_sub, map_mul, map_add (f := _)]; field_simp
  rw [e1, e2, isUnitIn_div_iff hp _ hSm, isUnitIn_div_iff hp _ hSm, mem_hcompl_iff hp,
    mem_hcompl_iff hp]
  have hor : a₁ ∈ p ∨ a₁ ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) p := by
    by_contra h
    push Not at h
    exact ha₁ ((mem_hcompl_iff hp a₁).2 h)
  rcases hor with h | h
  · exact BE.avoid_two hQ (k₁ * s₃) h hS'.1 hS'.2 hM'.2
  · rcases BE.avoid_two hp (k₁ * s₃) h hS'.2 hS'.1 hM'.1 with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm

theorem isHermSemilocal_locRing (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {p : Ideal (𝓞 K)}
    (hp : p.IsMaximal) : IsHermSemilocal (locRing p) :=
  ⟨fun _ ha => star_mem_locRing hp.isPrime ha, frac_locRing p, unram_locRing hK hp,
    principal_locRing hK hp, unit_or_locRing hp.isPrime⟩

end ReciprocityTheory.ChartRestriction.L3.WA
end
end

section -- merged from Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.ExistsIsomFrame
section -- merged from Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.ExistsIsomFix
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L3.WA

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

def quasiRefl (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) (a : K) : V →ₗ[K] V :=
  LinearMap.id - a • (h u).smulRight u

theorem quasiRefl_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) (a : K) (v : V) :
    quasiRefl h u a v = v - (a * h u v) • u := by
  simp [quasiRefl, smul_smul]

private theorem sesq_smul_right_eq_mul (h : V →ₗ⋆[K] V →ₗ[K] K) (c : K) (x y : V) :
    h x (c • y) = c * h x y := by
  rw [map_smul, smul_eq_mul]

theorem quasiRefl_comp (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) {a b : K}
    (hab : a + b = a * b * h u u) : quasiRefl h u a ∘ₗ quasiRefl h u b = LinearMap.id := by
  ext v
  rw [LinearMap.comp_apply, quasiRefl_apply, quasiRefl_apply, LinearMap.id_apply,
    map_sub, sesq_smul_right_eq_mul, sub_sub, ← add_smul]
  have hc : b * h u v + a * (h u v - b * h u v * h u u) = 0 := by
    linear_combination (h u v) * hab
  rw [hc, zero_smul, sub_zero]

private theorem sesq_smul_left_eq_star_mul (h : V →ₗ⋆[K] V →ₗ[K] K) (c : K) (x y : V) :
    h (c • x) y = star c * h x y := by
  rw [LinearMap.map_smulₛₗ₂, smul_eq_mul, starRingEnd_apply]

private theorem star_apply_eq_apply_swap_of_isSymm {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (x y : V) :
    star (h x y) = h y x := by
  have := LinearMap.isSymm_def.mp hs x y
  rwa [starRingEnd_apply] at this

theorem quasiRefl_isom {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (u : V) {a : K}
    (ha : a + star a = a * star a * h u u) (v w : V) :
    h (quasiRefl h u a v) (quasiRefl h u a w) = h v w := by
  have hsy := star_apply_eq_apply_swap_of_isSymm hs
  simp only [quasiRefl_apply, map_sub, LinearMap.sub_apply, sesq_smul_left_eq_star_mul,
    sesq_smul_right_eq_mul, star_mul, hsy]
  linear_combination (-(h v u * h u w)) * ha

theorem exists_isom_fix {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0)
    {x y : V} (hx : h x x = 1) (hy : h y y = 1) :
    ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, τ x = y ∧ ∀ v, h x v = 0 → h y v = 0 → τ v = v := by
  by_cases hxy : x = y
  · subst hxy
    exact ⟨1, Subgroup.one_mem _, rfl, fun v _ _ => rfl⟩
  have hsy := star_apply_eq_apply_swap_of_isSymm hs
  obtain ⟨c, hcdef⟩ : ∃ c, c = h (x - y) x := ⟨_, rfl⟩
  have hsum : c + star c = h (x - y) (x - y) := by
    rw [hcdef, hsy]
    simp only [map_sub, LinearMap.sub_apply, hx, hy]
    ring
  have hc0 : c ≠ 0 := by
    intro h0
    apply hxy
    have : h (x - y) (x - y) = 0 := by rw [← hsum, h0, star_zero, add_zero]
    exact sub_eq_zero.mp (hd _ this)
  have hs0 : star c ≠ 0 := star_ne_zero.mpr hc0
  have ha : c⁻¹ + star c⁻¹ = c⁻¹ * star c⁻¹ * h (x - y) (x - y) := by
    rw [← hsum, star_inv₀]
    field_simp
    ring
  have h1 : quasiRefl h (x - y) c⁻¹ ∘ₗ quasiRefl h (x - y) (star c⁻¹) =
      LinearMap.id := quasiRefl_comp h (x - y) ha
  have h2 : quasiRefl h (x - y) (star c⁻¹) ∘ₗ quasiRefl h (x - y) c⁻¹ =
      LinearMap.id := quasiRefl_comp h (x - y) (by rw [add_comm, ha]; ring)
  refine ⟨LinearEquiv.ofLinear _ _ h1 h2, ?_, ?_, ?_⟩
  · exact fun v w => quasiRefl_isom hs (x - y) ha v w
  · change quasiRefl h (x - y) c⁻¹ x = y
    rw [quasiRefl_apply, ← hcdef, inv_mul_cancel₀ hc0, one_smul, sub_sub_cancel]
  · intro v hxv hyv
    change quasiRefl h (x - y) c⁻¹ v = v
    rw [quasiRefl_apply, map_sub, LinearMap.sub_apply, hxv, hyv, sub_zero, mul_zero,
      zero_smul, sub_zero]

end ReciprocityTheory.ChartRestriction.L3.WA
end
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L3.WA

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

structure IsSelfDualMod (S : Subring K) (h : V →ₗ⋆[K] V →ₗ[K] K) (M : AddSubgroup V) : Prop where
  smul_mem : ∀ a ∈ S, ∀ m ∈ M, a • m ∈ M
  int : ∀ x ∈ M, ∀ y ∈ M, h x y ∈ S
  dual : ∀ x : V, (∀ m ∈ M, h m x ∈ S) → x ∈ M
  span : ∀ x : V, ∃ t : K, t ≠ 0 ∧ t • x ∈ M

variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V}

theorem exists_next (hS : IsHermSemilocal S) (hs : h.IsSymm) (hM : IsSelfDualMod S h M)
    {ι : Type*} [DecidableEq ι] (x : ι → V) (hx : ∀ i j, h (x i) (x j) = if i = j then 1 else 0)
    (s : Finset ι) (hxM : ∀ i ∈ s, x i ∈ M) (j : ι) (hj : j ∉ s) :
    ∃ z ∈ M, h z z = 1 ∧ ∀ i ∈ s, h (x i) z = 0 := by
  have hsym : ∀ u v, star (h u v) = h v u := fun u v => hs.eq u v
  let f : V →+ K :=
    { toFun := fun m => h m (x j)
      map_zero' := by simp
      map_add' := by intro a b; simp }
  have hf : ∀ m, f m = h m (x j) := fun _ => rfl
  have hAS : ∀ c ∈ S, ∀ a ∈ M.map f, c * a ∈ M.map f := by
    rintro c hc _ ⟨m, hm, rfl⟩
    refine ⟨star c • m, hM.smul_mem _ (hS.star_mem _ hc) _ hm, ?_⟩
    rw [hf, hf, map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]
  obtain ⟨t, ht0, htM⟩ := hM.span (x j)
  have h0 : ∃ a ∈ M.map f, a ≠ 0 := by
    refine ⟨_, ⟨t • x j, htM, rfl⟩, ?_⟩
    rw [hf, map_smulₛₗ, LinearMap.smul_apply, hx, if_pos rfl, smul_eq_mul, mul_one,
      starRingEnd_apply]
    exact star_ne_zero.mpr ht0
  have hb : ∀ a ∈ M.map f, t * a ∈ S := by
    rintro _ ⟨m, hm, rfl⟩
    have := hM.int m hm _ htM
    rwa [map_smul, smul_eq_mul] at this
  obtain ⟨α, ⟨w₀, hw₀, hα⟩, hα0, hdiv⟩ := hS.principal (M.map f) hAS h0 ⟨t, ht0, hb⟩
  rw [hf] at hα
  have hy₀ : α⁻¹ • x j ∈ M := by
    apply hM.dual
    intro m hm
    have := hdiv _ ⟨m, hm, rfl⟩
    rw [map_smul, smul_eq_mul, mul_comm]
    exact this
  have hyy : h (α⁻¹ • x j) (α⁻¹ • x j) = star α⁻¹ * α⁻¹ := by
    rw [map_smul, map_smulₛₗ, LinearMap.smul_apply, hx, if_pos rfl, starRingEnd_apply,
      smul_eq_mul, smul_eq_mul, mul_one, mul_comm]
  obtain ⟨b, hb1, hbS⟩ := exists_norm_one_mul_mem hS (a := α⁻¹)
    (by rw [← hyy]; exact hM.int _ hy₀ _ hy₀)
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hb1
  have hwM : w₀ - ∑ i ∈ s, h (x i) w₀ • x i ∈ M :=
    M.sub_mem hw₀ (M.sum_mem fun i hi =>
      hM.smul_mem _ (hM.int _ (hxM i hi) _ hw₀) _ (hxM i hi))
  generalize hwdef : w₀ - ∑ i ∈ s, h (x i) w₀ • x i = w at hwM
  have hxw : ∀ k, h (x k) w = h (x k) w₀ - if k ∈ s then h (x k) w₀ else 0 := by
    intro k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hwdef, map_sub, map_sum]
    congr 1
    simp only [map_smul, smul_eq_mul, hx, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
  have hyw : h (α⁻¹ • x j) w = 1 := by
    rw [map_smulₛₗ, LinearMap.smul_apply, hxw, if_neg hj, sub_zero, ← hsym w₀ (x j), hα,
      starRingEnd_apply, smul_eq_mul, ← star_mul', inv_mul_cancel₀ hα0, star_one]
  have hyy' : h (α⁻¹ • x j) (α⁻¹ • x j) = star (α⁻¹ * b) * (α⁻¹ * b) := by
    rw [hyy, star_mul']
    calc star α⁻¹ * α⁻¹ = star α⁻¹ * α⁻¹ * (star b * b) := by rw [hb1, mul_one]
      _ = _ := by ring
  obtain ⟨c, hc, d, hd, hcd⟩ := exists_norm_one_of_pair hS hs hbS
    (mul_ne_zero (inv_ne_zero hα0) hb0) hyy' hyw (hM.int w hwM w hwM)
  refine ⟨c • w + d • α⁻¹ • x j, M.add_mem (hM.smul_mem _ hc _ hwM) (hM.smul_mem _ hd _ hy₀),
    hcd, fun i hi => ?_⟩
  have hij : i ≠ j := fun e => hj (e ▸ hi)
  rw [map_add (f := _), map_smul, map_smul, map_smul, hxw, if_pos hi, sub_self, hx, if_neg hij]
  simp

theorem exists_isom_frame (hS : IsHermSemilocal S) (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0)
    (hM : IsSelfDualMod S h M) {n : ℕ} (e : Fin n → V)
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ i, g (e i) ∈ M := by
  have P : ∀ k, k ≤ n → ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ i : Fin n, i.val < k → g (e i) ∈ M := by
    intro k
    induction k with
    | zero => intro _; exact ⟨1, one_mem _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨g, hg, hgM⟩ := ih (by omega)
      have hg' : ∀ u v, h (g u) (g v) = h u v := hg
      have hx : ∀ i i', h (g (e i)) (g (e i')) = if i = i' then 1 else 0 := fun i i' => by
        rw [hg']; exact he i i'
      obtain ⟨z, hzM, hzz, hzo⟩ := exists_next hS hs hM (fun i => g (e i)) hx
        (Finset.univ.filter (fun i : Fin n => i.val < k))
        (fun i hi => hgM i (Finset.mem_filter.mp hi).2) ⟨k, hk⟩ (by simp)
      obtain ⟨τ, hτ, hτj, hτfix⟩ := exists_isom_fix hs hd (x := g (e ⟨k, hk⟩)) (y := z)
        (by rw [hx, if_pos rfl]) hzz
      refine ⟨τ * g, mul_mem hτ hg, fun i hi => ?_⟩
      show τ (g (e i)) ∈ M
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h1 | h1
      · rw [hτfix]
        · exact hgM i h1
        · rw [hx, if_neg]
          intro hc
          rw [← hc] at h1
          exact lt_irrefl _ h1
        · have := hzo i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
          rw [← hs.eq, this, map_zero]
      · have : i = ⟨k, hk⟩ := Fin.ext h1
        rw [this, hτj]
        exact hzM
  obtain ⟨g, hg, hgM⟩ := P n le_rfl
  exact ⟨g, hg, fun i => hgM i i.isLt⟩

end ReciprocityTheory.ChartRestriction.L3.WA
end
end

open NumberField Module

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L3.WA

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem smul_mem_loc {L : Submodule (𝓞 K) V} {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K}
    (ha : a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p) {m : V} (hm : m ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L) :
    a • m ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L := by
  obtain ⟨s, hs, hsa⟩ := (Formalism.HermitianLatticesTheory.locDual_mem_locR p a).mp ha
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp hsa
  obtain ⟨t, ht, htm⟩ := hm
  show ∃ u ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p, u • (a • m) ∈ L
  refine ⟨s * t, (Formalism.HermitianLatticesTheory.hcompl (K := K) p).mul_mem hs ht, ?_⟩
  have key : (s * t) • (a • m) = r • (t • m) := by
    rw [← algebraMap_smul K (s * t) (a • m), ← algebraMap_smul K r (t • m),
      ← algebraMap_smul K t m, smul_smul, smul_smul, hr, map_mul]
    congr 1
    ring
  rw [key]
  exact L.smul_mem r htm

private theorem mem_locR_of_unimod_lemma {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    {p : Ideal (𝓞 K)} (hu : Formalism.HermitianLatticesTheory.IsUnimodularAt h p L) {x y : V}
    (hx : x ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L) (hy : y ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L) :
    h x y ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by
  have hu' : Formalism.HermitianLatticesTheory.dualAt h p (Formalism.HermitianLatticesTheory.loc (K := K) p L) = Formalism.HermitianLatticesTheory.loc (K := K) p L := hu
  have hy2 : y ∈ Formalism.HermitianLatticesTheory.dualAt h p (Formalism.HermitianLatticesTheory.loc (K := K) p L) := by
    rw [hu']
    exact hy
  simp only [Formalism.HermitianLatticesTheory.dualAt, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply] at hy2
  exact hy2 x hx

private theorem mem_loc_of_mem_lemma_3 {L : Submodule (𝓞 K) V} (p : Ideal (𝓞 K)) {x : V}
    (hx : x ∈ L) : x ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L := by
  show ∃ u ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p, u • x ∈ L
  exact ⟨1, (Formalism.HermitianLatticesTheory.hcompl (K := K) p).one_mem, by rw [one_smul]; exact hx⟩

theorem isSelfDualMod_loc {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) {p : Ideal (𝓞 K)} (hp : p.IsPrime)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodularAt h p L) :
    IsSelfDualMod (locRing p) h (Formalism.HermitianLatticesTheory.loc (K := K) p L).toAddSubgroup := by
  have hu' : ∀ x, x ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L ↔
      ∀ y ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L, h y x ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by
    intro x
    rw [← Formalism.HermitianLatticesTheory.locDual_mem_dualAt]
    unfold Formalism.HermitianLatticesTheory.IsUnimodularAt at hu
    rw [hu]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha m hm
    exact smul_mem_loc hp ha hm
  · intro x hx y hy
    exact (hu' y).mp hy x hx
  · intro x hx
    exact (hu' x).mpr hx
  · intro x
    obtain ⟨n, hn, hnx⟩ := Formalism.HermitianLatticesTheory.traceReal_mult L hL x
    refine ⟨(n : K), by exact_mod_cast hn, ?_⟩
    rw [Int.cast_smul_eq_zsmul]
    exact Formalism.HermitianLatticesTheory.locBasic_le_locS _ L hnx

private theorem mem_loc_of_smul_lemma_2 {L : Submodule (𝓞 K) V} {p : Ideal (𝓞 K)} {s : 𝓞 K}
    (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) {y : V}
    (hy : s • y ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L) : y ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L := by
  obtain ⟨t, ht, hty⟩ := hy
  show ∃ u ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p, u • y ∈ L
  exact ⟨t * s, (Formalism.HermitianLatticesTheory.hcompl (K := K) p).mul_mem ht hs, by rw [mul_smul]; exact hty⟩

theorem gmap_loc_eq_of_frame {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    {p : Ideal (𝓞 K)} (hp : p.IsPrime) (hu : Formalism.HermitianLatticesTheory.IsUnimodularAt h p L) {n : ℕ} {e : Fin n → V}
    (hspan : Submodule.span K (Set.range e) = ⊤)
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) {g : V ≃ₗ[K] V}
    (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (hge : ∀ i, g (e i) ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L) :
    Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.loc (K := K) p (Submodule.span (𝓞 K) (Set.range e))) =
      Formalism.HermitianLatticesTheory.loc (K := K) p L := by
  have hg' : ∀ x y, h (g x) (g y) = h x y := hg
  apply le_antisymm
  · intro y hy
    simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨s, hs, hsx⟩ := hx
    refine mem_loc_of_smul_lemma_2 hs ?_
    have hN : Submodule.span (𝓞 K) (Set.range e) ≤
        (Formalism.HermitianLatticesTheory.loc (K := K) p L).comap ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hge i
    have h1 := hN hsx
    rw [Submodule.mem_comap, map_smul ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) s x] at h1
    exact h1
  · intro y hy
    have hz : g.symm y ∈ Submodule.span K (Set.range e) := by
      rw [hspan]
      exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hz
    obtain ⟨c, hc⟩ := hz
    have hcj : ∀ j, c j ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by
      intro j
      have e2 : h (g (e j)) y = h (e j) (g.symm y) := by
        conv_lhs => rw [← g.apply_symm_apply y]
        exact hg' _ _
      have e1 : c j = h (g (e j)) y := by
        rw [e2, ← hc]
        set_option synthInstance.maxHeartbeats 100000 in
          simp [map_sum, he]
      rw [e1]
      exact mem_locR_of_unimod_lemma hu (hge j) hy
    have hzN : g.symm y ∈ Formalism.HermitianLatticesTheory.loc (K := K) p (Submodule.span (𝓞 K) (Set.range e)) := by
      rw [← hc]
      refine sum_mem (fun i _ => ?_)
      exact smul_mem_loc hp (hcj i) (mem_loc_of_mem_lemma_3 p (Submodule.subset_span ⟨i, rfl⟩))
    simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
    exact ⟨g.symm y, hzN, by simp⟩

end ReciprocityTheory.ChartRestriction.L3.WA
