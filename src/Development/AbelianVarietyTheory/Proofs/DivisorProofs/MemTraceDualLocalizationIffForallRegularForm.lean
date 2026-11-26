module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularTopFormPoleOrderHeightOnePrimeStatement
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMemLocalizationIffForallPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowDvdDifferentIdealIffPowSuccDvdMap
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.TameDifferent

private theorem trace_add_of_short_exact {k A M C : Type*} [Field k]
    [AddCommGroup A] [Module k A] [AddCommGroup M] [Module k M] [AddCommGroup C] [Module k C]
    [Module.Finite k M] (f : A →ₗ[k] M) (g : M →ₗ[k] C) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : ∀ a, g (f a) = 0) (hex : ∀ m, g m = 0 → ∃ a, f a = m)
    (α : A →ₗ[k] A) (φ : M →ₗ[k] M) (γ : C →ₗ[k] C)
    (h1 : ∀ a, φ (f a) = f (α a)) (h2 : ∀ m, g (φ m) = γ (g m)) :
    LinearMap.trace k M φ = LinearMap.trace k A α + LinearMap.trace k C γ := by
  have : Module.Finite k A := Module.Finite.of_injective f hf
  have : Module.Finite k C := Module.Finite.of_surjective g hg
  obtain ⟨s, hs⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hg)
  obtain ⟨l, hl⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hf)
  have hs' : ∀ c, g (s c) = c := fun c => LinearMap.congr_fun hs c
  have hl' : ∀ a, l (f a) = a := fun a => LinearMap.congr_fun hl a
  let r : M →ₗ[k] A := l ∘ₗ (LinearMap.id - s ∘ₗ g)
  have hr : ∀ m, f (r m) = m - s (g m) := by
    intro m
    obtain ⟨a, ha⟩ := hex (m - s (g m)) (by simp [hs'])
    have : r m = a := by
      simp only [r, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
      rw [← ha, hl']
    rw [this, ha]
  have hrf : ∀ a, r (f a) = a := by
    intro a
    apply hf
    rw [hr, hfg, map_zero, sub_zero]
  have hφ : φ = (φ ∘ₗ f) ∘ₗ r + (φ ∘ₗ s) ∘ₗ g := by
    ext m
    simp [hr]
  have e1 : r ∘ₗ (φ ∘ₗ f) = α := by
    ext a
    simp only [LinearMap.comp_apply, h1, hrf]
  have e2 : g ∘ₗ (φ ∘ₗ s) = γ := by
    ext c
    simp only [LinearMap.comp_apply, h2, hs']
  calc LinearMap.trace k M φ
      = LinearMap.trace k M ((φ ∘ₗ f) ∘ₗ r) + LinearMap.trace k M ((φ ∘ₗ s) ∘ₗ g) := by
        rw [← map_add (f := _), ← hφ]
    _ = _ := by
        rw [LinearMap.trace_comp_comm' r (φ ∘ₗ f), LinearMap.trace_comp_comm' g (φ ∘ₗ s), e1, e2]

theorem trace_quotient_pow {k B : Type*} [Field k] [CommRing B] [IsDedekindDomain B]
    (P : Ideal B) [P.IsMaximal] (hP : P ≠ ⊥) (e : ℕ)
    [Algebra k (B ⧸ P ^ (e + 1))] [Algebra k (B ⧸ P)] [Module.Finite k (B ⧸ P ^ (e + 1))]
    (h : ∀ c : k, Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero e))
      (algebraMap k (B ⧸ P ^ (e + 1)) c) = algebraMap k (B ⧸ P) c) (x : B) :
    Algebra.trace k (B ⧸ P ^ (e + 1)) (Ideal.Quotient.mk _ x) =
      (e + 1 : k) * Algebra.trace k (B ⧸ P) (Ideal.Quotient.mk _ x) := by
  rename_i hmax instA instP instF
  revert h instF instA
  induction e with
  | zero =>
    intro instA instF h
    have hbij : Function.Bijective
        (Ideal.Quotient.factor (Ideal.pow_le_self (I := P) (Nat.succ_ne_zero 0))) := by
      refine ⟨?_, Ideal.Quotient.factor_surjective _⟩
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hy
      rw [Ideal.Quotient.eq_zero_iff_mem]
      simpa using hy
    let g : (B ⧸ P ^ (0 + 1)) →ₐ[k] B ⧸ P :=
      { toRingHom := Ideal.Quotient.factor (Ideal.pow_le_self (Nat.succ_ne_zero 0))
        commutes' := h }
    have := Algebra.trace_eq_of_algEquiv (AlgEquiv.ofBijective g hbij) (Ideal.Quotient.mk _ x)
    rw [← this]
    simp [g]
  | succ e ih =>
    intro instA instF h
    have hle : P ^ (e + 1 + 1) ≤ P ^ (e + 1) := Ideal.pow_le_pow_right (Nat.le_succ _)
    let instB : Algebra k (B ⧸ P ^ (e + 1)) :=
      ((Ideal.Quotient.factor hle).comp (algebraMap k (B ⧸ P ^ (e + 1 + 1)))).toAlgebra
    let g : (B ⧸ P ^ (e + 1 + 1)) →ₐ[k] B ⧸ P ^ (e + 1) :=
      { toRingHom := Ideal.Quotient.factor hle
        commutes' := fun _ => rfl }
    have hgmk : ∀ y : B, g (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ y := fun _ => rfl
    have hg : Function.Surjective g := Ideal.Quotient.factor_surjective hle
    have instG : Module.Finite k (B ⧸ P ^ (e + 1)) := Module.Finite.of_surjective g.toLinearMap hg
    have ih' := @ih instB instG (by
      intro c
      rw [← h c]
      change Ideal.Quotient.factor _ (Ideal.Quotient.factor hle (algebraMap k _ c)) = _
      obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (algebraMap k (B ⧸ P ^ (e + 1 + 1)) c)
      rw [← hz]
      rfl)
    obtain ⟨a, ha, ha'⟩ := Ideal.exists_mem_pow_notMem_pow_succ P hP hmax.ne_top (e + 1)
    let f0 : (B ⧸ P) →ₗ[B] B ⧸ P ^ (e + 1 + 1) :=
      Submodule.mapQ P (P ^ (e + 1 + 1) : Ideal B) (LinearMap.mul B B a) (by
        intro y hy
        change a * y ∈ P ^ (e + 1 + 1)
        rw [pow_succ P (e + 1)]
        exact Ideal.mul_mem_mul ha hy)
    have hf0 : ∀ y : B, f0 (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ (a * y) := fun _ => rfl
    let f : (B ⧸ P) →ₗ[k] B ⧸ P ^ (e + 1 + 1) :=
      { toFun := f0
        map_add' := f0.map_add
        map_smul' := by
          intro c y
          obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
          obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (algebraMap k (B ⧸ P ^ (e + 1 + 1)) c)
          rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, ← h c, ← hz,
            Ideal.Quotient.factor_mk, ← map_mul, hf0, hf0, ← map_mul]
          congr 1
          ring }
    have hf : ∀ y : B, f (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ (a * y) := fun _ => rfl
    have key := trace_add_of_short_exact f g.toLinearMap ?_ hg ?_ ?_
      (Algebra.lmul k _ (Ideal.Quotient.mk _ x)) (Algebra.lmul k _ (Ideal.Quotient.mk _ x))
      (Algebra.lmul k _ (Ideal.Quotient.mk _ x)) ?_ ?_
    · rw [← Algebra.trace_apply, ← Algebra.trace_apply, ← Algebra.trace_apply] at key
      rw [key, ih']
      push_cast
      ring
    · set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [hf, Ideal.Quotient.eq_zero_iff_mem] at hy
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact (Ideal.IsMaximal.mem_pow_mul P hy).resolve_left ha'
    · intro y
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [hf, AlgHom.toLinearMap_apply, hgmk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ ha
    · intro m hm
      obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
      rw [AlgHom.toLinearMap_apply, hgmk, Ideal.Quotient.eq_zero_iff_mem] at hm
      have hsup : P ^ (e + 1 + 1) ⊔ Ideal.span {a} = P ^ (e + 1) := by
        refine Ideal.eq_prime_pow_of_succ_lt_of_le hP ?_ ?_
        · refine lt_of_le_of_ne le_sup_left fun hh => ha' ?_
          rw [hh]
          exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
        · exact sup_le hle ((Ideal.span_singleton_le_iff_mem _).2 ha)
      rw [← hsup] at hm
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hm
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hw
      refine ⟨Ideal.Quotient.mk _ y, ?_⟩
      rw [hf, map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.2 hu, zero_add, mul_comm]
    · intro y
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      change Ideal.Quotient.mk _ x * f (Ideal.Quotient.mk _ y) =
        f (Ideal.Quotient.mk _ x * Ideal.Quotient.mk _ y)
      rw [← map_mul, hf, hf, ← map_mul]
      congr 1
      ring
    · intro m
      change g (Ideal.Quotient.mk _ x * m) = Ideal.Quotient.mk _ x * g m
      rw [map_mul, hgmk]

end GlobalTheory.TameDifferent

namespace GlobalTheory.TameDifferent

open nonZeroDivisors Module

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
  [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] [Module.Finite A B]

theorem intTrace_mk_eq
    {p : Ideal A} [p.IsMaximal] (P Q : Ideal B) [P.IsMaximal] [P.LiesOver p] (hP0 : P ≠ ⊥)
    (n : ℕ) (hPQ : IsCoprime P Q) (hP : P ^ (n + 1) * Q = Ideal.map (algebraMap A B) p)
    (x : B) (hx : x ∈ Q) :
    Ideal.Quotient.mk p (Algebra.intTrace A B x) =
      ((n + 1 : ℕ) : A ⧸ p) * Algebra.trace (A ⧸ p) (B ⧸ P) (Ideal.Quotient.mk _ x) := by
  let : Algebra (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap (by
      rw [← Ideal.map_le_iff_le_comap, ← hP]
      exact Ideal.mul_le_right)
  have : IsScalarTower A (A ⧸ p) (B ⧸ Q) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ p) (B ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ Q)
  let : Algebra (A ⧸ p) (B ⧸ P ^ (n + 1)) := Ideal.Quotient.algebraQuotientOfLEComap (by
      rw [← Ideal.map_le_iff_le_comap, ← hP]
      exact Ideal.mul_le_left)
  have : IsScalarTower A (A ⧸ p) (B ⧸ P ^ (n + 1)) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ p) (B ⧸ P ^ (n + 1)) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ P ^ (n + 1))
  let e : (B ⧸ p.map (algebraMap A B)) ≃ₐ[A ⧸ p] ((B ⧸ P ^ (n + 1)) × B ⧸ Q) :=
    { __ := (Ideal.quotEquivOfEq hP.symm).trans
        (Ideal.quotientMulEquivQuotientProd _ Q hPQ.pow_left),
      commutes' := Quotient.ind fun _ ↦ rfl }
  have hx' : (e (Ideal.Quotient.mk _ x)).2 = 0 := by
    simpa [e, Ideal.Quotient.eq_zero_iff_mem]
  have hx'' : (e (Ideal.Quotient.mk _ x)).1 = Ideal.Quotient.mk _ x := by
    simp [e]
  let := Ideal.Quotient.field p
  rw [← Algebra.trace_quotient_eq_of_isDedekindDomain, ← Algebra.trace_eq_of_algEquiv e,
    Algebra.trace_prod_apply, hx', hx'', map_zero, add_zero, Nat.cast_add, Nat.cast_one]
  refine trace_quotient_pow P hP0 n ?_ x
  intro c
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  rfl

theorem not_pow_dvd_differentIdeal [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsMaximal] (P Q : Ideal B) [P.IsMaximal] [P.LiesOver p]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)] (hP0 : P ≠ ⊥)
    (n : ℕ) (hPQ : IsCoprime P Q) (hP : P ^ (n + 1) * Q = Ideal.map (algebraMap A B) p)
    (hn : ((n + 1 : ℕ) : A ⧸ p) ≠ 0) :
    ¬ P ^ (n + 1) ∣ differentIdeal A B := by
  intro h
  let := Ideal.Quotient.field p
  let := Ideal.Quotient.field P
  obtain ⟨x, hx⟩ : ∃ x, Algebra.trace (A ⧸ p) (B ⧸ P) x ≠ 0 := by
    simpa [LinearMap.ext_iff] using Algebra.trace_ne_zero (A ⧸ p) (B ⧸ P)
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h1 : x ∈ P ⊔ Q := by
    rw [Ideal.isCoprime_iff_sup_eq.mp hPQ]; trivial
  obtain ⟨u, hu, y, hy, rfl⟩ := Submodule.mem_sup.mp h1
  rw [map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.mpr hu, zero_add] at hx
  refine not_dvd_differentIdeal_of_intTrace_not_mem A _ Q hP y hy ?_ h
  rw [← Ideal.Quotient.eq_zero_iff_mem, intTrace_mk_eq P Q hP0 n hPQ hP y hy]
  exact mul_ne_zero hn hx

end GlobalTheory.TameDifferent

namespace GlobalTheory.TameDifferent

open nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem pow_dvd_differentIdeal_iff_pow_succ_dvd_map : ∀ (A B : Type) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [CharZero (IsLocalRing.ResidueField A)] (Q : Ideal B) [Q.IsMaximal]
    [Q.LiesOver (IsLocalRing.maximalIdeal A)] (n : ℕ),
    Q ^ n ∣ differentIdeal A B ↔ Q ^ (n + 1) ∣ (IsLocalRing.maximalIdeal A).map (algebraMap A B) := by
  intro A B _ _ _ _ _ _ _ _ _ Q _ _ n
  have hm : IsLocalRing.maximalIdeal A ≠ ⊥ := IsDiscreteValuationRing.not_a_field A
  have hm' : (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective A B)).not.mpr hm
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hm Q
  obtain ⟨R, h₁, h₂⟩ := Ideal.eq_prime_pow_mul_coprime hm' Q
  set e := Multiset.count Q
    (UniqueFactorizationMonoid.normalizedFactors ((IsLocalRing.maximalIdeal A).map (algebraMap A B)))
  have hQm : Q ∣ (IsLocalRing.maximalIdeal A).map (algebraMap A B) :=
    Ideal.dvd_iff_le.mpr (Ideal.map_le_iff_le_comap.mpr Ideal.LiesOver.over.le)
  have hk : ∀ k, Q ^ k ∣ (IsLocalRing.maximalIdeal A).map (algebraMap A B) ↔ k ≤ e := by
    intro k
    constructor
    · intro h
      by_contra hlt
      push_neg at hlt
      have h3 : Q ^ e * Q ∣ Q ^ e * R := by
        rw [← pow_succ, ← h₂]
        exact (pow_dvd_pow Q hlt).trans h
      have h4 : Q ∣ R := (mul_dvd_mul_iff_left (pow_ne_zero _ hQ0)).mp h3
      have h5 : R ≤ Q := Ideal.dvd_iff_le.mp h4
      apply (Ideal.IsMaximal.ne_top ‹Q.IsMaximal›)
      rw [← h₁]
      exact le_antisymm le_sup_left (sup_le le_rfl h5)
    · intro h
      rw [h₂]
      exact (pow_dvd_pow Q h).trans (dvd_mul_right _ _)
  have he : e ≠ 0 := by
    have := (hk 1).mp (by simpa using hQm)
    omega
  obtain ⟨k, hke⟩ := Nat.exists_eq_succ_of_ne_zero he
  have : CharZero A := RingHom.charZero (IsLocalRing.residue A)
  have : CharZero (FractionRing A) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective A (FractionRing A))
  have : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  have : Algebra.IsSeparable (FractionRing A) (FractionRing B) := inferInstance
  have hc : CharZero (A ⧸ IsLocalRing.maximalIdeal A) :=
    inferInstanceAs (CharZero (IsLocalRing.ResidueField A))
  have : Algebra.IsSeparable (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ Q) := by
    let := Ideal.Quotient.field (IsLocalRing.maximalIdeal A)
    let := Ideal.Quotient.field Q
    infer_instance
  have hD1 : Q ^ (e - 1) ∣ differentIdeal A B :=
    pow_sub_one_dvd_differentIdeal A Q e hm ((hk e).mpr le_rfl)
  have hD2 : ¬ Q ^ e ∣ differentIdeal A B := by
    rw [hke]
    refine not_pow_dvd_differentIdeal (p := IsLocalRing.maximalIdeal A) Q R hQ0 k (Ideal.isCoprime_iff_sup_eq.mpr h₁) ?_ ?_
    · rw [h₂, hke]
    · exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  rw [hk (n + 1)]
  constructor
  · intro h
    by_contra hlt
    exact hD2 ((pow_dvd_pow Q (by omega)).trans h)
  · intro h
    exact (pow_dvd_pow Q (by omega)).trans hD1

end GlobalTheory.TameDifferent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMemLocalizationIffForallPrime
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.CodimDual

theorem loc_pow {B : Type} [CommRing B] (Q : Ideal B) [hQ : Q.IsPrime] (s : B)
    (hs : ∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) (n : ℕ) :
    ∀ y ∈ Q ^ n, ∃ c r : B, r ∉ Q ∧ r * y = c * s ^ n := by
  induction n with
  | zero => exact fun y _ => ⟨y, 1, (Ideal.ne_top_iff_one Q).1 hQ.ne_top, by simp⟩
  | succ n ih =>
    intro y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro m hm x hx
      obtain ⟨c, r, hr, e⟩ := ih m hm
      obtain ⟨c', r', hr', e'⟩ := hs x hx
      refine ⟨c * c', r * r', fun h => (hQ.mem_or_mem h).elim hr hr', ?_⟩
      linear_combination (r' * x) * e + (c * s ^ n) * e'
    · rintro x x' ⟨c, r, hr, e⟩ ⟨c', r', hr', e'⟩
      refine ⟨r' * c + r * c', r * r', fun h => (hQ.mem_or_mem h).elim hr hr', ?_⟩
      linear_combination r' * e + r * e'

theorem exact_exponent {B : Type} [CommRing B] [IsDedekindDomain B] (Q : Ideal B) [hQ : Q.IsPrime] (h0 : Q ≠ ⊥)
    (s : B) (hsQ : s ∈ Q) (hs : ∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) (e : ℕ) (x a r : B)
    (ha : a ∉ Q) (hr : r ∉ Q) (h : r * x = a * s ^ e) : x ∈ Q ^ e ∧ x ∉ Q ^ (e + 1) := by
  refine ⟨(Ideal.IsPrime.mul_mem_pow Q (a := r) ?_).resolve_left hr, fun hx => ?_⟩
  · rw [h]; exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hsQ e)
  · have h1 : s ^ e ∈ Q ^ (e + 1) :=
      (Ideal.IsPrime.mul_mem_pow Q (a := a) (h ▸ Ideal.mul_mem_left _ _ hx)).resolve_left ha
    refine (Ideal.pow_succ_lt_pow h0 e).not_ge fun y hy => ?_
    obtain ⟨c', r', hr', e'⟩ := loc_pow Q s hs e y hy
    exact (Ideal.IsPrime.mul_mem_pow Q (a := r') (e' ▸ Ideal.mul_mem_left _ _ h1)).resolve_left hr'

section Core

variable {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B] [CharZero (IsLocalRing.ResidueField A)]

theorem different_exponent (π : A) (hπ : IsLocalRing.maximalIdeal A = Ideal.span {π}) (Q : Ideal B) [hQ : Q.IsPrime]
    (s : B) (e : ℕ) (he : 1 ≤ e) (hsQ : s ∈ Q) (hs : ∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) (a r : B)
    (ha : a ∉ Q) (hr : r ∉ Q) (h : r * algebraMap A B π = a * s ^ e) :
    Q ^ (e - 1) ∣ differentIdeal A B ∧ ¬ Q ^ e ∣ differentIdeal A B := by
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact IsDiscreteValuationRing.not_a_field A (by simpa using hπ)
  have hπQ : algebraMap A B π ∈ Q := (hQ.mem_or_mem (x := r)
    (h ▸ Q.mul_mem_left _ (Q.pow_mem_of_mem hsQ e he))).resolve_left hr
  have h0 : Q ≠ ⊥ := by
    rintro rfl
    exact hπ0 ((FaithfulSMul.algebraMap_injective A B) (by simpa using hπQ))
  haveI : Q.IsMaximal := hQ.isMaximal h0
  haveI : Q.LiesOver (IsLocalRing.maximalIdeal A) :=
    ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) Q)).symm⟩
  obtain ⟨h1, h2⟩ := exact_exponent Q h0 s hsQ hs e _ a r ha hr h
  rw [GlobalTheory.TameDifferent.pow_dvd_differentIdeal_iff_pow_succ_dvd_map A B Q, GlobalTheory.TameDifferent.pow_dvd_differentIdeal_iff_pow_succ_dvd_map A B Q, hπ, Ideal.map_span, Set.image_singleton, Nat.sub_add_cancel he,
    Ideal.dvd_span_singleton, Ideal.dvd_span_singleton]
  exact ⟨h1, h2⟩

variable (F K : Type) [Field F] [Field K] [Algebra A F] [IsFractionRing A F] [Algebra B K] [IsFractionRing B K]
  [Algebra F K] [Algebra A K] [IsScalarTower A F K] [IsScalarTower A B K] [FiniteDimensional F K]
  [Algebra.IsSeparable F K]


omit [CharZero (IsLocalRing.ResidueField A)] in
theorem trace_mem_iff (z : K) :
    (∀ b : B, Algebra.trace F K (z * algebraMap B K b) ∈ (algebraMap A F).range) ↔
      ∀ d ∈ differentIdeal A B, ∃ c : B, algebraMap B K c = z * algebraMap B K d := by
  haveI : IsIntegralClosure B A K := IsIntegralClosure.of_isIntegrallyClosed B A K
  have h1 : (∀ b : B, Algebra.trace F K (z * algebraMap B K b) ∈ (algebraMap A F).range) ↔
      z ∈ FractionalIdeal.dual A F (1 : FractionalIdeal (nonZeroDivisors B) K) := by
    rw [FractionalIdeal.mem_dual (I := (1 : FractionalIdeal (nonZeroDivisors B) K)) one_ne_zero]
    constructor
    · intro h a ha
      obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      exact h b
    · intro h b
      exact h _ ((FractionalIdeal.mem_one_iff _).2 ⟨b, rfl⟩)
  have h2 := coeIdeal_differentIdeal A F K B
  have h3 : ((differentIdeal A B : Ideal B) : FractionalIdeal (nonZeroDivisors B) K) ≠ 0 := by
    rw [h2]; exact inv_ne_zero (FractionalIdeal.dual_ne_zero A F one_ne_zero)
  rw [h1, ← inv_inv (FractionalIdeal.dual A F (1 : FractionalIdeal (nonZeroDivisors B) K)), ← h2,
    FractionalIdeal.mem_inv_iff h3]
  constructor
  · intro h d hd
    exact (FractionalIdeal.mem_one_iff _).1 (h _ (FractionalIdeal.mem_coeIdeal_of_mem _ hd))
  · intro h y hy
    obtain ⟨d, hd, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact (FractionalIdeal.mem_one_iff _).2 (h d hd)

theorem core_mp (π : A) (hπ : IsLocalRing.maximalIdeal A = Ideal.span {π}) (z : K)
    (hz : ∀ b : B, Algebra.trace F K (z * algebraMap B K b) ∈ (algebraMap A F).range) (Q : Ideal B) [hQ : Q.IsPrime]
    (s : B) (e : ℕ) (he : 1 ≤ e) (hsQ : s ∈ Q) (hs : ∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) (a r : B)
    (ha : a ∉ Q) (hr : r ∉ Q) (h : r * algebraMap A B π = a * s ^ e) :
    ∃ c r : B, r ∉ Q ∧ algebraMap B K r * (algebraMap B K s ^ (e - 1) * z) = algebraMap B K c := by
  obtain ⟨⟨J, hJ⟩, h2⟩ := different_exponent π hπ Q s e he hsQ hs a r ha hr h
  have hJQ : ¬ J ≤ Q := fun hle => h2 (by
    rw [hJ]
    nth_rewrite 1 [← Nat.sub_add_cancel he]
    rw [pow_succ]
    exact mul_dvd_mul_left _ (Ideal.dvd_iff_le.2 hle))
  obtain ⟨j, hj, hjQ⟩ := SetLike.not_le_iff_exists.1 hJQ
  obtain ⟨c, hc⟩ := (trace_mem_iff F K z).1 hz (s ^ (e - 1) * j)
    (hJ ▸ Ideal.mul_mem_mul (Ideal.pow_mem_pow hsQ _) hj)
  refine ⟨c, j, hjQ, ?_⟩
  rw [hc, map_mul, map_pow]; ring

theorem core_mpr (π : A) (hπ : IsLocalRing.maximalIdeal A = Ideal.span {π}) (z : K)
    (hz : ∀ Q : Ideal B, Q.IsMaximal → ∃ (s : B) (e : ℕ), 1 ≤ e ∧ s ∈ Q ∧ (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) ∧
      (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ r * algebraMap A B π = a * s ^ e) ∧
      ∃ c r : B, r ∉ Q ∧ algebraMap B K r * (algebraMap B K s ^ (e - 1) * z) = algebraMap B K c) :
    ∀ b : B, Algebra.trace F K (z * algebraMap B K b) ∈ (algebraMap A F).range := by
  rw [trace_mem_iff (A := A) F K z]
  intro d hd
  let I : Ideal B := (LinearMap.range (Algebra.linearMap B K)).comap
    (LinearMap.toSpanSingleton B K (z * algebraMap B K d))
  have hI : ∀ r : B, r ∈ I ↔ ∃ c : B, algebraMap B K c = algebraMap B K r * (z * algebraMap B K d) := by
    intro r
    simp only [I, Submodule.mem_comap, LinearMap.mem_range, LinearMap.toSpanSingleton_apply, Algebra.smul_def,
      Algebra.linearMap_apply]
  have htop : I = ⊤ := by
    by_contra hne
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨s, e, he, hsQ, hs, ⟨a, r, ha, hr, h⟩, c, r', hr', hc⟩ := hz Q hQ
    obtain ⟨h1, -⟩ := different_exponent π hπ Q s e he hsQ hs a r ha hr h
    obtain ⟨c', r'', hr'', e'⟩ := loc_pow Q s hs (e - 1) d (Ideal.dvd_iff_le.1 h1 hd)
    refine (hQ.isPrime.mem_or_mem (hle ((hI (r' * r'')).2 ⟨c * c', ?_⟩))).elim hr' hr''
    have e2 := congrArg (algebraMap B K) e'
    simp only [map_mul, map_pow] at e2 ⊢
    linear_combination (-algebraMap B K c') * hc - (algebraMap B K r' * z) * e2
  obtain ⟨c, hc⟩ := (hI 1).1 (htop ▸ Submodule.mem_top)
  exact ⟨c, by simpa using hc⟩

end Core

section Transfer

variable {B B' : Type} [CommRing B] [CommRing B'] [Algebra B B'] (M : Submonoid B) [IsLocalization M B']


include M in
theorem gen_up (Q' : Ideal B') [hQ : Q'.IsPrime] (s : B)
    (hs : ∀ y ∈ Q'.under B, ∃ c r : B, r ∉ Q'.under B ∧ r * y = c * s) :
    ∀ y ∈ Q', ∃ c r : B', r ∉ Q' ∧ r * y = c * algebraMap B B' s := by
  intro y hy
  obtain ⟨⟨b, m⟩, hb⟩ := IsLocalization.surj M y
  obtain ⟨c, r, hr, e⟩ := hs b (by
    rw [Ideal.under_def, Ideal.mem_comap, ← hb]; exact Q'.mul_mem_right _ hy)
  refine ⟨algebraMap B B' c, algebraMap B B' r * algebraMap B B' m, fun h => (hQ.mem_or_mem h).elim hr fun hm => ?_, ?_⟩
  · exact hQ.ne_top (Q'.eq_top_of_isUnit_mem hm (IsLocalization.map_units B' m))
  · have e2 := congrArg (algebraMap B B') e
    simp only [map_mul] at e2 hb
    linear_combination e2 + algebraMap B B' r * hb


include M in
theorem loc_down {K : Type} [CommRing K] [Algebra B K] [Algebra B' K] [IsScalarTower B B' K] (Q' : Ideal B')
    [hQ : Q'.IsPrime] (w : K) (c r : B') (hr : r ∉ Q') (h : algebraMap B' K r * w = algebraMap B' K c) :
    ∃ c r : B, r ∉ Q'.under B ∧ algebraMap B K r * w = algebraMap B K c := by
  obtain ⟨⟨r0, m1⟩, h1⟩ := IsLocalization.surj M r
  obtain ⟨⟨c0, m2⟩, h2⟩ := IsLocalization.surj M c
  have hu : ∀ m : M, algebraMap B B' m ∉ Q' := fun m hm =>
    hQ.ne_top (Q'.eq_top_of_isUnit_mem hm (IsLocalization.map_units B' m))
  refine ⟨c0 * m1, r0 * m2, fun hm => ?_, ?_⟩
  · rw [Ideal.under_def, Ideal.mem_comap, map_mul, ← h1] at hm
    exact (hQ.mem_or_mem hm).elim (fun h' => (hQ.mem_or_mem h').elim hr (hu m1)) (hu m2)
  · have e1 := congrArg (algebraMap B' K) h1
    have e2 := congrArg (algebraMap B' K) h2
    simp only [map_mul, ← IsScalarTower.algebraMap_apply] at e1 e2 ⊢
    linear_combination (algebraMap B K m1 * algebraMap B K m2) * h - (algebraMap B K m2 * w) * e1
      + algebraMap B K m1 * e2

end Transfer

theorem mem_range_iff {A F A' : Type} [CommRing A] [CommRing A'] [Field F] [Algebra A F] [IsFractionRing A F]
    [Algebra A A'] [Algebra A' F] [IsScalarTower A A' F] (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime A' p] (x : F) :
    x ∈ (algebraMap A' F).range ↔ ∃ r c : A, r ∉ p ∧ algebraMap A F r * x = algebraMap A F c := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨⟨c, r⟩, h⟩ := IsLocalization.surj p.primeCompl y
    refine ⟨r, c, r.2, ?_⟩
    have e := congrArg (algebraMap A' F) h
    simp only [map_mul, ← IsScalarTower.algebraMap_apply] at e
    rw [mul_comm, e]
  · rintro ⟨r, c, hr, h⟩
    obtain ⟨v, hv⟩ := (IsLocalization.map_units A' (⟨r, hr⟩ : p.primeCompl)).exists_left_inv
    refine ⟨v * algebraMap A A' c, ?_⟩
    have e := congrArg (algebraMap A' F) hv
    simp only [map_mul, map_one, ← IsScalarTower.algebraMap_apply] at e ⊢
    linear_combination (-algebraMap A' F v) * h + x * e

theorem trace_mem_localization_iff (A F K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Field F] [Field K] [Algebra A F] [IsFractionRing A F] [Algebra F K] [Algebra A K] [IsScalarTower A F K]
    [FiniteDimensional F K] [Algebra.IsSeparable F K] (hchar : ∀ n : ℕ, n ≠ 0 → IsUnit (n : A))
    (p : Ideal A) [hp : p.IsPrime] (hp1 : p.height = 1) (t : A) (hpt : p = Ideal.span {t})
    (hdata : ∀ Q : Ideal (integralClosure A K), Q.IsPrime → Q.under A = p →
      ∃ (s : integralClosure A K) (e : ℕ), 1 ≤ e ∧ s ∈ Q ∧ (∀ y ∈ Q, ∃ c r, r ∉ Q ∧ r * y = c * s) ∧
        (∃ a r : integralClosure A K, a ∉ Q ∧ r ∉ Q ∧ r * algebraMap A _ t = a * s ^ e)) (z : K) :
    (∀ b : integralClosure A K, ∃ r c : A, r ∉ p ∧ algebraMap A F r * Algebra.trace F K (z * b) = algebraMap A F c) ↔
      ∀ Q : Ideal (integralClosure A K), Q.IsPrime → Q.under A = p →
        ∀ (s : integralClosure A K) (e : ℕ), 1 ≤ e → s ∈ Q → (∀ y ∈ Q, ∃ c r, r ∉ Q ∧ r * y = c * s) →
          (∃ a r : integralClosure A K, a ∉ Q ∧ r ∉ Q ∧ r * algebraMap A _ t = a * s ^ e) →
          ∃ c r : integralClosure A K, r ∉ Q ∧ (r : K) * ((s : K) ^ (e - 1) * z) = c := by
  set_option synthInstance.maxHeartbeats 200000 in
  let Ap := Localization.subalgebra.ofField F p.primeCompl p.primeCompl_le_nonZeroDivisors
  haveI : IsLocalization.AtPrime Ap p := inferInstance
  haveI : IsDiscreteValuationRing Ap := GlobalTheory.isDiscreteValuationRing_of_height_eq_one p hp1 Ap
  haveI : CharZero (IsLocalRing.ResidueField Ap) := charZero_of_inj_zero fun n hn => by
    by_contra h
    have := ((hchar n h).map ((IsLocalRing.residue Ap).comp (algebraMap A Ap))).ne_zero
    rw [map_natCast] at this
    exact this hn
  let B := integralClosure A K
  let Bp := integralClosure Ap K
  haveI : IsDedekindDomain Bp := integralClosure.isDedekindDomain Ap F K
  haveI : Module.Finite Ap Bp := IsIntegralClosure.finite Ap F K Bp
  haveI : IsFractionRing Bp K := integralClosure.isFractionRing_of_finite_extension F K
  have hinj : Function.Injective (algebraMap Ap K) := by
    rw [IsScalarTower.algebraMap_eq Ap F K]
    exact (algebraMap F K).injective.comp (IsFractionRing.injective Ap F)
  haveI : FaithfulSMul Ap Bp := (faithfulSMul_iff_algebraMap_injective Ap Bp).2 fun x y h =>
    hinj (congrArg (fun w : Bp => (w : K)) h)
  haveI : Module.IsTorsionFree Ap Bp := inferInstance
  letI : Algebra B Bp := (RingHom.codRestrict B.val.toRingHom Bp fun b => IsIntegral.tower_top (A := Ap) b.2).toAlgebra
  haveI : IsScalarTower B Bp K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A B Bp := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsLocalization (Algebra.algebraMapSubmonoid K p.primeCompl) K := IsLocalization.self (by
    rintro _ ⟨a, ha, rfl⟩
    rw [IsUnit.mem_submonoid_iff, IsScalarTower.algebraMap_apply A Ap K]
    exact (IsLocalization.map_units Ap (⟨a, ha⟩ : p.primeCompl)).map _)
  let M := Algebra.algebraMapSubmonoid B p.primeCompl
  haveI : IsLocalization M Bp := IsLocalization.integralClosure (R := A) (S := K) (Rf := Ap) (Sf := K) p.primeCompl
  have hπ : IsLocalRing.maximalIdeal Ap = Ideal.span {algebraMap A Ap t} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p Ap]
    conv_lhs => rw [hpt]
    rw [Ideal.map_span, Set.image_singleton]
  have hrel : ∀ (s a r : B) (e : ℕ), r * algebraMap A B t = a * s ^ e →
      algebraMap B Bp r * algebraMap Ap Bp (algebraMap A Ap t) = algebraMap B Bp a * algebraMap B Bp s ^ e := by
    intro s a r e h
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B Bp, ← map_mul, h, map_mul, map_pow]
  constructor
  · intro hL Q hQ hQp s e he hsQ hs ⟨a, r, ha, hr, h⟩
    have hz : ∀ b : Bp, Algebra.trace F K (z * algebraMap Bp K b) ∈ (algebraMap Ap F).range := by
      intro b
      obtain ⟨⟨b0, _, m, hm, rfl⟩, hb⟩ := IsLocalization.surj M b
      obtain ⟨r, c, hr, h⟩ := hL b0
      refine (mem_range_iff p _).2 ⟨r * m, c, fun h' => (hp.mem_or_mem h').elim hr hm, ?_⟩
      have e1 : (b0 : K) = (b : K) * algebraMap A K m := (congrArg (fun w : Bp => (w : K)) hb).symm
      have e2 : z * (b0 : K) = algebraMap A F m • (z * algebraMap Bp K b) := by
        rw [e1, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
        change _ = _ * (z * (b : K))
        ring
      rw [← h, e2, map_smul, map_mul, smul_eq_mul, mul_assoc]
    have hdis : Disjoint (M : Set B) (Q : Set B) := by
      rw [Set.disjoint_left]
      rintro _ ⟨m, hm, rfl⟩ hmQ
      exact hm (hQp ▸ hmQ : m ∈ p)
    haveI := IsLocalization.isPrime_of_isPrime_disjoint M Bp Q hQ hdis
    have hu := IsLocalization.under_map_of_isPrime_disjoint M Bp hQ hdis
    generalize Ideal.map (algebraMap B Bp) Q = Q' at *
    subst hu
    obtain ⟨c', r', hr', h'⟩ := core_mp F K _ hπ z hz Q' (algebraMap B Bp s) e he hsQ (gen_up M Q' s hs) _ _ ha hr
      (hrel s a r e h)
    exact loc_down M Q' _ c' r' hr' h'
  · intro hR b
    refine (mem_range_iff (A' := Ap) p _).1 (core_mpr F K _ hπ z (fun Q' hQ' => ?_) (algebraMap B Bp b))
    have hQp : (Q'.under B).under A = p := by
      have h1 : Q'.under Ap = IsLocalRing.maximalIdeal Ap :=
        IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := Ap) Q')
      rw [Ideal.under_under, ← Ideal.under_under (B := Ap), h1]
      ext x
      exact IsLocalization.AtPrime.to_map_mem_maximal_iff Ap p x
    obtain ⟨s, e, he, hsQ, hs, a, r, ha, hr, h⟩ := hdata (Q'.under B) inferInstance hQp
    obtain ⟨c, r', hr', h'⟩ := hR (Q'.under B) inferInstance hQp s e he hsQ hs ⟨a, r, ha, hr, h⟩
    exact ⟨algebraMap B Bp s, e, he, hsQ, gen_up M Q' s hs, ⟨_, _, ha, hr, hrel s a r e h⟩,
      algebraMap B Bp c, algebraMap B Bp r', hr', h'⟩

theorem trace_mem_localization_iff_forall_prime :
    ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∀ t : A, Irreducible t → p = Ideal.span {t} → (∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → Q.height = 1) → (∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → ∃ (s : B) (e : ℕ), 1 ≤ e ∧ s ∈ Q ∧ (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) ∧ (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * algebraMap F K t = a * s ^ e)) → ∀ z : K, (∀ b : B, ∃ r c : A, r ∉ p ∧ (r : F) * Algebra.trace F K (z * b) = c) ↔ ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → ∀ (s : B) (e : ℕ), 1 ≤ e → s ∈ Q → (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) → (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * algebraMap F K t = a * s ^ e) → ∃ c r : B, r ∉ Q ∧ (r : K) * s ^ (e - 1) * z = c := by
  intro k F K _ _ _ _ _ _ _ _ _ d u hu A _ hA B hB p hp hp1 t _ hpt _ hdata z
  haveI : IsNoetherianRing A := by
    subst hA
    exact isNoetherianRing_of_ringEquiv _ hu.aevalEquiv.toRingEquiv
  haveI : IsIntegrallyClosed A := by
    subst hA
    exact IsIntegrallyClosed.of_equiv hu.aevalEquiv.toRingEquiv
  haveI : CharZero F := charZero_of_injective_ringHom (algebraMap k F).injective
  have hchar : ∀ n : ℕ, n ≠ 0 → IsUnit (n : A) := fun n hn => by
    simpa using (IsUnit.mk0 (n : k) (Nat.cast_ne_zero.2 hn)).map (algebraMap k A)
  subst hB
  have hover : ∀ Q : Ideal (integralClosure A K), Q.under A = p ↔
      ∀ a : A, ∀ b : integralClosure A K, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p) := by
    intro Q
    constructor
    · rintro rfl a b hb
      have : b = algebraMap A _ a := Subtype.ext hb
      rw [this]; rfl
    · intro h
      ext a
      exact h a (algebraMap A _ a) rfl
  have hrel : ∀ (s a r : integralClosure A K) (e : ℕ), r * algebraMap A _ t = a * s ^ e ↔
      (r : K) * algebraMap F K t = a * s ^ e := fun s a r e => Subtype.ext_iff
  have key := trace_mem_localization_iff A F K hchar p hp1 t hpt (by
    simp only [hover, hrel]; exact hdata) z
  simp only [hover, hrel, ← mul_assoc] at key
  exact key

end GlobalTheory.CodimDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMemLocalizationIffForallPrimeStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_mem_localization_iff_forall_prime_alt : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∀ t : A, Irreducible t → p = Ideal.span {t} → (∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → Q.height = 1) → (∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → ∃ (s : B) (e : ℕ), 1 ≤ e ∧ s ∈ Q ∧ (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) ∧ (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * algebraMap F K t = a * s ^ e)) → ∀ z : K, (∀ b : B, ∃ r c : A, r ∉ p ∧ (r : F) * Algebra.trace F K (z * b) = c) ↔ ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → ∀ (s : B) (e : ℕ), 1 ≤ e → s ∈ Q → (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) → (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * algebraMap F K t = a * s ^ e) → ∃ c r : B, r ∉ Q ∧ (r : K) * s ^ (e - 1) * z = c := by
  first | (exact @GlobalTheory.CodimDual.trace_mem_localization_iff_forall_prime) | (exact GlobalTheory.CodimDual.trace_mem_localization_iff_forall_prime) | (intros; apply GlobalTheory.CodimDual.trace_mem_localization_iff_forall_prime  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureHeightEqOneOfLiesOver
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureHeightEqOneOfLiesOver
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

theorem integralClosure_height_eq_one_of_liesOver : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (A : Subalgebra k F) [IsFractionRing A F] (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → Q.height = 1 := by
  intro k F K _ _ _ _ _ _ _ _ A _ B hB p hp hp1 Q hQ hlo

  have hmem : ∀ a : A, algebraMap F K (a : F) ∈ B := by
    intro a
    rw [hB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
    exact isIntegral_algebraMap (R := A) (A := K) (x := a)
  let f : A →+* B := ((algebraMap F K).comp A.val.toRingHom).codRestrict B hmem
  letI : Algebra A B := f.toAlgebra
  have hf : ∀ a : A, ((algebraMap A B a : B) : K) = algebraMap F K (a : F) := fun _ => rfl

  let φ : B →ₐ[A] K :=
    { toRingHom := B.val.toRingHom
      commutes' := fun a => rfl }
  have hint : Algebra.IsIntegral A B := by
    refine ⟨fun b => ?_⟩
    have key : ∀ x : K, x ∈ B → x ∈ integralClosure A K := by
      intro x hx
      rw [hB, Subalgebra.mem_restrictScalars] at hx
      exact hx
    have hb : (b : K) ∈ integralClosure A K := key b b.2
    rw [← isIntegral_algHom_iff φ Subtype.val_injective]
    exact hb

  have hcomap : Q.comap (algebraMap A B) = p := by
    ext a
    exact hlo a (algebraMap A B a) (hf a)
  haveI := hp
  haveI := hQ
  have hpne : p ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hp1
  apply le_antisymm
  · rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) by rfl, Ideal.height_le_iff]
    intro Q' hQ' hlt
    haveI := hQ'
    by_contra hge
    have hQ'ne : Q' ≠ ⊥ := by
      intro h
      apply hge
      rw [h, Ideal.height_bot]
      norm_num
    have h1 : Q'.comap (algebraMap A B) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot A hQ'ne
    have h2 : Q'.comap (algebraMap A B) < p := hcomap ▸ Ideal.IsIntegral.comap_lt_comap hlt
    haveI : (Q'.comap (algebraMap A B)).IsPrime := Ideal.comap_isPrime _ _
    have h3 := Ideal.height_add_one_le_of_lt_of_isPrime h2
    have h4 : 1 ≤ (Q'.comap (algebraMap A B)).height := by
      rw [Order.one_le_iff_pos, pos_iff_ne_zero]
      exact fun h => h1 (Ideal.height_eq_zero_iff_eq_bot.mp h)
    rw [hp1] at h3
    have : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add h4 le_rfl).trans h3
    norm_num at this
  · rw [Order.one_le_iff_pos, pos_iff_ne_zero]
    intro h
    rw [Ideal.height_eq_zero_iff_eq_bot] at h
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpne
    have : algebraMap A B a ∈ Q := by rw [← Ideal.mem_comap, hcomap]; exact ha
    rw [h, Ideal.mem_bot] at this
    apply ha0
    have := congrArg (fun x : B => (x : K)) this
    simp only [hf, ZeroMemClass.coe_zero] at this
    exact Subtype.ext ((algebraMap F K).injective (this.trans (map_zero _).symm))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureHeightEqOneOfLiesOverStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_eq_one_of_liesOver_height_one : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (A : Subalgebra k F) [IsFractionRing A F] (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → Q.height = 1 := by
  first | (exact @GlobalTheory.integralClosure_height_eq_one_of_liesOver) | (exact GlobalTheory.integralClosure_height_eq_one_of_liesOver) | (intros; apply GlobalTheory.integralClosure_height_eq_one_of_liesOver  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureHeightOneUniformizerRamificationA
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureHeightOneUniformizerRamificationA
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

theorem exists_localUniformizer_and_order {B : Type} [CommRing B] [IsDomain B]
    [IsNoetherianRing B] [IsIntegrallyClosed B] (Q : Ideal B) [Q.IsPrime] (hQ : Q.height = 1)
    (x : B) (hx0 : x ≠ 0) (hxQ : x ∈ Q) :
    ∃ (s : B) (e : ℕ), 1 ≤ e ∧ s ∈ Q ∧ (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) ∧
      (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ r * x = a * s ^ e) := by
  let L := Localization.AtPrime Q
  haveI : IsDiscreteValuationRing L := isDiscreteValuationRing_of_height_eq_one Q hQ L
  have hle : Q.primeCompl ≤ nonZeroDivisors B := Q.primeCompl_le_nonZeroDivisors
  have hinj : Function.Injective (algebraMap B L) := IsLocalization.injective L hle
  have hcomap : (IsLocalRing.maximalIdeal L).comap (algebraMap B L) = Q :=
    IsLocalization.AtPrime.under_maximalIdeal L Q
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible L
  obtain ⟨⟨s, r0⟩, hs⟩ := IsLocalization.surj Q.primeCompl ϖ
  simp only at hs
  have hu0 : IsUnit (algebraMap B L r0) := IsLocalization.map_units L r0
  have hsirr : Irreducible (algebraMap B L s) := by
    rw [← hs]; exact (irreducible_mul_isUnit hu0).mpr hϖ
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hsirr
  have hsQ : s ∈ Q := by
    rw [← hcomap, Ideal.mem_comap, hmax]; exact Ideal.subset_span rfl
  refine ⟨s, ?_⟩
  have hxL : algebraMap B L x ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap B L)]; exact fun h => hx0 (hinj h)
  obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hxL hsirr
  have hxm : algebraMap B L x ∈ IsLocalRing.maximalIdeal L := by
    rw [← Ideal.mem_comap, hcomap]; exact hxQ
  refine ⟨n, ?_, hsQ, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      rw [h, pow_zero, mul_one] at hw
      exact (IsLocalRing.mem_maximalIdeal _).mp hxm (hw ▸ w.isUnit)
    · exact h
  · intro y hy
    have hym : algebraMap B L y ∈ Ideal.span {algebraMap B L s} := by
      rw [← hmax, ← Ideal.mem_comap, hcomap]; exact hy
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hym
    obtain ⟨⟨c, r⟩, hcr⟩ := IsLocalization.surj Q.primeCompl z
    simp only at hcr
    refine ⟨c, r, r.2, hinj ?_⟩
    rw [map_mul, map_mul, ← hz, ← hcr]; ring
  · obtain ⟨⟨a, r⟩, har⟩ := IsLocalization.surj Q.primeCompl (w : L)
    simp only at har
    have hau : IsUnit (algebraMap B L a) := by
      rw [← har]; exact w.isUnit.mul (IsLocalization.map_units L r)
    refine ⟨a, r, ?_, r.2, hinj ?_⟩
    · intro haQ
      have : algebraMap B L a ∈ IsLocalRing.maximalIdeal L := by
        rw [← Ideal.mem_comap, hcomap]; exact haQ
      exact (IsLocalRing.mem_maximalIdeal _).mp this hau
    · rw [map_mul, map_mul, map_pow, ← har, hw]; ring

theorem integralClosure_height_one_uniformizer_ramification :
    ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (p : Ideal A), p.IsPrime → ∀ t : A, Irreducible t → p = Ideal.span {t} → ∀ Q : Ideal B, Q.IsPrime → Q.height = 1 → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → ∃ (s : B) (e : ℕ), 1 ≤ e ∧ s ∈ Q ∧ (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) ∧ (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * algebraMap F K t = a * s ^ e) := by
  intro k F K _ _ _ _ _ _ _ _ _ d u hu A _ hA B hB p _ t ht hpt Q _ hQ hlie
  have hN : IsNoetherianRing A := by
    subst hA
    exact isNoetherianRing_of_ringEquiv _ hu.aevalEquiv.toRingEquiv
  have hI : IsIntegrallyClosed A := by
    subst hA
    have : IsIntegrallyClosed (MvPolynomial (Fin d) k) :=
      UniqueFactorizationMonoid.instIsIntegrallyClosed
    exact IsIntegrallyClosed.of_equiv hu.aevalEquiv.toRingEquiv
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  subst hB
  have hNB : IsNoetherianRing (integralClosure A K) := by
    letI : IsNoetherianRing A := hN
    letI : IsIntegrallyClosed A := hI
    exact integralClosure.isNoetherianRing (A := A) (K := F) (L := K)
  have hIB : IsIntegrallyClosed (integralClosure A K) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension F
  haveI : IsNoetherianRing ((integralClosure A K).restrictScalars k) := hNB
  haveI : IsIntegrallyClosed ((integralClosure A K).restrictScalars k) := hIB
  have hmem : algebraMap F K (t : F) ∈ (integralClosure A K).restrictScalars k := by
    rw [Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
    exact isIntegral_algebraMap (x := t)
  let x : (integralClosure A K).restrictScalars k := ⟨_, hmem⟩
  have hxQ : x ∈ Q := (hlie t x rfl).mpr (hpt ▸ Ideal.subset_span rfl)
  have hx0 : x ≠ 0 := by
    intro h
    have h' : algebraMap F K (t : F) = 0 := congrArg Subtype.val h
    rw [map_eq_zero_iff _ (algebraMap F K).injective, ZeroMemClass.coe_eq_zero] at h'
    exact ht.ne_zero h'
  obtain ⟨s, e, he, hs, hgen, a, r, ha, hr, hrx⟩ := exists_localUniformizer_and_order Q hQ x hx0 hxQ
  refine ⟨s, e, he, hs, hgen, a, r, ha, hr, ?_⟩
  have := congrArg Subtype.val hrx
  simpa using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureHeightOneUniformizerRamificationAStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformizer_ramification_of_height_one : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (p : Ideal A), p.IsPrime → ∀ t : A, Irreducible t → p = Ideal.span {t} → ∀ Q : Ideal B, Q.IsPrime → Q.height = 1 → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → ∃ (s : B) (e : ℕ), 1 ≤ e ∧ s ∈ Q ∧ (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) ∧ (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * algebraMap F K t = a * s ^ e) := by
  first | (exact @GlobalTheory.integralClosure_height_one_uniformizer_ramification) | (exact GlobalTheory.integralClosure_height_one_uniformizer_ramification) | (intros; apply GlobalTheory.integralClosure_height_one_uniformizer_ramification  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTraceDualLocalizationIffForallRegularForm
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

theorem heightOne_eq_span_irreducible : ∀ (k F : Type) [Field k] [Field F] [Algebra k F] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F), A = Algebra.adjoin k (Set.range u) → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∃ t : A, Irreducible t ∧ p = Ideal.span {t} := by
  intro k F _ _ _ d u hu A hA p hp hh
  subst hA
  haveI := hp
  haveI : UniqueFactorizationMonoid (Algebra.adjoin k (Set.range u)) :=
    hu.aevalEquiv.toMulEquiv.uniqueFactorizationMonoid inferInstance
  obtain ⟨g, hg⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hh).principal
  refine ⟨g, ?_, hg⟩
  have hne : g ≠ 0 := by
    rintro rfl
    exact p.ne_bot_of_height_eq_one hh (by rw [hg]; simp)
  rw [hg] at hp
  exact ((Ideal.span_singleton_prime hne).mp hp).irreducible

theorem mem_traceDual_localization_iff_forall_regularForm : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → Algebra.Smooth k B → ∀ τ : DR k K →ₗ[K] K, τ (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (u j))) = 1 → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∀ z : K, (∀ b : B, ∃ r c : A, r ∉ p ∧ (r : F) * Algebra.trace F K (z * b) = c) ↔ ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → (∃ r : B, r ∉ Q ∧ ∃ y ∈ omB k K B d, τ y = r * z) := by
  intro k F K _ _ _ _ _ _ _ _ _ d u hu A _ hA B hB hsm τ hτ p hp hh z
  obtain ⟨t, ht, hpt⟩ := heightOne_eq_span_irreducible k F d u hu A hA p hp hh
  have h2 : ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → Q.height = 1 :=
    fun Q hQ hov => GlobalTheory.T.height_eq_one_of_liesOver_height_one k F K A B hB p hp hh Q hQ hov
  have h3 := fun Q hQ hov => GlobalTheory.T.exists_uniformizer_ramification_of_height_one k F K d u hu A hA B hB p hp t ht hpt Q hQ (h2 Q hQ hov) hov
  rw [GlobalTheory.T.trace_mem_localization_iff_forall_prime_alt k F K d u hu A hA B hB p hp hh t ht hpt h2 h3 z]
  constructor
  · intro hl Q hQ hov
    obtain ⟨s, e, he, hs, hun, htd⟩ := h3 Q hQ hov
    exact (GlobalTheory.T.regular_topForm_pole_order_height_one_prime k F K d u hu A hA B hB hsm τ hτ Q hQ (h2 Q hQ hov) t s e ht he hs hun htd z).mpr
      (hl Q hQ hov s e he hs hun htd)
  · intro hr Q hQ hov s e he hs hun htd
    exact (GlobalTheory.T.regular_topForm_pole_order_height_one_prime k F K d u hu A hA B hB hsm τ hτ Q hQ (h2 Q hQ hov) t s e ht he hs hun htd z).mp (hr Q hQ hov)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTraceDualLocalizationIffForallRegularFormStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_traceDual_localization_iff_forall_regularForm_alt : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → Algebra.Smooth k B → ∀ τ : DR k K →ₗ[K] K, τ (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (u j))) = 1 → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∀ z : K, (∀ b : B, ∃ r c : A, r ∉ p ∧ (r : F) * Algebra.trace F K (z * b) = c) ↔ ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → (∃ r : B, r ∉ Q ∧ ∃ y ∈ omB k K B d, τ y = r * z) := by
  first | (exact @GlobalTheory.mem_traceDual_localization_iff_forall_regularForm) | (exact GlobalTheory.mem_traceDual_localization_iff_forall_regularForm) | (intros; apply GlobalTheory.mem_traceDual_localization_iff_forall_regularForm  <;> assumption)
end
