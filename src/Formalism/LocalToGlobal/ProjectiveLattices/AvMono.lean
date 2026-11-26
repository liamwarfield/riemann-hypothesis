module

public import Mathlib

@[expose] public section

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.AvMono
set_option autoImplicit false

noncomputable section

open Polynomial IsLocalRing

namespace Formalism.L2.Pj.AvAlg

variable {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]

theorem mem_adjoin_mod (α : B) (hres : Algebra.adjoin (ResidueField A) {residue B α} = ⊤) (f : A[X])
    (hβ : Irreducible (aeval α f)) :
    ∀ (n : ℕ) (b : B), ∃ s ∈ Algebra.adjoin A {α}, ∃ c : B, b = s + aeval α f ^ n * c := by
  have hra : ∀ G : A[X], residue B (aeval α G) = aeval (residue B α) (G.map (residue A)) := by
    intro G
    rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂]
    congr 1
    all_goals (ext x; simp only [RingHom.comp_apply]; exact (IsLocalRing.ResidueField.algebraMap_residue x).symm)
  intro n
  induction n with
  | zero => intro b; exact ⟨0, Subalgebra.zero_mem _, b, by simp⟩
  | succ n ih =>
    intro b
    obtain ⟨s, hs, c, rfl⟩ := ih b
    have hc : residue B c ∈ Algebra.adjoin (ResidueField A) {residue B α} := by
      rw [hres]; exact Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hc
    obtain ⟨p, hp⟩ := hc
    obtain ⟨P, rfl⟩ := Polynomial.map_surjective (residue A) IsLocalRing.residue_surjective p
    have hm : c - aeval α P ∈ maximalIdeal B := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hra]
      rw [← hp]
      exact sub_self _
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hβ, Ideal.mem_span_singleton'] at hm
    obtain ⟨c', hc'⟩ := hm
    have hα : aeval α f ∈ Algebra.adjoin A {α} := by
      rw [Algebra.adjoin_singleton_eq_range_aeval]; exact AlgHom.mem_range_self _ f
    have hP : aeval α P ∈ Algebra.adjoin A {α} := by
      rw [Algebra.adjoin_singleton_eq_range_aeval]; exact AlgHom.mem_range_self _ P
    refine ⟨s + aeval α f ^ n * aeval α P, ?_, c', ?_⟩
    · exact Subalgebra.add_mem _ hs (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hα n) hP)
    · have e : c = aeval α P + c' * aeval α f := by rw [hc']; ring
      rw [e]
      ring

end Formalism.L2.Pj.AvAlg

namespace Formalism.L2.Pj.AvAlg

variable {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]

theorem adjoin_eq_top_of_gen [Module.Finite A B] (hinj : Function.Injective (algebraMap A B)) (α : B)
    (hres : Algebra.adjoin (ResidueField A) {residue B α} = ⊤) (f : A[X]) (hβ : Irreducible (aeval α f)) :
    Algebra.adjoin A {α} = ⊤ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hϖ0 : algebraMap A B ϖ ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]; exact hϖ.ne_zero
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hϖ0 hβ
  have hϖm : ϖ ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
  have key : (⊤ : Submodule A B) ≤ Subalgebra.toSubmodule (Algebra.adjoin A {α}) ⊔ (maximalIdeal A) • ⊤ := by
    intro b _
    obtain ⟨s, hs, c, hc⟩ := mem_adjoin_mod α hres f hβ e b
    have e1 : b = s + ϖ • ((↑u⁻¹ : B) * c) := by
      rw [hc, Algebra.smul_def, hu]
      congr 1
      rw [mul_comm (↑u : B), mul_assoc, ← mul_assoc (↑u : B), Units.mul_inv, one_mul]
    rw [e1]
    exact Submodule.add_mem_sup ((Subalgebra.mem_toSubmodule _).mpr hs)
      (Submodule.smul_mem_smul hϖm Submodule.mem_top)
  have hfg : (⊤ : Submodule A B).FG := Module.Finite.fg_top
  have hle := Submodule.le_of_le_smul_of_le_jacobson_bot hfg
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge key
  rw [eq_top_iff]
  intro x _
  exact (Subalgebra.mem_toSubmodule _).mp (hle Submodule.mem_top)

end Formalism.L2.Pj.AvAlg

namespace Formalism.L2.Pj.AvAlg

variable {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]

theorem residue_aeval (α : B) (G : A[X]) :
    residue B (aeval α G) = aeval (residue B α) (G.map (residue A)) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂]
  congr 1
  all_goals (ext x; simp only [RingHom.comp_apply]; exact (IsLocalRing.ResidueField.algebraMap_residue x).symm)

theorem adjoin_residue_gen [Finite (ResidueField B)] :
    ∃ γ : ResidueField B, Algebra.adjoin (ResidueField A) {γ} = ⊤ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ResidueField B)ˣ)
  refine ⟨(g : ResidueField B), ?_⟩
  rw [eq_top_iff]
  intro x _
  by_cases hx : x = 0
  · rw [hx]; exact Subalgebra.zero_mem _
  · obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.mpr (hg (Units.mk0 x hx)))
    have e : x = (g : ResidueField B) ^ n := by
      rw [← Units.val_pow_eq_pow_val, show g ^ n = Units.mk0 x hx from hn, Units.val_mk0]
    rw [e]
    exact Subalgebra.pow_mem (Algebra.adjoin (ResidueField A) {(g : ResidueField B)})
      (Algebra.subset_adjoin (Set.mem_singleton _)) n

theorem exists_adjoin_eq_top [Module.Finite A B] [Finite (ResidueField A)]
    (hinj : Function.Injective (algebraMap A B)) : ∃ α : B, Algebra.adjoin A {α} = ⊤ := by
  haveI : Finite (ResidueField B) := IsLocalRing.ResidueField.finite_of_finite (R := A) ‹_›
  obtain ⟨γ, hγ⟩ := adjoin_residue_gen (A := A) (B := B)
  obtain ⟨α0, rfl⟩ := IsLocalRing.residue_surjective γ
  have hint : IsIntegral (ResidueField A) (residue B α0) := IsIntegral.of_finite _ _
  have hsep : (minpoly (ResidueField A) (residue B α0)).Separable :=
    PerfectField.separable_of_irreducible (minpoly.irreducible hint)
  have hq0 : aeval (residue B α0) (minpoly (ResidueField A) (residue B α0)) = 0 := minpoly.aeval _ _
  have hq' : aeval (residue B α0) (derivative (minpoly (ResidueField A) (residue B α0))) ≠ 0 :=
    hsep.aeval_derivative_ne_zero hq0
  obtain ⟨P, hP⟩ := Polynomial.map_surjective (residue A) IsLocalRing.residue_surjective
    (minpoly (ResidueField A) (residue B α0))
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hm : aeval α0 P ∈ maximalIdeal B := by
    rw [← IsLocalRing.residue_eq_zero_iff, residue_aeval, hP, hq0]
  have hd : IsUnit (aeval α0 (derivative P)) := by
    by_contra hnu
    have h3 : aeval α0 (derivative P) ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    rw [← IsLocalRing.residue_eq_zero_iff, residue_aeval, ← Polynomial.derivative_map, hP] at h3
    exact hq' h3
  by_cases h2 : aeval α0 P ∈ Ideal.span {π ^ 2}
  · refine ⟨α0 + π, adjoin_eq_top_of_gen hinj (α0 + π) ?_ P ?_⟩
    · have hr : residue B π = 0 :=
        (IsLocalRing.residue_eq_zero_iff _).mpr (hmax ▸ Ideal.mem_span_singleton_self π)
      rw [map_add (f := _), hr, add_zero]; exact hγ
    · obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp h2
      obtain ⟨k, hk⟩ := Polynomial.binomExpansion (P.map (algebraMap A B)) α0 π
      have e : aeval (α0 + π) P = π * (aeval α0 (derivative P) + π * (t + k)) := by
        simp only [Polynomial.aeval_def, ← Polynomial.eval_map] at ht ⊢
        rw [← Polynomial.derivative_map, hk, ← ht]
        ring
      have hv : IsUnit (aeval α0 (derivative P) + π * (t + k)) := by
        by_contra hnu
        have h1 : aeval α0 (derivative P) + π * (t + k) ∈ maximalIdeal B :=
          (IsLocalRing.mem_maximalIdeal _).mpr hnu
        have h3 : π * (t + k) ∈ maximalIdeal B := by
          rw [hmax]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self π)
        have h4 : aeval α0 (derivative P) ∈ maximalIdeal B := by
          simpa using Ideal.sub_mem _ h1 h3
        exact (IsLocalRing.mem_maximalIdeal _).mp h4 hd
      rw [e]
      exact (irreducible_mul_isUnit hv).mpr hπ
  · refine ⟨α0, adjoin_eq_top_of_gen hinj α0 hγ P ?_⟩
    rw [hmax] at hm
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hm
    have hwu : IsUnit w := by
      by_contra hnu
      apply h2
      have h5 : w ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      rw [hmax, Ideal.mem_span_singleton'] at h5
      obtain ⟨v, hv⟩ := h5
      rw [Ideal.mem_span_singleton']
      exact ⟨v, by rw [← hw, ← hv]; ring⟩
    rw [← hw, mul_comm]
    exact (irreducible_mul_isUnit hwu).mpr hπ

end Formalism.L2.Pj.AvAlg
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.PowMapMemOfPowMulMem
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.GenericSectionMinimum

structure IsDer {A : Type*} [CommRing A] (δ : A → A) : Prop where
  add : ∀ x y, δ (x + y) = δ x + δ y
  mul : ∀ x y, δ (x * y) = x * δ y + y * δ x

namespace IsDer

variable {A : Type*} [CommRing A] {δ : A → A}

theorem der_zero (h : IsDer δ) : δ 0 = 0 := by
  have e := h.add 0 0
  rw [add_zero] at e
  linear_combination -e

theorem der_one (h : IsDer δ) : δ 1 = 0 := by
  have e := h.mul 1 1
  simp only [one_mul] at e
  linear_combination -e

theorem der_neg (h : IsDer δ) (x : A) : δ (-x) = -δ x := by
  have e := h.add x (-x)
  rw [add_neg_cancel, h.der_zero] at e
  linear_combination -e

theorem der_sub (h : IsDer δ) (x y : A) : δ (x - y) = δ x - δ y := by
  rw [sub_eq_add_neg, h.add, h.der_neg, sub_eq_add_neg]

theorem der_pow_succ (h : IsDer δ) (x : A) (n : ℕ) : δ (x ^ (n + 1)) = (n + 1 : A) * x ^ n * δ x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ x (n + 1), h.mul, ih]
    push_cast
    ring

theorem mul_map_pow (h : IsDer δ) (z : A) (r : ℕ) : z * δ (z ^ r) = (r : A) * z ^ r * δ z := by
  cases r with
  | zero => simp [h.der_one]
  | succ n =>
    rw [h.der_pow_succ]
    push_cast
    ring

theorem der_sum (h : IsDer δ) {ι : Type*} (s : Finset ι) (f : ι → A) : δ (∑ i ∈ s, f i) = ∑ i ∈ s, δ (f i) := by
  exact map_sum (AddMonoidHom.mk' δ h.add) f s

theorem pow_map_mem_of_pow_mul_mem (h : IsDer δ) (I : Ideal A) (hI : ∀ x ∈ I, δ x ∈ I) (hu : ∀ n : ℕ, 0 < n → IsUnit (n : A))
    (y : A) : ∀ m r : ℕ, y ^ m * δ y ^ r ∈ I → δ y ^ (r + 2 * m) ∈ I := by
  intro m
  induction m with
  | zero => intro r hr; simpa using hr
  | succ m ih =>
    intro r hr
    have hwJ : δ y * δ (y ^ (m + 1) * δ y ^ r) ∈ I := I.mul_mem_left _ (hI _ hr)
    have e := h.mul_map_pow (δ y) r
    have key : δ y * δ (y ^ (m + 1) * δ y ^ r) =
        (r : A) * δ (δ y) * (y ^ (m + 1) * δ y ^ r) + ((m : A) + 1) * (y ^ m * δ y ^ (r + 2)) := by
      rw [h.mul, h.der_pow_succ]
      linear_combination y ^ (m + 1) * e
    have h2 : ((m : A) + 1) * (y ^ m * δ y ^ (r + 2)) ∈ I := by
      have h3 : (r : A) * δ (δ y) * (y ^ (m + 1) * δ y ^ r) ∈ I := I.mul_mem_left _ hr
      have h5 := I.sub_mem hwJ h3
      rwa [key, add_sub_cancel_left] at h5
    have hu1 := hu (m + 1) (Nat.succ_pos m)
    push_cast at hu1
    have h4 : y ^ m * δ y ^ (r + 2) ∈ I := (Ideal.unit_mul_mem_iff_mem I hu1).mp h2
    have h6 := ih (r + 2) h4
    rwa [show r + 2 + 2 * m = r + 2 * (m + 1) by ring] at h6

theorem pow_mem (h : IsDer δ) (I : Ideal A) (hI : ∀ x ∈ I, δ x ∈ I) (hu : ∀ n : ℕ, 0 < n → IsUnit (n : A))
    {y : A} {n : ℕ} (hy : y ^ n ∈ I) : δ y ^ (2 * n) ∈ I := by
  have e := h.pow_map_mem_of_pow_mul_mem I hI hu y n 0 (by simpa using hy)
  simpa using e

theorem mem_max [IsArtinianRing A] (h : IsDer δ) (hu : ∀ n : ℕ, 0 < n → IsUnit (n : A)) (m : Ideal A)
    [hm : m.IsMaximal] {x : A} (hx : x ∈ m) : δ x ∈ m := by

  have hx' : algebraMap A (Localization.AtPrime m) x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime m) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m x).mpr hx
  have hnil : IsNilpotent (algebraMap A (Localization.AtPrime m) x) := by
    obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := Localization.AtPrime m)
    refine ⟨k, ?_⟩
    have hj : algebraMap A (Localization.AtPrime m) x ∈ Ideal.jacobson (⊥ : Ideal (Localization.AtPrime m)) := by
      rwa [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
    have := Ideal.pow_mem_pow hj k
    rwa [hk, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  obtain ⟨n, hn⟩ := hnil
  rw [← map_pow] at hn
  obtain ⟨⟨s, hs⟩, hsx⟩ := (IsLocalization.map_eq_zero_iff m.primeCompl (Localization.AtPrime m) _).mp hn
  have hs' : s ∉ m := hs

  have hsx0 : (s * x) ^ (n + 1) ∈ (⊥ : Ideal A) := by
    rw [Ideal.mem_bot]
    calc (s * x) ^ (n + 1) = s ^ n * x * (s * x ^ n) := by ring
      _ = 0 := by simp only at hsx; rw [hsx, mul_zero]
  have hb : ∀ z ∈ (⊥ : Ideal A), δ z ∈ (⊥ : Ideal A) := by
    intro z hz
    rw [Ideal.mem_bot] at hz ⊢
    rw [hz, h.der_zero]
  have hd := h.pow_mem ⊥ hb hu hsx0
  rw [Ideal.mem_bot] at hd
  have hdm : δ (s * x) ∈ m := hm.isPrime.mem_of_pow_mem _ (by rw [hd]; exact m.zero_mem)
  rw [h.mul] at hdm
  have hxs : x * δ s ∈ m := m.mul_mem_right _ hx
  have hsd : s * δ x ∈ m := by
    have := m.sub_mem hdm hxs
    rwa [add_sub_cancel_right] at this
  exact (hm.isPrime.mem_or_mem hsd).resolve_left hs'

theorem quot (h : IsDer δ) (I : Ideal A) (hI : ∀ x ∈ I, δ x ∈ I) :
    ∃ δ' : A ⧸ I → A ⧸ I, IsDer δ' ∧ ∀ x, δ' (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (δ x) := by
  classical
  let s := Function.surjInv (Ideal.Quotient.mk_surjective (I := I))
  have hs : ∀ q, Ideal.Quotient.mk I (s q) = q := Function.surjInv_eq _
  have key : ∀ x, Ideal.Quotient.mk I (δ (s (Ideal.Quotient.mk I x))) = Ideal.Quotient.mk I (δ x) := by
    intro x
    rw [Ideal.Quotient.eq, ← h.der_sub]
    exact hI _ (Ideal.Quotient.eq.mp (hs _))
  refine ⟨fun q => Ideal.Quotient.mk I (δ (s q)), ⟨fun a b => ?_, fun a b => ?_⟩, key⟩
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_add (f := _), key, key, key, h.add, map_add (f := _)]
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul, key, key, key, h.mul, map_add (f := _), map_mul, map_mul]

theorem ofLoc {B : Type*} [CommRing B] [Algebra A B] (S : Submonoid A) [IsLocalization S B] (d : A → B)
    (hadd : ∀ x y, d (x + y) = d x + d y)
    (hmul : ∀ x y, d (x * y) = algebraMap A B x * d y + algebraMap A B y * d x) :
    ∃ δ' : B → B, IsDer δ' ∧ ∀ a, δ' (algebraMap A B a) = d a := by
  have d1 : d 1 = 0 := by
    have e := hmul 1 1
    simp only [mul_one, map_one, one_mul] at e
    linear_combination -e
  have d0 : d 0 = 0 := by
    have e := hadd 0 0
    simp only [add_zero] at e
    linear_combination -e

  let ψ : A →+* TrivSqZeroExt B B :=
    { toFun := fun a => TrivSqZeroExt.inl (algebraMap A B a) + TrivSqZeroExt.inr (d a)
      map_one' := by ext <;> simp [d1]
      map_mul' := fun x y => by
        ext
        · simp
        · simp [hmul, TrivSqZeroExt.snd_mul]; ring
      map_zero' := by ext <;> simp [d0]
      map_add' := fun x y => by
        ext
        · simp
        · simp [hadd] }
  have hψ : ∀ s : S, IsUnit (ψ s) := by
    intro s
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa [ψ] using IsLocalization.map_units B s
  let φ : B →+* TrivSqZeroExt B B := IsLocalization.lift hψ
  have hφ : ∀ a, φ (algebraMap A B a) = ψ a := IsLocalization.lift_eq hψ
  let fst : TrivSqZeroExt B B →+* B :=
    { toFun := TrivSqZeroExt.fst
      map_one' := rfl
      map_mul' := fun x y => TrivSqZeroExt.fst_mul x y
      map_zero' := rfl
      map_add' := fun x y => rfl }
  have hfst : ∀ x, (φ x).fst = x := by
    have e : fst.comp φ = RingHom.id B := by
      apply IsLocalization.ringHom_ext S
      ext a
      simp only [RingHom.comp_apply, RingHom.id_apply, hφ]
      show TrivSqZeroExt.fst (ψ a) = _
      simp [ψ]
    intro x
    exact congrArg (fun f : B →+* B => f x) e
  refine ⟨fun x => (φ x).snd, ⟨fun x y => by simp, fun x y => ?_⟩, fun a => by simp [hφ, ψ]⟩
  simp only [map_mul, TrivSqZeroExt.snd_mul, hfst, smul_eq_mul, op_smul_eq_mul]
  ring

end IsDer

end Formalism.L2.Pj.GenericSectionMinimum
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
noncomputable section

namespace Formalism.L2.Pj

section Graded

variable {K R M W : Type} [Field K] [CommRing R] [Algebra K R] [AddCommMonoid M] (key : W → M)
  (C : W → Submodule K R)

def incG (w : W) : C w →ₗ[K] AddMonoidAlgebra R M where
  toFun F := AddMonoidAlgebra.single (key w) (F : R)
  map_add' F F' := by simp [AddMonoidAlgebra.single_add]
  map_smul' a F := by simp [AddMonoidAlgebra.smul_single]

theorem incG_apply (w : W) (F : C w) : incG key C w F = AddMonoidAlgebra.single (key w) (F : R) := rfl

def cfG (K : Type) [Field K] [Algebra K R] (m : M) : AddMonoidAlgebra R M →ₗ[K] R where
  toFun x := x.coeff m
  map_add' x y := by simp
  map_smul' a x := by simp

open Classical in
theorem coeff_incG (m : M) (w : W) (F : C w) :
    (incG key C w F).coeff m = if key w = m then (F : R) else 0 := by
  rw [incG_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem incG_inj (w : W) : Function.Injective (incG key C w) := fun F F' h => by
  have h1 := congrArg (fun x : AddMonoidAlgebra R M => x.coeff (key w)) h
  simp only [coeff_incG, if_true] at h1
  exact Subtype.ext h1

theorem incG_indep (hkey : Function.Injective key) :
    iSupIndep fun w : W => LinearMap.range (incG key C w) := by
  intro w
  rw [Submodule.disjoint_def]
  intro x hx hx'
  obtain ⟨F, rfl⟩ := LinearMap.mem_range.mp hx
  have hle : (⨆ (u) (_ : u ≠ w), LinearMap.range (incG key C u)) ≤ LinearMap.ker (cfG K (key w)) := by
    refine iSup₂_le fun u hu => ?_
    rintro _ ⟨G', rfl⟩
    rw [LinearMap.mem_ker]
    change (incG key C u G').coeff (key w) = 0
    rw [coeff_incG, if_neg (fun h => hu (hkey h))]
  have h0 : (incG key C w F).coeff (key w) = 0 := hle hx'
  rw [coeff_incG, if_pos rfl] at h0
  rw [show F = 0 from Subtype.ext h0, map_zero]

theorem incG_mul {w w' u : W} (hu : key u = key w + key w') (F : C w) (F' : C w')
    (h : (F : R) * (F' : R) ∈ C u) : incG key C w F * incG key C w' F' = incG key C u ⟨_, h⟩ := by
  rw [incG_apply, incG_apply, incG_apply, AddMonoidAlgebra.single_mul_single, hu]

def vG (v : R → EReal) (x : AddMonoidAlgebra R M) : EReal := ⨅ m, v (x.coeff m)

variable {v : R → EReal}

theorem vG_zero (h0 : v 0 = ⊤) : vG v (0 : AddMonoidAlgebra R M) = ⊤ := by simp [vG, h0]

theorem vG_single (h0 : v 0 = ⊤) (m : M) (r : R) : vG v (AddMonoidAlgebra.single m r) = v r := by
  classical
  apply le_antisymm
  · exact (iInf_le _ m).trans (by rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same])
  · refine le_iInf fun u => ?_
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs
    · exact le_rfl
    · rw [h0]; exact le_top

theorem vG_incG (h0 : v 0 = ⊤) (w : W) (F : C w) : vG v (incG key C w F) = v F := vG_single h0 _ _

theorem vG_add (ha : ∀ r s, min (v r) (v s) ≤ v (r + s)) (x y : AddMonoidAlgebra R M) :
    min (vG v x) (vG v y) ≤ vG v (x + y) := by
  refine le_iInf fun m => ?_
  have : (x + y).coeff m = x.coeff m + y.coeff m := by simp
  rw [this]
  exact (min_le_min (iInf_le _ m) (iInf_le _ m)).trans (ha _ _)

theorem ereal_add_iInf {ι : Type} (c : ℝ) (f : ι → EReal) :
    (c : EReal) + ⨅ i, f i = ⨅ i, ((c : EReal) + f i) := by
  have hc : ∀ x : EReal, ((-c : ℝ) : EReal) + ((c : EReal) + x) = x := by
    intro x
    induction x using EReal.rec with
    | bot => simp
    | top => simp
    | coe x => norm_cast; ring
  have hc' : ∀ x : EReal, (c : EReal) + (((-c : ℝ) : EReal) + x) = x := by
    intro x
    induction x using EReal.rec with
    | bot => simp
    | top => simp
    | coe x => norm_cast; ring
  apply le_antisymm
  · exact le_iInf fun i => add_le_add le_rfl (iInf_le f i)
  · have h1 : ((-c : ℝ) : EReal) + ⨅ i, ((c : EReal) + f i) ≤ ⨅ i, f i :=
      le_iInf fun i => (add_le_add le_rfl (iInf_le (fun i => (c : EReal) + f i) i)).trans (hc (f i)).le
    have h2 := add_le_add (le_refl (c : EReal)) h1
    rwa [hc'] at h2

theorem vG_smul {a : K} {t : ℝ} (hs : ∀ r, v (a • r) = (t : EReal) + v r) (x : AddMonoidAlgebra R M) :
    vG v (a • x) = (t : EReal) + vG v x := by
  unfold vG
  rw [ereal_add_iInf]
  refine iInf_congr fun m => ?_
  have : (a • x).coeff m = a • x.coeff m := by simp
  rw [this, hs]

theorem vG_ne_bot (h0 : v 0 = ⊤) (hb : ∀ r, v r ≠ ⊥) (x : AddMonoidAlgebra R M) : vG v x ≠ ⊥ := by
  classical
  have hT : x.coeff.support.inf (fun m => v (x.coeff m)) ≤ vG v x := by
    refine le_iInf fun m => ?_
    by_cases hm : m ∈ x.coeff.support
    · exact Finset.inf_le hm
    · rw [Finsupp.notMem_support_iff.mp hm, h0]; exact le_top
  have hne : x.coeff.support.inf (fun m => v (x.coeff m)) ≠ ⊥ := by
    rw [Ne, Finset.inf_eq_bot_iff]; push Not
    exact fun m _ => hb _
  intro h
  exact hne (le_bot_iff.mp (h ▸ hT))

theorem vG_mul (h0 : v 0 = ⊤) (hm : ∀ r s, v (r * s) = v r + v s) (w w' : W) (F : C w) (F' : C w') :
    vG v (incG key C w F * incG key C w' F') = vG v (incG key C w F) + vG v (incG key C w' F') := by
  rw [incG_apply, incG_apply, AddMonoidAlgebra.single_mul_single, vG_single h0, vG_single h0, vG_single h0, hm]

end Graded

end Formalism.L2.Pj
end
end
