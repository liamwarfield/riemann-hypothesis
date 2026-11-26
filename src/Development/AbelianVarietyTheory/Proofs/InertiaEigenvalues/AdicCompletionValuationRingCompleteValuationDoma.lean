module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionValuationRingCompleteValuationDoma
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionValuationRingCompleteValuationDoma
open scoped NNReal

namespace GlobalTheory.ValCompletion

section General
variable {R : Type} [CommRing R] {I : Ideal R} {a : R}

theorem evalₐ_eq_zero_iff (h : I = Ideal.span {a}) (n : ℕ) (y : AdicCompletion I R) :
    AdicCompletion.evalₐ I n y = 0 ↔ algebraMap R (AdicCompletion I R) a ^ n ∣ y := by
  have hfg : I.FG := ⟨{a}, by simp [h]⟩
  have e : (I ^ n).map (algebraMap R (AdicCompletion I R)) =
      Ideal.span {algebraMap R (AdicCompletion I R) a ^ n} := by
    have : I ^ n = Ideal.span {a ^ n} := by rw [h, Ideal.span_singleton_pow]
    rw [this, Ideal.map_span, Set.image_singleton, map_pow]
  rw [← Ideal.mem_span_singleton, ← e, ← Submodule.restrictScalars_mem R,
    ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval hfg, LinearMap.mem_ker]
  have h' : (I ^ n • ⊤ : Ideal R) = I ^ n := by ext x; simp
  exact map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq R h').injective

theorem evalₐ_algebraMap (n : ℕ) (r : R) :
    AdicCompletion.evalₐ I n (algebraMap R (AdicCompletion I R) r) = Ideal.Quotient.mk _ r := by
  rw [AlgHom.commutes]; rfl

theorem factorPow_evalₐ {m n : ℕ} (h : m ≤ n) (y : AdicCompletion I R) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n y) = AdicCompletion.evalₐ I m y := by
  induction y using AdicCompletion.induction_on with
  | _ x =>
    simp only [AdicCompletion.evalₐ_mk]
    rw [← AdicCompletion.Ideal.mk_eq_mk I h x]
    rfl

theorem isUnit_evalₐ (y : AdicCompletion I R) (hy : IsUnit (AdicCompletion.evalₐ I 1 y)) (n : ℕ) :
    IsUnit (AdicCompletion.evalₐ I n y) := by
  have key : IsUnit (AdicCompletion.evalₐ I (n + 1) y) := by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) y)
    rw [← factorPow_evalₐ (show 1 ≤ n + 1 by omega), ← ha] at hy
    obtain ⟨b, hb⟩ := hy.exists_right_inv
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have h1 : a * b - 1 ∈ I ^ 1 := by
      rw [← Ideal.Quotient.eq]
      exact hb
    rw [pow_one] at h1
    have hn : IsNilpotent (Ideal.Quotient.mk (I ^ (n + 1)) (a * b - 1)) :=
      ⟨n + 1, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow h1 _⟩
    have hu := hn.isUnit_add_one
    rw [map_sub, map_one, sub_add_cancel, map_mul] at hu
    rw [← ha]
    exact isUnit_of_mul_isUnit_left hu
  rw [← factorPow_evalₐ (Nat.le_succ n)]
  exact key.map _

theorem isUnit_of_evalₐ (y : AdicCompletion I R) (hy : IsUnit (AdicCompletion.evalₐ I 1 y)) :
    IsUnit y := by
  let f : (n : ℕ) → Localization.Away y →+* R ⧸ I ^ n := fun n =>
    IsLocalization.Away.lift (g := (AdicCompletion.evalₐ I n).toRingHom) y (isUnit_evalₐ y hy n)
  have hf0 : ∀ n x, f n (algebraMap _ _ x) = AdicCompletion.evalₐ I n x := fun n x =>
    IsLocalization.Away.lift_eq y _ x
  have hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow I hle).comp (f n) = f m := by
    intro m n hle
    refine IsLocalization.ringHom_ext (Submonoid.powers y) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply, hf0, factorPow_evalₐ]
  have e : AdicCompletion.liftRingHom I f hf (algebraMap _ _ y) = y :=
    AdicCompletion.ext_evalₐ fun n => by rw [AdicCompletion.evalₐ_liftRingHom, hf0]
  rw [← e]
  exact (IsLocalization.Away.algebraMap_isUnit y).map _

end General

section Val
variable {V : Type} [CommRing V] [IsDomain V] [ValuationRing V] {x : V}

theorem not_pow_succ_dvd_pow (hx0 : x ≠ 0) (hxu : ¬ IsUnit x) (m : ℕ) : ¬ x ^ (m + 1) ∣ x ^ m := by
  rintro ⟨c, hc⟩
  apply hxu
  have h : x ^ m * 1 = x ^ m * (x * c) := by rw [mul_one]; nth_rewrite 1 [hc]; ring
  exact IsUnit.of_mul_eq_one c (mul_left_cancel₀ (pow_ne_zero m hx0) h).symm

theorem algebraMap_pow_ne_zero (hx0 : x ≠ 0) (hxu : ¬ IsUnit x) (m : ℕ) : (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ^ m ≠ 0 := by
  intro h
  have h2 := congrArg (AdicCompletion.evalₐ (Ideal.span {x}) (m + 1)) h
  rw [← map_pow, evalₐ_algebraMap, map_zero, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2
  exact not_pow_succ_dvd_pow hx0 hxu m h2

theorem exists_eq_mul_unit (hx0 : x ≠ 0) (hxu : ¬ IsUnit x) (y : AdicCompletion (Ideal.span {x}) V) (hy : y ≠ 0) :
    ∃ (a : V) (n : ℕ), a ∣ x ^ n ∧ ∃ u : (AdicCompletion (Ideal.span {x}) V)ˣ, y = algebraMap V (AdicCompletion (Ideal.span {x}) V) a * u := by
  obtain ⟨n, hn⟩ : ∃ n, AdicCompletion.evalₐ (Ideal.span {x}) n y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy (AdicCompletion.ext_evalₐ fun n => by rw [hc n, map_zero])
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (Ideal.span {x}) (n + 1) y)
  have hna : ¬ x ^ n ∣ a := by
    intro hd
    apply hn
    rw [← factorPow_evalₐ (Nat.le_succ n), ← ha, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hd
  obtain ⟨b, hb⟩ : a ∣ x ^ n := by
    obtain ⟨c, hc | hc⟩ := PreValuationRing.cond a (x ^ n)
    · exact ⟨c, hc.symm⟩
    · exact absurd ⟨c, hc.symm⟩ hna
  obtain ⟨z, hz⟩ : algebraMap V (AdicCompletion (Ideal.span {x}) V) x ^ (n + 1) ∣ y - algebraMap V (AdicCompletion (Ideal.span {x}) V) a := by
    rw [← evalₐ_eq_zero_iff rfl, map_sub, evalₐ_algebraMap, ← ha, sub_self]
  have hunit : IsUnit (1 + algebraMap V (AdicCompletion (Ideal.span {x}) V) b * algebraMap V (AdicCompletion (Ideal.span {x}) V) x * z) := by
    apply isUnit_of_evalₐ
    have hx1 : Ideal.Quotient.mk (Ideal.span {x} ^ 1) x = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]; exact Ideal.mem_span_singleton_self x
    rw [map_add (f := _), map_one, map_mul, map_mul, evalₐ_algebraMap, evalₐ_algebraMap, hx1,
      mul_zero, zero_mul, add_zero]
    exact isUnit_one
  refine ⟨a, n, ⟨b, hb⟩, hunit.unit, ?_⟩
  rw [IsUnit.unit_spec, mul_add, mul_one]
  have : y = algebraMap V (AdicCompletion (Ideal.span {x}) V) a + algebraMap V (AdicCompletion (Ideal.span {x}) V) x ^ (n + 1) * z := by rw [← hz]; ring
  rw [this, pow_succ, ← map_pow, hb, map_mul]
  ring

end Val

end GlobalTheory.ValCompletion


open GlobalTheory.ValCompletion in
theorem GlobalTheory.adicCompletion_valuationRing_props : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (x : V), x ≠ 0 → ¬ IsUnit x → IsDomain (AdicCompletion (Ideal.span {x}) V) ∧ PreValuationRing (AdicCompletion (Ideal.span {x}) V) ∧ algebraMap V (AdicCompletion (Ideal.span {x}) V) x ≠ 0 ∧ ¬ IsUnit (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ∧ IsAdicComplete (Ideal.span {algebraMap V (AdicCompletion (Ideal.span {x}) V) x}) (AdicCompletion (Ideal.span {x}) V) := by
  intro V _ _ _ x hx0 hxu
  have hne : algebraMap V (AdicCompletion (Ideal.span {x}) V) x ≠ 0 := by
    simpa using algebraMap_pow_ne_zero hx0 hxu 1
  have hnt : Nontrivial (AdicCompletion (Ideal.span {x}) V) := ⟨⟨_, _, hne⟩⟩
  have hdom : IsDomain (AdicCompletion (Ideal.span {x}) V) := by
    refine @NoZeroDivisors.to_isDomain _ _ hnt ⟨fun {y z} hyz => ?_⟩
    by_contra hc
    push_neg at hc
    obtain ⟨a, n, ⟨c, hc1⟩, u, rfl⟩ := exists_eq_mul_unit hx0 hxu y hc.1
    obtain ⟨b, m, ⟨d, hd1⟩, w, rfl⟩ := exists_eq_mul_unit hx0 hxu z hc.2
    apply algebraMap_pow_ne_zero hx0 hxu (n + m)
    have h1 : algebraMap V (AdicCompletion (Ideal.span {x}) V) a * algebraMap V (AdicCompletion (Ideal.span {x}) V) b = 0 := by
      have h2 : algebraMap V (AdicCompletion (Ideal.span {x}) V) a * algebraMap V (AdicCompletion (Ideal.span {x}) V) b * ((u : AdicCompletion (Ideal.span {x}) V) * w) = 0 := by
        rw [← hyz]; ring
      exact (Units.mul_left_eq_zero (u * w)).1 (by rw [Units.val_mul]; exact h2)
    rw [pow_add, ← map_pow, ← map_pow, hc1, hd1]
    simp only [map_mul]
    calc _ = (algebraMap V (AdicCompletion (Ideal.span {x}) V) a * algebraMap V (AdicCompletion (Ideal.span {x}) V) b) * (algebraMap V (AdicCompletion (Ideal.span {x}) V) c * algebraMap V (AdicCompletion (Ideal.span {x}) V) d) := by ring
      _ = 0 := by rw [h1, zero_mul]
  refine ⟨hdom, ⟨fun y z => ?_⟩, hne, ?_, ?_⟩
  · by_cases hy : y = 0
    · exact ⟨0, Or.inr (by rw [hy, mul_zero])⟩
    by_cases hz : z = 0
    · exact ⟨0, Or.inl (by rw [hz, mul_zero])⟩
    obtain ⟨a, n, -, u, rfl⟩ := exists_eq_mul_unit hx0 hxu y hy
    obtain ⟨b, m, -, w, rfl⟩ := exists_eq_mul_unit hx0 hxu z hz
    obtain ⟨c, hc | hc⟩ := PreValuationRing.cond a b
    · refine ⟨algebraMap V (AdicCompletion (Ideal.span {x}) V) c * ((u⁻¹ : (AdicCompletion (Ideal.span {x}) V)ˣ) : AdicCompletion (Ideal.span {x}) V) * w, Or.inl ?_⟩
      rw [← hc, map_mul]
      calc _ = algebraMap V (AdicCompletion (Ideal.span {x}) V) a * algebraMap V (AdicCompletion (Ideal.span {x}) V) c * w * ((u : AdicCompletion (Ideal.span {x}) V) * ((u⁻¹ : (AdicCompletion (Ideal.span {x}) V)ˣ) : AdicCompletion (Ideal.span {x}) V)) := by ring
        _ = _ := by rw [Units.mul_inv, mul_one]
    · refine ⟨algebraMap V (AdicCompletion (Ideal.span {x}) V) c * ((w⁻¹ : (AdicCompletion (Ideal.span {x}) V)ˣ) : AdicCompletion (Ideal.span {x}) V) * u, Or.inr ?_⟩
      rw [← hc, map_mul]
      calc _ = algebraMap V (AdicCompletion (Ideal.span {x}) V) b * algebraMap V (AdicCompletion (Ideal.span {x}) V) c * u * ((w : AdicCompletion (Ideal.span {x}) V) * ((w⁻¹ : (AdicCompletion (Ideal.span {x}) V)ˣ) : AdicCompletion (Ideal.span {x}) V)) := by ring
        _ = _ := by rw [Units.mul_inv, mul_one]
  · rintro ⟨v, hv⟩
    apply hxu
    obtain ⟨e, he⟩ := isUnit_iff_exists_inv.1 (⟨v, hv⟩ : IsUnit (algebraMap V (AdicCompletion (Ideal.span {x}) V) x))
    have h2 := congrArg (AdicCompletion.evalₐ (Ideal.span {x}) 1) he
    have hx1 : Ideal.Quotient.mk (Ideal.span {x} ^ 1) x = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]; exact Ideal.mem_span_singleton_self x
    rw [map_mul, evalₐ_algebraMap, hx1, zero_mul, map_one, eq_comm, ← map_one (Ideal.Quotient.mk _),
      Ideal.Quotient.eq_zero_iff_mem, pow_one, Ideal.mem_span_singleton] at h2
    exact isUnit_of_dvd_one h2
  · have e : (Ideal.span {x}).map (algebraMap V (AdicCompletion (Ideal.span {x}) V)) = Ideal.span {algebraMap V (AdicCompletion (Ideal.span {x}) V) x} := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [← e, IsAdicComplete.map_algebraMap_iff]
    exact AdicCompletion.isAdicComplete (Submodule.fg_span_singleton x)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionValuationRingCompleteValuationDomaStatement
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicCompletion_valuationRing_complete_valuationDomain : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (x : V), x ≠ 0 → ¬ IsUnit x → IsDomain (AdicCompletion (Ideal.span {x}) V) ∧ PreValuationRing (AdicCompletion (Ideal.span {x}) V) ∧ algebraMap V (AdicCompletion (Ideal.span {x}) V) x ≠ 0 ∧ ¬ IsUnit (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ∧ IsAdicComplete (Ideal.span {algebraMap V (AdicCompletion (Ideal.span {x}) V) x}) (AdicCompletion (Ideal.span {x}) V) := by
  first | exact @GlobalTheory.adicCompletion_valuationRing_props | exact GlobalTheory.adicCompletion_valuationRing_props | (intros; apply GlobalTheory.adicCompletion_valuationRing_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDetGenericSumMemOfCharpolyCoeffMem
open scoped BigOperators

namespace GlobalTheory

namespace Amitsur

open Matrix Polynomial

theorem det_one_sub_smul_mem_of_nilpotent {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]
    (U : Subring A) (t : A) (N : ℕ) (ht : t ^ N = 0) (S : Set (Matrix ι ι A))
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hsm : ∀ a ∈ S, t • a ∈ S)
    (hdet : ∀ a ∈ S, (1 - a).det ∈ U) :
    ∀ B ∈ AddSubmonoid.closure S, (1 - t • B).det ∈ U := by
  have hpow : ∀ (k : ℕ), ∀ a ∈ S, t ^ k • a ∈ S := by
    intro k a ha
    induction k with
    | zero => simpa using ha
    | succ k ih => rw [pow_succ', mul_smul]; exact hsm _ ih
  have hM1 : ∀ a ∈ S, ∀ y ∈ AddSubmonoid.closure S, a * y ∈ AddSubmonoid.closure S := by
    intro a ha y hy
    induction hy using AddSubmonoid.closure_induction with
    | mem x hx => exact AddSubmonoid.subset_closure (hmul a ha x hx)
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  have hM2 : ∀ y ∈ AddSubmonoid.closure S, t • y ∈ AddSubmonoid.closure S := by
    intro y hy
    induction hy using AddSubmonoid.closure_induction with
    | mem x hx => exact AddSubmonoid.subset_closure (hsm x hx)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  have hM3 : ∀ a ∈ S, ∀ (j : ℕ), ∀ y ∈ AddSubmonoid.closure S,
      a ^ j * y ∈ AddSubmonoid.closure S := by
    intro a ha j y hy
    induction j with
    | zero => simpa using hy
    | succ j ih => rw [pow_succ', mul_assoc]; exact hM1 a ha _ ih
  have step : ∀ e : ℕ, (∀ C ∈ AddSubmonoid.closure S, (1 - t ^ (e + 2) • C).det ∈ U) →
      ∀ B ∈ AddSubmonoid.closure S, (1 - t ^ (e + 1) • B).det ∈ U := by
    intro e ih
    have key : ∀ B ∈ AddSubmonoid.closure S, ∀ C ∈ AddSubmonoid.closure S,
        (1 - t ^ (e + 1) • (B + t • C)).det ∈ U := by
      intro B hB
      induction hB using AddSubmonoid.closure_induction_left with
      | zero =>
        intro C hC
        have := ih C hC
        rwa [zero_add, smul_smul, ← pow_succ]
      | add_left s hs B hB ihB =>
        intro C hC
        set a : Matrix ι ι A := t ^ (e + 1) • s with ha
        have haS : a ∈ S := hpow _ _ hs
        have haN : a ^ N = 0 := by
          rw [ha, _root_.smul_pow, ← pow_mul, add_mul, one_mul, pow_add, ht, mul_zero, zero_smul]
        set g : Matrix ι ι A := ∑ j ∈ Finset.range N, a ^ j with hg
        have hga : (1 - a) * g = 1 := by
          rw [hg, mul_neg_geom_sum, haN, sub_zero]
        set y : Matrix ι ι A := B + t • C with hy
        have hyM : y ∈ AddSubmonoid.closure S := add_mem hB (hM2 C hC)
        have hgy : g * y ∈ AddSubmonoid.closure S := by
          rw [hg, Finset.sum_mul]
          exact sum_mem fun j _ => hM3 a haS j y hyM
        have hC' : C + (t ^ e • s) * (g * y) ∈ AddSubmonoid.closure S :=
          add_mem hC (hM1 _ (hpow _ _ hs) _ hgy)
        have h1 := ihB _ hC'
        have e1 : B + t • (C + (t ^ e • s) * (g * y)) = g * y := by
          have h2 : t • ((t ^ e • s) * (g * y)) = a * (g * y) := by
            rw [← smul_mul_assoc, smul_smul, ← pow_succ']
          have h3 : g * y = (1 - a) * g * y + a * (g * y) := by noncomm_ring
          rw [smul_add, h2, ← add_assoc, ← hy]
          conv_rhs => rw [h3, hga, one_mul]
        rw [e1] at h1
        have e2 : 1 - t ^ (e + 1) • (s + B + t • C) = (1 - a) * (1 - t ^ (e + 1) • (g * y)) := by
          rw [mul_sub, mul_one, mul_smul_comm, ← mul_assoc, hga, one_mul, add_assoc, ← hy,
            smul_add, ← ha, sub_sub]
        rw [e2, det_mul]
        exact U.mul_mem (hdet a haS) h1
    intro B hB
    simpa using key B hB 0 (zero_mem _)
  have all : ∀ k e : ℕ, N ≤ e + k → ∀ B ∈ AddSubmonoid.closure S,
      (1 - t ^ (e + 1) • B).det ∈ U := by
    intro k
    induction k with
    | zero =>
      intro e he B _
      have : t ^ (e + 1) = 0 := pow_eq_zero_of_le (by omega) ht
      simp [this]
    | succ k ih =>
      intro e he
      exact step e (ih (e + 1) (by omega))
  intro B hB
  simpa using all N 0 (by omega) B hB

theorem eval₂_charpolyRev {R A ι : Type*} [CommRing R] [CommRing A] [Fintype ι] [DecidableEq ι]
    (φ : R →+* A) (u : A) (s : Matrix ι ι R) :
    (1 - u • s.map φ).det = s.charpolyRev.eval₂ φ u := by
  rw [← coe_eval₂RingHom, Matrix.charpolyRev, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.one_apply] <;> ring

theorem det_sum_smul_mem {R ι κ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (T : Subring R) (S : Set (Matrix ι ι R)) (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
    (hchar : ∀ a ∈ S, ∀ j, a.charpoly.coeff j ∈ T)
    (F : Finset κ) (c : κ → R) (s : κ → Matrix ι ι R) (hc : ∀ k, c k ∈ T) (hs : ∀ k, s k ∈ S) :
    (∑ k ∈ F, c k • s k).det ∈ T := by
  nontriviality R
  set n := Fintype.card ι with hn
  let I : Ideal R[X] := Ideal.span {X ^ (n + 1)}
  let π : R[X] →+* R[X] ⧸ I := Ideal.Quotient.mk I
  let φ : R →+* R[X] ⧸ I := π.comp C
  let U : Subring (R[X] ⧸ I) := (π.comp (Polynomial.mapRingHom T.subtype)).range
  have hφ : ∀ x ∈ T, φ x ∈ U := fun x hx => ⟨C ⟨x, hx⟩, by simp [φ]⟩
  have htU : π X ∈ U := ⟨X, by simp⟩
  have ht : π X ^ (n + 1) = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  let S' : Set (Matrix ι ι (R[X] ⧸ I)) := {a | ∃ u ∈ U, ∃ b ∈ S, a = u • b.map φ}
  have main := det_one_sub_smul_mem_of_nilpotent U (π X) (n + 1) ht S' (by
      rintro _ ⟨u, hu, a, ha, rfl⟩ _ ⟨v, hv, b, hb, rfl⟩
      refine ⟨u * v, U.mul_mem hu hv, a * b, hmul a ha b hb, ?_⟩
      rw [Matrix.map_mul, smul_mul_smul_comm]) (by
      rintro _ ⟨u, hu, a, ha, rfl⟩
      exact ⟨π X * u, U.mul_mem htU hu, a, ha, by rw [smul_smul]⟩) (by
      rintro _ ⟨u, hu, a, ha, rfl⟩
      rw [eval₂_charpolyRev, eval₂_eq_sum, Polynomial.sum]
      refine U.sum_mem fun j _ => U.mul_mem (hφ _ ?_) (U.pow_mem hu _)
      rw [← reverse_charpoly, coeff_reverse]
      exact hchar a ha _)
    ((∑ k ∈ F, c k • s k).map φ) (by
      have : (∑ k ∈ F, c k • s k).map φ = ∑ k ∈ F, φ (c k) • (s k).map φ := by
        ext i j
        simp [Matrix.sum_apply]
      rw [this]
      exact sum_mem fun k _ => AddSubmonoid.subset_closure ⟨_, hφ _ (hc k), _, hs k, rfl⟩)
  set B := ∑ k ∈ F, c k • s k
  rw [eval₂_charpolyRev] at main
  have h1 : B.charpolyRev.eval₂ φ (π X) = π B.charpolyRev := by
    rw [← Polynomial.hom_eval₂, eval₂_C_X]
  rw [h1] at main
  obtain ⟨p, hp⟩ := main
  have h2 : X ^ (n + 1) ∣ p.map T.subtype - B.charpolyRev :=
    Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hp)
  have h3 := X_pow_dvd_iff.1 h2 n (by omega)
  rw [coeff_sub, sub_eq_zero, coeff_map, ← reverse_charpoly, coeff_reverse,
    charpoly_natDegree_eq_dim, ← hn, revAt_le le_rfl, Nat.sub_self] at h3
  rw [det_eq_sign_charpoly_coeff, ← h3]
  exact T.mul_mem (T.pow_mem (T.neg_mem T.one_mem) _) (p.coeff n).2

end Amitsur

theorem coeff_det_generic_sum_mem_of_charpoly_coeff_mem :
    ∀ {O X G : Type} [CommRing O] [Monoid G] (T : Subalgebra O (X → O)) (n : ℕ)
      (r : X → G →* Matrix (Fin n) (Fin n) O),
      (∀ g j, (fun x => (r x g).charpoly.coeff j) ∈ T) →
      ∀ (m : ℕ) (g : Fin m → G) (d : Fin m →₀ ℕ),
        (fun x => AddMonoidAlgebra.coeff (Matrix.det (∑ k,
          (MvPolynomial.X k : MvPolynomial (Fin m) O) • (r x (g k)).map MvPolynomial.C)) d) ∈ T := by
  intro O X G _ _ T n r h m g d
  let ρ : G → Matrix (Fin n) (Fin n) (X → O) := fun a => Matrix.of fun i j x => r x a i j
  have hρx : ∀ a x, (ρ a).map (Pi.evalRingHom (fun _ : X => O) x) = r x a := by
    intro a x; ext i j; simp [ρ]
  have hρ : ∀ a b, ρ (a * b) = ρ a * ρ b := by
    intro a b
    ext i j x
    simp [ρ, Matrix.mul_apply]
  have hch : ∀ a j, (ρ a).charpoly.coeff j ∈ T := by
    intro a j
    convert h a j using 1
    funext x
    rw [← hρx, Matrix.charpoly_map, Polynomial.coeff_map]
    rfl
  let T' : Subring (MvPolynomial (Fin m) (X → O)) :=
    (MvPolynomial.map (σ := Fin m) T.toSubring.subtype).range
  have main := Amitsur.det_sum_smul_mem T'
    (Set.range fun a => (ρ a).map (MvPolynomial.C (σ := Fin m))) (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact ⟨a * b, by simp only [hρ, Matrix.map_mul]⟩) (by
      rintro _ ⟨a, rfl⟩ j
      rw [Matrix.charpoly_map, Polynomial.coeff_map]
      exact ⟨MvPolynomial.C ⟨_, hch a j⟩, MvPolynomial.map_C _ _⟩)
    Finset.univ (fun k => MvPolynomial.X k) (fun k => (ρ (g k)).map MvPolynomial.C)
    (fun k => ⟨MvPolynomial.X k, by simp⟩) (fun k => ⟨g k, rfl⟩)
  obtain ⟨p, hp⟩ := main
  have h1 : AddMonoidAlgebra.coeff (MvPolynomial.map T.toSubring.subtype p) d ∈ T := by
    rw [MvPolynomial.coeff_map]
    exact (AddMonoidAlgebra.coeff p d).2
  rw [hp] at h1
  convert h1 using 1
  funext x
  change _ = Pi.evalRingHom (fun _ : X => O) x (AddMonoidAlgebra.coeff _ d)
  rw [← MvPolynomial.coeff_map, RingHom.map_det]
  have heq : (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (r x (g k)).map (MvPolynomial.C (σ := Fin m))) =
      (MvPolynomial.map (Pi.evalRingHom (fun _ : X => O) x)).mapMatrix
        (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) • (ρ (g k)).map (MvPolynomial.C (σ := Fin m))) := by
    ext i j
    simp [Matrix.sum_apply, ρ]
  rw [heq]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowDescentCyclotomic
open NumberField

namespace GlobalTheory

namespace CyclotomicKummerDescent

theorem geom_sum_valuation {l : ℕ} (hl : l.Prime) {t : ℕ} (ht1 : 1 < t)
    (ht : (l : ℤ) ^ 2 ∣ (t : ℤ) - 1) (r : ℕ) :
    l ^ r ∣ ∑ i ∈ Finset.range (l ^ r), t ^ i ∧
      ¬ l ^ (r + 1) ∣ ∑ i ∈ Finset.range (l ^ r), t ^ i := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have h1 : (l : ℤ) ∣ (t : ℤ) - 1 := (dvd_pow_self _ two_ne_zero).trans ht
  have h2 : ¬ (l : ℤ) ∣ (t : ℤ) := fun h => hp.not_dvd_one (by simpa using dvd_sub h h1)
  have hlte : emultiplicity (l : ℤ) ((t : ℤ) ^ (l ^ r) - 1 ^ (l ^ r)) =
      emultiplicity (l : ℤ) ((t : ℤ) - 1) + r := by
    rcases hl.eq_two_or_odd' with rfl | hodd
    · have h := Int.two_pow_sub_pow' (x := t) (y := 1) (2 ^ r) (by simpa using ht)
        (by simpa using h2)
      have h3 : emultiplicity (2 : ℤ) ((2 ^ r : ℕ) : ℤ) = r := by
        push_cast
        exact emultiplicity_pow_self_of_prime Int.prime_two r
      rw [h3] at h
      simpa using h
    · rw [Int.emultiplicity_pow_sub_pow hl hodd h1 h2,
        emultiplicity_pow_self_of_prime hl.prime]
  rw [one_pow, ← geom_sum_mul, emultiplicity_mul hp, add_comm] at hlte
  have hfin : emultiplicity (l : ℤ) ((t : ℤ) - 1) ≠ ⊤ := by
    rw [← finiteMultiplicity_iff_emultiplicity_ne_top, Int.finiteMultiplicity_iff]
    refine ⟨by simpa using hl.ne_one, ?_⟩
    have : (1 : ℤ) < t := by exact_mod_cast ht1
    omega
  have h4 : emultiplicity (l : ℤ) (∑ i ∈ Finset.range (l ^ r), (t : ℤ) ^ i) = (r : ℕ∞) :=
    WithTop.add_left_cancel hfin hlte
  rw [emultiplicity_eq_coe] at h4
  exact_mod_cast h4

theorem exists_aut {E K : Type} [Field E] [NumberField E] [Field K] [Algebra E K] {M : ℕ}
    [NeZero M] [IsCyclotomicExtension {M} E K] {ζ : K} (hζ : IsPrimitiveRoot ζ M) {g : ℕ}
    (hg : g.Coprime M) :
    ∃ τ : K ≃ₐ[E] K, τ ζ = ζ ^ (g ^ (Module.finrank ℚ E).factorial) := by
  haveI := IsCyclotomicExtension.finiteDimensional {M} E K
  haveI := IsCyclotomicExtension.isGalois {M} E K
  haveI : NumberField K := NumberField.of_module_finite E K
  set H := (hζ.autToPow E).range with hH
  have hcard : Nat.card H = Module.finrank E K := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact (Nat.card_congr (MonoidHom.ofInjective (hζ.autToPow_injective E)).toEquiv).symm
  have htot : M.totient ≤ Module.finrank ℚ E * Module.finrank E K := by
    rw [Module.finrank_mul_finrank, ← Polynomial.natDegree_cyclotomic M ℚ,
      Polynomial.cyclotomic_eq_minpoly_rat hζ (NeZero.pos M)]
    exact minpoly.natDegree_le ζ
  have hidx : H.index * Nat.card H = M.totient := by
    rw [Subgroup.index_mul_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hle : H.index ≤ Module.finrank ℚ E := by
    rw [← hidx, hcard] at htot
    exact Nat.le_of_mul_le_mul_right htot Module.finrank_pos
  have hdvd : H.index ∣ (Module.finrank ℚ E).factorial :=
    Nat.dvd_factorial (Nat.pos_of_ne_zero H.index_ne_zero_of_finite) hle
  have hmem : ZMod.unitOfCoprime g hg ^ (Module.finrank ℚ E).factorial ∈ H := by
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, pow_mul]
    exact H.pow_mem (H.pow_index_mem _) c
  obtain ⟨τ, hτ⟩ := hmem
  refine ⟨τ, ?_⟩
  rw [← hζ.autToPow_spec E τ, hτ, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime,
    ← Nat.cast_pow, ZMod.val_natCast]
  exact (pow_eq_pow_mod _ hζ.pow_eq_one).symm

theorem descent {E K : Type} [Field E] [Field K] [Algebra E K] {M : ℕ}
    [NeZero M] [IsCyclotomicExtension {M} E K] {ζ : K} (hζ : IsPrimitiveRoot ζ M) {k n : ℕ}
    (τ : K ≃ₐ[E] K) (hτ : τ ζ = ζ ^ (k + 1))
    (hN : M ∣ (∑ i ∈ Finset.range n, (k + 1) ^ i) * k) {u : E} {w : K} (hw0 : w ≠ 0)
    (hw : w ^ M = algebraMap E K u) :
    ∃ (α : K) (v : E), α ^ M = 1 ∧ α ^ (∑ i ∈ Finset.range n, (k + 1) ^ i) = 1 ∧
      algebraMap E K v * α = w ^ k := by
  haveI := IsCyclotomicExtension.finiteDimensional {M} E K
  haveI := IsCyclotomicExtension.isGalois {M} E K
  have hext : ∀ σ σ' : K ≃ₐ[E] K, σ ζ = σ' ζ → σ = σ' := by
    intro σ σ' h
    apply hζ.autToPow_injective E
    rw [← hζ.autToPow_spec E σ, ← hζ.autToPow_spec E σ'] at h
    exact Units.ext (ZMod.val_injective M (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))
  have hcomm : ∀ σ : K ≃ₐ[E] K, σ * τ = τ * σ := fun σ =>
    hζ.autToPow_injective E (by rw [map_mul, map_mul, mul_comm])
  have hroot : ∀ η : K, η ^ M = 1 → τ η = η ^ (k + 1) := by
    intro η hη
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hη
    rw [map_pow, hτ, ← pow_mul, ← pow_mul, mul_comm]
  have hcoc : ∀ σ : K ≃ₐ[E] K, ∃ a : K, a ^ M = 1 ∧ σ w = a * w := by
    intro σ
    refine ⟨σ w / w, ?_, by field_simp⟩
    rw [div_pow, ← map_pow, hw, AlgEquiv.commutes, ← hw, div_self (pow_ne_zero _ hw0)]
  have hne : ∀ a : K, a ^ M = 1 → a ≠ 0 := by
    rintro a ha rfl
    rw [zero_pow (NeZero.ne M)] at ha
    exact zero_ne_one ha
  obtain ⟨α, hαM, hα⟩ := hcoc τ
  have hα0 := hne α hαM
  have hiter : ∀ m : ℕ, (τ ^ m) w = α ^ (∑ i ∈ Finset.range m, (k + 1) ^ i) * w ∧
      (τ ^ m) ζ = ζ ^ ((k + 1) ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih.1, ih.2, map_mul, map_pow,
        map_pow, hτ, hα, hroot α hαM, geom_sum_succ]
      constructor <;> ring
  have hgeom : ∀ m : ℕ, (k + 1) ^ m = (∑ i ∈ Finset.range m, (k + 1) ^ i) * k + 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, pow_succ, add_mul, mul_add, mul_one]; omega
  have hτn : τ ^ n = 1 := by
    apply hext
    obtain ⟨c, hc⟩ := hN
    rw [(hiter n).2, hgeom, hc, pow_succ, pow_mul, hζ.pow_eq_one]
    simp
  have hαN : α ^ (∑ i ∈ Finset.range n, (k + 1) ^ i) = 1 := by
    have h := (hiter n).1
    rw [hτn, AlgEquiv.one_apply] at h
    exact mul_right_cancel₀ hw0 (by rw [← h, one_mul])
  have hfix : ∀ σ : K ≃ₐ[E] K, σ (w ^ k / α) = w ^ k / α := by
    intro σ
    obtain ⟨a, haM, ha⟩ := hcoc σ
    have ha0 := hne a haM
    have h := congrArg (fun f : K ≃ₐ[E] K => f w) (hcomm σ)
    simp only [AlgEquiv.mul_apply] at h
    rw [hα, ha, map_mul, map_mul, ha, hα, hroot a haM] at h
    have hσα : σ α = a ^ k * α :=
      mul_right_cancel₀ (mul_ne_zero ha0 hw0) (by rw [h]; ring)
    rw [map_div₀, map_pow, hσα, ha, mul_pow]
    field_simp
  obtain ⟨v, hv⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).mpr hfix
  exact ⟨α, v, hαM, hαN, by rw [hv]; field_simp⟩

end CyclotomicKummerDescent


open CyclotomicKummerDescent in
theorem exists_pow_descent_cyclotomic :
    ∀ (E : Type) [Field E] [NumberField E] (l r : ℕ), l.Prime → ∃ M : ℕ, 0 < M ∧ l ^ r ∣ M ∧
    ∀ (Ω : Type) [Field Ω] [Algebra E Ω] (ζ : Ω), IsPrimitiveRoot ζ M → ∀ (u : E) (w : Ω),
      w ∈ IntermediateField.adjoin E {ζ} → w ^ M = algebraMap E Ω u →
        ∃ v : E, v ^ (l ^ r) = u := by
  intro E _ _ l r hl
  set m := (Module.finrank ℚ E).factorial with hm
  have ht1 : 1 < (1 + l ^ 2) ^ m :=
    Nat.one_lt_pow (Nat.factorial_ne_zero _) (by have := pow_pos hl.pos 2; omega)
  obtain ⟨k, hk⟩ : ∃ k, (1 + l ^ 2) ^ m = k + 1 := ⟨_, (Nat.sub_add_cancel ht1.le).symm⟩
  have hk0 : k ≠ 0 := by omega
  obtain ⟨s, e, he, hke⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk0 l hl.ne_one
  have hdiv : (l : ℤ) ^ 2 ∣ (((1 + l ^ 2) ^ m : ℕ) : ℤ) - 1 := by
    have := sub_dvd_pow_sub_pow (1 + (l : ℤ) ^ 2) 1 m
    simpa using this
  obtain ⟨hN1, hN2⟩ := geom_sum_valuation hl ht1 hdiv r
  rw [hk] at hN1 hN2
  refine ⟨l ^ (r + s), pow_pos hl.pos _, pow_dvd_pow _ (by omega), ?_⟩
  intro Ω _ _ ζ hζ u w hwK hw
  haveI : NeZero (l ^ (r + s)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hint : IsIntegral E ζ := (hζ.isIntegral (NeZero.pos _)).tower_top
  set K := IntermediateField.adjoin E {ζ} with hK
  haveI : IsCyclotomicExtension {l ^ (r + s)} E K := by
    change IsCyclotomicExtension {l ^ (r + s)} E K.toSubalgebra
    rw [hK, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hζ.adjoin_isCyclotomicExtension E
  let ζ' : K := ⟨ζ, IntermediateField.mem_adjoin_simple_self E ζ⟩
  have hζ' : IsPrimitiveRoot ζ' (l ^ (r + s)) :=
    IsPrimitiveRoot.of_map_of_injective (f := K.val) hζ K.val.injective
  let w' : K := ⟨w, hwK⟩
  have hw' : w' ^ (l ^ (r + s)) = algebraMap E K u := Subtype.ext hw
  rcases eq_or_ne u 0 with rfl | hu
  · exact ⟨0, zero_pow (pow_ne_zero _ hl.ne_zero)⟩
  have hw0 : w' ≠ 0 := by
    intro h
    rw [h, zero_pow (NeZero.ne _), eq_comm, map_eq_zero] at hw'
    exact hu hw'
  have hg : (1 + l ^ 2).Coprime (l ^ (r + s)) := by
    apply Nat.Coprime.pow_right
    rw [sq, Nat.coprime_add_mul_left_left]
    exact Nat.coprime_one_left l
  obtain ⟨τ, hτ⟩ := exists_aut (E := E) hζ' hg
  rw [← hm, hk] at hτ
  obtain ⟨α, v, hαM, hαN, hv⟩ := descent hζ' (n := l ^ r) τ hτ
    (by rw [pow_add]; exact mul_dvd_mul hN1 ⟨e, hke⟩) hw0 hw'
  have hαr : α ^ (l ^ r) = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hl).mp (orderOf_dvd_of_pow_eq_one hαM)
    have h1 := orderOf_dvd_of_pow_eq_one hαN
    rw [hj] at h1
    have hjr : j ≤ r := by
      by_contra hc
      exact hN2 ((pow_dvd_pow l (by omega)).trans h1)
    exact orderOf_dvd_iff_pow_eq_one.mp (hj ▸ pow_dvd_pow l hjr)
  have hvu : v ^ (l ^ r) = u ^ e := by
    apply (algebraMap E K).injective
    have h := congrArg (· ^ (l ^ r)) hv
    simp only [mul_pow, hαr, mul_one] at h
    rw [map_pow, map_pow, h, ← hw', hke, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hco : IsCoprime (e : ℤ) ((l ^ r : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr
      (Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hl).mpr he).symm)
  obtain ⟨a, b, hab⟩ := hco
  refine ⟨v ^ a * u ^ b, ?_⟩
  rw [mul_pow, ← zpow_natCast (v ^ a), ← zpow_natCast (u ^ b), ← zpow_mul, ← zpow_mul, mul_comm a,
    zpow_mul, zpow_natCast, hvu, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hu, mul_comm _ a, hab,
    zpow_one]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LangXRoot
namespace GlobalTheory.PMonE.LangIsogenyConstruction

open Polynomial

section Lang
variable {k V : Type} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]

noncomputable def langX (q : ℕ) (a : ℕ → k) : ℕ → k[X]
  | 0 => C (a 0) * X ^ q
  | (i + 1) => (langX q a i) ^ q + C (a (i + 1)) * X ^ q

theorem langX_dvd (q : ℕ) (hq : 1 < q) (a : ℕ → k) (i : ℕ) : (X : k[X]) ^ q ∣ langX q a i := by
  induction i with
  | zero => exact Dvd.intro_left _ rfl
  | succ i ih =>
    exact dvd_add (ih.trans (dvd_pow_self _ (by omega))) (Dvd.intro_left _ rfl)

theorem langX_ne (q : ℕ) (hq : 1 < q) (a : ℕ → k) (i : ℕ) (h : ∃ j ≤ i, a j ≠ 0) :
    langX q a i ≠ 0 := by
  induction i with
  | zero =>
    obtain ⟨j, hj, ha⟩ := h
    obtain rfl : j = 0 := by omega
    simp [langX, ha]
  | succ i ih =>
    intro h0
    have h0' : (langX q a i) ^ q + C (a (i + 1)) * X ^ q = 0 := h0
    have h1 : (langX q a i) ^ q = - (C (a (i + 1)) * X ^ q) := eq_neg_of_add_eq_zero_left h0'
    have hd : (X : k[X]) ^ (q * q) ∣ (langX q a i) ^ q := by
      rw [pow_mul]; exact pow_dvd_pow_of_dvd (langX_dvd q hq a i) q
    have hc := (X_pow_dvd_iff.1 hd) q (by nlinarith)
    rw [h1] at hc
    have ha : a (i + 1) = 0 := by simpa using hc
    have hX : langX q a i = 0 := by
      rw [ha] at h1
      simp only [map_zero, zero_mul, neg_zero] at h1
      exact pow_eq_zero_iff (by omega) |>.1 h1
    refine ih ?_ hX
    obtain ⟨j, hj, haj⟩ := h
    refine ⟨j, ?_, haj⟩
    by_contra hji
    have : j = i + 1 := by omega
    exact haj (this ▸ ha)

theorem langX_root (q : ℕ) (hq : 1 < q) (a : ℕ → k) (i : ℕ) (h : langX q a i ≠ 0) :
    ∃ y : k, y ≠ 0 ∧ (langX q a i).eval y = y := by
  obtain ⟨T, hT⟩ := langX_dvd q hq a i
  have hT0 : T ≠ 0 := by
    rintro rfl
    exact h (by simpa using hT)
  have hdeg : 0 < (X ^ (q - 1) * T).degree := by
    rw [degree_mul, degree_X_pow]
    have h0 : 0 ≤ T.degree := zero_le_degree_iff.2 hT0
    have h1 : (0 : WithBot ℕ) < ((q - 1 : ℕ) : WithBot ℕ) := by
      exact_mod_cast (by omega : 0 < q - 1)
    exact add_pos_of_pos_of_nonneg h1 h0
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root (X ^ (q - 1) * T - C 1)
    (by rw [degree_sub_C hdeg]; exact hdeg.ne')
  have hy' : y ^ (q - 1) * T.eval y = 1 := by
    have h2 : (X ^ (q - 1) * T - C 1).eval y = 0 := hy
    simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_C] at h2
    exact sub_eq_zero.1 h2
  refine ⟨y, ?_, ?_⟩
  · rintro rfl
    rw [zero_pow (by omega)] at hy'
    simp at hy'
  · rw [hT]
    simp only [eval_mul, eval_pow, eval_X]
    have h3 : y ^ q = y * y ^ (q - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [h3, mul_assoc, hy', mul_one]

theorem as_root (q : ℕ) (hq : 1 < q) (c : k) : ∃ z : k, z ^ q - z = c := by
  have hdeg : (X ^ q - (X + C c) : k[X]).degree = q := by
    rw [degree_sub_eq_left_of_degree_lt, degree_X_pow]
    rw [degree_X_pow, degree_X_add_C]
    exact_mod_cast hq
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (X ^ q - (X + C c) : k[X]) (by
    rw [hdeg]; exact_mod_cast (by omega : q ≠ 0))
  have h2 : (X ^ q - (X + C c) : k[X]).eval z = 0 := hz
  simp only [eval_sub, eval_add, eval_pow, eval_X, eval_C] at h2
  exact ⟨z, by linear_combination h2⟩

def langQ (U : Submodule k V) (F : V → V) (v : V) (r : ℕ) : Prop :=
  ∃ u ∈ U, ∃ a : ℕ → k, F^[r] v = u + ∑ i ∈ Finset.range r, a i • F^[i] v

theorem lang_span [FiniteDimensional k V] (q : ℕ) (hq : 1 < q) (F : V →+ V)
    (hF : ∀ (a : k) (v : V), F (a • v) = a ^ q • F v) (hinj : Function.Injective F) :
    Submodule.span k {v : V | F v = v} = ⊤ := by
  classical
  set U := Submodule.span k {v : V | F v = v} with hU
  have hfix : ∀ w, F w = w → w ∈ U := fun w hw => Submodule.subset_span hw
  have h2 : ∀ u ∈ U, ∃ u' ∈ U, F u' - u' = u := by
    intro u hu
    induction hu using Submodule.closure_induction with
    | zero => exact ⟨0, U.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨x', hx', ex⟩ := hx
      obtain ⟨y', hy', ey⟩ := hy
      exact ⟨x' + y', U.add_mem hx' hy', by rw [map_add (f := _), ← ex, ← ey]; abel⟩
    | smul_mem c w hw =>
      obtain ⟨z, hz⟩ := as_root q hq c
      refine ⟨z • w, U.smul_mem _ (hfix w hw), ?_⟩
      rw [hF, show F w = w from hw, ← sub_smul, hz]
  have h3 : ∀ u ∈ U, ∃ u' ∈ U, F u' = u := by
    intro u hu
    induction hu using Submodule.closure_induction with
    | zero => exact ⟨0, U.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨x', hx', ex⟩ := hx
      obtain ⟨y', hy', ey⟩ := hy
      exact ⟨x' + y', U.add_mem hx' hy', by rw [map_add (f := _), ← ex, ← ey]⟩
    | smul_mem c w hw =>
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c (by omega : 0 < q)
      refine ⟨z • w, U.smul_mem _ (hfix w hw), ?_⟩
      rw [hF, show F w = w from hw, hz]
  have h4 : ∀ x, F x ∈ U → x ∈ U := by
    intro x hx
    obtain ⟨u', hu', e⟩ := h3 _ hx
    rw [← hinj e]; exact hu'
  have h4' : ∀ (n : ℕ) (x : V), (⇑F)^[n] x ∈ U → x ∈ U := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      rw [Function.iterate_succ_apply'] at hx
      exact ih x (h4 _ hx)
  by_contra hne
  obtain ⟨v, hv⟩ : ∃ v, v ∉ U := by
    by_contra hall
    push Not at hall
    exact hne (eq_top_iff.2 fun x _ => hall x)
  have hex : ∃ r, langQ U (⇑F) v r := by
    let N : ℕ →o Submodule k V :=
      ⟨fun j => Submodule.span k (Set.range fun i : Fin j => (⇑F)^[(i : ℕ)] v), by
        intro j j' h
        refine Submodule.span_mono ?_
        rintro _ ⟨i, rfl⟩
        exact ⟨Fin.castLE h i, rfl⟩⟩
    obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.2 inferInstance N
    have hmem : (⇑F)^[n] v ∈ N (n + 1) := Submodule.subset_span ⟨Fin.last n, rfl⟩
    rw [← hn (n + 1) (by omega)] at hmem
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hmem
    refine ⟨n, 0, U.zero_mem, fun i => if h : i < n then c ⟨i, h⟩ else 0, ?_⟩
    rw [zero_add, ← hc, Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [i.2]
  obtain ⟨r, ⟨u, hu, a, ha⟩, hmin⟩ : ∃ r, langQ U (⇑F) v r ∧ ∀ j < r, ¬ langQ U (⇑F) v j :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso
      rw [h0] at ha
      simp only [Function.iterate_zero, id_eq, Finset.range_zero, Finset.sum_empty, add_zero] at ha
      exact hv (ha ▸ hu)
    · exact ⟨r - 1, by omega⟩
  by_cases hall : ∀ j ≤ s, a j = 0
  · have h0 : ∑ i ∈ Finset.range (s + 1), a i • (⇑F)^[i] v = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [hall i (by simpa [Nat.lt_succ_iff] using hi), zero_smul]
    rw [h0, add_zero] at ha
    exact hv (h4' (s + 1) v (ha ▸ hu))
  · push Not at hall
    obtain ⟨y, hy0, hy⟩ := langX_root q hq a s (langX_ne q hq a s hall)
    obtain ⟨x, hxdef⟩ : ∃ x : ℕ → k, x = fun i => (langX q a i).eval y := ⟨_, rfl⟩
    have hx0 : x 0 = y ^ q * a 0 := by
      rw [hxdef]
      show (C (a 0) * X ^ q : k[X]).eval y = _
      simp only [eval_mul, eval_C, eval_pow, eval_X]
      ring
    have hxs : ∀ i, x (i + 1) = (x i) ^ q + y ^ q * a (i + 1) := by
      intro i
      rw [hxdef]
      show ((langX q a i) ^ q + C (a (i + 1)) * X ^ q : k[X]).eval y =
        ((langX q a i).eval y) ^ q + y ^ q * a (i + 1)
      simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
      ring
    have hxy : x s = y := by rw [hxdef]; exact hy
    obtain ⟨z, hz⟩ : ∃ z : V, z = ∑ i ∈ Finset.range (s + 1), x i • (⇑F)^[i] v := ⟨_, rfl⟩
    have hFz : F z - z = y ^ q • u := by
      have e1 : F z = ∑ i ∈ Finset.range s, (x i) ^ q • (⇑F)^[i + 1] v +
          y ^ q • (⇑F)^[s + 1] v := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hz, map_sum, Finset.sum_range_succ]
        congr 1
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [hF, Function.iterate_succ_apply']
        · rw [hF, Function.iterate_succ_apply', hxy]
      have e2 : z = x 0 • v + ∑ i ∈ Finset.range s, x (i + 1) • (⇑F)^[i + 1] v := by
        rw [hz, Finset.sum_range_succ', add_comm]; rfl
      have e3 : ∑ i ∈ Finset.range (s + 1), a i • (⇑F)^[i] v =
          a 0 • v + ∑ i ∈ Finset.range s, a (i + 1) • (⇑F)^[i + 1] v := by
        rw [Finset.sum_range_succ', add_comm]; rfl
      rw [sub_eq_iff_eq_add, e1, ha, e3]
      conv_rhs => rw [e2]
      simp only [hx0, hxs, add_smul, Finset.sum_add_distrib, smul_add, Finset.smul_sum, smul_smul]
      abel
    obtain ⟨u', hu', e'⟩ := h2 (y ^ q • u) (U.smul_mem _ hu)
    have hzU : z ∈ U := by
      have h5 : F (z - u') = z - u' := by
        rw [map_sub, sub_eq_sub_iff_sub_eq_sub, hFz, e']
      have h6 := U.add_mem (hfix _ h5) hu'
      simpa using h6
    apply hmin s (by omega)
    refine ⟨y⁻¹ • z, U.smul_mem _ hzU, fun i => - (y⁻¹ * x i), ?_⟩
    rw [hz, Finset.sum_range_succ, hxy, smul_add, smul_smul, inv_mul_cancel₀ hy0, one_smul,
      Finset.smul_sum]
    simp only [neg_smul, Finset.sum_neg_distrib, smul_smul]
    abel

theorem lang_basis [FiniteDimensional k V] (q : ℕ) (hq : 1 < q) (F : V →+ V)
    (hF : ∀ (a : k) (v : V), F (a • v) = a ^ q • F v) (hinj : Function.Injective F) :
    ∃ b : Module.Basis (Fin (Module.finrank k V)) k V, ∀ i, F (b i) = b i := by
  classical
  have hs : ⊤ ≤ Submodule.span k {v : V | F v = v} := (lang_span q hq F hF hinj).ge
  let b' := Module.Basis.ofSpan hs
  haveI : Finite _ := Module.Finite.finite_basis b'
  letI := Fintype.ofFinite ((linearIndepOn_empty k id).extend (Set.empty_subset {v : V | F v = v}))
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b').symm
  refine ⟨b'.reindex e, fun i => ?_⟩
  have h1 : b' (e.symm i) ∈ {v : V | F v = v} := Module.Basis.ofSpan_subset hs ⟨e.symm i, rfl⟩
  simpa using h1

end Lang

end GlobalTheory.PMonE.LangIsogenyConstruction
end
