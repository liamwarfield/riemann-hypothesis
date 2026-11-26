module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegrallyClosedPowerSeries
open IsLocalRing

namespace GlobalTheory.PowerSeriesNormal

open PowerSeries

variable {R : Type} [CommRing R] [IsDomain R]

theorem dvd_of_pow_dvd [IsNoetherianRing R] [IsIntegrallyClosed R] {f g h : R} (hg : g ≠ 0)
    (hh : h ≠ 0) (H : ∀ n : ℕ, g ^ n ∣ h * f ^ n) : g ∣ f := by
  classical
  let K := FractionRing R
  have hinj := IsFractionRing.injective R K
  have hgK : algebraMap R K g ≠ 0 := (map_ne_zero_iff _ hinj).2 hg
  have hhK : algebraMap R K h ≠ 0 := (map_ne_zero_iff _ hinj).2 hh
  set x : K := algebraMap R K f / algebraMap R K g with hx
  let M : Submodule R K := Submodule.span R {(algebraMap R K h)⁻¹}
  have hpow : ∀ n : ℕ, x ^ n ∈ M := by
    intro n
    obtain ⟨c, hc⟩ := H n
    have : x ^ n = c • (algebraMap R K h)⁻¹ := by
      rw [Algebra.smul_def, hx, div_pow, eq_mul_inv_iff_mul_eq₀ hhK, div_mul_eq_mul_div,
        div_eq_iff (pow_ne_zero _ hgK)]
      have := congrArg (algebraMap R K) hc
      simp only [map_mul, map_pow] at this
      linear_combination this
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  have hle : Subalgebra.toSubmodule (Algebra.adjoin R {x}) ≤ M := by
    intro y hy
    rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨p, rfl⟩ := hy
    change Polynomial.aeval x p ∈ M
    rw [Polynomial.aeval_eq_sum_range]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hpow i)
  have : IsNoetherian R M := isNoetherian_of_fg_of_noetherian M (Submodule.fg_span_singleton _)
  have := isNoetherian_of_le hle
  have hint : IsIntegral R x :=
    isIntegral_of_submodule_noetherian _ this x (Algebra.subset_adjoin rfl)
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff K).1 inferInstance hint
  refine ⟨y, hinj ?_⟩
  rw [map_mul, hy, hx, mul_comm]
  exact (div_mul_cancel₀ _ hgK).symm

theorem dvd_of_dvd_X_pow_mul {u a : R⟦X⟧} (hu : ¬ (X : R⟦X⟧) ∣ u) {c : ℕ}
    (h : u ∣ X ^ c * a) : u ∣ a := by
  induction c generalizing a with
  | zero => simpa using h
  | succ c ih =>
    apply ih
    obtain ⟨v, hv⟩ := h
    have hXv : (X : R⟦X⟧) ∣ u * v := ⟨X ^ c * a, by rw [← hv]; ring⟩
    rcases X_prime.dvd_or_dvd hXv with hu' | ⟨w, hw⟩
    · exact absurd hu' hu
    · refine ⟨w, mul_left_cancel₀ (X_ne_zero (R := R)) ?_⟩
      calc X * (X ^ c * a) = X ^ (c + 1) * a := by ring
        _ = u * v := hv
        _ = X * (u * w) := by rw [hw]; ring

theorem exists_eq_X_pow_mul {f : R⟦X⟧} (hf : f ≠ 0) :
    ∃ (a : ℕ) (f₁ : R⟦X⟧), ¬ (X : R⟦X⟧) ∣ f₁ ∧ f = X ^ a * f₁ := by
  obtain ⟨f₁, hf₁⟩ := X_pow_order_dvd (φ := f)
  refine ⟨f.order.toNat, f₁, ?_, hf₁⟩
  rintro ⟨e, he⟩
  have hd : (X : R⟦X⟧) ^ (f.order.toNat + 1) ∣ f := ⟨e, by rw [pow_succ, mul_assoc, ← he, ← hf₁]⟩
  rw [X_pow_dvd_iff] at hd
  exact coeff_order hf (hd _ (Nat.lt_succ_self _))

def almostMultiples (g : R⟦X⟧) : Ideal R⟦X⟧ where
  carrier := {f | ∃ h, h ≠ 0 ∧ ∀ n : ℕ, g ^ n ∣ h * f ^ n}
  zero_mem' := ⟨1, one_ne_zero, fun n => by
    rw [one_mul]; exact pow_dvd_pow_of_dvd (dvd_zero g) n⟩
  add_mem' := by
    rintro a b ⟨h, hh, H⟩ ⟨k, hk, K⟩
    refine ⟨h * k, mul_ne_zero hh hk, fun n => ?_⟩
    rw [add_pow, Finset.mul_sum]
    refine Finset.dvd_sum fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have e : g ^ n = g ^ i * g ^ (n - i) := by rw [← pow_add, Nat.add_sub_cancel' hi']
    have e2 : h * k * (a ^ i * b ^ (n - i) * (n.choose i : R⟦X⟧))
        = (h * a ^ i) * (k * b ^ (n - i)) * (n.choose i : R⟦X⟧) := by ring
    rw [e, e2]
    exact (mul_dvd_mul (H i) (K _)).mul_right _
  smul_mem' := by
    rintro c a ⟨h, hh, H⟩
    refine ⟨h, hh, fun n => ?_⟩
    rw [smul_eq_mul, mul_pow, mul_left_comm]
    exact (H n).mul_left _

private theorem mem_almostMultiples_iff {g f : R⟦X⟧} :
    f ∈ almostMultiples g ↔ ∃ h, h ≠ 0 ∧ ∀ n : ℕ, g ^ n ∣ h * f ^ n := Iff.rfl

private theorem constantCoeff_dvd_of_mem_almostMultiples [IsNoetherianRing R] [IsIntegrallyClosed R] {g e : R⟦X⟧}
    (hg : ¬ (X : R⟦X⟧) ∣ g) (he : e ∈ almostMultiples g) :
    constantCoeff g ∣ constantCoeff e := by
  obtain ⟨h, hh, H⟩ := mem_almostMultiples_iff.1 he
  obtain ⟨b, h₁, hh₁, rfl⟩ := exists_eq_X_pow_mul hh
  have H' : ∀ n : ℕ, g ^ n ∣ h₁ * e ^ n := fun n =>
    dvd_of_dvd_X_pow_mul (fun hX => hg (X_prime.dvd_of_dvd_pow hX))
      (c := b) (by simpa [mul_assoc] using H n)
  have hg0 : constantCoeff g ≠ 0 := fun h0 => hg (X_dvd_iff.2 h0)
  have hh0 : constantCoeff h₁ ≠ 0 := fun h0 => hh₁ (X_dvd_iff.2 h0)
  exact dvd_of_pow_dvd hg0 hh0 fun n => by
    simpa [map_mul, map_pow] using map_dvd constantCoeff (H' n)

private theorem mem_almostMultiples_of_X_pow_mul_mem {g e : R⟦X⟧} (hg : ¬ (X : R⟦X⟧) ∣ g) {k : ℕ}
    (he : X ^ k * e ∈ almostMultiples g) : e ∈ almostMultiples g := by
  obtain ⟨h, hh, H⟩ := mem_almostMultiples_iff.1 he
  refine mem_almostMultiples_iff.2 ⟨h, hh, fun n => ?_⟩
  have : h * (X ^ k * e) ^ n = X ^ (k * n) * (h * e ^ n) := by ring
  exact dvd_of_dvd_X_pow_mul (fun hX => hg (X_prime.dvd_of_dvd_pow hX)) (this ▸ H n)

private theorem exists_X_pow_dvd_sub_mul_of_mem_almostMultiples [IsNoetherianRing R] [IsIntegrallyClosed R] {g f : R⟦X⟧}
    (hg : ¬ (X : R⟦X⟧) ∣ g) (hf : f ∈ almostMultiples g) :
    ∀ k : ℕ, ∃ r : R⟦X⟧, X ^ k ∣ f - g * r := by
  have hgI : g ∈ almostMultiples g :=
    mem_almostMultiples_iff.2 ⟨1, one_ne_zero, fun n => by rw [one_mul]⟩
  intro k
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨r, e, he⟩ := ih
    have hmem : X ^ k * e ∈ almostMultiples g := by
      rw [← he]; exact Ideal.sub_mem _ hf (Ideal.mul_mem_right _ _ hgI)
    obtain ⟨c, hc⟩ := constantCoeff_dvd_of_mem_almostMultiples hg (mem_almostMultiples_of_X_pow_mul_mem hg hmem)
    refine ⟨r + C c * X ^ k, ?_⟩
    have hX : (X : R⟦X⟧) ∣ e - g * C c := by
      rw [X_dvd_iff]; simp [hc]
    obtain ⟨w, hw⟩ := hX
    refine ⟨w, ?_⟩
    have : f - g * (r + C c * X ^ k) = X ^ k * (e - g * C c) := by
      linear_combination he
    rw [this, hw]; ring

theorem almostMultiples_le [IsNoetherianRing R] [IsIntegrallyClosed R] {g : R⟦X⟧}
    (hg : ¬ (X : R⟦X⟧) ∣ g) : almostMultiples g ≤ Ideal.span {g} := by
  intro f hf
  rw [Ideal.mem_span_singleton]
  choose r hr using exists_X_pow_dvd_sub_mul_of_mem_almostMultiples hg hf
  have hstable : ∀ j m : ℕ, j ≤ m → coeff j (r (m + 1)) = coeff j (r (j + 1)) := by
    intro j m hjm
    have h1 : X ^ (j + 1) ∣ g * (r (j + 1) - r (m + 1)) := by
      have e1 : g * (r (j + 1) - r (m + 1)) = (f - g * r (m + 1)) - (f - g * r (j + 1)) := by ring
      rw [e1]
      exact dvd_sub ((pow_dvd_pow X (by omega)).trans (hr (m + 1))) (hr (j + 1))
    have h2 := X_prime.pow_dvd_of_dvd_mul_left (j + 1) hg h1
    rw [X_pow_dvd_iff] at h2
    have := h2 j (Nat.lt_succ_self j)
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  refine ⟨mk fun k => coeff k (r (k + 1)), ?_⟩
  rw [← sub_eq_zero]
  ext m
  rw [map_zero]
  have hq : X ^ (m + 1) ∣ r (m + 1) - mk fun k => coeff k (r (k + 1)) := by
    rw [X_pow_dvd_iff]
    intro j hj
    rw [map_sub, coeff_mk, hstable j m (by omega), sub_self]
  have hsum : X ^ (m + 1) ∣ f - g * mk fun k => coeff k (r (k + 1)) := by
    have e1 : f - g * (mk fun k => coeff k (r (k + 1))) =
        (f - g * r (m + 1)) + g * (r (m + 1) - mk fun k => coeff k (r (k + 1))) := by ring
    rw [e1]
    exact dvd_add (hr (m + 1)) (dvd_mul_of_dvd_right hq g)
  rw [X_pow_dvd_iff] at hsum
  exact hsum m (Nat.lt_succ_self m)

theorem dvd_of_pow_dvd_powerSeries [IsNoetherianRing R] [IsIntegrallyClosed R] {f g h : R⟦X⟧}
    (hg : g ≠ 0) (hh : h ≠ 0) (H : ∀ n : ℕ, g ^ n ∣ h * f ^ n) : g ∣ f := by
  obtain ⟨a, g₁, hg₁, rfl⟩ := exists_eq_X_pow_mul hg
  have hg₁0 : g₁ ≠ 0 := by rintro rfl; exact hg₁ (dvd_zero _)
  have hmem : f ∈ almostMultiples g₁ := ⟨h, hh, fun n =>
    (pow_dvd_pow_of_dvd (dvd_mul_left g₁ (X ^ a)) n).trans (H n)⟩
  obtain ⟨f', rfl⟩ := Ideal.mem_span_singleton.1 (almostMultiples_le hg₁ hmem)
  rcases eq_or_ne f' 0 with rfl | hf'
  · simp
  obtain ⟨e, f₁, hf₁, rfl⟩ := exists_eq_X_pow_mul hf'
  obtain ⟨b, h₁, hh₁, rfl⟩ := exists_eq_X_pow_mul hh
  have h1 : g₁ ^ (b + 1) * X ^ (a * (b + 1)) ∣
      g₁ ^ (b + 1) * (X ^ (b + e * (b + 1)) * (h₁ * f₁ ^ (b + 1))) := by
    have e1 : (X ^ a * g₁) ^ (b + 1) = g₁ ^ (b + 1) * X ^ (a * (b + 1)) := by ring
    have e2 : X ^ b * h₁ * (g₁ * (X ^ e * f₁)) ^ (b + 1) =
        g₁ ^ (b + 1) * (X ^ (b + e * (b + 1)) * (h₁ * f₁ ^ (b + 1))) := by ring
    rw [← e1, ← e2]; exact H (b + 1)
  have h2 := (mul_dvd_mul_iff_left (pow_ne_zero (b + 1) hg₁0)).1 h1
  have hw : ¬ (X : R⟦X⟧) ∣ h₁ * f₁ ^ (b + 1) := fun hX =>
    (X_prime.dvd_or_dvd hX).elim hh₁ fun h' => hf₁ (X_prime.dvd_of_dvd_pow h')
  have hae : a ≤ e := by
    by_contra hlt
    push Not at hlt
    have h3 : (X : R⟦X⟧) ^ (b + e * (b + 1) + 1) ∣ X ^ (b + e * (b + 1)) * (h₁ * f₁ ^ (b + 1)) :=
      (pow_dvd_pow X (by nlinarith)).trans h2
    rw [pow_succ] at h3
    exact hw ((mul_dvd_mul_iff_left (pow_ne_zero _ (X_ne_zero (R := R)))).1 h3)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hae
  exact ⟨X ^ d * f₁, by ring⟩

theorem isIntegrallyClosed_powerSeries : ∀ (R : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R], IsIntegrallyClosed (PowerSeries R) := by
  intro R _ _ _ _
  let K := FractionRing R⟦X⟧
  rw [isIntegrallyClosed_iff K]
  intro x hx
  obtain ⟨⟨f, ⟨g, hg⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R⟦X⟧) x
  have hg0 : g ≠ 0 := nonZeroDivisors.ne_zero hg
  set x := IsLocalization.mk' K f (⟨g, hg⟩ : nonZeroDivisors R⟦X⟧) with hxdef
  have hgx : algebraMap R⟦X⟧ K g * x = algebraMap R⟦X⟧ K f := by
    rw [mul_comm, hxdef]; exact IsLocalization.mk'_spec K f ⟨g, hg⟩
  obtain ⟨p, hp, hpx⟩ := hx
  have hpx' : Polynomial.aeval x p = 0 := by rw [Polynomial.aeval_def]; exact hpx
  have key : ∀ n : ℕ, g ^ n ∣ g ^ p.natDegree * f ^ n := by
    intro n
    set q := (Polynomial.X ^ n : Polynomial R⟦X⟧) %ₘ p
    have hq : Polynomial.aeval x q = x ^ n := by
      rw [Polynomial.aeval_modByMonic_eq_self_of_root hpx']; simp
    have hqd : q.natDegree ≤ p.natDegree := Polynomial.natDegree_modByMonic_le _ hp
    have hterm : ∀ i ≤ p.natDegree, algebraMap R⟦X⟧ K g ^ p.natDegree * x ^ i =
        algebraMap R⟦X⟧ K (g ^ (p.natDegree - i) * f ^ i) := by
      intro i hi
      calc algebraMap R⟦X⟧ K g ^ p.natDegree * x ^ i
          = algebraMap R⟦X⟧ K g ^ (p.natDegree - i) * (algebraMap R⟦X⟧ K g * x) ^ i := by
            rw [mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hi]
        _ = algebraMap R⟦X⟧ K (g ^ (p.natDegree - i) * f ^ i) := by
            rw [hgx, map_mul, map_pow, map_pow]
    have hz : algebraMap R⟦X⟧ K g ^ p.natDegree * x ^ n = algebraMap R⟦X⟧ K
        (∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * (g ^ (p.natDegree - i) * f ^ i)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hq, Polynomial.aeval_eq_sum_range, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ p.natDegree := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hqd
      rw [Algebra.smul_def, mul_left_comm, hterm i hi']
      simp only [map_mul]
    refine ⟨∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * (g ^ (p.natDegree - i) * f ^ i),
      IsFractionRing.injective R⟦X⟧ K ?_⟩
    rw [map_mul, map_mul, ← hz, map_pow, map_pow, ← hgx, map_pow]
    ring
  obtain ⟨y, hy⟩ := dvd_of_pow_dvd_powerSeries hg0 (pow_ne_zero _ hg0) key
  refine ⟨y, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq, hy, map_mul, mul_comm]

end GlobalTheory.PowerSeriesNormal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNatMulMem
namespace GlobalTheory.NatMulMemUnitaryExistence

open NumberField

theorem exists_nat_mul_mem {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ k : ℕ, 0 < k ∧ ∃ a : 𝓞 E, (a : E) = (k : E) * c := by
  obtain ⟨y, hy, hint⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)).exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  have hcast : ((y.natAbs : ℕ) : E) = ((y.natAbs : ℤ) : E) := (Int.cast_natCast _).symm
  have hint' : IsIntegral ℤ ((y.natAbs : E) * c) := by
    rcases Int.natAbs_eq y with h | h
    · rw [hcast, ← h, ← zsmul_eq_mul]; exact hint
    · have h2 : (y.natAbs : ℤ) = -y := by omega
      rw [hcast, h2, Int.cast_neg, neg_mul, ← zsmul_eq_mul]; exact hint.neg
  exact ⟨⟨_, hint'⟩, rfl⟩

theorem main {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ d • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hL]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_pos, by simpa using hy⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hy
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, Nat.mul_pos hd₁ hd₂, ?_⟩
    have e : (d₁ * d₂) • (y + z) = d₂ • (d₁ • y) + d₁ • (d₂ • z) := by
      rw [smul_add, mul_comm, mul_smul, mul_comm, mul_smul]
    rw [e]
    exact L.add_mem (L.smul_of_tower_mem d₂ h₁) (L.smul_of_tower_mem d₁ h₂)
  | smul c y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨k, hk, a, ha⟩ := exists_nat_mul_mem c
    refine ⟨k * d, Nat.mul_pos hk hd, ?_⟩
    have e : (k * d) • (c • y) = a • (d • y) := by
      funext i
      simp only [Pi.smul_apply, nsmul_eq_mul, smul_eq_mul]
      rw [Algebra.smul_def, show algebraMap (𝓞 E) E a = (a : E) from rfl, ha]
      simp only [Pi.mul_apply, Pi.natCast_apply]
      push_cast; ring
    rw [e]
    exact L.smul_mem a h

theorem target : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)),
    Submodule.span E (↑L : Set (Fin n → E)) = ⊤ → ∀ (x : Fin n → E), ∃ (d : ℕ), (0 : ℕ) < d ∧ d • x ∈ L :=
  fun L hL x => main L hL x

end GlobalTheory.NatMulMemUnitaryExistence
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSystemOfParametersInsert
open IsLocalRing

namespace GlobalTheory

theorem exists_systemOfParameters_insert (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S]
    [IsNoetherianRing S] (a : S) (ha0 : a ≠ 0) (ha : a ∈ maximalIdeal S) :
    ∃ (n : ℕ) (x : Fin n → S), (∀ i, x i ∈ maximalIdeal S) ∧
      ringKrullDim S = (n : WithBot ℕ∞) + 1 ∧
      ∃ N : ℕ, maximalIdeal S ^ N ≤ Ideal.span (insert a (Set.range x)) := by
  classical
  have hIle : Ideal.span {a} ≤ maximalIdeal S := (Ideal.span_singleton_le_iff_mem _).mpr ha
  have hIne : Ideal.span {a} ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ hIle))
  have : Nontrivial (S ⧸ Ideal.span {a}) := Ideal.Quotient.nontrivial_iff.mpr hIne
  have : IsLocalRing (S ⧸ Ideal.span {a}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hdim : ringKrullDim (S ⧸ Ideal.span {a}) + 1 = ringKrullDim S :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero ha0) ha
  obtain ⟨s, hsmin, hcard⟩ :=
    Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal (S ⧸ Ideal.span {a}))
  have hht := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := S ⧸ Ideal.span {a})
  have hsle : Ideal.span (s : Set (S ⧸ Ideal.span {a})) ≤ maximalIdeal (S ⧸ Ideal.span {a}) :=
    hsmin.1.2
  have hcomap : (maximalIdeal (S ⧸ Ideal.span {a})).comap (Ideal.Quotient.mk (Ideal.span {a})) =
      maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  have hmapeq : Ideal.map (Ideal.Quotient.mk (Ideal.span {a})) (maximalIdeal S) =
      maximalIdeal (S ⧸ Ideal.span {a}) := by
    rw [← hcomap, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  let e := s.equivFin
  let x : Fin s.card → S := fun i =>
    (Ideal.Quotient.mk_surjective ((e.symm i : S ⧸ Ideal.span {a}))).choose
  have hx : ∀ i, Ideal.Quotient.mk (Ideal.span {a}) (x i) = e.symm i := fun i =>
    (Ideal.Quotient.mk_surjective _).choose_spec
  have hrange : Ideal.Quotient.mk (Ideal.span {a}) '' Set.range x =
      (s : Set (S ⧸ Ideal.span {a})) := by
    rw [← Set.range_comp]
    ext q
    constructor
    · rintro ⟨i, rfl⟩
      simp only [Function.comp_apply, hx]
      exact (e.symm i).2
    · intro hq
      exact ⟨e ⟨q, hq⟩, by simp [hx]⟩
  refine ⟨s.card, x, fun i => ?_, ?_, ?_⟩
  · rw [← hcomap, Ideal.mem_comap, hx]
    exact hsle (Ideal.subset_span (e.symm i).2)
  · rw [← hdim, ← hht, ← hcard]
    norm_cast
  · have hrad : maximalIdeal (S ⧸ Ideal.span {a}) ≤
        (Ideal.span (s : Set (S ⧸ Ideal.span {a}))).radical := by
      rw [Ideal.radical_eq_sInf]
      refine le_sInf ?_
      rintro p ⟨hsp, hp⟩
      exact hsmin.2 ⟨hp, hsp⟩ (IsLocalRing.le_maximalIdeal hp.ne_top)
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
    refine ⟨N, fun y hy => ?_⟩
    have h1 := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span {a})) hy
    rw [Ideal.map_pow, hmapeq] at h1
    have h2 := hN h1
    rw [← hrange, ← Ideal.map_span] at h2
    obtain ⟨z, hz, hzy⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h2
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp hzy)
    exact Ideal.mem_span_insert.mpr ⟨-c, z, hz, by linear_combination hc⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SmoothOfIsDedekindDomain
namespace GlobalTheory.DedekindSmooth

open Polynomial IsLocalRing

theorem isSmoothAt_bot (k : Type) [Field k] [PerfectField k] (B : Type) [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] : Algebra.IsSmoothAt k (⊥ : Ideal B) := by
  have h : IsField (Localization.AtPrime (⊥ : Ideal B)) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal]
    simp
  letI := h.toField
  have : Algebra.EssFiniteType B (Localization.AtPrime (⊥ : Ideal B)) :=
    .of_isLocalization _ (⊥ : Ideal B).primeCompl
  have : Algebra.EssFiniteType k (Localization.AtPrime (⊥ : Ideal B)) := .comp _ B _
  exact Algebra.FormallySmooth.of_perfectField

theorem exists_uniformiser (B : Type) [CommRing B] [IsDedekindDomain B] (q : Ideal B) [q.IsPrime]
    (hq : q ≠ ⊥) : ∃ t ∈ q, t ≠ 0 ∧ maximalIdeal (Localization.AtPrime q) =
      Ideal.span {algebraMap B (Localization.AtPrime q) t} := by
  have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hq
    (Localization.AtPrime q)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime q)
  obtain ⟨⟨t, s⟩, h⟩ := IsLocalization.surj q.primeCompl π
  have hs : IsUnit (algebraMap B (Localization.AtPrime q) s) := IsLocalization.map_units _ s
  have hm : maximalIdeal (Localization.AtPrime q) =
      Ideal.span {algebraMap B (Localization.AtPrime q) t} := by
    simp only at h
    rw [← h, Ideal.span_singleton_mul_right_unit hs, hπ.maximalIdeal_eq]
  refine ⟨t, ?_, ?_, hm⟩
  · rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q, hm]
    exact Ideal.mem_span_singleton_self _
  · rintro rfl
    simp only [map_zero] at h
    exact mul_ne_zero hπ.ne_zero hs.ne_zero h

theorem isSmoothAt_of_ne_bot (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B]
    [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : Ideal B) [hqp : q.IsPrime]
    (hq : q ≠ ⊥) : Algebra.IsSmoothAt k q := by
  obtain ⟨t, htq, ht0, hm⟩ := exists_uniformiser B q hq
  have hqm : q.IsMaximal := hqp.isMaximal hq
  have htr : Transcendental k t := by
    intro ha
    have hi := ha.isIntegral
    have hu : IsUnit t := hi.isUnit ht0
    exact hqp.ne_top (Ideal.eq_top_of_isUnit_mem _ htq hu)
  letI : Algebra k[X] B := (aeval t : k[X] →ₐ[k] B).toRingHom.toAlgebra
  have : IsScalarTower k k[X] B := .of_algebraMap_eq fun c => by
    change _ = aeval t (algebraMap k k[X] c)
    simp
  have hinj : Function.Injective (algebraMap k[X] B) := transcendental_iff_injective.mp htr
  have : FaithfulSMul k[X] B := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : Module.Flat k[X] B := inferInstance
  have : Algebra.FiniteType k[X] B := .of_restrictScalars_finiteType k _ _
  have : Algebra.FinitePresentation k[X] B :=
    (Algebra.FinitePresentation.of_finiteType (R := k[X]) (A := B)).mp ‹_›
  let p : Ideal k[X] := q.under k[X]
  letI := Localization.AtPrime.algebraOfLiesOver p q
  have hsep : Algebra.IsSeparable p.ResidueField q.ResidueField := by
    have : Module.Finite k (B ⧸ q) := by
      letI := Ideal.Quotient.field q
      exact finite_of_finite_type_of_isJacobsonRing k (B ⧸ q)
    have : Module.Finite k q.ResidueField :=
      Module.Finite.of_surjective (IsScalarTower.toAlgHom k (B ⧸ q) q.ResidueField).toLinearMap
        (Ideal.bijective_algebraMap_quotient_residueField q).2
    have : IsScalarTower k p.ResidueField q.ResidueField := .of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply k k[X] p.ResidueField,
        ← IsScalarTower.algebraMap_apply k[X] p.ResidueField q.ResidueField,
        ← IsScalarTower.algebraMap_apply]
    exact Algebra.isSeparable_tower_top_of_isSeparable k _ _
  have hmap : p.map (algebraMap k[X] (Localization.AtPrime q)) = maximalIdeal _ := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply k[X] B (Localization.AtPrime q),
        IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q]
      exact hx
    · have hX : algebraMap k[X] B X = t := aeval_X t
      rw [hm, Ideal.span_singleton_le_iff_mem, ← hX, ← IsScalarTower.algebraMap_apply]
      apply Ideal.mem_map_of_mem
      change algebraMap k[X] B X ∈ q
      rwa [hX]
  have : Algebra.IsUnramifiedAt k[X] q :=
    (Algebra.isUnramifiedAt_iff_map_eq k[X] p q).mpr ⟨hsep, hmap⟩
  have : Algebra.IsEtaleAt k[X] q := .of_isUnramifiedAt_of_flat q
  exact Algebra.FormallySmooth.comp k k[X] _

theorem smooth_of_isDedekindDomain :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [IsDedekindDomain B]
      [Algebra k B] [Algebra.FiniteType k B], Algebra.Smooth k B := by
  intro k _ _ B _ _ _ _
  have : Algebra.FinitePresentation k B :=
    (Algebra.FinitePresentation.of_finiteType (R := k) (A := B)).mp ‹_›
  refine ⟨Algebra.smoothLocus_eq_univ_iff.mp (Set.eq_univ_iff_forall.mpr fun q => ?_), ‹_›⟩
  obtain ⟨q, hq⟩ := q
  by_cases h : q = ⊥
  · subst h
    exact isSmoothAt_bot k B
  · exact isSmoothAt_of_ne_bot k B q h

end GlobalTheory.DedekindSmooth
end
