module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetAverageProdFundamentalDomainPlaneLatticePow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAbsoluteValueCompleteSpaceOfDvr

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowerSeriesCompletionEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowerSeriesCompletionEmbedding
open Polynomial

namespace GlobalTheory.CurveCompletion

theorem residue_exists (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (Q : Ideal A) (hQ : Q.IsMaximal) (c : A) :
    ∃ a : k, c - algebraMap k A a ∈ Q := by
  letI := Ideal.Quotient.field Q
  haveI : Module.Finite k (A ⧸ Q) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ Q)
  obtain ⟨a, ha⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := A ⧸ Q)).2
    (Ideal.Quotient.mk Q c)
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← ha]
  simp [Ideal.Quotient.algebraMap_eq]

section Dedekind
variable {A : Type} [CommRing A] [IsDedekindDomain A]

theorem pow_le_span_sup {Q : Ideal A} [Q.IsPrime] (hQ : Q ≠ ⊥) {π : A} (hπ : π ∈ Q)
    (hπ2 : π ∉ Q ^ 2) : ∀ m : ℕ, Q ^ m ≤ Ideal.span {π ^ m} ⊔ Q ^ (m + 1) := by
  first
  | exact @_root_.GlobalTheory.SpanPowerSupremum.pow_le_span_pow_sup
  | exact _root_.GlobalTheory.SpanPowerSupremum.pow_le_span_pow_sup
  | (apply _root_.GlobalTheory.SpanPowerSupremum.pow_le_span_pow_sup <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpanPowerSupremum.pow_le_span_pow_sup <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpanPowerSupremum.pow_le_span_pow_sup <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpanPowerSupremum.pow_le_span_pow_sup ..)

theorem pow_not_mem {Q : Ideal A} [Q.IsPrime] (hQ : Q ≠ ⊥) {π : A} (hπ : π ∈ Q)
    (hπ2 : π ∉ Q ^ 2) (m : ℕ) : π ^ m ∉ Q ^ (m + 1) := by
  first
  | exact @_root_.GlobalTheory.AlgebraicIntegerNormBound.main
  | exact _root_.GlobalTheory.AlgebraicIntegerNormBound.main
  | (apply _root_.GlobalTheory.AlgebraicIntegerNormBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AlgebraicIntegerNormBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AlgebraicIntegerNormBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AlgebraicIntegerNormBound.main ..)

end Dedekind

section Series
variable {k A : Type} [Field k] [CommRing A] [Algebra k A] (Q : Ideal A) (π : A)

theorem aeval_mem_of_dvd (hπ : π ∈ Q) (m : ℕ) (r : k[X]) (h : X ^ m ∣ r) :
    aeval π r ∈ Q ^ m := by
  obtain ⟨s, rfl⟩ := h
  rw [map_mul, map_pow, aeval_X]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hπ m)

theorem dvd_of_aeval_mem (hπ : π ∈ Q) (hnot : ∀ m : ℕ, π ^ m ∉ Q ^ (m + 1)) :
    ∀ (m : ℕ) (r : k[X]), aeval π r ∈ Q ^ m → X ^ m ∣ r := by
  intro m
  induction m with
  | zero => intro r _; simp
  | succ m ih =>
    intro r hr
    obtain ⟨s, rfl⟩ := ih r (Ideal.pow_le_pow_right (Nat.le_succ m) hr)
    obtain ⟨s', hs'⟩ := Polynomial.X_dvd_sub_C (p := s)
    have hs : s = C (s.coeff 0) + X * s' := by rw [← hs']; ring
    by_cases h0 : s.coeff 0 = 0
    · rw [hs, h0, map_zero, zero_add, ← mul_assoc, ← pow_succ]
      exact dvd_mul_right _ _
    · exfalso
      apply hnot m
      have e0 : aeval π s = algebraMap k A (s.coeff 0) + π * aeval π s' := by
        conv_lhs => rw [hs]
        simp [aeval_C]
      have e : aeval π (X ^ m * s) =
          π ^ m * algebraMap k A (s.coeff 0) + π ^ (m + 1) * aeval π s' := by
        rw [map_mul, map_pow, aeval_X, e0]; ring
      rw [e] at hr
      have h2 : π ^ m * algebraMap k A (s.coeff 0) ∈ Q ^ (m + 1) := by
        have h3 : π ^ (m + 1) * aeval π s' ∈ Q ^ (m + 1) :=
          Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hπ _)
        have := Ideal.sub_mem _ hr h3
        simpa using this
      have h4 := Ideal.mul_mem_right (algebraMap k A (s.coeff 0)⁻¹) _ h2
      rwa [mul_assoc, ← map_mul, mul_inv_cancel₀ h0, map_one, mul_one] at h4

theorem aeval_mem_iff (hπ : π ∈ Q) (hnot : ∀ m : ℕ, π ^ m ∉ Q ^ (m + 1)) (m : ℕ) (r : k[X]) :
    aeval π r ∈ Q ^ m ↔ X ^ m ∣ r :=
  ⟨dvd_of_aeval_mem Q π hπ hnot m r, aeval_mem_of_dvd Q π hπ m r⟩

theorem coe_dvd_iff (m : ℕ) (r : k[X]) :
    (PowerSeries.X : PowerSeries k) ^ m ∣ (r : PowerSeries k) ↔ X ^ m ∣ r := by
  rw [PowerSeries.X_pow_dvd_iff, Polynomial.X_pow_dvd_iff]
  simp [Polynomial.coeff_coe]

theorem eq_of_forall_dvd (f g : PowerSeries k)
    (h : ∀ m : ℕ, (PowerSeries.X : PowerSeries k) ^ m ∣ f - g) : f = g := by
  ext n
  have := PowerSeries.X_pow_dvd_iff.mp (h (n + 1)) n (Nat.lt_succ_self n)
  rw [map_sub, sub_eq_zero] at this
  exact this

end Series

section Construction
variable {k A : Type} [Field k] [CommRing A] [Algebra k A] (Q : Ideal A) (π : A)
  (hex : ∀ (m : ℕ) (u : A), ∃ p : k[X], u - aeval π p ∈ Q ^ m)

noncomputable def approx (m : ℕ) (u : A) : k[X] := Classical.choose (hex m u)

theorem approx_spec (m : ℕ) (u : A) : u - aeval π (approx Q π hex m u) ∈ Q ^ m :=
  Classical.choose_spec (hex m u)

noncomputable def ser (u : A) : PowerSeries k :=
  PowerSeries.mk fun n => (approx Q π hex (n + 1) u).coeff n

variable {Q π} (hπ : π ∈ Q) (hnot : ∀ m : ℕ, π ^ m ∉ Q ^ (m + 1))
include hπ hnot

theorem ser_sub_approx (m : ℕ) (u : A) :
    (PowerSeries.X : PowerSeries k) ^ m ∣ ser Q π hex u - (approx Q π hex m u : PowerSeries k) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro n hn
  rw [map_sub, Polynomial.coeff_coe, ser, PowerSeries.coeff_mk, sub_eq_zero]
  have hmem : aeval π (approx Q π hex m u - approx Q π hex (n + 1) u) ∈ Q ^ (n + 1) := by
    have e : aeval π (approx Q π hex m u - approx Q π hex (n + 1) u) =
        (u - aeval π (approx Q π hex (n + 1) u)) - (u - aeval π (approx Q π hex m u)) := by
      rw [map_sub]; ring
    rw [e]
    exact Ideal.sub_mem _ (approx_spec Q π hex _ u)
      (Ideal.pow_le_pow_right hn (approx_spec Q π hex m u))
  have hd := (Polynomial.X_pow_dvd_iff).mp (dvd_of_aeval_mem Q π hπ hnot _ _ hmem) n
    (Nat.lt_succ_self n)
  rw [Polynomial.coeff_sub, sub_eq_zero] at hd
  exact hd.symm

theorem mem_iff_dvd (m : ℕ) (u : A) (p : k[X]) :
    u - aeval π p ∈ Q ^ m ↔
      (PowerSeries.X : PowerSeries k) ^ m ∣ ser Q π hex u - (p : PowerSeries k) := by
  set q := approx Q π hex m u
  have e1 : u - aeval π p = (u - aeval π q) + aeval π (q - p) := by rw [map_sub]; ring
  have e2 : ser Q π hex u - (p : PowerSeries k) =
      (ser Q π hex u - (q : PowerSeries k)) + ((q - p : k[X]) : PowerSeries k) := by
    rw [Polynomial.coe_sub]; ring
  rw [e1, Ideal.add_mem_iff_right _ (approx_spec Q π hex m u), e2,
    (dvd_add_right (ser_sub_approx hex hπ hnot m u)), coe_dvd_iff,
    aeval_mem_iff Q π hπ hnot]

theorem ser_eq (u : A) (f : PowerSeries k)
    (h : ∀ m : ℕ, ∃ p : k[X], u - aeval π p ∈ Q ^ m ∧
      (PowerSeries.X : PowerSeries k) ^ m ∣ f - (p : PowerSeries k)) :
    ser Q π hex u = f := by
  apply eq_of_forall_dvd
  intro m
  obtain ⟨p, hp, hd⟩ := h m
  have := dvd_sub ((mem_iff_dvd hex hπ hnot m u p).mp hp) hd
  rwa [sub_sub_sub_cancel_right] at this

noncomputable def serHom : A →ₐ[k] PowerSeries k where
  toFun := ser Q π hex
  map_one' := ser_eq hex hπ hnot 1 1 fun m => ⟨1, by simp, by simp⟩
  map_zero' := ser_eq hex hπ hnot 0 0 fun m => ⟨0, by simp, by simp⟩
  map_add' u v := by
    apply ser_eq hex hπ hnot
    intro m
    refine ⟨approx Q π hex m u + approx Q π hex m v, ?_, ?_⟩
    · have e : u + v - aeval π (approx Q π hex m u + approx Q π hex m v) =
          (u - aeval π (approx Q π hex m u)) + (v - aeval π (approx Q π hex m v)) := by
        rw [map_add (f := _)]; ring
      rw [e]
      exact Ideal.add_mem _ (approx_spec Q π hex m u) (approx_spec Q π hex m v)
    · have e : ser Q π hex u + ser Q π hex v -
          ((approx Q π hex m u + approx Q π hex m v : k[X]) : PowerSeries k) =
          (ser Q π hex u - (approx Q π hex m u : PowerSeries k)) +
            (ser Q π hex v - (approx Q π hex m v : PowerSeries k)) := by
        rw [Polynomial.coe_add]; ring
      rw [e]
      exact dvd_add (ser_sub_approx hex hπ hnot m u) (ser_sub_approx hex hπ hnot m v)
  map_mul' u v := by
    apply ser_eq hex hπ hnot
    intro m
    refine ⟨approx Q π hex m u * approx Q π hex m v, ?_, ?_⟩
    · have e : u * v - aeval π (approx Q π hex m u * approx Q π hex m v) =
          (u - aeval π (approx Q π hex m u)) * v +
            aeval π (approx Q π hex m u) * (v - aeval π (approx Q π hex m v)) := by
        rw [map_mul]; ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (approx_spec Q π hex m u))
        (Ideal.mul_mem_left _ _ (approx_spec Q π hex m v))
    · have e : ser Q π hex u * ser Q π hex v -
          ((approx Q π hex m u * approx Q π hex m v : k[X]) : PowerSeries k) =
          (ser Q π hex u - (approx Q π hex m u : PowerSeries k)) * ser Q π hex v +
            (approx Q π hex m u : PowerSeries k) *
              (ser Q π hex v - (approx Q π hex m v : PowerSeries k)) := by
        rw [Polynomial.coe_mul]; ring
      rw [e]
      exact dvd_add (Dvd.dvd.mul_right (ser_sub_approx hex hπ hnot m u) _)
        (Dvd.dvd.mul_left (ser_sub_approx hex hπ hnot m v) _)
  commutes' c := by
    apply ser_eq hex hπ hnot
    intro m
    exact ⟨C c, by simp, by simp⟩

end Construction

section Existence
variable {k A : Type} [Field k] [CommRing A] [Algebra k A] {Q : Ideal A} {π : A}

theorem exists_approx (hπ : π ∈ Q) (hres : ∀ c : A, ∃ a : k, c - algebraMap k A a ∈ Q)
    (hsup : ∀ m : ℕ, Q ^ m ≤ Ideal.span {π ^ m} ⊔ Q ^ (m + 1)) :
    ∀ (m : ℕ) (u : A), ∃ p : k[X], u - aeval π p ∈ Q ^ m := by
  first
  | exact @_root_.GlobalTheory.IntegralNormBound.target
  | exact _root_.GlobalTheory.IntegralNormBound.target
  | (apply _root_.GlobalTheory.IntegralNormBound.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralNormBound.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralNormBound.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralNormBound.target ..)

end Existence

theorem exists_completion_embedding : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k]
    [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (Q : Ideal A),
    Q.IsMaximal → Q ≠ ⊥ → ∃ (σ : A →ₐ[k] PowerSeries k) (π : A), σ π = PowerSeries.X ∧
      Function.Injective σ ∧
      (∀ (m : ℕ) (u : A), u ∈ Q ^ m ↔ (PowerSeries.X : PowerSeries k) ^ m ∣ σ u) ∧
      ∀ (m : ℕ) (φ : PowerSeries k), ∃ u : A,
        (PowerSeries.X : PowerSeries k) ^ m ∣ φ - σ u := by
  intro k A _ _ _ _ _ _ _ Q hQ hQ0
  haveI : Q.IsPrime := hQ.isPrime
  obtain ⟨π, hπ1, hπ2⟩ := SetLike.exists_of_lt (Ideal.pow_succ_lt_pow hQ0 1)
  have hπ : π ∈ Q := by simpa using hπ1
  have hnot := pow_not_mem hQ0 hπ hπ2
  have hex := exists_approx (k := k) hπ (residue_exists k A Q hQ) (pow_le_span_sup hQ0 hπ hπ2)
  have hmem : ∀ (m : ℕ) (u : A),
      u ∈ Q ^ m ↔ (PowerSeries.X : PowerSeries k) ^ m ∣ serHom hex hπ hnot u := by
    intro m u
    have := mem_iff_dvd hex hπ hnot m u 0
    change u ∈ Q ^ m ↔ (PowerSeries.X : PowerSeries k) ^ m ∣ ser Q π hex u
    simpa using this
  refine ⟨serHom hex hπ hnot, π, ?_, ?_, hmem, ?_⟩
  · exact ser_eq hex hπ hnot π PowerSeries.X fun m => ⟨X, by simp, by simp⟩
  · rw [injective_iff_map_eq_zero]
    intro u hu
    have hall : ∀ m : ℕ, u ∈ Q ^ m := fun m => (hmem m u).mpr (by rw [hu]; exact dvd_zero _)
    have hbot := Ideal.iInf_pow_eq_bot_of_isDomain Q hQ.ne_top
    have : u ∈ ⨅ i, Q ^ i := Submodule.mem_iInf _ |>.mpr hall
    rw [hbot] at this
    exact (Submodule.mem_bot A).mp this
  · intro m φ
    refine ⟨aeval π (PowerSeries.trunc m φ), ?_⟩
    have h1 := (mem_iff_dvd hex hπ hnot m (aeval π (PowerSeries.trunc m φ))
      (PowerSeries.trunc m φ)).mp (by simp)
    have h2 : (PowerSeries.X : PowerSeries k) ^ m ∣ φ - (PowerSeries.trunc m φ : PowerSeries k) := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro n hn
      rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hn, sub_self]
    have := dvd_sub h2 h1
    rwa [sub_sub_sub_cancel_right] at this

end GlobalTheory.CurveCompletion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowerSeriesCompletionEmbeddingStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_power_series_completion_embedding : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (Q : Ideal A), Q.IsMaximal → Q ≠ ⊥ → ∃ (σ : A →ₐ[k] PowerSeries k) (π : A), σ π = PowerSeries.X ∧ Function.Injective σ ∧ (∀ (m : ℕ) (u : A), u ∈ Q ^ m ↔ (PowerSeries.X : PowerSeries k) ^ m ∣ σ u) ∧ ∀ (m : ℕ) (φ : PowerSeries k), ∃ u : A, (PowerSeries.X : PowerSeries k) ^ m ∣ φ - σ u := by
  first | exact @GlobalTheory.CurveCompletion.exists_completion_embedding | exact GlobalTheory.CurveCompletion.exists_completion_embedding | (intros; apply GlobalTheory.CurveCompletion.exists_completion_embedding <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeformMultipleZerosLinearFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeformMultipleZerosLinearFamily
open Polynomial

set_option linter.deprecated false

namespace GlobalTheory.DeformZeros

variable {k J I : Type} [Field k] [Fintype J] [Fintype I]

noncomputable def sys (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k)
    (x : J ⊕ I → PowerSeries k) : Option (I × Fin N) → PowerSeries k
  | none => ∑ j, x (Sum.inl j) * ξ j
  | some (i, l) => ∑ j, x (Sum.inl j) *
      (((PowerSeries.derivativeFun)^[l.1] (s i j)).subst (x (Sum.inr i)) : PowerSeries k)

noncomputable def linFun (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k) (y₀ : J → k)
    (v : J ⊕ I → k) : Option (I × Fin N) → k
  | none => ∑ j, v (Sum.inl j) * PowerSeries.constantCoeff (ξ j)
  | some (i, l) => ∑ j, v (Sum.inl j) *
        PowerSeries.constantCoeff ((PowerSeries.derivativeFun)^[l.1] (s i j))
      + v (Sum.inr i) * ∑ j, y₀ j * PowerSeries.coeff 1 ((PowerSeries.derivativeFun)^[l.1] (s i j))

noncomputable def lin (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k) (y₀ : J → k) :
    (J ⊕ I → k) →ₗ[k] (Option (I × Fin N) → k) where
  toFun := linFun N ξ s y₀
  map_add' v w := by
    funext e; rcases e with _ | ⟨i, l⟩ <;> simp [linFun, add_mul, Finset.sum_add_distrib] <;> ring
  map_smul' c v := by
    funext e; rcases e with _ | ⟨i, l⟩ <;> simp [linFun, Finset.mul_sum, mul_assoc, mul_add]

lemma iter_eq (f : PowerSeries k) (l : ℕ) :
    (PowerSeries.derivativeFun)^[l] f = (PowerSeries.derivative (R := k))^[l] f := by
  induction l generalizing f with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]; rfl

lemma cc_subst (φ a : PowerSeries k) (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.constantCoeff (φ.subst a : PowerSeries k) = PowerSeries.constantCoeff φ :=
  (GlobalTheory.T.powerSeries_taylor_subst_first_order k φ a 0 1 le_rfl ha).1

end GlobalTheory.DeformZeros

namespace GlobalTheory.DeformZeros

variable {k : Type} [Field k]

lemma dvd_step {m : ℕ} (hm : 1 ≤ m) (y g S S' : PowerSeries k) (y0 c A : k)
    (hy : PowerSeries.constantCoeff y = y0) (hS : PowerSeries.constantCoeff S = A)
    (hT : (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣
      S' - S - PowerSeries.X ^ m * PowerSeries.C c) :
    (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣
      (y + PowerSeries.X ^ m * g) * S' - y * S
        - PowerSeries.X ^ m * PowerSeries.C (PowerSeries.constantCoeff g * A + y0 * c) := by
  obtain ⟨r, hr⟩ := hT
  have hS' : S' = S + PowerSeries.X ^ m * PowerSeries.C c + PowerSeries.X ^ (m + 1) * r := by
    linear_combination hr
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have heq : (y + PowerSeries.X ^ (n + 1) * g) * S' - y * S
      - PowerSeries.X ^ (n + 1) * PowerSeries.C (PowerSeries.constantCoeff g * A + y0 * c)
      = PowerSeries.X ^ (n + 1) * (y * PowerSeries.C c - PowerSeries.C (y0 * c)
          + (g * S - PowerSeries.C (PowerSeries.constantCoeff g * A)))
        + PowerSeries.X ^ (n + 1 + 1) * (y * r + PowerSeries.X ^ n *
          (g * PowerSeries.C c + PowerSeries.X * g * r)) := by
    rw [hS', map_add (f := _)]; ring
  rw [heq]
  refine dvd_add ?_ (dvd_mul_right _ _)
  rw [pow_succ]
  refine mul_dvd_mul_left _ ?_
  rw [PowerSeries.X_dvd_iff]
  simp [hy, hS]

end GlobalTheory.DeformZeros

namespace GlobalTheory.DeformZeros

theorem deform : ∀ (k J I : Type) [Field k] [CharZero k] [Fintype J] [Fintype I] (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k) (y₀ : J → k), 1 ≤ N →
 ∑ j, y₀ j * PowerSeries.constantCoeff (ξ j) = 0 →
 (∀ i, ∀ l < N, ∑ j, y₀ j * PowerSeries.coeff l (s i j) = 0) → (∀ i, ∑ j, y₀ j * PowerSeries.coeff N (s i j) ≠ 0) →
 (∀ (e₀ : k) (e : I → ℕ → k), ∃ h : J → k, ∑ j, h j * PowerSeries.constantCoeff (ξ j) = e₀ ∧ ∀ i, ∀ l, l + 1 < N → ∑ j, h j * PowerSeries.coeff l (s i j) = e i l) →
 ∃ (y : J → PowerSeries k) (a : I → PowerSeries k), (∀ j, PowerSeries.constantCoeff (y j) = y₀ j) ∧ (∀ i, PowerSeries.constantCoeff (a i) = 0) ∧
   ∑ j, y j * ξ j = 0 ∧ ∀ i, ∀ l < N, ∑ j, y j * (((PowerSeries.derivativeFun)^[l] (s i j)).subst (a i) : PowerSeries k) = 0 := by
  intro k J I _ _ _ _ N ξ s y₀ hN h0 hlow hN' hsurj

  have hA : ∀ (f : PowerSeries k) (l : ℕ), PowerSeries.constantCoeff ((PowerSeries.derivativeFun)^[l] f)
      = (l.factorial : k) * PowerSeries.coeff l f := by
    intro f l; rw [iter_eq]; exact PowerSeries.constantCoeff_iterate_derivative f l
  have hB : ∀ (f : PowerSeries k) (l : ℕ), PowerSeries.coeff 1 ((PowerSeries.derivativeFun)^[l] f)
      = ((2 : ℕ).ascFactorial l : k) * PowerSeries.coeff (1 + l) f := by
    intro f l; rw [iter_eq]; exact PowerSeries.coeff_iterate_derivative f l 1
  have hsur : Function.Surjective (lin N ξ s y₀) := by

    intro w
    have hfac : ∀ l : ℕ, (l.factorial : k) ≠ 0 := fun l => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero l)
    obtain ⟨hv, hv0, hvl⟩ := hsurj (w none)
      (fun i l => if hl : l < N then w (some (i, ⟨l, hl⟩)) / (l.factorial : k) else 0)
    have hN1 : N - 1 < N := by omega
    have hS : ∀ i, ∑ j, y₀ j * PowerSeries.coeff 1 ((PowerSeries.derivativeFun)^[N - 1] (s i j)) ≠ 0 := by
      intro i
      simp only [hB]
      have e1 : 1 + (N - 1) = N := by omega
      rw [e1]
      have hasc : ((Nat.ascFactorial 2 (N - 1) : ℕ) : k) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.ascFactorial_pos 1 (N - 1)).ne'
      calc ∑ j, y₀ j * (((Nat.ascFactorial 2 (N - 1) : ℕ) : k) * PowerSeries.coeff N (s i j))
          = ((Nat.ascFactorial 2 (N - 1) : ℕ) : k) * ∑ j, y₀ j * PowerSeries.coeff N (s i j) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ ≠ 0 := mul_ne_zero hasc (hN' i)
    refine ⟨Sum.elim hv (fun i => (w (some (i, ⟨N - 1, hN1⟩)) - ∑ j, hv j *
        PowerSeries.constantCoeff ((PowerSeries.derivativeFun)^[N - 1] (s i j))) /
        ∑ j, y₀ j * PowerSeries.coeff 1 ((PowerSeries.derivativeFun)^[N - 1] (s i j))), ?_⟩
    funext e
    rcases e with _ | ⟨i, l⟩
    · simpa [lin, linFun] using hv0
    · simp only [lin, linFun, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr]
      rcases Nat.lt_or_ge (l.1 + 1) N with hl | hl
      · have h1 : ∑ j, hv j * PowerSeries.constantCoeff ((PowerSeries.derivativeFun)^[l.1] (s i j))
            = w (some (i, l)) := by
          simp only [hA]
          have := hvl i l.1 hl
          rw [dite_eq_left l.2] at this
          calc ∑ j, hv j * ((l.1.factorial : k) * PowerSeries.coeff l.1 (s i j))
              = (l.1.factorial : k) * ∑ j, hv j * PowerSeries.coeff l.1 (s i j) := by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
            _ = w (some (i, l)) := by rw [this, mul_div_assoc', mul_div_cancel_left₀ _ (hfac _)]
        have h2 : ∑ j, y₀ j * PowerSeries.coeff 1 ((PowerSeries.derivativeFun)^[l.1] (s i j)) = 0 := by
          simp only [hB]
          calc ∑ j, y₀ j * (((Nat.ascFactorial 2 l.1 : ℕ) : k) * PowerSeries.coeff (1 + l.1) (s i j))
              = ((Nat.ascFactorial 2 l.1 : ℕ) : k) * ∑ j, y₀ j * PowerSeries.coeff (1 + l.1) (s i j) := by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
            _ = 0 := by rw [hlow i (1 + l.1) (by omega), mul_zero]
        rw [h1, h2, mul_zero, add_zero]
      · have hl' : l = ⟨N - 1, hN1⟩ := Fin.ext (by simp; omega)
        subst hl'
        rw [div_mul_cancel₀ _ (hS i)]
        ring
  have hbase : ∀ e, PowerSeries.constantCoeff
      (sys N ξ s (fun i => PowerSeries.C (Sum.elim y₀ 0 i)) e) = 0 := by

    intro e
    rcases e with _ | ⟨i, l⟩
    set_option synthInstance.maxHeartbeats 100000 in
      · simp [sys, map_sum, h0]
    · set_option synthInstance.maxHeartbeats 100000 in
        simp only [sys, map_sum, map_mul, PowerSeries.constantCoeff_C, Sum.elim_inl, Sum.elim_inr]
      have h' : ∀ j, PowerSeries.constantCoeff (((PowerSeries.derivativeFun)^[l.1] (s i j)).subst
          (PowerSeries.C ((0 : I → k) i)) : PowerSeries k) = (l.1.factorial : k) * PowerSeries.coeff l.1 (s i j) := by
        intro j; rw [cc_subst _ _ (by simp), hA]
      simp only [h']
      calc ∑ j, y₀ j * ((l.1.factorial : k) * PowerSeries.coeff l.1 (s i j))
          = (l.1.factorial : k) * ∑ j, y₀ j * PowerSeries.coeff l.1 (s i j) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [hlow i l.1 l.2, mul_zero]
  have htay : ∀ (x h : J ⊕ I → PowerSeries k) (m : ℕ), 1 ≤ m →
      (∀ i, PowerSeries.constantCoeff (x i) = Sum.elim y₀ 0 i) → ∀ e,
      (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ sys N ξ s (fun i => x i + PowerSeries.X ^ m * h i) e
        - sys N ξ s x e - PowerSeries.X ^ m *
          PowerSeries.C (lin N ξ s y₀ (fun i => PowerSeries.constantCoeff (h i)) e) := by

    intro x h m hm hx0 e
    rcases e with _ | ⟨i, l⟩
    · simp only [sys, lin, linFun, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl]
      have heq : ∑ j, (x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) * ξ j - ∑ j, x (Sum.inl j) * ξ j
          - PowerSeries.X ^ m * PowerSeries.C (∑ j, PowerSeries.constantCoeff (h (Sum.inl j)) * PowerSeries.constantCoeff (ξ j))
          = PowerSeries.X ^ m * (∑ j, h (Sum.inl j) * ξ j - PowerSeries.C (∑ j, PowerSeries.constantCoeff (h (Sum.inl j)) * PowerSeries.constantCoeff (ξ j))) := by
        rw [mul_sub, Finset.mul_sum]; simp only [add_mul, Finset.sum_add_distrib, mul_assoc]; ring
      rw [heq, pow_succ]
      refine mul_dvd_mul_left _ ?_
      rw [PowerSeries.X_dvd_iff]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum]
    · simp only [sys, lin, linFun, LinearMap.coe_mk, AddHom.coe_mk]
      set a := x (Sum.inr i)
      set b := h (Sum.inr i)
      have ha : PowerSeries.constantCoeff a = 0 := by simpa using hx0 (Sum.inr i)
      have key : ∀ j, (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣
          (x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) *
            (((PowerSeries.derivativeFun)^[l.1] (s i j)).subst (a + PowerSeries.X ^ m * b) : PowerSeries k)
          - x (Sum.inl j) * (((PowerSeries.derivativeFun)^[l.1] (s i j)).subst a : PowerSeries k)
          - PowerSeries.X ^ m * PowerSeries.C (PowerSeries.constantCoeff (h (Sum.inl j)) *
              PowerSeries.constantCoeff ((PowerSeries.derivativeFun)^[l.1] (s i j))
              + y₀ j * (PowerSeries.constantCoeff b * PowerSeries.coeff 1 ((PowerSeries.derivativeFun)^[l.1] (s i j)))) := by
        intro j
        have T := GlobalTheory.T.powerSeries_taylor_subst_first_order k ((PowerSeries.derivativeFun)^[l.1] (s i j)) a b m hm ha
        exact dvd_step hm _ _ _ _ _ _ _ (by simpa using hx0 (Sum.inl j)) T.1 T.2
      have heq : ∑ j, (x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) *
            (((PowerSeries.derivativeFun)^[l.1] (s i j)).subst (a + PowerSeries.X ^ m * b) : PowerSeries k)
          - ∑ j, x (Sum.inl j) * (((PowerSeries.derivativeFun)^[l.1] (s i j)).subst a : PowerSeries k)
          - PowerSeries.X ^ m * PowerSeries.C (∑ j, PowerSeries.constantCoeff (h (Sum.inl j)) *
              PowerSeries.constantCoeff ((PowerSeries.derivativeFun)^[l.1] (s i j))
              + PowerSeries.constantCoeff b * ∑ j, y₀ j * PowerSeries.coeff 1 ((PowerSeries.derivativeFun)^[l.1] (s i j)))
          = ∑ j, ((x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) *
            (((PowerSeries.derivativeFun)^[l.1] (s i j)).subst (a + PowerSeries.X ^ m * b) : PowerSeries k)
          - x (Sum.inl j) * (((PowerSeries.derivativeFun)^[l.1] (s i j)).subst a : PowerSeries k)
          - PowerSeries.X ^ m * PowerSeries.C (PowerSeries.constantCoeff (h (Sum.inl j)) *
              PowerSeries.constantCoeff ((PowerSeries.derivativeFun)^[l.1] (s i j))
              + y₀ j * (PowerSeries.constantCoeff b * PowerSeries.coeff 1 ((PowerSeries.derivativeFun)^[l.1] (s i j))))) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← map_sum,
          Finset.sum_add_distrib, Finset.mul_sum (a := PowerSeries.constantCoeff b)]
        congr 4
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [heq]
      exact Finset.dvd_sum fun j _ => key j
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.T.newton_powerSeries_surjective_linearization_solution k (J ⊕ I) (Option (I × Fin N)) (sys N ξ s) (Sum.elim y₀ 0)
    (lin N ξ s y₀) hsur hbase htay
  refine ⟨fun j => x (Sum.inl j), fun i => x (Sum.inr i), fun j => by simpa using hx0 (Sum.inl j),
    fun i => by simpa using hx0 (Sum.inr i), hx none, ?_⟩
  intro i l hl
  exact hx (some (i, ⟨l, hl⟩))

end GlobalTheory.DeformZeros
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeformMultipleZerosLinearFamilyStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deform_multiple_zeros_linear_family : ∀ (k J I : Type) [Field k] [CharZero k] [Fintype J] [Fintype I] (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k) (y₀ : J → k), 1 ≤ N →
 ∑ j, y₀ j * PowerSeries.constantCoeff (ξ j) = 0 →
 (∀ i, ∀ l < N, ∑ j, y₀ j * PowerSeries.coeff l (s i j) = 0) → (∀ i, ∑ j, y₀ j * PowerSeries.coeff N (s i j) ≠ 0) →
 (∀ (e₀ : k) (e : I → ℕ → k), ∃ h : J → k, ∑ j, h j * PowerSeries.constantCoeff (ξ j) = e₀ ∧ ∀ i, ∀ l, l + 1 < N → ∑ j, h j * PowerSeries.coeff l (s i j) = e i l) →
 ∃ (y : J → PowerSeries k) (a : I → PowerSeries k), (∀ j, PowerSeries.constantCoeff (y j) = y₀ j) ∧ (∀ i, PowerSeries.constantCoeff (a i) = 0) ∧
   ∑ j, y j * ξ j = 0 ∧ ∀ i, ∀ l < N, ∑ j, y j * (((PowerSeries.derivativeFun)^[l] (s i j)).subst (a i) : PowerSeries k) = 0 := by
  first | exact @GlobalTheory.DeformZeros.deform | exact GlobalTheory.DeformZeros.deform | (intros; apply GlobalTheory.DeformZeros.deform <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IterateDerivativeFunMulSubstLeibniz
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IterateDerivativeFunMulSubstLeibniz
open Polynomial

namespace GlobalTheory

theorem iterate_derivation_mul_antidiagonal {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (D : Derivation R S S) (a b : S) (n : ℕ) :
    (⇑D)^[n] (a * b) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, n.choose ij.1 • ((⇑D)^[ij.1] a * (⇑D)^[ij.2] b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_antidiagonal_choose_succ_nsmul (fun i j => (⇑D)^[i] a * (⇑D)^[j] b) n,
      Function.iterate_succ_apply', ih, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    have hc : n.choose ij.2 = n.choose ij.1 := by
      rw [← hij, Nat.choose_symm_add]
    rw [hc, map_nsmul, Derivation.leibniz, Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    simp only [smul_eq_mul, ← nsmul_add]
    congr 1
    ring

theorem iterate_derivativeFun_mul_subst :
    ∀ (k : Type) [Field k] (a φ ψ : PowerSeries k) (l : ℕ), PowerSeries.constantCoeff a = 0 →
      (((PowerSeries.derivativeFun)^[l] (φ * ψ)).subst a : PowerSeries k) =
        ∑ p ∈ Finset.range (l + 1), l.choose p •
          ((((PowerSeries.derivativeFun)^[p] φ).subst a : PowerSeries k) *
            ((PowerSeries.derivativeFun)^[l - p] ψ).subst a) := by
  intro k _ a φ ψ l ha
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero' ha
  have hit : ∀ (n : ℕ) (f : PowerSeries k),
      (PowerSeries.derivativeFun)^[n] f = (⇑(PowerSeries.derivative (R := k)))^[n] f := by
    intro n f
    induction n generalizing f with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
      rfl
  simp only [hit]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [iterate_derivation_mul_antidiagonal,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => l.choose i • ((⇑(PowerSeries.derivative (R := k)))^[i] φ *
        (⇑(PowerSeries.derivative (R := k)))^[j] ψ)) l,
    ← PowerSeries.coe_substAlgHom hs, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_nsmul, map_mul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IterateDerivativeFunMulSubstLeibnizStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iterate_derivativeFun_mul_subst_leibniz : ∀ (k : Type) [Field k] (a φ ψ : PowerSeries k) (l : ℕ), PowerSeries.constantCoeff a = 0 →
 (((PowerSeries.derivativeFun)^[l] (φ * ψ)).subst a : PowerSeries k) = ∑ p ∈ Finset.range (l + 1), l.choose p • ((((PowerSeries.derivativeFun)^[p] φ).subst a : PowerSeries k) * ((PowerSeries.derivativeFun)^[l - p] ψ).subst a) := by
  first | exact @GlobalTheory.iterate_derivativeFun_mul_subst | exact GlobalTheory.iterate_derivativeFun_mul_subst | (intros; apply GlobalTheory.iterate_derivativeFun_mul_subst <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormalDeformationPowerSeriesSolution
open Polynomial

namespace GlobalTheory.FormalDeform

theorem constantCoeff_subst_eq {k : Type} [Field k] (a φ : PowerSeries k)
    (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.constantCoeff (φ.subst a : PowerSeries k) = PowerSeries.constantCoeff φ := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' ha
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_subst' hs,
    finsum_eq_single _ 0]
  · simp
  · intro d hd
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, ha, zero_pow hd, smul_zero]

theorem not_mem_pow_succ {A : Type} [CommRing A] [IsDedekindDomain A] {N : ℕ} {I : Type}
    [Fintype I] {D P₀ : Ideal A} {Q : I → Ideal A} {f₀ : A} (hP₀ : P₀.IsMaximal)
    (hQmax : ∀ i, (Q i).IsMaximal) (hQinj : Function.Injective Q) (hQP : ∀ i, Q i ≠ P₀)
    (hDQ : ∀ i, ¬ D ≤ Q i) (hf₀ : f₀ ≠ 0)
    (hspan : Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N) (i : I) : f₀ ∉ Q i ^ (N + 1) := by
  classical
  intro hmem
  have hQne : Q i ≠ ⊥ := by
    intro h
    rw [h, Ideal.bot_pow (Nat.succ_ne_zero N), Ideal.mem_bot] at hmem
    exact hf₀ hmem
  have hp : Prime (Q i) := Ideal.prime_of_isPrime hQne (hQmax i).isPrime
  have hdvd : Q i ^ (N + 1) ∣ Ideal.span {f₀} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
  have hsplit : Ideal.span {f₀} = Q i ^ N * (P₀ * D * ∏ j ∈ Finset.univ.erase i, Q j ^ N) := by
    rw [hspan, ← Finset.mul_prod_erase Finset.univ (fun j => Q j ^ N) (Finset.mem_univ i)]
    ring
  rw [hsplit, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero N hQne)] at hdvd
  rcases hp.dvd_or_dvd hdvd with h | h
  · rcases hp.dvd_or_dvd h with h | h
    · exact hQP i (hP₀.eq_of_le (hQmax i).ne_top (Ideal.le_of_dvd h)).symm
    · exact hDQ i (Ideal.le_of_dvd h)
  · have hprod : ∀ s : Finset I, Q i ∣ ∏ j ∈ s, Q j ^ N →
        ∃ j ∈ s, Q i ∣ Q j ^ N := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.prod_empty]
        intro hd
        exact (hp.not_unit (isUnit_iff_dvd_one.mpr hd)).elim
      | @insert j s hj ih =>
        rw [Finset.prod_insert hj]
        intro hd
        rcases hp.dvd_or_dvd hd with hd | hd
        · exact ⟨j, Finset.mem_insert_self _ _, hd⟩
        · obtain ⟨a, ha, had⟩ := ih hd
          exact ⟨a, Finset.mem_insert_of_mem ha, had⟩
    obtain ⟨j, hj, hji⟩ := hprod _ h
    have hle : Q j ≤ Q i := Ideal.le_of_dvd (hp.dvd_of_dvd_pow hji)
    exact (Finset.mem_erase.mp hj).1 (hQinj ((hQmax j).eq_of_le (hQmax i).ne_top hle))

theorem coeff_map_sum {k A : Type} [Field k] [CommRing A] [Algebra k A] {m : ℕ}
    (σ : A →ₐ[k] PowerSeries k) (v : Fin m → A) (c : Fin m → k) (l : ℕ) :
    ∑ j, c j * PowerSeries.coeff l (σ (v j)) = PowerSeries.coeff l (σ (∑ j, c j • v j)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_smul]

theorem formal_deformation : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (I : Type) [Fintype I] (V : Submodule k A) (D P₀ : Ideal A) (Q : I → Ideal A) (f₀ : A), 2 ≤ N → P₀.IsMaximal → (FiniteDimensional k V ∧ (∀ v ∈ V, v ∈ D) ∧ (∀ i, (Q i).IsMaximal) ∧ Function.Injective Q ∧ (∀ i, Q i ≠ P₀) ∧ (∀ i, ¬ D ≤ Q i) ∧ ¬ D ≤ P₀ ∧ f₀ ∈ V ∧ f₀ ≠ 0 ∧ Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N ∧ (∀ u : A, ∃ v ∈ V, u - v ∈ P₀ * ∏ i, Q i ^ (N - 1))) → ∃ (ξ : A →ₐ[k] PowerSeries k) (Δ : I → ℕ → A →ₗ[k] PowerSeries k) (m : ℕ) (v : Fin m → A) (y : Fin m → PowerSeries k),
  Function.Injective ξ ∧ (∀ i, Δ i 0 1 = 1) ∧ (∀ i, (∀ l, ∀ u w : A, Δ i l (u * w) = ∑ p ∈ Finset.range (l + 1), l.choose p • (Δ i p u * Δ i (l - p) w))) ∧ (∀ i, ∃ π : A, Δ i 1 π = 1) ∧
  (∀ j, v j ∈ V) ∧ LinearIndependent k v ∧ (∃ j, IsUnit (y j)) ∧ ∑ j, y j * ξ (v j) = 0 ∧ (∀ i, ∀ l < N, ∑ j, y j * Δ i l (v j) = 0) ∧
  (∀ i i', i ≠ i' → ∃ u : A, IsUnit (Δ i 0 u - Δ i' 0 u)) ∧ (∀ i, ∃ u : A, IsUnit (Δ i 0 u - ξ u)) ∧ (∀ i, ∃ u ∈ D, IsUnit (Δ i 0 u)) ∧ (∃ u ∈ D, IsUnit (ξ u)) := by
  intro k A _ _ _ _ _ _ _ N I _ V D P₀ Q f₀ hN hP₀ hyp
  obtain ⟨hVfin, hVD, hQmax, hQinj, hQP, hDQ, hDP, hf₀V, hf₀, hspan, hsurj⟩ := hyp
  classical
  have hne : Ideal.span {f₀} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hf₀
  have hf₀P : f₀ ∈ P₀ := by
    have : Ideal.span {f₀} ≤ P₀ := hspan ▸ le_trans Ideal.mul_le_left Ideal.mul_le_left
    exact this (Ideal.mem_span_singleton_self f₀)
  have hf₀Q : ∀ i, f₀ ∈ Q i ^ N := by
    intro i
    have h1 : Ideal.span {f₀} ≤ ∏ i, Q i ^ N := hspan ▸ Ideal.mul_le_right
    have h2 : (∏ i, Q i ^ N) ≤ Q i ^ N :=
      Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun j => Q j ^ N) (Finset.mem_univ i))
    exact h2 (h1 (Ideal.mem_span_singleton_self f₀))
  have hP₀ne : P₀ ≠ ⊥ := by
    rintro rfl; exact hf₀ ((Ideal.mem_bot).mp hf₀P)
  have hQne : ∀ i, Q i ≠ ⊥ := by
    intro i h
    have := hf₀Q i
    rw [h, Ideal.bot_pow (by omega), Ideal.mem_bot] at this
    exact hf₀ this

  obtain ⟨σ₀, π₀, -, hσ₀inj, hσ₀pow, hσ₀surj⟩ := GlobalTheory.T.exists_power_series_completion_embedding k A P₀ hP₀ hP₀ne
  have hcomp := fun i => GlobalTheory.T.exists_power_series_completion_embedding k A (Q i) (hQmax i) (hQne i)
  choose σ π hσπ hσinj hσpow hσsurj using hcomp
  have hzero : ∀ (τ : A →ₐ[k] PowerSeries k) (R : Ideal A),
      (∀ (m : ℕ) (u : A), u ∈ R ^ m ↔ (PowerSeries.X : PowerSeries k) ^ m ∣ τ u) →
      ∀ u, u ∈ R ↔ PowerSeries.constantCoeff (τ u) = 0 := by
    intro τ R h u
    rw [← PowerSeries.X_dvd_iff, ← pow_one (PowerSeries.X : PowerSeries k), ← h 1 u, pow_one]

  set b := Module.finBasis k V with hb
  set m := Module.finrank k V with hm
  let v : Fin m → A := fun j => (b j : A)
  have hrepr : ∀ x : V, ∑ j, b.repr x j • v j = (x : A) := by
    intro x
    have h := congrArg Subtype.val (b.sum_repr x)
    rw [Submodule.coe_sum] at h
    simpa [v] using h
  let y₀ : Fin m → k := fun j => b.repr ⟨f₀, hf₀V⟩ j
  have hy₀ : ∑ j, y₀ j • v j = f₀ := hrepr ⟨f₀, hf₀V⟩
  have hlin : ∀ (τ : A →ₐ[k] PowerSeries k) (c : Fin m → k) (l : ℕ),
      ∑ j, c j * PowerSeries.coeff l (τ (v j)) = PowerSeries.coeff l (τ (∑ j, c j • v j)) :=
    fun τ c l => coeff_map_sum τ v c l
  have hlin0 : ∀ (τ : A →ₐ[k] PowerSeries k) (c : Fin m → k),
      ∑ j, c j * PowerSeries.constantCoeff (τ (v j)) =
        PowerSeries.constantCoeff (τ (∑ j, c j • v j)) := by
    intro τ c
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hlin τ c 0
  have h1 : ∑ j, y₀ j * PowerSeries.constantCoeff (σ₀ (v j)) = 0 := by
    rw [hlin0, hy₀]; exact (hzero σ₀ P₀ hσ₀pow f₀).mp hf₀P
  have h2 : ∀ i, ∀ l < N, ∑ j, y₀ j * PowerSeries.coeff l (σ i (v j)) = 0 := by
    intro i l hl
    rw [hlin, hy₀]
    exact PowerSeries.X_pow_dvd_iff.mp ((hσpow i N f₀).mp (hf₀Q i)) l hl
  have h3 : ∀ i, ∑ j, y₀ j * PowerSeries.coeff N (σ i (v j)) ≠ 0 := by
    intro i hc
    rw [hlin, hy₀] at hc
    apply not_mem_pow_succ hP₀ hQmax hQinj hQP hDQ hf₀ hspan i
    rw [hσpow i (N + 1) f₀, PowerSeries.X_pow_dvd_iff]
    intro l hl
    rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl
    · exact PowerSeries.X_pow_dvd_iff.mp ((hσpow i N f₀).mp (hf₀Q i)) l hl
    · exact hc
  have h4 : ∀ (e₀ : k) (e : I → ℕ → k), ∃ h : Fin m → k,
      ∑ j, h j * PowerSeries.constantCoeff (σ₀ (v j)) = e₀ ∧
        ∀ i, ∀ l, l + 1 < N → ∑ j, h j * PowerSeries.coeff l (σ i (v j)) = e i l := by
    intro e₀ e
    obtain ⟨u₀, hu₀⟩ := hσ₀surj 1 (PowerSeries.C e₀)
    choose u hu using fun i => hσsurj i (N - 1) (PowerSeries.mk (e i))
    let P : Option I → Ideal A := fun o => o.elim P₀ Q
    let ex : Option I → ℕ := fun o => o.elim 1 (fun _ => N - 1)
    obtain ⟨w, hw⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Finset.univ) P ex
      (by
        rintro (_ | i) -
        exacts [Ideal.prime_of_isPrime hP₀ne hP₀.isPrime,
          Ideal.prime_of_isPrime (hQne i) (hQmax i).isPrime])
      (by
        rintro (_ | i) - (_ | j) - hij
        · exact absurd rfl hij
        · exact (hQP j).symm
        · exact hQP i
        · exact hQinj.ne (fun h => hij (by rw [h])))
      (fun o => o.1.elim u₀ u)
    have hw₀ : w - u₀ ∈ P₀ := by simpa [P, ex] using hw none (Finset.mem_univ _)
    have hwi : ∀ i, w - u i ∈ Q i ^ (N - 1) := fun i => by
      simpa [P, ex] using hw (some i) (Finset.mem_univ _)
    obtain ⟨v', hv'V, hv'⟩ := hsurj w
    have hv'P : v' - u₀ ∈ P₀ := by
      have : w - v' ∈ P₀ := Ideal.mul_le_left hv'
      have e1 : v' - u₀ = (w - u₀) - (w - v') := by ring
      rw [e1]; exact P₀.sub_mem hw₀ this
    have hv'Q : ∀ i, v' - u i ∈ Q i ^ (N - 1) := by
      intro i
      have h5 : (∏ i, Q i ^ (N - 1)) ≤ Q i ^ (N - 1) :=
        Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun j => Q j ^ (N - 1)) (Finset.mem_univ i))
      have : w - v' ∈ Q i ^ (N - 1) := h5 (Ideal.mul_le_right hv')
      have e1 : v' - u i = (w - u i) - (w - v') := by ring
      rw [e1]; exact Ideal.sub_mem _ (hwi i) this
    refine ⟨fun j => b.repr ⟨v', hv'V⟩ j, ?_, ?_⟩
    · rw [hlin0, hrepr ⟨v', hv'V⟩]
      have h6 : (PowerSeries.X : PowerSeries k) ^ 1 ∣ σ₀ v' - σ₀ u₀ := by
        rw [← map_sub, ← hσ₀pow 1, pow_one]; exact hv'P
      have h7 : (PowerSeries.X : PowerSeries k) ∣ PowerSeries.C e₀ - σ₀ v' := by
        have := dvd_sub hu₀ h6
        rw [pow_one] at this
        convert this using 1; ring
      rw [PowerSeries.X_dvd_iff, map_sub, PowerSeries.constantCoeff_C, sub_eq_zero] at h7
      exact h7.symm
    · intro i l hl
      rw [hlin, hrepr ⟨v', hv'V⟩]
      have h6 : (PowerSeries.X : PowerSeries k) ^ (N - 1) ∣ σ i v' - σ i (u i) := by
        rw [← map_sub, ← hσpow i]; exact hv'Q i
      have h7 := PowerSeries.X_pow_dvd_iff.mp (dvd_sub (hu i) h6) l (by omega)
      rw [show PowerSeries.mk (e i) - σ i (u i) - (σ i v' - σ i (u i)) =
        PowerSeries.mk (e i) - σ i v' by ring, map_sub, PowerSeries.coeff_mk, sub_eq_zero] at h7
      exact h7.symm
  obtain ⟨y, a, hy0, ha0, hyξ, hyΔ⟩ := GlobalTheory.T.deform_multiple_zeros_linear_family k (Fin m) I N (fun j => σ₀ (v j))
    (fun i j => σ i (v j)) y₀ (by omega) h1 h2 h3 h4
  have hsub : ∀ i, PowerSeries.HasSubst (a i) :=
    fun i => PowerSeries.HasSubst.of_constantCoeff_zero' (ha0 i)
  let Δ : I → ℕ → A →ₗ[k] PowerSeries k := fun i l =>
    (PowerSeries.substAlgHom (R := k) (hsub i)).toLinearMap ∘ₗ
      ((PowerSeries.derivative (R := k)).toLinearMap ^ l) ∘ₗ (σ i).toLinearMap
  have hΔ : ∀ i l u, Δ i l u =
      (((PowerSeries.derivativeFun)^[l] (σ i u)).subst (a i) : PowerSeries k) := by
    intro i l u
    simp only [Δ, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      Module.End.coe_pow, PowerSeries.coe_substAlgHom]
    rfl
  have hcc : ∀ i u, PowerSeries.constantCoeff (Δ i 0 u) = PowerSeries.constantCoeff (σ i u) := by
    intro i u
    rw [hΔ]
    exact constantCoeff_subst_eq _ _ (ha0 i)
  have hunit : ∀ φ : PowerSeries k, IsUnit φ ↔ PowerSeries.constantCoeff φ ≠ 0 := by
    intro φ; rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  have hQσ : ∀ i u, u ∈ Q i ↔ PowerSeries.constantCoeff (σ i u) = 0 :=
    fun i => hzero (σ i) (Q i) (hσpow i)
  have hPσ : ∀ u, u ∈ P₀ ↔ PowerSeries.constantCoeff (σ₀ u) = 0 := hzero σ₀ P₀ hσ₀pow
  refine ⟨σ₀, Δ, m, v, y, hσ₀inj, ?_, ?_, ?_, ?_, ?_, ?_, hyξ, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hΔ, Function.iterate_zero, id, map_one, ← PowerSeries.coe_substAlgHom (hsub i), map_one]
  · intro i l u w
    simp only [hΔ, map_mul]
    exact GlobalTheory.T.iterate_derivativeFun_mul_subst_leibniz k (a i) _ _ l (ha0 i)
  · intro i
    refine ⟨π i, ?_⟩
    have hX : PowerSeries.derivativeFun (PowerSeries.X : PowerSeries k) = 1 :=
      PowerSeries.derivative_X
    rw [hΔ, Function.iterate_one, hσπ, hX, ← PowerSeries.coe_substAlgHom (hsub i), map_one]
  · intro j; exact (b j).2
  · exact b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  · by_contra hcon
    push_neg at hcon
    have hz : ∀ j, y₀ j = 0 := by
      intro j
      have := hcon j
      rwa [hunit, hy0, not_not] at this
    apply hf₀
    rw [← hy₀]
    simp [hz]
  · intro i l hl
    simpa only [hΔ] using hyΔ i l hl
  · intro i i' hii'
    have hle : ¬ Q i' ≤ Q i := fun h =>
      hii' (hQinj ((hQmax i').eq_of_le (hQmax i).ne_top h)).symm
    obtain ⟨u, hu', hu⟩ := SetLike.not_le_iff_exists.mp hle
    refine ⟨u, ?_⟩
    rw [hunit, map_sub, hcc, hcc, (hQσ i' u).mp hu', sub_zero]
    exact fun h => hu ((hQσ i u).mpr h)
  · intro i
    have hle : ¬ P₀ ≤ Q i := fun h => hQP i (hP₀.eq_of_le (hQmax i).ne_top h).symm
    obtain ⟨u, hu', hu⟩ := SetLike.not_le_iff_exists.mp hle
    refine ⟨u, ?_⟩
    rw [hunit, map_sub, hcc, (hPσ u).mp hu', sub_zero]
    exact fun h => hu ((hQσ i u).mpr h)
  · intro i
    obtain ⟨u, hu', hu⟩ := SetLike.not_le_iff_exists.mp (hDQ i)
    refine ⟨u, hu', ?_⟩
    rw [hunit, hcc]
    exact fun h => hu ((hQσ i u).mpr h)
  · obtain ⟨u, hu', hu⟩ := SetLike.not_le_iff_exists.mp hDP
    refine ⟨u, hu', ?_⟩
    rw [hunit]
    exact fun h => hu ((hPσ u).mpr h)

end GlobalTheory.FormalDeform
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormalDeformationPowerSeriesSolutionStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formal_deformation_powerSeries_solution : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (I : Type) [Fintype I] (V : Submodule k A) (D P₀ : Ideal A) (Q : I → Ideal A) (f₀ : A), 2 ≤ N → P₀.IsMaximal → (FiniteDimensional k V ∧ (∀ v ∈ V, v ∈ D) ∧ (∀ i, (Q i).IsMaximal) ∧ Function.Injective Q ∧ (∀ i, Q i ≠ P₀) ∧ (∀ i, ¬ D ≤ Q i) ∧ ¬ D ≤ P₀ ∧ f₀ ∈ V ∧ f₀ ≠ 0 ∧ Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N ∧ (∀ u : A, ∃ v ∈ V, u - v ∈ P₀ * ∏ i, Q i ^ (N - 1))) → ∃ (ξ : A →ₐ[k] PowerSeries k) (Δ : I → ℕ → A →ₗ[k] PowerSeries k) (m : ℕ) (v : Fin m → A) (y : Fin m → PowerSeries k),
  Function.Injective ξ ∧ (∀ i, Δ i 0 1 = 1) ∧ (∀ i, (∀ l, ∀ u w : A, Δ i l (u * w) = ∑ p ∈ Finset.range (l + 1), l.choose p • (Δ i p u * Δ i (l - p) w))) ∧ (∀ i, ∃ π : A, Δ i 1 π = 1) ∧
  (∀ j, v j ∈ V) ∧ LinearIndependent k v ∧ (∃ j, IsUnit (y j)) ∧ ∑ j, y j * ξ (v j) = 0 ∧ (∀ i, ∀ l < N, ∑ j, y j * Δ i l (v j) = 0) ∧
  (∀ i i', i ≠ i' → ∃ u : A, IsUnit (Δ i 0 u - Δ i' 0 u)) ∧ (∀ i, ∃ u : A, IsUnit (Δ i 0 u - ξ u)) ∧ (∀ i, ∃ u ∈ D, IsUnit (Δ i 0 u)) ∧ (∃ u ∈ D, IsUnit (ξ u)) := by
  first | exact @GlobalTheory.FormalDeform.formal_deformation | exact GlobalTheory.FormalDeform.formal_deformation | (intros; apply GlobalTheory.FormalDeform.formal_deformation <;> assumption)
end
