module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.IaDivDown
public import Lemmata.PeriodicFunctions.PeriodicApplyMulAdd

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.WeightedSumToGaussSum
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.SumSliceEq
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.WeightedSumScaling
open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

open Loc LocE

section Perm

variable {K : Type} [Field K]

theorem perm_range (M : ℕ) (f : ℕ → ℕ) (hf : ∀ i < M, f i < M)
    (hinj : ∀ i < M, ∀ j < M, f i = f j → i = j) (g : ℕ → K) :
    ∑ i ∈ Finset.range M, g (f i) = ∑ i ∈ Finset.range M, g i := by
  have hI : Set.InjOn f (Finset.range M : Set ℕ) := fun i hi j hj h =>
    hinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) h
  rw [← Finset.sum_image (g := f) hI]
  congr 1
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_range.2 (hf i (Finset.mem_range.1 hi))
  · rw [Finset.card_image_of_injOn hI]

theorem sum_range_mul (M m : ℕ) (g : ℕ → K) (hg : ∀ i, g (i + M) = g i) :
    ∑ i ∈ Finset.range (M * m), g i = (m : K) * ∑ i ∈ Finset.range M, g i := by
  first | exact Bl.PeriodicFunctions.goal1 .. | (apply Bl.PeriodicFunctions.goal1 <;> assumption) | (intros; apply Bl.PeriodicFunctions.goal1 <;> assumption)

end Perm

variable {E K : Type} [Field E] [NumberField E] [Field K]

def Sg (P : HeightOneSpectrum (𝓞 E)) (A B : ℕ) (φ : E → K) : K :=
  ∑ i ∈ Finset.range (qOf P ^ (A + B)), φ ((i : E) / (qOf P : E) ^ A)

def W1 (P : HeightOneSpectrum (𝓞 E)) (A B : ℕ) (φ : E → K) : K := ((qOf P : K) ^ B)⁻¹ * Sg P A B φ

def Good1 (P : HeightOneSpectrum (𝓞 E)) (a b : ℕ) (φ : E → K) : Prop :=
  (∀ u, φ u ≠ 0 → IntAt P ((qOf P : E) ^ a * u)) ∧
  (∀ u δ, IntAt P (δ / (qOf P : E) ^ b) → φ (u + δ) = φ u)

variable {P : HeightOneSpectrum (𝓞 E)}

theorem sum_vals (hp : (Ideal.absNorm P.asIdeal).Prime) (A B : ℕ) (φ : E → K) :
    ∑ u ∈ valsQ E (qOf P) A B, φ u = Sg P A B φ := by
  classical
  have hq := pow_ne_zero A (qE_ne P hp)
  unfold valsQ Sg
  rw [Finset.sum_image]
  intro x _ y _ hxy
  have h2 : ((x : ℕ) : E) = y := by
    have := congrArg (· * (qOf P : E) ^ A) hxy
    simpa [div_mul_cancel₀ _ hq] using this
  exact_mod_cast h2

theorem good_function_mono {a b a' : ℕ} (ha : a ≤ a') {φ : E → K} (h : Good1 P a b φ) : Good1 P a' b φ :=
  ⟨fun u hu => ia_up P ha (h.1 u hu), h.2⟩

section Main

variable (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hK : ((qOf P : ℕ) : K) ≠ 0)
include hN hp hq

theorem sg_stab {a b A B : ℕ} (hA : a ≤ A) (hB : b ≤ B) {φ : E → K} (h : Good1 P a b φ) :
    Sg P A B φ = ((qOf P ^ (B - b) : ℕ) : K) * Sg P a b φ := by
  have hq0 := qE_ne P hp
  have qp : 0 < qOf P := hp.pos

  have s1 : Sg P A B φ = ∑ i ∈ Finset.range (qOf P ^ (a + B)), φ ((i : E) / (qOf P : E) ^ a) := by
    unfold Sg
    have hI : Set.InjOn (fun i : ℕ => qOf P ^ (A - a) * i) (Finset.range (qOf P ^ (a + B)) : Set ℕ) :=
      fun i _ j _ h => Nat.eq_of_mul_eq_mul_left (pow_pos qp _) h
    have hsub : (Finset.range (qOf P ^ (a + B))).image (fun i : ℕ => qOf P ^ (A - a) * i) ⊆
        Finset.range (qOf P ^ (A + B)) := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      rw [Finset.mem_range] at hi ⊢
      have : A + B = (A - a) + (a + B) := by omega
      rw [this, pow_add]
      exact Nat.mul_lt_mul_of_pos_left hi (pow_pos qp _)
    rw [← Finset.sum_subset hsub, Finset.sum_image hI]
    · refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      push_cast
      have : (qOf P : E) ^ A = (qOf P : E) ^ (A - a) * (qOf P : E) ^ a := by
        rw [← pow_add, Nat.sub_add_cancel hA]
      rw [this]
      field_simp
    · intro i hi hni
      by_contra hne
      have h1 := h.1 _ hne
      have e : (qOf P : E) ^ a * ((i : E) / (qOf P : E) ^ A) = (i : E) / (qOf P : E) ^ (A - a) := by
        have : (qOf P : E) ^ A = (qOf P : E) ^ (A - a) * (qOf P : E) ^ a := by
          rw [← pow_add, Nat.sub_add_cancel hA]
        rw [this]
        field_simp
      rw [e, hN.1 E P hp hq] at h1
      obtain ⟨i', rfl⟩ := h1
      apply hni
      refine Finset.mem_image.2 ⟨i', Finset.mem_range.2 ?_, rfl⟩
      have hi' := Finset.mem_range.1 hi
      have : A + B = (A - a) + (a + B) := by omega
      rw [this, pow_add] at hi'
      exact Nat.lt_of_mul_lt_mul_left hi'

  rw [s1]
  have e2 : qOf P ^ (a + B) = qOf P ^ (a + b) * qOf P ^ (B - b) := by
    rw [← pow_add]
    congr 1
    omega
  rw [e2, sum_range_mul]
  · rfl
  · intro i
    have e3 : (((i + qOf P ^ (a + b) : ℕ) : E) / (qOf P : E) ^ a) = (i : E) / (qOf P : E) ^ a + (qOf P : E) ^ b := by
      push_cast
      rw [pow_add]
      field_simp
    rw [e3]
    apply h.2
    rw [div_self (pow_ne_zero _ hq0)]
    exact ia_one P

include hK in
theorem weighted_sum_stable {a b A B : ℕ} (hA : a ≤ A) (hB : b ≤ B) {φ : E → K} (h : Good1 P a b φ) :
    W1 P A B φ = W1 P a b φ := by
  unfold W1
  rw [sg_stab hN hp hq hA hB h]
  push_cast
  have e : (qOf P : K) ^ B = (qOf P : K) ^ (B - b) * (qOf P : K) ^ b := by
    rw [← pow_add, Nat.sub_add_cancel hB]
  rw [e]
  field_simp

theorem sg_transl {a b : ℕ} {φ : E → K} (h : Good1 P a b φ) {β : E} (hβ : IntAt P ((qOf P : E) ^ a * β)) :
    Good1 P a b (fun u => φ (u + β)) ∧ Sg P a b (fun u => φ (u + β)) = Sg P a b φ := by
  have hq0 := qE_ne P hp
  have qp : 0 < qOf P := hp.pos
  refine ⟨⟨fun u hu => ?_, fun u δ hδ => ?_⟩, ?_⟩
  · have h1 := h.1 _ hu
    have e : (qOf P : E) ^ a * u = (qOf P : E) ^ a * (u + β) - (qOf P : E) ^ a * β := by ring
    rw [e]
    exact ia_sub P h1 hβ
  · show φ (u + δ + β) = φ (u + β)
    rw [add_right_comm]
    exact h.2 _ _ hδ
  · obtain ⟨j, -, hj⟩ := hN.2.1 E P hp hq _ (a + b) hβ
    set M := qOf P ^ (a + b) with hM
    have Mpos : 0 < M := pow_pos qp _
    unfold Sg
    rw [← hM]
    have key : ∀ i : ℕ, φ ((i : E) / (qOf P : E) ^ a + β) = φ ((((i + j) % M : ℕ) : E) / (qOf P : E) ^ a) := by
      intro i
      have hd := congrArg (Nat.cast (R := E)) (Nat.mod_add_div (i + j) M)
      push_cast at hd
      have e : (i : E) / (qOf P : E) ^ a + β = (((i + j) % M : ℕ) : E) / (qOf P : E) ^ a +
          ((((i + j) / M : ℕ) : E) * (qOf P : E) ^ b + (β - (j : E) / (qOf P : E) ^ a)) := by
        have hr : (((i + j) % M : ℕ) : E) = (i : E) + j - (qOf P : E) ^ (a + b) * (((i + j) / M : ℕ) : E) := by
          rw [hM] at hd
          push_cast at hd ⊢
          linear_combination hd
        rw [hr, pow_add]
        field_simp
        ring
      rw [e]
      apply h.2
      have e2 : ((((i + j) / M : ℕ) : E) * (qOf P : E) ^ b + (β - (j : E) / (qOf P : E) ^ a)) / (qOf P : E) ^ b =
          (((i + j) / M : ℕ) : E) + ((qOf P : E) ^ a * β - j) / (qOf P : E) ^ (a + b) := by
        rw [pow_add]
        field_simp
      rw [e2]
      exact ia_add P (ia_nat P _) hj
    simp only [key]
    exact perm_range M (fun i => (i + j) % M) (fun i _ => Nat.mod_lt _ Mpos)
      (fun i hi i' hi' hii => by
        have h3 : i % M = i' % M := Nat.ModEq.add_right_cancel' j hii
        rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at h3)
      (fun i => φ ((i : E) / (qOf P : E) ^ a))

theorem sg_unit {a b : ℕ} {φ : E → K} (h : Good1 P a b φ) {w : E} (hw : UnitAt P w) :
    Good1 P a b (fun u => φ (w * u)) ∧ Sg P a b (fun u => φ (w * u)) = Sg P a b φ := by
  have hq0 := qE_ne P hp
  have qp : 0 < qOf P := hp.pos
  refine ⟨⟨fun u hu => ?_, fun u δ hδ => ?_⟩, ?_⟩
  · have h1 := h.1 _ hu
    have e : (qOf P : E) ^ a * u = w⁻¹ * ((qOf P : E) ^ a * (w * u)) := by
      field_simp [hw.1]
    rw [e]
    exact ia_mul P hw.2.2 h1
  · show φ (w * (u + δ)) = φ (w * u)
    rw [mul_add]
    apply h.2
    rw [mul_div_assoc]
    exact ia_mul P hw.2.1 hδ
  · obtain ⟨w0, hco, hw0⟩ := hN.2.2.2.2 E P hp hq w (a + b) hw.1 hw.2.1 hw.2.2
    set M := qOf P ^ (a + b) with hM
    have Mpos : 0 < M := pow_pos qp _
    unfold Sg
    rw [← hM]
    have key : ∀ i : ℕ, φ (w * ((i : E) / (qOf P : E) ^ a)) = φ ((((w0 * i) % M : ℕ) : E) / (qOf P : E) ^ a) := by
      intro i
      have hd := congrArg (Nat.cast (R := E)) (Nat.mod_add_div (w0 * i) M)
      have e : w * ((i : E) / (qOf P : E) ^ a) = (((w0 * i) % M : ℕ) : E) / (qOf P : E) ^ a +
          ((((w0 * i) / M : ℕ) : E) * (qOf P : E) ^ b + (w - w0) * (i : E) / (qOf P : E) ^ a) := by
        have hr : (((w0 * i) % M : ℕ) : E) = (w0 : E) * i - (qOf P : E) ^ (a + b) * (((w0 * i) / M : ℕ) : E) := by
          rw [hM] at hd
          push_cast at hd ⊢
          linear_combination hd
        rw [hr, pow_add]
        field_simp
        ring
      rw [e]
      apply h.2
      have e2 : ((((w0 * i) / M : ℕ) : E) * (qOf P : E) ^ b + (w - w0) * (i : E) / (qOf P : E) ^ a) / (qOf P : E) ^ b =
          (((w0 * i) / M : ℕ) : E) + (i : E) * ((w - w0) / (qOf P : E) ^ (a + b)) := by
        rw [pow_add]
        field_simp
      rw [e2]
      exact ia_add P (ia_nat P _) (ia_mul P (ia_nat P _) hw0)
    simp only [key]
    have hcoM : Nat.gcd M w0 = 1 := by
      rw [hM, Nat.gcd_comm]
      exact Nat.Coprime.pow_right _ hco
    exact perm_range M (fun i => (w0 * i) % M) (fun i _ => Nat.mod_lt _ Mpos)
      (fun i hi i' hi' hii => by
        have h3 : i % M = i' % M := Nat.ModEq.cancel_left_of_coprime hcoM hii
        rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at h3)
      (fun i => φ ((i : E) / (qOf P : E) ^ a))

theorem sg_qpow {a b : ℕ} {φ : E → K} (h : Good1 P a b φ) (f : ℕ) :
    Good1 P (a + f) b (fun u => φ ((qOf P : E) ^ f * u)) ∧
      Sg P (a + f) b (fun u => φ ((qOf P : E) ^ f * u)) = ((qOf P ^ f : ℕ) : K) * Sg P a b φ := by
  have hq0 := qE_ne P hp
  refine ⟨⟨fun u hu => ?_, fun u δ hδ => ?_⟩, ?_⟩
  · have h1 := h.1 _ hu
    rw [pow_add, mul_assoc]
    exact h1
  · show φ ((qOf P : E) ^ f * (u + δ)) = φ ((qOf P : E) ^ f * u)
    rw [mul_add]
    apply h.2
    rw [mul_div_assoc]
    exact ia_mul P (ia_qpow P _) hδ
  · have e : Sg P (a + f) b (fun u => φ ((qOf P : E) ^ f * u)) = Sg P a (b + f) φ := by
      unfold Sg
      rw [show a + f + b = a + (b + f) by ring]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      rw [pow_add]
      field_simp
    rw [e, sg_stab hN hp hq le_rfl (Nat.le_add_right b f) h, Nat.add_sub_cancel_left]

theorem sg_qinv {a b : ℕ} {φ : E → K} (h : Good1 P a b φ) (f : ℕ) :
    Good1 P a (b + f) (fun u => φ (u / (qOf P : E) ^ f)) ∧
      Sg P a (b + f) (fun u => φ (u / (qOf P : E) ^ f)) = Sg P a b φ := by
  have hq0 := qE_ne P hp
  refine ⟨⟨fun u hu => ?_, fun u δ hδ => ?_⟩, ?_⟩
  · have h1 := h.1 _ hu
    have e : (qOf P : E) ^ a * u = (qOf P : E) ^ f * ((qOf P : E) ^ a * (u / (qOf P : E) ^ f)) := by
      field_simp
    rw [e]
    exact ia_mul P (ia_qpow P _) h1
  · show φ ((u + δ) / (qOf P : E) ^ f) = φ (u / (qOf P : E) ^ f)
    rw [add_div]
    apply h.2
    have e : δ / (qOf P : E) ^ f / (qOf P : E) ^ b = δ / (qOf P : E) ^ (b + f) := by
      rw [pow_add]
      field_simp
    rw [e]
    exact hδ
  · have e : Sg P a (b + f) (fun u => φ (u / (qOf P : E) ^ f)) = Sg P (a + f) b φ := by
      unfold Sg
      rw [show a + (b + f) = a + f + b by ring]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      rw [pow_add]
      field_simp
    rw [e, sg_stab hN hp hq (Nat.le_add_right a f) le_rfl h, Nat.sub_self, pow_zero, Nat.cast_one, one_mul]


include hK in
theorem weighted_sum_scaling {d : E} (hd : d ≠ 0) (a b : ℕ) :
    ∃ a' b' : ℕ, ∀ φ : E → K, Good1 P a b φ →
      Good1 P a' b' (fun u => φ (d * u)) ∧ W1 P a' b' (fun u => φ (d * u)) = (qOf P : K) ^ vq P d * W1 P a b φ := by
  have hq0 := qE_ne P hp
  obtain ⟨w, hdw, hw⟩ := vq_spec hN hp hq hd
  rcases Int.eq_nat_or_neg (vq P d) with ⟨f, hf | hf⟩
  · refine ⟨a + f, b, fun φ h => ?_⟩
    have e : (fun u => φ (d * u)) = fun u => (fun u => φ ((qOf P : E) ^ f * u)) (w * u) := by
      funext u
      rw [hdw, hf, zpow_natCast, mul_assoc]
    obtain ⟨g1, s1⟩ := sg_qpow hN hp hq h f
    obtain ⟨g2, s2⟩ := sg_unit hN hp hq g1 hw
    rw [e]
    refine ⟨g2, ?_⟩
    unfold W1
    rw [s2, s1, hf, zpow_natCast]
    push_cast
    ring
  · refine ⟨a, b + f, fun φ h => ?_⟩
    have e : (fun u => φ (d * u)) = fun u => (fun u => φ (u / (qOf P : E) ^ f)) (w * u) := by
      funext u
      rw [hdw, hf, zpow_neg, zpow_natCast]
      congr 1
      field_simp
    obtain ⟨g1, s1⟩ := sg_qinv hN hp hq h f
    obtain ⟨g2, s2⟩ := sg_unit hN hp hq g1 hw
    rw [e]
    refine ⟨g2, ?_⟩
    unfold W1
    rw [s2, s1, hf, zpow_neg, zpow_natCast, pow_add]
    field_simp

end Main

end PI.TwistedEisensteinNonvanishing.W
end
end

open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

open Loc LocE Function

variable {E K : Type} [Field E] [NumberField E] [Field K]

section Slice

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem sum_slice (k : ι) (S : ι → Finset E) (u0 : E) (F : (ι → E) → K) :
    ∑ t ∈ Fintype.piFinset S, F t =
      ∑ t ∈ Fintype.piFinset (update S k {u0}), ∑ u ∈ S k, F (update t k u) := by
  rw [← Finset.sum_product' (f := fun t u => F (update t k u))]
  refine Finset.sum_nbij' (fun t => (update t k u0, t k)) (fun p => update p.1 k p.2) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_product] at ht ⊢
    refine ⟨fun i => ?_, ht k⟩
    by_cases hi : i = k
    · subst hi; simp
    · simp [Function.update_of_ne hi, ht i]
  · intro p hp
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_product] at hp ⊢
    intro i
    by_cases hi : i = k
    · subst hi; simpa using hp.2
    · simpa [Function.update_of_ne hi] using hp.1 i
  · intro t _
    simp
  · intro p hp
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_product] at hp
    have h1 : p.1 k = u0 := by simpa using hp.1 k
    refine Prod.ext ?_ ?_
    · show update (update p.1 k p.2) k u0 = p.1
      rw [Function.update_idem, ← h1, Function.update_eq_self]
    · simp
  · intro t _
    simp

theorem sum_slice_eq (k : ι) (S : ι → Finset E) (T T' : Finset E) (F G : (ι → E) → K) (α : K)
    (h : ∀ t : ι → E, ∑ u ∈ T, F (update t k u) = α * ∑ u ∈ T', G (update t k u)) :
    ∑ t ∈ Fintype.piFinset (update S k T), F t = α * ∑ t ∈ Fintype.piFinset (update S k T'), G t := by
  rw [sum_slice k (update S k T) 0 F, sum_slice k (update S k T') 0 G]
  simp only [Function.update_idem, Function.update_self]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => h t

theorem good_slice {P : HeightOneSpectrum (𝓞 E)} {a b : ℕ} {H : (ι → E) → K} (hH : Good P a b H)
    (t : ι → E) (k : ι) : Good1 P a b (fun u => H (update t k u)) := by
  refine ⟨fun u hu => ?_, fun u δ hδ => ?_⟩
  · simpa using hH.1 (update t k u) hu k
  · have h0 : IntAt P 0 :=
      ⟨0, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
    have e : update t k (u + δ) = update t k u + Pi.single k δ := by
      funext l
      by_cases hl : l = k
      · subst hl; simp
      · simp [hl]
    show H (update t k (u + δ)) = H (update t k u)
    rw [e]
    refine hH.2 _ _ fun l => ?_
    by_cases hl : l = k
    · subst hl; simpa using hδ
    · simpa [hl] using h0

end Slice

section Stab

variable {P : HeightOneSpectrum (𝓞 E)} (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hK : ((qOf P : ℕ) : K) ≠ 0)
include hN hp hq

theorem sum_stab {ι : Type} [Fintype ι] [DecidableEq ι] {a b A B : ℕ} (hA : a ≤ A) (hB : b ≤ B)
    {H : (ι → E) → K} (hH : Good P a b H) :
    ∑ t ∈ Fintype.piFinset (fun _ : ι => valsQ E (qOf P) A B), H t =
      ((qOf P ^ (B - b) : ℕ) : K) ^ Fintype.card ι *
        ∑ t ∈ Fintype.piFinset (fun _ : ι => valsQ E (qOf P) a b), H t := by
  classical

  have sumV : ∀ (A' B' : ℕ) (φ : E → K), ∑ u ∈ valsQ E (qOf P) A' B', φ u = Sg P A' B' φ := by
    intro A' B' φ
    unfold valsQ Sg
    rw [Finset.sum_image]
    intro i hi j _ hij
    by_cases hq : ((qOf P : ℕ) : E) ^ A' = 0
    · exfalso
      have h2 := pow_eq_zero_iff'.1 hq
      have hq0 : qOf P = 0 := by exact_mod_cast h2.1
      simp [hq0, h2.2] at hi
    · exact_mod_cast (div_left_inj' hq).1 hij
  have hslice : ∀ (S : ι → Finset E) (k : ι),
      ∑ t ∈ Fintype.piFinset (update S k (valsQ E (qOf P) A B)), H t =
        ((qOf P ^ (B - b) : ℕ) : K) * ∑ t ∈ Fintype.piFinset (update S k (valsQ E (qOf P) a b)), H t :=
    fun S k => sum_slice_eq k S _ _ H H _ fun t => by
      rw [sumV, sumV, sg_stab hN hp hq hA hB (good_slice hH t k)]
  have key : ∀ s : Finset ι, ∑ t ∈ Fintype.piFinset (fun _ : ι => valsQ E (qOf P) A B), H t =
      ((qOf P ^ (B - b) : ℕ) : K) ^ s.card * ∑ t ∈ Fintype.piFinset
        (fun i => if i ∈ s then valsQ E (qOf P) a b else valsQ E (qOf P) A B), H t := by
    intro s
    refine Finset.induction_on s (by simp) ?_
    intro k s hk ih
    rw [ih, Finset.card_insert_of_notMem hk, pow_succ, mul_assoc]
    congr 1
    have e1 : (fun i => if i ∈ s then valsQ E (qOf P) a b else valsQ E (qOf P) A B) =
        update (fun i => if i ∈ s then valsQ E (qOf P) a b else valsQ E (qOf P) A B) k
          (valsQ E (qOf P) A B) := by
      funext i
      by_cases h : i = k
      · subst h; simp [hk]
      · simp [h]
    have e2 : (fun i => if i ∈ insert k s then valsQ E (qOf P) a b else valsQ E (qOf P) A B) =
        update (fun i => if i ∈ s then valsQ E (qOf P) a b else valsQ E (qOf P) A B) k
          (valsQ E (qOf P) a b) := by
      funext i
      by_cases h : i = k
      · subst h; simp
      · simp [h]
    rw [e2]
    conv_lhs => rw [e1]
    exact hslice _ k
  simpa using key Finset.univ

include hK in
theorem rs_stab {ι : Type} [Fintype ι] [DecidableEq ι] {a b A B : ℕ} (hA : a ≤ A) (hB : b ≤ B)
    {H : (ι → E) → K} (hH : Good P a b H) : RS P A B H = RS P a b H := by
  unfold RS
  rw [sum_stab hN hp hq hA hB hH, ← mul_assoc, ← mul_pow]
  congr 2
  push_cast
  have hqb : ((qOf P : K)) ^ B = (qOf P : K) ^ b * (qOf P : K) ^ (B - b) := by
    rw [← pow_add, Nat.add_sub_cancel' hB]
  rw [hqb, mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hK), mul_one]

end Stab

theorem stab_of (hN : NTAll) : StabP := by
  intro E' K' _ _ _ P hp hq hK ι _ _ a b H hH A B hA hB
  exact rs_stab hN hp hq hK hA hB hH

end PI.TwistedEisensteinNonvanishing.W
end
end

open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

open Loc LocE Function

variable {E K : Type} [Field E] [NumberField E] [Field K]

section QTdef

variable (P : HeightOneSpectrum (𝓞 E)) {ι : Type} [Fintype ι] [DecidableEq ι]

def QT (T : (ι → E) → (ι → E)) (c : K) : Prop :=
  ∀ a b : ℕ, ∃ a' b' : ℕ, ∀ H : (ι → E) → K, Good P a b H →
    Good P a' b' (fun t => H (T t)) ∧ RS P a' b' (fun t => H (T t)) = c * RS P a b H

variable {P}

theorem qt_comp {T1 T2 : (ι → E) → (ι → E)} {c1 c2 : K} (h1 : QT P T1 c1) (h2 : QT P T2 c2) :
    QT P (fun t => T1 (T2 t)) (c2 * c1) := by
  intro a b
  obtain ⟨a1, b1, h1'⟩ := h1 a b
  obtain ⟨a2, b2, h2'⟩ := h2 a1 b1
  refine ⟨a2, b2, fun H hH => ?_⟩
  obtain ⟨g1, r1⟩ := h1' H hH
  obtain ⟨g2, r2⟩ := h2' (fun t => H (T1 t)) g1
  exact ⟨g2, r2.trans (by rw [r1]; ring)⟩

theorem qt_congr {T T' : (ι → E) → (ι → E)} {c c' : K} (h : QT P T c) (hT : ∀ t, T' t = T t) (hc : c' = c) :
    QT P T' c' := by
  have hTT : T' = T := funext hT
  subst hTT
  subst hc
  exact h

def em (k l : ι) (d c β : E) (t : ι → E) : ι → E := update t k (d * t k + c * t l + β)

end QTdef

section Em

variable {P : HeightOneSpectrum (𝓞 E)} (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hK : ((qOf P : ℕ) : K) ≠ 0)
include hN hp hq hK

theorem weighted_sum_to_gauss_sum {N : ℕ} {f g : E → K} {c : K} (h : W1 P N N f = c * W1 P N N g) :
    Sg P N N f = c * Sg P N N g := by
  have hq0 : ((qOf P : K) ^ N)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hK)
  unfold W1 at h
  apply mul_left_cancel₀ hq0
  rw [h]
  ring

theorem qt_em {ι : Type} [Fintype ι] [DecidableEq ι] (k l : ι) {d : E} (hd : d ≠ 0) (c β : E)
    (hkl : l ≠ k ∨ c = 0) : QT P (em k l d c β) ((qOf P : K) ^ vq P d) := by
  have hq0 := qE_ne P hp
  intro a b
  obtain ⟨gc, hgc⟩ := ia_bound P hN hp hq c
  obtain ⟨gβ, hgβ⟩ := ia_bound P hN hp hq β
  obtain ⟨gd, hgd⟩ := ia_bound P hN hp hq d
  obtain ⟨gi, hgi⟩ := ia_bound P hN hp hq d⁻¹
  obtain ⟨a2, b2, hsc⟩ := weighted_sum_scaling (K := K) hN hp hq hK hd (a + gc + gβ) b

  have hcl : ∀ t : ι → E, (∀ j, IntAt P ((qOf P : E) ^ a * t j)) →
      IntAt P ((qOf P : E) ^ (a + gc + gβ) * (c * t l + β)) := by
    intro t ht
    have e : (qOf P : E) ^ (a + gc + gβ) * (c * t l + β) =
        (qOf P : E) ^ gβ * (((qOf P : E) ^ gc * c) * ((qOf P : E) ^ a * t l)) +
          (qOf P : E) ^ (a + gc) * ((qOf P : E) ^ gβ * β) := by
      rw [pow_add, pow_add]
      ring
    rw [e]
    exact ia_add P (ia_mul P (ia_qpow P _) (ia_mul P hgc (ht l))) (ia_mul P (ia_qpow P _) hgβ)
  have hcl' : ∀ t : ι → E, (∀ j, j ≠ k → IntAt P ((qOf P : E) ^ a * t j)) →
      IntAt P ((qOf P : E) ^ (a + gc + gβ) * (c * t l + β)) := by
    intro t ht
    rcases hkl with hlk | hc0
    · have e : (qOf P : E) ^ (a + gc + gβ) * (c * t l + β) =
          (qOf P : E) ^ gβ * (((qOf P : E) ^ gc * c) * ((qOf P : E) ^ a * t l)) +
            (qOf P : E) ^ (a + gc) * ((qOf P : E) ^ gβ * β) := by
        rw [pow_add, pow_add]
        ring
      rw [e]
      exact ia_add P (ia_mul P (ia_qpow P _) (ia_mul P hgc (ht l hlk))) (ia_mul P (ia_qpow P _) hgβ)
    · have e : (qOf P : E) ^ (a + gc + gβ) * (c * t l + β) = (qOf P : E) ^ (a + gc) * ((qOf P : E) ^ gβ * β) := by
        rw [hc0, pow_add]
        ring
      rw [e]
      exact ia_mul P (ia_qpow P _) hgβ
  have hupd : ∀ (t : ι → E) (u : E), c * update t k u l = c * t l := by
    intro t u
    rcases hkl with hlk | hc0
    · rw [update_of_ne hlk]
    · rw [hc0, zero_mul, zero_mul]
  refine ⟨a + gc + gβ + gi, b + gd + gc, fun H hH => ?_⟩
  have hgood : Good P (a + gc + gβ + gi) (b + gd + gc) (fun t => H (em k l d c β t)) := by
    refine ⟨fun t ht j => ?_, fun t δ hδ => ?_⟩
    · have hs := hH.1 _ ht
      have hoth : ∀ j, j ≠ k → IntAt P ((qOf P : E) ^ a * t j) := by
        intro j hj
        have := hs j
        rwa [em, update_of_ne hj] at this
      by_cases hj : j = k
      · subst hj
        have hx := hs j
        rw [em, update_self] at hx
        have e : (qOf P : E) ^ (a + gc + gβ + gi) * t j = ((qOf P : E) ^ gi * d⁻¹) *
            ((qOf P : E) ^ (gc + gβ) * ((qOf P : E) ^ a * (d * t j + c * t l + β)) -
              (qOf P : E) ^ (a + gc + gβ) * (c * t l + β)) := by
          rw [pow_add, pow_add, pow_add, pow_add]
          field_simp
          ring
        rw [e]
        exact ia_mul P hgi (ia_sub P (ia_mul P (ia_qpow P _) hx) (hcl' t hoth))
      · exact ia_up P (by omega) (hoth j hj)
    · have e : em k l d c β (t + δ) = em k l d c β t + update δ k (d * δ k + c * δ l) := by
        ext j
        by_cases hj : j = k
        · subst hj
          simp only [em, update_self, Pi.add_apply]
          ring
        · simp only [em, update_of_ne hj, Pi.add_apply]
      show H (em k l d c β (t + δ)) = H (em k l d c β t)
      rw [e]
      apply hH.2
      intro j
      by_cases hj : j = k
      · subst hj
        rw [update_self]
        have e2 : (d * δ j + c * δ l) / (qOf P : E) ^ b = ((qOf P : E) ^ gd * d) * (δ j / (qOf P : E) ^ (b + gd)) +
            ((qOf P : E) ^ gc * c) * (δ l / (qOf P : E) ^ (b + gc)) := by
          rw [pow_add, pow_add]
          field_simp
        rw [e2]
        exact ia_add P (ia_mul P hgd (ia_div_down P hp (by omega) (hδ j)))
          (ia_mul P hgc (ia_div_down P hp (by omega) (hδ l)))
      · rw [update_of_ne hj]
        exact ia_div_down P hp (by omega) (hδ j)
  refine ⟨hgood, ?_⟩
  set N := max (max (a + gc + gβ + gi) (b + gd + gc)) (max (max a2 b2) (a + gc + gβ + b)) with hNdef
  rw [← rs_stab hN hp hq hK (A := N) (B := N) (by omega) (by omega) hgood,
    ← rs_stab hN hp hq hK (A := N) (B := N) (by omega) (by omega) hH]
  have key : ∑ t ∈ Fintype.piFinset (fun _ : ι => valsQ E (qOf P) N N), H (em k l d c β t) =
      (qOf P : K) ^ vq P d * ∑ t ∈ Fintype.piFinset (fun _ : ι => valsQ E (qOf P) N N), H t := by
    have h0 := sum_slice_eq k (fun _ : ι => valsQ E (qOf P) N N) (valsQ E (qOf P) N N) (valsQ E (qOf P) N N)
      (fun t => H (em k l d c β t)) H ((qOf P : K) ^ vq P d) ?_
    · rwa [update_eq_self k (fun _ : ι => valsQ E (qOf P) N N)] at h0
    intro t
    have e1 : ∀ u, em k l d c β (update t k u) = update t k (d * u + (c * t l + β)) := by
      intro u
      rw [em, update_idem, update_self, hupd, add_assoc]
    simp only [e1]
    by_cases hz : ∀ u, H (update t k u) = 0
    · rw [Finset.sum_eq_zero (fun u _ => hz _), Finset.sum_eq_zero (fun u _ => hz _), mul_zero]
    simp only [not_forall] at hz
    obtain ⟨u0, hu0⟩ := hz
    have hs := hH.1 _ hu0
    have hβ' : IntAt P ((qOf P : E) ^ (a + gc + gβ) * (c * t l + β)) := by
      apply hcl'
      intro j hj
      have := hs j
      rwa [update_of_ne hj] at this
    obtain ⟨gψ, eψ⟩ := sg_transl hN hp hq (good_function_mono (by omega) (good_slice hH t k)) hβ'
    obtain ⟨gs, es⟩ := hsc _ gψ
    have s1 : ∑ u ∈ valsQ E (qOf P) N N, H (update t k (d * u + (c * t l + β))) =
        Sg P N N (fun u => H (update t k (d * u + (c * t l + β)))) := sum_vals hp N N _
    have s2 : ∑ u ∈ valsQ E (qOf P) N N, H (update t k u) = Sg P N N (fun u => H (update t k u)) :=
      sum_vals hp N N _
    rw [s1, s2]
    apply weighted_sum_to_gauss_sum hN hp hq hK
    have w1 : W1 P N N (fun u => H (update t k (d * u + (c * t l + β)))) =
        W1 P a2 b2 (fun u => H (update t k (d * u + (c * t l + β)))) :=
      weighted_sum_stable hN hp hq hK (by omega) (by omega) gs
    have w2 : W1 P N N (fun u => H (update t k u)) = W1 P (a + gc + gβ) b (fun u => H (update t k u)) :=
      weighted_sum_stable hN hp hq hK (by omega) (by omega) (good_function_mono (by omega) (good_slice hH t k))
    rw [w1, es, w2]
    unfold W1
    rw [eψ]
  unfold RS
  rw [key]
  ring

end Em

end PI.TwistedEisensteinNonvanishing.W
end
end

open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

open Loc LocE Function Matrix

variable {E K : Type} [Field E] [NumberField E] [Field K]

theorem qt_id {P : HeightOneSpectrum (𝓞 E)} {ι : Type} [Fintype ι] [DecidableEq ι] :
    QT P (fun t : ι → E => t) (1 : K) :=
  fun a b => ⟨a, b, fun _ h => ⟨h, (one_mul _).symm⟩⟩

section Lin

variable {P : HeightOneSpectrum (𝓞 E)} (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hK : ((qOf P : ℕ) : K) ≠ 0)
include hN hp hq hK

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem qt_transvec (t : TransvectionStruct ι E) :
    QT P (fun v => t.toMatrix *ᵥ v) ((qOf P : K) ^ vq P t.toMatrix.det) := by
  have hmv : ∀ v : ι → E, t.toMatrix *ᵥ v = em t.i t.j 1 t.c 0 v := by
    intro v
    funext k
    by_cases h : k = t.i
    · subst h
      simp [TransvectionStruct.toMatrix, Matrix.transvection, Matrix.add_mulVec,
        Matrix.single_mulVec, em] <;> ring
    · simp [TransvectionStruct.toMatrix, Matrix.transvection, Matrix.add_mulVec,
        Matrix.single_mulVec, em, h]
  exact qt_congr (qt_em hN hp hq hK t.i t.j one_ne_zero t.c 0 (Or.inl t.hij.symm)) hmv (by rw [t.det])

theorem qt_diag (D : ι → E) (hD : ∀ i, D i ≠ 0) :
    QT P (fun v => diagonal D *ᵥ v) ((qOf P : K) ^ vq P (diagonal D).det) := by
  classical
  have key : ∀ s : Finset ι, QT P (fun v : ι → E => fun k => if k ∈ s then D k * v k else v k)
      ((qOf P : K) ^ (∑ k ∈ s, vq P (D k))) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact qt_congr qt_id (fun v => by funext k; simp) (by simp)
    | insert a s ha ih =>
      refine qt_congr (qt_comp (qt_em hN hp hq hK a a (hD a) 0 0 (Or.inr rfl)) ih) (fun v => ?_) ?_
      · funext k
        by_cases hk : k = a
        · subst hk
          simp [em, ha]
        · simp [em, hk, Function.update_apply]
      · rw [Finset.sum_insert ha, zpow_add₀ hK, mul_comm]
  refine qt_congr (key Finset.univ) (fun v => by funext k; simp [Matrix.mulVec_diagonal]) ?_
  rw [Matrix.det_diagonal, vq_prod (s := Finset.univ) (f := D) (hf := fun i _ => hD i)]
  all_goals assumption

theorem qt_matrix (M : Matrix ι ι E) (hM : M.det ≠ 0) :
    QT P (fun v => M *ᵥ v) ((qOf P : K) ^ vq P M.det) := by
  classical
  obtain ⟨L, L', D, hMLD⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M
  have hlist : ∀ l : List (TransvectionStruct ι E),
      QT P (fun v => (l.map TransvectionStruct.toMatrix).prod *ᵥ v) (1 : K) := by
    intro l
    induction l with
    | nil => exact qt_congr qt_id (fun v => by simp) rfl
    | cons t l ih =>
      refine qt_congr (qt_comp (qt_transvec hN hp hq hK t) ih) (fun v => by simp [Matrix.mulVec_mulVec]) ?_
      rw [t.det, vq_one, zpow_zero, one_mul]
      all_goals assumption
  have hl1 : ∀ l : List (TransvectionStruct ι E), ((l.map TransvectionStruct.toMatrix).prod).det = 1 := by
    intro l
    induction l with
    | nil => simp
    | cons t l ih => simp [Matrix.det_mul, t.det, ih]
  have hdetM : M.det = (diagonal D).det := by
    rw [hMLD, Matrix.det_mul, Matrix.det_mul, hl1, hl1, one_mul, mul_one]
  have hD : ∀ i, D i ≠ 0 := by
    intro i hi
    apply hM
    rw [hdetM, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  refine qt_congr (qt_comp (hlist L) (qt_comp (qt_diag hN hp hq hK D hD) (hlist L')))
    (fun v => by rw [hMLD]; simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]) ?_
  rw [hdetM, one_mul, mul_one]

theorem qt_transl (τ : ι → E) : QT P (fun v : ι → E => v + τ) (1 : K) := by
  classical
  have key : ∀ s : Finset ι, QT P (fun v : ι → E => fun k => if k ∈ s then v k + τ k else v k) (1 : K) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact qt_congr qt_id (fun v => by funext k; simp) rfl
    | insert a s ha ih =>
      refine qt_congr (qt_comp (qt_em hN hp hq hK a a one_ne_zero 0 (τ a) (Or.inr rfl)) ih) (fun v => ?_) ?_
      · funext k
        by_cases hk : k = a
        · subst hk
          simp [em, ha]
        · simp [em, hk, Function.update_apply]
      · rw [vq_one, zpow_zero, one_mul]
        all_goals assumption
  exact qt_congr (key Finset.univ) (fun v => by funext k; simp) rfl

theorem qt_aff (L : (ι → E) ≃ₗ[E] (ι → E)) (τ : ι → E) :
    QT P (fun t => L t + τ) ((qOf P : K) ^ vq P (LinearMap.det (L : (ι → E) →ₗ[E] (ι → E)))) := by
  have hL : ∀ t, L t = LinearMap.toMatrix' (L : (ι → E) →ₗ[E] (ι → E)) *ᵥ t :=
    fun t => (LinearMap.toMatrix'_mulVec _ t).symm
  have hdet : (LinearMap.toMatrix' (L : (ι → E) →ₗ[E] (ι → E))).det ≠ 0 := by
    rw [LinearMap.det_toMatrix']
    exact (LinearEquiv.isUnit_det' L).ne_zero
  refine qt_congr (qt_comp (qt_transl hN hp hq hK τ) (qt_matrix hN hp hq hK _ hdet))
    (fun t => by simp only [hL]) ?_
  rw [LinearMap.det_toMatrix', mul_one]

end Lin

theorem cov_of (hN : NTAll) : CoVP := by
  intro E K _ _ _ P hp hq hK ι _ _ L τ
  exact ⟨(qOf P : K) ^ vq P (LinearMap.det (L : (ι → E) →ₗ[E] (ι → E))), zpow_ne_zero _ hK,
    qt_aff hN hp hq hK L τ⟩

end PI.TwistedEisensteinNonvanishing.W
