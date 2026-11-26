module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfKillsIdealPowerTorsionSemiAbelian

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimaryTorsionDivisibleAndTorsionEqIdealTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimaryTorsionDivisibleAndTorsionEqIdealTorsion
open NumberField

namespace GlobalTheory

theorem primaryTorsion_divisible_and_gTorsion :
    ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M] (g : ℕ) (I : Ideal (𝓞 E)), g.Prime → Ideal.absNorm I = g → (g : 𝓞 E) ∉ I ^ 2 → (∀ x : M, ∃ y : M, g • y = x) → (∀ (j : ℕ) (x : M), (∀ a ∈ I ^ j, a • x = 0) → ∃ y : M, g • y = x ∧ ∀ a ∈ I ^ (j + 1), a • y = 0) ∧ (∀ (j : ℕ) (x : M), (∀ a ∈ I ^ j, a • x = 0) → g • x = 0 → ∀ a ∈ I, a • x = 0) := by
  intro E _ _ M _ _ g I hg hN hg2 hdiv
  have hgI : (g : 𝓞 E) ∈ I := by
    have := Ideal.absNorm_mem I
    rwa [hN] at this
  have hIne : I ≠ ⊥ := by
    rintro rfl
    rw [Ideal.absNorm_bot] at hN
    exact hg.ne_zero hN.symm
  have hprime : I.IsPrime := Ideal.isPrime_of_irreducible_absNorm (by rw [hN]; exact hg)
  have hmax : I.IsMaximal := hprime.isMaximal hIne
  obtain ⟨J, hJ⟩ := (Ideal.dvd_iff_le).2 ((Ideal.span_singleton_le_iff_mem I).2 hgI)
  have hJI : ¬ J ≤ I := by
    intro h
    apply hg2
    have h2 : Ideal.span {(g : 𝓞 E)} ≤ I ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right h
    exact h2 (Ideal.mem_span_singleton_self _)
  have hsup : I ⊔ J = ⊤ := by
    by_contra h
    exact hJI (le_sup_right.trans (le_of_eq (hmax.eq_of_le h le_sup_left).symm))
  have hpow : ∀ k : ℕ, I ^ k ⊔ J = ⊤ := fun k => Ideal.pow_sup_eq_top hsup
  refine ⟨fun j x hx => ?_, fun j x hx hgx a ha => ?_⟩
  · obtain ⟨y0, hy0⟩ := hdiv x
    have h1 : (1 : 𝓞 E) ∈ I ^ j ⊔ J := by rw [hpow j]; exact Submodule.mem_top
    obtain ⟨f, hf, e, he, hfe⟩ := Submodule.mem_sup.1 h1
    refine ⟨e • y0, ?_, ?_⟩
    · rw [← Nat.cast_smul_eq_nsmul (𝓞 E), smul_comm, Nat.cast_smul_eq_nsmul (𝓞 E), hy0]
      have : e = 1 - f := by rw [← hfe]; ring
      rw [this, sub_smul, one_smul, hx f hf, sub_zero]
    · intro a ha
      have hae : a * e ∈ I ^ j * Ideal.span {(g : 𝓞 E)} := by
        rw [hJ, ← mul_assoc, ← pow_succ]
        exact Ideal.mul_mem_mul ha he
      have hker : I ^ j * Ideal.span {(g : 𝓞 E)} ≤
          LinearMap.ker (LinearMap.toSpanSingleton (𝓞 E) M y0) := by
        rw [Ideal.mul_le]
        intro c hc s hs
        obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hs
        rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← mul_assoc, mul_smul,
          Nat.cast_smul_eq_nsmul (𝓞 E), hy0]
        exact hx _ (Ideal.mul_mem_right _ _ hc)
      have := hker hae
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at this
      rw [smul_smul]; exact this
  · have hker : I ^ j ⊔ Ideal.span {(g : 𝓞 E)} ≤
        LinearMap.ker (LinearMap.toSpanSingleton (𝓞 E) M x) := by
      refine sup_le (fun b hb => ?_) ?_
      · rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]; exact hx b hb
      · refine (Ideal.span_singleton_le_iff_mem _).2 ?_
        rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, Nat.cast_smul_eq_nsmul]
        exact hgx
    have hIle : I ≤ I ^ j ⊔ Ideal.span {(g : 𝓞 E)} := by
      cases j with
      | zero => rw [pow_zero, Ideal.one_eq_top]; exact le_top.trans le_sup_left
      | succ k =>
        have h : I = I ^ (k + 1) ⊔ Ideal.span {(g : 𝓞 E)} := by
          calc I = I * (I ^ k ⊔ J) := by rw [hpow k, Ideal.mul_top]
            _ = I ^ (k + 1) ⊔ Ideal.span {(g : 𝓞 E)} := by rw [Ideal.mul_sup, hJ, pow_succ']
        exact h.le
    have := hker (hIle ha)
    rwa [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimaryTorsionDivisibleAndTorsionEqIdealTorsionStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primaryTorsion_divisible_and_torsion_eq_ideal_torsion : ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M] (g : ℕ) (I : Ideal (𝓞 E)), g.Prime → Ideal.absNorm I = g → (g : 𝓞 E) ∉ I ^ 2 → (∀ x : M, ∃ y : M, g • y = x) → (∀ (j : ℕ) (x : M), (∀ a ∈ I ^ j, a • x = 0) → ∃ y : M, g • y = x ∧ ∀ a ∈ I ^ (j + 1), a • y = 0) ∧ (∀ (j : ℕ) (x : M), (∀ a ∈ I ^ j, a • x = 0) → g • x = 0 → ∀ a ∈ I, a • x = 0) := by
  first | exact @GlobalTheory.primaryTorsion_divisible_and_gTorsion | exact GlobalTheory.primaryTorsion_divisible_and_gTorsion | (intros; apply GlobalTheory.primaryTorsion_divisible_and_gTorsion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOrderUnipotentAutDivisiblePrimaryEqId
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOrderUnipotentAutDivisiblePrimaryEqId
namespace GlobalTheory
namespace FiniteOrderUnipotent

open Finset

variable {A : Type} [AddCommGroup A]

theorem end_mul_apply (f h : AddMonoid.End A) (x : A) : (f * h) x = f (h x) := rfl

theorem end_add_apply (f h : AddMonoid.End A) (x : A) : (f + h) x = f x + h x := rfl

theorem end_nsmul_apply (n : ℕ) (f : AddMonoid.End A) (x : A) : (n • f) x = n • f x := rfl

theorem end_neg_apply (f : AddMonoid.End A) (x : A) : (-f) x = -f x := rfl

theorem end_zero_apply (x : A) : (0 : AddMonoid.End A) x = 0 := rfl

theorem inj_core {g : ℕ} (hprim : ∀ x : A, ∃ j : ℕ, g ^ j • x = 0)
    (N Z : AddMonoid.End A) (hc : Commute N Z) (k c : ℕ) (hcg : Nat.Coprime c g)
    (hk : ∀ x : A, g • x = 0 → (N ^ k) x = 0) :
    ∀ x : A, c • x = N (Z x) → x = 0 := by
  intro x hx
  obtain ⟨j, hj⟩ := hprim x
  induction j generalizing x with
  | zero => simpa using hj
  | succ j ih =>
    have hgx : g • x = 0 := by
      apply ih (g • x)
      · rw [smul_comm, hx, ← map_nsmul, ← map_nsmul]
      · rw [← mul_smul, ← pow_succ]; exact hj
    have key : ∀ i : ℕ, c ^ i • x = ((N * Z) ^ i) x := by
      intro i
      induction i with
      | zero => simp
      | succ i ih2 =>
        rw [pow_succ', mul_smul, ih2, ← map_nsmul, hx, pow_succ, end_mul_apply, end_mul_apply]
    have hck : c ^ k • x = 0 := by
      rw [key k, hc.mul_pow k, end_mul_apply]
      apply hk
      rw [← map_nsmul, hgx, map_zero]
    have h1 := addOrderOf_dvd_of_nsmul_eq_zero hck
    have h2 := addOrderOf_dvd_of_nsmul_eq_zero hgx
    have h3 := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one (hcg.pow_left k)] at h3
    exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem comm_geom (B : AddMonoid.End A) (n : ℕ) : Commute (B - 1) (∑ i ∈ range n, B ^ i) :=
  Commute.sum_right _ _ _ fun i _ => ((Commute.refl B).pow_right i).sub_left (Commute.one_left _)

theorem kill_mul {g k : ℕ} (N P : AddMonoid.End A) (hc : Commute N P)
    (hk : ∀ x : A, g • x = 0 → (N ^ k) x = 0) : ∀ x : A, g • x = 0 → ((N * P) ^ k) x = 0 := by
  intro x hx
  rw [hc.mul_pow k, end_mul_apply]
  apply hk
  rw [← map_nsmul, hx, map_zero]

theorem coprime_order {g : ℕ} (hprim : ∀ x : A, ∃ j : ℕ, g ^ j • x = 0)
    (B : AddMonoid.End A) (n k : ℕ) (hB : B ^ n = 1) (hng : Nat.Coprime n g)
    (hk : ∀ x : A, g • x = 0 → ((B - 1) ^ k) x = 0) : B = 1 := by
  set Z : AddMonoid.End A := ∑ i ∈ range n, ∑ j ∈ range i, B ^ j with hZ
  have hS : (∑ i ∈ range n, B ^ i) = (n : AddMonoid.End A) + (B - 1) * Z := by
    rw [hZ, Finset.mul_sum]
    simp_rw [mul_geom_sum]
    rw [Finset.sum_sub_distrib]
    simp
  have hSN : (∑ i ∈ range n, B ^ i) * (B - 1) = 0 := by
    rw [geom_sum_mul, hB, sub_self]
  have hcZ : Commute (B - 1) (-Z) := by
    refine Commute.neg_right ?_
    exact Commute.sum_right _ _ _ fun i _ => comm_geom B i
  rw [← sub_eq_zero]
  ext y
  have hx := congrArg (fun F : AddMonoid.End A => F y) hSN
  simp only [end_mul_apply] at hx
  rw [hS] at hx
  change (n : AddMonoid.End A) ((B - 1) y) + (B - 1) (Z ((B - 1) y)) = (0 : AddMonoid.End A) y at hx
  have hx' : n • ((B - 1) y) = (B - 1) ((-Z) ((B - 1) y)) := by
    have e0 : (-Z) ((B - 1) y) = -(Z ((B - 1) y)) := rfl
    rw [e0, map_neg, eq_neg_iff_add_eq_zero, ← AddMonoid.End.natCast_apply]
    exact hx
  simpa using inj_core hprim (B - 1) (-Z) hcZ k n hng hk _ hx'

theorem binom_identity (N : AddMonoid.End A) (h : ℕ) (hp : (h + 2).Prime) :
    (N + 1) ^ (h + 2) = 1 + (h + 2) • N
      + (h + 2) • (N ^ 2 * ∑ m ∈ range h, ((h + 2).choose (m + 2) / (h + 2)) • N ^ m)
      + N ^ (h + 2) := by
  rw [(Commute.one_right N).add_pow, sum_range_succ, sum_range_succ', sum_range_succ']
  simp only [one_pow, mul_one]
  have hmid : (∑ m ∈ range h, N ^ (m + 1 + 1) * (((h + 2).choose (m + 1 + 1) : ℕ) : AddMonoid.End A))
      = (h + 2) • (N ^ 2 * ∑ m ∈ range h, ((h + 2).choose (m + 2) / (h + 2)) • N ^ m) := by
    rw [Finset.mul_sum]
    rw [← Finset.sum_nsmul]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hlt : m + 2 < h + 2 := by simp at hm; omega
    have hdvd := hp.dvd_choose_self (k := m + 2) (by omega) hlt
    rw [mul_smul_comm, smul_smul, Nat.mul_div_cancel' hdvd, ← pow_add, ← nsmul_eq_mul']
    congr 2
    omega
  rw [hmid]
  simp only [pow_zero, pow_one, Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_self,
    Nat.cast_one, mul_one, zero_add]
  rw [← nsmul_eq_mul']
  abel

theorem prime_order {g : ℕ} (hg : g.Prime) (hprim : ∀ x : A, ∃ j : ℕ, g ^ j • x = 0)
    (hdiv : ∀ x : A, ∃ y : A, g • y = x)
    (B : AddMonoid.End A) (k : ℕ) (hkg : k + 2 ≤ g) (hB : B ^ g = 1)
    (hk : ∀ x : A, g • x = 0 → ((B - 1) ^ k) x = 0) : B = 1 := by
  obtain ⟨e, rfl⟩ : ∃ e, g = k + e + 2 := ⟨g - k - 2, by omega⟩
  set N := B - 1 with hN
  have hBN : B = N + 1 := by rw [hN, sub_add_cancel]
  set V : AddMonoid.End A :=
    ∑ m ∈ range (k + e), ((k + e + 2).choose (m + 2) / (k + e + 2)) • N ^ m with hV
  have hid := binom_identity N (k + e) hg
  rw [← hBN, hB] at hid
  have hid' : (k + e + 2) • N + ((k + e + 2) • (N ^ 2 * V) + N ^ (k + e + 2)) = 0 := by
    rw [eq_comm, add_assoc, add_assoc, add_eq_left] at hid
    exact hid
  have hNV : Commute N V :=
    Commute.sum_right _ _ _ fun m _ => ((Commute.refl N).pow_right m).smul_right _
  choose d hd using hdiv
  let M : AddMonoid.End A :=
    { toFun := fun y => (N ^ k) (d y)
      map_zero' := hk _ (hd 0)
      map_add' := fun a b => by
        rw [← map_add (f := _), ← sub_eq_zero, ← map_sub]
        apply hk
        rw [smul_sub, smul_add, hd, hd, hd, sub_self] }
  have hMy : ∀ y, M y = (N ^ k) (d y) := fun y => rfl
  have hMN : ∀ y, M (N y) = N (M y) := by
    intro y
    rw [hMy, hMy, ← end_mul_apply N, (Commute.self_pow N k).eq, end_mul_apply,
      ← sub_eq_zero, ← map_sub]
    apply hk
    rw [smul_sub, hd, ← map_nsmul, hd, sub_self]
  have hcM : Commute N M := by
    show N * M = M * N
    ext y
    exact (hMN y).symm
  have hcZ : Commute N (-(V + N ^ e * M)) :=
    (hNV.add_right (((Commute.refl N).pow_right e).mul_right hcM)).neg_right
  rw [← sub_eq_zero]
  ext y
  have h0 := congrArg (fun F : AddMonoid.End A => F (d y)) hid'
  simp only [end_add_apply, end_nsmul_apply, end_mul_apply, end_zero_apply] at h0
  rw [← map_nsmul, hd, ← map_nsmul, ← map_nsmul, hd] at h0
  have hpow : N ^ (k + e + 2) = N ^ e * N * N * N ^ k := by
    rw [← pow_succ, ← pow_succ, ← pow_add]
    congr 1
    omega
  rw [hpow, end_mul_apply, end_mul_apply, end_mul_apply, ← hMy, ← hMN, sq, end_mul_apply,
    ← end_mul_apply N V, hNV.eq, end_mul_apply] at h0
  have hx : 1 • (N y) = N ((-(V + N ^ e * M)) (N y)) := by
    rw [one_smul, end_neg_apply, map_neg, end_add_apply, end_mul_apply, map_add (f := _), eq_neg_iff_add_eq_zero]
    rw [← end_mul_apply N (N ^ e), ← pow_succ', pow_succ, end_mul_apply]
    exact h0
  exact inj_core hprim N _ hcZ k 1 (Nat.coprime_one_left _) hk _ hx

theorem nil_index {g r : ℕ} (hg : g.Prime) (T : Finset A) (hT : T.card ≤ g ^ r)
    (hTA : ∀ x : A, g • x = 0 → x ∈ T) (N : AddMonoid.End A) (m : ℕ)
    (hm : ∀ x : A, g • x = 0 → (N ^ m) x = 0) : ∀ x : A, g • x = 0 → (N ^ r) x = 0 := by
  haveI := Fact.mk hg
  let S : AddSubgroup A :=
    { carrier := {x | g • x = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [smul_add, ha, hb, add_zero]
      zero_mem' := smul_zero _
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [smul_neg, ha, neg_zero] }
  have hS : ∀ x : A, x ∈ S ↔ g • x = 0 := fun x => Iff.rfl
  obtain ⟨_⟩ : Nonempty (Module (ZMod g) S) := ⟨AddCommGroup.zmodModule (fun x => Subtype.ext (by
    simpa using (hS x.1).mp x.2))⟩
  haveI : Finite S := Finite.of_injective (fun x : S => (⟨x.1, hTA x.1 ((hS x.1).mp x.2)⟩ : T))
    (by intro a b h; apply Subtype.ext; simpa using congrArg Subtype.val h)
  haveI : Module.Finite (ZMod g) S := Module.Finite.of_finite
  have hcard : Nat.card S ≤ g ^ r := by
    have := Nat.card_le_card_of_injective (fun x : S => (⟨x.1, hTA x.1 ((hS x.1).mp x.2)⟩ : T))
      (by intro a b h; apply Subtype.ext; simpa using congrArg Subtype.val h)
    rw [Nat.card_eq_fintype_card (α := T), Fintype.card_coe] at this
    exact this.trans hT
  have hc2 : Nat.card S = g ^ Module.finrank (ZMod g) S := by
    have := @Module.natCard_eq_pow_finrank (ZMod g) S _ _ _ _
    rw [this, Nat.card_zmod]
  rw [hc2] at hcard
  have hle : Module.finrank (ZMod g) S ≤ r := (Nat.pow_le_pow_iff_right hg.one_lt).mp hcard
  let f : S →+ S :=
    { toFun := fun x => ⟨N x.1, by
        rw [hS, ← map_nsmul, (hS x.1).mp x.2, map_zero]⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  let fl : S →ₗ[ZMod g] S := f.toZModLinearMap g
  have hpow : ∀ (i : ℕ) (x : S), ((fl ^ i) x : A) = (N ^ i) x.1 := by
    intro i
    induction i with
    | zero => intro x; rfl
    | succ i ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, end_mul_apply]
      rfl
  have hnil : IsNilpotent fl := ⟨m, LinearMap.ext fun x => Subtype.ext (by
    rw [hpow]; exact hm _ ((hS x.1).mp x.2))⟩
  have hfin : fl ^ Module.finrank (ZMod g) S = 0 := by
    have h := LinearMap.aeval_self_charpoly fl
    rw [hnil.charpoly_eq_X_pow_finrank, Polynomial.aeval_X_pow] at h
    exact h
  have hr : fl ^ r = 0 := pow_eq_zero_of_le hle hfin
  intro x hx
  have := hpow r ⟨x, (hS x).mpr hx⟩
  rw [hr] at this
  exact this.symm

theorem kill_geom {g r : ℕ} (C : AddMonoid.End A) (s : ℕ)
    (h : ∀ x : A, g • x = 0 → ((C - 1) ^ r) x = 0) :
    ∀ x : A, g • x = 0 → ((C ^ s - 1) ^ r) x = 0 := by
  rw [← mul_geom_sum]
  exact kill_mul _ _ (comm_geom C s) h

end FiniteOrderUnipotent


open FiniteOrderUnipotent in
theorem finite_order_unipotent_eq_id : ∀ (A : Type) [AddCommGroup A] (β : A →+ A) (n g r m : ℕ),
    0 < n → (∀ x : A, β^[n] x = x) → g.Prime → r + 2 ≤ g → (∀ x : A, ∃ y : A, g • y = x) →
    (∀ x : A, ∃ j : ℕ, g ^ j • x = 0) →
    (∃ T : Finset A, T.card ≤ g ^ r ∧ ∀ x : A, g • x = 0 → x ∈ T) →
    (∀ x : A, g • x = 0 → (fun z => β z - z)^[m] x = 0) → ∀ x : A, β x = x := by
  intro A _ β n g r m hn hβ hg hrg hdiv hprim hT hu
  obtain ⟨T, hTc, hTA⟩ := hT
  let B : AddMonoid.End A := β
  have hBn : B ^ n = 1 := by
    ext x
    rw [AddMonoid.End.coe_pow]
    exact hβ x
  have hcoe : ⇑(B - 1) = fun z => β z - z := rfl
  have hm : ∀ x : A, g • x = 0 → ((B - 1) ^ m) x = 0 := by
    intro x hx
    rw [AddMonoid.End.coe_pow, hcoe]
    exact hu x hx
  have hr := nil_index hg T hTc hTA (B - 1) m hm
  obtain ⟨a, n', hndvd, hnn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' g hg.ne_one
  have hcop : Nat.Coprime n' g := ((Nat.Prime.coprime_iff_not_dvd hg).mpr hndvd).symm
  have claim : ∀ (a : ℕ) (C : AddMonoid.End A), (∀ x : A, g • x = 0 → ((C - 1) ^ r) x = 0) →
      C ^ (g ^ a) = 1 → C = 1 := by
    intro a
    induction a with
    | zero => intro C _ h; simpa using h
    | succ a ih =>
      intro C hC hCa
      have hCg : C ^ g = 1 :=
        ih (C ^ g) (kill_geom C g hC) (by rw [← pow_mul, ← pow_succ']; exact hCa)
      exact prime_order hg hprim hdiv C r hrg hCg hC
  have hB1 : B ^ (g ^ a) = 1 := by
    refine coprime_order hprim (B ^ (g ^ a)) n' r ?_ hcop (kill_geom B (g ^ a) hr)
    rw [← pow_mul, ← hnn, hBn]
  have hB : B = 1 := claim a B hr hB1
  intro x
  show B x = x
  rw [hB]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOrderUnipotentAutDivisiblePrimaryEqIdStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteOrder_unipotent_aut_divisible_primary_eq_id : ∀ (A : Type) [AddCommGroup A] (β : A →+ A) (n g r m : ℕ), 0 < n → (∀ x : A, β^[n] x = x) → g.Prime → r + 2 ≤ g → (∀ x : A, ∃ y : A, g • y = x) → (∀ x : A, ∃ j : ℕ, g ^ j • x = 0) → (∃ T : Finset A, T.card ≤ g ^ r ∧ ∀ x : A, g • x = 0 → x ∈ T) → (∀ x : A, g • x = 0 → (fun z => β z - z)^[m] x = 0) → ∀ x : A, β x = x := by
  first | exact @GlobalTheory.finite_order_unipotent_eq_id | exact GlobalTheory.finite_order_unipotent_eq_id | (intros; apply GlobalTheory.finite_order_unipotent_eq_id <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallTorsionSetForEndomorphism
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.NeatUnip

theorem iter_comp {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] (α : G ⟶ G) (n : ℕ)
    (x : 𝟙_ (Over (Sp k)) ⟶ G) :
    x ≫ (fun f : G ⟶ G => f ≫ α)^[n] (𝟙 G) = (fun z => z ≫ α)^[n] x := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    rw [← ih, Category.assoc]

theorem finite_order_unipotent_eq_id : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G] (act : OAct (𝓞 E) G) (α : G ⟶ G) (n m g r : ℕ) (I : Ideal (𝓞 E)), IsSemiAbelian G → IsMonHom α → (∀ a, act.act a ≫ α = α ≫ act.act a) → 0 < n → (fun f : G ⟶ G => f ≫ α)^[n] (𝟙 G) = 𝟙 G → g.Prime → Ideal.absNorm I = g → (g : 𝓞 E) ∉ I ^ 2 → r + 1 < g → (∃ T : Finset (𝟙_ (Over (Sp k)) ⟶ G), T.card ≤ g ^ r ∧ ∀ x : 𝟙_ (Over (Sp k)) ⟶ G, (∀ a ∈ I, x ≫ act.act a = 1) → x ∈ T) → (∀ x : 𝟙_ (Over (Sp k)) ⟶ G, (∀ a ∈ I, x ≫ act.act a = 1) → (fun z : 𝟙_ (Over (Sp k)) ⟶ G => (z ≫ α) * z⁻¹)^[m] x = 1) → α = 𝟙 G := by
  intro E _ _ k _ _ _ G _ act α n m g r I hG hα hcomm hn hpow hg hI hI2 hr hfin hunip
  classical
  haveI := hG.comm
  haveI := hα
  haveI : ∀ a, IsMonHom (act.act a) := act.hom
  letI cg : CommGroup (𝟙_ (Over (Sp k)) ⟶ G) := Hom.commGroup
  have act0 : act.act 0 = 1 := by
    have h := act.add 0 0
    rw [add_zero] at h
    exact left_eq_mul.mp h
  letI inst : Module (𝓞 E) (Additive (𝟙_ (Over (Sp k)) ⟶ G)) :=
  { smul := fun a x => Additive.ofMul (x.toMul ≫ act.act a)
    one_smul := fun x => by
      show Additive.ofMul (x.toMul ≫ act.act 1) = x
      rw [act.one, Category.comp_id]; rfl
    mul_smul := fun a b x => by
      show Additive.ofMul (x.toMul ≫ act.act (a * b)) = Additive.ofMul ((x.toMul ≫ act.act b) ≫ act.act a)
      rw [mul_comm a b, act.mul, Category.assoc]
    smul_zero := fun a => by
      show Additive.ofMul ((1 : 𝟙_ (Over (Sp k)) ⟶ G) ≫ act.act a) = Additive.ofMul 1
      rw [MonObj.one_comp]
    smul_add := fun a x y => by
      show Additive.ofMul ((x.toMul * y.toMul) ≫ act.act a) = Additive.ofMul ((x.toMul ≫ act.act a) * (y.toMul ≫ act.act a))
      rw [MonObj.mul_comp]
    add_smul := fun a b x => by
      show Additive.ofMul (x.toMul ≫ act.act (a + b)) = Additive.ofMul ((x.toMul ≫ act.act a) * (x.toMul ≫ act.act b))
      rw [act.add, MonObj.comp_mul]
    zero_smul := fun x => by
      show Additive.ofMul (x.toMul ≫ act.act 0) = Additive.ofMul 1
      rw [act0, MonObj.comp_one] }
  have hsmul : ∀ (a : 𝓞 E) (x : Additive (𝟙_ (Over (Sp k)) ⟶ G)), a • x = Additive.ofMul (x.toMul ≫ act.act a) :=
    fun _ _ => rfl
  have htors : ∀ (J : Ideal (𝓞 E)) (x : 𝟙_ (Over (Sp k)) ⟶ G),
      (∀ a ∈ J, a • Additive.ofMul x = 0) ↔ ∀ a ∈ J, x ≫ act.act a = 1 := fun J x =>
    forall₂_congr fun a _ => by rw [hsmul]; exact ofMul_eq_zero
  let β : Additive (𝟙_ (Over (Sp k)) ⟶ G) →ₗ[𝓞 E] Additive (𝟙_ (Over (Sp k)) ⟶ G) :=
  { toFun := fun x => Additive.ofMul (x.toMul ≫ α)
    map_add' := fun x y => by
      show Additive.ofMul ((x.toMul * y.toMul) ≫ α) = Additive.ofMul ((x.toMul ≫ α) * (y.toMul ≫ α))
      rw [MonObj.mul_comp]
    map_smul' := fun a x => by
      show Additive.ofMul ((x.toMul ≫ act.act a) ≫ α) = Additive.ofMul ((x.toMul ≫ α) ≫ act.act a)
      rw [Category.assoc, hcomm, Category.assoc] }
  have hβ : ∀ x, β x = Additive.ofMul (x.toMul ≫ α) := fun _ => rfl

  let A : AddSubgroup (Additive (𝟙_ (Over (Sp k)) ⟶ G)) :=
  { carrier := {x | ∃ j : ℕ, ∀ a ∈ I ^ j, a • x = 0}
    add_mem' := by
      rintro x y ⟨i, hi⟩ ⟨j, hj⟩
      refine ⟨i + j, fun a ha => ?_⟩
      rw [smul_add, hi a (Ideal.pow_le_pow_right (by omega) ha),
        hj a (Ideal.pow_le_pow_right (by omega) ha), add_zero]
    zero_mem' := ⟨0, fun a _ => smul_zero a⟩
    neg_mem' := by
      rintro x ⟨j, hj⟩
      exact ⟨j, fun a ha => by rw [smul_neg, hj a ha, neg_zero]⟩ }
  have memA : ∀ x, x ∈ A ↔ ∃ j : ℕ, ∀ a ∈ I ^ j, a • x = 0 := fun _ => Iff.rfl
  let βA : A →+ A :=
  { toFun := fun x => ⟨β x.1, by
      obtain ⟨j, hj⟩ := (memA x.1).1 x.2
      exact ⟨j, fun a ha => by rw [← LinearMap.map_smul, hj a ha, map_zero]⟩⟩
    map_zero' := Subtype.ext (map_zero β)
    map_add' := fun x y => Subtype.ext (map_add β x.1 y.1) }
  have hβA : ∀ x : A, ((βA x : A) : Additive (𝟙_ (Over (Sp k)) ⟶ G)) = β x.1 := fun _ => rfl
  have hβAit : ∀ (N : ℕ) (x : A), ((βA^[N] x : A) : Additive (𝟙_ (Over (Sp k)) ⟶ G)) = β^[N] x.1 := by
    intro N; induction N with
    | zero => intro x; rfl
    | succ N ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hβA, ih]
  have hβit : ∀ (N : ℕ) (x : Additive (𝟙_ (Over (Sp k)) ⟶ G)),
      β^[N] x = Additive.ofMul ((fun z => z ≫ α)^[N] x.toMul) := by
    intro N; induction N with
    | zero => intro x; rfl
    | succ N ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]; rfl
  have hsubit : ∀ (N : ℕ) (x : A),
      (((fun z : A => βA z - z)^[N] x : A) : Additive (𝟙_ (Over (Sp k)) ⟶ G)) =
        Additive.ofMul ((fun z : 𝟙_ (Over (Sp k)) ⟶ G => (z ≫ α) * z⁻¹)^[N] (Additive.toMul x.1)) := by
    intro N; induction N with
    | zero => intro x; rfl
    | succ N ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', AddSubgroup.coe_sub, hβA, ih, hβ,
        toMul_ofMul, ← ofMul_div, div_eq_mul_inv]
  have hgI : (g : 𝓞 E) ∈ I := hI ▸ Ideal.absNorm_mem I
  have hdivM : ∀ x : Additive (𝟙_ (Over (Sp k)) ⟶ G), ∃ y, g • y = x := by
    intro x
    obtain ⟨y, hy⟩ := GlobalTheory.SS.torusExtension_points_divisible k G (GlobalTheory.TorsionDense.nonempty_torusExtension G hG)
      g hg.one_le x.toMul
    exact ⟨Additive.ofMul y, by rw [← ofMul_pow, hy]; rfl⟩
  obtain ⟨hred1, hred2⟩ := GlobalTheory.T.primaryTorsion_divisible_and_torsion_eq_ideal_torsion E (Additive (𝟙_ (Over (Sp k)) ⟶ G)) g I hg hI hI2 hdivM
  have key := GlobalTheory.T.finiteOrder_unipotent_aut_divisible_primary_eq_id A βA n g r m hn
    (fun x => Subtype.ext (by
      rw [hβAit, hβit, ← iter_comp, hpow, Category.comp_id]; rfl))
    hg (by omega)
    (fun x => by
      obtain ⟨j, hj⟩ := (memA x.1).1 x.2
      obtain ⟨y, hy, hy'⟩ := hred1 j x.1 hj
      exact ⟨⟨y, j + 1, hy'⟩, Subtype.ext (by rw [AddSubgroup.coe_nsmul]; exact hy)⟩)
    (fun x => by
      obtain ⟨j, hj⟩ := (memA x.1).1 x.2
      refine ⟨j, Subtype.ext ?_⟩
      rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero, ← Nat.cast_smul_eq_nsmul (𝓞 E), Nat.cast_pow]
      exact hj _ (Ideal.pow_mem_pow hgI j))
    (by
      obtain ⟨T, hT, hTm⟩ := hfin
      refine ⟨(T.map Additive.ofMul.toEmbedding).subtype (· ∈ A), ?_, fun x hx => ?_⟩
      · rw [Finset.card_subtype]
        exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_map]; exact hT)
      · have hx' : g • x.1 = 0 := by have := congrArg Subtype.val hx; simpa using this
        obtain ⟨j, hj⟩ := (memA x.1).1 x.2
        have h1 := hred2 j x.1 hj hx'
        rw [Finset.mem_subtype, Finset.mem_map]
        exact ⟨Additive.toMul x.1, hTm _ ((htors I _).1 h1), rfl⟩)
    (fun x hx => by
      have hx' : g • x.1 = 0 := by have := congrArg Subtype.val hx; simpa using this
      obtain ⟨j, hj⟩ := (memA x.1).1 x.2
      have h1 := hred2 j x.1 hj hx'
      refine Subtype.ext ?_
      have h2 := hunip (Additive.toMul x.1) ((htors I _).1 h1)
      rw [hsubit, h2]; rfl)
  have hfix : ∀ (j : ℕ) (x : 𝟙_ (Over (Sp k)) ⟶ G), (∀ a ∈ I ^ j, x ≫ act.act a = 1) → x ≫ α = x := by
    intro j x hx
    have h := congrArg Subtype.val (key ⟨Additive.ofMul x, j, (htors _ x).2 hx⟩)
    exact congrArg Additive.toMul h
  have hγ : IsMonHom (α * (𝟙 G)⁻¹) := by
    rw [Hom.mul_def, Hom.inv_def]; infer_instance
  have hI1 : I ≠ ⊤ := fun h => by
    rw [h, Ideal.absNorm_top] at hI
    exact hg.one_lt.ne hI
  have h1 := GlobalTheory.T.eq_one_of_kills_idealPowerTorsion_semiAbelian E k G act (α * (𝟙 G)⁻¹) I hG hγ
    (fun a => by
      rw [MonObj.comp_mul, GrpObj.comp_inv, MonObj.mul_comp, GrpObj.inv_comp, hcomm, Category.comp_id,
        Category.id_comp])
    hI1
    (fun j x hx => by rw [MonObj.comp_mul, GrpObj.comp_inv, hfix j x hx, Category.comp_id, mul_inv_cancel])
  rw [mul_inv_eq_one] at h1
  exact h1

end GlobalTheory.NeatUnip
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallTorsionSetForEndomorphismStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_small_torsion_set_for_endomorphism : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G] (act : OAct (𝓞 E) G) (α : G ⟶ G) (n m g r : ℕ) (I : Ideal (𝓞 E)), IsSemiAbelian G → IsMonHom α → (∀ a, act.act a ≫ α = α ≫ act.act a) → 0 < n → (fun f : G ⟶ G => f ≫ α)^[n] (𝟙 G) = 𝟙 G → g.Prime → Ideal.absNorm I = g → (g : 𝓞 E) ∉ I ^ 2 → r + 1 < g → (∃ T : Finset (𝟙_ (Over (Sp k)) ⟶ G), T.card ≤ g ^ r ∧ ∀ x : 𝟙_ (Over (Sp k)) ⟶ G, (∀ a ∈ I, x ≫ act.act a = 1) → x ∈ T) → (∀ x : 𝟙_ (Over (Sp k)) ⟶ G, (∀ a ∈ I, x ≫ act.act a = 1) → (fun z : 𝟙_ (Over (Sp k)) ⟶ G => (z ≫ α) * z⁻¹)^[m] x = 1) → α = 𝟙 G := by
  first | exact @GlobalTheory.NeatUnip.finite_order_unipotent_eq_id | exact GlobalTheory.NeatUnip.finite_order_unipotent_eq_id | (intros; apply GlobalTheory.NeatUnip.finite_order_unipotent_eq_id <;> assumption)
end
