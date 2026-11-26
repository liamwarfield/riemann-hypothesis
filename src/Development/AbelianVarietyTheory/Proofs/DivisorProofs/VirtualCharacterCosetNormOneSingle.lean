module

public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrreducibleOfVirtualCharacterNormOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CliffordSemidirectPrimeIndexIrreducibleCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CliffordSemidirectPrimeIndexIrreducibleCharacter
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem clifford_prime_index : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ),
    (Nat.card Γ).Prime → s ≠ 1 → ∀ χ : G ⋊[φ] Γ → ℂ, IsIrrChar ℂ ℂ χ →
      (∀ δ, χ (inl δ * inr s) = 0) ∨ (IsIrrChar ℂ ℂ (fun g => χ (inl g)) ∧
        ∑ᶠ g, χ (inl g * inr s) * star (χ (inl g * inr s)) = (Nat.card G : ℂ)) := by
  intro G Γ _ _ _ _ φ s hl hs χ hχ
  haveI : Finite (G ⋊[φ] Γ) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  haveI := Fintype.ofFinite (G ⋊[φ] Γ)
  have hH : Nat.card (G ⋊[φ] Γ) = Nat.card G * Nat.card Γ := by
    rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
  have hHne : (Nat.card (G ⋊[φ] Γ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hord : orderOf s = Nat.card Γ := by
    rcases (Nat.dvd_prime hl).1 (orderOf_dvd_natCard s) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hs
    · exact h
  have hgen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    have htop : Subgroup.zpowers s = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord])
    intro t
    rw [htop]
    trivial
  have hl0 : Nat.card Γ ≠ 0 := hl.ne_zero
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (Nat.card Γ : ℂ))) (Nat.card Γ) :=
    Complex.isPrimitiveRoot_exp _ hl0
  obtain ⟨η, hη1, hηs, hF⟩ := GlobalTheory.Shin.CosetFourier.fourier_coset_sums G Γ φ s hgen _ hζ
  set ζ := Complex.exp (2 * Real.pi * Complex.I / (Nat.card Γ : ℂ)) with hζdef
  have hχchar : IsChar ℂ ℂ χ := by
    obtain ⟨n, ρ, -, h⟩ := hχ
    exact ⟨n, ρ, h⟩
  have hVR := virt_mul_comap_conj_ind_linear (G ⋊[φ] Γ)
  have hnorm : ∑ᶠ x, χ x * star (χ x) = (Nat.card (G ⋊[φ] Γ) : ℂ) := by
    obtain ⟨n, ρ, hρ, h⟩ := hχ
    haveI := hρ
    haveI : Invertible (Nat.card (G ⋊[φ] Γ) : ℂ) := invertibleOfNonzero hHne
    have ho := Representation.char_orthonormal ρ ρ
    rw [if_pos ⟨Representation.Equiv.refl ρ⟩] at ho
    have hc : χ = ρ.character := funext fun g => by simpa using h g
    rw [finsum_eq_sum_of_fintype]
    have hst : ∀ x, star (χ x) = χ x⁻¹ := star_virt_eq_inv _ χ (isChar_mem_virt_complex hχchar)
    simp_rw [hst]
    rw [hc]
    exact ((inv_mul_eq_one₀ hHne).1 (by simpa using ho)).symm
  have hηstar : ∀ x, (η x : ℂ) * star (η x : ℂ) = 1 := by
    intro x
    have h := star_virt_eq_inv _ (fun x => (η x : ℂ)) (hVR.2.2.2.2 η) x
    rw [h, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hψchar : ∀ a : ℕ, IsChar ℂ ℂ (fun x => χ x * (η x : ℂ) ^ a) := by
    intro a
    have h := isChar_mul_complex hχchar (isChar_monoidHom_complex (η ^ a))
    convert h using 1
  have hψnorm : ∀ a : ℕ, ∑ᶠ x, (fun x => χ x * (η x : ℂ) ^ a) x * star ((fun x => χ x * (η x : ℂ) ^ a) x) =
      (Nat.card (G ⋊[φ] Γ) : ℂ) := by
    intro a
    rw [← hnorm]
    congr 1
    funext x
    dsimp only
    rw [star_mul, star_pow]
    calc χ x * (η x : ℂ) ^ a * (star (η x : ℂ) ^ a * star (χ x))
        = χ x * star (χ x) * ((η x : ℂ) * star (η x : ℂ)) ^ a := by ring
      _ = χ x * star (χ x) := by rw [hηstar, one_pow, mul_one]
  have hψirr : ∀ a : ℕ, IsIrrChar ℂ ℂ (fun x => χ x * (η x : ℂ) ^ a) := fun a =>
    ((irr_of_norm_one _ _ (isChar_mem_virt_complex (hψchar a)) (hψnorm a)).2 (hψchar a)).1
  by_cases hcase : ∃ a, 0 < a ∧ a < Nat.card Γ ∧ (fun x => χ x * (η x : ℂ) ^ a) = χ
  · left
    obtain ⟨a, ha0, hal, he⟩ := hcase
    intro δ
    have h1 := congrFun he (inl δ * inr s)
    have hv : (η (inl δ * inr s) : ℂ) = ζ := by rw [map_mul, hη1, one_mul, hηs]
    rw [hv] at h1
    have hζa : ζ ^ a ≠ 1 := hζ.pow_ne_one_of_pos_of_lt ha0.ne' hal
    have h2 : χ (inl δ * inr s) * (ζ ^ a - 1) = 0 := by rw [mul_sub, h1, mul_one, sub_self]
    exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 hζa)
  · right
    push_neg at hcase
    have hNa : ∀ a ∈ Finset.range (Nat.card Γ), a ≠ 0 →
        ∑ᶠ x, χ x * star (χ x * (η x : ℂ) ^ a) = 0 := by
      intro a ha ha0
      have hne := hcase a (Nat.pos_of_ne_zero ha0) (Finset.mem_range.1 ha)
      have hp := pair_eq_zero_of_isIrrChar_ne _ χ _ hχ (hψirr a) (Ne.symm hne)
      unfold pair at hp
      have hs0 := (mul_eq_zero.1 hp).resolve_left (inv_ne_zero hHne)
      rw [← hs0]
      congr 1
      funext x
      have h := star_virt_eq_inv _ _ (isChar_mem_virt_complex (hψchar a)) x
      rw [h]
    have hN0 : ∑ᶠ x, χ x * star (χ x * (η x : ℂ) ^ 0) = (Nat.card (G ⋊[φ] Γ) : ℂ) := by
      simpa using hnorm
    have h0mem : 0 ∈ Finset.range (Nat.card Γ) := Finset.mem_range.2 (Nat.pos_of_ne_zero hl0)
    obtain ⟨hA, hB⟩ := hF χ χ
    rw [Finset.sum_eq_single 0 (fun a ha ha0 => hNa a ha ha0) (fun h => absurd h0mem h), hN0, hH] at hA
    rw [Finset.sum_eq_single 0 (fun a ha ha0 => by rw [hNa a ha ha0, mul_zero]) (fun h => absurd h0mem h),
      pow_zero, one_mul, hN0, hH] at hB
    have hlc : (Nat.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hl0
    push_cast at hA hB
    have hSG : ∑ᶠ g, χ (inl g) * star (χ (inl g)) = (Nat.card G : ℂ) :=
      mul_left_cancel₀ hlc (by rw [hA, mul_comm])
    refine ⟨?_, mul_left_cancel₀ hlc (by rw [hB, mul_comm])⟩
    have hrchar : IsChar ℂ ℂ (fun g => χ (inl g)) := by
      obtain ⟨n, ρ, h⟩ := hχchar
      exact ⟨n, ρ.comp SemidirectProduct.inl, fun g => h _⟩
    exact ((irr_of_norm_one G _ (isChar_mem_virt_complex hrchar) hSG).2 hrchar).1

end GlobalTheory.Shin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CliffordSemidirectPrimeIndexIrreducibleCharacterStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.clifford_semidirect_primeIndex_irreducibleCharacter : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ χ : G ⋊[φ] Γ → ℂ, IsIrrChar ℂ ℂ χ → (∀ δ, χ (inl δ * inr s) = 0) ∨ (IsIrrChar ℂ ℂ (fun g => χ (inl g)) ∧ ∑ᶠ g, χ (inl g * inr s) * star (χ (inl g * inr s)) = (Nat.card G : ℂ)) := by
  first | (exact @GlobalTheory.Shin.clifford_prime_index) | (exact GlobalTheory.Shin.clifford_prime_index) | (intros; apply GlobalTheory.Shin.clifford_prime_index <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectCosetPairingEqZeroOrTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectCosetPairingEqZeroOrTwist
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.CliffTwo

def twistRep {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (ν : H →* ℂˣ) : Representation ℂ H V where
  toFun x := ((ν x : ℂˣ) : ℂ) • ρ x
  map_one' := by simp
  map_mul' x y := by rw [map_mul, map_mul, Units.val_mul, smul_mul_smul_comm]

theorem twistRep_apply {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (ν : H →* ℂˣ) (x : H) : twistRep ρ ν x = ((ν x : ℂˣ) : ℂ) • ρ x := rfl

theorem isIrreducible_twistRep {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ H V} (h : ρ.IsIrreducible) (ν : H →* ℂˣ) :
    (twistRep ρ ν).IsIrreducible := by
  let f : Subrepresentation (twistRep ρ ν) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        have := S.toSubmodule.smul_mem (((ν g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
        simpa [twistRep_apply, smul_smul] using this⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv =>
        S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact f.isSimpleOrder_iff.2 h

theorem isIrrChar_mul_char {H : Type} [Group H] {χ : H → ℂ} (hχ : IsIrrChar ℂ ℂ χ) (ν : H →* ℂˣ) :
    IsIrrChar ℂ ℂ (fun x => χ x * ((ν x : ℂˣ) : ℂ)) := by
  obtain ⟨n, ρ, hρ, hc⟩ := hχ
  refine ⟨n, twistRep ρ ν, isIrreducible_twistRep hρ ν, fun g => ?_⟩
  simp only [hc, Representation.character, twistRep_apply, map_smul, smul_eq_mul,
    Algebra.algebraMap_self, RingHom.id_apply]
  ring

end GlobalTheory.CliffTwo


open GlobalTheory.CliffTwo in
theorem GlobalTheory.Shin.coset_pair_eq_zero_or_twist :
    ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ),
    (Nat.card Γ).Prime → s ≠ 1 → ∀ χ χ' : G ⋊[φ] Γ → ℂ, IsIrrChar ℂ ℂ χ → IsIrrChar ℂ ℂ χ' →
    ∑ᶠ g, χ (inl g * inr s) * star (χ' (inl g * inr s)) = 0 ∨
      ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧ ∀ x, χ x = χ' x * (η x : ℂ) := by
  intro G Γ _ _ _ _ φ s hp hs χ χ' hχ hχ'
  haveI : Finite (G ⋊[φ] Γ) := Finite.of_equiv _ (SemidirectProduct.equivProd (φ := φ)).symm
  haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩
  have hgen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    intro t; rw [zpowers_eq_top_of_prime_card rfl hs]; trivial
  have hζ := Complex.isPrimitiveRoot_exp (Nat.card Γ) hp.ne_zero
  obtain ⟨η, hη1, -, hsum⟩ := GlobalTheory.Shin.CosetFourier.fourier_coset_sums G Γ φ s hgen _ hζ
  have hS := (hsum χ χ').2
  by_cases h0 : ∑ᶠ g, χ (inl g * inr s) * star (χ' (inl g * inr s)) = 0
  · exact Or.inl h0
  right
  have hne : ∑ a ∈ Finset.range (Nat.card Γ), Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ)) ^ a *
      ∑ᶠ x, χ x * star (χ' x * (η x : ℂ) ^ a) ≠ 0 := by
    rw [← hS]; exact mul_ne_zero (by exact_mod_cast hp.ne_zero) h0
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hT : ∑ᶠ x, χ x * star (χ' x * (η x : ℂ) ^ a) ≠ 0 := right_ne_zero_of_mul ha
  have hpow : ∀ x, ((η ^ a) x : ℂ) = (η x : ℂ) ^ a := fun x => by simp
  have hψ : IsIrrChar ℂ ℂ (fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) := isIrrChar_mul_char hχ' (η ^ a)
  refine ⟨η ^ a, fun g => by simp [hη1], fun x => ?_⟩
  by_contra hx
  have hne' : χ ≠ fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ) := fun e => hx (congrFun e x)
  have hpair : pair χ (fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) = 0 := by
    first | exact GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne (G ⋊[φ] Γ) χ _ hχ hψ hne' | exact GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne χ _ hχ hψ hne' | exact GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne hχ hψ hne'
  have hvirt : (fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) ∈ Virt ℂ ℂ (G ⋊[φ] Γ) := by
    obtain ⟨n, ρ, -, hc⟩ := hψ
    exact AddSubgroup.subset_closure ⟨n, ρ, hc⟩
  have hstar : ∀ g, star ((fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) g) = (fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) g⁻¹ := by
    first | exact GlobalTheory.CuspGL.star_virt_eq_inv (G ⋊[φ] Γ) _ hvirt | exact GlobalTheory.CuspGL.star_virt_eq_inv _ hvirt | exact GlobalTheory.CuspGL.star_virt_eq_inv hvirt
  apply hT
  have hcard : (Nat.card (G ⋊[φ] Γ) : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have : ∑ᶠ x, χ x * star (χ' x * (η x : ℂ) ^ a) =
      ∑ᶠ x, χ x * (fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) x⁻¹ := by
    congr 1; ext x; have hx := hstar x; simp only [hpow] at hx ⊢; rw [← hx]
  rw [this]
  unfold pair at hpair
  exact (mul_eq_zero.1 hpair).resolve_left (inv_ne_zero hcard)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectCosetPairingEqZeroOrTwistStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semidirect_coset_pairing_eq_zero_or_twist : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ χ χ' : G ⋊[φ] Γ → ℂ, IsIrrChar ℂ ℂ χ → IsIrrChar ℂ ℂ χ' → ∑ᶠ g, χ (inl g * inr s) * star (χ' (inl g * inr s)) = 0 ∨ ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧ ∀ x, χ x = χ' x * (η x : ℂ) := by
  first | (exact @GlobalTheory.Shin.coset_pair_eq_zero_or_twist) | (exact GlobalTheory.Shin.coset_pair_eq_zero_or_twist) | (intros; apply GlobalTheory.Shin.coset_pair_eq_zero_or_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CyclotomicSumNormSqEqOneSingleNonzero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CyclotomicSumNormSqEqOneSingleNonzero
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory

theorem cycloSq_mod_eq_zero_iff {l a b : ℕ} (hl : 0 < l) (ha : a < l) (hb : b < l) :
    (a + (l - 1) * b) % l = 0 ↔ b = a := by
  rw [← Nat.dvd_iff_mod_eq_zero]
  constructor
  · intro h
    have h2 : (l : ℤ) ∣ ((a + (l - 1) * b : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h
    have h3 : ((a + (l - 1) * b : ℕ) : ℤ) = ((a : ℤ) - b) + l * b := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ l)]; ring
    rw [h3] at h2
    have h' : (l : ℤ) ∣ (a : ℤ) - b := (dvd_add_left (dvd_mul_right _ _)).mp h2
    have := Int.eq_zero_of_abs_lt_dvd h' (by rw [abs_lt]; constructor <;> omega)
    omega
  · rintro rfl
    obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    exact ⟨b, by simp; ring⟩

theorem cycloSq_coeff_eq {l : ℕ} (hl : l.Prime) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ l) (a : ℕ → ℤ)
    (h : ∑ d ∈ Finset.range l, (a d : ℂ) * ζ ^ d = 0) : ∀ d < l, a d = a (l - 1) := by
  have hl1 : 1 < l := hl.one_lt
  have hgeom : ∑ d ∈ Finset.range l, ζ ^ d = 0 := hζ.geom_sum_eq_zero hl1
  set Q : ℚ[X] := ∑ d ∈ Finset.range (l - 1), C (((a d - a (l - 1) : ℤ)) : ℚ) * X ^ d with hQdef
  have hQ : aeval ζ Q = 0 := by
    have h1 : ∑ d ∈ Finset.range l, (((a d - a (l - 1) : ℤ)) : ℂ) * ζ ^ d = 0 := by
      simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib, h, ← Finset.mul_sum, hgeom,
        mul_zero, sub_zero]
    have hl' : l = (l - 1) + 1 := by omega
    rw [hl', Finset.sum_range_succ] at h1
    simp only [Nat.add_sub_cancel, sub_self, Int.cast_zero, zero_mul, add_zero] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hQdef, map_sum]
    simpa using h1
  have hdvd : minpoly ℚ ζ ∣ Q := minpoly.dvd ℚ ζ hQ
  have hdeg : (minpoly ℚ ζ).natDegree = l - 1 := by
    rw [← cyclotomic_eq_minpoly_rat hζ hl.pos, natDegree_cyclotomic, Nat.totient_prime hl]
  have hQ0 : Q = 0 := by
    by_contra hne
    have h1 := natDegree_le_of_dvd hdvd hne
    have h2 : Q.natDegree ≤ l - 2 := natDegree_sum_le_of_forall_le _ _ (fun d hd =>
      (natDegree_C_mul_X_pow_le _ _).trans (by rw [Finset.mem_range] at hd; omega))
    omega
  intro d hd
  by_cases hd' : d = l - 1
  · rw [hd']
  have h1 : Q.coeff d = 0 := by rw [hQ0]; simp
  rw [hQdef, finsetSum_coeff] at h1
  simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range] at h1
  rw [if_pos (by omega)] at h1
  have : ((a d - a (l - 1) : ℤ) : ℚ) = 0 := h1
  exact_mod_cast sub_eq_zero.mp (by exact_mod_cast this)

end GlobalTheory

namespace GlobalTheory

def cycloSqCoeff (l : ℕ) (f : ℕ → ℤ) (d : ℕ) : ℤ :=
  ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l,
    if (a + (l - 1) * b) % l = d then f a * f b else 0

theorem cycloSq_mul_star {l : ℕ} (hl : 0 < l) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ l) (f : ℕ → ℤ) :
    (∑ a ∈ Finset.range l, (f a : ℂ) * ζ ^ a) * star (∑ a ∈ Finset.range l, (f a : ℂ) * ζ ^ a)
      = ∑ d ∈ Finset.range l, (cycloSqCoeff l f d : ℂ) * ζ ^ d := by
  have hnorm : ‖ζ‖ = 1 := hζ.norm'_eq_one hl.ne'
  have hinv : ζ⁻¹ = ζ ^ (l - 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel hl, hζ.pow_eq_one]
  have hstar : star ζ = ζ ^ (l - 1) := by
    rw [← hinv, Complex.inv_eq_conj hnorm]; rfl
  have hpow : ∀ m, ζ ^ m = ζ ^ (m % l) := by
    intro m
    conv_lhs => rw [← Nat.div_add_mod m l]
    rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  rw [star_sum, Finset.sum_mul_sum]
  calc ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l, (f a : ℂ) * ζ ^ a * star ((f b : ℂ) * ζ ^ b)
      = ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l,
          ((f a * f b : ℤ) : ℂ) * ζ ^ ((a + (l - 1) * b) % l) := by
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
        rw [← hpow, star_mul', star_pow, hstar, star_intCast, pow_add, pow_mul]
        push_cast; ring
    _ = ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l, ∑ d ∈ Finset.range l,
          (if (a + (l - 1) * b) % l = d then ((f a * f b : ℤ) : ℂ) * ζ ^ d else 0) := by
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (Nat.mod_lt _ hl))]
    _ = ∑ d ∈ Finset.range l, ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l,
          (if (a + (l - 1) * b) % l = d then ((f a * f b : ℤ) : ℂ) * ζ ^ d else 0) := by
        exact (Finset.sum_congr rfl (fun a _ => Finset.sum_comm)).trans Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        simp only [cycloSqCoeff, Int.cast_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
        split_ifs <;> simp

theorem cycloSq_sum_coeff {l : ℕ} (hl : 0 < l) (f : ℕ → ℤ) :
    ∑ d ∈ Finset.range l, cycloSqCoeff l f d
      = ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l, f a * f b := by
  simp only [cycloSqCoeff]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (Nat.mod_lt _ hl))]

theorem cycloSq_coeff_zero {l : ℕ} (hl : 0 < l) (f : ℕ → ℤ) :
    cycloSqCoeff l f 0 = ∑ a ∈ Finset.range l, f a ^ 2 := by
  simp only [cycloSqCoeff]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.mem_range] at ha
  rw [Finset.sum_congr rfl (g := fun b => if b = a then f a * f b else 0) (fun b hb => by
    simp only [cycloSq_mod_eq_zero_iff hl ha (Finset.mem_range.mp hb)])]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr ha), sq]

theorem cycloSq_two_mul {l : ℕ} (f : ℕ → ℤ) :
    ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l, (f a - f b) ^ 2
      = 2 * ((l : ℤ) * ∑ a ∈ Finset.range l, f a ^ 2
          - ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l, f a * f b) := by
  have : ∀ a b : ℕ, (f a - f b) ^ 2 = f a ^ 2 + f b ^ 2 - 2 * (f a * f b) := fun a b => by ring
  simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
  ring

theorem cycloSq_le_of_ne_zero {l : ℕ} (hl : 1 < l) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ l)
    (f : ℕ → ℤ) (hc : ∑ a ∈ Finset.range l, (f a : ℂ) * ζ ^ a ≠ 0) :
    (l : ℤ) ≤ ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l, (f a - f b) ^ 2 := by
  have hne : ∃ x ∈ Finset.range l, f x ≠ f 0 := by
    by_contra hall
    push_neg at hall
    apply hc
    rw [Finset.sum_congr rfl (fun a ha => by rw [hall a ha]), ← Finset.mul_sum,
      hζ.geom_sum_eq_zero hl, mul_zero]
  obtain ⟨x, hx, hfx⟩ := hne
  have h0 : 0 ∈ Finset.range l := Finset.mem_range.mpr (by omega)
  have hx0 : x ≠ 0 := by rintro rfl; exact hfx rfl
  have hR : ∀ a ∈ Finset.range l, 0 ≤ ∑ b ∈ Finset.range l, (f a - f b) ^ 2 :=
    fun a _ => Finset.sum_nonneg (fun b _ => sq_nonneg _)
  have hsum := Finset.add_le_sum hR hx h0 hx0
  have hxy : (l : ℤ) ≤ ∑ b ∈ Finset.range l, (f x - f b) ^ 2
      + ∑ b ∈ Finset.range l, (f 0 - f b) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    calc (l : ℤ) = ∑ b ∈ Finset.range l, (1 : ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun b _ => by
        have h1 := sq_nonneg (f x - f b)
        have h2 := sq_nonneg (f 0 - f b)
        by_cases h : f x = f b
        · have : f 0 - f b ≠ 0 := by omega
          rcases lt_or_gt_of_ne this with h3 | h3 <;> nlinarith
        · have : f x - f b ≠ 0 := by omega
          rcases lt_or_gt_of_ne this with h3 | h3 <;> nlinarith)
  linarith

end GlobalTheory

namespace GlobalTheory

theorem cyclo_sum_mul_star_eq_one_single : ∀ (l : ℕ) (ζ : ℂ), l.Prime → IsPrimitiveRoot ζ l →
    ∀ (I : Type) (S : Finset I) (n : I → ℕ → ℤ),
      ∑ i ∈ S, (∑ a ∈ Finset.range l, (n i a : ℂ) * ζ ^ a) *
          star (∑ a ∈ Finset.range l, (n i a : ℂ) * ζ ^ a) = 1 →
      ∃ i₀ ∈ S, ∀ i ∈ S, i ≠ i₀ → ∑ a ∈ Finset.range l, (n i a : ℂ) * ζ ^ a = 0 := by
  intro l ζ hl hζ I S n hsum
  have hl0 : 0 < l := hl.pos
  have hl1 : 1 < l := hl.one_lt
  set N : ℕ → ℤ := fun d => ∑ i ∈ S, cycloSqCoeff l (n i) d with hN
  have hT : ∑ d ∈ Finset.range l, (N d : ℂ) * ζ ^ d = 1 := by
    rw [← hsum, Finset.sum_congr rfl (fun i _ => cycloSq_mul_star hl0 hζ (n i))]
    simp only [hN, Int.cast_sum, Finset.sum_mul]
    exact Finset.sum_comm
  set A : ℕ → ℤ := fun d => N d - if d = 0 then 1 else 0 with hAdef
  have hA : ∑ d ∈ Finset.range l, (A d : ℂ) * ζ ^ d = 0 := by
    simp only [hAdef, Int.cast_sub, sub_mul, Finset.sum_sub_distrib, hT]
    simp [hl0]
  have hAeq := cycloSq_coeff_eq hl hζ A hA
  have hNd : ∀ d ∈ (Finset.range l).erase 0, N d = N 0 - 1 := by
    intro d hd
    rw [Finset.mem_erase, Finset.mem_range] at hd
    have h3 : A d = A 0 := (hAeq d hd.2).trans (hAeq 0 hl0).symm
    simp only [hAdef, if_neg hd.1, if_true, sub_zero] at h3
    linarith
  have h0mem : 0 ∈ Finset.range l := Finset.mem_range.mpr hl0
  have hsumN : ∑ d ∈ Finset.range l, N d = N 0 + ((l : ℤ) - 1) * (N 0 - 1) := by
    rw [← Finset.add_sum_erase _ _ h0mem, Finset.sum_congr rfl hNd, Finset.sum_const,
      Finset.card_erase_of_mem h0mem, Finset.card_range, nsmul_eq_mul,
      Nat.cast_sub (by omega : 1 ≤ l)]
    push_cast; ring
  have hsumN' : ∑ d ∈ Finset.range l, N d
      = ∑ i ∈ S, ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l, n i a * n i b := by
    simp only [hN]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => cycloSq_sum_coeff hl0 (n i))
  have hN0 : N 0 = ∑ i ∈ S, ∑ a ∈ Finset.range l, n i a ^ 2 :=
    Finset.sum_congr rfl (fun i _ => cycloSq_coeff_zero hl0 (n i))
  have hQsum : ∑ i ∈ S, ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l, (n i a - n i b) ^ 2
      = 2 * ((l : ℤ) - 1) := by
    rw [Finset.sum_congr rfl (fun i _ => cycloSq_two_mul (n i)), ← Finset.mul_sum,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← hN0, ← hsumN', hsumN]
    ring
  have hQnn : ∀ i ∈ S, 0 ≤ ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l, (n i a - n i b) ^ 2 :=
    fun i _ => Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => sq_nonneg _))
  obtain ⟨i₀, hi₀, hc₀⟩ : ∃ i₀ ∈ S, ∑ a ∈ Finset.range l, (n i₀ a : ℂ) * ζ ^ a ≠ 0 := by
    by_contra H
    push_neg at H
    rw [Finset.sum_eq_zero (fun i hi => by rw [H i hi, zero_mul])] at hsum
    exact zero_ne_one hsum
  refine ⟨i₀, hi₀, fun i hi hne => ?_⟩
  by_contra hci
  have h1 := cycloSq_le_of_ne_zero hl1 hζ (n i) hci
  have h2 := cycloSq_le_of_ne_zero hl1 hζ (n i₀) hc₀
  have h3 := Finset.add_le_sum hQnn hi hi₀ hne
  linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CyclotomicSumNormSqEqOneSingleNonzeroStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomic_sum_normSq_eq_one_single_nonzero : ∀ (l : ℕ) (ζ : ℂ), l.Prime → IsPrimitiveRoot ζ l → ∀ (I : Type) (S : Finset I) (n : I → ℕ → ℤ), ∑ i ∈ S, (∑ a ∈ Finset.range l, (n i a : ℂ) * ζ ^ a) * star (∑ a ∈ Finset.range l, (n i a : ℂ) * ζ ^ a) = 1 → ∃ i₀ ∈ S, ∀ i ∈ S, i ≠ i₀ → ∑ a ∈ Finset.range l, (n i a : ℂ) * ζ ^ a = 0 := by
  first | (exact @GlobalTheory.cyclo_sum_mul_star_eq_one_single) | (exact GlobalTheory.cyclo_sum_mul_star_eq_one_single) | (intros; apply GlobalTheory.cyclo_sum_mul_star_eq_one_single <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VirtualCharacterCosetNormOneSingle
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem int_comb_unit_norm_single {ι G : Type} [Fintype ι] [Fintype G] (l : ℕ) (hl : l.Prime)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ l) (f : ι → G → ℂ) (c : ι → ℤ) (R : ι → ι → Prop)
    (hR : Equivalence R) (hG : (Fintype.card G : ℂ) ≠ 0)
    (hnorm : ∀ i, ∑ g, f i g * star (f i g) = Fintype.card G)
    (horth : ∀ i j, ∑ g, f i g * star (f j g) ≠ 0 → R i j)
    (hrel : ∀ i j, R i j → ∃ a < l, ∀ g, f i g = ζ ^ a * f j g)
    (hsum : ∑ g, (∑ i, (c i : ℂ) * f i g) * star (∑ i, (c i : ℂ) * f i g) = Fintype.card G) :
    ∃ i₀ e, ∀ g, ∑ i, (c i : ℂ) * f i g = e * f i₀ g := by
  letI S : Setoid ι := ⟨R, hR⟩
  let rep : Quotient S → ι := Quotient.out
  have hrep : ∀ t : ι, R t (rep ⟦t⟧) := fun t => hR.symm (Quotient.mk_out t)
  choose a ha hfa using fun t => hrel t _ (hrep t)
  let n : Quotient S → ℕ → ℤ := fun i b => ∑ t, if (⟦t⟧ : Quotient S) = i ∧ a t = b then c t else 0
  let C : Quotient S → ℂ := fun i => ∑ b ∈ Finset.range l, (n i b : ℂ) * ζ ^ b
  have hF : ∀ g, ∑ t, (c t : ℂ) * f t g = ∑ i, C i * f (rep i) g := by
    intro g
    have h1 : ∀ i, C i * f (rep i) g =
        ∑ t, if (⟦t⟧ : Quotient S) = i then (c t : ℂ) * (ζ ^ a t * f (rep i) g) else 0 := by
      intro i
      simp only [C, n, Int.cast_sum, Int.cast_ite, Int.cast_zero, Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases h : (⟦t⟧ : Quotient S) = i
      · simp only [h, true_and, if_true]
        rw [Finset.sum_ite_eq]
        simp only [Finset.mem_range, ha t, if_true]
        ring
      · simp [h]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_ite_eq]
    simp [hfa t g]
  have hort : ∀ i j, i ≠ j → ∑ g, f (rep i) g * star (f (rep j) g) = 0 := by
    intro i j hij
    by_contra h
    apply hij
    rw [← Quotient.out_eq i, ← Quotient.out_eq j]
    exact Quotient.sound (horth _ _ h)
  have hexp : ∀ g, (∑ i, C i * f (rep i) g) * star (∑ i, C i * f (rep i) g) =
      ∑ i, ∑ j, C i * star (C j) * (f (rep i) g * star (f (rep j) g)) := by
    intro g
    rw [star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul']
    ring
  have h2 : ∑ g, (∑ i, C i * f (rep i) g) * star (∑ i, C i * f (rep i) g) =
      (∑ i, C i * star (C i)) * Fintype.card G := by
    simp_rw [hexp]
    rw [Finset.sum_comm]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm, Finset.sum_eq_single i]
    · rw [← Finset.mul_sum, hnorm]
    · intro j _ hji
      rw [← Finset.mul_sum, hort i j (Ne.symm hji), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  simp_rw [hF] at hsum
  rw [h2] at hsum
  have h3 : ∑ i, C i * star (C i) = 1 := by
    have := hsum
    rw [← one_mul (Fintype.card G : ℂ)] at this
    exact mul_right_cancel₀ hG (by simpa using this)
  obtain ⟨i₀, -, hi₀⟩ := GlobalTheory.T.cyclotomic_sum_normSq_eq_one_single_nonzero l ζ hl hζ (Quotient S) Finset.univ n h3
  refine ⟨rep i₀, C i₀, fun g => ?_⟩
  rw [hF, Finset.sum_eq_single i₀]
  · intro i _ hi
    have : C i = 0 := hi₀ i (Finset.mem_univ i) hi
    rw [this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i₀) h

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem virt_coset_norm_one_single : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ]
    (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ),
    ∑ᶠ g, X (inl g * inr s) * star (X (inl g * inr s)) = (Nat.card G : ℂ) →
    ∃ (χ : G ⋊[φ] Γ → ℂ) (e : ℂ), IsIrrChar ℂ ℂ χ ∧ IsIrrChar ℂ ℂ (fun g => χ (inl g)) ∧
      ∀ δ, X (inl δ * inr s) = e * χ (inl δ * inr s) := by
  intro G Γ _ _ _ _ φ s hp hs X hX hXn
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Finite (G ⋊[φ] Γ) :=
    Finite.of_injective (fun x : G ⋊[φ] Γ => (x.left, x.right))
      (fun x y h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  obtain ⟨c, hirr, hXc, -⟩ := GlobalTheory.BI.virt_expand (G ⋊[φ] Γ) X hX
  let T := c.support.filter (fun χ : G ⋊[φ] Γ → ℂ => ¬ ∀ δ, χ (inl δ * inr s) = 0)
  have hT : ∀ t : T, IsIrrChar ℂ ℂ t.1 ∧ ¬ ∀ δ, t.1 (inl δ * inr s) = 0 := fun t =>
    ⟨hirr _ (Finset.mem_filter.1 t.2).1, (Finset.mem_filter.1 t.2).2⟩
  let f : T → G → ℂ := fun t g => t.1 (inl g * inr s)
  have hX' : ∀ g, X (inl g * inr s) = ∑ t : T, (c t.1 : ℂ) * f t g := by
    intro g
    rw [hXc, Finsupp.sum, Finset.sum_apply]
    simp only [Pi.smul_apply, zsmul_eq_mul]
    rw [Finset.sum_coe_sort T (fun χ => (c χ : ℂ) * χ (inl g * inr s))]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun χ _ => ?_
    split_ifs with h
    · rw [h g, mul_zero]
    · rfl
  let R : T → T → Prop := fun t u => ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧
    ∀ x, t.1 x = u.1 x * (η x : ℂ)
  have hR : Equivalence R := by
    refine ⟨fun t => ⟨1, fun g => rfl, fun x => by simp⟩, ?_, ?_⟩
    · rintro t u ⟨η, h1, h2⟩
      refine ⟨η⁻¹, fun g => by simp [h1 g], fun x => ?_⟩
      rw [h2 x, MonoidHom.inv_apply, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        mul_one]
    · rintro t u v ⟨η, h1, h2⟩ ⟨η', h1', h2'⟩
      refine ⟨η' * η, fun g => by simp [h1 g, h1' g], fun x => ?_⟩
      rw [h2 x, h2' x, MonoidHom.mul_apply, Units.val_mul, mul_assoc]
  haveI : NeZero (Nat.card Γ) := ⟨hp.ne_zero⟩
  have hζ := Complex.isPrimitiveRoot_exp (Nat.card Γ) hp.ne_zero
  have hnorm : ∀ t, ∑ g, f t g * star (f t g) = Fintype.card G := by
    intro t
    rcases GlobalTheory.T.clifford_semidirect_primeIndex_irreducibleCharacter G Γ φ s hp hs t.1 (hT t).1 with h | ⟨-, h⟩
    · exact absurd h (hT t).2
    · rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card] at h
      exact h
  have horth : ∀ t u, ∑ g, f t g * star (f u g) ≠ 0 → R t u := by
    intro t u h
    rcases GlobalTheory.T.semidirect_coset_pairing_eq_zero_or_twist G Γ φ s hp hs t.1 u.1 (hT t).1 (hT u).1 with h' | h'
    · rw [finsum_eq_sum_of_fintype] at h'
      exact absurd h' h
    · exact h'
  have hrel : ∀ t u, R t u → ∃ a < Nat.card Γ, ∀ g,
      f t g = Complex.exp (2 * Real.pi * Complex.I / (Nat.card Γ : ℂ)) ^ a * f u g := by
    rintro t u ⟨η, h1, h2⟩
    have hpow : ((η (inr s) : ℂˣ) : ℂ) ^ Nat.card Γ = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow, pow_card_eq_one', map_one, map_one,
        Units.val_one]
    obtain ⟨a, ha, hb⟩ := hζ.eq_pow_of_pow_eq_one hpow
    refine ⟨a, ha, fun g => ?_⟩
    simp only [f]
    rw [h2, map_mul, h1, one_mul, hb, mul_comm]
  have hsum : ∑ g, (∑ t : T, (c t.1 : ℂ) * f t g) * star (∑ t : T, (c t.1 : ℂ) * f t g) =
      Fintype.card G := by
    rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card] at hXn
    simp_rw [← hX']
    exact hXn
  obtain ⟨t₀, e, he⟩ := int_comb_unit_norm_single (Nat.card Γ) hp _ hζ f (fun t => c t.1) R hR
    (Nat.cast_ne_zero.2 Fintype.card_ne_zero) hnorm horth hrel hsum
  refine ⟨t₀.1, e, (hT t₀).1, ?_, fun δ => by rw [hX', he]⟩
  rcases GlobalTheory.T.clifford_semidirect_primeIndex_irreducibleCharacter G Γ φ s hp hs t₀.1 (hT t₀).1 with h | ⟨h, -⟩
  · exact absurd h (hT t₀).2
  · exact h

end GlobalTheory.Shin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VirtualCharacterCosetNormOneSingleStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.virtualCharacter_coset_normOne_single : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∑ᶠ g, X (inl g * inr s) * star (X (inl g * inr s)) = (Nat.card G : ℂ) → ∃ (χ : G ⋊[φ] Γ → ℂ) (e : ℂ), IsIrrChar ℂ ℂ χ ∧ IsIrrChar ℂ ℂ (fun g => χ (inl g)) ∧ ∀ δ, X (inl δ * inr s) = e * χ (inl δ * inr s) := by
  first | (exact @GlobalTheory.Shin.virt_coset_norm_one_single) | (exact GlobalTheory.Shin.virt_coset_norm_one_single) | (intros; apply GlobalTheory.Shin.virt_coset_norm_one_single <;> assumption)
end
