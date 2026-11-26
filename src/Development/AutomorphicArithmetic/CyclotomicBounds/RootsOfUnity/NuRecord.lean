module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.HostCls
public import Development.AutomorphicArithmetic.PrimeDiscriminants.ExistsPrimitiveRootTorsionOrder
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.TotientLeOfCycPowEqOne
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.CycGrp

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.NuSumApprox
namespace KStar.Tree

variable (l : ℕ) [Fact l.Prime]

private theorem nsa_isUnit {c : ℤ_[l]} (hc : ¬ (l : ℤ_[l]) ∣ c) : IsUnit c := by
  by_contra hu
  have : c ∈ IsLocalRing.maximalIdeal ℤ_[l] := hu
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
  exact hc this

private theorem nsa_dvd_iff (x : ℤ_[l]) : (l : ℤ_[l]) ∣ x ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

private theorem nsa_nat (k : ℕ) (m : ℕ) (h : (l : ℤ_[l]) ^ k ∣ (m : ℤ_[l])) : l ^ k ∣ m := by
  have := (PadicInt.pow_p_dvd_int_iff (p := l) k (m : ℤ)).1 (by simpa using h)
  exact_mod_cast this

private theorem nsa_lte (s n : ℕ) (hs : s ≠ 0) (hn : Odd n) :
    ¬ (l : ℤ) ^ (s + n.factorization l + 1) ∣ (1 + (l : ℤ) ^ s) ^ n - 1 := by
  have hp : l.Prime := Fact.out
  have hpz : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hxy : (l : ℤ) ∣ (1 + (l : ℤ) ^ s) - 1 := by
    simpa using dvd_pow_self (l : ℤ) hs
  have hx : ¬ (l : ℤ) ∣ 1 + (l : ℤ) ^ s := by
    intro h
    exact hpz.not_dvd_one ((dvd_add_left (dvd_pow_self (l : ℤ) hs)).1 h)
  have hs' : emultiplicity (l : ℤ) ((1 + (l : ℤ) ^ s) - 1) = s := by
    rw [add_sub_cancel_left]
    exact emultiplicity_pow_self_of_prime hpz s
  have key : emultiplicity (l : ℤ) ((1 + (l : ℤ) ^ s) ^ n - 1 ^ n) =
      ((s + n.factorization l : ℕ) : ℕ∞) := by
    by_cases hl : l = 2
    · have hnd : ¬ l ∣ n := by
        subst hl
        exact hn.not_two_dvd_nat
      rw [emultiplicity_pow_sub_pow_of_prime hpz hxy hx (by exact_mod_cast hnd), hs',
        Nat.factorization_eq_zero_of_not_dvd hnd, add_zero]
    · rw [Int.emultiplicity_pow_sub_pow hp (hp.odd_of_ne_two hl) hxy hx n, hs',
        Nat.factorization_def n hp, Nat.cast_add, padicValNat_eq_emultiplicity hn0]
  rw [one_pow] at key
  intro h
  have := le_emultiplicity_of_pow_dvd h
  rw [key] at this
  have := Nat.cast_le.1 this
  omega

theorem nuOf_le_of_approx {Γ : Type} [Group Γ] (ε : Γ →* ℤ_[l]ˣ) (n m : ℕ) (u : ℤ_[l]ˣ)
    (h : ∀ k : ℕ, ∃ g, (l : ℤ_[l]) ^ k ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) - u)
    (hu : ¬ (l : ℤ_[l]) ^ (m + 1) ∣ (u : ℤ_[l]) ^ n - 1) : nuOf l ε n ≤ m := by
  obtain ⟨g, hg⟩ := h (m + 1)
  refine Nat.sInf_le ⟨g, fun hc => hu ?_⟩
  have h2 := hg.trans (sub_dvd_pow_sub_pow ((ε g : ℤ_[l]ˣ) : ℤ_[l]) (u : ℤ_[l]) n)
  have h3 := dvd_sub hc h2
  convert h3 using 1
  ring

theorem exists_unit_not_dvd (C n : ℕ) (hC : C ≠ 0) (h2 : 2 ∣ C) (hn : Odd n) :
    ∃ u : ℤ_[l]ˣ, (l : ℤ_[l]) ^ C.factorization l ∣ (u : ℤ_[l]) - 1 ∧
      ¬ (l : ℤ_[l]) ^ (C.factorization l + (if l ∣ C then n.factorization l else 0) + 1) ∣ (u : ℤ_[l]) ^ n - 1 := by
  have hp : l.Prime := Fact.out
  by_cases hlC : l ∣ C
  · rw [if_pos hlC]
    have hs : C.factorization l ≠ 0 := (hp.factorization_pos_of_dvd hC hlC).ne'
    generalize C.factorization l = s at hs ⊢
    have hU : IsUnit (1 + (l : ℤ_[l]) ^ s) := by
      apply nsa_isUnit
      intro h
      exact PadicInt.prime_p.not_dvd_one ((dvd_add_left (dvd_pow_self (l : ℤ_[l]) hs)).1 h)
    refine ⟨hU.unit, by simp, fun h => nsa_lte l s n hs hn ?_⟩
    rw [← PadicInt.pow_p_dvd_int_iff]
    simpa using h
  · rw [if_neg hlC, Nat.factorization_eq_zero_of_not_dvd hlC]
    refine ⟨-1, by simp, fun h => hlC ?_⟩
    have e : ((-1 : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 = -((2 : ℕ) : ℤ_[l]) := by
      simp only [Units.val_neg, Units.val_one, hn.neg_one_pow]
      push_cast
      ring
    rw [e, dvd_neg] at h
    have := nsa_nat l _ _ h
    simp only [add_zero, zero_add, pow_one] at this
    exact this.trans h2

theorem exists_sq_unit_not_dvd (n : ℕ) (hn : ¬ (l - 1) / 2 ∣ n) (hl : l ≠ 2) :
    ∃ u : ℤ_[l]ˣ, ¬ (l : ℤ_[l]) ^ (0 + 1) ∣ ((u ^ 2 : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 := by
  have hp : l.Prime := Fact.out
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod l)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hg
  have hx : PadicInt.toZMod ((((g : ZMod l).val : ℕ)) : ℤ_[l]) = (g : ZMod l) := by
    rw [map_natCast, ZMod.natCast_zmod_val]
  have hU : IsUnit ((((g : ZMod l).val : ℕ)) : ℤ_[l]) := by
    apply nsa_isUnit
    rw [nsa_dvd_iff, hx]
    exact g.ne_zero
  refine ⟨hU.unit, fun h => hn ?_⟩
  rw [zero_add, pow_one, nsa_dvd_iff, map_sub, map_one, map_pow, Units.val_pow_eq_pow_val, map_pow,
    IsUnit.unit_spec, hx, sub_eq_zero, ← pow_mul] at h
  have h1 : g ^ (2 * n) = 1 := by
    apply Units.ext
    simpa using h
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hg] at h2
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hl
  have e1 : l - 1 = 2 * k := by omega
  rw [e1] at h2 ⊢
  rw [Nat.mul_div_cancel_left k two_pos]
  exact Nat.dvd_of_mul_dvd_mul_left two_pos h2

end KStar.Tree
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.HostApprox
section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.AutApprox
open NumberField KStar.Tree

private theorem UpperTheory.Mu.exists_aut_pow (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (M : ℕ) (hM : M ≠ 0)
    (a : ℕ) (ha : a.Coprime M) : ∃ σ : Ω ≃ₐ[ℚ] Ω, ∀ t : Ω, t ^ M = 1 → σ t = t ^ a := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero M := ⟨hM⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have hξ' : IsPrimitiveRoot (ξ ^ a) M := hξ.pow_of_coprime a ha
  have hpos : 0 < M := Nat.pos_of_ne_zero hM
  have hc : IsConjRoot ℚ (ξ ^ a) ξ := by
    unfold IsConjRoot
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hξ hpos, ← Polynomial.cyclotomic_eq_minpoly_rat hξ' hpos]
  obtain ⟨σ, hσ⟩ := hc.exists_algEquiv
  refine ⟨σ, fun t ht => ?_⟩
  obtain ⟨i, -, rfl⟩ := hξ.eq_pow_of_pow_eq_one ht
  rw [map_pow, hσ, ← pow_mul, ← pow_mul, mul_comm]

private theorem UpperTheory.Mu.dvd_sub_iff (l : ℕ) [Fact l.Prime] (r : ℕ) (x y : ℤ_[l]) :
    (l : ℤ_[l]) ^ r ∣ x - y ↔ PadicInt.toZModPow r x = PadicInt.toZModPow r y := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero]

theorem UpperTheory.Mu.autApprox :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ), N ≠ 0 → ∀ (ζ : Ω), IsPrimitiveRoot ζ N → ∀ (v : (ZMod N)ˣ) (u : ℤ_[l]ˣ), (l : ℤ_[l]) ^ N.factorization l ∣ (u : ℤ_[l]) - (((v : ZMod N).val : ℕ) : ℤ_[l]) → ∀ k : ℕ, ∃ σ : Ω ≃ₐ[ℚ] Ω, σ ζ = ζ ^ (v : ZMod N).val ∧ (l : ℤ_[l]) ^ k ∣ ((cyc l ℚ Ω σ : ℤ_[l]ˣ) : ℤ_[l]) - u := by
  intro l hl Ω _ _ _ N hN ζ hζ v u huv k
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hp : l.Prime := hl.out
  set s := N.factorization l with hs
  set N' := N / l ^ s with hN'
  have hNN : l ^ s * N' = N := Nat.ordProj_mul_ordCompl_eq_self N l
  have hcop : Nat.Coprime l N' := Nat.coprime_ordCompl hp hN
  have hcP : Nat.Coprime N' (l ^ (s + k)) := hcop.symm.pow_right _
  have hN'0 : N' ≠ 0 := by
    intro h
    rw [h, mul_zero] at hNN
    exact hN hNN.symm
  have hP0 : l ^ (s + k) ≠ 0 := pow_ne_zero _ hp.ne_zero
  haveI : NeZero (l ^ (s + k)) := ⟨hP0⟩
  obtain ⟨a, ha1, ha2⟩ := Nat.chineseRemainder hcP (v : ZMod N).val
    (PadicInt.toZModPow (s + k) (u : ℤ_[l])).val
  have hau : ((a : ℕ) : ZMod (l ^ (s + k))) = PadicInt.toZModPow (s + k) (u : ℤ_[l]) := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 ha2, ZMod.natCast_zmod_val]
  have hcoP : a.Coprime (l ^ (s + k)) := by
    rw [← ZMod.isUnit_iff_coprime, hau]
    exact (Units.isUnit u).map _
  have hcoN' : a.Coprime N' := by
    have h1 : (v : ZMod N).val.Coprime N' :=
      (ZMod.val_coe_unit_coprime v).coprime_dvd_right (Dvd.intro_left _ hNN)
    unfold Nat.Coprime at h1 ⊢
    rw [ha1.gcd_eq, h1]
  have hdu : (l : ℤ_[l]) ^ (s + k) ∣ (u : ℤ_[l]) - (a : ℤ_[l]) := by
    rw [UpperTheory.Mu.dvd_sub_iff, map_natCast, hau]
  have has : a ≡ (v : ZMod N).val [MOD l ^ s] := by
    have h1 : (l : ℤ_[l]) ^ s ∣ (a : ℤ_[l]) - (((v : ZMod N).val : ℕ) : ℤ_[l]) := by
      have h2 := dvd_sub huv ((pow_dvd_pow _ (Nat.le_add_right s k)).trans hdu)
      convert h2 using 1
      ring
    rw [UpperTheory.Mu.dvd_sub_iff, map_natCast, map_natCast] at h1
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 h1
  have haN : a ≡ (v : ZMod N).val [MOD N] := by
    have := (Nat.modEq_and_modEq_iff_modEq_mul (hcop.pow_left s)).1 ⟨has, ha1⟩
    rwa [hNN] at this
  obtain ⟨σ, hσ⟩ := UpperTheory.Mu.exists_aut_pow Ω (N' * l ^ (s + k)) (mul_ne_zero hN'0 hP0) a
    (Nat.Coprime.mul_right hcoN' hcoP)
  refine ⟨σ, ?_, ?_⟩
  · have h1 : ζ ^ (N' * l ^ (s + k)) = 1 := by
      have : N' * l ^ (s + k) = N * l ^ k := by rw [← hNN]; ring
      rw [this, pow_mul, hζ.pow_eq_one, one_pow]
    have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨_, Nat.pos_of_ne_zero hN, hζ.pow_eq_one⟩
    rw [hσ ζ h1, hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf]
    exact haN
  · refine (pow_dvd_pow _ (Nat.le_add_left k s)).trans ?_
    rw [UpperTheory.Mu.dvd_sub_iff, ← hau]
    obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ (s + k))
    haveI (i : ℕ) : HasEnoughRootsOfUnity Ω (l ^ i) := by
      haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ hp.ne_zero⟩
      infer_instance
    have h1 := cyclotomicCharacter.spec l (n := s + k) (σ : Ω ≃+* Ω) η hη.pow_eq_one
    have h2 : σ η = η ^ a := hσ η (by rw [mul_comm, pow_mul, hη.pow_eq_one, one_pow])
    have h3 : η ^ (PadicInt.toZModPow (s + k) ((cyc l ℚ Ω σ : ℤ_[l]ˣ) : ℤ_[l])).val = η ^ a :=
      h1.symm.trans h2
    have hfin : IsOfFinOrder η := isOfFinOrder_iff_pow_eq_one.2 ⟨_, Nat.pos_of_ne_zero hP0, hη.pow_eq_one⟩
    rw [hfin.pow_eq_pow_iff_modEq, ← hη.eq_orderOf, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val] at h3
    exact h3
end

open NumberField Formalism.HC KStar.Tree

theorem UpperTheory.Mu.hostApprox :
    ∀ (φ : Frame) (H : HostRaw φ) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω] (v : (ZMod H.condN)ˣ), H.art v = 1 → ∀ u : ℤ_[l]ˣ, (l : ℤ_[l]) ^ H.condN.factorization l ∣ (u : ℤ_[l]) - (((v : ZMod H.condN).val : ℕ) : ℤ_[l]) → ∀ k : ℕ, ∃ g : Ω ≃ₐ[H.E] Ω, (l : ℤ_[l]) ^ k ∣ ((cyc l H.E Ω g : ℤ_[l]ˣ) : ℤ_[l]) - u := by
  intro φ H l _ Ω _ _ _ v hv u hu k
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap H.E Ω).injective
  haveI : IsScalarTower ℚ H.E Ω := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed H.E
  haveI : Algebra.IsAlgebraic H.E Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ H.E Ω
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have hN : H.condN ≠ 0 := by
    obtain ⟨hq, hd, -⟩ := H.hyp
    exact Nat.mul_ne_zero (Nat.mul_ne_zero H.QS_pos.ne' hq.ne_zero) hd.ne_zero
  haveI : NeZero (H.QS * H.q * H.d) := ⟨hN⟩
  haveI : NeZero (((H.QS * H.q * H.d : ℕ)) : ℚ) := ⟨by exact_mod_cast hN⟩
  haveI : IsGalois ℚ (CyclotomicField (H.QS * H.q * H.d) ℚ) :=
    @IsCyclotomicExtension.isGalois {H.QS * H.q * H.d} ℚ (CyclotomicField (H.QS * H.q * H.d) ℚ) _ _ _
      (CyclotomicField.isCyclotomicExtension (H.QS * H.q * H.d) ℚ)
  letI : Algebra H.E (CyclotomicField (H.QS * H.q * H.d) ℚ) := H.cycEmb.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ H.E (CyclotomicField (H.QS * H.q * H.d) ℚ) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Algebra.IsAlgebraic H.E (CyclotomicField (H.QS * H.q * H.d) ℚ) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) H.E
  let ι : CyclotomicField (H.QS * H.q * H.d) ℚ →ₐ[H.E] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let ιQ : CyclotomicField (H.QS * H.q * H.d) ℚ →ₐ[ℚ] Ω := ι.restrictScalars ℚ
  have hι : ∀ x : H.E, ιQ (H.cycEmb x) = algebraMap H.E Ω x := fun x => ι.commutes x
  have hζ : IsPrimitiveRoot (ιQ H.cycZeta) H.condN := H.cycZeta_prim.map_of_injective ιQ.injective
  obtain ⟨σ, hσζ, hσu⟩ := UpperTheory.Mu.autApprox l Ω H.condN hN (ιQ H.cycZeta) hζ v u hu k
  letI : Algebra (CyclotomicField (H.QS * H.q * H.d) ℚ) Ω := ιQ.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ (CyclotomicField (H.QS * H.q * H.d) ℚ) Ω :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let τ := σ.restrictNormal (CyclotomicField (H.QS * H.q * H.d) ℚ)
  have hτ : ∀ y, ιQ (τ y) = σ (ιQ y) := fun y => AlgEquiv.restrictNormal_commutes σ _ y
  have hτζ : τ H.cycZeta = H.cycZeta ^ ((v : ZMod H.condN).val) := by
    have e : ιQ (τ H.cycZeta) = ιQ (H.cycZeta ^ ((v : ZMod H.condN).val)) := by
      rw [hτ, hσζ, map_pow]
    exact ιQ.injective e
  have hfix : ∀ x : H.E, σ (algebraMap H.E Ω x) = algebraMap H.E Ω x := by
    intro x
    have h := H.art_spec v τ hτζ x
    rw [show H.art v = 1 from hv, map_one, AlgEquiv.one_apply] at h
    rw [← hι, ← hτ, ← h]
  exact ⟨{ σ with commutes' := hfix }, hσu⟩
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.NuLe
open NumberField Formalism.HC KStar.Tree

theorem UpperTheory.Mu.nuLe :
    ∀ (φ : Frame) (H : HostRaw φ) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω] (n : ℕ), Odd n → l ≠ H.q → l ≠ H.d → nuOf l (cyc l H.E Ω) n ≤ H.QS.factorization l + (if l ∣ H.QS then n.factorization l else 0) := by
  intro φ H l _ Ω _ _ _ n hn hq hd
  have hQS0 : H.QS ≠ 0 := H.QS_pos.ne'
  obtain ⟨u, hu1, hun⟩ := exists_unit_not_dvd l H.QS n hQS0 H.two_dvd_QS hn
  apply nuOf_le_of_approx l (cyc l H.E Ω) n _ u _ hun
  have hN : H.condN = H.QS * H.q * H.d := rfl
  have hfac : H.condN.factorization l = H.QS.factorization l := by
    have hq0 : H.q ≠ 0 := H.q_prime.ne_zero
    have hd0 : H.d ≠ 0 := H.d_prime.ne_zero
    rw [hN, Nat.factorization_mul (mul_ne_zero hQS0 hq0) hd0, Nat.factorization_mul hQS0 hq0]
    simp only [Finsupp.add_apply]
    rw [H.q_prime.factorization, H.d_prime.factorization]
    simp [Finsupp.single_apply, Ne.symm hq, Ne.symm hd]
  have h2 : 2 ≤ H.condN := by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero H.condN_ne_zero) H.two_dvd_condN
    exact this
  haveI : Fact (1 < H.condN) := ⟨by omega⟩
  intro k
  apply UpperTheory.Mu.hostApprox φ H l Ω 1 (map_one _) u _ k
  rw [hfac]
  simpa [ZMod.val_one] using hu1
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.NuQDUnit
open NumberField Formalism.HC KStar.Tree

private theorem nuQD_unit (N M l : ℕ) [Fact l.Prime] (hN : N = M * l) (hM : M ≠ 0) (hc : M.Coprime l)
    (u : ℤ_[l]ˣ) :
    ∃ v : (ZMod N)ˣ, (v : ZMod N).val ≡ 1 [MOD M] ∧
      (l : ℤ_[l]) ^ N.factorization l ∣
        ((u ^ 2 : ℤ_[l]ˣ) : ℤ_[l]) - ((((v ^ 2 : (ZMod N)ˣ) : ZMod N).val : ℕ) : ℤ_[l]) := by
  subst hN
  have hl : l.Prime := Fact.out
  haveI : NeZero M := ⟨hM⟩
  haveI : NeZero (M * l) := ⟨mul_ne_zero hM hl.ne_zero⟩
  let e := ZMod.chineseRemainder hc
  let w : (ZMod M × ZMod l)ˣ := MulEquiv.prodUnits.symm (1, Units.map (PadicInt.toZMod : ℤ_[l] →+* ZMod l).toMonoidHom u)
  let v : (ZMod (M * l))ˣ := Units.map e.symm.toRingHom.toMonoidHom w
  have he : e (v : ZMod (M * l)) = (w : ZMod M × ZMod l) := by
    simp [v]
  have hw : (w : ZMod M × ZMod l) = (1, PadicInt.toZMod (u : ℤ_[l])) := rfl
  have h1 : ZMod.cast (v : ZMod (M * l)) = (1 : ZMod M) := by
    have := congrArg Prod.fst he
    rw [hw] at this
    simpa [e, ZMod.chineseRemainder] using this
  have h2 : ZMod.cast (v : ZMod (M * l)) = PadicInt.toZMod (u : ℤ_[l]) := by
    have := congrArg Prod.snd he
    rw [hw] at this
    simpa [e, ZMod.chineseRemainder] using this
  have hfac : (M * l).factorization l = 1 := by
    rw [Nat.factorization_mul hM hl.ne_zero]
    simp only [Finsupp.add_apply, hl.factorization_self]
    have : ¬ l ∣ M := fun h => by
      have h' := Nat.Coprime.coprime_dvd_left h hc
      have h'' : l = 1 := by simpa using h'
      exact hl.one_lt.ne' h''
    rw [Nat.factorization_eq_zero_of_not_dvd this]
  refine ⟨v, ?_, ?_⟩
  · rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, h1, Nat.cast_one]
  · rw [hfac, pow_one]
    have hk : PadicInt.toZMod (((u ^ 2 : ℤ_[l]ˣ) : ℤ_[l]) - ((((v ^ 2 : (ZMod (M * l))ˣ) : ZMod (M * l)).val : ℕ) : ℤ_[l])) = 0 := by
      rw [map_sub, map_natCast, ZMod.natCast_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
        map_pow, ZMod.cast_pow (dvd_mul_left l M), h2, sub_self]
    have hmem : _ ∈ RingHom.ker (PadicInt.toZMod : ℤ_[l] →+* ZMod l) := hk
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hmem
    exact hmem

theorem UpperTheory.Mu.nuQD :
    ∀ (φ : Frame) (H : HostRaw φ) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω] (n : ℕ), (l = H.q ∨ l = H.d) → ¬ (l - 1) / 2 ∣ n → nuOf l (cyc l H.E Ω) n = 0 := by
  intro φ H l _ Ω _ _ _ n hl hn
  have hl2 : l ≠ 2 := by
    rcases hl with rfl | rfl
    · exact H.q_ne_two
    · exact H.d_ne_two
  obtain ⟨u, hu⟩ := exists_sq_unit_not_dvd l n hn hl2
  have hle := nuOf_le_of_approx l (cyc l H.E Ω) n 0 (u ^ 2) ?_ hu
  · omega
  intro k
  have hN : H.condN = H.QS * H.q * H.d := rfl
  rcases hl with rfl | rfl
  · obtain ⟨v, hv1, hv⟩ := nuQD_unit H.condN (H.QS * H.d) H.q (by rw [hN]; ring)
      (mul_ne_zero H.QS_ne_zero H.d_prime.ne_zero) H.coprime_QSd_q u
    have ha : H.art (v ^ 2) = 1 := by
      rw [map_pow]
      exact H.art_q v hv1
    exact UpperTheory.Mu.hostApprox φ H H.q Ω (v ^ 2) ha (u ^ 2) hv k
  · obtain ⟨v, hv1, hv⟩ := nuQD_unit H.condN (H.QS * H.q) H.d hN
      (mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero) H.coprime_QSq_d u
    have ha : H.art (v ^ 2) = 1 := by
      haveI : NeZero (H.QS * H.q) := ⟨mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero⟩
      haveI : NeZero H.condN := ⟨H.condN_ne_zero⟩
      have hdvd : H.QS * H.q ∣ H.condN := ⟨H.d, hN⟩
      have hv2 : ((v ^ 2 : (ZMod H.condN)ˣ) : ZMod H.condN).val ≡ 1 [MOD H.QS * H.q] := by
        have h1 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hv1
        rw [ZMod.natCast_val] at h1
        rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, Units.val_pow_eq_pow_val,
          ZMod.cast_pow hdvd, h1]
        simp
      have hd2 := H.art_d (v ^ 2) hv2
      rw [map_pow] at hd2 ⊢
      rcases H.art_d v hv1 with h | h
      · rw [h, one_pow]
      · rw [h] at hd2 ⊢
        rcases hd2 with h' | h'
        · exact h'
        · have hi : φ.iod = 1 := by
            rw [pow_two] at h'
            exact mul_eq_left.mp h'
          rw [hi, one_pow]
    exact UpperTheory.Mu.hostApprox φ H H.d Ω (v ^ 2) ha (u ^ 2) hv k
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.WDvdQS
open NumberField Formalism.HC KStar.Tree

private theorem wDvdQS_crt {N A B : ℕ} [NeZero N] (h : N = A * B) (hAB : A.Coprime B) (y : ℕ) (hy : y.Coprime B) :
    ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ 1 [MOD A] ∧ (u : ZMod N).val ≡ y [MOD B] := by
  subst h
  obtain ⟨u, hu1, hu2⟩ := Formalism.HC.Der.exists_unit_crt hAB 1 y (Nat.coprime_one_left A) hy
  exact ⟨u, hu1, hu2⟩

private theorem wDvdQS_not_dvd {φ : Frame} (H : HostRaw φ) (A p : ℕ) (hp : p.Prime) (h3 : 3 < p)
    (hN : H.condN = A * p) (hA : A.Coprime p)
    (hart : ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD A] → H.art u ^ 2 = 1) : ¬ p ∣ H.w := by
  intro hdvd
  haveI : NeZero H.condN := ⟨by rw [hN]; exact mul_ne_zero (fun h0 => by simp [h0] at hA; exact hp.one_lt.ne' hA) hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := H.exists_primitiveRoot_w
  have hζp : IsPrimitiveRoot (ζ ^ (H.w / p)) p := hζ.pow H.w_pos (Nat.div_mul_cancel hdvd).symm
  have hξ : IsPrimitiveRoot (Formalism.HC.Der.emb H (ζ ^ (H.w / p))) p :=
    hζp.map_of_injective (Formalism.HC.Der.emb H).toRingHom.injective
  have hpN : p ∣ H.condN := ⟨A, by rw [hN, mul_comm]⟩
  have hcop : (2 : ℕ).Coprime p := (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
  obtain ⟨u, hu1, hu2⟩ := wDvdQS_crt hN hA 2 hcop
  have ha : H.art (u ^ 2) = 1 := by rw [map_pow]; exact hart u hu1
  have he := Formalism.HC.Der.emb_art H (u ^ 2) (ζ ^ (H.w / p))
  rw [ha, map_one, AlgEquiv.one_apply, Formalism.HC.Der.tauN_root] at he
  · have hmod : ((u ^ 2 : (ZMod H.condN)ˣ) : ZMod H.condN).val ≡ 1 [MOD p] := by
      have he' : (Formalism.HC.Der.emb H (ζ ^ (H.w / p))) ^ ((u ^ 2 : (ZMod H.condN)ˣ) : ZMod H.condN).val
          = (Formalism.HC.Der.emb H (ζ ^ (H.w / p))) ^ 1 := by
        rw [pow_one]; exact he.symm
      have := (hξ.isOfFinOrder hp.ne_zero).pow_eq_pow_iff_modEq.mp he'
      rwa [← hξ.eq_orderOf] at this
    have h4 : ((u ^ 2 : (ZMod H.condN)ˣ) : ZMod H.condN).val ≡ 2 * 2 [MOD p] := by
      rw [Units.val_pow_eq_pow_val, sq, ZMod.val_mul]
      exact ((Nat.mod_modEq _ _).of_dvd hpN).trans (Nat.ModEq.mul hu2 hu2)
    have h41 : 1 ≡ 4 [MOD p] := hmod.symm.trans h4
    have h3 : p ∣ 3 := (Nat.modEq_iff_dvd' (by norm_num)).mp h41
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  · exact (hξ.pow_eq_one_iff_dvd _).mpr hpN

theorem UpperTheory.Mu.wDvdQS :
    ∀ (φ : Frame) (H : HostRaw φ), H.q ≠ 3 → H.w ∣ H.QS ∧ ¬ H.q ∣ H.w ∧ ¬ H.d ∣ H.w := by
  intro φ H hq3
  have hq := H.hyp.1
  have hd := H.hyp.2.1
  have hq8 := H.hyp.2.2.1
  have hd16 := H.hyp.2.2.2.1
  have hqd : Nat.Coprime H.q H.d := (Nat.coprime_primes hq hd).2 (by omega)
  have h1 : ¬ H.q ∣ H.w :=
    wDvdQS_not_dvd H (H.QS * H.d) H.q hq (by omega) (by ring)
      (Nat.Coprime.mul_left H.QS_coprime.coprime_mul_right_right hqd.symm) H.art_q
  have h2 : ¬ H.d ∣ H.w := by
    refine wDvdQS_not_dvd H (H.QS * H.q) H.d hd (by omega) rfl (Der.cop_QSq_d H) fun u hu => ?_
    rcases H.art_d u hu with h | h
    · rw [h, one_pow]
    · rw [h, sq]
      exact Prod.ext (show ((1, -1) : Formalism.FrobeniusOrbits.G0) * (1, -1) = 1 by decide) (mul_one _)
  refine ⟨?_, h1, h2⟩
  have h3 : H.w ∣ H.QS * H.q :=
    ((hd.coprime_iff_not_dvd.2 h2).symm).dvd_of_dvd_mul_right H.w_dvd_condN
  exact ((hq.coprime_iff_not_dvd.2 h1).symm).dvd_of_dvd_mul_right h3
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.SumFactorizationMulLogLe
open NumberField Formalism.HC KStar.Tree

private theorem sum_factorization_mul_log_le (m : ℕ) (S : Finset ℕ) :
    ∑ l ∈ S, (m.factorization l : ℝ) * Real.log l ≤ Real.log m := by
  classical
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  calc ∑ l ∈ S, (m.factorization l : ℝ) * Real.log l
      = ∑ l ∈ S.filter (· ∈ m.factorization.support), (m.factorization l : ℝ) * Real.log l := by
        refine (Finset.sum_filter_of_ne ?_).symm
        intro l _ h
        by_contra hs
        rw [Finsupp.notMem_support_iff.mp hs] at h
        simp at h
    _ ≤ ∑ l ∈ m.factorization.support, (m.factorization l : ℝ) * Real.log l := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro l hl
          exact (Finset.mem_filter.mp hl).2
        · intro l hl _
          have hp : l.Prime := Nat.prime_of_mem_primeFactors (by simpa using hl)
          apply mul_nonneg (Nat.cast_nonneg _)
          exact Real.log_nonneg (by exact_mod_cast hp.one_lt.le)

theorem UpperTheory.Mu.nuSum :
    ∀ (φ : Frame) (H : HostRaw φ) (Ω : Type) [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω] (n : ℕ), Odd n → ¬ (H.q - 1) / 2 ∣ n → ¬ (H.d - 1) / 2 ∣ n → ∀ ν : ℕ → ℕ, (∀ (l : ℕ) [Fact l.Prime], ν l = nuOf l (cyc l H.E Ω) n) → ∀ S : Finset ℕ, (∀ l ∈ S, l.Prime) → ∑ l ∈ S, (ν l : ℝ) * Real.log l ≤ Real.log H.QS + Real.log n := by
  intro φ H Ω _ _ _ n hn hq hd ν hν S hS
  have key : ∀ l ∈ S, (ν l : ℝ) * Real.log l ≤
      (H.QS.factorization l : ℝ) * Real.log l + (n.factorization l : ℝ) * Real.log l := by
    intro l hl
    have hp : l.Prime := hS l hl
    haveI : Fact l.Prime := ⟨hp⟩
    have hlog : 0 ≤ Real.log l := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    have hnat : ν l ≤ H.QS.factorization l + n.factorization l := by
      rw [hν l]
      by_cases hlq : l = H.q
      · rw [UpperTheory.Mu.nuQD φ H l Ω n (Or.inl hlq) (hlq ▸ hq)]
        exact Nat.zero_le _
      by_cases hld : l = H.d
      · rw [UpperTheory.Mu.nuQD φ H l Ω n (Or.inr hld) (hld ▸ hd)]
        exact Nat.zero_le _
      have := UpperTheory.Mu.nuLe φ H l Ω n hn hlq hld
      split_ifs at this <;> omega
    rw [← add_mul]
    apply mul_le_mul_of_nonneg_right _ hlog
    exact_mod_cast hnat
  calc ∑ l ∈ S, (ν l : ℝ) * Real.log l
      ≤ ∑ l ∈ S, ((H.QS.factorization l : ℝ) * Real.log l + (n.factorization l : ℝ) * Real.log l) :=
        Finset.sum_le_sum key
    _ = ∑ l ∈ S, (H.QS.factorization l : ℝ) * Real.log l + ∑ l ∈ S, (n.factorization l : ℝ) * Real.log l :=
        Finset.sum_add_distrib
    _ ≤ Real.log H.QS + Real.log n :=
        add_le_add (sum_factorization_mul_log_le H.QS S) (sum_factorization_mul_log_le n S)
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.SplitNotDvd
open NumberField IsDedekindDomain Formalism.HC

open Ideal in
theorem UpperTheory.Mu.splitNotDvd :
    ∀ (φ : Frame) (H : HostAx φ), H.toHostRaw.Exact → ∀ p : ℕ, p.Prime → {v : HeightOneSpectrum (𝓞 H.E) | ((p : ℕ) : 𝓞 H.E) ∈ v.asIdeal}.ncard = Module.finrank ℚ H.E → ¬ p ∣ H.QS := by
  intro φ H hex p hp hcard hdvd
  haveI hpf : Fact p.Prime := ⟨hp⟩
  haveI hgal : IsGalois ℚ H.E := H.galois
  obtain ⟨u, hu, hne⟩ := hex p hp hdvd
  set pZ : Ideal ℤ := Ideal.span {((p : ℕ) : ℤ)} with hpZ
  haveI hmax : pZ.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hmem : ∀ P : Ideal (𝓞 H.E), P.IsPrime → (((p : ℕ) : 𝓞 H.E) ∈ P ↔ P.LiesOver pZ) := by
    intro P hP
    constructor
    · intro h
      rw [Ideal.liesOver_iff]
      refine hmax.eq_of_le (Ideal.IsPrime.ne_top (Ideal.IsPrime.comap _)) ?_
      rw [hpZ, Ideal.span_le, Set.singleton_subset_iff]
      simpa [Ideal.under] using h
    · intro h
      have hz : ((p : ℕ) : ℤ) ∈ Ideal.under ℤ P := by
        rw [← (Ideal.liesOver_iff P pZ).1 h]
        exact Ideal.subset_span rfl
      simpa [Ideal.under] using hz
  have hset : (pZ.primesOver (𝓞 H.E)).ncard = Module.finrank ℚ H.E := by
    rw [← hcard]
    have heq : pZ.primesOver (𝓞 H.E) =
        (fun v : HeightOneSpectrum (𝓞 H.E) => v.asIdeal) '' {v | ((p : ℕ) : 𝓞 H.E) ∈ v.asIdeal} := by
      ext P
      constructor
      · rintro ⟨hP, hl⟩
        have hnb : P ≠ ⊥ := by
          intro hb
          have hz := (hmem P hP).2 hl
          rw [hb, Ideal.mem_bot] at hz
          exact hp.ne_zero (by exact_mod_cast hz)
        exact ⟨⟨P, hP, hnb⟩, (hmem P hP).2 hl, rfl⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v.isPrime, (hmem _ v.isPrime).1 hv⟩
    rw [heq, Set.ncard_image_of_injective _ (fun a b h => HeightOneSpectrum.ext h)]
  have hn : 0 < Module.finrank ℚ H.E := Module.finrank_pos
  obtain ⟨P, hPp, hPl⟩ := Set.nonempty_of_ncard_ne_zero (hset ▸ hn.ne')
  haveI := hPp
  haveI := hPl
  have key := Ideal.ncard_primesOver_mul_card_inertia_mul_finrank (G := Gal(H.E/ℚ)) pZ P
  rw [hset, IsGalois.card_aut_eq_finrank, mul_assoc] at key
  have h1 : Nat.card (Ideal.inertia Gal(H.E/ℚ) P) * P.inertiaDeg ℤ = 1 :=
    Nat.eq_of_mul_eq_mul_left hn (key.trans (mul_one _).symm)
  have hI : Nat.card (Ideal.inertia Gal(H.E/ℚ) P) = 1 := Nat.eq_one_of_mul_eq_one_right h1
  have hbot := Subgroup.eq_bot_of_card_eq _ hI
  set σ : Gal(H.E/ℚ) := H.gal.symm (H.art u) with hσ
  have hin : ∀ x : 𝓞 H.E, σ • x - x ∈ P := by
    refine (H.der.inertia p P σ).2 ⟨u, ?_, by simp [σ]⟩
    refine Nat.ModEq.of_dvd ?_ hu
    have hpc : p ∣ H.condN := dvd_trans hdvd (HostRaw.QS_dvd_condN _)
    have hv : p ^ H.condN.factorization p ∣ H.condN := Nat.ordProj_dvd _ _
    refine Nat.div_dvd_div_left hv ?_
    exact dvd_pow_self p (Nat.Prime.factorization_pos_of_dvd hp (HostRaw.condN_ne_zero _) hpc).ne'
  have hσI : σ ∈ Ideal.inertia Gal(H.E/ℚ) P := AddSubgroup.mem_inertia.2 hin
  rw [hbot, Subgroup.mem_bot] at hσI
  apply hne
  simpa [σ] using congrArg H.gal hσI
end

open NumberField Formalism.BasicNotions KStar.Tree

namespace UpperTheory.Mu

theorem tr_odd (R : Ranks) : Odd (R.t * R.r) := by
  refine Nat.odd_mul.2 ⟨R.t_odd, ?_⟩
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have hm := R.two_le_m
  unfold Ranks.r
  exact ⟨a + b - 1, by omega⟩

variable {R : Ranks} (H : Host R)

theorem half_not_dvd {l : ℕ} (h : l = H.q ∨ l = H.d) : ¬ (l - 1) / 2 ∣ R.t * R.r := by
  have hpos : 0 < R.t * R.r := (tr_odd R).pos
  obtain ⟨hq, hd⟩ := H.qd_big
  have e : 4 * R.t * R.r = 4 * (R.t * R.r) := by ring
  rw [e] at hq hd
  apply Nat.not_dvd_of_pos_of_lt hpos
  generalize R.t * R.r = N at *
  rcases h with rfl | rfl <;> omega

theorem w_dvd_QS : H.w ∣ H.QS := (wDvdQS _ H.toHostRaw H.q_ne_three).1

variable (Ω : Type) [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω]

theorem nu_eq_zero_of_qd (l : ℕ) [Fact l.Prime] (h : l = H.q ∨ l = H.d) : nuOf l (cyc l H.E Ω) (R.t * R.r) = 0 :=
  nuQD _ H.toHostRaw l Ω _ h (half_not_dvd H h)

theorem nu_eq_zero_of_not_dvd (l : ℕ) [Fact l.Prime] (h : ¬ l ∣ H.QS) : nuOf l (cyc l H.E Ω) (R.t * R.r) = 0 := by
  by_cases hqd : l = H.q ∨ l = H.d
  · exact nu_eq_zero_of_qd H Ω l hqd
  · push_neg at hqd
    have hle := nuLe _ H.toHostRaw l Ω (R.t * R.r) (tr_odd R) hqd.1 hqd.2
    rw [if_neg h, Nat.factorization_eq_zero_of_not_dvd h] at hle
    omega

theorem nu_eq_zero_of_split (l : ℕ) [hl : Fact l.Prime]
    (h : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 H.E) | ((l : ℕ) : 𝓞 H.E) ∈ v.asIdeal}.ncard = Module.finrank ℚ H.E) :
    nuOf l (cyc l H.E Ω) (R.t * R.r) = 0 :=
  nu_eq_zero_of_not_dvd H Ω l (splitNotDvd _ H.toHostAx H.QS_exact l hl.out h)

theorem sum_nu_le (ν : ℕ → ℝ) (hν : ∀ (l : ℕ) [Fact l.Prime], ν l = (nuOf l (cyc l H.E Ω) (R.t * R.r) : ℝ))
    (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) :
    ∑ l ∈ S, ν l * Real.log l ≤ Real.log (H.QS : ℝ) + Real.log ((R.t * R.r : ℕ) : ℝ) := by
  classical
  let μ : ℕ → ℕ := fun l => if h : l.Prime then (haveI := Fact.mk h; nuOf l (cyc l H.E Ω) (R.t * R.r)) else 0
  have hμ : ∀ (l : ℕ) [Fact l.Prime], μ l = nuOf l (cyc l H.E Ω) (R.t * R.r) := fun l hl => dif_pos hl.out
  refine le_of_eq_of_le (Finset.sum_congr rfl fun l hl => ?_)
    (nuSum _ H.toHostRaw Ω _ (tr_odd R) (half_not_dvd H (Or.inl rfl)) (half_not_dvd H (Or.inr rfl)) μ hμ S hS)
  haveI := Fact.mk (hS l hl)
  rw [hν l, hμ l]

theorem budget_le : Real.log (H.QS : ℝ) + Real.log ((R.t * R.r : ℕ) : ℝ) ≤
    2 * Real.log R.n + Real.log R.t + Real.log R.r := by
  have h1 : Real.log (H.QS : ℝ) ≤ 2 * Real.log R.n := by
    have : ((H.QS : ℕ) : ℝ) ≤ (R.n : ℝ) ^ 2 := by exact_mod_cast H.QS_le
    have h0 : (0 : ℝ) < H.QS := by exact_mod_cast H.QS_pos
    simpa using Real.log_le_log h0 this
  have h2 := (tr_odd R).pos
  have ht : (R.t : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mul_pos_right h2).ne'
  have hr : (R.r : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mul_pos_left h2).ne'
  rw [Nat.cast_mul, Real.log_mul ht hr]
  linarith

end UpperTheory.Mu
