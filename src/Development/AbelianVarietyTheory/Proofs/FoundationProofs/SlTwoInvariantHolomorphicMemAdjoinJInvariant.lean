module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HsCodiscreteNeBot
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerClassEqImpPowRatio
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneSubTwoDivLeSquarefreeLabelMass
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MassDegTypeLeCycleType
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingCyclotomicTowerLevel
public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoInvariantHolomorphicMemAdjoinJInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExponentsIntegralOfTranslationInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExponentsIntegralOfTranslationInvariant
open scoped MatrixGroups
open GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem exp_two_pi_rat_mem_range {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (r : ℚ) :
    ∃ a : Ω, ε a = Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero r.den := ⟨r.den_nz⟩
  haveI : NeZero (r.den : Ω) := ⟨Nat.cast_ne_zero.2 r.den_nz⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω r.den
  have hζ' : IsPrimitiveRoot (ε ζ) r.den := hζ.map_of_injective ε.injective
  have he : Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) ^ r.den = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨r.num, ?_⟩
    have h1 : ((r.den : ℚ) * r : ℚ) = r.num := Rat.den_mul_eq_num r
    have h2 : (r.den : ℂ) * (r : ℂ) = (r.num : ℂ) := by exact_mod_cast congrArg (fun x : ℚ => (x : ℂ)) h1
    rw [← h2]; ring
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one he
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

theorem Tower.exponent_integral_of_translation_invariant {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    {ε : Ω →+* ℂ} (X : Tower Ω ε) (h : X.K) (hh : X.sl (ofSL ModularGroup.T) h = h) (r : ℚ)
    (hr : (X.exp h).coeff r ≠ 0) : ∃ m : ℤ, r = m := by
  have e : ∀ (γ : SL(2, ℤ)) (i j : Fin 2), ent (ofSL γ) i j = ((γ.1 i j : ℤ) : ℚ) := fun _ _ _ => rfl
  have e10 : ent (ofSL ModularGroup.T) 1 0 = 0 := by rw [e]; simp [ModularGroup.T]
  have e00 : ent (ofSL ModularGroup.T) 0 0 = 1 := by rw [e]; simp [ModularGroup.T]
  have e01 : ent (ofSL ModularGroup.T) 0 1 = 1 := by rw [e]; simp [ModularGroup.T]
  have e11 : ent (ofSL ModularGroup.T) 1 1 = 1 := by rw [e]; simp [ModularGroup.T]
  have key := X.exp_upper _ e10 h r
  rw [hh, e00, e01, e11, mul_one, div_one] at key
  have h1 : eOm ε r = 1 := by
    have : eOm ε r * (X.exp h).coeff r = 1 * (X.exp h).coeff r := by rw [one_mul]; exact key.symm
    exact mul_right_cancel₀ hr this
  have h2 : ε (eOm ε r) = Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) :=
    Function.invFun_eq (exp_two_pi_rat_mem_range ε r)
  rw [h1, map_one] at h2
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h2.symm
  refine ⟨n, ?_⟩
  have h3 : (r : ℂ) = (n : ℂ) := by
    have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    apply mul_left_cancel₀ hne
    rw [hn]; ring
  exact_mod_cast h3

end GlobalTheory.KZ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExponentsIntegralOfTranslationInvariantStatement
open scoped MatrixGroups
open GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponents_integral_of_translation_invariant : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (h : X.K), X.sl (ofSL ModularGroup.T) h = h → ∀ r : ℚ, (X.exp h).coeff r ≠ 0 → ∃ m : ℤ, r = m := by
  first | exact @GlobalTheory.KZ.Tower.exponent_integral_of_translation_invariant | exact GlobalTheory.KZ.Tower.exponent_integral_of_translation_invariant | (intros; apply GlobalTheory.KZ.Tower.exponent_integral_of_translation_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoInvariantHolomorphicMemAdjoinJInvariant
noncomputable section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.LevelOne

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem eq_const_of_nonneg [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (h : X.K) (hinv : ∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h)
    (φ : ℂ → ℂ) (hd : DifferentiableOn ℂ φ Hs) (ha : X.an h = (φ : Mero))
    (hneg : ∀ r : ℚ, r < 0 → (X.exp h).coeff r = 0) :
    h = algebraMap Ω X.K ((X.exp h).coeff 0) := by
  set a0 := (X.exp h).coeff 0 with ha0
  have hsupp : ∀ r : ℚ, (X.exp h).coeff r ≠ 0 → ∃ n : ℕ, r = n := by
    intro r hr
    obtain ⟨m, rfl⟩ := GlobalTheory.T.exponents_integral_of_translation_invariant X h (hinv _) r hr
    have hm : 0 ≤ m := by
      by_contra hm
      exact hr (hneg _ (by exact_mod_cast (not_le.1 hm)))
    exact ⟨m.toNat, by rw [← Int.cast_natCast, Int.toNat_of_nonneg hm]⟩
  obtain ⟨B, t, hB⟩ := GlobalTheory.T.modularTower_function_tendsto_constTerm_exponential X h φ hd.continuousOn ha hsupp
  have hinvφ := GlobalTheory.T.modularTower_function_slTwoInt_invariant X h φ hd.continuousOn ha hinv
  have hexp1 : ∀ z : ℂ, t < z.im → Real.exp (-(2 * Real.pi * (z.im - t))) ≤ 1 := by
    intro z hz
    rw [Real.exp_le_one_iff]
    have : 0 < z.im - t := by linarith
    have := Real.pi_pos
    nlinarith
  obtain ⟨c, hc⟩ := GlobalTheory.T.const_of_slTwoInt_invariant_bounded_upperHalfPlane φ hd hinvφ ⟨‖ε a0‖ + |B|, t, fun z hz hzt => by
    have h1 := hB z hz hzt
    have h2 := hexp1 z hzt
    have h3 : B * Real.exp (-(2 * Real.pi * (z.im - t))) ≤ |B| := by
      calc B * Real.exp (-(2 * Real.pi * (z.im - t))) ≤ |B| * Real.exp (-(2 * Real.pi * (z.im - t))) :=
            mul_le_mul_of_nonneg_right (le_abs_self B) (Real.exp_pos _).le
        _ ≤ |B| * 1 := mul_le_mul_of_nonneg_left h2 (abs_nonneg B)
        _ = |B| := mul_one _
    calc ‖φ z‖ = ‖(φ z - ε a0) + ε a0‖ := by ring_nf
      _ ≤ ‖φ z - ε a0‖ + ‖ε a0‖ := norm_add_le _ _
      _ ≤ ‖ε a0‖ + |B| := by linarith⟩
  have hca : c = ε a0 := by
    have hle : ∀ s : ℝ, max t 0 < s → ‖c - ε a0‖ ≤ B * Real.exp (-(2 * Real.pi * (s - t))) := by
      intro s hs
      have hs0 : 0 < s := lt_of_le_of_lt (le_max_right _ _) hs
      have hst : t < s := lt_of_le_of_lt (le_max_left _ _) hs
      have hz : ((s : ℂ) * Complex.I) ∈ Hs := by simp [Hs, hs0]
      have := hB _ hz (by simpa using hst)
      rw [hc _ hz] at this
      simpa using this
    have ht : Filter.Tendsto (fun s : ℝ => B * Real.exp (-(2 * Real.pi * (s - t)))) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun s : ℝ => 2 * Real.pi * (s - t)) Filter.atTop Filter.atTop := by
        apply Filter.Tendsto.const_mul_atTop Real.two_pi_pos
        exact Filter.tendsto_atTop_add_const_right _ _ Filter.tendsto_id
      have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul B
      simpa using h2
    have h0 : ‖c - ε a0‖ ≤ 0 := ge_of_tendsto ht (Filter.eventually_gt_atTop (max t 0) |>.mono hle)
    have := norm_le_zero_iff.1 h0
    exact sub_eq_zero.1 this
  apply SiegelModel.an_injective X
  rw [ha, X.an_c]
  exact SiegelModel.germ_eq_of_eqOn fun z hz => by rw [hc z hz, hca]

theorem mem_adjoin_j : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ h : X.K,
    (∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h) → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h = (φ : Mero)) →
    h ∈ Algebra.adjoin Ω {X.jK} := by
  intro Ω _ _ _ ε X _ hj
  obtain ⟨ψ, hψ, hψa⟩ := hj
  have key : ∀ n : ℕ, ∀ h : X.K, (∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h) →
      (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h = (φ : Mero)) →
      (∀ r : ℚ, r < -(n : ℚ) → (X.exp h).coeff r = 0) → h ∈ Algebra.adjoin Ω {X.jK} := by
    intro n
    induction n with
    | zero =>
      intro h hinv hol hneg
      obtain ⟨φ, hd, ha⟩ := hol
      rw [eq_const_of_nonneg X h hinv φ hd ha (by simpa using hneg)]
      exact Subalgebra.algebraMap_mem _ _
    | succ n ih =>
      intro h hinv hol hneg
      obtain ⟨φ, hd, ha⟩ := hol
      obtain ⟨c, hcdef⟩ : ∃ c : Ω, c = (X.exp h).coeff (-((n + 1 : ℕ) : ℚ)) := ⟨_, rfl⟩
      obtain ⟨h', hh'⟩ : ∃ h' : X.K, h' = h - algebraMap Ω X.K c * X.jK ^ (n + 1) := ⟨_, rfl⟩
      have hj := GlobalTheory.T.hahnSeries_pow_of_leading_qInv (X.exp X.jK) X.j_exp.1 X.j_exp.2.1 (n + 1)
      have hinv' : ∀ γ : SL(2, ℤ), X.sl (ofSL γ) h' = h' := by
        intro γ
        rw [hh', map_sub, map_mul, map_pow, X.j_inv, hinv, AlgEquiv.commutes]
      have hol' : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h' = (φ : Mero) := by
        refine ⟨fun z => φ z - ε c * ψ z ^ (n + 1), ?_, ?_⟩
        · exact hd.sub ((hψ.pow _).const_mul _)
        · rw [hh', map_sub, map_mul, map_pow, X.an_c, ha, hψa]
          rfl
      have hneg' : ∀ r : ℚ, r < -(n : ℚ) → (X.exp h').coeff r = 0 := by
        intro r hr
        by_contra hrz
        obtain ⟨m, rfl⟩ := GlobalTheory.T.exponents_integral_of_translation_invariant X h' (hinv' _) r hrz
        apply hrz
        have hcoe : (X.exp h').coeff (m : ℚ) =
            (X.exp h).coeff m - c * ((X.exp X.jK) ^ (n + 1)).coeff m := by
          rw [hh', map_sub, map_mul, AlgHom.commutes, map_pow, HahnSeries.coeff_sub, HahnSeries.algebraMap_apply',
            PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, HahnSeries.ofPowerSeries_C,
            HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
        rw [hcoe]
        have hm : m ≤ -((n : ℤ) + 1) := by
          have : (m : ℚ) < -(n : ℚ) := hr
          have : m < -(n : ℤ) := by exact_mod_cast this
          omega
        rcases hm.lt_or_eq with hlt | heq
        · have hq : (m : ℚ) < -((n + 1 : ℕ) : ℚ) := by push_cast; exact_mod_cast hlt
          rw [hneg _ hq, hj.2 _ hq]
          ring
        · have hq : (m : ℚ) = -((n + 1 : ℕ) : ℚ) := by rw [heq]; push_cast; ring
          rw [hq, hj.1, hcdef]
          ring
      have hmem := ih h' hinv' hol' hneg'
      have hsum : h = h' + algebraMap Ω X.K c * X.jK ^ (n + 1) := by rw [hh']; abel
      have hjm : X.jK ∈ Algebra.adjoin Ω {X.jK} := Algebra.self_mem_adjoin_singleton Ω X.jK
      rw [hsum]
      exact add_mem hmem (mul_mem (Subalgebra.algebraMap_mem _ _) (pow_mem hjm _))
  intro h hinv hol
  refine key ⌈-(X.exp h).order⌉₊ h hinv hol fun r hr => HahnSeries.coeff_eq_zero_of_lt_order ?_
  have := Nat.le_ceil (-(X.exp h).order)
  linarith

end GlobalTheory.KZ.LevelOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoInvariantHolomorphicMemAdjoinJInvariantStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slTwo_invariant_holomorphic_mem_adjoin_jInvariant : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ h : X.K, (∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h) → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h = (φ : Mero)) → h ∈ Algebra.adjoin Ω {X.jK} := by
  first | exact @GlobalTheory.KZ.LevelOne.mem_adjoin_j | exact GlobalTheory.KZ.LevelOne.mem_adjoin_j | (intros; apply GlobalTheory.KZ.LevelOne.mem_adjoin_j <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassNoLargePrimeFactorLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardCycleTypeConsMul
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

open Equiv Finset

theorem card_cycleType_cons_mul (N p : ℕ) (hp : 2 ≤ p) (hpN : p ≤ N) (m : Multiset ℕ)
    (hpm : p ∉ m) (hs : m.sum ≤ N - p) (h2 : ∀ a ∈ m, 2 ≤ a) :
    (univ.filter fun σ : Perm (Fin N) => σ.cycleType = p ::ₘ m).card * p * (N - p).factorial
      = N.factorial * (univ.filter fun σ : Perm (Fin (N - p)) => σ.cycleType = m).card := by
  have hA := Equiv.Perm.card_of_cycleType_mul_eq (α := Fin N) (p ::ₘ m)
  have hB := Equiv.Perm.card_of_cycleType_mul_eq (α := Fin (N - p)) m
  rw [Fintype.card_fin] at hA hB
  have hcA : (p ::ₘ m).sum ≤ N ∧ ∀ a ∈ p ::ₘ m, 2 ≤ a := by
    refine ⟨by rw [Multiset.sum_cons]; omega, fun a ha => ?_⟩
    rcases Multiset.mem_cons.1 ha with rfl | ha
    · exact hp
    · exact h2 a ha
  rw [if_pos hcA] at hA
  rw [if_pos ⟨hs, h2⟩] at hB
  have hsum : N - (p ::ₘ m).sum = N - p - m.sum := by
    rw [Multiset.sum_cons, Nat.sub_sub]
  have hfac : ∏ n ∈ (p ::ₘ m).toFinset, ((p ::ₘ m).count n).factorial =
      ∏ n ∈ m.toFinset, (m.count n).factorial := by
    rw [Multiset.toFinset_cons, Finset.prod_insert (by simpa using hpm), Multiset.count_cons_self,
      Multiset.count_eq_zero.2 hpm, zero_add, Nat.factorial_one, one_mul]
    refine Finset.prod_congr rfl fun n hn => ?_
    have hne : n ≠ p := fun h => hpm (h ▸ Multiset.mem_toFinset.1 hn)
    rw [Multiset.count_cons_of_ne hne]
  rw [hsum, Multiset.prod_cons, hfac] at hA
  rw [← hB, ← hA]
  ring

theorem card_mem_cycleType_mul (N p : ℕ) (hp : 2 ≤ p) (hN : N < 2 * p) (hpN : p ≤ N) :
    (univ.filter fun σ : Perm (Fin N) => p ∈ σ.cycleType).card * p = N.factorial := by
  have hTm : ∀ m ∈ (univ : Finset (Perm (Fin (N - p)))).image Perm.cycleType,
      m.sum ≤ N - p ∧ ∀ a ∈ m, 2 ≤ a := by
    intro m hm
    obtain ⟨τ, -, rfl⟩ := Finset.mem_image.1 hm
    refine ⟨?_, fun a ha => Perm.two_le_of_mem_cycleType ha⟩
    simpa using τ.sum_cycleType_le
  have hpT : ∀ m ∈ (univ : Finset (Perm (Fin (N - p)))).image Perm.cycleType, p ∉ m := by
    intro m hm hpm
    have h1 := Multiset.le_sum_of_mem hpm
    have h2 := (hTm m hm).1
    omega
  have hfib : (univ.filter fun σ : Perm (Fin N) => p ∈ σ.cycleType).card =
      ∑ m ∈ (univ : Finset (Perm (Fin (N - p)))).image Perm.cycleType,
        (univ.filter fun σ : Perm (Fin N) => σ.cycleType = p ::ₘ m).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun σ : Perm (Fin N) => σ.cycleType.erase p)
      (t := (univ : Finset (Perm (Fin (N - p)))).image Perm.cycleType)]
    · refine Finset.sum_congr rfl fun m _ => ?_
      congr 1
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        rw [← h2, Multiset.cons_erase h1]
      · intro h
        rw [h]
        exact ⟨Multiset.mem_cons_self _ _, Multiset.erase_cons_head _ _⟩
    · intro σ hσ
      have hσ' : p ∈ σ.cycleType := by simpa using hσ
      have hsum := Multiset.sum_erase hσ'
      have hle := σ.sum_cycleType_le
      rw [Fintype.card_fin] at hle
      have hc : (σ.cycleType.erase p).sum ≤ Fintype.card (Fin (N - p)) ∧
          ∀ a ∈ σ.cycleType.erase p, 2 ≤ a := by
        refine ⟨by rw [Fintype.card_fin]; omega, fun a ha => ?_⟩
        exact Perm.two_le_of_mem_cycleType (Multiset.mem_of_mem_erase ha)
      obtain ⟨τ, hτ⟩ := (Perm.exists_with_cycleType_iff (Fin (N - p))).2 hc
      exact Finset.mem_image.2 ⟨τ, Finset.mem_univ _, hτ⟩
  have hmain : (univ.filter fun σ : Perm (Fin N) => p ∈ σ.cycleType).card * p * (N - p).factorial
      = N.factorial * (N - p).factorial := by
    rw [hfib, Finset.sum_mul, Finset.sum_mul,
      Finset.sum_congr rfl fun m hm =>
        card_cycleType_cons_mul N p hp hpN m (hpT m hm) (hTm m hm).1 (hTm m hm).2,
      ← Finset.mul_sum]
    congr 1
    have hc := Finset.card_eq_sum_card_image Perm.cycleType (univ : Finset (Perm (Fin (N - p))))
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hc
    exact hc.symm
  exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos _) hmain

theorem card_perm_long_cycle : ∀ N p : ℕ, N < 2 * p → p ≤ N →
    (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts).card * p
      = N.factorial := by
  intro N p hN hpN
  rcases Nat.lt_or_ge p 2 with hp | hp
  · obtain rfl : p = 1 := by omega
    obtain rfl : N = 1 := by omega
    have hall : ∀ σ : Equiv.Perm (Fin 1), 1 ∈ σ.partition.parts := by
      intro σ
      have hs : σ.partition.parts.sum = 1 := σ.partition.parts_sum.trans (Fintype.card_fin 1)
      obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero (s := σ.partition.parts)
        (fun h => by rw [h, Multiset.sum_zero] at hs; exact absurd hs (by norm_num))
      have h1 := σ.partition.parts_pos ha
      have h2 := Multiset.le_sum_of_mem ha
      obtain rfl : a = 1 := by omega
      exact ha
    rw [Finset.filter_true_of_mem (fun σ _ => hall σ), Finset.card_univ, Fintype.card_perm]
    simp
  · have hiff : ∀ σ : Equiv.Perm (Fin N), p ∈ σ.partition.parts ↔ p ∈ σ.cycleType := by
      intro σ
      rw [Equiv.Perm.parts_partition, Multiset.mem_add]
      constructor
      · rintro (h | h)
        · exact h
        · have := Multiset.eq_of_mem_replicate h
          omega
      · exact Or.inl
    simp_rw [hiff]
    exact card_mem_cycleType_mul N p hp hN hpN

end GlobalTheory.BadShare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassNoLargePrimeFactorLe
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem add_le_sum_of_mem_of_ne {s : Multiset ℕ} {p q : ℕ} (hp : p ∈ s) (hq : q ∈ s) (h : p ≠ q) : p + q ≤ s.sum := by
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hp
  have hq' : q ∈ t := (Multiset.mem_cons.mp hq).resolve_left (Ne.symm h)
  obtain ⟨u, rfl⟩ := Multiset.exists_cons_of_mem hq'
  rw [Multiset.sum_cons, Multiset.sum_cons, ← add_assoc]
  exact Nat.le_add_right _ _

theorem card_perm_no_long_cycle (N : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, N < 2 * p) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∀ p ∈ S, p ∉ σ.partition.parts).card +
      ∑ p ∈ S, (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts).card = N.factorial := by
  have hsum : ∀ σ : Equiv.Perm (Fin N), σ.partition.parts.sum = N := fun σ => by
    simpa using σ.partition.parts_sum
  have hdisj : (S : Set ℕ).PairwiseDisjoint
      fun p => Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts := by
    intro p hp q hq hpq
    rw [Function.onFun, Finset.disjoint_filter]
    intro σ _ hpσ hqσ
    have h1 := add_le_sum_of_mem_of_ne hpσ hqσ hpq
    rw [hsum σ] at h1
    have h2 := hS p hp
    have h3 := hS q hq
    omega
  rw [← Finset.card_biUnion hdisj]
  have hc : (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∀ p ∈ S, p ∉ σ.partition.parts) =
      (S.biUnion fun p => Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts)ᶜ := by
    ext σ
    simp
  rw [hc, Finset.card_compl_add_card, Fintype.card_perm, Fintype.card_fin]

theorem mass_not_hasPrimeFactor_le : ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 100000 ≤ N →
    (mass g N fun f => ¬ HasPrimeFactor g N f) ≤ 1 - 1 / (10 * Real.log N) := by
  intro g _ N hN
  set S := (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) with hSdef
  have hS : ∀ p ∈ S, N < 2 * p := fun p hp => (Finset.mem_filter.mp hp).2.2.1
  have hSN : ∀ p ∈ S, p ≤ N := fun p hp =>
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
  have hmono : (mass g N fun f => ¬ HasPrimeFactor g N f) ≤
      mass g N fun f => ∀ p ∈ S, p ∉ degType g f := by
    have hsub : (sqSet g N).filter (fun f => ¬ HasPrimeFactor g N f) ⊆
        (sqSet g N).filter (fun f => ∀ p ∈ S, p ∉ degType g f) := by
      intro f hf
      rw [Finset.mem_filter] at hf ⊢
      refine ⟨hf.1, ?_⟩
      intro p hp hpf
      apply hf.2
      unfold degType at hpf
      unfold HasPrimeFactor
      obtain ⟨h, hh, rfl⟩ := Multiset.mem_map.mp hpf
      obtain ⟨-, hpr, h2, h3⟩ := Finset.mem_filter.mp hp
      exact ⟨h, UniqueFactorizationMonoid.irreducible_of_normalized_factor h hh,
        UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hh, hpr, h2, h3⟩
    unfold mass
    convert Finset.sum_le_sum_of_subset_of_nonneg (f := fun f => ((torusCard g f : ℝ))⁻¹) hsub
      (fun f _ _ => by positivity)
  have hT := GlobalTheory.T.mass_degType_le_card_cycleType_div g N (fun m : Multiset ℕ => ∀ p ∈ S, p ∉ m)
  have hcount := card_perm_no_long_cycle N S hS
  have hlong : ∀ p ∈ S, ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
      p ∈ σ.partition.parts).card : ℝ) = N.factorial / p := by
    intro p hp
    have hp0 : 0 < p := by have := hS p hp; omega
    have hp0' : (p : ℝ) ≠ 0 := by exact_mod_cast hp0.ne'
    rw [eq_div_iff hp0']
    exact_mod_cast card_perm_long_cycle N p (hS p hp) (hSN p hp)
  have hfac : (N.factorial : ℝ) ≠ 0 := by positivity
  have hratio : ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
      ∀ p ∈ S, p ∉ σ.partition.parts).card : ℝ) / N.factorial = 1 - ∑ p ∈ S, (1 : ℝ) / p := by
    have hc : ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
        ∀ p ∈ S, p ∉ σ.partition.parts).card : ℝ) = N.factorial - ∑ p ∈ S, (N.factorial : ℝ) / p := by
      rw [← Finset.sum_congr rfl hlong]
      have := congrArg (fun n : ℕ => (n : ℝ)) hcount
      push_cast at this
      linarith
    rw [hc, sub_div, div_self hfac, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [div_right_comm, div_self hfac]
  have hprimes := inv_log_le_sum_inv_primes_between N hN
  calc _ ≤ _ := hmono
    _ ≤ _ := hT
    _ = 1 - ∑ p ∈ S, (1 : ℝ) / p := by convert hratio
    _ ≤ 1 - 1 / (10 * Real.log N) := by linarith

end GlobalTheory.BadShare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassNoLargePrimeFactorLeStatement
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squarefreeLabelTorusMass_no_large_prime_factor_le : ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 100000 ≤ N → (mass g N fun f => ¬ HasPrimeFactor g N f) ≤ 1 - 1 / (10 * Real.log N) := by
  first | exact @GlobalTheory.BadShare.mass_not_hasPrimeFactor_le | exact GlobalTheory.BadShare.mass_not_hasPrimeFactor_le | (intros; apply GlobalTheory.BadShare.mass_not_hasPrimeFactor_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerLevelEmbeddingInjectiveRangeAdjoinRoots
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerLevelEmbeddingInjectiveRangeAdjoinRoots
open GlobalTheory.K5 GlobalTheory.KumDlog

noncomputable section

namespace GlobalTheory.K5.LevEmb

theorem emb_inj_range : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (m : ℕ), 1 ≤ m → ∀ ι : On p m →ₐ[O0 p] Ω, IsEmb T m ι →
    Function.Injective ι ∧ ι.range = Lev T m := by
  intro p _ Ω _ _ hΩ T m hm ι hι
  obtain ⟨b, hb⟩ := GlobalTheory.K5.OnFree.on_free p m
  have hadj : Algebra.adjoin (O0 p) {xn p m, yn p m} = ⊤ :=
    GlobalTheory.K5.OnDVR.adjoin_eq_top_of_basis b (xn p m) (yn p m) (fun i => (i : ℕ)) (fun j => (j : ℕ))
      (fun i j => hb i j)
  refine ⟨?_, ?_⟩
  · obtain ⟨hdom, -, -⟩ := GlobalTheory.K5.OnDVR.isDVR_On p m hm
    haveI : Module.Finite (O0 p) (On p m) := Module.Finite.of_basis b
    haveI : Algebra.IsIntegral (O0 p) (On p m) := Algebra.IsIntegral.of_finite _ _
    have hk : RingHom.ker (ι : On p m →+* Ω) = ⊥ := by
      apply Ideal.eq_bot_of_comap_eq_bot (R := O0 p)
      rw [eq_bot_iff]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker] at ha
      have h1 : algebraMap (O0 p) Ω a = 0 := by
        rw [← ι.commutes]; exact ha
      rw [Ideal.mem_bot]
      exact hΩ.inj (by rw [h1, map_zero])
    exact (RingHom.injective_iff_ker_eq_bot _).2 hk
  · rw [← Algebra.map_top, ← hadj, AlgHom.map_adjoin, Set.image_pair, hι.1, hι.2]
    rfl

end GlobalTheory.K5.LevEmb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerLevelEmbeddingInjectiveRangeAdjoinRootsStatement
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.towerLevelEmbedding_injective_range_adjoinRoots : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (m : ℕ), 1 ≤ m → ∀ ι : On p m →ₐ[O0 p] Ω, IsEmb T m ι →
  Function.Injective ι ∧ ι.range = Lev T m := by
  first | exact @GlobalTheory.K5.LevEmb.emb_inj_range | exact GlobalTheory.K5.LevEmb.emb_inj_range | (intros; apply GlobalTheory.K5.LevEmb.emb_inj_range <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpTwoPiIRatInFieldRootsOfUnityProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpTwoPiIRatInFieldRootsOfUnityProperties
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNRoots

theorem alg_mem_range (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (z : ℂ) (hz : IsAlgebraic ℚ z) : z ∈ ε.range := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hi : IsIntegral ℚ z := hz.isIntegral
  set p := minpoly ℚ z with hp
  have hm : p.Monic := minpoly.monic hi
  have hqm : (p.map (algebraMap ℚ Ω)).Monic := hm.map _
  have hroots := hqm.roots_map_of_card_eq_natDegree ε IsAlgClosed.card_roots_eq_natDegree
  have hcomp : ε.comp (algebraMap ℚ Ω) = algebraMap ℚ ℂ := Subsingleton.elim _ _
  rw [Polynomial.map_map, hcomp] at hroots
  have hne : p.map (algebraMap ℚ ℂ) ≠ 0 := (hm.map _).ne_zero
  have hzr : z ∈ (p.map (algebraMap ℚ ℂ)).roots := by
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot, Polynomial.eval_map_algebraMap]
    exact minpoly.aeval ℚ z
  rw [← hroots] at hzr
  obtain ⟨w, -, hw⟩ := Multiset.mem_map.1 hzr
  exact ⟨w, hw⟩

theorem exp_isAlgebraic (x : ℚ) : IsAlgebraic ℚ (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) := by
  have hpow : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have : (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = (x.num : ℂ) * (2 * Real.pi * Complex.I) := by
      have hx : (x : ℂ) = (x.num : ℂ) / (x.den : ℂ) := by
        exact_mod_cast (Rat.num_div_den x).symm
      have hd : (x.den : ℂ) ≠ 0 := by exact_mod_cast x.den_nz
      rw [hx]; field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  refine ⟨Polynomial.X ^ x.den - Polynomial.C 1, Polynomial.X_pow_sub_C_ne_zero x.pos 1, ?_⟩
  simp [hpow]

theorem main : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ ε.range) ∧ (∀ x : ℚ, ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ∧ eOm ε 0 = 1 ∧ (∀ x y : ℚ, eOm ε (x + y) = eOm ε x * eOm ε y) ∧ (∀ N : ℕ, 0 < N → IsPrimitiveRoot (eOm ε (1 / N)) N) ∧ ∀ z : ℂ, IsAlgebraic ℚ z → z ∈ ε.range := by
  intro Ω _ _ _ ε
  have hr : ∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ ε.range :=
    fun x => alg_mem_range Ω ε _ (exp_isAlgebraic x)
  have he : ∀ x : ℚ, ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
    intro x
    obtain ⟨w, hw⟩ := hr x
    exact Function.invFun_eq ⟨w, hw⟩
  have hinj : Function.Injective ε := ε.injective
  refine ⟨hr, he, ?_, ?_, ?_, fun z hz => alg_mem_range Ω ε z hz⟩
  · apply hinj; rw [he, map_one]; simp
  · intro x y; apply hinj
    rw [map_mul, he, he, he, ← Complex.exp_add]; congr 1; push_cast; ring
  · intro N hN
    apply IsPrimitiveRoot.of_map_of_injective (f := ε) _ hinj
    rw [he]
    have h := Complex.isPrimitiveRoot_exp N hN.ne'
    convert h using 2
    push_cast; ring

end GlobalTheory.FNRoots
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpTwoPiIRatInFieldRootsOfUnityPropertiesStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expTwoPiIRatInField_roots_of_unity_properties : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ ε.range) ∧ (∀ x : ℚ, ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ∧ eOm ε 0 = 1 ∧ (∀ x y : ℚ, eOm ε (x + y) = eOm ε x * eOm ε y) ∧ (∀ N : ℕ, 0 < N → IsPrimitiveRoot (eOm ε (1 / N)) N) ∧ ∀ z : ℂ, IsAlgebraic ℚ z → z ∈ ε.range := by
  first | exact @GlobalTheory.FNRoots.main | exact GlobalTheory.FNRoots.main | (intros; apply GlobalTheory.FNRoots.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassDivisorBound
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassDivisorBound
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem mass_true_le_one (g : ℕ) [Fact g.Prime] (N : ℕ) : (mass g N fun _ => True) ≤ 1 := by
  refine (GlobalTheory.T.mass_degType_le_card_cycleType_div g N (fun _ => True)).trans (le_of_eq ?_)
  rw [Finset.filter_true, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have hN : (N.factorial : ℝ) ≠ 0 := by positivity
  exact div_self hN

theorem mass_dvd_le (g : ℕ) [Fact g.Prime] (N a : ℕ) (h : (ZMod g)[X]) (hh : h ∈ sqSet g a) :
    (mass g N fun f => h ∣ f) ≤ ((torusCard g h : ℝ))⁻¹ * mass g (N - a) fun _ => True := by
  obtain ⟨hmon, hdeg, -, -⟩ := mem_sqSet.1 hh
  have hh0 : h ≠ 0 := hmon.ne_zero
  unfold mass
  set S := (sqSet g N).filter fun f => h ∣ f with hS
  have hfac : ∀ f ∈ S, h * (f /ₘ h) = f := by
    intro f hf
    have hd : h ∣ f := (Finset.mem_filter.1 hf).2
    have e := Polynomial.modByMonic_add_div f h
    rwa [(Polynomial.modByMonic_eq_zero_iff_dvd hmon).2 hd, zero_add] at e
  have hmem : ∀ f ∈ S, f /ₘ h ∈ sqSet g (N - a) := by
    intro f hf
    obtain ⟨fmon, fdeg, fsq, fc0⟩ := mem_sqSet.1 (Finset.mem_filter.1 hf).1
    have e := hfac f hf
    have umon : (f /ₘ h).Monic := hmon.of_mul_monic_left (by rw [e]; exact fmon)
    refine mem_sqSet.2 ⟨umon, ?_, ?_, ?_⟩
    · have hd := hmon.natDegree_mul umon
      rw [e, fdeg, hdeg] at hd
      omega
    · exact Squarefree.of_mul_right (by rw [e]; exact fsq)
    · intro hz
      apply fc0
      rw [← e, Polynomial.mul_coeff_zero, hz, mul_zero]
  have hinj : Set.InjOn (fun f => f /ₘ h) (S : Set (ZMod g)[X]) := by
    intro f hf f' hf' hq
    rw [← hfac f hf, ← hfac f' hf']
    exact congrArg (h * ·) hq
  have hterm : ∀ f ∈ S, ((torusCard g f : ℝ))⁻¹ =
      ((torusCard g h : ℝ))⁻¹ * ((torusCard g (f /ₘ h) : ℝ))⁻¹ := by
    intro f hf
    have e := hfac f hf
    have hu0 : f /ₘ h ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at e
      exact (mem_sqSet.1 (Finset.mem_filter.1 hf).1).1.ne_zero e.symm
    conv_lhs => rw [← e]
    rw [torusCard_mul hh0 hu0, Nat.cast_mul, mul_inv]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Nat.cast_nonneg _))
  rw [← Finset.sum_image (f := fun u => ((torusCard g u : ℝ))⁻¹) hinj, Finset.filter_true]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => inv_nonneg.2 (Nat.cast_nonneg _))
  intro u hu
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hu
  exact hmem f hf

theorem divisor_bound : ∀ (g : ℕ) [Fact g.Prime], (∀ N : ℕ, (mass g N fun _ => True) ≤ 1) ∧
    ∀ (N a : ℕ), ∀ h ∈ sqSet g a, (mass g N fun f => h ∣ f) ≤ ((torusCard g h : ℝ))⁻¹ := by
  intro g _
  refine ⟨mass_true_le_one g, fun N a h hh => ?_⟩
  refine (mass_dvd_le g N a h hh).trans ?_
  exact mul_le_of_le_one_right (inv_nonneg.2 (Nat.cast_nonneg _)) (mass_true_le_one g _)

end GlobalTheory.BadShare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassDivisorBoundStatement
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squarefreeLabelTorusMass_divisor_bound : ∀ (g : ℕ) [Fact g.Prime], (∀ N : ℕ, (mass g N fun _ => True) ≤ 1) ∧ ∀ (N a : ℕ), ∀ h ∈ sqSet g a, (mass g N fun f => h ∣ f) ≤ ((torusCard g h : ℝ))⁻¹ := by
  first | exact @GlobalTheory.BadShare.divisor_bound | exact GlobalTheory.BadShare.divisor_bound | (intros; apply GlobalTheory.BadShare.divisor_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesAndDerivUniqueOfCoefficients
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesAndDerivUniqueOfCoefficients
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.EvUniq

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]


variable (Ω) in
def zpHom : ℤ_[p] →+* Ω :=
  (algebraMap (O0 p) Ω).comp ((algebraMap (Lau p) (O0 p)).comp HahnSeries.C)

theorem zpHom_apply (z : ℤ_[p]) : zpHom (Ω := Ω) z = zp Ω z := by
  simp [zpHom, zp, HahnSeries.C_apply]

theorem zp_neg (z : ℤ_[p]) : zp Ω (-z) = - zp Ω z := by
  rw [← zpHom_apply, map_neg, zpHom_apply]

theorem zpHom_injective (hc : IsClo p Ω) : Function.Injective (zpHom (p := p) (Ω := Ω)) := by
  haveI := Basic.charZero_of_isClo hc
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro m hm
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hm
  have hu : zpHom (Ω := Ω) ((PadicInt.unitCoeff h0 : ℤ_[p])) ≠ 0 :=
    ((Units.isUnit (PadicInt.unitCoeff h0)).map (zpHom (Ω := Ω))).ne_zero
  have hp0 : (p : Ω) ^ m.valuation ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  exact mul_ne_zero hu hp0 hm

theorem exists_coords (hc : IsClo p Ω) {ι : Type} [Fintype ι] (E : ι → Ω) :
    ∃ (κ : Type) (_ : Fintype κ) (f : κ → Ω) (M : ι → κ → ℤ_[p]),
      (∀ k, E k = ∑ i, zp Ω (M k i) * f i) ∧
      ∀ v : ι → ℤ_[p], ∑ k, zp Ω (v k) * E k = 0 → ∀ i, ∑ k, v k * M k i = 0 := by
  letI : Algebra ℤ_[p] Ω := (zpHom (p := p) (Ω := Ω)).toAlgebra
  have hsm : ∀ (m : ℤ_[p]) (x : Ω), m • x = zp Ω m * x := fun m x => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, zpHom_apply]
  haveI : NoZeroSMulDivisors ℤ_[p] Ω := ⟨fun {m x} hmx => by
    rw [hsm] at hmx
    rcases mul_eq_zero.1 hmx with h0 | h0
    · left; exact zpHom_injective hc (by rw [zpHom_apply, h0, map_zero])
    · right; exact h0⟩
  let S : Submodule ℤ_[p] Ω := Submodule.span ℤ_[p] (Set.range E)
  haveI : Module.Finite ℤ_[p] S := Module.Finite.span_of_finite _ (Set.finite_range E)
  haveI : Module.Free ℤ_[p] S := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis ℤ_[p] S
  have hE : ∀ k, E k ∈ S := fun k => Submodule.subset_span ⟨k, rfl⟩
  refine ⟨Module.Free.ChooseBasisIndex ℤ_[p] S, inferInstance, fun i => (b i : Ω),
    fun k i => b.repr ⟨E k, hE k⟩ i, ?_, ?_⟩
  · intro k
    have h2 := congrArg Subtype.val (b.sum_repr ⟨E k, hE k⟩)
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul, hsm] at h2
    exact h2.symm
  · intro v hv i
    have h0 : (∑ k, v k • (⟨E k, hE k⟩ : S)) = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul, hsm, Submodule.coe_zero]
      exact hv
    have := congrArg (fun s => b.repr s i) h0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at this
    exact this

theorem psi_C {T : Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ) (m : ℤ_[p]) :
    ψ (algebraMap (Lau p) (O0 p) (HahnSeries.C m)) = zp Ω m := by
  rw [h.sub (HahnSeries.C m) (HahnSeries.C m), zp, HahnSeries.C_apply]
  · intro i
    simp only [HahnSeries.C_apply, HahnSeries.coeff_single]
    by_cases hi : i = 0
    · simp [hi]
    · have : (p : ℤ) ^ n * i ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)) hi
      simp [hi, this]
  · intro r hr
    have : r ≠ 0 := by rintro rfl; exact hr (dvd_zero _)
    simp [HahnSeries.C_apply, HahnSeries.coeff_single, this]

theorem sum_psi_eq_zero (hc : IsClo p Ω) {T : Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ)
    {ι : Type} [Fintype ι] (E : ι → Ω) (A G : ι → Lau p) (φ : ℤ → ℤ_[p])
    (hA : ∀ r, ∑ k, E k * zp Ω ((A k).coeff r) = 0)
    (hG : ∀ k r, (G k).coeff r = φ r * (A k).coeff r) :
    ∑ k, E k * ψ (algebraMap (Lau p) (O0 p) (G k)) = 0 := by
  obtain ⟨κ, _, f, M, hE, hind⟩ := exists_coords hc E
  have hB : ∀ i, ∑ k, HahnSeries.C (M k i) * G k = 0 := by
    intro i
    apply HahnSeries.ext
    funext r
    rw [HahnSeries.coeff_sum]
    simp only [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, hG,
      HahnSeries.coeff_zero]
    have h1 := hind (fun k => (A k).coeff r) (by rw [← hA r]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _) i
    calc ∑ k, M k i * (φ r * (A k).coeff r) = φ r * ∑ k, (A k).coeff r * M k i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
      _ = 0 := by rw [h1, mul_zero]
  calc ∑ k, E k * ψ (algebraMap (Lau p) (O0 p) (G k))
      = ∑ i, f i * ψ (algebraMap (Lau p) (O0 p) (∑ k, HahnSeries.C (M k i) * G k)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_mul, psi_C h, hE, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
    _ = 0 := by simp only [hB, map_zero, mul_zero, Finset.sum_const_zero]

theorem thL_coeff (a : Lau p) (r : ℤ) : (thL a).coeff r = (r : ℤ_[p]) * a.coeff r := rfl

theorem ev_unique : ∀ (p : ℕ) [Fact p.Prime], ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ), ∀ (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (c : ℤ → Ω) (x x' y y' : Ω),
    Ev ψ c x x' → Ev ψ c y y' → x = y ∧ x' = y' := by
  intro p _ Ω _ _ hc T n ψ h c x x' y y' hx hy
  obtain ⟨d, e, a, -, hca, rfl, rfl⟩ := hx
  obtain ⟨d', e', a', -, hca', rfl, rfl⟩ := hy
  let E : Fin d ⊕ Fin d' → Ω := Sum.elim e e'
  let A : Fin d ⊕ Fin d' → Lau p := Sum.elim a (fun s => -a' s)
  have hA : ∀ r, ∑ k, E k * zp Ω ((A k).coeff r) = 0 := by
    intro r
    simp only [E, A, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, HahnSeries.coeff_neg, zp_neg,
      mul_neg, Finset.sum_neg_distrib]
    linear_combination hca' r - hca r
  have h1 := sum_psi_eq_zero hc h E A A (fun _ => 1) hA (fun k r => by simp)
  have h2 := sum_psi_eq_zero hc h E A (fun k => thL (A k)) (fun r => (r : ℤ_[p])) hA
    (fun k r => thL_coeff _ _)
  have thL_neg : ∀ b : Lau p, thL (-b) = - thL b := fun b => by
    apply HahnSeries.ext
    funext r
    simp only [thL_coeff, HahnSeries.coeff_neg, mul_neg]
  simp only [E, A, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, map_neg, mul_neg,
    Finset.sum_neg_distrib, thL_neg] at h1 h2
  exact ⟨sub_eq_zero.1 (by simpa [sub_eq_add_neg] using h1), sub_eq_zero.1 (by simpa [sub_eq_add_neg] using h2)⟩

end GlobalTheory.EvUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesAndDerivUniqueOfCoefficientsStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evalSeriesAndDeriv_unique_of_coefficients : ∀ (p : ℕ) [Fact p.Prime], ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ), ∀ (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (c : ℤ → Ω) (x x' y y' : Ω), Ev ψ c x x' → Ev ψ c y y' → x = y ∧ x' = y' := by
  first | exact @GlobalTheory.EvUniq.ev_unique | exact GlobalTheory.EvUniq.ev_unique | (intros; apply GlobalTheory.EvUniq.ev_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneHolomorphicMulEqZeroIff
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneHolomorphicMulEqZeroIff
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fn_mul_eq_zero_dom : ∀ f g : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g → (∀ τ, f τ * g τ = 0) → f = 0 ∨ g = 0 := by
  intro f g hf hg hfg
  have hF := (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hG := (UpperHalfPlane.mdifferentiable_iff.mp hg).analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hU : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  have hne : ({z : ℂ | 0 < z.im}).Nonempty := ⟨Complex.I, by simp⟩
  rcases AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero hF hG (fun z _ => by simp [Function.comp_apply, hfg]) hU with h | h
  · left
    funext τ
    have := h (τ : ℂ) τ.im_pos
    simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using this
  · right
    funext τ
    have := h (τ : ℂ) τ.im_pos
    simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneHolomorphicMulEqZeroIffStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff : ∀ f g : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g → (∀ τ, f τ * g τ = 0) → f = 0 ∨ g = 0 := by
  first | exact @GlobalTheory.fn_mul_eq_zero_dom | exact GlobalTheory.fn_mul_eq_zero_dom | (intros; apply GlobalTheory.fn_mul_eq_zero_dom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsComplexRingEquivExtendingSubfieldAut
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsComplexRingEquivExtendingSubfieldAut
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_ringEquiv_extend_of_embedding :
    ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (s : Ω ≃+* Ω), ∃ g : ℂ ≃+* ℂ, ∀ x, g (ε x) = ε (s x) := by
  intro Ω _ ε s
  letI : Algebra Ω ℂ := ε.toAlgebra
  obtain ⟨B, hB⟩ := exists_isTranscendenceBasis Ω ℂ
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hB
  let e := hB.1.aevalEquiv.symm.toRingEquiv.trans
    ((MvPolynomial.mapEquiv B s).trans hB.1.aevalEquiv.toRingEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv ℂ ℂ e, fun x => ?_⟩
  have h1 : ∀ y : Ω,
      algebraMap _ ℂ (hB.1.aevalEquiv (MvPolynomial.C y)) = ε y := fun y => by
    rw [hB.1.algebraMap_aevalEquiv, MvPolynomial.aeval_C]
    rfl
  conv_lhs => rw [← h1 x]
  rw [IsAlgClosure.equivOfEquiv_algebraMap, ← h1 (s x)]
  congr 1
  simp [e]

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsComplexRingEquivExtendingSubfieldAutStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complex_ringEquiv_extending_subfield_aut : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (s : Ω ≃+* Ω), ∃ g : ℂ ≃+* ℂ, ∀ x, g (ε x) = ε (s x) := by
  first | exact @GlobalTheory.FN.exists_ringEquiv_extend_of_embedding | exact GlobalTheory.FN.exists_ringEquiv_extend_of_embedding | (intros; apply GlobalTheory.FN.exists_ringEquiv_extend_of_embedding <;> assumption)
end
end
