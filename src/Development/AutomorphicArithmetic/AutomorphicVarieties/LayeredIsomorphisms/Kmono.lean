module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Kmono
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.kmono :
    ∀ C C' : ℝ, C ≤ C' → LemmaK C → LemmaK C' := by
  intro C C' hCC hK
  unfold LemmaK at hK ⊢
  intro l _ L Ω _ _ _ _ _ D hL hMu e he
  obtain ⟨hf, hb⟩ := hK l L Ω D hL hMu e he
  refine ⟨hf, hb.trans ?_⟩
  unfold kBound
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right
  · apply Real.rpow_le_rpow_of_exponent_le _ hCC
    have hn : 0 < Module.finrank ℚ L := Module.finrank_pos
    have h1 : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
    have h2 : (1 : ℝ) ≤ (Module.finrank ℚ L : ℝ) := by exact_mod_cast hn
    nlinarith
  · rcases Nat.eq_zero_or_pos (discr L).natAbs with h0 | h0
    · rw [h0]
      simp
    · apply Real.log_nonneg
      have : (1 : ℝ) ≤ ((discr L).natAbs : ℝ) := by exact_mod_cast h0
      linarith
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Rootdeg
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.rootdeg :
    ∀ (L : Type) [Field L] [NumberField L] (l k : ℕ), l.Prime → (∃ ζ : L, IsPrimitiveRoot ζ (l ^ k)) →
      l ^ k ≤ 2 * Module.finrank ℚ L := by
  intro L _ _ l k hl ⟨ζ, hζ⟩
  have hpos : 0 < l ^ k := pow_pos hl.pos k
  have ht : (l ^ k).totient ≤ Module.finrank ℚ L := by
    have h1 := hζ.lcm_totient_le_finrank (K := ℚ) hζ
      (by rw [Nat.lcm_self]; exact Polynomial.cyclotomic.irreducible_rat hpos)
    rwa [Nat.lcm_self] at h1
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [pow_zero, Nat.totient_one] at ht ⊢
    omega
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Nat.totient_prime_pow hl hk, Nat.add_sub_cancel] at ht
    have h2 : l ≤ 2 * (l - 1) := by
      have := hl.two_le
      omega
    calc l ^ (m + 1) = l ^ m * l := pow_succ l m
      _ ≤ l ^ m * (2 * (l - 1)) := Nat.mul_le_mul_left _ h2
      _ = 2 * (l ^ m * (l - 1)) := by ring
      _ ≤ 2 * Module.finrank ℚ L := Nat.mul_le_mul_left _ ht
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Imports
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.disc :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), 0 < N → Nonempty (L →ₐ[ℚ] CyclotomicField N ℚ) →
      Real.log ((discr L).natAbs : ℝ) ≤ (Module.finrank ℚ L : ℝ) * Real.log (N : ℝ) := by
  intro L _ _ N hN hφ
  obtain ⟨φ⟩ := hφ
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero (N : ℚ) := ⟨by exact_mod_cast hN.ne'⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  letI : Algebra L (CyclotomicField N ℚ) := φ.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ L (CyclotomicField N ℚ) :=
    IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)
  have key := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow L (𝓞 L)
    (CyclotomicField N ℚ) (𝓞 (CyclotomicField N ℚ))
  have hdC := IsCyclotomicExtension.Rat.natAbs_discr N (CyclotomicField N ℚ)
  have hfin : Module.finrank ℚ (CyclotomicField N ℚ) = N.totient :=
    IsCyclotomicExtension.finrank (CyclotomicField N ℚ) (Polynomial.cyclotomic.irreducible_rat hN)
  have htow := Module.finrank_mul_finrank ℚ L (CyclotomicField N ℚ)
  have hm : 0 < Module.finrank L (CyclotomicField N ℚ) := Module.finrank_pos
  have hne := NumberField.discr_ne_zero (CyclotomicField N ℚ)
  have hdL := NumberField.discr_ne_zero L
  have h1 : (discr L).natAbs ^ Module.finrank L (CyclotomicField N ℚ)
      ≤ (discr (CyclotomicField N ℚ)).natAbs := by
    rw [key]
    have h0 : Ideal.absNorm (differentIdeal (𝓞 L) (𝓞 (CyclotomicField N ℚ))) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at key
      exact hne (Int.natAbs_eq_zero.mp key)
    exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero h0)
  have h2 : (discr (CyclotomicField N ℚ)).natAbs
      ≤ (N ^ Module.finrank ℚ L) ^ Module.finrank L (CyclotomicField N ℚ) := by
    rw [hdC, ← pow_mul, htow, hfin]
    exact Nat.div_le_self _ _
  have h3 : (discr L).natAbs ≤ N ^ Module.finrank ℚ L :=
    (Nat.pow_le_pow_iff_left hm.ne').mp (h1.trans h2)
  have hd0 : 0 < (discr L).natAbs := Int.natAbs_pos.mpr hdL
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast hd0)
  exact_mod_cast h3
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Logs
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.logs :
    (∀ (l : ℕ) (J Ct X x : ℝ), 2 ≤ l → 0 < J → 0 ≤ Ct → 1 ≤ X → X ^ (1 / J) ≤ x →
        ((Nat.log l ⌊X ^ Ct⌋₊ : ℕ) : ℝ) ≤ 2 * Ct * J * Real.log x) ∧
      (∀ (J eps X x : ℝ), 0 < J → 0 < eps → 1 ≤ X → X ^ (1 / J) ≤ x → X ^ (eps / (4 * J)) ≤ x ^ (eps / 4)) ∧
      (∀ (e : ℕ) (A1 x : ℝ), 1 ≤ x → (2 : ℝ) ^ e ≤ x ^ A1 → (e : ℝ) + 2 ≤ (2 * |A1| + 2) * (1 + Real.log x)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro l J Ct X x hl hJ hCt hX hx
    have hX0 : 0 < X := by linarith
    have hx1 : 1 ≤ x := le_trans (Real.one_le_rpow hX (by positivity)) hx
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hlogX : Real.log X ≤ J * Real.log x := by
      have h1 : Real.log (X ^ (1 / J)) ≤ Real.log x :=
        Real.log_le_log (Real.rpow_pos_of_pos hX0 _) hx
      rw [Real.log_rpow hX0] at h1
      have h2 : J * ((1 / J) * Real.log X) = Real.log X := by field_simp
      calc Real.log X = J * ((1 / J) * Real.log X) := h2.symm
        _ ≤ J * Real.log x := mul_le_mul_of_nonneg_left h1 hJ.le
    have hl2 : (1:ℝ) / 2 < Real.log l := by
      have h3 : Real.log 2 ≤ Real.log l := Real.log_le_log (by norm_num) (by exact_mod_cast hl)
      have h4 := Real.log_two_gt_d9
      linarith
    rcases Nat.eq_zero_or_pos ⌊X ^ Ct⌋₊ with h0 | hpos
    · rw [h0, Nat.log_zero_right, Nat.cast_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCt) hJ.le) hlogx
    · have hpow : (l:ℝ) ^ (Nat.log l ⌊X ^ Ct⌋₊) ≤ X ^ Ct := by
        have h1 : l ^ (Nat.log l ⌊X ^ Ct⌋₊) ≤ ⌊X ^ Ct⌋₊ := Nat.pow_log_le_self l hpos.ne'
        have h2 : ((⌊X ^ Ct⌋₊ : ℕ) : ℝ) ≤ X ^ Ct := Nat.floor_le (Real.rpow_nonneg hX0.le _)
        calc (l:ℝ) ^ (Nat.log l ⌊X ^ Ct⌋₊) = ((l ^ (Nat.log l ⌊X ^ Ct⌋₊) : ℕ) : ℝ) :=
              (Nat.cast_pow l _).symm
          _ ≤ ((⌊X ^ Ct⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
          _ ≤ X ^ Ct := h2
      have hl0 : (0:ℝ) < l := by exact_mod_cast (by omega : 0 < l)
      have hlog := Real.log_le_log (pow_pos hl0 _) hpow
      rw [Real.log_pow, Real.log_rpow hX0] at hlog
      have hk0 : (0:ℝ) ≤ (Nat.log l ⌊X ^ Ct⌋₊ : ℕ) := Nat.cast_nonneg _
      have hk : ((Nat.log l ⌊X ^ Ct⌋₊ : ℕ) : ℝ) ≤ 2 * (((Nat.log l ⌊X ^ Ct⌋₊ : ℕ) : ℝ) * Real.log l) := by
        nlinarith [mul_le_mul_of_nonneg_left hl2.le hk0]
      nlinarith [mul_le_mul_of_nonneg_left hlogX hCt]
  · intro J eps X x hJ heps hX hx
    have hX0 : 0 ≤ X := by linarith
    have h1 : X ^ (eps / (4 * J)) = (X ^ (1 / J)) ^ (eps / 4) := by
      rw [← Real.rpow_mul hX0]
      congr 1
      field_simp
    rw [h1]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hX0 _) hx (by positivity)
  · intro e A1 x hx h
    have hx0 : 0 < x := by linarith
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
    have hlog := Real.log_le_log (by positivity) h
    rw [Real.log_pow, Real.log_rpow hx0] at hlog
    have h2 := Real.log_two_gt_d9
    have habs : A1 * Real.log x ≤ |A1| * Real.log x :=
      mul_le_mul_of_nonneg_right (le_abs_self A1) hlogx
    have he0 : (0:ℝ) ≤ e := Nat.cast_nonneg e
    have he : (e:ℝ) ≤ 2 * (e * Real.log 2) := by nlinarith
    nlinarith [abs_nonneg A1, mul_nonneg (abs_nonneg A1) hlogx]
end
