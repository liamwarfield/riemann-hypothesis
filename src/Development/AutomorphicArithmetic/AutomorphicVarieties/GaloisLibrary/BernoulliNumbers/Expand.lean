module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Expand
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_expand :
    ∀ (N k a : ℕ), 0 < N → bcoef N k a = ∑ j ∈ range (k + 1), (k.choose j : ℚ) * bernoulli j * (N : ℚ) ^ ((j : ℤ) - 1) * (a : ℚ) ^ (k - j) := by
  intro N k a hN
  have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  simp only [bcoef]
  rw [Polynomial.bernoulli, Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [Polynomial.eval_monomial, div_pow]
  have hsplit : (N : ℚ) ^ ((k : ℤ) - 1) = (N : ℚ) ^ ((j : ℤ) - 1) * (N : ℚ) ^ ((k - j : ℕ) : ℤ) := by
    rw [← zpow_add₀ hN']
    congr 1
    push_cast [hjk]
    ring
  rw [hsplit, zpow_natCast]
  have hp : (N : ℚ) ^ (k - j) ≠ 0 := pow_ne_zero _ hN'
  field_simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Parity
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_parity :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] {N : ℕ} [NeZero N] (k : ℕ) (χ : DirichletCharacter Ω N), (χ.toUnitHom.ker ∈ parKer N k ↔ χ (-1) = (-1) ^ k) ∧ (χ.primitiveCharacter (-1) = χ (-1)) := by
  intro Ω _ _ N _ k χ
  have hne : (-1 : Ω) ≠ 1 := by norm_num
  refine ⟨?_, ?_⟩
  · have hval : χ.toUnitHom (-1) = 1 ↔ χ (-1) = 1 := by
      rw [← Units.val_inj, MulChar.coe_toUnitHom, Units.val_neg, Units.val_one, Units.val_one]
    show ((-1 : (ZMod N)ˣ) ∈ χ.toUnitHom.ker ↔ Even k) ↔ _
    rw [MonoidHom.mem_ker, hval]
    rcases Nat.even_or_odd k with hk | hk
    · rw [hk.neg_one_pow]
      simp [hk]
    · rw [hk.neg_one_pow]
      have hk' : ¬ Even k := Nat.not_even_iff_odd.mpr hk
      rcases χ.even_or_odd with h | h
      · have h1 : χ (-1) = 1 := h
        simp [hk', h1, hne.symm]
      · have h1 : χ (-1) = -1 := h
        simp [hk', h1, hne]
  · have hd := DirichletCharacter.conductor_dvd_level χ
    have h := DirichletCharacter.changeLevel_eq_cast_of_dvd χ.primitiveCharacter hd (-1)
    rw [DirichletCharacter.changeLevel_primitiveCharacter, Units.val_neg, Units.val_one,
      ZMod.cast_neg hd, ZMod.cast_one hd] at h
    exact h.symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Sumicc
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_sumicc :
    ∀ {M : Type} [AddCommMonoid M] {N : ℕ} [NeZero N] (G : ZMod N → M), ∑ a ∈ Icc 1 N, G (a : ZMod N) = ∑ a : ZMod N, G a := by
  intro M _ N _ G
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  refine Finset.sum_nbij' (fun a : ℕ => (a : ZMod N)) (fun x : ZMod N => if x.val = 0 then N else x.val)
    ?_ ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_univ _
  · intro x _
    have hx := ZMod.val_lt x
    refine Finset.mem_Icc.2 ?_
    split_ifs with h0
    · exact ⟨hN, le_rfl⟩
    · exact ⟨Nat.pos_of_ne_zero h0, hx.le⟩
  · intro a ha
    have ha' := Finset.mem_Icc.1 ha
    simp only [ZMod.val_natCast]
    rcases Nat.lt_or_ge a N with h | h
    · rw [Nat.mod_eq_of_lt h, if_neg (by omega)]
    · have hEq : a = N := by omega
      subst hEq
      simp
  · intro x _
    split_ifs with h0
    · rw [ZMod.natCast_self]
      exact ((ZMod.val_eq_zero x).1 h0).symm
    · exact ZMod.natCast_zmod_val x
  · intro a _
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primden
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_primden :
    ∀ (k j : ℕ), j ≤ k → ∃ z : ℤ, (primorial (k + 1) : ℚ) * bernoulli j = z := by
  intro k j hjk
  have hdvd : ∀ p : ℕ, p.Prime → p ≤ k + 1 → p ∣ primorial (k + 1) := by
    intro p hp hpk
    exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hp⟩)
  rcases Nat.even_or_odd j with ⟨m, rfl⟩ | hodd
  · obtain ⟨z0, hz0⟩ := Bernoulli.vonStaudt_clausen m
    have h2 : m + m = 2 * m := by ring
    rw [h2]
    have hB : bernoulli (2 * m) = (z0 : ℚ) - ∑ p ∈ range (2 * m + 2) with Nat.Prime p ∧ p - 1 ∣ 2 * m, (1 : ℚ) / p := by
      rw [hz0]; ring
    refine ⟨(primorial (k + 1) : ℤ) * z0 - ∑ p ∈ range (2 * m + 2) with Nat.Prime p ∧ p - 1 ∣ 2 * m, ((primorial (k + 1) / p : ℕ) : ℤ), ?_⟩
    rw [Int.cast_sub, Int.cast_mul, Int.cast_sum]
    simp only [Int.cast_natCast]
    rw [hB, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter, Finset.mem_range] at hp
    have hpd : p ∣ primorial (k + 1) := hdvd p hp.2.1 (by omega)
    rw [Nat.cast_div hpd (Nat.cast_ne_zero.2 hp.2.1.ne_zero)]
    ring
  · rcases Nat.lt_or_ge 1 j with h1 | h1
    · exact ⟨0, by rw [bernoulli_eq_zero_of_odd hodd h1]; simp⟩
    · have hj : j = 1 := by
        obtain ⟨r, rfl⟩ := hodd
        omega
      subst hj
      obtain ⟨t, ht⟩ := hdvd 2 Nat.prime_two (by omega)
      refine ⟨-(t : ℤ), ?_⟩
      rw [bernoulli_one, ht]
      push_cast
      ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Condmap
open Finset UpperTheory.V.Bern

private theorem change_level_value_eq {R S : Type} [CommRing R] [CommRing S] {N : ℕ} [NeZero N] (f : R →+* S)
    {d e : ℕ} (hde : e = d) (hd : d ∣ N) (he : e ∣ N) (φ : DirichletCharacter R d) (ψ : DirichletCharacter S e)
    (h : DirichletCharacter.changeLevel he ψ = (DirichletCharacter.changeLevel hd φ).ringHomComp f) (a : ℕ) :
    ψ (a : ZMod e) = f (φ (a : ZMod d)) := by
  subst hde
  have hc : (DirichletCharacter.changeLevel hd φ).ringHomComp f = DirichletCharacter.changeLevel hd (φ.ringHomComp f) := by
    ext u
    simp [MulChar.ringHomComp_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd]
  have hψ : ψ = φ.ringHomComp f := DirichletCharacter.changeLevel_injective hd (h.trans hc)
  subst hψ
  simp [MulChar.ringHomComp_apply]

theorem UpperTheory.V.Bern.b_condmap :
    ∀ {R S : Type} [CommRing R] [CommRing S] {N : ℕ} [NeZero N] (f : R →+* S), Function.Injective f → ∀ χ : DirichletCharacter R N, DirichletCharacter.conductor (χ.ringHomComp f) = χ.conductor ∧ (∀ a : ℕ, primVal (χ.ringHomComp f) a = f (primVal χ a)) ∧ (χ.ringHomComp f).toUnitHom.ker = χ.toUnitHom.ker := by
  intro R S _ _ N _ f hf χ
  have hker : (χ.ringHomComp f).toUnitHom.ker = χ.toUnitHom.ker := by
    ext u
    simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one, MulChar.ringHomComp_apply]
    constructor
    · intro h
      exact hf (h.trans (map_one f).symm)
    · intro h
      rw [h, map_one]
  have hset : DirichletCharacter.conductorSet (χ.ringHomComp f) = χ.conductorSet := by
    ext d
    simp only [DirichletCharacter.mem_conductorSet_iff]
    constructor
    · intro h
      have h' := (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mp h
      rw [hker] at h'
      exact (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mpr h'
    · intro h
      have h' := (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mp h
      rw [← hker] at h'
      exact (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mpr h'
  have hcond : DirichletCharacter.conductor (χ.ringHomComp f) = χ.conductor := by
    unfold DirichletCharacter.conductor
    rw [hset]
  refine ⟨hcond, ?_, hker⟩
  intro a
  unfold primVal
  exact change_level_value_eq f hcond χ.conductor_dvd_level (DirichletCharacter.conductor_dvd_level (χ.ringHomComp f))
    χ.primitiveCharacter (DirichletCharacter.primitiveCharacter (χ.ringHomComp f))
    (by rw [DirichletCharacter.changeLevel_primitiveCharacter, DirichletCharacter.changeLevel_primitiveCharacter]) a
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primval
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_primval :
    ∀ {R : Type} [CommRing R] {N : ℕ} [NeZero N] (χ : DirichletCharacter R N) (x : ZMod χ.conductor), χ.primitiveCharacter x = 0 ∨ ∃ u : (ZMod N)ˣ, χ.primitiveCharacter x = χ u := by
  intro R _ N _ χ x
  by_cases hx : IsUnit x
  · right
    obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective χ.conductor_dvd_level hx.unit
    refine ⟨u, ?_⟩
    conv_rhs => rw [← χ.changeLevel_primitiveCharacter]
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, ← ZMod.unitsMap_val, hu]
    · simp
    · exact χ.conductor_dvd_level
  · left
    exact MulChar.map_nonunit _ hx
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Sumval
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_sumval :
    ∀ (M : ℤ), M ≠ 0 → ∀ T : Finset ℕ, (∀ l ∈ T, l.Prime) → ∑ l ∈ T, (padicValInt l M : ℝ) * Real.log l ≤ Real.log |(M : ℝ)| := by
  intro M hM T hT
  have hN : M.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hM
  have hlog : Real.log |(M : ℝ)| = Real.log (M.natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hlog, Real.log_nat_eq_sum_factorization, Finsupp.sum]
  calc ∑ l ∈ T, (padicValInt l M : ℝ) * Real.log l
      = ∑ l ∈ T, (M.natAbs.factorization l : ℝ) * Real.log l := by
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [Nat.factorization_def _ (hT l hl)]
        rfl
    _ = ∑ l ∈ T.filter (· ∈ M.natAbs.factorization.support),
          (M.natAbs.factorization l : ℝ) * Real.log l := by
        refine (Finset.sum_filter_of_ne fun l _ h => ?_).symm
        rw [Finsupp.mem_support_iff]
        intro h0
        apply h
        simp [h0]
    _ ≤ ∑ p ∈ M.natAbs.factorization.support,
          (M.natAbs.factorization p : ℝ) * Real.log p := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => ?_
        · intro x hx
          exact (Finset.mem_filter.mp hx).2
        · exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BOneSum
open Finset UpperTheory.V.Bern

private theorem UpperTheory.V.Bern.b_one_sum {R : Type} [AddCommMonoid R] {N : ℕ} [NeZero N] (Φ : ZMod N → R) :
    ∑ a ∈ Icc 1 N, Φ (a : ZMod N) = ∑ a : ZMod N, Φ a := by
  refine Finset.sum_nbij' (fun a : ℕ => (a : ZMod N)) (fun b => (b - 1).val + 1) ?_ ?_ ?_ ?_ ?_
  · intro a _
    simp
  · intro b _
    simp only [Finset.mem_Icc]
    exact ⟨by omega, ZMod.val_lt _⟩
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
    have hk : k < N := by omega
    simp [Nat.cast_add, ZMod.val_cast_of_lt hk]
  · intro b _
    push_cast
    simp
  · intro a _
    rfl

theorem UpperTheory.V.Bern.b_one :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N : ℕ} [NeZero N] (Φ : ZMod N → R), ∑ a : ZMod N, Φ a = 0 → (N : R) * genB 1 Φ = ∑ a ∈ Icc 1 N, Φ (a : ZMod N) * (a : R) := by
  intro R _ _ N _ Φ hΦ
  simp only [genB, bcoef, Polynomial.bernoulli_one]
  have hs : ∑ a ∈ Icc 1 N, Φ (a : ZMod N) = 0 := (UpperTheory.V.Bern.b_one_sum Φ).trans hΦ
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have key : ∀ x : ℕ, (N : R) * (Φ (x : ZMod N) * algebraMap ℚ R ((N : ℚ) ^ ((1 : ℕ) - 1 : ℤ) * Polynomial.eval ((x : ℚ) / N) (Polynomial.X - Polynomial.C 2⁻¹))) = Φ (x : ZMod N) * (x : R) - algebraMap ℚ R ((N : ℚ) / 2) * Φ (x : ZMod N) := by
    intro x
    have e : (N : ℚ) * ((N : ℚ) ^ ((1 : ℕ) - 1 : ℤ) * Polynomial.eval ((x : ℚ) / N) (Polynomial.X - Polynomial.C 2⁻¹)) = (x : ℚ) - (N : ℚ) / 2 := by
      simp
      field_simp
    calc (N : R) * (Φ (x : ZMod N) * algebraMap ℚ R ((N : ℚ) ^ ((1 : ℕ) - 1 : ℤ) * Polynomial.eval ((x : ℚ) / N) (Polynomial.X - Polynomial.C 2⁻¹)))
        = Φ (x : ZMod N) * algebraMap ℚ R ((N : ℚ) * ((N : ℚ) ^ ((1 : ℕ) - 1 : ℤ) * Polynomial.eval ((x : ℚ) / N) (Polynomial.X - Polynomial.C 2⁻¹))) := by
          rw [map_mul (algebraMap ℚ R) (N : ℚ), map_natCast]
          ring
      _ = _ := by
          rw [e, map_sub, map_natCast]
          ring
  rw [Finset.mul_sum]
  simp_rw [key]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hs, mul_zero, sub_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Charbij
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_charbij :
    ∀ {N : ℕ} [NeZero N] {K Ω : Type} [Field K] [Field Ω] [HasEnoughRootsOfUnity K (Monoid.exponent (ZMod N)ˣ)] (f : K →+* Ω) (P : Set (Subgroup (ZMod N)ˣ)), Set.BijOn (fun χ : DirichletCharacter K N => (χ.ringHomComp f : DirichletCharacter Ω N)) (charSet K P) (charSet Ω P) := by
  intro N _ K Ω _ _ _ f P
  have hf : Function.Injective f := f.injective
  have hker : ∀ χ : DirichletCharacter K N, (MulChar.toUnitHom (χ.ringHomComp f)).ker = (MulChar.toUnitHom χ).ker := by
    intro χ
    ext u
    simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one, MulChar.ringHomComp_apply]
    constructor
    · intro h
      exact hf (h.trans (map_one f).symm)
    · intro h
      rw [h, map_one]
  refine ⟨?_, ?_, ?_⟩
  · intro χ hχ
    simp only [charSet, Set.mem_setOf_eq] at hχ ⊢
    rw [hker]
    exact hχ
  · intro χ₁ _ χ₂ _ h
    ext u
    have h' := congrArg (fun ψ : DirichletCharacter Ω N => ψ u) h
    simp only [MulChar.ringHomComp_apply] at h'
    exact hf h'
  · intro χ' hχ'
    have he : NeZero (Monoid.exponent (ZMod N)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (Monoid.exponent (ZMod N)ˣ)
    have hne : (primitiveRoots (Monoid.exponent (ZMod N)ˣ) K).Nonempty :=
      ⟨ζ, (mem_primitiveRoots (NeZero.pos _)).mpr hζ⟩
    have hmem : ∀ u, MulChar.toUnitHom χ' u ∈ rootsOfUnity (Monoid.exponent (ZMod N)ˣ) Ω := by
      intro u
      rw [mem_rootsOfUnity, ← map_pow, Monoid.pow_exponent_eq_one, map_one]
    let ψ : (ZMod N)ˣ →* Kˣ := (rootsOfUnity (Monoid.exponent (ZMod N)ˣ) K).subtype.comp
      ((rootsOfUnityEquivOfPrimitiveRoots hf hne).symm.toMonoidHom.comp
        ((MulChar.toUnitHom χ').codRestrict _ hmem))
    have hcomp : (MulChar.ofUnitHom ψ).ringHomComp f = χ' := by
      ext u
      rw [MulChar.ringHomComp_apply, MulChar.ofUnitHom_coe]
      show f (((rootsOfUnityEquivOfPrimitiveRoots hf hne).symm ⟨MulChar.toUnitHom χ' u, hmem u⟩ : Kˣ) : K) = χ' u
      rw [rootsOfUnityEquivOfPrimitiveRoots_symm_apply]
      simp [MulChar.coe_toUnitHom]
    refine ⟨MulChar.ofUnitHom ψ, ?_, hcomp⟩
    simp only [charSet, Set.mem_setOf_eq] at hχ' ⊢
    rw [← hker, hcomp]
    exact hχ'
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BRaabe
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bcoef
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_egf :
    ∀ (N a : ℕ), 0 < N → (PowerSeries.mk fun k => bcoef N k a / (k.factorial : ℚ)) * (PowerSeries.rescale (N : ℚ) (PowerSeries.exp ℚ) - 1) = PowerSeries.X * PowerSeries.rescale (a : ℚ) (PowerSeries.exp ℚ) := by
  intro N a hN
  have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have h := congrArg (PowerSeries.rescale (N : ℚ)) (Polynomial.bernoulli_generating_function ((a : ℚ) / N))
  rw [map_mul, map_mul, map_sub, map_one, PowerSeries.rescale_mk, PowerSeries.rescale_X,
    PowerSeries.rescale_rescale] at h
  have hc : ((a : ℚ) / N) * N = a := by field_simp
  rw [hc] at h
  beta_reduce at h
  have hmk : (PowerSeries.mk fun k => bcoef N k a / (k.factorial : ℚ)) =
      PowerSeries.C (1 / (N : ℚ)) * PowerSeries.mk (fun n => (N : ℚ) ^ n *
        (Polynomial.aeval ((a : ℚ) / N)) ((1 / (n.factorial : ℚ)) • Polynomial.bernoulli n)) := by
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    simp only [bcoef, map_smul, Polynomial.coe_aeval_eq_eval, smul_eq_mul]
    rw [zpow_sub_one₀ hN', zpow_natCast]
    have hf : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
    field_simp
  rw [hmk, mul_assoc, h, ← mul_assoc, ← mul_assoc, ← map_mul, one_div_mul_cancel hN', map_one, one_mul]
end

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_raabe :
    ∀ (N m k a : ℕ), 0 < N → 0 < m → bcoef N k a = ∑ j ∈ range m, bcoef (N * m) k (a + j * N) := by
  intro N m k a hN hm
  let F : ℕ → ℕ → PowerSeries ℚ := fun M c => PowerSeries.mk fun i => bcoef M i c / (i.factorial : ℚ)
  let y : PowerSeries ℚ := PowerSeries.rescale (N : ℚ) (PowerSeries.exp ℚ)
  let E : PowerSeries ℚ := PowerSeries.rescale ((N * m : ℕ) : ℚ) (PowerSeries.exp ℚ) - 1
  have hpow : ∀ j : ℕ, y ^ j = PowerSeries.rescale ((j : ℚ) * N) (PowerSeries.exp ℚ) := by
    intro j
    simp only [y]
    rw [← map_pow, PowerSeries.exp_pow_eq_rescale_exp, PowerSeries.rescale_rescale]
  have hE : E = (∑ j ∈ range m, y ^ j) * (y - 1) := by
    rw [geom_sum_mul, hpow]
    simp only [E]
    push_cast
    rw [mul_comm (m : ℚ)]
  have hE0 : E ≠ 0 := by
    intro h
    have h1 := congrArg (PowerSeries.coeff 1) h
    simp [E, PowerSeries.coeff_rescale, PowerSeries.coeff_exp] at h1
    rcases h1 with h1 | h1
    · exact hN.ne' h1
    · exact hm.ne' h1
  suffices h : F N a = ∑ j ∈ range m, F (N * m) (a + j * N) by
    have h2 := congrArg (PowerSeries.coeff k) h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h2
    simp only [F, PowerSeries.coeff_mk] at h2
    rw [← Finset.sum_div, div_left_inj' (by positivity)] at h2
    exact h2
  apply mul_right_cancel₀ hE0
  calc F N a * E = F N a * (y - 1) * ∑ j ∈ range m, y ^ j := by rw [hE]; ring
    _ = PowerSeries.X * PowerSeries.rescale (a : ℚ) (PowerSeries.exp ℚ) * ∑ j ∈ range m, y ^ j := by
        rw [b_egf N a hN]
    _ = ∑ j ∈ range m, PowerSeries.X * PowerSeries.rescale ((a + j * N : ℕ) : ℚ) (PowerSeries.exp ℚ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hpow, mul_assoc, PowerSeries.exp_mul_exp_eq_exp_add]
        push_cast
        rfl
    _ = ∑ j ∈ range m, F (N * m) (a + j * N) * E := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [b_egf (N * m) (a + j * N) (Nat.mul_pos hN hm)]
    _ = (∑ j ∈ range m, F (N * m) (a + j * N)) * E := by rw [Finset.sum_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BUpper
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Polybound
open Finset UpperTheory.V.Bern

private theorem polybound_cast (k : ℕ) (x : ℚ) :
    (((Polynomial.bernoulli k).eval x : ℚ) : ℝ) = bernoulliFun k (x : ℝ) := by
  rw [bernoulliFun, Polynomial.eval_map_algebraMap, ← eq_ratCast (algebraMap ℚ ℝ) x,
    Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, eq_ratCast]

private theorem polybound_norm_fourier (n : ℤ) (y : UnitAddCircle) : ‖fourier n y‖ = 1 := by
  rw [fourier_apply]; exact Circle.norm_coe _

private theorem polybound_big {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (2 * Real.pi) ^ k / (k.factorial : ℝ) * |bernoulliFun k x| ≤ 4 := by
  have hs := hasSum_one_div_nat_pow_mul_fourier hk hx
  have h2 : ∀ (m : ℤ) (y : UnitAddCircle), ‖fourier m y + (-1) ^ k * fourier (-m) y‖ ≤ 2 := by
    intro m y
    calc _ ≤ ‖fourier m y‖ + ‖(-1 : ℂ) ^ k * fourier (-m) y‖ := norm_add_le _ _
      _ = 2 := by
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, polybound_norm_fourier,
          polybound_norm_fourier]
        norm_num
  have hbound : ‖-(2 * (Real.pi : ℂ) * Complex.I) ^ k / (k.factorial : ℂ) * (bernoulliFun k x : ℂ)‖
      ≤ 2 * (Real.pi ^ 2 / 6) := by
    rw [← hs.tsum_eq]
    refine tsum_of_norm_bounded (hasSum_zeta_two.mul_left 2) fun n ↦ ?_
    rw [norm_mul]
    have h1 : ‖1 / (n : ℂ) ^ k‖ ≤ 1 / (n : ℝ) ^ 2 := by
      rw [norm_div, norm_one, norm_pow, Complex.norm_natCast]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [zero_pow (by omega : k ≠ 0)]
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hn1 hk)
    calc _ ≤ 1 / (n : ℝ) ^ 2 * 2 := mul_le_mul h1 (h2 _ _) (norm_nonneg _) (by positivity)
      _ = 2 * (1 / (n : ℝ) ^ 2) := mul_comm _ _
  have hnorm : ‖-(2 * (Real.pi : ℂ) * Complex.I) ^ k / (k.factorial : ℂ) * (bernoulliFun k x : ℂ)‖
      = (2 * Real.pi) ^ k / (k.factorial : ℝ) * |bernoulliFun k x| := by
    rw [norm_mul, norm_div, norm_neg, norm_pow, norm_mul, norm_mul, Complex.norm_I,
      Complex.norm_real, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one, Complex.norm_two]
  rw [← hnorm]
  refine hbound.trans ?_
  nlinarith [Real.pi_pos, Real.pi_lt_d2]

theorem UpperTheory.V.Bern.b_polybound :
    ∀ (k : ℕ) (x : ℚ), 0 ≤ x → x ≤ 1 → |(((Polynomial.bernoulli k).eval x : ℚ) : ℝ)| ≤ 4 * (k.factorial : ℝ) / (2 * Real.pi) ^ k := by
  intro k x h0 h1
  have hx0 : (0 : ℝ) ≤ x := by exact_mod_cast h0
  have hx1 : (x : ℝ) ≤ 1 := by exact_mod_cast h1
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rcases lt_or_ge k 2 with hk | hk
  · interval_cases k
    · simp [Polynomial.bernoulli_zero]
    · simp only [Polynomial.bernoulli_one, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
        Nat.factorial_one, Nat.cast_one, pow_one]
      have key : |(x : ℝ) - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      have : (1 : ℝ) / 2 ≤ 4 * 1 / (2 * Real.pi) := by
        rw [le_div_iff₀ hpi]
        nlinarith [Real.pi_lt_d2]
      linarith
  · have hb := polybound_big hk (x := (x : ℝ)) ⟨hx0, hx1⟩
    rw [polybound_cast]
    have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    rw [div_mul_eq_mul_div, div_le_iff₀ hf] at hb
    rw [le_div_iff₀ (pow_pos hpi k)]
    linarith [mul_comm (|bernoulliFun k x|) ((2 * Real.pi) ^ k)]
end

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_upper :
    ∀ {N : ℕ} (k : ℕ) (Φ : ZMod N → ℂ), 0 < N → (∀ a, ‖Φ a‖ ≤ 1) → ‖genB k Φ‖ ≤ 4 * (N : ℝ) ^ k * (k.factorial : ℝ) / (2 * Real.pi) ^ k := by
  intro N k Φ hN hΦ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set C : ℝ := 4 * (k.factorial : ℝ) / (2 * Real.pi) ^ k with hC
  have hterm : ∀ a ∈ Icc 1 N,
      ‖Φ (a : ZMod N) * algebraMap ℚ ℂ (bcoef N k a)‖ ≤ (N : ℝ) ^ ((k : ℤ) - 1) * C := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    have hx0 : (0 : ℚ) ≤ (a : ℚ) / N := by positivity
    have hx1 : (a : ℚ) / N ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hN)]
      exact_mod_cast ha.2
    have hb : ‖algebraMap ℚ ℂ (bcoef N k a)‖ =
        (N : ℝ) ^ ((k : ℤ) - 1) * |((Polynomial.eval ((a : ℚ) / N) (Polynomial.bernoulli k) : ℚ) : ℝ)| := by
      rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs, bcoef]
      push_cast
      rw [abs_mul, abs_of_pos (zpow_pos hNr _)]
    rw [norm_mul, hb]
    have hp := b_polybound k ((a : ℚ) / N) hx0 hx1
    calc ‖Φ (a : ZMod N)‖ * ((N : ℝ) ^ ((k : ℤ) - 1) *
          |((Polynomial.eval ((a : ℚ) / N) (Polynomial.bernoulli k) : ℚ) : ℝ)|)
        ≤ 1 * ((N : ℝ) ^ ((k : ℤ) - 1) * C) := by
          apply mul_le_mul (hΦ _) _ (by positivity) zero_le_one
          exact mul_le_mul_of_nonneg_left hp (zpow_pos hNr _).le
      _ = (N : ℝ) ^ ((k : ℤ) - 1) * C := one_mul _
  calc ‖genB k Φ‖ ≤ ∑ a ∈ Icc 1 N, ‖Φ (a : ZMod N) * algebraMap ℚ ℂ (bcoef N k a)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ a ∈ Icc 1 N, (N : ℝ) ^ ((k : ℤ) - 1) * C := Finset.sum_le_sum hterm
    _ = 4 * (N : ℝ) ^ k * (k.factorial : ℝ) / (2 * Real.pi) ^ k := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
          zpow_sub_one₀ hNr.ne', zpow_natCast, hC]
        field_simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BUltraUnit
open Finset UpperTheory.V.Bern

private theorem b_ultra_int {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω] {y : Ω}
    (h : IsIntegral ℤ y) : ‖y‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := Ω)).integer y := h.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := Ω))).mem_of_integral h1
  have h3 : ‖y‖₊ ≤ 1 := h2
  exact_mod_cast h3

private theorem b_ultra_unit {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω] (l : ℕ)
    [hl : Fact l.Prime] (hn : ‖(l : Ω)‖ = (l : ℝ)⁻¹) (m : ℤ) (hm : ¬ (l : ℤ) ∣ m) :
    ‖(m : Ω)‖ = 1 := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl.out
  obtain ⟨a, b, hab⟩ := (hp.irreducible.coprime_iff_not_dvd).mpr hm
  have h1 : (a : Ω) * l + b * m = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hlt : ‖(l : Ω)‖ < 1 := by rw [hn]; exact inv_lt_one_of_one_lt₀ hl1
  refine le_antisymm (IsUltrametricDist.norm_intCast_le_one Ω m) ?_
  by_contra hc
  push Not at hc
  have ha := IsUltrametricDist.norm_intCast_le_one Ω a
  have hb := IsUltrametricDist.norm_intCast_le_one Ω b
  have h2 := IsUltrametricDist.norm_add_le_max ((a : Ω) * l) ((b : Ω) * m)
  rw [h1, norm_one, norm_mul, norm_mul] at h2
  have h3 : ‖(a : Ω)‖ * ‖(l : Ω)‖ < 1 := mul_lt_one_of_nonneg_of_lt_one_right ha (norm_nonneg _) hlt
  have h4 : ‖(b : Ω)‖ * ‖(m : Ω)‖ < 1 := mul_lt_one_of_nonneg_of_lt_one_right hb (norm_nonneg _) hc
  exact absurd h2 (not_le.mpr (max_lt h3 h4))

private theorem b_ultra_log {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω] (l : ℕ)
    [hl : Fact l.Prime] (hn : ‖(l : Ω)‖ = (l : ℝ)⁻¹) (M : ℤ) (hM : M ≠ 0) :
    -Real.log ‖(M : Ω)‖ = (padicValInt l M : ℝ) * Real.log l := by
  obtain ⟨m, hm⟩ := padicValInt_dvd (p := l) M
  have hnd : ¬ (l : ℤ) ∣ m := by
    rintro ⟨c, hc⟩
    have : (l : ℤ) ^ (padicValInt l M + 1) ∣ M := ⟨c, by
      conv_lhs => rw [hm, hc]
      ring⟩
    rcases (padicValInt_dvd_iff _ _).mp this with h | h
    · exact hM h
    · omega
  have h1 : (M : Ω) = (l : Ω) ^ padicValInt l M * m := by
    exact_mod_cast congrArg (Int.cast : ℤ → Ω) hm
  rw [h1, norm_mul, b_ultra_unit l hn m hnd, mul_one, norm_pow, hn, Real.log_pow, Real.log_inv]
  ring

theorem UpperTheory.V.Bern.b_ultra :
    ∀ {Ω ι : Type} [NormedField Ω] [IsUltrametricDist Ω] [CharZero Ω] (l : ℕ) [Fact l.Prime], ‖(l : Ω)‖ = (l : ℝ)⁻¹ → ∀ (S : Set ι) (x : ι → Ω) (D : ℕ) (M : ℤ), S.Finite → M ≠ 0 → (∀ i ∈ S, IsIntegral ℤ ((D : Ω) * x i)) → ∏ᶠ i ∈ S, (D : Ω) * x i = (M : Ω) → ∑ᶠ i ∈ S, max 0 (-Real.log ‖x i‖) ≤ (padicValInt l M : ℝ) * Real.log l := by
  intro Ω ι _ _ _ l _ hn S x D M hS hM hint hprod
  rw [finprod_mem_eq_finite_toFinset_prod _ hS] at hprod
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, ← b_ultra_log l hn M hM, ← hprod, norm_prod]
  have hM' : (M : Ω) ≠ 0 := by exact_mod_cast hM
  have hne : ∀ i ∈ hS.toFinset, (D : Ω) * x i ≠ 0 := by
    rw [← Finset.prod_ne_zero_iff, hprod]; exact hM'
  rw [Real.log_prod (fun i hi => norm_ne_zero_iff.mpr (hne i hi)), ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ∈ S := by simpa using hi
  have h0 := hne i hi
  have hD : (D : Ω) ≠ 0 := left_ne_zero_of_mul h0
  have hx : x i ≠ 0 := right_ne_zero_of_mul h0
  refine max_le ?_ ?_
  · have := Real.log_nonpos (norm_nonneg _) (b_ultra_int (hint i hi'))
    linarith
  · rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hD) (norm_ne_zero_iff.mpr hx)]
    have := Real.log_nonpos (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one Ω D)
    linarith
end
