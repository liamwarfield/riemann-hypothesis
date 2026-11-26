module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BNzC

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BNzany
open Finset UpperTheory.V.Bern

private theorem nz_iff {R S : Type} [Field R] [Algebra ℚ R] [Field S] [Algebra ℚ S] {N : ℕ} [NeZero N]
    (f : R →+* S) (χ : DirichletCharacter R N) (k : ℕ) :
    ((χ.ringHomComp f : DirichletCharacter S N) (-1) = (-1) ^ k ↔ χ (-1) = (-1) ^ k) ∧
    (Bprim k (χ.ringHomComp f : DirichletCharacter S N) ≠ 0 ↔ Bprim k χ ≠ 0) ∧
    (genB k (χ.ringHomComp f : ZMod N → S) ≠ 0 ↔ genB k χ ≠ 0) := by
  have hinj : Function.Injective f := f.injective
  refine ⟨?_, ?_, ?_⟩
  · rw [MulChar.ringHomComp_apply]
    have e : ((-1 : S)) ^ k = f ((-1 : R) ^ k) := by simp
    rw [e]
    exact hinj.eq_iff
  · rw [← b_primmap f hinj k χ]
    exact map_ne_zero_iff f hinj
  · rw [← map_genB_char f k χ]
    exact map_ne_zero_iff f hinj

theorem UpperTheory.V.Bern.b_nzany :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] {N : ℕ} [NeZero N] (χ : DirichletCharacter Ω N) (k : ℕ), 1 ≤ k → χ (-1) = (-1) ^ k → Bprim k χ ≠ 0 ∧ (2 ≤ k → genB k χ ≠ 0) := by
  intro Ω _ _ N _ χ k hk hχ
  haveI : NeZero (Monoid.exponent (ZMod N)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let i : Ω →+* AlgebraicClosure Ω := algebraMap _ _
  let f : AlgebraicClosure ℚ →+* AlgebraicClosure Ω :=
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure Ω).toRingHom
  let g : AlgebraicClosure ℚ →+* ℂ :=
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] ℂ).toRingHom
  obtain ⟨ψ, -, hψ⟩ := (UpperTheory.V.Bern.b_charbij (N := N) f Set.univ).surjOn
    (show (χ.ringHomComp i : DirichletCharacter _ N) ∈ charSet (AlgebraicClosure Ω) Set.univ from Set.mem_univ _)
  obtain ⟨a1, a2, a3⟩ := nz_iff i χ k
  obtain ⟨b1, b2, b3⟩ := nz_iff f ψ k
  obtain ⟨c1, c2, c3⟩ := nz_iff g ψ k
  simp only at hψ
  rw [hψ] at b1 b2 b3
  obtain ⟨h1, h2⟩ := UpperTheory.V.Bern.b_nzC (ψ.ringHomComp g) k hk (c1.2 (b1.1 (a1.2 hχ)))
  exact ⟨a2.1 (b2.2 (c2.1 h1)), fun h => a3.1 (b3.2 (c3.1 (h2 h)))⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Prodint
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Denupper
open Finset UpperTheory.V.Bern

private theorem bernoulli_denominator_bound {N M : ℕ} (k : ℕ) (Φ : ZMod M → ℂ) (hM : 0 < M) (hMN : M ≤ N)
    (hΦ : ∀ a, ‖Φ a‖ ≤ 1) : ‖(den N k : ℂ) * genB k Φ‖ ≤ bnd N k := by
  have hb := b_upper k Φ hM hΦ
  have hp : (primorial (k + 1) : ℝ) ≤ 4 ^ (k + 1) := by exact_mod_cast primorial_le_four_pow (k + 1)
  have h4 : (4 : ℝ) ^ k ≤ (2 * Real.pi) ^ k :=
    pow_le_pow_left₀ (by norm_num) (by linarith [Real.pi_gt_three]) k
  have hpi : 0 < (2 * Real.pi) ^ k := by positivity
  have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
  rw [norm_mul, Complex.norm_natCast, den, bnd]
  push_cast
  calc (N : ℝ) * (primorial (k + 1) : ℝ) * ‖genB k Φ‖
      ≤ N * 4 ^ (k + 1) * (4 * (N : ℝ) ^ k * k.factorial / (2 * Real.pi) ^ k) := by
        gcongr
        exact hb.trans (by gcongr)
    _ = 16 * (N : ℝ) ^ (k + 1) * k.factorial * (4 ^ k / (2 * Real.pi) ^ k) := by ring
    _ ≤ 16 * (N : ℝ) ^ (k + 1) * k.factorial * 1 := by
        gcongr
        rw [div_le_one hpi]
        exact h4
    _ = _ := mul_one _

theorem UpperTheory.V.Bern.b_denupper :
    ∀ {N : ℕ} [NeZero N] (k : ℕ) (χ : DirichletCharacter ℂ N), ‖(den N k : ℂ) * genB k χ‖ ≤ bnd N k ∧ ‖(den N k : ℂ) * Bprim k χ‖ ≤ bnd N k ∧ 1 ≤ bnd N k := by
  intro N _ k χ
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  refine ⟨bernoulli_denominator_bound k _ hN le_rfl (fun a => χ.norm_le_one a), ?_, ?_⟩
  · exact bernoulli_denominator_bound k _ (Nat.pos_of_ne_zero χ.conductor_ne_zero)
      (Nat.le_of_dvd hN χ.conductor_dvd_level) (fun a => χ.primitiveCharacter.norm_le_one a)
  · have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (k + 1) := one_le_pow₀ (by exact_mod_cast hN)
    have h2 : (1 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
    unfold bnd
    nlinarith [mul_le_mul h1 h2 zero_le_one (zero_le_one.trans h1)]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Ratprod
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_ratprod :
    ∀ {N : ℕ} [NeZero N] (P : Set (Subgroup (ZMod N)ˣ)) (F : ∀ (Ω : Type) [Field Ω] [CharZero Ω], DirichletCharacter Ω N → Ω), (∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [CharZero Ω] (f : K →+* Ω) (χ : DirichletCharacter K N), f (F K χ) = F Ω (χ.ringHomComp f)) → ∃ q : ℚ, ∀ (Ω : Type) [Field Ω] [CharZero Ω] [HasEnoughRootsOfUnity Ω (Monoid.exponent (ZMod N)ˣ)], ∏ᶠ χ ∈ charSet Ω P, F Ω χ = (q : Ω) := by
  intro N _ P F hF
  set e := Monoid.exponent (ZMod N)ˣ with he_def
  haveI he : NeZero e := ⟨Monoid.exponent_ne_zero_of_finite⟩
  haveI : NeZero (e : ℚ) := ⟨by exact_mod_cast he.out⟩
  haveI hcyc : IsCyclotomicExtension {e} ℚ (CyclotomicField e ℚ) :=
    CyclotomicField.isCyclotomicExtension e ℚ
  haveI : IsGalois ℚ (CyclotomicField e ℚ) := IsCyclotomicExtension.isGalois {e} ℚ _
  haveI : FiniteDimensional ℚ (CyclotomicField e ℚ) :=
    IsCyclotomicExtension.finiteDimensional {e} ℚ _
  have hζ := IsCyclotomicExtension.zeta_spec e ℚ (CyclotomicField e ℚ)
  haveI : HasEnoughRootsOfUnity (CyclotomicField e ℚ) e :=
    ⟨⟨_, hζ⟩, rootsOfUnity.isCyclic (CyclotomicField e ℚ) e⟩
  have hfin : ∀ (Ω : Type) [Field Ω], (charSet Ω P).Finite := fun Ω _ => Set.toFinite _
  have hfix : ∀ σ : CyclotomicField e ℚ ≃ₐ[ℚ] CyclotomicField e ℚ,
      σ (∏ᶠ χ ∈ charSet (CyclotomicField e ℚ) P, F (CyclotomicField e ℚ) χ) =
        ∏ᶠ χ ∈ charSet (CyclotomicField e ℚ) P, F (CyclotomicField e ℚ) χ := by
    intro σ
    have h1 := (σ.toRingHom.toMonoidHom).map_finprod_mem
      (fun χ => F (CyclotomicField e ℚ) χ) (hfin (CyclotomicField e ℚ))
    refine h1.trans ?_
    exact finprod_mem_eq_of_bijOn _ (b_charbij σ.toRingHom P)
      (fun χ _ => hF _ _ σ.toRingHom χ)
  have hbot := (IsGalois.mem_bot_iff_fixed _).2 hfix
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.1 hbot
  refine ⟨q, fun Ω _ _ _ => ?_⟩
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω e
  have hmin : Polynomial.aeval ω (minpoly ℚ (hζ.powerBasis ℚ).gen) = 0 := by
    rw [IsPrimitiveRoot.powerBasis_gen, ← hζ.minpoly_eq_cyclotomic_of_irreducible
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos e)), Polynomial.aeval_def,
      Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hω.isRoot_cyclotomic (NeZero.pos e)
  let g := (hζ.powerBasis ℚ).lift ω hmin
  calc ∏ᶠ χ ∈ charSet Ω P, F Ω χ
      = ∏ᶠ χ ∈ charSet (CyclotomicField e ℚ) P, g.toRingHom (F (CyclotomicField e ℚ) χ) :=
        (finprod_mem_eq_of_bijOn _ (b_charbij g.toRingHom P)
          (fun χ _ => hF _ _ g.toRingHom χ)).symm
    _ = g.toRingHom (∏ᶠ χ ∈ charSet (CyclotomicField e ℚ) P, F (CyclotomicField e ℚ) χ) :=
        (g.toRingHom.toMonoidHom.map_finprod_mem _ (hfin _)).symm
    _ = (q : Ω) := by
        rw [← hq]
        exact g.commutes q |>.trans (eq_ratCast _ q)
end

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_prodint :
    ∀ {N : ℕ} [NeZero N] (k : ℕ) (P : Set (Subgroup (ZMod N)ˣ)), 1 ≤ k → P ⊆ parKer N k → ∃ M : ℤ, M ≠ 0 ∧ Real.log |(M : ℝ)| ≤ (charSet ℂ P).ncard * Real.log (bnd N k) ∧ ∀ (Ω : Type) [Field Ω] [CharZero Ω] [HasEnoughRootsOfUnity Ω (Monoid.exponent (ZMod N)ˣ)], ∏ᶠ χ ∈ charSet Ω P, (den N k : Ω) * Bprim k χ = (M : Ω) := by
  intro N _ k P hk hP
  obtain ⟨q, hq⟩ := b_ratprod P (fun Ω _ _ χ => (den N k : Ω) * Bprim k χ) (by
    intro K Ω _ _ _ _ f χ
    simp only [map_mul, map_natCast]
    rw [b_primmap f f.injective])
  have hfin : (charSet ℂ P).Finite := Set.toFinite _
  haveI : NeZero (Monoid.exponent (ZMod N)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have hC := hq ℂ
  rw [finprod_mem_eq_finite_toFinset_prod _ hfin] at hC
  have hint : IsIntegral ℤ (q : ℂ) := by
    rw [← hC]
    exact IsIntegral.prod _ fun χ _ => (b_primmem k χ).2.2.1
  have hint' : IsIntegral ℤ q := by
    have : (q : ℂ) = algebraMap ℚ ℂ q := rfl
    rw [this] at hint
    exact (isIntegral_algebraMap_iff ).mp hint
  obtain ⟨M, hM⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'
  have hM' : (M : ℚ) = q := by simpa using hM
  subst hM'
  have hC' : ∏ χ ∈ hfin.toFinset, (den N k : ℂ) * Bprim k χ = (M : ℂ) := by
    rw [hC]; simp
  have hM0 : M ≠ 0 := by
    have : (M : ℂ) ≠ 0 := by
      rw [← hC']
      refine Finset.prod_ne_zero_iff.mpr fun χ hχ => mul_ne_zero ?_ ?_
      · exact Nat.cast_ne_zero.mpr (den_pos (NeZero.pos N) k).ne'
      · have hχ' : χ.toUnitHom.ker ∈ P := hfin.mem_toFinset.mp hχ
        exact (b_nzC χ k hk ((b_parity k χ).1.mp (hP hχ'))).1
    exact_mod_cast this
  refine ⟨M, hM0, ?_, fun Ω _ _ _ => ?_⟩
  · have hle : |(M : ℝ)| ≤ bnd N k ^ (charSet ℂ P).ncard := by
      have h1 : |(M : ℝ)| = ‖(M : ℂ)‖ := by simp
      rw [h1, ← hC', norm_prod, Set.ncard_eq_toFinset_card _ hfin, ← Finset.prod_const]
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun χ _ => (b_denupper k χ).2.1
    rw [← Real.log_pow]
    exact Real.log_le_log (abs_pos.mpr (Int.cast_ne_zero.mpr hM0)) hle
  · rw [hq Ω]; simp
end
