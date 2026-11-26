module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwAbs

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.EmbCyc
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.embCyc :
    ∀ (N m M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsAbelianGalois ℚ K] (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] [IsCyclotomicExtension {m} K K'] (L : Type) [Field L] [NumberField L] [Algebra K' L] [IsCyclotomicExtension {M} K' L], N ∣ M → m ∣ M → Nonempty (K →ₐ[ℚ] CyclotomicField N ℚ) → IsCyclotomicExtension {M} ℚ L := by
  intro N m M _ K _ _ _ K' _ _ _ _ L _ _ _ _ hNM hmM hφ
  obtain ⟨φ⟩ := hφ
  have hM0 : M ≠ 0 := NeZero.ne M
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hM0 (zero_dvd_iff.mp hNM)
  haveI : NeZero N := ⟨hN0⟩
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot K' L (Set.mem_singleton M) hM0
  let F : Subalgebra ℚ L := Algebra.adjoin ℚ {ζ}
  have hroot : ∀ x : L, ∀ k : ℕ, k ∣ M → x ^ k = 1 → x ∈ F := by
    intro x k hk hx
    have hxM : x ^ M = 1 := by
      obtain ⟨j, hj⟩ := hk
      rw [hj, pow_mul, hx, one_pow]
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hxM
    rw [← hi]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton ζ)) _
  have hpN : IsPrimitiveRoot (ζ ^ (M / N)) N := by
    have := hζ.pow_of_dvd (p := M / N) ?_ (Nat.div_dvd_of_dvd hNM)
    · rwa [Nat.div_div_self hNM hM0] at this
    · exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hNM) (Nat.pos_of_ne_zero hN0)).ne'
  have hsp : Polynomial.Splits ((Polynomial.X ^ N - 1 : Polynomial ℚ).map (algebraMap ℚ L)) := by
    simpa using Polynomial.X_pow_sub_one_splits hpN
  have : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  haveI := IsCyclotomicExtension.isSplittingField_X_pow_sub_one N ℚ (CyclotomicField N ℚ)
  let ψ : CyclotomicField N ℚ →ₐ[ℚ] L :=
    Polynomial.IsSplittingField.lift (CyclotomicField N ℚ) (Polynomial.X ^ N - 1) hsp
  have h1 : ∀ y, ψ y ∈ F := by
    intro y
    have hy := IsCyclotomicExtension.adjoin_roots (S := {N}) (A := ℚ) y
    have hle : Algebra.adjoin ℚ {b : CyclotomicField N ℚ | ∃ n : ℕ, n ∈ ({N} : Set ℕ) ∧ n ≠ 0 ∧ b ^ n = 1}
        ≤ F.comap ψ := by
      rw [Algebra.adjoin_le_iff]
      rintro b ⟨n, hn, -, hb⟩
      rw [Set.mem_singleton_iff] at hn
      rw [hn] at hb
      exact hroot (ψ b) N hNM (by rw [← map_pow, hb, map_one])
    exact hle hy
  have h2 : ∀ k : K, algebraMap K' L (algebraMap K K' k) ∈ F := by
    intro k
    let e1 : K →ₐ[ℚ] L := ((algebraMap K' L).comp (algebraMap K K')).toRatAlgHom
    let e2 : K →ₐ[ℚ] L := ψ.comp φ
    let g := e2.equivFieldRange
    haveI := Normal.of_algEquiv g
    have hr := AlgHom.fieldRange_of_normal (e1.comp g.symm.toAlgHom)
    have hk : e1 k ∈ e2.fieldRange := by
      rw [← hr]
      exact AlgHom.mem_fieldRange.mpr ⟨g k, by simp⟩
    obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.mp hk
    show e1 k ∈ F
    rw [← hy]
    exact h1 (φ y)
  have h3 : ∀ x : K', algebraMap K' L x ∈ F := by
    intro x
    have hx := IsCyclotomicExtension.adjoin_roots (S := {m}) (A := K) x
    induction hx using Algebra.adjoin_induction with
    | mem b hb =>
      obtain ⟨n, hn, -, hbn⟩ := hb
      rw [Set.mem_singleton_iff] at hn
      rw [hn] at hbn
      exact hroot _ m hmM (by rw [← map_pow, hbn, map_one])
    | algebraMap k => exact h2 k
    | add a b _ _ ha hb =>
      rw [map_add (f := _)]
      exact add_mem ha hb
    | mul a b _ _ ha hb =>
      rw [map_mul]
      exact mul_mem ha hb
  have h4 : ∀ x : L, x ∈ F := by
    intro x
    have hx := IsCyclotomicExtension.adjoin_roots (S := {M}) (A := K') x
    induction hx using Algebra.adjoin_induction with
    | mem b hb =>
      obtain ⟨n, hn, -, hbn⟩ := hb
      rw [Set.mem_singleton_iff] at hn
      rw [hn] at hbn
      exact hroot _ M dvd_rfl hbn
    | algebraMap k => exact h3 k
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  rw [IsCyclotomicExtension.iff_singleton]
  refine ⟨⟨ζ, hζ⟩, fun x => Algebra.adjoin_mono ?_ (h4 x)⟩
  rintro _ rfl
  exact hζ.pow_eq_one
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem totient_prime_pow_add_le_pow_mul_totient (l : ℕ) (hl : l.Prime) (n k : ℕ) :
    (l ^ (n + k)).totient ≤ l ^ k * (l ^ n).totient := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using Nat.totient_le (l ^ k)
  · rw [Nat.totient_prime_pow hl (by omega), Nat.totient_prime_pow hl hn]
    have : n + k - 1 = k + (n - 1) := by omega
    rw [this, pow_add, mul_assoc]

theorem UpperTheory.V.FW.embed :
    ∀ (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [NumberField K] [IsAbelianGalois ℚ K], ∃ f D : ℕ, f.Coprime l ∧ 1 < f ∧ ∀ (n n₀ : ℕ) (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] [IsCyclotomicExtension {l ^ n} K K'], ∃ (m : ℕ) (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K' L) (_ : IsCyclotomicExtension {f * l ^ m} ℚ L), n₀ ≤ m ∧ Module.finrank K' L ≤ D * l ^ n₀ := by
  intro l hl K _ _ _
  have hp : l.Prime := hl.out
  obtain ⟨N, hN, ⟨φ⟩⟩ := CF.kwHom K
  obtain ⟨e, f₀, hf₀, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hp.one_lt.ne'
  have hf₀c : f₀.Coprime l := ((Nat.Prime.coprime_iff_not_dvd hp).2 hf₀).symm
  have hf₀pos : 0 < f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h | h
    · simp [h] at hN
    · exact h
  have hlc : (l + 1).Coprime l := by
    simp
  refine ⟨f₀ * (l + 1), f₀ * (l + 1) * l ^ e, Nat.Coprime.mul_left hf₀c hlc, ?_, ?_⟩
  · have : 1 < l + 1 := by have := hp.one_lt; omega
    calc 1 < l + 1 := this
      _ ≤ f₀ * (l + 1) := Nat.le_mul_of_pos_left _ hf₀pos
  intro n n₀ K' _ _ _ _
  set m := n + (e + n₀) with hm
  set M := f₀ * (l + 1) * l ^ m with hM
  have hMpos : 0 < M := by
    have := hp.pos
    positivity
  haveI : NeZero M := ⟨hMpos.ne'⟩
  let L := CyclotomicField M K'
  haveI : Module.Finite K' L := IsCyclotomicExtension.finite {M} K' L
  haveI : NumberField L := NumberField.of_module_finite K' L
  have hdvdN : l ^ e * f₀ ∣ M := by
    refine ⟨(l + 1) * l ^ (n + n₀), ?_⟩
    rw [hM, hm]
    ring
  have hdvdm : l ^ n ∣ M := by
    refine ⟨f₀ * (l + 1) * l ^ (e + n₀), ?_⟩
    rw [hM, hm]
    ring
  have hcyc : IsCyclotomicExtension {M} ℚ L :=
    embCyc (l ^ e * f₀) (l ^ n) M K K' L hdvdN hdvdm ⟨φ⟩
  refine ⟨m, L, inferInstance, inferInstance, inferInstance, hcyc, by omega, ?_⟩
  have hL : Module.finrank ℚ L = M.totient := IsCyclotomicExtension.Rat.finrank M L
  have hlnpos : 0 < l ^ n := pow_pos hp.pos n
  have hK' : (l ^ n).totient ≤ Module.finrank ℚ K' := by
    have hz := IsCyclotomicExtension.zeta_spec (l ^ n) K K'
    have h1 := Polynomial.cyclotomic_eq_minpoly_rat hz hlnpos
    have h2 := minpoly.natDegree_le (A := ℚ) (IsCyclotomicExtension.zeta (l ^ n) K K')
    rw [← h1, Polynomial.natDegree_cyclotomic] at h2
    exact h2
  have htow := Module.finrank_mul_finrank ℚ K' L
  have htot : M.totient ≤ f₀ * (l + 1) * l ^ e * l ^ n₀ * (l ^ n).totient := by
    have hco : (f₀ * (l + 1)).Coprime (l ^ m) := (Nat.Coprime.mul_left hf₀c hlc).pow_right m
    rw [hM, Nat.totient_mul hco]
    calc (f₀ * (l + 1)).totient * (l ^ m).totient ≤ f₀ * (l + 1) * (l ^ m).totient :=
          Nat.mul_le_mul_right _ (Nat.totient_le _)
      _ ≤ f₀ * (l + 1) * (l ^ (e + n₀) * (l ^ n).totient) :=
          Nat.mul_le_mul_left _ (totient_prime_pow_add_le_pow_mul_totient l hp n (e + n₀))
      _ = f₀ * (l + 1) * l ^ e * l ^ n₀ * (l ^ n).totient := by
          rw [pow_add]
          ring
  have htpos : 0 < (l ^ n).totient := Nat.totient_pos.2 hlnpos
  refine Nat.le_of_mul_le_mul_right ?_ htpos
  calc Module.finrank K' L * (l ^ n).totient ≤ Module.finrank K' L * Module.finrank ℚ K' :=
        Nat.mul_le_mul_left _ hK'
    _ = M.totient := by rw [mul_comm, htow, hL]
    _ ≤ f₀ * (l + 1) * l ^ e * l ^ n₀ * (l ^ n).totient := htot
