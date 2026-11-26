module

public import Mathlib

@[expose] public section

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.PartialDerivativeExponent
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent

open MvPowerSeries

variable {σ : Type}

variable {k : Type} [CommRing k]

variable [Algebra ℚ k]

private lemma coeff_XX_pow_lemma (d : ℕ) (e : Fin 2 →₀ ℕ) :
    coeff e ((X 0 + X 1 : MvPowerSeries (Fin 2) k) ^ d) =
      if e 0 + e 1 = d then ((d.choose (e 0) : ℕ) : k) else 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [add_pow, map_sum]
  have key : ∀ m ∈ Finset.range (d + 1),
      coeff e ((X 0 : MvPowerSeries (Fin 2) k) ^ m * X 1 ^ (d - m) * (d.choose m : MvPowerSeries (Fin 2) k)) =
        if e 0 = m ∧ e 1 = d - m then (d.choose m : k) else 0 := by
    intro m _
    rw [← map_natCast (C : k →+* MvPowerSeries (Fin 2) k), coeff_mul_C, X_pow_eq, X_pow_eq,
      monomial_mul_monomial, coeff_monomial]
    have hiff : (e = Finsupp.single 0 m + Finsupp.single 1 (d - m)) ↔ (e 0 = m ∧ e 1 = d - m) := by
      constructor
      · rintro rfl
        simp
      · rintro ⟨h0, h1⟩
        ext i
        fin_cases i <;> simp [h0, h1]
    by_cases h : e 0 = m ∧ e 1 = d - m
    · rw [if_pos (hiff.2 h), if_pos h]
      simp
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h, zero_mul]
  rw [Finset.sum_congr rfl key]
  by_cases hd : e 0 + e 1 = d
  · rw [if_pos hd, Finset.sum_eq_single (e 0)]
    · rw [if_pos ⟨rfl, by omega⟩]
    · intro m _ hm
      rw [if_neg]
      rintro ⟨h, _⟩
      exact hm h.symm
    · intro h
      exfalso
      apply h
      rw [Finset.mem_range]
      omega
  · rw [if_neg hd]
    apply Finset.sum_eq_zero
    intro m hm
    rw [Finset.mem_range] at hm
    rw [if_neg]
    rintro ⟨h0, h1⟩
    omega

private lemma coeff_substX_lemma_2 (i : Fin 2) (f : PowerSeries k) (e : Fin 2 →₀ ℕ) :
    coeff e (PowerSeries.subst (X i : MvPowerSeries (Fin 2) k) f) =
      if e = Finsupp.single i (e i) then PowerSeries.coeff (e i) f else 0 := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))]
  simp_rw [coeff_X_pow]
  by_cases h : e = Finsupp.single i (e i)
  · rw [if_pos h, finsum_eq_single _ (e i)]
    · rw [if_pos h, smul_eq_mul, mul_one]
    · intro d hd
      rw [if_neg, smul_zero]
      intro h'
      apply hd
      rw [h']
      simp
  · rw [if_neg h]
    have hz : ∀ d : ℕ, (PowerSeries.coeff d f • if e = Finsupp.single i d then (1 : k) else 0) = 0 := by
      intro d
      rw [if_neg, smul_zero]
      intro h'
      apply h
      rw [h']
      simp
    simp only [hz, finsum_zero]

theorem exp_biv :
    PowerSeries.subst (X (0 : Fin 2) + X 1 : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) =
      PowerSeries.subst (X (0 : Fin 2) : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) *
        PowerSeries.subst (X (1 : Fin 2) : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) := by
  ext e
  have hsum : PowerSeries.HasSubst (X 0 + X 1 : MvPowerSeries (Fin 2) k) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have hL : coeff e (PowerSeries.subst (X (0 : Fin 2) + X 1 : MvPowerSeries (Fin 2) k) (PowerSeries.exp k)) =
      PowerSeries.coeff (e 0 + e 1) (PowerSeries.exp k) * ((e 0 + e 1).choose (e 0) : k) := by
    rw [PowerSeries.coeff_subst hsum, finsum_eq_single _ (e 0 + e 1)]
    · rw [coeff_XX_pow_lemma, if_pos rfl, smul_eq_mul]
    · intro d hd
      rw [coeff_XX_pow_lemma, if_neg (fun h => hd h.symm), smul_zero]
  have hR : coeff e (PowerSeries.subst (X (0 : Fin 2) : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) *
        PowerSeries.subst (X (1 : Fin 2) : MvPowerSeries (Fin 2) k) (PowerSeries.exp k)) =
      PowerSeries.coeff (e 0) (PowerSeries.exp k) * PowerSeries.coeff (e 1) (PowerSeries.exp k) := by
    rw [coeff_mul, Finset.sum_eq_single (Finsupp.single 0 (e 0), Finsupp.single 1 (e 1))]
    · rw [coeff_substX_lemma_2, coeff_substX_lemma_2, if_pos (by simp), if_pos (by simp)]
      simp
    · rintro ⟨p, q⟩ hpq hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
      rw [coeff_substX_lemma_2, coeff_substX_lemma_2]
      by_cases h1 : p = Finsupp.single 0 (p 0)
      · by_cases h2 : q = Finsupp.single 1 (q 1)
        · exfalso
          apply hne
          have hq0 : q 0 = 0 := by
            rw [h2]
            simp
          have hp1 : p 1 = 0 := by
            rw [h1]
            simp
          have c0 := DFunLike.congr_fun hpq 0
          have c1 := DFunLike.congr_fun hpq 1
          simp only [Finsupp.coe_add, Pi.add_apply] at c0 c1
          rw [Prod.mk.injEq]
          constructor
          · rw [h1]
            congr 1
            omega
          · rw [h2]
            congr 1
            omega
        · rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
    · intro h
      exfalso
      apply h
      rw [Finset.HasAntidiagonal.mem_antidiagonal]
      ext i
      fin_cases i <;> simp
  rw [hL, hR, PowerSeries.coeff_exp, PowerSeries.coeff_exp, PowerSeries.coeff_exp,
    ← map_natCast (algebraMap ℚ k), ← map_mul, ← map_mul]
  congr 1
  have hle : e 0 ≤ e 0 + e 1 := Nat.le_add_right _ _
  have h := Nat.choose_mul_factorial_mul_factorial hle
  rw [Nat.add_sub_cancel_left] at h
  have h' : ((e 0 + e 1).choose (e 0) : ℚ) * ((e 0).factorial : ℚ) * ((e 1).factorial : ℚ) =
      ((e 0 + e 1).factorial : ℚ) := by
    exact_mod_cast h
  have hc : ((e 0 + e 1).choose (e 0) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hle).ne'
  have hf0 : ((e 0).factorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  have hf1 : ((e 1).factorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  rw [← h']
  field_simp

theorem psubst_comp {τ υ : Type} (b : τ → MvPowerSeries υ k) (hb : HasSubst b)
    (a : MvPowerSeries τ k) (ha : constantCoeff a = 0) (f : PowerSeries k) :
    subst b (PowerSeries.subst a f) = PowerSeries.subst (subst b a) f := by
  have ha' : HasSubst (fun _ : Unit => a) := hasSubst_of_constantCoeff_zero (fun _ => ha)
  simp only [PowerSeries.subst]
  rw [subst_comp_subst_apply ha' hb]

theorem expS_add {τ : Type} (x y : MvPowerSeries τ k) (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) :
    PowerSeries.subst (x + y) (PowerSeries.exp k) =
      PowerSeries.subst x (PowerSeries.exp k) * PowerSeries.subst y (PowerSeries.exp k) := by
  have hb : HasSubst (![x, y] : Fin 2 → MvPowerSeries τ k) :=
    hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp [hx, hy])
  have h := congrArg (subst (![x, y] : Fin 2 → MvPowerSeries τ k)) (exp_biv (k := k))
  rw [psubst_comp _ hb (X 0 + X 1) (by simp), subst_mul hb, psubst_comp _ hb (X 0) (by simp),
    psubst_comp _ hb (X 1) (by simp)] at h
  simpa [subst_add hb, subst_X hb] using h

end Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinSt
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin

open Matrix

def WhitenStatement : Prop :=
  ∀ (d : ℕ) (L : Matrix (Fin d) (Fin d) ℝ), L.PosDef →
    ∃ R : Matrix (Fin d) (Fin d) ℝ, IsUnit R.det ∧ L = Rᵀ * R

def HalfTraceStatement : Prop :=
  ∀ (d : ℕ) (L G K R : Matrix (Fin d) (Fin d) ℝ), L = Rᵀ * R → IsUnit R.det → G.PosSemidef →
    Kᵀ * G = -(G * K) → K * L = -(L * Kᵀ) → IsUnit K.det →
    ∀ x : Fin d → ℝ, x ⬝ᵥ (G *ᵥ x) ≤
      (1 / 2) * trace (L * G) * (((R⁻¹)ᵀ *ᵥ x) ⬝ᵥ ((R⁻¹)ᵀ *ᵥ x))

def ShortDualStatement : Prop :=
  ∀ (d : ℕ) (L R : Matrix (Fin d) (Fin d) ℝ) (μ : ℝ), 0 < d → L = Rᵀ * R → IsUnit R.det → 0 < μ →
    (∀ t : Fin d → ℤ, t ≠ 0 → μ ^ 2 ≤ (fun i => (t i : ℝ)) ⬝ᵥ (L *ᵥ fun i => (t i : ℝ))) →
    ∀ δ : ℝ, 0 < δ → ∃ c : Fin d → Fin d → ℤ, LinearIndependent ℤ c ∧
      ∀ j, ((R⁻¹)ᵀ *ᵥ fun i => (c j i : ℝ)) ⬝ᵥ ((R⁻¹)ᵀ *ᵥ fun i => (c j i : ℝ)) ≤
        ((d : ℝ) / μ + δ) ^ 2

def FiniteShortStatement : Prop :=
  ∀ (d : ℕ) (G : Matrix (Fin d) (Fin d) ℝ), G.PosDef → ∀ B : ℝ,
    {c : Fin d → ℤ | (fun i => (c i : ℝ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℝ)) ≤ B}.Finite

end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanDirAlg
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg

open NumberField Matrix

section Core

variable {E : Type} [Field E] [NumberField E] {κ : Type} [Fintype κ]

theorem hom_basis {R' : Type} [Ring R'] (f : 𝓞 E →+* R') (b : Module.Basis κ ℤ (𝓞 E)) (x : 𝓞 E) :
    f x = ∑ k, ((b.repr x k : ℤ) : R') * f (b k) := by
  conv_lhs => rw [← b.sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, zsmul_eq_mul]

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {ι : Type} [Fintype ι] [DecidableEq ι]
  [DecidableEq κ]

theorem decomp_of_inv (ρ : 𝓞 E →+* Module.End R M) (χ : ι → (𝓞 E →+* R)) (b : Module.Basis κ ℤ (𝓞 E))
    (Cm : κ → ι → R) (hAC : ∀ σ τ, ∑ i, χ σ (b i) * Cm i τ = if σ = τ then 1 else 0)
    (hCA : ∀ i j, ∑ τ, Cm i τ * χ τ (b j) = if i = j then 1 else 0) :
    (∀ m : M, ∃ mσ : ι → M, (∀ σ (a : 𝓞 E), ρ a (mσ σ) = χ σ a • mσ σ) ∧ ∑ σ, mσ σ = m) ∧
    (∀ mσ : ι → M, (∀ σ (a : 𝓞 E), ρ a (mσ σ) = χ σ a • mσ σ) → ∑ σ, mσ σ = 0 → ∀ σ, mσ σ = 0) := by
  classical
  set Q : ι → M → M := fun σ m => ∑ i, Cm i σ • ρ (b i) m with hQ
  have hcoef : ∀ (a : 𝓞 E) (i : κ), ∑ τ, χ τ a * Cm i τ = ((b.repr a i : ℤ) : R) := by
    intro a i
    have h1 : ∀ τ, χ τ a = ∑ k, ((b.repr a k : ℤ) : R) * χ τ (b k) := fun τ => hom_basis (χ τ) b a
    have hCA' : ∀ k, ∑ τ, χ τ (b k) * Cm i τ = if i = k then 1 else 0 := by
      intro k
      rw [← hCA i k]
      exact Finset.sum_congr rfl fun τ _ => mul_comm _ _
    simp_rw [h1, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum, hCA']
    simp
  have F3 : ∀ (a : 𝓞 E) (m : M), ρ a m = ∑ τ, χ τ a • Q τ m := by
    intro a m
    simp only [hQ, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hcoef]
    conv_lhs => rw [hom_basis ρ b a]
    simp [Module.End.mul_apply, Module.End.intCast_apply, Int.cast_smul_eq_zsmul]
  have eig : ∀ σ (a : 𝓞 E) (m : M), ρ a (Q σ m) = χ σ a • Q σ m := by
    intro σ a m
    have h1 : ρ a (Q σ m) = ∑ i, Cm i σ • ρ (a * b i) m := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hQ, map_sum, map_smul, map_mul, Module.End.mul_apply]
    rw [h1]
    simp_rw [F3 _ m, map_mul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have h2 : ∀ τ, ∑ i, Cm i σ * (χ τ a * χ τ (b i)) = χ τ a * (if τ = σ then 1 else 0) := by
      intro τ
      rw [← hAC τ σ, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp_rw [h2]
    simp
  have hsum1 : ∀ m : M, ∑ σ, Q σ m = m := by
    intro m
    have := F3 1 m
    simp at this
    exact this.symm
  have hlin : ∀ σ (f : ι → M), Q σ (∑ σ', f σ') = ∑ σ', Q σ (f σ') := by
    intro σ f
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hQ, map_sum, Finset.smul_sum]
    exact Finset.sum_comm
  refine ⟨fun m => ⟨fun σ => Q σ m, fun σ a => eig σ a m, hsum1 m⟩, ?_⟩
  intro mσ hmσ hsum σ
  have hQe : ∀ τ σ', Q τ (mσ σ') = if σ' = τ then mσ σ' else 0 := by
    intro τ σ'
    simp only [hQ, hmσ, smul_smul]
    rw [← Finset.sum_smul]
    rw [show ∑ i, Cm i τ * χ σ' (b i) = if σ' = τ then 1 else 0 from by
      rw [← hAC σ' τ]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _]
    split_ifs <;> simp
  have h0 : Q σ (∑ σ', mσ σ') = 0 := by
    rw [hsum]
    simp [hQ]
  rw [hlin] at h0
  simpa [hQe] using h0

end Core

section NT

variable (E : Type) [Field E] [NumberField E]

theorem isUnit_of_not_dvd {V : Type} [CommRing V] [IsLocalRing V] (g : ℕ) (hg : g.Prime) (hgV : ¬ IsUnit (g : V))
    (d : ℤ) (hd : ¬ (g : ℤ) ∣ d) : IsUnit (d : V) := by
  have hp : Prime (g : ℤ) := Nat.prime_iff_prime_int.mp hg
  obtain ⟨u, v, huv⟩ := (Irreducible.coprime_iff_not_dvd hp.irreducible).2 hd
  have h1 : (u : V) * (g : V) + (v : V) * (d : V) = 1 := by
    have := congrArg (Int.cast : ℤ → V) huv
    push_cast at this
    exact this
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h1 with h | h
  · exact absurd (isUnit_of_mul_isUnit_right h) hgV
  · exact isUnit_of_mul_isUnit_right h

end NT

end Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg
end
end
