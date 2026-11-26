module

public import Formalism.PeriodIntegrals.QuotInv

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DeterminantKernelFiniteness.ExistsDenomBackward
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DeterminantKernelFiniteness.ExistsNatMulMemFracFam
noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KerDetFinW

open PI.KerIso

lemma natCast_mem_int {K : Type} [Field K] [NumberField K] (N : ℕ) :
    (N : K) ∈ (algebraMap (𝓞 K) K).range :=
  ⟨N, map_natCast _ _⟩

lemma exists_nat_mul_mem_int {K : Type} [Field K] [NumberField K] (x : K) :
    ∃ d : ℕ, 0 < d ∧ (d : K) * x ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨y, hy0, hy⟩ := (IsFractionRing.isAlgebraic_iff ℤ ℚ K |>.mpr (.of_finite ℚ x)).exists_integral_multiple
  have h1 : (y : K) * x ∈ (algebraMap (𝓞 K) K).range := by
    refine ⟨⟨y • x, hy⟩, ?_⟩
    show y • x = _
    rw [zsmul_eq_mul]
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, ?_⟩
  rcases Int.natAbs_eq y with h | h
  · have : ((y.natAbs : ℕ) : K) = (y : K) := by
      conv_rhs => rw [h]
      simp
    rw [this]; exact h1
  · have : ((y.natAbs : ℕ) : K) = -(y : K) := by
      conv_rhs => rw [h]
      simp
    rw [this, neg_mul]; exact neg_mem h1

lemma exists_nat_mul_mem_int_fam {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
    (f : ι → K) : ∃ N : ℕ, 0 < N ∧ ∀ i, (N : K) * f i ∈ (algebraMap (𝓞 K) K).range := by
  choose d hd0 hd using fun i => exists_nat_mul_mem_int (f i)
  refine ⟨∏ i, d i, Finset.prod_pos fun i _ => hd0 i, fun i => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  rw [hc, Nat.cast_mul, mul_comm (d i : K), mul_assoc]
  exact mul_mem (natCast_mem_int c) (hd i)

lemma int_mul_mem {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) {k : K} (hk : k ∈ (algebraMap (𝓞 K) K).range)
    {y : E} (hy : y ∈ I) : algebraMap K E k * y ∈ I := by
  obtain ⟨z, rfl⟩ := hk
  have hz : IsIntegral ℤ (algebraMap K E (algebraMap (𝓞 K) K z)) :=
    (RingOfIntegers.isIntegral_coe z).map (algebraMap K E).toIntAlgHom
  have := (I : Submodule (𝓞 E) E).smul_mem (⟨_, hz⟩ : 𝓞 E) hy
  have e : ((⟨_, hz⟩ : 𝓞 E) • y) = algebraMap K E (algebraMap (𝓞 K) K z) * y := Algebra.smul_def _ _
  rw [← FractionalIdeal.mem_coe]
  convert this using 1
  exact e.symm

lemma nat_mul_mem {E : Type} [Field E] [NumberField E]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (c : ℕ) {y : E} (hy : y ∈ I) :
    (c : E) * y ∈ I := by
  have := (I : Submodule (𝓞 E) E).smul_mem (c : 𝓞 E) hy
  rw [Algebra.smul_def, map_natCast] at this
  exact this

lemma exists_nat_mul_mem_frac {E : Type} [Field E] [NumberField E]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) (y : E) :
    ∃ d : ℕ, 0 < d ∧ (d : E) * y ∈ I := by
  have hbot : (I : Submodule (𝓞 E) E) ≠ ⊥ := fun h => hI (FractionalIdeal.coeToSubmodule_eq_bot.1 h)
  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨d, hd0, z, hz⟩ := exists_nat_mul_mem_int (y / a)
  refine ⟨d, hd0, ?_⟩
  have hmem := (I : Submodule (𝓞 E) E).smul_mem z haI
  rw [Algebra.smul_def, hz] at hmem
  have : (d : E) * (y / a) * a = (d : E) * y := by field_simp
  rw [this] at hmem
  exact hmem

lemma exists_nat_mul_mem_frac_fam {E : Type} [Field E] [NumberField E]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) {ι : Type} [Fintype ι]
    (f : ι → E) : ∃ N : ℕ, 0 < N ∧ ∀ i, (N : E) * f i ∈ I := by
  choose d hd0 hd using fun i => exists_nat_mul_mem_frac I hI (f i)
  refine ⟨∏ i, d i, Finset.prod_pos fun i _ => hd0 i, fun i => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  rw [hc, Nat.cast_mul, mul_comm (d i : E), mul_assoc]
  exact nat_mul_mem I c (hd i)

end PI.KerDetFinW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DeterminantKernelFiniteness.ValuationLeOneOfDenom
noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KerDetFinW

open PI.KerIso

lemma det_mem_of_entries {K : Type} [Field K] (R : Subring K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (h : ∀ i j, A i j ∈ R) : A.det ∈ R := by
  have hB : R.subtype.mapMatrix (Matrix.of fun i j => (⟨A i j, h i j⟩ : R)) = A := by
    ext i j
    rfl
  rw [← hB, ← RingHom.map_det]
  exact SetLike.coe_mem _

lemma det_denom {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ℕ) (A : Matrix ι ι K) (u : ι → ℕ) (hu : ∀ j, Nat.Coprime (u j) p)
    (hA : ∀ i j, (u j : K) * A i j ∈ (algebraMap (𝓞 K) K).range) :
    ∃ U : ℕ, Nat.Coprime U p ∧ (U : K) * A.det ∈ (algebraMap (𝓞 K) K).range := by
  refine ⟨∏ j, u j, Nat.Coprime.prod_left (fun j _ => hu j), ?_⟩
  have h1 : ((∏ j, u j : ℕ) : K) * A.det = (A * Matrix.diagonal (fun j => (u j : K))).det := by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    push_cast
    ring
  rw [h1]
  apply det_mem_of_entries
  intro i j
  rw [Matrix.mul_diagonal, mul_comm]
  exact hA i j

lemma valuation_natCast_eq_one {K : Type} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {p U : ℕ}
    (hp𝔭 : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal) (hU : Nat.Coprime U p) :
    𝔭.valuation K (U : K) = 1 := by
  have hU' : ((U : ℕ) : 𝓞 K) ∉ 𝔭.asIdeal := by
    intro hmem
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hU
    apply 𝔭.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h2 : ((a * (U : ℤ) + b * (p : ℤ) : ℤ) : 𝓞 K) ∈ 𝔭.asIdeal := by
      push_cast
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hp𝔭)
    rw [hab, Int.cast_one] at h2
    exact h2
  have hK : ((U : ℕ) : K) = algebraMap (𝓞 K) K (U : 𝓞 K) := (map_natCast _ _).symm
  rw [hK, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  refine le_antisymm (𝔭.intValuation_le_one _) (not_lt.mp fun hlt => hU' ?_)
  exact Ideal.dvd_span_singleton.mp ((𝔭.intValuation_lt_one_iff_dvd _).mp hlt)

lemma valuation_le_one_of_denom {K : Type} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {p U : ℕ}
    (hp𝔭 : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal) (hU : Nat.Coprime U p) {x : K}
    (hx : (U : K) * x ∈ (algebraMap (𝓞 K) K).range) : 𝔭.valuation K x ≤ 1 := by
  obtain ⟨r, hr⟩ := hx
  have h1 : 𝔭.valuation K (U : K) = 1 := valuation_natCast_eq_one 𝔭 hp𝔭 hU
  have h2 : 𝔭.valuation K ((U : K) * x) ≤ 1 := by
    rw [← hr, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact 𝔭.intValuation_le_one r
  rwa [map_mul, h1, one_mul] at h2

lemma comp_denom {K E : Type} [Field K] [NumberField K] [Field E] [Algebra K E] {n : Type} [Fintype n]
    {M : Set E} {g g' : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)} {p : ℕ}
    (hg : AtP M g p) (hg' : AtP M g' p) (v : Fin 4 × n → K)
    (hv : ∀ w, v w ∈ (algebraMap (𝓞 K) K).range) :
    ∃ u : ℕ, Nat.Coprime u p ∧ ∀ w, (u : K) * (g.symm.trans g') v w ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨s, hs, hsM⟩ := hg.2 v hv
  have hx : ∀ a, ((s : K) • g.symm v) a ∈ M := by
    intro a
    rw [Pi.smul_apply, Algebra.smul_def, map_natCast]
    exact hsM a
  obtain ⟨t, ht, htM⟩ := hg'.1 ((s : K) • g.symm v) hx
  refine ⟨t * s, Nat.Coprime.mul_left ht hs, fun w => ?_⟩
  have h := htM w
  rw [map_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc] at h
  rw [LinearEquiv.trans_apply, Nat.cast_mul]
  exact h

lemma det_valuation_le_one {K E : Type} [Field K] [NumberField K] [Field E] [Algebra K E] {n : Type}
    [Fintype n] {M : Set E} {g g' : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)} {p : ℕ}
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (hp𝔭 : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal)
    (hg : AtP M g p) (hg' : AtP M g' p) :
    𝔭.valuation K (LinearMap.det ((g.symm.trans g' : (Fin 4 × n → K) ≃ₗ[K] _) :
      (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K))) ≤ 1 := by
  classical
  set f := ((g.symm.trans g' : (Fin 4 × n → K) ≃ₗ[K] _) :
    (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K)) with hf
  have hcol : ∀ j : Fin 4 × n, ∃ u : ℕ, Nat.Coprime u p ∧
      ∀ i, (u : K) * LinearMap.toMatrix' f i j ∈ (algebraMap (𝓞 K) K).range := by
    intro j
    have hv : ∀ w, (Pi.single j (1 : K) : Fin 4 × n → K) w ∈ (algebraMap (𝓞 K) K).range := by
      intro w
      by_cases hw : w = j
      · subst hw
        rw [Pi.single_eq_same]
        exact one_mem _
      · rw [Pi.single_eq_of_ne hw]
        exact zero_mem _
    obtain ⟨u, hu, hu'⟩ := comp_denom hg hg' (Pi.single j (1 : K)) hv
    exact ⟨u, hu, fun i => by rw [LinearMap.toMatrix'_apply]; exact hu' i⟩
  choose u hu hu' using hcol
  obtain ⟨U, hU, hUd⟩ := det_denom p (LinearMap.toMatrix' f) u hu (fun i j => hu' j i)
  rw [LinearMap.det_toMatrix'] at hUd
  exact valuation_le_one_of_denom 𝔭 hp𝔭 hU hUd

theorem ordK_detRel_eq_zero {K E : Type} [Field K] [NumberField K] [Field E] [Algebra K E] {n : Type}
    [Fintype n] {M : Set E} {g g' : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)} {p : ℕ}
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (hp𝔭 : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal)
    (hg : AtP M g p) (hg' : AtP M g' p) : ordK 𝔭 (detRel g' g) = 0 := by
  have h1 : 𝔭.valuation K (detRel g' g) ≤ 1 := det_valuation_le_one 𝔭 hp𝔭 hg hg'
  have h2 : 𝔭.valuation K (detRel g g') ≤ 1 := det_valuation_le_one 𝔭 hp𝔭 hg' hg
  have hprod : detRel g' g * detRel g g' = 1 := by
    unfold detRel
    rw [← LinearMap.det_comp]
    have hc : ((g.symm.trans g' : (Fin 4 × n → K) ≃ₗ[K] _) :
        (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K)).comp
        ((g'.symm.trans g : (Fin 4 × n → K) ≃ₗ[K] _) :
        (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K)) = LinearMap.id :=
      LinearMap.ext fun x => by simp
    rw [hc, LinearMap.det_id]
  have hm : 𝔭.valuation K (detRel g' g) * 𝔭.valuation K (detRel g g') = 1 := by
    rw [← map_mul, hprod, map_one]
  have hv : 𝔭.valuation K (detRel g' g) = 1 := by
    refine le_antisymm h1 ?_
    calc 1 = 𝔭.valuation K (detRel g' g) * 𝔭.valuation K (detRel g g') := hm.symm
      _ ≤ 𝔭.valuation K (detRel g' g) * 1 := by gcongr
      _ = 𝔭.valuation K (detRel g' g) := mul_one _
  unfold ordK
  rw [hv]
  simp

end PI.KerDetFinW
end
end

noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KerDetFinW

open PI.KerIso

lemma exists_denom_forward {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    {n : Type} [Fintype n] (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : Fin 4 → E, (∀ a, x a ∈ I) → ∀ w,
      (N : K) * g₀ x w ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨α, hα, hαI⟩ := I.isFractional
  have hα0 : algebraMap (𝓞 E) E α ≠ 0 := by
    intro h
    exact nonZeroDivisors.ne_zero hα
      ((map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).1 h)
  let b := RingOfIntegers.basis E
  let φ : Fin 4 → Fin 4 × n → (E →ₗ[K] K) := fun a w =>
    LinearMap.proj w ∘ₗ (g₀ : (Fin 4 → E) →ₗ[K] (Fin 4 × n → K)) ∘ₗ
      LinearMap.single K (fun _ : Fin 4 => E) a
  obtain ⟨N, hN0, hN⟩ := exists_nat_mul_mem_int_fam
    (fun q : Fin 4 × Module.Free.ChooseBasisIndex ℤ (𝓞 E) × (Fin 4 × n) =>
      φ q.1 q.2.2 ((algebraMap (𝓞 E) E α)⁻¹ * algebraMap (𝓞 E) E (b q.2.1)))
  refine ⟨N, hN0, fun x hx w => ?_⟩
  have hxs : g₀ x w = ∑ a, φ a w (x a) := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply]
    rfl
  have hterm : ∀ a, (N : K) * φ a w (x a) ∈ (algebraMap (𝓞 K) K).range := by
    intro a
    obtain ⟨z, hz⟩ := hαI (x a) (FractionalIdeal.mem_coe.2 (hx a))
    have hxa : x a = ∑ i, (b.repr z i) • ((algebraMap (𝓞 E) E α)⁻¹ * algebraMap (𝓞 E) E (b i)) := by
      have h1 : x a = (algebraMap (𝓞 E) E α)⁻¹ * algebraMap (𝓞 E) E z := by
        rw [hz, Algebra.smul_def, inv_mul_cancel_left₀ hα0]
      rw [h1]
      conv_lhs => rw [← b.sum_repr z]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, mul_smul_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hxa, map_sum, Finset.mul_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [map_zsmul, mul_smul_comm]
    exact zsmul_mem (hN (a, i, w)) _
  rw [hxs, Finset.mul_sum]
  exact Subring.sum_mem _ fun a _ => hterm a

lemma exists_denom_backward {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    {n : Type} [Fintype n] (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0)
    (g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)) :
    ∃ N : ℕ, 0 < N ∧ ∀ v : Fin 4 × n → K, (∀ w, v w ∈ (algebraMap (𝓞 K) K).range) → ∀ a,
      (N : E) * g₀.symm v a ∈ I := by
  classical
  obtain ⟨N, hN0, hN⟩ := exists_nat_mul_mem_frac_fam I hI
    (fun q : (Fin 4 × n) × Fin 4 => g₀.symm (Pi.single q.1 1) q.2)
  refine ⟨N, hN0, fun v hv a => ?_⟩
  have hv' : g₀.symm v = ∑ w, v w • g₀.symm (Pi.single w 1) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← map_smul]
    congr 1
    ext j
    rw [Pi.single_apply, Pi.smul_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [hv', Finset.sum_apply, Finset.mul_sum, ← FractionalIdeal.mem_coe]
  refine Submodule.sum_mem _ fun w _ => ?_
  rw [FractionalIdeal.mem_coe, Pi.smul_apply, Algebra.smul_def, mul_left_comm]
  exact int_mul_mem I (hv w) (hN (w, a))

theorem detOrdFin : DetOrdFin := by
  intro K E _ _ _ _ _ n _ I hI S pp gp g₀ hpp hgp
  obtain ⟨N₁, h1pos, h1⟩ := exists_denom_forward (K := K) I g₀
  obtain ⟨N₂, h2pos, h2⟩ := exists_denom_backward I hI g₀
  have hg₀ : ∀ p, p.Prime → ¬ p ∣ N₁ * N₂ → AtP {x : E | x ∈ I} g₀ p := by
    intro p hp hdvd
    have hcop : Nat.Coprime (N₁ * N₂) p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hdvd).symm
    exact ⟨fun x hx => ⟨N₁, Nat.Coprime.coprime_dvd_left (dvd_mul_right N₁ N₂) hcop, h1 x hx⟩,
      fun v hv => ⟨N₂, Nat.Coprime.coprime_dvd_left (dvd_mul_left N₂ N₁) hcop, h2 v hv⟩⟩
  refine (Nat.divisors (N₁ * N₂)).finite_toSet.subset ?_
  rintro p ⟨hp, hS, hne⟩
  rw [Finset.mem_coe, Nat.mem_divisors]
  refine ⟨?_, (Nat.mul_pos h1pos h2pos).ne'⟩
  by_contra hdvd
  exact hne (ordK_detRel_eq_zero (pp p) (hpp p hp hS) (hg₀ p hp hdvd) (hgp p hp hS))

end PI.KerDetFinW
end
end

theorem ordRelativeDet_finite : PI.KerIso.DetOrdFin := PI.KerDetFinW.detOrdFin
