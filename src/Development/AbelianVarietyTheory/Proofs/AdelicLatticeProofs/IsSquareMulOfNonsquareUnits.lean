module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareOfValuedSubOneLt
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareMulOfNonsquareUnits
open NumberField IsDedekindDomain GlobalTheory.QNorm IsLocalRing
open scoped WithZero

namespace GlobalTheory.QNorm

theorem _root_.GlobalTheory.QNorm.isSquare_of_isSquare_residue_odd (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (h2 : Valued.v (2 : v.adicCompletion F) = 1)
    (z : v.adicCompletionIntegers F) (hz : Valued.v (z : v.adicCompletion F) = 1)
    (h : IsSquare (residue (v.adicCompletionIntegers F) z)) :
    IsSquare (z : v.adicCompletion F) := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨w, rfl⟩ := residue_surjective r
  have hmem : z - w * w ∈ maximalIdeal (v.adicCompletionIntegers F) := by
    rw [← residue_eq_zero_iff, map_sub, map_mul, hr, sub_self]
  have hlt : Valued.v ((z : v.adicCompletion F) - w * w) < 1 := by
    have hnu : ¬ IsUnit (z - w * w) := hmem
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hnu
    have hle := ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 (z - w * w).2)
    push_cast at hnu hle
    exact lt_of_le_of_ne hle hnu
  have hw : Valued.v (w : v.adicCompletion F) = 1 := by
    by_contra hne
    have hwle := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 w.2
    have hw1 : Valued.v (w : v.adicCompletion F) < 1 := lt_of_le_of_ne hwle hne
    have : Valued.v (z : v.adicCompletion F) < 1 := by
      have hsplit : (z : v.adicCompletion F) = ((z : v.adicCompletion F) - w * w) + w * w := by ring
      rw [hsplit]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hlt ?_)
      rw [map_mul]
      calc Valued.v (w : v.adicCompletion F) * Valued.v (w : v.adicCompletion F)
          ≤ 1 * Valued.v (w : v.adicCompletion F) := by gcongr
        _ < 1 := by rw [one_mul]; exact hw1
    rw [hz] at this
    exact lt_irrefl _ this
  have hw0 : (w : v.adicCompletion F) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hw; exact zero_ne_one hw
  have h4 : Valued.v (4 : v.adicCompletion F) = 1 := by
    rw [show (4 : v.adicCompletion F) = 2 * 2 by norm_num, map_mul, h2, one_mul]
  have hsq : IsSquare ((z : v.adicCompletion F) / (w * w)) := by
    apply _root_.GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt
    rw [h4, show (z : v.adicCompletion F) / (w * w) - 1 = ((z : v.adicCompletion F) - w * w) / (w * w) by
      field_simp, map_div₀, map_mul, hw, mul_one, div_one]
    exact hlt
  obtain ⟨s, hs⟩ := hsq
  refine ⟨s * w, ?_⟩
  have : (z : v.adicCompletion F) = (z : v.adicCompletion F) / (w * w) * (w * w) := by
    field_simp
  rw [this, hs]
  ring

theorem _root_.GlobalTheory.QNorm.isSquare_mul_of_nonsquare_units : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), Valued.v (2 : v.adicCompletion F) = 1 → ∀ x y : v.adicCompletion F, Valued.v x = 1 → Valued.v y = 1 → ¬ IsSquare x → ¬ IsSquare y → IsSquare (x * y) := by
  intro F _ _ v h2 x y hx hy hnx hny
  classical
  haveI : Fintype (ResidueField (v.adicCompletionIntegers F)) :=
    @Fintype.ofFinite _ (_root_.GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v)
  let x' : v.adicCompletionIntegers F :=
    ⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 hx.le⟩
  let y' : v.adicCompletionIntegers F :=
    ⟨y, (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 hy.le⟩
  have hrx : ¬ IsSquare (residue (v.adicCompletionIntegers F) x') :=
    fun h => hnx (_root_.GlobalTheory.QNorm.isSquare_of_isSquare_residue_odd F v h2 x' hx h)
  have hry : ¬ IsSquare (residue (v.adicCompletionIntegers F) y') :=
    fun h => hny (_root_.GlobalTheory.QNorm.isSquare_of_isSquare_residue_odd F v h2 y' hy h)
  have hx0 : residue (v.adicCompletionIntegers F) x' ≠ 0 := fun h => hrx (h ▸ ⟨0, by simp⟩)
  have hy0 : residue (v.adicCompletionIntegers F) y' ≠ 0 := fun h => hry (h ▸ ⟨0, by simp⟩)
  have hres : IsSquare (residue (v.adicCompletionIntegers F) (x' * y')) := by
    rw [map_mul, ← quadraticChar_one_iff_isSquare (mul_ne_zero hx0 hy0), map_mul,
      quadraticChar_neg_one_iff_not_isSquare.2 hrx, quadraticChar_neg_one_iff_not_isSquare.2 hry]
    norm_num
  have hxy : Valued.v (((x' * y' : v.adicCompletionIntegers F)) : v.adicCompletion F) = 1 := by
    push_cast
    rw [map_mul]
    simp [x', y', hx, hy]
  simpa [x', y'] using _root_.GlobalTheory.QNorm.isSquare_of_isSquare_residue_odd F v h2 (x' * y') hxy hres

end GlobalTheory.QNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqPowMulPthPowAdicCompletionUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqPowMulPthPowAdicCompletionUnit
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm IsLocalRing
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_eq_pow_mul_pow_of_isCyclic {G : Type*} [CommGroup G] [IsCyclic G] {p : ℕ}
    (hp : p.Prime) {x : G} (hx : ∀ r : G, r ^ p ≠ x) (y : G) :
    ∃ (k : ℕ) (r : G), y = x ^ k * r ^ p := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg x)
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg y)
  have hpa : ¬ (p : ℤ) ∣ a := by
    rintro ⟨c, rfl⟩
    exact hx (g ^ c) (by rw [← zpow_natCast, ← zpow_mul, mul_comm])
  have hcop : IsCoprime (p : ℤ) a :=
    ((Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd).2 hpa
  obtain ⟨u, w, huw⟩ := hcop
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg (b * w) hp0)
  refine ⟨k, g ^ (b * u + a * (b * w / p)), ?_⟩
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hk]
  congr 1
  have := Int.emod_add_mul_ediv (b * w) p
  linear_combination (-b) * huw - a * this

theorem exists_pow_eq_of_residue_pow {R : Type*} [CommRing R] [IsLocalRing R]
    [HenselianRing R (maximalIdeal R)] {n : ℕ} (hn : IsUnit (n : R)) {u : R} (hu : IsUnit u)
    (c : ResidueField R) (hc : c ^ n = residue R u) : ∃ v : R, v ^ n = u := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  obtain ⟨a, rfl⟩ := residue_surjective c
  have ha : IsUnit a := by
    have : IsUnit (residue R a ^ n) := hc ▸ hu.map _
    exact (isUnit_map_iff (residue R) a).1 ((isUnit_pow_iff hn0).1 this)
  obtain ⟨v, hv, -⟩ := HenselianRing.is_henselian (I := maximalIdeal R) (X ^ n - C u : R[X])
    (monic_X_pow_sub_C u hn0) a
    (by rw [← residue_eq_zero_iff]; simp [hc])
    (IsUnit.map _ (by simpa [derivative_X_pow] using hn.mul (ha.pow _)))
  exact ⟨v, by simpa [sub_eq_zero] using hv⟩

theorem exists_eq_pow_mul_pow_of_henselian {R : Type*} [CommRing R] [IsLocalRing R]
    [HenselianRing R (maximalIdeal R)] [Finite (ResidueField R)] {p : ℕ} (hp : p.Prime)
    (hn : IsUnit (p : R)) (x y : Rˣ) (hx : ∀ r : R, r ^ p ≠ x) :
    ∃ (k : ℕ) (r : R), (y : R) = x ^ k * r ^ p := by
  let f : Rˣ →* (ResidueField R)ˣ := Units.map (residue R : R →* ResidueField R)
  have hx' : ∀ r : (ResidueField R)ˣ, r ^ p ≠ f x := by
    intro r hr
    obtain ⟨s, hs⟩ := exists_pow_eq_of_residue_pow hn x.isUnit (r : ResidueField R)
      (by rw [← Units.val_pow_eq_pow_val, hr]; rfl)
    exact hx s hs
  obtain ⟨k, r, hr⟩ := exists_eq_pow_mul_pow_of_isCyclic hp hx' (f y)
  have h1 : r ^ p = f ((x ^ k)⁻¹ * y) := by
    rw [map_mul, map_inv, map_pow, hr, inv_mul_cancel_left]
  obtain ⟨s, hs⟩ := exists_pow_eq_of_residue_pow hn ((x ^ k)⁻¹ * y).isUnit (r : ResidueField R)
    (by rw [← Units.val_pow_eq_pow_val, h1]; rfl)
  refine ⟨k, s, ?_⟩
  rw [hs, ← Units.val_pow_eq_pow_val, ← Units.val_mul, mul_inv_cancel_left]

theorem exists_eq_pow_mul_pow_of_unit : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletion F), p.Prime → v.valuation F (p : F) = 1 → Valued.v x = 1 → Valued.v y = 1 → (∀ r : v.adicCompletion F, r ^ p ≠ x) → ∃ (k : ℕ) (r : v.adicCompletion F), y = x ^ k * r ^ p := by
  intro p F _ _ v x y hp hv hx hy hx'
  haveI := GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  let a : v.adicCompletionIntegers F := ⟨x, hx.le⟩
  let b : v.adicCompletionIntegers F := ⟨y, hy.le⟩
  have ha : IsUnit a := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hx
  have hb : IsUnit b := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hy
  have hn : IsUnit (p : v.adicCompletionIntegers F) := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    have h := (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (p : F)).trans hv
    have e : ((p : v.adicCompletionIntegers F) : v.adicCompletion F) =
        algebraMap F (v.adicCompletion F) (p : F) := by simp
    rw [e]
    exact h
  obtain ⟨k, r, hr⟩ := exists_eq_pow_mul_pow_of_henselian hp hn ha.unit hb.unit
    (fun r hr => hx' r (congrArg Subtype.val hr))
  exact ⟨k, r, congrArg Subtype.val hr⟩

end GlobalTheory.CNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqPowMulPthPowAdicCompletionUnitStatement
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_pow_mul_pth_pow_adicCompletion_unit : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletion F), p.Prime → v.valuation F (p : F) = 1 → Valued.v x = 1 → Valued.v y = 1 → (∀ r : v.adicCompletion F, r ^ p ≠ x) → ∃ (k : ℕ) (r : v.adicCompletion F), y = x ^ k * r ^ p := by
  first | exact @GlobalTheory.CNorm.exists_eq_pow_mul_pow_of_unit | exact GlobalTheory.CNorm.exists_eq_pow_mul_pow_of_unit | (intros; apply GlobalTheory.CNorm.exists_eq_pow_mul_pow_of_unit <;> assumption)
end
end
