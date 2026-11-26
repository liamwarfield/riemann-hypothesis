module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem disc_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = (c ^ 12)⁻¹ * (4096 * (Real.pi : ℂ) ^ 12) * DD τ := by
  have hc : c ≠ 0 := h.1
  have hD : DD τ = (E₄ τ ^ 3 - E₆ τ ^ 2) / 1728 := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ
  rw [g₂_eq h, g₃_eq h, hD]
  field_simp
  ring

theorem jInv_eq_jT {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) : jInv L = jT τ := by
  have hc : c ≠ 0 := h.1
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hDD : DD τ ≠ 0 := DD_ne_zero τ
  show 1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = E₄ τ ^ 3 / DD τ
  rw [disc_eq h, g₂_eq h]
  field_simp
  ring

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGBasic
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem mem_Aio {d l : ℕ} [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (x : Om d) : x ∈ Aio d l ι ↔ ‖ι (x : ℂ)‖ ≤ 1 := by
  rw [Aio, ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff, NormedField.valuation_apply,
    ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  try exact Iff.rfl

theorem mem_nonunits_Aio {d l : ℕ} [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (x : Om d) :
    x ∈ (Aio d l ι).nonunits ↔ ‖ι (x : ℂ)‖ < 1 := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal (A := Aio d l ι)]
  constructor
  · rintro ⟨h1, h2⟩
    have hle : ‖ι (x : ℂ)‖ ≤ 1 := (mem_Aio ι x).1 h1
    refine lt_of_le_of_ne hle fun heq => ?_
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h2
    apply h2
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at heq
    have hinv : x⁻¹ ∈ Aio d l ι :=
      (mem_Aio ι x⁻¹).2 (le_of_eq (by rw [IntermediateField.coe_inv, map_inv₀, norm_inv, heq, inv_one]))
    have hm : (⟨x, h1⟩ : Aio d l ι) * ⟨x⁻¹, hinv⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hx0)
    exact ⟨⟨_, _, hm, (mul_comm _ _).trans hm⟩, rfl⟩
  · intro h
    refine ⟨(mem_Aio ι x).2 h.le, ?_⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have hy := (mem_Aio ι (((u⁻¹ : (Aio d l ι)ˣ) : Aio d l ι) : Om d)).1 ((u⁻¹ : (Aio d l ι)ˣ) : Aio d l ι).2
    have h0 : ((u : Aio d l ι) : Om d) * (((u⁻¹ : (Aio d l ι)ˣ) : Aio d l ι) : Om d) = 1 :=
      congrArg Subtype.val u.mul_inv
    rw [hu] at h0
    have hmul : (x : ℂ) * ((((u⁻¹ : (Aio d l ι)ˣ) : Aio d l ι) : Om d) : ℂ) = 1 :=
      congrArg (fun t : Om d => (t : ℂ)) h0
    have hn : ‖ι (x : ℂ)‖ * ‖ι ((((u⁻¹ : (Aio d l ι)ˣ) : Aio d l ι) : Om d) : ℂ)‖ = 1 := by
      simpa using congrArg (fun t => ‖ι t‖) hmul
    nlinarith [norm_nonneg (ι (x : ℂ)), mul_le_mul_of_nonneg_left hy (norm_nonneg (ι (x : ℂ)))]

theorem mem_of_isIntegral {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) {x : Ω} (hx : IsIntegral ℤ x) : x ∈ A := by
  have h2 : IsIntegral A x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hy]
  exact y.2

theorem exists_Om (d : ℕ) {z : ℂ} (hz : IsIntegral ℤ z) : ∃ x : Om d, (x : ℂ) = z ∧ IsIntegral ℤ x := by
  have hzK : IsIntegral (KQ d) z := hz.tower_top
  have hmem : z ∈ Om d := hzK
  refine ⟨⟨z, hmem⟩, rfl, ?_⟩
  exact (isIntegral_algHom_iff (x := (⟨z, hmem⟩ : Om d)) (algebraMap (Om d) ℂ).toIntAlgHom
    (algebraMap (Om d) ℂ).injective).mp hz

theorem Om_isAlgebraic (d : ℕ) (x : Om d) : IsAlgebraic ℚ (x : ℂ) := by
  have hx : IsIntegral (KQ d) (x : ℂ) := x.2
  exact (isIntegral_trans (R := ℚ) _ hx).isAlgebraic

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDeltaInt
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem twelve_dvd_five_pow_three_add_seven_pow_five (d : ℤ) : (12 : ℤ) ∣ 5 * d ^ 3 + 7 * d ^ 5 := by
  have key : ∀ x : ZMod 12, 5 * x ^ 3 + 7 * x ^ 5 = 0 := by decide
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (5 * d ^ 3 + 7 * d ^ 5) 12).mp
    (by push_cast; exact key _)
  exact_mod_cast h

theorem sigma_congr (n : ℕ) :
    (12 : ℤ) ∣ 5 * (ArithmeticFunction.sigma 3 n : ℤ) + 7 * (ArithmeticFunction.sigma 5 n : ℤ) := by
  rw [ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.dvd_sum fun d _ => twelve_dvd_five_pow_three_add_seven_pow_five _

def s3Z : PowerSeries ℤ := PowerSeries.mk fun n => (ArithmeticFunction.sigma 3 n : ℤ)

def s5Z : PowerSeries ℤ := PowerSeries.mk fun n => (ArithmeticFunction.sigma 5 n : ℤ)

def tZ : PowerSeries ℤ := PowerSeries.mk fun n =>
  (5 * (ArithmeticFunction.sigma 3 n : ℤ) + 7 * (ArithmeticFunction.sigma 5 n : ℤ)) / 12

theorem eisensteinFourInt_eq : e4Z = 1 + PowerSeries.C (240 : ℤ) * s3Z := by
  ext n
  simp only [e4Z, s3Z, map_add (f := _), PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_one]
  split_ifs with h
  · subst h; simp
  · ring

theorem eisensteinSixInt_eq : e6Z = 1 - PowerSeries.C (504 : ℤ) * s5Z := by
  ext n
  simp only [e6Z, s5Z, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_one]
  split_ifs with h
  · subst h; simp
  · ring

theorem tZ_mul : PowerSeries.C (12 : ℤ) * tZ =
    PowerSeries.C (5 : ℤ) * s3Z + PowerSeries.C (7 : ℤ) * s5Z := by
  ext n
  simp only [map_add (f := _), PowerSeries.coeff_C_mul, tZ, s3Z, s5Z, PowerSeries.coeff_mk]
  exact Int.mul_ediv_cancel' (sigma_congr n)

theorem eisenstein_cube_sub_sq_eq : e4Z ^ 3 - e6Z ^ 2 = PowerSeries.C (1728 : ℤ) *
    (tZ + PowerSeries.C (100 : ℤ) * s3Z ^ 2 + PowerSeries.C (8000 : ℤ) * s3Z ^ 3
      - PowerSeries.C (147 : ℤ) * s5Z ^ 2) := by
  have h := tZ_mul
  rw [eisensteinFourInt_eq, eisensteinSixInt_eq]
  simp only [map_ofNat] at h ⊢
  linear_combination (-144 : PowerSeries ℤ) * h

theorem dZ_mul : PowerSeries.C (1728 : ℤ) * dZ = e4Z ^ 3 - e6Z ^ 2 := by
  ext n
  rw [PowerSeries.coeff_C_mul, dZ, PowerSeries.coeff_mk, eisenstein_cube_sub_sq_eq, PowerSeries.coeff_C_mul]
  exact Int.mul_ediv_cancel' (dvd_mul_right _ _)

private theorem dZ_eq_tZ_add_s3Z_sq_add_s3Z_cube_sub_s5Z_sq : dZ = tZ + PowerSeries.C (100 : ℤ) * s3Z ^ 2 +
    PowerSeries.C (8000 : ℤ) * s3Z ^ 3 - PowerSeries.C (147 : ℤ) * s5Z ^ 2 := by
  have h := dZ_mul.trans eisenstein_cube_sub_sq_eq
  refine mul_left_cancel₀ (fun h0 => ?_) h
  have := congrArg PowerSeries.constantCoeff h0
  rw [PowerSeries.constantCoeff_C, map_zero] at this
  norm_num at this

theorem dZ_coeff_zero : PowerSeries.coeff 0 dZ = 0 := by
  rw [dZ_eq_tZ_add_s3Z_sq_add_s3Z_cube_sub_s5Z_sq]
  simp only [map_sub, map_add (f := _), PowerSeries.coeff_C_mul, pow_succ, pow_zero, one_mul,
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_zero, tZ, s3Z, s5Z, PowerSeries.coeff_mk, ArithmeticFunction.sigma_apply]
  norm_num

theorem dZ_coeff_one : PowerSeries.coeff 1 dZ = 1 := by
  rw [dZ_eq_tZ_add_s3Z_sq_add_s3Z_cube_sub_s5Z_sq]
  simp only [map_sub, map_add (f := _), PowerSeries.coeff_C_mul, pow_succ, pow_zero, one_mul,
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_zero, tZ, s3Z, s5Z, PowerSeries.coeff_mk, ArithmeticFunction.sigma_apply]
  norm_num

theorem dC_eq : dC = qExpansion 1 DD := by
  have h4 : qExpansion 1 ⇑((E₄.mul E₄).mul E₄) = qExpansion 1 E₄ ^ 3 := by
    rw [ModularForm.qExpansion_mul one_pos (by simp), ModularForm.qExpansion_mul one_pos (by simp)]
    ring
  have h6 : qExpansion 1 ⇑(E₆.mul E₆) = qExpansion 1 E₆ ^ 2 := by
    rw [ModularForm.qExpansion_mul one_pos (by simp)]
    ring
  have hfun : DD = ⇑((1 / 1728 : ℂ) • ((E₄.mul E₄).mul E₄)) - ⇑((1 / 1728 : ℂ) • (E₆.mul E₆)) := by
    funext τ
    simp only [DD, ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq, Pi.sub_apply,
      ModularForm.coe_smul, ModularForm.coe_mul, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  have hd := congrArg (PowerSeries.map (Int.castRingHom ℂ)) dZ_mul
  rw [map_mul, map_sub, map_pow, map_pow, PowerSeries.map_C, map_eisensteinFourInt, map_eisensteinSixInt] at hd
  rw [hfun, ModularForm.qExpansion_sub one_pos (by simp), ModularForm.coe_smul, ModularForm.coe_smul,
    ModularForm.qExpansion_smul one_pos (by simp), ModularForm.qExpansion_smul one_pos (by simp),
    h4, h6, ← smul_sub, ← hd, PowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul]
  rw [show (1 / 1728 : ℂ) * (Int.castRingHom ℂ) 1728 = 1 by norm_num, map_one, one_mul]
  rfl

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.CoeffRescaleExpandOfNotDvd
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem coeff_xp {R : Type*} [CommRing R] (k : ℕ) (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (xp k f) = if k ∣ n then PowerSeries.coeff (n / k) f else 0 := by
  rw [xp, PowerSeries.coeff_mk]

theorem xp_eq_expand {R : Type*} [CommRing R] {k : ℕ} (hk : k ≠ 0) (f : PowerSeries R) :
    xp k f = PowerSeries.expand k hk f := by
  ext n
  rw [coeff_xp, PowerSeries.coeff_expand]

theorem xp_add {R : Type*} [CommRing R] (k : ℕ) (f g : PowerSeries R) : xp k (f + g) = xp k f + xp k g := by
  ext n
  simp only [coeff_xp, map_add (f := _)]
  split_ifs <;> simp

theorem xp_sub {R : Type*} [CommRing R] (k : ℕ) (f g : PowerSeries R) : xp k (f - g) = xp k f - xp k g := by
  ext n
  simp only [coeff_xp, map_sub]
  split_ifs <;> simp

theorem xp_mul {R : Type*} [CommRing R] {k : ℕ} (hk : k ≠ 0) (f g : PowerSeries R) :
    xp k (f * g) = xp k f * xp k g := by
  rw [xp_eq_expand hk, xp_eq_expand hk, xp_eq_expand hk, map_mul]

theorem xp_pow {R : Type*} [CommRing R] {k : ℕ} (hk : k ≠ 0) (f : PowerSeries R) (n : ℕ) :
    xp k (f ^ n) = xp k f ^ n := by
  rw [xp_eq_expand hk, xp_eq_expand hk, map_pow]

theorem xp_C_mul {R : Type*} [CommRing R] (k : ℕ) (c : R) (f : PowerSeries R) :
    xp k (PowerSeries.C c * f) = PowerSeries.C c * xp k f := by
  ext n
  simp only [coeff_xp, PowerSeries.coeff_C_mul]
  split_ifs <;> simp

theorem xp_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (k : ℕ) (f : PowerSeries R) :
    xp k (f.map φ) = (xp k f).map φ := by
  ext n
  simp only [coeff_xp, PowerSeries.coeff_map]
  split_ifs <;> simp

theorem CoeffIn.map_int (R : Subring ℂ) (f : PowerSeries ℤ) : CoeffIn R (f.map (Int.castRingHom ℂ)) := by
  intro n
  rw [PowerSeries.coeff_map, eq_intCast]
  exact intCast_mem R _

theorem CoeffIn.add {R : Subring ℂ} {f g : PowerSeries ℂ} (hf : CoeffIn R f) (hg : CoeffIn R g) :
    CoeffIn R (f + g) := by
  intro n
  rw [map_add (f := _)]
  exact add_mem (hf n) (hg n)

theorem CoeffIn.sub {R : Subring ℂ} {f g : PowerSeries ℂ} (hf : CoeffIn R f) (hg : CoeffIn R g) :
    CoeffIn R (f - g) := by
  intro n
  rw [map_sub]
  exact sub_mem (hf n) (hg n)

theorem CoeffIn.mul {R : Subring ℂ} {f g : PowerSeries ℂ} (hf : CoeffIn R f) (hg : CoeffIn R g) :
    CoeffIn R (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  exact sum_mem fun p _ => mul_mem (hf _) (hg _)

theorem CoeffIn.one (R : Subring ℂ) : CoeffIn R 1 := by
  intro n
  rw [PowerSeries.coeff_one]
  split_ifs
  · exact one_mem R
  · exact zero_mem R

theorem CoeffIn.pow {R : Subring ℂ} {f : PowerSeries ℂ} (hf : CoeffIn R f) (n : ℕ) : CoeffIn R (f ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact ReciprocityTheory.ChartRestriction.L1.CoeffIn.one R
  | succ n ih =>
    rw [pow_succ]
    exact ReciprocityTheory.ChartRestriction.L1.CoeffIn.mul ih hf

theorem CoeffIn.xp {R : Subring ℂ} {f : PowerSeries ℂ} (hf : CoeffIn R f) (k : ℕ) : CoeffIn R (xp k f) := by
  intro n
  rw [coeff_xp]
  split_ifs
  · exact hf _
  · exact zero_mem R

theorem CoeffIn.sub1 {R : Subring ℂ} {f : PowerSeries ℂ} (hf : CoeffIn R f) {c : ℂ} (hc : c ∈ R) (k : ℕ) :
    CoeffIn R (sub1 c k f) := by
  have hr : ReciprocityTheory.ChartRestriction.L1.CoeffIn R (PowerSeries.rescale c f) := fun m => by
    rw [PowerSeries.coeff_rescale]
    exact mul_mem (pow_mem hc m) (hf m)
  exact ReciprocityTheory.ChartRestriction.L1.CoeffIn.xp hr k

theorem LowUnit.mul {R : Subring ℂ} {f g : PowerSeries ℂ} {n n' : ℕ} {u u' : ℂ} (hf : LowUnit R f n u)
    (hg : LowUnit R g n' u') : LowUnit R (f * g) (n + n') (u * u') := by
  obtain ⟨hu, hui, hu0, hlow, hc⟩ := hf
  obtain ⟨hu', hui', hu0', hlow', hc'⟩ := hg
  refine ⟨mul_mem hu hu', by rw [mul_inv]; exact mul_mem hui hui', mul_ne_zero hu0 hu0', ?_, ?_⟩
  · intro m hm
    rw [PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    by_cases h1 : p.1 < n
    · rw [hlow _ h1, zero_mul]
    · rw [hlow' _ (by omega), mul_zero]
  · rw [PowerSeries.coeff_mul, Finset.sum_eq_single (n, n')]
    · rw [hc, hc']
    · intro p hp hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      by_cases h1 : p.1 < n
      · rw [hlow _ h1, zero_mul]
      · have h2 : p.2 < n' := by
          by_contra h2
          exact hne (Prod.ext (by show p.1 = n; omega) (by show p.2 = n'; omega))
        rw [hlow' _ h2, mul_zero]
    · intro h
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (rfl : n + n' = n + n')) h

theorem LowUnit.one (R : Subring ℂ) : LowUnit R 1 0 1 := by
  refine ⟨one_mem R, by rw [inv_one]; exact one_mem R, one_ne_zero,
    fun n hn => absurd hn (Nat.not_lt_zero n), ?_⟩
  simp

theorem LowUnit.prod {R : Subring ℂ} {α : Type*} (s : Finset α) (f : α → PowerSeries ℂ)
    (hf : ∀ t ∈ s, ∃ n u, LowUnit R (f t) n u) : ∃ n u, LowUnit R (∏ t ∈ s, f t) n u := Finset.prod_induction f (fun g => ∃ n u, ReciprocityTheory.ChartRestriction.L1.LowUnit R g n u)
    (fun a b ⟨n, u, ha⟩ ⟨n', u', hb⟩ => ⟨n + n', u * u', ReciprocityTheory.ChartRestriction.L1.LowUnit.mul ha hb⟩)
    ⟨0, 1, ReciprocityTheory.ChartRestriction.L1.LowUnit.one R⟩ hf

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModChebOm
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

def ChebOmSt : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (S : Set (HeightOneSpectrum (𝓞 E))) (hS : S.Finite) (H : Subgroup (Ω ≃ₐ[E] Ω)) (hn : H.Normal)
    (ho : IsOpen (H : Set (Ω ≃ₐ[E] Ω)))
    (hI : ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), LiesAbove A v → v ∉ S →
      ∀ g : Ω ≃ₐ[E] Ω, InertiaEl A g → g ∈ H) (σ : Ω ≃ₐ[E] Ω),
    ∃ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)) (φ : Ω ≃ₐ[E] Ω), LiesAbove A v ∧ v ∉ S ∧
      (Nat.card (𝓞 E ⧸ v.asIdeal)).Prime ∧ IsArithFrobenius A v φ ∧ σ⁻¹ * φ ∈ H

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModHnf
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem exists_hermite_normal_form_coords {m : ℕ} (hm : 0 < m) (p q r s : ℤ) (h : p * s - q * r = m) :
    ∃ (x y z w : ℤ) (a b e : ℕ), x * w - y * z = 1 ∧ a * e = m ∧ b < e ∧
      p = x * a ∧ q = x * b + y * e ∧ r = z * a ∧ s = z * b + w * e := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  set g : ℕ := Int.gcd p r with hg
  have hg0 : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · rw [hg, Int.gcd_eq_zero_iff] at h0
      rw [h0.1, h0.2] at h
      simp at h
      omega
    · exact h0
  have hgZ : (0 : ℤ) < g := by exact_mod_cast hg0
  obtain ⟨x, hx⟩ : (g : ℤ) ∣ p := Int.gcd_dvd_left p r
  obtain ⟨z, hz⟩ : (g : ℤ) ∣ r := Int.gcd_dvd_right p r
  set u := Int.gcdA p r
  set v := Int.gcdB p r
  have hbez : (g : ℤ) = p * u + r * v := Int.gcd_eq_gcd_ab p r
  have h1 : x * u + z * v = 1 := by
    have : (g : ℤ) * (x * u + z * v) = g * 1 := by
      rw [mul_one]; conv_rhs => rw [hbez, hx, hz]
      ring
    exact mul_left_cancel₀ hgZ.ne' this
  set E : ℤ := x * s - z * q with hE
  have hgE : (g : ℤ) * E = m := by rw [← h, hx, hz, hE]; ring
  have hE0 : 0 < E := by
    by_contra hc
    have : (g : ℤ) * E ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hgZ.le (not_lt.mp hc)
    omega
  set b0 : ℤ := u * q + v * s with hb0
  have hmod0 : 0 ≤ b0 % E := Int.emod_nonneg _ hE0.ne'
  have hmod1 : b0 % E < E := Int.emod_lt_of_pos _ hE0
  have hdiv : b0 % E + E * (b0 / E) = b0 := Int.emod_add_mul_ediv b0 E
  set k := b0 / E
  set B := b0 % E
  have hEn : ((E.toNat : ℕ) : ℤ) = E := Int.toNat_of_nonneg hE0.le
  have hBn : ((B.toNat : ℕ) : ℤ) = B := Int.toNat_of_nonneg hmod0
  refine ⟨x, x * k - v, z, z * k + u, g, B.toNat, E.toNat, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination h1
  · have : ((g * E.toNat : ℕ) : ℤ) = m := by push_cast; rw [hEn]; exact hgE
    exact_mod_cast this
  · omega
  · rw [hx]; ring
  · rw [hEn, hBn]
    have : x * B + (x * k - v) * E = x * b0 - v * E := by rw [← hdiv]; ring
    rw [this, hb0, hE]
    linear_combination (-q) * h1
  · rw [hz]; ring
  · rw [hEn, hBn]
    have : z * B + (z * k + u) * E = z * b0 + u * E := by rw [← hdiv]; ring
    rw [this, hb0, hE]
    linear_combination (-s) * h1

theorem hnf_exists {m : ℕ} (hm : 0 < m) (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det = m) :
    ∃ (γ : SL(2, ℤ)) (t : ℕ × ℕ × ℕ), t ∈ Tm m ∧ M = (γ : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t := by
  rw [Matrix.det_fin_two] at hM
  obtain ⟨x, y, z, w, a, b, e, hdet, hae, hbe, h00, h01, h10, h11⟩ :=
    exists_hermite_normal_form_coords hm (M 0 0) (M 0 1) (M 1 0) (M 1 1) hM
  refine ⟨⟨!![x, y; z, w], by rw [Matrix.det_fin_two_of]; exact hdet⟩, (a, b, e),
    (mem_Tm hm _).2 ⟨hae, hbe⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Tmat, Matrix.mul_apply, Fin.sum_univ_two, h00, h01, h10, h11]

theorem hnf_unique {m : ℕ} (hm : 0 < m) {t t' : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) (ht' : t' ∈ Tm m)
    (γ : SL(2, ℤ)) (h : Tmat t = (γ : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t') : t = t' := by
  obtain ⟨a, b, e⟩ := t
  obtain ⟨a', b', e'⟩ := t'
  obtain ⟨hae, hbe⟩ := (mem_Tm hm _).1 ht
  obtain ⟨hae', hbe'⟩ := (mem_Tm hm _).1 ht'
  obtain ⟨ha, he⟩ := Tm_pos hm ht
  obtain ⟨ha', he'⟩ := Tm_pos hm ht'
  simp only at hae hbe hae' hbe' ha he ha' he'
  have hdet : γ.1 0 0 * γ.1 1 1 - γ.1 0 1 * γ.1 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact γ.2
  have h00 : (a : ℤ) = γ.1 0 0 * a' := by
    have := congrFun (congrFun h 0) 0
    simpa [Tmat, Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : (b : ℤ) = γ.1 0 0 * b' + γ.1 0 1 * e' := by
    have := congrFun (congrFun h 0) 1
    simpa [Tmat, Matrix.mul_apply, Fin.sum_univ_two] using this
  have h10 : (0 : ℤ) = γ.1 1 0 * a' := by
    have := congrFun (congrFun h 1) 0
    simpa [Tmat, Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : (e : ℤ) = γ.1 1 0 * b' + γ.1 1 1 * e' := by
    have := congrFun (congrFun h 1) 1
    simpa [Tmat, Matrix.mul_apply, Fin.sum_univ_two] using this
  generalize γ.1 0 0 = x at *
  generalize γ.1 0 1 = y at *
  generalize γ.1 1 0 = z at *
  generalize γ.1 1 1 = w at *
  have haZ : (0 : ℤ) < a := by exact_mod_cast ha
  have haZ' : (0 : ℤ) < a' := by exact_mod_cast ha'
  have heZ' : (0 : ℤ) < e' := by exact_mod_cast he'
  have hz : z = 0 := by
    rcases mul_eq_zero.1 h10.symm with h0 | h0
    · exact h0
    · omega
  subst hz
  have hxw : x * w = 1 := by linear_combination hdet
  have hx0 : 0 < x := by
    by_contra hc
    have : x * a' ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hc) haZ'.le
    omega
  have hx : x = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hxw with h0 | h0
    · exact h0
    · omega
  subst hx
  have hw : w = 1 := by linear_combination hxw
  subst hw
  have e1 : a = a' := by omega
  have e2 : e = e' := by omega
  subst e1 e2
  have hy : y = 0 := by
    have hbZ : (b : ℤ) < e := by exact_mod_cast hbe
    have hbZ' : (b' : ℤ) < e := by exact_mod_cast hbe'
    by_contra hc
    rcases lt_or_gt_of_ne hc with h0 | h0
    · have : y * e ≤ -1 * e := mul_le_mul_of_nonneg_right (by omega) heZ'.le
      omega
    · have : 1 * (e : ℤ) ≤ y * e := mul_le_mul_of_nonneg_right (by omega) heZ'.le
      omega
  subst hy
  have e3 : b = b' := by omega
  subst e3
  rfl

end ReciprocityTheory.ChartRestriction.L1
end
end
