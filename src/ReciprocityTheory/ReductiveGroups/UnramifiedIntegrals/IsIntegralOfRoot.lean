module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGmQ
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgBasic

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.IsIntegralOfRoot
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem isIntegral_of_root {P : Polynomial ℂ} (hP : ∀ i, IsIntegral ℤ (P.coeff i))
    (hu : IsIntegral ℤ (P.leadingCoeff)⁻¹) (h0 : P.leadingCoeff ≠ 0) {x : ℂ} (hx : P.eval x = 0) :
    IsIntegral ℤ x := by
  have hmon : (Polynomial.C (P.leadingCoeff)⁻¹ * P).Monic :=
    Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ h0)
  have hdeg : (Polynomial.C (P.leadingCoeff)⁻¹ * P).natDegree ≠ 0 := by
    rw [Polynomial.natDegree_C_mul (inv_ne_zero h0)]
    intro hd
    rw [Polynomial.eq_C_of_natDegree_eq_zero hd, Polynomial.eval_C] at hx
    apply h0
    rw [Polynomial.leadingCoeff, hd]
    exact hx
  refine IsIntegral.of_aeval_monic_of_isIntegral_coeff hmon hdeg ?_ ?_
  · rw [Polynomial.eval_mul, hx, mul_zero]
    exact isIntegral_zero
  · intro i
    rw [Polynomial.coeff_C_mul]
    exact hu.mul (hP i)

theorem jT_isIntegral {m : ℕ} (hm : 0 < m) (hsq : ¬ IsSquare m) {τ : ℍ} (h : Gm m τ = 0) :
    IsIntegral ℤ (jT τ) := by
  obtain ⟨n0, u, hu1, hu2, hu3, hlow, hcoef⟩ := gmQ_low hm hsq
  have hmf : IsMF (12 * ((2 * (Tm m).card : ℕ) : ℤ)) (Gm m) :=
    (gmForm hm).congr_weight (by push_cast; ring)
  obtain ⟨P, hPR, -, hlead, hval⟩ := qPrin_low (Rm m) _ (Gm m) hmf (gmQ_coeffIn hm) n0 u hu3 hlow hcoef
  have h1 := hval τ
  rw [h] at h1
  have h2 : P.eval (jT τ) = 0 := by
    rcases mul_eq_zero.mp h1.symm with h3 | h3
    · exact absurd h3 (pow_ne_zero _ (DD_ne_zero τ))
    · exact h3
  exact isIntegral_of_root (fun i => Rm_isIntegral hm (hPR i)) (by rw [hlead]; exact Rm_isIntegral hm hu2)
    (by rw [hlead]; exact hu3) h2

theorem cm1 : JInvariantIntegrality := by
  intro d L hsf hd4 hL
  obtain ⟨c, τ, hτ⟩ := latTau L
  have hd : 0 < d := by omega
  obtain ⟨A, B, C, D, h1, h2, h3⟩ := cmPoint hd hL hτ (-1) 2
  rw [jInv_eq_jT hτ]
  refine jT_isIntegral hd ?_ (Gm_vanish hd τ A B C D (by linarith) ?_)
  · rintro ⟨r, hr⟩
    have : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
    rcases this with h | h | h | h <;> simp [hr, Nat.mul_mod, h] at hd4
  · rw [← h1, h2]; ring

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgMulN
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

theorem powerSeries_subst_subst_of_constantCoeff_zero {R : Type} [CommRing R] {α β : Type} (φ : PowerSeries R)
    {u : MvPowerSeries α R} (hu : MvPowerSeries.constantCoeff u = 0) {b : α → MvPowerSeries β R}
    (hb : MvPowerSeries.HasSubst b) : (φ.subst u).subst b = φ.subst (u.subst b) := by
  rw [PowerSeries.subst, PowerSeries.subst]
  first
  | exact MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.HasSubst.of_constantCoeff_zero (fun _ => hu)) hb φ
  | exact MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hu)) hb φ
  | exact MvPowerSeries.subst_comp_subst_apply
      ((PowerSeries.HasSubst.of_constantCoeff_zero hu).hasSubst) hb φ
  | exact MvPowerSeries.subst_comp_subst_apply
      ⟨fun _ => by rw [hu]; exact IsNilpotent.zero, by simp⟩ hb φ

theorem mulN_integral {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} (h : LawD lam Φ) (n : ℕ) :
    ∃ e : PowerSeries K, constantCoeff e = 0 ∧ IntegralPS e ∧ lam.subst e = C (n : K) * lam := by
  have hXs : lam.subst (X : PowerSeries K) = lam := by
    have ha1 : PowerSeries.HasSubst (X : PowerSeries K) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' PowerSeries.constantCoeff_X
    ext m
    rw [PowerSeries.coeff_subst' ha1]
    rw [finsum_eq_single _ m]
    · rw [PowerSeries.coeff_X_pow_self, smul_eq_mul, mul_one]
    · intro d hd
      rw [PowerSeries.coeff_X_pow, if_neg (Ne.symm hd), smul_zero]
  induction n with
  | zero =>
    refine ⟨0, map_zero _, by unfold IntegralPS; intro k; simp, ?_⟩
    ext k
    rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' (map_zero _)),
      Nat.cast_zero, map_zero, zero_mul, map_zero]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, h.lam0, zero_smul]
    · rw [zero_pow hd.ne', map_zero, smul_zero]
  | succ n ih =>
    obtain ⟨e, he0, he, hlog⟩ := ih
    have hP0 : ∀ s, MvPowerSeries.constantCoeff ((![e, X] : Fin 2 → PowerSeries K) s) = 0 := by
      intro s
      fin_cases s
      · exact he0
      · exact PowerSeries.constantCoeff_X
    have hPint : ∀ s, IntegralMv ((![e, X] : Fin 2 → PowerSeries K) s) := by
      intro s
      fin_cases s
      · exact (integralPS_iff_mv e).mp he
      · exact (integralPS_iff_mv _).mp integralPS_X
    have ha : MvPowerSeries.HasSubst (![e, X] : Fin 2 → PowerSeries K) :=
      ⟨fun s => by rw [hP0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
    refine ⟨Φ.subst (![e, X] : Fin 2 → PowerSeries K), ?_, ?_, ?_⟩
    · have h0 : MvPowerSeries.constantCoeff (Φ.subst (![e, X] : Fin 2 → PowerSeries K)) = 0 := by
        rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_subst ha]
        apply finsum_eq_zero_of_forall_eq_zero
        intro d
        by_cases hd : d = 0
        · rw [hd, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.Φ0, zero_smul]
        · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
            by_contra hc
            push_neg at hc
            exact hd (Finsupp.ext hc)
          rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Finsupp.prod, map_prod,
            Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by rw [map_pow, hP0 s, zero_pow hs]),
            smul_zero]
      exact h0
    · exact (integralPS_iff_mv _).mpr (integralMv_subst2 h.Φint hP0 hPint)
    · rw [← powerSeries_subst_subst_of_constantCoeff_zero lam h.Φ0 ha, h.log]
      unfold atX atY
      first
      | rw [MvPowerSeries.subst_add ha]
      | rw [← MvPowerSeries.coe_substAlgHom ha, map_add (f := _), MvPowerSeries.coe_substAlgHom]
      rw [powerSeries_subst_subst_of_constantCoeff_zero lam (MvPowerSeries.constantCoeff_X 0) ha,
        powerSeries_subst_subst_of_constantCoeff_zero lam (MvPowerSeries.constantCoeff_X 1) ha,
        MvPowerSeries.subst_X ha, MvPowerSeries.subst_X ha]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [hlog, hXs, Nat.cast_succ, map_add (f := _), map_one]
      ring

end ReciprocityTheory.ChartRestriction.L1
end
end
