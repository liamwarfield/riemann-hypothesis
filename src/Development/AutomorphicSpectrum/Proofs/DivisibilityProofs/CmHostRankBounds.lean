module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPositiveAdd
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Proportional
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerArithAgreement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerGeometricAgreement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreePolynomialEval
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormSubEqOne
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProportionalStatement

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBounds
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBounds
noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace GlobalTheory.CompanionTheory.Ar.Top.HostNumbers

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rt_sq (H : Host E) : (H.rt : E) ^ 2 = -(H.d : E) := by
  have h := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
  push_cast at h
  exact h

theorem seven_le_d (H : Host E) : 7 ≤ H.d := by
  have h := H.d_mod
  omega

private theorem two_mul_pow_self_le_succ_pow (m : ℕ) (hm : 1 ≤ m) : 2 * m ^ m ≤ (m + 1) ^ m := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hb : (1:ℝ) + m * (1 / m) ≤ (1 + 1 / m) ^ m :=
    one_add_mul_le_pow (by have : (0:ℝ) ≤ 1 / m := by positivity
                           linarith) m
  have h1 : (1:ℝ) + m * (1 / m) = 2 := by field_simp; ring
  have hR : (2:ℝ) * (m:ℝ) ^ m ≤ ((m:ℝ) + 1) ^ m := by
    calc (2:ℝ) * (m:ℝ) ^ m = (1 + m * (1 / m)) * (m:ℝ) ^ m := by rw [h1]
      _ ≤ (1 + 1 / m) ^ m * (m:ℝ) ^ m := by gcongr
      _ = ((1 + 1 / m) * m) ^ m := by rw [mul_pow]
      _ = ((m:ℝ) + 1) ^ m := by congr 1; field_simp
  exact_mod_cast hR

private theorem two_pow_mul_factorial_le_two_mul_pow_self (m : ℕ) (hm : 1 ≤ m) : 2 ^ m * m.factorial ≤ 2 * m ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h1 := two_mul_pow_self_le_succ_pow k hk
    calc 2 ^ (k+1) * (k+1).factorial = 2 * (k+1) * (2 ^ k * k.factorial) := by
          rw [Nat.factorial_succ, pow_succ]; ring
      _ ≤ 2 * (k+1) * (2 * k ^ k) := Nat.mul_le_mul_left _ ih
      _ ≤ 2 * (k+1) * (k+1) ^ k := Nat.mul_le_mul_left _ h1
      _ = 2 * (k+1) ^ (k+1) := by ring

private theorem two_pow_mul_factorial_sq_le_pow_two_mul (m : ℕ) (hm : 2 ≤ m) :
    2 ^ m * m.factorial ^ 2 ≤ m ^ (2 * m) := by
  have h := two_pow_mul_factorial_le_two_mul_pow_self m (by omega)
  have hsq : (2 ^ m * m.factorial) ^ 2 ≤ (2 * m ^ m) ^ 2 := Nat.pow_le_pow_left h 2
  have h4' : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h4 : 4 * 2 ^ m ≤ 2 ^ m * 2 ^ m := Nat.mul_le_mul_right _ h4'
  have h5 : 4 * (2 ^ m * m.factorial ^ 2) ≤ 4 * m ^ (2 * m) := by
    calc 4 * (2 ^ m * m.factorial ^ 2) = (4 * 2 ^ m) * m.factorial ^ 2 := by ring
      _ ≤ (2 ^ m * 2 ^ m) * m.factorial ^ 2 := Nat.mul_le_mul_right _ h4
      _ = (2 ^ m * m.factorial) ^ 2 := by ring
      _ ≤ (2 * m ^ m) ^ 2 := hsq
      _ = 4 * m ^ (2 * m) := by ring
  exact Nat.le_of_mul_le_mul_left h5 (by norm_num)

theorem two_pow_le_host (H : Host E) : 2 ^ Module.finrank ℚ E ≤ (discr E).natAbs := by
  let F := maximalRealSubfield E
  have hdiff : differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
    letI := FractionRing.liftAlgebra (𝓞 F) (FractionRing (𝓞 E))
    haveI := H.unram
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    haveI := hP.isPrime
    have hdvd : P ∣ differentIdeal (𝓞 F) (𝓞 E) := Ideal.dvd_iff_le.mpr hle
    have hun : Algebra.IsUnramifiedAt (𝓞 F) P :=
      Algebra.FormallyUnramified.comp (𝓞 F) (𝓞 E) (Localization.AtPrime P)
    exact ((not_dvd_differentIdeal_iff (A := 𝓞 F) (P := P)).mpr hun) hdvd
  have h2 : Module.finrank F E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F E
  have htow : (discr E).natAbs = (discr F).natAbs ^ 2 := by
    rw [NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) E (𝓞 E),
      hdiff, ← Ideal.one_eq_top, map_one, one_mul, h2]
  have hfr : Module.finrank ℚ E = 2 * Module.finrank ℚ F := by
    rw [← Module.finrank_mul_finrank ℚ F E, h2, mul_comm]
  have hFpos : 0 < Module.finrank ℚ F := Module.finrank_pos
  rcases Nat.lt_or_ge (Module.finrank ℚ F) 2 with hm | hm
  · exfalso
    have hm1 : Module.finrank ℚ F = 1 := by omega
    have hE : 2 < |discr E| := NumberField.abs_discr_gt_two (by rw [hfr]; omega)
    have hinj : Function.Injective (Algebra.ofId ℚ F) := (Algebra.ofId ℚ F).toRingHom.injective
    have hsurj : Function.Surjective (Algebra.ofId ℚ F) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := (Algebra.ofId ℚ F).toLinearMap) (by rw [Module.finrank_self, hm1])).mp hinj
    have hF : discr F = 1 := by
      rw [← NumberField.discr_eq_discr_of_algEquiv ℚ (AlgEquiv.ofBijective (Algebra.ofId ℚ F) ⟨hinj, hsurj⟩),
        NumberField.discr_rat]
    rw [hF] at htow
    have h1 : (discr E).natAbs = 1 := by simpa using htow
    rw [Int.abs_eq_natAbs, h1] at hE
    norm_num at hE
  · have hF := NumberField.abs_discr_ge' F
    rw [NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, mul_zero, pow_zero, one_mul] at hF
    have key := two_pow_mul_factorial_sq_le_pow_two_mul _ hm
    have hR : (2:ℝ) ^ Module.finrank ℚ F ≤ (((discr F).natAbs : ℤ) : ℝ) := by
      rw [← Int.abs_eq_natAbs]
      refine le_trans ?_ hF
      rw [le_div_iff₀ (by positivity)]
      exact_mod_cast key
    have hN : 2 ^ Module.finrank ℚ F ≤ (discr F).natAbs := by exact_mod_cast hR
    rw [htow, hfr, pow_mul]
    calc (2 ^ 2) ^ Module.finrank ℚ F = (2 ^ Module.finrank ℚ F) ^ 2 := by
          rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (discr F).natAbs ^ 2 := Nat.pow_le_pow_left hN 2

theorem two_le_hostRd (H : Host E) : 2 ≤ hostRd E := by
  have h := two_pow_le_host H
  have hn : (Module.finrank ℚ E : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E)).ne'
  have h' : ((2:ℝ) ^ Module.finrank ℚ E) ≤ |((discr E : ℤ) : ℝ)| := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast h
  unfold hostRd
  calc (2:ℝ) = ((2:ℝ) ^ Module.finrank ℚ E) ^ (1 / (Module.finrank ℚ E : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_one_div_cancel hn, Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow (by positivity) h' (by positivity)

theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  have h := H.sqrt_neg_disc_sq
  rw [pow_two] at h
  have hd : (7:ℝ) ≤ H.d := by exact_mod_cast seven_le_d H
  have hre : H.rt0.re * H.rt0.re - H.rt0.im * H.rt0.im = -(H.d:ℝ) := by
    have h1 := congrArg Complex.re h
    simp only [Complex.mul_re, Complex.neg_re, Complex.natCast_re] at h1
    exact h1
  have him : H.rt0.re * H.rt0.im + H.rt0.im * H.rt0.re = 0 := by
    have h1 := congrArg Complex.im h
    simp only [Complex.mul_im, Complex.neg_im, Complex.natCast_im, neg_zero] at h1
    exact h1
  have h1 : H.rt0.re * H.rt0.im = 0 := by linear_combination (1/2 : ℝ) * him
  have h2 : H.rt0.re * H.rt0.re * (H.rt0.re * H.rt0.re + H.d) = 0 := by
    linear_combination (H.rt0.re * H.rt0.re) * hre + (H.rt0.re * H.rt0.im) * h1
  have h3 : H.rt0.re * H.rt0.re = 0 := by
    rcases mul_eq_zero.mp h2 with h4 | h4
    · exact h4
    · nlinarith [mul_self_nonneg H.rt0.re]
  have ha : H.rt0.re = 0 := mul_self_eq_zero.mp h3
  apply Complex.ext
  · simp only [Complex.conj_re, Complex.neg_re, ha, neg_zero]
  · simp only [Complex.conj_im, Complex.neg_im]

theorem rt0_ne_zero (H : Host E) : H.rt0 ≠ 0 := by
  intro h
  have h2 := H.sqrt_neg_disc_sq
  rw [h] at h2
  have h3 : (H.d : ℂ) = 0 := by linear_combination h2
  have h4 : H.d = 0 := by exact_mod_cast h3
  have := seven_le_d H
  omega

theorem emb_rt (H : Host E) (τ : E →+* ℂ) : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
  have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, rt_sq H, map_neg, map_natCast]
  have h2 := H.sqrt_neg_disc_sq
  have h3 : (τ (H.rt : E) - H.rt0) * (τ (H.rt : E) + H.rt0) = 0 := by
    linear_combination h1 - h2
  rcases mul_eq_zero.mp h3 with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

def conjEquiv (H : Host E) :
    {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} ≃ {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} where
  toFun τ := ⟨ComplexEmbedding.conjugate τ.1, by
    rw [ComplexEmbedding.conjugate_coe_eq, τ.2, rt0_conj_neg_ne_zero]
    intro h
    exact rt0_ne_zero H (self_eq_neg.1 h.symm)⟩
  invFun τ := ⟨ComplexEmbedding.conjugate τ.1, by
    rw [ComplexEmbedding.conjugate_coe_eq, (emb_rt H τ.1).resolve_left τ.2, map_neg, rt0_conj_neg_ne_zero, neg_neg]⟩
  left_inv τ := Subtype.ext (by simp)
  right_inv τ := Subtype.ext (by simp)

theorem two_mul_card_CMType (H : Host E) : 2 * Fintype.card (CMType H) = Module.finrank ℚ E := by
  classical
  have h1 : Nat.card (E →+* ℂ) = Nat.card {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} +
      Nat.card {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)).symm
  have h2 : Nat.card {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} =
      Nat.card {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} :=
    (Nat.card_congr (conjEquiv H)).symm
  have h3 : Nat.card (E →+* ℂ) = Module.finrank ℚ E := by
    rw [Nat.card_eq_fintype_card]
    exact NumberField.Embeddings.card E ℂ
  have h4 : Fintype.card (CMType H) = Nat.card {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} := by
    rw [← Nat.card_eq_fintype_card]
  omega

theorem host_numbers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), 2 ≤ hostRd E ∧ Nonempty (CMType H) ∧ 2 * Fintype.card (CMType H) = Module.finrank ℚ E := by
  intro E _ _ _ H
  refine ⟨two_le_hostRd H, ?_, two_mul_card_CMType H⟩
  rw [← Fintype.card_pos_iff]
  have h1 := two_mul_card_CMType H
  have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
  omega

end GlobalTheory.CompanionTheory.Ar.Top.HostNumbers
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBoundsStatement
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_host_rank_bounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), 2 ≤ hostRd E ∧ Nonempty (CMType H) ∧ 2 * Fintype.card (CMType H) = Module.finrank ℚ E := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers | exact GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.EvalRhoAntisymDeltaNe
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem eval_formPoly_none_zero {σ : Type} [Fintype σ] (n : ℕ) (a : (Fin n → Option σ) → ℝ) (c : σ → ℝ) :
    eval (fun o : Option σ => o.elim 0 c) (PB.formPoly n a) =
      eval c (PB.formPoly n fun w => a fun j => some (w j)) := by
  have h : ∀ Q : MvPolynomial (Option σ) ℝ,
      eval c (aeval (fun o : Option σ => o.elim (0 : MvPolynomial σ ℝ) X) Q) =
        eval (fun o : Option σ => o.elim 0 c) Q := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C r => simp
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p o hp =>
      rw [map_mul, map_mul, map_mul, hp]
      cases o <;> simp
  rw [← h, PB.killNone_formPoly]

theorem linA_zero_pow {Ψ : Type} [Fintype Ψ] {N : ℕ} (lam : Wt Ψ N) (k : ℕ) :
    linA lam 0 ^ k = toA (linRoot lam ^ k) := by
  simp [linA, toA, map_pow]

theorem swapWt_uncurry {Ψ : Type} [DecidableEq Ψ] {N : ℕ} (τ : Ψ) (a b : Fin N) (lam : Wt Ψ N) :
    (fun x : Ψ × Fin N => swapWt τ a b lam x.1 x.2) =
      (fun x : Ψ × Fin N => lam x.1 x.2) ∘ Equiv.swap (τ, a) (τ, b) := by
  funext ⟨σ, i⟩
  by_cases hσ : σ = τ
  · subst hσ
    by_cases h1 : i = a
    · subst h1; simp [swapWt]
    · by_cases h2 : i = b
      · subst h2; simp [swapWt]
      · simp [swapWt, Equiv.swap_apply_def, h1, h2]
  · simp [swapWt, Equiv.swap_apply_def, hσ]

theorem eval_rho_antisymDelta_ne {Ψ : Type} [Fintype Ψ] {N : ℕ} :
    eval (fun x : Ψ × Fin N => (rhoWt : Wt Ψ N) x.1 x.2) (GroundTheory.Heights₂.Heights.antisymDelta Ψ N) ≠ 0 := by
  simp only [GroundTheory.Heights₂.Heights.antisymDelta, map_prod, map_sub, eval_X]
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun a _ =>
    Finset.prod_ne_zero_iff.2 fun b hb => ?_
  have hab : a < b := Finset.mem_Ioi.1 hb
  have hab' : (a : ℕ) < b := hab
  have : ((a : ℕ) : ℝ) < b := by exact_mod_cast hab'
  simp only [rhoWt]
  intro h
  linarith

end GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem Realis_PB_gapS_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {D : ℕ} {σ : Type} [Fintype σ]
    {S : PB.AnSys D (Option σ)} {P : Ideal (MRing ι)} (Re : PB.Realis S P) (II : IntersectionSystem) (c : σ → ℝ) :
    eval (fun o : Option σ => o.elim 0 c) (Re.PB II) = eval c ((Re.comap some).PB II) :=
  eval_formPoly_none_zero _ _ c

theorem AnSys_degPoly_gapS_zero {D : ℕ} {σ : Type} [Fintype σ] (S : PB.AnSys D (Option σ)) (c : σ → ℝ) :
    eval (fun o : Option σ => o.elim 0 c) S.degPoly = eval c (S.comap some).degPoly :=
  eval_formPoly_none_zero _ _ c

end GlobalTheory.CompanionTheory.Ar.Top
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumLogPrimeDivPredLeLog
section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.SumLogPrimeRatioLe
open Finset

namespace LevelTowerAlt

theorem log_div_pred_le (p B : ℕ) (hB : 2 ≤ B) (h : B < p) :
    Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ 3 * Real.log B / B := by
  have hB2 : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hBp : (B : ℝ) + 1 ≤ p := by exact_mod_cast h
  have hB0 : (0 : ℝ) < B := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hlogB : 0.6931471803 < Real.log B :=
    Real.log_two_gt_d9.trans_le (Real.log_le_log (by norm_num) hB2)
  have hratio : Real.log ((p : ℝ) / B) ≤ (p : ℝ) / B - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hp0 hB0)
  rw [Real.log_div hp0.ne' hB0.ne'] at hratio
  have key : Real.log p * B ≤ B * Real.log B + ((p : ℝ) - B) := by
    have h1 := mul_le_mul_of_nonneg_right hratio hB0.le
    rw [sub_mul, sub_mul, div_mul_cancel₀ _ hB0.ne', one_mul] at h1
    linarith
  rw [div_le_div_iff₀ hp1 hB0]
  have h3 : 0 ≤ 3 * ((p : ℝ) - 1) - B := by linarith
  have h4 := mul_le_mul_of_nonneg_right hlogB.le h3
  nlinarith

theorem sum_log_prime_ratio_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (S S₀ : Finset ℕ) (B : ℕ), 2 ≤ B → (∀ p ∈ S, p.Prime ∧ (p ≤ B ∨ p ∈ S₀)) → S₀.card ≤ B → ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ C * Real.log B := by
  refine ⟨8, by norm_num, fun S S₀ B hB hS hcard => ?_⟩
  have hB2 : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := by linarith
  have hBne : (B : ℝ) ≠ 0 := hB0.ne'
  have hlogB : 0.6931471803 < Real.log B :=
    Real.log_two_gt_d9.trans_le (Real.log_le_log (by norm_num) hB2)
  rw [← Finset.sum_filter_add_sum_filter_not S (fun p => p ≤ B)]
  have hsmall : ∑ p ∈ S with p ≤ B, Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ Real.log B + 2.2 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
      (GlobalTheory.PrimeLogSum.sum_log_div_pred_le B)
    · intro p hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hp.2), (hS p hp.1).1⟩
    · intro p hp _
      have hpr := (Finset.mem_filter.1 hp).2
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hpr.two_le
      exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
  have hlarge : ∑ p ∈ S with ¬ p ≤ B, Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ 3 * Real.log B := by
    have hsub : S.filter (fun p => ¬ p ≤ B) ⊆ S₀ := by
      intro p hp
      rw [Finset.mem_filter] at hp
      exact (hS p hp.1).2.resolve_left hp.2
    have hc : ((S.filter (fun p => ¬ p ≤ B)).card : ℝ) ≤ B := by
      exact_mod_cast (Finset.card_le_card hsub).trans hcard
    refine (Finset.sum_le_card_nsmul _ _ (3 * Real.log B / B) ?_).trans ?_
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact LevelTowerAlt.log_div_pred_le p B hB (not_le.1 hp.2)
    · rw [nsmul_eq_mul]
      calc _ ≤ (B : ℝ) * (3 * Real.log B / B) :=
            mul_le_mul_of_nonneg_right hc (div_nonneg (by linarith) hB0.le)
        _ = 3 * Real.log B := by field_simp
  linarith

end LevelTowerAlt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumLogPrimeDivPredLeLog
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.sum_log_prime_div_pred_le_log : ∃ C : ℝ, 0 ≤ C ∧ ∀ (S S₀ : Finset ℕ) (B : ℕ), 2 ≤ B → (∀ p ∈ S, p.Prime ∧ (p ≤ B ∨ p ∈ S₀)) → S₀.card ≤ B → ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ C * Real.log B := by
  first | exact @LevelTowerAlt.sum_log_prime_ratio_le | exact LevelTowerAlt.sum_log_prime_ratio_le
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumLogPrimeDivPredLeLogStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_log_prime_div_pred_le_log : ∃ C : ℝ, 0 ≤ C ∧ ∀ (S S₀ : Finset ℕ) (B : ℕ), 2 ≤ B → (∀ p ∈ S, p.Prime ∧ (p ≤ B ∨ p ∈ S₀)) → S₀.card ≤ B → ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ C * Real.log B := by
  first | exact @GlobalTheory.CompanionTheory.Relay.sum_log_prime_div_pred_le_log | exact GlobalTheory.CompanionTheory.Relay.sum_log_prime_div_pred_le_log | (intros; apply GlobalTheory.CompanionTheory.Relay.sum_log_prime_div_pred_le_log <;> assumption)
end
end
