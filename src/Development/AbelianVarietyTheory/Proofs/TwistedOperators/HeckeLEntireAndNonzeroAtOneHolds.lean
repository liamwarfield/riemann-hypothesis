module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExtensionEmbeddingMixedSymmOfIsComplex
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdealCharacterOfUnitaryHeckeChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOneOfInfOfVal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaEulerProductNeZeroOneAddMulI
open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff

namespace GlobalTheory

theorem conj_apply_conj_of_entire (Z : ℂ → ℂ) (hZ : Differentiable ℂ Z)
    (h : ∀ s : ℂ, 1 < s.re → starRingEnd ℂ (Z (starRingEnd ℂ s)) = Z s) (s : ℂ) :
    starRingEnd ℂ (Z (starRingEnd ℂ s)) = Z s := by
  have hZ' : Differentiable ℂ (fun s => starRingEnd ℂ (Z (starRingEnd ℂ s))) := by
    intro s
    have := (hZ (starRingEnd ℂ s)).conj_conj
    rw [Complex.conj_conj] at this
    exact this
  have hev : (fun s => starRingEnd ℂ (Z (starRingEnd ℂ s))) =ᶠ[nhds (2 : ℂ)] Z := by
    have ho : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by simp)] with s hs
    exact h s hs
  have := AnalyticOnNhd.eq_of_eventuallyEq
    (hZ'.differentiableOn.analyticOnNhd isOpen_univ)
    (hZ.differentiableOn.analyticOnNhd isOpen_univ) hev
  exact congrFun this s

theorem zetaEulerProduct_ne_zero_one_add_mul_I : ∀ (ι : Type) (N : ι → ℕ), (∀ i, 2 ≤ N i) → (∀ σ : ℝ, 1 < σ → Summable fun i => (N i : ℝ) ^ (-σ)) → Nonempty ι → ∀ Z : ℂ → ℂ, Differentiable ℂ Z → (∀ s : ℂ, 1 < s.re → Z s = (s - 1) * Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-s)))) → ∀ t : ℝ, t ≠ 0 → Z (1 + (t : ℂ) * Complex.I) ≠ 0 := by
  intro ι N hN hsum hne Z hZ hZs t ht ha
  obtain ⟨i₀⟩ := hne
  have hpos : ∀ i, 0 < N i := fun i => by have := hN i; omega
  have hN0 : ∀ i, ((N i : ℕ) : ℂ) ≠ 0 := fun i => by exact_mod_cast (hpos i).ne'
  have hconj : ∀ s, starRingEnd ℂ (Z (starRingEnd ℂ s)) = Z s := by
    refine conj_apply_conj_of_entire Z hZ fun s hs => ?_
    have hs' : 1 < (starRingEnd ℂ s).re := by simpa using hs
    rw [hZs _ hs', hZs s hs, map_mul, map_sub, Complex.conj_conj, map_one, ← Complex.exp_conj,
      Complex.conj_tsum]
    simp only [conj_neg_log_euler_factor _ (hN _) 1 (by simp) s hs, map_one]
  set u : ℂ := (t : ℂ) * Complex.I with hu
  have hu0 : u ≠ 0 := mul_ne_zero (by exact_mod_cast ht) Complex.I_ne_zero
  have hure : u.re = 0 := by simp [hu]
  have huc : starRingEnd ℂ u = -u := by simp [hu]
  have hb : Z (1 - u) = 0 := by
    rw [← hconj, map_sub, map_one, huc, sub_neg_eq_add, ha, map_zero]
  have hds : ∀ (f : ℂ → ℂ) (a : ℂ), Differentiable ℂ f → Differentiable ℂ (dslope f a) := by
    intro f a hf
    rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]
    exact hf.differentiableOn
  have hmul : ∀ (f : ℂ → ℂ) (a : ℂ), f a = 0 → ∀ s, (s - a) * dslope f a s = f s := by
    intro f a h0 s
    have := sub_smul_dslope f a s
    rw [smul_eq_mul, h0, sub_zero] at this
    exact this
  have hD1 := hds Z (1 + u) hZ
  have hD2 := hds Z (1 - u) hZ
  have hG := hds _ (1 - u) hD1
  have hD1b : dslope Z (1 + u) (1 - u) = 0 := by
    have := hmul Z (1 + u) ha (1 - u)
    rw [hb, mul_eq_zero] at this
    refine this.resolve_left fun h => hu0 ?_
    linear_combination (-1 / 2 : ℂ) * h
  set c : ι → ℂ := fun i => ((N i : ℕ) : ℂ) ^ (-u) with hcdef
  have hc : ∀ i, ‖c i‖ ≤ 1 := fun i => by
    simp only [hcdef]
    rw [Complex.norm_natCast_cpow_of_pos (hpos i), Complex.neg_re, hure]
    simp
  have hcc : ∀ i, starRingEnd ℂ (c i) = ((N i : ℕ) : ℂ) ^ u := fun i => by
    have harg' : ((N i : ℕ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
    have := Complex.cpow_conj ((N i : ℕ) : ℂ) (-u) harg'
    rw [map_neg, huc, neg_neg, map_natCast] at this
    exact this.symm
  have key := GlobalTheory.landau_exp_summable (ι × ℕ)
    (fun p => (2 + 2 * (c p.1 ^ (p.2 + 1)).re) / ((p.2 : ℝ) + 1))
    (fun p => ((p.2 : ℝ) + 1) * Real.log (N p.1))
    (fun s => Z s * dslope (dslope Z (1 + u)) (1 - u) s * dslope Z (1 + u) (s + u) *
      dslope Z (1 - u) (s - u))
    (fun p => by
      have hw : ‖c p.1 ^ (p.2 + 1)‖ ≤ 1 := by
        rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hc _)
      have h1 := Complex.abs_re_le_norm (c p.1 ^ (p.2 + 1))
      have h2 := neg_abs_le (c p.1 ^ (p.2 + 1)).re
      apply div_nonneg (by linarith) (by positivity))
    (fun p => mul_nonneg (by positivity) (Real.log_natCast_nonneg _))
    (((hZ.mul hG).mul (hD1.comp (differentiable_id.add_const u))).mul
      (hD2.comp (differentiable_id.sub_const u)))
    (fun s hs => by
      refine ⟨_, GlobalTheory.LogEulerSeries.hasSum_log_zeta_sq_mul ι N c hN hc hsum s hs, ?_⟩
      have e1 : ∀ i, c i * ((N i : ℕ) : ℂ) ^ (-s) = 1 * ((N i : ℕ) : ℂ) ^ (-(s + u)) := by
        intro i
        simp only [hcdef]
        rw [one_mul, ← Complex.cpow_add _ _ (hN0 i)]
        congr 1; ring
      have e2 : ∀ i, starRingEnd ℂ (c i) * ((N i : ℕ) : ℂ) ^ (-s) =
          1 * ((N i : ℕ) : ℂ) ^ (-(s - u)) := by
        intro i
        rw [hcc, one_mul, ← Complex.cpow_add _ _ (hN0 i)]
        congr 1; ring
      simp only [e1, e2]
      rw [Complex.exp_add, Complex.exp_add, two_mul, Complex.exp_add]
      have h0 := hZs s hs
      have h1 := hZs (s + u) (by simpa [hure] using hs)
      have h2 := hZs (s - u) (by simpa [hure] using hs)
      have g0 := hmul Z (1 + u) ha s
      have g0' := hmul _ (1 - u) hD1b s
      have g1 := hmul Z (1 + u) ha (s + u)
      have g2 := hmul Z (1 - u) hb (s - u)
      have n1 : s - 1 ≠ 0 := fun h => by
        have := congrArg Complex.re h
        simp at this; linarith
      have n2 : s - (1 + u) ≠ 0 := fun h => by
        have := congrArg Complex.re h
        simp [hure] at this; linarith
      have n3 : s - (1 - u) ≠ 0 := fun h => by
        have := congrArg Complex.re h
        simp [hure] at this; linarith
      generalize Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-s))) = E at *
      generalize Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-(s + u)))) = E1 at *
      generalize Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-(s - u)))) = E2 at *
      generalize dslope (dslope Z (1 + u)) (1 - u) s = G at *
      generalize dslope Z (1 + u) (s + u) = A at *
      generalize dslope Z (1 - u) (s - u) = B at *
      have k0 : (s - (1 + u)) * (s - (1 - u)) * G = (s - 1) * E := by
        rw [← h0, ← g0, ← g0']; ring
      have k1 : (s - 1) * A = (s - (1 - u)) * E1 := by
        linear_combination g1 + h1
      have k2 : (s - 1) * B = (s - (1 + u)) * E2 := by
        linear_combination g2 + h2
      apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero n1 n2) n3)
      rw [h0]
      calc (s - 1) * (s - (1 + u)) * (s - (1 - u)) * ((s - 1) * E * G * A * B)
          = E * ((s - (1 + u)) * (s - (1 - u)) * G) * ((s - 1) * A) * ((s - 1) * B) := by ring
        _ = _ := by rw [k0, k1, k2]; ring)
  exact not_summable_two_add_two_re_pow_div (c i₀) (hc i₀) (key.prod_factor i₀)

end GlobalTheory
end

open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open Formalism.L2.Host (HChar)

namespace GlobalTheory.HeckeOne
open GlobalTheory.CMVal (eulerFactor IsHeckeL)
variable {K : Type} [Field K] [NumberField K]

theorem two_le_N (P : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm P.asIdeal :=
  NumberField.HeightOneSpectrum.one_lt_absNorm P

theorem sumN (σ : ℝ) (hσ : 1 < σ) : Summable fun P : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm P.asIdeal : ℝ) ^ (-σ) :=
  ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow K).2 σ hσ).2

theorem nonemptyN : Nonempty (HeightOneSpectrum (𝓞 K)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 K)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩⟩

noncomputable def cf (χ : HChar K) (P : HeightOneSpectrum (𝓞 K)) : ℂ := if χ.UnrAt P then ((χ.val P : ℂˣ) : ℂ) else 0

theorem norm_cf {χ : HChar K} (h : χ.IsUnitary) (P : HeightOneSpectrum (𝓞 K)) : ‖cf χ P‖ ≤ 1 := by
  unfold cf; split_ifs
  · exact (h _).le
  · simp

theorem hasProd_exp {χ : HChar K} (h : χ.IsUnitary) {s : ℂ} (hs : 1 < s.re) : HasProd (eulerFactor χ s)
    (Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - cf χ P * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s)))) := by
  refine (((GlobalTheory.eulerProduct_eq_exp_and_pos _ (fun P : HeightOneSpectrum (𝓞 K) => Ideal.absNorm P.asIdeal) (cf χ) two_le_N
    (norm_cf h) sumN).1 s hs).2).congr_fun fun P => ?_
  unfold eulerFactor cf; split_ifs <;> simp

theorem eulerFactor_mul_normChar (χ : HChar K) (t : ℝ) (s : ℂ) :
    eulerFactor (χ * normChar K t) s = eulerFactor χ (s + (t : ℂ) * Complex.I) := by
  funext v
  have hiff : (χ * normChar K t).UnrAt v ↔ χ.UnrAt v :=
    ⟨fun h => by simpa using h.mul (unrAt_normChar t v).inv, fun h => h.mul (unrAt_normChar t v)⟩
  have hN := two_le_N v
  unfold eulerFactor
  by_cases h : χ.UnrAt v
  · rw [if_pos h, if_pos (hiff.2 h), Formalism.L2.Host.HChar.val_mul, Units.val_mul, val_normChar, mul_assoc,
      ← Complex.cpow_add _ _ (by exact_mod_cast (by omega : Ideal.absNorm v.asIdeal ≠ 0))]
    congr 4; ring
  · rw [if_neg h, if_neg (mt hiff.1 h)]

theorem entire_of_not_normPow {χ : HChar K} (hu : χ.IsUnitary) (hχ : ¬ ∃ t : ℝ, IsNormPow χ t) :
    ∃ Λ : ℂ → ℂ, IsHeckeL χ Λ := by
  obtain ⟨t, φ, hφ1, hφ2, hφ3, hφ4, hφ5⟩ := GlobalTheory.HeckeOne.exists_normChar_smooth_homogeneous_inf K χ hu
  set χ₀ := χ * normChar K (-t) with hχ₀
  have he : χ = χ₀ * normChar K t := by
    rw [hχ₀, mul_assoc, ← normChar_add, neg_add_cancel, normChar_zero, mul_one]
  have hu₀ : χ₀.IsUnitary := hu.mul (isUnitary_normChar _)
  obtain ⟨m, X, hm, hX0, hX1, hXm, hXn, hXz, hXP, hXβ⟩ := GlobalTheory.T.exists_idealCharacter_of_unitary_heckeChar K χ₀ hu₀
  have hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = φ (mixedEmbedding K β) := fun β h0 h1 => by
    have h0' : (β : K) ≠ 0 := by exact_mod_cast h0
    rw [hXβ β (Units.mk0 _ h0') rfl h1, ← hφ5]; rfl
  have hJ : ∃ J, J ≠ ⊥ ∧ J ⊔ m = ⊤ ∧ X J ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hφ := GlobalTheory.eq_one_of_homogeneous_of_eq_one_on_class K m φ hm hφ3.continuousOn hφ2 (fun β h0 h1 => by
      rw [← hβ β h0 h1]
      refine hcon _ (by rwa [Ne, Ideal.span_singleton_eq_bot]) ?_
      rw [Ideal.eq_top_iff_one, show (1 : 𝓞 K) = β - (β - 1) by ring]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self β)) (Ideal.mem_sup_right h1))
    have h1 : χ₀ = 1 := GlobalTheory.HeckeUnrTrivial.eq_one_of_inf_of_val K χ₀ (fun k => by
      have := hφ (mixedEmbedding K (k : K)) (by
        rw [mixedEmbedding.norm_eq_norm]
        exact_mod_cast abs_ne_zero.2 (Algebra.norm_ne_zero_iff.2 k.ne_zero))
      rw [hφ5, inv_eq_one] at this
      exact Units.ext this) fun v hv => by
      have h2 := hXP v
      rw [if_pos hv] at h2
      refine Units.ext (h2.symm.trans (hcon _ v.ne_bot ?_))
      by_contra h3
      exact (χ₀.val v).ne_zero (h2.symm.trans (hXz _ h3))
    exact hχ ⟨t, (isNormPow_iff _ _).2 (by rw [he, h1, one_mul])⟩
  have hle : ∀ I, ‖X I‖ ≤ 1 := fun I => by
    by_cases hI : I = ⊥
    · simp [hI, hX0]
    by_cases hI' : I ⊔ m = ⊤
    · exact (hXn I hI hI').le
    · simp [hXz I hI']
  obtain ⟨Z, hZd, hZ, hZ1⟩ := GlobalTheory.idealCharacter_LSeries_continuation K m X φ hm hX0 hXm hXn hXz hφ1 hφ2 hφ3 hφ4 hβ
  have hd : Differentiable ℂ (dslope Z 1) := by
    rw [← differentiableOn_univ] at hZd ⊢
    exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr hZd
  refine ⟨fun s => dslope Z 1 (s + (t : ℂ) * Complex.I), hd.comp (by fun_prop), fun s hs => ?_⟩
  have hs' : 1 < (s + (t : ℂ) * Complex.I).re := by simpa using hs
  rw [he, eulerFactor_mul_normChar]
  convert hasProd_exp hu₀ hs' using 1
  have hs1 : s + (t : ℂ) * Complex.I ≠ 1 := fun h => by rw [h] at hs'; simp at hs'
  have hs2 := sub_ne_zero.mpr hs1
  beta_reduce
  rw [dslope_of_ne _ hs1, slope_def_field, hZ1 hJ, hZ _ hs',
    GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K X hX0 hX1 hXm hle _ hs', sub_zero, mul_div_cancel_left₀ _ hs2]
  simp only [hXP, cf]

theorem _root_.GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne_holds : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne := by
  intro K _ _ χ hu
  refine ⟨entire_of_not_normPow hu, fun h1 => ?_⟩
  obtain ⟨Z, hZd, hZ⟩ := GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire K
  by_cases hχ : ∃ t : ℝ, IsNormPow χ t
  · obtain ⟨t, ht⟩ := hχ
    rw [isNormPow_iff] at ht
    subst ht
    have ht0 : t ≠ 0 := fun h => h1 (h ▸ normChar_zero)
    have ht1 : (1 : ℂ) + (t : ℂ) * Complex.I - 1 ≠ 0 := by simpa using ht0
    refine ⟨fun s => Z (s + (t : ℂ) * Complex.I) / (s + (t : ℂ) * Complex.I - 1), ⟨?_, fun s hs => ?_⟩,
      div_ne_zero (GlobalTheory.zetaEulerProduct_ne_zero_one_add_mul_I _ _ two_le_N sumN nonemptyN Z hZd hZ t ht0) ht1⟩
    · exact ((hZd.comp (f := fun s : ℂ => s + (t : ℂ) * Complex.I) (by fun_prop)).analyticAt 1).div (by fun_prop) ht1
    · have hs' : 1 < (s + (t : ℂ) * Complex.I).re := by simpa using hs
      have hs1 : s + (t : ℂ) * Complex.I ≠ 1 := fun h => by rw [h] at hs'; simp at hs'
      rw [← one_mul (normChar K t), eulerFactor_mul_normChar]
      convert hasProd_exp (χ := 1) (fun _ => by simp) hs' using 1
      have hc : ∀ P : HeightOneSpectrum (𝓞 K), cf 1 P = 1 := fun P => if_pos fun _ _ => rfl
      simp only [hc]
      rw [hZ _ hs', mul_div_cancel_left₀ _ (sub_ne_zero.mpr hs1)]
  · obtain ⟨Λ, hΛ⟩ := entire_of_not_normPow hu hχ
    exact ⟨Λ, isContAtOne_of_isHeckeL hΛ, GlobalTheory.eulerProduct_ne_zero_one_of_entire _ _ (cf χ) two_le_N (norm_cf hu) sumN
      nonemptyN Z Λ hZd hΛ.1 hZ fun s hs => (hΛ.2 s hs).unique (hasProd_exp hu hs)⟩

end GlobalTheory.HeckeOne
