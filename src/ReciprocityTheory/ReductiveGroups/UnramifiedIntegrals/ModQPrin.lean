module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ExistsTeichmullerRepModPrime

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem IsMF.analytic {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) : AnalyticAt ℂ (cuspFunction 1 f) 0 := by
  obtain ⟨g, hg⟩ := hf
  have hfg : f = ⇑g := funext fun τ => (hg τ).symm
  subst hfg
  exact ModularFormClass.analyticAt_cuspFunction_zero g one_pos (by simp)

theorem qExp_AA_pow (n : ℕ) : qExpansion 1 (fun τ => AA τ ^ n) = aC ^ n := by
  induction n with
  | zero =>
    have : (fun τ => AA τ ^ 0) = (1 : ℍ → ℂ) := by funext τ; simp
    rw [this, qExpansion_one, pow_zero]
  | succ n ih =>
    have : (fun τ => AA τ ^ (n + 1)) = (fun τ => AA τ ^ n) * AA := by funext τ; simp [pow_succ]
    rw [this, qExpansion_mul (isMF_AA.pow n).analytic isMF_AA.analytic, ih, pow_succ, aC_eq]

theorem aC_coeff_zero : PowerSeries.coeff 0 aC = 1 := by
  have h4 : PowerSeries.coeff 0 e4Z = 1 := by rw [e4Z, PowerSeries.coeff_mk, if_pos rfl]
  rw [aC, aZ, PowerSeries.coeff_map]
  simp [pow_succ, PowerSeries.coeff_mul, h4]

theorem IsMF.div_DD {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f)
    (h0 : PowerSeries.coeff 0 (qExpansion 1 f) = 0) :
    ∃ h : ℍ → ℂ, IsMF (k - 12) h ∧ (∀ τ, f τ = DD τ * h τ) ∧
      qExpansion 1 f = dC * qExpansion 1 h := by
  obtain ⟨g, hg⟩ := hf
  obtain rfl : (⇑g : ℍ → ℂ) = f := funext hg
  refine ⟨CuspForm.discriminantEquiv (toCuspForm g h0), ⟨_, fun _ => rfl⟩, fun τ => ?_, ?_⟩
  · exact (discriminant_mul_discriminantEquiv_apply (toCuspForm g h0) τ).symm
  · rw [dC_eq]
    exact qExpansion_eq_qExpansion_discriminant_mul g h0

theorem coeff_mul_low (V G : PowerSeries ℂ) (hV : PowerSeries.coeff 0 V = 1) (n : ℕ)
    (hG : ∀ i < n, PowerSeries.coeff i G = 0) :
    (∀ i < n, PowerSeries.coeff i (V * G) = 0) ∧
      PowerSeries.coeff n (V * G) = PowerSeries.coeff n G := by
  constructor
  · intro i hi
    rw [PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [hG x.2 (by omega), mul_zero]
  · rw [PowerSeries.coeff_mul, Finset.sum_eq_single (0, n)]
    · rw [hV, one_mul]
    · intro x hx hne
      obtain ⟨a, b⟩ := x
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      have hb : b < n := by
        by_contra hb'
        apply hne
        have ha0 : a = 0 := by simp only at hx; omega
        have hbn : b = n := by simp only at hx; omega
        rw [ha0, hbn]
      rw [hG b hb, mul_zero]
    · intro h
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp)) h

theorem exists_dC_inv : ∃ v : PowerSeries ℤ, PowerSeries.coeff 0 v = 1 ∧
    ∀ H : PowerSeries ℂ, PowerSeries.X * H = v.map (Int.castRingHom ℂ) * (dC * H) := by
  set u : PowerSeries ℤ := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) dZ with hu
  have hd0 : PowerSeries.coeff 0 dZ = 0 := by
    rw [dZ, PowerSeries.coeff_mk]
    simp [e4Z, e6Z, pow_succ, PowerSeries.coeff_mul]
  have hd1 : PowerSeries.coeff 1 dZ = 1 := by
    rw [dZ, PowerSeries.coeff_mk]
    simp [e4Z, e6Z, pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ] <;> norm_num
  have hXu : dZ = PowerSeries.X * u := by
    ext n
    rcases n with _ | n
    · rw [hd0, PowerSeries.coeff_zero_X_mul]
    · rw [PowerSeries.coeff_succ_X_mul, hu, PowerSeries.coeff_mk]
  have hu0 : PowerSeries.constantCoeff u = ((1 : ℤˣ) : ℤ) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hu, PowerSeries.coeff_mk, zero_add, hd1, Units.val_one]
  refine ⟨PowerSeries.invOfUnit u 1, ?_, fun H => ?_⟩
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_invOfUnit, inv_one, Units.val_one]
  · have hinv := PowerSeries.mul_invOfUnit u 1 hu0
    have hdC : dC = PowerSeries.X * u.map (Int.castRingHom ℂ) := by
      rw [dC, hXu, map_mul, PowerSeries.map_X]
    rw [hdC]
    have h1 : (u.map (Int.castRingHom ℂ)) * (PowerSeries.invOfUnit u 1).map (Int.castRingHom ℂ) = 1 := by
      rw [← map_mul, hinv, map_one]
    linear_combination (-(PowerSeries.X * H)) * h1

theorem coeffIn_of_dC_mul (R : Subring ℂ) (H : PowerSeries ℂ) (h : CoeffIn R (dC * H)) : CoeffIn R H := by
  obtain ⟨v, -, hv⟩ := exists_dC_inv
  intro n
  rw [← PowerSeries.coeff_succ_X_mul, hv H, PowerSeries.coeff_mul]
  refine sum_mem fun x _ => mul_mem ?_ (h x.2)
  rw [PowerSeries.coeff_map, eq_intCast]
  exact intCast_mem _ _

theorem low_of_dC_mul (H : PowerSeries ℂ) (n0 : ℕ) (u : ℂ) (hu : u ≠ 0)
    (h0 : ∀ n < n0, PowerSeries.coeff n (dC * H) = 0) (h1 : PowerSeries.coeff n0 (dC * H) = u) :
    ∃ k, n0 = k + 1 ∧ (∀ n < k, PowerSeries.coeff n H = 0) ∧ PowerSeries.coeff k H = u := by
  obtain ⟨v, hv0, hv⟩ := exists_dC_inv
  have hV : PowerSeries.coeff 0 (v.map (Int.castRingHom ℂ)) = 1 := by
    rw [PowerSeries.coeff_map, hv0, map_one]
  obtain ⟨hlow, hn0⟩ := coeff_mul_low _ _ hV n0 h0
  rw [h1, ← hv H] at hn0
  rw [← hv H] at hlow
  rcases n0 with _ | k
  · rw [PowerSeries.coeff_zero_X_mul] at hn0
    exact absurd hn0.symm hu
  · refine ⟨k, rfl, fun n hn => ?_, ?_⟩
    · rw [← PowerSeries.coeff_succ_X_mul]
      exact hlow _ (by omega)
    · rw [← PowerSeries.coeff_succ_X_mul]
      exact hn0

theorem exists_integral_poly_of_qExpansion (R : Subring ℂ) (N : ℕ) : ∀ f : ℍ → ℂ, IsMF (12 * (N : ℤ)) f →
    CoeffIn R (qExpansion 1 f) →
    ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ R) ∧ P.natDegree ≤ N ∧
      (∀ τ, f τ = DD τ ^ N * P.eval (jT τ)) ∧
      ∀ (n0 : ℕ) (u : ℂ), u ≠ 0 → (∀ n < n0, PowerSeries.coeff n (qExpansion 1 f) = 0) →
        PowerSeries.coeff n0 (qExpansion 1 f) = u → P.leadingCoeff = u := by
  induction N with
  | zero =>
    intro f hf hR
    obtain ⟨g, hg⟩ := hf.congr_weight (k' := 0) (by simp)
    obtain ⟨c, hc⟩ := levelOne_weight_zero_const g
    have hfc : f = c • (1 : ℍ → ℂ) := by
      funext τ; rw [← hg τ, hc]; simp
    have hq : qExpansion 1 f = c • (1 : PowerSeries ℂ) := by
      have h1 : AnalyticAt ℂ (cuspFunction 1 (1 : ℍ → ℂ)) 0 := by
        have : IsMF 0 (1 : ℍ → ℂ) := ⟨1, fun τ => by simp⟩
        exact this.analytic
      rw [hfc, qExpansion_smul h1, qExpansion_one]
    refine ⟨Polynomial.C c, fun i => ?_, by simp, fun τ => ?_, fun n0 u hu h0 h1 => ?_⟩
    · have := hR 0
      rw [hq] at this
      rw [Polynomial.coeff_C]
      split_ifs
      · simpa using this
      · exact R.zero_mem
    · rw [hfc]; simp
    · rw [hq] at h1
      rw [Polynomial.leadingCoeff_C]
      cases n0 with
      | zero => simpa using h1
      | succ k =>
        exfalso; apply hu; rw [← h1]
        simp [PowerSeries.coeff_one]
  | succ N ih =>
    intro f hf hR
    set a0 : ℂ := PowerSeries.coeff 0 (qExpansion 1 f) with ha0
    have hA : IsMF (12 * ((N + 1 : ℕ) : ℤ)) (fun τ => AA τ ^ (N + 1)) :=
      (isMF_AA.pow (N + 1)).congr_weight (by ring)
    have hcA : IsMF (12 * ((N + 1 : ℕ) : ℤ)) (fun τ => a0 * AA τ ^ (N + 1)) := hA.const_mul a0
    have hg : IsMF (12 * ((N + 1 : ℕ) : ℤ)) (fun τ => f τ - a0 * AA τ ^ (N + 1)) := hf.sub hcA
    have hqg : qExpansion 1 (fun τ => f τ - a0 * AA τ ^ (N + 1)) =
        qExpansion 1 f - a0 • aC ^ (N + 1) := by
      have e1 : (fun τ => f τ - a0 * AA τ ^ (N + 1)) = f - a0 • (fun τ => AA τ ^ (N + 1)) := by
        funext τ; simp
      have e2 : (fun τ => a0 * AA τ ^ (N + 1)) = a0 • (fun τ => AA τ ^ (N + 1)) := by
        funext τ; simp
      rw [e1, qExpansion_sub hf.analytic (e2 ▸ hcA.analytic), qExpansion_smul hA.analytic,
        qExp_AA_pow]
    have haR : a0 ∈ R := hR 0
    have hac : ∀ n, PowerSeries.coeff n (aC ^ (N + 1)) ∈ R := by
      intro n
      have : aC ^ (N + 1) = (aZ ^ (N + 1)).map (Int.castRingHom ℂ) := by rw [map_pow]; rfl
      rw [this, PowerSeries.coeff_map]
      exact intCast_mem R _
    have hac0 : PowerSeries.coeff 0 (aC ^ (N + 1)) = 1 := by
      have := aC_coeff_zero
      simp only [PowerSeries.coeff_zero_eq_constantCoeff] at this ⊢
      rw [map_pow, this, one_pow]
    have hg0 : PowerSeries.coeff 0 (qExpansion 1 (fun τ => f τ - a0 * AA τ ^ (N + 1))) = 0 := by
      rw [hqg, map_sub, PowerSeries.coeff_smul, hac0]; simp [ha0]
    obtain ⟨h, hh, hfh, hqh⟩ := hg.div_DD hg0
    have hh' : IsMF (12 * (N : ℤ)) h := hh.congr_weight (by push_cast; ring)
    have hRh : CoeffIn R (qExpansion 1 h) := by
      apply coeffIn_of_dC_mul
      rw [← hqh, hqg]
      intro n
      rw [map_sub, PowerSeries.coeff_smul]
      exact R.sub_mem (hR n) (R.mul_mem haR (hac n))
    obtain ⟨P', hP1, hP2, hP3, hP4⟩ := ih h hh' hRh
    refine ⟨Polynomial.C a0 * Polynomial.X ^ (N + 1) + P', fun i => ?_, ?_, fun τ => ?_,
      fun n0 u hu h0 h1 => ?_⟩
    · rw [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
      refine R.add_mem ?_ (hP1 i)
      split_ifs
      · exact haR
      · exact R.zero_mem
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (by omega))
      exact Polynomial.natDegree_C_mul_X_pow_le _ _
    · have hD := DD_ne_zero τ
      have e := hfh τ
      rw [hP3 τ] at e
      have : f τ = a0 * AA τ ^ (N + 1) + DD τ * (DD τ ^ N * P'.eval (jT τ)) := by
        rw [← e]; ring
      rw [this]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X]
      have hj : DD τ ^ (N + 1) * jT τ ^ (N + 1) = AA τ ^ (N + 1) := by
        rw [← mul_pow, jT, mul_div_cancel₀ _ hD]
      rw [← hj]; ring
    · by_cases hz : a0 = 0
      · have hq' : qExpansion 1 f = dC * qExpansion 1 h := by
          rw [← hqh, hqg, hz]; simp
        rw [hq'] at h0 h1
        obtain ⟨k, -, hk0, hk1⟩ := low_of_dC_mul _ n0 u hu h0 h1
        rw [hz]; simp only [map_zero, zero_mul, zero_add]
        exact hP4 k u hu hk0 hk1
      · have hn0 : n0 = 0 := by
          by_contra hne
          exact hz (h0 0 (Nat.pos_of_ne_zero hne))
        subst hn0
        rw [Polynomial.leadingCoeff_add_of_degree_lt', Polynomial.leadingCoeff_mul_X_pow,
          Polynomial.leadingCoeff_C]
        · exact h1
        · rw [Polynomial.degree_C_mul_X_pow _ hz]
          refine lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hP2) ?_
          exact_mod_cast Nat.lt_succ_self N

theorem qPrin (R : Subring ℂ) (N : ℕ) (f : ℍ → ℂ) (hf : IsMF (12 * (N : ℤ)) f)
    (hR : CoeffIn R (qExpansion 1 f)) :
    ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ R) ∧ P.natDegree ≤ N ∧
      ∀ τ, f τ = DD τ ^ N * P.eval (jT τ) := by
  obtain ⟨P, h1, h2, h3, -⟩ := exists_integral_poly_of_qExpansion R N f hf hR
  exact ⟨P, h1, h2, h3⟩

theorem qPrin_low (R : Subring ℂ) (N : ℕ) (f : ℍ → ℂ) (hf : IsMF (12 * (N : ℤ)) f)
    (hR : CoeffIn R (qExpansion 1 f)) (n0 : ℕ) (u : ℂ) (hu : u ≠ 0)
    (h0 : ∀ n < n0, PowerSeries.coeff n (qExpansion 1 f) = 0)
    (h1 : PowerSeries.coeff n0 (qExpansion 1 f) = u) :
    ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ R) ∧ P.natDegree ≤ N ∧ P.leadingCoeff = u ∧
      ∀ τ, f τ = DD τ ^ N * P.eval (jT τ) := by
  obtain ⟨P, hc, hd, he, hl⟩ := exists_integral_poly_of_qExpansion R N f hf hR
  exact ⟨P, hc, hd, hl n0 u hu h0 h1, he⟩

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormLeOneOfIntegralInt
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1.KE

open Formalism.L2.Th1.CM

theorem norm_le_one_of_integral {K R : Type*} [NormedField K] [IsUltrametricDist K] [CommRing R]
    [Algebra R K] (hR : ∀ r : R, ‖algebraMap R K r‖ ≤ 1) (δ : K) (h : IsIntegral R δ) : ‖δ‖ ≤ 1 := by
  obtain ⟨p, hp, hpe⟩ := h
  by_contra hlt
  rw [not_le] at hlt
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one, one_mul] at hpe
  have h1 : δ ^ p.natDegree = - ∑ i ∈ Finset.range p.natDegree, algebraMap R K (p.coeff i) * δ ^ i :=
    eq_neg_of_add_eq_zero_right hpe
  have hpos : 0 < ‖δ‖ := lt_trans zero_lt_one hlt
  have h2 : ‖∑ i ∈ Finset.range p.natDegree, algebraMap R K (p.coeff i) * δ ^ i‖
      ≤ ‖δ‖ ^ p.natDegree / ‖δ‖ := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow, le_div_iff₀ hpos]
    have hi' : i + 1 ≤ p.natDegree := Finset.mem_range.mp hi
    calc ‖algebraMap R K (p.coeff i)‖ * ‖δ‖ ^ i * ‖δ‖ ≤ 1 * ‖δ‖ ^ i * ‖δ‖ := by
          gcongr; exact hR _
      _ = ‖δ‖ ^ (i + 1) := by rw [one_mul, pow_succ]
      _ ≤ ‖δ‖ ^ p.natDegree := pow_le_pow_right₀ hlt.le hi'
  have h3 : ‖δ‖ ^ p.natDegree / ‖δ‖ < ‖δ‖ ^ p.natDegree := div_lt_self (by positivity) hlt
  have h4 : ‖δ ^ p.natDegree‖ = ‖δ‖ ^ p.natDegree := norm_pow _ _
  rw [h1, norm_neg] at h4
  linarith

theorem norm_int_le_one {K : Type*} [NormedField K] [IsUltrametricDist K] (n : ℤ) :
    ‖algebraMap ℤ K n‖ ≤ 1 := by
  simpa using IsUltrametricDist.norm_intCast_le_one K n

theorem norm_le_one_of_integral_int {K : Type*} [NormedField K] [IsUltrametricDist K] (δ : K)
    (h : IsIntegral ℤ δ) : ‖δ‖ ≤ 1 :=
  norm_le_one_of_integral norm_int_le_one δ h

theorem norm_pow_sub_pow_le {K : Type*} [NormedField K] [IsUltrametricDist K] {x y : K}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (i : ℕ) : ‖x ^ i - y ^ i‖ ≤ ‖x - y‖ := by
  induction i with
  | zero => simp
  | succ i ih =>
    have : x ^ (i + 1) - y ^ (i + 1) = x * (x ^ i - y ^ i) + (x - y) * y ^ i := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖x‖ * ‖x ^ i - y ^ i‖ ≤ 1 * ‖x - y‖ := by gcongr
        _ = _ := one_mul _
    · rw [norm_mul, norm_pow]
      calc ‖x - y‖ * ‖y‖ ^ i ≤ ‖x - y‖ * 1 := by
            gcongr; exact pow_le_one₀ (norm_nonneg _) hy
        _ = _ := mul_one _

theorem norm_eval_sub_eval_le {K : Type*} [NormedField K] [IsUltrametricDist K] (P : Polynomial K)
    (hP : ∀ i, ‖P.coeff i‖ ≤ 1) {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖P.eval x - P.eval y‖ ≤ ‖x - y‖ := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
  rw [← mul_sub, norm_mul]
  calc ‖P.coeff i‖ * ‖x ^ i - y ^ i‖ ≤ 1 * ‖x - y‖ := by
        gcongr
        · exact hP i
        · exact norm_pow_sub_pow_le hx hy i
    _ = _ := one_mul _

theorem finite_domain_frob (R : Type*) [CommRing R] [IsDomain R] [Finite R] (l : ℕ) (hl : l.Prime)
    (h0 : (l : R) = 0) : ∃ f : ℕ, 0 < f ∧ ∀ x : R, x ^ (l ^ f) = x := by
  classical
  have hch : CharP R l := (CharP.charP_iff_prime_eq_zero hl).mpr h0
  let _ := Fintype.ofFinite R
  let _ : Field R := Fintype.fieldOfDomain R
  obtain ⟨n, -, hq⟩ := FiniteField.card R l
  exact ⟨n, n.pos, fun x => hq ▸ FiniteField.pow_card x⟩

theorem frob_fix_of_integral {K : Type*} [NormedField K] [IsUltrametricDist K] (l : ℕ)
    (hlp : l.Prime) (hl : ‖(l : K)‖ < 1) (δ : K) (hδ : IsIntegral ℤ δ) :
    ∃ f : ℕ, 0 < f ∧ ‖δ ^ (l ^ f) - δ‖ < 1 := by
  let A : Subalgebra ℤ K := Algebra.adjoin ℤ {δ}
  have hA : ∀ x : A, ‖(x : K)‖ ≤ 1 := fun x =>
    norm_le_one_of_integral norm_int_le_one _ (adjoin_le_integralClosure hδ x.2)
  let I : Ideal A :=
    { carrier := {x | ‖(x : K)‖ < 1}
      add_mem' := fun {a b} ha hb =>
        lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        change ‖((c * x : A) : K)‖ < 1
        rw [MulMemClass.coe_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hA c) (norm_nonneg _) hx }
  have hImem : ∀ x : A, x ∈ I ↔ ‖(x : K)‖ < 1 := fun x => Iff.rfl
  have hIprime : I.IsPrime := by
    refine ⟨?_, ?_⟩
    · intro h
      have h1 : (1 : A) ∈ I := h ▸ Submodule.mem_top
      rw [hImem] at h1
      simp at h1
    · intro x y hxy
      by_contra hcon
      rw [not_or, hImem, hImem, not_lt, not_lt] at hcon
      rw [hImem, MulMemClass.coe_mul, norm_mul] at hxy
      have := one_le_mul_of_one_le_of_one_le hcon.1 hcon.2
      linarith
  have : Module.Finite ℤ A := Algebra.finite_adjoin_simple_of_isIntegral hδ
  have hl0 : ((l : ℕ) : A ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I) l, Ideal.Quotient.eq_zero_iff_mem, hImem]
    have h2 : (((l : ℕ) : A) : K) = (l : K) := map_natCast A.val l
    rw [h2]
    exact hl
  have htors : Module.IsTorsion ℤ (A ⧸ I) := fun {x} =>
    ⟨⟨(l : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hlp.ne_zero)⟩, by
      change (l : ℤ) • x = 0
      rw [zsmul_eq_mul, Int.cast_natCast, hl0, zero_mul]⟩
  have : Finite (A ⧸ I) := Module.finite_of_fg_torsion _ htors
  obtain ⟨f, hf, h⟩ := finite_domain_frob (A ⧸ I) l hlp hl0
  refine ⟨f, hf, ?_⟩
  let d : A := ⟨δ, Algebra.self_mem_adjoin_singleton ℤ δ⟩
  have h3 := h (Ideal.Quotient.mk I d)
  rw [← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, hImem] at h3
  exact h3

variable (l : ℕ) [Fact l.Prime]

theorem rmu_isIntegral_int {x : ℂ_[l]} (hx : x ∈ Rmu l) : IsIntegral ℤ x := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨n, hn, -, h⟩ := hx
    exact IsIntegral.of_pow hn (h ▸ isIntegral_one)
  | zero => exact isIntegral_zero
  | one => exact isIntegral_one
  | add x y _ _ hx hy => exact hx.add hy
  | neg x _ hx => exact hx.neg
  | mul x y _ _ hx hy => exact hx.mul hy

theorem isIntegral_int_of_rmu (δ : ℂ_[l]) (hδ : IsIntegral (Rmu l) δ) :
    (Int.castRingHom ℂ_[l]).IsIntegralElem δ := by
  have : Algebra.IsIntegral ℤ (Rmu l) := ⟨fun x => by
    have := rmu_isIntegral_int l x.2
    exact (isIntegral_algebraMap_iff (A := Rmu l) (B := ℂ_[l]) ).mp this⟩
  have h : IsIntegral ℤ δ := isIntegral_trans δ hδ
  exact (Subsingleton.elim (algebraMap ℤ ℂ_[l]) (Int.castRingHom ℂ_[l])) ▸ h

theorem tch_mem_rmu {x : ℂ_[l]} (hx : x ∈ Tch l) : x ∈ Rmu l := by
  rcases hx with rfl | hx
  · exact (Rmu l).zero_mem
  · exact Subring.subset_closure hx

end ReciprocityTheory.ChartRestriction.L1.KE
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModVanish
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem fac_eq_zero_of_smul (t : ℕ × ℕ × ℕ) (τ : ℍ) (γ : SL(2, ℤ))
    (h : γ • pt t.1 t.2.1 t.2.2 τ = τ) : fac t τ = 0 := by
  unfold fac
  have h1 : AA τ = denom γ (pt t.1 t.2.1 t.2.2 τ) ^ 12 * AA (pt t.1 t.2.1 t.2.2 τ) := by
    rw [← AA_smul, h]
  have h2 : DD τ = denom γ (pt t.1 t.2.1 t.2.2 τ) ^ 12 * DD (pt t.1 t.2.1 t.2.2 τ) := by
    rw [← DD_smul, h]
  rw [h1, h2]
  ring

private lemma exists_SL2_mul_eq_Tmat_of_det_eq {m : ℕ} (hm : 0 < m) (A B C D : ℤ) (hdet : A * D - B * C = m) :
    ∃ g : SL(2, ℤ), ∃ s ∈ Tm m, 0 < s.2.2 ∧ (g : Matrix (Fin 2) (Fin 2) ℤ) * !![A, B; C, D] = Tmat s := by
  have hAC : A ≠ 0 ∨ C ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h0 : (m : ℤ) = 0 := by rw [← hdet, hc.1, hc.2]; ring
    omega
  obtain ⟨G, hG⟩ : ∃ G : ℕ, G = Int.gcd A C := ⟨_, rfl⟩
  have hGpos : 0 < G := by
    rw [hG]
    first
    | exact Int.gcd_pos_iff.mpr hAC
    | (rcases hAC with h | h
       · exact Int.gcd_pos_of_ne_zero_left C h
       · exact Int.gcd_pos_of_ne_zero_right A h)
  obtain ⟨a0, ha0⟩ : (G : ℤ) ∣ A := by
    rw [hG]
    first | exact Int.gcd_dvd_left | exact Int.gcd_dvd_left A C | exact Int.gcd_dvd_left _ _
  obtain ⟨c0, hc0⟩ : (G : ℤ) ∣ C := by
    rw [hG]
    first | exact Int.gcd_dvd_right | exact Int.gcd_dvd_right A C | exact Int.gcd_dvd_right _ _
  obtain ⟨x, y, hbez⟩ : ∃ x y : ℤ, (G : ℤ) = A * x + C * y :=
    ⟨_, _, by rw [hG]; exact Int.gcd_eq_gcd_ab A C⟩
  have hG0 : (G : ℤ) ≠ 0 := by exact_mod_cast hGpos.ne'
  have h1 : a0 * x + c0 * y = 1 := by
    apply mul_left_cancel₀ hG0
    linear_combination -hbez - x * ha0 - y * hc0
  obtain ⟨d, hd⟩ : ∃ d : ℤ, d = a0 * D - c0 * B := ⟨_, rfl⟩
  have hGd : (G : ℤ) * d = m := by
    rw [hd]
    linear_combination hdet - D * ha0 + B * hc0
  have hdpos : 0 < d := by
    have h2 : 0 < (G : ℤ) * d := by rw [hGd]; exact_mod_cast hm
    have h3 : (0 : ℤ) < G := by exact_mod_cast hGpos
    by_contra h4
    push_neg at h4
    nlinarith
  obtain ⟨q, b, hdiv, hb0, hbd⟩ : ∃ q b : ℤ, d * q + b = x * B + y * D ∧ 0 ≤ b ∧ b < d :=
    ⟨(x * B + y * D) / d, (x * B + y * D) % d,
      (by first
          | (have h5 := Int.emod_add_ediv (x * B + y * D) d; linarith)
          | (have h5 := Int.ediv_add_emod' (x * B + y * D) d; linarith)
          | (have h5 := Int.mul_ediv_add_emod (x * B + y * D) d; linarith)), Int.emod_nonneg _ hdpos.ne',
      Int.emod_lt_of_pos _ hdpos⟩
  have hdet1 : (x + q * c0) * a0 - (y - q * a0) * -c0 = 1 := by linear_combination h1
  have e1 : (x + q * c0) * A + (y - q * a0) * C = (G : ℤ) := by
    linear_combination -hbez + q * c0 * ha0 - q * a0 * hc0
  have e2 : (x + q * c0) * B + (y - q * a0) * D = b := by
    linear_combination -hdiv + q * hd
  have e3 : -c0 * A + a0 * C = 0 := by
    linear_combination -c0 * ha0 + a0 * hc0
  have e4 : -c0 * B + a0 * D = d := by
    linear_combination -hd
  lift d to ℕ using hdpos.le
  lift b to ℕ using hb0
  have hGdn : G * d = m := by exact_mod_cast hGd
  have hmd : m / G = d := by rw [← hGdn, Nat.mul_div_cancel_left _ hGpos]
  refine ⟨⟨!![x + q * c0, y - q * a0; -c0, a0], by rw [Matrix.det_fin_two_of]; exact hdet1⟩, (G, b, d), ?_, by show 0 < d; exact_mod_cast hdpos, ?_⟩
  · simp only [Tm, Finset.mem_image, Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range]
    refine ⟨⟨G, b⟩, ⟨⟨⟨d, hGdn.symm⟩, hm.ne'⟩, ?_⟩, ?_⟩
    · rw [hmd]; exact_mod_cast hbd
    · simp [hmd]
  · show !![x + q * c0, y - q * a0; -c0, a0] * !![A, B; C, D] = Tmat (G, b, d)
    rw [Matrix.mul_fin_two, e1, e2, e3, e4]
    all_goals first | rfl | (unfold Tmat; rfl) | simp [Tmat]

theorem Gm_vanish {m : ℕ} (hm : 0 < m) (τ : ℍ) (A B C D : ℤ) (hdet : A * D - B * C = m)
    (hfix : (A : ℂ) * τ + B = τ * (C * τ + D)) : Gm m τ = 0 := by
  obtain ⟨g, s, hs, he, hgs⟩ := exists_SL2_mul_eq_Tmat_of_det_eq hm A B C D hdet
  obtain ⟨p, q, r, w, hg⟩ : ∃ p q r w : ℤ, (g : Matrix (Fin 2) (Fin 2) ℤ) = !![p, q; r, w] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdg : p * w - q * r = 1 := by
    have h0 := Matrix.SpecialLinearGroup.det_coe g
    rw [hg, Matrix.det_fin_two_of] at h0
    exact h0
  have hp : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = p := by rw [hg]; rfl
  have hq : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = q := by rw [hg]; rfl
  have hr : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = r := by rw [hg]; rfl
  have hw : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = w := by rw [hg]; rfl
  rw [hg] at hgs
  unfold Tmat at hgs
  rw [Matrix.mul_fin_two] at hgs
  have e00 : p * A + q * C = ((s.1 : ℕ) : ℤ) := congrFun (congrFun hgs 0) 0
  have e01 : p * B + q * D = ((s.2.1 : ℕ) : ℤ) := congrFun (congrFun hgs 0) 1
  have e10 : r * A + w * C = 0 := congrFun (congrFun hgs 1) 0
  have e11 : r * B + w * D = ((s.2.2 : ℕ) : ℤ) := congrFun (congrFun hgs 1) 1
  have ea : (s.1 : ℂ) = p * A + q * C := by exact_mod_cast e00.symm
  have eb : (s.2.1 : ℂ) = p * B + q * D := by exact_mod_cast e01.symm
  have ez : (r : ℂ) * A + w * C = 0 := by exact_mod_cast e10
  have ee : (s.2.2 : ℂ) = r * B + w * D := by exact_mod_cast e11.symm
  have hE : (s.2.2 : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  have hden : (r : ℂ) * τ + w ≠ 0 := by
    intro h0
    have him : (r : ℝ) * τ.im = 0 := by
      have h3 := congrArg Complex.im h0
      simpa using h3
    have hτ := τ.im_pos
    have hr0 : r = 0 := by
      rcases mul_eq_zero.mp him with h4 | h4
      · exact_mod_cast h4
      · linarith
    rw [hr0] at h0
    have hw0 : w = 0 := by
      have h3 := congrArg Complex.re h0
      simp at h3
      exact_mod_cast h3
    rw [hr0, hw0] at hdg
    simp at hdg
  have c1 : ∀ z : ℤ, (((algebraMap ℤ ℝ) z : ℝ) : ℂ) = (z : ℂ) := by
    intro z
    rw [eq_intCast]
    push_cast
    rfl
  have hform : ((g • τ : ℍ) : ℂ) = ((p : ℂ) * τ + q) / ((r : ℂ) * τ + w) := by
    simp [UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom,
      UpperHalfPlane.σ, hp, hq, hr, hw]
    try rw [c1 p, c1 q, c1 r, c1 w]
  have hX : ((s.1 : ℂ) * τ + (s.2.1 : ℂ)) / (s.2.2 : ℂ) = ((p : ℂ) * τ + q) / ((r : ℂ) * τ + w) := by
    rw [div_eq_div_iff hE hden]
    linear_combination ((τ : ℂ) * (r * τ + w)) * ea + ((r : ℂ) * τ + w) * eb
      + ((p : ℂ) * (r * τ + w) - (p * τ + q) * r) * hfix + ((p : ℂ) * τ + q) * τ * ez
      - ((p : ℂ) * τ + q) * ee
  have hpt : pt s.1 s.2.1 s.2.2 τ = g • τ := by
    unfold pt
    rw [hX, ← hform]
    first
    | exact UpperHalfPlane.ofComplex_apply (g • τ)
    | simp
  unfold Gm
  apply Finset.prod_eq_zero hs
  apply fac_eq_zero_of_smul s τ g⁻¹
  rw [hpt, inv_smul_smul]

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFrobSer
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem xp_zmod {p : ℕ} (hp : p.Prime) (f : PowerSeries (ZMod p)) : xp p f = f ^ p := by
  haveI := Fact.mk hp
  ext n
  have key := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q n) (PowerSeries.trunc_trunc_pow (n := n + 1) f p)
  simp only [PowerSeries.coeff_trunc, Nat.lt_add_one, ↓reduceIte] at key
  rw [← key, ← Polynomial.coe_pow, Polynomial.coeff_coe, ← ZMod.expand_card, Polynomial.coeff_expand hp.pos]
  simp only [xp, PowerSeries.coeff_mk]
  split_ifs with h
  · rw [PowerSeries.coeff_trunc, if_pos (Nat.lt_succ_of_le (Nat.div_le_self n p))]
  · rfl

theorem exists_C_mul_of_map_eq_zero {p : ℕ} (h : PowerSeries ℤ)
    (h0 : h.map (Int.castRingHom (ZMod p)) = 0) :
    ∃ g : PowerSeries ℤ, h = PowerSeries.C (p : ℤ) * g := by
  have hd : ∀ n, (p : ℤ) ∣ PowerSeries.coeff n h := by
    intro n
    have h1 := congrArg (PowerSeries.coeff n) h0
    rw [PowerSeries.coeff_map, map_zero, eq_intCast] at h1
    exact (CharP.intCast_eq_zero_iff (ZMod p) p _).1 h1
  refine ⟨PowerSeries.mk fun n => PowerSeries.coeff n h / p, ?_⟩
  ext n
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, Int.mul_ediv_cancel' (hd n)]

theorem xp_congr {p : ℕ} (hp : p.Prime) (f : PowerSeries ℤ) :
    ∃ g : PowerSeries ℤ, xp p f = f ^ p + PowerSeries.C (p : ℤ) * g := by
  have hmap : (xp p f).map (Int.castRingHom (ZMod p)) = xp p (f.map (Int.castRingHom (ZMod p))) := by
    ext n
    simp only [xp, PowerSeries.coeff_map, PowerSeries.coeff_mk]
    split_ifs <;> simp
  have h0 : (xp p f - f ^ p).map (Int.castRingHom (ZMod p)) = 0 := by
    rw [map_sub, map_pow, hmap, xp_zmod hp, sub_self]
  obtain ⟨g, hg⟩ := exists_C_mul_of_map_eq_zero (p := p) _ h0
  exact ⟨g, by rw [← hg]; ring⟩

theorem sub_pow_congr {p : ℕ} (hp : p.Prime) (f g : PowerSeries ℤ) :
    ∃ w : PowerSeries ℤ, (f - g) ^ p = f ^ p - g ^ p + PowerSeries.C (p : ℤ) * w := by
  haveI := Fact.mk hp
  haveI : CharP (PowerSeries (ZMod p)) p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) (PowerSeries (ZMod p))).injective p
  have h0 : ((f - g) ^ p - (f ^ p - g ^ p)).map (Int.castRingHom (ZMod p)) = 0 := by
    rw [map_sub, map_pow, map_sub, map_sub, map_pow, map_pow, sub_pow_char, sub_self]
  obtain ⟨w, hw⟩ := exists_C_mul_of_map_eq_zero (p := p) _ h0
  exact ⟨w, by rw [← hw]; ring⟩

theorem rescale_congr {p : ℕ} (hp : 0 < p) (b : ℕ) (f : PowerSeries ℤ) :
    ∃ w : PowerSeries ℂ, CoeffIn (Rm p) w ∧
      PowerSeries.rescale (zetaC p ^ b) (f.map (Int.castRingHom ℂ)) =
        f.map (Int.castRingHom ℂ) + PowerSeries.C (1 - zetaC p) * w := by
  refine ⟨PowerSeries.mk fun n => -(∑ i ∈ Finset.range (b * n), zetaC p ^ i) * ((PowerSeries.coeff n f : ℤ) : ℂ), ?_, ?_⟩
  · intro n
    rw [PowerSeries.coeff_mk]
    exact mul_mem (neg_mem (sum_mem fun i _ => pow_mem (Subring.subset_closure (Set.mem_singleton _)) _))
      (intCast_mem _ _)
  · ext n
    simp only [map_add (f := _), PowerSeries.coeff_rescale, PowerSeries.coeff_map, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_mk, eq_intCast]
    have hg := geom_sum_mul (zetaC p) (b * n)
    linear_combination (-((PowerSeries.coeff n f : ℤ) : ℂ)) * hg

theorem zetaC_isPrimitiveRoot {p : ℕ} (hp : p ≠ 0) : IsPrimitiveRoot (zetaC p) p := Complex.isPrimitiveRoot_exp p hp

theorem p_mem_span {p : ℕ} (hp : p.Prime) : ∃ r ∈ Rm p, (p : ℂ) = (1 - zetaC p) * r := by
  haveI := Fact.mk hp
  have hζ := zetaC_isPrimitiveRoot hp.ne_zero
  have hmem : ∀ μ ∈ primitiveRoots p ℂ, μ ∈ Rm p := by
    intro μ hμ
    rw [mem_primitiveRoots hp.pos] at hμ
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one
    exact pow_mem (Subring.subset_closure (Set.mem_singleton _)) _
  have hprod : (p : ℂ) = ∏ μ ∈ primitiveRoots p ℂ, (1 - μ) := by
    have h1 := Polynomial.eval_one_cyclotomic_prime (R := ℂ) (p := p)
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at h1
    simpa using h1.symm
  refine ⟨∏ μ ∈ (primitiveRoots p ℂ).erase (zetaC p), (1 - μ),
    prod_mem fun μ hμ => sub_mem (one_mem _) (hmem μ (Finset.mem_of_mem_erase hμ)), ?_⟩
  rw [hprod, Finset.mul_prod_erase _ _ ((mem_primitiveRoots hp.pos).2 hζ)]

theorem one_sub_zeta_pow {p : ℕ} (hp : p.Prime) : ∃ r ∈ Rm p, (1 - zetaC p) ^ p = (p : ℂ) * r := by
  have hζ := zetaC_isPrimitiveRoot hp.ne_zero
  have hz : zetaC p ∈ Rm p := Subring.subset_closure (Set.mem_singleton _)
  set z : Rm p := ⟨zetaC p, hz⟩ with hzdef
  have hzc : (z : ℂ) = zetaC p := rfl
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (1 : Rm p) (-z)
  have hr' : (1 - zetaC p) ^ p = 1 + (-zetaC p) ^ p + p * (-(zetaC p * (r : ℂ))) := by
    have h1 := congrArg (fun x : Rm p => (x : ℂ)) hr
    push_cast at h1
    rw [hzc] at h1
    rw [sub_eq_add_neg, h1]
    ring
  have hm : -(zetaC p * (r : ℂ)) ∈ Rm p := neg_mem (mul_mem hz r.2)
  rcases hp.eq_two_or_odd' with rfl | hodd
  · refine ⟨1 + -(zetaC 2 * (r : ℂ)), add_mem (one_mem _) hm, ?_⟩
    rw [hr', neg_sq, hζ.pow_eq_one]
    push_cast
    ring
  · refine ⟨-(zetaC p * (r : ℂ)), hm, ?_⟩
    rw [hr', hodd.neg_pow, hζ.pow_eq_one]
    ring

theorem one_sub_zeta_ne_zero {p : ℕ} (hp : p.Prime) : 1 - zetaC p ≠ 0 := by
  exact sub_ne_zero.2 ((zetaC_isPrimitiveRoot hp.ne_zero).ne_one hp.one_lt).symm

end ReciprocityTheory.ChartRestriction.L1
end
end
