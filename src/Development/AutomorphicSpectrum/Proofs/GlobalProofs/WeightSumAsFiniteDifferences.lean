module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ShintaniValuesNegativeIntegersRational
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeSeriesDerivativeGrowthBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeSeriesDerivativeGrowthBound
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem one_le_sizeE_of_nonneg {r : ℕ} (x : Fin r → ℝ) (hx : ∀ i, 0 ≤ x i) : 1 ≤ sizeE x := by
  unfold sizeE
  have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hx i)
  linarith

theorem linF_comparable_sizeE {ι : Type} {r : ℕ} (a : ι → Fin r → ℝ) (b : ι → ℝ) (j : ι)
    (ha : ∀ i, 0 < a j i) (hb : 0 < b j) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : Fin r → ℝ, (∀ i, 0 ≤ x i) →
      c * sizeE x ≤ linF a b j x ∧ linF a b j x ≤ C * sizeE x := by
  let f : Option (Fin r) → ℝ := fun o => o.elim (b j) (a j)
  obtain ⟨p, hp⟩ := Finite.exists_min f
  obtain ⟨q, hq⟩ := Finite.exists_max f
  have hpos : ∀ o, 0 < f o := by
    intro o
    cases o with
    | none => exact hb
    | some i => exact ha i
  refine ⟨f p, f q, hpos p, hpos q, fun x hx => ?_⟩
  unfold linF sizeE
  constructor
  · rw [mul_add, mul_one, Finset.mul_sum]
    exact add_le_add (hp none)
      (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hp (some i)) (hx i))
  · rw [mul_add, mul_one, Finset.mul_sum]
    exact add_le_add (hq none)
      (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hq (some i)) (hx i))

theorem rpow_le_of_comparable (c C T : ℝ) (hc : 0 < c) (hC : 0 < C) (hT : 0 ≤ T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L E t D : ℝ, 1 ≤ E → c * E ≤ L → L ≤ C * E → |t| ≤ T → t ≤ D →
      L ^ t ≤ K * E ^ D := by
  refine ⟨Real.exp ((|Real.log c| + |Real.log C|) * T), (Real.exp_pos _).le, ?_⟩
  intro L E t D hE h1 h2 ht htD
  have hE0 : 0 < E := by linarith
  have hL : 0 < L := lt_of_lt_of_le (mul_pos hc hE0) h1
  have hu : 0 < L / E := div_pos hL hE0
  have hu1 : c ≤ L / E := (le_div_iff₀ hE0).2 h1
  have hu2 : L / E ≤ C := (div_le_iff₀ hE0).2 h2
  have hlog1 : Real.log c ≤ Real.log (L / E) := Real.log_le_log hc hu1
  have hlog2 : Real.log (L / E) ≤ Real.log C := Real.log_le_log hu hu2
  have habs : |Real.log (L / E)| ≤ |Real.log c| + |Real.log C| := by
    rw [abs_le]
    constructor
    · have := neg_abs_le (Real.log c)
      have := abs_nonneg (Real.log C)
      linarith
    · have := le_abs_self (Real.log C)
      have := abs_nonneg (Real.log c)
      linarith
  have hLE : L = (L / E) * E := by field_simp
  have hfirst : (L / E) ^ t ≤ Real.exp ((|Real.log c| + |Real.log C|) * T) := by
    rw [Real.rpow_def_of_pos hu]
    apply Real.exp_le_exp.2
    calc Real.log (L / E) * t ≤ |Real.log (L / E) * t| := le_abs_self _
      _ = |Real.log (L / E)| * |t| := abs_mul _ _
      _ ≤ (|Real.log c| + |Real.log C|) * T :=
        mul_le_mul habs ht (abs_nonneg _) (by positivity)
  have hsecond : E ^ t ≤ E ^ D := Real.rpow_le_rpow_of_exponent_le hE htD
  calc L ^ t = (L / E) ^ t * E ^ t := by
        rw [← Real.mul_rpow hu.le hE0.le, ← hLE]
    _ ≤ Real.exp ((|Real.log c| + |Real.log C|) * T) * E ^ D :=
        mul_le_mul hfirst hsecond (Real.rpow_nonneg hE0.le _) (Real.exp_pos _).le

theorem prod_zpow_eq_zpow_sum {ι : Type} (E : ℝ) (hE : E ≠ 0) (S : Finset ι) (f : ι → ℤ) :
    ∏ j ∈ S, E ^ f j = E ^ ∑ j ∈ S, f j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ hE]

theorem norm_factor_le {ι : Type} (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (j : ι)
    (ha : ∀ i, 0 < a j i) (hb : 0 < b j) (B R β : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, ‖s‖ ≤ R → -(B : ℝ) ≤ s.re → ∀ x : Fin r → ℝ, (∀ i, 0 ≤ x i) →
      ‖((linF a b j x : ℝ) : ℂ) ^ (-s - (β : ℂ))‖ ≤ K * sizeE x ^ ((B : ℤ) - (β : ℤ)) := by
  obtain ⟨c, C, hc, hC, hcmp⟩ := linF_comparable_sizeE a b j ha hb
  obtain ⟨K, hK0, hK⟩ := rpow_le_of_comparable c C ((R : ℝ) + β) hc hC (by positivity)
  refine ⟨K, hK0, fun s hs hs' x hx => ?_⟩
  have hE := one_le_sizeE_of_nonneg x hx
  have hE0 : 0 < sizeE x := by linarith
  obtain ⟨h1, h2⟩ := hcmp x hx
  have hL : 0 < linF a b j x := lt_of_lt_of_le (mul_pos hc hE0) h1
  have hre : (-s - (β : ℂ)).re = -s.re - β := by simp
  have hsr : |s.re| ≤ R := (Complex.abs_re_le_norm s).trans hs
  have hβ : (0 : ℝ) ≤ β := by positivity
  have ht : |-s.re - (β : ℝ)| ≤ (R : ℝ) + β := by
    rw [abs_le] at hsr ⊢
    constructor <;> linarith [hsr.1, hsr.2]
  have htD : -s.re - (β : ℝ) ≤ (((B : ℤ) - (β : ℤ) : ℤ) : ℝ) := by
    push_cast
    linarith
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hL, hre, ← Real.rpow_intCast]
  exact hK _ _ _ _ hE h1 h2 ht htD

theorem baseBound : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ (B R : ℕ) (β : ι → ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, ‖s‖ ≤ R → -(B : ℝ) ≤ s.re →
  ∀ x : Fin r → ℝ, (∀ i, 0 ≤ x i) →
    ‖Fr a b s β x‖ ≤ C * sizeE x ^ ((Fintype.card ι : ℤ) * (B : ℤ) - ∑ j, (β j : ℤ)) := by
  intro ι _ r a b ha hb B R β
  have hj := fun j => norm_factor_le r a b j (ha j) (hb j) B R (β j)
  choose K hK0 hK using hj
  refine ⟨∏ j, K j, Finset.prod_nonneg fun j _ => hK0 j, fun s hs hs' x hx => ?_⟩
  have hE0 : sizeE x ≠ 0 := by
    have := one_le_sizeE_of_nonneg x hx
    intro h
    linarith
  unfold Fr
  rw [norm_prod]
  calc ∏ j, ‖((linF a b j x : ℝ) : ℂ) ^ (-s - (β j : ℂ))‖
      ≤ ∏ j, (K j * sizeE x ^ ((B : ℤ) - (β j : ℤ))) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hK j s hs hs' x hx)
    _ = (∏ j, K j) * sizeE x ^ ((Fintype.card ι : ℤ) * (B : ℤ) - ∑ j, (β j : ℤ)) := by
        rw [Finset.prod_mul_distrib, prod_zpow_eq_zpow_sum _ hE0, Finset.sum_sub_distrib]
        simp

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeSeriesDerivativeGrowthBoundStatement
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_series_derivative_growth_bound : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ (B R : ℕ) (β : ι → ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, ‖s‖ ≤ R → -(B : ℝ) ≤ s.re →
  ∀ x : Fin r → ℝ, (∀ i, 0 ≤ x i) →
    ‖Fr a b s β x‖ ≤ C * sizeE x ^ ((Fintype.card ι : ℤ) * (B : ℤ) - ∑ j, (β j : ℤ)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.baseBound | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.baseBound | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.baseBound <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeSeriesRealDerivativeFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeSeriesRealDerivativeFormula
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DerivDLR

variable {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ}

lemma linF_line (a : ι → Fin r → ℝ) (b : ι → ℝ) (j : ι) (x : Fin r → ℝ) (i : Fin r) (t : ℝ) :
    linF a b j (x + t • (Pi.single i 1 : Fin r → ℝ)) = linF a b j x + t * a j i := by
  have h : ∀ k, a j k * (x + t • (Pi.single i 1 : Fin r → ℝ)) k
      = a j k * x k + (if k = i then t * a j i else 0) := by
    intro k
    by_cases hk : k = i
    · subst hk; simp; ring
    · simp [Pi.single_apply, hk]
  simp only [linF, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

lemma linF_pos (a : ι → Fin r → ℝ) (b : ι → ℝ) (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j)
    (j : ι) (y : Fin r → ℝ) (hy : ∀ k, 0 ≤ y k) : 0 < linF a b j y := by
  have : 0 ≤ ∑ i, a j i * y i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (ha j i).le (hy i)
  have := hb j
  unfold linF
  linarith

lemma hasDerivAt_factor (a : ι → Fin r → ℝ) (b : ι → ℝ) (w : ℂ) (j : ι) (i : Fin r)
    (x : Fin r → ℝ) (τ : ℝ)
    (hpos : 0 < linF a b j (x + τ • (Pi.single i 1 : Fin r → ℝ))) :
    HasDerivAt (fun t : ℝ => ((linF a b j (x + t • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ^ w)
      ((a j i : ℂ) * (w * ((linF a b j (x + τ • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ^ (w - 1))) τ := by
  have hlin : HasDerivAt (fun t : ℝ => linF a b j (x + t • (Pi.single i 1 : Fin r → ℝ))) (a j i) τ := by
    have : (fun t : ℝ => linF a b j (x + t • (Pi.single i 1 : Fin r → ℝ)))
        = fun t : ℝ => linF a b j x + t * a j i := by
      funext t; exact linF_line a b j x i t
    rw [this]
    simpa using ((hasDerivAt_id τ).mul_const (a j i)).const_add (linF a b j x)
  have hC := hlin.ofReal_comp
  have hslit : ((linF a b j (x + τ • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ∈ Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.2 hpos
  have hpow := ((hasDerivAt_id _).cpow_const (c := w) hslit)
  refine (HasDerivAt.scomp τ hpow hC).congr_deriv ?_
  simp only [id, mul_one, smul_eq_mul]
  rfl

lemma hasDerivAt_Fr (a : ι → Fin r → ℝ) (b : ι → ℝ) (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j)
    (s : ℂ) (β : ι → ℕ) (i : Fin r) (x : Fin r → ℝ) (τ : ℝ)
    (hy : ∀ k, 0 ≤ (x + τ • (Pi.single i 1 : Fin r → ℝ)) k) :
    HasDerivAt (fun t : ℝ => Fr a b s β (x + t • (Pi.single i 1 : Fin r → ℝ)))
      (∑ j, (-s - (β j : ℂ)) * (a j i : ℂ) *
        Fr a b s (β + Pi.single j 1) (x + τ • (Pi.single i 1 : Fin r → ℝ))) τ := by
  have hprod := HasDerivAt.fun_finsetProd (u := Finset.univ)
    (f := fun j (t : ℝ) => ((linF a b j (x + t • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ^ (-s - (β j : ℂ)))
    (x := τ)
    (fun j _ => hasDerivAt_factor a b (-s - (β j : ℂ)) j i x τ (linF_pos a b ha hb j _ hy))
  refine hprod.congr_deriv ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  have hF : Fr a b s (β + Pi.single j 1) (x + τ • (Pi.single i 1 : Fin r → ℝ))
      = ((linF a b j (x + τ • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ^ (-s - (β j : ℂ) - 1) *
        ∏ k ∈ Finset.univ.erase j,
          ((linF a b k (x + τ • (Pi.single i 1 : Fin r → ℝ)) : ℝ) : ℂ) ^ (-s - (β k : ℂ)) := by
    unfold Fr
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    congr 1
    · congr 1
      simp only [Pi.add_apply, Pi.single_eq_same]
      push_cast
      ring
    · refine Finset.prod_congr rfl fun k hk => ?_
      have hkj : k ≠ j := Finset.ne_of_mem_erase hk
      simp [Pi.single_apply, hkj]
  rw [hF, smul_eq_mul]
  ring

theorem hasDerivAt_DLR_Fr (ι : Type) [Fintype ι] [DecidableEq ι] (r : ℕ) (a : ι → Fin r → ℝ)
    (b : ι → ℝ) (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j)
    (s : ℂ) (β : ι → ℕ) (cs : List (Fin r)) (i : Fin r) (x : Fin r → ℝ) (τ : ℝ)
    (hx : ∀ k, 0 ≤ x k) (hτ : 0 ≤ τ) :
    HasDerivAt (fun t : ℝ => DLR cs (Fr a b s β) (x + t • (Pi.single i 1 : Fin r → ℝ)))
      (∑ j, (-s - (β j : ℂ)) * (a j i : ℂ) *
        DLR cs (Fr a b s (β + Pi.single j 1)) (x + τ • (Pi.single i 1 : Fin r → ℝ))) τ := by
  induction cs generalizing x with
  | nil =>
    have hy : ∀ k, 0 ≤ (x + τ • (Pi.single i 1 : Fin r → ℝ)) k := by
      intro k
      have : 0 ≤ τ * (Pi.single i 1 : Fin r → ℝ) k := by
        refine mul_nonneg hτ ?_
        by_cases hk : k = i
        · subst hk; simp
        · simp [Pi.single_apply, hk]
      simpa using add_nonneg (hx k) this
    simpa [DLR] using hasDerivAt_Fr a b ha hb s β i x τ hy
  | cons c cs ih =>
    have hxc : ∀ k, 0 ≤ (x + (Pi.single c 1 : Fin r → ℝ)) k := by
      intro k
      have : 0 ≤ (Pi.single c 1 : Fin r → ℝ) k := by
        by_cases hk : k = c
        · subst hk; simp
        · simp [Pi.single_apply, hk]
      simpa using add_nonneg (hx k) this
    have hsw : ∀ (G : (Fin r → ℝ) → ℂ) (t : ℝ),
        DLR (c :: cs) G (x + t • (Pi.single i 1 : Fin r → ℝ))
          = DLR cs G ((x + (Pi.single c 1 : Fin r → ℝ)) + t • (Pi.single i 1 : Fin r → ℝ))
            - DLR cs G (x + t • (Pi.single i 1 : Fin r → ℝ)) := by
      intro G t
      have : x + t • (Pi.single i 1 : Fin r → ℝ) + (Pi.single c 1 : Fin r → ℝ)
          = (x + (Pi.single c 1 : Fin r → ℝ)) + t • (Pi.single i 1 : Fin r → ℝ) := by abel
      change fdR c (DLR cs G) _ = _
      simp only [fdR, this]
    have h := (ih (x + Pi.single c 1) hxc).sub (ih x hx)
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hsw _ t)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsw, mul_sub]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DerivDLR
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeSeriesRealDerivativeFormulaStatement
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_series_real_derivative_formula : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), (∀ j i, 0 < a j i) → (∀ j, 0 < b j) →
  ∀ (s : ℂ) (β : ι → ℕ) (cs : List (Fin r)) (i : Fin r) (x : Fin r → ℝ) (τ : ℝ), (∀ k, 0 ≤ x k) → 0 ≤ τ →
    HasDerivAt (fun t : ℝ => DLR cs (Fr a b s β) (x + t • (Pi.single i 1 : Fin r → ℝ)))
      (∑ j, (-s - (β j : ℂ)) * (a j i : ℂ) *
        DLR cs (Fr a b s (β + Pi.single j 1)) (x + τ • (Pi.single i 1 : Fin r → ℝ))) τ := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DerivDLR.hasDerivAt_DLR_Fr | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DerivDLR.hasDerivAt_DLR_Fr | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DerivDLR.hasDerivAt_DLR_Fr <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ShintaniValuesNegativeIntegersRational
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DiffDecay

theorem zpow_le_two_pow_mul {E u : ℝ} (hE : 0 < E) (h1 : E ≤ u) (h2 : u ≤ 2 * E) (z : ℤ) :
    u ^ z ≤ 2 ^ z.natAbs * E ^ z := by
  have hu : 0 < u := lt_of_lt_of_le hE h1
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · simp only [Int.natAbs_natCast, zpow_natCast]
    calc u ^ n ≤ (2 * E) ^ n := pow_le_pow_left₀ hu.le h2 n
      _ = 2 ^ n * E ^ n := mul_pow _ _ _
  · simp only [Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_natCast]
    have hEn : 0 < E ^ n := pow_pos hE n
    have a1 : (u ^ n)⁻¹ ≤ (E ^ n)⁻¹ := inv_anti₀ hEn (pow_le_pow_left₀ hE.le h1 n)
    have a2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    calc (u ^ n)⁻¹ ≤ (E ^ n)⁻¹ := a1
      _ = 1 * (E ^ n)⁻¹ := (one_mul _).symm
      _ ≤ 2 ^ n * (E ^ n)⁻¹ := mul_le_mul_of_nonneg_right a2 (inv_nonneg.2 hEn.le)

theorem one_le_sizeE {r : ℕ} {x : Fin r → ℝ} (hx : ∀ i, 0 ≤ x i) : 1 ≤ sizeE x := by
  have : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => hx i
  unfold sizeE; linarith

theorem sizeE_add_smul {r : ℕ} (x : Fin r → ℝ) (c : Fin r) (τ : ℝ) :
    sizeE (x + τ • (Pi.single c 1 : Fin r → ℝ)) = sizeE x + τ := by
  simp [sizeE, Finset.sum_add_distrib, Pi.single_apply]
  ring

theorem nonneg_add_smul {r : ℕ} {x : Fin r → ℝ} (hx : ∀ i, 0 ≤ x i) (c : Fin r) {τ : ℝ} (hτ : 0 ≤ τ) (k : Fin r) :
    0 ≤ (x + τ • (Pi.single c 1 : Fin r → ℝ)) k := by
  have : 0 ≤ τ * (Pi.single c 1 : Fin r → ℝ) k := by
    refine mul_nonneg hτ ?_
    by_cases h : k = c
    · subst h; simp
    · simp [Pi.single_apply, h]
  simpa using add_nonneg (hx k) this

theorem sum_add_single {ι : Type} [Fintype ι] [DecidableEq ι] (β : ι → ℕ) (j : ι) :
    ∑ i, (((β + Pi.single j 1 : ι → ℕ) i : ℕ) : ℤ) = ∑ i, (β i : ℤ) + 1 := by
  simp [Finset.sum_add_distrib, Pi.single_apply]

theorem diff_bound (ι : Type) [Fintype ι] [DecidableEq ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j) (B R : ℕ) (cs : List (Fin r)) (β : ι → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, ‖s‖ ≤ R → -(B : ℝ) ≤ s.re → ∀ x : Fin r → ℝ, (∀ i, 0 ≤ x i) →
      ‖DLR cs (Fr a b s β) x‖ ≤ C * sizeE x ^ ((Fintype.card ι : ℤ) * (B : ℤ) - ∑ j, (β j : ℤ) - (cs.length : ℤ)) := by
  induction cs generalizing β with
  | nil =>
    obtain ⟨C, hC, h⟩ := GlobalTheory.T.cone_series_derivative_growth_bound ι r a b ha hb B R β
    refine ⟨C, hC, fun s hs hB x hx => ?_⟩
    simpa [DLR] using h s hs hB x hx
  | cons c cs ih =>
    choose C hC0 hC using fun j => ih (β + Pi.single j 1)
    obtain ⟨z, hz⟩ : ∃ z : ℤ, z = (Fintype.card ι : ℤ) * (B : ℤ) - ∑ j, (β j : ℤ) - ((c :: cs).length : ℤ) := ⟨_, rfl⟩
    rw [← hz]
    have hzj : ∀ j, (Fintype.card ι : ℤ) * (B : ℤ) - ∑ i, (((β + Pi.single j 1 : ι → ℕ) i : ℕ) : ℤ) - (cs.length : ℤ) = z := by
      intro j
      rw [sum_add_single, hz, List.length_cons]
      push_cast
      ring
    have hterm : ∀ j, 0 ≤ ((R : ℝ) + β j) * a j c * C j := fun j =>
      mul_nonneg (mul_nonneg (by positivity) (ha j c).le) (hC0 j)
    refine ⟨(∑ j, ((R : ℝ) + β j) * a j c * C j) * 2 ^ z.natAbs,
      mul_nonneg (Finset.sum_nonneg fun j _ => hterm j) (by positivity), fun s hs hB x hx => ?_⟩
    have hE1 : 1 ≤ sizeE x := one_le_sizeE hx
    have hE0 : 0 < sizeE x := by linarith
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01'
      (f := fun t : ℝ => DLR cs (Fr a b s β) (x + t • (Pi.single c 1 : Fin r → ℝ)))
      (f' := fun τ => ∑ j, (-s - (β j : ℂ)) * (a j c : ℂ) *
        DLR cs (Fr a b s (β + Pi.single j 1)) (x + τ • (Pi.single c 1 : Fin r → ℝ)))
      (C := (∑ j, ((R : ℝ) + β j) * a j c * C j) * 2 ^ z.natAbs * sizeE x ^ z)
      (fun τ hτ => (GlobalTheory.T.cone_series_real_derivative_formula ι r a b ha hb s β cs c x τ hx hτ.1).hasDerivWithinAt)
      (fun τ hτ => ?_)
    · simpa [DLR, fdR] using hmv
    · have hu1 : sizeE x ≤ sizeE (x + τ • (Pi.single c 1 : Fin r → ℝ)) := by
        rw [sizeE_add_smul]; linarith [hτ.1]
      have hu2 : sizeE (x + τ • (Pi.single c 1 : Fin r → ℝ)) ≤ 2 * sizeE x := by
        rw [sizeE_add_smul]; linarith [hτ.2.le]
      have hpow := zpow_le_two_pow_mul hE0 hu1 hu2 z
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_le_sum fun j _ => ?_
      have hD := hC j s hs hB _ (nonneg_add_smul hx c hτ.1)
      rw [hzj j] at hD
      have hs1 : ‖-s - (β j : ℂ)‖ ≤ (R : ℝ) + β j := by
        refine (norm_sub_le _ _).trans ?_
        simpa using hs
      have ha1 : ‖(a j c : ℂ)‖ = a j c := by
        simp [abs_of_pos (ha j c)]
      rw [norm_mul, norm_mul, ha1]
      calc ‖-s - (β j : ℂ)‖ * a j c * ‖DLR cs (Fr a b s (β + Pi.single j 1)) (x + τ • (Pi.single c 1 : Fin r → ℝ))‖
          ≤ ((R : ℝ) + β j) * a j c * (C j * (2 ^ z.natAbs * sizeE x ^ z)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right hs1 (ha j c).le) (hD.trans ?_) (norm_nonneg _)
              (mul_nonneg (by positivity) (ha j c).le)
            exact mul_le_mul_of_nonneg_left hpow (hC0 j)
        _ = ((R : ℝ) + β j) * a j c * C j * 2 ^ z.natAbs * sizeE x ^ z := by ring

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DiffDecay
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ShintaniValuesNegativeIntegersRationalStatement
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_difference_cone_bound : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ (B R : ℕ) (cs : List (Fin r)) (β : ι → ℕ),
  ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, ‖s‖ ≤ R → -(B : ℝ) ≤ s.re → ∀ x : Fin r → ℝ, (∀ i, 0 ≤ x i) →
    ‖DLR cs (Fr a b s β) x‖ ≤ C * sizeE x ^ ((Fintype.card ι : ℤ) * (B : ℤ) - ∑ j, (β j : ℤ) - (cs.length : ℤ)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DiffDecay.diff_bound | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DiffDecay.diff_bound | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DiffDecay.diff_bound <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HighDifferenceVanishesNegativeInteger
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HighDifferenceVanishesNegativeInteger
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem coneTerm_differentiable_in_s_alt {ι : Type} [Fintype ι] {r : ℕ} {a : ι → Fin r → ℝ} {b : ι → ℝ}
    (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j) (m : Fin r → ℕ) :
    Differentiable ℂ (fun s => coneTerm a b s m) := by
  unfold GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.coneTerm
  refine Differentiable.fun_finsetProd fun j _ => ?_
  refine Differentiable.const_cpow differentiable_neg (Or.inl ?_)
  have hpos : 0 < b j + ∑ i, a j i * (m i : ℝ) :=
    add_pos_of_pos_of_nonneg (hb j)
      (Finset.sum_nonneg fun i _ => mul_nonneg (ha j i).le (Nat.cast_nonneg _))
  exact Complex.ofReal_ne_zero.mpr hpos.ne'

theorem DL_coneTerm_differentiable : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ),
    (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ (cs : List (Fin r)) (m : Fin r → ℕ),
      Differentiable ℂ (fun s => DL cs (coneTerm a b s) m) := by
  intro ι _ r a b ha hb cs
  induction cs with
  | nil => intro m; exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.coneTerm_differentiable_in_s_alt ha hb m
  | cons c cs ih =>
    intro m
    simp only [GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL, List.foldr_cons, GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.fd] at ih ⊢
    exact (ih (m + Pi.single c 1)).sub (ih m)

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HighDifferenceVanishesNegativeIntegerStatement
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_difference_cone_term_differentiable : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ (cs : List (Fin r)) (m : Fin r → ℕ), Differentiable ℂ (fun s => DL cs (coneTerm a b s) m) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_differentiable | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_differentiable | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_differentiable <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDifferenceConeTermEq
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDifferenceConeTermEq
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem cast_add_single_one {r : ℕ} (m : Fin r → ℕ) (c : Fin r) :
    (fun i => (((m + Pi.single c 1 : Fin r → ℕ) i : ℕ) : ℝ)) =
      (fun i => (m i : ℝ)) + Pi.single c 1 := by
  funext i
  by_cases h : i = c
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

theorem DL_coneTerm_eq_DLR : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (s : ℂ) (cs : List (Fin r)) (m : Fin r → ℕ),
  DL cs (coneTerm a b s) m = DLR cs (Fr a b s 0) (fun i => (m i : ℝ)) := by
  intro ι _ r a b s cs m
  induction cs generalizing m with
  | nil => simp [DL, DLR, coneTerm, Fr, linF]
  | cons c cs ih =>
    have h1 : DL (c :: cs) (coneTerm a b s) m =
        DL cs (coneTerm a b s) (m + Pi.single c 1) - DL cs (coneTerm a b s) m := rfl
    have h2 : ∀ x : Fin r → ℝ, DLR (c :: cs) (Fr a b s 0) x =
        DLR cs (Fr a b s 0) (x + Pi.single c 1) - DLR cs (Fr a b s 0) x := fun _ => rfl
    rw [h1, h2, ih, ih, cast_add_single_one]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDifferenceConeTermEqStatement
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_difference_cone_term_eq : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (s : ℂ) (cs : List (Fin r)) (m : Fin r → ℕ),
  DL cs (coneTerm a b s) m = DLR cs (Fr a b s 0) (fun i => (m i : ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_eq_DLR | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_eq_DLR | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_eq_DLR <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SummableInverseSquareProduct
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SummableInverseSquareProduct
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem summable_inv_one_add_sq :
    Summable (fun n : ℕ => ((1 + (n : ℝ)) ^ 2)⁻¹) := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  refine ((summable_nat_add_iff 1).mpr h).congr fun n => ?_
  simp only [Nat.cast_add, Nat.cast_one, one_div, add_comm (n : ℝ) 1]

theorem summable_prod_inv_one_add_sq :
    ∀ r : ℕ, Summable (fun m : Fin r → ℕ => ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹) := by
  intro r
  induction r with
  | zero => exact Summable.of_finite
  | succ r ih =>
    have h := GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_inv_one_add_sq.mul_of_nonneg ih
      (fun n => inv_nonneg.mpr (sq_nonneg _))
      (fun m => Finset.prod_nonneg fun i _ => inv_nonneg.mpr (sq_nonneg _))
    rw [← (Fin.consEquiv fun _ : Fin (r + 1) => ℕ).summable_iff]
    refine h.congr fun p => ?_
    simp [Fin.consEquiv, Fin.prod_univ_succ, mul_comm]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SummableInverseSquareProductStatement
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_inverse_square_product : ∀ r : ℕ, Summable (fun m : Fin r → ℕ => ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_prod_inv_one_add_sq | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_prod_inv_one_add_sq | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_prod_inv_one_add_sq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SizePowerLeInverseSquareProduct
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SizePowerLeInverseSquareProduct
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem sizeE_zpow_le_prod_inv_sq (r n B N : ℕ) (cs : List (Fin r)) (m : Fin r → ℕ)
    (hN : n * B + 2 ≤ N) (hc : ∀ i, cs.count i = N ∨ m i = 0) :
    sizeE (fun i => (m i : ℝ)) ^ ((n : ℤ) * (B : ℤ) - (cs.length : ℤ)) ≤
      ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹ := by
  have hcount : ∀ l : List (Fin r), ∑ i, l.count i = l.length := by
    intro l
    first
      | simpa using Multiset.sum_count_eq_card (l : Multiset (Fin r))
      | (induction l with
          | nil => simp
          | cons a t ih => simp [List.count_cons, Finset.sum_add_distrib, ih])
  set S := sizeE (fun i => (m i : ℝ)) with hSdef
  have hSval : S = 1 + ∑ i, (m i : ℝ) := rfl
  have hsum0 : 0 ≤ ∑ i, (m i : ℝ) := Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  have hS1 : 1 ≤ S := by rw [hSval]; linarith
  have hmS : ∀ i, 1 + (m i : ℝ) ≤ S := by
    intro i
    rw [hSval]
    have := Finset.single_le_sum (f := fun j => (m j : ℝ)) (fun j _ => Nat.cast_nonneg (m j)) (Finset.mem_univ i)
    linarith
  set K := Finset.univ.filter (fun i => m i ≠ 0) with hKdef
  set k := K.card with hkdef
  have hg : ∏ i, (if m i ≠ 0 then (S ^ 2)⁻¹ else (1 : ℝ)) = ((S ^ 2)⁻¹) ^ k := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  have hle : ∏ i, (if m i ≠ 0 then (S ^ 2)⁻¹ else (1 : ℝ)) ≤ ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹ := by
    apply Finset.prod_le_prod₀
    · intro i _
      split_ifs
      · positivity
      · norm_num
    · intro i _
      split_ifs with hi
      · exact inv_anti₀ (by positivity) (by gcongr; exact hmS i)
      · rw [ne_eq, not_not] at hi
        simp [hi]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · have hm : ∀ i, m i = 0 := by
      intro i
      by_contra hi
      have hiK : i ∈ K := by simp [hKdef, hi]
      rw [Finset.card_eq_zero.mp hk] at hiK
      simp at hiK
    have hS : S = 1 := by rw [hSval]; simp [hm]
    calc S ^ ((n : ℤ) * (B : ℤ) - (cs.length : ℤ)) = ((S ^ 2)⁻¹) ^ k := by rw [hS, hk]; simp
      _ ≤ ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹ := by rw [← hg]; exact hle
  · have hKsum : ∑ i ∈ K, cs.count i = k * N := by
      have hKN : ∀ i ∈ K, cs.count i = N := fun i hi => (hc i).resolve_right (Finset.mem_filter.mp hi).2
      rw [Finset.sum_congr rfl hKN, Finset.sum_const, smul_eq_mul]
    have hLk : k * N ≤ cs.length := by
      rw [← hKsum, ← hcount cs]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ K)
    have h2 : n * B ≤ n * B * k := Nat.le_mul_of_pos_right _ hk
    have hA : n * B + 2 * k ≤ cs.length :=
      calc n * B + 2 * k ≤ n * B * k + 2 * k := Nat.add_le_add_right h2 _
        _ = (n * B + 2) * k := by ring
        _ ≤ N * k := Nat.mul_le_mul_right k hN
        _ = k * N := Nat.mul_comm _ _
        _ ≤ cs.length := hLk
    have hexp : (n : ℤ) * (B : ℤ) - (cs.length : ℤ) ≤ -(2 * (k : ℤ)) := by
      have hcast : ((n * B + 2 * k : ℕ) : ℤ) ≤ (cs.length : ℤ) := by exact_mod_cast hA
      push_cast at hcast
      linarith
    have hz : S ^ (-(2 * (k : ℤ))) = ((S ^ 2)⁻¹) ^ k := by
      rw [zpow_neg, show (2 * (k : ℤ)) = ((2 * k : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul, inv_pow]
    calc S ^ ((n : ℤ) * (B : ℤ) - (cs.length : ℤ)) ≤ S ^ (-(2 * (k : ℤ))) := zpow_le_zpow_right₀ hS1 hexp
      _ = ((S ^ 2)⁻¹) ^ k := hz
      _ = ∏ i, (if m i ≠ 0 then (S ^ 2)⁻¹ else (1 : ℝ)) := hg.symm
      _ ≤ ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹ := hle

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SizePowerLeInverseSquareProductStatement
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.size_power_le_inverse_square_product : ∀ (r n B N : ℕ) (cs : List (Fin r)) (m : Fin r → ℕ), n * B + 2 ≤ N → (∀ i, cs.count i = N ∨ m i = 0) →
  sizeE (fun i => (m i : ℝ)) ^ ((n : ℤ) * (B : ℤ) - (cs.length : ℤ)) ≤ ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.sizeE_zpow_le_prod_inv_sq | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.sizeE_zpow_le_prod_inv_sq | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.sizeE_zpow_le_prod_inv_sq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.WeightSumAsFiniteDifferences
set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem differentiableOn_tsum_weighted_DL_halfplane : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ (B N : ℕ) (cs : List (Fin r)) (u : (Fin r → ℕ) → ℚ), Fintype.card ι * B + 2 ≤ N → BddW u →
  (∀ i, cs.count i = N ∨ ∀ m, m i ≠ 0 → u m = 0) →
  DifferentiableOn ℂ (fun s => ∑' m, (u m : ℂ) * DL cs (coneTerm a b s) m) {s | -(B : ℝ) < s.re} := by
  intro ι _ r a b ha hb B N cs u hN hu hsupp
  classical
  obtain ⟨Cu, hCu⟩ := hu
  have hCu0 : 0 ≤ Cu := (abs_nonneg _).trans (hCu 0)
  have hopen : ∀ R : ℕ, IsOpen {s : ℂ | ‖s‖ < (R : ℝ) ∧ -(B : ℝ) < s.re} := fun R =>
    (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_re)
  have key : ∀ R : ℕ, DifferentiableOn ℂ (fun s => ∑' m, (u m : ℂ) * DL cs (coneTerm a b s) m)
      {s : ℂ | ‖s‖ < (R : ℝ) ∧ -(B : ℝ) < s.re} := by
    intro R
    obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.real_difference_cone_bound ι r a b ha hb B R cs 0
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun m : Fin r → ℕ => Cu * C * ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹)
      ((GlobalTheory.T.summable_inverse_square_product r).mul_left _) ?_ (hopen R) ?_
    · intro m
      exact ((GlobalTheory.T.finite_difference_cone_term_differentiable ι r a b ha hb cs m).const_mul _).differentiableOn
    · intro m s hs
      have hprod : 0 ≤ ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹ :=
        Finset.prod_nonneg fun i _ => by positivity
      by_cases hum : u m = 0
      · simp only [hum, Rat.cast_zero, zero_mul, norm_zero]
        positivity
      · have hcount : ∀ i, cs.count i = N ∨ m i = 0 := by
          intro i
          rcases hsupp i with h | h
          · exact Or.inl h
          · exact Or.inr (by_contra fun hne => hum (h m hne))
        have hbound := hC s hs.1.le hs.2.le (fun i => (m i : ℝ)) (fun i => Nat.cast_nonneg _)
        simp only [Pi.zero_apply, Nat.cast_zero, Finset.sum_const_zero, sub_zero] at hbound
        have hsize := GlobalTheory.T.size_power_le_inverse_square_product r (Fintype.card ι) B N cs m hN hcount
        have hDL : ‖DL cs (coneTerm a b s) m‖ ≤ C * ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹ := by
          rw [GlobalTheory.T.finite_difference_cone_term_eq ι r a b s cs m]
          exact hbound.trans (mul_le_mul_of_nonneg_left hsize hC0)
        rw [norm_mul, Complex.norm_ratCast, mul_assoc]
        exact mul_le_mul (hCu m) hDL (norm_nonneg _) hCu0
  intro s hs
  obtain ⟨R, hR⟩ := exists_nat_gt ‖s‖
  have hmem : s ∈ {s : ℂ | ‖s‖ < (R : ℝ) ∧ -(B : ℝ) < s.re} := ⟨hR, hs⟩
  exact ((key R s hmem).differentiableAt ((hopen R).mem_nhds hmem)).differentiableWithinAt

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.WeightSumAsFiniteDifferencesStatement
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_series_differentiable_left_strip : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ (B N : ℕ) (cs : List (Fin r)) (u : (Fin r → ℕ) → ℚ), Fintype.card ι * B + 2 ≤ N → BddW u →
  (∀ i, cs.count i = N ∨ ∀ m, m i ≠ 0 → u m = 0) →
  DifferentiableOn ℂ (fun s => ∑' m, (u m : ℂ) * DL cs (coneTerm a b s) m) {s | -(B : ℝ) < s.re} := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.differentiableOn_tsum_weighted_DL_halfplane | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.differentiableOn_tsum_weighted_DL_halfplane | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.differentiableOn_tsum_weighted_DL_halfplane <;> assumption)
end
