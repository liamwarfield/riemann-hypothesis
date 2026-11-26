module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDirichletLFunctionZeroGapNearOne
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqIdOfIsUnramifiedAt
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IteratedDerivLogDerivDirichletLViaNearbyZeros

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExceptionalDirichletZeroUniqueZeroFreeRegion
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExceptionalDirichletZeroUniqueZeroFreeRegion
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.ExceptionalPair

theorem one_le_log {M : ℕ} (hM : 3 ≤ M) : 1 ≤ Real.log M := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_d9]

theorem log_mul_le {M : ℕ} (hM : 3 ≤ M) {a : ℝ} (ha : 0 < a) (ha3 : a ≤ 3) :
    Real.log (a * M) ≤ 2 * Real.log M := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  rw [Real.log_mul ha.ne' hM0.ne']
  have := Real.log_le_log ha (show a ≤ (M : ℝ) by linarith)
  linarith

theorem le_log_mul {M : ℕ} (hM : 3 ≤ M) {a : ℝ} (ha : 1 ≤ a) :
    Real.log M ≤ Real.log (a * M) := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  exact Real.log_le_log hM0 (le_mul_of_one_le_left hM0.le ha)

theorem div_log_le {M : ℕ} (hM : 3 ≤ M) {c₁ c : ℝ} (h0 : 0 ≤ c) (h : c₁ ≤ c / 2) :
    c₁ / Real.log M ≤ c / Real.log (2 * M) := by
  have hl := log_mul_le hM (a := 2) (by norm_num) (by norm_num)
  have hpos : 0 < Real.log M := lt_of_lt_of_le one_pos (one_le_log hM)
  have hpos2 : 0 < Real.log (2 * M) := by
    linarith [le_log_mul hM (a := 2) (by norm_num)]
  rw [div_le_div_iff₀ hpos hpos2]
  nlinarith [mul_nonneg (sub_nonneg.2 h) hpos2.le, mul_nonneg h0 (sub_nonneg.2 hl)]

private theorem exists_ne_zero_smul_mem_of_mem_span' {a b x y : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hx : 0 < x) (hxy : x ≤ y) :
    a / y ≤ b / x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  rw [div_le_div_iff₀ hy hx]
  nlinarith [mul_le_mul_of_nonneg_right hab hx.le, mul_le_mul_of_nonneg_left hxy (ha.trans hab)]

theorem main : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₀ → ∃ c : ℝ, 0 < c ∧ ∀ (M : ℕ) [NeZero M], 3 ≤ M → (∀ (χ χ' : DirichletCharacter ℂ M) (β β' : ℝ), IsExc c₁ χ β → IsExc c₁ χ' β' → χ = χ' ∧ β = β') ∧ (∀ (χ : DirichletCharacter ℂ M) (β : ℝ), IsExc c₁ χ β → χ ≠ 1 ∧ 7 / 8 ≤ β ∧ LFunction χ β = 0 ∧ ord χ β = 1 ∧ c / ((M : ℝ) ^ 2 * Real.log M) ≤ 1 - β) ∧ ∀ (χ : DirichletCharacter ℂ M) (ρ : ℂ), ρ.re < 1 → LFunction χ ρ = 0 → (ρ.im = 0 ∧ IsExc c₁ χ ρ.re) ∨ ρ.re ≤ 1 - c / Real.log (M * (|ρ.im| + 2)) := by
  obtain ⟨cu, hcu, hU⟩ := GlobalTheory.RealZeroNearOne.main
  obtain ⟨cp, hcp, hP⟩ := GlobalTheory.ZeroFreePrincipal.zero_free
  obtain ⟨cz, hcz, hZ⟩ := GlobalTheory.ZeroFreeComplex.zero_free_region
  obtain ⟨cs, hcs, hS⟩ := GlobalTheory.T.exists_dirichletLFunction_zero_gap_near_one
  refine ⟨min (1 / 8) (min (cu / 2) (cp / 2)),
    lt_min (by norm_num) (lt_min (by linarith) (by linarith)), fun c₁ hc₁ hc₁0 => ?_⟩
  have hc18 : c₁ ≤ 1 / 8 := hc₁0.trans (min_le_left _ _)
  have hcu2 : c₁ ≤ cu / 2 := hc₁0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcp2 : c₁ ≤ cp / 2 := hc₁0.trans ((min_le_right _ _).trans (min_le_right _ _))
  set c := min c₁ (min cz (min cp (cs / 2))) with hcdef
  have hcpos : 0 < c := lt_min hc₁ (lt_min hcz (lt_min hcp (by linarith)))
  have hcc₁ : c ≤ c₁ := min_le_left _ _
  have hccz : c ≤ cz := (min_le_right _ _).trans (min_le_left _ _)
  have hccp : c ≤ cp := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hccs : c ≤ cs / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨c, hcpos, fun M _ hM => ?_⟩
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hlog1 : 1 ≤ Real.log M := one_le_log hM
  have hlogpos : 0 < Real.log M := lt_of_lt_of_le one_pos hlog1
  have hsmall : c₁ / Real.log M ≤ 1 / 8 := (div_le_self hc₁.le hlog1).trans hc18
  have hlogT : ∀ t : ℝ, 0 < Real.log (M * (|t| + 2)) := fun t =>
    Real.log_pos (by nlinarith [abs_nonneg t])
  have hexc : ∀ (χ : DirichletCharacter ℂ M) (β : ℝ), IsExc c₁ χ β →
      χ ≠ 1 ∧ 7 / 8 ≤ β ∧ LFunction χ β = 0 ∧ 1 - cu / Real.log (2 * M) ≤ β := by
    intro χ β h
    obtain ⟨_, hlt, hlt1, hL⟩ := h
    have hβ : 7 / 8 ≤ β := by linarith
    have hne : (β : ℂ) ≠ 1 := fun h => by
      have := congrArg Complex.re h
      simp at this
      linarith
    have hLχ : LFunction χ β = 0 :=
      (GlobalTheory.T.dirichletL_zeros_eq_primitiveCharacter_zeros M χ β (by simp; linarith) (Or.inr hne)).1.mpr hL
    refine ⟨fun hχ => ?_, hβ, hLχ, by linarith [div_log_le hM hcu.le hcu2]⟩
    rw [hχ] at hLχ
    have h1 := hP M (β : ℂ) hne hLχ
    have e : (M : ℝ) * 2 = 2 * M := mul_comm _ _
    rw [Complex.ofReal_re, Complex.ofReal_im, abs_zero, zero_add, e] at h1
    linarith [div_log_le hM hcp.le hcp2]
  refine ⟨fun χ χ' β β' h h' => ?_, fun χ β h => ?_, fun χ ρ hre hL => ?_⟩
  · obtain ⟨n1, -, L1, b1⟩ := hexc χ β h
    obtain ⟨n2, -, L2, b2⟩ := hexc χ' β' h'
    obtain ⟨s1, -⟩ := h
    obtain ⟨s2, -⟩ := h'
    obtain ⟨e1, e2, -⟩ := hU M χ χ' β β' n1 n2 s1 s2 b1 b2 L1 L2
    exact ⟨e1, e2⟩
  · obtain ⟨n1, h78, L1, b1⟩ := hexc χ β h
    obtain ⟨s1, -⟩ := h
    refine ⟨n1, h78, L1, ?_, ?_⟩
    · have hd := (hU M χ χ β β n1 n1 s1 s1 b1 b1 L1 L1).2.2
      have h1 := (GlobalTheory.RealZeroNearOne.analyticAt_L n1 (β : ℂ)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
        L1 hd
      rw [GlobalTheory.Lin.ord, analyticOrderNatAt, h1]
      rfl
    · have h1 := hS M χ β (Or.inl n1) L1 (by simp)
      rw [Complex.ofReal_re] at h1
      have hl3 := log_mul_le hM (a := 3) (by norm_num) le_rfl
      have hl3pos : 0 < Real.log (3 * M) := Real.log_pos (by linarith)
      have hD : 0 < (M : ℝ) ^ 2 * Real.log M := by positivity
      have hE : 0 < (M : ℝ) ^ 2 * Real.log (3 * M) := by positivity
      calc c / ((M : ℝ) ^ 2 * Real.log M) ≤ (cs / 2) / ((M : ℝ) ^ 2 * Real.log M) :=
            exists_ne_zero_smul_mem_of_mem_span' hcpos.le hccs hD le_rfl
        _ = cs / (2 * ((M : ℝ) ^ 2 * Real.log M)) := div_div cs 2 _
        _ ≤ cs / ((M : ℝ) ^ 2 * Real.log (3 * M)) :=
            exists_ne_zero_smul_mem_of_mem_span' hcs.le le_rfl hE (by nlinarith [sq_nonneg (M : ℝ)])
        _ ≤ 1 - β := h1
  · by_cases hreal : χ ^ 2 = 1 ∧ ρ.im = 0
    · obtain ⟨hsq, him⟩ := hreal
      have hρ : ρ = (ρ.re : ℂ) := Complex.ext (by simp) (by simp [him])
      by_cases hbig : 1 - c₁ / Real.log M < ρ.re
      · left
        refine ⟨him, ?_⟩
        have hpos : 0 < ρ.re := by linarith
        have hne : ρ ≠ 1 := fun h => by
          rw [h] at hre
          simp at hre
        have hL' := (GlobalTheory.T.dirichletL_zeros_eq_primitiveCharacter_zeros M χ ρ hpos (Or.inr hne)).1.mp hL
        unfold IsExc
        refine ⟨hsq, hbig, hre, ?_⟩
        rw [← hρ]
        exact hL'
      · right
        replace hbig := not_lt.mp hbig
        rw [him, abs_zero, zero_add]
        have h2 : Real.log M ≤ Real.log (M * 2) := by
          rw [mul_comm]
          exact le_log_mul hM (by norm_num)
        have := exists_ne_zero_smul_mem_of_mem_span' hcpos.le hcc₁ hlogpos h2
        linarith
    · right
      have hne' : χ ^ 2 = 1 → ρ.im ≠ 0 := fun h h' => hreal ⟨h, h'⟩
      by_cases hχ : χ = 1
      · have him : ρ.im ≠ 0 := hne' (by rw [hχ]; exact one_pow 2)
        have hne : ρ ≠ 1 := fun h => him (by rw [h]; simp)
        rw [hχ] at hL
        have h1 := hP M ρ hne hL
        have := exists_ne_zero_smul_mem_of_mem_span' hcpos.le hccp (hlogT ρ.im) le_rfl
        linarith
      · have hor : χ ^ 2 ≠ 1 ∨ ρ.im ≠ 0 := by
          by_cases h : χ ^ 2 = 1
          · exact Or.inr (hne' h)
          · exact Or.inl h
        have h1 := hZ M χ ρ hχ hL hor
        have := exists_ne_zero_smul_mem_of_mem_span' hcpos.le hccz (hlogT ρ.im) le_rfl
        linarith

end GlobalTheory.ExceptionalPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExceptionalDirichletZeroUniqueZeroFreeRegionStatement
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exceptionalDirichletZero_unique_zeroFreeRegion : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₀ → ∃ c : ℝ, 0 < c ∧ ∀ (M : ℕ) [NeZero M], 3 ≤ M → (∀ (χ χ' : DirichletCharacter ℂ M) (β β' : ℝ), IsExc c₁ χ β → IsExc c₁ χ' β' → χ = χ' ∧ β = β') ∧ (∀ (χ : DirichletCharacter ℂ M) (β : ℝ), IsExc c₁ χ β → χ ≠ 1 ∧ 7 / 8 ≤ β ∧ LFunction χ β = 0 ∧ ord χ β = 1 ∧ c / ((M : ℝ) ^ 2 * Real.log M) ≤ 1 - β) ∧ ∀ (χ : DirichletCharacter ℂ M) (ρ : ℂ), ρ.re < 1 → LFunction χ ρ = 0 → (ρ.im = 0 ∧ IsExc c₁ χ ρ.re) ∨ ρ.re ≤ 1 - c / Real.log (M * (|ρ.im| + 2)) := by
  first | exact @GlobalTheory.ExceptionalPair.main | exact GlobalTheory.ExceptionalPair.main | (intros; apply GlobalTheory.ExceptionalPair.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionFamilyLogDerivPositivity
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionFamilyLogDerivPositivity
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk.LFamPos

theorem norm_lamChi_le (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (n : ℕ) : ‖𝓕.lamChi χ n‖ ≤ 2 * Λ n := by
  refine le_trans ?_ (𝓕.lam_le n)
  unfold LFam.lamChi
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun g _ => ?_)
  rw [norm_mul, AddChar.norm_apply, one_mul, Complex.norm_real, Real.norm_of_nonneg (𝓕.lam_nonneg g n)]

theorem summable_lamChi (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (𝓕.lamChi χ) s := by
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).smul (2 : ℂ)
  refine Summable.of_norm_bounded h.norm fun n => ?_
  refine LSeries.norm_term_le s ?_
  refine (norm_lamChi_le 𝓕 χ n).trans (le_of_eq ?_)
  simp [abs_of_nonneg vonMangoldt_nonneg]

theorem hasSum_re (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (σ : ℝ) (u : ℂ) (hs : 1 < σ) (hu : u.re = 0) :
    HasSum (fun n : ℕ => ∑ g, (if n = 0 then 0 else 𝓕.lam g n * (n : ℝ) ^ (-σ)) * (χ g * (n : ℂ) ^ (-u)).re)
      (LSeries (𝓕.lamChi χ) (σ + u)).re := by
  have h := (summable_lamChi 𝓕 χ (s := σ + u) (by simpa [hu] using hs)).hasSum
  have h2 := Complex.hasSum_re h
  convert h2 using 2 with n
  · by_cases hn : n = 0
    · simp [hn]
    · have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      rw [LSeries.term_of_ne_zero hn, LFam.lamChi, Finset.sum_div, Complex.re_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [if_neg hn, ← Complex.re_ofReal_mul]
      congr 1
      rw [div_eq_mul_inv, ← cpow_neg, neg_add, cpow_add _ _ hn']
      push_cast
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
      push_cast
      ring
  · rfl

theorem hasSum_re₀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (σ : ℝ) (hs : 1 < σ) :
    HasSum (fun n : ℕ => ∑ g, (if n = 0 then 0 else 𝓕.lam g n * (n : ℝ) ^ (-σ)) * (χ g).re)
      (LSeries (𝓕.lamChi χ) σ).re := by
  simpa using hasSum_re 𝓕 χ σ 0 hs rfl

theorem w_nonneg (𝓕 : LFam) (σ : ℝ) (n : ℕ) (g : 𝓕.G) :
    0 ≤ (if n = 0 then 0 else 𝓕.lam g n * (n : ℝ) ^ (-σ)) := by
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (𝓕.lam_nonneg g n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem pm_one {G : Type} [AddCommGroup G] (χ : AddChar G ℂ) (h : χ * χ = 1) (g : G) :
    χ g = 1 ∨ χ g = -1 := by
  have : χ g * χ g = 1 := by
    have := congrArg (fun φ : AddChar G ℂ => φ g) h
    simpa using this
  exact mul_self_eq_one_iff.mp this

theorem trig (z : ℂ) (hz : ‖z‖ = 1) : 0 ≤ 3 + 4 * z.re + (z * z).re := by
  have h : z.re * z.re + z.im * z.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hz]; norm_num
  rw [Complex.mul_re]
  nlinarith [sq_nonneg (z.re + 1)]

theorem positivity : ∀ (𝓕 : LFam) (χ ψ : AddChar 𝓕.G ℂ) (σ t : ℝ), 1 < σ → 0 ≤ 3 * (LSeries (𝓕.lamChi 1) σ).re + 4 * (LSeries (𝓕.lamChi χ) (σ + t * I)).re + (LSeries (𝓕.lamChi (χ * χ)) (σ + 2 * t * I)).re ∧ 0 ≤ (LSeries (𝓕.lamChi 1) σ).re ∧ (χ * χ = 1 → ψ * ψ = 1 → 0 ≤ (LSeries (𝓕.lamChi 1) σ).re + (LSeries (𝓕.lamChi χ) σ).re ∧ 0 ≤ (LSeries (𝓕.lamChi 1) σ).re + (LSeries (𝓕.lamChi χ) σ).re + (LSeries (𝓕.lamChi ψ) σ).re + (LSeries (𝓕.lamChi (χ * ψ)) σ).re) := by
  intro 𝓕 χ ψ σ t hσ
  have h1 := hasSum_re₀ 𝓕 1 σ hσ
  refine ⟨?_, ?_, fun hχ hψ => ⟨?_, ?_⟩⟩
  · have h2 := hasSum_re 𝓕 χ σ (t * I) hσ (by simp)
    have h3 := hasSum_re 𝓕 (χ * χ) σ (2 * t * I) hσ (by simp)
    refine HasSum.nonneg (fun n => ?_) (((h1.mul_left 3).add (h2.mul_left 4)).add h3)
    by_cases hn : n = 0
    · simp [hn]
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_nonneg fun g _ => ?_
    have hz : ‖χ g * (n : ℂ) ^ (-(t * I))‖ = 1 := by
      rw [norm_mul, AddChar.norm_apply, one_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp
    have ht := trig _ hz
    have he : (χ * χ) g * (n : ℂ) ^ (-(2 * t * I)) = (χ g * (n : ℂ) ^ (-(t * I))) * (χ g * (n : ℂ) ^ (-(t * I))) := by
      rw [show -(2 * (t : ℂ) * I) = -(t * I) + -(t * I) by ring, cpow_add _ _ hn', AddChar.mul_apply]
      ring
    rw [he, AddChar.one_apply, Complex.one_re]
    have := mul_nonneg (w_nonneg 𝓕 σ n g) ht
    linarith
  · refine HasSum.nonneg (fun n => Finset.sum_nonneg fun g _ => ?_) h1
    rw [AddChar.one_apply, Complex.one_re, mul_one]
    exact w_nonneg 𝓕 σ n g
  · refine HasSum.nonneg (fun n => ?_) (h1.add (hasSum_re₀ 𝓕 χ σ hσ))
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_nonneg fun g _ => ?_
    have hw := w_nonneg 𝓕 σ n g
    rw [AddChar.one_apply]
    rcases pm_one χ hχ g with h | h <;> rw [h] <;> simp only [one_re, neg_re] <;> linarith
  · refine HasSum.nonneg (fun n => ?_) (((h1.add (hasSum_re₀ 𝓕 χ σ hσ)).add (hasSum_re₀ 𝓕 ψ σ hσ)).add (hasSum_re₀ 𝓕 (χ * ψ) σ hσ))
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_nonneg fun g _ => ?_
    have hw := w_nonneg 𝓕 σ n g
    rw [AddChar.one_apply, AddChar.mul_apply]
    rcases pm_one χ hχ g with h | h <;> rcases pm_one ψ hψ g with h' | h' <;> rw [h, h'] <;>
      simp only [one_re, neg_re, mul_one, mul_neg, neg_neg] <;> linarith

end GlobalTheory.Hk.LFamPos
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionFamilyLogDerivPositivityStatement
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity : ∀ (𝓕 : LFam) (χ ψ : AddChar 𝓕.G ℂ) (σ t : ℝ), 1 < σ → 0 ≤ 3 * (LSeries (𝓕.lamChi 1) σ).re + 4 * (LSeries (𝓕.lamChi χ) (σ + t * I)).re + (LSeries (𝓕.lamChi (χ * χ)) (σ + 2 * t * I)).re ∧ 0 ≤ (LSeries (𝓕.lamChi 1) σ).re ∧ (χ * χ = 1 → ψ * ψ = 1 → 0 ≤ (LSeries (𝓕.lamChi 1) σ).re + (LSeries (𝓕.lamChi χ) σ).re ∧ 0 ≤ (LSeries (𝓕.lamChi 1) σ).re + (LSeries (𝓕.lamChi χ) σ).re + (LSeries (𝓕.lamChi ψ) σ).re + (LSeries (𝓕.lamChi (χ * ψ)) σ).re) := by
  first | exact @GlobalTheory.Hk.LFamPos.positivity | exact GlobalTheory.Hk.LFamPos.positivity | (intros; apply GlobalTheory.Hk.LFamPos.positivity <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DirichletLFewZerosSmallDisc
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DirichletLFewZerosSmallDisc
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.SmallDiscZeros

private lemma derSeries_one_eq_tsum_vonMangoldt (σ : ℝ) :
    _root_.GlobalTheory.Lin.derSeries (fun n ↦ (1 : DirichletCharacter ℂ 1) n) 0 ((σ : ℂ) + (0 : ℝ) * I) =
      ((∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  unfold _root_.GlobalTheory.Lin.derSeries
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n ↦ ?_
  dsimp only
  rw [MulChar.one_apply (isUnit_of_subsingleton _)]
  push_cast
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
  simp

private lemma re_natCast_div_pow_zero_add_one (m : ℕ) (z : ℂ) :
    ((m : ℂ) / z ^ (0 + 1)).re = m * (z⁻¹).re := by
  rw [zero_add, pow_one, div_eq_mul_inv, ← Complex.ofReal_natCast, Complex.re_ofReal_mul]

private lemma re_lt_one_of_mem_zerosDisc {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {c w : ℂ}
    {R : ℝ} (hw : w ∈ _root_.GlobalTheory.Lin.zerosDisc χ c R) : w.re < 1 := by
  simp only [_root_.GlobalTheory.Lin.zerosDisc, Set.mem_setOf_eq] at hw
  obtain ⟨-, h1, h0⟩ := hw
  by_contra h
  exact LFunction_ne_zero_of_one_le_re χ h1 (not_lt.mp h) h0

private lemma inv_re_nonneg_of_re_nonneg {z : ℂ} (h : 0 ≤ z.re) : 0 ≤ (z⁻¹).re := by
  rw [Complex.inv_re]
  exact div_nonneg h (Complex.normSq_nonneg _)

private lemma summable_vonMangoldt_mul_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ ↦ vonMangoldt n * (n : ℝ) ^ (-σ) := by
  have h := LSeriesSummable_vonMangoldt (s := (σ : ℂ)) (by simpa using hσ)
  have h' : Summable fun n ↦ ‖LSeries.term (fun n ↦ (vonMangoldt n : ℂ)) (σ : ℂ) n‖ :=
    summable_norm_iff.mpr h
  refine h'.congr fun n ↦ ?_
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg,
      Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

private lemma norm_derSeries_le_tsum_vonMangoldt {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    ‖_root_.GlobalTheory.Lin.derSeries (fun n ↦ χ n) 0 s‖ ≤
      ∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-s.re) := by
  unfold _root_.GlobalTheory.Lin.derSeries
  refine tsum_of_norm_bounded (summable_vonMangoldt_mul_rpow_neg hs).hasSum fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
    rw [norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
      Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg, Complex.neg_re]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right vonMangoldt_nonneg (DirichletCharacter.norm_le_one χ _))
      (by positivity)

private lemma inv_re_ge_of_norm_sub_le {t r : ℝ} {w : ℂ} (hr : 0 < r) (hw : ‖w - (1 + t * I)‖ ≤ r)
    (hre : w.re < 1) : 1 / (4 * r) ≤ ((((1 + r : ℝ) : ℂ) + t * I - w)⁻¹).re := by
  set z : ℂ := ((1 + r : ℝ) : ℂ) + t * I - w with hz
  have hzre : z.re = 1 + r - w.re := by simp [hz]
  have hzre' : r < z.re := by linarith
  have hznorm : ‖z‖ ≤ 2 * r := by
    have hz' : z = (r : ℂ) - (w - (1 + t * I)) := by rw [hz]; push_cast; ring
    rw [hz']
    calc ‖(r : ℂ) - (w - (1 + t * I))‖ ≤ ‖(r : ℂ)‖ + ‖w - (1 + t * I)‖ := norm_sub_le _ _
      _ ≤ r + r := by rw [Complex.norm_real, Real.norm_of_nonneg hr.le]; linarith
      _ = 2 * r := by ring
  have hpos : 0 < Complex.normSq z := by
    refine Complex.normSq_pos.mpr fun h ↦ ?_
    rw [h, Complex.zero_re] at hzre'
    linarith
  rw [Complex.inv_re, div_le_div_iff₀ (by positivity) hpos, Complex.normSq_eq_norm_sq]
  nlinarith [mul_le_mul hznorm hznorm (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 2 * r)]

theorem _root_.GlobalTheory.SmallDiscZeros.few_zeros : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t r : ℝ), (χ ≠ 1 ∨ 2 ≤ |t|) → 0 < r → r ≤ 1 / 2 → (_root_.GlobalTheory.Lin.zerosDisc χ (1 + t * I) r).Finite ∧ (∑ᶠ w ∈ _root_.GlobalTheory.Lin.zerosDisc χ (1 + t * I) r, (_root_.GlobalTheory.Lin.ord χ w : ℝ)) ≤ C * (1 + r * Real.log (q * (|t| + 2))) := by
  obtain ⟨C, hC, hmain⟩ := _root_.GlobalTheory.LogDerivHigher.main
  refine ⟨6 + 4 * C, by positivity, ?_⟩
  intro q _ χ t r hχt hr hr2
  have hσ1 : 1 < 1 + r := by linarith
  have hσ2 : 1 + r ≤ 2 := by linarith
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hL0 : 0 ≤ Real.log (q * (|t| + 2)) :=
    Real.log_nonneg (by nlinarith [abs_nonneg t])
  have hTS : _root_.GlobalTheory.Lin.zerosDisc χ (1 + t * I) r ⊆ _root_.GlobalTheory.Lin.zerosDisc χ (2 + t * I) 3 := by
    intro w hw
    simp only [_root_.GlobalTheory.Lin.zerosDisc, Set.mem_setOf_eq] at hw ⊢
    refine ⟨?_, hw.2⟩
    calc ‖w - (2 + t * I)‖ = ‖(w - (1 + t * I)) - 1‖ := by ring_nf
      _ ≤ ‖w - (1 + t * I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 3 := by rw [norm_one]; linarith [hw.1]
  obtain ⟨hfin, -, hbound⟩ := hmain q χ (1 + r) t 0 hσ1 hσ2
  obtain ⟨hfin₁, -, hbound₁⟩ := hmain 1 1 (1 + r) 0 0 hσ1 hσ2
  have hTfin := hfin.subset hTS
  refine ⟨hTfin, ?_⟩
  set G : ℝ := ∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-(1 + r)) with hG
  have hG_le : G ≤ 1 / r + C := by
    rw [derSeries_one_eq_tsum_vonMangoldt, if_pos rfl] at hbound₁
    have hP : (1 : ℂ) / (((1 + r : ℝ) : ℂ) + (0 : ℝ) * I - 1) ^ (0 + 1) = ((1 / r : ℝ) : ℂ) := by
      push_cast; ring
    rw [hP] at hbound₁
    have hZ₁ : 0 ≤ (∑ᶠ w ∈ _root_.GlobalTheory.Lin.zerosDisc (1 : DirichletCharacter ℂ 1) (2 + (0 : ℝ) * I) 3,
        ((_root_.GlobalTheory.Lin.ord (1 : DirichletCharacter ℂ 1) w : ℕ) : ℂ) /
          (((1 + r : ℝ) : ℂ) + (0 : ℝ) * I - w) ^ (0 + 1)).re := by
      rw [finsum_mem_eq_finite_toFinset_sum _ hfin₁, Complex.re_sum]
      refine Finset.sum_nonneg fun w hw ↦ ?_
      rw [re_natCast_div_pow_zero_add_one]
      have hw' := re_lt_one_of_mem_zerosDisc ((Set.Finite.mem_toFinset hfin₁).mp hw)
      refine mul_nonneg (Nat.cast_nonneg _) (inv_re_nonneg_of_re_nonneg ?_)
      simp
      linarith
    have hre := (Complex.re_le_norm _).trans hbound₁
    rw [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re] at hre
    have hlog : Real.log ((1 : ℕ) * (|(0 : ℝ)| + 2)) ≤ 1 := by
      norm_num
      linarith [Real.log_two_lt_d9]
    have hCl : C * Real.log ((1 : ℕ) * (|(0 : ℝ)| + 2)) / (1 + r) ^ 0 ≤ C := by
      rw [pow_zero, div_one]
      nlinarith
    linarith
  have key : ∀ (X Y W : ℂ) (B : ℝ), ‖(X - Y) + W‖ ≤ B → ‖W‖ ≤ B + ‖X‖ + ‖Y‖ := by
    intro X Y W B h
    have hW : W = ((X - Y) + W) - X + Y := by ring
    rw [hW]
    calc ‖((X - Y) + W) - X + Y‖ ≤ ‖(X - Y) + W‖ + ‖X‖ + ‖Y‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ B + ‖X‖ + ‖Y‖ := by linarith
  have hZnorm := key _ _ _ _ hbound
  rw [pow_zero, div_one] at hZnorm
  have hre : (((1 + r : ℝ) : ℂ) + t * I).re = 1 + r := by simp
  have hA := norm_derSeries_le_tsum_vonMangoldt χ (s := ((1 + r : ℝ) : ℂ) + t * I) (by rw [hre]; exact hσ1)
  rw [hre] at hA
  have hZn : ‖∑ᶠ w ∈ _root_.GlobalTheory.Lin.zerosDisc χ (2 + t * I) 3,
      ((_root_.GlobalTheory.Lin.ord χ w : ℕ) : ℂ) / (((1 + r : ℝ) : ℂ) + t * I - w) ^ (0 + 1)‖ ≤
      C * Real.log (q * (|t| + 2)) + G + 1 := by
    split_ifs at hZnorm with h1
    · have ht : 2 ≤ |t| := hχt.resolve_left (not_not.mpr h1)
      have him : |t| ≤ ‖((1 + r : ℝ) : ℂ) + t * I - 1‖ := by
        have := Complex.abs_im_le_norm (((1 + r : ℝ) : ℂ) + t * I - 1)
        simpa using this
      have hY : ‖(1 : ℂ) / (((1 + r : ℝ) : ℂ) + t * I - 1) ^ (0 + 1)‖ ≤ 1 := by
        rw [zero_add, pow_one, norm_div, norm_one, div_le_one (by linarith)]
        linarith
      linarith
    · rw [norm_zero] at hZnorm
      linarith
  have hZre : (∑ᶠ w ∈ _root_.GlobalTheory.Lin.zerosDisc χ (1 + t * I) r, (_root_.GlobalTheory.Lin.ord χ w : ℝ)) *
      (1 / (4 * r)) ≤ (∑ᶠ w ∈ _root_.GlobalTheory.Lin.zerosDisc χ (2 + t * I) 3,
      ((_root_.GlobalTheory.Lin.ord χ w : ℕ) : ℂ) / (((1 + r : ℝ) : ℂ) + t * I - w) ^ (0 + 1)).re := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hTfin, Finset.sum_mul,
      finsum_mem_eq_finite_toFinset_sum _ hfin, Complex.re_sum]
    refine (Finset.sum_le_sum fun w hw ↦ ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Set.Finite.toFinset_subset_toFinset.mpr hTS)
        fun w hw _ ↦ ?_)
    · rw [re_natCast_div_pow_zero_add_one]
      have hw' := (Set.Finite.mem_toFinset hTfin).mp hw
      refine mul_le_mul_of_nonneg_left (inv_re_ge_of_norm_sub_le hr ?_ (re_lt_one_of_mem_zerosDisc hw'))
        (Nat.cast_nonneg _)
      simp only [_root_.GlobalTheory.Lin.zerosDisc, Set.mem_setOf_eq] at hw'
      exact hw'.1
    · rw [re_natCast_div_pow_zero_add_one]
      have hw' := re_lt_one_of_mem_zerosDisc ((Set.Finite.mem_toFinset hfin).mp hw)
      refine mul_nonneg (Nat.cast_nonneg _) (inv_re_nonneg_of_re_nonneg ?_)
      simp
      linarith
  set N := ∑ᶠ w ∈ _root_.GlobalTheory.Lin.zerosDisc χ (1 + t * I) r, (_root_.GlobalTheory.Lin.ord χ w : ℝ) with hN
  set L := Real.log (q * (|t| + 2)) with hL
  have h1 : N * (1 / (4 * r)) ≤ C * L + G + 1 := hZre.trans ((Complex.re_le_norm _).trans hZn)
  have h2 : N ≤ 4 * r * (C * L + G + 1) := by
    have h4 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 4 * r)
    have e : 4 * r * (N * (1 / (4 * r))) = N := by field_simp
    linarith
  have h3 : 4 * r * (C * L + G + 1) ≤ 4 * (C * (r * L)) + 4 + 4 * r * (C + 1) := by
    have e : 4 * r * (1 / r) = 4 := by field_simp
    have h5 := mul_le_mul_of_nonneg_left hG_le (by positivity : (0 : ℝ) ≤ 4 * r)
    nlinarith
  have hrL : 0 ≤ r * L := by positivity
  have h6 := mul_le_mul_of_nonneg_right hr2 (by positivity : (0 : ℝ) ≤ C + 1)
  nlinarith [mul_nonneg hC.le hrL]

end GlobalTheory.SmallDiscZeros
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DirichletLFewZerosSmallDiscStatement
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dirichletL_few_zeros_small_disc : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t r : ℝ), (χ ≠ 1 ∨ 2 ≤ |t|) → 0 < r → r ≤ 1 / 2 → (zerosDisc χ (1 + t * I) r).Finite ∧ (∑ᶠ w ∈ zerosDisc χ (1 + t * I) r, (ord χ w : ℝ)) ≤ C * (1 + r * Real.log (q * (|t| + 2))) := by
  first | exact @GlobalTheory.SmallDiscZeros.few_zeros | exact GlobalTheory.SmallDiscZeros.few_zeros | (intros; apply GlobalTheory.SmallDiscZeros.few_zeros <;> assumption)
end
end
