module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsPolynomialSubMem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUnitPowSubOne
noncomputable section

open Filter Topology

namespace GlobalTheory.PadicLogUnits

variable {l : ℕ} [hl : Fact l.Prime]

def term (y : ℚ_[l]) (k : ℕ) : ℚ_[l] := (-1 : ℚ_[l]) ^ k * y ^ (k + 1) / ((k : ℚ_[l]) + 1)

def lg (x : ℚ_[l]) : ℚ_[l] := ∑' k : ℕ, term (x - 1) k

lemma inv_norm_succ_le (k : ℕ) : ‖((k : ℚ_[l]) + 1)‖⁻¹ ≤ 2 ^ k := by
  have h0 : ((k + 1 : ℕ) : ℚ_[l]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have h1 : ((k : ℚ_[l]) + 1) = ((k + 1 : ℕ) : ℚ_[l]) := by push_cast; rfl
  rw [h1, Padic.norm_eq_zpow_neg_valuation h0, Padic.valuation_natCast, zpow_neg, inv_inv,
    zpow_natCast]
  have h2 : l ^ padicValNat l (k + 1) ≤ k + 1 := Nat.le_of_dvd (Nat.succ_pos k) (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  rw [Nat.padicValNat_def] at h2
  have h3 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  exact_mod_cast h2.trans h3

lemma norm_pow_div_le {y : ℚ_[l]} (hy : ‖y‖ ≤ 1 / 3) (k : ℕ) :
    ‖y ^ (k + 1) / ((k : ℚ_[l]) + 1)‖ ≤ ‖y‖ * (2 / 3) ^ k := by
  rw [norm_div, norm_pow, div_eq_mul_inv, pow_succ']
  have h1 : ‖y‖ ^ k ≤ (1 / 3) ^ k := pow_le_pow_left₀ (norm_nonneg _) hy k
  calc ‖y‖ * ‖y‖ ^ k * ‖((k : ℚ_[l]) + 1)‖⁻¹ ≤ ‖y‖ * (1 / 3) ^ k * 2 ^ k := by
        gcongr
        exact inv_norm_succ_le k
    _ = ‖y‖ * (2 / 3) ^ k := by rw [mul_assoc, ← mul_pow]; norm_num

lemma norm_term_le {y : ℚ_[l]} (hy : ‖y‖ ≤ 1 / 3) (k : ℕ) :
    ‖term y k‖ ≤ ‖y‖ * (2 / 3) ^ k := by
  rw [term, mul_div_assoc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact norm_pow_div_le hy k

lemma summable_geo (c : ℝ) : Summable fun k : ℕ => c * (2 / 3 : ℝ) ^ k :=
  (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left c

lemma summable_term {y : ℚ_[l]} (hy : ‖y‖ ≤ 1 / 3) : Summable (term y) :=
  Summable.of_norm_bounded (summable_geo ‖y‖) (norm_term_le hy)

lemma norm_lg {x : ℚ_[l]} (hx : ‖x - 1‖ ≤ 1 / 3) : ‖lg x‖ = ‖x - 1‖ := by
  rcases eq_or_ne (x - 1) 0 with h | h
  · simp [lg, h, term]
  have hpos : 0 < ‖x - 1‖ := norm_pos_iff.mpr h
  rw [lg, (summable_term hx).tsum_eq_zero_add]
  have h0 : term (x - 1) 0 = x - 1 := by simp [term]
  have h1 : ‖∑' k : ℕ, term (x - 1) (k + 1)‖ ≤ ‖x - 1‖ * (2 / 3) := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun k => ?_
    refine (norm_term_le hx (k + 1)).trans ?_
    gcongr
    exact pow_le_of_le_one (by norm_num) (by norm_num) (Nat.succ_ne_zero k)
  have h2 : ‖∑' k : ℕ, term (x - 1) (k + 1)‖ < ‖x - 1‖ := by linarith
  rw [h0, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h2.ne', max_eq_left h2.le]

lemma desc_eval_neg_one (k : ℕ) :
    (descPochhammer ℚ_[l] k).eval (-1) = (-1) ^ k * (k.factorial : ℚ_[l]) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [descPochhammer_succ_eval, ih, Nat.factorial_succ]
    push_cast
    ring

lemma tendsto_pow_zero : Tendsto (fun n : ℕ => (l : ℚ_[l]) ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one

lemma tendsto_choose (k : ℕ) :
    Tendsto (fun n : ℕ => (((l ^ n - 1).choose k : ℕ) : ℚ_[l])) atTop (𝓝 ((-1) ^ k)) := by
  have hk : (k.factorial : ℚ_[l]) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have h1 : Tendsto (fun n : ℕ => (l : ℚ_[l]) ^ n - 1) atTop (𝓝 (-1)) := by
    simpa using (tendsto_pow_zero (l := l)).sub_const 1
  have h2 := (((descPochhammer ℚ_[l] k).continuous.tendsto (-1)).comp h1).div_const
    (k.factorial : ℚ_[l])
  rw [desc_eval_neg_one, mul_div_cancel_right₀ _ hk] at h2
  refine h2.congr fun n => ?_
  rw [Nat.cast_choose_eq_descPochhammer_div, Nat.cast_sub (Nat.one_le_pow _ _ hl.out.pos)]
  simp

lemma pow_sub_one_div (y : ℚ_[l]) (M : ℕ) :
    ((1 + y) ^ (M + 1) - 1) / ((M + 1 : ℕ) : ℚ_[l]) =
      ∑' k : ℕ, ((M.choose k : ℕ) : ℚ_[l]) * (y ^ (k + 1) / ((k : ℚ_[l]) + 1)) := by
  have h0 : ((M + 1 : ℕ) : ℚ_[l]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero M
  rw [tsum_eq_sum (s := Finset.range (M + 1))
    (fun k hk => by rw [Nat.choose_eq_zero_of_lt (by simpa using hk)]; simp)]
  rw [add_comm 1 y, add_pow, Finset.sum_range_succ', div_eq_iff h0, Finset.sum_mul]
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : ((k : ℚ_[l]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have h := congrArg (Nat.cast : ℕ → ℚ_[l]) (Nat.add_one_mul_choose_eq M k)
  push_cast at h ⊢
  field_simp
  linear_combination (-(y ^ (k + 1))) * h

lemma tendsto_lg {x : ℚ_[l]} (hx : ‖x - 1‖ ≤ 1 / 3) :
    Tendsto (fun n : ℕ => (x ^ (l ^ n) - 1) / (l : ℚ_[l]) ^ n) atTop (𝓝 (lg x)) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (n k : ℕ) => (((l ^ n - 1).choose k : ℕ) : ℚ_[l]) *
      ((x - 1) ^ (k + 1) / ((k : ℚ_[l]) + 1))) (g := term (x - 1))
    (summable_geo ‖x - 1‖) (fun k => by
      rw [term, mul_div_assoc]; exact (tendsto_choose k).mul_const _)
    (Eventually.of_forall fun n k => by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)).trans
        (norm_pow_div_le hx k))
  refine h.congr fun n => ?_
  rw [← pow_sub_one_div, Nat.sub_add_cancel (Nat.one_le_pow _ _ hl.out.pos)]
  simp

lemma norm_mul_sub_one {x w : ℚ_[l]} (hx : ‖x - 1‖ ≤ 1 / 3) (hw : ‖w - 1‖ ≤ 1 / 3) :
    ‖x * w - 1‖ ≤ 1 / 3 := by
  have : x * w - 1 = (x - 1) * (w - 1) + (x - 1) + (w - 1) := by ring
  rw [this]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hw)
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hx)
  rw [norm_mul]
  nlinarith [norm_nonneg (x - 1), norm_nonneg (w - 1)]

lemma lg_mul {x w : ℚ_[l]} (hx : ‖x - 1‖ ≤ 1 / 3) (hw : ‖w - 1‖ ≤ 1 / 3) :
    lg (x * w) = lg x + lg w := by
  have h := ((tendsto_lg hx).add (tendsto_lg hw)).add
    (tendsto_pow_zero.mul ((tendsto_lg hx).mul (tendsto_lg hw)))
  rw [zero_mul, add_zero] at h
  refine tendsto_nhds_unique (tendsto_lg (norm_mul_sub_one hx hw)) (h.congr fun n => ?_)
  have h0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  rw [mul_pow]
  field_simp
  ring

lemma lg_pow {x : ℚ_[l]} (hx : ‖x - 1‖ ≤ 1 / 3) (m : ℕ) :
    ‖x ^ m - 1‖ ≤ 1 / 3 ∧ lg (x ^ m) = m * lg x := by
  induction m with
  | zero => simp [lg, term]
  | succ m ih =>
    rw [pow_succ]
    refine ⟨norm_mul_sub_one ih.1 hx, ?_⟩
    rw [lg_mul ih.1 hx, ih.2]
    push_cast
    ring

lemma continuousOn_lg : ContinuousOn (lg (l := l)) {x | ‖x - 1‖ ≤ 1 / 3} := by
  refine continuousOn_tsum (fun k => ?_) (summable_geo (1 / 3)) (fun k x hx => ?_)
  · unfold term
    fun_prop
  · refine (norm_term_le hx k).trans ?_
    gcongr
    exact hx

lemma norm_unit_pow_sub_one {u : ℚ_[l]} (hu : ‖u‖ = 1) :
    ‖u ^ (l * (l - 1)) - 1‖ ≤ (l : ℝ) ^ (-(2 : ℕ) : ℤ) := by
  let z : ℤ_[l] := ⟨u, hu.le⟩
  have hz : IsUnit z := PadicInt.isUnit_iff.mpr hu
  obtain ⟨v, hv⟩ := hz.map (PadicInt.toZModPow (p := l) 2)
  have h1 := ZMod.pow_totient v
  rw [Nat.totient_prime_pow hl.out (by norm_num)] at h1
  have h2 : z ^ (l * (l - 1)) - 1 ∈ RingHom.ker (PadicInt.toZModPow (p := l) 2) := by
    rw [RingHom.mem_ker, RingHom.map_sub, map_pow, map_one, ← hv, ← Units.val_pow_eq_pow_val]
    simp only [Nat.add_one_sub_one, pow_one] at h1
    rw [h1]
    simp
  rw [PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow] at h2
  exact h2

lemma zpow_le_third {j : ℕ} (h1 : 1 ≤ j) (h2 : l = 2 → 2 ≤ j) :
    (l : ℝ) ^ (-(j : ℤ)) ≤ 1 / 3 := by
  have h3 : 3 ≤ l ^ j := by
    by_cases h : l = 2
    · subst h
      exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (h2 rfl))
    · have := hl.out.two_le
      calc 3 ≤ l ^ 1 := by rw [pow_one]; omega
        _ ≤ l ^ j := Nat.pow_le_pow_right hl.out.pos h1
  rw [zpow_neg, zpow_natCast, one_div]
  exact inv_anti₀ (by norm_num) (by exact_mod_cast h3)

lemma norm_unit_pow_sub_one' {u : ℚ_[l]} (hu : ‖u‖ = 1) : ‖u ^ (l * (l - 1)) - 1‖ ≤ 1 / 3 :=
  (norm_unit_pow_sub_one hu).trans (zpow_le_third (by norm_num) fun _ => le_rfl)

lemma logZl_eq (u : ℚ_[l]) :
    Formalism.MainNotions.LocalSituation.logZl l u = lg (u ^ (l * (l - 1))) / ((l : ℚ_[l]) * ((l : ℚ_[l]) - 1)) := rfl

lemma norm_sub_one : ‖(l : ℚ_[l]) - 1‖ = 1 := by
  have h : ‖(l : ℚ_[l])‖ < ‖(-1 : ℚ_[l])‖ := by
    simpa using Padic.norm_p_lt_one (p := l)
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne, max_eq_right h.le]
  simp

theorem logZl_hom : ∀ (l : ℕ) [Fact l.Prime],
    (∀ u w : ℚ_[l], ‖u‖ = 1 → ‖w‖ = 1 →
      Formalism.MainNotions.LocalSituation.logZl l (u * w) = Formalism.MainNotions.LocalSituation.logZl l u + Formalism.MainNotions.LocalSituation.logZl l w) ∧
    ContinuousOn (Formalism.MainNotions.LocalSituation.logZl l) {u | ‖u‖ = 1} ∧
    (∀ u : ℚ_[l], ‖u‖ = 1 → ‖Formalism.MainNotions.LocalSituation.logZl l u‖ ≤ 1) ∧
    ∀ j : ℕ, 1 ≤ j → (l = 2 → 2 ≤ j) → ∀ u : ℚ_[l], ‖u - 1‖ ≤ (l : ℝ) ^ (-(j : ℤ)) →
      ‖Formalism.MainNotions.LocalSituation.logZl l u‖ = ‖u - 1‖ := by
  intro l hl
  refine ⟨fun u w hu hw => ?_, ?_, fun u hu => ?_, fun j h1 h2 u hu => ?_⟩
  · rw [logZl_eq, logZl_eq, logZl_eq, mul_pow,
      lg_mul (norm_unit_pow_sub_one' hu) (norm_unit_pow_sub_one' hw), add_div]
  · exact (continuousOn_lg.comp (continuous_pow (l * (l - 1))).continuousOn
      fun u hu => norm_unit_pow_sub_one' hu).div_const _
  · have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl.out.one_le
    rw [logZl_eq, norm_div, norm_lg (norm_unit_pow_sub_one' hu), norm_mul, norm_sub_one,
      mul_one, Padic.norm_p, div_le_one (by positivity)]
    refine (norm_unit_pow_sub_one hu).trans ?_
    rw [← zpow_neg_one]
    exact zpow_le_zpow_right₀ hl1 (by norm_num)
  · have hu' := hu.trans (zpow_le_third h1 h2)
    have h0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast hl.out.ne_zero
    have h3 : (l : ℚ_[l]) - 1 ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_sub_one]; exact one_ne_zero
    rw [logZl_eq, (lg_pow hu' _).2, Nat.cast_mul, Nat.cast_sub hl.out.one_le, Nat.cast_one,
      mul_div_cancel_left₀ _ (mul_ne_zero h0 h3), norm_lg hu']

end GlobalTheory.PadicLogUnits
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocAinfUntiltEpsOneEqZeta
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.TiedMu

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem zeta_pow (AI : LocAinf l P) (k n : ℕ) : AI.ζ (n + k) ^ l ^ n = AI.ζ k := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, Nat.add_right_comm, AI.ζ_succ, ih]

theorem untilt_eps (AI : LocAinf l P) : AI.ε.untilt = 1 := by
  refine Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_
  refine ⟨AI.ζ n, (AI.ε_coeff n).symm, ?_⟩
  have h := zeta_pow AI 0 n
  rw [add_zero, AI.ζ_zero] at h
  rw [h]

theorem locAinf_untilt_epsOne_eq_zeta (AI : LocAinf l P) : AI.ε1.untilt = AI.ζ 1 := by
  refine Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_
  refine ⟨AI.ζ (n + 1), ?_, ?_⟩
  · refine (AI.ε_coeff (n + 1)).symm.trans ?_
    have h : AI.ε = AI.ε1 ^ l := by rw [LocAinf.ε1, frobeniusEquiv_symm_pow_p]
    rw [h]
    exact Perfection.coeff_pow_p _ _
  · rw [zeta_pow AI 1 n]

theorem eps_ne_one (AI : LocAinf l P) : AI.ε ≠ 1 := by
  intro h
  apply AI.ζ_one
  rw [← locAinf_untilt_epsOne_eq_zeta, LocAinf.ε1, h, map_one, map_one]

theorem eps_pow_ne_one (AI : LocAinf l P) (j : ℕ) : AI.ε ^ l ^ j ≠ 1 := by
  induction j with
  | zero => simpa using eps_ne_one AI
  | succ j ih =>
    intro h
    apply ih
    apply (frobeniusEquiv (OCb l) l).injective
    rw [frobeniusEquiv_apply, frobeniusEquiv_apply, frobenius_def, frobenius_def, ← pow_mul,
      ← pow_succ, h, one_pow]

theorem eps_root_pow (AI : LocAinf l P) (s : ℕ) : AI.εroot s ^ l ^ s = AI.ε := by
  induction s with
  | zero => simp [LocAinf.εroot]
  | succ s ih =>
    rw [LocAinf.εroot, Function.iterate_succ_apply', pow_succ', pow_mul, frobeniusEquiv_symm_pow_p]
    exact ih

theorem isUnit_aB (e : Per.Fl l) (he : e.untilt = 1) (hne : e ≠ 1) :
    IsUnit (Per.aB l (Per.tm e - 1)) :=
  GlobalTheory.CrisLoc.unit_of_root_aB l e he hne

theorem isUnit_of_aB {AI : LocAinf l P} (T : LocTied l P AI) (a : Ainf l) (h : IsUnit (Per.aB l a)) :
    IsUnit (AI.ιA a) := by
  rw [← T.ιA] at h
  have h' := h.map T.eB.symm
  rwa [RingEquiv.symm_apply_apply] at h'

theorem tied_mu_units : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → (∀ s : ℕ, IsUnit (AI.ιA (WittVector.teichmuller l (AI.εroot s) - 1))) ∧ (∀ j : ℕ, IsUnit (AI.ιA (WittVector.teichmuller l (AI.ε ^ l ^ j) - 1))) ∧ IsUnit (AI.ιA AI.ξ) ∧ ∀ z : ℤ_[l], AI.ιA (algebraMap ℤ_[l] (Ainf l) z) = algebraMap ℚ_[l] P.R.B (z : ℚ_[l]) := by
  intro l _ P AI T
  have hj : ∀ j : ℕ, IsUnit (AI.ιA (WittVector.teichmuller l (AI.ε ^ l ^ j) - 1)) := fun j =>
    isUnit_of_aB T _ (isUnit_aB (AI.ε ^ l ^ j)
      (by rw [map_pow, untilt_eps, one_pow]) (eps_pow_ne_one AI j))
  have hμ : IsUnit (AI.ιA AI.μ) := by simpa [LocAinf.μ] using hj 0
  refine ⟨fun s => ?_, hj, ?_, fun z => ?_⟩
  · have h := geom_sum_mul (WittVector.teichmuller l (AI.εroot s)) (l ^ s)
    rw [← map_pow, eps_root_pow] at h
    rw [LocAinf.μ, ← h, map_mul] at hμ
    exact isUnit_of_mul_isUnit_right hμ
  · rw [AI.μ_eq, map_mul] at hμ
    exact isUnit_of_mul_isUnit_right hμ
  · apply T.eB.injective
    rw [T.ιA, T.zB]
    exact GlobalTheory.RingIface.aB_algebraMap_padicInt l z

end GlobalTheory.TiedMu
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffEqZeroOfStable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.UnramDisjoint

theorem coeff_eq_zero_of_stable {F Ω ι : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
    [Fintype ι] (K N : IntermediateField F Ω)
    (hN : ∀ (g : Ω ≃ₐ[F] Ω) (y : Ω), y ∈ N → g y ∈ N) (x : ι → Ω) (hx : ∀ i, x i ∈ K)
    (hind : ∀ c : ι → Ω, (∀ i, c i ∈ K ⊓ N) → ∑ i, c i * x i = 0 → ∀ i, c i = 0)
    (c : ι → Ω) (hc : ∀ i, c i ∈ N) (h : ∑ i, c i * x i = 0) : ∀ i, c i = 0 := by
  classical
  suffices H : ∀ n : ℕ, ∀ c : ι → Ω, (Finset.univ.filter (fun i => c i ≠ 0)).card = n →
      (∀ i, c i ∈ N) → ∑ i, c i * x i = 0 → ∀ i, c i = 0 from H _ c rfl hc h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c hcard hc h
  by_contra hne
  obtain ⟨j, hj⟩ := not_forall.mp hne

  set d : ι → Ω := fun i => c i * (c j)⁻¹ with hd
  have hdN : ∀ i, d i ∈ N := fun i => N.mul_mem (hc i) (N.inv_mem (hc j))
  have hdj : d j = 1 := mul_inv_cancel₀ hj
  have hdsum : ∑ i, d i * x i = 0 := by
    calc ∑ i, d i * x i = (∑ i, c i * x i) * (c j)⁻¹ := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i _ => by simp only [hd]; ring)
      _ = 0 := by rw [h, zero_mul]

  have hfix : ∀ g ∈ K.fixingSubgroup, ∀ i, g (d i) = d i := by
    intro g hg
    have hgx : ∀ i, g (x i) = x i := fun i => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _ (hx i)
    set e : ι → Ω := fun i => g (d i) - d i with he
    have heN : ∀ i, e i ∈ N := fun i => N.sub_mem (hN g _ (hdN i)) (hdN i)
    have h2 : ∑ i, g (d i) * x i = 0 := by
      have := congrArg g hdsum
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero] at this
      simpa only [map_mul, hgx] using this
    have hesum : ∑ i, e i * x i = 0 := by
      simp only [he, sub_mul, Finset.sum_sub_distrib, h2, hdsum, sub_zero]
    have hej : e j = 0 := by simp only [he, hdj, map_one, sub_self]
    have hlt : (Finset.univ.filter (fun i => e i ≠ 0)).card < n := by
      rw [← hcard]
      apply Finset.card_lt_card
      refine (Finset.ssubset_iff_of_subset ?_).mpr ⟨j, ?_, ?_⟩
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        intro hci
        apply hi
        have hdi : d i = 0 := by simp only [hd, hci, zero_mul]
        simp only [he, hdi, map_zero, sub_zero]
      · simp [hj]
      · simp [hej]
    intro i
    exact sub_eq_zero.mp (ih _ hlt e rfl heN hesum i)

  have hdK : ∀ i, d i ∈ K := by
    intro i
    rw [← InfiniteGalois.fixedField_fixingSubgroup K, IntermediateField.mem_fixedField_iff]
    exact fun g hg => hfix g hg i
  have h0 := hind d (fun i => ⟨hdK i, hdN i⟩) hdsum j
  rw [hdj] at h0
  exact one_ne_zero h0

theorem apply_mem_Kur {l : ℕ} [Fact l.Prime] (g : GQ l) (y : Om l) (hy : y ∈ MaximalUnramifiedExtension l) :
    g y ∈ MaximalUnramifiedExtension l := by
  delta MaximalUnramifiedExtension at hy ⊢
  have hmap : (IntermediateField.adjoin ℚ_[l] {x : PadicAlgCl l | ∃ m, 0 < m ∧ ¬l ∣ m ∧ x ^ m = 1}).map
      (g : PadicAlgCl l →ₐ[ℚ_[l]] PadicAlgCl l) ≤
      IntermediateField.adjoin ℚ_[l] {x : PadicAlgCl l | ∃ m, 0 < m ∧ ¬l ∣ m ∧ x ^ m = 1} := by
    rw [IntermediateField.adjoin_map]
    apply IntermediateField.adjoin.mono
    rintro _ ⟨z, ⟨m, hm, hl, hz⟩, rfl⟩
    exact ⟨m, hm, hl, by rw [← map_pow, hz, map_one]⟩
  exact hmap ⟨y, hy, rfl⟩

theorem linearIndependent_Kur (l : ℕ) [Fact l.Prime] (K : FinExt l) (m : ℕ) (x : Fin m → ↥K.1)
    (hx : LinearIndependent ↥(K0 K) x) :
    LinearIndependent ↥(MaximalUnramifiedExtension l) (fun i => (x i : Om l)) := by
  rw [Fintype.linearIndependent_iff] at hx ⊢
  intro a ha
  have hcoe : ∀ z : ↥(K0 K), ((algebraMap ↥(K0 K) ↥K.1 z : ↥K.1) : Om l) = z := fun z => rfl
  have hzero := coeff_eq_zero_of_stable (F := ℚ_[l]) K.1 (MaximalUnramifiedExtension l) (fun g y hy => apply_mem_Kur g y hy)
    (fun i => (x i : Om l)) (fun i => (x i).2)
    (fun c hc hsum => by
      have hc0 := hx (fun i => ⟨c i, hc i⟩) (by
        apply Subtype.ext
        simpa [Algebra.smul_def, hcoe] using hsum)
      intro i
      simpa using congrArg Subtype.val (hc0 i))
    (fun i => (a i : Om l)) (fun i => (a i).2)
    (by simpa [Algebra.smul_def] using ha)
  intro i
  exact Subtype.ext (hzero i)

end GlobalTheory.UnramDisjoint
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiFree
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiFree
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc

namespace GlobalTheory.Cyc.PhiFree

open PowerSeries

theorem bijective_of_congr {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (a : R) [IsPrecomplete (Ideal.span {a}) M] [IsHausdorff (Ideal.span {a}) M]
    [IsHausdorff (Ideal.span {a}) N] (ha : ∀ y : N, a • y = 0 → y = 0) (S T : M →ₗ[R] N)
    (hS : Function.Bijective S) (h : ∀ z, T z - S z ∈ (Ideal.span {a} • ⊤ : Submodule R N)) :
    Function.Bijective T := by
  constructor
  · rw [injective_iff_map_eq_zero]
    have step : ∀ z, T z = 0 → ∃ z', T z' = 0 ∧ z = a • z' := fun z hz => by
      have h1 := h z
      rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
      obtain ⟨u, -, hu⟩ := h1
      obtain ⟨v, rfl⟩ := hS.2 u
      have h2 : z = a • (-v) := hS.1 (by rw [map_smul, map_neg, smul_neg, hu, hz]; simp)
      exact ⟨-v, ha _ (by rw [← map_smul, ← h2, hz]), h2⟩
    have all : ∀ (n : ℕ) z, T z = 0 → ∃ z', z = a ^ n • z' := fun n => by
      induction n with
      | zero => exact fun z _ => ⟨z, by simp⟩
      | succ n ih =>
        intro z hz
        obtain ⟨z', h1, rfl⟩ := step z hz
        obtain ⟨w, rfl⟩ := ih z' h1
        exact ⟨w, by rw [smul_smul, pow_succ']⟩
    intro z hz
    refine IsHausdorff.haus' (I := Ideal.span {a}) z fun n => ?_
    obtain ⟨w, rfl⟩ := all n z hz
    rw [SModEq.zero]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self a) n) trivial
  · refine surjective_of_mkQ_comp_surjective (I := Ideal.span {a}) fun G => ?_
    obtain ⟨G, rfl⟩ := Submodule.Quotient.mk_surjective _ G
    obtain ⟨z, rfl⟩ := hS.2 G
    exact ⟨z, (Submodule.Quotient.eq _).2 (h z)⟩

theorem bijective_one_add {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : B) (n : ℕ)
    (h : Function.Bijective fun z : Fin n → A => ∑ j : Fin n, x ^ (j : ℕ) * f (z j)) :
    Function.Bijective fun z : Fin n → A => ∑ j : Fin n, (1 + x) ^ (j : ℕ) * f (z j) := by
  have key : ∀ (t : B) (p : Polynomial.degreeLT A n),
      ∑ j : Fin n, t ^ (j : ℕ) * f (Polynomial.degreeLTEquiv A n p j) = p.1.eval₂ f t := fun t p => by
    rw [Polynomial.eval₂_eq_sum, ← Polynomial.sum_fin _ (by simp) (Polynomial.mem_degreeLT.1 p.2)]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  let e : (Fin n → A) ≃ₗ[A] (Fin n → A) := (Polynomial.degreeLTEquiv A n).symm.trans
    ((Polynomial.taylorLinearEquiv 1 n).trans (Polynomial.degreeLTEquiv A n))
  convert h.comp e.bijective using 1
  funext z
  obtain ⟨p, rfl⟩ := (Polynomial.degreeLTEquiv A n).surjective z
  simp only [e, Function.comp, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, key]
  change _ = (Polynomial.taylor 1 p.1).eval₂ f x
  rw [Polynomial.taylor_apply, Polynomial.eval₂_comp]
  simp [add_comm]

theorem coeff_sum_expand {R : Type} [CommRing R] (n : ℕ) (hn : n ≠ 0) (z : Fin n → R⟦X⟧) (i : Fin n)
    (m : ℕ) : coeff (n * m + i) (∑ j : Fin n, X ^ (j : ℕ) * expand n hn (z j)) = coeff m (z i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single i]
  · rw [coeff_X_pow_mul, coeff_expand_mul]
  · intro j _ hj
    rw [coeff_X_pow_mul']
    split_ifs with h
    · refine coeff_expand_of_not_dvd _ _ _ fun hd => hj (Fin.ext ?_)
      have h1 : (j : ℕ) ≡ n * m + i [MOD n] := (Nat.modEq_iff_dvd' h).2 hd
      have h2 : n * m + i ≡ i [MOD n] := by simp [Nat.ModEq]
      exact (h1.trans h2).eq_of_lt_of_lt j.2 i.2
    · rfl
  · simp

theorem bijective_expand {R : Type} [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    Function.Bijective fun z : Fin n → R⟦X⟧ => ∑ j : Fin n, X ^ (j : ℕ) * expand n hn (z j) := by
  constructor
  · intro z z' h
    funext i
    ext m
    rw [← coeff_sum_expand n hn z, ← coeff_sum_expand n hn z']
    exact congrArg _ h
  · intro y
    refine ⟨fun i => PowerSeries.mk fun m => coeff (n * m + i) y, ?_⟩
    ext k
    have h := coeff_sum_expand n hn (fun i => PowerSeries.mk fun m => coeff (n * m + i) y)
      ⟨k % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩ (k / n)
    simpa [Nat.div_add_mod] using h

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]

theorem coeff_phi_sub_expand_mem (J : Ideal O) (hl : (l : O) ∈ J) (z : O⟦X⟧) (k : ℕ) :
    coeff k (phi l O z - expand l (Fact.out : l.Prime).ne_zero z) ∈ J := by
  have h : (PowerSeries.map (Ideal.Quotient.mk J)).comp (phi l O : O⟦X⟧ →+* O⟦X⟧) =
      (PowerSeries.map (Ideal.Quotient.mk J)).comp
        (expand l (Fact.out : l.Prime).ne_zero : O⟦X⟧ →ₐ[O] O⟦X⟧) := by
    have hX : PowerSeries.map (Ideal.Quotient.mk J) (phi l O X) = X ^ l := by
      obtain ⟨r, hr⟩ := Series.phi_X_mod l O
      have h0 : ((l : ℕ) : (O ⧸ J)⟦X⟧) = 0 := by
        rw [← map_natCast (C (R := O ⧸ J)), ← map_natCast (Ideal.Quotient.mk J),
          Ideal.Quotient.eq_zero_iff_mem.2 hl, map_zero]
      rw [hr]
      simp [h0]
    refine Fon.ps_hom_ext (fun r => ?_) ?_ ?_
    · exact congrArg (PowerSeries.map (Ideal.Quotient.mk J))
        (((phi l O).commutes r).trans ((expand l (Fact.out : l.Prime).ne_zero).commutes r).symm)
    · exact hX.trans (by simp)
    · refine Fon.eq_zero_of_pow_dvd ?_
      change constantCoeff (PowerSeries.map (Ideal.Quotient.mk J) (phi l O X)) = 0
      rw [hX]
      simp [(Fact.out : l.Prime).ne_zero]
  have h1 := congrArg (coeff k) (RingHom.congr_fun h z)
  rw [map_sub, ← Ideal.Quotient.eq]
  simpa only [RingHom.comp_apply, coeff_map, RingHom.coe_coe] using h1

end GlobalTheory.Cyc.PhiFree

namespace GlobalTheory.Cyc

open PhiFree CompleteBaseChange

theorem phi_free : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Algebra ℤ_[l] O], (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ y : PowerSeries O, ∃! z : Fin l → PowerSeries O, y = ∑ j : Fin l, (1 + PowerSeries.X) ^ (j : ℕ) * phi l O (z j) := by
  intro l _ O _ _ _ _ _ _ hl y
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hm := ha.maximalIdeal_eq
  have hla : (l : O) ∈ Ideal.span {a} := hm ▸ (IsLocalRing.mem_maximalIdeal _).2 hl
  have : IsAdicComplete (Ideal.span {a}) O := hm ▸ ‹_›
  have hJ : (Ideal.span {a}).FG := Submodule.fg_span_singleton a
  have : IsPrecomplete (Ideal.span {a}) (PowerSeries O) := isPrecomplete_pi (Unit →₀ ℕ) hJ
  have : IsHausdorff (Ideal.span {a}) (PowerSeries O) := isHausdorff_pi (Unit →₀ ℕ) hJ
  have : IsPrecomplete (Ideal.span {a}) (Fin l → PowerSeries O) := isPrecomplete_pi _ hJ
  have : IsHausdorff (Ideal.span {a}) (Fin l → PowerSeries O) := isHausdorff_pi _ hJ
  let F : (PowerSeries O →ₐ[O] PowerSeries O) → (Fin l → PowerSeries O) →ₗ[O] PowerSeries O := fun f =>
    { toFun := fun z => ∑ j : Fin l, PowerSeries.X ^ (j : ℕ) * f (z j)
      map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.smul_sum] }
  have hT : Function.Bijective (F (phi l O)) := by
    refine bijective_of_congr a (fun y hy => ?_) (F (PowerSeries.expand l (Fact.out : l.Prime).ne_zero)) _
      (bijective_expand l _) fun z => ?_
    · ext k
      have h1 := congrArg (PowerSeries.coeff k) hy
      rw [map_smul, map_zero, smul_eq_mul] at h1
      exact (mul_eq_zero.1 h1).resolve_left ha.ne_zero
    · change (∑ j : Fin l, _) - (∑ j : Fin l, _) ∈ _
      rw [← Finset.sum_sub_distrib]
      refine Submodule.sum_mem _ fun j _ => ?_
      have h1 : phi l O (z j) - PowerSeries.expand l (Fact.out : l.Prime).ne_zero (z j) ∈
          (Ideal.span {a} • ⊤ : Submodule O (PowerSeries O)) :=
        (mem_smul_top_pi (ι := Unit →₀ ℕ) hJ _).2 fun d => by
          have h2 := coeff_phi_sub_expand_mem l O _ hla (z j) (d ())
          rw [PowerSeries.coeff, Finsupp.unique_single d |>.symm] at h2
          rw [smul_eq_mul, Ideal.mul_top]
          exact h2
      rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1 ⊢
      obtain ⟨u, -, hu⟩ := h1
      exact ⟨PowerSeries.X ^ (j : ℕ) * u, trivial, by rw [← mul_sub, ← hu, mul_smul_comm]⟩
  have h := (bijective_one_add (phi l O : PowerSeries O →+* PowerSeries O) PowerSeries.X l hT).existsUnique y
  simpa only [eq_comm (a := y), RingHom.coe_coe] using h

end GlobalTheory.Cyc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiFreeStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_decomposition_one_add_X_pow_mul_phi : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Algebra ℤ_[l] O], (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ y : PowerSeries O, ∃! z : Fin l → PowerSeries O, y = ∑ j : Fin l, (1 + PowerSeries.X) ^ (j : ℕ) * phi l O (z j) := by
  first | exact @GlobalTheory.Cyc.phi_free | exact GlobalTheory.Cyc.phi_free | (intros; apply GlobalTheory.Cyc.phi_free <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankPeriodFunctorCoeffBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankPeriodFunctorCoeffBaseChange
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CoeffBC

section General

variable {L L' : Type} [Field L] [Field L'] [Algebra L L'] {ι : Type} [Fintype ι] [DecidableEq ι]
  {M M' : Type} [AddCommGroup M] [Module L M] [AddCommGroup M'] [Module L' M'] [Module L M']
  {N N' : Type} [AddCommGroup N] [Module L N] [AddCommGroup N'] [Module L' N'] [Module L N']

def IsCoord (u : ι → L') (J : M →ₗ[L] M') (π : ι → M' →ₗ[L] M) : Prop :=
  (∀ x, ∑ k, u k • J (π k x) = x) ∧ ∀ k l m, π k (u l • J m) = if k = l then m else 0

def Rel (π : ι → M' →ₗ[L] M) (S : Submodule L M) (S' : Submodule L' M') : Prop :=
  ∀ x, x ∈ S' ↔ ∀ k, π k x ∈ S

theorem exists_isCoord [IsScalarTower L L' M'] (u : Basis ι L L') (J : M →ₗ[L] M')
    (h : IsBaseChange L' J) : ∃ π : ι → M' →ₗ[L] M, IsCoord u J π := by
  let π : ι → M' →ₗ[L] M := fun k =>
    (TensorProduct.lid L M).toLinearMap ∘ₗ LinearMap.rTensor M (u.coord k) ∘ₗ
      (h.equiv.symm.toLinearMap.restrictScalars L)
  have hπ : ∀ k (s : L') (m : M), π k (s • J m) = u.repr s k • m := by
    intro k s m
    have : h.equiv.symm (s • J m) = s ⊗ₜ[L] m := by
      rw [LinearEquiv.symm_apply_eq, h.equiv_tmul]
    simp only [π, LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, this]
    simp
  refine ⟨π, fun x => ?_, fun k l m => ?_⟩
  · obtain ⟨y, rfl⟩ := h.equiv.surjective x
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul s m =>
      rw [h.equiv_tmul]
      simp only [hπ, map_smul]
      conv_rhs => rw [← u.sum_repr s, Finset.sum_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_assoc, smul_comm]
    | add a b ha hb =>
      simp only [map_add (f := _), smul_add, Finset.sum_add_distrib, ha, hb]
  · rw [hπ, u.repr_self, Finsupp.single_apply]
    by_cases hk : k = l
    · simp [hk]
    · simp [hk, Ne.symm hk]

variable {u : ι → L'} {J : M →ₗ[L] M'} {π : ι → M' →ₗ[L] M}
  {JN : N →ₗ[L] N'} {πN : ι → N' →ₗ[L] N}

theorem IsCoord.sum (h : IsCoord u J π) (m : ι → M) (k : ι) :
    π k (∑ l, u l • J (m l)) = m k := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, h.2]

theorem IsCoord.comm (h : IsCoord u J π) (hN : IsCoord u JN πN) (f : N →ₗ[L] M)
    (f' : N' →ₗ[L'] M') (hf : ∀ y, f' (JN y) = J (f y)) (k : ι) (x : N') :
    π k (f' x) = f (πN k x) := by
  conv_lhs => rw [← hN.1 x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum f', map_smul, hf]
  exact h.sum _ k

theorem IsCoord.rel_ker (h : IsCoord u J π) (hN : IsCoord u JN πN) (f : N →ₗ[L] M)
    (f' : N' →ₗ[L'] M') (hf : ∀ y, f' (JN y) = J (f y)) :
    Rel πN (LinearMap.ker f) (LinearMap.ker f') := by
  intro x
  simp only [LinearMap.mem_ker, ← h.comm hN f f' hf]
  refine ⟨fun hx k => by simp [hx], fun hx => ?_⟩
  rw [← h.1 (f' x)]
  simp [hx]

theorem IsCoord.rel_range (h : IsCoord u J π) (hN : IsCoord u JN πN) (f : N →ₗ[L] M)
    (f' : N' →ₗ[L'] M') (hf : ∀ y, f' (JN y) = J (f y)) :
    Rel π (LinearMap.range f) (LinearMap.range f') := by
  intro x
  constructor
  · rintro ⟨y, rfl⟩ k
    exact ⟨_, (h.comm hN f f' hf k y).symm⟩
  · intro hx
    choose y hy using hx
    refine ⟨∑ k, u k • JN (y k), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hf, hy]
    exact h.1 x

omit [Algebra L L'] [Fintype ι] [DecidableEq ι] in
theorem Rel.inf {S T : Submodule L M} {S' T' : Submodule L' M'} (h : Rel π S S')
    (h' : Rel π T T') : Rel π (S ⊓ T) (S' ⊓ T') := by
  intro x
  simp only [Submodule.mem_inf, h x, h' x, forall_and]

omit [Algebra L L'] [Fintype ι] [DecidableEq ι] in
theorem Rel.iInf {κ : Type} {S : κ → Submodule L M} {S' : κ → Submodule L' M'}
    (h : ∀ i, Rel π (S i) (S' i)) : Rel π (⨅ i, S i) (⨅ i, S' i) := by
  intro x
  simp only [Submodule.mem_iInf, fun i => h i x]
  exact forall_comm

theorem IsCoord.nonempty_equiv [IsScalarTower L L' M'] (h : IsCoord u J π) {S : Submodule L M}
    {S' : Submodule L' M'} (hS : Rel π S S') : Nonempty (S' ≃ₗ[L] (ι → S)) := by
  let F : S' →ₗ[L] (ι → S) := LinearMap.pi fun k =>
    LinearMap.codRestrict S (π k ∘ₗ (S'.subtype.restrictScalars L))
      (fun x => (hS x.1).1 x.2 k)
  have hF : ∀ x k, (F x k : M) = π k x := fun _ _ => rfl
  refine ⟨LinearEquiv.ofBijective F ⟨?_, ?_⟩⟩
  · intro x y hxy
    apply Subtype.ext
    rw [← h.1 x, ← h.1 y]
    simp only [← hF, hxy]
  · intro m
    refine ⟨⟨∑ l, u l • J (m l), (hS _).2 fun k => ?_⟩, ?_⟩
    · rw [h.sum (fun l => (m l : M))]; exact (m k).2
    · funext k
      apply Subtype.ext
      rw [hF]
      exact h.sum (fun l => (m l : M)) k

theorem IsCoord.finrank_eq [IsScalarTower L L' M'] {u : Basis ι L L'} (h : IsCoord u J π)
    {S : Submodule L M} {S' : Submodule L' M'} (hS : Rel π S S') :
    finrank L' S' = finrank L S := by
  obtain ⟨e⟩ := h.nonempty_equiv hS
  haveI : Module.Finite L L' := Module.Finite.of_basis u
  have h1 : finrank L L' * finrank L' S' = finrank L S' := Module.finrank_mul_finrank L L' S'
  have h2 : finrank L (ι → S) = Fintype.card ι * finrank L S := by
    simp [Module.finrank, rank_fun_eq_lift_mul]
  rw [e.finrank_eq, h2, ← Module.finrank_eq_card_basis u] at h1
  exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h1

theorem IsCoord.finite_iff [IsScalarTower L L' M'] {u : Basis ι L L'} (h : IsCoord u J π)
    {S : Submodule L M} {S' : Submodule L' M'} (hS : Rel π S S') :
    Module.Finite L' S' ↔ Module.Finite L S := by
  obtain ⟨e⟩ := h.nonempty_equiv hS
  haveI : Module.Finite L L' := Module.Finite.of_basis u
  obtain ⟨k⟩ := u.index_nonempty
  constructor
  · intro _
    haveI : Module.Finite L S' := Module.Finite.trans L' S'
    haveI : Module.Finite L (ι → S) := Module.Finite.equiv e
    exact Module.Finite.of_surjective (LinearMap.proj k : (ι → S) →ₗ[L] S)
      (LinearMap.proj_surjective k)
  · intro _
    haveI : Module.Finite L S' := Module.Finite.equiv e.symm
    exact Module.Finite.of_restrictScalars_finite L L' S'

theorem IsCoord.tensor {Q : Type} [Field Q] [Algebra Q L] [Algebra Q L'] [Module Q M] [Module Q M']
    [IsScalarTower Q L M] [IsScalarTower Q L M'] [IsScalarTower Q L' M']
    (h : IsCoord u J π) (C : Type) [AddCommGroup C] [Module Q C] :
    IsCoord u (AlgebraTensorModule.map J (LinearMap.id : C →ₗ[Q] C))
      (fun k => AlgebraTensorModule.map (π k) (LinearMap.id : C →ₗ[Q] C)) := by
  constructor
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m c =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, TensorProduct.smul_tmul']
      rw [← TensorProduct.sum_tmul, h.1]
    | add a b ha hb => simp only [map_add (f := _), smul_add, Finset.sum_add_distrib, ha, hb]
  · intro k l x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m c =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, TensorProduct.smul_tmul', h.2]
      split_ifs <;> simp
    | add a b ha hb =>
      simp only [map_add (f := _), smul_add, ha, hb]
      split_ifs <;> simp

theorem map_comm {Q : Type} [Field Q] [Algebra Q L] [Algebra Q L'] [Module Q M] [Module Q M']
    [IsScalarTower Q L M] [IsScalarTower Q L M'] [IsScalarTower Q L' M']
    {C D : Type} [AddCommGroup C] [Module Q C] [AddCommGroup D] [Module Q D]
    (f : M →ₗ[L] M) (f' : M' →ₗ[L'] M') (hf : ∀ m, f' (J m) = J (f m)) (φ : C →ₗ[Q] D)
    (y : M ⊗[Q] C) :
    AlgebraTensorModule.map f' φ (AlgebraTensorModule.map J (LinearMap.id : C →ₗ[Q] C) y) =
      AlgebraTensorModule.map J (LinearMap.id : D →ₗ[Q] D) (AlgebraTensorModule.map f φ y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m c => simp [hf]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

end General

theorem finrank_baseChange : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) (LL LL' : Type) [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL'] [FiniteDimensional LL LL'] (V V' : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [AddCommGroup V'] [Module LL' V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL' V'] [IsScalarTower LL LL' V'] (ρ : Representation LL G V) (ρ' : Representation LL' G V') (j : V →ₗ[LL] V'), IsBaseChange LL' j → (∀ g x, j (ρ g x) = ρ' g (j x)) → finrank LL' V' = finrank LL V ∧ finrank LL' ↥(H0V ρ') = finrank LL ↥(H0V ρ) ∧ (finrank LL' ↥(Dcris PD ρ') = finrank LL ↥(Dcris PD ρ) ∧ (Module.Finite LL' ↥(Dcris PD ρ') ↔ Module.Finite LL ↥(Dcris PD ρ))) ∧ (finrank LL' ↥(DdR PD ρ') = finrank LL ↥(DdR PD ρ) ∧ (Module.Finite LL' ↥(DdR PD ρ') ↔ Module.Finite LL ↥(DdR PD ρ))) ∧ (∀ a : ℤ, finrank LL' ↥(DdR PD ρ' ⊓ FilV PD (LL := LL') (V := V') a) = finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a)) ∧ (∀ τ : K₀ →ₐ[Qp] LL, finrank LL' ↥(DcrisL PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ)) = finrank LL ↥(DcrisL PD ρ τ)) ∧ ∀ τ : K →ₐ[Qp] LL, finrank LL' ↥(DdRE PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ)) = finrank LL ↥(DdRE PD ρ τ) ∧ ∀ a : ℤ, finrank LL' ↥(FildR PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ) a) = finrank LL ↥(FildR PD ρ τ a) := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL LL' _ _ _ _ _ _ _ V V' _ _ _ _ _ _ _ _ _ _ ρ ρ' j hj hρ
  classical
  haveI : IsScalarTower Qp LL V' := IsScalarTower.of_algebraMap_smul fun r x => by
    rw [← algebraMap_smul LL' (algebraMap Qp LL r) x, ← IsScalarTower.algebraMap_apply,
      algebraMap_smul]
  let u := Module.finBasis LL LL'
  obtain ⟨π, h⟩ := exists_isCoord u j hj
  have hB := h.tensor (Q := Qp) B
  have hR := h.tensor (Q := Qp) BdR
  have r0 : Rel π (H0V ρ) (H0V ρ') :=
    Rel.iInf fun g => h.rel_ker h _ _ fun y => by simp [hρ]
  have rc : Rel _ (Dcris PD ρ) (Dcris PD ρ') :=
    Rel.iInf fun g => hB.rel_ker hB _ _ fun y => by
      simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, actVB]
      rw [map_comm (ρ g) (ρ' g) (fun m => (hρ g m).symm)]
  have rd : Rel _ (DdR PD ρ) (DdR PD ρ') :=
    Rel.iInf fun g => hR.rel_ker hR _ _ fun y => by
      simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, actVdR]
      rw [map_comm (ρ g) (ρ' g) (fun m => (hρ g m).symm)]
  have rf : ∀ a : ℤ,
      Rel (fun k => AlgebraTensorModule.map (π k) (LinearMap.id : BdR →ₗ[Qp] BdR))
        (FilV PD (LL := LL) (V := V) a) (FilV PD (LL := LL') (V := V') a) := by
    intro a
    have hF := h.tensor (Q := Qp) ↥((PD.Fil a).restrictScalars Qp)
    refine hR.rel_range hF
      (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil a).restrictScalars Qp).subtype)
      (AlgebraTensorModule.map (LinearMap.id : V' →ₗ[LL'] V')
        ((PD.Fil a).restrictScalars Qp).subtype) fun y => ?_
    exact map_comm (J := j) LinearMap.id LinearMap.id (fun _ => rfl)
      ((PD.Fil a).restrictScalars Qp).subtype y
  have re : ∀ τ : K →ₐ[Qp] LL,
      Rel _ (DdRE PD ρ τ) (DdRE PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ)) :=
    fun τ => rd.inf (Rel.iInf fun c => hR.rel_ker hR _ _ fun y => by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, mulVdR,
        map_smul, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, algebraMap_smul]
      rw [map_comm (L' := LL') (J := j) LinearMap.id LinearMap.id (fun _ => rfl)])
  have rl : ∀ τ : K₀ →ₐ[Qp] LL,
      Rel _ (DcrisL PD ρ τ) (DcrisL PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ)) :=
    fun τ => rc.inf (Rel.iInf fun c => hB.rel_ker hB _ _ fun y => by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, mulVB,
        map_smul, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, algebraMap_smul]
      rw [map_comm (L' := LL') (J := j) LinearMap.id LinearMap.id (fun _ => rfl)])
  refine ⟨?_, h.finrank_eq r0, ⟨hB.finrank_eq rc, hB.finite_iff rc⟩,
    ⟨hR.finrank_eq rd, hR.finite_iff rd⟩, fun a => hR.finrank_eq (rd.inf (rf a)),
    fun τ => hB.finrank_eq (rl τ),
    fun τ => ⟨hR.finrank_eq (re τ), fun a => hR.finrank_eq ((re τ).inf (rf a))⟩⟩
  have := h.finrank_eq (S := ⊤) (S' := ⊤) (fun x => by simp)
  simpa using this

end GlobalTheory.CoeffBC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankPeriodFunctorCoeffBaseChangeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_periodFunctor_coeff_baseChange : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) (LL LL' : Type) [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL'] [FiniteDimensional LL LL'] (V V' : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [AddCommGroup V'] [Module LL' V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL' V'] [IsScalarTower LL LL' V'] (ρ : Representation LL G V) (ρ' : Representation LL' G V') (j : V →ₗ[LL] V'), IsBaseChange LL' j → (∀ g x, j (ρ g x) = ρ' g (j x)) → finrank LL' V' = finrank LL V ∧ finrank LL' ↥(H0V ρ') = finrank LL ↥(H0V ρ) ∧ (finrank LL' ↥(Dcris PD ρ') = finrank LL ↥(Dcris PD ρ) ∧ (Module.Finite LL' ↥(Dcris PD ρ') ↔ Module.Finite LL ↥(Dcris PD ρ))) ∧ (finrank LL' ↥(DdR PD ρ') = finrank LL ↥(DdR PD ρ) ∧ (Module.Finite LL' ↥(DdR PD ρ') ↔ Module.Finite LL ↥(DdR PD ρ))) ∧ (∀ a : ℤ, finrank LL' ↥(DdR PD ρ' ⊓ FilV PD (LL := LL') (V := V') a) = finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a)) ∧ (∀ τ : K₀ →ₐ[Qp] LL, finrank LL' ↥(DcrisL PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ)) = finrank LL ↥(DcrisL PD ρ τ)) ∧ ∀ τ : K →ₐ[Qp] LL, finrank LL' ↥(DdRE PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ)) = finrank LL ↥(DdRE PD ρ τ) ∧ ∀ a : ℤ, finrank LL' ↥(FildR PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ) a) = finrank LL ↥(FildR PD ρ τ a) := by
  first | exact @GlobalTheory.CoeffBC.finrank_baseChange | exact GlobalTheory.CoeffBC.finrank_baseChange | (intros; apply GlobalTheory.CoeffBC.finrank_baseChange <;> assumption)
end
end
