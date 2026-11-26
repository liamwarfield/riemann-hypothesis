module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DirichletCharFiniteFourierTransformProperties
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummableCardDivisorsSqDivOneAddRpow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LipschitzWeightOnePeriodicMeanZeroStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasModerateGrowthAlgebraSlashStable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumQExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoAtTopOfCofinite
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.RowLim

noncomputable def symS (f : ℤ → ℂ) (R : ℕ) : ℂ := ∑ d ∈ Finset.Icc (-(R : ℤ)) R, f d

lemma symS_succ (f : ℤ → ℂ) (R : ℕ) :
    symS f (R + 1) = f (-((R : ℤ) + 1)) + (f ((R : ℤ) + 1) + symS f R) := by
  unfold symS
  have h : Finset.Icc (-((R + 1 : ℕ) : ℤ)) ((R + 1 : ℕ) : ℤ)
      = insert (-((R : ℤ) + 1)) (insert ((R : ℤ) + 1) (Finset.Icc (-(R : ℤ)) R)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
  rw [h, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
    Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]

lemma symS_shift_one (f : ℤ → ℂ) (R : ℕ) :
    symS (fun d => f (d + 1)) R - symS f R = f ((R : ℤ) + 1) - f (-(R : ℤ)) := by
  induction R with
  | zero => simp [symS]
  | succ R ih =>
    rw [symS_succ, symS_succ]
    push_cast
    have e1 : -((R : ℤ) + 1) + 1 = -(R : ℤ) := by ring
    rw [e1]
    linear_combination ih

lemma tendsto_atTop_of_cofinite {f : ℤ → ℂ} (hf : Tendsto f cofinite (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := hf.mono_left (by rw [Int.cofinite_eq]; exact le_sup_right)

lemma tendsto_atBot_of_cofinite {f : ℤ → ℂ} (hf : Tendsto f cofinite (𝓝 0)) :
    Tendsto f atBot (𝓝 0) := hf.mono_left (by rw [Int.cofinite_eq]; exact le_sup_left)

lemma shift_tendsto {f : ℤ → ℂ} (hf : Tendsto f cofinite (𝓝 0)) (r : ℤ) :
    Tendsto (fun d => f (d + r)) cofinite (𝓝 0) :=
  hf.comp (add_left_injective r).tendsto_cofinite

lemma symS_shift_tendsto (r : ℕ) : ∀ f : ℤ → ℂ, Tendsto f cofinite (𝓝 0) →
    Tendsto (fun R => symS (fun d => f (d + r)) R - symS f R) atTop (𝓝 0) := by
  induction r with
  | zero => intro f _; simp
  | succ r ih =>
    intro f hf
    have h1 := ih (fun e => f (e + 1)) (shift_tendsto hf 1)
    have hR : Tendsto (fun R : ℕ => (R : ℤ)) atTop atTop := tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun R : ℕ => f ((R : ℤ) + 1) - f (-(R : ℤ))) atTop (𝓝 0) := by
      have a := (tendsto_atTop_of_cofinite hf).comp (tendsto_atTop_add_const_right _ 1 hR)
      have b := (tendsto_atBot_of_cofinite hf).comp (tendsto_neg_atTop_atBot.comp hR)
      simpa using a.sub b
    have := h1.add ((tendsto_congr (fun R => (symS_shift_one f R).symm)).1 h2)
    rw [add_zero] at this
    refine (tendsto_congr fun R => ?_).1 this
    have e : (fun d : ℤ => f (d + ((r + 1 : ℕ) : ℤ))) = fun d => f (d + (r : ℤ) + 1) := by
      funext d; push_cast; ring_nf
    beta_reduce
    rw [e]; ring

noncomputable def mean (L : ℕ) (k : ℤ → ℂ) (d : ℤ) : ℂ := (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, k (d + r)

lemma mean_tendsto {L : ℕ} {k : ℤ → ℂ} (hk : Tendsto k cofinite (𝓝 0)) :
    Tendsto (mean L k) cofinite (𝓝 0) := by
  have : Tendsto (fun d => ∑ r ∈ Finset.range L, k (d + r)) cofinite (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.range L) fun r _ => shift_tendsto hk r
  have h2 := this.const_mul ((L : ℂ)⁻¹)
  rw [mul_zero] at h2
  exact h2

lemma bdd_mul_tendsto {A k : ℤ → ℂ} {C : ℝ} (hA : ∀ d, ‖A d‖ ≤ C)
    (hk : Tendsto k cofinite (𝓝 0)) : Tendsto (fun d => A d * k d) cofinite (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero] at hk ⊢
  refine squeeze_zero (fun _ => norm_nonneg _) (fun d => ?_) (by simpa using hk.const_mul C)
  rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hA d) (norm_nonneg _)

lemma symS_mul_mean_tendsto {L : ℕ} {A k : ℤ → ℂ} {C : ℝ} (hA : ∀ d, ‖A d‖ ≤ C)
    (hsum : ∀ d, ∑ r ∈ Finset.range L, A (d - r) = 0) (hk : Tendsto k cofinite (𝓝 0)) :
    Tendsto (symS fun d => A d * mean L k d) atTop (𝓝 0) := by
  set f : ℕ → ℤ → ℂ := fun r e => A (e - r) * k e with hf
  have eq : ∀ R, symS (fun d => A d * mean L k d) R
      = (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, (symS (fun d => f r (d + r)) R - symS (f r) R) := by
    intro R
    have h0 : ∑ r ∈ Finset.range L, symS (f r) R = 0 := by
      simp only [symS, hf]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun d _ => ?_
      rw [← Finset.sum_mul, hsum, zero_mul]
    rw [Finset.sum_sub_distrib, h0, sub_zero]
    simp only [symS, mean, hf, add_sub_cancel_right]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [show (symS fun d => A d * mean L k d) = _ from funext eq]
  have := tendsto_finsetSum (Finset.range L) fun r _ =>
    symS_shift_tendsto r (f r) (bdd_mul_tendsto (fun d => hA (d - r)) hk)
  simpa using this.const_mul ((L : ℂ)⁻¹)

theorem rowlim : ∀ (L : ℕ) (A g : ℤ → ℂ) (G : ℤ × ℤ → ℂ) (c : ℤ), 0 < L → (∃ C : ℝ, ∀ d, ‖A d‖ ≤ C) → (∀ d, ∑ r ∈ Finset.range L, A (d - r) = 0) → (∀ d, G (c, d) = g d) → Tendsto g cofinite (𝓝 0) → (Summable fun d : ℤ => A d * dif L (0, 1) (dif L (0, 1) G) (c, d)) → Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R : ℤ)) R, A d * g d) atTop (𝓝 (∑' d : ℤ, A d * dif L (0, 1) (dif L (0, 1) G) (c, d))) := by
  intro L A g G c _ ⟨C, hA⟩ hsum hG hg hS
  have hpt : ∀ (F : ℤ × ℤ → ℂ) (d : ℤ), dif L (0, 1) F (c, d) = F (c, d) - mean L (fun e => F (c, e)) d := by
    intro F d
    have e : ∀ r : ℕ, (c, d) + (r : ℤ) • ((0 : ℤ), (1 : ℤ)) = (c, d + r) := by
      intro r; ext <;> simp
    simp only [dif, mean, e]
  set h : ℤ → ℂ := fun d => g d - mean L g d with hh
  have hG1 : ∀ d, dif L (0, 1) G (c, d) = h d := by
    intro d; rw [hpt]; simp only [hh, hG]
  have hG2 : ∀ d, dif L (0, 1) (dif L (0, 1) G) (c, d) = h d - mean L h d := by
    intro d; rw [hpt, hG1]; simp only [hG1]
  simp only [hG2] at hS ⊢
  have hTs := (hS.hasSum.comp Finset.tendsto_Icc_neg)
  have hh0 : Tendsto h cofinite (𝓝 0) := by simpa using hg.sub (mean_tendsto hg)
  have k1 := symS_mul_mean_tendsto hA hsum hg
  have k2 := symS_mul_mean_tendsto hA hsum hh0
  have := (hTs.add k1).add k2
  rw [add_zero, add_zero] at this
  refine (tendsto_congr fun R => ?_).1 this
  simp only [Function.comp, symS, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [hh]; ring

end GlobalTheory.RowLim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LipschitzFormulaPeriodicWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LipschitzFormulaPeriodicWeight
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem lipschitz_periodic : ∀ (j L : ℕ) (φ : ZMod L → ℂ) (z : ℂ), 2 ≤ j → 0 < L → 0 < z.im → Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R : ℤ)) R, φ (d : ZMod L) * trm j 0 (z + d)) atTop (𝓝 ((-2 * π * Complex.I / L) ^ j / (j - 1).factorial * ∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (j - 1) * hat φ (m + 1 : ℕ) * cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L))) := by
  intro j L φ z hj hL hz
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  have htrm : ∀ w : ℂ, trm (k + 2) 0 w = (w ^ (k + 2))⁻¹ := fun w => by simp [trm]
  set f : ℤ → ℂ := fun d => φ (d : ZMod L) * ((z + d) ^ (k + 2))⁻¹ with hf_def
  obtain ⟨M, hM⟩ : ∃ M, ∀ x, ‖φ x‖ ≤ M := ⟨∑ x, ‖φ x‖, fun x =>
    Finset.single_le_sum (f := fun x => ‖φ x‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ x)⟩
  have hs0 : ∀ w : ℂ, Summable fun d : ℤ => ((w + d) ^ (k + 2))⁻¹ := fun w => by
    have := EisensteinSeries.linear_right_summable w 1 (k := ((k + 2 : ℕ) : ℤ)) (by push_cast; omega)
    simp only [Int.cast_one, one_mul, zpow_natCast] at this
    exact this
  have hfs : Summable f := by
    refine Summable.of_norm_bounded ((hs0 z).norm.mul_left M) fun d => ?_
    simp only [f, norm_mul]
    exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
  have hlim : Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R : ℤ)) R, f d) atTop (𝓝 (∑' d, f d)) :=
    hfs.hasSum.comp (tendsto_atTop_finset_of_monotone
      (fun a b hab => Finset.Icc_subset_Icc (by omega) (by omega)) fun x => ⟨x.natAbs, Finset.mem_Icc.mpr
        ⟨by rw [Int.natCast_natAbs]; exact neg_abs_le x, by rw [Int.natCast_natAbs]; exact le_abs_self x⟩⟩)
  have hval : ∑' d, f d = (-2 * π * Complex.I / L) ^ (k + 2) / (k + 2 - 1).factorial *
      ∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (k + 2 - 1) * hat φ (m + 1 : ℕ) * cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L) := by
    set C : ℂ := (-2 * π * Complex.I) ^ (k + 2) / (k + 1).factorial with hC
    set w : ℕ → ℂ := fun r => (z + r) / L with hw_def
    have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    have hwim : ∀ r : ℕ, 0 < (w r).im := fun r => by
      simp only [w, Complex.div_natCast_im, Complex.add_im, Complex.natCast_im, add_zero]; positivity
    set q : ℕ → ℂ := fun r => cexp (2 * π * Complex.I * w r) with hq_def
    have hq : ∀ r, ‖q r‖ < 1 := fun r => UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨w r, hwim r⟩
    set g : ℕ → ℕ → ℂ := fun r m => ((m + 1 : ℕ) : ℂ) ^ (k + 1) * q r ^ (m + 1) with hg_def
    have hgs : ∀ r, Summable (g r) := fun r => by
      have h0 : Summable (fun n : ℕ => (n : ℂ) ^ (k + 1) * q r ^ n) :=
        summable_pow_mul_geometric_of_norm_lt_one (k + 1) (hq r)
      have h1 := (summable_nat_add_iff (f := fun n : ℕ => (n : ℂ) ^ (k + 1) * q r ^ n) 1).mpr h0
      refine h1.congr fun m => ?_
      simp only [g, Nat.cast_add, Nat.cast_one]
    have hres : ∀ r : Fin L, HasSum (fun n : ℤ => f (n * L + (r : ℕ)))
        (φ ((r : ℕ) : ZMod L) * ((L : ℂ)⁻¹) ^ (k + 2) * (C * ∑' m, g r m)) := by
      intro r
      have hid := EisensteinSeries.qExpansion_identity_pnat (k := k + 1) (by omega) ⟨w r, hwim r⟩
      rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (n : ℂ) ^ (k + 1) *
        cexp (2 * π * Complex.I * ((⟨w r, hwim r⟩ : ℍ) : ℂ)) ^ n)] at hid
      have h1 : HasSum (fun n : ℤ => ((w r + n) ^ (k + 2))⁻¹) (C * ∑' m, g r m) := by
        convert (hs0 (w r)).hasSum using 1
        simp only [one_div] at hid
        rw [hid]
      have h2 := h1.mul_left (φ ((r : ℕ) : ZMod L) * ((L : ℂ)⁻¹) ^ (k + 2))
      refine (congrArg (fun F => HasSum F _) (funext fun n => ?_)).mpr h2
      simp only [f]
      have e1 : (((n * L + (r : ℕ) : ℤ)) : ZMod L) = ((r : ℕ) : ZMod L) := by push_cast; simp
      have e2 : z + (((n * L + (r : ℕ) : ℤ)) : ℂ) = L * (w r + n) := by
        simp only [w]; push_cast; field_simp; ring
      rw [e1, e2, mul_pow, mul_inv, inv_pow]; ring
    let e : Fin L × ℤ ≃ ℤ := (Equiv.prodComm _ _).trans (Int.divModEquiv L).symm
    have he : ∀ p : Fin L × ℤ, e p = p.2 * L + ((p.1 : ℕ) : ℤ) := fun p => by
      simp [e, Int.divModEquiv_symm_apply]
    have hfe : HasSum (f ∘ e) (∑' d, f d) := by rw [e.hasSum_iff]; exact hfs.hasSum
    have hg2 : HasSum (fun r : Fin L => φ ((r : ℕ) : ZMod L) * ((L : ℂ)⁻¹) ^ (k + 2) * (C * ∑' m, g r m))
        (∑' d, f d) :=
      hfe.prod_fiberwise fun r => by
        convert hres r using 1
        funext n; simp only [Function.comp_apply, he]
    have hsum : ∑ r : Fin L, φ ((r : ℕ) : ZMod L) * ∑' m, g r m = ∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (k + 1) *
        hat φ (m + 1 : ℕ) * cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L) := by
      simp_rw [← tsum_mul_left]
      rw [← Summable.tsum_finsetSum (f := fun (r : Fin L) m => φ ((r : ℕ) : ZMod L) * g r m)
        (fun r _ => (hgs r).mul_left _)]
      refine tsum_congr fun m => ?_
      rw [Fin.sum_univ_eq_sum_range (fun y => φ (y : ZMod L) * g y m) L]
      simp only [hat, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun y _ => ?_
      have : q y ^ (m + 1) = cexp (2 * π * Complex.I * (y * (((m + 1 : ℕ) : ℤ) : ℂ)) / L) *
          cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L) := by
        rw [hq_def, ← Complex.exp_nat_mul, ← Complex.exp_add]
        congr 1
        simp only [w]; push_cast; field_simp; ring
      simp only [g, this]; ring
    rw [hg2.unique (hasSum_fintype _), show k + 2 - 1 = k + 1 by omega, ← hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hC, div_pow]; ring
  rw [← hval]
  refine hlim.congr fun R => Finset.sum_congr rfl fun d _ => ?_
  simp [f, htrm]

end GlobalTheory.EisM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LipschitzFormulaPeriodicWeightStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lipschitz_formula_periodic_weight : ∀ (j L : ℕ) (φ : ZMod L → ℂ) (z : ℂ), 2 ≤ j → 0 < L → 0 < z.im → Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R : ℤ)) R, φ (d : ZMod L) * trm j 0 (z + d)) atTop (𝓝 ((-2 * π * Complex.I / L) ^ j / (j - 1).factorial * ∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (j - 1) * hat φ (m + 1 : ℕ) * cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L))) := by
  first | exact @GlobalTheory.EisM.lipschitz_periodic | exact GlobalTheory.EisM.lipschitz_periodic | (intros; apply GlobalTheory.EisM.lipschitz_periodic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumQExpansion
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section
namespace GlobalTheory.LatQ

theorem hat_bounded (L : ℕ) (φ : ZMod L → ℂ) : ∃ C : ℝ, ∀ x, ‖hat φ x‖ ≤ C := by
  refine ⟨∑ y ∈ Finset.range L, ‖φ (y : ZMod L)‖, fun x => ?_⟩
  unfold hat
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [norm_mul]
  have : ‖cexp (2 * π * Complex.I * ((y : ℂ) * (x : ℂ)) / (L : ℂ))‖ = 1 := by
    have h : (2 * π * Complex.I * ((y : ℂ) * (x : ℂ)) / (L : ℂ)) = ((2 * π * y * x / L : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  rw [this, mul_one]

theorem trm_zero_eq (j : ℕ) (w : ℂ) : trm j 0 w = (w ^ j)⁻¹ := by
  simp [trm]

theorem trm_neg (j : ℕ) (w : ℂ) : trm j 0 (-w) = (-1) ^ j * trm j 0 w := by
  rw [trm_zero_eq, trm_zero_eq, neg_pow, mul_inv, ← inv_pow, inv_neg, inv_one]

theorem trm_tendsto (j : ℕ) (hj : 1 ≤ j) (z : ℂ) :
    Tendsto (fun d : ℤ => trm j 0 (z + d)) cofinite (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun d : ℤ => |(d : ℝ)|) cofinite atTop :=
    (tendsto_norm_cocompact_atTop.comp Int.tendsto_coe_cofinite)
  have h2 : Tendsto (fun d : ℤ => ‖z + d‖) cofinite atTop := by
    refine tendsto_atTop_mono (fun d => ?_) (tendsto_atTop_add_const_right _ (-‖z‖) h1)
    have := norm_sub_norm_le ((d : ℂ)) (-z)
    simp only [Complex.norm_intCast, norm_neg, sub_neg_eq_add] at this
    linarith [show ‖(d : ℂ) + z‖ = ‖z + d‖ by rw [add_comm]]
  have h3 : Tendsto (fun d : ℤ => ‖z + d‖ ^ j) cofinite atTop :=
    (tendsto_pow_atTop (by omega)).comp h2
  refine h3.inv_tendsto_atTop.congr (fun d => ?_)
  simp [trm_zero_eq, norm_inv, norm_pow]

theorem sum_range_eq_univ (L : ℕ) (hL : 0 < L) (φ : ZMod L → ℂ) (f : ℕ → ZMod L)
    (hf : Set.InjOn f (Finset.range L)) :
    haveI : NeZero L := ⟨hL.ne'⟩;
    ∑ r ∈ Finset.range L, φ (f r) = ∑ y, φ y := by
  haveI : NeZero L := ⟨hL.ne'⟩
  rw [← Finset.sum_image (fun x hx y hy h => hf hx hy h)]
  congr 1
  apply Finset.eq_univ_of_card
  rw [Finset.card_image_of_injOn hf, Finset.card_range, ZMod.card]

theorem kills (L : ℕ) (hL : 0 < L) (φ : ZMod L → ℂ) (d : ℤ) :
    ∑ r ∈ Finset.range L, φ ((d - r : ℤ) : ZMod L) = hat φ 0 := by
  have h1 : hat φ 0 = ∑ y ∈ Finset.range L, φ (y : ZMod L) := by simp [hat]
  rw [h1, sum_range_eq_univ L hL φ, sum_range_eq_univ L hL φ]
  · intro a ha b hb h
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have := congrArg ZMod.val h
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
    exact this
  · intro a ha b hb h
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
    have h2 : (d - (b : ℤ)) - (d - (a : ℤ)) = (a : ℤ) - b := by ring
    rw [h2] at h
    have h3 := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
    omega

theorem phi_bounded (L : ℕ) (hL : 0 < L) (φ : ZMod L → ℂ) : ∃ C : ℝ, ∀ y, ‖φ y‖ ≤ C := by
  haveI : NeZero L := ⟨hL.ne'⟩
  exact ⟨∑ y, ‖φ y‖, fun y => Finset.single_le_sum (f := fun y => ‖φ y‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ y)⟩

theorem latF_mul (L : ℕ) (hL : 0 < L) (b : ℤ → ℂ) (φ : ZMod L → ℂ) (k d : ℤ) :
    latF L b φ (k * L, d) = b k * φ (d : ZMod L) := by
  have : (L : ℤ) ≠ 0 := by exact_mod_cast hL.ne'
  simp [latF, Int.mul_ediv_cancel _ this]

theorem latF_ndvd (L : ℕ) (b : ℤ → ℂ) (φ : ZMod L → ℂ) (x : ℤ × ℤ) (h : ¬ (L : ℤ) ∣ x.1) :
    latF L b φ x = 0 := by
  simp [latF, h]

theorem row_summable (j L : ℕ) (hj : 1 ≤ j) (hL : 0 < L) (A : ℤ → ℂ) (hA : ∃ C : ℝ, ∀ d, ‖A d‖ ≤ C) (τ : ℍ) (c : ℤ) :
    Summable fun d : ℤ => A d * dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) (c, d) := by
  obtain ⟨C, hC⟩ := hA
  have hs := (GlobalTheory.T.summable_regularizedEisensteinLatticeTerm j L (0, 1) τ hj hL).prod_factor c
  refine (hs.mul_left C).of_norm_bounded (fun d => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC d) (norm_nonneg _)

theorem row_lim (j L : ℕ) (b : ℤ → ℂ) (φ : ZMod L → ℂ) (hj : 1 ≤ j) (hL : 0 < L) (h0 : hat φ 0 = 0)
    (τ : ℍ) (k : ℤ) :
    Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R : ℤ)) R, b k * φ (d : ZMod L) * trm j 0 (((k * L : ℤ) : ℂ) * τ + d))
      atTop (𝓝 (∑' d : ℤ, latF L b φ (k * L, d) *
        dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) (k * L, d))) := by
  simp_rw [latF_mul L hL b φ k]
  obtain ⟨C, hC⟩ := phi_bounded L hL φ
  have hA : ∃ C : ℝ, ∀ d : ℤ, ‖b k * φ (d : ZMod L)‖ ≤ C :=
    ⟨‖b k‖ * C, fun d => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)⟩
  have hK : ∀ d : ℤ, ∑ r ∈ Finset.range L, b k * φ (((d - r : ℤ)) : ZMod L) = 0 := by
    intro d; rw [← Finset.mul_sum, kills L hL φ d, h0, mul_zero]
  exact GlobalTheory.RowLim.rowlim L (fun d => b k * φ (d : ZMod L)) (fun d => trm j 0 (((k * L : ℤ) : ℂ) * τ + d))
    (fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) (k * L) hL hA hK (fun d => rfl)
    (trm_tendsto j hj _) (row_summable j L hj hL _ hA τ _)

theorem lip_all (j L : ℕ) (φ : ZMod L → ℂ) (z : ℂ) (hj : 1 ≤ j) (hL : 0 < L) (hz : 0 < z.im) (h0 : hat φ 0 = 0) :
    Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R : ℤ)) R, φ (d : ZMod L) * trm j 0 (z + d)) atTop
      (𝓝 ((-2 * π * Complex.I / L) ^ j / (j - 1).factorial *
        ∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (j - 1) * hat φ (m + 1 : ℕ) * cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L))) := by
  rcases (show j = 1 ∨ 2 ≤ j by omega) with rfl | hj2
  · convert GlobalTheory.T.lipschitz_weight_one_periodic_mean_zero L φ z hL hz h0 using 2
    simp
  · exact GlobalTheory.T.lipschitz_formula_periodic_weight j L φ z hj2 hL hz

theorem row_pos (j L : ℕ) (b : ℤ → ℂ) (φ : ZMod L → ℂ) (hj : 1 ≤ j) (hL : 0 < L) (h0 : hat φ 0 = 0)
    (τ : ℍ) (n : ℕ) :
    ∑' d : ℤ, latF L b φ (((n + 1 : ℕ) : ℤ) * L, d) *
        dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) (((n + 1 : ℕ) : ℤ) * L, d) =
      (-2 * π * Complex.I / L) ^ j / (j - 1).factorial *
        (b (n + 1 : ℕ) * ∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (j - 1) * hat φ (m + 1 : ℕ) *
          cexp (2 * π * Complex.I * (m + 1 : ℕ) * ((n + 1 : ℕ) * τ))) := by
  have hlim := row_lim j L b φ hj hL h0 τ ((n + 1 : ℕ) : ℤ)
  have hz : 0 < ((((((n + 1 : ℕ) : ℤ) * L : ℤ)) : ℂ) * (τ : ℂ)).im := by
    have : (((((n + 1 : ℕ) : ℤ) * L : ℤ)) : ℂ) = (((n + 1 : ℕ) * L : ℕ) : ℝ) := by push_cast; ring
    rw [this, Complex.im_ofReal_mul]
    exact mul_pos (by exact_mod_cast Nat.mul_pos (Nat.succ_pos n) hL) τ.im_pos
  have h2 := (lip_all j L φ _ hj hL hz h0).const_mul (b ((n + 1 : ℕ) : ℤ))
  have h3 : (fun R : ℕ => b ((n + 1 : ℕ) : ℤ) * ∑ d ∈ Finset.Icc (-(R : ℤ)) R,
      φ (d : ZMod L) * trm j 0 (((((n + 1 : ℕ) : ℤ) * L : ℤ) : ℂ) * τ + d)) =
      (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R : ℤ)) R,
        b ((n + 1 : ℕ) : ℤ) * φ (d : ZMod L) * trm j 0 (((((n + 1 : ℕ) : ℤ) * L : ℤ) : ℂ) * τ + d)) := by
    funext R; rw [Finset.mul_sum]; simp_rw [mul_assoc]
  rw [h3] at h2
  rw [tendsto_nhds_unique hlim h2]
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have h4 : ∀ m : ℕ, cexp (2 * π * Complex.I * ((m + 1 : ℕ) : ℂ) * ((((((n + 1 : ℕ) : ℤ) * L : ℤ)) : ℂ) * τ) / L) =
      cexp (2 * π * Complex.I * ((m + 1 : ℕ) : ℂ) * (((n + 1 : ℕ) : ℂ) * τ)) := by
    intro m; congr 1; push_cast; field_simp
  simp_rw [h4]
  ring

theorem row_neg (j L : ℕ) (b : ℤ → ℂ) (φ : ZMod L → ℂ) (hj : 1 ≤ j) (hL : 0 < L) (h0 : hat φ 0 = 0)
    (hpar : ∀ x y : ℤ, b (-x) * φ (-(y : ZMod L)) = (-1) ^ j * (b x * φ y)) (τ : ℍ) (k : ℤ) :
    ∑' d : ℤ, latF L b φ ((-k) * L, d) *
        dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) ((-k) * L, d) =
    ∑' d : ℤ, latF L b φ (k * L, d) *
        dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) (k * L, d) := by
  refine tendsto_nhds_unique (row_lim j L b φ hj hL h0 τ (-k)) ?_
  refine (row_lim j L b φ hj hL h0 τ k).congr (fun R => ?_)
  refine Finset.sum_nbij' (fun d => -d) (fun d => -d) ?_ ?_ ?_ ?_ ?_
  · intro d hd; simp only [Finset.mem_Icc] at hd ⊢; omega
  · intro d hd; simp only [Finset.mem_Icc] at hd ⊢; omega
  · intro d _; simp
  · intro d _; simp
  · intro d _
    have e1 : (((-k) * L : ℤ) : ℂ) * τ + ((-d : ℤ) : ℂ) = -(((k * L : ℤ) : ℂ) * τ + (d : ℂ)) := by push_cast; ring
    have e2 := hpar k d
    rw [e1, trm_neg, show ((-d : ℤ) : ZMod L) = -(d : ZMod L) by push_cast; rfl]
    have : ((-1 : ℂ) ^ j) * (-1) ^ j = 1 := by rw [← mul_pow]; norm_num
    linear_combination (-((-1 : ℂ) ^ j * trm j 0 (((k * L : ℤ) : ℂ) * τ + (d : ℂ)))) * e2 -
      (b k * φ (d : ZMod L) * trm j 0 (((k * L : ℤ) : ℂ) * τ + (d : ℂ))) * this

theorem row_zero_indep (j L : ℕ) (b : ℤ → ℂ) (φ : ZMod L → ℂ) (τ τ' : ℍ) :
    ∑' d : ℤ, latF L b φ ((0 : ℤ) * L, d) *
        dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) ((0 : ℤ) * L, d) =
    ∑' d : ℤ, latF L b φ ((0 : ℤ) * L, d) *
        dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ' + y.2)) ((0 : ℤ) * L, d) := by
  congr 1; funext d; congr 1
  simp [dif]

theorem latF_bounded (L : ℕ) (hL : 0 < L) (b : ℤ → ℂ) (φ : ZMod L → ℂ) (hb : ∃ C : ℝ, ∀ x, ‖b x‖ ≤ C) :
    ∃ C : ℝ, ∀ x, ‖latF L b φ x‖ ≤ C := by
  obtain ⟨Cb, hCb⟩ := hb
  obtain ⟨Cφ, hCφ⟩ := phi_bounded L hL φ
  have hb0 : 0 ≤ Cb := (norm_nonneg _).trans (hCb 0)
  have hφ0 : 0 ≤ Cφ := (norm_nonneg _).trans (hCφ 0)
  refine ⟨Cb * Cφ, fun x => ?_⟩
  unfold latF; split_ifs
  · rw [norm_mul]; exact mul_le_mul (hCb _) (hCφ _) (norm_nonneg _) hb0
  · simp only [norm_zero]; positivity

theorem tsum_rows (L : ℕ) (hL : 0 < L) (F : ℤ → ℂ) (κ S : ℂ) (T : ℕ → ℂ) (hFs : Summable F)
    (hz : ∀ k, ¬ (L : ℤ) ∣ k → F k = 0) (hneg : ∀ k : ℤ, F ((-k) * L) = F (k * L))
    (hpos : ∀ n : ℕ, F (((n + 1 : ℕ) : ℤ) * L) = κ * T n) (hT : HasSum T S) :
    ∑' k, F k = F ((0 : ℤ) * L) + 2 * κ * S := by
  have hinj : Function.Injective (fun n : ℤ => n * (L : ℤ)) :=
    fun x y h => mul_right_cancel₀ (by exact_mod_cast hL.ne' : (L : ℤ) ≠ 0) h
  have hsupp : Function.support F ⊆ Set.range (fun n : ℤ => n * (L : ℤ)) := by
    intro k hk
    by_contra hn
    exact hk (hz k fun ⟨n, hn'⟩ => hn ⟨n, by rw [hn', mul_comm]⟩)
  rw [← hinj.tsum_eq hsupp]
  have hg : Summable fun n : ℤ => F (n * L) := hFs.comp_injective hinj
  have hsucc : Function.Injective (fun n : ℕ => (n : ℤ) + 1) := fun x y h => by simpa using h
  have hnsucc : Function.Injective (fun n : ℕ => -((n : ℤ) + 1)) := fun x y h => by simpa using h
  rw [tsum_of_add_one_of_neg_add_one (f := fun n : ℤ => F (n * L)) (hg.comp_injective hsucc) (hg.comp_injective hnsucc)]
  have hpos' : ∀ n : ℕ, F (((n : ℤ) + 1) * L) = κ * T n := fun n => by rw [← hpos n, Nat.cast_succ]
  simp only [hneg, hpos', tsum_mul_left, hT.tsum_eq]
  ring

theorem lat_qexp : ∀ (j L : ℕ) (b : ℤ → ℂ) (φ : ZMod L → ℂ), 1 ≤ j → 0 < L → (∃ C : ℝ, ∀ x, ‖b x‖ ≤ C) →
    hat φ 0 = 0 → (∀ x y : ℤ, b (-x) * φ (-(y : ZMod L)) = (-1) ^ j * (b x * φ y)) →
    ∃ c : ℂ, PolyB (eis j c (hat φ) b) ∧ ∀ τ : ℍ, lat j 0 L (0, 1) (latF L b φ) τ =
      2 * (-2 * π * Complex.I / L) ^ j / (j - 1).factorial * qs (eis j c (hat φ) b) τ := by
  intro j L b φ hj hL hb h0 hpar
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hκ : ((-2 * π * Complex.I / L) ^ j / (j - 1).factorial : ℂ) ≠ 0 := by
    refine div_ne_zero (pow_ne_zero _ (div_ne_zero ?_ hL')) (by exact_mod_cast (Nat.factorial_pos _).ne')
    refine mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  generalize hκdef : ((-2 * π * Complex.I / L) ^ j / (j - 1).factorial : ℂ) = κ at hκ
  obtain ⟨K, hK⟩ : ∃ K : ℂ, ∀ τ : ℍ, ∑' d : ℤ, latF L b φ ((0 : ℤ) * L, d) *
      dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) ((0 : ℤ) * L, d) = K :=
    ⟨_, fun τ => row_zero_indep j L b φ τ UpperHalfPlane.I⟩
  refine ⟨K / (2 * κ), (GlobalTheory.T.coeffEisensteinSeriesTwisted_qExpansion_double j _ (hat φ) b (hat_bounded L φ) hb).1, fun τ => ?_⟩
  have hq := (GlobalTheory.T.coeffEisensteinSeriesTwisted_qExpansion_double j (K / (2 * κ)) (hat φ) b (hat_bounded L φ) hb).2.2 τ
  obtain ⟨CΦ, hCΦ⟩ := latF_bounded L hL b φ hb
  have hs : Summable fun x : ℤ × ℤ => latF L b φ x *
      dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) x := by
    refine ((GlobalTheory.T.summable_regularizedEisensteinLatticeTerm j L (0, 1) τ hj hL).mul_left CΦ).of_norm_bounded (fun x => ?_)
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hCΦ x) (norm_nonneg _)
  have hrows := tsum_rows L hL (fun k => ∑' d : ℤ, latF L b φ (k, d) *
      dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) (k, d)) κ _ _ hs.prod
    (fun k hk => by simp only [latF_ndvd L b φ (k, _) hk, zero_mul, tsum_zero])
    (fun k => row_neg j L b φ hj hL h0 hpar τ k)
    (fun n => by rw [← hκdef]; exact row_pos j L b φ hj hL h0 τ n) hq
  have e : (2 * (-2 * π * Complex.I / L) ^ j / (j - 1).factorial : ℂ) = 2 * κ := by rw [← hκdef]; ring
  rw [e, lat, hs.tsum_prod, hrows]
  beta_reduce
  rw [hK τ]
  field_simp
  ring

end GlobalTheory.LatQ

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumQExpansionStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularizedEisensteinLatticeSum_qExpansion : ∀ (j L : ℕ) (b : ℤ → ℂ) (φ : ZMod L → ℂ), 1 ≤ j → 0 < L → (∃ C : ℝ, ∀ x, ‖b x‖ ≤ C) → hat φ 0 = 0 → (∀ x y : ℤ, b (-x) * φ (-(y : ZMod L)) = (-1) ^ j * (b x * φ y)) → ∃ c : ℂ, PolyB (eis j c (hat φ) b) ∧ ∀ τ : ℍ, lat j 0 L (0, 1) (latF L b φ) τ = 2 * (-2 * π * Complex.I / L) ^ j / (j - 1).factorial * qs (eis j c (hat φ) b) τ := by
  first | exact @GlobalTheory.LatQ.lat_qexp | exact GlobalTheory.LatQ.lat_qexp | (intros; apply GlobalTheory.LatQ.lat_qexp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinLatticeFunctionIsModularFormCoeffSeq
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisForm

lemma sum_shift (L : ℕ) [NeZero L] (φ : ZMod L → ℂ) (u e : ZMod L) (he : IsUnit e) :
    ∑ r ∈ Finset.range L, φ (u + (r : ZMod L) * e) = ∑ y, φ y := by
  rw [Finset.sum_range (fun r => φ (u + (r : ZMod L) * e))]
  refine Fintype.sum_bijective (fun i : Fin L => u + ((i : ℕ) : ZMod L) * e) ?_ _ _ (fun _ => rfl)
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp [ZMod.card]⟩
  intro i i' h
  simp only [add_right_inj] at h
  have h' := he.mul_right_cancel h
  rw [ZMod.natCast_eq_natCast_iff'] at h'
  ext
  rwa [Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt i'.2] at h'

lemma hat_zero (L : ℕ) [NeZero L] (φ : ZMod L → ℂ) : hat φ 0 = ∑ y, φ y := by
  have := sum_shift L φ 0 1 isUnit_one
  simp only [zero_add, mul_one] at this
  rw [← this]; simp [hat]

lemma bdd_of_periodic (L₂ : ℕ) (hL : 0 < L₂) (b : ℤ → ℂ) (hb : ∀ x, b (x + L₂) = b x) :
    ∃ C : ℝ, ∀ x, ‖b x‖ ≤ C := by
  have hp : Function.Periodic b (L₂ : ℤ) := hb
  have hpz : ∀ y n : ℤ, b (y + n * L₂) = b y := fun y n => by simpa using hp.int_mul n y
  refine ⟨∑ i ∈ Finset.range L₂, ‖b i‖, fun x => ?_⟩
  have h1 := Int.emod_nonneg x (by omega : (L₂ : ℤ) ≠ 0)
  have h2 := Int.emod_lt_of_pos x (by omega : (0 : ℤ) < L₂)
  have e : b x = b (((x % L₂).toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg h1, ← hpz (x % L₂) (x / L₂)]
    congr 1
    rw [Int.emod_def]; ring
  rw [e]
  exact Finset.single_le_sum (f := fun i : ℕ => ‖b i‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_range.mpr (by omega))

lemma latF_trans (L₁ L₂ : ℕ) (hL₁ : 0 < L₁) (b χ₁ χ₂ : ℤ → ℂ) (φ : ZMod L₁ → ℂ)
    (hb : ∀ x, b (x + L₂) = b x)
    (hχ : ∀ d : ℤ, IsCoprime d (L₁ * L₂ : ℕ) → (∀ y, φ y = χ₁ d * φ (y * d)) ∧ ∀ x, b (x * d) = χ₂ d * b x)
    (a b' k d : ℤ) (hdet : a * d - b' * (L₁ * L₂ * k) = 1) (x : ℤ × ℤ) :
    latF L₁ b φ x = χ₁ d * χ₂ d * latF L₁ b φ (x.1 * a + x.2 * (L₁ * L₂ * k), x.1 * b' + x.2 * d) := by
  have hp : Function.Periodic b (L₂ : ℤ) := hb
  have hpz : ∀ y n : ℤ, b (y + n * L₂) = b y := fun y n => by simpa using hp.int_mul n y
  have hL : (L₁ : ℤ) ≠ 0 := by exact_mod_cast hL₁.ne'
  have hcop : IsCoprime d ((L₁ * L₂ : ℕ) : ℤ) := ⟨a, -(b' * k), by push_cast; linear_combination hdet⟩
  obtain ⟨hφ, hbχ⟩ := hχ d hcop
  have hcopa : IsCoprime (L₁ : ℤ) a := ⟨-(b' * L₂ * k), d, by linear_combination hdet⟩
  unfold latF
  by_cases h : (L₁ : ℤ) ∣ x.1
  · obtain ⟨m, hm⟩ := h
    have h2 : (L₁ : ℤ) ∣ x.1 * a + x.2 * (L₁ * L₂ * k) := ⟨m * a + x.2 * L₂ * k, by rw [hm]; ring⟩
    rw [if_pos ⟨m, hm⟩, if_pos h2]
    have e1 : x.1 / L₁ = m := by rw [hm, Int.mul_ediv_cancel_left _ hL]
    have e2 : (x.1 * a + x.2 * (L₁ * L₂ * k)) / L₁ = m * a + (x.2 * k) * L₂ := by
      rw [show x.1 * a + x.2 * (L₁ * L₂ * k) = L₁ * (m * a + (x.2 * k) * L₂) by rw [hm]; ring,
        Int.mul_ediv_cancel_left _ hL]
    have e3 : (((x.1 * b' + x.2 * d : ℤ)) : ZMod L₁) = (x.2 : ZMod L₁) * (d : ZMod L₁) := by
      rw [hm]; push_cast; rw [ZMod.natCast_self]; ring
    rw [e1, e2, e3, hpz]
    have e4 : b m = χ₂ d * b (m * a) := by
      rw [← hbχ, ← hpz m (m * b' * L₁ * k)]
      congr 1
      linear_combination (-m) * hdet
    rw [e4, hφ (x.2 : ZMod L₁)]; ring
  · have h2 : ¬ (L₁ : ℤ) ∣ x.1 * a + x.2 * (L₁ * L₂ * k) := by
      intro h2; apply h
      have h3 : (L₁ : ℤ) ∣ x.2 * (L₁ * L₂ * k) := ⟨x.2 * L₂ * k, by ring⟩
      exact hcopa.dvd_of_dvd_mul_right ((dvd_add_left h3).mp h2)
    rw [if_neg h, if_neg h2, mul_zero]

lemma latF_kills (L₁ L₂ : ℕ) (hL₁ : 0 < L₁) (b : ℤ → ℂ) (φ : ZMod L₁ → ℂ)
    (hb : ∀ x, b (x + L₂) = b x) (hhat : hat φ 0 = 0) (k d : ℤ) (hd : IsUnit (d : ZMod L₁)) :
    Kills L₁ (L₁ * L₂ * k, d) (latF L₁ b φ) := by
  haveI : NeZero L₁ := ⟨hL₁.ne'⟩
  have hp : Function.Periodic b (L₂ : ℤ) := hb
  have hpz : ∀ y n : ℤ, b (y + n * L₂) = b y := fun y n => by simpa using hp.int_mul n y
  have hL : (L₁ : ℤ) ≠ 0 := by exact_mod_cast hL₁.ne'
  rw [hat_zero] at hhat
  intro x
  by_cases h : (L₁ : ℤ) ∣ x.1
  · obtain ⟨m, hm⟩ := h
    calc ∑ r ∈ Finset.range L₁, latF L₁ b φ (x - (r : ℤ) • ((L₁ : ℤ) * L₂ * k, d))
        = ∑ r ∈ Finset.range L₁, b m * φ ((x.2 : ZMod L₁) + (r : ZMod L₁) * (-(d : ZMod L₁))) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          simp only [latF, Prod.fst_sub, Prod.snd_sub, Prod.smul_mk, smul_eq_mul]
          rw [if_pos ⟨m - r * L₂ * k, by rw [hm]; ring⟩,
            show x.1 - (r : ℤ) * (L₁ * L₂ * k) = L₁ * (m + (-(r * k)) * L₂) by rw [hm]; ring,
            Int.mul_ediv_cancel_left _ hL, hpz]
          congr 2; push_cast; ring
      _ = 0 := by rw [← Finset.mul_sum, sum_shift L₁ φ _ _ hd.neg, hhat, mul_zero]
  · refine Finset.sum_eq_zero fun r _ => ?_
    simp only [latF, Prod.fst_sub, Prod.snd_sub, Prod.smul_mk, smul_eq_mul]
    rw [if_neg]
    intro h2; apply h
    have h3 : (L₁ : ℤ) ∣ (r : ℤ) * (L₁ * L₂ * k) := ⟨r * L₂ * k, by ring⟩
    simpa using dvd_add h2 h3

end GlobalTheory.EisForm

namespace GlobalTheory.EisForm

theorem eis_latF_mf : ∀ (j L₁ L₂ : ℕ) (b χ₁ χ₂ : ℤ → ℂ) (φ : ZMod L₁ → ℂ), 1 ≤ j → 0 < L₁ → 0 < L₂ → hat φ 0 = 0 →
    (∀ x, b (x + L₂) = b x) →
    (∀ d : ℤ, IsCoprime d (L₁ * L₂ : ℕ) → (∀ y, φ y = χ₁ d * φ (y * d)) ∧ ∀ x, b (x * d) = χ₂ d * b x) →
    χ₁ (-1) * χ₂ (-1) = (-1) ^ j →
    ∃ c : ℂ, MF j (L₁ * L₂) (fun d => χ₁ d * χ₂ d) (eis j c (hat φ) b) ∧
      ∀ τ : ℍ, lat j 0 L₁ (0, 1) (latF L₁ b φ) τ = 2 * (-2 * π * Complex.I / L₁) ^ j / (j - 1).factorial * qs (eis j c (hat φ) b) τ := by
  intro j L₁ L₂ b χ₁ χ₂ φ hj hL₁ hL₂ hhat hb hχ hpar
  haveI : NeZero L₁ := ⟨hL₁.ne'⟩
  obtain ⟨Cb, hCb⟩ := bdd_of_periodic L₂ hL₂ b hb
  have hparity : ∀ x y : ℤ, b (-x) * φ (-(y : ZMod L₁)) = (-1) ^ j * (b x * φ y) := by
    intro x y
    obtain ⟨hφ, hbb⟩ := hχ (-1) ⟨-1, 0, by ring⟩
    have h1 := hφ (-(y : ZMod L₁))
    have h2 := hbb x
    rw [show -(y : ZMod L₁) * ((-1 : ℤ) : ZMod L₁) = y by push_cast; ring] at h1
    rw [mul_neg_one] at h2
    rw [h1, h2, ← hpar]; ring
  obtain ⟨c, hP, hq⟩ := GlobalTheory.T.regularizedEisensteinLatticeSum_qExpansion j L₁ b φ hj hL₁ ⟨Cb, hCb⟩ hhat hparity
  refine ⟨c, ⟨hP, ?_⟩, hq⟩
  set K : ℂ := 2 * (-2 * π * Complex.I / L₁) ^ j / (j - 1).factorial with hKdef
  have hK : K ≠ 0 := by
    have hL : (L₁ : ℂ) ≠ 0 := by exact_mod_cast hL₁.ne'
    simp [hKdef, Real.pi_ne_zero, Complex.I_ne_zero, hL, Nat.factorial_ne_zero]
  set Φ := latF L₁ b φ with hΦ
  have hq' : ∀ τ, qs (eis j c (hat φ) b) τ = K⁻¹ * lat j 0 L₁ (0, 1) Φ τ := fun τ => by
    rw [hq τ, ← mul_assoc, inv_mul_cancel₀ hK, one_mul]
  have hΦb : ∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C := by
    have hC0 : 0 ≤ Cb := le_trans (norm_nonneg _) (hCb 0)
    refine ⟨Cb * ∑ y, ‖φ y‖, fun x => ?_⟩
    simp only [hΦ, latF]
    split_ifs
    · rw [norm_mul]
      exact mul_le_mul (hCb _) (Finset.single_le_sum (f := fun y => ‖φ y‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ _)) (norm_nonneg _) hC0
    · simpa using mul_nonneg hC0 (Finset.sum_nonneg fun y _ => norm_nonneg (φ y))
  intro γ hc τ
  obtain ⟨k, hk⟩ := hc
  push_cast at hk
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * ((L₁ : ℤ) * L₂ * k) = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    rw [← hk]; exact this
  have hunit : IsUnit ((γ 1 1 : ℤ) : ZMod L₁) := by
    refine isUnit_iff_exists_inv.mpr ⟨((γ 0 0 : ℤ) : ZMod L₁), ?_⟩
    have := congrArg (fun z : ℤ => (z : ZMod L₁)) hdet
    push_cast at this
    rw [ZMod.natCast_self] at this
    linear_combination this
  set χd := χ₁ (γ 1 1) * χ₂ (γ 1 1) with hχd
  have htr : ∀ x : ℤ × ℤ, (fun y => χd * Φ y) (x.1 * γ 0 0 + x.2 * γ 1 0, x.1 * γ 0 1 + x.2 * γ 1 1) = Φ x := by
    intro x
    have := latF_trans L₁ L₂ hL₁ b χ₁ χ₂ φ hb hχ (γ 0 0) (γ 0 1) k (γ 1 1) hdet x
    rw [← hk] at this
    exact this.symm
  have hlin : ∀ w, lat j 0 L₁ w (fun y => χd * Φ y) τ = χd * lat j 0 L₁ w Φ τ := by
    intro w
    unfold lat
    rw [← tsum_mul_left]
    congr 1; ext x; ring
  have hw : ((0 : ℤ) * γ 0 0 + 1 * γ 1 0, (0 : ℤ) * γ 0 1 + 1 * γ 1 1) = ((L₁ : ℤ) * L₂ * k, γ 1 1) := by
    simp [hk]
  have hk1 : Kills L₁ ((L₁ : ℤ) * L₂ * k, γ 1 1) Φ := latF_kills L₁ L₂ hL₁ b φ hb hhat k (γ 1 1) hunit
  have hk0 : Kills L₁ (0, 1) Φ := by
    simpa using latF_kills L₁ L₂ hL₁ b φ hb hhat 0 1 (by simp)
  rw [hq', hq', GlobalTheory.T.regularizedEisensteinLatticeSum_slTwo_smul j L₁ (0, 1) Φ (fun y => χd * Φ y) γ τ htr, hlin]
  simp only [Prod.fst, Prod.snd]
  rw [hw, GlobalTheory.T.regularizedEisensteinLatticeSum_direction_indep j L₁ _ (0, 1) Φ τ hj hL₁ hΦb hk1 hk0]
  ring

end GlobalTheory.EisForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinLatticeFunctionIsModularFormCoeffSeqStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_latticeFunction_isModularFormCoeffSeq : ∀ (j L₁ L₂ : ℕ) (b χ₁ χ₂ : ℤ → ℂ) (φ : ZMod L₁ → ℂ), 1 ≤ j → 0 < L₁ → 0 < L₂ → hat φ 0 = 0 → (∀ x, b (x + L₂) = b x) → (∀ d : ℤ, IsCoprime d (L₁ * L₂ : ℕ) → (∀ y, φ y = χ₁ d * φ (y * d)) ∧ ∀ x, b (x * d) = χ₂ d * b x) → χ₁ (-1) * χ₂ (-1) = (-1) ^ j → ∃ c : ℂ, MF j (L₁ * L₂) (fun d => χ₁ d * χ₂ d) (eis j c (hat φ) b) ∧ ∀ τ : ℍ, lat j 0 L₁ (0, 1) (latF L₁ b φ) τ = 2 * (-2 * π * Complex.I / L₁) ^ j / (j - 1).factorial * qs (eis j c (hat φ) b) τ := by
  first | exact @GlobalTheory.EisForm.eis_latF_mf | exact GlobalTheory.EisForm.eis_latF_mf | (intros; apply GlobalTheory.EisForm.eis_latF_mf <;> assumption)
end
