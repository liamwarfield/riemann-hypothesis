module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeYDerivativeTermIntegralPolynomialDecay

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivHeckePhiFourierTransformBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivHeckePhiFourierTransformBound
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo.TermBoundDeriv

theorem rpow_le_add_inv_pow {t r : ℝ} {s : ℕ} (ht : 0 < t) (hr : |r| ≤ s) :
    t ^ r ≤ (t + t⁻¹) ^ s := by
  have hti : 0 < t⁻¹ := inv_pos.mpr ht
  have hM1 : 1 ≤ t + t⁻¹ := by
    rcases le_total 1 t with h | h
    · linarith
    · have : 1 ≤ t⁻¹ := one_le_inv_iff₀.mpr ⟨ht, h⟩
      linarith
  have hsr : (t + t⁻¹) ^ (s : ℝ) = (t + t⁻¹) ^ s := Real.rpow_natCast _ _
  rw [← hsr]
  rcases le_total 0 r with h0 | h0
  · calc t ^ r ≤ (t + t⁻¹) ^ r := Real.rpow_le_rpow ht.le (by linarith) h0
      _ ≤ (t + t⁻¹) ^ (s : ℝ) := Real.rpow_le_rpow_of_exponent_le hM1 (le_trans (le_abs_self r) hr)
  · have e : t ^ r = t⁻¹ ^ (-r) := by
      rw [Real.inv_rpow ht.le, Real.rpow_neg ht.le, inv_inv]
    rw [e]
    calc t⁻¹ ^ (-r) ≤ (t + t⁻¹) ^ (-r) := Real.rpow_le_rpow hti.le (by linarith) (by linarith)
      _ ≤ (t + t⁻¹) ^ (s : ℝ) := Real.rpow_le_rpow_of_exponent_le hM1 (le_trans (neg_le_abs r) hr)

end GlobalTheory.HeckeTwo.TermBoundDeriv

namespace GlobalTheory.HeckeTwo.TermBoundDeriv

theorem iteratedDeriv_hTrans_bound :
    (∀ j : ℕ, ∃ (S : Finset (ℕ × ℕ × ℕ)) (P : ℕ × ℕ × ℕ → Polynomial ℂ),
    (∀ p ∈ S, 2 ≤ p.1 + 2 * p.2.1 ∧ p.1 + 2 * p.2.1 = p.2.2 + 2 + j) ∧
    ∀ σ ∈ halfPlane, ∀ ν y : ℝ, y ≠ 0 →
      iteratedDeriv j (hTrans σ ν) y = ∑ p ∈ S, (P p).eval σ * GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y) → (∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ a b m : ℕ, 2 ≤ a + 2 * b → ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖GlobalTheory.HeckeTwo.TermSmooth.intT σ ν a b m y‖ ≤ C * |y| ^ ((m : ℝ) + 1 - a - 2 * b - 2 * σ.re) / (1 + |ν * y|) ^ N) →
  ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ j : ℕ, ∃ s : ℕ, ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖iteratedDeriv j (hTrans σ ν) y‖ ≤ C * (|y| + |y|⁻¹) ^ s / (1 + |ν * y|) ^ N := by
  intro hder hint K hK hKH j
  obtain ⟨S, P, hS, hEq⟩ := hder j
  obtain ⟨R, hR⟩ : ∃ R, ∀ σ ∈ K, ‖σ‖ ≤ R := hK.isBounded.exists_norm_le
  refine ⟨⌈1 + (j : ℝ) + 2 * R⌉₊, fun N => ?_⟩
  have hCex : ∀ p : ℕ × ℕ × ℕ, ∃ C : ℝ, 0 ≤ C ∧ (p ∈ S → ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y‖ ≤
        C * |y| ^ ((p.2.2 : ℝ) + 1 - p.1 - 2 * p.2.1 - 2 * σ.re) / (1 + |ν * y|) ^ N) := by
    intro p
    by_cases hp : p ∈ S
    · obtain ⟨C, hC⟩ := hint K hK hKH p.1 p.2.1 p.2.2 (hS p hp).1 N
      refine ⟨max C 0, le_max_right _ _, fun _ σ hσ ν y hν hy => (hC σ hσ ν y hν hy).trans ?_⟩
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity)
    · exact ⟨0, le_rfl, fun h => absurd h hp⟩
  choose Cp hCp0 hCp using hCex
  have hBex : ∀ p : ℕ × ℕ × ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ σ ∈ K, ‖(P p).eval σ‖ ≤ B := by
    intro p
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (P p).continuous.continuousOn
    exact ⟨max B 0, le_max_right _ _, fun σ hσ => (hB σ hσ).trans (le_max_left _ _)⟩
  choose B hB0 hB using hBex
  refine ⟨∑ p ∈ S, B p * Cp p, fun σ hσ ν y hν hy => ?_⟩
  have hy' : 0 < |y| := abs_pos.mpr hy
  have hD : 0 < (1 + |ν * y|) ^ N := by positivity
  have hre : |σ.re| ≤ R := (Complex.abs_re_le_norm σ).trans (hR σ hσ)
  rw [hEq σ (hKH hσ) ν y hy]
  calc ‖∑ p ∈ S, (P p).eval σ * GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y‖
      ≤ ∑ p ∈ S, ‖(P p).eval σ * GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y‖ :=
        norm_sum_le _ _
    _ ≤ ∑ p ∈ S, B p * (Cp p * (|y| + |y|⁻¹) ^ ⌈1 + (j : ℝ) + 2 * R⌉₊ / (1 + |ν * y|) ^ N) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [norm_mul]
        apply mul_le_mul (hB p σ hσ) _ (norm_nonneg _) (hB0 p)
        refine (hCp p hp σ hσ ν y hν hy).trans ?_
        apply div_le_div_of_nonneg_right _ hD.le
        apply mul_le_mul_of_nonneg_left _ (hCp0 p)
        apply rpow_le_add_inv_pow hy'
        have hc : (p.1 : ℝ) + 2 * p.2.1 = p.2.2 + 2 + j := by exact_mod_cast (hS p hp).2
        have he : (p.2.2 : ℝ) + 1 - p.1 - 2 * p.2.1 - 2 * σ.re = -(1 + j + 2 * σ.re) := by
          linarith
        rw [he, abs_neg]
        refine le_trans ?_ (Nat.le_ceil _)
        have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        calc |1 + (j : ℝ) + 2 * σ.re| ≤ |1 + (j : ℝ)| + |2 * σ.re| := abs_add_le _ _
          _ = 1 + j + 2 * |σ.re| := by
              rw [abs_of_nonneg (by linarith), abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
          _ ≤ 1 + j + 2 * R := by linarith
    _ = (∑ p ∈ S, B p * Cp p) * (|y| + |y|⁻¹) ^ ⌈1 + (j : ℝ) + 2 * R⌉₊ / (1 + |ν * y|) ^ N := by
        rw [Finset.sum_mul, Finset.sum_div]
        refine Finset.sum_congr rfl fun p _ => ?_
        ring

end GlobalTheory.HeckeTwo.TermBoundDeriv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivHeckePhiFourierTransformBoundStatement
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedDeriv_heckePhiFourierTransform_bound : (∀ j : ℕ, ∃ (S : Finset (ℕ × ℕ × ℕ)) (P : ℕ × ℕ × ℕ → Polynomial ℂ),
    (∀ p ∈ S, 2 ≤ p.1 + 2 * p.2.1 ∧ p.1 + 2 * p.2.1 = p.2.2 + 2 + j) ∧
    ∀ σ ∈ halfPlane, ∀ ν y : ℝ, y ≠ 0 →
      iteratedDeriv j (hTrans σ ν) y = ∑ p ∈ S, (P p).eval σ * GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y) → (∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ a b m : ℕ, 2 ≤ a + 2 * b → ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖GlobalTheory.HeckeTwo.TermSmooth.intT σ ν a b m y‖ ≤ C * |y| ^ ((m : ℝ) + 1 - a - 2 * b - 2 * σ.re) / (1 + |ν * y|) ^ N) →
  ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ j : ℕ, ∃ s : ℕ, ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖iteratedDeriv j (hTrans σ ν) y‖ ≤ C * (|y| + |y|⁻¹) ^ s / (1 + |ν * y|) ^ N := by
  first | exact @GlobalTheory.HeckeTwo.TermBoundDeriv.iteratedDeriv_hTrans_bound | exact GlobalTheory.HeckeTwo.TermBoundDeriv.iteratedDeriv_hTrans_bound | (intros; apply GlobalTheory.HeckeTwo.TermBoundDeriv.iteratedDeriv_hTrans_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPiUpperHalfPlaneImBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPiUpperHalfPlaneImBounds
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory

theorem isCompact_pi_upperHalfPlane_im_bounds :
    ∀ (ι : Type) [Fintype ι] (L : Set (ι → ℂ)), IsCompact L → (∀ z ∈ L, ∀ i, 0 < (z i).im) →
    ∃ c c' : ℝ, 0 < c ∧ ∀ z ∈ L, ∀ i, c ≤ (z i).im ∧ (z i).im ≤ c' := by
  intro ι _ L hL hpos
  obtain ⟨C, hC⟩ := hL.isBounded.exists_norm_le
  have hup : ∀ z ∈ L, ∀ i, (z i).im ≤ C := fun z hz i =>
    (Complex.im_le_norm (z i)).trans ((norm_le_pi_norm z i).trans (hC z hz))
  rcases L.eq_empty_or_nonempty with hE | hne
  · exact ⟨1, 0, one_pos, by simp [hE]⟩
  have hm : ∀ i, ∃ m : ℝ, 0 < m ∧ ∀ z ∈ L, m ≤ (z i).im := by
    intro i
    have hc : Continuous fun z : ι → ℂ => (z i).im :=
      Complex.continuous_im.comp (continuous_apply i)
    obtain ⟨x, hx, hmin⟩ := hL.exists_isMinOn hne hc.continuousOn
    exact ⟨(x i).im, hpos x hx i, fun z hz => hmin hz⟩
  choose m hm0 hmle using hm
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, C, one_pos, fun z _ i => isEmptyElim i⟩
  refine ⟨Finset.univ.inf' Finset.univ_nonempty m, C, ?_, fun z hz i => ⟨?_, hup z hz i⟩⟩
  · exact (Finset.lt_inf'_iff _).2 fun i _ => hm0 i
  · exact (Finset.inf'_le _ (Finset.mem_univ i)).trans (hmle i z hz)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPiUpperHalfPlaneImBoundsStatement
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_im_bounds_of_isCompact_upperHalfPlane : ∀ (ι : Type) [Fintype ι] (L : Set (ι → ℂ)), IsCompact L → (∀ z ∈ L, ∀ i, 0 < (z i).im) →
    ∃ c c' : ℝ, 0 < c ∧ ∀ z ∈ L, ∀ i, c ≤ (z i).im ∧ (z i).im ≤ c' := by
  first | exact @GlobalTheory.isCompact_pi_upperHalfPlane_im_bounds | exact GlobalTheory.isCompact_pi_upperHalfPlane_im_bounds | (intros; apply GlobalTheory.isCompact_pi_upperHalfPlane_im_bounds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivHeckeFourierFactorLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivHeckeFourierFactorLe
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.HeckeTwo.FactorBound

theorem iteratedDeriv_eChar (i : ℕ) :
    iteratedDeriv i (fun x : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * (x : ℂ))) =
      fun x : ℝ => (2 * (Real.pi : ℂ) * I) ^ i * Complex.exp (2 * (Real.pi : ℂ) * I * (x : ℂ)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have h1 : HasDerivAt (fun z : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * z))
        (Complex.exp (2 * (Real.pi : ℂ) * I * (x : ℂ)) * (2 * (Real.pi : ℂ) * I)) (x : ℂ) := by
      have := ((hasDerivAt_id (x : ℂ)).const_mul (2 * (Real.pi : ℂ) * I)).cexp
      simpa using this
    have h2 := (h1.comp_ofReal).const_mul ((2 * (Real.pi : ℂ) * I) ^ i)
    rw [h2.deriv]
    ring

theorem contDiff_eChar :
    ContDiff ℝ ω (fun x : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * (x : ℂ))) :=
  (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

theorem norm_iteratedFDeriv_eChar (i : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ i (fun x : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * (x : ℂ))) x‖ = (2 * Real.pi) ^ i := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eChar]
  simp only [norm_mul, norm_pow]
  have : ‖Complex.exp (2 * (Real.pi : ℂ) * I * (x : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [this, mul_one]
  congr 1
  simp [Complex.norm_real, abs_of_pos Real.pi_pos]

theorem norm_iteratedFDeriv_eRe (a : ℝ) (i : ℕ) (w : ℂ) :
    ‖iteratedFDeriv ℝ i (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((a * w.re : ℝ) : ℂ))) w‖ ≤
      (2 * Real.pi * |a|) ^ i := by
  set L : ℂ →L[ℝ] ℝ := a • Complex.reCLM
  have hf : (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((a * w.re : ℝ) : ℂ))) =
      (fun x : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * (x : ℂ))) ∘ L := by
    funext w; simp [L]
  rw [hf, L.iteratedFDeriv_comp_right contDiff_eChar w le_top]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [norm_iteratedFDeriv_eChar, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hL : ‖L‖ ≤ |a| := by
    simp only [L]
    refine (norm_smul_le _ _).trans ?_
    simp [Complex.reCLM_norm]
  rw [mul_pow (2 * Real.pi) |a| i]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hL i) (pow_nonneg (mul_nonneg zero_le_two Real.pi_pos.le) _)

theorem norm_iteratedFDerivWithin_hIm (σ : ℂ) (hσ : σ ∈ halfPlane) (ν β : ℝ) (j : ℕ) (w : ℂ)
    (hw : β * w.im ≠ 0) :
    ‖iteratedFDerivWithin ℝ j (fun w : ℂ => hTrans σ ν (β * w.im)) {w : ℂ | β * w.im ≠ 0} w‖ ≤
      ‖iteratedDeriv j (hTrans σ ν) (β * w.im)‖ * |β| ^ j := by
  set L : ℂ →L[ℝ] ℝ := β • Complex.imCLM
  have hS : IsOpen {y : ℝ | y ≠ 0} := isOpen_ne
  have hpre : {w : ℂ | β * w.im ≠ 0} = L ⁻¹' {y : ℝ | y ≠ 0} := by ext w; simp [L]
  have hf : (fun w : ℂ => hTrans σ ν (β * w.im)) = hTrans σ ν ∘ L := by funext w; simp [L]
  have hLw : L w = β * w.im := by simp [L]
  have hLw' : L w ∈ {y : ℝ | y ≠ 0} := by rw [hLw]; exact hw
  rw [hf, hpre, L.iteratedFDerivWithin_comp_right (TermSmooth.contDiffOn_hTrans σ hσ ν) hS.uniqueDiffOn
    (hS.preimage L.continuous).uniqueDiffOn hLw' (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, iteratedFDerivWithin_of_isOpen j hS hLw',
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, hLw]
  have hL : ‖L‖ ≤ |β| := by
    simp only [L]
    refine (norm_smul_le _ _).trans ?_
    simp [Complex.imCLM_norm]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hL j) (norm_nonneg _)

theorem norm_iteratedFDeriv_le_sum (σ : ℂ) (hσ : σ ∈ halfPlane) (ν β : ℝ) (hβ : β ≠ 0) (k : ℕ) (w : ℂ)
    (hw : 0 < w.im) :
    ‖iteratedFDeriv ℝ k (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((ν * β * w.re : ℝ) : ℂ)) *
          hTrans σ ν (β * w.im)) w‖ ≤
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (2 * Real.pi * |ν * β|) ^ i *
        (‖iteratedDeriv (k - i) (hTrans σ ν) (β * w.im)‖ * |β| ^ (k - i)) := by
  set V : Set ℂ := {w : ℂ | β * w.im ≠ 0}
  have hV : IsOpen V := isOpen_ne_fun (continuous_const.mul Complex.continuous_im) continuous_const
  have hwV : w ∈ V := mul_ne_zero hβ hw.ne'
  have hu : ContDiffOn ℝ ∞ (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((ν * β * w.re : ℝ) : ℂ))) V :=
    ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul Complex.reCLM.contDiff))).cexp).contDiffOn
  have hv : ContDiffOn ℝ ∞ (fun w : ℂ => hTrans σ ν (β * w.im)) V :=
    (TermSmooth.contDiffOn_hTrans σ hσ ν).comp (contDiff_const.mul Complex.imCLM.contDiff).contDiffOn
      fun z hz => hz
  rw [← iteratedFDerivWithin_of_isOpen k hV hwV]
  refine (norm_iteratedFDerivWithin_mul_le hu hv hV.uniqueDiffOn hwV (by exact_mod_cast le_top)).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  rw [iteratedFDerivWithin_of_isOpen i hV hwV]
  refine mul_le_mul (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_eRe (ν * β) i w) (Nat.cast_nonneg _))
    (norm_iteratedFDerivWithin_hIm σ hσ ν β (k - i) w hwV) (norm_nonneg _) ?_
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by positivity) _)

theorem norm_iteratedFDeriv_fourierFactor_le :
    (∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ j : ℕ, ∃ s : ℕ, ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖iteratedDeriv j (hTrans σ ν) y‖ ≤ C * (|y| + |y|⁻¹) ^ s / (1 + |ν * y|) ^ N) →
  ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ c c' : ℝ, 0 < c → ∀ k : ℕ, ∃ m : ℕ, ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν β : ℝ, ν ≠ 0 → β ≠ 0 → ∀ w : ℂ, c ≤ w.im → w.im ≤ c' →
      ‖iteratedFDeriv ℝ k (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((ν * β * w.re : ℝ) : ℂ)) *
          hTrans σ ν (β * w.im)) w‖ ≤ C * (|β| + |β|⁻¹) ^ m / (1 + |ν * β|) ^ N := by
  intro H K hK hKH c c' hc k
  choose s hs using H K hK hKH
  refine ⟨k + ∑ j ∈ Finset.range (k + 1), s j, fun N => ?_⟩
  choose C hC using fun j => hs j (N + k)
  set M : ℝ := max c' c⁻¹ with hMdef
  set μ : ℝ := min 1 c with hμdef
  have hM : 0 < M := lt_of_lt_of_le (inv_pos.2 hc) (le_max_right _ _)
  have hμ : 0 < μ := lt_min one_pos hc
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (2 * Real.pi) ^ i *
      (|C (k - i)| * M ^ s (k - i) / μ ^ (N + k)), ?_⟩
  intro σ hσ ν β hν hβ w hw1 hw2
  have hσH : σ ∈ halfPlane := hKH hσ
  have ht : 0 < w.im := lt_of_lt_of_le hc hw1
  set t := w.im with htdef
  set B : ℝ := |β| + |β|⁻¹ with hBdef
  set A : ℝ := 1 + |ν * β| with hAdef
  have hβp : 0 < |β| := abs_pos.2 hβ
  have hB1 : 1 ≤ B := by
    rcases le_total 1 |β| with h | h
    · have := inv_nonneg.2 hβp.le; linarith
    · have := (one_le_inv₀ hβp).2 h; linarith
  have hA1 : 1 ≤ A := by have := abs_nonneg (ν * β); linarith
  have hApos : 0 < A := by linarith
  have hy : β * t ≠ 0 := mul_ne_zero hβ ht.ne'
  have hyB : |β * t| + |β * t|⁻¹ ≤ M * B := by
    rw [abs_mul, abs_of_pos ht, mul_inv, hBdef, mul_add]
    have h1 : |β| * t ≤ M * |β| := by
      rw [mul_comm M]; exact mul_le_mul_of_nonneg_left (hw2.trans (le_max_left _ _)) hβp.le
    have h2 : |β|⁻¹ * t⁻¹ ≤ M * |β|⁻¹ := by
      rw [mul_comm M]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hβp.le)
      exact (inv_anti₀ hc hw1).trans (le_max_right _ _)
    linarith
  have hyA : μ * A ≤ 1 + |ν * (β * t)| := by
    rw [← mul_assoc, abs_mul (ν * β), abs_of_pos ht, hAdef, mul_add, mul_one]
    have h1 : μ ≤ 1 := min_le_left _ _
    have h2 : μ ≤ t := (min_le_right _ _).trans hw1
    have h3 : μ * |ν * β| ≤ |ν * β| * t := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    linarith
  have hh : ∀ j, ‖iteratedDeriv j (hTrans σ ν) (β * t)‖ ≤
      |C j| * (M * B) ^ s j / (μ * A) ^ (N + k) := by
    intro j
    refine (hC j σ hσ ν (β * t) hν hy).trans ?_
    have hX : 0 ≤ (|β * t| + |β * t|⁻¹) ^ s j := by positivity
    calc C j * (|β * t| + |β * t|⁻¹) ^ s j / (1 + |ν * (β * t)|) ^ (N + k)
        ≤ |C j| * (|β * t| + |β * t|⁻¹) ^ s j / (1 + |ν * (β * t)|) ^ (N + k) := by
          gcongr
          exact le_abs_self _
      _ ≤ |C j| * (M * B) ^ s j / (μ * A) ^ (N + k) := by
          gcongr
  refine (norm_iteratedFDeriv_le_sum σ hσH ν β hβ k w ht).trans ?_
  rw [mul_div_assoc, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  set j := k - i with hjdef
  have hjk : j ≤ k := Nat.sub_le _ _
  have hsj : s j ≤ ∑ j ∈ Finset.range (k + 1), s j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_of_le hjk))
  have hd : (2 * Real.pi * |ν * β|) ^ i ≤ (2 * Real.pi) ^ i * A ^ k := by
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc |ν * β| ^ i ≤ A ^ i := pow_le_pow_left₀ (abs_nonneg _) (by linarith) i
      _ ≤ A ^ k := pow_le_pow_right₀ hA1 hik
  have he : |β| ^ j ≤ B ^ k :=
    (pow_le_pow_left₀ hβp.le (by have := inv_nonneg.2 hβp.le; linarith) j).trans (pow_le_pow_right₀ hB1 hjk)
  calc (k.choose i : ℝ) * (2 * Real.pi * |ν * β|) ^ i * (‖iteratedDeriv j (hTrans σ ν) (β * t)‖ * |β| ^ j)
      ≤ (k.choose i : ℝ) * ((2 * Real.pi) ^ i * A ^ k) *
          ((|C j| * (M * B) ^ s j / (μ * A) ^ (N + k)) * B ^ k) := by
        gcongr
        exact hh j
    _ = (k.choose i : ℝ) * (2 * Real.pi) ^ i * (|C j| * M ^ s j / μ ^ (N + k)) * (B ^ (k + s j) / A ^ N) := by
        have hA0 : A ≠ 0 := hApos.ne'
        have hμ0 : μ ≠ 0 := hμ.ne'
        rw [mul_pow, mul_pow, pow_add, pow_add]
        field_simp
        rw [mul_pow, mul_pow, pow_add]
        ring
    _ ≤ (k.choose i : ℝ) * (2 * Real.pi) ^ i * (|C j| * M ^ s j / μ ^ (N + k)) *
          (B ^ (k + ∑ j ∈ Finset.range (k + 1), s j) / A ^ N) := by
        gcongr
        all_goals first | exact hB1 | omega

end GlobalTheory.HeckeTwo.FactorBound

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivHeckeFourierFactorLeStatement
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_iteratedFDeriv_heckeFourierFactor_le : (∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ j : ℕ, ∃ s : ℕ, ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖iteratedDeriv j (hTrans σ ν) y‖ ≤ C * (|y| + |y|⁻¹) ^ s / (1 + |ν * y|) ^ N) →
  ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ c c' : ℝ, 0 < c → ∀ k : ℕ, ∃ m : ℕ, ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν β : ℝ, ν ≠ 0 → β ≠ 0 → ∀ w : ℂ, c ≤ w.im → w.im ≤ c' →
      ‖iteratedFDeriv ℝ k (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((ν * β * w.re : ℝ) : ℂ)) *
          hTrans σ ν (β * w.im)) w‖ ≤ C * (|β| + |β|⁻¹) ^ m / (1 + |ν * β|) ^ N := by
  first | exact @GlobalTheory.HeckeTwo.FactorBound.norm_iteratedFDeriv_fourierFactor_le | exact GlobalTheory.HeckeTwo.FactorBound.norm_iteratedFDeriv_fourierFactor_le | (intros; apply GlobalTheory.HeckeTwo.FactorBound.norm_iteratedFDeriv_fourierFactor_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivHeckePhiFourierTransformRepr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivHeckePhiFourierTransformRepr
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.HeckeTwo.TermSmooth

theorem sum_pushforward_eval (σ : ℂ) (F : ℕ × ℕ × ℕ → ℂ) (g : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ)
    (c : ℕ × ℕ × ℕ → Polynomial ℂ) (U S' : Finset (ℕ × ℕ × ℕ)) (hU : ∀ p ∈ U, g p ∈ S') :
    ∑ q ∈ S', (∑ p ∈ U, if g p = q then c p else 0).eval σ * F q = ∑ p ∈ U, (c p).eval σ * F (g p) := by
  simp_rw [Polynomial.eval_finsetSum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  simp_rw [apply_ite (Polynomial.eval σ), Polynomial.eval_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq, if_pos (hU p hp)]

theorem iteratedDeriv_hTrans_repr : ∀ j : ℕ, ∃ (S : Finset (ℕ × ℕ × ℕ)) (P : ℕ × ℕ × ℕ → Polynomial ℂ),
    (∀ p ∈ S, 2 ≤ p.1 + 2 * p.2.1 ∧ p.1 + 2 * p.2.1 = p.2.2 + 2 + j) ∧
    ∀ σ ∈ halfPlane, ∀ ν y : ℝ, y ≠ 0 →
      iteratedDeriv j (hTrans σ ν) y = ∑ p ∈ S, (P p).eval σ * GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y := by
  intro j
  induction j with
  | zero =>
    refine ⟨{(2, 0, 0)}, fun _ => 1, ?_, ?_⟩
    · intro p hp; rw [Finset.mem_singleton] at hp; subst hp; norm_num
    · intro σ hσ ν y hy
      simp [iteratedDeriv_zero, hTrans_eq σ ν hy]
  | succ j ih =>
    obtain ⟨S, P, hS, hP⟩ := ih
    let f1 : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun p => (p.1 + 1, p.2.1, p.2.2)
    let f2 : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun p => (p.1, p.2.1 + 1, p.2.2 + 1)
    let f3 : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun p => (p.1, p.2.1, p.2.2 - 1)
    let T := S.filter (fun p => 1 ≤ p.2.2)
    let c1 : ℕ × ℕ × ℕ → Polynomial ℂ := fun p => Polynomial.C (-(p.1 : ℂ) * I) * P p
    let c2 : ℕ × ℕ × ℕ → Polynomial ℂ := fun p =>
      Polynomial.C 2 * (-Polynomial.X - Polynomial.C (p.2.1 : ℂ)) * P p
    let c3 : ℕ × ℕ × ℕ → Polynomial ℂ := fun p => Polynomial.C (p.2.2 : ℂ) * P p
    let S' := S.image f1 ∪ S.image f2 ∪ T.image f3
    refine ⟨S', fun q => (∑ p ∈ S, if f1 p = q then c1 p else 0) + (∑ p ∈ S, if f2 p = q then c2 p else 0)
        + ∑ p ∈ T, if f3 p = q then c3 p else 0, ?_, ?_⟩
    · intro q hq
      simp only [S', Finset.mem_union, Finset.mem_image, T, Finset.mem_filter] at hq
      rcases hq with (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | ⟨p, ⟨hp, hm⟩, rfl⟩ <;>
        have := hS p hp <;> simp only [f1, f2, f3] <;> omega
    · intro σ hσ ν y hy
      have hev : iteratedDeriv j (hTrans σ ν) =ᶠ[nhds y]
          fun y => ∑ p ∈ S, (P p).eval σ * intT σ ν p.1 p.2.1 p.2.2 y :=
        Filter.eventually_of_mem (isOpen_ne.mem_nhds hy) fun z hz => hP σ hσ ν z hz
      have hd : HasDerivAt (fun y => ∑ p ∈ S, (P p).eval σ * intT σ ν p.1 p.2.1 p.2.2 y)
          (∑ p ∈ S, (P p).eval σ * (-(p.1 : ℂ) * I * intT σ ν (p.1 + 1) p.2.1 p.2.2 y
            + 2 * (-σ - (p.2.1 : ℂ)) * intT σ ν p.1 (p.2.1 + 1) (p.2.2 + 1) y
            + (p.2.2 : ℂ) * intT σ ν p.1 p.2.1 (p.2.2 - 1) y)) y :=
        HasDerivAt.fun_sum fun p hp => (hasDerivAt_intT σ hσ ν p.2.2 (hS p hp).1 hy).const_mul _
      rw [iteratedDeriv_succ, hev.deriv_eq, hd.deriv]
      set F : ℕ × ℕ × ℕ → ℂ := fun q => intT σ ν q.1 q.2.1 q.2.2 y with hF
      have e1 := sum_pushforward_eval σ F f1 c1 S S' fun p hp => by
        simp only [S', Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inl ⟨p, hp, rfl⟩)
      have e2 := sum_pushforward_eval σ F f2 c2 S S' fun p hp => by
        simp only [S', Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inr ⟨p, hp, rfl⟩)
      have e3 := sum_pushforward_eval σ F f3 c3 T S' fun p hp => by
        simp only [S', Finset.mem_union, Finset.mem_image]; exact Or.inr ⟨p, hp, rfl⟩
      have e3' : ∑ p ∈ T, (c3 p).eval σ * F (f3 p) = ∑ p ∈ S, (c3 p).eval σ * F (f3 p) := by
        refine Finset.sum_filter_of_ne fun p _ hne => ?_
        by_contra h
        have h0 : p.2.2 = 0 := by omega
        apply hne
        simp [c3, h0]
      have split : ∀ q, ((∑ p ∈ S, if f1 p = q then c1 p else 0) + (∑ p ∈ S, if f2 p = q then c2 p else 0)
          + ∑ p ∈ T, if f3 p = q then c3 p else 0).eval σ * F q =
          (∑ p ∈ S, if f1 p = q then c1 p else 0).eval σ * F q +
          (∑ p ∈ S, if f2 p = q then c2 p else 0).eval σ * F q +
          (∑ p ∈ T, if f3 p = q then c3 p else 0).eval σ * F q := by
        intro q; rw [Polynomial.eval_add, Polynomial.eval_add]; ring
      show _ = ∑ q ∈ S', _ * F q
      rw [Finset.sum_congr rfl fun q _ => split q, Finset.sum_add_distrib, Finset.sum_add_distrib, e1, e2, e3, e3',
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [c1, c2, c3, F, f1, f2, f3, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
        Polynomial.eval_neg, Polynomial.eval_X]
      ring

end GlobalTheory.HeckeTwo.TermSmooth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivHeckePhiFourierTransformReprStatement
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedDeriv_heckePhiFourierTransform_repr : ∀ j : ℕ, ∃ (S : Finset (ℕ × ℕ × ℕ)) (P : ℕ × ℕ × ℕ → Polynomial ℂ),
    (∀ p ∈ S, 2 ≤ p.1 + 2 * p.2.1 ∧ p.1 + 2 * p.2.1 = p.2.2 + 2 + j) ∧
    ∀ σ ∈ halfPlane, ∀ ν y : ℝ, y ≠ 0 →
      iteratedDeriv j (hTrans σ ν) y = ∑ p ∈ S, (P p).eval σ * GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y := by
  first | exact @GlobalTheory.HeckeTwo.TermSmooth.iteratedDeriv_hTrans_repr | exact GlobalTheory.HeckeTwo.TermSmooth.iteratedDeriv_hTrans_repr | (intros; apply GlobalTheory.HeckeTwo.TermSmooth.iteratedDeriv_hTrans_repr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivProdCoordLeLeibniz
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivProdCoordLeLeibniz
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.LeibnizProd

theorem countPerms_le_factorial {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : Sym ι n) :
    ((p : Multiset ι).countPerms : ℝ) ≤ (n.factorial : ℝ) := by
  have h1 : (p : Multiset ι).countPerms =
      Nat.multinomial Finset.univ (fun j => (p : Multiset ι).count j) := by
    rw [Multiset.countPerms, Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)]
    rfl
  have h2 : ∑ j, (p : Multiset ι).count j = n := by
    rw [Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)]
    exact p.2
  have h3 := Nat.multinomial_spec Finset.univ (fun j => (p : Multiset ι).count j)
  rw [h2] at h3
  have h4 : (p : Multiset ι).countPerms ≤ n.factorial := by
    rw [h1]
    exact Nat.le_of_dvd (Nat.factorial_pos n) (Dvd.intro_left _ h3)
  exact_mod_cast h4

theorem sum_sym_le {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (a : ι → ℕ → ℝ)
    (ha : ∀ i k, 0 ≤ a i k) :
    ∑ p ∈ (Finset.univ : Finset ι).sym n, ∏ j, a j ((p : Multiset ι).count j) ≤
      ∏ j, ∑ k ∈ Finset.range (n + 1), a j k := by
  rw [← Finset.sum_prod_piFinset]
  let φ : Sym ι n → (ι → ℕ) := fun p j => (p : Multiset ι).count j
  have hinj : Set.InjOn φ ↑((Finset.univ : Finset ι).sym n) := by
    intro p _ q _ h
    apply Sym.coe_injective
    ext j
    exact congrFun h j
  have hs := Finset.sum_image (f := fun c : ι → ℕ => ∏ j, a j (c j)) hinj
  rw [← hs]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro c hc
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 hc
    rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_range, Nat.lt_succ_iff]
    calc (p : Multiset ι).count j ≤ Multiset.card (p : Multiset ι) := Multiset.count_le_card _ _
      _ = n := p.2
  · intro c _ _
    exact Finset.prod_nonneg fun j _ => ha j _

theorem norm_iteratedFDeriv_comp_apply_le {ι : Type} [Fintype ι] (g : ℂ → ℂ) (U : Set ℂ)
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (j : ι) (z : ι → ℂ) (hz : z j ∈ U) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun w : ι → ℂ => g (w j)) z‖ ≤ ‖iteratedFDeriv ℝ k g (z j)‖ := by
  set P : (ι → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) j
  have hPo : IsOpen (P ⁻¹' U) := hU.preimage P.continuous
  have hzP : P z ∈ U := hz
  have hzP' : z ∈ P ⁻¹' U := hz
  have e := P.iteratedFDerivWithin_comp_right hg hU.uniqueDiffOn hPo.uniqueDiffOn hzP (i := k)
    (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen k hPo hzP', iteratedFDerivWithin_of_isOpen k hU hzP] at e
  have hfun : (fun w : ι → ℂ => g (w j)) = g ∘ P := rfl
  rw [hfun, e]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hP : ‖P‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun w => by simpa [P] using norm_le_pi_norm w j)
  calc ‖iteratedFDeriv ℝ k g (P z)‖ * ∏ _i : Fin k, ‖P‖ ≤ ‖iteratedFDeriv ℝ k g (P z)‖ * 1 := by
        gcongr
        exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hP)
    _ = ‖iteratedFDeriv ℝ k g (z j)‖ := by rw [mul_one]; rfl

theorem norm_iteratedFDeriv_prod_apply_le : ∀ (ι : Type) [Fintype ι] (g : ι → ℂ → ℂ) (U : ι → Set ℂ), (∀ i, IsOpen (U i)) →
    (∀ i, ContDiffOn ℝ ∞ (g i) (U i)) → ∀ z : ι → ℂ, (∀ i, z i ∈ U i) → ∀ n : ℕ,
      ‖iteratedFDeriv ℝ n (fun z : ι → ℂ => ∏ i, g i (z i)) z‖ ≤
        n.factorial * ∏ i, ∑ k ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ k (g i) (z i)‖ := by
  intro ι _ g U hU hg z hz n
  classical
  set V : Set (ι → ℂ) := ⋂ i, (fun w : ι → ℂ => w i) ⁻¹' U i with hVdef
  have hV : IsOpen V := isOpen_iInter_of_finite fun i => (hU i).preimage (continuous_apply i)
  have hzV : z ∈ V := Set.mem_iInter.2 hz
  have hf : ∀ i ∈ (Finset.univ : Finset ι), ContDiffOn ℝ ∞ (fun w : ι → ℂ => g i (w i)) V := by
    intro i _
    exact (hg i).comp (contDiff_apply ℝ (fun _ => ℂ) i).contDiffOn (fun w hw => Set.mem_iInter.1 hw i)
  have key := norm_iteratedFDerivWithin_prod_le (u := Finset.univ) hf hV.uniqueDiffOn hzV (n := n)
    (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen n hV hzV] at key
  refine key.trans ?_
  calc _ ≤ ∑ p ∈ (Finset.univ : Finset ι).sym n, (n.factorial : ℝ) *
        ∏ j, ‖iteratedFDeriv ℝ ((p : Multiset ι).count j) (g j) (z j)‖ := by
        gcongr with p hp j
        · exact_mod_cast countPerms_le_factorial p
        · rw [iteratedFDerivWithin_of_isOpen _ hV hzV]
          exact norm_iteratedFDeriv_comp_apply_le (g j) (U j) (hU j) (hg j) j z (hz j) _
    _ ≤ _ := by
        rw [← Finset.mul_sum]
        gcongr
        exact sum_sym_le n (fun j k => ‖iteratedFDeriv ℝ k (g j) (z j)‖) (fun _ _ => norm_nonneg _)

end GlobalTheory.LeibnizProd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivProdCoordLeLeibnizStatement
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_iteratedFDeriv_prod_coord_le_leibniz : ∀ (ι : Type) [Fintype ι] (g : ι → ℂ → ℂ) (U : ι → Set ℂ), (∀ i, IsOpen (U i)) →
    (∀ i, ContDiffOn ℝ ∞ (g i) (U i)) → ∀ z : ι → ℂ, (∀ i, z i ∈ U i) → ∀ n : ℕ,
      ‖iteratedFDeriv ℝ n (fun z : ι → ℂ => ∏ i, g i (z i)) z‖ ≤
        n.factorial * ∏ i, ∑ k ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ k (g i) (z i)‖ := by
  first | exact @GlobalTheory.LeibnizProd.norm_iteratedFDeriv_prod_apply_le | exact GlobalTheory.LeibnizProd.norm_iteratedFDeriv_prod_apply_le | (intros; apply GlobalTheory.LeibnizProd.norm_iteratedFDeriv_prod_apply_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FTermIteratedFDerivBound
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo.TermBound

theorem factorSmooth (σ : ℂ) (hσ : σ ∈ halfPlane) (ν β : ℝ) (hβ : β ≠ 0) :
    ContDiffOn ℝ ∞ (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((ν * β * w.re : ℝ) : ℂ)) *
      hTrans σ ν (β * w.im)) {w : ℂ | 0 < w.im} := by
  have hre : ContDiff ℝ ∞ (fun w : ℂ => ((ν * β * w.re : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul Complex.reCLM.contDiff)
  have h1 : ContDiff ℝ ∞ (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((ν * β * w.re : ℝ) : ℂ))) :=
    Complex.contDiff_exp.comp (contDiff_const.mul hre)
  have h2 : ContDiffOn ℝ ∞ (fun w : ℂ => hTrans σ ν (β * w.im)) {w : ℂ | 0 < w.im} := by
    refine (GlobalTheory.HeckeTwo.TermSmooth.contDiffOn_hTrans σ hσ ν).comp
      (contDiff_const.mul Complex.imCLM.contDiff : ContDiff ℝ ∞ fun w : ℂ => β * w.im).contDiffOn ?_
    intro w hw; exact mul_ne_zero hβ (ne_of_gt hw)
  exact h1.contDiffOn.mul h2

theorem fTerm_iteratedFDeriv_bound : ∀ (F : Type) [Field F] [NumberField F] (K : Set ℂ), IsCompact K → K ⊆ halfPlane →
    ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F → ∀ n : ℕ, ∃ m : ℕ, ∀ N : ℕ, ∃ C : ℝ,
      ∀ σ ∈ K, ∀ z ∈ L, ∀ b ν : F, b ≠ 0 → ν ≠ 0 →
        ‖iteratedFDeriv ℝ n (fun z : Emb F → ℂ => fTerm σ z b ν) z‖ ≤
          C * ∏ τ : Emb F, (|τ b| + |τ b|⁻¹) ^ m / (1 + |τ ν * τ b|) ^ N := by
  intro F _ _ K hK hKH L hL hLH n
  obtain ⟨c, c', hc, hcc⟩ := GlobalTheory.T.exists_im_bounds_of_isCompact_upperHalfPlane (Emb F) L hL (fun z hz τ => hLH hz τ)
  have hfb := GlobalTheory.T.norm_iteratedFDeriv_heckeFourierFactor_le (GlobalTheory.T.iteratedDeriv_heckePhiFourierTransform_bound GlobalTheory.T.iteratedDeriv_heckePhiFourierTransform_repr GlobalTheory.T.heckeYDerivativeTermIntegral_polynomial_decay) K hK hKH c c' hc
  choose mk hmk using hfb
  refine ⟨(Finset.range (n + 1)).sup mk, fun N => ?_⟩
  choose Ck hCk using fun k => hmk k N
  refine ⟨n.factorial * (∑ k ∈ Finset.range (n + 1), max (Ck k) 0) ^ Fintype.card (Emb F), ?_⟩
  intro σ hσ z hz b ν hb hν
  have hσH : σ ∈ halfPlane := hKH hσ
  set m := (Finset.range (n + 1)).sup mk with hm
  set C0 := ∑ k ∈ Finset.range (n + 1), max (Ck k) 0 with hC0
  set g : Emb F → ℂ → ℂ := fun τ w => Complex.exp (2 * (Real.pi : ℂ) * I * ((τ ν * τ b * w.re : ℝ) : ℂ)) *
    hTrans σ (τ ν) (τ b * w.im) with hg
  have hfun : (fun z : Emb F → ℂ => fTerm σ z b ν) = fun z => ∏ τ, g τ (z τ) := rfl
  have hτb : ∀ τ : Emb F, τ b ≠ 0 := fun τ => (map_ne_zero τ).2 hb
  have hτν : ∀ τ : Emb F, τ ν ≠ 0 := fun τ => (map_ne_zero τ).2 hν
  have hsm : ∀ τ, ContDiffOn ℝ ∞ (g τ) {w : ℂ | 0 < w.im} := fun τ => factorSmooth σ hσH (τ ν) (τ b) (hτb τ)
  have hopen : ∀ τ : Emb F, IsOpen {w : ℂ | 0 < w.im} := fun _ => isOpen_lt continuous_const Complex.continuous_im
  rw [hfun]
  refine (GlobalTheory.T.norm_iteratedFDeriv_prod_coord_le_leibniz (Emb F) g (fun _ => {w : ℂ | 0 < w.im}) hopen hsm z (fun τ => hLH hz τ) n).trans ?_
  have hfac : ∀ τ, ∑ k ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ k (g τ) (z τ)‖ ≤
      C0 * ((|τ b| + |τ b|⁻¹) ^ m / (1 + |τ ν * τ b|) ^ N) := by
    intro τ
    rw [hC0, Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    have h1 := hCk k σ hσ (τ ν) (τ b) (hτν τ) (hτb τ) (z τ) (hcc z hz τ).1 (hcc z hz τ).2
    have hB1 : (1 : ℝ) ≤ |τ b| + |τ b|⁻¹ := by
      have hp : 0 < |τ b| := abs_pos.2 (hτb τ)
      rcases le_total 1 |τ b| with h | h
      · linarith [inv_pos.2 hp]
      · have : 1 ≤ |τ b|⁻¹ := (one_le_inv₀ hp).2 h
        linarith
    have hmk' : mk k ≤ m := Finset.le_sup hk
    have hpow : (|τ b| + |τ b|⁻¹) ^ mk k ≤ (|τ b| + |τ b|⁻¹) ^ m := pow_le_pow_right₀ hB1 hmk'
    have hden : 0 < (1 + |τ ν * τ b|) ^ N := by positivity
    calc ‖iteratedFDeriv ℝ k (g τ) (z τ)‖ ≤ Ck k * (|τ b| + |τ b|⁻¹) ^ mk k / (1 + |τ ν * τ b|) ^ N := h1
      _ ≤ max (Ck k) 0 * ((|τ b| + |τ b|⁻¹) ^ m / (1 + |τ ν * τ b|) ^ N) := by
        rw [mul_div_assoc]
        exact mul_le_mul (le_max_left _ _) (div_le_div_of_nonneg_right hpow hden.le) (by positivity)
          (le_max_right _ _)
  calc (n.factorial : ℝ) * ∏ τ, ∑ k ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ k (g τ) (z τ)‖
      ≤ n.factorial * ∏ τ : Emb F, (C0 * ((|τ b| + |τ b|⁻¹) ^ m / (1 + |τ ν * τ b|) ^ N)) := by
        exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun τ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
          (fun τ _ => hfac τ)) (by positivity)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]; ring

end GlobalTheory.HeckeTwo.TermBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FTermIteratedFDerivBoundStatement
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_iteratedFDeriv_fTerm_le_of_isCompact : ∀ (F : Type) [Field F] [NumberField F] (K : Set ℂ), IsCompact K → K ⊆ halfPlane →
    ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F → ∀ n : ℕ, ∃ m : ℕ, ∀ N : ℕ, ∃ C : ℝ,
      ∀ σ ∈ K, ∀ z ∈ L, ∀ b ν : F, b ≠ 0 → ν ≠ 0 →
        ‖iteratedFDeriv ℝ n (fun z : Emb F → ℂ => fTerm σ z b ν) z‖ ≤
          C * ∏ τ : Emb F, (|τ b| + |τ b|⁻¹) ^ m / (1 + |τ ν * τ b|) ^ N := by
  first | exact @GlobalTheory.HeckeTwo.TermBound.fTerm_iteratedFDeriv_bound | exact GlobalTheory.HeckeTwo.TermBound.fTerm_iteratedFDeriv_bound | (intros; apply GlobalTheory.HeckeTwo.TermBound.fTerm_iteratedFDeriv_bound <;> assumption)
end
