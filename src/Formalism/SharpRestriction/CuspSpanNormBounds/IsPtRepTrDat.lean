module

public import Formalism.SharpRestriction.CuspSpanNormBounds.SpanMemOfImage
public import Formalism.SharpRestriction.CuspSpanNormBounds.WeightedUniformRotatedOfExpansion
public import Formalism.SharpRestriction.CuspSpanNormBounds.TheoremBConstants

@[expose] public section

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.BlockExponentKappaIdentity
open MeasureTheory Matrix Finset

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

section Weight

variable {k r : ℕ} {κ τ : ℝ}

def Wbig (k r : ℕ) (κ τ : ℝ) : ℝ := ∏ a : Fin (r + 1), tF r κ τ a ^ (4 * (2 * (r - a.val) + k - 1))

def frameBlockSum (g : ℕ → ℕ → ℕ) : ℕ → List (ℂ × ℕ) → ℕ
  | _, [] => 0
  | acc, (_, s) :: bs => g acc s + frameBlockSum g (acc + s) bs

def frGN (k r acc s : ℕ) : ℕ := 2 * s * (Ml k r (acc + s) + s - 3)

def frGE (r acc s : ℕ) : ℕ := 2 * (r + 1 - (acc + s)) + (s - 1)

def frTri (d : ℕ) : ℕ := ∑ j ∈ range d, (d - j)

theorem ptWeightFrom_scale (hκ : 0 < κ) (hτ : 0 < τ) (T T' : ℝ) (acc : ℕ) (bs : List (ℂ × ℕ)) :
    ptWeightFrom k r (τ ^ 2 * T) (τ ^ 2 * T') acc (scaleBlocks κ τ r acc bs) =
      τ ^ frameBlockSum (fun a s => 2 * frGN k r a s) acc bs *
        κ ^ frameBlockSum (fun a s => frGE r a s * frGN k r a s) acc bs * ptWeightFrom k r T T' acc bs := by
  induction bs generalizing acc with
  | nil => simp [ptWeightFrom, scaleBlocks, frameBlockSum]
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [scaleBlocks, ptWeightFrom, frameBlockSum]
    rw [ih (acc + s)]
    by_cases h : s = 1 ∧ acc + 1 = r + 1
    · rw [if_pos h, if_pos h]
      obtain ⟨rfl, h2⟩ := h
      have e1 : 2 * (r + 1 - (acc + 1)) + (1 - 1) = 0 := by omega
      have e2 : frGE r acc 1 = 0 := by unfold frGE; omega
      have e3 : 2 * frGN k r acc 1 = 4 * (k - 1) := by unfold frGN Ml; omega
      have hbase : Complex.normSq (((τ ^ 2 * κ ^ 0 : ℝ) : ℂ) * t) - τ ^ 2 * T * (τ ^ 2 * T') =
          τ ^ 4 * (Complex.normSq t - T * T') := by
        rw [Complex.normSq_mul, Complex.normSq_ofReal]; ring
      rw [e1, hbase, e2, e3, mul_pow]
      ring
    · rw [if_neg h, if_neg h, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      unfold frGE frGN
      ring

theorem sum_pos_blocks (f : ℕ → ℕ → ℕ) (acc : ℕ) (bs : List (ℂ × ℕ)) :
    ∑ p ∈ range (bs.map Prod.snd).sum, f (acc + p) (p - frStart bs p) =
      frameBlockSum (fun a s => ∑ i ∈ range s, f (a + i) i) acc bs := by
  induction bs generalizing acc with
  | nil => simp [frameBlockSum]
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_range_add, frameBlockSum, ← ih (acc + s)]
    congr 1
    · refine Finset.sum_congr rfl fun p hp => ?_
      have hp' : p < s := Finset.mem_range.mp hp
      simp only [frStart, if_pos hp', Nat.sub_zero]
    · refine Finset.sum_congr rfl fun p _ => ?_
      simp only [frStart]
      rw [if_neg (show ¬ (s + p < s) by omega), show s + p - s = p by omega,
        show acc + (s + p) = acc + s + p by omega,
        show s + p - (s + frStart bs p) = p - frStart bs p by omega]

theorem sum_rootPat_diff (γ : Point ℂ (r + 1)) :
    ∑ p ∈ rootPat γ, (p.2.val - p.1.val) = frameBlockSum (fun a s => ∑ i ∈ range s, frTri i) 0 γ.1 := by
  have h1 := sum_rootPat (fun a b => b - a) γ
  have h2 := sum_pos_blocks (fun _ d => frTri d) 0 γ.1
  rw [γ.2.2] at h2
  rw [h1, ← h2]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_Ico_eq_sum_range]
  unfold frTri
  refine Finset.sum_congr rfl fun j hj => ?_
  exact (Nat.sub_sub b (frStart γ.1 b) j).symm

theorem Wbig_eq : Wbig k r κ τ = τ ^ (∑ a ∈ range (r + 1), 4 * (2 * (r - a) + k - 1)) *
    κ ^ (∑ a ∈ range (r + 1), (r - a) * (4 * (2 * (r - a) + k - 1))) := by
  unfold Wbig
  rw [Fin.prod_univ_eq_prod_range (fun a => tF r κ τ a ^ (4 * (2 * (r - a) + k - 1)))]
  simp_rw [tF, mul_pow, ← pow_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]

theorem alphaPt_sq_mul (hκ : 0 < κ) (hτ : 0 < τ) (γ : Point ℂ (r + 1)) :
    alphaPt κ τ γ ^ 2 * κ ^ (4 * ∑ p ∈ rootPat γ, (p.2.val - p.1.val)) = κ ^ (2 * (rootPat γ).card) := by
  have h1 : ∀ p ∈ rootPat γ,
      (tF r κ τ p.2.val / tF r κ τ p.1.val) ^ 2 * κ ^ (2 * (p.2.val - p.1.val)) = 1 := by
    intro p hp
    have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2.1
    have hlt' : p.1.val < p.2.val := hlt
    have hle : p.2.val ≤ r := Nat.lt_succ_iff.mp p.2.isLt
    have e : tF r κ τ p.1.val = tF r κ τ p.2.val * κ ^ (p.2.val - p.1.val) := by
      unfold tF; rw [mul_assoc, ← pow_add]; congr 2; omega
    have h2 := tF_pos (r := r) hκ hτ p.2.val
    have h3 : 0 < κ ^ (p.2.val - p.1.val) := pow_pos hκ _
    have h4 : tF r κ τ p.2.val / (tF r κ τ p.2.val * κ ^ (p.2.val - p.1.val)) * κ ^ (p.2.val - p.1.val) = 1 := by
      field_simp
    rw [e, pow_mul', ← mul_pow, h4, one_pow]
  set P := ∏ p ∈ rootPat γ, (tF r κ τ p.2.val / tF r κ τ p.1.val) ^ 2 with hP
  set S := ∑ p ∈ rootPat γ, (p.2.val - p.1.val) with hS
  have hPS : P * κ ^ (2 * S) = 1 := by
    rw [hS, Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum, hP, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one h1
  unfold alphaPt
  rw [← hP, show (κ ^ (rootPat γ).card * P) ^ 2 * κ ^ (4 * S) =
    κ ^ (2 * (rootPat γ).card) * (P * κ ^ (2 * S)) ^ 2 by ring, hPS]
  ring

theorem frTri_succ (d : ℕ) : frTri (d + 1) = frTri d + (d + 1) := by
  unfold frTri
  rw [Finset.sum_range_succ']
  congr 1
  · exact Finset.sum_congr rfl fun j _ => by omega

theorem two_mul_frTri (d : ℕ) : 2 * frTri d = d * (d + 1) := by
  induction d with
  | zero => simp [frTri]
  | succ n ih => rw [frTri_succ, mul_add, ih]; ring

theorem block_exponent_tau_identity (m k' s' : ℕ) :
    2 * (2 * (s' + 1) * (2 * m + k' + s')) = ∑ i ∈ range (s' + 1), 4 * (2 * (m + i) + k') := by
  induction s' with
  | zero => simp only [zero_add, add_zero, Finset.sum_range_one]; ring
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; ring

theorem block_exponent_kappa_identity (m k' s' : ℕ) :
    (2 * m + s') * (2 * (s' + 1) * (2 * m + k' + s')) + 4 * ∑ i ∈ range (s' + 1), frTri i =
      ∑ i ∈ range (s' + 1), (m + i) * (4 * (2 * (m + i) + k')) := by
  induction s' with
  | zero =>
    simp only [zero_add, add_zero, Finset.sum_range_one, frTri, Finset.range_zero, Finset.sum_empty, mul_zero]; ring
  | succ n ih =>
    rw [Finset.sum_range_succ frTri (n + 1),
      Finset.sum_range_succ (fun i => (m + i) * (4 * (2 * (m + i) + k'))) (n + 1), ← ih]
    have h := two_mul_frTri (n + 1)
    nlinarith [h]

theorem blk_tau (hk : 1 ≤ k) (a s : ℕ) (h : a + s ≤ r + 1) :
    2 * frGN k r a s = ∑ i ∈ range s, 4 * (2 * (r - (a + i)) + k - 1) := by
  rcases s with _ | s'
  · simp [frGN]
  obtain ⟨m, hm⟩ : ∃ m, m = r + 1 - (a + (s' + 1)) := ⟨_, rfl⟩
  have hN : frGN k r a (s' + 1) = 2 * (s' + 1) * (2 * m + (k - 1) + s') := by
    unfold frGN Ml; congr 1; omega
  rw [hN, block_exponent_tau_identity m (k - 1) s',
    ← Finset.sum_range_reflect (fun i => 4 * (2 * (r - (a + i)) + k - 1)) (s' + 1)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.mp hi
  try dsimp only
  omega

theorem blk_kappa (hk : 1 ≤ k) (a s : ℕ) (h : a + s ≤ r + 1) :
    frGE r a s * frGN k r a s + 4 * ∑ i ∈ range s, frTri i =
      ∑ i ∈ range s, (r - (a + i)) * (4 * (2 * (r - (a + i)) + k - 1)) := by
  rcases s with _ | s'
  · simp [frGN]
  obtain ⟨m, hm⟩ : ∃ m, m = r + 1 - (a + (s' + 1)) := ⟨_, rfl⟩
  have hN : frGN k r a (s' + 1) = 2 * (s' + 1) * (2 * m + (k - 1) + s') := by
    unfold frGN Ml; congr 1; omega
  have hE : frGE r a (s' + 1) = 2 * m + s' := by unfold frGE; omega
  rw [hN, hE, block_exponent_kappa_identity m (k - 1) s',
    ← Finset.sum_range_reflect (fun i => (r - (a + i)) * (4 * (2 * (r - (a + i)) + k - 1))) (s' + 1)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.mp hi
  try dsimp only
  have e1 : r - (a + (s' + 1 - 1 - i)) = m + i := by omega
  have e2 : 2 * (m + i) + k - 1 = 2 * (m + i) + (k - 1) := by omega
  rw [e1, e2]

theorem frame_block_sum_congr {g₁ g₂ : ℕ → ℕ → ℕ} {R : ℕ} (h : ∀ a s, a + s ≤ R → g₁ a s = g₂ a s) (acc : ℕ)
    (bs : List (ℂ × ℕ)) (hb : acc + (bs.map Prod.snd).sum ≤ R) : frameBlockSum g₁ acc bs = frameBlockSum g₂ acc bs := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [List.map_cons, List.sum_cons] at hb
    simp only [frameBlockSum]
    rw [h acc s (by omega), ih (acc + s) (by omega)]

theorem frame_block_sum_add (g₁ g₂ : ℕ → ℕ → ℕ) (acc : ℕ) (bs : List (ℂ × ℕ)) :
    frameBlockSum (fun a s => g₁ a s + g₂ a s) acc bs = frameBlockSum g₁ acc bs + frameBlockSum g₂ acc bs := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [frameBlockSum]
    rw [ih (acc + s)]; ring

theorem frame_block_sum_mul (c : ℕ) (g : ℕ → ℕ → ℕ) (acc : ℕ) (bs : List (ℂ × ℕ)) :
    frameBlockSum (fun a s => c * g a s) acc bs = c * frameBlockSum g acc bs := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [frameBlockSum]
    rw [ih (acc + s)]; ring

theorem ptWeight_ptTr (hk : 1 ≤ k) (hκ : 0 < κ) (hτ : 0 < τ) (T T' : ℝ) (γ : Point ℂ (r + 1)) :
    ptWeight k r (τ ^ 2 * T) (τ ^ 2 * T') (ptTr κ τ hκ hτ γ) * κ ^ (2 * (rootPat γ).card) =
      Wbig k r κ τ * alphaPt κ τ γ ^ 2 * ptWeight k r T T' γ := by
  have hsum : 0 + (γ.1.map Prod.snd).sum ≤ r + 1 := by rw [γ.2.2]; omega
  have hU := sum_pos_blocks (fun p _ => 4 * (2 * (r - p) + k - 1)) 0 γ.1
  have hV := sum_pos_blocks (fun p _ => (r - p) * (4 * (2 * (r - p) + k - 1))) 0 γ.1
  rw [γ.2.2] at hU hV
  simp only [zero_add] at hU hV
  have hA : frameBlockSum (fun a s => 2 * frGN k r a s) 0 γ.1 = ∑ a ∈ range (r + 1), 4 * (2 * (r - a) + k - 1) := by
    rw [hU]
    refine frame_block_sum_congr ?_ 0 γ.1 hsum
    intro a s h; exact blk_tau hk a s h
  have hB : frameBlockSum (fun a s => frGE r a s * frGN k r a s) 0 γ.1 + 4 * ∑ p ∈ rootPat γ, (p.2.val - p.1.val) =
      ∑ a ∈ range (r + 1), (r - a) * (4 * (2 * (r - a) + k - 1)) := by
    rw [hV, sum_rootPat_diff, ← frame_block_sum_mul, ← frame_block_sum_add]
    refine frame_block_sum_congr ?_ 0 γ.1 hsum
    intro a s h; exact blk_kappa hk a s h
  have hα := alphaPt_sq_mul hκ hτ γ
  unfold ptWeight
  rw [ptTr_val, ptWeightFrom_scale hκ hτ, Wbig_eq, hA, ← hB, ← hα, pow_add]
  ring

end Weight

end Formalism.MainNotions.FrameBoundFromBesselTorus
end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.FrameFactorGe
section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.BcWeightEqZeroOf
open MeasureTheory Matrix Finset
open scoped ContDiff

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

def sBig (r : ℕ) (κ τ : ℝ) (p : (Fin r → ℂ) × ℂ) : (Fin r → ℂ) × ℂ :=
  (fun a => ((tF r κ τ a.val ^ 2 : ℝ) : ℂ) * p.1 a, ((τ ^ 2 : ℝ) : ℂ) * p.2)

def sBigL (r : ℕ) (κ τ : ℝ) : ((Fin r → ℂ) × ℂ) →ₗ[ℝ] ((Fin r → ℂ) × ℂ) :=
  LinearMap.prodMap (LinearMap.pi fun a => ((tF r κ τ a.val ^ 2) • LinearMap.id) ∘ₗ LinearMap.proj a)
    ((τ ^ 2) • LinearMap.id)

theorem sBigL_apply (r : ℕ) (κ τ : ℝ) (p : (Fin r → ℂ) × ℂ) : sBigL r κ τ p = sBig r κ τ p := by
  ext a <;> simp [sBigL, sBig, Complex.real_smul]

def jacBig (r : ℕ) (κ τ : ℝ) : ℝ := (∏ a : Fin r, tF r κ τ a.val ^ 4) * τ ^ 4

def wBig (k r : ℕ) (κ τ : ℝ) : ℝ :=
  (∏ a : Fin r, (tF r κ τ a.val ^ 2) ^ (2 * (Mdim k r a - 2))) * (τ ^ 4) ^ (k - 1)

section Norm

variable {k r : ℕ} {κ τ : ℝ}

theorem det_sBigL : LinearMap.det (sBigL r κ τ) = jacBig r κ τ := by
  rw [sBigL, LinearMap.det_prodMap, LinearMap.det_pi]
  simp only [LinearMap.det_smul, LinearMap.det_id, Complex.finrank_real_complex, mul_one, jacBig]
  congr 1
  · refine Finset.prod_congr rfl fun a _ => ?_; ring
  · ring

theorem jacBig_pos (hκ : 0 < κ) (hτ : 0 < τ) : 0 < jacBig r κ τ :=
  mul_pos (Finset.prod_pos fun a _ => pow_pos (tF_pos hκ hτ _) 4) (pow_pos hτ 4)

theorem wBig_pos (hκ : 0 < κ) (hτ : 0 < τ) : 0 < wBig k r κ τ :=
  mul_pos (Finset.prod_pos fun a _ => pow_pos (pow_pos (tF_pos hκ hτ _) 2) _) (pow_pos (pow_pos hτ 4) _)

theorem lintegral_sBig (hκ : 0 < κ) (hτ : 0 < τ) (G : (Fin r → ℂ) × ℂ → ENNReal) :
    ∫⁻ p, G p = ENNReal.ofReal (jacBig r κ τ) * ∫⁻ p, G (sBig r κ τ p) := by
  have hdet : LinearMap.det (sBigL r κ τ) ≠ 0 := by rw [det_sBigL]; exact (jacBig_pos hκ hτ).ne'
  let e : ((Fin r → ℂ) × ℂ) ≃ₗ[ℝ] ((Fin r → ℂ) × ℂ) := LinearMap.equivOfDetNeZero (sBigL r κ τ) hdet
  let eM : ((Fin r → ℂ) × ℂ) ≃ᵐ ((Fin r → ℂ) × ℂ) := e.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have : (volume : Measure ((Fin r → ℂ) × ℂ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; exact Measure.prod.instIsAddHaarMeasure _ _
  have hmap : Measure.map eM (volume : Measure ((Fin r → ℂ) × ℂ)) =
      ENNReal.ofReal |(LinearMap.det (sBigL r κ τ))⁻¹| • volume := by
    rw [← Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet]
    rfl
  have h1 : ∫⁻ p, G (sBig r κ τ p) = ENNReal.ofReal |(jacBig r κ τ)⁻¹| * ∫⁻ p, G p := by
    have : (fun p => G (sBig r κ τ p)) = fun p => G (eM p) := by
      funext p; rw [← sBigL_apply]; rfl
    rw [this, ← lintegral_map_equiv, hmap, lintegral_smul_measure, det_sBigL, smul_eq_mul]
  rw [h1, ← mul_assoc, ← ENNReal.ofReal_mul (jacBig_pos hκ hτ).le, abs_inv,
    abs_of_pos (jacBig_pos hκ hτ), mul_inv_cancel₀ (jacBig_pos hκ hτ).ne', ENNReal.ofReal_one, one_mul]

theorem bcWeight_sBig (hκ : 0 < κ) (hτ : 0 < τ) (T T' : ℝ) (p : (Fin r → ℂ) × ℂ) :
    bcWeight k r (τ ^ 2 * T) (τ ^ 2 * T') (sBig r κ τ p) = wBig k r κ τ * bcWeight k r T T' p := by
  have hn : Complex.normSq (((τ ^ 2 : ℝ) : ℂ) * p.2) = τ ^ 4 * Complex.normSq p.2 := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal]; ring
  have h4 : 0 < τ ^ 4 := pow_pos hτ 4
  unfold bcWeight sBig
  simp only
  rw [hn]
  by_cases hc : T * T' ≤ Complex.normSq p.2
  · rw [if_pos (by nlinarith), if_pos hc]
    have hprod : ∏ a : Fin r, ‖((tF r κ τ a.val ^ 2 : ℝ) : ℂ) * p.1 a‖ ^ (2 * (Mdim k r a - 2)) =
        (∏ a : Fin r, (tF r κ τ a.val ^ 2) ^ (2 * (Mdim k r a - 2))) *
          ∏ a : Fin r, ‖p.1 a‖ ^ (2 * (Mdim k r a - 2)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos (tF_pos hκ hτ _) 2), mul_pow]
    rw [hprod, show τ ^ 4 * Complex.normSq p.2 - τ ^ 2 * T * (τ ^ 2 * T') =
      τ ^ 4 * (Complex.normSq p.2 - T * T') by ring, mul_pow, wBig]
    ring
  · rw [if_neg (by intro h; apply hc; nlinarith), if_neg hc, mul_zero]

theorem hsNormSq_eq_sum {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) :
    hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_self_eq_norm_sq_to_K]; norm_cast

theorem hsNormSq_nonneg {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) : 0 ≤ hsNormSq A := by
  rw [hsNormSq_eq_sum]; positivity

theorem hsNormSq_smul {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (C : ℂ) (A : Wq →L[ℂ] Wp) :
    hsNormSq (C • A) = ‖C‖ ^ 2 * hsNormSq A := by
  rw [hsNormSq_eq_sum, hsNormSq_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [FunLike.coe_smul, Pi.smul_apply, norm_smul, mul_pow]

theorem bcWeight_eq_zero_of {T T' : ℝ} (hk : 2 ≤ k) (p : (Fin r → ℂ) × ℂ)
    (h : ¬ ((∀ a, p.1 a ≠ 0) ∧ T * T' < Complex.normSq p.2)) : bcWeight k r T T' p = 0 := by
  unfold bcWeight
  split_ifs with hc
  · rcases not_and_or.mp h with h1 | h1
    · push Not at h1
      obtain ⟨a, ha⟩ := h1
      have hpos : 2 * (Mdim k r a - 2) ≠ 0 := by unfold Mdim; omega
      rw [Finset.prod_eq_zero (Finset.mem_univ a) (by rw [ha, norm_zero, zero_pow hpos]), zero_mul]
    · have : Complex.normSq p.2 = T * T' := le_antisymm (not_lt.mp h1) hc
      rw [this, sub_self, zero_pow (by omega), mul_zero]
  · rfl

theorem jNorm2_tr (hκ : 0 < κ) (hτ : 0 < τ) (L L₁ : LocBessel k r)
    (e1 : Tz k r L₁.z = τ ^ 2 * Tz k r L.z) (e2 : Tz k r L₁.z' = τ ^ 2 * Tz k r L.z')
    (f : Mx k r → (L.Wq →L[ℂ] L.Wp)) (f₁ : Mx k r → (L₁.Wq →L[ℂ] L₁.Wp))
    (μsec μsec₁ : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (C : ℂ)
    (hk : 2 ≤ k)
    (hJ : ∀ p : (Fin r → ℂ) × ℂ, (∀ a, p.1 a ≠ 0) → Tz k r L.z * Tz k r L.z' < Complex.normSq p.2 →
      hsNormSq (L₁.J f₁ (bigCell k r (sBig r κ τ p).1 (μsec₁ (sBig r κ τ p).2))) =
        ‖C‖ ^ 2 * hsNormSq (L.J f (bigCell k r p.1 (μsec p.2)))) :
    jNorm2 L₁ f₁ μsec₁ = ENNReal.ofReal (jacBig r κ τ * wBig k r κ τ * ‖C‖ ^ 2) * jNorm2 L f μsec := by
  unfold jNorm2 jNormSq
  rw [e1, e2, lintegral_sBig hκ hτ]
  have hw := wBig_pos (k := k) (r := r) hκ hτ
  have hpt : ∀ p : (Fin r → ℂ) × ℂ,
      ENNReal.ofReal (bcWeight k r (τ ^ 2 * Tz k r L.z) (τ ^ 2 * Tz k r L.z') (sBig r κ τ p) *
        ‖Real.sqrt (hsNormSq (L₁.J f₁ (bigCell k r (sBig r κ τ p).1 (μsec₁ (sBig r κ τ p).2))))‖ ^ 2) =
      ENNReal.ofReal (wBig k r κ τ * ‖C‖ ^ 2) *
        ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') p *
          ‖Real.sqrt (hsNormSq (L.J f (bigCell k r p.1 (μsec p.2))))‖ ^ 2) := by
    intro p
    by_cases hD : (∀ a, p.1 a ≠ 0) ∧ Tz k r L.z * Tz k r L.z' < Complex.normSq p.2
    swap
    · have h0 := bcWeight_eq_zero_of (T := Tz k r L.z) (T' := Tz k r L.z') hk p (by tauto)
      rw [bcWeight_sBig hκ hτ, h0]; simp
    rw [← ENNReal.ofReal_mul (by positivity), hJ p hD.1 hD.2, bcWeight_sBig hκ hτ,
      Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
      Real.sq_sqrt (mul_nonneg (sq_nonneg _) (hsNormSq_nonneg _)), Real.sq_sqrt (hsNormSq_nonneg _)]
    congr 1; ring
  beta_reduce
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, ← ENNReal.ofReal_mul (jacBig_pos hκ hτ).le,
    mul_assoc (jacBig r κ τ)]

theorem wbPart_smul (z : Fin (2 * r + k + 1) → ℂ) (t : ℂ) : wbPart k r (t • z) = t • wbPart k r z := by
  funext j; rfl

def secTr (τ : ℝ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  fun ζ => μsec (ζ / ((τ ^ 2 : ℝ) : ℂ))

theorem secTr_sBig (hτ : 0 < τ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (p : (Fin r → ℂ) × ℂ) :
    secTr τ μsec (sBig r κ τ p).2 = μsec p.2 := by
  unfold secTr sBig
  have : ((τ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hτ 2).ne'
  simp only
  rw [mul_div_cancel_left₀ _ this]

theorem isSection_tr (hτ : 0 < τ) {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (h : IsSection k r z z' μsec) : IsSection k r ((τ : ℂ) • z) ((τ : ℂ) • z') (secTr τ μsec) := by
  have h2 : ((τ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hτ 2).ne'
  have h4 : 0 < τ ^ 4 := pow_pos hτ 4
  have hns : ∀ ζ : ℂ, Complex.normSq (ζ / ((τ ^ 2 : ℝ) : ℂ)) = Complex.normSq ζ / τ ^ 4 := by
    intro ζ; rw [Complex.normSq_div, Complex.normSq_ofReal]; ring
  have hreg : ∀ ζ : ℂ, Tz k r ((τ : ℂ) • z) * Tz k r ((τ : ℂ) • z') < Complex.normSq ζ →
      Tz k r z * Tz k r z' < Complex.normSq (ζ / ((τ ^ 2 : ℝ) : ℂ)) := by
    intro ζ hζ
    rw [Tz_smul, Tz_smul] at hζ
    rw [hns, lt_div_iff₀ h4]; nlinarith
  refine ⟨fun i j => ?_, fun ζ hζ => ?_⟩
  · have hc : ContDiff ℝ ∞ (fun ζ : ℂ => ζ / ((τ ^ 2 : ℝ) : ℂ)) := by
      have : (fun ζ : ℂ => ζ / ((τ ^ 2 : ℝ) : ℂ)) = fun ζ => ((τ ^ 2)⁻¹ : ℝ) • ζ := by
        funext ζ; rw [Complex.real_smul, div_eq_inv_mul]; push_cast; ring
      rw [this]; exact contDiff_const_smul _
    exact (h.1 i j).comp hc.contDiffOn fun ζ hζ => hreg ζ hζ
  · obtain ⟨hu, hv⟩ := h.2 _ (hreg ζ hζ)
    refine ⟨hu, ?_⟩
    unfold secTr
    rw [wbPart_smul, wbPart_smul]
    unfold herm at hv ⊢
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, hv]
    simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
    field_simp
    push_cast; ring

end Norm

end Formalism.MainNotions.FrameBoundFromBesselTorus
end
end

open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

variable {r : ℕ} {κ τ : ℝ}

theorem frames_ineqs {pw pw₁ s K ρ F : ℝ} (X : ENNReal) (hs : 0 ≤ s) (hK : 0 ≤ K) (hρ : 0 < ρ)
    (h1 : ρ ≤ F) (h2 : ρ⁻¹ ≤ F) (he : pw₁ * s = K * ρ * pw) :
    ENNReal.ofReal pw₁ * (ENNReal.ofReal s * X) ≤ ENNReal.ofReal (K * F) * (ENNReal.ofReal pw * X) ∧
      ENNReal.ofReal K * (ENNReal.ofReal pw * X) ≤ ENNReal.ofReal F * (ENNReal.ofReal pw₁ * (ENNReal.ofReal s * X)) := by
  have hF : 0 < F := lt_of_lt_of_le hρ h1
  rw [← mul_assoc (ENNReal.ofReal pw₁), ← ENNReal.ofReal_mul' hs, he]
  by_cases hp : pw ≤ 0
  · have h0 : K * ρ * pw ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hK hρ.le) hp
    rw [ENNReal.ofReal_of_nonpos h0, ENNReal.ofReal_of_nonpos hp]
    simp
  · push Not at hp
    constructor
    · rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg hK hF.le)]
      gcongr ENNReal.ofReal ?_ * _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hK) hp.le
    · rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_mul hF.le]
      gcongr ENNReal.ofReal ?_ * _
      have : 1 ≤ F * ρ := by
        have := mul_le_mul_of_nonneg_right h2 hρ.le
        rwa [inv_mul_cancel₀ hρ.ne'] at this
      nlinarith [mul_nonneg hK hp.le]

end Formalism.MainNotions.FrameBoundFromBesselTorus
end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.ContinuousRootCoords
open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

section Meas2

variable {k r : ℕ} {κ τ : ℝ}

theorem ofReal_ne_zero_of_pos {α : ℝ} (hα : 0 < α) : ENNReal.ofReal α ≠ 0 := (ENNReal.ofReal_pos.mpr hα).ne'

theorem map_cjT_cjIT_smul (hκ : 0 < κ) (hτ : 0 < τ) {α : ℝ} (hα : 0 < α) (μ₁ : Measure (Mt k r)) :
    ENNReal.ofReal α • ((ENNReal.ofReal α)⁻¹ • μ₁.map (cjIT k r κ τ)).map (cjT k r κ τ) = μ₁ := by
  rw [Measure.map_smul, Measure.map_map measurable_cjT continuous_cjIT.measurable]
  have e : cjT k r κ τ ∘ cjIT k r κ τ = id := funext (cjT_cjIT hκ hτ)
  rw [e, Measure.map_id, smul_smul, ENNReal.mul_inv_cancel (ofReal_ne_zero_of_pos hα) ENNReal.ofReal_ne_top,
    one_smul]
  exact measurable_cjT.aemeasurable

theorem phiP_phiPI (hκ : 0 < κ) (hτ : 0 < τ) (p : PairSp k r) : phiP k r κ τ (phiPI k r κ τ p) = p :=
  Prod.ext (Prod.ext (cjT_cjIT hκ hτ _) (cjT_cjIT hκ hτ _)) (Prod.ext (cjT_cjIT hκ hτ _) (cjT_cjIT hκ hτ _))

theorem use₉ (hκ : 0 < κ) (hτ : 0 < τ) {α : ℝ} (hα : 0 < α) (ν₁ : Measure (PairSp k r)) :
    (ENNReal.ofReal α)⁻¹ • (ENNReal.ofReal α • ν₁.map (phiPI k r κ τ)).map (phiP k r κ τ) = ν₁ := by
  rw [Measure.map_smul, Measure.map_map measurable_phiP measurable_phiPI]
  have e : phiP k r κ τ ∘ phiPI k r κ τ = id := funext (phiP_phiPI hκ hτ)
  rw [e, Measure.map_id, smul_smul, ENNReal.inv_mul_cancel (ofReal_ne_zero_of_pos hα) ENNReal.ofReal_ne_top,
    one_smul]
  exact measurable_phiP.aemeasurable

theorem stabAct_phiP (hκ : 0 < κ) (hτ : 0 < τ) (g a : Mx k r) (x : PairSp k r) :
    stabAct (cj k r κ τ g) (cj k r κ τ a) (phiP k r κ τ x) = phiP k r κ τ (stabAct g a x) := by
  obtain ⟨⟨h, n⟩, ⟨h', n'⟩⟩ := x
  refine Prod.ext (Prod.ext rfl ?_) (Prod.ext rfl ?_)
  · funext i j
    show (cj k r κ τ a * cj k r κ τ (Matrix.of n)) i j = cj k r κ τ (a * Matrix.of n) i j
    rw [cj_mul hκ hτ]
  · funext i j
    show ((cj k r κ τ g)⁻¹ * cj k r κ τ a * cj k r κ τ g * cj k r κ τ (Matrix.of n')) i j =
      cj k r κ τ (g⁻¹ * a * g * Matrix.of n') i j
    rw [cj_mul hκ hτ, cj_mul hκ hτ, cj_mul hκ hτ, cj_inv hκ hτ]

theorem isOrbQuot_map_iff (hκ : 0 < κ) (hτ : 0 < τ) (L L₁ : LocBessel k r)
    (hP : pairMeas L₁ = (pairMeas L).map (phiP k r κ τ))
    (g : Mx k r) (μR : Measure (Mt k r)) (ν : Measure (PairSp k r)) {α : ℝ} (hα : 0 < α) :
    IsOrbQuot L₁ (cj k r κ τ g) (ENNReal.ofReal α • μR.map (cjT k r κ τ))
        ((ENNReal.ofReal α)⁻¹ • ν.map (phiP k r κ τ)) ↔ IsOrbQuot L g μR ν := by
  have ha0 := ofReal_ne_zero_of_pos hα
  have hat : ENNReal.ofReal α ≠ ⊤ := ENNReal.ofReal_ne_top
  have key : ∀ f : PairSp k r → ENNReal,
      ∫⁻ x, (∫⁻ a, f (stabAct (cj k r κ τ g) (Matrix.of a) x) ∂(ENNReal.ofReal α • μR.map (cjT k r κ τ)))
        ∂((ENNReal.ofReal α)⁻¹ • ν.map (phiP k r κ τ)) =
      ∫⁻ x, (∫⁻ a, f (phiP k r κ τ (stabAct g (Matrix.of a) x)) ∂μR) ∂ν := by
    intro f
    have inner : ∀ x, ∫⁻ a, f (stabAct (cj k r κ τ g) (Matrix.of a) x)
        ∂(ENNReal.ofReal α • μR.map (cjT k r κ τ)) =
        ENNReal.ofReal α * ∫⁻ a, f (stabAct (cj k r κ τ g) (cj k r κ τ (Matrix.of a)) x) ∂μR := by
      intro x
      rw [lintegral_smul_measure, smul_eq_mul, ← cjE_coe hκ hτ, lintegral_map_equiv]
      rfl
    simp_rw [inner]
    rw [lintegral_smul_measure, smul_eq_mul, lintegral_const_mul' _ _ hat, ← mul_assoc,
      ENNReal.inv_mul_cancel ha0 hat, one_mul, ← phiE_coe hκ hτ, lintegral_map_equiv]
    simp only [phiE_coe, stabAct_phiP hκ hτ]
  have hs : ∀ y, (phiE hκ hτ).symm (phiP k r κ τ y) = y := fun y => (phiE hκ hτ).symm_apply_apply y
  unfold IsOrbQuot
  rw [hP]
  constructor
  · intro h f hf
    have h1 := h (f ∘ (phiE hκ hτ).symm) (hf.comp (phiE hκ hτ).symm.measurable)
    rw [key (f ∘ (phiE hκ hτ).symm)] at h1
    rw [← phiE_coe hκ hτ, lintegral_map_equiv] at h1
    simp only [Function.comp_apply, phiE_coe, hs] at h1
    exact h1
  · intro h f hf
    rw [key f, ← phiE_coe hκ hτ, lintegral_map_equiv]
    exact h (fun y => f (phiE hκ hτ y)) (hf.comp (phiE hκ hτ).measurable)

theorem IsOrbQuot_trD_iff (hκ : 0 < κ) (hτ : 0 < τ) (L : LocBessel k r)
    (hz : inWb k r ((τ : ℂ) • L.z) ∧ 0 < Tz k r ((τ : ℂ) • L.z))
    (hz' : inWb k r ((τ : ℂ) • L.z') ∧ 0 < Tz k r ((τ : ℂ) • L.z'))
    (hπ : IsHCTypeW k r ((τ : ℂ) • L.z) L.u (fun x => L.π (cjI k r κ τ x)))
    (hπ' : IsHCTypeW k r ((τ : ℂ) • L.z') L.u' (fun x => L.π' (cjI k r κ τ x)))
    (hμW : IsHaarOn (UWset k r ((τ : ℂ) • L.z)) (L.μW.map (cjT k r κ τ)) ∧ L.μW.map (cjT k r κ τ) Set.univ = 1)
    (hμW' : IsHaarOn (UWset k r ((τ : ℂ) • L.z')) (L.μW'.map (cjT k r κ τ)) ∧
      L.μW'.map (cjT k r κ τ) Set.univ = 1)
    (g : Mx k r) (μR : Measure (Mt k r)) (ν : Measure (PairSp k r)) {α : ℝ} (hα : 0 < α) :
    IsOrbQuot (trD L κ τ (L.κN * ENNReal.ofReal (deltaN k r κ τ)) hz hz' hπ hπ' hμW hμW') (cj k r κ τ g)
        (ENNReal.ofReal α • μR.map (cjT k r κ τ)) ((ENNReal.ofReal α)⁻¹ • ν.map (phiP k r κ τ)) ↔
      IsOrbQuot L g μR ν :=
  isOrbQuot_map_iff hκ hτ L _ (pairMeas_trD hκ hτ L hz hz' hπ hπ' hμW hμW') g μR ν hα

def scC {P : Type*} [Fintype P] (lam : P → ℝ) : (P → ℂ) →ₗ[ℝ] (P → ℂ) :=
  LinearMap.pi fun p => (lam p • LinearMap.id) ∘ₗ LinearMap.proj p

theorem scC_apply {P : Type*} [Fintype P] (lam : P → ℝ) (v : P → ℂ) (p : P) :
    scC lam v p = ((lam p : ℝ) : ℂ) * v p := by
  simp [scC, Complex.real_smul]

theorem det_scC {P : Type*} [Fintype P] (lam : P → ℝ) : LinearMap.det (scC lam) = ∏ p, lam p ^ 2 := by
  rw [scC, LinearMap.det_pi]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [LinearMap.det_smul, LinearMap.det_id, Complex.finrank_real_complex, mul_one]

theorem map_scC_volume {P : Type*} [Fintype P] (lam : P → ℝ) (h : ∀ p, lam p ≠ 0) :
    (volume : Measure (P → ℂ)).map (fun v p => ((lam p : ℝ) : ℂ) * v p) =
      ENNReal.ofReal (∏ p, lam p ^ 2)⁻¹ • volume := by
  have hd : LinearMap.det (scC lam) ≠ 0 := by
    rw [det_scC]; exact Finset.prod_ne_zero_iff.mpr fun p _ => pow_ne_zero _ (h p)
  have e : (fun (v : P → ℂ) p => ((lam p : ℝ) : ℂ) * v p) = ⇑(scC lam) :=
    funext fun v => funext fun p => (scC_apply lam v p).symm
  rw [e, Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd, det_scC,
    abs_of_nonneg (inv_nonneg.mpr (Finset.prod_nonneg fun p _ => sq_nonneg _))]

theorem continuous_rootCoords (z : Fin (2 * r + k + 1) → ℂ) (γ : Point ℂ (r + 1)) :
    Continuous (rootCoords k r z γ) := by
  refine continuous_pi fun p => ?_
  by_cases hi : (p.1.1 : ℕ) < r
  · have e : (fun x => rootCoords k r z γ x p) =
        fun x : Mt k r => ((Matrix.of x : Mx k r) *ᵥ fvec k r z p.1.2) (eI k r ⟨p.1.1.val, hi⟩) := by
      funext x; simp only [rootCoords, flagMat, dif_pos hi]
    rw [e]
    have hc : Continuous fun x : Mt k r => ((Matrix.of x : Mx k r) *ᵥ fvec k r z p.1.2) :=
      Continuous.matrix_mulVec (A := fun x : Mt k r => (Matrix.of x : Mx k r)) (B := fun _ => fvec k r z p.1.2)
        continuous_id continuous_const
    exact (continuous_apply (eI k r ⟨p.1.1.val, hi⟩)).comp hc
  · have e : (fun x => rootCoords k r z γ x p) = fun _ : Mt k r => (if p.1.1 = p.1.2 then (1 : ℂ) else 0) := by
      funext x; simp only [rootCoords, flagMat, dif_neg hi]
    rw [e]
    exact continuous_const

theorem isRootMeas_congr_pat (L : LocBessel k r) {γ₁ γ : Point ℂ (r + 1)} (h : rootPat γ₁ = rootPat γ)
    (g : Mx k r) (μR : Measure (Mt k r)) : IsRootMeas L γ₁ g μR ↔ IsRootMeas L γ g μR := by
  unfold IsRootMeas rootCoords
  rw [h]

theorem ar1 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) : (a * b)⁻¹ * (a * c) * b = c := by
  rw [mul_inv]
  calc a⁻¹ * b⁻¹ * (a * c) * b = (a⁻¹ * a) * (b⁻¹ * b) * c := by ring
    _ = c := by rw [inv_mul_cancel₀ ha, inv_mul_cancel₀ hb]; ring

theorem ar2 {a b c : ℝ} (hb : b ≠ 0) : a * b * c * b⁻¹ = a * c := by
  calc a * b * c * b⁻¹ = a * c * (b * b⁻¹) := by ring
    _ = a * c := by rw [mul_inv_cancel₀ hb, mul_one]

theorem isRootMeas_map_iff (hκ : 0 < κ) (hτ : 0 < τ) (L L₁ : LocBessel k r) (hz₁ : L₁.z = (τ : ℂ) • L.z)
    (hc₁ : L₁.c = (κ : ℂ) * L.c) (γ : Point ℂ (r + 1)) (g : Mx k r) (μR : Measure (Mt k r)) :
    IsRootMeas L₁ γ (cj k r κ τ g) (ENNReal.ofReal (alphaPt κ τ γ) • μR.map (cjT k r κ τ)) ↔
      IsRootMeas L γ g μR := by
  have hz := L.hz.1
  obtain ⟨lam, hlam_def⟩ : ∃ lam : rootPat γ → ℝ, lam = fun p => tF r κ τ p.1.2.val / tF r κ τ p.1.1.val :=
    ⟨_, rfl⟩
  have hlam : ∀ p, 0 < lam p := fun p => by
    rw [hlam_def]; exact div_pos (tF_pos hκ hτ _) (tF_pos hκ hτ _)
  obtain ⟨B, hB_def⟩ : ∃ B : ℝ, B = ∏ p, lam p ^ 2 := ⟨_, rfl⟩
  have hB : 0 < B := by rw [hB_def]; exact Finset.prod_pos fun p _ => pow_pos (hlam p) 2
  have hA : alphaPt κ τ γ = κ ^ (rootPat γ).card * B := by
    rw [hB_def, hlam_def]; unfold alphaPt; rw [← Finset.prod_coe_sort]
  have hApos : 0 < alphaPt κ τ γ := by rw [hA]; exact mul_pos (pow_pos hκ _) hB
  have hκn : κ ^ (rootPat γ).card ≠ 0 := pow_ne_zero _ hκ.ne'
  obtain ⟨D, hD⟩ : ∃ D : (rootPat γ → ℂ) → (rootPat γ → ℂ), D = fun v p => ((lam p : ℝ) : ℂ) * v p := ⟨_, rfl⟩
  obtain ⟨D', hD'⟩ : ∃ D' : (rootPat γ → ℂ) → (rootPat γ → ℂ), D' = fun v p => (((lam p)⁻¹ : ℝ) : ℂ) * v p :=
    ⟨_, rfl⟩
  have hDm : Measurable D := by
    rw [hD]; exact (continuous_pi fun p => continuous_const.mul (continuous_apply p)).measurable
  have hD'm : Measurable D' := by
    rw [hD']; exact (continuous_pi fun p => continuous_const.mul (continuous_apply p)).measurable
  have hDD : D' ∘ D = id := by
    funext v p
    rw [hD, hD']
    show (((lam p)⁻¹ : ℝ) : ℂ) * (((lam p : ℝ) : ℂ) * v p) = v p
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (hlam p).ne', Complex.ofReal_one, one_mul]
  have hRc := (continuous_rootCoords (k := k) (r := r) L.z γ).measurable
  have hcomp : rootCoords k r ((τ : ℂ) • L.z) γ ∘ cjT k r κ τ = D ∘ rootCoords k r L.z γ :=
    funext fun x => funext fun p => by rw [hD, hlam_def]; exact rootCoords_cjT hκ hτ hz γ x p
  have hmap : (ENNReal.ofReal (alphaPt κ τ γ) • μR.map (cjT k r κ τ)).map (rootCoords k r ((τ : ℂ) • L.z) γ) =
      ENNReal.ofReal (alphaPt κ τ γ) • (μR.map (rootCoords k r L.z γ)).map D := by
    rw [Measure.map_smul, Measure.map_map (continuous_rootCoords _ γ).measurable measurable_cjT, hcomp,
      ← Measure.map_map hDm hRc]
    exact (continuous_rootCoords _ γ).measurable.aemeasurable
  have hnorm : (‖(κ : ℂ) * L.c‖ / (2 * Real.pi)) ^ (rootPat γ).card =
      κ ^ (rootPat γ).card * (‖L.c‖ / (2 * Real.pi)) ^ (rootPat γ).card := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hκ.le, mul_div_assoc, mul_pow]
  have hB' : ∏ p, ((lam p)⁻¹) ^ 2 = B⁻¹ := by
    rw [hB_def, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun p _ => inv_pow _ _
  have hC0 : 0 ≤ (‖L.c‖ / (2 * Real.pi)) ^ (rootPat γ).card := by positivity
  have hvolD : (volume : Measure (rootPat γ → ℂ)).map D = ENNReal.ofReal B⁻¹ • volume := by
    rw [hD, map_scC_volume lam (fun p => (hlam p).ne'), ← hB_def]
  have hvolD' : (volume : Measure (rootPat γ → ℂ)).map D' = ENNReal.ofReal B • volume := by
    rw [hD', map_scC_volume (fun p => (lam p)⁻¹) (fun p => inv_ne_zero (hlam p).ne'), hB', inv_inv]
  unfold IsRootMeas
  rw [hz₁, hc₁]
  apply and_congr
  · rw [Measure.smul_apply, smul_eq_mul, ← cjE_coe hκ hτ, MeasurableEquiv.map_apply, mul_eq_zero]
    have hset : (cjE hκ hτ) ⁻¹' {x : Mt k r | Matrix.of x ∉ RStab k r (cj k r κ τ g)} =
        {x : Mt k r | Matrix.of x ∉ RStab k r g} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, cjE_coe, of_cjT, cj_mem_RStab_iff hκ hτ]
    rw [hset]
    exact or_iff_right (ofReal_ne_zero_of_pos hApos)
  · rw [hmap, hnorm]
    constructor
    · intro h
      have h2 : (μR.map (rootCoords k r L.z γ)).map D = (ENNReal.ofReal (alphaPt κ τ γ))⁻¹ •
          ENNReal.ofReal (κ ^ (rootPat γ).card * (‖L.c‖ / (2 * Real.pi)) ^ (rootPat γ).card) • volume := by
        rw [← h, smul_smul, ENNReal.inv_mul_cancel (ofReal_ne_zero_of_pos hApos) ENNReal.ofReal_ne_top,
          one_smul]
      have hX : μR.map (rootCoords k r L.z γ) = ((μR.map (rootCoords k r L.z γ)).map D).map D' := by
        rw [Measure.map_map hD'm hDm, hDD, Measure.map_id]
      rw [hX, h2, Measure.map_smul, Measure.map_smul, hvolD', smul_smul, smul_smul]
      congr 1
      rw [← ENNReal.ofReal_inv_of_pos hApos, ← ENNReal.ofReal_mul (inv_nonneg.mpr hApos.le),
        ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr hApos.le) (mul_nonneg (pow_nonneg hκ.le _) hC0)), hA]
      congr 1
      exact ar1 hκn hB.ne'
      all_goals exact hD'm.aemeasurable
    · intro h
      rw [h, Measure.map_smul, hvolD, smul_smul, smul_smul]
      congr 1
      rw [← ENNReal.ofReal_mul hApos.le, ← ENNReal.ofReal_mul (mul_nonneg hApos.le hC0), hA]
      congr 1
      exact ar2 hB.ne'
      all_goals exact hDm.aemeasurable

theorem IsRootMeas_trD_iff (hκ : 0 < κ) (hτ : 0 < τ) (L : LocBessel k r) (κN₁ : ENNReal)
    (hz : inWb k r ((τ : ℂ) • L.z) ∧ 0 < Tz k r ((τ : ℂ) • L.z))
    (hz' : inWb k r ((τ : ℂ) • L.z') ∧ 0 < Tz k r ((τ : ℂ) • L.z'))
    (hπ : IsHCTypeW k r ((τ : ℂ) • L.z) L.u (fun x => L.π (cjI k r κ τ x)))
    (hπ' : IsHCTypeW k r ((τ : ℂ) • L.z') L.u' (fun x => L.π' (cjI k r κ τ x)))
    (hμW : IsHaarOn (UWset k r ((τ : ℂ) • L.z)) (L.μW.map (cjT k r κ τ)) ∧ L.μW.map (cjT k r κ τ) Set.univ = 1)
    (hμW' : IsHaarOn (UWset k r ((τ : ℂ) • L.z')) (L.μW'.map (cjT k r κ τ)) ∧
      L.μW'.map (cjT k r κ τ) Set.univ = 1)
    {γ₁ γ : Point ℂ (r + 1)} (hγ : rootPat γ₁ = rootPat γ) (g : Mx k r) (μR : Measure (Mt k r)) :
    IsRootMeas (trD L κ τ κN₁ hz hz' hπ hπ' hμW hμW') γ₁ (cj k r κ τ g)
        (ENNReal.ofReal (alphaPt κ τ γ) • μR.map (cjT k r κ τ)) ↔ IsRootMeas L γ g μR := by
  rw [isRootMeas_congr_pat _ hγ]
  exact isRootMeas_map_iff hκ hτ L _ rfl rfl γ g μR

end Meas2

end Formalism.MainNotions.FrameBoundFromBesselTorus
end
end

open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

def OneBesselTor (D : D7) (Cgf : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (κ₀ κ τ : ℝ),
    0 < κ₀ → 0 < κ → 0 < τ → L.c = cOfDpsi (κ₀ : ℂ) → 0 < L.κN → L.κN ≠ ⊤ → L.ε = epsSH D.R →
    GapAtLeast L.ε L.lam (Cgf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3)) →
    IsKFinCoefH L.σ f →
    ∃ (f₁ : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (C : ℂ), C ≠ 0 ∧ IsKFinCoefH L.σ f₁ ∧
      (∀ (c : Fin D.R.rS → ℂ) (μ : Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ), (∀ a, c a ≠ 0) →
        μᴴ * Hb D.R.k * μ = Hb D.R.k →
        L.J (fun x => f₁ (cj D.R.k D.R.rS κ τ x)) (bigCell D.R.k D.R.rS c μ) =
          C • L.J f (bigCell D.R.k D.R.rS c μ)) ∧
      (∀ (γ : Point ℂ (D.R.rS + 1)) (g : Mx D.R.k D.R.rS) (μR : Measure (Mt D.R.k D.R.rS))
        (ν : Measure (PairSp D.R.k D.R.rS)),
        Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → IsPtRep L γ g → IsRelStab L g →
        IsRootMeas L γ g μR → IsOrbQuot L g μR ν →
        OrbInt L (fun x => f₁ (cj D.R.k D.R.rS κ τ x)) g ν = C • OrbInt L f g ν)

section Dat

variable {k r : ℕ} {κ τ : ℝ}

theorem hzTr (L : LocBessel k r) (hτ : 0 < τ) : inWb k r ((τ : ℂ) • L.z) ∧ 0 < Tz k r ((τ : ℂ) • L.z) := by
  obtain ⟨h1, h2⟩ := L.hz
  unfold inWb Tz at *
  refine ⟨fun i hi => by simp [h1 i hi], ?_⟩
  unfold herm at *
  have e : star ((τ : ℂ) • L.z) ⬝ᵥ Hpk k r *ᵥ ((τ : ℂ) • L.z) =
      ((τ : ℂ) * τ) * (star L.z ⬝ᵥ Hpk k r *ᵥ L.z) := by
    rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    simp only [Complex.star_def, Complex.conj_ofReal]
    ring
  rw [e, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  have hp : 0 < τ * τ := mul_pos hτ hτ
  nlinarith

theorem hzTr' (L : LocBessel k r) (hτ : 0 < τ) : inWb k r ((τ : ℂ) • L.z') ∧ 0 < Tz k r ((τ : ℂ) • L.z') := by
  obtain ⟨h1, h2⟩ := L.hz'
  unfold inWb Tz at *
  refine ⟨fun i hi => by simp [h1 i hi], ?_⟩
  unfold herm at *
  have e : star ((τ : ℂ) • L.z') ⬝ᵥ Hpk k r *ᵥ ((τ : ℂ) • L.z') =
      ((τ : ℂ) * τ) * (star L.z' ⬝ᵥ Hpk k r *ᵥ L.z') := by
    rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    simp only [Complex.star_def, Complex.conj_ofReal]
    ring
  rw [e, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  have hp : 0 < τ * τ := mul_pos hτ hτ
  nlinarith

abbrev trDat (L : LocBessel k r) (κ τ : ℝ) (hκ : 0 < κ) (hτ : 0 < τ) : LocBessel k r :=
  trD L κ τ (L.κN * ENNReal.ofReal (deltaN k r κ τ)) (hzTr L hτ) (hzTr' L hτ)
    (isHCTypeW_cjI hκ hτ L.hz.1 L.hπ) (isHCTypeW_cjI hκ hτ L.hz'.1 L.hπ')
    ⟨isHaarOn_map_cjT hκ hτ L.hz.1 L.hμW.1, by rw [map_cjT_univ]; exact L.hμW.2⟩
    ⟨isHaarOn_map_cjT hκ hτ L.hz'.1 L.hμW'.1, by rw [map_cjT_univ]; exact L.hμW'.2⟩

theorem alphaPt_pos (hκ : 0 < κ) (hτ : 0 < τ) (γ : Point ℂ (r + 1)) : 0 < alphaPt κ τ γ := by
  unfold alphaPt tF
  positivity

theorem isPtRep_trDat (hκ : 0 < κ) (hτ : 0 < τ) (L : LocBessel k r) (γ : Point ℂ (r + 1)) (g : Mx k r) :
    IsPtRep (trDat L κ τ hκ hτ) (ptTr κ τ hκ hτ γ) (cj k r κ τ g) ↔ IsPtRep L γ g := by
  unfold IsPtRep
  apply and_congr (cj_mem_UH_iff hκ hτ g)
  show Zhat k r ((τ : ℂ) • L.z) ((τ : ℂ) • L.z') (cj k r κ τ g) = ptMat (ptTr κ τ hκ hτ γ) ↔
    Zhat k r L.z L.z' g = ptMat γ
  constructor
  · intro h
    ext a b
    have h1 : Zhat k r ((τ : ℂ) • L.z) ((τ : ℂ) • L.z') (cj k r κ τ g) a b = ptMat (ptTr κ τ hκ hτ γ) a b := by
      rw [h]
    rw [Zhat_cj hκ hτ L.hz.1 L.hz'.1, ptMat_ptTr hκ hτ] at h1
    have hne : ((tF r κ τ a * tF r κ τ b : ℝ) : ℂ) ≠ 0 := by
      have hp : 0 < tF r κ τ a * tF r κ τ b := by
        unfold tF
        positivity
      exact_mod_cast hp.ne'
    exact mul_left_cancel₀ hne h1
  · intro h
    ext a b
    rw [Zhat_cj hκ hτ L.hz.1 L.hz'.1, ptMat_ptTr hκ hτ, h]

theorem orbSq_trDat (hκ : 0 < κ) (hτ : 0 < τ) (L : LocBessel k r) (F F₁ : Mx k r → (L.Wq →L[ℂ] L.Wp))
    (γ : Point ℂ (r + 1)) (C : ℂ)
    (hO : ∀ (g : Mx k r) (μR : Measure (Mt k r)) (ν : Measure (PairSp k r)), IsPtRep L γ g → IsRelStab L g →
      IsRootMeas L γ g μR → IsOrbQuot L g μR ν →
      OrbInt L (fun x => F₁ (cj k r κ τ x)) g ν = C • OrbInt L F g ν) :
    orbSq (trDat L κ τ hκ hτ) F₁ (ptTr κ τ hκ hτ γ) =
      ENNReal.ofReal ((alphaPt κ τ γ)⁻¹ ^ 2 * ‖C‖ ^ 2) * orbSq L F γ := by
  have hα := alphaPt_pos hκ hτ γ
  set α := alphaPt κ τ γ with hαdef
  have hpat : rootPat (ptTr κ τ hκ hτ γ) = rootPat γ := rootPat_ptTr hκ hτ γ
  have hrel : ∀ g, IsRelStab (trDat L κ τ hκ hτ) (cj k r κ τ g) ↔ IsRelStab L g := fun g =>
    isRelStab_iff hκ hτ L (trDat L κ τ hκ hτ) L.hz.1 L.hz'.1 rfl rfl rfl g
  have hroot : ∀ g μR, IsRootMeas (trDat L κ τ hκ hτ) (ptTr κ τ hκ hτ γ) (cj k r κ τ g)
      (ENNReal.ofReal α • Measure.map (cjT k r κ τ) μR) ↔ IsRootMeas L γ g μR := fun g μR =>
    IsRootMeas_trD_iff hκ hτ L _ _ _ _ _ _ _ hpat g μR
  have hquot : ∀ g μR ν, IsOrbQuot (trDat L κ τ hκ hτ) (cj k r κ τ g)
      (ENNReal.ofReal α • Measure.map (cjT k r κ τ) μR) ((ENNReal.ofReal α)⁻¹ • Measure.map (phiP k r κ τ) ν) ↔
      IsOrbQuot L g μR ν := fun g μR ν => IsOrbQuot_trD_iff hκ hτ L _ _ _ _ _ _ g μR ν hα
  have key : ∀ g μR ν, IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR → IsOrbQuot L g μR ν →
      ENNReal.ofReal (hsNormSq (OrbInt (trDat L κ τ hκ hτ) F₁ (cj k r κ τ g)
        ((ENNReal.ofReal α)⁻¹ • Measure.map (phiP k r κ τ) ν))) =
      ENNReal.ofReal (α⁻¹ ^ 2 * ‖C‖ ^ 2) * ENNReal.ofReal (hsNormSq (OrbInt L F g ν)) := by
    intro g μR ν h1 h2 h3 h4
    show ENNReal.ofReal (@hsNormSq L.Wp L.Wq _ _ _ _ _ (OrbInt (trDat L κ τ hκ hτ) F₁ (cj k r κ τ g)
      ((ENNReal.ofReal α)⁻¹ • Measure.map (phiP k r κ τ) ν))) = _
    rw [OrbInt_trD hκ hτ L _ _ _ _ _ _ _ F₁ g _ ν, hO g μR ν h1 h2 h3 h4, smul_smul, hsNormSq_smul,
      ENNReal.toReal_inv, ENNReal.toReal_ofReal hα.le, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hα, mul_pow]
  unfold orbSq
  apply le_antisymm
  · refine iSup_le fun g₁ => iSup_le fun μR₁ => iSup_le fun ν₁ => iSup_le fun h => ?_
    obtain ⟨g, rfl⟩ : ∃ g, g₁ = cj k r κ τ g := ⟨cjI k r κ τ g₁, (cj_cjI hκ hτ g₁).symm⟩
    obtain ⟨μR, rfl⟩ : ∃ μR, μR₁ = ENNReal.ofReal α • Measure.map (cjT k r κ τ) μR :=
      ⟨_, (map_cjT_cjIT_smul hκ hτ hα μR₁).symm⟩
    obtain ⟨ν, rfl⟩ : ∃ ν, ν₁ = (ENNReal.ofReal α)⁻¹ • Measure.map (phiP k r κ τ) ν :=
      ⟨_, (use₉ hκ hτ hα ν₁).symm⟩
    obtain ⟨h1, h2, h3, h4⟩ := h
    have h1' := (isPtRep_trDat hκ hτ L γ g).mp h1
    have h2' := (hrel g).mp h2
    have h3' := (hroot g μR).mp h3
    have h4' := (hquot g μR ν).mp h4
    rw [key g μR ν h1' h2' h3' h4']
    gcongr
    exact le_iSup_of_le g (le_iSup_of_le μR (le_iSup_of_le ν (le_iSup_of_le ⟨h1', h2', h3', h4'⟩ le_rfl)))
  · simp_rw [ENNReal.mul_iSup]
    refine iSup_le fun g => iSup_le fun μR => iSup_le fun ν => iSup_le fun h => ?_
    obtain ⟨h1, h2, h3, h4⟩ := h
    rw [← key g μR ν h1 h2 h3 h4]
    exact le_iSup_of_le (cj k r κ τ g) (le_iSup_of_le (ENNReal.ofReal α • Measure.map (cjT k r κ τ) μR)
      (le_iSup_of_le ((ENNReal.ofReal α)⁻¹ • Measure.map (phiP k r κ τ) ν)
        (le_iSup_of_le ⟨(isPtRep_trDat hκ hτ L γ g).mpr h1, (hrel g).mpr h2, (hroot g μR).mpr h3,
          (hquot g μR ν).mpr h4⟩ le_rfl)))

theorem jacBig_eq (r : ℕ) (κ τ : ℝ) : jacBig r κ τ = τ ^ (4 * (r + 1)) * κ ^ (2 * r * (r + 1)) := by
  unfold jacBig tF
  have key : ∀ n : ℕ, 2 * ∑ i ∈ Finset.range n, (n - i) = n * (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have h2 : ∑ i ∈ Finset.range n, (n + 1 - i) = ∑ i ∈ Finset.range n, ((n - i) + 1) :=
        Finset.sum_congr rfl fun i hi => by
          have := Finset.mem_range.mp hi
          omega
      rw [h2, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
      have h3 : n + 1 - n = 1 := by omega
      rw [h3]
      nlinarith [ih]
  have hsum : ∑ a : Fin r, 4 * (r - (a : ℕ)) = 2 * r * (r + 1) := by
    rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => r - i) r]
    have := key r
    nlinarith [this]
  calc (∏ a : Fin r, (τ * κ ^ (r - (a : ℕ))) ^ 4) * τ ^ 4
      = (∏ a : Fin r, (τ ^ 4 * κ ^ (4 * (r - (a : ℕ))))) * τ ^ 4 := by
        congr 1
        refine Finset.prod_congr rfl fun a _ => ?_
        rw [mul_pow, ← pow_mul, mul_comm (r - (a : ℕ)) 4]
    _ = τ ^ (4 * r) * κ ^ (∑ a : Fin r, 4 * (r - (a : ℕ))) * τ ^ 4 := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul,
          Finset.prod_pow_eq_pow_sum]
    _ = τ ^ (4 * (r + 1)) * κ ^ (2 * r * (r + 1)) := by
        rw [hsum]
        ring

theorem wBig_eq_Wbig (hk : 1 ≤ k) (r : ℕ) (κ τ : ℝ) : wBig k r κ τ = Wbig k r κ τ := by
  unfold wBig Wbig Mdim
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun a _ => ?_
    rw [Fin.coe_castSucc, ← pow_mul]
    congr 1
    omega
  · simp only [Fin.val_last, tF, Nat.sub_self, pow_zero, mul_one, Nat.mul_zero, zero_add]
    rw [← pow_mul]

end Dat

end Formalism.MainNotions.FrameBoundFromBesselTorus
