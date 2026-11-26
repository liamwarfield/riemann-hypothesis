module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjectionBounds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStF
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResSymGram

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResChiSandwichLower
section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResChiSandwichUpper
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace ResChiSandwich

open MvPolynomial MeasureTheory Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjectionBounds
open scoped ComplexOrder Matrix

noncomputable section

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem trace_comb_le {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e) {N r : ℕ}
    (f : Fin r → MvPolynomial (Ix κ) ℤ) (g : Fin r → MvPolynomial (Fin (D + 1)) ℤ)
    (hf : ∀ k, (f k).IsHomogeneous N) (hg : ∀ k, (g k).IsHomogeneous N)
    (htr : ∀ k, aeval (x ∘ e) (g k) = secTrace x e N (aeval x (f k))) (c : Fin r → ℂ) {S : ℝ}
    (hS : ∀ z ∈ pts (coordIdeal ℤ x),
      ‖∑ k, c k * eval z (map (Int.castRingHom ℂ) (f k))‖ ≤ S * pnorm e z ^ N)
    (w : Fin (D + 1) → ℂ) :
    ‖∑ k, c k * eval w (map (Int.castRingHom ℂ) (g k))‖ ≤
      (projDeg x e : ℝ) * S * Real.sqrt (sqN w) ^ N := by
  classical
  obtain ⟨Δ, hΔ0, hΔ⟩ := exists_isDiscr hfr
  have hFc : Continuous fun w : Fin (D + 1) → ℂ => ‖∑ k, c k * eval w (map (Int.castRingHom ℂ) (g k))‖ :=
    (continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_eval _)).norm
  have hGc : Continuous fun w : Fin (D + 1) → ℂ => (projDeg x e : ℝ) * S * Real.sqrt (sqN w) ^ N := by
    unfold sqN
    fun_prop
  have hgood : ∀ w ∈ {w : Fin (D + 1) → ℂ | eval w Δ ≠ 0},
      w ∈ {w : Fin (D + 1) → ℂ | ‖∑ k, c k * eval w (map (Int.castRingHom ℂ) (g k))‖ ≤
        (projDeg x e : ℝ) * S * Real.sqrt (sqN w) ^ N} := by
    intro w hw
    obtain ⟨hfin, hcard, -, htrace⟩ := hΔ w hw
    simp only [Set.mem_ofPred_eq]
    have hsum : ∑ k, c k * eval w (map (Int.castRingHom ℂ) (g k)) =
        ∑ z ∈ hfin.toFinset, ∑ k, c k * eval z (map (Int.castRingHom ℂ) (f k)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [htrace N (f k) (g k) (hf k) (hg k) (htr k), finsum_mem_eq_finite_toFinset_sum _ hfin,
        Finset.mul_sum]
    rw [hsum]
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ z ∈ hfin.toFinset,
        ‖∑ k, c k * eval z (map (Int.castRingHom ℂ) (f k))‖ ≤ S * Real.sqrt (sqN w) ^ N := by
      intro z hz
      rw [Set.Finite.mem_toFinset] at hz
      have h := hS z hz.1
      have hw' : z ∘ e = w := funext hz.2
      rwa [pnorm_eq_sqN, hw'] at h
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin, hcard, mul_assoc]
  have hcl := closure_minimal hgood (isClosed_le hFc hGc)
  rw [(dense_eval_ne_zero hΔ0).closure_eq] at hcl
  exact hcl (Set.mem_univ w)

theorem quad_upper_pull {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e) (hFS : IsPullFS x e m)
    {n k r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ} (hb : IsSecBasis x n b)
    (H : Fin (projDeg x e) → MvPolynomial (Ix κ) ℤ) (hH : ∀ l, (H l).IsHomogeneous k)
    (g : Fin r → Fin (projDeg x e) → MvPolynomial (Fin (D + 1)) ℤ)
    (hgh : ∀ j l, (g j l).IsHomogeneous (n + k))
    (hgv : ∀ j l, aeval (x ∘ e) (g j l) = secTrace x e (n + k) (aeval x (b j) * aeval x (H l)))
    {Cε : ℝ} (hCε : ∀ l, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (H l))‖ ≤ Cε * m.ρ z ^ k)
    {B : ℝ} (hB : 0 ≤ B) (hsup : ∀ c : Fin r → ℂ, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖∑ j, c j * secFun (b j) z‖ ^ 2 * wgt m n z ≤ B * bNormSq μ (fun j => secFun (b j)) (wgt m n) c)
    (c : Fin r → ℂ) :
    (star c ⬝ᵥ (((traceMat D (n + k) g).map (Int.cast : ℤ → ℂ))ᴴ * monoDiag D (n + k) (projDeg x e) *
      (traceMat D (n + k) g).map (Int.cast : ℤ → ℂ)) *ᵥ c).re ≤
      (projDeg x e : ℝ) ^ 3 * Cε ^ 2 * B * bNormSq μ (fun j => secFun (b j)) (wgt m n) c := by
  classical
  choose F hFh hFb using hb.1
  set β := bNormSq μ (fun j => secFun (b j)) (wgt m n) c with hβ
  have hβ0 : 0 ≤ β := bNormSq_nonneg' μ m _ c
  set S := Cε * Real.sqrt (B * β) with hSdef
  have hl : ∀ l, ∫ w, ‖∑ j, c j * eval w (map (Int.castRingHom ℂ) (g j l))‖ ^ 2 ∂(sphProb (D + 1)) ≤
      ((projDeg x e : ℝ) * S) ^ 2 := by
    intro l
    have htr : ∀ j, aeval (x ∘ e) (g j l) = secTrace x e (n + k) (aeval x (F j * H l)) := fun j => by
      rw [hgv, map_mul, hFb j, aeval_map_intQ]
    have hS : ∀ z ∈ pts (coordIdeal ℤ x),
        ‖∑ j, c j * eval z (map (Int.castRingHom ℂ) (F j * H l))‖ ≤ S * pnorm e z ^ (n + k) := by
      intro z hz
      have hmz : m.ρ z = pnorm e z := hFS z hz
      have e1 : ∑ j, c j * eval z (map (Int.castRingHom ℂ) (F j * H l)) =
          (∑ j, c j * secFun (b j) z) * eval z (map (Int.castRingHom ℂ) (H l)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, map_mul, hFb j, secFun_map_intQ]; ring
      rw [e1, norm_mul, hSdef, pow_add, ← hmz]
      have h1 := norm_le_of_sq_wgt_le hz.1 (norm_nonneg _) (mul_nonneg hB hβ0) (hsup c z hz)
      have h2 := hCε l z hz
      calc ‖∑ j, c j * secFun (b j) z‖ * ‖eval z (map (Int.castRingHom ℂ) (H l))‖
          ≤ (Real.sqrt (B * β) * m.ρ z ^ n) * (Cε * m.ρ z ^ k) :=
            mul_le_mul h1 h2 (norm_nonneg _) (by have := m.nonneg z; positivity)
        _ = Cε * Real.sqrt (B * β) * (m.ρ z ^ n * m.ρ z ^ k) := by ring
    refine integral_sphProb_le _ (fun w => sq_nonneg _) fun w hw => ?_
    have ht := trace_comb_le hfr (fun j => F j * H l) (fun j => g j l)
      (fun j => (hFh j).mul (hH l)) (fun j => hgh j l) htr c hS w
    rw [hw, Real.sqrt_one, one_pow, mul_one] at ht
    exact pow_le_pow_left₀ (norm_nonneg _) ht 2
  rw [quad_conj, quad_monoDiag]
  simp_rw [sum_monoNormSq_traceMat g hgh c]
  calc ∑ l : Fin (projDeg x e), ∫ w, ‖∑ j, c j * eval w (map (Int.castRingHom ℂ) (g j l))‖ ^ 2 ∂(sphProb (D + 1))
      ≤ ∑ _l : Fin (projDeg x e), ((projDeg x e : ℝ) * S) ^ 2 := Finset.sum_le_sum fun l _ => hl l
    _ = (projDeg x e : ℝ) ^ 3 * Cε ^ 2 * B * β := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hSdef, mul_pow, mul_pow,
        Real.sq_sqrt (mul_nonneg hB hβ0)]
      ring

theorem upper {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e) (hFS : IsPullFS x e m)
    (hint : ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis x n b → ∀ i j,
      Integrable (fun z => starRingEnd ℂ (secFun (b i) z) * secFun (b j) z * (wgt m n z : ℂ)) μ)
    (hpd : ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis x n b →
      (bGram μ (fun k => secFun (b k)) (wgt m n)).PosDef)
    (hsup : ∃ K : ℝ, ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), 1 ≤ n → IsSecBasis x n b →
      ∀ (c : Fin r → ℂ), ∀ z ∈ pts (coordIdeal ℤ x),
        ‖∑ k, c k * secFun (b k) z‖ ^ 2 * wgt m n z ≤
          K * (n : ℝ) ^ D * bNormSq μ (fun k => secFun (b k)) (wgt m n) c) :
    ∃ (k : ℕ) (C : ℝ), ∀ n : ℕ, 1 ≤ n → ∀ (r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis x n b →
      -(1 / 2) * Real.log (bGram μ (fun j => secFun (b j)) (wgt m n)).det.re ≤
        (projDeg x e : ℝ) * chiP D (n + k) + C * (n : ℝ) ^ D * Real.log (n + 1) := by
  classical
  have hrat := hfr.isRatProjFrame
  obtain ⟨k, ε, hε, hli⟩ := exists_indep_sections x e hrat
  have hεH : ∀ l, ∃ Hl : MvPolynomial (Ix κ) ℤ, Hl.IsHomogeneous k ∧ aeval x Hl = ε l := fun l => by
    obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.mp (hε l)
    exact ⟨p, (mem_homogeneousSubmodule _ _).mp hp, hpe⟩
  choose H hHh hHe using hεH
  have hHe' : (fun l => aeval x (H l)) = ε := funext hHe
  have hCl : ∀ l, ∃ S : ℝ, 0 ≤ S ∧ ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (H l))‖ ≤ S * pnorm e z ^ k :=
    fun l => form_le_pnorm hfr k _ ((hHh l).map _)
  choose Cl _ hCl using hCl
  set Cε := ∑ l, |Cl l| with hCεdef
  have hCε : ∀ l, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (H l))‖ ≤ Cε * m.ρ z ^ k := fun l z hz => by
    have hmz : m.ρ z = pnorm e z := hFS z hz
    rw [hmz]
    exact (hCl l z hz).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |Cl i|) (fun i _ => abs_nonneg _) (Finset.mem_univ l)))
      (pow_nonneg (pnorm_nonneg e z) _))
  obtain ⟨K, hK⟩ := hsup
  obtain ⟨k', hk'⟩ := finrank_sec_le x e hfr
  set T : ℝ := max 1 ((projDeg x e : ℝ) ^ 3 * Cε ^ 2 * |K|) with hTdef
  have hT1 : 1 ≤ T := le_max_left _ _
  refine ⟨k, (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * ((1 / 2) * (Real.log T / Real.log 2 + D)),
    fun n hn r b hb => ?_⟩
  obtain rfl := hb.card_eq
  choose F hFh hFb using hb.1
  have hbF : ∀ j, aeval x (b j) = aeval x (F j) := fun j => by rw [hFb j, aeval_map_intQ]
  have hgex : ∀ j l, ∃ p : MvPolynomial (Fin (D + 1)) ℤ, p.IsHomogeneous (n + k) ∧
      aeval (x ∘ e) p = secTrace x e (n + k) (aeval x (b j) * aeval x (H l)) := fun j l => by
    have hmem : aeval x (b j) * aeval x (H l) ∈ sec ℤ x (n + k) := by
      rw [hbF j, ← map_mul]
      exact Submodule.mem_map.mpr ⟨F j * H l, (mem_homogeneousSubmodule _ _).mpr ((hFh j).mul (hHh l)), rfl⟩
    obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.mp (secTrace_mem x e hfr (n + k) hmem)
    exact ⟨p, (mem_homogeneousSubmodule _ _).mp hp, hpe⟩
  choose g hgh hgv using hgex
  have hinj := traceMat_injective hrat hb H hHh (by rw [hHe']; exact hli) g hgh hgv
  have hr := le_of_injective_mulVec _ hinj
  have hG' := hpd n _ b hb
  have hG := monoDiag_posDef D (n + k) (projDeg x e)
  set A := Real.sqrt (T * (n : ℝ) ^ D) with hAdef
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hTn : 1 ≤ T * (n : ℝ) ^ D := one_le_mul_of_one_le_of_one_le hT1 (one_le_pow₀ hn1)
  have hA : 0 < A := Real.sqrt_pos.mpr (by linarith)
  have hA2 : A ^ 2 = T * (n : ℝ) ^ D := Real.sq_sqrt (by linarith)
  have hnorm : (((A : ℂ) ^ 2) • bGram μ (fun j => secFun (b j)) (wgt m n) -
      ((traceMat D (n + k) g).map (Int.cast : ℤ → ℂ))ᴴ * monoDiag D (n + k) (projDeg x e) *
        (traceMat D (n + k) g).map (Int.cast : ℤ → ℂ)).PosSemidef := by
    refine psd_sub_of_quad_le (isHermitian_sq_smul hG'.isHermitian A)
      (Matrix.isHermitian_conjTranspose_mul_mul _ hG.isHermitian) fun c => ?_
    have hq := quad_upper_pull hfr hFS hb H hHh g hgh hgv hCε (mul_nonneg (abs_nonneg K)
      (pow_nonneg (Nat.cast_nonneg n) D)) (fun c z hz => (hK n _ b hn hb c z hz).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K)
          (pow_nonneg (Nat.cast_nonneg n) D)) (bNormSq_nonneg' μ m _ c))) c
    have hβ0 := bNormSq_nonneg' μ m (n := n) (fun j => secFun (b j)) c
    have hre : (star c ⬝ᵥ (((A : ℂ) ^ 2) • bGram μ (fun j => secFun (b j)) (wgt m n)) *ᵥ c).re =
        A ^ 2 * bNormSq μ (fun j => secFun (b j)) (wgt m n) c := by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
        bNormSq_eq_re μ _ _ (hint n _ b hb)]
    rw [hre, hA2]
    refine hq.trans (mul_le_mul_of_nonneg_right ?_ hβ0)
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (Nat.cast_nonneg n) D)
  have hsmall : ∀ i, ((((1 : Matrix (Fin (projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) (n + k)).card))
      (Fin (projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) (n + k)).card)) ℤ).map (Int.cast : ℤ → ℂ))ᴴ *
      monoDiag D (n + k) (projDeg x e) *
      (1 : Matrix (Fin (projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) (n + k)).card))
      (Fin (projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) (n + k)).card)) ℤ).map (Int.cast : ℤ → ℂ)) i i).re
      ≤ (1 : ℝ) ^ 2 := by
    intro i
    rw [Matrix.map_one _ Int.cast_zero Int.cast_one, Matrix.conjTranspose_one, Matrix.one_mul,
      Matrix.mul_one, monoDiag, Matrix.diagonal_apply_eq, Complex.ofReal_re, one_pow]
    exact monoNormSq_le_one _
  have key := neg_log_det_le hr hG' hG _ hinj 1 (by simp) hA one_pos hnorm hsmall
  rw [Real.log_one, mul_zero, add_zero, neg_log_det_monoDiag] at key
  obtain ⟨hL0, hL⟩ := log_sqrt_bound D hT1 hn
  have hrb : ((finrank ℤ (sec ℤ x n) : ℕ) : ℝ) ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D := by
    have h1 : ((finrank ℤ (sec ℤ x n) : ℕ) : ℝ) ≤ (projDeg x e : ℝ) * (((n + k' + D).choose D : ℕ) : ℝ) := by
      exact_mod_cast hk' n
    rw [mul_assoc]
    exact h1.trans (mul_le_mul_of_nonneg_left (choose_bound k' D hn) (Nat.cast_nonneg _))
  have hX : 0 ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D := by positivity
  have h3 : ((finrank ℤ (sec ℤ x n) : ℕ) : ℝ) * Real.log A ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D *
      ((1 / 2) * (Real.log T / Real.log 2 + D) * Real.log (n + 1)) :=
    (mul_le_mul_of_nonneg_right hrb hL0).trans (mul_le_mul_of_nonneg_left hL hX)
  have h4 : (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D *
      ((1 / 2) * (Real.log T / Real.log 2 + D) * Real.log (n + 1)) =
      (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * ((1 / 2) * (Real.log T / Real.log 2 + D)) *
        (n : ℝ) ^ D * Real.log (n + 1) := by ring
  linarith

end

end ResChiSandwich

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace ResChiSandwich

open MvPolynomial MeasureTheory Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjectionBounds
open scoped ComplexOrder Matrix

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem bNormSq_le_of_pts_of {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    [IsProbabilityMeasure μ] (hcar : μ (pts (coordIdeal ℤ x))ᶜ = 0) {n r : ℕ}
    (s : Fin r → (Ix κ → ℂ) → ℂ) (c : Fin r → ℂ) {B : ℝ}
    (h : ∀ z ∈ pts (coordIdeal ℤ x), ‖∑ j, c j * s j z‖ ^ 2 * wgt m n z ≤ B) :
    bNormSq μ s (wgt m n) c ≤ B := by
  have hae : ∀ᵐ z ∂μ, z ∈ pts (coordIdeal ℤ x) := ae_iff.mpr hcar
  unfold bNormSq
  calc ∫ z, ‖∑ j, c j * s j z‖ ^ 2 * wgt m n z ∂μ ≤ ∫ _z, B ∂μ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun z => ?_) (integrable_const B) ?_
        · exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (pow_nonneg (m.nonneg z) _))
        · filter_upwards [hae] with z hz using h z hz
    _ = B := by simp

theorem form_le_rho {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {e : Fin (D + 1) → Ix κ}
    (hfr : IsProjFrame x e) (hFS : IsPullFS x e m) (k : ℕ) (f : MvPolynomial (Ix κ) ℂ) (hf : f.IsHomogeneous k) :
    ∃ S : ℝ, ∀ z ∈ pts (coordIdeal ℤ x), ‖eval z f‖ ≤ S * m.ρ z ^ k := by
  obtain ⟨S, -, hS⟩ := form_le_pnorm hfr k f hf
  refine ⟨S, fun z hz => ?_⟩
  have hmz : m.ρ z = pnorm e z := hFS z hz
  rw [hmz]
  exact hS z hz

theorem lower {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e) (hFS : IsPullFS x e m)
    [IsProbabilityMeasure μ] (hcar : μ (pts (coordIdeal ℤ x))ᶜ = 0)
    (hint : ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis x n b → ∀ i j,
      Integrable (fun z => starRingEnd ℂ (secFun (b i) z) * secFun (b j) z * (wgt m n z : ℂ)) μ)
    (hpd : ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis x n b →
      (bGram μ (fun k => secFun (b k)) (wgt m n)).PosDef) :
    ∃ (k : ℕ) (C : ℝ), ∀ n : ℕ, k + 1 ≤ n → ∀ (r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis x n b →
      (projDeg x e : ℝ) * chiP D (n - k) - C * (n : ℝ) ^ D * Real.log (n + 1) ≤
        -(1 / 2) * Real.log (bGram μ (fun j => secFun (b j)) (wgt m n)).det.re := by
  classical
  obtain ⟨kε, ε, hε, hli⟩ := exists_indep_sections x e hfr.isRatProjFrame
  have hεH : ∀ l, ∃ Hl : MvPolynomial (Ix κ) ℤ, Hl.IsHomogeneous kε ∧ aeval x Hl = ε l := fun l => by
    obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.mp (hε l)
    exact ⟨p, (mem_homogeneousSubmodule _ _).mp hp, hpe⟩
  choose H hHh hHe using hεH
  have hliH : LinearIndependent (fnField (x ∘ e)) fun l => aeval x (H l) := by
    rw [show (fun l => aeval x (H l)) = ε from funext hHe]; exact hli
  have hCl : ∀ l, ∃ S : ℝ, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (H l))‖ ≤ S * m.ρ z ^ kε :=
    fun l => form_le_rho hfr hFS kε _ ((hHh l).map _)
  choose Cl hCl using hCl
  set Cε := ∑ l, |Cl l| with hCεdef
  have hCε0 : 0 ≤ Cε := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hCε : ∀ l, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (H l))‖ ≤ Cε * m.ρ z ^ kε := fun l z hz =>
    (hCl l z hz).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |Cl i|) (fun i _ => abs_nonneg _) (Finset.mem_univ l)))
      (pow_nonneg (m.nonneg z) _))
  obtain ⟨k₀, hk₀⟩ := exists_sec_eq_mul x e hfr
  obtain ⟨tb, htb⟩ := exists_isSecBasis x k₀
  choose Tf hTfh hTfb using htb.1
  have hCt : ∀ i, ∃ S : ℝ, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (Tf i))‖ ≤ S * m.ρ z ^ k₀ :=
    fun i => form_le_rho hfr hFS k₀ _ ((hTfh i).map _)
  choose Cti hCti using hCt
  set Ct := ∑ i, |Cti i| with hCtdef
  have hCt : ∀ i, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (Tf i))‖ ≤ Ct * m.ρ z ^ k₀ := fun i z hz =>
    (hCti i z hz).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |Cti i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)))
      (pow_nonneg (m.nonneg z) _))
  have hCt0 : 0 ≤ Ct := Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨k', hk'⟩ := finrank_sec_le x e hfr
  set T : ℝ := max 1 (Cε ^ 2 * (projDeg x e : ℝ) * ((1 + 0 + D : ℕ) : ℝ) ^ D) with hTdef
  have hT1 : 1 ≤ T := le_max_left _ _
  set lam : ℝ := max 1 Ct with hlamdef
  have hlam1 : 1 ≤ lam := le_max_left _ _
  have hloglam : 0 ≤ Real.log lam := Real.log_nonneg hlam1
  refine ⟨max kε k₀, (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D *
    ((1 / 2) * (Real.log T / Real.log 2 + D) + Real.log lam / Real.log 2), fun n hn r b hb => ?_⟩
  obtain rfl := hb.card_eq
  have hn1 : 1 ≤ n := by omega
  have hnk : n - kε + kε = n := Nat.sub_add_cancel (by omega)
  have hnk₀ : n - k₀ + k₀ = n := Nat.sub_add_cancel (by omega)
  obtain ⟨crd, hcrd1, hcrd2⟩ := exists_crd hb

  have hQh : ∀ p : Fin (projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) (n - kε)).card),
      (prodForm e (adtEnum D (n - kε) (finProdFinEquiv.symm p).2) (H (finProdFinEquiv.symm p).1)).IsHomogeneous n :=
    fun p => by
      have := prodForm_isHomogeneous e (adtEnum_sum D (n - kε) (finProdFinEquiv.symm p).2)
        (hHh (finProdFinEquiv.symm p).1)
      rwa [hnk] at this
  have hQm : ∀ p, aeval x (prodForm e (adtEnum D (n - kε) (finProdFinEquiv.symm p).2)
      (H (finProdFinEquiv.symm p).1)) ∈ sec ℤ x n := fun p =>
    Submodule.mem_map.mpr ⟨_, (mem_homogeneousSubmodule _ _).mpr (hQh p), rfl⟩
  set M : Matrix (Fin (finrank ℤ (sec ℤ x n)))
      (Fin (projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) (n - kε)).card)) ℤ :=
    Matrix.of fun j p => crd ⟨_, hQm p⟩ j with hMdef
  have hM : ∀ p, ∑ j, (M j p : Ω) * aeval x (b j) = aeval x (prodForm e
      (adtEnum D (n - kε) (finProdFinEquiv.symm p).2) (H (finProdFinEquiv.symm p).1)) :=
    fun p => hcrd1 ⟨_, hQm p⟩
  have hinj := injective_map_of_int_ker M (alphaMat_ker hfr H hliH M hM)
  have hr := le_of_injective_mulVec _ hinj
  have hG' := monoDiag_posDef D (n - kε) (projDeg x e)
  have hG := hpd n _ b hb
  set A := Real.sqrt (T * (n : ℝ) ^ D) with hAdef
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hTn : 1 ≤ T * (n : ℝ) ^ D := one_le_mul_of_one_le_of_one_le hT1 (one_le_pow₀ hn1')
  have hA : 0 < A := Real.sqrt_pos.mpr (by linarith)
  have hA2 : A ^ 2 = T * (n : ℝ) ^ D := Real.sq_sqrt (by linarith)
  have hnorm : (((A : ℂ) ^ 2) • monoDiag D (n - kε) (projDeg x e) -
      (M.map (Int.cast : ℤ → ℂ))ᴴ * bGram μ (fun j => secFun (b j)) (wgt m n) *
        M.map (Int.cast : ℤ → ℂ)).PosSemidef := by
    refine psd_sub_of_quad_le (isHermitian_sq_smul hG'.isHermitian A)
      (Matrix.isHermitian_conjTranspose_mul_mul _ hG.isHermitian) fun c => ?_
    rw [quad_conj, ← bNormSq_eq_re μ _ _ (hint n _ b hb), Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, ← Complex.ofReal_pow, Complex.re_ofReal_mul, quad_monoDiag]
    have hq0 : 0 ≤ ∑ l : Fin (projDeg x e), ∑ i, monoNormSq (adtEnum D (n - kε) i) *
        ‖c (finProdFinEquiv (l, i))‖ ^ 2 := Finset.sum_nonneg fun l _ =>
      Finset.sum_nonneg fun i _ => mul_nonneg (monoNormSq_pos _).le (sq_nonneg _)
    refine bNormSq_le_of_pts_of hcar _ _ fun z hz => ?_
    rw [sum_mulVec_secFun hb M _ hQh hM c z hz]
    have h1 := pt_lower hFS H hCε0 hCε c hz
    rw [hnk] at h1
    refine h1.trans ?_
    have hswap : ∑ l : Fin (projDeg x e), ∑ i, ‖c (finProdFinEquiv (l, i))‖ ^ 2 *
        monoNormSq (adtEnum D (n - kε) i) = ∑ l : Fin (projDeg x e), ∑ i,
        monoNormSq (adtEnum D (n - kε) i) * ‖c (finProdFinEquiv (l, i))‖ ^ 2 :=
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hswap, hA2]
    refine mul_le_mul_of_nonneg_right ?_ hq0
    have hB1 : (((n - kε + D).choose D : ℕ) : ℝ) ≤ (((n + 0 + D).choose D : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_le_choose D (by omega)
    have hB2 := choose_bound 0 D hn1
    calc Cε ^ 2 * (projDeg x e : ℝ) * (((n - kε + D).choose D : ℕ) : ℝ)
        ≤ Cε ^ 2 * (projDeg x e : ℝ) * (((1 + 0 + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D) :=
          mul_le_mul_of_nonneg_left (hB1.trans hB2) (by positivity)
      _ = (Cε ^ 2 * (projDeg x e : ℝ) * ((1 + 0 + D : ℕ) : ℝ) ^ D) * (n : ℝ) ^ D := by ring
      _ ≤ T * (n : ℝ) ^ D := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

  have hQ'h : ∀ s : Fin (Finset.Nat.antidiagonalTuple (D + 1) (n - k₀)).card × Fin (finrank ℤ (sec ℤ x k₀)),
      (prodForm e (adtEnum D (n - k₀) s.1) (Tf s.2)).IsHomogeneous n := fun s => by
    have := prodForm_isHomogeneous e (adtEnum_sum D (n - k₀) s.1) (hTfh s.2)
    rwa [hnk₀] at this
  have hwm : ∀ s : Fin (Finset.Nat.antidiagonalTuple (D + 1) (n - k₀)).card × Fin (finrank ℤ (sec ℤ x k₀)),
      aeval x (prodForm e (adtEnum D (n - k₀) s.1) (Tf s.2)) ∈ sec ℤ x n := fun s =>
    Submodule.mem_map.mpr ⟨_, (mem_homogeneousSubmodule _ _).mpr (hQ'h s), rfl⟩
  have hspan := crd_span hcrd2 hb _ hwm (sec_le_span_prod (hk₀ n (by omega)) htb Tf hTfb)
  obtain ⟨f, hfdet⟩ := exists_cols_det_ne_zero _ hspan
  set Nm : Matrix (Fin (finrank ℤ (sec ℤ x n))) (Fin (finrank ℤ (sec ℤ x n))) ℤ :=
    Matrix.of fun p q => crd ⟨_, hwm (f q)⟩ p with hNm
  have hsmall : ∀ i, (((Nm.map (Int.cast : ℤ → ℂ))ᴴ * bGram μ (fun j => secFun (b j)) (wgt m n) *
      Nm.map (Int.cast : ℤ → ℂ)) i i).re ≤ lam ^ 2 := by
    intro i
    rw [diag_conj_eq, ← bNormSq_eq_re μ _ _ (hint n _ b hb)]
    refine bNormSq_le_of_pts_of hcar _ _ fun z hz => ?_
    have hv : Nm.map (Int.cast : ℤ → ℂ) *ᵥ Pi.single i 1 =
        fun p => ((crd ⟨_, hwm (f i)⟩ p : ℤ) : ℂ) := by
      funext p
      simp [hNm, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hv, sum_secFun_eq' hb _ (hQ'h (f i)) _ (hcrd1 ⟨_, hwm (f i)⟩) z hz]
    have h1 := pt_small hFS (adtEnum_sum D (n - k₀) (f i).1) (Tf (f i).2) (hCt (f i).2) hz
    rw [hnk₀] at h1
    exact h1.trans (pow_le_pow_left₀ hCt0 (le_max_right _ _) 2)
  have key := neg_log_det_le hr hG' hG M hinj _ hfdet hA (by linarith) hnorm hsmall
  rw [neg_log_det_monoDiag] at key

  have hmono : Monotone (chiP D) := monotone_nat_of_le_succ fun n => by
    have := chiP_succ_sub_nonneg D n; linarith
  have hm := mul_le_mul_of_nonneg_left (hmono (show n - max kε k₀ ≤ n - kε by omega))
    (Nat.cast_nonneg (projDeg x e) : (0 : ℝ) ≤ projDeg x e)
  obtain ⟨hL0, hL⟩ := log_sqrt_bound D hT1 hn1
  have hll := log_le_div_mul hloglam hn1
  set R' := projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) (n - kε)).card
  set r := finrank ℤ (sec ℤ x n)
  have hrR : (R' : ℝ) ≤ r := by exact_mod_cast hr
  have hR0 : (0 : ℝ) ≤ R' := Nat.cast_nonneg _
  have hrb : (r : ℝ) ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D := by
    have h1 : (r : ℝ) ≤ (projDeg x e : ℝ) * (((n + k' + D).choose D : ℕ) : ℝ) := by
      exact_mod_cast hk' n
    rw [mul_assoc]
    exact h1.trans (mul_le_mul_of_nonneg_left (choose_bound k' D hn1) (Nat.cast_nonneg _))
  have hX : 0 ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D := by positivity
  have hlogn : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have h3 : (R' : ℝ) * Real.log A ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D *
      ((1 / 2) * (Real.log T / Real.log 2 + D) * Real.log (n + 1)) :=
    (mul_le_mul_of_nonneg_right (hrR.trans hrb) hL0).trans (mul_le_mul_of_nonneg_left hL hX)
  have h4 : ((r : ℝ) - R') * Real.log lam ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D *
      (n : ℝ) ^ D * (Real.log lam / Real.log 2 * Real.log (n + 1)) :=
    (mul_le_mul_of_nonneg_right (by linarith) hloglam).trans (mul_le_mul_of_nonneg_left hll hX)
  have h5 : (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D *
      ((1 / 2) * (Real.log T / Real.log 2 + D) + Real.log lam / Real.log 2) * (n : ℝ) ^ D *
        Real.log (n + 1) = (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D *
      ((1 / 2) * (Real.log T / Real.log 2 + D) * Real.log (n + 1)) +
      (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D *
      (Real.log lam / Real.log 2 * Real.log (n + 1)) := by ring
  linarith

end

end ResChiSandwich

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
open scoped ComplexOrder

noncomputable section

theorem ResChiBounds.proof (hR : ResolutionSupBound.Statement) : ResChiBounds.Statement := by
  intro D Ω _ _ κ _ d e hfr hFS
  have hint : ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n b → ∀ i j,
      Integrable (fun z => starRingEnd ℂ (secFun (b i) z) * secFun (b j) z * (wgt d.m n z : ℂ))
        (ResSym.symMeasure d) := fun n r b hb => ResSym.integrable_gram d hb.1
  have hpd : ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n b →
      (bGram (ResSym.symMeasure d) (fun k => secFun (b k)) (wgt d.m n)).PosDef :=
    fun n r b hb => ResSym.posDef_gram d hb
  obtain ⟨k₁, C₁, h₁⟩ := ResChiSandwich.upper hfr hFS hint hpd (ResSym.sup_le_gram hR d)
  obtain ⟨k₂, C₂, h₂⟩ := ResChiSandwich.lower hfr hFS (ResSym.symMeasure_compl_pts d) hint hpd
  have hmono : Monotone (chiP D) := monotone_nat_of_le_succ fun n => by
    have := chiP_succ_sub_nonneg D n; linarith
  have hδ : (0 : ℝ) ≤ (projDeg d.x e : ℝ) := Nat.cast_nonneg _
  refine ⟨max k₁ k₂, max C₁ C₂, fun n hn => ?_⟩
  obtain ⟨b₀, hb₀⟩ := exists_isSecBasis d.x n
  have h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n p.2 := ⟨⟨_, b₀⟩, hb₀⟩
  rw [ResSym.resChi_eq d n h]
  have hX : 0 ≤ (n : ℝ) ^ D * Real.log (n + 1) :=
    mul_nonneg (by positivity) (Real.log_nonneg (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith))
  have hu := h₁ n (by omega) _ _ h.choose_spec
  have hl := h₂ n (by omega) _ _ h.choose_spec
  constructor
  · have hm : chiP D (n - max k₁ k₂) ≤ chiP D (n - k₂) := hmono (by omega)
    have hm' := mul_le_mul_of_nonneg_left hm hδ
    have hc : C₂ * (n : ℝ) ^ D * Real.log (n + 1) ≤ max C₁ C₂ * (n : ℝ) ^ D * Real.log (n + 1) := by
      rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hX
    linarith
  · have hm : chiP D (n + k₁) ≤ chiP D (n + max k₁ k₂) := hmono (by omega)
    have hm' := mul_le_mul_of_nonneg_left hm hδ
    have hc : C₁ * (n : ℝ) ^ D * Real.log (n + 1) ≤ max C₁ C₂ * (n : ℝ) ^ D * Real.log (n + 1) := by
      rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX
    linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
