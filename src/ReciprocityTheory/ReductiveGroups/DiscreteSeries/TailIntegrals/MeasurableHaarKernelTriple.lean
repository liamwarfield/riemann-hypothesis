module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.NormFixedUnitaryEntryLeOne

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.SphericalFunctionFixedUnitaryEqOne
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k : ℕ}

def sg (k : ℕ) (i : Fin (2 * 0 + k + 1)) : ℂ := if i = iK k then -1 else 1

lemma hpk_diag (k : ℕ) : Hpk k 0 = Matrix.diagonal (sg k) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, Matrix.diagonal_apply, sg, iK, wI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega | simp_all

lemma hpk_mulVec (v : Fin (2 * 0 + k + 1) → ℂ) (i : Fin (2 * 0 + k + 1)) :
    (Hpk k 0 *ᵥ v) i = sg k i * v i := by
  rw [hpk_diag, Matrix.mulVec_diagonal]

lemma hpk_sq (k : ℕ) : Hpk k 0 * Hpk k 0 = 1 := by
  rw [hpk_diag, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases h : i = iK k <;> simp [sg, h]

lemma herm0 (v w : Fin (2 * 0 + k + 1) → ℂ) :
    herm (Hpk k 0) v w = ∑ i, star (w i) * (sg k i * v i) := by
  simp only [herm, dotProduct, Pi.star_apply, hpk_mulVec]

lemma herm_re (y : Fin (2 * 0 + k + 1) → ℂ) :
    (herm (Hpk k 0) y y).re = tW (iK k) y ^ 2 - Complex.normSq (y (iK k)) := by
  have hterm : ∀ i, (star (y i) * (sg k i * y i)).re =
      Complex.normSq (y i) - (if i = iK k then 2 * Complex.normSq (y i) else 0) := by
    intro i
    by_cases h : i = iK k
    · simp [sg, h, Complex.normSq_apply, Complex.mul_re]
      ring
    · simp [sg, h, Complex.normSq_apply, Complex.mul_re]
  rw [herm0, tW_sq, Complex.re_sum, Finset.sum_congr rfl fun i _ => hterm i,
    Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

lemma phi'_eq (hk : 1 ≤ k) :
    phiV' k 0 0 = ((Real.sqrt 2)⁻¹ : ℂ) • (bvec (iW k) - bvec (iK k)) := by
  have hWK := iW_ne_iK hk
  funext i
  rw [phiV', hpk_mulVec]
  show sg k i * (((Real.sqrt 2)⁻¹ : ℂ) • (bvec (iW k) + bvec (iK k))) i = (((Real.sqrt 2)⁻¹ : ℂ) • (bvec (iW k) - bvec (iK k))) i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, bvec]
  rcases eq_or_ne i (iW k) with rfl | h1
  · simp [sg, hWK]
  · rcases eq_or_ne i (iK k) with rfl | h2
    · simp [sg, hWK.symm]
    · simp [h1, h2]

lemma phi'_iW (hk : 1 ≤ k) : phiV' k 0 0 (iW k) = ((Real.sqrt 2)⁻¹ : ℂ) := by
  rw [phi'_eq hk]
  simp [bvec, iW_ne_iK hk]

lemma phi'_iK (hk : 1 ≤ k) : phiV' k 0 0 (iK k) = -((Real.sqrt 2)⁻¹ : ℂ) := by
  rw [phi'_eq hk]
  simp [bvec, (iW_ne_iK hk).symm]

lemma phi'_zero (hk : 1 ≤ k) (i : Fin (2 * 0 + k + 1)) (h1 : i ≠ iW k) (h2 : i ≠ iK k) :
    phiV' k 0 0 i = 0 := by
  rw [phi'_eq hk]
  simp [bvec, h1, h2]

lemma normSq_c : Complex.normSq ((Real.sqrt 2)⁻¹ : ℂ) = 1 / 2 := by
  rw [map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma star_c : star ((Real.sqrt 2)⁻¹ : ℂ) = ((Real.sqrt 2)⁻¹ : ℂ) := by
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]

lemma norm_c : ‖((Real.sqrt 2)⁻¹ : ℂ)‖ = (Real.sqrt 2)⁻¹ := by
  rw [norm_inv, Complex.norm_of_nonneg (Real.sqrt_nonneg 2)]

lemma phi'_dot (hk : 1 ≤ k) : star (phiV' k 0 0) ⬝ᵥ phiV' k 0 0 = 1 := by
  have hWK := iW_ne_iK hk
  have hφ : ∀ i, Complex.normSq (phiV' k 0 0 i) =
      (if i = iW k then 1 / 2 else 0) + (if i = iK k then 1 / 2 else 0) := by
    intro i
    rcases eq_or_ne i (iW k) with rfl | h1
    · rw [phi'_iW hk, normSq_c, if_pos rfl, if_neg hWK, add_zero]
    · rcases eq_or_ne i (iK k) with rfl | h2
      · rw [phi'_iK hk, Complex.normSq_neg, normSq_c, if_neg h1, if_pos rfl, zero_add]
      · rw [phi'_zero hk i h1 h2, map_zero, if_neg h1, if_neg h2, add_zero]
  rw [dot_star_self, Finset.sum_congr rfl fun i _ => hφ i, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  norm_num

private lemma sum_phi_lemma (hk : 1 ≤ k) (X : Fin (2 * 0 + k + 1) → ℂ) :
    ∑ i, star (phiV' k 0 0 i) * (sg k i * X i) = ((Real.sqrt 2)⁻¹ : ℂ) * (X (iW k) + X (iK k)) := by
  have hWK := iW_ne_iK hk
  have h : ∀ i, star (phiV' k 0 0 i) * (sg k i * X i) =
      (if i = iW k then ((Real.sqrt 2)⁻¹ : ℂ) * X (iW k) else 0) + (if i = iK k then ((Real.sqrt 2)⁻¹ : ℂ) * X (iK k) else 0) := by
    intro i
    rcases eq_or_ne i (iW k) with rfl | h1
    · rw [phi'_iW hk, star_c, if_pos rfl, if_neg hWK, add_zero]
      simp [sg, hWK]
    · rcases eq_or_ne i (iK k) with rfl | h2
      · rw [phi'_iK hk, star_neg, star_c, if_neg h1, if_pos rfl, zero_add]
        simp [sg]
      · rw [phi'_zero hk i h1 h2, star_zero, zero_mul, if_neg h1, if_neg h2, add_zero]
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

lemma phi'_iso (hk : 1 ≤ k) : herm (Hpk k 0) (phiV' k 0 0) (phiV' k 0 0) = 0 := by
  rw [herm0, sum_phi_lemma hk, phi'_iW hk, phi'_iK hk]
  ring

private lemma dl0_lemma_2 (M : Mat k 0) :
    Dl k 0 0 M = herm (Hpk k 0) (M *ᵥ phiV' k 0 0) (phiV' k 0 0) := by
  unfold Dl
  exact Matrix.det_fin_one _

lemma dl_eq (hk : 1 ≤ k) (M : Mat k 0) :
    Dl k 0 0 M = ((Real.sqrt 2)⁻¹ : ℂ) * ((M *ᵥ phiV' k 0 0) (iW k) + (M *ᵥ phiV' k 0 0) (iK k)) := by
  rw [dl0_lemma_2, herm0, sum_phi_lemma hk]

lemma G_left {g : Mat k 0} (hg : g ∈ GV k 0) : (Hpk k 0 * gᴴ * Hpk k 0) * g = 1 := by
  have hg' : gᴴ * Hpk k 0 * g = Hpk k 0 := hg
  calc Hpk k 0 * gᴴ * Hpk k 0 * g = Hpk k 0 * (gᴴ * Hpk k 0 * g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hpk_sq]

lemma G_star {g : Mat k 0} (hg : g ∈ GV k 0) : g * Hpk k 0 * gᴴ = Hpk k 0 := by
  have h1 : g * (Hpk k 0 * gᴴ * Hpk k 0) = 1 := mul_eq_one_comm.mp (G_left hg)
  calc g * Hpk k 0 * gᴴ = g * (Hpk k 0 * gᴴ * Hpk k 0) * Hpk k 0 := by
        simp only [Matrix.mul_assoc, hpk_sq, Matrix.mul_one]
    _ = Hpk k 0 := by rw [h1, Matrix.one_mul]

lemma G_det {g : Mat k 0} (hg : g ∈ GV k 0) : g.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (G_left hg)
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at this
  exact zero_ne_one this

lemma herm_G {g : Mat k 0} (hg : g ∈ GV k 0) (v w : Fin (2 * 0 + k + 1) → ℂ) :
    herm (Hpk k 0) (g *ᵥ v) (g *ᵥ w) = herm (Hpk k 0) v w := by
  have hg' : gᴴ * Hpk k 0 * g = Hpk k 0 := hg
  simp only [herm]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec]
  rw [← Matrix.mul_assoc, hg']

private lemma ga0_lemma_3 (Y : Fin (0 + 1) → Fin (2 * 0 + k + 1) → ℂ) :
    Ga k 0 0 Y = (star (Y 0) ⬝ᵥ Y 0).re := by
  unfold Ga
  exact congrArg Complex.re (Matrix.det_fin_one _)

lemma sphericalFunction_fixedUnitary_eq_one (hk : 1 ≤ k) {h : Mat k 0} (hh : h ∈ U0 k) (s : Fin (0 + 1) → ℝ) : fsR k 0 s h = 1 := by
  rw [fsR, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ga0_lemma_3]
  rw [fixedUnitary_preserves_normSq hh, phi'_dot hk, Complex.one_re, Real.one_rpow]

lemma fsE_avg (hk : 1 ≤ k) {h : Mat k 0} (hh : h ∈ U0 k) (g h' : Mat k 0) (s : Fin (0 + 1) → ℝ) :
    FsE k 0 s (h⁻¹ * g * h') = ENNReal.ofReal ((Real.sqrt 2)⁻¹ *
      ‖(hᴴ *ᵥ ((g * h') *ᵥ phiV' k 0 0)) (iW k) + ((g * h') *ᵥ phiV' k 0 0) (iK k)‖) ^ (-s 0) := by
  have hinv : h⁻¹ = hᴴ := Matrix.inv_eq_left_inv (fixedUnitary_projection_identities hh).1
  rw [FsE, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, enn_nnnorm, dl_eq hk, norm_mul, norm_c,
    hinv, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, fixedUnitary_mulVec_fixedIndex (fixedUnitary_conjTranspose_mem hh)]

lemma outer_eq (hk : 1 ≤ k) {h' : Mat k 0} (hh : h' ∈ U0 k) (g : Mat k 0) :
    ‖((g * h') *ᵥ phiV' k 0 0) (iK k)‖ = (Real.sqrt 2)⁻¹ *
      ‖(h'ᴴ *ᵥ (fun j => star (g (iK k) j))) (iW k) + -star (g (iK k) (iK k))‖ := by
  have hM : ∀ M : Mat k 0, (M *ᵥ phiV' k 0 0) (iK k) =
      ((Real.sqrt 2)⁻¹ : ℂ) * (M (iK k) (iW k) - M (iK k) (iK k)) := by
    intro M
    rw [phi'_eq hk, Matrix.mulVec_smul, Matrix.mulVec_sub]
    simp [bvec, Matrix.mulVec_single]
  rw [hM, norm_mul, norm_c]
  congr 1
  have h1 : (g * h') (iK k) (iK k) = g (iK k) (iK k) := by
    rw [Matrix.mul_apply]
    simp [fixedUnitary_apply_fixedIndex_right hh]
  have h2 : (h'ᴴ *ᵥ fun j => star (g (iK k) j)) (iW k) = star ((g * h') (iK k) (iW k)) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, star_sum,
      star_mul]
  rw [h1, h2, ← star_neg, ← star_add, norm_star, sub_eq_add_neg]

lemma outer_ws {g : Mat k 0} (hg : g ∈ GV k 0) :
    tW (iK k) (fun j => star (g (iK k) j)) ^ 2 + 1 = Complex.normSq (g (iK k) (iK k)) := by
  have e : (g * Hpk k 0 * gᴴ) (iK k) (iK k) = Hpk k 0 (iK k) (iK k) := by rw [G_star hg]
  rw [hpk_diag, Matrix.diagonal_apply_eq, Matrix.mul_apply] at e
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply] at e
  have hsK : sg k (iK k) = -1 := by simp [sg]
  have e2 : herm (Hpk k 0) (fun j => star (g (iK k) j)) (fun j => star (g (iK k) j)) = -1 := by
    rw [herm0, ← hsK, ← e]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [star_star]
    ring
  have hre := herm_re (k := k) (fun j => star (g (iK k) j))
  rw [e2] at hre
  have hn : Complex.normSq (star (g (iK k) (iK k))) = Complex.normSq (g (iK k) (iK k)) :=
    Complex.normSq_conj _
  simp only [Complex.neg_re, Complex.one_re] at hre
  rw [hn] at hre
  linarith

lemma iso_y (hk : 1 ≤ k) {g h' : Mat k 0} (hg : g ∈ GV k 0) (hh : h' ∈ GV k 0) :
    tW (iK k) ((g * h') *ᵥ phiV' k 0 0) ^ 2 = Complex.normSq (((g * h') *ᵥ phiV' k 0 0) (iK k)) ∧
    ((g * h') *ᵥ phiV' k 0 0) (iK k) ≠ 0 := by
  have hgh : g * h' ∈ GV k 0 := by
    show (g * h')ᴴ * Hpk k 0 * (g * h') = Hpk k 0
    have hg' : gᴴ * Hpk k 0 * g = Hpk k 0 := hg
    have hh' : h'ᴴ * Hpk k 0 * h' = Hpk k 0 := hh
    rw [Matrix.conjTranspose_mul]
    calc h'ᴴ * gᴴ * Hpk k 0 * (g * h') = h'ᴴ * (gᴴ * Hpk k 0 * g) * h' := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k 0 := by rw [hg', hh']
  have hiso : herm (Hpk k 0) ((g * h') *ᵥ phiV' k 0 0) ((g * h') *ᵥ phiV' k 0 0) = 0 := by
    rw [herm_G hgh, phi'_iso hk]
  have hre := herm_re ((g * h') *ᵥ phiV' k 0 0)
  rw [hiso, Complex.zero_re] at hre
  refine ⟨by linarith, fun h0 => ?_⟩
  have hsum := tW_sq (iK k) ((g * h') *ᵥ phiV' k 0 0)
  rw [h0, map_zero, sub_zero] at hsum
  rw [h0, map_zero] at hre
  have hz : ∑ i, Complex.normSq (((g * h') *ᵥ phiV' k 0 0) i) = 0 := by
    rw [← hsum]
    linarith
  have hall : ∀ i, ((g * h') *ᵥ phiV' k 0 0) i = 0 := fun i =>
    Complex.normSq_eq_zero.mp
      ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg _)).mp hz i
        (Finset.mem_univ i))
  have hdet : (g * h').det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero (G_det hg) (G_det hh)
  have hphi := Matrix.eq_zero_of_mulVec_eq_zero hdet (funext hall)
  have hW := congrFun hphi (iW k)
  rw [phi'_iW hk, Pi.zero_apply] at hW
  exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))) hW

end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
end
end

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Base0

private def PhiA (k : ℕ) (A : ℝ) (g : Mt k 0) : ℝ≥0∞ := ENNReal.ofReal (gN (Matrix.of g) ^ (-A))

private lemma phiA_ne_top (k : ℕ) (A : ℝ) (g : Mt k 0) : PhiA k A g ≠ ∞ := ENNReal.ofReal_ne_top

private lemma measurable_phiA (k : ℕ) (A : ℝ) : Measurable (PhiA k A) := by
  have hc : Continuous fun g : Mt k 0 => gN (Matrix.of g) := by
    unfold gN
    apply Continuous.sqrt
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))
  unfold PhiA
  exact ENNReal.measurable_ofReal.comp (hc.measurable.pow_const (-A))

private def Gf (k : ℕ) (σ : ℝ) (h g h' : Mt k 0) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.sqrt 2)⁻¹ * ‖((Matrix.of h)ᴴ *ᵥ ((Matrix.of g * Matrix.of h') *ᵥ phiV' k 0 0)) (iW k) +
    ((Matrix.of g * Matrix.of h') *ᵥ phiV' k 0 0) (iK k)‖) ^ (-σ)


set_option maxHeartbeats 800000 in
private lemma measurable_Gf (k : ℕ) (σ : ℝ) :
    Measurable (fun p : Mt k 0 × Mt k 0 × Mt k 0 => Gf k σ p.1 p.2.1 p.2.2) := by
  have hof : Continuous (fun M : Mt k 0 => (Matrix.of M : Mat k 0)) := continuous_id
  have h1 : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 => Matrix.of p.1 := hof.comp continuous_fst
  have h21 : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 => Matrix.of p.2.1 :=
    hof.comp (continuous_fst.comp continuous_snd)
  have h22 : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 => Matrix.of p.2.2 :=
    hof.comp (continuous_snd.comp continuous_snd)
  have hw : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 =>
      (Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0 :=
    (h21.matrix_mul h22).matrix_mulVec continuous_const
  have hv : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 =>
      (Matrix.of p.1)ᴴ *ᵥ ((Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0) :=
    h1.matrix_conjTranspose.matrix_mulVec hw
  have hc : Continuous fun p : Mt k 0 × Mt k 0 × Mt k 0 =>
      (Real.sqrt 2)⁻¹ * ‖((Matrix.of p.1)ᴴ *ᵥ ((Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0)) (iW k) +
        ((Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0) (iK k)‖ :=
    continuous_const.mul ((((continuous_apply (iW k)).comp hv).add ((continuous_apply (iK k)).comp hw)).norm)
  have hm : Measurable (fun p : Mt k 0 × Mt k 0 × Mt k 0 => ENNReal.ofReal
      ((Real.sqrt 2)⁻¹ * ‖((Matrix.of p.1)ᴴ *ᵥ ((Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0)) (iW k) +
        ((Matrix.of p.2.1 * Matrix.of p.2.2) *ᵥ phiV' k 0 0) (iK k)‖) ^ (-σ)) :=
    (ENNReal.measurable_ofReal.comp hc.measurable).pow_const (-σ)
  unfold Gf
  exact hm

private lemma s_facts {k : ℕ} (hk : 1 ≤ k) {s : Fin (0 + 1) → ℝ} (hs : SAdm k 0 s) :
    0 ≤ s 0 ∧ s 0 < k := by
  have h := hs 0
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  simp [s0] at h
  obtain ⟨h1, h2⟩ := h
  constructor <;> linarith

private lemma nsq_tr_lemma {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) :
    ((∑ i, ∑ j, Complex.normSq (Y i j) : ℝ) : ℂ) = (Yᴴ * Y).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

private lemma gN_left_lemma_2 {k r : ℕ} {κ : Mat k r} (hκ : κᴴ * κ = 1) (X : Mat k r) : gN (κ * X) = gN X := by
  unfold gN
  congr 1
  apply Complex.ofReal_injective
  rw [nsq_tr_lemma, nsq_tr_lemma, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc κᴴ, hκ, Matrix.one_mul]

private lemma gN_right_lemma_3 {k r : ℕ} {κ : Mat k r} (hκ : κᴴ * κ = 1) (X : Mat k r) : gN (X * κ) = gN X := by
  have hκ' : κ * κᴴ = 1 := by
    first
      | exact mul_eq_one_comm.mp hκ
      | exact (Matrix.mul_eq_one_comm).1 hκ
      | exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) hκ
  unfold gN
  congr 1
  apply Complex.ofReal_injective
  rw [nsq_tr_lemma, nsq_tr_lemma, Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm,
    Matrix.mul_assoc, Matrix.mul_assoc, hκ', Matrix.mul_one]

private lemma phiA_inv (k : ℕ) (A : ℝ) : ∀ κ ∈ Kset k 0, ∀ g,
    PhiA k A (lmulM κ g) = PhiA k A g ∧ PhiA k A (rmulF κ g) = PhiA k A g := by
  intro κ hκ g
  have hu : κᴴ * κ = 1 := by
    simp only [Kset, Set.mem_setOf_eq] at hκ
    exact hκ.2
  refine ⟨?_, ?_⟩
  · simp only [PhiA, lmulM]
    exact congrArg (fun t => ENNReal.ofReal (t ^ (-A))) (gN_left_lemma_2 hu (Matrix.of g))
  · simp only [PhiA, rmulF]
    exact congrArg (fun t => ENNReal.ofReal (t ^ (-A))) (gN_right_lemma_3 hu (Matrix.of g))

private lemma avg_one {k : ℕ} (hk : 1 ≤ k) (hT : TBoth) {s : Fin (0 + 1) → ℝ} {μG : Measure (Mt k 0)}
    (hμG : IsHaarOn (GV k 0) μG) (A : ℝ) {h h' : Mat k 0} (hh : h ∈ U0 k) (hh' : h' ∈ U0 k) :
    ∫⁻ g, PhiA k A g * FsE k 0 s (h⁻¹ * Matrix.of g * h') ∂μG = JInt μG A s := by
  rw [hT k 0 s μG (PhiA k A) hk hμG (measurable_phiA k A) (phiA_inv k A) h hh.1 h' hh'.1, sphericalFunction_fixedUnitary_eq_one hk hh,
    sphericalFunction_fixedUnitary_eq_one hk hh', mul_one, ENNReal.ofReal_one, one_mul]
  rfl

private lemma measurable_haarKernelTriple (k : ℕ) (A σ : ℝ) :
    Measurable (fun q : (Mt k 0 × Mt k 0) × Mt k 0 => PhiA k A q.1.2 * Gf k σ q.2 q.1.2 q.1.1) := by
  have hs : Measurable fun q : (Mt k 0 × Mt k 0) × Mt k 0 => q.1.2 := measurable_snd.comp measurable_fst
  have h1 := (measurable_phiA k A).comp hs
  have hm : Measurable fun q : (Mt k 0 × Mt k 0) × Mt k 0 => (q.2, q.1.2, q.1.1) := by fun_prop
  have h2 := (measurable_Gf k σ).comp hm
  simp only [Function.comp_def] at h1 h2
  exact h1.mul h2

private lemma avg_key {k : ℕ} (hk : 1 ≤ k) (hT : TBoth) {s : Fin (0 + 1) → ℝ} {μG : Measure (Mt k 0)}
    (hμG : IsHaarOn (GV k 0) μG) (A : ℝ) {ν : Measure (Mt k 0)} (hν : IsHaarOn (U0 k) ν)
    [IsFiniteMeasure ν] [SigmaFinite μG] :
    JInt μG A s * (ν Set.univ * ν Set.univ) =
      ∫⁻ g, PhiA k A g * ∫⁻ h', ∫⁻ h, Gf k (s 0) h g h' ∂ν ∂ν ∂μG := by
  have step1 : JInt μG A s * (ν Set.univ * ν Set.univ) = ∫⁻ h', ∫⁻ h, JInt μG A s ∂ν ∂ν := by
    rw [lintegral_const, lintegral_const, mul_assoc]
  have step2 : ∫⁻ h', ∫⁻ h, JInt μG A s ∂ν ∂ν =
      ∫⁻ h', ∫⁻ h, ∫⁻ g, PhiA k A g * Gf k (s 0) h g h' ∂μG ∂ν ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_mem_fixedUnitary hν] with h' hh'
    refine lintegral_congr_ae ?_
    filter_upwards [ae_mem_fixedUnitary hν] with h hh
    rw [← avg_one hk hT hμG A hh hh']
    refine lintegral_congr (fun g => ?_)
    rw [fsE_avg hk hh]
    rfl
  have step3 : ∫⁻ h', ∫⁻ h, ∫⁻ g, PhiA k A g * Gf k (s 0) h g h' ∂μG ∂ν ∂ν =
      ∫⁻ h', ∫⁻ g, ∫⁻ h, PhiA k A g * Gf k (s 0) h g h' ∂ν ∂μG ∂ν := by
    refine lintegral_congr (fun h' => ?_)
    have hmap : Measurable (fun p : Mt k 0 × Mt k 0 => ((h', p.2), p.1)) :=
      (measurable_const.prodMk measurable_snd).prodMk measurable_fst
    have hm : Measurable ((fun q : (Mt k 0 × Mt k 0) × Mt k 0 => PhiA k A q.1.2 * Gf k (s 0) q.2 q.1.2 q.1.1) ∘
        (fun p : Mt k 0 × Mt k 0 => ((h', p.2), p.1))) := Measurable.comp (measurable_haarKernelTriple k A (s 0)) hmap
    exact lintegral_lintegral_swap hm.aemeasurable
  have step4 : ∫⁻ h', ∫⁻ g, ∫⁻ h, PhiA k A g * Gf k (s 0) h g h' ∂ν ∂μG ∂ν =
      ∫⁻ g, ∫⁻ h', ∫⁻ h, PhiA k A g * Gf k (s 0) h g h' ∂ν ∂ν ∂μG :=
    lintegral_lintegral_swap (Measurable.lintegral_prod_right' (measurable_haarKernelTriple k A (s 0))).aemeasurable
  have step5 : ∫⁻ g, ∫⁻ h', ∫⁻ h, PhiA k A g * Gf k (s 0) h g h' ∂ν ∂ν ∂μG =
      ∫⁻ g, PhiA k A g * ∫⁻ h', ∫⁻ h, Gf k (s 0) h g h' ∂ν ∂ν ∂μG := by
    refine lintegral_congr (fun g => ?_)
    rw [← lintegral_const_mul' _ _ (phiA_ne_top k A g)]
    refine lintegral_congr (fun h' => ?_)
    rw [lintegral_const_mul' _ _ (phiA_ne_top k A g)]
  rw [step1, step2, step3, step4, step5]

private lemma ptw {k : ℕ} (hk : 1 ≤ k) {σ : ℝ} (hσ : 0 ≤ σ) {ν : Measure (Mt k 0)}
    (hν : IsHaarOn (U0 k) ν) (hK1f : C0 k σ ν + ν Set.univ ≠ ∞) (g : Mt k 0)
    (hg : (Matrix.of g : Mat k 0) ∈ GV k 0) :
    ∫⁻ h', ∫⁻ h, Gf k σ h g h' ∂ν ∂ν ≤
      (C0 k σ ν + ν Set.univ) * (ENNReal.ofReal (1 / 8) ^ (-σ) * (C0 k σ ν + ν Set.univ)) := by
  have hc2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 : ℝ) / 2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have hws := outer_ws hg
  have hgkk : 1 ≤ ‖(Matrix.of g : Mat k 0) (iK k) (iK k)‖ := by
    have h1 : 1 ≤ Complex.normSq ((Matrix.of g : Mat k 0) (iK k) (iK k)) := by
      nlinarith [sq_nonneg (tW (iK k) (fun j => star ((Matrix.of g : Mat k 0) (iK k) j)))]
    rw [← Complex.sq_norm] at h1
    nlinarith [norm_nonneg ((Matrix.of g : Mat k 0) (iK k) (iK k))]
  have hbn : ‖-star ((Matrix.of g : Mat k 0) (iK k) (iK k))‖ = ‖(Matrix.of g : Mat k 0) (iK k) (iK k)‖ := by
    rw [norm_neg, norm_star]
  have hb0 : -star ((Matrix.of g : Mat k 0) (iK k) (iK k)) ≠ 0 := by
    intro h; rw [h, norm_zero] at hbn; linarith
  have hvb : tW (iK k) (fun j => star ((Matrix.of g : Mat k 0) (iK k) j)) ^ 2 ≤
      Complex.normSq (-star ((Matrix.of g : Mat k 0) (iK k) (iK k))) := by
    have : Complex.normSq (star ((Matrix.of g : Mat k 0) (iK k) (iK k))) =
        Complex.normSq ((Matrix.of g : Mat k 0) (iK k) (iK k)) := Complex.normSq_conj _
    rw [Complex.normSq_neg, this]; linarith
  calc ∫⁻ h', ∫⁻ h, Gf k σ h g h' ∂ν ∂ν
      ≤ ∫⁻ h', ENNReal.ofReal ((Real.sqrt 2)⁻¹ *
          ‖((Matrix.of g * Matrix.of h') *ᵥ phiV' k 0 0) (iK k)‖ / 2) ^ (-σ) *
            (C0 k σ ν + ν Set.univ) ∂ν := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_mem_fixedUnitary hν] with h' hh'
        obtain ⟨e, hne⟩ := iso_y hk hg hh'.1
        unfold Gf
        exact bnd hk hν hσ (lam := (Real.sqrt 2)⁻¹) (by positivity)
          ((Matrix.of g * Matrix.of h') *ᵥ phiV' k 0 0) _ hne (le_of_eq e)
    _ = (∫⁻ h', ENNReal.ofReal (1 / 4 * ‖((Matrix.of h')ᴴ *ᵥ (fun j => star ((Matrix.of g : Mat k 0) (iK k) j)))
          (iW k) + -star ((Matrix.of g : Mat k 0) (iK k) (iK k))‖) ^ (-σ) ∂ν) * (C0 k σ ν + ν Set.univ) := by
        rw [lintegral_mul_const' _ _ hK1f]
        congr 1
        refine lintegral_congr_ae ?_
        filter_upwards [ae_mem_fixedUnitary hν] with h' hh'
        rw [outer_eq hk hh' (Matrix.of g)]
        congr 2
        rw [← mul_assoc, hc2]; ring
    _ ≤ (ENNReal.ofReal (1 / 4 * ‖-star ((Matrix.of g : Mat k 0) (iK k) (iK k))‖ / 2) ^ (-σ) *
          (C0 k σ ν + ν Set.univ)) * (C0 k σ ν + ν Set.univ) :=
        mul_le_mul' (bnd hk hν hσ (by norm_num) _ _ hb0 hvb) le_rfl
    _ ≤ (ENNReal.ofReal (1 / 8) ^ (-σ) * (C0 k σ ν + ν Set.univ)) * (C0 k σ ν + ν Set.univ) :=
        mul_le_mul' (mul_le_mul' (ofReal_rpow_neg_anti hσ (by rw [hbn]; linarith)) le_rfl) le_rfl
    _ = (C0 k σ ν + ν Set.univ) * (ENNReal.ofReal (1 / 8) ^ (-σ) * (C0 k σ ν + ν Set.univ)) := mul_comm _ _

theorem aStepBase_of (hB2 : InductiveHeisenbergInputs) (hT : TBoth) : AStepBase := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hCW, hGN, -, -, -, -, -, -, -, -, hHW, -⟩ := hB2
  intro k hk s hs μG hμG A hA
  obtain ⟨hσ0, hσk⟩ := s_facts hk hs
  obtain ⟨ν, hν⟩ := hHW k 0 (bvec (iK k)) (inWb_iK k) (Tz_iK k)
  have hν' : IsHaarOn (U0 k) ν := hν
  have hνf := haar_univ_lt_top hCW hν'
  have hν0 : ν Set.univ ≠ 0 := fun h => hν.ne_zero (Measure.measure_univ_eq_zero.mp h)
  have : IsFiniteMeasure ν := ⟨hνf⟩
  have : IsFiniteMeasureOnCompacts μG := ⟨fun K hK => hμG.finite_compact K hK⟩
  have hC0 := haarIntegralConstant_lt_top hk hν' hνf hσ0 hσk
  have hK1f : C0 k (s 0) ν + ν Set.univ ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hC0.ne, hνf.ne⟩
  have hKc : (C0 k (s 0) ν + ν Set.univ) *
      (ENNReal.ofReal (1 / 8) ^ (-s 0) * (C0 k (s 0) ν + ν Set.univ)) ≠ ∞ := by
    refine ENNReal.mul_ne_top hK1f (ENNReal.mul_ne_top ?_ hK1f)
    rw [ENNReal.ofReal_rpow_of_pos (by norm_num)]; exact ENNReal.ofReal_ne_top
  have key := avg_key hk hT (s := s) hμG A hν'
  have hfin : ∫⁻ g, PhiA k A g * ∫⁻ h', ∫⁻ h, Gf k (s 0) h g h' ∂ν ∂ν ∂μG < ∞ := by
    calc ∫⁻ g, PhiA k A g * ∫⁻ h', ∫⁻ h, Gf k (s 0) h g h' ∂ν ∂ν ∂μG
        ≤ ∫⁻ g, PhiA k A g * ((C0 k (s 0) ν + ν Set.univ) *
            (ENNReal.ofReal (1 / 8) ^ (-s 0) * (C0 k (s 0) ν + ν Set.univ))) ∂μG := by
          refine lintegral_mono_ae ?_
          filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμG.conc] with g hg
          exact mul_le_mul' le_rfl (ptw hk hσ0 hν' hK1f g (not_not.mp hg))
      _ = (∫⁻ g, PhiA k A g ∂μG) * ((C0 k (s 0) ν + ν Set.univ) *
            (ENNReal.ofReal (1 / 8) ^ (-s 0) * (C0 k (s 0) ν + ν Set.univ))) :=
          lintegral_mul_const' _ _ hKc
      _ < ∞ := ENNReal.mul_lt_top (hGN k 0 μG A hμG hA) hKc.lt_top
  by_contra hc
  rw [not_lt, top_le_iff] at hc
  rw [hc, ENNReal.top_mul (mul_ne_zero hν0 hν0)] at key
  rw [← key] at hfin
  exact lt_irrefl _ hfin

end ReciprocityTheory.ChartRestriction.DS.Xi
