module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelRegionNormBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FixedPointsGramVector
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingAffine
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOpNormPowerIntegralLtTopClosedSubgroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselRegularDoubleCosetPolynomialProperness
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryOpNormBoundedByTwoFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RegularPosCompl
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem regular_pos_compl : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → γ ∈ GG k r → Gf k r z z' γ ≠ 0 → 0 < Gf k r z z' γ ∧ Dmin k r z z' γ (Fin.last (r + 1)) ≠ 0 ∧ IsUnit (gramM k r z z' γ).det ∧ ∀ y : Fin (2 * r + k + 1) → ℂ, y ≠ 0 → (∀ i, herm (Hpk k r) y (gramVec k r z z' γ i) = 0) → 0 < (herm (Hpk k r) y y).re := by
  intro k r z z' γ hz hz' hT hT' hγ hG

  have hGpos : 0 < Gf k r z z' γ :=
    lt_of_le_of_ne (Formalism.QuantumDeterminants.gNonneg k r z z' hz hz' hT hT' γ hγ) (Ne.symm hG)

  have hdet : (gramM k r z z' γ).det ≠ 0 := by
    intro h0
    apply hG
    have hg := Formalism.QuantumDeterminants.gGram k r z z' hz hz' γ hγ
    rw [h0, mul_zero] at hg
    exact_mod_cast hg

  have hk : 1 ≤ k := by
    by_contra hk0
    have hk' : k = 0 := by omega
    subst hk'
    apply hdet
    have hunit : ¬ IsUnit (gramM 0 r z z' γ) := by
      intro hu
      have h1 := Matrix.rank_of_isUnit _ hu
      rw [Formalism.QuantumDeterminants.gn_gramM_eq] at h1
      have h2 := Matrix.rank_mul_le_right
        ((Formalism.QuantumDeterminants.gnB 0 r z z' γ)ᴴ * Hpk 0 r) (Formalism.QuantumDeterminants.gnB 0 r z z' γ)
      have h3 := Matrix.rank_le_card_height (Formalism.QuantumDeterminants.gnB 0 r z z' γ)
      simp only [Fintype.card_sum, Fintype.card_fin] at h1 h3
      omega
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hunit
    exact hunit
  refine ⟨hGpos, ?_, isUnit_iff_ne_zero.mpr hdet, ?_⟩
  ·
    intro h0
    have hG' := hGpos
    unfold Gf at hG'
    rw [h0, map_zero] at hG'
    have hTT := mul_pos hT hT'
    have hn := Complex.normSq_nonneg (Dmin k r z z' γ ⟨r, by omega⟩)
    nlinarith
  ·
    intro y hy horth
    have hmem : y ∈ Formalism.FourierDecayAlt.C2.Uperp k r z z' γ := by
      rw [Formalism.FourierDecayAlt.C2.Uperp, LinearMap.mem_ker, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec]
      funext i
      rw [Pi.zero_apply, ← horth i]
      simp [herm, Matrix.mulVec, dotProduct]
    exact (Formalism.FourierDecayAlt.P.gram_independent_signature' k r z z' γ ⟨hk, ⟨hz, hT⟩, ⟨hz', hT'⟩⟩ ⟨hγ, hGpos⟩).2.2.1 y hmem hy

end GlobalTheory.SgInf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryOpNormBoundedByTwoFrames
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.IsomBound

open GlobalTheory.SgInf.FrameBound

variable {n : ℕ} {ι : Type} [Fintype ι]

theorem eucl_add_le (u v : Fin n → ℂ) : eucl (u + v) ≤ eucl u + eucl v := by
  rw [eucl_eq, eucl_eq, eucl_eq]
  exact norm_add_le (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 v)

theorem eucl_sub_le (u v : Fin n → ℂ) : eucl (u - v) ≤ eucl u + eucl v := by
  rw [eucl_eq, eucl_eq, eucl_eq]
  exact norm_sub_le (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 v)

theorem eucl_smul (c : ℂ) (v : Fin n → ℂ) : eucl (c • v) = ‖c‖ * eucl v := by
  rw [eucl_eq, eucl_eq]
  exact norm_smul c (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))

theorem eucl_sum_le {κ : Type} (s : Finset κ) (f : κ → Fin n → ℂ) :
    eucl (∑ i ∈ s, f i) ≤ ∑ i ∈ s, eucl (f i) := by
  simp only [eucl_eq]
  rw [WithLp.toLp_sum]
  exact norm_sum_le _ _

theorem norm_star_dot_le (w v : Fin n → ℂ) : ‖star w ⬝ᵥ v‖ ≤ eucl w * eucl v := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 v)
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, ← eucl_eq, ← eucl_eq] at h
  exact h

theorem star_dot_self (v : Fin n → ℂ) : star v ⬝ᵥ v = ((eucl v ^ 2 : ℝ) : ℂ) := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, ← eucl_eq] at h
  rw [h]; norm_cast

theorem star_dot_mulVec (H : Matrix (Fin n) (Fin n) ℂ) (w v : Fin n → ℂ) :
    star (H *ᵥ w) ⬝ᵥ v = star w ⬝ᵥ (Hᴴ *ᵥ v) := by
  rw [star_mulVec, dotProduct_mulVec]

theorem eucl_mulVec_of_unitary {H : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ * H = 1) (v : Fin n → ℂ) :
    eucl (H *ᵥ v) = eucl v := by
  have h1 := star_dot_self (H *ᵥ v)
  rw [star_dot_mulVec, mulVec_mulVec, hH, one_mulVec, star_dot_self] at h1
  have h2 : eucl (H *ᵥ v) ^ 2 = eucl v ^ 2 := by exact_mod_cast h1.symm
  exact (pow_left_inj₀ (eucl_nonneg _) (eucl_nonneg _) two_ne_zero).1 h2

def fam (b : ι → Fin n → ℂ) : Matrix (Fin n) ι ℂ := fun p i => b i p

theorem fam_mulVec (b : ι → Fin n → ℂ) (x : ι → ℂ) : fam b *ᵥ x = ∑ i, x i • b i := by
  funext p
  simp [fam, mulVec, dotProduct, Finset.sum_apply, mul_comm]

omit [Fintype ι] in
theorem famH_mulVec_apply (b : ι → Fin n → ℂ) (y : Fin n → ℂ) (j : ι) :
    ((fam b)ᴴ *ᵥ y) j = star (b j) ⬝ᵥ y := by
  simp [fam, mulVec, dotProduct, conjTranspose_apply]

omit [Fintype ι] in
theorem mul_fam (s : Matrix (Fin n) (Fin n) ℂ) (b : ι → Fin n → ℂ) :
    s * fam b = fam (fun i => s *ᵥ b i) := by
  ext p i
  simp [fam, Matrix.mul_apply, mulVec, dotProduct]

omit [Fintype ι] in
theorem famH_mul_mul_fam (H : Matrix (Fin n) (Fin n) ℂ) (b : ι → Fin n → ℂ) (m i : ι) :
    ((fam b)ᴴ * H * fam b) m i = herm H (b i) (b m) := by
  simp only [herm, Matrix.mul_apply, fam, mulVec, dotProduct, conjTranspose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [Pi.star_apply]; ring

theorem eucl_fam_mulVec_le (b : ι → Fin n → ℂ) (M : ℝ) (hM : ∀ i, eucl (b i) ≤ M) (x : ι → ℂ) :
    eucl (fam b *ᵥ x) ≤ M * ∑ i, ‖x i‖ := by
  rw [fam_mulVec]
  refine (eucl_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [eucl_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hM i) (norm_nonneg _)

theorem sum_norm_mulVec_le (Ti : Matrix ι ι ℂ) (y : ι → ℂ) (Y : ℝ) (hY : ∀ j, ‖y j‖ ≤ Y) :
    ∑ i, ‖(Ti *ᵥ y) i‖ ≤ (∑ i, ∑ j, ‖Ti i j‖) * Y := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul]
  simp only [mulVec, dotProduct]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hY j) (norm_nonneg _)

omit [Fintype ι] in
theorem vecMul_fam (c : ι → Fin n → ℂ) (y : Fin n → ℂ) (i : ι) : (y ᵥ* fam c) i = y ⬝ᵥ c i := by
  simp [fam, vecMul, dotProduct]

theorem herm_fam_mulVec (H : Matrix (Fin n) (Fin n) ℂ) (c : ι → Fin n → ℂ) (x : ι → ℂ) (v : Fin n → ℂ) :
    herm H (fam c *ᵥ x) v = ∑ i, herm H (c i) v * x i := by
  unfold herm
  rw [mulVec_mulVec, dotProduct_mulVec, mul_fam]
  simp only [dotProduct, vecMul_fam]

theorem herm_swap {H : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ = H) (v w : Fin n → ℂ) :
    herm H v w = star (herm H w v) := by
  unfold herm
  rw [star_dotProduct, star_dot_mulVec, hH]

theorem herm_sub_smul {H : Matrix (Fin n) (Fin n) ℂ} (v w : Fin n → ℂ) (t : ℂ) :
    herm H (v - t • w) (v - t • w) =
      herm H v v - t * herm H w v - star t * herm H v w + star t * t * herm H w w := by
  simp only [herm, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, star_sub, star_smul,
    sub_dotProduct, smul_dotProduct, smul_eq_mul]
  ring

theorem herm_re_le {H : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ * H = 1) (w : Fin n → ℂ) :
    (herm H w w).re ≤ eucl w ^ 2 := by
  refine (Complex.re_le_norm _).trans ?_
  unfold herm
  refine (norm_star_dot_le _ _).trans ?_
  rw [eucl_mulVec_of_unitary hH, sq]

def gram (H : Matrix (Fin n) (Fin n) ℂ) (b : ι → Fin n → ℂ) : Matrix ι ι ℂ := fun m i => herm H (b i) (b m)

omit [Fintype ι] in
theorem gram_eq (H : Matrix (Fin n) (Fin n) ℂ) (b : ι → Fin n → ℂ) : gram H b = (fam b)ᴴ * H * fam b := by
  ext m i; rw [famH_mul_mul_fam]; rfl

theorem eucl_proj_le {H : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ * H = 1) (b b' : ι → Fin n → ℂ)
    (Ti : Matrix ι ι ℂ) (M M' : ℝ) (hM' : 0 ≤ M') (hM : ∀ i, eucl (b i) ≤ M) (hb' : ∀ i, eucl (b' i) ≤ M')
    (u : Fin n → ℂ) :
    eucl (fam b' *ᵥ (Ti *ᵥ ((fam b)ᴴ *ᵥ (H *ᵥ u)))) ≤ M' * ((∑ i, ∑ j, ‖Ti i j‖) * (M * eucl u)) := by
  refine (eucl_fam_mulVec_le b' M' hb' _).trans (mul_le_mul_of_nonneg_left ?_ hM')
  refine sum_norm_mulVec_le Ti _ _ fun j => ?_
  rw [famH_mulVec_apply]
  refine (norm_star_dot_le _ _).trans ?_
  rw [eucl_mulVec_of_unitary hH]
  exact mul_le_mul_of_nonneg_right (hM j) (eucl_nonneg _)


omit [Fintype ι] in
theorem sq_le_of_pos {H : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ = H) (hH2 : H * H = 1)
    (b' : ι → Fin n → ℂ) (hpos : ∀ y, (∀ i, herm H y (b' i) = 0) → 0 ≤ (herm H y y).re)
    (v w : Fin n → ℂ) (hv : ∀ i, herm H v (b' i) = 0) (hw : ∀ i, herm H w (b' i) = 0)
    (hwv : herm H w v = ((eucl v ^ 2 : ℝ) : ℂ)) (a : ℝ) (ha : 0 < a) (hw2 : eucl w ≤ a * eucl v) :
    eucl v ^ 2 ≤ a ^ 2 * (herm H v v).re := by
  have hH' : Hᴴ * H = 1 := by rw [hH, hH2]
  set t : ℝ := 1 / a ^ 2 with ht
  have hy : ∀ i, herm H (v - (t : ℂ) • w) (b' i) = 0 := fun i => by
    simp only [herm, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    change herm H v (b' i) - _ * herm H w (b' i) = 0
    rw [hv, hw, mul_zero, sub_zero]
  have h0 := hpos _ hy
  rw [herm_sub_smul, herm_swap hH v w, hwv] at h0
  have hW := herm_re_le hH' w
  have ht0 : 0 < t := by positivity
  have hwa : eucl w ^ 2 ≤ a ^ 2 * eucl v ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (eucl_nonneg _) hw2 2
  simp only [Complex.add_re, Complex.sub_re, Complex.star_def, Complex.conj_ofReal, mul_assoc,
    Complex.re_ofReal_mul, Complex.ofReal_re] at h0
  have hta : t * a ^ 2 = 1 := by rw [ht]; field_simp
  have h1 : t * (t * (herm H w w).re) ≤ t * eucl v ^ 2 := by
    calc t * (t * (herm H w w).re) ≤ t * (t * (a ^ 2 * eucl v ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hW.trans hwa) ht0.le) ht0.le
      _ = t * eucl v ^ 2 := by rw [← mul_assoc t (a ^ 2), hta, one_mul]
  have h2 : t * eucl v ^ 2 ≤ (herm H v v).re := by linarith
  calc eucl v ^ 2 = a ^ 2 * (t * eucl v ^ 2) := by rw [← mul_assoc, mul_comm (a ^ 2) t, hta, one_mul]
    _ ≤ a ^ 2 * (herm H v v).re := mul_le_mul_of_nonneg_left h2 (sq_nonneg a)

variable [DecidableEq ι]

def proj (H : Matrix (Fin n) (Fin n) ℂ) (b : ι → Fin n → ℂ) (Ti : Matrix ι ι ℂ) (u : Fin n → ℂ) :
    Fin n → ℂ :=
  fam b *ᵥ (Ti *ᵥ ((fam b)ᴴ *ᵥ (H *ᵥ u)))

theorem herm_sub_proj {H : Matrix (Fin n) (Fin n) ℂ} {b : ι → Fin n → ℂ} {Ti : Matrix ι ι ℂ}
    (hTi : gram H b * Ti = 1) (u : Fin n → ℂ) (m : ι) : herm H (u - proj H b Ti u) (b m) = 0 := by
  have e : ∀ x : Fin n → ℂ, herm H x (b m) = ((fam b)ᴴ *ᵥ (H *ᵥ x)) m := fun x => by
    rw [famH_mulVec_apply]; rfl
  rw [e, proj]
  simp only [mulVec_sub, mulVec_mulVec, ← Matrix.mul_assoc]
  rw [← gram_eq, hTi, Matrix.one_mul, sub_self, Pi.zero_apply]

theorem sq_le_compl {H : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ = H) (hH2 : H * H = 1)
    (b' : ι → Fin n → ℂ) (Ti : Matrix ι ι ℂ) (hTi : gram H b' * Ti = 1)
    (hpos : ∀ y, (∀ i, herm H y (b' i) = 0) → 0 ≤ (herm H y y).re)
    (β : ℝ) (hβ : 0 ≤ β) (hb' : ∀ i, eucl (b' i) ≤ β) (v : Fin n → ℂ) (hv : ∀ i, herm H v (b' i) = 0) :
    eucl v ^ 2 ≤ (1 + (∑ i, ∑ j, ‖Ti i j‖) * β ^ 2) ^ 2 * (herm H v v).re := by
  have hH' : Hᴴ * H = 1 := by rw [hH, hH2]
  set N := ∑ i, ∑ j, ‖Ti i j‖ with hN
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  set u' := H *ᵥ v with hu'
  set w := u' - proj H b' Ti u' with hw
  refine sq_le_of_pos hH hH2 b' hpos v w hv (herm_sub_proj hTi u') ?_ _ (by positivity) ?_
  · have e : herm H (u' - proj H b' Ti u') v = herm H u' v - herm H (proj H b' Ti u') v := by
      simp only [herm, mulVec_sub, dotProduct_sub]
    rw [hw, e, proj, herm_fam_mulVec,
      Finset.sum_eq_zero fun i _ => by rw [herm_swap hH, hv i, star_zero, zero_mul], sub_zero]
    unfold herm
    rw [hu', mulVec_mulVec, hH2, one_mulVec, star_dot_self]
  · refine (eucl_sub_le _ _).trans ?_
    have h1 : eucl u' = eucl v := eucl_mulVec_of_unitary hH' v
    have h2 := eucl_proj_le hH' b' b' Ti β β hβ hb' hb' u'
    rw [h1] at h2 ⊢
    have h2' : eucl (proj H b' Ti u') ≤ β * (N * (β * eucl v)) := h2
    have e : β * (N * (β * eucl v)) = N * β ^ 2 * eucl v := by ring
    linarith

theorem det_isUnit_of_herm {H s : Matrix (Fin n) (Fin n) ℂ} (hH2 : H * H = 1) (hs : sᴴ * H * s = H) :
    IsUnit s.det := by
  have h1 : H.det * H.det = 1 := by rw [← det_mul, hH2, det_one]
  have h2 := congrArg Matrix.det hs
  rw [det_mul, det_mul] at h2
  have hH0 : H.det ≠ 0 := fun h => by rw [h, zero_mul] at h1; exact zero_ne_one h1
  have h3 : H.det * (s.det * sᴴ.det) = H.det * 1 := by rw [mul_one]; linear_combination h2
  exact IsUnit.of_mul_eq_one _ (mul_left_cancel₀ hH0 h3)

theorem herm_mulVec_mulVec {H s : Matrix (Fin n) (Fin n) ℂ} (hs : sᴴ * H * s = H) (x y : Fin n → ℂ) :
    herm H (s *ᵥ x) (s *ᵥ y) = herm H x y := by
  unfold herm
  rw [star_mulVec, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, ← Matrix.mul_assoc, hs,
    ← dotProduct_mulVec]

theorem core {H : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ = H) (hH2 : H * H = 1)
    (b : ι → Fin n → ℂ) (Ti : Matrix ι ι ℂ) (hTi : gram H b * Ti = 1)
    (hpos : ∀ y, (∀ i, herm H y (b i) = 0) → 0 ≤ (herm H y y).re)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ i, eucl (b i) ≤ M)
    (s : Matrix (Fin n) (Fin n) ℂ) (hs : sᴴ * H * s = H)
    (β : ℝ) (hβ1 : 1 ≤ β) (hβ : ∀ i, eucl (s *ᵥ b i) ≤ β) (u : Fin n → ℂ) :
    eucl (s *ᵥ u) ≤ ((∑ i, ∑ j, ‖Ti i j‖) * M + (1 + ∑ i, ∑ j, ‖Ti i j‖) *
      (1 + (∑ i, ∑ j, ‖Ti i j‖) * M ^ 2)) * β ^ 2 * eucl u := by
  have hH' : Hᴴ * H = 1 := by rw [hH, hH2]
  set N := ∑ i, ∑ j, ‖Ti i j‖ with hN
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  have hβ0 : 0 ≤ β := zero_le_one.trans hβ1
  set b' : ι → Fin n → ℂ := fun i => s *ᵥ b i with hb'
  have hiso : ∀ x y, herm H (s *ᵥ x) (s *ᵥ y) = herm H x y := herm_mulVec_mulVec hs
  have hgram : gram H b' = gram H b := by ext m i; exact hiso _ _
  have hdet := det_isUnit_of_herm hH2 hs
  have hpos' : ∀ y, (∀ i, herm H y (b' i) = 0) → 0 ≤ (herm H y y).re := fun y hy => by
    have e : y = s *ᵥ (s⁻¹ *ᵥ y) := by rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
    have := hpos (s⁻¹ *ᵥ y) fun i => by rw [← hiso, ← e]; exact hy i
    rwa [← hiso, ← e] at this
  set y := u - proj H b Ti u with hy
  have hyb : ∀ i, herm H y (b i) = 0 := herm_sub_proj hTi u
  have hv : ∀ i, herm H (s *ᵥ y) (b' i) = 0 := fun i => by
    show herm H (s *ᵥ y) (s *ᵥ b i) = 0
    rw [hiso]; exact hyb i
  have esplit : s *ᵥ u = s *ᵥ proj H b Ti u + s *ᵥ y := by rw [hy, mulVec_sub, add_sub_cancel]
  have h1 : eucl (s *ᵥ proj H b Ti u) ≤ β * (N * (M * eucl u)) := by
    rw [proj, mulVec_mulVec, mul_fam]
    exact eucl_proj_le hH' b b' Ti M β hβ0 hM hβ u
  have hy2 : eucl y ≤ (1 + N * M ^ 2) * eucl u := by
    refine (eucl_sub_le _ _).trans ?_
    have := eucl_proj_le hH' b b Ti M M hM0 hM hM u
    rw [proj]
    have e : M * (N * (M * eucl u)) = N * M ^ 2 * eucl u := by ring
    linarith
  have h2 := sq_le_compl hH hH2 b' Ti (hgram ▸ hTi) hpos' β hβ0 hβ (s *ᵥ y) hv
  rw [hiso] at h2
  have h3 : (herm H y y).re ≤ eucl y ^ 2 := herm_re_le hH' y
  have hA : 0 ≤ 1 + N * β ^ 2 := add_nonneg zero_le_one (mul_nonneg hN0 (sq_nonneg _))
  have hB : 0 ≤ 1 + N * M ^ 2 := add_nonneg zero_le_one (mul_nonneg hN0 (sq_nonneg _))
  have h4 : eucl (s *ᵥ y) ^ 2 ≤ ((1 + N * β ^ 2) * ((1 + N * M ^ 2) * eucl u)) ^ 2 := by
    calc eucl (s *ᵥ y) ^ 2 ≤ (1 + N * β ^ 2) ^ 2 * (herm H y y).re := h2
      _ ≤ (1 + N * β ^ 2) ^ 2 * eucl y ^ 2 := mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
      _ ≤ (1 + N * β ^ 2) ^ 2 * ((1 + N * M ^ 2) * eucl u) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (eucl_nonneg _) hy2 2) (sq_nonneg _)
      _ = _ := by ring
  have h5 : eucl (s *ᵥ y) ≤ (1 + N * β ^ 2) * ((1 + N * M ^ 2) * eucl u) :=
    (pow_le_pow_iff_left₀ (eucl_nonneg _) (mul_nonneg hA (mul_nonneg hB (eucl_nonneg _))) two_ne_zero).1 h4
  rw [esplit]
  refine (eucl_add_le _ _).trans ?_
  have hu0 := eucl_nonneg u
  have hb2 : β ≤ β ^ 2 := by nlinarith
  have hb3 : 1 + N * β ^ 2 ≤ (1 + N) * β ^ 2 := by nlinarith
  have e1 : β * (N * (M * eucl u)) ≤ β ^ 2 * (N * (M * eucl u)) :=
    mul_le_mul_of_nonneg_right hb2 (mul_nonneg hN0 (mul_nonneg hM0 hu0))
  have e2 : (1 + N * β ^ 2) * ((1 + N * M ^ 2) * eucl u) ≤ ((1 + N) * β ^ 2) * ((1 + N * M ^ 2) * eucl u) :=
    mul_le_mul_of_nonneg_right hb3 (mul_nonneg hB hu0)
  have e3 : β ^ 2 * (N * (M * eucl u)) + ((1 + N) * β ^ 2) * ((1 + N * M ^ 2) * eucl u) =
      (N * M + (1 + N) * (1 + N * M ^ 2)) * β ^ 2 * eucl u := by ring
  linarith

end GlobalTheory.SgInf.IsomBound

namespace GlobalTheory.SgInf

open IsomBound FrameBound

theorem continuous_eucl {N : ℕ} : Continuous (eucl : (Fin N → ℂ) → ℝ) := by
  unfold eucl
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
    Complex.continuous_normSq.comp (continuous_apply i))

variable {k r : ℕ}

theorem continuous_gramVec (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1) ⊕ Fin (r + 1)) :
    Continuous fun γ : Mat k r => gramVec k r z z' γ i := by
  cases i with
  | inl a => exact continuous_const
  | inr b => exact continuous_id.matrix_mulVec continuous_const

theorem continuous_gramM (z z' : Fin (2 * r + k + 1) → ℂ) :
    Continuous fun γ : Mat k r => gramM k r z z' γ := by
  refine continuous_matrix fun i j => ?_
  unfold gramM herm
  exact (continuous_gramVec z z' i).star.dotProduct
    (continuous_const.matrix_mulVec (continuous_gramVec z z' j))

def isomConst (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) : ℝ :=
  (∑ i, ∑ j, ‖(gramM k r z z' γ)⁻¹ i j‖) * (∑ i, eucl (gramVec k r z z' γ i)) +
    (1 + ∑ i, ∑ j, ‖(gramM k r z z' γ)⁻¹ i j‖) *
      (1 + (∑ i, ∑ j, ‖(gramM k r z z' γ)⁻¹ i j‖) * (∑ i, eucl (gramVec k r z z' γ i)) ^ 2)

theorem continuousOn_isomConst (z z' : Fin (2 * r + k + 1) → ℂ) (C : Set (Mat k r))
    (hC : ∀ γ ∈ C, IsUnit (gramM k r z z' γ).det) : ContinuousOn (isomConst z z') C := by
  have hM : Continuous fun γ : Mat k r => ∑ i, eucl (gramVec k r z z' γ i) :=
    continuous_finsetSum _ fun i _ => continuous_eucl.comp (continuous_gramVec z z' i)
  have hN : ContinuousOn (fun γ : Mat k r => ∑ i, ∑ j, ‖(gramM k r z z' γ)⁻¹ i j‖) C := by
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ContinuousOn.norm ?_
    have e : ∀ γ ∈ C, (gramM k r z z' γ)⁻¹ i j =
        (gramM k r z z' γ).det⁻¹ * (gramM k r z z' γ).adjugate i j := fun γ _ => by
      rw [Matrix.inv_def, Ring.inverse_eq_inv]; rfl
    refine ContinuousOn.congr ?_ e
    refine ContinuousOn.mul (ContinuousOn.inv₀ ((continuous_gramM z z').matrix_det.continuousOn)
      fun γ hγ => (hC γ hγ).ne_zero) ?_
    exact ((continuous_gramM z z').matrix_adjugate.matrix_elem i j).continuousOn
  unfold isomConst
  exact (hN.mul hM.continuousOn).add ((continuousOn_const.add hN).mul
    (continuousOn_const.add (hN.mul (hM.pow 2).continuousOn)))

theorem isom_frame_bound : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (C : Set (Mat k r)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsCompact C → (∀ γ ∈ C, γ ∈ GG k r ∧ Gf k r z z' γ ≠ 0) → ∃ C0 : ℝ, ∀ γ ∈ C, ∀ s ∈ GG k r, ∀ B : ℝ, 1 ≤ B → (∀ i, eucl (s *ᵥ gramVec k r z z' γ i) ≤ B) → opn s ≤ C0 * B ^ 2 := by
  intro k r z z' C hz hz' hT hT' hC hreg
  have hR := fun γ (hγ : γ ∈ C) =>
    regular_pos_compl k r z z' γ hz hz' hT hT' (hreg γ hγ).1 (hreg γ hγ).2
  obtain ⟨C0, hC0⟩ := hC.exists_bound_of_continuousOn
    (continuousOn_isomConst z z' C fun γ hγ => (hR γ hγ).2.2.1)
  refine ⟨C0, fun γ hγ s hs B hB1 hB => ?_⟩
  obtain ⟨hH1, hH2, -⟩ := hpkFacts k r
  set N := ∑ i, ∑ j, ‖(gramM k r z z' γ)⁻¹ i j‖ with hN
  set M := ∑ i, eucl (gramVec k r z z' γ i) with hM
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => eucl_nonneg _
  have hMi : ∀ i, eucl (gramVec k r z z' γ i) ≤ M := fun i =>
    Finset.single_le_sum (f := fun i => eucl (gramVec k r z z' γ i)) (fun _ _ => eucl_nonneg _)
      (Finset.mem_univ i)
  have hTi : gram (Hpk k r) (gramVec k r z z' γ) * (gramM k r z z' γ)⁻¹ = 1 := by
    have e : gram (Hpk k r) (gramVec k r z z' γ) = gramM k r z z' γ := rfl
    rw [e]; exact mul_nonsing_inv _ (hR γ hγ).2.2.1
  have hpos : ∀ y, (∀ i, herm (Hpk k r) y (gramVec k r z z' γ i) = 0) →
      0 ≤ (herm (Hpk k r) y y).re := fun y hy => by
    by_cases h0 : y = 0
    · subst h0; simp [herm]
    · exact ((hR γ hγ).2.2.2 y h0 hy).le
  have key := fun u => core hH1 hH2 (gramVec k r z z' γ) (gramM k r z z' γ)⁻¹ hTi hpos M hM0 hMi s hs
    B hB1 hB u
  have eK : isomConst z z' γ = N * M + (1 + N) * (1 + N * M ^ 2) := rfl
  have hK0 : 0 ≤ isomConst z z' γ := by
    rw [eK]
    exact add_nonneg (mul_nonneg hN0 hM0) (mul_nonneg (add_nonneg zero_le_one hN0)
      (add_nonneg zero_le_one (mul_nonneg hN0 (sq_nonneg _))))
  have hK : isomConst z z' γ ≤ C0 := (le_abs_self _).trans (Real.norm_eq_abs _ ▸ hC0 γ hγ)
  have hB0 : 0 ≤ B ^ 2 := sq_nonneg _
  have hopn : opn s ≤ isomConst z z' γ * B ^ 2 := by
    unfold opn
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK0 hB0) fun x => ?_
    have h := key (WithLp.ofLp x)
    have e1 : eucl (s *ᵥ WithLp.ofLp x) = ‖Matrix.toEuclideanCLM (𝕜 := ℂ) s x‖ := by rw [eucl_eq]; rfl
    have e2 : eucl (WithLp.ofLp x) = ‖x‖ := by rw [eucl_eq]
    rw [e1, e2] at h
    rw [eK]
    exact h
  exact hopn.trans (mul_le_mul_of_nonneg_right hK hB0)

end GlobalTheory.SgInf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryOpNormBoundedByTwoFramesStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometry_opNorm_bounded_by_two_frames : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (C : Set (Mat k r)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsCompact C → (∀ γ ∈ C, γ ∈ GG k r ∧ Gf k r z z' γ ≠ 0) → ∃ C0 : ℝ, ∀ γ ∈ C, ∀ s ∈ GG k r, ∀ B : ℝ, 1 ≤ B → (∀ i, eucl (s *ᵥ gramVec k r z z' γ i) ≤ B) → opn s ≤ C0 * B ^ 2 := by
  first | exact @GlobalTheory.SgInf.isom_frame_bound | exact GlobalTheory.SgInf.isom_frame_bound | (intros; apply GlobalTheory.SgInf.isom_frame_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselRegularDoubleCosetPolynomialProperness
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.PolyProper

variable {k r : ℕ}

theorem gram_det_unit : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (hermitian_pos_facts_hold k r).2.1

theorem mul_mem {g h : Mat k r} (hg : g ∈ GG k r) (hh : h ∈ GG k r) : g * h ∈ GG k r :=
  (unitary_group_holds _ _ gram_det_unit).2.1 g hg h hh

theorem inv_mem {g : Mat k r} (hg : g ∈ GG k r) : g⁻¹ ∈ GG k r :=
  ((unitary_group_holds _ _ gram_det_unit).2.2 g hg).2

theorem det_unit {g : Mat k r} (hg : g ∈ GG k r) : IsUnit g.det :=
  ((unitary_group_holds _ _ gram_det_unit).2.2 g hg).1

theorem mem_of_S {z : Fin (2 * r + k + 1) → ℂ} {s : Mat k r} (hs : s ∈ Sset k r z) : s ∈ GG k r := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  exact mul_mem hh.1 hm.1

theorem inv_eq {g : Mat k r} (hg : g ∈ GG k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  apply Matrix.inv_eq_left_inv
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  rw [Matrix.mul_assoc (Hpk k r), Matrix.mul_assoc (Hpk k r), h]
  exact (hermitian_pos_facts_hold k r).2.1

theorem left_bound (z z' : Fin (2 * r + k + 1) → ℂ) (C : Set (Mat k r)) (hz : inWb k r z)
    (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') (hC : IsCompact C)
    (hCr : C ⊆ Greg k r z z') :
    ∃ C0 : ℝ, ∀ γ ∈ C, ∀ s ∈ Sset k r z, ∀ s' ∈ Sset k r z',
      opn s ≤ C0 * opn (s * γ * s'⁻¹) ^ (2 * (r ^ 2 + r + 1)) := by
  obtain ⟨C1, h1⟩ := GlobalTheory.T.siegel_region_norm_bound k r z z' C hz hz' hT hT' hC hCr
  obtain ⟨C2, h2⟩ := GlobalTheory.T.isometry_opNorm_bounded_by_two_frames k r z z' C hz hz' hT hT' hC
    (fun γ hγ => ⟨(hCr hγ).1, (hCr hγ).2.2⟩)
  obtain ⟨hN1, -, -, -, hN5, -⟩ := GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r
  refine ⟨C2 * (max 1 C1) ^ 2, fun γ hγ s hs s' hs' => ?_⟩
  have hsG := mem_of_S hs
  have hs'G := mem_of_S hs'
  have hγG : γ ∈ GG k r := (hCr hγ).1
  have hxG : s * γ * s'⁻¹ ∈ GG k r := mul_mem (mul_mem hsG hγG) (inv_mem hs'G)
  have hx1 : 1 ≤ opn (s * γ * s'⁻¹) := (hN1 _ hxG).2
  have hxs : (s * γ * s'⁻¹) * s' = s * γ := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (det_unit hs'G), Matrix.mul_one]
  have h1' := h1 γ hγ s hs s' hs'
  have h5 := hN5 (s * γ * s'⁻¹)
  set X := opn (s * γ * s'⁻¹) with hX
  have hp1 : 1 ≤ X ^ (r * (r + 1)) := one_le_pow₀ hx1
  have hm1 : (1 : ℝ) ≤ max 1 C1 := le_max_left _ _
  have hle : C1 * X ^ (r * (r + 1)) ≤ max 1 C1 * X ^ (r * (r + 1)) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hQ1 : 1 ≤ max 1 C1 * X ^ (r * (r + 1)) := one_le_mul_of_one_le_of_one_le hm1 hp1
  have hB : 1 ≤ X * (max 1 C1 * X ^ (r * (r + 1))) := one_le_mul_of_one_le_of_one_le hx1 hQ1
  have key := h2 γ hγ s hsG (X * (max 1 C1 * X ^ (r * (r + 1)))) hB (by
    rintro (a | b)
    · show eucl (s *ᵥ fvec k r z a) ≤ _
      refine ((h1' a).1.trans hle).trans ?_
      exact le_mul_of_one_le_left (by linarith) hx1
    · show eucl (s *ᵥ (γ *ᵥ fvec k r z' b)) ≤ _
      rw [Matrix.mulVec_mulVec, ← hxs, ← Matrix.mulVec_mulVec]
      refine (h5 _).trans ?_
      exact mul_le_mul_of_nonneg_left ((h1' b).2.trans hle) (by linarith))
  refine key.trans (le_of_eq ?_)
  ring

theorem poly_proper : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (C : Set (Mat k r)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsCompact C → C ⊆ Greg k r z z' → ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ γ ∈ C, ∀ s ∈ Sset k r z, ∀ s' ∈ Sset k r z', max (opn s) (opn s') ≤ C0 * opn (s * γ * s'⁻¹) ^ (2 * (r ^ 2 + r + 1)) := by
  intro k r z z' C hz hz' hT hT' hC hCr
  obtain ⟨C1, h1⟩ := left_bound z z' C hz hz' hT hT' hC hCr
  have hcont : Continuous fun g : Mat k r => Hpk k r * gᴴ * Hpk k r :=
    (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
  have hCr' : (fun g : Mat k r => Hpk k r * gᴴ * Hpk k r) '' C ⊆ Greg k r z' z := by
    rintro _ ⟨γ, hγ, rfl⟩
    have hγG : γ ∈ GG k r := (hCr hγ).1
    show Hpk k r * γᴴ * Hpk k r ∈ _
    rw [← inv_eq hγG]
    exact (GlobalTheory.T.besselZhat_inv_and_regular_iff k r z z' γ hγG).2.1 (hCr hγ)
  obtain ⟨C2, h2⟩ := left_bound z' z _ hz' hz hT' hT (hC.image hcont) hCr'
  obtain ⟨hN1, -⟩ := GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r
  refine ⟨max 1 (max C1 C2), le_max_left _ _, fun γ hγ s hs s' hs' => ?_⟩
  have hsG := mem_of_S hs
  have hs'G := mem_of_S hs'
  have hγG : γ ∈ GG k r := (hCr hγ).1
  have hxG : s * γ * s'⁻¹ ∈ GG k r := mul_mem (mul_mem hsG hγG) (inv_mem hs'G)
  have hinv : s' * γ⁻¹ * s⁻¹ = (s * γ * s'⁻¹)⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (det_unit hs'G),
      Matrix.mul_assoc]
  have ha := h1 γ hγ s hs s' hs'
  have hb := h2 γ⁻¹ ⟨γ, hγ, (inv_eq hγG).symm⟩ s' hs' s hs
  rw [hinv, (hN1 _ hxG).1] at hb
  have hp : 0 ≤ opn (s * γ * s'⁻¹) ^ (2 * (r ^ 2 + r + 1)) := pow_nonneg (opn_nonneg _) _
  refine max_le (ha.trans ?_) (hb.trans ?_)
  · exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hp
  · exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hp

end GlobalTheory.SgInf.PolyProper
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselRegularDoubleCosetPolynomialPropernessStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselRegularDoubleCoset_polynomial_properness : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (C : Set (Mat k r)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsCompact C → C ⊆ Greg k r z z' → ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ γ ∈ C, ∀ s ∈ Sset k r z, ∀ s' ∈ Sset k r z', max (opn s) (opn s') ≤ C0 * opn (s * γ * s'⁻¹) ^ (2 * (r ^ 2 + r + 1)) := by
  first | exact @GlobalTheory.SgInf.PolyProper.poly_proper | exact GlobalTheory.SgInf.PolyProper.poly_proper | (intros; apply GlobalTheory.SgInf.PolyProper.poly_proper <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOrbitOpNormIntegralFiniteOnCompactRegular
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.OrbNorm

theorem continuous_opn {n : ℕ} : Continuous (opn : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  unfold opn
  have h : Continuous (fun g : Matrix (Fin n) (Fin n) ℂ => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) g) :=
    LinearMap.continuous_of_finiteDimensional
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearEquiv.toLinearMap)
  exact continuous_norm.comp h

theorem opn_pos {k r : ℕ} {g : Mat k r} (hg : g ∈ GG k r) : 0 < opn g := by
  rcases (opn_nonneg g).lt_or_eq with h | h
  · exact h
  exfalso
  have h0 : g = 0 := by
    have h1 : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 * r + k + 1)) g = 0 := by
      rw [← norm_eq_zero]; exact h.symm
    simpa using h1
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  rw [h0] at hg'
  have hH : Hpk k r = 0 := by simpa using hg'.symm
  have hr : r < 2 * r + k + 1 := by omega
  have hent : Hpk k r ⟨r, hr⟩ ⟨r, hr⟩ = 0 := by rw [hH]; rfl
  simp only [Hpk] at hent
  split_ifs at hent
  all_goals first
    | exact absurd ⟨le_refl r, Nat.le_add_right r k, trivial⟩ ‹¬(r ≤ r ∧ r ≤ r + k ∧ True)›
    | norm_num at hent

theorem integrable_of_normInt {k r : ℕ} {μ : Measure (Mt k r)} {A : ℝ} (h : normInt μ A < ⊤) :
    Integrable (fun x : Mt k r => opn (Matrix.of x) ^ (-A)) μ := by
  have hm : Measurable (fun x : Mt k r => opn (Matrix.of x) ^ (-A)) :=
    ((continuous_opn.comp (continuous_id : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)))).measurable).pow_const _
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (opn_nonneg _) _)]
  exact h

theorem rpow_le {a a' x C0 A : ℝ} {M : ℕ} (ha : 0 < a) (ha' : 0 < a') (hx : 0 ≤ x) (hC : 0 < C0)
    (hA : 0 ≤ A) (h : max a a' ≤ C0 * x ^ M) :
    x ^ (-(2 * M * A)) ≤ C0 ^ (2 * A) * (a ^ (-A) * a' ^ (-A)) := by
  have hy : 0 < x ^ M := by
    have h1 : 0 < max a a' := lt_max_of_lt_left ha
    exact pos_of_mul_pos_right (lt_of_lt_of_le h1 h) hC.le
  have hCy : 0 < C0 * x ^ M := mul_pos hC hy
  have hx' : x ^ (-(2 * M * A)) = (x ^ M) ^ (-(2 * A)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    congr 1
    ring
  have h1 : (C0 * x ^ M) ^ (-A) ≤ a ^ (-A) :=
    Real.rpow_le_rpow_of_nonpos ha (le_trans (le_max_left _ _) h) (by linarith)
  have h2 : (C0 * x ^ M) ^ (-A) ≤ a' ^ (-A) :=
    Real.rpow_le_rpow_of_nonpos ha' (le_trans (le_max_right _ _) h) (by linarith)
  have key : C0 ^ (2 * A) * ((C0 * x ^ M) ^ (-A) * (C0 * x ^ M) ^ (-A)) = (x ^ M) ^ (-(2 * A)) := by
    rw [← Real.rpow_add hCy, Real.mul_rpow hC.le hy.le, ← mul_assoc, ← Real.rpow_add hC]
    have e1 : 2 * A + (-A + -A) = 0 := by ring
    have e2 : -A + -A = -(2 * A) := by ring
    rw [e1, e2, Real.rpow_zero, one_mul]
  rw [hx', ← key]
  exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (Real.rpow_nonneg hCy.le _) (Real.rpow_nonneg ha.le _))
    (Real.rpow_nonneg hC.le _)

theorem orbNormInt_lt_top : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μS μS' : Measure (Mt k r)) (b : ℝ) (C : Set (Mat k r)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsHaarOn (Sset k r z) μS → IsHaarOn (Sset k r z') μS' → 2 * ((2 * (r ^ 2 + r + 1) : ℕ) : ℝ) * (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) < b → IsCompact C → C ⊆ Greg k r z z' → (∀ γ ∈ C, orbNormInt μS μS' b γ < ⊤) ∧ ∃ F : Mt k r × Mt k r → ℝ, Integrable F (μS.prod μS') ∧ ∀ γ ∈ C, ∀ p : Mt k r × Mt k r, Matrix.of p.1 ∈ Sset k r z → Matrix.of p.2 ∈ Sset k r z' → opn (Matrix.of (act2 γ p)) ^ (-b) ≤ F p := by
  intro k r z z' μS μS' b C hz hz' hT hT' hS hS' hb hC hCr
  obtain ⟨C0, hC0, hbd⟩ := GlobalTheory.T.besselRegularDoubleCoset_polynomial_properness k r z z' C hz hz' hT hT' hC hCr
  obtain ⟨-, -, -, hSS, -⟩ := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hz hT
  obtain ⟨-, -, -, hSS', -⟩ := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z' hz' hT'
  set M : ℕ := 2 * (r ^ 2 + r + 1) with hM
  have hM0 : 0 < M := by rw [hM]; positivity
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM0
  have hMpos : (0 : ℝ) < 2 * (M : ℝ) := by linarith
  set A : ℝ := b / (2 * (M : ℝ)) with hA
  have hA2 : 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < A := by
    rw [hA, lt_div_iff₀ hMpos]
    linarith
  have hA0 : 0 ≤ A := le_of_lt (lt_of_le_of_lt (by positivity) hA2)
  have hbA : b = 2 * (M : ℝ) * A := by
    rw [hA]
    field_simp
  have hi := integrable_of_normInt (GlobalTheory.T.besselOpNormPowerIntegral_lt_top_closedSubgroup k r (Sset k r z) μS A hSS hS hA2)
  have hi' := integrable_of_normInt (GlobalTheory.T.besselOpNormPowerIntegral_lt_top_closedSubgroup k r (Sset k r z') μS' A hSS' hS' hA2)
  have : SigmaFinite μS := hS.1
  have : SigmaFinite μS' := hS'.1
  let F : Mt k r × Mt k r → ℝ := fun p =>
    C0 ^ (2 * A) * (opn (Matrix.of p.1) ^ (-A) * opn (Matrix.of p.2) ^ (-A))
  have hF : Integrable F (μS.prod μS') := (hi.mul_prod hi').const_mul _
  have hbound : ∀ γ ∈ C, ∀ p : Mt k r × Mt k r, Matrix.of p.1 ∈ Sset k r z → Matrix.of p.2 ∈ Sset k r z' →
      opn (Matrix.of (act2 γ p)) ^ (-b) ≤ F p := by
    intro γ hγ p h1 h2
    have hg1 := opn_pos (hSS.1 h1)
    have hg2 := opn_pos (hSS'.1 h2)
    have hmax := hbd γ hγ _ h1 _ h2
    rw [hbA]
    exact rpow_le hg1 hg2 (opn_nonneg _) (by linarith) hA0 hmax
  refine ⟨fun γ hγ => ?_, F, hF, hbound⟩
  have e1 : ∀ᵐ p ∂(μS.prod μS'), Matrix.of p.1 ∈ Sset k r z := by
    rw [ae_iff]
    refine measure_mono_null (t := {x : Mt k r | Matrix.of x ∉ Sset k r z} ×ˢ Set.univ)
      (fun p hp => ⟨hp, trivial⟩) ?_
    rw [Measure.prod_prod, hS.2.2.1, zero_mul]
  have e2 : ∀ᵐ p ∂(μS.prod μS'), Matrix.of p.2 ∈ Sset k r z' := by
    rw [ae_iff]
    refine measure_mono_null (t := Set.univ ×ˢ {x : Mt k r | Matrix.of x ∉ Sset k r z'})
      (fun p hp => ⟨trivial, hp⟩) ?_
    rw [Measure.prod_prod, hS'.2.2.1, mul_zero]
  calc orbNormInt μS μS' b γ ≤ ∫⁻ p, ENNReal.ofReal (F p) ∂(μS.prod μS') := by
        unfold orbNormInt
        apply lintegral_mono_ae
        filter_upwards [e1, e2] with p h1 h2
        exact ENNReal.ofReal_le_ofReal (hbound γ hγ p h1 h2)
    _ < ⊤ := hF.lintegral_lt_top

end GlobalTheory.SgInf.OrbNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOrbitOpNormIntegralFiniteOnCompactRegularStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselOrbitOpNormIntegral_finite_on_compact_regular : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μS μS' : Measure (Mt k r)) (b : ℝ) (C : Set (Mat k r)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsHaarOn (Sset k r z) μS → IsHaarOn (Sset k r z') μS' → 2 * ((2 * (r ^ 2 + r + 1) : ℕ) : ℝ) * (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) < b → IsCompact C → C ⊆ Greg k r z z' → (∀ γ ∈ C, orbNormInt μS μS' b γ < ⊤) ∧ ∃ F : Mt k r × Mt k r → ℝ, Integrable F (μS.prod μS') ∧ ∀ γ ∈ C, ∀ p : Mt k r × Mt k r, Matrix.of p.1 ∈ Sset k r z → Matrix.of p.2 ∈ Sset k r z' → opn (Matrix.of (act2 γ p)) ^ (-b) ≤ F p := by
  first | exact @GlobalTheory.SgInf.OrbNorm.orbNormInt_lt_top | exact GlobalTheory.SgInf.OrbNorm.orbNormInt_lt_top | (intros; apply GlobalTheory.SgInf.OrbNorm.orbNormInt_lt_top <;> assumption)
end
