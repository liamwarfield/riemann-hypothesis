module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.VacUnique
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.UnitDetOfUnitary
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.LocOpCont
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocOpMMLaw
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocOpExOfTAll

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.POfAddQOf
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.IsUnitDenominatorBasePoint
noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {m n : ℕ}

open Complex

theorem herm_diag {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℝ), Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      Uᴴ * b * U = Matrix.diagonal fun j => (l j : ℂ) := by
  have hA : b.IsHermitian := hb
  refine ⟨(hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ), hA.eigenvalues, ?_, ?_, ?_⟩
  · rw [← Matrix.star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  · rw [← Matrix.star_eq_conjTranspose]; exact Unitary.coe_mul_star_self _
  · have := hA.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at this
    rw [← Matrix.star_eq_conjTranspose, this]
    rfl

theorem isUnit_denominator_base_point (sg : ℤˣ) (g : GR n) : IsUnit ((mR g).toBlocks₂₁ * Z0 sg + (mR g).toBlocks₂₂).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hG : InG (mR g) := g.2
  have key := inG_dot hG ((Z0 sg *ᵥ x) ⊕ᵥ x)
  have hMv : mR g *ᵥ ((Z0 sg *ᵥ x) ⊕ᵥ x) =
      ((mR g).toBlocks₁₁ *ᵥ (Z0 sg *ᵥ x) + (mR g).toBlocks₁₂ *ᵥ x) ⊕ᵥ 0 := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (mR g)]
    rw [← hx]
    simp only [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.add_mulVec,
      Matrix.mulVec_mulVec]
  have hZx : Z0 sg *ᵥ x = (I * ((sg : ℤ) : ℂ)) • x := by
    rw [Z0, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hMv, dot_JJ, dot_JJ, hZx] at key
  simp at key
  have hs : star x ⬝ᵥ x ≠ 0 := by
    open scoped ComplexOrder in
    exact fun h0 => hx0 (dotProduct_star_self_eq_zero.mp h0)
  have hc : I * ((sg : ℤ) : ℂ) ≠ 0 :=
    mul_ne_zero I_ne_zero (Int.cast_ne_zero.mpr (Units.ne_zero sg))
  have hcs : I * ((sg : ℤ) : ℂ) * (star x ⬝ᵥ x) = 0 := by
    linear_combination key / 2
  exact mul_ne_zero hc hs hcs

theorem mobius_mul_base_point (sg : ℤˣ) (g h : GR n) : mob (mR (g * h)) (Z0 sg) = mob (mR g) (mob (mR h) (Z0 sg)) := by
  rw [mR_mul]; exact mob_mul _ _ _ (isUnit_denominator_base_point sg h)

theorem k_poly {sg : ℤˣ} {L : LOp m n} (h : LocHyp sg L) (k : GR n) (hk : InK (mR k)) (P : PX m n) :
    ∃ Q : PX m n, Q.totalDegree ≤ P.totalDegree ∧ L k (fP P) = fP Q := by
  obtain ⟨a, b, b', t, ha, hb, hb', hk'⟩ := all_eq k
  have hsw := isSw_fP P
  have h0 : IsPG sg P.totalDegree (Z0 sg) (fP P) := ⟨P, le_rfl, fP_eq_gZ sg P⟩
  have hT : ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = (t : ℂ) • 1 := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  have hm1 : IsUnit (-1 : Matrix (Fin n) (Fin n) ℂ).det := isUnit_neg_one_det
  have hsq : ((sg : ℤ) : ℝ) * ((sg : ℤ) : ℝ) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  set w : ℂ := I * ((sg : ℤ) : ℂ) + t with hw
  have hwim : 0 < ((sg : ℤ) : ℝ) * w.im := by
    simp [hw, hsq]
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_im, mul_zero] at hwim
    exact lt_irrefl _ hwim
  set ω : ℂ := (-w)⁻¹ with hω
  have hωim : 0 < ((sg : ℤ) : ℝ) * ω.im := by
    have := im_neg_inv hwim
    rwa [neg_inv] at this
  have h1 := pg_nG h hT hsw h0
  have h2 := pg_mG h hm1 (h.sw _ _ hsw) h1
  have e2 : mob (mR (mG (-1 : Matrix (Fin n) (Fin n) ℂ))) (mob (mR (nG ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))))
      (Z0 sg)) = Matrix.diagonal fun _ : Fin n => w := by
    rw [mR_mG hm1, mR_nG hT, mob_nU, mob_mLc _ _ hm1]
    simp only [Matrix.conjTranspose_neg, Matrix.conjTranspose_one, neg_mul, one_mul, mul_neg, mul_one,
      neg_neg, Z0, hw, ← Matrix.smul_one_eq_diagonal, add_smul]
  rw [e2] at h2
  have h3 := pg_jG_diag h (fun _ => hwim) (h.sw _ _ (h.sw _ _ hsw)) h2
  rw [← e2] at h3
  have e3 : mob (mR (jG n)) (mob (mR (mG (-1 : Matrix (Fin n) (Fin n) ℂ)))
      (mob (mR (nG ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)))) (Z0 sg))) =
      Matrix.diagonal fun _ : Fin n => ω := by
    rw [e2, mR_jG, mob_JJ_diag _ (fun _ => hw0)]
  have h4 := pg_nG h hb' (h.sw _ _ (h.sw _ _ (h.sw _ _ hsw))) h3
  obtain ⟨U, l, hU1, hU2, hUb⟩ := herm_diag hb'
  have eU : Uᴴ * mob (mR (nG b')) (mob (mR (jG n)) (mob (mR (mG (-1 : Matrix (Fin n) (Fin n) ℂ)))
      (mob (mR (nG ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)))) (Z0 sg)))) * U =
      Matrix.diagonal fun j => ω + l j := by
    rw [mR_nG hb', mob_nU, e3, Matrix.mul_add, Matrix.add_mul, hUb, ← Matrix.smul_one_eq_diagonal,
      Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU1, Matrix.smul_one_eq_diagonal,
      Matrix.diagonal_add]
  have hz5 : ∀ j, 0 < ((sg : ℤ) : ℝ) * (ω + l j).im := by
    intro j
    simpa using hωim
  have h5 := pg_jG h hU1 hU2 eU hz5 (h.sw _ _ (h.sw _ _ (h.sw _ _ (h.sw _ _ hsw)))) h4
  have h6 := pg_nG h hb (h.sw _ _ (h.sw _ _ (h.sw _ _ (h.sw _ _ (h.sw _ _ hsw))))) h5
  have h7 := pg_mG h ha (h.sw _ _ (h.sw _ _ (h.sw _ _ (h.sw _ _ (h.sw _ _ (h.sw _ _ hsw)))))) h6
  have hL : L k (fP P) = L (mG a) (L (nG b) (L (jG n) (L (nG b') (L (jG n) (L (mG (-1))
      (L (nG ((t : ℂ) • 1)) (fP P))))))) := by
    rw [hk']
    simp only [mul_assoc]
    rw [h.mul _ _ _ hsw, h.mul _ _ _ hsw, h.mul _ _ _ hsw, h.mul _ _ _ hsw, h.mul _ _ _ hsw,
      h.mul _ _ _ hsw]
  have hZ : mob (mR k) (Z0 sg) = mob (mR (mG a)) (mob (mR (nG b)) (mob (mR (jG n)) (mob (mR (nG b'))
      (mob (mR (jG n)) (mob (mR (mG (-1))) (mob (mR (nG ((t : ℂ) • 1))) (Z0 sg))))))) := by
    rw [hk']
    simp only [mul_assoc]
    rw [mobius_mul_base_point, mobius_mul_base_point, mobius_mul_base_point, mobius_mul_base_point, mobius_mul_base_point, mobius_mul_base_point]
  have hK := mob_K sg (mR k) hk (isUnit_denominator_base_point sg k)
  rw [hZ] at hK
  rw [hK, ← hL] at h7
  obtain ⟨Q, hQ, hfeq⟩ := h7
  exact ⟨Q, hQ, by rw [hfeq, fP_eq_gZ sg Q]⟩

end PositivityTheory.SiegelWeilFormula.KLI

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.LowerLeftBlockLeviUnipotent
noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {m n : ℕ}

variable {sg : ℤˣ} {L : LOp m n}

def nbM (c : Matrix (Fin n) (Fin n) ℂ) : M2 n := Matrix.fromBlocks 1 0 c 1

theorem inG_nbM {c : Matrix (Fin n) (Fin n) ℂ} (hc : cᴴ = c) : InG (nbM c) := by
  unfold InG nbM JJ
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hc]

theorem nbM_inv (c : Matrix (Fin n) (Fin n) ℂ) : (nbM c)⁻¹ = nbM (-c) := by
  apply Matrix.inv_eq_left_inv
  unfold nbM
  rw [Matrix.fromBlocks_multiply]
  simp

theorem nb_eq {c : Matrix (Fin n) (Fin n) ℂ} (hc : cᴴ = c) (hu : IsUnit c.det) :
    toGR (nbM c) (inG_nbM hc) = mG (-c⁻¹) * nG c * jG n * nG c⁻¹ := by
  have hci : (c⁻¹)ᴴ = c⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hc]
  have hnu : IsUnit (-c⁻¹).det := by
    rw [Matrix.det_neg]
    exact ((isUnit_one.neg).pow _).mul (Matrix.isUnit_nonsing_inv_det c hu)
  apply mR_injective
  rw [mR_toGR, mR_mul, mR_mul, mR_mul, mR_mG hnu, mR_nG hc, mR_jG, mR_nG hci]
  have h1 : c⁻¹ * c = 1 := Matrix.nonsing_inv_mul c hu
  have h2 : c * c⁻¹ = 1 := Matrix.mul_nonsing_inv c hu
  have h3 : ((-c⁻¹)ᴴ)⁻¹ = -c := by
    rw [Matrix.conjTranspose_neg, hci]
    exact Matrix.inv_eq_left_inv (by rw [neg_mul_neg, h2])
  unfold nbM mLc nU JJ
  rw [h3]
  simp only [Matrix.fromBlocks_multiply]
  simp [h1, h2, Matrix.neg_mul, Matrix.mul_neg]

def dT (i0 : Fin n) (t : ℝ) : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => if i = i0 then (t : ℂ) else 1

theorem dT_herm (i0 : Fin n) (t : ℝ) : (dT i0 t)ᴴ = dT i0 t := by
  unfold dT
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  by_cases h : i = i0 <;> simp [h]

theorem dT_det (i0 : Fin n) (t : ℝ) : (dT i0 t).det = t := by
  simp [dT, Matrix.det_diagonal]

def pth (i0 : Fin n) (t : ℝ) : GR n :=
  toGR (nbM (-dT i0 t)) (inG_nbM (by rw [Matrix.conjTranspose_neg, dT_herm]))

theorem pth_cont (i0 : Fin n) : Continuous (pth i0) := by
  have hdT : Continuous fun t : ℝ => dT i0 t := by
    unfold dT
    refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
    by_cases h : i = i0
    · simp only [h, if_true]
      exact Complex.continuous_ofReal
    · simp only [h, if_false]
      exact continuous_const
  have hnb : ∀ f : ℝ → Matrix (Fin n) (Fin n) ℂ, Continuous f → Continuous fun t => nbM (f t) := by
    intro f hf
    unfold nbM
    exact continuous_const.matrix_fromBlocks continuous_const hf continuous_const
  unfold pth toGR
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · show Continuous fun t => nbM (-dT i0 t)
    exact hnb _ hdT.neg
  · show Continuous fun t => (nbM (-dT i0 t))⁻¹
    simp only [nbM_inv, neg_neg]
    exact hnb _ hdT

theorem weight_factor_ne_zero (p q : ℕ) (e : ℤ) (g : GR n) : F0 p q e g ≠ 0 := by
  unfold F0 f0
  have h1 : Matrix.det (mR g) ≠ 0 := (det_ne_of_inG (M := mR g) g.2).ne_zero
  exact mul_ne_zero (zpow_ne_zero _ h1)
    (mul_ne_zero (zpow_ne_zero _ (automorphy_first_det_ne_zero g)) (zpow_ne_zero _ (automorphy_second_det_ne_zero g)))

theorem pq_sum (sg : ℤˣ) (m : ℕ) : ((pOf sg m : ℕ) : ℤ) + (qOf sg m : ℕ) = m := by
  unfold pOf qOf
  split_ifs <;> simp

theorem lower_left_block_levi_unipotent (a b : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) (hb : bᴴ = b) :
    (mR (mG a * nG b)).toBlocks₂₁ = 0 := by
  rw [mR_mul, mR_mG ha, mR_nG hb, lower_left_block_mul]
  simp [mLc, nU]

theorem S_law (h : LocHyp sg L) {k : ℤ}
    (hk : ∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → mR y = mLc a → ∀ f, IsSw f →
      L y f = fun u => (a.det / (‖a.det‖ : ℂ)) ^ k * (‖a.det‖ : ℂ) ^ m * f (Matrix.of u * a))
    (a b : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) (hb : bᴴ = b) (g : GR n) :
    L (mG a * nG b * g) (fP 1) 0 = (a.det / (‖a.det‖ : ℂ)) ^ k * (‖a.det‖ : ℂ) ^ m * L g (fP 1) 0 := by
  have hf := isSw_fP (1 : PX m n)
  have hz : ∀ F : (Fin m → Fin n → ℂ) → ℂ, F (Matrix.of (0 : Fin m → Fin n → ℂ) * a) = F 0 := by
    intro F
    congr 1
    exact Matrix.zero_mul a
  have e2 : L (nG b * g) (fP 1) (Matrix.of (0 : Fin m → Fin n → ℂ) * a) = L g (fP 1) 0 := by
    refine (hz _).trans ?_
    rw [h.mul _ _ _ hf, h.nU (nG b) b hb (mR_nG hb) _ (h.sw _ _ hf)]
    simp
  have e1 := congrFun (hk (mG a) a ha (mR_mG ha) _ (h.sw (nG b * g) _ hf)) 0
  rw [mul_assoc, h.mul _ _ _ hf, e1]
  show _ * _ * L (nG b * g) (fP 1) (Matrix.of (0 : Fin m → Fin n → ℂ) * a) = _
  rw [e2]

theorem S_cell (h : LocHyp sg L) {C : ℂ}
    (hJ : ∀ y : GR n, mR y = JJ n → ∀ f, IsSw f → L y f 0 = C * ∫ v, f v)
    (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) :
    L (jG n * nG b) (fP (1 : PX m n)) 0 =
      C * secN (fun _ : Fin m => true) (2 * Real.pi) (2 * Real.pi * ((sg : ℤ) : ℝ)) (1 : PX m n) b := by
  have hf := isSw_fP (1 : PX m n)
  rw [h.mul _ _ _ hf, hJ (jG n) mR_jG _ (h.sw _ _ hf), h.nU (nG b) b hb (mR_nG hb) _ hf]
  unfold secN fP
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only
  rw [gramX_true]
  have e : Complex.I * ((2 * Real.pi * (((sg : ℤ) : ℝ)) : ℝ) : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I * (((sg : ℤ) : ℂ)) := by
    push_cast
    ring
  rw [e]
  ring

theorem even_im_hermitian_sub (h : LocHyp sg L) (hn : 0 < n) {k : ℤ}
    (hk : ∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → mR y = mLc a → ∀ f, IsSw f →
      L y f = fun u => (a.det / (‖a.det‖ : ℂ)) ^ k * (‖a.det‖ : ℂ) ^ m * f (Matrix.of u * a)) :
    Even (k - m) := by
  obtain i0 : Fin n := ⟨0, hn⟩
  obtain ⟨C, hC0, hJ⟩ := h.longWeylFunctional
  obtain ⟨κ, hκ0, hκ⟩ := gauss_cell (m := m) (n := n) sg 0
  have key : ∀ t : ℝ, t ≠ 0 →
      L (pth i0 t) (fP 1) 0 * κ * star ((t : ℂ)⁻¹) ^ (m : ℤ) =
        F0 (pOf sg m) (qOf sg m) 0 (pth i0 t) * C *
          (((t : ℂ)⁻¹ / (‖(t : ℂ)⁻¹‖ : ℂ)) ^ k * (‖(t : ℂ)⁻¹‖ : ℂ) ^ m) := by
    intro t ht
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    have hc : (-dT i0 t)ᴴ = -dT i0 t := by rw [Matrix.conjTranspose_neg, dT_herm]
    have hdc : (-dT i0 t).det = (-1) ^ n * (t : ℂ) := by
      rw [Matrix.det_neg, dT_det, Fintype.card_fin]
    have hu : IsUnit (-dT i0 t).det := by
      rw [hdc]
      exact isUnit_iff_ne_zero.2 (mul_ne_zero (pow_ne_zero _ (by norm_num)) ht')
    have hci : ((-dT i0 t)⁻¹)ᴴ = (-dT i0 t)⁻¹ := by
      rw [Matrix.conjTranspose_nonsing_inv, hc]
    have hd : (-(-dT i0 t)⁻¹).det = (t : ℂ)⁻¹ := by
      rw [Matrix.det_neg, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hdc, Fintype.card_fin,
        mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (by norm_num)), one_mul]
    have hnu : IsUnit (-(-dT i0 t)⁻¹).det := by
      rw [hd]
      exact isUnit_iff_ne_zero.2 (inv_ne_zero ht')
    have hp : pth i0 t = mG (-(-dT i0 t)⁻¹) * nG (-dT i0 t) * jG n * nG (-dT i0 t)⁻¹ :=
      nb_eq hc hu
    rw [hp, mul_assoc (mG _ * nG _) (jG n) _, S_law h hk _ _ hnu hc, S_cell h hJ _ hci,
      weight_factor_mul_parabolic _ _ _ _ _ (lower_left_block_levi_unipotent _ _ hnu hc), weight_factor_levi_unipotent _ _ _ _ _ hnu hc, hκ _ hci, hd, pq_sum]
    simp only [zpow_zero, one_mul, sub_zero]
    ring
  have hpos : ∀ t : ℝ, 0 < t →
      L (pth i0 t) (fP 1) 0 * κ = F0 (pOf sg m) (qOf sg m) 0 (pth i0 t) * C := by
    intro t ht
    have e := key t ht.ne'
    have hr : ((t : ℂ))⁻¹ = ((t⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    have hr0 : ((t⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast inv_ne_zero ht.ne'
    rw [hr, Complex.star_def, Complex.conj_ofReal, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.2 ht.le), div_self hr0, one_zpow, one_mul, zpow_natCast] at e
    apply mul_right_cancel₀ (pow_ne_zero m hr0)
    rw [e]
  have hneg : ∀ t : ℝ, t < 0 →
      L (pth i0 t) (fP 1) 0 * κ = (-1) ^ k * (-1) ^ m * (F0 (pOf sg m) (qOf sg m) 0 (pth i0 t) * C) := by
    intro t ht
    have e := key t ht.ne
    have hr : ((t : ℂ))⁻¹ = ((t⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    have hr0 : ((t⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast inv_ne_zero ht.ne
    rw [hr, Complex.star_def, Complex.conj_ofReal, Complex.norm_real,
      Real.norm_of_nonpos (inv_nonpos.2 ht.le), Complex.ofReal_neg, div_neg, div_self hr0,
      neg_pow, zpow_natCast] at e
    apply mul_right_cancel₀ (pow_ne_zero m hr0)
    rw [e]
    ring
  have hφ : Continuous fun t : ℝ => L (pth i0 t) (fP 1) 0 * κ :=
    ((h.cont 1 0).comp (pth_cont i0)).mul continuous_const
  have hψ : Continuous fun t : ℝ => F0 (pOf sg m) (qOf sg m) 0 (pth i0 t) * C :=
    ((continuous_weight_factor_unitary _ _ _).comp (pth_cont i0)).mul continuous_const
  have hs : Filter.Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hs' : Filter.Tendsto (fun j : ℕ => -(1 / ((j : ℝ) + 1))) Filter.atTop (nhds 0) := by
    simpa using hs.neg
  have hpos' : ∀ j : ℕ, (0 : ℝ) < 1 / ((j : ℝ) + 1) := fun j => by positivity
  have e1 : L (pth i0 0) (fP 1) 0 * κ = F0 (pOf sg m) (qOf sg m) 0 (pth i0 0) * C := by
    have A := (hφ.tendsto 0).comp hs
    have B := (hψ.tendsto 0).comp hs
    refine tendsto_nhds_unique A ?_
    refine B.congr (fun j => ?_)
    exact (hpos _ (hpos' j)).symm
  have e2 : L (pth i0 0) (fP 1) 0 * κ =
      (-1) ^ k * (-1) ^ m * (F0 (pOf sg m) (qOf sg m) 0 (pth i0 0) * C) := by
    have A := (hφ.tendsto 0).comp hs'
    have B := ((hψ.tendsto 0).comp hs').const_mul ((-1 : ℂ) ^ k * (-1) ^ m)
    refine tendsto_nhds_unique A ?_
    refine B.congr (fun j => ?_)
    exact (hneg _ (neg_neg_of_pos (hpos' j))).symm
  have hψ0 : F0 (pOf sg m) (qOf sg m) 0 (pth i0 0) * C ≠ 0 := mul_ne_zero (weight_factor_ne_zero _ _ _ _) hC0
  have hε : ((-1 : ℂ)) ^ k * (-1) ^ m = 1 := by
    rw [e1] at e2
    have := mul_right_cancel₀ hψ0 (e2.symm.trans (one_mul _).symm)
    exact this
  rcases Int.even_or_odd (k - m) with he | ho
  · exact he
  · exfalso
    have h1 : ((-1 : ℂ)) ^ (k - m) = -1 := ho.neg_one_zpow
    have h2 : ((-1 : ℂ)) ^ k = (-1) ^ (k - m) * (-1) ^ m := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
      congr 1
      ring
    rw [h2, h1] at hε
    have h3 : ((-1 : ℂ)) ^ m * (-1) ^ m = 1 := by
      rw [← mul_pow]
      norm_num
    have : (-1 : ℂ) = 1 := by linear_combination hε + h3
    norm_num at this

theorem LocHyp.mM' (h : LocHyp sg L) : ∃ e : ℤ, ∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det →
    mR y = mLc a → ∀ f, IsSw f → L y f = fun u => a.det ^ e * (star a.det) ^ ((m : ℤ) - e) * f (Matrix.of u * a) := by
  obtain ⟨k, hk⟩ := h.mM
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    refine ⟨0, fun y a ha hy f hf => ?_⟩
    rw [hk y a ha hy f hf]
    simp [Matrix.det_isEmpty]
  · obtain ⟨j, hj⟩ := even_im_hermitian_sub h hn hk
    refine ⟨m + j, fun y a ha hy f hf => ?_⟩
    rw [hk y a ha hy f hf]
    funext u
    congr 1
    have hz : a.det ≠ 0 := ha.ne_zero
    have hr : (‖a.det‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
    have hs : star a.det = (‖a.det‖ : ℂ) * (‖a.det‖ : ℂ) * (a.det)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hz, mul_comm, Complex.star_def, Complex.mul_conj,
        Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [hs, show k = (m : ℤ) + (j + j) by omega, show (m : ℤ) - (m + j) = -j by ring]
    have hzj := zpow_ne_zero j hz
    have hrj := zpow_ne_zero j hr
    rw [div_zpow, zpow_add₀ hz, zpow_add₀ hz, zpow_add₀ hr, zpow_add₀ hr, zpow_add₀ hz,
      zpow_natCast, zpow_natCast, zpow_neg, mul_zpow, mul_zpow, inv_zpow]
    field_simp

end PositivityTheory.SiegelWeilFormula.KLI

end
end

noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {m n : ℕ}

variable {sg : ℤˣ} {L : LOp m n}

theorem L_fP_lin (h : LocHyp sg L) (y : GR n) (a : ℂ) (P Q : PX m n) :
    L y (fP (a • P + Q)) = a • L y (fP P) + L y (fP Q) := by
  rw [fP_add_smul]
  exact h.lin y a _ _ (isSw_fP P) (isSw_fP Q)

theorem L_fP_zero (h : LocHyp sg L) (y : GR n) : L y (fP (0 : PX m n)) = 0 := by
  have e := L_fP_lin h y 1 0 0
  simp only [one_smul, add_zero] at e
  have : L y (fP (0 : PX m n)) + L y (fP 0) - L y (fP 0) = L y (fP 0) := by abel
  rw [← e] at this
  simpa using this.symm

def sLOf (h : LocHyp sg L) : PX m n →ₗ[ℂ] (GR n → ℂ) where
  toFun P y := L y (fP P) 0
  map_add' P Q := by
    funext y
    have e := L_fP_lin h y 1 P Q
    simp only [one_smul] at e
    simp [e]
  map_smul' a P := by
    funext y
    have e := L_fP_lin h y a P 0
    simp only [add_zero, L_fP_zero h] at e
    simp [e]


open scoped Classical in
def rhoFun (h : LocHyp sg L) (k : GR n) (P : PX m n) : PX m n :=
  if hk : InK (mR k) then Classical.choose (k_poly h k hk P) else 0

open scoped Classical in
theorem rhoFun_spec (h : LocHyp sg L) {k : GR n} (hk : InK (mR k)) (P : PX m n) :
    (rhoFun h k P).totalDegree ≤ P.totalDegree ∧ L k (fP P) = fP (rhoFun h k P) := by
  simp only [rhoFun, dif_pos hk]
  exact Classical.choose_spec (k_poly h k hk P)


open scoped Classical in
def rhoOf (h : LocHyp sg L) (k : GR n) : PX m n →ₗ[ℂ] PX m n where
  toFun := rhoFun h k
  map_add' P Q := by
    by_cases hk : InK (mR k)
    · apply fP_injective
      rw [← (rhoFun_spec h hk _).2]
      have e := L_fP_lin h k 1 P Q
      simp only [one_smul] at e
      rw [e, (rhoFun_spec h hk P).2, (rhoFun_spec h hk Q).2]
      have e2 := fP_add_smul (1 : ℂ) (rhoFun h k P) (rhoFun h k Q)
      simp only [one_smul] at e2
      rw [e2]
    · simp [rhoFun, dif_neg hk]
  map_smul' a P := by
    by_cases hk : InK (mR k)
    · apply fP_injective
      rw [← (rhoFun_spec h hk _).2]
      have e := L_fP_lin h k a P 0
      simp only [add_zero, L_fP_zero h] at e
      rw [e, (rhoFun_spec h hk P).2]
      have e2 := fP_add_smul a (rhoFun h k P) 0
      simp only [add_zero, fP_zero] at e2
      simp [e2]
    · simp [rhoFun, dif_neg hk]

theorem cnt_true : cnt (fun _ : Fin m => true) true = m := by
  simp [cnt]

theorem cnt_false : cnt (fun _ : Fin m => true) false = 0 := by
  simp [cnt]

theorem pOf_add_qOf (sg : ℤˣ) (m : ℕ) : ((pOf sg m : ℕ) : ℤ) + (qOf sg m : ℕ) = m := by
  unfold pOf qOf
  split_ifs <;> simp

theorem locData_of (h : LocHyp sg L) :
    ∃ (sL : PX m n →ₗ[ℂ] (GR n → ℂ)) (ρ : GR n → PX m n →ₗ[ℂ] PX m n) (e : ℤ),
      LocData (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((sg : ℤ) : ℝ)) (pOf sg m) (qOf sg m) e sL ρ ∧
      (∀ P y, sL P y = L y (fP P) 0) ∧ ∀ (k : GR n) P, InK (mR k) → L k (fP P) = fP (ρ k P) := by
  obtain ⟨e, he⟩ := h.mM'
  obtain ⟨C, hC, hJ⟩ := h.longWeylFunctional

  have hlaw : ∀ (P : PX m n) (y g : GR n), (mR y).toBlocks₂₁ = 0 →
      sLOf h P (y * g) = F0 (pOf sg m) (qOf sg m) e y * sLOf h P g := by
    intro P y g hy
    obtain ⟨a, b, ha, hb, rfl⟩ := par_eq y hy
    have hg := h.sw g _ (isSw_fP P)
    show L (mG a * nG b * g) (fP P) 0 = _ * L g (fP P) 0
    rw [h.mul _ _ _ (isSw_fP P), h.mul _ _ _ hg, he (mG a) a ha (mR_mG ha) _ (h.sw _ _ hg),
      h.nU (nG b) b hb (mR_nG hb) _ hg, weight_factor_levi_unipotent _ _ _ a b ha hb, pOf_add_qOf]
    have key : ∀ X : Fin m → Fin n → ℂ, X = 0 → Complex.exp (2 * Real.pi * Complex.I * ((sg : ℤ) : ℂ) *
        (b * ((Matrix.of X)ᴴ * Matrix.of X)).trace) * L g (fP P) X = L g (fP P) 0 := by
      rintro X rfl
      rw [show Matrix.of (0 : Fin m → Fin n → ℂ) = 0 from rfl]
      simp
    simp only []
    rw [key _ (by funext i j; exact congrFun (congrFun (Matrix.zero_mul a) i) j)]

  have hcell : ∀ (P : PX m n) (b : Matrix (Fin n) (Fin n) ℂ), bᴴ = b →
      sLOf h P (jG n * nG b) = C * secN (fun _ : Fin m => true) (2 * Real.pi) (2 * Real.pi * ((sg : ℤ) : ℝ)) P b := by
    intro P b hb
    show L (jG n * nG b) (fP P) 0 = _
    rw [h.mul _ _ _ (isSw_fP P), hJ (jG n) mR_jG _ (h.sw _ _ (isSw_fP P)), h.nU (nG b) b hb (mR_nG hb) _ (isSw_fP P)]
    simp only [secN, gramX_true, fP]
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    push_cast
    ring_nf
  have hvac : ∀ g, sLOf h 1 g = F0 (pOf sg m) (qOf sg m) e g := by
    refine vac_unique sg e (sLOf h 1) C (h.cont 1 0) ?_ (hlaw 1) (hcell 1)
    show L 1 (fP 1) 0 = 1
    rw [h.one _ (isSw_fP 1), fP_one_zero]
  refine ⟨sLOf h, rhoOf h, e, ?_, fun P y => rfl, fun k P hk => (rhoFun_spec h hk P).2⟩
  refine
    { cpos := by positivity
      sign := ?_
      cont := fun P => h.cont P 0
      vac := hvac
      law := hlaw
      cell := ⟨C, hC, fun P g b hb hg => by rw [eq_jn g b hb hg]; exact hcell P b hb⟩
      kact := ?_
      kvac := ?_
      kfin := ?_ }
  · rcases Int.units_eq_one_or sg with rfl | rfl
    · left; simp [pOf, qOf, cnt_true, cnt_false]
    · right; simp [pOf, qOf, cnt_true, cnt_false]
  · intro P g k hk
    show L (g * k) (fP P) 0 = L g (fP (rhoFun h k P)) 0
    rw [h.mul _ _ _ (isSw_fP P), (rhoFun_spec h hk P).2]
  · intro k hk
    have hd := (rhoFun_spec h hk 1).1
    rw [MvPolynomial.totalDegree_one, Nat.le_zero, MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hd
    have h1 : sLOf h (rhoOf h k 1) 1 = sLOf h 1 (1 * k) := by
      show L 1 (fP (rhoFun h k 1)) 0 = L (1 * k) (fP 1) 0
      rw [h.mul _ _ _ (isSw_fP 1), ← (rhoFun_spec h hk 1).2]
    change sLOf h (rhoFun h k 1) 1 = _ at h1
    set c := AddMonoidAlgebra.coeff (rhoFun h k 1) 0 with hcdef
    have hc : (MvPolynomial.C c : PX m n) = c • (1 : PX m n) := by rw [MvPolynomial.smul_eq_C_mul, mul_one]
    rw [hd, hc, map_smul, Pi.smul_apply, one_mul, hvac, weight_factor_one, smul_eq_mul, mul_one] at h1
    show rhoFun h k 1 = _
    rw [hd, hc, h1, hvac]
  · intro P
    refine ⟨MvPolynomial.restrictTotalDegree _ ℂ P.totalDegree, fin_deg _,
      (MvPolynomial.mem_restrictTotalDegree _ _ _).2 le_rfl, ?_, ?_⟩
    · intro k hk Q hQ
      rw [MvPolynomial.mem_restrictTotalDegree] at hQ ⊢
      exact ((rhoFun_spec h hk Q).1).trans hQ
    · intro Q hQ l'
      rw [MvPolynomial.mem_restrictTotalDegree] at hQ
      refine continuousOn_of_evX P.totalDegree (fun k => rhoOf h k Q)
        (fun k hk => ((rhoFun_spec h hk Q).1).trans hQ) (fun u => ?_) l'
      have hcts : ContinuousOn (fun k => L k (fP Q) u / gs (2 * Real.pi) u) {k | InK (mR k)} :=
        ((h.cont Q u).div_const _).continuousOn
      refine hcts.congr (fun k hk => ?_)
      show evX (rhoFun h k Q) u = L k (fP Q) u / gs (2 * Real.pi) u
      rw [(rhoFun_spec h hk Q).2, fP, mul_div_assoc, div_self (show gs (2 * Real.pi) u ≠ 0 from Complex.exp_ne_zero _), mul_one]

end PositivityTheory.SiegelWeilFormula.KLI

end
end

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem goodSig_pq {n m : ℕ} (sg : ℤˣ) (h : n ≤ m) : GoodSig n (pOf sg m) (qOf sg m) := by
  unfold pOf qOf GoodSig
  split_ifs
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))

theorem locHyp_of (hT : TAll) (hA : AuxiliaryPrimeFunction) {d : SD σ} (R : RD d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ} (hL : R.IsLocOp w L) :
    LocHyp (R.sg w) L := by
  have hG : GoodAwayEx := KFock.goodAwayEx
  refine
    { sw := fun y f hf => (hL y f hf).1
      one := R.locOp_one hT hG hL
      mul := R.locOp_mul hT hG hL
      lin := R.locOp_lin hT hG hL
      nU := R.locOp_nU hT hG hL
      mM := ?_
      nbar := ?_
      longWeylFunctional := R.localOperator_longWeyl_integral hT hA hG hL
      cont := locOp_cont hT R hL }
  · obtain ⟨k, hk⟩ := R.locOp_mM_law w hT hG hL
    exact ⟨k, fun y a ha hy f hf => hk y a ha hy f hf⟩
  · obtain ⟨C, s, κ, ε, hs, hκ, h4, hf, -, hs2, hη⟩ := R.locOp_nbar hT hA hG hL
    exact ⟨C, s, κ, ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹, hs, hκ, hs2, hη, h4, fun y c hc hy f hf' => hf y c hc hy f hf'⟩

theorem locInst_of (hT : TAll) (hA : AuxiliaryPrimeFunction) (_hF : FockMem) (_hLi : LiftEx) : LocInst := by
  intro F E _ _ _ _ _ σ d R w L hL
  obtain ⟨sL, ρ, e, hD, h1, h2⟩ := locData_of (locHyp_of hT hA R hL)
  exact ⟨sL, ρ, pOf (R.sg w) d.m, qOf (R.sg w) d.m, e, fun hnm => goodSig_pq _ hnm, hD, h1, h2⟩

end PositivityTheory.SiegelWeilFormula.KLI

end
