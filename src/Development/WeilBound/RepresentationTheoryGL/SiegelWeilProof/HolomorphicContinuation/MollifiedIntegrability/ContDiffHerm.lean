module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Lagr

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.RatBound
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GBFinal
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem herm_isHermitian (y : E n) : (herm y).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, herm, star_add, star_div₀, star_mul', Complex.star_def, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat]
  push_cast
  ring

theorem cls_zero (s : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) :
    cls s 0 p q R = fun y => Fr s p q R (herm y) := by
  funext y
  simp [cls, Fr, evUV, uM, vM]

theorem herm_spectral (y : E n) : ∃ k ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ lam : Fin n → ℝ,
    herm y = k * Matrix.diagonal (fun i => (lam i : ℂ)) * kᴴ := by
  have hH := herm_isHermitian y
  refine ⟨hH.eigenvectorUnitary, hH.eigenvectorUnitary.2, hH.eigenvalues, ?_⟩
  conv_lhs => rw [hH.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  rfl

theorem conj_det (k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (A : Mc n) : (k * A * kᴴ).det = A.det := by
  have h1 : k * kᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff.1 hk); simpa [Matrix.star_eq_conjTranspose] using this
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm (k.det), mul_assoc, ← Matrix.det_mul, h1, Matrix.det_one, mul_one]

theorem one_sub_conj (k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (c : ℂ) (A : Mc n) :
    (1 : Mc n) + c • (k * A * kᴴ) = k * (1 + c • A) * kᴴ := by
  have h1 : k * kᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff.1 hk); simpa [Matrix.star_eq_conjTranspose] using this
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1, Matrix.mul_smul, Matrix.smul_mul]

theorem det_one_add_herm (y : E n) : ∃ lam : Fin n → ℝ, ∀ c : ℂ,
    ((1 : Mc n) + c • herm y).det = ∏ i, (1 + c * lam i) ∧ ((1 : Mc n) + herm y * herm y).det = ∏ i, (1 + (lam i : ℂ) ^ 2) := by
  obtain ⟨k, hk, lam, hy⟩ := herm_spectral y
  have h1 : kᴴ * k = 1 := by
    have := (Matrix.mem_unitaryGroup_iff'.1 hk); simpa [Matrix.star_eq_conjTranspose] using this
  refine ⟨lam, fun c => ⟨?_, ?_⟩⟩
  · rw [hy, one_sub_conj k hk, conj_det k hk]
    rw [show (1 : Mc n) + c • Matrix.diagonal (fun i => (lam i : ℂ)) = Matrix.diagonal (fun i => 1 + c * lam i) by
      ext i j; by_cases h : i = j <;> simp [Matrix.diagonal, h]]
    simp
  · have : herm y * herm y = k * (Matrix.diagonal (fun i => (lam i : ℂ)) * Matrix.diagonal (fun i => (lam i : ℂ))) * kᴴ := by
      rw [hy]
      calc k * diagonal (fun i => (lam i : ℂ)) * kᴴ * (k * diagonal (fun i => (lam i : ℂ)) * kᴴ)
          = k * diagonal (fun i => (lam i : ℂ)) * (kᴴ * k) * diagonal (fun i => (lam i : ℂ)) * kᴴ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [this, show (1 : Mc n) + k * (diagonal (fun i => (lam i : ℂ)) * diagonal (fun i => (lam i : ℂ))) * kᴴ =
        (1 : Mc n) + (1 : ℂ) • (k * (diagonal (fun i => (lam i : ℂ)) * diagonal (fun i => (lam i : ℂ))) * kᴴ) by simp,
      one_sub_conj k hk, conj_det k hk, Matrix.diagonal_mul_diagonal]
    rw [show (1 : Mc n) + (1 : ℂ) • diagonal (fun i => (lam i : ℂ) * lam i) = diagonal (fun i => 1 + (lam i : ℂ) ^ 2) by
      ext i j; by_cases h : i = j <;> simp [Matrix.diagonal, h, sq]]
    simp

theorem dP_eq (y : E n) : ∃ lam : Fin n → ℝ, dP y = ∏ i, (1 + lam i ^ 2) ∧
    (((dP y : ℝ) : ℂ) = ((1 : Mc n) + herm y * herm y).det) ∧
    ∀ c : ℂ, ((1 : Mc n) + c • herm y).det = ∏ i, (1 + c * lam i) := by
  obtain ⟨lam, h⟩ := det_one_add_herm y
  have h2 := (h 0).2
  have hre : dP y = ∏ i, (1 + lam i ^ 2) := by
    simp only [dP, h2]
    rw [show (∏ i, (1 + (lam i : ℂ) ^ 2)) = ((∏ i, (1 + lam i ^ 2) : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]
  refine ⟨lam, hre, ?_, fun c => (h c).1⟩
  rw [hre, h2]; push_cast; rfl

theorem dP_pos (y : E n) : 0 < dP y := by
  obtain ⟨lam, h, -⟩ := dP_eq y
  rw [h]; exact Finset.prod_pos fun i _ => by positivity

theorem herm_mem_Ugood (s : ℂ) (hs : s = 1 ∨ s = -1) (y : E n) : herm y ∈ Ugood s := by
  obtain ⟨lam, -, -, h⟩ := dP_eq y
  have key : ∀ c : ℂ, (c = 1 ∨ c = -1) → ((1 : Mc n) + (c * (Complex.I * s)) • herm y).det ≠ 0 := by
    intro c hc
    rw [h, Finset.prod_ne_zero_iff]
    intro i _ h0
    have h1 := congrArg Complex.re h0
    rcases hc with rfl | rfl <;> rcases hs with rfl | rfl <;> simp at h1
  refine ⟨isUnit_iff_ne_zero.2 ?_, isUnit_iff_ne_zero.2 ?_⟩
  · have := key (-1) (Or.inr rfl); rwa [neg_one_mul, neg_smul, ← sub_eq_add_neg] at this
  · have := key 1 (Or.inl rfl); rwa [one_mul] at this

theorem dP_of_spectral (y : E n) (k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (lam : Fin n → ℝ)
    (hy : herm y = k * Matrix.diagonal (fun i => (lam i : ℂ)) * kᴴ) : dP y = ∏ i, (1 + lam i ^ 2) := by
  have h1 : kᴴ * k = 1 := by
    have := (Matrix.mem_unitaryGroup_iff'.1 hk); simpa [Matrix.star_eq_conjTranspose] using this
  have : herm y * herm y = k * (Matrix.diagonal (fun i => (lam i : ℂ)) * Matrix.diagonal (fun i => (lam i : ℂ))) * kᴴ := by
    rw [hy]
    calc k * diagonal (fun i => (lam i : ℂ)) * kᴴ * (k * diagonal (fun i => (lam i : ℂ)) * kᴴ)
        = k * diagonal (fun i => (lam i : ℂ)) * (kᴴ * k) * diagonal (fun i => (lam i : ℂ)) * kᴴ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have h2 : ((1 : Mc n) + herm y * herm y).det = ((∏ i, (1 + lam i ^ 2) : ℝ) : ℂ) := by
    rw [this, show (1 : Mc n) + k * (diagonal (fun i => (lam i : ℂ)) * diagonal (fun i => (lam i : ℂ))) * kᴴ =
        (1 : Mc n) + (1 : ℂ) • (k * (diagonal (fun i => (lam i : ℂ)) * diagonal (fun i => (lam i : ℂ))) * kᴴ) by simp,
      one_sub_conj k hk, conj_det k hk, Matrix.diagonal_mul_diagonal]
    rw [show (1 : Mc n) + (1 : ℂ) • diagonal (fun i => (lam i : ℂ) * lam i) = diagonal (fun i => 1 + (lam i : ℂ) ^ 2) by
      ext i j; by_cases h : i = j <;> simp [Matrix.diagonal, h, sq]]
    simp
  simp only [dP, h2, Complex.ofReal_re]

theorem det_u_mul_det_v (s : ℂ) (hs : s = 1 ∨ s = -1) (y : E n) :
    (uM s y).det * (vM s y).det = (((dP y : ℝ) : ℂ))⁻¹ := by
  obtain ⟨lam, -, hdP, -⟩ := dP_eq y
  have hg := herm_mem_Ugood s hs y
  have hprod : ((1 : Mc n) - (Complex.I * s) • herm y) * (1 + (Complex.I * s) • herm y) = 1 + herm y * herm y := by
    have hs2 : (Complex.I * s) * (Complex.I * s) = -1 := by
      rcases hs with rfl | rfl <;> simp [← sq, Complex.I_sq] <;> ring_nf <;> simp [Complex.I_sq]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs2]
    simp [neg_smul]; abel
  have h1 := Matrix.det_nonsing_inv_mul_det (A := (1 : Mc n) - (Complex.I * s) • herm y) hg.1
  have h2 := Matrix.det_nonsing_inv_mul_det (A := (1 : Mc n) + (Complex.I * s) • herm y) hg.2
  rw [hdP, ← hprod, Matrix.det_mul]
  simp only [uM, vM]
  apply eq_inv_of_mul_eq_one_left
  calc ((1 - (Complex.I * s) • herm y)⁻¹).det * ((1 + (Complex.I * s) • herm y)⁻¹).det *
        ((1 - (Complex.I * s) • herm y).det * (1 + (Complex.I * s) • herm y).det)
      = (((1 - (Complex.I * s) • herm y)⁻¹).det * (1 - (Complex.I * s) • herm y).det) *
        (((1 + (Complex.I * s) • herm y)⁻¹).det * (1 + (Complex.I * s) • herm y).det) := by ring
    _ = 1 := by rw [h1, h2, one_mul]

theorem cls_nat (s : ℂ) (hs : s = 1 ∨ s = -1) (i p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) :
    cls s (i : ℂ) p q R = cls s 0 (p + i) (q + i) R := by
  funext y
  have h := det_u_mul_det_v s hs y
  simp only [cls, neg_zero, Complex.cpow_zero, one_mul, Complex.cpow_neg, Complex.cpow_natCast, pow_add]
  rw [show ((((dP y : ℝ) : ℂ)) ^ i)⁻¹ = ((uM s y).det * (vM s y).det) ^ i by rw [h, inv_pow]]
  ring

theorem prod_flatMap_real {α : Type} (l : List α) (f : α → List ℝ) :
    (l.flatMap f).prod = (l.map fun a => (f a).prod).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.prod_append, ih]

theorem prod_blocks (N : ℕ) (g : Fin N → Fin n → ℝ) :
    ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => g j k).prod = ∏ j, ∏ k, g j k := by
  rw [prod_flatMap_real, Fin.prod_univ_def]
  congr 1

theorem length_blocks {α : Type} (N : ℕ) (g : Fin N → Fin n → α) :
    ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => g j k).length = N * n := by
  simp

theorem prod_sqrt_perm (σ : Equiv.Perm (Fin n)) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    ∏ k, Real.sqrt (w (σ k) * w k) = ∏ k, w k := by
  have h1 : ∀ k, Real.sqrt (w (σ k) * w k) = Real.sqrt (w (σ k)) * Real.sqrt (w k) := fun k =>
    Real.sqrt_mul (hw _).le _
  simp_rw [h1, Finset.prod_mul_distrib, Equiv.prod_comp σ (fun k => Real.sqrt (w k)), ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => Real.mul_self_sqrt (hw k).le

theorem conj_mem_Ugood (s : ℂ) (k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (b : Mc n) (hb : b ∈ Ugood s) :
    k * b * kᴴ ∈ Ugood s := by
  refine ⟨?_, ?_⟩
  · rw [sub_eq_add_neg, ← neg_smul, one_sub_conj k hk, conj_det k hk, neg_smul, ← sub_eq_add_neg]; exact hb.1
  · rw [one_sub_conj k hk, conj_det k hk]; exact hb.2

def conjL (k : Mc n) : Mc n →ₗ[ℂ] Mc n := (LinearMap.mulLeft ℂ k).comp (LinearMap.mulRight ℂ kᴴ)

theorem conjL_apply (k c : Mc n) : conjL k c = k * c * kᴴ := by
  simp [conjL, Matrix.mul_assoc]

theorem contDiff_conj (k : Mc n) : ContDiff ℂ (⊤ : ℕ∞) (fun c : Mc n => k * c * kᴴ) := by
  have : (fun c : Mc n => k * c * kᴴ) = (LinearMap.toContinuousLinearMap (conjL k) : Mc n → Mc n) := by
    funext c; simp [conjL_apply]
  rw [this]; exact ContinuousLinearMap.contDiff _

end PositivityTheory.Rg.Sw.WR.K.GB
end
end

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem ratBound (hC : CauchyW) (hI : Invar) (hB : PBound) (hL : Link) (s : ℂ) (hs : s = 1 ∨ s = -1)
    (p q N : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) :
    ∃ C : ℝ, ∀ y : E n, ‖(Delta^[N] (cls s 0 p q R)) y‖ ≤ C * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) := by
  obtain ⟨hUo, hFc, c₀, C₀, hc₀, hb⟩ := hB n s hs p q R
  set K : ℝ := ((N * n : ℕ) : ℝ) with hK
  set C₁ : ℝ := max C₀ 0 with hC₁
  refine ⟨(Fintype.card (Fin N → Equiv.Perm (Fin n)) : ℝ) * ((K / c₀) ^ n) ^ N * C₁, fun y => ?_⟩
  obtain ⟨k, hk, lam, hy⟩ := herm_spectral y
  set w : Fin n → ℝ := fun i => 1 + |lam i| with hw
  have hwpos : ∀ i, 0 < w i := fun i => by simp only [hw]; positivity
  set W : ℝ := ∏ i, w i with hW
  have hWpos : 0 < W := Finset.prod_pos fun i _ => hwpos i
  set d : Mc n := Matrix.diagonal (fun i => (lam i : ℂ)) with hd
  set ρ : Fin n → Fin n → ℝ := fun i j => c₀ * Real.sqrt ((1 + |lam i|) * (1 + |lam j|)) with hρ
  have hρpos : ∀ i j, 0 < ρ i j := fun i j => mul_pos hc₀ (Real.sqrt_pos.2 (mul_pos (hwpos i) (hwpos j)))
  have hlink := (hL n (Fr s p q R) (Ugood s) hUo hFc (herm_mem_Ugood s hs)).1 N y
  rw [cls_zero, hlink, hy]
  set F' : Mc n → ℂ := fun c => Fr s p q R (k * c * kᴴ) with hF'
  set U' : Set (Mc n) := {c | k * c * kᴴ ∈ Ugood s} with hU'
  have hU'o : IsOpen U' := hUo.preimage (contDiff_conj k).continuous
  have hF'c : ContDiffOn ℂ (⊤ : ℕ∞) F' U' := hFc.comp (contDiff_conj k).contDiffOn (fun c hc => hc)
  have hdisc : pdisc d ρ ⊆ U' := fun b hb' => (hb k hk lam b hb').1
  have hdmem : d ∈ U' := hdisc (fun i j => by simp [hρpos i j |>.le])
  have hherm' : ∀ y', herm y' ∈ U' := fun y' => conj_mem_Ugood s k hk _ (herm_mem_Ugood s hs y')
  rw [← hI n (Fr s p q R) (Ugood s) hUo hFc k hk N d hdmem, (hL n F' U' hU'o hF'c hherm').2 N d hdmem]
  have hM : ∀ b ∈ pdisc d ρ, ‖F' b‖ ≤ C₁ * W ^ (-((p + q : ℕ) : ℝ)) := fun b hb' =>
    ((hb k hk lam b hb').2).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hWpos.le _))
  have hword : ∀ τ : Fin N → Equiv.Perm (Fin n),
      ‖word ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k)) F' d‖ ≤
        ((K / c₀) ^ n / W) ^ N * (C₁ * W ^ (-((p + q : ℕ) : ℝ))) := by
    intro τ
    have h := hC n F' U' hU'o hF'c d ρ hρpos hdisc _ hM ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k))
    refine h.trans (le_of_eq ?_)
    congr 1
    rw [List.map_flatMap]
    simp only [List.map_map, Function.comp_def]
    rw [prod_blocks N (fun j k => (((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k)).length : ℝ) /
      ρ (τ j k) k)]
    rw [length_blocks]
    show ∏ j, ∏ k, K / ρ ((τ j) k) k = ((K / c₀) ^ n / W) ^ N
    have hblock : ∀ j, ∏ k, K / ρ ((τ j) k) k = (K / c₀) ^ n / W := by
      intro j
      have hs := prod_sqrt_perm (τ j) w hwpos
      simp only [hw] at hs
      simp only [hρ]
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, hs, div_pow]
      simp only [hW, hw]
      field_simp
    rw [Finset.prod_congr rfl fun j _ => hblock j, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsgn : ∀ τ : Fin N → Equiv.Perm (Fin n), ‖(((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ))‖ = 1 := by
    intro τ
    have h : ∀ j, |((Equiv.Perm.sign (τ j) : ℤ))| = 1 := fun j => by
      rcases Int.units_eq_one_or (Equiv.Perm.sign (τ j)) with h | h <;> simp [h]
    have h2 : |∏ j, ((Equiv.Perm.sign (τ j) : ℤ))| = 1 := by
      rw [Finset.abs_prod, Finset.prod_eq_one fun j _ => h j]
    rw [Complex.norm_intCast]
    exact_mod_cast h2
  have hdP : dP y ≤ W ^ (2 : ℝ) := by
    rw [dP_of_spectral y k hk lam hy, Real.rpow_two, hW, ← Finset.prod_pow]
    refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
    simp only [hw]
    have : lam i ^ 2 = |lam i| ^ 2 := (sq_abs _).symm
    nlinarith [abs_nonneg (lam i)]
  have hWe : ∀ e : ℝ, 0 ≤ e → W ^ (-e) ≤ (dP y) ^ (-e / 2) := by
    intro e he
    have h1 : W ^ (-e) = (W ^ (2 : ℝ)) ^ (-e / 2) := by
      rw [← Real.rpow_mul hWpos.le]; ring_nf
    rw [h1]
    exact Real.rpow_le_rpow_of_nonpos (dP_pos y) hdP (by linarith)
  calc ‖∑ τ : Fin N → Equiv.Perm (Fin n), (((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ)) *
          word ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k)) F' d‖
      ≤ ∑ τ : Fin N → Equiv.Perm (Fin n), ((K / c₀) ^ n / W) ^ N * (C₁ * W ^ (-((p + q : ℕ) : ℝ))) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
        rw [norm_mul, hsgn τ, one_mul]; exact hword τ
    _ = (Fintype.card (Fin N → Equiv.Perm (Fin n)) : ℝ) * ((K / c₀) ^ n) ^ N * C₁ *
          (W ^ (-((p + q + N : ℕ) : ℝ))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have : W ^ (-((p + q + N : ℕ) : ℝ)) = W ^ (-((p + q : ℕ) : ℝ)) * (W ^ N)⁻¹ := by
          rw [show (-((p + q + N : ℕ) : ℝ)) = (-((p + q : ℕ) : ℝ)) + (-(N : ℝ)) by push_cast; ring,
            Real.rpow_add hWpos, Real.rpow_neg hWpos.le, Real.rpow_natCast, Real.rpow_neg hWpos.le, Real.rpow_natCast]
        rw [this, div_pow]; ring
    _ ≤ (Fintype.card (Fin N → Equiv.Perm (Fin n)) : ℝ) * ((K / c₀) ^ n) ^ N * C₁ *
          (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) := by
        refine mul_le_mul_of_nonneg_left (hWe _ (by positivity)) ?_
        refine mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (pow_nonneg (div_nonneg (by positivity) hc₀.le) _) _))
          (le_max_right _ _)

end PositivityTheory.Rg.Sw.WR.K.GB
end
end

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_herm (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (herm (n := n)) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  have hc : ∀ a b : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x : E n => ((x a b : ℝ) : ℂ)) := fun a b =>
    Complex.ofRealCLM.contDiff.comp ((contDiff_apply ℝ (fun _ => ℝ) b).comp (contDiff_apply ℝ (fun _ => (Fin n → ℝ)) a))
  simp only [herm]
  push_cast
  exact (((hc i j).add (hc j i)).div_const 2).add ((contDiff_const.mul ((hc i j).sub (hc j i))).div_const 2)

theorem clsGainB_of (hC : CauchyW) (hI : Invar) (hB : PBound) (hL : Link) (hT : Twist) (hLg : Lagr) : ClsGain := by
  intro n s hs p q N R
  obtain ⟨hUo, hFc, -⟩ := hB n s hs p q R
  have hH : ContDiff ℝ (⊤ : ℕ∞) (cls s 0 p q R) := by
    rw [cls_zero]
    rw [contDiff_iff_contDiffAt]
    intro y
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (Fr s p q R) (herm y) :=
      ((hFc.restrict_scalars ℝ).contDiffAt (hUo.mem_nhds (herm_mem_Ugood s hs y)))
    exact h1.comp y (contDiff_herm n).contDiffAt
  obtain ⟨G, hGc, hG⟩ := hT n (cls s 0 p q R) hH N
  have hcls : ∀ z : ℂ, cls s z p q R = fun y => ((dP y : ℝ) : ℂ) ^ (-z) * cls s 0 p q R y := by
    intro z; funext y; simp only [cls, neg_zero, Complex.cpow_zero, one_mul]; ring
  set D := n * N with hD
  have hrat : ∀ i : ℕ, ∃ C : ℝ, ∀ y : E n,
      ‖(Delta^[N] (cls s 0 (p + i) (q + i) R)) y‖ ≤ C * (dP y) ^ (-((p + i + (q + i) + N : ℕ) : ℝ) / 2) :=
    fun i => ratBound hC hI hB hL s hs (p + i) (q + i) N R
  choose Ci hCi using hrat
  obtain ⟨CL, hCL⟩ := hLg D
  set Cm : ℝ := ∑ i ∈ Finset.range (D + 1), |Ci i| with hCm
  refine ⟨D + 1, fun j => Polynomial.X ^ (j : ℕ), fun j => G j, fun j => (hGc j).continuous, ⟨CL * Cm, ?_⟩, ?_⟩
  · intro j y
    have hdp := dP_pos y
    have hval : ∀ i ≤ D, ‖∑ j ∈ Finset.range (D + 1), ((i : ℕ) : ℂ) ^ j * G j y‖ ≤ Cm * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) := by
      intro i hi
      have e1 := hG (i : ℂ) y
      rw [← hcls, cls_nat s hs i p q R] at e1
      have hne : (((dP y : ℝ) : ℂ)) ^ (-(i : ℂ)) ≠ 0 := by
        rw [Complex.cpow_neg, Complex.cpow_natCast]; exact inv_ne_zero (pow_ne_zero _ (by exact_mod_cast hdp.ne'))
      have e2 : ∑ j ∈ Finset.range (D + 1), ((i : ℕ) : ℂ) ^ j * G j y =
          (((dP y : ℝ) : ℂ)) ^ i * (Delta^[N] (cls s 0 (p + i) (q + i) R)) y := by
        rw [e1, Complex.cpow_neg, Complex.cpow_natCast, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast hdp.ne')), one_mul]
      rw [e2, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hdp.le]
      have hb := hCi i y
      have hCi_le : |Ci i| ≤ Cm := by
        rw [hCm]
        exact Finset.single_le_sum (f := fun i => |Ci i|) (fun i _ => abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
      calc dP y ^ i * ‖(Delta^[N] (cls s 0 (p + i) (q + i) R)) y‖
          ≤ dP y ^ i * (Ci i * (dP y) ^ (-((p + i + (q + i) + N : ℕ) : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left hb (pow_nonneg hdp.le _)
        _ = Ci i * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) := by
            rw [← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add hdp]
            congr 2; push_cast; ring
        _ ≤ Cm * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right ((le_abs_self _).trans hCi_le) (Real.rpow_nonneg hdp.le _)
    have := hCL (fun j => G j y) _ hval j (Nat.lt_succ_iff.1 j.2)
    simpa [mul_assoc] using this
  · intro z y
    rw [hcls z, hG z y]
    congr 1
    rw [Finset.sum_range (fun j => z ^ j * G j y)]
    simp [Polynomial.eval_pow, Polynomial.eval_X]

end PositivityTheory.Rg.Sw.WR.K.GB
