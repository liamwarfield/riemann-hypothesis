module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ContDiffHerm
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GBInvar
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GBTwist

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GBLagr
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

theorem lagr : Lagr := by
  intro D
  set V : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ := Matrix.vandermonde fun i => ((i : ℕ) : ℂ) with hV
  have hdet : V.det ≠ 0 := by
    rw [hV, Matrix.det_vandermonde]
    refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_
    have hij : i < j := (Finset.mem_Ioi.1 hj)
    intro h
    have : ((j : ℕ) : ℂ) = ((i : ℕ) : ℂ) := by linear_combination h
    have := Nat.cast_injective this
    exact absurd (Fin.ext this) (ne_of_gt hij)
  have hunit : IsUnit V.det := isUnit_iff_ne_zero.2 hdet
  set W := V⁻¹ with hW
  refine ⟨∑ j, ∑ i, ‖W j i‖, fun c B hB j hj => ?_⟩
  set cv : Fin (D + 1) → ℂ := fun j => c j with hcv
  have hvals : ∀ i : Fin (D + 1), V.mulVec cv i = ∑ j ∈ Finset.range (D + 1), (((i : ℕ) : ℕ) : ℂ) ^ j * c j := by
    intro i
    simp only [Matrix.mulVec, dotProduct, hV, Matrix.vandermonde_apply, hcv]
    rw [Fin.sum_univ_eq_sum_range (fun k => ((i : ℕ) : ℂ) ^ k * c k)]
  have hB' : ∀ i : Fin (D + 1), ‖V.mulVec cv i‖ ≤ B := fun i => by
    rw [hvals i]; exact hB i (Nat.lt_succ_iff.1 i.2)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB' 0)
  have hinv : W.mulVec (V.mulVec cv) = cv := by
    rw [Matrix.mulVec_mulVec, hW, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
  set jj : Fin (D + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have hc : c j = ∑ i, W jj i * V.mulVec cv i := by
    have := congrFun hinv jj
    simp only [Matrix.mulVec, dotProduct, hcv] at this ⊢
    rw [this]
  rw [hc]
  calc ‖∑ i, W jj i * V.mulVec cv i‖ ≤ ∑ i, ‖W jj i * V.mulVec cv i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖W jj i‖ * B := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hB' i) (norm_nonneg _)
    _ = (∑ i, ‖W jj i‖) * B := by rw [Finset.sum_mul]
    _ ≤ (∑ j, ∑ i, ‖W j i‖) * B := by
        refine mul_le_mul_of_nonneg_right ?_ hB0
        exact Finset.single_le_sum (f := fun j => ∑ i, ‖W j i‖) (fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg _)
          (Finset.mem_univ jj)

end PositivityTheory.Rg.Sw.WR.K.GB
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GBBound
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem pb_cd_entry (i j : Fin n) : ContDiff ℂ (⊤ : ℕ∞) (fun b : Mc n => b i j) :=
  contDiff_apply_apply (𝕜 := ℂ) (E := ℂ) i j

theorem pb_cd_det {f : Mc n → Mc n} (hf : ∀ i j, ContDiff ℂ (⊤ : ℕ∞) (fun b => f b i j)) :
    ContDiff ℂ (⊤ : ℕ∞) (fun b => (f b).det) := by
  have e : (fun b => (f b).det) =
      fun b => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, f b (σ i) i := by
    funext b; rw [Matrix.det_apply']
  rw [e]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hf _ _)

theorem pb_cd_affine (a : ℂ) (e : ℂ) (i j : Fin n) :
    ContDiff ℂ (⊤ : ℕ∞) (fun b : Mc n => (1 + (e * a) • b) i j) := by
  have h : (fun b : Mc n => (1 + (e * a) • b) i j) = fun b => (1 : Mc n) i j + (e * a) * b i j := by
    funext b; simp [Matrix.add_apply, Matrix.smul_apply]
  rw [h]; exact contDiff_const.add (contDiff_const.mul (pb_cd_entry i j))

theorem pb_cd_adj {f : Mc n → Mc n} (hf : ∀ i j, ContDiff ℂ (⊤ : ℕ∞) (fun b => f b i j)) (i j : Fin n) :
    ContDiff ℂ (⊤ : ℕ∞) (fun b => (f b).adjugate i j) := by
  simp only [Matrix.adjugate_apply]
  apply pb_cd_det
  intro r c
  by_cases h : r = j
  · subst h; simp only [Matrix.updateRow_self]; exact contDiff_const
  · simp only [Matrix.updateRow_ne h]; exact hf r c

theorem pb_cdOn_inv {f : Mc n → Mc n} (hf : ∀ i j, ContDiff ℂ (⊤ : ℕ∞) (fun b => f b i j)) (s : Set (Mc n))
    (hs : ∀ b ∈ s, (f b).det ≠ 0) (i j : Fin n) : ContDiffOn ℂ (⊤ : ℕ∞) (fun b => (f b)⁻¹ i j) s := by
  have e : (fun b => (f b)⁻¹ i j) = fun b => ((f b).det)⁻¹ * (f b).adjugate i j := by
    funext b; rw [Matrix.inv_def, Ring.inverse_eq_inv]; simp [Matrix.smul_apply]
  rw [e]
  exact ((pb_cd_det hf).contDiffOn.inv hs).mul (pb_cd_adj hf i j).contDiffOn

theorem pb_cdOn_detInv {f : Mc n → Mc n} (hf : ∀ i j, ContDiff ℂ (⊤ : ℕ∞) (fun b => f b i j)) (s : Set (Mc n))
    (hs : ∀ b ∈ s, (f b).det ≠ 0) : ContDiffOn ℂ (⊤ : ℕ∞) (fun b => (f b)⁻¹.det) s := by
  have e : (fun b => (f b)⁻¹.det) = fun b => ((f b).det)⁻¹ := by
    funext b; rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  rw [e]; exact (pb_cd_det hf).contDiffOn.inv hs

theorem pb_cdOn_eval {ι : Type} (R : MvPolynomial ι ℂ) (v : ι → Mc n → ℂ) (s : Set (Mc n))
    (hv : ∀ k, ContDiffOn ℂ (⊤ : ℕ∞) (v k) s) :
    ContDiffOn ℂ (⊤ : ℕ∞) (fun b => MvPolynomial.eval (fun k => v k b) R) s := by
  induction R using MvPolynomial.induction_on with
  | C a => simpa using (contDiffOn_const : ContDiffOn ℂ (⊤ : ℕ∞) (fun _ : Mc n => a) s)
  | add p q hp hq => simpa using hp.add hq
  | mul_X p k hp => simpa using hp.mul (hv k)

theorem pb_eval_bound {ι : Type} (R : MvPolynomial ι ℂ) (B : ℝ) :
    ∃ C : ℝ, ∀ v : ι → ℂ, (∀ k, ‖v k‖ ≤ B) → ‖MvPolynomial.eval v R‖ ≤ C := by
  induction R using MvPolynomial.induction_on with
  | C a => exact ⟨‖a‖, fun v _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨C1, h1⟩ := hp; obtain ⟨C2, h2⟩ := hq
    exact ⟨C1 + C2, fun v hv => by
      simp only [map_add (f := _)]; exact (norm_add_le _ _).trans (add_le_add (h1 v hv) (h2 v hv))⟩
  | mul_X p k hp =>
    obtain ⟨C1, h1⟩ := hp
    exact ⟨max C1 0 * max B 0, fun v hv => by
      simp only [map_mul, MvPolynomial.eval_X, norm_mul]
      exact mul_le_mul ((h1 v hv).trans (le_max_left _ _)) ((hv k).trans (le_max_left _ _))
        (norm_nonneg _) (le_max_right _ _)⟩

theorem pb_norm_one_sub (a : ℂ) (ha : a = Complex.I ∨ a = -Complex.I) (l : ℝ) :
    (1 + |l|) / Real.sqrt 2 ≤ ‖1 - a * (l : ℂ)‖ := by
  have hsq : ‖1 - a * (l : ℂ)‖ ^ 2 = 1 + l ^ 2 := by
    rw [Complex.sq_norm]
    rcases ha with rfl | rfl <;> simp [Complex.normSq_apply] <;> ring
  have h2 : ((1 + |l|) / Real.sqrt 2) ^ 2 ≤ ‖1 - a * (l : ℂ)‖ ^ 2 := by
    rw [hsq, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    nlinarith [sq_abs l, sq_nonneg (1 - |l|), abs_nonneg l]
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 h2

def pbwt (lam : Fin n → ℝ) (i : Fin n) : ℝ := Real.sqrt (1 + |lam i|)

theorem pbwt_pos (lam : Fin n → ℝ) (i : Fin n) : 0 < pbwt lam i := Real.sqrt_pos.2 (by positivity)

theorem pb_one_le_wt (lam : Fin n → ℝ) (i : Fin n) : 1 ≤ pbwt lam i := by
  unfold pbwt; rw [Real.one_le_sqrt]; linarith [abs_nonneg (lam i)]

theorem pbwt_sq (lam : Fin n → ℝ) (i : Fin n) : pbwt lam i ^ 2 = 1 + |lam i| :=
  Real.sq_sqrt (by positivity)

theorem pb_dom (a : ℂ) (ha : a = Complex.I ∨ a = -Complex.I) (lam : Fin n → ℝ) (c₀ : ℝ) (hc : 0 ≤ c₀)
    (hc₀ : (n : ℝ) * c₀ ≤ 1 / 4) (b : Mc n)
    (hb : ∀ i j, ‖b i j - Matrix.diagonal (fun i => (lam i : ℂ)) i j‖ ≤ c₀ * (pbwt lam i * pbwt lam j))
    (x : Fin n → ℂ) (B : ℝ) (hy : ∀ i, ‖((1 - a • b) *ᵥ x) i‖ ≤ B * pbwt lam i) :
    ∀ i, pbwt lam i * ‖x i‖ ≤ 3 * B := by
  intro i
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun j => pbwt lam j * ‖x j‖) ⟨i, Finset.mem_univ _⟩
  set m := pbwt lam i0 * ‖x i0‖ with hmdef
  have hm : ∀ j, pbwt lam j * ‖x j‖ ≤ m := fun j => hi0 j (Finset.mem_univ _)
  have hm0 : 0 ≤ m := mul_nonneg (pbwt_pos lam i0).le (norm_nonneg _)
  have ha1 : ‖a‖ = 1 := by rcases ha with rfl | rfl <;> simp
  have hD : ∑ j, Matrix.diagonal (fun i => (lam i : ℂ)) i0 j * x j = (lam i0 : ℂ) * x i0 := by
    rw [Finset.sum_eq_single i0]
    · simp [Matrix.diagonal_apply_eq]
    · intro j _ hj; simp [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
    · simp
  have row : ((1 - a • b) *ᵥ x) i0 = (1 - a * (lam i0 : ℂ)) * x i0 -
      a * ∑ j, (b i0 j - Matrix.diagonal (fun i => (lam i : ℂ)) i0 j) * x j := by
    have e1 : ((1 - a • b) *ᵥ x) i0 = x i0 - a * ∑ j, b i0 j * x j := by
      simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, sub_mul,
        Finset.sum_sub_distrib, Finset.mul_sum, Matrix.one_apply, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_assoc]
    rw [e1]; simp only [sub_mul, Finset.sum_sub_distrib, hD]; ring
  have hsum : ‖∑ j, (b i0 j - Matrix.diagonal (fun i => (lam i : ℂ)) i0 j) * x j‖ ≤ (n : ℝ) * (c₀ * pbwt lam i0 * m) := by
    calc ‖∑ j, (b i0 j - Matrix.diagonal (fun i => (lam i : ℂ)) i0 j) * x j‖ ≤ ∑ j, ‖(b i0 j - Matrix.diagonal (fun i => (lam i : ℂ)) i0 j) * x j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin n, c₀ * pbwt lam i0 * m := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul]
        calc ‖(b i0 j - Matrix.diagonal (fun i => (lam i : ℂ)) i0 j)‖ * ‖x j‖ ≤ (c₀ * (pbwt lam i0 * pbwt lam j)) * ‖x j‖ :=
              mul_le_mul_of_nonneg_right (hb i0 j) (norm_nonneg _)
          _ = c₀ * pbwt lam i0 * (pbwt lam j * ‖x j‖) := by ring
          _ ≤ c₀ * pbwt lam i0 * m :=
              mul_le_mul_of_nonneg_left (hm j) (mul_nonneg hc (pbwt_pos lam i0).le)
      _ = (n : ℝ) * (c₀ * pbwt lam i0 * m) := by simp
  have hlow : (pbwt lam i0 / Real.sqrt 2) * m ≤ ‖(1 - a * (lam i0 : ℂ)) * x i0‖ := by
    rw [norm_mul]
    have h1 := pb_norm_one_sub a ha (lam i0)
    have : (pbwt lam i0 / Real.sqrt 2) * m = ((1 + |lam i0|) / Real.sqrt 2) * ‖x i0‖ := by
      rw [hmdef, ← pbwt_sq]; ring
    rw [this]; exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have hup : ‖(1 - a * (lam i0 : ℂ)) * x i0‖ ≤ B * pbwt lam i0 + (n : ℝ) * (c₀ * pbwt lam i0 * m) := by
    have e : (1 - a * (lam i0 : ℂ)) * x i0 = ((1 - a • b) *ᵥ x) i0 + a * ∑ j, (b i0 j - Matrix.diagonal (fun i => (lam i : ℂ)) i0 j) * x j := by
      rw [row]; ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add (hy i0) ?_)
    rw [norm_mul, ha1, one_mul]; exact hsum
  have key : pbwt lam i0 * (m / Real.sqrt 2) ≤ pbwt lam i0 * (B + (n : ℝ) * c₀ * m) := by
    have := hlow.trans hup
    calc pbwt lam i0 * (m / Real.sqrt 2) = (pbwt lam i0 / Real.sqrt 2) * m := by ring
      _ ≤ B * pbwt lam i0 + (n : ℝ) * (c₀ * pbwt lam i0 * m) := this
      _ = pbwt lam i0 * (B + (n : ℝ) * c₀ * m) := by ring
  have key2 := le_of_mul_le_mul_left key (pbwt_pos lam i0)
  have hs2 : Real.sqrt 2 ≤ 10 / 7 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hsp : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hmd : m * (7 / 10) ≤ m / Real.sqrt 2 := by
    rw [le_div_iff₀ hsp]; nlinarith
  have hnc : (n : ℝ) * c₀ * m ≤ m / 4 := by nlinarith
  have hfin : m ≤ 3 * B := by nlinarith
  exact (hm i).trans hfin

theorem pb_inv (a : ℂ) (ha : a = Complex.I ∨ a = -Complex.I) (lam : Fin n → ℝ) (c₀ : ℝ) (hc : 0 ≤ c₀)
    (hc₀ : (n : ℝ) * c₀ ≤ 1 / 4) (b : Mc n)
    (hb : ∀ i j, ‖b i j - Matrix.diagonal (fun i => (lam i : ℂ)) i j‖ ≤ c₀ * (pbwt lam i * pbwt lam j)) :
    IsUnit (1 - a • b).det ∧ (∀ i j, ‖(1 - a • b)⁻¹ i j‖ ≤ 3 / (pbwt lam i * pbwt lam j)) := by
  have hdet : IsUnit (1 - a • b).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hv0
    funext i
    have := pb_dom a ha lam c₀ hc hc₀ b hb v 0 (fun i => by simp [hv]) i
    have hw := pbwt_pos lam i
    have : ‖v i‖ ≤ 0 := by nlinarith [norm_nonneg (v i)]
    simpa using le_antisymm this (norm_nonneg _)
  refine ⟨hdet, fun i j => ?_⟩
  set Y := 1 - a • b
  have hx : Y *ᵥ (Y⁻¹ *ᵥ Pi.single j 1) = Pi.single j 1 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hwj := pbwt_pos lam j
  have key := pb_dom a ha lam c₀ hc hc₀ b hb (Y⁻¹ *ᵥ Pi.single j 1) (1 / pbwt lam j) (fun k => by
    rw [hx]
    by_cases hk : k = j
    · subst hk; simp [inv_mul_cancel₀ hwj.ne']
    · simp [Pi.single_apply, hk]; exact mul_nonneg (by positivity) (pbwt_pos lam k).le) i
  have e : (Y⁻¹ *ᵥ Pi.single j 1) i = Y⁻¹ i j := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [e] at key
  have hwi := pbwt_pos lam i
  rw [le_div_iff₀ (mul_pos hwi hwj)]
  calc ‖Y⁻¹ i j‖ * (pbwt lam i * pbwt lam j) = (pbwt lam i * ‖Y⁻¹ i j‖) * pbwt lam j := by ring
    _ ≤ (3 * (1 / pbwt lam j)) * pbwt lam j := mul_le_mul_of_nonneg_right key hwj.le
    _ = 3 := by field_simp

theorem pb_det_le (A : Mc n) (f : Fin n → ℝ) (K : ℝ)
    (hA : ∀ i j, ‖A i j‖ ≤ K / (f i * f j)) : ‖A.det‖ ≤ (Nat.factorial n : ℝ) * (K ^ n / (∏ i, f i) ^ 2) := by
  rw [Matrix.det_apply']
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      ‖((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A (σ i) i‖ ≤ K ^ n / (∏ i, f i) ^ 2 := by
    intro σ
    have hs : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    rw [norm_mul, hs, one_mul, norm_prod]
    calc ∏ i, ‖A (σ i) i‖ ≤ ∏ i, K / (f (σ i) * f i) :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hA _ _)
      _ = K ^ n / (∏ i, f i) ^ 2 := by
          rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            Finset.prod_mul_distrib, Equiv.prod_comp σ f, sq]
  calc ‖∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A (σ i) i‖
      ≤ ∑ σ : Equiv.Perm (Fin n), ‖((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), K ^ n / (∏ i, f i) ^ 2 := Finset.sum_le_sum fun σ _ => hterm σ
    _ = (Nat.factorial n : ℝ) * (K ^ n / (∏ i, f i) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

theorem pb_kk (k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) : k * kᴴ = 1 ∧ kᴴ * k = 1 :=
  ⟨by simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.1 hk,
   by simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.1 hk⟩

theorem pb_norm_det_unitary (k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) : ‖k.det‖ = 1 := by
  have h2 : k.det * star k.det = 1 := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, (pb_kk k hk).1, Matrix.det_one]
  have h3 : Complex.normSq k.det = 1 := by
    have := h2; rw [Complex.star_def, Complex.mul_conj] at this; exact_mod_cast this
  have h4 : ‖k.det‖ ^ 2 = 1 := by rw [Complex.sq_norm, h3]
  nlinarith [norm_nonneg k.det, sq_nonneg (‖k.det‖ - 1)]

theorem pb_conj (c : ℂ) (k b : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    1 - c • (k * b * kᴴ) = k * (1 - c • b) * kᴴ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, (pb_kk k hk).1, Matrix.mul_smul, Matrix.smul_mul]

theorem pb_conj_inv (Y k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : IsUnit Y.det) :
    (k * Y * kᴴ)⁻¹ = k * Y⁻¹ * kᴴ := by
  apply Matrix.inv_eq_right_inv
  calc k * Y * kᴴ * (k * Y⁻¹ * kᴴ) = k * (Y * (kᴴ * k) * Y⁻¹) * kᴴ := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [(pb_kk k hk).2, Matrix.mul_one, Matrix.mul_nonsing_inv _ hY, Matrix.mul_one, (pb_kk k hk).1]

theorem pb_conj_unit (Y k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : IsUnit Y.det) :
    IsUnit (k * Y * kᴴ).det := by
  rw [isUnit_iff_ne_zero, Matrix.det_mul, Matrix.det_mul]
  have h1 : k.det ≠ 0 := fun h => by simpa [h] using pb_norm_det_unitary k hk
  have h2 : kᴴ.det ≠ 0 := by
    rw [Matrix.det_conjTranspose]; exact fun h => h1 (by simpa using h)
  exact mul_ne_zero (mul_ne_zero h1 (isUnit_iff_ne_zero.1 hY)) h2

theorem pb_conj_entry (M k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (K : ℝ)
    (hM : ∀ a b, ‖M a b‖ ≤ K) (i j : Fin n) : ‖(k * M * kᴴ) i j‖ ≤ (n : ℝ) * ((n : ℝ) * K) := by
  have hk' : kᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem hk
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ b, ‖(k * M) i b * kᴴ b j‖ ≤ ∑ _b : Fin n, (n : ℝ) * K := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul, Matrix.mul_apply]
        have e2 : ‖kᴴ b j‖ ≤ 1 := entry_norm_bound_of_unitary hk' b j
        have e1 : ‖∑ a, k i a * M a b‖ ≤ (n : ℝ) * K := by
          refine (norm_sum_le _ _).trans ?_
          calc ∑ a, ‖k i a * M a b‖ ≤ ∑ _a : Fin n, K := by
                refine Finset.sum_le_sum fun a _ => ?_
                rw [norm_mul]
                calc ‖k i a‖ * ‖M a b‖ ≤ 1 * K :=
                      mul_le_mul (entry_norm_bound_of_unitary hk i a) (hM a b) (norm_nonneg _) zero_le_one
                  _ = K := one_mul K
            _ = (n : ℝ) * K := by simp
        calc ‖∑ a, k i a * M a b‖ * ‖kᴴ b j‖ ≤ ((n : ℝ) * K) * 1 :=
              mul_le_mul e1 e2 (norm_nonneg _) ((norm_nonneg _).trans e1)
          _ = (n : ℝ) * K := mul_one _
    _ = (n : ℝ) * ((n : ℝ) * K) := by simp

theorem pb_cd_oneSub (c : ℂ) (i j : Fin n) : ContDiff ℂ (⊤ : ℕ∞) (fun b : Mc n => (1 - c • b) i j) := by
  have h : (fun b : Mc n => (1 - c • b) i j) = fun b => (1 + ((-1) * c) • b) i j := by
    funext b; simp [sub_eq_add_neg, neg_smul]
  rw [h]; exact pb_cd_affine c (-1) i j

theorem pBound : PBound := by
  intro n s hs p q R
  have ha : Complex.I * s = Complex.I ∨ Complex.I * s = -Complex.I := by rcases hs with rfl | rfl <;> simp
  have ham : -(Complex.I * s) = Complex.I ∨ -(Complex.I * s) = -Complex.I := by
    rcases ha with h | h <;> simp [h]
  have hplus : ∀ b : Mc n, (1 + (Complex.I * s) • b) = 1 - (-(Complex.I * s)) • b := by
    intro b; rw [neg_smul, sub_neg_eq_add]
  have he1 : ∀ i j, ContDiff ℂ (⊤ : ℕ∞) (fun b : Mc n => (1 - (Complex.I * s) • b) i j) :=
    fun i j => pb_cd_oneSub _ i j
  have he2 : ∀ i j, ContDiff ℂ (⊤ : ℕ∞) (fun b : Mc n => (1 + (Complex.I * s) • b) i j) := fun i j => by
    simpa [one_mul] using pb_cd_affine (Complex.I * s) 1 i j
  have hd1 := pb_cd_det he1
  have hd2 := pb_cd_det he2
  have hopen : IsOpen (Ugood (n := n) s) := by
    have e : Ugood (n := n) s = {b | (1 - (Complex.I * s) • b).det ≠ 0} ∩ {b | (1 + (Complex.I * s) • b).det ≠ 0} := by
      ext b; simp [Ugood, isUnit_iff_ne_zero]
    rw [e]
    exact (isOpen_ne_fun hd1.continuous continuous_const).inter (isOpen_ne_fun hd2.continuous continuous_const)
  have hne1 : ∀ b ∈ Ugood (n := n) s, (1 - (Complex.I * s) • b).det ≠ 0 := fun b hb => isUnit_iff_ne_zero.1 hb.1
  have hne2 : ∀ b ∈ Ugood (n := n) s, (1 + (Complex.I * s) • b).det ≠ 0 := fun b hb => isUnit_iff_ne_zero.1 hb.2
  have hsmooth : ContDiffOn ℂ (⊤ : ℕ∞) (Fr s p q R) (Ugood s) := by
    have hv : ∀ k : Bool × Fin n × Fin n, ContDiffOn ℂ (⊤ : ℕ∞) (fun b : Mc n => if k.1 then
        (1 + (Complex.I * s) • b)⁻¹ k.2.1 k.2.2 else (1 - (Complex.I * s) • b)⁻¹ k.2.1 k.2.2) (Ugood s) := by
      rintro ⟨t, i, j⟩
      cases t
      · simpa using pb_cdOn_inv he1 _ hne1 i j
      · simpa using pb_cdOn_inv he2 _ hne2 i j
    exact (((pb_cdOn_detInv he1 _ hne1).pow p).mul ((pb_cdOn_detInv he2 _ hne2).pow q)).mul
      (pb_cdOn_eval R _ _ hv)
  obtain ⟨CR, hCR⟩ := pb_eval_bound R ((n : ℝ) * ((n : ℝ) * 3))
  refine ⟨hopen, hsmooth, 1 / (4 * (n : ℝ) + 4),
    ((Nat.factorial n : ℝ) * 3 ^ n) ^ p * ((Nat.factorial n : ℝ) * 3 ^ n) ^ q * CR, by positivity, ?_⟩
  intro k hk lam b hb
  set K1 : ℝ := (Nat.factorial n : ℝ) * 3 ^ n with hK1def
  have hc₀ : (n : ℝ) * (1 / (4 * (n : ℝ) + 4)) ≤ 1 / 4 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith
  have hb' : ∀ i j, ‖b i j - Matrix.diagonal (fun i => (lam i : ℂ)) i j‖ ≤
      (1 / (4 * (n : ℝ) + 4)) * (pbwt lam i * pbwt lam j) := by
    intro i j
    have := hb i j
    simpa [pbwt, Real.sqrt_mul (by positivity : (0:ℝ) ≤ 1 + |lam i|)] using this
  obtain ⟨hu1, hY1⟩ := pb_inv _ ha lam _ (by positivity) hc₀ b hb'
  obtain ⟨hu2, hY2⟩ := pb_inv _ ham lam _ (by positivity) hc₀ b hb'
  have c1 : 1 - (Complex.I * s) • (k * b * kᴴ) = k * (1 - (Complex.I * s) • b) * kᴴ := pb_conj _ k b hk
  have c2 : 1 + (Complex.I * s) • (k * b * kᴴ) = k * (1 - (-(Complex.I * s)) • b) * kᴴ := by
    rw [hplus]; exact pb_conj _ k b hk
  refine ⟨⟨by rw [c1]; exact pb_conj_unit _ k hk hu1, by rw [c2]; exact pb_conj_unit _ k hk hu2⟩, ?_⟩
  have i1 : (1 - (Complex.I * s) • (k * b * kᴴ))⁻¹ = k * (1 - (Complex.I * s) • b)⁻¹ * kᴴ := by
    rw [c1]; exact pb_conj_inv _ k hk hu1
  have i2 : (1 + (Complex.I * s) • (k * b * kᴴ))⁻¹ = k * (1 - (-(Complex.I * s)) • b)⁻¹ * kᴴ := by
    rw [c2]; exact pb_conj_inv _ k hk hu2
  set P : ℝ := ∏ i, (1 + |lam i|) with hPdef
  have hP : 0 < P := Finset.prod_pos fun i _ => by positivity
  have hPw : (∏ i, pbwt lam i) ^ 2 = P := by
    rw [← Finset.prod_pow]; exact Finset.prod_congr rfl fun i _ => pbwt_sq lam i
  have hdetY : ∀ (Y : Mc n), (∀ i j, ‖Y i j‖ ≤ 3 / (pbwt lam i * pbwt lam j)) → ‖Y.det‖ ≤ K1 / P := by
    intro Y hYb
    have := pb_det_le Y (pbwt lam) 3 hYb
    rw [hPw] at this
    calc ‖Y.det‖ ≤ (Nat.factorial n : ℝ) * (3 ^ n / P) := this
      _ = K1 / P := by rw [hK1def]; ring
  have hdc : ∀ (Y : Mc n), ‖(k * Y * kᴴ).det‖ = ‖Y.det‖ := by
    intro Y
    rw [Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul, pb_norm_det_unitary k hk, Matrix.det_conjTranspose,
      norm_star, pb_norm_det_unitary k hk, one_mul, mul_one]
  have hdet1 : ‖(1 - (Complex.I * s) • (k * b * kᴴ))⁻¹.det‖ ≤ K1 / P := by
    rw [i1, hdc]; exact hdetY _ hY1
  have hdet2 : ‖(1 + (Complex.I * s) • (k * b * kᴴ))⁻¹.det‖ ≤ K1 / P := by
    rw [i2, hdc]; exact hdetY _ hY2
  have hent : ∀ (Y : Mc n), (∀ i j, ‖Y i j‖ ≤ 3 / (pbwt lam i * pbwt lam j)) →
      ∀ i j, ‖(k * Y * kᴴ) i j‖ ≤ (n : ℝ) * ((n : ℝ) * 3) := by
    intro Y hYb i j
    refine pb_conj_entry Y k hk 3 (fun a c => (hYb a c).trans ?_) i j
    rw [div_le_iff₀ (mul_pos (pbwt_pos lam a) (pbwt_pos lam c))]
    nlinarith [pb_one_le_wt lam a, pb_one_le_wt lam c]
  have hev : ‖MvPolynomial.eval (fun k' : Bool × Fin n × Fin n => if k'.1 then
      (1 + (Complex.I * s) • (k * b * kᴴ))⁻¹ k'.2.1 k'.2.2 else (1 - (Complex.I * s) • (k * b * kᴴ))⁻¹ k'.2.1 k'.2.2) R‖
      ≤ CR := by
    apply hCR
    rintro ⟨t, i, j⟩
    cases t
    · simp only [Bool.false_eq_true, if_false]; rw [i1]; exact hent _ hY1 i j
    · simp only [if_true]; rw [i2]; exact hent _ hY2 i j
  have hrp : P ^ (-((p + q : ℕ) : ℝ)) = (P ^ (p + q))⁻¹ := by
    rw [Real.rpow_neg hP.le, Real.rpow_natCast]
  show ‖(1 - (Complex.I * s) • (k * b * kᴴ))⁻¹.det ^ p * (1 + (Complex.I * s) • (k * b * kᴴ))⁻¹.det ^ q *
      MvPolynomial.eval (fun k' : Bool × Fin n × Fin n => if k'.1 then
      (1 + (Complex.I * s) • (k * b * kᴴ))⁻¹ k'.2.1 k'.2.2 else (1 - (Complex.I * s) • (k * b * kᴴ))⁻¹ k'.2.1 k'.2.2) R‖
      ≤ K1 ^ p * K1 ^ q * CR * P ^ (-((p + q : ℕ) : ℝ))
  rw [hrp, norm_mul, norm_mul, norm_pow, norm_pow]
  have hK1 : 0 ≤ K1 := by positivity
  calc _ ≤ (K1 / P) ^ p * (K1 / P) ^ q * CR := by gcongr
    _ = K1 ^ p * K1 ^ q * CR * (P ^ (p + q))⁻¹ := by
      rw [div_pow, div_pow, pow_add, mul_inv, div_eq_mul_inv, div_eq_mul_inv]; ring

end PositivityTheory.Rg.Sw.WR.K.GB
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GBCauchy
noncomputable section

open Matrix Metric

namespace PositivityTheory.Rg.Sw.WR.K.GB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contDiffOn_cpart {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U)
    (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (i j : Fin n) : ContDiffOn ℂ (⊤ : ℕ∞) (cpart i j F) U := by
  letI : NormedAddCommGroup (Mc n →L[ℂ] ℂ) := ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℂ (Mc n →L[ℂ] ℂ) := ContinuousLinearMap.toNormedSpace
  have hle : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    rw [← WithTop.coe_one, ← WithTop.coe_add, top_add]
  have h1 : ContDiffOn ℂ (⊤ : ℕ∞) (fun b => fderiv ℂ F b) U :=
    hF.fderiv_of_isOpen (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) hU hle
  exact h1.clm_apply contDiffOn_const

theorem contDiffOn_word {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U)
    (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) : ∀ L : List (Fin n × Fin n), ContDiffOn ℂ (⊤ : ℕ∞) (word L F) U
  | [] => hF
  | ij :: L => contDiffOn_cpart hU (contDiffOn_word hU hF L) ij.1 ij.2

theorem mem_pdisc_self (b : Mc n) {r : Fin n → Fin n → ℝ} (hr : ∀ i j, 0 < r i j) : b ∈ pdisc b r := by
  intro i j
  simp only [sub_self, norm_zero]
  exact (hr i j).le

theorem shift_apply (b : Mc n) (w : ℂ) (i j a c : Fin n) :
    (b + w • Matrix.single i j (1 : ℂ)) a c - b a c = if i = a ∧ j = c then w else 0 := by
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_sub_cancel_left]
  by_cases h : i = a ∧ j = c
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [Matrix.single_apply_of_ne _ _ _ _ _ h, if_neg h, mul_zero]

theorem shift_mem (b : Mc n) {r : Fin n → Fin n → ℝ} (hr : ∀ i j, 0 < r i j) (i j : Fin n) {w : ℂ}
    (hw : ‖w‖ ≤ r i j) : b + w • Matrix.single i j (1 : ℂ) ∈ pdisc b r := by
  intro a c
  rw [shift_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact hw
  · simpa using (hr a c).le

theorem shift_sub (b : Mc n) {r : Fin n → Fin n → ℝ} (hr : ∀ i j, 0 < r i j) (i j : Fin n) {w : ℂ}
    {K l : ℝ} (hK : 0 < K) (hl : 0 ≤ l) (hlK : l + 1 = K) (hw : ‖w‖ = r i j / K) :
    pdisc (b + w • Matrix.single i j (1 : ℂ)) (fun a c => r a c * (l / K)) ⊆ pdisc b r := by
  intro x hx a c
  have h1 := hx a c
  have h2 : ‖x a c - b a c‖ ≤ ‖x a c - (b + w • Matrix.single i j (1 : ℂ)) a c‖ +
      ‖(b + w • Matrix.single i j (1 : ℂ)) a c - b a c‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  rw [shift_apply] at h2
  have hlK' : l / K ≤ 1 := by rw [div_le_one hK]; linarith
  split_ifs at h2 with h
  · obtain ⟨rfl, rfl⟩ := h
    rw [hw] at h2
    have : r i j * (l / K) + r i j / K = r i j := by
      field_simp
      rw [← hlK]
    linarith
  · simp only [norm_zero, add_zero] at h2
    have := mul_le_of_le_one_right (hr a c).le hlK'
    linarith

theorem cauchy_gen {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U)
    (M : ℝ) : ∀ (L : List (Fin n × Fin n)) (b : Mc n) (r : Fin n → Fin n → ℝ), (∀ i j, 0 < r i j) →
      pdisc b r ⊆ U → (∀ x ∈ pdisc b r, ‖F x‖ ≤ M) →
      ‖word L F b‖ ≤ (L.map fun ij => (L.length : ℝ) / r ij.1 ij.2).prod * M := by
  intro L
  induction L with
  | nil =>
    intro b r hr _ hM
    simp only [word, List.foldr_nil, List.map_nil, List.prod_nil, one_mul]
    exact hM b (mem_pdisc_self b hr)
  | cons ij L ih =>
    intro b r hr hsub hM
    set K : ℝ := (L.length : ℝ) + 1 with hKdef
    have hK : 0 < K := by positivity
    set δ : ℝ := r ij.1 ij.2 / K with hδdef
    have hδ : 0 < δ := div_pos (hr _ _) hK
    have hδr : δ ≤ r ij.1 ij.2 := div_le_self (hr _ _).le (by simp [hKdef])
    set E : Mc n := Matrix.single ij.1 ij.2 (1 : ℂ) with hE
    set G : Mc n → ℂ := word L F with hG
    have hGd : ContDiffOn ℂ (⊤ : ℕ∞) G U := contDiffOn_word hU hF L
    set f : ℂ → ℂ := fun w => G (b + w • E) with hf
    have hφ : ∀ w : ℂ, HasDerivAt (fun w : ℂ => b + w • E) E w := by
      intro w
      have h := ((hasDerivAt_id w).smul_const E).const_add b
      rw [one_smul] at h
      exact h
    have hin : ∀ w : ℂ, ‖w‖ ≤ δ → b + w • E ∈ U := fun w hw =>
      hsub (shift_mem b hr ij.1 ij.2 (hw.trans hδr))
    have hdiffG : ∀ x ∈ U, DifferentiableAt ℂ G x := fun x hx =>
      ((hGd.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    have hfd : DifferentiableOn ℂ f (closedBall 0 δ) := by
      intro w hw
      have hw' : ‖w‖ ≤ δ := by simpa using hw
      exact ((hdiffG _ (hin w hw')).hasFDerivAt.comp_hasDerivAt w (hφ w)).differentiableAt.differentiableWithinAt
    have hderiv : deriv f 0 = word (ij :: L) F b := by
      have h0 : b + (0 : ℂ) • E = b := by simp
      have hb : DifferentiableAt ℂ G (b + (0 : ℂ) • E) := by
        rw [h0]; exact hdiffG b (hsub (mem_pdisc_self b hr))
      have h3 : HasDerivAt f (fderiv ℂ G (b + (0 : ℂ) • E) E) 0 := hb.hasFDerivAt.comp_hasDerivAt (0 : ℂ) (hφ 0)
      rw [h3.deriv, h0]
      rfl
    set B : ℝ := (L.map fun ij => K / r ij.1 ij.2).prod * M with hB
    have hsphere : ∀ w ∈ sphere (0 : ℂ) δ, ‖f w‖ ≤ B := by
      intro w hw
      have hw' : ‖w‖ = δ := by simpa using hw
      rcases Nat.eq_zero_or_pos L.length with hL | hL
      · have hLnil : L = [] := List.length_eq_zero_iff.mp hL
        subst hLnil
        show ‖F (b + w • E)‖ ≤ B
        simp only [hB, List.map_nil, List.prod_nil, one_mul]
        exact hM _ (shift_mem b hr ij.1 ij.2 (hw'.le.trans hδr))
      · have hl : (0 : ℝ) < L.length := by exact_mod_cast hL
        set r' : Fin n → Fin n → ℝ := fun a c => r a c * ((L.length : ℝ) / K) with hr'
        have hr'pos : ∀ a c, 0 < r' a c := fun a c => mul_pos (hr a c) (div_pos hl hK)
        have hs := shift_sub b hr ij.1 ij.2 (w := w) hK hl.le (by simp [hKdef]) hw'
        have := ih (b + w • E) r' hr'pos (hs.trans hsub) (fun x hx => hM x (hs hx))
        have heq : (L.map fun ij => (L.length : ℝ) / r' ij.1 ij.2) = (L.map fun ij => K / r ij.1 ij.2) := by
          apply List.map_congr_left
          intro x _
          simp only [hr']
          field_simp
        rw [heq] at this
        exact this
    have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ
      (hfd.diffContOnCl_ball subset_rfl) hsphere
    rw [hderiv] at hc
    calc ‖word (ij :: L) F b‖ ≤ B / δ := hc
      _ = ((ij :: L).map fun ij' => ((ij :: L).length : ℝ) / r ij'.1 ij'.2).prod * M := by
        simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        rw [hB, hδdef, ← hKdef]
        field_simp

theorem cauchyW : CauchyW := by
  intro n F U hU hF b₀ ρ hρ hP M hM L
  exact cauchy_gen hU hF M L b₀ ρ hρ hP hM

end PositivityTheory.Rg.Sw.WR.K.GB
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GBLink
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def hermL (n : ℕ) : (Fin n → Fin n → ℝ) →L[ℝ] Mc n :=
  LinearMap.toContinuousLinearMap
    { toFun := herm
      map_add' := fun x y => by
        ext i j; simp only [herm, Pi.add_apply, Matrix.add_apply]; push_cast; ring
      map_smul' := fun c x => by
        ext i j; simp only [herm, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, RingHom.id_apply]
        rw [Complex.real_smul]; push_cast; ring }

theorem hermL_apply (x : Fin n → Fin n → ℝ) : hermL n x = herm x := rfl

theorem vkl_re (k l a b : Fin n) :
    (vkl k l a b).re = (if a = k ∧ b = l then 1 / 2 else 0) + (if a = l ∧ b = k then 1 / 2 else 0) := by
  unfold vkl; split_ifs <;> simp

theorem vkl_im (k l a b : Fin n) :
    (vkl k l a b).im = (if a = k ∧ b = l then 1 / 2 else 0) + (if a = l ∧ b = k then -1 / 2 else 0) := by
  unfold vkl; split_ifs <;> simp

theorem herm_re_im_vkl (k l : Fin n) :
    herm (fun a b => (vkl k l a b).re) + Complex.I • herm (fun a b => (vkl k l a b).im) =
      Matrix.single l k (1 : ℂ) := by
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply]
  unfold herm
  dsimp only
  rw [vkl_re, vkl_re, vkl_im, vkl_im]
  have e1 : (if j = k ∧ i = l then (1 / 2 : ℝ) else 0) = 1 / 2 * (if i = l ∧ j = k then 1 else 0) := by
    split_ifs <;> first | (exfalso; tauto) | norm_num
  have e2 : (if j = l ∧ i = k then (1 / 2 : ℝ) else 0) = 1 / 2 * (if i = k ∧ j = l then 1 else 0) := by
    split_ifs <;> first | (exfalso; tauto) | norm_num
  have e3 : (if i = k ∧ j = l then (1 / 2 : ℝ) else 0) = 1 / 2 * (if i = k ∧ j = l then 1 else 0) := by
    split_ifs <;> first | (exfalso; tauto) | norm_num
  have e4 : (if i = l ∧ j = k then (1 / 2 : ℝ) else 0) = 1 / 2 * (if i = l ∧ j = k then 1 else 0) := by
    split_ifs <;> first | (exfalso; tauto) | norm_num
  have e5 : (if i = l ∧ j = k then (-1 / 2 : ℝ) else 0) = -1 / 2 * (if i = l ∧ j = k then 1 else 0) := by
    split_ifs <;> first | (exfalso; tauto) | norm_num
  have e6 : (if j = l ∧ i = k then (-1 / 2 : ℝ) else 0) = -1 / 2 * (if i = k ∧ j = l then 1 else 0) := by
    split_ifs <;> first | (exfalso; tauto) | norm_num
  have e7 : (if l = i ∧ k = j then (1 : ℂ) else 0) = (((if i = l ∧ j = k then (1 : ℝ) else 0) : ℝ) : ℂ) := by
    by_cases h : i = l ∧ j = k
    · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]; simp
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]; simp
  rw [e1, e2, e3, e4, e5, e6, e7]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

variable {F G : Mc n → ℂ} {U : Set (Mc n)}

theorem dkl_comp_herm (k l : Fin n) (y : Fin n → Fin n → ℝ) (hd : DifferentiableAt ℂ G (herm y)) :
    Dkl k l (fun y => G (herm y)) y = cpart l k G (herm y) := by
  have hG : HasFDerivAt G ((fderiv ℂ G (herm y)).restrictScalars ℝ) (herm y) :=
    hd.hasFDerivAt.restrictScalars ℝ
  have hc : HasFDerivAt (fun y => G (herm y)) (((fderiv ℂ G (herm y)).restrictScalars ℝ).comp (hermL n)) y :=
    hG.comp y (hermL n).hasFDerivAt
  unfold Dkl dirC cpart
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', hermL_apply]
  rw [← herm_re_im_vkl k l, map_add (f := _), map_smul, smul_eq_mul]

theorem cpart_contDiffOn (i j : Fin n) (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) :
    ContDiffOn ℂ (⊤ : ℕ∞) (cpart i j F) U := by
  have h := hF.fderiv_of_isOpen hU (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by norm_cast)
  exact h.clm_apply contDiffOn_const

theorem differentiableAt_of_cdo (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) {b : Mc n} (hb : b ∈ U) :
    DifferentiableAt ℂ F b :=
  ((hF.contDiffAt (hU.mem_nhds hb)).differentiableAt (by norm_cast))

theorem foldr_herm (τ : Fin n → Fin n) (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (hh : ∀ y, herm y ∈ U)
    (L : List (Fin n)) :
    L.foldr (fun k g => Dkl k (τ k) g) (fun y => F (herm y)) =
        (fun y => (L.foldr (fun k g => cpart (τ k) k g) F) (herm y)) ∧
      ContDiffOn ℂ (⊤ : ℕ∞) (L.foldr (fun k g => cpart (τ k) k g) F) U := by
  induction L with
  | nil => exact ⟨rfl, hF⟩
  | cons a L ih =>
    refine ⟨?_, cpart_contDiffOn _ _ hU ih.2⟩
    simp only [List.foldr_cons]
    rw [ih.1]
    funext y
    exact dkl_comp_herm a (τ a) y (differentiableAt_of_cdo hU ih.2 (hh y))

theorem deltaC_contDiffOn (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) :
    ContDiffOn ℂ (⊤ : ℕ∞) (DeltaC F) U := by
  have : DeltaC F = fun b => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (List.finRange n).foldr (fun k g => cpart (σ k) k g) F b := by
    funext b; simp [DeltaC, Finset.sum_apply]
  rw [this]
  refine ContDiffOn.sum fun σ _ => ContDiffOn.const_smul _ ?_
  have key : ∀ L : List (Fin n), ContDiffOn ℂ (⊤ : ℕ∞) (L.foldr (fun k g => cpart (σ k) k g) F) U := by
    intro L; induction L with
    | nil => exact hF
    | cons a L ih => exact cpart_contDiffOn _ _ hU ih
  exact key _

theorem delta_herm (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (hh : ∀ y, herm y ∈ U) :
    Delta (fun y => F (herm y)) = fun y => DeltaC F (herm y) := by
  funext y
  simp only [Delta, DeltaC, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [(foldr_herm σ hU hF hh _).1]

theorem iterate_herm (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (hh : ∀ y, herm y ∈ U) (N : ℕ) :
    (Delta^[N] (fun y => F (herm y))) = (fun y => (DeltaC^[N] F) (herm y)) ∧
      ContDiffOn ℂ (⊤ : ℕ∞) (DeltaC^[N] F) U := by
  induction N with
  | zero => exact ⟨rfl, hF⟩
  | succ N ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih.1]
    exact ⟨delta_herm hU ih.2 hh, deltaC_contDiffOn hU ih.2⟩

theorem eqOn_cpart (i j : Fin n) (hU : IsOpen U) {H H' : Mc n → ℂ} (h : Set.EqOn H H' U) :
    Set.EqOn (cpart i j H) (cpart i j H') U := fun b hb => by
  have : H =ᶠ[nhds b] H' := Filter.eventuallyEq_of_mem (hU.mem_nhds hb) h
  simp only [cpart, this.fderiv_eq]

theorem eqOn_word (L : List (Fin n × Fin n)) (hU : IsOpen U) {H H' : Mc n → ℂ} (h : Set.EqOn H H' U) :
    Set.EqOn (word L H) (word L H') U := by
  induction L with
  | nil => exact h
  | cons a L ih => exact eqOn_cpart a.1 a.2 hU ih

theorem word_contDiffOn (L : List (Fin n × Fin n)) (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) :
    ContDiffOn ℂ (⊤ : ℕ∞) (word L F) U := by
  induction L with
  | nil => exact hF
  | cons a L ih => exact cpart_contDiffOn _ _ hU ih

theorem cpart_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → Mc n → ℂ) (i j : Fin n) (hU : IsOpen U)
    (hf : ∀ t, ContDiffOn ℂ (⊤ : ℕ∞) (f t) U) :
    Set.EqOn (cpart i j (fun x => ∑ t ∈ s, c t * f t x)) (fun x => ∑ t ∈ s, c t * cpart i j (f t) x) U := by
  intro b hb
  have hd : ∀ t ∈ s, DifferentiableAt ℂ (fun x => c t * f t x) b := fun t _ =>
    (differentiableAt_of_cdo hU (hf t) hb).const_mul (c t)
  simp only [cpart]
  have hs : HasFDerivAt (fun x => ∑ t ∈ s, c t * f t x) (∑ t ∈ s, fderiv ℂ (fun x => c t * f t x) b) b :=
    HasFDerivAt.fun_sum (fun t ht => (hd t ht).hasFDerivAt)
  rw [hs.fderiv, _root_.sum_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : HasFDerivAt (fun x => c t * f t x) (c t • fderiv ℂ (f t) b) b :=
    (differentiableAt_of_cdo hU (hf t) hb).hasFDerivAt.const_mul (c t)
  rw [h1.fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem word_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → Mc n → ℂ) (L : List (Fin n × Fin n))
    (hU : IsOpen U) (hf : ∀ t, ContDiffOn ℂ (⊤ : ℕ∞) (f t) U) :
    Set.EqOn (word L (fun x => ∑ t ∈ s, c t * f t x)) (fun x => ∑ t ∈ s, c t * word L (f t) x) U := by
  induction L with
  | nil => intro b _; rfl
  | cons a L ih =>
    intro b hb
    have h1 := eqOn_cpart a.1 a.2 hU ih hb
    simp only [word, List.foldr_cons] at h1 ⊢
    rw [h1]
    exact cpart_sum s c (fun t => word L (f t)) a.1 a.2 hU (fun t => word_contDiffOn L hU (hf t)) hb

theorem word_append (L₁ L₂ : List (Fin n × Fin n)) (H : Mc n → ℂ) :
    word (L₁ ++ L₂) H = word L₁ (word L₂ H) := by
  simp [word, List.foldr_append]

def blk (σ : Equiv.Perm (Fin n)) : List (Fin n × Fin n) := (List.finRange n).map fun k => (σ k, k)

theorem deltaC_eq_word (H : Mc n → ℂ) :
    DeltaC H = fun b => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * word (blk σ) H b := by
  funext b
  simp only [DeltaC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, word, blk, List.foldr_map]

theorem flat_succ {N : ℕ} (τ : Fin (N + 1) → Equiv.Perm (Fin n)) :
    (List.finRange (N + 1)).flatMap (fun j => blk (τ j)) =
      blk (τ 0) ++ (List.finRange N).flatMap (fun j => blk (τ j.succ)) := by
  rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map]

theorem deltaC_iter_word (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (N : ℕ) :
    Set.EqOn (DeltaC^[N] F) (fun b => ∑ τ : Fin N → Equiv.Perm (Fin n),
      ((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ) *
        word ((List.finRange N).flatMap fun j => blk (τ j)) F b) U := by
  induction N with
  | zero => intro b _; simp [word]
  | succ N ih =>
    intro b hb
    rw [Function.iterate_succ_apply', deltaC_eq_word]
    dsimp only
    have step : ∀ σ : Equiv.Perm (Fin n), word (blk σ) (DeltaC^[N] F) b =
        ∑ τ : Fin N → Equiv.Perm (Fin n), ((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ) *
          word (blk σ ++ (List.finRange N).flatMap fun j => blk (τ j)) F b := by
      intro σ
      rw [eqOn_word (blk σ) hU ih hb]
      have hw := word_sum (Finset.univ : Finset (Fin N → Equiv.Perm (Fin n)))
        (fun τ => ((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ))
        (fun τ => word ((List.finRange N).flatMap fun j => blk (τ j)) F) (blk σ) hU
        (fun τ => word_contDiffOn _ hU hF) hb
      rw [hw]
      simp only [word_append]
    simp only [step, Finset.mul_sum]
    rw [← (Fin.consEquiv fun _ => Equiv.Perm (Fin n)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
    simp only [Fin.consEquiv_apply, flat_succ, Fin.cons_zero, Fin.cons_succ, Fin.prod_univ_succ]
    push_cast
    ring

theorem link : Link := by
  intro n F U hU hF hh
  exact ⟨fun N y => by rw [(iterate_herm hU hF hh N).1],
    fun N b hb => (deltaC_iter_word hU hF N hb).trans (by simp only [blk])⟩

end PositivityTheory.Rg.Sw.WR.K.GB
end
end

namespace PositivityTheory.Rg.Sw.WR.K.GB

theorem clsGainB : PositivityTheory.Rg.Sw.WR.ClsGain := clsGainB_of cauchyW invar pBound link twist lagr

end PositivityTheory.Rg.Sw.WR.K.GB
