module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.KernInvariantSymmPos
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPlaceKernelHolomorphicWeightRowHighest
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LowestWeightFunctionMulEq
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MeasurePreservingMulLeft
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IntegrableOnMinorFin

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExtendByZeroAntitoneOffBreak
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.LowestBound

noncomputable def rowMix {r : ℕ} (k : ℕ) (Y : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j => if (i : ℕ) < k then Y i j else (1 : Matrix (Fin r) (Fin r) ℂ) i j

theorem det_rowMix {r : ℕ} (Y : Matrix (Fin r) (Fin r) ℂ) (k : Fin (r + 1)) :
    (rowMix k Y).det = lminor Y k := by
  have h := Nat.le_of_lt_succ k.isLt
  rw [Matrix.twoBlockTriangular_det (rowMix k Y) (fun i => (i : ℕ) < k) (fun i hi j hj => by
    have : i ≠ j := fun e => hi (e ▸ hj)
    simp [rowMix, hi, Matrix.one_apply_ne this])]
  have e1 : toSquareBlockProp (rowMix k Y) (fun i => ¬ (i : ℕ) < k) = 1 := by
    ext i j
    simp [toSquareBlockProp_def, rowMix, i.2, Matrix.one_apply, Subtype.ext_iff]
  rw [e1, det_one, mul_one, lminor,
    ← Matrix.det_submatrix_equiv_self (Fin.castLEquiv h)]
  congr 1
  ext i j
  simp [toSquareBlockProp_def, rowMix]

theorem norm_lminor_le {r p : ℕ} (h : p ≤ r) (Y : Matrix (Fin r) (Fin r) ℂ)
    (hY : Yᵀ * (Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) * Y.map (starRingEnd ℂ) =
      Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) (k : Fin (r + 1)) :
    ‖lminor Y k‖ ≤ ‖lminor Y ⟨p, Nat.lt_succ_of_le h⟩‖ := by
  have h1 := FramePotential.one_le_norm_lminor_sq h Y hY
  have h0 : lminor Y ⟨p, Nat.lt_succ_of_le h⟩ ≠ 0 := by
    intro e; rw [e] at h1; norm_num at h1
  set N := rowMix p Y with hN
  have hNd : N.det = lminor Y ⟨p, Nat.lt_succ_of_le h⟩ := det_rowMix Y ⟨p, Nat.lt_succ_of_le h⟩
  have hu : IsUnit N.det := isUnit_iff_ne_zero.2 (hNd ▸ h0)
  set N' : Matrix (Fin r) (Fin r) ℂ :=
    Matrix.of fun i j => if (i : ℕ) < p then (1 : Matrix (Fin r) (Fin r) ℂ) i j else Y i j with hN'
  have hNN : N'ᴴ * N' = Nᴴ * N := by
    ext a b
    have e := congrFun (congrFun hY b) a
    rw [Matrix.mul_apply] at e
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply] at e
    have e2 : (Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) b a =
        ∑ k, (1 : Matrix (Fin r) (Fin r) ℂ) k b * ((sgn p (k : ℕ) : ℝ) : ℂ) *
          conj ((1 : Matrix (Fin r) (Fin r) ℂ) k a) := by
      rw [Finset.sum_eq_single b (fun c _ hc => by simp [Matrix.one_apply_ne hc]) (by simp)]
      by_cases hab : b = a
      · subst hab; simp
      · simp [hab]
    rw [e2, ← sub_eq_zero, ← Finset.sum_sub_distrib] at e
    rw [Matrix.mul_apply, Matrix.mul_apply, eq_comm, ← sub_eq_zero, ← Finset.sum_sub_distrib, ← e]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : (k : ℕ) < p
    · simp [hN, hN', rowMix, sgn, hk, Matrix.conjTranspose_apply, mul_comm]
    · simp [hN, hN', rowMix, sgn, hk, Matrix.conjTranspose_apply, mul_comm]
      ring
  set U := N' * N⁻¹ with hU
  have hUU : Uᴴ * U = 1 := by
    rw [hU, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc N'ᴴ, hNN, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, ← conjTranspose_mul,
      Matrix.mul_nonsing_inv _ hu, conjTranspose_one]
  have hUU' : U * Uᴴ = 1 := mul_eq_one_comm.1 hUU
  have hrow : ∀ i, ∑ j, ‖U i j‖ ^ 2 = 1 := by
    intro i
    have e := congrFun (congrFun hUU' i) i
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at e
    simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj'] at e
    exact_mod_cast e
  have hrow1 : ∀ i, ∑ j, ‖(N * N⁻¹) i j‖ ^ 2 = 1 := by
    intro i
    rw [Matrix.mul_nonsing_inv _ hu,
      Finset.sum_eq_single i (fun c _ hc => by simp [Matrix.one_apply_ne' hc]) (by simp)]
    simp
  have hM : ‖(rowMix k Y * N⁻¹).det‖ ≤ 1 := by
    refine (Hadamard.norm_det_le_prod_row _).trans_eq (Finset.prod_eq_one fun i _ => ?_)
    rw [Real.sqrt_eq_one]
    by_cases hi : ((i : ℕ) < k ↔ (i : ℕ) < p)
    · rw [← hrow1 i]
      simp only [Matrix.mul_apply, hN, rowMix, Matrix.of_apply, hi]
    · rw [← hrow i]
      have hi' : (i : ℕ) < k ↔ ¬ (i : ℕ) < p := by tauto
      simp only [hU, Matrix.mul_apply, hN', rowMix, Matrix.of_apply, hi', ite_not]
  rw [det_mul, det_rowMix, det_nonsing_inv, Ring.inverse_eq_inv', hNd, norm_mul, norm_inv,
    ← div_eq_mul_inv, div_le_one (norm_pos_iff.2 h0)] at hM
  exact hM

theorem norm_det_eq_one {r p : ℕ} (Y : Matrix (Fin r) (Fin r) ℂ)
    (hY : Yᵀ * (Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) * Y.map (starRingEnd ℂ) =
      Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) : ‖Y.det‖ = 1 := by
  have e := congrArg (fun M => ‖M.det‖) hY
  have e1 : ‖(Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)).det‖ = 1 := by
    rw [det_diagonal, norm_prod]
    refine Finset.prod_eq_one fun a _ => ?_
    unfold sgn; split_ifs <;> simp
  have e2 : (Y.map (starRingEnd ℂ)).det = conj Y.det := ((starRingEnd ℂ).map_det Y).symm
  simp only [det_mul, norm_mul, e1, e2, det_transpose, Complex.norm_conj, mul_one] at e
  nlinarith [norm_nonneg Y.det]

theorem prod_zpow_sub (t : ℕ → ℂ) (L : ℕ → ℤ) (r : ℕ) (ht : ∀ j < r, t j ≠ 0) :
    (∏ k ∈ Finset.range r, (∏ j ∈ Finset.range (k + 1), t j) ^ (L k - L (k + 1))) *
      (∏ j ∈ Finset.range r, t j) ^ L r = ∏ j ∈ Finset.range r, t j ^ L j := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h0 : ∏ j ∈ Finset.range (r + 1), t j ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j hj => ht j (Finset.mem_range.1 hj)
    rw [Finset.prod_range_succ, mul_assoc, ← zpow_add₀ h0, sub_add_cancel,
      Finset.prod_range_succ t, mul_zpow, ← mul_assoc, ih fun j hj => ht j (by omega),
      Finset.prod_range_succ]

def ext0 {r : ℕ} (la : Fin r → ℤ) (j : ℕ) : ℤ := if h : j < r then la ⟨j, h⟩ else 0

noncomputable def minorProd {r : ℕ} (la : Fin r → ℤ) (Y : Matrix (Fin r) (Fin r) ℂ) : ℂ :=
  ∏ k : Fin r, lminor Y k.succ ^ (ext0 la k - ext0 la (k + 1))

theorem minorProd_scale {r : ℕ} (la : Fin r → ℤ) (Y Y' : Matrix (Fin r) (Fin r) ℂ) (t : Fin r → ℂ)
    (ht : ∀ i, t i ≠ 0) (h : ∀ k : Fin (r + 1), lminor Y' k =
      lminor Y k * ∏ j : Fin k, t (Fin.castLE (Nat.le_of_lt_succ k.isLt) j)) :
    minorProd la Y' = (∏ i, t i ^ la i) * minorProd la Y := by
  set s : ℕ → ℂ := fun j => if h : j < r then t ⟨j, h⟩ else 1 with hs
  have key := prod_zpow_sub s (ext0 la) r (fun j hj => by simp [hs, hj, ht])
  have e0 : ext0 la r = 0 := by simp [ext0]
  rw [e0, zpow_zero, mul_one, Finset.prod_range, Finset.prod_range] at key
  have e1 : ∏ i, t i ^ la i = ∏ i : Fin r, s i ^ ext0 la i :=
    Finset.prod_congr rfl fun i _ => by simp [hs, ext0]
  rw [e1, ← key, minorProd, minorProd, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [h, mul_zpow, mul_comm, Finset.prod_range]
  congr 2
  refine Finset.prod_congr rfl fun j _ => ?_
  have hj : (j : ℕ) < r := by have := j.isLt; have := k.isLt; simp only [Fin.val_succ] at *; omega
  simp only [hs, hj, dif_pos]
  rfl

theorem lminor_diagonal_mul {r : ℕ} (t : Fin r → ℂ) (Y : Matrix (Fin r) (Fin r) ℂ)
    (k : Fin (r + 1)) : lminor (Matrix.diagonal t * Y) k =
      lminor Y k * ∏ j : Fin k, t (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) := by
  rw [lminor, lminor, mul_comm, ← det_diagonal, ← det_mul]
  congr 1
  ext a b
  simp [Matrix.diagonal_mul]

theorem extendByZero_antitone_off_break {r p : ℕ} (la : Fin r → ℤ)
    (h1 : ∀ i j : Fin r, i ≤ j → (j : ℕ) < p → la j ≤ la i)
    (h2 : ∀ i j : Fin r, p ≤ (i : ℕ) → i ≤ j → la j ≤ la i) {k : ℕ} (hk : k + 1 < r)
    (hp : k + 1 ≠ p) : 0 ≤ ext0 la k - ext0 la (k + 1) := by
  have hk' : k < r := by omega
  simp only [ext0, hk, hk', dif_pos, sub_nonneg]
  rcases lt_or_gt_of_ne hp with h | h
  · exact h1 _ _ (by simp [Fin.le_def]) h
  · exact h2 _ _ (by simp only; omega) (by simp [Fin.le_def])

theorem norm_minorProd_le {r p : ℕ} (h : p ≤ r) (la : Fin r → ℤ) (n : ℕ)
    (h1 : ∀ i j : Fin r, i ≤ j → (j : ℕ) < p → la j ≤ la i)
    (h2 : ∀ i j : Fin r, p ≤ (i : ℕ) → i ≤ j → la j ≤ la i)
    (h3 : ∀ i j : Fin r, (i : ℕ) < p → p ≤ (j : ℕ) → la i + n ≤ la j)
    (Y : Matrix (Fin r) (Fin r) ℂ)
    (hY : Yᵀ * (Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) * Y.map (starRingEnd ℂ) =
      Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) :
    ‖minorProd la Y‖ * ‖lminor Y ⟨p, Nat.lt_succ_of_le h⟩‖ ^ n ≤ 1 := by
  set δ := ‖lminor Y ⟨p, Nat.lt_succ_of_le h⟩‖ with hδ
  have hδ1 : 1 ≤ δ := by
    have := FramePotential.one_le_norm_lminor_sq h Y hY
    nlinarith [norm_nonneg (lminor Y ⟨p, Nat.lt_succ_of_le h⟩)]
  have hδ0 : 0 < δ := by linarith
  have hlast : ∀ k : Fin (r + 1), (k : ℕ) = r → ‖lminor Y k‖ = 1 := by
    intro k hk
    obtain rfl : k = Fin.last r := Fin.ext hk
    rw [← norm_det_eq_one Y hY]
    rfl
  set M : ℕ → ℤ := fun k => ext0 la (min k (r - 1)) with hM
  have hb : ‖minorProd la Y‖ ≤ δ ^ (M 0 - M r) := by
    have hz : ∀ s : Finset ℕ, ∀ g : ℕ → ℤ, δ ^ (∑ k ∈ s, g k) = ∏ k ∈ s, δ ^ g k := by
      intro s g
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hδ0.ne', ih]
    rw [← Finset.sum_range_sub' M r, hz, Finset.prod_range, minorProd, norm_prod]
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun k _ => ?_
    have hk := k.isLt
    rw [norm_zpow]
    by_cases hk' : (k : ℕ) + 1 = r
    · rw [hlast _ hk', _root_.one_zpow]
      simp only [hM]
      rw [show min ((k : ℕ) + 1) (r - 1) = min (k : ℕ) (r - 1) by omega, sub_self, zpow_zero]
    simp only [hM]
    rw [show min ((k : ℕ) + 1) (r - 1) = k + 1 by omega, show min (k : ℕ) (r - 1) = k by omega]
    by_cases hp : (k : ℕ) + 1 = p
    · have : k.succ = ⟨p, Nat.lt_succ_of_le h⟩ := Fin.ext hp
      rw [this]
    · exact zpow_le_zpow_left₀ (extendByZero_antitone_off_break la h1 h2 (by omega) hp) (norm_nonneg _)
        (norm_lminor_le h Y hY _)
  refine (mul_le_mul_of_nonneg_right hb (by positivity)).trans ?_
  rw [← zpow_natCast, ← zpow_add₀ hδ0.ne']
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have : δ = 1 := by simp [hδ, lminor]
    simp [this]
  rcases h.eq_or_lt with rfl | hpr
  · have : δ = 1 := hlast _ rfl
    simp [this]
  refine zpow_le_one_of_nonpos₀ hδ1 ?_
  have := h3 ⟨0, by omega⟩ ⟨r - 1, by omega⟩ hp (by simp only; omega)
  have e1 : M 0 = la ⟨0, by omega⟩ := by simp [hM, ext0, show 0 < r by omega]
  have e2 : M r = la (⟨r - 1, by omega⟩ : Fin r) := by simp [hM, ext0, show r - 1 < r by omega]
  omega

theorem differentiable_lminor {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℂ) (τ : Ψ) (k : Fin (r + 1)) :
    Differentiable ℂ fun x : Frame Ψ r => lminor (A * mat x τ) k := by
  simp only [lminor, det_apply', submatrix_apply, Matrix.mul_apply, mat, Matrix.of_apply]
  fun_prop

theorem differentiableAt_prod {V ι : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (s : Finset ι)
    {g : ι → V → ℂ} {y : V} (h : ∀ i ∈ s, DifferentiableAt ℂ (g i) y) :
    DifferentiableAt ℂ (fun x => ∏ i ∈ s, g i x) y := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end GlobalTheory.LowestBound

theorem GlobalTheory.lowest_weight_function_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (q0 : ℕ) (hr : X.p0 + q0 = r) (n : ℕ) (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (x₀ : Frame X.Ψ r), Even n → (∀ τ : X.Ψ, gram τ.1 X.Gm (mat x₀ τ) = sgnM X) → ∀ f : Frame X.Ψ r → ℂ, DifferentiableOn ℂ f X.dom → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, f (rmul x b) = bchar (wtOf X hr c c' n) b * f x) → (∀ t : X.Ψ → Fin r → ℂ, (∀ τ i, ‖t τ i‖ = 1) → ∀ x ∈ X.dom, f (X.lmulC (fun τ => mat x₀ τ * Matrix.diagonal (t τ) * (mat x₀ τ)⁻¹) x) = (∏ τ, ∏ i, t τ i ^ wtOf X hr c c' n τ i) * f x) → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = sgnM X) → ‖f x‖ * ∏ τ, ‖lminor ((mat x₀ τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ ^ n ≤ ‖f x₀‖ := by
  intro E _ _ _ r X q0 hr n c c' x₀ hn hx₀ f hf hB hT x hx
  have hdom : ∀ {y : Frame X.Ψ r}, AR.Up.IsOrth X y → y ∈ X.dom := by
    intro y ho
    refine AR.Up.ExF.mem_dom_of_gramPos X fun τ => ⟨AR.Up.ExF.det_ne_of_orth X ho τ, ?_⟩
    have e : X.gramPos y τ = 1 := by
      ext a b
      simp only [Data.gramPos, ho τ, Matrix.submatrix_apply, Matrix.diagonal_apply,
        Matrix.one_apply, Fin.castLE_inj]
      split_ifs <;> simp [sgn]
    rw [e]; exact Matrix.PosDef.one
  have h₀ : x₀ ∈ X.dom := hdom hx₀
  have hu : ∀ τ, IsUnit (mat x₀ τ).det := fun τ => isUnit_iff_ne_zero.2 (h₀ τ).1
  set la := wtOf X hr c c' n with hla
  have hd : X.IsDominant la := wtOf_isDominant X hr c c' n
  set m : Frame X.Ψ r → ℂ :=
    fun y => ∏ τ, LowestBound.minorProd (la τ) ((mat x₀ τ)⁻¹ * mat y τ) with hm
  have hm0 : m x₀ = 1 := by
    refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun k _ => ?_
    rw [Matrix.nonsing_inv_mul _ (hu τ), AR.Up.LUPf.lminor_one, _root_.one_zpow]
  have hmd : DifferentiableOn ℂ m X.dom := by
    intro y hy
    refine DifferentiableAt.differentiableWithinAt ?_
    simp only [hm, LowestBound.minorProd]
    refine LowestBound.differentiableAt_prod _ fun τ _ =>
      LowestBound.differentiableAt_prod _ fun k _ => ?_
    refine (LowestBound.differentiable_lminor _ τ _ y).zpow ?_
    by_cases hk : (k : ℕ) + 1 = X.p0
    · left
      have : k.succ = ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ := Fin.ext hk
      rw [this]
      exact Up.lminor_inv_mul_ne_zero hx₀ hy τ
    by_cases hk' : (k : ℕ) + 1 = r
    · left
      have : k.succ = Fin.last r := Fin.ext hk'
      rw [this]
      change ((mat x₀ τ)⁻¹ * mat y τ).det ≠ 0
      rw [det_mul, det_nonsing_inv, Ring.inverse_eq_inv']
      exact mul_ne_zero (inv_ne_zero (h₀ τ).1) (hy τ).1
    · right
      exact LowestBound.extendByZero_antitone_off_break _ (hd τ).1 (hd τ).2.1 (by have := k.isLt; omega) hk
  have key := lowest_weight_function_mul_eq X la x₀ hx₀ h₀ f m hf hmd hB (fun y _ b hb => ?_) hT
    (fun t ht y _ => ?_) x (hdom hx)
  · rw [hm0, mul_one] at key
    rw [key, norm_mul, mul_right_comm]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    rw [hm, norm_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_one₀ (fun τ _ => by positivity) fun τ _ => ?_
    refine LowestBound.norm_minorProd_le X.p0_le (la τ) n (hd τ).1 (hd τ).2.1 (fun i j hi hj => ?_)
      _ ?_
    · obtain ⟨i | i, rfl⟩ := (rowIdx hr).surjective i <;>
        obtain ⟨j | j, rfl⟩ := (rowIdx hr).surjective j <;>
        have hi' := i.isLt <;> have hj' := j.isLt <;>
        simp only [rowIdx_inl, rowIdx_inr, hla, wtOf_inl, wtOf_inr] at hi hj ⊢ <;>
        obtain ⟨s, rfl⟩ := hn <;> omega
    · have e := FrameDegreeData.gram_mul τ.1 X.Gm (mat x₀ τ) ((mat x₀ τ)⁻¹ * mat x τ)
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ (hu τ), hx τ, hx₀ τ] at e
      exact e.symm
  · simp only [hm, bchar]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    refine LowestBound.minorProd_scale _ _ _ (fun i => b τ i i) (FrameDegreeData.bdiag_ne X hb τ) fun k => ?_
    change lminor ((mat x₀ τ)⁻¹ * (mat y τ * mat b τ)) k = _
    rw [← Matrix.mul_assoc, FramePotential.lminor_mul_upper _ (FrameDegreeData.upper_of_bor X hb τ)]
    rfl
  · simp only [hm]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    refine LowestBound.minorProd_scale _ _ _ (t τ)
      (fun i => norm_ne_zero_iff.1 (by rw [ht τ i]; exact one_ne_zero)) fun k => ?_
    change lminor ((mat x₀ τ)⁻¹ * (mat x₀ τ * Matrix.diagonal (t τ) * (mat x₀ τ)⁻¹ * mat y τ)) k = _
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (hu τ),
      LowestBound.lminor_diagonal_mul]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GaussianKernelIntegrableOnThinSlab
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.KernInt

theorem norm_zpow_le {z : ℂ} {C : ℝ} (h1 : ‖z‖ ≤ C) (h2 : ‖z⁻¹‖ ≤ C) (k : ℤ) :
    ‖z ^ k‖ ≤ C ^ k.natAbs := by
  cases k with
  | ofNat k =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast, Int.natAbs_natCast, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 _
  | negSucc k =>
    rw [zpow_negSucc, ← inv_pow, norm_pow, Int.natAbs_negSucc]
    exact pow_le_pow_left₀ (norm_nonneg _) h2 _

theorem integrableOn_comp_linearEquiv {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W]
    (μ : Measure V) (ν : Measure W) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] (L : V ≃ₗ[ℂ] W)
    {g : W → ℝ} {S : Set W} (h : IntegrableOn g S ν) : IntegrableOn (g ∘ L) (L ⁻¹' S) μ := by
  let L' := L.toContinuousLinearEquiv
  have _ : (μ.map L').IsAddHaarMeasure := L'.isAddHaarMeasure_map μ
  have e := Measure.isAddLeftInvariant_eq_smul (μ.map L') ν
  have h2 : IntegrableOn g S (μ.map L') := by
    rw [e, IntegrableOn, Measure.restrict_smul]
    exact h.smul_measure_nnreal
  exact (L'.toHomeomorph.measurableEmbedding.integrableOn_map_iff).1 h2

theorem integrableOn_place {r p q n : ℕ} (hr : p + q = r) (hp : p ≤ r) (hn : 2 * r ≤ n) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ A : Matrix (Fin r) (Fin r) ℂ, IsUnit A.det →
      IntegrableOn (fun x : Fin r → Fin r → ℂ =>
        (‖lminor (A * Matrix.of x) ⟨p, Nat.lt_succ_of_le hp⟩‖ ^ n)⁻¹)
      {x | ∀ a b, ‖((A * Matrix.of x)ᵀ * (Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) *
        (A * Matrix.of x).map conj) a b -
        (Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) a b‖ < δ₀} volume := by
  subst hr
  obtain ⟨δ₀, h0, h⟩ := GlobalTheory.T.integrableOn_inv_norm_det_pow_near_indefinite_gram p q n hn
  refine ⟨δ₀, h0, fun A hA => ?_⟩
  let e : Fin p ⊕ Fin q ≃ Fin (p + q) := finSumFinEquiv
  let L : (Fin (p + q) → Fin (p + q) → ℂ) ≃ₗ[ℂ] ((Fin p ⊕ Fin q) → (Fin p ⊕ Fin q) → ℂ) :=
    { toFun := fun x => (A * Matrix.of x).submatrix e e
      invFun := fun y => (A⁻¹ * (Matrix.of y).submatrix e.symm e.symm : Matrix _ _ ℂ)
      map_add' := fun x y => by
        change (A * (Matrix.of x + Matrix.of y)).submatrix e e = _
        rw [Matrix.mul_add]; rfl
      map_smul' := fun c x => by
        change (A * (c • Matrix.of x)).submatrix e e = _
        rw [Matrix.mul_smul]; rfl
      left_inv := fun x => by
        change A⁻¹ * ((A * Matrix.of x).submatrix e e).submatrix e.symm e.symm = Matrix.of x
        rw [Matrix.submatrix_submatrix, e.self_comp_symm, Matrix.submatrix_id_id,
          Matrix.nonsing_inv_mul_cancel_left _ _ hA]
      right_inv := fun y => by
        change (A * (A⁻¹ * (Matrix.of y).submatrix e.symm e.symm)).submatrix e e = Matrix.of y
        rw [Matrix.mul_nonsing_inv_cancel_left _ _ hA,
          Matrix.submatrix_submatrix, e.symm_comp_self, Matrix.submatrix_id_id] }
  have _ : (volume : Measure (Fin (p + q) → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have _ : (volume : Measure (Fin (p + q) → Fin (p + q) → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have _ : (volume : Measure (Fin p ⊕ Fin q → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have _ : (volume : Measure ((Fin p ⊕ Fin q) → (Fin p ⊕ Fin q) → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have hS : Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (-1 : Matrix (Fin q) (Fin q) ℂ) =
      (Matrix.diagonal fun a : Fin (p + q) => ((sgn p (a : ℕ) : ℝ) : ℂ)).submatrix e e := by
    rw [Matrix.submatrix_diagonal_equiv]
    ext (a | a) (b | b) <;> simp [Matrix.diagonal_apply, Matrix.one_apply, sgn, e]
    split_ifs <;> simp
  refine (integrableOn_comp_linearEquiv volume volume L h).mono_set fun x hx a b => ?_
  have e1 : Matrix.of (L x) = (A * Matrix.of x).submatrix e e := rfl
  rw [e1, hS, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, ← Matrix.submatrix_map,
    Matrix.submatrix_mul_equiv]
  exact hx _ _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem gram_inv_mul {x₀ : Frame X.Ψ r} (hx₀ : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x₀ τ) = sgnM X)
    (τ : X.Ψ) (hu : IsUnit (mat x₀ τ).det) (y : Matrix (Fin r) (Fin r) ℂ) :
    ((mat x₀ τ)⁻¹ * y)ᵀ * sgnM X * ((mat x₀ τ)⁻¹ * y).map conj = gram τ.1 X.Gm y := by
  have e := FrameDegreeData.gram_mul τ.1 X.Gm (mat x₀ τ) ((mat x₀ τ)⁻¹ * y)
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ hu, hx₀ τ] at e
  exact e.symm

theorem hermC_eq_gram (τ : E →+* ℂ) (A : Matrix (Fin r) (Fin r) ℂ) (v w : Fin r → ℂ) :
    hermC τ X.Gm (A *ᵥ v) (A *ᵥ w) = ∑ a, ∑ b, v a * gram τ X.Gm A a b * conj (w b) := by
  have e : ∀ v w : Fin r → ℂ, ∀ M : Matrix (Fin r) (Fin r) ℂ,
      ∑ a, ∑ b, v a * M a b * conj (w b) = v ⬝ᵥ M *ᵥ star w := fun v w M => by
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [e, FrameDegreeData.gram_eq]
  refine (e _ _ (X.Gm.map τ)).trans ?_
  rw [Matrix.star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec v, Matrix.vecMul_transpose, ← Matrix.mulVec_transpose]
  rfl

theorem torus_unitary {x₀ : Frame X.Ψ r} (hx₀ : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x₀ τ) = sgnM X)
    (τ : X.Ψ) (hu : IsUnit (mat x₀ τ).det) (t : Fin r → ℂ) (ht : ∀ i, ‖t i‖ = 1) (v w : Fin r → ℂ) :
    hermC τ.1 X.Gm ((mat x₀ τ * Matrix.diagonal t * (mat x₀ τ)⁻¹) *ᵥ v)
      ((mat x₀ τ * Matrix.diagonal t * (mat x₀ τ)⁻¹) *ᵥ w) = hermC τ.1 X.Gm v w := by
  have e : gram τ.1 X.Gm (mat x₀ τ * Matrix.diagonal t * (mat x₀ τ)⁻¹) = gram τ.1 X.Gm 1 := by
    have e1 : gram τ.1 X.Gm (mat x₀ τ * Matrix.diagonal t) = gram τ.1 X.Gm (mat x₀ τ) := by
      rw [FrameDegreeData.gram_mul, hx₀ τ, sgnM, Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero _),
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      rw [mul_right_comm, Complex.mul_conj', ht]
      simp
    rw [FrameDegreeData.gram_mul, e1, ← FrameDegreeData.gram_mul, Matrix.mul_nonsing_inv _ hu]
  rw [hermC_eq_gram, e, ← hermC_eq_gram, Matrix.one_mulVec, Matrix.one_mulVec]

end GlobalTheory.SW.KernInt

theorem GlobalTheory.SW.kern_integrableOn_slab : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ) (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (m : ℕ) (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), Even n → (∀ j, P j ∈ Harm.rowHighest ℂ c c') → 2 * r ≤ n → ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ → ∀ x₁ ∈ X.dom, IntegrableOn (fun x₂ => kern X hr idx P x₁ x₂) (slab X δ) volume ∧ ∃ C : ℝ, ∀ x₂ ∈ slab X δ, ‖kern X hr idx P x₁ x₂‖ ≤ C := by
  intro E _ _ _ r X g q0 hr idx n c c' m P hn hP h2
  obtain ⟨δa, ha, hA⟩ := thin_slab E r X
  obtain ⟨δb, hb, hB⟩ := KernInt.integrableOn_place hr X.p0_le h2
  refine ⟨min δa δb, lt_min ha hb, fun δ hδ hδ1 x₁ hx₁ => ?_⟩
  obtain ⟨hopen, hsub, horth, -, hun, ⟨C, hC⟩, hdec⟩ := hA δ hδ (hδ1.trans (min_le_left _ _))
  obtain ⟨x₀, hx₀, b₁, hb₁, rfl⟩ := hdec x₁ hx₁
  obtain ⟨hinv, hsym, -⟩ := kern_invariant_symm_pos E r X g q0 hr idx n c c' m P hn hP
  have hhol := KernHol.kern_hol_weight E r X g q0 hr idx n c c' m P hn hP
  have h₀ : x₀ ∈ X.dom := hsub (horth x₀ hx₀)
  have hu : ∀ τ, IsUnit (mat x₀ τ).det := fun τ => isUnit_iff_ne_zero.2 (h₀ τ).1
  set la := wtOf X hr c c' n with hla
  set f : Frame X.Ψ r → ℂ := fun x => kern X hr idx P x x₀ with hf
  have hbd := lowest_weight_function_bound E r X q0 hr n c c' x₀ hn hx₀ f (hhol x₀ h₀).1
    (hhol x₀ h₀).2 (fun t ht x hx => by
      have ht0 : ∀ τ i, t τ i ≠ 0 := fun τ i => norm_ne_zero_iff.1 (by rw [ht τ i]; exact one_ne_zero)
      have hU := fun τ => KernInt.torus_unitary X hx₀ τ (hu τ) (t τ) (ht τ)
      let s : Frame X.Ψ r := fun τ => Matrix.diagonal fun i => (t τ i)⁻¹
      have hs : s ∈ Bor X.Ψ r := fun τ => by
        refine ⟨?_, fun a c hca => Matrix.diagonal_apply_ne _ hca.ne'⟩
        change (Matrix.diagonal fun i => (t τ i)⁻¹).det ≠ 0
        rw [Matrix.det_diagonal]
        exact Finset.prod_ne_zero_iff.2 fun i _ => inv_ne_zero (ht0 τ i)
      have e : X.lmulC (fun τ => mat x₀ τ * Matrix.diagonal (t τ) * (mat x₀ τ)⁻¹) (rmul x₀ s) = x₀ := by
        funext τ
        change mat x₀ τ * Matrix.diagonal (t τ) * (mat x₀ τ)⁻¹ *
          (mat x₀ τ * Matrix.diagonal fun i => (t τ i)⁻¹) = mat x₀ τ
        rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (hu τ), Matrix.mul_assoc,
          Matrix.diagonal_mul_diagonal]
        simp [ht0]
      have hxs : rmul x₀ s ∈ X.dom := ((hun _ hU).2.2 _).1 (by rw [e]; exact h₀)
      have e2 := hinv _ hU x hx _ hxs
      rw [e] at e2
      simp only [hf]
      rw [e2, hsym _ hxs _ hx, (hhol x hx).2 x₀ h₀ s hs, map_mul, ← hsym _ h₀ _ hx]
      congr 1
      rw [bchar, map_prod]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      have e3 : s τ i i = conj (t τ i) :=
        (Matrix.diagonal_apply_eq _ _).trans (Complex.inv_eq_conj (ht τ i))
      rw [map_zpow₀, e3, Complex.conj_conj])
  set D : Frame X.Ψ r → X.Ψ → ℝ := fun x τ =>
    ‖lminor ((mat x₀ τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ with hD
  set K : ℝ := ‖bchar la b₁‖ * ∏ τ, ∏ i, C ^ (la τ i).natAbs with hK
  have key : ∀ x ∈ slab X δ, ‖kern X hr idx P (rmul x₀ b₁) x‖ ≤ K * ‖f x₀‖ ∧
      ‖kern X hr idx P (rmul x₀ b₁) x‖ ≤
        (K * ‖f x₀‖ * ∏ _τ : X.Ψ, (C ^ X.p0) ^ n) * ∏ τ, (D x τ ^ n)⁻¹ := by
    intro x hx
    have hxd := hsub hx
    obtain ⟨x', hx', b, hb, rfl, hbC⟩ := hC x hx
    have hx'd := hsub (horth x' hx')
    have h1 : ∀ τ, 1 ≤ D x' τ := fun τ => by
      have := FramePotential.one_le_norm_lminor_sq X.p0_le ((mat x₀ τ)⁻¹ * mat x' τ)
        ((KernInt.gram_inv_mul X hx₀ τ (hu τ) _).trans (hx' τ))
      exact (one_le_sq_iff_one_le_abs _).1 this |>.trans_eq (abs_norm _)
    have h3 : ‖bchar la b‖ ≤ ∏ τ, ∏ i, C ^ (la τ i).natAbs := by
      rw [bchar, norm_prod]
      refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun τ _ => ?_
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ =>
        KernInt.norm_zpow_le (hbC τ i i).1 (hbC τ i i).2 _
    have h4 : ‖kern X hr idx P (rmul x₀ b₁) (rmul x' b)‖ ≤ K * ‖f x'‖ := by
      rw [(hhol _ hxd).2 x₀ h₀ b₁ hb₁, hsym _ hxd _ h₀, (hhol _ h₀).2 x' hx'd b hb, norm_mul,
        Complex.norm_conj, norm_mul, hK, mul_assoc]
      gcongr
    have hK0 : 0 ≤ K := mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans h3)
    have h5 : ‖f x'‖ * ∏ τ, D x' τ ^ n ≤ ‖f x₀‖ := hbd x' hx'
    have h6 : 1 ≤ ∏ τ, D x' τ ^ n := by
      refine le_of_eq_of_le ?_ (Finset.prod_le_prod₀ (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)
        fun τ _ => one_le_pow₀ (h1 τ))
      simp
    have h7 : ∀ τ, D (rmul x' b) τ = D x' τ * ∏ j : Fin X.p0,
        ‖b τ (Fin.castLE X.p0_le j) (Fin.castLE X.p0_le j)‖ := fun τ => by
      change ‖lminor ((mat x₀ τ)⁻¹ * (mat x' τ * mat b τ)) _‖ = _
      rw [← Matrix.mul_assoc, FramePotential.lminor_mul_upper _ (FrameDegreeData.upper_of_bor X hb τ),
        norm_mul, norm_prod]
      rfl
    have h8 : ∀ τ, 0 < D (rmul x' b) τ := fun τ => by
      rw [h7]
      exact mul_pos (one_pos.trans_le (h1 τ))
        (Finset.prod_pos fun j _ => norm_pos_iff.2 (FrameDegreeData.bdiag_ne X hb τ _))
    have h9 : ∀ τ, D (rmul x' b) τ ≤ D x' τ * C ^ X.p0 := fun τ => by
      rw [h7]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (g := fun _ => C) fun j _ => (hbC τ _ _).1).trans_eq ?_
      simp
    have h10 : ∏ τ, D (rmul x' b) τ ^ n ≤ (∏ τ, D x' τ ^ n) * ∏ _τ : X.Ψ, (C ^ X.p0) ^ n := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod₀ (fun τ _ => (pow_pos (h8 τ) n).le) fun τ _ => ?_
      rw [← mul_pow]
      exact pow_le_pow_left₀ (h8 τ).le (h9 τ) n
    have h11 : 0 < ∏ τ, D (rmul x' b) τ ^ n := Finset.prod_pos fun τ _ => pow_pos (h8 τ) n
    have h12 : 0 ≤ ∏ _τ : X.Ψ, (C ^ X.p0) ^ n :=
      nonneg_of_mul_nonneg_right (h11.trans_le h10).le (one_pos.trans_le h6)
    refine ⟨h4.trans (mul_le_mul_of_nonneg_left ((le_mul_of_one_le_right (norm_nonneg _) h6).trans h5)
      hK0), h4.trans ?_⟩
    rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, le_div_iff₀ h11, mul_assoc K, mul_assoc K]
    refine mul_le_mul_of_nonneg_left ?_ hK0
    refine (mul_le_mul_of_nonneg_left h10 (norm_nonneg _)).trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right h5 h12
  refine ⟨?_, _, fun x hx => (key x hx).1⟩
  have hI : IntegrableOn (fun x : Frame X.Ψ r => ∏ τ, (D x τ ^ n)⁻¹) (slab X δ) volume := by
    have hτ := fun τ : X.Ψ => hB (mat x₀ τ)⁻¹ (Matrix.isUnit_nonsing_inv_det _ (hu τ))
    simp only [IntegrableOn] at hτ
    have _ : ∀ S : Set (Fin r → Fin r → ℂ), SigmaFinite (volume.restrict S) := fun S => inferInstance
    have h := Integrable.fintype_prod_dep hτ
    rw [← Measure.restrict_pi_pi] at h
    refine IntegrableOn.mono_set h fun x hx τ _ a b => ?_
    have := KernInt.gram_inv_mul X hx₀ τ (hu τ) (mat x τ)
    refine lt_of_eq_of_lt ?_ ((hx τ a b).trans_le (hδ1.trans (min_le_right _ _)))
    rw [← this]
    rfl
  refine Integrable.mono' (hI.const_mul _) ?_
    ((ae_restrict_iff' hopen.measurableSet).2 (Filter.Eventually.of_forall fun x hx => (key x hx).2))
  refine ContinuousOn.aestronglyMeasurable ?_ hopen.measurableSet
  refine ContinuousOn.congr (f := fun x => bchar la b₁ * conj (f x)) ?_ fun x hx => ?_
  · exact continuousOn_const.mul
      (Complex.continuous_conj.comp_continuousOn ((hhol x₀ h₀).1.continuousOn.mono hsub))
  · change kern X hr idx P (rmul x₀ b₁) x = _
    rw [(hhol _ (hsub hx)).2 x₀ h₀ b₁ hb₁, hsym _ (hsub hx) _ h₀]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GaussianKernelIntegrableOnThinSlabStatement
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussianKernel_integrableOn_thin_slab : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ) (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (m : ℕ) (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), Even n → (∀ j, P j ∈ Harm.rowHighest ℂ c c') → 2 * r ≤ n → ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ → ∀ x₁ ∈ X.dom, IntegrableOn (fun x₂ => kern X hr idx P x₁ x₂) (slab X δ) volume ∧ ∃ C : ℝ, ∀ x₂ ∈ slab X δ, ‖kern X hr idx P x₁ x₂‖ ≤ C := by
  first | exact @GlobalTheory.SW.kern_integrableOn_slab | exact GlobalTheory.SW.kern_integrableOn_slab | (intros; apply GlobalTheory.SW.kern_integrableOn_slab <;> assumption)
end
