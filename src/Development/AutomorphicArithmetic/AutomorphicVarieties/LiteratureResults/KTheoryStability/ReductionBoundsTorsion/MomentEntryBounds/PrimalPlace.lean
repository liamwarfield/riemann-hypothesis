module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.InstLCSL

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.SumSqGe
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.OfSInvCoe
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.OneLeAbsNorm
open NumberField

namespace PositivityTheory.KB.MomentRationality.Ht

variable {L : Type*} [Field L] [NumberField L]

theorem exists_den (s : Finset L) : ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ s, IsIntegral ℤ ((d : L) * x) := by
  obtain ⟨d, hd, h⟩ := exists_integral_multiples ℤ ℚ s
  refine ⟨d, hd, fun x hx => ?_⟩
  have := h x hx
  rwa [zsmul_eq_mul] at this

end PositivityTheory.KB.MomentRationality.Ht
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.SubLeSumAbsConsecutiveDiff
open Matrix

namespace PositivityTheory.KB.MomentRationality.Ht

section Lin

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem re_star_dot_self (u : n → ℂ) : (star u ⬝ᵥ u).re = ∑ i, ‖u i‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

theorem re_quad (A : Matrix n n ℂ) (v : n → ℂ) :
    (star v ⬝ᵥ ((Aᴴ * A) *ᵥ v)).re = ∑ i, ‖(A *ᵥ v) i‖ ^ 2 := by
  rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, re_star_dot_self]

theorem sum_norm_unitary {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ) (u : n → ℂ) :
    ∑ i, ‖(U *ᵥ u) i‖ ^ 2 = ∑ i, ‖u i‖ ^ 2 := by
  rw [← re_quad, ← re_star_dot_self]
  have h : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (mem_unitaryGroup_iff').1 hU
  rw [h, one_mulVec]

theorem single_le_sum_sq (u : n → ℂ) (i : n) : ‖u i‖ ^ 2 ≤ ∑ j, ‖u j‖ ^ 2 :=
  Finset.single_le_sum (f := fun j => ‖u j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

end Lin

section Tri

variable {m : ℕ}

theorem mulVec_upper {Q : Matrix (Fin m) (Fin m) ℂ} (hQ : Q.BlockTriangular id) {z : Fin m → ℂ}
    {i : Fin m} (hz : ∀ j, i < j → z j = 0) : (Q *ᵥ z) i = Q i i * z i := by
  rw [mulVec, dotProduct, Finset.sum_eq_single i]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hQ (show id j < id i from h), zero_mul]
    · rw [hz j h, mul_zero]
  · simp

theorem mulVec_lower {Q : Matrix (Fin m) (Fin m) ℂ} (hQ : ∀ a b : Fin m, a < b → Q a b = 0) {z : Fin m → ℂ}
    {i : Fin m} (hz : ∀ j, j < i → z j = 0) : (Q *ᵥ z) i = Q i i * z i := by
  rw [mulVec, dotProduct, Finset.sum_eq_single i]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hz j h, mul_zero]
    · rw [hQ i j h, zero_mul]
  · simp

theorem mul_diag_upper {A B : Matrix (Fin m) (Fin m) ℂ} (hA : A.BlockTriangular id) (hB : B.BlockTriangular id)
    (i : Fin m) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hA (show id j < id i from h), zero_mul]
    · rw [hB (show id i < id j from h), mul_zero]
  · simp

theorem inv_upper {A B : Matrix (Fin m) (Fin m) ℂ} (hA : A.BlockTriangular id) (hBA : B * A = 1) :
    B.BlockTriangular id ∧ ∀ i, B i i * A i i = 1 := by
  have : Invertible A := invertibleOfLeftInverse A B hBA
  have hB : A⁻¹ = B := Matrix.inv_eq_left_inv hBA
  have ht : B.BlockTriangular id := hB ▸ blockTriangular_inv_of_blockTriangular hA
  refine ⟨ht, fun i => ?_⟩
  rw [← mul_diag_upper ht hA, hBA, one_apply_eq]

end Tri

section Tele

theorem sub_le_sum_abs_consecutive_diff {N : ℕ} (s : Fin N → ℝ) (i j : Fin N) :
    s i - s j ≤ ∑ a : Fin N, ∑ b : Fin N, if (b : ℕ) = a + 1 then |s a - s b| else 0 := by
  classical
  set f : ℕ → ℝ := fun k => if h : k < N then s ⟨k, h⟩ else 0 with hf
  have hfs : ∀ a : Fin N, f a = s a := fun a => by simp [hf, a.2]
  have hW : (∑ a : Fin N, ∑ b : Fin N, if (b : ℕ) = a + 1 then |s a - s b| else 0) =
      ∑ k ∈ Finset.range N, if k + 1 < N then |f k - f (k + 1)| else 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => if k + 1 < N then |f k - f (k + 1)| else 0)]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : (a : ℕ) + 1 < N
    · rw [Finset.sum_eq_single ⟨(a : ℕ) + 1, ha⟩]
      · simp [ha, hf, a.2]
      · intro b _ hb
        rw [if_neg]
        intro e
        exact hb (Fin.ext e)
      · simp
    · rw [if_neg ha]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [if_neg]
      intro e
      exact ha (e ▸ b.2)
  rw [hW, ← hfs i, ← hfs j]
  have key : ∀ a b : ℕ, a ≤ b → b < N → |f a - f b| ≤
      ∑ k ∈ Finset.range N, if k + 1 < N then |f k - f (k + 1)| else 0 := by
    intro a b hab hb
    have htel : f a - f b = ∑ k ∈ Finset.Ico a b, (f k - f (k + 1)) := by
      rw [Finset.sum_Ico_eq_sum_range]
      have := Finset.sum_range_sub' (fun k => f (a + k)) (b - a)
      simp only [add_zero] at this
      rw [show a + (b - a) = b by omega] at this
      rw [← this]
      exact Finset.sum_congr rfl fun k _ => by rw [add_assoc]
    rw [htel]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hsub : Finset.Ico a b ⊆ Finset.range N := by
      intro k hk
      simp only [Finset.mem_Ico] at hk
      simp only [Finset.mem_range]
      omega
    refine (Finset.sum_le_sum fun k hk => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => by split_ifs <;> simp)
    · simp only [Finset.mem_Ico] at hk
      rw [if_pos (by omega)]
  rcases le_total (i : ℕ) j with h | h
  · exact (le_abs_self _).trans (key i j h j.2)
  · refine le_trans ?_ (key j i h i.2)
    rw [abs_sub_comm]
    exact le_abs_self _

end Tele

end PositivityTheory.KB.MomentRationality.Ht
end

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.MomentRationality.Ht

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

theorem mt_mul (x y : Sp L N) (w : InfinitePlace L) :
    mt (x * y) w = mt x w * mt y w := rfl

theorem mt_one (w : InfinitePlace L) : mt (1 : Sp L N) w = 1 := rfl

theorem mt_inv_mul (x : Sp L N) (w : InfinitePlace L) : mt x⁻¹ w * mt x w = 1 := by
  rw [← mt_mul, inv_mul_cancel, mt_one]

theorem mt_mul_inv (x : Sp L N) (w : InfinitePlace L) : mt x w * mt x⁻¹ w = 1 := by
  rw [← mt_mul, mul_inv_cancel, mt_one]

theorem ofS_inv_coe (x : Sp L N) (w : InfinitePlace L) :
    ((((ofS L N x) w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = mt x⁻¹ w := by
  rw [← Pi.inv_apply, ← map_inv]
  rfl

theorem mat_one (w : InfinitePlace L) : mat (one L N).1 w = 1 := rfl

theorem q_actL (x : Sp L N) (y : Lat L N) :
    q (actL (ofS L N x) (one L N).1) y = ∑ w, ∑ i, ‖(mt x⁻¹ w *ᵥ toR y w) i‖ ^ 2 := by
  simp only [q, qR]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hm : mat (actL (ofS L N x) (one L N).1) w = (mt x⁻¹ w)ᴴ * mt x⁻¹ w := by
    simp only [actL, LinearMap.coe_toContinuousLinearMap', actM, LinearMap.coe_mk, AddHom.coe_mk, mat_mkHS, mat_one, Matrix.mul_one, ofS_inv_coe]
  rw [hm, re_quad]

theorem q_dual (x : Sp L N) (y : Lat L N) :
    q (dualH (actL (ofS L N x) (one L N).1)) y =
      ∑ w, ∑ i, ‖((mt x w)ᵀ *ᵥ toR y w) i‖ ^ 2 := by
  simp only [q, qR]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hBM : mt x⁻¹ w * mt x w = 1 := mt_inv_mul x w
  have hMB : mt x w * mt x⁻¹ w = 1 := mt_mul_inv x w
  have hm : mat (actL (ofS L N x) (one L N).1) w = (mt x⁻¹ w)ᴴ * mt x⁻¹ w := by
    simp only [actL, LinearMap.coe_toContinuousLinearMap', actM, LinearMap.coe_mk, AddHom.coe_mk, mat_mkHS, mat_one, Matrix.mul_one, ofS_inv_coe]
  have hinv : (mat (actL (ofS L N x) (one L N).1) w)⁻¹ = mt x w * (mt x w)ᴴ := by
    rw [hm]
    refine Matrix.inv_eq_left_inv ?_
    calc mt x w * (mt x w)ᴴ * ((mt x⁻¹ w)ᴴ * mt x⁻¹ w)
        = mt x w * (mt x⁻¹ w * mt x w)ᴴ * mt x⁻¹ w := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBM, Matrix.conjTranspose_one, Matrix.mul_one, hMB]
  have hd : mat (dualH (actL (ofS L N x) (one L N).1)) w =
      ((mt x w)ᵀ)ᴴ * (mt x w)ᵀ := by
    simp only [dualH, mat_mkHS]
    rw [hinv, Matrix.transpose_mul]
    rfl
  rw [hd, re_quad]

theorem lam_ge (hN : 1 ≤ N) {h : HS L N} {κ : ℝ} (hκ : ∀ y : Lat L N, y ≠ 0 → κ ≤ q h y) : κ ≤ lam h := by
  have hne : Nonempty {y : Lat L N // y ≠ 0} := by
    refine ⟨⟨fun _ => 1, fun h0 => ?_⟩⟩
    have := congrFun h0 ⟨0, hN⟩
    exact one_ne_zero this
  unfold lam
  exact le_ciInf fun y => hκ y.1 y.2

end PositivityTheory.KB.MomentRationality.Ht
end
end

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.MomentRationality.Ht

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

abbrev gi (g : GL (Fin N) L) : Matrix (Fin N) (Fin N) L := ((g⁻¹ : GL (Fin N) L) : Matrix (Fin N) (Fin N) L)

theorem z_ne (hN : 1 ≤ N) {g : GL (Fin N) L} {z : InfinitePlace L → ℂ} {c : Sp L N}
    (hc : ∀ w, mt c w = z w • (g : Matrix (Fin N) (Fin N) L).map w.embedding) (w : InfinitePlace L) : z w ≠ 0 := by
  intro h
  have h1 := hc w
  rw [h, zero_smul] at h1
  have h2 : (mt c w).det = 1 := (c w).prop
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  rw [h1, Matrix.det_zero] at h2
  exact zero_ne_one h2

theorem emb_toL (y : Lat L N) (w : InfinitePlace L) (a : Fin N) : w.embedding (toL y a) = toR y w a := rfl

theorem cinv_vec (hN : 1 ≤ N) {g : GL (Fin N) L} {z : InfinitePlace L → ℂ} {c : Sp L N}
    (hc : ∀ w, mt c w = z w • (g : Matrix (Fin N) (Fin N) L).map w.embedding) (y : Lat L N) (w : InfinitePlace L) :
    mt c⁻¹ w *ᵥ toR y w = (z w)⁻¹ • (fun a => w.embedding ((gi g *ᵥ toL y) a)) := by
  have hz := z_ne hN hc w
  have hgg : (g : Matrix (Fin N) (Fin N) L) * gi g = 1 := g.mul_inv
  have hinv : mt c⁻¹ w * mt c w = 1 := by
    show (((c w)⁻¹ : Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * (c w : Matrix (Fin N) (Fin N) ℂ) = 1
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hx : toR y w = mt c w *ᵥ ((z w)⁻¹ • (fun a => w.embedding ((gi g *ᵥ toL y) a))) := by
    rw [hc w, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hz, one_smul]
    funext a
    change toR y w a = ((g : Matrix (Fin N) (Fin N) L).map w.embedding *ᵥ (w.embedding ∘ (gi g *ᵥ toL y))) a
    rw [← RingHom.map_mulVec, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec, emb_toL]
  rw [hx, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]

theorem cT_vec {g : GL (Fin N) L} {z : InfinitePlace L → ℂ} {c : Sp L N}
    (hc : ∀ w, mt c w = z w • (g : Matrix (Fin N) (Fin N) L).map w.embedding) (y : Lat L N) (w : InfinitePlace L) :
    (mt c w)ᵀ *ᵥ toR y w = z w • (fun a => w.embedding (((g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y) a)) := by
  rw [hc w, transpose_smul, smul_mulVec, ← transpose_map]
  congr 1
  ext a
  have := RingHom.map_mulVec w.embedding (g : Matrix (Fin N) (Fin N) L)ᵀ (toL y) a
  rw [this]
  rfl

theorem toL_ne {y : Lat L N} (hy : y ≠ 0) : toL y ≠ 0 := by
  intro h
  apply hy
  funext a
  have h1 := congrFun h a
  simpa [toL] using h1

theorem gi_ne (g : GL (Fin N) L) {y : Lat L N} (hy : y ≠ 0) : gi g *ᵥ toL y ≠ 0 := by
  intro h
  apply toL_ne hy
  have := congrArg (fun v => (g : Matrix (Fin N) (Fin N) L) *ᵥ v) h
  simpa [mulVec_mulVec, Units.mul_inv, one_mulVec] using this

theorem gT_ne (g : GL (Fin N) L) {y : Lat L N} (hy : y ≠ 0) : (g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y ≠ 0 := by
  intro h
  apply toL_ne hy
  have h2 : (gi g)ᵀ * (g : Matrix (Fin N) (Fin N) L)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, g.mul_inv, Matrix.transpose_one]
  have h1 : (gi g)ᵀ *ᵥ ((g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y) = (gi g)ᵀ *ᵥ 0 := by rw [h]
  rwa [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, Matrix.mulVec_zero] at h1

theorem int_d {d : ℤ} {G : Matrix (Fin N) (Fin N) L} (hd : ∀ i j, IsIntegral ℤ ((d : L) * G i j)) (y : Lat L N)
    (a : Fin N) : IsIntegral ℤ ((d : L) * (G *ᵥ toL y) a) := by
  simp only [mulVec, dotProduct, Finset.mul_sum]
  refine IsIntegral.sum _ fun j _ => ?_
  rw [← mul_assoc]
  exact (hd a j).mul (RingOfIntegers.isIntegral_coe (y j))

theorem sum_sq_ge (hL : IsTotallyComplex L) {d : ℤ} (hd : d ≠ 0) {β : L} (hβ : β ≠ 0)
    (hint : IsIntegral ℤ ((d : L) * β)) : ((d : ℝ) ^ 2)⁻¹ ≤ ∑ w : InfinitePlace L, ‖w.embedding β‖ ^ 2 := by
  have hdR : (d : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hd
  let α : 𝓞 L := ⟨(d : L) * β, hint⟩
  have hαc : ((α : 𝓞 L) : L) = (d : L) * β := rfl
  have hα0 : α ≠ 0 := by
    intro h
    have h1 : ((α : 𝓞 L) : L) = 0 := by rw [h]; rfl
    rw [hαc] at h1
    exact mul_ne_zero (Int.cast_ne_zero.mpr hd) hβ h1
  obtain ⟨w, hw⟩ : ∃ w : InfinitePlace L, 1 ≤ w ((α : 𝓞 L) : L) := by
    by_contra H
    push_neg at H
    obtain ⟨w0⟩ : Nonempty (InfinitePlace L) := inferInstance
    exact absurd (InfinitePlace.one_le_of_lt_one hα0 (fun z _ => H z)) (not_le.mpr (H w0))
  have hwα : w ((α : 𝓞 L) : L) = |(d : ℝ)| * ‖w.embedding β‖ := by
    rw [← InfinitePlace.norm_embedding_eq, hαc, map_mul, norm_mul, map_intCast, Complex.norm_intCast]
  have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  have h1 : 1 ≤ (d : ℝ) ^ 2 * ‖w.embedding β‖ ^ 2 := by
    have h2 : (1 : ℝ) ≤ (|(d : ℝ)| * ‖w.embedding β‖) ^ 2 := one_le_pow₀ (hwα ▸ hw)
    rwa [mul_pow, sq_abs] at h2
  have key : ((d : ℝ) ^ 2)⁻¹ ≤ ‖w.embedding β‖ ^ 2 := by
    calc ((d : ℝ) ^ 2)⁻¹ = ((d : ℝ) ^ 2)⁻¹ * 1 := (mul_one _).symm
      _ ≤ ((d : ℝ) ^ 2)⁻¹ * ((d : ℝ) ^ 2 * ‖w.embedding β‖ ^ 2) := by gcongr
      _ = ‖w.embedding β‖ ^ 2 := by field_simp
  exact key.trans (Finset.single_le_sum (f := fun v : InfinitePlace L => ‖v.embedding β‖ ^ 2)
    (fun v _ => sq_nonneg _) (Finset.mem_univ w))

end PositivityTheory.KB.MomentRationality.Ht
end
end

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.MomentRationality.Ht

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

theorem primal_place (hN : 1 ≤ N) {g : GL (Fin N) L} {z : InfinitePlace L → ℂ} {c : Sp L N}
    (hc : ∀ w, mt c w = z w • (g : Matrix (Fin N) (Fin N) L).map w.embedding)
    {M : ℝ} {p : Sp L N} (hp : p ∈ Om L N M) {s : Fin N → ℝ} (hs : ∑ i, s i = 0) {k : Sp L N} (hk : k ∈ KS L N)
    (y : Lat L N) {i0 : Fin N} (hgt : ∀ j, i0 < j → (gi g *ᵥ toL y) j = 0) (w : InfinitePlace L) :
    (Real.exp (-s i0) * M⁻¹ * (‖z w‖⁻¹ * ‖w.embedding ((gi g *ᵥ toL y) i0)‖)) ^ 2 ≤
      ∑ i, ‖(mt (c * (p * dg L N s hs * k))⁻¹ w *ᵥ toR y w) i‖ ^ 2 := by
  have mt_mul (x y : Sp L N) (v : InfinitePlace L) :
      mt (x * y) v = mt x v * mt y v := rfl
  have mt_inv_mul (x : Sp L N) (v : InfinitePlace L) : mt x⁻¹ v * mt x v = 1 := by
    rw [← mt_mul, inv_mul_cancel]
    rfl
  have cinv_vec : mt c⁻¹ w *ᵥ toR y w = (z w)⁻¹ •
      (fun a => w.embedding ((gi g *ᵥ toL y) a)) := by
    have hz : z w ≠ 0 := by
      intro h
      have h1 := hc w
      rw [h, zero_smul] at h1
      have h2 : (mt c w).det = 1 := (c w).prop
      haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
      rw [h1, Matrix.det_zero] at h2
      exact zero_ne_one h2
    have hgg : (g : Matrix (Fin N) (Fin N) L) * gi g = 1 := g.mul_inv
    have hx : toR y w = mt c w *ᵥ ((z w)⁻¹ •
        (fun a => w.embedding ((gi g *ᵥ toL y) a))) := by
      rw [hc w, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hz, one_smul]
      funext a
      change toR y w a = ((g : Matrix (Fin N) (Fin N) L).map w.embedding *ᵥ (w.embedding ∘ (gi g *ᵥ toL y))) a
      rw [← RingHom.map_mulVec, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
      rfl
    rw [hx, Matrix.mulVec_mulVec, mt_inv_mul, Matrix.one_mulVec]
  obtain ⟨hpu, hpM, -, -⟩ := hp
  have hPp : mt p⁻¹ w * mt p w = 1 := mt_inv_mul p w
  obtain ⟨hPu, hPd⟩ := inv_upper (hpu w) hPp
  have hD : mt (dg L N s hs)⁻¹ w = diagonal fun i => ((Real.exp (-s i) : ℝ) : ℂ) := by
    have h1 := mt_inv_mul (dg L N s hs) w
    have h2 : mt (dg L N s hs) w = diagonal fun i => ((Real.exp (s i) : ℝ) : ℂ) := rfl
    rw [h2] at h1
    have h3 : (diagonal fun i => ((Real.exp (s i) : ℝ) : ℂ)) * (diagonal fun i => ((Real.exp (-s i) : ℝ) : ℂ)) = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
    calc mt (dg L N s hs)⁻¹ w
        = mt (dg L N s hs)⁻¹ w * ((diagonal fun i => ((Real.exp (s i) : ℝ) : ℂ)) *
            (diagonal fun i => ((Real.exp (-s i) : ℝ) : ℂ))) := by rw [h3, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hK : mt k⁻¹ w ∈ unitaryGroup (Fin N) ℂ := by
    have hU := hk w
    have h1 : mt k⁻¹ w * mt k w = 1 := mt_inv_mul k w
    have h2 : mt k⁻¹ w = star (mt k w) := by
      calc mt k⁻¹ w = mt k⁻¹ w * (mt k w * star (mt k w)) := by
            rw [Unitary.mul_star_self_of_mem hU, Matrix.mul_one]
        _ = star (mt k w) := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [h2]
    exact Unitary.star_mem hU
  have hQ : mt (c * (p * dg L N s hs * k))⁻¹ w *ᵥ toR y w =
      mt k⁻¹ w *ᵥ (mt (dg L N s hs)⁻¹ w *ᵥ (mt p⁻¹ w *ᵥ (mt c⁻¹ w *ᵥ toR y w))) := by
    simp only [_root_.mul_inv_rev, mt_mul, mulVec_mulVec, Matrix.mul_assoc]
  rw [hQ, sum_norm_unitary hK]
  refine le_trans ?_ (single_le_sum_sq _ i0)
  have hzero : ∀ j, i0 < j → ((z w)⁻¹ • fun a => w.embedding ((gi g *ᵥ toL y) a)) j = 0 := by
    intro j hj
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hgt j hj, map_zero, mul_zero]
  rw [cinv_vec, hD, mulVec_diagonal, mulVec_upper hPu hzero]
  have hne : mt p w i0 i0 ≠ 0 := by
    intro h
    have h1 := hPd i0
    rw [h, mul_zero] at h1
    exact zero_ne_one h1
  have hpos : 0 < ‖mt p w i0 i0‖ := norm_pos_iff.2 hne
  have hM : 0 < M := lt_of_lt_of_le hpos (hpM w i0 i0)
  have hPi : M⁻¹ ≤ ‖mt p⁻¹ w i0 i0‖ := by
    have h3 : ‖mt p⁻¹ w i0 i0‖ * ‖mt p w i0 i0‖ = 1 := by rw [← norm_mul, hPd i0, norm_one]
    rw [eq_inv_of_mul_eq_one_left h3]
    exact inv_anti₀ hpos (hpM w i0 i0)
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), norm_inv]
  have hM' : 0 ≤ M⁻¹ := inv_nonneg.2 hM.le
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  rw [mul_assoc]
  gcongr

theorem dual_place {g : GL (Fin N) L} {z : InfinitePlace L → ℂ} {c : Sp L N}
    (hc : ∀ w, mt c w = z w • (g : Matrix (Fin N) (Fin N) L).map w.embedding)
    {M : ℝ} {p : Sp L N} (hp : p ∈ Om L N M) {s : Fin N → ℝ} (hs : ∑ i, s i = 0) {k : Sp L N} (hk : k ∈ KS L N)
    (y : Lat L N) {i1 : Fin N} (hlt : ∀ j, j < i1 → ((g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y) j = 0)
    (w : InfinitePlace L) :
    (Real.exp (s i1) * M⁻¹ * (‖z w‖ * ‖w.embedding (((g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y) i1)‖)) ^ 2 ≤
      ∑ i, ‖((mt (c * (p * dg L N s hs * k)) w)ᵀ *ᵥ toR y w) i‖ ^ 2 := by
  have mt_mul (x y : Sp L N) (v : InfinitePlace L) :
      mt (x * y) v = mt x v * mt y v := rfl
  have cT_vec : (mt c w)ᵀ *ᵥ toR y w = z w •
      (fun a => w.embedding (((g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y) a)) := by
    rw [hc w, transpose_smul, smul_mulVec, ← transpose_map]
    congr 1
    ext a
    have := RingHom.map_mulVec w.embedding (g : Matrix (Fin N) (Fin N) L)ᵀ (toL y) a
    rw [this]
    rfl
  obtain ⟨hpu, hpM, hpm, -⟩ := hp
  have hKT : (mt k w)ᵀ ∈ unitaryGroup (Fin N) ℂ := by
    rw [mem_unitaryGroup_iff]
    have h1 : star (mt k w) * mt k w = 1 := Unitary.star_mul_self_of_mem (hk w)
    have h2 : star ((mt k w)ᵀ) = (star (mt k w))ᵀ := by
      ext i j
      simp [star_eq_conjTranspose]
    rw [h2, ← transpose_mul, h1, transpose_one]
  have hQ : (mt (c * (p * dg L N s hs * k)) w)ᵀ *ᵥ toR y w =
      (mt k w)ᵀ *ᵥ ((mt (dg L N s hs) w)ᵀ *ᵥ ((mt p w)ᵀ *ᵥ ((mt c w)ᵀ *ᵥ toR y w))) := by
    simp only [mt_mul, transpose_mul, mulVec_mulVec, Matrix.mul_assoc]
  have hD : (mt (dg L N s hs) w)ᵀ = diagonal fun i => ((Real.exp (s i) : ℝ) : ℂ) := by
    rw [show mt (dg L N s hs) w = diagonal fun i => ((Real.exp (s i) : ℝ) : ℂ) from rfl,
      diagonal_transpose]
  have hlow : ∀ a b : Fin N, a < b → (mt p w)ᵀ a b = 0 := fun a b hab => by
    rw [transpose_apply]
    exact hpu w hab
  have hzero : ∀ j, j < i1 → (z w • fun a => w.embedding (((g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y) a)) j = 0 := by
    intro j hj
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hlt j hj, map_zero, mul_zero]
  rw [hQ, sum_norm_unitary hKT]
  refine le_trans ?_ (single_le_sum_sq _ i1)
  rw [cT_vec, hD, mulVec_diagonal, mulVec_lower hlow hzero, transpose_apply]
  have hM : 0 ≤ M := (norm_nonneg _).trans (hpM w i1 i1)
  have hM' : 0 ≤ M⁻¹ := inv_nonneg.2 hM
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  rw [mul_assoc]
  gcongr
  exact hpm w i1

end PositivityTheory.KB.MomentRationality.Ht
