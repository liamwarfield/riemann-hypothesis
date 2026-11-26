module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfB
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
  {x0 : Frame X.Ψ r} (D : ExtFPf.LUData X x0) (FF : Set (V (nd X)))

private theorem gram_eq_lemma (τ' : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (Y : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ' G Y = Yᵀ * G.map τ' * Y.map (starRingEnd ℂ) := by
  ext a c
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm

private theorem transpose_mul_mul_map_cc_eq_of_herm_mulVec (G : Matrix (Fin r) (Fin r) E) (γ : GL (Fin r) E)
    (hγ : ∀ v w : Fin r → E, ReciprocityTheory.ChartRestriction.G.FD.herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v)
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w) = ReciprocityTheory.ChartRestriction.G.FD.herm G v w) :
    (γ : Matrix (Fin r) (Fin r) E)ᵀ * G * (γ : Matrix (Fin r) (Fin r) E).map ReciprocityTheory.ChartRestriction.G.FD.cc = G := by
  ext a b
  have hv : ∀ c : Fin r, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (Pi.single c (1 : E) : Fin r → E) =
      fun p => (γ : Matrix (Fin r) (Fin r) E) p c := by
    intro c
    ext p
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hcc : ∀ q : Fin r, ReciprocityTheory.ChartRestriction.G.FD.cc ((Pi.single b (1 : E) : Fin r → E) q) =
      (Pi.single b (1 : E) : Fin r → E) q := by
    intro q
    by_cases hq : q = b
    · subst hq
      simp [ReciprocityTheory.ChartRestriction.G.FD.cc]
    · simp [Pi.single_apply, hq, ReciprocityTheory.ChartRestriction.G.FD.cc]
  have h := hγ (Pi.single a 1) (Pi.single b 1)
  rw [hv, hv] at h
  unfold ReciprocityTheory.ChartRestriction.G.FD.herm at h
  simp only [hcc] at h
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact h.trans (by simp [Pi.single_apply])

private theorem lact_mem_dom' {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact γ x ∈ X.dom := by
  intro τ
  obtain ⟨hxd, hxm⟩ := hx τ
  have hmat : ReciprocityTheory.ChartRestriction.G.FD.mat (lact γ x) τ =
      (γ : Matrix (Fin r) (Fin r) E).map τ.1 * ReciprocityTheory.ChartRestriction.G.FD.mat x τ := rfl
  have hU : ((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ * X.Gm.map τ.1 *
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) = X.Gm.map τ.1 := by
    have h0 := transpose_mul_mul_map_cc_eq_of_herm_mulVec X.Gm γ (X.Γ_stab γ hγ).1
    have hconj : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) =
        ((γ : Matrix (Fin r) (Fin r) E).map ReciprocityTheory.ChartRestriction.G.FD.cc).map τ.1 := by
      ext a b
      simp only [Matrix.map_apply]
      exact (ReciprocityTheory.ChartRestriction.G.FD.emb_cc τ.1 _).symm
    rw [hconj, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, h0]
  have hU' : ∀ Y : Matrix (Fin r) (Fin r) ℂ, ((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ *
      (X.Gm.map τ.1 * (((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) * Y)) =
      X.Gm.map τ.1 * Y := by
    intro Y
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU]
  refine ⟨?_, fun i => ?_⟩
  · rw [hmat, Matrix.det_mul]
    refine mul_ne_zero ?_ hxd
    have hdet : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det = τ.1 (γ : Matrix (Fin r) (Fin r) E).det :=
      (RingHom.map_det _ _).symm
    rw [hdet]
    exact (map_ne_zero τ.1).2 (Matrix.isUnits_det_units γ).ne_zero
  · have hg : ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.mat (lact γ x) τ) =
        ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) := by
      rw [hmat, gram_eq_lemma, gram_eq_lemma, Matrix.transpose_mul, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
      rw [hU']
    have hd : ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (lact γ x) τ i = ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i := by
      unfold ReciprocityTheory.ChartRestriction.G.FD.dmin
      rw [hg]
    rw [hd]
    exact hxm i

private theorem submatrix_castLE_transpose_mul_mul_map_conj_of_upper {i : ℕ} (h : i ≤ r) (B M : Matrix (Fin r) (Fin r) ℂ)
    (hB : ∀ a c : Fin r, c < a → B a c = 0) :
    (Bᵀ * M * B.map (starRingEnd ℂ)).submatrix (Fin.castLE h) (Fin.castLE h) =
      (B.submatrix (Fin.castLE h) (Fin.castLE h))ᵀ * M.submatrix (Fin.castLE h) (Fin.castLE h) *
        (B.submatrix (Fin.castLE h) (Fin.castLE h)).map (starRingEnd ℂ) := by
  have hout : ∀ d : Fin r, d ∉ Set.range (Fin.castLE h) → i ≤ (d : ℕ) := by
    intro d hd
    by_contra hlt
    push_neg at hlt
    exact hd (Set.mem_range.2 ⟨⟨d, hlt⟩, Fin.ext rfl⟩)
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ ?_
  · intro d hd
    try dsimp only
    have hlt : Fin.castLE h c < d := by
      show (c : ℕ) < d
      exact lt_of_lt_of_le c.isLt (hout d hd)
    rw [hB d (Fin.castLE h c) hlt, map_zero, mul_zero]
  · intro d'
    try dsimp only
    congr 1
    refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ ?_
    · intro k hk
      try dsimp only
      have hlt : Fin.castLE h a < k := by
        show (a : ℕ) < k
        exact lt_of_lt_of_le a.isLt (hout k hk)
      rw [hB k (Fin.castLE h a) hlt, zero_mul]
    · intro k'
      rfl

private theorem exists_pos_lminor_gram_mul_eq (τ' : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (Xm Bm : Matrix (Fin r) (Fin r) ℂ) (hB : ∀ a c : Fin r, c < a → Bm a c = 0)
    (hdiag : ∀ a, Bm a a ≠ 0) (i : Fin (r + 1)) :
    ∃ t : ℝ, 0 < t ∧ ReciprocityTheory.ChartRestriction.G.FD.lminor (ReciprocityTheory.ChartRestriction.G.FD.gram τ' G (Xm * Bm)) i =
      (t : ℂ) * ReciprocityTheory.ChartRestriction.G.FD.lminor (ReciprocityTheory.ChartRestriction.G.FD.gram τ' G Xm) i := by
  have hi : (i : ℕ) ≤ r := Nat.le_of_lt_succ i.isLt
  have hBs : (Bm.submatrix (Fin.castLE hi) (Fin.castLE hi)).det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular (M := Bm.submatrix (Fin.castLE hi) (Fin.castLE hi))
      (fun a c hca => hB (Fin.castLE hi a) (Fin.castLE hi c) hca)]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hdiag _
  refine ⟨Complex.normSq (Bm.submatrix (Fin.castLE hi) (Fin.castLE hi)).det,
    Complex.normSq_pos.2 hBs, ?_⟩
  have hg : ReciprocityTheory.ChartRestriction.G.FD.gram τ' G (Xm * Bm) =
      Bmᵀ * ReciprocityTheory.ChartRestriction.G.FD.gram τ' G Xm * Bm.map (starRingEnd ℂ) := by
    rw [gram_eq_lemma, gram_eq_lemma, Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  have hc : ((Bm.submatrix (Fin.castLE hi) (Fin.castLE hi)).map (starRingEnd ℂ)).det =
      starRingEnd ℂ (Bm.submatrix (Fin.castLE hi) (Fin.castLE hi)).det :=
    (RingHom.map_det _ _).symm
  unfold ReciprocityTheory.ChartRestriction.G.FD.lminor
  rw [hg, submatrix_castLE_transpose_mul_mul_map_conj_of_upper hi _ _ hB, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc,
    ← Complex.mul_conj]
  ring

private theorem rmul_mem_dom_of_mem_dom {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    rmul x b ∈ X.dom := by
  intro τ
  obtain ⟨hxd, hxm⟩ := hx τ
  obtain ⟨hbd, hbt⟩ := hb τ
  have hB : ∀ a c : Fin r, c < a → ReciprocityTheory.ChartRestriction.G.FD.mat b τ a c = 0 := hbt
  have hdiag : ∀ a : Fin r, ReciprocityTheory.ChartRestriction.G.FD.mat b τ a a ≠ 0 := by
    have h1 := Matrix.det_of_upperTriangular (M := ReciprocityTheory.ChartRestriction.G.FD.mat b τ) hB
    rw [h1] at hbd
    exact fun a => Finset.prod_ne_zero_iff.1 hbd a (Finset.mem_univ a)
  refine ⟨?_, fun i => ?_⟩
  · show (ReciprocityTheory.ChartRestriction.G.FD.mat x τ * ReciprocityTheory.ChartRestriction.G.FD.mat b τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hxd hbd
  · obtain ⟨t, ht, he⟩ := exists_pos_lminor_gram_mul_eq τ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.mat x τ)
      (ReciprocityTheory.ChartRestriction.G.FD.mat b τ) hB hdiag i
    have he' : ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (rmul x b) τ i =
        (t : ℂ) * ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i := he
    rw [he', Complex.re_ofReal_mul, mul_left_comm]
    exact mul_pos ht (hxm i)

private theorem mem_bor_rmul {b b' : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r) :
    rmul b b' ∈ Bor X.Ψ r := by
  intro τ
  obtain ⟨hd, ht⟩ := hb τ
  obtain ⟨hd', ht'⟩ := hb' τ
  refine ⟨?_, fun a c hca => ?_⟩
  · show (ReciprocityTheory.ChartRestriction.G.FD.mat b τ * ReciprocityTheory.ChartRestriction.G.FD.mat b' τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hd hd'
  · show (ReciprocityTheory.ChartRestriction.G.FD.mat b τ * ReciprocityTheory.ChartRestriction.G.FD.mat b' τ) a c = 0
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k a with hk | hk
    · rw [show ReciprocityTheory.ChartRestriction.G.FD.mat b τ a k = 0 from ht a k hk, zero_mul]
    · rw [show ReciprocityTheory.ChartRestriction.G.FD.mat b' τ k c = 0 from ht' k c (lt_of_lt_of_le hca hk), mul_zero]

private theorem FD_mat_inv_mem_bor {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) ∈ Bor X.Ψ r := by
  intro τ
  obtain ⟨hd, ht⟩ := hb τ
  refine ⟨?_, fun a c hca => ?_⟩
  · show ((ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹).det ≠ 0
    first
      | exact (Matrix.isUnit_nonsing_inv_det _ (Ne.isUnit hd)).ne_zero
      | (rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]; exact inv_ne_zero hd)
  · haveI := (ReciprocityTheory.ChartRestriction.G.FD.mat b τ).invertibleOfIsUnitDet (Ne.isUnit hd)
    have hT : (ReciprocityTheory.ChartRestriction.G.FD.mat b τ).BlockTriangular id := fun a c h => ht a c h
    exact Matrix.blockTriangular_inv_of_blockTriangular hT hca

private theorem rmul_assoc_frame (u v w : Frame X.Ψ r) : rmul (rmul u v) w = rmul u (rmul v w) := by
  funext τ
  exact Matrix.mul_assoc (ReciprocityTheory.ChartRestriction.G.FD.mat u τ) (ReciprocityTheory.ChartRestriction.G.FD.mat v τ) (ReciprocityTheory.ChartRestriction.G.FD.mat w τ)

private theorem rmul_rmul_inv_mat_eq_self {y b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    rmul (rmul y b) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) = y := by
  funext τ
  show ReciprocityTheory.ChartRestriction.G.FD.mat y τ * ReciprocityTheory.ChartRestriction.G.FD.mat b τ * (ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹ = y τ
  rw [Matrix.mul_nonsing_inv_cancel_right _ _ (Ne.isUnit (hb τ).1)]
  rfl

private theorem rmul_mem_T_iff {y b : Frame X.Ψ r} (hy : y ∈ X.dom) (hb : b ∈ Bor X.Ψ r) :
    rmul y b ∈ T D FF ↔ y ∈ T D FF := by
  have hyb : rmul y b ∈ X.dom := rmul_mem_dom_of_mem_dom hb hy
  by_cases hΔ : D.Δ y = 0
  · have hn : ¬ y ∈ T D FF := fun h => (show _ ∧ _ ∧ _ from h).2.1 hΔ
    refine iff_of_false ?_ hn
    intro h
    have hΔ' : D.Δ (rmul y b) ≠ 0 := (show _ ∧ _ ∧ _ from h).2.1
    obtain ⟨hz, hb', he⟩ := D.split _ hyb hΔ'
    have hy' : y = rmul (cpt X x0 (D.zOf (rmul y b)))
        (rmul (D.bOf (rmul y b)) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) := by
      calc y = rmul (rmul y b) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) := (rmul_rmul_inv_mat_eq_self hb).symm
        _ = rmul (rmul (cpt X x0 (D.zOf (rmul y b))) (D.bOf (rmul y b))) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) :=
          congrArg (fun w => rmul w (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) he
        _ = _ := rmul_assoc_frame _ _ _
    have h2 := (D.uniq _ hz _ (mem_bor_rmul hb' (FD_mat_inv_mem_bor hb))).1
    rw [← hy'] at h2
    exact h2 hΔ
  · obtain ⟨hz, hb0, he⟩ := D.split y hy hΔ
    have hyb' : rmul y b = rmul (cpt X x0 (D.zOf y)) (rmul (D.bOf y) b) :=
      (congrArg (fun w => rmul w b) he).trans (rmul_assoc_frame _ _ _)
    obtain ⟨hΔ1, hz1, -⟩ := D.uniq _ hz _ (mem_bor_rmul hb0 hb)
    rw [← hyb'] at hΔ1 hz1
    constructor
    · intro h
      have hF : D.zOf (rmul y b) ∈ FF := (show _ ∧ _ ∧ _ from h).2.2
      rw [hz1] at hF
      show _ ∧ _ ∧ _
      exact ⟨hy, hΔ, hF⟩
    · intro h
      have hF : D.zOf y ∈ FF := (show _ ∧ _ ∧ _ from h).2.2
      show _ ∧ _ ∧ _
      refine ⟨hyb, hΔ1, ?_⟩
      rw [hz1]
      exact hF

theorem ind_rmul {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x b : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hb : b ∈ Bor X.Ψ r) {M : Type*} [One M] [Zero M] :
    (T D FF).indicator (1 : Frame X.Ψ r → M) (lact γ⁻¹ (rmul x b)) =
      (T D FF).indicator (1 : Frame X.Ψ r → M) (lact γ⁻¹ x) := by
  have hγi : γ⁻¹ ∈ X.Γ := X.Γ.inv_mem hγ
  have hy : lact γ⁻¹ x ∈ X.dom := lact_mem_dom' hγi hx
  have hlr : lact γ⁻¹ (rmul x b) = rmul (lact γ⁻¹ x) b := by
    funext τ
    dsimp only [lact, rmul, mat]
    exact (Matrix.mul_assoc (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1)
      (Matrix.of (x τ)) (Matrix.of (b τ))).symm
  rw [hlr]
  by_cases h : lact γ⁻¹ x ∈ T D FF
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((rmul_mem_T_iff D FF hy hb).2 h)]
    rfl
  · first
      | rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem (fun h' => h ((rmul_mem_T_iff D FF hy hb).1 h'))]
      | rw [Set.indicator_of_not_mem h,
          Set.indicator_of_not_mem (fun h' => h ((rmul_mem_T_iff D FF hy hb).1 h'))]

theorem ind_cpt {z : V (nd X)} (hz : z ∈ OmF X x0) {M : Type*} [One M] [Zero M] :
    (T D FF).indicator (1 : Frame X.Ψ r → M) (cpt X x0 z) = FF.indicator 1 z := by
  have hb : (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) ∈ Bor X.Ψ r := by
    refine fun τ => ⟨?_, fun a c hca => ?_⟩
    · show Matrix.det (1 : Matrix (Fin r) (Fin r) ℂ) ≠ 0
      simp
    · exact Matrix.one_apply_ne hca.ne'
  have h1 : rmul (cpt X x0 z) (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) = cpt X x0 z := by
    funext τ
    first
      | exact Matrix.mul_one _
      | simp [ReciprocityTheory.ChartRestriction.G.FD.rmul, ReciprocityTheory.ChartRestriction.G.FD.mat]
  obtain ⟨hΔ, hzz, -⟩ := D.uniq z hz _ hb
  rw [h1] at hΔ hzz
  have hiff : cpt X x0 z ∈ T D FF ↔ z ∈ FF := by
    constructor
    · intro h
      have h' : D.zOf (cpt X x0 z) ∈ FF := h.2.2
      rw [hzz] at h'
      exact h'
    · intro h
      show _ ∧ _ ∧ _
      refine ⟨hz, hΔ, ?_⟩
      rw [hzz]
      exact h
  by_cases hF : z ∈ FF
  · rw [Set.indicator_of_mem (hiff.2 hF), Set.indicator_of_mem hF]
    rfl
  · first
      | rw [Set.indicator_of_notMem (fun h => hF (hiff.1 h)), Set.indicator_of_notMem hF]
      | rw [Set.indicator_of_not_mem (fun h => hF (hiff.1 h)), Set.indicator_of_not_mem hF]

private theorem continuous_cpt_apply (y0 : Frame X.Ψ r) : Continuous fun z => cpt X y0 z := by
  unfold ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt ReciprocityTheory.ChartRestriction.G.FD.rmul ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat
    ReciprocityTheory.ChartRestriction.G.FD.mat
  refine continuous_pi fun τ => ?_
  refine Continuous.matrix_mul continuous_const ?_
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.of_apply]
  split_ifs
  · first
      | fun_prop
      | exact (EuclideanSpace.proj _).continuous
  · exact continuous_const
  · exact continuous_const

private theorem cpt_lact_upper_bounds (γ : GL (Fin r) E) (y0 : Frame X.Ψ r) (z : V (nd X)) :
    cpt X (lact γ y0) z = lact γ (cpt X y0 z) := by
  show rmul (lact γ y0) (nmat X z) = lact γ (rmul y0 (nmat X z))
  funext τ
  dsimp only [lact, rmul, mat]
  exact Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (Matrix.of (y0 τ))
    (Matrix.of (nmat X z τ))

private theorem gram_mat_lact_of_mem_Γ {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.mat (lact γ x) τ) =
      ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) := by
  have hmat : ReciprocityTheory.ChartRestriction.G.FD.mat (lact γ x) τ =
      (γ : Matrix (Fin r) (Fin r) E).map τ.1 * ReciprocityTheory.ChartRestriction.G.FD.mat x τ := rfl
  have hU : ((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ * X.Gm.map τ.1 *
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) = X.Gm.map τ.1 := by
    have h0 := transpose_mul_mul_map_cc_eq_of_herm_mulVec X.Gm γ (X.Γ_stab γ hγ).1
    have hconj : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) =
        ((γ : Matrix (Fin r) (Fin r) E).map ReciprocityTheory.ChartRestriction.G.FD.cc).map τ.1 := by
      ext a b
      simp only [Matrix.map_apply]
      exact (ReciprocityTheory.ChartRestriction.G.FD.emb_cc τ.1 _).symm
    rw [hconj, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, h0]
  have hU' : ∀ Y : Matrix (Fin r) (Fin r) ℂ, ((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ *
      (X.Gm.map τ.1 * (((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) * Y)) =
      X.Gm.map τ.1 * Y := by
    intro Y
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU]
  rw [hmat, gram_eq_lemma, gram_eq_lemma, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
  rw [hU']

private theorem lact_inv_apply_lact (γ : GL (Fin r) E) (y : Frame X.Ψ r) : lact γ⁻¹ (lact γ y) = y := by
  funext τ
  show ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * Matrix.of (y τ)) = y τ
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  rfl

private theorem continuous_FD_dmin (X : Data E r) (τ : X.Ψ) (i : Fin (r + 1)) :
    Continuous fun x : Frame X.Ψ r => ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i := by
  unfold ReciprocityTheory.ChartRestriction.G.FD.dmin ReciprocityTheory.ChartRestriction.G.FD.lminor ReciprocityTheory.ChartRestriction.G.FD.gram
    ReciprocityTheory.ChartRestriction.G.FD.hermC ReciprocityTheory.ChartRestriction.G.FD.col ReciprocityTheory.ChartRestriction.G.FD.mat
  refine Continuous.matrix_det ?_
  refine Continuous.matrix_submatrix ?_ _ _
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.of_apply]
  refine continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun d _ => ?_
  refine Continuous.mul (Continuous.mul ?_ continuous_const) ?_
  · exact (continuous_apply _).comp ((continuous_apply _).comp (continuous_apply τ))
  · exact Complex.continuous_conj.comp
      ((continuous_apply _).comp ((continuous_apply _).comp (continuous_apply τ)))

private theorem isOpen_dom_of_data (X : Data E r) : IsOpen X.dom := by
  show IsOpen {x : Frame X.Ψ r | ∀ τ : X.Ψ, (ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0 ∧
    ∀ i : Fin (r + 1), 0 < ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i * (ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i).re}
  simp only [Set.setOf_forall, Set.setOf_and]
  refine isOpen_iInter_of_finite fun τ => ?_
  refine IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · refine isOpen_ne_fun (Continuous.matrix_det ?_) continuous_const
    unfold ReciprocityTheory.ChartRestriction.G.FD.mat
    exact continuous_apply τ
  · exact isOpen_lt continuous_const
      (continuous_const.mul (Complex.continuous_re.comp (continuous_FD_dmin X τ i)))

private theorem muF_lact_upper_bounds {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (y0 : Frame X.Ψ r) :
    muF X (lact γ y0) = muF X y0 := by
  have hOm : OmF X (lact γ y0) = OmF X y0 := by
    ext z
    show cpt X (lact γ y0) z ∈ X.dom ↔ cpt X y0 z ∈ X.dom
    rw [cpt_lact_upper_bounds]
    constructor
    · intro h
      have h2 := lact_mem_dom' (X.Γ.inv_mem hγ) h
      rwa [lact_inv_apply_lact] at h2
    · intro h
      exact lact_mem_dom' hγ h
  have hd : ∀ z, ReciprocityTheory.ChartRestriction.G.AR.Up.densF X (lact γ y0) z = ReciprocityTheory.ChartRestriction.G.AR.Up.densF X y0 z := by
    intro z
    unfold ReciprocityTheory.ChartRestriction.G.AR.Up.densF
    rw [cpt_lact_upper_bounds]
    simp only [ReciprocityTheory.ChartRestriction.G.FD.dmin, gram_mat_lact_of_mem_Γ hγ]
  unfold ReciprocityTheory.ChartRestriction.G.AR.Up.muF
  rw [hOm]
  simp only [hd]

private theorem isOrth_lact' {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {y0 : Frame X.Ψ r} (h : IsOrth X y0) :
    IsOrth X (lact γ y0) := by
  intro τ
  rw [gram_mat_lact_of_mem_Γ hγ]
  exact h τ

private theorem measurableSet_T (hF : MeasurableSet FF) : MeasurableSet (T D FF) := by
  classical
  have hUo : IsOpen {x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0} :=
    (isOpen_dom_of_data X).inter (isOpen_ne_fun D.hΔ.continuous continuous_const)
  have hpw : Measurable ({x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0}.piecewise D.zOf fun _ => 0) :=
    D.hz.continuousOn.measurable_piecewise continuousOn_const hUo.measurableSet
  have hT : T D FF = {x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0} ∩
      ({x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0}.piecewise D.zOf fun _ => 0) ⁻¹' FF := by
    ext x
    constructor
    · intro h
      obtain ⟨h1, h2, h3⟩ := (show _ ∧ _ ∧ _ from h)
      refine ⟨⟨h1, h2⟩, ?_⟩
      show ({x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0}.piecewise D.zOf fun _ => 0) x ∈ FF
      rw [Set.piecewise_eq_of_mem _ _ _
        (show x ∈ {x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0} from ⟨h1, h2⟩)]
      exact h3
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have h3' : ({x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0}.piecewise D.zOf fun _ => 0) x ∈ FF := h3
      rw [Set.piecewise_eq_of_mem _ _ _
        (show x ∈ {x : Frame X.Ψ r | x ∈ X.dom ∧ D.Δ x ≠ 0} from ⟨h1, h2⟩)] at h3'
      show _ ∧ _ ∧ _
      exact ⟨h1, h2, h3'⟩
  rw [hT]
  exact hUo.measurableSet.inter (hpw hF)

private theorem measurable_lact (γ : GL (Fin r) E) : Measurable fun x : Frame X.Ψ r => lact γ x := by
  refine Continuous.measurable ?_
  unfold lact ReciprocityTheory.ChartRestriction.G.FD.mat
  exact continuous_pi fun τ => Continuous.matrix_mul continuous_const (continuous_apply τ)

private theorem ae_mem_omF (y0 : Frame X.Ψ r) : ∀ᵐ z ∂muF X y0, z ∈ OmF X y0 := by
  have hOm : MeasurableSet (OmF X y0) :=
    ((isOpen_dom_of_data X).preimage (continuous_cpt_apply y0)).measurableSet
  have hac : muF X y0 ≪ volume.restrict (OmF X y0) := by
    unfold ReciprocityTheory.ChartRestriction.G.AR.Up.muF
    exact withDensity_absolutelyContinuous _ _
  exact hac.ae_le (ae_restrict_mem hOm)

private theorem lact_mul_upper_bounds (a b : GL (Fin r) E) (x : Frame X.Ψ r) :
    lact (a * b) x = lact a (lact b x) := by
  funext τ
  dsimp only [lact, mat]
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]
  try rfl

private theorem lact_rmul_eq_rmul_lact (g : GL (Fin r) E) (y c : Frame X.Ψ r) :
    lact g (rmul y c) = rmul (lact g y) c := by
  funext τ
  dsimp only [lact, rmul, mat]
  exact (Matrix.mul_assoc ((g : Matrix (Fin r) (Fin r) E).map τ.1) (Matrix.of (y τ))
    (Matrix.of (c τ))).symm

private theorem eq_of_lact_inv_cpt_mem_T (hFF : IsFundSet X x0 FF) {z : V (nd X)} (hz : z ∈ OmF X x0)
    {γ1 γ2 : GL (Fin r) E} (h1 : γ1 ∈ X.Γ) (h2 : γ2 ∈ X.Γ)
    (hT1 : lact γ1⁻¹ (cpt X x0 z) ∈ T D FF) (hT2 : lact γ2⁻¹ (cpt X x0 z) ∈ T D FF) : γ1 = γ2 := by
  obtain ⟨y1, hy1⟩ : ∃ y, y = lact γ1⁻¹ (cpt X x0 z) := ⟨_, rfl⟩
  obtain ⟨y2, hy2⟩ : ∃ y, y = lact γ2⁻¹ (cpt X x0 z) := ⟨_, rfl⟩
  rw [← hy1] at hT1
  rw [← hy2] at hT2
  obtain ⟨hd1, hΔ1, hF1⟩ := (show _ ∧ _ ∧ _ from hT1)
  obtain ⟨hd2, hΔ2, hF2⟩ := (show _ ∧ _ ∧ _ from hT2)
  obtain ⟨hO1, hB1, he1⟩ := D.split y1 hd1 hΔ1
  obtain ⟨hO2, hB2, he2⟩ := D.split y2 hd2 hΔ2
  have hx1 : lact γ1 y1 = cpt X x0 z := by
    have h := lact_inv_apply_lact γ1⁻¹ (cpt X x0 z)
    rw [inv_inv] at h
    rw [hy1]
    exact h
  have hg : (γ2⁻¹ * γ1) ∈ X.Γ := X.Γ.mul_mem (X.Γ.inv_mem h2) h1
  have hEq : cpt X x0 (D.zOf y2) = lact (γ2⁻¹ * γ1) (rmul (cpt X x0 (D.zOf y1)) (rmul (D.bOf y1) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y2) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r))) := by
    calc cpt X x0 (D.zOf y2) = rmul (rmul (cpt X x0 (D.zOf y2)) (D.bOf y2)) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y2) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) := (rmul_rmul_inv_mat_eq_self hB2).symm
      _ = rmul y2 (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y2) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) := by rw [← he2]
      _ = rmul (lact γ2⁻¹ (lact γ1 y1)) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y2) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) := by rw [hx1, hy2]
      _ = rmul (lact (γ2⁻¹ * γ1) y1) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y2) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) := by rw [lact_mul_upper_bounds]
      _ = rmul (lact (γ2⁻¹ * γ1) (rmul (cpt X x0 (D.zOf y1)) (D.bOf y1))) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y2) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) := by rw [← he1]
      _ = lact (γ2⁻¹ * γ1) (rmul (rmul (cpt X x0 (D.zOf y1)) (D.bOf y1)) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y2) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) := (lact_rmul_eq_rmul_lact _ _ _).symm
      _ = lact (γ2⁻¹ * γ1) (rmul (cpt X x0 (D.zOf y1)) (rmul (D.bOf y1) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y2) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r))) :=
        congrArg (lact (γ2⁻¹ * γ1)) (rmul_assoc_frame _ _ _)
  have hw : D.zOf y1 = D.zOf y2 :=
    hFF.2.2.1 _ hF1 _ hF2 _ hg _ (mem_bor_rmul hB1 (FD_mat_inv_mem_bor hB2)) hEq
  have hB' : lact (γ2⁻¹ * γ1) y1 = y2 := by rw [lact_mul_upper_bounds, hx1, hy2]
  have hfree : lact (γ2⁻¹ * γ1) (cpt X x0 (D.zOf y1)) = rmul (cpt X x0 (D.zOf y1)) (rmul (D.bOf y2) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y1) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) := by
    calc lact (γ2⁻¹ * γ1) (cpt X x0 (D.zOf y1)) = rmul (rmul (lact (γ2⁻¹ * γ1) (cpt X x0 (D.zOf y1))) (D.bOf y1)) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y1) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) :=
          (rmul_rmul_inv_mat_eq_self hB1).symm
      _ = rmul (lact (γ2⁻¹ * γ1) (rmul (cpt X x0 (D.zOf y1)) (D.bOf y1))) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y1) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) := by
        first
          | rw [lact_rmul_eq_rmul_lact]
          | exact congrArg (fun w => rmul w _) (lact_rmul_eq_rmul_lact _ _ _).symm
      _ = rmul (rmul (cpt X x0 (D.zOf y2)) (D.bOf y2)) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y1) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) := by rw [← he1, hB', ← he2]
      _ = rmul (cpt X x0 (D.zOf y1)) (rmul (D.bOf y2) (fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (D.bOf y1) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) := by
        rw [← hw]
        exact rmul_assoc_frame _ _ _
  have h1' := X.Γ_free _ hg _ hO1 _ (mem_bor_rmul hB2 (FD_mat_inv_mem_bor hB1)) hfree
  exact (inv_mul_eq_one.1 h1').symm

theorem lunfold_one (hM : MeasInvStatement (E := E)) (hx0 : IsOrth X x0) (hFF : IsFundSet X x0 FF)
    (φ : Frame X.Ψ r → ℝ≥0∞) (hφ : Measurable φ)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    ∫⁻ z in FF, φ (lact γ (cpt X x0 z)) ∂muF X x0 =
      ∫⁻ z, (T D FF).indicator 1 (lact γ⁻¹ (cpt X x0 z)) * φ (cpt X x0 z) ∂muF X x0 := by
  classical
  obtain ⟨Fn, hFn⟩ : ∃ Fn : Frame X.Ψ r → ℝ≥0∞,
      Fn = fun x => (T D FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞) (lact γ⁻¹ x) * φ x := ⟨_, rfl⟩
  have hFm : Measurable Fn := by
    rw [hFn]
    exact ((measurable_one.indicator (measurableSet_T D FF hFF.1)).comp (measurable_lact γ⁻¹)).mul hφ
  have hFB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Fn (rmul x b) = Fn x := by
    intro x hx b hb
    rw [hFn]
    simp only [ind_rmul D FF hγ hx hb (M := ℝ≥0∞), hB x hx b hb]
  have hpt : ∀ z ∈ OmF X x0,
      FF.indicator (fun z => φ (lact γ (cpt X x0 z))) z = Fn (lact γ (cpt X x0 z)) := by
    intro z hz
    rw [hFn]
    dsimp only
    rw [lact_inv_apply_lact, ind_cpt D FF hz (M := ℝ≥0∞)]
    by_cases h : z ∈ FF
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Pi.one_apply, one_mul]
    · first
        | rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
        | rw [Set.indicator_of_not_mem h, Set.indicator_of_not_mem h, zero_mul]
  rw [← lintegral_indicator hFF.1]
  calc ∫⁻ z, FF.indicator (fun z => φ (lact γ (cpt X x0 z))) z ∂muF X x0
      = ∫⁻ z, Fn (lact γ (cpt X x0 z)) ∂muF X x0 :=
        lintegral_congr_ae ((ae_mem_omF x0).mono fun z hz => hpt z hz)
    _ = ∫⁻ z, Fn (cpt X (lact γ x0) z) ∂muF X (lact γ x0) := by
        rw [muF_lact_upper_bounds hγ]
        simp only [cpt_lact_upper_bounds]
    _ = ∫⁻ z, Fn (cpt X x0 z) ∂muF X x0 :=
        hM r X (lact γ x0) x0 (isOrth_lact' hγ hx0) hx0 Fn hFm hFB
    _ = _ := by rw [hFn]

include D in
theorem lunfold (hM : MeasInvStatement (E := E)) (hx0 : IsOrth X x0) (hFF : IsFundSet X x0 FF)
    (φ : Frame X.Ψ r → ℝ≥0∞) (hφ : Measurable φ)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) :
    ∑' γ : X.Γ, ∫⁻ z in FF, φ (lact γ.1 (cpt X x0 z)) ∂muF X x0 = ∫⁻ z, φ (cpt X x0 z) ∂muF X x0 := by
  classical
  rw [tsum_congr fun γ : X.Γ => lunfold_one D FF hM hx0 hFF φ hφ hB γ.2]
  rw [← lintegral_tsum]
  swap
  · intro γ
    exact (((measurable_one.indicator (measurableSet_T D FF hFF.1)).comp
      ((measurable_lact γ.1⁻¹).comp (continuous_cpt_apply x0).measurable)).mul
      (hφ.comp (continuous_cpt_apply x0).measurable)).aemeasurable
  apply lintegral_congr_ae
  filter_upwards [ae_mem_omF x0, hFF.2.2.2] with z hz hcov
  obtain ⟨z', hz'F, γ0, hγ0, b0, hb0, hx⟩ := hcov
  have hx' : lact γ0⁻¹ (cpt X x0 z) = rmul (cpt X x0 z') b0 := by rw [hx, lact_inv_apply_lact]
  have hz'O : z' ∈ OmF X x0 := hFF.2.1 hz'F
  obtain ⟨hΔ', hzz', -⟩ := D.uniq z' hz'O b0 hb0
  have hxT : lact γ0⁻¹ (cpt X x0 z) ∈ T D FF := by
    rw [hx']
    show _ ∧ _ ∧ _
    refine ⟨rmul_mem_dom_of_mem_dom hb0 hz'O, hΔ', ?_⟩
    rw [hzz']
    exact hz'F
  have hsum : ∑' γ : X.Γ, (T D FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞) (lact γ.1⁻¹ (cpt X x0 z)) = 1 := by
    rw [tsum_eq_single ⟨γ0, hγ0⟩]
    · exact Set.indicator_of_mem hxT 1
    · intro γ hne
      have hnT : lact γ.1⁻¹ (cpt X x0 z) ∉ T D FF := fun hγT =>
        hne (Subtype.ext (eq_of_lact_inv_cpt_mem_T D FF hFF hz γ.2 hγ0 hγT hxT))
      first
        | exact Set.indicator_of_notMem hnT 1
        | exact Set.indicator_of_not_mem hnT 1
  show ∑' γ : X.Γ, (T D FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞) (lact γ.1⁻¹ (cpt X x0 z)) *
    φ (cpt X x0 z) = φ (cpt X x0 z)
  rw [ENNReal.tsum_mul_right, hsum, one_mul]

private theorem real_invariance_of_measInvStatement (hM : MeasInvStatement (E := E)) {y0 y1 : Frame X.Ψ r}
    (h0 : IsOrth X y0) (h1 : IsOrth X y1) (g : Frame X.Ψ r → ℝ) (hg : Measurable g)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, g (rmul x b) = g x) :
    ∫ z, g (cpt X y0 z) ∂muF X y0 = ∫ z, g (cpt X y1 z) ∂muF X y1 := by
  have hm0 : Measurable fun z => g (cpt X y0 z) := hg.comp (continuous_cpt_apply y0).measurable
  have hm1 : Measurable fun z => g (cpt X y1 z) := hg.comp (continuous_cpt_apply y1).measurable
  have hpos : ∫⁻ z, ENNReal.ofReal (g (cpt X y0 z)) ∂muF X y0 =
      ∫⁻ z, ENNReal.ofReal (g (cpt X y1 z)) ∂muF X y1 :=
    hM r X y0 y1 h0 h1 (fun x => ENNReal.ofReal (g x)) (ENNReal.measurable_ofReal.comp hg)
      (fun x hx b hb => by simp only [hB x hx b hb])
  have hneg : ∫⁻ z, ENNReal.ofReal (-g (cpt X y0 z)) ∂muF X y0 =
      ∫⁻ z, ENNReal.ofReal (-g (cpt X y1 z)) ∂muF X y1 :=
    hM r X y0 y1 h0 h1 (fun x => ENNReal.ofReal (-g x)) (ENNReal.measurable_ofReal.comp hg.neg)
      (fun x hx b hb => by simp only [hB x hx b hb])
  have hn : ∫⁻ z, ‖g (cpt X y0 z)‖ₑ ∂muF X y0 = ∫⁻ z, ‖g (cpt X y1 z)‖ₑ ∂muF X y1 :=
    hM r X y0 y1 h0 h1 (fun x => ‖g x‖ₑ) hg.enorm (fun x hx b hb => by simp only [hB x hx b hb])
  by_cases hi : Integrable (fun z => g (cpt X y0 z)) (muF X y0)
  · have hi' : Integrable (fun z => g (cpt X y1 z)) (muF X y1) := by
      refine ⟨hm1.aestronglyMeasurable, ?_⟩
      have h2 := hi.2
      unfold HasFiniteIntegral at h2 ⊢
      rwa [← hn]
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi', hpos, hneg]
  · have hi' : ¬ Integrable (fun z => g (cpt X y1 z)) (muF X y1) := by
      intro h
      refine hi ⟨hm0.aestronglyMeasurable, ?_⟩
      have h2 := h.2
      unfold HasFiniteIntegral at h2 ⊢
      rwa [hn]
    rw [integral_undef hi, integral_undef hi']

theorem cMeasInv (hM : MeasInvStatement (E := E)) (hx0 : IsOrth X x0) {x0' : Frame X.Ψ r}
    (hx0' : IsOrth X x0') (ψ : Frame X.Ψ r → ℂ) (hψ : Measurable ψ)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x) :
    ∫ z, ψ (cpt X x0 z) ∂muF X x0 = ∫ z, ψ (cpt X x0' z) ∂muF X x0' := by
  have hm0 : Measurable fun z => ψ (cpt X x0 z) := hψ.comp (continuous_cpt_apply x0).measurable
  have hm1 : Measurable fun z => ψ (cpt X x0' z) := hψ.comp (continuous_cpt_apply x0').measurable
  have hn : ∫⁻ z, ‖ψ (cpt X x0 z)‖ₑ ∂muF X x0 = ∫⁻ z, ‖ψ (cpt X x0' z)‖ₑ ∂muF X x0' :=
    hM r X x0 x0' hx0 hx0' (fun x => ‖ψ x‖ₑ) hψ.enorm (fun x hx b hb => by simp only [hB x hx b hb])
  by_cases hi : Integrable (fun z => ψ (cpt X x0 z)) (muF X x0)
  · have hi' : Integrable (fun z => ψ (cpt X x0' z)) (muF X x0') := by
      refine ⟨hm1.aestronglyMeasurable, ?_⟩
      have h2 := hi.2
      unfold HasFiniteIntegral at h2 ⊢
      rwa [← hn]
    apply Complex.ext
    · have e0 := Complex.reCLM.integral_comp_comm hi
      have e1 := Complex.reCLM.integral_comp_comm hi'
      simp only [Complex.reCLM_apply] at e0 e1
      rw [← e0, ← e1]
      exact real_invariance_of_measInvStatement hM hx0 hx0' (fun x => (ψ x).re) (Complex.measurable_re.comp hψ)
        (fun x hx b hb => by simp only [hB x hx b hb])
    · have e0 := Complex.imCLM.integral_comp_comm hi
      have e1 := Complex.imCLM.integral_comp_comm hi'
      simp only [Complex.imCLM_apply] at e0 e1
      rw [← e0, ← e1]
      exact real_invariance_of_measInvStatement hM hx0 hx0' (fun x => (ψ x).im) (Complex.measurable_im.comp hψ)
        (fun x hx b hb => by simp only [hB x hx b hb])
  · have hi' : ¬ Integrable (fun z => ψ (cpt X x0' z)) (muF X x0') := by
      intro h
      refine hi ⟨hm0.aestronglyMeasurable, ?_⟩
      have h2 := h.2
      unfold HasFiniteIntegral at h2 ⊢
      rwa [hn]
    rw [integral_undef hi, integral_undef hi']

theorem cunfold_one (hM : MeasInvStatement (E := E)) (hx0 : IsOrth X x0) (hFF : IsFundSet X x0 FF)
    (G : Frame X.Ψ r → ℂ) (hG : Measurable G)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    ∫ z in FF, G (lact γ (cpt X x0 z)) ∂muF X x0 =
      ∫ z, (T D FF).indicator (1 : Frame X.Ψ r → ℂ) (lact γ⁻¹ (cpt X x0 z)) * G (cpt X x0 z) ∂muF X x0 := by
  classical
  obtain ⟨Fn, hFn⟩ : ∃ Fn : Frame X.Ψ r → ℂ,
      Fn = fun x => (T D FF).indicator (1 : Frame X.Ψ r → ℂ) (lact γ⁻¹ x) * G x := ⟨_, rfl⟩
  have hFm : Measurable Fn := by
    rw [hFn]
    exact ((measurable_one.indicator (measurableSet_T D FF hFF.1)).comp (measurable_lact γ⁻¹)).mul hG
  have hFB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Fn (rmul x b) = Fn x := by
    intro x hx b hb
    rw [hFn]
    simp only [ind_rmul D FF hγ hx hb (M := ℂ), hB x hx b hb]
  have hpt : ∀ z ∈ OmF X x0,
      FF.indicator (fun z => G (lact γ (cpt X x0 z))) z = Fn (lact γ (cpt X x0 z)) := by
    intro z hz
    rw [hFn]
    dsimp only
    rw [lact_inv_apply_lact, ind_cpt D FF hz (M := ℂ)]
    by_cases h : z ∈ FF
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Pi.one_apply, one_mul]
    · first
        | rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
        | rw [Set.indicator_of_not_mem h, Set.indicator_of_not_mem h, zero_mul]
  rw [← integral_indicator hFF.1]
  calc ∫ z, FF.indicator (fun z => G (lact γ (cpt X x0 z))) z ∂muF X x0
      = ∫ z, Fn (lact γ (cpt X x0 z)) ∂muF X x0 :=
        integral_congr_ae ((ae_mem_omF x0).mono fun z hz => hpt z hz)
    _ = ∫ z, Fn (cpt X (lact γ x0) z) ∂muF X (lact γ x0) := by
        rw [muF_lact_upper_bounds hγ]
        simp only [cpt_lact_upper_bounds]
    _ = ∫ z, Fn (cpt X x0 z) ∂muF X x0 :=
        cMeasInv hM (isOrth_lact' hγ hx0) hx0 Fn hFm hFB
    _ = _ := by rw [hFn]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
end

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem norm_chi {la : Wt X.Ψ r} {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) : ‖X.χ la γ‖ = 1 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  have := congrArg norm (h γ hγ)
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp this

theorem conj_chi {la : Wt X.Ψ r} {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    (starRingEnd ℂ) (X.χ la γ) = (X.χ la γ)⁻¹ := by
  have h := norm_chi X (la := la) hγ
  have hn : Complex.normSq (X.χ la γ) = 1 := by rw [Complex.normSq_eq_norm_sq, h, one_pow]
  rw [Complex.inv_def, hn, inv_one, Complex.ofReal_one, mul_one]

theorem meas_indC {f : Frame X.Ψ r → ℂ} (hf : ContinuousOn f X.dom) : Measurable (X.dom.indicator f) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact hf.measurable_piecewise continuousOn_const (FourierCoefficientDomain.isOpen_dom X).measurableSet

def Gu (P f0 : Frame X.Ψ r → ℂ) (W : Frame X.Ψ r → ℝ≥0∞) (x : Frame X.Ψ r) : ℂ :=
  X.dom.indicator P x * (starRingEnd ℂ) (X.dom.indicator f0 x) * ((W x).toReal : ℂ)

def phi0 (f0 : Frame X.Ψ r → ℂ) (W : Frame X.Ψ r → ℝ≥0∞) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  ENNReal.ofReal (‖X.dom.indicator f0 x‖ ^ 2) * W x

theorem Gu_dom {P f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞} {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Gu X P f0 W x = P x * (starRingEnd ℂ) (f0 x) * ((W x).toReal : ℂ) := by
  simp [Gu, Set.indicator_of_mem hx]

theorem unfoldedDensity_on_dom {f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞} {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    phi0 X f0 W x = ENNReal.ofReal (‖f0 x‖ ^ 2) * W x := by
  simp [phi0, Set.indicator_of_mem hx]

theorem Gu_meas {P f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞} (hP : ContinuousOn P X.dom)
    (hf : ContinuousOn f0 X.dom) (hW : Measurable W) : Measurable (Gu X P f0 W) :=
  ((meas_indC X hP).mul (Complex.continuous_conj.measurable.comp (meas_indC X hf))).mul
    (Complex.measurable_ofReal.comp hW.ennreal_toReal)

theorem measurable_unfoldedDensity {f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞} (hf : ContinuousOn f0 X.dom)
    (hW : Measurable W) : Measurable (phi0 X f0 W) :=
  (ENNReal.measurable_ofReal.comp ((meas_indC X hf).norm.pow_const 2)).mul hW

theorem Gu_rmul {la : Wt X.Ψ r} {P f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞}
    (hP : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x)
    (hf : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, f0 (rmul x b) = bchar la b * f0 x)
    (hW : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, W (rmul x b) = W x / ENNReal.ofReal (‖bchar la b‖ ^ 2))
    {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) :
    Gu X P f0 W (rmul x b) = Gu X P f0 W x := by
  rw [Gu_dom X (OrthogonalFrameDomain.rmul_mem_dom X hx hb), Gu_dom X hx, hP x hx b hb, hf x hx b hb, hW x hx b hb]
  have hc : bchar la b ≠ 0 := bchar_ne X hb la
  have hn : (‖bchar la b‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hc
  have hcc : bchar la b * (starRingEnd ℂ) (bchar la b) = (‖bchar la b‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (by positivity), map_mul]
  push_cast
  rw [show bchar la b * P x * ((starRingEnd ℂ) (bchar la b) * (starRingEnd ℂ) (f0 x)) *
      (((W x).toReal : ℂ) / (‖bchar la b‖ : ℂ) ^ 2) = (bchar la b * (starRingEnd ℂ) (bchar la b)) *
      (P x * (starRingEnd ℂ) (f0 x) * ((W x).toReal : ℂ)) / (‖bchar la b‖ : ℂ) ^ 2 by ring, hcc]
  field_simp

theorem unfoldedDensity_borel_invariant {la : Wt X.Ψ r} {f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞}
    (hf : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, f0 (rmul x b) = bchar la b * f0 x)
    (hW : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, W (rmul x b) = W x / ENNReal.ofReal (‖bchar la b‖ ^ 2))
    {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) :
    phi0 X f0 W (rmul x b) = phi0 X f0 W x := by
  rw [unfoldedDensity_on_dom X (OrthogonalFrameDomain.rmul_mem_dom X hx hb), unfoldedDensity_on_dom X hx, hf x hx b hb, hW x hx b hb]
  have hc : bchar la b ≠ 0 := bchar_ne X hb la
  have h0 : ENNReal.ofReal (‖bchar la b‖ ^ 2) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    exact pow_pos (norm_pos_iff.mpr hc) 2
  rw [norm_mul, mul_pow, ENNReal.ofReal_mul (by positivity)]
  rw [show ENNReal.ofReal (‖bchar la b‖ ^ 2) * ENNReal.ofReal (‖f0 x‖ ^ 2) *
      (W x / ENNReal.ofReal (‖bchar la b‖ ^ 2)) = ENNReal.ofReal (‖f0 x‖ ^ 2) *
      (W x / ENNReal.ofReal (‖bchar la b‖ ^ 2) * ENNReal.ofReal (‖bchar la b‖ ^ 2)) by ring,
    ENNReal.div_mul_cancel h0 ENNReal.ofReal_ne_top]

theorem unfoldedDensity_gamma_invariant {la : Wt X.Ψ r} {f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞}
    (hf : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, f0 (lact γ x) = X.χ la γ * f0 x)
    (hW : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, W (lact γ x) = W x)
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    phi0 X f0 W (lact γ x) = phi0 X f0 W x := by
  rw [unfoldedDensity_on_dom X ((lact_mem_dom_iff X hγ x).mpr hx), unfoldedDensity_on_dom X hx, hf γ hγ x hx, hW γ hγ x hx,
    norm_mul, norm_chi X hγ, one_mul]

theorem ineq_pt (a b : ℂ) (w : ℝ≥0∞) {k : ℝ} (hk : 0 < k) :
    ‖a * (starRingEnd ℂ) b * ((w.toReal : ℝ) : ℂ)‖ₑ ≤
      ENNReal.ofReal (‖a‖ ^ 2 / k) * w + ENNReal.ofReal k * (ENNReal.ofReal (‖b‖ ^ 2) * w) := by
  rcases eq_or_ne w ⊤ with rfl | hw
  · simp
  · have hw' : w = ENNReal.ofReal w.toReal := (ENNReal.ofReal_toReal hw).symm
    have ht : 0 ≤ w.toReal := ENNReal.toReal_nonneg
    rw [← ofReal_norm]
    conv_rhs => rw [hw']
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul hk.le, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg ht]
    have hA := norm_nonneg a
    have hB := norm_nonneg b
    have h1 : ‖a‖ ^ 2 / k + k * ‖b‖ ^ 2 - 2 * (‖a‖ * ‖b‖) = (‖a‖ - k * ‖b‖) ^ 2 / k := by
      field_simp; ring
    have h2 : 0 ≤ (‖a‖ - k * ‖b‖) ^ 2 / k := div_nonneg (sq_nonneg _) hk.le
    have h3 : 0 ≤ ‖a‖ ^ 2 / k + k * ‖b‖ ^ 2 - ‖a‖ * ‖b‖ := by nlinarith [mul_nonneg hA hB]
    nlinarith [mul_nonneg ht h3]

theorem enorm_ind_mul {M : Set (Frame X.Ψ r)} (y : Frame X.Ψ r) (c : ℂ) :
    ‖M.indicator (1 : Frame X.Ψ r → ℂ) y * c‖ₑ = M.indicator (1 : Frame X.Ψ r → ℝ≥0∞) y * ‖c‖ₑ := by
  by_cases h : y ∈ M
  · simp [Set.indicator, h]
  · simp [Set.indicator, h]

theorem ka_meas (x0 : Frame X.Ψ r) (bb : ℝ) : Measurable (kaF X x0 bb) := by
  have hd : ∀ τ : X.Ψ, Measurable fun z => dmin X.Gm (cpt X x0 z) τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ :=
    fun τ => ((ExtFPf.cont_dmin X τ _).comp (cpt_cont X x0)).measurable
  unfold kaF rhF
  exact Real.measurable_exp.comp (measurable_const.mul
    (Finset.measurable_sum _ fun τ _ => Real.measurable_log.comp (hd τ).norm).neg)

theorem pairUnfold_of (hM : MeasInvStatement (E := E)) (hK : KaUnfoldStatement (E := E))
    (hLU : LUStatement (E := E)) : PairUnfoldStatement (E := E) := by
  intro r X x0 hx0 hPD la W bb hW hWl hbb F P hF hInAt hP hPF FF hFF f0 hf0 hf0FF
  obtain ⟨D⟩ := ExtFPf.luData_of hLU X x0 hx0
  have hf0S : X.IsSec la f0 := hf0.1.1
  have hGm : Measurable (Gu X P f0 W) := Gu_meas X hP.1.continuousOn hf0S.1.continuousOn hW.1
  have hGB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Gu X P f0 W (rmul x b) = Gu X P f0 W x :=
    fun x hx b hb => Gu_rmul X hP.2 hf0S.2.1 hW.2.1 hx hb
  have hnB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ‖Gu X P f0 W (rmul x b)‖ₑ = ‖Gu X P f0 W x‖ₑ :=
    fun x hx b hb => by rw [hGB x hx b hb]
  have hG_lact : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, Gu X P f0 W (lact γ x) =
      (X.χ la γ)⁻¹ * P (lact γ x) * (starRingEnd ℂ) (f0 x) * ((W x).toReal : ℂ) := by
    intro γ hγ x hx
    rw [Gu_dom X ((lact_mem_dom_iff X hγ x).mpr hx), hf0S.2.2 γ hγ x hx, hW.2.2 γ hγ x hx, map_mul,
      conj_chi X hγ]
    ring

  have hfin : ∫⁻ z, ‖Gu X P f0 W (cpt X x0 z)‖ₑ ∂muF X x0 < ⊤ := by
    obtain ⟨C, hC, hCle⟩ := hK r X x0 hx0 hPD FF hFF bb hbb
    have hI2 : ∫⁻ z, ENNReal.ofReal (kaF X x0 bb z) * phi0 X f0 W (cpt X x0 z) ∂muF X x0 < ⊤ := by
      refine lt_of_le_of_lt (hCle _ (measurable_unfoldedDensity X hf0S.1.continuousOn hW.1)
        (fun x hx b hb => unfoldedDensity_borel_invariant X hf0S.2.1 hW.2.1 hx hb)
        (fun γ hγ x hx => unfoldedDensity_gamma_invariant X hf0S.2.2 hW.2.2 hγ hx)) (ENNReal.mul_lt_top hC ?_)
      have : ∫⁻ z in FF, phi0 X f0 W (cpt X x0 z) ∂muF X x0 =
          ∫⁻ z in FF, ENNReal.ofReal (‖f0 (cpt X x0 z)‖ ^ 2) * W (cpt X x0 z) ∂muF X x0 :=
        setLIntegral_congr_fun hFF.1 fun z hz => unfoldedDensity_on_dom X (hFF.2.1 hz)
      rw [this]; exact hf0FF
    calc ∫⁻ z, ‖Gu X P f0 W (cpt X x0 z)‖ₑ ∂muF X x0
        ≤ ∫⁻ z, (ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z) +
            ENNReal.ofReal (kaF X x0 bb z) * phi0 X f0 W (cpt X x0 z)) ∂muF X x0 := by
          refine lintegral_mono_ae ?_
          filter_upwards [ExtFPf.ae_OmF] with z hz
          rw [Gu_dom X hz, unfoldedDensity_on_dom X hz, hPF z hz]
          exact ineq_pt _ _ _ (Real.exp_pos _)
      _ = ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z) ∂muF X x0 +
            ∫⁻ z, ENNReal.ofReal (kaF X x0 bb z) * phi0 X f0 W (cpt X x0 z) ∂muF X x0 :=
          lintegral_add_right _ ((ENNReal.measurable_ofReal.comp (ka_meas X x0 bb)).mul
            ((measurable_unfoldedDensity X hf0S.1.continuousOn hW.1).comp (cpt_cont X x0).measurable))
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hInAt, hI2⟩
  have hsum1 : ∑' γ : X.Γ, ∫⁻ z in FF, ‖Gu X P f0 W (lact γ.1 (cpt X x0 z))‖ₑ ∂muF X x0 < ⊤ := by
    rw [lunfold D FF hM hx0 hFF (fun x => ‖Gu X P f0 W x‖ₑ) hGm.enorm hnB]; exact hfin

  have hL : Set.EqOn (fun z => poin X la P (cpt X x0 z) * (starRingEnd ℂ) (f0 (cpt X x0 z)) *
      ((W (cpt X x0 z)).toReal : ℂ)) (fun z => ∑' γ : X.Γ, Gu X P f0 W (lact γ.1 (cpt X x0 z))) FF := by
    intro z hz
    have hzd : cpt X x0 z ∈ X.dom := hFF.2.1 hz
    simp only [poin]
    rw [← tsum_mul_right, ← tsum_mul_right]
    exact tsum_congr fun γ => (hG_lact γ.1 γ.2 _ hzd).symm
  rw [setIntegral_congr_fun hFF.1 hL]
  have hmeas1 : ∀ γ : X.Γ, AEStronglyMeasurable (fun z => Gu X P f0 W (lact γ.1 (cpt X x0 z)))
      ((muF X x0).restrict FF) := fun γ =>
    (hGm.comp ((lact_cont X γ.1).comp (cpt_cont X x0)).measurable).aestronglyMeasurable
  rw [integral_tsum hmeas1 hsum1.ne]
  have hcu : ∀ γ : X.Γ, ∫ z in FF, Gu X P f0 W (lact γ.1 (cpt X x0 z)) ∂muF X x0 =
      ∫ z, (T D FF).indicator (1 : Frame X.Ψ r → ℂ) (lact γ.1⁻¹ (cpt X x0 z)) * Gu X P f0 W (cpt X x0 z)
        ∂muF X x0 := fun γ => cunfold_one D FF hM hx0 hFF _ hGm hGB γ.2
  rw [tsum_congr hcu]
  have hmeas2 : ∀ γ : X.Γ, AEStronglyMeasurable (fun z => (T D FF).indicator (1 : Frame X.Ψ r → ℂ)
      (lact γ.1⁻¹ (cpt X x0 z)) * Gu X P f0 W (cpt X x0 z)) (muF X x0) := by
    intro γ
    have h1 : Measurable ((T D FF).indicator (1 : Frame X.Ψ r → ℂ)) :=
      measurable_one.indicator (T_meas D FF hFF.1)
    have h2 : Measurable fun z => lact γ.1⁻¹ (cpt X x0 z) :=
      ((lact_cont X γ.1⁻¹).comp (cpt_cont X x0)).measurable
    exact ((h1.comp h2).mul (hGm.comp (cpt_cont X x0).measurable)).aestronglyMeasurable
  have hsum2 : ∑' γ : X.Γ, ∫⁻ z, ‖(T D FF).indicator (1 : Frame X.Ψ r → ℂ) (lact γ.1⁻¹ (cpt X x0 z)) *
      Gu X P f0 W (cpt X x0 z)‖ₑ ∂muF X x0 ≠ ⊤ := by
    have : ∀ γ : X.Γ, ∫⁻ z, ‖(T D FF).indicator (1 : Frame X.Ψ r → ℂ) (lact γ.1⁻¹ (cpt X x0 z)) *
        Gu X P f0 W (cpt X x0 z)‖ₑ ∂muF X x0 =
        ∫⁻ z in FF, ‖Gu X P f0 W (lact γ.1 (cpt X x0 z))‖ₑ ∂muF X x0 := fun γ => by
      rw [lunfold_one D FF hM hx0 hFF (fun x => ‖Gu X P f0 W x‖ₑ) hGm.enorm hnB γ.2]
      simp only [enorm_ind_mul]
    rw [tsum_congr this]; exact hsum1.ne
  rw [← integral_tsum hmeas2 hsum2]
  refine integral_congr_ae ?_
  filter_upwards [ae_unique D FF hFF] with z ⟨hzO, γ0, hγ0, hu⟩
  rw [tsum_eq_single ⟨γ0, hγ0⟩]
  · rw [Set.indicator_of_mem ((hu γ0 hγ0).mpr rfl), Pi.one_apply, one_mul, Gu_dom X hzO, hPF z hzO]
  · intro γ hne
    rw [Set.indicator_of_notMem, zero_mul]
    intro h
    exact hne (Subtype.ext ((hu γ.1 γ.2).mp h))

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
