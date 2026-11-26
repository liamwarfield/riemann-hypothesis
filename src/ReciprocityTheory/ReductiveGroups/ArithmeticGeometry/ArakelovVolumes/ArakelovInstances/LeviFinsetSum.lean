module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.LminorMapConj

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.DetSubMapConj
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def Dsg : Fin r → ℝ := fun a => sgn X.p0 (a : ℕ)

theorem Dsg_ne (a : Fin r) : Dsg X a ≠ 0 := by
  unfold Dsg sgn
  split_ifs <;> norm_num

def Xd (z u : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  (mat (nmat X z) τ)⁻¹ * KapPf.Lin X τ u

def Yd (b : Frame X.Ψ r) (z u : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  (mat b τ)⁻¹ * Xd X z u τ * mat b τ

theorem nmat_det_unit (z : V (nd X)) (τ : X.Ψ) : IsUnit (mat (nmat X z) τ).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (KapPf.isUnit_nmat X τ z)

theorem mat_line (x0 b : Frame X.Ψ r) (hb : b ∈ Bor X.Ψ r) (z u : V (nd X)) (τ : X.Ψ) (ζ : ℂ) :
    mat (cpt X x0 (z + ζ • u)) τ =
      mat (rmul (cpt X x0 z) b) τ * ((1 + ζ • Yd X b z u τ) * (mat b τ)⁻¹) := by
  have hBu : IsUnit (mat b τ).det := isUnit_iff_ne_zero.2 (hb τ).1
  have hNu := nmat_det_unit X z τ
  show mat x0 τ * mat (nmat X (z + ζ • u)) τ =
    mat x0 τ * mat (nmat X z) τ * mat b τ *
      ((1 + ζ • ((mat b τ)⁻¹ * ((mat (nmat X z) τ)⁻¹ * KapPf.Lin X τ u) * mat b τ)) * (mat b τ)⁻¹)
  rw [KapPf.nmat_eq X (z + ζ • u) τ, map_add (f := _), map_smul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hBu, Matrix.mul_nonsing_inv _ hBu,
    Matrix.mul_nonsing_inv_cancel_left _ _ hNu]
  rw [KapPf.nmat_eq X z τ]
  simp only [Matrix.mul_add, Matrix.mul_one]
  abel

theorem upper_inv (B : Matrix (Fin r) (Fin r) ℂ) (hBd : B.det ≠ 0) (hB : ∀ a c : Fin r, c < a → B a c = 0) :
    ∀ a c : Fin r, c < a → B⁻¹ a c = 0 := by
  intro a c hca
  have := B.invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 hBd)
  have hBT : B.BlockTriangular id := fun i j h => hB i j h
  exact (Matrix.blockTriangular_inv_of_blockTriangular hBT) hca

theorem det_sub_map_conj (M : Matrix (Fin r) (Fin r) ℂ) {m : ℕ} (hm : m ≤ r) :
    ((M.map (starRingEnd ℂ)).submatrix (Fin.castLE hm) (Fin.castLE hm)).det =
      starRingEnd ℂ (M.submatrix (Fin.castLE hm) (Fin.castLE hm)).det := by
  rw [Matrix.submatrix_map]
  exact (RingHom.map_det _ _).symm

theorem dmin_line (x0 b : Frame X.Ψ r) (hb : b ∈ Bor X.Ψ r) (z u : V (nd X)) (τ : X.Ψ)
    (hgram : gram τ.1 X.Gm (mat (rmul (cpt X x0 z) b) τ) = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (ζ : ℂ) (k : Fin (r + 1)) :
    dmin X.Gm (cpt X x0 (z + ζ • u)) τ k =
      ((mat b τ)⁻¹.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det *
        starRingEnd ℂ (Gz (Nat.le_of_lt_succ k.isLt) (Dsg X) (Yd X b z u τ) ζ).det *
        starRingEnd ℂ ((mat b τ)⁻¹.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt))
          (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det := by
  have hk := Nat.le_of_lt_succ k.isLt
  have hL : ∀ a c : Fin r, c < a → (mat b τ)⁻¹ a c = 0 :=
    upper_inv (mat b τ) (hb τ).1 (fun a c h => (hb τ).2 a c h)
  have hU : ∀ a c : Fin r, c < a → ((mat b τ)⁻¹.map (starRingEnd ℂ)) a c = 0 := by
    intro a c h
    rw [Matrix.map_apply, hL a c h, map_zero]
  have hgram' : gram τ.1 X.Gm (mat (rmul (cpt X x0 z) b) τ) = diagonal fun a : Fin r => ((Dsg X a : ℝ) : ℂ) := hgram
  have hre : ((1 + ζ • Yd X b z u τ) * (mat b τ)⁻¹)ᵀ * (diagonal fun a : Fin r => ((Dsg X a : ℝ) : ℂ)) *
        ((1 + ζ • Yd X b z u τ) * (mat b τ)⁻¹).map (starRingEnd ℂ) =
      ((mat b τ)⁻¹)ᵀ * ((1 + ζ • Yd X b z u τ)ᵀ * (diagonal fun a : Fin r => ((Dsg X a : ℝ) : ℂ)) *
        (1 + ζ • Yd X b z u τ).map (starRingEnd ℂ)) * (mat b τ)⁻¹.map (starRingEnd ℂ) := by
    rw [Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  calc dmin X.Gm (cpt X x0 (z + ζ • u)) τ k
      = lminor (((mat b τ)⁻¹)ᵀ * ((1 + ζ • Yd X b z u τ)ᵀ * (diagonal fun a : Fin r => ((Dsg X a : ℝ) : ℂ)) *
          (1 + ζ • Yd X b z u τ).map (starRingEnd ℂ)) * (mat b τ)⁻¹.map (starRingEnd ℂ)) k := by
        show lminor (gram τ.1 X.Gm (mat (cpt X x0 (z + ζ • u)) τ)) k = _
        rw [mat_line X x0 b hb z u τ ζ, ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_mul, hgram', hre]
    _ = ((mat b τ)⁻¹.submatrix (Fin.castLE hk) (Fin.castLE hk)).det *
          lminor ((1 + ζ • Yd X b z u τ)ᵀ * (diagonal fun a : Fin r => ((Dsg X a : ℝ) : ℂ)) *
            (1 + ζ • Yd X b z u τ).map (starRingEnd ℂ)) k *
          (((mat b τ)⁻¹.map (starRingEnd ℂ)).submatrix (Fin.castLE hk) (Fin.castLE hk)).det :=
        lminor_LMU _ _ _ hL hU k
    _ = _ := by
        rw [tr_D_conj, lminor_map_conj, det_sub_map_conj (mat b τ)⁻¹ hk]
        rfl

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
end
end

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates ReciprocityTheory.AnForm Filter Topology

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem neg2log_nfac (la : Wt X.Ψ r) (x : Frame X.Ψ r) (hx : ∀ τ i, dmin X.Gm x τ i ≠ 0) :
    -2 * Real.log (X.nfac la x) = ∑ τ, ∑ i : Fin r, (la τ i : ℝ) *
      (Real.log ‖dmin X.Gm x τ i.succ‖ - Real.log ‖dmin X.Gm x τ i.castSucc‖) := by
  unfold Data.nfac
  have hpos : ∀ τ (i : Fin r), 0 < ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ :=
    fun τ i => norm_pos_iff.2 (div_ne_zero (hx _ _) (hx _ _))
  rw [Real.log_prod (fun τ _ => (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hpos τ i) _).ne'),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (hpos τ i) _).ne'), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.log_rpow (hpos τ i), norm_div, Real.log_div (norm_ne_zero_iff.2 (hx _ _)) (norm_ne_zero_iff.2 (hx _ _))]
  ring

theorem levi_const {ι : Type} [Fintype ι] (c : ℝ) (z w : ι → ℂ) : levi (fun _ => c) z w = 0 := by
  unfold levi
  have h : (fderiv ℝ fun _ : ι → ℂ => c) = fun _ => 0 := by
    funext x
    exact fderiv_const_apply c
  rw [h]
  simp

theorem levi_affine {ι : Type} [Fintype ι] (K c : ℝ) (f : (ι → ℂ) → ℝ) (z w : ι → ℂ)
    (hf : ContDiffAt ℝ 2 f z) : levi (fun v => K + c * f v) z w = c * levi f z w := by
  rw [levi_add_smul c contDiffAt_const hf, levi_const, zero_add]

theorem levi_finset_sum {ι κ : Type} [Fintype ι] (s : Finset κ) (F : κ → (ι → ℂ) → ℝ) (z w : ι → ℂ)
    (hF : ∀ j ∈ s, ContDiffAt ℝ 2 (F j) z) :
    levi (fun v => ∑ j ∈ s, F j v) z w = ∑ j ∈ s, levi (F j) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [levi_const]
  | insert a s ha ih =>
    have hs : ContDiffAt ℝ 2 (fun v => ∑ j ∈ s, F j v) z :=
      ContDiffAt.sum fun j hj => hF j (Finset.mem_insert_of_mem hj)
    have e : (fun v => ∑ j ∈ insert a s, F j v) = fun v => (∑ j ∈ s, F j v) + 1 * F a v := by
      funext v; rw [Finset.sum_insert ha]; ring
    rw [e, levi_add_smul 1 hs (hF a (Finset.mem_insert_self a s)),
      ih fun j hj => hF j (Finset.mem_insert_of_mem hj), Finset.sum_insert ha]
    ring

theorem det_lead_ne (U : Matrix (Fin r) (Fin r) ℂ) (hU : ∀ a c : Fin r, c < a → U a c = 0) (hd : U.det ≠ 0)
    {m : ℕ} (hm : m ≤ r) : (U.submatrix (Fin.castLE hm) (Fin.castLE hm)).det ≠ 0 := by
  have htri : U.BlockTriangular id := fun a c h => hU a c h
  have hdiag : ∀ a, U a a ≠ 0 := by
    intro a ha
    apply hd
    rw [Matrix.det_of_upperTriangular htri]
    exact Finset.prod_eq_zero (Finset.mem_univ a) ha
  have htri2 : (U.submatrix (Fin.castLE hm) (Fin.castLE hm)).BlockTriangular id := by
    intro a c h
    exact hU _ _ (Fin.lt_def.mpr (by simp only [Fin.coe_castLE]; exact Fin.lt_def.mp h))
  rw [Matrix.det_of_upperTriangular htri2]
  exact Finset.prod_ne_zero_iff.mpr fun a _ => hdiag _

section Line

variable (x0 b : Frame X.Ψ r) (z u : V (nd X))

def fk (τ : X.Ψ) (k : Fin (r + 1)) : (Fin 1 → ℂ) → ℝ :=
  fY (Nat.le_of_lt_succ k.isLt) (Dsg X) (Yd X b z u τ)

def cB (τ : X.Ψ) (k : Fin (r + 1)) : ℝ :=
  Real.log (‖((mat b τ)⁻¹.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt))
    (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det‖ ^ 2)

variable {X x0 b z u}

theorem dmin_line_norm (hb : b ∈ Bor X.Ψ r) (hgram : ∀ τ, gram τ.1 X.Gm (mat (rmul (cpt X x0 z) b) τ) =
      diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (v : Fin 1 → ℂ) (τ : X.Ψ) (k : Fin (r + 1)) :
    ‖dmin X.Gm (cpt X x0 (z + (v 0) • u)) τ k‖ =
      ‖((mat b τ)⁻¹.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt))
        (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det‖ ^ 2 * |fk X b z u τ k v| := by
  rw [dmin_line X x0 b hb z u τ (hgram τ) (v 0) k, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
  have hg : (Gz (Nat.le_of_lt_succ k.isLt) (Dsg X) (Yd X b z u τ) (v 0)).det.im = 0 := by
    have h := congrArg Matrix.det (Gz_herm (Nat.le_of_lt_succ k.isLt) (Dsg X) (Yd X b z u τ) (v 0))
    rw [Matrix.det_conjTranspose] at h
    exact Complex.conj_eq_iff_im.1 h
  have hn : ‖(Gz (Nat.le_of_lt_succ k.isLt) (Dsg X) (Yd X b z u τ) (v 0)).det‖ = |fk X b z u τ k v| := by
    unfold fk fY
    exact (Complex.abs_re_eq_norm.2 hg).symm
  rw [hn]
  ring

end Line

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
