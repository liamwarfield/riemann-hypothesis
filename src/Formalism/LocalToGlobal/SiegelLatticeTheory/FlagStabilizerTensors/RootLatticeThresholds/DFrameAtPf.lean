module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RootHaarLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyCut

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DFrameAtPfB
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DFrameAtPfA
noncomputable section

open Matrix Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.DFrameAtPf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.PtRepPf

theorem exists_unitary_of_gram {k : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (α β : M →ₗ[ℂ] (Fin k → ℂ)) (h : ∀ p q, star (α p) ⬝ᵥ α q = star (β p) ⬝ᵥ β q) :
    ∃ ψ ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ p, ψ *ᵥ α p = β p := by
  let T : (Fin k → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin k) := (WithLp.linearEquiv 2 ℂ (Fin k → ℂ)).symm
  have hT : ∀ u v, inner ℂ (T u) (T v) = star u ⬝ᵥ v := by
    intro u v
    rw [dotProduct_comm]
    rfl
  let a : M →ₗ[ℂ] EuclideanSpace ℂ (Fin k) := T.toLinearMap ∘ₗ α
  let b : M →ₗ[ℂ] EuclideanSpace ℂ (Fin k) := T.toLinearMap ∘ₗ β
  have hab : ∀ p q, inner ℂ (a p) (a q) = inner ℂ (b p) (b q) := by
    intro p q
    simp only [a, b, LinearMap.comp_apply, LinearEquiv.coe_coe, hT, h]
  have hker : LinearMap.ker a ≤ LinearMap.ker b := by
    intro p hp
    rw [LinearMap.mem_ker] at hp ⊢
    have h2 := hab p p
    rw [hp, inner_zero_left, eq_comm, inner_self_eq_zero] at h2
    exact h2
  let g : LinearMap.range a →ₗ[ℂ] EuclideanSpace ℂ (Fin k) :=
    (LinearMap.ker a).liftQ b hker ∘ₗ (LinearMap.quotKerEquivRange a).symm.toLinearMap
  have hg : ∀ p, g ⟨a p, LinearMap.mem_range_self a p⟩ = b p := by
    intro p
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hgi : ∀ s t : LinearMap.range a, inner ℂ (g s) (g t) = inner ℂ s t := by
    rintro ⟨_, p, rfl⟩ ⟨_, q, rfl⟩
    rw [hg, hg, Submodule.coe_inner]
    exact (hab p q).symm
  let F := (g.isometryOfInner hgi).extend
  have hF : ∀ p, F (a p) = b p := by
    intro p
    have := LinearIsometry.extend_apply (g.isometryOfInner hgi) ⟨a p, LinearMap.mem_range_self a p⟩
    rw [LinearMap.coe_isometryOfInner, hg] at this
    exact this
  let ψ : Matrix (Fin k) (Fin k) ℂ :=
    LinearMap.toMatrix' (T.symm.toLinearMap ∘ₗ F.toLinearMap ∘ₗ T.toLinearMap)
  have hψ : ∀ u, ψ *ᵥ u = T.symm (F (T u)) := by
    intro u
    simp only [ψ, LinearMap.toMatrix'_mulVec, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearIsometry.coe_toLinearMap]
  have hiso : ∀ u v, star (ψ *ᵥ u) ⬝ᵥ (ψ *ᵥ v) = star u ⬝ᵥ v := by
    intro u v
    rw [← hT, ← hT, hψ, hψ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      LinearIsometry.inner_map_map]
  refine ⟨ψ, ?_, fun p => ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    have := hiso (Pi.single i 1) (Pi.single j 1)
    simp [Matrix.mul_apply, dotProduct, Matrix.one_apply] at this ⊢
    rw [this]
    by_cases hij : i = j
    · subst hij
      simp [Pi.single_apply]
    · simp [Pi.single_apply, hij]
      exact Ne.symm hij
  · rw [hψ]
    have := hF p
    simp only [a, b, LinearMap.comp_apply, LinearEquiv.coe_coe] at this
    rw [this, LinearEquiv.symm_apply_apply]

section Lift

variable {n k : ℕ} (ε : Fin n → Bool)

def liftV (wb : Fin k → Fin n → ℂ) (U : Matrix (Fin k) (Fin k) ℂ) (y : Fin n → ℂ) : Fin n → ℂ :=
  y + ∑ a, ((U - 1) *ᵥ wCoord ε wb y) a • wb a

def liftL (wb : Fin k → Fin n → ℂ) (U : Matrix (Fin k) (Fin k) ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun := liftV ε wb U
  map_add' x y := by
    have hw : wCoord ε wb (x + y) = wCoord ε wb x + wCoord ε wb y := by
      funext i; simp [wCoord, hJ_add_right]
    simp only [liftV, hw, mulVec_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' c x := by
    have hw : wCoord ε wb (c • x) = c • wCoord ε wb x := by
      funext i; simp [wCoord, hJ_smul_right]
    simp only [liftV, hw, mulVec_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add,
      Finset.smul_sum, smul_smul]

def liftM (wb : Fin k → Fin n → ℂ) (U : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix' (liftL ε wb U)

theorem liftM_mulVec (wb : Fin k → Fin n → ℂ) (U : Matrix (Fin k) (Fin k) ℂ) (y : Fin n → ℂ) :
    liftM ε wb U *ᵥ y = y + ∑ a, ((U - 1) *ᵥ wCoord ε wb y) a • wb a := by
  rw [liftM, LinearMap.toMatrix'_mulVec]; rfl

variable {ε}

theorem hJ_wb_sum {wb : Fin k → Fin n → ℂ} (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0)
    (c : Fin k) (p : Fin k → ℂ) : hJ ε (wb c) (∑ a, p a • wb a) = p c := by
  rw [hJ_sum_right]
  simp only [hJ_smul_right, hon, mul_ite, mul_one, mul_zero]
  simp

theorem wCoord_liftM {wb : Fin k → Fin n → ℂ} (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0)
    (U : Matrix (Fin k) (Fin k) ℂ) (y : Fin n → ℂ) :
    wCoord ε wb (liftM ε wb U *ᵥ y) = U *ᵥ wCoord ε wb y := by
  funext c
  show hJ ε (wb c) (liftM ε wb U *ᵥ y) = (U *ᵥ wCoord ε wb y) c
  rw [liftM_mulVec, hJ_add_right, hJ_wb_sum hon, sub_mulVec, one_mulVec, Pi.sub_apply]
  show wCoord ε wb y c + _ = _
  ring

theorem liftM_fix {wb : Fin k → Fin n → ℂ} (U : Matrix (Fin k) (Fin k) ℂ) (y : Fin n → ℂ)
    (hy : ∀ i, hJ ε (wb i) y = 0) : liftM ε wb U *ᵥ y = y := by
  have h0 : wCoord ε wb y = 0 := funext hy
  rw [liftM_mulVec, h0, mulVec_zero]
  simp

private theorem liftM_iso_lemma {wb : Fin k → Fin n → ℂ} (p : Fin k → ℂ) (y : Fin n → ℂ) :
    hJ ε (∑ a, p a • wb a) y = star p ⬝ᵥ wCoord ε wb y := by
  rw [hJ_sum_left]
  simp only [hJ_smul_left, dotProduct, wCoord, Pi.star_apply]

private theorem liftM_iso_lemma_2 {wb : Fin k → Fin n → ℂ} (p : Fin k → ℂ) (x : Fin n → ℂ) :
    hJ ε x (∑ a, p a • wb a) = star (wCoord ε wb x) ⬝ᵥ p := by
  rw [hJ_sum_right]
  simp only [hJ_smul_right, dotProduct, wCoord, Pi.star_apply, hJ_conj]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem liftM_iso_lemma_3 {wb : Fin k → Fin n → ℂ}
    (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0) (q p : Fin k → ℂ) :
    hJ ε (∑ a, q a • wb a) (∑ a, p a • wb a) = star q ⬝ᵥ p := by
  rw [liftM_iso_lemma]
  congr 1
  funext c
  exact hJ_wb_sum hon c p

theorem liftM_iso {wb : Fin k → Fin n → ℂ} (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0)
    (U : Matrix (Fin k) (Fin k) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin k) ℂ) (x y : Fin n → ℂ) :
    hJ ε (liftM ε wb U *ᵥ x) (liftM ε wb U *ᵥ y) = hJ ε x y := by
  have hu : Uᴴ * U = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  have key : (U - 1) + (U - 1)ᴴ + (U - 1)ᴴ * (U - 1) = 0 := by
    simp only [conjTranspose_sub, conjTranspose_one, sub_mul, mul_sub, mul_one, one_mul, hu]
    abel
  rw [liftM_mulVec, liftM_mulVec, hJ_add_left, hJ_add_right, hJ_add_right, liftM_iso_lemma_3 hon,
    liftM_iso_lemma_2, liftM_iso_lemma]
  have e : ∀ a b : Fin k → ℂ, star a ⬝ᵥ ((U - 1) *ᵥ b) + (star ((U - 1) *ᵥ a) ⬝ᵥ b
      + star ((U - 1) *ᵥ a) ⬝ᵥ ((U - 1) *ᵥ b))
      = star a ⬝ᵥ (((U - 1) + (U - 1)ᴴ + (U - 1)ᴴ * (U - 1)) *ᵥ b) := by
    intro a b
    rw [star_mulVec, ← dotProduct_mulVec, ← dotProduct_mulVec, add_mulVec, add_mulVec,
      ← mulVec_mulVec, dotProduct_add, dotProduct_add]
    ring
  rw [add_assoc, e, key, zero_mulVec, dotProduct_zero, add_zero]

def liftU (wb : Fin k → Fin n → ℂ) (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0)
    (U : Matrix (Fin k) (Fin k) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin k) ℂ) : Formalism.REAL.UJ ε :=
  ⟨(Matrix.isUnit_iff_isUnit_det _).2 (by
      have hA := inUJ_of_iso ε _ (liftM_iso hon U hU)
      unfold Formalism.REAL.inUJ at hA
      have h1 := congrArg Matrix.det hA
      rw [det_mul, det_mul] at h1
      have hJ0 : (Formalism.REAL.Jm ε).det ≠ 0 := by
        unfold Formalism.REAL.Jm
        rw [det_diagonal]
        exact Finset.prod_ne_zero_iff.2 fun a _ => by split_ifs <;> norm_num
      refine isUnit_iff_ne_zero.2 fun h0 => hJ0 ?_
      rw [← h1, show (liftM ε wb U).det = 0 from h0, mul_zero])|>.unit, inUJ_of_iso ε _ (liftM_iso hon U hU)⟩

theorem liftU_mulVec (wb : Fin k → Fin n → ℂ) (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0)
    (U : Matrix (Fin k) (Fin k) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin k) ℂ) (y : Fin n → ℂ) :
    uMat (liftU wb hon U hU) *ᵥ y = liftM ε wb U *ᵥ y := rfl

end Lift

end Formalism.L2.SG.Pf.Carrier.DFrameAtPf
end
end

noncomputable section

open Matrix Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.DFrameAtPf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.PtRepPf

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ}

def lamS (r : ℕ) (sc : ℝ) (a : Fin (r + 1)) : ℂ := ((sc : ℂ) ^ (r - a.1))⁻¹

theorem lamS_last (sc : ℝ) : lamS r sc (Fin.last r) = 1 := by
  simp [lamS]

theorem lamS_star (sc : ℝ) (a : Fin (r + 1)) : star (lamS r sc a) = lamS r sc a := by
  simp [lamS, Complex.star_def, Complex.conj_ofReal]

theorem lamS_ne {sc : ℝ} (hsc : sc ≠ 0) (a : Fin (r + 1)) : lamS r sc a ≠ 0 := inv_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hsc))

theorem famSc_eq (sc : ℝ) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    famSc sc e z = fun a => lamS r sc a • fam e z a := rfl

theorem zhat_famSc (sc : ℝ) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (G : Matrix (Fin n) (Fin n) ℂ) :
    Zhat ε (famSc sc e z) (famSc sc e z') G =
      diagonal (lamS r sc) * Zhat ε (fam e z) (fam e z') G * diagonal (lamS r sc) := by
  ext a b
  simp only [Formalism.L2.SG.RealObj.Zhat, Formalism.L2.SG.HidaSetting.hJ, Matrix.diagonal_mul, Matrix.mul_diagonal, famSc_eq,
    Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, lamS_star]
  ring

theorem dl_scale (lam : Fin (r + 1) → ℂ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (l : ℕ) (hl : l ≤ r + 1) :
    Formalism.L2.SG.RealObj.Dl (diagonal lam * Z * diagonal lam) l = (∏ i : Fin l, lam (Fin.castLE hl i)) ^ 2 * Formalism.L2.SG.RealObj.Dl Z l := by
  unfold Formalism.L2.SG.RealObj.Dl
  rw [dite_eq_left hl, dite_eq_left hl]
  have h1 : (diagonal lam * Z * diagonal lam).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      diagonal (fun i => lam (Fin.castLE hl i)) * Z.submatrix (Fin.castLE hl) (Fin.castLE hl) *
        diagonal (fun i => lam (Fin.castLE hl i)) := by
    ext i j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [h1, det_mul, det_mul, det_diagonal]
  ring

theorem gv_scale (T T' : ℝ) (lam : Fin (r + 1) → ℂ) (hL : lam (Fin.last r) = 1)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    Gv T T' (diagonal lam * Z * diagonal lam) = ‖∏ a, lam a‖ ^ 4 * Gv T T' Z := by
  unfold Formalism.L2.SG.RealObj.Gv
  rw [dl_scale lam Z (r + 1) le_rfl, dl_scale lam Z r (Nat.le_succ r)]
  have hP : (∏ i : Fin r, lam (Fin.castLE (Nat.le_succ r) i)) = ∏ a, lam a := by
    rw [Fin.prod_univ_castSucc, hL, mul_one]
    rfl
  have hP2 : (∏ i : Fin (r + 1), lam (Fin.castLE le_rfl i)) = ∏ a, lam a :=
    Fintype.prod_congr _ _ (fun i => rfl)
  rw [hP, hP2]
  simp only [norm_mul, norm_pow]
  ring

theorem gv_pos_scale (T T' : ℝ) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (G : Matrix (Fin n) (Fin n) ℂ)
    (s0 sc : ℝ) (hsc : sc ≠ 0) (h0 : 0 < Gv T T' (Zhat ε (famSc s0 e z) (famSc s0 e z') G)) :
    0 < Gv T T' (Zhat ε (famSc sc e z) (famSc sc e z') G) := by
  rw [zhat_famSc, gv_scale T T' _ (lamS_last sc)]
  rw [zhat_famSc, gv_scale T T' _ (lamS_last s0)] at h0
  have hpos : 0 < Gv T T' (Zhat ε (fam e z) (fam e z') G) := by
    by_contra hc
    push_neg at hc
    have h5 : ‖∏ a, lamS r s0 a‖ ^ 4 * Gv T T' (Zhat ε (fam e z) (fam e z') G) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
    linarith
  have hne : ∏ a, lamS r sc a ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun a _ => lamS_ne hsc a)
  exact mul_pos (pow_pos (norm_pos_iff.mpr hne) 4) hpos

theorem dot_swap (v w : Fin k → ℂ) : star v ⬝ᵥ w = star (star w ⬝ᵥ v) := by
  simp only [dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem dot_self (v : Fin k → ℂ) : star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul', Complex.ofReal_sum, Complex.ofReal_pow]

theorem unit_dot (v : Fin k → ℂ) (hv : v ≠ 0) :
    star (((eN v : ℂ))⁻¹ • v) ⬝ᵥ (((eN v : ℂ))⁻¹ • v) = 1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hs : (0 : ℝ) < ∑ i, ‖v i‖ ^ 2 :=
    lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2)
      (Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i))
  have hpos : 0 < eN v := Real.sqrt_pos.mpr hs
  have hc : ((eN v : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  have hE : ((eN v : ℝ) : ℂ) ^ 2 = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, eN, Real.sq_sqrt hs.le]
  rw [star_smul, smul_dotProduct, dotProduct_smul, dot_self, ← hE]
  simp only [smul_eq_mul, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  field_simp

theorem pairW (F : Fr ε r k) (w y : Fin n → ℂ) (hw : ∀ a, hJ ε (F.e a) w = 0) (hy : ∀ a, hJ ε (F.e a) y = 0) :
    hJ ε w y = -(F.T : ℂ)⁻¹ * hJ ε F.z y * star (hJ ε F.z w) +
      star (wCoord ε F.wb w) ⬝ᵥ wCoord ε F.wb y := by
  rw [F.pair w y hw hy]
  congr 1
  simp only [dotProduct, Pi.star_apply, wCoord]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem sum_gram (v : Fin (r + 1) → Fin n → ℂ) (t : ℂ)
    (hv : ∀ b c, hJ ε (v b) (v c) = if b = Fin.last r ∧ c = Fin.last r then t else 0) (p q : Fin (r + 1) → ℂ) :
    hJ ε (∑ b, p b • v b) (∑ c, q c • v c) = star (p (Fin.last r)) * q (Fin.last r) * t := by
  have hL : ∀ (f : Fin (r + 1) → Fin n → ℂ) (w : Fin n → ℂ), (∑ x, f x) ⬝ᵥ w = ∑ x, f x ⬝ᵥ w := by
    intro f w
    simp only [dotProduct, Finset.sum_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hR : ∀ (u : Fin n → ℂ) (f : Fin (r + 1) → Fin n → ℂ), u ⬝ᵥ (∑ x, f x) = ∑ x, u ⬝ᵥ f x := by
    intro u f
    simp only [dotProduct, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_comm
  have expand : hJ ε (∑ b, p b • v b) (∑ c, q c • v c) = ∑ b, ∑ c, star (p b) * q c * hJ ε (v b) (v c) := by
    simp only [Formalism.L2.SG.HidaSetting.hJ, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul]
    rw [hL]
    simp only [hR, smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => by ring))
  rw [expand]
  simp only [hv, mul_ite, mul_zero]
  rw [Fintype.sum_eq_single (Fin.last r) (fun b hb => by simp [hb])]
  rw [Fintype.sum_eq_single (Fin.last r) (fun c hc => by simp [hc])]
  simp

theorem dframe_loc (A B : Fr ε r k) (he : B.e = A.e) (i0 : Fin k) (g : Formalism.REAL.UJ ε) (sc : ℝ) (hsc : sc ≠ 0)
    (hG : 0 < Gv A.T B.T (Zhat ε (famSc sc A.e A.z) (famSc sc A.e B.z) (uMat g))) :
    ∃ h h' : Matrix (Fin k) (Fin k) ℂ,
      IsDFrame ε (famSc sc A.e A.z) (famSc sc A.e B.z) (uMat g) (uMat g⁻¹) A.wb B.wb i0 i0 h h' := by
  classical
  obtain ⟨hZu, -⟩ := gv_facts A.T_pos B.T_pos _ hG
  set f := famSc sc A.e A.z with hfdef
  set f' := famSc sc A.e B.z with hf'def
  set Gm := uMat g with hGm
  set Gi := uMat g⁻¹ with hGi
  set Zs := Zhat ε f f' Gm with hZs
  have hD : Zs.det ≠ 0 := isUnit_iff_ne_zero.1 hZu
  have hDl : Formalism.L2.SG.RealObj.Dl Zs (r + 1) = Zs.det := dl_top Zs
  have hDr : Formalism.L2.SG.RealObj.Dl Zs r = adjugate Zs (Fin.last r) (Fin.last r) := dl_r Zs

  have hfa : ∀ a : Fin r, f (Fin.castSucc a) = lamS r sc (Fin.castSucc a) • A.e a := fun a => by
    rw [hfdef, famSc_eq]
    show lamS r sc (Fin.castSucc a) • fam A.e A.z (Fin.castSucc a) = _
    rw [fam_cs]
  have hfL : f (Fin.last r) = A.z := by rw [hfdef, famSc_eq]; simp only [lamS_last, fam_last, one_smul]
  have hfB : f' = fun a => lamS r sc a • fam B.e B.z a := by rw [hf'def, famSc_eq, he]
  have hf'a : ∀ a : Fin r, f' (Fin.castSucc a) = lamS r sc (Fin.castSucc a) • B.e a := fun a => by
    rw [hfB]
    show lamS r sc (Fin.castSucc a) • fam B.e B.z (Fin.castSucc a) = _
    rw [fam_cs]
  have hf'L : f' (Fin.last r) = B.z := by rw [hfB]; simp only [lamS_last, fam_last, one_smul]
  have hgf : ∀ b c, hJ ε (f b) (f c) = if b = Fin.last r ∧ c = Fin.last r then -(A.T : ℂ) else 0 := by
    intro b c
    rw [hfdef, famSc_eq]
    simp only
    rw [hJ_smul_left, hJ_smul_right, lamS_star, A.gf]
    split_ifs with h
    · rw [h.1, h.2, lamS_last]; ring
    · ring
  have hgf' : ∀ b c, hJ ε (Gm *ᵥ f' b) (Gm *ᵥ f' c) =
      if b = Fin.last r ∧ c = Fin.last r then -(B.T : ℂ) else 0 := by
    intro b c
    rw [hGm, hJ_UJ, hfB]
    simp only
    rw [hJ_smul_left, hJ_smul_right, lamS_star, B.gf]
    split_ifs with h
    · rw [h.1, h.2, lamS_last]; ring
    · ring
  have hGG : ∀ q, Gm *ᵥ (Gi *ᵥ q) = q := fun q => by rw [mulVec_mulVec, hGm, hGi, uMat_mul_inv, one_mulVec]
  have hpv : ∀ p q, hJ ε p (Gi *ᵥ q) = hJ ε (Gm *ᵥ p) q := fun p q => by
    rw [← hJ_UJ ε g p (Gi *ᵥ q), ← hGm, hGG]
  have hGi2 : ∀ p q, hJ ε (Gi *ᵥ p) (Gi *ᵥ q) = hJ ε p q := fun p q => hJ_UJ ε g⁻¹ p q
  have heA : ∀ y, hJ ε (f (Fin.last r)) y = 0 ∨ True → (∀ a, hJ ε (f a) y = if a = Fin.last r then hJ ε A.z y else 0) →
      ∀ a, hJ ε (A.e a) y = 0 := fun y _ hy a => by
    have h := hy (Fin.castSucc a)
    rw [hfa, hJ_smul_left, lamS_star, if_neg (Fin.castSucc_ne_last a)] at h
    exact (mul_eq_zero.1 h).resolve_left (lamS_ne hsc _)
  have heB : ∀ y, (∀ b, hJ ε (f' b) y = if b = Fin.last r then hJ ε B.z y else 0) → ∀ a, hJ ε (B.e a) y = 0 :=
    fun y hy a => by
      have h := hy (Fin.castSucc a)
      rw [hf'a, hJ_smul_left, lamS_star, if_neg (Fin.castSucc_ne_last a)] at h
      exact (mul_eq_zero.1 h).resolve_left (lamS_ne hsc _)

  set x' := xPr Zs Gm f' with hx'
  have hfx' : ∀ a, hJ ε (f a) x' = if a = Fin.last r then Zs.det else 0 := by
    intro a
    rw [hx', xPr, hJ_sum_right]
    simp only [hJ_smul_right]
    have h := congrFun (congrFun (mul_adjugate Zs) a) (Fin.last r)
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
    have h2 : ∑ b, adjugate Zs b (Fin.last r) * hJ ε (f a) (Gm *ᵥ f' b) =
        ∑ b, Zs a b * adjugate Zs b (Fin.last r) := Finset.sum_congr rfl fun b _ => mul_comm _ _
    rw [h2, h]
    split_ifs <;> simp
  have hzx' : hJ ε A.z x' = Zs.det := by have h := hfx' (Fin.last r); rwa [hfL, if_pos rfl] at h
  have hex' : ∀ a, hJ ε (A.e a) x' = 0 := heA x' (Or.inr trivial) fun a => by
    rw [hfx', hzx']
  have hx'x' : hJ ε x' x' = star (adjugate Zs (Fin.last r) (Fin.last r)) *
      adjugate Zs (Fin.last r) (Fin.last r) * (-(B.T : ℂ)) := by
    rw [hx']; unfold xPr
    exact sum_gram (fun b => Gm *ᵥ f' b) _ hgf' _ _

  set x := xUn Zs f with hx
  have hxf : ∀ b, hJ ε x (Gm *ᵥ f' b) = if b = Fin.last r then Zs.det else 0 := by
    intro b
    rw [hx, xUn, hJ_sum_left]
    simp only [hJ_smul_left, star_star]
    have h := congrFun (congrFun (adjugate_mul Zs) (Fin.last r)) b
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
    rw [show ∑ a, adjugate Zs (Fin.last r) a * hJ ε (f a) (Gm *ᵥ f' b) =
      ∑ a, adjugate Zs (Fin.last r) a * Zs a b from rfl, h]
    by_cases hb : b = Fin.last r
    · subst hb; simp
    · rw [if_neg hb, if_neg (Ne.symm hb), mul_zero]
  have hf'x : ∀ b, hJ ε (f' b) (Gi *ᵥ x) = if b = Fin.last r then star Zs.det else 0 := by
    intro b
    rw [hpv, ← hJ_conj, hxf]
    split_ifs <;> simp
  have hzx : hJ ε B.z (Gi *ᵥ x) = star Zs.det := by have h := hf'x (Fin.last r); rwa [hf'L, if_pos rfl] at h
  have hex : ∀ a, hJ ε (B.e a) (Gi *ᵥ x) = 0 := heB _ fun b => by rw [hf'x, hzx]
  have hxx : hJ ε (Gi *ᵥ x) (Gi *ᵥ x) = star (star (adjugate Zs (Fin.last r) (Fin.last r))) *
      star (adjugate Zs (Fin.last r) (Fin.last r)) * (-(A.T : ℂ)) := by
    rw [hGi2, hx]; unfold xUn
    exact sum_gram f _ hgf _ _

  have hGv : Gv A.T B.T Zs = ‖Zs.det‖ ^ 2 - A.T * B.T * ‖adjugate Zs (Fin.last r) (Fin.last r)‖ ^ 2 := by
    unfold Gv; rw [hDl, hDr]
  have hTA : (A.T : ℂ) ≠ 0 := by exact_mod_cast A.T_pos.ne'
  have hTB : (B.T : ℂ) ≠ 0 := by exact_mod_cast B.T_pos.ne'
  have hw1 : wCoord ε A.wb x' ≠ 0 := by
    intro h0
    have h := pairW A x' x' hex' hex'
    rw [h0, dotProduct_zero, add_zero, hzx', hx'x'] at h
    have hn1 : star Zs.det * Zs.det = (‖Zs.det‖ : ℂ) ^ 2 := by rw [norm_sq_star]; push_cast; ring
    have hn2 : star (adjugate Zs (Fin.last r) (Fin.last r)) * adjugate Zs (Fin.last r) (Fin.last r) =
        (‖adjugate Zs (Fin.last r) (Fin.last r)‖ : ℂ) ^ 2 := by rw [norm_sq_star]; push_cast; ring
    have hTi : (A.T : ℂ) * (A.T : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hTA
    have h3 : ((Gv A.T B.T Zs : ℝ) : ℂ) = 0 := by
      rw [hGv]; push_cast
      linear_combination (-1 : ℂ) * hn1 + ((A.T : ℂ) * B.T) * hn2 + (A.T : ℂ) * h +
        (-(Zs.det * star Zs.det)) * hTi
    have : Gv A.T B.T Zs = 0 := by exact_mod_cast h3
    linarith
  have hw2 : wCoord ε B.wb (Gi *ᵥ x) ≠ 0 := by
    intro h0
    have h := pairW B _ _ hex hex
    rw [h0, dotProduct_zero, add_zero, hzx, hxx] at h
    simp only [star_star] at h
    have hn1 : star Zs.det * Zs.det = (‖Zs.det‖ : ℂ) ^ 2 := by rw [norm_sq_star]; push_cast; ring
    have hn2 : adjugate Zs (Fin.last r) (Fin.last r) * star (adjugate Zs (Fin.last r) (Fin.last r)) =
        (‖adjugate Zs (Fin.last r) (Fin.last r)‖ : ℂ) ^ 2 := by rw [mul_comm, norm_sq_star]; push_cast; ring
    have hTi : (B.T : ℂ) * (B.T : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hTB
    have h3 : ((Gv A.T B.T Zs : ℝ) : ℂ) = 0 := by
      rw [hGv]; push_cast
      linear_combination (-1 : ℂ) * hn1 + ((A.T : ℂ) * B.T) * hn2 + (B.T : ℂ) * h +
        (-(star Zs.det * Zs.det)) * hTi
    have : Gv A.T B.T Zs = 0 := by exact_mod_cast h3
    linarith
  set nn := (Formalism.L2.SG.RealObj.Dl Zs (r + 1))⁻¹ • wCoord ε A.wb x' with hnn
  set nn' := (star (Formalism.L2.SG.RealObj.Dl Zs (r + 1)))⁻¹ • wCoord ε B.wb (Gi *ᵥ x) with hnn'
  have hnn0 : nn ≠ 0 := smul_ne_zero (inv_ne_zero (by rw [hDl]; exact hD)) hw1
  have hnn0' : nn' ≠ 0 := smul_ne_zero (inv_ne_zero (by rw [hDl, star_ne_zero]; exact hD)) hw2
  set u := ((eN nn : ℂ))⁻¹ • nn with hu
  set u' := ((eN nn' : ℂ))⁻¹ • nn' with hu'
  have huu : star u ⬝ᵥ u = 1 := unit_dot nn hnn0
  have huu' : star u' ⬝ᵥ u' = 1 := unit_dot nn' hnn0'

  let cf : (Fin n → ℂ) →ₗ[ℂ] (Fin (r + 1) → ℂ) × (Fin (r + 1) → ℂ) :=
    LinearMap.prod (LinearMap.pi fun a => formB ε (f a)) (LinearMap.pi fun b => formB ε (Gm *ᵥ f' b))
  let U0 := LinearMap.ker cf
  have hU0 : ∀ y ∈ U0, (∀ a, hJ ε (f a) y = 0) ∧ ∀ b, hJ ε (Gm *ᵥ f' b) y = 0 := fun y hy => by
    rw [LinearMap.mem_ker] at hy
    exact ⟨fun a => congrFun (congrArg Prod.fst hy) a, fun b => congrFun (congrArg Prod.snd hy) b⟩
  have hU0' : ∀ y, (∀ a, hJ ε (f a) y = 0) → (∀ b, hJ ε (Gm *ᵥ f' b) y = 0) → y ∈ U0 := fun y ha hb =>
    LinearMap.mem_ker.2 (Prod.ext (funext ha) (funext hb))
  have hAy : ∀ y ∈ U0, (∀ a, hJ ε (A.e a) y = 0) ∧ hJ ε A.z y = 0 := fun y hy => by
    obtain ⟨ha, -⟩ := hU0 y hy
    refine ⟨heA y (Or.inr trivial) fun a => ?_, by rw [← hfL]; exact ha _⟩
    rw [ha a]; split_ifs with h
    · rw [← hfL, ← h]; exact (ha a).symm
    · rfl
  have hBy : ∀ y ∈ U0, (∀ a, hJ ε (B.e a) (Gi *ᵥ y) = 0) ∧ hJ ε B.z (Gi *ᵥ y) = 0 := fun y hy => by
    obtain ⟨-, hb⟩ := hU0 y hy
    have h0 : ∀ b, hJ ε (f' b) (Gi *ᵥ y) = 0 := fun b => by rw [hpv]; exact hb b
    refine ⟨heB _ fun b => ?_, by rw [← hf'L]; exact h0 _⟩
    rw [h0 b]; split_ifs with h
    · rw [← hf'L, ← h]; exact (h0 b).symm
    · rfl
  have hG1 : ∀ y1 ∈ U0, ∀ y2 ∈ U0, star (wCoord ε B.wb (Gi *ᵥ y1)) ⬝ᵥ wCoord ε B.wb (Gi *ᵥ y2) =
      star (wCoord ε A.wb y1) ⬝ᵥ wCoord ε A.wb y2 := fun y1 h1 y2 h2 => by
    have hA := pairW A y1 y2 (hAy y1 h1).1 (hAy y2 h2).1
    have hB := pairW B _ _ (hBy y1 h1).1 (hBy y2 h2).1
    rw [(hAy y2 h2).2, mul_zero, zero_mul, zero_add] at hA
    rw [(hBy y2 h2).2, mul_zero, zero_mul, zero_add, hGi2] at hB
    rw [← hA, ← hB]
  have hG2 : ∀ y ∈ U0, star (wCoord ε A.wb y) ⬝ᵥ u = 0 := fun y hy => by
    have hxy : hJ ε x' y = 0 := by
      rw [hx', xPr, hJ_sum_left]
      exact Finset.sum_eq_zero fun b _ => by rw [hJ_smul_left, (hU0 y hy).2 b, mul_zero]
    have h := pairW A y x' (hAy y hy).1 hex'
    rw [(hAy y hy).2, star_zero, mul_zero, zero_add, ← hJ_conj, hxy, star_zero] at h
    rw [hu, hnn, dotProduct_smul, dotProduct_smul, ← h, smul_zero, smul_zero]
  have hG3 : ∀ y ∈ U0, star (wCoord ε B.wb (Gi *ᵥ y)) ⬝ᵥ u' = 0 := fun y hy => by
    have hxy : hJ ε x y = 0 := by
      rw [hx, xUn, hJ_sum_left]
      exact Finset.sum_eq_zero fun a _ => by rw [hJ_smul_left, (hU0 y hy).1 a, mul_zero]
    have h := pairW B (Gi *ᵥ y) (Gi *ᵥ x) (hBy y hy).1 hex
    rw [(hBy y hy).2, star_zero, mul_zero, zero_add, hGi2, ← hJ_conj, hxy, star_zero] at h
    rw [hu', hnn', dotProduct_smul, dotProduct_smul, ← h, smul_zero, smul_zero]
  have key : ∀ (a b t : Fin k → ℂ) (c1 c2 : ℂ), star a ⬝ᵥ t = 0 → star t ⬝ᵥ b = 0 → star t ⬝ᵥ t = 1 →
      star (a + c1 • t) ⬝ᵥ (b + c2 • t) = star a ⬝ᵥ b + star c1 * c2 := by
    intro a b t c1 c2 h1 h2 h3
    simp only [star_add, star_smul, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, h1, h2, h3,
      smul_eq_mul, mul_zero, add_zero, zero_add, mul_one]
    ring

  let wcL : (Fin k → Fin n → ℂ) → (Fin n → ℂ) →ₗ[ℂ] (Fin k → ℂ) := fun wb => LinearMap.pi fun i => formB ε (wb i)
  let α : U0 × ℂ →ₗ[ℂ] (Fin k → ℂ) :=
    LinearMap.coprod (wcL B.wb ∘ₗ Matrix.mulVecLin Gi ∘ₗ U0.subtype) (LinearMap.toSpanSingleton ℂ _ u')
  let β : U0 × ℂ →ₗ[ℂ] (Fin k → ℂ) :=
    LinearMap.coprod (wcL A.wb ∘ₗ U0.subtype) (LinearMap.toSpanSingleton ℂ _ u)
  have hα : ∀ (y : U0) (c : ℂ), α (y, c) = wCoord ε B.wb (Gi *ᵥ (y : Fin n → ℂ)) + c • u' := fun _ _ => rfl
  have hβ : ∀ (y : U0) (c : ℂ), β (y, c) = wCoord ε A.wb (y : Fin n → ℂ) + c • u := fun _ _ => rfl
  obtain ⟨ψ, hψU, hψ⟩ := exists_unitary_of_gram α β (by
    rintro ⟨y1, c1⟩ ⟨y2, c2⟩
    rw [hα, hα, hβ, hβ,
      key _ _ _ _ _ (hG3 y1 y1.2) (by rw [dot_swap, hG3 y2 y2.2, star_zero]) huu',
      key _ _ _ _ _ (hG2 y1 y1.2) (by rw [dot_swap, hG2 y2 y2.2, star_zero]) huu,
      hG1 y1 y1.2 y2 y2.2])
  have hψu : ψ *ᵥ u' = u := by
    have h := hψ (0, 1)
    have hwc0 : ∀ wb : Fin k → Fin n → ℂ, wCoord ε wb 0 = 0 := fun wb => funext fun i => hJ_zero_right ε _
    rw [hα, hβ] at h
    simpa [hwc0] using h
  have hψy : ∀ y ∈ U0, ψ *ᵥ wCoord ε B.wb (Gi *ᵥ y) = wCoord ε A.wb y := fun y hy => by
    have h := hψ (⟨y, hy⟩, 0)
    rw [hα, hβ, zero_smul, zero_smul, add_zero, add_zero] at h
    exact h

  obtain ⟨h, hhU, hh⟩ := exists_unitary_of_gram (LinearMap.toSpanSingleton ℂ _ (Pi.single i0 (1 : ℂ)))
    (LinearMap.toSpanSingleton ℂ _ u) (by
      intro c1 c2
      simp only [LinearMap.toSpanSingleton_apply, star_smul, smul_dotProduct, dotProduct_smul, huu]
      rw [dotProduct_single, Pi.star_apply, Pi.single_eq_same, star_one, mul_one])
  have hh1 : h *ᵥ Pi.single i0 1 = u := by simpa using hh 1
  have hψψ : star ψ * ψ = 1 := (Matrix.mem_unitaryGroup_iff').1 hψU
  have hhh : h * star h = 1 := (Matrix.mem_unitaryGroup_iff).1 hhU
  unfold IsDFrame
  refine ⟨h, star ψ * h, hhU, Submonoid.mul_mem _ (Unitary.star_mem hψU) hhU, hh1, ?_, ?_⟩
  · rw [← mulVec_mulVec, hh1, ← hψu, mulVec_mulVec, hψψ, one_mulVec]
  · intro y ha hb
    rw [star_mul, star_star, mulVec_mulVec, ← mul_assoc, hhh, one_mul]
    exact hψy y (hU0' y ha hb)

end Formalism.L2.SG.Pf.Carrier.DFrameAtPf
end
end

noncomputable section

open NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut.PtRepPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace DFrameAtPf

theorem matW_liftU {n k : ℕ} {ε : Fin n → Bool} (wb : Fin k → Fin n → ℂ)
    (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0)
    (U : Matrix (Fin k) (Fin k) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    (Matrix.of fun a b => hJ ε (wb a) (uMat (liftU wb hon U hU) *ᵥ wb b)) = U := by
  ext a b
  rw [Matrix.of_apply, liftU_mulVec]
  have h1 := congrFun (wCoord_liftM hon U (wb b)) a
  have h2 : wCoord ε wb (wb b) = Pi.single b 1 := by
    funext i
    show hJ ε (wb i) (wb b) = _
    rw [hon, Pi.single_apply]
  rw [h2, mulVec_single_one] at h1
  exact h1

end DFrameAtPf

open DFrameAtPf

variable {D : D7}

theorem dFrame_any (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (s0 sc : ℝ) (hsc : sc ≠ 0)
    (i0 : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (γ : X.B.I.Ginf) (hG : ∀ v, 0 < GX X u u' s0 γ v) :
    ∃ h h', IsDFrameX X u u' sc i0 i0 γ h h' := by
  have hloc : ∀ v, ∃ h h' : Matrix (Fin D.R.k) (Fin D.R.k) ℂ,
      IsDFrame (X.B.I.ε v) (frm X u sc v) (frm X u' sc v) (uMat (γ v)) (uMat ((γ v)⁻¹)) (X.wfr u v)
        (X.wfr u' v) (i0 v) (i0 v) h h' := fun v =>
    dframe_loc (frU X u v) (frU X u' v) rfl (i0 v) (γ v) sc hsc
      (gv_pos_scale (Tw u) (Tw u') (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u'))
        (uMat (γ v)) s0 sc hsc (hG v))
  choose H H' hH using hloc
  have hon : ∀ uu v, ∀ i j, hJ (X.B.I.ε v) (X.wfr uu v i) (X.wfr uu v j) = if i = j then 1 else 0 :=
    fun uu v => X.wfr_on uu v
  have hmem : ∀ uu (U : ∀ v, Matrix (Fin D.R.k) (Fin D.R.k) ℂ) (hU : ∀ v, U v ∈ Matrix.unitaryGroup _ ℂ),
      (fun v => liftU (X.wfr uu v) (hon uu v) (U v) (hU v) : X.B.I.Ginf) ∈ HsetU X uu := by
    intro uu U hU v x hx
    show uMat (liftU (X.wfr uu v) (hon uu v) (U v) (hU v)) *ᵥ rv X.B.I v x = rv X.B.I v x
    rw [liftU_mulVec]
    refine liftM_fix _ _ fun i => ?_
    rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hx
    · exact (frU X uu v).we i a
    · exact (frU X uu v).wf i a
    · rw [Set.mem_singleton_iff] at hx; subst hx; exact (frU X uu v).wz i
  have hmat : ∀ uu (U : ∀ v, Matrix (Fin D.R.k) (Fin D.R.k) ℂ) (hU : ∀ v, U v ∈ Matrix.unitaryGroup _ ℂ) v,
      Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr uu v) v (fun v => liftU (X.wfr uu v) (hon uu v) (U v) (hU v)) = U v :=
    fun uu U hU v => matW_liftU (X.wfr uu v) (hon uu v) (U v) (hU v)
  refine ⟨fun v => liftU (X.wfr u v) (hon u v) (H v) (hH v).1,
    fun v => liftU (X.wfr u' v) (hon u' v) (H' v) (hH v).2.1,
    hmem u H (fun v => (hH v).1), hmem u' H' (fun v => (hH v).2.1), fun v => ?_⟩
  rw [hmat u H (fun v => (hH v).1) v, hmat u' H' (fun v => (hH v).2.1) v]
  exact hH v

theorem dual_frame_at_places (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ)
    (i0 : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) : DFrameAt X u u' sc i0 i0 := by
  intro hsc w _ hG
  exact dFrame_any X u u' D.host.rdE sc hsc.ne' i0 (gamW X u u' w) hG

end Formalism.L2.SG.Pf.Carrier
