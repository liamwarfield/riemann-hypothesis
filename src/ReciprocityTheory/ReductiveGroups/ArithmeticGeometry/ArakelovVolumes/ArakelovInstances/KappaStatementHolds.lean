module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.QuotientIsHausdorff

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.HasFDerivAtNmat
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.DetOfBlockDiag
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem det_of_blockDiag {m α : Type} [Fintype m] [DecidableEq m] [LinearOrder α] (M : Matrix m m ℂ)
    (bk : m → α) (hM : M.BlockTriangular bk) (dg : m → ℂ)
    (hd : ∀ i j, bk i = bk j → M i j = if i = j then dg i else 0) : M.det = ∏ i, dg i := by
  classical
  rw [hM.det]
  have hb : ∀ k, M.toSquareBlock bk k = Matrix.diagonal (fun i : {i // bk i = k} => dg i) := by
    intro k
    ext i j
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply]
    rw [hd i j (i.2.trans j.2.symm), Matrix.diagonal_apply]
    simp [Subtype.ext_iff]
  simp only [hb, Matrix.det_diagonal]
  rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image bk) (g := bk)
    (fun x _ => Finset.mem_image_of_mem bk (Finset.mem_univ x)) dg]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← Finset.prod_subtype (Finset.univ.filter fun i => bk i = k) (p := fun i => bk i = k)
    (fun i => by simp)]

theorem ent_eq_iff (e e' : Ent X) :
    e = e' ↔ e.1 = e'.1 ∧ e.2.1.1 = e'.2.1.1 ∧ e.2.1.2 = e'.2.1.2 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨τ, ⟨⟨a, c⟩, h⟩⟩ := e
    obtain ⟨τ', ⟨⟨a', c'⟩, h'⟩⟩ := e'
    rintro ⟨h1, h2, h3⟩
    simp only at h1 h2 h3
    subst h1 h2 h3
    rfl

def embF (v : Ent X → ℂ) (τ : X.Ψ) (x c : Fin r) : ℂ := if h : c < x then v ⟨τ, ⟨(x, c), h⟩⟩ else 0

theorem embF_single (e' : Ent X) (τ : X.Ψ) (x c : Fin r) :
    embF X (Pi.single e' 1) τ x c = if τ = e'.1 ∧ x = e'.2.1.1 ∧ c = e'.2.1.2 then 1 else 0 := by
  unfold embF
  by_cases h1 : c < x
  · rw [dite_eq_left h1, Pi.single_apply]
    by_cases h2 : τ = e'.1 ∧ x = e'.2.1.1 ∧ c = e'.2.1.2
    · rw [if_pos h2, if_pos ((ent_eq_iff X _ _).2 h2)]
    · rw [if_neg h2, if_neg (fun h => h2 ((ent_eq_iff X _ _).1 h))]
  · rw [dite_eq_right h1, if_neg]
    rintro ⟨rfl, rfl, rfl⟩
    exact h1 e'.2.2

def lmulL (N : Frame X.Ψ r) : (Ent X → ℂ) →ₗ[ℂ] (Ent X → ℂ) where
  toFun v e := ∑ x, N e.1 e.2.1.1 x * embF X v e.1 x e.2.1.2
  map_add' v w := by
    funext e
    simp only [Pi.add_apply, embF]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> ring
  map_smul' a v := by
    funext e
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, embF, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> ring

def rmulL (b : Frame X.Ψ r) : (Ent X → ℂ) →ₗ[ℂ] (Ent X → ℂ) where
  toFun v e := ∑ y, embF X v e.1 e.2.1.1 y * b e.1 y e.2.1.2
  map_add' v w := by
    funext e
    simp only [Pi.add_apply, embF]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> ring
  map_smul' a v := by
    funext e
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, embF, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> ring

theorem lmulL_entry (N : Frame X.Ψ r) (e e' : Ent X) :
    LinearMap.toMatrix (Pi.basisFun ℂ (Ent X)) (Pi.basisFun ℂ (Ent X)) (lmulL X N) e e' =
      if e.1 = e'.1 ∧ e.2.1.2 = e'.2.1.2 then N e.1 e.2.1.1 e'.2.1.1 else 0 := by
  classical
  rw [LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr]
  show ∑ x, N e.1 e.2.1.1 x * embF X (Pi.single e' 1) e.1 x e.2.1.2 = _
  simp only [embF_single, mul_ite, mul_one, mul_zero]
  split_ifs with h
  · rw [Finset.sum_eq_single e'.2.1.1]
    · rw [if_pos ⟨h.1, rfl, h.2⟩]
    · intro x _ hx
      rw [if_neg]
      exact fun h' => hx h'.2.1
    · simp
  · refine Finset.sum_eq_zero fun x _ => ?_
    rw [if_neg]
    exact fun h' => h ⟨h'.1, h'.2.2⟩

theorem rmulL_entry (b : Frame X.Ψ r) (e e' : Ent X) :
    LinearMap.toMatrix (Pi.basisFun ℂ (Ent X)) (Pi.basisFun ℂ (Ent X)) (rmulL X b) e e' =
      if e.1 = e'.1 ∧ e.2.1.1 = e'.2.1.1 then b e.1 e'.2.1.2 e.2.1.2 else 0 := by
  classical
  rw [LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr]
  show ∑ y, embF X (Pi.single e' 1) e.1 e.2.1.1 y * b e.1 y e.2.1.2 = _
  simp only [embF_single, ite_mul, one_mul, zero_mul]
  split_ifs with h
  · rw [Finset.sum_eq_single e'.2.1.2]
    · rw [if_pos ⟨h.1, h.2, rfl⟩]
    · intro y _ hy
      rw [if_neg]
      exact fun h' => hy h'.2.2
    · simp
  · refine Finset.sum_eq_zero fun y _ => ?_
    rw [if_neg]
    exact fun h' => h ⟨h'.1, h'.2.1⟩

theorem det_lmulL_unit (N : Frame X.Ψ r) (hlow : ∀ τ a x, a < x → N τ a x = 0) (hdiag : ∀ τ a, N τ a a = 1) :
    LinearMap.det (lmulL X N) = 1 := by
  classical
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Ent X))]
  rw [det_of_blockDiag _ (fun e : Ent X => OrderDual.toDual e.2.1.1) (fun e e' hlt => by
      rw [lmulL_entry]
      split_ifs with h
      · exact hlow _ _ _ (by simpa using hlt)
      · rfl) (fun _ => 1) (fun e e' hk => by
      rw [lmulL_entry]
      have hk' : e.2.1.1 = e'.2.1.1 := by simpa using hk
      by_cases h : e = e'
      · subst h; simp [hdiag]
      · rw [if_neg h, if_neg]
        intro h2
        exact h ((ent_eq_iff X e e').2 ⟨h2.1, hk', h2.2⟩))]
  simp

theorem det_lmulL_upper (b : Frame X.Ψ r) (hup : ∀ τ a x, x < a → b τ a x = 0) :
    LinearMap.det (lmulL X b) = ∏ e : Ent X, b e.1 e.2.1.1 e.2.1.1 := by
  classical
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Ent X))]
  exact det_of_blockDiag _ (fun e : Ent X => e.2.1.1) (fun e e' hlt => by
      rw [lmulL_entry]
      split_ifs with h
      · exact hup _ _ _ hlt
      · rfl) _ (fun e e' hk => by
      rw [lmulL_entry]
      by_cases h : e = e'
      · subst h; simp
      · rw [if_neg h, if_neg]
        intro h2
        exact h ((ent_eq_iff X e e').2 ⟨h2.1, hk, h2.2⟩))

theorem det_rmulL_upper (b : Frame X.Ψ r) (hup : ∀ τ a x, x < a → b τ a x = 0) :
    LinearMap.det (rmulL X b) = ∏ e : Ent X, b e.1 e.2.1.2 e.2.1.2 := by
  classical
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Ent X))]
  exact det_of_blockDiag _ (fun e : Ent X => OrderDual.toDual e.2.1.2) (fun e e' hlt => by
      rw [rmulL_entry]
      split_ifs with h
      · exact hup _ _ _ (by simpa using hlt)
      · rfl) _ (fun e e' hk => by
      rw [rmulL_entry]
      have hk' : e.2.1.2 = e'.2.1.2 := by simpa using hk
      by_cases h : e = e'
      · subst h; simp
      · rw [if_neg h, if_neg]
        intro h2
        exact h ((ent_eq_iff X e e').2 ⟨h2.1, h2.2, hk'⟩))

theorem prod_low_row (g : Fin r → ℂ) :
    ∏ p : {p : Fin r × Fin r // p.2 < p.1}, g p.1.1 = ∏ a, g a ^ (a : ℕ) := by
  rw [← Finset.prod_subtype (Finset.univ.filter fun p : Fin r × Fin r => p.2 < p.1) (fun p => by simp)
    (fun p : Fin r × Fin r => g p.1), Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_filter]
  dsimp only
  rw [Finset.prod_const]
  congr 1
  rw [← Fin.card_Iio a]
  congr 1
  ext c
  simp

theorem prod_low_col (g : Fin r → ℂ) :
    ∏ p : {p : Fin r × Fin r // p.2 < p.1}, g p.1.2 = ∏ c, g c ^ (r - 1 - (c : ℕ)) := by
  rw [← Finset.prod_subtype (Finset.univ.filter fun p : Fin r × Fin r => p.2 < p.1) (fun p => by simp)
    (fun p : Fin r × Fin r => g p.2), Finset.prod_filter, Fintype.prod_prod_type, Finset.prod_comm]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [← Finset.prod_filter]
  dsimp only
  rw [Finset.prod_const]
  congr 1
  rw [← Fin.card_Ioi c]
  congr 1
  ext a
  simp

theorem bchar_kap (b : Frame X.Ψ r) (hd : ∀ τ a, b τ a a ≠ 0) :
    bchar (kapW X) b = (∏ e : Ent X, b e.1 e.2.1.1 e.2.1.1) / ∏ e : Ent X, b e.1 e.2.1.2 e.2.1.2 := by
  rw [Fintype.prod_prod_type, Fintype.prod_prod_type, ← Finset.prod_div_distrib]
  unfold bchar
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [prod_low_row (fun a => b τ a a), prod_low_col (fun c => b τ c c), ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  have ha : (a : ℕ) ≤ r - 1 := by omega
  rw [kapW, show (2 * ((a : ℕ) : ℤ) - ((r : ℤ) - 1)) = ((a : ℕ) : ℤ) - ((r - 1 - (a : ℕ) : ℕ) : ℤ) by
    push_cast [Nat.sub_sub, Nat.cast_sub (by omega : 1 + (a : ℕ) ≤ r)]; ring,
    zpow_sub₀ (hd τ a), zpow_natCast, zpow_natCast]

end ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
end
end

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates Matrix Topology Filter
open scoped Classical

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def vecOf (z : V (nd X)) : Ent X → ℂ := fun e => z (Fintype.equivFin (Ent X) e)

def Lin (τ : X.Ψ) : V (nd X) →ₗ[ℂ] Matrix (Fin r) (Fin r) ℂ where
  toFun z := Matrix.of (embF X (vecOf X z) τ)
  map_add' z w := by
    ext a c
    simp only [Matrix.of_apply, Matrix.add_apply, embF, vecOf]
    split_ifs
    · rfl
    · simp
  map_smul' t z := by
    ext a c
    simp only [Matrix.of_apply, Matrix.smul_apply, embF, vecOf, smul_eq_mul, RingHom.id_apply]
    split_ifs
    · rfl
    · simp

theorem nmat_eq (z : V (nd X)) (τ : X.Ψ) : mat (nmat X z) τ = 1 + Lin X τ z := by
  ext a c
  simp only [mat, nmat, Lin, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Matrix.add_apply,
    Matrix.one_apply, embF, vecOf]
  split_ifs with h1 h2 <;> first
    | (subst h2; exact absurd h1 (lt_irrefl _))
    | simp_all
    | omega

theorem hasFDerivAt_nmat (τ : X.Ψ) (z : V (nd X)) :
    HasFDerivAt (fun z' => mat (nmat X z') τ) (LinearMap.toContinuousLinearMap (Lin X τ)) z := by
  have e : (fun z' => mat (nmat X z') τ) = fun z' => 1 + LinearMap.toContinuousLinearMap (Lin X τ) z' :=
    funext fun z' => by rw [nmat_eq]; rfl
  rw [e]
  exact (LinearMap.toContinuousLinearMap (Lin X τ)).hasFDerivAt.const_add 1

theorem isUnit_nmat (τ : X.Ψ) (z : V (nd X)) : IsUnit (mat (nmat X z) τ) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_lowerTriangular]
  · simp [mat, nmat]
  · intro a c hac
    have h' : a < c := OrderDual.toDual_lt_toDual.mp hac
    simp only [mat, nmat, Matrix.of_apply]
    rw [dite_eq_right (not_lt.mpr h'.le), if_neg h'.ne]

def entryL (a c : Fin r) : Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ] ℂ where
  toFun M := M a c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem lower_deriv (τ : X.Ψ) (A : Matrix (Fin r) (Fin r) ℂ) (U : Set (V (nd X))) (hU : IsOpen U)
    (Φ : V (nd X) → V (nd X)) (bf : V (nd X) → Matrix (Fin r) (Fin r) ℂ)
    (hrel : ∀ z ∈ U, mat (nmat X (Φ z)) τ * bf z = A * mat (nmat X z) τ)
    (hup : ∀ z ∈ U, ∀ a c : Fin r, c < a → bf z a c = 0)
    (z : V (nd X)) (hz : z ∈ U) (Φ' : V (nd X) →L[ℂ] V (nd X)) (hΦ : HasFDerivAt Φ Φ' z)
    (h : V (nd X)) (a c : Fin r) (hca : c < a) :
    (bf z * (Ring.inverse (mat (nmat X z) τ) * Lin X τ h) -
      (Ring.inverse (mat (nmat X (Φ z)) τ) * Lin X τ (Φ' h)) * bf z) a c = 0 := by
  obtain ⟨G, hG⟩ : ∃ G : V (nd X) → Matrix (Fin r) (Fin r) ℂ,
      G = fun w => Ring.inverse (mat (nmat X (Φ w)) τ) * A * mat (nmat X w) τ := ⟨_, rfl⟩
  have hbfG : ∀ w ∈ U, bf w = G w := by
    intro w hw
    rw [hG]
    dsimp only
    rw [mul_assoc, ← hrel w hw, ← mul_assoc,
      Ring.inverse_mul_cancel _ (isUnit_nmat X τ (Φ w)), one_mul]
  have hMd : HasFDerivAt (fun w => mat (nmat X (Φ w)) τ)
      ((LinearMap.toContinuousLinearMap (Lin X τ)).comp Φ') z :=
    (hasFDerivAt_nmat X τ (Φ z)).comp z hΦ
  have hinv : DifferentiableAt ℂ (fun w => Ring.inverse (mat (nmat X (Φ w)) τ)) z := by
    have hi := (differentiableAt_inverse (𝕜 := ℂ) (isUnit_nmat X τ (Φ z))).comp z hMd.differentiableAt
    exact hi
  have hGd : DifferentiableAt ℂ G z := by
    rw [hG]
    exact (hinv.mul (differentiableAt_const A)).mul (hasFDerivAt_nmat X τ z).differentiableAt
  have hGd' : HasFDerivAt G (fderiv ℂ G z) z := hGd.hasFDerivAt
  have hent : (fderiv ℂ G z h) a c = 0 := by
    have hE : HasFDerivAt (fun w => G w a c)
        ((LinearMap.toContinuousLinearMap (entryL a c)).comp (fderiv ℂ G z)) z :=
      (LinearMap.toContinuousLinearMap (entryL a c)).hasFDerivAt.comp z hGd'
    have heq : (fun w => G w a c) =ᶠ[𝓝 z] fun _ => (0 : ℂ) :=
      Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw => by
        show G w a c = 0
        rw [← hbfG w hw]
        exact hup w hw a c hca
    have h0 : HasFDerivAt (fun w => G w a c) (0 : V (nd X) →L[ℂ] ℂ) z :=
      (hasFDerivAt_const (0 : ℂ) z).congr_of_eventuallyEq heq
    have := congrArg (fun T => T h) (hE.unique h0)
    exact this
  have hLHS := hMd.mul' hGd'
  have hRHS : HasFDerivAt (fun w => A * mat (nmat X w) τ)
      (A • LinearMap.toContinuousLinearMap (Lin X τ)) z := (hasFDerivAt_nmat X τ z).const_mul A
  have heq2 : (fun w => A * mat (nmat X w) τ) =ᶠ[𝓝 z] fun w => mat (nmat X (Φ w)) τ * G w :=
    Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw => by
      show A * mat (nmat X w) τ = mat (nmat X (Φ w)) τ * G w
      rw [← hbfG w hw]
      exact (hrel w hw).symm
  have hU2 := (hLHS.congr_of_eventuallyEq heq2).unique hRHS
  have I : mat (nmat X (Φ z)) τ * fderiv ℂ G z h + Lin X τ (Φ' h) * G z = A * Lin X τ h := by
    have := congrArg (fun T => T h) hU2
    exact this
  have e1 : Ring.inverse (mat (nmat X (Φ z)) τ) * mat (nmat X (Φ z)) τ = 1 :=
    Ring.inverse_mul_cancel _ (isUnit_nmat X τ (Φ z))
  have e2 : mat (nmat X z) τ * Ring.inverse (mat (nmat X z) τ) = 1 :=
    Ring.mul_inverse_cancel _ (isUnit_nmat X τ z)
  have hGh : fderiv ℂ G z h =
      Ring.inverse (mat (nmat X (Φ z)) τ) * (A * Lin X τ h - Lin X τ (Φ' h) * G z) := by
    rw [← I, add_sub_cancel_right, ← mul_assoc, e1, one_mul]
  have hGz : G z * (Ring.inverse (mat (nmat X z) τ) * Lin X τ h) =
      Ring.inverse (mat (nmat X (Φ z)) τ) * A * Lin X τ h := by
    rw [hG]
    simp only
    rw [mul_assoc (Ring.inverse (mat (nmat X (Φ z)) τ) * A), ← mul_assoc (mat (nmat X z) τ), e2, one_mul]
  rw [hbfG z hz, hGz, ← hent, hGh, mul_sub]
  simp only [mul_assoc]

end ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
end
end

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates Matrix Topology Filter
open scoped Classical

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem nmat_lower (w : V (nd X)) (τ : X.Ψ) : (mat (nmat X w) τ).BlockTriangular OrderDual.toDual := by
  intro i j hij
  have hij' : i < j := hij
  simp [mat, nmat, hij'.ne, not_lt.mpr hij'.le]

theorem ninv_lower (w : V (nd X)) (τ : X.Ψ) (x y : Fin r) (hxy : x < y) :
    Ring.inverse (mat (nmat X w) τ) x y = 0 := by
  have : Invertible (mat (nmat X w) τ) := (isUnit_nmat X τ w).invertible
  have h := Matrix.blockTriangular_inv_of_blockTriangular (nmat_lower X w τ)
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  exact h hxy

theorem ninv_diag (w : V (nd X)) (τ : X.Ψ) (a : Fin r) : Ring.inverse (mat (nmat X w) τ) a a = 1 := by
  have hu : IsUnit (mat (nmat X w) τ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_nmat X τ w)

  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv _ hu) a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a] at h1
  · rw [← Matrix.nonsing_inv_eq_ringInverse]
    simpa [mat, nmat] using h1
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · have h0 : (mat (nmat X w) τ)⁻¹ k a = 0 := by
        rw [Matrix.nonsing_inv_eq_ringInverse]
        exact ninv_lower X w τ k a hlt
      rw [h0, mul_zero]
    · rw [nmat_lower X w τ hgt, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

def ninvF (w : V (nd X)) : Frame X.Ψ r := fun τ a c => Ring.inverse (mat (nmat X w) τ) a c

theorem det_lmulL_ninv (w : V (nd X)) : LinearMap.det (lmulL X (ninvF X w)) = 1 :=
  det_lmulL_unit X (ninvF X w) (fun τ a x h => ninv_lower X w τ a x h) (fun τ a => ninv_diag X w τ a)

theorem embF_lmulL (w : V (nd X)) (τ : X.Ψ) (v : V (nd X)) (x c : Fin r) :
    embF X (lmulL X (ninvF X w) (vecOf X v)) τ x c =
      (Ring.inverse (mat (nmat X w) τ) * Lin X τ v) x c := by
  have hl : ∀ (N : Frame X.Ψ r) (u : Ent X → ℂ) (e : Ent X),
      lmulL X N u e = ∑ k, N e.1 e.2.1.1 k * embF X u e.1 k e.2.1.2 := fun _ _ _ => rfl
  have hL : ∀ k c' : Fin r, Lin X τ v k c' = embF X (vecOf X v) τ k c' := fun _ _ => rfl
  rw [Matrix.mul_apply]
  by_cases h : c < x
  · rw [embF, dite_eq_left h, hl]
    rfl
  ·
    rw [embF, dite_eq_right h]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : c < k
    · rw [ninv_lower X w τ x k (lt_of_le_of_lt (not_lt.mp h) hk), zero_mul]
    · rw [hL, embF, dite_eq_right hk, mul_zero]

def vecL : V (nd X) ≃ₗ[ℂ] (Ent X → ℂ) :=
  (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).trans
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin (Ent X)))

theorem vecL_apply (v : V (nd X)) : vecL X v = vecOf X v := rfl

theorem kappa_statement_holds : KapGGStatement (E := E) := by
  intro r X x0 x1 γ U Φ bf hU hdiff hrel z hz
  obtain ⟨hdom, hbor, -⟩ := hrel z hz
  set Φ' := fderiv ℂ Φ z with hΦ'
  have hΦ : HasFDerivAt Φ Φ' z := ((hdiff z hz).differentiableAt (hU.mem_nhds hz)).hasFDerivAt

  have hmat : ∀ z' ∈ U, ∀ τ : X.Ψ, mat x0 τ * mat (nmat X z') τ =
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x1 τ) *
        (mat (nmat X (Φ z')) τ * mat (bf z') τ) := by
    intro z' hz' τ
    have h := congrFun (hrel z' hz').2.2 τ
    change mat x0 τ * mat (nmat X z') τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 *
      ((mat x1 τ * mat (nmat X (Φ z')) τ) * mat (bf z') τ) at h
    rw [h]
    simp only [Matrix.mul_assoc]

  have hG : ∀ τ : X.Ψ, IsUnit ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x1 τ).det := by
    intro τ
    have h0 : (mat x0 τ * mat (nmat X z) τ).det ≠ 0 := (hdom τ).1
    rw [hmat z hz τ, Matrix.det_mul] at h0
    exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul h0)
  have hrel' : ∀ τ : X.Ψ, ∀ z' ∈ U, mat (nmat X (Φ z')) τ * mat (bf z') τ =
      (((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x1 τ)⁻¹ * mat x0 τ) * mat (nmat X z') τ := by
    intro τ z' hz'
    rw [Matrix.mul_assoc, hmat z' hz' τ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hG τ),
      Matrix.one_mul]
  have hup : ∀ τ : X.Ψ, ∀ z' ∈ U, ∀ a c : Fin r, c < a → mat (bf z') τ a c = 0 :=
    fun τ z' hz' a c h => ((hrel z' hz').2.1 τ).2 a c h
  set b := bf z with hb

  have key : (rmulL X b) ∘ₗ (lmulL X (ninvF X (Φ z))) ∘ₗ
      ((vecL X : V (nd X) →ₗ[ℂ] (Ent X → ℂ)) ∘ₗ (Φ' : V (nd X) →ₗ[ℂ] V (nd X)) ∘ₗ
        ((vecL X).symm : (Ent X → ℂ) →ₗ[ℂ] V (nd X))) =
      (lmulL X b) ∘ₗ (lmulL X (ninvF X z)) := by
    refine LinearMap.ext fun u => funext fun e => ?_
    obtain ⟨h, rfl⟩ : ∃ h, vecL X h = u := ⟨(vecL X).symm u, (vecL X).apply_symm_apply u⟩
    rcases e with ⟨τ, ⟨⟨a, c⟩, hca⟩⟩
    have hld := lower_deriv X τ _ U hU Φ (fun z' => mat (bf z') τ) (hrel' τ) (hup τ) z hz Φ' hΦ h a c hca
    rw [Matrix.sub_apply, sub_eq_zero, Matrix.mul_apply, Matrix.mul_apply] at hld
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      ContinuousLinearMap.coe_coe]
    simp only [vecL_apply]
    show ∑ y, embF X (lmulL X (ninvF X (Φ z)) (vecOf X (Φ' h))) τ a y * b τ y c =
      ∑ x, b τ a x * embF X (lmulL X (ninvF X z) (vecOf X h)) τ x c
    simp only [embF_lmulL]
    exact hld.symm
  have hdet := congrArg LinearMap.det key
  simp only [LinearMap.det_comp, LinearMap.det_conj, det_lmulL_ninv, one_mul] at hdet
  have hupb : ∀ τ a x, x < a → b τ a x = 0 := fun τ a x h => (hbor τ).2 a x h
  rw [det_lmulL_upper X b hupb, det_rmulL_upper X b hupb] at hdet

  have hd : ∀ τ a, b τ a a ≠ 0 := by
    intro τ a
    have h0 := (hbor τ).1
    rw [Matrix.det_of_isUpperTriangular (M := mat b τ) (fun i j h => (hbor τ).2 i j h)] at h0
    exact Finset.prod_ne_zero_iff.mp h0 a (Finset.mem_univ a)
  have hcol : ∏ e : Ent X, b e.1 e.2.1.2 e.2.1.2 ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun e _ => hd _ _
  rw [bchar_kap X b hd]
  show LinearMap.det (Φ' : V (nd X) →ₗ[ℂ] V (nd X)) = _
  exact eq_div_of_mul_eq hcol (by rw [mul_comm, hdet, mul_one])

end ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
