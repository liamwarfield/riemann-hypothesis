module

public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul

@[expose] public section

section -- merged from ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsCalc
namespace ReciprocityTheory.AnForm.A

open MeasureTheory ReciprocityTheory.AnForm Matrix

noncomputable section

theorem integrable_fderiv_apply_of_cs {D : ℕ} {g : (Fin D → ℂ) → ℂ} (hg : ContDiff ℝ 1 g)
    (hcs : HasCompactSupport g) (u : Fin D → ℂ) : Integrable (fun z => fderiv ℝ g z u) := by
  have hc : Continuous fun z => fderiv ℝ g z u :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine hc.integrable_of_hasCompactSupport ?_
  exact (hcs.fderiv ℝ).mono fun z hz h0 => hz (by simp [h0])

theorem integral_fderiv_apply_of_cs {D : ℕ} {g : (Fin D → ℂ) → ℂ} (hg : ContDiff ℝ 1 g)
    (hcs : HasCompactSupport g) (u : Fin D → ℂ) : ∫ z, fderiv ℝ g z u = 0 := by
  have hd := hg.differentiable one_ne_zero
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : Fin D → ℂ => (1 : ℂ)) (g := g) (v := u)
    (by simp) (by simpa using integrable_fderiv_apply_of_cs hg hcs u)
    (by simpa using (hg.continuous.integrable_of_hasCompactSupport hcs))
    (fun x _ => differentiableAt_const _) (fun x _ => hd x)
  simpa using h

theorem integral_dz_formula : IntegralDzStatement := by
  intro D j g hg hcs
  have h1 := integrable_fderiv_apply_of_cs hg hcs (Pi.single j 1)
  have h2 := integrable_fderiv_apply_of_cs hg hcs (Complex.I • Pi.single j 1)
  have i1 := integral_fderiv_apply_of_cs hg hcs (Pi.single j 1)
  have i2 := integral_fderiv_apply_of_cs hg hcs (Complex.I • Pi.single j 1)
  constructor
  · unfold dz
    rw [integral_div, integral_sub h1 (h2.const_mul _), integral_const_mul, i1, i2]
    simp
  · unfold dzb
    rw [integral_div, integral_add h1 (h2.const_mul _), integral_const_mul, i1, i2]
    simp

theorem mixedDisc_transpose {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mdisc (fun k => (A k)ᵀ) = mdisc A := by
  unfold mdisc
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← Matrix.transpose_sum, Matrix.det_transpose]

theorem mdisc_swap_row {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (p q : Fin D) (hpq : p ≠ q)
    (j k a b : Fin D) :
    mdisc (Function.update (Function.update A p (Matrix.single j k 1)) q (Matrix.single a b 1)) =
      - mdisc (Function.update (Function.update A p (Matrix.single a k 1)) q
          (Matrix.single j b 1)) := by
  have hu : ∀ (X Y : Matrix (Fin D) (Fin D) ℂ) r, Function.update (Function.update A p X) q Y r =
      if r = q then Y else if r = p then X else A r := by
    intro X Y r
    simp only [Function.update_apply]
  rw [mdisc_eq_sum_perm, mdisc_eq_sum_perm, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h1 : σ k = p
  · by_cases h2 : σ b = q
    · have hkb : k ≠ b := fun h => hpq (h1.symm.trans (h ▸ h2))
      have hM : (Matrix.of fun i c => Function.update (Function.update A p (Matrix.single a k 1)) q
          (Matrix.single j b 1) (σ c) i c) = (Matrix.of fun i c => Function.update (Function.update A p
          (Matrix.single j k 1)) q (Matrix.single a b 1) (σ c) i c).submatrix id (Equiv.swap k b) := by
        ext i c
        simp only [Matrix.of_apply, Matrix.submatrix_apply, id, hu]
        by_cases hck : c = k
        · rw [hck, Equiv.swap_apply_left, h1, h2]
          simp [hpq, Ne.symm hpq, Matrix.single_apply]
        · by_cases hcb : c = b
          · rw [hcb, Equiv.swap_apply_right, h1, h2]
            simp [hpq, Ne.symm hpq, Matrix.single_apply]
          · rw [Equiv.swap_apply_of_ne_of_ne hck hcb]
            have hp : σ c ≠ p := fun h => hck (σ.injective (h.trans h1.symm))
            have hq : σ c ≠ q := fun h => hcb (σ.injective (h.trans h2.symm))
            simp [hp, hq]
      rw [hM, Matrix.det_permute', Equiv.Perm.sign_swap hkb]
      simp
    · have hbq : b ≠ σ.symm q := fun h => h2 (by rw [h, Equiv.apply_symm_apply])
      rw [Matrix.det_eq_zero_of_column_eq_zero (σ.symm q) fun i => by
          simp [hu, Matrix.single_apply, hbq],
        Matrix.det_eq_zero_of_column_eq_zero (σ.symm q) fun i => by
          simp [hu, Matrix.single_apply, hbq], neg_zero]
  · have hkp : k ≠ σ.symm p := fun h => h1 (by rw [h, Equiv.apply_symm_apply])
    rw [Matrix.det_eq_zero_of_column_eq_zero (σ.symm p) fun i => by
        simp [hu, Matrix.single_apply, hkp, hpq],
      Matrix.det_eq_zero_of_column_eq_zero (σ.symm p) fun i => by
        simp [hu, Matrix.single_apply, hkp, hpq], neg_zero]

abbrev BilinSp (D : ℕ) := (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ

def evalL {D : ℕ} (x w : Fin D → ℂ) : BilinSp D →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ w).comp (ContinuousLinearMap.apply ℝ ((Fin D → ℂ) →L[ℝ] ℝ) x)

theorem evalL_apply {D : ℕ} (x w : Fin D → ℂ) (H : BilinSp D) : evalL x w H = H x w := rfl

def hessEntry {D : ℕ} (a b : Fin D) : BilinSp D →L[ℝ] ℂ :=
  (1 / 4 : ℂ) • (Complex.ofRealCLM.comp
      (evalL (Pi.single a 1) (Pi.single b 1) +
        evalL (Complex.I • Pi.single a 1) (Complex.I • Pi.single b 1)) +
    Complex.I • Complex.ofRealCLM.comp
      (evalL (Pi.single a 1) (Complex.I • Pi.single b 1) -
        evalL (Complex.I • Pi.single a 1) (Pi.single b 1)))

theorem hessEntry_apply {D : ℕ} (a b : Fin D) (H : BilinSp D) :
    hessEntry a b H =
      ((H (Pi.single a 1) (Pi.single b 1) +
          H (Complex.I • Pi.single a 1) (Complex.I • Pi.single b 1) : ℝ) +
        Complex.I * ((H (Pi.single a 1) (Complex.I • Pi.single b 1) -
          H (Complex.I • Pi.single a 1) (Pi.single b 1) : ℝ))) / 4 := by
  simp only [hessEntry, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, evalL_apply,
    smul_eq_mul]
  push_cast
  ring

def hessMat {D : ℕ} : BilinSp D →ₗ[ℝ] Matrix (Fin D) (Fin D) ℂ where
  toFun H := Matrix.of fun a b => hessEntry a b H
  map_add' H K := by ext a b; simp
  map_smul' c H := by ext a b; simp

theorem hessMat_apply {D : ℕ} (H : BilinSp D) (a b : Fin D) : hessMat H a b = hessEntry a b H := rfl

theorem hessC_eq_hessMat {D : ℕ} (φ : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ) :
    hessC φ y = hessMat (fderiv ℝ (fderiv ℝ φ) y) := by
  ext a b
  rw [hessMat_apply, hessEntry_apply]
  rfl

theorem continuous_mdisc {D : ℕ} :
    Continuous (fun A : Fin D → Matrix (Fin D) (Fin D) ℂ => mdisc A) := by
  unfold mdisc
  refine continuous_const.mul (continuous_finsetSum _ fun S _ => continuous_const.mul ?_)
  exact (continuous_finsetSum _ fun k _ => continuous_apply k).matrix_det

theorem hessCof_eq {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (y : Fin (n + 1) → ℂ) (j k : Fin (n + 1)) :
    hessCof φ y j k = mdisc (Fin.cons (Matrix.single j k 1) fun i => hessMat (fderiv ℝ (fderiv ℝ (φ i)) y)) := by
  simp only [hessCof, mixedCof, hessC_eq_hessMat]

private theorem exists_continuousMultilinearMap_eq_mdisc (D : ℕ) :
    ∃ Mc : ContinuousMultilinearMap ℝ (fun _ : Fin D => Fin D → Fin D → ℂ) ℂ,
      ∀ x : Fin D → Matrix (Fin D) (Fin D) ℂ, Mc x = mdisc x := by
  obtain ⟨M, hM⟩ := (by
    show ∃ F : MultilinearMap (RingHom.id ℂ)
        (fun _ : Fin D => Matrix (Fin D) (Fin D) ℂ) ℂ,
        ⇑F = _root_.ReciprocityTheory.AnForm.mdisc
    refine ⟨MultilinearMap.mk' _root_.ReciprocityTheory.AnForm.mdisc
      _root_.ReciprocityTheory.AnForm.A.mdisc_update_add ?_, rfl⟩
    intro A k c B
    simpa only [RingHom.id_apply, smul_eq_mul] using
      (_root_.ReciprocityTheory.AnForm.A.mdisc_update_smul A k c B))
  let Mr : MultilinearMap (RingHom.id ℝ) (fun _ : Fin D => Fin D → Fin D → ℂ) ℂ := M.restrictScalars ℝ
  have hMr : ∀ x : Fin D → Matrix (Fin D) (Fin D) ℂ, Mr x = mdisc x := fun x => congrFun hM x
  exact ⟨⟨Mr, by
    have : (⇑Mr : (Fin D → Fin D → Fin D → ℂ) → ℂ) = fun x => mdisc x := funext hMr
    show Continuous (⇑Mr)
    rw [this]
    exact continuous_mdisc⟩, hMr⟩

theorem hessCof_hasDeriv {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (z : Fin (n + 1) → ℂ)
    (hφ : ∀ i, DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (φ i))) z) (j k : Fin (n + 1)) :
    DifferentiableAt ℝ (fun y => hessCof φ y j k) z ∧ ∀ u,
      fderiv ℝ (fun y => hessCof φ y j k) z u = ∑ i, mdisc (Function.update
        (Fin.cons (Matrix.single j k 1) fun l => hessC (φ l) z) i.succ
          (hessMat (fderiv ℝ (fderiv ℝ (fderiv ℝ (φ i))) z u))) := by
  obtain ⟨Mc, hMc⟩ := exists_continuousMultilinearMap_eq_mdisc (n + 1)
  let Lℓ : BilinSp (n + 1) →ₗ[ℝ] (Fin (n + 1) → Fin (n + 1) → ℂ) := hessMat
  let L : BilinSp (n + 1) →L[ℝ] (Fin (n + 1) → Fin (n + 1) → ℂ) := LinearMap.toContinuousLinearMap Lℓ
  let g : (Fin (n + 1) → ℂ) → (Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℂ) :=
    fun y => Fin.cons (Matrix.single j k (1 : ℂ) : Fin (n + 1) → Fin (n + 1) → ℂ)
      fun l => L (fderiv ℝ (fderiv ℝ (φ l)) y)
  let g' : (Fin (n + 1) → ℂ) →L[ℝ] (Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℂ) :=
    ContinuousLinearMap.pi fun i =>
      Fin.cases 0 (fun l => L.comp (fderiv ℝ (fderiv ℝ (fderiv ℝ (φ l))) z)) i
  have hg : HasFDerivAt g g' z := by
    refine hasFDerivAt_pi.2 fun i => ?_
    refine Fin.cases ?_ (fun l => ?_) i
    · simp only [g, g', Fin.cons_zero, Fin.cases_zero]
      exact hasFDerivAt_const _ _
    · simp only [g, g', Fin.cons_succ, Fin.cases_succ]
      exact L.hasFDerivAt.comp z (hφ l).hasFDerivAt
  have hfun : (fun y => hessCof φ y j k) = fun y => Mc (g y) := by
    funext y
    rw [hessCof_eq, ← hMc]
    rfl
  have hD : HasFDerivAt (fun y => Mc (g y)) ((Mc.linearDeriv (g z)).comp g') z :=
    (Mc.hasFDerivAt (g z)).comp z hg
  rw [hfun]
  refine ⟨hD.differentiableAt, fun u => ?_⟩
  rw [hD.fderiv, ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.linearDeriv_apply,
    Fin.sum_univ_succ]
  have h0 : g' u 0 = 0 := by simp [g']
  have hz : Mc (Function.update (g z) 0 (g' u 0)) = 0 := by
    rw [h0]
    exact Mc.toMultilinearMap.map_update_zero _ _
  rw [hz, zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hMc]
  congr 1
  funext r
  by_cases hr : r = i.succ
  · rw [hr, Function.update_self, Function.update_self]
    simp only [g', ContinuousLinearMap.pi_apply, Fin.cases_succ, ContinuousLinearMap.comp_apply]
    rfl
  · rw [Function.update_of_ne hr, Function.update_of_ne hr]
    refine Fin.cases ?_ (fun l => ?_) r
    · rfl
    · simp only [g, Fin.cons_succ]
      rw [hessC_eq_hessMat]
      rfl

theorem mdisc_update_comb {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (q : Fin D) (c d : ℂ)
    (B C : Matrix (Fin D) (Fin D) ℂ) :
    mdisc (Function.update A q (c • B + d • C)) =
      c * mdisc (Function.update A q B) + d * mdisc (Function.update A q C) := by
  rw [mdisc_update_add, mdisc_update_smul, mdisc_update_smul]

theorem mdisc_update_expand {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (q : Fin D)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    mdisc (Function.update A q X) =
      ∑ a, ∑ b, X a b * mdisc (Function.update A q (Matrix.single a b 1)) := by
  obtain ⟨M, hM⟩ := (by
    show ∃ F : MultilinearMap (RingHom.id ℂ)
        (fun _ : Fin D => Matrix (Fin D) (Fin D) ℂ) ℂ,
        ⇑F = _root_.ReciprocityTheory.AnForm.mdisc
    refine ⟨MultilinearMap.mk' _root_.ReciprocityTheory.AnForm.mdisc
      _root_.ReciprocityTheory.AnForm.A.mdisc_update_add ?_, rfl⟩
    intro A k c B
    simpa only [RingHom.id_apply, smul_eq_mul] using
      (_root_.ReciprocityTheory.AnForm.A.mdisc_update_smul A k c B))
  have hX : X = ∑ a, ∑ b, X a b • Matrix.single a b (1 : ℂ) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero]
    rw [Finset.sum_eq_single i (fun c _ hc => by simp [hc]) (by simp),
      Finset.sum_eq_single j (fun c _ hc => by simp [hc]) (by simp)]
    simp
  have h : ∀ Y, mdisc (Function.update A q Y) = M.toLinearMap A q Y := fun Y => by
    rw [MultilinearMap.toLinearMap_apply, hM]
  rw [h]
  conv_lhs => rw [hX]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, smul_eq_mul]
  simp only [← h]

theorem mdisc_sum_row {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (p q : Fin D) (hpq : p ≠ q)
    (k : Fin D) (S : Fin D → Matrix (Fin D) (Fin D) ℂ) (hS : ∀ j a b, S j a b = S a j b) :
    ∑ j, mdisc (Function.update (Function.update A p (Matrix.single j k 1)) q (S j)) = 0 := by
  rw [Finset.sum_congr rfl fun j _ => mdisc_update_expand _ q (S j)]
  have h2 : ∑ j, ∑ a, ∑ b, S j a b * mdisc (Function.update (Function.update A p (Matrix.single j k 1)) q
      (Matrix.single a b 1)) = -∑ j, ∑ a, ∑ b, S j a b * mdisc (Function.update
      (Function.update A p (Matrix.single j k 1)) q (Matrix.single a b 1)) := by
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    rw [hS a j b, mdisc_swap_row A p q hpq j k a b]
    ring
  linear_combination (1 / 2 : ℂ) * h2

theorem update_transpose {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (p q : Fin D)
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    (fun r => (Function.update (Function.update A p X) q Y r)ᵀ) =
      Function.update (Function.update (fun r => (A r)ᵀ) p Xᵀ) q Yᵀ := by
  funext r
  simp only [Function.update_apply]
  split_ifs <;> rfl

theorem mdisc_sum_col {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (p q : Fin D) (hpq : p ≠ q)
    (j : Fin D) (S : Fin D → Matrix (Fin D) (Fin D) ℂ) (hS : ∀ k a b, S k a b = S b a k) :
    ∑ k, mdisc (Function.update (Function.update A p (Matrix.single j k 1)) q (S k)) = 0 := by
  have ht : ∀ k', mdisc (Function.update (Function.update A p (Matrix.single j k' 1)) q (S k')) =
      mdisc (Function.update (Function.update (fun r => (A r)ᵀ) p (Matrix.single k' j 1)) q (S k')ᵀ) := by
    intro k'
    rw [← mixedDisc_transpose, update_transpose, Matrix.transpose_single]
  rw [Finset.sum_congr rfl fun k' _ => ht k']
  exact mdisc_sum_row (fun r => (A r)ᵀ) p q hpq j (fun k' => (S k')ᵀ)
    (fun x a b => by simp only [Matrix.transpose_apply]; exact hS x b a)

theorem exists_hessCof_multilinear (n : ℕ) (j k : Fin (n + 1)) :
    ∃ G : ContinuousMultilinearMap ℝ (fun _ : Fin n => BilinSp (n + 1)) ℂ,
      ∀ (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (y : Fin (n + 1) → ℂ),
        hessCof φ y j k = G (fun i => fderiv ℝ (fderiv ℝ (φ i)) y) := by
  obtain ⟨Mc, hMc⟩ := exists_continuousMultilinearMap_eq_mdisc (n + 1)
  let Lℓ : BilinSp (n + 1) →ₗ[ℝ] (Fin (n + 1) → Fin (n + 1) → ℂ) := hessMat
  let L : BilinSp (n + 1) →L[ℝ] (Fin (n + 1) → Fin (n + 1) → ℂ) := LinearMap.toContinuousLinearMap Lℓ
  refine ⟨(Mc.curryLeft (Matrix.single j k (1 : ℂ) : Fin (n + 1) → Fin (n + 1) → ℂ)).compContinuousLinearMap
    fun _ => L, fun φ y => ?_⟩
  rw [hessCof_eq, ← hMc]
  rfl

theorem hessCof_contDiffOn {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (U : Set (Fin (n + 1) → ℂ))
    (hU : IsOpen U) (m : ℕ) (hφ : ∀ i, ContDiffOn ℝ (m + 2) (φ i) U) (j k : Fin (n + 1)) :
    ContDiffOn ℝ m (fun y => hessCof φ y j k) U := by
  obtain ⟨G, hG⟩ := exists_hessCof_multilinear n j k
  have h2 : ∀ i, ContDiffOn ℝ m (fun y => fderiv ℝ (fderiv ℝ (φ i)) y) U := fun i =>
    ((hφ i).fderiv_of_isOpen (m := ((m + 1 : ℕ) : WithTop ℕ∞)) hU
      (by exact_mod_cast (show m + 1 + 1 ≤ m + 2 by omega))).fderiv_of_isOpen hU
      (by exact_mod_cast (le_refl (m + 1)))
  have hc : ContDiffOn ℝ m (fun y => G (fun i => fderiv ℝ (fderiv ℝ (φ i)) y)) U :=
    G.contDiff.comp_contDiffOn (contDiffOn_pi.2 h2)
  have hfun : (fun y => hessCof φ y j k) = fun y => G (fun i => fderiv ℝ (fderiv ℝ (φ i)) y) :=
    funext fun y => hG φ y
  rw [hfun]
  exact hc

end

end ReciprocityTheory.AnForm.A
end

namespace ReciprocityTheory.AnForm.A

open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology

noncomputable section

theorem third_fderiv_symm_one_two {D : ℕ} (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (h : ContDiffAt ℝ 3 φ z)
    (u x : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) z u x = fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) z x u := by
  have h2 : ContDiffAt ℝ 2 (fderiv ℝ φ) z := h.fderiv_right (by first | norm_num | simp | rfl)
  exact h2.isSymmSndFDerivAt (by first | simp | norm_num | (simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)) u x

theorem differentiableAt_snd_fderiv {D : ℕ} (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (h : ContDiffAt ℝ 3 φ z) : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ φ)) z := by
  have h2 : ContDiffAt ℝ 2 (fderiv ℝ φ) z := h.fderiv_right (by first | norm_num | simp | rfl)
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ φ)) z := h2.fderiv_right (by first | norm_num | simp | rfl)
  exact h1.differentiableAt (by first | norm_num | simp | exact one_ne_zero)

theorem third_fderiv_symm_two_three {D : ℕ} (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (h : ContDiffAt ℝ 3 φ z)
    (u x y : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) z u x y = fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) z u y x := by
  have hd := differentiableAt_snd_fderiv φ z h
  have key : ∀ x y : Fin D → ℂ,
      fderiv ℝ (⇑(evalL x y) ∘ fderiv ℝ (fderiv ℝ φ)) z =
        (evalL x y).comp (fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) z) :=
    fun x y => ((evalL x y).hasFDerivAt.comp z hd.hasFDerivAt).fderiv
  have h2 : ContDiffAt ℝ 2 φ z := h.of_le (by first | norm_num | simp | rfl)
  have hev : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 φ w := h2.eventually (by first | simp | norm_num | decide | exact ENat.coe_ne_top _)
  have ev : (⇑(evalL x y) ∘ fderiv ℝ (fderiv ℝ φ)) =ᶠ[𝓝 z]
      (⇑(evalL y x) ∘ fderiv ℝ (fderiv ℝ φ)) := by
    filter_upwards [hev] with w hw
    simp only [Function.comp_apply, evalL, ContinuousLinearMap.coe_comp',
      ContinuousLinearMap.apply_apply]
    exact hw.isSymmSndFDerivAt (by first | simp | norm_num | (simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)) x y
  have e := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) ev
  rw [key x y, key y x] at e
  have e2 := congrArg (fun L => L u) e
  simpa only [evalL, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.apply_apply] using e2

theorem dzEntry_symm {D : ℕ} (T : (Fin D → ℂ) →L[ℝ] BilinSp D) (hT : ∀ u x, T u x = T x u)
    (j a b : Fin D) :
    (1 / 2 : ℂ) * hessEntry a b (T (Pi.single j 1)) +
        (-(Complex.I / 2)) * hessEntry a b (T (Complex.I • Pi.single j 1)) =
      (1 / 2 : ℂ) * hessEntry j b (T (Pi.single a 1)) +
        (-(Complex.I / 2)) * hessEntry j b (T (Complex.I • Pi.single a 1)) := by
  have e1 := hT (Pi.single j 1) (Pi.single a 1)
  have e2 := hT (Pi.single j 1) (Complex.I • Pi.single a 1)
  have e3 := hT (Complex.I • Pi.single j 1) (Pi.single a 1)
  have e4 := hT (Complex.I • Pi.single j 1) (Complex.I • Pi.single a 1)
  simp only [hessEntry_apply, e1, e2, e3, e4]
  push_cast
  linear_combination
    ((T (Complex.I • Pi.single a 1) (Pi.single j 1) (Complex.I • Pi.single b 1) : ℂ) -
      (T (Pi.single a 1) (Complex.I • Pi.single j 1) (Complex.I • Pi.single b 1) : ℂ)) / 8 *
      Complex.I_sq

theorem dzbEntry_symm {D : ℕ} (T : (Fin D → ℂ) →L[ℝ] BilinSp D)
    (hT : ∀ u x y, T u x y = T y x u) (k a b : Fin D) :
    (1 / 2 : ℂ) * hessEntry a b (T (Pi.single k 1)) +
        (Complex.I / 2) * hessEntry a b (T (Complex.I • Pi.single k 1)) =
      (1 / 2 : ℂ) * hessEntry a k (T (Pi.single b 1)) +
        (Complex.I / 2) * hessEntry a k (T (Complex.I • Pi.single b 1)) := by
  have e1 := hT (Pi.single b 1) (Pi.single a 1) (Pi.single k 1)
  have e2 := hT (Pi.single b 1) (Complex.I • Pi.single a 1) (Complex.I • Pi.single k 1)
  have e3 := hT (Pi.single b 1) (Pi.single a 1) (Complex.I • Pi.single k 1)
  have e4 := hT (Pi.single b 1) (Complex.I • Pi.single a 1) (Pi.single k 1)
  have e5 := hT (Complex.I • Pi.single b 1) (Pi.single a 1) (Pi.single k 1)
  have e6 := hT (Complex.I • Pi.single b 1) (Complex.I • Pi.single a 1)
    (Complex.I • Pi.single k 1)
  have e7 := hT (Complex.I • Pi.single b 1) (Pi.single a 1) (Complex.I • Pi.single k 1)
  have e8 := hT (Complex.I • Pi.single b 1) (Complex.I • Pi.single a 1) (Pi.single k 1)
  simp only [hessEntry_apply, e1, e2, e3, e4, e5, e6, e7, e8]
  push_cast
  linear_combination
    ((T (Pi.single k 1) (Complex.I • Pi.single a 1) (Complex.I • Pi.single b 1) : ℂ) -
      (T (Complex.I • Pi.single k 1) (Complex.I • Pi.single a 1) (Pi.single b 1) : ℂ)) / 8 *
      Complex.I_sq

theorem piolaStatement_statement : PiolaStatement := by
  intro n φ U hU hφ z hz
  have hφz : ∀ i, ContDiffAt ℝ 3 (φ i) z := fun i => (hφ i).contDiffAt (hU.mem_nhds hz)
  have hdiff : ∀ i, DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (φ i))) z :=
    fun i => differentiableAt_snd_fderiv _ z (hφz i)
  set T : Fin n → (Fin (n + 1) → ℂ) →L[ℝ] BilinSp (n + 1) :=
    fun i => fderiv ℝ (fderiv ℝ (fderiv ℝ (φ i))) z with hTdef
  set H : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := fun l => hessC (φ l) z with hH
  constructor
  · intro k
    have hj : ∀ j, dz j (fun y => hessCof φ y j k) z = ∑ i, mdisc (Function.update
        (Function.update (Fin.cons 0 H) 0 (Matrix.single j k 1)) i.succ
        ((1 / 2 : ℂ) • hessMat (T i (Pi.single j 1)) +
          (-(Complex.I / 2)) • hessMat (T i (Complex.I • Pi.single j 1)))) := by
      intro j
      obtain ⟨_, hD⟩ := hessCof_hasDeriv φ z hdiff j k
      rw [Fin.update_cons_zero]
      simp only [mdisc_update_comb, Finset.sum_add_distrib, ← Finset.mul_sum]
      show (fderiv ℝ _ z _ - Complex.I * fderiv ℝ _ z _) / 2 = _
      rw [hD, hD]; ring
    rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine mdisc_sum_row _ 0 i.succ (Fin.succ_ne_zero i).symm k _ fun j a b => ?_
    simp only [Matrix.add_apply, Matrix.smul_apply, hessMat_apply, smul_eq_mul]
    exact dzEntry_symm (T i) (third_fderiv_symm_one_two _ z (hφz i)) j a b
  · intro j
    have hk : ∀ k, dzb k (fun y => hessCof φ y j k) z = ∑ i, mdisc (Function.update
        (Function.update (Fin.cons 0 H) 0 (Matrix.single j k 1)) i.succ
        ((1 / 2 : ℂ) • hessMat (T i (Pi.single k 1)) +
          (Complex.I / 2) • hessMat (T i (Complex.I • Pi.single k 1)))) := by
      intro k
      obtain ⟨_, hD⟩ := hessCof_hasDeriv φ z hdiff j k
      rw [Fin.update_cons_zero]
      simp only [mdisc_update_comb, Finset.sum_add_distrib, ← Finset.mul_sum]
      show (fderiv ℝ _ z _ + Complex.I * fderiv ℝ _ z _) / 2 = _
      rw [hD, hD]; ring
    rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine mdisc_sum_col _ 0 i.succ (Fin.succ_ne_zero i).symm j _ fun k a b => ?_
    simp only [Matrix.add_apply, Matrix.smul_apply, hessMat_apply, smul_eq_mul]
    refine dzbEntry_symm (T i) (fun u x y => ?_) k a b
    rw [third_fderiv_symm_one_two _ z (hφz i), third_fderiv_symm_two_three _ z (hφz i), third_fderiv_symm_one_two _ z (hφz i)]

section DzCalc

variable {D : ℕ} {j : Fin D} {f g : (Fin D → ℂ) → ℂ} {z : Fin D → ℂ}

theorem dz_congr (h : f =ᶠ[𝓝 z] g) : dz j f z = dz j g z := by
  have e : fderiv ℝ f z = fderiv ℝ g z := Filter.EventuallyEq.fderiv_eq h
  unfold dz
  rw [e]

theorem dzb_congr (h : f =ᶠ[𝓝 z] g) : dzb j f z = dzb j g z := by
  have e : fderiv ℝ f z = fderiv ℝ g z := Filter.EventuallyEq.fderiv_eq h
  unfold dzb
  rw [e]

theorem dz_add (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dz j (fun y => f y + g y) z = dz j f z + dz j g z := by
  have e : fderiv ℝ (fun y => f y + g y) z = fderiv ℝ f z + fderiv ℝ g z := by
    first
    | (exact (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv)
    | (exact (hf.hasFDerivAt.fun_add hg.hasFDerivAt).fderiv)
    | (exact fderiv_add hf hg)
    | (exact fderiv_fun_add hf hg)
  unfold dz
  rw [e, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
  ring

theorem dz_mul (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dz j (fun y => f y * g y) z = dz j f z * g z + f z * dz j g z := by
  have e : fderiv ℝ (fun y => f y * g y) z = f z • fderiv ℝ g z + g z • fderiv ℝ f z := by
    first
    | (exact (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv)
    | (exact (hf.hasFDerivAt.fun_mul hg.hasFDerivAt).fderiv)
    | (exact fderiv_mul hf hg)
    | (exact fderiv_fun_mul hf hg)
  unfold dz
  rw [e]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem dz_of_eventually_zero (h : f =ᶠ[𝓝 z] fun _ => 0) : dz j f z = 0 := by
  rw [dz_congr h]
  unfold dz
  simp

theorem dzb_of_eventually_zero (h : f =ᶠ[𝓝 z] fun _ => 0) : dzb j f z = 0 := by
  rw [dzb_congr h]
  unfold dzb
  simp

theorem differentiableAt_dzb (hf : ContDiffAt ℝ 2 f z) : DifferentiableAt ℝ (dzb j f) z := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by first | norm_num | simp | rfl)).differentiableAt (by first | norm_num | simp | exact one_ne_zero)
  have h1 : DifferentiableAt ℝ (fun y => fderiv ℝ f y (Pi.single j 1)) z :=
    hd.clm_apply (differentiableAt_const _)
  have h2 : DifferentiableAt ℝ (fun y => fderiv ℝ f y (Complex.I • Pi.single j 1)) z :=
    hd.clm_apply (differentiableAt_const _)
  have h3 : DifferentiableAt ℝ (fun y => Complex.I * fderiv ℝ f y (Complex.I • Pi.single j 1)) z :=
    (differentiableAt_const _).mul h2
  have h4 : DifferentiableAt ℝ (fun y => fderiv ℝ f y (Pi.single j 1) +
      Complex.I * fderiv ℝ f y (Complex.I • Pi.single j 1)) z := h1.add h3
  have h5 : DifferentiableAt ℝ (fun y => (fderiv ℝ f y (Pi.single j 1) +
      Complex.I * fderiv ℝ f y (Complex.I • Pi.single j 1)) / 2) z := by
    first
      | (exact h4.div_const (2 : ℂ))
      | (simpa only [div_eq_mul_inv] using h4.mul_const (2⁻¹ : ℂ))
      | (fun_prop)
  exact h5

end DzCalc

private lemma sum_superset_neg_one_pow_fin_eq_ite_univ (N : ℕ) (T : Finset (Fin N)) :
    ∑ S : Finset (Fin N), (if T ⊆ S then (-1 : ℂ) ^ (N - S.card) else 0) =
      if T = Finset.univ then 1 else 0 := by
  rw [← (Equiv.mk (compl : Finset (Fin N) → Finset (Fin N)) compl compl_compl
    compl_compl).sum_comp]
  simp only [Equiv.coe_fn_mk]
  have hc : ∀ S : Finset (Fin N), N - Sᶜ.card = S.card := by
    intro S
    have h1 := Finset.card_le_univ S
    rw [Fintype.card_fin] at h1
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  have hsub : ∀ S : Finset (Fin N), (T ⊆ Sᶜ) ↔ (S ⊆ Tᶜ) := fun S => by
    constructor
    · intro h x hx
      rw [Finset.mem_compl]
      intro hxT
      exact (Finset.mem_compl.mp (h hxT)) hx
    · intro h x hx
      rw [Finset.mem_compl]
      intro hxS
      exact (Finset.mem_compl.mp (h hxS)) hx
  simp only [hc, hsub]
  rw [← Finset.sum_filter]
  have hf : Finset.univ.filter (fun S : Finset (Fin N) => S ⊆ Tᶜ) = Tᶜ.powerset := by
    ext S; simp
  rw [hf]
  have h0 : (∑ m ∈ Tᶜ.powerset, (-1 : ℤ) ^ m.card) = if Tᶜ = ∅ then 1 else 0 :=
    Finset.sum_powerset_neg_one_pow_card
  have h1 : (∑ m ∈ Tᶜ.powerset, (-1 : ℂ) ^ m.card) =
      ((∑ m ∈ Tᶜ.powerset, (-1 : ℤ) ^ m.card : ℤ) : ℂ) := by simp
  rw [h1, h0]
  by_cases hT : T = Finset.univ
  · have h2 : Tᶜ = ∅ := by rw [hT]; simp
    simp [h2, hT]
  · have h2 : Tᶜ ≠ ∅ := by
      intro h
      apply hT
      ext x
      simp only [Finset.mem_univ, iff_true]
      by_contra hx
      have hx' : x ∈ Tᶜ := Finset.mem_compl.mpr hx
      rw [h] at hx'
      simp at hx'
    simp [h2, hT]

private lemma mdisc_eq_inv_factorial_mul_sum_sign_prod {N : ℕ} (M : Fin N → Matrix (Fin N) (Fin N) ℂ) :
    mdisc M = (1 / (N.factorial : ℂ)) * ∑ σ : Equiv.Perm (Fin N), ∑ f : Fin N → Fin N,
      (if Finset.univ.image f = Finset.univ then
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (f i) (σ i) i else 0) := by
  unfold mdisc
  congr 1
  have hdet : ∀ S : Finset (Fin N), (∑ k ∈ S, M k).det =
      ∑ σ : Equiv.Perm (Fin N), ∑ f : Fin N → Fin N,
        (if ∀ i, f i ∈ S then ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (f i) (σ i) i else 0) := by
    intro S
    rw [Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hpf : Fintype.piFinset (fun _ : Fin N => S) =
        Finset.univ.filter (fun f : Fin N → Fin N => ∀ i, f i ∈ S) := by
      ext f; simp [Fintype.mem_piFinset]
    have hp : ∏ i, (∑ k ∈ S, M k) (σ i) i =
        ∑ f ∈ Fintype.piFinset (fun _ : Fin N => S), ∏ i, M (f i) (σ i) i := by
      simp only [Matrix.sum_apply]
      rw [Finset.prod_univ_sum]
    rw [hp, hpf, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [mul_ite, mul_zero]
  simp only [hdet, Finset.mul_sum]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Finset (Fin N))))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Finset (Fin N))))]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hiff : ∀ S : Finset (Fin N), (∀ i, f i ∈ S) ↔ Finset.univ.image f ⊆ S := fun S => by
    simp [Finset.image_subset_iff]
  have hS : ∀ S : Finset (Fin N), (-1 : ℂ) ^ (N - S.card) *
      (if ∀ i, f i ∈ S then ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (f i) (σ i) i else 0) =
      (if Finset.univ.image f ⊆ S then (-1 : ℂ) ^ (N - S.card) else 0) *
        (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (f i) (σ i) i) := by
    intro S
    by_cases h : ∀ i, f i ∈ S
    · rw [if_pos h, if_pos ((hiff S).mp h)]
    · rw [if_neg h, if_neg (fun h' => h ((hiff S).mpr h')), mul_zero, zero_mul]
  rw [Finset.sum_congr rfl fun S _ => hS S, ← Finset.sum_mul, sum_superset_neg_one_pow_fin_eq_ite_univ]
  split_ifs <;> simp

private lemma prod_cons_eq_sum_mul_prod_cons_single {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (σ : Equiv.Perm (Fin (n + 1)))
    (f : Fin (n + 1) → Fin (n + 1)) (hf : Finset.univ.image f = Finset.univ) :
    ∏ i, (Fin.cons A B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i =
      ∑ j, ∑ k, A j k * ∏ i, (Fin.cons (Matrix.single j k 1) B :
        Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i := by
  have hs : Function.Surjective f := fun y => by
    have hy : y ∈ Finset.univ.image f := by rw [hf]; exact Finset.mem_univ y
    simpa using hy
  have hi : Function.Injective f := Finite.injective_iff_surjective.mpr hs
  obtain ⟨i0, hi0⟩ := hs 0
  have hne : ∀ i ∈ Finset.univ.erase i0, f i ≠ 0 := fun i hi' h =>
    (Finset.mem_erase.mp hi').1 (hi (h.trans hi0.symm))
  have hrest : ∀ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      ∏ i ∈ Finset.univ.erase i0,
        (Fin.cons X B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i =
      ∏ i ∈ Finset.univ.erase i0,
        (Fin.cons 0 B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i := by
    intro X
    refine Finset.prod_congr rfl fun i hi' => ?_
    obtain ⟨m, hm⟩ := Fin.exists_succ_eq.mpr (hne i hi')
    rw [← hm, Fin.cons_succ, Fin.cons_succ]
  have hsplit : ∀ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      ∏ i, (Fin.cons X B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i =
        X (σ i0) i0 * ∏ i ∈ Finset.univ.erase i0,
          (Fin.cons 0 B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i := by
    intro X
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0), hrest X, hi0, Fin.cons_zero]
  simp only [hsplit]
  simp only [← mul_assoc, ← Finset.sum_mul]
  congr 1
  simp only [Matrix.single_apply]
  first
    | (rw [Finset.sum_eq_single (σ i0) (fun x _ hx => by simp [hx]) (by simp)]
       rw [Finset.sum_eq_single i0 (fun x _ hx => by simp [hx]) (by simp)]
       simp)
    | (simp [ite_and])
    | (simp [ite_and, Finset.sum_ite_eq', Finset.sum_ite_eq])

theorem mixedDisc_cons_eq_sum {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons A B) = ∑ j, ∑ k, A j k * mixedCof B j k := by
  have e1 : ∀ g : Fin (n + 1) → Fin (n + 1) → Equiv.Perm (Fin (n + 1)) →
      (Fin (n + 1) → Fin (n + 1)) → ℂ,
      ∑ j, ∑ k, ∑ σ, ∑ f, g j k σ f = ∑ σ, ∑ f, ∑ j, ∑ k, g j k σ f := by
    intro g
    calc ∑ j, ∑ k, ∑ σ, ∑ f, g j k σ f = ∑ j, ∑ σ, ∑ k, ∑ f, g j k σ f :=
          Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ σ, ∑ j, ∑ k, ∑ f, g j k σ f := Finset.sum_comm
      _ = ∑ σ, ∑ j, ∑ f, ∑ k, g j k σ f :=
          Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ σ, ∑ f, ∑ j, ∑ k, g j k σ f := Finset.sum_congr rfl fun σ _ => Finset.sum_comm
  have ht : ∀ (σ : Equiv.Perm (Fin (n + 1))) (f : Fin (n + 1) → Fin (n + 1)),
      (if Finset.univ.image f = Finset.univ then ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ i, (Fin.cons A B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i
        else 0) =
      ∑ j, ∑ k, A j k * (if Finset.univ.image f = Finset.univ then
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, (Fin.cons (Matrix.single j k 1) B :
          Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i else 0) := by
    intro σ f
    by_cases hf : Finset.univ.image f = Finset.univ
    · simp only [if_pos hf]
      rw [prod_cons_eq_sum_mul_prod_cons_single A B σ f hf, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    · simp [if_neg hf]
  rw [mdisc_eq_inv_factorial_mul_sum_sign_prod]
  simp only [mixedCof, mdisc_eq_inv_factorial_mul_sum_sign_prod]
  simp only [ht]
  simp only [Finset.mul_sum, e1]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun f _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem maDens_cons_eq {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (v : (Fin (n + 1) → ℂ) → ℝ)
    (z : Fin (n + 1) → ℂ) :
    maDens (Fin.cons v φ) z = ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) *
      (mdisc (Fin.cons (hessC v z) fun i => hessC (φ i) z)).re := by
  have e : (fun k => hessC ((Fin.cons v φ : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) k) z) =
      Fin.cons (hessC v z) fun i => hessC (φ i) z := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k <;> simp
  rw [maDens, e]

theorem monge_ampere_density_cofactor : MaDensCofStatement := by
  intro n φ v U hU hv z hz
  have hs : ∀ j k : Fin (n + 1), hessC v z j k = dz j (dzb k (cplx v)) z := by
    intro j k
    have hv2 : ContDiffAt ℝ 2 v z := hv.contDiffAt (hU.mem_nhds hz)
    have hDv : DifferentiableAt ℝ (fderiv ℝ v) z :=
      (hv2.fderiv_right (m := 1) (by first | norm_num | simp | rfl)).differentiableAt (by first | norm_num | simp | exact one_ne_zero)
    have hw : ∀ w : Fin (n + 1) → ℂ, HasFDerivAt (fun y => ((fderiv ℝ v y w : ℝ) : ℂ))
        (Complex.ofRealCLM.comp
          ((ContinuousLinearMap.apply ℝ ℝ w).comp (fderiv ℝ (fderiv ℝ v) z))) z :=
      fun w => Complex.ofRealCLM.hasFDerivAt.comp z
        ((ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp z hDv.hasFDerivAt)
    have hg : HasFDerivAt (fun y => (1 / 2 : ℂ) * (((fderiv ℝ v y (Pi.single k 1) : ℝ) : ℂ) +
        Complex.I * ((fderiv ℝ v y (Complex.I • Pi.single k 1) : ℝ) : ℂ)))
        ((1 / 2 : ℂ) • (Complex.ofRealCLM.comp ((ContinuousLinearMap.apply ℝ ℝ (Pi.single k 1)).comp
            (fderiv ℝ (fderiv ℝ v) z)) +
          Complex.I • Complex.ofRealCLM.comp
            ((ContinuousLinearMap.apply ℝ ℝ (Complex.I • Pi.single k 1)).comp
              (fderiv ℝ (fderiv ℝ v) z)))) z := by
      first
        | (exact ((hw _).add ((hw _).const_mul Complex.I)).const_mul (1 / 2 : ℂ))
        | (exact ((hw _).fun_add ((hw _).const_mul Complex.I)).const_mul (1 / 2 : ℂ))
        | (exact ((hw _).add ((hw _).fun_const_mul Complex.I)).fun_const_mul (1 / 2 : ℂ))
        | (exact ((hw _).fun_add ((hw _).fun_const_mul Complex.I)).fun_const_mul (1 / 2 : ℂ))
    have heq : dzb k (cplx v) =ᶠ[𝓝 z] fun y => (1 / 2 : ℂ) *
        (((fderiv ℝ v y (Pi.single k 1) : ℝ) : ℂ) +
          Complex.I * ((fderiv ℝ v y (Complex.I • Pi.single k 1) : ℝ) : ℂ)) := by
      filter_upwards [hU.mem_nhds hz] with y hy
      have hdy : DifferentiableAt ℝ v y :=
        (hv.contDiffAt (hU.mem_nhds hy)).differentiableAt (by first | norm_num | simp | exact one_ne_zero)
      have hf : fderiv ℝ (cplx v) y = Complex.ofRealCLM.comp (fderiv ℝ v y) :=
        (Complex.ofRealCLM.hasFDerivAt.comp y hdy.hasFDerivAt).fderiv
      unfold dzb
      rw [hf]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, Complex.ofRealCLM_apply]
      ring
    rw [dz_congr heq]
    unfold dz
    rw [hg.fderiv]
    simp only [hessC, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.apply_apply,
      Complex.ofRealCLM_apply, smul_eq_mul]
    push_cast
    linear_combination ((fderiv ℝ (fderiv ℝ v) z (Complex.I • Pi.single j 1)
      (Complex.I • Pi.single k 1) : ℝ) : ℂ) / 4 * Complex.I_sq
  rw [maDens_cons_eq, mixedDisc_cons_eq_sum]
  have hsum : (∑ j, ∑ k, hessC v z j k * mixedCof (fun i => hessC (φ i) z) j k) =
      ∑ j, ∑ k, hessCof φ z j k * dz j (dzb k (cplx v)) z := by
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hs j k]
    simp only [hessCof]
    ring
  rw [hsum]

end

end ReciprocityTheory.AnForm.A
