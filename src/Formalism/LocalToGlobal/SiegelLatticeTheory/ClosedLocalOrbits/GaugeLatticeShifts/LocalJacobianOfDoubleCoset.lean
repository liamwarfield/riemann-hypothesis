module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IsClosedSLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SigmaFiniteOfB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.MulVecMapMem

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.BigCellMulVecWb
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

theorem bigMem_holds : BigMem := Formalism.QuantumDeterminants.bigCellMem

theorem hJ_P {n : ℕ} {ε : Fin n → Bool} {P H : Matrix (Fin n) (Fin n) ℂ} (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = H)
    (x y : Fin n → ℂ) : hJ ε (P *ᵥ x) (P *ᵥ y) = Formalism.QuantumDeterminants.herm H y x := by
  unfold hJ Formalism.QuantumDeterminants.herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hPJ]

theorem hJ_smul_l {n : ℕ} (ε : Fin n → Bool) (a : ℂ) (x y : Fin n → ℂ) : hJ ε (a • x) y = conj a * hJ ε x y := by
  unfold hJ
  rw [star_smul, smul_dotProduct, smul_eq_mul, Complex.star_def]

theorem hJ_smul_r {n : ℕ} (ε : Fin n → Bool) (a : ℂ) (x y : Fin n → ℂ) : hJ ε x (a • y) = a * hJ ε x y := by
  unfold hJ
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem fam_eq {r k : ℕ} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {e : Fin r → Fin (2 * r + k + 1) → ℂ} {z zH : Fin (2 * r + k + 1) → ℂ}
    (hPe : ∀ a, P *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) = e a) (hPz : P *ᵥ zH = z) (a : Fin (r + 1)) :
    fam e z a = P *ᵥ Formalism.QuantumDeterminants.fvec k r zH a := by
  unfold fam Formalism.QuantumDeterminants.fvec
  split_ifs with h
  · have ha : a = Fin.castSucc ⟨a.val, h⟩ := Fin.ext rfl
    conv_lhs => rw [ha]
    rw [Fin.snoc_castSucc]
    exact (hPe _).symm
  · have ha : a = Fin.last r := Fin.ext (by have := a.2; simp only [Fin.val_last]; omega)
    subst ha
    rw [Fin.snoc_last]
    exact hPz.symm

theorem bigCell_mulVec_wb {k r : ℕ} (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    {w : Fin (2 * r + k + 1) → ℂ} (hw : Formalism.QuantumDeterminants.inWb k r w) :
    Formalism.QuantumDeterminants.bigCell k r c μ *ᵥ w = Formalism.FourierDecayAlt.B2.embWb k r μ *ᵥ w := by
  ext i
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
  · have hj1 : ¬ j.val < r := by omega
    unfold Formalism.QuantumDeterminants.bigCell Formalism.FourierDecayAlt.B2.embWb
    rw [dite_eq_right hj1, dite_eq_left hj.2]
    by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · rw [dite_eq_left hi, dite_eq_left ⟨hi, hj⟩]
    · rw [dite_eq_right hi, dite_eq_right (fun h => hi h.1),
        if_neg (fun (h : i = j ∧ ¬(r ≤ i.val ∧ i.val ≤ r + k)) => hi (by rw [h.1]; exact hj))]
  · rw [hw j (by omega)]
    simp

theorem conj_scinv (sc : ℝ) (m : ℕ) : conj (((sc : ℂ) ^ m)⁻¹) = ((sc : ℂ) ^ m)⁻¹ := by
  simp [map_inv₀, map_pow]

theorem zBig : ZBig := by
  intro r k ε e z z' zH zH' P sc hPJ hPdet hPe hzH hzH' hPz hPz' hsc μsec hsec q hq hζ
  have hU : (μsec q.2)ᴴ * Formalism.QuantumDeterminants.Hb k * μsec q.2 = Formalism.QuantumDeterminants.Hb k := (hsec.2 q.2 hζ).1
  refine ⟨inUJ_conj hPJ hPdet (bigMem_holds k r q.1 _ hq hU), ?_⟩
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPdet
  have hB : ∀ y, (P * Formalism.QuantumDeterminants.bigCell k r q.1 (μsec q.2) * P⁻¹) *ᵥ (P *ᵥ y) =
      P *ᵥ (Formalism.QuantumDeterminants.bigCell k r q.1 (μsec q.2) *ᵥ y) := by
    intro y
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one, ← Matrix.mulVec_mulVec]
  have hlast : Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.bigCell k r q.1 (μsec q.2) *ᵥ zH') zH = q.2 := by
    have h1W : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ Formalism.QuantumDeterminants.UWset k r zH := by
      refine ⟨by simp [Formalism.QuantumDeterminants.UH], fun a => by simp, by simp⟩
    have h1W' : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ Formalism.QuantumDeterminants.UWset k r zH' := by
      refine ⟨by simp [Formalism.QuantumDeterminants.UH], fun a => by simp, by simp⟩
    have := (Formalism.FourierDecayAlt.P.b2_rank_one_mem k r zH zH' μsec hzH hzH' hsec q.2 hζ 1 h1W 1 h1W').2
    rw [inv_one, Matrix.one_mul, Matrix.mul_one] at this
    rw [bigCell_mulVec_wb q.1 _ hzH']
    exact this
  have hZ := Formalism.QuantumDeterminants.bigCellZhat k r zH zH' q.1 (μsec q.2) hzH hzH'
  ext a b
  simp only [Zhat, famSc]
  rw [Matrix.mulVec_smul, hJ_smul_l, hJ_smul_r, fam_eq hPe hPz a, fam_eq hPe hPz' b, hB, hJ_P hPJ]
  have hZab := congrFun (congrFun hZ a) b
  simp only [Formalism.QuantumDeterminants.Zhat] at hZab
  rw [hZab, conj_scinv]
  by_cases hab : a = b
  · subst hab
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    by_cases ha : a.val < r
    · rw [dite_eq_left ha]
      have ha' : a = Fin.castSucc ⟨a.val, ha⟩ := Fin.ext rfl
      conv_rhs => rw [ha']
      unfold coordSc
      rw [Fin.snoc_castSucc]
      ring
    · rw [dite_eq_right ha, hlast]
      have ha' : a = Fin.last r := Fin.ext (by have := a.2; simp only [Fin.val_last]; omega)
      subst ha'
      unfold coordSc
      rw [Fin.snoc_last]
      simp
  · rw [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ hab]
    ring

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProdIccRange
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.CoordinateScalingProducts

open Formalism.L2.SG.RealObj

theorem prod_Icc_range (y : ℕ → ℝ) : ∀ r : ℕ,
    ∏ l ∈ Finset.Icc 1 r, ∏ i ∈ Finset.range l, y i = ∏ i ∈ Finset.range r, y i ^ (r - i)
  | 0 => by simp
  | r + 1 => by
    rw [Finset.prod_Icc_succ_top (by omega), prod_Icc_range y r,
      Finset.prod_range_succ (fun i => y i ^ (r + 1 - i)) r, Finset.prod_range_succ y r]
    have h : ∀ i ∈ Finset.range r, y i ^ (r + 1 - i) = y i ^ (r - i) * y i := fun i hi => by
      have hi' := Finset.mem_range.1 hi
      rw [show r + 1 - i = (r - i) + 1 by omega, pow_succ]
    have hp : (∏ i ∈ Finset.range r, y i ^ (r + 1 - i)) =
        (∏ i ∈ Finset.range r, y i ^ (r - i)) * (∏ i ∈ Finset.range r, y i) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl h
    rw [hp, show r + 1 - r = 1 by omega, pow_one, mul_assoc]

def lam (r : ℕ) (sc : ℝ) (a : Fin r) : ℂ := (((sc : ℂ) ^ (r - a.1))⁻¹) ^ 2

theorem coordSc_cs {r : ℕ} (sc : ℝ) (q : (Fin r → ℂ) × ℂ) (a : Fin r) :
    coordSc r sc q a.castSucc = lam r sc a * q.1 a := by
  simp [coordSc, lam]

theorem coordSc_last {r : ℕ} (sc : ℝ) (q : (Fin r → ℂ) × ℂ) : coordSc r sc q (Fin.last r) = q.2 := by
  simp [coordSc]

theorem dl_diag {r : ℕ} (c : Fin (r + 1) → ℂ) (l : ℕ) (hl : l ≤ r + 1) :
    Dl (Matrix.diagonal c) l = ∏ i : Fin l, c (Fin.castLE hl i) := by
  rw [Dl, dif_pos hl, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hl), Matrix.det_diagonal]
  rfl

theorem gv_cs {r : ℕ} (T T' sc : ℝ) (q : (Fin r → ℂ) × ℂ) :
    Gv T T' (Matrix.diagonal (coordSc r sc q)) =
      (∏ a : Fin r, ‖lam r sc a * q.1 a‖ ^ 2) * (Complex.normSq q.2 - T * T') := by
  have h1 : ∀ i : Fin (r + 1), Fin.castLE le_rfl i = i := fun i => Fin.ext rfl
  have h2 : ∀ i : Fin r, Fin.castLE (Nat.le_succ r) i = i.castSucc := fun i => Fin.ext rfl
  rw [Gv, dl_diag _ (r + 1) le_rfl, dl_diag _ r (Nat.le_succ r)]
  simp only [h1, h2]
  rw [Fin.prod_univ_castSucc, coordSc_last]
  simp only [coordSc_cs]
  rw [norm_mul, norm_prod, Complex.normSq_eq_norm_sq, Finset.prod_pow]
  ring

theorem jac_cs {r : ℕ} (sc : ℝ) (q : (Fin r → ℂ) × ℂ) :
    JacV (Matrix.diagonal (coordSc r sc q)) = ∏ a : Fin r, (‖lam r sc a * q.1 a‖ ^ 4) ^ (r - a.1) := by
  let y : ℕ → ℝ := fun i => if h : i < r then ‖lam r sc ⟨i, h⟩ * q.1 ⟨i, h⟩‖ ^ 4 else 0
  have hl : ∀ l ∈ Finset.Icc 1 r,
      modC (Dl (Matrix.diagonal (coordSc r sc q)) l) ^ 2 = ∏ i ∈ Finset.range l, y i := by
    intro l hl
    have hlr : l ≤ r := (Finset.mem_Icc.1 hl).2
    have hl1 : l ≤ r + 1 := by omega
    rw [dl_diag _ l hl1, modC, norm_prod, ← Finset.prod_pow, ← Finset.prod_pow,
      ← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi : i.1 < r := lt_of_lt_of_le i.2 hlr
    have hc : Fin.castLE hl1 i = (⟨i.1, hi⟩ : Fin r).castSucc := Fin.ext rfl
    rw [hc, coordSc_cs]
    simp only [y, dif_pos hi]
    ring
  rw [JacV, Finset.prod_congr rfl hl, prod_Icc_range y r,
    ← Fin.prod_univ_eq_prod_range (fun i => y i ^ (r - i)) r]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp only [y, dif_pos a.2]

def lamW (r k : ℕ) (sc : ℝ) : ℝ := ∏ a : Fin r, ‖lam r sc a‖ ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2))

theorem wt_cs {r k : ℕ} (hk : 1 ≤ k) (T T' sc : ℝ) (q : (Fin r → ℂ) × ℂ) :
    wtLoc k T T' (coordSc r sc q) = lamW r k sc *
      ((∏ a : Fin r, ‖q.1 a‖ ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2))) * (Complex.normSq q.2 - T * T') ^ (k - 1)) := by
  rw [wtLoc, gv_cs, jac_cs, lamW, mul_pow, ← Finset.prod_pow]
  have h : ∀ a ∈ (Finset.univ : Finset (Fin r)),
      (‖lam r sc a * q.1 a‖ ^ 2) ^ (k - 1) * (‖lam r sc a * q.1 a‖ ^ 4) ^ (r - a.1) =
        ‖lam r sc a‖ ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2)) * ‖q.1 a‖ ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2)) := by
    intro a _
    have e : 2 * (Formalism.QuantumDeterminants.Mdim k r a - 2) = 2 * (k - 1) + 4 * (r - a.1) := by
      unfold Formalism.QuantumDeterminants.Mdim
      omega
    rw [e, norm_mul]
    ring
  have hp := Finset.prod_congr rfl h
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib] at hp
  linear_combination (Complex.normSq q.2 - T * T') ^ (k - 1) * hp

def Gi (r k : ℕ) (T T' : ℝ) (F : (Fin (r + 1) → ℂ) → ℝ≥0∞) : (Fin (r + 1) → ℂ) → ℝ≥0∞ :=
  (GoodLoc (r := r) T T').indicator fun c => ENNReal.ofReal (wtLoc k T T' c) * F c

def nrm (r : ℕ) (sc : ℝ) : ℝ := Complex.normSq (∏ a, lam r sc a)

theorem lam_ne {r : ℕ} {sc : ℝ} (hsc : 0 < sc) (a : Fin r) : lam r sc a ≠ 0 := by
  unfold lam
  exact pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ (by exact_mod_cast hsc.ne')))

def Lsc (r : ℕ) (sc : ℝ) (hsc : 0 < sc) : (Fin r → ℂ) ≃ᵐ (Fin r → ℂ) where
  toFun v a := lam r sc a * v a
  invFun v a := (lam r sc a)⁻¹ * v a
  left_inv v := funext fun a => inv_mul_cancel_left₀ (lam_ne hsc a) (v a)
  right_inv v := funext fun a => mul_inv_cancel_left₀ (lam_ne hsc a) (v a)
  measurable_toFun := by
    show Measurable fun v : Fin r → ℂ => fun a => lam r sc a * v a
    fun_prop
  measurable_invFun := by
    show Measurable fun v : Fin r → ℂ => fun a => (lam r sc a)⁻¹ * v a
    fun_prop

def Phe (r : ℕ) (sc : ℝ) (hsc : 0 < sc) : ((Fin r → ℂ) × ℂ) ≃ᵐ (Fin (r + 1) → ℂ) :=
  ((MeasurableEquiv.prodCongr (Lsc r sc hsc) (MeasurableEquiv.refl ℂ)).trans MeasurableEquiv.prodComm).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => ℂ) (Fin.last r)).symm

theorem phe_apply {r : ℕ} {sc : ℝ} (hsc : 0 < sc) (q : (Fin r → ℂ) × ℂ) : Phe r sc hsc q = coordSc r sc q := by
  funext i
  simp [Phe, Lsc, coordSc, MeasurableEquiv.piFinSuccAbove_symm_apply, lam]
  rfl

theorem map_Lsc {r : ℕ} {sc : ℝ} (hsc : 0 < sc) :
    (volume : Measure (Fin r → ℂ)).map (Lsc r sc hsc) = ENNReal.ofReal (nrm r sc)⁻¹ • volume := by
  have hnrm : 0 < nrm r sc :=
    Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => lam_ne hsc a)
  let f : (Fin r → ℂ) →ₗ[ℝ] (Fin r → ℂ) :=
    LinearMap.pi fun a => (Algebra.lmul ℝ ℂ (lam r sc a)).comp (LinearMap.proj a)
  have hf : ⇑(Lsc r sc hsc) = ⇑f := by
    funext v
    rfl
  have hdet : LinearMap.det f = nrm r sc := by
    rw [LinearMap.det_pi]
    simp_rw [← Algebra.norm_apply, Algebra.norm_complex_apply]
    rw [nrm, map_prod]
  rw [hf, Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; exact hnrm.ne'), hdet,
    abs_of_pos (inv_pos.2 hnrm)]

theorem map_Phe {r : ℕ} {sc : ℝ} (hsc : 0 < sc) :
    (volume : Measure ((Fin r → ℂ) × ℂ)).map (Phe r sc hsc) = ENNReal.ofReal (nrm r sc)⁻¹ • volume := by
  have e1 : (volume : Measure ((Fin r → ℂ) × ℂ)).map
      (MeasurableEquiv.prodCongr (Lsc r sc hsc) (MeasurableEquiv.refl ℂ)) =
        ENNReal.ofReal (nrm r sc)⁻¹ • volume := by
    have hc : ⇑(MeasurableEquiv.prodCongr (Lsc r sc hsc) (MeasurableEquiv.refl ℂ)) =
        Prod.map (Lsc r sc hsc) id := rfl
    rw [Measure.volume_eq_prod, hc, ← Measure.map_prod_map _ _ (Lsc r sc hsc).measurable measurable_id,
      map_Lsc hsc, Measure.map_id, Measure.prod_smul_left]
  have e2 := Measure.measurePreserving_swap (μ := (volume : Measure (Fin r → ℂ))) (ν := (volume : Measure ℂ))
  have e3 := (measurePreserving_piFinSuccAbove (fun _ : Fin (r + 1) => (volume : Measure ℂ)) (Fin.last r)).symm
  have hs : ⇑(MeasurableEquiv.prodComm : ((Fin r → ℂ) × ℂ) ≃ᵐ (ℂ × (Fin r → ℂ))) = Prod.swap := rfl
  unfold Phe
  rw [MeasurableEquiv.coe_trans, MeasurableEquiv.coe_trans, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (by fun_prop) (by fun_prop), e1, hs,
    Measure.map_smul _ e2.measurable.aemeasurable, Measure.map_smul _ e3.measurable.aemeasurable,
    Measure.volume_eq_prod, e2.map_eq]
  congr 1
  exact e3.map_eq

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.CoordinateScalingProducts

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj CoordinateScalingProducts

private theorem dcLoc_eq_formula (r : ℕ) :
    dcLoc (r := r) = (2 : ℝ≥0∞) ^ (r + 1) • (volume : Measure (Fin (r + 1) → ℂ)) := by
  unfold dcLoc
  have : SigmaFinite ((2 : ℝ≥0∞) • (volume : Measure ℂ)) := by
    have h2 : (2 : ℝ≥0∞) = ((2 : NNReal) : ℝ≥0∞) := rfl
    rw [h2, ← ENNReal.smul_def]
    infer_instance
  refine Measure.pi_eq fun s _ => ?_
  rw [Measure.smul_apply, volume_pi, Measure.pi_pi, smul_eq_mul]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

private theorem measurableSet_goodLoc' (r : ℕ) (T T' : ℝ) : MeasurableSet (GoodLoc (r := r) T T') := by
  have hc : Continuous fun c : Fin (r + 1) → ℂ => Gv T T' (Matrix.diagonal c) := by
    simp only [Gv, dl_diag _ (r + 1) le_rfl, dl_diag _ r (Nat.le_succ r)]
    fun_prop
  rw [GoodLoc, Set.ofPred_and, Set.ofPred_forall]
  refine (MeasurableSet.iInter fun l => ?_).inter (measurableSet_lt measurable_const hc.measurable)
  exact (measurable_pi_apply l) (measurableSet_singleton 0).compl

private theorem volume_normSq_snd_eq_const_eq_zero {r : ℕ} {T T' : ℝ} :
    (volume : Measure ((Fin r → ℂ) × ℂ)) {q | Complex.normSq q.2 = T * T'} = 0 := by
  have hS : {z : ℂ | Complex.normSq z = T * T'} ⊆ Metric.sphere 0 (Real.sqrt (T * T')) := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz
    rw [mem_sphere_zero_iff_norm, ← hz, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have h0 : (volume : Measure ℂ) {z : ℂ | Complex.normSq z = T * T'} = 0 :=
    measure_mono_null hS (Measure.addHaar_sphere volume 0 _)
  have he : {q : (Fin r → ℂ) × ℂ | Complex.normSq q.2 = T * T'} =
      Set.univ ×ˢ {z : ℂ | Complex.normSq z = T * T'} := by
    ext q
    simp
  rw [he, Measure.volume_eq_prod, Measure.prod_prod, h0, mul_zero]

theorem coordW_holds : CoordW := by
  intro r k T T' sc hk hT hT' hsc
  have hnrm : 0 < nrm r sc :=
    Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => lam_ne hsc a)
  have hlamW : 0 < lamW r k sc :=
    Finset.prod_pos fun a _ => pow_pos (norm_pos_iff.2 (lam_ne hsc a)) _
  have hTT : 0 < T * T' := mul_pos hT hT'
  set C : ℝ := 2 ^ (r + 1) * nrm r sc * lamW r k sc with hC
  have hCpos : 0 < C := by positivity
  refine ⟨C⁻¹, inv_pos.2 hCpos, fun F => ?_⟩
  have hae : (fun q => (GoodLoc (r := r) T T').indicator
      (fun c => ENNReal.ofReal (wtLoc k T T' c) * F c) (Phe r sc hsc q)) =ᵐ[volume]
      fun q => ENNReal.ofReal (lamW r k sc) *
        (ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) * F (coordSc r sc q)) := by
    have hq : ∀ᵐ q : (Fin r → ℂ) × ℂ ∂volume, Complex.normSq q.2 ≠ T * T' := by
      rw [ae_iff]
      simpa using volume_normSq_snd_eq_const_eq_zero (r := r) (T := T) (T' := T')
    filter_upwards [hq] with q hq
    rw [phe_apply]
    by_cases hg : coordSc r sc q ∈ GoodLoc (r := r) T T'
    · rw [Set.indicator_of_mem hg, wt_cs hk, ENNReal.ofReal_mul hlamW.le, mul_assoc]
      have hG := hg.2
      rw [gv_cs] at hG
      have hp : 0 ≤ ∏ a : Fin r, ‖lam r sc a * q.1 a‖ ^ 2 :=
        Finset.prod_nonneg fun _ _ => by positivity
      have hN : T * T' < Complex.normSq q.2 := by
        by_contra h
        rw [not_lt] at h
        have := mul_nonpos_of_nonneg_of_nonpos hp (by linarith : Complex.normSq q.2 - T * T' ≤ 0)
        linarith
      unfold Formalism.QuantumDeterminants.bcWeight
      rw [if_pos hN.le]
    · rw [Set.indicator_of_notMem hg]
      have hb : Formalism.QuantumDeterminants.bcWeight k r T T' q = 0 := by
        unfold Formalism.QuantumDeterminants.bcWeight
        split_ifs with hle
        · have hlt : T * T' < Complex.normSq q.2 := lt_of_le_of_ne hle (Ne.symm hq)
          by_cases hall : ∀ a, q.1 a ≠ 0
          · exfalso
            apply hg
            refine ⟨fun l => ?_, ?_⟩
            · induction l using Fin.lastCases with
              | last =>
                rw [coordSc_last]
                intro h0
                rw [h0, map_zero] at hlt
                linarith
              | cast a =>
                rw [coordSc_cs]
                exact mul_ne_zero (lam_ne hsc a) (hall a)
            · rw [gv_cs]
              exact mul_pos (Finset.prod_pos fun a _ =>
                pow_pos (norm_pos_iff.2 (mul_ne_zero (lam_ne hsc a) (hall a))) 2) (by linarith)
          · simp only [not_forall, not_not] at hall
            obtain ⟨a, ha⟩ := hall
            rw [Finset.prod_eq_zero (Finset.mem_univ a), zero_mul]
            rw [ha, norm_zero]
            apply zero_pow
            unfold Formalism.QuantumDeterminants.Mdim
            omega
        · rfl
      rw [hb]
      simp
  have key : ∫⁻ c in GoodLoc (r := r) T T', ENNReal.ofReal (wtLoc k T T' c) * F c ∂(dcLoc (r := r)) =
      ENNReal.ofReal C * ∫⁻ q : (Fin r → ℂ) × ℂ,
        ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) * F (coordSc r sc q) := by
    rw [dcLoc_eq_formula, Measure.restrict_smul, lintegral_smul_measure,
      ← lintegral_indicator (measurableSet_goodLoc' r T T')]
    have hvol : (volume : Measure (Fin (r + 1) → ℂ)) =
        ENNReal.ofReal (nrm r sc) • (volume.map (Phe r sc hsc)) := by
      rw [map_Phe hsc, smul_smul, ← ENNReal.ofReal_mul hnrm.le, mul_inv_cancel₀ hnrm.ne',
        ENNReal.ofReal_one, one_smul]
    rw [hvol, lintegral_smul_measure, lintegral_map_equiv, lintegral_congr_ae hae,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hC, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
    simp only [smul_eq_mul, ENNReal.ofReal_ofNat]
    ring
  rw [key, ← mul_assoc, ← ENNReal.ofReal_mul (inv_pos.2 hCpos).le, inv_mul_cancel₀ hCpos.ne',
    ENNReal.ofReal_one, one_mul]

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SecWbHolds
namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

theorem secWb_holds : SecWb := fun k r z z' hk hz hz' hT hT' =>
  Formalism.FourierDecayAlt.P.SettingConstruction.sectionExists k r z z' hk hz hz' hT hT'

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HpkExHolds
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarTranslationMeasurability

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

theorem meas_invM : Measurable (invM : Mt k r → Mt k r) := by
  unfold invM
  have hof : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
  have hc : Continuous fun x : Mt k r => ((Matrix.of x).adjugate : Mt k r) := hof.matrix_adjugate
  have hdc : Continuous fun x : Mt k r => (Matrix.of x : Mat k r).det := hof.matrix_det
  have hd : Measurable fun x : Mt k r => Ring.inverse (Matrix.of x : Mat k r).det := by
    simp only [Ring.inverse_eq_inv']
    exact hdc.measurable.inv
  have he : (fun x : Mt k r => (((Matrix.of x : Mat k r)⁻¹ : Mat k r) : Mt k r)) =
      fun x : Mt k r => (Ring.inverse (Matrix.of x).det • (Matrix.of x).adjugate : Mt k r) := by
    funext x
    rw [Matrix.inv_def]
  have hc' : Measurable fun x : Mt k r => ((Matrix.of x).adjugate : Mt k r) :=
    Measurable.of_eval fun i => Measurable.of_eval fun j =>
      ((continuous_apply j).comp ((continuous_apply i).comp hc)).measurable
  rw [he]
  exact hd.smul hc'

theorem meas_mulM : Measurable (mulM : Mt k r × Mt k r → Mt k r) := by
  unfold mulM
  have hc : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 * Matrix.of p.2 : Mat k r)) :=
    Continuous.matrix_mul continuous_fst continuous_snd
  exact Measurable.of_eval fun i => Measurable.of_eval fun j =>
    ((continuous_apply j).comp ((continuous_apply i).comp hc)).measurable

def Cm (g : Mt k r) (p : SS k r) : Mt k r := mulM (mulM (mulM (mulM (p.1.1, p.1.2), g), p.2.2), p.2.1)

def Tm (g : Mt k r) (p : Mt k r × Mt k r) : Mt k r := mulM (mulM (p.1, g), invM p.2)

theorem meas_Cm (g : Mt k r) : Measurable (Cm g) := by
  unfold Cm
  have hm := meas_mulM (k := k) (r := r)
  exact hm.comp ((hm.comp ((hm.comp ((hm.comp (measurable_fst.fst.prodMk measurable_fst.snd)).prodMk
    measurable_const)).prodMk measurable_snd.snd)).prodMk measurable_snd.fst)

theorem meas_Tm (g : Mt k r) : Measurable (Tm g) := by
  unfold Tm
  have hm := meas_mulM (k := k) (r := r)
  exact hm.comp ((hm.comp (measurable_fst.prodMk measurable_const)).prodMk (meas_invM.comp measurable_snd))

theorem tgt_eq (A B A' : Measure (Mt k r)) [SFinite A] [SFinite B] [SFinite A']
    (hB : B.map invM = B) (hA' : A'.map invM = A') (g : Mt k r) (φ : Mt k r → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ s, ∫⁻ s', φ (Tm g (s, s')) ∂(Formalism.MainNotions.S.muS A' B) ∂(Formalism.MainNotions.S.muS A B) =
      ∫⁻ p, φ (Cm g p) ∂((A.prod B).prod (A'.prod B)) := by
  have hm := meas_mulM (k := k) (r := r)
  have hi := meas_invM (k := k) (r := r)
  have hT := meas_Tm g
  have hmu : ∀ X Y : Measure (Mt k r), Formalism.MainNotions.S.muS X Y = (X.prod Y).map mulM := fun _ _ => rfl
  rw [hmu, hmu]
  have step1 : ∀ s, ∫⁻ s', φ (Tm g (s, s')) ∂((A'.prod B).map mulM) =
      ∫⁻ y, φ (Tm g (s, mulM y)) ∂(A'.prod B) := fun s =>
    lintegral_map (hφ.comp (hT.comp (measurable_const.prodMk measurable_id))) hm
  rw [lintegral_congr step1]
  have hH : Measurable fun s => ∫⁻ y, φ (Tm g (s, mulM y)) ∂(A'.prod B) :=
    Measurable.lintegral_prod_right' (f := fun q : Mt k r × (Mt k r × Mt k r) => φ (Tm g (q.1, mulM q.2)))
      (hφ.comp (hT.comp (measurable_fst.prodMk (hm.comp measurable_snd))))
  rw [lintegral_map hH hm]
  have hF : Measurable fun p : (Mt k r × Mt k r) × (Mt k r × Mt k r) => φ (Tm g (mulM p.1, mulM p.2)) :=
    hφ.comp (hT.comp ((hm.comp measurable_fst).prodMk (hm.comp measurable_snd)))
  rw [← lintegral_prod _ hF.aemeasurable]
  have hpt : ∀ p : (Mt k r × Mt k r) × (Mt k r × Mt k r),
      Tm g (mulM p.1, mulM p.2) = Cm g (Prod.map id (Prod.map invM invM) p) := by
    intro p
    show (Matrix.of p.1.1 * Matrix.of p.1.2 * Matrix.of g * (Matrix.of p.2.1 * Matrix.of p.2.2)⁻¹ : Mat k r) =
      Matrix.of p.1.1 * Matrix.of p.1.2 * Matrix.of g * (Matrix.of p.2.2)⁻¹ * (Matrix.of p.2.1)⁻¹
    rw [Matrix.mul_inv_rev]
    exact (mul_assoc _ _ _).symm
  simp only [hpt]
  have h2 : (A'.prod B).map (Prod.map invM invM) = A'.prod B := by
    rw [← Measure.map_prod_map A' B hi hi, hA', hB]
  have hP : ((A.prod B).prod (A'.prod B)).map (Prod.map id (Prod.map invM invM)) = (A.prod B).prod (A'.prod B) := by
    rw [← Measure.map_prod_map _ _ measurable_id (hi.prodMap hi), Measure.map_id, h2]
  refine (lintegral_map (f := φ ∘ Cm g) (hφ.comp (meas_Cm g)) (measurable_id.prodMap (hi.prodMap hi))).symm.trans ?_
  rw [hP]
  rfl

theorem src_eq (A B A' : Measure (Mt k r)) [SFinite A] [SFinite B] [SFinite A']
    (hA : A.map invM = A) (hB : B.map invM = B) (g : Mat k r) (φ : Mt k r → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ p, φ (sgs p g) ∂((A.prod B).prod (A'.prod B)) = ∫⁻ p, φ (Cm g p) ∂((A.prod B).prod (A'.prod B)) := by
  have hi := meas_invM (k := k) (r := r)
  have hpt : ∀ p : SS k r, (sgs p g : Mt k r) = Cm g (Prod.map (Prod.map invM invM) id p) := fun _ => rfl
  simp only [hpt]
  have h1 : (A.prod B).map (Prod.map invM invM) = A.prod B := by
    rw [← Measure.map_prod_map A B hi hi, hA, hB]
  have hP : ((A.prod B).prod (A'.prod B)).map (Prod.map (Prod.map invM invM) id) = (A.prod B).prod (A'.prod B) := by
    rw [← Measure.map_prod_map _ _ (hi.prodMap hi) measurable_id, Measure.map_id, h1]
  refine (lintegral_map (f := φ ∘ Cm g) (hφ.comp (meas_Cm g)) ((hi.prodMap hi).prodMap measurable_id)).symm.trans ?_
  rw [hP]
  rfl

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarTranslationMeasurability

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 HaarTranslationMeasurability

theorem hpkEx_holds : HpkEx := by
  intro k r z z' hk hz hz' hT hT' μ μW μW' μN hμ hW hW' hN μsec hsec
  obtain ⟨μG0, hG0⟩ := Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r
  obtain ⟨μW0, hW0⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r z hz hT
  obtain ⟨μW0', hW0'⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r z' hz' hT'
  obtain ⟨μN0, hN0⟩ := Formalism.FourierDecayAlt.P.unipotent_haar_exists k r
  have hD : IsMeasData k r z z' μsec μG0 μW0 μN0 μW0' := ⟨hk, hz, hz', hT, hT', hG0, hW0, hN0, hW0', hsec⟩
  obtain ⟨C, hC, hInt⟩ := Formalism.FourierDecayAlt.P.integration_formula_constant k r z z' μsec μG0 μW0 μN0 μW0' hD
  have cG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  have cW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have cW' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z'
  have cN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  obtain ⟨a, ha0, hat, rfl⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant cG hG0 hμ
  obtain ⟨b, hb0, hbt, rfl⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant cW hW0 hW
  obtain ⟨b', hb0', hbt', rfl⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant cW' hW0' hW'
  obtain ⟨d, hd0, hdt, rfl⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant cN hN0 hN
  haveI := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hW0
  haveI := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hW0'
  haveI := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hN0
  have iW := Formalism.FourierDecayAlt.P.haar_measure_inversion k r _ μW0 cW hW0
  have iW' := Formalism.FourierDecayAlt.P.haar_measure_inversion k r _ μW0' cW' hW0'
  have iN := Formalism.FourierDecayAlt.P.haar_measure_inversion k r _ μN0 cN hN0
  have jW' : (b' • μW0').map invM = b' • μW0' := by
    rw [Measure.map_smul b' meas_invM.aemeasurable, iW']
  have jN : (d • μN0).map invM = d • μN0 := by
    rw [Measure.map_smul d meas_invM.aemeasurable, iN]
  set κ : ℝ≥0∞ := b * d * (b' * d) with hκ
  have hκ0 : κ ≠ 0 := by simp [hκ, hb0, hd0, hb0']
  have hκt : κ ≠ ⊤ := by simp [hκ, ENNReal.mul_eq_top, hbt, hdt, hbt']
  have key : ∀ (g : Mat k r) (φ : Mt k r → ℝ≥0∞), Measurable φ →
      ∫⁻ s, ∫⁻ s', φ (fun i j => (Matrix.of s * g * (Matrix.of s')⁻¹) i j)
          ∂(Formalism.MainNotions.S.muS (b' • μW0') (d • μN0)) ∂(Formalism.MainNotions.S.muS (b • μW0) (d • μN0)) =
        κ * ∫⁻ p, φ (sgs p g) ∂((μW0.prod μN0).prod (μW0'.prod μN0)) := by
    intro g φ hφ
    have := tgt_eq (b • μW0) (d • μN0) (b' • μW0') jN jW' g φ hφ
    refine this.trans ?_
    rw [src_eq μW0 μN0 μW0' iW iN g φ hφ]
    simp only [Measure.prod_smul_left, Measure.prod_smul_right, lintegral_smul_measure, smul_eq_mul, hκ]
    ring
  have hne : a * (C : ℝ≥0∞) ≠ ⊤ := ENNReal.mul_ne_top hat ENNReal.coe_ne_top
  have hne0 : a * (C : ℝ≥0∞) ≠ 0 := mul_ne_zero ha0 (by exact_mod_cast hC.ne')
  refine ⟨(a * C / κ).toReal, ENNReal.toReal_pos (by simp [ENNReal.div_eq_zero_iff, hne0, hκt])
    (ENNReal.div_lt_top hne hκ0).ne, fun φ hφ => ?_⟩
  rw [ENNReal.ofReal_toReal (ENNReal.div_lt_top hne hκ0).ne, lintegral_smul_measure, hInt φ hφ, smul_eq_mul]
  simp_rw [key _ φ hφ]
  have hc : ∀ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q) *
      (κ * ∫⁻ p, φ (sgs p (bigCell k r q.1 (μsec q.2))) ∂((μW0.prod μN0).prod (μW0'.prod μN0))) =
      κ * (ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q) *
        ∫⁻ p, φ (sgs p (bigCell k r q.1 (μsec q.2))) ∂((μW0.prod μN0).prod (μW0'.prod μN0))) := fun q => by ring
  simp_rw [hc]
  rw [lintegral_const_mul' _ _ hκt, ← mul_assoc, ← mul_assoc, ENNReal.div_mul_cancel hκ0 hκt]

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
end
end

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

theorem transEx_holds (hHC : HaarCorr) (hW : CoordW) : TransEx := fun hH _ =>
  jacExGood_of_N (jacExGoodN_of_hpkEx_of_pFrame_of_haarCorr hH pFrame_holds hHC zBig bigMem_holds hW secWb_holds)

theorem local_jacobian_of_double_coset (h1 : DiagDCLoc) (hR : RightInvS) (hHC : HaarCorr) (hW : CoordW) : JacLoc :=
  jacLoc_of_ex h1 hR (degRed_holds hR (transEx_holds hHC hW hpkEx_holds hR))

theorem jacLoc_of_rightInv_haarCorr (hR : RightInvS) (hHC : HaarCorr) (hW : CoordW) : JacLoc :=
  local_jacobian_of_double_coset Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.DiagDCLoc_holds hR hHC hW

theorem jacLoc_of_rightInv_setCorr (hR : RightInvS) (hSC : SetCorr) (hW : CoordW) : JacLoc :=
  jacLoc_of_rightInv_haarCorr hR (haarCorr_of hSC) hW

theorem jacLoc_of_setCorr' (hSC : SetCorr) (hW : CoordW) : JacLoc :=
  jacLoc_of_rightInv_setCorr (rightInvS_of hSC (haarCorr_of hSC)) hSC hW

theorem jacLoc_of_setCorr (hSC : SetCorr) : JacLoc :=
  jacLoc_of_setCorr' hSC coordW_holds

theorem jacLoc_holds : JacLoc :=
  jacLoc_of_setCorr setCorr_holds

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates
