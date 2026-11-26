module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetPointGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarBoundOfMultiplicity

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdelicAbsDetPowDiagonalUniformizerMul
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdelicAbsDetPowDiagonalUniformizerMul
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
namespace GlobalTheory.CellEvalDet

open Matrix

variable {E : Type} [Field E] [NumberField E]

theorem detPow_eq_rpow {n : ℕ} (x : ℝ) (g : GA E n) :
    GlobalTheory.RSJ.detPow E n x g =
      ((GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ) := by
  have hpos := (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det g)).2
  rw [Real.rpow_def_of_pos hpos, ← GlobalTheory.IdeleLogNormCompare.logNorm_eq_log_ideleModule]
  simp only [GlobalTheory.RSJ.detPow, chiDet, GlobalTheory.HeckeGal.Model.absPow, MonoidHom.coe_comp, Function.comp_apply]
  change ‖Complex.exp ((x : ℂ) * (GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det g) : ℂ))‖ = _
  rw [Complex.norm_exp]
  congr 1
  simp [mul_comm]

theorem det_diagT {R : Type} [CommRing R] {n : ℕ} (t : Fin n → Rˣ) :
    GeneralLinearGroup.det (GlobalTheory.SmGL.diagT R (Fin n) t) = ∏ i, t i := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, GlobalTheory.SmGL.val_diagT, det_diagonal, Units.coe_prod]

def posVal : {r : ℝ // 0 < r} →* ℝ where
  toFun r := r
  map_one' := rfl
  map_mul' _ _ := rfl

theorem qV_pos (v : HeightOneSpectrum (𝓞 E)) : (0 : ℝ) < qV E v :=
  lt_of_le_of_ne (Nat.cast_nonneg _) (GlobalTheory.AdeleScale.qV_ne_zero v).symm

end GlobalTheory.CellEvalDet


open GlobalTheory.CellEvalDet Matrix in
theorem GlobalTheory.CellEvalDet.detPow_tl_mul : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (x : ℝ) (g : GA E n),
    GlobalTheory.RSJ.detPow E n x (GlobalTheory.CellDec.tl n ϖ l * g) =
      (∏ w ∈ l.support, (qV E w : ℝ) ^ (-x * ∑ i, (l w i : ℝ))) * GlobalTheory.RSJ.detPow E n x g := by
  intro E _ _ _ n ϖ hϖ l x g
  rw [GlobalTheory.RSJ.Model.detPow_mul, detPow_eq_rpow x (GlobalTheory.CellDec.tl n ϖ l)]
  congr 1
  have hdet : GeneralLinearGroup.det (GlobalTheory.CellDec.tl n ϖ l) =
      ∏ i, finId E (GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun y : Fin n → ℤ => y i) rfl l)) := by
    unfold GlobalTheory.CellDec.tl
    rw [det_finGL, det_diagT, map_prod]
  have hmod : ((GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det (GlobalTheory.CellDec.tl n ϖ l)) : ℝ)) =
      ∏ i, ∏ v ∈ l.support, ((qV E v : ℝ) ^ (l v i))⁻¹ := by
    rw [hdet, map_prod]
    change posVal (∏ i, _) = _
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    change ((GroundTheory.Global.IdeleGroup.ideleModule E _ : ℝ)) = _
    rw [GlobalTheory.AdeleScale.ideleModule_finId_adl ϖ hϖ _ l.support (fun v hv => by
      rw [Finsupp.notMem_support_iff] at hv; simp [hv])]
    simp
  rw [hmod, Finset.prod_comm, ← Real.finsetProd_rpow _ _ (fun v _ =>
    Finset.prod_nonneg fun i _ => inv_nonneg.2 (zpow_nonneg (Nat.cast_nonneg _) _)) x]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hq := qV_pos (E := E) v
  have e : ∀ i, ((qV E v : ℝ) ^ (l v i))⁻¹ = (qV E v : ℝ) ^ (-(l v i : ℝ)) := fun i => by
    rw [Real.rpow_neg hq.le, Real.rpow_intCast]
  simp_rw [e]
  rw [← Real.rpow_sum_of_pos hq, ← Real.rpow_mul hq.le]
  congr 1
  rw [Finset.sum_neg_distrib]
  ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdelicAbsDetPowDiagonalUniformizerMulStatement
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idelicAbsDetPow_diagonalUniformizer_mul : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (x : ℝ) (g : GA E n),
    GlobalTheory.RSJ.detPow E n x (GlobalTheory.CellDec.tl n ϖ l * g) =
      (∏ w ∈ l.support, (qV E w : ℝ) ^ (-x * ∑ i, (l w i : ℝ))) * GlobalTheory.RSJ.detPow E n x g := by
  first | exact @GlobalTheory.CellEvalDet.detPow_tl_mul | exact GlobalTheory.CellEvalDet.detPow_tl_mul | (intros; apply GlobalTheory.CellEvalDet.detPow_tl_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumSchurSquareCellProductEqEulerProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumSchurSquareCellProductEqEulerProduct
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.RSCellSum

theorem schurDir_eq_tsum_locFac (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) :
    GlobalTheory.RSPole.schurDir q α x = ∑' ν : Fin n → ℤ, GlobalTheory.RSCell.locFac q α x ν := by
  let g : {l : Fin n → ℕ // Antitone l} → (Fin n → ℤ) := fun l i => (l.1 i : ℤ)
  have hg : Function.Injective g := by
    intro a b h
    apply Subtype.ext
    funext i
    have := congrFun h i
    simpa [g] using this
  have hs : Function.support (GlobalTheory.RSCell.locFac q α x) ⊆ Set.range g := by
    intro ν hν
    rw [Function.mem_support] at hν
    unfold GlobalTheory.RSCell.locFac at hν
    split_ifs at hν with h
    · refine ⟨⟨fun i => (ν i).toNat, fun i j hij => Int.toNat_le_toNat (h.1 hij)⟩, ?_⟩
      funext i
      simp [g, Int.toNat_of_nonneg (h.2 i)]
    · exact absurd rfl hν
  rw [← hg.tsum_eq hs, GlobalTheory.RSPole.schurDir]
  refine tsum_congr fun l => ?_
  have hA : Antitone (g l) ∧ ∀ i, 0 ≤ g l i :=
    ⟨fun i j hij => by simpa [g] using l.2 hij, fun i => by simp [g]⟩
  rw [GlobalTheory.RSCell.locFac, if_pos hA]
  simp [g]

theorem tsum_cellProd_sub_eq_eulD (E : Type) [Field E] [NumberField E] (n : ℕ)
    (T : Finset (HeightOneSpectrum (𝓞 E)))
    (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin n → ℂ) (x : ℝ) (l₀ : GlobalTheory.CellDec.abelian₂ E n T) :
    ∑' l : GlobalTheory.CellDec.abelian₂ E n T, GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) =
      GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal) α x := by
  let sh : GlobalTheory.CellDec.abelian₂ E n T ≃ GlobalTheory.CellDec.abelian₂ E n T :=
    { toFun := fun l => ⟨l.1 - l₀.1, fun v hv => by simp [l.2 v hv, l₀.2 v hv]⟩
      invFun := fun l => ⟨l.1 + l₀.1, fun v hv => by simp [l.2 v hv, l₀.2 v hv]⟩
      left_inv := fun l => Subtype.ext (by simp)
      right_inv := fun l => Subtype.ext (by simp) }
  have h1 : ∑' l : GlobalTheory.CellDec.abelian₂ E n T, GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) =
      ∑' l : GlobalTheory.CellDec.abelian₂ E n T, GlobalTheory.RSCell.cellProd T α x l.1 :=
    sh.tsum_eq (fun l => GlobalTheory.RSCell.cellProd T α x l.1)
  rw [h1]
  have hsupp : ∀ l : GlobalTheory.CellDec.abelian₂ E n T, ∀ w ∈ l.1.support, w ∉ T := fun l w hw hT =>
    (Finsupp.mem_support_iff.1 hw) (l.2 w hT)
  let e : GlobalTheory.CellDec.abelian₂ E n T ≃ ({w : HeightOneSpectrum (𝓞 E) // w ∉ T} →₀ (Fin n → ℤ)) :=
    { toFun := fun l => l.1.subtypeDomain (fun w => w ∉ T)
      invFun := fun ν => ⟨ν.extendDomain, fun v hv => by simp [Finsupp.extendDomain_apply, hv]⟩
      left_inv := fun l => Subtype.ext (Finsupp.extendDomain_subtypeDomain l.1 (hsupp l))
      right_inv := fun ν => Finsupp.subtypeDomain_extendDomain ν }
  let f : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → (Fin n → ℤ) → ℝ≥0∞ :=
    fun w ν => GlobalTheory.RSCell.locFac (Ideal.absNorm w.1.asIdeal) (α w) x ν
  have hf0 : ∀ w, f w 0 = 1 := fun w => GlobalTheory.RSCell.locFac_zero _ _ _
  let h : HeightOneSpectrum (𝓞 E) → (Fin n → ℤ) → ℝ≥0∞ := fun w ν =>
    if hw : w ∈ T then 1 else GlobalTheory.RSCell.locFac (Ideal.absNorm w.asIdeal) (α ⟨w, hw⟩) x ν
  have h2 : ∀ l : GlobalTheory.CellDec.abelian₂ E n T, GlobalTheory.RSCell.cellProd T α x l.1 = (e l).prod f := by
    intro l
    have : (e l).prod f = (l.1.subtypeDomain (fun w => w ∉ T)).prod (fun a b => h a.1 b) := by
      refine Finset.prod_congr rfl fun a _ => ?_
      simp only [h, dif_neg a.2, f]
      rfl
    rw [this, Finsupp.prod_subtypeDomain_index (hsupp l)]
    rfl
  rw [tsum_congr h2, e.tsum_eq (fun ν => ν.prod f),
    (GlobalTheory.EulerSum.euler_product_intVec_ennreal n f hf0).2, GlobalTheory.RSPole.eulD]
  refine tprod_congr fun w => ?_
  rw [schurDir_eq_tsum_locFac]

end GlobalTheory.RSCellSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumSchurSquareCellProductEqEulerProductStatement
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_schurSquareCellProduct_eq_eulerProduct : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin n → ℂ) (x : ℝ) (l₀ : GlobalTheory.CellDec.abelian₂ E n T),
    ∑' l : GlobalTheory.CellDec.abelian₂ E n T, GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) =
      GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal) α x := by
  first | exact @GlobalTheory.RSCellSum.tsum_cellProd_sub_eq_eulD | exact GlobalTheory.RSCellSum.tsum_cellProd_sub_eq_eulD | (intros; apply GlobalTheory.RSCellSum.tsum_cellProd_sub_eq_eulD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergLocalTermEqSphericalWhittakerProduc
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergLocalTermEqSphericalWhittakerProduc
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.ZEulLocal

theorem wtS_eq_sum (n : ℕ) (a : Fin n → ℤ) :
    GlobalTheory.CellDec.wtS n a = ∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * a i := by
  have h1 : ∀ i : Fin n, (∑ j : Fin n, if i < j then a i - a j else 0) =
      (∑ j : Fin n, if i < j then a i else 0) - ∑ j : Fin n, if i < j then a j else 0 := by
    intro i
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [GlobalTheory.CellDec.wtS, Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_sub_distrib,
    Finset.sum_comm (f := fun i j => if i < j then a j else 0)]
  simp only [← Finset.sum_filter, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Finset.sum_const,
    Fin.card_Ioi, Fin.card_Iio, nsmul_eq_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.isLt
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring


open GlobalTheory.JSW in
theorem localTerm_eq : ∀ (q : ℕ), 0 < q → ∀ (n : ℕ) (α β : Fin n → ℂ) (x : ℝ) (v : Fin n → ℤ), (∀ i, 0 ≤ v i) → Antitone v →
    (((q : ℝ) ^ GlobalTheory.CellDec.wtS n v : ℝ) : ℂ) *
      (GlobalTheory.JSW.sphW q α (fun i => (v i).toNat) * conj (GlobalTheory.JSW.sphW q β (fun i => (v i).toNat))) *
      (((q : ℝ) ^ (-x * ∑ i, (v i : ℝ)) : ℝ) : ℂ) = GlobalTheory.ZEul.rsTerm q α β x v := by
  intro q hq n α β x v h0 hv
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hl : Antitone (fun i => (v i).toNat) := fun i j hij => Int.toNat_le_toNat (hv hij)
  have hcast : ∀ i, (((v i).toNat : ℕ) : ℂ) = ((v i : ℝ) : ℂ) := by
    intro i
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (h0 i)]
    simp
  set cR : ℝ := ∑ i : Fin n, ((n : ℝ) - 1 - 2 * (i : ℕ)) * (v i : ℝ) with hcR
  have hc : (∑ i : Fin n, (((n : ℂ) - 1 - 2 * (i : ℕ)) * (((v i).toNat : ℕ) : ℂ))) = (cR : ℂ) := by
    rw [hcR]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcast i, Complex.ofReal_intCast]
  set A : ℝ := (q : ℝ) ^ (-cR / 2) with hA'
  have hA : (q : ℂ) ^ (-(cR : ℂ) / 2) = (A : ℂ) := by
    rw [hA', Complex.ofReal_cpow hqR.le]
    push_cast
    rfl
  have hW : (GlobalTheory.CellDec.wtS n v : ℝ) = cR := by
    rw [GlobalTheory.ZEulLocal.wtS_eq_sum, hcR]
    push_cast
    rfl
  have key : (q : ℝ) ^ GlobalTheory.CellDec.wtS n v * (A * A) = 1 := by
    rw [hA', ← Real.rpow_add hqR, ← Real.rpow_intCast, ← Real.rpow_add hqR, hW]
    rw [show cR + (-cR / 2 + -cR / 2) = 0 by ring, Real.rpow_zero]
  have key2 : (((q : ℝ) ^ (-x * ∑ i, (v i : ℝ)) : ℝ) : ℂ) = ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, (v i).toNat) := by
    have e : (q : ℂ) ^ (-(x : ℂ)) = (((q : ℝ) ^ (-x) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hqR.le]
      push_cast
      rfl
    rw [e, ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul hqR.le]
    congr 3
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    exact_mod_cast (Int.toNat_of_nonneg (h0 i)).symm
  rw [sphW, sphW, if_pos hl, if_pos hl, hc, hA, GlobalTheory.ZEul.rsTerm, if_pos ⟨h0, hv⟩, key2, map_mul,
    Complex.conj_ofReal]
  calc _ = (((q : ℝ) ^ GlobalTheory.CellDec.wtS n v * (A * A) : ℝ) : ℂ) *
        (schurAt (fun i => (v i).toNat) α * conj (schurAt (fun i => (v i).toNat) β) *
          ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, (v i).toNat)) := by push_cast; ring
    _ = _ := by rw [key]; simp

end GlobalTheory.ZEulLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergLocalTermEqSphericalWhittakerProducStatement
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankinSelbergLocalTerm_eq_sphericalWhittaker_product : ∀ (q : ℕ), 0 < q → ∀ (n : ℕ) (α β : Fin n → ℂ) (x : ℝ) (v : Fin n → ℤ), (∀ i, 0 ≤ v i) → Antitone v →
    (((q : ℝ) ^ GlobalTheory.CellDec.wtS n v : ℝ) : ℂ) *
      (GlobalTheory.JSW.sphW q α (fun i => (v i).toNat) * conj (GlobalTheory.JSW.sphW q β (fun i => (v i).toNat))) *
      (((q : ℝ) ^ (-x * ∑ i, (v i : ℝ)) : ℝ) : ℂ) = GlobalTheory.ZEul.rsTerm q α β x v := by
  first | (exact @GlobalTheory.ZEulLocal.localTerm_eq) | (exact GlobalTheory.ZEulLocal.localTerm_eq) | (intros; apply GlobalTheory.ZEulLocal.localTerm_eq  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisMatchOfDenseSeparable
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisMatchOfDenseSeparable
open GlobalTheory.JR Matrix MeasureTheory Filter Topology Polynomial

namespace GlobalTheory.JR.DenseMatch

theorem charpoly_companion {k : Type} [CommRing k] :
    ∀ (r : ℕ) (p : Fin r → k), (companion p).charpoly = X ^ r + ∑ i : Fin r, C (p i) * X ^ (i : ℕ) := by
  intro r
  induction r with
  | zero => intro p; simp [Matrix.charpoly, Matrix.det_isEmpty]
  | succ s ih =>
    cases s with
    | zero =>
      intro p
      simp [Matrix.charpoly, Matrix.det_unique, charmatrix_apply, companion]
    | succ n =>
      intro p
      have h00 : (charmatrix (companion p)).submatrix Fin.succ Fin.succ
          = charmatrix (companion (fun i : Fin (n + 1) => p i.succ)) := by
        ext i j
        simp only [submatrix_apply, charmatrix_apply, companion, of_apply, diagonal_apply, Fin.succ_inj,
          Fin.val_succ]
        split_ifs <;> first | rfl | simp_all | omega
      have hlast : ((charmatrix (companion p)).submatrix Fin.succ (Fin.last (n + 1)).succAbove).det
          = (-1) ^ (n + 1) := by
        rw [Fin.succAbove_last, Matrix.det_of_upperTriangular]
        · have : ∀ i : Fin (n + 1), (charmatrix (companion p)).submatrix Fin.succ Fin.castSucc i i = -1 := by
            intro i
            simp only [submatrix_apply, charmatrix_apply, companion, of_apply, diagonal_apply]
            split_ifs <;> simp_all [Fin.ext_iff] <;> omega
          simp only [submatrix_apply] at this
          simp [this]
        · intro i j hij
          simp only [submatrix_apply, charmatrix_apply, companion, of_apply, diagonal_apply]
          have : (j : ℕ) < i := hij
          split_ifs <;> simp_all [Fin.ext_iff] <;> omega
      rw [Matrix.charpoly, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
        Finset.sum_eq_single (Fin.last n)]
      · rw [Fin.succAbove_zero, h00, ← Matrix.charpoly, ih, Fin.succ_last, hlast]
        have e1 : charmatrix (companion p) 0 0 = X := by
          simp [charmatrix_apply, companion]
        have e2 : charmatrix (companion p) 0 (Fin.last (n + 1)) = C (p 0) := by
          simp [charmatrix_apply, companion, Fin.ext_iff]
        rw [e1, e2, Fin.sum_univ_succ (n := n + 1)]
        simp only [Fin.val_last, Fin.val_zero, Fin.val_succ, pow_zero, mul_one]
        have : ((-1 : k[X]) ^ (n + 1)) * (-1) ^ (n + 1) = 1 := by rw [← mul_pow]; simp
        have e3 : ∑ x : Fin (n + 1), C (p x.succ) * X ^ ((x : ℕ) + 1)
            = X * ∑ i : Fin (n + 1), C (p i.succ) * X ^ (i : ℕ) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
        rw [e3, Nat.succ_eq_add_one]
        linear_combination C (p 0) * this
      · intro j _ hj
        have : charmatrix (companion p) 0 j.succ = 0 := by
          have hjn : (j : ℕ) ≠ n := fun h => hj (Fin.ext (by simp [h]))
          rw [charmatrix_apply, diagonal_apply_ne _ (Fin.succ_ne_zero j).symm]
          simp only [companion, of_apply, Fin.val_succ, Fin.val_zero]
          rw [if_neg (by omega)]
          simp
        rw [this, mul_zero, zero_mul]
      · simp

end GlobalTheory.JR.DenseMatch

namespace GlobalTheory.JR.DenseMatch

theorem finite_not_separable_add_C {F : Type} [Field F] [CharZero F] (P : F[X]) :
    {t : F | ¬ (P + C t).Separable}.Finite := by
  by_cases hd : derivative P = 0
  · obtain ⟨c, rfl⟩ : ∃ c, P = C c := ⟨P.coeff 0, eq_C_of_derivative_eq_zero hd⟩
    refine (Set.finite_singleton (-c)).subset fun t ht => ?_
    simp only [Set.mem_setOf_eq, ← C_add, separable_C, isUnit_iff_ne_zero, not_not] at ht
    simp only [Set.mem_singleton_iff]; linear_combination ht
  · let K := AlgebraicClosure F
    have hfin : ((fun α : K => -aeval α P) '' (derivative P).rootSet K).Finite :=
      ((derivative P).rootSet_finite K).image _
    refine (hfin.preimage (algebraMap F K).injective.injOn).subset fun t ht => ?_
    simp only [Set.mem_setOf_eq, separable_def, isCoprime_iff_aeval_ne_zero_of_isAlgClosed F K,
      not_forall, not_or, not_not, derivative_add, derivative_C, add_zero] at ht
    obtain ⟨α, h1, h2⟩ := ht
    refine ⟨α, ?_, ?_⟩
    · rw [mem_rootSet]; exact ⟨hd, h2⟩
    · simp only [map_add (f := _), aeval_C] at h1
      linear_combination -h1

theorem frequently_of_curve {Y F : Type} [TopologicalSpace Y] [NontriviallyNormedField F] (γ : F → Y)
    (hγ : Continuous γ) (x₀ : Y) (h0 : γ 0 = x₀) (P : Y → Prop) (hfin : {t | ¬ P (γ t)}.Finite) :
    ∃ᶠ x in 𝓝 x₀, P x := by
  intro hne
  have h1 : ∀ᶠ t in 𝓝[≠] (0 : F), ¬ P (γ t) :=
    ((h0 ▸ hγ.tendsto 0).mono_left nhdsWithin_le_nhds).eventually hne
  have h2 : ∀ᶠ t in 𝓝[≠] (0 : F), t ∉ {t | ¬ P (γ t)} := by
    have hc : IsClosed ({t | ¬ P (γ t)} \ {0}) := (hfin.subset Set.diff_subset).isClosed
    have : ∀ᶠ t in 𝓝 (0 : F), t ∉ ({t | ¬ P (γ t)} \ {0}) := hc.isOpen_compl.mem_nhds (by simp)
    filter_upwards [nhdsWithin_le_nhds this, self_mem_nhdsWithin] with t ht ht0
    exact fun hb => ht ⟨hb, ht0⟩
  obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
  exact ht2 ht1

theorem continuous_Delta {r : ℕ} {F : Type} [NontriviallyNormedField F] :
    Continuous (fun a : Inv r F => Delta a) := by
  have hc : Continuous (fun p : Fin r → F => companion p) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [companion, of_apply]
    split_ifs
    · exact (continuous_apply i).neg
    · exact continuous_const
    · exact continuous_const
  have hc' : Continuous (fun a : Inv r F => companion a.1) := hc.comp continuous_fst
  unfold Delta
  apply Continuous.matrix_det
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [hankel, of_apply, mom, sec]
  exact (continuous_snd.fst).dotProduct ((hc'.pow _).matrix_mulVec continuous_const)

end GlobalTheory.JR.DenseMatch

namespace GlobalTheory.JR.DenseMatch

theorem frequently_separable {F : Type} [NontriviallyNormedField F] [CharZero F] :
    ∀ (r : ℕ) (a₀ : Inv r F), ∃ᶠ a in 𝓝 a₀, (companion a.1).charpoly.Separable
  | 0, a₀ => (Eventually.of_forall fun a => by rw [charpoly_companion]; simp).frequently
  | s + 1, a₀ => by
    have key : ∀ t : F, (companion (a₀.1 + Pi.single 0 t)).charpoly = (companion a₀.1).charpoly + C t := by
      intro t
      rw [charpoly_companion, charpoly_companion, Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp [Pi.single_apply, Fin.succ_ne_zero]
      ring
    have hs : Continuous (fun t : F => (Pi.single 0 t : Fin (s + 1) → F)) :=
      continuous_pi fun i => by simp only [Pi.single_apply]; split_ifs <;> fun_prop
    refine frequently_of_curve (fun t : F => ((a₀.1 + Pi.single 0 t, a₀.2) : Inv (s + 1) F)) (by fun_prop) a₀
      (by simp) (fun a => (companion a.1).charpoly.Separable) ?_
    refine (finite_not_separable_add_C (companion a₀.1).charpoly).subset fun t ht => ?_
    simpa [key] using ht

theorem frequently_mom_ne_zero {F : Type} [NontriviallyNormedField F] (s : ℕ) (a₀ : Inv (s + 1) F) :
    ∃ᶠ a in 𝓝 a₀, mom (sec a) 0 ≠ 0 := by
  have key : ∀ a : Inv (s + 1) F, mom (sec a) 0 = a.2.1 0 := by
    intro a; simp [mom, sec, dotProduct, Fin.sum_univ_succ, Fin.succ_ne_zero]
  have hs : Continuous (fun t : F => (Pi.single 0 t : Fin (s + 1) → F)) :=
    continuous_pi fun i => by simp only [Pi.single_apply]; split_ifs <;> fun_prop
  refine frequently_of_curve (fun t : F => ((a₀.1, a₀.2.1 + Pi.single 0 t, a₀.2.2) : Inv (s + 1) F))
    (by fun_prop) a₀ (by simp) (fun a => mom (sec a) 0 ≠ 0) ?_
  refine (Set.finite_singleton (-a₀.2.1 0)).subset fun t ht => ?_
  simp only [Set.mem_setOf_eq, key, not_not, Pi.add_apply, Pi.single_eq_same] at ht
  simp only [Set.mem_singleton_iff]; linear_combination ht

theorem match_of_frequently {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (M : Meas r F E) (f' : Gl r F → ℂ) (f : Hn r F E → ℂ)
    (hf' : IsTest f') (hf : IsTest f) (G : Inv r F → Prop) (hG : ∀ a₀ : Inv r F, ∃ᶠ a in 𝓝 a₀, G a)
    (h : ∀ a : Inv r F, Delta a ≠ 0 → G a → MatchAt M f' f a) : Match M f' f := by
  intro a₀ hΔ
  have hcont : ∀ᶠ a in 𝓝 a₀, Delta a ≠ 0 := continuous_Delta.continuousAt.eventually_ne hΔ
  have hL7 := GlobalTheory.T.jacquetRallisOrbitalIntegrals_invariant_locallyConstant F E r M
  have hO := hL7.2.2.1 f' hf' a₀ hΔ
  constructor
  · intro X hX
    have hU := hL7.2.2.2 f hf a₀ X hΔ hX
    obtain ⟨a, ha1, ha2, ha3, ⟨X', hX'⟩, hUX⟩ := ((hG a₀).and_eventually (hcont.and (hO.and hU))).exists
    rw [← ha3, (h a ha2 ha1).1 X' hX', hUX X' hX']
  · intro hno
    have h5 := (GlobalTheory.T.invariant_image_openClosed_local_sections F E r a₀ hΔ).1 hno
    obtain ⟨a, ha1, ha2, ha3, ha4⟩ := ((hG a₀).and_eventually (hcont.and (hO.and h5))).exists
    rw [← ha3]
    exact (h a ha2 ha1).2 ha4

theorem match_of_dense : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (f' : Gl r F → ℂ) (f : Hn r F E → ℂ),
    IsTest f' → IsTest f →
      ((∀ a : Inv r F, Delta a ≠ 0 → (companion a.1).charpoly.Separable → MatchAt M f' f a) → Match M f' f) ∧
      (0 < r → (∀ a : Inv r F, Delta a ≠ 0 → mom (sec a) 0 ≠ 0 → MatchAt M f' f a) → Match M f' f) := by
  intro F E _ _ _ _ _ r M f' f hf' hf
  haveI : CharZero F := Unram.charZero (F := F) (E := E)
  refine ⟨fun h => match_of_frequently M f' f hf' hf _ (frequently_separable r) h, fun hr h => ?_⟩
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hr.ne'
  exact match_of_frequently M f' f hf' hf _ (frequently_mom_ne_zero s) h

end GlobalTheory.JR.DenseMatch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisMatchOfDenseSeparableStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallis_match_of_dense_separable : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (f' : Gl r F → ℂ) (f : Hn r F E → ℂ), IsTest f' → IsTest f → ((∀ a : Inv r F, Delta a ≠ 0 → (companion a.1).charpoly.Separable → MatchAt M f' f a) → Match M f' f) ∧ (0 < r → (∀ a : Inv r F, Delta a ≠ 0 → mom (sec a) 0 ≠ 0 → MatchAt M f' f a) → Match M f' f) := by
  first | exact @GlobalTheory.JR.DenseMatch.match_of_dense | exact GlobalTheory.JR.DenseMatch.match_of_dense | (intros; apply GlobalTheory.JR.DenseMatch.match_of_dense <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedRankinSelbergIntegrandContinuousInvarian
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedRankinSelbergIntegrandContinuousInvarian
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.RSCellB

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem row_mul_of_mem_NA {ℓ : Fin a} (hℓ : (ℓ : ℕ) + 1 = a) {u : GA E a} (hu : u ∈ GlobalTheory.CellDec.NA E a)
    (g : GA E a) : (u * g).val ℓ = g.val ℓ := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
  funext j
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single ℓ]
  · rw [h2 ℓ, one_mul]
  · intro k _ hk
    have hlt : k < ℓ := by
      rcases lt_or_gt_of_ne hk with h | h
      · exact h
      · exact absurd k.2 (by have : (ℓ : ℕ) < k := h; omega)
    rw [h1 ℓ k hlt, zero_mul]
  · intro h; exact absurd (Finset.mem_univ ℓ) h

theorem det_of_mem_NA {u : GA E a} (hu : u ∈ GlobalTheory.CellDec.NA E a) : GeneralLinearGroup.det u = 1 := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, Units.val_one, Matrix.det_of_upperTriangular (fun i j h => h1 i j h)]
  simp [h2]

end GlobalTheory.RSCellB

namespace GlobalTheory.RSCellB

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem rsPsi_self_mul (ℓ : Fin a) {W : GA E a → ℂ} {u : GA E a} (hW : ∀ g, ‖W (u * g)‖ = ‖W g‖)
    (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (g : GA E a)
    (y : Fin a → Ad E) :
    GlobalTheory.RSTheta.rsPsi ℓ W W Φ J η (u * g) y = GlobalTheory.RSTheta.rsPsi ℓ W W Φ J η g y := by
  simp only [GlobalTheory.RSTheta.rsPsi, GlobalTheory.ThetaPoisson.thetaFn, GlobalTheory.RSTheta.rsInf, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, mul_assoc u g, hW]

theorem bInt_continuous_invariant_finite : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a), (ℓ : ℕ) + 1 = a →
    ∀ (F : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E),
    Continuous (GlobalTheory.JSW.whit F) → (∀ u ∈ GlobalTheory.CellDec.NA E a, ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    Continuous Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ →
    Continuous (fun p : ℝ × GA E a => GlobalTheory.RSCell.bInt ℓ F Φ J η p.1 p.2) ∧
      (∀ x, ∀ u ∈ GlobalTheory.CellDec.NA E a, ∀ g, GlobalTheory.RSCell.bInt ℓ F Φ J η x (u * g) = GlobalTheory.RSCell.bInt ℓ F Φ J η x g) ∧
      ∀ x g, GlobalTheory.RSCell.bInt ℓ F Φ J η x g ≠ ⊤ := by
  intro E _ _ _ a ℓ hℓ F Φ J η hWc hWu hΦc hΦs
  have hdet : Continuous fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) :=
    continuous_subtype_val.comp (continuous_ideleModule.comp (GroundTheory.Automorphic.AdelicGLn.continuous_det E a))
  refine ⟨?_, ?_, ?_⟩
  · have h1 : Continuous fun p : ℝ × GA E a => (p.2, p.2.val ℓ) :=
      continuous_snd.prodMk ((continuous_apply ℓ).comp ((Units.continuous_val (M := Matrix (Fin a) (Fin a) (Ad E))).comp continuous_snd))
    have h2 := (GlobalTheory.RSTheta.continuous_rsPsi hWc hWc hΦc hΦs J η).comp h1
    have h3 : Continuous fun p : ℝ × GA E a => (ideleModule E (GeneralLinearGroup.det p.2) : ℝ) ^ p.1 :=
      (hdet.comp continuous_snd).rpow continuous_fst fun p => Or.inl (ideleModule E (GeneralLinearGroup.det p.2)).2.ne'
    exact h2.enorm.ennreal_mul (ENNReal.continuous_ofReal.comp h3) (fun _ => Or.inr ENNReal.ofReal_ne_top)
      (fun _ => Or.inr enorm_ne_top)
  · intro x u hu g
    simp only [GlobalTheory.RSCell.bInt, row_mul_of_mem_NA hℓ hu, map_mul, det_of_mem_NA hu, one_mul]
    rw [rsPsi_self_mul ℓ (hWu u hu)]
  · intro x g
    exact ENNReal.mul_ne_top enorm_ne_top ENNReal.ofReal_ne_top

end GlobalTheory.RSCellB

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedRankinSelbergIntegrandContinuousInvarianStatement
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedRankinSelbergIntegrand_continuous_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a), (ℓ : ℕ) + 1 = a →
    ∀ (F : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E),
    Continuous (GlobalTheory.JSW.whit F) → (∀ u ∈ GlobalTheory.CellDec.NA E a, ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    Continuous Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ →
    Continuous (fun p : ℝ × GA E a => GlobalTheory.RSCell.bInt ℓ F Φ J η p.1 p.2) ∧
      (∀ x, ∀ u ∈ GlobalTheory.CellDec.NA E a, ∀ g, GlobalTheory.RSCell.bInt ℓ F Φ J η x (u * g) = GlobalTheory.RSCell.bInt ℓ F Φ J η x g) ∧
      ∀ x g, GlobalTheory.RSCell.bInt ℓ F Φ J η x g ≠ ⊤ := by
  first | exact @GlobalTheory.RSCellB.bInt_continuous_invariant_finite | exact GlobalTheory.RSCellB.bInt_continuous_invariant_finite | (intros; apply GlobalTheory.RSCellB.bInt_continuous_invariant_finite <;> assumption)
end
end
