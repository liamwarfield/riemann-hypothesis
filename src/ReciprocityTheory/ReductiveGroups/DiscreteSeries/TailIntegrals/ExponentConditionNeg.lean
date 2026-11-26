module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Imports

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.RhoSqInsSucc
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux

abbrev Yp (p m : ℕ) := (Fin (p + 1) → ℂ) × (Fin p → ℂ) × (Fin m → ℂ) × ℝ

def ins {p m : ℕ} (y : Yp p m) (z : ℂ) : Xp (p + 1) m := (y.1, Fin.cons z y.2.1, y.2.2)

def bS {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : ℂ :=
  ∑ j : Fin p, if l.val ≤ j.val then x.2.1 j * star (x.1 j) else 0

lemma Lsq_ins {p m : ℕ} (y : Yp p m) (z : ℂ) (l : Fin (p + 2)) :
    Lsq (ins y z) l = Lsq (tailPt y) l := rfl

private theorem ins_snd_fst_eq_tailPt_snd_fst_of_ne_zero {p m : ℕ} (y : Yp p m) (z : ℂ) {j : Fin (p + 1)} (hj : j ≠ 0) :
    (ins y z).2.1 j = (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y).2.1 j := by
  induction j using Fin.cases with
  | zero => exact absurd rfl hj
  | succ k => simp [ins, ReciprocityTheory.ChartRestriction.DS.Xi.tailPt]

lemma sum_ins_succ {p m : ℕ} (y : Yp p m) (z : ℂ) (i : Fin (p + 1)) (g : ℂ → ℂ → ℂ) :
    (∑ j : Fin (p + 1), if i.succ.val ≤ j.val then g ((ins y z).2.1 j) ((ins y z).1 j) else 0) =
      ∑ j : Fin (p + 1), if i.succ.val ≤ j.val then g ((tailPt y).2.1 j) ((tailPt y).1 j) else 0 := by
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : i.succ.val ≤ j.val
  · have hj : j ≠ 0 := by
      rintro rfl
      simp at h
    rw [if_pos h, if_pos h, ins_snd_fst_eq_tailPt_snd_fst_of_ne_zero y z hj]
    all_goals rfl
  · rw [if_neg h, if_neg h]

lemma sumR_ins_succ {p m : ℕ} (y : Yp p m) (z : ℂ) (i : Fin (p + 1)) :
    (∑ j : Fin (p + 1), if i.succ.val ≤ j.val then ‖(ins y z).2.1 j‖ ^ 2 else 0) =
      ∑ j : Fin (p + 1), if i.succ.val ≤ j.val then ‖(tailPt y).2.1 j‖ ^ 2 else 0 := by
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : i.succ.val ≤ j.val
  · have hj : j ≠ 0 := by
      rintro rfl
      simp at h
    rw [if_pos h, if_pos h, ins_snd_fst_eq_tailPt_snd_fst_of_ne_zero y z hj]
  · rw [if_neg h, if_neg h]

lemma rhoSq_ins_succ {p m : ℕ} (y : Yp p m) (z : ℂ) (i : Fin (p + 1)) :
    rhoSq (ins y z) i.succ = rhoSq (tailPt y) i.succ := by
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.rhoSq
  rw [Lsq_ins, sumR_ins_succ]
  all_goals rfl

lemma bco_ins_succ {p m : ℕ} (y : Yp p m) (z : ℂ) (i : Fin (p + 1)) :
    bco (ins y z) i.succ = bco (tailPt y) i.succ := by
  have h : (∑ j : Fin (p + 1), if i.succ.val ≤ j.val then (ins y z).2.1 j * star ((ins y z).1 j) else 0) =
      ∑ j : Fin (p + 1), if i.succ.val ≤ j.val then (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y).2.1 j * star ((ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y).1 j) else 0 :=
    sum_ins_succ y z i (fun a b => a * star b)
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.bco
  rw [h]
  all_goals rfl

lemma de_ins_succ {p m : ℕ} (y : Yp p m) (z : ℂ) (i : Fin (p + 1)) :
    de (ins y z) i.succ = de (tailPt y) i.succ := by
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.de
  rw [Lsq_ins, rhoSq_ins_succ, bco_ins_succ]

lemma Lsq_ge_one {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 1 ≤ Lsq x l := by
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.Lsq
  have : 0 ≤ ∑ j : Fin p, (if j.val < l.val then ‖x.1 j‖ ^ 2 else 0) :=
    Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)
  linarith

lemma Lsq_mono {p m : ℕ} (x : Xp p m) {l l' : Fin (p + 1)} (h : l ≤ l') : Lsq x l ≤ Lsq x l' := by
  have h' : l.val ≤ l'.val := Fin.le_iff_val_le_val.mp h
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.Lsq
  have : ∑ j : Fin p, (if j.val < l.val then ‖x.1 j‖ ^ 2 else 0) ≤
      ∑ j : Fin p, (if j.val < l'.val then ‖x.1 j‖ ^ 2 else 0) := by
    apply Finset.sum_le_sum
    intro j _
    by_cases h1 : j.val < l.val
    · have h2 : j.val < l'.val := lt_of_lt_of_le h1 h'
      rw [if_pos h1, if_pos h2]
    · rw [if_neg h1]
      split_ifs <;> positivity
  linarith

lemma rhoSq_ge {p m : ℕ} (x : Xp p m) (l l' : Fin (p + 1)) : Lsq x l' ≤ rhoSq x l := by
  have h1 := Lsq_mono x (Fin.le_last l')
  have h2 : 0 ≤ ∑ i, ‖x.2.2.1 i‖ ^ 2 := Finset.sum_nonneg (fun i _ => by positivity)
  have h3 : 0 ≤ ∑ j : Fin p, (if l.val ≤ j.val then ‖x.2.1 j‖ ^ 2 else 0) :=
    Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.rhoSq
  linarith

lemma de_ge_one {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 1 ≤ de x l := by
  have hL := Lsq_ge_one x l
  have hR : 1 ≤ ReciprocityTheory.ChartRestriction.DS.Xi.rhoSq x l := le_trans hL (rhoSq_ge x l l)
  have hc : 0 ≤ ‖ReciprocityTheory.ChartRestriction.DS.Xi.bco x l‖ ^ 2 := by positivity
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.de
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith)

def splitE (p m : ℕ) : Xp (p + 1) m ≃ᵐ Yp p m × ℂ :=
  ((MeasurableEquiv.refl (Fin (p + 1) → ℂ)).prodCongr
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => ℂ) 0).prodCongr
        (MeasurableEquiv.refl ((Fin m → ℂ) × ℝ)))).trans
    (((MeasurableEquiv.refl (Fin (p + 1) → ℂ)).prodCongr MeasurableEquiv.prodAssoc).trans
      (MeasurableEquiv.prodAssoc.symm.trans
        ((MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl _)).trans
          (MeasurableEquiv.prodAssoc.trans MeasurableEquiv.prodComm))))

lemma splitE_mp (p m : ℕ) : MeasurePreserving (splitE p m) volume volume := by
  have e1 : MeasurePreserving ((MeasurableEquiv.refl (Fin (p + 1) → ℂ)).prodCongr
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => ℂ) 0).prodCongr
        (MeasurableEquiv.refl ((Fin m → ℂ) × ℝ)))) volume volume :=
    (MeasurePreserving.id volume).prod
      ((volume_preserving_piFinSuccAbove (fun _ : Fin (p + 1) => ℂ) 0).prod (MeasurePreserving.id volume))
  have e2 : MeasurePreserving ((MeasurableEquiv.refl (Fin (p + 1) → ℂ)).prodCongr
      (MeasurableEquiv.prodAssoc :
        (ℂ × (Fin p → ℂ)) × ((Fin m → ℂ) × ℝ) ≃ᵐ ℂ × (Fin p → ℂ) × ((Fin m → ℂ) × ℝ))) volume volume :=
    (MeasurePreserving.id volume).prod volume_preserving_prodAssoc
  have e3 : MeasurePreserving (MeasurableEquiv.prodAssoc :
      ((Fin (p + 1) → ℂ) × ℂ) × ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ)) ≃ᵐ
        (Fin (p + 1) → ℂ) × ℂ × ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ))).symm volume volume :=
    MeasurePreserving.symm _ volume_preserving_prodAssoc
  have e4 : MeasurePreserving ((MeasurableEquiv.prodComm :
      (Fin (p + 1) → ℂ) × ℂ ≃ᵐ ℂ × (Fin (p + 1) → ℂ)).prodCongr
      (MeasurableEquiv.refl ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ)))) volume volume :=
    Measure.measurePreserving_swap.prod (MeasurePreserving.id volume)
  have e5 : MeasurePreserving (MeasurableEquiv.prodAssoc :
      (ℂ × (Fin (p + 1) → ℂ)) × ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ)) ≃ᵐ
        ℂ × (Fin (p + 1) → ℂ) × ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ))) volume volume :=
    volume_preserving_prodAssoc
  have e6 : MeasurePreserving (MeasurableEquiv.prodComm :
      ℂ × ((Fin (p + 1) → ℂ) × ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ))) ≃ᵐ
        ((Fin (p + 1) → ℂ) × ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ))) × ℂ) volume volume :=
    Measure.measurePreserving_swap
  exact e6.comp (e5.comp (e4.comp (e3.comp (e2.comp e1))))

lemma ins_splitE {p m : ℕ} (x : Xp (p + 1) m) : ins (splitE p m x).1 (splitE p m x).2 = x := by
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  funext j
  induction j using Fin.cases with
  | zero => rfl
  | succ k =>
    show x.2.1 (Fin.succAbove 0 k) = x.2.1 k.succ
    simp

lemma split_le {p m : ℕ} (G : Xp (p + 1) m → ℝ≥0∞) :
    ∫⁻ x, G x ≤ ∫⁻ y : Yp p m, ∫⁻ z : ℂ, G (ins y z) := by
  have h := (splitE_mp p m).lintegral_comp_emb (splitE p m).measurableEmbedding
    (fun w => G (ins w.1 w.2))
  simp only [ins_splitE] at h
  exact h.trans_le (lintegral_prod_le _)

lemma cont_Lsq {p m : ℕ} (l : Fin (p + 1)) : Continuous (fun x : Xp p m => Lsq x l) := by
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.Lsq
  exact continuous_const.fun_add (continuous_finsetSum _ (fun j _ => by
    by_cases h : j.val < l.val <;> simp only [h, ↓reduceIte] <;> fun_prop))

lemma cont_rhoSq {p m : ℕ} (l : Fin (p + 1)) : Continuous (fun x : Xp p m => rhoSq x l) := by
  have h1 := cont_Lsq (p := p) (m := m) (Fin.last p)
  have h2 : Continuous fun x : ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m => ∑ i, ‖x.2.2.1 i‖ ^ 2 :=
    continuous_finsetSum _ (fun i _ => by fun_prop)
  have h3 : Continuous fun x : ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m => ∑ j : Fin p, if l.val ≤ j.val then ‖x.2.1 j‖ ^ 2 else 0 :=
    continuous_finsetSum _ (fun j _ => by
      by_cases h : l.val ≤ j.val <;> simp only [h, ↓reduceIte] <;> fun_prop)
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.rhoSq
  exact (h1.add h2).add h3

lemma cont_bco {p m : ℕ} (l : Fin (p + 1)) : Continuous (fun x : Xp p m => bco x l) := by
  have h00 : Continuous fun x : ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m => ∑ i, ‖x.2.2.1 i‖ ^ 2 :=
    continuous_finsetSum _ (fun i _ => by fun_prop)
  have h0 : Continuous fun x : ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m =>
      (((-(∑ i, ‖x.2.2.1 i‖ ^ 2) / 2 : ℝ)) : ℂ) + (x.2.2.2 : ℂ) * Complex.I :=
    (Complex.continuous_ofReal.comp (h00.neg.div_const 2)).add
      ((Complex.continuous_ofReal.comp (by fun_prop : Continuous fun x : ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m => x.2.2.2)).mul continuous_const)
  have hs : Continuous fun x : ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m => ∑ j : Fin p, if l.val ≤ j.val then x.2.1 j * star (x.1 j) else 0 :=
    continuous_finsetSum _ (fun j _ => by
      by_cases h : l.val ≤ j.val <;> simp only [h, ↓reduceIte] <;> fun_prop)
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.bco
  exact h0.sub hs

lemma cont_de {p m : ℕ} (l : Fin (p + 1)) : Continuous (fun x : Xp p m => de x l) := by
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.de
  exact Real.continuous_sqrt.comp
    (((cont_Lsq l).mul (cont_rhoSq l)).add ((cont_bco l).norm.pow 2))

lemma cont_linF {p m : ℕ} (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) : Continuous (linF η η' ζ) := by
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.linF
  exact (continuous_finsetSum _ fun j _ => by fun_prop).add (continuous_finsetSum _ fun i _ => by fun_prop)

lemma cont_tailPt {p m : ℕ} : Continuous (fun y : Yp p m => tailPt y) := by
  have hmid : Continuous fun y : Yp p m => (Fin.cons (0 : ℂ) y.2.1 : Fin (p + 1) → ℂ) :=
    continuous_pi (fun j => by
      induction j using Fin.cases with
      | zero => simp only [Fin.cons_zero]; exact continuous_const
      | succ k => simp only [Fin.cons_succ]; fun_prop)
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.tailPt
  fun_prop

lemma meas_fS {p m : ℕ} (s : Fin (p + 2) → ℝ) : Measurable (fS (p := p) (m := m) s) := by
  unfold fS
  exact Finset.measurable_prod _ (fun l _ =>
    ENNReal.measurable_ofReal.comp ((cont_de (p := p + 1) (m := m) l).measurable.pow_const _))

end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.DeZeroBounds
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux

private def qB {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : ℝ :=
  Lsq x l * rhoSq x l + (-(∑ i, ‖x.2.2.1 i‖ ^ 2) / 2 - (bS x l).re) ^ 2

private lemma one_le_Lsq {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 1 ≤ Lsq x l := by
  unfold Lsq
  have h : 0 ≤ ∑ j : Fin p, (if j.val < l.val then ‖x.1 j‖ ^ 2 else 0) :=
    Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)
  linarith

private lemma Lsq_last_le_rhoSq {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) :
    Lsq x (Fin.last p) ≤ rhoSq x l := by
  unfold rhoSq
  have h1 : 0 ≤ ∑ i, ‖x.2.2.1 i‖ ^ 2 := Finset.sum_nonneg (fun i _ => by positivity)
  have h2 : 0 ≤ ∑ j : Fin p, (if l.val ≤ j.val then ‖x.2.1 j‖ ^ 2 else 0) :=
    Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)
  linarith

private lemma qB_nonneg {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 0 ≤ qB x l := by
  have h1 := one_le_Lsq x l
  have h2 := one_le_Lsq x (Fin.last p)
  have h3 := Lsq_last_le_rhoSq x l
  have h4 : 0 ≤ Lsq x l * rhoSq x l := mul_nonneg (by linarith) (by linarith)
  unfold qB
  exact add_nonneg h4 (sq_nonneg _)

private lemma norm_bco_sq_eq {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) :
    ‖bco x l‖ ^ 2 = (-(∑ i, ‖x.2.2.1 i‖ ^ 2) / 2 - (bS x l).re) ^ 2 + (x.2.2.2 - (bS x l).im) ^ 2 := by
  have hb : bco x l = (((-(∑ i, ‖x.2.2.1 i‖ ^ 2) / 2 : ℝ)) : ℂ) + (x.2.2.2 : ℂ) * Complex.I - bS x l := rfl
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hb]
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, Complex.sub_im, Complex.add_im, Complex.mul_im]
  ring

private lemma de_rpow {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) (r : ℝ) :
    de x l ^ r = (qB x l + (x.2.2.2 - (bS x l).im) ^ 2) ^ (r / 2) := by
  have h0 : 0 ≤ qB x l + (x.2.2.2 - (bS x l).im) ^ 2 := add_nonneg (qB_nonneg x l) (sq_nonneg _)
  have he : de x l = Real.sqrt (qB x l + (x.2.2.2 - (bS x l).im) ^ 2) := by
    unfold de qB
    rw [norm_bco_sq_eq]
    congr 1
    ring
  rw [he, Real.sqrt_eq_rpow, ← Real.rpow_mul h0]
  congr 1
  ring

private lemma Lsq_zero' {p m : ℕ} (x : Xp p m) : Lsq x 0 = 1 := by
  unfold Lsq
  simp

private lemma de_sq' {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) :
    de x l ^ 2 = Lsq x l * rhoSq x l + ‖bco x l‖ ^ 2 := by
  have h1 := one_le_Lsq x l
  have h2 := one_le_Lsq x (Fin.last p)
  have h3 := Lsq_last_le_rhoSq x l
  unfold de
  rw [Real.sq_sqrt]
  exact add_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)

private lemma rhoSq_one_le {p m : ℕ} (x : Xp (p + 1) m) : rhoSq x 1 ≤ rhoSq x 0 := by
  unfold rhoSq
  have h : ∑ j : Fin (p + 1), (if (1 : Fin (p + 1 + 1)).val ≤ j.val then ‖x.2.1 j‖ ^ 2 else 0) ≤
      ∑ j : Fin (p + 1), (if (0 : Fin (p + 1 + 1)).val ≤ j.val then ‖x.2.1 j‖ ^ 2 else 0) := by
    apply Finset.sum_le_sum
    intro j _
    split_ifs <;> first | exact le_rfl | positivity | simp_all
  linarith

private lemma bS_tailPt_zero_eq_one {p m : ℕ} (y : Yp p m) : bS (tailPt y) 0 = bS (tailPt y) 1 := by
  unfold bS tailPt
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp

private lemma de_zero_bounds {p m : ℕ} (y : Yp p m) :
    de (tailPt y) 1 ^ 2 ≤ Lsq (tailPt y) 1 * de (tailPt y) 0 ^ 2 ∧
      |(tailPt y).2.2.2 - (bS (tailPt y) 1).im| ≤ de (tailPt y) 0 := by
  have hb0 := bS_tailPt_zero_eq_one y
  have hbc : bco (tailPt y) 0 = bco (tailPt y) 1 := by
    have h := hb0
    unfold bS at h
    unfold bco
    rw [h]
  have hL0 := Lsq_zero' (tailPt y)
  have hL1 := one_le_Lsq (tailPt y) 1
  have hr := rhoSq_one_le (tailPt y)
  have hr1 : Lsq (tailPt y) (Fin.last (p + 1)) ≤ rhoSq (tailPt y) 1 := Lsq_last_le_rhoSq _ _
  have hr2 := one_le_Lsq (tailPt y) (Fin.last (p + 1))
  constructor
  · rw [de_sq', de_sq', hL0, hbc]
    have h5 : Lsq (tailPt y) 1 * rhoSq (tailPt y) 1 ≤ Lsq (tailPt y) 1 * rhoSq (tailPt y) 0 :=
      mul_le_mul_of_nonneg_left hr (by linarith)
    have h6 := mul_le_mul_of_nonneg_right hL1 (sq_nonneg ‖bco (tailPt y) 1‖)
    nlinarith
  · have h0 : 0 ≤ Lsq (tailPt y) 0 * rhoSq (tailPt y) 0 := by
      rw [hL0, one_mul]; linarith
    unfold de
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    rw [norm_bco_sq_eq, hb0]
    nlinarith [sq_nonneg (-(∑ i, ‖(tailPt y).2.2.1 i‖ ^ 2) / 2 - (bS (tailPt y) 1).re)]

theorem beta_bound (hL : SLOW) {p m : ℕ} (e : Fin (p + 2) → ℝ) {γ : ℝ} (he : ∀ l, 0 < e l)
    (he1 : ∀ l, e l ≤ 1) (hγ2 : γ < 2) (hα : 0 < γ / 2 - e 0) :
    ∃ CS : ℝ, 0 < CS ∧ ∀ (a : Fin (p + 1) → ℂ) (a'' : Fin p → ℂ) (u : Fin m → ℂ),
      ∫⁻ β : ℝ, ENNReal.ofReal (Lsq (tailPt (a, a'', u, β)) 1 ^ (-1 + γ / 2)) *
          ENNReal.ofReal (de (tailPt (a, a'', u, β)) 0 ^ (-(γ - e 0))) *
          ∏ i : Fin (p + 1), ENNReal.ofReal
            (de (tailPt (a, a'', u, β)) i.succ ^ (-(s0N (p + 1) m i.succ - e i.succ))) ≤
        ENNReal.ofReal CS * ∫⁻ β : ℝ,
          ENNReal.ofReal (Lsq (tailPt (a, a'', u, β)) 1 ^ ((-2 + (γ / 2 - e 0)) / 2)) *
          ENNReal.ofReal (de (tailPt (a, a'', u, β)) 1 ^ (-(γ / 2 - e 0))) *
          ∏ i : Fin (p + 1), ENNReal.ofReal (de (tailPt (a, a'', u, β)) i.succ ^
            (-(s0N (p + 1) m i.succ + (fun i : Fin (p + 1) => -e i.succ) i))) := by
  have hγ0 : 0 < γ := by linarith [he 0]
  obtain ⟨C, hC⟩ := hL (p + 1) (γ / 2 - e 0 + ∑ i : Fin (p + 1), s0N (p + 1) m i.succ) (γ / 2)
    (by linarith) (by linarith)
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun a a'' u => ?_⟩
  set L := Lsq (tailPt (a, a'', u, 0)) 1 with hLdef
  have hLX : ∀ β : ℝ, Lsq (tailPt (a, a'', u, β)) 1 = L := fun β => rfl
  have hL1 : 1 ≤ L := Lsq_ge_one _ 1
  have hL0 : 0 < L := by linarith
  set Al : Fin (p + 2) → ℝ := fun l => Real.sqrt (qB (tailPt (a, a'', u, 0)) l) with hAl
  set bl : Fin (p + 2) → ℝ := fun l => (bS (tailPt (a, a'', u, 0)) l).im with hbl
  set c := bl 1 with hc
  set t : Fin (p + 1) → ℝ := fun i => s0N (p + 1) m i.succ - e i.succ + if i = 0 then γ / 2 - e 0 else 0
    with ht
  have hfac : ∀ (β : ℝ) (l : Fin (p + 2)) (r : ℝ),
      de (tailPt (a, a'', u, β)) l ^ r = (Al l ^ 2 + (β - bl l) ^ 2) ^ (r / 2) := by
    intro β l r
    rw [de_rpow, hAl, hbl]
    simp only
    rw [Real.sq_sqrt (qB_nonneg _ _)]
    rfl
  have hG : ∀ β : ℝ, ENNReal.ofReal (de (tailPt (a, a'', u, β)) 1 ^ (-(γ / 2 - e 0))) *
      ∏ i : Fin (p + 1), ENNReal.ofReal
        (de (tailPt (a, a'', u, β)) i.succ ^ (-(s0N (p + 1) m i.succ - e i.succ))) =
      slowly t (fun i => Al i.succ) (fun i => bl i.succ) β := by
    intro β
    have hd1 : 0 < de (tailPt (a, a'', u, β)) 1 := lt_of_lt_of_le one_pos (de_ge_one _ _)
    unfold slowly
    simp only [Fin.prod_univ_succ]
    rw [← mul_assoc]
    congr 1
    · rw [Fin.succ_zero_eq_one', ← ENNReal.ofReal_mul (Real.rpow_nonneg hd1.le _),
        ← Real.rpow_add hd1, hfac]
      congr 2
      simp only [ht, Fin.succ_zero_eq_one', if_true]
      ring
    · refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [hfac]
      congr 2
      simp only [ht, Fin.succ_ne_zero, if_false]
      ring
  have hR : ∀ β : ℝ,
      ENNReal.ofReal (Lsq (tailPt (a, a'', u, β)) 1 ^ ((-2 + (γ / 2 - e 0)) / 2)) *
        ENNReal.ofReal (de (tailPt (a, a'', u, β)) 1 ^ (-(γ / 2 - e 0))) *
        ∏ i : Fin (p + 1), ENNReal.ofReal (de (tailPt (a, a'', u, β)) i.succ ^
          (-(s0N (p + 1) m i.succ + (fun i : Fin (p + 1) => -e i.succ) i))) =
      ENNReal.ofReal (L ^ ((-2 + (γ / 2 - e 0)) / 2)) *
        slowly t (fun i => Al i.succ) (fun i => bl i.succ) β := by
    intro β
    rw [← hG β, hLX, mul_assoc]
    simp only [sub_eq_add_neg]
  have hpt : ∀ β : ℝ, β ≠ c →
      ENNReal.ofReal (Lsq (tailPt (a, a'', u, β)) 1 ^ (-1 + γ / 2)) *
          ENNReal.ofReal (de (tailPt (a, a'', u, β)) 0 ^ (-(γ - e 0))) *
          ∏ i : Fin (p + 1), ENNReal.ofReal
            (de (tailPt (a, a'', u, β)) i.succ ^ (-(s0N (p + 1) m i.succ - e i.succ))) ≤
        ENNReal.ofReal (L ^ (-1 + γ / 2) * L ^ ((γ / 2 - e 0) / 2)) *
          (slowly t (fun i => Al i.succ) (fun i => bl i.succ) β * ENNReal.ofReal (|β - c| ^ (-(γ / 2)))) := by
    intro β hβ
    rw [hLX, ← hG β]
    obtain ⟨hsq, habs⟩ := de_zero_bounds (a, a'', u, β)
    have habs' : |β - c| ≤ de (tailPt (a, a'', u, β)) 0 := habs
    have hsq' : de (tailPt (a, a'', u, β)) 1 ^ 2 ≤ L * de (tailPt (a, a'', u, β)) 0 ^ 2 := hsq
    have hd0 : 0 < de (tailPt (a, a'', u, β)) 0 := lt_of_lt_of_le one_pos (de_ge_one _ _)
    have hd1 : 0 < de (tailPt (a, a'', u, β)) 1 := lt_of_lt_of_le one_pos (de_ge_one _ _)
    have hcpos : 0 < |β - c| := abs_pos.mpr (sub_ne_zero.mpr hβ)
    have hreal : de (tailPt (a, a'', u, β)) 0 ^ (-(γ - e 0)) ≤
        L ^ ((γ / 2 - e 0) / 2) * de (tailPt (a, a'', u, β)) 1 ^ (-(γ / 2 - e 0)) *
          |β - c| ^ (-(γ / 2)) := by
      have hsplit : de (tailPt (a, a'', u, β)) 0 ^ (-(γ - e 0)) =
          de (tailPt (a, a'', u, β)) 0 ^ (-(γ / 2 - e 0)) * de (tailPt (a, a'', u, β)) 0 ^ (-(γ / 2)) := by
        rw [← Real.rpow_add hd0]; congr 1; ring
      rw [hsplit]
      set s := Real.sqrt L with hs
      have hs0 : 0 < s := Real.sqrt_pos.mpr hL0
      have hs2 : s ^ 2 = L := Real.sq_sqrt hL0.le
      have hle : de (tailPt (a, a'', u, β)) 1 ≤ s * de (tailPt (a, a'', u, β)) 0 := by
        nlinarith [mul_pos hs0 hd0]
      have hdiv : de (tailPt (a, a'', u, β)) 1 / s ≤ de (tailPt (a, a'', u, β)) 0 := by
        rw [div_le_iff₀ hs0]; linarith
      have h1 : de (tailPt (a, a'', u, β)) 0 ^ (-(γ / 2 - e 0)) ≤
          L ^ ((γ / 2 - e 0) / 2) * de (tailPt (a, a'', u, β)) 1 ^ (-(γ / 2 - e 0)) := by
        refine (Real.rpow_le_rpow_of_nonpos (div_pos hd1 hs0) hdiv (by linarith)).trans (le_of_eq ?_)
        rw [Real.div_rpow hd1.le hs0.le, Real.rpow_neg hs0.le, div_inv_eq_mul, hs,
          Real.sqrt_eq_rpow, ← Real.rpow_mul hL0.le, mul_comm]
        congr 2
        ring
      have h2 : de (tailPt (a, a'', u, β)) 0 ^ (-(γ / 2)) ≤ |β - c| ^ (-(γ / 2)) :=
        Real.rpow_le_rpow_of_nonpos hcpos habs' (by linarith)
      exact mul_le_mul h1 h2 (Real.rpow_nonneg hd0.le _)
        (mul_nonneg (Real.rpow_nonneg hL0.le _) (Real.rpow_nonneg hd1.le _))
    calc _ ≤ ENNReal.ofReal (L ^ (-1 + γ / 2)) *
          ENNReal.ofReal (L ^ ((γ / 2 - e 0) / 2) * de (tailPt (a, a'', u, β)) 1 ^ (-(γ / 2 - e 0)) *
            |β - c| ^ (-(γ / 2))) *
          ∏ i : Fin (p + 1), ENNReal.ofReal
            (de (tailPt (a, a'', u, β)) i.succ ^ (-(s0N (p + 1) m i.succ - e i.succ))) :=
          by gcongr
      _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hL0.le _) (Real.rpow_nonneg hd1.le _)),
          ENNReal.ofReal_mul (Real.rpow_nonneg hL0.le _),
          ENNReal.ofReal_mul (Real.rpow_nonneg hL0.le _)]
        ring
  have hs0N : ∀ i : Fin (p + 2), 1 ≤ s0N (p + 1) m i := by
    intro i
    unfold s0N
    split_ifs
    · norm_num
    · have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
  have ht0 : ∀ i, 0 ≤ t i := by
    intro i
    simp only [ht]
    have h1 := hs0N i.succ
    have h2 := he1 i.succ
    split_ifs <;> linarith
  have hT : ∑ i, t i ≤ γ / 2 - e 0 + ∑ i : Fin (p + 1), s0N (p + 1) m i.succ := by
    simp only [ht, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have : ∑ i : Fin (p + 1), (s0N (p + 1) m i.succ - e i.succ) ≤
        ∑ i : Fin (p + 1), s0N (p + 1) m i.succ :=
      Finset.sum_le_sum (fun i _ => by linarith [he i.succ])
    linarith
  have hA : ∀ i : Fin (p + 1), L ≤ Al i.succ := by
    intro i
    have hmono : Lsq (tailPt (a, a'', u, 0)) 1 ≤ Lsq (tailPt (a, a'', u, 0)) i.succ := by
      apply Lsq_mono
      rw [← Fin.succ_zero_eq_one']
      exact Fin.succ_le_succ_iff.mpr (Fin.zero_le _)
    have hrho := rhoSq_ge (tailPt (a, a'', u, 0)) i.succ 1
    have hq : L ^ 2 ≤ qB (tailPt (a, a'', u, 0)) i.succ := by
      unfold qB
      have : L * L ≤ Lsq (tailPt (a, a'', u, 0)) i.succ * rhoSq (tailPt (a, a'', u, 0)) i.succ :=
        mul_le_mul hmono hrho hL0.le (by linarith)
      nlinarith [sq_nonneg (-(∑ i, ‖(tailPt (a, a'', u, 0)).2.2.1 i‖ ^ 2) / 2 -
        (bS (tailPt (a, a'', u, 0)) i.succ).re)]
    rw [← Real.sqrt_sq hL0.le]
    exact Real.sqrt_le_sqrt hq
  have hslow := hC t (fun i => Al i.succ) (fun i => bl i.succ - c) L hL0 ht0 hT hA
  have htr1 : ∫⁻ β : ℝ, slowly t (fun i => Al i.succ) (fun i => bl i.succ) β *
      ENNReal.ofReal (|β - c| ^ (-(γ / 2))) =
      ∫⁻ β : ℝ, slowly t (fun i => Al i.succ) (fun i => bl i.succ - c) β *
        ENNReal.ofReal (|β| ^ (-(γ / 2))) := by
    have h := lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun β => slowly t (fun i => Al i.succ) (fun i => bl i.succ) β *
        ENNReal.ofReal (|β - c| ^ (-(γ / 2)))) c
    rw [← h]
    refine lintegral_congr (fun β => ?_)
    simp only [add_sub_cancel_right]
    congr 1
    unfold slowly
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [show β + c - bl i.succ = β - (bl i.succ - c) by ring]
  have htr2 : ∫⁻ β : ℝ, slowly t (fun i => Al i.succ) (fun i => bl i.succ - c) β =
      ∫⁻ β : ℝ, slowly t (fun i => Al i.succ) (fun i => bl i.succ) β := by
    have h := lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun β => slowly t (fun i => Al i.succ) (fun i => bl i.succ) β) c
    rw [← h]
    refine lintegral_congr (fun β => ?_)
    unfold slowly
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [show β + c - bl i.succ = β - (bl i.succ - c) by ring]
  have hK0 : 0 ≤ L ^ (-1 + γ / 2) * L ^ ((γ / 2 - e 0) / 2) :=
    mul_nonneg (Real.rpow_nonneg hL0.le _) (Real.rpow_nonneg hL0.le _)
  have hid : L ^ (-1 + γ / 2) * L ^ ((γ / 2 - e 0) / 2) * (max C 1 * L ^ (-(γ / 2))) =
      max C 1 * L ^ ((-2 + (γ / 2 - e 0)) / 2) := by
    rw [mul_comm (max C 1), ← mul_assoc, ← Real.rpow_add hL0, ← Real.rpow_add hL0, mul_comm]
    congr 2
    ring
  have hle : ENNReal.ofReal (C * L ^ (-(γ / 2))) ≤ ENNReal.ofReal (max C 1 * L ^ (-(γ / 2))) :=
    ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hL0.le _))
  calc _ ≤ ∫⁻ β : ℝ, ENNReal.ofReal (L ^ (-1 + γ / 2) * L ^ ((γ / 2 - e 0) / 2)) *
          (slowly t (fun i => Al i.succ) (fun i => bl i.succ) β *
            ENNReal.ofReal (|β - c| ^ (-(γ / 2)))) := by
        refine lintegral_mono_ae ?_
        filter_upwards [Measure.ae_ne volume c] with β hβ
        exact hpt β hβ
    _ = ENNReal.ofReal (L ^ (-1 + γ / 2) * L ^ ((γ / 2 - e 0) / 2)) *
          ∫⁻ β : ℝ, slowly t (fun i => Al i.succ) (fun i => bl i.succ - c) β *
            ENNReal.ofReal (|β| ^ (-(γ / 2))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, htr1]
    _ ≤ ENNReal.ofReal (L ^ (-1 + γ / 2) * L ^ ((γ / 2 - e 0) / 2)) *
          (ENNReal.ofReal (C * L ^ (-(γ / 2))) *
            ∫⁻ β : ℝ, slowly t (fun i => Al i.succ) (fun i => bl i.succ) β) := by
        rw [← htr2]
        exact mul_le_mul_of_nonneg_left hslow zero_le
    _ ≤ ENNReal.ofReal (L ^ (-1 + γ / 2) * L ^ ((γ / 2 - e 0) / 2)) *
          (ENNReal.ofReal (max C 1 * L ^ (-(γ / 2))) *
            ∫⁻ β : ℝ, slowly t (fun i => Al i.succ) (fun i => bl i.succ) β) := by
        gcongr
    _ = ENNReal.ofReal (max C 1) * (ENNReal.ofReal (L ^ ((-2 + (γ / 2 - e 0)) / 2)) *
          ∫⁻ β : ℝ, slowly t (fun i => Al i.succ) (fun i => bl i.succ) β) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hK0, hid,
          ENNReal.ofReal_mul (le_trans zero_le_one (le_max_right _ _)), mul_assoc]
    _ = _ := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        refine lintegral_congr (fun β => ?_)
        exact (hR β).symm

end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.LintegralInsertFiberLe
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux

private lemma rpow_sq_half {a : ℝ} (ha : 0 ≤ a) (r : ℝ) : a ^ r = (a ^ 2) ^ (r / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
  congr 1
  push_cast
  ring

private lemma nnorm_ae (γ : ℝ) (f : ℂ → ℝ≥0∞) :
    ∫⁻ z : ℂ, f z * (‖z‖₊ : ℝ≥0∞) ^ (-γ) = ∫⁻ z : ℂ, f z * ENNReal.ofReal (‖z‖ ^ (-γ)) := by
  apply lintegral_congr_ae
  have h0 : ∀ᵐ z : ℂ, z ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ))
  filter_upwards [h0] with z hz
  congr 1
  rw [← ENNReal.ofReal_rpow_of_pos (norm_pos_iff.mpr hz)]
  congr 1
  rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]

private lemma core {e0 γ C : ℝ}
    (hC : ∀ (c : ℂ) (D : ℝ), 0 < D →
      (∫⁻ x : ℂ, ENNReal.ofReal ((‖x - c‖ ^ 2 + D ^ 2) ^ (-1 + e0 / 2)) *
        ENNReal.ofReal (‖x‖ ^ (-γ))) ≤ ENNReal.ofReal (C * (‖c‖ ^ 2 + D ^ 2) ^ (-(γ - e0) / 2)))
    {L d1 d0 : ℝ} (c : ℂ) (f : ℂ → ℝ) (hL : 0 < L) (hd1 : 0 < d1) (hd0 : 0 ≤ d0)
    (h0 : d0 ^ 2 = L * ‖c‖ ^ 2 + d1 ^ 2 / L) (hf0 : ∀ z, 0 ≤ f z)
    (hf : ∀ z, f z ^ 2 = L * ‖z - c‖ ^ 2 + d1 ^ 2 / L) :
    ∫⁻ z : ℂ, ENNReal.ofReal (f z ^ (-(2 - e0))) * ENNReal.ofReal (‖z‖ ^ (-γ)) ≤
      ENNReal.ofReal (max C 1 * L ^ (-1 + γ / 2) * d0 ^ (-(γ - e0))) := by
  have hD : 0 < d1 / L := div_pos hd1 hL
  have hsq : ∀ t : ℝ, L * t + d1 ^ 2 / L = L * (t + (d1 / L) ^ 2) := by
    intro t
    have := hL.ne'
    field_simp
  have he : -(2 - e0) / 2 = -1 + e0 / 2 := by ring
  have hpt : ∀ z, f z ^ (-(2 - e0)) =
      L ^ (-1 + e0 / 2) * (‖z - c‖ ^ 2 + (d1 / L) ^ 2) ^ (-1 + e0 / 2) := by
    intro z
    rw [rpow_sq_half (hf0 z), hf z, hsq, he, Real.mul_rpow hL.le (by positivity)]
  have hX : ‖c‖ ^ 2 + (d1 / L) ^ 2 = d0 ^ 2 / L := by
    rw [h0, hsq]; field_simp
  have hLp : L ^ (-1 + γ / 2) = L ^ (-1 + e0 / 2) / L ^ (-(γ - e0) / 2) := by
    rw [← Real.rpow_sub hL]; congr 1; ring
  have hd0p : (d0 ^ 2) ^ (-(γ - e0) / 2) = d0 ^ (-(γ - e0)) := (rpow_sq_half hd0 _).symm
  calc ∫⁻ z : ℂ, ENNReal.ofReal (f z ^ (-(2 - e0))) * ENNReal.ofReal (‖z‖ ^ (-γ))
      = ∫⁻ z : ℂ, ENNReal.ofReal (L ^ (-1 + e0 / 2)) *
          (ENNReal.ofReal ((‖z - c‖ ^ 2 + (d1 / L) ^ 2) ^ (-1 + e0 / 2)) *
            ENNReal.ofReal (‖z‖ ^ (-γ))) := by
        refine lintegral_congr (fun z => ?_)
        rw [hpt z, ENNReal.ofReal_mul (Real.rpow_nonneg hL.le _), mul_assoc]
    _ = ENNReal.ofReal (L ^ (-1 + e0 / 2)) *
          ∫⁻ z : ℂ, ENNReal.ofReal ((‖z - c‖ ^ 2 + (d1 / L) ^ 2) ^ (-1 + e0 / 2)) *
            ENNReal.ofReal (‖z‖ ^ (-γ)) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (L ^ (-1 + e0 / 2)) *
          ENNReal.ofReal (C * (‖c‖ ^ 2 + (d1 / L) ^ 2) ^ (-(γ - e0) / 2)) := by
        gcongr
        exact hC c _ hD
    _ ≤ ENNReal.ofReal (L ^ (-1 + e0 / 2)) *
          ENNReal.ofReal (max C 1 * (‖c‖ ^ 2 + (d1 / L) ^ 2) ^ (-(γ - e0) / 2)) := by
        gcongr
        exact le_max_left _ _
    _ = ENNReal.ofReal (L ^ (-1 + e0 / 2) *
          (max C 1 * (‖c‖ ^ 2 + (d1 / L) ^ 2) ^ (-(γ - e0) / 2))) :=
        (ENNReal.ofReal_mul (Real.rpow_nonneg hL.le _)).symm
    _ = ENNReal.ofReal (max C 1 * L ^ (-1 + γ / 2) * d0 ^ (-(γ - e0))) := by
        congr 1
        rw [hX, Real.div_rpow (sq_nonneg _) hL.le, hd0p, hLp]
        ring

theorem lintegral_insertFiber_le (hC1 : C1) (hK : KER) {e0 γ : ℝ} (he0 : 0 < e0) (hγ : e0 < γ) (hγ2 : γ < 2) :
    ∃ CK : ℝ, 0 < CK ∧ ∀ {p m : ℕ} (y : Yp p m),
      ∫⁻ z : ℂ, ENNReal.ofReal (de (ins y z) 0 ^ (-(2 - e0))) * (‖z‖₊ : ℝ≥0∞) ^ (-γ) ≤
        ENNReal.ofReal (CK * Lsq (tailPt y) 1 ^ (-1 + γ / 2) * de (tailPt y) 0 ^ (-(γ - e0))) := by
  obtain ⟨C, hC⟩ := hK e0 γ he0 hγ hγ2
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro p m y
  have hf : ∀ z : ℂ, de (ins y z) 0 ^ 2 =
      Lsq (tailPt y) 1 * ‖z - y.1 0 * bco (tailPt y) 1 / (Lsq (tailPt y) 1 : ℂ)‖ ^ 2 +
        de (tailPt y) 1 ^ 2 / Lsq (tailPt y) 1 := by
    intro z
    have hb : bco (ins y z) 1 = bco (tailPt y) 1 := by simpa using bco_ins_succ y z 0
    have hd : de (ins y z) 1 = de (tailPt y) 1 := by simpa using de_ins_succ y z 0
    have h := hC1 p m (ins y z)
    rw [hb, hd, Lsq_ins] at h
    simp only [ins, Fin.cons_zero] at h
    exact h
  have h0 : de (tailPt y) 0 ^ 2 =
      Lsq (tailPt y) 1 * ‖y.1 0 * bco (tailPt y) 1 / (Lsq (tailPt y) 1 : ℂ)‖ ^ 2 +
        de (tailPt y) 1 ^ 2 / Lsq (tailPt y) 1 := by
    have := hf 0
    rw [zero_sub, norm_neg] at this
    exact this
  calc _ = ∫⁻ z : ℂ, ENNReal.ofReal (de (ins y z) 0 ^ (-(2 - e0))) * ENNReal.ofReal (‖z‖ ^ (-γ)) :=
        nnorm_ae γ _
    _ ≤ _ := core hC _ (fun z => de (ins y z) 0) (lt_of_lt_of_le one_pos (Lsq_ge_one _ _))
        (lt_of_lt_of_le one_pos (de_ge_one _ _)) (le_trans zero_le_one (de_ge_one _ _)) h0
        (fun z => le_trans zero_le_one (de_ge_one _ _)) hf

end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux

theorem avg {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ] (Φ : ℝ → X → X)
    (hΦm : Measurable (fun q : ℝ × X => Φ q.1 q.2))
    (hΦ : ∀ t ∈ Icc (1 : ℝ) 2, MeasurePreserving (Φ t) μ μ) {f w : X → ℝ≥0∞}
    (hf : Measurable f) (hw : Measurable w) (K : ℝ≥0∞)
    (hK : ∀ t ∈ Icc (1 : ℝ) 2, ∀ x, f (Φ t x) ≤ K * f x) :
    ∫⁻ x, f x * w x ∂μ ≤ K * ∫⁻ x, f x * (∫⁻ t in Icc (1 : ℝ) 2, w (Φ t x)) ∂μ := by
  have hvol : volume (Icc (1 : ℝ) 2) = 1 := by
    rw [Real.volume_Icc]; norm_num
  have hm2 : Measurable (fun q : ℝ × X => f q.2 * w (Φ q.1 q.2)) :=
    (hf.comp measurable_snd).mul (hw.comp hΦm)
  have hm3 : Measurable fun t : ℝ => ∫⁻ x, f x * w (Φ t x) ∂μ := hm2.lintegral_prod_right'
  calc ∫⁻ x, f x * w x ∂μ = ∫⁻ _t in Icc (1 : ℝ) 2, (∫⁻ x, f x * w x ∂μ) := by
        rw [setLIntegral_const, hvol, mul_one]
    _ ≤ ∫⁻ t in Icc (1 : ℝ) 2, K * (∫⁻ x, f x * w (Φ t x) ∂μ) := by
        refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
        calc ∫⁻ x, f x * w x ∂μ = ∫⁻ x, f (Φ t x) * w (Φ t x) ∂μ :=
              ((hΦ t ht).lintegral_comp (hf.mul hw)).symm
          _ ≤ ∫⁻ x, K * (f x * w (Φ t x)) ∂μ := lintegral_mono fun x => by
              rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hK t ht x) zero_le
          _ = K * ∫⁻ x, f x * w (Φ t x) ∂μ :=
              lintegral_const_mul K (hf.mul (hw.comp (hΦ t ht).measurable))
    _ = K * ∫⁻ t in Icc (1 : ℝ) 2, (∫⁻ x, f x * w (Φ t x) ∂μ) := lintegral_const_mul K hm3
    _ = K * ∫⁻ x, (∫⁻ t in Icc (1 : ℝ) 2, f x * w (Φ t x)) ∂μ := by
        rw [lintegral_lintegral_swap (f := fun t x => f x * w (Φ t x)) hm2.aemeasurable]
    _ = K * ∫⁻ x, f x * (∫⁻ t in Icc (1 : ℝ) 2, w (Φ t x)) ∂μ := by
        congr 1
        refine lintegral_congr fun x => ?_
        exact lintegral_const_mul (f x)
          ((show Measurable (Function.uncurry fun t x => w (Φ t x)) from hw.comp hΦm).of_uncurry_right)

lemma exponentCondition_neg {p : ℕ} (e : Fin (p + 2) → ℝ) {α : ℝ} (he : ∀ l, 0 < e l)
    (hα : 2 * ∑ i : Fin (p + 1), e i.succ < α) :
    CHCond p (Function.update (fun i : Fin (p + 1) => -e i.succ) 0
        (α + (fun i : Fin (p + 1) => -e i.succ) 0)) ∧
      0 < α + 2 * ∑ i, (fun i : Fin (p + 1) => -e i.succ) i := by
  have hpos : ∀ i : Fin (p + 1), 0 ≤ e i.succ := fun i => (he _).le
  have hS : ∀ s : Finset (Fin (p + 1)), ∑ i ∈ s, e i.succ ≤ ∑ i : Fin (p + 1), e i.succ :=
    fun s => Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) fun i _ _ => hpos i
  have hN : ∀ s : Finset (Fin (p + 1)), 0 ≤ ∑ i ∈ s, e i.succ :=
    fun s => Finset.sum_nonneg fun i _ => hpos i
  have hupd : ∀ j, Function.update (fun i : Fin (p + 1) => -e i.succ) 0
      (α + (fun i : Fin (p + 1) => -e i.succ) 0) j = -e j.succ + if j = 0 then α else 0 := by
    intro j
    rw [Function.update_apply]
    split_ifs with hj
    · subst hj
      show α + -e (Fin.succ 0) = -e (Fin.succ 0) + α
      ring
    · show -e j.succ = -e j.succ + 0
      ring
  have hsum : ∀ s : Finset (Fin (p + 1)), ∑ j ∈ s, Function.update (fun i : Fin (p + 1) => -e i.succ) 0
      (α + (fun i : Fin (p + 1) => -e i.succ) 0) j =
        -∑ j ∈ s, e j.succ + if (0 : Fin (p + 1)) ∈ s then α else 0 := by
    intro s
    rw [Finset.sum_congr rfl fun j _ => hupd j, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    congr 1
    simp
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.CHCond
  refine ⟨⟨fun l => ?_, fun l _ => ?_⟩, ?_⟩
  · have h0 : (0 : Fin (p + 1)) ∈ Finset.Iic l := by simp
    rw [hsum, if_pos h0]
    linarith [hS (Finset.Iic l), hN Finset.univ]
  · have h0 : (0 : Fin (p + 1)) ∈ Finset.Iic l := by simp
    have h0' : (0 : Fin (p + 1)) ∉ Finset.Ioi l := by simp [Finset.mem_Ioi]
    have hdis : Disjoint (Finset.Iic l) (Finset.Ioi l) :=
      Finset.disjoint_left.2 fun j h1 h2 =>
        lt_irrefl _ (lt_of_le_of_lt (Finset.mem_Iic.1 h1) (Finset.mem_Ioi.1 h2))
    have hAB : ∑ j ∈ Finset.Iic l, e j.succ + ∑ j ∈ Finset.Ioi l, e j.succ ≤
        ∑ j : Fin (p + 1), e j.succ := by
      rw [← Finset.sum_union hdis]; exact hS _
    rw [hsum, hsum, if_pos h0, if_neg h0']
    linarith [hN (Finset.Iic l), hN (Finset.Ioi l)]
  · show 0 < α + 2 * ∑ i : Fin (p + 1), -e i.succ
    rw [Finset.sum_neg_distrib]
    linarith [hN Finset.univ]

private theorem lintegral_prod4_eq_iterated {A B C : Type*} [MeasureSpace A] [MeasureSpace B] [MeasureSpace C]
    [SigmaFinite (volume : Measure A)] [SigmaFinite (volume : Measure B)]
    [SigmaFinite (volume : Measure C)]
    (T : A × B × C × ℝ → ℝ≥0∞) (hT : Measurable T) :
    ∫⁻ y, T y = ∫⁻ a, ∫⁻ b, ∫⁻ c, ∫⁻ t, T (a, b, c, t) := by
  simp only [Measure.volume_eq_prod]
  rw [lintegral_prod _ hT.aemeasurable]
  refine lintegral_congr fun a => ?_
  rw [lintegral_prod (fun w : B × C × ℝ => T (a, w))
    (hT.comp (by fun_prop : Measurable fun w : B × C × ℝ => (a, w))).aemeasurable]
  refine lintegral_congr fun b => ?_
  exact lintegral_prod (fun w : C × ℝ => T (a, b, w))
    (hT.comp (by fun_prop : Measurable fun w : C × ℝ => (a, b, w))).aemeasurable

theorem tail_bound (hT : TailFin) (hC1 : C1) (hK : KER) (hL : SLOW) {p m : ℕ} (e : Fin (p + 2) → ℝ)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (he : ∀ l, 0 < e l)
    (hsum : e 0 + 2 * ∑ i : Fin (p + 1), e i.succ < γ / 2) :
    ∃ C : ℝ, ∫⁻ x : Xp (p + 1) m, fS (fun l => s0N (p + 1) m l - e l) x * (‖x.2.1 0‖₊ : ℝ≥0∞) ^ (-γ) ≤
      ENNReal.ofReal C := by
  have hS0 : 0 ≤ ∑ i : Fin (p + 1), e i.succ := Finset.sum_nonneg fun i _ => (he _).le
  have he0γ : e 0 < γ := by linarith
  have hγ2 : γ < 2 := by linarith
  have hα : 0 < γ / 2 - e 0 := by linarith
  have he1 : ∀ l, e l ≤ 1 := by
    intro l
    rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨i, rfl⟩
    · linarith
    · have : e i.succ ≤ ∑ j : Fin (p + 1), e j.succ :=
        Finset.single_le_sum (f := fun j : Fin (p + 1) => e j.succ) (fun j _ => (he _).le)
          (Finset.mem_univ i)
      linarith [he 0]
  obtain ⟨CK, hCK0, hCK⟩ := lintegral_insertFiber_le hC1 hK (he 0) he0γ hγ2
  obtain ⟨CS, hCS0, hCS⟩ := beta_bound (m := m) hL e he he1 hγ2 hα
  have hec := exponentCondition_neg (α := γ / 2 - e 0) e he (by linarith)
  have hfin := hT p m (γ / 2 - e 0) (fun i => -e i.succ) hec.1 hec.2
  have hc0 : ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m 0 = 2 := by simp [ReciprocityTheory.ChartRestriction.DS.Xi.s0N]
  obtain ⟨P, hP⟩ : ∃ P : Yp p m → ℝ≥0∞, P = fun y => ∏ i : Fin (p + 1),
      ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.de (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) i.succ ^
        (-(ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m i.succ - e i.succ))) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : Yp p m → ℝ≥0∞, F = fun y =>
      ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.Lsq (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) 1 ^ (-1 + γ / 2)) *
        ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.de (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) 0 ^ (-(γ - e 0))) * P y := ⟨_, rfl⟩
  obtain ⟨T, hTd⟩ : ∃ T : Yp p m → ℝ≥0∞, T = fun y =>
      ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.Lsq (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) 1 ^ ((-2 + (γ / 2 - e 0)) / 2)) *
        ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.de (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) 1 ^ (-(γ / 2 - e 0))) *
        ∏ i : Fin (p + 1), ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.de (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) i.succ ^
          (-(ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m i.succ + (fun i : Fin (p + 1) => -e i.succ) i))) := ⟨_, rfl⟩
  have hmL : ∀ l : Fin (p + 1 + 1), Measurable fun y : Yp p m => ReciprocityTheory.ChartRestriction.DS.Xi.Lsq (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) l :=
    fun l => ((cont_Lsq l).comp cont_tailPt).measurable
  have hmH : ∀ l : Fin (p + 1 + 1), Measurable fun y : Yp p m => ReciprocityTheory.ChartRestriction.DS.Xi.de (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) l :=
    fun l => ((cont_de l).comp cont_tailPt).measurable
  have hPm : Measurable P := by
    rw [hP]
    exact Finset.measurable_prod _ fun i _ => ENNReal.measurable_ofReal.comp ((hmH i.succ).pow_const _)
  have hFm : Measurable F := by
    rw [hF]
    exact ((ENNReal.measurable_ofReal.comp ((hmL 1).pow_const _)).mul
      (ENNReal.measurable_ofReal.comp ((hmH 0).pow_const _))).mul hPm
  have hTm : Measurable T := by
    rw [hTd]
    exact ((ENNReal.measurable_ofReal.comp ((hmL 1).pow_const _)).mul
      (ENNReal.measurable_ofReal.comp ((hmH 1).pow_const _))).mul
      (Finset.measurable_prod _ fun i _ => ENNReal.measurable_ofReal.comp ((hmH i.succ).pow_const _))
  have hPne : ∀ y, P y ≠ ∞ := fun y => by
    rw [hP]; exact ENNReal.prod_ne_top fun i _ => ENNReal.ofReal_ne_top
  have hinner : ∀ y : Yp p m,
      ∫⁻ z : ℂ, fS (fun l => ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m l - e l) (ins y z) *
        (‖(ins y z).2.1 0‖₊ : ℝ≥0∞) ^ (-γ) ≤ ENNReal.ofReal CK * F y := by
    intro y
    have h1 : ∀ z, fS (fun l => ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m l - e l) (ins y z) =
        ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.de (ins y z) 0 ^ (-(ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m 0 - e 0))) *
        ∏ i : Fin (p + 1), ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.de (ins y z) i.succ ^
          (-(ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m i.succ - e i.succ))) :=
      fun z => Fin.prod_univ_succ _
    have hz : ∀ z, (ins y z).2.1 0 = z := fun z => by simp [ins]
    have hPz : ∀ z, ∏ i : Fin (p + 1), ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.de (ins y z) i.succ ^
        (-(ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m i.succ - e i.succ))) = P y := fun z => by
      rw [hP]
      exact Finset.prod_congr rfl fun i _ => by rw [de_ins_succ]
    have hnn : 0 ≤ CK * ReciprocityTheory.ChartRestriction.DS.Xi.Lsq (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) 1 ^ (-1 + γ / 2) :=
      mul_nonneg hCK0.le (Real.rpow_nonneg (zero_le_one.trans (Lsq_ge_one _ _)) _)
    calc ∫⁻ z : ℂ, fS (fun l => ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m l - e l) (ins y z) *
          (‖(ins y z).2.1 0‖₊ : ℝ≥0∞) ^ (-γ)
        = ∫⁻ z : ℂ, P y * (ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.de (ins y z) 0 ^ (-(2 - e 0))) *
            (‖z‖₊ : ℝ≥0∞) ^ (-γ)) := by
          refine lintegral_congr fun z => ?_
          rw [h1 z, hc0, hz z, hPz z]
          ring
      _ = P y * ∫⁻ z : ℂ, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.Xi.de (ins y z) 0 ^ (-(2 - e 0))) *
            (‖z‖₊ : ℝ≥0∞) ^ (-γ) := lintegral_const_mul' _ _ (hPne y)
      _ ≤ P y * ENNReal.ofReal (CK * ReciprocityTheory.ChartRestriction.DS.Xi.Lsq (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) 1 ^ (-1 + γ / 2) *
            ReciprocityTheory.ChartRestriction.DS.Xi.de (ReciprocityTheory.ChartRestriction.DS.Xi.tailPt y) 0 ^ (-(γ - e 0))) := mul_le_mul_of_nonneg_left (hCK y) zero_le
      _ = ENNReal.ofReal CK * F y := by
          simp only [hF]
          rw [ENNReal.ofReal_mul hnn, ENNReal.ofReal_mul hCK0.le]
          ring
  have hkey : ∫⁻ y, F y ≤ ENNReal.ofReal CS * ReciprocityTheory.ChartRestriction.DS.Xi.TailInt p m (γ / 2 - e 0) (fun i => -e i.succ) := by
    have htail : ReciprocityTheory.ChartRestriction.DS.Xi.TailInt p m (γ / 2 - e 0) (fun i => -e i.succ) = ∫⁻ y, T y := by
      rw [hTd]; rfl
    rw [htail, lintegral_prod4_eq_iterated F hFm, lintegral_prod4_eq_iterated T hTm]
    calc ∫⁻ a : Fin (p + 1) → ℂ, ∫⁻ b : Fin p → ℂ, ∫⁻ c : Fin m → ℂ, ∫⁻ t : ℝ, F (a, b, c, t)
        ≤ ∫⁻ a : Fin (p + 1) → ℂ, ∫⁻ b : Fin p → ℂ, ∫⁻ c : Fin m → ℂ,
            ENNReal.ofReal CS * ∫⁻ t : ℝ, T (a, b, c, t) := by
          refine lintegral_mono fun a => lintegral_mono fun b => lintegral_mono fun c => ?_
          subst hF hP hTd
          exact hCS a b c
      _ = ENNReal.ofReal CS * ∫⁻ a : Fin (p + 1) → ℂ, ∫⁻ b : Fin p → ℂ, ∫⁻ c : Fin m → ℂ,
            ∫⁻ t : ℝ, T (a, b, c, t) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun a => ?_
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun b => ?_
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ⟨CK * CS * (ReciprocityTheory.ChartRestriction.DS.Xi.TailInt p m (γ / 2 - e 0) (fun i => -e i.succ)).toReal, ?_⟩
  calc _ ≤ ∫⁻ y : Yp p m, ∫⁻ z : ℂ,
        fS (fun l => ReciprocityTheory.ChartRestriction.DS.Xi.s0N (p + 1) m l - e l) (ins y z) *
          (‖(ins y z).2.1 0‖₊ : ℝ≥0∞) ^ (-γ) := split_le _
    _ ≤ ∫⁻ y : Yp p m, ENNReal.ofReal CK * F y := lintegral_mono hinner
    _ = ENNReal.ofReal CK * ∫⁻ y, F y := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal CK * (ENNReal.ofReal CS * ReciprocityTheory.ChartRestriction.DS.Xi.TailInt p m (γ / 2 - e 0) (fun i => -e i.succ)) :=
        mul_le_mul_of_nonneg_left hkey zero_le
    _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg hCK0.le hCS0.le), ENNReal.ofReal_mul hCK0.le,
          ENNReal.ofReal_toReal hfin.ne]
        ring

end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi
