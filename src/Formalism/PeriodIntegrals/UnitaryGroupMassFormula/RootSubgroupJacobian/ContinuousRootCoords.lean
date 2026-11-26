module

public import Formalism.PeriodIntegrals.BetaLUniq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.NegOnePowMulSelf

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.TriShear
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.TriDefs
open MeasureTheory

namespace PI.AmpRootCommon.Tri

def TriShear : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (r : ι → ℕ) (g : ι → (ι → ℂ) → ℂ),
    (∀ i, Measurable (g i)) →
    (∀ i (x y : ι → ℂ), (∀ j, r j < r i → x j = y j) → g i x = g i y) →
    MeasurePreserving (fun x : ι → ℂ => fun i => x i + g i x) volume volume

end PI.AmpRootCommon.Tri
end

open MeasureTheory

noncomputable section

namespace PI.AmpRootCommon.Tri

def extNe {ι : Type} [DecidableEq ι] (a : ι) (y : {i // i ≠ a} → ℂ) : ι → ℂ :=
  fun j => if h : j ≠ a then y ⟨j, h⟩ else 0

theorem measurable_extNe {ι : Type} [DecidableEq ι] (a : ι) : Measurable (extNe a) := by
  refine Measurable.of_eval (fun j => ?_)
  by_cases h : j ≠ a
  · simp only [extNe, dif_pos h]
    exact measurable_pi_apply _
  · simp only [extNe, dif_neg h]
    exact measurable_const

theorem measurePreserving_of_card (n : ℕ) : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    ∀ (r : ι → ℕ) (g : ι → (ι → ℂ) → ℂ), (∀ i, Measurable (g i)) →
    (∀ i (x y : ι → ℂ), (∀ j, r j < r i → x j = y j) → g i x = g i y) →
    MeasurePreserving (fun x : ι → ℂ => fun i => x i + g i x) volume volume := by
  induction n with
  | zero =>
    intro ι _ _ hcard r g hg hdep
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard
    have hid : (fun x : ι → ℂ => fun i => x i + g i x) = id :=
      funext fun x => funext fun i => isEmptyElim i
    rw [hid]
    exact MeasurePreserving.id _
  | succ n ih =>
    intro ι _ _ hcard r g hg hdep
    have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨a, ha⟩ := Finite.exists_max r
    have hcard' : Fintype.card {i // i ≠ a} = n := by
      rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ a),
        Finset.card_univ, hcard]
      rfl
    have hext : ∀ i (x : ι → ℂ), g i x = g i (extNe a (fun j : {j // j ≠ a} => x j.1)) := by
      intro i x
      apply hdep i
      intro j hj
      by_cases hja : j ≠ a
      · simp only [extNe, dif_pos hja]
      · have hja' : j = a := not_not.mp hja
        rw [hja'] at hj
        have := ha i
        omega
    have hT := ih {i // i ≠ a} hcard' (fun i => r i.1)
      (fun i y => g i.1 (extNe a y))
      (fun i => (hg i.1).comp (measurable_extNe a))
      (fun i y y' hyy' => hdep i.1 _ _ (fun j hj => by
        by_cases hja : j ≠ a
        · simp only [extNe, dif_pos hja]
          exact hyy' ⟨j, hja⟩ hj
        · simp only [extNe, dif_neg hja]))
    have hc : Measurable (fun (y : {i // i ≠ a} → ℂ) (_ : {i // ¬ i ≠ a}) => g a (extNe a y)) :=
      Measurable.of_eval fun _ => (hg a).comp (measurable_extNe a)
    have hS : MeasurePreserving
        (fun p : ({i // i ≠ a} → ℂ) × ({i // ¬ i ≠ a} → ℂ) =>
          ((fun i => p.1 i + g i.1 (extNe a p.1)),
            p.2 + fun (_ : {i // ¬ i ≠ a}) => g a (extNe a p.1))) volume volume :=
      hT.skew_product (g := fun y z => z + fun (_ : {i // ¬ i ≠ a}) => g a (extNe a y))
        (measurable_snd.add (hc.comp measurable_fst))
        (ae_of_all _ fun y => map_add_right_eq_self volume _)
    have hΦ := volume_preserving_piEquivPiSubtypeProd (fun _ : ι => ℂ) (fun i => i ≠ a)
    have hF : (fun x : ι → ℂ => fun i => x i + g i x) =
        (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℂ) (fun i => i ≠ a)).symm ∘
          (fun p : ({i // i ≠ a} → ℂ) × ({i // ¬ i ≠ a} → ℂ) =>
            ((fun i => p.1 i + g i.1 (extNe a p.1)),
              p.2 + fun (_ : {i // ¬ i ≠ a}) => g a (extNe a p.1))) ∘
          (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℂ) (fun i => i ≠ a)) := by
      funext x i
      show x i + g i x = (if h : i ≠ a then _ else _)
      by_cases hi : i ≠ a
      · rw [dif_pos hi]
        show x i + g i x = x i + g i (extNe a (fun j : {j // j ≠ a} => x j.1))
        rw [← hext i x]
      · rw [dif_neg hi]
        show x i + g i x = x i + g a (extNe a (fun j : {j // j ≠ a} => x j.1))
        have hia : i = a := not_not.mp hi
        rw [hia, ← hext a x]
    rw [hF]
    exact (MeasurePreserving.symm _ hΦ).comp (hS.comp hΦ)

theorem triShear : TriShear :=
  fun ι _ _ r g hg hdep => measurePreserving_of_card (Fintype.card ι) ι rfl r g hg hdep

end PI.AmpRootCommon.Tri
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupJacobian.BlkLt
noncomputable section

namespace PI.AmpRootJacW

open Formalism.MainNotions.S PI.AmpRootCommon

theorem blk_lt : ∀ (bs : List (ℂ × ℕ)) (i j : ℕ), i < j → j < (bs.map Prod.snd).sum →
    blockIdx bs i ≠ blockIdx bs j → pv bs i < pv bs j
  | [], i, j, _, hj, _ => by simp at hj
  | (t, s) :: bs, i, j, hij, hj, hne => by
    simp only [List.map_cons, List.sum_cons] at hj
    simp only [blockIdx, pv] at hne ⊢
    by_cases hi : i < s
    · by_cases hjs : j < s
      · simp [hi, hjs] at hne
      · rw [ite_eq_left hi, ite_eq_right hjs]
        omega
    · have hjs : ¬ j < s := by omega
      simp only [ite_eq_right hi, ite_eq_right hjs] at hne ⊢
      have := blk_lt bs (i - s) (j - s) (by omega) (by omega) (fun e => hne (by rw [e]))
      omega

end PI.AmpRootJacW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupJacobian.SUpPowEqZero
open MeasureTheory Matrix

noncomputable section

namespace PI.AmpRootJacW

variable {n : ℕ}

def SUp (V : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ i j : Fin n, j.val ≤ i.val → V i j = 0

theorem sUp_neg {V : Matrix (Fin n) (Fin n) ℂ} (hV : SUp V) : SUp (-V) := by
  intro i j h
  simp [hV i j h]

theorem sUp_pow {V : Matrix (Fin n) (Fin n) ℂ} (hV : SUp V) :
    ∀ (m : ℕ) (i j : Fin n), j.val < i.val + m → (V ^ m) i j = 0
  | 0, i, j, h => by
    rw [pow_zero, Matrix.one_apply, if_neg]
    rintro rfl; omega
  | m + 1, i, j, h => by
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l.val < i.val + m
    · rw [sUp_pow hV m i l hl, zero_mul]
    · rw [hV l j (by omega), mul_zero]

theorem sUp_pow_eq_zero {V : Matrix (Fin n) (Fin n) ℂ} (hV : SUp V) (m : ℕ) (hm : n ≤ m) : V ^ m = 0 := by
  ext i j
  have hj := j.2
  simp only [Matrix.zero_apply]
  exact sUp_pow hV m i j (by omega)

def gInv (V : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ m ∈ Finset.range (n + 2), (-V) ^ m

theorem mul_gInv {V : Matrix (Fin n) (Fin n) ℂ} (hV : SUp V) : (1 + V) * gInv V = 1 := by
  unfold gInv
  have h := mul_neg_geom_sum (-V) (n + 2)
  rw [sub_neg_eq_add] at h
  rw [h, sUp_pow_eq_zero (sUp_neg hV) (n + 2) (by omega), sub_zero]

theorem pow_agree {V V' : Matrix (Fin n) (Fin n) ℂ} (hV : SUp V) (hV' : SUp V') (d : ℕ)
    (h : ∀ a b : Fin n, b.val ≤ a.val + d → V a b = V' a b) :
    ∀ (m : ℕ) (i j : Fin n), j.val ≤ i.val + d → (V ^ (m + 1)) i j = (V' ^ (m + 1)) i j
  | 0, i, j, hij => by rw [pow_one, pow_one]; exact h i j hij
  | m + 1, i, j, hij => by
    rw [pow_succ' V (m + 1), pow_succ' V' (m + 1), Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h1 : l.val ≤ i.val
    · rw [hV i l h1, hV' i l h1, zero_mul, zero_mul]
    by_cases h2 : j.val ≤ l.val
    · rw [sUp_pow hV (m + 1) l j (by omega), sUp_pow hV' (m + 1) l j (by omega), mul_zero, mul_zero]
    rw [h i l (by omega), pow_agree hV hV' d h m l j (by omega)]

theorem pow_apply_eq_of_agree {V V' : Matrix (Fin n) (Fin n) ℂ} (hV : SUp V) (hV' : SUp V') (g : ℕ)
    (h : ∀ a b : Fin n, b.val < a.val + g → V a b = V' a b) (m : ℕ) (i j : Fin n)
    (hij : j.val ≤ i.val + g) : (V ^ (m + 1 + 1)) i j = (V' ^ (m + 1 + 1)) i j := by
  rw [pow_succ, pow_succ V', Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases hk : k.val < i.val + (m + 1)
  · rw [sUp_pow hV (m + 1) i k hk, sUp_pow hV' (m + 1) i k hk, zero_mul, zero_mul]
  · by_cases hjk : j.val ≤ k.val
    · rw [hV k j hjk, hV' k j hjk, mul_zero, mul_zero]
    · have h' : ∀ a b : Fin n, b.val ≤ a.val + (g - 1) → V a b = V' a b := fun a b hab => h a b (by omega)
      rw [pow_agree hV hV' (g - 1) h' m i k (by omega), h k j (by omega)]

section Pat

variable (S : Finset (Fin n × Fin n))

def vM (v : S → ℂ) : Matrix (Fin n) (Fin n) ℂ := fun i j => if h : (i, j) ∈ S then v ⟨(i, j), h⟩ else 0

theorem vM_at (v : S → ℂ) (q : S) : vM S v q.1.1 q.1.2 = v q := by
  unfold vM
  rw [dite_eq_left q.2]

theorem sUp_vM (hS : ∀ q ∈ S, q.1 < q.2) (v : S → ℂ) : SUp (vM S v) := by
  intro i j hji
  unfold vM
  rw [dite_eq_right]
  intro hm
  have h1 : i < j := hS _ hm
  rw [Fin.lt_def] at h1
  omega

theorem continuous_vM : Continuous (vM S) := by
  unfold vM
  refine continuous_pi fun i => continuous_pi fun j => ?_
  split_ifs with h
  · exact continuous_apply _
  · exact continuous_const

def invC (v : S → ℂ) : S → ℂ := fun q => gInv (vM S v) q.1.1 q.1.2

def rk (q : S) : ℕ := q.1.2.val - q.1.1.val

def hSh (q : S) (v : S → ℂ) : ℂ :=
  -(∑ m ∈ Finset.range n, ((-vM S v) ^ (m + 1 + 1)) q.1.1 q.1.2)

theorem invC_eq (hS : ∀ q ∈ S, q.1 < q.2) (v : S → ℂ) (q : S) : invC S v q = -(v q + hSh S q v) := by
  unfold invC gInv hSh
  rw [Matrix.sum_apply, Finset.sum_range_succ', Finset.sum_range_succ']
  have hq : q.1.1 ≠ q.1.2 := ne_of_lt (hS q.1 q.2)
  simp only [pow_zero, zero_add, pow_one, add_zero, Matrix.one_apply_ne hq, Matrix.neg_apply, vM_at]
  ring

theorem hSh_dep (hS : ∀ q ∈ S, q.1 < q.2) (q : S) (v w : S → ℂ) (h : ∀ p, rk S p < rk S q → v p = w p) :
    hSh S q v = hSh S q w := by
  unfold hSh
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have hq : q.1.1 < q.1.2 := hS q.1 q.2
  rw [Fin.lt_def] at hq
  have hr : rk S q = q.1.2.val - q.1.1.val := rfl
  refine pow_apply_eq_of_agree (sUp_neg (sUp_vM S hS v)) (sUp_neg (sUp_vM S hS w)) (rk S q) ?_ m q.1.1 q.1.2 ?_
  · intro a b hab
    simp only [Matrix.neg_apply, vM]
    split_ifs with hm
    · rw [h ⟨(a, b), hm⟩ ?_]
      show b.val - a.val < rk S q
      rw [hr] at hab ⊢
      omega
    · rfl
  · rw [hr]
    omega

theorem continuous_hSh (q : S) : Continuous (hSh S q) := by
  unfold hSh
  refine Continuous.neg (continuous_finsetSum _ (fun m _ => ?_))
  have h1 : Continuous (fun v : S → ℂ => (-vM S v) ^ (m + 1 + 1)) := ((continuous_vM S).neg).pow _
  exact h1.matrix_elem q.1.1 q.1.2

theorem shear_mp (hS : ∀ q ∈ S, q.1 < q.2) :
    MeasurePreserving (fun v : S → ℂ => fun q => v q + hSh S q v) volume volume := by
  exact PI.AmpRootCommon.Tri.measurePreserving_of_card (Fintype.card S) S rfl (rk S) (fun q v => hSh S q v)
    (fun q => (continuous_hSh S q).measurable) (fun q x y hxy => hSh_dep S hS q x y hxy)

end Pat

theorem mp_reindex {ι : Type} [Fintype ι] (τ : ι ≃ ι) :
    MeasurePreserving (fun (w : ι → ℂ) i => w (τ i)) volume volume := by
  have h := MeasureTheory.volume_preserving_arrowCongr' τ.symm (MeasurableEquiv.refl ℂ) (MeasurePreserving.id volume)
  convert h using 1
  all_goals first
    | rfl
    | (funext w i; simp [MeasurableEquiv.arrowCongr', Equiv.arrowCongr'])

theorem mp_unitConj1 (c : ℂ) (hc : ‖c‖ = 1) : MeasurePreserving (fun x : ℂ => c * star x) volume volume := by
  let u : Circle := ⟨c, by simp [Submonoid.unitSphere, hc]⟩
  have h := ((Complex.conjLIE).trans (rotation u)).measurePreserving
  convert h using 1
  all_goals first
    | rfl
    | (funext x; simp only [LinearIsometryEquiv.trans_apply, rotation_apply, Complex.conjLIE_apply]; rfl)

theorem mp_unitConj {ι : Type} [Fintype ι] (τ : ι ≃ ι) (c : ι → ℂ) (hc : ∀ i, ‖c i‖ = 1) :
    MeasurePreserving (fun (w : ι → ℂ) i => c i * star (w (τ i))) volume volume := by
  have h1 : MeasurePreserving (fun (x : ι → ℂ) i => c i * star (x i)) volume volume :=
    MeasureTheory.volume_preserving_pi (fun i => mp_unitConj1 (c i) (hc i))
  exact h1.comp (mp_reindex τ)

theorem phi_mp (S : Finset (Fin n × Fin n)) (hS : ∀ q ∈ S, q.1 < q.2) (τ : S ≃ S) (c : S → ℂ)
    (hc : ∀ q, ‖c q‖ = 1) :
    MeasurePreserving (fun (v : S → ℂ) q => c q * star (invC S v (τ q))) volume volume := by
  have h1 := mp_unitConj τ (fun q => -c q) (fun q => by rw [norm_neg]; exact hc q)
  have h2 := shear_mp S hS
  convert h1.comp h2 using 1
  funext v q
  simp only [Function.comp_apply, invC_eq S hS v (τ q), star_neg, star_add]
  ring

end PI.AmpRootJacW
end
end

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace PI.AmpRootJacW

open Formalism.QuantumDeterminants Formalism.MainNotions.S PI.AmpRootCommon

variable {k r : ℕ}

theorem rootPat_lt (p : Point ℂ (r + 1)) : ∀ q ∈ rootPat p, q.1 < q.2 := by
  intro q hq
  exact (Finset.mem_filter.mp hq).2.1

theorem mem_rootPat {p : Point ℂ (r + 1)} {i j : Fin (r + 1)} :
    (i, j) ∈ rootPat p ↔ i < j ∧ blockIdx p.1 i.val = blockIdx p.1 j.val := by
  simp only [rootPat, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem pv_cons_eq (t : ℂ) (s : ℕ) (bs : List (ℂ × ℕ)) (i : ℕ) :
    pv ((t, s) :: bs) i = if i < s then s - 1 - i else s + pv bs (i - s) := rfl

private theorem blockIdx_cons_eq (t : ℂ) (s : ℕ) (bs : List (ℂ × ℕ)) (i : ℕ) :
    blockIdx ((t, s) :: bs) i = if i < s then 0 else 1 + blockIdx bs (i - s) := rfl

private theorem ptEntry_cons_eq (t : ℂ) (s : ℕ) (bs : List (ℂ × ℕ)) (i j : ℕ) :
    ptEntry ((t, s) :: bs) i j =
      if i < s ∧ j < s then (if i + j + 1 = s then t else 0)
      else if s ≤ i ∧ s ≤ j then ptEntry bs (i - s) (j - s) else 0 := rfl

private theorem blockIdx_pv_eq : ∀ (bs : List (ℂ × ℕ)) (i : ℕ), i < (bs.map Prod.snd).sum →
    blockIdx bs (pv bs i) = blockIdx bs i
  | [], i, h => by simp at h
  | (t, s) :: bs, i, h => by
    simp only [List.map_cons, List.sum_cons] at h
    by_cases hi : i < s
    · have h1 : s - 1 - i < s := by omega
      simp only [pv_cons_eq, blockIdx_cons_eq, hi, h1, ↓reduceIte]
    · have ih := blockIdx_pv_eq bs (i - s) (by omega)
      have h1 : ¬ (s + pv bs (i - s) < s) := by omega
      simp only [pv_cons_eq, blockIdx_cons_eq, hi, h1, ↓reduceIte, Nat.add_sub_cancel_left, ih]

private theorem pv_lt_pv_of_lt_of_blockIdx_eq : ∀ (bs : List (ℂ × ℕ)) (i j : ℕ), i < j → blockIdx bs i = blockIdx bs j →
    j < (bs.map Prod.snd).sum → pv bs j < pv bs i
  | [], i, j, _, _, h => by simp at h
  | (t, s) :: bs, i, j, hij, hb, h => by
    simp only [List.map_cons, List.sum_cons] at h
    by_cases hj : j < s
    · have hi : i < s := by omega
      simp only [pv_cons_eq, hi, hj, ↓reduceIte]
      omega
    · by_cases hi : i < s
      · simp only [blockIdx_cons_eq, hi, hj, ↓reduceIte] at hb
        omega
      · have hb' : blockIdx bs (i - s) = blockIdx bs (j - s) := by
          simp only [blockIdx_cons_eq, hi, hj, ↓reduceIte] at hb
          omega
        have ih := pv_lt_pv_of_lt_of_blockIdx_eq bs (i - s) (j - s) (by omega) hb' (by omega)
        simp only [pv_cons_eq, hi, hj, ↓reduceIte]
        omega

theorem tau_mem {p : Point ℂ (r + 1)} (q : rootPat p) : (ptσ p q.1.2, ptσ p q.1.1) ∈ rootPat p := by
  obtain ⟨hlt, hb⟩ := (mem_rootPat (i := q.1.1) (j := q.1.2)).mp q.2
  have hs : (p.1.map Prod.snd).sum = r + 1 := p.2.2
  have h1 := q.1.1.2
  have h2 := q.1.2.2
  rw [mem_rootPat]
  refine ⟨?_, ?_⟩
  · show pv p.1 q.1.2.val < pv p.1 q.1.1.val
    exact pv_lt_pv_of_lt_of_blockIdx_eq p.1 _ _ hlt hb (by omega)
  · show blockIdx p.1 (pv p.1 q.1.2.val) = blockIdx p.1 (pv p.1 q.1.1.val)
    rw [blockIdx_pv_eq p.1 _ (by omega), blockIdx_pv_eq p.1 _ (by omega)]
    exact hb.symm

def tauE (p : Point ℂ (r + 1)) : rootPat p ≃ rootPat p where
  toFun q := ⟨(ptσ p q.1.2, ptσ p q.1.1), tau_mem q⟩
  invFun q := ⟨(ptσ p q.1.2, ptσ p q.1.1), tau_mem q⟩
  left_inv q := by
    apply Subtype.ext
    simp only [ptσ_invol, Prod.mk.eta]
  right_inv q := by
    apply Subtype.ext
    simp only [ptσ_invol, Prod.mk.eta]

def cU (p : Point ℂ (r + 1)) (q : rootPat p) : ℂ := star (ptζ p q.1.2) / star (ptζ p q.1.1)

theorem norm_ptζ (p : Point ℂ (r + 1)) (i : Fin (r + 1)) :
    ‖ptζ p i‖ = ‖ptEntry p.1 i.val (pv p.1 i.val)‖ := by
  simp only [ptζ, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rfl

private theorem ptEntry_pv_eq_of_blockIdx_eq : ∀ (bs : List (ℂ × ℕ)) (i j : ℕ), blockIdx bs i = blockIdx bs j →
    i < (bs.map Prod.snd).sum → j < (bs.map Prod.snd).sum → ptEntry bs i (pv bs i) = ptEntry bs j (pv bs j)
  | [], i, _, _, h, _ => by simp at h
  | (t, s) :: bs, i, j, hb, hi', hj' => by
    simp only [List.map_cons, List.sum_cons] at hi' hj'
    by_cases hi : i < s <;> by_cases hj : j < s
    · have e1 : i + (s - 1 - i) + 1 = s := by omega
      have e2 : j + (s - 1 - j) + 1 = s := by omega
      have l1 : s - 1 - i < s := by omega
      have l2 : s - 1 - j < s := by omega
      simp only [pv_cons_eq, ptEntry_cons_eq, hi, hj, l1, l2, e1, e2, and_self, ↓reduceIte]
    · simp only [blockIdx_cons_eq, hi, hj, ↓reduceIte] at hb
      omega
    · simp only [blockIdx_cons_eq, hi, hj, ↓reduceIte] at hb
      omega
    · have hb' : blockIdx bs (i - s) = blockIdx bs (j - s) := by
        simp only [blockIdx_cons_eq, hi, hj, ↓reduceIte] at hb
        omega
      have ih := ptEntry_pv_eq_of_blockIdx_eq bs (i - s) (j - s) hb' (by omega) (by omega)
      have g1 : s ≤ i := by omega
      have g2 : s ≤ j := by omega
      have g3 : s ≤ s + pv bs (i - s) := Nat.le_add_right _ _
      have g4 : s ≤ s + pv bs (j - s) := Nat.le_add_right _ _
      simp only [pv_cons_eq, ptEntry_cons_eq, hi, hj, g1, g2, g3, g4, false_and, and_self, ↓reduceIte,
        Nat.add_sub_cancel_left, ih]

theorem norm_cU (p : Point ℂ (r + 1)) (q : rootPat p) : ‖cU p q‖ = 1 := by
  obtain ⟨_, hb⟩ := (mem_rootPat (i := q.1.1) (j := q.1.2)).mp q.2
  have hs : (p.1.map Prod.snd).sum = r + 1 := p.2.2
  have h1 := q.1.1.2
  have h2 := q.1.2.2
  have e : ‖ptζ p q.1.2‖ = ‖ptζ p q.1.1‖ := by
    rw [norm_ptζ, norm_ptζ, ptEntry_pv_eq_of_blockIdx_eq p.1 q.1.2.val q.1.1.val hb.symm (by omega) (by omega)]
  have hne : ‖ptζ p q.1.1‖ ≠ 0 := norm_ne_zero_iff.mpr (ptζ_ne p _)
  simp only [cU, norm_div, norm_star, e]
  exact div_self hne

def phiR (p : Point ℂ (r + 1)) (v : rootPat p → ℂ) : rootPat p → ℂ :=
  fun q => cU p q * star (invC (rootPat p) v (tauE p q))

theorem phiR_mp (p : Point ℂ (r + 1)) : MeasurePreserving (phiR p) volume volume :=
  phi_mp _ (rootPat_lt p) (tauE p) (cU p) (norm_cU p)

theorem conj_back {g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g₀ ∈ UH (Hpk k r))
    (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : g₀⁻¹ * (g₀ * X * g₀⁻¹) * g₀ = X := by
  have hH : (Hpk k r).det ≠ 0 := by
    intro h0
    have h2 := congrArg Matrix.det (Hpk_mul_self (k := k) (r := r))
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h2
    exact zero_ne_one h2
  have hdet := congrArg Matrix.det (show g₀ᴴ * Hpk k r * g₀ = Hpk k r from hg)
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have hu : IsUnit g₀.det := isUnit_iff_ne_zero.mpr fun h0 => by
    rw [h0, mul_zero] at hdet
    exact hH hdet.symm
  have h1 : g₀⁻¹ * g₀ = 1 := Matrix.nonsing_inv_mul _ hu
  calc g₀⁻¹ * (g₀ * X * g₀⁻¹) * g₀ = (g₀⁻¹ * g₀) * X * (g₀⁻¹ * g₀) := by simp only [Matrix.mul_assoc]
    _ = X := by rw [h1, Matrix.one_mul, Matrix.mul_one]

private theorem pv_lt_pv_of_lt_of_blockIdx_ne : ∀ (bs : List (ℂ × ℕ)) (i j : ℕ), i < j → blockIdx bs i ≠ blockIdx bs j →
    j < (bs.map Prod.snd).sum → pv bs i < pv bs j
  | [], i, j, _, _, h => by simp at h
  | (t, s) :: bs, i, j, hij, hb, h => by
    simp only [List.map_cons, List.sum_cons] at h
    by_cases hj : j < s
    · have hi : i < s := by omega
      simp only [blockIdx_cons_eq, hi, hj, ↓reduceIte] at hb
      exact absurd rfl hb
    · by_cases hi : i < s
      · simp only [pv_cons_eq, hi, hj, ↓reduceIte]
        omega
      · have hb' : blockIdx bs (i - s) ≠ blockIdx bs (j - s) := by
          intro he
          apply hb
          simp only [blockIdx_cons_eq, hi, hj, ↓reduceIte, he]
        have ih := pv_lt_pv_of_lt_of_blockIdx_ne bs (i - s) (j - s) (by omega) hb' (by omega)
        simp only [pv_cons_eq, hi, hj, ↓reduceIte]
        omega

theorem flag_eq_one_add {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    {g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {p : Point ℂ (r + 1)}
    (hg : g₀ ∈ UH (Hpk k r)) (hP : ZhatO k r z z' g₀ = ptMat p)
    {x : Mt k r} (hx : Matrix.of x ∈ Rset k r g₀) :
    flagMat k r z' (Matrix.of x) = 1 + vM (rootPat p) (rootCoords k r z' p x) := by
  have hN : Matrix.of x ∈ Nset k r := hx.1
  have ha : g₀ * Matrix.of x * g₀⁻¹ ∈ RStab k r g₀ := ⟨hx.2, by rw [conj_back hg]; exact hx.1⟩
  have hs : (p.1.map Prod.snd).sum = r + 1 := p.2.2
  ext i j
  simp only [Matrix.add_apply, vM]
  by_cases hm : (i, j) ∈ rootPat p
  · rw [dite_eq_left hm]
    have hij : i ≠ j := ne_of_lt ((mem_rootPat.mp hm).1)
    rw [Matrix.one_apply_ne hij, zero_add]
    rfl
  · rw [dite_eq_right hm, add_zero]
    by_cases hji : j ≤ i
    · rw [flagMat_lower hN i j hji, Matrix.one_apply]
    · have hij : i < j := not_le.mp hji
      have hb : blockIdx p.1 i.val ≠ blockIdx p.1 j.val := fun h => hm (mem_rootPat.mpr ⟨hij, h⟩)
      have hj2 := j.2
      have hlt : (ptσ p i).val < (ptσ p j).val :=
        pv_lt_pv_of_lt_of_blockIdx_ne p.1 _ _ hij hb (by omega)
      have h0 := (flag_offblock hz hz' hg hP ha i j hlt).1
      rw [conj_back hg] at h0
      rw [h0, Matrix.one_apply_ne (ne_of_lt hij)]

theorem rootCoords_conj {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    {g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {p : Point ℂ (r + 1)}
    (hg : g₀ ∈ UH (Hpk k r)) (hP : ZhatO k r z z' g₀ = ptMat p)
    {x : Mt k r} (hx : Matrix.of x ∈ Rset k r g₀) :
    rootCoords k r z p (fun i j => (g₀ * Matrix.of x * g₀⁻¹) i j) = phiR p (rootCoords k r z' p x) := by
  have hF' : flagMat k r z' (Matrix.of x) = 1 + vM (rootPat p) (rootCoords k r z' p x) :=
    flag_eq_one_add hz hz' hg hP hx
  have hG : (1 + vM (rootPat p) (rootCoords k r z' p x)) * gInv (vM (rootPat p) (rootCoords k r z' p x)) = 1 :=
    mul_gInv (sUp_vM (rootPat p) (rootPat_lt p) _)
  have hrel := flag_rel_Rset hz hz' hg hx
  rw [hF'] at hrel
  have key : (flagMat k r z (g₀ * Matrix.of x * g₀⁻¹))ᴴ * Zhat k r z z' g₀ =
      Zhat k r z z' g₀ * gInv (vM (rootPat p) (rootCoords k r z' p x)) := by
    calc _ = (flagMat k r z (g₀ * Matrix.of x * g₀⁻¹))ᴴ * Zhat k r z z' g₀ *
          ((1 + vM (rootPat p) (rootCoords k r z' p x)) * gInv (vM (rootPat p) (rootCoords k r z' p x))) := by
          rw [hG, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hrel]
  have inj : ∀ a b : Fin (r + 1), ptσ p a = ptσ p b ↔ a = b := fun a b =>
    ⟨fun h => by simpa only [ptσ_invol] using congrArg (ptσ p) h, fun h => h ▸ rfl⟩
  funext q
  have e := congrFun (congrFun key q.1.2) (ptσ p q.1.1)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, zhat_pt hP, inj, mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at e
  have e2 := congrArg star e
  simp only [star_mul', star_star] at e2
  have hne : star (ptζ p q.1.1) ≠ 0 := star_ne_zero.mpr (ptζ_ne p _)
  show flagMat k r z (g₀ * Matrix.of x * g₀⁻¹) q.1.1 q.1.2 =
    star (ptζ p q.1.2) / star (ptζ p q.1.1) *
      star (gInv (vM (rootPat p) (rootCoords k r z' p x)) (ptσ p q.1.2) (ptσ p q.1.1))
  field_simp
  linear_combination e2

theorem measurable_conjM (a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (fun x : Mt k r => fun i j => (a * Matrix.of x * b) i j) := by
  have hc : Continuous (fun x : Mt k r => fun i j => (a * Matrix.of x * b) i j) :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
  exact hc.measurable

theorem continuous_rootCoords (z : Fin (2 * r + k + 1) → ℂ) (p : Point ℂ (r + 1)) :
    Continuous (rootCoords k r z p) := by
  refine continuous_pi fun q => ?_
  simp only [rootCoords, flagMat]
  by_cases hi : q.1.1.val < r
  · simp only [hi, ↓reduceDIte]
    fun_prop
  · simp only [hi, ↓reduceDIte]
    exact continuous_const

theorem cont_of : Continuous (fun x : Mt k r => (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :=
  continuous_id

theorem isClosed_N : IsClosed {x : Mt k r | Matrix.of x ∈ Nset k r} := by
  have hc : Continuous (fun x : Mt k r => (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :=
    cont_of
  simp only [Nset, UH, Set.mem_ofPred_eq, Set.ofPred_and, Set.ofPred_forall]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
  · exact isClosed_eq ((hc.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hc) continuous_const
  · exact isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq (hc.matrix_elem _ _) continuous_const
  · exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_eq (hc.matrix_elem _ _) continuous_const

theorem measurableSet_RStab (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    MeasurableSet {x : Mt k r | Matrix.of x ∈ RStab k r g} := by
  have hf : Continuous (fun x : Mt k r => (fun i j => (g⁻¹ * Matrix.of x * g) i j : Mt k r)) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have h2 : IsClosed {x : Mt k r | g⁻¹ * Matrix.of x * g ∈ Nset k r} := isClosed_N.preimage hf
  exact (isClosed_N.inter h2).measurableSet

theorem rootJac : PI.AmpRoot.RootJac := by
  intro k r L p g₀ μ₀ hrep _ hnull hmap
  obtain ⟨hg, hP⟩ := hrep
  have hz := L.hz.1
  have hz' := L.hz'.1
  have hf : Measurable (fun x : Mt k r => fun i j => (g₀ * Matrix.of x * g₀⁻¹) i j) := measurable_conjM _ _
  have hae : ∀ᵐ x ∂μ₀, Matrix.of x ∈ Rset k r g₀ := ae_iff.mpr hnull
  refine ⟨?_, ?_⟩
  · have hs : MeasurableSet {x : Mt k r | Matrix.of x ∉ RStab k r g₀} := (measurableSet_RStab g₀).compl
    rw [Measure.map_apply hf hs]
    refine measure_mono_null ?_ hnull
    intro x hx
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hx ⊢
    intro hR
    exact hx ⟨hR.2, (show g₀⁻¹ * (g₀ * Matrix.of x * g₀⁻¹) * g₀ ∈ Nset k r by rw [conj_back hg]; exact hR.1)⟩
  · rw [Measure.map_map (continuous_rootCoords L.z p).measurable hf]
    have hcongr : (rootCoords k r L.z p ∘ fun x : Mt k r => fun i j => (g₀ * Matrix.of x * g₀⁻¹) i j)
        =ᵐ[μ₀] (phiR p ∘ rootCoords k r L.z' p) := by
      filter_upwards [hae] with x hx
      exact rootCoords_conj hz hz' hg hP hx
    rw [Measure.map_congr hcongr,
      ← Measure.map_map (phiR_mp p).measurable (continuous_rootCoords L.z' p).measurable, hmap,
      Measure.map_smul _ (phiR_mp p).measurable.aemeasurable, (phiR_mp p).map_eq]

end PI.AmpRootJacW
