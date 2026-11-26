module

public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopTwistDensOfZeta
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnFibMem

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGHead
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal

theorem mono_omit {k r m : ℕ} (hm : m + 1 ≤ r) (c : Fin m → Fin (2 * r + k + 1)) (hc : StrictMono c)
    (hlt : ∀ l, (c l).val < m + 1) : ∃ l0 : Fin (m + 1), c = xR k r (m + 1) hm ∘ l0.succAbove := by
  have hex : ∃ l0 : Fin (m + 1), ∀ l, (c l).val ≠ l0.val := by
    by_contra hne
    push Not at hne
    choose f hf using hne
    have hinj : Function.Injective f := by
      intro a b hab
      apply Fin.ext
      have := hf a; have := hf b; rw [hab] at *; omega
    have := Fintype.card_le_of_injective f hinj
    simp at this
  obtain ⟨l0, hl0⟩ := hex
  refine ⟨l0, ?_⟩
  apply uniq_mono _ _ ?_ hc
  · intro l
    have h1 : (⟨(c l).val, hlt l⟩ : Fin (m + 1)) ≠ l0 := by
      intro h; apply hl0 l; rw [← h]
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq h1
    refine ⟨j, ?_⟩
    ext
    simp only [Function.comp_apply, xR, eI, Fin.val_castLE]
    rw [hj]
  · exact (fun a b hab => by simp only [Function.comp_apply, xR, eI]; exact Fin.strictMono_succAbove l0 hab)

theorem omit_inj {k r m : ℕ} (hm : m + 1 ≤ r) :
    Function.Injective (fun l0 : Fin (m + 1) => xR k r (m + 1) hm ∘ l0.succAbove) := by
  intro l0 l1 h
  apply Fin.succAbove_left_injective
  funext l
  have h2 := congrArg Fin.val (congrFun h l)
  exact Fin.ext (by simpa [C3.xR, eI] using h2)

theorem AAx_omit {A : Type} [Ring A] [Algebra ℂ A] (k r m : ℕ) (hm : m + 1 ≤ r)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (xi : Fin r → Fin (2 * r + k + 1) → ℂ) (u : ℂ)
    (hz : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < m → m + 1 ≤ p.val → xi a p = 0) :
    AAx k r E xi m (by omega) u = ∑ l0 : Fin (m + 1),
      (Matrix.of fun a l : Fin m => xi (Fin.castLE (by omega) a) (xR k r (m + 1) hm (l0.succAbove l))).det •
        qminor E (xR k r m (by omega)) (xR k r (m + 1) hm ∘ l0.succAbove) u := by
  classical
  unfold AAx
  set g := fun l0 : Fin (m + 1) => xR k r (m + 1) hm ∘ l0.succAbove
  have hg : Function.Injective g := omit_inj hm
  have hsub : Finset.image g Finset.univ ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_image (fun a _ b _ h => hg h)]
    apply Finset.sum_congr rfl
    intro l0 _
    rw [if_pos]
    · rfl
    · intro a b hab; simp only [g, Function.comp_apply, xR, eI]; exact Fin.strictMono_succAbove l0 hab
  · intro c _ hc
    split_ifs with hP
    · by_cases hS : ∀ l, (c l).val < m + 1
      · obtain ⟨l0, hl0⟩ := mono_omit hm c hP hS
        exact absurd (Finset.mem_image.2 ⟨l0, Finset.mem_univ _, hl0.symm⟩) hc
      · push Not at hS
        obtain ⟨l, hl⟩ := hS
        rw [Matrix.det_eq_zero_of_column_eq_zero l (fun a => by
          simp only [Matrix.of_apply]; exact hz _ _ (by simp) hl), zero_smul]
    · rfl

theorem inv_last {m : ℕ} (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hZ : Z.det ≠ 0) (b : Fin (m + 1)) :
    Z⁻¹ b (Fin.last m) = Z.det⁻¹ * ((-1) ^ (m + (b : ℕ)) * (Z.submatrix Fin.castSucc b.succAbove).det) := by
  rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last, Fin.val_last,
    smul_eq_mul, Ring.inverse_eq_inv']

theorem _root_.Formalism.FourierDecayAlt.P.head_algebra_relations : Formalism.FourierDecayAlt.KB.HeadAlg := by
  intro A _ _ M _ _ k r m hm z' E La xi Z c u hG hR hZ hc hL hxi hxl
  have hxi' : ∀ (a : Fin r) (q : Fin (2 * r + k + 1)) (ha : a.val < m + 1),
      xi a q = if h : q.val < m + 1 then Z ⟨a.val, ha⟩ ⟨q.val, h⟩ else 0 := by
    intro a q ha; have := hxi ⟨a.val, ha⟩ q; simpa using this
  have hxl' : ∀ (a : Fin r) (q : Fin (2 * r + k + 1)), a.val = m + 1 → xi a q = if q.val = m + 1 then c else 0 := by
    intro a q ha
    have e : a = ⟨m + 1, by omega⟩ := Fin.ext ha
    rw [e]; exact hxl q

  have hA2 : AAx k r E xi (m + 2) hm u = (Z.det * c) • qminor E (xR k r (m + 2) hm) (xR k r (m + 2) hm) u := by
    rw [AAx_head k r E xi (m + 2) hm (Matrix.of fun a b : Fin (m + 2) => xi (Fin.castLE hm a) (xR k r (m + 2) hm b)) u
      ?_ (fun a b => rfl)]
    · congr 1
      rw [Matrix.det_succ_row _ (Fin.last (m + 1)), Fin.sum_univ_castSucc, Finset.sum_eq_zero]
      · simp only [Matrix.of_apply, Matrix.submatrix, Fin.succAbove_last, zero_add]
        have h1 : xi (Fin.castLE hm (Fin.last (m + 1))) (xR k r (m + 2) hm (Fin.last (m + 1))) = c := by
          rw [hxl' _ _ (by simp), if_pos (by simp [xR, eI])]
        rw [h1]
        have h2 : (Matrix.of fun i j : Fin (m + 1) => xi (Fin.castLE hm (Fin.castSucc i))
            (xR k r (m + 2) hm (Fin.castSucc j))) = Z := by
          ext i j
          simp only [Matrix.of_apply]
          rw [hxi' _ _ (by simp <;> omega), dite_eq_left (by simp [xR, eI] <;> omega)]
          congr 1
        rw [h2]
        simp only [Fin.val_last]
        rw [← two_mul, pow_mul]; norm_num; ring
      · intro j _
        simp only [Matrix.of_apply]
        rw [hxl' _ _ (by simp), if_neg (by simp [xR, eI]; omega)]
        ring
    · intro a p ha hp
      by_cases ha' : a.val < m + 1
      · rw [hxi' a p ha', dite_eq_right (by omega)]
      · rw [hxl' a p (by omega), if_neg (by omega)]
  have hA1 : AAx k r E xi (m + 1) (by omega) u = Z.det • qminor E (xR k r (m + 1) (by omega)) (xR k r (m + 1) (by omega)) u := by
    rw [AAx_head k r E xi (m + 1) (by omega) Z u]
    · intro a p ha hp
      rw [hxi' a p ha, dite_eq_right (by omega)]
    · intro a b
      rw [hxi' _ _ (by simp <;> omega), dite_eq_left (by simp [xR, eI] <;> omega)]
      congr 1
  have hA0 : AAx k r E xi m (by omega) u = ∑ l0 : Fin (m + 1),
      (Z.submatrix Fin.castSucc l0.succAbove).det •
        qminor E (xR k r m (by omega)) (xR k r (m + 1) (by omega) ∘ l0.succAbove) u := by
    rw [AAx_omit k r m (by omega) E xi u]
    · apply Finset.sum_congr rfl
      intro l0 _
      congr 2
      ext a l
      simp only [Matrix.of_apply, Matrix.submatrix_apply]
      rw [hxi' _ _ (by simp <;> omega), dite_eq_left (by simp [xR, eI] <;> omega)]
      congr 1
    · intro a p ha hp
      rw [hxi' a p (by omega), dite_eq_right (by omega)]

  set a := xR k r (m + 2) hm with hadef
  have hav : ∀ l, (a l).val = l.val := by intro l; simp [a, xR, eI]
  have hcs : a ∘ Fin.castSucc = xR k r (m + 1) (by omega) := by
    funext l; ext; simp [a, xR, eI]
  have hmain : La (qminor E a a u) = La (qminor E (xR k r (m + 1) (by omega)) (xR k r (m + 1) (by omega)) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) -
      La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) := by
    have hexp := Formalism.FourierDecayAlt.P.expansion_last_column A _ (m + 1) E a a u
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hexp, map_sum, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have hzero : ∀ l : Fin m, La ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.castSucc l) : Fin (m + 2)) : ℕ)) : ℤ) : A) *
        (qminor E (a ∘ (Fin.castSucc (Fin.castSucc l)).succAbove) (a ∘ Fin.castSucc) u *
          Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.castSucc l))) (a (Fin.last (m + 1))))) = 0 := by
      intro l
      rw [la_intmul]
      have hne : a (Fin.castSucc (Fin.castSucc l)) ≠ a (Fin.last (m + 1)) := by
        intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this; omega
      rw [tm_offdiag _ _ hne, hR _ _ _ (by simp only [InNp, hav]; simp; omega)]
      have : dpsiP k r z' (a (Fin.castSucc (Fin.castSucc l))) (a (Fin.last (m + 1))) = 0 := by
        unfold dpsiP; simp only [hav]; simp; split_ifs <;> first | rfl | omega
      rw [this, zero_smul, smul_zero]
    rw [Finset.sum_eq_zero (fun l _ => hzero l), zero_add]
    have hlast : La ((((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ)) : ℤ) : A) *
        (qminor E (a ∘ (Fin.last (m + 1)).succAbove) (a ∘ Fin.castSucc) u *
          Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.last (m + 1))) (a (Fin.last (m + 1))))) =
        La (qminor E (xR k r (m + 1) (by omega)) (xR k r (m + 1) (by omega)) u *
          Tm E (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) := by
      rw [la_intmul, Fin.succAbove_last, hcs]
      have h1 : a (Fin.last (m + 1)) = eI k r ⟨m + 1, by omega⟩ := by ext; rw [hav]; simp [eI]
      rw [h1]
      have h2 : ((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ))) = 1 := by
        simp only [Fin.val_last]; rw [← two_mul, pow_mul]; norm_num
      rw [h2]; simp
    rw [hlast]
    have hmT : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.last m))) (a (Fin.last (m + 1)))) =
        La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) := by
      have hne : a (Fin.castSucc (Fin.last m)) ≠ a (Fin.last (m + 1)) := by
        intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this
      rw [tm_offdiag _ _ hne, hR _ _ _ (by simp only [InNp, hav]; simp; omega)]
      have : dpsiP k r z' (a (Fin.castSucc (Fin.last m))) (a (Fin.last (m + 1))) = 1 := by
        unfold dpsiP; simp only [hav]; simp; split_ifs <;> first | rfl | omega
      rw [this, one_smul]
    rw [la_intmul, hmT]
    have h3 : ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.last m) : Fin (m + 2)) : ℕ))) : ℤ) : ℂ) = -1 := by
      simp only [Fin.val_castSucc, Fin.val_last]
      push_cast
      rw [show m + 1 + m = 2 * m + 1 by ring, pow_succ, pow_mul]; norm_num
    rw [h3, neg_one_smul]; abel

  set rowsP : Fin (m + 1) → Fin (2 * r + k + 1) := Fin.cons (eI k r ⟨m + 1, by omega⟩) (xR k r m (by omega)) with hrP
  have hrows : a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove = rowsP ∘ (finRotate (m + 1)) := by
    funext q
    ext
    simp only [Function.comp_apply]
    by_cases hq : q = Fin.last m
    · subst hq
      rw [finRotate_last]
      simp only [rowsP, Fin.cons_zero]
      rw [hav, succAbove_val]; simp [eI]
    · have hq' : q.val < m := by
        have := q.isLt; have : q.val ≠ m := fun h' => hq (Fin.ext (by simp [h'])); omega
      have hr1 : finRotate (m + 1) q = Fin.succ ⟨q.val, hq'⟩ := by
        ext; rw [coe_finRotate_of_ne_last hq]; simp
      rw [hr1]
      simp only [rowsP, Fin.cons_succ]
      rw [hav, succAbove_val]; simp [xR, eI]; omega
  have hQ : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) =
      ∑ l : Fin (m + 1), ((-1 : ℂ) ^ (m + (l : ℕ)) * (c * Z⁻¹ l (Fin.last m))) •
        La (qminor E (xR k r m (by omega)) (xR k r (m + 1) (by omega) ∘ l.succAbove) u) := by
    rw [hrows, Formalism.REAL.quantumMinorRowSkew_holds A _ (m + 1) E rowsP _ (finRotate (m + 1)) u, la_intmul, sign_finRotate]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Formalism.FourierDecayAlt.P.expansion_first_line A _ m E hG rowsP _ u, map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [la_intmul]
    have hr0 : rowsP 0 = eI k r ⟨m + 1, by omega⟩ := by simp [rowsP]
    have hrs : rowsP ∘ Fin.succ = xR k r m (by omega) := by funext q; simp [rowsP]
    rw [hr0, hrs, hcs]
    have hx : xR k r (m + 1) (by omega) l = eI k r ⟨l.val, by omega⟩ := by ext; simp [xR, eI]
    have hne : eI k r ⟨m + 1, by omega⟩ ≠ eI k r ⟨l.val, by omega⟩ := by
      intro h'; have := congrArg Fin.val h'; simp [eI] at this; omega
    rw [hx, tm_offdiag _ _ hne, hL l, smul_smul, smul_smul]
    congr 1
    push_cast
    rw [pow_add]
    try ring
  have hT : Tm E (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩) =
      algebraMap ℂ A (u - ((m + 1 : ℕ) : ℂ)) + E (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩) := by
    simp [Tm]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hA2, hA1, hA0, map_smul, smul_smul, inv_mul_cancel₀ (mul_ne_zero hZ hc), one_smul, smul_mul_assoc, map_smul,
    smul_smul, inv_mul_cancel₀ hZ, one_smul, map_sum, hmain, hQ, hT, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [map_smul, smul_smul, inv_last Z hZ]
  congr 1
  have hs : ((-1 : ℂ) ^ (m + (l : ℕ))) * (-1) ^ (m + (l : ℕ)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  linear_combination (c * Z.det⁻¹ * (Z.submatrix Fin.castSucc l.succAbove).det) * hs

end Formalism.FourierDecayAlt.P.PBG
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVstep
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBFV

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.TwistedTransfer

theorem fsv_mul_conj (s t : ℂ) : fsv s t * conj (fsv s t) = 1 := by
  unfold fsv
  rw [← Complex.exp_conj, ← Complex.exp_add]
  convert Complex.exp_zero using 2
  simp only [map_sub, map_mul, Complex.conj_conj]
  ring

theorem fsv_zero (t : ℂ) : fsv 0 t = 1 := by
  simp [fsv]

section Wave

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem hsInner_smul_right (a : ℂ) (U V : Wq →L[ℂ] Wp) : B.hsInner U (a • V) = conj a * B.hsInner U V := by
  have e : Formalism.FourierDecayAlt.B.hsVec (a • V) = a • Formalism.FourierDecayAlt.B.hsVec V := by
    unfold Formalism.FourierDecayAlt.B.hsVec
    rw [← WithLp.toLp_smul]
    rfl
  unfold Formalism.FourierDecayAlt.B.hsInner
  rw [e, inner_smul_left]

theorem pairAt_mulOp_right (μ : Measure (Mt k r)) (l : Fin r) (s : ℂ) (Wv : Module.End ℂ (RadSp k r z z' π π'))
    (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ Φ (Wv Ψ) c = conj (fsv s (c l)) * pairAt μ Φ Ψ c := by
  unfold pairAt
  simp only [hW Ψ c, hsInner_smul_right]
  exact integral_const_mul _ _

theorem form_mulOp_right (μ : Measure (Mt k r)) (l : Fin r) (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp k r z z' π π'))
    (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) (u y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) (t : ℂ) :
    form μ l.succ u (act (io (mkP Wv Wv')) y) (Function.update c l t) =
      conj (fsv s t) * form μ l.succ u y (Function.update c l t) := by
  unfold form
  rw [← integral_const_mul]
  congr 1
  funext c'
  simp only [act_io]
  change _ * ∑ a, pairAt μ (u a) (Wv (y a)) _ = _
  simp only [pairAt_mulOp_right μ l s Wv hW, glue_succ_update, ← Finset.mul_sum]
  ring

theorem act_Vw_zero (w : List (Letter ℂ S)) (x : Ix S → RadSp k r z z' π π') :
    act (Vw (mkP (1 : Module.End ℂ (RadSp k r z z' π π')) 1) 0 w) x = x := by
  have hU : ∀ w : List (Letter ℂ S), (UUiw (0 : ℂ) w : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) = 1 := by
    intro w
    induction w with
    | nil => rfl
    | cons l w ih =>
      rw [UUiw, ih, mul_one]
      have h0 : (Uinv (A := Pr (RadSp k r z z' π π')) (if l.plus then (0 : ℂ) else star 0)) = 1 := by
        rw [star_zero, ite_self]
        unfold Uinv
        rw [map_zero]
        exact Matrix.one_fin_two.symm
      rw [h0, Formalism.FourierDecayAlt.P.Wd11.liftMatrix_one, Formalism.FourierDecayAlt.P.Wd1.ins_one]
  have h1 : (mkP (1 : Module.End ℂ (RadSp k r z z' π π')) 1) = 1 := rfl
  funext a
  rw [Vw, hU, mul_one, h1, act_io]
  rfl

theorem isMulOp_one_c (l : Fin r) :
    multiplicationOperator (1 : Module.End ℂ (RadSp k r z z' π π')) (fun c _ => fsv 0 (c l)) := by
  intro Φ c g
  simp [fsv_zero]

theorem isMulOp_one_c' (l : Fin r) :
    multiplicationOperator (1 : Module.End ℂ (RadSp k r z z' π π')) (fun c _ => fsv (-0) (c l)) := by
  intro Φ c g
  simp [fsv_zero]

theorem isMulOp_one_zeta :
    multiplicationOperator (1 : Module.End ℂ (RadSp k r z z' π π')) (fun _ g => fsv 0 (P5.zeta k r z z' g)) := by
  intro Φ c g
  simp [fsv_zero]

theorem isMulOp_one_zeta_conj :
    multiplicationOperator (1 : Module.End ℂ (RadSp k r z z' π π')) (fun _ g => fsv (-0) (P5.zeta k r z z' g)) := by
  intro Φ c g
  simp [fsv_zero]

end Wave

section Step

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
variable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
  (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
  (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
  (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)

theorem ph_wave_right (hD : IsData P z z' π π' X μ L st l0) (w : List (Letter ℂ S))
    (hnd : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) (l : Fin P.r) (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
    (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) (hW' : multiplicationOperator Wv' (fun c _ => fsv (-s) (c l)))
    (x y : Ix S → RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) (t : ℂ) :
    ph L st μ l w x (act (Vw (mkP Wv Wv') s w) y) c t = conj (fsv s t) * ph L st μ l w x y c t := by
  obtain ⟨hwave, hc1, hc2, hp⟩ := waveSiteAll Wp Wq P z z' π π' X L hD.2.2.1 l s Wv Wv' hW hW'
  have hbT : bTl L l w * Vw (mkP Wv Wv') s w = io (mkP Wv Wv') * bTl L l w :=
    Formalism.FourierDecayAlt.P.plane_wave_vector_identity ℂ _ S (site L l) (mkP Wv Wv') (mkP Wv' Wv) s w hwave hc1 hc2 hp hnd
  simp only [P5.ph, RRform]
  rw [← act_mul (bTl L l w) (Vw (mkP Wv Wv') s w) y, hbT, act_mul (io (mkP Wv Wv')) (bTl L l w) y,
    form_mulOp_right μ l s Wv Wv' hW]
  ring

theorem rr_wave_A (hD : IsData P z z' π π' X μ L st l0) (hOn : ThmPOn (S := S) P z z' π π' μ L st K l0)
    (w : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 w) (hr : 0 < P.r) (s : ℂ)
    (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
    (hW : multiplicationOperator Wv (fun c _ => fsv s (c ⟨0, hr⟩))) (hW' : multiplicationOperator Wv' (fun c _ => fsv (-s) (c ⟨0, hr⟩)))
    (x y : Ix S → RadSp P.k P.r z z' π π') (hx : InK (K 0) x) (hy : InK (K 0) y)
    (hVy : InK (K 0) (act (Vw (mkP Wv Wv') s w) y)) (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r) :
    RRform L st μ 0 w (act (Vw (mkP Wv Wv') s w) x) (act (Vw (mkP Wv Wv') s w) y) c = RRform L st μ 0 w x y c := by
  have hl : (⟨0, hr⟩ : Fin P.r).castSucc = 0 := Fin.ext rfl
  have hstep := (hOn w hw).2.1 ⟨0, hr⟩
  unfold StepP at hstep
  rw [hl] at hstep
  obtain ⟨φ, -, hφ, -, hφs⟩ := hstep x (act (Vw (mkP Wv Wv') s w) y) hx hVy c hc
  obtain ⟨ψ, -, hψ, -, hψs⟩ := hstep x y hx hy c hc
  have h1 := hφs s Wv Wv' hW hW'
  have h0 := hψs 0 1 1 (isMulOp_one_c _) (isMulOp_one_c' _)
  rw [act_Vw_zero] at h0
  rw [← h1, ← h0]
  have hae : ∀ᵐ t : ℂ ∂volume, t ≠ 0 := by
    rw [ae_iff]
    simpa using (measure_singleton (0 : ℂ) : volume ({0} : Set ℂ) = 0)
  refine integral_congr_ae ?_
  filter_upwards [hae] with t ht
  rw [hφ t ht, hψ t ht, ph_wave_right P z z' π π' X μ L st l0 hD w hw.1.1 ⟨0, hr⟩ s Wv Wv' hW hW',
    fsv_zero, ← mul_assoc, fsv_mul_conj, one_mul]

theorem topDens_wave_right (hD : IsData P z z' π π' X μ L st l0) (w : List (Letter ℂ S))
    (hw : Fr.admitted st w) (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
    (hW : multiplicationOperator Wv (fun _ g => fsv s (P5.zeta P.k P.r z z' g)))
    (hW' : multiplicationOperator Wv' (fun _ g => fsv (-s) (P5.zeta P.k P.r z z' g)))
    (x y : Ix S → RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) (g : Mx P.k P.r) :
    topDens L st w x (act (Vw (mkP Wv Wv') s w) y) c g =
      conj (fsv s (P5.zeta P.k P.r z z' g)) * topDens L st w x y c g := by
  obtain ⟨hP, -, hAL, hQQ, -, -, hSL, hLS⟩ := hD
  have hW1 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv s (P5.zeta P.k P.r z z' g) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW
  have hW2 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv' Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv (-s) (P5.zeta P.k P.r z z' g) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW'
  have hWW' : Wv * Wv' = 1 := by
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, Module.End.one_apply, hW1, hW2, smul_smul, fsv_mul_fsv_neg, one_smul]
  have hW'W : Wv' * Wv = 1 := by
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, Module.End.one_apply, hW1, hW2, smul_smul, fsv_neg_mul_fsv, one_smul]
  have f_fi : mkP Wv Wv' * mkP Wv' Wv = 1 := pr_ext hWW' hWW'
  have fi_f : mkP Wv' Wv * mkP Wv Wv' = 1 := pr_ext hW'W hW'W
  have hfn : ∀ g ∈ Fr.zfns L, Commute (mkP Wv Wv') g := by
    obtain ⟨-, -, -, -, -, -, hz, hzi, hzb, hzbi, hG, hGi, -⟩ := hAL
    have key : ∀ j j' : Fin 6, Commute (mkP Wv Wv') (mkP (X.fn j) (X.fn j')) := by
      intro j j'
      show _ * _ = _ * _
      exact pr_ext (mulOp_comm_fn X Wv _ hW j) (mulOp_comm_fn X Wv' _ hW' j').symm
    intro g hg
    simp only [Fr.zfns, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hz]; exact key _ _
    · rw [hzi]; exact key _ _
    · rw [hzb]; exact key _ _
    · rw [hzbi]; exact key _ _
    · rw [hG]; exact key _ _
    · rw [hGi]; exact key _ _
  have hGG : Commute (mkP Wv Wv') L.GG := hfn _ (mem_zfns L).2.2.2.2.1
  have hfiGG : Commute (mkP Wv' Wv) L.GG := (commute_inv hGG.symm f_fi fi_f).symm
  obtain ⟨e11, e10⟩ := zeta_entries Formalism.FourierDecayAlt.P.actual_zeta_smooth_alt hP X st l0 hQQ s Wv Wv' hW hW'
  have hx : ∀ Y, Commute (mkP Wv Wv') (st.x Y) := by
    intro Y
    have h := e11 Y
    rw [hLS.tau Y] at h
    have h1 : L.GG * (mkP Wv' Wv * st.x Y * mkP Wv Wv') = L.GG * st.x Y := by
      conv_rhs => rw [← h]
      rw [← mul_assoc (mkP Wv' Wv) L.GG, hfiGG.eq]
      simp only [mul_assoc]
    have h2 : mkP Wv' Wv * st.x Y * mkP Wv Wv' = st.x Y := by
      calc mkP Wv' Wv * st.x Y * mkP Wv Wv' = L.GGi * (L.GG * (mkP Wv' Wv * st.x Y * mkP Wv Wv')) := by
            rw [← mul_assoc, L.GGi_GG, one_mul]
        _ = L.GGi * (L.GG * st.x Y) := by rw [h1]
        _ = st.x Y := by rw [← mul_assoc, L.GGi_GG, one_mul]
    show mkP Wv Wv' * st.x Y = st.x Y * mkP Wv Wv'
    calc mkP Wv Wv' * st.x Y = mkP Wv Wv' * (mkP Wv' Wv * st.x Y * mkP Wv Wv') := by rw [h2]
      _ = st.x Y * mkP Wv Wv' := by rw [← mul_assoc, ← mul_assoc, f_fi, one_mul]
  have hl : ∀ Y ∈ st.inv, mkP Wv' Wv * (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y) * mkP Wv Wv' =
      L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y - algebraMap ℂ _ s := by
    intro Y hY
    have h := e10 Y
    rw [hLS.low Y hY, hLS.tau Y] at h
    have hfix : Commute (mkP Wv' Wv) (st.x Y) := (commute_inv (hx Y).symm f_fi fi_f).symm
    have cancel : ∀ T, st.xi Y * L.GGi * (L.GG * st.x Y * T) = T := by
      intro T
      calc st.xi Y * L.GGi * (L.GG * st.x Y * T) = st.xi Y * (L.GGi * L.GG) * st.x Y * T := by
            simp only [mul_assoc]
        _ = T := by rw [L.GGi_GG, mul_one, (hLS.x_xi Y hY).2, one_mul]
    have h3 : mkP Wv' Wv * (L.GG * st.x Y * (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y)) * mkP Wv Wv' =
        L.GG * st.x Y * (mkP Wv' Wv * (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y) * mkP Wv Wv') := by
      rw [← mul_assoc (mkP Wv' Wv) (L.GG * st.x Y), ← mul_assoc (mkP Wv' Wv) L.GG, hfiGG.eq,
        mul_assoc L.GG (mkP Wv' Wv), hfix.eq]
      simp only [mul_assoc]
    rw [h3, ← mul_sub] at h
    rw [← cancel (mkP Wv' Wv * _ * mkP Wv Wv'), h, cancel]
  have hWH : WaveHyp L st (mkP Wv Wv') (mkP Wv' Wv) s := ⟨f_fi, fi_f, rfl, hfn, hx, hl⟩
  obtain ⟨hFV, -⟩ := frame_twist_F hSL hLS hWH w hw
  unfold topDens
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← act_mul, hFV, act_mul (io (mkP Wv Wv')) (Fr.ofWord L st w).F y, act_io,
    show (mkP Wv Wv').1 = Wv from rfl, hW1, hsInner_smul_right]

theorem rr_wave_B (hD : IsData P z z' π π' X μ L st l0) (hOn : ThmPOn (S := S) P z z' π π' μ L st K l0)
    (w : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 w) (hr : P.r = 0) (s : ℂ)
    (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
    (hW : multiplicationOperator Wv (fun _ g => fsv s (P5.zeta P.k P.r z z' g)))
    (hW' : multiplicationOperator Wv' (fun _ g => fsv (-s) (P5.zeta P.k P.r z z' g)))
    (x y : Ix S → RadSp P.k P.r z z' π π') (hx : InK (K 0) x) (hy : InK (K 0) y)
    (hVy : InK (K 0) (act (Vw (mkP Wv Wv') s w) y)) (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r) :
    RRform L st μ 0 w (act (Vw (mkP Wv Wv') s w) x) (act (Vw (mkP Wv Wv') s w) y) c = RRform L st μ 0 w x y c := by
  have hl : (0 : Fin (P.r + 1)) = Fin.last P.r := Fin.ext (by simp [hr])
  obtain ⟨hTop, -, -⟩ := hOn w hw
  rw [hl] at hx hy hVy ⊢
  obtain ⟨-, hφs, -⟩ := hTop x (act (Vw (mkP Wv Wv') s w) y) hx hVy c hc
  obtain ⟨-, hψs, -⟩ := hTop x y hx hy c hc
  have h0 := hψs 0 1 1 isMulOp_one_zeta isMulOp_one_zeta_conj
  rw [act_Vw_zero] at h0
  rw [← hφs s Wv Wv' hW hW', ← h0]
  congr 1
  funext g
  rw [topDens_wave_right P z z' π π' X μ L st l0 hD w hw.1 s Wv Wv' hW hW', fsv_zero, ← mul_assoc, fsv_mul_conj,
    one_mul]

end Step

end Formalism.FourierDecayAlt.P.PBFV
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PolynomialHeadTypes
namespace Formalism.FourierDecayAlt.P.PBI

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

def HighestUnipotentIntegral : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (h : C.LPt) (ζ : ℂ) (hh : D.IsLocPt h P.r)
    (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ) (m₀r : B.Mat P.k (P.r - P.r)),
    KB.CptCoef p.T.base F → ζ ≠ 0 →
    D.castV (by omega) (liftVec P.k P.r (P.r - P.r) ν'r) = p.ν' →
    D.castM (by omega) (ιLev P.k P.r (P.r - P.r) m₀r) = p.m₀ →
    p.V F (h ++ [(1, ζ)]) =
      D.vecV (p.T.bs P.r) ν'r m₀r
        (D.castF (by simp [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' F h)) [(1, ζ)]

end

end Formalism.FourierDecayAlt.P.PBI
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ThetaConjOfParts
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def CptInCC : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : B.Mat k r → E) (C : Set (B.Mat k r)),
    B.CkOn ⊤ (B.GV k r) F → IsCompact C → (∀ g, g ∉ C → F g = 0) → ∀ (A : ℝ) (m : ℕ), B.InCC A m F

theorem thr_big (k r m : ℕ) :
    TransportedAlt k r (9 * ((r : ℝ) + 1) * ((((2 * r + k + 1 : ℕ) : ℝ)) ^ 2 + 1) + 6 * (r : ℝ) * (m : ℝ)) m := by
  unfold TransportedAlt
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [Nat.cast_nonneg (α := ℝ) r, sq_nonneg (((2 * r + k + 1 : ℕ) : ℝ))]

end Formalism.FourierDecayAlt.P.JFxG

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.KloostDensOfParts
namespace Formalism.FourierDecayAlt.P.PBJ

open MeasureTheory Formalism.FourierDecayAlt

def KCls {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (Ψ : G.Mat n → V) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ HasCompactSupport Ψ ∧ ∀ Z ∈ tsupport Ψ, G.detM Z ≠ 0

def FubTop : Prop :=
  ∀ (β : ℂ) (p s : ℕ) (σ : Equiv.Perm (Fin (p + s))) (d : Fin (p + s) → ℂ) (σh : Equiv.Perm (Fin p))
    (dh : Fin p → ℂ) (σb : Equiv.Perm (Fin s)) (db : Fin s → ℂ) (V : Type) [NormedAddCommGroup V]
    [NormedSpace ℂ V] [CompleteSpace V] (Ψ : G.Mat (p + s) → V),
    (∀ i, dh i ≠ 0) → (∀ i, db i ≠ 0) → U.hMat σ d = U.blk2 (U.hMat σh dh) 0 0 (U.hMat σb db) → KCls Ψ →
    U.PhiTop (p := p + s) (s := 0) β σ d Ψ (fun x => x.elim0) =
      U.PhiTop (p := s) (s := 0) β σb db (U.PhiTop (p := p) (s := s) β σh dh Ψ) (fun x => x.elim0)

def FreezeLast : Prop :=
  ∀ (β : ℂ) (p : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (Ψ : G.Mat (p + 1) → V), KCls Ψ → ∀ c : ℂ, c ≠ 0 →
    ∃ Ψc : G.Mat p → V, KCls Ψc ∧ ∀ (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ), (∀ i, d i ≠ 0) →
      U.PhiTop (p := p) (s := 1) β σ d Ψ (fun _ _ => c) = U.PhiTop (p := p) (s := 0) β σ d Ψc (fun x => x.elim0)

def OmLongTop : Prop :=
  ∀ β : ℂ, β ≠ 0 → ∀ n : ℕ, ∃ κ : ℂ, κ ≠ 0 ∧
    ∀ (σ : Equiv.Perm (Fin (n + 1))) (d : Fin (n + 1) → ℂ) (z : ℂ) (V : Type) [NormedAddCommGroup V]
      [NormedSpace ℂ V] [CompleteSpace V] (Φ : G.Mat (n + 1) → V),
      z ≠ 0 → U.hMat σ d = G.ptLong (n + 1) z →
      G.OmLong β n Φ z = κ • U.PhiTop (p := n + 1) (s := 0) β σ d Φ (fun x => x.elim0)

def OmBlockTop : Prop :=
  ∀ β : ℂ, β ≠ 0 → ∀ n : ℕ, ∃ κ : ℂ, κ ≠ 0 ∧
    ∀ (σ : Equiv.Perm (Fin (n + 1))) (d : Fin (n + 1) → ℂ) (t c : ℂ) (V : Type) [NormedAddCommGroup V]
      [NormedSpace ℂ V] [CompleteSpace V] (Φ : G.Mat (n + 1) → V),
      t ≠ 0 → c ≠ 0 → U.hMat σ d = G.ptBlock n t c →
      G.OmBlock β n Φ t c = κ • U.PhiTop (p := n + 1) (s := 0) β σ d Φ (fun x => x.elim0)

def KloostDensOfParts : Prop := FubTop → FreezeLast → OmLongTop → OmBlockTop → KB.KloostDens

end Formalism.FourierDecayAlt.P.PBJ
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PrStarFst
namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd

section Act

variable {V : Type} [AddCommGroup V] [Module ℂ V] {S : Type} [Fintype S] [DecidableEq S]

theorem pr_add_fst (p q : Q.Pr V) : (p + q).1 = p.1 + q.1 := rfl
theorem pr_mul_fst (p q : Q.Pr V) : (p * q).1 = p.1 * q.1 := rfl
theorem pr_zero_fst : (0 : Q.Pr V).1 = 0 := rfl
theorem pr_one_fst : (1 : Q.Pr V).1 = 1 := rfl

theorem pr_sum_fst {ι : Type*} (s : Finset ι) (f : ι → Q.Pr V) : (∑ i ∈ s, f i).1 = ∑ i ∈ s, (f i).1 := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, pr_zero_fst]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, pr_add_fst, ih]

def actP (M : SlopeTestRemainingChoices S (Q.Pr V)) (X : Ix S → V) : Ix S → V := fun a => ∑ b, (M a b).1 (X b)

theorem polyAction_mul (M N : SlopeTestRemainingChoices S (Q.Pr V)) (X : Ix S → V) : actP (M * N) X = actP M (actP N X) := by
  funext a
  unfold actP
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, pr_sum_fst, pr_mul_fst, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
  exact Finset.sum_comm

theorem polyAction_one₂ (X : Ix S → V) : actP (1 : SlopeTestRemainingChoices S (Q.Pr V)) X = X := by
  funext a
  unfold actP
  rw [Finset.sum_eq_single a]
  · rw [Matrix.one_apply_eq, pr_one_fst]
    rfl
  · intro b _ hb
    rw [Matrix.one_apply_ne (Ne.symm hb), pr_zero_fst]
    rfl
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem blockMulVec_add (M : SlopeTestRemainingChoices S (Q.Pr V)) (X Y : Ix S → V) : actP M (X + Y) = actP M X + actP M Y := by
  funext a
  simp only [actP, Pi.add_apply, map_add (f := _), Finset.sum_add_distrib]

theorem actP_smul (M : SlopeTestRemainingChoices S (Q.Pr V)) (c : ℂ) (X : Ix S → V) : actP M (c • X) = c • actP M X := by
  funext a
  simp only [actP, Pi.smul_apply, map_smul, Finset.smul_sum]

end Act

end Formalism.FourierDecayAlt.P.PBF
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRealisation
namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section L2

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def gramL {ι : Type} (μ : Measure ℂ) (F G : ι × ℂ → ℂ → H) (p q : ι × ℂ) : ℂ :=
  ∫ D, ⟪F p D, G q D⟫_ℂ ∂μ

theorem inner_toLp {μ : Measure ℂ} {f g : ℂ → H} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hf.toLp f, hg.toLp g⟫_ℂ = ∫ D, ⟪f D, g D⟫_ℂ ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with D h1 h2
  rw [h1, h2]

theorem integrable_inner_of_memLp {μ : Measure ℂ} {f g : ℂ → H} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun D => ⟪f D, g D⟫_ℂ) μ := by
  refine (L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with D h1 h2
  rw [h1, h2]

theorem blockPSD_gramL {ι : Type} (μ : Measure ℂ) (Y : Finset ι) (U A : ι × ℂ → ℂ → H)
    (memU : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (U (h, x)) 2 μ)
    (memA : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (A (h, x)) 2 μ) (Xs : Finset ℂ) (hXs : ∀ x ∈ Xs, x ≠ 0) :
    KB.BlockPSD (Y ×ˢ Xs) (Y ×ˢ Xs) (gramL μ U U) (gramL μ U A) (gramL μ A A) := by
  have hmem : ∀ p ∈ Y ×ˢ Xs, MemLp (U p) 2 μ ∧ MemLp (A p) 2 μ := by
    intro p hp
    rw [Finset.mem_product] at hp
    have hx := hXs _ hp.2
    exact ⟨memU _ hp.1 _ hx, memA _ hp.1 _ hx⟩
  let v : {x // x ∈ (Y ×ˢ Xs).disjSum (Y ×ˢ Xs)} → Lp H 2 μ := fun x =>
    Sum.elim (fun p => if hp : MemLp (U p) 2 μ then hp.toLp (U p) else 0)
      (fun q => if hq : MemLp (A q) 2 μ then hq.toLp (A q) else 0) x.1
  unfold KB.BlockPSD TB.PSDOn
  open scoped ComplexOrder in
  refine (congrArg Matrix.PosSemidef ?_).mpr (Matrix.posSemidef_gram ℂ v)
  ext i j
  obtain ⟨x, hx⟩ := i
  obtain ⟨y, hy⟩ := j
  rcases x with p | q <;> rcases y with p' | q'
  · have h1 := (hmem p (Finset.inl_mem_disjSum.mp hx)).1
    have h2 := (hmem p' (Finset.inl_mem_disjSum.mp hy)).1
    simp only [Matrix.of_apply, Matrix.gram, v, Sum.elim_inl, dif_pos h1, dif_pos h2, inner_toLp h1 h2, gramL]
  · have h1 := (hmem p (Finset.inl_mem_disjSum.mp hx)).1
    have h2 := (hmem q' (Finset.inr_mem_disjSum.mp hy)).2
    simp only [Matrix.of_apply, Matrix.gram, v, Sum.elim_inl, Sum.elim_inr, dif_pos h1, dif_pos h2,
      inner_toLp h1 h2, gramL]
  · have h1 := (hmem q (Finset.inr_mem_disjSum.mp hx)).2
    have h2 := (hmem p' (Finset.inl_mem_disjSum.mp hy)).1
    simp only [Matrix.of_apply, Matrix.gram, v, Sum.elim_inl, Sum.elim_inr, dif_pos h1, dif_pos h2, gramL]
    rw [← inner_conj_symm, inner_toLp h2 h1]
  · have h1 := (hmem q (Finset.inr_mem_disjSum.mp hx)).2
    have h2 := (hmem q' (Finset.inr_mem_disjSum.mp hy)).2
    simp only [Matrix.of_apply, Matrix.gram, v, Sum.elim_inr, dif_pos h1, dif_pos h2, inner_toLp h1 h2, gramL]

end L2

end

end Formalism.FourierDecayAlt.P.PBK
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameThresholdBoundHolds
namespace Formalism.FourierDecayAlt.P.PBD

open Formalism.FourierDecayAlt

def FrameThresholdBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (G : Sz.Glob ι) (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ) (w : ι),
    0 < G.g → 0 < G.lenI → 28 * Real.exp 1 ≤ C →
    (∀ one, 0 ≤ J.supA G de de' T T' l one w) →
    (∀ (b s : ℕ) (Q cg : ℝ), 1 ≤ b → 0 ≤ Q → Q ≤ Real.exp 1 → 0 ≤ cg →
      cg ≤ (28 * G.N / G.lenI) ^ (2 * (b - 1) + s) →
      (2 * Real.pi / G.g) ^ (-(S6.nuBlock G.r b s)) * Q * cg *
          J.supA G de de' T T' l (decide (b = 1 ∧ s + 1 = 1)) w ≤
        J.thrS G C de de' T T' l b (s + 1) w) ∧
    (∀ (b : ℕ) (Q cg : ℝ), 1 ≤ b → 0 ≤ Q → Q ≤ Real.exp 1 → 0 ≤ cg →
      cg ≤ (28 * G.N / G.lenI) ^ (2 * (b - 1)) →
      √((2 * Real.pi / G.g) ^ (-(2 * S6.nuBlock G.r b ((G.r : ℤ) + 2 - b))) * Q * cg *
          J.supA G de de' T T' l false w * (√(T * T'))⁻¹) ≤
        J.thrP G C de de' T T' l b w)

theorem pow_bound (C x : ℝ) (n : ℕ) (hx : 0 ≤ x) (hC : 28 * Real.exp 1 ≤ C) :
    Real.exp 1 * (28 * x) ^ n ≤ C * (C * x) ^ n := by
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hC28 : (28 : ℝ) ≤ C := by nlinarith
  have heC : Real.exp 1 ≤ C := by nlinarith
  have hpow : (28 * x) ^ n ≤ (C * x) ^ n := pow_le_pow_left₀ (by positivity) (by nlinarith) n
  exact mul_le_mul heC hpow (by positivity) (by linarith)

theorem frame_threshold_bound : FrameThresholdBound := by
  intro ι _ G C de de' T T' l w hg hI hC hA
  have hN : 0 ≤ G.N := by unfold Sz.Glob.N; positivity
  have hkg : 0 < 2 * Real.pi / G.g := by positivity
  have key : ∀ (n : ℕ) (Q cg : ℝ), 0 ≤ Q → Q ≤ Real.exp 1 → 0 ≤ cg → cg ≤ (28 * G.N / G.lenI) ^ n →
      Q * cg ≤ C * (C * (G.N / G.lenI)) ^ n := by
    intro n Q cg h0 h1 h2 h3
    have hx : 0 ≤ G.N / G.lenI := div_nonneg hN hI.le
    rw [mul_div_assoc] at h3
    calc Q * cg ≤ Real.exp 1 * (28 * (G.N / G.lenI)) ^ n := mul_le_mul h1 h3 h2 (by positivity)
      _ ≤ C * (C * (G.N / G.lenI)) ^ n := pow_bound C _ n hx hC
  refine ⟨fun b s Q cg hb h0 h1 h2 h3 => ?_, fun b Q cg hb h0 h1 h2 h3 => ?_⟩
  · have hA' := hA (decide (b = 1 ∧ s + 1 = 1))
    have hk := key (2 * (b - 1) + s) Q cg h0 h1 h2 h3
    have hz : (2 * Real.pi / G.g) ^ (-(S6.nuBlock G.r b s)) =
        (2 * Real.pi / G.g) ^ (2 * (b - 1) + s) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hkg.ne']
      congr 1
      unfold S6.nuBlock
      omega
    have hn : 2 * (b - 1) + (s + 1) - 1 = 2 * (b - 1) + s := by omega
    unfold J.thrS Sz.lamThreshold Sz.Glob.m
    rw [hn, hz, show C * (2 * Real.pi / G.g) * G.N / G.lenI = (C * (G.N / G.lenI)) * (2 * Real.pi / G.g) by ring,
      mul_pow]
    have hP : 0 ≤ (2 * Real.pi / G.g) ^ (2 * (b - 1) + s) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ *
        J.supA G de de' T T' l (decide (b = 1 ∧ s + 1 = 1)) w := mul_nonneg (by positivity) hA'
    calc (2 * Real.pi / G.g) ^ (2 * (b - 1) + s) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ * Q * cg *
          J.supA G de de' T T' l (decide (b = 1 ∧ s + 1 = 1)) w
        = ((2 * Real.pi / G.g) ^ (2 * (b - 1) + s) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ *
          J.supA G de de' T T' l (decide (b = 1 ∧ s + 1 = 1)) w) * (Q * cg) := by ring
      _ ≤ ((2 * Real.pi / G.g) ^ (2 * (b - 1) + s) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ *
          J.supA G de de' T T' l (decide (b = 1 ∧ s + 1 = 1)) w) * (C * (C * (G.N / G.lenI)) ^ (2 * (b - 1) + s)) :=
          mul_le_mul_of_nonneg_left hk hP
      _ = C * (((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ * J.supA G de de' T T' l (decide (b = 1 ∧ s + 1 = 1)) w) *
          ((C * (G.N / G.lenI)) ^ (2 * (b - 1) + s) * (2 * Real.pi / G.g) ^ (2 * (b - 1) + s)) := by ring
  · have hA' := hA false
    have hk := key (2 * (b - 1)) Q cg h0 h1 h2 h3
    have hz : (2 * Real.pi / G.g) ^ (-(2 * S6.nuBlock G.r b ((G.r : ℤ) + 2 - b))) =
        (2 * Real.pi / G.g) ^ (2 * b - 1) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hkg.ne']
      congr 1
      unfold S6.nuBlock
      omega
    unfold J.thrP Sz.lamPrimeSq Sz.Glob.m
    apply Real.sqrt_le_sqrt
    rw [hz, show C * G.N / G.lenI = C * (G.N / G.lenI) by ring]
    have hP : 0 ≤ (2 * Real.pi / G.g) ^ (2 * b - 1) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ *
        J.supA G de de' T T' l false w * (√(T * T'))⁻¹ := mul_nonneg (mul_nonneg (by positivity) hA') (by positivity)
    calc (2 * Real.pi / G.g) ^ (2 * b - 1) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ * Q * cg *
          J.supA G de de' T T' l false w * (√(T * T'))⁻¹
        = ((2 * Real.pi / G.g) ^ (2 * b - 1) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ *
          J.supA G de de' T T' l false w * (√(T * T'))⁻¹) * (Q * cg) := by ring
      _ ≤ ((2 * Real.pi / G.g) ^ (2 * b - 1) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ *
          J.supA G de de' T T' l false w * (√(T * T'))⁻¹) * (C * (C * (G.N / G.lenI)) ^ (2 * (b - 1))) :=
          mul_le_mul_of_nonneg_left hk hP
      _ = C * (((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ * J.supA G de de' T T' l false w) *
          (2 * Real.pi / G.g) ^ (2 * b - 1) * (√(T * T'))⁻¹ * (C * (G.N / G.lenI)) ^ (2 * (b - 1)) := by ring

end Formalism.FourierDecayAlt.P.PBD

theorem Formalism.FourierDecayAlt.P.frame_threshold_bound_holds : Formalism.FourierDecayAlt.P.PBD.FrameThresholdBound := Formalism.FourierDecayAlt.P.PBD.frame_threshold_bound
end
