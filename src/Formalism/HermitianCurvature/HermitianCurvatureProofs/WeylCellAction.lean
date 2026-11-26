module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MemLevelZeroOfMemGroup

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.FubiniRightIntegral
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.PBF

section slots

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {n r : ℕ}

theorem liftM_star (M : SlopeTestRemainingChoices (Fin n) A) : liftM (star M) = star (liftM M) := by
  ext z z'
  simp only [Matrix.star_apply, liftM_apply]
  by_cases h : z 0 = z' 0
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h), star_zero]

theorem liftM_neg (M : SlopeTestRemainingChoices (Fin n) A) : liftM (-M) = -liftM M := by
  rw [← liftRingHom_apply_eq_liftM, map_neg, liftRingHom_apply_eq_liftM]

theorem liftM_sub (M N : SlopeTestRemainingChoices (Fin n) A) : liftM (M - N) = liftM M - liftM N := by
  rw [← liftRingHom_apply_eq_liftM, map_sub, liftRingHom_apply_eq_liftM, liftRingHom_apply_eq_liftM]

theorem liftM_pow (M : SlopeTestRemainingChoices (Fin n) A) (m : ℕ) : liftM (M ^ m) = liftM M ^ m := by
  rw [← liftRingHom_apply_eq_liftM, map_pow, liftRingHom_apply_eq_liftM]

theorem matrix_two_map_lift (a b c d : SlopeTestRemainingChoices (Fin n) A) :
    (!![a, b; c, d] : M2 (SlopeTestRemainingChoices (Fin n) A)).map liftM = !![liftM a, liftM b; liftM c, liftM d] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

structure Lifted (f : FrameData (Fin n) A) (f' : FrameData (Fin (n + 1)) A) : Prop where
  F : f'.F = liftM f.F
  ee : ∀ Y, f'.ee Y = liftM (f.ee Y)
  x : ∀ Y, f'.x Y = liftM (f.x Y)
  xi : ∀ Y, f'.xi Y = liftM (f.xi Y)
  c : f'.c = liftM f.c
  ci : f'.ci = liftM f.ci
  q : f'.q = f.q
  N : f'.N = f.N

variable (L : LevelData A r)

theorem io_lift (x : A) : (io x : SlopeTestRemainingChoices (Fin (n + 1)) A) = liftM (io x) := io_succ x

theorem lifted_l {f : FrameData (Fin n) A} {f' : FrameData (Fin (n + 1)) A} (hf : Lifted f f') (Y : ℂ) :
    f'.l L Y = liftM (f.l L Y) := by
  simp only [FrameData.l, kapL, liftM_add, liftM_mul, hf.ee Y, io_lift]

theorem lifted_m {f : FrameData (Fin n) A} {f' : FrameData (Fin (n + 1)) A} (hf : Lifted f f') (Y : ℂ) :
    f'.m L Y = liftM (f.m L Y) := by
  simp only [FrameData.m, FrameData.d, FrameData.di, wt, wti, liftM_mul, liftM_pow, hf.N, hf.c, hf.ci,
    lifted_l L hf, liftM_star, io_lift]

theorem lifted_DD {f : FrameData (Fin n) A} {f' : FrameData (Fin (n + 1)) A} (hf : Lifted f f') (Y Ya : ℂ) :
    f'.DD Y Ya = liftM (f.DD Y Ya) := by
  simp only [FrameData.DD, liftM_smul, liftM_sub, hf.ee]

theorem tz_lift : (tz L : SlopeTestRemainingChoices (Fin (n + 1)) A) = liftM (tz L) := io_succ _

theorem lifted_plus {f : FrameData (Fin n) A} {f' : FrameData (Fin (n + 1)) A} (hf : Lifted f f') (a : Fin n)
    (Ya : ℂ) : Lifted (f.plus L a Ya) (f'.plus L a.succ Ya) := by
  refine ⟨?_, fun Y => ?_, fun Y => ?_, fun Y => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [FrameData.plus]
    rw [hf.F, liftM_mul, ← ins_succ, map_mul_liftM, matrix_two_map_lift, matrix_two_map_lift, lifted_l L hf]
    simp only [liftM_mul, liftM_zero, liftM_one, io_lift]
  · simp only [FrameData.plus]
    rw [← ins_succ, matrix_two_map_lift]
    simp only [liftM_add, liftM_sub, liftM_mul, liftM_neg, liftM_smul, liftM_zero, liftM_one, hf.ee, hf.x, hf.xi,
      lifted_DD hf, tz_lift]
  · simp only [FrameData.plus]
    rw [hf.x, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, liftM_one]
  · simp only [FrameData.plus]
    rw [hf.xi, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, liftM_one]
  · simp only [FrameData.plus]
    rw [hf.c, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, hf.q, hf.x, hf.xi]
  · simp only [FrameData.plus]
    rw [hf.ci, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, hf.q, hf.x, hf.xi]
  · simp only [FrameData.plus, hf.q]
  · simp only [FrameData.plus, hf.N]

theorem lifted_minus {f : FrameData (Fin n) A} {f' : FrameData (Fin (n + 1)) A} (hf : Lifted f f') (b : Fin n)
    (Yb : ℂ) : Lifted (f.minus L b Yb) (f'.minus L b.succ Yb) := by
  refine ⟨?_, fun Y => ?_, fun Y => ?_, fun Y => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [FrameData.minus]
    rw [hf.F, liftM_mul, ← ins_succ, map_mul_liftM, matrix_two_map_lift, matrix_two_map_lift, lifted_m L hf]
    simp only [liftM_mul, liftM_zero, liftM_one, io_lift]
  · simp only [FrameData.minus]
    rw [← ins_succ, matrix_two_map_lift]
    simp only [liftM_add, liftM_sub, liftM_mul, liftM_neg, liftM_smul, liftM_zero, liftM_one, hf.ee, hf.x, hf.xi,
      hf.q, lifted_DD hf, tz_lift]
  · simp only [FrameData.minus]
    rw [hf.x, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, liftM_one]
  · simp only [FrameData.minus]
    rw [hf.xi, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, liftM_one]
  · simp only [FrameData.minus]
    rw [hf.c, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, hf.q, hf.x, hf.xi]
  · simp only [FrameData.minus]
    rw [hf.ci, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, hf.q, hf.x, hf.xi]
  · simp only [FrameData.minus, hf.q]
  · simp only [FrameData.minus, hf.N]

theorem lifted_ofWord (st : Start A) :
    ∀ u : List (Letter ℂ (Fin n)), Lifted (ofWord L st u) (ofWord L st (u.map upL))
  | [] => ⟨by simp [ofWord, Start.frame, liftM_one], fun Y => io_succ _, fun Y => io_succ _, fun Y => io_succ _,
      by simp [ofWord, Start.frame, liftM_one], by simp [ofWord, Start.frame, liftM_one], rfl, rfl⟩
  | l :: u => by
    have ih := lifted_ofWord st u
    rw [List.map_cons]
    by_cases hp : l.plus
    · have e1 : ofWord L st (l :: u) = (ofWord L st u).plus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      have e2 : ofWord L st (upL l :: u.map upL) = (ofWord L st (u.map upL)).plus L l.intersection_update_fsHerm_neg_one.succ l.pt := by
        simp [ofWord, upL, hp]
      rw [e1, e2]
      exact lifted_plus L ih l.intersection_update_fsHerm_neg_one l.pt
    · have e1 : ofWord L st (l :: u) = (ofWord L st u).minus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      have e2 : ofWord L st (upL l :: u.map upL) = (ofWord L st (u.map upL)).minus L l.intersection_update_fsHerm_neg_one.succ l.pt := by
        simp [ofWord, upL, hp]
      rw [e1, e2]
      exact lifted_minus L ih l.intersection_update_fsHerm_neg_one l.pt

theorem bT_lift (σ : Site A) : ∀ u : List (Letter ℂ (Fin n)), bT σ (u.map upL) = liftM (bT σ u)
  | [] => by simp [bT, liftM_one]
  | l :: u => by
    rw [List.map_cons, bT, bT, bT_lift σ u, liftM_mul]
    congr 1
    show ins l.intersection_update_fsHerm_neg_one.succ (lift0 (if l.plus then Ts σ l.pt else (Ts σ l.pt).map star)) =
      liftM (ins l.intersection_update_fsHerm_neg_one (lift0 (if l.plus then Ts σ l.pt else (Ts σ l.pt).map star)))
    rw [liftZero_succ_eq_map, ins_succ]

theorem bTA_lift (u : List (Letter ℂ (Fin n))) : TL.bTA L (u.map upL) = liftM (TL.bTA L u) := by
  simp only [TL.bTA, bT_lift]
  rw [← liftRingHom_apply_eq_liftM, map_list_prod, List.map_map]
  rfl

end slots

end Formalism.FourierDecayAlt.P.PBN
end
end

open MeasureTheory Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.PBF

section row

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {n r : ℕ}

theorem unit_matrix_zero_mul_apply (N : SlopeTestRemainingChoices (Fin (n + 1)) A) (i : Fin 2) (e : Ix (Fin n)) (m : Ix (Fin (n + 1))) :
    (eU (0 : Fin (n + 1)) i 0 * N : SlopeTestRemainingChoices (Fin (n + 1)) A) (Fin.cons 0 e) m =
      if (0 : Fin 2) = i then N (Fin.cons 0 e) m else 0 := by
  rw [Matrix.mul_apply]
  simp only [insert_unit_matrix_zero_apply, ite_mul, one_mul, zero_mul]
  by_cases hi : (0 : Fin 2) = i
  · subst hi
    simp
  · simp [hi]

theorem row_sum (col : Fin 2 → SlopeTestRemainingChoices (Fin (n + 1)) A) (N : SlopeTestRemainingChoices (Fin (n + 1)) A) (e : Ix (Fin n))
    (m : Ix (Fin (n + 1))) :
    ((∑ i : Fin 2, eU (0 : Fin (n + 1)) i 0 * col i) * N : SlopeTestRemainingChoices (Fin (n + 1)) A) (Fin.cons 0 e) m =
      (col 0 * N : SlopeTestRemainingChoices (Fin (n + 1)) A) (Fin.cons 0 e) m := by
  rw [Finset.sum_mul, Matrix.sum_apply, Fin.sum_univ_two, mul_assoc, mul_assoc, unit_matrix_zero_mul_apply, unit_matrix_zero_mul_apply]
  simp

theorem io_mul_apply {S : Type} [Fintype S] [DecidableEq S] (x : A) (N : SlopeTestRemainingChoices S A) (z m : Ix S) :
    (io x * N : SlopeTestRemainingChoices S A) z m = x * N z m := by
  rw [io, Matrix.scalar_apply, Matrix.diagonal_mul]

theorem firstRow (hWS : TL.WordStep) (L : LevelData A r) (st : Start A) (hA : TL.AHyp L st) (y : ℂ)
    (u : List (Letter ℂ (Fin n))) (hadm : admitted st (⟨true, 0, y⟩ :: u.map upL)) (e : Ix (Fin n)) :
    ((ofWord L st (⟨true, 0, y⟩ :: u.map upL)).F * TL.bTA L (⟨true, 0, y⟩ :: u.map upL)) (Fin.cons 0 e) e1 =
      TL.aP L y * ((ofWord L st u).F * TL.bTA L u) e e1 := by
  rw [hWS A (Fin (n + 1)) r L st ⟨true, 0, y⟩ (u.map upL) hA hadm (Fin.cons 0 e)]
  rw [(lifted_ofWord L st u).F, bTA_lift, ← liftM_mul]
  dsimp only
  rw [row_sum]
  simp only [TL.letterCol, ↓reduceIte, Matrix.cons_val_zero]
  rw [io_mul_apply, liftM_apply]
  congr 1

end row

section act

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem act_e1Vec (M : SlopeTestRemainingChoices S (Q.Pr (Q.RadSp k r z z' π π'))) (Φ : Q.RadSp k r z z' π π') (x : Ix S) :
    P5.act M (Top.firstStateVector Φ) x = (M x e1).1 Φ := by
  unfold P5.act Top.firstStateVector
  rw [Finset.sum_eq_single (e1 : Ix S)]
  · split_ifs with h
    · rfl
    · exact absurd rfl h
  · intro b _ hb
    have hb' : ¬(b = fun _ => 0) := hb
    simp [hb']
  · intro h
    exact absurd (Finset.mem_univ _) h

end act

theorem cutWord_tail {P : M.Par} {l0 : ℕ} {l : C.Letter} {w : List C.Letter} (h : KB.CutWord P l0 (l :: w)) :
    KB.CutWord P l0 w := by
  refine ⟨fun a => h.1 a.succ, fun a b hab => h.2 a.succ b.succ fun e => hab (Fin.succ_injective _ e)⟩

section main

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem rad_plus (hWS : TL.WordStep) (P : M.Par) (p : KB.Pl P Wp Wq) (X : Q.ActualOps P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')
    (μ : Measure (Mt P.k P.r)) (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')) P.r)
    (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')))
    (hD : P5.IsData P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' X μ L st p.l0) (w : List C.Letter) (y : ℝ)
    (hcut : KB.CutWord P p.l0 ((true, y) :: w)) (Φ : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')
    (e : Ix (Fin w.length)) :
    P5.act ((Fr.ofWord L st (D.positionted ((true, y) :: w))).F * P5.bTall L (D.positionted ((true, y) :: w)))
        (Top.firstStateVector Φ) (Fin.cons 0 e) =
      (TL.aP L (y : ℂ)).1 (P5.act ((Fr.ofWord L st (D.positionted w)).F * P5.bTall L (D.positionted w)) (Top.firstStateVector Φ) e) := by
  have hA := (Formalism.FourierDecayAlt.P.actual_algebra_facts Wp Wq P _ _ _ _ X μ L st p.l0 hD).1
  have hOK := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' st p.l0 p.hP.1 p.hl.1
    p.hl.2.1 hD.2.2.2.2.1 hD.2.2.2.2.2.1 ((true, y) :: w) hcut.1 hcut.2
  have hadm := hOK.1
  rw [act_e1Vec, act_e1Vec]
  rw [positioned_cons] at hadm ⊢
  exact congrArg (fun x : Q.Pr _ => x.1 Φ) (firstRow hWS L st hA (y : ℂ) (D.positionted w) hadm e)

end main

end Formalism.FourierDecayAlt.P.PBN

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBN

end Formalism.FourierDecayAlt.P
