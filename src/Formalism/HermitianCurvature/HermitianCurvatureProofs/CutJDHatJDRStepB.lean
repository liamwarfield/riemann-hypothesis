module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerMatrixBlockThreeMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellMulVecBasis

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRStepBRules
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.StepB

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx3 Formalism.FourierDecayAlt.P.WeylCellAction

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem tailW (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) (b : Fin r) : ∀ n : ℕ, ∀ i : Fin (r + 1), i.val = b.val + 1 + n →
    ∃ T : Mx k r, wCell k r i c = wCell k r b.succ c * T ∧ T ∈ Glev k r b.succ ∧
      (∀ v, inWb k r v → T *ᵥ v = v) := by
  intro n
  induction n with
  | zero =>
    intro i hi
    have : i = b.succ := Fin.ext (by simp [hi])
    subst this
    exact ⟨1, by simp, glev_one _, fun v _ => by simp⟩
  | succ n ih =>
    intro i hi
    have hl : b.val + 1 + n < r := by have := i.isLt; omega
    set l : Fin r := ⟨b.val + 1 + n, hl⟩ with hldef
    have hil : i = l.succ := Fin.ext (by simp [l, hi]; omega)
    subst hil
    obtain ⟨T, hT, hTG, hTv⟩ := ih l.castSucc (by simp [l])
    have hw := (Formalism.FourierDecayAlt.P.weyl_level_element_properties k r l (c l) (hc l)).1
    refine ⟨T * w1 k r l (c l), ?_, ?_, ?_⟩
    · rw [Formalism.FourierDecayAlt.P.Qx6.wCell_succ, hT, Matrix.mul_assoc]
    · exact glev_mul hTG (glev_mono (by rw [Fin.le_def]; simp [l]) hw)
    · intro v hv
      rw [← Matrix.mulVec_mulVec, Formalism.FourierDecayAlt.P.CutMP.unipotent_fixes_anisotropic_vector l _ v hv, hTv v hv]

theorem bvec_wI_inWb (v : Fin (k + 1)) : inWb k r (bvec (wI k r v)) := by
  intro i hi
  simp only [bvec, Pi.single_apply]
  rw [if_neg]
  intro h
  have := congrArg Fin.val h
  simp [wI] at this
  omega

section rules

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rightRuleB (z' : Fin (2 * r + k + 1) → ℂ) (D : Set (Mx k r)) (f : Mx k r → E) (hz' : inWb k r z')
    (hD : IsOpen D) (hS : SmoothLev k r 0 D f) (hR : RightEq k r z' 0 D f) (g : Mx k r) (hg : g ∈ Glev k r 0 ∩ D)
    (a : Fin r) (ha : a.val + 1 < r) (w : Fin (k + 1)) : EH k r (eI k r a) (wI k r w) f g = 0 := by
  have hc : Continuous fun x : Mx k r => g * x := cont_lmul g
  have hD' : IsOpen {x : Mx k r | g * x ∈ D} := hD.preimage hc
  have hS' : SmoothLev k r a.castSucc {x | g * x ∈ D} (fun x => f (g * x)) :=
    smooth_left g (fun x hx => glev0 hg.1 hx) hS
  have hR' : RightEq k r z' a.castSucc {x | g * x ∈ D} (fun x => f (g * x)) := by
    intro x hx n hn
    have := hR (g * x) ⟨glev0 hg.1 hx.1, hx.2⟩ n (nlev_mono (zero_le' _) hn)
    simpa [Matrix.mul_assoc] using this
  have h1 : (1 : Mx k r) ∈ Glev k r a.castSucc ∩ {x | g * x ∈ D} :=
    ⟨glev_one _, by simpa using hg.2⟩
  have hrule := (Formalism.FourierDecayAlt.P.right_action_rule E k r z' a {x | g * x ∈ D} (fun x => f (g * x)) hz' hD' hS' hR'
    1 h1).1
  have hjlt : r + w.val - a.val - 1 < mdim k r a.succ := by simp [mdim]; omega
  have hpos : posL k r a.succ ⟨r + w.val - a.val - 1, hjlt⟩ = wI k r w := by
    simp [posL, wI, Fin.ext_iff]; omega
  have h := hrule ⟨r + w.val - a.val - 1, hjlt⟩
  rw [hpos, eH_left, Matrix.mul_one] at h
  rw [h]
  have hx : xv k r z' a.succ ⟨r + w.val - a.val - 1, hjlt⟩ = 0 := by
    simp only [xv, fvec, hpos]
    rw [dif_pos (show (a.succ : Fin (r + 1)).val < r by simp; omega)]
    simp only [bvec, Pi.single_apply]
    rw [if_neg]
    intro h'
    have := congrArg Fin.val h'
    simp [wI, eI] at this
    omega
  rw [hx, zero_smul]

theorem leftRuleB (z : Fin (2 * r + k + 1) → ℂ) (D : Set (Mx k r)) (f : Mx k r → E) (hz : inWb k r z)
    (hD : IsOpen D) (hDN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D) (hS : SmoothLev k r 0 D f)
    (hL : LeftEq k r z 0 D f) (c : Fin r → ℂ) (hc : c ∈ OmX r) (g : Mx k r) (hg : g ∈ Glev k r (Fin.last r))
    (hWD : wCell k r (Fin.last r) c * g ∈ D) (b : Fin r) (hb : b.val + 1 < r) (v : Fin (k + 1)) :
    EH k r (wI k r v) (eI k r b) f (wCell k r (Fin.last r) c * g) = 0 := by
  have hcne : ∀ l, c l ≠ 0 := hc
  have head_comm : ∀ (i : Fin (r + 1)),
      wCell k r i c ∈ Glev k r 0 ∧
        ∀ j : Fin (r + 1), i ≤ j → ∀ x ∈ Glev k r j, wCell k r i c * x = x * wCell k r i c := by
    intro i
    induction i using Fin.induction with
    | zero =>
      rw [Formalism.FourierDecayAlt.P.Qx6.wCell_zero]
      exact ⟨glev_one _, fun _ _ x _ => by simp⟩
    | succ l ih =>
      obtain ⟨ih0, ihc⟩ := ih
      have hw := Formalism.FourierDecayAlt.P.weyl_level_element_properties k r l (c l) (hcne l)
      rw [Formalism.FourierDecayAlt.P.Qx6.wCell_succ]
      refine ⟨glev_mul ih0 (glev_mono (zero_le' _) hw.1), fun j hj x hx => ?_⟩
      have hx1 : x ∈ Glev k r l.succ := glev_mono hj hx
      have hcj : l.castSucc ≤ j := le_trans (by rw [Fin.le_def]; simp) hj
      rw [Matrix.mul_assoc, (hw.2 x hx1).2.1, ← Matrix.mul_assoc, ihc j hcj x hx, Matrix.mul_assoc]
  obtain ⟨hW0, hWcomm⟩ := head_comm b.castSucc
  obtain ⟨T, hT, hTG, hTv⟩ := tailW (k := k) c hcne b (r - b.val - 1) (Fin.last r) (by simp; omega)
  have hg₁ : T * g ∈ Glev k r b.succ := glev_mul hTG (glev_mono (Fin.le_last _) hg)
  have hsplit : wCell k r (Fin.last r) c * g = wCell k r b.castSucc c * (w1 k r b (c b) * (T * g)) := by
    simp only [hT, Formalism.FourierDecayAlt.P.Qx6.wCell_succ, Matrix.mul_assoc]
  have hWx : ∀ x ∈ Glev k r b.castSucc, wCell k r b.castSucc c * x ∈ Glev k r 0 := fun x hx => glev0 hW0 hx
  have hS' := smooth_left (E := E) (f := f) (D := D) (wCell k r b.castSucc c) hWx hS
  have hcont : Continuous fun x : Mx k r => wCell k r b.castSucc c * x := cont_lmul _
  have hD' : IsOpen {x : Mx k r | wCell k r b.castSucc c * x ∈ D} := hD.preimage hcont
  have hN' : ∀ x ∈ Glev k r b.castSucc ∩ {x | wCell k r b.castSucc c * x ∈ D}, ∀ n ∈ Nlev k r b.castSucc,
      n * x ∈ {x | wCell k r b.castSucc c * x ∈ D} := by
    intro x hx n hn
    show wCell k r b.castSucc c * (n * x) ∈ D
    rw [← Matrix.mul_assoc, hWcomm b.castSucc le_rfl n hn.2, Matrix.mul_assoc]
    exact hDN _ ⟨hWx x hx.1, hx.2⟩ n (nlev_mono (zero_le' _) hn)
  have hL' : LeftEq k r z b.castSucc {x | wCell k r b.castSucc c * x ∈ D}
      (fun x => f (wCell k r b.castSucc c * x)) := by
    intro x hx n hn
    show f (wCell k r b.castSucc c * (n * x)) = _ • f (wCell k r b.castSucc c * x)
    rw [← Matrix.mul_assoc, hWcomm b.castSucc le_rfl n hn.2, Matrix.mul_assoc]
    exact hL _ ⟨hWx x hx.1, hx.2⟩ n (nlev_mono (zero_le' _) hn)
  have hpt : w1 k r b (c b) * (T * g) ∈ {x | wCell k r b.castSucc c * x ∈ D} := by
    show _ ∈ D
    rw [← hsplit]; exact hWD
  have hrule := (Formalism.FourierDecayAlt.P.left_action_rule E k r z b {x | wCell k r b.castSucc c * x ∈ D}
    (fun x => f (wCell k r b.castSucc c * x)) hz hD' hS' hN' hL' (c b) (hcne b) (T * g) hg₁ hpt).1
  have hjlt : r + v.val - b.val - 1 < mdim k r b.succ := by simp [mdim]; omega
  have hpos : posL k r b.succ ⟨r + v.val - b.val - 1, hjlt⟩ = wI k r v := by
    simp [posL, wI, Fin.ext_iff]; omega
  have h := hrule ⟨r + v.val - b.val - 1, hjlt⟩
  rw [hpos, eH_left, ← hsplit] at h
  rw [h]
  have hb1 : (b.succ : Fin (r + 1)).val < r := by simp; omega
  have hy : ybv k r z b.succ (T * g) ⟨r + v.val - b.val - 1, hjlt⟩ = 0 := by
    simp only [ybv, hpos, fvec, dif_pos hb1]
    rw [Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_bvec_eI, ← Matrix.mulVec_mulVec]
    have hgw : inWb k r (g *ᵥ bvec (wI k r v)) :=
      Formalism.FourierDecayAlt.P.NFRadRedLocSec.inWb_uwb (Formalism.FourierDecayAlt.P5.Rad.glev_last_uwb hg) (bvec_wI_inWb v)
    rw [hTv _ hgw]
    exact hgw _ (Or.inr (by simp [esI]; omega))
  rw [hy, mul_zero, zero_smul]

end rules

section ring

theorem zcomm {A : Type} [Ring A] (z : ℤ) (X Y : A) : ((z : ℤ) : A) * (X * Y) = X * (((z : ℤ) : A) * Y) := by
  rw [← mul_assoc, (Int.cast_commute z X).eq, mul_assoc]

theorem succ_above_one_val {t : ℕ} (i : Fin (t + 1)) :
    ((Fin.succ (0 : Fin (t + 1))).succAbove i).val = if i.val = 0 then 0 else i.val + 1 := by
  unfold Fin.succAbove
  split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def]

theorem zmul {A : Type} [Ring A] [Algebra ℂ A] (z : ℤ) (x : A) : ((z : ℤ) : A) * x = ((z : ℂ)) • x := by
  rw [Algebra.smul_def, map_intCast]

theorem stepB_ring {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    {M : Type} [AddCommGroup M] [Module ℂ M] (Λ : A →ₗ[ℂ] M) (p0 p1 : Fin n) (h01 : p0 ≠ p1) (κ : ℂ)
    {t : ℕ} (a b : Fin (t + 2) → Fin n) (ha0 : a 0 = p0) (ha1 : a 1 = p1) (hb0 : b 0 = p0) (hb1 : b 1 = p1)
    (haR : ∀ m : Fin (t + 2), 2 ≤ m.val → a m ≠ p0)
    (hbR : ∀ m : Fin (t + 2), 2 ≤ m.val → b m ≠ p0)
    (hL0 : ∀ m : Fin (t + 2), 2 ≤ m.val → ∀ X, Λ (E (a m) p0 * X) = 0)
    (hL1 : ∀ X, Λ (E p1 p0 * X) = κ • Λ X)
    (hR0 : ∀ m : Fin (t + 2), 2 ≤ m.val → ∀ X, Λ (X * E p0 (b m)) = 0)
    (hR1 : ∀ X, Λ (X * E p0 p1) = Λ X) (u : ℂ) :
    Λ (qminor E a b u) = Λ (Tm E u p0 p0 * qminor E (a ∘ Fin.succ) (b ∘ Fin.succ) (u - 1)) -
      κ • Λ (qminor E (fun j : Fin t => a ⟨j.val + 2, by omega⟩) (fun j : Fin t => b ⟨j.val + 2, by omega⟩)
        (u - 1 - 1)) := by

  set a' : Fin (t + 1) → Fin n := a ∘ (Fin.succ (0 : Fin (t + 1))).succAbove with ha'
  set b' : Fin (t + 1) → Fin n := b ∘ Fin.succ with hb'
  set τ : Equiv.Perm (Fin (t + 1)) := (Fin.last t).cycleRange with hτ
  have hsq : ((Equiv.Perm.sign τ : ℤ) : A) * ((Equiv.Perm.sign τ : ℤ) : A) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hsg : ((Equiv.Perm.sign τ : ℤ) : A) = (((-1 : ℤ) ^ t : ℤ) : A) := by
    rw [hτ, Fin.sign_cycleRange]
    simp
  have hlast : (a' ∘ τ) (Fin.last t) = p0 := by
    show a ((Fin.succ (0 : Fin (t + 1))).succAbove (τ (Fin.last t))) = p0
    rw [hτ, Fin.cycleRange_self, ← ha0]
    congr 1
  have hcs : (a' ∘ τ) ∘ Fin.castSucc = fun j : Fin t => a ⟨j.val + 2, by omega⟩ := by
    funext j
    simp only [Function.comp_apply, hτ, ha']
    congr 1
    apply Fin.ext
    rw [succ_above_one_val, Fin.coe_cycleRange_of_lt (by rw [Fin.lt_def]; simp)]
    try simp
  have hbs : b' ∘ Fin.succ = fun j : Fin t => b ⟨j.val + 2, by omega⟩ := by
    funext j
    simp only [Function.comp_apply, hb']
    rfl
  have hQ' : Λ (qminor E a' b' (u - 1)) =
      Λ (qminor E (fun j : Fin t => a ⟨j.val + 2, by omega⟩) (fun j : Fin t => b ⟨j.val + 2, by omega⟩)
        (u - 1 - 1)) := by
    have hsk := Formalism.REAL.quantumMinorRowSkew_holds A n (t + 1) E a' b' τ (u - 1)
    have e1 : qminor E a' b' (u - 1) = ((Equiv.Perm.sign τ : ℤ) : A) * qminor E (a' ∘ τ) b' (u - 1) := by
      rw [hsk, ← mul_assoc, hsq, one_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, Formalism.FourierDecayAlt.P.expansion_last_line A n t E hE (a' ∘ τ) b' (u - 1), Finset.mul_sum, map_sum,
      Fin.sum_univ_succ]
    have hrest : ∀ m : Fin t, Λ (((Equiv.Perm.sign τ : ℤ) : A) * ((((-1 : ℤ) ^ (t + ((m.succ : Fin (t + 1)) : ℕ)) : ℤ) : A) *
        (qminor E ((a' ∘ τ) ∘ Fin.castSucc) (b' ∘ m.succ.succAbove) (u - 1 - 1) *
          Tm E (u - 1) ((a' ∘ τ) (Fin.last t)) (b' m.succ)))) = 0 := by
      intro m
      have hbm : b' m.succ = b ⟨m.val + 2, by omega⟩ := rfl
      rw [hlast, hbm]
      unfold Tm
      rw [if_neg (Ne.symm (hbR ⟨m.val + 2, by omega⟩ (by simp))), zero_add, ← mul_assoc, ← mul_assoc]
      exact hR0 ⟨m.val + 2, by omega⟩ (by simp) _
    rw [Finset.sum_eq_zero (fun m _ => hrest m), add_zero, hlast]
    have hb0' : b' 0 = p1 := by simp only [hb', Function.comp_apply]; exact hb1
    rw [hb0']
    unfold Tm
    rw [if_neg h01, zero_add, ← mul_assoc, ← mul_assoc, hR1, Fin.succAbove_zero, hcs, hbs, hsg, ← Int.cast_mul]
    have h11 : ((-1 : ℤ) ^ t * (-1) ^ (t + ((0 : Fin (t + 1)) : ℕ))) = 1 := by
      rw [Fin.val_zero, add_zero, ← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [h11, Int.cast_one, one_mul]

  set_option synthInstance.maxHeartbeats 100000 in
    rw [Formalism.FourierDecayAlt.P.expansion_first_column A n (t + 1) E a b u, map_sum, Fin.sum_univ_succ, Fin.sum_univ_succ]
  have hrest : ∀ m : Fin t, Λ ((((-1 : ℤ) ^ ((m.succ.succ : Fin (t + 2)) : ℕ) : ℤ) : A) *
      (Tm E u (a m.succ.succ) (b 0) * qminor E (a ∘ m.succ.succ.succAbove) (b ∘ Fin.succ) (u - 1))) = 0 := by
    intro m
    rw [hb0]
    unfold Tm
    rw [if_neg (haR _ (by simp)), zero_add, zcomm]
    exact hL0 _ (by simp) _
  rw [Finset.sum_eq_zero (fun m _ => hrest m), add_zero]
  have h1 : Λ ((((-1 : ℤ) ^ (((0 : Fin (t + 1)).succ : Fin (t + 2)) : ℕ) : ℤ) : A) *
      (Tm E u (a (0 : Fin (t + 1)).succ) (b 0) * qminor E (a ∘ (0 : Fin (t + 1)).succ.succAbove) (b ∘ Fin.succ) (u - 1))) =
      -(κ • Λ (qminor E a' b' (u - 1))) := by
    have ha1' : a (0 : Fin (t + 1)).succ = p1 := ha1
    rw [ha1', hb0]
    unfold Tm
    rw [if_neg (Ne.symm h01), zero_add, zcomm, hL1, zmul, map_smul]
    simp <;> rfl
  rw [h1, hQ']
  simp only [Fin.val_zero, pow_zero, Int.cast_one, one_mul, Fin.succAbove_zero, hb0, ha0]
  rw [hb']
  exact (sub_eq_add_neg _ _).symm
end ring
end Formalism.FourierDecayAlt.P.CutMP.StepB
end
end

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.StepB

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2 Formalism.FourierDecayAlt.P.PBN Formalism.FourierDecayAlt.P.PBN.MC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open scoped ContDiff

section point

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)} (hD : IsOpen D)

theorem posL_cI_comp {t : ℕ} (a : Fin t → Fin (2 * r + k + 1)) : posL k r 0 ∘ (cI ∘ a) = a :=
  funext fun l => posL_cI _

theorem la_qminor {f : Mx k r → E} (hf : SmoothLev k r 0 D f) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ)
    {x : Mx k r} (hx : x ∈ Glev k r 0 ∩ D) :
    La hD ⟨cut k r 0 D f, cut_mem hD hf⟩ x (qminor (EA hD) a b u) = qminorOp (EH k r) a b u f x := by
  rw [La_apply]
  have e1 : ((qminor (EA (E := E) hD) a b u : SA E hD) : Module.End ℂ (VS k r 0 D E)) =
      qminor (Eh (E := E) (i := 0) hD) (cI ∘ a) (cI ∘ b) u := by
    have := map_qminor (SA E hD).val (EA hD) a b u
    rw [Subalgebra.coe_val] at this
    rw [this]
    exact qminor_reindex (Eh hD) cI cI_inj _ _ _
  rw [e1, rep_qminor hD _ _ _ _ _ hx]
  have hloc := (good_qminor (E := E) hD (cI ∘ a) (cI ∘ b) u).loc (cut k r 0 D f) f
    (fun x' hx' => cut_of_mem _ hx') _ hx
  rw [posL_cI_comp, posL_cI_comp] at hloc
  rw [posL_cI_comp, posL_cI_comp]
  exact hloc

include hD in
theorem sm_qminor {f : Mx k r → E} (hf : SmoothLev k r 0 D f) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    SmoothLev k r 0 D (qminorOp (EH k r) a b u f) := by
  have h := (good_qminor (E := E) hD (cI ∘ a) (cI ∘ b) u).sm f hf
  rw [posL_cI_comp, posL_cI_comp] at h
  exact h

theorem cell_mem {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) :
    wCell k r (Fin.last r) c * g ∈ Glev k r 0 :=
  Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _) (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hg)

theorem cell_cd {g : Mx k r} : ContDiffOn ℝ ∞ (fun c' : Fin r → ℂ => wCell k r (Fin.last r) c' * g) (OmX r) :=
  Formalism.FourierDecayAlt.P.Qx3.cdo_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_smooth _) contDiffOn_const

include hD in
theorem nhds_cell {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r))
    (hcD : wCell k r (Fin.last r) c * g ∈ D) :
    ∀ᶠ c' in nhds c, c' ∈ OmX r ∧ wCell k r (Fin.last r) c' * g ∈ Glev k r 0 ∩ D := by
  have hwc : ContinuousAt (fun c' : Fin r → ℂ => wCell k r (Fin.last r) c' * g) c :=
    (cell_cd (g := g)).continuousOn.continuousAt ((Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc)
  filter_upwards [(Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc, hwc.preimage_mem_nhds (hD.mem_nhds hcD)] with c' h1 h2
  exact ⟨h1, cell_mem h1 hg, h2⟩

theorem pOp_ev {F₁ F₂ : (Fin r → ℂ) → E} {c : Fin r → ℂ} (l : Fin r) (h : F₁ =ᶠ[nhds c] F₂) :
    pOp l F₁ c = pOp l F₂ c := by
  simp only [pOp, wirt, h.fderiv_eq]

include hD in
theorem diff_qminor {f : Mx k r → E} (hf : SmoothLev k r 0 D f) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ)
    {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r))
    (hcD : wCell k r (Fin.last r) c * g ∈ D) :
    DifferentiableAt ℝ (fun c' => qminorOp (EH k r) a b u f (wCell k r (Fin.last r) c' * g)) c :=
  Formalism.FourierDecayAlt.P.WeylCellAction.diff_comp (sm_qminor hD hf a b u) (φ := fun c' => wCell k r (Fin.last r) c' * g) cell_cd
    (fun c' hc' => cell_mem hc' hg) hc hcD

theorem la_E (v₀ : VS k r 0 D E) {x : Mx k r} (hx : x ∈ Glev k r 0 ∩ D) (p q : Fin (2 * r + k + 1)) (X : SA E hD) :
    La hD v₀ x (EA hD p q * X) = EH k r p q (((X : Module.End ℂ (VS k r 0 D E)) v₀ : VS k r 0 D E) : Mx k r → E) x := by
  rw [La_apply, Subalgebra.coe_mul, Module.End.mul_apply, EA_val, ev_E hD _ _ _ hx, posL_cI, posL_cI]

theorem EA_v0B (z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') {f : Mx k r → E}
    (hf : SmoothLev k r 0 D f) (hRf : RightEq k r z' 0 D f) (a : Fin r) (ha : a.val + 1 < r) (w : Fin (k + 1)) :
    ((EA hD (eI k r a) (wI k r w) : SA E hD) : Module.End ℂ (VS k r 0 D E)) ⟨cut k r 0 D f, cut_mem hD hf⟩ = 0 := by
  apply Subtype.ext
  funext g
  by_cases hg : g ∈ Glev k r 0 ∩ D
  · rw [EA_val, ev_E hD _ _ _ hg]
    have hloc := (good_eh (E := E) hD (cI (eI k r a)) (cI (wI k r w))).loc (cut k r 0 D f) f
      (fun x hx => cut_of_mem f hx) g hg
    simp only [posL_cI] at hloc
    rw [posL_cI, posL_cI]
    show EH k r (eI k r a) (wI k r w) (cut k r 0 D f) g = 0
    rw [hloc, rightRuleB z' D f hz' hD hf hRf g hg a ha w]
  · show ((Eh hD (cI (eI k r a)) (cI (wI k r w)) ⟨cut k r 0 D f, cut_mem hD hf⟩ : VS k r 0 D E) : Mx k r → E) g = 0
    rw [(Eh hD (cI (eI k r a)) (cI (wI k r w)) ⟨cut k r 0 D f, cut_mem hD hf⟩).2.2 g hg]

end point

section pt

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rowsN_val (l : Fin (r + 1)) (s : Fin (k + 1)) (j : Fin (r - l.val + k)) :
    (rowsN k r l s j).val = if j.val < r - l.val + s.val then l.val + j.val else l.val + j.val + 1 := by
  unfold rowsN
  split_ifs <;> rfl

theorem stepB_pt (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z') {D : Set (Mx k r)}
    (hD : IsOpen D) (hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D)
    {f : Mx k r → E} (hf : SmoothLev k r 0 D f) (hLf : LeftEq k r z 0 D f) (hRf : RightEq k r z' 0 D f)
    {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r))
    (hcD : wCell k r (Fin.last r) c * g ∈ D) (l : ℕ) (hl : l + 2 ≤ r) (s t : Fin (k + 1)) (u : ℂ) :
    qminorOp (EH k r) (rowsN k r ⟨l, by omega⟩ s) (rowsN k r ⟨l, by omega⟩ t) u f (wCell k r (Fin.last r) c * g) =
      u • qminorOp (EH k r) (rowsN k r ⟨l + 1, by omega⟩ s) (rowsN k r ⟨l + 1, by omega⟩ t) (u - 1) f
          (wCell k r (Fin.last r) c * g) +
        pOp ⟨l, by omega⟩ (fun c' => qminorOp (EH k r) (rowsN k r ⟨l + 1, by omega⟩ s)
          (rowsN k r ⟨l + 1, by omega⟩ t) (u - 1) f (wCell k r (Fin.last r) c' * g)) c -
        (c ⟨l + 1, by omega⟩ / c ⟨l, by omega⟩) • qminorOp (EH k r) (rowsN k r ⟨l + 2, by omega⟩ s)
          (rowsN k r ⟨l + 2, by omega⟩ t) (u - 1 - 1) f (wCell k r (Fin.last r) c * g) := by
  set x0 := wCell k r (Fin.last r) c * g with hx0def
  have hx0 : x0 ∈ Glev k r 0 ∩ D := ⟨cell_mem hc hg, hcD⟩
  set v₀ : VS k r 0 D E := ⟨cut k r 0 D f, cut_mem hD hf⟩ with hv₀
  have hLv : LeftEq k r z 0 D (v₀ : Mx k r → E) := leftEq_cut z hN hLf
  set Λ := La hD v₀ x0 with hΛ
  set tt := r - l - 2 + k with htt
  have hT : tt + 2 = r - (⟨l, by omega⟩ : Fin (r + 1)).val + k := by simp only [Fin.val_mk]; omega
  have hT1 : tt + 1 = r - (⟨l + 1, by omega⟩ : Fin (r + 1)).val + k := by simp only [Fin.val_mk]; omega
  have hT2 : tt = r - (⟨l + 2, by omega⟩ : Fin (r + 1)).val + k := by simp only [Fin.val_mk]; omega
  set a := rowsN k r ⟨l, by omega⟩ s ∘ Fin.cast hT with ha
  set b := rowsN k r ⟨l, by omega⟩ t ∘ Fin.cast hT with hb
  have hav : ∀ m : Fin (tt + 2), (a m).val = if m.val < r - l + s.val then l + m.val else l + m.val + 1 := by
    intro m; simp only [ha, Function.comp_apply, rowsN_val, Fin.val_cast, Fin.val_mk]
  have hbv : ∀ m : Fin (tt + 2), (b m).val = if m.val < r - l + t.val then l + m.val else l + m.val + 1 := by
    intro m; simp only [hb, Function.comp_apply, rowsN_val, Fin.val_cast, Fin.val_mk]
  have hab_le : ∀ m : Fin (tt + 2), (a m).val ≤ r + k ∧ (b m).val ≤ r + k := by
    intro m
    have := m.isLt
    rw [hav, hbv]
    constructor <;> split_ifs <;> omega

  have hLmid : ∀ p : Fin (2 * r + k + 1), l + 2 ≤ p.val → p.val ≤ r + k → ∀ X : SA E hD,
      Λ (EA hD p (eI k r ⟨l, by omega⟩) * X) = 0 := by
    intro p hp1 hp2 X
    rw [hΛ, la_E hD v₀ hx0]
    have hsm := (((X : Module.End ℂ (VS k r 0 D E)) v₀ : VS k r 0 D E)).2.1
    have hle := leftEq_SA hD z hN X v₀ hLv
    by_cases hpr : p.val < r
    · have hpe : p = eI k r ⟨p.val, hpr⟩ := Fin.ext (by simp [eI])
      rw [hpe, Formalism.FourierDecayAlt.P.left_rule_cell E k r z D _ hz hD hN hsm hle c hc g hg hcD ⟨p.val, hpr⟩ ⟨l, by omega⟩
        (by simp; omega), if_neg (by simp; omega), zero_smul]
    · have hpw : p = wI k r ⟨p.val - r, by omega⟩ := Fin.ext (by simp [wI]; omega)
      rw [hpw, leftRuleB z D _ hz hD hN hsm hle c hc g hg hcD ⟨l, by omega⟩ (by simp; omega)]
  have hL1 : ∀ X : SA E hD, Λ (EA hD (eI k r ⟨l + 1, by omega⟩) (eI k r ⟨l, by omega⟩) * X) =
      (c ⟨l + 1, by omega⟩ / c ⟨l, by omega⟩) • Λ X := by
    intro X
    rw [hΛ, la_E hD v₀ hx0]
    have hsm := (((X : Module.End ℂ (VS k r 0 D E)) v₀ : VS k r 0 D E)).2.1
    have hle := leftEq_SA hD z hN X v₀ hLv
    rw [Formalism.FourierDecayAlt.P.left_rule_cell E k r z D _ hz hD hN hsm hle c hc g hg hcD ⟨l + 1, by omega⟩ ⟨l, by omega⟩
      (by simp), if_pos (by simp), La_apply]
  have hRmid : ∀ p : Fin (2 * r + k + 1), l + 2 ≤ p.val → p.val ≤ r + k → ∀ X : SA E hD,
      Λ (X * EA hD (eI k r ⟨l, by omega⟩) p) = 0 := by
    intro p hp1 hp2 X
    rw [hΛ, La_apply, Subalgebra.coe_mul, Module.End.mul_apply]
    have hzero : ((EA hD (eI k r ⟨l, by omega⟩) p : SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ = 0 := by
      by_cases hpr : p.val < r
      · have hpe : p = eI k r ⟨p.val, hpr⟩ := Fin.ext (by simp [eI])
        rw [hpe, hv₀, root_vector_action_cutoff hD z' hz' Formalism.FourierDecayAlt.P.right_rule_derivative hf hRf ⟨l, by omega⟩ ⟨p.val, hpr⟩ (by simp; omega),
          if_neg (by simp; omega), zero_smul]
      · have hpw : p = wI k r ⟨p.val - r, by omega⟩ := Fin.ext (by simp [wI]; omega)
        rw [hpw, hv₀, EA_v0B hD z' hz' hf hRf ⟨l, by omega⟩ (by simp; omega)]
    rw [hzero, map_zero]
    rfl
  have hR1 : ∀ X : SA E hD, Λ (X * EA hD (eI k r ⟨l, by omega⟩) (eI k r ⟨l + 1, by omega⟩)) = Λ X := by
    intro X
    rw [hΛ, La_apply, La_apply, Subalgebra.coe_mul, Module.End.mul_apply]
    rw [hv₀, root_vector_action_cutoff hD z' hz' Formalism.FourierDecayAlt.P.right_rule_derivative hf hRf ⟨l, by omega⟩ ⟨l + 1, by omega⟩ (by simp),
      if_pos (by simp), one_smul]
  have hne : eI k r ⟨l, by omega⟩ ≠ eI k r ⟨l + 1, by omega⟩ := by simp [eI, Fin.ext_iff]
  have hring := stepB_ring (EA (E := E) hD) (EA_gl hD) Λ (eI k r ⟨l, by omega⟩) (eI k r ⟨l + 1, by omega⟩) hne
    (c ⟨l + 1, by omega⟩ / c ⟨l, by omega⟩) a b
    (Fin.ext (by rw [hav]; simp [eI]; first | omega | (split_ifs <;> omega)))
    (Fin.ext (by rw [hav]; simp [eI]; first | omega | (split_ifs <;> omega)))
    (Fin.ext (by rw [hbv]; simp [eI]; first | omega | (split_ifs <;> omega)))
    (Fin.ext (by rw [hbv]; simp [eI]; first | omega | (split_ifs <;> omega)))
    (fun m hm h => by have := congrArg Fin.val h; rw [hav] at this; simp [eI] at this; split_ifs at this <;> omega)
    (fun m hm h => by have := congrArg Fin.val h; rw [hbv] at this; simp [eI] at this; split_ifs at this <;> omega)
    (fun m hm X => hLmid (a m) (by rw [hav]; split_ifs <;> omega) (hab_le m).1 X) hL1
    (fun m hm X => hRmid (b m) (by rw [hbv]; split_ifs <;> omega) (hab_le m).2 X) hR1 u

  have hc1 : a ∘ Fin.succ = rowsN k r ⟨l + 1, by omega⟩ s ∘ Fin.cast hT1 := by
    funext j; apply Fin.ext
    simp only [Function.comp_apply]
    rw [hav, rowsN_val]
    simp only [Fin.val_succ, Fin.val_cast, Fin.val_mk]
    split_ifs <;> omega
  have hd1 : b ∘ Fin.succ = rowsN k r ⟨l + 1, by omega⟩ t ∘ Fin.cast hT1 := by
    funext j; apply Fin.ext
    simp only [Function.comp_apply]
    rw [hbv, rowsN_val]
    simp only [Fin.val_succ, Fin.val_cast, Fin.val_mk]
    split_ifs <;> omega
  have hc2 : (fun j : Fin tt => a ⟨j.val + 2, by omega⟩) = rowsN k r ⟨l + 2, by omega⟩ s ∘ Fin.cast hT2 := by
    funext j; apply Fin.ext
    simp only [Function.comp_apply]
    rw [hav, rowsN_val]
    simp only [Fin.val_cast, Fin.val_mk]
    split_ifs <;> omega
  have hd2 : (fun j : Fin tt => b ⟨j.val + 2, by omega⟩) = rowsN k r ⟨l + 2, by omega⟩ t ∘ Fin.cast hT2 := by
    funext j; apply Fin.ext
    simp only [Function.comp_apply]
    rw [hbv, rowsN_val]
    simp only [Fin.val_cast, Fin.val_mk]
    split_ifs <;> omega
  rw [hc1, hd1, hc2, hd2] at hring

  have hread : ∀ {t' : ℕ} (a' b' : Fin t' → Fin (2 * r + k + 1)) (w : ℂ) (x : Mx k r), x ∈ Glev k r 0 ∩ D →
      La hD v₀ x (qminor (EA hD) a' b' w) = qminorOp (EH k r) a' b' w f x :=
    fun a' b' w x hx => la_qminor hD hf a' b' w hx
  rw [hΛ, hread _ _ _ _ hx0, hread _ _ _ _ hx0, ← hΛ] at hring
  rw [ha, hb] at hring
  simp only [top_qminor_cast] at hring
  rw [hring]

  congr 1
  set Q1 := qminor (EA (E := E) hD) (rowsN k r ⟨l + 1, by omega⟩ s ∘ Fin.cast hT1)
    (rowsN k r ⟨l + 1, by omega⟩ t ∘ Fin.cast hT1) (u - 1) with hQ1
  have hT' : Λ (Tm (EA hD) u (eI k r ⟨l, by omega⟩) (eI k r ⟨l, by omega⟩) * Q1) =
      u • Λ Q1 + EH k r (eI k r ⟨l, by omega⟩) (eI k r ⟨l, by omega⟩)
        (((Q1 : Module.End ℂ (VS k r 0 D E)) v₀ : VS k r 0 D E) : Mx k r → E) x0 := by
    unfold Tm
    rw [if_pos rfl, add_mul, map_add (f := _), la_E hD v₀ hx0, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      map_smul]
  rw [hT', Formalism.FourierDecayAlt.P.torus_cell E k r D _ hD (((Q1 : Module.End ℂ (VS k r 0 D E)) v₀ : VS k r 0 D E)).2.1
    c hc g hg hcD ⟨l, by omega⟩]
  rw [hΛ, hread _ _ _ _ hx0, top_qminor_cast]
  congr 1
  apply pOp_ev
  filter_upwards [nhds_cell hD hc hg hcD] with c' hc'
  have := hread (rowsN k r ⟨l + 1, by omega⟩ s ∘ Fin.cast hT1) (rowsN k r ⟨l + 1, by omega⟩ t ∘ Fin.cast hT1) (u - 1) _ hc'.2
  rw [La_apply, top_qminor_cast] at this
  exact this

end pt

section asm

variable {k r : ℕ}

theorem uC_step (l : ℕ) (hl : l + 1 ≤ r) (Y : ℂ) :
    Q.uC k r ⟨l + 1, by omega⟩ Y = Q.uC k r ⟨l, by omega⟩ Y - 1 := by
  simp only [Q.uC, Q.mdim, Fin.val_mk]
  have e : r - l = r - (l + 1) + 1 := by omega
  rw [e]
  push_cast
  ring

theorem uC_gauge (l : ℕ) (hl : l < r) (Y : ℂ) :
    Q.uC k r ⟨l, by omega⟩ Y = Y + ((Mdim k r ⟨l, hl⟩ - 1 : ℕ) : ℂ) / 2 := by
  simp only [Q.uC, Q.mdim, Mdim, Fin.val_mk]
  have e : 2 * (r - l) + k + 1 - 1 = 2 * (r - l) + k := by omega
  rw [e]
  push_cast
  ring

theorem has_fderiv_double_sum {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι ι' : Type} [Fintype ι] [Fintype ι']
    (κ : ι → ι' → ℂ) (F : ι → ι' → (Fin r → ℂ) → E) {c : Fin r → ℂ} (hF : ∀ i j, DifferentiableAt ℝ (F i j) c) :
    HasFDerivAt (fun c' => ∑ i, ∑ j, κ i j • F i j c') (∑ i, ∑ j, κ i j • fderiv ℝ (F i j) c) c := by
  exact HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => HasFDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    (hF i j).hasFDerivAt.const_smul (κ i j)

theorem partial_derivative_double_sum {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι ι' : Type} [Fintype ι] [Fintype ι']
    (κ : ι → ι' → ℂ) (F : ι → ι' → (Fin r → ℂ) → E) {c : Fin r → ℂ} (hF : ∀ i j, DifferentiableAt ℝ (F i j) c)
    (l : Fin r) (hc : c ∈ OmX r) :
    pOp l (fun c' => ∑ i, ∑ j, κ i j • F i j c') c = ∑ i, ∑ j, κ i j • pOp l (F i j) c := by
  simp only [pOp, if_pos hc, wirt, (has_fderiv_double_sum κ F hF).fderiv, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply]
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  module

theorem fin_alg {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι ι' : Type} [Fintype ι] [Fintype ι']
    (w Y n c1 c0 : ℂ) (κ : ι → ι' → ℂ) (A P B : ι → ι' → E) :
    w • ∑ i, ∑ j, κ i j • ((Y + n) • A i j + P i j - (c1 / c0) • B i j) =
      Y • (w • ∑ i, ∑ j, κ i j • A i j) + w • (∑ i, ∑ j, κ i j • P i j + n • ∑ i, ∑ j, κ i j • A i j) -
        c1 • (c0⁻¹ • (w • ∑ i, ∑ j, κ i j • B i j)) := by
  simp only [Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [div_eq_mul_inv]
  module

end asm

end Formalism.FourierDecayAlt.P.CutMP.StepB

namespace Formalism.FourierDecayAlt.P.CutMP

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBN.MC Formalism.FourierDecayAlt.P.CutMP.StepB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem residue_second_move_holds : JDRStepB := by
  intro Wp Wq _ _ _ _ k r z z' π π' D Y hz hz' hD J hJ l hl c hc g hg hcg
  obtain ⟨hf, hLf, hRf, -⟩ := hJ
  have hDo : IsOpen D := hD.1
  have h1N : (1 : Mx k r) ∈ Nlev k r 0 := ⟨(Formalism.QuantumDeterminants.unipotent_subgroup_holds k r).1, by simp [Glev, UH]⟩
  have hN : ∀ x ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * x ∈ D := by
    intro x hx n hn
    have := hD.2 x hx n ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one z, n, hn, (one_mul n).symm⟩ 1
      ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one z', 1, h1N, (one_mul 1).symm⟩
    rwa [Matrix.mul_one] at this
  obtain ⟨κ, hκ⟩ : ∃ κ : Fin (k + 1) → Fin (k + 1) → ℂ, κ = fun (s t : Fin (k + 1)) =>
    ((-1 : ℂ) ^ ((s : ℕ) + (t : ℕ))) * herm (Hpk k r) (bvec (wI k r s)) z' * (g⁻¹ *ᵥ z) (wI k r t) := ⟨_, rfl⟩
  obtain ⟨wt, hwt⟩ : ∃ wt : (Fin r → ℂ) → ℂ,
    wt = fun c' => ((∏ a : Fin r, ‖c' a‖ ^ (Mdim k r a - 1) : ℝ) : ℂ) := ⟨_, rfl⟩
  have hFN : ∀ (m : ℕ) (hm : m ≤ r), ∀ c' ∈ OmX r, FN k r z z' Y J ⟨m, by omega⟩ c' g =
      wt c' • ∑ s, ∑ t, κ s t • qminorOp (EH k r) (rowsN k r ⟨m, by omega⟩ s) (rowsN k r ⟨m, by omega⟩ t)
        (Q.uC k r ⟨m, by omega⟩ Y) J (wCell k r (Fin.last r) c' * g) := by
    intro m hm c' hc'
    subst hκ hwt
    unfold FN NL
    rw [resG_last, inv_wCell_last_mul_mulVec_of_inWb hc' hg hz]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Q.crd, cOp, ciOp]

  obtain ⟨F1, hF1⟩ : ∃ F1 : Fin (k + 1) → Fin (k + 1) → (Fin r → ℂ) → (Wq →L[ℂ] Wp), F1 = fun s t c' =>
    qminorOp (EH k r) (rowsN k r ⟨l + 1, by omega⟩ s) (rowsN k r ⟨l + 1, by omega⟩ t) (Q.uC k r ⟨l + 1, by omega⟩ Y) J
      (wCell k r (Fin.last r) c' * g) := ⟨_, rfl⟩
  have hd1 : ∀ s t, DifferentiableAt ℝ (F1 s t) c := fun s t => by
    rw [hF1]
    exact diff_qminor hDo hf _ _ _ hc hg hcg
  have hp1 : pOp ⟨l, by omega⟩ (fun c' => FN k r z z' Y J ⟨l + 1, by omega⟩ c' g) c =
      wt c • (∑ s, ∑ t, κ s t • pOp ⟨l, by omega⟩ (F1 s t) c +
        (((Mdim k r ⟨l, by omega⟩ - 1 : ℕ) : ℂ) / 2) • ∑ s, ∑ t, κ s t • F1 s t c) := by
    rw [Formalism.FourierDecayAlt.P.PBN.pOp_locO ⟨l, by omega⟩ (fun c' hc' => hFN (l + 1) (by omega) c' hc') hc]
    have eF : ∀ c', (∑ s, ∑ t, κ s t • qminorOp (EH k r) (rowsN k r ⟨l + 1, by omega⟩ s) (rowsN k r ⟨l + 1, by omega⟩ t)
        (Q.uC k r ⟨l + 1, by omega⟩ Y) J (wCell k r (Fin.last r) c' * g)) = ∑ s, ∑ t, κ s t • F1 s t c' := by
      intro c'; rw [hF1]
    simp only [eF]
    subst hwt
    beta_reduce
    have hdH : DifferentiableAt ℝ (fun c' => ∑ s, ∑ t, κ s t • F1 s t c') c :=
      (has_fderiv_double_sum κ F1 hd1).differentiableAt
    have hG := Formalism.FourierDecayAlt.P.gauge_positivity (Wq →L[ℂ] Wp) r (fun a => Mdim k r a - 1)
      (fun c' => ∑ s, ∑ t, κ s t • F1 s t c') c hc hdH ⟨l, by omega⟩
    rw [hG, partial_derivative_double_sum κ F1 hd1 ⟨l, by omega⟩ hc]
  rw [hp1, hFN l (by omega) c hc, hFN (l + 1) (by omega) c hc, hFN (l + 2) (by omega) c hc]

  have hpt : ∀ s t, qminorOp (EH k r) (rowsN k r ⟨l, by omega⟩ s) (rowsN k r ⟨l, by omega⟩ t) (Q.uC k r ⟨l, by omega⟩ Y)
      J (wCell k r (Fin.last r) c * g) =
      (Y + ((Mdim k r ⟨l, by omega⟩ - 1 : ℕ) : ℂ) / 2) • qminorOp (EH k r) (rowsN k r ⟨l + 1, by omega⟩ s)
          (rowsN k r ⟨l + 1, by omega⟩ t) (Q.uC k r ⟨l + 1, by omega⟩ Y) J (wCell k r (Fin.last r) c * g) +
        pOp ⟨l, by omega⟩ (F1 s t) c -
        (c ⟨l + 1, by omega⟩ / c ⟨l, by omega⟩) • qminorOp (EH k r) (rowsN k r ⟨l + 2, by omega⟩ s)
          (rowsN k r ⟨l + 2, by omega⟩ t) (Q.uC k r ⟨l + 2, by omega⟩ Y) J (wCell k r (Fin.last r) c * g) := by
    intro s t
    have h := stepB_pt z z' hz hz' hDo hN hf hLf hRf hc hg hcg l hl s t (Q.uC k r ⟨l, by omega⟩ Y)
    rw [uC_step (k := k) (l + 1) (by omega) Y, uC_step (k := k) l (by omega) Y]
    rw [hF1]
    rw [uC_step (k := k) l (by omega) Y, ← uC_gauge (k := k) l (by omega) Y]
    exact h
  have hL : (∑ s, ∑ t, κ s t • qminorOp (EH k r) (rowsN k r ⟨l, by omega⟩ s) (rowsN k r ⟨l, by omega⟩ t)
      (Q.uC k r ⟨l, by omega⟩ Y) J (wCell k r (Fin.last r) c * g)) =
      ∑ s, ∑ t, κ s t • ((Y + ((Mdim k r ⟨l, by omega⟩ - 1 : ℕ) : ℂ) / 2) • qminorOp (EH k r)
          (rowsN k r ⟨l + 1, by omega⟩ s) (rowsN k r ⟨l + 1, by omega⟩ t) (Q.uC k r ⟨l + 1, by omega⟩ Y) J
            (wCell k r (Fin.last r) c * g) +
        pOp ⟨l, by omega⟩ (F1 s t) c -
        (c ⟨l + 1, by omega⟩ / c ⟨l, by omega⟩) • qminorOp (EH k r) (rowsN k r ⟨l + 2, by omega⟩ s)
          (rowsN k r ⟨l + 2, by omega⟩ t) (Q.uC k r ⟨l + 2, by omega⟩ Y) J (wCell k r (Fin.last r) c * g)) :=
    Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by rw [hpt s t]
  have hA : (∑ s, ∑ t, κ s t • F1 s t c) = ∑ s, ∑ t, κ s t • qminorOp (EH k r) (rowsN k r ⟨l + 1, by omega⟩ s)
      (rowsN k r ⟨l + 1, by omega⟩ t) (Q.uC k r ⟨l + 1, by omega⟩ Y) J (wCell k r (Fin.last r) c * g) := by
    rw [hF1]
  rw [hL, hA]
  exact fin_alg _ _ _ _ _ _ _ _ _

end Formalism.FourierDecayAlt.P.CutMP
