module

public import Formalism.SharpRestriction.Divisibility.ThetaNormsAndLinks
public import Formalism.SharpRestriction.Divisibility.SlopeExcess.HeightBoundOfComponentBounds
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalLinkOfBranchIdentitiesAndMultiplicity
public import Formalism.LocalToGlobal.ClassOfRecordOfChoice

@[expose] public section

section -- merged from Formalism.SharpRestriction.Divisibility.SlopeExcess.UniformSizeBoundOfOpenFamily
section -- merged from Formalism.SharpRestriction.Divisibility.AdmissibleRank.FreeFamilyOfLeavesAndAdmissible
set_option linter.unusedVariables false

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions MeasureTheory Matrix ComplexConjugate

end Formalism.MainNotions.DIV

end

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hkSigPar_lt (D : D7) (τ : D.what₂.Tau) (i : ℕ) (hi : i + 1 < D.R.k - 1 + D.R.m) :
    DV.sigPar D τ (i + 1) < DV.sigPar D τ i := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  unfold DV.sigPar
  by_cases h1 : i + 1 < D.R.k - 1
  · have h0 : i < D.R.k - 1 := by omega
    rw [dite_eq_left h1, dite_eq_left h0]
    have a := (D.hc τ).u_gt_v ⟨i + 1, h1⟩
    have b := (D.hc τ).v_gt_u ⟨i, h0⟩
    exact a.trans b
  · by_cases h0 : i < D.R.k - 1
    · have hb : i + 1 - (D.R.k - 1) < D.R.m := by omega
      rw [dite_eq_right h1, dite_eq_left hb, dite_eq_left h0]
      have a := (D.hc τ).u_last_gt (by omega) (by omega)
      have b := (D.hc τ).v_gt_u ⟨i, h0⟩
      have e1 : (⟨i + 1 - (D.R.k - 1), hb⟩ : Fin D.R.m) = ⟨0, by omega⟩ := by
        rw [Fin.mk.injEq]
        omega
      have e2 : (⟨i + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := by
        rw [Fin.mk.injEq]
        omega
      rw [e1]
      have b' : (D.hc τ).u ⟨D.R.k - 1, by omega⟩ < (D.hc τ).v ⟨i, h0⟩ := by
        rw [← e2]
        exact b
      exact a.trans b'
    · have hb0 : i - (D.R.k - 1) < D.R.m := by omega
      have hb1 : i + 1 - (D.R.k - 1) < D.R.m := by omega
      have hb2 : i - (D.R.k - 1) + 1 < D.R.m := by omega
      rw [dite_eq_right h1, dite_eq_left hb1, dite_eq_right h0, dite_eq_left hb0]
      have a := (D.hc τ).gap_be ⟨i - (D.R.k - 1), hb0⟩
      have b := (D.hc τ).gap_eb ⟨i - (D.R.k - 1), hb0⟩ hb2
      have e1 : (⟨i + 1 - (D.R.k - 1), hb1⟩ : Fin D.R.m) = ⟨i - (D.R.k - 1) + 1, hb2⟩ := by
        rw [Fin.mk.injEq]
        omega
      rw [e1]
      have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
      linarith

theorem aPlusQ_step (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) (hi : i + 1 < D.R.k - 1 + D.R.m) :
    DV.aPlusQ D j τ (i + 1) ≤ DV.aPlusQ D j τ i := by
  obtain ⟨a, ha⟩ := DV.sigPar_int D τ i
  obtain ⟨b, hb⟩ := DV.sigPar_int D τ (i + 1)
  have h := hkSigPar_lt D τ i hi
  rw [ha, hb] at h
  have h' : b < a := by exact_mod_cast h
  have h'' : (b : ℚ) + 1 ≤ a := by exact_mod_cast h'
  rw [DV.aPlusQ_eq, DV.aPlusQ_eq, ha, hb]
  push_cast
  linarith

theorem aMinusQ_step (D : D7) (j : ℕ) (τ : D.what₂.Tau) (c : ℕ) (hc : j + c + 1 < D.R.m) :
    DV.aMinusQ D j τ c ≤ DV.aMinusQ D j τ (c + 1) := by
  have h0 : j + c < D.R.m := by omega
  have h1 : j + (c + 1) < D.R.m := by omega
  unfold DV.aMinusQ
  rw [dite_eq_left h0, dite_eq_left h1]
  have a := (D.hc τ).gap_be ⟨j + c, h0⟩
  have b := (D.hc τ).gap_eb ⟨j + c, h0⟩ hc
  have e1 : (⟨j + (c + 1), h1⟩ : Fin D.R.m) = ⟨j + c + 1, hc⟩ := by
    rw [Fin.mk.injEq]
    omega
  rw [e1]
  have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
  push_cast
  linarith

theorem aMinusQ_mono (D : D7) (j : ℕ) (τ : D.what₂.Tau) (c c' : ℕ) (h : c ≤ c') (hc' : j + c' < D.R.m) :
    DV.aMinusQ D j τ c ≤ DV.aMinusQ D j τ c' := by
  induction c', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact (ih (by omega)).trans (aMinusQ_step D j τ n (by omega))

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Family

end Formalism.MainNotions.DIV

end

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions Formalism.BasicNotions.DV

section Proved

open Formalism.BasicNotions.TH

end Proved

section Split20

set_option linter.unusedVariables false

open Formalism.BasicNotions Formalism.BasicNotions.TH

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Split20

end Formalism.MainNotions.DIV

end
end

noncomputable section

namespace Formalism.MainNotions.DIV.Proofs

open Formalism.BasicNotions Formalism.MainNotions

theorem top2c2_dlSize (eps : ℝ) (Fm : FamP eps) : J.DlSize Fm := by
  unfold J.DlSize
  refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
  have hx1 : Fm.x1 < x := by linarith
  obtain ⟨-, -, -, -, -, -, hQD, -⟩ := Fm.sizes x hx1 i
  obtain ⟨-, -, -, -, -, h, -⟩ := hQD
  exact h

end Formalism.MainNotions.DIV.Proofs
end
end

noncomputable section

namespace Formalism.L2.DIV.SlopeMaxB

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.DIV.Proofs Formalism.MainNotions.DIV.Proofs.HHParts

theorem muMax_le_pol {D : D7} (L : SizeData₂ D) (hS : SizesAt L) (C CTu : ℝ)
    (hTu : ∀ u, Real.log ((D.mem u).A.T : ℝ) ≤ CTu * D.R.m * L.sc.L) (h : LocalQuadraticParts.FrobeniusExpansionCongruence L C) (u : D.what₂.Word) :
    ((D.fm u).lat 0).muMax ≤ |C| * (12 + 2 * |CTu|) * szPol L ^ 4 * L.sc.b := by
  obtain ⟨hN, -, hK, -, -, -, hQD, hTT, -, -, -, -, -, -, -, -, hDel, -, -, -, -, -, -⟩ := hS
  have hP := one_le_szPol L
  have hb := one_le_b L
  have hP0 : 0 ≤ szPol L := by linarith
  have hb0 : 0 ≤ L.sc.b := by linarith
  have hk1 := k_one hK
  have hr1 : 1 ≤ D.host.rdE := hQD.2.2.2.2.2.2.1
  obtain ⟨-, hr2⟩ := log_rdE_bounds hN hQD
  have hkP := k_le L
  have hfP := f_le L
  have hmP := m_le L
  have hLP := L_le L
  have hL0 := (sc_L_pos L).le
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hT0 : (0 : ℝ) ≤ LocalQuadraticParts.nTT D := Nat.cast_nonneg _
  have hTP : LocalQuadraticParts.nTT D ≤ szPol L := TT_le hTT
  have ha0 := a_nonneg L
  have haP := a_le L hK
  have hb'0 := b'_nonneg L
  have hb'P : L.sc.b' ≤ szPol L * L.sc.b := (b'_le_a L).trans haP
  have hSc0 := L.Sc_pos.le
  have hScP := Sc_le' hN hK hDel

  have hlkv : Real.log ((D.R.k : ℝ) * D.host.v) ≤ 3 * szPol L := by
    have hv : D.host.v = D.host.rdE / 2 := rfl
    have hle : (D.R.k : ℝ) * D.host.v ≤ (D.R.k : ℝ) * D.host.rdE := by
      rw [hv]; exact mul_le_mul_of_nonneg_left (by linarith) hk0
    have hpos : 0 < (D.R.k : ℝ) * D.host.v := by rw [hv]; positivity
    have e1 := Real.log_le_log hpos hle
    have e0 : Real.log ((D.R.k : ℝ) * D.host.rdE) = Real.log (D.R.k : ℝ) + Real.log D.host.rdE :=
      Real.log_mul (by linarith) (by linarith)
    rw [e0] at e1
    have e2 : Real.log (D.R.k : ℝ) ≤ D.R.k := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < D.R.k by linarith); linarith
    linarith
  set lkv := Real.log ((D.R.k : ℝ) * D.host.v) with hlkvd
  set lT := Real.log ((D.mem u).A.T : ℝ) with hlTd
  have hlT0 : 0 ≤ lT := Real.log_natCast_nonneg _
  have hlTP : lT ≤ |CTu| * (szPol L * szPol L) := by
    refine (hTu u).trans ?_
    have e1 : CTu * D.R.m * L.sc.L ≤ |CTu| * D.R.m * L.sc.L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hm0) hL0
    have e2 : (D.R.m : ℝ) * L.sc.L ≤ szPol L * szPol L := mul_le_mul hmP hLP hL0 hP0
    have e3 := mul_le_mul_of_nonneg_left e2 (abs_nonneg CTu)
    calc CTu * D.R.m * L.sc.L ≤ |CTu| * D.R.m * L.sc.L := e1
      _ = |CTu| * ((D.R.m : ℝ) * L.sc.L) := by ring
      _ ≤ _ := e3
  have hc0 := abs_nonneg CTu
  have hlkv0 : 0 ≤ lkv := by
    apply Real.log_nonneg
    have hk5 : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
    have hkR : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk5
    have hv : D.host.v = D.host.rdE / 2 := rfl
    rw [hv]; nlinarith

  have q1 : LocalQuadraticParts.nTT D * L.sc.a * lkv ≤ szPol L * (szPol L * L.sc.b) * (3 * szPol L) :=
    mul_le_mul (mul_le_mul hTP haP ha0 hP0) hlkv hlkv0 (by positivity)
  have q2a : (D.R.k : ℝ) * lkv + lT ≤ szPol L * (3 * szPol L) + |CTu| * (szPol L * szPol L) :=
    add_le_add (mul_le_mul hkP hlkv hlkv0 hP0) hlTP
  have q2b : L.sc.b' + L.Sc ≤ 2 * (szPol L * L.sc.b) := by linarith
  have q2 : (D.R.f : ℝ) * (L.sc.b' + L.Sc) * ((D.R.k : ℝ) * lkv + lT) ≤
      szPol L * (2 * (szPol L * L.sc.b)) * (szPol L * (3 * szPol L) + |CTu| * (szPol L * szPol L)) :=
    mul_le_mul (mul_le_mul hfP q2b (by linarith) hP0) q2a (by positivity) (by positivity)
  have q3 : (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * L.sc.L ≤ szPol L * szPol L ^ 2 * szPol L :=
    mul_le_mul (mul_le_mul hfP (pow_le_pow_left₀ hk0 hkP 2) (by positivity) hP0) hLP hL0 (by positivity)
  have q10 : 0 ≤ LocalQuadraticParts.nTT D * L.sc.a * lkv := by positivity
  have q20 : 0 ≤ (D.R.f : ℝ) * (L.sc.b' + L.Sc) * ((D.R.k : ℝ) * lkv + lT) := by positivity
  have q30 : 0 ≤ (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * L.sc.L := by positivity
  have hsum : LocalQuadraticParts.nTT D * L.sc.a * lkv + (D.R.f : ℝ) * (L.sc.b' + L.Sc) * ((D.R.k : ℝ) * lkv + lT) +
      (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * L.sc.L ≤ (12 + 2 * |CTu|) * szPol L ^ 4 * L.sc.b := by
    have p34 : szPol L ^ 3 * L.sc.b ≤ szPol L ^ 4 * L.sc.b :=
      mul_le_mul_of_nonneg_right (pow_mono_P (L := L) (by norm_num)) hb0
    have p4 : szPol L ^ 4 ≤ szPol L ^ 4 * L.sc.b := le_mul_of_one_le_right (by positivity) hb
    have r1 : szPol L * (szPol L * L.sc.b) * (3 * szPol L) = 3 * (szPol L ^ 3 * L.sc.b) := by ring
    have r2 : szPol L * (2 * (szPol L * L.sc.b)) * (szPol L * (3 * szPol L) + |CTu| * (szPol L * szPol L)) =
        (6 + 2 * |CTu|) * (szPol L ^ 4 * L.sc.b) := by ring
    have r3 : szPol L * szPol L ^ 2 * szPol L = szPol L ^ 4 := by ring
    rw [r1] at q1; rw [r2] at q2; rw [r3] at q3
    have : (12 + 2 * |CTu|) * szPol L ^ 4 * L.sc.b =
        3 * (szPol L ^ 4 * L.sc.b) + (6 + 2 * |CTu|) * (szPol L ^ 4 * L.sc.b) + 3 * (szPol L ^ 4 * L.sc.b) := by ring
    have p40 : 0 ≤ szPol L ^ 4 * L.sc.b := by positivity
    linarith
  have h2 := (h u).2
  have e : C * LocalQuadraticParts.nTT D * L.sc.a * lkv + C * D.R.f * (L.sc.b' + L.Sc) * (D.R.k * lkv + lT) +
      C * D.R.f * (D.R.k : ℝ) ^ 2 * L.sc.L =
      C * (LocalQuadraticParts.nTT D * L.sc.a * lkv + (D.R.f : ℝ) * (L.sc.b' + L.Sc) * ((D.R.k : ℝ) * lkv + lT) +
      (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * L.sc.L) := by ring
  rw [e] at h2
  refine h2.trans ?_
  calc C * (LocalQuadraticParts.nTT D * L.sc.a * lkv + (D.R.f : ℝ) * (L.sc.b' + L.Sc) * ((D.R.k : ℝ) * lkv + lT) +
        (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * L.sc.L)
      ≤ |C| * (LocalQuadraticParts.nTT D * L.sc.a * lkv + (D.R.f : ℝ) * (L.sc.b' + L.Sc) * ((D.R.k : ℝ) * lkv + lT) +
        (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * L.sc.L) := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    _ ≤ |C| * ((12 + 2 * |CTu|) * szPol L ^ 4 * L.sc.b) := mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = |C| * (12 + 2 * |CTu|) * szPol L ^ 4 * L.sc.b := by ring

def EbMu (l : List ℝ) : ℝ := 4 * (max (l.headD 0) 5 + 3) + 1

def BoundB {eps : ℝ} (Fm : FamP eps) (Eb : List ℝ → ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (i : Fm.Ix x) u,
    (((Fm.D x i).fm u).lat 0).muMax ≤ (Fm.L x i).sc.x ^ Eb Fm.cOut * (Fm.L x i).sc.b

theorem boundB_of_slopes {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm) (h : LocalQuadraticParts.SlopesFamily Fm) : BoundB Fm EbMu := by
  obtain ⟨C, xa, h⟩ := h
  obtain ⟨xt, hT⟩ := hT
  refine ⟨max (max xa xt) (max 9 (|C| * (12 + 2 * |Fm.CTu|))), fun x hx hx1 i u => ?_⟩
  have ga : xa ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have gt : xt ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have g9 : max 9 (|C| * (12 + 2 * |Fm.CTu|)) ≤ x := le_trans (le_max_right _ _) hx
  have hsc : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  have hCt : (Fm.L x i).Ct = Fm.Ct := Fm.Ct_eq x i
  have h1 := muMax_le_pol (Fm.L x i) (Fm.sizes x hx1 i) C Fm.CTu (hT x gt i).2 (h x ga i) u
  have h2 := bPol_le (Fm.sizes x hx1 i) (|C| * (12 + 2 * |Fm.CTu|)) 4 (by rw [hsc]; exact g9)
  have hE : EbMu Fm.cOut = ((4 : ℕ) : ℝ) * (max (Fm.L x i).Ct 5 + 3) + 1 := by
    unfold EbMu; rw [cOut_headD, hCt]; norm_num
  rw [hE]
  exact h1.trans h2

theorem slopes_of_values {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm)
    (hCV : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u)) : LocalQuadraticParts.SlopesFamily Fm :=
  J.slopes_family_of_column_values Fm hT (top2c2_dlSize eps Fm) (flipTwoThree.familySlopeLower_of_open Fm (Formalism.L2.GlobalTheoryTheory.TraceIntegrality.lower_slope_inequality_family Fm))
    (flipTwoThree.familySlopeMax_of_open Fm 4 (Formalism.L2.GlobalTheoryTheory.TraceIntegrality.slope_inequality_family_four Fm)) hCV

theorem boundB_of_values {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm)
    (hCV : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u)) : BoundB Fm EbMu :=
  boundB_of_slopes Fm hT (slopes_of_values Fm hT hCV)

end Formalism.L2.DIV.SlopeMaxB

end
