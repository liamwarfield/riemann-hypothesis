module

public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseUnipotentVolumeConjDiagonalEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmMulRightOfIsCMExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryWeylCellShellIsOpenCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureWeylCellOddUnitary

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingTermCoefEqResidueCardZpow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingTermCoefEqResidueCardZpow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

noncomputable section
namespace GlobalTheory.FunObj.AaCoef
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx

section Core
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}


variable (k n c) in
def volDiag : (n ⊕ Fin c → kˣ) →* ℚ where
  toFun d := invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL d)).toMonoidHom)
  map_one' := by
    have h : diagGL (1 : n ⊕ Fin c → kˣ) = 1 := Units.ext (by simp [diagGL_val])
    rw [h, map_one]
    exact (congrArg invVol (Subgroup.map_id _)).trans invVol_KO
  map_mul' := GlobalTheory.T.inverseUnipotentVolume_conj_diagonalUnitsGL_mul

omit [IsNonarchimedeanLocalField k] [ValuativeRel k] [TopologicalSpace k] in
theorem prod_zpow_eq {ι : Type} (s : Finset ι) (q : ℚ) (hq : q ≠ 0) (g : ι → ℤ) :
    ∏ t ∈ s, q ^ g t = q ^ ∑ t ∈ s, g t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hq]

theorem resCard_ne_zero : (resCard k : ℚ) ≠ 0 := by
  rw [resCard, Nat.cast_ne_zero]
  exact Nat.card_pos.ne'

theorem invVol_diag_zpow (ϖ : kˣ) (hϖ : IsUnif ϖ) (f : n ⊕ Fin c → ℤ) : ∃ z : ℤ,
    invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL fun r => ϖ ^ f r)).toMonoidHom) = (resCard k : ℚ) ^ z ∧
      |z| ≤ Fintype.card (n ⊕ Fin c) * ∑ r, |f r| := by
  choose z hz hzb using fun t : n ⊕ Fin c => GlobalTheory.T.exists_inverseUnipotentVolume_conj_diagonal_eq (k := k) (n := n) (c := c) ϖ hϖ t
  have hd : (fun r => ϖ ^ f r) = ∏ t, (Pi.mulSingle t ϖ) ^ f t := by
    funext r
    rw [Finset.prod_apply, Finset.prod_eq_single r]
    · simp
    · intro t _ ht; simp [Ne.symm ht]
    · simp
  have hq := resCard_ne_zero (k := k)
  let F := (volDiag k n c).toHomUnits
  have hF : ∀ d, (F d : ℚ) = invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL d)).toMonoidHom) := fun _ => rfl
  refine ⟨∑ t, z t * f t, ?_, ?_⟩
  · rw [← hF, hd, map_prod, Units.coe_prod]
    simp_rw [map_zpow, Units.val_zpow_eq_zpow_val, hF, hz, ← _root_.zpow_mul]
    exact prod_zpow_eq _ _ hq _
  · calc |∑ t, z t * f t| ≤ ∑ t, |z t * f t| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t, (Fintype.card (n ⊕ Fin c) : ℤ) * |f t| := Finset.sum_le_sum fun t _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hzb t) (abs_nonneg _)
      _ = _ := (Finset.mul_sum _ _ _).symm

end Core

section Frame
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {G : Grid k}
  (hs : 1 ≤ G.s)

theorem conjLevel_KO (g : G.VertexGroup) {j : ℕ} (hj : j < G.m) :
    conjLevel hs (fun _ => KO k _) g hj = (KO k _).map (MulAut.conj (toFrame hs hj (g (G.m, j)))).toMonoidHom := by
  have h : topRank G j + (G.m - 1 - j) = G.rank (G.m, j) := by have := topRank_add hs j; omega
  have hK : (KO k (Fin (G.rank (G.m, j)))).map (toFrame hs hj).toMonoidHom = KO k _ := by
    ext x
    rw [Subgroup.map_equiv_eq_comap_symm', Subgroup.mem_comap, mem_KO_iff, mem_KO_iff, ← map_inv]
    exact and_congr ((frame h).symm.forall_congr fun _ => (frame h).symm.forall_congr fun _ => Iff.rfl)
      ((frame h).symm.forall_congr fun _ => (frame h).symm.forall_congr fun _ => Iff.rfl)
  rw [conjLevel, Subgroup.map_map, ← hK, Subgroup.map_map]
  congr 1
  ext x : 1
  simp
end Frame

section AA
variable {D : D7}

def aaExp (w : Pl D.host.E) (j : ℕ) : Fin (topRank (bareGrid w) j) ⊕ Fin (D.R.m - 1 - j) → ℤ :=
  Sum.elim (fun _ => 0) fun p => FractionalIdeal.count D.host.E w D.host.AA * ((D.R.m - 1 - j - p.val : ℕ) : ℤ) -
    FractionalIdeal.count D.host.E w D.host.AAbar * (p.val + 1)

theorem toFrame_aaElt (w : Pl D.host.E) (hs : 1 ≤ (bareGrid w).s) {j : ℕ} (hj : j < (bareGrid w).m) :
    toFrame hs hj (aaElt w j) = diagGL fun r => unifAt w ^ aaExp w j r := by
  refine Units.ext ?_
  have h : topRank (bareGrid w) j + ((bareGrid w).m - 1 - j) = (bareGrid w).rank ((bareGrid w).m, j) := by
    have := topRank_add hs j; have hm : (bareGrid w).m = D.R.m := rfl; omega
  show (aaElt w j).val.submatrix (frame h) (frame h) = _
  rw [aaElt, diagGL_val, diagGL_val, submatrix_diagonal_equiv]
  congr 1
  funext x
  rcases x with a | p
  · show _ = ((unifAt w ^ aaExp w j (Sum.inl a) : (Kw w)ˣ) : Kw w)
    rw [show aaExp w j (Sum.inl a) = 0 from rfl]
    simp [frame, Nat.not_le.2 a.2]
  · have e : ∀ (x : ℤ) (N : ℕ), ((unifAt w) ^ x) ^ N = unifAt w ^ (x * N) := fun x N => by
      rw [← zpow_natCast, ← _root_.zpow_mul]
    show _ = ((unifAt w ^ aaExp w j (Sum.inr p) : (Kw w)ˣ) : Kw w)
    rw [show aaExp w j (Sum.inr p) = FractionalIdeal.count D.host.E w D.host.AA * ((D.R.m - 1 - j - p.val : ℕ) : ℤ) -
      FractionalIdeal.count D.host.E w D.host.AAbar * (p.val + 1) from rfl]
    simp only [Function.comp_apply, frame, Equiv.trans_apply, finSumFinEquiv_apply_right, finCongr_apply, Fin.val_cast,
      Fin.val_natAdd, le_add_iff_nonneg_right, zero_le, if_true, Nat.add_sub_cancel_left, genAt]
    congr 1
    rw [e, e, ← _root_.zpow_neg, ← _root_.zpow_add]
    congr 1
end AA

section Main
variable {D : D7}

theorem rank_le_bigN (w : Pl D.host.E) {j : ℕ} (hj : j < D.R.m) :
    (bareGrid w).rank ((bareGrid w).m, j) ≤ bigN D := by
  have h1 : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hj)
  have h2 := Formalism.BasicNotions.Ranks.r_eq D.R
  simp only [Grid.rank, bareGrid, bigN, sLen, add_mul] at h1 ⊢
  nlinarith

theorem sum_abs_aaExp_le (w : Pl D.host.E) (j : ℕ) :
    ∑ r, |aaExp w j r| ≤ (D.R.m : ℤ) * ((D.R.m : ℤ) * (|FractionalIdeal.count D.host.E w D.host.AA| +
      |FractionalIdeal.count D.host.E w D.host.AAbar|)) := by
  set A := FractionalIdeal.count D.host.E w D.host.AA
  set A' := FractionalIdeal.count D.host.E w D.host.AAbar
  have hA : 0 ≤ |A| + |A'| := by positivity
  rw [Fintype.sum_sum_type]
  have h0 : ∑ a : Fin (topRank (bareGrid w) j), |aaExp w j (Sum.inl a)| = 0 :=
    Finset.sum_eq_zero fun a _ => by simp [show aaExp w j (Sum.inl a) = 0 from rfl]
  rw [h0, zero_add]
  have hp : ∀ p : Fin (D.R.m - 1 - j), |aaExp w j (Sum.inr p)| ≤ (D.R.m : ℤ) * (|A| + |A'|) := fun p => by
    have hpv := p.2
    rw [show aaExp w j (Sum.inr p) = A * ((D.R.m - 1 - j - p.val : ℕ) : ℤ) - A' * (p.val + 1) from rfl]
    have e1 : (((D.R.m - 1 - j - p.val : ℕ) : ℤ)) ≤ D.R.m := by omega
    have e2 : ((p.val : ℤ) + 1) ≤ D.R.m := by omega
    have e3 : (0 : ℤ) ≤ ((D.R.m - 1 - j - p.val : ℕ) : ℤ) := by positivity
    calc |A * ((D.R.m - 1 - j - p.val : ℕ) : ℤ) - A' * (p.val + 1)|
        ≤ |A * ((D.R.m - 1 - j - p.val : ℕ) : ℤ)| + |A' * (p.val + 1)| := abs_sub _ _
      _ = |A| * ((D.R.m - 1 - j - p.val : ℕ) : ℤ) + |A'| * (p.val + 1) := by
          rw [abs_mul, abs_mul, abs_of_nonneg e3, abs_of_nonneg (by positivity : (0 : ℤ) ≤ p.val + 1)]
      _ ≤ |A| * D.R.m + |A'| * D.R.m := add_le_add (mul_le_mul_of_nonneg_left e1 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left e2 (abs_nonneg _))
      _ = _ := by ring
  calc ∑ p : Fin (D.R.m - 1 - j), |aaExp w j (Sum.inr p)| ≤ ∑ _p : Fin (D.R.m - 1 - j), (D.R.m : ℤ) * (|A| + |A'|) :=
        Finset.sum_le_sum fun p _ => hp p
    _ = ((D.R.m - 1 - j : ℕ) : ℤ) * ((D.R.m : ℤ) * (|A| + |A'|)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by omega) (by positivity)

theorem factor (w : Pl D.host.E) (hs : 1 ≤ (bareGrid w).s) (g : (bareGrid w).VertexGroup) {j : ℕ} (hj : j < (bareGrid w).m)
    (hg : g ((bareGrid w).m, j) = aaElt w j) : ∃ z : ℤ,
    invVol (conjLevel hs (fun _ => KO _ _) g hj) = (resCard (Kw w) : ℚ) ^ z ∧
      |z| ≤ (bigN D : ℤ) * ((D.R.m : ℤ) * ((D.R.m : ℤ) * (|FractionalIdeal.count D.host.E w D.host.AA| +
        |FractionalIdeal.count D.host.E w D.host.AAbar|))) := by
  rw [conjLevel_KO, hg, toFrame_aaElt w hs hj]
  obtain ⟨z, hz, hzb⟩ := invVol_diag_zpow (unifAt w) (isUnif_unifAt w) (aaExp w j)
  refine ⟨z, hz, hzb.trans ?_⟩
  have hc : (Fintype.card (Fin (topRank (bareGrid w) j) ⊕ Fin (D.R.m - 1 - j)) : ℤ) ≤ bigN D := by
    have h := topRank_add hs j
    have hr := rank_le_bigN w hj
    have hm : (bareGrid w).m = D.R.m := rfl
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    exact_mod_cast (show topRank (bareGrid w) j + (D.R.m - 1 - j) ≤ bigN D by omega)
  exact mul_le_mul hc (sum_abs_aaExp_le w j) (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)

end Main

theorem aaTerm_coef_eq_zpow {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)
    (w : Pl D.host.E) : ∃ n : ℤ, (aaTerm W w).coef = (resCard (Kw w) : ℚ) ^ n ∧
      |n| ≤ 2 * ((D.R.m : ℤ) ^ 3 * (bigN D : ℤ) ^ 2 * (|FractionalIdeal.count D.host.E w D.host.AA| +
        |FractionalIdeal.count D.host.E w D.host.AAbar|)) := by
  set B := (bigN D : ℤ) * ((D.R.m : ℤ) * ((D.R.m : ℤ) * (|FractionalIdeal.count D.host.E w D.host.AA| +
        |FractionalIdeal.count D.host.E w D.host.AAbar|))) with hB
  have hz : ∀ i : Fin ((bareGrid w).m - 2), ∃ z : ℤ, invVol (conjLevel (G := bareGrid w) one_le_sLen (fun _ => KO _ _)
      ((Reps.through (G := bareGrid w) one_le_sLen (fun _ => KO _ _) (aaElt w)).elt
        fun i => DoubleCoset.mk _ _ (aaElt w (i + 1))) (j := i + 1) (by omega)) = (resCard (Kw w) : ℚ) ^ z ∧ |z| ≤ B :=
    fun i => factor w one_le_sLen _ _ (through_elt _ (by omega))
  choose z hz hzb using hz
  refine ⟨∑ i, z i, ?_, ?_⟩
  · show ∏ i : Fin ((bareGrid w).m - 2), _ = _
    rw [Finset.prod_congr rfl fun i _ => hz i]
    exact prod_zpow_eq _ _ resCard_ne_zero _
  · have hB0 : 0 ≤ B := by positivity
    calc |∑ i, z i| ≤ ∑ i, |z i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin ((bareGrid w).m - 2), B := Finset.sum_le_sum fun i _ => hzb i
      _ = (((bareGrid w).m - 2 : ℕ) : ℤ) * B := by simp
      _ ≤ (D.R.m : ℤ) * B := mul_le_mul_of_nonneg_right (by simp only [bareGrid]; omega) hB0
      _ ≤ _ := by
        have hN : (bigN D : ℤ) ≤ (bigN D : ℤ) ^ 2 := by
          rcases Nat.eq_zero_or_pos (bigN D) with h | h
          · simp [h]
          · nlinarith [show (1 : ℤ) ≤ bigN D by exact_mod_cast h]
        have hA : 0 ≤ |FractionalIdeal.count D.host.E w D.host.AA| + |FractionalIdeal.count D.host.E w D.host.AAbar| :=
          by positivity
        have hm : (0 : ℤ) ≤ D.R.m := by positivity
        rw [hB]
        have : (D.R.m : ℤ) * ((bigN D : ℤ) * ((D.R.m : ℤ) * ((D.R.m : ℤ) * (|FractionalIdeal.count D.host.E w D.host.AA| +
          |FractionalIdeal.count D.host.E w D.host.AAbar|)))) = (bigN D : ℤ) * ((D.R.m : ℤ) ^ 3 *
          (|FractionalIdeal.count D.host.E w D.host.AA| + |FractionalIdeal.count D.host.E w D.host.AAbar|)) := by ring
        rw [this]
        have h3 : 0 ≤ (D.R.m : ℤ) ^ 3 * (|FractionalIdeal.count D.host.E w D.host.AA| +
          |FractionalIdeal.count D.host.E w D.host.AAbar|) := by positivity
        nlinarith

end GlobalTheory.FunObj.AaCoef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingTermCoefEqResidueCardZpowStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldingTerm_coef_eq_residueCard_zpow : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (w : Pl D.host.E), ∃ n : ℤ, (aaTerm W w).coef = (resCard (Kw w) : ℚ) ^ n ∧ |n| ≤ 2 * ((D.R.m : ℤ) ^ 3 * (bigN D : ℤ) ^ 2 * (|FractionalIdeal.count D.host.E w D.host.AA| + |FractionalIdeal.count D.host.E w D.host.AAbar|)) := by
  first | exact @GlobalTheory.FunObj.AaCoef.aaTerm_coef_eq_zpow | exact GlobalTheory.FunObj.AaCoef.aaTerm_coef_eq_zpow | (intros; apply GlobalTheory.FunObj.AaCoef.aaTerm_coef_eq_zpow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDiagonalConjLastSimpleReflectionCell
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDiagonalConjLastSimpleReflectionCell
noncomputable section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

namespace GlobalTheory

namespace WeylCell

namespace WeylUnipotentShell

section Diag

variable {L : Type} [Field L] {σ : L →+* L} {n : ℕ}

theorem diag_inv_of_diag (t : GU σ n)
    (ht : ∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) :
    ∀ i j, i ≠ j → (((t⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0 := by
  intro i j hij
  have h := (GlobalTheory.LGrp.mem_GU_iff σ n (t : GL (Fin n) L)).1 t.2 i j
  rw [Subgroup.coe_inv, h, ht _ _ (fun e => hij (Fin.rev_injective e).symm), map_zero]

theorem diag_mul_mul_diag_apply (s u t : GU σ n)
    (hs : ∀ i j, i ≠ j → ((s : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0)
    (ht : ∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) (i j : Fin n) :
    (((s * u * t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      ((s : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i * ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j *
        ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j j := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, Matrix.mul_apply,
    Finset.sum_eq_single j (fun b _ hb => by rw [ht b j hb, mul_zero]) (by simp), Matrix.mul_apply,
    Finset.sum_eq_single i (fun b _ hb => by rw [hs i b (Ne.symm hb), zero_mul]) (by simp)]

theorem diag_inv_mul_diag (t : GU σ n)
    (ht : ∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) (i : Fin n) :
    (((t⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i *
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1 := by
  have h := diag_mul_mul_diag_apply t⁻¹ 1 t (diag_inv_of_diag t ht) ht i i
  rw [mul_one, inv_mul_cancel] at h
  simpa using h.symm

end Diag

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem v_cornerU_conj {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {n : ℕ} (k : Fin (n / 2))
    (t : GU σ n) (ht : ∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) (u : GU σ n) :
    Valued.v (cornerU k (t⁻¹ * u * t)) =
      WithZero.exp (2 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) *
        Valued.v (cornerU k u) := by
  unfold cornerU
  rw [diag_mul_mul_diag_apply _ _ _ (diag_inv_of_diag t ht) ht]
  have h1 := diag_inv_mul_diag t ht (lo k)
  have h2 := (GlobalTheory.LGrp.mem_GU_iff σ n (t : GL (Fin n) L)).1 t.2 (lo k) (lo k)
  rw [← Subgroup.coe_inv] at h2
  have h0 : ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k) ≠ 0 := right_ne_zero_of_mul_eq_one h1
  have h3 : Valued.v ((((t⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k)) =
      WithZero.exp (ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) := by
    rw [eq_inv_of_mul_eq_one_left h1, map_inv₀, GlobalTheory.BorelUMod.v_eq_exp h0, ← WithZero.exp_neg, neg_neg]
  have h4 : Valued.v (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k).rev (lo k).rev) =
      WithZero.exp (ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) := by
    rw [← h3, h2, hσ]
  rw [map_mul, map_mul, h3, h4, two_mul, WithZero.exp_add, mul_right_comm]

theorem conj_mem_cellU_last [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q)
    {n : ℕ} {k : Fin (n / 2)} (hk : ¬ k.val + 1 < n / 2) (hn : ¬ Even n)
    {y : GU σ n} (hy : y ∈ KU σ n) (hw : IsWeylRep (simpleU k) (y : GL (Fin n) L))
    (t : GU σ n) (ht : ∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0)
    (u : GU σ n) (hu : u ∈ cellU y) : t⁻¹ * u * t ∈ cellU y := by
  rw [mem_cellU_last_iff L ϖ σ q hU n k hk hn y hy hw] at hu ⊢
  obtain ⟨⟨hb, hd⟩, hz⟩ := hu
  have e := diag_mul_mul_diag_apply t⁻¹ u t (diag_inv_of_diag t ht) ht
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij h => ?_⟩
  · rw [e, hb i j hij, mul_zero, zero_mul]
  · rw [e, hd i, mul_one, diag_inv_mul_diag t ht]
  · rw [e, hz i j hij h, mul_zero, zero_mul]

theorem integral_conj_diag_cellU_last :
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ [MeasurableSpace (cellU y)] [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure],
      μ ((KU σ n).subgroupOf (cellU y)) = 1 →
    ∀ t : GU σ n, (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) →
      (∀ F : GU σ n → ℂ, ∫ u : cellU y, F (t⁻¹ * (u : GU σ n) * t) ∂μ =
        (q : ℂ) ^ (-4 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) * ∫ u : cellU y, F (u : GU σ n) ∂μ) ∧
      (∀ F : GU σ n → ENNReal, ∫⁻ u : cellU y, F (t⁻¹ * (u : GU σ n) * t) ∂μ =
        ‖(q : ℂ) ^ (-4 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k)))‖ₑ * ∫⁻ u : cellU y, F (u : GU σ n) ∂μ) := by
  intro L _ _ _ ϖ σ q hU n k hk hn y hy hw _ _ μ _ hμ t ht
  have hsh := (GlobalTheory.T.unitaryWeylCellShell_isOpenCompactSubgroup L ϖ σ q hU n k hk hn y hy hw).1
  have hvol := GlobalTheory.T.haar_measure_weyl_cell_odd_unitary L ϖ σ q hU n k hk hn y hy hw μ hμ
  have hcv := v_cornerU_conj hU.2.1 k t ht
  have hq : (2 : ℕ) ≤ q := hU.2.2.2.2.2.1
  generalize ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k)) = o at hcv ⊢
  have hm := conj_mem_cellU_last hU hk hn hy hw t ht
  have hm' := conj_mem_cellU_last hU hk hn hy hw t⁻¹ (diag_inv_of_diag t ht)
  let κ : cellU y ≃* cellU y :=
    { toFun := fun u => ⟨t⁻¹ * u * t, hm u u.2⟩
      invFun := fun u => ⟨t⁻¹⁻¹ * u * t⁻¹, hm' u u.2⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun u v => Subtype.ext (by simp [mul_assoc]) }
  have hc : Continuous κ := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  have hc' : Continuous κ.symm := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  let e : cellU y ≃ᵐ cellU y := (Homeomorph.mk κ.toEquiv hc hc').toMeasurableEquiv
  have he : ∀ u : cellU y, ((e u : cellU y) : GU σ n) = t⁻¹ * u * t := fun u => rfl
  haveI : (μ.map e).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ κ hc hc'
  haveI : LocallyCompactSpace (cellU y) :=
    (hsh 0).2.1.locallyCompactSpace_of_mem_nhds_of_group ((hsh 0).1.mem_nhds (hsh 0).2.2.1)
  have hpre : ∀ j : ℤ, e ⁻¹' shellU k y j = shellU k y (j - 2 * o) := by
    intro j
    ext u
    simp only [Set.mem_preimage, shellU, Set.mem_setOf_eq, he, hcv]
    rw [WithZero.exp_sub, le_div_iff₀' (WithZero.exp_pos)]
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hnorm : ‖(q : ℂ) ^ (-4 * o)‖ = (q : ℝ) ^ (-4 * o) := by
    rw [norm_zpow, Complex.norm_natCast]
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (a : ℤ) = |o| := ⟨o.natAbs, by simp⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, (b : ℤ) = a - o := ⟨(a - o).toNat, by
    rw [Int.toNat_of_nonneg]; rw [ha]; linarith [le_abs_self o]⟩
  have key : μ.map e = ‖(q : ℂ) ^ (-4 * o)‖ₑ • μ := by
    refine GlobalTheory.T.haarMeasure_unique_sigmaCompact_normalised_compactOpen (cellU y) μ (μ.map e) (fun j : ℕ => shellU k y j)
      (fun j => ⟨(hsh j).2.1, (hsh j).1.measurableSet⟩) ?_ (shellU k y ((2 * a : ℕ) : ℤ)) _ (hsh _).1 (hsh _).2.1
      ⟨1, (hsh _).2.2.1⟩ ?_
    · exact Set.eq_univ_of_forall fun u => Set.mem_iUnion.2 ⟨_, mem_shellU_depth k y u⟩
    · rw [e.map_apply, hpre]
      have h2 : ((2 * a : ℕ) : ℤ) - 2 * o = ((2 * b : ℕ) : ℤ) := by push_cast; rw [hb]; ring
      rw [h2, hvol, hvol, ← ofReal_norm_eq_enorm, hnorm, ← ENNReal.ofReal_natCast q,
        ← ENNReal.ofReal_pow (Nat.cast_nonneg q), ← ENNReal.ofReal_pow (Nat.cast_nonneg q),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hq0]
      congr 1
      have e1 : 2 * a / 2 = a := by omega
      have e2 : 2 * b / 2 = b := by omega
      rw [e1, e2]
      push_cast
      rw [hb]; ring
  refine ⟨fun F => ?_, fun F => ?_⟩
  · have h := integral_map_equiv (μ := μ) e (fun u : cellU y => F (u : GU σ n))
    rw [key, integral_smul_measure, toReal_enorm, hnorm, Complex.real_smul] at h
    simp only [he] at h
    rw [← h]
    push_cast
    rfl
  · have h := lintegral_map_equiv (μ := μ) (fun u : cellU y => F (u : GU σ n)) e
    rw [key, lintegral_smul_measure, smul_eq_mul] at h
    simp only [he] at h
    exact h.symm

end WeylUnipotentShell

end WeylCell

end GlobalTheory

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDiagonalConjLastSimpleReflectionCellStatement
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_diagonal_conj_lastSimpleReflectionCell : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ [MeasurableSpace (cellU y)] [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure],
      μ ((KU σ n).subgroupOf (cellU y)) = 1 →
    ∀ t : GU σ n, (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) →
      (∀ F : GU σ n → ℂ, ∫ u : cellU y, F (t⁻¹ * (u : GU σ n) * t) ∂μ =
        (q : ℂ) ^ (-4 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) * ∫ u : cellU y, F (u : GU σ n) ∂μ) ∧
      (∀ F : GU σ n → ENNReal, ∫⁻ u : cellU y, F (t⁻¹ * (u : GU σ n) * t) ∂μ =
        ‖(q : ℂ) ^ (-4 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k)))‖ₑ * ∫⁻ u : cellU y, F (u : GU σ n) ∂μ) := by
  first | exact @GlobalTheory.WeylCell.WeylUnipotentShell.integral_conj_diag_cellU_last | exact GlobalTheory.WeylCell.WeylUnipotentShell.integral_conj_diag_cellU_last | (intros; apply GlobalTheory.WeylCell.WeylUnipotentShell.integral_conj_diag_cellU_last <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDepthPowerLastSimpleReflectionCell
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumSu21RankOneSeriesDifferences
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumSu21RankOneSeriesDifferences
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

namespace GlobalTheory.SURankOneSeries

theorem term_even (q z : ℂ) (hq : q ≠ 0) (i : ℕ) :
    (z / q ^ 2) ^ (2 * i) * q ^ (2 * i + 2 * (2 * i / 2)) = (z ^ 2) ^ i := by
  have h : 2 * i / 2 = i := by omega
  rw [h, div_pow, ← pow_mul, show 2 * i + 2 * i = 2 * (2 * i) by ring, ← pow_mul]
  field_simp

theorem term_odd (q z : ℂ) (hq : q ≠ 0) (i : ℕ) :
    (z / q ^ 2) ^ (2 * i + 1) * q ^ (2 * i + 1 + 2 * ((2 * i + 1) / 2)) = z / q * (z ^ 2) ^ i := by
  have h : (2 * i + 1) / 2 = i := by omega
  rw [h]
  have h4 : 2 * i + 1 + 2 * i = 2 * (2 * i) + 1 := by ring
  rw [h4]
  simp only [div_pow, ← pow_mul]
  rw [show 2 * (2 * i + 1) = (2 * (2 * i) + 1) + 1 by ring, pow_succ q (2 * (2 * i) + 1)]
  field_simp
  ring

theorem hasSum_weighted (q z : ℂ) (hq : q ≠ 0) (hz : ‖z‖ < 1) :
    HasSum (fun j : ℕ => (z / q ^ 2) ^ j * q ^ (j + 2 * (j / 2))) ((1 + q⁻¹ * z) / (1 - z ^ 2)) := by
  have hz2 : ‖z ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg z]
  have hg := hasSum_geometric_of_norm_lt_one hz2
  have he : HasSum (fun k : ℕ => (z / q ^ 2) ^ (2 * k) * q ^ (2 * k + 2 * (2 * k / 2))) (1 - z ^ 2)⁻¹ := by
    have : (fun k : ℕ => (z / q ^ 2) ^ (2 * k) * q ^ (2 * k + 2 * (2 * k / 2))) = fun k => (z ^ 2) ^ k :=
      funext fun k => term_even q z hq k
    rw [this]; exact hg
  have ho : HasSum (fun k : ℕ => (z / q ^ 2) ^ (2 * k + 1) * q ^ (2 * k + 1 + 2 * ((2 * k + 1) / 2)))
      (z / q * (1 - z ^ 2)⁻¹) := by
    have : (fun k : ℕ => (z / q ^ 2) ^ (2 * k + 1) * q ^ (2 * k + 1 + 2 * ((2 * k + 1) / 2))) =
        fun k => z / q * (z ^ 2) ^ k := funext fun k => term_odd q z hq k
    rw [this]; exact hg.mul_left _
  have h1 : (1 : ℂ) - z ^ 2 ≠ 0 := by
    intro h
    have : z ^ 2 = 1 := by linear_combination -h
    have : ‖z ^ 2‖ = 1 := by rw [this, norm_one]
    linarith
  have e : (1 - z ^ 2)⁻¹ + z / q * (1 - z ^ 2)⁻¹ = (1 + q⁻¹ * z) / (1 - z ^ 2) := by
    field_simp
  rw [← e]
  exact HasSum.even_add_odd (f := fun j : ℕ => (z / q ^ 2) ^ j * q ^ (j + 2 * (j / 2))) he ho

theorem hasSum_series : ∀ (q : ℕ), 2 ≤ q → ∀ z : ℂ, ‖z‖ < 1 →
    HasSum (fun j : ℕ => (z / (q : ℂ) ^ 2) ^ j *
      ((q : ℂ) ^ (j + 2 * (j / 2)) - (if j = 0 then 0 else (q : ℂ) ^ (j - 1 + 2 * ((j - 1) / 2))))) (cSU q z) := by
  intro q hq z hz
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hA := hasSum_weighted (q : ℂ) z hq0 hz
  set w : ℂ := z / (q : ℂ) ^ 2 with hw
  set S : ℂ := (1 + (q : ℂ)⁻¹ * z) / (1 - z ^ 2) with hS
  set a : ℕ → ℂ := fun j => w ^ j * (q : ℂ) ^ (j + 2 * (j / 2)) with ha
  set b : ℕ → ℂ := fun j => if j = 0 then 0 else w * a (j - 1) with hb
  have hB : HasSum b (w * S) := by
    refine (hasSum_nat_add_iff' 1).mp ?_
    have e : (fun n => b (n + 1)) = fun n => w * a n := by
      funext n; simp [hb]
    rw [e]
    simpa [hb] using hA.mul_left w
  have hfun : (fun j : ℕ => w ^ j *
      ((q : ℂ) ^ (j + 2 * (j / 2)) - (if j = 0 then 0 else (q : ℂ) ^ (j - 1 + 2 * ((j - 1) / 2))))) =
      fun j => a j - b j := by
    funext j
    rcases j with _ | n
    · simp [ha, hb]
    · simp only [ha, hb, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      rw [pow_succ]; ring
  rw [hfun]
  have h1 : (1 : ℂ) - z ^ 2 ≠ 0 := by
    intro h
    have : z ^ 2 = 1 := by linear_combination -h
    have : ‖z ^ 2‖ = 1 := by rw [this, norm_one]
    rw [norm_pow] at this
    nlinarith [norm_nonneg z]
  have e : cSU (q : ℂ) z = S - w * S := by
    rw [cSU, hS, hw]
    field_simp
  rw [e]
  exact hA.sub hB

end GlobalTheory.SURankOneSeries
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumSu21RankOneSeriesDifferencesStatement
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_cSU_power_differences : ∀ (q : ℕ), 2 ≤ q → ∀ z : ℂ, ‖z‖ < 1 →
    HasSum (fun j : ℕ => (z / (q : ℂ) ^ 2) ^ j *
      ((q : ℂ) ^ (j + 2 * (j / 2)) - (if j = 0 then 0 else (q : ℂ) ^ (j - 1 + 2 * ((j - 1) / 2))))) (cSU q z) := by
  first | exact @GlobalTheory.SURankOneSeries.hasSum_series | exact GlobalTheory.SURankOneSeries.hasSum_series | (intros; apply GlobalTheory.SURankOneSeries.hasSum_series <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDepthPowerLastSimpleReflectionCell
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

namespace GlobalTheory.WeylCell.WeylUnipotentShell.Atone

theorem level_sets {X : Type} [MeasurableSpace X] (μ : Measure X) (f : X → ℕ) (V : ℕ → ℝ)
    (hmeas : ∀ j : ℕ, MeasurableSet {x | f x ≤ j})
    (hV : ∀ j, μ {x | f x ≤ j} = ENNReal.ofReal (V j))
    (hV0 : ∀ j, 0 ≤ V j) :
    Measurable f ∧ ∀ j, μ (f ⁻¹' {j}) = ENNReal.ofReal (V j - if j = 0 then 0 else V (j - 1)) := by
  have hset : ∀ i : ℕ, f ⁻¹' {i + 1} = {x | f x ≤ i + 1} \ {x | f x ≤ i} := by
    intro i; ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_diff, Set.mem_setOf_eq]; omega
  have hset0 : f ⁻¹' {0} = {x | f x ≤ 0} := by
    ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]; omega
  refine ⟨measurable_to_countable' fun j => ?_, fun j => ?_⟩
  · rcases j with _ | i
    · rw [hset0]; exact hmeas 0
    · rw [hset]; exact (hmeas _).diff (hmeas _)
  · rcases j with _ | i
    · rw [hset0, hV]; simp
    · have hsub : {x | f x ≤ i} ⊆ {x | f x ≤ i + 1} := fun x hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢; omega
      rw [hset, measure_diff hsub (hmeas i).nullMeasurableSet (by rw [hV]; exact ENNReal.ofReal_ne_top),
        hV, hV, if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel, ENNReal.ofReal_sub _ (hV0 i)]

theorem sums_over_levels {X : Type} [MeasurableSpace X] (μ : Measure X) (f : X → ℕ) (hf : Measurable f)
    (w : ℕ → ℝ) (hw0 : ∀ j, 0 ≤ w j) (hw : ∀ j, μ (f ⁻¹' {j}) = ENNReal.ofReal (w j))
    (c : ℕ → ℂ) (s : ℂ) (hs : HasSum (fun j => c j * (w j : ℂ)) s) (r : ℝ)
    (hr : HasSum (fun j => ‖c j‖ * w j) r) :
    ∫⁻ x, ‖c (f x)‖ₑ ∂μ = ENNReal.ofReal r ∧ Integrable (fun x => c (f x)) μ ∧ ∫ x, c (f x) ∂μ = s := by
  have hmap : ∀ j, (μ.map f) {j} = ENNReal.ofReal (w j) := fun j => by
    rw [Measure.map_apply hf (measurableSet_singleton j)]; exact hw j
  have hL : ∫⁻ x, ‖c (f x)‖ₑ ∂μ = ENNReal.ofReal r := by
    rw [← lintegral_map (f := fun j => ‖c j‖ₑ) measurable_from_nat hf, lintegral_countable']
    simp_rw [hmap]
    rw [← hr.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (norm_nonneg _) (hw0 j)) hr.summable]
    congr 1; funext j
    rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_eq_enorm]
  have hI : Integrable (fun x => c (f x)) μ := by
    refine ⟨(measurable_from_nat.comp hf).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, hL]; exact ENNReal.ofReal_lt_top
  refine ⟨hL, hI, ?_⟩
  have hIm : Integrable c (μ.map f) :=
    (integrable_map_measure measurable_from_nat.aestronglyMeasurable hf.aemeasurable).2 hI
  rw [← integral_map hf.aemeasurable measurable_from_nat.aestronglyMeasurable, integral_countable hIm,
    ← hs.tsum_eq]
  congr 1; funext j
  rw [measureReal_def, hmap, ENNReal.toReal_ofReal (hw0 j), Complex.real_smul, mul_comm]

end GlobalTheory.WeylCell.WeylUnipotentShell.Atone


open GlobalTheory.WeylCell.WeylUnipotentShell.Atone in
theorem _root_.GlobalTheory.WeylCell.WeylUnipotentShell.integral_depth_cell : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ [MeasurableSpace (cellU y)] [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure],
      μ ((KU σ n).subgroupOf (cellU y)) = 1 →
    ∀ z : ℂ, ‖z‖ < 1 →
      Integrable (fun u : cellU y => (z / (q : ℂ) ^ 2) ^ depthU k (u : GU σ n)) μ ∧
      ∫ u : cellU y, (z / (q : ℂ) ^ 2) ^ depthU k (u : GU σ n) ∂μ = cSU q z ∧
      ∫⁻ u : cellU y, ‖(z / (q : ℂ) ^ 2) ^ depthU k (u : GU σ n)‖ₑ ∂μ = ‖cSU q ((‖z‖ : ℝ) : ℂ)‖ₑ := by
  intro L _ _ _ ϖ σ q hq n k hk hn y hy hwy _ _ μ _ hμ z hz
  have q2 : 2 ≤ q := hq.2.2.2.2.2.1
  have hsh := GlobalTheory.T.unitaryWeylCellShell_isOpenCompactSubgroup L ϖ σ q hq n k hk hn y hy hwy
  have hvol := GlobalTheory.T.haar_measure_weyl_cell_odd_unitary L ϖ σ q hq n k hk hn y hy hwy μ hμ
  let f : cellU y → ℕ := fun u => depthU k (u : GU σ n)
  let V : ℕ → ℝ := fun j => (q : ℝ) ^ (j + 2 * (j / 2))
  have hV0 : ∀ j, 0 ≤ V j := fun j => by positivity
  have hlev : ∀ j : ℕ, {u : cellU y | f u ≤ j} = shellU k y j := by
    intro j; ext u; exact (mem_shellU_iff_depth k y j u).symm
  have hmeas : ∀ j : ℕ, MeasurableSet {u : cellU y | f u ≤ j} := fun j => by
    rw [hlev]; exact (hsh.1 j).1.measurableSet
  have hV : ∀ j : ℕ, μ {u : cellU y | f u ≤ j} = ENNReal.ofReal (V j) := fun j => by
    rw [hlev, hvol j, ENNReal.ofReal_pow (Nat.cast_nonneg q), ENNReal.ofReal_natCast]
  obtain ⟨hf, hlv⟩ := level_sets μ f V hmeas hV hV0
  let w : ℕ → ℝ := fun j => V j - if j = 0 then 0 else V (j - 1)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hw0 : ∀ j, 0 ≤ w j := fun j => by
    simp only [w, V]
    split_ifs with h
    · simp only [sub_zero]; positivity
    · rw [sub_nonneg]; exact pow_le_pow_right₀ hq1 (by omega)
  have hwc : ∀ j : ℕ, ((w j : ℝ) : ℂ) = (q : ℂ) ^ (j + 2 * (j / 2)) -
      (if j = 0 then 0 else (q : ℂ) ^ (j - 1 + 2 * ((j - 1) / 2))) := fun j => by
    simp only [w, V]; split_ifs <;> push_cast <;> rfl
  let c : ℕ → ℂ := fun j => (z / (q : ℂ) ^ 2) ^ j
  have hs : HasSum (fun j => c j * (w j : ℂ)) (cSU q z) := by
    simp only [c, hwc]; exact GlobalTheory.T.hasSum_cSU_power_differences q q2 z hz
  have hz' : ‖((‖z‖ : ℝ) : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]; exact hz
  have hs' := GlobalTheory.T.hasSum_cSU_power_differences q q2 _ hz'
  have hterm : ∀ j : ℕ, (((‖z‖ : ℝ) : ℂ) / (q : ℂ) ^ 2) ^ j *
      ((q : ℂ) ^ (j + 2 * (j / 2)) - (if j = 0 then 0 else (q : ℂ) ^ (j - 1 + 2 * ((j - 1) / 2)))) =
      ((‖c j‖ * w j : ℝ) : ℂ) := fun j => by
    rw [← hwc]; simp only [c, norm_pow, norm_div, Complex.norm_natCast]; push_cast; rfl
  simp only [hterm] at hs'
  have hsum : Summable (fun j => ‖c j‖ * w j) := Complex.summable_ofReal.1 hs'.summable
  have hr := hsum.hasSum
  have heq : cSU q ((‖z‖ : ℝ) : ℂ) = ((∑' j, ‖c j‖ * w j : ℝ) : ℂ) :=
    hs'.unique (Complex.hasSum_ofReal.2 hr)
  obtain ⟨h1, h2, h3⟩ := sums_over_levels μ f hf w hw0 hlv c _ hs _ hr
  refine ⟨h2, h3, ?_⟩
  rw [h1, heq, ← ofReal_norm_eq_enorm, Complex.norm_real,
    Real.norm_of_nonneg (tsum_nonneg fun j => mul_nonneg (norm_nonneg _) (hw0 j))]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDepthPowerLastSimpleReflectionCellStatement
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_depth_power_lastSimpleReflectionCell : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ [MeasurableSpace (cellU y)] [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure],
      μ ((KU σ n).subgroupOf (cellU y)) = 1 →
    ∀ z : ℂ, ‖z‖ < 1 →
      Integrable (fun u : cellU y => (z / (q : ℂ) ^ 2) ^ depthU k (u : GU σ n)) μ ∧
      ∫ u : cellU y, (z / (q : ℂ) ^ 2) ^ depthU k (u : GU σ n) ∂μ = cSU q z ∧
      ∫⁻ u : cellU y, ‖(z / (q : ℂ) ^ 2) ^ depthU k (u : GU σ n)‖ₑ ∂μ = ‖cSU q ((‖z‖ : ℝ) : ℂ)‖ₑ := by
  first | exact @GlobalTheory.WeylCell.WeylUnipotentShell.integral_depth_cell | exact GlobalTheory.WeylCell.WeylUnipotentShell.integral_depth_cell | (intros; apply GlobalTheory.WeylCell.WeylUnipotentShell.integral_depth_cell <;> assumption)
end
end
