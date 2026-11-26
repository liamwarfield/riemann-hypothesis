module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowVertexAdjacentStepsTranslateFrames

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPhaseLastInnerVertexInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPhaseLastInnerVertexInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport

noncomputable section

namespace GlobalTheory.TopLevelInv

theorem pairing_gl_inv {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (κ : GL n k) (u y : n → k) :
    ∑ r, (∑ s, u s * κ.val s r) * (∑ t, (κ⁻¹).val r t * y t) = ∑ r, u r * y r := by
  change (u ᵥ* κ.val) ⬝ᵥ ((κ⁻¹).val *ᵥ y) = u ⬝ᵥ y
  rw [dotProduct_mulVec, vecMul_vecMul, Units.mul_inv, vecMul_one]

theorem phase_eq_of_lastMove {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (j : ℕ) (hB : j + 2 = Γ.m)
    (κ : GL (Fin (topRank Γ (j + 1))) k) (x x' : ColArgs Γ) (e e' : Vars Γ) :
    (∀ i, i ≠ j → i ≠ j + 1 → x' i = x i) → x' (j + 1) = x (j + 1) * κ.val →
    (∀ i : Fin (Γ.m - 1), i.val ≠ j → e' i = e i) →
    stepPt (x' j) (e' ⟨j, by omega⟩) = ((embX (Γ.m - 2 - j) κ)⁻¹).val * stepPt (x j) (e ⟨j, by omega⟩) →
    phase x e = phase x' e' := by
  intro hx hx1 he hst
  unfold phase
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.2
  rcases Nat.lt_or_ge i.val j with h | h
  · have hxi : x' i = x i := hx _ (by omega) (by omega)
    have hei : e' i = e i := he _ (by omega)
    have hc : colVar x' e' i = colVar x e i := by
      funext r; simp only [colVar, hxi, hei]
    have hch : ch (stepPt (x' i) (e' i)) = ch (stepPt (x i) (e i)) := by rw [hxi, hei]
    rw [hch, hc]
    congr 1
    split_ifs with hev
    · have hr : rowVar x' e' (i + 1) = rowVar x e (i + 1) := by
        have hne : (i : ℕ) + 1 ≠ j := by
          intro h'
          rw [show Γ.m - 2 - (i : ℕ) = 1 by omega] at hev
          exact Nat.not_even_one hev
        funext s
        have h1 : x' (i + 1) = x (i + 1) := hx _ hne (by omega)
        simp only [rowVar, h1]
        split_ifs with h3
        · rw [he ⟨(i : ℕ) + 1, h3⟩ (by simpa using hne)]
        · rfl
      rw [hr]
    · rfl
  · obtain ⟨i, hi'⟩ := i
    have hij : i = j := by simp only at h hi; omega
    subst hij
    have h0 : Γ.m - 2 - i = 0 := by omega
    have hch : ∀ z : Matrix (Fin (topRank Γ (i + 1)) ⊕ Fin (Γ.m - 2 - i)) (Fin (topRank Γ i) ⊕ Fin (Γ.m - 2 - i + 1)) k,
        ch z = 0 := by
      intro z
      haveI : IsEmpty (Fin (Γ.m - 2 - i)) := ⟨fun l => by have := l.2; omega⟩
      simp [ch]
    rw [hch, hch, zero_add, zero_add]
    simp only [Fin.val_mk]
    rw [if_pos (by rw [h0]; exact ⟨0, rfl⟩), if_pos (by rw [h0]; exact ⟨0, rfl⟩)]
    have hrow : ∀ (z : ColArgs Γ) (f : Vars Γ) s, rowVar z f (i + 1) s = z (i + 1) (topLast Γ (i + 1 + 1)) s := by
      intro z f s
      simp only [rowVar]
      rw [dite_eq_right (by omega)]
    simp only [hrow, hx1, colVar, Fin.val_mk, hst, map_inv]
    rw [← map_inv]
    have hv : ∀ (g : GL (Fin (topRank Γ (i + 1))) k) a b,
        (embX (Γ.m - 2 - i) g).val (Sum.inl a) (Sum.inl b) = g.val a b := fun _ _ _ => rfl
    have hv2 : ∀ (g : GL (Fin (topRank Γ (i + 1))) k) a b,
        (embX (Γ.m - 2 - i) g).val (Sum.inl a) (Sum.inr b) = 0 := fun _ _ _ => rfl
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, hv, hv2, zero_mul, Finset.sum_const_zero, add_zero]
    exact (pairing_gl_inv κ _ _).symm

end GlobalTheory.TopLevelInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPhaseLastInnerVertexInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiPhase_lastInnerVertex_invariant : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (j : ℕ) (hB : j + 2 = Γ.m) (κ : GL (Fin (topRank Γ (j + 1))) k) (x x' : ColArgs Γ) (e e' : Vars Γ),
    (∀ i, i ≠ j → i ≠ j + 1 → x' i = x i) → x' (j + 1) = x (j + 1) * κ.val →
    (∀ i : Fin (Γ.m - 1), i.val ≠ j → e' i = e i) →
    stepPt (x' j) (e' ⟨j, by omega⟩) = ((embX (Γ.m - 2 - j) κ)⁻¹).val * stepPt (x j) (e ⟨j, by omega⟩) →
    phase x e = phase x' e' := by
  first | exact @GlobalTheory.TopLevelInv.phase_eq_of_lastMove | exact GlobalTheory.TopLevelInv.phase_eq_of_lastMove | (intros; apply GlobalTheory.TopLevelInv.phase_eq_of_lastMove <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPhaseAdjacentInnerStepsInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPhaseAdjacentInnerStepsInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport

namespace GlobalTheory.TopLevelInv

theorem phase_eq_of_two_steps : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (j : ℕ) (hA : j + 2 < Γ.m) (x x' : ColArgs Γ) (e e' : Vars Γ),
    (∀ i, i ≠ j → i ≠ j + 1 → x' i = x i) → (∀ i : Fin (Γ.m - 1), i.val ≠ j → i.val ≠ j + 1 → e' i = e i) →
    ch (stepPt (x' j) (e' ⟨j, by omega⟩)) + ch (stepPt (x' (j + 1)) (e' ⟨j + 1, by omega⟩)) +
        (if Even (Γ.m - 2 - j) then ∑ r, rowVar x' e' (j + 1) r * colVar x' e' ⟨j, by omega⟩ r else 0) =
      ch (stepPt (x j) (e ⟨j, by omega⟩)) + ch (stepPt (x (j + 1)) (e ⟨j + 1, by omega⟩)) +
        (if Even (Γ.m - 2 - j) then ∑ r, rowVar x e (j + 1) r * colVar x e ⟨j, by omega⟩ r else 0) →
    (Odd (Γ.m - 2 - j) → ∀ s : Fin (topRank Γ j), rowVar x' e' j s = rowVar x e j s) →
    (Odd (Γ.m - 2 - j) → ∀ r : Fin (topRank Γ (j + 1 + 1)), colVar x' e' ⟨j + 1, by omega⟩ r = colVar x e ⟨j + 1, by omega⟩ r) →
    phase x e = phase x' e' := by
  intro k _ _ _ _ _ _ Γ j hA x x' e e' hx he h0 hrow hcol
  have hch : ∀ i : Fin (Γ.m - 1), i.val ≠ j → i.val ≠ j + 1 →
      ch (stepPt (x' i) (e' i)) = ch (stepPt (x i) (e i)) := by
    intro i h1 h2; rw [hx i h1 h2, he i h1 h2]
  have hcv : ∀ i : Fin (Γ.m - 1), i.val ≠ j → i.val ≠ j + 1 → ∀ r, colVar x' e' i r = colVar x e i r := by
    intro i h1 h2 r; simp only [colVar]; rw [hx i h1 h2, he i h1 h2]
  have hrv : ∀ n : ℕ, n ≠ j → n ≠ j + 1 → ∀ s, rowVar x' e' n s = rowVar x e n s := by
    intro n h1 h2 s; unfold rowVar
    split_ifs with h
    · rw [hx n h1 h2, he ⟨n, h⟩ h1 h2]
    · rw [hx n h1 h2]
  have hodd : Even (Γ.m - 2 - (j + 1)) ↔ Odd (Γ.m - 2 - j) := by
    rw [show Γ.m - 2 - j = (Γ.m - 2 - (j + 1)) + 1 by omega, Nat.odd_add_one, Nat.not_odd_iff_even]
  have hP1 : (if Even (Γ.m - 2 - (j + 1)) then ∑ r, rowVar x' e' (j + 1 + 1) r * colVar x' e' ⟨j + 1, by omega⟩ r else 0)
      = (if Even (Γ.m - 2 - (j + 1)) then ∑ r, rowVar x e (j + 1 + 1) r * colVar x e ⟨j + 1, by omega⟩ r else 0) := by
    split_ifs with hE
    · refine Finset.sum_congr rfl fun r _ => ?_
      rw [hrv (j + 1 + 1) (by omega) (by omega), hcol (hodd.1 hE) r]
    · rfl
  unfold phase
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib,
    Fintype.sum_eq_add (⟨j, by omega⟩ : Fin (Γ.m - 1)) ⟨j + 1, by omega⟩ (by simp [Fin.ext_iff]) ?_]
  · have hch1 := h0
    simp only [Fin.val_mk] at hP1 ⊢
    rw [hP1]
    linear_combination -h0
  · rintro ⟨i, hi⟩ ⟨h1, h2⟩
    simp only [ne_eq, Fin.ext_iff, Fin.val_mk] at h1 h2
    rw [sub_eq_zero, hch ⟨i, hi⟩ h1 h2]
    congr 1
    by_cases hij : i + 1 = j
    · subst hij
      split_ifs with hE
      · refine Finset.sum_congr rfl fun r _ => ?_
        rw [hcv ⟨i, hi⟩ h1 h2, hrow ?_ r]
        rw [show Γ.m - 2 - i = (Γ.m - 2 - (i + 1)) + 1 by omega, Nat.even_add_one, Nat.not_even_iff_odd] at hE
        exact hE
      · rfl
    · split_ifs
      · refine Finset.sum_congr rfl fun r _ => ?_
        rw [hcv ⟨i, hi⟩ h1 h2 r, hrv (i + 1) hij (by omega) r]
      · rfl

end GlobalTheory.TopLevelInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPhaseAdjacentInnerStepsInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiPhase_adjacentInnerSteps_invariant : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (j : ℕ) (hA : j + 2 < Γ.m) (x x' : ColArgs Γ) (e e' : Vars Γ),
    (∀ i, i ≠ j → i ≠ j + 1 → x' i = x i) → (∀ i : Fin (Γ.m - 1), i.val ≠ j → i.val ≠ j + 1 → e' i = e i) →
    ch (stepPt (x' j) (e' ⟨j, by omega⟩)) + ch (stepPt (x' (j + 1)) (e' ⟨j + 1, by omega⟩)) +
        (if Even (Γ.m - 2 - j) then ∑ r, rowVar x' e' (j + 1) r * colVar x' e' ⟨j, by omega⟩ r else 0) =
      ch (stepPt (x j) (e ⟨j, by omega⟩)) + ch (stepPt (x (j + 1)) (e ⟨j + 1, by omega⟩)) +
        (if Even (Γ.m - 2 - j) then ∑ r, rowVar x e (j + 1) r * colVar x e ⟨j, by omega⟩ r else 0) →
    (Odd (Γ.m - 2 - j) → ∀ s : Fin (topRank Γ j), rowVar x' e' j s = rowVar x e j s) →
    (Odd (Γ.m - 2 - j) → ∀ r : Fin (topRank Γ (j + 1 + 1)), colVar x' e' ⟨j + 1, by omega⟩ r = colVar x e ⟨j + 1, by omega⟩ r) →
    phase x e = phase x' e' := by
  first | exact @GlobalTheory.TopLevelInv.phase_eq_of_two_steps | exact GlobalTheory.TopLevelInv.phase_eq_of_two_steps | (intros; apply GlobalTheory.TopLevelInv.phase_eq_of_two_steps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingFilledArgsMoveInnerLastColumnVertex
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingFilledArgsMoveInnerLastColumnVertex
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport

noncomputable section
namespace GlobalTheory.TopLevelInv

theorem fill_moveVertex : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (hs : 1 ≤ Γ.s) (j : ℕ) (hj : j + 1 < Γ.m) (g : GL (Fin (Γ.rank (Γ.m, j + 1))) k)
    (x x' : ColArgs Γ) (y : RowArgs Γ) (e e' : Vars Γ),
    (∀ l, l ≠ j → l ≠ j + 1 → downMap hs x' e' l = downMap hs x e l) →
    downMap hs x' e' j = (g⁻¹).val * downMap hs x e j →
    downMap hs x' e' (j + 1) = downMap hs x e (j + 1) * g.val →
    Γ.moveArgs .one (Pi.mulSingle (Γ.m, j + 1) g) (fill hs x y e) = fill hs x' y e' := by
  intro k _ _ _ _ _ _ Γ hs j hj g x x' y e e' hrest hj0 hj1
  funext b
  cases b with
  | theta i l =>
    by_cases hi : i = Γ.m
    · subst hi
      rw [moveArgs_theta, fill_theta, fill_theta, transpose_transpose]
      by_cases hl : l = j
      · subst hl
        have h1 : (Pi.mulSingle (Γ.m, l + 1) g : Γ.VertexGroup) (Γ.m, l) = 1 :=
          Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h) _
        rw [h1, Pi.mulSingle_eq_same, Units.val_one, Matrix.mul_one, hj0]
      · by_cases hl' : l = j + 1
        · subst hl'
          have h1 : (Pi.mulSingle (Γ.m, j + 1) g : Γ.VertexGroup) (Γ.m, j + 1 + 1) = 1 :=
            Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h) _
          rw [h1, Pi.mulSingle_eq_same, inv_one, Units.val_one, Matrix.one_mul, hj1]
        · have h1 : (Pi.mulSingle (Γ.m, j + 1) g : Γ.VertexGroup) (Γ.m, l) = 1 :=
            Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _
          have h2 : (Pi.mulSingle (Γ.m, j + 1) g : Γ.VertexGroup) (Γ.m, l + 1) = 1 :=
            Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _
          simp only [h1, h2, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one, hrest l hl hl']
    · simp [fill, Grid.moveArgs, hi]
  | ex i l =>
    by_cases hl : l = Γ.m
    · subst hl
      have h1 : (Pi.mulSingle (Γ.m, j + 1) g : Γ.VertexGroup) (i, Γ.m) = 1 :=
        Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _
      have h2 : (Pi.mulSingle (Γ.m, j + 1) g : Γ.VertexGroup) (i + 1, Γ.m) = 1 :=
        Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _
      simp only [Grid.moveArgs, Edge.src, Edge.tgt, fill_ex, h1, h2, map_one, inv_one, Units.val_one,
        Matrix.one_mul, Matrix.mul_one]
    · simp [fill, Grid.moveArgs, hl]

end GlobalTheory.TopLevelInv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingFilledArgsMoveInnerLastColumnVertexStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldingFilledArgs_moveInnerLastColumnVertex : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (hs : 1 ≤ Γ.s) (j : ℕ) (hj : j + 1 < Γ.m) (g : GL (Fin (Γ.rank (Γ.m, j + 1))) k)
    (x x' : ColArgs Γ) (y : RowArgs Γ) (e e' : Vars Γ),
    (∀ l, l ≠ j → l ≠ j + 1 → downMap hs x' e' l = downMap hs x e l) →
    downMap hs x' e' j = (g⁻¹).val * downMap hs x e j →
    downMap hs x' e' (j + 1) = downMap hs x e (j + 1) * g.val →
    Γ.moveArgs .one (Pi.mulSingle (Γ.m, j + 1) g) (fill hs x y e) = fill hs x' y e' := by
  first | exact @GlobalTheory.TopLevelInv.fill_moveVertex | exact GlobalTheory.TopLevelInv.fill_moveVertex | (intros; apply GlobalTheory.TopLevelInv.fill_moveVertex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DownwardVertexMapLastVertexMulOfFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DownwardVertexMapLastVertexMulOfFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport

noncomputable section

namespace GlobalTheory.TopLevelInv

theorem frame_symm_of_zero {a c b : ℕ} (h : a + c = b) (hc : c = 0) (p : Fin b) :
    (frame h).symm p = Sum.inl ⟨p.val, by omega⟩ := by
  subst hc
  rw [Equiv.symm_apply_eq]
  ext
  simp only [frame, Equiv.trans_apply, finCongr_apply, Fin.val_cast]
  rfl

theorem downMap_last_mul_of_toFrame_eq : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (hs : 1 ≤ Γ.s) (j : ℕ) (hj : j + 1 < Γ.m) (hB : j + 2 = Γ.m)
    (g : GL (Fin (Γ.rank (Γ.m, j + 1))) k) (κ : GL (Fin (topRank Γ (j + 1))) k),
    toFrame hs hj g = embX (Γ.m - 1 - (j + 1)) κ → ∀ (x x' : ColArgs Γ) (e e' : Vars Γ), x' (j + 1) = x (j + 1) * κ.val →
    downMap hs x' e' (j + 1) = downMap hs x e (j + 1) * g.val := by
  intro k _ _ _ _ _ _ Γ hs j hj hB g κ hg x x' e e' hx
  have hr : Γ.rank (Γ.m, j + 1) = topRank Γ (j + 1) := by have := topRank_add hs (j + 1); omega
  have hval : ∀ p q, g.val p q = κ.val (Fin.cast hr p) (Fin.cast hr q) := by
    intro p q
    have h1 : g = (toFrame hs hj).symm (embX _ κ) := by rw [← hg, MulEquiv.symm_apply_apply]
    rw [h1]
    unfold toFrame
    rw [frameGL_symm_val, submatrix_apply, frame_symm_of_zero _ (by omega), frame_symm_of_zero _ (by omega)]
    rfl
  unfold downMap
  rw [dite_eq_right (by omega), dite_eq_left (by omega), dite_eq_right (by omega), dite_eq_left (by omega), hx]
  ext r q
  simp only [submatrix_apply, Matrix.mul_apply, hval]
  exact (Fintype.sum_equiv (finCongr hr) _ _ (fun p => rfl)).symm

end GlobalTheory.TopLevelInv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DownwardVertexMapLastVertexMulOfFrameStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.downwardVertexMap_lastVertex_mul_of_frame : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (hs : 1 ≤ Γ.s) (j : ℕ) (hj : j + 1 < Γ.m) (hB : j + 2 = Γ.m)
    (g : GL (Fin (Γ.rank (Γ.m, j + 1))) k) (κ : GL (Fin (topRank Γ (j + 1))) k),
    toFrame hs hj g = embX (Γ.m - 1 - (j + 1)) κ → ∀ (x x' : ColArgs Γ) (e e' : Vars Γ), x' (j + 1) = x (j + 1) * κ.val →
    downMap hs x' e' (j + 1) = downMap hs x e (j + 1) * g.val := by
  first | exact @GlobalTheory.TopLevelInv.downMap_last_mul_of_toFrame_eq | exact GlobalTheory.TopLevelInv.downMap_last_mul_of_toFrame_eq | (intros; apply GlobalTheory.TopLevelInv.downMap_last_mul_of_toFrame_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorMoveArgumentsLastRowVertex
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section
namespace GlobalTheory.TopLevelInv.FlatStep
open GlobalTheory.FunObj.FiniteSupport

section Helpers
variable {k : Type} [Field k]

theorem reindex_mul_frameGL {a c b : ℕ} {ι : Type} {a' : ℕ} (h : a + c = b) (f : ι ≃ Fin a') (g : GL (Fin b) k)
    (D : Matrix ι (Fin a ⊕ Fin c) k) :
    D.reindex f (frame h) * g.val = (D * (frameGL h g).val).reindex f (frame h) := by
  ext r s
  simp only [reindex_apply, Matrix.mul_apply, submatrix_apply, frameGL_val]
  exact Fintype.sum_equiv (frame h).symm _ _ fun p => by simp

theorem frameGL_embX_congr {a c c' b : ℕ} (hc : c = c') (h : a + c = b) (h' : a + c' = b) {g : GL (Fin b) k}
    {κ : GL (Fin a) k} (H : frameGL h g = embX c κ) : frameGL h' g = embX c' κ := by
  subst hc; exact H

theorem eq_one_of_mem_symN_zero {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {v : GL (n ⊕ Fin c) k}
    (hv : v ∈ symN k n c) (hc : c = 0) : v = 1 := by
  subst hc
  have key : ∀ p, N k n 0 p = ⊥ := fun p => by
    rw [N, Subgroup.closure_eq_bot_iff]
    intro g hg
    rw [Set.mem_singleton_iff]
    refine Units.ext (Matrix.ext fun r s => ?_)
    rcases r with r | r
    · rcases s with s | s
      · exact hg _ _ le_rfl
      · exact s.elim0
    · exact r.elim0
  rw [symN, key, key, sup_bot_eq, Subgroup.mem_bot] at hv
  exact hv

abbrev StepFam (Γ : Grid k) [MeasurableSpace k] : Type :=
  ∀ i : Fin (Γ.m - 1), (StepVar (Fin (topRank Γ (i + 1))) (Γ.m - 2 - i) (Fin (topRank Γ i)) → k) ≃ᵐ
    (StepVar (Fin (topRank Γ (i + 1))) (Γ.m - 2 - i) (Fin (topRank Γ i)) → k)

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]

theorem measurePreserving_stepFam {Γ : Grid k} (ν : Measure k) [ν.IsAddHaarMeasure] (φ : StepFam Γ)
    (hφ : ∀ i, MeasurePreserving (φ i) (stepVol ν _ _ _) (stepVol ν _ _ _)) :
    MeasurePreserving (MeasurableEquiv.piCongrRight φ) (varsVol Γ ν) (varsVol Γ ν) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : ∀ i : Fin (Γ.m - 1), SigmaFinite (stepVol ν (Fin (topRank Γ (i + 1))) (Γ.m - 2 - i) (Fin (topRank Γ i))) :=
    fun i => by unfold stepVol; infer_instance
  rw [varsVol_eq]
  exact measurePreserving_pi _ _ hφ

theorem measurePreserving_update {Γ : Grid k} (ν : Measure k) (Ψ : StepFam Γ)
    (hΨ : ∀ i, MeasurePreserving (Ψ i) (stepVol ν _ _ _) (stepVol ν _ _ _)) (i₀ : Fin (Γ.m - 1))
    (φ : (StepVar (Fin (topRank Γ (i₀ + 1))) (Γ.m - 2 - i₀) (Fin (topRank Γ i₀)) → k) ≃ᵐ
      (StepVar (Fin (topRank Γ (i₀ + 1))) (Γ.m - 2 - i₀) (Fin (topRank Γ i₀)) → k))
    (hφ : MeasurePreserving φ (stepVol ν _ _ _) (stepVol ν _ _ _)) :
    ∀ i, MeasurePreserving ((Function.update Ψ i₀ φ : StepFam Γ) i) (stepVol ν _ _ _) (stepVol ν _ _ _) := by
  intro i
  rcases eq_or_ne i i₀ with rfl | h
  · rw [Function.update_self]; exact hφ
  · rw [Function.update_of_ne h]; exact hΨ i

theorem flatTensor_comp_of_equiv {Γ : Grid k} (hs : 1 ≤ Γ.s) (ψ : AddChar k Circle) (ν : Measure k) (F : Γ.Args → ℂ)
    (A : Γ.Args → Γ.Args) (x x' : ColArgs Γ) (y : RowArgs Γ) (Φ : Vars Γ ≃ᵐ Vars Γ)
    (hΦ : MeasurePreserving Φ (varsVol Γ ν) (varsVol Γ ν))
    (hfill : ∀ e, A (fill hs x y e) = fill hs x' y (Φ e)) (hph : ∀ e, phase x e = phase x' (Φ e)) :
    flatTensor hs ψ ν (fun z => F (A z)) x y = flatTensor hs ψ ν F x' y := by
  rw [flatTensor, flatTensor, ← hΦ.integral_comp' (flatIntegrand hs ψ F x' y)]
  congr 1
  funext e
  simp only [flatIntegrand, hfill e, hph e]

theorem downMap_congr {Γ : Grid k} (hs : 1 ≤ Γ.s) {x x' : ColArgs Γ} {e e' : Vars Γ} {l : ℕ} (hx : x' l = x l)
    (he : ∀ h : l < Γ.m - 1, e' ⟨l, h⟩ = e ⟨l, h⟩) : downMap hs x' e' l = downMap hs x e l := by
  unfold downMap
  split_ifs with h1
  · rw [hx, he h1]
  · rw [hx]
  · rfl

end Helpers

theorem flatTensor_moveArgs_mulSingle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (hs : 1 ≤ Γ.s) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (F : Γ.Args → ℂ)
    (j : ℕ) (hj : j + 1 < Γ.m) (g : GL (Fin (Γ.rank (Γ.m, j + 1))) k) (κ : GL (Fin (topRank Γ (j + 1))) k),
    valuation k (gdet κ : k) = 1 → ∀ v ∈ symN k (Fin (topRank Γ (j + 1))) (Γ.m - 1 - (j + 1)), toFrame hs hj g = v * embX _ κ →
    ∀ (x : ColArgs Γ) (y : RowArgs Γ),
      flatTensor hs ψ ν (fun z => F (Γ.moveArgs .one (Pi.mulSingle (Γ.m, j + 1) g) z)) x y = flatTensor hs ψ ν F (colMove j κ x) y := by
  intro k _ _ _ _ _ _ Γ hs ψ ν _ F j hj g κ hdet v hv hg x y
  have hcol : ∀ i, i ≠ j → i ≠ j + 1 → colMove j κ x i = x i := fun i h1 h2 => by
    simp only [colMove, Function.update_of_ne h1, Function.update_of_ne h2]
  have hcj : colMove j κ x j = (κ⁻¹).val * x j := by
    simp only [colMove, Function.update_of_ne (show j ≠ j + 1 by omega), Function.update_self]
  have hcj1 : colMove j κ x (j + 1) = x (j + 1) * κ.val := by
    simp only [colMove, Function.update_self]
  rcases Nat.lt_or_ge (j + 2) Γ.m with hA | hB
  · obtain ⟨φ₀, hφ₀, φ₁, hφ₁, H⟩ := GlobalTheory.T.lastRowVertex_adjacentSteps_translate_frames (a₀ := topRank Γ j) (a₂ := topRank Γ (j + 1 + 1))
      (c := Γ.m - 2 - (j + 1)) (c₀ := Γ.m - 2 - j) ν (by omega) (by omega)
      (by have := topRank_add hs (j + 1); omega) (by have := topRank_add hs (j + 1); omega) _ g κ hdet v hv hg
      (x j) (x (j + 1))
    have h01 : (⟨j, by omega⟩ : Fin (Γ.m - 1)) ≠ ⟨j + 1, by omega⟩ := fun h => by simp at h
    let Ψ0 : StepFam Γ := fun i => MeasurableEquiv.refl _
    let Ψ1 : StepFam Γ := Function.update Ψ0 ⟨j, by omega⟩ φ₀
    let Ψ2 : StepFam Γ := Function.update Ψ1 ⟨j + 1, by omega⟩ φ₁
    let Φ : Vars Γ ≃ᵐ Vars Γ := MeasurableEquiv.piCongrRight Ψ2
    have hΦ0 : ∀ e, Φ e ⟨j, by omega⟩ = φ₀ (e ⟨j, by omega⟩) := fun e => by
      show Function.update Ψ1 ⟨j + 1, by omega⟩ φ₁ ⟨j, by omega⟩ (e ⟨j, by omega⟩) = _
      rw [Function.update_of_ne h01]
      show Function.update Ψ0 ⟨j, by omega⟩ φ₀ ⟨j, by omega⟩ (e ⟨j, by omega⟩) = _
      rw [Function.update_self]
    have hΦ1 : ∀ e, Φ e ⟨j + 1, by omega⟩ = φ₁ (e ⟨j + 1, by omega⟩) := fun e => by
      show Function.update Ψ1 ⟨j + 1, by omega⟩ φ₁ ⟨j + 1, by omega⟩ (e ⟨j + 1, by omega⟩) = _
      rw [Function.update_self]
    have hΦo : ∀ e (i : Fin (Γ.m - 1)), i.val ≠ j → i.val ≠ j + 1 → Φ e i = e i := fun e i h1 h2 => by
      show Function.update Ψ1 ⟨j + 1, by omega⟩ φ₁ i (e i) = _
      rw [Function.update_of_ne (fun h => h2 (by rw [h]))]
      show Function.update Ψ0 ⟨j, by omega⟩ φ₀ i (e i) = _
      rw [Function.update_of_ne (fun h => h1 (by rw [h]))]
      rfl
    have hMP : MeasurePreserving Φ (varsVol Γ ν) (varsVol Γ ν) :=
      measurePreserving_stepFam ν Ψ2 (measurePreserving_update ν Ψ1
        (measurePreserving_update ν Ψ0 (fun i => MeasurePreserving.id _) ⟨j, by omega⟩ φ₀ hφ₀) ⟨j + 1, by omega⟩ φ₁ hφ₁)
    refine flatTensor_comp_of_equiv hs ψ ν F _ x (colMove j κ x) y Φ hMP (fun e => ?_) (fun e => ?_)
    · refine GlobalTheory.T.unfoldingFilledArgs_moveInnerLastColumnVertex hs j hj g x (colMove j κ x) y e (Φ e) (fun l h1 h2 => ?_) ?_ ?_
      · exact downMap_congr hs (hcol l h1 h2) fun h => hΦo e ⟨l, h⟩ h1 h2
      · rw [downMap, dite_eq_left (show j < Γ.m - 1 by omega), downMap, dite_eq_left (show j < Γ.m - 1 by omega), hcj, hΦ0]
        exact ((H (e ⟨j, by omega⟩) (e ⟨j + 1, by omega⟩)).1 _).symm
      · rw [downMap, dite_eq_left (show j + 1 < Γ.m - 1 by omega), downMap, dite_eq_left (show j + 1 < Γ.m - 1 by omega),
          hcj1, hΦ1]
        exact ((H (e ⟨j, by omega⟩) (e ⟨j + 1, by omega⟩)).2.1 _).symm
    · have hrow : ∀ (x : ColArgs Γ) (e : Vars Γ) r, rowVar x e (j + 1) r = ∑ l : Fin (Γ.m - 2 - (j + 1)),
          if l.val = (Γ.m - 2 - (j + 1)) / 2 then stepPt (x (j + 1)) (e ⟨j + 1, by omega⟩) (.inr l) (.inl r) else 0 :=
        fun x e r => by rw [rowVar, dite_eq_left (by omega)]
      refine GlobalTheory.T.fourierJacobiPhase_adjacentInnerSteps_invariant j hA x (colMove j κ x) e (Φ e) hcol (fun i h1 h2 => hΦo e i h1 h2) ?_ ?_ ?_
      · simp only [hrow, colVar]
        rw [hcj, hcj1, hΦ0, hΦ1]
        exact (H (e ⟨j, by omega⟩) (e ⟨j + 1, by omega⟩)).2.2.1
      · intro ho s
        rw [rowVar, rowVar, dite_eq_left (by omega), dite_eq_left (by omega)]
        refine Finset.sum_congr rfl fun l _ => ?_
        split_ifs with hl
        · rw [hcj, hΦ0]
          exact (H (e ⟨j, by omega⟩) (e ⟨j + 1, by omega⟩)).2.2.2.1 ho l s hl
        · rfl
      · intro ho r
        simp only [colVar]
        rw [hcj1, hΦ1]
        exact (H (e ⟨j, by omega⟩) (e ⟨j + 1, by omega⟩)).2.2.2.2 ho r _ rfl
  · have hB' : j + 2 = Γ.m := by omega
    obtain rfl : v = 1 := eq_one_of_mem_symN_zero hv (by omega)
    have hg' : toFrame hs hj g = embX _ κ := by rw [hg, one_mul]
    obtain ⟨φ₀, hφ₀, H⟩ := GlobalTheory.T.fourierJacobiStep_leftChange_measurePreserving (n := Fin (topRank Γ (j + 1))) (n' := Fin (topRank Γ j)) (c := Γ.m - 2 - j)
      ν 1 (one_mem _) κ hdet (x j)
    let Ψ0 : StepFam Γ := fun i => MeasurableEquiv.refl _
    let Ψ1 : StepFam Γ := Function.update Ψ0 ⟨j, by omega⟩ φ₀
    let Φ : Vars Γ ≃ᵐ Vars Γ := MeasurableEquiv.piCongrRight Ψ1
    have hΦ0 : ∀ e, Φ e ⟨j, by omega⟩ = φ₀ (e ⟨j, by omega⟩) := fun e => by
      show Function.update Ψ0 ⟨j, by omega⟩ φ₀ ⟨j, by omega⟩ (e ⟨j, by omega⟩) = _
      rw [Function.update_self]
    have hΦo : ∀ e (i : Fin (Γ.m - 1)), i.val ≠ j → Φ e i = e i := fun e i h1 => by
      show Function.update Ψ0 ⟨j, by omega⟩ φ₀ i (e i) = _
      rw [Function.update_of_ne (fun h => h1 (by rw [h]))]
      rfl
    have hMP : MeasurePreserving Φ (varsVol Γ ν) (varsVol Γ ν) :=
      measurePreserving_stepFam ν Ψ1 (measurePreserving_update ν Ψ0 (fun i => MeasurePreserving.id _) ⟨j, by omega⟩ φ₀ hφ₀)
    have hf : frameGL (show topRank Γ (j + 1) + (Γ.m - 2 - j) = Γ.rank (Γ.m, j + 1) by
        have := topRank_add hs (j + 1); omega) g = embX (Γ.m - 2 - j) κ :=
      frameGL_embX_congr (by omega) _ _ hg'
    refine flatTensor_comp_of_equiv hs ψ ν F _ x (colMove j κ x) y Φ hMP (fun e => ?_) (fun e => ?_)
    · refine GlobalTheory.T.unfoldingFilledArgs_moveInnerLastColumnVertex hs j hj g x (colMove j κ x) y e (Φ e) (fun l h1 h2 => ?_) ?_ ?_
      · exact downMap_congr hs (hcol l h1 h2) fun h => hΦo e ⟨l, h⟩ h1
      · rw [downMap, dite_eq_left (show j < Γ.m - 1 by omega), downMap, dite_eq_left (show j < Γ.m - 1 by omega), hcj, hΦ0,
          ← H, one_mul, mul_reindex, map_inv, hf]
      · exact GlobalTheory.T.downwardVertexMap_lastVertex_mul_of_frame hs j hj hB' g κ hg' x (colMove j κ x) e (Φ e) hcj1
    · refine GlobalTheory.T.fourierJacobiPhase_lastInnerVertex_invariant j hB' κ x (colMove j κ x) e (Φ e) hcol hcj1 (fun i h1 => hΦo e i h1) ?_
      rw [hcj, hΦ0, ← H, one_mul]

end GlobalTheory.TopLevelInv.FlatStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorMoveArgumentsLastRowVertexStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatTensor_moveArguments_lastRow_vertex : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (hs : 1 ≤ Γ.s) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (F : Γ.Args → ℂ)
    (j : ℕ) (hj : j + 1 < Γ.m) (g : GL (Fin (Γ.rank (Γ.m, j + 1))) k) (κ : GL (Fin (topRank Γ (j + 1))) k),
    valuation k (gdet κ : k) = 1 → ∀ v ∈ symN k (Fin (topRank Γ (j + 1))) (Γ.m - 1 - (j + 1)), toFrame hs hj g = v * embX _ κ →
    ∀ (x : ColArgs Γ) (y : RowArgs Γ),
      flatTensor hs ψ ν (fun z => F (Γ.moveArgs .one (Pi.mulSingle (Γ.m, j + 1) g) z)) x y = flatTensor hs ψ ν F (colMove j κ x) y := by
  first | exact @GlobalTheory.TopLevelInv.FlatStep.flatTensor_moveArgs_mulSingle | exact GlobalTheory.TopLevelInv.FlatStep.flatTensor_moveArgs_mulSingle | (intros; apply GlobalTheory.TopLevelInv.FlatStep.flatTensor_moveArgs_mulSingle <;> assumption)
end
