module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.HaarIdx

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSpanSingle
noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni)

section Span

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mem_span_single (s : Set ι) (v : ι → K) :
    v ∈ Submodule.span K ((fun j => Pi.single j (1 : K)) '' s) ↔ ∀ i, i ∉ s → v i = 0 := by
  classical
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      intro i hi
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      simp [Pi.single_apply, hij]
    | zero => intro i _; rfl
    | add x y _ _ hx hy => intro i hi; simp [hx i hi, hy i hi]
    | smul a x _ hx => intro i hi; simp [hx i hi]
  · intro h
    have hv : v = ∑ i, v i • Pi.single i (1 : K) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    by_cases hi : i ∈ s
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · simp [h i hi]

end Span

variable {K : Type} [Field K] {r k : ℕ}

def pe (b : Fin (r + 1)) : Idx r k := if h : (b : ℕ) < r then Sum.inl ⟨b, h⟩ else zI

def ColFlag (m : Matrix (Idx r k) (Idx r k) K) : Prop :=
  ∀ b : Fin (r + 1), m *ᵥ Pi.single (pe b) 1 - Pi.single (pe b) 1 ∈
    Submodule.span K ((fun a => Pi.single (pe (k := k) a) (1 : K)) '' {a | a < b})

theorem colFlag_iff' (m : Matrix (Idx r k) (Idx r k) K) :
    ColFlag m ↔ ∀ b : Fin (r + 1), ∀ i, (∀ a, a < b → i ≠ pe a) →
      m i (pe b) = if i = pe b then 1 else 0 := by
  classical
  unfold ColFlag
  refine forall_congr' fun b => ?_
  have himg : (fun a => Pi.single (pe (k := k) a) (1 : K)) '' {a | a < b} =
      (fun j => Pi.single j (1 : K)) '' (pe '' {a | a < b}) := by
    rw [Set.image_image]
  rw [himg, mem_span_single]
  refine forall_congr' fun i => ?_
  have h1 : i ∉ pe '' {a | a < b} ↔ ∀ a, a < b → i ≠ pe a := by
    simp only [Set.mem_image, Set.mem_setOf_eq, not_exists, not_and]
    exact forall_congr' fun a => imp_congr_right fun _ => ne_comm
  rw [h1]
  refine imp_congr_right fun _ => ?_
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, sub_eq_zero]

theorem pe_castSucc (i : Fin r) : pe (k := k) (Fin.castSucc i) = Sum.inl i := by
  have h : ((Fin.castSucc i : Fin (r + 1)) : ℕ) < r := i.isLt
  unfold pe
  rw [dite_eq_left h]
  rfl

theorem pe_last : pe (r := r) (k := k) (Fin.last r) = zI := by
  unfold pe
  rw [dite_eq_right (by simp)]

theorem pe_inl_of_lt {a b : Fin (r + 1)} (h : a < b) : pe (k := k) a = Sum.inl ⟨a, by omega⟩ := by
  unfold pe
  rw [dite_eq_left (by omega)]

theorem colFlag_iff (m : Matrix (Idx r k) (Idx r k) K) : ColFlag m ↔ ColC m := by
  classical
  rw [colFlag_iff']
  constructor
  · intro H
    have Hc : ∀ (j : Fin r) (i : Idx r k), (∀ a : Fin r, a < j → i ≠ Sum.inl a) →
        m i (Sum.inl j) = if i = Sum.inl j then 1 else 0 := by
      intro j i hi
      have := H (Fin.castSucc j) i (fun a ha => by
        rw [pe_inl_of_lt ha]
        exact hi _ (by rw [Fin.lt_def] at ha ⊢; simpa using ha))
      rwa [pe_castSucc] at this
    have Hz : ∀ i : Idx r k, (∀ a : Fin r, i ≠ Sum.inl a) → m i zI = if i = zI then 1 else 0 := by
      intro i hi
      have := H (Fin.last r) i (fun a ha => by
        rw [pe_inl_of_lt ha]
        exact hi _)
      rwa [pe_last] at this
    have Hinr : ∀ (j : Fin r) (x : Mid k ⊕ Fin r), m (Sum.inr x) (Sum.inl j) = 0 := by
      intro j x
      have := Hc j (Sum.inr x) (fun a _ h => Sum.inr_ne_inl h)
      simpa using this
    unfold ColC IsUpUni
    refine ⟨⟨?_, fun a => ?_⟩, ?_, ?_, fun w => ?_, ?_, fun j => ?_⟩
    · intro i j hij
      have hij' : j < i := hij
      have := Hc j (Sum.inl i) (fun a ha h => by
        cases h
        exact lt_irrefl _ (ha.trans hij'))
      simpa [b11, hij'.ne'] using this
    · have := Hc a (Sum.inl a) (fun a' ha' h => by
        cases h
        exact lt_irrefl _ ha')
      simpa [b11] using this
    · ext a b
      simp [b21, Hinr]
    · ext a b
      simp [b31, Hinr]
    · simpa [wI, zI] using Hz (wI w) (fun a h => Sum.inr_ne_inl h)
    · simpa using Hz zI (fun a h => Sum.inr_ne_inl h)
    · simpa [zI] using Hz (Sum.inr (Sum.inr j)) (fun a h => Sum.inr_ne_inl h)
  · intro hC
    unfold ColC IsUpUni at hC
    obtain ⟨⟨hup, hdiag⟩, h21, h31, hw, hzz, hf⟩ := hC
    intro b i hi
    induction b using Fin.lastCases with
    | last =>
      rw [pe_last]
      rcases i with i' | ((w | u) | j)
      · exact absurd (pe_castSucc i').symm (hi _ (Fin.castSucc_lt_last i'))
      · simpa [wI, zI] using hw w
      · cases u
        simpa [zI] using hzz
      · simpa [zI] using hf j
    | cast j =>
      rw [pe_castSucc]
      rcases i with i' | (x | j')
      · rcases lt_trichotomy i' j with h | rfl | h
        · exact absurd (pe_castSucc i').symm (hi _ (Fin.castSucc_lt_castSucc_iff.mpr h))
        · simpa [b11] using hdiag i'
        · have := hup h
          simpa [b11, h.ne'] using this
      · simpa [b21] using congrFun (congrFun h21 x) j
      · simpa [b31] using congrFun (congrFun h31 j') j

end MassDataIdxStIm
end
end

noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni)

variable {K : Type} [Field K] {r k : ℕ}

def pf (b : Fin (r + 1)) : Idx r k := if h : (b : ℕ) < r then Sum.inr (Sum.inr (Fin.rev ⟨b, h⟩)) else zI

def RowFlag (m : Matrix (Idx r k) (Idx r k) K) : Prop :=
  ∀ b : Fin (r + 1), mᵀ *ᵥ Pi.single (pf b) 1 - Pi.single (pf b) 1 ∈
    Submodule.span K ((fun a => Pi.single (pf (k := k) a) (1 : K)) '' {a | a < b})

theorem rowFlag_iff' (m : Matrix (Idx r k) (Idx r k) K) :
    RowFlag m ↔ ∀ b : Fin (r + 1), ∀ i, (∀ a, a < b → i ≠ pf a) →
      m (pf b) i = if i = pf b then 1 else 0 := by
  classical
  unfold RowFlag
  refine forall_congr' fun b => ?_
  have himg : (fun a => Pi.single (pf (k := k) a) (1 : K)) '' {a | a < b} =
      (fun j => Pi.single j (1 : K)) '' (pf '' {a | a < b}) := by
    rw [Set.image_image]
  rw [himg, mem_span_single]
  refine forall_congr' fun i => ?_
  have h1 : i ∉ pf '' {a | a < b} ↔ ∀ a, a < b → i ≠ pf a := by
    simp only [Set.mem_image, Set.mem_setOf_eq, not_exists, not_and]
    exact forall_congr' fun a => imp_congr_right fun _ => ne_comm
  rw [h1]
  refine imp_congr_right fun _ => ?_
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, sub_eq_zero, Matrix.transpose_apply]

theorem pf_castSucc (i : Fin r) : pf (k := k) (Fin.castSucc i) = Sum.inr (Sum.inr (Fin.rev i)) := by
  have h : ((Fin.castSucc i : Fin (r + 1)) : ℕ) < r := i.isLt
  unfold pf
  rw [dite_eq_left h]
  rfl

theorem pf_last : pf (r := r) (k := k) (Fin.last r) = zI := by
  unfold pf
  rw [dite_eq_right (by simp)]

theorem pf_of_lt {a b : Fin (r + 1)} (h : a < b) :
    pf (k := k) a = Sum.inr (Sum.inr (Fin.rev ⟨a, by have := b.isLt; omega⟩)) := by
  unfold pf
  rw [dite_eq_left (by omega)]

theorem rowFlag_iff (m : Matrix (Idx r k) (Idx r k) K) : RowFlag m ↔ RowC m := by
  classical
  rw [rowFlag_iff']
  constructor
  · intro H
    have Hr : ∀ (j : Fin r) (i : Idx r k), (∀ a : Fin r, a < j → i ≠ Sum.inr (Sum.inr (Fin.rev a))) →
        m (Sum.inr (Sum.inr (Fin.rev j))) i = if i = Sum.inr (Sum.inr (Fin.rev j)) then 1 else 0 := by
      intro j i hi
      have := H (Fin.castSucc j) i (fun a ha => by
        rw [pf_of_lt ha]
        exact hi _ (by rw [Fin.lt_def] at ha ⊢; simpa using ha))
      rwa [pf_castSucc] at this
    have Hz : ∀ i : Idx r k, (∀ a : Fin r, i ≠ Sum.inr (Sum.inr (Fin.rev a))) →
        m zI i = if i = zI then 1 else 0 := by
      intro i hi
      have := H (Fin.last r) i (fun a ha => by
        rw [pf_of_lt ha]
        exact hi _)
      rwa [pf_last] at this
    have Hf : ∀ (a : Fin r) (i : Idx r k), (∀ b : Fin r, i = Sum.inr (Sum.inr b) → b ≤ a) →
        m (Sum.inr (Sum.inr a)) i = if i = Sum.inr (Sum.inr a) then 1 else 0 := by
      intro a i hi
      have := Hr (Fin.rev a) i (fun c hc h => by
        have hle := hi _ h
        rw [Fin.le_def, Fin.val_rev] at hle
        rw [Fin.lt_def, Fin.val_rev] at hc
        have := a.isLt
        have := c.isLt
        omega)
      simpa only [Fin.rev_rev] using this
    unfold RowC IsUpUni
    refine ⟨⟨?_, fun a => ?_⟩, ?_, ?_, fun w => ?_, ?_, fun j => ?_⟩
    · intro a b hab
      have hab' : b < a := hab
      have := Hf a (Sum.inr (Sum.inr b)) (fun c h => by
        cases h
        exact hab'.le)
      simpa [b33, hab'.ne] using this
    · have := Hf a (Sum.inr (Sum.inr a)) (fun c h => by
        cases h
        exact le_rfl)
      simpa [b33] using this
    · ext a b
      simpa [b31] using Hf a (Sum.inl b) (fun c h => absurd h Sum.inl_ne_inr)
    · ext a x
      simpa [b32] using Hf a (Sum.inr (Sum.inl x)) (fun c h => by simp at h)
    · simpa [wI, zI] using Hz (wI w) (fun a h => by simp [wI] at h)
    · simpa using Hz zI (fun a h => by simp [zI] at h)
    · simpa [zI] using Hz (Sum.inl j) (fun a h => Sum.inl_ne_inr h)
  · intro hC
    unfold RowC IsUpUni at hC
    obtain ⟨⟨hup, hdiag⟩, h31, h32, hw, hzz, hl⟩ := hC
    intro b i hi
    induction b using Fin.lastCases with
    | last =>
      rw [pf_last]
      rcases i with c | ((w | u) | j)
      · simpa [zI] using hl c
      · simpa [wI, zI] using hw w
      · cases u
        simpa [zI] using hzz
      · exact absurd (by rw [pf_castSucc, Fin.rev_rev]) (hi _ (Fin.castSucc_lt_last (Fin.rev j)))
    | cast j =>
      rw [pf_castSucc]
      rcases i with c | (x | j')
      · simpa [b31] using congrFun (congrFun h31 (Fin.rev j)) c
      · simpa [b32] using congrFun (congrFun h32 (Fin.rev j)) x
      · rcases lt_trichotomy j' (Fin.rev j) with h | h | h
        · have h0 : m (Sum.inr (Sum.inr (Fin.rev j))) (Sum.inr (Sum.inr j')) = 0 := hup h
          rw [h0, if_neg]
          simp [h.ne]
        · subst h
          simpa [b33] using hdiag (Fin.rev j)
        · have hlt : Fin.castSucc (Fin.rev j') < Fin.castSucc j := by
            rw [Fin.castSucc_lt_castSucc_iff, Fin.lt_def, Fin.val_rev]
            rw [Fin.lt_def, Fin.val_rev] at h
            have := j.isLt
            have := j'.isLt
            omega
          exact absurd (by rw [pf_castSucc, Fin.rev_rev]) (hi _ hlt)

end MassDataIdxStIm
