module

public import Mathlib

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnfoldEquiv
open NumberField IsDedekindDomain Module MvPolynomial

noncomputable section

namespace PI.UnfoldEquiv

namespace Loc

section Groups

variable (k : Type) [CommRing k] (n c : ℕ)

def atN {k : Type} [CommRing k] {N : ℕ} (v : Fin N → k) (i : ℕ) : k := if h : i < N then v ⟨i, h⟩ else 0

def eN (N i : ℕ) : Fin N → k := fun l => if l.1 = i then 1 else 0

def supp (N : ℕ) (s : Set ℕ) : Submodule k (Fin N → k) where
  carrier := {v | ∀ l : Fin N, l.1 ∉ s → v l = 0}
  add_mem' := fun {a b} ha hb l hl => by simp [ha l hl, hb l hl]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun r a ha l hl => by simp [ha l hl]

def Ufl (i : ℕ) : Submodule k (Fin (n + c) → k) := supp k (n + c) {l | l < n + i}

def inX : (Fin n → k) →ₗ[k] (Fin (n + c) → k) :=
  LinearMap.pi fun l => if h : l.1 < n then LinearMap.proj ⟨l.1, h⟩ else 0

def R1cond (r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : Prop :=
  (∀ i, ∀ v ∈ Ufl k n c i, r v ∈ Ufl k n c i) ∧ r (eN k (n + c) n) = eN k (n + c) n ∧
    ∀ i, r (eN k (n + c) (n + i)) - eN k (n + c) (n + i) ∈ Ufl k n c i


variable {k n c}

def n1Arg (r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : k :=
  ∑ i ∈ Finset.range (c - 1), atN (r (eN k (n + c) (n + i + 1))) (n + i)

end Groups

section Data

variable {k K : Type} [CommRing k] [Field K]

variable (n' c' n c : ℕ)

def IsFree (l s : ℕ) : Prop := n' ≤ s ∧ (s - n' = c ∨ (1 ≤ s - n' ∧ (l < n ∨ l - n < s - n')))

instance (l s : ℕ) : Decidable (IsFree n' n c l s) := by unfold IsFree; infer_instance

abbrev FC : Type := {p : Fin (n + c) × Fin (n' + c') // IsFree n' n c p.1.1 p.2.1}

variable {n' c' n c}

def xx1 (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (t : FC n' c' n c → k) : (Fin (n' + c') → k) →ₗ[k] (Fin (n + c) → k) :=
  Matrix.toLin' (Matrix.of fun (l : Fin (n + c)) (s : Fin (n' + c')) =>
    if hf : IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩
    else if hs : s.1 < n' then (if hl : l.1 < n then LinearMap.toMatrix' xj ⟨l.1, hl⟩ ⟨s.1, hs⟩ else 0)
    else if l.1 = n + (s.1 - n') then 1 else 0)

def chArg (x : (Fin (n' + c') → k) →ₗ[k] (Fin (n + c) → k)) : k :=
  ∑ i ∈ Finset.range c, atN (x (eN k (n' + c') (n' + i + 1))) (n + i)

end Data

end Loc

end PI.UnfoldEquiv

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnfoldingEquivalence.Points
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnfoldingEquivalence.ExtractFreeFillMatrix
open PI.UnfoldEquiv PI.UnfoldEquiv.Loc

noncomputable section

namespace PI.UnfoldEquiv.UnitaryGroupMassFormula

variable {k : Type} [CommRing k]

theorem eN_apply (N i : ℕ) (l : Fin N) : eN k N i l = if l.1 = i then 1 else 0 := rfl

theorem mem_Ufl {n c i : ℕ} {v : Fin (n + c) → k} :
    v ∈ Ufl k n c i ↔ ∀ l : Fin (n + c), ¬ (l.1 < n + i) → v l = 0 := Iff.rfl

theorem atN_add {N : ℕ} (v w : Fin N → k) (i : ℕ) : atN (v + w) i = atN v i + atN w i := by
  simp only [atN]
  split_ifs <;> simp

theorem atN_smul {N : ℕ} (a : k) (v : Fin N → k) (i : ℕ) : atN (a • v) i = a * atN v i := by
  simp only [atN]
  split_ifs <;> simp

theorem atN_of_mem {n c i : ℕ} {v : Fin (n + c) → k} (hv : v ∈ Ufl k n c i) : atN v (n + i) = 0 := by
  unfold atN
  split_ifs with h
  · exact (mem_Ufl.1 hv) ⟨n + i, h⟩ (lt_irrefl _)
  · rfl

theorem atN_eN {N i : ℕ} (h : i < N) : atN (eN k N i) i = 1 := by
  rw [atN, dite_eq_left h, eN_apply]
  exact if_pos rfl

theorem atN_eN_ne {N i j : ℕ} (h : j ≠ i) : atN (eN k N j) i = 0 := by
  unfold atN
  split_ifs with hi
  · rw [eN_apply]
    exact if_neg fun e => h e.symm
  · rfl

def base {n' n c : ℕ} (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (l : Fin (n + c)) (s : Fin (n' + (c + 1))) : k :=
  if hs : s.1 < n' then (if hl : l.1 < n then LinearMap.toMatrix' xj ⟨l.1, hl⟩ ⟨s.1, hs⟩ else 0)
    else if l.1 = n + (s.1 - n') then 1 else 0

def Q {n' n c : ℕ} (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (x : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k)) : Prop :=
  (∀ v, x (inX k n' (c + 1) v) = inX k n c (xj v)) ∧ (0 < c → x (eN k (n' + (c + 1)) n') = eN k (n + c) n) ∧
    ∀ j, 1 ≤ j → j < c → x (eN k (n' + (c + 1)) (n' + j)) - eN k (n + c) (n + j) ∈ Ufl k n c j

def fe {n' n c : ℕ} (x : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k)) : FC n' (c + 1) n c → k :=
  fun p => x (Pi.single p.1.2 1) p.1.1

theorem fillMatrix_single {n' n c : ℕ} (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (t : FC n' (c + 1) n c → k)
    (l : Fin (n + c)) (s : Fin (n' + (c + 1))) :
    xx1 xj t (Pi.single s 1) l = if hf : IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩ else base xj l s := by
  simp only [xx1, Matrix.toLin'_apply, Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply,
    Matrix.of_apply, base]

end PI.UnfoldEquiv.UnitaryGroupMassFormula
end
end

open PI.UnfoldEquiv PI.UnfoldEquiv.Loc

noncomputable section

namespace PI.UnfoldEquiv.UnitaryGroupMassFormula

variable {k : Type} [CommRing k]

private theorem eN_val_eq_single {N : ℕ} (s : Fin N) : eN k N s.1 = Pi.single s 1 := by
  funext l
  simp only [eN, Pi.single_apply, Fin.ext_iff]

private theorem inX_apply' {n c : ℕ} (v : Fin n → k) (l : Fin (n + c)) :
    inX k n c v l = if h : l.1 < n then v ⟨l.1, h⟩ else 0 := by
  simp only [inX, LinearMap.pi_apply]
  split_ifs <;> simp

private theorem inX_single' {n c : ℕ} (s : Fin n) :
    inX k n c (Pi.single s 1) = Pi.single ⟨s.1, by have := s.2; omega⟩ 1 := by
  funext l
  rw [inX_apply']
  by_cases h : l.1 < n
  · rw [dite_eq_left h]
    simp only [Pi.single_apply, Fin.ext_iff]
  · rw [dite_eq_right h, Pi.single_apply, if_neg]
    intro e
    rw [Fin.ext_iff] at e
    have := s.2
    simp only at e
    omega

private theorem mem_Ufl_iff' {n c i : ℕ} (v : Fin (n + c) → k) :
    v ∈ Ufl k n c i ↔ ∀ l : Fin (n + c), ¬ l.1 < n + i → v l = 0 := Iff.rfl

theorem Q_iff {n' n c : ℕ} (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (x : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k)) :
    Q xj x ↔ ∀ (l : Fin (n + c)) (s : Fin (n' + (c + 1))), ¬ IsFree n' n c l.1 s.1 → x (Pi.single s 1) l = base xj l s := by
  constructor
  · rintro ⟨h1, h2, h3⟩ l s hnf
    simp only [IsFree, not_and, not_or] at hnf
    unfold base
    by_cases hs : s.1 < n'
    · rw [dite_eq_left hs]
      have e : (Pi.single s 1 : Fin (n' + (c + 1)) → k) =
          inX k n' (c + 1) (Pi.single ⟨s.1, hs⟩ 1) := by
        rw [inX_single']
      rw [e, h1, inX_apply']
      split_ifs with hl
      · rfl
      · rfl
    · rw [dite_eq_right hs]
      obtain ⟨j, hj⟩ : ∃ j, s.1 = n' + j := ⟨s.1 - n', by omega⟩
      rw [hj] at hnf
      rw [hj, Nat.add_sub_cancel_left, ← eN_val_eq_single s, hj]
      obtain ⟨hjc, hj2⟩ := hnf (by omega)
      simp only [Nat.add_sub_cancel_left] at hjc hj2
      by_cases hj0 : j = 0
      · subst hj0
        have hc : 0 < c := by omega
        have k2 := congrFun (h2 hc) l
        simpa [eN] using k2
      · have hjlt : j < c := by have := s.2; omega
        obtain ⟨hl1, hl2⟩ := hj2 (by omega)
        have hl : ¬ l.1 < n + j := by omega
        have k4 := (mem_Ufl_iff' _).1 (h3 j (by omega) hjlt) l hl
        rw [Pi.sub_apply, sub_eq_zero] at k4
        rw [k4]
        simp only [eN]
  · intro H
    have Hs : ∀ (l : Fin (n + c)) (s : ℕ) (hs : s < n' + (c + 1)), ¬ IsFree n' n c l.1 s →
        x (eN k (n' + (c + 1)) s) l = base xj l ⟨s, hs⟩ := by
      intro l s hs h
      have k5 := H l ⟨s, hs⟩ h
      rw [← eN_val_eq_single] at k5
      exact k5
    refine ⟨?_, ?_, ?_⟩
    · intro v
      have e : x ∘ₗ inX k n' (c + 1) = inX k n c ∘ₗ xj := by
        ext s' l
        simp only [LinearMap.comp_apply, LinearMap.single_apply]
        have hs' := s'.2
        rw [inX_single', ← eN_val_eq_single, Hs l s'.1 (by omega) (by simp only [IsFree]; omega),
          inX_apply']
        unfold base
        rw [dite_eq_left hs']
        split_ifs with hl
        · rfl
        · rfl
      exact LinearMap.congr_fun e v
    · intro hc
      funext l
      rw [Hs l n' (by omega) (by simp only [IsFree]; omega)]
      simp [base, eN]
    · intro j hj1 hjc
      rw [mem_Ufl_iff']
      intro l hl
      have hnl : ¬ n' + j < n' := by omega
      rw [Pi.sub_apply, Hs l (n' + j) (by omega) (by simp only [IsFree]; omega)]
      simp [base, eN, hnl]

theorem isFillOf_fillMatrix {n' n c : ℕ} (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (t : FC n' (c + 1) n c → k) : Q xj (xx1 xj t) := by
  rw [Q_iff]
  intro l s h
  rw [fillMatrix_single, dite_eq_right h]

theorem fillMatrix_extractFree {n' n c : ℕ} {xj : (Fin n' → k) →ₗ[k] (Fin n → k)} {x : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k)}
    (h : Q xj x) : xx1 xj (fe x) = x := by
  ext s l
  simp only [LinearMap.comp_apply, LinearMap.single_apply]
  rw [fillMatrix_single]
  split_ifs with hf
  · rfl
  · exact ((Q_iff xj x).1 h l s hf).symm

theorem Q_map {n' n c : ℕ} {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} {g : (Fin n → k) ≃ₗ[k] (Fin n → k)}
    (hr : R1cond k n c r) (hg : ∀ x, r (inX k n c x) = inX k n c (g x)) {xj : (Fin n' → k) →ₗ[k] (Fin n → k)}
    {x : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k)} (h : Q xj x) :
    Q (g.toLinearMap ∘ₗ xj) (r.toLinearMap ∘ₗ x) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun v => ?_, fun hc => ?_, fun j hj1 hjc => ?_⟩
  · show r (x (inX k n' (c + 1) v)) = inX k n c (g (xj v))
    rw [h1, hg]
  · show r (x (eN k (n' + (c + 1)) n')) = eN k (n + c) n
    rw [h2 hc, hr.2.1]
  · show r (x (eN k (n' + (c + 1)) (n' + j))) - eN k (n + c) (n + j) ∈ Ufl k n c j
    have e : r (x (eN k (n' + (c + 1)) (n' + j))) - eN k (n + c) (n + j) =
        r (x (eN k (n' + (c + 1)) (n' + j)) - eN k (n + c) (n + j)) +
          (r (eN k (n + c) (n + j)) - eN k (n + c) (n + j)) := by
      rw [map_sub]
      abel
    rw [e]
    exact Submodule.add_mem _ (hr.1 j _ (h3 j hj1 hjc)) (hr.2.2 j)

end PI.UnfoldEquiv.UnitaryGroupMassFormula
end
end

open PI.UnfoldEquiv PI.UnfoldEquiv.Loc

noncomputable section

namespace PI.UnfoldEquiv.UnitaryGroupMassFormula

variable {k : Type} [CommRing k]

theorem atN_map {n c i : ℕ} {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r) (hi : i < c)
    {w : Fin (n + c) → k} (hw : w ∈ Ufl k n c (i + 1)) : atN (r w) (n + i) = atN w (n + i) := by
  have hlt : n + i < n + c := by omega
  have hw' : w - PI.UnfoldEquiv.Loc.atN w (n + i) • PI.UnfoldEquiv.Loc.eN k (n + c) (n + i) ∈ PI.UnfoldEquiv.Loc.Ufl k n c i := by
    rw [mem_Ufl] at hw ⊢
    intro l hl
    rw [Pi.sub_apply, Pi.smul_apply, eN_apply, smul_eq_mul]
    by_cases hl' : l.1 = n + i
    · rw [if_pos hl', mul_one, PI.UnfoldEquiv.Loc.atN, dite_eq_left hlt]
      have hle : l = ⟨n + i, hlt⟩ := Fin.ext hl'
      rw [hle, sub_self]
    · rw [if_neg hl', mul_zero, sub_zero]
      exact hw l (by omega)
  have hre : PI.UnfoldEquiv.Loc.atN (r (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i))) (n + i) = 1 := by
    have h1 := atN_of_mem (hr.2.2 i)
    have h2 := atN_add (r (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) - PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) (n + i)
    rw [sub_add_cancel] at h2
    rw [h2, h1, atN_eN hlt, zero_add]
  have hdec : r w = r (w - PI.UnfoldEquiv.Loc.atN w (n + i) • PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) + PI.UnfoldEquiv.Loc.atN w (n + i) • r (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i)) := by
    rw [map_sub, map_smul, sub_add_cancel]
  rw [hdec, atN_add, atN_smul, atN_of_mem (hr.1 i _ hw'), hre, zero_add, mul_one]

private theorem atN_zero {N : ℕ} (i : ℕ) : PI.UnfoldEquiv.Loc.atN (0 : Fin N → k) i = 0 := by
  have h := atN_smul (0 : k) (0 : Fin N → k) i
  rwa [zero_smul, zero_mul] at h

private theorem eN_eq_zero_of_le {N i : ℕ} (h : N ≤ i) : PI.UnfoldEquiv.Loc.eN k N i = 0 := by
  funext l
  have hl := l.2
  rw [eN_apply, Pi.zero_apply, if_neg (by omega)]

theorem chArg_map {n' n c : ℕ} {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r)
    {xj : (Fin n' → k) →ₗ[k] (Fin n → k)} {x : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k)} (h : Q xj x) :
    chArg (n' := n') (c' := c + 1) (n := n) (c := c) (r.toLinearMap ∘ₗ x) = chArg x + n1Arg r := by
  have key : ∀ i ∈ Finset.range c,
      PI.UnfoldEquiv.Loc.atN (r (x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)))) (n + i) =
        PI.UnfoldEquiv.Loc.atN (x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1))) (n + i) + PI.UnfoldEquiv.Loc.atN (r (PI.UnfoldEquiv.Loc.eN k (n + c) (n + i + 1))) (n + i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hic : i + 1 < c
    · have hu : x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)) - PI.UnfoldEquiv.Loc.eN k (n + c) (n + i + 1) ∈ PI.UnfoldEquiv.Loc.Ufl k n c (i + 1) :=
        h.2.2 (i + 1) (by omega) hic
      have hcoord := atN_map hr hi hu
      have hx : x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)) =
          (x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)) - PI.UnfoldEquiv.Loc.eN k (n + c) (n + i + 1)) + PI.UnfoldEquiv.Loc.eN k (n + c) (n + i + 1) :=
        (sub_add_cancel _ _).symm
      rw [hx, map_add (f := _), atN_add, atN_add, hcoord, atN_eN_ne (by omega : n + i + 1 ≠ n + i), add_zero]
    · have hw : x (PI.UnfoldEquiv.Loc.eN k (n' + (c + 1)) (n' + i + 1)) ∈ PI.UnfoldEquiv.Loc.Ufl k n c (i + 1) := by
        rw [mem_Ufl]
        intro l hl
        exfalso
        have := l.2
        omega
      rw [atN_map hr hi hw, eN_eq_zero_of_le (by omega : n + c ≤ n + i + 1), map_zero,
        atN_zero, add_zero]
  simp only [PI.UnfoldEquiv.Loc.chArg, PI.UnfoldEquiv.Loc.n1Arg, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib]
  congr 1
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    simp
  · obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
    rw [Nat.add_sub_cancel, Finset.sum_range_succ, eN_eq_zero_of_le (by omega : n + (m + 1) ≤ n + m + 1), map_zero,
      atN_zero, add_zero]

end PI.UnfoldEquiv.UnitaryGroupMassFormula
