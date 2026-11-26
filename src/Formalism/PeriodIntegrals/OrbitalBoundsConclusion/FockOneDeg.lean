module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.ExistsMonomialWeight
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CharIdem

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.RedDefs
noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FockOneDegW

def KHc : Prop := ∀ p q r s : ℕ, ∀ a b : Ix p q, sameBlock a b → ∀ (e : ℕ) (P : Pol p q r s),
  homogeneousComponent e (fockAct1 p q r s (Eab a b) P) =
    fockAct1 p q r s (Eab a b) (homogeneousComponent e P)

def KHarm : Prop := ∀ p q r s : ℕ, ∀ a b : Ix p q, sameBlock a b → ∀ P : Pol p q r s,
  Harm2 P → Harm2 (fockAct1 p q r s (Eab a b) P)

def HcHarm : Prop := ∀ p q r s : ℕ, ∀ (e : ℕ) (P : Pol p q r s),
  Harm2 P → Harm2 (homogeneousComponent e P)

def HarmSub : Prop := ∀ p q r s : ℕ,
  Harm2 (0 : Pol p q r s) ∧ (∀ P Q : Pol p q r s, Harm2 P → Harm2 Q → Harm2 (P + Q)) ∧
    (∀ (c : ℂ) (P : Pol p q r s), Harm2 P → Harm2 (c • P))

def KAdj : Prop := ∀ p q r s : ℕ, ∀ a b : Ix p q, sameBlock a b → ∀ P Q : Pol p q r s,
  fockInner P (fockAct1 p q r s (Eab a b) Q) = fockInner (fockAct1 p q r s (Eab b a) P) Q

def HwExist : Prop := ∀ p q r s : ℕ, ∀ U : Submodule ℂ (Pol p q r s), FiniteDimensional ℂ U → U ≠ ⊥ →
  (∀ a b : Ix p q, sameBlock a b → ∀ u ∈ U, fockAct1 p q r s (Eab a b) u ∈ U) →
    ∃ (ν : Ix p q → ℚ) (v : Pol p q r s), v ∈ U ∧ IsHW (fockAct1 p q r s) ν v

end PI.FockOneDegW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.RedOps
noncomputable section

open Matrix FockH1Action MvPolynomial FockRaiseLowInner

namespace PI.FockOneDegW.RedOps

open PI.FockOneDegW

variable {p q r s : ℕ}

theorem lowOp_apply (c d : Ix r s) (P : Pol p q r s) :
    lowOp (p := p) (q := q) c d P = ∑ a : Ix p q, (if linePos ((a, d) : Ln p q r s) = true then
      pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) P) else 0) := by
  unfold lowOp
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> rfl

theorem hc_lowOp (c d : Ix r s) (e : ℕ) (P : Pol p q r s) :
    homogeneousComponent e (lowOp (p := p) (q := q) c d P) =
      lowOp (p := p) (q := q) c d (homogeneousComponent (e + 2) P) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [lowOp_apply, lowOp_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rw [FockRL.hc_pderiv, FockRL.hc_pderiv]
  · exact map_zero _

theorem hc_comm_of_homog {σ : Type} (T : Module.End ℂ (MvPolynomial σ ℂ))
    (hT : ∀ (d : ℕ) (P : MvPolynomial σ ℂ), P ∈ homog σ d → T P ∈ homog σ d) (e : ℕ)
    (P : MvPolynomial σ ℂ) :
    homogeneousComponent e (T P) = T (homogeneousComponent e P) := by
  have key : ∀ d, homogeneousComponent e (T (homogeneousComponent d P)) =
      if e = d then T (homogeneousComponent d P) else 0 := fun d =>
    homogeneousComponent_of_mem (hT d _ ((mem_homogeneousSubmodule _ _).2 (homogeneousComponent_isHomogeneous d P)))
  conv_lhs => rw [← sum_homogeneousComponent P]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  simp only [key]
  rw [Finset.sum_ite_eq]
  split_ifs with he
  · rfl
  · simp only [Finset.mem_range, not_lt] at he
    rw [homogeneousComponent_eq_zero _ _ (by omega), map_zero]

theorem inner_posOp (a b : Ix p q) (hab : sameBlock a b) (P Q : Pol p q r s) :
    fockInner P (posOp a b Q) = fockInner (posOp b a P) Q := by
  rw [posOp_apply, posOp_apply, fockInner_sum_right, fockInner_sum_left]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hl : linePos ((b, c) : Ln p q r s) = linePos ((a, c) : Ln p q r s) :=
    (FockRL.linePos_left b a c).2 (FockRL.sameBlock_symm hab)
  rw [hl]
  split_ifs
  · rw [fockInner_mul_X, fockInner_X_mul]
  · rw [fockInner_zero_right, fockInner_zero_left]

theorem inner_negOp (a b : Ix p q) (hab : sameBlock a b) (P Q : Pol p q r s) :
    fockInner P (negOp a b Q) = fockInner (negOp b a P) Q := by
  rw [negOp_apply, negOp_apply, fockInner_sum_right, fockInner_sum_left]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hl : linePos ((b, c) : Ln p q r s) = linePos ((a, c) : Ln p q r s) :=
    (FockRL.linePos_left b a c).2 (FockRL.sameBlock_symm hab)
  rw [hl]
  split_ifs
  · rw [fockInner_zero_right, fockInner_zero_left]
  · rw [fockInner_mul_X, fockInner_X_mul]

theorem dd_X_mul (m m' l : Ln p q r s) (Q : Pol p q r s) :
    pderiv m (pderiv m' (X l * Q)) = X l * pderiv m (pderiv m' Q) +
      (if m' = l then pderiv m Q else 0) + (if m = l then pderiv m' Q else 0) := by
  classical
  by_cases h1 : m' = l <;> by_cases h2 : m = l <;>
    simp [h1, h2, Derivation.leibniz, pderiv_X, Pi.single_apply, eq_comm] <;> ring

end PI.FockOneDegW.RedOps

namespace PI.FockOneDegW

open PI.FockOneDegW.RedOps

theorem harmonic_submodule : HarmSub := by
  intro p q r s
  refine ⟨?_, ?_, ?_⟩
  · rw [harmIff]; intro c d _; exact map_zero _
  · intro P Q hP hQ
    rw [harmIff] at hP hQ ⊢
    intro c d hcd
    rw [map_add (f := _), hP c d hcd, hQ c d hcd, add_zero]
  · intro k P hP
    rw [harmIff] at hP ⊢
    intro c d hcd
    rw [map_smul, hP c d hcd, smul_zero]

theorem highest_weight_harmonic : HcHarm := by
  intro p q r s e P hP
  rw [harmIff] at hP ⊢
  intro c d hcd
  apply FockRaiseLowGrade.eq_zero_of_hc
  intro e'
  rw [hc_lowOp, FockRaiseLowGrade.hc_hc]
  split_ifs with h
  · subst h
    rw [← hc_lowOp, hP c d hcd, map_zero]
  · exact map_zero _

theorem kernel_highest_weight : KHc := by
  intro p q r s a b hab e P
  refine hc_comm_of_homog _ (fun d P hP => ?_) e P
  have hKC : IsKC (Eab a b) := by
    intro x y hxy
    simp only [Eab, Matrix.single_apply]
    split_ifs with h'
    · obtain ⟨rfl, rfl⟩ := h'
      exact absurd hab hxy
    · rfl
  exact (gradedOscillatorProperty p q r s).1 (Eab a b) hKC d P hP

theorem fock_kernel_adjoint : KAdj := by
  intro p q r s a b hab P Q
  have hba : sameBlock b a := FockRL.sameBlock_symm hab
  rw [fock_operators_kernel p q r s a b hab, fock_operators_kernel p q r s b a hba]
  simp only [sub_eq_add_neg, LinearMap.add_apply, LinearMap.neg_apply, fockInner_add_right,
    fockInner_add_left, fockInner_neg_right, fockInner_neg_left, inner_posOp a b hab,
    inner_negOp b a hba]
  by_cases h : a = b
  · subst h
    simp [fockInner_smul_right, fockInner_smul_left]
  · simp [h, Ne.symm h, fockInner_zero_right, fockInner_zero_left]

end PI.FockOneDegW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.KernelHarmonic
noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FockOneDegW.RedOps

open PI.FockOneDegW

variable {p q r s : ℕ}

theorem lowOp_Xd (c d : Ix r s) (l l' : Ln p q r s) (P : Pol p q r s) :
    lowOp (p := p) (q := q) c d (X l * pderiv l' P) =
      X l * pderiv l' (lowOp (p := p) (q := q) c d P) +
      ∑ a : Ix p q, (if linePos ((a, d) : Ln p q r s) = true then
        ((if ((a, d) : Ln p q r s) = l then pderiv ((a, c) : Ln p q r s) (pderiv l' P) else 0) +
         (if ((a, c) : Ln p q r s) = l then pderiv ((a, d) : Ln p q r s) (pderiv l' P) else 0))
        else 0) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [lowOp_apply, lowOp_apply, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : linePos ((a, d) : Ln p q r s) = true
  · simp only [h, ↓reduceIte]
    have hc : pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) (pderiv l' P)) =
        pderiv l' (pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) P)) := by
      rw [PI.FockOneDegW.Core.pd_comm ((a, d) : Ln p q r s) l' P,
        PI.FockOneDegW.Core.pd_comm ((a, c) : Ln p q r s) l' (pderiv ((a, d) : Ln p q r s) P)]
    rw [dd_X_mul, hc]
    abel
  · simp [h]

theorem sum_rows (c d e : Ix r s) (a : Ix p q) (F G : Ix p q → Pol p q r s) :
    ∑ a' : Ix p q, (if linePos ((a', d) : Ln p q r s) = true then
      ((if ((a', d) : Ln p q r s) = (a, e) then F a' else 0) +
       (if ((a', c) : Ln p q r s) = (a, e) then G a' else 0)) else 0) =
    if linePos ((a, d) : Ln p q r s) = true then
      ((if d = e then F a else 0) + (if c = e then G a else 0)) else 0 := by
  rw [Finset.sum_eq_single a]
  · simp [Prod.mk.injEq]
  · intro b _ hb
    simp [Prod.mk.injEq, hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem not_both (c d : Ix r s) (hcd : ¬ sameBlock c d) (a : Ix p q)
    (h1 : linePos ((a, c) : Ln p q r s) = true) (h2 : linePos ((a, d) : Ln p q r s) = true) :
    False :=
  hcd ((FockRL.linePos_right a c d).1 (h1.trans h2.symm))

theorem lowOp_posOp (c d : Ix r s) (hcd : ¬ sameBlock c d) (a b : Ix p q) (P : Pol p q r s) :
    lowOp (p := p) (q := q) c d (posOp a b P) =
      posOp a b (lowOp (p := p) (q := q) c d P) +
      (if linePos ((a, d) : Ln p q r s) = true then
        pderiv ((a, c) : Ln p q r s) (pderiv ((b, d) : Ln p q r s) P) else 0) := by
  have hcd' : c ≠ d := by
    rintro rfl; exact hcd (by rcases c with c | c <;> simp [sameBlock])
  set_option synthInstance.maxHeartbeats 100000 in
    rw [posOp_apply, posOp_apply, map_sum]
  have hterm : ∀ e : Ix r s,
      lowOp (p := p) (q := q) c d (if linePos ((a, e) : Ln p q r s) = true then
        X ((a, e) : Ln p q r s) * pderiv ((b, e) : Ln p q r s) P else 0) =
      (if linePos ((a, e) : Ln p q r s) = true then
        X ((a, e) : Ln p q r s) * pderiv ((b, e) : Ln p q r s) (lowOp (p := p) (q := q) c d P) else 0) +
      (if linePos ((a, e) : Ln p q r s) = true then
        (if linePos ((a, d) : Ln p q r s) = true then
          ((if d = e then pderiv ((a, c) : Ln p q r s) (pderiv ((b, e) : Ln p q r s) P) else 0) +
           (if c = e then pderiv ((a, d) : Ln p q r s) (pderiv ((b, e) : Ln p q r s) P) else 0))
          else 0) else 0) := by
    intro e
    by_cases h : linePos ((a, e) : Ln p q r s) = true
    · simp only [h, ↓reduceIte]
      rw [lowOp_Xd, sum_rows c d e a (fun a' => pderiv ((a', c) : Ln p q r s) (pderiv ((b, e) : Ln p q r s) P))
        (fun a' => pderiv ((a', d) : Ln p q r s) (pderiv ((b, e) : Ln p q r s) P))]
    · simp [h]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single d]
  · by_cases h : linePos ((a, d) : Ln p q r s) = true
    · simp [h, hcd']
    · simp [h]
  · intro e _ hed
    by_cases h1 : linePos ((a, e) : Ln p q r s) = true
    · by_cases h2 : linePos ((a, d) : Ln p q r s) = true
      · have hce : c ≠ e := by
          rintro rfl; exact not_both c d hcd a h1 h2
        simp [h1, h2, Ne.symm hed, hce]
      · simp [h1, h2]
    · simp [h1]
  · simp

theorem lowOp_negOp (c d : Ix r s) (hcd : ¬ sameBlock c d) (a b : Ix p q) (hab : sameBlock a b)
    (P : Pol p q r s) :
    lowOp (p := p) (q := q) c d (negOp b a P) =
      negOp b a (lowOp (p := p) (q := q) c d P) +
      (if linePos ((a, d) : Ln p q r s) = true then
        pderiv ((a, c) : Ln p q r s) (pderiv ((b, d) : Ln p q r s) P) else 0) := by
  have hcd' : c ≠ d := by
    rintro rfl; exact hcd (by rcases c with c | c <;> simp [sameBlock])
  have hba : linePos ((b, d) : Ln p q r s) = linePos ((a, d) : Ln p q r s) :=
    (FockRL.linePos_left b a d).2 (FockRL.sameBlock_symm hab)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [negOp_apply, negOp_apply, map_sum]
  have hterm : ∀ e : Ix r s,
      lowOp (p := p) (q := q) c d (if linePos ((b, e) : Ln p q r s) = true then 0 else
        X ((b, e) : Ln p q r s) * pderiv ((a, e) : Ln p q r s) P) =
      (if linePos ((b, e) : Ln p q r s) = true then 0 else
        X ((b, e) : Ln p q r s) * pderiv ((a, e) : Ln p q r s) (lowOp (p := p) (q := q) c d P)) +
      (if linePos ((b, e) : Ln p q r s) = true then 0 else
        (if linePos ((b, d) : Ln p q r s) = true then
          ((if d = e then pderiv ((b, c) : Ln p q r s) (pderiv ((a, e) : Ln p q r s) P) else 0) +
           (if c = e then pderiv ((b, d) : Ln p q r s) (pderiv ((a, e) : Ln p q r s) P) else 0))
          else 0)) := by
    intro e
    by_cases h : linePos ((b, e) : Ln p q r s) = true
    · simp [h]
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      rw [lowOp_Xd, sum_rows c d e b (fun a' => pderiv ((a', c) : Ln p q r s) (pderiv ((a, e) : Ln p q r s) P))
        (fun a' => pderiv ((a', d) : Ln p q r s) (pderiv ((a, e) : Ln p q r s) P))]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single c]
  · by_cases h : linePos ((b, d) : Ln p q r s) = true
    · have hbc : linePos ((b, c) : Ln p q r s) = false := by
        cases h' : linePos ((b, c) : Ln p q r s)
        · rfl
        · exact (not_both c d hcd b h' h).elim
      rw [← hba]
      simp [h, hbc, Ne.symm hcd', PI.FockOneDegW.Core.pd_comm ((b, d) : Ln p q r s) ((a, c) : Ln p q r s) P]
    · rw [← hba]
      simp [h]
  · intro e _ hec
    by_cases h1 : linePos ((b, e) : Ln p q r s) = true
    · simp [h1]
    · by_cases h2 : linePos ((b, d) : Ln p q r s) = true
      · have hde : d ≠ e := by
          rintro rfl; exact h1 h2
        simp [h1, h2, hde, Ne.symm hec]
      · simp [h1, h2]
  · simp

end PI.FockOneDegW.RedOps

namespace PI.FockOneDegW

open PI.FockOneDegW.RedOps

theorem kernel_harmonic : KHarm := by
  intro p q r s a b hab P hP
  rw [harmIff] at hP ⊢
  intro c d hcd
  rw [fock_operators_kernel p q r s a b hab]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, map_add (f := _), map_sub, lowOp_posOp c d hcd,
    lowOp_negOp c d hcd a b hab, hP c d hcd, map_zero, zero_add, sub_self]
  split_ifs <;> simp [hP c d hcd]

end PI.FockOneDegW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.HighestWeightExists
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.CoeffXMulPderivSelf
noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FockOneDegW.HwC

def sgnL {p q r s : ℕ} (l : Ln p q r s) : ℚ := if linePos l = true then 1 else -1

def wtv {p q r s : ℕ} (β : Ln p q r s →₀ ℕ) (c : Ix p q) : ℚ :=
  ∑ d : Ix r s, sgnL ((c, d) : Ln p q r s) * (β (c, d) : ℚ) + kShift r s c

theorem coeff_X_mul_pderiv_self {σ : Type*} (l : σ) (P : MvPolynomial σ ℂ) (β : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (X l * pderiv l P) β = (β l : ℂ) * AddMonoidAlgebra.coeff P β := by
  classical
  rw [coeff_X_mul']
  by_cases h : l ∈ β.support
  · rw [if_pos h, coeff_pderiv]
    have h1 : 1 ≤ β l := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp h)
    have hle : Finsupp.single l 1 ≤ β := Finsupp.single_le_iff.mpr h1
    rw [tsub_add_cancel_of_le hle, Finsupp.tsub_apply, Finsupp.single_eq_same, mul_comm]
    congr 1
    rw [Nat.cast_sub h1]
    push_cast
    ring
  · rw [if_neg h]
    have h0 : β l = 0 := by simpa [Finsupp.mem_support_iff] using h
    simp [h0]

theorem coeff_X_mul_pderiv_ne {σ : Type*} (l l' : σ) (P : MvPolynomial σ ℂ) (γ : σ →₀ ℕ)
    (h : AddMonoidAlgebra.coeff (X l * pderiv l' P) γ ≠ 0) :
    ∃ β ∈ P.support, β + Finsupp.single l 1 = γ + Finsupp.single l' 1 := by
  classical
  rw [coeff_X_mul'] at h
  by_cases hs : l ∈ γ.support
  · rw [if_pos hs, coeff_pderiv] at h
    refine ⟨γ - Finsupp.single l 1 + Finsupp.single l' 1, ?_, ?_⟩
    · rw [mem_support_iff]
      exact left_ne_zero_of_mul h
    · have hle : Finsupp.single l 1 ≤ γ :=
        Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs))
      rw [add_right_comm, tsub_add_cancel_of_le hle]
  · rw [if_neg hs] at h
    exact absurd rfl h

theorem wtv_add {p q r s : ℕ} (β γ : Ln p q r s →₀ ℕ) (c : Ix p q) :
    wtv (β + γ) c = wtv β c + wtv γ c - kShift r s c := by
  unfold wtv
  simp only [Finsupp.coe_add, Pi.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib]
  ring

theorem wtv_single {p q r s : ℕ} (l : Ln p q r s) (c : Ix p q) :
    wtv (Finsupp.single l 1) c = (if l.1 = c then sgnL l else 0) + kShift r s c := by
  unfold wtv
  congr 1
  have key : ∀ d : Ix r s, sgnL ((c, d) : Ln p q r s) * ((Finsupp.single l 1 ((c, d) : Ln p q r s) : ℕ) : ℚ) =
      if d = l.2 ∧ l.1 = c then sgnL l else 0 := by
    intro d
    by_cases h1 : d = l.2 ∧ l.1 = c
    · obtain ⟨rfl, rfl⟩ := h1
      simp
    · rw [if_neg h1]
      have hne : l ≠ ((c, d) : Ln p q r s) := fun he => h1 ⟨by rw [he], by rw [he]⟩
      simp [Finsupp.single_apply, hne]
  simp_rw [key]
  by_cases h : l.1 = c <;> simp [h]

theorem wtv_shift {p q r s : ℕ} (l l' : Ln p q r s) (β γ : Ln p q r s →₀ ℕ)
    (h : β + Finsupp.single l 1 = γ + Finsupp.single l' 1) (c : Ix p q) :
    wtv γ c = wtv β c + (if l.1 = c then sgnL l else 0) - (if l'.1 = c then sgnL l' else 0) := by
  have h1 := wtv_add β (Finsupp.single l 1) c
  have h2 := wtv_add γ (Finsupp.single l' 1) c
  rw [h] at h1
  rw [h2, wtv_single, wtv_single] at h1
  linarith

theorem sameBlock_refl' {p q : ℕ} (c : Ix p q) : sameBlock c c := by
  cases c <;> trivial

theorem coeff_Ecc {p q r s : ℕ} (c : Ix p q) (P : Pol p q r s) (β : Ln p q r s →₀ ℕ) :
    AddMonoidAlgebra.coeff (fockAct1 p q r s (Eab c c) P) β = ((wtv β c : ℚ) : ℂ) * AddMonoidAlgebra.coeff P β := by
  classical
  have hline : ∀ l : Ln p q r s, AddMonoidAlgebra.coeff (omE l l P) β =
      (((sgnL l * β l + sgnL l / 2 : ℚ)) : ℂ) * AddMonoidAlgebra.coeff P β := by
    intro l
    by_cases hl : linePos l = true
    · simp only [omE, raiB, lowB, hl, if_true, LinearMap.add_apply, Module.End.mul_apply,
        LinearMap.mulLeft_apply, Derivation.coeFn_coe, LinearMap.smul_apply,
        Module.End.one_apply, MvPolynomial.coeff_add, coeff_smul, smul_eq_mul, coeff_X_mul_pderiv_self, sgnL]
      push_cast
      ring
    · have hl' : linePos l = false := by simpa using hl
      have e : AddMonoidAlgebra.coeff (pderiv l (X l * P)) β = ((β l : ℂ) + 1) * AddMonoidAlgebra.coeff P β := by
        rw [coeff_pderiv, add_comm β, coeff_X_mul, mul_comm]
      simp only [omE, raiB, lowB, hl', Bool.false_eq_true, if_false, if_true, LinearMap.add_apply,
        Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.neg_apply, Derivation.coeFn_coe,
        LinearMap.smul_apply, Module.End.one_apply, MvPolynomial.coeff_add, coeff_neg, coeff_smul, smul_eq_mul, e, sgnL]
      push_cast
      ring
  rw [fockAct1_Eab_apply, coeff_sum]
  simp_rw [hline]
  rw [← Finset.sum_mul]
  congr 1
  unfold wtv
  push_cast
  rw [Finset.sum_add_distrib]
  congr 1
  cases c with
  | inl i => simp [kShift, cPair, sgnL, linePos, Fintype.sum_sum_type]; ring
  | inr i => simp [kShift, cPair, sgnL, linePos, Fintype.sum_sum_type]; ring

theorem wt_Eab {p q r s : ℕ} (a b : Ix p q) (hab : sameBlock a b) (hne : a ≠ b)
    (P : Pol p q r s) (γ : Ln p q r s →₀ ℕ) (hγ : γ ∈ (fockAct1 p q r s (Eab a b) P).support) :
    ∃ β ∈ P.support, ∀ c, wtv γ c =
      wtv β c + (if a = c then 1 else 0) - (if b = c then 1 else 0) := by
  classical
  rw [fockAct1_Eab_apply, mem_support_iff, coeff_sum] at hγ
  obtain ⟨d, -, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero hγ
  have hne' : ((a, d) : Ln p q r s) ≠ (b, d) := fun h => hne (Prod.ext_iff.mp h).1
  have hpos : linePos ((a, d) : Ln p q r s) = linePos ((b, d) : Ln p q r s) := by
    cases a <;> cases b <;> cases d <;> simp_all [sameBlock, linePos]
  simp only [omE, if_neg hne', add_zero, Module.End.mul_apply] at hd
  by_cases hl : linePos ((a, d) : Ln p q r s) = true
  · have hl2 : linePos ((b, d) : Ln p q r s) = true := hpos ▸ hl
    simp only [raiB, lowB, hl, hl2, if_true, LinearMap.mulLeft_apply,
      Derivation.coeFn_coe] at hd
    obtain ⟨β, hβ, hsum⟩ := coeff_X_mul_pderiv_ne _ _ P γ hd
    refine ⟨β, hβ, fun c => ?_⟩
    rw [wtv_shift _ _ β γ hsum c]
    simp [sgnL, hl, hl2]
  · have hl1 : linePos ((a, d) : Ln p q r s) = false := by simpa using hl
    have hl2 : linePos ((b, d) : Ln p q r s) = false := hpos ▸ hl1
    have e : pderiv ((a, d) : Ln p q r s) (X ((b, d) : Ln p q r s) * P) =
        X ((b, d) : Ln p q r s) * pderiv ((a, d) : Ln p q r s) P := by
      rw [Derivation.leibniz, pderiv_X, Pi.single_apply, if_neg hne'.symm]
      simp [mul_comm]
    simp only [raiB, lowB, hl1, hl2, Bool.false_eq_true, if_false, LinearMap.mulLeft_apply,
      LinearMap.neg_apply, Derivation.coeFn_coe, e, coeff_neg, ne_eq, neg_eq_zero] at hd
    obtain ⟨β, hβ, hsum⟩ := coeff_X_mul_pderiv_ne _ _ P γ hd
    refine ⟨β, hβ, fun c => ?_⟩
    rw [wtv_shift _ _ β γ hsum c]
    simp [sgnL, hl1, hl2]
    split_ifs <;> ring

def IsWt {p q r s : ℕ} (ν : Ix p q → ℚ) (P : Pol p q r s) : Prop :=
  ∀ β ∈ P.support, ∀ c, wtv β c = ν c

theorem Ecc_of_wt {p q r s : ℕ} {ν : Ix p q → ℚ} {P : Pol p q r s} (hP : IsWt ν P) (c : Ix p q) :
    fockAct1 p q r s (Eab c c) P = ((ν c : ℚ) : ℂ) • P := by
  ext β
  rw [coeff_Ecc, coeff_smul, smul_eq_mul]
  by_cases hβ : β ∈ P.support
  · rw [hP β hβ c]
  · have h0 : AddMonoidAlgebra.coeff P β = 0 := by simpa [mem_support_iff] using hβ
    rw [h0, mul_zero, mul_zero]

theorem wt_Eab_of {p q r s : ℕ} {ν : Ix p q → ℚ} {P : Pol p q r s} (hP : IsWt ν P)
    (a b : Ix p q) (hab : sameBlock a b) (hne : a ≠ b) :
    IsWt (fun c => ν c + (if a = c then 1 else 0) - (if b = c then 1 else 0))
      (fockAct1 p q r s (Eab a b) P) := by
  intro γ hγ c
  obtain ⟨β, hβ, h⟩ := wt_Eab a b hab hne P γ hγ
  rw [h c, hP β hβ c]

end PI.FockOneDegW.HwC
end
end

noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FockOneDegW.HwC


open Classical in
theorem exists_wtvec {p q r s : ℕ} (U : Submodule ℂ (Pol p q r s))
    (hU : ∀ c : Ix p q, ∀ u ∈ U, fockAct1 p q r s (Eab c c) u ∈ U) :
    ∀ (n : ℕ) (u : Pol p q r s), u ∈ U → u ≠ 0 → (u.support.image wtv).card ≤ n →
      ∃ (ν : Ix p q → ℚ) (v : Pol p q r s), v ∈ U ∧ v ≠ 0 ∧ IsWt ν v ∧ v.support ⊆ u.support := by
  intro n
  induction n with
  | zero =>
    intro u _ hu0 hcard
    exfalso
    apply hu0
    have h0 := Nat.le_zero.1 hcard
    rw [Finset.card_eq_zero, Finset.image_eq_empty] at h0
    exact MvPolynomial.support_eq_empty.1 h0
  | succ n ih =>
    intro u hu hu0 hcard
    by_cases hall : ∀ β₁ ∈ u.support, ∀ β₂ ∈ u.support, wtv β₁ = wtv β₂
    · obtain ⟨β₀, hβ₀⟩ := Finset.nonempty_iff_ne_empty.2 (fun h => hu0 (MvPolynomial.support_eq_empty.1 h))
      exact ⟨wtv β₀, u, hu, hu0, fun β hβ c => by rw [hall β hβ β₀ hβ₀], subset_rfl⟩
    · push_neg at hall
      obtain ⟨β₁, h₁, β₂, h₂, hne⟩ := hall
      obtain ⟨c, hc⟩ := Function.ne_iff.1 hne

      have hcoeff : ∀ β, AddMonoidAlgebra.coeff (fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u) β =
          (((wtv β c : ℚ) : ℂ) - ((wtv β₁ c : ℚ) : ℂ)) * AddMonoidAlgebra.coeff u β := by
        intro β
        rw [coeff_sub, coeff_Ecc, coeff_smul, smul_eq_mul]
        ring
      have hsub : (fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u).support ⊆ u.support := by
        intro β hβ
        rw [MvPolynomial.mem_support_iff] at hβ ⊢
        intro h0
        apply hβ
        rw [hcoeff, h0, mul_zero]
      have hmem : fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u ∈ U :=
        U.sub_mem (hU c u hu) (U.smul_mem _ hu)
      have hβ₂ : β₂ ∈ (fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u).support := by
        rw [MvPolynomial.mem_support_iff, hcoeff]
        refine mul_ne_zero ?_ (MvPolynomial.mem_support_iff.1 h₂)
        rw [sub_ne_zero]
        exact_mod_cast (Ne.symm hc)
      have hne0 : fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u ≠ 0 := by
        intro h
        rw [h, MvPolynomial.support_zero] at hβ₂
        simp at hβ₂
      have himg : (fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u).support.image wtv ⊆
          (u.support.image wtv).erase (wtv β₁) := by
        intro w hw
        obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hw
        refine Finset.mem_erase.2 ⟨fun heq => ?_, Finset.mem_image_of_mem _ (hsub hβ)⟩
        have h0 : AddMonoidAlgebra.coeff (fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u) β = 0 := by
          rw [hcoeff, heq, sub_self, zero_mul]
        exact (MvPolynomial.mem_support_iff.1 hβ) h0
      have hcard' : ((fockAct1 p q r s (Eab c c) u - ((wtv β₁ c : ℚ) : ℂ) • u).support.image wtv).card ≤ n := by
        have h1 := Finset.card_le_card himg
        have h2 := Finset.card_erase_of_mem (Finset.mem_image_of_mem wtv h₁)
        omega
      obtain ⟨ν, v, hv, hv0, hvw, hvs⟩ := ih _ hmem hne0 hcard'
      exact ⟨ν, v, hv, hv0, hvw, hvs.trans hsub⟩

theorem exists_cover {p q r s : ℕ} (U : Submodule ℂ (Pol p q r s)) [FiniteDimensional ℂ U] :
    ∃ S : Finset (Ln p q r s →₀ ℕ), ∀ u ∈ U, u.support ⊆ S := by
  classical
  let bs := Module.finBasis ℂ U
  refine ⟨Finset.univ.biUnion fun k => ((bs k : U) : Pol p q r s).support, fun u hu => ?_⟩
  have e : (⟨u, hu⟩ : U) = ∑ k, (bs.repr ⟨u, hu⟩ k) • bs k := (bs.sum_repr _).symm
  have e' : u = ∑ k, (bs.repr ⟨u, hu⟩ k) • ((bs k : U) : Pol p q r s) := by
    have h := congrArg Subtype.val e
    rw [Submodule.coe_sum] at h
    simp only [Submodule.coe_smul] at h
    exact h
  rw [e']
  exact MvPolynomial.support_sum.trans (Finset.biUnion_mono fun k _ => MvPolynomial.support_smul)

def tw {p q : ℕ} : Ix p q → ℚ
  | .inl i => -((i : ℕ) : ℚ)
  | .inr j => -((j : ℕ) : ℚ)

def fw {p q : ℕ} (ν : Ix p q → ℚ) : ℚ := ∑ c, tw c * ν c

theorem fw_shift {p q : ℕ} (ν : Ix p q → ℚ) (a b : Ix p q) :
    fw (fun c => ν c + (if a = c then 1 else 0) - (if b = c then 1 else 0)) =
      fw ν + tw a - tw b := by
  unfold fw
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem posC_facts {p q : ℕ} {a b : Ix p q} (h : posC a b) :
    sameBlock a b ∧ a ≠ b ∧ tw b < tw a := by
  rcases a with i | i <;> rcases b with j | j <;> simp only [posC] at h
  · refine ⟨trivial, fun e => (ne_of_lt h) (Sum.inl.inj e), ?_⟩
    have h' : (i : ℕ) < j := h
    show -((j : ℕ) : ℚ) < -((i : ℕ) : ℚ)
    exact neg_lt_neg (by exact_mod_cast h')
  · refine ⟨trivial, fun e => (ne_of_lt h) (Sum.inr.inj e), ?_⟩
    have h' : (i : ℕ) < j := h
    show -((j : ℕ) : ℚ) < -((i : ℕ) : ℚ)
    exact neg_lt_neg (by exact_mod_cast h')

end PI.FockOneDegW.HwC

namespace PI.FockOneDegW

open HwC

open Classical in
theorem hwExist : HwExist := by
  intro p q r s U hfd hU0 hstab
  haveI := hfd
  obtain ⟨S, hS⟩ := exists_cover U
  have hdiag : ∀ c : Ix p q, ∀ u ∈ U, fockAct1 p q r s (Eab c c) u ∈ U :=
    fun c => hstab c c (by cases c <;> trivial)

  have hwtS : ∀ (ν : Ix p q → ℚ) (v : Pol p q r s), v ∈ U → v ≠ 0 → IsWt ν v → ν ∈ S.image wtv := by
    intro ν v hv hv0 hw
    obtain ⟨β, hβ⟩ := Finset.nonempty_iff_ne_empty.2 (fun h => hv0 (MvPolynomial.support_eq_empty.1 h))
    exact Finset.mem_image.2 ⟨β, hS v hv hβ, funext fun c => hw β hβ c⟩
  have hT : ((S.image wtv).filter (fun ν => ∃ v ∈ U, v ≠ 0 ∧ IsWt ν v)).Nonempty := by
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    obtain ⟨ν, v, hv, hv0, hvw, -⟩ := exists_wtvec U hdiag _ u hu hu0 le_rfl
    exact ⟨ν, Finset.mem_filter.2 ⟨hwtS ν v hv hv0 hvw, v, hv, hv0, hvw⟩⟩

  obtain ⟨ν₀, hν₀, hmax⟩ := Finset.exists_max_image _ fw hT
  obtain ⟨-, v, hv, hv0, hvw⟩ := Finset.mem_filter.1 hν₀
  refine ⟨ν₀, v, hv, ?_⟩
  unfold IsHW hwSub
  refine ⟨hv0, Submodule.mem_inf.2 ⟨?_, ?_⟩⟩
  · simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply]
    intro a
    rw [Ecc_of_wt hvw a, sub_self]
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro a b hab
    obtain ⟨hsame, hne, htw⟩ := posC_facts hab
    by_contra hw0
    have hwU := hstab a b hsame v hv
    have hw' := wt_Eab_of hvw a b hsame hne
    have hmemT : (fun c => ν₀ c + (if a = c then 1 else 0) - (if b = c then 1 else 0)) ∈
        (S.image wtv).filter (fun ν => ∃ v ∈ U, v ≠ 0 ∧ IsWt ν v) :=
      Finset.mem_filter.2 ⟨hwtS _ _ hwU hw0 hw', _, hwU, hw0, hw'⟩
    have h1 := hmax _ hmemT
    rw [fw_shift] at h1
    linarith

end PI.FockOneDegW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.SameBlockOfPosC
noncomputable section

open Matrix FockH1Action MvPolynomial FockRaiseLowInner

namespace PI.FockOneDegW

theorem sameBlock_of_posC {p q : ℕ} {a b : Ix p q} (h : posC a b) : sameBlock a b := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [posC, sameBlock]

theorem isKC_Eab {p q : ℕ} {a b : Ix p q} (h : sameBlock a b) : IsKC (Eab a b) := by
  intro x y hxy
  simp only [Eab, Matrix.single_apply]
  split_ifs with h'
  · obtain ⟨rfl, rfl⟩ := h'
    exact absurd h hxy
  · rfl

def harmSub (hS : HarmSub) (p q r s : ℕ) : Submodule ℂ (Pol p q r s) where
  carrier := {P | Harm2 P}
  zero_mem' := (hS p q r s).1
  add_mem' := fun ha hb => (hS p q r s).2.1 _ _ ha hb
  smul_mem' := fun c _ h => (hS p q r s).2.2 c _ h

def innerL {σ : Type} (x : MvPolynomial σ ℂ) : MvPolynomial σ ℂ →ₗ[ℂ] ℂ where
  toFun Q := fockInner x Q
  map_add' Q Q' := fockInner_add_right x Q Q'
  map_smul' c Q := by simp [fockInner_smul_right]

theorem exists_orth {σ : Type} {V N : Submodule ℂ (MvPolynomial σ ℂ)} [FiniteDimensional ℂ V]
    (hNV : N < V) : ∃ c ∈ V, c ≠ 0 ∧ ∀ n ∈ N, fockInner n c = 0 := by
  classical
  have : FiniteDimensional ℂ N := Submodule.finiteDimensional_of_le hNV.le
  set k := Module.finrank ℂ N
  let b := Module.finBasis ℂ N
  let Φ : MvPolynomial σ ℂ →ₗ[ℂ] (Fin k → ℂ) := LinearMap.pi (fun i => innerL ((b i : N) : MvPolynomial σ ℂ))
  let Ψ := Φ.domRestrict V
  have h1 := LinearMap.finrank_range_add_finrank_ker Ψ
  have h2 : Module.finrank ℂ (LinearMap.range Ψ) ≤ k := by
    have := Submodule.finrank_le (LinearMap.range Ψ)
    simpa [Module.finrank_fin_fun] using this
  have h3 : k < Module.finrank ℂ V := Submodule.finrank_lt_finrank_of_lt hNV
  have h4 : LinearMap.ker Ψ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at h1
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h4
  refine ⟨(x : MvPolynomial σ ℂ), x.2, fun h => hx0 (Subtype.ext h), fun n hn => ?_⟩
  have hx' : ∀ i, fockInner ((b i : N) : MvPolynomial σ ℂ) (x : MvPolynomial σ ℂ) = 0 := by
    intro i
    have := congrFun (LinearMap.mem_ker.mp hx) i
    simpa [Ψ, Φ, innerL] using this
  have hsum := b.sum_repr ⟨n, hn⟩
  have hn' : n = ∑ i, (b.repr ⟨n, hn⟩ i) • ((b i : N) : MvPolynomial σ ℂ) := by
    conv_lhs => rw [show n = ((⟨n, hn⟩ : N) : MvPolynomial σ ℂ) from rfl, ← hsum]
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
  rw [hn', fockInner_sum_left]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [fockInner_smul_left, hx' i, mul_zero]

theorem key_of (hI : InnerFacts) (hKc : KHc) (hKh : KHarm) (hHc : HcHarm) (hS : HarmSub)
    (hA : KAdj) (hE : HwExist) (hT : HwHarmDeg)
    {p q r s : ℕ} (μ : Ix p q → ℚ) (W : Submodule ℂ (Pol p q r s)) [FiniteDimensional ℂ W]
    (hWK : KStable (fockAct1 p q r s) W)
    (hWhw : ∀ (ν : Ix p q → ℚ) (w : Pol p q r s), w ∈ W → IsHW (fockAct1 p q r s) ν w → ν = μ)
    (P : Pol p q r s) (hPW : P ∈ W) (hH : Harm2 P) (e : ℕ)
    (he : homogeneousComponent e P ≠ 0) :
    (e : ℚ) = degW (cPair r s) μ := by
  classical
  let V : Submodule ℂ (Pol p q r s) := W ⊓ harmSub hS p q r s
  let N : Submodule ℂ (Pol p q r s) :=
    V ⊓ LinearMap.ker (homogeneousComponent e : Pol p q r s →ₗ[ℂ] Pol p q r s)
  haveI : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le inf_le_left
  have hVst : ∀ a b : Ix p q, sameBlock a b → ∀ u ∈ V, fockAct1 p q r s (Eab a b) u ∈ V := by
    intro a b hab u hu
    exact ⟨hWK _ (isKC_Eab hab) u hu.1, hKh p q r s a b hab u hu.2⟩
  have hNst : ∀ a b : Ix p q, sameBlock a b → ∀ u ∈ N, fockAct1 p q r s (Eab a b) u ∈ N := by
    intro a b hab u hu
    refine ⟨hVst a b hab u hu.1, ?_⟩
    have h0 : homogeneousComponent e u = 0 := hu.2
    show homogeneousComponent e (fockAct1 p q r s (Eab a b) u) = 0
    rw [hKc p q r s a b hab e u, h0, map_zero]
  let C : Submodule ℂ (Pol p q r s) :=
    { carrier := {c | c ∈ V ∧ ∀ n ∈ N, fockInner n c = 0}
      add_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨V.add_mem hx hy, fun n hn => ?_⟩
        rw [fockInner_add_right, hx' n hn, hy' n hn, add_zero]
      zero_mem' := ⟨V.zero_mem, fun n _ => fockInner_zero_right n⟩
      smul_mem' := by
        rintro c x ⟨hx, hx'⟩
        refine ⟨V.smul_mem c hx, fun n hn => ?_⟩
        rw [fockInner_smul_right, hx' n hn, mul_zero] }
  have hPV : P ∈ V := ⟨hPW, hH⟩
  have hPN : P ∉ N := fun h => he h.2
  have hNV : N < V := lt_of_le_of_ne inf_le_left (fun h => hPN (h ▸ hPV))
  obtain ⟨c0, hc0V, hc0, hc0N⟩ := exists_orth hNV
  have hCne : C ≠ ⊥ := by
    intro h
    have : c0 ∈ C := ⟨hc0V, hc0N⟩
    rw [h, Submodule.mem_bot] at this
    exact hc0 this
  haveI : FiniteDimensional ℂ C :=
    Submodule.finiteDimensional_of_le (show C ≤ V from fun x hx => hx.1)
  have hCst : ∀ a b : Ix p q, sameBlock a b → ∀ u ∈ C, fockAct1 p q r s (Eab a b) u ∈ C := by
    intro a b hab u hu
    refine ⟨hVst a b hab u hu.1, fun n hn => ?_⟩
    rw [hA p q r s a b hab n u]
    have hba : sameBlock b a := by
      rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]
    exact hu.2 _ (hNst b a hba n hn)
  obtain ⟨ν, v, hvC, hv0, hvhw⟩ := hE p q r s C inferInstance hCne hCst
  have hνμ : ν = μ := hWhw ν v hvC.1.1 ⟨hv0, hvhw⟩
  subst hνμ

  have hve : homogeneousComponent e v ≠ 0 := by
    intro h
    have hvN : v ∈ N := ⟨hvC.1, h⟩
    have := hvC.2 v hvN
    exact hv0 ((hI _ v v v 0).2.2.2.2.1 this)
  have hwt : ∀ a : Ix p q, fockAct1 p q r s (Eab a a) v = ((ν a : ℚ) : ℂ) • v := by
    intro a
    have := (Submodule.mem_iInf _).mp hvhw.1 a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    simpa using this
  have hraise : ∀ a b : Ix p q, posC a b → fockAct1 p q r s (Eab a b) v = 0 := by
    intro a b hab
    have h1 := (Submodule.mem_iInf _).mp hvhw.2 a
    have h2 := (Submodule.mem_iInf _).mp h1 b
    have h3 := (Submodule.mem_iInf _).mp h2 hab
    exact LinearMap.mem_ker.mp h3
  have hsame : ∀ a : Ix p q, sameBlock a a := by
    intro a; rcases a with a | a <;> simp [sameBlock]
  have hHW : IsHW (fockAct1 p q r s) ν (homogeneousComponent e v) := by
    refine ⟨hve, ?_, ?_⟩
    · refine (Submodule.mem_iInf _).mpr fun a => ?_
      rw [LinearMap.mem_ker, LinearMap.sub_apply, ← hKc p q r s a a (hsame a) e v, hwt a,
        map_smul, LinearMap.smul_apply, LinearMap.id_apply, sub_self]
    · refine (Submodule.mem_iInf _).mpr fun a => (Submodule.mem_iInf _).mpr fun b =>
        (Submodule.mem_iInf _).mpr fun hab => ?_
      rw [LinearMap.mem_ker, ← hKc p q r s a b (sameBlock_of_posC hab) e v, hraise a b hab, map_zero]
  have hhom : homogeneousComponent e v ∈ homog (Ix p q × Ix r s) e :=
    (mem_homogeneousSubmodule _ _).mpr (homogeneousComponent_isHomogeneous e v)
  exact hT p q r s ν e _ hhom hHW (hHc p q r s e v hvC.1.2)

theorem reduction_of (hI : InnerFacts) (hKc : KHc) (hKh : KHarm) (hHc : HcHarm) (hS : HarmSub)
    (hA : KAdj) (hE : HwExist) : Reduction := by
  intro hT p q r s μ P hP0 hOT hH
  obtain ⟨W, hWfd, hPW, hWK, hWhw⟩ := hOT
  have key := fun e he => key_of hI hKc hKh hHc hS hA hE hT μ W hWK hWhw P hPW hH e he
  obtain ⟨e, he⟩ : ∃ e, homogeneousComponent e P ≠ 0 := by
    by_contra h
    push_neg at h
    exact hP0 (FockRaiseLowGrade.eq_zero_of_hc P h)
  refine ⟨e, key e he, ?_⟩
  have hother : ∀ e', e' ≠ e → homogeneousComponent e' P = 0 := by
    intro e' hne
    by_contra h
    have h1 := key e' h
    rw [← key e he] at h1
    exact hne (by exact_mod_cast h1)
  have hPe : P = homogeneousComponent e P := by
    have : P - homogeneousComponent e P = 0 := by
      apply FockRaiseLowGrade.eq_zero_of_hc
      intro e'
      rw [map_sub, FockRaiseLowGrade.hc_hc]
      by_cases h : e' = e
      · subst h; simp
      · rw [if_neg h, hother e' h, sub_zero]
    exact sub_eq_zero.mp this
  rw [hPe]
  exact (mem_homogeneousSubmodule _ _).mpr (homogeneousComponent_isHomogeneous e P)

end PI.FockOneDegW
end
end

theorem fock_degree_one : PI.FockDegreeTwoParts.OneDeg :=
  PI.FockOneDegW.oneDeg_of
    (PI.FockOneDegW.Core.hwHarmDeg_of PI.FockOneDegW.fock_operators_kernel PI.FockOneDegW.harmIff)
    (PI.FockOneDegW.reduction_of PI.FockOneDegW.fock_inner_facts PI.FockOneDegW.kernel_highest_weight
      PI.FockOneDegW.kernel_harmonic PI.FockOneDegW.highest_weight_harmonic PI.FockOneDegW.harmonic_submodule
      PI.FockOneDegW.fock_kernel_adjoint PI.FockOneDegW.hwExist)
    PI.FockOneDegW.Swap.fock_swap_groups
