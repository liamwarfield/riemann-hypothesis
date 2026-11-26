module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SignedCoordinateEqSignSmul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.AAvCongr
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ThirdPeelingMinorMemIdeal
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstPeelingMinorMemIdeal
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

section peel

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem sign_last (m : ℕ) : ((((-1 : ℤ) ^ (m + m) : ℤ) : A)) = 1 := by
  rw [← two_mul, pow_mul]
  norm_num

theorem smul_mem' (I : Ideal A) (c : ℂ) {x : A} (hx : x ∈ I) : c • x ∈ I := by
  rw [Algebra.smul_def]
  exact I.mul_mem_left _ hx

theorem peel_core {m : ℕ} (I : Ideal A) {ι : Type} [Fintype ι] (η : ι → ℂ) (Q : Fin (m + 1) → A)
    (T : Fin (m + 1) → ι → A) (κ : ℂ)
    (hT : ∀ l, (∑ w, η w • T l w) - algebraMap ℂ A (if l = Fin.last m then κ else 0) ∈ I) :
    (∑ w, η w • ∑ l : Fin (m + 1), ((((-1 : ℤ) ^ (m + (l : ℕ)) : ℤ) : A)) * (Q l * T l w)) -
      κ • Q (Fin.last m) ∈ I := by
  have key : (∑ w, η w • ∑ l : Fin (m + 1), ((((-1 : ℤ) ^ (m + (l : ℕ)) : ℤ) : A)) * (Q l * T l w)) -
      κ • Q (Fin.last m) = ∑ l : Fin (m + 1), ((((-1 : ℤ) ^ (m + (l : ℕ)) : ℤ) : A)) *
        (Q l * ((∑ w, η w • T l w) - algebraMap ℂ A (if l = Fin.last m then κ else 0))) := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_smul_comm, Finset.smul_sum]
    congr 1
    · exact Finset.sum_comm
    · rw [Finset.sum_eq_single (Fin.last m)]
      · rw [if_pos rfl, Fin.val_last, sign_last, one_mul, Algebra.smul_def, Algebra.commutes]
      · intro l _ hl
        rw [if_neg hl, map_zero, mul_zero, mul_zero]
      · intro hn
        exact absurd (Finset.mem_univ _) hn
  rw [key]
  exact Submodule.sum_mem _ fun l _ => I.mul_mem_left _ (I.mul_mem_left _ (hT l))

theorem peel_col {n m : ℕ} (I : Ideal A) (E : Fin n → Fin n → A) {ι : Type} [Fintype ι] (η : ι → ℂ)
    (a : Fin (m + 1) → Fin n) (b0 : Fin m → Fin n) (bw : ι → Fin n) (u κ : ℂ)
    (hT : ∀ l, (∑ w, η w • Tm E (u - (m : ℂ)) (a l) (bw w)) - algebraMap ℂ A (if l = Fin.last m then κ else 0) ∈ I) :
    (∑ w, η w • qminor E a (Fin.snoc (α := fun _ => Fin n) b0 (bw w)) u) - κ • qminor E (a ∘ Fin.castSucc) b0 u ∈ I := by
  have hexp : ∀ w, qminor E a (Fin.snoc (α := fun _ => Fin n) b0 (bw w)) u =
      ∑ l : Fin (m + 1), ((((-1 : ℤ) ^ (m + (l : ℕ)) : ℤ) : A)) *
        (qminor E (a ∘ l.succAbove) b0 u * Tm E (u - (m : ℂ)) (a l) (bw w)) := by
    intro w
    rw [Formalism.FourierDecayAlt.P.expansion_last_column A n m E a (Fin.snoc (α := fun _ => Fin n) b0 (bw w)) u]
    congr 1; ext l
    have h1 : (Fin.snoc (α := fun _ => Fin n) b0 (bw w) : Fin (m + 1) → Fin n) ∘ Fin.castSucc = b0 := by
      funext x; simp [Fin.snoc_castSucc]
    rw [h1, Fin.snoc_last]
  simp_rw [hexp]
  have := peel_core I η (fun l => qminor E (a ∘ l.succAbove) b0 u) (fun l w => Tm E (u - (m : ℂ)) (a l) (bw w)) κ hT
  simpa [Fin.succAbove_last] using this

theorem hT_of (I : Ideal A) {ι : Type} [Fintype ι] (η : ι → ℂ) (X : ι → A) (d : ι → ℂ) (c : ℂ)
    (hX : ∀ w, X w - algebraMap ℂ A (d w) ∈ I) (hc : ∑ w, η w * d w = c) :
    (∑ w, η w • X w) - algebraMap ℂ A c ∈ I := by
  have e : (∑ w, η w • X w) - algebraMap ℂ A c = ∑ w, η w • (X w - algebraMap ℂ A (d w)) := by
    rw [← hc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [smul_sub, Finset.sum_sub_distrib, map_sum, map_mul, Algebra.smul_def, mul_sub]
  rw [e]
  exact Submodule.sum_mem _ fun w _ => smul_mem' I _ (hX w)

end peel

def pe (k r p : ℕ) : Fin (2 * r + k + 1) := ⟨min p (2 * r + k), by omega⟩
def ps (k r p : ℕ) : Fin (2 * r + k + 1) := ⟨2 * r + k - p, by omega⟩

@[simp] theorem pe_val (k r p : ℕ) : (pe k r p).val = min p (2 * r + k) := rfl
@[simp] theorem ps_val (k r p : ℕ) : (ps k r p).val = 2 * r + k - p := rfl

theorem mem_gen {A : Type} [Ring A] [Algebra ℂ A] {k r : ℕ} {z' : Fin (2 * r + k + 1) → ℂ}
    {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A} {p q : Fin (2 * r + k + 1)} (h : InNp k r p q) :
    E p q - algebraMap ℂ A (dpsiP k r z' p q) ∈ Ideal.span (rgen k r z' E) := Ideal.subset_span ⟨p, q, h, rfl⟩

theorem tm_offdiag {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) {p q : Fin n}
    (h : p ≠ q) : Tm E u p q = E p q := by
  simp [Tm, h]

theorem last_iff {m : ℕ} (l : Fin (m + 1)) : l = Fin.last m ↔ l.val = m := by
  rw [Fin.ext_iff, Fin.val_last]

theorem first_peeling_minor_mem_ideal {A : Type} [Ring A] [Algebra ℂ A] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (u : ℂ) : ∀ (m i : ℕ), i ≤ m → m + 1 ≤ r →
    qminor E (fun l : Fin m => pe k r l.val) (fun l : Fin m => pe k r (if l.val < i then l.val else l.val + 1)) u -
      qminor E (fun l : Fin i => pe k r l.val) (fun l : Fin i => pe k r l.val) u ∈ Ideal.span (rgen k r z' E) := by
  intro m
  induction m with
  | zero =>
    intro i hi _
    have hi0 : i = 0 := by omega
    subst hi0
    have e : (fun l : Fin 0 => pe k r (if l.val < 0 then l.val else l.val + 1)) = fun l : Fin 0 => pe k r l.val :=
      funext fun l => l.elim0
    rw [e, sub_self]
    exact Submodule.zero_mem _
  | succ m ih =>
    intro i hi hr
    rcases Nat.lt_or_ge i (m + 1) with hlt | hge
    · have hih := ih i (by omega) (by omega)
      have hstep : qminor E (fun l : Fin (m + 1) => pe k r l.val)
            (fun l : Fin (m + 1) => pe k r (if l.val < i then l.val else l.val + 1)) u -
          qminor E (fun l : Fin m => pe k r l.val)
            (fun l : Fin m => pe k r (if l.val < i then l.val else l.val + 1)) u ∈
            Ideal.span (rgen k r z' E) := by
        have hc := peel_core (Ideal.span (rgen k r z' E)) (ι := Unit) (fun _ => (1 : ℂ))
          (fun l : Fin (m + 1) => qminor E ((fun l : Fin (m + 1) => pe k r l.val) ∘ l.succAbove)
              (fun l : Fin m => pe k r (if l.val < i then l.val else l.val + 1)) u)
          (fun l _ => Tm E (u - (m : ℂ)) (pe k r l.val) (pe k r (m + 1))) 1 ?_
        · rw [Formalism.FourierDecayAlt.P.expansion_last_column A (2 * r + k + 1) m E]
          have hm : ¬ (m < i) := by omega
          simpa [Fin.succAbove_last, Fin.val_last, hm, Function.comp_def, Fin.coe_castSucc] using hc
        · intro l
          have hl := l.isLt
          have h1 : min (l.val) (2 * r + k) = l.val := Nat.min_eq_left (by omega)
          have h2 : min (m + 1) (2 * r + k) = m + 1 := Nat.min_eq_left (by omega)
          have hne : pe k r l.val ≠ pe k r (m + 1) := by
            intro e
            have := congrArg Fin.val e
            simp only [pe_val, h1, h2] at this
            omega
          have hin : InNp k r (pe k r l.val) (pe k r (m + 1)) := by
            simp only [InNp, pe_val, h1, h2]
            omega
          have hd : dpsiP k r z' (pe k r l.val) (pe k r (m + 1)) = if l.val = m then 1 else 0 := by
            simp only [dpsiP, pe_val, h1, h2]
            rw [if_pos ⟨by omega, by omega⟩]
            split_ifs <;> first | rfl | (exfalso; omega)
          simp only [Finset.univ_unique, Finset.sum_singleton, one_smul, last_iff]
          rw [tm_offdiag _ _ hne, ← hd]
          exact mem_gen hin
      have hsum := (Ideal.span (rgen k r z' E)).add_mem hstep hih
      rwa [sub_add_sub_cancel] at hsum
    · have hi1 : i = m + 1 := by omega
      subst hi1
      have e : (fun l : Fin (m + 1) => pe k r (if l.val < m + 1 then l.val else l.val + 1)) =
          fun l : Fin (m + 1) => pe k r l.val := by
        funext l
        rw [if_pos l.isLt]
      rw [e, sub_self]
      exact Submodule.zero_mem _

theorem first_peeling_identity : PeelingOmittedColumn := by
  intro A _ _ k r z' E m hm i u
  have e1 : ∀ (j : ℕ) (hj : j ≤ r), xR k r j hj = fun l : Fin j => pe k r l.val := by
    intro j hj
    funext l
    apply Fin.ext
    simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE, pe_val]
    have := l.isLt
    omega
  have e2 : (fun l : Fin m => xR k r (m + 1) hm (i.succAbove l)) =
      fun l : Fin m => pe k r (if l.val < i.val then l.val else l.val + 1) := by
    funext l
    apply Fin.ext
    simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE, pe_val, succAbove_val]
    have := l.isLt
    split_ifs <;> omega
  rw [e2, e1, e1]
  exact first_peeling_minor_mem_ideal k r z' E u m i.val (by have := i.isLt; omega) hm

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem pe_lt {k r p : ℕ} (h : p < 2 * r + k + 1) : (pe k r p).val = p := by
  rw [pe_val]
  omega

theorem herm_wsum (k r : ℕ) (v y : Fin (2 * r + k + 1) → ℂ) (hv : inWb k r v) :
    herm (Hpk k r) v y = ∑ w : Fin (k + 1), v (wI k r w) * herm (Hpk k r) (bvec (wI k r w)) y := by
  have hv' : v = ∑ w : Fin (k + 1), v (wI k r w) • bvec (wI k r w) := by
    funext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, bvec, smul_eq_mul]
    by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · rw [Finset.sum_eq_single ⟨i.val - r, by omega⟩]
      · have e : wI k r ⟨i.val - r, by omega⟩ = i := Fin.ext (by simp only [wI]; omega)
        rw [e, Pi.single_eq_same, mul_one]
      · intro w _ hw
        rw [Pi.single_eq_of_ne, mul_zero]
        intro e
        apply hw
        apply Fin.ext
        have := congrArg Fin.val e
        simp only [wI, Fin.val_mk] at this ⊢
        omega
      · intro hn
        exact absurd (Finset.mem_univ _) hn
    · rw [hv i (by omega)]
      symm
      apply Finset.sum_eq_zero
      intro w _
      rw [Pi.single_eq_of_ne, mul_zero]
      intro e
      have := congrArg Fin.val e
      simp only [wI] at this
      omega
  conv_lhs => rw [hv']
  simp only [herm, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem dpsi_e_w (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (p : ℕ) (hp : p < r) (w : Fin (k + 1)) :
    dpsiP k r z' (pe k r p) (wI k r w) = if p + 1 = r then z' (wI k r w) else 0 := by
  have h1 : min p (2 * r + k) = p := by omega
  have hw : (wI k r w).val = r + w.val := rfl
  have hwk := w.isLt
  simp only [dpsiP, pe_val, h1, hw]
  rw [if_neg (by omega), if_pos (by omega)]

theorem dpsi_last_basis_shift (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (a b : ℕ) (ha : a < r) (hb : b < r) :
    dpsiP k r z' (ps k r a) (ps k r b) = if b + 1 = a then 1 else 0 := by
  have c1 : ¬(2 * r + k - a < r ∧ 2 * r + k - b < r) := by omega
  have c2 : ¬(2 * r + k - a < r ∧ r ≤ 2 * r + k - b ∧ 2 * r + k - b ≤ r + k) := by omega
  have c3 : ¬(r ≤ 2 * r + k - a ∧ 2 * r + k - a ≤ r + k ∧ r + k < 2 * r + k - b) := by omega
  have c4 : r + k < 2 * r + k - a ∧ r + k < 2 * r + k - b := by omega
  have c5 : (2 * r + k - b = 2 * r + k - a + 1) ↔ (b + 1 = a) := by omega
  have c6 : ¬(2 * r + k - a ≤ r + k) := by omega
  simp only [dpsiP, ps_val, c1, c2, c3, c4, c5, c6, if_false, if_true, and_self, and_false, false_and, and_true]

theorem third_peeling_minor_mem_ideal {A : Type} [Ring A] [Algebra ℂ A] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (hG : GlRel E) (ell : ℂ) : ∀ (m i : ℕ), i ≤ m → m + 1 ≤ r →
    qminor E (fun l : Fin m => ps k r (if l.val < i then l.val else l.val + 1)) (fun l : Fin m => ps k r l.val)
        (ell + (m : ℂ) - 1) -
      qminor E (fun l : Fin i => ps k r l.val) (fun l : Fin i => ps k r l.val) (ell + (i : ℂ) - 1) ∈
      Ideal.span (rgen k r z' E) := by
  intro m
  induction m with
  | zero =>
    intro i hi _
    have hi0 : i = 0 := by omega
    subst hi0
    have e : (fun l : Fin 0 => ps k r (if l.val < 0 then l.val else l.val + 1)) = fun l : Fin 0 => ps k r l.val :=
      funext fun l => l.elim0
    rw [e, sub_self]
    exact Submodule.zero_mem _
  | succ m ih =>
    intro i hi hr
    rcases Nat.lt_or_ge i (m + 1) with hlt | hge
    · have hih := ih i (by omega) (by omega)
      have hu : ell + ((m + 1 : ℕ) : ℂ) - 1 = ell + (m : ℂ) := by push_cast; ring
      rw [hu]
      have hstep : qminor E (fun l : Fin (m + 1) => ps k r (if l.val < i then l.val else l.val + 1))
            (fun l : Fin (m + 1) => ps k r l.val) (ell + (m : ℂ)) -
          qminor E (fun l : Fin m => ps k r (if l.val < i then l.val else l.val + 1))
            (fun l : Fin m => ps k r l.val) (ell + (m : ℂ) - 1) ∈ Ideal.span (rgen k r z' E) := by
        have hc := peel_core (Ideal.span (rgen k r z' E)) (ι := Unit) (fun _ => (1 : ℂ))
          (fun l : Fin (m + 1) => qminor E
              ((fun l : Fin (m + 1) => ps k r (if l.val < i then l.val else l.val + 1)) ∘ Fin.castSucc)
              ((fun l : Fin (m + 1) => ps k r l.val) ∘ l.succAbove) (ell + (m : ℂ) - 1))
          (fun l _ => Tm E (ell + (m : ℂ)) (ps k r (m + 1)) (ps k r l.val)) 1 ?_
        · rw [Formalism.FourierDecayAlt.P.expansion_last_line A (2 * r + k + 1) m E hG]
          have hm : ¬ (m < i) := by omega
          simpa [Fin.succAbove_last, Fin.val_last, hm, Function.comp_def, Fin.coe_castSucc] using hc
        · intro l
          have hl := l.isLt
          have hne : ps k r (m + 1) ≠ ps k r l.val := by
            intro e
            have := congrArg Fin.val e
            simp only [ps_val] at this
            omega
          have hin : InNp k r (ps k r (m + 1)) (ps k r l.val) := by
            simp only [InNp, ps_val]
            omega
          have hd : dpsiP k r z' (ps k r (m + 1)) (ps k r l.val) = if l.val = m then 1 else 0 := by
            rw [dpsi_last_basis_shift k r z' (m + 1) l.val (by omega) (by omega)]
            split_ifs <;> first | rfl | (exfalso; omega)
          simp only [Finset.univ_unique, Finset.sum_singleton, one_smul, last_iff]
          rw [tm_offdiag _ _ hne, ← hd]
          exact mem_gen hin
      have hsum := (Ideal.span (rgen k r z' E)).add_mem hstep hih
      rwa [sub_add_sub_cancel] at hsum
    · have hi1 : i = m + 1 := by omega
      subst hi1
      have e : (fun l : Fin (m + 1) => ps k r (if l.val < m + 1 then l.val else l.val + 1)) =
          fun l : Fin (m + 1) => ps k r l.val := by
        funext l
        rw [if_pos l.isLt]
      rw [e, sub_self]
      exact Submodule.zero_mem _

private theorem sR_eq_ps (k r j : ℕ) (hj : j ≤ r) : sR k r j hj = fun l : Fin j => ps k r l.val := by
  funext l
  apply Fin.ext
  simp only [sR, Formalism.QuantumDeterminants.esI, Fin.coe_castLE, ps_val]

private theorem sR_succAbove_eq_ps (k r m : ℕ) (hm : m + 1 ≤ r) (i : Fin (m + 1)) :
    (fun l : Fin m => sR k r (m + 1) hm (i.succAbove l)) =
      fun l : Fin m => ps k r (if l.val < i.val then l.val else l.val + 1) := by
  funext l
  apply Fin.ext
  simp only [sR, Formalism.QuantumDeterminants.esI, Fin.coe_castLE, ps_val, succAbove_val]

theorem third_peeling_identity : PeelingDualColumn := by
  intro A _ _ k r z' E hG m hm i ell
  rw [sR_succAbove_eq_ps, sR_eq_ps, sR_eq_ps]
  exact third_peeling_minor_mem_ideal k r z' E hG ell m i.val (by have := i.isLt; omega) hm

theorem second_peeling_identity : PeelingCovector := by
  intro A _ _ k m z' yb E i u hz'
  have ha : xR k (m + 1) (m + 1) le_rfl = fun l : Fin (m + 1) => pe k (m + 1) l.val := by
    funext l; ext; simp only [xR, eI, Fin.val_castLE]; rw [pe_lt (by omega)]
  have hb : (fun l : Fin m => xR k (m + 1) (m + 1) le_rfl (i.succAbove l)) =
      fun l : Fin m => pe k (m + 1) (if l.val < i.val then l.val else l.val + 1) := by
    funext l; ext; simp only [xR, eI, Fin.val_castLE, succAbove_val, pe_val]; all_goals (split_ifs <;> omega)
  have hi : xR k (m + 1) i.val (by have := i.isLt; omega) = fun l : Fin i.val => pe k (m + 1) l.val := by
    funext l; ext; simp only [xR, eI, Fin.val_castLE]; rw [pe_lt (by omega)]
  rw [hb, ha, hi]
  have step := peel_col (Ideal.span (rgen k (m + 1) z' E)) E (fun w => herm (Hpk k (m + 1)) (bvec (wI k (m + 1) w)) yb)
    (fun l : Fin (m + 1) => pe k (m + 1) l.val) (fun l : Fin m => pe k (m + 1) (if l.val < i.val then l.val else l.val + 1))
    (wI k (m + 1)) u (herm (Hpk k (m + 1)) z' yb) (by
      intro l
      have := l.isLt
      apply hT_of _ _ _ (fun w => dpsiP k (m + 1) z' (pe k (m + 1) l.val) (wI k (m + 1) w))
      · intro w
        have hw := w.isLt
        have hne : pe k (m + 1) l.val ≠ wI k (m + 1) w := by
          intro h2; have h3 := congrArg Fin.val h2; rw [pe_lt (by omega)] at h3; simp only [wI] at h3; omega
        rw [tm_offdiag _ _ hne]
        apply mem_gen
        simp only [InNp, wI]; rw [pe_lt (by omega)]; omega
      · simp only [dpsi_e_w k (m + 1) z' l.val (by omega), last_iff]
        by_cases hl : l.val = m
        · have e : l.val + 1 = m + 1 := by omega
          simp only [e, if_true, hl]
          rw [herm_wsum k (m + 1) z' yb hz']
          congr 1; ext w; ring
        · have e : ¬ (l.val + 1 = m + 1) := by omega
          simp [e, hl])
  have hc : ((fun l : Fin (m + 1) => pe k (m + 1) l.val) ∘ Fin.castSucc) = fun l : Fin m => pe k (m + 1) l.val := by
    funext l; simp
  rw [hc] at step
  have h2 := smul_mem' _ (herm (Hpk k (m + 1)) z' yb) (first_peeling_minor_mem_ideal k (m + 1) z' E u m i.val (by omega) (by omega))
  have := Ideal.add_mem _ step h2
  rw [smul_sub] at this
  simpa using this

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem la_ideal {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M] {k r : ℕ}
    {z' : Fin (2 * r + k + 1) → ℂ} {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A} {La : A →ₗ[ℂ] M}
    (hR : RightRuleFn k r z' E La) {x : A} (hx : x ∈ Ideal.span (rgen k r z' E)) : La x = 0 := by
  have key : ∀ y ∈ Ideal.span (rgen k r z' E), ∀ a : A, La (a * y) = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, q, hpq, rfl⟩ := hy
      intro a
      rw [mul_sub, map_sub, hR a p q hpq, ← Algebra.commutes, ← Algebra.smul_def, map_smul, sub_self]
    | zero => intro a; simp
    | add x y _ _ hx hy => intro a; rw [mul_add, map_add (f := _), hx, hy, add_zero]
    | smul b x _ hx => intro a; rw [smul_eq_mul, ← mul_assoc]; exact hx (a * b)
  simpa using key x hx 1

theorem la_congr {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M] {k r : ℕ}
    {z' : Fin (2 * r + k + 1) → ℂ} {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A} {La : A →ₗ[ℂ] M}
    (hR : RightRuleFn k r z' E La) {x y : A} (hx : x - y ∈ Ideal.span (rgen k r z' E)) : La x = La y := by
  have := la_ideal hR hx
  rwa [map_sub, sub_eq_zero] at this

theorem sum_single {M : Type*} [AddCommGroup M] [Module ℂ M] {m N : ℕ} (P : (Fin m → Fin N) → Prop)
    [DecidablePred P] (X : Fin m → Fin N → ℂ) (S : Set (Fin N)) (hX : ∀ a p, p ∉ S → X a p = 0)
    (e : Fin m → Fin N) (he : P e) (huniq : ∀ c, P c → (∀ l, c l ∈ S) → c = e) (F : (Fin m → Fin N) → M) :
    (∑ c : Fin m → Fin N, if P c then (Matrix.of fun a l => X a (c l)).det • F c else 0) =
      (Matrix.of fun a l => X a (e l)).det • F e := by
  rw [Finset.sum_eq_single e]
  · rw [if_pos he]
  · intro c _ hc
    split_ifs with hP
    · by_cases hS : ∀ l, c l ∈ S
      · exact absurd (huniq c hP hS) hc
      · push Not at hS
        obtain ⟨l, hl⟩ := hS
        rw [Matrix.det_eq_zero_of_column_eq_zero l (fun a => by simp [hX a _ hl]), zero_smul]
    · rfl
  · intro h; exact absurd (Finset.mem_univ e) h

theorem uniq_mono {α : Type} [LinearOrder α] {m : ℕ} (e c : Fin m → α) (he : StrictMono e) (hc : StrictMono c)
    (hS : ∀ l, c l ∈ Set.range e) : c = e := by
  have hcard : (Finset.image e Finset.univ).card = m := by
    rw [Finset.card_image_of_injective _ he.injective]; simp
  have hS' : ∀ l, c l ∈ Finset.image e Finset.univ := by
    intro l; obtain ⟨x, hx⟩ := hS l; rw [← hx]; exact Finset.mem_image_of_mem e (Finset.mem_univ x)
  rw [Finset.orderEmbOfFin_unique hcard hS' hc]
  exact (Finset.orderEmbOfFin_unique hcard (fun l => Finset.mem_image_of_mem e (Finset.mem_univ l)) he).symm

theorem uniq_key {N m : ℕ} (key : Fin N → ℕ) (hkey : Function.Injective key) (e c : Fin m → Fin N)
    (he : StrictMono (fun l => key (e l))) (hc : StrictMono (fun l => key (c l)))
    (hS : ∀ l, c l ∈ Set.range e) : c = e := by
  have h := uniq_mono (fun l => key (e l)) (fun l => key (c l)) he hc (by
    intro l; obtain ⟨x, hx⟩ := hS l; exact ⟨x, by simp only [hx]⟩)
  funext l; exact hkey (congrFun h l)

theorem AAx_congr {A : Type} [Ring A] [Algebra ℂ A] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (xi : Fin r → Fin (2 * r + k + 1) → ℂ) {m1 m2 : ℕ} (h : m1 = m2) (h1 : m1 ≤ r) (h2 : m2 ≤ r) (u : ℂ) :
    AAx k r E xi m1 h1 u = AAx k r E xi m2 h2 u := by subst h; rfl

theorem AAv_congr {A : Type} [Ring A] [Algebra ℂ A] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (y : Fin r → Fin (2 * r + k + 1) → ℂ) {m1 m2 : ℕ} (h : m1 = m2) (h1 : m1 ≤ r) (h2 : m2 ≤ r) (ell : ℂ) :
    AAv k r E y m1 h1 ell = AAv k r E y m2 h2 ell := by subst h; rfl

theorem sgnW_sq (m : ℕ) : sgnW m * sgnW m = 1 := by
  unfold sgnW; rw [← pow_add, ← two_mul, pow_mul]; simp

theorem scal_E (dh t σ ε : ℂ) (s' : ℕ) (hdh : dh ≠ 0) (ht : t ≠ 0) (hσ : σ * σ = 1) (hε : ε * ε = 1) :
    (dh * t ^ (s' + 1) * (ε * σ))⁻¹ * (dh * t ^ s' * σ) = ε * t⁻¹ * (dh⁻¹ * dh) := by
  have hσ0 : σ ≠ 0 := by intro h0; rw [h0, zero_mul] at hσ; exact zero_ne_one hσ
  have hε0 : ε ≠ 0 := by intro h0; rw [h0, zero_mul] at hε; exact zero_ne_one hε
  have hεi : ε⁻¹ = ε := inv_eq_of_mul_eq_one_right hε
  rw [mul_inv, mul_inv, mul_inv, hεi, inv_mul_cancel₀ hdh, pow_succ]
  field_simp

theorem AAx_head {A : Type} [Ring A] [Algebra ℂ A] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (xi : Fin r → Fin (2 * r + k + 1) → ℂ) (i0 : ℕ) (hi0 : i0 ≤ r) (h : Matrix (Fin i0) (Fin i0) ℂ) (u : ℂ)
    (hz : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 → i0 ≤ p.val → xi a p = 0)
    (hh : ∀ a b : Fin i0, xi (Fin.castLE hi0 a) (xR k r i0 hi0 b) = h a b) :
    AAx k r E xi i0 hi0 u = h.det • qminor E (xR k r i0 hi0) (xR k r i0 hi0) u := by
  unfold AAx
  rw [sum_single (fun c => StrictMono c) (fun a p => xi (Fin.castLE hi0 a) p) (Set.range (xR k r i0 hi0))
    ?_ (xR k r i0 hi0) ?_ ?_]
  · congr 2
    ext a l
    simp only [Matrix.of_apply]
    exact hh a l
  · intro a p hp
    apply hz _ _ (by simp)
    by_contra hlt; push Not at hlt; apply hp; exact ⟨⟨p.val, hlt⟩, by ext; simp [xR, eI]⟩
  · intro a b hab; simp only [xR, eI]; exact hab
  · intro c hc hS
    exact uniq_mono _ _ (fun a b hab => by simp only [xR, eI]; exact hab) hc hS

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem keyS_inj (k r : ℕ) : Function.Injective (keyS k r) := by
  intro p q hpq
  apply Fin.ext
  have hp := p.isLt
  have hq := q.isLt
  unfold keyS at hpq
  split_ifs at hpq <;> omega

theorem keyS_esI (k r : ℕ) (x : Fin r) : keyS k r (esI k r x) = x.val := by
  have hx := x.isLt
  have c : r + k < 2 * r + k - x.val := by omega
  simp only [keyS, Formalism.QuantumDeterminants.esI, c, if_true]
  omega

theorem star_sgnW (m : ℕ) : star (sgnW m) = sgnW m := by
  simp [sgnW]

theorem neg_one_sq' (s : ℕ) : ((-1 : ℂ) ^ s) * ((-1) ^ s) = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

theorem zb_col_zero (i0 s' : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) (a : ℕ) (ha : a < i0 + s') :
    Zb i0 (s' + 1) h t a i0 = 0 := by
  unfold Zb
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem sgnW_succ' (s : ℕ) : sgnW (s + 1) = (-1) ^ s * sgnW s := by
  unfold sgnW
  rw [← pow_add]
  congr 1
  cases s with
  | zero => rfl
  | succ k =>
    have e : (k + 1 + 1) * (k + 1 + 1 - 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1) := by
      simp only [Nat.add_sub_cancel]
      ring
    rw [e, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
    ring

theorem first_expansion_identity : ExpansionOmittedColumn := by
  intro A _ _ M _ _ k r z' E La xi i0 s h t u hs hj hR hdet ht hxi
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hm : i0 + s' ≤ r := by omega
  rw [AAx_congr k r E xi (show i0 + (s' + 1) - 1 = i0 + s' by omega) _ hm u]
  have hhead : AAx k r E xi i0 (by omega) u =
      h.det • qminor E (xR k r i0 (by omega)) (xR k r i0 (by omega)) u := by
    apply AAx_head
    · intro a p ha hp
      rw [hxi a p (by omega)]
      split_ifs with hp'
      · unfold Zb
        rw [dite_eq_left ha, dite_eq_right (by omega)]
      · rfl
    · intro a b
      have ha := a.isLt
      have hb := b.isLt
      rw [hxi _ _ (by simp only [Fin.coe_castLE]; omega)]
      rw [if_pos (by simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE]; omega)]
      simp [Zb, xR, Formalism.QuantumDeterminants.eI, ha, hb]
  have he : StrictMono (fun l : Fin (i0 + s') =>
      xR k r (i0 + s' + 1) (by omega) ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l)) := by
    intro a b hab
    have := (Fin.strictMono_succAbove (⟨i0, by omega⟩ : Fin (i0 + s' + 1))) hab
    rw [Fin.lt_def] at this ⊢
    simpa [xR, Formalism.QuantumDeterminants.eI] using this
  have hmain : AAx k r E xi (i0 + s') hm u = (h.det * t ^ s' * sgnW s') •
      qminor E (xR k r (i0 + s') hm)
        (fun l => xR k r (i0 + s' + 1) (by omega) ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l)) u := by
    classical
    have hX : ∀ (a : Fin (i0 + s')) (p : Fin (2 * r + k + 1)),
        p ∉ {p : Fin (2 * r + k + 1) | p.val < i0 + s' + 1 ∧ p.val ≠ i0} → xi (Fin.castLE hm a) p = 0 := by
      intro a p hp
      simp only [Set.mem_setOf_eq, not_and, not_not] at hp
      have ha := a.isLt
      rw [hxi _ p (by simp only [Fin.coe_castLE]; omega)]
      split_ifs with hp1
      · rw [hp (by omega)]
        exact zb_col_zero i0 s' h t _ (by simp only [Fin.coe_castLE]; omega)
      · rfl
    have hu : ∀ c : Fin (i0 + s') → Fin (2 * r + k + 1), StrictMono c →
        (∀ l, c l ∈ {p : Fin (2 * r + k + 1) | p.val < i0 + s' + 1 ∧ p.val ≠ i0}) →
        c = fun l => xR k r (i0 + s' + 1) (by omega) ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l) := by
      intro c hc hS
      apply uniq_mono _ _ he hc
      intro l
      obtain ⟨h1, h2⟩ := hS l
      have hne : (⟨(c l).val, h1⟩ : Fin (i0 + s' + 1)) ≠ ⟨i0, by omega⟩ := fun e => h2 (congrArg Fin.val e)
      obtain ⟨j, hj'⟩ := Fin.exists_succAbove_eq hne
      refine ⟨j, ?_⟩
      apply Fin.ext
      simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE, hj']
    have hs := sum_single (M := A) StrictMono (fun a p => xi (Fin.castLE hm a) p)
      {p : Fin (2 * r + k + 1) | p.val < i0 + s' + 1 ∧ p.val ≠ i0} hX _ he hu
      (fun c => qminor E (xR k r (i0 + s') hm) c u)
    have hdet' : (Matrix.of fun a l : Fin (i0 + s') => xi (Fin.castLE hm a)
        (xR k r (i0 + s' + 1) (by omega) ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l))).det =
        h.det * t ^ s' * sgnW s' := by
      have hp := minors_first_case i0 s' h t ⟨i0, by omega⟩
      rw [if_pos rfl] at hp
      rw [← hp]
      congr 1
      ext a l
      have ha := a.isLt
      have hl := ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l).isLt
      simp only [Matrix.of_apply]
      rw [hxi _ _ (by simp only [Fin.coe_castLE]; omega)]
      rw [if_pos (by simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE]; omega)]
      simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE]
    unfold AAx
    rw [← hdet']
    convert hs using 1
  have hpeel := first_peeling_identity A k r z' E (i0 + s') (by omega) ⟨i0, by omega⟩ u
  have hL := la_congr hR hpeel
  have hsc : (h.det * t ^ (s' + 1) * sgnW (s' + 1))⁻¹ * (h.det * t ^ s' * sgnW s') =
      (-1 : ℂ) ^ (s' + 1 - 1) * t⁻¹ * (h.det⁻¹ * h.det) := by
    rw [sgnW_succ', Nat.add_sub_cancel, scal_E _ _ _ _ s' hdet ht (sgnW_sq s') (neg_one_sq' s')]
  rw [hmain, hhead, map_smul, map_smul, hL, (derivative_leading_zb i0 (s' + 1) h t).2,
    (derivative_leading_zb i0 (s' + 1) h t).1, smul_smul, smul_smul, smul_smul]
  congr 1
  rw [hsc]
  ring

end Formalism.FourierDecayAlt.P.SignAntidiagonal
