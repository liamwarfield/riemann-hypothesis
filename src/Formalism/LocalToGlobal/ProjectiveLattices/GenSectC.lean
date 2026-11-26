module

public import Mathlib

@[expose] public section

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.GenSectB
section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.GenSectA
noncomputable section

namespace Formalism.L2.Pj.GenSect

open MvPolynomial
open scoped TensorProduct

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (D m : ℕ)

abbrev KT : Type := MvPolynomial (Fin (D + 1) × Fin m) K

abbrev KTf : Type := FractionRing (KT K D m)

abbrev ΩT : Type := MvPolynomial (Fin (D + 1) × Fin m) Ω

def ktToΩ : KT K D m →+* ΩT Ω D m := MvPolynomial.map (algebraMap K Ω)

def KTS : Submonoid (ΩT Ω D m) := (nonZeroDivisors (KT K D m)).map (ktToΩ K Ω D m)

abbrev RS : Type := Localization (KTS K Ω D m)

instance algKTR : Algebra (KTf K D m) (RS K Ω D m) :=
  (IsLocalization.map (M := nonZeroDivisors (KT K D m)) (T := KTS K Ω D m) (RS K Ω D m) (ktToΩ K Ω D m)
    (Submonoid.le_comap_map _) :
    KTf K D m →+* RS K Ω D m).toAlgebra

variable {K Ω D m}

def sec (x : Fin m → Ω) (i : Fin D) : ΩT Ω D m := ∑ j, X (i.succ, j) * C (x j)


variable (K) in
def Is (x : Fin m → Ω) : Ideal (RS K Ω D m) :=
  Ideal.span (Set.range fun i : Fin D => algebraMap (ΩT Ω D m) (RS K Ω D m) (sec x i))

def Zs (j₀ : Fin m) (p : Fin (D + 1) × Fin m) : Prop := p.1 ≠ 0 ∧ p.2 = j₀

instance (j₀ : Fin m) : DecidablePred (Zs (D := D) j₀) := fun p => by unfold Zs; infer_instance


variable (Ω D) in
abbrev CT (j₀ : Fin m) : Type :=
  MvPolynomial {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p} Ω

def xv (j₀ : Fin m) (p : Fin (D + 1) × Fin m) : CT Ω D j₀ :=
  if h : Zs j₀ p then 0 else X ⟨p, h⟩

def rr (x : Fin m → Ω) (j₀ : Fin m) (j : Fin m) : Ω := x j / x j₀

def gs (x : Fin m → Ω) (j₀ : Fin m) (p : Fin (D + 1) × Fin m) : CT Ω D j₀ :=
  if Zs j₀ p then -∑ k, xv j₀ (p.1, k) * C (rr x j₀ k) else xv j₀ p

def psi (x : Fin m → Ω) (j₀ : Fin m) : ΩT Ω D m →ₐ[Ω] CT Ω D j₀ := aeval (gs x j₀)

def incl (j₀ : Fin m) : CT Ω D j₀ →ₐ[Ω] ΩT Ω D m := rename Subtype.val

theorem xv_of_not {j₀ : Fin m} {p : Fin (D + 1) × Fin m} (h : ¬ Zs j₀ p) :
    xv (Ω := Ω) j₀ p = X ⟨p, h⟩ := by
  rw [xv, dif_neg h]

theorem xv_of_Z {j₀ : Fin m} {p : Fin (D + 1) × Fin m} (h : Zs j₀ p) :
    xv (Ω := Ω) j₀ p = 0 := by
  rw [xv, dif_pos h]

theorem psi_X (x : Fin m → Ω) (j₀ : Fin m) (p : Fin (D + 1) × Fin m) :
    psi x j₀ (X p) = gs x j₀ p := by
  rw [psi, aeval_X]

theorem psi_C (x : Fin m → Ω) (j₀ : Fin m) (a : Ω) :
    psi (D := D) x j₀ (C a) = C a := by
  rw [psi, aeval_C, MvPolynomial.algebraMap_eq]

theorem incl_C (j₀ : Fin m) (a : Ω) : incl (D := D) j₀ (C a) = C a := by
  rw [incl, rename_C]

theorem gs_succ (x : Fin m → Ω) (j₀ : Fin m) (i : Fin D) (j : Fin m) :
    gs x j₀ (i.succ, j) = xv j₀ (i.succ, j) +
      if j = j₀ then -∑ k, xv j₀ (i.succ, k) * C (rr x j₀ k) else 0 := by
  by_cases h : j = j₀
  · have hz : Zs j₀ (i.succ, j) := by
      unfold Zs
      exact ⟨Fin.succ_ne_zero i, h⟩
    rw [gs, if_pos hz, xv_of_Z hz, if_pos h, zero_add]
    try rfl
  · have hz : ¬ Zs j₀ (i.succ, j) := by
      unfold Zs
      exact fun hz => h hz.2
    rw [gs, if_neg hz, if_neg h, add_zero]

theorem psi_sec (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0) (i : Fin D) :
    psi x j₀ (sec x i) = 0 := by
  have hS : (∑ k, xv (Ω := Ω) j₀ (i.succ, k) * C (rr x j₀ k)) * C (x j₀) =
      ∑ k, xv (Ω := Ω) j₀ (i.succ, k) * C (x k) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, ← C_mul, rr]
    congr 2
    exact div_mul_cancel₀ (x k) hx₀
  have hI : ∑ j : Fin m, (if j = j₀ then -∑ k, xv (Ω := Ω) j₀ (i.succ, k) * C (rr x j₀ k) else 0) * C (x j) =
      -(∑ k, xv (Ω := Ω) j₀ (i.succ, k) * C (rr x j₀ k)) * C (x j₀) := by
    rw [Finset.sum_eq_single j₀]
    · rw [if_pos rfl]
    · intro b _ hb
      rw [if_neg hb, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ j₀) h
  have h1 : psi x j₀ (sec x i) = ∑ j, gs x j₀ (i.succ, j) * C (x j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [sec, map_sum, map_mul, psi_X, psi_C]
  rw [h1]
  simp only [gs_succ, add_mul]
  rw [Finset.sum_add_distrib, hI, neg_mul, hS]
  exact add_neg_cancel _

theorem incl_xv_succ (j₀ : Fin m) (i : Fin D) (k : Fin m) :
    incl (Ω := Ω) j₀ (xv j₀ (i.succ, k)) = if k = j₀ then 0 else X (i.succ, k) := by
  by_cases h : k = j₀
  · have hz : Zs j₀ (i.succ, k) := by
      unfold Zs
      exact ⟨Fin.succ_ne_zero i, h⟩
    rw [xv_of_Z hz, map_zero, if_pos h]
  · have hz : ¬ Zs j₀ (i.succ, k) := by
      unfold Zs
      exact fun hz => h hz.2
    rw [xv_of_not hz, if_neg h, incl, rename_X]
    try rfl

theorem X_sub_incl_gs (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0) (i : Fin D) :
    X (i.succ, j₀) - incl j₀ (gs x j₀ (i.succ, j₀)) = C (x j₀)⁻¹ * sec x i := by
  have hz : Zs j₀ (i.succ, j₀) := by
    unfold Zs
    exact ⟨Fin.succ_ne_zero i, rfl⟩
  rw [gs, if_pos hz]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_neg, map_sum, map_mul, incl_C, incl_xv_succ, sub_neg_eq_add, sec, Finset.mul_sum]
  have hX : (X (i.succ, j₀) : ΩT Ω D m) = ∑ j : Fin m, if j = j₀ then (X (i.succ, j₀) : ΩT Ω D m) else 0 := by
    simp
  rw [hX, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j = j₀
  · subst h
    rw [if_pos rfl, if_pos rfl, zero_mul, add_zero, mul_left_comm, ← C_mul, inv_mul_cancel₀ hx₀, C_1, mul_one]
  · rw [if_neg h, if_neg h, zero_add, rr, div_eq_mul_inv, C_mul]
    ring

theorem sub_incl_psi_mem (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0) (f : ΩT Ω D m) :
    f - incl j₀ (psi x j₀ f) ∈ Ideal.span (Set.range (sec x)) := by
  have hgen : ∀ p : Fin (D + 1) × Fin m,
      X p - incl j₀ (psi x j₀ (X p)) ∈ Ideal.span (Set.range (sec x)) := by
    intro p
    rw [psi_X]
    by_cases hp : Zs j₀ p
    · obtain ⟨i', j⟩ := p
      have hp' : i' ≠ 0 ∧ j = j₀ := hp
      obtain ⟨i, rfl⟩ : ∃ i : Fin D, i.succ = i' := by
        exact Fin.exists_succ_eq.mpr hp'.1
      rw [hp'.2, X_sub_incl_gs x j₀ hx₀ i]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    · simp [gs, hp, xv_of_not hp, incl]
  induction f using MvPolynomial.induction_on
  next a =>
    rw [psi_C, incl_C, sub_self]
    exact Ideal.zero_mem _
  next f g hf hg =>
    have e : f + g - incl j₀ (psi x j₀ (f + g)) =
        (f - incl j₀ (psi x j₀ f)) + (g - incl j₀ (psi x j₀ g)) := by
      simp only [map_add (f := _)]
      ring
    rw [e]
    exact Ideal.add_mem _ hf hg
  next f p hf =>
    have e : f * X p - incl j₀ (psi x j₀ (f * X p)) =
        (f - incl j₀ (psi x j₀ f)) * X p + incl j₀ (psi x j₀ f) * (X p - incl j₀ (psi x j₀ (X p))) := by
      simp only [map_mul]
      ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hf) (Ideal.mul_mem_left _ _ (hgen p))

theorem psi_eq_zero_iff (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0) (f : ΩT Ω D m) :
    psi x j₀ f = 0 ↔ f ∈ Ideal.span (Set.range (sec x)) := by
  constructor
  · intro h
    have hm := sub_incl_psi_mem x j₀ hx₀ f
    rwa [h, map_zero, sub_zero] at hm
  · intro hf
    have hle : Ideal.span (Set.range (sec (D := D) x)) ≤ RingHom.ker (psi (D := D) x j₀) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact RingHom.mem_ker.mpr (psi_sec x j₀ hx₀ i)
    exact RingHom.mem_ker.mp (hle hf)

theorem pderiv_xv (j₀ : Fin m) (q : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p}) (p : Fin (D + 1) × Fin m) :
    pderiv q (xv (Ω := Ω) j₀ p) = if p = q.1 then 1 else 0 := by
  by_cases hp : Zs j₀ p
  · have hne : p ≠ q.1 := fun h => q.2 (h ▸ hp)
    rw [xv_of_Z hp, map_zero, if_neg hne]
  · rw [xv_of_not hp, pderiv_X, Pi.single_apply]
    by_cases h : p = q.1
    · have e : (⟨p, hp⟩ : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p}) = q := Subtype.ext h
      rw [if_pos e, if_pos h]
    · have e : (⟨p, hp⟩ : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p}) ≠ q :=
        fun e => h (congrArg Subtype.val e)
      rw [if_neg e, if_neg h]

theorem pderiv_gs (x : Fin m → Ω) (j₀ : Fin m) (q : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p})
    (p : Fin (D + 1) × Fin m) :
    pderiv q (gs x j₀ p) = (if p = q.1 then 1 else 0) -
      if Zs j₀ p ∧ p.1 = q.1.1 then C (rr x j₀ q.1.2) else 0 := by
  by_cases hp : Zs j₀ p
  · have hne : p ≠ q.1 := fun h => q.2 (h ▸ hp)
    rw [gs, if_pos hp, if_neg hne, zero_sub, map_neg]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Derivation.leibniz, pderiv_C, smul_zero, smul_eq_mul, pderiv_xv, mul_zero, zero_add]
    rw [Finset.sum_eq_single q.1.2]
    · by_cases h1 : p.1 = q.1.1
      · have e : (p.1, q.1.2) = q.1 := Prod.ext h1 rfl
        rw [if_pos e, if_pos ⟨hp, h1⟩, mul_one]
      · have e : (p.1, q.1.2) ≠ q.1 := fun h => h1 (by have h' := congrArg Prod.fst h; exact h')
        have hn : ¬ (Zs j₀ p ∧ p.1 = q.1.1) := fun h => h1 h.2
        rw [if_neg e, if_neg hn, mul_zero]
    · intro k _ hk
      have e : (p.1, k) ≠ q.1 := fun h => hk (congrArg Prod.snd h)
      rw [if_neg e, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hn : ¬ (Zs j₀ p ∧ p.1 = q.1.1) := fun h => hp h.1
    rw [gs, if_neg hp, pderiv_xv, if_neg hn, sub_zero]

theorem pderiv_aeval {ι : Type*} [Fintype ι] [DecidableEq ι] (j₀ : Fin m) (u : ι → CT Ω D j₀)
    (q : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p}) (G : MvPolynomial ι K) :
    pderiv q (aeval u G) = ∑ p, aeval u (pderiv p G) * pderiv q (u p) := by
  induction G using MvPolynomial.induction_on
  next a =>
    simp
  next G₁ G₂ h₁ h₂ =>
    simp only [map_add (f := _), h₁, h₂, add_mul, Finset.sum_add_distrib]
  next G i h =>
    have e1 : ∀ p, pderiv p (G * X i) = G * pderiv p (X i) + X i * pderiv p G := fun p => by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have hs : ∑ p, aeval u (G * pderiv p (X i)) * pderiv q (u p) = aeval u G * pderiv q (u i) := by
      rw [Finset.sum_eq_single i]
      · rw [pderiv_X_self, mul_one]
      · intro b _ hb
        have h0 : pderiv b (X i : MvPolynomial ι K) = 0 := by
          exact pderiv_X_of_ne (Ne.symm hb)
        rw [h0, mul_zero, map_zero, zero_mul]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rw [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, smul_eq_mul, h]
    simp only [e1, map_add (f := _), add_mul, Finset.sum_add_distrib]
    rw [hs]
    simp only [map_mul, aeval_X, Finset.mul_sum, mul_assoc]

end Formalism.L2.Pj.GenSect
end
end

noncomputable section

namespace Formalism.L2.Pj.GenSect

open MvPolynomial Cardinal

theorem exists_pderiv_ne_zero_lt' {K : Type*} [Field K] [CharZero K] {ι : Type*}
    (P : MvPolynomial ι K) (hP : 0 < P.totalDegree) :
    ∃ i, pderiv i P ≠ 0 ∧ (pderiv i P).totalDegree < P.totalDegree := by
  classical
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp at hP
  obtain ⟨s, hs, hsd⟩ := Finset.exists_mem_eq_sup P.support (support_nonempty.2 hP0)
    (fun s : ι →₀ ℕ => s.sum fun _ e => e)
  have htd : P.totalDegree = s.sum fun _ e => e := hsd
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [htd] at hP
    simp at hP
  obtain ⟨i, hi⟩ : ∃ i, s i ≠ 0 := by
    by_contra h
    push Not at h
    exact hs0 (Finsupp.ext h)
  have hdeg : ∀ t : ι →₀ ℕ, t i ≠ 0 →
      (t.sum fun _ e => e) = ((t - Finsupp.single i 1).sum fun _ e => e) + 1 := by
    intro t ht
    have hle : Finsupp.single i 1 ≤ t := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 ht)
    conv_lhs => rw [← tsub_add_cancel_of_le hle]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  have hder : pderiv i P =
      ∑ t ∈ P.support, monomial (t - Finsupp.single i 1) (AddMonoidAlgebra.coeff P t * (t i : K)) := by
    conv_lhs => rw [P.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [pderiv_monomial]
  refine ⟨i, ?_, ?_⟩
  · intro h0
    have hc := congrArg (AddMonoidAlgebra.coeff · (s - Finsupp.single i 1)) h0
    rw [hder, coeff_sum, AddMonoidAlgebra.coeff_zero, Finset.sum_eq_single s] at hc
    · rw [coeff_monomial, if_pos rfl] at hc
      exact mul_ne_zero (mem_support_iff.1 hs) (by exact_mod_cast hi) hc
    · intro t _ hts
      rw [coeff_monomial]
      split_ifs with heq
      · by_cases hti : t i = 0
        · simp [hti]
        · exfalso
          apply hts
          have h1 : Finsupp.single i 1 ≤ t := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hti)
          have h2 : Finsupp.single i 1 ≤ s := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hi)
          rw [← tsub_add_cancel_of_le h1, ← tsub_add_cancel_of_le h2, heq]
      · rfl
    · intro hns
      exact absurd hs hns
  · have hpos : (⊥ : ℕ) < s.sum fun _ e => e := by
      rw [← htd]
      exact hP
    rw [htd, hder]
    refine lt_of_le_of_lt (MvPolynomial.totalDegree_finsetSum _ _) ((Finset.sup_lt_iff hpos).2 fun t ht => ?_)
    by_cases hti : t i = 0
    · simpa [hti, htd] using hP
    · refine lt_of_le_of_lt (totalDegree_monomial_le _ _) ?_
      have h1 := hdeg t hti
      have h2 : (t.sum fun _ e => e) ≤ s.sum fun _ e => e := by
        rw [← htd]
        exact le_totalDegree ht
      rw [h1] at h2
      exact h2

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}

theorem card_Z (j₀ : Fin m) : Fintype.card {p : Fin (D + 1) × Fin m // Zs j₀ p} = D := by
  let e : {p : Fin (D + 1) × Fin m // Zs j₀ p} ≃ {i : Fin (D + 1) // i ≠ 0} :=
    { toFun := fun q => ⟨q.1.1, (q.2 : q.1.1 ≠ 0 ∧ q.1.2 = j₀).1⟩
      invFun := fun i => ⟨(i.1, j₀), (⟨i.2, rfl⟩ : i.1 ≠ 0 ∧ j₀ = j₀)⟩
      left_inv := fun q => by
        obtain ⟨⟨a, b⟩, h⟩ := q
        have hb : b = j₀ := (h : a ≠ 0 ∧ b = j₀).2
        subst hb
        rfl
      right_inv := fun i => rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]
  simp

theorem trdeg_CT (j₀ : Fin m) (htr : Algebra.trdeg K Ω = D) :
    Algebra.trdeg K (CT (Ω := Ω) (D := D) j₀) = (Fintype.card (Fin (D + 1) × Fin m) : Cardinal) := by
  classical
  have hle : D ≤ Fintype.card (Fin (D + 1) × Fin m) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    have := j₀.pos
    nlinarith
  rw [← trdeg_add_eq (R := K) (S := Ω) (A := CT (Ω := Ω) (D := D) j₀), htr,
    MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype,
    Fintype.card_subtype_compl, card_Z, ← Nat.cast_add, Nat.add_sub_of_le hle]

theorem isAlgebraic_map_adjoin {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (φ : A →ₐ[R] B) (hφ : Function.Injective φ) (s : Set A) {a : A}
    (h : IsAlgebraic (Algebra.adjoin R s) a) : IsAlgebraic (Algebra.adjoin R (φ '' s)) (φ a) := by
  have hmem : ∀ y : Algebra.adjoin R s, φ y ∈ Algebra.adjoin R (φ '' s) := by
    intro y
    rw [← AlgHom.map_adjoin]
    exact Subalgebra.mem_map.2 ⟨y, y.2, rfl⟩
  let f : Algebra.adjoin R s →+* Algebra.adjoin R (φ '' s) :=
    { toFun := fun y => ⟨φ y, hmem y⟩
      map_one' := by ext; simp
      map_mul' := by intros; ext; simp
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  have hf : Function.Injective f := fun y z hyz => Subtype.ext (hφ (congrArg Subtype.val hyz))
  exact h.ringHom_of_comp_eq (f := f) (g := φ.toRingHom) hf (RingHom.ext fun y => rfl)

theorem alg_CT (x : Fin m → Ω) (j₀ : Fin m)
    (halg : ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (rr x j₀))) ω)
    (hr : ∀ k, IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀)))
      (C (rr x j₀ k) : CT (Ω := Ω) (D := D) j₀)) :
    Algebra.IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀))) (CT (Ω := Ω) (D := D) j₀) := by
  have hC : ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀)))
      (C ω : CT (Ω := Ω) (D := D) j₀) := by
    intro ω
    have h1 := isAlgebraic_map_adjoin (IsScalarTower.toAlgHom K Ω (CT (Ω := Ω) (D := D) j₀)) (C_injective _ _) _
      (halg ω)
    refine IsAlgebraic.adjoin_of_forall_isAlgebraic ?_ h1
    rintro _ ⟨⟨_, ⟨k, rfl⟩, rfl⟩, -⟩
    exact hr k
  constructor
  intro c
  have hc : c ∈ Algebra.adjoin K (Set.range (X : _ → CT (Ω := Ω) (D := D) j₀) ∪ Set.range (C : Ω → CT (Ω := Ω) (D := D) j₀)) := by
    induction c using MvPolynomial.induction_on with
    | C a => exact Algebra.subset_adjoin (Or.inr ⟨a, rfl⟩)
    | add p r hp hr => exact add_mem hp hr
    | mul_X p n hp => exact mul_mem hp (Algebra.subset_adjoin (Or.inl ⟨n, rfl⟩))
  have h0 : IsAlgebraic (Algebra.adjoin K (Set.range (X : _ → CT (Ω := Ω) (D := D) j₀) ∪
      Set.range (C : Ω → CT (Ω := Ω) (D := D) j₀))) c :=
    isAlgebraic_algebraMap (⟨c, hc⟩ : Algebra.adjoin K _)
  refine IsAlgebraic.adjoin_of_forall_isAlgebraic ?_ h0
  rintro y ⟨hy | ⟨ω, rfl⟩, -⟩
  · obtain ⟨q, rfl⟩ := hy
    have hq : (X q : CT (Ω := Ω) (D := D) j₀) ∈ Algebra.adjoin K (Set.range (gs (D := D) x j₀)) :=
      Algebra.subset_adjoin ⟨q.1, by rw [gs, if_neg q.2, xv_of_not q.2]⟩
    exact isAlgebraic_algebraMap (⟨X q, hq⟩ : Algebra.adjoin K _)
  · exact hC ω

theorem gs_indep [CharZero K] (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0)
    (htr : Algebra.trdeg K Ω = D)
    (halg : ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (rr x j₀))) ω) :
    AlgebraicIndependent K (gs (D := D) x j₀) := by
  classical
  by_contra hdep
  have hex : ∃ n, ∃ G : MvPolynomial (Fin (D + 1) × Fin m) K, aeval (gs x j₀) G = 0 ∧ G ≠ 0 ∧
      G.totalDegree = n := by
    rw [algebraicIndependent_iff] at hdep
    push Not at hdep
    obtain ⟨G, h1, h2⟩ := hdep
    exact ⟨_, G, h1, h2, rfl⟩
  obtain ⟨G, hG0, hGne, hGdeg⟩ := Nat.find_spec hex
  have hmin : ∀ H : MvPolynomial (Fin (D + 1) × Fin m) K, H.totalDegree < G.totalDegree →
      aeval (gs x j₀) H = 0 → H = 0 := by
    intro H hH h0
    by_contra hne
    rw [hGdeg] at hH
    exact Nat.find_min hex hH ⟨H, h0, hne, rfl⟩
  have hd : ∀ q : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p},
      ∑ p, aeval (gs x j₀) (pderiv p G) * pderiv q (gs x j₀ p) = 0 := by
    intro q; rw [← pderiv_aeval, hG0, map_zero]
  have hsum : ∀ q : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p},
      ∑ p, aeval (gs x j₀) (pderiv p G) * pderiv q (gs x j₀ p) =
        aeval (gs x j₀) (pderiv q.1 G) -
          if q.1.1 = 0 then 0 else aeval (gs x j₀) (pderiv (q.1.1, j₀) G) * C (rr x j₀ q.1.2) := by
    intro q
    simp_rw [pderiv_gs, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    congr 1
    split_ifs with h0
    · exact Finset.sum_eq_zero fun p _ =>
        if_neg (show ¬ (Zs j₀ p ∧ p.1 = q.1.1) from fun e => e.1.1 (e.2.trans h0))
    · rw [Finset.sum_eq_single (q.1.1, j₀)]
      · exact if_pos (show Zs j₀ (q.1.1, j₀) ∧ (q.1.1, j₀).1 = q.1.1 from ⟨⟨h0, rfl⟩, rfl⟩)
      · intro p _ hp
        exact if_neg (show ¬ (Zs j₀ p ∧ p.1 = q.1.1) from fun e => hp (Prod.ext_iff.mpr ⟨e.2, e.1.2⟩))
      · intro h; exact absurd (Finset.mem_univ _) h
  have hpos : 0 < G.totalDegree := by
    by_contra h
    have h0 : G.totalDegree = 0 := by omega
    rw [totalDegree_eq_zero_iff_eq_C] at h0
    rw [h0, aeval_C] at hG0
    have hc : AddMonoidAlgebra.coeff G 0 = 0 :=
      (algebraMap K (CT (Ω := Ω) (D := D) j₀)).injective (by rw [hG0, map_zero])
    exact hGne (by rw [h0, hc, C_0])
  obtain ⟨p₁, hp₁ne, hp₁lt⟩ := exists_pderiv_ne_zero_lt' G hpos
  have hp₁ : aeval (gs x j₀) (pderiv p₁ G) ≠ 0 := fun h => hp₁ne (hmin _ hp₁lt h)
  have hexi : ∃ i : Fin D, aeval (gs x j₀) (pderiv (i.succ, j₀) G) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hp₁
    by_cases hZ : Zs j₀ p₁
    · obtain ⟨h1, h2⟩ := hZ
      obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr h1
      have e : p₁ = (i.succ, j₀) := Prod.ext_iff.mpr ⟨hi.symm, h2⟩
      rw [e]; exact hall i
    · have h := hd ⟨p₁, hZ⟩
      rw [hsum] at h
      split_ifs at h with h0
      · rwa [sub_zero] at h
      · obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr h0
        simp only at h hi
        rw [← hi, hall i, zero_mul, sub_zero] at h
        exact h
  obtain ⟨i, hi⟩ := hexi
  have hr : ∀ k, IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀)))
      (C (rr x j₀ k) : CT (Ω := Ω) (D := D) j₀) := by
    intro k
    by_cases hk : k = j₀
    · subst hk
      rw [rr, div_self hx₀, C_1]
      exact isAlgebraic_one
    · have hq : ¬ Zs j₀ (i.succ, k) := fun h => hk h.2
      have h := hd ⟨(i.succ, k), hq⟩
      rw [hsum, if_neg (Fin.succ_ne_zero i), sub_eq_zero] at h
      have m1 : aeval (gs x j₀) (pderiv (i.succ, j₀) G) ∈ Algebra.adjoin K (Set.range (gs x j₀)) := by
        rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨_, rfl⟩
      have m2 : aeval (gs x j₀) (pderiv (i.succ, k) G) ∈ Algebra.adjoin K (Set.range (gs x j₀)) := by
        rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨_, rfl⟩
      refine ⟨Polynomial.C ⟨_, m1⟩ * Polynomial.X - Polynomial.C ⟨_, m2⟩, ?_, ?_⟩
      · intro h0
        have h1 := congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f 1) h0
        simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
          Polynomial.coeff_zero, if_pos, one_ne_zero, if_false, sub_zero] at h1
        exact hi (congrArg Subtype.val h1)
      · rw [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X]
        exact sub_eq_zero.mpr h.symm
  have := alg_CT x j₀ halg hr
  have htb : IsTranscendenceBasis K (gs (D := D) x j₀) :=
    Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite K (gs x j₀)
      (by rw [trdeg_CT j₀ htr, Cardinal.mk_fintype])
  exact hdep htb.1

theorem gs_alg [CharZero K] (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0)
    (htr : Algebra.trdeg K Ω = D)
    (halg : ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (rr x j₀))) ω) :
    Algebra.IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀))) (CT (Ω := Ω) (D := D) j₀) :=
  ((gs_indep x j₀ hx₀ htr halg).isTranscendenceBasis_of_trdeg_le_of_finite
    (by rw [trdeg_CT j₀ htr, Cardinal.mk_fintype])).isAlgebraic

theorem halg_of (x : Fin m → Ω) (j₀ : Fin m) (htr : Algebra.trdeg K Ω = D)
    (hbig : Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) = D) :
    ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (rr x j₀))) ω := by
  intro ω
  have hadd := trdeg_add_eq (R := K)
    (S := IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) (A := Ω)
  rw [hbig, htr] at hadd
  have h0 : Algebra.trdeg (IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) Ω = 0 := by
    rcases (Cardinal.add_eq_left_iff).mp hadd with h | h
    · exact absurd ((le_max_left _ _).trans h) (not_le.mpr ((Cardinal.natCast_lt_aleph0 (n := D))))
    · exact h
  have halg : Algebra.IsAlgebraic (IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) Ω := by
    exact trdeg_eq_zero_iff.mp h0
  exact IntermediateField.isAlgebraic_adjoin_iff.mp (halg.isAlgebraic ω)

end Formalism.L2.Pj.GenSect
end
end

noncomputable section

namespace Formalism.L2.Pj.GenSect

open MvPolynomial
open scoped TensorProduct

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}

theorem psi_kt (x : Fin m → Ω) (j₀ : Fin m) (q : KT K D m) :
    psi x j₀ (ktToΩ K Ω D m q) = aeval (gs x j₀) q := by
  show aeval (gs x j₀) (MvPolynomial.map (algebraMap K Ω) q) = aeval (gs x j₀) q
  rw [MvPolynomial.aeval_map_algebraMap]

theorem algKTR_apply (q : KT K D m) :
    algebraMap (KTf K D m) (RS K Ω D m) (algebraMap (KT K D m) (KTf K D m) q) =
      algebraMap (ΩT Ω D m) (RS K Ω D m) (ktToΩ K Ω D m q) := by
  exact IsLocalization.map_eq _ _

def Phi (x : Fin m → Ω) (j₀ : Fin m) (hinj : ∀ q : KT K D m, q ≠ 0 → aeval (gs x j₀) q ≠ 0) :
    RS K Ω D m →+* FractionRing (CT Ω D j₀) :=
  IsLocalization.lift (M := KTS K Ω D m)
    (g := (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))).comp (psi x j₀).toRingHom) (by
      rintro ⟨s, hs⟩
      obtain ⟨q, hq, rfl⟩ := hs
      refine isUnit_iff_ne_zero.mpr ?_
      show algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ (ktToΩ K Ω D m q)) ≠ 0
      rw [psi_kt]
      exact fun h => hinj q (nonZeroDivisors.ne_zero hq)
        ((IsFractionRing.injective (CT Ω D j₀) (FractionRing (CT Ω D j₀))) (h.trans (map_zero _).symm)))

theorem Phi_algebraMap (x : Fin m → Ω) (j₀ : Fin m) (hinj : ∀ q : KT K D m, q ≠ 0 → aeval (gs x j₀) q ≠ 0)
    (a : ΩT Ω D m) :
    Phi x j₀ hinj (algebraMap (ΩT Ω D m) (RS K Ω D m) a) =
      algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ a) :=
  IsLocalization.lift_eq _ _

theorem Phi_mk'_spec (x : Fin m → Ω) (j₀ : Fin m)
    (hinj : ∀ q : KT K D m, q ≠ 0 → aeval (gs x j₀) q ≠ 0) (a : ΩT Ω D m) (y : KTS K Ω D m)
    (v : FractionRing (CT Ω D j₀)) :
    Phi x j₀ hinj (IsLocalization.mk' (RS K Ω D m) a y) = v ↔
      algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ a) =
        algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ y) * v :=
  IsLocalization.lift_mk'_spec _ _ _ _

theorem ker_Phi (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0)
    (hinj : ∀ q : KT K D m, q ≠ 0 → aeval (gs x j₀) q ≠ 0) :
    Is (K := K) x = RingHom.ker (Phi x j₀ hinj) := by
  apply le_antisymm
  · rw [Is, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, Phi_algebraMap, psi_sec x j₀ hx₀ i, map_zero]
  · intro r hr
    rw [RingHom.mem_ker] at hr
    obtain ⟨⟨a, y⟩, rfl⟩ := IsLocalization.mk'_surjective (KTS K Ω D m) r
    dsimp only at hr ⊢
    rw [Phi_mk'_spec, mul_zero, ← map_zero (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))),
      (IsFractionRing.injective (CT Ω D j₀) (FractionRing (CT Ω D j₀))).eq_iff,
      psi_eq_zero_iff x j₀ hx₀] at hr
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    apply Ideal.mul_mem_right
    have hle : Ideal.map (algebraMap (ΩT Ω D m) (RS K Ω D m)) (Ideal.span (Set.range (sec x))) ≤
        Is (K := K) x := by
      rw [Ideal.map_span, Is]
      apply Ideal.span_mono
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    exact hle (Ideal.mem_map_of_mem _ hr)

theorem quotient_generic_section_field [CharZero K] (hfg : (⊤ : IntermediateField K Ω).FG) (htr : Algebra.trdeg K Ω = D)
    (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0)
    (hbig : Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) = D) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra (KTf K D m) E), FiniteDimensional (KTf K D m) E ∧
      Nonempty ((RS K Ω D m ⧸ Is (K := K) x) ≃ₐ[KTf K D m] E) := by
  classical
  have halg := halg_of x j₀ htr hbig
  have hind := gs_indep x j₀ hx₀ htr halg
  have hal := gs_alg x j₀ hx₀ htr halg
  have hI : Function.Injective (aeval (gs x j₀) : KT K D m →ₐ[K] CT Ω D j₀) := hind
  have hinj : ∀ q : KT K D m, q ≠ 0 → aeval (gs x j₀) q ≠ 0 := fun q hq h =>
    hq (hI (h.trans (map_zero _).symm))
  let χ : KT K D m →+* FractionRing (CT Ω D j₀) :=
    (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))).comp
      (aeval (gs x j₀) : KT K D m →ₐ[K] CT Ω D j₀).toRingHom
  have hχ : Function.Injective χ :=
    (IsFractionRing.injective (CT Ω D j₀) (FractionRing (CT Ω D j₀))).comp hI
  let baseAlgebra : Algebra (KT K D m) (FractionRing (CT Ω D j₀)) := χ.toAlgebra
  let baseModule : Module (KT K D m) (FractionRing (CT Ω D j₀)) :=
    @Algebra.toModule _ _ _ _ baseAlgebra
  let baseSMul : SMul (KT K D m) (FractionRing (CT Ω D j₀)) := baseAlgebra.toSMul
  let fractionAlgebra : Algebra (KTf K D m) (FractionRing (CT Ω D j₀)) :=
    (IsFractionRing.lift hχ).toAlgebra
  have tower : IsScalarTower (KT K D m) (KTf K D m) (FractionRing (CT Ω D j₀)) :=
    IsScalarTower.of_algebraMap_eq (S := KTf K D m) (A := FractionRing (CT Ω D j₀))
      fun q => (IsFractionRing.lift_algebraMap (K := KTf K D m) hχ q).symm
  have key : ∀ r : KTf K D m, Phi x j₀ hinj (algebraMap (KTf K D m) (RS K Ω D m) r) =
      IsFractionRing.lift hχ r := by
    have h : (Phi x j₀ hinj).comp (algebraMap (KTf K D m) (RS K Ω D m)) = IsFractionRing.lift hχ := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors (KT K D m)) (RingHom.ext fun q => ?_)
      simp only [RingHom.comp_apply]
      rw [algKTR_apply, Phi_algebraMap, psi_kt, IsFractionRing.lift_algebraMap]
      rfl
    exact fun r => RingHom.congr_fun h r
  let ΦK : RS K Ω D m →ₐ[KTf K D m] FractionRing (CT Ω D j₀) :=
    { Phi x j₀ hinj with commutes' := key }
  have hint : ∀ c : CT Ω D j₀,
      IsIntegral (KTf K D m) (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) c) := by
    intro c
    haveI := hal
    obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := Algebra.adjoin K (Set.range (gs (D := D) x j₀))) c
    let e := hind.aevalEquiv
    have hKT : IsAlgebraic (KT K D m) (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) c) := by
      refine ⟨p.map (e.symm : Algebra.adjoin K (Set.range (gs (D := D) x j₀)) →+* KT K D m), ?_, ?_⟩
      · exact (Polynomial.map_ne_zero_iff e.symm.injective).2 hp0
      · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
        have hcomp : (algebraMap (KT K D m) (FractionRing (CT Ω D j₀))).comp
              (e.symm : Algebra.adjoin K (Set.range (gs (D := D) x j₀)) →+* KT K D m) =
            (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))).comp
              (algebraMap (Algebra.adjoin K (Set.range (gs (D := D) x j₀))) (CT Ω D j₀)) := by
          refine RingHom.ext fun a => ?_
          simp only [RingHom.comp_apply]
          show algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (aeval (gs x j₀) (e.symm a)) = _
          rw [← hind.algebraMap_aevalEquiv, AlgEquiv.apply_symm_apply]
        rw [hcomp, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hp, map_zero]
    exact (hKT.extendScalars (IsFractionRing.injective (KT K D m) (KTf K D m))).isIntegral
  obtain ⟨t, ht⟩ := hfg
  let G : Set (FractionRing (CT Ω D j₀)) :=
    Set.range (fun v => algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (X v)) ∪
      (fun ω => algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (MvPolynomial.C ω)) '' (t : Set Ω)
  haveI : Finite G := ((Set.finite_range _).union (t.finite_toSet.image _)).to_subtype
  let E' := IntermediateField.adjoin (KTf K D m) G
  haveI hfd : FiniteDimensional (KTf K D m) E' := IntermediateField.finiteDimensional_adjoin (by
    rintro _ (⟨v, rfl⟩ | ⟨ω, _, rfl⟩) <;> exact hint _)
  have hK : ∀ k : K, algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))
      (MvPolynomial.C (algebraMap K Ω k)) ∈ E' := by
    intro k
    have e1 : algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (MvPolynomial.C (algebraMap K Ω k)) =
        algebraMap (KTf K D m) (FractionRing (CT Ω D j₀))
          (algebraMap (KT K D m) (KTf K D m) (MvPolynomial.C k)) := by
      rw [← IsScalarTower.algebraMap_apply]
      show _ = algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (aeval (gs x j₀) (MvPolynomial.C k))
      rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_apply]
    rw [e1]
    exact E'.algebraMap_mem _
  have hΩ : ∀ ω : Ω, algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (MvPolynomial.C ω) ∈ E' := by
    let θ : Ω →+* FractionRing (CT Ω D j₀) :=
      (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))).comp MvPolynomial.C
    let Si : IntermediateField K Ω := Subfield.toIntermediateField (E'.toSubfield.comap θ) (fun k => hK k)
    have hle : IntermediateField.adjoin K (t : Set Ω) ≤ Si := by
      rw [IntermediateField.adjoin_le_iff]
      intro ω hω
      exact IntermediateField.subset_adjoin (KTf K D m) G (Or.inr ⟨ω, hω, rfl⟩)
    intro ω
    have hω : ω ∈ IntermediateField.adjoin K (t : Set Ω) := by
      rw [ht]
      exact IntermediateField.mem_top
    exact hle hω
  have hmemC : ∀ c : CT Ω D j₀, algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) c ∈ E' := by
    intro c
    apply MvPolynomial.induction_on c
    · intro ω
      exact hΩ ω
    · intro p q hp hq
      rw [map_add (f := _)]
      exact add_mem hp hq
    · intro p v hp
      rw [map_mul]
      exact mul_mem hp (IntermediateField.subset_adjoin (KTf K D m) G (Or.inl ⟨v, rfl⟩))
  have hrange : ∀ r : RS K Ω D m, Phi x j₀ hinj r ∈ E' := by
    intro r
    obtain ⟨⟨a, y⟩, rfl⟩ := IsLocalization.mk'_surjective (KTS K Ω D m) r
    dsimp only
    rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul, Phi_algebraMap]
    refine mul_mem (hmemC _) ?_
    have hy : algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ y) ≠ 0 := by
      obtain ⟨q, hq, hqy⟩ := y.2
      rw [← hqy, psi_kt]
      intro h
      exact hinj q (nonZeroDivisors.ne_zero hq)
        ((IsFractionRing.injective (CT Ω D j₀) (FractionRing (CT Ω D j₀))) (h.trans (map_zero _).symm))
    have h1 : Phi x j₀ hinj (IsLocalization.mk' (RS K Ω D m) (1 : ΩT Ω D m) y) =
        (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ y))⁻¹ := by
      rw [Phi_mk'_spec, map_one, map_one, mul_inv_cancel₀ hy]
    rw [h1]
    exact inv_mem (hmemC _)
  let S := ΦK.range
  let L : S →ₗ[KTf K D m] E' :=
    { toFun := fun s => ⟨s.1, by
        obtain ⟨r, hr⟩ := (AlgHom.mem_range ΦK).1 s.2
        rw [← hr]
        exact hrange r⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  haveI : FiniteDimensional (KTf K D m) S :=
    FiniteDimensional.of_injective L (by
      intro a b h
      have h' := congrArg (fun e : E' => (e : FractionRing (CT Ω D j₀))) h
      exact Subtype.ext h')
  have hSf : IsField S := IsField.of_isDomain_of_finite (KTf K D m) S
  let E := S.toIntermediateField' hSf
  let g : RS K Ω D m →ₐ[KTf K D m] E :=
    { toFun := fun r => ⟨ΦK r, ΦK.mem_range_self r⟩
      map_one' := Subtype.ext (map_one ΦK)
      map_mul' := fun a b => Subtype.ext (map_mul ΦK a b)
      map_zero' := Subtype.ext (map_zero ΦK)
      map_add' := fun a b => Subtype.ext (map_add ΦK a b)
      commutes' := fun r => Subtype.ext (ΦK.commutes r) }
  have hg : Function.Surjective g := by
    rintro ⟨v, hv⟩
    obtain ⟨r, rfl⟩ := (AlgHom.mem_range ΦK).1 (show v ∈ S from hv)
    exact ⟨r, rfl⟩
  have hker : RingHom.ker g = Is (K := K) x := by
    rw [ker_Phi x j₀ hx₀ hinj]
    ext r
    simp only [RingHom.mem_ker]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  refine ⟨E, inferInstance, inferInstance, ?_, ⟨(Ideal.quotientEquivAlgOfEq (KTf K D m) hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hg)⟩⟩
  exact FiniteDimensional.of_injective
    ({ toFun := fun e => (⟨e.1, e.2⟩ : S), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
      E →ₗ[KTf K D m] S)
    (by
      intro a b h
      have h' := congrArg (fun e : S => (e : FractionRing (CT Ω D j₀))) h
      exact Subtype.ext h')

end Formalism.L2.Pj.GenSect
