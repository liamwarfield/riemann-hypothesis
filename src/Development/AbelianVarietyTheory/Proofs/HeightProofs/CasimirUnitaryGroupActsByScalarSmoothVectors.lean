module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedNonsplitExistsConjInvolutionUniformise

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CasimirDifferenceOperatorEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.SignatureLieSetExpandOrthonormalBases
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.SignatureLieSetExpandOrthonormalBases
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined

noncomputable section
namespace GlobalTheory.TypeSum.CasBasis.Expand
variable {n : ℕ}

theorem sum_get {α M : Type*} [AddCommMonoid M] (l : List α) (f : α → M) :
    ∑ i : Fin l.length, f (l.get i) = (l.map f).sum := by
  rw [Fin.sum_univ_def]
  conv_rhs => rw [← List.map_get_finRange l]
  rw [List.map_map]
  rfl

theorem trace_mul_unitE (U : Mx n) (a b : Fin n) : trace (U * unitE a b) = U b a := by
  simpa [unitE] using (Matrix.trace_mul_single U a b 1)

theorem sum_flatMap {α M : Type*} [AddCommMonoid M] (l : List α) (f : α → List M) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem filter_split {α M : Type*} [AddCommMonoid M] (l : List α) (c d : α → Bool) (F : α → M) :
    ((l.filter fun p => c p && (d p == true)).map F).sum + ((l.filter fun p => c p && (d p == false)).map F).sum =
      (l.map fun p => if c p then F p else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    cases hc : c a <;> cases hd : d a <;> simp [← ih] <;> abel

theorem sum_map_neg' {α M : Type*} [AddCommGroup M] (l : List α) (f : α → M) :
    (l.map fun x => -f x).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, neg_add]

theorem sum_product_list {M : Type*} [AddCommMonoid M] (G : Fin n × Fin n → M) :
    ((List.product (List.finRange n) (List.finRange n)).map G).sum = ∑ a, ∑ b, G (a, b) := by
  simp [List.product, List.map_flatMap, sum_flatMap, List.map_map, Fin.sum_univ_def, Function.comp_def]

variable {ε : Fin n → Bool}

theorem diag_re {U : Mx n} (hU : U ∈ lieSet ε) (a : Fin n) : (U a a).re = 0 := by
  have h := (mem_lieSet_iff_entry.mp hU) a a
  rcases ha : ε a <;> simp [ha] at h <;> have h2 := congrArg Complex.re h <;> simp at h2 <;> linarith

theorem entry_same {U : Mx n} (hU : U ∈ lieSet ε) {a b : Fin n} (h : ε a = ε b) : U b a = -star (U a b) := by
  have h1 := (mem_lieSet_iff_entry.mp hU) a b
  rw [h] at h1
  have : (starRingEnd ℂ) (U b a) = -U a b := by
    rcases hb : ε b <;> simp [hb] at h1 <;> first | linear_combination h1 | linear_combination -h1
  have h3 := congrArg (starRingEnd ℂ) this
  simp at h3
  simpa [Complex.star_def] using h3

theorem entry_opp {U : Mx n} (hU : U ∈ lieSet ε) {a b : Fin n} (h : ε a ≠ ε b) : U b a = star (U a b) := by
  have h1 := (mem_lieSet_iff_entry.mp hU) a b
  have : star (U b a) = U a b := by
    rcases ha : ε a <;> rcases hb : ε b <;> simp_all <;> first | linear_combination h1 | linear_combination -h1
  have h3 := congrArg star this
  simpa using h3

abbrev tm (U X : Mx n) : Mx n := (trace (U * X)).re • X

theorem tm_diag {U : Mx n} (hU : U ∈ lieSet ε) (a : Fin n) :
    tm U (Complex.I • unitE a a) = -(U a a • unitE a a) := by
  have h := diag_re hU a
  simp only [tm, Matrix.mul_smul, trace_smul, trace_mul_unitE, ← Complex.coe_smul, smul_smul, ← neg_smul]
  congr 1
  apply Complex.ext <;> simp [h]

theorem tm_same {U : Mx n} (hU : U ∈ lieSet ε) {a b : Fin n} (h : ε a = ε b) :
    tm U (invSqrtTwo • (unitE a b - unitE b a)) + tm U ((invSqrtTwo * Complex.I) • (unitE a b + unitE b a)) =
      -(U a b • unitE a b + U b a • unitE b a) := by
  have hba := entry_same hU h
  simp only [tm, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_add, trace_smul, trace_sub, trace_add, trace_mul_unitE,
    ← Complex.coe_smul, hba]
  match_scalars <;> simp only [smul_eq_mul] <;> apply Complex.ext <;>
    simp [invSqrtTwo, Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im] <;> field_simp
  all_goals (try rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]) <;> ring

theorem tm_opp {U : Mx n} (hU : U ∈ lieSet ε) {a b : Fin n} (h : ε a ≠ ε b) :
    tm U (invSqrtTwo • (unitE a b + unitE b a)) + tm U ((invSqrtTwo * Complex.I) • (unitE a b - unitE b a)) =
      U a b • unitE a b + U b a • unitE b a := by
  have hba := entry_opp hU h
  simp only [tm, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_add, trace_smul, trace_sub, trace_add, trace_mul_unitE,
    ← Complex.coe_smul, hba]
  match_scalars <;> simp only [smul_eq_mul] <;> apply Complex.ext <;>
    simp [invSqrtTwo, Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im] <;> field_simp
  all_goals (try rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]) <;> ring

abbrev pairTerm (U : Mx n) (p : Fin n × Fin n) : Mx n := U p.1 p.2 • unitE p.1 p.2 + U p.2 p.1 • unitE p.2 p.1

theorem decomp (U : Mx n) :
    U = ∑ a, U a a • unitE a a + ∑ a, ∑ b, if a < b then pairTerm U (a, b) else 0 := by
  ext r t
  simp only [Matrix.add_apply, Matrix.sum_apply, apply_ite (fun M : Mx n => M r t), pairTerm, Matrix.smul_apply,
    single_apply, smul_eq_mul, Matrix.zero_apply]
  simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']
  rcases lt_trichotomy r t with h | rfl | h
  · rw [Finset.sum_eq_single r (fun x _ hx => Finset.sum_eq_zero fun y _ => by split_ifs <;> grind) (by simp),
      Finset.sum_eq_single t (fun y _ hy => by split_ifs <;> grind) (by simp)]
    simp [h, h.ne, not_lt.mpr h.le]
  · simp only [lt_self_iff_false, if_true]
    rw [Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => by split_ifs <;> grind]
    simp
  · rw [Finset.sum_eq_single t (fun x _ hx => Finset.sum_eq_zero fun y _ => by split_ifs <;> grind) (by simp),
      Finset.sum_eq_single r (fun y _ hy => by split_ifs <;> grind) (by simp)]
    simp [h, h.ne, h.ne', not_lt.mpr h.le]

theorem pairs_split (U : Mx n) :
    ((pairs ε true).map (pairTerm U)).sum + ((pairs ε false).map (pairTerm U)).sum =
      ∑ a, ∑ b, if a < b then pairTerm U (a, b) else 0 :=
  (filter_split _ (fun p : Fin n × Fin n => decide (p.1 < p.2)) (fun p : Fin n × Fin n => ε p.1 == ε p.2)
    (pairTerm U)).trans (by rw [sum_product_list]; simp)

theorem sum_k {U : Mx n} (hU : U ∈ lieSet ε) :
    ∑ i, tm U (kB ε i) = -(∑ a, U a a • unitE a a + ((pairs ε true).map (pairTerm U)).sum) := by
  rw [show (∑ i, tm U (kB ε i)) = ((kList ε).map (tm U)).sum from sum_get _ _]
  simp only [kList, List.map_append, List.sum_append, List.map_map, List.map_flatMap, sum_flatMap, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero, Function.comp_def, tm_diag hU]
  rw [List.map_congr_left (g := fun p => -pairTerm U p) (fun p hp => by
    have hs : ε p.1 = ε p.2 := by
      simp [pairs] at hp
      exact hp.2.2
    exact tm_same hU hs), Fin.sum_univ_def, sum_map_neg', sum_map_neg', neg_add]

theorem sum_p {U : Mx n} (hU : U ∈ lieSet ε) :
    ∑ b, tm U (pB ε b) = ((pairs ε false).map (pairTerm U)).sum := by
  rw [show (∑ b, tm U (pB ε b)) = ((pList ε).map (tm U)).sum from sum_get _ _]
  simp only [pList, List.map_flatMap, sum_flatMap, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [List.map_congr_left (g := pairTerm U) (fun p hp => by
    have hs : ε p.1 ≠ ε p.2 := by
      simp [pairs] at hp
      exact hp.2.2
    exact tm_opp hU hs)]

end GlobalTheory.TypeSum.CasBasis.Expand

namespace GlobalTheory.TypeSum.CasBasis


open Expand in
theorem lieSet_expand_bases : ∀ (n : ℕ) (ε : Fin n → Bool), ∀ U ∈ lieSet ε,
    U = ∑ b, (trace (U * pB ε b)).re • pB ε b - ∑ i, (trace (U * kB ε i)).re • kB ε i := by
  intro n ε U hU
  have h1 := sum_p hU
  have h2 := sum_k hU
  simp only [tm] at h1 h2
  rw [h1, h2, sub_neg_eq_add]
  conv_lhs => rw [decomp U]
  rw [← pairs_split (ε := ε)]
  abel

end GlobalTheory.TypeSum.CasBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.SignatureLieSetExpandOrthonormalBasesStatement
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.signature_lieSet_expand_orthonormal_bases : ∀ (n : ℕ) (ε : Fin n → Bool), ∀ U ∈ lieSet ε, U = ∑ b, (trace (U * pB ε b)).re • pB ε b - ∑ i, (trace (U * kB ε i)).re • kB ε i := by
  first | exact @GlobalTheory.TypeSum.CasBasis.lieSet_expand_bases | exact GlobalTheory.TypeSum.CasBasis.lieSet_expand_bases | (intros; apply GlobalTheory.TypeSum.CasBasis.lieSet_expand_bases <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ReTraceHermitianOrthonormalBasisMulEqIte
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ReTraceHermitianOrthonormalBasisMulEqIte
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined

noncomputable section

namespace GlobalTheory.TypeSum.CasBasis.PB

variable {n : ℕ}

theorem tr_unit (a b c d : Fin n) :
    trace (unitE a b * unitE c d) = if b = c ∧ d = a then 1 else 0 := by
  by_cases hbc : b = c
  · subst hbc
    rw [unitE, unitE, Matrix.single_mul_single_same, one_mul]
    by_cases hda : d = a
    · subst hda; simp [Matrix.trace_single_eq_same]
    · rw [Matrix.trace_single_eq_of_ne (h := Ne.symm hda)]; simp [hda]
  · rw [unitE, unitE, Matrix.single_mul_single_of_ne _ _ _ _ hbc]; simp [hbc]

theorem sq_inv : invSqrtTwo * invSqrtTwo = (1 / 2 : ℂ) := by
  rw [invSqrtTwo, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  push_cast; ring

def B (X Y : Mx n) : ℝ := (trace (X * Y)).re

theorem B_comm (X Y : Mx n) : B X Y = B Y X := by
  simp only [B, Matrix.trace_mul_comm X Y]

def f (p : Fin n × Fin n) : List (Mx n) :=
  [invSqrtTwo • (unitE p.1 p.2 + unitE p.2 p.1), (invSqrtTwo * Complex.I) • (unitE p.1 p.2 - unitE p.2 p.1)]

theorem pList_eq (ε : Fin n → Bool) : pList ε = (pairs ε false).flatMap f := rfl

theorem mem_pairs' {ε : Fin n → Bool} {p : Fin n × Fin n} (h : p ∈ pairs ε false) : p.1 < p.2 := by
  simp only [pairs, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2.1

theorem nodup_pairs (ε : Fin n → Bool) : (pairs ε false).Nodup :=
  (List.Nodup.product (List.nodup_finRange n) (List.nodup_finRange n)).filter _

theorem norm_one {a b : Fin n} (hab : a < b) : ∀ X ∈ f (a, b), B X X = 1 := by
  have h1 : a ≠ b := hab.ne
  have h2 : b ≠ a := hab.ne'
  intro X hX
  simp only [f, List.mem_cons, List.not_mem_nil, or_false] at hX
  rcases hX with rfl | rfl
  · simp only [B, smul_mul_smul_comm, Matrix.trace_smul, mul_add, add_mul, Matrix.trace_add, tr_unit,
      h1, h2, and_self, and_false, false_and, if_true, if_false, sq_inv, smul_eq_mul]
    norm_num
  · simp only [B, smul_mul_smul_comm, Matrix.trace_smul, mul_sub, sub_mul, Matrix.trace_sub, tr_unit,
      h1, h2, and_self, and_false, false_and, if_true, if_false, smul_eq_mul]
    have : invSqrtTwo * Complex.I * (invSqrtTwo * Complex.I) = -(1 / 2 : ℂ) := by
      rw [show invSqrtTwo * Complex.I * (invSqrtTwo * Complex.I) = invSqrtTwo * invSqrtTwo * (Complex.I * Complex.I) by ring,
        sq_inv, Complex.I_mul_I]; ring
    rw [this]; norm_num

theorem within {a b : Fin n} (hab : a < b) : (f (a, b)).Pairwise fun X Y => B X Y = 0 := by
  have h1 : a ≠ b := hab.ne
  have h2 : b ≠ a := hab.ne'
  simp only [f, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
    List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true]
  simp only [B, smul_mul_smul_comm, Matrix.trace_smul, mul_sub, add_mul, Matrix.trace_sub, Matrix.trace_add, tr_unit,
    h1, h2, and_self, and_false, false_and, if_true, if_false, smul_eq_mul]
  simp

theorem across {a b c d : Fin n} (hab : a < b) (hcd : c < d) (hne : (a, b) ≠ (c, d)) :
    ∀ X ∈ f (a, b), ∀ Y ∈ f (c, d), B X Y = 0 := by
  have e1 : ¬ (b = c ∧ d = a) := by rintro ⟨rfl, rfl⟩; exact lt_asymm hab hcd
  have e2 : ¬ (b = d ∧ c = a) := by rintro ⟨rfl, rfl⟩; exact hne rfl
  have e3 : ¬ (a = c ∧ d = b) := by rintro ⟨rfl, rfl⟩; exact hne rfl
  have e4 : ¬ (a = d ∧ c = b) := by rintro ⟨rfl, rfl⟩; exact lt_asymm hab hcd
  intro X hX Y hY
  simp only [f, List.mem_cons, List.not_mem_nil, or_false] at hX hY
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;>
  simp only [B, smul_mul_smul_comm, Matrix.trace_smul, mul_sub, sub_mul, mul_add, add_mul, Matrix.trace_sub,
    Matrix.trace_add, tr_unit, e1, e2, e3, e4, if_false, sub_zero, add_zero, smul_zero, Complex.zero_re]

theorem pairwise_pList (ε : Fin n → Bool) : (pList ε).Pairwise fun X Y => B X Y = 0 := by
  rw [pList_eq, List.pairwise_flatMap]
  refine ⟨fun p hp => ?_, ?_⟩
  · obtain ⟨a, b⟩ := p
    exact within (mem_pairs' hp)
  · refine (nodup_pairs ε).imp_of_mem fun {p q} hp hq hne => ?_
    obtain ⟨a, b⟩ := p
    obtain ⟨c, d⟩ := q
    exact across (mem_pairs' hp) (mem_pairs' hq) hne

theorem norm_pList (ε : Fin n → Bool) : ∀ X ∈ pList ε, B X X = 1 := by
  intro X hX
  rw [pList_eq, List.mem_flatMap] at hX
  obtain ⟨⟨a, b⟩, hp, hX⟩ := hX
  exact norm_one (mem_pairs' hp) X hX

end GlobalTheory.TypeSum.CasBasis.PB

namespace GlobalTheory.TypeSum.CasBasis

theorem pB_orthonormal : ∀ (n : ℕ) (ε : Fin n → Bool) (a b : Fin (pList ε).length),
    (trace (pB ε a * pB ε b)).re = if a = b then 1 else 0 := by
  intro n ε a b
  have hpw := List.pairwise_iff_get.1 (PB.pairwise_pList ε)
  show PB.B (pB ε a) (pB ε b) = _
  rcases lt_trichotomy a b with h | rfl | h
  · rw [if_neg h.ne]; exact hpw a b h
  · rw [if_pos rfl]; exact PB.norm_pList ε _ (List.get_mem _ _)
  · rw [if_neg h.ne', PB.B_comm]; exact hpw b a h

end GlobalTheory.TypeSum.CasBasis

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ReTraceHermitianOrthonormalBasisMulEqIteStatement
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.re_trace_hermitianOrthonormalBasis_mul_eq_ite : ∀ (n : ℕ) (ε : Fin n → Bool) (a b : Fin (pList ε).length), (trace (pB ε a * pB ε b)).re = if a = b then 1 else 0 := by
  first | exact @GlobalTheory.TypeSum.CasBasis.pB_orthonormal | exact GlobalTheory.TypeSum.CasBasis.pB_orthonormal | (intros; apply GlobalTheory.TypeSum.CasBasis.pB_orthonormal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ReTraceSkewHermitianMulHermitianOrthonormalBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ReTraceSkewHermitianMulHermitianOrthonormalBasis
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined

namespace GlobalTheory.TypeSum.CasBasis

theorem unitE_apply_eq_zero_of_sign {n : ℕ} {ε : Fin n → Bool} {i j a b : Fin n}
    (h : (ε i = ε j) ≠ (ε a = ε b)) : unitE i j a b = 0 := by
  rw [unitE, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact h rfl

theorem kList_entry_zero {n : ℕ} {ε : Fin n → Bool} {X : Mx n} (hX : X ∈ kList ε) {a b : Fin n}
    (hab : ε a ≠ ε b) : X a b = 0 := by
  unfold kList at hX
  rcases List.mem_append.1 hX with h | h
  · obtain ⟨c, -, rfl⟩ := List.mem_map.1 h
    have h1 : unitE c c a b = 0 :=
      unitE_apply_eq_zero_of_sign (ε := ε) (by simp [hab])
    simp only [Matrix.smul_apply, h1, smul_zero]
  · obtain ⟨p, hp, hX⟩ := List.mem_flatMap.1 h
    have hpe : ε p.1 = ε p.2 := by
      have := (List.mem_filter.1 hp).2
      simp at this
      exact this.2
    have h1 : unitE p.1 p.2 a b = 0 :=
      unitE_apply_eq_zero_of_sign (ε := ε) (by simp [hab, hpe])
    have h2 : unitE p.2 p.1 a b = 0 :=
      unitE_apply_eq_zero_of_sign (ε := ε) (by simp [hab, hpe])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl <;>
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, h1, h2, sub_zero, add_zero, smul_zero]

theorem pList_entry_zero {n : ℕ} {ε : Fin n → Bool} {Y : Mx n} (hY : Y ∈ pList ε) {a b : Fin n}
    (hab : ε a = ε b) : Y a b = 0 := by
  unfold pList at hY
  obtain ⟨p, hp, hY⟩ := List.mem_flatMap.1 hY
  have hpe : ε p.1 ≠ ε p.2 := by
    have := (List.mem_filter.1 hp).2
    simp at this
    exact this.2
  have h1 : unitE p.1 p.2 a b = 0 :=
    unitE_apply_eq_zero_of_sign (ε := ε) (by simp [hab, hpe])
  have h2 : unitE p.2 p.1 a b = 0 :=
    unitE_apply_eq_zero_of_sign (ε := ε) (by simp [hab, Ne.symm hpe])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hY
  rcases hY with rfl | rfl <;>
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, h1, h2, sub_zero, add_zero, smul_zero]

theorem re_trace_kB_mul_pB : ∀ (n : ℕ) (ε : Fin n → Bool) (i : Fin (kList ε).length) (b : Fin (pList ε).length),
    (trace (kB ε i * pB ε b)).re = 0 := by
  intro n ε i b
  have hX : kB ε i ∈ kList ε := List.get_mem _ _
  have hY : pB ε b ∈ pList ε := List.get_mem _ _
  have : trace (kB ε i * pB ε b) = 0 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => ?_
    by_cases h : ε a = ε c
    · rw [pList_entry_zero hY h.symm, mul_zero]
    · rw [kList_entry_zero hX h, zero_mul]
  rw [this, Complex.zero_re]

end GlobalTheory.TypeSum.CasBasis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ReTraceSkewHermitianMulHermitianOrthonormalBasisStatement
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.re_trace_skewHermitian_mul_hermitianOrthonormalBasis : ∀ (n : ℕ) (ε : Fin n → Bool) (i : Fin (kList ε).length) (b : Fin (pList ε).length), (trace (kB ε i * pB ε b)).re = 0 := by
  first | exact @GlobalTheory.TypeSum.CasBasis.re_trace_kB_mul_pB | exact GlobalTheory.TypeSum.CasBasis.re_trace_kB_mul_pB | (intros; apply GlobalTheory.TypeSum.CasBasis.re_trace_kB_mul_pB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.SkewHermitianOrthonormalBasisTraceOrthonormal
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.SkewHermitianOrthonormalBasisTraceOrthonormal
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined

noncomputable section

namespace GlobalTheory.TypeSum.CasBasis.KOrth

theorem trE {n : ℕ} (a b c d : Fin n) : trace (unitE a b * unitE c d) = if b = c ∧ a = d then 1 else 0 := by
  simp only [unitE]
  by_cases h : b = c
  · subst h; rw [Matrix.single_mul_single_same]
    by_cases h2 : a = d
    · subst h2; simp
    · simp [h2, Matrix.trace_single_eq_of_ne _ _ _ h2]
  · rw [Matrix.single_mul_single_of_ne _ _ _ _ h]; simp [h]

theorem s2 : invSqrtTwo * invSqrtTwo = 1/2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

theorem mem_pairs_lt {n : ℕ} {ε : Fin n → Bool} {s : Bool} {p : Fin n × Fin n} (h : p ∈ pairs ε s) : p.1 < p.2 := by
  simp only [pairs, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2.1

theorem nodup_pairs {n : ℕ} (ε : Fin n → Bool) (s : Bool) : (pairs ε s).Nodup :=
  ((List.nodup_finRange n).product (List.nodup_finRange n)).filter _

section
variable {n : ℕ}

theorem d_self (a : Fin n) : trace ((Complex.I • unitE a a) * (Complex.I • unitE a a)) = -1 := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, trE]; simp

theorem d_ne {a b : Fin n} (h : a ≠ b) : trace ((Complex.I • unitE a a) * (Complex.I • unitE b b)) = 0 := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, trE]; simp [h]

theorem trace_casimirAntisymPair_mul_self {a b : Fin n} (h : a < b) :
    trace ((invSqrtTwo • (unitE a b - unitE b a)) * (invSqrtTwo • (unitE a b - unitE b a))) = -1 := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.trace_sub, trE]
  simp only [h.ne, h.ne', and_self, and_false, false_and, if_true, if_false, smul_eq_mul]
  linear_combination (-2 : ℂ) * s2

theorem trace_casimirSymPairI_mul_self {a b : Fin n} (h : a < b) :
    trace (((invSqrtTwo * Complex.I) • (unitE a b + unitE b a)) * ((invSqrtTwo * Complex.I) • (unitE a b + unitE b a))) = -1 := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.add_mul,
    Matrix.trace_add, trE]
  simp only [h.ne, h.ne', and_self, and_false, false_and, if_true, if_false, smul_eq_mul]
  linear_combination (2 * invSqrtTwo * invSqrtTwo) * Complex.I_mul_I - (2 : ℂ) * s2

theorem p12 {a b : Fin n} (h : a < b) :
    trace ((invSqrtTwo • (unitE a b - unitE b a)) * ((invSqrtTwo * Complex.I) • (unitE a b + unitE b a))) = 0 := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.sub_mul,
    Matrix.trace_add, Matrix.trace_sub, trE]
  simp only [h.ne, h.ne', and_self, and_false, false_and, if_true, if_false, smul_eq_mul]
  ring

theorem dp1 (a : Fin n) {b c : Fin n} (h : b < c) :
    trace ((Complex.I • unitE a a) * (invSqrtTwo • (unitE b c - unitE c b))) = 0 := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sub, Matrix.trace_sub, trE]
  have h1 : ¬ (a = b ∧ a = c) := fun ⟨h1, h2⟩ => h.ne (h1 ▸ h2)
  have h2 : ¬ (a = c ∧ a = b) := fun ⟨h1, h2⟩ => h.ne (h2 ▸ h1)
  simp [h1, h2]

theorem dp2 (a : Fin n) {b c : Fin n} (h : b < c) :
    trace ((Complex.I • unitE a a) * ((invSqrtTwo * Complex.I) • (unitE b c + unitE c b))) = 0 := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.trace_add, trE]
  have h1 : ¬ (a = b ∧ a = c) := fun ⟨h1, h2⟩ => h.ne (h1 ▸ h2)
  have h2 : ¬ (a = c ∧ a = b) := fun ⟨h1, h2⟩ => h.ne (h2 ▸ h1)
  simp [h1, h2]

theorem pq_facts {p q : Fin n × Fin n} (hp : p.1 < p.2) (hq : q.1 < q.2) (hpq : p ≠ q) :
    ¬ (p.2 = q.1 ∧ p.1 = q.2) ∧ ¬ (p.2 = q.2 ∧ p.1 = q.1) ∧ ¬ (p.1 = q.1 ∧ p.2 = q.2) ∧
      ¬ (p.1 = q.2 ∧ p.2 = q.1) := by
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun ⟨h1, h2⟩ => hpq (Prod.ext h2 h1), fun ⟨h1, h2⟩ => hpq (Prod.ext h1 h2),
    fun ⟨h1, h2⟩ => ?_⟩
  · have := hp.trans_eq h1; have := hq.trans_eq h2.symm; exact absurd (hp.trans (h1 ▸ h2 ▸ hq)) (lt_irrefl _)
  · exact absurd (hp.trans (h2 ▸ h1 ▸ hq)) (lt_irrefl _)

end
end GlobalTheory.TypeSum.CasBasis.KOrth

namespace GlobalTheory.TypeSum.CasBasis.KOrth
variable {n : ℕ}

theorem pq_zero {p q : Fin n × Fin n} (hp : p.1 < p.2) (hq : q.1 < q.2) (hpq : p ≠ q) :
    ∀ X ∈ [invSqrtTwo • (unitE p.1 p.2 - unitE p.2 p.1), (invSqrtTwo * Complex.I) • (unitE p.1 p.2 + unitE p.2 p.1)],
    ∀ Y ∈ [invSqrtTwo • (unitE q.1 q.2 - unitE q.2 q.1), (invSqrtTwo * Complex.I) • (unitE q.1 q.2 + unitE q.2 q.1)],
    trace (X * Y) = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := pq_facts hp hq hpq
  have e1 : trace (unitE p.1 p.2 * unitE q.1 q.2) = 0 := by rw [trE, if_neg h1]
  have e2 : trace (unitE p.1 p.2 * unitE q.2 q.1) = 0 := by rw [trE, if_neg h2]
  have e3 : trace (unitE p.2 p.1 * unitE q.1 q.2) = 0 := by rw [trE, if_neg h3]
  have e4 : trace (unitE p.2 p.1 * unitE q.2 q.1) = 0 := by rw [trE, if_neg h4]
  intro X hX Y hY
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hX hY
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;>
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_add, Matrix.trace_sub, e1, e2, e3, e4] <;> simp

theorem kList_self (ε : Fin n → Bool) : ∀ X ∈ kList ε, trace (X * X) = -1 := by
  intro X hX
  simp only [kList, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at hX
  rcases hX with ⟨a, -, rfl⟩ | ⟨p, hp, rfl | rfl⟩
  · exact d_self a
  · exact trace_casimirAntisymPair_mul_self (mem_pairs_lt hp)
  · exact trace_casimirSymPairI_mul_self (mem_pairs_lt hp)

theorem kList_pairwise (ε : Fin n → Bool) : (kList ε).Pairwise (fun X Y => trace (X * Y) = 0) := by
  rw [kList, List.pairwise_append, List.pairwise_map, List.pairwise_flatMap]
  refine ⟨(List.nodup_finRange n).imp fun h => d_ne h, ⟨fun p hp => ?_, ?_⟩, ?_⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true, List.forall_mem_nil]
    exact ⟨p12 (mem_pairs_lt hp), fun _ h => h.elim⟩
  · exact (nodup_pairs ε true).imp_of_mem fun hp hq hpq => pq_zero (mem_pairs_lt hp) (mem_pairs_lt hq) hpq
  · intro X hX Y hY
    simp only [List.mem_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hX hY
    obtain ⟨a, -, rfl⟩ := hX
    obtain ⟨p, hp, rfl | rfl⟩ := hY
    · exact dp1 a (mem_pairs_lt hp)
    · exact dp2 a (mem_pairs_lt hp)

end GlobalTheory.TypeSum.CasBasis.KOrth

namespace GlobalTheory.TypeSum.CasBasis

theorem kB_trace_orthonormal : ∀ (n : ℕ) (ε : Fin n → Bool) (i j : Fin (kList ε).length),
    (trace (kB ε i * kB ε j)).re = if i = j then -1 else 0 := by
  intro n ε i j
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, kB, KOrth.kList_self ε _ (List.get_mem _ _)]; simp
  · rw [if_neg hij]
    have hP := List.pairwise_iff_get.mp (KOrth.kList_pairwise ε)
    rcases lt_or_gt_of_ne hij with h | h
    · rw [kB, hP i j h]; simp
    · rw [kB, Matrix.trace_mul_comm, hP j i h]; simp

end GlobalTheory.TypeSum.CasBasis

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.SkewHermitianOrthonormalBasisTraceOrthonormalStatement
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewHermitianOrthonormalBasis_trace_orthonormal : ∀ (n : ℕ) (ε : Fin n → Bool) (i j : Fin (kList ε).length), (trace (kB ε i * kB ε j)).re = if i = j then -1 else 0 := by
  first | exact @GlobalTheory.TypeSum.CasBasis.kB_trace_orthonormal | exact GlobalTheory.TypeSum.CasBasis.kB_trace_orthonormal | (intros; apply GlobalTheory.TypeSum.CasBasis.kB_trace_orthonormal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CasimirDifferenceOperatorEquivariant
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum.CasEquiv

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

abbrev trF (U V : Mx n) : ℝ := (trace (U * V)).re

theorem trF_sum_left {ι : Type} (s : Finset ι) (r : ι → ℝ) (Z : ι → Mx n) (V : Mx n) :
    trF (∑ c ∈ s, r c • Z c) V = ∑ c ∈ s, r c * trF (Z c) V := by
  simp [trF, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]

theorem trF_comm (U V : Mx n) : trF U V = trF V U := by
  simp only [trF, Matrix.trace_mul_comm U V]

theorem dRep_finsum (hσ : IsURepOn (UJset ε) σ) {Z : Mx n} (hZ : Z ∈ lieSet ε) {ι : Type} (s : Finset ι)
    (w : ι → H) (hw : ∀ i, Sm ε σ (w i)) : dRep σ Z (∑ i ∈ s, w i) = ∑ i ∈ s, dRep σ Z (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := Dw_smul hσ (l := [Z]) (by simp [hZ]) (0 : ℂ) (x := 0) ((smooth (Jm ε) σ).zero_mem)
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    exact Dw_add hσ (l := [Z]) (by simp [hZ]) (hw _) ((smooth (Jm ε) σ).sum_mem fun i _ => hw i)

variable [CompleteSpace H]

theorem dRep_sum_fin (h : Std ε σ) {ι : Type} [Fintype ι] {Z : ι → Mx n} (hZ : ∀ c, Z c ∈ lieSet ε) {w : H}
    (hw : Sm ε σ w) (a : ι → ℝ) : dRep σ (∑ c, a c • Z c) w = ∑ c, (a c : ℂ) • dRep σ (Z c) w := by
  let e := Fintype.equivFin ι
  have := h.dRep_sum (B := Z ∘ e.symm) (fun i => hZ _) hw (a ∘ e.symm)
  simpa only [Function.comp_apply, e.symm.sum_comp (fun c => a c • Z c),
    e.symm.sum_comp (fun c => (a c : ℂ) • dRep σ (Z c) w)] using this

theorem dRep_dRep_sum (h : Std ε σ) {ι : Type} [Fintype ι] {Z : ι → Mx n} (hZ : ∀ c, Z c ∈ lieSet ε) {v : H}
    (hv : Sm ε σ v) (a b : ι → ℝ) :
    dRep σ (∑ c, a c • Z c) (dRep σ (∑ d, b d • Z d) v) =
      ∑ c, ∑ d, ((a c * b d : ℝ) : ℂ) • dRep σ (Z c) (dRep σ (Z d) v) := by
  have hs : ∀ d, Sm ε σ (dRep σ (Z d) v) := fun d => dRep_mem (isUnit_Jm ε) h.1 hv (hZ d)
  have hw : Sm ε σ (∑ d, (b d : ℂ) • dRep σ (Z d) v) :=
    (smooth (Jm ε) σ).sum_mem fun d _ => (smooth (Jm ε) σ).smul_mem _ (hs d)
  rw [dRep_sum_fin h hZ hv b, dRep_sum_fin h hZ hw a]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [dRep_finsum h.1 (hZ c) _ _ fun d => (smooth (Jm ε) σ).smul_mem _ (hs d), Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have := Dw_smul h.1 (l := [Z c]) (by simp [hZ c]) (b d : ℂ) (hs d)
  rw [show dRep σ (Z c) ((b d : ℂ) • dRep σ (Z d) v) = (b d : ℂ) • dRep σ (Z c) (dRep σ (Z d) v) from this,
    smul_smul]
  push_cast; ring_nf

theorem trF_conj {g : Mx n} (hg : g ∈ UJset ε) (U V : Mx n) : trF (g⁻¹ * U * g) V = trF U (g * V * g⁻¹) := by
  unfold trF
  congr 1
  rw [show g⁻¹ * U * g * V = g⁻¹ * (U * g * V) by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem trF_conj_conj {g : Mx n} (hg : g ∈ UJset ε) (U V : Mx n) :
    trF (g * U * g⁻¹) (g * V * g⁻¹) = trF U V := by
  unfold trF
  congr 1
  have e : g * U * g⁻¹ * (g * V * g⁻¹) = g * (U * V * g⁻¹) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc g⁻¹ g, inv_mul_UJ hg, Matrix.one_mul]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, inv_mul_UJ hg, Matrix.mul_one]

theorem conj_mem' {g : Mx n} (hg : g ∈ UJset ε) {X : Mx n} (hX : X ∈ lieSet ε) : g * X * g⁻¹ ∈ lieSet ε := by
  have := conj_mem_lie (isUnit_Jm ε) (inv_mem_UJ hg) hX
  rwa [Matrix.nonsing_inv_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (isUnit_of_UJ hg))] at this

theorem coef_orth {ι : Type} [Fintype ι] [DecidableEq ι] {Z : ι → Mx n} {s : ι → ℝ} (hs : ∀ c, s c * s c = 1)
    (hO : ∀ c d, trF (Z c) (Z d) = if c = d then s c else 0)
    (hE : ∀ U ∈ lieSet ε, U = ∑ c, (s c * trF U (Z c)) • Z c) (hZ : ∀ c, Z c ∈ lieSet ε) {g : Mx n}
    (hg : g ∈ UJset ε) (d e : ι) :
    ∑ c, s c * (s d * trF (g⁻¹ * Z c * g) (Z d)) * (s e * trF (g⁻¹ * Z c * g) (Z e)) =
      if d = e then s d else 0 := by
  have h3 : ∑ c, s c * trF (Z c) (g * Z d * g⁻¹) * trF (Z c) (g * Z e * g⁻¹) =
      trF (g * Z d * g⁻¹) (g * Z e * g⁻¹) := by
    conv_rhs => rw [hE _ (conj_mem' hg (hZ d)), trF_sum_left]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [trF_comm (g * Z d * g⁻¹) (Z c)]
  rw [trF_conj_conj hg, hO] at h3
  simp only [trF_conj hg]
  calc _ = s d * s e * ∑ c, s c * trF (Z c) (g * Z d * g⁻¹) * trF (Z c) (g * Z e * g⁻¹) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun c _ => ?_; ring
    _ = _ := by
        rw [h3]; split_ifs with hde
        · subst hde; rw [mul_assoc, hs, mul_one]
        · simp

theorem sum_sq_conj (h : Std ε σ) {ι : Type} [Fintype ι] [DecidableEq ι] {Z : ι → Mx n} {s : ι → ℝ}
    (hs : ∀ c, s c * s c = 1) (hO : ∀ c d, trF (Z c) (Z d) = if c = d then s c else 0)
    (hE : ∀ U ∈ lieSet ε, U = ∑ c, (s c * trF U (Z c)) • Z c) (hZ : ∀ c, Z c ∈ lieSet ε) {g : Mx n}
    (hg : g ∈ UJset ε) {v : H} (hv : Sm ε σ v) :
    ∑ c, (s c : ℂ) • dRep σ (g⁻¹ * Z c * g) (dRep σ (g⁻¹ * Z c * g) v) =
      ∑ c, (s c : ℂ) • dRep σ (Z c) (dRep σ (Z c) v) := by
  set a : ι → ι → ℝ := fun c d => s d * trF (g⁻¹ * Z c * g) (Z d) with ha
  have hW : ∀ c, g⁻¹ * Z c * g = ∑ d, a c d • Z d := fun c =>
    hE _ (conj_mem_lie (isUnit_Jm ε) hg (hZ c))
  have key := coef_orth hs hO hE hZ hg
  calc _ = ∑ c, (s c : ℂ) • ∑ d, ∑ e, ((a c d * a c e : ℝ) : ℂ) • dRep σ (Z d) (dRep σ (Z e) v) :=
        Finset.sum_congr rfl fun c _ => by rw [hW c, dRep_dRep_sum h hZ hv]
    _ = ∑ d, ∑ e, ((∑ c, s c * a c d * a c e : ℝ) : ℂ) • dRep σ (Z d) (dRep σ (Z e) v) := by
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Complex.ofReal_sum, Finset.sum_smul]
        refine Finset.sum_congr rfl fun c _ => ?_
        congr 1; push_cast; ring
    _ = _ := by
        simp only [ha, key]
        refine Finset.sum_congr rfl fun d _ => ?_
        simp [apply_ite]

omit [CompleteSpace H] in
theorem casOp_translate (hσ : IsURepOn (UJset ε) σ) {d e : ℕ} {X : Fin d → Mx n} {Y : Fin e → Mx n}
    (hX : ∀ i, X i ∈ lieSet ε) (hY : ∀ b, Y b ∈ lieSet ε) {g : Mx n} (hg : g ∈ UJset ε) {v : H} (hv : Sm ε σ v) :
    casOp σ X Y (σ g v) = σ g (casOp σ (fun i => g⁻¹ * X i * g) (fun b => g⁻¹ * Y b * g) v) := by
  have h : ∀ Z ∈ lieSet ε, dRep σ Z (dRep σ Z (σ g v)) = σ g (dRep σ (g⁻¹ * Z * g) (dRep σ (g⁻¹ * Z * g) v)) :=
    fun Z hZ => Dw_translate hσ hg hv (l := [Z, Z]) (by simp [hZ])
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [casOp, h _ (hX _), h _ (hY _), map_sub, map_sum]

theorem kk_orth (n : ℕ) (ε : Fin n → Bool) (i j : Fin (kList ε).length) :
    (trace (kB ε i * kB ε j)).re = if i = j then -1 else 0 := GlobalTheory.T.skewHermitianOrthonormalBasis_trace_orthonormal n ε i j
theorem pp_orth (n : ℕ) (ε : Fin n → Bool) (a b : Fin (pList ε).length) :
    (trace (pB ε a * pB ε b)).re = if a = b then 1 else 0 := GlobalTheory.T.re_trace_hermitianOrthonormalBasis_mul_eq_ite n ε a b
theorem kp_orth (n : ℕ) (ε : Fin n → Bool) (i : Fin (kList ε).length) (b : Fin (pList ε).length) :
    (trace (kB ε i * pB ε b)).re = 0 := GlobalTheory.T.re_trace_skewHermitian_mul_hermitianOrthonormalBasis n ε i b
theorem expand (n : ℕ) (ε : Fin n → Bool) : ∀ U ∈ lieSet ε,
    U = ∑ b, (trace (U * pB ε b)).re • pB ε b - ∑ i, (trace (U * kB ε i)).re • kB ε i := GlobalTheory.T.signature_lieSet_expand_orthonormal_bases n ε

theorem casOp_equivariant : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ g ∈ UJset ε, ∀ v, Sm ε σ v →
      casOp σ (kB ε) (pB ε) (σ g v) = σ g (casOp σ (kB ε) (pB ε) v) := by
  intro n ε H _ _ _ σ h g hg v hv
  obtain ⟨hk, hp⟩ := GlobalTheory.T.orthonormalBases_mem_unitaryLieAlgebra n ε
  let Z : Fin (kList ε).length ⊕ Fin (pList ε).length → Mx n := Sum.elim (kB ε) (pB ε)
  let s : Fin (kList ε).length ⊕ Fin (pList ε).length → ℝ := Sum.elim (fun _ => -1) (fun _ => 1)
  have hs : ∀ c, s c * s c = 1 := by rintro (c | c) <;> simp [s]
  have hZ : ∀ c, Z c ∈ lieSet ε := by rintro (c | c); exacts [hk c, hp c]
  have hO : ∀ c d, trF (Z c) (Z d) = if c = d then s c else 0 := by
    rintro (c | c) (d | d)
    · simpa [Z, s] using kk_orth n ε c d
    · simpa [Z, s] using kp_orth n ε c d
    · simpa [Z, s, trF_comm] using kp_orth n ε d c
    · simpa [Z, s] using pp_orth n ε c d
  have hE : ∀ U ∈ lieSet ε, U = ∑ c, (s c * trF U (Z c)) • Z c := by
    intro U hU
    simp only [Fintype.sum_sum_type, Z, s, Sum.elim_inl, Sum.elim_inr, neg_one_mul, one_mul, neg_smul,
      Finset.sum_neg_distrib]
    conv_lhs => rw [expand n ε U hU]
    abel
  have := sum_sq_conj h hs hO hE hZ hg hv
  simp only [Fintype.sum_sum_type, Z, s, Sum.elim_inl, Sum.elim_inr, Complex.ofReal_neg, Complex.ofReal_one, neg_smul,
    one_smul, Finset.sum_neg_distrib] at this
  rw [casOp_translate h.1 hk hp hg hv]
  congr 1
  simp only [casOp, sub_eq_neg_add]
  exact this

end GlobalTheory.TypeSum.CasEquiv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CasimirDifferenceOperatorEquivariantStatement
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimirDifferenceOperator_equivariant : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ g ∈ UJset ε, ∀ v, Sm ε σ v → casOp σ (kB ε) (pB ε) (σ g v) = σ g (casOp σ (kB ε) (pB ε) v) := by
  first | exact @GlobalTheory.TypeSum.CasEquiv.casOp_equivariant | exact GlobalTheory.TypeSum.CasEquiv.casOp_equivariant | (intros; apply GlobalTheory.TypeSum.CasEquiv.casOp_equivariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSmoothEigenvectorCasimirDifferenceOperator
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSmoothEigenvectorCasimirDifferenceOperator
noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis
  GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum.CasBasis

theorem exists_eigen_casOp : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)) (d e : ℕ) (X : Fin d → Mx n) (Y : Fin e → Mx n), Std ε σ →
    (∀ i, X i ∈ lieSet ε) → (∀ b, Y b ∈ lieSet ε) →
    (∀ k ∈ Kset ε, ∀ v, Sm ε σ v → casOp σ X Y (σ k v) = σ k (casOp σ X Y v)) →
    ∃ (u : H) (χ : ℂ), Sm ε σ u ∧ u ≠ 0 ∧ casOp σ X Y u = χ • u := by
  intro n ε H _ _ _ σ d e X Y h hX hY hK
  have hσ := h.1
  obtain ⟨v₀, hv₀K, hv₀⟩ := h.2.2.2.2
  let f : KG ε → ℂ := fun k => star ⟪v₀, σ (toMK k) v₀⟫_ℂ
  have hfc : Continuous f := (continuous_const.inner (KCoef.continuous_orbit hσ v₀)).star
  obtain ⟨Q, hQ⟩ := KCoef.exists_clm_kAvg hσ hfc
  obtain ⟨m, a, c, -, haK, -, hsum⟩ := kAvg_finite_rank n ε H σ h f (KCoef.kFinFun_coef hσ hv₀K)
  let Ss : Submodule ℂ H := smooth (Jm ε) σ
  let V : Submodule ℂ H := Ss.map (Q : H →ₗ[ℂ] H)
  have hVspan : V ≤ Submodule.span ℂ (Set.range a) := by
    rintro _ ⟨w, -, rfl⟩
    change Q w ∈ _
    rw [hQ, hsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hVsm : ∀ u ∈ V, Sm ε σ u := by
    intro u hu
    have hspan : Submodule.span ℂ (Set.range a) ≤ Ss :=
      Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact h.2.2.1 _ (haK j))
    exact hspan (hVspan hu)
  haveI : FiniteDimensional ℂ V :=
    by
      haveI := FiniteDimensional.span_of_finite ℂ (Set.finite_range a)
      exact Submodule.finiteDimensional_of_le hVspan

  have hcomm : ∀ v, Sm ε σ v → casOp σ X Y (Q v) = Q (casOp σ X Y v) := by
    intro v hv
    have hQv : Sm ε σ (Q v) := hVsm _ ⟨v, hv, rfl⟩
    refine h.dense_smooth.eq_of_inner_right ℂ fun y hy => ?_
    have hy' : Sm ε σ y := hy
    rw [inner_casOp hσ hX hY hy' hQv, hQ, hQ, KCoef.inner_kAvg hσ hfc, KCoef.inner_kAvg hσ hfc]
    congr 1
    funext k
    congr 1
    rw [← inner_casOp hσ hX hY hy' (Sm.translate hσ hv (KCoef.toMK_mem_UJ k)), hK _ (toMK_mem_K k) v hv]
  have hVmap : ∀ u ∈ V, casOp σ X Y u ∈ V := by
    rintro _ ⟨v, hv, rfl⟩
    change casOp σ X Y (Q v) ∈ V
    rw [hcomm v hv]
    exact ⟨_, sm_casOp hσ hX hY hv, rfl⟩
  let F : Module.End ℂ V :=
    { toFun := fun u => ⟨casOp σ X Y u, hVmap u u.2⟩
      map_add' := fun x y => Subtype.ext (casOp_add hσ hX hY (hVsm _ x.2) (hVsm _ y.2))
      map_smul' := fun r x => Subtype.ext (casOp_smul hσ hX hY r (hVsm _ x.2)) }
  have hQv₀ : Q v₀ ≠ 0 := by
    intro h0
    apply KCoef.inner_kAvg_ne_zero hσ hv₀
    rw [← hQ, h0, inner_zero_right]
  haveI : Nontrivial V := ⟨⟨⟨Q v₀, v₀, h.2.2.1 _ hv₀K, rfl⟩, 0, fun h0 => hQv₀ (congrArg Subtype.val h0)⟩⟩
  obtain ⟨χ, hχ⟩ := Module.End.exists_eigenvalue F
  obtain ⟨u, hu⟩ := hχ.exists_hasEigenvector
  refine ⟨u, χ, hVsm _ u.2, fun h0 => hu.2 (Subtype.ext h0), ?_⟩
  exact congrArg Subtype.val (hu.apply_eq_smul)

end GlobalTheory.TypeSum.CasBasis

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSmoothEigenvectorCasimirDifferenceOperatorStatement
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_eigenvector_casimirDifferenceOperator : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)) (d e : ℕ) (X : Fin d → Mx n) (Y : Fin e → Mx n), Std ε σ → (∀ i, X i ∈ lieSet ε) → (∀ b, Y b ∈ lieSet ε) → (∀ k ∈ Kset ε, ∀ v, Sm ε σ v → casOp σ X Y (σ k v) = σ k (casOp σ X Y v)) → ∃ (u : H) (χ : ℂ), Sm ε σ u ∧ u ≠ 0 ∧ casOp σ X Y u = χ • u := by
  first | exact @GlobalTheory.TypeSum.CasBasis.exists_eigen_casOp | exact GlobalTheory.TypeSum.CasBasis.exists_eigen_casOp | (intros; apply GlobalTheory.TypeSum.CasBasis.exists_eigen_casOp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CasimirUnitaryGroupActsByScalarSmoothVectors
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.TypeSum.CasBasis

theorem casimir_scalar : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∃ χ : ℂ, ∀ v, Sm ε σ v → ∑ b, dRep σ (pB ε b) (dRep σ (pB ε b) v) = χ • v + ∑ i, dRep σ (kB ε i) (dRep σ (kB ε i) v) := by
  intro n ε H _ _ _ σ h
  obtain ⟨hX, hY⟩ := GlobalTheory.T.orthonormalBases_mem_unitaryLieAlgebra n ε
  have hG := GlobalTheory.T.casimirDifferenceOperator_equivariant n ε H σ h
  obtain ⟨u, χ, hu, hu0, hχ⟩ := GlobalTheory.T.exists_smooth_eigenvector_casimirDifferenceOperator n ε H σ _ _ (kB ε) (pB ε) h hX hY fun k hk v hv => hG k (K_le_UJ hk) v hv
  have hχr : (starRingEnd ℂ) χ = χ := by
    have e := inner_casOp h.1 hX hY hu hu
    rw [hχ, inner_smul_left, inner_smul_right] at e
    have hne : ⟪u, u⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hu0
    exact (mul_right_cancel₀ hne e).symm
  refine ⟨χ, fun v hv => ?_⟩
  have hws : Sm ε σ (casOp σ (kB ε) (pB ε) v - χ • v) :=
    (smooth (Jm ε) σ).sub_mem (sm_casOp h.1 hX hY hv) ((smooth (Jm ε) σ).smul_mem χ hv)
  have h0 : ∀ g ∈ UJset ε,
      ((innerSL ℂ (casOp σ (kB ε) (pB ε) v - χ • v) : H →L[ℂ] ℂ) : H →ₗ[ℂ] ℂ) (σ g u) = 0 := by
    intro g hg
    have hgu := hu.translate h.1 hg
    simp only [ContinuousLinearMap.coe_coe, innerSL_apply_apply, inner_sub_left, inner_smul_left, hχr]
    rw [← inner_casOp h.1 hX hY hv hgu, hG g hg u hu, hχ, map_smul, inner_smul_right, sub_self]
  have hz := h.eq_zero_of_orbit (sobCont_inner _) hu hu0 h0 hws
  simp only [ContinuousLinearMap.coe_coe, innerSL_apply_apply, inner_self_eq_zero] at hz
  simp only [casOp, sub_sub, sub_eq_zero] at hz
  rw [hz, add_comm]

end GlobalTheory.TypeSum.CasBasis

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CasimirUnitaryGroupActsByScalarSmoothVectorsStatement
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_unitaryGroup_acts_by_scalar_smoothVectors : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∃ χ : ℂ, ∀ v, Sm ε σ v → ∑ b, dRep σ (pB ε b) (dRep σ (pB ε b) v) = χ • v + ∑ i, dRep σ (kB ε i) (dRep σ (kB ε i) v) := by
  first | exact @GlobalTheory.TypeSum.CasBasis.casimir_scalar | exact GlobalTheory.TypeSum.CasBasis.casimir_scalar | (intros; apply GlobalTheory.TypeSum.CasBasis.casimir_scalar <;> assumption)
end
