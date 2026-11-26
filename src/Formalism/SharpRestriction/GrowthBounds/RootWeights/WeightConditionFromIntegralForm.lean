module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.ExponentFactorialAddSingleOne
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FirstStatementB

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.CrLift
section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.CasimirIsotypicNoHigherWeight
section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicComponentLeLowerWeights
section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.CrCCommApply
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def cr_C (E : GLOps n K V) : Module.End K V := ∑ a : Fin n, ∑ b : Fin n, E a b * E b a

theorem cr_C_comm (E : GLOps n K V) (hR : SatisfiesGLRelations E) (c d : Fin n) : cr_C E * E c d = E c d * cr_C E := by
  classical
  have key : ∀ a b, E a b * E b a * E c d - E c d * (E a b * E b a) =
      E a b * ((if a = c then E b d else 0) - (if d = b then E c a else 0)) +
        ((if b = c then E a d else 0) - (if d = a then E c b else 0)) * E b a := by
    intro a b
    rw [← hR b a c d, ← hR a b c d]; noncomm_ring
  have S1 : ∑ a : Fin n, ∑ b : Fin n, E a b * (if a = c then E b d else 0) = ∑ b, E c b * E b d := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [mul_ite]
  have S2 : ∑ a : Fin n, ∑ b : Fin n, E a b * (if d = b then E c a else 0) = ∑ a, E a d * E c a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [mul_ite]
  have S3 : ∑ a : Fin n, ∑ b : Fin n, (if b = c then E a d else 0) * E b a = ∑ a, E a d * E c a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [ite_mul]
  have S4 : ∑ a : Fin n, ∑ b : Fin n, (if d = a then E c b else 0) * E b a = ∑ b, E c b * E b d := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [ite_mul]
  rw [← sub_eq_zero, cr_C, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have : ∀ a : Fin n, (∑ b : Fin n, E a b * E b a) * E c d - E c d * ∑ b : Fin n, E a b * E b a =
      ∑ b : Fin n, (E a b * ((if a = c then E b d else 0) - (if d = b then E c a else 0)) +
        ((if b = c then E a d else 0) - (if d = a then E c b else 0)) * E b a) := by
    intro a
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => key a b
  rw [Finset.sum_congr rfl fun a _ => this a]
  simp only [mul_sub, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [S1, S2, S3, S4]
  abel

theorem cr_C_comm_apply (E : GLOps n K V) (hR : SatisfiesGLRelations E) (c d : Fin n) (x : V) :
    cr_C E (E c d x) = E c d (cr_C E x) := by
  have := congrArg (fun f : Module.End K V => f x) (cr_C_comm E hR c d)
  simpa using this

theorem cr_sym {M : Type*} [AddCommMonoid M] (F : Fin n → Fin n → M) :
    ∑ a, ∑ b, F a b = ∑ a, F a a + ∑ a, ∑ b, if a < b then F a b + F b a else 0 :=
  _root_.UpperTheory.Reformulated.B.DoubleSumDiagonalOffDiagonal.main F

theorem cr_C_wt (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E mu) :
    cr_C E x = ((cr_c mu : ℤ) : K) • x + (2 : K) • ∑ a : Fin n, ∑ b : Fin n, if a < b then E b a (E a b x) else 0 := by
  classical
  have hx' := (v2rep_mem_weightSp E mu x).1 hx
  have e0 : cr_C E x = ∑ a : Fin n, ∑ b : Fin n, E a b (E b a x) := by
    simp [cr_C, LinearMap.sum_apply]
  have e1 : ∀ a, E a a (E a a x) = ((mu a : K) ^ 2) • x := by
    intro a
    rw [hx' a, map_smul, hx' a, smul_smul, sq]
  have e2 : ∀ a b : Fin n, E a b (E b a x) + E b a (E a b x) =
      (2 : K) • E b a (E a b x) + ((mu a : K) - (mu b : K)) • x := by
    intro a b
    rw [v2rep_comm E hR a b b a x]
    simp only [if_true, hx' a, hx' b, sub_smul, two_smul]
    abel
  rw [e0, cr_sym, Finset.sum_congr rfl fun a _ => e1 a]
  have e3 : ∀ a b : Fin n, (if a < b then E a b (E b a x) + E b a (E a b x) else 0) =
      (2 : K) • (if a < b then E b a (E a b x) else 0) + (if a < b then ((mu a : K) - (mu b : K)) else 0) • x := by
    intro a b
    split_ifs
    · exact e2 a b
    · simp
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => e3 a b]
  simp only [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.sum_smul]
  have e4 : ((cr_c mu : ℤ) : K) = ∑ a, (mu a : K) ^ 2 + ∑ a : Fin n, ∑ b : Fin n,
      (if a < b then ((mu a : K) - (mu b : K)) else 0) := by
    simp only [cr_c, cr_h]
    push_cast
    rfl
  rw [e4, add_smul]
  abel

theorem cr_C_hwv (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v) :
    cr_C E v = ((cr_c mu : ℤ) : K) • v := by
  rw [cr_C_wt E hR mu v hv.2.1]
  have : ∑ a : Fin n, ∑ b : Fin n, (if a < b then E b a (E a b v) else 0) = 0 := by
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    split_ifs with h
    · rw [hv.2.2 a b h, map_zero]
    · rfl
  rw [this, smul_zero, add_zero]

theorem cr_C_stable (E : GLOps n K V) (W : Submodule K V) (hW : IsStableUnderOperators E W) (x : V) (hx : x ∈ W) :
    cr_C E x ∈ W := by
  simp only [cr_C, LinearMap.sum_apply, Module.End.mul_apply]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => hW a b _ (hW b a _ hx)

theorem cr_C_weightSp (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E mu) :
    cr_C E x ∈ weightSp E mu := by
  rw [v2rep_mem_weightSp] at hx ⊢
  intro a
  rw [← cr_C_comm_apply E hR, hx a, map_smul]

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def cr_WS (E : GLOps n K V) (S : Set (Fin n → ℤ)) : Submodule K V := ⨆ ν ∈ S, weightSp E ν

theorem cr_WS_mono (E : GLOps n K V) {S S' : Set (Fin n → ℤ)} (h : S ⊆ S') : cr_WS E S ≤ cr_WS E S' := by
  unfold cr_WS
  exact biSup_mono fun i hi => h hi

theorem cr_WS_of_mem (E : GLOps n K V) {S : Set (Fin n → ℤ)} {ν : Fin n → ℤ} (h : ν ∈ S) :
    weightSp E ν ≤ cr_WS E S := by
  unfold cr_WS
  exact le_iSup₂ (f := fun ν (_ : ν ∈ S) => weightSp E ν) ν h

theorem cr_wt_disj [CharZero K] (E : GLOps n K V) {ν ν' : Fin n → ℤ} (hne : ν ≠ ν') {x : V}
    (h1 : x ∈ weightSp E ν) (h2 : x ∈ weightSp E ν') : x = 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hne
  have e1 := (v2rep_mem_weightSp E ν x).1 h1 a
  have e2 := (v2rep_mem_weightSp E ν' x).1 h2 a
  have e3 : ((ν a : K) - (ν' a : K)) • x = 0 := by rw [sub_smul, ← e1, ← e2, sub_self]
  rcases smul_eq_zero.1 e3 with h | h
  · exact absurd (Int.cast_injective (sub_eq_zero.1 h)) ha
  · exact h

theorem cr_wt_diag_stable (E : GLOps n K V) (ν : Fin n → ℤ) (a : Fin n) (x : V) (hx : x ∈ weightSp E ν) :
    E a a x ∈ weightSp E ν := by
  rw [(v2rep_mem_weightSp E ν x).1 hx a]
  exact Submodule.smul_mem _ _ hx

theorem cr_WS_mem [CharZero K] (E : GLOps n K V) {S : Set (Fin n → ℤ)} {ν0 : Fin n → ℤ} {z : V}
    (hz : z ∈ cr_WS E S) (hz0 : z ∈ weightSp E ν0) (hne : z ≠ 0) : ν0 ∈ S := by
  classical
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hz
  have hf' : ∀ ν, f ν ∈ weightSp E ν := fun ν => (iSup_le fun _ => le_rfl : (⨆ (_ : ν ∈ S), weightSp E ν) ≤ _) (hf ν)
  have h := v2rep_comp_mem E (weightSp E ν0) (fun a x hx => cr_wt_diag_stable E ν0 a x hx) f.support
    (fun ν => f ν) (fun ν _ => hf' ν) hz0
  have hsupp : ∀ ν ∈ f.support, ν = ν0 := by
    intro ν hν
    by_contra hh
    exact (Finsupp.mem_support_iff.1 hν) (cr_wt_disj E hh (hf' ν) (h ν hν))
  by_contra hS
  have h0 : f ν0 = 0 := by
    have := hf ν0
    simpa [hS] using this
  apply hne
  refine Finset.sum_eq_zero fun ν hν => ?_
  rw [hsupp ν hν]
  exact h0

def cr_Low (lam : Fin n → ℤ) : Set (Fin n → ℤ) := {ν | lam - ν ∈ cr_Pos n ∧ 0 < weightHeight' (lam - ν)}

def weightsBelow (lam : Fin n → ℤ) : Set (Fin n → ℤ) := {ν | lam - ν ∈ cr_Pos n}

theorem cr_Low_sub (lam : Fin n → ℤ) : cr_Low lam ⊆ weightsBelow lam := fun _ hν => hν.1

theorem cr_lower (E : GLOps n K V) (hR : SatisfiesGLRelations E) (lam : Fin n → ℤ) (a b : Fin n) (h : b < a) :
    cr_WS E (weightsBelow lam) ≤ (cr_WS E (cr_Low lam)).comap (E a b) := by
  refine iSup₂_le fun ν hν x hx => ?_
  show E a b x ∈ cr_WS E (cr_Low lam)
  refine cr_WS_of_mem E ?_ (v2rep_shift E hR a b ν x hx)
  have e : lam - (ν + rootW a b) = (lam - ν) + rootW b a := by
    ext c; simp only [rootW, Pi.sub_apply, Pi.add_apply]; ring
  refine ⟨?_, ?_⟩
  · rw [e]; exact add_mem hν (cr_root_mem b a h)
  · rw [e, cr_ht_add]
    have h1 := cr_Pos_ht hν
    have h2 := cr_ht_root b a h
    omega

theorem cr_Y_le (E : GLOps n K V) (hR : SatisfiesGLRelations E) (lam : Fin n → ℤ) (v : V) (hv : IsHWV E lam v) (k : ℕ) :
    cyclicLevelSubmodule E v k ≤ Submodule.span K {v} ⊔ cr_WS E (cr_Low lam) := by
  have hv0 : Submodule.span K {v} ⊔ cr_WS E (cr_Low lam) ≤ cr_WS E (weightsBelow lam) := by
    refine sup_le ?_ (cr_WS_mono E (cr_Low_sub lam))
    rw [Submodule.span_singleton_le_iff_mem]
    refine cr_WS_of_mem E ?_ hv.2.1
    show lam - lam ∈ cr_Pos n
    rw [sub_self]; exact zero_mem _
  induction k with
  | zero => exact le_sup_left
  | succ k ih =>
    refine sup_le ih ?_
    refine iSup_le fun ab => iSup_le fun hab => ?_
    rw [Submodule.map_le_iff_le_comap]
    refine (ih.trans hv0).trans ((cr_lower E hR lam ab.1 ab.2 hab).trans ?_)
    exact Submodule.comap_mono le_sup_right

theorem cr_isoIn_le (E : GLOps n K V) (hR : SatisfiesGLRelations E) (Wx : Submodule K V) (lam : Fin n → ℤ) :
    isotypicPartIn E Wx lam ≤ (Wx ⊓ weightSp E lam) ⊔ cr_WS E (cr_Low lam) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨u, hu, v, hvW, hv, rfl⟩
  obtain ⟨k, hk⟩ := v2rep_Umon_Y E hR lam v hv u hu 0 v (Submodule.mem_span_singleton_self v)
  have hle : Submodule.span K {v} ⊔ cr_WS E (cr_Low lam) ≤ (Wx ⊓ weightSp E lam) ⊔ cr_WS E (cr_Low lam) := by
    refine sup_le_sup_right ?_ _
    rw [Submodule.span_singleton_le_iff_mem]
    exact ⟨hvW, hv.2.1⟩
  exact hle (cr_Y_le E hR lam v hv k hk)

theorem isotypic_component_le_lower_weights (E : GLOps n K V) (hR : SatisfiesGLRelations E) (Wx : Submodule K V) (lam : Fin n → ℤ) :
    isotypicPartIn E Wx lam ≤ cr_WS E (weightsBelow lam) := by
  refine (cr_isoIn_le E hR Wx lam).trans (sup_le ?_ (cr_WS_mono E (cr_Low_sub lam)))
  refine inf_le_right.trans (cr_WS_of_mem E ?_)
  show lam - lam ∈ cr_Pos n
  rw [sub_self]; exact zero_mem _

theorem cr_dom [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (rel : SatisfiesGLRelations E) {mu : Fin n → ℤ} {v : V}
    (hne : v ≠ 0) (hv : v ∈ weightSp E mu) (a b : Fin n) (hab : a ≠ b) (he : E a b v = 0) : mu b ≤ mu a := by
  have hba : b ≠ a := hab.symm
  have hef : E a b * E b a - E b a * E a b = E a a - E b b := by
    have := rel a b b a
    simpa using this
  have h1 : E a a * E a b - E a b * E a a = E a b := by
    have := rel a a a b
    simpa [hba] using this
  have h2 : E b b * E a b - E a b * E b b = - E a b := by
    have := rel b b a b
    simpa [hba] using this
  have h3 : E a a * E b a - E b a * E a a = - E b a := by
    have := rel a a b a
    simpa [hab] using this
  have h4 : E b b * E b a - E b a * E b b = E b a := by
    have := rel b b b a
    simpa [hab] using this
  have hva : E a a v = (mu a : K) • v := (v2rep_mem_weightSp E mu v).1 hv a
  have hvb : E b b v = (mu b : K) • v := (v2rep_mem_weightSp E mu v).1 hv b
  have hhf : (E a a - E b b) * E b a - E b a * (E a a - E b b) = -(2 • E b a) := by
    have : (E a a - E b b) * E b a - E b a * (E a a - E b b) =
        (E a a * E b a - E b a * E a a) - (E b b * E b a - E b a * E b b) := by noncomm_ring
    rw [this, h3, h4, two_smul]; abel
  have hhe : (E a a - E b b) * E a b - E a b * (E a a - E b b) = 2 • E a b := by
    have : (E a a - E b b) * E a b - E a b * (E a a - E b b) =
        (E a a * E a b - E a b * E a a) - (E b b * E a b - E a b * E b b) := by noncomm_ring
    rw [this, h1, h2, two_smul]; abel
  have hhv : (E a a - E b b) v = ((mu a : K) - (mu b : K)) • v := by
    rw [LinearMap.sub_apply, hva, hvb, sub_smul]
  by_cases hh0 : E a a - E b b = 0
  · rw [hh0, LinearMap.zero_apply] at hhv
    rcases smul_eq_zero.1 hhv.symm with h | h
    · exact (Int.cast_injective (sub_eq_zero.1 h)).ge
    · exact absurd h hne
  have t : IsSl2Triple (E a a - E b b) (E a b) (E b a) :=
    { h_ne_zero := hh0
      lie_e_f := by rw [Ring.lie_def]; exact hef
      lie_h_e_nsmul := by rw [Ring.lie_def]; exact hhe
      lie_h_f_nsmul := by rw [Ring.lie_def]; exact hhf }
  have P : t.HasPrimitiveVectorWith v ((mu a : K) - (mu b : K)) :=
    { ne_zero := hne
      lie_h := by rw [Module.End.lie_apply]; exact hhv
      lie_e := by rw [Module.End.lie_apply]; exact he }
  obtain ⟨m, hm⟩ := P.exists_nat
  have : ((mu a - mu b : ℤ) : K) = ((m : ℤ) : K) := by push_cast; exact hm
  have := Int.cast_injective this
  omega

theorem cr_hwv_dom [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (rel : SatisfiesGLRelations E) {mu : Fin n → ℤ} {v : V}
    (hv : IsHWV E mu v) : Dominant mu := by
  intro a b hab
  rcases hab.lt_or_eq with h | h
  · exact cr_dom E rel hv.1 hv.2.1 a b h.ne (hv.2.2 a b h)
  · rw [h]

theorem cr_isoIn_dom [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (rel : SatisfiesGLRelations E) (Wx : Submodule K V)
    {mu : Fin n → ℤ} {x : V} (hx : x ∈ isotypicPartIn E Wx mu) (hne : x ≠ 0) : Dominant mu := by
  by_contra hd
  apply hne
  have : isotypicPartIn E Wx mu = ⊥ := by
    rw [isotypicPartIn, Submodule.span_eq_bot]
    rintro y ⟨u, _, v, _, hv, rfl⟩
    exact absurd (cr_hwv_dom E rel hv) hd
  rw [this] at hx
  exact (Submodule.mem_bot K).1 hx

end Formalism.MainNotions.G.GLWeightTheory
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.CrAevalStable
noncomputable section

open Finset Polynomial

namespace Formalism.MainNotions.G.GLWeightTheory

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem cr_pow_mod (T : Module.End K V) (Z : Submodule K V) (hZ : ∀ x ∈ Z, T x ∈ Z) (a : K) (x : V)
    (hx : T x - a • x ∈ Z) (k : ℕ) : (T ^ k) x - a ^ k • x ∈ Z := by
  induction k with
  | zero => simp [Z.zero_mem]
  | succ k ih =>
    have e1 : (T ^ (k + 1)) x = T ((T ^ k) x) := by rw [pow_succ', Module.End.mul_apply]
    have e2 : a ^ (k + 1) • x = a ^ k • (a • x) := by rw [pow_succ, mul_smul]
    have e3 : (T ^ (k + 1)) x - a ^ (k + 1) • x =
        T ((T ^ k) x - a ^ k • x) + a ^ k • (T x - a • x) := by
      rw [e1, e2, map_sub, map_smul, smul_sub]; abel
    rw [e3]
    exact Z.add_mem (hZ _ ih) (Z.smul_mem _ hx)

theorem cr_aeval_mod (T : Module.End K V) (Z : Submodule K V) (hZ : ∀ x ∈ Z, T x ∈ Z) (a : K) (x : V)
    (hx : T x - a • x ∈ Z) (q : K[X]) : aeval T q x - q.eval a • x ∈ Z := by
  refine Polynomial.induction_on' q (fun p r hp hr => ?_) (fun n c => ?_)
  · have e : aeval T (p + r) x - (p + r).eval a • x =
        (aeval T p x - p.eval a • x) + (aeval T r x - r.eval a • x) := by
      rw [map_add (f := _), LinearMap.add_apply, eval_add, add_smul]; abel
    rw [e]; exact Z.add_mem hp hr
  · rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, eval_monomial, mul_smul,
      ← smul_sub]
    exact Z.smul_mem c (cr_pow_mod T Z hZ a x hx n)

theorem cr_aeval_eig (T : Module.End K V) (a : K) (x : V) (hx : T x = a • x) (q : K[X]) :
    aeval T q x = q.eval a • x := by
  have h := cr_aeval_mod T ⊥ (fun y hy => by
      rw [Submodule.mem_bot] at hy ⊢; rw [hy, map_zero]) a x
    (by rw [hx, sub_self]; exact Submodule.zero_mem _) q
  rw [Submodule.mem_bot, sub_eq_zero] at h
  exact h

theorem cr_aeval_stable (T : Module.End K V) (Z : Submodule K V) (hZ : ∀ x ∈ Z, T x ∈ Z) (x : V) (hx : x ∈ Z)
    (q : K[X]) : aeval T q x ∈ Z := by
  have h := cr_aeval_mod T Z hZ 0 x (by rw [zero_smul, sub_zero]; exact hZ x hx) q
  have h' := Z.add_mem h (Z.smul_mem (q.eval 0) hx)
  rwa [sub_add_cancel] at h'

theorem cr_aeval_comm (T X' : Module.End K V) (h : T * X' = X' * T) (q : K[X]) (x : V) :
    aeval T q (X' x) = X' (aeval T q x) := by
  have hc : Commute T X' := h
  refine Polynomial.induction_on' q (fun p r hp hr => ?_) (fun n c => ?_)
  · rw [map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hp, hr, map_add (f := _)]
  · rw [aeval_monomial, Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, map_smul]
    congr 1
    exact LinearMap.congr_fun (hc.pow_left n).eq x

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open Finset Polynomial

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def cr_quot (E : GLOps n K V) (Z : Submodule K V) (hZ : IsStableUnderOperators E Z) : GLOps n K (V ⧸ Z) :=
  fun a b => Z.mapQ Z (E a b) (fun x hx => hZ a b x hx)

theorem cr_quot_mk (E : GLOps n K V) (Z : Submodule K V) (hZ : IsStableUnderOperators E Z) (a b : Fin n) (x : V) :
    cr_quot E Z hZ a b (Z.mkQ x) = Z.mkQ (E a b x) := rfl

theorem cr_quot_rel (E : GLOps n K V) (hR : SatisfiesGLRelations E) (Z : Submodule K V) (hZ : IsStableUnderOperators E Z) :
    SatisfiesGLRelations (cr_quot E Z hZ) := by
  intro a b c d
  refine LinearMap.ext fun y => ?_
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective Z y
  have h := congrArg (fun f : Module.End K V => Z.mkQ (f x)) (hR a b c d)
  split_ifs at h ⊢ <;> simpa [cr_quot] using h

theorem cr_quot_wt (E : GLOps n K V) (Z : Submodule K V) (hZ : IsStableUnderOperators E Z) (ν : Fin n → ℤ) (x : V)
    (hx : x ∈ weightSp E ν) : Z.mkQ x ∈ weightSp (cr_quot E Z hZ) ν := by
  rw [weightSp, Submodule.mem_iInf] at hx ⊢
  intro a
  have h := LinearMap.mem_ker.mp (hx a)
  rw [LinearMap.mem_ker]
  have e : (cr_quot E Z hZ a a - (ν a : K) • (1 : Module.End K (V ⧸ Z))) (Z.mkQ x)
      = Z.mkQ ((E a a - (ν a : K) • (1 : Module.End K V)) x) := by
    simp [cr_quot]
  rw [e, h, map_zero]

theorem cr_quot_top (E : GLOps n K V) (Z : Submodule K V) (hZ : IsStableUnderOperators E Z)
    (hT : (⨆ ν, weightSp E ν) = ⊤) : (⊤ : Submodule K (V ⧸ Z)) ≤ ⨆ ν, weightSp (cr_quot E Z hZ) ν := by
  intro y _
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective Z y
  have hx : x ∈ ⨆ ν, weightSp E ν := by rw [hT]; exact Submodule.mem_top
  have h1 : Z.mkQ x ∈ Submodule.map Z.mkQ (⨆ ν, weightSp E ν) := Submodule.mem_map_of_mem hx
  rw [Submodule.map_iSup] at h1
  have hle : (⨆ ν, Submodule.map Z.mkQ (weightSp E ν)) ≤ ⨆ ν, weightSp (cr_quot E Z hZ) ν := by
    refine iSup_mono fun ν => ?_
    rintro _ ⟨w, hw, rfl⟩
    exact cr_quot_wt E Z hZ ν w hw
  exact hle h1

private lemma casimir_commute_E (E : GLOps n K V) (hR : SatisfiesGLRelations E) (c d : Fin n) :
    cr_C E * E c d = E c d * cr_C E := by
  have key : ∀ a b, E a b * E b a * E c d - E c d * (E a b * E b a)
      = E a b * ((if a = c then E b d else 0) - if d = b then E c a else 0)
        + ((if b = c then E a d else 0) - if d = a then E c b else 0) * E b a := by
    intro a b
    rw [← hR b a c d, ← hR a b c d]
    noncomm_ring
  have S1 : ∑ a, ∑ b, E a b * (if a = c then E b d else 0) = ∑ b, E c b * E b d := by
    rw [Finset.sum_eq_single c]
    · simp
    · intro a _ ha
      simp [ha]
    · simp
  have S2 : ∑ a, ∑ b, E a b * (if d = b then E c a else 0) = ∑ a, E a d * E c a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp
  have S3 : ∑ a, ∑ b, (if b = c then E a d else 0) * E b a = ∑ a, E a d * E c a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp
  have S4 : ∑ a, ∑ b, (if d = a then E c b else 0) * E b a = ∑ b, E c b * E b d := by
    rw [Finset.sum_eq_single d]
    · simp
    · intro a _ ha
      simp [Ne.symm ha]
    · simp
  have hexp : cr_C E * E c d - E c d * cr_C E
      = ∑ a, ∑ b, (E a b * E b a * E c d - E c d * (E a b * E b a)) := by
    simp only [cr_C, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
  rw [← sub_eq_zero, hexp]
  simp only [key, mul_sub, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [S1, S2, S3, S4]
  abel

private lemma casimir_apply_eq_smul_of_isHWV (E : GLOps n K V) (hR : SatisfiesGLRelations E) (ν : Fin n → ℤ) (v : V) (hv : IsHWV E ν v) :
    cr_C E v = (cr_c ν : K) • v := by
  have hw : ∀ a, E a a v = (ν a : K) • v := by
    intro a
    have h0 := hv.2.1
    rw [weightSp, Submodule.mem_iInf] at h0
    have h := LinearMap.mem_ker.mp (h0 a)
    simpa [sub_eq_zero] using h
  have hterm : ∀ a b, E a b (E b a v)
      = (if a = b then (ν a : K) ^ 2 else if a < b then (ν a : K) - ν b else 0) • v := by
    intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · have hc := congrArg (fun f : Module.End K V => f v) (hR a b b a)
      rw [if_neg h.ne, if_pos h, sub_smul]
      simpa [hv.2.2 a b h, hw] using hc
    · simp [hw, sq, mul_smul]
    · rw [if_neg (ne_of_gt h), if_neg (not_lt.mpr h.le), hv.2.2 b a h, map_zero, zero_smul]
  have hs : (∑ a, ∑ b, (if a = b then (ν a : K) ^ 2 else if a < b then (ν a : K) - ν b else 0))
      = (cr_c ν : K) := by
    have split : ∀ a b, (if a = b then (ν a : K) ^ 2 else if a < b then (ν a : K) - ν b else 0)
        = (if a = b then (ν a : K) ^ 2 else 0) + (if a < b then (ν a : K) - ν b else 0) := by
      intro a b
      by_cases h : a = b
      · subst h
        simp
      · simp [h]
    simp only [cr_c, cr_h]
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_congr rfl fun b _ => split a b, Finset.sum_add_distrib]
    simp
  rw [← hs, Finset.sum_smul]
  unfold cr_C
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← hterm]
  rfl

private lemma casimir_commute_of_mem_Umon (E : GLOps n K V) (hR : SatisfiesGLRelations E) (u : Module.End K V) (hu : u ∈ Umon E) :
    cr_C E * u = u * cr_C E := by
  have h : Umon E ≤ Submonoid.centralizer {cr_C E} := by
    unfold Umon
    rw [Submonoid.closure_le]
    rintro _ ⟨⟨c, d⟩, rfl⟩
    rw [SetLike.mem_coe, Submonoid.mem_centralizer_iff]
    rintro g rfl
    exact casimir_commute_E E hR c d
  exact Submonoid.mem_centralizer_iff.mp (h hu) _ rfl

private lemma aeval_apply_eq_eval_smul_of_eigenvector (f : Module.End K V) (c : K) (t : V) (ht : f t = c • t) (p : K[X]) :
    aeval f p t = p.eval c • t := by
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro a
    simp
  · intro p q hp hq
    simp only [map_add (f := _), LinearMap.add_apply, hp, hq, Polynomial.eval_add, add_smul]
  · intro k a h
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Polynomial.eval_mul, Polynomial.eval_X]
    change (aeval f (Polynomial.C a * X ^ k)) (f t) = _
    rw [ht, map_smul, h, smul_smul, mul_comm]

private lemma casimir_apply_eq_smul_of_mem_isotypicPartIn (E : GLOps n K V) (hR : SatisfiesGLRelations E) (W : Submodule K V) (ν : Fin n → ℤ) (x : V)
    (hx : x ∈ isotypicPartIn E W ν) : cr_C E x = (cr_c ν : K) • x := by
  have hle : isotypicPartIn E W ν ≤ LinearMap.ker (cr_C E - (cr_c ν : K) • (1 : Module.End K V)) := by
    unfold isotypicPartIn
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, v, _, hH, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    have h1 : cr_C E (u v) = u (cr_C E v) := by
      change (cr_C E * u) v = (u * cr_C E) v
      rw [casimir_commute_of_mem_Umon E hR u hu]
    simp [h1, casimir_apply_eq_smul_of_isHWV E hR ν v hH]
  have h := LinearMap.mem_ker.mp (hle hx)
  simpa [sub_eq_zero] using h

private lemma casimir_apply_eq_smul_of_mem_iSup_isotypic (E : GLOps n K V) (hR : SatisfiesGLRelations E) (Wx : (Fin n → ℤ) → Submodule K V) (c0 : ℤ) (z : V)
    (hz : z ∈ ⨆ ν ∈ {ν : Fin n → ℤ | cr_c ν = c0}, isotypicPartIn E (Wx ν) ν) : cr_C E z = (c0 : K) • z := by
  have hle : (⨆ ν ∈ {ν : Fin n → ℤ | cr_c ν = c0}, isotypicPartIn E (Wx ν) ν)
      ≤ LinearMap.ker (cr_C E - (c0 : K) • (1 : Module.End K V)) := by
    refine iSup₂_le fun ν hν => ?_
    intro x hx
    rw [LinearMap.mem_ker]
    have h := casimir_apply_eq_smul_of_mem_isotypicPartIn E hR (Wx ν) ν x hx
    rw [Set.mem_setOf_eq] at hν
    rw [hν] at h
    simp [h]
  have h := LinearMap.mem_ker.mp (hle hz)
  simpa [sub_eq_zero] using h

theorem casimir_polynomial_isolates_level [CharZero K] (E : GLOps n K V) (hR : SatisfiesGLRelations E) (Wx : (Fin n → ℤ) → Submodule K V) (z : V)
    (hz : z ∈ ⨆ ν, isotypicPartIn E (Wx ν) ν) (c0 : ℤ) : ∃ r : K[X], r.eval (c0 : K) = 1 ∧
      aeval (cr_C E) r z ∈ ⨆ ν ∈ {ν : Fin n → ℤ | cr_c ν = c0}, isotypicPartIn E (Wx ν) ν := by
  have hK2 : ∀ t ∈ (⨆ ν ∈ {ν : Fin n → ℤ | cr_c ν = c0}, isotypicPartIn E (Wx ν) ν), ∀ p : K[X],
      aeval (cr_C E) p t = p.eval (c0 : K) • t := fun t ht p =>
    aeval_apply_eq_eval_smul_of_eigenvector _ _ t (casimir_apply_eq_smul_of_mem_iSup_isotypic E hR Wx c0 t ht) p
  refine Submodule.iSup_induction (x := z) (fun ν => isotypicPartIn E (Wx ν) ν) hz ?_ ?_ ?_
  · intro ν x hx
    have hxC := casimir_apply_eq_smul_of_mem_isotypicPartIn E hR (Wx ν) ν x hx
    by_cases hc : cr_c ν = c0
    · refine ⟨1, by simp, ?_⟩
      have hm : x ∈ ⨆ ν ∈ {ν : Fin n → ℤ | cr_c ν = c0}, isotypicPartIn E (Wx ν) ν :=
        Submodule.mem_iSup_of_mem ν (Submodule.mem_iSup_of_mem hc hx)
      simpa using hm
    · have hne : (c0 : K) - (cr_c ν : K) ≠ 0 := by
        rw [sub_ne_zero]
        exact fun h => hc (Int.cast_injective h).symm
      refine ⟨Polynomial.C ((c0 : K) - cr_c ν)⁻¹ * (X - Polynomial.C (cr_c ν : K)), ?_, ?_⟩
      · rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X,
          Polynomial.eval_C]
        exact inv_mul_cancel₀ hne
      · rw [aeval_apply_eq_eval_smul_of_eigenvector _ _ x hxC]
        simp
  · exact ⟨1, by simp, by simp⟩
  · intro x y hx hy
    obtain ⟨r1, e1, m1⟩ := hx
    obtain ⟨r2, e2, m2⟩ := hy
    refine ⟨r1 * r2, by simp [e1, e2], ?_⟩
    rw [LinearMap.map_add (f := _)]
    refine add_mem ?_ ?_
    · rw [mul_comm, map_mul]
      change aeval (cr_C E) r2 (aeval (cr_C E) r1 x) ∈ _
      rw [hK2 _ m1]
      exact Submodule.smul_mem _ _ m1
    · rw [map_mul]
      change aeval (cr_C E) r1 (aeval (cr_C E) r2 y) ∈ _
      rw [hK2 _ m2]
      exact Submodule.smul_mem _ _ m2

theorem casimir_acts_scalar_on_level (E : GLOps n K V) (hR : SatisfiesGLRelations E) (Wx : (Fin n → ℤ) → Submodule K V) (c0 : ℤ) (z : V)
    (hz : z ∈ ⨆ ν ∈ {ν : Fin n → ℤ | cr_c ν = c0}, isotypicPartIn E (Wx ν) ν) : cr_C E z = (c0 : K) • z := by
  exact casimir_apply_eq_smul_of_mem_iSup_isotypic E hR Wx c0 z hz

theorem cr_Pos_zero_or {β : Fin n → ℤ} (h : β ∈ cr_Pos n) : β = 0 ∨ 0 < weightHeight' β := by
  unfold weightHeight'
  induction h using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨a, b, hab, rfl⟩ := hx
    right
    have e : (∑ i : Fin n, ((i : ℕ) : ℤ) * rootW a b i) = ((a : ℕ) : ℤ) - ((b : ℕ) : ℤ) := by
      simp [rootW, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
    rw [e]
    have hab' : (a : ℕ) < (b : ℕ) := hab
    omega
  | zero => left; rfl
  | add x y _ _ hx hy =>
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · left
      simp
    · right
      simpa using hy
    · right
      simpa using hx
    · right
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, neg_add]
      linarith

theorem casimir_isotypic_no_higher_weight [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (hR : SatisfiesGLRelations E)
    (Wx : (Fin n → ℤ) → Submodule K V) (mu : Fin n → ℤ) (hmu : Dominant mu) (ν' : Fin n → ℤ)
    (hν' : ν' - mu ∈ cr_Pos n) (hpos : 0 < weightHeight' (ν' - mu)) (z : V)
    (hz : z ∈ ⨆ ν ∈ {ν : Fin n → ℤ | cr_c ν = cr_c mu}, isotypicPartIn E (Wx ν) ν) (hzw : z ∈ weightSp E ν') : z = 0 := by
  by_contra hne
  have hle : (⨆ ν ∈ {ν : Fin n → ℤ | cr_c ν = cr_c mu}, isotypicPartIn E (Wx ν) ν) ≤
      cr_WS E {τ | ∃ ν, Dominant ν ∧ cr_c ν = cr_c mu ∧ ν - τ ∈ cr_Pos n} := by
    refine iSup₂_le fun ν hν x hx => ?_
    by_cases hx0 : x = 0
    · rw [hx0]; exact zero_mem _
    · have hd := cr_isoIn_dom E hR (Wx ν) hx hx0
      have hsub : weightsBelow ν ⊆ {τ | ∃ ν, Dominant ν ∧ cr_c ν = cr_c mu ∧ ν - τ ∈ cr_Pos n} :=
        fun τ hτ => ⟨ν, hd, hν, hτ⟩
      exact cr_WS_mono E hsub (isotypic_component_le_lower_weights E hR (Wx ν) ν hx)
  obtain ⟨ν, hd, hc, hp⟩ := cr_WS_mem E (hle hz) hzw hne
  have e : ν - mu = (ν - ν') + (ν' - mu) := by abel
  have h1 : ν - mu ∈ cr_Pos n := by rw [e]; exact add_mem hp hν'
  have h2 : 0 < weightHeight' (ν - mu) := by
    rw [e, cr_ht_add]
    have := cr_Pos_ht hp
    omega
  have := cr_c_lt hd hmu h1 h2
  omega

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open Finset Polynomial

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem cr_lift [CharZero K] (E : GLOps n K V) (hT : (⨆ ν, weightSp E ν) = ⊤) (W Z : Submodule K V)
    (hW : IsStableUnderOperators E W) (hZ : IsStableUnderOperators E Z) (mu : Fin n → ℤ) (x0 : V) (hx0 : x0 ∈ W)
    (hq : Z.mkQ x0 ∈ weightSp (cr_quot E Z hZ) mu) :
    ∃ x ∈ W, x ∈ weightSp E mu ∧ Z.mkQ x = Z.mkQ x0 := by
  classical
  have hg := v2rep_graded E W (fun a x hx => hW a a x hx) x0 hx0 (by rw [hT]; trivial)
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hg
  have hm : ∑ ν ∈ f.support, Z.mkQ (f ν) = Z.mkQ x0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hsum, Finsupp.sum, map_sum]
  have hc := v2rep_comp_mem (cr_quot E Z hZ) (weightSp (cr_quot E Z hZ) mu)
    (fun a x hx => cr_wt_diag_stable _ mu a x hx) f.support (fun ν => Z.mkQ (f ν))
    (fun ν _ => cr_quot_wt E Z hZ ν _ (hf ν).1) (by rw [hm]; exact hq)
  refine ⟨f mu, (hf mu).2, (hf mu).1, ?_⟩
  rw [← hm]
  symm
  refine Finset.sum_eq_single mu (fun ν hν hne => ?_) (fun hn => ?_)
  · exact cr_wt_disj _ hne (cr_quot_wt E Z hZ ν _ (hf ν).1) (hc ν hν)
  · rw [Finsupp.notMem_support_iff.1 hn, map_zero]

theorem cr_CR [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (hR : SatisfiesGLRelations E)
    (hT : (⨆ ν, weightSp E ν) = ⊤) (W : Submodule K V) (hW : IsStableUnderOperators E W) :
    W ≤ ⨆ mu, isotypicPartIn E W mu := by
  classical
  set W2 : Submodule K V := ⨆ mu, isotypicPartIn E W mu with hW2
  have hW2st : IsStableUnderOperators E W2 := v2rep_iSup_stable E _ fun mu => v2rep_isoIn_stable E W mu
  by_contra hnot
  have hZne : W.map W2.mkQ ≠ ⊥ := by
    intro h
    apply hnot
    have := (LinearMap.le_ker_iff_map (f := W2.mkQ) (p := W)).2 h
    rwa [Submodule.ker_mkQ] at this
  have hZst : IsStableUnderOperators (cr_quot E W2 hW2st) (W.map W2.mkQ) := by
    rintro a b y ⟨x, hx, rfl⟩
    exact ⟨E a b x, hW a b x hx, rfl⟩
  have hRq := cr_quot_rel E hR W2 hW2st
  obtain ⟨mu, xb, hxbZ, hxb⟩ := v2rep_exists_hwv (cr_quot E W2 hW2st) hRq (W.map W2.mkQ) hZst
    (le_top.trans (cr_quot_top E W2 hW2st hT)) hZne
  obtain ⟨x0, hx0W, rfl⟩ := hxbZ
  obtain ⟨x, hxW, hxwt, hxq⟩ := cr_lift E hT W W2 hW hW2st mu x0 hx0W hxb.2.1
  rw [← hxq] at hxb
  have hdom : Dominant mu := cr_hwv_dom _ hRq hxb
  have hxn : x ∉ W2 := fun h => hxb.1 ((Submodule.Quotient.mk_eq_zero W2).2 h)
  have hup : ∀ a b : Fin n, a < b → E a b x ∈ W2 := by
    intro a b hab
    have := hxb.2.2 a b hab
    rw [cr_quot_mk] at this
    exact (Submodule.Quotient.mk_eq_zero W2).1 this
  set T := cr_C E with hTdef
  have hTW2 : ∀ z ∈ W2, T z ∈ W2 := cr_C_stable E W2 hW2st
  have hy : T x - ((cr_c mu : ℤ) : K) • x ∈ W2 := by
    rw [hTdef, cr_C_wt E hR mu x hxwt, add_sub_cancel_left]
    refine W2.smul_mem _ (Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_)
    split_ifs with h
    · exact hW2st b a _ (hup a b h)
    · exact zero_mem _
  obtain ⟨q, hq1, hq2⟩ := casimir_polynomial_isolates_level E hR (fun _ => W) _ hy (cr_c mu)
  set x' := aeval T q x with hx'
  have h1 : x' - x ∈ W2 := by
    have := cr_aeval_mod T W2 hTW2 _ x hy q
    rwa [hq1, one_smul] at this
  have h2 : x' ∈ W := cr_aeval_stable T W (cr_C_stable E W hW) x hxW q
  have h3 : x' ∈ weightSp E mu := cr_aeval_stable T _ (cr_C_weightSp E hR mu) x hxwt q
  have h4 : x' ∉ W2 := by
    intro h
    apply hxn
    have : x = x' - (x' - x) := by abel
    rw [this]; exact W2.sub_mem h h1

  have hy0 : T x' - ((cr_c mu : ℤ) : K) • x' = aeval T q (T x - ((cr_c mu : ℤ) : K) • x) := by
    rw [map_sub, map_smul, cr_aeval_comm T T rfl q x]
  have hy0e : T (T x' - ((cr_c mu : ℤ) : K) • x') = ((cr_c mu : ℤ) : K) • (T x' - ((cr_c mu : ℤ) : K) • x') := by
    rw [hy0]
    exact casimir_acts_scalar_on_level E hR (fun _ => W) (cr_c mu) _ hq2
  have hzero : ∀ a b : Fin n, a < b → E a b x' = 0 := by
    intro a b hab
    set z := E a b x' with hz
    have hzW2 : z ∈ W2 := by
      have : z = E a b x + E a b (x' - x) := by rw [hz, ← map_add (f := _)]; congr 1; abel
      rw [this]; exact W2.add_mem (hup a b hab) (hW2st a b _ h1)
    have hzwt : z ∈ weightSp E (mu + rootW a b) := v2rep_shift E hR a b mu x' h3
    set w1 := T z - ((cr_c mu : ℤ) : K) • z with hw1
    have hw1' : w1 = E a b (T x' - ((cr_c mu : ℤ) : K) • x') := by
      rw [hw1, hz, map_sub, map_smul, hTdef, cr_C_comm_apply E hR]
    have hw1e : T w1 = ((cr_c mu : ℤ) : K) • w1 := by
      rw [hw1', hTdef, cr_C_comm_apply E hR, ← hTdef, hy0e, map_smul]
    obtain ⟨r, hr1, hr2⟩ := casimir_polynomial_isolates_level E hR (fun _ => W) z hzW2 (cr_c mu)
    have hz0 : aeval T r z = 0 := by
      refine casimir_isotypic_no_higher_weight E hR (fun _ => W) mu hdom (mu + rootW a b) ?_ ?_ _ hr2
        (cr_aeval_stable T _ (cr_C_weightSp E hR _) z hzwt r)
      · rw [add_sub_cancel_left]; exact cr_root_mem a b hab
      · rw [add_sub_cancel_left]; exact cr_ht_root a b hab
    have hspan : aeval T r z - r.eval (((cr_c mu : ℤ) : K)) • z ∈ Submodule.span K {w1} := by
      refine cr_aeval_mod T (Submodule.span K {w1}) ?_ _ z (Submodule.mem_span_singleton_self w1) r
      intro y hy
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [map_smul, hw1e, smul_comm]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w1))
    rw [hz0, hr1, one_smul, zero_sub] at hspan
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hspan
    have hzt : z = (-t) • w1 := by rw [neg_smul, ht, neg_neg]
    have hw0 : w1 = 0 := by
      have : T z = ((cr_c mu : ℤ) : K) • z := by rw [hzt, map_smul, hw1e, smul_comm]
      rw [hw1, this, sub_self]
    rw [hzt, hw0, smul_zero]
  apply h4
  have hne : x' ≠ 0 := fun h => h4 (by rw [h]; exact zero_mem _)
  exact Submodule.mem_iSup_of_mem mu (Submodule.subset_span ⟨1, one_mem _, x', h2, ⟨hne, h3, hzero⟩, rfl⟩)

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open Finset Polynomial

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def cr_Hs (E : GLOps n K V) (lam : Fin n → ℤ) : Submodule K V :=
  weightSp E lam ⊓ ⨅ a : Fin n, ⨅ b : Fin n, ⨅ (_ : a < b), LinearMap.ker (E a b)

theorem cr_mem_Hs (E : GLOps n K V) (lam : Fin n → ℤ) (x : V) :
    x ∈ cr_Hs E lam ↔ x ∈ weightSp E lam ∧ ∀ a b : Fin n, a < b → E a b x = 0 := by
  simp only [cr_Hs, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]

theorem cr_compl [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (hR : SatisfiesGLRelations E)
    (hT : (⨆ ν, weightSp E ν) = ⊤) (W : Submodule K V) (hW : IsStableUnderOperators E W) :
    ∃ W' : Submodule K V, IsCompl W W' ∧ IsStableUnderOperators E W' := by
  classical
  choose Q hQ using fun lam : Fin n → ℤ => Submodule.exists_isCompl (cr_Hs E lam ⊓ W)
  set H' : (Fin n → ℤ) → Submodule K V := fun lam => cr_Hs E lam ⊓ Q lam with hH'
  set W' : Submodule K V := ⨆ lam, isotypicPartIn E (H' lam) lam with hW'
  have hW'st : IsStableUnderOperators E W' := v2rep_iSup_stable E _ fun mu => v2rep_isoIn_stable E (H' mu) mu
  refine ⟨W', ⟨?_, ?_⟩, hW'st⟩
  ·
    rw [disjoint_iff]
    by_contra hne
    have hst : IsStableUnderOperators E (W ⊓ W') := fun a b x hx => ⟨hW a b x hx.1, hW'st a b x hx.2⟩
    obtain ⟨lam, w, hwm, hw⟩ := v2rep_exists_hwv E hR (W ⊓ W') hst (le_top.trans hT.ge) hne
    have hdl : Dominant lam := cr_hwv_dom E hR hw
    obtain ⟨r, hr1, hr2⟩ := casimir_polynomial_isolates_level E hR H' w hwm.2 (cr_c lam)
    rw [cr_aeval_eig (cr_C E) _ w (cr_C_hwv E hR lam w hw) r, hr1, one_smul] at hr2
    have hle : (⨆ ν ∈ {ν : Fin n → ℤ | cr_c ν = cr_c lam}, isotypicPartIn E (H' ν) ν) ≤
        H' lam ⊔ cr_WS E {τ | τ ≠ lam} := by
      refine iSup₂_le fun ν hν x hx => ?_
      by_cases hνl : ν = lam
      · subst hνl
        have hsub : cr_Low ν ⊆ {τ | τ ≠ ν} := by
          intro τ hτ h
          have h2 := hτ.2
          rw [h, sub_self, cr_ht_zero] at h2
          exact lt_irrefl _ h2
        exact (sup_le_sup inf_le_left (cr_WS_mono E hsub)) (cr_isoIn_le E hR (H' ν) ν hx)
      · by_cases hx0 : x = 0
        · rw [hx0]; exact zero_mem _
        · have hd := cr_isoIn_dom E hR (H' ν) hx hx0
          have hsub : weightsBelow ν ⊆ {τ | τ ≠ lam} := by
            intro τ hτ h
            have hτ' : ν - τ ∈ cr_Pos n := hτ
            rw [h] at hτ'
            rcases cr_Pos_zero_or hτ' with h0 | h0
            · exact hνl (sub_eq_zero.1 h0)
            · have := cr_c_lt hd hdl hτ' h0
              have hν' : cr_c ν = cr_c lam := hν
              omega
          exact Submodule.mem_sup_right (cr_WS_mono E hsub (isotypic_component_le_lower_weights E hR (H' ν) ν hx))
    obtain ⟨h, hh, l, hl, hsum⟩ := Submodule.mem_sup.1 (hle hr2)
    have hhw : h ∈ weightSp E lam := ((cr_mem_Hs E lam h).1 hh.1).1
    have hl0 : l = 0 := by
      by_contra hl0
      have hlw : l ∈ weightSp E lam := by
        have : l = w - h := by rw [← hsum]; abel
        rw [this]; exact Submodule.sub_mem _ hw.2.1 hhw
      exact (cr_WS_mem E hl hlw hl0) rfl
    rw [hl0, add_zero] at hsum
    rw [hsum] at hh
    have hwHs : w ∈ cr_Hs E lam ⊓ W := ⟨hh.1, hwm.1⟩
    have := (hQ lam).disjoint.le_bot ⟨hwHs, hh.2⟩
    exact hw.1 ((Submodule.mem_bot K).1 this)
  ·
    rw [codisjoint_iff, eq_top_iff]
    refine (cr_CR E hR hT ⊤ (fun _ _ _ _ => trivial)).trans (iSup_le fun mu => ?_)
    refine Submodule.span_le.2 ?_
    rintro x ⟨u, hu, v, _, hv, rfl⟩
    have hvHs : v ∈ cr_Hs E mu := (cr_mem_Hs E mu v).2 ⟨hv.2.1, hv.2.2⟩
    have hvt : v ∈ (cr_Hs E mu ⊓ W) ⊔ Q mu := by rw [(hQ mu).sup_eq_top]; trivial
    obtain ⟨v1, hv1, v2, hv2, rfl⟩ := Submodule.mem_sup.1 hvt
    have hv2Hs : v2 ∈ cr_Hs E mu := by
      have : v2 = (v1 + v2) - v1 := by abel
      rw [this]; exact Submodule.sub_mem _ hvHs hv1.1
    show u (v1 + v2) ∈ W ⊔ W'
    rw [map_add (f := _)]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (v2rep_Umon_stable E W hW u hu v1 hv1.2))
      (Submodule.mem_sup_right ?_)
    by_cases h0 : v2 = 0
    · rw [h0, map_zero]; exact zero_mem _
    · have h2 := (cr_mem_Hs E mu v2).1 hv2Hs
      exact Submodule.mem_iSup_of_mem mu (Submodule.subset_span ⟨u, hu, v2, ⟨hv2Hs, hv2⟩, ⟨h0, h2.1, h2.2⟩, rfl⟩)

theorem weight_condition_from_integral_form (D : Formalism.BasicNotions.D7) : adm2 D := by
  intro K V _ _ _ _ _ n E hE W hW
  exact cr_compl E hE.1 hE.2.2 W hW

end Formalism.MainNotions.G.GLWeightTheory
