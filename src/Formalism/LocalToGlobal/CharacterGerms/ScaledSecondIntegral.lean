module

public import Formalism.LocalToGlobal.CharacterGerms.GeNatCast

@[expose] public section

section -- merged from Formalism.LocalToGlobal.CharacterGerms.ScaledSecondIntegral
namespace Formalism.L2.FormalSeriesBounds

open Finset

noncomputable section

variable {C : Type*} [Field C] {V : VF C} {d : ℕ} {I J : Type*}

section Ops

variable {N : Type*}

theorem Vpow_zero (x : ℕ → N → C) : Vpow 0 x = x := by
  funext i n
  simp [Vpow]

theorem Vpow_succ (s : ℕ) (x : ℕ → N → C) : Vpow (s + 1) x = Vpow 1 (Vpow s x) := by
  funext i n
  simp only [Vpow]
  split_ifs <;> first | rfl | omega | (congr 1; omega)

end Ops

namespace Cart

variable (X : Cart V d I J)

theorem Vpow_mem (s : ℕ) {x : ℕ → I ⊕ J → C} (hx : x ∈ X.Ty) : Vpow s x ∈ X.Ty := by
  induction s with
  | zero => rw [Vpow_zero]; exact hx
  | succ s ih => rw [Vpow_succ]; exact X.V_mem _ ih

theorem bound0 : ∀ (i : ℕ) (x : ℕ → I ⊕ J → C), x ∈ X.Ty → ∀ n, V.Ge (-(i : ℝ)) (x i n) := by
  intro i
  induction i with
  | zero =>
    intro x hx n
    simpa using X.t2 x hx 0 (fun j hj => absurd hj (Nat.not_lt_zero j)) n
  | succ i ih =>
    intro x hx n
    have := (ih _ (X.F_mem x hx) n).of_l_mul
    exact this.mono (by push_cast; linarith)

def IsCurve (a : ZMod d) (u : I → C) (x : ℕ → I ⊕ J → C) : Prop :=
  x ∈ X.Ty ∧ x 0 = Sum.elim u 0 ∧ ∀ (i : ℕ) n, X.ty n ≠ a + i → x i n = 0

section Std

variable [DecidableEq I]

theorem exists_std (b : I) : ∃ x, X.IsCurve (X.ty (Sum.inl b)) (Pi.single b 1) x := by
  have hu : ∀ c, V.Ge 0 ((Pi.single b (1 : C) : I → C) c) := by
    intro c
    by_cases hc : c = b
    · subst hc
      simpa using (VF.Ge.one (V := V))
    · simpa [Pi.single_apply, hc] using (VF.Ge.zero (V := V) 0)
  have hty : ∀ c, X.ty (Sum.inl c) ≠ X.ty (Sum.inl b) → (Pi.single b (1 : C) : I → C) c = 0 := by
    intro c hc
    have : c ≠ b := fun h => hc (h ▸ rfl)
    simp [Pi.single_apply, this]
  obtain ⟨x, hx, h0, h1⟩ := X.t4 _ _ hu hty
  exact ⟨x, hx, h0, h1⟩

def std (b : I) : ℕ → I ⊕ J → C := Classical.choose (X.exists_std b)

theorem std_spec (b : I) : X.IsCurve (X.ty (Sum.inl b)) (Pi.single b 1) (X.std b) :=
  Classical.choose_spec (X.exists_std b)

variable [Fintype I]

def lift (h : I ⊕ J → C) : ℕ → I ⊕ J → C :=
  (∑ b, teich V.l (h (Sum.inl b)) (X.std b)) + const0 (Sum.elim 0 (fun j => h (Sum.inr j)))

theorem lift_mem {h : I ⊕ J → C} (hh : ∀ n, V.Ge 0 (h n)) : X.lift h ∈ X.Ty := by
  unfold lift
  exact X.Ty.add_mem (X.Ty.sum_mem fun b _ => X.teich_mem _ (hh _) _ (X.std_spec b).1)
    (X.t3 _ fun j => hh _)

theorem lift_apply (h : I ⊕ J → C) (i : ℕ) (n : I ⊕ J) : X.lift h i n =
    (∑ b, h (Sum.inl b) ^ (V.l ^ i) * X.std b i n) +
      const0 (Sum.elim 0 (fun j => h (Sum.inr j))) i n := by
  simp only [lift, Pi.add_apply, Finset.sum_apply, teich]

theorem lift_zero (h : I ⊕ J → C) : X.lift h 0 = h := by
  funext n
  rw [lift_apply]
  simp only [pow_zero, pow_one, (X.std_spec _).2.1, const0, if_pos rfl]
  cases n with
  | inl b' => simp [Pi.single_apply]
  | inr j => simp

theorem boundS : ∀ (i s : ℕ) (x : ℕ → I ⊕ J → C), x ∈ X.Ty → (∀ j < s, x j = 0) →
    ∀ n, V.Ge (-(i : ℝ)) (x (s + i) n) := by
  intro i
  induction i with
  | zero =>
    intro s x hx hz n
    simpa using X.t2 x hx s hz n
  | succ i ih =>
    intro s x hx hz n
    have hint : ∀ m, V.Ge 0 (x s m) := X.t2 x hx s hz
    have hL := X.lift_mem hint
    have hx' : x - Vpow s (X.lift (x s)) ∈ X.Ty := X.Ty.sub_mem hx (X.Vpow_mem s hL)
    have hz' : ∀ j < s + 1, (x - Vpow s (X.lift (x s))) j = 0 := by
      intro j hj
      funext m
      simp only [Pi.sub_apply, Pi.zero_apply, Vpow]
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with h | h
      · rw [if_pos h, hz j h]
        simp
      · subst h
        rw [if_neg (lt_irrefl _), Nat.sub_self, X.lift_zero, sub_self]
    have h1 := ih (s + 1) _ hx' hz' n
    have h2 := X.bound0 (i + 1) _ hL n
    have hsplit : x (s + (i + 1)) n =
        (x - Vpow s (X.lift (x s))) (s + 1 + i) n + X.lift (x s) (i + 1) n := by
      simp only [Pi.sub_apply, Vpow]
      rw [if_neg (by omega), show s + 1 + i - s = i + 1 by omega, show s + 1 + i = s + (i + 1) by omega]
      ring
    rw [hsplit]
    exact (h1.mono (by push_cast; linarith)).add h2

end Std

def Good (a : ZMod d) (u : I → C) (x : ℕ → I ⊕ J → C) : Prop :=
  X.IsCurve a u x ∧ ∀ c, x 1 (Sum.inl c) = 0

def V2 (_X : Cart V d I J) (x : ℕ → I ⊕ J → C) : I → C := fun b => (V.l : C) * x 2 (Sum.inl b)

def c0' (_X : Cart V d I J) (x : ℕ → I ⊕ J → C) : J → C := fun j => (V.l : C) * x 1 (Sum.inr j)

variable {X}

theorem Good.bound [DecidableEq I] [Fintype I] {a : ZMod d} {u : I → C} {x : ℕ → I ⊕ J → C}
    (h : X.Good a u x) (i : ℕ) (n : I ⊕ J) : V.Ge (-((i : ℝ) + 1)) (x (i + 2) n) := by
  have hx := h.1.1
  have hF := X.F_mem _ hx
  have hζ : ∀ j, V.Ge 0 ((V.l : C) * x 1 (Sum.inr j)) := fun j => by
    have := X.t2 _ hF 0 (fun _ h => absurd h (Nat.not_lt_zero _)) (Sum.inr j)
    exact this
  have hw : Fs V.l x - const0 (Sum.elim 0 (fun j => (V.l : C) * x 1 (Sum.inr j))) ∈ X.Ty :=
    X.Ty.sub_mem hF (X.t3 _ hζ)
  have hw0 : ∀ j < 1, (Fs V.l x - const0 (Sum.elim 0 (fun j => (V.l : C) * x 1 (Sum.inr j))) :
      ℕ → I ⊕ J → C) j = 0 := by
    intro j hj
    obtain rfl : j = 0 := by omega
    funext m
    cases m with
    | inl c => simp [Fs, const0, h.2 c]
    | inr k => simp [Fs, const0]
  have hb := X.boundS i 1 _ hw hw0 n
  have he : (Fs V.l x - const0 (Sum.elim 0 (fun j => (V.l : C) * x 1 (Sum.inr j))) :
      ℕ → I ⊕ J → C) (1 + i) n =
      (V.l : C) * x (i + 2) n := by
    simp only [Pi.sub_apply, Fs, const0]
    rw [if_neg (by omega), sub_zero, show 1 + i + 1 = i + 2 by omega]
  rw [he] at hb
  exact hb.of_l_mul.mono (by linarith)

theorem Good.bound_one {a : ZMod d} {u : I → C} {x : ℕ → I ⊕ J → C}
    (h : X.Good a u x) (n : I ⊕ J) : V.Ge (-1) (x 1 n) := by
  have := X.t2 _ (X.F_mem _ h.1.1) 0 (fun i hi => absurd hi (Nat.not_lt_zero i)) n
  have h2 : V.Ge 0 ((V.l : C) * x 1 n) := this
  exact h2.of_l_mul.mono (by norm_num)

theorem Good.c0'_int {a : ZMod d} {u : I → C} {x : ℕ → I ⊕ J → C}
    (h : X.Good a u x) (j : J) : V.Ge 0 (X.c0' x j) := by
  have := X.t2 _ (X.F_mem _ h.1.1) 0 (fun i hi => absurd hi (Nat.not_lt_zero i)) (Sum.inr j)
  exact this

theorem Good.comb {ι : Type*} (s : Finset ι) {a : ZMod d} {u : ι → I → C}
    {x : ι → ℕ → I ⊕ J → C} {co : ι → C} (hco : ∀ k ∈ s, V.Ge 0 (co k))
    (h : ∀ k ∈ s, X.Good a (u k) (x k)) :
    X.Good a (∑ k ∈ s, co k • u k) (∑ k ∈ s, teich V.l (co k) (x k)) := by
  refine And.intro (And.intro ?_ (And.intro ?_ ?_)) ?_
  · exact X.Ty.sum_mem fun k hk => X.teich_mem _ (hco k hk) _ (h k hk).1.1
  · funext n
    simp only [Finset.sum_apply, teich, pow_zero, pow_one]
    calc ∑ k ∈ s, co k * x k 0 n = ∑ k ∈ s, co k * Sum.elim (u k) 0 n :=
          Finset.sum_congr rfl fun k hk => by rw [(h k hk).1.2.1]
      _ = _ := by cases n <;> simp [Finset.sum_apply]
  · intro i n hn
    simp only [Finset.sum_apply, teich]
    exact Finset.sum_eq_zero fun k hk => by rw [(h k hk).1.2.2 i n hn, mul_zero]
  · intro c
    simp only [Finset.sum_apply, teich]
    exact Finset.sum_eq_zero fun k hk => by rw [(h k hk).2 c, mul_zero]

theorem scaledSecond_sum {ι : Type*} (s : Finset ι) (x : ι → ℕ → I ⊕ J → C) (co : ι → C) (b : I) :
    X.V2 (∑ k ∈ s, teich V.l (co k) (x k)) b = ∑ k ∈ s, co k ^ (V.l ^ 2) * X.V2 (x k) b := by
  simp only [V2, Finset.sum_apply, teich, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem c0'_comb {ι : Type*} (s : Finset ι) (x : ι → ℕ → I ⊕ J → C) (co : ι → C) (j : J) :
    X.c0' (∑ k ∈ s, teich V.l (co k) (x k)) j = ∑ k ∈ s, co k ^ V.l * X.c0' (x k) j := by
  simp only [c0', Finset.sum_apply, teich, pow_one, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

end Cart

end

end Formalism.L2.FormalSeriesBounds
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePSplitLA
namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePSplit

open Polynomial Matrix

section Sep

variable {K : Type} [Field K] [CharZero K]

theorem aff_sub (α β : K) (h : α ≠ 0 ∨ β ≠ 0) : {t : ℕ | α + (t : K) * β = 0}.Subsingleton := by
  intro t1 h1 t2 h2
  simp only [Set.mem_setOf_eq] at h1 h2
  by_cases hb : β = 0
  · rw [hb, mul_zero, add_zero] at h1
    exact absurd h1 (h.resolve_right (not_not.mpr hb))
  · have h3 : ((t1 : K) - t2) * β = 0 := by linear_combination h1 - h2
    have h4 : (t1 : K) = t2 := sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hb)
    exact_mod_cast h4

theorem exists_sep {O : Type} [CommRing O] {ι : Type} [Fintype ι] (em : ι → (O →+* K))
    (hem : Function.Injective em) : ∃ x0 : O, ∀ c c', c ≠ c' → em c x0 ≠ em c' x0 := by
  classical
  have key : ∀ F : Finset (ι × ι), (∀ q ∈ F, q.1 ≠ q.2) → ∃ x0 : O, ∀ q ∈ F, em q.1 x0 ≠ em q.2 x0 := by
    intro F
    induction F using Finset.induction_on with
    | empty => intro _; exact ⟨0, by simp⟩
    | insert p F _ ih =>
      intro hF
      obtain ⟨x, hx⟩ := ih fun q hq => hF q (Finset.mem_insert_of_mem hq)
      obtain ⟨z, hz⟩ : ∃ z, em p.1 z ≠ em p.2 z := by
        by_contra h
        push Not at h
        exact hF p (Finset.mem_insert_self p F) (hem (RingHom.ext h))
      have hfin : (⋃ q ∈ ((↑(insert p F) : Set (ι × ι))),
          {t : ℕ | (em q.1 x - em q.2 x) + (t : K) * (em q.1 z - em q.2 z) = 0}).Finite := by
        refine Set.Finite.biUnion (Finset.finite_toSet _) fun q hq => (aff_sub _ _ ?_).finite
        rcases Finset.mem_insert.1 (Finset.mem_coe.1 hq) with rfl | hq'
        · exact Or.inr (sub_ne_zero.2 hz)
        · exact Or.inl (sub_ne_zero.2 (hx q hq'))
      obtain ⟨t, ht⟩ := hfin.infinite_compl.nonempty
      refine ⟨x + (t : O) * z, fun q hq h => ht (Set.mem_biUnion (Finset.mem_coe.2 hq) ?_)⟩
      simp only [Set.mem_ofPred_eq]
      simp only [map_add (f := _), map_mul, map_natCast] at h
      linear_combination h
  obtain ⟨x0, hx0⟩ := key (Finset.univ.filter fun q : ι × ι => q.1 ≠ q.2)
    (fun q hq => (Finset.mem_filter.1 hq).2)
  exact ⟨x0, fun c c' hcc' => hx0 (c, c') (Finset.mem_filter.2 ⟨Finset.mem_univ _, hcc'⟩)⟩

end Sep

section Mat

variable {K : Type} [Field K] {n : ℕ}

theorem alg_mulVec (a : K) (A : Matrix (Fin n) (Fin n) K) (w : Fin n → K) :
    (algebraMap K (Matrix (Fin n) (Fin n) K) a * A) *ᵥ w = a • (A *ᵥ w) := by
  rw [← Algebra.smul_def, Matrix.smul_mulVec]

theorem alg_mulVec1 (a : K) (w : Fin n → K) :
    algebraMap K (Matrix (Fin n) (Fin n) K) a *ᵥ w = a • w := by
  rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem commute_aeval {A B : Matrix (Fin n) (Fin n) K} (h : Commute A B) (f : K[X]) : Commute A (aeval B f) := by
  induction f using Polynomial.induction_on with
  | C a =>
    rw [aeval_C]
    exact (Algebra.commutes a A).symm
  | add p q hp hq =>
    rw [map_add (f := _)]
    exact hp.add_right hq
  | monomial k a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
    exact ih.mul_right h

theorem pow_shift (N B : Matrix (Fin n) (Fin n) K) (hNB : Commute N B) (lam : K) (w : Fin n → K)
    (hw : N *ᵥ w = lam • w) (k : ℕ) :
    (N + B) ^ k *ᵥ w = (algebraMap K (Matrix (Fin n) (Fin n) K) lam + B) ^ k *ᵥ w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih,
      Matrix.add_mulVec, Matrix.add_mulVec]
    congr 1
    have hc : Commute N ((algebraMap K (Matrix (Fin n) (Fin n) K) lam + B) ^ k) :=
      ((show Commute (algebraMap K (Matrix (Fin n) (Fin n) K) lam) N from Algebra.commutes lam N).symm.add_right
        hNB).pow_right k
    rw [Matrix.mulVec_mulVec, hc.eq, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul, alg_mulVec1]

theorem aeval_shift (N B : Matrix (Fin n) (Fin n) K) (hNB : Commute N B) (lam : K) (w : Fin n → K)
    (hw : N *ᵥ w = lam • w) (f : K[X]) :
    aeval (N + B) f *ᵥ w = aeval (algebraMap K (Matrix (Fin n) (Fin n) K) lam + B) f *ᵥ w := by
  induction f using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), Matrix.add_mulVec, Matrix.add_mulVec, hp, hq]
  | monomial k a _ =>
    rw [map_mul, map_mul, aeval_C, aeval_C, map_pow, map_pow, aeval_X, aeval_X, alg_mulVec, alg_mulVec,
      pow_shift N B hNB lam w hw (k + 1)]

theorem X_sub_mul_basis {ι : Type} [DecidableEq ι] {s : Finset ι} {v : ι → K} {i : ι} (hi : i ∈ s) :
    (X - Polynomial.C (v i)) * Lagrange.basis s v i =
      Polynomial.C (Lagrange.nodalWeight s v i) * Lagrange.nodal s v := by
  rw [Lagrange.nodal_eq_mul_nodal_erase hi]
  simp only [Lagrange.basis, Lagrange.basisDivisor, Finset.prod_mul_distrib, Lagrange.nodalWeight, Lagrange.nodal,
    map_prod]
  ring

theorem coeff_extract [CharZero K] {ι : Type} [Fintype ι] [DecidableEq ι] (B : Matrix (Fin n) (Fin n) K)
    (w : Fin n → K) (a μ : ι → K) (c : ι) (hac : a c = 0) (ha : ∀ c', c' ≠ c → a c' ≠ 0)
    (h : ∀ t : ℕ, aeval B (∏ c', (Polynomial.C (a c') + Polynomial.C (t : K) * (X - Polynomial.C (μ c')))) *ᵥ w = 0) :
    B *ᵥ w = μ c • w := by
  set R : K[X][X] := ∏ c', (Polynomial.C (Polynomial.C (a c')) + X * Polynomial.C (X - Polynomial.C (μ c'))) with hR
  have hev : ∀ t : ℕ, R.eval (Polynomial.C (t : K)) =
      ∏ c', (Polynomial.C (a c') + Polynomial.C (t : K) * (X - Polynomial.C (μ c'))) := by
    intro t
    rw [hR, eval_prod]
    refine Finset.prod_congr rfl fun c' _ => ?_
    rw [eval_add, eval_C, eval_mul, eval_X, eval_C]
  have hcoord : ∀ i, (aeval B (R.coeff 1) *ᵥ w) i = 0 := by
    intro i
    set q : K[X] := ∑ k ∈ Finset.range (R.natDegree + 2), monomial k ((aeval B (R.coeff k) *ᵥ w) i) with hq
    have hroot : ∀ t : ℕ, q.eval (t : K) = 0 := by
      intro t
      have h1 := congrFun (h t) i
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hev t, eval_eq_sum_range' (n := R.natDegree + 2) (by omega), map_sum, Matrix.sum_mulVec,
        Finset.sum_apply, Pi.zero_apply] at h1
      rw [hq, eval_finsetSum]
      refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) h1
      rw [eval_monomial, ← map_pow, map_mul, aeval_C, ← Algebra.commutes, alg_mulVec, Pi.smul_apply, smul_eq_mul,
        mul_comm]
    have hq0 : q = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (Nat.cast_injective (R := K)))
      rintro _ ⟨t, rfl⟩
      exact hroot t
    have hc1 := congrArg (fun p : K[X] => p.coeff 1) hq0
    simp only [hq, finsetSum_coeff, coeff_monomial_apply, Finset.sum_ite_eq', Finset.mem_range, coeff_zero] at hc1
    rw [if_pos (by omega)] at hc1
    exact hc1
  have hR1 : R.coeff 1 = (X - Polynomial.C (μ c)) * Polynomial.C (∏ c' ∈ Finset.univ.erase c, a c') := by
    rw [hR, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c), hac, map_zero, map_zero, zero_add, mul_assoc]
    refine (coeff_X_mul _ 0).trans ?_
    rw [coeff_C_mul, coeff_zero_eq_eval_zero, eval_prod, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun c' _ => ?_
    rw [eval_add, eval_C, eval_mul, eval_X, zero_mul, add_zero]
  have hπ : ∏ c' ∈ Finset.univ.erase c, a c' ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun c' hc' => ha c' (Finset.ne_of_mem_erase hc')
  have hv : aeval B (R.coeff 1) *ᵥ w = 0 := funext hcoord
  rw [hR1, map_mul, aeval_C, ← Algebra.commutes, alg_mulVec, map_sub, aeval_X, aeval_C, Matrix.sub_mulVec,
    alg_mulVec1] at hv
  have h2 := (smul_eq_zero.1 hv).resolve_left hπ
  rwa [sub_eq_zero] at h2

end Mat

theorem split_holds : SplitSt := by
  intro K _ _ O _ n ι _ _ M P em hPP hPM hinj hann v
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hP : P = 0 := by
      have h := hann 0
      rw [Finset.univ_eq_empty, Finset.prod_empty, map_one, one_mul] at h
      exact h
    refine ⟨fun c => (hι.false c).elim, ?_, fun c => (hι.false c).elim⟩
    rw [hP, Matrix.zero_mulVec, Finset.univ_eq_empty, Finset.sum_empty]
  obtain ⟨x0, hx0⟩ := exists_sep em hinj
  have hinjl : Set.InjOn (fun c => em c x0) (Finset.univ : Finset ι) := fun c _ c' _ h => by
    by_contra hne
    exact hx0 c c' hne h
  refine ⟨fun c => P *ᵥ (aeval (M x0) (Lagrange.basis Finset.univ (fun c => em c x0) c) *ᵥ v), ?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [← Matrix.mulVec_sum, ← Matrix.sum_mulVec, ← map_sum, Lagrange.sum_basis hinjl Finset.univ_nonempty, map_one,
      Matrix.one_mulVec]
  intro c x
  set u := aeval (M x0) (Lagrange.basis Finset.univ (fun c => em c x0) c) *ᵥ v with hu
  have hP0 : Commute P (M x0) := hPM x0

  have hXL : (X - Polynomial.C (em c x0)) * Lagrange.basis Finset.univ (fun c => em c x0) c =
      Polynomial.C (Lagrange.nodalWeight Finset.univ (fun c => em c x0) c) * ∏ c', (X - Polynomial.C (em c' x0)) :=
    by
      simpa only [Lagrange.nodal_eq] using
        (X_sub_mul_basis (v := fun c' => em c' x0) (Finset.mem_univ c))
  have hE0 : (M x0 - algebraMap K _ (em c x0)) *
      (P * aeval (M x0) (Lagrange.basis Finset.univ (fun c => em c x0) c)) = 0 := by
    have e1 : M x0 - algebraMap K (Matrix (Fin n) (Fin n) K) (em c x0) = aeval (M x0) (X - Polynomial.C (em c x0)) := by
      rw [map_sub, aeval_X, aeval_C]
    rw [e1, ← mul_assoc, ← (commute_aeval hP0 _).eq, mul_assoc, ← map_mul, hXL, map_mul, aeval_C, ← mul_assoc,
      ← Algebra.commutes, mul_assoc, (commute_aeval hP0 _).eq, hann x0, mul_zero]
  have hw0 : M x0 *ᵥ (P *ᵥ u) = em c x0 • (P *ᵥ u) := by
    have h1 := congrArg (fun A => A *ᵥ v) hE0
    simp only [Matrix.zero_mulVec] at h1
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, alg_mulVec1, sub_eq_zero] at h1
    exact h1

  refine coeff_extract (M x) (P *ᵥ u) (fun c' => em c x0 - em c' x0) (fun c' => em c' x) c (sub_self _)
    (fun c' hc' => sub_ne_zero.2 (hx0 c c' (Ne.symm hc'))) fun t => ?_
  have hcx : Commute (M x0) ((t : Matrix (Fin n) (Fin n) K) * M x) := by
    refine ((Nat.cast_commute t (M x0)).symm).mul_right ?_
    show M x0 * M x = M x * M x0
    rw [← map_mul, ← map_mul, mul_comm]
  have h1 := congrArg (fun A => A *ᵥ u) (hann (x0 + (t : O) * x))
  simp only [Matrix.zero_mulVec] at h1
  rw [← Matrix.mulVec_mulVec, map_add (f := _), map_mul, map_natCast, aeval_shift _ _ hcx (em c x0) _ hw0] at h1
  have e2 : algebraMap K (Matrix (Fin n) (Fin n) K) (em c x0) + (t : Matrix (Fin n) (Fin n) K) * M x =
      aeval (M x) (Polynomial.C (em c x0) + Polynomial.C (t : K) * X) := by
    rw [map_add (f := _), map_mul, aeval_C, aeval_C, aeval_X, map_natCast]
  rw [e2, ← aeval_comp, prod_comp] at h1
  refine Eq.trans ?_ h1
  congr 2
  refine Finset.prod_congr rfl fun c' _ => ?_
  rw [sub_comp, X_comp, C_comp]
  simp only [map_add (f := _), map_mul, map_natCast, map_sub]
  ring

end RowTiePSplit

end Formalism.L2.FormalSeriesBounds
end
