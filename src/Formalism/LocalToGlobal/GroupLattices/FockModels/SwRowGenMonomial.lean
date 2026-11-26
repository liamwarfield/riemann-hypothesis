module

public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LEhwLemmas

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GroupLattices.FockModels.SwRowDivZero
open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.GradedWeylDivisibility

variable (R : Type) [CommRing R] {r n : ℕ}

def Dop (a b : Fin r) :
    Derivation R (MvPolynomial (Fin r × Fin n) R) (MvPolynomial (Fin r × Fin n) R) :=
  mkDerivation R fun v => if v.1 = b then X (a, v.2) else 0

theorem Dop_X (a b : Fin r) (v : Fin r × Fin n) :
    Dop R a b (X v) = if v.1 = b then X (a, v.2) else 0 :=
  MvPolynomial.mkDerivation_X R _ v

def DL (a b : Fin r) : Module.End R (MvPolynomial (Fin r × Fin n) R) := (Dop R a b).toLinearMap

theorem DL_apply (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) R) : DL R a b f = Dop R a b f := rfl

theorem sw_rowGen_X (a b : Fin r) (v : Fin r × Fin n) :
    rowGen R a b (X v) = Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) := by
  exact rowGen_X R a b v

theorem sw_rowGen_C (a b : Fin r) (c : R) :
    rowGen R a b (C c : MvPolynomial (Fin r × Fin n) R) = Polynomial.C (C c) := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Polynomial.algebraMap_apply,
    MvPolynomial.algebraMap_eq]

theorem sw_deriv (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) R) :
    (1 + if a = b then Polynomial.X else 0) * Polynomial.derivative (rowGen R a b f) =
      rowGen R a b (Dop R a b f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    rw [sw_rowGen_C, Polynomial.derivative_C, mul_zero, MvPolynomial.derivation_C, map_zero]
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), mul_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.derivative_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add (f := _),
      map_mul, map_mul, ← hp, Dop_X, sw_rowGen_X]
    by_cases h1 : v.1 = b <;> by_cases h2 : a = b <;>
      simp only [h1, h2, if_true, if_false, sw_rowGen_X, map_zero, mul_zero, zero_mul, add_zero,
        Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_mul,
        Polynomial.derivative_X, zero_add, one_mul, mul_one, Polynomial.derivative_zero] <;> ring

theorem sw_rowDiv_zero (a b : Fin r) (g : MvPolynomial (Fin r × Fin n) R) : rowDiv R a b 0 g = g := by
  unfold rowDiv
  induction g using MvPolynomial.induction_on with
  | C c => rw [sw_rowGen_C, Polynomial.coeff_C_zero]
  | add p q hp hq => rw [map_add (f := _), Polynomial.coeff_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.mul_coeff_zero, hp, sw_rowGen_X]
    split_ifs <;> simp

theorem sw_step_ne (a b : Fin r) (hab : a ≠ b) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R) :
    ((k + 1 : ℕ) : R) • rowDiv R a b (k + 1) f = rowDiv R a b k (Dop R a b f) := by
  have h := sw_deriv R a b f
  rw [if_neg hab, add_zero, one_mul] at h
  unfold rowDiv
  rw [← h, Polynomial.coeff_derivative, MvPolynomial.smul_eq_C_mul, mul_comm]
  congr 1
  simp

theorem sw_step_eq (a : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R) :
    ((k + 1 : ℕ) : R) • rowDiv R a a (k + 1) f =
      rowDiv R a a k (Dop R a a f) - (k : R) • rowDiv R a a k f := by
  have h := sw_deriv R a a f
  rw [if_pos rfl] at h
  unfold rowDiv
  rw [← h, add_mul, one_mul, Polynomial.coeff_add]
  cases k with
  | zero =>
    rw [Polynomial.coeff_X_mul_zero, add_zero, Polynomial.coeff_derivative]
    simp [MvPolynomial.smul_eq_C_mul, mul_comm]
  | succ k =>
    rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative, Polynomial.coeff_derivative]
    simp only [MvPolynomial.smul_eq_C_mul]
    push_cast
    simp only [map_add (f := _), map_natCast, map_one]
    ring

theorem sw_pow_ne (a b : Fin r) (hab : a ≠ b) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R) :
    ((k.factorial : ℕ) : R) • rowDiv R a b k f = (DL R a b ^ k) f := by
  induction k generalizing f with
  | zero => simp [sw_rowDiv_zero]
  | succ k ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, mul_comm, mul_smul, sw_step_ne R a b hab k f, ih,
      pow_succ, Module.End.mul_apply, DL_apply]

theorem sw_pow_eq (a : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R) :
    ((k.factorial : ℕ) : R) • rowDiv R a a k f =
      (((List.range k).map fun j : ℕ => DL R (n := n) a a -
        (j : R) • (1 : Module.End R (MvPolynomial (Fin r × Fin n) R))).prod) f := by
  induction k generalizing f with
  | zero => simp [sw_rowDiv_zero]
  | succ k ih =>
    have step : ((k + 1 : ℕ) : R) • rowDiv R a a (k + 1) f =
        rowDiv R a a k ((DL R (n := n) a a - (k : R) • (1 : Module.End R (MvPolynomial (Fin r × Fin n) R))) f) := by
      rw [sw_step_eq R a k f, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, DL_apply,
        sub_eq_add_neg ((Dop R a a) f), rowDiv_add, ← neg_smul, rowDiv_smul, neg_smul, sub_eq_add_neg]
    rw [Nat.factorial_succ, Nat.cast_mul, mul_comm, mul_smul, step, ih, List.range_succ,
      List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, Module.End.mul_apply]

theorem sw_rel (a b c d : Fin r) :
    DL R (n := n) a b * DL R c d - DL R c d * DL R a b =
      (if b = c then DL R a d else 0) - (if d = a then DL R c b else 0) := by
  have hder : ⁅Dop R (n := n) a b, Dop R (n := n) c d⁆ =
      (if b = c then Dop R (n := n) a d else 0) - (if d = a then Dop R (n := n) c b else 0) := by
    apply MvPolynomial.derivation_ext
    intro v
    rw [Derivation.commutator_apply, Dop_X, Dop_X, apply_ite (Dop R (n := n) a b),
      apply_ite (Dop R (n := n) c d), map_zero, map_zero, Dop_X, Dop_X]
    by_cases h1 : v.1 = d <;> by_cases h2 : v.1 = b <;> by_cases h3 : b = c <;>
      by_cases h4 : d = a <;> simp [h1, h2, h3, h4, Dop_X, @eq_comm _ c b, @eq_comm _ a d]
  refine LinearMap.ext fun f => ?_
  have h := congrArg (fun D : Derivation R _ _ => D f) hder
  simp only [Derivation.commutator_apply] at h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, DL_apply]
  rw [h]
  split_ifs <;> simp [DL_apply]

end Formalism.L2.G.Model
end
end

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.GradedWeylDivisibility

theorem sw_dom (R : Type) [CommRing R] [IsDomain R] {r n : ℕ} (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ dualWeyl R r n ν) :
    ∀ m ∈ f.support, ∀ k : ℕ,
      (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ t : Fin n with t.val < k, ν t := by
  classical
  obtain ⟨b, hb, h2⟩ := sSBasis R r n ν
  rw [← hb.2.1] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨-, -, K, sz, hsz, I, hshape, -, hbm⟩ := h2 i
    intro m hm k
    rw [hbm] at hm
    have h := (bidetDominance R r n K sz hsz I m hm).1 k
    rw [hshape] at h
    exact h
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.mp (support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    exact hx m (support_smul hm)

theorem sw_kill (R : Type) [CommRing R] [IsDomain R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (G : MvPolynomial (Fin r × Fin n) R) (hG : G ∈ dualWeyl R r n ν)
    (hGh : IsWeightedHomogeneous (rowW r n) G (rowNu (r := r) ν))
    (a b : Fin r) (hab : a < b) (k : ℕ) (hk : 1 ≤ k) : rowDiv R a b k G = 0 := by
  classical
  have hGp : IsWeightedHomogeneous (lehwP a) G
      ((∑ a' : Fin r with a'.val < a.val + 1, rowNu (r := r) ν a' : ℕ) : ℤ) := by
    intro m hm
    rw [lehw_weight_P]
    have hm' := hGh hm
    congr 1
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [← lehw_weight_rowW, hm']
  have hsh := lehw_rowDiv_shift R (lehwP a) 1 a b (highestWeightCount_self_eq_succ_of_lt hab) _ k G hGp
  have hmem := rowDivStable R r n ν a b k G hG
  by_contra hne
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hne
  have h1 := hsh hm
  rw [lehw_weight_P] at h1
  have h2 := sw_dom R ν _ hmem m (mem_support_iff.mpr hm) (a.val + 1)
  rw [← rowNuSum r n ν hn] at h2
  have h3 : ((∑ a' : Fin r with a'.val < a.val + 1, rowDeg m a' : ℕ) : ℤ) ≤
      ((∑ a' : Fin r with a'.val < a.val + 1, rowNu (r := r) ν a' : ℕ) : ℤ) := by exact_mod_cast h2
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  rw [h1] at h3
  linarith

theorem sw_eval_hw (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    eval (idPoint R r n) (hw R hn ν) = 1 := by
  unfold hw
  rw [map_prod]
  refine Finset.prod_eq_one fun s _ => ?_
  rw [map_pow, eval_idPoint_lpMinor R (r := r) (n := n) (s.val + 1) (by omega) (by omega), one_pow]

theorem sw_line (K : Type) [Field K] [Infinite K] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν)
    (G : MvPolynomial (Fin r × Fin n) K) (hG : G ∈ dualWeyl K r n ν)
    (hGh : IsWeightedHomogeneous (rowW r n) G (rowNu (r := r) ν)) :
    G = eval (idPoint K r n) G • hw K hn ν := by
  obtain ⟨c, hc⟩ := hwLine K r n hn ν hν G hG (fun a b hab k hk => sw_kill K hn ν G hG hGh a b hab k hk)
  have h1 : eval (idPoint K r n) G = c := by
    rw [hc, smul_eq_C_mul, map_mul, eval_C, sw_eval_hw, mul_one]
  rw [h1]
  exact hc

theorem sw_rowGen_X_self (R : Type) [CommRing R] {r n : ℕ} (a : Fin r) (v : Fin r × Fin n) :
    rowGen R a a (X v) = Polynomial.C (X v) * (1 + Polynomial.X) ^ (lgraded_wa (n := n) a v) := by
  rw [rowGen, aeval_X]
  unfold lgraded_wa
  split_ifs with h
  · obtain ⟨b, s⟩ := v
    simp only at h
    subst h
    ring
  · simp

theorem sw_rowGen_monomial (R : Type) [CommRing R] {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) (c : R) :
    rowGen R a a (monomial m c) =
      Polynomial.C (monomial m c) * (1 + Polynomial.X) ^ (Finsupp.weight (lgraded_wa a) m) := by
  rw [monomial_eq, map_mul, Finsupp.prod, map_prod, sw_rowGen_C]
  simp_rw [map_pow, sw_rowGen_X_self, mul_pow, Finset.prod_mul_distrib, ← pow_mul,
    Finset.prod_pow_eq_pow_sum]
  rw [Finsupp.weight_apply, Finsupp.sum, map_mul, map_prod]
  simp_rw [map_pow, smul_eq_mul, mul_comm (lgraded_wa a _)]
  ring

theorem sw_euler_monomial (R : Type) [CommRing R] {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) (c : R) :
    rowDiv R a a 1 (monomial m c) = ((Finsupp.weight (lgraded_wa a) m : ℕ) : R) • monomial m c := by
  rw [rowDiv, sw_rowGen_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow,
    Nat.choose_one_right, smul_eq_C_mul, mul_comm]
  simp

theorem sw_coeff_euler (R : Type) [CommRing R] {r n : ℕ} (a : Fin r) (f : MvPolynomial (Fin r × Fin n) R)
    (m : Fin r × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (rowDiv R a a 1 f) m = ((Finsupp.weight (lgraded_wa a) m : ℕ) : R) * AddMonoidAlgebra.coeff f m := by
  induction f using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [sw_euler_monomial, coeff_smul, coeff_monomial, smul_eq_mul]
    split_ifs with h
    · subst h; rfl
    · simp
  | add p q hp hq => rw [rowDiv_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem sw_Dop_self (R : Type) [CommRing R] {r n : ℕ} (a : Fin r) (f : MvPolynomial (Fin r × Fin n) R) :
    Dop R a a f = rowDiv R a a 1 f := by
  have h := sw_step_eq R a 0 f
  simp only [zero_add, Nat.cast_one, one_smul, Nat.cast_zero, zero_smul, sub_zero, sw_rowDiv_zero] at h
  exact h.symm

theorem sw_Dop_ne (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (hab : a ≠ b)
    (f : MvPolynomial (Fin r × Fin n) R) : Dop R a b f = rowDiv R a b 1 f := by
  have h := sw_step_ne R a b hab 0 f
  simp only [zero_add, Nat.cast_one, one_smul, sw_rowDiv_zero] at h
  exact h.symm

theorem sw_Dop_rowDiv (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r)
    (f : MvPolynomial (Fin r × Fin n) R) : Dop R a b f = rowDiv R a b 1 f := by
  by_cases hab : a = b
  · subst hab; exact sw_Dop_self R a f
  · exact sw_Dop_ne R a b hab f

theorem sw_euler (R : Type) [CommRing R] {r n : ℕ} (a : Fin r) (μ : Fin r → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous (rowW r n) f μ) :
    Dop R a a f = (μ a : R) • f := by
  rw [sw_Dop_self]
  ext m
  rw [sw_coeff_euler, coeff_smul, smul_eq_mul]
  by_cases hm : AddMonoidAlgebra.coeff f m = 0
  · rw [hm, mul_zero, mul_zero]
  · rw [← lgraded_weight_rowW, hf hm]

theorem sw_bidet_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    map φ (bideterminant R sz hsz I) = bideterminant S sz hsz I := by
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp

theorem sw_weyl_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ} (hn : n ≤ r)
    (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ weyl R r n hn ν) :
    map φ f ∈ weyl S r n hn ν := by
  unfold weyl at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    rw [← lclosedeq_applyWord_map, lclosedeq_hw_map]
    exact Submodule.subset_span ⟨w, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

theorem sw_weyl_eq (K : Type) [Field K] [CharZero K] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    weyl K r n hn ν = dualWeyl K r n ν := by
  apply le_antisymm (weylLeDual K r n hn ν hν)
  obtain ⟨b, hb, h2⟩ := sSBasis K r n ν
  rw [← hb.2.1, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨-, -, N, sz, hsz, I, hshape, -, hbm⟩ := h2 i
  have h3 : bideterminant ℤ sz hsz I ∈ dualWeyl ℤ r n ν := by
    have := bidetMem ℤ r n N sz hsz I
    rwa [hshape] at this
  obtain ⟨c, hc, h4⟩ := weylRational r n hn ν hν _ h3
  have h5 := sw_weyl_map (Int.castRingHom K) hn ν _ h4
  rw [zsmul_eq_mul, map_mul, map_intCast, sw_bidet_map, ← hbm] at h5
  have hcK : (c : K) ≠ 0 := by exact_mod_cast hc
  have h6 : b i = (c : K)⁻¹ • (((c : ℤ) : MvPolynomial (Fin r × Fin n) K) * b i) := by
    rw [smul_eq_C_mul, ← mul_assoc]
    have : (C (c : K)⁻¹ : MvPolynomial (Fin r × Fin n) K) * ((c : ℤ) : MvPolynomial (Fin r × Fin n) K) = 1 := by
      rw [← map_intCast (C : K →+* MvPolynomial (Fin r × Fin n) K), ← map_mul, inv_mul_cancel₀ hcK, map_one]
    rw [this, one_mul]
  show b i ∈ weyl K r n hn ν
  rw [h6]
  exact Submodule.smul_mem _ _ h5

end Formalism.L2.G.Model
