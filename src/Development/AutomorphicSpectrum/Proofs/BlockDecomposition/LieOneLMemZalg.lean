module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionAction
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsCoefficientFieldChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfinite

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOneLMemZalg
open NumberField GlobalTheory.CuspRep Polynomial Finset

namespace GlobalTheory.CompanionTheory.CapelliTrace

theorem mem_of_dual {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) (x : A)
    (h : ∀ f : A →ₗ[ℂ] ℂ, (∀ z ∈ S, f z = 0) → f x = 0) : x ∈ S := by
  by_contra hx
  have hx' : x ∉ Subalgebra.toSubmodule S := hx
  obtain ⟨f, hf1, hf2⟩ := Submodule.exists_le_ker_of_notMem hx'
  exact hf1 (h f fun z hz => LinearMap.mem_ker.1 (hf2 hz))

theorem prod_X_sub {n : ℕ} (s : Finset (Fin n)) :
    (∏ l ∈ s, (X - C ((l : ℕ) : ℂ))).natDegree = s.card ∧ (∏ l ∈ s, (X - C ((l : ℕ) : ℂ))).Monic := by
  refine ⟨?_, monic_prod_of_monic _ _ fun l _ => monic_X_sub_C _⟩
  rw [natDegree_prod_of_monic _ _ fun l _ => monic_X_sub_C _, Finset.sum_congr rfl fun l _ => natDegree_X_sub_C _]
  simp

theorem trace_mem {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) (n : ℕ) (M : Fin n → Fin n → A)
    (h : ∀ u : ℂ, Formalism.REAL.qdet M u ∈ S) : ∑ i, M i i ∈ S := by
  obtain ⟨Rm, hR⟩ := GlobalTheory.qdet_top_three_orders A n M
  refine mem_of_dual S _ fun f hf => ?_
  have f1 : f 1 = 0 := hf 1 S.one_mem
  set Q : ℂ[X] := ∑ i, C (f (M i i)) * ∏ l ∈ univ.erase i, (X - C ((l : ℕ) : ℂ)) +
    ∑ i, ∑ j ∈ univ.filter (fun j => i < j), C (f (M i i * M j j - M j i * M i j)) *
      ∏ l ∈ (univ.erase i).erase j, (X - C ((l : ℕ) : ℂ)) +
    ∑ d ∈ range (n - 2), C (f (Rm d)) * X ^ d with hQ
  have hQ0 : Q = 0 := Polynomial.funext fun u => by
    have h1 := hf _ (h u)
    rw [hR u] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_smul, smul_eq_mul, f1, mul_zero, zero_add] at h1
    simp only [hQ, eval_add, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_sub, eval_X, eval_pow, eval_zero]
    rw [← h1]
    congr 1
    · congr 1
      · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
    · exact Finset.sum_congr rfl fun d _ => mul_comm _ _
  have hc := congrArg (fun p : ℂ[X] => p.coeff (n - 1)) hQ0
  simp only [hQ, coeff_add, finsetSum_coeff, coeff_C_mul, coeff_zero] at hc
  have t1 : ∀ i : Fin n, (∏ l ∈ univ.erase i, (X - C ((l : ℕ) : ℂ))).coeff (n - 1) = 1 := fun i => by
    obtain ⟨hd, hm⟩ := prod_X_sub (univ.erase i)
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at hd
    rw [← hd]; exact hm.coeff_natDegree
  have t2 : ∀ i : Fin n, ∀ j ∈ univ.filter (fun j => i < j),
      (∏ l ∈ (univ.erase i).erase j, (X - C ((l : ℕ) : ℂ))).coeff (n - 1) = 0 := fun i j hj => by
    have hij : i < j := (mem_filter.1 hj).2
    have hj' : (j : ℕ) < n := j.2
    have hi' : (i : ℕ) < j := hij
    obtain ⟨hd, -⟩ := prod_X_sub ((univ.erase i).erase j)
    rw [card_erase_of_mem (mem_erase.2 ⟨hij.ne', mem_univ _⟩), card_erase_of_mem (mem_univ _), card_univ,
      Fintype.card_fin] at hd
    exact coeff_eq_zero_of_natDegree_lt (by omega)
  have t3 : ∀ d ∈ range (n - 2), ((X : ℂ[X]) ^ d).coeff (n - 1) = 0 := fun d hd => by
    rw [coeff_X_pow, if_neg]
    have := mem_range.1 hd
    omega
  have e3 : ∑ d ∈ range (n - 2), f (Rm d) * ((X : ℂ[X]) ^ d).coeff (n - 1) = 0 :=
    Finset.sum_eq_zero fun d hd => by rw [t3 d hd, mul_zero]
  have e2 : ∑ i : Fin n, ∑ j ∈ univ.filter (fun j => i < j), f (M i i * M j j - M j i * M i j) *
      (∏ l ∈ (univ.erase i).erase j, (X - C ((l : ℕ) : ℂ))).coeff (n - 1) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj => by rw [t2 i j hj, mul_zero]
  have e1 : ∑ i : Fin n, f (M i i) * (∏ l ∈ univ.erase i, (X - C ((l : ℕ) : ℂ))).coeff (n - 1) = ∑ i, f (M i i) :=
    Finset.sum_congr rfl fun i _ => by rw [t1 i, mul_one]
  rw [e1, e2, e3, add_zero, add_zero] at hc
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact hc

end GlobalTheory.CompanionTheory.CapelliTrace

namespace GlobalTheory.CompanionTheory.CapelliTrace

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
open Classical in
theorem atEmb_one (τ : E →+* ℂ) : atEmb τ 1 = Pi.single (InfinitePlace.mk τ) 1 := by
  unfold atEmb; split_ifs <;> simp

theorem Eop_add_conj (τ : E →+* ℂ) (i j : Fin a) :
    Eop τ i j + Eop (ComplexEmbedding.conjugate τ) i j = lieS E a i j (atEmb τ 1) := by
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by rw [atEmb_eq]; simp
  simp only [Eop, atEmb_conj, map_one, Complex.conj_I, e, map_neg, smul_neg, sub_neg_eq_add]
  module

theorem sum_atEmb_one : ∑ τ : E →+* ℂ, atEmb τ 1 = (2 : Cinf E) := by
  classical
  funext w
  simp only [atEmb_one, Finset.sum_apply, Pi.single_apply]
  rw [Finset.sum_boole]
  have h := InfinitePlace.card_filter_mk_eq w
  have h2 : InfinitePlace.mult w = 2 := by
    simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)]
  have h3 : (Finset.univ.filter fun τ : E →+* ℂ => w = InfinitePlace.mk τ) =
      Finset.univ.filter fun τ : E →+* ℂ => InfinitePlace.mk τ = w := by
    ext τ; simp [eq_comm]
  rw [h3, h, h2]
  simp

end GlobalTheory.CompanionTheory.CapelliTrace

namespace GlobalTheory.CompanionTheory.CapelliTrace

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem sum_Eop (i j : Fin a) : ∑ τ : E →+* ℂ, Eop τ i j = lieS E a i j 1 := by
  set X := ∑ τ : E →+* ℂ, Eop τ i j
  have hc : ∑ τ : E →+* ℂ, Eop (ComplexEmbedding.conjugate τ) i j = X :=
    Equiv.sum_comp (Function.Involutive.toPerm _ (ComplexEmbedding.involutive_conjugate E)) fun τ => Eop τ i j
  have h2 : (2 : ℂ) • X = (2 : ℂ) • lieS E a i j 1 := by
    rw [two_smul, two_smul]
    nth_rewrite 2 [← hc]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun τ _ => Eop_add_conj τ i j, ← map_sum, sum_atEmb_one,
      show (2 : Cinf E) = 1 + 1 from one_add_one_eq_two.symm, map_add]
  exact smul_right_injective _ two_ne_zero h2

theorem lie_oneL_eq : lie E a (oneL E a) = ∑ τ : E →+* ℂ, ∑ i, Eop τ i i := by
  rw [Finset.sum_comm, Finset.sum_congr rfl fun i _ => sum_Eop i i]
  have e : oneL E a = ∑ i : Fin a, toL (Matrix.single i i (1 : Cinf E)) := by
    funext k l
    change (1 : Matrix (Fin a) (Fin a) (Cinf E)) k l = (∑ i : Fin a, Matrix.single i i (1 : Cinf E)) k l
    rw [Matrix.sum_apply]
    by_cases h : k = l
    · subst h; simp [Matrix.single_apply]
    · rw [Matrix.one_apply_ne h]
      exact (Finset.sum_eq_zero fun c _ => by
        rw [Matrix.single_apply, if_neg fun hc => h (hc.1.symm.trans hc.2)]).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  rfl

theorem lie_oneL_mem_Zalg : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    lie E a (oneL E a) ∈ Zalg E a := by
  intro E _ _ _ a
  rw [lie_oneL_eq]
  refine Subalgebra.sum_mem _ fun τ _ => trace_mem (Zalg E a) a (Eop τ) fun u => ?_
  have h : cap (a := a) τ (u - ((a : ℂ) - 1) / 2) ∈ Zalg E a := Algebra.subset_adjoin ⟨τ, _, rfl⟩
  rwa [cap, sub_add_cancel] at h

end GlobalTheory.CompanionTheory.CapelliTrace
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwLMulSelf
open Finset PositivityTheory.RgBcC.RealD
open CompanionTheory.D.LK (Pos key)

noncomputable section

namespace GlobalTheory.CompanionTheory.LvChain

variable {n : ℕ}

theorem key_lt (i : Pos n) : key i < n * n := by
  obtain ⟨⟨a, b⟩, hab⟩ := i
  have ha := a.isLt
  have hb := b.isLt
  show (a : ℕ) * n + b < n * n
  calc (a : ℕ) * n + b < a * n + n := by omega
    _ = (a + 1) * n := by ring
    _ ≤ n * n := Nat.mul_le_mul_right _ ha

theorem keyL_inj {l m : Lt n} (h : keyL l = keyL m) : l = m := by
  obtain ⟨b1, p1⟩ := l
  obtain ⟨b2, p2⟩ := m
  have k1 := key_lt p1
  have k2 := key_lt p2
  have hk : key p1 = key p2 ∧ b1 = b2 := by
    simp only [keyL] at h
    cases b1 <;> cases b2 <;> simp at h ⊢ <;> omega
  obtain ⟨hk, rfl⟩ := hk
  obtain ⟨⟨a1, c1⟩, h1⟩ := p1
  obtain ⟨⟨a2, c2⟩, h2⟩ := p2
  have hc1 := c1.isLt
  have hc2 := c2.isLt
  have hn : 0 < n := by omega
  have hk' : (c1 : ℕ) + a1 * n = c2 + a2 * n := by
    have e : (a1 : ℕ) * n + c1 = a2 * n + c2 := hk
    linarith
  have ea : (a1 : ℕ) = a2 := by
    have := congrArg (· / n) hk'
    simpa [Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hc1, Nat.div_eq_of_lt hc2] using this
  have ec : (c1 : ℕ) = c2 := by
    have := congrArg (· % n) hk'
    simpa [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc1, Nat.mod_eq_of_lt hc2] using this
  have e1 : a1 = a2 := Fin.ext ea
  have e2 : c1 = c2 := Fin.ext ec
  subst e1 e2
  rfl

def twL (l m : Lt n) : ℂ := if keyL m < keyL l then -1 else 1

theorem twL_self (l : Lt n) : twL l l = 1 := by simp [twL]

theorem twL_mul_self (l m : Lt n) : twL l m * twL l m = 1 := by
  unfold twL
  split_ifs <;> norm_num

theorem twL_swap {l m : Lt n} (h : l ≠ m) : twL m l = -twL l m := by
  have hk : keyL l ≠ keyL m := fun e => h (keyL_inj e)
  unfold twL
  split_ifs with h1 h2 h2
  · exfalso; omega
  · norm_num
  · norm_num
  · exfalso; omega

theorem sgL_mul_self (l : Lt n) (A : Finset (Lt n)) : sgL l A * sgL l A = 1 := by
  unfold sgL
  rw [← mul_pow]
  norm_num

theorem sgL_ne_zero (l : Lt n) (A : Finset (Lt n)) : sgL l A ≠ 0 := by
  unfold sgL
  exact pow_ne_zero _ (by norm_num)

theorem sgL_insert (l : Lt n) {m : Lt n} {A : Finset (Lt n)} (h : m ∉ A) :
    sgL l (insert m A) = twL l m * sgL l A := by
  unfold sgL twL
  rw [Finset.filter_insert]
  split_ifs with hk
  · rw [Finset.card_insert_of_notMem (fun hm => h (Finset.mem_filter.1 hm).1), pow_succ]; ring
  · simp

theorem sgL_erase (l : Lt n) {m : Lt n} {A : Finset (Lt n)} (h : m ∈ A) :
    sgL l (A.erase m) = twL l m * sgL l A := by
  have h1 := sgL_insert l (Finset.notMem_erase m A)
  rw [Finset.insert_erase h] at h1
  rw [h1, ← mul_assoc, twL_mul_self, one_mul]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem annL_apply (l : Lt n) (x : Cq n V) (A : Finset (Lt n)) :
    annL l x A = if l ∈ A then 0 else sgL l A • x (insert l A) := rfl

theorem creL_apply (l : Lt n) (x : Cq n V) (A : Finset (Lt n)) :
    creL l x A = if l ∈ A then sgL l A • x (A.erase l) else 0 := rfl

theorem liftL_apply {V' : Type} [AddCommGroup V'] [Module ℂ V'] (T : V →ₗ[ℂ] V') (x : Cq n V) (A : Finset (Lt n)) :
    liftL n T x A = T (x A) := rfl

theorem annL_annL (i j : Lt n) : (annL i * annL j + annL j * annL i : Module.End ℂ (Cq n V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply,
    annL_apply]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  · simp [hi]
  by_cases hj : j ∈ A
  · simp [hj]
  simp only [hi, hj, Finset.mem_insert, hij, hji, or_self, if_false]
  rw [sgL_insert j hi, sgL_insert i hj, twL_swap hij, Finset.insert_comm j i, smul_smul, smul_smul, ← add_smul]
  have : sgL i A * (-twL i j * sgL j A) + sgL j A * (twL i j * sgL i A) = 0 := by ring
  rw [this, zero_smul]

theorem creL_creL (i j : Lt n) : (creL i * creL j + creL j * creL i : Module.End ℂ (Cq n V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply,
    creL_apply]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  swap
  · simp [hi]
  by_cases hj : j ∈ A
  swap
  · simp [hj]
  simp only [hi, hj, Finset.mem_erase, ne_eq, hij, hji, not_false_eq_true, and_self, if_true]
  rw [sgL_erase j hi, sgL_erase i hj, twL_swap hij, Finset.erase_right_comm (a := j) (b := i), smul_smul, smul_smul,
    ← add_smul]
  have : sgL i A * (-twL i j * sgL j A) + sgL j A * (twL i j * sgL i A) = 0 := by ring
  rw [this, zero_smul]

theorem annL_creL (i j : Lt n) :
    (annL i * creL j + creL j * annL i : Module.End ℂ (Cq n V)) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    refine LinearMap.ext fun x => funext fun A => ?_
    simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, annL_apply, creL_apply,
      Module.End.one_apply]
    by_cases hi : i ∈ A
    · have h1 : i ∉ A.erase i := Finset.notMem_erase i A
      rw [if_pos hi, if_pos hi, if_neg h1, sgL_erase i hi, twL_self, one_mul, Finset.insert_erase hi,
        smul_smul, sgL_mul_self, one_smul, zero_add]
    · have h1 : i ∈ insert i A := Finset.mem_insert_self i A
      rw [if_neg hi, if_pos h1, if_neg hi, sgL_insert i hi, twL_self, one_mul, Finset.erase_insert hi,
        smul_smul, sgL_mul_self, one_smul, add_zero]
  · rw [if_neg hij]
    refine LinearMap.ext fun x => funext fun A => ?_
    simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply, Pi.add_apply,
      Pi.zero_apply, annL_apply, creL_apply]
    by_cases hi : i ∈ A
    · have hi' : i ∈ A.erase j := Finset.mem_erase.2 ⟨hij, hi⟩
      simp [hi, hi']
    · by_cases hj : j ∈ A
      · have hj' : j ∈ insert i A := Finset.mem_insert_of_mem hj
        have hi' : i ∉ A.erase j := fun hm => hi (Finset.mem_of_mem_erase hm)
        rw [if_neg hi, if_pos hj', if_pos hj, if_neg hi', sgL_insert j hi, sgL_erase i hj,
          twL_swap hij, Finset.erase_insert_of_ne hij, smul_smul, smul_smul, ← add_smul]
        have e : sgL i A * (-twL i j * sgL j A) + sgL j A * (twL i j * sgL i A) = 0 := by ring
        rw [e, zero_smul]
      · have hj' : j ∉ insert i A := by simp [hj, Ne.symm hij]
        simp [hi, hj, hj']

theorem annL_ne {i : Lt n} {x : Cq n V} {A : Finset (Lt n)} (h : annL i x A ≠ 0) : i ∉ A ∧ x (insert i A) ≠ 0 := by
  rw [annL_apply] at h
  by_cases hi : i ∈ A
  · simp [hi] at h
  · refine ⟨hi, fun hx => h ?_⟩
    simp [hi, hx]

theorem creL_ne {i : Lt n} {x : Cq n V} {A : Finset (Lt n)} (h : creL i x A ≠ 0) : i ∈ A ∧ x (A.erase i) ≠ 0 := by
  rw [creL_apply] at h
  by_cases hi : i ∈ A
  · refine ⟨hi, fun hx => h ?_⟩
    simp [hi, hx]
  · simp [hi] at h

theorem liftL_annL (T : Module.End ℂ V) (l : Lt n) :
    ((liftL n T : Module.End ℂ (Cq n V)) * annL l : Module.End ℂ (Cq n V)) = annL l * (liftL n T : Module.End ℂ (Cq n V)) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [Module.End.mul_apply, liftL_apply, annL_apply]
  split_ifs <;> simp [liftL_apply]

theorem liftL_creL (T : Module.End ℂ V) (l : Lt n) :
    ((liftL n T : Module.End ℂ (Cq n V)) * creL l : Module.End ℂ (Cq n V)) = creL l * (liftL n T : Module.End ℂ (Cq n V)) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [Module.End.mul_apply, liftL_apply, creL_apply]
  split_ifs <;> simp [liftL_apply]

def adS (S : Lt n → Prop) (s : Bool) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  open Classical in ∑ l : Lt n, ∑ k : Lt n, if S l then adCL s p q l k • (creL k * annL l) else 0

def Lv (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  (liftL n (kA E1 E2 p q) : Module.End ℂ (Cq n V)) + adLL lev false p q

end GlobalTheory.CompanionTheory.LvChain
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMonicAevalMemOfLeSup
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.Affgl

theorem exists_monic_aeval_mem_of_le_sup {R : Type*} [Ring R] [Algebra ℂ R] (A : Subalgebra ℂ R)
    (V I : Submodule ℂ R) [FiniteDimensional ℂ V] (h : ∀ z ∈ A, z ∈ V ⊔ I) (z : R) (hz : z ∈ A) :
    ∃ p : Polynomial ℂ, p.Monic ∧ Polynomial.aeval z p ∈ I := by
  have hmemA : ∀ p : Polynomial ℂ, Polynomial.aeval z p ∈ A := by
    intro p
    have e : Polynomial.aeval z p = ((Polynomial.aeval (⟨z, hz⟩ : A) p : A) : R) := by
      simpa using (Polynomial.aeval_algHom_apply A.val (⟨z, hz⟩ : A) p)
    rw [e]
    exact Subtype.property _
  let f : Polynomial ℂ →ₗ[ℂ] R ⧸ I := I.mkQ ∘ₗ (Polynomial.aeval z).toLinearMap
  have hf : ∀ p, f p ∈ V.map I.mkQ := by
    intro p
    obtain ⟨v, hv, i, hi, e⟩ := Submodule.mem_sup.1 (h _ (hmemA p))
    refine ⟨v, hv, ?_⟩
    change I.mkQ v = I.mkQ (Polynomial.aeval z p)
    have hi0 : I.mkQ i = 0 := by simpa using hi
    rw [← e, map_add (f := _), hi0, add_zero]
  let g : Polynomial ℂ →ₗ[ℂ] V.map I.mkQ := f.codRestrict _ hf
  have hnot : ¬ Function.Injective g := fun hinj =>
    Polynomial.not_finite (R := ℂ) (Module.Finite.of_injective g hinj)
  obtain ⟨p, hgp, hp⟩ : ∃ p, g p = 0 ∧ p ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hnot ((injective_iff_map_eq_zero g).2 fun p hp => hcon p hp)
  have hI : Polynomial.aeval z p ∈ I := by
    have : f p = 0 := congrArg Subtype.val hgp
    simpa [f] using this
  refine ⟨p * Polynomial.C p.leadingCoeff⁻¹, Polynomial.monic_mul_leadingCoeff_inv hp, ?_⟩
  rw [map_mul, Polynomial.aeval_C, ← Algebra.commutes, ← Algebra.smul_def]
  exact I.smul_mem _ hI

theorem exists_monic_aeval_apply_eq_zero (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (a : ℕ) (J : Set (Module.End ℂ (Sm E a))) (hJ : Cofin J) (z : Module.End ℂ (Sm E a))
    (hz : z ∈ Zalg E a) :
    ∃ p : Polynomial ℂ, p.Monic ∧ ∀ φ : Sm E a, (∀ j ∈ J, j φ = 0) →
      Polynomial.aeval z p φ = 0 := by
  obtain ⟨-, V, hV, hcov⟩ := hJ
  obtain ⟨p, hp, hI⟩ := exists_monic_aeval_mem_of_le_sup (Zalg E a) V _ hcov z hz
  refine ⟨p, hp, fun φ hφ => ?_⟩
  have key : ∀ y ∈ Submodule.span ℂ {y | ∃ x ∈ Zalg E a, ∃ j ∈ J, y = x * j}, y φ = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, -, j, hj, rfl⟩ := hy
      simp [hφ j hj]
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul c u _ hu => simp [hu]
  exact key _ hI

theorem minpoly_on_killed : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    ∀ J : Set (Module.End ℂ (Sm E a)), Cofin J → ∀ z ∈ Zalg E a, ∃ p : Polynomial ℂ, p.Monic ∧
      ∀ φ : Sm E a, (∀ j ∈ J, j φ = 0) → Polynomial.aeval z p φ = 0 :=
  fun E _ _ _ a J hJ z hz => exists_monic_aeval_apply_eq_zero E a J hJ z hz

end GlobalTheory.CompanionTheory.Affgl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingTwistedDeterminantSubquotient
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingTwistedDeterminantSubquotient
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

noncomputable section

namespace GlobalTheory.CompanionTheory.DualQuot

theorem exists_subquotient_dual_nu : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n s : ℕ) (V' : Type) [AddCommGroup V'] [Module ℂ V'] (S : IrrRep (GL (Fin n) k))
    (A' : Representation ℂ (GL (Fin n) k) V'), IsSmooth A' → ∀ B : S.V →ₗ[ℂ] V' →ₗ[ℂ] ℂ,
    (∀ g w w', B (S.ρ g w) (A' g w') = ((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) * B w w') → B ≠ 0 →
    ∃ Q : IrrRep (GL (Fin n) k), IsSubquotient Q.ρ A' ∧
      IrrGL.of Q.ρ Q.smooth Q.irr = (dualCl (IrrGL.of S.ρ S.smooth S.irr)).nu (s : ℂ) := by
  intro k _ _ _ _ n s V' _ _ S A' hA' B hB hB0
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hAd : GlobalTheory.Published.IrreducibleAdmissibleGL := fun k _ _ _ _ n V _ _ π => (hBZ k).1 (Fin n) V π
  have hχ : IsSmoothChar (absPow k (s : ℂ)) := isSmoothChar_absPow _
  have hχ' : IsSmoothChar (absPow k (-(s : ℂ))) := isSmoothChar_absPow _
  have hprod : ∀ g : GL (Fin n) k, ((detChar (Fin n) (absPow k (-(s : ℂ))) g : ℂˣ) : ℂ) *
      ((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) = 1 := by
    intro g
    rw [absPow_neg, detChar_apply, detChar_apply, MonoidHom.inv_apply]
    simp
  have hT := isSmooth_twist hA' hχ'.detChar
  have hBT : ∀ g a b, B (S.ρ g a) (GlobalTheory.SmGL.twist A' (detChar (Fin n) (absPow k (-(s : ℂ)))) g b) = B a b := by
    intro g a b
    rw [twist_apply, map_smul, hB, smul_eq_mul, ← mul_assoc, hprod, one_mul]
  let f := GlobalTheory.InvPairing.pairMap S.ρ hT B hBT
  have hc := GlobalTheory.CompanionTheory.ZcDual.isIrreducible_contra hAd S.ρ S.smooth S.irr
  have hsurj : Function.Surjective f := by
    let R : Subrepresentation (contra S.ρ) :=
      { toSubmodule := LinearMap.range f.toLinearMap
        apply_mem_toSubmodule := fun g v hv => by
          obtain ⟨w, rfl⟩ := hv
          refine ⟨GlobalTheory.SmGL.twist A' (detChar (Fin n) (absPow k (-(s : ℂ)))) g w, ?_⟩
          have := LinearMap.congr_fun (f.isIntertwining' g) w
          simpa only [LinearMap.comp_apply] using this }
    rcases hc.eq_bot_or_eq_top R with hR | hR
    · exfalso
      refine hB0 (GlobalTheory.InvPairing.eq_zero_of_pairMap S.ρ hT B hBT fun b => ?_)
      have : f b ∈ R.toSubmodule := ⟨b, rfl⟩
      rw [hR] at this
      exact (Submodule.mem_bot ℂ).1 this
    · intro l
      have : l ∈ R.toSubmodule := by rw [hR]; exact Submodule.mem_top
      obtain ⟨b, hb⟩ := this
      exact ⟨b, hb⟩
  let F : A'.IntertwiningMap (GlobalTheory.SmGL.twist (contra S.ρ) (detChar (Fin n) (absPow k (s : ℂ)))) :=
    { toLinearMap := f.toLinearMap
      isIntertwining' := fun g => by
        refine LinearMap.ext fun w => ?_
        have h := LinearMap.congr_fun (f.isIntertwining' g) w
        simp only [LinearMap.comp_apply, twist_apply, map_smul] at h ⊢
        rw [← h, smul_smul, mul_comm, hprod, one_smul] }
  refine ⟨⟨_, GlobalTheory.SmGL.twist (contra S.ρ) (detChar (Fin n) (absPow k (s : ℂ))),
    isSmooth_twist (isSmooth_contra _) hχ.detChar, isIrreducible_twist hc _⟩,
    IsSubquotient.of_surjective F hsurj, ?_⟩
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hAd, IrrGL.nu, IrrGL.tw_of]
  exact IrrGL.of_eq_of.2
    ⟨(twistEquiv (GlobalTheory.ContraRefl.contraEquiv (IrrGL.equivOf S.ρ S.smooth S.irr)) _).symm⟩

end GlobalTheory.CompanionTheory.DualQuot

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingTwistedDeterminantSubquotientStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_twisted_determinant_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n s : ℕ) (V' : Type) [AddCommGroup V'] [Module ℂ V'] (S : IrrRep (GL (Fin n) k))
    (A' : Representation ℂ (GL (Fin n) k) V'), IsSmooth A' → ∀ B : S.V →ₗ[ℂ] V' →ₗ[ℂ] ℂ,
    (∀ g w w', B (S.ρ g w) (A' g w') = ((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) * B w w') → B ≠ 0 →
    ∃ Q : IrrRep (GL (Fin n) k), IsSubquotient Q.ρ A' ∧
      IrrGL.of Q.ρ Q.smooth Q.irr = (dualCl (IrrGL.of S.ρ S.smooth S.irr)).nu (s : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.DualQuot.exists_subquotient_dual_nu | exact GlobalTheory.CompanionTheory.DualQuot.exists_subquotient_dual_nu | (intros; apply GlobalTheory.CompanionTheory.DualQuot.exists_subquotient_dual_nu <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentreDerivativeLieAction
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentreDerivativeLieAction
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.CuspFinDeriv

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)

def cExp (t : ℝ) : GL (Fin a) (Cinf E) :=
  Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ))

theorem splitCentre_eq_infGL (t : ℝ) : GlobalTheory.UnitaryBC.splitCentre E a t = infGL E a (cExp E a t) := rfl

theorem cExp_zero : cExp E a 0 = 1 := by
  have h1 : (GlobalTheory.CuspRep.expU fun _ : InfinitePlace E => ((0 : ℝ) : ℂ)) = 1 := by
    apply Units.ext
    funext v
    simp [GlobalTheory.CuspRep.expU]
  unfold cExp
  rw [h1, map_one]

theorem hasDerivAt_cExp : HasDerivAt (fun t => toL (cExp E a t).val) (oneL E a) 0 := by
  unfold cExp GlobalTheory.CuspRep.toL GlobalTheory.CuspRep.oneL
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  rw [hasDerivAt_pi]
  intro v
  simp [GlobalTheory.CuspRep.expU, Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    have h := (Complex.hasDerivAt_exp ((0 : ℝ) : ℂ)).comp_ofReal
    simp only [Complex.ofReal_zero, Complex.exp_zero] at h
    simpa using h
  · simpa [hij] using hasDerivAt_const (0 : ℝ) (0 : ℂ)

theorem hasDerivAt_splitCentre : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (g : GA E a) (s : ℝ),
    HasDerivAt (fun s : ℝ => φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a s))
      ((lie E a (oneL E a) φ).1 (g * GlobalTheory.UnitaryBC.splitCentre E a s)) s := by
  intro E _ _ _ a φ g s
  have hφ := φ.2
  unfold GlobalTheory.CuspRep.Sm at hφ
  have hc := hφ (g * GlobalTheory.UnitaryBC.splitCentre E a s)
  have hopen : IsOpen (GlobalTheory.CuspRep.invSet E a) := by
    unfold GlobalTheory.CuspRep.invSet
    have hdet : Continuous fun x : GlobalTheory.CuspRep.Lie E a => (Matrix.of x).det :=
      (continuous_id.comp continuous_id).matrix_det
    have h3 := Units.isOpen.preimage hdet
    simpa [Matrix.isUnit_iff_isUnit_det] using h3
  have hmem : GlobalTheory.CuspRep.oneL E a ∈ GlobalTheory.CuspRep.invSet E a := by
    unfold GlobalTheory.CuspRep.invSet GlobalTheory.CuspRep.oneL GlobalTheory.CuspRep.toL
    change IsUnit (1 : Matrix (Fin a) (Fin a) (Cinf E))
    exact isUnit_one
  have hdiff : DifferentiableAt ℝ (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s))
      (GlobalTheory.CuspRep.oneL E a) :=
    (hc.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hmem)
  have hγ0 : GlobalTheory.CuspRep.toL (cExp E a 0).val = GlobalTheory.CuspRep.oneL E a := by
    rw [cExp_zero]
    rfl
  have hl : HasFDerivAt (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s))
      (fderiv ℝ (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s)) (GlobalTheory.CuspRep.oneL E a))
      (GlobalTheory.CuspRep.toL (cExp E a 0).val) := by
    rw [hγ0]
    exact hdiff.hasFDerivAt
  have hcomp := hl.comp_hasDerivAt (0 : ℝ) (hasDerivAt_cExp E a)
  have hadd : ∀ s t : ℝ, GlobalTheory.UnitaryBC.splitCentre E a (s + t) =
      GlobalTheory.UnitaryBC.splitCentre E a s * GlobalTheory.UnitaryBC.splitCentre E a t := by
    intro s t
    rw [splitCentre_eq_infGL, splitCentre_eq_infGL, splitCentre_eq_infGL, ← map_mul]
    congr 1
    unfold cExp
    rw [← map_mul]
    congr 1
    apply Units.ext
    funext v
    simp [GlobalTheory.CuspRep.expU, Complex.exp_add]
  have hval : ∀ t : ℝ, GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s)
      (GlobalTheory.CuspRep.toL (cExp E a t).val) = (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a (s + t)) := by
    intro t
    unfold GlobalTheory.CuspRep.chart GlobalTheory.CuspRep.toL
    have hu : IsUnit (Matrix.of (Matrix.of.symm (cExp E a t).val)) := by
      change IsUnit (cExp E a t).val
      exact (cExp E a t).isUnit
    rw [dite_eq_left hu]
    have hunit : hu.unit = cExp E a t := Units.ext (by rfl)
    rw [hunit, ← splitCentre_eq_infGL, hadd, mul_assoc]
  have hF : HasDerivAt (fun t : ℝ => (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a (s + t)))
      (fderiv ℝ (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s)) (GlobalTheory.CuspRep.oneL E a)
        (GlobalTheory.CuspRep.oneL E a)) (s - s) := by
    rw [sub_self]
    have h5 : (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s) ∘ fun t => GlobalTheory.CuspRep.toL (cExp E a t).val) =
        fun t : ℝ => (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a (s + t)) := funext hval
    rw [← h5]
    exact hcomp
  have hF2 := HasDerivAt.comp_sub_const s s hF
  have h6 : (fun x : ℝ => (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a (s + (x - s)))) =
      fun x : ℝ => (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a x) := by
    funext x
    rw [show s + (x - s) = x by ring]
  rw [h6] at hF2
  exact hF2

end GlobalTheory.CompanionTheory.CuspFinDeriv

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentreDerivativeLieActionStatement
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_centre_derivative_lie_action : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (g : GA E a) (s : ℝ), HasDerivAt (fun s : ℝ => φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a s)) ((lie E a (oneL E a) φ).1 (g * GlobalTheory.UnitaryBC.splitCentre E a s)) s := by
  first | exact @GlobalTheory.CompanionTheory.CuspFinDeriv.hasDerivAt_splitCentre | exact GlobalTheory.CompanionTheory.CuspFinDeriv.hasDerivAt_splitCentre | (intros; apply GlobalTheory.CompanionTheory.CuspFinDeriv.hasDerivAt_splitCentre <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellUnipotentUniquenessClosed
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellUnipotentUniquenessClosed
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.LowerOpen

theorem inv_conj_apply {k : Type} [Field k] {N : ℕ} (w : Equiv.Perm (Fin N)) (x : GL (Fin N) k)
    (p q : Fin N) :
    (((GroundTheory.Automorphic.permGL k w)⁻¹ * x * GroundTheory.Automorphic.permGL k w : GL (Fin N) k) :
      Matrix (Fin N) (Fin N) k) p q = (x : Matrix (Fin N) (Fin N) k) (w p) (w q) := by
  have h1 : (((GroundTheory.Automorphic.permGL k w)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      w.permMatrix k := by
    rw [← map_inv]
    show ((w⁻¹)⁻¹).permMatrix k = w.permMatrix k
    rw [inv_inv]
  have h2 : ((GroundTheory.Automorphic.permGL k w : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      (w⁻¹).permMatrix k := rfl
  rw [Units.val_mul, Units.val_mul, h1, h2, Equiv.Perm.permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp [Equiv.Perm.inv_def]

theorem lt_of_blk_lt {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {p q : Fin N}
    (hb : blk (stdBlocks d hd) (wOpen d hd q) < blk (stdBlocks d hd) (wOpen d hd p)) : p < q := by
  by_contra hpq
  have h1 := Tuple.monotone_sort (GlobalTheory.CompanionTheory.Rodier.wKey d hd) (not_lt.mp hpq)
  simp only [Function.comp_apply, GlobalTheory.CompanionTheory.Rodier.wKey] at h1
  have hb' : blk (stdBlocks d hd) (Tuple.sort (GlobalTheory.CompanionTheory.Rodier.wKey d hd) q) <
      blk (stdBlocks d hd) (Tuple.sort (GlobalTheory.CompanionTheory.Rodier.wKey d hd) p) := hb
  rw [Prod.Lex.toLex_le_toLex] at h1
  rcases h1 with h | ⟨h, -⟩
  · exact lt_asymm hb' (OrderDual.toDual_lt_toDual.mp h)
  · exact (ne_of_lt hb') (OrderDual.toDual.injective h)

theorem lower_entries {k : Type} [Field k] {h N : ℕ} {d : Fin h → ℕ} {hd : ∑ a, d a = N}
    {x : GL (Fin N) k} (hx : x ∈ unipRadLower k (stdBlocks d hd)) (i j : Fin N) :
    (blk (stdBlocks d hd) i < blk (stdBlocks d hd) j → (x : Matrix (Fin N) (Fin N) k) i j = 0) ∧
      (blk (stdBlocks d hd) i = blk (stdBlocks d hd) j →
        (x : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j) := by
  obtain ⟨hpl, hdiag⟩ := (GlobalTheory.SmGL.mem_unipRadLower k).mp hx
  rw [GlobalTheory.SmGL.mem_parabLower_iff] at hpl
  obtain ⟨⟨a, i'⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, j'⟩, rfl⟩ := (stdBlocks d hd).surjective j
  rw [GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]
  refine ⟨fun hab => hpl a b i' j' hab, fun hab => ?_⟩
  subst hab
  rw [hdiag a i' j', Matrix.one_apply, Matrix.one_apply]
  simp [(stdBlocks d hd).apply_eq_iff_eq]

theorem parab_inf_lower {k : Type} [Field k] {h N : ℕ} {d : Fin h → ℕ} {hd : ∑ a, d a = N}
    {x : GL (Fin N) k} (hp : x ∈ parab k (stdBlocks d hd))
    (hx : x ∈ unipRadLower k (stdBlocks d hd)) : x = 1 := by
  ext i j
  rcases lt_trichotomy (blk (stdBlocks d hd) i) (blk (stdBlocks d hd) j) with hlt | heq | hgt
  · have hij : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hlt
    rw [(lower_entries hx i j).1 hlt]
    simp [Matrix.one_apply, hij]
  · rw [(lower_entries hx i j).2 heq]
    simp
  · have hij : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hgt
    rw [GlobalTheory.SmGL.mem_parab.mp hp i j hgt]
    simp [Matrix.one_apply, hij]

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)


variable {k d hd} in
theorem mem_unipU_iff {u : GL (Fin N) k} :
    u ∈ unipU k d hd ↔ u ∈ unipB k (Fin N) ∧
      pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹ ∈ unipRadLower k (stdBlocks d hd) := by
  rw [GlobalTheory.CompanionTheory.Rodier.unipU, Subgroup.mem_inf, Subgroup.mem_comap]
  rfl

theorem inv_conj_mem_unipU {x : GL (Fin N) k} (hx : x ∈ unipRadLower k (stdBlocks d hd)) :
    (pm k (wOpen d hd))⁻¹ * x * pm k (wOpen d hd) ∈ unipU k d hd := by
  rw [mem_unipU_iff]
  refine ⟨?_, ?_⟩
  · rw [GlobalTheory.SmGL.mem_unipB]
    have hent : ∀ p q, (((pm k (wOpen d hd))⁻¹ * x * pm k (wOpen d hd) : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k) p q = (x : Matrix (Fin N) (Fin N) k) (wOpen d hd p) (wOpen d hd q) :=
      fun p q => inv_conj_apply (wOpen d hd) x p q
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · rw [hent]
      rcases lt_trichotomy (blk (stdBlocks d hd) (wOpen d hd i)) (blk (stdBlocks d hd) (wOpen d hd j))
        with hlt | heq | hgt
      · exact (lower_entries hx _ _).1 hlt
      · rw [(lower_entries hx _ _).2 heq, Matrix.one_apply, if_neg]
        intro h
        exact hji.ne' ((wOpen d hd).injective h)
      · exact absurd (lt_of_blk_lt d hd hgt) (not_lt.mpr hji.le)
    · rw [hent, (lower_entries hx _ _).2 rfl]
      simp
  · have he : pm k (wOpen d hd) * ((pm k (wOpen d hd))⁻¹ * x * pm k (wOpen d hd)) *
        (pm k (wOpen d hd))⁻¹ = x := by group
    rw [he]
    exact hx

theorem eq_of_mul_eq {p u u' : GL (Fin N) k} (hp : p ∈ parab k (stdBlocks d hd))
    (hu : u ∈ unipU k d hd) (hu' : u' ∈ unipU k d hd)
    (e : p * pm k (wOpen d hd) * u = pm k (wOpen d hd) * u') : u = u' := by
  have hv : u' * u⁻¹ ∈ unipU k d hd := (unipU k d hd).mul_mem hu' ((unipU k d hd).inv_mem hu)
  have hlow := (mem_unipU_iff.mp hv).2
  have hpeq : pm k (wOpen d hd) * (u' * u⁻¹) * (pm k (wOpen d hd))⁻¹ = p := by
    calc pm k (wOpen d hd) * (u' * u⁻¹) * (pm k (wOpen d hd))⁻¹
        = (pm k (wOpen d hd) * u') * u⁻¹ * (pm k (wOpen d hd))⁻¹ := by group
      _ = (p * pm k (wOpen d hd) * u) * u⁻¹ * (pm k (wOpen d hd))⁻¹ := by rw [e]
      _ = p := by group
  rw [hpeq] at hlow
  have h1 := parab_inf_lower hp hlow
  rw [h1] at e
  simpa using e

theorem isClosed_unipU : IsClosed (unipU k d hd : Set (GL (Fin N) k)) := by
  have hent : ∀ (i j : Fin N) (c : k),
      IsClosed {g : GL (Fin N) k | (g : Matrix (Fin N) (Fin N) k) i j = c} :=
    fun i j c => isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const
  have hB : IsClosed (unipB k (Fin N) : Set (GL (Fin N) k)) := by
    have hs : (unipB k (Fin N) : Set (GL (Fin N) k)) =
        (⋂ i, ⋂ j, ⋂ (_ : j < i), {g : GL (Fin N) k | (g : Matrix (Fin N) (Fin N) k) i j = 0}) ∩
          ⋂ i, {g : GL (Fin N) k | (g : Matrix (Fin N) (Fin N) k) i i = 1} := by
      ext g
      simp [GlobalTheory.SmGL.mem_unipB]
    rw [hs]
    exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => hent i j 0).inter
      (isClosed_iInter fun i => hent i i 1)
  have hL : IsClosed (unipRadLower k (stdBlocks d hd) : Set (GL (Fin N) k)) := by
    have hs : (unipRadLower k (stdBlocks d hd) : Set (GL (Fin N) k)) =
        (⋂ a, ⋂ b, ⋂ i, ⋂ j, ⋂ (_ : a < b), {g : GL (Fin N) k |
          (g : Matrix (Fin N) (Fin N) k) (stdBlocks d hd ⟨a, i⟩) (stdBlocks d hd ⟨b, j⟩) = 0}) ∩
          ⋂ a, ⋂ i, ⋂ j, {g : GL (Fin N) k |
            (g : Matrix (Fin N) (Fin N) k) (stdBlocks d hd ⟨a, i⟩) (stdBlocks d hd ⟨a, j⟩) =
              (1 : Matrix (Fin (d a)) (Fin (d a)) k) i j} := by
      ext g
      simp [GlobalTheory.SmGL.mem_unipRadLower, GlobalTheory.SmGL.mem_parabLower_iff]
    rw [hs]
    exact (isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun i =>
      isClosed_iInter fun j => isClosed_iInter fun _ => hent _ _ _).inter
      (isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun j => hent _ _ _)
  have hc : Continuous fun u : GL (Fin N) k => pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹ :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hs : (unipU k d hd : Set (GL (Fin N) k)) =
      (unipB k (Fin N) : Set (GL (Fin N) k)) ∩
        (fun u : GL (Fin N) k => pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹) ⁻¹'
          (unipRadLower k (stdBlocks d hd) : Set (GL (Fin N) k)) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
    exact mem_unipU_iff
  rw [hs]
  exact hB.inter (hL.preimage hc)

end GlobalTheory.CompanionTheory.Rodier.LowerOpen

namespace GlobalTheory.CompanionTheory.Rodier

theorem unipU_open_cell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ x ∈ unipRadLower k (stdBlocks d hd), (pm k (wOpen d hd))⁻¹ * x * pm k (wOpen d hd) ∈ unipU k d hd) ∧ (∀ p ∈ parab k (stdBlocks d hd), ∀ u ∈ unipU k d hd, ∀ u' ∈ unipU k d hd, p * pm k (wOpen d hd) * u = pm k (wOpen d hd) * u' → u = u') ∧ IsClosed (unipU k d hd : Set (GL (Fin N) k)) := by
  intro k _ _ _ _ h N d hd
  exact ⟨fun x hx => LowerOpen.inv_conj_mem_unipU k d hd hx,
    fun p hp u hu u' hu' e => LowerOpen.eq_of_mul_eq k d hd hp hu hu' e,
    LowerOpen.isClosed_unipU k d hd⟩

end GlobalTheory.CompanionTheory.Rodier
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellUnipotentUniquenessClosedStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_cell_unipotent_uniqueness_closed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ x ∈ unipRadLower k (stdBlocks d hd), (pm k (wOpen d hd))⁻¹ * x * pm k (wOpen d hd) ∈ unipU k d hd) ∧ (∀ p ∈ parab k (stdBlocks d hd), ∀ u ∈ unipU k d hd, ∀ u' ∈ unipU k d hd, p * pm k (wOpen d hd) * u = pm k (wOpen d hd) * u' → u = u') ∧ IsClosed (unipU k d hd : Set (GL (Fin N) k)) := by
  first | exact @GlobalTheory.CompanionTheory.Rodier.unipU_open_cell | exact GlobalTheory.CompanionTheory.Rodier.unipU_open_cell | (intros; apply GlobalTheory.CompanionTheory.Rodier.unipU_open_cell <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetIntegralInvMulVec
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem setIntegral_inv_mulVec {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k)
    [ν.IsAddHaarMeasure] (m : ℕ) (g : GL (Fin m) k) (M : Set (Fin m → k))
    (F : (Fin m → k) → ℂ) :
    ∫ x in M, F (((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) *ᵥ x) ∂(piHaar ν m) =
      ((nabs k (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) *
        ∫ y in {y | (g : Matrix (Fin m) (Fin m) k) *ᵥ y ∈ M}, F y ∂(piHaar ν m) := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  haveI := GlobalTheory.SplitWeil.secondCountable k
  have hinv : ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) * (g : Matrix (Fin m) (Fin m) k) = 1 :=
    Units.inv_mul g
  have hinv' : (g : Matrix (Fin m) (Fin m) k) * ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) = 1 :=
    Units.mul_inv g
  let e : (Fin m → k) ≃ᵐ (Fin m → k) :=
    { toFun := fun x => (g : Matrix (Fin m) (Fin m) k) *ᵥ x
      invFun := fun x => ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) *ᵥ x
      left_inv := fun x => by simp only [mulVec_mulVec, hinv, one_mulVec]
      right_inv := fun x => by simp only [mulVec_mulVec, hinv', one_mulVec]
      measurable_toFun := (continuous_const.matrix_mulVec continuous_id).measurable
      measurable_invFun := (continuous_const.matrix_mulVec continuous_id).measurable }
  have he : MeasurableEmbedding (Matrix.mulVec (g : Matrix (Fin m) (Fin m) k)) :=
    e.measurableEmbedding
  have hμ := GlobalTheory.UnipChange.smul_map_mulVec_pi ν (g : Matrix (Fin m) (Fin m) k)
    (Matrix.GeneralLinearGroup.det g) (Matrix.GeneralLinearGroup.val_det_apply g)
  unfold GlobalTheory.CompanionTheory.MirPair.piHaar GlobalTheory.SplitWeil.nabs
  conv_lhs => rw [← hμ]
  rw [Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal, Complex.real_smul,
    he.restrict_map, he.integral_map]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [mulVec_mulVec, hinv, one_mulVec]

end GlobalTheory.CompanionTheory.MirPair
end
