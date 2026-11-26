module

public import GroundTheory.AutomorphicForms.HarishChandraCentre.Projection

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.HarishChandraCentre.Fischer
section -- merged from GroundTheory.AutomorphicForms.HarishChandraCentre.FischerForm
namespace GroundTheory.Automorphic.HarishChandra

open MvPolynomial

variable {σ : Type*}

def mfact (m : σ →₀ ℕ) : ℕ := m.prod fun _ k => k.factorial

theorem mfact_pos (m : σ →₀ ℕ) : 0 < mfact m :=
  Finset.prod_pos fun _ _ => Nat.factorial_pos _

theorem mfact_add_single [DecidableEq σ] (s : σ →₀ ℕ) (a : σ) :
    mfact (s + Finsupp.single a 1) = mfact s * (s a + 1) := by
  unfold mfact
  have h1 := Finsupp.mul_prod_erase' (s + Finsupp.single a 1) a (fun _ k => k.factorial)
    (fun _ => Nat.factorial_zero)
  have h2 := Finsupp.mul_prod_erase' s a (fun _ k => k.factorial) (fun _ => Nat.factorial_zero)
  have he : Finsupp.erase a (s + Finsupp.single a 1) = Finsupp.erase a s := by
    ext v
    by_cases hv : v = a
    · subst hv; simp
    · simp [Finsupp.erase_ne hv]
  rw [← h1, ← h2, he]
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  ring

noncomputable def fischer (f g : MvPolynomial σ ℂ) : ℂ :=
  ∑ m ∈ g.support, (mfact m : ℂ) * star (AddMonoidAlgebra.coeff f m) * AddMonoidAlgebra.coeff g m

theorem fischer_eq_sum (f g : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ)) (hg : g.support ⊆ s) :
    fischer f g = ∑ m ∈ s, (mfact m : ℂ) * star (AddMonoidAlgebra.coeff f m) * AddMonoidAlgebra.coeff g m :=
  Finset.sum_subset hg fun m _ hm => by simp [MvPolynomial.notMem_support_iff.1 hm]

theorem fischer_add_left (f f' g : MvPolynomial σ ℂ) :
    fischer (f + f') g = fischer f g + fischer f' g := by
  simp only [fischer, MvPolynomial.coeff_add, star_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem fischer_smul_left (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fischer (c • f) g = star c * fischer f g := by
  simp only [fischer, coeff_smul, smul_eq_mul, star_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem fischer_add_right (f g g' : MvPolynomial σ ℂ) :
    fischer f (g + g') = fischer f g + fischer f g' := by
  classical
  set s := g.support ∪ g'.support
  rw [fischer_eq_sum f (g + g') s (MvPolynomial.support_add),
    fischer_eq_sum f g s Finset.subset_union_left, fischer_eq_sum f g' s Finset.subset_union_right]
  simp only [MvPolynomial.coeff_add, mul_add, Finset.sum_add_distrib]

theorem fischer_smul_right (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fischer f (c • g) = c * fischer f g := by
  rw [fischer_eq_sum f (c • g) g.support (MvPolynomial.support_smul), fischer, Finset.mul_sum]
  simp only [coeff_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

@[simp] theorem fischer_zero_left (g : MvPolynomial σ ℂ) : fischer 0 g = 0 := by simp [fischer]

@[simp] theorem fischer_zero_right (f : MvPolynomial σ ℂ) : fischer f 0 = 0 := by simp [fischer]

theorem fischer_sum_left {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℂ)
    (g : MvPolynomial σ ℂ) : fischer (∑ i ∈ s, f i) g = ∑ i ∈ s, fischer (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fischer_add_left, ih]

theorem fischer_sum_right {ι : Type*} (s : Finset ι) (f : MvPolynomial σ ℂ)
    (g : ι → MvPolynomial σ ℂ) : fischer f (∑ i ∈ s, g i) = ∑ i ∈ s, fischer f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fischer_add_right, ih]

theorem fischer_conj_symm (f g : MvPolynomial σ ℂ) : star (fischer f g) = fischer g f := by
  classical
  rw [fischer_eq_sum g f (f.support ∪ g.support) Finset.subset_union_left,
    fischer_eq_sum f g (f.support ∪ g.support) Finset.subset_union_right, star_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [star_mul', Complex.star_def, Complex.conj_natCast, Complex.conj_conj]
  ring

theorem fischer_monomial [DecidableEq σ] (s t : σ →₀ ℕ) (c d : ℂ) :
    fischer (monomial s c) (monomial t d) = if s = t then (mfact s : ℂ) * star c * d else 0 := by
  rw [fischer_eq_sum _ _ {t} (MvPolynomial.support_monomial_subset), Finset.sum_singleton]
  simp only [coeff_monomial]
  by_cases h : s = t
  · subst h; simp
  · simp [h]

theorem fischer_X_mul (a : σ) (f g : MvPolynomial σ ℂ) :
    fischer (X a * f) g = fischer f (pderiv a g) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq => rw [mul_add, fischer_add_left, fischer_add_left, hp, hq]
  | monomial s c =>
    induction g using MvPolynomial.induction_on' with
    | add p q hp hq => rw [fischer_add_right, map_add (f := _), fischer_add_right, hp, hq]
    | monomial t d =>
      rw [X, monomial_mul, one_mul, pderiv_monomial, fischer_monomial, fischer_monomial]
      by_cases ht : t a = 0
      · have hne : Finsupp.single a 1 + s ≠ t := by
          intro h
          have := congrArg (fun m => m a) h
          simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at this
          omega
        rw [if_neg hne]
        split_ifs <;> simp [ht]
      · have hle : Finsupp.single a 1 ≤ t := by
          intro v
          by_cases hv : v = a
          · subst hv; simp only [Finsupp.single_eq_same]; omega
          · rw [Finsupp.single_apply, if_neg (Ne.symm hv)]; exact Nat.zero_le _
        have hiff : Finsupp.single a 1 + s = t ↔ s = t - Finsupp.single a 1 := by
          constructor
          · rintro rfl; simp
          · rintro rfl; rw [add_comm]; exact tsub_add_cancel_of_le hle
        by_cases h : s = t - Finsupp.single a 1
        · have h' := hiff.2 h
          rw [if_pos h', if_pos h]
          have hsa : (s a + 1 : ℕ) = t a := by
            rw [← h']; simp [add_comm]
          rw [add_comm (Finsupp.single a 1) s, mfact_add_single, ← hsa]
          push_cast
          ring
        · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]

theorem fischer_pderiv (a : σ) (f g : MvPolynomial σ ℂ) :
    fischer (pderiv a f) g = fischer f (X a * g) := by
  rw [← fischer_conj_symm, ← fischer_X_mul, fischer_conj_symm]

theorem fischer_self (f : MvPolynomial σ ℂ) :
    fischer f f = ((∑ m ∈ f.support, (mfact m : ℝ) * Complex.normSq (AddMonoidAlgebra.coeff f m) : ℝ) : ℂ) := by
  rw [fischer]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_assoc, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]

theorem fischer_self_eq_zero_iff (f : MvPolynomial σ ℂ) : fischer f f = 0 ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  rw [fischer_self, Complex.ofReal_eq_zero] at h
  have hnn : ∀ m ∈ f.support, 0 ≤ (mfact m : ℝ) * Complex.normSq (AddMonoidAlgebra.coeff f m) :=
    fun m _ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h
  ext m
  by_contra hm
  have hm' : m ∈ f.support := MvPolynomial.mem_support_iff.2 hm
  have := hz m hm'
  rcases mul_eq_zero.1 this with h1 | h1
  · exact (Nat.cast_ne_zero.2 (mfact_pos m).ne') h1
  · exact hm (Complex.normSq_eq_zero.1 h1)

end GroundTheory.Automorphic.HarishChandra
end

namespace GroundTheory.Automorphic.HarishChandra

open MvPolynomial

variable {n : ℕ}

theorem fischer_rowOp (i j : Fin n) (f g : Poly n) :
    fischer (rowOp i j f) g = fischer f (rowOp j i g) := by
  rw [rowOp_apply, rowOp_apply, fischer_sum_left, fischer_sum_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fischer_X_mul, fischer_pderiv]

theorem rowOp_X (i j b c : Fin n) :
    rowOp i j (X (b, c) : Poly n) = if b = j then X (i, c) else 0 := by
  rw [rowOp_apply]
  by_cases hb : b = j
  · subst hb
    rw [if_pos rfl, Finset.sum_eq_single c]
    · rw [pderiv_X_self, mul_one]
    · intro k _ hk
      rw [pderiv_X_of_ne (by intro h; exact hk (Prod.ext_iff.1 h).2.symm), mul_zero]
    · simp
  · rw [if_neg hb]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [pderiv_X_of_ne (by intro h; exact hb (Prod.ext_iff.1 h).1), mul_zero]

noncomputable def rowDer (i j : Fin n) : Derivation ℂ (Poly n) (Poly n) :=
  Derivation.mk' (rowOp i j) fun a b => by
    rw [rowOp_apply, rowOp_apply, rowOp_apply, smul_eq_mul, smul_eq_mul, Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring

theorem rowDer_apply (i j : Fin n) (f : Poly n) : rowDer i j f = rowOp i j f := rfl

theorem rowOp_comm_self (a i j : Fin n) :
    rowOp a a * rowOp i j =
      rowOp i j * rowOp a a + ((if i = a then 1 else 0) - (if j = a then 1 else 0) : ℂ) • rowOp i j := by
  have key : ⁅rowDer a a, rowDer i j⁆ =
      ((if i = a then 1 else 0) - (if j = a then 1 else 0) : ℂ) • rowDer i j := by
    apply MvPolynomial.derivation_ext
    rintro ⟨b, c⟩
    rw [Derivation.commutator_apply, Derivation.smul_apply, rowDer_apply, rowDer_apply,
      rowDer_apply, rowDer_apply]
    by_cases hbj : b = j <;> by_cases hba : b = a <;> by_cases hia : i = a <;>
      simp_all [rowOp_X]
  refine LinearMap.ext fun f => ?_
  have h := congrArg (fun D : Derivation ℂ (Poly n) (Poly n) => D f) key
  simp only [Derivation.commutator_apply, Derivation.smul_apply, rowDer_apply] at h
  simp only [mul_apply_eq_comp, LinearMap.add_apply, LinearMap.smul_apply]
  rw [← h]
  abel

def rowWt (m : Fin n × Fin n →₀ ℕ) (i : Fin n) : ℕ := ∑ k, m (i, k)

theorem rowOp_self_monomial (i : Fin n) (s : Fin n × Fin n →₀ ℕ) (c : ℂ) :
    rowOp i i (monomial s c) = monomial s (c * (rowWt s i : ℂ)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [rowOp_apply, rowWt, Nat.cast_sum, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pderiv_monomial, X, monomial_mul, one_mul]
  by_cases hk : s (i, k) = 0
  · simp [hk]
  · have hle : Finsupp.single (i, k) 1 ≤ s := by
      intro v
      rw [Finsupp.single_apply]
      split_ifs with hv
      · subst hv; omega
      · exact Nat.zero_le _
    rw [add_tsub_cancel_of_le hle]

theorem coeff_rowOp_self (i : Fin n) (m : Fin n × Fin n →₀ ℕ) (f : Poly n) :
    AddMonoidAlgebra.coeff (rowOp i i f) m = (rowWt m i : ℂ) * AddMonoidAlgebra.coeff f m := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]
  | monomial s c =>
    rw [rowOp_self_monomial, coeff_monomial, coeff_monomial]
    by_cases h : s = m
    · subst h; simp [mul_comm]
    · simp [h]

theorem rowWt_eq_of_eigen {h : Poly n} {c : Fin n → ℂ} (hc : ∀ a, rowOp a a h = c a • h)
    {m : Fin n × Fin n →₀ ℕ} (hm : m ∈ h.support) (a : Fin n) : (rowWt m a : ℂ) = c a := by
  have := congrArg (AddMonoidAlgebra.coeff · m) (hc a)
  rw [coeff_rowOp_self, coeff_smul, smul_eq_mul] at this
  exact mul_right_cancel₀ (MvPolynomial.mem_support_iff.1 hm) this

noncomputable def wtProj (μ : Fin n → ℕ) : Module.End ℂ (Poly n) where
  toFun f := ∑ m ∈ f.support with rowWt m = μ, monomial m (AddMonoidAlgebra.coeff f m)
  map_add' f g := by
    classical
    ext m
    simp only [coeff_sum, coeff_monomial, MvPolynomial.coeff_add]
    simp only [Finset.sum_ite_eq', Finset.mem_filter, MvPolynomial.mem_support_iff, MvPolynomial.coeff_add]
    by_cases hm : rowWt m = μ <;> simp only [hm, and_true, and_false, if_false]
    · by_cases h1 : AddMonoidAlgebra.coeff f m = 0 <;> by_cases h2 : AddMonoidAlgebra.coeff g m = 0 <;> by_cases h3 : AddMonoidAlgebra.coeff f m + AddMonoidAlgebra.coeff g m = 0 <;>
        simp_all
    · simp
  map_smul' c f := by
    classical
    ext m
    simp only [coeff_sum, coeff_monomial, coeff_smul, smul_eq_mul, RingHom.id_apply]
    simp only [Finset.sum_ite_eq', Finset.mem_filter, MvPolynomial.mem_support_iff, coeff_smul,
      smul_eq_mul]
    by_cases hm : rowWt m = μ <;> simp only [hm, and_true, and_false, if_false]
    · by_cases h1 : AddMonoidAlgebra.coeff f m = 0 <;> by_cases h2 : c * AddMonoidAlgebra.coeff f m = 0 <;> simp_all
    · simp

theorem coeff_wtProj (μ : Fin n → ℕ) (m : Fin n × Fin n →₀ ℕ) (f : Poly n) :
    AddMonoidAlgebra.coeff (wtProj μ f) m = if rowWt m = μ then AddMonoidAlgebra.coeff f m else 0 := by
  classical
  change AddMonoidAlgebra.coeff (∑ m ∈ f.support with rowWt m = μ, monomial m (AddMonoidAlgebra.coeff f m)) m = _
  simp only [coeff_sum, coeff_monomial, Finset.sum_ite_eq', Finset.mem_filter,
    MvPolynomial.mem_support_iff]
  by_cases hm : rowWt m = μ
  · by_cases h1 : AddMonoidAlgebra.coeff f m = 0 <;> simp [hm, h1]
  · simp [hm]

theorem wtProj_eq_self_iff (μ : Fin n → ℕ) (f : Poly n) :
    wtProj μ f = f ↔ ∀ m ∈ f.support, rowWt m = μ := by
  constructor
  · intro h m hm
    by_contra hne
    have := congrArg (AddMonoidAlgebra.coeff · m) h
    rw [coeff_wtProj, if_neg hne] at this
    exact MvPolynomial.mem_support_iff.1 hm this.symm
  · intro h
    ext m
    rw [coeff_wtProj]
    split_ifs with hm
    · rfl
    · by_contra hc
      exact hm (h m (MvPolynomial.mem_support_iff.2 (Ne.symm hc)))

theorem wtProj_wtProj (μ ν : Fin n → ℕ) (f : Poly n) :
    wtProj μ (wtProj ν f) = if μ = ν then wtProj ν f else 0 := by
  by_cases h : μ = ν
  · subst h
    rw [if_pos rfl]
    ext m
    rw [coeff_wtProj, coeff_wtProj]
    split_ifs <;> rfl
  · rw [if_neg h]
    ext m
    rw [coeff_wtProj, coeff_wtProj, MvPolynomial.coeff_zero]
    split_ifs with h1 h2
    · exact absurd (h1.symm.trans h2) h
    · rfl
    · rfl

theorem rowOp_self_of_wtProj (μ : Fin n → ℕ) (v : Poly n) (i : Fin n) (h : wtProj μ v = v) :
    rowOp i i v = (μ i : ℂ) • v := by
  ext m
  rw [coeff_rowOp_self, coeff_smul, smul_eq_mul]
  by_cases hm : m ∈ v.support
  · rw [(wtProj_eq_self_iff μ v).1 h m hm]
  · rw [MvPolynomial.notMem_support_iff.1 hm]; simp

theorem wtProj_eq_self_of_eigen {h : Poly n} (ν : Fin n → ℕ)
    (hc : ∀ a, rowOp a a h = (ν a : ℂ) • h) : wtProj ν h = h := by
  rw [wtProj_eq_self_iff]
  intro m hm
  funext a
  exact_mod_cast rowWt_eq_of_eigen hc hm a

theorem sum_wtProj (f : Poly n) : ∑ ν ∈ f.support.image rowWt, wtProj ν f = f := by
  classical
  ext m
  rw [coeff_sum]
  simp only [coeff_wtProj, Finset.sum_ite_eq, Finset.mem_image]
  split_ifs with h
  · rfl
  · by_contra hc
    exact h ⟨m, MvPolynomial.mem_support_iff.2 (Ne.symm hc), rfl⟩

theorem fischer_wtProj (μ : Fin n → ℕ) (f g : Poly n) :
    fischer (wtProj μ f) g = fischer f (wtProj μ g) := by
  classical
  set s := f.support ∪ g.support
  have hg : (wtProj μ g).support ⊆ s := fun m hm => by
    rw [MvPolynomial.mem_support_iff, coeff_wtProj] at hm
    split_ifs at hm
    · exact Finset.mem_union_right _ (MvPolynomial.mem_support_iff.2 hm)
    · exact absurd rfl hm
  rw [fischer_eq_sum _ _ s Finset.subset_union_right, fischer_eq_sum _ _ s hg]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_wtProj, coeff_wtProj]
  split_ifs <;> simp

theorem wtProj_comm {T : Module.End ℂ (Poly n)} (hT : ∀ a, T * rowOp a a = rowOp a a * T)
    (μ : Fin n → ℕ) (f : Poly n) : wtProj μ (T f) = T (wtProj μ f) := by
  classical
  have hν : ∀ ν, wtProj ν (T (wtProj ν f)) = T (wtProj ν f) := fun ν =>
    wtProj_eq_self_of_eigen ν fun a => by
      have h1 := congrArg (fun S : Module.End ℂ (Poly n) => S (wtProj ν f)) (hT a)
      simp only [mul_apply_eq_comp] at h1
      rw [← h1, rowOp_self_of_wtProj ν _ a (by rw [wtProj_wtProj, if_pos rfl]), map_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [← sum_wtProj f, map_sum, map_sum]
  rw [Finset.sum_eq_single μ]
  · exact hν μ
  · intro ν _ hne
    rw [← hν ν, wtProj_wtProj, if_neg (Ne.symm hne)]
  · intro hμ
    have h0 : wtProj μ f = 0 := by
      ext m
      rw [coeff_wtProj, MvPolynomial.coeff_zero]
      split_ifs with hm
      · by_contra hc
        exact hμ (Finset.mem_image.2 ⟨m, MvPolynomial.mem_support_iff.2 hc, hm⟩)
      · rfl
    rw [h0, map_zero, map_zero]

def wtHeight (μ : Fin n → ℕ) : ℤ := ∑ a, ((n : ℤ) - a) * μ a

theorem rowOp_shift {μ : Fin n → ℕ} {v : Poly n} (hv : wtProj μ v = v) {i j : Fin n} (hij : i < j)
    (hne : rowOp i j v ≠ 0) :
    ∃ μ' : Fin n → ℕ, wtProj μ' (rowOp i j v) = rowOp i j v ∧ ∑ a, μ' a = ∑ a, μ a ∧
      wtHeight μ < wtHeight μ' := by
  classical
  set w := rowOp i j v
  have heig : ∀ a, rowOp a a w =
      ((μ a : ℂ) + ((if i = a then 1 else 0) - (if j = a then 1 else 0))) • w := by
    intro a
    have h1 := congrArg (fun S : Module.End ℂ (Poly n) => S v) (rowOp_comm_self a i j)
    simp only [mul_apply_eq_comp, LinearMap.add_apply, LinearMap.smul_apply] at h1
    rw [h1, rowOp_self_of_wtProj μ v a hv, map_smul, add_smul]
  obtain ⟨m, hm⟩ : ∃ m, m ∈ w.support := by
    by_contra h
    push Not at h
    exact hne (MvPolynomial.support_eq_empty.1 (Finset.eq_empty_of_forall_notMem h))
  have hwt : ∀ m' ∈ w.support, ∀ a, ((rowWt m' a : ℕ) : ℤ) =
      (μ a : ℤ) + ((if i = a then 1 else 0) - (if j = a then 1 else 0)) := by
    intro m' hm' a
    have := rowWt_eq_of_eigen heig hm' a
    have : ((rowWt m' a : ℤ) : ℂ) = (((μ a : ℤ) + ((if i = a then 1 else 0) -
        (if j = a then 1 else 0)) : ℤ) : ℂ) := by
      push_cast; rw [this]
    exact_mod_cast this
  refine ⟨rowWt m, ?_, ?_, ?_⟩
  · rw [wtProj_eq_self_iff]
    intro m' hm'
    funext a
    have h1 := hwt m' hm' a
    have h2 := hwt m hm a
    omega
  · have : ∀ a, ((rowWt m a : ℕ) : ℤ) = (μ a : ℤ) + ((if i = a then 1 else 0) - (if j = a then 1 else 0)) :=
      hwt m hm
    have hs : ((∑ a, rowWt m a : ℕ) : ℤ) = ((∑ a, μ a : ℕ) : ℤ) := by
      push_cast
      rw [Finset.sum_congr rfl fun a _ => this a, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp
    exact_mod_cast hs
  · have hsum : wtHeight (rowWt m) = wtHeight μ + (((n : ℤ) - i) - ((n : ℤ) - j)) := by
      unfold wtHeight
      simp_rw [hwt m hm]
      simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have : ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by exact_mod_cast hij
    rw [hsum]
    linarith

theorem eq_zero_of_forall_highestWeight (T T' : Module.End ℂ (Poly n))
    (hcomm : ∀ i j, T * rowOp i j = rowOp i j * T)
    (hadj : ∀ f g, fischer (T f) g = fischer f (T' g))
    (hnormal : T * T' = T' * T)
    (hhw : ∀ (v : Poly n) (μ : Fin n → ℕ), (∀ i j, i < j → rowOp i j v = 0) → wtProj μ v = v →
      T v = 0) : T = 0 := by
  classical

  have hadj' : ∀ f g, fischer (T' f) g = fischer f (T g) := fun f g => by
    rw [← fischer_conj_symm, ← hadj, fischer_conj_symm]

  have hker : ∀ k, T k = 0 → T' k = 0 := by
    intro k hk
    have h1 : fischer (T' k) (T' k) = fischer (T k) (T k) := by
      rw [hadj', hadj]
      have := congrArg (fun S : Module.End ℂ (Poly n) => S k) hnormal
      simp only [mul_apply_eq_comp] at this
      rw [this]
    rw [hk, fischer_zero_left] at h1
    exact (fischer_self_eq_zero_iff _).1 h1
  set S : Set (Poly n) := {s | ∀ k, T k = 0 → fischer s k = 0}
  have hS1 : ∀ f, T f ∈ S := fun f k hk => by rw [hadj, hker k hk, fischer_zero_right]
  have hS2 : ∀ μ, ∀ s ∈ S, wtProj μ s ∈ S := fun μ s hs k hk => by
    rw [fischer_wtProj]
    refine hs _ ?_
    rw [← wtProj_comm (fun a => hcomm a a), hk, map_zero]
  have hS3 : ∀ i j, ∀ s ∈ S, rowOp i j s ∈ S := fun i j s hs k hk => by
    rw [fischer_rowOp]
    refine hs _ ?_
    have := congrArg (fun S : Module.End ℂ (Poly n) => S k) (hcomm j i)
    simp only [mul_apply_eq_comp] at this
    rw [this, hk, map_zero]
  have hS4 : ∀ s ∈ S, T s = 0 → s = 0 := fun s hs hT =>
    (fischer_self_eq_zero_iff s).1 (hs s hT)
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.zero_apply]
  by_contra hg
  set g := T f
  obtain ⟨m₀, hm₀⟩ : ∃ m, m ∈ g.support := by
    by_contra h
    push Not at h
    exact hg (MvPolynomial.support_eq_empty.1 (Finset.eq_empty_of_forall_notMem h))
  set μ₀ := rowWt m₀
  have hμ₀ : wtProj μ₀ g ≠ 0 := by
    intro h
    have := congrArg (AddMonoidAlgebra.coeff · m₀) h
    rw [coeff_wtProj, if_pos rfl, MvPolynomial.coeff_zero] at this
    exact MvPolynomial.mem_support_iff.1 hm₀ this
  set d := ∑ a, μ₀ a
  set W : Finset (Fin n → ℕ) :=
    ((Finset.univ : Finset (Fin n → Fin (d + 1))).image fun μ i => (μ i : ℕ)).filter
      fun μ => ∑ a, μ a = d ∧ ∃ s ∈ S, wtProj μ s ≠ 0
  have hmemW : ∀ μ : Fin n → ℕ, ∑ a, μ a = d → (∃ s ∈ S, wtProj μ s ≠ 0) → μ ∈ W := by
    intro μ hsum hex
    refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨fun i => ⟨μ i, ?_⟩, Finset.mem_univ _, rfl⟩,
      hsum, hex⟩
    have : μ i ≤ d := hsum ▸ Finset.single_le_sum (fun a _ => Nat.zero_le (μ a)) (Finset.mem_univ i)
    omega
  have hW : W.Nonempty := ⟨μ₀, hmemW μ₀ rfl ⟨g, hS1 f, hμ₀⟩⟩
  obtain ⟨μ, hμW, hμmax⟩ := Finset.exists_max_image W wtHeight hW
  obtain ⟨hμsum, s, hs, hvne⟩ := (Finset.mem_filter.1 hμW).2
  set v := wtProj μ s
  have hvS : v ∈ S := hS2 μ s hs
  have hvv : wtProj μ v = v := by rw [wtProj_wtProj, if_pos rfl]
  have hhwv : ∀ i j, i < j → rowOp i j v = 0 := by
    intro i j hij
    by_contra hne
    obtain ⟨μ', h1, h2, h3⟩ := rowOp_shift hvv hij hne
    have hmem : μ' ∈ W := hmemW μ' (h2.trans hμsum) ⟨rowOp i j v, hS3 i j v hvS, by rw [h1]; exact hne⟩
    exact absurd (hμmax μ' hmem) (not_le.2 h3)
  exact hvne (hS4 v hvS (hhw v μ hhwv hvv))

end GroundTheory.Automorphic.HarishChandra
end

namespace GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

open MvPolynomial

variable {n : ℕ}

theorem exists_adjoint (u : U n) :
    ∃ u' : U n, ∀ f g : Poly n, fischer (rho 0 u f) g = fischer f (rho 0 u' g) := by
  induction u using U.induction with
  | halg r =>
    refine ⟨algebraMap ℂ (U n) (star r), fun f g => ?_⟩
    simp only [AlgHom.commutes, Module.algebraMap_end_apply, fischer_smul_left, fischer_smul_right]
  | hι X =>
    refine ⟨∑ a : Fin n × Fin n, star (X a.1 a.2) • e (a.2, a.1), fun f g => ?_⟩
    rw [ι_eq_sum_e]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, fischer_sum_left,
      fischer_sum_right, fischer_smul_left, fischer_smul_right, star_star]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show e a = e (a.1, a.2) from rfl, rho_zero_e, rho_zero_e, fischer_rowOp]
  | hmul a b ha hb =>
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    refine ⟨b' * a', fun f g => ?_⟩
    rw [map_mul, Module.End.mul_apply, ha', hb', map_mul, Module.End.mul_apply]
  | hadd a b ha hb =>
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    refine ⟨a' + b', fun f g => ?_⟩
    rw [map_add (f := _), LinearMap.add_apply, fischer_add_left, ha', hb', map_add (f := _), LinearMap.add_apply,
      fischer_add_right]

theorem eq_zero_of_mem_center_of_hcProjLin_eq_zero {z : U n}
    (hz : z ∈ Subalgebra.center ℂ (U n)) (h : hcProjLin z = 0) : z = 0 := by
  obtain ⟨z', hz'⟩ := exists_adjoint z
  have hc : ∀ u : U n, u * z = z * u := fun u => (Subalgebra.mem_center_iff.1 hz) u
  apply eq_zero_of_rho_zero_eq_zero
  refine eq_zero_of_forall_highestWeight (rho 0 z) (rho 0 z') ?_ hz' ?_ ?_
  · intro i j
    rw [← rho_zero_e, ← map_mul, ← map_mul, hc]
  · rw [← map_mul, ← map_mul, hc]
  · intro v μ hup hwt
    have := rep_apply_of_highestWeight (rho 0) (fun i => (μ i : ℂ)) (v := v)
      (fun a ha => by
        rw [show e a = e (a.1, a.2) from rfl, rho_zero_e]
        exact hup a.1 a.2 ha)
      (fun k => by rw [rho_zero_e]; exact rowOp_self_of_wtProj μ v k hwt)
      (fun k => hc (e (k, k)))
    rw [this, h, map_zero, zero_smul]

theorem hcProjLin_injOn_center :
    Set.InjOn (hcProjLin (n := n)) (Subalgebra.center ℂ (U n) : Set (U n)) := by
  intro z hz z' hz' h
  have := eq_zero_of_mem_center_of_hcProjLin_eq_zero (Subalgebra.sub_mem _ hz hz')
    (by rw [map_sub, h, sub_self])
  exact sub_eq_zero.1 this

theorem translate_neg_translate (c : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ) :
    translate (-c) (translate c p) = p := by
  refine MvPolynomial.funext fun lam => ?_
  rw [eval_translate, eval_translate, neg_add_cancel_right]

theorem translate_injective (c : Fin n → ℂ) : Function.Injective (translate (n := n) c) :=
  Function.LeftInverse.injective (translate_neg_translate c)

theorem harishChandraHom_injective : Function.Injective (harishChandraHom (n := n)) := by
  intro z z' h
  rw [harishChandraHom_apply, harishChandraHom_apply] at h
  exact Subtype.ext (hcProjLin_injOn_center z.2 z'.2 (translate_injective _ h))

end GroundTheory.Automorphic.HarishChandra
