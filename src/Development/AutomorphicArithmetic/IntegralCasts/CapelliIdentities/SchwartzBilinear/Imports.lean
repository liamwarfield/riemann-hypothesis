module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.Imports
namespace UpperTheory.Reformulated.B.P6.r08a

theorem GlobalTheory.CompanionTheory.AvgFree.Cov.exists_sep :
    ∀ {K : Type} [inst : AddCommGroup K] (H : AddSubgroup K) (T : Finset K), ∃ Rep ⊆ T, (∀ x ∈ T, ∃ r ∈ Rep, x - r ∈ H) ∧ ∀ r ∈ Rep, ∀ r' ∈ Rep, r - r' ∈ H → r = r' := by
  intro K inst H T
  classical
  refine Finset.induction_on T ?_ ?_
  · refine ⟨∅, Finset.Subset.refl _, ?_, ?_⟩
    · intro x hx
      exact absurd hx (Finset.notMem_empty x)
    · intro r hr
      exact absurd hr (Finset.notMem_empty r)
  · intro a S _ha ih
    obtain ⟨Rep, hsub, hcov, hsep⟩ := ih
    by_cases h : ∃ r ∈ Rep, a - r ∈ H
    · refine ⟨Rep, hsub.trans (Finset.subset_insert a S), ?_, hsep⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with hxa | hx
      · rw [hxa]
        exact h
      · exact hcov x hx
    · have h' : ∀ r ∈ Rep, a - r ∉ H := fun r hr har => h ⟨r, hr, har⟩
      refine ⟨insert a Rep, Finset.insert_subset_insert a hsub, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with hxa | hx
        · refine ⟨a, Finset.mem_insert_self a Rep, ?_⟩
          rw [hxa, sub_self]
          exact H.zero_mem
        · obtain ⟨r, hr, hxr⟩ := hcov x hx
          exact ⟨r, Finset.mem_insert_of_mem hr, hxr⟩
      · intro r hr r' hr' hrr
        rcases Finset.mem_insert.mp hr with hra | hr
        · rcases Finset.mem_insert.mp hr' with hr'a | hr'
          · rw [hra, hr'a]
          · rw [hra] at hrr
            exact absurd hrr (h' r' hr')
        · rcases Finset.mem_insert.mp hr' with hr'a | hr'
          · rw [hr'a] at hrr
            have hn := H.neg_mem hrr
            rw [neg_sub] at hn
            exact absurd hn (h' r hr)
          · exact hsep r hr r' hr' hrr

end UpperTheory.Reformulated.B.P6.r08a
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.EigenvectorsSumZeroEqZero
namespace UpperTheory.Reformulated.B.P6.r14a

theorem eigenvectors_sum_zero_eq_zero {ι κ A : Type} [DecidableEq ι] [AddCommGroup A] [Module ℂ A]
    (T : κ → Module.End ℂ A) (f : ι → κ → ℂ) (hf : Function.Injective f) :
    ∀ (s : Finset ι) (v : ι → A), (∀ i ∈ s, ∀ k, T k (v i) = f i k • v i) →
      ∑ i ∈ s, v i = 0 → ∀ i ∈ s, v i = 0 := by
  classical
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro v hv hsum a ha
    by_cases hall : ∀ b ∈ s, b = a
    · have h1 : ∑ i ∈ s, v i = v a := by
        apply Finset.sum_eq_single_of_mem a ha
        intro b hb hba
        exact absurd (hall b hb) hba
      rw [← h1]
      exact hsum
    · push_neg at hall
      obtain ⟨b, hb, hba⟩ := hall
      have hfb : f b ≠ f a := fun h => hba (hf h)
      obtain ⟨k, hk⟩ : ∃ k, f b k ≠ f a k := Function.ne_iff.mp hfb
      have hw_eig : ∀ i ∈ s.erase a, ∀ k', T k' ((f i k - f a k) • v i)
          = f i k' • ((f i k - f a k) • v i) := by
        intro i hi k'
        rw [map_smul, hv i (Finset.mem_of_mem_erase hi) k', smul_comm]
      have h2 : ∑ i ∈ s, (f i k - f a k) • v i = 0 := by
        have h3 : ∑ i ∈ s, (f i k - f a k) • v i
            = T k (∑ i ∈ s, v i) - f a k • ∑ i ∈ s, v i := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          rw [hv i hi k, sub_smul]
        rw [h3, hsum, map_zero, smul_zero, sub_zero]
      have hw_sum : ∑ i ∈ s.erase a, (f i k - f a k) • v i = 0 := by
        have h4 := Finset.sum_erase_add s (fun i => (f i k - f a k) • v i) ha
        simp only [sub_self, zero_smul, add_zero] at h4
        rw [h4]
        exact h2
      have hw0 := ih (s.erase a) (Finset.erase_ssubset ha)
        (fun i => (f i k - f a k) • v i) hw_eig hw_sum
      have hz : ∀ i ∈ s, f i k ≠ f a k → v i = 0 := by
        intro i hi hne
        have hia : i ≠ a := fun h => hne (by rw [h])
        have h5 : (f i k - f a k) • v i = 0 := hw0 i (Finset.mem_erase.mpr ⟨hia, hi⟩)
        rcases smul_eq_zero.mp h5 with h | h
        · exact absurd (sub_eq_zero.mp h) hne
        · exact h
      have hts : s.filter (fun i => f i k = f a k) ⊂ s := by
        rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
        exact ⟨b, hb, fun h => hk (Finset.mem_filter.mp h).2⟩
      have hsum_t : ∑ i ∈ s.filter (fun i => f i k = f a k), v i = 0 := by
        rw [Finset.sum_filter_of_ne]
        · exact hsum
        · intro i hi hvi
          by_contra hne
          exact hvi (hz i hi hne)
      exact ih _ hts v (fun i hi k' => hv i (Finset.filter_subset _ _ hi) k') hsum_t a
        (Finset.mem_filter.mpr ⟨ha, rfl⟩)

theorem GlobalTheory.CompanionTheory.PresRho.eq_zero_of_sum_weightVec :
    ∀ {ι κ A : Type} [DecidableEq ι] [inst : AddCommGroup A] [inst_1 : _root_.Module ℂ A] (T : κ → Module.End ℂ A) (f : ι → κ → ℂ), Function.Injective f → ∀ (s : Finset ι) (v : ι → A), (∀ i ∈ s, ∀ (k : κ), DFunLike.coe (T k) (v i) = f i k • v i) → ∑ i ∈ s, v i = OfNat.ofNat (nat_lit 0) → ∀ i ∈ s, v i = OfNat.ofNat (nat_lit 0) := by
  intro ι κ A _ _ _ T f hf s v hv hsum
  exact eigenvectors_sum_zero_eq_zero T f hf s v hv hsum

end UpperTheory.Reformulated.B.P6.r14a
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.LargePrimeDivisors
namespace UpperTheory.Reformulated.B.P6.LargePrimeDivisors

open scoped Int LT OfNat Polynomial Dvd

open Polynomial in
theorem mul_sub_mul_add_ne_zero (f : Polynomial ℤ) (hf : 0 < f.natDegree) (c : ℤ) :
    f * (f - C c) * (f + C c) ≠ 0 := by
  have h1 : f ≠ 0 := by
    rintro rfl
    simp at hf
  have h2 : f - C c ≠ 0 := by
    intro h
    have h' : f = C c := sub_eq_zero.mp h
    rw [h', natDegree_C] at hf
    exact lt_irrefl _ hf
  have h3 : f + C c ≠ 0 := by
    intro h
    have h' : f = -C c := eq_neg_of_add_eq_zero_left h
    rw [h', natDegree_neg, natDegree_C] at hf
    exact lt_irrefl _ hf
  exact mul_ne_zero (mul_ne_zero h1 h2) h3

theorem exists_nat_eval_mul_ne_zero (P : Polynomial ℤ) (hP : P ≠ 0) (a : ℤ) (ha : a ≠ 0) :
    ∃ t : ℕ, P.eval (a * (t : ℤ)) ≠ 0 := by
  by_contra h
  push_neg at h
  apply hP
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply Set.infinite_of_injective_forall_mem (f := fun t : ℕ => a * (t : ℤ))
  · intro x y hxy
    have h2 : (x : ℤ) = (y : ℤ) := mul_left_cancel₀ ha hxy
    exact_mod_cast h2
  · intro t
    exact h t

theorem exists_prime_gt_dvd_eval_of_natDegree_pos (f : Polynomial ℤ) (hf : 0 < f.natDegree) (N : ℕ) :
    ∃ (p : ℕ) (m : ℤ), Nat.Prime p ∧ N < p ∧ (p : ℤ) ∣ Polynomial.eval m f := by
  by_cases hc : f.eval 0 = 0
  · obtain ⟨p, hNp, hp⟩ := Nat.exists_infinite_primes (N + 1)
    refine ⟨p, p, hp, by omega, ?_⟩
    have h1 := Polynomial.sub_dvd_eval_sub (p : ℤ) 0 f
    rw [hc, sub_zero, sub_zero] at h1
    exact h1
  · have hM0 : ((N.factorial : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
    have hcM : f.eval 0 * (N.factorial : ℤ) ≠ 0 := mul_ne_zero hc hM0
    obtain ⟨t, ht⟩ := exists_nat_eval_mul_ne_zero _ (mul_sub_mul_add_ne_zero f hf (f.eval 0)) _ hcM
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_C] at ht
    obtain ⟨k, hk⟩ := Polynomial.sub_dvd_eval_sub (f.eval 0 * (N.factorial : ℤ) * (t : ℤ)) 0 f
    have hw : f.eval (f.eval 0 * (N.factorial : ℤ) * (t : ℤ)) =
        f.eval 0 * (1 + (N.factorial : ℤ) * ((t : ℤ) * k)) := by
      linear_combination hk
    rw [hw] at ht
    have hv0 : (1 + (N.factorial : ℤ) * ((t : ℤ) * k)) ≠ 0 := by
      intro h0
      apply ht
      rw [h0]
      ring
    have hv1 : (1 + (N.factorial : ℤ) * ((t : ℤ) * k)) ≠ 1 := by
      intro h0
      apply ht
      rw [h0]
      ring
    have hv2 : (1 + (N.factorial : ℤ) * ((t : ℤ) * k)) ≠ -1 := by
      intro h0
      apply ht
      rw [h0]
      ring
    have hna : (1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs ≠ 1 := by
      intro h0
      rcases Int.natAbs_eq_iff.mp h0 with h | h
      · exact hv1 (by exact_mod_cast h)
      · exact hv2 (by rw [h]; norm_num)
    have hp : Nat.Prime ((1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs.minFac) :=
      Nat.minFac_prime hna
    have hpv : ((((1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs.minFac : ℕ)) : ℤ) ∣
        (1 + (N.factorial : ℤ) * ((t : ℤ) * k)) :=
      Int.ofNat_dvd_left.mpr (Nat.minFac_dvd _)
    refine ⟨_, f.eval 0 * (N.factorial : ℤ) * (t : ℤ), hp, ?_, ?_⟩
    · by_contra hle
      push_neg at hle
      have hpN : ((1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs.minFac) ∣ N.factorial :=
        Nat.dvd_factorial hp.pos hle
      have hpN' : ((((1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs.minFac : ℕ)) : ℤ) ∣
          (N.factorial : ℤ) * ((t : ℤ) * k) :=
        Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr hpN) _
      have h1 : ((((1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs.minFac : ℕ)) : ℤ) ∣ 1 :=
        (dvd_add_left hpN').mp hpv
      have h2 : (1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs.minFac ∣ 1 := by
        exact_mod_cast h1
      exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
    · rw [hw]
      exact Dvd.dvd.mul_left hpv _

theorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_large_prime_dvd_eval :
    ∀ (f : Polynomial ℤ), OfNat.ofNat (nat_lit 0) < f.natDegree → ∀ (N : ℕ), ∃ (p : ℕ) (m : ℤ), Nat.Prime p ∧ N < p ∧ p.cast ∣ Polynomial.eval m f := by
  intro f hf N
  exact exists_prime_gt_dvd_eval_of_natDegree_pos f hf N

end UpperTheory.Reformulated.B.P6.LargePrimeDivisors
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.DoubleSumReduceSecond
namespace UpperTheory.Reformulated.B.P6.r26a

open scoped HSub SubNegMonoid AddGroup AddGroupWithOne Ring HMul Distrib OfNat Zero MulZeroClass Finset Semiring Fin Complex AddCommGroup Module Module.End

noncomputable def PositivityTheory.D.DSIC.KRel :
    {n : ℕ} → {A : Type} → [inst_h0 : Ring A] → (Fin n → Bool) → (Fin n → Fin n → A) → Prop :=
  fun {n : ℕ} {A : Type} {inst_f0 : Ring A} (ε_h1 : Fin n → Bool) (F : Fin n → Fin n → A) ↦ ∀ (a b c d : Fin n), ε_h1 a = ε_h1 b → ε_h1 c = ε_h1 d → F a b * F c d - F c d * F a b = (if b = c then F a d else OfNat.ofNat (nat_lit 0)) - if d = a then F c b else OfNat.ofNat (nat_lit 0)

noncomputable def Formalism.REAL.CasK.{u_1} :
    {A : Type u_1} → [inst_h0 : Ring A] → {n : ℕ} → (Fin n → Bool) → (Fin n → Fin n → A) → A :=
  fun {A : Type u_1} {inst_f1 : Ring A} {n : ℕ} (ε_h1 : Fin n → Bool) (E : Fin n → Fin n → A) ↦ ∑ a : Fin n, ∑ b : Fin n, if ε_h1 a = ε_h1 b then E a b * E b a else OfNat.ofNat (nat_lit 0)

theorem commutator_casimir_term {V : Type} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (hK : PositivityTheory.D.DSIC.KRel ε E) {c d : Fin n} (hcd : ε c = ε d)
    (a b : Fin n) :
    E c d * (if ε a = ε b then E a b * E b a else 0) - (if ε a = ε b then E a b * E b a else 0) * E c d
      = ((if ε a = ε b then (if d = a then E c b * E b a else 0) else 0)
          - (if ε a = ε b then (if a = c then E a b * E b d else 0) else 0))
        + ((if ε a = ε b then (if d = b then E a b * E c a else 0) else 0)
          - (if ε a = ε b then (if b = c then E a d * E b a else 0) else 0)) := by
  by_cases h : ε a = ε b
  · simp only [if_pos h]
    have h1 : E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0) :=
      hK a b c d h hcd
    have h2 : E b a * E c d - E c d * E b a = (if a = c then E b d else 0) - (if d = b then E c a else 0) :=
      hK b a c d h.symm hcd
    have key : E c d * (E a b * E b a) - E a b * E b a * E c d
        = -((E a b * E c d - E c d * E a b) * E b a) - E a b * (E b a * E c d - E c d * E b a) := by
      noncomm_ring
    rw [key, h1, h2]
    simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero]
    abel
  · simp only [if_neg h]
    simp

theorem double_sum_reduce_first {V : Type} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n, (if ε a = ε b then (if d = a then E c b * E b a else 0) else 0))
      = ∑ b : Fin n, (if ε d = ε b then E c b * E b d else 0) := by
  rw [Finset.sum_eq_single d]
  · apply Finset.sum_congr rfl
    intro b _
    simp
  · intro a _ had
    apply Finset.sum_eq_zero
    intro b _
    simp [Ne.symm had]
  · intro h
    exact absurd (Finset.mem_univ d) h

theorem double_sum_reduce_fourth {V : Type} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n, (if ε a = ε b then (if a = c then E a b * E b d else 0) else 0))
      = ∑ b : Fin n, (if ε c = ε b then E c b * E b d else 0) := by
  rw [Finset.sum_eq_single c]
  · apply Finset.sum_congr rfl
    intro b _
    simp
  · intro a _ hac
    apply Finset.sum_eq_zero
    intro b _
    simp [hac]
  · intro h
    exact absurd (Finset.mem_univ c) h

theorem double_sum_reduce_third {V : Type} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n, (if ε a = ε b then (if d = b then E a b * E c a else 0) else 0))
      = ∑ a : Fin n, (if ε a = ε d then E a d * E c a else 0) := by
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single d]
  · simp
  · intro b _ hbd
    simp [Ne.symm hbd]
  · intro h
    exact absurd (Finset.mem_univ d) h

theorem double_sum_reduce_second {V : Type} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n, (if ε a = ε b then (if b = c then E a d * E b a else 0) else 0))
      = ∑ a : Fin n, (if ε a = ε c then E a d * E c a else 0) := by
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hbc
    simp [hbc]
  · intro h
    exact absurd (Finset.mem_univ c) h

theorem PositivityTheory.D.LK.casK_comm :
    ∀ {n : ℕ} {ε_h0 : Fin n → Bool} {V : Type} [inst_h2 : AddCommGroup V] [inst_h3 : _root_.Module ℂ V] {E : Fin n → Fin n → Module.End ℂ V}, PositivityTheory.D.DSIC.KRel ε_h0 E → ∀ {c d : Fin n}, ε_h0 c = ε_h0 d → Commute (E c d) (Formalism.REAL.CasK ε_h0 E) := by
  intro n ε V _ _ E hK c d hcd
  show E c d * Formalism.REAL.CasK ε E = Formalism.REAL.CasK ε E * E c d
  rw [← sub_eq_zero]
  have hsum : E c d * Formalism.REAL.CasK ε E - Formalism.REAL.CasK ε E * E c d
      = ∑ a : Fin n, ∑ b : Fin n, (E c d * (if ε a = ε b then E a b * E b a else 0)
          - (if ε a = ε b then E a b * E b a else 0) * E c d) := by
    unfold Formalism.REAL.CasK
    simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]
  rw [hsum]
  simp only [commutator_casimir_term ε E hK hcd, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [double_sum_reduce_first, double_sum_reduce_fourth, double_sum_reduce_third, double_sum_reduce_second, hcd]
  simp

end UpperTheory.Reformulated.B.P6.r26a
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.BlockTriangularLevi
namespace UpperTheory.Reformulated.B.P6.BlockTriangularLevi

open scoped Sigma DFunLike EquivLike Equiv Matrix CommSemiring CommRing Membership Set Preorder PartialOrder SemilatticeInf Lattice DistribLattice MulZeroClass Units Semiring HMul MulOne MulOneClass Monoid DivInvMonoid Group OfNat One Inv InvOneClass DivInvOneMonoid DivisionMonoid Subgroup Submonoid Subsemigroup Subtype SetLike MulZeroOneClass MonoidHom OneHom Pi PUnit Fin Finset HAdd AddMonoidWithOne AddGroupWithOne Ring DivisionRing Field CommGroup Circle DivisionSemiring Semifield Complex SeminormedRing SeminormedCommRing NormedCommRing NormedField AddChar Zero HSub

noncomputable def GlobalTheory.SmGL.blk :
    {α n : Type} → {m : α → Type} → (a : α) × m a ≃ n → n → α :=
  fun {α n : Type} {m : α → Type} (e : (a : α) × m a ≃ n) (i : n) ↦ Sigma.fst (β := fun (a : α) ↦ m a) (DFunLike.coe (β := fun (x_h1 : n) ↦ (a : α) × m a) e.symm i)

theorem blockIndex_sigma_equiv {α n : Type} {m : α → Type} (e : (a : α) × m a ≃ n) (a : α) (i : m a) :
    GlobalTheory.SmGL.blk (m := m) e (e ⟨a, i⟩) = a := by
  show (e.symm (e ⟨a, i⟩)).1 = a
  rw [Equiv.symm_apply_apply]

theorem blockTriangular_mul_submatrix {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [Fintype n] (e : (a : α) × m a ≃ n) (a : α) (X Y : Matrix n n R)
    (hX : X.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e))
    (hY : Y.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)) :
    (X * Y).submatrix (fun i : m a => e ⟨a, i⟩) (fun i : m a => e ⟨a, i⟩)
      = X.submatrix (fun i : m a => e ⟨a, i⟩) (fun i : m a => e ⟨a, i⟩)
        * Y.submatrix (fun i : m a => e ⟨a, i⟩) (fun i : m a => e ⟨a, i⟩) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← e.sum_comp, Fintype.sum_sigma, Finset.sum_eq_single a]
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro l _
    rcases lt_or_gt_of_ne hb with h | h
    · have h' : GlobalTheory.SmGL.blk (m := m) e (e ⟨b, l⟩) < GlobalTheory.SmGL.blk (m := m) e (e ⟨a, i⟩) := by
        rw [blockIndex_sigma_equiv, blockIndex_sigma_equiv]; exact h
      rw [hX h', zero_mul]
    · have h' : GlobalTheory.SmGL.blk (m := m) e (e ⟨a, j⟩) < GlobalTheory.SmGL.blk (m := m) e (e ⟨b, l⟩) := by
        rw [blockIndex_sigma_equiv, blockIndex_sigma_equiv]; exact h
      rw [hY h', mul_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem GlobalTheory.SmGL.parab_obl_1 :
    ∀ (R : Type) [inst_h0 : CommRing R] {α n : Type} {m : α → Type} [inst_h2 : LinearOrder α] [inst_h3 : Fintype n] [inst_h4 : DecidableEq n] (e : (a : α) × m a ≃ n) {x y : GL n R}, Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} x → Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} y → Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} (x * y) := by
  intro R _ α n m _ _ _ e x y hx hy
  show ((x * y : GL n R) : Matrix n n R).BlockTriangular _
  rw [Units.val_mul]
  exact Matrix.BlockTriangular.mul hx hy

theorem GlobalTheory.SmGL.parab_obl_2 :
    ∀ (R : Type) [inst_h0 : CommRing R] {α n : Type} {m : α → Type} [inst_h2 : LinearOrder α] [inst_h3 : Fintype n] [inst_h4 : DecidableEq n] (e : (a : α) × m a ≃ n), Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} (OfNat.ofNat (nat_lit 1)) := by
  intro R _ α n m _ _ _ e
  show ((1 : GL n R) : Matrix n n R).BlockTriangular _
  rw [Units.val_one]
  exact Matrix.blockTriangular_one

theorem GlobalTheory.SmGL.parab_obl_3 :
    ∀ (R : Type) [inst_h0 : CommRing R] {α n : Type} {m : α → Type} [inst_h2 : LinearOrder α] [inst_h3 : Fintype n] [inst_h4 : DecidableEq n] (e : (a : α) × m a ≃ n) {x : GL n R}, Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} x → Membership.mem (γ := Set (GL n R)) {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)} x⁻¹ := by
  intro R _ α n m _ _ _ e x hx
  show ((x⁻¹ : GL n R) : Matrix n n R).BlockTriangular _
  rw [Matrix.coe_units_inv]
  haveI : Invertible (x : Matrix n n R) := x.invertible
  exact Matrix.blockTriangular_inv_of_blockTriangular hx

noncomputable def GlobalTheory.SmGL.parab :
    (R : Type) → [inst_h0 : CommRing R] → {α n : Type} → {m : α → Type} → [inst_h2 : LinearOrder α] → [inst_h3 : Fintype n] → [inst_h4 : DecidableEq n] → (a : α) × m a ≃ n → Subgroup (GL n R) :=
  fun (R : Type) {inst_h0 : CommRing R} {α n : Type} {m : α → Type} {inst_h2 : LinearOrder α} {inst_h3 : Fintype n} {inst_h4 : DecidableEq n} (e : (a : α) × m a ≃ n) ↦ { carrier := {g : GL n R | g.val.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)}, mul_mem' := @GlobalTheory.SmGL.parab_obl_1 R inst_h0 α n m inst_h2 inst_h3 inst_h4 e, one_mem' := GlobalTheory.SmGL.parab_obl_2 R (m := m) e, inv_mem' := @GlobalTheory.SmGL.parab_obl_3 R inst_h0 α n m inst_h2 inst_h3 inst_h4 e }

@[reducible] noncomputable def GlobalTheory.SmGL.Levi :
    (R : Type) → [inst_h0 : CommRing R] → {α : Type} → (m : α → Type) → [inst_h2 : (a : α) → Fintype (m a)] → [inst_h3 : (a : α) → DecidableEq (m a)] → Type :=
  fun (R : Type) {inst_f0 : CommRing R} {α : Type} (m : α → Type) {inst_f1 : (a : α) → Fintype (m a)} {inst_f2 : (a : α) → DecidableEq (m a)} ↦ (a : α) → GL (m a) R

theorem GlobalTheory.SmGL.diagBlock_obl_1 :
    ∀ (R : Type) [inst_h0 : CommRing R] {α n : Type} {m : α → Type} [inst_h2 : LinearOrder α] [inst_h3 : (a : α) → Fintype (m a)] [inst_h4 : (a : α) → DecidableEq (m a)] [inst_h5 : Fintype n] [inst_h6 : DecidableEq n] (e : (a : α) × m a ≃ n) (a : α), Eq (α := Matrix (m a) (m a) R) (Matrix.submatrix (m := n) (n := n) (Units.val (Subtype.val (p := fun (x : GL n R) ↦ Membership.mem (γ := Subgroup (GL n R)) (GlobalTheory.SmGL.parab R (m := m) e) x) (OfNat.ofNat (nat_lit 1)))) (fun (i : m a) ↦ DFunLike.coe (β := fun (x_h7 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) fun (i : m a) ↦ DFunLike.coe (β := fun (x_h8 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) (OfNat.ofNat (nat_lit 1)) := by
  intro R _ α n m _ _ _ _ _ e a
  show ((1 : GL n R) : Matrix n n R).submatrix _ _ = 1
  rw [Units.val_one]
  exact Matrix.submatrix_one _ (e.injective.comp sigma_mk_injective)

theorem GlobalTheory.SmGL.diagBlock_obl_2 :
    ∀ (R : Type) [inst_h0 : CommRing R] {α n : Type} {m : α → Type} [inst_h2 : Fintype α] [inst_h3 : LinearOrder α] [inst_h4 : (a : α) → Fintype (m a)] [inst_h5 : (a : α) → DecidableEq (m a)] [inst_h6 : Fintype n] [inst_h7 : DecidableEq n] (e : (a : α) × m a ≃ n) (a : α) (x y : ↥(GlobalTheory.SmGL.parab R (m := m) e)), ((x * y).val (p := fun (x : GL n R) ↦ Membership.mem (γ := Subgroup (GL n R)) (GlobalTheory.SmGL.parab R (m := m) e) x).val.submatrix (fun (i : m a) ↦ DFunLike.coe (β := fun (x_h8 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) fun (i : m a) ↦ DFunLike.coe (β := fun (x_h9 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) = HMul.hMul (α := Matrix (m a) (m a) R) (x.val (p := fun (x : GL n R) ↦ Membership.mem (γ := Subgroup (GL n R)) (GlobalTheory.SmGL.parab R (m := m) e) x).val.submatrix (fun (i : m a) ↦ DFunLike.coe (β := fun (x_h10 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) fun (i : m a) ↦ DFunLike.coe (β := fun (x_h11 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) (y.val (p := fun (x : GL n R) ↦ Membership.mem (γ := Subgroup (GL n R)) (GlobalTheory.SmGL.parab R (m := m) e) x).val.submatrix (fun (i : m a) ↦ DFunLike.coe (β := fun (x_h12 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) fun (i : m a) ↦ DFunLike.coe (β := fun (x_h13 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) := by
  intro R _ α n m _ _ _ _ _ _ e a x y
  have hx : ((x : GL n R) : Matrix n n R).BlockTriangular (GlobalTheory.SmGL.blk (m := m) e) := x.2
  have hy : ((y : GL n R) : Matrix n n R).BlockTriangular (GlobalTheory.SmGL.blk (m := m) e) := y.2
  have key := blockTriangular_mul_submatrix e a _ _ hx hy
  exact key

noncomputable def GlobalTheory.SmGL.diagBlock :
    (R : Type) → [inst_h0 : CommRing R] → {α n : Type} → {m : α → Type} → [inst_h2 : Fintype α] → [inst_h3 : LinearOrder α] → [inst_h4 : (a : α) → Fintype (m a)] → [inst_h5 : (a : α) → DecidableEq (m a)] → [inst_h6 : Fintype n] → [inst_h7 : DecidableEq n] → (e : (a : α) × m a ≃ n) → (a : α) → ↥(GlobalTheory.SmGL.parab R (m := m) e) →* Matrix (m a) (m a) R :=
  fun (R : Type) {inst_f3 : CommRing R} {α n : Type} {m : α → Type} {inst_f4 : Fintype α} {inst_f5 : LinearOrder α} {inst_f6 : (a : α) → Fintype (m a)} {inst_f7 : (a : α) → DecidableEq (m a)} {inst_f8 : Fintype n} {inst_f9 : DecidableEq n} (e : (a : α) × m a ≃ n) (a : α) ↦ { toFun := fun (p : ↥(GlobalTheory.SmGL.parab R (m := m) e)) ↦ p.val (p := fun (x : GL n R) ↦ Membership.mem (γ := Subgroup (GL n R)) (GlobalTheory.SmGL.parab R (m := m) e) x).val.submatrix (fun (i : m a) ↦ DFunLike.coe (β := fun (x_h8 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i)) fun (i : m a) ↦ DFunLike.coe (β := fun (x_h9 : (a : α) × m a) ↦ n) e (Sigma.mk (β := fun (a : α) ↦ m a) a i), map_one' := GlobalTheory.SmGL.diagBlock_obl_1 R (m := m) e a, map_mul' := GlobalTheory.SmGL.diagBlock_obl_2 R (m := m) e a }

noncomputable def GlobalTheory.SmGL.leviProj :
    (R : Type) → [inst_h0 : CommRing R] → {α n : Type} → {m : α → Type} → [inst_h2 : Fintype α] → [inst_h3 : LinearOrder α] → [inst_h4 : (a : α) → Fintype (m a)] → [inst_h5 : (a : α) → DecidableEq (m a)] → [inst_h6 : Fintype n] → [inst_h7 : DecidableEq n] → (e : (a : α) × m a ≃ n) → ↥(GlobalTheory.SmGL.parab R (m := m) e) →* GlobalTheory.SmGL.Levi R m :=
  fun (R : Type) {inst_f10 : CommRing R} {α n : Type} {m : α → Type} {inst_f11 : Fintype α} {inst_f12 : LinearOrder α} {inst_f13 : (a : α) → Fintype (m a)} {inst_f14 : (a : α) → DecidableEq (m a)} {inst_f15 : Fintype n} {inst_f16 : DecidableEq n} (e : (a : α) × m a ≃ n) ↦ MonoidHom.pi (f := fun (a : α) ↦ GL (m a) R) fun (a : α) ↦ MonoidHom.toHomUnits (GlobalTheory.SmGL.diagBlock R (m := m) e a)

noncomputable def GlobalTheory.SmGL.unipRad :
    (R : Type) → [inst_h0 : CommRing R] → {α n : Type} → {m : α → Type} → [inst_h2 : Fintype α] → [inst_h3 : LinearOrder α] → [inst_h4 : (a : α) → Fintype (m a)] → [inst_h5 : (a : α) → DecidableEq (m a)] → [inst_h6 : Fintype n] → [inst_h7 : DecidableEq n] → (a : α) × m a ≃ n → Subgroup (GL n R) :=
  fun (R : Type) {inst_f17 : CommRing R} {α n : Type} {m : α → Type} {inst_f18 : Fintype α} {inst_f19 : LinearOrder α} {inst_f20 : (a : α) → Fintype (m a)} {inst_f21 : (a : α) → DecidableEq (m a)} {inst_f22 : Fintype n} {inst_f23 : DecidableEq n} (e : (a : α) × m a ≃ n) ↦ Subgroup.map (G := ↥(GlobalTheory.SmGL.parab R (m := m) e)) (Subgroup.subtype (GlobalTheory.SmGL.parab R (m := m) e)) (MonoidHom.ker (GlobalTheory.SmGL.leviProj R (m := m) e))

noncomputable def GlobalTheory.SmGL.points :
    (n : Type) → (_ : n) × Unit ≃ n :=
  fun (n : Type) ↦ Equiv.sigmaUnique n fun (x_h0 : n) ↦ Unit

noncomputable def GlobalTheory.SmGL.unipB :
    (R : Type) → [inst_h0 : CommRing R] → (n : Type) → [inst_h1 : Fintype n] → [inst_h2 : DecidableEq n] → [inst_h3 : LinearOrder n] → Subgroup (GL n R) :=
  fun (R : Type) {inst_f24 : CommRing R} (n : Type) {inst_f25 : Fintype n} {inst_f26 : DecidableEq n} {inst_f27 : LinearOrder n} ↦ GlobalTheory.SmGL.unipRad R (m := fun (a : n) ↦ Unit) (GlobalTheory.SmGL.points n)

noncomputable def GlobalTheory.Whittaker.superDiag :
    {R : Type} → [inst_h0 : CommRing R] → {n : ℕ} → GL (Fin n) R → R :=
  fun {R : Type} {inst_f28 : CommRing R} {n : ℕ} (g : GL (Fin n) R) ↦ ∑ i : Fin n, ∑ j : Fin n with j.val = i.val + OfNat.ofNat (nat_lit 1), g.val i j

noncomputable def DiscreteGroups.sglob.LConv.IsWhitTest :
    {k : Type} → [inst_h0 : Field k] → [inst_h1 : TopologicalSpace k] → {m : ℕ} → AddChar k Circle → (GL (Fin m) k → ℂ) → Prop :=
  fun {k : Type} {inst_f29 : Field k} {inst_f30 : TopologicalSpace k} {m : ℕ} (ψ : AddChar k Circle) (f : GL (Fin m) k → ℂ) ↦ (∀ (u : GL (Fin m) k), Membership.mem (γ := Subgroup (GL (Fin m) k)) (GlobalTheory.SmGL.unipB k (Fin m)) u → ∀ (g : GL (Fin m) k), f (u * g) = Subtype.val (p := fun (x : ℂ) ↦ Membership.mem (γ := Submonoid ℂ) (Submonoid.unitSphere ℂ) x) (DFunLike.coe (β := fun (x_h4 : k) ↦ Circle) ψ (GlobalTheory.Whittaker.superDiag u)) * f g) ∧ IsLocallyConstant f ∧ ∃ (C : Set (GL (Fin m) k)), IsCompact C ∧ ∀ (g : GL (Fin m) k), f g ≠ OfNat.ofNat (nat_lit 0) → ∃ (u : GL (Fin m) k), Membership.mem (γ := Subgroup (GL (Fin m) k)) (GlobalTheory.SmGL.unipB k (Fin m)) u ∧ ∃ c ∈ C, g = u * c

theorem DiscreteGroups.sglob.LConv.IsWhitTest.sub :
    ∀ {k : Type} [inst_h0 : Field k] [inst_h1 : TopologicalSpace k] {m : ℕ} {ψ : AddChar k Circle} {f f' : GL (Fin m) k → ℂ}, DiscreteGroups.sglob.LConv.IsWhitTest ψ f → DiscreteGroups.sglob.LConv.IsWhitTest ψ f' → DiscreteGroups.sglob.LConv.IsWhitTest (m := m) ψ fun (g : GL (Fin m) k) ↦ f g - f' g := by
  intro k _ _ m ψ f f' hf hf'
  unfold DiscreteGroups.sglob.LConv.IsWhitTest at hf hf' ⊢
  obtain ⟨h1, h2, C, hC, h3⟩ := hf
  obtain ⟨h1', h2', C', hC', h3'⟩ := hf'
  refine ⟨?_, h2.sub h2', C ∪ C', hC.union hC', ?_⟩
  · intro u hu g
    beta_reduce
    rw [h1 u hu g, h1' u hu g, mul_sub]
  · intro g hg
    beta_reduce at hg
    by_cases hfg : f g = 0
    · have hfg' : f' g ≠ 0 := by
        intro h
        apply hg
        rw [hfg, h, sub_zero]
      obtain ⟨u, hu, c, hc, rfl⟩ := h3' g hfg'
      exact ⟨u, hu, c, Set.mem_union_right _ hc, rfl⟩
    · obtain ⟨u, hu, c, hc, rfl⟩ := h3 g hfg
      exact ⟨u, hu, c, Set.mem_union_left _ hc, rfl⟩

end UpperTheory.Reformulated.B.P6.BlockTriangularLevi
end
