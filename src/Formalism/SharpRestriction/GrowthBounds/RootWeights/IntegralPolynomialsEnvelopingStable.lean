module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.ExistsHighestWeightVectorFindim
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.MultidegreePartFinitelyGenerated

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.IntegralGeneratorsPreserveLattice
section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.PolarizationDividedPowerMonomial
section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.DividedPowersPreserveZero
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section good

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

def DividedPowersPreserve (Q : V → Prop) (D : Module.End K V) : Prop :=
  ∀ (k : ℕ) (x : V), Q x → Q (((k.factorial : K)⁻¹) • (D ^ k) x)

theorem predicate_finset_sum_mem (Q : V → Prop) (h0 : Q 0) (hadd : ∀ x y, Q x → Q y → Q (x + y)) {α : Type*}
    (s : Finset α) (f : α → V) (h : ∀ i ∈ s, Q (f i)) : Q (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hadd _ _ (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem divided_powers_preserve_add (Q : V → Prop) (h0 : Q 0) (hadd : ∀ x y, Q x → Q y → Q (x + y))
    (D D' : Module.End K V) (hc : Commute D D') (hD : DividedPowersPreserve Q D) (hD' : DividedPowersPreserve Q D') :
    DividedPowersPreserve Q (D + D') := by
  intro k x hx
  rw [hc.add_pow, LinearMap.sum_apply, Finset.smul_sum]
  refine predicate_finset_sum_mem Q h0 hadd _ _ fun m hm => ?_
  have hmk : m ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  have h1 := hD m _ (hD' (k - m) x hx)
  have h2 : ((k.factorial : K)⁻¹) • (D ^ m * D' ^ (k - m) * ((k.choose m : ℕ) : Module.End K V)) x =
      ((m.factorial : K)⁻¹) • (D ^ m) ((((k - m).factorial : K)⁻¹) • (D' ^ (k - m)) x) := by
    have h3 : ((k.choose m : ℕ) : Module.End K V) x = ((k.choose m : ℕ) : K) • x := by
      rw [Module.End.natCast_apply, Nat.cast_smul_eq_nsmul]
    simp only [Module.End.mul_apply, h3, map_smul, smul_smul]
    congr 1
    have h4 : ((k.choose m : ℕ) : K) = (k.factorial : K) / ((m.factorial : K) * ((k - m).factorial : K)) :=
      Nat.cast_choose K hmk
    have hk : (k.factorial : K) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have hm' : (m.factorial : K) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    have hkm : ((k - m).factorial : K) ≠ 0 := by exact_mod_cast (k - m).factorial_ne_zero
    rw [h4]
    field_simp
  rw [h2]
  exact h1

end good

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section ops

variable {K : Type} [Field K] {σ : Type}

def polarizationOperator (K : Type) [Field K] {σ : Type} (v w : σ) : Module.End K (MvPolynomial σ K) :=
  (LinearMap.mulLeft K (X v)) ∘ₗ (pderiv w).toLinearMap

theorem polarization_monomial (v w : σ) (m : σ →₀ ℕ) (c : K) :
    polarizationOperator K v w (monomial m c) = monomial (m - Finsupp.single w 1 + Finsupp.single v 1) (c * (m w : K)) := by
  show X v * pderiv w (monomial m c) = _
  rw [pderiv_monomial, X, monomial_mul, one_mul, add_comm (Finsupp.single v 1)]

theorem polarization_commute (v w v' w' : σ) (h1 : w ≠ v') (h2 : w ≠ w') (h3 : w' ≠ v) :
    Commute (polarizationOperator K v w) (polarizationOperator K v' w') := by
  show polarizationOperator K v w * polarizationOperator K v' w' = polarizationOperator K v' w' * polarizationOperator K v w
  refine LinearMap.ext fun f => ?_
  induction f using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [Module.End.mul_apply, Module.End.mul_apply, polarization_monomial, polarization_monomial,
      polarization_monomial, polarization_monomial]
    have e1 : (m - Finsupp.single w' 1 + Finsupp.single v' 1 : σ →₀ ℕ) w = m w := by
      simp [Finsupp.single_apply, h1, h2, Ne.symm h1, Ne.symm h2]
    have e2 : (m - Finsupp.single w 1 + Finsupp.single v 1 : σ →₀ ℕ) w' = m w' := by
      simp [Finsupp.single_apply, h3, Ne.symm h2, Ne.symm h3, h2]
    have hexp : (m - Finsupp.single w' 1 + Finsupp.single v' 1 - Finsupp.single w 1
        + Finsupp.single v 1 : σ →₀ ℕ) =
        m - Finsupp.single w 1 + Finsupp.single v 1 - Finsupp.single w' 1 + Finsupp.single v' 1 := by
      ext x
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      by_cases a1 : w = x <;> by_cases a2 : w' = x <;> by_cases a3 : v = x <;>
        by_cases a4 : v' = x <;> (try subst_vars) <;> (try simp_all) <;> omega
    rw [e1, e2, hexp]
    congr 1
    ring
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), hp, hq]

end ops

section fact

variable {σ : Type}

theorem exponent_factorial_ne_zero_of (m : σ →₀ ℕ) : expFact m ≠ 0 := by
  unfold expFact Finsupp.prod
  exact Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _

end fact

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

structure MonomialGradedLattice (p : ℕ) {K : Type} [Field K] {σ : Type} (Q : MvPolynomial σ K → Prop) : Prop where
  zero : Q 0
  add : ∀ F G, Q F → Q G → Q (F + G)
  lin : ∀ u : MvPolynomial σ K →ₗ[K] MvPolynomial σ K,
    (∀ m c, Q (monomial m c) → Q (u (monomial m c))) → ∀ F, Q F → Q (u F)
  step : ∀ (m m' : σ →₀ ℕ) (c : K) (z : ℤ), Q (monomial m c) →
    (z = 0 ∨ padicValNat p (expFact m) ≤ 2 * padicValInt p z + padicValNat p (expFact m')) →
    Q (monomial m' (c * (z : K)))

section

variable {K : Type} [Field K] [CharZero K] {σ : Type}

theorem divided_powers_preserve_polarization (p : ℕ) [Fact p.Prime] (Q : MvPolynomial σ K → Prop) (hQ : MonomialGradedLattice p Q) (ε : ℤ)
    (hε : ε.natAbs = 1) (v w : σ) (hvw : v ≠ w) : DividedPowersPreserve Q ((ε : K) • polarizationOperator K v w) := by
  classical
  intro k x hx
  show Q (((k.factorial : K)⁻¹ • ((ε : K) • polarizationOperator K v w) ^ k) x)
  refine hQ.lin ((k.factorial : K)⁻¹ • ((ε : K) • polarizationOperator K v w) ^ k) ?_ x hx
  intro m c hmc

  set mj : ℕ → (σ →₀ ℕ) := fun j => (m.update w (m w - j)).update v (m v + j) with hmj
  have hmjw : ∀ j, mj j w = m w - j := fun j => by
    simp [hmj, Finsupp.update_apply, Ne.symm hvw]
  have hmjv : ∀ j, mj j v = m v + j := fun j => by
    simp [hmj, Finsupp.update_apply]
  have hmjo : ∀ j i, i ≠ v → i ≠ w → mj j i = m i := fun j i hiv hiw => by
    simp [hmj, Finsupp.update_apply, hiv, hiw]
  have hT : ∀ j, (polarizationOperator K v w ^ j) (monomial m c) =
      monomial (mj j) (c * ((m w).descFactorial j : K)) := by
    intro j
    induction j with
    | zero =>
      have h0 : mj 0 = m := by
        ext i
        by_cases hiv : i = v
        · rw [hiv, hmjv]
          rfl
        · by_cases hiw : i = w
          · rw [hiw, hmjw]
            rfl
          · exact hmjo 0 i hiv hiw
      rw [h0]
      simp
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      show X v * pderiv w (monomial (mj j) (c * ((m w).descFactorial j : K))) = _
      rw [MvPolynomial.pderiv_monomial, hmjw,
        show (X v : MvPolynomial σ K) = monomial (Finsupp.single v 1) 1 from rfl,
        MvPolynomial.monomial_mul, one_mul]
      by_cases hj : j < m w
      · have hexp : Finsupp.single v 1 + (mj j - Finsupp.single w 1) = mj (j + 1) := by
          ext i
          by_cases hiv : i = v
          · rw [hiv]
            simp [hmjv, Finsupp.single_apply, hvw, Ne.symm hvw] <;> omega
          · by_cases hiw : i = w
            · rw [hiw]
              simp [hmjw, Finsupp.single_apply, hvw, Ne.symm hvw] <;> omega
            · simp [hmjo j i hiv hiw, hmjo (j + 1) i hiv hiw, Finsupp.single_apply, Ne.symm hiv,
                Ne.symm hiw]
        rw [hexp, Nat.descFactorial_succ, Nat.cast_mul]
        congr 1
        ring
      · have h1 : (m w).descFactorial (j + 1) = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
        have h2 : m w - j = 0 := by omega
        rw [h1, h2]
        simp
  have hk : (k.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hval : ((k.factorial : K)⁻¹ • ((ε : K) • polarizationOperator K v w) ^ k) (monomial m c) =
      monomial (mj k) (c * (((ε ^ k * ((m w).choose k : ℤ) : ℤ)) : K)) := by
    rw [smul_pow, LinearMap.smul_apply, LinearMap.smul_apply, hT k, MvPolynomial.smul_monomial,
      MvPolynomial.smul_monomial, Nat.descFactorial_eq_factorial_mul_choose]
    congr 1
    simp only [smul_eq_mul]
    push_cast
    rw [inv_mul_eq_iff_eq_mul₀ hk]
    ring
  rw [hval]
  refine hQ.step m (mj k) c _ hmc ?_
  by_cases hkw : k ≤ m w
  · right
    have hz : padicValInt p (ε ^ k * ((m w).choose k : ℤ)) = padicValNat p ((m w).choose k) := by
      simp [padicValInt, Int.natAbs_mul, Int.natAbs_pow, hε, ← Nat.padicValNat_def]
    rw [hz]
    set s : Finset σ := m.support ∪ {v, w} with hs
    have hvs : v ∈ s := by simp [hs]
    have hws : w ∈ s.erase v := by simp [hs, Ne.symm hvw]
    have hsub1 : m.support ⊆ s := Finset.subset_union_left
    have hsub2 : (mj k).support ⊆ s := by
      intro i hi
      rw [Finsupp.mem_support_iff] at hi
      by_cases hiv : i = v
      · rw [hiv]
        simp [hs]
      · by_cases hiw : i = w
        · rw [hiw]
          simp [hs]
        · rw [hmjo k i hiv hiw] at hi
          exact Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hi)
    have hE : expFact m = (m v).factorial * ((m w).factorial *
        ∏ i ∈ (s.erase v).erase w, (m i).factorial) := by
      unfold expFact
      rw [Finsupp.prod_of_support_subset m hsub1 (fun _ k => k.factorial) (fun _ _ => rfl),
        ← Finset.mul_prod_erase s _ hvs, ← Finset.mul_prod_erase (s.erase v) _ hws]
    have hE' : expFact (mj k) = (m v + k).factorial * ((m w - k).factorial *
        ∏ i ∈ (s.erase v).erase w, (m i).factorial) := by
      unfold expFact
      rw [Finsupp.prod_of_support_subset (mj k) hsub2 (fun _ k => k.factorial) (fun _ _ => rfl),
        ← Finset.mul_prod_erase s _ hvs, ← Finset.mul_prod_erase (s.erase v) _ hws, hmjv, hmjw]
      congr 2
      refine Finset.prod_congr rfl fun i hi => ?_
      have hiw : i ≠ w := Finset.ne_of_mem_erase hi
      have hiv : i ≠ v := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
      rw [hmjo k i hiv hiw]
    have hid : expFact m * (m v + k).choose k = expFact (mj k) * (m w).choose k := by
      have e1 := Nat.choose_mul_factorial_mul_factorial (show k ≤ m v + k by omega)
      rw [Nat.add_sub_cancel] at e1
      have e2 := Nat.choose_mul_factorial_mul_factorial hkw
      rw [hE, hE', ← e1, ← e2]
      ring
    have hEpos : expFact m ≠ 0 := by
      rw [hE]
      positivity
    have hE'pos : expFact (mj k) ≠ 0 := by
      rw [hE']
      positivity
    have hC1 : (m v + k).choose k ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hC2 : (m w).choose k ≠ 0 := (Nat.choose_pos hkw).ne'
    have hv := congrArg (padicValNat p) hid
    rw [(show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hEpos hC1, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hE'pos hC2] at hv
    omega
  · left
    have : (m w).choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [this]

theorem list_prod_eigen_shift {V : Type*} [AddCommGroup V] [Module K V] (E : Module.End K V) (x : V) (w : K)
    (hx : E x = w • x) (k : ℕ) :
    ((List.range k).map fun j : ℕ => E - (j : K) • (1 : Module.End K V)).prod x =
      (∏ j ∈ Finset.range k, (w - (j : K))) • x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.prod_append, Finset.prod_range_succ]
    simp [hx, ih]
    first
      | done
      | module
      | (rw [mul_comm, mul_smul]; module)

theorem prod_range_sub_eq_factorial_choose (w : ℤ) (k : ℕ) :
    (∏ j ∈ Finset.range k, ((w : K) - (j : K))) = (k.factorial : K) * ((Ring.choose w k : ℤ) : K) := by
  have h1 : (∏ j ∈ Finset.range k, (w - (j : ℤ))) = (k.factorial : ℤ) * Ring.choose w k := by
    rw [← descPochhammer_eval_eq_prod_range, Polynomial.eval_eq_smeval,
      Ring.descPochhammer_eq_factorial_smul_choose]
    first
      | rw [nsmul_eq_mul]
      | rw [smul_eq_mul]
      | simp
  have h2 := congrArg (Int.cast (R := K)) h1
  push_cast at h2
  exact h2

end

section

variable {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ}


open Classical in
def letterPolarization (K : Type) [Field K] {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (a b : Fin n) (l : ι) :
    Module.End K (MvPolynomial (ι × Fin n) K) :=
  if l ∈ S then (if LL.vec l then polarizationOperator K (l, a) (l, b) else -(polarizationOperator K (l, b) (l, a))) else 0

theorem gl_operator_eq_sum_letters (LL : Letters ι) (S : Set ι) (a b : Fin n) :
    glOps K n LL S a b = ∑ l : ι, letterPolarization K LL S a b l := rfl

theorem letter_polarization_commute (LL : Letters ι) (S : Set ι) (a b : Fin n) (l l' : ι) (h : l ≠ l') :
    Commute (letterPolarization K LL S a b l) (letterPolarization K LL S a b l') := by
  have hne : ∀ x y : Fin n, ((l, x) : ι × Fin n) ≠ (l', y) := fun x y hxy => h (congrArg Prod.fst hxy)
  have hc : ∀ x y x' y' : Fin n, Commute (polarizationOperator K (l, x) (l, y)) (polarizationOperator K (l', x') (l', y')) :=
    fun x y x' y' => polarization_commute _ _ _ _ (hne _ _) (hne _ _) (hne _ _).symm
  unfold letterPolarization
  by_cases h1 : l ∈ S
  · by_cases h2 : l' ∈ S
    · rw [if_pos h1, if_pos h2]
      by_cases v1 : LL.vec l = true <;> by_cases v2 : LL.vec l' = true
      · rw [if_pos v1, if_pos v2]
        exact hc _ _ _ _
      · rw [if_pos v1, if_neg v2]
        exact (hc _ _ _ _).neg_right
      · rw [if_neg v1, if_pos v2]
        exact (hc _ _ _ _).neg_left
      · rw [if_neg v1, if_neg v2]
        exact (hc _ _ _ _).neg_left.neg_right
    · rw [if_neg h2]
      exact Commute.zero_right _
  · rw [if_neg h1]
    exact Commute.zero_left _

theorem divided_powers_preserve_letter (p : ℕ) [Fact p.Prime] (Q : MvPolynomial (ι × Fin n) K → Prop) (hQ : MonomialGradedLattice p Q)
    (LL : Letters ι) (S : Set ι) (a b : Fin n) (hab : a ≠ b) (l : ι) : DividedPowersPreserve Q (letterPolarization K LL S a b l) := by
  unfold letterPolarization
  split_ifs with h1 h2
  · have := divided_powers_preserve_polarization p Q hQ 1 rfl (l, a) (l, b) (by simp [hab])
    simpa using this
  · have := divided_powers_preserve_polarization p Q hQ (-1) rfl (l, b) (l, a) (by simp [Ne.symm hab])
    simpa using this
  · unfold DividedPowersPreserve
    intro k x hx
    rcases k with _ | k
    · simpa using hx
    · simpa using hQ.zero

theorem divided_powers_preserve_gl_operator (p : ℕ) [Fact p.Prime] (Q : MvPolynomial (ι × Fin n) K → Prop) (hQ : MonomialGradedLattice p Q)
    (LL : Letters ι) (S : Set ι) (a b : Fin n) (hab : a ≠ b) : DividedPowersPreserve Q (glOps K n LL S a b) := by
  classical
  rw [gl_operator_eq_sum_letters]
  have key : ∀ s : Finset ι, DividedPowersPreserve Q (∑ l ∈ s, letterPolarization K LL S a b l) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · rw [Finset.sum_empty]
      unfold DividedPowersPreserve
      intro k x hx
      rcases k with _ | k
      · simpa using hx
      · simpa using hQ.zero
    · intro l s hl ih
      rw [Finset.sum_insert hl]
      refine divided_powers_preserve_add Q hQ.zero hQ.add _ _ ?_ (divided_powers_preserve_letter p Q hQ LL S a b hab l) ih
      exact Commute.sum_right _ _ _ fun l' hl' => letter_polarization_commute LL S a b l l' (by rintro rfl; exact hl hl')
  exact key Finset.univ

theorem integral_generators_preserve_lattice (p : ℕ) [Fact p.Prime] (Q : MvPolynomial (ι × Fin n) K → Prop) (hQ : MonomialGradedLattice p Q)
    (LL : Letters ι) (S : Set ι) (u : Module.End K (MvPolynomial (ι × Fin n) K))
    (hu : u ∈ UZgens (glOps K n LL S)) (F : MvPolynomial (ι × Fin n) K) (hF : Q F) : Q (u F) := by
  classical
  rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
  · exact divided_powers_preserve_gl_operator p Q hQ LL S a b hab k F hF
  · refine hQ.lin (binomE (glOps K n LL S) a k) ?_ F hF
    intro m c hmc
    set w : ℤ := ∑ l : ι, (if l ∈ S then (if LL.vec l then ((m (l, a) : ℕ) : ℤ) else -((m (l, a) : ℕ) : ℤ))
      else 0) with hw
    have heig : glOps K n LL S a a (monomial m c) = (w : K) • monomial m c := by
      rw [gl_operator_eq_sum_letters, LinearMap.sum_apply, hw]
      push_cast
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun l _ => ?_
      unfold letterPolarization polarizationOperator
      split_ifs
      · simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply,
          LinearMap.coe_toAddHom]
        change X (l, a) * (pderiv (l, a)) ((monomial m) c) = _
        rw [MvPolynomial.X_mul_pderiv_monomial, Nat.cast_smul_eq_nsmul]
      · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply]
        change -(X (l, a) * (pderiv (l, a)) ((monomial m) c)) = _
        rw [MvPolynomial.X_mul_pderiv_monomial, neg_smul, Nat.cast_smul_eq_nsmul]
      · simp
    have hprod := list_prod_eigen_shift (glOps K n LL S a a) (monomial m c) (w : K) heig k
    rw [prod_range_sub_eq_factorial_choose w k] at hprod
    have hk : (k.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have key : binomE (glOps K n LL S) a k (monomial m c) = monomial m (c * ((Ring.choose w k : ℤ) : K)) := by
      unfold binomE
      rw [LinearMap.smul_apply, hprod, smul_smul, ← mul_assoc, inv_mul_cancel₀ hk, one_mul,
        MvPolynomial.smul_monomial]
      congr 1
      ring
    rw [key]
    exact hQ.step m m c (Ring.choose w k) hmc (Or.inr (by omega))

end

theorem char_zero_stability_of_closure {p : ℕ} (hp : p.Prime) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hchar : CharZero (KK O)) (h : FockLatticeClosure p O) : IntegralFormGeneratorsPreserveLattices p O := by
  classical
  haveI := hchar
  haveI : Fact p.Prime := ⟨hp⟩
  intro n ι _ LL S u hu
  obtain ⟨h0, hadd, _, _, _, hlin, hstep, hint, hmono, hiff⟩ := h (ι × Fin n)
  refine ⟨fun F hF => ?_, fun F hF => ?_⟩
  ·
    have hQ : MonomialGradedLattice p (fun F : MvPolynomial (ι × Fin n) (KK O) => F ∈ IntPol O (ι × Fin n)) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hiff]
        intro m
        exact ⟨0, by simp⟩
      · intro F G hF hG
        rw [hiff] at hF hG ⊢
        intro m
        obtain ⟨a, ha⟩ := hF m
        obtain ⟨b, hb⟩ := hG m
        exact ⟨a + b, by rw [MvPolynomial.coeff_add, ha, hb, map_add (f := _)]⟩
      · intro u' hu' F hF
        refine hint u' (fun m => ?_) F hF
        have h1 := hmono m 1
        simp only [Int.cast_one] at h1
        exact hu' m 1 h1
      · intro m m' c z hmc _
        rw [hiff] at hmc ⊢
        obtain ⟨o, ho⟩ := hmc m
        rw [MvPolynomial.coeff_monomial, if_pos rfl] at ho
        intro m''
        rw [MvPolynomial.coeff_monomial]
        split_ifs
        · exact ⟨o * z, by rw [ho, map_mul, map_intCast]⟩
        · exact ⟨0, by simp⟩
    exact integral_generators_preserve_lattice p _ hQ LL S u hu F hF
  · have hQ : MonomialGradedLattice p (fun F : MvPolynomial (ι × Fin n) (KK O) => InBB (O := O) p F) :=
      ⟨h0, hadd, hlin, hstep⟩
    exact integral_generators_preserve_lattice p _ hQ LL S u hu F hF

end Formalism.MainNotions.G.GLWeightTheory
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.PolynomialIsotypicLatticeOfParts
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem operator_list_lattice_scaling {O : Type} [CommRing O] [IsDomain O] {σ : Type} (p : ℕ)
    (L : Submodule O (MvPolynomial σ (KK O))) (W : Submodule (KK O) (MvPolynomial σ (KK O)))
    (l : List (Module.End (KK O) (MvPolynomial σ (KK O)) × ℕ))
    (hW : ∀ eD ∈ l, ∀ F ∈ W, eD.1 F ∈ W)
    (hL : ∀ eD ∈ l, ∀ F ∈ W, F ∈ L → ((p : KK O) ^ eD.2) • eD.1 F ∈ L) :
    ∀ F ∈ W, F ∈ L → (l.map Prod.fst).prod F ∈ W ∧
      ((p : KK O) ^ (l.map Prod.snd).sum) • (l.map Prod.fst).prod F ∈ L := by
  induction l with
  | nil =>
    intro F hF hFL
    simp [hF, hFL]
  | cons eD l ih =>
    intro F hF hFL
    have hW' : ∀ e ∈ l, ∀ F ∈ W, e.1 F ∈ W := fun e he => hW e (List.mem_cons_of_mem _ he)
    have hL' : ∀ e ∈ l, ∀ F ∈ W, F ∈ L → ((p : KK O) ^ e.2) • e.1 F ∈ L :=
      fun e he => hL e (List.mem_cons_of_mem _ he)
    obtain ⟨h1, h2⟩ := ih hW' hL' F hF hFL
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    refine ⟨hW eD (by simp) _ h1, ?_⟩
    have h3 := hL eD (by simp) _ (W.smul_mem ((p : KK O) ^ (l.map Prod.snd).sum) h1) h2
    rw [map_smul, smul_smul, ← pow_add] at h3
    exact h3

theorem polynomial_isotypic_lattice_of_parts (D : Formalism.BasicNotions.D7) (hCR : CompleteReducibilityIsotypic) (hOrth : ContravariantIsotypicOrthogonal) (hDom : HighestWeightDominant)
    (hRes : SubrepRestrictionRep) (hPol : PolynomialGLRepresentation) (hLat : AdmissibleDVRIntegralFormLatticesStable) (h13 : IsotypicProjectorTheoremField D) : FilteredProjectorCorollaryField D := by
  intro p n' O _ _ _ S0 hG n ι _ LL N Ss hmono
  obtain ⟨hchar, hLat'⟩ := hLat p n' O S0 hG
  obtain ⟨hL1, hL2, BBs, hBB, hL3⟩ := hLat' n ι LL
  refine ⟨fun i => hL1 (Ss i), ?_⟩
  intro ee hee
  obtain ⟨hP1, hP2, hP3, -, -, -, B, hB1, hB2⟩ := hPol (KK O) ι n LL
  have hT : ∀ S : Set ι, (⨆ mu : Fin n → ℤ, isoSub (glOps (KK O) n LL S) mu) = ⊤ :=
    fun S => hCR (KK O) _ n _ (hP1 S)

  have hdis : ∀ i lam (S' : Set ι), Disjoint (Ss i) S' → ∀ a b,
      ee i lam * glOps (KK O) n LL S' a b = glOps (KK O) n LL S' a b * ee i lam := by
    intro i lam S' hS' a b
    refine isotypic_projector_commutes _ (hT (Ss i)) lam _ (hee i lam) _ fun mu x hx => ?_
    exact isotypic_stable_commuting _ _ (fun c d => (hP2 (Ss i) S' hS' c d a b).symm) mu x hx
  have hle : ∀ i j, i ≤ j → ∀ lam a b,
      ee i lam * glOps (KK O) n LL (Ss j) a b = glOps (KK O) n LL (Ss j) a b * ee i lam := by
    intro i j hij lam a b
    rw [hP3 (Ss i) (Ss j) (hmono hij) a b, mul_add, add_mul, hdis i lam _ Set.disjoint_sdiff_right a b]
    congr 1
    exact isotypic_projector_commutes _ (hT (Ss i)) lam _ (hee i lam) _ fun mu x hx => isotypic_stable_gl_operator _ mu a b x hx
  have hcomm' : ∀ i j, i ≤ j → ∀ lam mu, ee i lam * ee j mu = ee j mu * ee i lam := by
    intro i j hij lam mu
    refine (isotypic_projector_commutes _ (hT (Ss j)) mu _ (hee j mu) _ fun nu x hx => ?_).symm
    exact isotypic_stable_commuting _ _ (fun c d => hle i j hij lam c d) nu x hx
  refine ⟨hle, hdis, ?_, ?_, ?_⟩
  · intro i j lam mu
    rcases le_total i j with h | h
    · exact hcomm' i j h lam mu
    · exact (hcomm' j i h mu lam).symm
  · intro i lam F G
    rw [← hB1, ← hB1]
    exact isotypic_projector_selfAdjoint _ (hT (Ss i)) lam _ (hee i lam) B
      (hOrth (KK O) _ n _ (hP1 (Ss i)) B (fun a b x y => hB2 (Ss i) a b x y)) F G
  · intro T d F hF
    have hstep := fun (i : Fin N) (lam : Fin n → ℤ) =>
      isotypic_projector_lattice_scaling D hDom hRes hPol h13 p n' O S0 hG n ι LL (Ss i) d lam (ee i lam) (hee i lam)
    have main : ∀ L : Submodule O (MvPolynomial (ι × Fin n) (KK O)),
        (∀ S : Set ι, ∀ u ∈ UZgens (glOps (KK O) n LL S), ∀ F ∈ L, u F ∈ L) → (latticeMultidegreePart L d).FG →
        MQ (K := KK O) (latticeMultidegreePart L d) = ⊤ → F ∈ L →
        ((p : KK O) ^ (∑ i, N0 n * Nat.log p (2 * degIn d (Ss i) + n - 1))) •
          (∑ t ∈ T, (List.ofFn fun i => ee i (t i)).prod) F ∈ L := by
      intro L hst hFG hMQ hFL
      rw [LinearMap.sum_apply, Finset.smul_sum]
      refine Submodule.sum_mem _ fun t _ => ?_
      have h := operator_list_lattice_scaling p L (Pol (KK O) n d)
        (List.ofFn fun i => (ee i (t i), N0 n * Nat.log p (2 * degIn d (Ss i) + n - 1)))
        (by
          intro eD heD
          obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 heD
          exact (hstep i (t i)).1)
        (by
          intro eD heD
          obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 heD
          exact (hstep i (t i)).2 L (hst (Ss i)) hFG hMQ) F hF hFL
      rw [List.map_ofFn, List.map_ofFn, List.sum_ofFn] at h
      exact h.2
    obtain ⟨h1, h2, h3, h4⟩ := hL3 d
    refine ⟨fun hFL => main _ (fun S u hu => (hL2 S u hu).1) h1 h2 hFL, fun hFB => ?_⟩
    rw [← hBB] at hFB ⊢
    exact main BBs (fun S u hu F hF => (hBB _).2 ((hL2 S u hu).2 F ((hBB _).1 hF))) h3 h4 hFB

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem integral_formula_lattice_holds : AdmissibleDVRIntegralFormLatticesStable := by
  intro p n' O _ _ _ S0 hG
  have hV : ValuationProperties p O := valuation_properties_hold hG.prime S0
  have hchar := dvr_fraction_field_char_zero hG.prime S0
  exact ⟨hchar, fun n ι _ LL => ⟨fun S => integral_formula_stability_holds hG.prime hV n ι LL S,
    fun S => char_zero_stability_of_closure hG.prime hchar (fock_lattice_closure_holds hV) n ι LL S, fock_lattice_finite_spanning_holds hG.prime S0 hV n ι⟩⟩

theorem polynomial_isotypic_lattice_corollary (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h13 : IsotypicProjectorTheoremField D) : FilteredProjectorCorollaryField D :=
  polynomial_isotypic_lattice_of_parts D (complete_reducibility_of_semisimple D h2) contravariant_orthogonality_holds highest_weight_dominant_holds (subrep_restriction_of_reducibility (complete_reducibility_of_semisimple D h2)) polynomial_representation_holds integral_formula_lattice_holds h13

end Formalism.MainNotions.G.GLWeightTheory
