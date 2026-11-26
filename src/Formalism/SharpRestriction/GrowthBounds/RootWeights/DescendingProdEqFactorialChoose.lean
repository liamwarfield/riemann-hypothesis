module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.ContravariantIsotypicOrthogonal

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.PolarizationDividedPowerSumSucc
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section v2dpAbs

variable {R : Type*} [CommRing R] {σ ι : Type*} [DecidableEq ι]

def dividedPowerExponent (src dst : ι → σ) (m : σ →₀ ℕ) (f : ι →₀ ℕ) : σ →₀ ℕ :=
  (m - Finsupp.mapDomain src f) + Finsupp.mapDomain dst f

def dividedPowerCoefficient (sg : ι → R) (src : ι → σ) (s : Finset ι) (m : σ →₀ ℕ) (f : ι →₀ ℕ) : R :=
  ∏ l ∈ s, sg l ^ (f l) * ((m (src l)).choose (f l) : R)

def dividedPowerMonomialTerm (sg : ι → R) (src dst : ι → σ) (s : Finset ι) (m : σ →₀ ℕ) (f : ι →₀ ℕ) : MvPolynomial σ R :=
  monomial (dividedPowerExponent src dst m f) (dividedPowerCoefficient sg src s m f)

def dividedPowerMonomialSum (sg : ι → R) (src dst : ι → σ) (s : Finset ι) (k : ℕ) (m : σ →₀ ℕ) : MvPolynomial σ R :=
  ∑ f ∈ Finset.finsuppAntidiag s k, dividedPowerMonomialTerm sg src dst s m f

def polarizationDerivation (sg : ι → R) (src dst : ι → σ) (l : ι) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  sg l • ((LinearMap.mulLeft R (X (dst l))) ∘ₗ (pderiv (src l)).toLinearMap)

theorem polarization_dividedPowerTerm (sg : ι → R) (src dst : ι → σ) (hs : Function.Injective src) (hd : ∀ l l', dst l' ≠ src l)
    (s : Finset ι) (m : σ →₀ ℕ) (f : ι →₀ ℕ) (l : ι) (hl : l ∈ s) :
    polarizationDerivation sg src dst l (dividedPowerMonomialTerm sg src dst s m f) =
      (f l + 1) • dividedPowerMonomialTerm sg src dst s m (f + Finsupp.single l 1) := by
  classical
  have h1 : Finsupp.mapDomain src f (src l) = f l := Finsupp.mapDomain_apply_of_injective hs f l
  have h2 : ∀ g : ι →₀ ℕ, Finsupp.mapDomain dst g (src l) = 0 := fun g =>
    Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨l', h⟩; exact hd l l' h)
  have hexp : Finsupp.single (dst l) 1 + (dividedPowerExponent src dst m f - Finsupp.single (src l) 1) =
      dividedPowerExponent src dst m (f + Finsupp.single l 1) := by
    ext v
    simp only [dividedPowerExponent, Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.add_apply,
      Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases hv : src l = v
    · subst hv
      have h3 := hd l l
      simp only [h1, h2, h3, if_true, if_false]
      omega
    · simp only [hv, if_false]
      omega
  have he : dividedPowerExponent src dst m f (src l) = m (src l) - f l := by
    simp [dividedPowerExponent, h1, h2]
  have hcf : sg l * (dividedPowerCoefficient sg src s m f * ((dividedPowerExponent src dst m f (src l) : ℕ) : R)) =
      ((f l + 1 : ℕ) : R) * dividedPowerCoefficient sg src s m (f + Finsupp.single l 1) := by
    rw [he]
    unfold dividedPowerCoefficient
    rw [← Finset.mul_prod_erase s _ hl, ← Finset.mul_prod_erase s _ hl]
    have h4 : ∏ x ∈ s.erase l, sg x ^ ((f + Finsupp.single l 1 : ι →₀ ℕ) x) *
        ((m (src x)).choose ((f + Finsupp.single l 1 : ι →₀ ℕ) x) : R) =
        ∏ x ∈ s.erase l, sg x ^ (f x) * ((m (src x)).choose (f x) : R) := by
      apply Finset.prod_congr rfl
      intro x hx
      have hx' : x ≠ l := (Finset.mem_erase.1 hx).1
      simp [hx'.symm]
    rw [h4]
    have hc : ((m (src l)).choose (f l + 1) : R) * ((f l + 1 : ℕ) : R) =
        ((m (src l)).choose (f l) : R) * ((m (src l) - f l : ℕ) : R) := by
      exact_mod_cast congrArg (Nat.cast (R := R)) (Nat.choose_succ_right_eq (m (src l)) (f l))
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, pow_succ]
    generalize (∏ x ∈ s.erase l, sg x ^ (f x) * ((m (src x)).choose (f x) : R)) = Er
    linear_combination (-(sg l ^ f l * sg l * Er)) * hc
  simp only [polarizationDerivation, dividedPowerMonomialTerm, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, pderiv_monomial]
  rw [X, monomial_mul, hexp, one_mul, smul_monomial, smul_eq_mul, hcf, ← nsmul_eq_mul, map_nsmul]

theorem finsuppAntidiag_succ_reindex {N : Type*} [AddCommMonoid N] (s : Finset ι) (k : ℕ) (l : ι) (hl : l ∈ s)
    (F : (ι →₀ ℕ) → N) :
    ∑ g ∈ Finset.finsuppAntidiag s (k + 1), (g l) • F g =
      ∑ f ∈ Finset.finsuppAntidiag s k, (f l + 1) • F (f + Finsupp.single l 1) := by
  have hL : ∑ g ∈ Finset.finsuppAntidiag s (k + 1), (g l) • F g =
      ∑ g ∈ (Finset.finsuppAntidiag s (k + 1)).filter (fun g => g l ≠ 0), (g l) • F g := by
    refine (Finset.sum_filter_of_ne ?_).symm
    intro g _ h h0
    apply h
    simp [h0]
  rw [hL]
  symm
  apply Finset.sum_nbij' (fun f => f + Finsupp.single l 1) (fun g => g - Finsupp.single l 1)
  · intro f hf
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_finsuppAntidiag] at hf ⊢
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← hf.1]
      simp [Finset.sum_add_distrib, Finsupp.single_apply, hl]
    · intro x hx
      rcases Finset.mem_union.1 (Finsupp.support_add hx) with h | h
      · exact hf.2 h
      · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset h)]
        exact hl
    · simp
  · intro g hg
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_finsuppAntidiag] at hg ⊢
    have hle : Finsupp.single l 1 ≤ g := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hg.2)
    have hg' : g - Finsupp.single l 1 + Finsupp.single l 1 = g := tsub_add_cancel_of_le hle
    refine ⟨?_, ?_⟩
    · have hsum : ∑ x ∈ s, (g - Finsupp.single l 1 : ι →₀ ℕ) x + ∑ x ∈ s, (Finsupp.single l 1 : ι →₀ ℕ) x =
          ∑ x ∈ s, g x := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun x _ => by rw [← Finsupp.add_apply, hg'])
      have h1 : ∑ x ∈ s, (Finsupp.single l 1 : ι →₀ ℕ) x = 1 := by
        simp [Finsupp.single_apply, hl]
      have h2 : ∑ x ∈ s, g x = k + 1 := hg.1.1
      have h3 : ∑ x ∈ s, (g - Finsupp.single l 1 : ι →₀ ℕ) x = k := by omega
      exact h3
    · intro x hx
      apply hg.1.2
      rw [Finsupp.mem_support_iff] at hx ⊢
      intro h0
      apply hx
      simp [h0]
  · intro f _
    simp
  · intro g hg
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_finsuppAntidiag] at hg
    exact tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hg.2))
  · intro f _
    simp

theorem polarization_dividedPowerSum_succ (sg : ι → R) (src dst : ι → σ) (hs : Function.Injective src) (hd : ∀ l l', dst l' ≠ src l)
    (s : Finset ι) (m : σ →₀ ℕ) (k : ℕ) :
    (∑ l ∈ s, polarizationDerivation sg src dst l) (dividedPowerMonomialSum sg src dst s k m) = (k + 1) • dividedPowerMonomialSum sg src dst s (k + 1) m := by
  have h1 : (∑ l ∈ s, polarizationDerivation sg src dst l) (dividedPowerMonomialSum sg src dst s k m) =
      ∑ l ∈ s, ∑ f ∈ Finset.finsuppAntidiag s k, polarizationDerivation sg src dst l (dividedPowerMonomialTerm sg src dst s m f) := by
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun l _ => map_sum _ _ _)
  have h2 : ∀ l ∈ s, ∑ f ∈ Finset.finsuppAntidiag s k, polarizationDerivation sg src dst l (dividedPowerMonomialTerm sg src dst s m f) =
      ∑ g ∈ Finset.finsuppAntidiag s (k + 1), (g l) • dividedPowerMonomialTerm sg src dst s m g := by
    intro l hl
    rw [finsuppAntidiag_succ_reindex s k l hl (dividedPowerMonomialTerm sg src dst s m)]
    exact Finset.sum_congr rfl (fun f _ => polarization_dividedPowerTerm sg src dst hs hd s m f l hl)
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_comm]
  unfold dividedPowerMonomialSum
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro g hg
  rw [← Finset.sum_smul, (Finset.mem_finsuppAntidiag.1 hg).1]

theorem dividedPowerMonomialSum_zero (sg : ι → R) (src dst : ι → σ) (s : Finset ι) (m : σ →₀ ℕ) :
    dividedPowerMonomialSum sg src dst s 0 m = monomial m 1 := by
  simp [dividedPowerMonomialSum, dividedPowerMonomialTerm, dividedPowerExponent, dividedPowerCoefficient, Finset.finsuppAntidiag_zero]

end v2dpAbs

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section v2dpCon

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ}

def polarizationSource (LL : Letters ι) (a b : Fin n) (l : ι) : ι × Fin n := if LL.vec l then (l, b) else (l, a)

def polarizationTarget (LL : Letters ι) (a b : Fin n) (l : ι) : ι × Fin n := if LL.vec l then (l, a) else (l, b)

def polarizationLetterSign (R : Type*) [CommRing R] (LL : Letters ι) (l : ι) : R := if LL.vec l then 1 else -1

theorem polarizationSource_injective (LL : Letters ι) (a b : Fin n) : Function.Injective (polarizationSource LL a b) := by
  intro l l' h
  have h1 : ∀ l₀, (polarizationSource LL a b l₀).1 = l₀ := fun l₀ => by
    unfold polarizationSource; split_ifs <;> rfl
  rw [← h1 l, h, h1 l']

theorem polarizationTarget_ne_source (LL : Letters ι) (a b : Fin n) (hab : a ≠ b) (l l' : ι) :
    polarizationTarget LL a b l' ≠ polarizationSource LL a b l := by
  intro h
  have e1 : (polarizationTarget LL a b l').1 = l' := by unfold polarizationTarget; split_ifs <;> rfl
  have e2 : (polarizationSource LL a b l).1 = l := by unfold polarizationSource; split_ifs <;> rfl
  have hl : l' = l := by rw [← e1, h, e2]
  subst hl
  unfold polarizationTarget polarizationSource at h
  split_ifs at h <;> simp only [Prod.mk.injEq] at h
  · exact hab h.2
  · exact hab h.2.symm

open Classical in
theorem glAct_eq_sum_polarizations (LL : Letters ι) (S : Set ι) (a b : Fin n) :
    glAct R LL S a b = ∑ l ∈ Finset.univ.filter (· ∈ S),
      polarizationDerivation (polarizationLetterSign R LL) (polarizationSource LL a b) (polarizationTarget LL a b) l := by
  rw [glAct, Finset.sum_filter]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp_all [polarizationDerivation, polarizationLetterSign, polarizationSource, polarizationTarget]

open Classical in
theorem divPowMono_eq_monomialSum (LL : Letters ι) (S : Set ι) (a b : Fin n) (k : ℕ) (m : ι × Fin n →₀ ℕ) :
    divPowMono R LL S a b k m =
      dividedPowerMonomialSum (polarizationLetterSign R LL) (polarizationSource LL a b) (polarizationTarget LL a b) (Finset.univ.filter (· ∈ S)) k m := by
  unfold divPowMono dividedPowerMonomialSum
  refine Finset.sum_congr rfl fun f hf => ?_
  have hsub : f.support ⊆ Finset.univ.filter (· ∈ S) := (Finset.mem_finsuppAntidiag.1 hf).2
  unfold dividedPowerMonomialTerm dividedPowerExponent dividedPowerCoefficient
  congr 1
  rw [← Finset.prod_subset hsub (f := fun l => polarizationLetterSign R LL l ^ f l *
    ((m (polarizationSource LL a b l)).choose (f l) : R)) ?_]
  · refine Finset.prod_congr rfl fun l _ => ?_
    by_cases hv : LL.vec l <;> simp [polarizationLetterSign, polarizationSource, hv]
  · intro l _ hl
    rw [Finsupp.notMem_support_iff.1 hl]
    simp

theorem glAct_comp_divPow (LL : Letters ι) (S : Set ι) (a b : Fin n) (hab : a ≠ b) (k : ℕ) :
    glAct R LL S a b ∘ₗ divPow R LL S a b k = (k + 1) • divPow R LL S a b (k + 1) := by
  classical
  refine (MvPolynomial.basisMonomials (ι × Fin n) R).ext fun m => ?_
  rw [LinearMap.comp_apply, LinearMap.smul_apply]
  simp only [divPow, Module.Basis.constr_basis]
  rw [divPowMono_eq_monomialSum, divPowMono_eq_monomialSum, glAct_eq_sum_polarizations]
  exact polarization_dividedPowerSum_succ _ _ _ (polarizationSource_injective LL a b) (polarizationTarget_ne_source LL a b hab) _ m k

theorem divPow_zero' (LL : Letters ι) (S : Set ι) (a b : Fin n) : divPow R LL S a b 0 = LinearMap.id := by
  classical
  refine (MvPolynomial.basisMonomials (ι × Fin n) R).ext fun m => ?_
  rw [LinearMap.id_apply]
  simp only [divPow, Module.Basis.constr_basis]
  rw [divPowMono_eq_monomialSum, dividedPowerMonomialSum_zero, MvPolynomial.coe_basisMonomials]

theorem glAct_pow_eq_factorial_divPow (LL : Letters ι) (S : Set ι) (a b : Fin n) (hab : a ≠ b) (k : ℕ) :
    (glAct R LL S a b : Module.End R (MvPolynomial (ι × Fin n) R)) ^ k = k.factorial • divPow R LL S a b k := by
  induction k with
  | zero => rw [pow_zero, divPow_zero', Nat.factorial_zero, one_smul]; rfl
  | succ k ih =>
    rw [pow_succ', ih, Module.End.mul_eq_comp, LinearMap.comp_smul, glAct_comp_divPow LL S a b hab k,
      smul_smul]
    congr 1
    rw [Nat.factorial_succ]
    ring

theorem X_mul_pderiv_monomial' {σ : Type*} (v : σ) (m : σ →₀ ℕ) (c : R) :
    X v * pderiv v (monomial m c) = ((m v : ℕ) : R) • monomial m c := by
  classical
  rw [MvPolynomial.pderiv_monomial]
  by_cases h : m v = 0
  · simp [h]
  · have hle : Finsupp.single v 1 ≤ m := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h)
    rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, add_tsub_cancel_of_le hle,
      MvPolynomial.smul_monomial, smul_eq_mul, mul_comm]

theorem glAct_diagonal_monomial (LL : Letters ι) (S : Set ι) (a : Fin n) (m : ι × Fin n →₀ ℕ) (c : R) :
    glAct R LL S a a (monomial m c) = ((wtS LL S m a : ℤ) : R) • monomial m c := by
  classical
  rw [glAct, LinearMap.sum_apply, wtS, Int.cast_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp_all [-MvPolynomial.pderiv_monomial, X_mul_pderiv_monomial']

theorem list_prod_shifted_eigen {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (T : Module.End K V) (w : K) (x : V)
    (h : T x = w • x) (L : List ℕ) :
    ((L.map fun j : ℕ => T - (j : K) • (1 : Module.End K V)).prod) x = ((L.map fun j : ℕ => w - (j : K)).prod) • x := by
  induction L with
  | nil => simp
  | cons j L ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, map_smul,
      LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, h]
    rw [← sub_smul, smul_smul, mul_comm]

theorem list_range_prod_eq_finset_prod {K : Type*} [CommRing K] (w : K) (k : ℕ) :
    ((List.range k).map fun j : ℕ => w - (j : K)).prod = ∏ j ∈ Finset.range k, (w - (j : K)) := by
  rw [Finset.prod_eq_multiset_prod, Finset.range_val, Multiset.range, Multiset.map_coe,
    Multiset.prod_coe]

theorem descending_prod_eq_factorial_choose (z : ℤ) (k : ℕ) : ∏ j ∈ Finset.range k, (z - (j : ℤ)) = (k.factorial : ℤ) * Ring.choose z k := by
  rw [← descPochhammer_eval_eq_prod_range, Polynomial.eval_eq_smeval,
    Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]

end v2dpCon

theorem dividedPower_formula_char_zero : DividedPowerFormulaCharZero := by
  intro R _ _ ι _ LL n S a b k hab
  show ((k.factorial : R)⁻¹) • (glAct R LL S a b) ^ k = divPow R LL S a b k
  rw [glAct_pow_eq_factorial_divPow LL S a b hab k, ← Nat.cast_smul_eq_nsmul R, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_smul]

theorem binomial_formula_char_zero : BinomialFormulaCharZero := by
  intro R _ _ ι _ LL n S a k
  classical
  refine (MvPolynomial.basisMonomials (ι × Fin n) R).ext fun m => ?_
  rw [binomPol, Module.Basis.constr_basis, MvPolynomial.coe_basisMonomials]
  show ((k.factorial : R)⁻¹ • ((List.range k).map fun j : ℕ =>
    glAct R LL S a a - (j : R) • (1 : Module.End R (MvPolynomial (ι × Fin n) R))).prod) (monomial m 1) = _
  rw [LinearMap.smul_apply, list_prod_shifted_eigen (glAct R LL S a a) ((wtS LL S m a : ℤ) : R) (monomial m 1)
    (glAct_diagonal_monomial LL S a m 1), list_range_prod_eq_finset_prod, smul_smul]
  have hc : ∏ j ∈ Finset.range k, (((wtS LL S m a : ℤ) : R) - (j : R)) =
      (((k.factorial : ℤ) * Ring.choose (wtS LL S m a) k : ℤ) : R) := by
    rw [← descending_prod_eq_factorial_choose]
    push_cast
    rfl
  rw [hc]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_mul,
    MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

end Formalism.MainNotions.G.GLWeightTheory
