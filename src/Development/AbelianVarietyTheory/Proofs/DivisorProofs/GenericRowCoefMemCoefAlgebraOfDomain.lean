module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRowSubstitutionPolyDiagonalEqSumComponents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepExistenceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleValueClassicalNormalForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectionStatementHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteOpenImmersionPSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneAddStrictLowerMemClosureTransvectionStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericGaussFactorisationCoeffSmulInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericGaussFactorisationCoeffSmulInjective
set_option autoImplicit false

noncomputable section

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

namespace GlobalTheory.GenCoef.LduLead

def key (N : ℕ) (v : Fin N × Fin N) : ℕ :=
  if v.1 = v.2 then N - (v.1 : ℕ) else N + 1 + Nat.pair v.1 v.2

theorem key_injective (N : ℕ) : Function.Injective (key N) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [key] at h
  split_ifs at h with h1 h2 h2
  · have ha := a.2; have ha' := a'.2
    have : (a : ℕ) = a' := by omega
    ext <;> simp_all [Fin.ext_iff]
  · omega
  · omega
  · have h3 : Nat.pair a b = Nat.pair a' b' := by omega
    rw [Nat.pair_eq_pair] at h3
    ext <;> simp [Fin.ext_iff, h3.1, h3.2]

def Var (N : ℕ) : Type := Fin N × Fin N

instance (N : ℕ) : LinearOrder (Var N) := LinearOrder.lift' (key N) (key_injective N)

instance (N : ℕ) : Finite (Var N) := inferInstanceAs (Finite (Fin N × Fin N))

def ord (N : ℕ) : MonomialOrder (Fin N × Fin N) := MonomialOrder.lex (σ := Var N)

theorem ord_lt_of (N : ℕ) (e f : Fin N × Fin N →₀ ℕ) (i : Fin N × Fin N)
    (h1 : ∀ j, key N j < key N i → e j = f j) (h2 : e i < f i) :
    (ord N).toSyn e < (ord N).toSyn f := by
  have hk : (MonomialOrder.lex (σ := Var N)).toSyn (e : Var N →₀ ℕ) <
      (MonomialOrder.lex (σ := Var N)).toSyn (f : Var N →₀ ℕ) := by
    exact (MonomialOrder.lex_lt_iff (σ := Var N)).2 (Finsupp.Lex.lt_iff.2 ⟨i, fun j hj => h1 j hj, h2⟩)
  exact hk

end GlobalTheory.GenCoef.LduLead

namespace GlobalTheory.GenCoef.LduLead

theorem key_lt_diag {N : ℕ} {j : Fin N × Fin N} {d : Fin N} (h : key N j < key N (d, d)) :
    j = (j.1, j.1) ∧ d < j.1 := by
  obtain ⟨x, y⟩ := j
  simp only [key, if_true] at h
  split_ifs at h with hxy
  · subst hxy; refine ⟨rfl, ?_⟩
    rw [Fin.lt_def]; have := d.2; have := x.2; simp at h ⊢; omega
  · omega

def lead (N : ℕ) (v : Fin N × Fin N) : Fin N × Fin N →₀ ℕ :=
  Finsupp.single v 1 + if v.1 = v.2 then 0 else Finsupp.single (min v.1 v.2, min v.1 v.2) 1

theorem lead_ne_zero (N : ℕ) (v : Fin N × Fin N) : lead N v ≠ 0 := by
  intro h
  have := congrArg (fun f => f v) h
  simp [lead] at this

variable (O : Type) [CommRing O] (N : ℕ)

theorem lduHom_X (v : Fin N × Fin N) :
    lduHom O N (X v) = ∑ c : Fin N, lowGen O N v.1 c * X (c, c) * upGen O N c v.2 := by
  rw [lduHom, aeval_X, diagGen, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]

end GlobalTheory.GenCoef.LduLead

namespace GlobalTheory.GenCoef.LduLead

variable (O : Type) [CommRing O] (N : ℕ)

theorem lead_apply (v w : Fin N × Fin N) :
    lead N v w = (if v = w then 1 else 0) +
      (if v.1 = v.2 then 0 else if (min v.1 v.2, min v.1 v.2) = w then 1 else 0) := by
  unfold lead
  split_ifs <;> simp_all [Finsupp.single_apply]

theorem entry_lead [Nontrivial O] (a b : Fin N) :
    (ord N).degree (lduHom O N (X (a, b))) = lead N (a, b) ∧
      (ord N).Monic (lduHom O N (X (a, b))) := by
  classical
  obtain ⟨d, hd⟩ : ∃ d, d = min a b := ⟨_, rfl⟩
  have hda : d ≤ a := hd ▸ min_le_left a b
  have hdb : d ≤ b := hd ▸ min_le_right a b
  have hdab : (d : ℕ) = a ∨ (d : ℕ) = b := by
    rcases le_total a b with h | h
    · left; rw [hd, min_eq_left h]
    · right; rw [hd, min_eq_right h]
  have ht : lowGen O N a d * X (d, d) * upGen O N d b = monomial (lead N (a, b)) 1 := by
    rcases lt_trichotomy a b with h | h | h
    · have e1 : d = a := hd.trans (min_eq_left h.le)
      have e2 : lead N (a, b) = Finsupp.single (a, a) 1 + Finsupp.single (a, b) 1 := by
        simp [lead, h.ne, min_eq_left h.le, add_comm]
      rw [e1, e2]
      simp [lowGen, upGen, h, h.ne, X, monomial_mul]
    · subst h
      have e1 : d = a := hd.trans (min_self a)
      rw [e1]
      simp [lowGen, upGen, lead, X]
    · have e1 : d = b := hd.trans (min_eq_right h.le)
      have e2 : lead N (a, b) = Finsupp.single (a, b) 1 + Finsupp.single (b, b) 1 := by
        simp [lead, h.ne', min_eq_right h.le]
      rw [e1, e2]
      simp [lowGen, upGen, h, h.ne', X, monomial_mul]
  have hpos : 0 < (ord N).toSyn (lead N (a, b)) := by
    rw [MonomialOrder.toSyn_lt_iff_ne_zero, Ne, (ord N).toSyn_eq_zero_iff]
    exact lead_ne_zero N _
  have hrest : (ord N).toSyn ((ord N).degree (∑ c ∈ Finset.univ.erase d,
      lowGen O N a c * X (c, c) * upGen O N c b)) < (ord N).toSyn (lead N (a, b)) := by
    refine lt_of_le_of_lt MonomialOrder.degree_sum_le ?_
    rw [Finset.sup_lt_iff (by simpa using hpos)]
    intro c hc
    have hc' : c ≠ d := Finset.ne_of_mem_erase hc
    by_cases hcd : c < d
    · have hca : c < a := lt_of_lt_of_le hcd hda
      have hcb : c < b := lt_of_lt_of_le hcd hdb
      have hm : lowGen O N a c * X (c, c) * upGen O N c b =
          monomial (Finsupp.single (a, c) 1 + Finsupp.single (c, c) 1 + Finsupp.single (c, b) 1) 1 := by
        simp [lowGen, upGen, hca.ne', hca, hcb.ne, hcb, X, monomial_mul]
      rw [hm]
      have h1 : (d : ℕ) ≤ a := hda
      have h2 : (d : ℕ) ≤ b := hdb
      have h3 : (c : ℕ) < d := hcd
      have h6 : (c : ℕ) < a := hca
      have h7 : (c : ℕ) < b := hcb
      refine lt_of_le_of_lt (MonomialOrder.degree_monomial_le _) (ord_lt_of N _ _ (d, d) ?_ ?_)
      · intro j hj
        obtain ⟨hj1, hj2⟩ := key_lt_diag hj
        rw [hj1]
        have h4 : (d : ℕ) < j.1 := hj2
        simp only [lead_apply, ← hd, Finsupp.add_apply, Finsupp.single_apply, Prod.ext_iff, Fin.ext_iff]
        split_ifs <;> omega
      · simp only [lead_apply, ← hd, Finsupp.add_apply, Finsupp.single_apply, Prod.ext_iff, Fin.ext_iff]
        split_ifs <;> omega
    · have hdc : d < c := lt_of_le_of_ne (not_lt.1 hcd) (Ne.symm hc')
      have hz : lowGen O N a c * X (c, c) * upGen O N c b = 0 := by
        rcases lt_or_ge a c with hac | hca
        · simp [lowGen, hac.ne, not_lt.2 hac.le]
        · have hbc : b < c := by
            rcases min_lt_iff.1 (hd ▸ hdc) with h | h
            · exact absurd hca (not_le.2 h)
            · exact h
          simp [upGen, hbc.ne', not_lt.2 hbc.le]
      rw [hz, MonomialOrder.degree_zero, map_zero]
      exact hpos
  have hsum := lduHom_X O N (a, b)
  dsimp only at hsum
  rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ d), ht]
  have hm : (ord N).degree (monomial (lead N (a, b)) (1 : O)) = lead N (a, b) := by
    rw [MonomialOrder.degree_monomial]; simp
  refine ⟨?_, ?_⟩
  · rw [MonomialOrder.degree_add_of_lt (by rw [hm]; exact hrest), hm]
  · exact MonomialOrder.Monic.add_of_lt MonomialOrder.monic_monomial_one (by rw [hm]; exact hrest)

end GlobalTheory.GenCoef.LduLead

namespace GlobalTheory.GenCoef.LduLead

variable (O : Type) [CommRing O] (N : ℕ)

def leadExp (m : Fin N × Fin N →₀ ℕ) : Fin N × Fin N →₀ ℕ := ∑ v, m v • lead N v

theorem leadExp_apply (m : Fin N × Fin N →₀ ℕ) (w : Fin N × Fin N) :
    leadExp N m w = ∑ v, m v * lead N v w := by
  simp [leadExp, Finsupp.finsetSum_apply]

theorem image_monomial_lead [Nontrivial O] (m : Fin N × Fin N →₀ ℕ) :
    (ord N).degree (lduHom O N (monomial m 1)) = leadExp N m ∧
      (ord N).Monic (lduHom O N (monomial m 1)) := by
  induction m using Finsupp.induction_linear with
  | zero => simp [leadExp, MonomialOrder.monic_one]
  | add f g hf hg =>
    have e : monomial (f + g) (1 : O) = monomial f 1 * monomial g 1 := by rw [monomial_mul, one_mul]
    rw [e, map_mul]
    have hle : leadExp N (f + g) = leadExp N f + leadExp N g := by
      simp [leadExp, add_smul, Finset.sum_add_distrib]
    refine ⟨?_, hf.2.mul hg.2⟩
    rw [MonomialOrder.degree_mul_of_isRegular_left (by rw [hf.2.leadingCoeff_eq_one]; exact isRegular_one)
      hg.2.ne_zero, hf.1, hg.1, hle]
  | single v k =>
    rw [← X_pow_eq_monomial, map_pow]
    obtain ⟨a, b⟩ := v
    obtain ⟨h1, h2⟩ := entry_lead O N a b
    have hle : leadExp N (Finsupp.single (a, b) k) = k • lead N (a, b) := by
      rw [leadExp, Finset.sum_eq_single (a, b)]
      · simp
      · intro w _ hw; simp [Finsupp.single_apply, Ne.symm hw]
      · simp
    refine ⟨?_, h2.pow⟩
    rw [MonomialOrder.degree_pow_of_pow_leadingCoeff_ne_zero (by rw [h2.leadingCoeff_eq_one, one_pow]; exact one_ne_zero),
      h1, hle]

theorem leadExp_injective : Function.Injective (leadExp N) := by
  intro m m' h
  have hw : ∀ w, leadExp N m w = leadExp N m' w := fun w => by rw [h]
  have hoff : ∀ w : Fin N × Fin N, w.1 ≠ w.2 → m w = m' w := by
    intro w hne
    have key : ∀ (n : Fin N × Fin N →₀ ℕ), leadExp N n w = n w := by
      intro n
      rw [leadExp_apply, Finset.sum_eq_single w]
      · have : (min w.1 w.2, min w.1 w.2) ≠ w := fun h' => hne (by rw [← h'])
        rw [lead_apply]; simp [hne, this]
      · intro v _ hv
        rw [lead_apply]
        have : (min v.1 v.2, min v.1 v.2) ≠ w := fun h' => hne (by rw [← h'])
        simp [hv, this]
      · simp
    rw [← key m, ← key m', hw]
  ext w
  by_cases hne : w.1 = w.2
  · have e := hw w
    rw [leadExp_apply, leadExp_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ w),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ w)] at e
    have hrest : ∑ v ∈ Finset.univ.erase w, m v * lead N v w = ∑ v ∈ Finset.univ.erase w, m' v * lead N v w := by
      refine Finset.sum_congr rfl fun v hv => ?_
      have hvw : v ≠ w := Finset.ne_of_mem_erase hv
      by_cases hv' : v.1 = v.2
      · rw [lead_apply]; simp [hvw, hv']
      · rw [hoff v hv']
    rw [hrest, add_left_inj] at e
    have hww : lead N w w = 1 := by rw [lead_apply]; simp [hne]
    simpa [hww] using e
  · exact hoff w hne

end GlobalTheory.GenCoef.LduLead

namespace GlobalTheory.GenCoef


open LduLead in
theorem lduHom_coeff_smul_injective : ∀ (O : Type) [CommRing O] (N : ℕ) (M : Type) [AddCommGroup M] [Module O M]
    (s : Finset (Fin N × Fin N →₀ ℕ)) (c : (Fin N × Fin N →₀ ℕ) → M),
    (∀ n, ∑ m ∈ s, (lduHom O N (monomial m 1)).coeff n • c m = 0) → ∀ m ∈ s, c m = 0 := by
  intro O _ N M _ _ s c H
  rcases subsingleton_or_nontrivial O with hO | hO
  · intro m _
    rw [← one_smul O (c m), Subsingleton.elim (1 : O) 0, zero_smul]
  classical
  by_contra hne
  push_neg at hne
  obtain ⟨m1, hm1, hc1⟩ := hne
  have hT : (s.filter fun m => c m ≠ 0).Nonempty := ⟨m1, Finset.mem_filter.2 ⟨hm1, hc1⟩⟩
  obtain ⟨m0, hm0, hmax⟩ := Finset.exists_max_image _ (fun m => (ord N).toSyn (leadExp N m)) hT
  rw [Finset.mem_filter] at hm0
  have e := H (leadExp N m0)
  rw [Finset.sum_eq_single m0] at e
  · obtain ⟨h1, h2⟩ := image_monomial_lead O N m0
    rw [← h1, h2.coeff_degree, one_smul] at e
    exact hm0.2 e
  · intro m hm hmm
    by_cases hcm : c m = 0
    · rw [hcm, smul_zero]
    · have hle := hmax m (Finset.mem_filter.2 ⟨hm, hcm⟩)
      have hlt : (ord N).toSyn (leadExp N m) < (ord N).toSyn (leadExp N m0) :=
        lt_of_le_of_ne hle fun h' => hmm (leadExp_injective N ((ord N).toSyn.injective h'))
      rw [MonomialOrder.coeff_eq_zero_of_lt (by rw [(image_monomial_lead O N m).1]; exact hlt), zero_smul]
  · intro h; exact absurd hm0.1 h

end GlobalTheory.GenCoef

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericGaussFactorisationCoeffSmulInjectiveStatement
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericGaussFactorisation_coeff_smul_injective : ∀ (O : Type) [CommRing O] (N : ℕ) (M : Type) [AddCommGroup M] [Module O M] (s : Finset (Fin N × Fin N →₀ ℕ)) (c : (Fin N × Fin N →₀ ℕ) → M), (∀ n, ∑ m ∈ s, (lduHom O N (monomial m 1)).coeff n • c m = 0) → ∀ m ∈ s, c m = 0 := by
  first | exact @GlobalTheory.GenCoef.lduHom_coeff_smul_injective | exact GlobalTheory.GenCoef.lduHom_coeff_smul_injective | (intros; apply GlobalTheory.GenCoef.lduHom_coeff_smul_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubstDualWeylExpressibleMatrixMulClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubstDualWeylExpressibleMatrixMulClosed
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.GenCoef

theorem rowSubst_mul_comp (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R]
    (Y Y' : Matrix (Fin N) (Fin N) R) (f : MvPolynomial (Fin N × Fin N) O) :
    rowSubst O N R (Y * Y') f = rowSubst R N R Y' (rowSubst O N R Y f) := by
  have h : (rowSubst O N R (Y * Y')) = ((rowSubst R N R Y').restrictScalars O).comp (rowSubst O N R Y) := by
    apply MvPolynomial.algHom_ext
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [rowSubst, AlgHom.comp_apply, AlgHom.restrictScalars_apply, aeval_X, map_sum, map_mul,
      algHom_C, Algebra.algebraMap_self, RingHom.id_apply, Matrix.mul_apply]
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  rw [h]; rfl

theorem rowSubst_self_map (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R]
    (Y' : Matrix (Fin N) (Fin N) R) (q : MvPolynomial (Fin N × Fin N) O) :
    rowSubst R N R Y' (MvPolynomial.map (algebraMap O R) q) = rowSubst O N R Y' q := by
  have h : ((rowSubst R N R Y').restrictScalars O).comp (MvPolynomial.mapAlgHom (Algebra.ofId O R)) = rowSubst O N R Y' := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [rowSubst]
  have := congrArg (fun φ => φ q) h
  simpa using this

theorem expr_mul (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (R : Type) [CommRing R] [Algebra O R]
    (Y Y' : Matrix (Fin N) (Fin N) R) (hY : Expr O N ν R Y) (hY' : Expr O N ν R Y') :
    Expr O N ν R (Y * Y') := by
  obtain ⟨n, r, p, hp, hf⟩ := hY
  obtain ⟨n', r', p', hp', hf'⟩ := hY'
  refine ⟨n * n', fun k => r (finProdFinEquiv.symm k).1 * r' (finProdFinEquiv.symm k).2,
    fun k => p' (finProdFinEquiv.symm k).2 * p (finProdFinEquiv.symm k).1, fun k => Subalgebra.mul_mem _ (hp' _) (hp _), ?_⟩
  intro f
  set_option synthInstance.maxHeartbeats 100000 in
    rw [rowSubst_mul_comp, hf f, map_sum]
  have e := (finProdFinEquiv (m := n) (n := n')).symm.sum_comp
    (fun x : Fin n × Fin n' => (r x.1 * r' x.2) • MvPolynomial.map (algebraMap O R)
      (((p' x.2 * p x.1) f : dualWeyl O N N ν) : MvPolynomial (Fin N × Fin N) O))
  rw [e, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, rowSubst_self_map, hf' (p i f), Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, Module.End.mul_apply]

end GlobalTheory.GenCoef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubstDualWeylExpressibleMatrixMulClosedStatement
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowSubstDualWeylExpressible_matrix_mul_closed : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (R : Type) [CommRing R] [Algebra O R] (Y Y' : Matrix (Fin N) (Fin N) R), Expr O N ν R Y → Expr O N ν R Y' → Expr O N ν R (Y * Y') := by
  first | exact @GlobalTheory.GenCoef.expr_mul | exact GlobalTheory.GenCoef.expr_mul | (intros; apply GlobalTheory.GenCoef.expr_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerRowOperatorMemDualWeylEndSubalgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerRowOperatorMemDualWeylEndSubalgebra
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RowDivMem
variable {O : Type} [CommRing O] {N : ℕ}

def wZ (N : ℕ) : Fin N × Fin N → (Fin N → ℤ) := fun v => Pi.single v.1 1

def δ (a b : Fin N) : Fin N → ℤ := Pi.single a 1 - Pi.single b 1

def PSh (a b : Fin N) (u : Fin N → ℤ) (P : Polynomial (MvPolynomial (Fin N × Fin N) O)) : Prop :=
  ∀ j : ℕ, IsWeightedHomogeneous (wZ N) (P.coeff j) (u + (j : ℤ) • δ a b)

theorem PSh.mul {a b : Fin N} {u u' : Fin N → ℤ} {P Q : Polynomial (MvPolynomial (Fin N × Fin N) O)}
    (hP : PSh a b u P) (hQ : PSh a b u' Q) : PSh a b (u + u') (P * Q) := by
  intro j
  rw [Polynomial.coeff_mul]
  rw [← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun x hx => ?_
  rw [mem_weightedHomogeneousSubmodule]
  have h := (hP x.1).mul (hQ x.2)
  have hx' : x.1 + x.2 = j := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  convert h using 1
  rw [← hx']; push_cast; rw [add_smul]; abel

theorem PSh.one (a b : Fin N) : PSh (O := O) a b 0 1 := by
  intro j
  rcases j with _ | j
  · simpa using isWeightedHomogeneous_one O (wZ N)
  · rw [Polynomial.coeff_one, if_neg (Nat.succ_ne_zero j)]
    exact isWeightedHomogeneous_zero _ _ _

theorem PSh.pow {a b : Fin N} {u : Fin N → ℤ} {P : Polynomial (MvPolynomial (Fin N × Fin N) O)}
    (hP : PSh a b u P) (n : ℕ) : PSh a b (n • u) (P ^ n) := by
  induction n with
  | zero => simpa using PSh.one (O := O) a b
  | succ n ih => rw [pow_succ, succ_nsmul]; exact ih.mul hP

theorem PSh.prod {a b : Fin N} {ι : Type} (s : Finset ι) (u : ι → Fin N → ℤ)
    (P : ι → Polynomial (MvPolynomial (Fin N × Fin N) O)) (h : ∀ i ∈ s, PSh a b (u i) (P i)) :
    PSh a b (∑ i ∈ s, u i) (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PSh.one (O := O) a b
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem PSh_rowGen_X (a b : Fin N) (hab : a ≠ b) (v : Fin N × Fin N) :
    PSh a b (wZ N v) (rowGen O a b (X v)) := by
  intro j
  simp only [rowGen, aeval_X]
  rcases j with _ | _ | j
  · by_cases hv : v.1 = b
    · simp [hv]; exact isWeightedHomogeneous_X O (wZ N) v
    · simp [hv]; exact isWeightedHomogeneous_X O (wZ N) v
  · by_cases hv : v.1 = b
    · simp [hv]
      convert isWeightedHomogeneous_X O (wZ N) (a, v.2) using 1
      simp [wZ, δ, hv]
    · simp [hv]; exact isWeightedHomogeneous_zero _ _ _
  · by_cases hv : v.1 = b
    · simp [hv, Polynomial.coeff_X, Polynomial.coeff_C]
      exact isWeightedHomogeneous_zero _ _ _
    · simp [hv, Polynomial.coeff_C]; exact isWeightedHomogeneous_zero _ _ _

theorem PSh.add {a b : Fin N} {u : Fin N → ℤ} {P Q : Polynomial (MvPolynomial (Fin N × Fin N) O)}
    (hP : PSh a b u P) (hQ : PSh a b u Q) : PSh a b u (P + Q) := fun j => by
  rw [Polynomial.coeff_add]; exact (hP j).add (hQ j)

theorem PSh.zero (a b : Fin N) (u : Fin N → ℤ) : PSh (O := O) a b u 0 := fun j => by
  rw [Polynomial.coeff_zero]; exact isWeightedHomogeneous_zero _ _ _

theorem PSh_rowGen_C (a b : Fin N) (r : O) : PSh a b 0 (rowGen O a b (C r)) := by
  intro j
  rw [show (C r : MvPolynomial (Fin N × Fin N) O) = algebraMap O _ r from rfl, AlgHom.commutes,
    Polynomial.algebraMap_apply, Polynomial.coeff_C]
  split_ifs with h
  · subst h
    simp only [Nat.cast_zero, zero_smul, add_zero]
    exact isWeightedHomogeneous_C (wZ N) r
  · exact isWeightedHomogeneous_zero _ _ _

theorem PSh_rowGen (a b : Fin N) (hab : a ≠ b) (u : Fin N → ℤ) (f : MvPolynomial (Fin N × Fin N) O)
    (hf : IsWeightedHomogeneous (wZ N) f u) : PSh a b u (rowGen O a b f) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  have key : ∀ d ∈ f.support, PSh a b u (rowGen O a b (monomial d (AddMonoidAlgebra.coeff f d))) := by
    intro d hd
    have hw : Finsupp.weight (wZ N) d = u := hf (mem_support_iff.mp hd)
    rw [monomial_eq, map_mul, Finsupp.prod, map_prod]
    have h1 := (PSh_rowGen_C a b (AddMonoidAlgebra.coeff f d)).mul
      (PSh.prod d.support (fun v => d v • wZ N v) (fun v => rowGen O a b (X v ^ d v)) fun v _ => by
        rw [map_pow]; exact (PSh_rowGen_X a b hab v).pow (d v))
    rw [zero_add] at h1
    convert h1 using 1
    rw [← hw, Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_induction _ (PSh a b u) (fun _ _ => PSh.add) (PSh.zero a b u) key

theorem weight_wZ (d : Fin N × Fin N →₀ ℕ) (c : Fin N) :
    Finsupp.weight (wZ N) d c = (Finsupp.weight (rowW N N) d c : ℤ) := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, wZ, rowW, Nat.cast_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [Pi.single_apply]

def shiftW (a b : Fin N) (k : ℕ) (w : Fin N → ℕ) : Fin N → ℕ :=
  fun c => w c + (if c = a then k else 0) - (if c = b then k else 0)

theorem rowDiv_isWH (a b : Fin N) (hab : a ≠ b) (j : ℕ) (w : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O)
    (hf : IsWeightedHomogeneous (rowW N N) f w) :
    IsWeightedHomogeneous (wZ N) (rowDiv O a b j f) ((fun c => (w c : ℤ)) + (j : ℤ) • δ a b) := by
  have hf' : IsWeightedHomogeneous (wZ N) f (fun c => (w c : ℤ)) := by
    intro d hd
    funext c
    rw [weight_wZ, hf hd]
  exact PSh_rowGen a b hab _ f hf' j

theorem proj_rowDiv (a b : Fin N) (hab : a ≠ b) (j k : ℕ) (w : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O)
    (hf : IsWeightedHomogeneous (rowW N N) f w) :
    weightedHomogeneousComponent (rowW N N) (shiftW a b k w) (rowDiv O a b j f) =
      if j = k then rowDiv O a b k f else 0 := by
  classical
  have hg := rowDiv_isWH a b hab j w f hf
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with h1 h2 h2
  · subst h2; rfl
  · by_contra hne
    have := congrFun (hg hne) a
    rw [weight_wZ, h1] at this
    simp [shiftW, δ, hab, Pi.single_apply] at this
    omega
  · subst h2
    by_contra hne
    apply h1
    funext c
    have := congrFun (hg (Ne.symm hne)) c
    rw [weight_wZ] at this
    simp only [shiftW, δ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul] at this ⊢
    split_ifs at this ⊢ <;> omega
  · simp

theorem rowAct_transvection (a b : Fin N) (h : MvPolynomial (Fin N × Fin N) O) :
    rowAct O (Matrix.transvection b a (1 : O)) h = Polynomial.eval 1 (rowGen O a b h) := by
  classical
  have key : (Polynomial.evalRingHom (1 : MvPolynomial (Fin N × Fin N) O)).comp (rowGen O a b (n := N)).toRingHom =
      (rowAct O (n := N) (Matrix.transvection b a (1 : O))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [rowGen, rowAct]
    · intro v
      simp [rowGen, rowAct, Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
        Finset.sum_add_distrib, add_mul, ite_mul]
      by_cases hv : v.1 = b
      · subst hv; simp
      · simp [hv, Ne.symm hv]
  exact (RingHom.congr_fun key h).symm

theorem proj_rowAct (a b : Fin N) (hab : a ≠ b) (k : ℕ) (w : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O)
    (hf : IsWeightedHomogeneous (rowW N N) f w) :
    weightedHomogeneousComponent (rowW N N) (shiftW a b k w) (rowAct O (Matrix.transvection b a (1 : O)) f) =
      rowDiv O a b k f := by
  classical
  rw [rowAct_transvection, Polynomial.eval_eq_sum_range]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [one_pow, mul_one, map_sum]
  have : ∀ j, (rowGen O a b f).coeff j = rowDiv O a b j f := fun j => rfl
  simp only [this, proj_rowDiv a b hab _ k w f hf, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with hk
  · rfl
  · exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

theorem rowW_le_total (d : Fin N × Fin N →₀ ℕ) (c : Fin N) :
    Finsupp.weight (rowW N N) d c ≤ ∑ s, Finsupp.weight (colW N N) d s := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, rowW, colW, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun v _ => ?_
  rw [← Finset.mul_sum]
  simp [Pi.single_apply]
  split_ifs <;> simp

def box (ν : Fin N → ℕ) : Finset (Fin N → ℕ) :=
  Fintype.piFinset fun _ : Fin N => Finset.range (∑ s, ν s + 1)

theorem decomp (ν : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ dualWeyl O N N ν) :
    f = ∑ w ∈ box ν, weightedHomogeneousComponent (rowW N N) w f := by
  classical
  have hcol : IsWeightedHomogeneous (colW N N) f ν :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp hf).1
  ext d
  rw [coeff_sum]
  simp only [coeff_weightedHomogeneousComponent, Finset.sum_ite_eq, ]
  split_ifs with h
  · rfl
  · by_contra hne
    apply h
    have hw := hcol hne
    simp only [box, Fintype.mem_piFinset, Finset.mem_range]
    intro c
    have := rowW_le_total d c
    rw [hw] at this
    omega

end GlobalTheory.RowDivMem

namespace GlobalTheory.GenCoef
open GlobalTheory.RowDivMem

theorem rowDiv_mem_dwAlg : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (a b : Fin N), a ≠ b → ∀ k : ℕ,
    ∃ p ∈ dwAlg O N ν, ∀ f : dualWeyl O N N ν,
      (p f : MvPolynomial (Fin N × Fin N) O) = rowDiv O a b k (f : MvPolynomial (Fin N × Fin N) O) := by
  intro O _ N ν a b hab k
  classical
  let g : GL (Fin N) O :=
    ⟨Matrix.transvection b a (-1), Matrix.transvection b a 1,
      by rw [Matrix.transvection_mul_transvection_same b a (Ne.symm hab)]; simp,
      by rw [Matrix.transvection_mul_transvection_same b a (Ne.symm hab)]; simp⟩
  have hg : ((g⁻¹ : GL (Fin N) O) : Matrix (Fin N) (Fin N) O) = Matrix.transvection b a 1 := rfl
  refine ⟨∑ w ∈ box ν, GlobalTheory.ExpFrame.rowProj O N ν (shiftW a b k w) * Formalism.UG.dualWeylRep O N N ν g *
      GlobalTheory.ExpFrame.rowProj O N ν w, ?_, fun f => ?_⟩
  · refine Subalgebra.sum_mem _ fun w _ => Subalgebra.mul_mem _ (Subalgebra.mul_mem _ ?_ ?_) ?_
    · exact Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩)
    · exact Algebra.subset_adjoin (Or.inl ⟨g, rfl⟩)
    · exact Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩)
  · rw [LinearMap.sum_apply, Submodule.coe_sum]
    conv_rhs => rw [decomp ν (f : MvPolynomial (Fin N × Fin N) O) f.2]
    have hlin : ∀ (s : Finset (Fin N → ℕ)) (F : (Fin N → ℕ) → MvPolynomial (Fin N × Fin N) O),
        rowDiv O a b k (∑ w ∈ s, F w) = ∑ w ∈ s, rowDiv O a b k (F w) := by
      intro s F
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [rowDiv, map_sum, Polynomial.finsetSum_coeff]
    rw [hlin]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [Module.End.mul_apply]
    change weightedHomogeneousComponent (rowW N N) (shiftW a b k w)
      (Formalism.UG.dwAct O N N g (weightedHomogeneousComponent (rowW N N) w (f : MvPolynomial (Fin N × Fin N) O))) = _
    rw [Formalism.UG.dwAct, hg]
    exact proj_rowAct a b hab k w _ (weightedHomogeneousComponent_isWeightedHomogeneous _ _)

end GlobalTheory.GenCoef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerRowOperatorMemDualWeylEndSubalgebraStatement
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedPowerRowOperator_mem_dualWeylEndSubalgebra : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (a b : Fin N), a ≠ b → ∀ k : ℕ, ∃ p ∈ dwAlg O N ν, ∀ f : dualWeyl O N N ν, (p f : MvPolynomial (Fin N × Fin N) O) = rowDiv O a b k (f : MvPolynomial (Fin N × Fin N) O) := by
  first | exact @GlobalTheory.GenCoef.rowDiv_mem_dwAlg | exact GlobalTheory.GenCoef.rowDiv_mem_dwAlg | (intros; apply GlobalTheory.GenCoef.rowDiv_mem_dwAlg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericRowCoefMemCoefAlgebraOfDomain
set_option autoImplicit false

noncomputable section

open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory.GenCoef

theorem expr_mul_of_parts : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (R : Type) [CommRing R] [Algebra O R]
    (Y Y' : Matrix (Fin N) (Fin N) R), Expr O N ν R Y → Expr O N ν R Y' → Expr O N ν R (Y * Y') := GlobalTheory.T.rowSubstDualWeylExpressible_matrix_mul_closed

theorem rowSubst_diagonal_of_parts : ∀ (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (d : Fin N → R) (D : ℕ)
    (f : MvPolynomial (Fin N × Fin N) O), f.totalDegree ≤ D →
    rowSubst O N R (Matrix.diagonal d) f = ∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (D + 1)),
      (∏ a, d a ^ w a) • MvPolynomial.map (algebraMap O R) (weightedHomogeneousComponent (rowW N N) w f) := GlobalTheory.T.matrixRowSubstitutionPoly_diagonal_eq_sum_components

theorem rowDiv_mem_of_parts : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (a b : Fin N), a ≠ b → ∀ k : ℕ,
    ∃ p ∈ dwAlg O N ν, ∀ f : dualWeyl O N N ν,
      (p f : MvPolynomial (Fin N × Fin N) O) = rowDiv O a b k (f : MvPolynomial (Fin N × Fin N) O) := GlobalTheory.T.dividedPowerRowOperator_mem_dualWeylEndSubalgebra

theorem rowSubst_transvection_of_parts : ∀ (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (a b : Fin N) (r : R)
    (D : ℕ) (f : MvPolynomial (Fin N × Fin N) O), f.totalDegree ≤ D →
    rowSubst O N R (Matrix.transvection a b r) f =
      ∑ k ∈ Finset.range (D + 1), r ^ k • MvPolynomial.map (algebraMap O R) (rowDiv O b a k f) := GlobalTheory.T.matrixRowSubstitutionPoly_transvection_eq_sum

theorem totalDegree_le_of_mem_of_parts : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O),
    f ∈ dualWeyl O N N ν → f.totalDegree ≤ ∑ a, ν a := GlobalTheory.T.totalDegree_le_of_mem_dualWeylLattice

theorem lower_mem_closure_of_parts : ∀ (R : Type) [CommRing R] (N : ℕ) (c : Matrix (Fin N) (Fin N) R), (∀ a b, a ≤ b → c a b = 0) →
    1 + c ∈ Submonoid.closure {M | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r} := GlobalTheory.T.one_add_strictLower_mem_closure_transvection'

theorem upper_mem_closure_of_parts : ∀ (R : Type) [CommRing R] (N : ℕ) (c : Matrix (Fin N) (Fin N) R), (∀ a b, b ≤ a → c a b = 0) →
    1 + c ∈ Submonoid.closure {M | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r} := GlobalTheory.T.one_add_strictUpper_mem_closure_transvection

theorem lduHom_pure_of_parts : ∀ (O : Type) [CommRing O] (N : ℕ) (M : Type) [AddCommGroup M] [Module O M]
    (s : Finset (Fin N × Fin N →₀ ℕ)) (c : (Fin N × Fin N →₀ ℕ) → M),
    (∀ n, ∑ m ∈ s, (lduHom O N (monomial m 1)).coeff n • c m = 0) → ∀ m ∈ s, c m = 0 := GlobalTheory.T.genericGaussFactorisation_coeff_smul_injective

theorem rowSubst_eq_sum_genSub_of_parts : ∀ (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R]
    (Y : Matrix (Fin N) (Fin N) R) (f : MvPolynomial (Fin N × Fin N) O),
    rowSubst O N R Y f = ∑ m ∈ (GlobalTheory.HighWt.genSub O N f).support, (m.prod fun v k => Y v.1 v.2 ^ k) •
      MvPolynomial.map (algebraMap O R) ((GlobalTheory.HighWt.genSub O N f).coeff m) := GlobalTheory.T.matrixRowSubstitutionPoly_eq_eval_genericRowSubstitution

theorem genSub_coeff_le_of_parts : ∀ (O : Type) [CommRing O] (N : ℕ) (D : ℕ) (f : MvPolynomial (Fin N × Fin N) O), f.totalDegree ≤ D →
    ∀ m, (GlobalTheory.HighWt.genSub O N f).coeff m ≠ 0 → ∀ v, m v ≤ D := GlobalTheory.T.genericRowSubstitution_coeff_exponent_le_degree

end GlobalTheory.GenCoef

namespace GlobalTheory.GenCoef

section Glue

variable {O : Type} [CommRing O] {N : ℕ} {ν : Fin N → ℕ} {R : Type} [CommRing R] [Algebra O R]

theorem expr_of_finset {κ : Type} (s : Finset κ) (Y : Matrix (Fin N) (Fin N) R) (r : κ → R)
    (p : κ → Module.End O (dualWeyl O N N ν)) (hp : ∀ i ∈ s, p i ∈ dwAlg O N ν)
    (h : ∀ f : dualWeyl O N N ν, rowSubst O N R Y (f : MvPolynomial (Fin N × Fin N) O) =
      ∑ i ∈ s, r i • MvPolynomial.map (algebraMap O R) (p i f : MvPolynomial (Fin N × Fin N) O)) :
    Expr O N ν R Y := by
  classical
  let e := s.equivFin
  refine ⟨s.card, fun j => r (e.symm j), fun j => p (e.symm j), fun j => hp _ (e.symm j).2, fun f => ?_⟩
  rw [h f, ← Finset.sum_coe_sort s]
  exact (Equiv.sum_comp e.symm (fun i : s => r i • MvPolynomial.map (algebraMap O R) (p i f : MvPolynomial (Fin N × Fin N) O))).symm

theorem expr_diagonal (d : Fin N → R) : Expr O N ν R (Matrix.diagonal d) := by
  classical
  refine expr_of_finset (Fintype.piFinset (fun _ : Fin N => Finset.range (∑ a, ν a + 1))) _ (fun w => ∏ a, d a ^ w a)
    (fun w => GlobalTheory.ExpFrame.rowProj O N ν w) (fun w _ => Algebra.subset_adjoin (Or.inr ⟨w, rfl⟩)) (fun f => ?_)
  rw [rowSubst_diagonal_of_parts O N R d _ _ (totalDegree_le_of_mem_of_parts O N ν _ f.2)]
  rfl

theorem expr_one : Expr O N ν R 1 := by
  have := expr_diagonal (O := O) (N := N) (ν := ν) (R := R) (fun _ => 1)
  rwa [Matrix.diagonal_one] at this

theorem expr_transvection (a b : Fin N) (hab : a ≠ b) (r : R) : Expr O N ν R (Matrix.transvection a b r) := by
  classical
  choose p hp hpf using rowDiv_mem_of_parts O N ν b a hab.symm
  refine expr_of_finset (Finset.range (∑ a, ν a + 1)) _ (fun k => r ^ k) p (fun k _ => hp k) (fun f => ?_)
  rw [rowSubst_transvection_of_parts O N R a b r _ _ (totalDegree_le_of_mem_of_parts O N ν _ f.2)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hpf k f]

theorem expr_of_mem_closure (Y : Matrix (Fin N) (Fin N) R)
    (hY : Y ∈ Submonoid.closure {M | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r}) :
    Expr O N ν R Y := by
  induction hY using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨a, b, r, hab, rfl⟩ := hx
    exact expr_transvection a b hab r
  | one => exact expr_one
  | mul x y _ _ hx hy => exact expr_mul_of_parts O N ν R x y hx hy

theorem expr_ldu : Expr O N ν (MvPolynomial (Fin N × Fin N) O) (lowGen O N * diagGen O N * upGen O N) := by
  classical
  have hL : lowGen O N = 1 + Matrix.of (fun a b => if b < a then (X (a, b) : MvPolynomial (Fin N × Fin N) O) else 0) := by
    ext a b
    by_cases h : a = b
    · subst h; simp [lowGen]
    · simp [lowGen, h, Matrix.one_apply_ne h]
  have hU : upGen O N = 1 + Matrix.of (fun a b => if a < b then (X (a, b) : MvPolynomial (Fin N × Fin N) O) else 0) := by
    ext a b
    by_cases h : a = b
    · subst h; simp [upGen]
    · simp [upGen, h, Matrix.one_apply_ne h]
  refine expr_mul_of_parts O N ν _ _ _ (expr_mul_of_parts O N ν _ _ _ ?_ (expr_diagonal _)) ?_
  · rw [hL]
    exact expr_of_mem_closure _ (lower_mem_closure_of_parts _ N _ fun a b hab => by simp [not_lt.mpr hab])
  · rw [hU]
    exact expr_of_mem_closure _ (upper_mem_closure_of_parts _ N _ fun a b hab => by simp [not_lt.mpr hab])

end Glue

end GlobalTheory.GenCoef

namespace GlobalTheory.GenCoef

theorem coef_mem (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (m : Fin N × Fin N →₀ ℕ) :
    ∃ p ∈ dwAlg O N ν, ∀ f : dualWeyl O N N ν,
      (p f : MvPolynomial (Fin N × Fin N) O) = (GlobalTheory.HighWt.genSub O N (f : MvPolynomial (Fin N × Fin N) O)).coeff m := by
  classical
  obtain ⟨n, r, p, hp, hY⟩ := expr_ldu (O := O) (N := N) (ν := ν)
  let D := ∑ a, ν a
  let Cm : (Fin N × Fin N →₀ ℕ) → (dualWeyl O N N ν →ₗ[O] MvPolynomial (Fin N × Fin N) O) := fun m =>
    { toFun := fun f => (GlobalTheory.HighWt.genSub O N (f : MvPolynomial (Fin N × Fin N) O)).coeff m
      map_add' := fun f g => by simp [GlobalTheory.HighWt.genSub]
      map_smul' := fun c f => by simp [GlobalTheory.HighWt.genSub] }
  let Φ : Module.End O (dualWeyl O N N ν) →ₗ[O] (dualWeyl O N N ν →ₗ[O] MvPolynomial (Fin N × Fin N) O) :=
    LinearMap.llcomp O _ _ _ (dualWeyl O N N ν).subtype
  let Asub : Submodule O (dualWeyl O N N ν →ₗ[O] MvPolynomial (Fin N × Fin N) O) :=
    (Subalgebra.toSubmodule (dwAlg O N ν)).map Φ
  let s0 : Finset (Fin N × Fin N →₀ ℕ) :=
    (Fintype.piFinset fun _ : Fin N × Fin N => Finset.range (D + 1)).map Finsupp.equivFunOnFinite.symm.toEmbedding
  let s := insert m s0
  have hs : ∀ m' : Fin N × Fin N →₀ ℕ, (∀ v, m' v ≤ D) → m' ∈ s := by
    intro m' h
    refine Finset.mem_insert_of_mem (Finset.mem_map.2 ⟨⇑m', Fintype.mem_piFinset.2 fun v => Finset.mem_range.2 (Nat.lt_succ_of_le (h v)), ?_⟩)
    simp
  have hsum : ∀ f : dualWeyl O N N ν, rowSubst O N _ (lowGen O N * diagGen O N * upGen O N) (f : MvPolynomial (Fin N × Fin N) O) =
      ∑ m' ∈ s, lduHom O N (monomial m' 1) •
        MvPolynomial.map (algebraMap O (MvPolynomial (Fin N × Fin N) O)) (Cm m' f) := by
    intro f
    rw [rowSubst_eq_sum_genSub_of_parts]
    refine Finset.sum_subset (fun m' hm' => hs m' (genSub_coeff_le_of_parts O N D _ (totalDegree_le_of_mem_of_parts O N ν _ f.2) m'
      (MvPolynomial.mem_support_iff.1 hm'))) (fun m' _ hm' => ?_) |>.trans (Finset.sum_congr rfl fun m' _ => ?_)
    · simp [Cm, MvPolynomial.notMem_support_iff.1 hm']
    · simp only [Cm, LinearMap.coe_mk, AddHom.coe_mk, lduHom, aeval_monomial, map_one, one_mul]
      rfl
  have hcoef : ∀ k : Fin N × Fin N →₀ ℕ, ∑ m' ∈ s, (lduHom O N (monomial m' 1)).coeff k • Cm m' =
      ∑ i, (r i).coeff k • Φ (p i) := by
    intro k
    apply LinearMap.ext
    intro f
    apply MvPolynomial.ext
    intro j
    have key : ∀ (t q : MvPolynomial (Fin N × Fin N) O),
        ((t • MvPolynomial.map (algebraMap O (MvPolynomial (Fin N × Fin N) O)) q).coeff j).coeff k = t.coeff k * q.coeff j := by
      intro t q
      rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_map, MvPolynomial.algebraMap_eq, smul_eq_mul, mul_comm,
        MvPolynomial.coeff_C_mul, mul_comm]
    have h := congrArg (fun q : MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O) => (q.coeff j).coeff k)
      ((hsum f).symm.trans (hY f))
    simp only [MvPolynomial.coeff_sum, key] at h
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul]
    simpa [Φ] using h
  have hzero := lduHom_pure_of_parts O N _ s (fun m' => Asub.mkQ (Cm m')) (fun k => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_smul, ← map_sum]
    rw [hcoef k, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (hp i))) m (Finset.mem_insert_self _ _)
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hzero
  obtain ⟨q, hq, hqe⟩ := Submodule.mem_map.1 hzero
  exact ⟨q, hq, fun f => congrArg (fun φ => φ f) hqe⟩

end GlobalTheory.GenCoef

namespace GlobalTheory.GenCoef

open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD GlobalTheory.ExpFrame

def atFactorHom (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ) (τ : ι) :
    Module.End O (dualWeyl O N N (res N (lam τ))) →ₐ[O] Module.End O (NablaT O N lam) where
  toFun p := atFactor τ p
  map_one' := by
    unfold atFactor
    rw [Module.End.one_eq_id, Function.update_eq_self]
    exact PiTensorProduct.map_id
  map_mul' p q := by
    unfold atFactor
    rw [← PiTensorProduct.map_mul]
    congr 1
    funext i
    by_cases h : i = τ
    · subst h; simp
    · simp [Function.update_of_ne h]; rfl
  map_zero' := by
    unfold atFactor
    have := PiTensorProduct.map_update_smul (R := O)
      (fun i : ι => (LinearMap.id : Module.End O (dualWeyl O N N (res N (lam i))))) τ (0 : O) 0
    simpa using this
  map_add' p q := by
    unfold atFactor
    exact PiTensorProduct.map_update_add (fun i : ι => (LinearMap.id : Module.End O (dualWeyl O N N (res N (lam i))))) τ p q
  commutes' c := by
    show atFactor τ _ = _
    unfold atFactor
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, PiTensorProduct.map_update_smul,
      Module.End.one_eq_id, Function.update_eq_self, PiTensorProduct.map_id, Module.End.one_eq_id]

theorem atFactor_mem_alg (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ) (τ : ι)
    (p : Module.End O (dualWeyl O N N (res N (lam τ)))) (hp : p ∈ dwAlg O N (res N (lam τ))) :
    atFactor τ p ∈ alg O N lam := by
  have hle : dwAlg O N (res N (lam τ)) ≤ (alg O N lam).comap (atFactorHom O N lam τ) := by
    refine Algebra.adjoin_le ?_
    rintro _ (⟨g, rfl⟩ | ⟨w, rfl⟩)
    · show atFactor τ _ ∈ alg O N lam
      have : atFactor τ (Formalism.UG.dualWeylRep O N N (res N (lam τ)) g) = grp O N lam (Function.update 1 τ g) := by
        show PiTensorProduct.map _ = PiTensorProduct.map _
        congr 1
        funext i
        by_cases h : i = τ
        · subst h; simp
        · simp [Function.update_of_ne h]; rfl
      rw [this]
      exact Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩)
    · show atFactor τ _ ∈ alg O N lam
      have hP : IsProj O N lam τ w (atFactor τ (rowProj O N (res N (lam τ)) w)) := by
        intro x y hy
        unfold atFactor
        rw [PiTensorProduct.map_tprod]
        congr 1
        funext σ
        by_cases h : σ = τ
        · subst h
          simp only [Function.update_self, LinearMap.restrict_apply, rowProj]
          exact Subtype.ext hy.symm
        · simp [Function.update_of_ne h]
      exact Algebra.subset_adjoin (Or.inr ⟨τ, w, hP⟩)
  exact hle hp

end GlobalTheory.GenCoef

namespace GlobalTheory.HighWt

open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD GlobalTheory.ExpFrame

theorem coefIn_of_domain : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (lam : ι → ℕ → ℕ), CoefIn O N lam := by
  intro O _ _ _ N ι _ _ lam τ m
  obtain ⟨p, hp, hpf⟩ := GlobalTheory.GenCoef.coef_mem O N (res N (lam τ)) m
  refine ⟨⟨_, GlobalTheory.GenCoef.atFactor_mem_alg O N lam τ p hp⟩, ?_⟩
  intro x y hy
  show atFactor τ p (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ y)
  unfold atFactor
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext σ
  by_cases h : σ = τ
  · subst h
    simp only [Function.update_self]
    exact Subtype.ext ((hpf _).trans hy.symm)
  · simp [Function.update_of_ne h]

end GlobalTheory.HighWt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericRowCoefMemCoefAlgebraOfDomainStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericRowCoef_mem_coefAlgebra_of_domain : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ), GlobalTheory.HighWt.CoefIn O N lam := by
  first | exact @GlobalTheory.HighWt.coefIn_of_domain | exact GlobalTheory.HighWt.coefIn_of_domain | (intros; apply GlobalTheory.HighWt.coefIn_of_domain <;> assumption)
end
