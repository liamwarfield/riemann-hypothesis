module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Formalism.LocalToGlobal.Columns.ColFormsLemmas
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ClassesDoubleCosets
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimesAPIntervalOfPrimesRel
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjOnInterQuadraticKernelsOfTraceEq
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedIntertwinerDecompOfQuadraticKernelStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationOperatorsActionOnRowWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationOperatorsActionOnRowWeight
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem rowE_apply_eq_sum (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) R) :
    rowE R r n a b f = ∑ s : Fin n, X (a, s) * pderiv (b, s) f := by
  simp [rowE, LinearMap.sum_apply]

theorem weight_rowW_eq_sum {r n : ℕ} (d : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowW r n) d a = ∑ s : Fin n, d (a, s) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply, Pi.smul_apply, rowW, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp

theorem weight_rowW_single {r n : ℕ} (v : Fin r × Fin n) :
    Finsupp.weight (rowW r n) (Finsupp.single v 1) = Pi.single v.1 1 := by
  simp [Finsupp.weight_apply, rowW]

theorem X_mul_monomial_pderiv_term {R : Type} [CommRing R] {r n : ℕ} (a b : Fin r) (s : Fin n)
    (d : Fin r × Fin n →₀ ℕ) (c : R) :
    X (a, s) * pderiv (b, s) (monomial d c) =
      monomial (Finsupp.single (a, s) 1 + (d - Finsupp.single (b, s) 1)) (c * (d (b, s) : R)) := by
  rw [pderiv_monomial, X, monomial_mul, one_mul]

end GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem rowE_diag_monomial {R : Type} [CommRing R] {r n : ℕ} (a : Fin r) (μ : Fin r → ℕ)
    (d : Fin r × Fin n →₀ ℕ) (c : R) (hd : Finsupp.weight (rowW r n) d = μ) :
    rowE R r n a a (monomial d c) = (μ a : R) • monomial d c := by
  rw [rowE_apply_eq_sum]
  have hterm : ∀ s : Fin n, X (a, s) * pderiv (a, s) (monomial d c) = monomial d (c * (d (a, s) : R)) := by
    intro s
    rw [X_mul_monomial_pderiv_term]
    by_cases h : d (a, s) = 0
    · simp [h]
    · rw [add_comm, tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h))]
  simp_rw [hterm]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, ← Finset.mul_sum, smul_monomial, smul_eq_mul, mul_comm]
  congr 2
  rw [← hd, weight_rowW_eq_sum]
  push_cast
  rfl

theorem rowE_monomial_eq_zero {R : Type} [CommRing R] {r n : ℕ} (a b : Fin r) (μ : Fin r → ℕ)
    (d : Fin r × Fin n →₀ ℕ) (c : R) (hd : Finsupp.weight (rowW r n) d = μ) (hb : μ b = 0) :
    rowE R r n a b (monomial d c) = 0 := by
  rw [rowE_apply_eq_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  have h0 : d (b, s) = 0 := by
    have h1 : ∑ t : Fin n, d (b, t) = 0 := by rw [← weight_rowW_eq_sum, hd, hb]
    exact (Finset.sum_eq_zero_iff.mp h1) s (Finset.mem_univ _)
  rw [X_mul_monomial_pderiv_term, h0]
  simp

theorem rowE_monomial_weight {R : Type} [CommRing R] {r n : ℕ} (a b : Fin r) (μ μ' : Fin r → ℕ)
    (d : Fin r × Fin n →₀ ℕ) (c : R) (hd : Finsupp.weight (rowW r n) d = μ)
    (hμ : μ' + Pi.single b 1 = μ + Pi.single a 1) :
    IsWeightedHomogeneous (rowW r n) (rowE R r n a b (monomial d c)) μ' := by
  rw [rowE_apply_eq_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun s _ => ?_
  rw [X_mul_monomial_pderiv_term]
  by_cases h : d (b, s) = 0
  · rw [h]; simp only [Nat.cast_zero, mul_zero, map_zero]
    exact isWeightedHomogeneous_zero R _ _
  · refine isWeightedHomogeneous_monomial _ _ _ ?_
    have hle : Finsupp.single (b, s) 1 ≤ d := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h)
    have hsplit : Finsupp.weight (rowW r n) (d - Finsupp.single (b, s) 1) + Pi.single b 1 = μ := by
      rw [← weight_rowW_single (b, s), ← map_add (f := _), tsub_add_cancel_of_le hle, hd]
    rw [map_add (f := _), weight_rowW_single]
    apply add_right_cancel (b := Pi.single b 1)
    rw [hμ, ← hsplit]
    simp only
    abel

theorem rowE_rowWeight : ∀ (R : Type) [CommRing R] (r n : ℕ) (μ : Fin r → ℕ) (f : MvPolynomial (Fin r × Fin n) R),
    IsWeightedHomogeneous (rowW r n) f μ → (∀ a, rowE R r n a a f = (μ a : R) • f) ∧
      ∀ a b, a ≠ b → (μ b = 0 → rowE R r n a b f = 0) ∧
        ∀ μ' : Fin r → ℕ, μ' + Pi.single b 1 = μ + Pi.single a 1 →
          IsWeightedHomogeneous (rowW r n) (rowE R r n a b f) μ' := by
  intro R _ r n μ f hf
  have hmon : ∀ d ∈ f.support, Finsupp.weight (rowW r n) d = μ := fun d hd => hf (mem_support_iff.mp hd)
  refine ⟨fun a => ?_, fun a b _ => ⟨fun hb => ?_, fun μ' hμ => ?_⟩⟩
  · conv_lhs => rw [f.as_sum]
    conv_rhs => rw [f.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun d hd => rowE_diag_monomial a μ d _ (hmon d hd)
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [f.as_sum, map_sum]
    exact Finset.sum_eq_zero fun d hd => rowE_monomial_eq_zero a b μ d _ (hmon d hd) hb
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [f.as_sum, map_sum]
    exact IsWeightedHomogeneous.sum _ _ _ fun d hd => rowE_monomial_weight a b μ μ' d _ (hmon d hd) hμ

end GlobalTheory.Alc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationOperatorsActionOnRowWeightStatement
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowPolarizationOperators_action_on_rowWeight : ∀ (R : Type) [CommRing R] (r n : ℕ) (μ : Fin r → ℕ) (f : MvPolynomial (Fin r × Fin n) R), IsWeightedHomogeneous (rowW r n) f μ → (∀ a, rowE R r n a a f = (μ a : R) • f) ∧ ∀ a b, a ≠ b → (μ b = 0 → rowE R r n a b f = 0) ∧ ∀ μ' : Fin r → ℕ, μ' + Pi.single b 1 = μ + Pi.single a 1 → IsWeightedHomogeneous (rowW r n) (rowE R r n a b f) μ' := by
  first | exact @GlobalTheory.Alc.rowE_rowWeight | exact GlobalTheory.Alc.rowE_rowWeight | (intros; apply GlobalTheory.Alc.rowE_rowWeight <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationOperatorsRelationsDivPowBaseChang
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationOperatorsRelationsDivPowBaseChang
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section

namespace GlobalTheory.Alc

theorem rowE_apply (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r) (P : MvPolynomial (Fin r × Fin n) R) :
    rowE R r n a b P = ∑ s : Fin n, X (a, s) * pderiv (b, s) P := by
  simp [rowE, LinearMap.sum_apply]

theorem rowE_X (R : Type) [CommRing R] (r n : ℕ) (a b c : Fin r) (t : Fin n) :
    rowE R r n a b (X (c, t)) = if b = c then X (a, t) else 0 := by
  rw [rowE_apply]
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single t]
    · simp
    · intro s _ hs
      rw [pderiv_X_of_ne (by simp [Ne.symm hs])]; simp
    · simp
  · refine Finset.sum_eq_zero fun s _ => ?_
    rw [pderiv_X_of_ne (by simp [Ne.symm h])]; simp

theorem rowE_mul (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r) (P Q : MvPolynomial (Fin r × Fin n) R) :
    rowE R r n a b (P * Q) = rowE R r n a b P * Q + P * rowE R r n a b Q := by
  simp only [rowE_apply, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Derivation.leibniz, smul_eq_mul]; ring

theorem rowE_C (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r) (x : R) :
    rowE R r n a b (C x) = 0 := by
  simp [rowE_apply]

theorem glRel_rowE (R : Type) [CommRing R] (r n : ℕ) : GlRel (rowE R r n) := by
  intro a b c d
  refine LinearMap.ext fun P => ?_
  induction P using MvPolynomial.induction_on with
  | C x => split_ifs <;> simp [rowE_C]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    obtain ⟨e, t⟩ := v
    have hX : (rowE R r n a b * rowE R r n c d - rowE R r n c d * rowE R r n a b) (X (e, t)) =
        ((if b = c then rowE R r n a d else 0) - (if d = a then rowE R r n c b else 0)) (X (e, t)) := by
      simp only [LinearMap.sub_apply, Module.End.mul_apply, rowE_X]
      split_ifs <;> simp_all [rowE_X]
    have hL : ∀ P Q, (rowE R r n a b * rowE R r n c d - rowE R r n c d * rowE R r n a b) (P * Q) =
        (rowE R r n a b * rowE R r n c d - rowE R r n c d * rowE R r n a b) P * Q +
          P * (rowE R r n a b * rowE R r n c d - rowE R r n c d * rowE R r n a b) Q := by
      intro P Q
      simp only [LinearMap.sub_apply, Module.End.mul_apply, rowE_mul, map_add (f := _)]; ring
    have hR : ∀ P Q, ((if b = c then rowE R r n a d else 0) - (if d = a then rowE R r n c b else 0)) (P * Q) =
        ((if b = c then rowE R r n a d else 0) - (if d = a then rowE R r n c b else 0)) P * Q +
          P * ((if b = c then rowE R r n a d else 0) - (if d = a then rowE R r n c b else 0)) Q := by
      intro P Q
      split_ifs <;> simp [rowE_mul] <;> ring
    rw [hL, hR, hp, hX]

theorem rowE_eq_rowDiv (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r) (P : MvPolynomial (Fin r × Fin n) R) :
    rowE R r n a b P = rowDiv R a b 1 P ∧ rowDiv R a b 0 P = P := by
  induction P using MvPolynomial.induction_on with
  | C x => simp [rowE_C, rowDiv, rowGen, Polynomial.algebraMap_apply, Polynomial.coeff_C]
  | add p q hp hq =>
    simp only [rowDiv, map_add (f := _), Polynomial.coeff_add] at *
    exact ⟨by rw [hp.1, hq.1], by rw [hp.2, hq.2]⟩
  | mul_X p v hp =>
    obtain ⟨e, t⟩ := v
    simp only [rowDiv, map_mul] at *
    have h0 : (rowGen R a b (X (e, t) : MvPolynomial (Fin r × Fin n) R)).coeff 0 = X (e, t) := by
      simp only [rowGen, aeval_X]; split_ifs <;> simp
    have h1 : (rowGen R a b (X (e, t) : MvPolynomial (Fin r × Fin n) R)).coeff 1 =
        if b = e then X (a, t) else 0 := by
      simp only [rowGen, aeval_X]
      by_cases h : e = b
      · simp [h, Polynomial.coeff_C]
      · simp [h, Ne.symm h, Polynomial.coeff_C]
    refine ⟨?_, by rw [Polynomial.mul_coeff_zero, hp.2, h0]⟩
    rw [rowE_mul, rowE_X, Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ]
    simp [hp.1, hp.2, h0, h1, add_comm]

theorem map_rowE {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (r n : ℕ) (a b : Fin r)
    (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (rowE R r n a b f) = rowE S r n a b (map φ f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rowE_apply, map_sum, map_mul, map_X, pderiv_map]

theorem map_rowE_pow {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (r n k : ℕ) (a b : Fin r)
    (f : MvPolynomial (Fin r × Fin n) R) :
    map φ ((rowE R r n ^ k) a b f) = (rowE S r n ^ k) a b (map φ f) := by
  induction k generalizing a b f with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    split_ifs <;> simp
  | succ k ih =>
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [pow_succ, Matrix.mul_apply, LinearMap.sum_apply, Module.End.mul_apply, map_sum, ih, map_rowE]

theorem map_gel {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (r n k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (gel R r n k f) = gel S r n k (map φ f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gel, Matrix.trace, Matrix.diag, LinearMap.sum_apply, map_sum, map_rowE_pow]

theorem rowOperators_main : ∀ (R : Type) [CommRing R] (r n : ℕ), GlRel (rowE R r n) ∧
    (∀ a b f, rowE R r n a b f = rowDiv R a b 1 f) ∧
    ∀ (S : Type) [CommRing S] (φ : R →+* S) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R),
      map φ (gel R r n k f) = gel S r n k (map φ f) := by
  intro R _ r n
  exact ⟨glRel_rowE R r n, fun a b f => (rowE_eq_rowDiv R r n a b f).1,
    fun S _ φ k f => map_gel φ r n k f⟩

end GlobalTheory.Alc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationOperatorsRelationsDivPowBaseChangStatement
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange : ∀ (R : Type) [CommRing R] (r n : ℕ), GlRel (rowE R r n) ∧ (∀ a b f, rowE R r n a b f = rowDiv R a b 1 f) ∧ ∀ (S : Type) [CommRing S] (φ : R →+* S) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R), map φ (gel R r n k f) = gel S r n k (map φ f) := by
  first | exact @GlobalTheory.Alc.rowOperators_main | exact GlobalTheory.Alc.rowOperators_main | (intros; apply GlobalTheory.Alc.rowOperators_main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowDegDominatedOfMemDualWeylModule
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowDegDominatedOfMemDualWeylModule
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem rowDeg_dominated_of_mem_dualWeyl (k : Type) [Field k] (N : ℕ) (ν : Fin N → ℕ) :
    ∀ f ∈ dualWeyl k N N ν, ∀ m ∈ f.support,
      (∀ j : ℕ, (∑ a : Fin N with a.val < j, rowDeg m a) ≤ ∑ a : Fin N with a.val < j, ν a) ∧
      ∑ a, rowDeg m a = ∑ a, ν a := by
  classical
  intro f hf
  rw [standardMonomialSpanDomain k N N ν] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hx
    intro m hm
    have h := bidetDominance k N N K sz hsz I m hm
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

end GlobalTheory.Alc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowDegDominatedOfMemDualWeylModuleStatement
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowDeg_dominated_of_mem_dualWeylModule : ∀ (k : Type) [Field k] (N : ℕ) (ν : Fin N → ℕ), ∀ f ∈ dualWeyl k N N ν, ∀ m ∈ f.support, (∀ j : ℕ, (∑ a : Fin N with a.val < j, rowDeg m a) ≤ ∑ a : Fin N with a.val < j, ν a) ∧ ∑ a, rowDeg m a = ∑ a, ν a := by
  first | exact @GlobalTheory.Alc.rowDeg_dominated_of_mem_dualWeyl | exact GlobalTheory.Alc.rowDeg_dominated_of_mem_dualWeyl | (intros; apply GlobalTheory.Alc.rowDeg_dominated_of_mem_dualWeyl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LiesOverSpanOfNatCastMemHeightOne
open NumberField IsDedekindDomain Formalism.L2.Col

namespace GlobalTheory

theorem liesOver_span_of_natCast_mem_heightOne {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (P : HeightOneSpectrum (𝓞 E)) (h : ((p : ℕ) : 𝓞 E) ∈ P.asIdeal) :
    P.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := by
    have : Fact p.Prime := ⟨hp⟩
    exact Int.ideal_span_isMaximal_of_prime p
  refine ⟨hmax.eq_of_le (Ideal.comap_ne_top _ P.isPrime.ne_top) ?_⟩
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
  exact h

theorem exists_comap_eq_or_eq_conj :
    ∀ (X : Fields), X.AbelianUnramifiedExtensionConditions → ∀ (p : ℕ), p.Prime → ∀ (w : HeightOneSpectrum (𝓞 X.K)) (P : HeightOneSpectrum (𝓞 X.E)),
      ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal → ((p : ℕ) : 𝓞 X.E) ∈ P.asIdeal → ∃ τ : X.Tau, SeesP w τ P ∨ SeesPbar w τ P := by
  intro X hX p hp w P hw hP
  have := hX.galE
  obtain ⟨τ₀⟩ : Nonempty X.Tau := Fintype.card_pos_iff.1 hX.ok.f_pos
  have h0 : ((p : ℕ) : 𝓞 X.E) ∈ (pullW τ₀ w).asIdeal := by
    change ((p : ℕ) : 𝓞 X.E) ∈ w.asIdeal.comap (X.embO τ₀)
    rw [Ideal.mem_comap, map_natCast]
    exact hw
  obtain ⟨g, hg⟩ := Ideal.exists_comap_galRestrict_eq ℤ ℚ X.E (𝓞 X.E) (p := Ideal.span {(p : ℤ)})
    (P₁ := (pullW τ₀ w).asIdeal) (P₂ := P.asIdeal)
    ⟨(pullW τ₀ w).isPrime, liesOver_span_of_natCast_mem_heightOne hp _ h0⟩
    ⟨P.isPrime, liesOver_span_of_natCast_mem_heightOne hp _ hP⟩
  have key : ∀ x : 𝓞 X.E, x ∈ P.asIdeal ↔ X.embO τ₀ (galRestrict ℤ ℚ X.E (𝓞 X.E) g x) ∈ w.asIdeal := by
    intro x
    rw [← hg]
    rfl
  have hc : ∀ x : 𝓞 X.E, ((X.embO τ₀ (galRestrict ℤ ℚ X.E (𝓞 X.E) g x) : 𝓞 X.K) : X.K) = X.emb τ₀ (g (x : X.E)) := by
    intro x
    exact congrArg (X.emb τ₀) (algebraMap_galRestrict_apply ℤ g x)
  obtain ⟨τ, hτ | hτ⟩ := hX.ok.emb_all ((X.emb τ₀).comp (g : X.E →+* X.E))
  · refine ⟨τ, Or.inl ?_⟩
    apply HeightOneSpectrum.ext
    ext x
    rw [key]
    have : X.embO τ₀ (galRestrict ℤ ℚ X.E (𝓞 X.E) g x) = X.embO τ x := by
      apply RingOfIntegers.ext
      rw [hc]
      exact RingHom.congr_fun hτ (x : X.E)
    rw [this]
    rfl
  · refine ⟨τ, Or.inr ?_⟩
    apply HeightOneSpectrum.ext
    ext x
    rw [mem_conjP, key]
    have : X.embO τ₀ (galRestrict ℤ ℚ X.E (𝓞 X.E) g (cO X.E x)) = X.embO τ (cO X.E (cO X.E x)) := by
      apply RingOfIntegers.ext
      rw [hc]
      exact RingHom.congr_fun hτ ((cO X.E x : 𝓞 X.E) : X.E)
    rw [this, cO_cO]
    rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GlMatrixUnitPowCommutatorAndTraceCentral
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CommPowEntry
namespace GlobalTheory.CommutatorPowerEntry

open Finset

theorem comm_pow_entry (A : Type) [Ring A] (N : ℕ) (E : Matrix (Fin N) (Fin N) A)
    (h : GlobalTheory.Alc.GlRel E) (k : ℕ) :
    ∀ (a b c d : Fin N), E a b * (E ^ k) c d - (E ^ k) c d * E a b =
      (if b = c then (E ^ k) a d else (0 : A)) - if d = a then (E ^ k) c b else (0 : A) := by
  induction k with
  | zero =>
    intro a b c d
    simp only [pow_zero, Matrix.one_apply]
    by_cases hcd : c = d <;> by_cases hbc : b = c <;> by_cases hda : d = a <;>
      simp_all [eq_comm]
  | succ k ih =>
    intro a b c d
    have h' : ∀ c d : Fin N, E a b * E c d - E c d * E a b =
        (if b = c then E a d else 0) - (if d = a then E c b else 0) := h a b
    have key : ∀ x y : A, E a b * (x * y) - (x * y) * E a b =
        (E a b * x - x * E a b) * y + x * (E a b * y - y * E a b) := by
      intro x y; noncomm_ring
    simp only [pow_succ, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, key, ih, h']
    simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hbc : b = c <;> by_cases hda : d = a <;> simp only [hbc, hda, if_true, if_false,
      Finset.sum_const_zero] <;> abel

theorem comm_trace_pow (A : Type) [Ring A] (N : ℕ) (E : Matrix (Fin N) (Fin N) A)
    (h : GlobalTheory.Alc.GlRel E) (k : ℕ) (a b : Fin N) :
    E a b * Matrix.trace (E ^ k) = Matrix.trace (E ^ k) * E a b := by
  rw [← sub_eq_zero]
  simp only [Matrix.trace, Matrix.diag, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
    comm_pow_entry A N E h k]
  simp [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem main : ∀ (A : Type) [inst : Ring A] (N : ℕ) (E : Matrix (Fin N) (Fin N) A), GlobalTheory.Alc.GlRel E → ∀ (k : ℕ), (∀ (a b c d : Fin N), E a b * (E ^ k) c d - (E ^ k) c d * E a b = (if b = c then (E ^ k) a d else (0 : A)) - if d = a then (E ^ k) c b else (0 : A)) ∧ ∀ (a b : Fin N), E a b * Matrix.trace (E ^ k) = Matrix.trace (E ^ k) * E a b := by
  intro A _ N E h k
  exact ⟨comm_pow_entry A N E h k, comm_trace_pow A N E h k⟩

end GlobalTheory.CommutatorPowerEntry
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GlMatrixUnitPowCommutatorAndTraceCentral
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem glRel_pow_comm : ∀ (A : Type) [Ring A] (N : ℕ) (E : Matrix (Fin N) (Fin N) A), GlRel E → ∀ k : ℕ, (∀ a b c d, E a b * (E ^ k) c d - (E ^ k) c d * E a b = (if b = c then (E ^ k) a d else 0) - (if d = a then (E ^ k) c b else 0)) ∧ ∀ a b, E a b * (E ^ k).trace = (E ^ k).trace * E a b := by
  first
  | exact @_root_.GlobalTheory.CommutatorPowerEntry.main
  | exact _root_.GlobalTheory.CommutatorPowerEntry.main
  | (apply _root_.GlobalTheory.CommutatorPowerEntry.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommutatorPowerEntry.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommutatorPowerEntry.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommutatorPowerEntry.main ..)

end GlobalTheory.Alc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GlMatrixUnitPowCommutatorAndTraceCentralStatement
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glMatrixUnit_pow_commutator_and_trace_central : ∀ (A : Type) [Ring A] (N : ℕ) (E : Matrix (Fin N) (Fin N) A), GlRel E → ∀ k : ℕ, (∀ a b c d, E a b * (E ^ k) c d - (E ^ k) c d * E a b = (if b = c then (E ^ k) a d else 0) - (if d = a then (E ^ k) c b else 0)) ∧ ∀ a b, E a b * (E ^ k).trace = (E ^ k).trace * E a b := by
  first | exact @GlobalTheory.Alc.glRel_pow_comm | exact GlobalTheory.Alc.glRel_pow_comm | (intros; apply GlobalTheory.Alc.glRel_pow_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CosetGroupEquiv
noncomputable section

namespace GlobalTheory.Proof.CosetGroupEquiv

open NumberField IsDedekindDomain Formalism.UG Formalism.BasicNotions Formalism.L2.Herm
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke

section Abstract

variable {G : Type} [Group G]

def cosetGrpEquiv (Γ K : Subgroup G) (y : G) : CosetGroupMembership.cosetGrp Γ K y ≃ stabAt Γ K y where
  toFun x := ⟨⟨x.1, ((CosetGroupMembership.mem_cosetGrp Γ K y x.1).1 x.2).1⟩, ((CosetGroupMembership.mem_cosetGrp Γ K y x.1).1 x.2).2⟩
  invFun x := ⟨x.1.1, (CosetGroupMembership.mem_cosetGrp Γ K y x.1.1).2 ⟨x.1.2, x.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_cosetGrp (Γ K : Subgroup G) (y : G) :
    Nat.card (CosetGroupMembership.cosetGrp Γ K y) = Nat.card (stabAt Γ K y) :=
  Nat.card_congr (cosetGrpEquiv Γ K y)

theorem sum_clause_iff (Γ K : Subgroup G) (m : ℝ) :
    (∀ (ι : Type) [Fintype ι] (y : ι → G),
      Function.Bijective (fun i => (DoubleCoset.mk Γ K (y i) : ClassSet Γ K)) →
      ∑ i, ((Nat.card (CosetGroupMembership.cosetGrp Γ K (y i)) : ℕ) : ℝ)⁻¹ = m) ↔
    (∀ [Fintype (ClassSet Γ K)] (s : ClassSet Γ K → G), (∀ c, DoubleCoset.mk Γ K (s c) = c) →
      ∑ c, ((Nat.card (stabAt Γ K (s c)) : ℕ) : ℝ)⁻¹ = m) := by
  constructor
  · intro h _ s hs
    have hb : Function.Bijective (fun c => (DoubleCoset.mk Γ K (s c) : ClassSet Γ K)) := by
      have : (fun c => (DoubleCoset.mk Γ K (s c) : ClassSet Γ K)) = id := funext hs
      rw [this]
      exact Function.bijective_id
    rw [← h _ s hb]
    simp only [card_cosetGrp]
  · intro h ι _ y hy
    let e : ι ≃ ClassSet Γ K := Equiv.ofBijective _ hy
    letI : Fintype (ClassSet Γ K) := Fintype.ofEquiv ι e
    have hs : ∀ c : ClassSet Γ K, DoubleCoset.mk Γ K (y (e.symm c)) = c := fun c => e.apply_symm_apply c
    rw [← h (fun c => y (e.symm c)) hs, ← e.symm.sum_comp]
    simp only [card_cosetGrp]

theorem cosetSum_iff (Γ K : Subgroup G) (m : ℝ) : CosetGroupMembership.CosetSum Γ K m ↔ ClassesDoubleCosets.CosetMass Γ K m :=
  and_congr Iff.rfl (and_congr (forall_congr' fun y => (cosetGrpEquiv Γ K y).finite_iff)
    (sum_clause_iff Γ K m))

end Abstract

section Obj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem stabHat_eq (hc : CMData F E) (S : HSpace E) (N : Submodule (𝓞 E) S.V) :
    CosetGroupMembership.stabHat hc S N = ClassesDoubleCosets.stabHat hc S N := rfl

theorem stabHat0_eq {R : Ranks} (sp : Spaces R F E) (N : Submodule (𝓞 E) (sp.X 0).V) :
    CosetGroupMembership.stabHat0 sp N = (levelAfL sp.cm.sig sp.gram0 (sp.crdLat0 N)).subgroupOf
      (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)) := by
  ext x
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

def InCoords (hc : CMData F E) {k : ℕ} (J : Matrix (Fin k) (Fin k) E) (Λ : Submodule (𝓞 E) (Fin k → E))
    (m : ℝ) : Prop :=
  CosetGroupMembership.CosetSum ((ratPts hc.sig J (Af F)).subgroupOf (UPts hc.sig J (Af F)))
    ((stabGL (hatL (F := F) Λ)).subgroupOf (UPts hc.sig J (Af F))) m

theorem inCoords_cast (hc : CMData F E) (S : HSpace E) {k : ℕ} (h : S.rank = k) (N : Submodule (𝓞 E) S.V)
    (m : ℝ) :
    InCoords hc S.gram (crdLat S N) m ↔
    InCoords hc (S.gram.reindex (finCongr h) (finCongr h))
      (N.map (((S.frame.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr h).symm) :
        S.V ≃ₗ[E] (Fin k → E)) : S.V →ₗ[E] (Fin k → E)).restrictScalars (𝓞 E))) m := by
  subst h
  rfl

theorem general_clause_iff {R : Ranks} (sp : Spaces R F E) (N : Submodule (𝓞 E) (sp.X 0).V) (m : ℝ) :
    CosetGroupMembership.CosetSum (UFin sp.cm (sp.X 0)) (CosetGroupMembership.stabHat sp.cm (sp.X 0) N) m ↔
    CosetGroupMembership.CosetSum (CosetGroupMembership.rat0 sp) (CosetGroupMembership.stabHat0 sp N) m :=
  inCoords_cast sp.cm (sp.X 0) sp.rank0 N m

end Obj

theorem general_iff : CosetGroupMembership.GeneralForm ↔ ClassesDoubleCosets.General := by
  unfold CosetGroupMembership.GeneralForm ClassesDoubleCosets.General
  simp only [cosetSum_iff, stabHat_eq]

theorem column_iff (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    CosetGroupMembership.ColumnForm D ↔ ClassesDoubleCosets.DefiniteSpaceClassStatement D Lv u := by
  letI := D.host.cmStar
  unfold CosetGroupMembership.ColumnForm ClassesDoubleCosets.DefiniteSpaceClassStatement
  refine forall_congr' fun N => forall_congr' fun _ => forall_congr' fun _ => ?_
  rw [cosetSum_iff, stabHat0_eq]
  rfl

theorem column_of_general (h : CosetGroupMembership.GeneralForm) (D : D7) : CosetGroupMembership.ColumnForm D := by
  letI := D.host.cmStar
  intro N hN hU
  exact (general_clause_iff D.sp N _).1
    (h D.host.F D.host.E D.sp.cm (D.sp.X 0) (D.sp.X_sig 0) (baseSpace_posDef D.R D.host.F D.sp) N hN hU)

theorem massAsCosetSum_iff : CosetGroupMembership.MassAsCosetSum ↔ ClassesDoubleCosets.ClassesAsDoubleCosets :=
  ⟨fun h => ⟨general_iff.1 h.1, fun D Lv u => (column_iff D Lv u).1 (h.2 D)⟩,
    fun h => ⟨general_iff.2 h.1, column_of_general (general_iff.2 h.1)⟩⟩

end GlobalTheory.Proof.CosetGroupEquiv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntertwinerZeroOfQuadraticTwists
open Formalism.MainNotions.N

namespace GlobalTheory

theorem trace_eq_of_agree_on_index_two_of_no_twisted_intertwiner : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (ρ₀ ρ ρ' : Γ →* GL (Fin n) k) (η₀ χ₁ χ₂ : Γ →* ℤˣ), (∀ g, η₀ g = 1 → ρ g = ρ₀ g) → (∀ g, η₀ g = 1 → ρ' g = ρ₀ g) → IsSSRep ρ → IsSSRep ρ' → (∀ c : Γ →* ℤˣ, (c = χ₁ ∨ c = χ₂ ∨ c = χ₁ * χ₂ ∨ c = χ₁ * η₀ ∨ c = χ₂ * η₀ ∨ c = χ₁ * χ₂ * η₀) → ∀ X : Matrix (Fin n) (Fin n) k, (∀ g, ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X = ((c g : ℤ) : k) • (X * ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) → X = 0) → (∀ g, χ₁ g = 1 → χ₂ g = 1 → ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) → ∀ g, ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace := by
  intro Γ k _ _ _ n ρ₀ ρ ρ' η₀ χ₁ χ₂ hρ hρ' hs hs' hno htr
  obtain ⟨P, hP⟩ := GlobalTheory.T.conj_on_inter_quadraticKernels_of_trace_eq Γ k n ρ ρ' χ₁ χ₂ hs hs' htr
  have hzero : ∀ c : Γ →* ℤˣ, (c = χ₁ ∨ c = χ₂ ∨ c = χ₁ * χ₂) →
      ∀ X : Matrix (Fin n) (Fin n) k,
      (∀ g ∈ (⊤ : Subgroup Γ), ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X =
        ((c g : ℤ) : k) • (X * ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) → X = 0 := by
    intro c hc X hX
    obtain ⟨A, B, hAB, hA, hB⟩ := GlobalTheory.T.twistedIntertwiner_decomp_of_quadraticKernel' Γ k n ρ₀ ρ₀ ⊤ c η₀ X (by
      intro g hg h
      have := hX g hg
      rwa [hρ g h, hρ' g h] at this)
    have hA0 : A = 0 := hno c (by tauto) A (fun g => hA g trivial)
    have hB0 : B = 0 := hno (c * η₀) (by rcases hc with rfl | rfl | rfl <;> simp) B
      (fun g => hB g trivial)
    rw [hAB, hA0, hB0, add_zero]
  obtain ⟨Y₁, Y₂, hY, hY₁, hY₂⟩ := GlobalTheory.T.twistedIntertwiner_decomp_of_quadraticKernel' Γ k n ρ' ρ χ₂.ker 1 χ₁
    (P : Matrix (Fin n) (Fin n) k) (by
      intro g hg h
      have h1 : ρ g * P = P * ρ' g := by rw [hP g h hg]; group
      have h2 := congrArg (fun x : GL (Fin n) k => (x : Matrix (Fin n) (Fin n) k)) h1
      simpa using h2)
  obtain ⟨A, B, hAB, hA, hB⟩ := GlobalTheory.T.twistedIntertwiner_decomp_of_quadraticKernel' Γ k n ρ' ρ ⊤ 1 χ₂ Y₁ (fun g _ h => hY₁ g h)
  obtain ⟨C, D, hCD, hC, hD⟩ := GlobalTheory.T.twistedIntertwiner_decomp_of_quadraticKernel' Γ k n ρ' ρ ⊤ (1 * χ₁) χ₂ Y₂ (fun g _ h => hY₂ g h)
  have hB0 : B = 0 := hzero _ (by simp) B hB
  have hC0 : C = 0 := hzero _ (by simp) C hC
  have hD0 : D = 0 := hzero _ (by simp) D hD
  have hPA : (P : Matrix (Fin n) (Fin n) k) = A := by
    rw [hY, hAB, hCD, hB0, hC0, hD0]; simp
  intro g
  have h1 : ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * (P : Matrix (Fin n) (Fin n) k) =
      (P : Matrix (Fin n) (Fin n) k) * ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    have := hA g trivial
    rw [← hPA] at this
    simpa using this
  have h2 : ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      (P : Matrix (Fin n) (Fin n) k) * ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *
        ((P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    rw [← h1, mul_assoc, Units.mul_inv, mul_one]
  rw [h2, Matrix.trace_mul_cycle, Units.inv_mul, one_mul]

end GlobalTheory
end
