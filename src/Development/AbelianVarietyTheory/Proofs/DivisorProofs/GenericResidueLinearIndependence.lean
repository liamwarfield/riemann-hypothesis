module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BertiniGeneralMembersNoDerivativeRelation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentKaehlerDOfAlgebraicIndependent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentKaehlerDOfAlgebraicIndependent
set_option autoImplicit false

open scoped TensorProduct
open KaehlerDifferential

namespace GlobalTheory.BertiniAlg

theorem linearIndependent_D_of_algebraicIndependent (k κ : Type) [Field k] [CharZero k] [Field κ]
    [Algebra k κ] [Algebra.EssFiniteType k κ] {σ : Type} (t : σ → κ)
    (ht : AlgebraicIndependent k t) :
    LinearIndependent κ (fun s => KaehlerDifferential.D k κ (t s)) := by
  let P := MvPolynomial σ k
  let φ : P →ₐ[k] κ := MvPolynomial.aeval t
  have hφ : Function.Injective φ := ht
  algebraize [φ.toRingHom]
  have : IsScalarTower k P κ := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  let K := FractionRing P
  have hinj : Function.Injective (algebraMap P κ) := hφ
  let : Algebra K κ := (IsFractionRing.lift (K := K) hinj).toAlgebra
  have : IsScalarTower P K κ := IsScalarTower.of_algebraMap_eq fun a =>
    (IsFractionRing.lift_algebraMap (K := K) hinj a).symm
  have : IsScalarTower k K κ := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k P K, ← IsScalarTower.algebraMap_apply P K κ,
      ← IsScalarTower.algebraMap_apply]
  have : Algebra.EssFiniteType K κ := .of_comp k K κ
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  have : Algebra.FormallySmooth K κ := Algebra.FormallySmooth.of_perfectField
  have : Algebra.FormallyEtale P K := .of_isLocalization (nonZeroDivisors P)
  have : Algebra.FormallySmooth P κ := .comp P K κ
  have hH : Subsingleton (Algebra.H1Cotangent P κ) := Algebra.FormallySmooth.subsingleton_h1Cotangent
  have hinjm : Function.Injective (mapBaseChange k P κ) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange k P κ x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  let b := (mvPolynomialBasis k σ).baseChange κ
  have h := b.linearIndependent.map' (mapBaseChange k P κ) (LinearMap.ker_eq_bot.2 hinjm)
  have hX (s : σ) : algebraMap P κ (MvPolynomial.X s) = t s := MvPolynomial.aeval_X t s
  have e : (fun s => KaehlerDifferential.D k κ (t s)) = mapBaseChange k P κ ∘ b := by
    funext s
    simp only [Function.comp_apply, b, Module.Basis.baseChange_apply, mvPolynomialBasis_apply]
    erw [mapBaseChange_tmul, one_smul, map_D, hX]
  rw [e]
  exact h

end GlobalTheory.BertiniAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentKaehlerDOfAlgebraicIndependentStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_kaehlerD_of_algebraicIndependent : ∀ (k κ : Type) [Field k] [CharZero k] [Field κ] [Algebra k κ] [Algebra.EssFiniteType k κ] {σ : Type} (t : σ → κ), AlgebraicIndependent k t → LinearIndependent κ (fun s => KaehlerDifferential.D k κ (t s)) := by
  first | exact @GlobalTheory.BertiniAlg.linearIndependent_D_of_algebraicIndependent | exact GlobalTheory.BertiniAlg.linearIndependent_D_of_algebraicIndependent | (intros; apply GlobalTheory.BertiniAlg.linearIndependent_D_of_algebraicIndependent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BertiniGeneralMembersNoDerivativeRelation
namespace GlobalTheory.BertiniC


open KaehlerDifferential in
theorem false_of_dependent_derivatives {k A κ : Type} [Field k] [CharZero k] [CommRing A] [Algebra k A]
    [Field κ] [Algebra k κ] [Algebra A κ] [IsScalarTower k A κ] [Algebra.EssFiniteType k κ]
    (n : ℕ) (δ : Fin n → Derivation k A A) (ω : Fin n → KaehlerDifferential k A)
    (hω : ∀ a : A, KaehlerDifferential.D k A a = ∑ l, δ l a • ω l)
    {ι : Type} [Fintype ι] (f : ι → A) (M : ℕ) (J : Finset (Fin M)) (i₀ : Fin M) (p₀ : ι)
    (hi₀ : i₀ ∈ J) (t : Fin M × ι → κ) (ht : AlgebraicIndependent k t) (c : Fin M → κ)
    (r1 : ∀ i ∈ J, ∑ p, t (i, p) * algebraMap A κ (f p) = 0)
    (r2 : ∀ l, ∑ i ∈ J, c i * ∑ p, t (i, p) * algebraMap A κ (δ l (f p)) = 0)
    (r3 : c i₀ - 1 = 0) (s : κ) (r4s : s * algebraMap A κ (f p₀) - 1 = 0) : False := by
  have r4 : algebraMap A κ (f p₀) ≠ 0 := by
    intro h
    rw [h, mul_zero, zero_sub, neg_eq_zero] at r4s
    exact one_ne_zero r4s
  have hlin := GlobalTheory.T.linearIndependent_kaehlerD_of_algebraicIndependent k κ t ht
  set m : Fin n → KaehlerDifferential k κ := fun l => KaehlerDifferential.map k k A κ (ω l) with hm
  have hdψ : ∀ a : A, D k κ (algebraMap A κ a) = ∑ l, algebraMap A κ (δ l a) • m l := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← KaehlerDifferential.map_D k k A κ, hω a, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [LinearMap.map_smul, algebraMap_smul]
  have e1 : ∀ i ∈ J, ∑ p, algebraMap A κ (f p) • D k κ (t (i, p)) =
      - ∑ p, t (i, p) • D k κ (algebraMap A κ (f p)) := by
    intro i hi
    have h := congrArg (D k κ) (r1 i hi)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h
    simp only [Derivation.leibniz, Finset.sum_add_distrib] at h
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h
  have e2 : ∑ i ∈ J, c i • ∑ p, t (i, p) • D k κ (algebraMap A κ (f p)) = 0 := by
    have : ∑ i ∈ J, c i • ∑ p, t (i, p) • D k κ (algebraMap A κ (f p)) =
        ∑ l, (∑ i ∈ J, c i * ∑ p, t (i, p) * algebraMap A κ (δ l (f p))) • m l := by
      simp only [hdψ, Finset.smul_sum, Finset.sum_smul, Finset.mul_sum, smul_smul, mul_assoc]
      conv_rhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    rw [this]
    simp [r2]
  have key : ∑ x ∈ J ×ˢ (Finset.univ : Finset ι), (c x.1 * algebraMap A κ (f x.2)) • D k κ (t x) = 0 := by
    rw [Finset.sum_product]
    simp only [mul_smul, ← Finset.smul_sum]
    rw [Finset.sum_congr rfl (fun i hi => by rw [e1 i hi]), ]
    simp only [smul_neg, Finset.sum_neg_distrib, e2, neg_zero]
  have := linearIndependent_iff'.1 hlin _ _ key (i₀, p₀) (by simp [hi₀])
  rw [sub_eq_zero.1 r3, one_mul] at this
  exact r4 this

section Construction

variable {k A : Type} [Field k] [CommRing A] [Algebra k A] {n : ℕ}
  (δ : Fin n → Derivation k A A) {ι : Type} [Fintype ι] (f : ι → A) {M : ℕ}
  (J : Finset (Fin M)) (i₀ : Fin M) (p₀ : ι)

abbrev Var (M : ℕ) (ι : Type) := (Fin M × ι) ⊕ (Fin M ⊕ Unit)


open MvPolynomial in
noncomputable def relIdeal : Ideal (MvPolynomial (Var M ι) A) :=
  Ideal.span {x | (∃ i ∈ J, x = ∑ p, X (Sum.inl (i, p)) * C (f p)) ∨
    (∃ l, x = ∑ i ∈ J, X (Sum.inr (Sum.inl i)) * ∑ p, X (Sum.inl (i, p)) * C (δ l (f p))) ∨
    x = X (Sum.inr (Sum.inl i₀)) - 1 ∨ x = X (Sum.inr (Sum.inr ())) * C (f p₀) - 1}

end Construction


open MvPolynomial in
theorem no_dependence_of_general : ∀ (k A : Type) [Field k] [CharZero k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (n : ℕ) (δ : Fin n → Derivation k A A) (ω : Fin n → KaehlerDifferential k A), (∀ a : A, KaehlerDifferential.D k A a = ∑ l, δ l a • ω l) → ∀ {ι : Type} [Fintype ι] (f : ι → A) (M : ℕ) (J : Finset (Fin M)) (i₀ : Fin M) (p₀ : ι), i₀ ∈ J → ∃ Q : MvPolynomial (Fin M × ι) k, Q ≠ 0 ∧ ∀ u : Fin M × ι → k, MvPolynomial.eval u Q ≠ 0 → ∀ (K : Type) [Field K] [Algebra k K] (φ : A →ₐ[k] K) (c : Fin M → K), φ (f p₀) ≠ 0 → c i₀ = 1 → (∀ i ∈ J, φ (∑ p, u (i, p) • f p) = 0) → ¬ ∀ l, ∑ i ∈ J, c i * φ (δ l (∑ p, u (i, p) • f p)) = 0 := by
  intro k A _ _ _ _ _ n δ ω hω ι _ f M J i₀ p₀ hi₀
  classical
  set I := relIdeal δ f J i₀ p₀ with hIdef
  let T := MvPolynomial (Var M ι) A ⧸ I
  let gm : MvPolynomial (Fin M × ι) k →ₐ[k] T :=
    aeval (fun x => Ideal.Quotient.mk I (X (Sum.inl x)))
  have g1mem : ∀ i ∈ J, (∑ p, X (Sum.inl (i, p)) * C (f p) : MvPolynomial (Var M ι) A) ∈ I :=
    fun i hi => Ideal.subset_span (Or.inl ⟨i, hi, rfl⟩)
  have g2mem : ∀ l, (∑ i ∈ J, X (Sum.inr (Sum.inl i)) * ∑ p, X (Sum.inl (i, p)) * C (δ l (f p)) :
      MvPolynomial (Var M ι) A) ∈ I :=
    fun l => Ideal.subset_span (Or.inr (Or.inl ⟨l, rfl⟩))
  have g3mem : (X (Sum.inr (Sum.inl i₀)) - 1 : MvPolynomial (Var M ι) A) ∈ I :=
    Ideal.subset_span (Or.inr (Or.inr (Or.inl rfl)))
  have g4mem : (X (Sum.inr (Sum.inr ())) * C (f p₀) - 1 : MvPolynomial (Var M ι) A) ∈ I :=
    Ideal.subset_span (Or.inr (Or.inr (Or.inr rfl)))
  have hni : ¬ Function.Injective gm := by
    intro hinj
    let S : Submonoid T := (nonZeroDivisors (MvPolynomial (Fin M × ι) k)).map gm
    have hS : ∀ Q : MvPolynomial (Fin M × ι) k, Q ≠ 0 → gm Q ∈ S := fun Q hQ =>
      Submonoid.mem_map_of_mem _ (mem_nonZeroDivisors_of_ne_zero hQ)
    have hdisj : Disjoint ((⊥ : Ideal T) : Set T) S := by
      rw [Set.disjoint_left]
      rintro x hx ⟨Q, hQ, rfl⟩
      have h0 : gm Q = 0 := (Submodule.mem_bot _).1 hx
      have : Q = 0 := hinj (by rw [h0, map_zero])
      exact nonZeroDivisors.ne_zero hQ this
    obtain ⟨𝔮, h𝔮, -, hd⟩ := Ideal.exists_le_prime_disjoint ⊥ S hdisj
    haveI := h𝔮
    let D := T ⧸ 𝔮
    let κ := FractionRing D
    let π : MvPolynomial (Var M ι) A →+* κ :=
      (algebraMap D κ).comp ((Ideal.Quotient.mk 𝔮).comp (Ideal.Quotient.mk I))
    have hπC : ∀ a : A, π (C a) = algebraMap A κ a := by
      intro a
      show algebraMap D κ (Ideal.Quotient.mk 𝔮 (Ideal.Quotient.mk I (C a))) = _
      rw [IsScalarTower.algebraMap_apply A D κ]
      rfl
    have hπI : ∀ x ∈ I, π x = 0 := by
      intro x hx
      show algebraMap D κ (Ideal.Quotient.mk 𝔮 (Ideal.Quotient.mk I x)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero, map_zero]
    have ht : AlgebraicIndependent k (fun x : Fin M × ι => π (X (Sum.inl x))) := by
      rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
      intro Q hQ
      by_contra hQ0
      have heq : (aeval (fun x : Fin M × ι => π (X (Sum.inl x))) :
          MvPolynomial (Fin M × ι) k →ₐ[k] κ) =
          (IsScalarTower.toAlgHom k D κ).comp ((Ideal.Quotient.mkₐ k 𝔮).comp gm) := by
        ext x
        simp [π, gm]
      rw [heq] at hQ
      have h1 : Ideal.Quotient.mk 𝔮 (gm Q) = 0 :=
        (IsFractionRing.injective D κ) (hQ.trans (map_zero _).symm)
      rw [Ideal.Quotient.eq_zero_iff_mem] at h1
      exact Set.disjoint_left.1 hd h1 (hS Q hQ0)
    apply false_of_dependent_derivatives n δ ω hω f M J i₀ p₀ hi₀ _ ht (fun i => π (X (Sum.inr (Sum.inl i))))
    · intro i hi
      have := hπI _ (g1mem i hi)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa only [map_sum, map_mul, hπC] using this
    · intro l
      have := hπI _ (g2mem l)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa only [map_sum, map_mul, hπC] using this
    · have h3 : π (X (Sum.inr (Sum.inl i₀)) - 1) = 0 := hπI _ g3mem
      rw [RingHom.map_sub, RingHom.map_one] at h3
      exact h3
    · have h4 := hπI _ g4mem
      rw [RingHom.map_sub, RingHom.map_mul, hπC, RingHom.map_one] at h4
      exact h4
  obtain ⟨Q, hQ0, hQ⟩ : ∃ Q, Q ≠ 0 ∧ gm Q = 0 := by
    by_contra hcon
    push_neg at hcon
    exact hni ((injective_iff_map_eq_zero gm).2 fun Q hQ => by_contra fun h => hcon Q h hQ)
  refine ⟨Q, hQ0, ?_⟩
  intro u hu K _ _ φ c hφ hc hrel hδ
  let e : MvPolynomial (Var M ι) A →+* K := eval₂Hom φ.toRingHom
    (Sum.elim (fun x => algebraMap k K (u x)) (Sum.elim c (fun _ => (φ (f p₀))⁻¹)))
  have hI : I ≤ RingHom.ker e := by
    rw [hIdef, relIdeal, Ideal.span_le]
    rintro x (⟨i, hi, rfl⟩ | ⟨l, rfl⟩ | rfl | rfl) <;> simp only [SetLike.mem_coe, RingHom.mem_ker]
    · have := hrel i hi
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [e, map_sum, Algebra.smul_def] using this
    · have := hδ l
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [e, map_sum, Algebra.smul_def] using this
    · simp [e, hc]
    · simp [e, inv_mul_cancel₀ hφ]
  let e' : T →+* K := Ideal.Quotient.lift I e (fun a ha => hI ha)
  have hcomp : e'.comp gm.toRingHom = (algebraMap k K).comp (eval u) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      show e' (gm (C a)) = algebraMap k K (eval u (C a))
      rw [MvPolynomial.aeval_C]
      show e (algebraMap k (MvPolynomial (Var M ι) A) a) = _
      rw [MvPolynomial.algebraMap_apply, eval₂Hom_C, eval_C]
      exact φ.commutes a
    · intro x
      show e' (gm (X x)) = algebraMap k K (eval u (X x))
      rw [MvPolynomial.aeval_X, eval_X]
      show e (X (Sum.inl x)) = _
      rw [eval₂Hom_X']
      rfl
  have := RingHom.congr_fun hcomp Q
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
  rw [hQ, map_zero] at this
  exact hu ((algebraMap k K).injective (this.symm.trans (map_zero _).symm))

end GlobalTheory.BertiniC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BertiniGeneralMembersNoDerivativeRelationStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bertini_general_members_no_derivative_relation : ∀ (k A : Type) [Field k] [CharZero k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (n : ℕ) (δ : Fin n → Derivation k A A) (ω : Fin n → KaehlerDifferential k A), (∀ a : A, KaehlerDifferential.D k A a = ∑ l, δ l a • ω l) → ∀ {ι : Type} [Fintype ι] (f : ι → A) (M : ℕ) (J : Finset (Fin M)) (i₀ : Fin M) (p₀ : ι), i₀ ∈ J → ∃ Q : MvPolynomial (Fin M × ι) k, Q ≠ 0 ∧ ∀ u : Fin M × ι → k, MvPolynomial.eval u Q ≠ 0 → ∀ (K : Type) [Field K] [Algebra k K] (φ : A →ₐ[k] K) (c : Fin M → K), φ (f p₀) ≠ 0 → c i₀ = 1 → (∀ i ∈ J, φ (∑ p, u (i, p) • f p) = 0) → ¬ ∀ l, ∑ i ∈ J, c i * φ (δ l (∑ p, u (i, p) • f p)) = 0 := by
  first | exact @GlobalTheory.BertiniC.no_dependence_of_general | exact GlobalTheory.BertiniC.no_dependence_of_general | (intros; apply GlobalTheory.BertiniC.no_dependence_of_general <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationSplitKaehlerDSmooth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationSplitKaehlerDSmooth
open KaehlerDifferential
namespace GlobalTheory
theorem bertini_derivation_split : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A], ∃ (n : ℕ) (δ : Fin n → Derivation k A A) (ω : Fin n → KaehlerDifferential k A), ∀ a : A, KaehlerDifferential.D k A a = ∑ l, δ l a • ω l := by
  intro k A _ _ _ _
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A (KaehlerDifferential k A)
  refine ⟨n, fun l => (LinearMap.proj l ∘ₗ g).compDer (KaehlerDifferential.D k A), fun l => f (Pi.single l 1), ?_⟩
  intro a
  have h := LinearMap.congr_fun hfg (KaehlerDifferential.D k A a)
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
  conv_lhs => rw [← h]
  conv_lhs => rw [pi_eq_sum_univ (g (KaehlerDifferential.D k A a))]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationSplitKaehlerDSmoothStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_split_kaehlerD_smooth : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A], ∃ (n : ℕ) (δ : Fin n → Derivation k A A) (ω : Fin n → KaehlerDifferential k A), ∀ a : A, KaehlerDifferential.D k A a = ∑ l, δ l a • ω l := by
  first | exact @GlobalTheory.bertini_derivation_split | exact GlobalTheory.bertini_derivation_split | (intros; apply GlobalTheory.bertini_derivation_split <;> assumption)
end
end

namespace GlobalTheory

open IsLocalRing

theorem derivation_mem_of_mem_sq {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
    (δ : Derivation k A A) (q : Ideal A) {x : A} (hx : x ∈ q ^ 2) : δ x ∈ q := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro m hm n hn
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact q.add_mem (q.mul_mem_right _ hm) (q.mul_mem_right _ hn)
  · intro x y hx hy
    rw [map_add (f := _)]; exact q.add_mem hx hy

theorem residue_algebraMap_eq_zero_iff_mem {A R : Type} [CommRing A] [CommRing R] [IsLocalRing R]
    [Algebra A R] (q : Ideal A) [q.IsPrime] [IsLocalization.AtPrime R q] (x : A) :
    residue R (algebraMap A R x) = 0 ↔ x ∈ q := by
  rw [residue_eq_zero_iff]
  conv_rhs => rw [← IsLocalization.AtPrime.under_maximalIdeal R q]
  rfl

theorem cotangent_relation_derivation {k A R : Type} [CommRing k] [CommRing A] [Algebra k A]
    (q : Ideal A) [q.IsPrime] [CommRing R] [IsLocalRing R] [Algebra A R]
    [IsLocalization.AtPrime R q]
    (δ : Derivation k A A) {κ : Type} (J : Finset κ) (g : κ → A)
    (hg : ∀ j, algebraMap A R (g j) ∈ maximalIdeal R) (c : κ → ResidueField R)
    (hrel : ∑ j ∈ J, c j • (maximalIdeal R).toCotangent ⟨_, hg j⟩ = 0) :
    ∑ j ∈ J, c j * residue R (algebraMap A R (δ (g j))) = 0 := by
  set ψ : A →+* ResidueField R := (residue R).comp (algebraMap A R) with hψdef
  have hψ : ∀ x, ψ x = 0 ↔ x ∈ q := fun x => residue_algebraMap_eq_zero_iff_mem q x
  have hgq : ∀ j, g j ∈ q := fun j => (hψ _).1 ((residue_eq_zero_iff _).2 (hg j))
  set r : κ → R := fun j => (residue_surjective (c j)).choose with hr
  have hrc : ∀ j, residue R (r j) = c j := fun j => (residue_surjective (c j)).choose_spec
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples q.primeCompl J r
  have hb' : ∀ i ∈ J, ∃ x : A, algebraMap A R x = (b : A) • r i := fun i hi => hb i hi
  choose! a ha using hb'
  have hb0 : ψ b ≠ 0 := fun h => b.2 ((hψ _).1 h)
  have hψa : ∀ j ∈ J, ψ (a j) = ψ b * c j := by
    intro j hj
    simp only [hψdef, RingHom.comp_apply, ha j hj, Algebra.smul_def, map_mul, hrc]
  set y : A := ∑ j ∈ J, a j * g j with hy
  have hyq : y ∈ q := q.sum_mem fun j _ => q.mul_mem_left _ (hgq j)

  have hT : (maximalIdeal R).toCotangent
      (∑ j ∈ J, algebraMap A R (a j) • (⟨_, hg j⟩ : maximalIdeal R)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    have : ∀ j ∈ J, (maximalIdeal R).toCotangent (algebraMap A R (a j) • (⟨_, hg j⟩ : maximalIdeal R))
        = ψ b • (c j • (maximalIdeal R).toCotangent ⟨_, hg j⟩) := by
      intro j hj
      rw [map_smul, smul_smul, ← hψa j hj]
      exact (algebraMap_smul (ResidueField R) (algebraMap A R (a j)) _).symm
    rw [Finset.sum_congr rfl this, ← Finset.smul_sum, hrel, smul_zero]
  rw [Ideal.toCotangent_eq_zero] at hT
  have hcoe : ((∑ j ∈ J, algebraMap A R (a j) • (⟨_, hg j⟩ : maximalIdeal R) : maximalIdeal R) : R)
      = algebraMap A R y := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hy, Submodule.coe_sum, map_sum, map_mul, Algebra.smul_def]
  rw [hcoe, ← IsLocalization.AtPrime.map_eq_maximalIdeal q R, ← Ideal.map_pow,
    IsLocalization.mem_map_algebraMap_iff q.primeCompl R] at hT
  obtain ⟨⟨x, s⟩, hxs⟩ := hT
  rw [← map_mul, IsLocalization.eq_iff_exists q.primeCompl R] at hxs
  obtain ⟨t, ht⟩ := hxs
  have hz : (t : A) * (y * s) ∈ q ^ 2 := ht ▸ Ideal.mul_mem_left _ _ x.2
  have hδz := (hψ _).2 (derivation_mem_of_mem_sq δ q hz)
  have hs0 : ψ s ≠ 0 := fun h => s.2 ((hψ _).1 h)
  have ht0 : ψ t ≠ 0 := fun h => t.2 ((hψ _).1 h)
  have hy0 : ψ y = 0 := (hψ _).2 hyq
  have hδy : ψ (δ y) = 0 := by
    simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, hy0] at hδz
    simpa [hs0, ht0] using hδz
  have hg0 : ∀ j, ψ (g j) = 0 := fun j => (hψ _).2 (hgq j)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hy, map_sum, map_sum] at hδy
  simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, hg0, zero_mul, add_zero] at hδy
  rw [Finset.sum_congr rfl (fun j hj => by rw [hψa j hj, mul_assoc]), ← Finset.mul_sum] at hδy
  exact (mul_eq_zero.1 hδy).resolve_left hb0

end GlobalTheory

namespace GlobalTheory
open IsLocalRing

theorem bertini_cotangent_independent : ∀ (k A : Type) [Field k] [CharZero k] [CommRing A] [Algebra k A] [Algebra.Smooth k A] {ι : Type} [Fintype ι] (f : ι → A) (M : ℕ), ∃ Q : MvPolynomial (Fin M × ι) k, Q ≠ 0 ∧ ∀ u : Fin M × ι → k, MvPolynomial.eval u Q ≠ 0 → ∀ (q : Ideal A) [q.IsPrime] (R : Type) [CommRing R] [IsLocalRing R] [Algebra A R] [IsLocalization.AtPrime R q], (∃ p, f p ∉ q) → LinearIndependent (IsLocalRing.ResidueField R) (fun j : {j : Fin M // algebraMap A R (∑ p, u (j, p) • f p) ∈ IsLocalRing.maximalIdeal R} => ((IsLocalRing.maximalIdeal R).toCotangent ⟨_, j.2⟩ : IsLocalRing.CotangentSpace R)) := by
  intro k A _ _ _ _ _ ι _ f M
  obtain ⟨n, δ, ω, hD⟩ := GlobalTheory.T.exists_derivation_split_kaehlerD_smooth k A
  have hC := fun (J : Finset (Fin M)) (i₀ : Fin M) (p₀ : ι) (h : i₀ ∈ J) =>
    GlobalTheory.T.bertini_general_members_no_derivative_relation k A n δ ω hD f M J i₀ p₀ h
  classical
  let Qf : Finset (Fin M) × Fin M × ι → MvPolynomial (Fin M × ι) k := fun x =>
    if h : x.2.1 ∈ x.1 then (hC x.1 x.2.1 x.2.2 h).choose else 1
  refine ⟨∏ x, Qf x, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro x _
    simp only [Qf]
    split_ifs with h
    · exact (hC _ _ _ h).choose_spec.1
    · exact one_ne_zero
  · intro u hu q _ R _ _ _ _ hp
    obtain ⟨p₀, hp₀⟩ := hp
    rw [map_prod, Finset.prod_ne_zero_iff] at hu
    rw [linearIndependent_iff']
    intro s w hw i₀ hi₀
    by_contra hne
    let ψ : A →+* ResidueField R := (residue R).comp (algebraMap A R)
    letI : Algebra k (ResidueField R) := (ψ.comp (algebraMap k A)).toAlgebra
    let φ : A →ₐ[k] ResidueField R := { ψ with commutes' := fun _ => rfl }
    let J : Finset (Fin M) := s.map (Function.Embedding.subtype _)
    let c : Fin M → ResidueField R := fun j =>
      if h : algebraMap A R (∑ p, u (j, p) • f p) ∈ maximalIdeal R then w ⟨j, h⟩ / w i₀ else 0
    have hJ : i₀.1 ∈ J := Finset.mem_map_of_mem _ hi₀
    have hx := hu (J, i₀.1, p₀) (Finset.mem_univ _)
    simp only [Qf, dif_pos hJ] at hx
    refine (hC J i₀.1 p₀ hJ).choose_spec.2 u hx (ResidueField R) φ c ?_ ?_ ?_ ?_
    · exact fun h => hp₀ ((residue_algebraMap_eq_zero_iff_mem q _).1 h)
    · show c i₀.1 = 1
      rw [show c i₀.1 = w i₀ / w i₀ from dif_pos i₀.2]
      exact div_self hne
    · intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.1 hi
      exact (residue_eq_zero_iff _).2 j.2
    · intro l
      have hrel : ∑ j ∈ s, (w j / w i₀) •
          (maximalIdeal R).toCotangent ⟨_, j.2⟩ = 0 := by
        simp_rw [div_eq_mul_inv, mul_comm _ (w i₀)⁻¹, mul_smul]
        rw [← Finset.smul_sum, hw, smul_zero]
      have key := cotangent_relation_derivation q (δ l) s
        (fun j => ∑ p, u (j.1, p) • f p) (fun j => j.2) (fun j => w j / w i₀) hrel
      rw [Finset.sum_map]
      convert key using 2 with j hj
      show c j.1 * φ _ = _
      rw [show c j.1 = w j / w i₀ from dif_pos j.2]
      rfl

end GlobalTheory
