module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralLiftCoprimeDerivative
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralLiftCoprimeDerivative
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IntCop

theorem lift_of_val_le {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (Q : E[X]) (h : ∀ n, w.valuation E (Q.coeff n) ≤ 1) :
    ∃ Q₀ : (w.adicCompletionIntegers E)[X],
      Q₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) =
        Q.map (algebraMap E (w.adicCompletion E)) := by
  have : Q.map (algebraMap E (w.adicCompletion E)) ∈
      Polynomial.lifts (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    refine ⟨⟨algebraMap E (w.adicCompletion E) (Q.coeff n),
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_⟩, rfl⟩
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (Q.coeff n)).trans_le (h n)
  obtain ⟨Q₀, hQ₀⟩ := (Polynomial.mem_lifts _).1 this
  exact ⟨Q₀, hQ₀⟩

theorem finite_bad {E : Type} [Field E] [NumberField E] (Q : E[X]) :
    {w : HeightOneSpectrum (𝓞 E) | ¬ ∀ n, w.valuation E (Q.coeff n) ≤ 1}.Finite := by
  refine ((Finset.range (Q.natDegree + 1)).finite_toSet.biUnion
    fun n _ => HeightOneSpectrum.Support.finite (𝓞 E) (Q.coeff n)).subset ?_
  intro w hw
  simp only [Set.mem_setOf_eq, not_forall, not_le] at hw
  obtain ⟨n, hn⟩ := hw
  have hn' : n < Q.natDegree + 1 := by
    by_contra hc
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero] at hn
    exact (not_lt.2 zero_le') hn
  simp only [Set.mem_iUnion]
  exact ⟨n, by simpa using hn', hn⟩

end GlobalTheory.IntCop

namespace GlobalTheory.IntCop

theorem eventually_integral_coprime : ∀ (E : Type) [Field E] [NumberField E] (P : E[X]), P.Separable →
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∃ P₀ : (w.adicCompletionIntegers E)[X],
      P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) = P.map (algebraMap E (w.adicCompletion E)) ∧
      IsCoprime P₀ (derivative P₀) := by
  intro E _ _ P hP
  obtain ⟨a, b, hab⟩ := hP
  have hfin := ((finite_bad P).union (finite_bad a)).union (finite_bad b)
  refine Filter.eventually_cofinite.2 (hfin.subset ?_)
  intro w hw
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  obtain ⟨⟨hPw, haw⟩, hbw⟩ := hc
  apply hw
  obtain ⟨P₀, hP₀⟩ := lift_of_val_le w P hPw
  obtain ⟨a₀, ha₀⟩ := lift_of_val_le w a haw
  obtain ⟨b₀, hb₀⟩ := lift_of_val_le w b hbw
  refine ⟨P₀, hP₀, a₀, b₀, ?_⟩
  have hinj : Function.Injective
      (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := Subtype.val_injective
  apply Polynomial.map_injective _ hinj
  rw [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
    ha₀, hb₀, hP₀, Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul,
    ← Polynomial.map_add, hab, Polynomial.map_one, Polynomial.map_one]

end GlobalTheory.IntCop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralLiftCoprimeDerivativeStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_integral_lift_coprime_derivative : ∀ (E : Type) [Field E] [NumberField E] (P : E[X]), P.Separable →
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∃ P₀ : (w.adicCompletionIntegers E)[X],
      P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) = P.map (algebraMap E (w.adicCompletion E)) ∧
      IsCoprime P₀ (derivative P₀) := by
  first | exact @GlobalTheory.IntCop.eventually_integral_coprime | exact GlobalTheory.IntCop.eventually_integral_coprime | (intros; apply GlobalTheory.IntCop.eventually_integral_coprime <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjResultantOfEllPolys
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjResultantOfEllPolys
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ResConj

theorem prod_product_mul (A B : Multiset ℂ) (f g : ℂ → ℂ) :
    ((A ×ˢ B).map fun ij => f ij.1 * g ij.2).prod =
      (A.map f).prod ^ Multiset.card B * (B.map g).prod ^ Multiset.card A := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons a A ih =>
    rw [Multiset.cons_product, Multiset.map_add (f := _), Multiset.prod_add, ih, Multiset.map_map]
    simp only [Function.comp_def, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
      Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, mul_pow, pow_succ]
    ring

theorem conj_prod_sub (A B : Multiset ℂ) (hA : ∀ x ∈ A, ‖x‖ = 1) (hB : ∀ y ∈ B, ‖y‖ = 1) :
    (starRingEnd ℂ) (((A ×ˢ B).map fun ij => ij.1 - ij.2).prod) *
        (A.prod ^ Multiset.card B * B.prod ^ Multiset.card A) =
      (-1) ^ (Multiset.card A * Multiset.card B) * ((A ×ˢ B).map fun ij => ij.1 - ij.2).prod := by
  have h := prod_product_mul A B id id
  simp only [Multiset.map_id, id, Multiset.map_id'] at h
  rw [← h, map_multiset_prod, Multiset.map_map, ← Multiset.prod_map_mul]
  have hc : ∀ ij ∈ A ×ˢ B, ((starRingEnd ℂ) ∘ fun ij : ℂ × ℂ => ij.1 - ij.2) ij * (ij.1 * ij.2) =
      (-1) * (ij.1 - ij.2) := by
    intro ij hij
    rw [Multiset.mem_product] at hij
    have h1 := hA _ hij.1
    have h2 := hB _ hij.2
    have n1 : ij.1 ≠ 0 := by intro h0; rw [h0, norm_zero] at h1; exact zero_ne_one h1
    have n2 : ij.2 ≠ 0 := by intro h0; rw [h0, norm_zero] at h2; exact zero_ne_one h2
    have c1 : (starRingEnd ℂ) ij.1 = ij.1⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h1]; simp
    have c2 : (starRingEnd ℂ) ij.2 = ij.2⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h2]; simp
    simp only [Function.comp_apply, map_sub, c1, c2]
    field_simp
    ring
  rw [Multiset.map_congr rfl hc, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
    Multiset.card_product]

theorem conj_resultant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (P₁ P₂ : E[X]),
    P₁ ∈ Ell E a → P₂ ∈ Ell E b → IsCMField.complexConj E (resultant P₁ P₂) *
      (((-1) ^ a * P₁.coeff 0) ^ b * ((-1) ^ b * P₂.coeff 0) ^ a) = (-1) ^ (a * b) * resultant P₁ P₂ := by
  intro E _ _ _ a b P₁ P₂ h₁ h₂
  obtain ⟨m₁, d₁, -, r₁⟩ := h₁
  obtain ⟨m₂, d₂, -, r₂⟩ := h₂
  let τ : E →+* ℂ := Classical.choice (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  have sA : (P₁.map τ).Splits := IsAlgClosed.splits _
  have sB : (P₂.map τ).Splits := IsAlgClosed.splits _
  have cA : Multiset.card (P₁.map τ).roots = a := by rw [← sA.natDegree_eq_card_roots, natDegree_map, d₁]
  have cB : Multiset.card (P₂.map τ).roots = b := by rw [← sB.natDegree_eq_card_roots, natDegree_map, d₂]
  have hres : τ (resultant P₁ P₂) =
      (((P₁.map τ).roots ×ˢ (P₂.map τ).roots).map fun ij => ij.1 - ij.2).prod := by
    rw [← resultant_eq_prod_roots_sub _ _ (m₁.map τ) (m₂.map τ) sA sB,
      ← resultant_map_map P₁ P₂ P₁.natDegree P₂.natDegree τ, natDegree_map, natDegree_map]
  have e₁ : τ ((-1) ^ a * P₁.coeff 0) = (P₁.map τ).roots.prod := by
    rw [map_mul, map_pow, map_neg, map_one, ← coeff_map, sA.coeff_zero_eq_prod_roots_of_monic (m₁.map τ),
      natDegree_map, d₁, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  have e₂ : τ ((-1) ^ b * P₂.coeff 0) = (P₂.map τ).roots.prod := by
    rw [map_mul, map_pow, map_neg, map_one, ← coeff_map, sB.coeff_zero_eq_prod_roots_of_monic (m₂.map τ),
      natDegree_map, d₂, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  have key := conj_prod_sub _ _ (r₁ τ) (r₂ τ)
  rw [cA, cB] at key
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, e₁, e₂, IsCMField.complexEmbedding_complexConj, hres, key,
    map_pow, map_neg, map_one]

end GlobalTheory.ResConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjResultantOfEllPolysStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_resultant_of_ell_polys : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (P₁ P₂ : E[X]), P₁ ∈ Ell E a → P₂ ∈ Ell E b → IsCMField.complexConj E (resultant P₁ P₂) * (((-1) ^ a * P₁.coeff 0) ^ b * ((-1) ^ b * P₂.coeff 0) ^ a) = (-1) ^ (a * b) * resultant P₁ P₂ := by
  first | exact @GlobalTheory.ResConj.conj_resultant | exact GlobalTheory.ResConj.conj_resultant | (intros; apply GlobalTheory.ResConj.conj_resultant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffLinearSubstitution
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffLinearSubstitution
set_option autoImplicit false

noncomputable section

open scoped Matrix

namespace GlobalTheory.GoodTop

namespace MixSubst

variable {n : ℕ}

theorem det_rows_sum (x : Fin n → Fin n → ℂ) (k : Fin n → Fin n → Fin n → ℂ) :
    (Matrix.of fun i d => ∑ c, x i c * k i c d).det =
      ∑ c : Fin n → Fin n, (∏ i, x i (c i)) * (Matrix.of fun i d => k i (c i) d).det := by
  have h : (Matrix.of fun i d => ∑ c, x i c * k i c d) = fun i => ∑ c, x i c • k i c := by
    ext i j
    simp
  rw [h]
  change (Matrix.detRowAlternating : AlternatingMap ℂ (Fin n → ℂ) ℂ (Fin n)) _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← AlternatingMap.coe_multilinearMap, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

theorem sum_sign_prod (J : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → Fin n) :
    ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) * ∏ i, J (c i) (u i) = (J.submatrix c id).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  rfl

theorem alt_sum (J : Matrix (Fin n) (Fin n) ℂ) (k : Fin n → Fin n → Fin n → ℂ) :
    ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i d => ∑ c, J c (u i) * k i c d).det =
      J.det * ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) * (Matrix.of fun i d => k i (u i) d).det := by
  have h1 : ∀ u : Equiv.Perm (Fin n), (Matrix.of fun i d => ∑ c, J c (u i) * k i c d).det =
      ∑ c : Fin n → Fin n, (∏ i, J (c i) (u i)) * (Matrix.of fun i d => k i (c i) d).det :=
    fun u => det_rows_sum (fun i c => J c (u i)) k
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, sum_sign_prod]
  symm
  refine Fintype.sum_of_injective (fun σ : Equiv.Perm (Fin n) => (σ : Fin n → Fin n)) DFunLike.coe_injective _ _
    (fun c hc => ?_) (fun σ => ?_)
  · have hinj : ¬ Function.Injective c := fun h =>
      hc ⟨Equiv.ofBijective c (Finite.injective_iff_bijective.mp h), rfl⟩
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, c i = c j ∧ i ≠ j := by
      simp only [Function.Injective, not_forall] at hinj
      obtain ⟨i, j, h, h'⟩ := hinj
      exact ⟨i, j, h, h'⟩
    rw [Matrix.det_zero_of_row_eq hne (by ext l; simp [hij]), zero_mul]
  · rw [Matrix.det_permute, mul_comm J.det]

theorem alt_sum_two (J J' : Matrix (Fin n) (Fin n) ℂ) (k : Fin n → Fin n → Fin n → ℂ) :
    ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => ∑ c, ∑ d, J c (u i) * J' d b * k i c d).det =
      J.det * J'.det *
        ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) * (Matrix.of fun i d => k i (u i) d).det := by
  have h1 : ∀ u : Equiv.Perm (Fin n), (Matrix.of fun i b => ∑ c, ∑ d, J c (u i) * J' d b * k i c d) =
      (Matrix.of fun i d => ∑ c, J c (u i) * k i c d) * J' := by
    intro u
    ext i b
    simp only [Matrix.of_apply, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  simp_rw [h1, Matrix.det_mul, ← mul_assoc, ← Finset.sum_mul]
  rw [alt_sum]
  ring

end MixSubst

theorem mixTop_subst {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r)
    (J J' : Matrix (Fin n) (Fin n) ℂ) :
    mixTop (fun i a b => ∑ c, ∑ d, (J c a * J' d b) • K i c d) = J.det * J'.det * mixTop K := by
  unfold mixTop
  rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  simp_rw [mul_assoc ((Equiv.Perm.sign π : ℤ) : ℂ), ← Finset.mul_sum]
  rw [mul_left_comm, ← MixSubst.alt_sum_two J J' (fun i c d => K i c d (p i) (p (π i)))]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

end GlobalTheory.GoodTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffLinearSubstitutionStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedTopChernCoeff_linear_substitution : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (J J' : Matrix (Fin n) (Fin n) ℂ), mixTop (fun i a b => ∑ c, ∑ d, (J c a * J' d b) • K i c d) = J.det * J'.det * mixTop K := by
  first | exact @GlobalTheory.GoodTop.mixTop_subst | exact GlobalTheory.GoodTop.mixTop_subst | (intros; apply GlobalTheory.GoodTop.mixTop_subst <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierDivisorAddEffective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierDivisorAddEffective
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

set_option autoImplicit false
noncomputable section
open GlobalTheory.Cartier.CartierDiv
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.Cartier.EffDiff

variable {X : Scheme.{0}} [IsIntegral X]

theorem exists_pow_regAt {V : X.Opens} (hV : IsAffineOpen V) (τ : Γ(X, V))
    (hη : genericPoint X ∈ X.basicOpen τ) {f : X.functionField}
    (hf : ∀ x ∈ X.basicOpen τ, RegAt x f) :
    ∃ m : ℕ, ∀ x ∈ V, RegAt x (f * fnOf V (X.basicOpen_le τ hη) τ ^ m) := by
  obtain ⟨b, hb⟩ := exists_fnOf_eq hη hf
  haveI := hV.isLocalization_basicOpen τ
  obtain ⟨m, a, e⟩ := IsLocalization.Away.surj τ b
  refine ⟨m, fun x hx => ?_⟩
  have e' := congrArg (fnOf _ hη) e
  rw [map_mul, map_pow, hb] at e'
  have h1 : ∀ c : Γ(X, V), fnOf _ hη (algebraMap Γ(X, V) Γ(X, X.basicOpen τ) c) =
      fnOf V (X.basicOpen_le τ hη) c := fun c => fnOf_resG (X.basicOpen_le τ) hη c
  rw [h1, h1] at e'
  rw [e']
  exact regAt_fnOf hx _ a

theorem eventually_eff_add_nsmul [CompactSpace X] {L : LB X} (hL : L.IsLB) (t : L.Sec)
    (ht : genericPoint X ∈ nonzeroLocus t) (D : CartierDiv X)
    (hD : ∀ x ∈ nonzeroLocus t, D.RegularAt x 1) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → (D + N • divOfSec hL t ht).Eff := by
  have key : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ m : ℕ, ∀ N, m ≤ N → ∀ y ∈ V,
      (D + N • divOfSec hL t ht).RegularAt y 1 := by
    intro x
    obtain ⟨W, hxW, h, hh⟩ := D.exists_isEqn_nhds x
    obtain ⟨i, hi⟩ := exists_chart hL x
    obtain ⟨V, hVa, hxV, hVle⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show x ∈ W ⊓ L.U i from ⟨hxW, hi⟩)
    have hVW : V ≤ W := hVle.trans inf_le_left
    have hVi : V ≤ L.U i := hVle.trans inf_le_right
    set τ : Γ(X, V) := resG X hVi (t.f i)
    have hbo : ∀ y, y ∈ X.basicOpen τ ↔ y ∈ V ∧ y ∈ nonzeroLocus t := fun y => by
      have hb : X.basicOpen τ = V ⊓ X.basicOpen (t.f i) := X.basicOpen_res _ _
      rw [hb]
      exact ⟨fun hy => ⟨hy.1, (mem_nonzeroLocus_iff t i (hVi hy.1)).2 hy.2⟩,
        fun hy => ⟨hy.1, (mem_nonzeroLocus_iff t i (hVi hy.1)).1 hy.2⟩⟩
    have hη : genericPoint X ∈ X.basicOpen τ := (hbo _).2 ⟨gen_mem hxV, ht⟩
    obtain ⟨m, hm⟩ := exists_pow_regAt hVa τ hη (f := h) fun y hy => by
      obtain ⟨hyV, hyt⟩ := (hbo y).1 hy
      have := (hh y (hVW hyV)).regularAt_iff.1 (hD y hyt)
      rwa [one_mul] at this
    refine ⟨V, hxV, m, fun N hN y hyV => ?_⟩
    have hT := (presents_divOfRatSec hL (isRatSec_ratOfSec t ht)).isEqn i y (hVi hyV)
    refine ⟨_, (hh y (hVW hyV)).add (hT.nsmul N), ?_⟩
    have e : (ratOfSec t ht i : X.functionField) = fnOf V (X.basicOpen_le τ hη) τ := by
      rw [val_ratOfSec (gen_mem (hVi hyV)), fnOf_resG]
    rw [one_mul, Units.val_mul, Units.val_pow_eq_pow_val, e, ← Nat.add_sub_cancel' hN, pow_add,
      ← mul_assoc]
    have hp := regAt_fnOf hyV (X.basicOpen_le τ hη) (τ ^ (N - m))
    rw [map_pow] at hp
    exact (hm y hyV).mul hp
  choose V hxV m hm using key
  obtain ⟨S, hS⟩ := exists_finset_iSup_eq_top V hxV
  refine ⟨S.sup m, fun N hN y => ?_⟩
  obtain ⟨x, hy⟩ := Opens.mem_iSup.1 (hS.ge (Set.mem_univ y))
  exact hm x N ((Finset.le_sup x.2).trans hN) y hy

end GlobalTheory.Cartier.EffDiff

theorem GlobalTheory.Cartier.EffDiff.exists_eff_and_add_eff : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (H : LB X),
    IsAmpleLB H → ∀ D : CartierDiv X, ∃ E : CartierDiv X, E.Eff ∧ (D + E).Eff := by
  intro X _ _ H hH D
  haveI := hH.compactSpace
  obtain ⟨W, hηW, g, hg⟩ := D.exists_isEqn_nhds (genericPoint X)
  obtain ⟨n, -, t, hηt, htW, hU⟩ := hH.exists_affine_le hηW
  have hL := isLB_lbPow hH.isLB n
  haveI : Nonempty (nonzeroLocus t) := ⟨⟨_, hηt⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X _ hU
  obtain ⟨a, c, hc, e⟩ := IsFractionRing.div_surjective (A := Γ(X, nonzeroLocus t))
    (g : X.functionField)
  have hfn : ∀ b : Γ(X, nonzeroLocus t),
      algebraMap Γ(X, nonzeroLocus t) X.functionField b = fnOf _ hηt b := fun _ => rfl
  have hc0 : fnOf _ hηt c ≠ 0 := by
    rw [← hfn]; exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hc
  obtain ⟨N₁, h₁⟩ := eventually_eff_add_nsmul hL t hηt (principal (Units.mk0 _ hc0))
    fun x hx => ⟨_, isEqn_principal _ x, by rw [one_mul, Units.val_mk0]; exact regAt_fnOf hx hηt c⟩
  obtain ⟨N₂, h₂⟩ := eventually_eff_add_nsmul hL t hηt (D + principal (Units.mk0 _ hc0))
    fun x hx => ⟨_, (hg x (htW hx)).add (isEqn_principal _ x), by
      rw [one_mul, Units.val_mul, Units.val_mk0, ← e, hfn, hfn, div_mul_cancel₀ _ hc0]
      exact regAt_fnOf hx hηt a⟩
  refine ⟨principal (Units.mk0 _ hc0) + max N₁ N₂ • divOfSec hL t hηt, h₁ _ (le_max_left _ _), ?_⟩
  rw [← add_assoc]
  exact h₂ _ (le_max_right _ _)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierDivisorAddEffectiveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_effective_cartierDivisor_add_effective : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (H : LB X), IsAmpleLB H → ∀ D : CartierDiv X, ∃ E : CartierDiv X, E.Eff ∧ (D + E).Eff := by
  first | exact @GlobalTheory.Cartier.EffDiff.exists_eff_and_add_eff | exact GlobalTheory.Cartier.EffDiff.exists_eff_and_add_eff | (intros; apply GlobalTheory.Cartier.EffDiff.exists_eff_and_add_eff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulBoundAtBaseChange
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.ChowHt GlobalTheory.Vanishing

namespace GlobalTheory.Vanishing

open H0

variable {Y T : Scheme.{0}} {k k' : Type} [CommRing k] [CommRing k'] {p : Y ⟶ Sp k} {q : T ⟶ Sp k'} {φ : k →+* k'}
  {r : T ⟶ Y} {P B N : LB Y} {P' B' N' : LB T} {O : Y.Opens} {W : T.Opens}

theorem pullChart_ofSec (a : ChartPull B' B r) (hq : r ≫ p = q ≫ spMap φ) (h : W ≤ r ⁻¹ᵁ O) (s : B.Sec) :
    pullChart a hq h (H0.ofSec p O s) = H0.ofSec q W (GlobalTheory.chartSec a s) :=
  LB.sec_ext fun i => fun_ext_ger fun z hz => by
    change germ i z hz.1 hz.2 _ = germ i z hz.1 hz.2 _
    rw [germ_pullChart, germ_ofSec]
    exact (congrArg _ (germ_ofSec _ _ _ _ s)).trans (ger_appLE r _ z hz.2 _).symm

theorem pullChart_mul (C : ProdChart P B N) (C' : ProdChart P' B' N') (a : ChartPull P' P r) (b : ChartPull B' B r)
    (c : ChartPull N' N r) (hC : ∀ t, ∃ s, a.idx (C'.a t) = C.a s ∧ b.idx (C'.b t) = C.b s ∧ c.idx (C'.c t) = C.c s)
    (hq : r ≫ p = q ≫ spMap φ) (h : W ≤ r ⁻¹ᵁ O) (σ : H0 p P O) (f : H0 p B O) :
    pullChart c hq h (C.mul σ f) = C'.mul (pullChart a hq h σ) (pullChart b hq h f) :=
  C'.sec_ext fun t z hz ha hb hc => by
    obtain ⟨s, e₁, e₂, e₃⟩ := hC t
    have key (y hy i j l) (e₁ : i = C.a s) (e₂ : j = C.b s) (e₃ : l = C.c s) (hi hj hl) :
        germ l y hy hl (C.mul σ f) = germ i y hy hi σ * germ j y hy hj f := by
      subst e₁ e₂ e₃
      exact C.germ_mul σ f s y hy hi hj hl
    rw [C'.germ_mul _ _ t z hz ha hb hc, germ_pullChart, germ_pullChart, germ_pullChart, ← map_mul]
    exact congrArg _ (key _ _ _ _ _ e₁ e₂ e₃ _ _ _)

end GlobalTheory.Vanishing

namespace GlobalTheory.HermTools

end GlobalTheory.HermTools

namespace GlobalTheory.Adelic.HermSys

variable {F : Type} [Field F] [NumberField F] {T : HermSys F} (E : Type) [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.Adelic.HermSys

namespace GlobalTheory.HilbertSamuel

variable {F : Type} [Field F] [NumberField F]

namespace Geo

variable (G : Geo F) (E : Type) [Field E] [NumberField E] [Algebra F E]

theorem toExt_mulW (j : ℕ) (u : Fin G.N → F) (f : G.Sec j) :
    G.toExt E (j + 1) (G.mulW j u f) = (G.baseChange E).mulW j (algebraMap F E ∘ u) (G.toExt E j f) := by
  refine (pullChart_mul _ (oneChart (isLB_tens (G.baseChange E).K.isLB (G.baseChange E).isLBA) (G.baseChange E).isLB
    (Nat.cast_succ j).symm) (GlobalTheory.chartPullPull G.L (G.fst E)) (G.chartAdj E j) (G.chartAdj E (j + 1))
    (fun t => ⟨((t.1.1 PUnit.unit, t.1.2 PUnit.unit), t.2 PUnit.unit), rfl, rfl, rfl⟩) _ le_rfl _ f).trans ?_
  refine congrArg (fun s => ProdChart.mul _ s _) ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact (map_smulₛₗ _ _ _).trans (congrArg _ (pullChart_ofSec _ _ _ (G.b k)))

end Geo

namespace Data

variable {X : Data F} (E : Type) [Field E] [NumberField E] [Algebra F E]



variable (X) in
theorem toExtV_mem {j : ℕ} {x : X.V j} (hx : x ∈ X.M j) : X.toExtV E j x ∈ (X.baseChange E).M j :=
  (Submodule.subset_span ⟨x, hx, rfl⟩ : extMap (X.toExt E j) (X.V j) x ∈
    Submodule.span (𝓞 E) (extMap (X.toExt E j) (X.V j) '' X.M j))

theorem MulStable.baseChange (h : X.MulStable) : (X.baseChange E).MulStable := fun j hj w hw f hf => by
  let X' := X.baseChange E
  let S := (X'.M (j + 1)).map ((X'.V (j + 1)).subtype.restrictScalars (𝓞 E))
  change X'.mulW j w f ∈ S
  induction hw using Submodule.span_induction with
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply]; exact add_mem ha hb
  | smul c a _ ha => rw [← algebraMap_smul E, map_smul, LinearMap.smul_apply, algebraMap_smul]; exact S.smul_mem _ ha
  | mem w hw =>
    obtain ⟨k, rfl⟩ := hw
    induction hf using Submodule.span_induction with
    | zero => exact (map_zero (X'.mulW j _)).symm ▸ zero_mem _
    | add a b _ _ ha hb => exact (map_add (X'.mulW j _) _ _).symm ▸ add_mem ha hb
    | smul c a _ ha =>
      exact (map_smul (X'.mulW j _) (algebraMap _ E c) _).symm ▸ S.smul_mem c ha
    | mem f hf =>
      obtain ⟨f, hf, rfl⟩ := hf
      obtain ⟨g, hg, e⟩ := h j hj _ (Submodule.subset_span ⟨k, rfl⟩) f hf
      exact ⟨_, X.toExtV_mem E hg, (congrArg (X.toExt E (j + 1)) e).trans (X.toExt_mulW E j _ _)⟩




end Data

end GlobalTheory.HilbertSamuel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffSlotLinear
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffUpdateAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffUpdateAdd
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

namespace GlobalTheory.GoodTop

theorem mixTop_update_add : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (j : Fin n) (L L' : EndValuedForm11Coeffs n r), mixTop (Function.update K j (L + L')) = mixTop (Function.update K j L) + mixTop (Function.update K j L') := by
  intro n r _ _ K j L L'
  have key : ∀ (M : EndValuedForm11Coeffs n r) (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      (Matrix.of fun i b => Function.update K j M i (u i) b (p i) (p (π i))) =
        (Matrix.of fun i b => K i (u i) b (p i) (p (π i))).updateRow j
          (fun b => M (u j) b (p j) (p (π j))) := by
    intro M p π u
    ext i b
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.updateRow_ne h, Function.update_of_ne h]
  unfold mixTop
  rw [← mul_add]
  congr 1
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun u _ => ?_
  rw [key, key, key, ← mul_add, ← Matrix.det_updateRow_add]
  rfl

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffUpdateAddStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedTopChernCoeff_update_add : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (j : Fin n) (L L' : EndValuedForm11Coeffs n r), mixTop (Function.update K j (L + L')) = mixTop (Function.update K j L) + mixTop (Function.update K j L') := by
  first | exact @GlobalTheory.GoodTop.mixTop_update_add | exact GlobalTheory.GoodTop.mixTop_update_add | (intros; apply GlobalTheory.GoodTop.mixTop_update_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffUpdateSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffUpdateSmul
set_option autoImplicit false

open GlobalTheory.GoodTop

namespace GlobalTheory.GoodTop

theorem mixTop_update_smul {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (j : Fin n)
    (t : ℂ) (L : EndValuedForm11Coeffs n r) :
    mixTop (Function.update K j (t • L)) = t * mixTop (Function.update K j L) := by
  have key : ∀ (M : EndValuedForm11Coeffs n r) (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      (Matrix.of fun i b => Function.update K j M i (u i) b (p i) (p (π i))) =
        (Matrix.of fun i b => K i (u i) b (p i) (p (π i))).updateRow j
          (fun b => M (u j) b (p j) (p (π j))) := by
    intro M p π u
    ext i b
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.updateRow_ne h, Function.update_of_ne h]
  have h2 : ∀ (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      (Matrix.of fun i b => Function.update K j (t • L) i (u i) b (p i) (p (π i))).det =
        t * (Matrix.of fun i b => Function.update K j L i (u i) b (p i) (p (π i))).det := by
    intro p π u
    rw [key, key, ← Matrix.det_updateRow_smul]
    rfl
  unfold mixTop
  simp only [h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun u _ => ?_
  ring

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffUpdateSmulStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedTopChernCoeff_update_smul : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (j : Fin n) (t : ℂ) (L : EndValuedForm11Coeffs n r), mixTop (Function.update K j (t • L)) = t * mixTop (Function.update K j L) := by
  first | exact @GlobalTheory.GoodTop.mixTop_update_smul | exact GlobalTheory.GoodTop.mixTop_update_smul | (intros; apply GlobalTheory.GoodTop.mixTop_update_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffSlotLinear
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem position_eq_update {n : ℕ} {α : Type} [Zero α] (K₁ L K₀ : α) (j : Fin n) :
    intersection_update_fsHerm_neg_one K₁ L K₀ j = Function.update (intersection_update_fsHerm_neg_one K₁ 0 K₀ j) j L := by
  funext i
  by_cases h : i = j
  · subst h; simp [intersection_update_fsHerm_neg_one]
  · simp [intersection_update_fsHerm_neg_one, Function.update_of_ne h, h]

theorem mixTop_position_linear {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K₁ K₀ L L' : EndValuedForm11Coeffs n r)
    (s t : ℂ) (j : Fin n) :
    mixTop (intersection_update_fsHerm_neg_one K₁ (s • L + t • L') K₀ j) = s * mixTop (intersection_update_fsHerm_neg_one K₁ L K₀ j) + t * mixTop (intersection_update_fsHerm_neg_one K₁ L' K₀ j) := by
  rw [position_eq_update, position_eq_update K₁ L, position_eq_update K₁ L', GlobalTheory.T.polarisedTopChernCoeff_update_add, GlobalTheory.T.polarisedTopChernCoeff_update_smul, GlobalTheory.T.polarisedTopChernCoeff_update_smul]

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffSlotLinearStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedTopChernCoeff_position_linear : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K₁ K₀ L L' : EndValuedForm11Coeffs n r) (s t : ℂ) (j : Fin n), mixTop (intersection_update_fsHerm_neg_one K₁ (s • L + t • L') K₀ j) = s * mixTop (intersection_update_fsHerm_neg_one K₁ L K₀ j) + t * mixTop (intersection_update_fsHerm_neg_one K₁ L' K₀ j) := by
  first | exact @GlobalTheory.GoodTop.mixTop_position_linear | exact GlobalTheory.GoodTop.mixTop_position_linear | (intros; apply GlobalTheory.GoodTop.mixTop_position_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerMassEqOfTopEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerMassEqOfTopEquiv
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.MassTor

section Closed

variable {G : Type} [Group G] [TopologicalSpace G]

theorem isCompact_closure_zpowers_iff {T : Subgroup G} (hT : IsClosed (T : Set G)) (t : T) :
    IsCompact (closure (Subgroup.zpowers (t : G) : Set G)) ↔ IsCompact (closure (Subgroup.zpowers t : Set T)) := by
  have hE : Topology.IsClosedEmbedding (Subtype.val : T → G) := hT.isClosedEmbedding_subtypeVal
  have h1 : (Subgroup.zpowers (t : G) : Set G) = Subtype.val '' (Subgroup.zpowers t : Set T) := by
    have := MonoidHom.map_zpowers T.subtype t
    rw [← Subgroup.coe_subtype, ← Subgroup.coe_map, this]
  rw [h1, hE.closure_image_eq, ← hE.isEmbedding.isCompact_iff]

theorem cptPart_eq_map {T : Subgroup G} (hT : IsClosed (T : Set G)) :
    cptPart T = (Subgroup.closure {t : T | IsCompact (closure (Subgroup.zpowers t : Set T))}).map T.subtype := by
  rw [MonoidHom.map_closure]
  unfold cptPart
  congr 1
  ext g
  constructor
  · rintro ⟨hg, hc⟩
    exact ⟨⟨g, hg⟩, (isCompact_closure_zpowers_iff hT ⟨g, hg⟩).1 hc, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t.2, (isCompact_closure_zpowers_iff hT t).2 ht⟩

theorem cptPart_le (T : Subgroup G) : cptPart T ≤ T :=
  (Subgroup.closure_le _).2 fun _ hg => hg.1

theorem mem_cptPart_iff {T : Subgroup G} (hT : IsClosed (T : Set G)) (t : T) :
    (t : G) ∈ cptPart T ↔ t ∈ Subgroup.closure {s : T | IsCompact (closure (Subgroup.zpowers s : Set T))} := by
  rw [cptPart_eq_map hT, Subgroup.mem_map]
  constructor
  · rintro ⟨s, hs, h⟩
    rwa [show s = t from Subtype.ext h] at hs
  · intro h
    exact ⟨t, h, rfl⟩

end Closed

theorem mem_closure_cpt_iff {A B : Type} [Group A] [TopologicalSpace A] [Group B] [TopologicalSpace B] (e : A ≃ₜ* B)
    (a : A) :
    a ∈ Subgroup.closure {s : A | IsCompact (closure (Subgroup.zpowers s : Set A))} ↔
      e a ∈ Subgroup.closure {s : B | IsCompact (closure (Subgroup.zpowers s : Set B))} := by
  have key : ∀ s : A, IsCompact (closure (Subgroup.zpowers s : Set A)) ↔
      IsCompact (closure (Subgroup.zpowers (e s) : Set B)) := by
    intro s
    have h1 : (Subgroup.zpowers (e s) : Set B) = e '' (Subgroup.zpowers s : Set A) := by
      have := MonoidHom.map_zpowers e.toMulEquiv.toMonoidHom s
      have h := congrArg (fun H : Subgroup B => (H : Set B)) this
      rw [Subgroup.coe_map] at h
      exact h.symm
    rw [h1]
    have h2 := e.toHomeomorph.image_closure (Subgroup.zpowers s : Set A)
    have h3 := e.toHomeomorph.isCompact_image (s := closure (Subgroup.zpowers s : Set A))
    rw [show (⇑e.toHomeomorph : A → B) = ⇑e from rfl] at h2 h3
    rw [← h2, h3]
  have himg : e.toMulEquiv.toMonoidHom '' {s : A | IsCompact (closure (Subgroup.zpowers s : Set A))} =
      {s : B | IsCompact (closure (Subgroup.zpowers s : Set B))} := by
    ext b
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact (key s).1 hs
    · intro hb
      refine ⟨e.symm b, (key _).2 ?_, ?_⟩
      · simpa using hb
      · exact e.apply_symm_apply b
  have hmap := MonoidHom.map_closure e.toMulEquiv.toMonoidHom
    {s : A | IsCompact (closure (Subgroup.zpowers s : Set A))}
  rw [himg] at hmap
  rw [← hmap, Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨a, h, rfl⟩
  · rintro ⟨x, hx, h⟩
    have : x = a := e.injective h
    rwa [← this]

theorem card_doubleCoset_congr {A B : Type} [Group A] [Group B] (e : A ≃* B) (H K : Subgroup A) (H' K' : Subgroup B)
    (hH : ∀ a, a ∈ H ↔ e a ∈ H') (hK : ∀ a, a ∈ K ↔ e a ∈ K') :
    Nat.card (DoubleCoset.Quotient (H : Set A) (K : Set A)) =
      Nat.card (DoubleCoset.Quotient (H' : Set B) (K' : Set B)) := by
  apply Nat.card_congr
  refine Quotient.congr e.toEquiv fun x y => ?_
  rw [DoubleCoset.rel_iff, DoubleCoset.rel_iff]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨e a, (hH a).1 ha, e b, (hK b).1 hb, by simp [map_mul]⟩
  · rintro ⟨a, ha, b, hb, h⟩
    refine ⟨e.symm a, (hH _).2 (by simpa using ha), e.symm b, (hK _).2 (by simpa using hb), ?_⟩
    apply e.injective
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv] at h
    simp [map_mul, h]

theorem mass_eq_of_equiv (G G' : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] (θ : G →* G) (θ' : G' →* G') (Γ : Subgroup G) (Γ' : Subgroup G')
    (δ : G) (δ' : G') (hT : IsClosed (twCent θ δ : Set G)) (hT' : IsClosed (twCent θ' δ' : Set G'))
    (e : twCent θ δ ≃ₜ* twCent θ' δ')
    (hΓ : ∀ t : twCent θ δ, (t : G) ∈ Γ ↔ ((e t : twCent θ' δ') : G') ∈ Γ') :
    mass θ Γ δ = mass θ' Γ' δ' := by
  have hC : ∀ t : twCent θ δ, (t : G) ∈ cptPart (twCent θ δ) ↔ ((e t : twCent θ' δ') : G') ∈ cptPart (twCent θ' δ') :=
    fun t => by rw [mem_cptPart_iff hT, mem_cptPart_iff hT', mem_closure_cpt_iff e]
  have hmem : ∀ t : twCent θ δ, (t : G) ∈ Γ ⊓ cptPart (twCent θ δ) ↔
      ((e t : twCent θ' δ') : G') ∈ Γ' ⊓ cptPart (twCent θ' δ') := fun t => by
    simp only [Subgroup.mem_inf]
    rw [hΓ t, hC t]
  let f : (Γ ⊓ cptPart (twCent θ δ) : Subgroup G) ≃ (Γ' ⊓ cptPart (twCent θ' δ') : Subgroup G') :=
    { toFun := fun g => ⟨(e ⟨g, cptPart_le _ g.2.2⟩ : G'), (hmem _).1 g.2⟩
      invFun := fun g' => ⟨(e.symm ⟨g', cptPart_le _ g'.2.2⟩ : G),
        (hmem (e.symm ⟨g', cptPart_le _ g'.2.2⟩)).2 (by rw [e.apply_symm_apply]; exact g'.2)⟩
      left_inv := fun g => by ext; simp
      right_inv := fun g' => by ext; simp }
  unfold mass
  rw [card_doubleCoset_congr e.toMulEquiv _ _ (Γ'.subgroupOf (twCent θ' δ')) ((cptPart (twCent θ' δ')).subgroupOf _)
    (fun a => by simp only [Subgroup.mem_subgroupOf]; exact hΓ a)
    (fun a => by simp only [Subgroup.mem_subgroupOf]; exact hC a), Nat.card_congr f]

end GlobalTheory.MassTor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerMassEqOfTopEquivStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedCentralizerMass_eq_of_topEquiv : ∀ (G G' : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] (θ : G →* G) (θ' : G' →* G') (Γ : Subgroup G) (Γ' : Subgroup G') (δ : G) (δ' : G'), IsClosed (twCent θ δ : Set G) → IsClosed (twCent θ' δ' : Set G') → ∀ (e : twCent θ δ ≃ₜ* twCent θ' δ'), (∀ t : twCent θ δ, (t : G) ∈ Γ ↔ ((e t : twCent θ' δ') : G') ∈ Γ') → mass θ Γ δ = mass θ' Γ' δ' := by
  first | exact @GlobalTheory.MassTor.mass_eq_of_equiv | exact GlobalTheory.MassTor.mass_eq_of_equiv | (intros; apply GlobalTheory.MassTor.mass_eq_of_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTopFormChartIntegralZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTopFormChartIntegralZero
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem glueMeas_zero_dens {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y]
    (e : κ → OpenPartialHomeomorph Y (V n)) : glueMeas e (fun _ _ => 0) = 0 := by
  have h : ∀ i, chartMeas (e i) (fun _ => 0) = 0 := by
    intro i
    unfold chartMeas
    have : ((fun _ : Y => (0 : ENNReal)) ∘ (e i).symm) = 0 := rfl
    rw [this, withDensity_zero, Measure.map_zero]
  unfold glueMeas
  simp only [h]
  exact le_antisymm (iSup_le fun _ => le_rfl) (Measure.zero_le _)

theorem hasInt_zero {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y]
    (e : κ → OpenPartialHomeomorph Y (V n)) (S : Set Y) : HasInt e (fun _ _ => 0) S 0 := by
  unfold HasInt
  simp only [mul_zero, ENNReal.ofReal_zero, glueMeas_zero_dens]
  simp

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTopFormChartIntegralZeroStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasTopFormChartIntegral_zero : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] (e : κ → OpenPartialHomeomorph Y (V n)) (S : Set Y), HasInt e (fun _ _ => 0) S 0 := by
  first | exact @GlobalTheory.GoodTop.hasInt_zero | exact GlobalTheory.GoodTop.hasInt_zero | (intros; apply GlobalTheory.GoodTop.hasInt_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyNearComplexPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyNearComplexPoint
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

namespace GlobalTheory.GoodTop

theorem frame_eventually {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ}
    (E : Fr (ratOf X) (fun _ : Unit => m) 0) {y : CxPts X.str σ} {A : Mat (fun _ : Unit => m) X.Fn}
    (hA : A ∈ E.S (under y)) : ∀ᶠ z in 𝓝 y, A ∈ E.S (under z) := by
  obtain ⟨U, B, hU, hB, hS⟩ := E.loc (under y)
  have hP := (hS _ hU A).1 hA
  have hreg : ∀ g : X.Fn, RegAt (under y) g → ∀ᶠ z in 𝓝 y, RegAt (under z) g := by
    intro g hg
    obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
    filter_upwards [(isOpen_ptsIn W).mem_nhds (mem_ptsIn.2 hW)] with z hz
    exact regAt_fnOf (mem_ptsIn.1 hz) _ a
  have hU' : ∀ᶠ z in 𝓝 y, under z ∈ U := by
    filter_upwards [(isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU)] with z hz
    exact mem_ptsIn.1 hz
  have h1 : ∀ᶠ z in 𝓝 y, ∀ τ, (∀ i j, RegAt (under z) ((A * B⁻¹) τ i j)) ∧ RegAt (under z) ((A * B⁻¹) τ).det⁻¹ :=
    Filter.eventually_all.2 fun τ => (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      hreg _ (mem_O_ratOf.1 ((hP τ).1 i j))).and (hreg _ (mem_O_ratOf.1 (hP τ).2.2.1))
  filter_upwards [hU', h1] with z hz hz1
  exact (hS _ hz A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 ((hz1 τ).1 i j), (hP τ).2.1, mem_O_ratOf.2 (hz1 τ).2,
    fun i j hi => absurd hi (by simp)⟩

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyNearComplexPointStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adaptedFrame_eventually_near_complexPoint : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) {y : CxPts X.str σ} {A : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → ∀ᶠ z in 𝓝 y, A ∈ E.S (under z) := by
  first | exact @GlobalTheory.GoodTop.frame_eventually | exact GlobalTheory.GoodTop.frame_eventually | (intros; apply GlobalTheory.GoodTop.frame_eventually <;> assumption)
end
end
