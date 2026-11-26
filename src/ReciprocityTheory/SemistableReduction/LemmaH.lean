module

public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import ReciprocityTheory.SemistableReduction.SJCoreA

@[expose] public section

section -- merged from ReciprocityTheory.SemistableReduction.LemmaH
namespace ReciprocityTheory.MultiplicativeHeights

open Matrix InnerProductSpace

theorem exists_unitary_mul_upper {n : ℕ} (x : Matrix (Fin n) (Fin n) ℂ) :
    ∃ k b : Matrix (Fin n) (Fin n) ℂ, k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ b.BlockTriangular id ∧
      x = k * b ∧ ∀ j, ‖b j j‖ ^ 2 ≤ colNormSq x j := by
  classical
  let std := EuclideanSpace.basisFun (Fin n) ℂ
  let f : Fin n → EuclideanSpace ℂ (Fin n) := fun j => (EuclideanSpace.equiv (Fin n) ℂ).symm (fun i => x i j)
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n) := by simp
  let e := gramSchmidtOrthonormalBasis hdim f
  have hstd : std.toBasis.toMatrix f = x := by
    ext i j
    simp [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, f, std]
  have hnorm : ∀ j, ‖f j‖ ^ 2 = colNormSq x j := by
    intro j
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp [colNormSq, f]
  refine ⟨std.toBasis.toMatrix e.toBasis, e.toBasis.toMatrix f, ?_, ?_, ?_, ?_⟩
  · simpa [OrthonormalBasis.coe_toBasis] using OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary std e
  · exact gramSchmidtOrthonormalBasis_inv_blockTriangular hdim f
  · rw [Module.Basis.toMatrix_mul_toMatrix, hstd]
  · intro j
    rw [← hnorm j, Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply]
    have h1 : ‖inner ℂ (e j) (f j)‖ ≤ ‖f j‖ := by
      calc ‖inner ℂ (e j) (f j)‖ ≤ ‖e j‖ * ‖f j‖ := norm_inner_le_norm _ _
        _ = ‖f j‖ := by rw [e.orthonormal.1 j, one_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2

private theorem P_ite_mul_eq_prod_triChar_mul {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι → ℕ)
    (a : ∀ s, Fin (p s) → ℕ) (P : (∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) → ℂ)
    (hP : ∀ (x : ∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) (s : ι) (b : Matrix (Fin (p s)) (Fin (p s)) ℂ),
      (∀ t, (x t).det ≠ 0) → b.det ≠ 0 → b.BlockTriangular id →
      P (Function.update x s (x s * b)) = triChar (a s) b * P x)
    (k b : ∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) (hk : ∀ s, (k s).det ≠ 0)
    (hb : ∀ s, (b s).det ≠ 0) (hbt : ∀ s, (b s).BlockTriangular id) (S : Finset ι) :
    P (fun t => if t ∈ S then k t * b t else k t) =
      (∏ s ∈ S, triChar (a s) (b s)) * P k := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert s S hs ih =>
    have hy : ∀ t, ((fun t => if t ∈ S then k t * b t else k t) t).det ≠ 0 := by
      intro t
      by_cases ht : t ∈ S
      · simp only [ht, if_true, Matrix.det_mul]
        exact mul_ne_zero (hk t) (hb t)
      · simp only [ht, if_false]
        exact hk t
    have heq : (fun t => if t ∈ insert s S then k t * b t else k t) =
        Function.update (fun t => if t ∈ S then k t * b t else k t) s
          ((fun t => if t ∈ S then k t * b t else k t) s * b s) := by
      funext t
      by_cases hts : t = s
      · subst hts
        simp [hs]
      · simp [hts]
    rw [heq, hP _ s (b s) hy (hb s) (hbt s), ih, Finset.prod_insert hs, mul_assoc]

theorem lemmaH_holds : LemmaHStatement := by
  intro ι _ _ p a P C R hP hC hR x hx hcol
  classical
  choose k b hk hbt hkb hdiag using fun s => exists_unitary_mul_upper (x s)
  have hkdet : ∀ s, (k s).det ≠ 0 := by
    intro s
    exact (Matrix.UnitaryGroup.det_isUnit ⟨k s, hk s⟩).ne_zero
  have hbdet : ∀ s, (b s).det ≠ 0 := by
    intro s h
    apply hx s
    rw [hkb s, Matrix.det_mul, h, mul_zero]
  have hxk : x = fun t => if t ∈ (Finset.univ : Finset ι) then k t * b t else k t := by
    funext t
    simp [← hkb t]
  have hmain := P_ite_mul_eq_prod_triChar_mul p a P hP k b hkdet hbdet hbt Finset.univ
  rw [← hxk] at hmain
  have hC0 : 0 ≤ C := by
    have h1 := hC (fun s => 1) (fun s => one_mem _)
    exact (norm_nonneg _).trans h1
  have hbR : ∀ s i, ‖b s i i‖ ≤ R := by
    intro s i
    have h1 := (hdiag s i).trans (hcol s i)
    nlinarith [norm_nonneg (b s i i)]
  have hprod : ‖∏ s, triChar (a s) (b s)‖ ≤ R ^ (∑ s, ∑ i, a s i) := by
    rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro s _
    rw [triChar, norm_prod, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro i _
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbR s i) _
  rw [hmain, norm_mul, mul_comm C]
  exact mul_le_mul hprod (hC k hk) (norm_nonneg _) (pow_nonneg hR _)

end ReciprocityTheory.MultiplicativeHeights
end

section -- merged from ReciprocityTheory.SemistableReduction.AevalIsWeightedHomogeneous
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MvPolynomial

def blockIndexWeight {B n : ℕ} (b : Fin B) : Fin B × Fin n → ℕ := fun p => if p.1 = b then 1 else 0

theorem weight_lh0BlockWt_apply {B n : ℕ} (b : Fin B) (s : Fin B × Fin n →₀ ℕ) :
    Finsupp.weight (blockIndexWeight (n := n) b) s = ∑ j : Fin n, s (b, j) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [blockIndexWeight, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b (fun x _ hx => by simp [hx]) (by simp)]
  simp

theorem isMultiHomogeneous_iff_forall_weighted_lh0BlockWt {R : Type*} [CommSemiring R] {B n : ℕ} (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin n) R) :
    IsMultiHomogeneous a f ↔ ∀ b, IsWeightedHomogeneous (blockIndexWeight b) f (a b) := by
  simp only [IsMultiHomogeneous, IsWeightedHomogeneous, weight_lh0BlockWt_apply, mem_support_iff]
  constructor
  · intro h b d hd
    exact h d hd b
  · intro h s hs b
    exact h b hs

theorem eval_mul_of_isMultiHomogeneous {B n : ℕ} {a : Fin B → ℕ} {g : MvPolynomial (Fin B × Fin n) ℂ}
    (hg : IsMultiHomogeneous a g) (c : ℂ) (z : Fin B × Fin n → ℂ) :
    eval (fun p => c * z p) g = c ^ (∑ b, a b) * eval z g := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hdeg : ∑ p, s p = ∑ b, a b := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun b _ => hg s hs b
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

private lemma sum_primitiveRoot_pow_mul_inv_pow_eq_ite {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) {a b : ℕ}
    (ha : a < N) (hb : b < N) :
    ∑ j : Fin N, (ζ ^ a * ζ⁻¹ ^ b) ^ (j : ℕ) = if a = b then (N : ℂ) else 0 := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le a) ha
  have hz : ζ ≠ 0 := hζ.ne_zero hN.ne'
  rw [Fin.sum_univ_eq_sum_range (fun j => (ζ ^ a * ζ⁻¹ ^ b) ^ j) N]
  split_ifs with hab
  · subst hab
    rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
    simp
  · have hω1 : ζ ^ a * ζ⁻¹ ^ b ≠ 1 := by
      intro h
      apply hab
      apply hζ.pow_inj ha hb
      rwa [inv_pow, mul_inv_eq_one₀ (pow_ne_zero _ hz)] at h
    have hωN : (ζ ^ a * ζ⁻¹ ^ b) ^ N = 1 := by
      rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm a, Nat.mul_comm b, pow_mul, pow_mul, inv_pow,
        hζ.pow_eq_one]
      simp
    rw [geom_sum_eq hω1, hωN]
    simp

theorem exists_torus_coeff_le {ι : Type*} [Fintype ι] (g : MvPolynomial ι ℂ) (s : ι →₀ ℕ) :
    ∃ z : ι → ℂ, (∀ i, ‖z i‖ = 1) ∧ ‖AddMonoidAlgebra.coeff g s‖ ≤ ‖eval z g‖ := by
  classical
  by_cases hs : s ∈ g.support
  swap
  · refine ⟨fun _ => 1, fun _ => by simp, ?_⟩
    rw [show AddMonoidAlgebra.coeff g s = 0 by simpa using hs, norm_zero]
    exact norm_nonneg _
  obtain ⟨N, hN⟩ : ∃ N, N = g.totalDegree + 1 := ⟨_, rfl⟩
  have hN0 : N ≠ 0 := by omega
  haveI : NeZero N := ⟨hN0⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ N := ⟨_, Complex.isPrimitiveRoot_exp N hN0⟩
  have hζn : ‖ζ‖ = 1 := hζ.norm'_eq_one hN0
  have hlt : ∀ d ∈ g.support, ∀ i, d i < N := by
    intro d hd i
    have h1 : d i ≤ d.sum fun _ e => e := by
      rw [Finsupp.sum_fintype _ _ (by simp)]
      exact Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)
    have h2 := le_totalDegree hd
    omega
  let z : (ι → Fin N) → ι → ℂ := fun k i => ζ ^ (k i : ℕ)
  let c : (ι → Fin N) → ℂ := fun k => ∏ i, ζ⁻¹ ^ ((k i : ℕ) * s i)
  have key : ∑ k, eval (z k) g * c k = (N : ℂ) ^ Fintype.card ι * AddMonoidAlgebra.coeff g s := by
    calc ∑ k, eval (z k) g * c k
        = ∑ d ∈ g.support, AddMonoidAlgebra.coeff g d * ∏ i, ∑ j : Fin N, (ζ ^ d i * ζ⁻¹ ^ s i) ^ (j : ℕ) := by
          simp only [eval_eq', Finset.sum_mul, z, c]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_assoc, ← Finset.prod_mul_distrib]
          congr 1
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, Nat.mul_comm (d i), Nat.mul_comm (s i)]
      _ = ∑ d ∈ g.support, AddMonoidAlgebra.coeff g d * (if d = s then (N : ℂ) ^ Fintype.card ι else 0) := by
          refine Finset.sum_congr rfl fun d hd => ?_
          congr 1
          simp_rw [sum_primitiveRoot_pow_mul_inv_pow_eq_ite hζ (hlt d hd _) (hlt s hs _)]
          split_ifs with hds
          · subst hds
            simp
          · obtain ⟨i, hi⟩ : ∃ i, d i ≠ s i := by
              by_contra h
              push_neg at h
              exact hds (Finsupp.ext h)
            exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
      _ = (N : ℂ) ^ Fintype.card ι * AddMonoidAlgebra.coeff g s := by
          rw [Finset.sum_eq_single s (fun d _ hd => by simp [hd]) (fun h => absurd hs h)]
          simp [mul_comm]
  by_contra hcon
  push_neg at hcon
  have hlt2 : ∀ k, ‖eval (z k) g * c k‖ < ‖AddMonoidAlgebra.coeff g s‖ := by
    intro k
    have hc : ‖c k‖ = 1 := by simp [c, norm_prod, norm_pow, norm_inv, hζn]
    rw [norm_mul, hc, mul_one]
    exact hcon (z k) (fun i => by simp [z, norm_pow, hζn])
  have hsum := norm_sum_le (Finset.univ : Finset (ι → Fin N)) (fun k => eval (z k) g * c k)
  have hsum2 : ∑ k, ‖eval (z k) g * c k‖ < ∑ _k : ι → Fin N, ‖AddMonoidAlgebra.coeff g s‖ :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun k _ => hlt2 k)
  rw [key, norm_mul, norm_pow, Complex.norm_natCast] at hsum
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul] at hsum2
  push_cast at hsum2
  linarith

end ReciprocityTheory.MultiplicativeHeights
end
end

section -- merged from ReciprocityTheory.SemistableReduction.IntegralClosureRankAndResidueTrdegLe
namespace ReciprocityTheory.MultiplicativeHeights

theorem integralClosureRank (O F L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field F] [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
    [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L] :
    IsDedekindDomain (integralClosure O L) ∧ Module.Finite O (integralClosure O L) ∧
      Module.Free O (integralClosure O L) ∧
      Module.finrank O (integralClosure O L) = Module.finrank F L ∧
      {Q : Ideal (integralClosure O L) | Q.IsMaximal}.Finite ∧
      ∑ᶠ Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal},
          Q.1.ramificationIdx O * Q.1.inertiaDeg O = Module.finrank F L := by
  set C := integralClosure O L
  haveI hD : IsDedekindDomain C := integralClosure.isDedekindDomain O F L
  haveI hFin : Module.Finite O C := IsIntegralClosure.finite O F L C
  haveI : Module.IsTorsionFree O L := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq O F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective O F)
  haveI : Module.IsTorsionFree O C := inferInstance
  haveI hFr : Module.Free O C := Module.free_of_finite_type_torsion_free'
  haveI : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension O F L C
  set m := IsLocalRing.maximalIdeal O
  have hm : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have key : ∀ Q : Ideal C, Q.IsMaximal ↔ Q ∈ IsDedekindDomain.primesOverFinset m C := by
    intro Q
    rw [IsDedekindDomain.mem_primesOverFinset_iff hm C]
    constructor
    · intro hQ
      have hu : (Q.under O).IsMaximal := Ideal.IsMaximal.under O Q
      refine ⟨hQ.isPrime, ⟨?_⟩⟩
      exact (IsLocalRing.eq_maximalIdeal hu).symm
    · rintro ⟨hP, hl⟩
      refine hP.isMaximal ?_
      rintro rfl
      apply hm
      rw [hl.over]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective O C)
  refine ⟨hD, hFin, hFr, IsIntegralClosure.rank O F L C, ?_, ?_⟩
  · exact (IsDedekindDomain.primesOverFinset m C).finite_toSet.subset fun Q hQ => (key Q).1 hQ
  · rw [← Ideal.sum_ramification_inertia C F L hm]
    rw [← finsum_comp_equiv (Equiv.subtypeEquivRight key).symm, finsum_eq_sum_of_fintype,
      ← Finset.sum_coe_sort (IsDedekindDomain.primesOverFinset m C)]
    refine Finset.sum_congr rfl fun P _ => ?_
    have hP := P.2
    rw [IsDedekindDomain.mem_primesOverFinset_iff hm C] at hP
    haveI := hP.1
    haveI := hP.2
    haveI : P.1.IsMaximal := ((key P.1).2 P.2)
    simp only [Equiv.subtypeEquivRight_symm_apply_coe]
    rw [Ideal.ramificationIdx_eq_ramificationIdx' m P.1 hm, Ideal.inertiaDeg_eq_inertiaDeg' m P.1]

open MvPolynomial

theorem algebraicIndependent_of_residue_lift {F₁ F₂ : Type} [Field F₁] [Field F₂] [Algebra F₁ F₂]
    (V : ValuationSubring F₂) {ι : Type*} (y : ι → V)
    (hx : letI := residueAlgebra V (algebraMap F₁ F₂)
      AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap F₁ F₂)))
        (fun i => IsLocalRing.residue V (y i))) :
    AlgebraicIndependent F₁ (fun i => ((y i : V) : F₂)) := by
  classical
  letI := residueAlgebra V (algebraMap F₁ F₂)
  rw [algebraicIndependent_iff] at hx ⊢
  intro p hp
  by_contra hne
  have hS : p.support.Nonempty := by
    rwa [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
  obtain ⟨m₀, hm₀, hmax⟩ := p.support.exists_max_image
    (fun m => (V.comap (algebraMap F₁ F₂)).valuation (p.coeff m)) hS
  have hc : p.coeff m₀ ≠ 0 := MvPolynomial.mem_support_iff.1 hm₀
  have hvc : (V.comap (algebraMap F₁ F₂)).valuation (p.coeff m₀) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 hc

  have hle : ∀ m, (p.coeff m₀)⁻¹ * p.coeff m ∈ V.comap (algebraMap F₁ F₂) := by
    intro m
    rw [← ValuationSubring.valuation_le_one_iff, map_mul, map_inv₀]
    by_cases hm : m ∈ p.support
    · calc ((V.comap (algebraMap F₁ F₂)).valuation (p.coeff m₀))⁻¹ *
            (V.comap (algebraMap F₁ F₂)).valuation (p.coeff m)
          ≤ ((V.comap (algebraMap F₁ F₂)).valuation (p.coeff m₀))⁻¹ *
            (V.comap (algebraMap F₁ F₂)).valuation (p.coeff m₀) := by
            gcongr
            exact hmax m hm
        _ = 1 := inv_mul_cancel₀ hvc
    · rw [MvPolynomial.notMem_support_iff.1 hm]
      simp
  have hpp : MvPolynomial.C (p.coeff m₀)⁻¹ * p ∈
      Set.range (MvPolynomial.map (V.comap (algebraMap F₁ F₂)).subtype) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro a ha
    obtain ⟨m, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 ha
    exact ⟨⟨_, hle m⟩, by simp [MvPolynomial.coeff_C_mul]⟩
  obtain ⟨qV, hqV⟩ := hpp
  have hcoeff : qV.coeff m₀ = 1 := by
    have e := congrArg (AddMonoidAlgebra.coeff · m₀) hqV
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, inv_mul_cancel₀ hc] at e
    exact Subtype.ext e
  have h0 : MvPolynomial.eval₂ (comapInclusion V (algebraMap F₁ F₂)) y qV = 0 := by
    apply Subtype.ext
    have e1 : MvPolynomial.aeval (fun i => ((y i : V) : F₂))
        (MvPolynomial.C (p.coeff m₀)⁻¹ * p) = 0 := by
      rw [map_mul, hp, mul_zero]
    rw [MvPolynomial.aeval_def, ← hqV, MvPolynomial.eval₂_map] at e1
    have e2 := MvPolynomial.eval₂_comp_left V.subtype (comapInclusion V (algebraMap F₁ F₂)) y qV
    have e3 : V.subtype.comp (comapInclusion V (algebraMap F₁ F₂)) =
        (algebraMap F₁ F₂).comp (V.comap (algebraMap F₁ F₂)).subtype := RingHom.ext fun _ => rfl
    rw [e3] at e2
    exact e2.trans e1

  have h1 : MvPolynomial.aeval (fun i => IsLocalRing.residue V (y i))
      (MvPolynomial.map (IsLocalRing.residue (V.comap (algebraMap F₁ F₂))) qV) = 0 := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    have e4 := MvPolynomial.eval₂_comp_left (IsLocalRing.residue V)
      (comapInclusion V (algebraMap F₁ F₂)) y qV
    rw [h0, map_zero] at e4
    have e5 : (algebraMap (IsLocalRing.ResidueField (V.comap (algebraMap F₁ F₂)))
        (IsLocalRing.ResidueField V)).comp (IsLocalRing.residue (V.comap (algebraMap F₁ F₂))) =
        (IsLocalRing.residue V).comp (comapInclusion V (algebraMap F₁ F₂)) :=
      RingHom.ext fun r => IsLocalRing.ResidueField.map_residue _ r
    rw [e5]
    exact e4.symm
  have e6 := congrArg (AddMonoidAlgebra.coeff · m₀) (hx _ h1)
  rw [MvPolynomial.coeff_map, hcoeff, map_one, MvPolynomial.coeff_zero] at e6
  exact one_ne_zero e6

theorem residueTrdegLe : TRStatement := by
  intro F₁ F₂ _ _ _ V
  letI := residueAlgebra V (algebraMap F₁ F₂)
  unfold Algebra.trdeg
  refine ciSup_le' fun s => ?_
  have hy : ∀ a : s.1, ∃ v : V, IsLocalRing.residue V v = a :=
    fun a => IsLocalRing.residue_surjective (a : IsLocalRing.ResidueField V)
  choose y hy using hy
  have hs : AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap F₁ F₂)))
      (fun a => IsLocalRing.residue V (y a)) := by
    have : (fun a => IsLocalRing.residue V (y a)) = ((↑) : s.1 → IsLocalRing.ResidueField V) :=
      funext hy
    rw [this]
    exact s.2
  exact (algebraicIndependent_of_residue_lift V y hs).cardinalMk_le_trdeg

theorem integralClosureRank_and_residueTrdegLe : DedekindRankStatement ∧ TRStatement :=
  ⟨by intro O F L; intros; exact integralClosureRank O F L, residueTrdegLe⟩

end ReciprocityTheory.MultiplicativeHeights
end

section -- merged from ReciprocityTheory.SemistableReduction.ExistsTorusPointOneLeNormSum
namespace ReciprocityTheory.MultiplicativeHeights

open MvPolynomial

noncomputable abbrev unitBallRing (K : Type*) [NormedField K] [IsUltrametricDist K] :
    ValuationSubring K :=
  (NormedField.valuation (K := K)).valuationSubring

theorem mem_unitBallRing {K : Type*} [NormedField K] [IsUltrametricDist K] (x : K) :
    x ∈ unitBallRing K ↔ ‖x‖ ≤ 1 := by
  change ‖x‖₊ ≤ 1 ↔ ‖x‖ ≤ 1
  rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_one]

theorem residue_eq_zero_iff_norm_lt_one {K : Type*} [NormedField K] [IsUltrametricDist K]
    (x : unitBallRing K) :
    IsLocalRing.residue (unitBallRing K) x = 0 ↔ ‖(x : K)‖ < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hx1 : ‖(x : K)‖ ≤ 1 := (mem_unitBallRing (x : K)).1 x.2
  constructor
  · intro hnu
    refine lt_of_le_of_ne hx1 fun h1 => hnu ?_
    have hx0 : (x : K) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h1
      exact zero_ne_one h1
    have hinv : (x : K)⁻¹ ∈ unitBallRing K := by
      rw [mem_unitBallRing, norm_inv, h1, inv_one]
    have hm : x * ⟨(x : K)⁻¹, hinv⟩ = 1 := Subtype.ext (by simp [hx0])
    exact ⟨⟨x, ⟨(x : K)⁻¹, hinv⟩, hm, by rw [mul_comm]; exact hm⟩, rfl⟩
  · intro hlt hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have h := congrArg (fun t : unitBallRing K => ‖(t : K)‖) hy
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one, norm_mul, norm_one] at h
    have hy1 : ‖(y : K)‖ ≤ 1 := (mem_unitBallRing (y : K)).1 y.2
    nlinarith [norm_nonneg (x : K), norm_nonneg (y : K)]

theorem infinite_residues {K : Type*} [NormedField K] [IsUltrametricDist K] (K₀ : Subfield K)
    (hK₀ : ResidueFieldInfiniteOn (K₀ : Set K)) :
    {y : IsLocalRing.ResidueField (unitBallRing K) | ∃ x : unitBallRing K,
      (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧ IsLocalRing.residue _ x = y}.Infinite := by
  classical
  intro hfin
  have hrep : ∀ y ∈ {y : IsLocalRing.ResidueField (unitBallRing K) | ∃ x : unitBallRing K,
      (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧ IsLocalRing.residue _ x = y},
      ∃ x : unitBallRing K, (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧ IsLocalRing.residue _ x = y :=
    fun y hy => hy
  choose! r hr using hrep
  unfold ResidueFieldInfiniteOn at hK₀
  obtain ⟨x, hxK, hx1, hxs⟩ := hK₀ (insert 0 (hfin.toFinset.image fun y => (r y : K)))
  have hx0 : 1 ≤ ‖x‖ := by simpa using hxs 0 (Finset.mem_insert_self _ _)
  have hxn : ‖x‖ = 1 := le_antisymm hx1 hx0
  let xb : unitBallRing K := ⟨x, (mem_unitBallRing x).2 hx1⟩
  have hmem : IsLocalRing.residue _ xb ∈ {y : IsLocalRing.ResidueField (unitBallRing K) |
      ∃ x : unitBallRing K, (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧ IsLocalRing.residue _ x = y} :=
    ⟨xb, hxK, hxn, rfl⟩
  obtain ⟨-, -, hreq⟩ := hr _ hmem
  have h0 : IsLocalRing.residue _ (xb - r (IsLocalRing.residue _ xb)) = 0 := by
    rw [map_sub, hreq, sub_self]
  rw [residue_eq_zero_iff_norm_lt_one] at h0
  have h0' : ‖x - (r (IsLocalRing.residue _ xb) : K)‖ < 1 := by simpa [xb] using h0
  have h1 := hxs (r (IsLocalRing.residue _ xb) : K)
    (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨_, hfin.mem_toFinset.2 hmem, rfl⟩))
  linarith

theorem exists_torus_point_one_le_norm_sum {K : Type*} [NormedField K] [IsUltrametricDist K]
    (K₀ : Subfield K) (hK₀ : ResidueFieldInfiniteOn (K₀ : Set K)) {n : ℕ}
    (F : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → K) (ha : ∀ χ, ‖a χ‖ ≤ 1)
    (χ₀ : Fin n → ℤ) (hχ₀ : χ₀ ∈ F) (ha₀ : ‖a χ₀‖ = 1) :
    ∃ τ : Fin n → K, (∀ i, τ i ∈ K₀ ∧ ‖τ i‖ = 1) ∧
      1 ≤ ‖∑ χ ∈ F, a χ * ∏ i, τ i ^ χ i‖ := by
  classical
  let N : ℕ := ∑ χ ∈ F, ∑ i, (χ i).natAbs
  have hN : ∀ χ ∈ F, ∀ i, 0 ≤ χ i + N := by
    intro χ hχ i
    have h1 : (χ i).natAbs ≤ ∑ j, (χ j).natAbs :=
      Finset.single_le_sum (f := fun j => (χ j).natAbs) (fun j _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have h2 : ∑ j, (χ j).natAbs ≤ N :=
      Finset.single_le_sum (f := fun χ : Fin n → ℤ => ∑ j, (χ j).natAbs)
        (fun _ _ => Nat.zero_le _) hχ
    omega
  let e : (Fin n → ℤ) → (Fin n →₀ ℕ) := fun χ =>
    Finsupp.equivFunOnFinite.symm (fun i => (χ i + N).toNat)
  have he : ∀ χ ∈ F, ∀ χ' ∈ F, e χ = e χ' → χ = χ' := by
    intro χ hχ χ' hχ' h
    funext i
    have h3 := congrArg (fun f : Fin n →₀ ℕ => f i) h
    simp only [e, Finsupp.coe_equivFunOnFinite_symm] at h3
    have h1 := hN χ hχ i
    have h2 := hN χ' hχ' i
    omega
  let aO : (Fin n → ℤ) → unitBallRing K := fun χ => ⟨a χ, (mem_unitBallRing _).2 (ha χ)⟩
  let P : MvPolynomial (Fin n) (unitBallRing K) := ∑ χ ∈ F, monomial (e χ) (aO χ)
  have hcoeff : AddMonoidAlgebra.coeff P (e χ₀) = aO χ₀ := by
    simp only [P, coeff_sum, coeff_monomial]
    rw [Finset.sum_eq_single_of_mem χ₀ hχ₀]
    · simp
    · intro χ hχ hne
      rw [ite_eq_right]
      exact fun h => hne (he χ hχ χ₀ hχ₀ h)
  have hQ : MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) P ≠ 0 := by
    intro h0
    have h4 := congrArg (AddMonoidAlgebra.coeff · (e χ₀)) h0
    rw [coeff_map, hcoeff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
      residue_eq_zero_iff_norm_lt_one] at h4
    exact absurd ha₀ (ne_of_lt h4)
  obtain ⟨y, hy, hyne⟩ : ∃ y ∈ Set.pi Set.univ (fun _ : Fin n =>
      {y : IsLocalRing.ResidueField (unitBallRing K) | ∃ x : unitBallRing K,
        (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧ IsLocalRing.residue _ x = y}),
      eval y (MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) P) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hQ (funext_set _ (fun _ => infinite_residues K₀ hK₀) (fun x hx => by
      rw [hcon x hx, map_zero]))
  choose σ hσK hσ1 hσr using fun i => hy i (Set.mem_univ i)
  refine ⟨fun i => (σ i : K), fun i => ⟨hσK i, hσ1 i⟩, ?_⟩
  have hr : IsLocalRing.residue (unitBallRing K) (eval σ P) ≠ 0 := by
    have hy' : y = fun i => IsLocalRing.residue (unitBallRing K) (σ i) :=
      funext fun i => (hσr i).symm
    have h5 : eval y (MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) P) =
        IsLocalRing.residue (unitBallRing K) (eval σ P) := by
      rw [eval_map, hy', MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, hom_eval₂,
        RingHom.comp_id]
    rwa [h5] at hyne
  have hge : 1 ≤ ‖((eval σ P : unitBallRing K) : K)‖ :=
    not_lt.1 fun h => hr ((residue_eq_zero_iff_norm_lt_one _).2 h)
  have hσ0 : ∀ i, (σ i : K) ≠ 0 := fun i h => by
    have h6 := hσ1 i
    rw [h, norm_zero] at h6
    exact zero_ne_one h6
  have hval : ((eval σ P : unitBallRing K) : K) =
      ∑ χ ∈ F, a χ * ∏ i, (σ i : K) ^ (χ i + N).toNat := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [P, map_sum, eval_monomial]
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    simp [e, aO]
  have hterm : ∀ χ ∈ F, ∏ i, (σ i : K) ^ (χ i + N).toNat =
      (∏ i, (σ i : K) ^ χ i) * ∏ i, (σ i : K) ^ N := by
    intro χ hχ
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, Int.toNat_of_nonneg (hN χ hχ i), zpow_add₀ (hσ0 i), zpow_natCast]
  have hsum : ((eval σ P : unitBallRing K) : K) =
      (∑ χ ∈ F, a χ * ∏ i, (σ i : K) ^ χ i) * ∏ i, (σ i : K) ^ N := by
    rw [hval, Finset.sum_mul]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [hterm χ hχ, mul_assoc]
  have hnorm1 : ‖∏ i, (σ i : K) ^ N‖ = 1 := by
    rw [norm_prod]
    simp [norm_pow, hσ1]
  rw [hsum, norm_mul, hnorm1, mul_one] at hge
  exact hge

end ReciprocityTheory.MultiplicativeHeights
end

section -- merged from ReciprocityTheory.SemistableReduction.SJCoreB
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric Set Real

theorem integral_volumeIoiPow (k : ℕ) (g : ℝ → ℝ) :
    ∫ r : Ioi (0 : ℝ), g r ∂(Measure.volumeIoiPow k) = ∫ r in Ioi (0 : ℝ), r ^ k * g r := by
  rw [Measure.volumeIoiPow, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [← integral_subtype_comap measurableSet_Ioi (fun r : ℝ => r ^ k * g r)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (pow_nonneg (le_of_lt r.2) k)]

theorem integrable_volumeIoiPow {k : ℕ} {g : ℝ → ℝ}
    (h : IntegrableOn (fun r ↦ r ^ k * g r) (Ioi 0)) :
    Integrable (fun r : Ioi (0 : ℝ) ↦ g r) (Measure.volumeIoiPow k) := by
  rw [Measure.volumeIoiPow, integrable_withDensity_iff (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have h2 := (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mp h
  refine h2.congr (Filter.Eventually.of_forall fun r => ?_)
  simp only [Function.comp_apply]
  rw [ENNReal.toReal_ofReal (pow_nonneg (le_of_lt r.2) k), mul_comm]

theorem finrank_euclidean_complex (n : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) = 2 * n := by
  rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, finrank_euclideanSpace,
    Fintype.card_fin]

private theorem homeomorphUnitSphereProd_smul_eq {n : ℕ} (x : ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n)))) :
    ((homeomorphUnitSphereProd _ x).2 : ℝ) •
      ((homeomorphUnitSphereProd _ x).1 : EuclideanSpace ℂ (Fin n)) = x := by
  have hx : ‖(x : EuclideanSpace ℂ (Fin n))‖ ≠ 0 := norm_ne_zero_iff.mpr x.2
  simp [homeomorphUnitSphereProd, homeomorphSphereProd, smul_smul, hx]

theorem integral_polar {n : ℕ} (hn : 0 < n) (f : EuclideanSpace ℂ (Fin n) → ℝ) :
    ∫ x, f x = ∫ p : UnitSphereC n × Ioi (0 : ℝ), f (p.2.1 • (p.1 : EuclideanSpace ℂ (Fin n)))
      ∂((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) - 1))) := by
  rw [← (Measure.measurePreserving_homeomorphUnitSphereProd
      (volume : Measure (EuclideanSpace ℂ (Fin n)))).integral_comp
      (homeomorphUnitSphereProd _).measurableEmbedding
      (fun p : UnitSphereC n × Ioi (0 : ℝ) ↦ f (p.2.1 • (p.1 : EuclideanSpace ℂ (Fin n))))]
  simp only [homeomorphUnitSphereProd_smul_eq]
  rw [integral_subtype_comap (measurableSet_singleton 0).compl
    (fun x : EuclideanSpace ℂ (Fin n) ↦ f x)]
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclidean_complex]; omega)
  rw [Measure.restrict_congr_set (show ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))) =ᵐ[volume] univ from
    ae_eq_univ.mpr (by rw [compl_compl]; exact measure_singleton 0)), Measure.restrict_univ]

theorem integrable_polar (n : ℕ) {f : EuclideanSpace ℂ (Fin n) → ℝ} (hf : Integrable f) :
    Integrable (fun p : UnitSphereC n × Ioi (0 : ℝ) ↦ f (p.2.1 • (p.1 : EuclideanSpace ℂ (Fin n))))
      ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) - 1))) := by
  rw [← (Measure.measurePreserving_homeomorphUnitSphereProd
      (volume : Measure (EuclideanSpace ℂ (Fin n)))).integrable_comp_emb
      (homeomorphUnitSphereProd _).measurableEmbedding]
  have h2 := (integrableOn_iff_comap_subtypeVal (measurableSet_singleton
    (0 : EuclideanSpace ℂ (Fin n))).compl).mp hf.integrableOn
  refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply, homeomorphUnitSphereProd_smul_eq]

def conjVec {n : ℕ} (c : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ star (WithLp.ofLp c i))

theorem inner_conjVec {n : ℕ} (c x : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (conjVec c) x = ∑ i, WithLp.ofLp c i * WithLp.ofLp x i := by
  simp [conjVec, PiLp.inner_apply, mul_comm]

theorem norm_conjVec {n : ℕ} (c : EuclideanSpace ℂ (Fin n)) : ‖conjVec c‖ = ‖c‖ := by
  simp [conjVec, EuclideanSpace.norm_eq]

theorem sphere_linear_zero_null {n : ℕ} (c : EuclideanSpace ℂ (Fin n)) (hc : c ≠ 0) :
    (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere
      {z : UnitSphereC n | ∑ i, WithLp.ofLp c i * spherePoint z i = 0} = 0 := by
  let K : Submodule ℝ (EuclideanSpace ℂ (Fin n)) :=
    (LinearMap.ker (innerₛₗ ℂ (conjVec c))).restrictScalars ℝ
  have hK : K ≠ ⊤ := by
    intro h
    have hm : conjVec c ∈ K := h ▸ Submodule.mem_top
    have hm' : inner ℂ (conjVec c) (conjVec c) = 0 := hm
    rw [inner_self_eq_zero] at hm'
    exact hc (by rw [← norm_eq_zero, ← norm_conjVec c, hm', norm_zero])
  have hset : {z : UnitSphereC n | ∑ i, WithLp.ofLp c i * spherePoint z i = 0} =
      {z : UnitSphereC n | inner ℂ (conjVec c) (z : EuclideanSpace ℂ (Fin n)) = 0} := by
    ext z
    simp only [Set.mem_setOf_eq, spherePoint, inner_conjVec]
  have hs : MeasurableSet
      {z : UnitSphereC n | inner ℂ (conjVec c) (z : EuclideanSpace ℂ (Fin n)) = 0} :=
    (isClosed_eq (continuous_const.inner continuous_subtype_val) continuous_const).measurableSet
  rw [hset, Measure.toSphere_apply' _ hs,
    measure_mono_null ?_ (Measure.addHaar_submodule _ K hK), mul_zero]
  rintro _ ⟨t, -, _, ⟨z, hz, rfl⟩, rfl⟩
  exact K.smul_mem t hz

def gaussLogC (a : ℝ) : ℝ := ∫ z : ℂ, log (a * ‖z‖) * exp (-‖z‖ ^ 2)

def gaussOneC : ℝ := ∫ z : ℂ, exp (-‖z‖ ^ 2)

private theorem integrableOn_rpow_mul_exp_neg_sq_Ioi (s : ℝ) (hs : -1 < s) :
    IntegrableOn (fun y : ℝ ↦ y ^ s * exp (-1 * y ^ 2)) (Ioi 0) :=
  integrableOn_rpow_mul_exp_neg_mul_sq one_pos hs

theorem integrable_gaussOneC : Integrable (fun z : ℂ ↦ exp (-‖z‖ ^ 2)) := by
  refine (integrable_fun_norm_addHaar volume (f := fun y : ℝ ↦ exp (-y ^ 2))).mpr ?_
  have hd : Module.finrank ℝ ℂ - 1 = 1 := by simp [Complex.finrank_real_complex]
  simp only [hd, pow_one, smul_eq_mul]
  refine (integrableOn_rpow_mul_exp_neg_sq_Ioi 1 (by norm_num)).congr_fun
    (fun y _ ↦ by simp [Real.rpow_one]) measurableSet_Ioi

private theorem mul_abs_log_mul_le {a : ℝ} (ha : 0 < a) (y : ℝ) (hy : 0 < y) :
    y * |log (a * y)| ≤ |log a| * y ^ (1 : ℝ) + 2 * y ^ (3 / 2 : ℝ) + 2 * y ^ (1 / 2 : ℝ) := by
  have h1 : log y ≤ 2 * y ^ (1 / 2 : ℝ) := by
    have := Real.log_le_rpow_div hy.le (show (0 : ℝ) < 1 / 2 by norm_num)
    linarith
  have h2 : -log y ≤ 2 * y ^ (-1 / 2 : ℝ) := by
    have := Real.log_le_rpow_div (inv_pos.mpr hy).le (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [Real.log_inv, Real.inv_rpow hy.le, ← Real.rpow_neg hy.le] at this
    have e : (-(1 / 2 : ℝ)) = -1 / 2 := by norm_num
    rw [e] at this
    linarith
  have p1 := Real.rpow_nonneg hy.le (1 / 2 : ℝ)
  have p2 := Real.rpow_nonneg hy.le (-1 / 2 : ℝ)
  have habs : |log y| ≤ 2 * y ^ (1 / 2 : ℝ) + 2 * y ^ (-1 / 2 : ℝ) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hlog : |log (a * y)| ≤ |log a| + |log y| := by
    rw [Real.log_mul ha.ne' hy.ne']; exact abs_add_le _ _
  have e1 : y * y ^ (1 / 2 : ℝ) = y ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hy, Real.rpow_one]
  have e2 : y * y ^ (-1 / 2 : ℝ) = y ^ (1 / 2 : ℝ) := by
    rw [show (1 / 2 : ℝ) = 1 + (-1 / 2) by norm_num, Real.rpow_add hy, Real.rpow_one]
  calc y * |log (a * y)| ≤ y * (|log a| + (2 * y ^ (1 / 2 : ℝ) + 2 * y ^ (-1 / 2 : ℝ))) := by
        gcongr; exact hlog.trans (by linarith)
    _ = |log a| * y ^ (1 : ℝ) + 2 * y ^ (3 / 2 : ℝ) + 2 * y ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_one]; linear_combination 2 * e1 + 2 * e2

theorem integrable_gaussLogC {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : ℂ ↦ log (a * ‖z‖) * exp (-‖z‖ ^ 2)) := by
  refine (integrable_fun_norm_addHaar volume
    (f := fun y : ℝ ↦ log (a * y) * exp (-y ^ 2))).mpr ?_
  have hd : Module.finrank ℝ ℂ - 1 = 1 := by simp [Complex.finrank_real_complex]
  simp only [hd, pow_one, smul_eq_mul]
  have hg : IntegrableOn (fun y : ℝ ↦ (|log a| * y ^ (1 : ℝ) + 2 * y ^ (3 / 2 : ℝ) +
      2 * y ^ (1 / 2 : ℝ)) * exp (-1 * y ^ 2)) (Ioi 0) := by
    have := (((integrableOn_rpow_mul_exp_neg_sq_Ioi 1 (by norm_num)).const_mul |log a|).add
      ((integrableOn_rpow_mul_exp_neg_sq_Ioi (3 / 2) (by norm_num)).const_mul 2)).add
      ((integrableOn_rpow_mul_exp_neg_sq_Ioi (1 / 2) (by norm_num)).const_mul 2)
    refine this.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun y _ ↦ ?_)
    simp only [Pi.add_apply]
    ring
  refine Integrable.mono' hg (by fun_prop) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy ↦ ?_
  have hy' : (0 : ℝ) < y := hy
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hy', abs_of_pos (exp_pos _), neg_one_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_abs_log_mul_le ha y hy') (exp_pos _).le

end ReciprocityTheory.MultiplicativeHeights
end
end
