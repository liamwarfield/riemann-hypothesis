module

public import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.RApprox

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.AlgebraicIndependentResidueIffGauss
namespace GlobalTheory

open MvPolynomial

theorem residue_valuationSubring_ne_zero_iff {U Γ : Type*} [Field U]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation U Γ) (x : v.valuationSubring) :
    IsLocalRing.residue v.valuationSubring x ≠ 0 ↔ v (x : U) = 1 := by
  rw [IsLocalRing.residue_ne_zero_iff_isUnit, ValuationSubring.valuation_eq_one_iff]
  exact (Valuation.isEquiv_valuation_valuationSubring v).symm.eq_one_iff_eq_one

private theorem residue_eval₂_comap {F U : Type} [Field F] [Field U] (f : F →+* U)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (σ : Type) (t : σ → U)
    (ht : ∀ s, t s ∈ v.valuationSubring) (p : MvPolynomial σ (v.valuationSubring.comap f)) :
    IsLocalRing.residue v.valuationSubring
        (MvPolynomial.eval₂ (ReciprocityTheory.MultiplicativeHeights.comapInclusion v.valuationSubring f)
          (fun s => ⟨t s, ht s⟩) p) =
      @MvPolynomial.aeval _ _ _ _ _
        (ReciprocityTheory.MultiplicativeHeights.residueAlgebra v.valuationSubring f)
        (fun s => IsLocalRing.residue v.valuationSubring ⟨t s, ht s⟩)
        (MvPolynomial.map (IsLocalRing.residue (v.valuationSubring.comap f)) p) := by
  let := ReciprocityTheory.MultiplicativeHeights.residueAlgebra v.valuationSubring f
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval₂_comp_left]
  congr 1

private theorem coe_eval₂_comapInclusion_eq_eval₂_map {F U : Type} [Field F] [Field U] (f : F →+* U)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (σ : Type) (t : σ → U)
    (ht : ∀ s, t s ∈ v.valuationSubring) (p : MvPolynomial σ (v.valuationSubring.comap f)) :
    ((MvPolynomial.eval₂ (ReciprocityTheory.MultiplicativeHeights.comapInclusion v.valuationSubring f)
          (fun s => (⟨t s, ht s⟩ : v.valuationSubring)) p : v.valuationSubring) : U) =
      MvPolynomial.eval₂ f t (MvPolynomial.map (v.valuationSubring.comap f).subtype p) := by
  rw [MvPolynomial.eval₂_map]
  exact MvPolynomial.eval₂_comp_left v.valuationSubring.subtype _ _ p

private theorem residue_comap_ne_zero_iff_valuation_eq_one {F U : Type} [Field F] [Field U] (f : F →+* U)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (c : v.valuationSubring.comap f) :
    IsLocalRing.residue (v.valuationSubring.comap f) c ≠ 0 ↔ v (f c) = 1 := by
  have h := residue_valuationSubring_ne_zero_iff v (ReciprocityTheory.MultiplicativeHeights.comapInclusion v.valuationSubring f c)
  rw [← IsLocalRing.ResidueField.map_residue, map_ne_zero] at h
  exact h

theorem algebraicIndependent_residue_iff_gauss (F U : Type) [Field F] [Field U] (f : F →+* U)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (σ : Type) (t : σ → U)
    (ht : ∀ s, t s ∈ v.valuationSubring) :
    (letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra v.valuationSubring f
     AlgebraicIndependent (IsLocalRing.ResidueField (v.valuationSubring.comap f))
      (fun s => IsLocalRing.residue v.valuationSubring ⟨t s, ht s⟩)) ↔
    ∀ p : MvPolynomial σ F, (∀ α, v (f (p.coeff α)) ≤ 1) → (∃ α, v (f (p.coeff α)) = 1) →
      v (MvPolynomial.eval₂ f t p) = 1 := by
  let := ReciprocityTheory.MultiplicativeHeights.residueAlgebra v.valuationSubring f
  rw [algebraicIndependent_iff]
  constructor
  · intro hind p hle hone
    obtain ⟨q, rfl⟩ : p ∈ Set.range (MvPolynomial.map (v.valuationSubring.comap f).subtype) := by
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro c hc
      obtain ⟨α, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
      exact ⟨⟨p.coeff α, ValuationSubring.mem_comap.mpr ((v.mem_valuationSubring_iff _).mpr (hle α))⟩, rfl⟩
    obtain ⟨α, hα⟩ := hone
    rw [MvPolynomial.coeff_map] at hα
    rw [← coe_eval₂_comapInclusion_eq_eval₂_map f v σ t ht q, ← residue_valuationSubring_ne_zero_iff, residue_eval₂_comap]
    intro h0
    have hq := congrArg (AddMonoidAlgebra.coeff · α) (hind _ h0)
    rw [MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero] at hq
    exact (residue_comap_ne_zero_iff_valuation_eq_one f v (q.coeff α)).mpr hα hq
  · intro hg r hr
    by_contra hne
    obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective _ IsLocalRing.residue_surjective r
    obtain ⟨α, hα⟩ := MvPolynomial.ne_zero_iff.mp hne
    rw [MvPolynomial.coeff_map] at hα
    have hle : ∀ β, v (f ((MvPolynomial.map (v.valuationSubring.comap f).subtype q).coeff β)) ≤ 1 := by
      intro β
      rw [MvPolynomial.coeff_map]
      exact (v.mem_valuationSubring_iff _).mp (ValuationSubring.mem_comap.mp (q.coeff β).2)
    have h1 := hg _ hle ⟨α, by
      rw [MvPolynomial.coeff_map]
      exact (residue_comap_ne_zero_iff_valuation_eq_one f v (q.coeff α)).mp hα⟩
    rw [← coe_eval₂_comapInclusion_eq_eval₂_map f v σ t ht q, ← residue_valuationSubring_ne_zero_iff, residue_eval₂_comap] at h1
    exact h1 hr

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IntegralElementsGenericLinearSectionGaussPoint
namespace GlobalTheory.GaussSection

open MvPolynomial

theorem eval_mem_closure {Ω U σ : Type} [Field Ω] [Field U] (f : Ω →+* U)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (t : σ → U) (S : Set U)
    (hS : ∀ s, t s ∈ S) (p : MvPolynomial σ Ω) (hp : ∀ α, v (f (p.coeff α)) ≤ 1) :
    eval₂ f t p ∈ Subring.closure ({u | u ∈ Set.range f ∧ v u ≤ 1} ∪ S) := by
  rw [MvPolynomial.eval₂_eq]
  apply sum_mem
  intro α _
  apply mul_mem
  · exact Subring.subset_closure (Or.inl ⟨Set.mem_range_self _, hp α⟩)
  · apply prod_mem
    intro i _
    exact pow_mem (Subring.subset_closure (Set.mem_union_right _ (hS i))) _

theorem exists_normalise {Ω U σ : Type} [Field Ω] [Field U] (f : Ω →+* U)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (p : MvPolynomial σ Ω) (hp : p ≠ 0) :
    ∃ (c : Ω) (q : MvPolynomial σ Ω), c ≠ 0 ∧ p = C c * q ∧ (∀ α, v (f (q.coeff α)) ≤ 1) ∧
      ∃ α, v (f (q.coeff α)) = 1 := by
  classical
  obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp hp
  obtain ⟨α₀, hα₀, hmax⟩ := p.support.exists_max_image (fun α => v (f (p.coeff α)))
    ⟨d, MvPolynomial.mem_support_iff.mpr hd⟩
  have hc : p.coeff α₀ ≠ 0 := MvPolynomial.mem_support_iff.mp hα₀
  have hfc : 0 < v (f (p.coeff α₀)) := by
    rw [zero_lt_iff, Ne, Valuation.zero_iff, map_eq_zero]
    exact hc
  refine ⟨p.coeff α₀, C (p.coeff α₀)⁻¹ * p, hc, ?_, fun α => ?_, α₀, ?_⟩
  · rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]
  · rw [coeff_C_mul, map_mul, map_mul, map_inv₀, map_inv₀, inv_mul_le_iff₀ hfc, mul_one]
    by_cases hα : α ∈ p.support
    · exact hmax α hα
    · rw [MvPolynomial.notMem_support_iff.mp hα, map_zero, map_zero]
      exact zero_le
  · rw [coeff_C_mul, inv_mul_cancel₀ hc, map_one, map_one]

theorem quotient_of_gauss {Ω U σ : Type} [Field Ω] [Field U] (f : Ω →+* U)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (t : σ → U) (S : Set U)
    (hS : ∀ s, t s ∈ S) (hS' : ∀ u ∈ S, ∃ p : MvPolynomial σ Ω, eval₂ f t p = u)
    (hG : ∀ p : MvPolynomial σ Ω, (∀ α, v (f (p.coeff α)) ≤ 1) → (∃ α, v (f (p.coeff α)) = 1) →
      v (eval₂ f t p) = 1)
    (g : U) (hg : g ∈ Subfield.closure (Set.range f ∪ S)) (hv : v g ≤ 1) :
    ∃ a ∈ Subring.closure ({u | u ∈ Set.range f ∧ v u ≤ 1} ∪ S),
      ∃ d ∈ Subring.closure ({u | u ∈ Set.range f ∧ v u ≤ 1} ∪ S), v d = 1 ∧ g * d = a := by
  classical
  by_cases hg0 : g = 0
  · exact ⟨0, zero_mem _, 1, one_mem _, map_one v, by rw [hg0, zero_mul]⟩
  have hle : Subring.closure (Set.range f ∪ S) ≤ (MvPolynomial.eval₂Hom f t).range := by
    rw [Subring.closure_le]
    rintro u (⟨c, rfl⟩ | hu)
    · exact ⟨C c, by simp⟩
    · obtain ⟨p, hp⟩ := hS' u hu
      exact ⟨p, hp⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.mp hg
  obtain ⟨P, rfl⟩ := hle hy
  obtain ⟨Q, rfl⟩ := hle hz
  simp only [MvPolynomial.coe_eval₂Hom] at hg0 hv ⊢
  have hz0 : eval₂ f t Q ≠ 0 := fun h => hg0 (by rw [h, div_zero])
  have hy0 : eval₂ f t P ≠ 0 := fun h => hg0 (by rw [h, zero_div])
  have hQ : Q ≠ 0 := by
    rintro rfl
    exact hz0 (eval₂_zero _ _)
  have hP : P ≠ 0 := by
    rintro rfl
    exact hy0 (eval₂_zero _ _)
  obtain ⟨c, Q', hc, rfl, hQi, hQu⟩ := exists_normalise f v Q hQ
  obtain ⟨c', P', -, rfl, hPi, hPu⟩ := exists_normalise f v P hP
  have hdQ := hG Q' hQi hQu
  have hdP := hG P' hPi hPu
  have hfc : f c ≠ 0 := (map_ne_zero f).mpr hc
  have hQ0 : eval₂ f t Q' ≠ 0 := by
    intro h
    rw [h, map_zero] at hdQ
    exact zero_ne_one hdQ
  simp only [eval₂_mul, eval₂_C] at hv ⊢
  refine ⟨f (c' / c) * eval₂ f t P',
    mul_mem (Subring.subset_closure (Or.inl ⟨Set.mem_range_self _, ?_⟩))
      (eval_mem_closure f v t S hS P' hPi),
    eval₂ f t Q', eval_mem_closure f v t S hS Q' hQi, hdQ, ?_⟩
  · have : v (f (c' / c)) = v (f c' * eval₂ f t P' / (f c * eval₂ f t Q')) := by
      rw [map_div₀, map_div₀, map_div₀, map_mul, map_mul, hdP, hdQ, mul_one, mul_one]
    rw [this]
    exact hv
  · rw [map_div₀]
    field_simp

private theorem algebraicIndependent_congr_algebra {ι R S : Type*} [CommRing R] [CommRing S] (x : ι → S)
    (A₁ A₂ : Algebra R S) (h : ∀ r, (letI := A₁; algebraMap R S r) = (letI := A₂; algebraMap R S r))
    (hx : letI := A₁; AlgebraicIndependent R x) : letI := A₂; AlgebraicIndependent R x := by
  obtain rfl := Algebra.algebra_ext A₁ A₂ h
  exact hx

theorem indep_comp {K Ω U τ : Type} [Field K] [Field Ω] [Field U] [Algebra K Ω] [Algebra Ω U]
    (v : Valuation U (WithZero (Multiplicative ℤ))) (s : τ → U)
    (hs : ∀ j, s j ∈ v.valuationSubring)
    (hG : ∀ p : MvPolynomial τ K, (∀ α, v (algebraMap Ω U (algebraMap K Ω (p.coeff α))) ≤ 1) →
      (∃ α, v (algebraMap Ω U (algebraMap K Ω (p.coeff α))) = 1) →
      v (eval₂ ((algebraMap Ω U).comp (algebraMap K Ω)) s p) = 1) :
    letI _iW := ReciprocityTheory.MultiplicativeHeights.residueAlgebra v.valuationSubring (algebraMap Ω U)
    letI _io := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (v.valuationSubring.comap (algebraMap Ω U))
      (algebraMap K Ω)
    letI : Algebra (IsLocalRing.ResidueField
        ((v.valuationSubring.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
        (IsLocalRing.ResidueField v.valuationSubring) :=
      ((algebraMap _ (IsLocalRing.ResidueField v.valuationSubring)).comp
        (algebraMap _ (IsLocalRing.ResidueField
          (v.valuationSubring.comap (algebraMap Ω U))))).toAlgebra
    AlgebraicIndependent
      (IsLocalRing.ResidueField
        ((v.valuationSubring.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
      (fun j => IsLocalRing.residue v.valuationSubring ⟨s j, hs j⟩) := by
  refine algebraicIndependent_congr_algebra _
    (ReciprocityTheory.MultiplicativeHeights.residueAlgebra v.valuationSubring ((algebraMap Ω U).comp (algebraMap K Ω))) _ ?_
    ((GlobalTheory.algebraicIndependent_residue_iff_gauss K U _ v τ s hs).mpr hG)
  intro r
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
  rfl

theorem integral_elements (K Ω U : Type) [Field K] [Field Ω] [Field U] [Algebra K Ω]
    (f : Ω →+* U) (D N : ℕ) (hD : Algebra.trdeg K Ω = D)
    (v : Valuation U (WithZero (Multiplicative ℤ))) (s : Fin (D + 1) × Fin N → U)
    (a : Fin N → Ω) (ha : ∃ k, a k ≠ 0)
    (hrel : ∀ i : Fin D, ∑ k, s (i.succ, k) * f (a k) = 0) (hs : ∀ p, v (s p) ≤ 1)
    (hG : ∀ p : MvPolynomial (Fin (D + 1) × Fin N) K,
      (∀ α, v (f (algebraMap K Ω (p.coeff α))) ≤ 1) →
      (∃ α, v (f (algebraMap K Ω (p.coeff α))) = 1) →
      v (MvPolynomial.eval₂ (f.comp (algebraMap K Ω)) s p) = 1) :
    ∀ g ∈ Subfield.closure (Set.range f ∪ Set.range s), v g ≤ 1 →
      ∃ a ∈ Subring.closure ({u | u ∈ Set.range f ∧ v u ≤ 1} ∪ Set.range s),
        ∃ d ∈ Subring.closure ({u | u ∈ Set.range f ∧ v u ≤ 1} ∪ Set.range s),
          v d = 1 ∧ g * d = a := by
  intro g hg hv
  classical
  let _ : Algebra Ω U := f.toAlgebra
  obtain ⟨k₁, hk₁⟩ := ha
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_max_image Finset.univ (fun k => v (f (a k)))
    ⟨k₁, Finset.mem_univ _⟩
  have ha₀ : a k₀ ≠ 0 := by
    intro h0
    have h := hk₀ k₁ (Finset.mem_univ _)
    rw [h0, map_zero, map_zero, le_zero_iff, Valuation.zero_iff, map_eq_zero] at h
    exact hk₁ h
  have hfa : f (a k₀) ≠ 0 := (map_ne_zero f).mpr ha₀
  have hva : 0 < v (f (a k₀)) := by
    rw [zero_lt_iff, Ne, Valuation.zero_iff]
    exact hfa
  have hsV : ∀ j, s j ∈ v.valuationSubring := hs
  set t : Fin N ⊕ (Fin D × {k : Fin N // k ≠ k₀}) → U :=
    Sum.elim (fun k => s (0, k)) (fun q => s (q.1.succ, q.2.1)) with ht_def
  have ht : ∀ x, t x ∈ v.valuationSubring := by
    rintro (k | q)
    · exact hsV _
    · exact hsV _
  have hcoefX : ∀ (x : Fin N ⊕ (Fin D × {k : Fin N // k ≠ k₀})) α,
      (X x : MvPolynomial _ Ω).coeff α ∈ v.valuationSubring.comap (algebraMap Ω U) := by
    intro x α
    rw [coeff_X]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hex : ∀ j : Fin (D + 1) × Fin N, ∃ q : MvPolynomial (Fin N ⊕ (Fin D × {k : Fin N // k ≠ k₀})) Ω,
      (∀ α, q.coeff α ∈ v.valuationSubring.comap (algebraMap Ω U)) ∧ MvPolynomial.aeval t q = s j := by
    rintro ⟨i, k⟩
    obtain rfl | ⟨i', rfl⟩ := Fin.eq_zero_or_eq_succ i
    · exact ⟨X (Sum.inl k), hcoefX _, by rw [aeval_X]; rfl⟩
    by_cases hk : k = k₀
    · rw [hk]
      refine ⟨∑ q : {k : Fin N // k ≠ k₀}, C (-(a q / a k₀)) * X (Sum.inr (i', q)), fun α => ?_, ?_⟩
      · rw [coeff_sum]
        refine sum_mem fun q _ => ?_
        rw [coeff_C_mul]
        refine mul_mem (neg_mem ?_) (hcoefX _ _)
        rw [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff,
          RingHom.algebraMap_toAlgebra, map_div₀, map_div₀, div_le_one₀ hva]
        exact hk₀ q (Finset.mem_univ _)
      · have hr := hrel i'
        rw [Fintype.sum_eq_add_sum_subtype_ne _ k₀] at hr
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_mul, aeval_C, aeval_X, RingHom.algebraMap_toAlgebra]
        have key : ∑ q : {k : Fin N // k ≠ k₀}, f (-(a q / a k₀)) * t (Sum.inr (i', q)) =
            -(∑ q : {k : Fin N // k ≠ k₀}, s (i'.succ, q.1) * f (a q)) / f (a k₀) := by
          rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [map_neg, map_div₀]
          simp only [ht_def, Sum.elim_inr]
          ring
        rw [key, div_eq_iff hfa]
        linear_combination -hr
    · exact ⟨X (Sum.inr (i', ⟨k, hk⟩)), hcoefX _, by rw [aeval_X]; rfl⟩
  choose P hPc hPe using hex
  have hcard : Fintype.card (Fin (D + 1) × Fin N) =
      Fintype.card (Fin N ⊕ (Fin D × {k : Fin N // k ≠ k₀})) + D := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by have := k₀.pos; omega⟩
    simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_subtype_compl,
      Fintype.card_unique]
    simp only [Nat.add_sub_cancel]
    ring
  have hind := indep_comp (K := K) (Ω := Ω) (U := U) v s hsV hG
  obtain ⟨-, -, h3⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.residueTrdeg K Ω U D hD
    (Fin N ⊕ (Fin D × {k : Fin N // k ≠ k₀})) t v.valuationSubring ht
    (Fin (D + 1) × Fin N) (fun j => ⟨s j, hsV j⟩) P hPc hcard hPe hind
  have hGΩ := (GlobalTheory.algebraicIndependent_residue_iff_gauss Ω U f v _ t ht).mp h3
  refine quotient_of_gauss f v t (Set.range s) ?_ ?_ hGΩ g hg hv
  · rintro (k | q)
    · exact ⟨(0, k), rfl⟩
    · exact ⟨(q.1.succ, q.2.1), rfl⟩
  · rintro u ⟨j, rfl⟩
    exact ⟨P j, (MvPolynomial.aeval_def _ _).symm.trans (hPe j)⟩

end GlobalTheory.GaussSection
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IntegralElementsGenericLinearSectionGaussPointStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_elements_generic_linear_section_gauss_point : ∀ (K Ω U : Type) [Field K] [Field Ω] [Field U] [Algebra K Ω] (f : Ω →+* U) (D N : ℕ), Algebra.trdeg K Ω = D → ∀ (v : Valuation U (WithZero (Multiplicative ℤ))) (t : Fin (D + 1) × Fin N → U) (x : Fin N → Ω), (∃ k, x k ≠ 0) → (∀ i : Fin D, ∑ k, t (i.succ, k) * f (x k) = 0) → (∀ p, v (t p) ≤ 1) → (∀ p : MvPolynomial (Fin (D + 1) × Fin N) K, (∀ α, v (f (algebraMap K Ω (p.coeff α))) ≤ 1) → (∃ α, v (f (algebraMap K Ω (p.coeff α))) = 1) → v (MvPolynomial.eval₂ (f.comp (algebraMap K Ω)) t p) = 1) → ∀ g ∈ Subfield.closure (Set.range f ∪ Set.range t), v g ≤ 1 → ∃ a ∈ Subring.closure ({u | u ∈ Set.range f ∧ v u ≤ 1} ∪ Set.range t), ∃ d ∈ Subring.closure ({u | u ∈ Set.range f ∧ v u ≤ 1} ∪ Set.range t), v d = 1 ∧ g * d = a := by
  first | exact @GlobalTheory.GaussSection.integral_elements | exact GlobalTheory.GaussSection.integral_elements | (intros; apply GlobalTheory.GaussSection.integral_elements <;> assumption)
end
