module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubgroupAverageLinearTranslateConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulHomInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalConjugationInvolutiveValuationPreserving
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftedCapelliDeterminantSubleadingCoeffTrace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftedCapelliDeterminantSubleadingCoeffTrace
namespace GlobalTheory.CapelliNext

open Finset

variable {A : Type} [Ring A] [Algebra ℂ A]

def shiftCoeff (d : ℕ) (p q : A) (c : ℕ → A) : ℕ → A :=
  fun i => (Nat.casesOn i 0 (fun j => p * c j) : A) + (if i < d + 1 then q * c i else 0)

theorem affine_mul_eq (d : ℕ) (p q : A) (c : ℕ → A) (u : ℂ) :
    (u • p + q) * (∑ i ∈ range (d + 1), u ^ i • c i)
      = ∑ i ∈ range (d + 1 + 1), u ^ i • shiftCoeff d p q c i := by
  unfold shiftCoeff
  simp only [smul_add, sum_add_distrib, add_mul]
  congr 1
  · rw [sum_range_succ' _ (d + 1), mul_sum]
    simp only [Nat.rec_zero, smul_zero, add_zero]
    refine sum_congr rfl fun i _ => ?_
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ]
  · rw [sum_range_succ _ (d + 1), mul_sum]
    simp only [lt_irrefl, if_false, smul_zero, add_zero]
    refine sum_congr rfl fun i hi => ?_
    rw [if_pos (mem_range.mp hi), mul_smul_comm]

theorem prod_affine_two_top (t : ℕ) (p : Fin (t + 1) → ℂ) (q : Fin (t + 1) → A) :
    ∃ c : ℕ → A, c (t + 1) = (∏ k, p k) • (1 : A) ∧
      c t = ∑ k, (∏ j, (if j = k then (1 : ℂ) else p j)) • q k ∧
      ∀ u : ℂ, (List.ofFn fun k => (u * p k) • (1 : A) + q k).prod
        = ∑ i ∈ range (t + 1 + 1), u ^ i • c i := by
  induction t with
  | zero =>
    let c : ℕ → A := fun i => if i = 0 then q 0 else if i = 1 then (p 0) • (1 : A) else 0
    refine ⟨c, ?_, ?_, fun u => ?_⟩
    · simp [c]
    · simp [c]
    · simp [c, sum_range_succ, add_comm]
      rw [mul_smul]
  | succ t ih =>
    obtain ⟨c, hc1, hc0, hc⟩ := ih (fun k => p k.succ) (fun k => q k.succ)
    refine ⟨shiftCoeff (t + 1) (p 0 • (1 : A)) (q 0) c, ?_, ?_, fun u => ?_⟩
    · simp only [shiftCoeff, lt_irrefl, if_false, add_zero]
      rw [hc1, smul_one_mul, smul_smul, ← Fin.prod_univ_succ]
    · simp only [shiftCoeff, lt_add_iff_pos_right, Nat.lt_add_one, if_true]
      rw [hc0, hc1, smul_one_mul, mul_smul_comm, mul_one, smul_sum, add_comm]
      conv_rhs => rw [Fin.sum_univ_succ]
      congr 1
      · simp [Fin.prod_univ_succ, smul_mul_assoc]
      · refine sum_congr rfl fun k _ => ?_
        simp [Fin.prod_univ_succ, Fin.succ_ne_zero, smul_smul, (Fin.succ_ne_zero _).symm]
    · rw [List.ofFn_succ, List.prod_cons, hc u]
      have : (u * p 0) • (1 : A) + q 0 = u • (p 0 • (1 : A)) + q 0 := by rw [smul_smul]
      rw [this, affine_mul_eq]

end GlobalTheory.CapelliNext

namespace GlobalTheory.CapelliNext
open Finset

theorem qdet_shift_next_coeff : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (s : ℂ), ∃ (c : ℕ → A) (t : ℂ),
    c (m + 1) = 1 ∧ c m = ∑ i, E i i + t • (1 : A) ∧
      ∀ u : ℂ, Formalism.REAL.qdet E (u - s) = ∑ k ∈ Finset.range (m + 1 + 1), u ^ k • c k := by
  intro A _ _ m E s
  have h : ∀ σ : Equiv.Perm (Fin (m + 1)), ∃ c : ℕ → A,
      c (m + 1) = (∏ k, (if σ k = k then (1 : ℂ) else 0)) • (1 : A) ∧
      c m = ∑ k, (∏ j, (if j = k then (1 : ℂ) else (if σ j = j then (1 : ℂ) else 0))) •
        ((if σ k = k then algebraMap ℂ A (-s - ((k : ℕ) : ℂ)) else 0) + E (σ k) k) ∧
      ∀ u : ℂ, (List.ofFn fun k : Fin (m + 1) => Formalism.REAL.Tm E (u - s - ((k : ℕ) : ℂ)) (id (σ k)) (id k)).prod
        = ∑ i ∈ range (m + 1 + 1), u ^ i • c i := by
    intro σ
    obtain ⟨c, hc1, hc0, hc⟩ := prod_affine_two_top m (fun k => if σ k = k then (1 : ℂ) else 0)
      (fun k => (if σ k = k then algebraMap ℂ A (-s - ((k : ℕ) : ℂ)) else 0) + E (σ k) k)
    refine ⟨c, hc1, hc0, fun u => ?_⟩
    rw [← hc u]
    congr 2
    funext k
    unfold Formalism.REAL.Tm
    simp only [id]
    split_ifs with hk
    · rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← add_assoc, ← add_smul]
      congr 2
      ring
    · simp
  choose c hc1 hc0 hc using h
  refine ⟨fun i => ∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : A) * c σ i,
    ∑ k : Fin (m + 1), (-s - ((k : ℕ) : ℂ)), ?_, ?_, fun u => ?_⟩
  · simp only
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin (m + 1)))]
    · rw [hc1 1]
      simp
    · intro σ _ hσ
      obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
        by_contra hne
        push_neg at hne
        exact hσ (Equiv.ext hne)
      rw [hc1 σ, Finset.prod_eq_zero (mem_univ k) (if_neg hk), zero_smul, mul_zero]
    · intro h1
      exact absurd (mem_univ _) h1
  · simp only
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin (m + 1)))]
    · rw [hc0 1]
      simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.coe_one,
        id_eq, if_true, ite_self, prod_const_one, one_smul]
      rw [sum_add_distrib, add_comm]
      congr 1
      simp only [Algebra.algebraMap_eq_smul_one, ← sum_smul]
    · intro σ _ hσ
      obtain ⟨k₀, hk₀⟩ : ∃ k, σ k ≠ k := by
        by_contra hne
        push_neg at hne
        exact hσ (Equiv.ext hne)
      rw [hc0 σ]
      have hz : ∀ k, (∏ j, (if j = k then (1 : ℂ) else (if σ j = j then (1 : ℂ) else 0))) = 0 := by
        intro k
        by_cases hk : σ k = k
        · refine Finset.prod_eq_zero (mem_univ k₀) ?_
          have : k₀ ≠ k := fun e => hk₀ (e ▸ hk)
          simp [this, hk₀]
        · refine Finset.prod_eq_zero (mem_univ (σ k)) ?_
          have h2 : σ (σ k) ≠ σ k := fun e => hk (σ.injective e)
          simp [hk, h2]
      simp [hz]
    · intro h1
      exact absurd (mem_univ _) h1
  · unfold Formalism.REAL.qdet Formalism.REAL.qminor
    rw [Finset.sum_congr rfl fun σ _ => by rw [hc σ u]]
    simp_rw [mul_sum, mul_smul_comm]
    rw [Finset.sum_comm]
    simp_rw [← smul_sum]

end GlobalTheory.CapelliNext
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftedCapelliDeterminantSubleadingCoeffTraceStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shifted_capelli_determinant_subleading_coeff_trace : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (s : ℂ), ∃ (c : ℕ → A) (t : ℂ),
    c (m + 1) = 1 ∧ c m = ∑ i, E i i + t • (1 : A) ∧
      ∀ u : ℂ, Formalism.REAL.qdet E (u - s) = ∑ k ∈ Finset.range (m + 1 + 1), u ^ k • c k := by
  first | exact @GlobalTheory.CapelliNext.qdet_shift_next_coeff | exact GlobalTheory.CapelliNext.qdet_shift_next_coeff | (intros; apply GlobalTheory.CapelliNext.qdet_shift_next_coeff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedOpenCompactEqIntegralDiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedOpenCompactEqIntegralDiv
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.HaarSum
open MeasureTheory

theorem vol_mul_relIndex {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (H H' : Subgroup G) (hle : H' ≤ H)
    (hc : IsCompact (H : Set G)) (ho : IsOpen (H' : Set G)) :
    μ.real H' * (H'.relIndex H : ℝ) = μ.real H ∧ H'.relIndex H ≠ 0 := by
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hc
  have hHo : IsOpen (H : Set G) := Subgroup.isOpen_mono hle ho
  have ho' : IsOpen ((H'.subgroupOf H : Subgroup H) : Set H) := ho.preimage continuous_subtype_val
  haveI : Finite (H ⧸ H'.subgroupOf H) := (H'.subgroupOf H).quotient_finite_of_isOpen ho'
  haveI : (H'.subgroupOf H).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hemb : MeasurableEmbedding (H.subtype : H → G) := MeasurableEmbedding.subtype_coe hHo.measurableSet
  have : (μ.comap (H.subtype : H → G)).IsMulLeftInvariant := Measure.IsMulLeftInvariant.comap μ hemb
  have key := (H'.subgroupOf H).index_mul_measure ho'.measurableSet (μ.comap (H.subtype : H → G))
  rw [hemb.comap_apply, hemb.comap_apply] at key
  have e1 : (H.subtype : H → G) '' Set.univ = (H : Set G) := by ext x; simp
  have e2 : (H.subtype : H → G) '' ((H'.subgroupOf H : Subgroup H) : Set H) = (H' : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hle hx⟩, hx, rfl⟩
  rw [e1, e2] at key
  refine ⟨?_, Subgroup.FiniteIndex.index_ne_zero⟩
  rw [Subgroup.relIndex, Measure.real, Measure.real, ← key, ENNReal.toReal_mul, mul_comm]
  simp

theorem integral_eq_sum_cosets {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (S : Subgroup G) (hS : IsOpen (S : Set G))
    (hfin : μ (S : Set G) ≠ ⊤) (u : G → ℂ) (hu : ∀ x, ∀ s ∈ S, u (x * s) = u x) (F : Finset (G ⧸ S))
    (hF : ∀ q : G ⧸ S, q ∉ F → u q.out = 0) :
    ∫ x, u x ∂μ = (μ.real (S : Set G) : ℂ) * ∑ q ∈ F, u q.out := by
  have key : ∀ x : G, u ((x : G ⧸ S).out) = u x := fun x => by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul S x
    rw [hh]
    exact hu x h h.2
  have hset : ∀ q : G ⧸ S, {x : G | (x : G ⧸ S) = q} = (fun x => q.out⁻¹ * x) ⁻¹' (S : Set G) := by
    intro q
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rw [eq_comm]
    exact QuotientGroup.eq
  have hmeas : ∀ q : G ⧸ S, MeasurableSet {x : G | (x : G ⧸ S) = q} := fun q => by
    rw [hset]
    exact (hS.preimage (continuous_const_mul _)).measurableSet
  have hμ : ∀ q : G ⧸ S, μ {x : G | (x : G ⧸ S) = q} = μ (S : Set G) := fun q => by
    rw [hset]
    exact measure_preimage_mul μ _ _
  have hfun : u = fun x => ∑ q ∈ F, ({x : G | (x : G ⧸ S) = q}.indicator (fun _ => u q.out) x) := by
    funext x
    rw [Finset.sum_eq_single (x : G ⧸ S)]
    · simp [Set.indicator, key]
    · intro q _ hq
      simp [Set.indicator, Ne.symm hq]
    · intro hx
      have h0 := hF _ hx
      rw [key] at h0
      simp [Set.indicator, key, h0]
  conv_lhs => rw [hfun]
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_indicator_const _ (hmeas q), Measure.real, hμ q, Complex.real_smul, Measure.real]
  · intro q _
    exact (integrableOn_const (hμ q ▸ hfin)).integrable_indicator (hmeas q)

theorem finite_cosets {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (S : Subgroup G)
    (hS : IsOpen (S : Set G)) {C : Set G} (hC : IsCompact C) : ((fun x : G => (x : G ⧸ S)) '' C).Finite := by
  haveI : DiscreteTopology (G ⧸ S) := QuotientGroup.discreteTopology hS
  exact (hC.image (continuous_coinduced_rng : Continuous fun x : G => (x : G ⧸ S))).finite_of_discrete

theorem hint_eq_integral : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (Λ : AddSubgroup V), IsOpen (Λ : Set V) → IsCompact (Λ : Set V) → ∀ u : V → ℂ,
    (∃ U : AddSubgroup V, IsOpen (U : Set V) ∧ ∀ x, ∀ y ∈ U, u (x + y) = u x) → HasCompactSupport u →
    GlobalTheory.BCT.hint (AddSubgroup.toSubgroup Λ) (fun X : Multiplicative V => u (Multiplicative.toAdd X)) =
      ((μ (Λ : Set V)).toReal : ℂ)⁻¹ * ∫ x, u x ∂μ := by
  intro V _ _ _ μ hμ Λ hΛo hΛc u ⟨U, hUo, hU⟩ hsupp
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  haveI := hμ
  let G := Multiplicative V
  letI : MeasurableSpace G := borel V
  haveI : BorelSpace G := ⟨rfl⟩
  let ν : Measure G := μ
  haveI : ν.IsMulLeftInvariant := ⟨fun g => Measure.IsAddLeftInvariant.map_add_left_eq_self (μ := μ) (Multiplicative.toAdd g)⟩
  let u' : G → ℂ := fun X => u (Multiplicative.toAdd X)
  let K : Subgroup G := AddSubgroup.toSubgroup Λ
  let S : Subgroup G := rStab u' ⊓ K
  have hSK : S ≤ K := inf_le_right
  have hSo : IsOpen (S : Set G) := by
    refine Subgroup.isOpen_mono (H₁ := AddSubgroup.toSubgroup (U ⊓ Λ)) ?_ ?_
    · intro x hx
      refine ⟨fun y => hU _ _ hx.1, hx.2⟩
    · exact hUo.inter hΛo
  have hKc : IsCompact (K : Set G) := hΛc
  obtain ⟨hvol, hidx⟩ := vol_mul_relIndex ν K S hSK hKc hSo
  have hKpos : 0 < μ (Λ : Set V) := hΛo.measure_pos μ ⟨0, Λ.zero_mem⟩
  have hKfin : μ (Λ : Set V) < ⊤ := hΛc.measure_lt_top
  have hSfin : ν (S : Set G) ≠ ⊤ := ne_top_of_le_ne_top hKfin.ne (measure_mono hSK)
  have hfinC := finite_cosets S hSo (C := tsupport u') hsupp
  have hF : ∀ q : G ⧸ S, q ∉ hfinC.toFinset → u' q.out = 0 := by
    intro q hq
    by_contra h
    apply hq
    rw [Set.Finite.mem_toFinset]
    exact ⟨q.out, subset_tsupport _ h, QuotientGroup.out_eq' q⟩
  have hint_eq := integral_eq_sum_cosets ν S hSo hSfin u' (fun x s hs => hs.1 x) hfinC.toFinset hF
  have hsum : ∑ᶠ q : G ⧸ S, u' q.out = ∑ q ∈ hfinC.toFinset, u' q.out := by
    refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
    by_contra h
    exact hq (hF q h)
  have hKr : (μ (Λ : Set V)).toReal = ν.real (S : Set G) * (S.relIndex K : ℝ) := hvol.symm
  have hKne : (μ (Λ : Set V)).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hKpos.ne', hKfin.ne⟩
  have hSne : ν.real (S : Set G) ≠ 0 := by
    intro h0
    rw [hKr, h0, zero_mul] at hKne
    exact hKne rfl
  change (((S.relIndex K : ℕ) : ℂ))⁻¹ * ∑ᶠ q : G ⧸ S, u' q.out = _ * ∫ x : G, u' x ∂ν
  rw [hint_eq, hsum, hKr]
  have hidx' : ((S.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hidx
  have hSne' : ((ν.real (S : Set G) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hSne
  push_cast
  field_simp

end GlobalTheory.HaarSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedOpenCompactEqIntegralDivStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haarIntegralNormalizedOpenCompact_eq_integral_div : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ → ∀ (Λ : AddSubgroup V), IsOpen (Λ : Set V) → IsCompact (Λ : Set V) → ∀ u : V → ℂ, (∃ U : AddSubgroup V, IsOpen (U : Set V) ∧ ∀ x, ∀ y ∈ U, u (x + y) = u x) → HasCompactSupport u → GlobalTheory.BCT.hint (AddSubgroup.toSubgroup Λ) (fun X : Multiplicative V => u (Multiplicative.toAdd X)) = ((μ (Λ : Set V)).toReal : ℂ)⁻¹ * ∫ x, u x ∂μ := by
  first | exact @GlobalTheory.HaarSum.hint_eq_integral | exact GlobalTheory.HaarSum.hint_eq_integral | (intros; apply GlobalTheory.HaarSum.hint_eq_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralEqClosedSubgroupConjAverage
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralEqClosedSubgroupConjAverage
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.IwRed

open GlobalTheory.LeviDesc GlobalTheory.TwOrbConj

theorem avg_const {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have hR : rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [mem_rStab]
  unfold avg
  simp only
  rw [hR, Subgroup.index_top]
  haveI : Unique (H ⧸ (⊤ : Subgroup H)) :=
    ⟨⟨QuotientGroup.mk 1⟩, fun a => QuotientGroup.induction_on a fun x => QuotientGroup.eq.2 (Subgroup.mem_top _)⟩
  rw [finsum_unique]
  simp

variable {G : Type} [Group G]

theorem avg_cavg (K P : Subgroup G) (δ : G) (hδ : δ ∈ P) (f : G → ℂ) (p : P) :
    avg (fun k : K.subgroupOf P => cavg K f (((p * k)⁻¹ * ⟨δ, hδ⟩ * (p * k) : P) : G)) =
      avg (fun k : K => f (((p : G) * k)⁻¹ * δ * ((p : G) * k))) := by
  have h : ∀ k : K.subgroupOf P, cavg K f (((p * k)⁻¹ * ⟨δ, hδ⟩ * (p * k) : P) : G) =
      avg (fun k : K => f (((p : G) * k)⁻¹ * δ * ((p : G) * k))) := by
    intro k
    have hk : ((k : P) : G) ∈ K := k.2
    unfold cavg
    rw [← avg_left (fun k' : K => f (((p : G) * k')⁻¹ * δ * ((p : G) * k'))) ⟨_, hk⟩]
    congr 1
    funext k'
    congr 1
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, _root_.mul_inv_rev]
    group
  simp_rw [h]
  exact avg_const _

theorem mem_twCent_sub (P : Subgroup G) (δ : G) (hδ : δ ∈ P) (x : P) :
    x ∈ twCent (MonoidHom.id P) ⟨δ, hδ⟩ ↔ (x : G) ∈ twCent (MonoidHom.id G) δ := by
  rw [mem_twCent, mem_twCent, Subtype.ext_iff]
  simp

theorem inf_eq_comap (K P : Subgroup G) (δ : G) (hδ : δ ∈ P) (p : P) :
    twCent (MonoidHom.id P) ⟨δ, hδ⟩ ⊓ (K.subgroupOf P).map (MulAut.conj p).toMonoidHom =
      (twCent (MonoidHom.id G) δ ⊓ K.map (MulAut.conj (p : G)).toMonoidHom).comap P.subtype := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_map_equiv, mem_twCent_sub, MulAut.conj_symm_apply,
    Subgroup.mem_subgroupOf, Subgroup.coe_subtype, Subgroup.coe_mul, InvMemClass.coe_inv]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem cptPart_map_sub (P : Subgroup G) (hP : IsClosed (P : Set G)) (δ : G) (hδ : δ ∈ P)
    (hT : twCent (MonoidHom.id G) δ ≤ P) :
    (cptPart (twCent (MonoidHom.id P) ⟨δ, hδ⟩)).map P.subtype = cptPart (twCent (MonoidHom.id G) δ) := by
  unfold cptPart
  rw [MonoidHom.map_closure]
  congr 1
  have hc : ∀ x : P, IsCompact (closure (Subgroup.zpowers x : Set P)) ↔
      IsCompact (closure (Subgroup.zpowers (x : G) : Set G)) := by
    intro x
    rw [(hP.isClosedEmbedding_subtypeVal).isInducing.isCompact_iff,
      ← (hP.isClosedEmbedding_subtypeVal).closure_image_eq]
    have : (Subtype.val '' (Subgroup.zpowers x : Set P)) = (Subgroup.zpowers (x : G) : Set G) := by
      rw [← Subgroup.coe_subtype, ← Subgroup.coe_map, MonoidHom.map_zpowers]
    first
      | (convert Iff.rfl using 3; exact this.symm)
      | (convert Iff.rfl using 3; exact this)
      | exact this ▸ Iff.rfl
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hx'⟩, rfl⟩
    exact ⟨(mem_twCent_sub P δ hδ x).1 hx, (hc x).1 hx'⟩
  · rintro ⟨hy, hy'⟩
    exact ⟨⟨y, hT hy⟩, ⟨(mem_twCent_sub P δ hδ _).2 hy, (hc _).2 hy'⟩, rfl⟩

end GlobalTheory.IwRed

namespace GlobalTheory.IwRed

open GlobalTheory.LeviDesc GlobalTheory.TwOrbConj

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem relIndex_sub (K P : Subgroup G) (hP : IsClosed (P : Set G)) (δ : G) (hδ : δ ∈ P)
    (hT : twCent (MonoidHom.id G) δ ≤ P) (p : P) :
    (twCent (MonoidHom.id P) ⟨δ, hδ⟩ ⊓ (K.subgroupOf P).map (MulAut.conj p).toMonoidHom).relIndex
        (cptPart (twCent (MonoidHom.id P) ⟨δ, hδ⟩)) =
      (twCent (MonoidHom.id G) δ ⊓ K.map (MulAut.conj (p : G)).toMonoidHom).relIndex
        (cptPart (twCent (MonoidHom.id G) δ)) := by
  rw [inf_eq_comap, Subgroup.relIndex_comap, cptPart_map_sub P hP δ hδ hT]

theorem summand_sub (K P : Subgroup G) (hP : IsClosed (P : Set G)) (δ : G) (hδ : δ ∈ P)
    (hT : twCent (MonoidHom.id G) δ ≤ P) (f : G → ℂ) (p : P) :
    summand (MonoidHom.id P) (K.subgroupOf P) ⟨δ, hδ⟩ (fun x : P => cavg K f (x : G)) p =
      summand (MonoidHom.id G) K δ f p := by
  unfold summand
  rw [relIndex_sub K P hP δ hδ hT p]
  congr 1
  simpa using avg_cavg K P δ hδ f p

def dcMap (K P : Subgroup G) (δ : G) (hδ : δ ∈ P) :
    DoubleCoset.Quotient (twCent (MonoidHom.id P) ⟨δ, hδ⟩ : Set P) (K.subgroupOf P : Set P) →
      DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (K : Set G) :=
  fun q => DoubleCoset.mk _ K ((Quotient.out q : P) : G)

theorem dcMap_bij (K P : Subgroup G) (δ : G) (hδ : δ ∈ P) (hT : twCent (MonoidHom.id G) δ ≤ P)
    (hPK : ∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k) : Function.Bijective (dcMap K P δ hδ) := by
  constructor
  · intro q₁ q₂ h
    obtain ⟨t, ht, k, hk, he⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 h
    have htP : t ∈ P := hT ht
    have hkP : k ∈ P := by
      have : k = ((Quotient.out q₁ : P) : G)⁻¹ * t⁻¹ * ((Quotient.out q₂ : P) : G) := by rw [he]; group
      rw [this]
      exact P.mul_mem (P.mul_mem (P.inv_mem (Quotient.out q₁).2) (P.inv_mem htP)) (Quotient.out q₂).2
    rw [← DoubleCoset.out_eq' q₁, ← DoubleCoset.out_eq' q₂, DoubleCoset.eq]
    refine ⟨⟨t, htP⟩, (mem_twCent_sub P δ hδ _).2 ht, ⟨k, hkP⟩, (Subgroup.mem_subgroupOf).2 hk, ?_⟩
    exact Subtype.ext (by simpa using he)
  · intro q
    obtain ⟨p, hp, k, hk, hg⟩ := hPK (Quotient.out q)
    refine ⟨DoubleCoset.mk _ _ (⟨p, hp⟩ : P), ?_⟩
    obtain ⟨t, ht, k', hk', he⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1
      (DoubleCoset.out_eq' (DoubleCoset.mk _ _ (⟨p, hp⟩ : P))).symm
    rw [← DoubleCoset.out_eq' q]
    show DoubleCoset.mk _ K _ = _
    rw [DoubleCoset.eq]
    refine ⟨(t : G)⁻¹, (twCent (MonoidHom.id G) δ).inv_mem ((mem_twCent_sub P δ hδ t).1 ht), ((k' : P) : G)⁻¹ * k,
      K.mul_mem (K.inv_mem ((Subgroup.mem_subgroupOf).1 hk')) hk, ?_⟩
    rw [hg]
    have he' := congrArg (fun x : P => (x : G)) he
    simp only [Subgroup.coe_mul] at he'
    rw [he']
    group

theorem twOrb_sub : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K P : Subgroup G),
    IsOpen (K : Set G) → IsCompact (K : Set G) → IsClosed (P : Set G) → (∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k) →
    ∀ (δ : G) (hδ : δ ∈ P), twCent (MonoidHom.id G) δ ≤ P → ∀ f : G → ℂ,
    (∃ K' : Subgroup G, IsOpen (K' : Set G) ∧ IsHecke K' f) →
    twOrb (MonoidHom.id G) K δ f = twOrb (MonoidHom.id P) (K.subgroupOf P) ⟨δ, hδ⟩ (fun p => GlobalTheory.LeviDesc.cavg K f (p : G)) := by
  intro G _ _ _ K P _ _ hP hPK δ hδ hT f _
  rw [twOrb_eq, twOrb_eq]
  rw [← finsum_comp_equiv (Equiv.ofBijective _ (dcMap_bij K P δ hδ hT hPK))]
  refine finsum_congr fun q => ?_
  rw [summand_sub K P hP δ hδ hT f]
  show summand _ K δ f (Quotient.out (DoubleCoset.mk _ K ((Quotient.out q : P) : G))) = _
  obtain ⟨t, ht, k, hk, he⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1
    (DoubleCoset.out_eq' (DoubleCoset.mk _ K ((Quotient.out q : P) : G))).symm
  rw [he, summand_rep _ K δ f _ ht hk]

end GlobalTheory.IwRed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralEqClosedSubgroupConjAverageStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitalIntegral_eq_closedSubgroup_conjAverage : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K P : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → IsClosed (P : Set G) → (∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k) → ∀ (δ : G) (hδ : δ ∈ P), twCent (MonoidHom.id G) δ ≤ P → ∀ f : G → ℂ, (∃ K' : Subgroup G, IsOpen (K' : Set G) ∧ IsHecke K' f) → twOrb (MonoidHom.id G) K δ f = twOrb (MonoidHom.id P) (K.subgroupOf P) ⟨δ, hδ⟩ (fun p => GlobalTheory.LeviDesc.cavg K f (p : G)) := by
  first | exact @GlobalTheory.IwRed.twOrb_sub | exact GlobalTheory.IwRed.twOrb_sub | (intros; apply GlobalTheory.IwRed.twOrb_sub <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjAverageUnipotentLocallyConstantCompactSuppor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjAverageUnipotentLocallyConstantCompactSuppor
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc.UnipMean

section Generic

variable {G : Type} [Group G]

def core (K K' : Subgroup G) : Subgroup G where
  carrier := {c | ∀ k ∈ K, k⁻¹ * c * k ∈ K'}
  one_mem' := by intro k _; simp
  mul_mem' := by
    intro a b ha hb k hk
    have : k⁻¹ * (a * b) * k = (k⁻¹ * a * k) * (k⁻¹ * b * k) := by group
    rw [this]; exact K'.mul_mem (ha k hk) (hb k hk)
  inv_mem' := by
    intro a ha k hk
    have : k⁻¹ * a⁻¹ * k = (k⁻¹ * a * k)⁻¹ := by group
    rw [this]; exact K'.inv_mem (ha k hk)

theorem isOpen_core [TopologicalSpace G] [IsTopologicalGroup G] (K K' : Subgroup G) (hK : IsCompact (K : Set G))
    (hK' : IsOpen (K' : Set G)) : IsOpen (core K K' : Set G) := by
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have h := hK.eventually_forall_of_forall_eventually (x₀ := (1 : G)) (P := fun c k => k⁻¹ * c * k ∈ K') ?_
  · exact h
  intro k _
  have hc : Continuous fun p : G × G => p.2⁻¹ * p.1 * p.2 := by fun_prop
  have h1 : (fun p : G × G => p.2⁻¹ * p.1 * p.2) (1, k) ∈ (K' : Set G) := by simp [K'.one_mem]
  exact hc.continuousAt.preimage_mem_nhds (hK'.mem_nhds h1)

theorem cavg_mul_core (K K' : Subgroup G) (f : G → ℂ) (hf : ∀ k ∈ K', ∀ x, f (x * k) = f x) (x c : G)
    (hc : c ∈ core K K') : cavg K f (x * c) = cavg K f x := by
  unfold cavg
  congr 1
  funext k
  have := hf _ (hc k k.2) ((k : G)⁻¹ * x * k)
  rw [← this]
  congr 1
  group

theorem exists_of_cavg_ne_zero (K : Subgroup G) (f : G → ℂ) (x : G) (h : cavg K f x ≠ 0) :
    ∃ k ∈ K, f (k⁻¹ * x * k) ≠ 0 := by
  by_contra hn
  push_neg at hn
  apply h
  unfold cavg avg
  have : (fun k : K => f ((k : G)⁻¹ * x * k)) = fun _ => 0 := funext fun k => hn k k.2
  rw [this]
  simp

end Generic

section Block

variable {E : Type} [Field E] [NumberField E] {n a b : ℕ} (h : a + b = n) (w : Pl E)

theorem isUnit_blkMat (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val)) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 m.1.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).1 m.2.isUnit)

theorem blk_val (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w m X).val = Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val) := by
  unfold blk
  simp only
  rw [dite_eq_left (isUnit_blkMat h w m X)]
  rfl

theorem blk_add (m : GLw a w × GLw b w) (x y : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    blk h w m (x + y) = blk h w m x * blk h w 1 y := by
  ext1
  rw [Units.val_mul, blk_val, blk_val, blk_val]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Prod.fst_one,
    Prod.snd_one, Units.val_one, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Matrix.mul_add]
  congr 2
  exact add_comm _ _

theorem blk_one_zero : blk h w (1 : GLw a w × GLw b w) 0 = 1 := by
  ext1
  rw [blk_val]
  simp only [Prod.fst_one, Prod.snd_one, Units.val_one, Matrix.mul_zero, Matrix.fromBlocks_one, Units.val_one]
  exact Matrix.submatrix_one_equiv _

theorem blk_one_neg (y : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w 1 y)⁻¹ = blk h w 1 (-y) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← blk_add, add_neg_cancel, blk_one_zero]

theorem continuous_blk_one : Continuous fun y : Matrix (Fin a) (Fin b) (w.adicCompletion E) => blk h w 1 y := by
  have hv : Continuous fun y : Matrix (Fin a) (Fin b) (w.adicCompletion E) => (blk h w 1 y).val := by
    simp only [blk_val, Prod.fst_one, Prod.snd_one, Units.val_one, Matrix.one_mul]
    exact (continuous_const.matrix_fromBlocks continuous_id continuous_const continuous_const).matrix_reindex _ _
  refine Units.continuous_iff.2 ⟨hv, ?_⟩
  simp only [blk_one_neg]
  exact hv.comp continuous_neg

def corner (m : GLw a w × GLw b w) (g : GLw n w) : Matrix (Fin a) (Fin b) (w.adicCompletion E) :=
  (m.1⁻¹).val * (Matrix.reindex (finSumFinEquiv.trans (finCongr h)).symm (finSumFinEquiv.trans (finCongr h)).symm
    g.val).toBlocks₁₂

theorem corner_blk (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    corner h w m (blk h w m X) = X := by
  rw [corner, blk_val, ← Matrix.reindex_symm, Equiv.symm_apply_apply, Matrix.toBlocks_fromBlocks₁₂,
    ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

theorem continuous_corner (m : GLw a w × GLw b w) : Continuous (corner h w m) := by
  unfold corner
  refine continuous_const.matrix_mul ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact (Units.continuous_val.matrix_elem _ _)

end Block

theorem cavg_blk_locConst_compactSupport : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw b w, (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (blk h w m (x + y)) = GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (blk h w m x)) ∧ HasCompactSupport (fun X => GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (blk h w m X)) := by
  intro E _ _ n a b h w f ⟨K', hK'o, hf⟩ m
  obtain ⟨_, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hCo : IsOpen (core (GlobalTheory.LFun.KGL w (n := n)) K' : Set (GLw n w)) := isOpen_core _ _ hKc hK'o
  let U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)) :=
    { carrier := {y | blk h w 1 y ∈ core (GlobalTheory.LFun.KGL w (n := n)) K'}
      zero_mem' := by
        simp only [Set.mem_setOf_eq, blk_one_zero]
        exact Subgroup.one_mem _
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at *
        rw [blk_add]
        exact Subgroup.mul_mem _ hx hy
      neg_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at *
        rw [← blk_one_neg]
        exact Subgroup.inv_mem _ hx }
  refine ⟨⟨U, hCo.preimage (continuous_blk_one h w), fun x y hy => ?_⟩, ?_⟩
  · rw [blk_add]
    exact cavg_mul_core _ _ f (fun k hk x => (hf.2 k hk x).2) _ _ hy
  · let S : Set (GLw n w) := (fun p : GLw n w × GLw n w × GLw n w => p.1 * p.2.1 * p.2.2) ''
      ((GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) ×ˢ (tsupport f ×ˢ (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w))))
    have hS : IsCompact S := (hKc.prod (hf.1.isCompact.prod hKc)).image (by fun_prop)
    refine HasCompactSupport.intro (hS.image (continuous_corner h w m)) fun X hX => ?_
    by_contra hne
    obtain ⟨k, hk, hfk⟩ := exists_of_cavg_ne_zero _ f _ hne
    refine hX ⟨blk h w m X, ⟨(k, k⁻¹ * blk h w m X * k, k⁻¹),
      ⟨hk, subset_tsupport _ hfk, Subgroup.inv_mem _ hk⟩, by group⟩, corner_blk h w m X⟩

end GlobalTheory.LeviDesc.UnipMean
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjAverageUnipotentLocallyConstantCompactSupporStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjAverage_unipotent_locallyConstant_compactSupport : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw b w, (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (blk h w m (x + y)) = GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (blk h w m x)) ∧ HasCompactSupport (fun X => GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (blk h w m X)) := by
  first | exact @GlobalTheory.LeviDesc.UnipMean.cavg_blk_locConst_compactSupport | exact GlobalTheory.LeviDesc.UnipMean.cavg_blk_locConst_compactSupport | (intros; apply GlobalTheory.LeviDesc.UnipMean.cavg_blk_locConst_compactSupport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorLevelIndicatorEqInvIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorLevelIndicatorEqInvIndex
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.HopLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem toSub_of_mem {G : Type} [Group G] (H : Subgroup G) {g : G} (h : g ∈ H) : toSub H g = ⟨g, h⟩ := by
  unfold toSub; rw [dif_pos h]

def comp (hU : Unr E) (n : ℕ) (w : Pl E) : finU (E := E) (n := n) →* UL n w :=
  ((cLoc w).comp (finU (E := E) (n := n)).subtype).codRestrict (UL n w) (fun x => cLoc_mem_UL E hU n w x)

theorem comp_eq (hU : Unr E) (w : Pl E) (x : finU (E := E) (n := n)) :
    comp hU n w x = toSub (UL n w) (cLoc w (x : UA E n)) :=
  (toSub_of_mem _ (cLoc_mem_UL E hU n w x)).symm

theorem mem_globLev (hU : Unr E) (S : Set (Pl E)) (L : ∀ w : Pl E, Subgroup (UL n w)) (x : finU (E := E) (n := n)) :
    x ∈ globLev S L ↔ ∀ w ∈ S, comp hU n w x ∈ L w := by
  unfold globLev
  simp only [Subgroup.mem_iInf, Subgroup.mem_comap, Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply,
    Subgroup.coe_subtype]
  refine forall_congr' fun w => forall_congr' fun _ => ⟨fun ⟨k, hk, e⟩ => ?_, fun h => ⟨_, h, rfl⟩⟩
  have : k = comp hU n w x := Subtype.ext e
  rwa [← this]

theorem globFn_indicator (hU : Unr E) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (hK : ∀ᶠ w in cofinite, K' w = KL n w) (x : finU (E := E) (n := n)) :
    globFn S (fun w => (K' w : Set (UL n w)).indicator 1) x = if x ∈ globLev S K' then 1 else 0 := by
  unfold globFn
  simp_rw [← comp_eq hU]
  by_cases hx : x ∈ globLev S K'
  · rw [if_pos hx]
    refine finprod_mem_of_eqOn_one fun w hw => ?_
    rw [Set.indicator_of_mem ((mem_globLev hU S K' x).1 hx w hw)]
    rfl
  · rw [if_neg hx, finprod_mem_def]
    obtain ⟨w₀, hw₀, hn⟩ : ∃ w ∈ S, comp hU n w x ∉ K' w := by
      by_contra h; push_neg at h; exact hx ((mem_globLev hU S K' x).2 h)
    refine finprod_eq_zero _ w₀ ?_ ?_
    · rw [Set.mulIndicator_of_mem hw₀, Set.indicator_of_notMem hn]
    · have h1 := Filter.eventually_cofinite.1 hK
      have h2 := Filter.eventually_cofinite.1 (LocAE.eventually_mem_KL E hU n x)
      refine (h1.union h2).subset fun w hw => ?_
      by_contra hc
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
      apply hw
      rw [Set.mulIndicator_apply]
      split_ifs
      · rw [Set.indicator_of_mem]
        · rfl
        · rw [hc.1, comp_eq hU]; exact hc.2
      · rfl

end GlobalTheory.BCT.HopLev

noncomputable section

namespace GlobalTheory.BCT.HopLev2

open GlobalTheory.BCT.HopLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem index_pi_univ {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

theorem relIndex_eq_prod {ι : Type} [Fintype ι] {G : Type} [Group G] {M : ι → Type} [∀ i, Group (M i)]
    (φ : G →* ((i : ι) → M i)) (Up U : Subgroup G) (K H : ∀ i, Subgroup (M i))
    (hK : ∀ g ∈ Up, ∀ i, φ g i ∈ K i) (hs : ∀ x : (i : ι) → M i, (∀ i, x i ∈ K i) → ∃ g ∈ Up, φ g = x)
    (hU : ∀ g, g ∈ U ↔ g ∈ Up ∧ ∀ i, φ g i ∈ H i) : U.relIndex Up = ∏ i, (H i).relIndex (K i) := by
  let ψ : Up →* ((i : ι) → K i) :=
    { toFun := fun g i => ⟨φ g.1 i, hK g.1 g.2 i⟩
      map_one' := by ext i; simp
      map_mul' := by intro x y; ext i; simp }
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨g, hg, e⟩ := hs (fun i => (x i).1) (fun i => (x i).2)
    exact ⟨⟨g, hg⟩, by ext i; simp [ψ, e]⟩
  have e : U.subgroupOf Up = (Subgroup.pi Set.univ fun i => (H i).subgroupOf (K i)).comap ψ := by
    ext g
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_pi, hU, g.2, ψ]
  rw [Subgroup.relIndex, e, Subgroup.index_comap_of_surjective _ hψ, index_pi_univ]
  rfl

theorem relIndex_globLev (hU : Unr E) (S : Set (Pl E)) (hS : IsSection S) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (hle : ∀ w, K' w ≤ KL n w) (hK : ∀ᶠ w in cofinite, K' w = KL n w) :
    (((globLev S K').relIndex (globLev S (KL n)) : ℕ) : ℂ) = ∏ᶠ w ∈ S, (((K' w).relIndex (KL n w) : ℕ) : ℂ) := by
  have hfin := Filter.eventually_cofinite.1 hK
  obtain ⟨T, hTS, hnT⟩ : ∃ T : Finset (Pl E), (∀ w ∈ T, w ∈ S) ∧ ∀ w ∈ S, w ∉ T → K' w = KL n w :=
    ⟨hfin.toFinset.filter (· ∈ S), fun w hw => (Finset.mem_filter.1 hw).2, fun w hw h => by
      by_contra hc
      exact h (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hc, hw⟩)⟩
  rw [finprod_mem_eq_prod_of_inter_mulSupport_eq _ (t := T)]
  · rw [← Finset.prod_coe_sort T]
    rw [relIndex_eq_prod (MonoidHom.pi fun i : T => comp hU n i.1) (globLev S (KL n)) (globLev S K')
      (fun i => KL n i.1) (fun i => K' i.1)]
    · push_cast; rfl
    · intro g hg i
      exact (mem_globLev hU S (KL n) g).1 hg i.1 (hTS _ i.2)
    · intro x hx
      obtain ⟨y, hyT, hyn⟩ : ∃ y : ∀ w : Pl E, UL n w, (∀ i : T, y i.1 = x i) ∧ ∀ w, w ∉ T → y w = 1 :=
        ⟨fun w => if h : w ∈ T then x ⟨w, h⟩ else 1, fun i => dif_pos i.2, fun w h => dif_neg h⟩
      have hy : ∀ w, y w ∈ KL n w := fun w => by
        by_cases h : w ∈ T
        · have := hx ⟨w, h⟩
          rw [hyT ⟨w, h⟩]
          exact this
        · rw [hyn w h]; exact one_mem _
      obtain ⟨g, hg⟩ := exists_finU_of_loc E hU n S hS y (Filter.Eventually.of_forall hy)
      have hg' : ∀ w ∈ S, comp hU n w g = y w := fun w hw => by rw [comp_eq]; exact hg w hw
      refine ⟨g, (mem_globLev hU S (KL n) g).2 fun w hw => by rw [hg' w hw]; exact hy w, ?_⟩
      funext i
      show comp hU n i.1 g = x i
      rw [hg' i.1 (hTS _ i.2)]
      exact hyT i
    · intro g
      rw [mem_globLev hU S K' g, mem_globLev hU S (KL n) g]
      refine ⟨fun h => ⟨fun w hw => hle w (h w hw), fun i => h i.1 (hTS _ i.2)⟩, fun ⟨h1, h2⟩ w hw => ?_⟩
      by_cases hwT : w ∈ T
      · exact h2 ⟨w, hwT⟩
      · rw [hnT w hw hwT]; exact h1 w hw
  · ext w
    simp only [Set.mem_inter_iff, Function.mem_mulSupport, Finset.mem_coe]
    refine ⟨fun ⟨hw, h⟩ => ⟨?_, h⟩, fun ⟨hw, h⟩ => ⟨hTS w hw, h⟩⟩
    by_contra hwT
    apply h
    rw [hnT w hw hwT, Subgroup.relIndex_self]
    simp

end GlobalTheory.BCT.HopLev2


open GlobalTheory.BCT.HopLev GlobalTheory.BCT.HopLev2 in
theorem GlobalTheory.BCT.hop_indicator_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ S : Set (Pl E), IsSection S → ∀ K' : ∀ w : Pl E, Subgroup (UL n w),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ φ ∈ fixed (RF E n) (globLev S K'),
    hop S K' (fun w => (K' w : Set (UL n w)).indicator 1) φ = (∏ᶠ w ∈ S, (((K' w).relIndex (KL n w) : ℕ) : ℂ))⁻¹ • φ := by
  intro E _ _ _ hU n _ S hS K' hK φ hφ
  rw [← relIndex_globLev hU S hS K' (fun w => (hK.1 w).2.1) hK.2]
  unfold hop levOp
  rw [LinearMap.smul_apply]
  congr 1
  set H := globLev S K'
  have hq : ∀ q : finU (E := E) (n := n) ⧸ H, q ≠ ((1 : finU (E := E) (n := n)) : finU (E := E) (n := n) ⧸ H) → Quotient.out q ∉ H := by
    intro q hq hm
    apply hq
    rw [← QuotientGroup.out_eq' q, QuotientGroup.eq]
    simpa using hm
  have h1 : Quotient.out ((1 : finU (E := E) (n := n)) : finU (E := E) (n := n) ⧸ H) ∈ H := by
    have := QuotientGroup.out_eq' ((1 : finU (E := E) (n := n)) : finU (E := E) (n := n) ⧸ H)
    rw [QuotientGroup.eq] at this
    simpa using this
  rw [finsum_eq_single _ ((1 : finU (E := E) (n := n)) : finU (E := E) (n := n) ⧸ H)]
  · rw [globFn_indicator hU S K' hK.2, if_pos h1, one_smul, LinearMap.comp_id]
    have := hφ ⟨_, h1⟩
    simpa using this
  · intro q hne
    rw [globFn_indicator hU S K' hK.2, if_neg (hq q hne), zero_smul]
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorLevelIndicatorEqInvIndexStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryHeckeOperator_levelIndicator_eq_inv_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ S : Set (Pl E), IsSection S → ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ φ ∈ fixed (RF E n) (globLev S K'), hop S K' (fun w => (K' w : Set (UL n w)).indicator 1) φ = (∏ᶠ w ∈ S, (((K' w).relIndex (KL n w) : ℕ) : ℂ))⁻¹ • φ := by
  first | exact @GlobalTheory.BCT.hop_indicator_level | exact GlobalTheory.BCT.hop_indicator_level | (intros; apply GlobalTheory.BCT.hop_indicator_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellHeightLocalReduction
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix Topology Pointwise

namespace GlobalTheory.WhitHered.CellLoc

section Alg

variable {k : Type} [Field k] {N : ℕ}

end Alg

section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N c : ℕ} {m : Fin c → ℕ}

theorem isClosed_parab (e : (Σ a, Fin (m a)) ≃ Fin N) : IsClosed (parab k e : Set (GL (Fin N) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : (parab k e : Set (GL (Fin N) k)) = ⋂ i, ⋂ j, ⋂ _ : blk e j < blk e i, {g : GL (Fin N) k | g.val i j = 0} := by
    ext g
    simp only [SetLike.mem_coe, mem_parab, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const

end Main

end GlobalTheory.WhitHered.CellLoc

end
end
