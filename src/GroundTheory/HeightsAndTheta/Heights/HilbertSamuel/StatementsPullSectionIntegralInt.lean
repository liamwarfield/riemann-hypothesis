module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullConeDegreeInt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStE
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.LocTransfer

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullSectionIntegralInt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def PullSectionIntegralInt.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (q N M : ℕ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ k, 1 ≤ e k) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) → (M : Ω) ≠ 0 →
    (∀ (d : K → ℕ) (g : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d → (∀ k, e k + N * Fintype.card (ι k) ≤ d k) →
      ∃ a : Fin (D + 1) → MRing ι, (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (a j) (d - e)) ∧
        (M : Ω) * aeval y g = ∑ j, aeval y (a j) * aeval y (L j)) →
    ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun k => ((q * e k : ℕ) : ℤ)) τ, ∀ j : Fin (D + 1), aeval y (L j) ≠ 0 →
      s / aeval y (L j) ^ (q * τ) ∈
        integralClosure
          (Algebra.adjoin ℤ (insert ((M : Ω)⁻¹) (Set.range fun i => aeval y (L i) / aeval y (L j)))) Ω

section Inhabitants

namespace PullSectionIntegralInt

end PullSectionIntegralInt

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseMonoBasis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open scoped Pointwise

noncomputable section

namespace VeroneseMonoBasis

theorem sec_x_eq (D n : ℕ) : sec ℤ (Veronese.x D) n = sec ℤ (Veronese.t D) (2 * n) := by
  rw [SectionsRank.sec_eq_span, SectionsRank.sec_eq_span, VeroneseGenDeg.range_alt, ← pow_mul]

theorem mono_mem_sec (D n : ℕ) (k : Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card) :
    (∏ i, Veronese.t D i ^ adtEnum D (2 * n) k i) ∈ sec ℤ (Veronese.x D) n := by
  rw [sec_x_eq]
  refine Submodule.mem_map.mpr ⟨monoZ (adtEnum D (2 * n) k),
    (mem_homogeneousSubmodule _ _).mpr (monoZ_isHomogeneous (adtEnum_sum D (2 * n) k)), ?_⟩
  rw [AlgHom.toLinearMap_apply, aeval_monoZ]

theorem linearIndependent_mono (D N : ℕ) :
    LinearIndependent ℤ (fun k : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card =>
      ∏ i, Veronese.t D i ^ adtEnum D N k i) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro u hu l
  set p : MvPolynomial (Fin (D + 1)) ℤ := ∑ k, u k • monoZ (adtEnum D N k) with hp
  have hpa : aeval (Veronese.t D) p = aeval (Veronese.t D) (0 : MvPolynomial (Fin (D + 1)) ℤ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hp, map_sum, map_zero, ← hu]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, aeval_monoZ]
  have hp0 := VeroneseGenDeg.aeval_t_injective D hpa
  have hc := congrArg (AddMonoidAlgebra.coeff · (Finsupp.equivFunOnFinite.symm (adtEnum D N l))) hp0
  rw [hp, coeff_sum, MvPolynomial.coeff_zero, Finset.sum_eq_single l (fun k _ hkl => ?_) (by simp)] at hc
  · rwa [coeff_smul, monoZ, coeff_monomial, if_pos rfl, smul_eq_mul, mul_one] at hc
  · rw [coeff_smul, monoZ, coeff_monomial, if_neg, smul_zero]
    intro hE
    exact hkl (adtEnum_injective D N (by simpa using hE))

end VeroneseMonoBasis


open VeroneseMonoBasis in
theorem VeroneseMonoBasis.proof : VeroneseMonoBasis.Statement := by
  intro D n
  have hex : ∀ k : Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card,
      ∃ f : MvPolynomial (Ix (Veronese.Idx D)) ℤ, f.IsHomogeneous n ∧
        aeval (Veronese.x D) f = ∏ i, Veronese.t D i ^ adtEnum D (2 * n) k i := fun k => by
    obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.mp (mono_mem_sec D n k)
    exact ⟨f, (mem_homogeneousSubmodule _ _).mp hf, hfx⟩
  choose f hf hfx using hex
  have hb : ∀ k, aeval (Veronese.x D) (map (Int.castRingHom ℚ) (f k)) =
      ∏ i, Veronese.t D i ^ adtEnum D (2 * n) k i := fun k => by
    rw [aeval_map_intQ, hfx]
  refine ⟨fun k => map (Int.castRingHom ℚ) (f k), ⟨fun k => ⟨f k, hf k, rfl⟩, ?_, ?_⟩, hb⟩
  · simp only [hb]
    exact linearIndependent_mono D (2 * n)
  · simp only [hb]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact mono_mem_sec D n k
    · rw [sec_x_eq]
      rintro _ ⟨g, hg, rfl⟩
      rw [AlgHom.toLinearMap_apply, aeval_eq_sum_adt _ ((mem_homogeneousSubmodule _ _).mp hg)]
      refine Submodule.sum_mem _ fun a ha => ?_
      have hai : adtEnum D (2 * n) ((Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).equivFin ⟨a, ha⟩) = a := by
        simp [adtEnum]
      rw [← zsmul_eq_mul, ← hai]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeDegreeInt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial BlockImageHilb

noncomputable section

namespace PullConeDegreeInt

section Lemmas

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem isWeightedHomogeneous_of_isMultiHomog {f : MRing ι} {a : K → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a := by
  intro m hm
  funext k
  rw [weight_blockWeight_apply]
  exact hf m (mem_support_iff.mpr hm) k

theorem isMultiHomog_of_isWeightedHomogeneous {f : MRing ι} {a : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a := by
  intro m hm k
  rw [← weight_blockWeight_apply, hf (mem_support_iff.mp hm)]

theorem mConeMap_eq (y : (Σ k, ι k) → Ω) {f : MRing ι} {a : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a) :
    mConeMap y f = MvPolynomial.C (aeval y f) * ∏ k, MvPolynomial.X k ^ a k := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hX : ∏ p : (Σ k, ι k), (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ μ p = ∏ k, MvPolynomial.X k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ μ ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, ← weight_blockWeight_apply, hf (mem_support_iff.mp hμ)]
  simp only [mConeMap, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow, MvPolynomial.algebraMap_apply]
  ring

theorem coeff_mConeMap (y : (Σ k, ι k) → Ω) (f : MRing ι) (n : K → ℕ) :
    AddMonoidAlgebra.coeff (mConeMap y f) (Finsupp.equivFunOnFinite.symm n) =
      aeval y (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) n f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial m r =>
    have hm := isWeightedHomogeneous_monomial (NumbersDVR.blockWeight ι) m r rfl
    rw [mConeMap_eq y hm, PullConeDegree.prod_X_pow_eq_monomial, C_mul_monomial, mul_one, coeff_monomial,
      weightedHomogeneousComponent_of_mem (n := Finsupp.weight (NumbersDVR.blockWeight ι) m) hm]
    by_cases h : n = Finsupp.weight (NumbersDVR.blockWeight ι) m
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun h' => h (Finsupp.equivFunOnFinite.symm.injective h').symm), map_zero]
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, hp, hq, map_add (f := _), map_add (f := _)]


omit [DecidableEq K] in
theorem exists_dvd_monomial (N : ℕ) (hne : ∀ k, Nonempty (ι k)) (μ : (Σ k, ι k) →₀ ℕ)
    (hμ : ∀ k, N * Fintype.card (ι k) ≤ ∑ i, μ ⟨k, i⟩) (r : ℤ) :
    ∃ c : ∀ k, ι k, (∏ k, (X ⟨k, c k⟩ : MRing ι)) ^ N ∣ monomial μ r := by
  have hc : ∀ k, ∃ i, N ≤ μ ⟨k, i⟩ := by
    intro k
    by_contra h
    simp only [not_exists, not_le] at h
    have hlt := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty (α := ι k)) (fun i _ => h i)
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm] at hlt
    exact absurd (hμ k) (not_le.mpr hlt)
  choose c hc using hc
  refine ⟨c, ?_⟩
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun i => by simp), Fintype.prod_sigma, ← Finset.prod_pow]
  refine Dvd.dvd.mul_left (Finset.prod_dvd_prod_of_dvd _ _ fun k _ => ?_) _
  exact (pow_dvd_pow _ (hc k)).trans
    (Finset.dvd_prod_of_mem (fun i => (X ⟨k, i⟩ : MRing ι) ^ μ ⟨k, i⟩) (Finset.mem_univ (c k)))

end Lemmas

theorem proof : PullConeDegreeInt.Statement := by
  classical
  intro K _ ι _ Ω _ y D e L N M hy hL hN d g hg hd
  have hne : ∀ k, Nonempty (ι k) := fun k => (hy k).elim fun i _ => ⟨i⟩
  have hg' := isWeightedHomogeneous_of_isMultiHomog hg

  have hgI : (M : MRing ι) * g ∈ coneNullIdealZ y L := by
    rw [g.as_sum, Finset.mul_sum]
    refine Ideal.sum_mem _ fun μ hμ => ?_
    obtain ⟨c, hc⟩ := exists_dvd_monomial N hne μ
      (fun k => by rw [hg μ hμ k]; have := hd k; omega) (AddMonoidAlgebra.coeff g μ)
    exact Ideal.mem_of_dvd _ (mul_dvd_mul_left _ hc) (hN c)
  have hI : coneNullIdealZ y L = RingHom.ker (mConeMap y) ⊔ Ideal.span (Set.range L) := by
    rw [coneNullIdealZ, Ideal.span_union, Ideal.span_eq]
    rfl
  rw [hI, Submodule.mem_sup] at hgI
  obtain ⟨u, hu, v, hv, huv⟩ := hgI
  obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp hv

  have hmapL : ∀ j, mConeMap y (L j) = monomial (Finsupp.equivFunOnFinite.symm e) (aeval y (L j)) := by
    intro j
    rw [mConeMap_eq y (isWeightedHomogeneous_of_isMultiHomog (hL j)), PullConeDegree.prod_X_pow_eq_monomial,
      C_mul_monomial, mul_one]
  have hMg : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) ((M : MRing ι) * g) d := by
    have h := (isWeightedHomogeneous_C (NumbersDVR.blockWeight ι) (M : ℤ)).mul hg'
    rw [zero_add, map_natCast] at h
    exact h
  have hψg : mConeMap y ((M : MRing ι) * g) =
      ∑ j, mConeMap y (b j) * monomial (Finsupp.equivFunOnFinite.symm e) (aeval y (L j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← huv, map_add (f := _), RingHom.mem_ker.mp hu, zero_add, ← hb, map_sum]
    simp only [map_mul, hmapL]

  refine ⟨fun j => weightedHomogeneousComponent (NumbersDVR.blockWeight ι) (d - e) (b j),
    fun j => isMultiHomog_of_isWeightedHomogeneous (weightedHomogeneousComponent_isWeightedHomogeneous _ _), ?_⟩
  have hc := congrArg (AddMonoidAlgebra.coeff · (Finsupp.equivFunOnFinite.symm d)) hψg
  rw [mConeMap_eq y hMg, PullConeDegree.prod_X_pow_eq_monomial, C_mul_monomial, mul_one,
    coeff_monomial, if_pos rfl, coeff_sum, map_mul, map_natCast] at hc
  rw [hc]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hle : Finsupp.equivFunOnFinite.symm e ≤ Finsupp.equivFunOnFinite.symm d :=
    Finsupp.le_def.mpr fun k => by simp only [Finsupp.coe_equivFunOnFinite_symm]; have := hd k; omega
  have hsub : Finsupp.equivFunOnFinite.symm d - Finsupp.equivFunOnFinite.symm e =
      Finsupp.equivFunOnFinite.symm (d - e) := by
    ext k
    simp
  rw [coeff_mul_monomial', if_pos hle, hsub, coeff_mConeMap]

end PullConeDegreeInt

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartDimLt
section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ChartDimLtTorus
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Algebra

noncomputable section

namespace ChartDimLt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_dim_add_card_le {J : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    (hJ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal J) (p : (k : K) → ι k)
    (𝔮 : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [𝔮.IsPrime] (h𝔮 : ReciprocityTheory.AnForm.R.chartIdeal J p ≤ 𝔮) :
    ∃ s : ℕ, ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) = s ∧
      ((s + Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ J) := by
  classical
  let : CommRing (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) := Ideal.Quotient.commRing 𝔮
  have : IsDomain (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) := Ideal.Quotient.isDomain 𝔮
  let y : (Σ k, ι k) → MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) :=
    fun q => C (Ideal.Quotient.mk 𝔮 (X q))
  let θ : (MvPolynomial (Σ k, ι k) ℂ) →ₐ[ℂ] MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) :=
    aeval (fun q => (X q.1 : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) * y q)
  have hy : ∀ f : (MvPolynomial (Σ k, ι k) ℂ), aeval y f = C (Ideal.Quotient.mk 𝔮 f) := by
    intro f
    have : (aeval y : (MvPolynomial (Σ k, ι k) ℂ) →ₐ[ℂ] MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) =
        (IsScalarTower.toAlgHom ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)
          (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))).comp (Ideal.Quotient.mkₐ ℂ 𝔮) := by
      apply MvPolynomial.algHom_ext
      intro q
      simp [y, MvPolynomial.algebraMap_eq]
    rw [this]
    simp [MvPolynomial.algebraMap_eq]
  have hJθ : J ≤ RingHom.ker θ := by
    obtain ⟨S, hS, hJS⟩ := hJ
    have hle : Ideal.span S ≤ RingHom.ker θ := by
      rw [Ideal.span_le]
      intro f hf
      obtain ⟨a, ha⟩ := hS f hf
      have hfJ : f ∈ J := by rw [hJS]; exact Ideal.subset_span hf
      have hf𝔮 : f ∈ 𝔮 := h𝔮 (Ideal.mem_sup_left hfJ)
      show θ f = 0
      simp only [θ]
      rw [ReciprocityTheory.AnForm.R.aeval_smul_of_isMultiHomog ha
          (X : K → MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) y, hy,
        Ideal.Quotient.eq_zero_iff_mem.mpr hf𝔮, map_zero, mul_zero]
    rw [hJS]
    exact hle
  have hdimR : ringKrullDim θ.range ≤ ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ J) := by
    let g : (MvPolynomial (Σ k, ι k) ℂ) ⧸ J →+* θ.range :=
      Ideal.Quotient.lift J (θ.rangeRestrict : (MvPolynomial (Σ k, ι k) ℂ) →+* θ.range)
        (fun a ha => Subtype.ext (by simpa using hJθ ha))
    refine ringKrullDim_le_of_surjective g ?_
    intro x
    obtain ⟨a, ha⟩ := θ.rangeRestrict_surjective x
    exact ⟨Ideal.Quotient.mk J a, ha⟩
  have : Algebra.FiniteType ℂ θ.range :=
    Algebra.FiniteType.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
  have : Algebra.FiniteType ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ 𝔮) (Ideal.Quotient.mkₐ_surjective ℂ 𝔮)
  obtain ⟨sA, hAdim, hAtr⟩ :=
    ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))
  obtain ⟨sR, hRdim, hRtr⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := θ.range)
  have : FaithfulSMul ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) :=
    (faithfulSMul_iff_algebraMap_injective ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)).mpr
      (algebraMap ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)).injective
  have : FaithfulSMul (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    (faithfulSMul_iff_algebraMap_injective (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)
      (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))).mpr
      (MvPolynomial.C_injective K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))
  have : FaithfulSMul ℂ θ.range :=
    (faithfulSMul_iff_algebraMap_injective ℂ θ.range).mpr (algebraMap ℂ θ.range).injective
  have : FaithfulSMul θ.range (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    (faithfulSMul_iff_algebraMap_injective θ.range
      (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))).mpr Subtype.val_injective
  have hT1 : trdeg ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) +
      trdeg (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) =
      trdeg ℂ (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    trdeg_add_eq ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)

  have h1 : ∀ k, Ideal.Quotient.mk 𝔮 (X ⟨k, p k⟩ : (MvPolynomial (Σ k, ι k) ℂ)) = 1 := by
    intro k
    rw [← map_one (Ideal.Quotient.mk 𝔮), Ideal.Quotient.eq]
    exact h𝔮 (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))
  have hXk : ∀ k, (X k : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) ∈ θ.range := by
    intro k
    refine (θ.mem_range).mpr ⟨X ⟨k, p k⟩, ?_⟩
    simp only [θ, y, aeval_X, h1, map_one, mul_one]
  have hXq : ∀ q, (X q.1 : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) * y q ∈ θ.range := fun q =>
    (θ.mem_range).mpr ⟨X q, by simp only [θ, aeval_X]⟩
  let AC := Subalgebra.algebraicClosure θ.range (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))
  have hRAC : ∀ t ∈ θ.range, t ∈ AC := fun t ht =>
    (Subalgebra.mem_algebraicClosure _ _).mpr (isAlgebraic_algebraMap (⟨t, ht⟩ : θ.range))
  have hyAC : ∀ q, y q ∈ AC := fun q =>
    (Subalgebra.mem_algebraicClosure _ _).mpr (IsAlgebraic.of_mul
      (mem_nonZeroDivisors_of_ne_zero (X_ne_zero q.1))
      ((Subalgebra.mem_algebraicClosure _ _).mp (hRAC _ (hXk q.1)))
      ((Subalgebra.mem_algebraicClosure _ _).mp (hRAC _ (hXq q))))
  have hCAC : ∀ f : (MvPolynomial (Σ k, ι k) ℂ), C (Ideal.Quotient.mk 𝔮 f) ∈ AC := by
    intro f
    refine MvPolynomial.induction_on (motive := fun f => C (Ideal.Quotient.mk 𝔮 f) ∈ AC) f ?_ ?_ ?_
    · intro c
      apply hRAC
      refine (θ.mem_range).mpr ⟨C c, ?_⟩
      simp only [θ, aeval_C, MvPolynomial.algebraMap_apply]
      rfl
    · intro f g hf hg
      rw [map_add (f := _), map_add (f := _)]
      exact AC.add_mem hf hg
    · intro f q hf
      rw [map_mul, map_mul]
      exact AC.mul_mem hf (hyAC q)
  have hall : ∀ t : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮), t ∈ AC := by
    intro t
    refine MvPolynomial.induction_on (motive := fun t => t ∈ AC) t ?_ ?_ ?_
    · intro a
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact hCAC f
    · intro f g hf hg
      exact AC.add_mem hf hg
    · intro f k hf
      exact AC.mul_mem hf (hRAC _ (hXk k))
  have : Algebra.IsAlgebraic θ.range (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    ⟨fun t => (Subalgebra.mem_algebraicClosure _ _).mp (hall t)⟩
  have hT2 : trdeg ℂ θ.range + trdeg θ.range (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) =
      trdeg ℂ (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    trdeg_add_eq ℂ θ.range
  have h0 : trdeg θ.range (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) = 0 := trdeg_eq_zero
  rw [h0, add_zero] at hT2
  have hK : trdeg (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) =
      (Fintype.card K : Cardinal) := by
    rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype]
  rw [hK, hAtr, ← hT2, hRtr] at hT1
  have hnat : sA + Fintype.card K = sR := by exact_mod_cast hT1
  refine ⟨sA, hAdim, ?_⟩
  rw [hnat, ← hRdim]
  exact hdimR

end ChartDimLt

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Algebra

noncomputable section

theorem ChartDimLt.proof : ChartDimLt.Statement := by
  intro K _ ι _ J e p hJ hdim
  have key : ∀ Z ∈ (ReciprocityTheory.AnForm.R.chartIdeal J p).minimalPrimes,
      ∃ s : ℕ, ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Z) = s ∧ s < e := by
    intro Z hZ
    have : Z.IsPrime := hZ.1.1
    obtain ⟨s, hs, hle⟩ := ChartDimLt.exists_dim_add_card_le hJ p Z hZ.1.2
    have hlt : ((s + Fintype.card K : ℕ) : WithBot ℕ∞) < ((e + Fintype.card K : ℕ) : WithBot ℕ∞) :=
      lt_of_le_of_lt hle hdim
    have hlt' : s + Fintype.card K < e + Fintype.card K := by exact_mod_cast hlt
    exact ⟨s, hs, by omega⟩
  cases e with
  | zero =>
    refine lt_of_le_of_lt
      (Targets.BaseChangeMin.ringKrullDim_quotient_le_of_minimalPrimes (N := ⊥) _ fun Z hZ => ?_)
      (WithBot.bot_lt_coe _)
    obtain ⟨s, -, hs⟩ := key Z hZ
    omega
  | succ n =>
    have hn : ((n : ℕ) : WithBot ℕ∞) < ((n + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast Nat.lt_succ_self n
    refine lt_of_le_of_lt
      (Targets.BaseChangeMin.ringKrullDim_quotient_le_of_minimalPrimes (N := ((n : ℕ) : WithBot ℕ∞)) _
        fun Z hZ => ?_) hn
    obtain ⟨s, hs, hsn⟩ := key Z hZ
    rw [hs]
    exact_mod_cast (by omega : s ≤ n)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
