module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsSupUnitsLocalNormsSqrtNeTop
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAdmissibleLocalNormMemSUnitsSupGlobalNorm
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.DenseMvPolynomialEvalNeZero
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

theorem dense_mvPolynomial_eval_ne_zero {D : ℕ} (q : MvPolynomial (Fin D) ℂ) (hq : q ≠ 0) :
    Dense {z : Fin D → ℂ | MvPolynomial.eval z q ≠ 0} := by
  rw [Metric.dense_iff]
  intro z₀ r hr
  by_contra hne
  apply hq
  refine MvPolynomial.funext_set (fun i => Metric.ball (z₀ i) r)
    (fun i => infinite_of_mem_nhds (z₀ i) (Metric.ball_mem_nhds _ hr)) (fun x hx => ?_)
  rw [map_zero]
  by_contra hx0
  apply hne
  refine ⟨x, ?_, hx0⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hr]
  exact fun i => hx i (Set.mem_univ i)

theorem exists_algIndep_tuple_near :
    ∀ (K : Type) [Field K] [Countable K] (sg : K →+* ℂ) (D : ℕ) (z₀ : Fin D → ℂ) (ε : ℝ), 0 < ε → ∃ z : Fin D → ℂ, (∀ i, ‖z i - z₀ i‖ < ε) ∧ ∀ p : MvPolynomial (Fin D) K, p ≠ 0 → MvPolynomial.eval₂ sg z p ≠ 0 := by
  intro K _ _ sg D z₀ ε hε
  let S : {p : MvPolynomial (Fin D) K // p ≠ 0} → Set (Fin D → ℂ) :=
    fun p => {z | MvPolynomial.eval z (MvPolynomial.map sg p.1) ≠ 0}
  have : Countable (MvPolynomial (Fin D) K) := by
    refine Function.Surjective.countable (f := fun l : List ((Fin D →₀ ℕ) × K) =>
      (l.map fun mc => MvPolynomial.monomial mc.1 mc.2).sum) fun p => ?_
    refine ⟨p.support.toList.map fun m => (m, AddMonoidAlgebra.coeff p m), ?_⟩
    simp only [List.map_map]
    rw [Finset.sum_map_toList]
    exact p.as_sum.symm
  have hS : Dense (⋂ p, S p) := by
    apply dense_iInter_of_isOpen
    · intro p
      exact isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const
    · intro p
      refine dense_mvPolynomial_eval_ne_zero _ fun h0 => p.2 ?_
      exact MvPolynomial.map_injective sg sg.injective (h0.trans (map_zero _).symm)
  obtain ⟨z, hzS, hz⟩ := hS.exists_mem_open (Metric.isOpen_ball (x := z₀)) (Metric.nonempty_ball.mpr hε)
  refine ⟨z, ?_, fun p hp => ?_⟩
  · rw [Metric.mem_ball, dist_pi_lt_iff hε] at hz
    intro i
    rw [← dist_eq_norm]
    exact hz i
  · rw [← MvPolynomial.eval_map]
    exact Set.mem_iInter.mp hzS ⟨p, hp⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsEmbeddingsOverInjective
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

theorem exists_natForm_norm_ge {ι J : Type*} [Fintype ι] [DecidableEq ι] (T : Finset J) (n : ℕ)
    (hn : T.card ≤ n) (v : J → ι → ℂ) (ε : ℝ) (hv : ∀ j ∈ T, ∃ a, ε ≤ ‖v j a‖) :
    ∃ c : ι → Fin (n + 1), ∀ j ∈ T, ε / 2 ≤ ‖∑ a, ((c a : ℕ) : ℂ) * v j a‖ := by
  classical
  by_contra hcon
  push Not at hcon
  set bad : J → Finset (ι → Fin (n + 1)) := fun j =>
    Finset.univ.filter fun c => ‖∑ a, ((c a : ℕ) : ℂ) * v j a‖ < ε / 2 with hbad
  set N := Fintype.card (ι → Fin (n + 1)) with hN
  have hNpos : 0 < N := Fintype.card_pos
  have h1 : ∀ j ∈ T, (bad j).card * (n + 1) ≤ N := by
    intro j hj
    obtain ⟨a, ha⟩ := hv j hj
    have hinj : Set.InjOn (fun p : (ι → Fin (n + 1)) × Fin (n + 1) => Function.update p.1 a p.2)
        ((bad j ×ˢ (Finset.univ : Finset (Fin (n + 1))) : Finset _) : Set _) := by
      rintro ⟨c, k⟩ hc ⟨c', k'⟩ hc' h
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hbad, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.coe_univ, Set.mem_univ, and_true] at hc hc'
      have hk : k = k' := by simpa using congrFun h a
      have hoff : ∀ b, b ≠ a → c b = c' b := fun b hb => by
        simpa [Function.update_of_ne hb] using congrFun h b
      have hsum : (∑ b, ((c b : ℕ) : ℂ) * v j b) - ∑ b, ((c' b : ℕ) : ℂ) * v j b
          = ((((c a : ℕ) : ℤ) - ((c' a : ℕ) : ℤ) : ℤ) : ℂ) * v j a := by
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_single a]
        · push_cast; ring
        · intro b _ hb; rw [hoff b hb]; ring
        · simp
      have hlt : ‖((((c a : ℕ) : ℤ) - ((c' a : ℕ) : ℤ) : ℤ) : ℂ) * v j a‖ < ε := by
        rw [← hsum]
        have := norm_sub_le (∑ b, ((c b : ℕ) : ℂ) * v j b) (∑ b, ((c' b : ℕ) : ℂ) * v j b)
        linarith
      have hca : c a = c' a := by
        by_contra hne
        have hz : (((c a : ℕ) : ℤ) - ((c' a : ℕ) : ℤ) : ℤ) ≠ 0 := by
          intro h0
          apply hne
          apply Fin.ext
          omega
        have h1 : (1 : ℝ) ≤ ‖((((c a : ℕ) : ℤ) - ((c' a : ℕ) : ℤ) : ℤ) : ℂ)‖ := by
          rw [Complex.norm_intCast]
          exact_mod_cast Int.one_le_abs hz
        rw [norm_mul] at hlt
        nlinarith [norm_nonneg (v j a)]
      refine Prod.ext ?_ hk
      funext b
      by_cases hb : b = a
      · subst hb; exact hca
      · exact hoff b hb
    have := Finset.card_le_card_of_injOn _ (t := Finset.univ) (fun _ _ => by simp) hinj
    simpa [hN] using this
  have h2 : (Finset.univ : Finset (ι → Fin (n + 1))) ⊆ T.biUnion bad := by
    intro c _
    obtain ⟨j, hj, h⟩ := hcon c
    exact Finset.mem_biUnion.2 ⟨j, hj, by simpa [hbad] using h⟩
  have h3 : N ≤ ∑ j ∈ T, (bad j).card := (Finset.card_le_card h2).trans Finset.card_biUnion_le
  have h4 : N * (n + 1) ≤ T.card * N := by
    calc N * (n + 1) ≤ (∑ j ∈ T, (bad j).card) * (n + 1) := Nat.mul_le_mul_right _ h3
      _ = ∑ j ∈ T, (bad j).card * (n + 1) := Finset.sum_mul ..
      _ ≤ ∑ j ∈ T, N := Finset.sum_le_sum h1
      _ = T.card * N := by simp
  nlinarith

theorem exists_root_near_of_norm_eval_lt (p : Polynomial ℂ) (hp : p.Monic) (x : ℂ) (δ : ℝ)
    (hδ : 0 < δ) (h : ‖p.eval x‖ < δ ^ p.natDegree) : ∃ r, p.IsRoot r ∧ ‖r - x‖ < δ := by
  by_contra hcon
  push Not at hcon
  have hs := IsAlgClosed.splits p
  rw [hs.eval_eq_prod_roots_of_monic hp, hs.natDegree_eq_card_roots] at h
  have key : ∀ s : Multiset ℂ, (∀ r ∈ s, δ ≤ ‖r - x‖) →
      δ ^ s.card ≤ ‖(s.map fun r => x - r).prod‖ := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      intro hs
      simp only [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, norm_mul, pow_succ']
      refine mul_le_mul ?_ (ih fun r hr => hs r (Multiset.mem_cons_of_mem hr)) (by positivity)
        (norm_nonneg _)
      rw [norm_sub_rev]
      exact hs a (Multiset.mem_cons_self _ _)
  exact absurd h (not_lt.2 (key _ fun r hr => hcon r (Polynomial.isRoot_of_mem_roots hr)))

theorem exists_embeddings_over_injective (R A Ω : Type*) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CommRing A] [IsDomain A] [Algebra R A] [Module.Finite R A]
    [FaithfulSMul R A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω] :
    ∃ n : ℕ, ∀ τ : R →+* ℂ, Function.Injective τ → ∃ T : Finset (Ω →+* ℂ), T.card ≤ n ∧
      (∀ σ ∈ T, σ.comp ((algebraMap A Ω).comp (algebraMap R A)) = τ) ∧
      ∀ (b : A) (r : ℂ), ((minpoly R b).map τ).IsRoot r → ∃ σ ∈ T, σ (algebraMap A Ω b) = r := by
  classical
  let _ : Algebra R Ω := ((algebraMap A Ω).comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FaithfulSMul R Ω := (faithfulSMul_iff_algebraMap_injective R Ω).2
    ((IsFractionRing.injective A Ω).comp (FaithfulSMul.algebraMap_injective R A))
  let F := FractionRing R
  let _ : Algebra F Ω := FractionRing.liftAlgebra R Ω
  have : IsScalarTower R F Ω := FractionRing.isScalarTower_liftAlgebra R Ω
  have : IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) Ω :=
    inferInstance
  have : FiniteDimensional F Ω := Module.Finite.of_isLocalization R A (nonZeroDivisors R)
  refine ⟨Module.finrank F Ω, fun τ hτ => ?_⟩
  let _ : Algebra F ℂ := (IsFractionRing.lift hτ : F →+* ℂ).toAlgebra
  have hF : ∀ x : R, algebraMap F ℂ (algebraMap R F x) = τ x := fun x =>
    IsFractionRing.lift_algebraMap hτ x
  let _ : Fintype (Ω →ₐ[F] ℂ) := Fintype.ofFinite _
  refine ⟨Finset.univ.image fun ψ : Ω →ₐ[F] ℂ => (ψ : Ω →+* ℂ), ?_, ?_, ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact card_algHom_le_finrank F Ω ℂ
  · intro σ hσ
    obtain ⟨ψ, -, rfl⟩ := Finset.mem_image.1 hσ
    ext x
    change ψ (algebraMap R Ω x) = τ x
    rw [IsScalarTower.algebraMap_apply R F Ω, AlgHom.commutes, hF]
  · intro b r hr
    have hb : IsIntegral R b := Algebra.IsIntegral.isIntegral b
    have h1 : r ∈ (minpoly F (algebraMap A Ω b)).rootSet ℂ := by
      rw [Polynomial.mem_rootSet]
      refine ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral _), ?_⟩
      rw [minpoly.isIntegrallyClosed_eq_field_fractions F Ω hb, Polynomial.aeval_def,
        Polynomial.eval₂_map, show (algebraMap F ℂ).comp (algebraMap R F) = τ from RingHom.ext hF,
        Polynomial.eval₂_eq_eval_map]
      exact hr
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly ℂ] at h1
    obtain ⟨ψ, hψ⟩ := h1
    exact ⟨ψ, Finset.mem_image.2 ⟨ψ, Finset.mem_univ _, rfl⟩, hψ⟩

theorem continuous_eval_map_eval₂Hom {K : Type*} [CommRing K] (sg : K →+* ℂ) {D : ℕ}
    (μ : Polynomial (MvPolynomial (Fin D) K)) (x : ℂ) :
    Continuous fun z : Fin D → ℂ => (μ.map (MvPolynomial.eval₂Hom sg z)).eval x := by
  simp only [Polynomial.eval_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  refine continuous_finsetSum _ fun i _ => Continuous.mul ?_ continuous_const
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq_eval_map]
  exact MvPolynomial.continuous_eval _

theorem generic_points_dense : (∀ (K : Type) [Field K] [Countable K] (sg : K →+* ℂ) (D : ℕ) (z₀ : Fin D → ℂ) (ε : ℝ), 0 < ε → ∃ z : Fin D → ℂ, (∀ i, ‖z i - z₀ i‖ < ε) ∧ ∀ p : MvPolynomial (Fin D) K, p ≠ 0 → MvPolynomial.eval₂ sg z p ≠ 0) → ∀ (K A Ω : Type) [Field K] [NumberField K] [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω] [Algebra K Ω] [IsScalarTower K A Ω] (sg : K →+* ℂ) (φ : A →+* ℂ), φ.comp (algebraMap K A) = sg → ∀ (S : Finset A) (ε : ℝ), 0 < ε → ∃ P ∈ PT (Ω := Ω) sg, ∀ a ∈ S, ‖P (algebraMap A Ω a) - φ a‖ < ε := by
  intro hgen K A Ω _ _ _ _ _ _ _ _ _ _ _ sg φ hφ S ε hε
  classical
  obtain ⟨D, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg K A
  let R := MvPolynomial (Fin D) K
  let _ : Algebra R A := g.toRingHom.toAlgebra
  have : Module.Finite R A := hfin
  have : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).2 hinj
  have : Countable K := Countable.of_equiv _ (Module.finBasis ℚ K).equivFun.toEquiv.symm
  obtain ⟨n, hn⟩ := exists_embeddings_over_injective R A Ω
  let z₀ : Fin D → ℂ := fun i => φ (g (MvPolynomial.X i))
  have hz₀ : MvPolynomial.eval₂Hom sg z₀ = φ.comp (algebraMap R A) := by
    apply MvPolynomial.ringHom_ext
    · intro k
      change _ = φ (g (algebraMap K _ k))
      rw [AlgHom.commutes, ← hφ]
      simp
    · intro i
      simp only [MvPolynomial.eval₂Hom_X']
      rfl
  let b : (S → Fin (n + 1)) → A := fun c => ∑ a : S, ((c a : ℕ) : A) * (a : A)
  have hev : ∀ᶠ z in nhds z₀, ∀ c, ‖((minpoly R (b c)).map (MvPolynomial.eval₂Hom sg z)).eval
      (φ (b c))‖ < (ε / 2) ^ (minpoly R (b c)).natDegree := by
    rw [Filter.eventually_all]
    intro c
    refine ((continuous_eval_map_eval₂Hom sg (minpoly R (b c)) (φ (b c))).norm.tendsto
      z₀).eventually_lt_const ?_
    have h0 : ((minpoly R (b c)).map (MvPolynomial.eval₂Hom sg z₀)).eval (φ (b c)) = 0 := by
      rw [hz₀, Polynomial.eval_map, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def,
        minpoly.aeval, map_zero]
    simp only [h0, norm_zero]
    positivity
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨z, hz, hzg⟩ := hgen K sg D z₀ η hη
  have hτ : Function.Injective (MvPolynomial.eval₂Hom sg z) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra h
    exact hzg p h hp
  obtain ⟨T, hT, hover, hroot⟩ := hn _ hτ
  have hsmall := hball (y := z) ((dist_pi_lt_iff hη).2 fun i => by
    rw [dist_eq_norm]; exact hz i)
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hc⟩ := exists_natForm_norm_ge T n hT
    (fun σ (a : S) => σ (algebraMap A Ω a) - φ a) ε (by
      intro σ hσ
      have hP : σ ∈ PT (Ω := Ω) sg := by
        ext k
        have := RingHom.congr_fun (hover σ hσ) (MvPolynomial.C k)
        rw [MvPolynomial.eval₂Hom_C] at this
        rw [← this]
        change σ _ = σ (algebraMap A Ω (g (algebraMap K _ k)))
        rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
      obtain ⟨a, ha, h⟩ := hcon σ hP
      exact ⟨⟨a, ha⟩, h⟩)
  have hmon : (minpoly R (b c)).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral _)
  obtain ⟨r, hr, hrε⟩ := exists_root_near_of_norm_eval_lt _
    (hmon.map (MvPolynomial.eval₂Hom sg z)) (φ (b c)) (ε / 2) (by positivity)
    (by rw [hmon.natDegree_map]; exact hsmall c)
  obtain ⟨σ, hσ, rfl⟩ := hroot _ r hr
  refine absurd hrε (not_lt.2 ?_)
  have hc' := hc σ hσ
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [b, map_sum, map_mul, map_natCast, mul_sub, Finset.sum_sub_distrib] using hc'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIdeleNotMulNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIdeleNotMulNorm
open NumberField IsDedekindDomain

namespace GlobalTheory.QNorm

theorem exists_adele_finite_component (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ e : AdeleRing (𝓞 F) F →+* v.adicCompletion F, (∀ x, e x = x.2 v) ∧
      ∀ t : F, e (algebraMap F (AdeleRing (𝓞 F) F) t) = algebraMap F (v.adicCompletion F) t :=
  ⟨{ toFun := fun x => x.2 v
     map_one' := rfl
     map_mul' := fun _ _ => rfl
     map_zero' := rfl
     map_add' := fun _ _ => rfl }, fun _ => rfl, fun _ => rfl⟩

theorem exists_infiniteAdele_real_component (F : Type) [Field F] [NumberField F]
    (σ : F →+* ℝ) :
    ∃ e : InfiniteAdeleRing F →+* ℝ,
      ∀ t : F, e (algebraMap F (InfiniteAdeleRing F) t) = σ t := by
  have hφ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp
  have hw : (InfinitePlace.mk (Complex.ofRealHom.comp σ)).IsReal := ⟨_, hφ, rfl⟩
  refine ⟨(InfinitePlace.Completion.extensionEmbeddingOfIsReal hw).comp
    (Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) _), fun t => ?_⟩
  have he := InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw
    ((WithAbs.equiv (InfinitePlace.mk (Complex.ofRealHom.comp σ)).1).symm t)
  change (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw)
    ((algebraMap F (InfiniteAdeleRing F) t) _) = σ t
  rw [InfiniteAdeleRing.algebraMap_apply]
  refine he.trans ?_
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hφ]
  simp


open Classical in
noncomputable def adeleOn (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (z : F) : AdeleRing (𝓞 F) F :=
  (algebraMap F (InfiniteAdeleRing F) z,
    (⟨fun v => if v ∈ S then algebraMap F (v.adicCompletion F) z else 1, by
      filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
      have hv' : v ∉ S := hv
      simp only [if_neg hv', SetLike.mem_coe]
      exact one_mem _⟩ : FiniteAdeleRing (𝓞 F) F))

theorem adeleOn_snd_of_mem (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (z : F) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    (adeleOn F S z).2 v = algebraMap F (v.adicCompletion F) z := if_pos hv

theorem adeleOn_snd_of_notMem (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (z : F) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    (adeleOn F S z).2 v = 1 := if_neg hv

theorem adeleOn_mul_inv (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) {z : F} (hz : z ≠ 0) :
    adeleOn F S z * adeleOn F S z⁻¹ = 1 := by
  refine Prod.ext ?_ (FiniteAdeleRing.ext F fun v => ?_)
  · change algebraMap F (InfiniteAdeleRing F) z * algebraMap F (InfiniteAdeleRing F) z⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hz, map_one]
  · change (adeleOn F S z).2 v * (adeleOn F S z⁻¹).2 v = 1
    by_cases hv : v ∈ S
    · rw [adeleOn_snd_of_mem F S _ hv, adeleOn_snd_of_mem F S _ hv, ← map_mul,
        mul_inv_cancel₀ hz, map_one]
    · rw [adeleOn_snd_of_notMem F S _ hv, adeleOn_snd_of_notMem F S _ hv, mul_one]

theorem div_mem_normSub {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F) (z t : Fˣ)
    (a b : L) (h : φ (z : F) = φ (t : F) * (a ^ 2 - φ δ * b ^ 2)) : z / t ∈ normSub φ δ := by
  refine ⟨a, b, ?_⟩
  have ht : φ (t : F) ≠ 0 := by simp
  rw [Units.val_div_eq_div_val, map_div₀, h]
  field_simp

theorem exists_idele_not_mul_norm : ∀ (F : Type) [Field F] [NumberField F] (δ : F), ¬ IsSquare δ → ∃ a : (AdeleRing (𝓞 F) F)ˣ, ∀ (t : F) (x y : AdeleRing (𝓞 F) F), (a : AdeleRing (𝓞 F) F) ≠ algebraMap F (AdeleRing (𝓞 F) F) t * (x ^ 2 - algebraMap F (AdeleRing (𝓞 F) F) δ * y ^ 2) := by
  intro F _ _ δ hsq
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hsq IsSquare.zero
  obtain ⟨S, hS, hδ, hadj⟩ := GlobalTheory.T.exists_admissible_localNorm_mem_sUnits_sup_globalNorm F (Units.mk0 δ hδ0) hsq
  have hne := sUnits_sup_locNorm_ne_top F (Units.mk0 δ hδ0) S hS hδ hsq
  simp only [Units.val_mk0] at hadj hne
  obtain ⟨z, hz⟩ : ∃ z : Fˣ, z ∉ sUnits F S ⊔ locNorm F δ S := by
    by_contra hcon
    push Not at hcon
    exact hne (Subgroup.eq_top_iff' _ |>.2 hcon)
  refine ⟨Units.mkOfMulEqOne _ _ (adeleOn_mul_inv F S z.ne_zero), fun t x y h => hz ?_⟩
  replace h : adeleOn F S z = algebraMap F (AdeleRing (𝓞 F) F) t *
      (x ^ 2 - algebraMap F (AdeleRing (𝓞 F) F) δ * y ^ 2) := h
  have ht : t ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at h
    have h1 : algebraMap F (InfiniteAdeleRing F) z = 0 := congrArg Prod.fst h
    exact z.ne_zero ((map_eq_zero _).1 h1)
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F), ∃ a b : v.adicCompletion F,
      (adeleOn F S z).2 v = algebraMap F (v.adicCompletion F) t *
        (a ^ 2 - algebraMap F (v.adicCompletion F) δ * b ^ 2) := by
    intro v
    obtain ⟨e, he, he'⟩ := exists_adele_finite_component F v
    refine ⟨e x, e y, ?_⟩
    rw [← he, h, map_mul, map_sub, map_mul, map_pow, map_pow, he', he']
  have h1 : Units.mk0 t ht ∈ sUnits F S ⊔ locNorm F δ S := by
    refine sup_le_sup_left (normSub_id_le_locNorm F δ S) _ (hadj _ fun v hv => ?_)
    obtain ⟨a, b, hab⟩ := hfin v
    rw [adeleOn_snd_of_notMem F S _ hv] at hab
    have h2 := div_mem_normSub (algebraMap F (v.adicCompletion F)) δ 1 (Units.mk0 t ht) a b
      (by simpa using hab)
    rwa [one_div, inv_mem_iff] at h2
  have h2 : z / Units.mk0 t ht ∈ locNorm F δ S := by
    refine ⟨Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => ?_,
      Subgroup.mem_iInf.2 fun σ => ?_⟩
    · obtain ⟨a, b, hab⟩ := hfin v
      rw [adeleOn_snd_of_mem F S _ hv] at hab
      exact div_mem_normSub _ δ z (Units.mk0 t ht) a b hab
    · obtain ⟨e, he⟩ := exists_infiniteAdele_real_component F σ
      refine div_mem_normSub σ δ z (Units.mk0 t ht) (e x.1) (e y.1) ?_
      have h3 : algebraMap F (InfiniteAdeleRing F) z = algebraMap F (InfiniteAdeleRing F) t *
          (x.1 ^ 2 - algebraMap F (InfiniteAdeleRing F) δ * y.1 ^ 2) := congrArg Prod.fst h
      have h4 := congrArg e h3
      rwa [map_mul, map_sub, map_mul, map_pow, map_pow, he, he, he] at h4
  have h3 := mul_mem (Subgroup.mem_sup_right (S := sUnits F S) h2) h1
  rwa [div_mul_cancel] at h3

end GlobalTheory.QNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIdeleNotMulNormStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idele_ne_algebraMap_mul_norm_of_not_isSquare : ∀ (F : Type) [Field F] [NumberField F] (δ : F), ¬ IsSquare δ → ∃ a : (AdeleRing (𝓞 F) F)ˣ, ∀ (t : F) (x y : AdeleRing (𝓞 F) F), (a : AdeleRing (𝓞 F) F) ≠ algebraMap F (AdeleRing (𝓞 F) F) t * (x ^ 2 - algebraMap F (AdeleRing (𝓞 F) F) δ * y ^ 2) := by
  first | exact @GlobalTheory.QNorm.exists_idele_not_mul_norm | exact GlobalTheory.QNorm.exists_idele_not_mul_norm | (intros; apply GlobalTheory.QNorm.exists_idele_not_mul_norm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.AeEvalCircleMapNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralLogNormLeHalfLogIntegralSq
open MeasureTheory Metric Set Filter Real
open scoped ENNReal Topology Pointwise

namespace GlobalTheory

section Rotation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def sphereRotation (θ : ℝ) (x : sphere (0 : E) 1) : sphere (0 : E) 1 :=
  ⟨circleMap 0 1 θ • (x : E), by simp [norm_smul]⟩

omit [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem coe_sphereRotation (θ : ℝ) (x : sphere (0 : E) 1) :
    (sphereRotation θ x : E) = circleMap 0 1 θ • (x : E) := rfl

omit [MeasurableSpace E] [BorelSpace E] in
theorem continuous_sphereRotation :
    Continuous (Function.uncurry (sphereRotation (E := E))) := by
  refine continuous_induced_rng.2 ?_
  have e : (Subtype.val ∘ Function.uncurry (sphereRotation (E := E))) =
      fun q : ℝ × sphere (0 : E) 1 => circleMap 0 1 q.1 • (q.2 : E) := by
    funext q
    exact coe_sphereRotation q.1 q.2
  rw [e]
  exact ((continuous_circleMap 0 1).comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem measurePreserving_sphereRotation [FiniteDimensional ℂ E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (θ : ℝ) :
    MeasurePreserving (sphereRotation θ) μ.toSphere μ.toSphere := by
  set ζ : ℂ := circleMap 0 1 θ with hζ_def
  have hζ : ‖ζ‖ = 1 := by simp [ζ, norm_circleMap_zero]
  have hζ0 : ζ ≠ 0 := by
    rw [← norm_ne_zero_iff, hζ]; exact one_ne_zero
  have hm : Measurable (sphereRotation (E := E) θ) :=
    (continuous_sphereRotation.comp (continuous_const.prodMk continuous_id)).measurable
  refine ⟨hm, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply hm hs, Measure.toSphere_apply' μ (hm hs), Measure.toSphere_apply' μ hs]
  congr 1
  have hset : Ioo (0 : ℝ) 1 • ((↑) '' (sphereRotation θ ⁻¹' s) : Set E) =
      (fun v : E => ζ • v) ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
    ext v
    constructor
    · rintro ⟨t, ht, _, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨t, ht, _, ⟨sphereRotation θ w, hw, rfl⟩, ?_⟩
      show t • ((sphereRotation θ w : sphere (0 : E) 1) : E) = ζ • (t • (w : E))
      rw [coe_sphereRotation]
      exact smul_comm t ζ (w : E)
    · rintro ⟨t, ht, _, ⟨u, hu, rfl⟩, huv⟩
      have hwmem : ζ⁻¹ • (u : E) ∈ sphere (0 : E) 1 := by
        simp [norm_smul, hζ]
      set w : sphere (0 : E) 1 := ⟨ζ⁻¹ • (u : E), hwmem⟩ with hw_def
      have hw : sphereRotation θ w = u := by
        apply Subtype.ext
        rw [coe_sphereRotation]
        show ζ • ζ⁻¹ • (u : E) = u
        rw [smul_smul, mul_inv_cancel₀ hζ0, one_smul]
      refine ⟨t, ht, _, ⟨w, ?_, rfl⟩, ?_⟩
      · show sphereRotation θ w ∈ s
        rw [hw]; exact hu
      · have huv' : t • (u : E) = ζ • v := huv
        show t • (ζ⁻¹ • (u : E)) = v
        rw [smul_comm t ζ⁻¹, huv', smul_smul, inv_mul_cancel₀ hζ0, one_smul]
  rw [hset]
  exact (measurePreserving_smul_of_norm_eq_one μ hζ).measure_preimage_emb
    (MeasurableEquiv.smul₀ ζ hζ0).measurableEmbedding _

end Rotation

section Torus

variable {ι : Type*} [Fintype ι]

end Torus

section Concavity

variable {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]

end Concavity

end GlobalTheory
end

open MeasureTheory Metric NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.MultiplicativeHeights
open scoped TensorProduct

namespace GlobalTheory

theorem ae_eval_circleMap_ne_zero : ∀ (m : ℕ) (f : MvPolynomial (Fin m) ℂ), f ≠ 0 →
    ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)),
      MvPolynomial.eval (fun i => circleMap 0 1 (x i)) f ≠ 0 := by
  intro m
  induction m with
  | zero =>
    intro f hf
    refine Filter.Eventually.of_forall fun x => ?_
    rw [MvPolynomial.eq_C_of_isEmpty f] at hf ⊢
    simpa using hf
  | succ m ih =>
    intro f hf
    set P := MvPolynomial.finSuccEquiv ℂ m f with hPdef
    have hP : P ≠ 0 := by
      intro h
      apply hf
      exact (MvPolynomial.finSuccEquiv ℂ m).injective (by rw [← hPdef, h, map_zero])
    obtain ⟨k, hk⟩ : ∃ k, P.coeff k ≠ 0 := by
      by_contra h
      push Not at h
      exact hP (Polynomial.ext fun k => by simpa using h k)
    have h1 := ih _ hk
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
    have he : MeasurePreserving e volume volume := volume_preserving_piFinSuccAbove _ 0
    have hcont : Continuous fun (x : Fin (m + 1) → ℝ) =>
        MvPolynomial.eval (fun i => circleMap 0 1 (x i)) f :=
      (MvPolynomial.continuous_eval f).comp
        (continuous_pi fun i => (continuous_circleMap 0 1).comp (continuous_apply i))
    have hmeas : MeasurableSet {z : ℝ × (Fin m → ℝ) |
        MvPolynomial.eval (fun i => circleMap 0 1 (e.symm z i)) f ≠ 0} :=
      (hcont.measurable.comp e.symm.measurable) (measurableSet_singleton 0).compl
    have key : ∀ᵐ z ∂(volume : Measure (ℝ × (Fin m → ℝ))),
        MvPolynomial.eval (fun i => circleMap 0 1 (e.symm z i)) f ≠ 0 := by
      rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae hmeas]
      rw [Measure.ae_ae_comm (p := fun y s =>
        MvPolynomial.eval (fun i => circleMap 0 1 (e.symm (y, s) i)) f ≠ 0) hmeas]
      filter_upwards [h1] with s hs
      set w : Fin m → ℂ := fun i => circleMap 0 1 (s i) with hw
      have hQ : Polynomial.map (MvPolynomial.eval w) P ≠ 0 := by
        intro h
        apply hs
        have := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q k) h
        simpa [Polynomial.coeff_map] using this
      have hfin : ({y : ℂ | Polynomial.eval y (Polynomial.map (MvPolynomial.eval w) P) = 0}).Finite :=
        Polynomial.finite_setOfPred_isRoot hQ
      have hnull := (hfin.countable.preimage_circleMap 0 one_ne_zero).measure_zero
        (volume : Measure ℝ)
      rw [measure_eq_zero_iff_ae_notMem] at hnull
      filter_upwards [hnull] with y hy
      have hc : (fun i => circleMap 0 1 ((e.symm (y, s) : Fin (m + 1) → ℝ) i)) =
          Fin.cons (circleMap 0 1 y) w := by
        have : (e.symm (y, s) : Fin (m + 1) → ℝ) = Fin.cons y s := by
          simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
        rw [this]
        funext i
        cases i using Fin.cases <;> simp [hw]
      rw [hc, MvPolynomial.eval_eq_eval_mv_eval']
      exact hy
    have := he.quasiMeasurePreserving.ae key
    filter_upwards [this] with x hx
    simpa using hx

theorem ae_eval₂_ne_zero_pi_toSphere (K : Type) [Field K] [Countable K] (sg : K →+* ℂ)
    (D N : ℕ) :
    ∀ᵐ t ∂(MeasureTheory.Measure.pi fun _ : Fin D =>
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere),
      ∀ p : MvPolynomial (Fin D × Fin (N + 1)) K, p ≠ 0 →
        MvPolynomial.eval₂ sg (fun q => (t q.1 : EuclideanSpace ℂ (Fin (N + 1))) q.2) p ≠ 0 := by
  have := NPB.countable_mvPoly (σ := Fin D × Fin (N + 1)) (R := K)
  set μ : Measure (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) :=
    Measure.pi fun _ : Fin D => (volume : Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere with hμ
  have hgen : ∀ᵐ z ∂μ, ∀ (a : Fin D → ℕ) (p : MvPolynomial (Fin D × Fin (N + 1)) K),
      IsMultiHomogeneous a p → p ≠ 0 → MvPolynomial.eval₂ sg (blockPoint z) p ≠ 0 := by
    rw [ae_all_iff]; intro a
    rw [ae_all_iff]; intro p
    by_cases hp : IsMultiHomogeneous a p ∧ p ≠ 0
    · have hm : IsMultiHomogeneous a (MvPolynomial.map sg p) :=
        fun s hs => hp.1 s (MvPolynomial.support_map_subset _ _ hs)
      have hm0 : MvPolynomial.map sg p ≠ 0 := fun h0 =>
        hp.2 (MvPolynomial.map_injective sg sg.injective (by rw [h0, map_zero]))
      filter_upwards [ae_toSphere D (N + 1) a _ hm0 hm] with z hz _ _
      rwa [MvPolynomial.eval_map] at hz
    · exact Filter.Eventually.of_forall fun z h1 h2 => absurd ⟨h1, h2⟩ hp
  rw [ae_all_iff]; intro p
  by_cases hp : p = 0
  · exact Filter.Eventually.of_forall fun z h => absurd hp h
  set φ : (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) → ℂ := fun t =>
    MvPolynomial.eval₂ sg (fun q => (t q.1 : EuclideanSpace ℂ (Fin (N + 1))) q.2) p with hφ
  have hφc : Continuous φ := by
    have : φ = fun t => MvPolynomial.eval (fun q => (t q.1 : EuclideanSpace ℂ (Fin (N + 1))) q.2) (MvPolynomial.map sg p) := by
      funext t; rw [MvPolynomial.eval_map]
    rw [this]
    exact (MvPolynomial.continuous_eval _).comp (continuous_pi fun q => by fun_prop)
  set T : (Fin (N + 1 + D) → ℝ) → (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) → (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) :=
    fun θ t i => sphereRotation (θ (Fin.natAdd (N + 1) i)) (t i) with hT
  have hTc : Continuous fun x : (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) × (Fin (N + 1 + D) → ℝ) =>
      T x.2 x.1 := by
    refine continuous_pi fun i => ?_
    exact (continuous_sphereRotation (E := EuclideanSpace ℂ (Fin (N + 1)))).comp
      (f := fun x : (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) × (Fin (N + 1 + D) → ℝ) =>
        (x.2 (Fin.natAdd (N + 1) i), x.1 i)) (by fun_prop)
  have hTμ : ∀ θ, MeasurePreserving (T θ) μ μ := fun θ =>
    measurePreserving_pi _ _ fun i => measurePreserving_sphereRotation (volume : Measure (EuclideanSpace ℂ (Fin (N + 1)))) _
  set q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K :=
    MvPolynomial.rename (fun r : Fin D × Fin (N + 1) => (r.1.succ, r.2)) p with hq
  have hq0 : q ≠ 0 := by
    intro h
    apply hp
    refine MvPolynomial.rename_injective (fun r : Fin D × Fin (N + 1) => (r.1.succ, r.2)) ?_
      (by rw [map_zero]; exact h)
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simpa using h
  have h1 : ∀ᵐ t ∂μ, ∀ᵐ θ ∂(volume : Measure (Fin (N + 1 + D) → ℝ)), φ (T θ t) ≠ 0 := by
    filter_upwards [hgen] with t ht
    have hq' : NPB.psi sg (blockPoint t) q ≠ 0 := fun h0 =>
      hq0 (NPB.psi_injective sg (blockPoint t) ht (by rw [h0, map_zero]))
    filter_upwards [ae_eval_circleMap_ne_zero _ _ hq'] with θ hθ
    rw [NPB.eval_psi, hq, MvPolynomial.eval₂_rename] at hθ
    convert hθ using 1
    simp only [hφ]
    congr 1
  rw [Measure.ae_ae_comm (p := fun t θ => φ (T θ t) ≠ 0)
    ((hφc.comp hTc).measurable (measurableSet_singleton 0).compl)] at h1
  have : (ae (volume : Measure (Fin (N + 1 + D) → ℝ))).NeBot := ae_neBot.2 (NeZero.ne _)
  obtain ⟨θ, hθ⟩ := h1.exists
  have h2 : ∀ᵐ t ∂μ, φ t ≠ 0 := by
    rw [← (hTμ θ).map_eq, ae_map_iff (p := fun x => φ x ≠ 0)
      (hTμ θ).measurable.aemeasurable
      (hφc.measurable (measurableSet_singleton 0).compl)]
    exact hθ
  filter_upwards [h2] with t ht _ using ht

end GlobalTheory
end
