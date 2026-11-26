module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentInFibreIffOfIsPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentInFibreIffOfIsPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem image_connectedComponent_of_isEmbedding {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    {q : A → B} (hq : Topology.IsEmbedding q) (a : A) :
    q '' connectedComponent a = connectedComponentIn (Set.range q) (q a) := by
  apply Set.Subset.antisymm
  · exact (isPreconnected_connectedComponent.image q hq.continuous.continuousOn).subset_connectedComponentIn
      ⟨a, mem_connectedComponent, rfl⟩ (Set.image_subset_range _ _)
  · intro x hx
    have hsub : connectedComponentIn (Set.range q) (q a) ⊆ Set.range q := connectedComponentIn_subset _ _
    have himg : q '' (q ⁻¹' connectedComponentIn (Set.range q) (q a)) = connectedComponentIn (Set.range q) (q a) :=
      Set.image_preimage_eq_of_subset hsub
    have hpc : IsPreconnected (q ⁻¹' connectedComponentIn (Set.range q) (q a)) := by
      rw [← hq.isInducing.isPreconnected_image, himg]
      exact isPreconnected_connectedComponentIn
    have hS : q ⁻¹' connectedComponentIn (Set.range q) (q a) ⊆ connectedComponent a :=
      hpc.subset_connectedComponent (mem_connectedComponentIn ⟨a, rfl⟩)
    rw [← himg] at hx
    exact Set.image_mono hS hx

theorem component_in_fibre_iff_of_isPullback :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X) (s : S) (Y : Scheme.{0}) (g : Y ⟶ Spec (S.residueField s))
      (q : Y ⟶ X) (y₀ : Y), IsPullback q g f (S.fromSpecResidueField s) → q y₀ = e s →
      ∀ y : Y, q y ∈ connectedComponentIn (f ⁻¹' {s}) (e s) ↔ y ∈ connectedComponent y₀ := by
  intro X S f e s Y g q y₀ hP h0 y
  haveI : IsPreimmersion q :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) hP.flip inferInstance
  have hq : Topology.IsEmbedding q := q.isEmbedding
  have hr : Set.range q = f ⁻¹' {s} := by
    have h1 : Set.range q = Set.range (pullback.fst f (S.fromSpecResidueField s)) := by
      rw [← hP.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.range_eq_univ.mpr, Set.image_univ]
      exact (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso hP.isoPullback)).surjective
    rw [h1, Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
  rw [← h0, ← hr, ← image_connectedComponent_of_isEmbedding hq]
  exact hq.injective.mem_set_image

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentInFibreIffOfIsPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_connectedComponentIn_fibre_iff_of_isPullback : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X) (s : S) (Y : Scheme.{0}) (g : Y ⟶ Spec (S.residueField s)) (q : Y ⟶ X) (y₀ : Y), IsPullback q g f (S.fromSpecResidueField s) → q y₀ = e s → ∀ y : Y, q y ∈ connectedComponentIn (f ⁻¹' {s}) (e s) ↔ y ∈ connectedComponent y₀ := by
  first | exact @GlobalTheory.component_in_fibre_iff_of_isPullback | exact GlobalTheory.component_in_fibre_iff_of_isPullback | (intros; apply GlobalTheory.component_in_fibre_iff_of_isPullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqPowOfIrreducible
open Polynomial

namespace GlobalTheory.CharpolyPowIrred

theorem charpoly_dvd_pow_of_aeval {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (G : K[X]) (hG : aeval M G = 0) :
    M.charpoly ∣ G ^ Fintype.card ι := by
  classical
  by_cases h0 : G = 0
  · subst h0
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
    · have : M.charpoly = 1 := by
        apply Polynomial.eq_one_of_monic_natDegree_zero M.charpoly_monic
        rw [Matrix.charpoly_natDegree_eq_dim, h]
      rw [this, h, pow_zero]
    · rw [zero_pow h.ne']
      exact dvd_zero _
  let Ω := AlgebraicClosure K
  let f := algebraMap K Ω
  rw [← Polynomial.map_dvd_map' f, Polynomial.map_pow, ← Matrix.charpoly_map]
  set N := M.map f with hNdef
  have hN : aeval N (G.map f) = 0 := by
    rw [aeval_map_algebraMap]
    have := congrArg (AlgHom.mapMatrix (m := ι) (Algebra.ofId K Ω)) hG
    rw [← aeval_algHom_apply, map_zero] at this
    exact this
  have hG0 : G.map f ≠ 0 := Polynomial.map_ne_zero h0
  refine (IsAlgClosed.splits _).dvd_of_roots_le_roots N.charpoly_monic.ne_zero ?_
  rw [roots_pow, Multiset.le_iff_count]
  intro μ
  rw [Multiset.count_nsmul]
  by_cases hμ : μ ∈ N.charpoly.roots
  · have h1 : μ ∈ spectrum Ω N := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
      exact isRoot_of_mem_roots hμ
    have h2 := spectrum.subset_polynomial_aeval N (G.map f) ⟨μ, h1, rfl⟩
    rw [hN] at h2
    have h3 : (G.map f).eval μ = 0 := by
      by_contra hne
      exact (spectrum.mem_iff.1 h2)
        (by simpa using (IsUnit.mk0 _ hne).map (algebraMap Ω (Matrix ι ι Ω)))
    have h4 : 1 ≤ (G.map f).roots.count μ :=
      Multiset.one_le_count_iff_mem.2 ((mem_roots hG0).2 h3)
    calc N.charpoly.roots.count μ ≤ Multiset.card N.charpoly.roots := Multiset.count_le_card _ _
      _ ≤ N.charpoly.natDegree := card_roots' _
      _ = Fintype.card ι := Matrix.charpoly_natDegree_eq_dim N
      _ ≤ Fintype.card ι * (G.map f).roots.count μ := Nat.le_mul_of_pos_right _ h4
  · rw [Multiset.count_eq_zero.2 hμ]
    exact Nat.zero_le _

end GlobalTheory.CharpolyPowIrred
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantDerivationOfCounitalComul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantDerivationOfCounitalComul
open scoped TensorProduct

namespace GlobalTheory

theorem invariant_derivation_exists :
    ∀ (k A : Type) [CommRing k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → ∀ l : A →ₗ[k] k, (∀ a b, l (a * b) = ε a * l b + ε b * l a) → ∃ D : Derivation k A A, ∀ a, ε (D a) = l a := by
  intro k A _ _ _ ε Δ hε l hl
  obtain ⟨h1, h2⟩ := hε
  let F : A ⊗[k] A →ₗ[k] A := (TensorProduct.rid k A).toLinearMap ∘ₗ LinearMap.lTensor A l
  let E : A ⊗[k] A →ₗ[k] A :=
    (TensorProduct.rid k A).toLinearMap ∘ₗ LinearMap.lTensor A ε.toLinearMap
  have hF : ∀ a b : A, F (a ⊗ₜ b) = l b • a := fun a b => by simp [F]
  have hE : ∀ a b : A, E (a ⊗ₜ b) = ε b • a := fun a b => by simp [E]
  have key : ∀ x y : A ⊗[k] A, F (x * y) = E x * F y + E y * F x := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul c d =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, hF, hF, hF, hE, hE, hl]
        simp only [Algebra.smul_def, map_add (f := _), map_mul]
        ring
      | add y₁ y₂ ih₁ ih₂ =>
        rw [mul_add, map_add (f := _), ih₁, ih₂, map_add (f := _), map_add (f := _)]
        ring
    | add x₁ x₂ ih₁ ih₂ =>
      rw [add_mul, map_add (f := _), ih₁, ih₂, map_add (f := _), map_add (f := _)]
      ring
  have hEΔ : ∀ a, E (Δ a) = a := fun a => h2 a
  have hεF : ∀ x : A ⊗[k] A,
      ε (F x) = l (TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [hF]
      simp [mul_comm]
    | add x₁ x₂ ih₁ ih₂ => rw [map_add (f := _), map_add (f := _), ih₁, ih₂, map_add (f := _), map_add (f := _), map_add (f := _)]
  refine ⟨Derivation.mk' (F ∘ₗ Δ.toLinearMap) (fun a b => ?_), fun a => ?_⟩
  · simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, map_mul,
      key, hEΔ, smul_eq_mul]
  · show ε (F (Δ a)) = l a
    rw [hεF, h1]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantDerivationOfCounitalComulStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_derivation_of_counital_comul : ∀ (k A : Type) [CommRing k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → ∀ l : A →ₗ[k] k, (∀ a b, l (a * b) = ε a * l b + ε b * l a) → ∃ D : Derivation k A A, ∀ a, ε (D a) = l a := by
  first | exact @GlobalTheory.invariant_derivation_exists | exact GlobalTheory.invariant_derivation_exists | (intros; apply GlobalTheory.invariant_derivation_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralHasSumEqIntegralIndicatorHasSum
open MeasureTheory

namespace GlobalTheory

theorem integral_hasSum_eq_integral_indicator_hasSum :
    ∀ {X ι : Type} [MeasurableSpace X] [Countable ι] (μ : Measure X) (k : ι → X → ℂ),
      (∀ i, Integrable (k i) μ) → {i | ∫ x, ‖k i x‖ ∂μ ≠ 0}.Finite →
      ∀ (p : Set ι) (K Kp : X → ℂ), (∀ x, HasSum (fun i => k i x) (K x)) →
      (∀ x, HasSum (fun i => p.indicator (fun i => k i x) i) (Kp x)) →
      (∀ i ∉ p, ∫ x, k i x ∂μ = 0) → ∫ x, K x ∂μ = ∫ x, Kp x ∂μ := by
  intro X ι _ _ μ k hk hfin p K Kp hK hKp h0
  classical
  set s := hfin.toFinset with hs
  have hnull : ∀ i ∉ s, k i =ᵐ[μ] 0 := by
    intro i hi
    have hi' : ∫ x, ‖k i x‖ ∂μ = 0 := by
      by_contra h
      exact hi (by simpa [hs] using h)
    have := (integral_eq_zero_iff_of_nonneg (fun x => norm_nonneg (k i x)) (hk i).norm).1 hi'
    filter_upwards [this] with x hx
    simpa using hx
  have hall : ∀ᵐ x ∂μ, ∀ i, i ∉ s → k i x = 0 := by
    rw [ae_all_iff]
    intro i
    by_cases hi : i ∈ s
    · exact Filter.Eventually.of_forall (fun x h => absurd hi h)
    · filter_upwards [hnull i hi] with x hx _
      exact hx
  have hKae : K =ᵐ[μ] fun x => ∑ i ∈ s, k i x := by
    filter_upwards [hall] with x hx
    exact (hK x).unique (hasSum_sum_of_ne_finset_zero (fun i hi => hx i hi))
  have hKpae : Kp =ᵐ[μ] fun x => ∑ i ∈ s, p.indicator (fun i => k i x) i := by
    filter_upwards [hall] with x hx
    refine (hKp x).unique (hasSum_sum_of_ne_finset_zero (fun i hi => ?_))
    by_cases hp : i ∈ p
    · simp [Set.indicator_of_mem hp, hx i hi]
    · simp [Set.indicator_of_notMem hp]
  have hind : ∀ i, (fun x => p.indicator (fun i => k i x) i) =
      if i ∈ p then k i else fun _ => 0 := by
    intro i
    by_cases hp : i ∈ p
    · funext x; simp [Set.indicator_of_mem hp, hp]
    · funext x; simp [Set.indicator_of_notMem hp, hp]
  rw [integral_congr_ae hKae, integral_congr_ae hKpae,
    MeasureTheory.integral_finsetSum s (fun i _ => hk i),
    MeasureTheory.integral_finsetSum s (fun i _ => by
      rw [hind i]; split_ifs
      · exact hk i
      · exact integrable_zero _ _ _)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hind i]
  split_ifs with hp
  · rfl
  · simp [h0 i hp]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizerEqPowRamificationIdxMulUnitIntegralCl
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizerEqPowRamificationIdxMulUnitIntegralCl
open IsLocalRing

namespace GlobalTheory

theorem pi_eq_pow_ramificationIdx_mul_unit
    (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D]
    (P : Ideal (integralClosure S L)) [P.IsMaximal] :
    Irreducible π → algebraMap S (integralClosure S L) π ∈ P →
      ∃ ϖ : Localization.AtPrime P, Irreducible ϖ ∧ ∃ u : (Localization.AtPrime P)ˣ,
        algebraMap S (Localization.AtPrime P) π = ϖ ^ P.ramificationIdx S * (u : Localization.AtPrime P) := by
  intro hπ hπP
  haveI : IsDedekindDomain (integralClosure S L) := integralClosure.isDedekindDomain S K L
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hO0 : algebraMap S (integralClosure S L) π ≠ 0 := by
    intro h
    have h2 : algebraMap (integralClosure S L) L (algebraMap S (integralClosure S L) π) = 0 := by rw [h, map_zero]
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply S K L] at h2
    rw [map_eq_zero_iff _ (algebraMap K L).injective,
      map_eq_zero_iff _ (IsFractionRing.injective S K)] at h2
    exact hπ0 h2
  have hPbot : P ≠ ⊥ := fun h => hO0 (by rw [h] at hπP; simpa using hπP)
  haveI hA : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (integralClosure S L) hPbot (Localization.AtPrime P)
  have hinj : Function.Injective (algebraMap (integralClosure S L) (Localization.AtPrime P)) :=
    IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors
  have hx0 : algebraMap S (Localization.AtPrime P) π ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply S (integralClosure S L) (Localization.AtPrime P)]
    exact fun h => hO0 (hinj (by rw [h, map_zero]))
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime P)
  obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ

  have hunder : P.under S = Ideal.span {π} := by
    have hmem : π ∈ P.under S := by simpa [Ideal.under] using hπP
    have hne : P.under S ≠ ⊥ := fun h => hπ0 (by rw [h] at hmem; simpa using hmem)
    have hmax : (P.under S).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
    rw [IsLocalRing.eq_maximalIdeal hmax, hπ.maximalIdeal_eq]
  have hram : P.ramificationIdx S = n := by
    rw [Ideal.ramificationIdx_def, hunder, Ideal.map_span, Set.image_singleton, hn,
      Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
      ← hϖ.maximalIdeal_eq, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal,
      ENat.toNat_natCast]
  refine ⟨ϖ, hϖ, u, ?_⟩
  rw [hram, hn, mul_comm]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizerEqPowRamificationIdxMulUnitIntegralClStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_eq_pow_ramificationIdx_mul_unit_integralClosure : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D] (P : Ideal (integralClosure S L)) [P.IsMaximal], Irreducible π → algebraMap S (integralClosure S L) π ∈ P → ∃ ϖ : Localization.AtPrime P, Irreducible ϖ ∧ ∃ u : (Localization.AtPrime P)ˣ, algebraMap S (Localization.AtPrime P) π = ϖ ^ P.ramificationIdx S * (u : Localization.AtPrime P) := by
  first | (exact @GlobalTheory.pi_eq_pow_ramificationIdx_mul_unit) | (exact GlobalTheory.pi_eq_pow_ramificationIdx_mul_unit) | (intros; apply GlobalTheory.pi_eq_pow_ramificationIdx_mul_unit  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerLeSpanImageKerOfSemilinear
open scoped InnerProductSpace

namespace GlobalTheory

theorem ker_le_span_image_ker_of_semilinear :
    ∀ (K X Y H W : Type) [Field K] [AddCommGroup X] [Module K X] [FiniteDimensional K X] [AddCommGroup Y] [Module K Y] [AddCommGroup H] [Module ℂ H] [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) (θ : X →ₗ[K] Y) (j : X →ₛₗ[σ] H) (jW : Y →ₛₗ[σ] W) (T : H →ₗ[ℂ] W), Submodule.span ℂ (Set.range j) = ⊤ → (∀ (n : ℕ) (b : Fin n → Y), LinearIndependent K b → LinearIndependent ℂ fun k => jW (b k)) → (∀ x, T (j x) = jW (θ x)) → LinearMap.ker T ≤ Submodule.span ℂ (j '' (LinearMap.ker θ : Set X)) := by
  intro K X Y H W _ _ _ _ _ _ _ _ _ _ σ θ j jW T hspan hind hT
  classical
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.ker θ)
  let b := Module.finBasis K C
  have hinj : LinearMap.ker (θ ∘ₗ C.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro m hm
    have h1 : (m : X) ∈ LinearMap.ker θ := hm
    have h2 : (m : X) ∈ LinearMap.ker θ ⊓ C := ⟨h1, m.2⟩
    rw [hC.inf_eq_bot] at h2
    exact Subtype.ext (by simpa using h2)
  have hli : LinearIndependent K (fun k => θ (b k : X)) :=
    b.linearIndependent.map' (θ ∘ₗ C.subtype) hinj
  have hli2 := hind _ _ hli
  set N := Submodule.span ℂ (j '' (LinearMap.ker θ : Set X)) with hN
  have hNT : N ≤ LinearMap.ker T := by
    rw [hN, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : θ x = 0 := hx
    show T (j x) = 0
    rw [hT, hx', map_zero]
  have htop : N ⊔ Submodule.span ℂ (Set.range fun k => j (b k : X)) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ LinearMap.ker θ ⊔ C := by rw [hC.sup_eq_top]; trivial
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _)]
    refine Submodule.add_mem_sup (Submodule.subset_span ⟨u, hu, rfl⟩) ?_
    have hcs : c = ∑ k, b.repr ⟨c, hc⟩ k • (b k : X) := by
      have := congrArg (fun z : C => (z : X)) (b.sum_repr ⟨c, hc⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hcs, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  intro h hh
  have hmem : h ∈ N ⊔ Submodule.span ℂ (Set.range fun k => j (b k : X)) := by
    rw [htop]; trivial
  obtain ⟨u, hu, s, hs, rfl⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hs
  have hTu : T u = 0 := hNT hu
  have h0 : ∑ k, a k • jW (θ (b k : X)) = 0 := by
    have : T (u + ∑ k, a k • j (b k : X)) = 0 := hh
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), hTu, zero_add, map_sum] at this
    simpa [hT] using this
  have ha := Fintype.linearIndependent_iff.1 hli2 a h0
  simpa [ha] using hu

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfIrred
universe u v

namespace GlobalTheory.CompanionTheory.BurnsideU

theorem mem_of_irred {K : Type u} {V : Type v} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : Subalgebra K (Module.End K V))
    (hirr : ∀ N : Submodule K V, (∀ f ∈ S, ∀ v ∈ N, f v ∈ N) → N = ⊥ ∨ N = ⊤)
    (f : Module.End K V) : f ∈ S := by
  classical
  rcases subsingleton_or_nontrivial V with hV | hV
  · have hf : f = 0 := LinearMap.ext fun v => Subsingleton.elim _ _
    rw [hf]
    exact S.zero_mem

  have : IsScalarTower K S V := ⟨fun _ _ _ => rfl⟩
  have : Nontrivial (Submodule S V) := (Submodule.nontrivial_iff S).mpr hV

  have : IsSimpleModule S V :=
    { eq_bot_or_eq_top := fun N => by
        rcases hirr (N.restrictScalars K) (fun g hg v hv => N.smul_mem ⟨g, hg⟩ hv) with h | h
        · exact Or.inl ((Submodule.restrictScalars_eq_bot_iff K S V).mp h)
        · exact Or.inr ((Submodule.restrictScalars_eq_top_iff K S V).mp h) }

  have hschur := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := S) (V := V) K

  let F : Module.End (Module.End S V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun g v => by
        obtain ⟨c, rfl⟩ := hschur.2 g
        change f ((algebraMap K (Module.End S V) c) v) = (algebraMap K (Module.End S V) c) (f v)
        simp [Module.algebraMap_end_apply, f.map_smul] }

  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := K) (M := V)
  obtain ⟨r, hr⟩ := jacobson_density F s
  have hfr : f = (r : Module.End K V) := by
    apply LinearMap.ext
    intro m
    have hm : m ∈ Submodule.span K (s : Set V) := hs ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem m hm => exact hr m hm
    | zero => simp
    | add _ _ _ _ h₁ h₂ => rw [map_add (f := _), map_add (f := _), h₁, h₂]
    | smul c _ _ h => rw [map_smul, map_smul, h]
  rw [hfr]
  exact r.2

theorem burnside_surj_of_irred {A : Type u} {V : Type v} [Ring A] [Algebra ℂ A] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V)
    (hirr : ∀ W : Submodule ℂ V, (∀ h, ∀ w ∈ W, ρ h w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Function.Surjective ρ :=
    by
    intro f
    have hf : f ∈ ρ.range :=
      mem_of_irred ρ.range (fun W hW => hirr W fun h w hw => hW (ρ h) ⟨h, rfl⟩ w hw) f
    obtain ⟨h, rfl⟩ := (AlgHom.mem_range ρ).mp hf
    exact ⟨h, rfl⟩

end GlobalTheory.CompanionTheory.BurnsideU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfMapPderivEqAndMapOneNeZero
namespace GlobalTheory.FockAlg


open MvPolynomial in
theorem injective_of_pderiv {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type}
    (Φ₀ : MvPolynomial ι ℂ →ₗ[ℂ] V) (d : ι → Module.End ℂ V)
    (hd : ∀ (i : ι) (p : MvPolynomial ι ℂ), Φ₀ (MvPolynomial.pderiv i p) = d i (Φ₀ p))
    (h1 : Φ₀ 1 ≠ 0) : Function.Injective Φ₀ := by
  classical
  have hC : ∀ p : MvPolynomial ι ℂ, Φ₀ p = 0 → (∀ m ∈ p.support, m = 0) → p = 0 := by
    intro p hp hs
    have e : p = (p.coeff 0) • (1 : MvPolynomial ι ℂ) := by
      ext m
      by_cases hm : m = 0
      · subst hm; simp
      · have : p.coeff m = 0 := by
          by_contra h
          exact hm (hs m (mem_support_iff.2 h))
        rw [this, coeff_smul, coeff_one, if_neg (Ne.symm hm), smul_zero]
    rw [e, map_smul, smul_eq_zero] at hp
    rcases hp with hp | hp
    · rw [e, hp, zero_smul]
    · exact absurd hp h1
  have key : ∀ n : ℕ, ∀ p : MvPolynomial ι ℂ, (∀ m ∈ p.support, m.degree ≤ n) →
      Φ₀ p = 0 → p = 0 := by
    intro n
    induction n with
    | zero =>
      intro p hs hp
      exact hC p hp (fun m hm => (Finsupp.degree_eq_zero_iff m).1 (Nat.le_zero.1 (hs m hm)))
    | succ n ih =>
      intro p hs hp
      have hz : ∀ i, pderiv i p = 0 := by
        intro i
        apply ih
        · intro m hm
          rw [mem_support_iff, coeff_pderiv] at hm
          have h2 := hs _ (mem_support_iff.2 (left_ne_zero_of_mul hm))
          rw [map_add (f := _), Finsupp.degree_single] at h2
          omega
        · rw [hd, hp, map_zero]
      apply hC p hp
      intro m hm
      by_contra hm0
      obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
        by_contra h
        push Not at h
        exact hm0 (Finsupp.ext h)
      have hle : Finsupp.single i 1 ≤ m := by
        rw [Finsupp.single_le_iff]; omega
      have hc := congrArg (fun q : MvPolynomial ι ℂ => q.coeff (m - Finsupp.single i 1)) (hz i)
      rw [coeff_pderiv, tsub_add_cancel_of_le hle, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, mul_eq_zero] at hc
      rcases hc with hc | hc
      · exact (mem_support_iff.1 hm) hc
      · exact (Nat.cast_add_one_ne_zero _) hc
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro p hp
  exact key (p.support.sup fun m => m.degree) p
    (fun m hm => Finset.le_sup (f := fun m : ι →₀ ℕ => m.degree) hm) hp

end GlobalTheory.FockAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperEighthFibrePowerOver
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperEighthFibrePowerOver
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.FibrePowerProper

theorem isProper_hom_of_iso {T : Scheme.{0}} {X Y : Over T} (e : X ≅ Y) (h : IsProper Y.hom) :
    IsProper X.hom := by
  have hw : X.hom = e.hom.left ≫ Y.hom := (Over.w e.hom).symm
  haveI : IsIso e.hom.left := (Over.forget T).map_isIso e.hom
  rw [hw]
  infer_instance

theorem isProper_prod_hom {T : Scheme.{0}} (X Y : Over T) (hX : IsProper X.hom)
    (hY : IsProper Y.hom) : IsProper (X ⨯ Y).hom := by
  have h1 : (X ⨯ Y).hom = (Over.prodLeftIsoPullback X Y).hom ≫ pullback.fst X.hom Y.hom ≫ X.hom := by
    rw [← Category.assoc, Over.prodLeftIsoPullback_hom_fst]
    exact (Over.w (prod.fst : X ⨯ Y ⟶ X)).symm
  have hfst : IsProper (pullback.fst X.hom Y.hom) := by haveI := hY; infer_instance
  rw [h1]
  infer_instance

theorem isProper_fan_pt {T : Scheme.{0}} : ∀ (n : ℕ) (f : Fin n → Over T),
    (∀ i, IsProper (f i).hom) → ∀ (c : Fan f), IsLimit c → IsProper c.pt.hom := by
  intro n
  induction n with
  | zero =>
      intro f _ c hc
      have h0 : IsLimit (Fan.mk (Over.mk (𝟙 T)) (fun i => i.elim0 : ∀ i, Over.mk (𝟙 T) ⟶ f i)) :=
        Fan.IsLimit.mk _ (fun _ => Over.mkIdTerminal.from _) (fun _ k => k.elim0)
          (fun _ _ _ => Over.mkIdTerminal.hom_ext _ _)
      have hId : IsProper (𝟙 T) := inferInstance
      exact isProper_hom_of_iso (hc.conePointUniqueUpToIso h0) hId
  | succ n ih =>
      intro f hf c hc
      let c₁ : Fan (fun i : Fin n => f i.succ) := limit.cone (Discrete.functor fun i : Fin n => f i.succ)
      have h1 : IsProper c₁.pt.hom :=
        ih (fun i => f i.succ) (fun i => hf i.succ) c₁ (limit.isLimit _)
      have hl := extendFanIsLimit f (limit.isLimit (Discrete.functor fun i : Fin n => f i.succ))
        (prodIsProd (f 0) c₁.pt)
      exact isProper_hom_of_iso (hc.conePointUniqueUpToIso hl) (isProper_prod_hom _ _ (hf 0) h1)

theorem isProper_eighth_fibre_power : ∀ {T : Scheme.{0}} {B C : Over T} (pr : Fin 8 → (B ⟶ C)),
    (∀ (T' : Over T) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr a = y a) →
    IsProper C.hom → IsProper B.hom := by
  intro T B C pr hu hC
  have hl : IsLimit (Fan.mk B pr) :=
    Fan.IsLimit.mk _ (fun s => (hu s.pt s.proj).choose)
      (fun s a => (hu s.pt s.proj).choose_spec.1 a)
      (fun s m hm => (hu s.pt s.proj).choose_spec.2 m hm)
  exact isProper_fan_pt 8 (fun _ => C) (fun _ => hC) _ hl

end GlobalTheory.FibrePowerProper
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperEighthFibrePowerOverStatement
open AlgebraicGeometry CategoryTheory Limits

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_eighth_fibre_power_over : ∀ {T : Scheme.{0}} {B C : Over T} (pr : Fin 8 → (B ⟶ C)), (∀ (T' : Over T) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr a = y a) → IsProper C.hom → IsProper B.hom := by
  first | exact @GlobalTheory.FibrePowerProper.isProper_eighth_fibre_power | exact GlobalTheory.FibrePowerProper.isProper_eighth_fibre_power | (intros; apply GlobalTheory.FibrePowerProper.isProper_eighth_fibre_power <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorCentralizerInjectiveCommutantEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorCentralizerInjectiveCommutantEq
open scoped TensorProduct Classical

namespace GlobalTheory

theorem tensor_centralizer_flat : ∀ (K : Type) [Field K] [Algebra ℚ K] (C : Type) [Ring C] [Algebra ℚ C] (y : C),
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id K K) (Subalgebra.centralizer ℚ ({y} : Set C)).val) ∧
    ∀ w : K ⊗[ℚ] C, Commute w ((1 : K) ⊗ₜ[ℚ] y) → ∃ w' : K ⊗[ℚ] (Subalgebra.centralizer ℚ ({y} : Set C)),
      Algebra.TensorProduct.map (AlgHom.id K K) (Subalgebra.centralizer ℚ ({y} : Set C)).val w' = w := by
  intro K _ _ C _ _ y
  set Z := Subalgebra.centralizer ℚ ({y} : Set C) with hZ
  have hmap : ∀ w', Algebra.TensorProduct.map (AlgHom.id K K) Z.val w'
      = LinearMap.lTensor K Z.val.toLinearMap w' := by
    intro w'
    induction w' using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  let ad : C →ₗ[ℚ] C := LinearMap.mulRight ℚ y - LinearMap.mulLeft ℚ y
  have hex : Function.Exact Z.val.toLinearMap ad := by
    intro x
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      rw [Subalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      have : x * g - g * x = 0 := by simpa [ad] using hx
      exact (sub_eq_zero.mp this).symm
    · rintro ⟨z, rfl⟩
      have hz := z.2
      rw [Subalgebra.mem_centralizer_iff] at hz
      have := hz y (Set.mem_singleton y)
      simp [ad, this]
  have hexK := Module.Flat.lTensor_exact K hex
  have hadK : ∀ w : K ⊗[ℚ] C, LinearMap.lTensor K ad w = w * ((1 : K) ⊗ₜ[ℚ] y) - ((1 : K) ⊗ₜ[ℚ] y) * w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [ad, TensorProduct.tmul_sub]
    | add a b ha hb => rw [map_add (f := _), ha, hb, add_mul, mul_add]; abel
  refine ⟨?_, ?_⟩
  · intro a b hab
    rw [hmap, hmap] at hab
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective hab
  · intro w hw
    have h0 : LinearMap.lTensor K ad w = 0 := by
      rw [hadK, hw.eq, sub_self]
    obtain ⟨w', hw'⟩ := (hexK w).mp h0
    exact ⟨w', by rw [hmap]; exact hw'⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorCentralizerInjectiveCommutantEqStatement
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_centralizer_injective_commutant_eq : ∀ (K : Type) [Field K] [Algebra ℚ K] (C : Type) [Ring C] [Algebra ℚ C] (y : C),
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id K K) (Subalgebra.centralizer ℚ ({y} : Set C)).val) ∧
    ∀ w : K ⊗[ℚ] C, Commute w ((1 : K) ⊗ₜ[ℚ] y) → ∃ w' : K ⊗[ℚ] (Subalgebra.centralizer ℚ ({y} : Set C)),
      Algebra.TensorProduct.map (AlgHom.id K K) (Subalgebra.centralizer ℚ ({y} : Set C)).val w' = w := by
  first | (exact @GlobalTheory.tensor_centralizer_flat) | (exact GlobalTheory.tensor_centralizer_flat) | (intros; apply GlobalTheory.tensor_centralizer_flat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyEntriesConjLeftRightMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyEntriesConjLeftRightMul
noncomputable section

open MvPolynomial

namespace GlobalTheory.PolyEntryMul

theorem totalDegree_bind₁_le_of_le_one {σ τ : Type*} (f : σ → MvPolynomial τ ℂ)
    (hf : ∀ i, (f i).totalDegree ≤ 1) (Q : MvPolynomial σ ℂ) :
    (bind₁ f Q).totalDegree ≤ Q.totalDegree := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [Q.as_sum, map_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hs)
  refine (Finset.sum_le_sum fun i _ => (totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left _ (hf i))).trans ?_
  simp [Finsupp.sum]

def subst {n : ℕ} (a b : Matrix (Fin n) (Fin n) ℂ) :
    (Fin n × Fin n) ⊕ (Fin n × Fin n) → MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ
  | Sum.inl z => ∑ k : Fin n, ∑ l : Fin n, C (a z.1 k * b l z.2) * X (Sum.inl (k, l))
  | Sum.inr z => ∑ k : Fin n, ∑ l : Fin n, C (star (a z.1 k * b l z.2)) * X (Sum.inr (k, l))

theorem totalDegree_subst {n : ℕ} (a b : Matrix (Fin n) (Fin n) ℂ) (i) :
    (subst a b i).totalDegree ≤ 1 := by
  rcases i with z | z <;>
  · refine totalDegree_finsetSum_le fun k _ => totalDegree_finsetSum_le fun l _ => ?_
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X]

theorem main : ∀ (n : ℕ) (a b : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ), ∃ Q : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ, Q.totalDegree ≤ P.totalDegree ∧ ∀ g : Matrix (Fin n) (Fin n) ℂ, MvPolynomial.eval (Sum.elim (fun z : Fin n × Fin n => (a * g * b) z.1 z.2) (fun z : Fin n × Fin n => star ((a * g * b) z.1 z.2))) P = MvPolynomial.eval (Sum.elim (fun z : Fin n × Fin n => (g) z.1 z.2) (fun z : Fin n × Fin n => star ((g) z.1 z.2))) Q := by
  intro n a b P
  refine ⟨bind₁ (subst a b) P, totalDegree_bind₁_le_of_le_one _ (totalDegree_subst a b) P, fun g => ?_⟩
  conv_rhs => rw [eval, eval₂Hom_bind₁]
  rw [eval]
  refine congrArg (fun x => eval₂Hom (RingHom.id ℂ) x P) (funext fun i => ?_)
  rcases i with z | z
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [Sum.elim_inl, subst, map_sum, map_mul, coe_eval₂Hom, eval₂_C, eval₂_X,
      RingHom.id_apply, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [Sum.elim_inr, subst, map_sum, map_mul, coe_eval₂Hom, eval₂_C, eval₂_X,
      RingHom.id_apply, Matrix.mul_apply, Finset.sum_mul, star_sum, star_mul']
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    ring

end GlobalTheory.PolyEntryMul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyEntriesConjLeftRightMulStatement
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_poly_entries_conj_left_right_mul : ∀ (n : ℕ) (a b : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ), ∃ Q : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ, Q.totalDegree ≤ P.totalDegree ∧ ∀ g : Matrix (Fin n) (Fin n) ℂ, MvPolynomial.eval (Sum.elim (fun z : Fin n × Fin n => (a * g * b) z.1 z.2) (fun z : Fin n × Fin n => star ((a * g * b) z.1 z.2))) P = MvPolynomial.eval (Sum.elim (fun z : Fin n × Fin n => (g) z.1 z.2) (fun z : Fin n × Fin n => star ((g) z.1 z.2))) Q := by
  first | exact @GlobalTheory.PolyEntryMul.main | exact GlobalTheory.PolyEntryMul.main | (intros; apply GlobalTheory.PolyEntryMul.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddValuationNatCastEqPadicValNat
namespace GlobalTheory

theorem addValuation_natCast_eq_padicValNat :
    ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime →
      v (p : C) = 1 → ∀ n : ℕ, n ≠ 0 →
        v (n : C) = (((padicValNat p n : ℕ) : ℝ) : WithTop ℝ) := by
  intro C _ _ v p hp hvp n hn
  have h1 : v (1 : C) = 0 := v.map_one

  have hnat : ∀ m : ℕ, 0 ≤ v (m : C) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      have h := v.map_add (k : C) 1
      rw [h1] at h
      push_cast
      exact le_trans (le_min ih le_rfl) h
  have hint : ∀ a : ℤ, 0 ≤ v (a : C) := by
    intro a
    obtain ⟨m, rfl | rfl⟩ := a.eq_nat_or_neg
    · simpa using hnat m
    · simpa [v.map_neg] using hnat m

  have hcop : ∀ m : ℕ, Nat.Coprime m p → v (m : C) = 0 := by
    intro m hm
    by_contra hne
    have hpos : 0 < v (m : C) := lt_of_le_of_ne (hnat m) (Ne.symm hne)
    have hbez : ((1 : ℤ)) = (m : ℤ) * Nat.gcdA m p + (p : ℤ) * Nat.gcdB m p := by
      have := Nat.gcd_eq_gcd_ab m p
      rw [hm] at this
      simpa using this
    have hC : (1 : C) = (m : C) * ((Nat.gcdA m p : ℤ) : C) + (p : C) * ((Nat.gcdB m p : ℤ) : C) := by
      have := congrArg (fun z : ℤ => (z : C)) hbez
      simpa using this
    have ha : 0 < v ((m : C) * ((Nat.gcdA m p : ℤ) : C)) := by
      rw [v.map_mul]
      exact lt_of_lt_of_le hpos (le_add_of_nonneg_right (hint _))
    have hb : 0 < v ((p : C) * ((Nat.gcdB m p : ℤ) : C)) := by
      rw [v.map_mul, hvp]
      exact lt_of_lt_of_le (by exact_mod_cast zero_lt_one) (le_add_of_nonneg_right (hint _))
    have h := v.map_add ((m : C) * ((Nat.gcdA m p : ℤ) : C)) ((p : C) * ((Nat.gcdB m p : ℤ) : C))
    rw [← hC, h1] at h
    exact absurd (lt_of_lt_of_le (lt_min ha hb) h) (lt_irrefl _)

  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := (fun {p n : ℕ} => _root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat p n)) (p := p) (n := n)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hn (by simpa using hm)
  have hnd : ¬ p ∣ m := by
    intro hd
    obtain ⟨c, rfl⟩ := hd
    have : p ^ (padicValNat p n + 1) ∣ n := ⟨c, by rw [pow_succ, mul_assoc, ← hm]⟩
    rw [Nat.padicValNat_def] at this
    exact pow_succ_multiplicity_not_dvd (p := p) hn this
  have hcm : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd).symm
  have hcast : (n : C) = (p : C) ^ (padicValNat p n) * (m : C) := by
    conv_lhs => rw [hm]
    push_cast
    ring
  rw [hcast, v.map_mul, v.map_pow, hvp, hcop m hcm, add_zero]
  simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralConeRingOfForallValuationSubring
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralConeRingOfForallValuationSubring
open MvPolynomial

namespace GlobalTheory

theorem isIntegral_coneRing_of_forall_valuationSubring :
    ∀ (F K : Type) [Field F] [Field K] (φ : F →+* K) (r e : ℕ) (w : Fin r → K) (τ : K), (∀ V : ValuationSubring K, (∀ c, φ c ∈ V) → ∃ i, w i ≠ 0 ∧ τ / w i ^ e ∈ V) → ∃ (m : ℕ) (b : Fin m → MvPolynomial (Fin r) F), (Polynomial.C τ * Polynomial.X ^ e) ^ m + ∑ k, MvPolynomial.eval₂ (Polynomial.C.comp φ) (fun i => Polynomial.C (w i) * Polynomial.X) (b k) * (Polynomial.C τ * Polynomial.X ^ e) ^ (k : ℕ) = 0 := by
  intro F K _ _ φ r e w τ h
  classical
  let L := FractionRing (Polynomial K)
  let j : Polynomial K →+* L := algebraMap (Polynomial K) L
  let g : MvPolynomial (Fin r) F →+* Polynomial K :=
    MvPolynomial.eval₂Hom (Polynomial.C.comp φ) (fun i => Polynomial.C (w i) * Polynomial.X)
  let y : Polynomial K := Polynomial.C τ * Polynomial.X ^ e
  have hjinj : Function.Injective j := IsFractionRing.injective _ _
  have hx : j y ∈ (integralClosure (Subring.closure (Set.range (j.comp g))) L).toSubring := by
    rw [← iInf_valuationSubring_superset, Subring.mem_iInf]
    intro V
    obtain ⟨W, hW⟩ := V
    change j y ∈ W
    let U : ValuationSubring K := W.comap (j.comp Polynomial.C)
    have hU : ∀ c, φ c ∈ U := by
      intro c
      have : j (g (MvPolynomial.C c)) ∈ W := hW ⟨_, rfl⟩
      simpa [g, U] using this
    obtain ⟨i, hi, hτ⟩ := h U hU
    have h1 : j (Polynomial.C (w i) * Polynomial.X) ∈ W := by
      have : j (g (MvPolynomial.X i)) ∈ W := hW ⟨_, rfl⟩
      simpa [g] using this
    have h2 : j (Polynomial.C (τ / w i ^ e)) ∈ W := hτ
    have hy : y = Polynomial.C (τ / w i ^ e) * (Polynomial.C (w i) * Polynomial.X) ^ e := by
      rw [mul_pow, ← mul_assoc, ← Polynomial.C_pow, ← Polynomial.C_mul,
        div_mul_cancel₀ _ (pow_ne_zero _ hi)]
    rw [hy, map_mul, map_pow]
    exact mul_mem h2 (pow_mem h1 _)
  have hcl : Subring.closure (Set.range (j.comp g)) = (j.comp g).range := by
    rw [← RingHom.coe_range]; exact Subring.closure_eq _
  rw [hcl] at hx
  have hint : IsIntegral (j.comp g).range (j y) := hx
  obtain ⟨p, hp, hpx⟩ := hint
  have hb : ∀ k : Fin p.natDegree, ∃ b : MvPolynomial (Fin r) F, j (g b) = (p.coeff k : L) :=
    fun k => (p.coeff k).2
  choose b hb using hb
  refine ⟨p.natDegree, b, hjinj ?_⟩
  have e1 := hpx
  rw [hp.as_sum] at e1
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at e1
  rw [Finset.sum_range (fun k => algebraMap (j.comp g).range L (p.coeff k) * j y ^ k)] at e1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, ← e1, map_add (f := _), map_sum, map_pow]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_pow]
  exact congrArg (· * j y ^ (k : ℕ)) (hb k)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralConeRingOfForallValuationSubringStatement
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_relation_C_mul_X_pow_of_valuationSubring : ∀ (F K : Type) [Field F] [Field K] (φ : F →+* K) (r e : ℕ) (w : Fin r → K) (τ : K), (∀ V : ValuationSubring K, (∀ c, φ c ∈ V) → ∃ i, w i ≠ 0 ∧ τ / w i ^ e ∈ V) → ∃ (m : ℕ) (b : Fin m → MvPolynomial (Fin r) F), (Polynomial.C τ * Polynomial.X ^ e) ^ m + ∑ k, MvPolynomial.eval₂ (Polynomial.C.comp φ) (fun i => Polynomial.C (w i) * Polynomial.X) (b k) * (Polynomial.C τ * Polynomial.X ^ e) ^ (k : ℕ) = 0 := by
  first | exact @GlobalTheory.isIntegral_coneRing_of_forall_valuationSubring | exact GlobalTheory.isIntegral_coneRing_of_forall_valuationSubring | (intros; apply GlobalTheory.isIntegral_coneRing_of_forall_valuationSubring <;> assumption)
end
end
