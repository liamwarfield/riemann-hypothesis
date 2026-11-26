module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StAdjoinIndepRelfinrank

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

def momentPoly {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ)
    (Q : MvPolynomial (Fin 3) (Ω → ℝ)) : MvPolynomial (Fin 3) ℝ :=
  ∑ m ∈ Q.support, monomial m (∫ p, w p * AddMonoidAlgebra.coeff Q m p ∂μ)

def dotPoly {Ω : Type*} (n : Ω → S2) : MvPolynomial (Fin 3) (Ω → ℝ) :=
  ∑ i, X i * C (fun p => (n p : E3) i)

def fibreMomentPoly (k : ℕ) : MvPolynomial (Fin 3) ℝ :=
  momentPoly (sphereMeasure.prod sphereMeasure)
    (fun p : S2 × S2 => (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (p.1 : E3) (p.2 : E3)) / 2))
    (aeval ![dotPoly Prod.fst, dotPoly Prod.snd] (dgPoly k))

def pushMomentPoly (k : ℕ) : MvPolynomial (Fin 3) ℝ :=
  (-(2 * (k : ℝ) - 1)) • momentPoly sphereMeasure (fun _ => 1) (dotPoly id ^ (2 * k - 2))

def FibreLocal.Statement : Prop :=
  (∀ (k : ℕ) (a : E3),
    ∫ n₁ : S2, ∫ n₂ : S2, (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (n₁ : E3) (n₂ : E3)) / 2) *
        eval ![inner ℝ a (n₁ : E3), inner ℝ a (n₂ : E3)] (dgPoly k) ∂sphereMeasure ∂sphereMeasure =
      -kappa k * inner ℝ a a ^ (k - 1)) ∧
  (∀ (k : ℕ) (B : Type) [CommRing B] [Algebra ℝ B] (a : Fin 3 → B),
    aeval a (fibreMomentPoly k) = algebraMap ℝ B (-kappa k) * (∑ i, a i ^ 2) ^ (k - 1)) ∧
  (∀ k : ℕ, 1 ≤ k → ∀ a : E3,
    -(2 * (k : ℝ) - 1) * ∫ n : S2, inner ℝ a (n : E3) ^ (2 * k - 2) ∂sphereMeasure =
      -(inner ℝ a a ^ (k - 1))) ∧
  (∀ k : ℕ, 1 ≤ k → ∀ (B : Type) [CommRing B] [Algebra ℝ B] (a : Fin 3 → B),
    aeval a (pushMomentPoly k) = -(∑ i, a i ^ 2) ^ (k - 1)) ∧
  ∀ k : ℕ, kappa k = (1 / 2) * ∑ j ∈ Finset.range k, (1 : ℝ) / (2 * j + 1)

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PAdjoinIndepRelfinrank
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open IntermediateField IntermediateField.algebraAdjoinAdjoin Module

theorem AdjoinIndepRelfinrank.proof : AdjoinIndepRelfinrank.Statement := by
  intro F Ω _ _ _ L₀ L ι t hle ht
  set L' : IntermediateField L₀ Ω := extendScalars hle with hL'
  set A : IntermediateField L₀ Ω := adjoin L₀ (Set.range t) with hA
  have ht' : AlgebraicIndependent L' t := ht

  let b := Module.Free.chooseBasis L₀ L'

  have hR : LinearIndependent (Algebra.adjoin L₀ (Set.range t)) (algebraMap L' Ω ∘ b) := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have hmem : ∀ j, ∃ p : MvPolynomial ι L₀, MvPolynomial.aeval t p = (g j : Ω) := fun j => by
      have : (g j : Ω) ∈ (MvPolynomial.aeval t : MvPolynomial ι L₀ →ₐ[L₀] Ω).range := by
        rw [← Algebra.adjoin_range_eq_range_aeval]
        exact (g j).2
      obtain ⟨p, hp⟩ := this
      exact ⟨p, hp⟩
    choose p hp using hmem
    set q : MvPolynomial ι L' :=
      ∑ j ∈ s, MvPolynomial.C (b j) * MvPolynomial.map (algebraMap L₀ L') (p j) with hq
    have hq0 : q = 0 := by
      apply ht'.eq_zero_of_aeval_eq_zero
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hq, map_sum]
      rw [← hg]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_map_algebraMap, hp, Subalgebra.smul_def,
        Function.comp_apply, mul_comm]
      rfl
    have hcoef : ∀ m, ∀ j ∈ s, AddMonoidAlgebra.coeff (p j) m = 0 := by
      intro m
      have h := congrArg (AddMonoidAlgebra.coeff · m) hq0
      rw [hq, MvPolynomial.coeff_sum] at h
      simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero,
        Finsupp.zero_apply] at h
      have hb := (linearIndependent_iff'.mp b.linearIndependent) s (fun j => AddMonoidAlgebra.coeff (p j) m)
      apply hb
      rw [← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, mul_comm]
    have hpi : p i = 0 := MvPolynomial.ext _ _ fun m => hcoef m i hi
    apply Subtype.ext
    rw [← hp i, hpi, map_zero]
    rfl
  have hK : LinearIndependent A (algebraMap L' Ω ∘ b) :=
    (LinearIndependent.iff_fractionRing (Algebra.adjoin L₀ (Set.range t)) A).mp hR
  have hdisj : A.LinearDisjoint L' := LinearDisjoint.of_basis_right' b hK

  have hlow : A.restrictScalars F = L₀ ⊔ adjoin F (Set.range t) := by
    rw [hA, restrictScalars_adjoin_eq_sup]
  have hle' : A ≤ (adjoin L' (A : Set Ω)).restrictScalars L₀ := subset_adjoin L' (A : Set Ω)
  have hup : ((adjoin L' (A : Set Ω)).restrictScalars L₀).restrictScalars F =
      L ⊔ adjoin F (Set.range t) := by
    refine (restrictScalars_adjoin_eq_sup F L (A : Set Ω)).trans ?_
    have hAF : adjoin F (A : Set Ω) = L₀ ⊔ adjoin F (Set.range t) := by
      rw [← hlow]
      exact adjoin_self F (A.restrictScalars F)
    rw [hAF, ← sup_assoc, sup_eq_left.mpr hle]
  have hrel : IntermediateField.relfinrank (L₀ ⊔ adjoin F (Set.range t)) (L ⊔ adjoin F (Set.range t)) =
      finrank A (extendScalars hle') := by
    rw [← hlow, ← hup]
    exact relfinrank_eq_finrank_of_le hle'
  rw [hrel, relfinrank_eq_finrank_of_le hle]
  by_cases hfin : Module.Finite L₀ L'
  · have : Algebra.IsAlgebraic L₀ L' := Algebra.IsAlgebraic.of_finite L₀ L'
    have := hdisj.adjoin_rank_eq_rank_right_of_isAlgebraic_right
    exact congrArg Cardinal.toNat this
  · rw [finrank_of_not_finite hfin]
    have : Module.Free A (extendScalars hle') :=
      Module.Free.of_divisionRing (K := A) (V := extendScalars hle')
    apply finrank_of_not_finite
    intro hfin'
    apply hfin
    let v : _ → extendScalars hle' := fun j => ⟨algebraMap L' Ω (b j), by
      exact IntermediateField.algebraMap_mem (adjoin L' (A : Set Ω)) (b j)⟩
    have hv : LinearIndependent A v := by
      apply LinearIndependent.of_comp (extendScalars hle').val.toLinearMap
      exact hK
    have := hv.finite_of_isNoetherian
    exact Module.Finite.of_basis b
end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PFinrankAdjoinRange
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

theorem FinrankAdjoinRange.proof : FinrankAdjoinRange.Statement := by
  intro F Φ Ω _ _ _ _ _ _ _ S
  set f := IsScalarTower.toAlgHom F Φ Ω
  set Φ₁ : IntermediateField F Ω := f.fieldRange
  let i : Φ ≃ₐ[F] Φ₁ := AlgEquiv.ofInjectiveField f
  have hi : (algebraMap Φ Ω : Φ → Ω) = (algebraMap Φ₁ Ω) ∘ i := by
    funext x; rfl

  have hres : (IntermediateField.adjoin Φ S).restrictScalars F =
      (IntermediateField.adjoin Φ₁ S).restrictScalars F :=
    IntermediateField.restrictScalars_adjoin_of_algEquiv i hi S

  have hle : Φ₁ ≤ Φ₁ ⊔ IntermediateField.adjoin F S := le_sup_left
  have hext : IntermediateField.extendScalars hle = IntermediateField.adjoin Φ₁ S := by
    apply IntermediateField.restrictScalars_injective F
    rw [IntermediateField.extendScalars_restrictScalars,
      IntermediateField.restrictScalars_adjoin_eq_sup]
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle, hext]

  let j : IntermediateField.adjoin Φ S ≃+* IntermediateField.adjoin Φ₁ S :=
    (IntermediateField.equivOfEq hres).toRingEquiv
  refine Algebra.finrank_eq_of_equiv_equiv i.toRingEquiv j ?_
  ext x
  rfl

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PLocAwaySpec
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter


open Classical in
theorem LocAwaySpec.proof : LocAwaySpec.Statement := by
  intro R _ Φ _ φ S hrep
  choose f g hg hfg using hrep
  have hE0 : IsUnit (φ (∏ c ∈ S, g c)) := by
    rw [map_prod]
    exact (Finset.prod_ne_zero_iff.mpr fun c _ => hg c).isUnit
  refine ⟨∏ c ∈ S, g c, hE0, ?_, ?_⟩
  · intro c hc
    set E := ∏ d ∈ S, g d with hEdef
    have hE : IsUnit (φ E) := by
      rw [hEdef, map_prod]
      exact (Finset.prod_ne_zero_iff.mpr fun c _ => hg c).isUnit
    have hunitE : IsUnit (algebraMap R (Localization.Away E) E) :=
      IsLocalization.Away.algebraMap_isUnit E
    have hu : IsUnit (algebraMap R (Localization.Away E) (g c)) :=
      isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem g hc)) hunitE
    refine ⟨algebraMap R (Localization.Away E) (f c) * ↑hu.unit⁻¹, ?_⟩
    have h1 : (IsLocalization.Away.lift E hE : Localization.Away E →+* Φ) ↑hu.unit = φ (g c) := by
      rw [IsUnit.unit_spec, IsLocalization.Away.lift_eq]
    have h2 : (IsLocalization.Away.lift E hE : Localization.Away E →+* Φ) ↑hu.unit⁻¹ = (φ (g c))⁻¹ := by
      rw [← h1, ← map_units_inv]
    rw [map_mul, IsLocalization.Away.lift_eq, h2, ← div_eq_mul_inv]
    exact (hfg c).symm
  · intro B _ ψ hψ hker z hz
    rw [RingHom.mem_ker] at hz ⊢
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (∏ c ∈ S, g c)) z
    have hsφ := congrArg (IsLocalization.Away.lift (∏ c ∈ S, g c) hE0 : Localization.Away (∏ c ∈ S, g c) →+* Φ) hs
    simp only [map_mul, IsLocalization.Away.lift_eq, hz, zero_mul] at hsφ
    have ha : ψ a = 0 := hker (RingHom.mem_ker.mpr hsφ.symm)
    have hsψ := congrArg (IsLocalization.Away.lift (∏ c ∈ S, g c) hψ :
      Localization.Away (∏ c ∈ S, g c) →+* B) hs
    simp only [map_mul, IsLocalization.Away.lift_eq, ha] at hsψ
    obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.mp s.2
    have hsu : IsUnit (ψ (s : R)) := by
      rw [← hn, map_pow]
      exact hψ.pow n
    exact (hsu.mul_left_eq_zero).mp hsψ

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PChartPrimElt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open Polynomial

theorem ChartPrimElt.proof : ChartPrimElt.Statement := by
  intro Φ _ _ Φ' _ _ Q _ r hfin
  set L := IntermediateField.adjoin Φ (Set.range r) with hL
  obtain ⟨α, hα⟩ := Field.exists_primitive_element Φ L
  have hint : IsIntegral Φ α := IsIntegral.of_finite Φ α
  have hmemL : ∀ q, r q ∈ L := fun q => IntermediateField.subset_adjoin Φ _ ⟨q, rfl⟩
  have halg : ∀ x ∈ Set.range r, IsAlgebraic Φ x := by
    rintro _ ⟨q, rfl⟩
    exact (IntermediateField.isAlgebraic_iff (x := (⟨r q, hmemL q⟩ : L))).1
      (Algebra.IsAlgebraic.isAlgebraic _)
  have hmem : (α : Φ') ∈ Algebra.adjoin Φ (Set.range r) := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]
    exact α.2
  rw [Algebra.adjoin_range_eq_range_aeval] at hmem
  obtain ⟨τ, hτ0⟩ := hmem
  have hτ : MvPolynomial.aeval r τ = (α : Φ') := hτ0
  have hm : minpoly Φ (MvPolynomial.aeval r τ) = minpoly Φ α := by
    rw [hτ]
    exact minpoly.algHom_eq L.val Subtype.val_injective α
  have hg : ∀ q, ∃ p : Φ[X], aeval α p = (⟨r q, hmemL q⟩ : L) := by
    intro q
    have h1 : (⟨r q, hmemL q⟩ : L) ∈ IntermediateField.adjoin Φ ({α} : Set L) := by rw [hα]; trivial
    rw [← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at h1
    obtain ⟨p, hp⟩ := h1
    exact ⟨p, hp⟩
  choose g hg using hg
  have hgθ : ∀ q, aeval (MvPolynomial.aeval r τ) (g q) = r q := by
    intro q
    rw [hτ, show (α : Φ') = L.val α from rfl, Polynomial.aeval_algHom_apply, hg q]
    rfl
  have hirr : Irreducible (minpoly Φ (MvPolynomial.aeval r τ)) := by
    rw [hm]
    exact minpoly.irreducible hint
  refine ⟨τ, g, ?_⟩
  have hsep : IsCoprime (minpoly Φ (MvPolynomial.aeval r τ))
      (derivative (minpoly Φ (MvPolynomial.aeval r τ))) := hirr.separable
  obtain ⟨a, b, hab⟩ := hsep
  refine ⟨b, ?_, hgθ, ⟨-a, by linear_combination hab⟩, ?_, ?_⟩
  · rw [hm]
    exact (Field.primitive_element_iff_minpoly_natDegree_eq Φ α).1 hα
  · apply minpoly.dvd
    have hfun : (fun q => aeval (MvPolynomial.aeval r τ) (g q)) = r := funext hgθ
    rw [map_sub, aeval_X, MvPolynomial.comp_aeval_apply, hfun, sub_self]
  · intro q hq
    have hnd : ¬ minpoly Φ (MvPolynomial.aeval r τ) ∣ g q := by
      rintro ⟨c, hc⟩
      apply hq
      rw [← hgθ q, hc, map_mul, minpoly.aeval, zero_mul]
    obtain ⟨a', b', hab'⟩ := (hirr.coprime_iff_not_dvd).2 hnd
    exact ⟨b', ⟨-a', by linear_combination hab'⟩⟩

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PRelAlgClosureFinite
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial IntermediateField.algebraAdjoinAdjoin

theorem RelAlgClosureFinite.linearIndependent_adjoin {K L : Type*} [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L) {σ : Type*} {x : σ → L} (hx : AlgebraicIndependent M x)
    {ι : Type*} {m : ι → M} (hm : LinearIndependent K m) :
    LinearIndependent (Algebra.adjoin K (Set.range x)) (fun i => (m i : L)) := by
  rw [linearIndependent_iff'] at hm ⊢
  intro s g hg i hi
  have hp : ∀ j, ∃ p : MvPolynomial σ K, aeval x p = (g j : L) := fun j => by
    have h : (g j : L) ∈ (aeval x : MvPolynomial σ K →ₐ[K] L).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact (g j).2
    exact (AlgHom.mem_range _).1 h
  choose p hp using hp
  have hP : (∑ j ∈ s, C (m j) * map (algebraMap K M) (p j) : MvPolynomial σ M) = 0 := by
    apply hx.eq_zero_of_aeval_eq_zero
    rw [← hg]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, aeval_C, aeval_map_algebraMap, hp]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subalgebra.smul_def, smul_eq_mul, mul_comm]
    rfl
  have hcoeff : ∀ d, ∀ j ∈ s, AddMonoidAlgebra.coeff (p j) d = 0 := fun d => by
    apply hm s (fun j => AddMonoidAlgebra.coeff (p j) d)
    have := congrArg (AddMonoidAlgebra.coeff · d) hP
    simp only [coeff_sum, coeff_C_mul, coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, mul_comm]
  have hpi : p i = 0 := MvPolynomial.ext _ _ fun d => by simp [hcoeff d i hi, AddMonoidAlgebra.coeff_zero]
  apply Subtype.ext
  rw [← hp i, hpi, map_zero]
  rfl

theorem RelAlgClosureFinite.proof : RelAlgClosureFinite.Statement := by
  intro K L _ _ _ S hS
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis K L
  set M := algebraicClosure K L
  have hM : AlgebraicIndependent M ((↑) : t → L) := ht.1.algebraicClosure
  set E := IntermediateField.adjoin K (Set.range ((↑) : t → L))
  have halg : Algebra.IsAlgebraic E L := ht.isAlgebraic_field
  have htop : IntermediateField.adjoin E (S : Set L) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ IntermediateField.adjoin K (S : Set L) := hS ▸ IntermediateField.mem_top
    have hle : IntermediateField.adjoin K (S : Set L) ≤
        (IntermediateField.adjoin E (S : Set L)).restrictScalars K :=
      IntermediateField.adjoin_le_iff.2 fun y hy => IntermediateField.subset_adjoin E _ hy
    exact hle hz
  have hfin : FiniteDimensional E L := by
    have h := IntermediateField.finiteDimensional_adjoin (K := E) (S := (S : Set L))
      fun y _ => (halg.isAlgebraic y).isIntegral
    rw [htop] at h
    exact (IntermediateField.topEquiv (F := E) (E := L)).toLinearEquiv.finiteDimensional
  let b := Module.Basis.ofVectorSpace K M
  have hli : LinearIndependent E (fun i => ((b i : M) : L)) :=
    (LinearIndependent.iff_fractionRing (Algebra.adjoin K (Set.range ((↑) : t → L))) E).1
      (RelAlgClosureFinite.linearIndependent_adjoin M hM b.linearIndependent)
  have : Finite (Module.Basis.ofVectorSpaceIndex K M) := hli.finite
  exact Module.Finite.of_basis b

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PLinearQuotient
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial

theorem LinearQuotient.proof : LinearQuotient.Statement := by
  intro F _ σ _ S hS
  classical

  let ℓ : (σ → F) →ₗ[F] MvPolynomial σ F := Fintype.linearCombination F (fun s => (X s : MvPolynomial σ F))
  have hSrange : ∀ f ∈ S, f ∈ LinearMap.range ℓ := by
    intro f hf
    rw [Fintype.range_linearCombination, ← homogeneousSubmodule_one_eq_span_X]
    exact hS f hf
  let L : Submodule F (σ → F) := (Submodule.span F S).comap ℓ
  let b := Module.finBasis F ((σ → F) ⧸ L)
  let r := Module.finrank F ((σ → F) ⧸ L)
  let θ : (σ → F) →ₗ[F] MvPolynomial (Fin r) F :=
    Fintype.linearCombination F (fun i => (X i : MvPolynomial (Fin r) F)) ∘ₗ
      (b.equivFun.toLinearMap ∘ₗ L.mkQ)
  have hθ : ∀ v, θ v = ∑ i, b.equivFun (L.mkQ v) i • (X i : MvPolynomial (Fin r) F) := fun v => rfl
  let φ : MvPolynomial σ F →ₐ[F] MvPolynomial (Fin r) F := aeval (fun s => θ (Pi.single s 1))

  have key : ∀ c, φ (ℓ c) = θ c := by
    have : φ.toLinearMap ∘ₗ ℓ = θ := by
      refine LinearMap.pi_ext (fun s x => ?_)
      have hx : (Pi.single s x : σ → F) = x • Pi.single s (1 : F) := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, ℓ,
        Fintype.linearCombination_apply_single, map_smul, φ, aeval_X]
      rw [hx, map_smul]
    exact fun c => LinearMap.congr_fun this c

  let lift : Fin r → (σ → F) := fun i => (L.mkQ_surjective (b i)).choose
  have hlift : ∀ i, L.mkQ (lift i) = b i := fun i => (L.mkQ_surjective (b i)).choose_spec
  let ψ : MvPolynomial (Fin r) F →ₐ[F] MvPolynomial σ F := aeval (fun i => ℓ (lift i))
  have hφψ : φ.comp ψ = AlgHom.id F _ := by
    refine MvPolynomial.algHom_ext (fun i => ?_)
    have he : b.equivFun (b i) = Pi.single i 1 := by
      funext j
      rw [Module.Basis.equivFun_self, Pi.single_apply]
      by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]
    simp only [AlgHom.comp_apply, ψ, aeval_X, key, AlgHom.id_apply]
    rw [show θ (lift i) = Fintype.linearCombination F (fun i => (X i : MvPolynomial (Fin r) F))
      (b.equivFun (L.mkQ (lift i))) from rfl, hlift, he, Fintype.linearCombination_apply_single, one_smul]
  have hψθ : ∀ v, ψ (θ v) = ℓ (∑ i, b.equivFun (L.mkQ v) i • lift i) := by
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hθ, map_sum, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, map_smul, aeval_X]
  have hspan : Submodule.span F S ≤ (Ideal.span S).restrictScalars F :=
    Submodule.span_le.mpr (fun f hf => Ideal.subset_span hf)
  refine ⟨r, φ, fun p => ⟨ψ p, by simpa using AlgHom.congr_fun hφψ p⟩, ?_, fun s => ?_⟩
  · apply le_antisymm
    · have hmk : (Ideal.Quotient.mkₐ F (Ideal.span S)).comp (ψ.comp φ) = Ideal.Quotient.mkₐ F (Ideal.span S) := by
        refine MvPolynomial.algHom_ext (fun s => ?_)
        simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
        rw [Ideal.Quotient.eq]
        have h1 : φ (X s) = θ (Pi.single s 1) := aeval_X _ _
        rw [h1, hψθ]
        have hmem : (∑ i, b.equivFun (L.mkQ (Pi.single s 1)) i • lift i) - Pi.single s 1 ∈ L := by
          rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
          have : (Submodule.Quotient.mk (∑ i, b.equivFun (L.mkQ (Pi.single s 1)) i • lift i) : (σ → F) ⧸ L) =
              ∑ i, b.equivFun (L.mkQ (Pi.single s 1)) i • b i := by
            set_option synthInstance.maxHeartbeats 100000 in
              rw [← Submodule.mkQ_apply, map_sum]
            simp only [map_smul, hlift]
          rw [this, b.sum_equivFun, Submodule.mkQ_apply, sub_self]
        have h2 := hspan hmem
        rw [map_sub] at h2
        have h3 : ℓ (Pi.single s 1) = X s := by
          simp [ℓ]
        rwa [h3] at h2
      intro f hf
      rw [RingHom.mem_ker] at hf
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have := AlgHom.congr_fun hmk f
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
      rw [← this, hf, map_zero, map_zero]
    · refine Ideal.span_le.mpr (fun f hf => ?_)
      obtain ⟨c, rfl⟩ := hSrange f hf
      have hc : c ∈ L := Submodule.subset_span hf
      show φ (ℓ c) = 0
      rw [key, hθ, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero L).mpr hc]
      simp
  · rw [← mem_homogeneousSubmodule, homogeneousSubmodule_one_eq_span_X, ← Fintype.range_linearCombination]
    refine ⟨b.equivFun (L.mkQ (Pi.single s 1)), ?_⟩
    rw [show φ (X s) = θ (Pi.single s 1) from aeval_X _ _]
    rfl

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PChartSpecCount
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open Polynomial

namespace ChartSpecCount

theorem exists_pow_mul_eq_map {R : Type*} [CommRing R] (E : R) {Q : Type*}
    (F : MvPolynomial Q (Localization.Away E)) :
    ∃ (n : ℕ) (F' : MvPolynomial Q R),
      MvPolynomial.map (algebraMap R (Localization.Away E)) F' =
        MvPolynomial.C (algebraMap R (Localization.Away E) (E ^ n)) * F := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj E a
    refine ⟨n, MvPolynomial.C b, ?_⟩
    rw [MvPolynomial.map_C, ← MvPolynomial.C_mul, map_pow, mul_comm, hb]
  | add F G hF hG =>
    obtain ⟨n, F', hF'⟩ := hF
    obtain ⟨k, G', hG'⟩ := hG
    refine ⟨n + k, MvPolynomial.C (E ^ k) * F' + MvPolynomial.C (E ^ n) * G', ?_⟩
    simp only [map_add (f := _), map_mul, MvPolynomial.map_C, hF', hG', pow_add, map_pow]
    ring
  | mul_X F i hF =>
    obtain ⟨n, F', hF'⟩ := hF
    exact ⟨n, F' * MvPolynomial.X i, by rw [map_mul, MvPolynomial.map_X, hF', mul_assoc]⟩

theorem eval₂_mvEval₂_C {A K Q : Type*} [CommRing A] [CommRing K] (k : A →+* K) (x : K) (G : Q → A[X])
    (F : MvPolynomial Q A) :
    (MvPolynomial.eval₂ C G F).eval₂ k x = MvPolynomial.eval₂ k (fun q => (G q).eval₂ k x) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add F G' hF hG => simp [Polynomial.eval₂_add, hF, hG]
  | mul_X F i hF => simp [Polynomial.eval₂_mul, hF]

theorem mvEval₂_eval₂_C {A K Q : Type*} [CommRing A] [CommRing K] (k : A →+* K) (y : Q → K)
    (τ : MvPolynomial Q A) (p : A[X]) :
    MvPolynomial.eval₂ k y (p.eval₂ MvPolynomial.C τ) = p.eval₂ k (MvPolynomial.eval₂ k y τ) := by
  induction p using Polynomial.induction_on' with
  | add p p' hp hp' => simp [Polynomial.eval₂_add, hp, hp']
  | monomial n a => simp [Polynomial.eval₂_monomial]

theorem dvd_map_of_dvd_map {A Φ K : Type*} [CommRing A] [Field Φ] [CommRing K] (fA : A →+* Φ) (σ : A →+* K)
    (hker : RingHom.ker fA ≤ RingHom.ker σ) {mA : A[X]} (hm : mA.Monic) {p : A[X]}
    (hp : mA.map fA ∣ p.map fA) : mA.map σ ∣ p.map σ := by
  have h0 : (p %ₘ mA).map fA = 0 := by
    rw [map_modByMonic fA hm]
    exact (modByMonic_eq_zero_iff_dvd (hm.map fA)).2 hp
  have h1 : (p %ₘ mA).map σ = 0 := by
    ext n
    rw [coeff_map, coeff_zero]
    exact RingHom.mem_ker.mp (hker (RingHom.mem_ker.mpr (by rw [← coeff_map, h0, coeff_zero])))
  refine ⟨(p /ₘ mA).map σ, ?_⟩
  conv_lhs => rw [← modByMonic_add_div p mA]
  rw [Polynomial.map_add (f := _), Polynomial.map_mul, h1, zero_add]

end ChartSpecCount


open ChartSpecCount in
theorem ChartSpecCount.proof (hPE : ChartPrimElt.Statement) (hLA : LocAwaySpec.Statement) :
    ChartSpecCount.Statement := by
  classical
  intro R _ Φ _ _ Φ' _ _ φ Q _ r hfrac hfin
  obtain ⟨τ, g, u, hdeg, hg, hu, -, hh⟩ := hPE Φ Φ' Q r hfin
  set θ : Φ' := MvPolynomial.aeval r τ with hθ
  have hint : IsIntegral Φ θ := by
    by_contra hni
    have h0 : minpoly Φ θ = 0 := minpoly.eq_zero hni
    rw [h0, natDegree_zero] at hdeg
    exact (Module.finrank_pos (R := Φ) (M := IntermediateField.adjoin Φ (Set.range r))).ne hdeg
  set m : Φ[X] := minpoly Φ θ with hm
  let hq : Q → Φ[X] := fun q => if hq : r q ≠ 0 then (hh q hq).choose else 0
  have hhq : ∀ q, r q ≠ 0 → m ∣ hq q * g q - 1 := by
    intro q hq0
    simp only [hq, dif_pos hq0]
    exact (hh q hq0).choose_spec
  let S : Finset Φ := m.coeffs ∪ u.coeffs ∪ τ.coeffs ∪ Finset.univ.biUnion (fun q => (g q).coeffs ∪ (hq q).coeffs)
  obtain ⟨E, hE, hS, hker⟩ := hLA R Φ φ S hfrac
  set φA : Localization.Away E →+* Φ := IsLocalization.Away.lift E hE with hφA
  have hφAR : φA.comp (algebraMap R (Localization.Away E)) = φ := by
    ext x
    exact IsLocalization.Away.lift_eq E hE x
  have hlift : ∀ p : Φ[X], p.coeffs ⊆ S → p ∈ lifts φA := by
    intro p hp
    rw [lifts_iff_coeff_lifts]
    intro n
    by_cases hn : p.coeff n = 0
    · exact ⟨0, by rw [hn, map_zero]⟩
    · exact hS _ (hp (coeff_mem_coeffs hn))
  obtain ⟨mA, hmA, hmAdeg, hmAmon⟩ := lifts_and_natDegree_eq_and_monic
    (hlift m (fun c hc => by
      simp only [S, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact Or.inl (Or.inl (Or.inl hc)))) (minpoly.monic hint)
  obtain ⟨uA, huA⟩ := (mem_lifts u).1 (hlift u (fun c hc => by
      simp only [S, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact Or.inl (Or.inl (Or.inr hc))))
  have hgl : ∀ q, ∃ gq : (Localization.Away E)[X], gq.map φA = g q := fun q => (mem_lifts _).1
    (hlift (g q) (fun c hc => by
      simp only [S, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact Or.inr ⟨q, Or.inl hc⟩))
  choose gA hgA using hgl
  have hhl : ∀ q, ∃ hq' : (Localization.Away E)[X], hq'.map φA = hq q := fun q => (mem_lifts _).1
    (hlift (hq q) (fun c hc => by
      simp only [S, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact Or.inr ⟨q, Or.inr hc⟩))
  choose hA hhA using hhl
  obtain ⟨τA, hτA⟩ := MvPolynomial.mem_range_map_iff_coeffs_subset.2 (fun c hc => hS c (by
      simp only [S, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact Or.inl (Or.inr (Finset.mem_coe.1 hc))) : (τ.coeffs : Set Φ) ⊆ Set.range φA)
  set f : Localization.Away E →+* Φ' := (algebraMap Φ Φ').comp φA with hf
  have hfφ : f.comp (algebraMap R (Localization.Away E)) = (algebraMap Φ Φ').comp φ := by
    rw [hf, RingHom.comp_assoc, hφAR]

  have hevθ : ∀ p : (Localization.Away E)[X], p.eval₂ f θ = aeval θ (p.map φA) := by
    intro p
    rw [aeval_def, eval₂_map]
  have hτθ : MvPolynomial.eval₂ f r τA = θ := by
    rw [hθ, hf, ← MvPolynomial.eval₂_map, hτA]
    rfl
  have hθm : mA.eval₂ f θ = 0 := by rw [hevθ, hmA, hm, minpoly.aeval]
  have hθg : ∀ q, (gA q).eval₂ f θ = r q := fun q => by rw [hevθ, hgA, hg q]
  have hθτ : (MvPolynomial.eval₂ C gA τA - X).eval₂ f θ = 0 := by
    rw [Polynomial.eval₂_sub, eval₂_mvEval₂_C, Polynomial.eval₂_X]
    simp only [hθg]
    rw [hτθ, sub_self]
  have hθu : (uA * derivative mA - 1).eval₂ f θ = 0 := by
    obtain ⟨c, hc⟩ := hu
    rw [hevθ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one, ← derivative_map, huA, hmA, hc,
      map_mul, hm, minpoly.aeval, zero_mul]
  have hθh : ∀ q, r q ≠ 0 → (hA q * gA q - 1).eval₂ f θ = 0 := by
    intro q hq0
    obtain ⟨c, hc⟩ := hhq q hq0
    rw [hevθ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one, hhA, hgA, hc, map_mul, hm,
      minpoly.aeval, zero_mul]
  refine ⟨E, fun h => hE.ne_zero h, ?_⟩
  intro ψ hkerψ hψ0
  have hψu : IsUnit (ψ E) := hψ0.isUnit
  have hσ := hker ℂ ψ hψu hkerψ
  have hσψ : (IsLocalization.Away.lift E hψu : Localization.Away E →+* ℂ).comp
      (algebraMap R (Localization.Away E)) = ψ := by
    ext x
    simp only [RingHom.comp_apply, IsLocalization.Away.lift_eq]
  generalize (IsLocalization.Away.lift E hψu : Localization.Away E →+* ℂ) = σ at hσ hσψ

  have hD : ∀ p : (Localization.Away E)[X], p.eval₂ f θ = 0 → mA.map σ ∣ p.map σ := by
    intro p hp
    refine dvd_map_of_dvd_map φA σ hσ hmAmon ?_
    rw [hmA, hm]
    exact minpoly.dvd Φ θ (by rw [← hevθ]; exact hp)
  have hDr : ∀ p : (Localization.Away E)[X], p.eval₂ f θ = 0 → ∀ t : ℂ, mA.eval₂ σ t = 0 →
      p.eval₂ σ t = 0 := by
    intro p hp t ht
    obtain ⟨c, hc⟩ := hD p hp
    have := congrArg (eval t) hc
    rw [eval_mul, eval_map, eval_map, ht, zero_mul] at this
    exact this

  have hZA : ∀ y : Q → ℂ, (∀ F : MvPolynomial Q R, MvPolynomial.eval₂ ((algebraMap Φ Φ').comp φ) r F = 0 →
      MvPolynomial.eval₂ ψ y F = 0) →
      ∀ F : MvPolynomial Q (Localization.Away E), MvPolynomial.eval₂ f r F = 0 → MvPolynomial.eval₂ σ y F = 0 := by
    intro y hy F hF
    obtain ⟨n, F', hF'⟩ := exists_pow_mul_eq_map E F
    have h1 : MvPolynomial.eval₂ ((algebraMap Φ Φ').comp φ) r F' = 0 := by
      rw [← hfφ, ← MvPolynomial.eval₂_map, hF', MvPolynomial.eval₂_mul, hF, mul_zero]
    have h2 := hy F' h1
    rw [← hσψ, ← MvPolynomial.eval₂_map, hF', MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C] at h2
    have hEn : σ (algebraMap R (Localization.Away E) (E ^ n)) ≠ 0 := by
      rw [← RingHom.comp_apply, hσψ, map_pow]
      exact pow_ne_zero _ hψ0
    exact (mul_eq_zero.1 h2).resolve_left hEn
  let G : ℂ → Q → ℂ := fun t q => (gA q).eval₂ σ t
  let T : Set ℂ := {t | mA.eval₂ σ t = 0}

  have hb : ∀ t ∈ T, ∀ F : MvPolynomial Q R, MvPolynomial.eval₂ ((algebraMap Φ Φ').comp φ) r F = 0 →
      MvPolynomial.eval₂ ψ (G t) F = 0 := by
    intro t ht F hF
    have hp : (MvPolynomial.eval₂ C gA (MvPolynomial.map (algebraMap R (Localization.Away E)) F)).eval₂ f θ = 0 := by
      rw [eval₂_mvEval₂_C]
      simp only [hθg]
      rw [MvPolynomial.eval₂_map, hfφ]
      exact hF
    have := hDr _ hp t ht
    rw [eval₂_mvEval₂_C, MvPolynomial.eval₂_map, hσψ] at this
    exact this

  have ha : ∀ y : Q → ℂ, (∀ F : MvPolynomial Q R, MvPolynomial.eval₂ ((algebraMap Φ Φ').comp φ) r F = 0 →
      MvPolynomial.eval₂ ψ y F = 0) → MvPolynomial.eval₂ σ y τA ∈ T ∧ G (MvPolynomial.eval₂ σ y τA) = y := by
    intro y hy
    have hyA := hZA y hy
    refine ⟨?_, ?_⟩
    · have := hyA (mA.eval₂ MvPolynomial.C τA) (by rw [mvEval₂_eval₂_C, hτθ, hθm])
      rw [mvEval₂_eval₂_C] at this
      exact this
    · funext q
      have := hyA (MvPolynomial.X q - (gA q).eval₂ MvPolynomial.C τA)
        (by rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_X, mvEval₂_eval₂_C, hτθ, hθg, sub_self])
      rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_X, mvEval₂_eval₂_C, sub_eq_zero] at this
      exact this.symm

  have hc : ∀ t ∈ T, MvPolynomial.eval₂ σ (G t) τA = t := by
    intro t ht
    have := hDr _ hθτ t ht
    rw [Polynomial.eval₂_sub, eval₂_mvEval₂_C, Polynomial.eval₂_X, sub_eq_zero] at this
    exact this
  have hZ : {y : Q → ℂ | ∀ F : MvPolynomial Q R, MvPolynomial.eval₂ ((algebraMap Φ Φ').comp φ) r F = 0 →
      MvPolynomial.eval₂ ψ y F = 0} = G '' T := by
    ext y
    constructor
    · intro hy
      exact ⟨_, (ha y hy).1, (ha y hy).2⟩
    · rintro ⟨t, ht, rfl⟩
      exact hb t ht
  have hinj : Set.InjOn G T := by
    intro t₁ h₁ t₂ h₂ h
    rw [← hc t₁ h₁, ← hc t₂ h₂, h]
  have hmw0 : mA.map σ ≠ 0 := (hmAmon.map σ).ne_zero
  have hT : T = ↑(mA.map σ).roots.toFinset := by
    ext t
    simp [T, mem_roots hmw0, eval_map]
  have hsep : (mA.map σ).Separable := by
    obtain ⟨c, hc'⟩ := hD _ hθu
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one, ← derivative_map] at hc'
    exact ⟨-c, uA.map σ, by linear_combination hc'⟩
  have hcard : T.ncard = Module.finrank Φ (IntermediateField.adjoin Φ (Set.range r)) := by
    rw [hT, Set.ncard_coe_finset, Multiset.toFinset_card_of_nodup (nodup_roots hsep),
      IsAlgClosed.card_roots_eq_natDegree, hmAmon.natDegree_map, hmAdeg, ← hdeg]
  refine ⟨?_, ?_, ?_⟩
  · rw [hZ, hT]
    exact (Finset.finite_toSet _).image G
  · rw [hZ, hinj.ncard_image, hcard]
  · intro y hy q hq0
    obtain ⟨hyT, hyG⟩ := ha y hy
    have := hDr _ (hθh q hq0) _ hyT
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_one, sub_eq_zero] at this
    intro h0
    rw [← hyG] at h0
    simp only [G] at h0
    rw [h0, mul_zero] at this
    exact zero_ne_one this

end GroundTheory.Heights₂.Heights.Inter
end
end
