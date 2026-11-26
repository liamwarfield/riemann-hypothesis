module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix

namespace GlobalTheory.AdSplit

theorem exists_prod_equiv (F E A B : Type) [CommRing F] [CommRing E] [Algebra F E]
    [CommRing A] [Algebra F A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [Algebra F B] [TopologicalSpace B] [IsTopologicalRing B] :
    letI : TopologicalSpace ((A × B) ⊗[F] E) := moduleTopology (A × B) ((A × B) ⊗[F] E)
    letI : TopologicalSpace (B ⊗[F] E) := moduleTopology B (B ⊗[F] E)
    letI : TopologicalSpace (A ⊗[F] E) := moduleTopology A (A ⊗[F] E)
    ∃ e : ((A × B) ⊗[F] E) ≃+* (A ⊗[F] E) × (B ⊗[F] E),
      (∀ z, (e z).1 = Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z ∧
        (e z).2 = Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) ∧
      Continuous e ∧ Continuous e.symm := by
  letI : TopologicalSpace ((A × B) ⊗[F] E) := moduleTopology (A × B) ((A × B) ⊗[F] E)
  letI : TopologicalSpace (B ⊗[F] E) := moduleTopology B (B ⊗[F] E)
  letI : TopologicalSpace (A ⊗[F] E) := moduleTopology A (A ⊗[F] E)
  haveI : IsModuleTopology (A × B) ((A × B) ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology B (B ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology A (A ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd ((A × B) ⊗[F] E) := IsModuleTopology.toContinuousAdd (A × B) _
  haveI : ContinuousAdd (A ⊗[F] E) := IsModuleTopology.toContinuousAdd A _
  haveI : ContinuousAdd (B ⊗[F] E) := IsModuleTopology.toContinuousAdd B _
  let p := Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E)
  let q := Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E)
  let l := TensorProduct.prodLeft F F A B E
  have hl : ∀ z, l z = (p z, q z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [Prod.ext_iff]
    | tmul a x => obtain ⟨a, b⟩ := a; simp [l, p, q]
    | add x y hx hy => simp [hx, hy]
  let e : ((A × B) ⊗[F] E) ≃+* (A ⊗[F] E) × (B ⊗[F] E) :=
    { l.toAddEquiv with
      map_mul' := fun x y => by
        change l (x * y) = l x * l y
        simp [hl] }
  have he : ∀ z, e z = (p z, q z) := hl
  let i : A ⊗[F] E →ₗ[F] (A × B) ⊗[F] E := LinearMap.rTensor E (LinearMap.inl F A B)
  let j : B ⊗[F] E →ₗ[F] (A × B) ⊗[F] E := LinearMap.rTensor E (LinearMap.inr F A B)
  have hp : Continuous p := by
    let φ : (A × B) ⊗[F] E →ₛₗ[RingHom.fst A B] A ⊗[F] E :=
      { toFun := p
        map_add' := map_add p
        map_smul' := fun r z => by
          induction z using TensorProduct.induction_on with
          | zero => simp
          | tmul a x => simp [p, TensorProduct.smul_tmul']
          | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy] }
    exact IsModuleTopology.continuous_of_linearMapₛₗ continuous_fst φ
  have hq : Continuous q := by
    let φ : (A × B) ⊗[F] E →ₛₗ[RingHom.snd A B] B ⊗[F] E :=
      { toFun := q
        map_add' := map_add q
        map_smul' := fun r z => by
          induction z using TensorProduct.induction_on with
          | zero => simp
          | tmul a x => simp [q, TensorProduct.smul_tmul']
          | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy] }
    exact IsModuleTopology.continuous_of_linearMapₛₗ continuous_snd φ
  have hi : Continuous i := by
    let φ : A ⊗[F] E →ₑ+[MonoidHom.inl A B] (A × B) ⊗[F] E :=
      { toFun := i
        map_zero' := map_zero i
        map_add' := map_add i
        map_smul' := fun r z => by
          induction z using TensorProduct.induction_on with
          | zero => simp
          | tmul a x => simp [i, TensorProduct.smul_tmul']
          | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy] }
    exact IsModuleTopology.continuous_of_distribMulActionHomₑ
      (continuous_id.prodMk continuous_const) φ
  have hj : Continuous j := by
    let φ : B ⊗[F] E →ₑ+[MonoidHom.inr A B] (A × B) ⊗[F] E :=
      { toFun := j
        map_zero' := map_zero j
        map_add' := map_add j
        map_smul' := fun r z => by
          induction z using TensorProduct.induction_on with
          | zero => simp
          | tmul a x => simp [j, TensorProduct.smul_tmul']
          | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy] }
    exact IsModuleTopology.continuous_of_distribMulActionHomₑ
      (continuous_const.prodMk continuous_id) φ
  have hpi : ∀ x, p (i x) = x ∧ q (i x) = 0 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [i, p, q]
    | add x y hx hy => simp [hx.1, hx.2, hy.1, hy.2]
  have hpj : ∀ x, p (j x) = 0 ∧ q (j x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [j, p, q]
    | add x y hx hy => simp [hx.1, hx.2, hy.1, hy.2]
  refine ⟨e, fun z => by rw [he]; exact ⟨rfl, rfl⟩, ?_, ?_⟩
  · have : (e : _ → _) = fun z => (p z, q z) := funext he
    rw [this]
    exact hp.prodMk hq
  · have : (e.symm : _ → _) = fun w => i w.1 + j w.2 := by
      funext w
      rw [RingEquiv.symm_apply_eq, he]
      simp [(hpi _).1, (hpi _).2, (hpj _).1, (hpj _).2]
    rw [this]
    exact (hi.comp continuous_fst).add (hj.comp continuous_snd)

theorem exists_adele_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] , letI : TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E); letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E); letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) := moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E); ∃ e : (AdeleRing (𝓞 F) F ⊗[F] E) ≃+* (InfiniteAdeleRing F ⊗[F] E) × (FiniteAdeleRing (𝓞 F) F ⊗[F] E), (∀ z, (e z).1 = Algebra.TensorProduct.map (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (AlgHom.id F E) z ∧ (e z).2 = Algebra.TensorProduct.map (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (AlgHom.id F E) z) ∧ Continuous e ∧ Continuous e.symm := by
  intro F E _ _ _ _ _
  exact exists_prod_equiv F E (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

end GlobalTheory.AdSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat

theorem one_ne_zero_fracIdeal (F : Type) [Field F] [NumberField F] :
    (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := one_ne_zero

theorem mem_adelicIdeal_one_iff_integral (F : Type) [Field F] [NumberField F]
    (a : FiniteAdeleRing (𝓞 F) F) :
    a ∈ GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 F)⁰ F) ↔
      ∀ v, a v ∈ v.adicCompletionIntegers F := by
  constructor
  · intro h v
    have hv := h v
    unfold GlobalTheory.Idele.localIdeal at hv
    revert hv
    generalize a v = y
    intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hk
      exact HeightOneSpectrum.coe_algebraMap_mem (R := 𝓞 F) (K := F) (v := v) r
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx =>
      rw [show c • x = (c : v.adicCompletion F) * x from rfl]
      exact mul_mem c.2 hx
  · intro h v
    unfold GlobalTheory.Idele.localIdeal
    rw [← mul_one (a v), show a v * 1 = (⟨a v, h v⟩ : v.adicCompletionIntegers F) •
      (1 : v.adicCompletion F) from rfl]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨1, (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩, map_one _⟩)

private theorem exists_valuation_sub_lt_of_injective (F : Type) [Field F] [NumberField F]
    (T : Finset (HeightOneSpectrum (𝓞 F))) (c : HeightOneSpectrum (𝓞 F) → F) :
    ∃ w : F, (∀ v ∈ T, v.valuation F (w - c v) ≤ 1) ∧ ∀ v ∉ T, v.valuation F w ≤ 1 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (𝓞 F)⁰ T c
  set d : 𝓞 F := (b : 𝓞 F) with hd_def
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hdK : algebraMap (𝓞 F) F d ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
  have hex : ∀ v : HeightOneSpectrum (𝓞 F), ∃ r : 𝓞 F,
      algebraMap (𝓞 F) F r = algebraMap (𝓞 F) F d * (if v ∈ T then c v else 0) := by
    intro v
    by_cases hv : v ∈ T
    · obtain ⟨r, hr⟩ := RingHom.mem_rangeS.1 (hb v hv)
      refine ⟨r, ?_⟩
      rw [if_pos hv, hr, Algebra.smul_def]
    · exact ⟨0, by simp [hv]⟩
  choose g hg using hex
  have hfin : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ Ideal.span {d}}.Finite :=
    Ideal.finite_factors (by
      simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot] using hd0)
  set S : Finset (HeightOneSpectrum (𝓞 F)) := T ∪ hfin.toFinset with hS
  obtain ⟨r, hr⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S)
    (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    (fun v : HeightOneSpectrum (𝓞 F) =>
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {d} : Ideal (𝓞 F))).factors)
    (fun v _ => v.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h)) (fun i => g i)
  have key : ∀ v ∈ S, v.valuation F (algebraMap (𝓞 F) F r / algebraMap (𝓞 F) F d -
      (if v ∈ T then c v else 0)) ≤ 1 := by
    intro v hv
    have h1 : algebraMap (𝓞 F) F r / algebraMap (𝓞 F) F d - (if v ∈ T then c v else 0)
        = algebraMap (𝓞 F) F (r - g v) / algebraMap (𝓞 F) F d := by
      rw [map_sub, hg v, sub_div, mul_div_cancel_left₀ _ hdK]
    rw [h1, map_div₀, div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff (v.valuation F)).2 hdK)),
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      v.intValuation_if_neg hd0]
    exact (v.intValuation_le_pow_iff_mem _ _).2 (hr v hv)
  refine ⟨algebraMap (𝓞 F) F r / algebraMap (𝓞 F) F d, fun v hv => ?_, fun v hv => ?_⟩
  · have h := key v (Finset.mem_union_left _ hv)
    rwa [if_pos hv] at h
  · by_cases hvS : v ∈ S
    · have h := key v hvS
      rwa [if_neg hv, sub_zero] at h
    · have hnd : ¬ v.asIdeal ∣ Ideal.span {d} := fun h =>
        hvS (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))
      have hd1 : v.valuation F (algebraMap (𝓞 F) F d) = 1 := by
        rw [HeightOneSpectrum.valuation_of_algebraMap]
        exact le_antisymm (v.intValuation_le_one d)
          (not_lt.1 (fun h => hnd ((v.intValuation_lt_one_iff_dvd d).1 h)))
      rw [map_div₀, hd1, div_one, HeightOneSpectrum.valuation_of_algebraMap]
      exact v.intValuation_le_one r

private theorem exists_sub_mem_adicCompletionIntegers' (F : Type) [Field F] [NumberField F]
    (z : FiniteAdeleRing (𝓞 F) F) :
    ∃ w : F, ∀ v, z v - algebraMap F (FiniteAdeleRing (𝓞 F) F) w v ∈
      v.adicCompletionIntegers F := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ z v ∈ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 z.2
  have hc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ c : F,
      z v - (c : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    intro v
    have hdense : DenseRange (fun c : F => (c : v.adicCompletion F)) :=
      HeightOneSpectrum.denseRange_algebraMap (K := F) (v := v)
    have hopen : IsOpen {t : v.adicCompletion F | z v - t ∈ v.adicCompletionIntegers F} :=
      (Valued.isOpen_valuationSubring _).preimage (continuous_const.sub continuous_id)
    have hne : z v ∈ {t : v.adicCompletion F | z v - t ∈ v.adicCompletionIntegers F} := by
      show z v - z v ∈ v.adicCompletionIntegers F
      rw [sub_self]
      exact zero_mem _
    exact hdense.exists_mem_open hopen ⟨z v, hne⟩
  choose c hc using hc
  obtain ⟨w, hw1, hw2⟩ := exists_valuation_sub_lt_of_injective F hfin.toFinset c
  refine ⟨w, fun v => ?_⟩
  rw [FiniteAdeleRing.algebraMap_apply]
  by_cases hv : v ∈ hfin.toFinset
  · have h1 : ((c v : F) : v.adicCompletion F) =
        ((c v - w : F) : v.adicCompletion F) + (w : v.adicCompletion F) := by
      rw [← HeightOneSpectrum.adicCompletion.coe_add, sub_add_cancel]
    have h2 : z v - (w : v.adicCompletion F) =
        (z v - (c v : v.adicCompletion F)) + ((c v - w : F) : v.adicCompletion F) := by
      rw [h1]; ring
    rw [h2]
    refine add_mem (hc v) ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Valuation.map_sub_swap]
    exact hw1 v hv
  · have hz : z v ∈ v.adicCompletionIntegers F := by
      by_contra h
      exact hv (hfin.mem_toFinset.2 h)
    refine sub_mem hz ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hw2 v hv

theorem exists_eq_algebraMap_add_nsmul (F : Type) [Field F] [NumberField F] (N : ℕ) (hN : 0 < N)
    (y : FiniteAdeleRing (𝓞 F) F) :
    ∃ (x : F) (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
      y = algebraMap F _ x + N • a := by
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨w, hw⟩ := exists_sub_mem_adicCompletionIntegers' F
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F)⁻¹ * y)
  refine ⟨N * w, algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F)⁻¹ * y -
    algebraMap F (FiniteAdeleRing (𝓞 F) F) w, fun v => hw v, ?_⟩
  have hA : (N : FiniteAdeleRing (𝓞 F) F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul,
      mul_inv_cancel₀ hN', map_one]
  rw [nsmul_eq_mul, map_mul, map_natCast]
  linear_combination (-y) * hA

theorem strong_approximation_mod_nat : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), 0 < N → (∀ y : FiniteAdeleRing (𝓞 F) F, ∃ (x : F) (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = algebraMap F _ x + N • a) ∧ ∀ y : FiniteAdeleRing (𝓞 F) F, (∀ v, y v ∈ v.adicCompletionIntegers F) → ∃ (x : 𝓞 F) (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = algebraMap F _ (x : F) + N • a := by
  intro F _ _ N hN
  refine ⟨exists_eq_algebraMap_add_nsmul F N hN, fun y hy => ?_⟩
  obtain ⟨x, a, ha, rfl⟩ := exists_eq_algebraMap_add_nsmul F N hN y
  have hx : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F x ≤ 1 := by
    intro v
    have hNa : (N • a) v ∈ v.adicCompletionIntegers F := by
      rw [show (N • a) v = N • a v from rfl]
      exact nsmul_mem (ha v) N
    have e : (algebraMap F (FiniteAdeleRing (𝓞 F) F) x + N • a) v =
        algebraMap F (FiniteAdeleRing (𝓞 F) F) x v + (N • a) v := rfl
    have h := sub_mem (hy v) hNa
    rw [e, add_sub_cancel_right, FiniteAdeleRing.algebraMap_apply,
      HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
    exact h
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) x hx
  subst hr
  exact ⟨r, a, ha, rfl⟩

end GlobalTheory.AdLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNatStatement
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdele_strong_approximation_mod_nat : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), 0 < N → (∀ y : FiniteAdeleRing (𝓞 F) F, ∃ (x : F) (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = algebraMap F _ x + N • a) ∧ ∀ y : FiniteAdeleRing (𝓞 F) F, (∀ v, y v ∈ v.adicCompletionIntegers F) → ∃ (x : 𝓞 F) (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = algebraMap F _ (x : F) + N • a := by
  first | exact @GlobalTheory.AdLat.strong_approximation_mod_nat | exact GlobalTheory.AdLat.strong_approximation_mod_nat | (intros; apply GlobalTheory.AdLat.strong_approximation_mod_nat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
open IsLocalRing NumberField IsDedekindDomain

namespace GlobalTheory

theorem _root_.GlobalTheory.isDiscreteValuationRing_and_finite_residueField_valuationSubringAtPrime
    {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] (v : IsDedekindDomain.HeightOneSpectrum R)
    (hfin : Finite (R ⧸ v.asIdeal)) :
      IsDiscreteValuationRing ↥(IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v) ∧
        Finite (IsLocalRing.ResidueField
          ↥(IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v)) := by
  let S := Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsLocalization.AtPrime S v.asIdeal := Localization.subalgebra.isLocalization_ofField K _ _
  have hD : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot S
  haveI : IsLocalRing S := inferInstance
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have hS : Finite (ResidueField S) :=
    Finite.of_equiv _ (IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal S).toEquiv
  exact ⟨hD, hS⟩

private theorem eq_of_le_of_mem_nonunits_of_dvr {K : Type*} [Field K]
    (A W : ValuationSubring K) (h : A ≤ W) [IsDiscreteValuationRing A]
    (a : A) (ha0 : a ≠ 0) (haW : (a : K) ∈ W.nonunits) : A = W := by
  have hmem : ∀ (B : ValuationSubring K) (hB : A ≤ B) (x : A),
      x ∈ A.idealOfLE B hB ↔ (x : K) ∈ B.nonunits := by
    intro B hB x
    rw [ValuationSubring.mem_nonunits_iff]
    unfold ValuationSubring.idealOfLE
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
    rfl
  have hmax : ∀ (B : ValuationSubring K) (hB : A ≤ B), (a : K) ∈ B.nonunits →
      A.idealOfLE B hB = maximalIdeal A := by
    intro B hB haB
    have hne : A.idealOfLE B hB ≠ ⊥ := by
      intro hbot
      have : a ∈ A.idealOfLE B hB := (hmem B hB a).2 haB
      rw [hbot, Ideal.mem_bot] at this
      exact ha0 this
    have := (inferInstance : (A.idealOfLE B hB).IsPrime).isMaximal hne
    exact IsLocalRing.eq_maximalIdeal this
  have haA : (a : K) ∈ A.nonunits := (ValuationSubring.nonunits_le_nonunits.2 h) haW
  have hcongr : ∀ (P Q : Ideal A) [P.IsPrime] [Q.IsPrime], P = Q → A.ofPrime P = A.ofPrime Q := by
    rintro P Q _ _ rfl; rfl
  calc A = A.ofPrime (A.idealOfLE A le_rfl) := (A.ofPrime_idealOfLE A le_rfl).symm
    _ = A.ofPrime (A.idealOfLE W h) := hcongr _ _ ((hmax A le_rfl haA).trans (hmax W h haW).symm)
    _ = W := A.ofPrime_idealOfLE W h

theorem _root_.GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField {L : Type*} [Field L]
    [NumberField L] (W : ValuationSubring L) {n : ℕ} (hn : n ≠ (0 : ℕ))
    (hW : (↑n : L) ∈ W.nonunits) :
      IsDiscreteValuationRing ↥W ∧ Finite (IsLocalRing.ResidueField ↥W) := by
  have hnW := hW
  have hint : ∀ x : 𝓞 L, algebraMap (𝓞 L) L x ∈ W := by
    intro x
    have h : IsIntegral W (x : L) := (RingOfIntegers.isIntegral_coe x).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
    show (x : L) ∈ W
    rw [← hy]; exact y.2
  let f : 𝓞 L →+* W := (algebraMap (𝓞 L) L).codRestrict W hint
  have hf : ∀ x : 𝓞 L, ((f x : W) : L) = (x : L) := fun x => rfl
  let P : Ideal (𝓞 L) := (maximalIdeal W).comap f
  have hPmem : ∀ x : 𝓞 L, x ∈ P ↔ (x : L) ∈ W.nonunits := by
    intro x
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff, ValuationSubring.mem_nonunits_iff, hf]
  have hnP : (n : 𝓞 L) ∈ P := by
    rw [hPmem]; simpa using hnW
  have hPne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Ideal.mem_bot] at hnP
    exact hn (by exact_mod_cast hnP)
  let v : HeightOneSpectrum (𝓞 L) := ⟨P, Ideal.comap_isPrime f (maximalIdeal W), hPne⟩
  have hfin : Finite (𝓞 L ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ hPne
  let A := HeightOneSpectrum.valuationSubringAtPrime L v
  have hAW : A ≤ W := by
    intro x hx
    let S := Localization.subalgebra.ofField L _ v.asIdeal.primeCompl_le_nonZeroDivisors
    haveI : IsLocalization.AtPrime S v.asIdeal := Localization.subalgebra.isLocalization_ofField L _ _
    obtain ⟨⟨a, s⟩, hy⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl (⟨x, hx⟩ : S)
    have hspec := congrArg Subtype.val (IsLocalization.mk'_spec S a s)
    simp only at hy
    rw [hy] at hspec
    change x * ((s : 𝓞 L) : L) = (a : L) at hspec
    have hsu : IsUnit (f s) := by
      by_contra hns
      exact s.2 (show (s : 𝓞 L) ∈ P from (IsLocalRing.mem_maximalIdeal _).2 hns)
    obtain ⟨t, ht⟩ := hsu.exists_right_inv
    have h1 : ((s : 𝓞 L) : L) * (t : L) = 1 := by
      rw [← hf]; exact congrArg Subtype.val ht
    have hx' : x = (a : L) * (t : L) := by
      calc x = x * (((s : 𝓞 L) : L) * (t : L)) := by rw [h1, mul_one]
        _ = (a : L) * (t : L) := by rw [← mul_assoc, hspec]
    rw [hx']
    exact mul_mem (hint a) t.2
  obtain ⟨hD, hF⟩ :=
    _root_.GlobalTheory.isDiscreteValuationRing_and_finite_residueField_valuationSubringAtPrime L v hfin
  have hnA : (n : L) ∈ A := natCast_mem A n
  have heq : A = W := eq_of_le_of_mem_nonunits_of_dvr A W hAW ⟨(n : L), hnA⟩
    (by
      intro h0
      have := congrArg Subtype.val h0
      simp only [ZeroMemClass.coe_zero] at this
      exact hn (by exact_mod_cast this)) hnW
  rw [← heq]
  exact ⟨hD, hF⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealProperties
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat

section

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem adele_mul_integral {a b : FiniteAdeleRing (𝓞 F) F} {v : HeightOneSpectrum (𝓞 F)}
    (ha : a v ∈ v.adicCompletionIntegers F) (hb : b v ∈ v.adicCompletionIntegers F) :
    (a * b) v ∈ v.adicCompletionIntegers F := by
  have : (a * b) v = a v * b v := RestrictedProduct.mul_apply _ a b v
  rw [this]; exact mul_mem ha hb

theorem adele_add_integral {a b : FiniteAdeleRing (𝓞 F) F} {v : HeightOneSpectrum (𝓞 F)}
    (ha : a v ∈ v.adicCompletionIntegers F) (hb : b v ∈ v.adicCompletionIntegers F) :
    (a + b) v ∈ v.adicCompletionIntegers F := by
  have : (a + b) v = a v + b v := RestrictedProduct.add_apply _ a b v
  rw [this]; exact add_mem ha hb

theorem adele_neg_integral {a : FiniteAdeleRing (𝓞 F) F} {v : HeightOneSpectrum (𝓞 F)}
    (ha : a v ∈ v.adicCompletionIntegers F) :
    (-a) v ∈ v.adicCompletionIntegers F := by
  have : (-a) v = -a v := RestrictedProduct.neg_apply _ a v
  rw [this]; exact neg_mem ha

theorem adele_one_integral (v : HeightOneSpectrum (𝓞 F)) :
    (1 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F := by
  have : (1 : FiniteAdeleRing (𝓞 F) F) v = 1 := RestrictedProduct.one_apply _ _
  rw [this]; exact one_mem _

theorem adele_zero_integral (v : HeightOneSpectrum (𝓞 F)) :
    (0 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F := by
  have : (0 : FiniteAdeleRing (𝓞 F) F) v = 0 := RestrictedProduct.zero_apply _ _
  rw [this]; exact zero_mem _

theorem tmul_mem_adelicCompletion_of_integral {J : Set E} {a : FiniteAdeleRing (𝓞 F) F}
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) {x : E} (hx : x ∈ J) :
    a ⊗ₜ[F] x ∈ hat1 F J :=
  AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩

theorem one_tmul_mem_adelicCompletionOfElementSet {J : Set E} {x : E} (hx : x ∈ J) :
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F J :=
  tmul_mem_adelicCompletion_of_integral F (adele_one_integral F) hx

theorem mul_mem_adelicCompletionOfElementSet_of_mul_mem {I J K : Set E} (h : ∀ x ∈ I, ∀ y ∈ J, x * y ∈ K)
    {x y : RA F E} (hx : x ∈ hat1 F I) (hy : y ∈ hat1 F J) : x * y ∈ hat1 F K := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨b, hb, y, hy, rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_adelicCompletion_of_integral F (fun v => adele_mul_integral F (ha v) (hb v))
        (h x hx y hy)
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | neg y _ h1 => rw [mul_neg]; exact neg_mem h1
  | zero => rw [zero_mul]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | neg y _ h1 => rw [neg_mul]; exact neg_mem h1

theorem galoisAut_mem_adelicCompletionOfElementSet (c : E ≃ₐ[F] E) {I J : Set E} (h : ∀ x ∈ I, c x ∈ J)
    {z : RA F E} (hz : z ∈ hat1 F I) : sg (FiniteAdeleRing (𝓞 F) F) c z ∈ hat1 F J := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hx
    exact tmul_mem_adelicCompletion_of_integral F ha (h x hx)
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [map_add (f := _)]; exact add_mem h1 h2
  | neg y _ h1 => rw [map_neg]; exact neg_mem h1

theorem mem_range_iff_adele_integral (x : F) :
    x ∈ (algebraMap (𝓞 F) F).range ↔
      ∀ v, algebraMap F (FiniteAdeleRing (𝓞 F) F) x v ∈ v.adicCompletionIntegers F := by
  simp only [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  constructor
  · rintro ⟨a, rfl⟩ v
    exact v.valuation_le_one a
  · exact HeightOneSpectrum.mem_integers_of_valuation_le_one F x

theorem linearForm_integral_of_one_tmul_mem_adelicCompletion {I : Set E} (t : E →ₗ[F] F)
    (ht : ∀ y ∈ I, t y ∈ (algebraMap (𝓞 F) F).range) {x : E}
    (hx : (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F I) :
    t x ∈ (algebraMap (𝓞 F) F).range := by
  let T : RA F E →ₗ[F] FiniteAdeleRing (𝓞 F) F :=
    (TensorProduct.rid F _).toLinearMap ∘ₗ LinearMap.lTensor _ t
  have hT : ∀ a y, T (a ⊗ₜ[F] y) = algebraMap F _ (t y) * a := by
    intro a y
    simp [T, Algebra.smul_def]
  have key : ∀ z ∈ hat1 F I, ∀ v, T z v ∈ v.adicCompletionIntegers F := by
    intro z hz v
    induction hz using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, y, hy, rfl⟩ := hx
      rw [hT]
      exact adele_mul_integral F
        ((mem_range_iff_adele_integral F _).1 (ht y hy) v) (ha v)
    | zero => rw [map_zero]; exact adele_zero_integral F v
    | add y z _ _ h1 h2 => rw [map_add (f := _)]; exact adele_add_integral F h1 h2
    | neg y _ h1 => rw [map_neg]; exact adele_neg_integral F h1
  rw [mem_range_iff_adele_integral]
  have := key _ hx
  rwa [hT, mul_one] at this

variable [NumberField E]

theorem one_tmul_mem_adelicCompletion_fractionalIdeal_iff (I : FractionalIdeal (𝓞 E)⁰ E) (x : E) :
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F (I : Set E) ↔ x ∈ I := by
  refine ⟨fun hx => ?_, fun hx => one_tmul_mem_adelicCompletionOfElementSet F hx⟩
  by_cases hI : I = 0
  · subst hI
    rw [FractionalIdeal.mem_zero_iff]
    by_contra h0
    obtain ⟨t, ht⟩ := Module.Projective.exists_dual_eq_one F h0
    apply RingOfIntegers.not_isField F
    rw [← IsFractionRing.surjective_iff_isField (K := F)]
    intro c
    have := linearForm_integral_of_one_tmul_mem_adelicCompletion F (c • t) (fun y hy => by
      have hy' : y = 0 := (FractionalIdeal.mem_zero_iff _).1 hy
      rw [hy', map_zero]; exact zero_mem _) hx
    simpa [ht] using this
  · rw [← FractionalIdeal.dual_dual (𝓞 F) F I,
      FractionalIdeal.mem_dual (FractionalIdeal.dual_ne_zero _ _ hI)]
    intro y hy
    rw [FractionalIdeal.mem_dual hI] at hy
    have := linearForm_integral_of_one_tmul_mem_adelicCompletion F (Algebra.traceForm F E y) hy hx
    rwa [Algebra.traceForm_apply, mul_comm] at this

theorem mem_adelicCompletion_mul_inv_fractionalIdeal (I J : FractionalIdeal (𝓞 E)⁰ E) (z : RA F E) (hI : I ≠ 0)
    (h : ∀ x ∈ I, z * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) ∈ hat1 F (J : Set E)) :
    z ∈ hat1 F ((J * I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  have h1 : (1 : E) ∈ I * I⁻¹ := by
    rw [mul_inv_cancel₀ hI]; exact FractionalIdeal.one_mem_one _
  have key : ∀ w ∈ I * I⁻¹, z * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] w) ∈
      hat1 F ((J * I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    intro w hw
    refine FractionalIdeal.mul_induction_on hw (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · have := mul_mem_adelicCompletionOfElementSet_of_mul_mem F (K := ((J * I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E))
        (fun a ha b hb => FractionalIdeal.mul_mem_mul ha hb) (h x hx) (one_tmul_mem_adelicCompletionOfElementSet F hy)
      rwa [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one] at this
    · rw [TensorProduct.tmul_add, mul_add]; exact add_mem hx hy
  have := key 1 h1
  rwa [← Algebra.TensorProduct.one_def, mul_one] at this

end

theorem adelicCompletion_fractionalIdeal_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ I J : FractionalIdeal (𝓞 E)⁰ E, ∀ x ∈ hat1 F (I : Set E), ∀ y ∈ hat1 F (J : Set E), x * y ∈ hat1 F ((I * J : FractionalIdeal (𝓞 E)⁰ E) : Set E)) ∧ (∀ (I : FractionalIdeal (𝓞 E)⁰ E) (x : E), (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F (I : Set E) ↔ x ∈ I) ∧ (∀ (I J : FractionalIdeal (𝓞 E)⁰ E) (z : RA F E), I ≠ 0 → (∀ x ∈ I, z * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) ∈ hat1 F (J : Set E)) → z ∈ hat1 F ((J * I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E)) ∧ ∀ (c : E ≃ₐ[F] E) (I I' : FractionalIdeal (𝓞 E)⁰ E), (∀ x ∈ I, c x ∈ I') → ∀ z ∈ hat1 F (I : Set E), sg (FiniteAdeleRing (𝓞 F) F) c z ∈ hat1 F (I' : Set E) := by
  intro F E _ _ _ _ _
  exact ⟨fun I J x hx y hy => mul_mem_adelicCompletionOfElementSet_of_mul_mem F
      (fun a ha b hb => FractionalIdeal.mul_mem_mul ha hb) hx hy,
    one_tmul_mem_adelicCompletion_fractionalIdeal_iff F, mem_adelicCompletion_mul_inv_fractionalIdeal F, fun c I I' h z hz => galoisAut_mem_adelicCompletionOfElementSet F c h hz⟩

end GlobalTheory.AdLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealPropertiesStatement
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicCompletion_fractionalIdeal_properties_alt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ I J : FractionalIdeal (𝓞 E)⁰ E, ∀ x ∈ hat1 F (I : Set E), ∀ y ∈ hat1 F (J : Set E), x * y ∈ hat1 F ((I * J : FractionalIdeal (𝓞 E)⁰ E) : Set E)) ∧ (∀ (I : FractionalIdeal (𝓞 E)⁰ E) (x : E), (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F (I : Set E) ↔ x ∈ I) ∧ (∀ (I J : FractionalIdeal (𝓞 E)⁰ E) (z : RA F E), I ≠ 0 → (∀ x ∈ I, z * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) ∈ hat1 F (J : Set E)) → z ∈ hat1 F ((J * I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E)) ∧ ∀ (c : E ≃ₐ[F] E) (I I' : FractionalIdeal (𝓞 E)⁰ E), (∀ x ∈ I, c x ∈ I') → ∀ z ∈ hat1 F (I : Set E), sg (FiniteAdeleRing (𝓞 F) F) c z ∈ hat1 F (I' : Set E) := by
  first | exact @GlobalTheory.AdLat.adelicCompletion_fractionalIdeal_properties | exact GlobalTheory.AdLat.adelicCompletion_fractionalIdeal_properties | (intros; apply GlobalTheory.AdLat.adelicCompletion_fractionalIdeal_properties <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRingEquivComplexCompEq
namespace GlobalTheory.CompRat

theorem exists_ringEquiv_complex_comp_eq :
    ∀ (k : Type) [Field k] [Countable k] (φ ψ : k →+* ℂ), ∃ τ : ℂ ≃+* ℂ, ∀ x, τ (φ x) = ψ x :=
  fun _ _ _ φ ψ => GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq φ ψ

end GlobalTheory.CompRat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix

namespace GlobalTheory.InfAdeleCM

variable {F : Type} [Field F] [NumberField F]

def ext (σ : F →+* ℂ) : InfiniteAdeleRing F →+* ℂ :=
  (InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk σ)).comp
    (Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) (InfinitePlace.mk σ))

theorem ext_apply (σ : F →+* ℂ) (a : InfiniteAdeleRing F) :
    ext σ a = InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk σ) (a (InfinitePlace.mk σ)) := rfl

theorem continuous_ext (σ : F →+* ℂ) : Continuous (ext σ) :=
  (InfinitePlace.Completion.isometry_extensionEmbedding (InfinitePlace.mk σ)).continuous.comp
    (continuous_apply (InfinitePlace.mk σ))

theorem ext_algebraMap [IsTotallyReal F] (σ : F →+* ℂ) (x : F) :
    ext σ (algebraMap F (InfiniteAdeleRing F) x) = σ x := by
  have h : (InfinitePlace.mk σ).embedding = σ :=
    InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal σ)
  rw [ext_apply, InfiniteAdeleRing.algebraMap_apply]
  simp [h]

theorem ext_eq_ofReal [IsTotallyReal F] (σ : F →+* ℂ) (a : InfiniteAdeleRing F) :
    ext σ a = (InfinitePlace.Completion.extensionEmbeddingOfIsReal
      (IsTotallyReal.isReal (InfinitePlace.mk σ)) (a (InfinitePlace.mk σ)) : ℝ) := by
  rw [ext_apply, InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]

theorem conj_ext [IsTotallyReal F] (σ : F →+* ℂ) (a : InfiniteAdeleRing F) :
    starRingEnd ℂ (ext σ a) = ext σ a := by
  rw [ext_eq_ofReal, Complex.conj_ofReal]

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem exists_hom [IsTotallyReal F] (τ : E →+* ℂ) :
    ∃ θ : InfiniteAdeleRing F ⊗[F] E →+* ℂ, (∀ x, θ (1 ⊗ₜ x) = τ x) ∧
      Continuous fun a : InfiniteAdeleRing F => θ (a ⊗ₜ (1 : E)) := by
  letI : Algebra F ℂ := (τ.comp (algebraMap F E)).toAlgebra
  let f : InfiniteAdeleRing F →ₐ[F] ℂ :=
    { ext (τ.comp (algebraMap F E)) with commutes' := fun x => ext_algebraMap _ x }
  let g : E →ₐ[F] ℂ := { τ with commutes' := fun x => rfl }
  refine ⟨(Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom, ?_, ?_⟩
  · intro x
    simp [g]
  · have : (fun a : InfiniteAdeleRing F =>
        (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom (a ⊗ₜ (1 : E))) =
        ext (τ.comp (algebraMap F E)) := by
      funext a
      simp [f]
    rw [this]
    exact continuous_ext _

theorem hom_tmul [IsTotallyReal F] (τ : E →+* ℂ) (θ : InfiniteAdeleRing F ⊗[F] E →+* ℂ)
    (h1 : ∀ x, θ (1 ⊗ₜ x) = τ x) (h2 : Continuous fun a : InfiniteAdeleRing F => θ (a ⊗ₜ (1 : E)))
    (a : InfiniteAdeleRing F) (x : E) :
    θ (a ⊗ₜ x) = ext (τ.comp (algebraMap F E)) a * τ x := by
  have : (fun a : InfiniteAdeleRing F => θ (a ⊗ₜ (1 : E))) = ext (τ.comp (algebraMap F E)) := by
    refine (InfiniteAdeleRing.denseRange_algebraMap F).equalizer h2 (continuous_ext _) ?_
    funext y
    simp only [Function.comp_apply, ext_algebraMap, RingHom.comp_apply]
    rw [← h1, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  rw [← this, ← h1, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem exists_delta (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (hτ : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x)) :
    ∃ δ : E, δ ≠ 0 ∧ c δ = -δ ∧ ∀ x : E, ∃ p q : F, x = algebraMap F E p + algebraMap F E q * δ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨y, hy⟩ : ∃ y, c y ≠ y := by
    by_contra h
    push_neg at h
    exact hc (AlgEquiv.ext h)
  have hcc : c (c y) = y := τ.injective (by rw [hτ, hτ, Complex.conj_conj])
  have hδ : y - c y ≠ 0 := sub_ne_zero.2 hy.symm
  have hcδ : c (y - c y) = -(y - c y) := by rw [map_sub, hcc]; ring
  refine ⟨y - c y, hδ, hcδ, ?_⟩
  generalize y - c y = δ at hδ hcδ
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h' := congrArg c hst
    have hsm : ∀ (p : F) (x : E), c (p • x) = p • c x := fun p x => by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, c.commutes]
    rw [map_add (f := _), hsm, hsm, map_one, hcδ, map_zero, smul_neg] at h'
    have ht : t • δ = 0 := by
      have : (2 : E) * (t • δ) = 0 := by linear_combination hst - h'
      simpa using this
    have ht' : t = 0 := by simpa [hδ] using ht
    refine ⟨?_, ht'⟩
    simpa [ht'] using hst
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by simp [h2])
  intro x
  have hx : x ∈ Submodule.span F (Set.range ![(1 : E), δ]) := hsp ▸ Submodule.mem_top
  rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at hx
  obtain ⟨p, q, rfl⟩ := hx
  exact ⟨p, q, by simp [Algebra.smul_def]⟩

theorem eq_or_conj (c : E ≃ₐ[F] E) (hτ : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x))
    {δ : E} (h0 : δ ≠ 0) (hc : c δ = -δ)
    (hs : ∀ x : E, ∃ p q : F, x = algebraMap F E p + algebraMap F E q * δ) (τ τ' : E →+* ℂ)
    (h : τ.comp (algebraMap F E) = τ'.comp (algebraMap F E)) :
    τ = τ' ∨ τ = ComplexEmbedding.conjugate τ' := by
  have hp : ∀ p, τ (algebraMap F E p) = τ' (algebraMap F E p) := fun p => RingHom.congr_fun h p
  obtain ⟨p, q, hpq⟩ := hs (δ * δ)
  have h' := congrArg c hpq
  rw [map_mul, map_add (f := _), map_mul, hc, c.commutes, c.commutes] at h'
  have hsq : δ * δ = algebraMap F E p := by linear_combination (hpq + h') / 2
  have : τ δ * τ δ = τ' δ * τ' δ := by rw [← map_mul, ← map_mul, hsq, hp]
  rcases mul_self_eq_mul_self_iff.1 this with e | e
  · left
    ext x
    obtain ⟨p, q, rfl⟩ := hs x
    simp [hp, e]
  · right
    ext x
    obtain ⟨p, q, rfl⟩ := hs x
    rw [ComplexEmbedding.conjugate_coe_eq, ← hτ]
    simp [hp, e, hc]

theorem exists_decomp {δ : E} (hs : ∀ x : E, ∃ p q : F, x = algebraMap F E p + algebraMap F E q * δ)
    (z : InfiniteAdeleRing F ⊗[F] E) : ∃ a b : InfiniteAdeleRing F, z = a ⊗ₜ 1 + b ⊗ₜ δ := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a x =>
    obtain ⟨p, q, rfl⟩ := hs x
    refine ⟨p • a, q • a, ?_⟩
    rw [TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.smul_tmul, Algebra.smul_def,
      Algebra.smul_def, mul_one]
  | add x y hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    exact ⟨a + a', b + b', by rw [TensorProduct.add_tmul, TensorProduct.add_tmul]; abel⟩

theorem mk_eq_iff [IsTotallyReal F] {σ σ' : F →+* ℂ} (h : InfinitePlace.mk σ = InfinitePlace.mk σ') : σ = σ' := by
  rw [← InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal σ), h,
    InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal σ')]

theorem exists_over [IsTotallyReal F] (Ψ : Set (E →+* ℂ))
    (hΨ : ∀ τ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (w : InfinitePlace F) :
    ∃ τ ∈ Ψ, InfinitePlace.mk (τ.comp (algebraMap F E)) = w := by
  have h : InfinitePlace.mk ((ComplexEmbedding.lift E w.embedding).comp (algebraMap F E)) = w := by
    rw [ComplexEmbedding.lift_comp_algebraMap, InfinitePlace.mk_embedding]
  by_cases hm : ComplexEmbedding.lift E w.embedding ∈ Ψ
  · exact ⟨_, hm, h⟩
  · refine ⟨ComplexEmbedding.conjugate (ComplexEmbedding.lift E w.embedding), ?_, ?_⟩
    · by_contra hn
      exact hm ((hΨ _).2 hn)
    · rw [← h, ← InfinitePlace.mk_conjugate_eq]
      congr 1
      ext x
      simp

theorem bijective [IsTotallyReal F] (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (hτ : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x))
    (θ : (E →+* ℂ) → (InfiniteAdeleRing F ⊗[F] E →+* ℂ))
    (hθ : ∀ τ a x, θ τ (a ⊗ₜ x) = ext (τ.comp (algebraMap F E)) a * τ x)
    (Ψ : Set (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) :
    Function.Bijective (fun (z : InfiniteAdeleRing F ⊗[F] E) (τ : Ψ) => θ τ.1 z) := by
  obtain ⟨δ, h0, hcδ, hs⟩ := exists_delta c h2 hc hτ
  have hre : ∀ τ : E →+* ℂ, (τ δ).re = 0 := by
    intro τ
    have := congrArg Complex.re (hτ τ δ)
    rw [hcδ, map_neg, Complex.neg_re, Complex.conj_re] at this
    linarith
  have him : ∀ τ : E →+* ℂ, (τ δ).im ≠ 0 := by
    intro τ h
    exact h0 (τ.injective (by rw [map_zero]; exact Complex.ext (hre τ) h))
  let r : ∀ w : InfinitePlace F, w.Completion →+* ℝ := fun w =>
    InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)
  have hr : ∀ w, Function.Bijective (r w) := fun w =>
    InfinitePlace.Completion.bijective_extensionEmbeddingOfIsReal _
  have hval : ∀ (τ : E →+* ℂ) (a b : InfiniteAdeleRing F), θ τ (a ⊗ₜ 1 + b ⊗ₜ δ) =
      ⟨r _ (a (InfinitePlace.mk (τ.comp (algebraMap F E)))),
        r _ (b (InfinitePlace.mk (τ.comp (algebraMap F E)))) * (τ δ).im⟩ := by
    intro τ a b
    rw [map_add (f := _), hθ, hθ, ext_eq_ofReal, ext_eq_ofReal, map_one, mul_one]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, hre, mul_zero, add_zero, r]
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, zero_add, r]
  choose t ht htw using exists_over (F := F) Ψ hΨ
  constructor
  · intro z z' hz
    obtain ⟨a, b, rfl⟩ := exists_decomp hs z
    obtain ⟨a', b', rfl⟩ := exists_decomp hs z'
    have key : ∀ w, a w = a' w ∧ b w = b' w := by
      intro w
      have := congrFun hz ⟨t w, ht w⟩
      simp only [hval, Complex.mk.injEq] at this
      rw [htw w] at this
      exact ⟨(hr w).1 this.1, (hr w).1 (mul_right_cancel₀ (him _) this.2)⟩
    have ha : a = a' := funext fun w => (key w).1
    have hb : b = b' := funext fun w => (key w).2
    rw [ha, hb]
  · intro y
    choose a ha using fun w => (hr w).2 (y ⟨t w, ht w⟩).re
    choose b hb using fun w => (hr w).2 ((y ⟨t w, ht w⟩).im / (t w δ).im)
    refine ⟨(show InfiniteAdeleRing F from a) ⊗ₜ[F] (1 : E) + (show InfiniteAdeleRing F from b) ⊗ₜ[F] δ, ?_⟩
    funext τ
    obtain ⟨τ, hτΨ⟩ := τ
    have e : t (InfinitePlace.mk (τ.comp (algebraMap F E))) = τ := by
      rcases eq_or_conj c hτ h0 hcδ hs _ _ (mk_eq_iff (htw (InfinitePlace.mk (τ.comp (algebraMap F E))))) with e | e
      · exact e
      · exact absurd (e ▸ ht _) ((hΨ τ).1 hτΨ)
    have := hval τ a b
    simp only [ha, hb, e] at this
    refine this.trans ?_
    apply Complex.ext
    · rfl
    · exact div_mul_cancel₀ _ (him τ)

theorem infAdele_tensor_bijective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 → IsTotallyReal F → (∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x)) → letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) := moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E); (∀ τ : E →+* ℂ, ∃ θ : InfiniteAdeleRing F ⊗[F] E →+* ℂ, (∀ x, θ (1 ⊗ₜ x) = τ x) ∧ Continuous fun a : InfiniteAdeleRing F => θ (a ⊗ₜ (1 : E))) ∧ ∀ θ : (E →+* ℂ) → (InfiniteAdeleRing F ⊗[F] E →+* ℂ), (∀ τ, (∀ x, θ τ (1 ⊗ₜ x) = τ x) ∧ Continuous fun a : InfiniteAdeleRing F => θ τ (a ⊗ₜ (1 : E))) → (∀ τ, Continuous (θ τ)) ∧ (∀ τ z, θ τ (sg (InfiniteAdeleRing F) c z) = starRingEnd ℂ (θ τ z)) ∧ ∀ Ψ : Set (E →+* ℂ), (∀ τ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → Function.Bijective (fun (z : InfiniteAdeleRing F ⊗[F] E) (τ : Ψ) => θ τ.1 z) := by
  intro F E _ _ _ _ _ c h2 hc hF hτ
  letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) :=
    moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  haveI : IsModuleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E) := ⟨rfl⟩
  refine ⟨exists_hom, fun θ hθ => ?_⟩
  have hθ' := fun τ => hom_tmul τ (θ τ) (hθ τ).1 (hθ τ).2
  refine ⟨fun τ => ?_, fun τ z => ?_, bijective c h2 hc hτ θ hθ'⟩
  · exact IsModuleTopology.continuous_of_ringHom (R := InfiniteAdeleRing F) (θ τ) (hθ τ).2
  · induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp only [sg, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id, hθ', map_mul, conj_ext]
      rw [← hτ]
      rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.InfAdeleCM
end
end
