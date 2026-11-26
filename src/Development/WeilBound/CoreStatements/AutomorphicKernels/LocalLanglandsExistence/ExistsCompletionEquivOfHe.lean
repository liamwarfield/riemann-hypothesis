module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingsTowerCompatible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalExtensionOfFiniteIndexWeilSubgroup
public import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.WeilEquivOfLocalDegreeOne
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.LocalLanglands.HeckeKernelConditions

theorem valuation_algebraMap_le_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {F : Type} [Field F] [NumberField F]
    [Algebra F Ω] (x : 𝓞 F) : A.valuation (algebraMap F Ω (x : F)) ≤ 1 := by
  have hint : IsIntegral ℤ (algebraMap F Ω (x : F)) :=
    (RingOfIntegers.isIntegral_coe x).map (algebraMap F Ω).toIntAlgHom
  have hA : IsIntegral A (algebraMap F Ω (x : F)) := hint.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hA
  rw [← hy]
  exact A.valuation_le_one y

theorem card_le_of_pow_eq_self {R : Type} [CommRing R] [IsDomain R] [Fintype R] {q : ℕ} (hq : 1 < q)
    (H : ∀ z : R, z ^ q = z) : Fintype.card R ≤ q := by
  classical
  have hdeg : (Polynomial.X ^ q - Polynomial.X : Polynomial R).natDegree = q := by
    have h1 : (Polynomial.X : Polynomial R).degree < (Polynomial.X ^ q : Polynomial R).degree := by
      rw [Polynomial.degree_X_pow, Polynomial.degree_X]; exact_mod_cast hq
    rw [Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_sub_eq_left_of_degree_lt h1),
      Polynomial.natDegree_X_pow]
  have hp : (Polynomial.X ^ q - Polynomial.X : Polynomial R) ≠ 0 := by
    intro h0; rw [h0, Polynomial.natDegree_zero] at hdeg; omega
  have hsub : (Finset.univ : Finset R).val ⊆ (Polynomial.X ^ q - Polynomial.X : Polynomial R).roots := by
    intro z _
    rw [Polynomial.mem_roots hp, Polynomial.IsRoot.def]
    simp [H z]
  have := Polynomial.card_le_degree_of_subset_roots hsub
  rwa [hdeg, Finset.card_univ] at this

section Transport

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}
  {K F : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] [Algebra K F] [IsScalarTower K F Ω]
  {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 F)}


omit [IsAlgClosure F Ω] in
theorem normV_eq_of_localDegreeOne (h : IsPlaceOver A v) (h' : IsPlaceOver A w)
    (hloc : ∀ (σ : Weil h) (x : F), (σ : G K Ω) (algebraMap F Ω x) = algebraMap F Ω x) :
    normV w = normV v := by
  classical
  obtain ⟨f, hf⟩ := GlobalTheory.WeilRestrict.normV_eq_pow_of_isPlaceOver h h'
  obtain ⟨φ, hφ⟩ := exists_isFrob h
  have hq : 1 < normV v := one_lt_normV v
  have hφW : φ ∈ Weil h := mem_Weil_of_isFrob h hφ
  have key : ∀ x : 𝓞 F, x ^ normV v - x ∈ w.asIdeal := by
    intro x
    rw [← h' (x ^ normV v - x)]
    have h1 := hφ.2 _ (valuation_algebraMap_le_one A x)
    have h2 : φ (algebraMap F Ω (x : F)) = algebraMap F Ω (x : F) := hloc ⟨φ, hφW⟩ (x : F)
    rw [h2, Valuation.map_sub_swap] at h1
    have e : algebraMap F Ω ((x ^ normV v - x : 𝓞 F) : F) =
        algebraMap F Ω (x : F) ^ normV v - algebraMap F Ω (x : F) := by
      push_cast
      rfl
    rw [e]
    exact h1
  have : w.asIdeal.IsPrime := w.isPrime
  have : Finite (𝓞 F ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  let _ : Fintype (𝓞 F ⧸ w.asIdeal) := Fintype.ofFinite _
  have hle : normV w ≤ normV v := by
    rw [normV, Nat.card_eq_fintype_card]
    refine card_le_of_pow_eq_self hq fun z => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact key x
  have h1w : 1 < normV w := one_lt_normV w
  rw [hf] at hle h1w ⊢
  have hf1 : f ≤ 1 := by
    exact (pow_le_pow_iff_right₀ hq).mp (show normV v ^ f ≤ normV v ^ 1 by rwa [pow_one])
  have hf0 : f ≠ 0 := by rintro rfl; simp at h1w
  have : f = 1 := by omega
  rw [this, pow_one]

end Transport

section GlobalModel

end GlobalModel

end PositivityTheory.Pf1.LocalLanglands.HeckeKernelConditions

end
end

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.LocalLanglands.HeckeKernelConditions.RamifiedPlaceLift

theorem continuous_symm_of_valued_eq {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 F)}
    (ι : v.adicCompletion K ≃+* w.adicCompletion F) (hv : ∀ x, Valued.v (ι x) = Valued.v x) :
    Continuous ι.symm := by
  refine continuous_of_continuousAt_zero ι.symm.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  rw [Filter.mem_map]
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  obtain ⟨x, hx⟩ : ∃ x : v.adicCompletion K, Valued.v.restrict x = γ.1 :=
    MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective _ γ.1
  have hx0 : Valued.v x ≠ 0 := by
    intro h0
    apply γ.ne_zero
    rw [← hx]
    simpa using h0
  have hy0 : Valued.v.restrict (ι x) ≠ 0 := by
    simpa [hv] using hx0
  refine Valued.mem_nhds_zero.2 ⟨Units.mk0 _ hy0, fun y hy => hγ ?_⟩
  have h1 : Valued.v y < Valued.v (ι x) := by
    simpa using hy
  have h2 : Valued.v (ι.symm y) < Valued.v x := by
    rw [← hv (ι.symm y), ← hv x, RingEquiv.apply_symm_apply]
    exact h1
  show Valued.v.restrict (ι.symm y) < γ
  rw [← hx]
  simpa using h2

section Pair

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}
  {K F : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] [Algebra K F] [IsScalarTower K F Ω]
  {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 F)}


omit [IsAlgClosure F Ω] in
theorem inertiaDeg_eq_one (h : IsPlaceOver A v) (h' : IsPlaceOver A w)
    (hloc : ∀ (σ : Weil h) (x : F), (σ : G K Ω) (algebraMap F Ω x) = algebraMap F Ω x) :
    w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
  have : w.asIdeal.LiesOver v.asIdeal := ⟨(GlobalTheory.WeilRestrict.comap_eq_of_isPlaceOver h h').symm⟩
  have hn := normV_eq_of_localDegreeOne h h' hloc
  have hf : normV w = normV v ^ w.asIdeal.inertiaDeg (𝓞 K) := by
    simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    exact (Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal).symm
  rw [hn] at hf
  exact Nat.pow_right_injective (one_lt_normV v) (hf.symm.trans (pow_one _).symm)


omit [IsAlgClosure F Ω] in
theorem exists_completionEquiv_of_he (h : IsPlaceOver A v) (h' : IsPlaceOver A w)
    (hloc : ∀ (σ : Weil h) (x : F), (σ : G K Ω) (algebraMap F Ω x) = algebraMap F Ω x)
    (he : w.asIdeal.ramificationIdx (𝓞 K) = 1) :
    ∃ ι : v.adicCompletion K ≃+* w.adicCompletion F, Continuous ι ∧ Continuous ι.symm ∧
      (∀ x : K, ι (algebraMap K _ x) = algebraMap F _ (algebraMap K F x)) ∧
      ∀ x, Valued.v (ι x) = Valued.v x := by
  have : w.asIdeal.LiesOver v.asIdeal := ⟨(GlobalTheory.WeilRestrict.comap_eq_of_isPlaceOver h h').symm⟩
  let _ : Algebra (v.adicCompletion K) (w.adicCompletion F) := (GroundTheory.Global.adicCompletionMap v w).toAlgebra
  have : IsScalarTower K (v.adicCompletion K) (w.adicCompletion F) :=
    .of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply K F (w.adicCompletion F)]
      exact (GroundTheory.Global.adicCompletionMap_algebraMap v w x).symm
  have : ContinuousSMul (v.adicCompletion K) (w.adicCompletion F) :=
    continuousSMul_of_algebraMap _ _ (GroundTheory.Global.continuous_adicCompletionMap v w)
  have hfin : Module.finrank (v.adicCompletion K) (w.adicCompletion F) = 1 := by
    rw [GroundTheory.Global.finrank_adicCompletion v w, he, inertiaDeg_eq_one h h' hloc]
  have hbij : Function.Bijective (algebraMap (v.adicCompletion K) (w.adicCompletion F)) := by
    refine ⟨(algebraMap (v.adicCompletion K) (w.adicCompletion F)).injective, fun y => ?_⟩
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (K := v.adicCompletion K) (1 : w.adicCompletion F)
      one_ne_zero).1 hfin y
    exact ⟨c, by rw [← hc, Algebra.algebraMap_eq_smul_one]⟩
  let ι := RingEquiv.ofBijective (algebraMap (v.adicCompletion K) (w.adicCompletion F)) hbij
  have hv : ∀ x, Valued.v (ι x) = Valued.v x := fun x => by
    have := GroundTheory.Global.valued_algebraMap_adicCompletion v w x
    rw [he, pow_one] at this
    exact this
  exact ⟨ι, GroundTheory.Global.continuous_adicCompletionMap v w, continuous_symm_of_valued_eq ι hv,
    GroundTheory.Global.adicCompletionMap_algebraMap v w, hv⟩

end Pair

end PositivityTheory.Pf1.LocalLanglands.HeckeKernelConditions.RamifiedPlaceLift

end
