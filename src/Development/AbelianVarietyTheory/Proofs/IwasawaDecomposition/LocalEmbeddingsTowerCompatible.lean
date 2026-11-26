module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionTraceNormContinuous

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinpolyIrreducibleLocalEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinpolyIrreducibleLocalEmbedding
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocIrred

theorem minpoly_map_adicCompletion_irreducible : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)), IsPlaceOver A v → (∀ σ : G K Ω, ∃ τ ∈ Dec (F := K) A, ∀ x : L, τ (algebraMap L Ω x) = σ (algebraMap L Ω x)) → ∀ ι : Ω →ₐ[K] Kbar v, IsLocEmb A v ι → ∀ α : L, Irreducible ((minpoly K α).map (algebraMap K (v.adicCompletion K))) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ A v hA hdec ι hι α
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  set a : Ω := algebraMap L Ω α with ha
  have hPa : minpoly K a = minpoly K α := by
    have := minpoly.algHom_eq (IsScalarTower.toAlgHom K L Ω) (algebraMap L Ω).injective α
    simpa [ha] using this
  rw [← hPa]
  have haint : IsIntegral K a := (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
  set P := minpoly K a with hP
  have hsep : P.Separable := (minpoly.irreducible haint).separable
  set β := ι a with hβdef
  have hβ : IsIntegral (v.adicCompletion K) β := Algebra.IsIntegral.isIntegral β
  set Q := minpoly (v.adicCompletion K) β with hQ
  have hQdvd : Q ∣ P.map (algebraMap K (v.adicCompletion K)) := by
    apply minpoly.dvd
    rw [Polynomial.aeval_map_algebraMap, hβdef, Polynomial.aeval_algHom_apply, hP, minpoly.aeval, map_zero]
  obtain ⟨θ, -, -, hlift⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc K Ω A v hA ι hι
  set R := (P.map (algebraMap K Ω)).roots with hR
  have hRcard : Multiset.card R = P.natDegree :=
    by
    rw [hR, IsAlgClosed.card_roots_eq_natDegree, Polynomial.natDegree_map]
  have hRnd : R.Nodup := Polynomial.nodup_roots (hsep.map)
  have hSnd : (R.map ι).Nodup := hRnd.map ι.injective
  have hQ0 : Q ≠ 0 := minpoly.ne_zero hβ
  have hsub : R.map ι ≤ (Q.map (algebraMap (v.adicCompletion K) (Kbar v))).roots := by
    rw [Multiset.le_iff_subset hSnd]
    intro y hy
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hy
    have hr0 : Polynomial.aeval r P = 0 := by
      have := (Polynomial.mem_roots_map (minpoly.ne_zero haint)).mp hr
      rwa [Polynomial.aeval_def]
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' haint.isAlgebraic hr0
    obtain ⟨τ, hτ, hτσ⟩ := hdec σ
    have hg : θ ⟨τ, hτ⟩ β = ι r := by
      rw [hβdef, hlift ⟨τ, hτ⟩ a, ← hσ]
      exact congrArg ι (hτσ α)
    rw [Polynomial.mem_roots_map hQ0, ← Polynomial.aeval_def, ← hg, Polynomial.aeval_algEquiv,
      AlgHom.comp_apply, hQ, minpoly.aeval, map_zero]
  have hdeg : P.natDegree ≤ Q.natDegree := by
    calc P.natDegree = Multiset.card (R.map ι) := by rw [Multiset.card_map, hRcard]
      _ ≤ Multiset.card (Q.map (algebraMap (v.adicCompletion K) (Kbar v))).roots := Multiset.card_le_card hsub
      _ ≤ (Q.map (algebraMap (v.adicCompletion K) (Kbar v))).natDegree := Polynomial.card_roots' _
      _ = Q.natDegree := Polynomial.natDegree_map _
  have heq : P.map (algebraMap K (v.adicCompletion K)) = Q :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hβ) ((minpoly.monic haint).map _) hQdvd
      (by rw [Polynomial.natDegree_map]; exact hdeg)
  rw [heq]
  exact minpoly.irreducible hβ

end GlobalTheory.LocIrred
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinpolyIrreducibleLocalEmbeddingStatement
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minpoly_irreducible_local_embedding : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)), IsPlaceOver A v → (∀ σ : G K Ω, ∃ τ ∈ Dec (F := K) A, ∀ x : L, τ (algebraMap L Ω x) = σ (algebraMap L Ω x)) → ∀ ι : Ω →ₐ[K] Kbar v, IsLocEmb A v ι → ∀ α : L, Irreducible ((minpoly K α).map (algebraMap K (v.adicCompletion K))) := by
  first | exact @GlobalTheory.LocIrred.minpoly_map_adicCompletion_irreducible | exact GlobalTheory.LocIrred.minpoly_map_adicCompletion_irreducible | (intros; apply GlobalTheory.LocIrred.minpoly_map_adicCompletion_irreducible <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtensionPow
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfValuationEqPow
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Filter Topology
open scoped WithZeroTopology WithZero

namespace GlobalTheory.CompletionHomContinuous

theorem continuous_of_valuation_eq_pow {A B Γ : Type*} [Field A] [Field B]
    [LinearOrderedCommGroupWithZero Γ] [hA : Valued A Γ] [hB : Valued B Γ]
    (hs : Function.Surjective hA.v) (g : A →+* B) {e : ℕ} (he : 0 < e)
    (hg : ∀ x, hB.v (g x) = hA.v x ^ e) : Continuous g := by
  refine continuous_of_continuousAt_zero g ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero B Γ).tendsto_right_iff]
  intro γ _
  have hc : Continuous fun x : A => hA.v x ^ e :=
    (Valued.continuous_valuation_of_surjective hs).pow e
  have h0 : Tendsto (fun x : A => hA.v x ^ e) (𝓝 0) (𝓝 0) :=
    hc.tendsto' 0 0 (by simp [he.ne'])
  rw [WithZeroTopology.tendsto_zero] at h0
  have hγ : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  filter_upwards [h0 _ hγ] with x hx
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding, hg]
  exact hx

theorem exists_completion_hom (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : HeightOneSpectrum (RingOfIntegers K))
    (v' : HeightOneSpectrum (RingOfIntegers L)) (e : ℕ) (he : 0 < e)
    (h : ∀ x : K, v'.valuation L (algebraMap K L x) = v.valuation K x ^ e) :
    ∃ f : adicCompletion K v →+* adicCompletion L v', Continuous f ∧
      (∀ x : K, f (algebraMap K (adicCompletion K v) x) =
        algebraMap L (adicCompletion L v') (algebraMap K L x)) ∧
      ∀ y : adicCompletion K v, (Valued.v (f y) : WithZero (Multiplicative ℤ)) = Valued.v y ^ e := by
  let g : WithVal (v.valuation K) →+* adicCompletion L v' :=
    (algebraMap L (adicCompletion L v')).comp
      ((algebraMap K L).comp (WithVal.equiv (v.valuation K)).toRingHom)
  have hL : ∀ x : L, (Valued.v (algebraMap L (adicCompletion L v') x) : WithZero (Multiplicative ℤ))
      = v'.valuation L x := fun x => valuedAdicCompletion_eq_valuation' v' x
  have hK : ∀ x : K, (Valued.v (algebraMap K (adicCompletion K v) x) : WithZero (Multiplicative ℤ))
      = v.valuation K x := fun x => valuedAdicCompletion_eq_valuation' v x
  have hg : Continuous g := by
    refine continuous_of_valuation_eq_pow (Γ := WithZero (Multiplicative ℤ)) ?_ g he ?_
    · intro c
      obtain ⟨x, hx⟩ := v.valuation_surjective K c
      exact ⟨(WithVal.equiv (v.valuation K)).symm x, hx⟩
    · intro x
      exact (hL _).trans (h _)
  let f : adicCompletion K v →+* adicCompletion L v' :=
    (UniformSpace.Completion.extensionHom g hg).comp (adicCompletion.equiv K v).toRingHom
  have hf : Continuous f :=
    (UniformSpace.Completion.continuous_extension (f := g)).comp
      (adicCompletion.continuous_toCompletion K v)
  have hfx : ∀ x : K, f (algebraMap K (adicCompletion K v) x) =
      algebraMap L (adicCompletion L v') (algebraMap K L x) := fun x =>
    UniformSpace.Completion.extensionHom_coe g hg ((WithVal.equiv (v.valuation K)).symm x)
  refine ⟨f, hf, hfx, fun y => ?_⟩
  refine (denseRange_algebraMap K v).induction_on y ?_ ?_
  · exact isClosed_eq
      ((Valued.continuous_valuation_of_surjective (valuedAdicCompletion_surjective L v')).comp hf)
      ((Valued.continuous_valuation_of_surjective (valuedAdicCompletion_surjective K v)).pow e)
  · intro x
    rw [hfx, hL, hK, h]

end GlobalTheory.CompletionHomContinuous
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtensionPow
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DenseCompl


open scoped WithZeroTopology in
theorem exists_extension_pow (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (e : ℕ) (he : 0 < e)
    (hv : ∀ x : K, v'.valuation L (algebraMap K L x) = v.valuation K x ^ e) :
    ∃ f : v.adicCompletion K →+* v'.adicCompletion L, Continuous f ∧
      (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) ∧
      ∀ y, Valued.v (f y) = Valued.v y ^ e := by
  first
  | exact @_root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom
  | exact _root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom
  | (apply _root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom <;> assumption)
  | (intros; apply _root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CompletionHomContinuous.exists_completion_hom ..)

end GlobalTheory.DenseCompl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtensionPowStatement
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extension_pow_alt : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (e : ℕ), 0 < e → (∀ x : K, v'.valuation L (algebraMap K L x) = v.valuation K x ^ e) → ∃ f : v.adicCompletion K →+* v'.adicCompletion L, Continuous f ∧ (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) ∧ ∀ y, Valued.v (f y) = Valued.v y ^ e := by
  first | exact @GlobalTheory.DenseCompl.exists_extension_pow | exact GlobalTheory.DenseCompl.exists_extension_pow | (intros; apply GlobalTheory.DenseCompl.exists_extension_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionTraceNormOfBasisImage
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionTraceNormOfBasisImage
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.adicCompletion_trace_norm_of_basis_image : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (f : v.adicCompletion K →+* v'.adicCompletion L), (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) → letI := f.toAlgebra; ∀ (n : ℕ) (b : Module.Basis (Fin n) K L) (b' : Module.Basis (Fin n) (v.adicCompletion K) (v'.adicCompletion L)), (∀ i, b' i = algebraMap L _ (b i)) → ∀ z : L, Algebra.trace (v.adicCompletion K) (v'.adicCompletion L) (algebraMap L _ z) = algebraMap K _ (Algebra.trace K L z) ∧ Algebra.norm (v.adicCompletion K) (algebraMap L (v'.adicCompletion L) z) = algebraMap K _ (Algebra.norm K z) := by
  intro K L _ _ _ _ _ v v' f hf
  letI := f.toAlgebra
  intro n b b' hb z
  have hM : Algebra.leftMulMatrix b' (algebraMap L (v'.adicCompletion L) z) =
      (Algebra.leftMulMatrix b z).map (algebraMap K (v.adicCompletion K)) := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]
    have key : algebraMap L (v'.adicCompletion L) z * b' j =
        ∑ k, (algebraMap K (v.adicCompletion K) (b.repr (z * b j) k)) • b' k := by
      rw [hb, ← map_mul]
      conv_lhs => rw [← b.sum_repr (z * b j)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hb, Algebra.smul_def, Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, hf]
    rw [key, b'.repr_sum_self]
  rw [Algebra.trace_eq_matrix_trace b', Algebra.norm_eq_matrix_det b', hM,
    Algebra.trace_eq_matrix_trace b, Algebra.norm_eq_matrix_det b]
  refine ⟨?_, ?_⟩
  · exact (AddMonoidHom.map_trace (algebraMap K (v.adicCompletion K)).toAddMonoidHom _).symm
  · exact (RingHom.map_det _ _).symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionTraceNormOfBasisImageStatement
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicCompletion_trace_norm_of_basis_image_alt : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (f : v.adicCompletion K →+* v'.adicCompletion L), (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) → letI := f.toAlgebra; ∀ (n : ℕ) (b : Module.Basis (Fin n) K L) (b' : Module.Basis (Fin n) (v.adicCompletion K) (v'.adicCompletion L)), (∀ i, b' i = algebraMap L _ (b i)) → ∀ z : L, Algebra.trace (v.adicCompletion K) (v'.adicCompletion L) (algebraMap L _ z) = algebraMap K _ (Algebra.trace K L z) ∧ Algebra.norm (v.adicCompletion K) (algebraMap L (v'.adicCompletion L) z) = algebraMap K _ (Algebra.norm K z) := by
  first | exact @GlobalTheory.adicCompletion_trace_norm_of_basis_image | exact GlobalTheory.adicCompletion_trace_norm_of_basis_image | (intros; apply GlobalTheory.adicCompletion_trace_norm_of_basis_image <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationPowOfIsPlaceOver
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationPowOfIsPlaceOver
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LyingOver

theorem valuation_pow_of_isPlaceOver : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)), IsPlaceOver A v → IsPlaceOver A v' → ∃ e : ℕ, 0 < e ∧ ∀ x : K, v'.valuation L (algebraMap K L x) = v.valuation K x ^ e := by
  intro K L Ω _ _ _ _ _ _ _ _ _ A v v' hv hv'
  have hcomap : v'.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal := by
    ext x
    rw [Ideal.mem_comap, ← hv x, ← hv' (algebraMap (𝓞 K) (𝓞 L) x)]
    have : ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K L (x : K) := rfl
    rw [this, ← IsScalarTower.algebraMap_apply]
  haveI : v'.asIdeal.LiesOver v.asIdeal := ⟨hcomap.symm⟩
  refine ⟨v.asIdeal.ramificationIdx' v'.asIdeal,
    Nat.pos_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver v'.asIdeal v.ne_bot), ?_⟩
  intro x
  rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal v'.asIdeal v.ne_bot]
  exact (IsDedekindDomain.HeightOneSpectrum.valuation_liesOver L v v' x).symm

end GlobalTheory.LyingOver
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationPowOfIsPlaceOverStatement
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_pow_of_isPlaceOver_alt : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)), IsPlaceOver A v → IsPlaceOver A v' → ∃ e : ℕ, 0 < e ∧ ∀ x : K, v'.valuation L (algebraMap K L x) = v.valuation K x ^ e := by
  first | exact @GlobalTheory.LyingOver.valuation_pow_of_isPlaceOver | exact GlobalTheory.LyingOver.valuation_pow_of_isPlaceOver | (intros; apply GlobalTheory.LyingOver.valuation_pow_of_isPlaceOver <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingsDifferByDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingsDifferByDecomposition
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Pointwise

namespace GlobalTheory.LocEmbDec

theorem exists_dec_of_isLocEmb : ∀ (K Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (ι ι₂ : Ω →ₐ[K] Kbar v), IsLocEmb A v ι → IsLocEmb A v ι₂ → ∃ σ ∈ Dec (F := K) A, ∀ z, ι₂ z = ι (σ z) := by
  intro K Ω _ _ _ _ _ A v ι ι₂ hι hι₂
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  set e : Ω ≃ₐ[K] ι.fieldRange := AlgEquiv.ofInjectiveField ι with he
  haveI : Normal K ι.fieldRange := Normal.of_algEquiv e
  have hr : (ι₂.comp e.symm.toAlgHom).fieldRange = ι.fieldRange :=
    AlgHom.fieldRange_of_normal _
  have hmem : ∀ z, ι₂ z ∈ ι.fieldRange := fun z => by
    rw [← hr]; exact ⟨e z, by simp⟩
  let f : Ω →ₐ[K] ι.fieldRange := ι₂.codRestrict ι.fieldRange.toSubalgebra hmem
  let σ0 : Ω →ₐ[K] Ω := e.symm.toAlgHom.comp f
  let σ : Ω ≃ₐ[K] Ω := AlgEquiv.ofBijective σ0 (Algebra.IsAlgebraic.algHom_bijective σ0)
  have key : ∀ z, ι (σ z) = ι₂ z := fun z => by
    have h1 : ((e (σ z) : ι.fieldRange) : Kbar v) = ι (σ z) := rfl
    rw [← h1]
    change ((e (e.symm (f z)) : ι.fieldRange) : Kbar v) = ι₂ z
    rw [AlgEquiv.apply_symm_apply]; rfl
  refine ⟨σ, ?_, fun z => (key z).symm⟩
  show σ • A = A
  have hA : ∀ x, σ x ∈ A ↔ x ∈ A := fun x => by rw [hι, key, ← hι₂]
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← hA]
  show σ (σ⁻¹ y) ∈ A ↔ y ∈ A
  rw [← AlgEquiv.mul_apply, mul_inv_cancel]
  rfl

end GlobalTheory.LocEmbDec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingsDifferByDecompositionStatement
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_embeddings_differ_by_decomposition : ∀ (K Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (ι ι₂ : Ω →ₐ[K] Kbar v), IsLocEmb A v ι → IsLocEmb A v ι₂ → ∃ σ ∈ Dec (F := K) A, ∀ z, ι₂ z = ι (σ z) := by
  first | exact @GlobalTheory.LocEmbDec.exists_dec_of_isLocEmb | exact GlobalTheory.LocEmbDec.exists_dec_of_isLocEmb | (intros; apply GlobalTheory.LocEmbDec.exists_dec_of_isLocEmb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentCompletionOfIrreducibleMinpolyA
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentCompletionOfIrreducibleMinpolyA
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem algebraMap_mem_span_of_mem_span {K L A M : Type} [Field K] [Field L] [Algebra K L]
    [Field A] [CommRing M] [Algebra L M] [Algebra A M] (g : K →+* A)
    (hg : ∀ c : K, algebraMap A M (g c) = algebraMap L M (algebraMap K L c))
    {ι : Type} (s : ι → L) (x : L) (hx : x ∈ Submodule.span K (Set.range s)) :
    algebraMap L M x ∈ Submodule.span A (Set.range fun i => algebraMap L M (s i)) := by
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [Algebra.smul_def, map_mul, ← hg, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ hy

theorem linearIndependent_completion_of_irreducible_minpoly :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (f : v.adicCompletion K →+* v'.adicCompletion L), (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) → (∀ α : L, Irreducible ((minpoly K α).map (algebraMap K (v.adicCompletion K)))) → letI := f.toAlgebra; ∀ (n : ℕ) (b : Module.Basis (Fin n) K L), LinearIndependent (v.adicCompletion K) fun i => algebraMap L (v'.adicCompletion L) (b i) := by
  intro K L _ _ _ _ _ v v' f hf hirr
  letI := f.toAlgebra
  intro n b
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  have hcomp : f.comp (algebraMap K (v.adicCompletion K)) =
      (algebraMap L (v'.adicCompletion L)).comp (algebraMap K L) := RingHom.ext hf
  have hroot : Polynomial.aeval (algebraMap L (v'.adicCompletion L) α)
      ((minpoly K α).map (algebraMap K (v.adicCompletion K))) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    change Polynomial.eval₂ (f.comp (algebraMap K (v.adicCompletion K))) _ _ = 0
    rw [hcomp, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval, map_zero]
  have hmin : (minpoly K α).map (algebraMap K (v.adicCompletion K)) =
      minpoly (v.adicCompletion K) (algebraMap L (v'.adicCompletion L) α) :=
    minpoly.eq_of_irreducible_of_monic (hirr α) hroot ((minpoly.monic hint).map _)
  have hdeg : (minpoly (v.adicCompletion K) (algebraMap L (v'.adicCompletion L) α)).natDegree
      = n := by
    rw [← hmin, (minpoly.monic hint).natDegree_map, ← IntermediateField.adjoin.finrank hint, hα,
      IntermediateField.finrank_top', Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hpow := linearIndependent_pow (K := v.adicCompletion K)
    (algebraMap L (v'.adicCompletion L) α)
  have hle : Submodule.span (v.adicCompletion K) (Set.range fun i : Fin (minpoly
      (v.adicCompletion K) (algebraMap L (v'.adicCompletion L) α)).natDegree =>
        (algebraMap L (v'.adicCompletion L) α) ^ (i : ℕ)) ≤
      Submodule.span (v.adicCompletion K)
        (Set.range fun i => algebraMap L (v'.adicCompletion L) (b i)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have := algebraMap_mem_span_of_mem_span (M := v'.adicCompletion L)
      (algebraMap K (v.adicCompletion K)) hf b (α ^ (i : ℕ)) (by rw [b.span_eq]; trivial)
    simpa using this
  have h1 := finrank_span_eq_card hpow
  have h2 := finrank_range_le_card (R := v.adicCompletion K)
    (fun i => algebraMap L (v'.adicCompletion L) (b i))
  haveI : Module.Finite (v.adicCompletion K) (Submodule.span (v.adicCompletion K)
      (Set.range fun i => algebraMap L (v'.adicCompletion L) (b i))) :=
    FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have h3 := Submodule.finrank_mono hle
  rw [linearIndependent_iff_card_eq_finrank_span]
  simp only [Fintype.card_fin] at h1 h2 ⊢
  rw [Set.finrank] at h2 ⊢
  omega

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentCompletionOfIrreducibleMinpolyAStatement
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_completion_of_irreducible_minpoly_alt : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (f : v.adicCompletion K →+* v'.adicCompletion L), (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) → (∀ α : L, Irreducible ((minpoly K α).map (algebraMap K (v.adicCompletion K)))) → letI := f.toAlgebra; ∀ (n : ℕ) (b : Module.Basis (Fin n) K L), LinearIndependent (v.adicCompletion K) fun i => algebraMap L (v'.adicCompletion L) (b i) := by
  first | exact @GlobalTheory.linearIndependent_completion_of_irreducible_minpoly | exact GlobalTheory.linearIndependent_completion_of_irreducible_minpoly | (intros; apply GlobalTheory.linearIndependent_completion_of_irreducible_minpoly <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueClosureIsoRamifiedExt
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueClosureIsoRamifiedExt
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocIntegral

open Polynomial
open scoped WithZero

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}

theorem exists_valued_eq (γ : ℤᵐ⁰) : ∃ c : v.adicCompletion K, Valued.v c = γ := by
  obtain ⟨x, hx⟩ := v.valuation_surjective K γ
  exact ⟨algebraMap K _ x, (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x).trans hx⟩

theorem valued_coeff_minpoly_le_one (e : ℕ) (he : 0 < e)
    (f : v.adicCompletion K →+* v'.adicCompletion L)
    (hfv : ∀ y, Valued.v (f y) = Valued.v y ^ e) :
    letI := f.toAlgebra; FiniteDimensional (v.adicCompletion K) (v'.adicCompletion L) →
    ∀ x : v'.adicCompletion L, Valued.v x ≤ 1 →
      ∀ n, Valued.v ((minpoly (v.adicCompletion K) x).coeff n) ≤ 1 := by
  letI := f.toAlgebra
  intro hfd x hx n
  letI : NontriviallyNormedField (v.adicCompletion K) := Valued.toNontriviallyNormedField _ ℤᵐ⁰
  haveI : IsUltrametricDist (v.adicCompletion K) :=
    inferInstanceAs (@IsUltrametricDist (v.adicCompletion K)
      (Valued.toNormedField (v.adicCompletion K) ℤᵐ⁰).toDist)
  haveI : CompleteSpace (v.adicCompletion K) := inferInstance
  choose c hc using (exists_valued_eq (v := v) : ∀ γ : ℤᵐ⁰, ∃ c : v.adicCompletion K, Valued.v c = γ)
  have hmono : ∀ a b : v.adicCompletion K, Valued.v a ≤ Valued.v b → ‖a‖ ≤ ‖b‖ :=
    fun a b h => Valued.toNormedField.norm_le_iff.2 h
  have hnorm : ∀ a b : v.adicCompletion K, Valued.v a = Valued.v b → ‖a‖ = ‖b‖ :=
    fun a b h => le_antisymm (hmono a b h.le) (hmono b a h.ge)
  have he' : (e : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast he.ne')
  let ρ : v'.adicCompletion L → ℝ := fun z => ‖c (Valued.v z)‖ ^ ((e : ℝ)⁻¹)
  have ρ_nonneg : ∀ z, 0 ≤ ρ z := fun z => Real.rpow_nonneg (norm_nonneg _) _
  have ρ_mul : ∀ a b, ρ (a * b) = ρ a * ρ b := by
    intro a b
    simp only [ρ]
    rw [← Real.mul_rpow (norm_nonneg _) (norm_nonneg _), ← norm_mul]
    congr 1
    apply hnorm
    rw [hc, Valuation.map_mul, Valuation.map_mul, hc, hc]
  have ρ_le : ∀ a b, Valued.v a ≤ Valued.v b → ρ a ≤ ρ b := by
    intro a b h
    exact Real.rpow_le_rpow (norm_nonneg _) (hmono _ _ (by rw [hc, hc]; exact h))
      (inv_nonneg.2 (Nat.cast_nonneg _))
  have ρ_zero : ρ 0 = 0 := by
    simp only [ρ]
    have : c (Valued.v (0 : v'.adicCompletion L)) = 0 := by
      rw [← Valuation.zero_iff Valued.v, hc, Valuation.map_zero]
    rw [this, norm_zero, Real.zero_rpow he']
  have ρ_eq_zero : ∀ z, ρ z = 0 → z = 0 := by
    intro z hz
    simp only [ρ] at hz
    rw [Real.rpow_eq_zero (norm_nonneg _) he', norm_eq_zero] at hz
    have := hc (Valued.v z)
    rw [hz, Valuation.map_zero] at this
    exact (Valuation.zero_iff _).1 this.symm
  have ρ_f : ∀ a, ρ (f a) = ‖a‖ := by
    intro a
    simp only [ρ]
    rw [hnorm _ (a ^ e) (by rw [hc, hfv, Valuation.map_pow]), norm_pow,
      Real.pow_rpow_inv_natCast (norm_nonneg _) he.ne']
  have ρ_one : ρ 1 = 1 := by
    have := ρ_f 1
    rwa [map_one, norm_one] at this
  let N : AlgebraNorm (v.adicCompletion K) (v'.adicCompletion L) :=
    { toFun := ρ
      map_zero' := ρ_zero
      add_le' := fun a b => by
        rcases le_total (Valued.v a) (Valued.v b) with h | h
        · have := ρ_le (a + b) b ((Valuation.map_add _ a b).trans (max_le h le_rfl))
          linarith [ρ_nonneg a]
        · have := ρ_le (a + b) a ((Valuation.map_add _ a b).trans (max_le le_rfl h))
          linarith [ρ_nonneg b]
      neg' := fun a => by simp only [ρ, Valuation.map_neg]
      mul_le' := fun a b => (ρ_mul a b).le
      eq_zero_of_map_eq_zero' := ρ_eq_zero
      smul' := fun a z => by
        rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, ρ_mul, ρ_f] }
  have hN : ∀ z, N z = ρ z := fun _ => rfl
  have hpm : IsPowMul N := by
    intro a k hk
    clear hk
    rw [hN, hN]
    induction k with
    | zero => simp [ρ_one]
    | succ k ih => rw [pow_succ, ρ_mul, ih, pow_succ]
  have hu := spectralNorm_unique (K := v.adicCompletion K) (L := v'.adicCompletion L) hpm
  have hsx : spectralNorm (v.adicCompletion K) (v'.adicCompletion L) x ≤ 1 := by
    rw [← spectralAlgNorm_def, ← hu, hN, ← ρ_one]
    exact ρ_le x 1 (by rw [Valuation.map_one]; exact hx)
  have hxi : IsIntegral (v.adicCompletion K) x := Algebra.IsIntegral.isIntegral x
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hxi)] at hsx
  exact Valued.toNormedField.norm_le_one_iff.1 (hsx n)

end GlobalTheory.LocIntegral

namespace GlobalTheory.LocIntegral

open Polynomial

theorem isIntegral_iff_isIntegral_map : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (e : ℕ)
    (f : v.adicCompletion K →+* v'.adicCompletion L), 0 < e →
    (∀ y, Valued.v (f y) = Valued.v y ^ e) →
    letI := f.toAlgebra; FiniteDimensional (v.adicCompletion K) (v'.adicCompletion L) →
    ∀ b₀ : Kbar v ≃+* Kbar v',
      (∀ x, b₀ (algebraMap (v.adicCompletion K) (Kbar v) x) =
        algebraMap (v'.adicCompletion L) (Kbar v') (f x)) →
      ∀ y : Kbar v, IsIntegral (v.adicCompletionIntegers K) y ↔
        IsIntegral (v'.adicCompletionIntegers L) (b₀ y) := by
  intro K L _ _ _ _ v v' e f he hfv
  letI := f.toAlgebra
  intro hfd b₀ hb y
  have hle : ∀ a ∈ v.adicCompletionIntegers K, f a ∈ v'.adicCompletionIntegers L := by
    intro a ha
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ha ⊢
    rw [hfv]
    exact pow_le_one₀ zero_le' ha
  let g : v.adicCompletionIntegers K →+* v'.adicCompletionIntegers L :=
    f.restrict (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L) hle
  have hg : ∀ a, ((g a : v'.adicCompletionIntegers L) : v'.adicCompletion L) = f a := fun _ => rfl
  have hcomp : (algebraMap (v'.adicCompletionIntegers L) (Kbar v')).comp g =
      b₀.toRingHom.comp (algebraMap (v.adicCompletionIntegers K) (Kbar v)) := by
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom]
    rw [IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K) (v.adicCompletion K) (Kbar v),
      IsScalarTower.algebraMap_apply (v'.adicCompletionIntegers L) (v'.adicCompletion L) (Kbar v'),
      hb]
    rfl
  constructor
  · intro hy
    exact IsIntegral.map_of_comp_eq g b₀.toRingHom hcomp hy
  · intro hy
    letI alg1 : Algebra (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L) := g.toAlgebra
    letI alg2 : Algebra (v'.adicCompletionIntegers L) (Kbar v) :=
      (b₀.symm.toRingHom.comp (algebraMap (v'.adicCompletionIntegers L) (Kbar v'))).toAlgebra
    haveI : IsScalarTower (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L) (Kbar v) := by
      refine IsScalarTower.of_algebraMap_eq fun a => ?_
      have h := congrArg (fun φ => b₀.symm (φ a)) hcomp
      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] at h
      rw [← h]
      rfl
    haveI : Algebra.IsIntegral (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L) := by
      constructor
      intro a
      have ha : Valued.v (a : v'.adicCompletion L) ≤ 1 :=
        (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 a.2
      have hc := valued_coeff_minpoly_le_one e he f hfv hfd (a : v'.adicCompletion L) ha
      have hai : IsIntegral (v.adicCompletion K) (a : v'.adicCompletion L) :=
        Algebra.IsIntegral.isIntegral _
      have hl : minpoly (v.adicCompletion K) (a : v'.adicCompletion L) ∈
          Polynomial.lifts (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro n
        exact ⟨⟨_, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hc n)⟩, rfl⟩
      obtain ⟨q, hq, -, hm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (minpoly.monic hai)
      refine ⟨q, hm, ?_⟩
      apply Subtype.ext
      have e1 := Polynomial.hom_eval₂ q (algebraMap (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L))
        (v'.adicCompletionIntegers L).subtype a
      have e2 : ((v'.adicCompletionIntegers L).subtype).comp
          (algebraMap (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L)) =
          (algebraMap (v.adicCompletion K) (v'.adicCompletion L)).comp
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) := by
        ext; rfl
      rw [e2, ← Polynomial.eval₂_map, hq] at e1
      exact e1.trans (minpoly.aeval (v.adicCompletion K) (a : v'.adicCompletion L))
    have h1 : IsIntegral (v'.adicCompletionIntegers L) y := by
      have := IsIntegral.map_of_comp_eq (RingHom.id (v'.adicCompletionIntegers L)) b₀.symm.toRingHom
        (by ext; rfl) hy
      simpa using this
    exact isIntegral_trans y h1

end GlobalTheory.LocIntegral
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueClosureIsoRamifiedExtStatement
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_closure_iso_ramified_ext : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (e : ℕ) (f : v.adicCompletion K →+* v'.adicCompletion L), 0 < e → (∀ y, Valued.v (f y) = Valued.v y ^ e) → letI := f.toAlgebra; FiniteDimensional (v.adicCompletion K) (v'.adicCompletion L) → ∀ b₀ : Kbar v ≃+* Kbar v', (∀ x, b₀ (algebraMap (v.adicCompletion K) (Kbar v) x) = algebraMap (v'.adicCompletion L) (Kbar v') (f x)) → ∀ y : Kbar v, IsIntegral (v.adicCompletionIntegers K) y ↔ IsIntegral (v'.adicCompletionIntegers L) (b₀ y) := by
  first | exact @GlobalTheory.LocIntegral.isIntegral_iff_isIntegral_map | exact GlobalTheory.LocIntegral.isIntegral_iff_isIntegral_map | (intros; apply GlobalTheory.LocIntegral.isIntegral_iff_isIntegral_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingsTowerCompatible
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

theorem GlobalTheory.LocalExtCompletion.exists_completion_ext : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (_ : IsPlaceOver A v'), IsLocalExt L h → ∀ (ι : Ω →ₐ[K] Kbar v) (ι' : Ω →ₐ[L] Kbar v'), IsLocEmb A v ι → IsLocEmb A v' ι' → ∃ (f : v.adicCompletion K →+* v'.adicCompletion L) (b : Kbar v ≃+* Kbar v'), Continuous f ∧ (∀ x, b (algebraMap _ _ x) = algebraMap _ _ (f x)) ∧ (∀ z, b (ι z) = ι' z) ∧ (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) ∧ (letI := f.toAlgebra; Module.finrank (v.adicCompletion K) (v'.adicCompletion L) = Module.finrank K L ∧ Continuous (Algebra.trace (v.adicCompletion K) (v'.adicCompletion L)) ∧ (∀ z : L, Algebra.trace (v.adicCompletion K) (v'.adicCompletion L) (algebraMap L _ z) = algebraMap K _ (Algebra.trace K L z)) ∧ Continuous (Algebra.norm (v.adicCompletion K) : v'.adicCompletion L → v.adicCompletion K) ∧ ∀ z : L, Algebra.norm (v.adicCompletion K) (algebraMap L (v'.adicCompletion L) z) = algebraMap K _ (Algebra.norm K z)) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' hloc ι ι' hι hι'
  obtain ⟨e, he, hv⟩ := GlobalTheory.T.valuation_pow_of_isPlaceOver_alt K L Ω A v v' h h'
  obtain ⟨f, hfc, hfK, hfv⟩ := GlobalTheory.T.exists_extension_pow_alt K L v v' e he hv
  have hirr := GlobalTheory.T.minpoly_irreducible_local_embedding K L Ω A v h (fun σ => by
    obtain ⟨τ, hτ⟩ := hloc σ
    exact ⟨τ, Weil_le_Dec h τ.2, hτ⟩) ι hι
  letI : Algebra (v.adicCompletion K) (v'.adicCompletion L) := f.toAlgebra
  have hind := GlobalTheory.T.linearIndependent_completion_of_irreducible_minpoly_alt K L v v' f hfK hirr _ (Module.finBasis K L)
  have hspan := GlobalTheory.T.span_basis_image_adicCompletion_eq_top_alt K L v v' f hfc hfK _ (Module.finBasis K L)
  let b' : Module.Basis (Fin (Module.finrank K L)) (v.adicCompletion K) (v'.adicCompletion L) :=
    Module.Basis.mk hind hspan.ge
  have hb' : ∀ i, b' i = algebraMap L _ (Module.finBasis K L i) := fun i => Module.Basis.mk_apply _ _ _
  haveI hfd : FiniteDimensional (v.adicCompletion K) (v'.adicCompletion L) := Module.Finite.of_basis b'
  have hrank : Module.finrank (v.adicCompletion K) (v'.adicCompletion L) = Module.finrank K L := by
    rw [Module.finrank_eq_card_basis b', Fintype.card_fin]
  have htn := GlobalTheory.T.adicCompletion_trace_norm_of_basis_image_alt K L v v' f hfK _ (Module.finBasis K L) b' hb'
  have hcont := GlobalTheory.T.adicCompletion_trace_norm_continuous_alt K L v v' f hfc hfd

  haveI : Algebra.IsAlgebraic (v.adicCompletion K) (v'.adicCompletion L) := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic (v.adicCompletion K) (Kbar v') :=
    Algebra.IsAlgebraic.trans (v.adicCompletion K) (v'.adicCompletion L) (Kbar v')
  haveI : IsAlgClosure (v.adicCompletion K) (Kbar v') := ⟨inferInstance, inferInstance⟩
  let b₀ : Kbar v ≃ₐ[v.adicCompletion K] Kbar v' := IsAlgClosure.equiv (v.adicCompletion K) (Kbar v) (Kbar v')
  have hb₀ : ∀ x, b₀ (algebraMap (v.adicCompletion K) (Kbar v) x) = algebraMap (v'.adicCompletion L) (Kbar v') (f x) :=
    fun x => (b₀.commutes x).trans rfl
  have hint := GlobalTheory.T.residue_closure_iso_ramified_ext K L v v' e f he hfv hfd b₀.toRingEquiv hb₀
  let ι₂ : Ω →ₐ[K] Kbar v :=
    { (b₀.symm.toRingEquiv.toRingHom.comp ι'.toRingHom) with
      commutes' := fun x => by
        change b₀.symm (ι' (algebraMap K Ω x)) = algebraMap K (Kbar v) x
        rw [IsScalarTower.algebraMap_apply K L Ω, ι'.commutes,
          IsScalarTower.algebraMap_apply L (v'.adicCompletion L) (Kbar v'), ← hfK, ← hb₀,
          AlgEquiv.symm_apply_apply, ← IsScalarTower.algebraMap_apply] }
  have hι₂ : IsLocEmb A v ι₂ := fun z => by
    rw [hι' z, hint]
    change IsIntegral _ (ι' z) ↔ IsIntegral _ (b₀ (b₀.symm (ι' z)))
    rw [AlgEquiv.apply_symm_apply]
  obtain ⟨σ, hσ, hσι⟩ := GlobalTheory.T.local_embeddings_differ_by_decomposition K Ω A v ι ι₂ hι hι₂
  obtain ⟨θ, -, -, hθ⟩ := GlobalTheory.T.decomposition_group_local_galois_iso K Ω A v h ι hι
  let g := θ ⟨σ, hσ⟩
  have hg : ∀ z, g (ι z) = b₀.symm (ι' z) := fun z => (hθ ⟨σ, hσ⟩ z).trans (hσι z).symm
  refine ⟨f, g.toRingEquiv.trans b₀.toRingEquiv, hfc, fun x => ?_, fun z => ?_, hfK, hrank, hcont.1,
    fun z => (htn z).1, hcont.2, fun z => (htn z).2⟩
  · change b₀ (g (algebraMap _ _ x)) = _
    rw [g.commutes, hb₀]
  · change b₀ (g (ι z)) = _
    rw [hg, AlgEquiv.apply_symm_apply]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingsTowerCompatibleStatement
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_embeddings_tower_compatible : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (_ : IsPlaceOver A v'), IsLocalExt L h → ∀ (ι : Ω →ₐ[K] Kbar v) (ι' : Ω →ₐ[L] Kbar v'), IsLocEmb A v ι → IsLocEmb A v' ι' → ∃ (f : v.adicCompletion K →+* v'.adicCompletion L) (b : Kbar v ≃+* Kbar v'), Continuous f ∧ (∀ x, b (algebraMap _ _ x) = algebraMap _ _ (f x)) ∧ (∀ z, b (ι z) = ι' z) ∧ (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) ∧ (letI := f.toAlgebra; Module.finrank (v.adicCompletion K) (v'.adicCompletion L) = Module.finrank K L ∧ Continuous (Algebra.trace (v.adicCompletion K) (v'.adicCompletion L)) ∧ (∀ z : L, Algebra.trace (v.adicCompletion K) (v'.adicCompletion L) (algebraMap L _ z) = algebraMap K _ (Algebra.trace K L z)) ∧ Continuous (Algebra.norm (v.adicCompletion K) : v'.adicCompletion L → v.adicCompletion K) ∧ ∀ z : L, Algebra.norm (v.adicCompletion K) (algebraMap L (v'.adicCompletion L) z) = algebraMap K _ (Algebra.norm K z)) := by
  first | exact @GlobalTheory.LocalExtCompletion.exists_completion_ext | exact GlobalTheory.LocalExtCompletion.exists_completion_ext | (intros; apply GlobalTheory.LocalExtCompletion.exists_completion_ext <;> assumption)
end
