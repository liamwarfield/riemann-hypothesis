module

public import GroundTheory.GlobalFields.SemilocalAlgebras.LocalDegree

@[expose] public section

section -- merged from GroundTheory.GlobalFields.SemilocalAlgebras.Approximation
namespace GroundTheory.Global

open IsDedekindDomain NumberField WithZeroMulInt WithZero Topology Filter

noncomputable section

namespace SemiLocal

variable {L : Type*} [Field L] [NumberField L]

theorem exists_sub_mem_pow_of_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → HeightOneSpectrum (𝓞 L)) (hw : Function.Injective w) (i : ι) (n : ℕ) :
    ∃ a : 𝓞 L, ∀ j, a - (if j = i then 1 else 0) ∈ (w j).asIdeal ^ n := by
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Finset.univ)
    (fun j ↦ (w j).asIdeal) (fun _ ↦ n) (fun j _ ↦ (w j).prime)
    (fun j _ k _ hjk h ↦ hjk (hw (HeightOneSpectrum.ext h)))
    (fun j ↦ if j.1 = i then 1 else 0)
  exact ⟨y, fun j ↦ hy j (Finset.mem_univ j)⟩

theorem norm_algebraMap_le_of_mem_pow (w : HeightOneSpectrum (𝓞 L)) (a : 𝓞 L) (n : ℕ)
    (ha : a ∈ w.asIdeal ^ n) :
    ‖algebraMap (𝓞 L) (w.adicCompletion L) a‖ ≤
      ((toNNReal (HeightOneSpectrum.absNorm_ne_zero w) (exp (-1 : ℤ)) : ℝ)) ^ n := by
  rw [IsScalarTower.algebraMap_apply (𝓞 L) L (w.adicCompletion L),
    HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply, ← FinitePlace.embedding_apply, FinitePlace.norm_embedding_int, ← NNReal.coe_pow,
    NNReal.coe_le_coe, ← map_pow]
  apply (toNNReal_strictMono (HeightOneSpectrum.one_lt_absNorm_nnreal w)).monotone
  rw [← exp_nsmul, smul_neg, nsmul_one]
  exact (w.intValuation_le_pow_iff_mem a n).2 ha

theorem toNNReal_exp_neg_one_lt_one (w : HeightOneSpectrum (𝓞 L)) :
    ((toNNReal (HeightOneSpectrum.absNorm_ne_zero w) (exp (-1 : ℤ)) : ℝ)) < 1 := by
  rw [← NNReal.coe_one, NNReal.coe_lt_coe,
    toNNReal_lt_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal w)]
  rw [← exp_zero, exp_lt_exp]
  norm_num

theorem denseRange_algebraMap_pi {ι : Type*} [Finite ι] (w : ι → HeightOneSpectrum (𝓞 L))
    (hw : Function.Injective w) :
    DenseRange (fun x : L ↦ fun i ↦ algebraMap L ((w i).adicCompletion L) x) := by
  classical
  have := Fintype.ofFinite ι
  let f : L →+* ((i : ι) → (w i).adicCompletion L) := RingHom.pi fun i ↦ algebraMap L _
  let S : Subring ((i : ι) → (w i).adicCompletion L) := f.range.topologicalClosure
  have hδ : ∀ i, Pi.single i 1 ∈ S := by
    intro i
    choose a ha using fun n ↦ exists_sub_mem_pow_of_injective w hw i n
    refine mem_closure_of_tendsto (b := atTop) (f := fun n ↦ f (algebraMap (𝓞 L) L (a n))) ?_
      (Eventually.of_forall fun n ↦ ⟨_, rfl⟩)
    rw [tendsto_pi_nhds]
    intro j
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (NNReal.coe_nonneg _)
        (toNNReal_exp_neg_one_lt_one (w j)))
    have h := norm_algebraMap_le_of_mem_pow (w j) _ n (ha n j)
    refine le_of_eq_of_le ?_ h
    congr 1
    by_cases hji : j = i
    · subst hji
      simp [f, ← IsScalarTower.algebraMap_apply]
    · simp [f, hji, ← IsScalarTower.algebraMap_apply]
  have hE : ∀ y : ι → L, (fun i ↦ algebraMap L ((w i).adicCompletion L) (y i)) ∈ S := by
    intro y
    have : (fun i ↦ algebraMap L ((w i).adicCompletion L) (y i)) =
        ∑ i, Pi.single i 1 * f (y i) := by
      funext j
      simp only [Finset.sum_apply, Pi.mul_apply, f, RingHom.pi_apply]
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb.symm]
      · simp
    rw [this]
    exact S.sum_mem fun i _ ↦ S.mul_mem (hδ i) (f.range.le_topologicalClosure ⟨y i, rfl⟩)
  have hdense : DenseRange (fun y : ι → L ↦ fun i ↦ algebraMap L ((w i).adicCompletion L) (y i)) :=
    DenseRange.piMap fun i ↦ HeightOneSpectrum.denseRange_algebraMap L (w i)
  have hsub : Set.range (fun y : ι → L ↦ fun i ↦ algebraMap L ((w i).adicCompletion L) (y i)) ⊆
      closure (Set.range f) := by
    rintro _ ⟨y, rfl⟩
    exact hE y
  exact dense_closure.1 (hdense.mono hsub)

end SemiLocal

end

end GroundTheory.Global
end

namespace GroundTheory.Global

open IsDedekindDomain NumberField TensorProduct Module

noncomputable section

namespace SemiLocal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (L) (v : HeightOneSpectrum (𝓞 K))

abbrev CompletionsOver : Type _ := (w : PlacesOver L v) → w.1.adicCompletion L

def tensorMap : v.adicCompletion K ⊗[K] L →ₐ[v.adicCompletion K] CompletionsOver L v :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (IsScalarTower.toAlgHom K L _)
    (fun _ _ ↦ Commute.all _ _)

@[simp] theorem tensorMap_tmul (a : v.adicCompletion K) (x : L) :
    tensorMap L v (a ⊗ₜ x) =
      algebraMap (v.adicCompletion K) (CompletionsOver L v) a * algebraMap L _ x := by
  simp [tensorMap]

theorem denseRange_algebraMap_completionsOver :
    DenseRange (algebraMap L (CompletionsOver L v)) :=
  denseRange_algebraMap_pi (fun w : PlacesOver L v ↦ w.1) Subtype.val_injective

open scoped Valued in
theorem tensorMap_surjective : Function.Surjective (tensorMap L v) := by
  have hclosed : IsClosed (LinearMap.range (tensorMap L v).toLinearMap :
      Set (CompletionsOver L v)) :=
    Submodule.isClosed_of_finiteDimensional _
  have hdense : Dense (Set.range (tensorMap L v)) := by
    refine (denseRange_algebraMap_completionsOver L v).mono ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by simp⟩
  rw [LinearMap.coe_range] at hclosed
  have h2 : closure (Set.range (tensorMap L v)) = Set.range (tensorMap L v) := hclosed.closure_eq
  rw [← Set.range_eq_univ, ← h2, hdense.closure_eq]

theorem sum_finrank_le :
    ∑ w : PlacesOver L v, finrank (v.adicCompletion K) (w.1.adicCompletion L) ≤ finrank K L := by
  rw [← Module.finrank_pi_fintype]
  calc _ ≤ finrank (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) :=
        LinearMap.finrank_le_finrank_of_surjective (f := (tensorMap L v).toLinearMap)
          (tensorMap_surjective L v)
    _ = finrank K L := Module.finrank_baseChange

theorem sum_ramificationIdx_mul_inertiaDeg :
    ∑ w : PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) * w.1.asIdeal.inertiaDeg (𝓞 K) =
      finrank K L := by
  have := v.isPrime
  rw [IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L,
    ← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 L)]
  exact Fintype.sum_equiv (placesOverEquiv L v) _ _ (fun _ ↦ rfl)

theorem sum_finrank_eq :
    ∑ w : PlacesOver L v, finrank (v.adicCompletion K) (w.1.adicCompletion L) = finrank K L := by
  refine le_antisymm (sum_finrank_le L v) ?_
  rw [← sum_ramificationIdx_mul_inertiaDeg L v]
  exact Finset.sum_le_sum fun w _ ↦ ramificationIdx_mul_inertiaDeg_le_finrank v w.1

theorem finrank_eq_ramificationIdx_mul_inertiaDeg (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    finrank (v.adicCompletion K) (w.adicCompletion L) =
      w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) := by
  have h := (Finset.sum_eq_sum_iff_of_le
    (fun (w : PlacesOver L v) _ ↦ ramificationIdx_mul_inertiaDeg_le_finrank v w.1)).1
    (by rw [sum_ramificationIdx_mul_inertiaDeg, sum_finrank_eq])
  exact (h ⟨w, inferInstance⟩ (Finset.mem_univ _)).symm

theorem tensorMap_injective : Function.Injective (tensorMap L v) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (tensorMap L v).toLinearMap)
    (by rw [Module.finrank_baseChange, Module.finrank_pi_fintype, sum_finrank_eq])).2
    (tensorMap_surjective L v)

def tensorEquiv : v.adicCompletion K ⊗[K] L ≃ₐ[v.adicCompletion K] CompletionsOver L v :=
  AlgEquiv.ofBijective (tensorMap L v) ⟨tensorMap_injective L v, tensorMap_surjective L v⟩

@[simp] theorem tensorEquiv_tmul (a : v.adicCompletion K) (x : L) :
    tensorEquiv L v (a ⊗ₜ x) =
      algebraMap (v.adicCompletion K) (CompletionsOver L v) a * algebraMap L _ x :=
  tensorMap_tmul L v a x

@[simp] theorem tensorEquiv_one_tmul (x : L) :
    tensorEquiv L v (1 ⊗ₜ x) = algebraMap L (CompletionsOver L v) x := by
  simp

def tensorMap' : L ⊗[K] v.adicCompletion K →ₐ[L] CompletionsOver L v :=
  Algebra.TensorProduct.lift (Algebra.ofId L _)
    (IsScalarTower.toAlgHom K (v.adicCompletion K) _) (fun _ _ ↦ Commute.all _ _)

@[simp] theorem tensorMap'_tmul (x : L) (a : v.adicCompletion K) :
    tensorMap' L v (x ⊗ₜ a) =
      algebraMap L (CompletionsOver L v) x * algebraMap (v.adicCompletion K) _ a := by
  simp [tensorMap']

theorem tensorMap'_eq_comp :
    ⇑(tensorMap' L v) = tensorEquiv L v ∘ Algebra.TensorProduct.comm K L (v.adicCompletion K) := by
  have : (tensorMap' L v).restrictScalars K =
      ((tensorEquiv L v).toAlgHom.restrictScalars K).comp
        (Algebra.TensorProduct.comm K L (v.adicCompletion K)).toAlgHom :=
    Algebra.TensorProduct.ext' fun x a ↦ by simp [mul_comm]
  exact congrArg DFunLike.coe this

def tensorEquiv' : L ⊗[K] v.adicCompletion K ≃ₐ[L] CompletionsOver L v :=
  AlgEquiv.ofBijective (tensorMap' L v) (by
    rw [tensorMap'_eq_comp]
    exact (tensorEquiv L v).bijective.comp (AlgEquiv.bijective _))

@[simp] theorem tensorEquiv'_tmul (x : L) (a : v.adicCompletion K) :
    tensorEquiv' L v (x ⊗ₜ a) =
      algebraMap L (CompletionsOver L v) x * algebraMap (v.adicCompletion K) _ a :=
  tensorMap'_tmul L v x a

theorem tensorEquiv'_tmul_mul (a : v.adicCompletion K) (y : L ⊗[K] v.adicCompletion K) :
    tensorEquiv' L v ((1 ⊗ₜ a) * y) =
      algebraMap (v.adicCompletion K) (CompletionsOver L v) a * tensorEquiv' L v y := by
  rw [map_mul, tensorEquiv'_tmul, map_one, one_mul]


open scoped Valued in
instance isModuleTopology_completionsOver :
    IsModuleTopology (v.adicCompletion K) (CompletionsOver L v) :=
  isModuleTopologyOfFiniteDimensional (𝕜 := v.adicCompletion K)

end SemiLocal

end

end GroundTheory.Global
