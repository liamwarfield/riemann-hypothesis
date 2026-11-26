module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLabelAtUnfolding

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfIsIntegralConj
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LocIntSpan

theorem exists_finset_algebraMap_mem (s : Finset ℚ) :
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ q ∈ s,
      algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ := by
  let d : ℤ := ∏ q ∈ s, (q.den : ℤ)
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.2 fun q _ => by exact_mod_cast q.den_nz
  have hfin : {v : HeightOneSpectrum ℤ | v.asIdeal ∣ Ideal.span {d}}.Finite :=
    Ideal.finite_factors (by simpa [Ideal.span_singleton_eq_bot] using hd)
  refine ⟨hfin.toFinset, fun v hv q hq => ?_⟩
  have hden : (q.den : ℤ) ∉ v.asIdeal := by
    intro h
    apply hv
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ hq) h
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have e : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) = v.valuation ℚ q :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v q
  rw [e]
  have hq' : q = ((q.num : ℤ) : ℚ) / ((q.den : ℤ) : ℚ) := by
    push_cast; exact (Rat.num_div_den q).symm
  rw [hq', map_div₀]
  have h1 : v.valuation ℚ ((q.num : ℤ) : ℚ) ≤ 1 := by
    rw [show ((q.num : ℤ) : ℚ) = algebraMap ℤ ℚ q.num from rfl, HeightOneSpectrum.valuation_of_algebraMap]
    exact v.intValuation_le_one _
  have h2 : v.valuation ℚ ((q.den : ℤ) : ℚ) = 1 := by
    rw [show ((q.den : ℤ) : ℚ) = algebraMap ℤ ℚ q.den from rfl, HeightOneSpectrum.valuation_of_algebraMap]
    exact le_antisymm (v.intValuation_le_one _)
      (not_lt.1 fun h => hden ((v.intValuation_lt_one_iff_mem _).1 h))
  rw [h2, div_one]
  exact h1

theorem isIntegral_of_isIntegral_conj {R A : Type} [CommRing R] [Ring A] [Algebra R A] (X : Aˣ) (y : A)
    (h : IsIntegral R (↑X * y * ↑X⁻¹)) : IsIntegral R y := by
  let f : A →ₐ[R] A :=
    { toFun := fun z => ↑X⁻¹ * z * ↑X
      map_one' := by simp
      map_mul' := fun a b => by simp [mul_assoc]
      map_zero' := by simp
      map_add' := fun a b => by simp [mul_add, add_mul]
      commutes' := fun r => by
        show _ * _ * _ = _
        rw [mul_assoc, Algebra.commutes, Units.inv_mul_cancel_left] }
  have := h.map f
  simpa [f, mul_assoc] using this

theorem map_id_injective (K : Type) [CommRing K] [Algebra ℚ K] {L C : Type} [Ring L] [Algebra ℚ L] [Ring C]
    [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (hι : Function.Injective ι) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id ℚ K) ι) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := K) ι.toLinearMap hι

theorem mem_of_isIntegral (v : HeightOneSpectrum ℤ) {x : v.adicCompletion ℚ}
    (hx : IsIntegral (v.adicCompletionIntegers ℚ) x) : x ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx
  exact y.2

theorem trace_one_tmul' {F E : Type} [Field F] [Field E] [Algebra F E] [Module.Finite F E]
    (R : Type) [CommRing R] [Algebra F R] (e : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

end GlobalTheory.LocIntSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatedTensorIntegrality
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetAdicIntegralTensorBasisOneMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetAdicIntegralTensorBasisOneMul
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan

theorem isIntB_one_mul_cofinite : ∀ (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (κ : Type) (b : Module.Basis κ ℚ C),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      IsIntB v b 1 ∧ ∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z) :=
  isIntB_one_mul_eventually

end GlobalTheory.AdicSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetAdicIntegralTensorBasisOneMulStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_adicIntegralTensorBasis_one_mul : ∀ (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (κ : Type) (b : Module.Basis κ ℚ C),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      IsIntB v b 1 ∧ ∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z) := by
  first | (exact @GlobalTheory.AdicSpan.isIntB_one_mul_cofinite) | (exact GlobalTheory.AdicSpan.isIntB_one_mul_cofinite) | (intros; apply GlobalTheory.AdicSpan.isIntB_one_mul_cofinite  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfAdicIntegralTensorBasisRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfAdicIntegralTensorBasisRing
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory.AdicSpan

theorem isIntegral_of_isIntB : ∀ (v : HeightOneSpectrum ℤ) (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (κ : Type)
    (b : Module.Basis κ ℚ C), IsIntB v b 1 → (∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z)) →
      ∀ y, IsIntB v b y → IsIntegral (v.adicCompletionIntegers ℚ) y := by
  intro v C _ _ _ κ b h1 hmul y hy
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  set e := Algebra.TensorProduct.basis (v.adicCompletion ℚ) b with he
  have hsmul : ∀ (a : v.adicCompletionIntegers ℚ) (x : v.adicCompletion ℚ ⊗[ℚ] C),
      a • x = (a : v.adicCompletion ℚ) • x := fun a x => (algebraMap_smul (v.adicCompletion ℚ) a x).symm
  have hadd : ∀ x z, IsIntB v b x → IsIntB v b z → IsIntB v b (x + z) := fun x z hx hz i => by
    rw [map_add (f := _), Finsupp.add_apply]; exact add_mem (hx i) (hz i)
  let S : Subalgebra (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ ⊗[ℚ] C) :=
    { carrier := {x | IsIntB v b x}
      mul_mem' := fun {x z} hx hz => hmul x z hx hz
      one_mem' := h1
      add_mem' := fun {x z} hx hz => hadd x z hx hz
      zero_mem' := isIntB_zero v b
      algebraMap_mem' := fun a => by
        show IsIntB v b (algebraMap _ _ a)
        rw [Algebra.algebraMap_eq_smul_one, hsmul]
        intro i
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
        exact mul_mem a.2 (h1 i) }
  have hS : Subalgebra.toSubmodule S = Submodule.span (v.adicCompletionIntegers ℚ)
      (Set.range fun i => (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] b i) := by
    apply le_antisymm
    · intro x hx
      rw [← e.sum_repr x]
      refine Submodule.sum_mem _ fun i _ => ?_
      obtain ⟨c, hc⟩ : ∃ c : v.adicCompletionIntegers ℚ, (c : v.adicCompletion ℚ) = e.repr x i :=
        ⟨⟨_, hx i⟩, rfl⟩
      rw [← hc, ← hsmul, he, Algebra.TensorProduct.basis_apply]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact isIntB_tmul_basis v b j
  refine IsIntegral.of_mem_of_fg S ?_ y hy
  rw [hS]
  exact Submodule.fg_span (Set.finite_range _)

end GlobalTheory.AdicSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfAdicIntegralTensorBasisRingStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_of_adicIntegralTensorBasis_ring : ∀ (v : HeightOneSpectrum ℤ) (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (κ : Type)
    (b : Module.Basis κ ℚ C), IsIntB v b 1 → (∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z)) →
      ∀ y, IsIntB v b y → IsIntegral (v.adicCompletionIntegers ℚ) y := by
  first | (exact @GlobalTheory.AdicSpan.isIntegral_of_isIntB) | (exact GlobalTheory.AdicSpan.isIntegral_of_isIntB) | (intros; apply GlobalTheory.AdicSpan.isIntegral_of_isIntB  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisOfTraceMemEventually
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisOfTraceMemEventually
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LocIntSpan

theorem isIntB_of_trace_mem :
    ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (bL : Module.Basis κ ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ E : v.adicCompletion ℚ ⊗[ℚ] L,
      (∀ i, Algebra.trace (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L)
          (E * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] bL i)) ∈ v.adicCompletionIntegers ℚ) →
        IsIntB v bL E := by
  intro L _ _ κ bL
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex bL
  have hd : Algebra.discr ℚ bL ≠ 0 := Algebra.discr_not_zero_of_basis ℚ bL
  obtain ⟨S, hS⟩ := exists_finset_algebraMap_mem
    (insert (Algebra.discr ℚ bL)⁻¹
      (Finset.univ.image fun p : κ × κ => Algebra.trace ℚ L (bL p.1 * bL p.2)))
  refine ⟨S, fun v hv E hE => ?_⟩
  set Q := v.adicCompletion ℚ
  let B := Algebra.TensorProduct.basis Q bL
  have hB : ∀ i, B i = (1 : Q) ⊗ₜ[ℚ] bL i := fun i => by
    simp [B, Algebra.TensorProduct.basis_apply]
  have htr : ∀ i j, Algebra.trace Q (Q ⊗[ℚ] L) (B i * B j) =
      algebraMap ℚ Q (Algebra.trace ℚ L (bL i * bL j)) := fun i j => by
    rw [hB, hB, Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_one_tmul']
  have hTM : Algebra.traceMatrix Q B = (algebraMap ℚ Q).mapMatrix (Algebra.traceMatrix ℚ bL) := by
    refine Matrix.ext fun i j => ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, Algebra.traceForm_apply]
    exact htr i j
  have hdet : (Algebra.traceMatrix Q B).det = algebraMap ℚ Q (Algebra.discr ℚ bL) := by
    rw [hTM, ← RingHom.map_det, Algebra.discr_def]
  have hG : ∀ i j, ∃ u : v.adicCompletionIntegers ℚ, algebraMap (v.adicCompletionIntegers ℚ) Q u =
      Algebra.trace Q (Q ⊗[ℚ] L) (B i * B j) := fun i j =>
    ⟨⟨_, hS v hv _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩))⟩,
      (htr i j).symm⟩
  have hω : ∀ i, ∃ u : v.adicCompletionIntegers ℚ, algebraMap (v.adicCompletionIntegers ℚ) Q u =
      Algebra.trace Q (Q ⊗[ℚ] L) (E * B i) := fun i => ⟨⟨_, by rw [hB]; exact hE i⟩, rfl⟩
  obtain ⟨u, hu⟩ := GlobalTheory.DiscConductor.det_smul_eq_sum (v.adicCompletionIntegers ℚ) Q (Q ⊗[ℚ] L) κ B E hG hω
  intro j
  have hrep : B.repr E j = (algebraMap ℚ Q (Algebra.discr ℚ bL))⁻¹ *
      algebraMap (v.adicCompletionIntegers ℚ) Q (u j) := by
    have h1 := congrArg (fun x => B.repr x j) hu
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_sum, Finset.sum_apply', Module.Basis.repr_self, Finsupp.single_apply, hdet] at h1
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)] at h1
    simp only [if_true, mul_one] at h1
    have hne : algebraMap ℚ Q (Algebra.discr ℚ bL) ≠ 0 := (map_ne_zero _).2 hd
    rw [← h1, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  show B.repr E j ∈ v.adicCompletionIntegers ℚ
  rw [hrep, ← map_inv₀]
  exact mul_mem (hS v hv _ (Finset.mem_insert_self _ _)) (u j).2

end GlobalTheory.LocIntSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisOfTraceMemEventuallyStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicIntegralTensorBasis_of_trace_mem_eventually : ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (bL : Module.Basis κ ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ E : v.adicCompletion ℚ ⊗[ℚ] L,
      (∀ i, Algebra.trace (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L)
          (E * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] bL i)) ∈ v.adicCompletionIntegers ℚ) →
        IsIntB v bL E := by
  first | (exact @GlobalTheory.LocIntSpan.isIntB_of_trace_mem) | (exact GlobalTheory.LocIntSpan.isIntB_of_trace_mem) | (intros; apply GlobalTheory.LocIntSpan.isIntB_of_trace_mem  <;> assumption)
end
end

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.LocIntSpan

theorem isIntB_of_isIntB_conj : ∀ (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (L : Type) [Field L] [NumberField L]
    (ι : L →ₐ[ℚ] C), Function.Injective ι → ∀ (κ : Type) (b : Module.Basis κ ℚ C) (κ' : Type)
    (bL : Module.Basis κ' ℚ L), ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      ∀ (X : (v.adicCompletion ℚ ⊗[ℚ] C)ˣ) (E : v.adicCompletion ℚ ⊗[ℚ] L),
        IsIntB v b (↑X * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι E * ↑X⁻¹) →
        IsIntB v bL E := by
  intro C _ _ _ L _ _ ι hι κ b κ' bL
  obtain ⟨S₁, h₁⟩ := GlobalTheory.T.exists_finset_adicIntegralTensorBasis_one_mul C κ b
  obtain ⟨S₂, h₂⟩ := GlobalTheory.T.exists_finset_adicIntegralTensorBasis_one_mul L κ' bL
  obtain ⟨S₃, h₃⟩ := GlobalTheory.T.adicIntegralTensorBasis_of_trace_mem_eventually L κ' bL
  refine ⟨S₁ ∪ S₂ ∪ S₃, fun v hv X E hE => ?_⟩
  simp only [Finset.mem_union, not_or] at hv
  obtain ⟨⟨hv1, hv2⟩, hv3⟩ := hv
  have hint := GlobalTheory.T.isIntegral_of_adicIntegralTensorBasis_ring v C κ b (h₁ v hv1).1 (h₁ v hv1).2 _ hE
  have hE' := isIntegral_of_isIntegral_conj X _ hint
  let F : v.adicCompletion ℚ ⊗[ℚ] L →ₐ[v.adicCompletion ℚ] v.adicCompletion ℚ ⊗[ℚ] C :=
    Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion ℚ) (v.adicCompletion ℚ)) ι
  have hF : ∀ x, F x = Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι x := fun x => rfl
  have hinj : Function.Injective (F.restrictScalars (v.adicCompletionIntegers ℚ)) := by
    intro x y hxy
    exact map_id_injective (v.adicCompletion ℚ) ι hι (by simpa [hF] using hxy)
  have hE'' : IsIntegral (v.adicCompletionIntegers ℚ) E :=
    (isIntegral_algHom_iff (F.restrictScalars (v.adicCompletionIntegers ℚ)) hinj).1 (by simpa [hF] using hE')
  refine h₃ v hv3 E fun i => mem_of_isIntegral v ?_
  have hb : IsIntegral (v.adicCompletionIntegers ℚ) ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] bL i) :=
    GlobalTheory.T.isIntegral_of_adicIntegralTensorBasis_ring v L κ' bL (h₂ v hv2).1 (h₂ v hv2).2 _ (isIntB_tmul_basis v bL i)
  exact GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral _ _ _ _ (hE''.mul hb)

end GlobalTheory.LocIntSpan
end
end

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.almost_all_places_twisted_unit_integral : ∀ (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (L : Type) [Field L] [NumberField L]
    (ι : L →ₐ[ℚ] C), Function.Injective ι → ∀ (κ : Type) (b : Module.Basis κ ℚ C) (κ' : Type)
    (bL : Module.Basis κ' ℚ L), ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      ∀ (X : (v.adicCompletion ℚ ⊗[ℚ] C)ˣ) (E : v.adicCompletion ℚ ⊗[ℚ] L),
        IsIntB v b (↑X * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι E * ↑X⁻¹) →
        IsIntB v bL E := by
  first | (exact @GlobalTheory.LocIntSpan.isIntB_of_isIntB_conj) | (exact GlobalTheory.LocIntSpan.isIntB_of_isIntB_conj) | (intros; apply GlobalTheory.LocIntSpan.isIntB_of_isIntB_conj  <;> assumption)
