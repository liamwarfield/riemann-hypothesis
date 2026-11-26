module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.KernelLatticeBaseChange
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XGraphRestrictBc
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubAndQuotientBundles

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentGeneratorDualIntegral
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentGeneratorDualIntegral
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField
open scoped nonZeroDivisors

section

variable (E : Type) [Field E] [NumberField E]

theorem mem_dual_one_iff_span_dualInt (y : E) :
    y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔
      y ∈ Submodule.span ℤ (Set.range (dualInt E)) := by
  classical
  have h := Submodule.traceDual_span_of_basis ℤ (1 : Submodule (𝓞 E) E) (integralBasis E) (by
    ext x
    rw [Submodule.restrictScalars_mem, mem_span_integralBasis, Submodule.mem_one]
    rfl)
  have h2 : y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔
      y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_dual_one]
  rw [h2, ← Submodule.restrictScalars_mem ℤ, h]
  have : (⇑(integralBasis E).traceDual) = dualInt E := by
    funext k
    unfold dualInt Module.Basis.traceDual
    congr!
  rw [this]

theorem different_mul_dual_one :
    ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) *
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) = 1 := by
  rw [coeIdeal_differentIdeal ℤ ℚ, inv_mul_cancel₀
    (FractionalIdeal.dual_ne_zero ℤ ℚ (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E)))]

theorem exists_different_mul_dualInt (x : 𝓞 E) (hx : x ∈ differentIdeal ℤ (𝓞 E))
    (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    ∃ z : 𝓞 E, (z : E) = (x : E) * dualInt E k := by
  have h1 : dualInt E k ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) :=
    (mem_dual_one_iff_span_dualInt E _).2 (Submodule.subset_span ⟨k, rfl⟩)
  have h2 : (x : E) ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) :=
    FractionalIdeal.mem_coeIdeal_of_mem _ hx
  have h3 := FractionalIdeal.mul_mem_mul h2 h1
  rw [different_mul_dual_one, FractionalIdeal.mem_one_iff] at h3
  exact h3

end

theorem different_generator_dualInt :
    ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (E : Type) [Field E]
      [NumberField E] (σ : E →+* K) (d : A), Function.Injective (algebraMap A K) →
      (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) →
      Submodule.span A {algebraMap A K d} =
        Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)} →
      algebraMap A K d ≠ 0 ∧
        (∀ k, algebraMap A K d * σ (dualInt E k) ∈ (algebraMap A K).range) ∧
        ∃ u : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A,
          ∑ k, algebraMap A K (u k) * (algebraMap A K d * σ (dualInt E k)) = 1 := by
  intro A K _ _ _ _ E _ _ σ d _ hσ hd
  have key : ∃ u : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A,
      ∑ k, algebraMap A K (u k) * (algebraMap A K d * σ (dualInt E k)) = 1 := by
    set M : Submodule A K :=
      Submodule.span A (Set.range fun k => algebraMap A K d * σ (dualInt E k)) with hM
    have hy : ∀ y ∈ Submodule.span ℤ (Set.range (dualInt E)), algebraMap A K d * σ y ∈ M := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        exact Submodule.subset_span ⟨k, rfl⟩
      | zero => simp
      | add a b _ _ ha hb => rw [map_add (f := _), mul_add]; exact M.add_mem ha hb
      | smul n a _ ha =>
        rw [map_zsmul, mul_smul_comm]
        exact zsmul_mem ha n
    have h1 : (1 : E) ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) *
        FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
      rw [different_mul_dual_one]
      exact FractionalIdeal.one_mem_one _
    have h2 : σ 1 ∈ M := by
      refine FractionalIdeal.mul_induction_on (C := fun z => σ z ∈ M) h1 ?_ ?_
      · intro x hx y hy'
        obtain ⟨x, hx0, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
        have hx' : σ (x : E) ∈ Submodule.span A {algebraMap A K d} := by
          rw [hd]; exact Submodule.subset_span ⟨x, hx0, rfl⟩
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hx'
        change σ ((x : E) * y) ∈ M
        rw [map_mul, ← ha, smul_mul_assoc]
        exact M.smul_mem a (hy y ((mem_dual_one_iff_span_dualInt E y).1 hy'))
      · intro x y hx hy
        rw [map_add (f := _)]; exact M.add_mem hx hy
    rw [map_one, hM, Submodule.mem_span_range_iff_exists_fun] at h2
    obtain ⟨u, hu⟩ := h2
    exact ⟨u, by simpa only [Algebra.smul_def] using hu⟩
  refine ⟨?_, ?_, key⟩
  · intro h0
    obtain ⟨u, hu⟩ := key
    simp [h0] at hu
  · intro k
    have hy : ∀ y ∈ Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)},
        y * σ (dualInt E k) ∈ (algebraMap A K).range := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, hx, rfl⟩ := hy
        obtain ⟨z, hz⟩ := exists_different_mul_dualInt E x hx k
        rw [← map_mul, ← hz]
        exact hσ z
      | zero => simp
      | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
      | smul n a _ ha =>
        rw [smul_mul_assoc, Algebra.smul_def]
        exact mul_mem ⟨n, rfl⟩ ha
    exact hy _ (hd ▸ Submodule.mem_span_singleton_self _)

end GlobalTheory.CompanionTheory.Ar.HT
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentGeneratorDualIntegralStatement
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.different_generator_dual_integral : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (E : Type) [Field E] [NumberField E] (σ : E →+* K) (d : A), Function.Injective (algebraMap A K) → (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → Submodule.span A {algebraMap A K d} = Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)} → algebraMap A K d ≠ 0 ∧ (∀ k, algebraMap A K d * σ (dualInt E k) ∈ (algebraMap A K).range) ∧ ∃ u : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A, ∑ k, algebraMap A K (u k) * (algebraMap A K d * σ (dualInt E k)) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.different_generator_dualInt | exact GlobalTheory.CompanionTheory.Ar.HT.different_generator_dualInt | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.different_generator_dualInt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RelatedPairsOrbitalTermEq
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.ProjEig

open Module NumberField

section

variable {E : Type} [Field E] [NumberField E]

theorem trace_dualInt_mul (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (x : E) :
    Algebra.trace ℚ E (dualInt E k * x) = (integralBasis E).repr x k := by
  classical
  have h : ∀ l, Algebra.trace ℚ E (dualInt E k * integralBasis E l) = if l = k then 1 else 0 := by
    intro l
    have := LinearMap.BilinForm.apply_dualBasis_left (B := Algebra.traceForm ℚ E)
      (traceForm_nondegenerate ℚ E) (integralBasis E) k l
    rw [Algebra.traceForm_apply] at this
    unfold dualInt
    convert this
  conv_lhs => rw [← (integralBasis E).sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, h]
  simp

theorem mul_dualInt_eq (a : 𝓞 E) (l : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    (a : E) * dualInt E l =
      ∑ k, (((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E k) l : ℤ) : E) *
        dualInt E k := by
  classical
  have h := ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E)
    (integralBasis E)).sum_repr ((a : E) * dualInt E l)
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, mul_comm (a : E),
    mul_assoc, trace_dualInt_mul, integralBasis_apply]
  have : (a : E) * algebraMap (𝓞 E) E (RingOfIntegers.basis E k)
      = algebraMap (𝓞 E) E (a * RingOfIntegers.basis E k) := by simp
  rw [this, integralBasis_repr_apply, Algebra.smul_def]
  simp [dualInt]

theorem sum_dualInt_mul :
    ∑ k, dualInt E k * ((RingOfIntegers.basis E k : 𝓞 E) : E) = 1 := by
  classical
  rw [← sub_eq_zero]
  refine (traceForm_nondegenerate ℚ E).1 _ fun y => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Algebra.traceForm_apply, sub_mul, map_sub, one_mul, Finset.sum_mul, map_sum,
    Algebra.trace_eq_matrix_trace (integralBasis E) y, sub_eq_zero, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_assoc, trace_dualInt_mul, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
    integralBasis_apply, mul_comm y]

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem mem_eigSp_iff_apply (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) (x : V) :
    x ∈ eigSp ρ σ ↔ ∀ a : 𝓞 E, ρ a x = σ (a : E) • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem rho_mul_eigProj (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) (a : 𝓞 E) :
    ρ a * eigProj ρ σ = σ (a : E) • eigProj ρ σ := by
  classical
  unfold eigProj
  rw [Finset.mul_sum, Finset.smul_sum]
  have h1 : ∀ k, ρ a * (σ (dualInt E k) • ρ (RingOfIntegers.basis E k)) =
      ∑ l, (σ (dualInt E k) *
        (((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E k) l : ℤ) : K)) •
          ρ (RingOfIntegers.basis E l) := by
    intro k
    rw [mul_smul_comm, ← map_mul]
    conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr (a * RingOfIntegers.basis E k)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_zsmul, mul_smul, Int.cast_smul_eq_zsmul]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [smul_smul, ← map_mul, mul_dualInt_eq, map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul σ, map_intCast, mul_comm]

theorem eigProj_mul_rho_comm (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) (a : 𝓞 E) :
    eigProj ρ σ * ρ a = ρ a * eigProj ρ σ := by
  unfold eigProj
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← map_mul, ← map_mul, mul_comm]

end

theorem eigProj_spec : ∀ (K : Type) [Field K] [CharZero K] (V : Type) [AddCommGroup V] [Module K V]
    (E : Type) [Field E] [NumberField E] (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K),
    (∀ x, eigProj ρ σ x ∈ eigSp ρ σ) ∧ (∀ x ∈ eigSp ρ σ, eigProj ρ σ x = x) ∧
    (∀ σ' : E →+* K, σ' ≠ σ → ∀ x ∈ eigSp ρ σ', eigProj ρ σ x = 0) ∧
    ∀ a : 𝓞 E, eigProj ρ σ * ρ a = ρ a * eigProj ρ σ := by
  intro K _ _ V _ _ E _ _ ρ σ
  refine ⟨fun x => ?_, fun x hx => ?_, fun σ' hσ x hx => ?_, eigProj_mul_rho_comm ρ σ⟩
  · rw [mem_eigSp_iff_apply]
    intro a
    rw [← Module.End.mul_apply, rho_mul_eigProj, LinearMap.smul_apply]
  · rw [mem_eigSp_iff_apply] at hx
    unfold eigProj
    rw [LinearMap.sum_apply]
    simp_rw [LinearMap.smul_apply, hx, smul_smul, ← map_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_smul, ← map_sum, sum_dualInt_mul, map_one, one_smul]
  · rw [mem_eigSp_iff_apply] at hx
    obtain ⟨a, ha⟩ : ∃ a : 𝓞 E, σ' (a : E) ≠ σ (a : E) := by
      by_contra hcon
      push Not at hcon
      exact hσ (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext hcon))
    have h1 : eigProj ρ σ (ρ a x) = ρ a (eigProj ρ σ x) := by
      rw [← Module.End.mul_apply, eigProj_mul_rho_comm, Module.End.mul_apply]
    rw [← Module.End.mul_apply (ρ a), rho_mul_eigProj, LinearMap.smul_apply, hx, map_smul,
      ← sub_eq_zero, ← sub_smul, smul_eq_zero] at h1
    exact h1.resolve_left (sub_ne_zero.mpr ha)

end GlobalTheory.CompanionTheory.Ar.HT.ProjEig
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjSumSumEmbeddingsEqTrace
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

theorem projSum_sum_embeddings_eq_trace (K : Type) [Field K] [CharZero K] (E : Type) [Field E]
    [NumberField E] [Fintype (E →+* K)] (h : Fintype.card (E →+* K) = Module.finrank ℚ E) (y : E) :
    ∑ σ : E →+* K, σ y = ((Algebra.trace ℚ E y : ℚ) : K) := by
  classical
  let L := AlgebraicClosure K
  let f : (E →+* K) → (E →ₐ[ℚ] L) := fun σ => ((algebraMap K L).comp σ).toRatAlgHom
  have hinj : Function.Injective f := by
    intro σ τ hst
    ext x
    apply (algebraMap K L).injective
    have := DFunLike.congr_fun hst x
    simpa [f] using this
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [h, AlgHom.card]
  apply (algebraMap K L).injective
  have ht := trace_eq_sum_embeddings L (K := ℚ) (L := E) (x := y)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_ratCast, ← eq_ratCast (algebraMap ℚ L), ht]
  exact Fintype.sum_bijective f hbij _ _ (fun σ => by simp [f])

theorem projSum_trace_dualInt (E : Type) [Field E] [NumberField E]
    (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    Algebra.trace ℚ E (dualInt E k) = (((RingOfIntegers.basis E).repr 1 k : ℤ) : ℚ) := by
  classical
  have h1 : (1 : E) = ∑ j, (((RingOfIntegers.basis E).repr 1 j : ℤ) : ℚ) • integralBasis E j := by
    have := congrArg (algebraMap (𝓞 E) E) ((RingOfIntegers.basis E).sum_repr 1)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, (algebraMap (𝓞 E) E).map_one] at this
    refine this.symm.trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integralBasis_apply, map_zsmul, Int.cast_smul_eq_zsmul]
  have h2 : Algebra.trace ℚ E (dualInt E k) = Algebra.traceForm ℚ E (dualInt E k) 1 := by
    rw [Algebra.traceForm_apply, mul_one]
  rw [h2]
  conv_lhs => rw [h1]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, dualInt, LinearMap.BilinForm.apply_dualBasis_left]
  simp

theorem sum_eigProj_eq_one (K : Type) [Field K] [CharZero K] (V : Type) [AddCommGroup V]
    [Module K V] (E : Type) [Field E] [NumberField E] (ρ : 𝓞 E →+* Module.End K V)
    [Fintype (E →+* K)] (h : Fintype.card (E →+* K) = Module.finrank ℚ E) :
    ∑ σ : E →+* K, eigProj ρ σ = 1 := by
  classical
  unfold eigProj
  rw [Finset.sum_comm]
  have := congrArg ρ ((RingOfIntegers.basis E).sum_repr 1)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ρ.map_one] at this
  refine Eq.trans ?_ this
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_smul, projSum_sum_embeddings_eq_trace K E h, projSum_trace_dualInt,
    Rat.cast_intCast, map_zsmul, Int.cast_smul_eq_zsmul]

end GlobalTheory.CompanionTheory.Ar.HT
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UltrametricDetNormLe
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UltrametricDetNormLe
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem norm_det_le_pow_card_of_ultrametric :
    ∀ (A : Type) [NormedField A] [IsUltrametricDist A] (I : Type) [Fintype I] [DecidableEq I]
      (M : Matrix I I A) (r : ℝ), 0 ≤ r → (∀ a b, ‖M a b‖ ≤ r) →
      ‖M.det‖ ≤ r ^ Fintype.card I := by
  intro A _ _ I _ _ M r hr hM
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hr _) ?_
  intro σ _
  rw [Units.smul_def, zsmul_eq_mul, norm_mul]
  have h1 : ‖(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A)‖ ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have h2 : ‖∏ i, M (σ i) i‖ ≤ r ^ Fintype.card I := by
    rw [norm_prod]
    calc ∏ i, ‖M (σ i) i‖ ≤ ∏ _i : I, r :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hM _ _)
      _ = r ^ Fintype.card I := by simp
  calc _ ≤ 1 * r ^ Fintype.card I :=
        mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end GlobalTheory.CompanionTheory.Ar.Fl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UltrametricDetNormLeStatement
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ultrametric_det_norm_le : ∀ (A : Type) [NormedField A] [IsUltrametricDist A] (I : Type) [Fintype I] [DecidableEq I] (M : Matrix I I A) (r : ℝ), 0 ≤ r → (∀ a b, ‖M a b‖ ≤ r) → ‖M.det‖ ≤ r ^ Fintype.card I := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.norm_det_le_pow_card_of_ultrametric | exact GlobalTheory.CompanionTheory.Ar.Fl.norm_det_le_pow_card_of_ultrametric | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.norm_det_le_pow_card_of_ultrametric <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsDiffGenerator
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

theorem diffGen_v_le_one {C : Type} [Field C] (v : Valuation C NNReal)
    {E : Type} [Field E] [NumberField E] (σ : E →+* C) (a : 𝓞 E) : v (σ (a : E)) ≤ 1 := by
  have h1 : IsIntegral ℤ (σ (a : E)) := (RingOfIntegers.isIntegral_coe a).map σ.toIntAlgHom
  have h2 : IsIntegral v.integer (σ (a : E)) := h1.tower_top
  exact (Valuation.integer.integers v).mem_of_integral h2

theorem diffGen_exists_max {C : Type} [Field C] (v : Valuation C NNReal)
    {E : Type} [Field E] [NumberField E] (σ : E →+* C) (D : Ideal (𝓞 E)) :
    ∃ x₀ ∈ D, ∀ x ∈ D, v (σ ((x : 𝓞 E) : E)) ≤ v (σ ((x₀ : 𝓞 E) : E)) := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian D : D.FG)
  rcases s.eq_empty_or_nonempty with h | h
  · refine ⟨0, D.zero_mem, fun x hx => ?_⟩
    rw [← hs, h, Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at hx
    simp [hx]
  · obtain ⟨x₀, hx₀s, hmax⟩ := s.exists_max_image (fun g : 𝓞 E => v (σ (g : E))) h
    refine ⟨x₀, ?_, fun x hx => ?_⟩
    · rw [← hs]
      exact Submodule.subset_span hx₀s
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hmax y hy
    | zero => simp
    | add y z _ _ hy hz =>
      calc v (σ ((y + z : 𝓞 E) : E)) = v (σ (y : E) + σ (z : E)) := by simp
        _ ≤ max (v (σ (y : E))) (v (σ (z : E))) := v.map_add _ _
        _ ≤ _ := max_le hy hz
    | smul r y _ hy =>
      calc v (σ ((r • y : 𝓞 E) : E)) = v (σ (r : E)) * v (σ (y : E)) := by simp [smul_eq_mul]
        _ ≤ 1 * v (σ (x₀ : E)) := mul_le_mul' (diffGen_v_le_one v σ r) hy
        _ = _ := one_mul _

theorem exists_diff_generator (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O]
    [Algebra O C] (hv : v.Integers O) [CharZero C] (E : Type) [Field E] [NumberField E]
    (σ : E →+* C) :
    (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap O C).range) ∧
      ∃ d : O, algebraMap O C d ≠ 0 ∧ v (algebraMap O C d) = diffAbs v σ ∧
        Submodule.span O {algebraMap O C d} =
          Submodule.span O {y : C | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)} := by
  have hint : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap O C).range := by
    intro a
    have h1 : IsIntegral ℤ (σ (a : E)) := (a.isIntegral_coe).map σ.toIntAlgHom
    have h3 : σ (a : E) ∈ v.integer := hv.mem_of_integral (h1.tower_top (A := O))
    exact RingHom.mem_range.2 (hv.exists_of_le_one ((Valuation.mem_integer_iff v _).1 h3))
  refine ⟨hint, ?_⟩
  obtain ⟨x₀, hx₀, hmax⟩ := diffGen_exists_max v σ (differentIdeal ℤ (𝓞 E))
  obtain ⟨d, hd⟩ := RingHom.mem_range.1 (hint x₀)
  have hne : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hσz : σ (z : E) ≠ 0 := (map_ne_zero σ).2 (by simpa using hz0)
  have hx0ne : σ (x₀ : E) ≠ 0 := by
    intro h
    have hle := hmax z hz
    rw [h, map_zero] at hle
    exact (v.ne_zero_iff.2 hσz) (le_antisymm hle zero_le)
  refine ⟨d, by rw [hd]; exact hx0ne, ?_, ?_⟩
  · rw [hd, diffAbs]
    apply le_antisymm
    · exact le_ciSup (f := fun x : differentIdeal ℤ (𝓞 E) => v (σ ((x : 𝓞 E) : E)))
        ⟨v (σ (x₀ : E)), by rintro _ ⟨x, rfl⟩; exact hmax x x.2⟩ ⟨x₀, hx₀⟩
    · exact ciSup_le fun x => hmax x x.2
  · rw [hd]
    apply le_antisymm
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.subset_span ⟨x₀, hx₀, rfl⟩
    · rw [Submodule.span_le]
      rintro y ⟨x, hx, rfl⟩
      have hle : v (σ (x : E) / σ (x₀ : E)) ≤ 1 := by
        rw [map_div₀]
        exact div_le_one_of_le₀ (hmax x hx) zero_le
      obtain ⟨c, hc⟩ := hv.exists_of_le_one hle
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      refine ⟨c, ?_⟩
      rw [Algebra.smul_def, hc, div_mul_cancel₀ _ hx0ne]

end GlobalTheory.CompanionTheory.Ar.HT
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KernelGraphBaseChangeHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KernelGraphBaseChangeHolds
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem kernel_graph_base_change : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ, (∀ i, (D.bc RC).kk τ i = spanOver RC (bcMap Ω C _ '' D.kk τ i)) ∧ ∀ i, (D.bc RC).stepGraph τ (fun a => algebraMap Ω C (χ τ a)) i = spanOver RC (Prod.map (algebraMap Ω C) (bcMap Ω C _) '' D.stepGraph τ (χ τ) i) :=
  @PositivityTheory.Xgn.kernel_lattice_base_change

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KernelGraphBaseChangeHoldsStatement
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_graph_base_change_holds : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ, (∀ i, (D.bc RC).kk τ i = spanOver RC (bcMap Ω C _ '' D.kk τ i)) ∧ ∀ i, (D.bc RC).stepGraph τ (fun a => algebraMap Ω C (χ τ a)) i = spanOver RC (Prod.map (algebraMap Ω C) (bcMap Ω C _) '' D.stepGraph τ (χ τ) i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.kernel_graph_base_change | exact GlobalTheory.CompanionTheory.Ar.Num.kernel_graph_base_change | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.kernel_graph_base_change <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeBaseChangeQuotient
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeBaseChangeQuotient
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.GraphRestrict

theorem main : ∀ {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ {V Vc : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup Vc] [Module C Vc] [Module Ω Vc] [IsScalarTower Ω C Vc] {Z Zc : Type} [AddCommGroup Z] [Module Ω Z] [AddCommGroup Zc] [Module C Zc] [Module Ω Zc] [IsScalarTower Ω C Zc] (b : V →ₗ[Ω] Vc) (b' : Z →ₗ[Ω] Zc), IsBaseChange C b → IsBaseChange C b' → ∀ (Δ : AddSubgroup (V × Z)) (H : AddSubgroup V) (N : ℕ), (∀ a ∈ R, ∀ v ∈ Δ, a • v ∈ Δ) → LocFree R N (Δ.map (AddMonoidHom.fst V Z)) → H ≤ Δ.map (AddMonoidHom.fst V Z) → (∀ a ∈ R, ∀ v ∈ H, a • v ∈ H) → spanOver RC (Prod.map b b' '' Δ) ⊓ (spanOver RC (b '' H)).prod ⊤ = spanOver RC (Prod.map b b' '' (Δ ⊓ H.prod ⊤ : AddSubgroup (V × Z))) ∧ (spanOver RC (Prod.map b b' '' Δ)).comap (AddMonoidHom.inr Vc Zc) = spanOver RC (b' '' Δ.comap (AddMonoidHom.inr V Z)) :=
  @PositivityTheory.Xgn.t_graph_restrict_bc

end GlobalTheory.CompanionTheory.Ar.GraphRestrict
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeBaseChangeQuotientStatement
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_free_base_change_quotient : ∀ {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ {V Vc : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup Vc] [Module C Vc] [Module Ω Vc] [IsScalarTower Ω C Vc] {Z Zc : Type} [AddCommGroup Z] [Module Ω Z] [AddCommGroup Zc] [Module C Zc] [Module Ω Zc] [IsScalarTower Ω C Zc] (b : V →ₗ[Ω] Vc) (b' : Z →ₗ[Ω] Zc), IsBaseChange C b → IsBaseChange C b' → ∀ (Δ : AddSubgroup (V × Z)) (H : AddSubgroup V) (N : ℕ), (∀ a ∈ R, ∀ v ∈ Δ, a • v ∈ Δ) → LocFree R N (Δ.map (AddMonoidHom.fst V Z)) → H ≤ Δ.map (AddMonoidHom.fst V Z) → (∀ a ∈ R, ∀ v ∈ H, a • v ∈ H) → spanOver RC (Prod.map b b' '' Δ) ⊓ (spanOver RC (b '' H)).prod ⊤ = spanOver RC (Prod.map b b' '' (Δ ⊓ H.prod ⊤ : AddSubgroup (V × Z))) ∧ (spanOver RC (Prod.map b b' '' Δ)).comap (AddMonoidHom.inr Vc Zc) = spanOver RC (b' '' Δ.comap (AddMonoidHom.inr V Z)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GraphRestrict.main | exact GlobalTheory.CompanionTheory.Ar.GraphRestrict.main | (intros; apply GlobalTheory.CompanionTheory.Ar.GraphRestrict.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SumEmbeddingDualInt
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.EigDim

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.HT.LatBasic

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {E : Type} [Field E] [NumberField E]

theorem trace_eigProj [FiniteDimensional K V] (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) :
    LinearMap.trace K V (eigProj ρ σ) = (finrank K (eigSp ρ σ) : K) :=
  LinearMap.IsProj.trace (p := eigSp ρ σ)
    ⟨fun x => eigProj_mem ρ σ x, fun _ hx => eigProj_of_mem hx⟩

theorem sum_embedding_dualInt [IsAlgClosed K] [CharZero K]
    (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    ∑ σ : E →+* K, σ (dualInt E k) = (((RingOfIntegers.basis E).repr 1 k : ℤ) : K) := by
  have h1 : ∑ σ : E →+* K, σ (dualInt E k) = ∑ σ : E →ₐ[ℚ] K, σ (dualInt E k) :=
    Fintype.sum_equiv (RingHom.equivRatAlgHom E K) _ _ fun _ => rfl
  have h2 := repr_eq_trace (E := E) 1 k
  rw [h1, ← trace_eq_sum_embeddings (E := K) (K := ℚ) (L := E)]
  have h3 : ((1 : 𝓞 E) : E) = 1 := map_one (algebraMap (𝓞 E) E)
  rw [h3, mul_one] at h2
  rw [← h2]
  simp

theorem sum_eigProj [IsAlgClosed K] [CharZero K] (ρ : 𝓞 E →+* Module.End K V) :
    ∑ σ : E →+* K, eigProj ρ σ = 1 := by
  unfold eigProj
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, sum_embedding_dualInt]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [← map_one ρ, ← (RingOfIntegers.basis E).sum_repr 1, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, Int.cast_smul_eq_zsmul]

theorem finrank_eigSp_mul :
    ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (V : Type) [AddCommGroup V] [Module K V]
      [FiniteDimensional K V] (E : Type) [Field E] [NumberField E] (ρ : 𝓞 E →+* Module.End K V),
      (∀ a : 𝓞 E, ∃ n : ℤ, LinearMap.trace K V (ρ a) = (n : K)) →
      ∀ σ : E →+* K, Module.finrank K (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) * Module.finrank ℚ E =
        Module.finrank K V := by
  intro K _ _ _ V _ _ _ E _ _ ρ htr σ
  choose m hm using fun k => htr (RingOfIntegers.basis E k)
  set l : E := ∑ k, (m k : E) * dualInt E k with hl
  have h1 : ∀ τ : E →+* K, (finrank K (eigSp ρ τ) : K) = τ l := by
    intro τ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← trace_eigProj, hl, map_sum]
    unfold eigProj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hm, map_mul, map_intCast, smul_eq_mul, mul_comm]
  have h2 : ∀ τ : E →+* K, (finrank K (eigSp ρ τ) : E) = l := fun τ =>
    τ.injective (by rw [map_natCast, h1])
  have h3 : ∀ τ : E →+* K, finrank K (eigSp ρ τ) = finrank K (eigSp ρ σ) := fun τ =>
    Nat.cast_injective ((h2 τ).trans (h2 σ).symm)
  have h4 : (finrank K V : K) = ∑ τ : E →+* K, (finrank K (eigSp ρ τ) : K) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← LinearMap.trace_one, ← sum_eigProj ρ, map_sum]
    exact Finset.sum_congr rfl fun τ _ => trace_eigProj ρ τ
  simp_rw [h3] at h4
  rw [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul] at h4
  have h5 : finrank K V = finrank ℚ E * finrank K (eigSp ρ σ) := by exact_mod_cast h4
  rw [h5, mul_comm]

end GlobalTheory.CompanionTheory.Ar.HT.EigDim
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeAdditiveSubQuotient
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeAdditiveSubQuotient
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.SubQuotDeg

theorem det_adapted {K V : Type} [Field K] [AddCommGroup V] [Module K V] (W : Submodule K V)
    {m n : ℕ} (bW cW : Module.Basis (Fin m) K W) (bQ cQ : Module.Basis (Fin n) K (V ⧸ W))
    (b c : Module.Basis (Fin (m + n)) K V)
    (hb1 : ∀ j, b (Fin.castAdd _ j) = bW j) (hb2 : ∀ j, W.mkQ (b (Fin.natAdd _ j)) = bQ j)
    (hc1 : ∀ j, c (Fin.castAdd _ j) = cW j) (hc2 : ∀ j, W.mkQ (c (Fin.natAdd _ j)) = cQ j) :
    b.det c = bW.det cW * bQ.det cQ := by
  have h1 : ∀ (i : Fin m) (x : W), b.repr (x : V) (Fin.castAdd _ i) = bW.repr x i := by
    intro i x
    have : (b.coord (Fin.castAdd _ i)).comp W.subtype = bW.coord i := by
      refine bW.ext fun j => ?_
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coord_apply,
        ← hb1, Module.Basis.repr_self, Finsupp.single_apply, Fin.castAdd_inj]
    exact LinearMap.congr_fun this x
  have h2 : ∀ (i : Fin n) (x : V), b.repr x (Fin.natAdd _ i) = bQ.repr (W.mkQ x) i := by
    intro i x
    have : b.coord (Fin.natAdd _ i) = (bQ.coord i).comp W.mkQ := by
      refine b.ext fun j => ?_
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · have h0 : W.mkQ (b (Fin.castAdd n j)) = 0 := by
          rw [hb1]; simp
        have hne : Fin.castAdd n j ≠ Fin.natAdd m i := by
          intro h
          have := congrArg Fin.val h
          simp at this
          omega
        simp only [LinearMap.comp_apply, Module.Basis.coord_apply, h0, map_zero,
          Module.Basis.repr_self, Finsupp.single_apply, hne, if_false, Finsupp.coe_zero,
          Pi.zero_apply]
      · simp only [LinearMap.comp_apply, Module.Basis.coord_apply, hb2,
          Module.Basis.repr_self, Finsupp.single_apply, Fin.natAdd_inj]
    exact LinearMap.congr_fun this x
  have key : (b.toMatrix c).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (bW.toMatrix cW)
        (Matrix.of fun i j => b.repr (c (Fin.natAdd _ j)) (Fin.castAdd _ i)) 0
        (bQ.toMatrix cQ) := by
    ext (i | i) (j | j)
    · simp [Module.Basis.toMatrix_apply, hc1, h1]
    · simp [Module.Basis.toMatrix_apply]
    · simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_right, finSumFinEquiv_apply_left,
        Module.Basis.toMatrix_apply, hc1, h2, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).2 (cW j).2]
      simp
    · simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_right,
        Module.Basis.toMatrix_apply, hc2, h2, Matrix.fromBlocks_apply₂₂]
  rw [Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.det_apply,
    ← Matrix.det_submatrix_equiv_self finSumFinEquiv, key, Matrix.det_fromBlocks_zero₂₁]

theorem deg_eq_subDeg_add_deg_quot : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type)
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V)
    (W : Submodule K V), IsBun C L → deg C L = subDeg C L W + deg C (quot C L W) := by
  intro K _ C V _ _ _ L W hL
  rcases isEmpty_or_nonempty C.I with hI | ⟨⟨i₀⟩⟩
  · simp [subDeg, deg, finsum_of_isEmpty]
  have hex := fun i => (hL.1 i).elim fun b hb => GlobalTheory.T.lattice_basis_adapted_to_subspace K C V i _ b (L i) W hb
  choose bW bQ b hb hbW hbQ h1 h2 using hex
  obtain ⟨hS, hQ⟩ := GlobalTheory.T.sub_and_quotient_bundles K C V L W hL
  obtain ⟨-, eL⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C V L _ (b i₀) b hL hb
  obtain ⟨fS, eS⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C W (sub C L W) _ (bW i₀) bW hS hbW
  obtain ⟨fQ, eQ⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C (V ⧸ W) (quot C L W) _ (bQ i₀) bQ hQ hbQ
  rw [subDeg, eL, eS, eQ, ← finsum_add_distrib]
  · refine finsum_congr fun i => ?_
    rw [det_adapted W (bW i₀) (bW i) (bQ i₀) (bQ i) (b i₀) (b i) (h1 i₀) (h2 i₀) (h1 i) (h2 i),
      map_mul, WithZero.log_mul, mul_add]
    · exact (C.v i).ne_zero_iff.2 ((bW i₀).isUnit_det (bW i)).ne_zero
    · exact (C.v i).ne_zero_iff.2 ((bQ i₀).isUnit_det (bQ i)).ne_zero
  · refine fS.subset fun i hi h => hi ?_
    simp only [h, WithZero.log_one, mul_zero]
  · refine fQ.subset fun i hi h => hi ?_
    simp only [h, WithZero.log_one, mul_zero]

end GlobalTheory.CompanionTheory.Ar.Crv.SubQuotDeg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeAdditiveSubQuotientStatement
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_additive_sub_quotient : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (W : Submodule K V), IsBun C L → deg C L = subDeg C L W + deg C (quot C L W) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.SubQuotDeg.deg_eq_subDeg_add_deg_quot | exact GlobalTheory.CompanionTheory.Ar.Crv.SubQuotDeg.deg_eq_subDeg_add_deg_quot | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.SubQuotDeg.deg_eq_subDeg_add_deg_quot <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LinearIndependentMapVec
noncomputable section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.SubFrob

variable {K : Type} [Field K]

theorem repr_semilinear {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    {σ : K →+* K} (F : V →ₛₗ[σ] V') {n : ℕ} (b : Module.Basis (Fin n) K V)
    (b' : Module.Basis (Fin n) K V') (h : ∀ j, b' j = F (b j)) (x : V) (j : Fin n) :
    b'.repr (F x) j = σ (b.repr x j) := by
  have hx : F x = ∑ k, σ (b.repr x k) • b' k := by
    conv_lhs => rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [LinearMap.map_smulₛₗ, h]
  rw [hx, b'.repr_sum_self]

theorem det_semilinear {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    {σ : K →+* K} (F : V →ₛₗ[σ] V') {n : ℕ} (b c : Module.Basis (Fin n) K V)
    (b' c' : Module.Basis (Fin n) K V') (h : ∀ j, b' j = F (b j)) (hc : ∀ j, c' j = F (c j)) :
    b'.det c' = σ (b.det c) := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det]
  congr 1
  ext i j
  simp only [Module.Basis.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, hc]
  exact repr_semilinear F b b' h _ _

theorem isLatOf_spanLat (C : ACurve K) {V V' : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] {σ : K →+* K} (F : V →ₛₗ[σ] V') {n : ℕ}
    (L : C.I → AddSubgroup V) (i : C.I) (hσ : ∀ a, C.v i a ≤ 1 → C.v i (σ a) ≤ 1)
    (b : Module.Basis (Fin n) K V) (b' : Module.Basis (Fin n) K V') (h : ∀ j, b' j = F (b j))
    (hL : IsLatOf C i b (L i)) : IsLatOf C i b' (spanLat C L F i) := by
  intro y
  constructor
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, x, ha, hx, rfl⟩ := hy
      intro q
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, repr_semilinear F b b' h]
      exact mul_le_one' ha (hσ _ ((hL x).1 hx q))
    | zero => intro q; simp
    | add x y _ _ hx hy =>
      intro q
      rw [map_add (f := _), Finsupp.add_apply]
      exact (C.v i).map_add_le (hx q) (hy q)
    | neg x _ hx =>
      intro q
      rw [map_neg, Finsupp.neg_apply, Valuation.map_neg]
      exact hx q
  · intro hy
    rw [← b'.sum_repr y]
    refine AddSubgroup.sum_mem _ fun k _ => AddSubgroup.subset_closure ⟨_, b k, hy k, ?_, by rw [h]⟩
    rw [hL]
    intro q
    rw [b.repr_self, Finsupp.single_apply]
    split_ifs <;> simp

theorem isLatOf_comap (C : ACurve K) {V : Type} [AddCommGroup V] [Module K V] (i : C.I)
    {m r : ℕ} (L : AddSubgroup V) (W : Submodule K V) (b : Module.Basis (Fin (m + r)) K V)
    (c : Module.Basis (Fin m) K W) (h : ∀ j, b (Fin.castAdd _ j) = c j) (hL : IsLatOf C i b L) :
    IsLatOf C i c (L.comap W.subtype.toAddMonoidHom) := by
  intro x
  have hx : (x : V) = ∑ k, (Fin.addCases (motive := fun _ => K) (fun j => c.repr x j) (fun _ => 0) k) • b k := by
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right, zero_smul, Finset.sum_const_zero, add_zero, h]
    have := congrArg W.subtype (c.sum_repr x)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    exact this.symm
  have hr : ∀ k, b.repr (x : V) k =
      Fin.addCases (motive := fun _ => K) (fun j => c.repr x j) (fun _ => 0) k := by
    intro k
    conv_lhs => rw [hx, b.repr_sum_self]
  rw [AddSubgroup.mem_comap]
  change (x : V) ∈ L ↔ _
  rw [hL]
  constructor
  · intro H q
    have := H (Fin.castAdd _ q)
    rwa [hr, Fin.addCases_left] at this
  · intro H q
    rw [hr]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) q
    · rw [Fin.addCases_left]; exact H j
    · rw [Fin.addCases_right]; simp

def mapVec (σ : K →+* K) (d : ℕ) : (Fin d → K) →ₛₗ[σ] (Fin d → K) where
  toFun x := fun j => σ (x j)
  map_add' x y := by ext; simp
  map_smul' a x := by ext; simp

theorem linearIndependent_mapVec (σ : K →+* K) {d n : ℕ} (v : Fin n → Fin d → K)
    (hv : LinearIndependent K v) : LinearIndependent K (fun j => mapVec σ d (v j)) := by
  have h1 : Function.Injective (Matrix.of v).vecMulLinear := by
    have := Matrix.vecMul_injective_iff.2 (show LinearIndependent K (Matrix.of v).row from hv)
    exact this
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 h1)
  set B : Matrix (Fin d) (Fin n) K := LinearMap.toMatrixRight' g with hB
  have hgB : ∀ x, g x = Matrix.vecMul x B := by
    intro x
    have : Matrix.toLinearMapRight' B = g := by
      rw [hB]; exact LinearMap.toMatrixRight'.symm_apply_apply g
    rw [← this]; rfl
  have h2 : Matrix.of v * B = 1 := by
    ext a b
    have := congrFun (LinearMap.congr_fun hg (Pi.single a 1)) b
    simp only [LinearMap.comp_apply, hgB, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul,
      LinearMap.id_apply, Matrix.single_one_vecMul] at this
    rw [Matrix.one_apply]
    change Matrix.vecMul (v a) B b = _
    simpa [Pi.single_apply, eq_comm] using this
  have h3 : (Matrix.of v).map σ * B.map σ = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one _ σ.map_zero σ.map_one]
  have h4 : LinearIndependent K ((Matrix.of v).map σ).row := by
    rw [← Matrix.vecMul_injective_iff]
    intro x y hxy
    have := congrArg (fun z => Matrix.vecMul z (B.map σ)) hxy
    simpa [Matrix.vecMul_vecMul, h3] using this
  exact h4

theorem exists_basis_top (σ : K →+* K) {d n : ℕ} (b : Module.Basis (Fin n) K (Fin d → K)) :
    ∃ b' : Module.Basis (Fin n) K (Fin d → K), ∀ j, b' j = mapVec σ d (b j) :=
  ⟨basisOfLinearIndependentOfCardEqFinrank' _ (linearIndependent_mapVec σ b b.linearIndependent)
    (Module.finrank_eq_card_basis b).symm, fun j => by simp⟩

theorem exists_basis_sub (σ : K →+* K) {d n : ℕ} (W : Submodule K (Fin d → K))
    (c : Module.Basis (Fin n) K W) :
    ∃ c' : Module.Basis (Fin n) K (Submodule.span K (mapVec σ d '' (W : Set (Fin d → K)))),
      ∀ j, (c' j : Fin d → K) = mapVec σ d (c j) := by
  have hli := linearIndependent_mapVec σ (fun j => (c j : Fin d → K))
    (c.linearIndependent.map' W.subtype W.ker_subtype)
  have hs : Submodule.span K (Set.range fun j => mapVec σ d (c j)) =
      Submodule.span K (mapVec σ d '' (W : Set (Fin d → K))) := by
    apply le_antisymm
    · apply Submodule.span_mono
      rintro _ ⟨j, rfl⟩
      exact ⟨c j, (c j).2, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have : x = ∑ k, c.repr ⟨x, hx⟩ k • (c k : Fin d → K) := by
        have := congrArg W.subtype (c.sum_repr ⟨x, hx⟩)
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum] at this
        exact this.symm
      set_option synthInstance.maxHeartbeats 100000 in
        rw [this, map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [LinearMap.map_smulₛₗ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  refine ⟨(Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hs), fun j => ?_⟩
  simp [Module.Basis.span_apply]

theorem subDeg_frob : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (W : Submodule K (Fin d → K)), IsBun C L → subDeg C (frobLat C p L) (frobSub p W) = p * subDeg C L W := by
  intro K _ C p _ _ d L W hL
  set σ := frobenius K p with hσ
  have hL' : IsBun C (frobLat C p L) := (GlobalTheory.T.frobenius_lattice_degree_mul_p K C p d L hL).1
  have hS := (GlobalTheory.T.sub_and_quotient_bundles K C _ L W hL).1
  have hS' := (GlobalTheory.T.sub_and_quotient_bundles K C _ _ (frobSub p W) hL').1
  have hv : ∀ i a, C.v i (σ a) = C.v i a ^ p := fun i a => by rw [hσ, frobenius_def, map_pow]
  have key : ∀ i, ∃ (c : Module.Basis (Fin (Module.finrank K W)) K W)
      (c' : Module.Basis (Fin (Module.finrank K W)) K (frobSub p W)),
      IsLatOf C i c (sub C L W i) ∧ IsLatOf C i c' (sub C (frobLat C p L) (frobSub p W) i) ∧
      ∀ j, (c' j : Fin d → K) = mapVec σ d (c j) := by
    intro i
    obtain ⟨b, hb⟩ := hL.1 i
    obtain ⟨c, -, b₁, hb₁, hc, -, hbc, -⟩ := GlobalTheory.T.lattice_basis_adapted_to_subspace K C _ i _ b (L i) W hb
    obtain ⟨b', hb'⟩ := exists_basis_top σ b₁
    obtain ⟨c', hc'⟩ := exists_basis_sub σ W c
    refine ⟨c, c', hc, ?_, hc'⟩
    refine isLatOf_comap C i _ _ b' c' (fun j => by rw [hb', hbc]; exact (hc' j).symm) ?_
    exact isLatOf_spanLat C (mapVec σ d) L i (fun a ha => by rw [hv]; exact pow_le_one' ha p)
      b₁ b' hb' hb₁
  choose c c' hc hc' hcc using key
  obtain ⟨e', he'⟩ : ∃ e' : Module.Basis (Fin (Module.finrank K W)) K (frobSub p W),
      ∀ j, (e' j : Fin d → K) = mapVec σ d (Module.finBasis K W j) :=
    exists_basis_sub σ W (Module.finBasis K W)
  let G : W →ₛₗ[σ] frobSub p W :=
    ((mapVec σ d).domRestrict W).codRestrict (frobSub p W)
      (fun x => Submodule.subset_span ⟨x, x.2, rfl⟩)
  obtain ⟨-, h1⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C _ _ _ (Module.finBasis K W) c hS hc
  obtain ⟨-, h2⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C _ _ _ e' c' hS' hc'
  unfold subDeg
  rw [h1, h2, mul_finsum]
  refine finsum_congr fun i => ?_
  have hd := det_semilinear G (Module.finBasis K W) (c i) e' (c' i)
    (fun j => Subtype.ext (he' j)) (fun j => Subtype.ext (hcc i j))
  rw [hd, hv, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring

end GlobalTheory.CompanionTheory.Ar.Crv.SubFrob
end
end
