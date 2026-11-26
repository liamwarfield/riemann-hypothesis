module

public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiablePolyDeriv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemISupInfWeightSubmoduleOfDiagonalStable
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeightComponentMem
namespace GlobalTheory.WeightSubspaceComponent

open Formalism.BasicNotions.TH

theorem mem_wtSub_iff {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (x : V) :
    x ∈ wtSub act μ ↔ ∀ a, act (Eab a a) x = ((μ a : ℚ) : ℂ) • x := by
  unfold wtSub
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem weight_component_mem {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V)
    (hN : ∀ (a : Ix p q), ∀ x ∈ N, act (Eab a a) x ∈ N)
    (S : Finset (Ix p q → ℚ)) (f : (Ix p q → ℚ) → V)
    (hf : ∀ ν, f ν ∈ wtSub act ν) (hS : ∑ ν ∈ S, f ν ∈ N) : ∀ ν ∈ S, f ν ∈ N := by
  classical
  induction S using Finset.strongInduction generalizing f with
  | H S ih =>
    intro ν hν
    by_cases h : ∃ μ ∈ S, μ ≠ ν
    · obtain ⟨μ, hμ, hne⟩ := h
      obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
      let g : (Ix p q → ℚ) → V := fun l => (((l a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ)) • f l
      have hg : ∀ l, g l ∈ wtSub act l := fun l => Submodule.smul_mem _ _ (hf l)
      have hsum : ∑ l ∈ S.erase μ, g l
          = act (Eab a a) (∑ l ∈ S, f l) - ((μ a : ℚ) : ℂ) • ∑ l ∈ S, f l := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Finset.sum_erase S (by simp [g]), map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [(mem_wtSub_iff act l (f l)).mp (hf l) a]
        exact sub_smul _ _ _
      have hmem : ∑ l ∈ S.erase μ, g l ∈ N := by
        rw [hsum]
        exact N.sub_mem (hN a _ hS) (N.smul_mem _ hS)
      have hgν := ih (S.erase μ) (Finset.erase_ssubset hμ) g hg hmem ν
        (Finset.mem_erase.mpr ⟨hne.symm, hν⟩)
      have hc : (((ν a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ)) ≠ 0 := by
        rw [sub_ne_zero]
        exact_mod_cast ha.symm
      exact (N.smul_mem_iff hc).mp hgν
    · have hone : ∑ l ∈ S, f l = f ν :=
        Finset.sum_eq_single_of_mem ν hν fun μ hμ hne => absurd ⟨μ, hμ, hne⟩ h
      rwa [hone] at hS

end GlobalTheory.WeightSubspaceComponent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemISupInfWeightSubmoduleOfDiagonalStable
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.WeightDecomp

lemma comp_mem {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V)
    (hN : ∀ a, ∀ x ∈ N, act (Eab a a) x ∈ N) (S : Finset (Ix p q → ℚ)) :
    ∀ f : (Ix p q → ℚ) → V, (∀ ν, f ν ∈ wtSub act ν) → ∑ ν ∈ S, f ν ∈ N → ∀ ν ∈ S, f ν ∈ N := by
  first
  | exact @_root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem
  | exact _root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem
  | (apply _root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem ..)

theorem mem_iSup_inf_wtSub : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V),
    (∀ a, ∀ x ∈ N, act (Eab a a) x ∈ N) → ∀ x ∈ N, x ∈ (⨆ μ : Ix p q → ℚ, wtSub act μ) →
      x ∈ ⨆ μ : Ix p q → ℚ, N ⊓ wtSub act μ := by
  intro p q V _ _ act N hN x hx hx'
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx'
  have h := comp_mem act N hN f.support f hf hx
  refine Submodule.sum_mem _ fun ν hν => ?_
  exact Submodule.mem_iSup_of_mem ν ⟨h ν hν, hf ν⟩

end GlobalTheory.WeightDecomp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemISupInfWeightSubmoduleOfDiagonalStableStatement
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_iSup_inf_weightSubmodule_of_diagonal_stable : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V), (∀ a, ∀ x ∈ N, act (Eab a a) x ∈ N) → ∀ x ∈ N, x ∈ (⨆ μ : Ix p q → ℚ, wtSub act μ) → x ∈ ⨆ μ : Ix p q → ℚ, N ⊓ wtSub act μ := by
  first | exact @GlobalTheory.WeightDecomp.mem_iSup_inf_wtSub | exact GlobalTheory.WeightDecomp.mem_iSup_inf_wtSub | (intros; apply GlobalTheory.WeightDecomp.mem_iSup_inf_wtSub <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyInverseHalfDifferent
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyInverseHalfDifferent
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory

namespace TraceDualFamily

open scoped nonZeroDivisors

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

lemma conj_conj (c : E ≃ₐ[ℚ] E) (φ₀ : E →+* ℂ)
    (hc : ∀ (φ : E →+* ℂ) (x : E), φ (c x) = starRingEnd ℂ (φ x)) (x : E) : c (c x) = x := by
  apply φ₀.injective
  rw [hc, hc, Complex.conj_conj]

lemma mem_range_iff (x : K) : x ∈ (algebraMap (𝓞 K) K).range ↔ IsIntegral ℤ x :=
  ⟨by rintro ⟨y, rfl⟩; exact RingOfIntegers.isIntegral_coe y, fun h => ⟨⟨x, h⟩, rfl⟩⟩

lemma isIntegral_trace_conj (c : E ≃ₐ[ℚ] E) (φ₀ : E →+* ℂ)
    (hc : ∀ (φ : E →+* ℂ) (x : E), φ (c x) = starRingEnd ℂ (φ x)) (z : E)
    (hz : IsIntegral ℤ (Algebra.trace K E z)) : IsIntegral ℤ (Algebra.trace K E (c z)) := by
  letI : Algebra K ℂ := (φ₀.comp (algebraMap K E)).toAlgebra
  have h1 : algebraMap K ℂ (Algebra.trace K E (c z)) =
      starRingEnd ℂ (algebraMap K ℂ (Algebra.trace K E z)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [trace_eq_sum_embeddings ℂ, trace_eq_sum_embeddings ℂ, map_sum]
    exact Finset.sum_congr rfl fun σ _ => hc (σ : E →+* ℂ) z
  have h2 : IsIntegral ℤ (algebraMap K ℂ (Algebra.trace K E (c z))) := by
    rw [h1]
    exact (hz.map (algebraMap K ℂ).toIntAlgHom).map (starRingEnd ℂ).toIntAlgHom
  exact (isIntegral_algHom_iff (algebraMap K ℂ).toIntAlgHom (algebraMap K ℂ).injective).mp h2

lemma isLocalizedModule_subtype (Λ : Submodule (𝓞 K) E)
    (h : Submodule.span K (Λ : Set E) = ⊤) : IsLocalizedModule (𝓞 K)⁰ Λ.subtype := by
  refine {
    map_units := (isLocalizedModule_id (𝓞 K)⁰ E K).map_units
    surj := ?_
    exists_of_eq := ?_ }
  · intro y
    have hy : y ∈ Submodule.span K (Λ : Set E) := h ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (𝓞 K)⁰ K _ y hy
    rw [Submodule.span_eq] at ht
    exact ⟨(⟨_, ht⟩, t), rfl⟩
  · intro x₁ x₂ hxy
    exact ⟨1, by simpa using hxy⟩

theorem exists_family (c : E ≃ₐ[ℚ] E) (φ₀ : E →+* ℂ)
    (hc : ∀ (φ : E →+* ℂ) (x : E), φ (c x) = starRingEnd ℂ (φ x))
    (I : FractionalIdeal (𝓞 E)⁰ E)
    (hI : ∀ x : E, x ∈ I ↔ ∀ y ∈ I, Algebra.trace K E (x * c y) ∈ (algebraMap (𝓞 K) K).range) :
    ∃ (r : ℕ) (a a' : Fin r → E), (∀ k, a k ∈ I) ∧ (∀ k, a' k ∈ I) ∧
      ∀ t : E, t = ∑ k, (Algebra.trace K E (t * c (a' k))) • a k := by
  have hI0 : I ≠ 0 := by
    rintro rfl
    have := (hI 1).mpr (by
      intro y hy
      rw [FractionalIdeal.mem_zero_iff] at hy
      subst hy
      simp)
    rw [FractionalIdeal.mem_zero_iff] at this
    exact one_ne_zero this
  let Λ : Submodule (𝓞 K) E := (I : Submodule (𝓞 E) E).restrictScalars (𝓞 K)
  have hsp : Submodule.span K (Λ : Set E) = ⊤ := by
    obtain ⟨x, hx, hx0⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hI0
    rw [eq_top_iff]
    intro t _
    have hx' : algebraMap (𝓞 E) E x ≠ 0 := by simpa using hx
    have halg : IsAlgebraic ℤ (t / algebraMap (𝓞 E) E x) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic _)
    obtain ⟨n, hn0, hn⟩ := halg.exists_integral_multiple
    have hmem : (n : E) * t ∈ Λ := by
      have := (I : Submodule (𝓞 E) E).smul_mem (⟨_, hn⟩ : 𝓞 E) hx0
      convert this using 1
      change _ ↔ (n • (t / algebraMap (𝓞 E) E x)) * algebraMap (𝓞 E) E x ∈ _
      rw [zsmul_eq_mul, mul_assoc, div_mul_cancel₀ _ hx']
      rfl
    have hnK : (n : K) ≠ 0 := by exact_mod_cast hn0
    have : t = (n : K)⁻¹ • ((n : E) * t) := by
      have hnE : (n : E) ≠ 0 := by exact_mod_cast hn0
      rw [Algebra.smul_def, map_inv₀, map_intCast, inv_mul_cancel_left₀ hnE]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  have : Module.Finite (𝓞 K) Λ := Module.Finite.iff_fg.mpr
    (Submodule.FG.restrictScalars (FractionalIdeal.fg_of_isNoetherianRing le_rfl I))
  have : Module.FinitePresentation (𝓞 K) Λ := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) Λ := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, f, g, -, -, hfg'⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 K) Λ
  have := isLocalizedModule_subtype Λ hsp
  have hext : ∀ i : Fin m, ∃ w : E, ∀ y : Λ, Algebra.trace K E ((y : E) * c w) = (g y i : K) := by
    intro i
    let φ : Λ →ₗ[𝓞 K] K := Algebra.linearMap (𝓞 K) K ∘ₗ LinearMap.proj i ∘ₗ g
    let ψ : E →ₗ[𝓞 K] K := IsLocalizedModule.lift (𝓞 K)⁰ Λ.subtype φ
      (IsLocalizedModule.map_units (S := (𝓞 K)⁰) (Algebra.linearMap (𝓞 K) K))
    obtain ⟨u, hu⟩ := ((Algebra.traceForm K E).toDual (traceForm_nondegenerate K E)).surjective
      (ψ.extendScalarsOfIsLocalization (𝓞 K)⁰ K)
    refine ⟨c.symm u, fun y => ?_⟩
    have h1 := LinearMap.congr_fun hu (y : E)
    rw [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply] at h1
    rw [AlgEquiv.apply_symm_apply, mul_comm, h1]
    exact IsLocalizedModule.lift_apply (𝓞 K)⁰ Λ.subtype φ
      (IsLocalizedModule.map_units (S := (𝓞 K)⁰) (Algebra.linearMap (𝓞 K) K)) y
  choose w hw using hext
  refine ⟨m, fun i => (f (Pi.single i 1) : E), w, fun i => Subtype.prop (f (Pi.single i 1)),
    fun i => ?_, ?_⟩
  · refine (hI _).mpr fun y hy => (mem_range_iff _).mpr ?_
    have e : w i * c y = c (y * c (w i)) := by rw [map_mul, conj_conj c φ₀ hc, mul_comm]
    rw [e]
    refine isIntegral_trace_conj c φ₀ hc _ ?_
    rw [hw i ⟨y, hy⟩]
    exact RingOfIntegers.isIntegral_coe _
  · intro u
    have hu : u ∈ Submodule.span K (Λ : Set E) := hsp ▸ Submodule.mem_top
    induction hu using Submodule.span_induction with
    | mem y hy =>
      have h1 : f (g ⟨y, hy⟩) = ⟨y, hy⟩ := LinearMap.congr_fun hfg' _
      have h2 : g ⟨y, hy⟩ = ∑ i, g ⟨y, hy⟩ i • (Pi.single i 1 : Fin m → 𝓞 K) := by
        ext j; simp [Pi.single_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h2, map_sum] at h1
      have h3 := congrArg Subtype.val h1
      simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul] at h3
      refine h3.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
      rw [hw i ⟨y, hy⟩]
      exact (algebraMap_smul K _ _).symm
    | zero => simp
    | add x y _ _ hx hy =>
      conv_lhs => rw [hx, hy]
      simp [add_mul, Finset.sum_add_distrib, add_smul]
    | smul a x _ hx =>
      conv_lhs => rw [hx]
      simp [Finset.smul_sum, mul_smul]

end TraceDualFamily

theorem exists_trace_dual_family_halfDifferent : ∀ (D : D7), ∃ (r : ℕ) (a a' : Fin r → D.host.E), (∀ k, a k ∈ D.host.AA0) ∧ (∀ k, a' k ∈ D.host.AA0) ∧ ∀ t : D.host.E, t = ∑ k, (Algebra.trace D.host.K D.host.E (t * D.host.conj (a' k))) • a k :=
  fun D => TraceDualFamily.exists_family D.host.conj D.host.φ₀
    (fun φ x => D.host.conjE_apply φ x) D.host.AA0
    (factMMUnimodular D.R D.host)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyInverseHalfDifferentStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_traceDual_family_inverseHalfDifferent : ∀ (D : D7), ∃ (r : ℕ) (a a' : Fin r → D.host.E), (∀ k, a k ∈ D.host.AA0) ∧ (∀ k, a' k ∈ D.host.AA0) ∧ ∀ t : D.host.E, t = ∑ k, (Algebra.trace D.host.K D.host.E (t * D.host.conj (a' k))) • a k := by
  first | exact @GlobalTheory.exists_trace_dual_family_halfDifferent | exact GlobalTheory.exists_trace_dual_family_halfDifferent | (intros; apply GlobalTheory.exists_trace_dual_family_halfDifferent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSSRepTraceNondegenerate
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSSRepTraceNondegenerate
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

namespace GlobalTheory

open Polynomial Matrix in
private theorem eq_zero_of_mulVec_eq_self_of_trace_mul_eq_zero {K : Type} [Field K] [CharZero K]
    {a : ℕ} (B : Subalgebra K (Matrix (Fin a) (Fin a) K)) {z : Matrix (Fin a) (Fin a) K}
    (hzB : z ∈ B) (htr : ∀ y ∈ B, (z * y).trace = 0) {v : Fin a → K} (hv : z *ᵥ v = v) :
    v = 0 := by
  classical
  obtain ⟨q, hpq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd z.charpoly
    (Matrix.charpoly_monic z).ne_zero 0
  set m := z.charpoly.rootMultiplicity 0 with hm
  simp only [map_zero, sub_zero] at hpq hq
  have hc : q.coeff 0 ≠ 0 := fun h => hq (Polynomial.X_dvd_iff.2 h)
  set c := q.coeff 0 with hcdef
  set R := aeval z q.divX with hR
  have hq' : aeval z q = z * R + c • 1 := by
    calc aeval z q = aeval z (X * q.divX + C (q.coeff 0)) := by rw [Polynomial.X_mul_divX_add]
      _ = z * R + c • 1 := by
        rw [map_add (f := _), map_mul, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
  have h0 : z ^ m * (z * R + c • 1) = 0 := by
    have := Matrix.aeval_self_charpoly z
    rwa [hpq, map_mul, map_pow, aeval_X, hq'] at this
  have hRz : z * R = R * z := by
    have := congrArg (aeval z) (mul_comm X q.divX)
    simpa [R] using this
  have h1 : z ^ (m + 1) * R = -(c • z ^ m) := by
    rw [pow_succ, mul_assoc]
    rw [mul_add, mul_smul_comm, mul_one] at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hkey : z ^ m = z ^ (m + 1) * ((-c⁻¹) • R) := by
    rw [mul_smul_comm, h1, smul_neg, smul_smul, neg_mul, inv_mul_cancel₀ hc, neg_smul, one_smul,
      neg_neg]
  set u := (-c⁻¹) • R with hu
  have hcomm : Commute z u := (show Commute z R from hRz).smul_right _
  have hstep : ∀ i, z ^ (m + i) = z ^ (m + i + 1) * u := by
    intro i
    rw [pow_add z m i, hkey, mul_assoc, ← (hcomm.pow_left i).eq, ← mul_assoc, ← pow_add,
      show m + 1 + i = m + i + 1 by omega]
  have hpow : ∀ k, z ^ (m + 1) = z ^ (m + 1 + k) * u ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ih, show m + 1 + k = m + (k + 1) by omega, hstep (k + 1), mul_assoc, ← pow_succ',
        show m + (k + 1) + 1 = m + 1 + (k + 1) by omega]
  have hRB : R ∈ B :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 hzB) (Polynomial.aeval_mem_adjoin_singleton K z)
  have huB : u ∈ B := B.smul_mem hRB _
  set n := m + 1 with hn
  have hnn := hpow n
  have hc' : u ^ n * z ^ n = z ^ n * u ^ n := (hcomm.pow_pow n n).eq.symm
  have he : IsIdempotentElem (z ^ n * u ^ n) := by
    show z ^ n * u ^ n * (z ^ n * u ^ n) = z ^ n * u ^ n
    rw [mul_assoc, ← mul_assoc (u ^ n) (z ^ n) (u ^ n), hc', ← mul_assoc, ← mul_assoc, ← pow_add,
      ← hnn]
  have hez : z ^ n * u ^ n * z ^ n = z ^ n := by
    rw [mul_assoc, hc', ← mul_assoc, ← pow_add, ← hnn]
  have htre : (z ^ n * u ^ n).trace = 0 := by
    have : z ^ n * u ^ n = z * (z ^ m * u ^ n) := by
      show z ^ (m + 1) * u ^ n = _
      rw [pow_succ', mul_assoc]
    rw [this]
    exact htr _ (B.mul_mem (B.pow_mem hzB m) (B.pow_mem huB n))
  have he0 : z ^ n * u ^ n = 0 := by
    have h1 : IsIdempotentElem (Matrix.toLin' (z ^ n * u ^ n)) := by
      unfold IsIdempotentElem at he ⊢
      rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, he]
    have h2 := (LinearMap.IsIdempotentElem.trace_eq_zero_iff h1).1
      (by rw [Matrix.trace_toLin'_eq, htre])
    exact Matrix.toLin'.injective (by rw [h2, map_zero])
  have hzn : z ^ n = 0 := by rw [← hez, he0, zero_mul]
  have hvn : ∀ k, (z ^ k) *ᵥ v = v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hv, ih]
  rw [← hvn n, hzn, Matrix.zero_mulVec]

open Polynomial Matrix in
theorem _root_.GlobalTheory.isSSRep_trace_nondegenerate :
    ∀ (Γ K : Type) [Group Γ] [Field K] [CharZero K] (a : ℕ) (ρ : Γ →* GL (Fin a) K), _root_.Formalism.MainNotions.N.IsSSRep ρ → (∀ x ∈ Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)), (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) := by
  intro Γ K _ _ _ a ρ hss x hx htrx
  classical
  unfold _root_.Formalism.MainNotions.N.IsSSRep at hss
  set P : Γ → Matrix (Fin a) (Fin a) K :=
    fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) with hP
  have hPmul : ∀ g h, P (g * h) = P g * P h := fun g h => by simp [hP, map_mul]
  have hP1 : P 1 = 1 := by simp [hP]
  have hgen : ∀ g, P g ∈ Submodule.span K (Set.range P) := fun g => Submodule.subset_span ⟨g, rfl⟩
  have hleft : ∀ g, ∀ y ∈ Submodule.span K (Set.range P),
      P g * y ∈ Submodule.span K (Set.range P) := by
    intro g y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨h, rfl⟩ := hy; rw [← hPmul]; exact hgen _
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y w _ _ hy hw => rw [mul_add]; exact Submodule.add_mem _ hy hw
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  have hAmul : ∀ y ∈ Submodule.span K (Set.range P), ∀ w ∈ Submodule.span K (Set.range P),
      y * w ∈ Submodule.span K (Set.range P) := by
    intro y hy w hw
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨g, rfl⟩ := hy; exact hleft g w hw
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add y t _ _ hy ht => rw [add_mul]; exact Submodule.add_mem _ hy ht
    | smul c y _ hy => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hy
  let B : Subalgebra K (Matrix (Fin a) (Fin a) K) :=
    { carrier := Submodule.span K (Set.range P)
      mul_mem' := fun hy hw => hAmul _ hy _ hw
      add_mem' := fun hy hw => Submodule.add_mem _ hy hw
      algebraMap_mem' := fun c => by
        rw [Algebra.algebraMap_eq_smul_one, ← hP1]
        exact Submodule.smul_mem _ c (hgen 1) }
  let J : Matrix (Fin a) (Fin a) K → Prop :=
    fun z => z ∈ Submodule.span K (Set.range P) ∧ ∀ g, (z * P g).trace = 0
  have hJtr : ∀ z, J z → ∀ y ∈ B, (z * y).trace = 0 := by
    intro z hz y hy
    have hy' : y ∈ Submodule.span K (Set.range P) := hy
    clear hy
    induction hy' using Submodule.span_induction with
    | mem y hg => obtain ⟨g, rfl⟩ := hg; exact hz.2 g
    | zero => simp
    | add y w _ _ h1 h2 => rw [mul_add, Matrix.trace_add, h1, h2, add_zero]
    | smul c y _ h => rw [mul_smul_comm, Matrix.trace_smul, h, smul_zero]
  have hJleft : ∀ g z, J z → J (P g * z) := by
    intro g z hz
    refine ⟨hleft g z hz.1, fun h => ?_⟩
    rw [mul_assoc, Matrix.trace_mul_comm, mul_assoc, ← hPmul]
    exact hz.2 _
  have hJright : ∀ g z, J z → J (z * P g) := by
    intro g z hz
    refine ⟨hAmul _ hz.1 _ (hgen g), fun h => ?_⟩
    rw [mul_assoc, ← hPmul]
    exact hz.2 _
  have hJ0 : J 0 := ⟨Submodule.zero_mem _, fun g => by simp⟩
  have hJadd : ∀ y z, J y → J z → J (y + z) := fun y z hy hz =>
    ⟨Submodule.add_mem _ hy.1 hz.1, fun g => by rw [add_mul, Matrix.trace_add, hy.2, hz.2, add_zero]⟩
  have hJsmul : ∀ (c : K) z, J z → J (c • z) := fun c z hz =>
    ⟨Submodule.smul_mem _ c hz.1, fun g => by rw [smul_mul_assoc, Matrix.trace_smul, hz.2, smul_zero]⟩
  have hfix : ∀ z, J z → ∀ v, z *ᵥ v = v → v = 0 := fun z hz v hv =>
    eq_zero_of_mulVec_eq_self_of_trace_mul_eq_zero B hz.1 (hJtr z hz) hv
  have hpres : ∀ S : Submodule K (Fin a → K), _root_.Formalism.MainNotions.N.IsInv ρ S →
      ∀ y ∈ Submodule.span K (Set.range P), ∀ s ∈ S, y *ᵥ s ∈ S := by
    intro S hS y hy s hs
    unfold _root_.Formalism.MainNotions.N.IsInv at hS
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨g, rfl⟩ := hy; exact hS g s hs
    | zero => rw [Matrix.zero_mulVec]; exact S.zero_mem
    | add y w _ _ h1 h2 => rw [Matrix.add_mulVec]; exact S.add_mem h1 h2
    | smul c y _ h => rw [Matrix.smul_mulVec]; exact S.smul_mem c h
  let W : Submodule K (Fin a → K) :=
    { carrier := {v | ∀ z, J z → z *ᵥ v = 0}
      add_mem' := fun {v w} hv hw z hz => by rw [Matrix.mulVec_add, hv z hz, hw z hz, add_zero]
      zero_mem' := fun z _ => Matrix.mulVec_zero z
      smul_mem' := fun c v hv z hz => by rw [Matrix.mulVec_smul, hv z hz, smul_zero] }
  have hWst : _root_.Formalism.MainNotions.N.IsInv ρ W := by
    unfold _root_.Formalism.MainNotions.N.IsInv
    intro g v hv
    have hv' : ∀ z, J z → z *ᵥ v = 0 := hv
    show ∀ z, J z → z *ᵥ (P g *ᵥ v) = 0
    intro z hz
    rw [Matrix.mulVec_mulVec]
    exact hv' _ (hJright g z hz)
  obtain ⟨W', hW'st, hcompl⟩ := hss W hWst
  have hW'bot : W' = ⊥ := by
    by_contra hne
    obtain ⟨S, ⟨hSst, hSW', hSne⟩, hmin⟩ := WellFounded.has_min wellFounded_lt
      {S : Submodule K (Fin a → K) | _root_.Formalism.MainNotions.N.IsInv ρ S ∧ S ≤ W' ∧ S ≠ ⊥} ⟨W', hW'st, le_rfl, hne⟩
    obtain ⟨s, hsS, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSne
    let T : Submodule K (Fin a → K) :=
      { carrier := {w | ∃ z, J z ∧ z *ᵥ s = w}
        add_mem' := by
          rintro _ _ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
          exact ⟨y + z, hJadd y z hy hz, Matrix.add_mulVec _ _ _⟩
        zero_mem' := ⟨0, hJ0, Matrix.zero_mulVec _⟩
        smul_mem' := by
          rintro c _ ⟨z, hz, rfl⟩
          exact ⟨c • z, hJsmul c z hz, Matrix.smul_mulVec _ _ _⟩ }
    have hTS : T ≤ S := by
      rintro _ ⟨z, hz, rfl⟩
      exact hpres S hSst z hz.1 s hsS
    have hTst : _root_.Formalism.MainNotions.N.IsInv ρ T := by
      unfold _root_.Formalism.MainNotions.N.IsInv
      rintro g _ ⟨z, hz, rfl⟩
      exact ⟨P g * z, hJleft g z hz, (Matrix.mulVec_mulVec _ _ _).symm⟩
    by_cases hT : T = ⊥
    · apply hs0
      have hsW : s ∈ W := by
        show ∀ z, J z → z *ᵥ s = 0
        intro z hz
        have hzT : z *ᵥ s ∈ T := ⟨z, hz, rfl⟩
        rw [hT] at hzT
        exact (Submodule.mem_bot K).1 hzT
      exact (Submodule.disjoint_def.1 hcompl.disjoint) s hsW (hSW' hsS)
    · have hTeq : T = S := by
        by_contra hTS'
        exact hmin T ⟨hTst, hTS.trans hSW', hT⟩ (lt_of_le_of_ne hTS hTS')
      have hsT : s ∈ T := hTeq ▸ hsS
      obtain ⟨z, hz, hzs⟩ := hsT
      exact hs0 (hfix z hz s hzs)
  have hWtop : W = ⊤ := by
    have h := hcompl.sup_eq_top
    rwa [hW'bot, sup_bot_eq] at h
  have hxJ : J x := ⟨hx, htrx⟩
  refine Matrix.ext_iff_mulVec.2 fun v => ?_
  rw [Matrix.zero_mulVec]
  have hv : ∀ z, J z → z *ᵥ v = 0 := (hWtop ▸ Submodule.mem_top : v ∈ W)
  exact hv x hxJ

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSSRepTraceNondegenerateStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_trace_mul_eq_zero_of_isSSRep : ∀ (Γ K : Type) [Group Γ] [Field K] [CharZero K] (a : ℕ) (ρ : Γ →* GL (Fin a) K), IsSSRep ρ → (∀ x ∈ Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)), (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) := by
  first | exact @GlobalTheory.isSSRep_trace_nondegenerate | exact GlobalTheory.isSSRep_trace_nondegenerate | (intros; apply GlobalTheory.isSSRep_trace_nondegenerate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApplyAtOriginMinorProductLinear
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApplyAtOriginMinorProductLinear
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum.Minor

open ReciprocityTheory.ChartRestriction.G Matrix

abbrev Incr (a d : ℕ) : Type := {s : Fin a → Fin d // StrictMono s}

noncomputable def toIncr {a d : ℕ} (S : Set.powersetCard (Fin d) a) : Incr a d :=
  ⟨GlobalTheory.subsetEnum S, (S.1.orderEmbOfFin S.2).strictMono⟩

theorem toIncr_bijective {a d : ℕ} : Function.Bijective (toIncr (a := a) (d := d)) := by
  constructor
  · intro S S' h
    have h1 : GlobalTheory.subsetEnum S = GlobalTheory.subsetEnum S' := congrArg Subtype.val h
    have h2 : (S.1 : Set (Fin d)) = S'.1 := by
      rw [← GlobalTheory.range_subsetEnum S, ← GlobalTheory.range_subsetEnum S', h1]
    exact Subtype.ext (Finset.coe_injective h2)
  · intro s
    have hc : (Finset.univ.image s.1).card = a := by
      rw [Finset.card_image_of_injective _ s.2.injective]; simp
    refine ⟨⟨Finset.univ.image s.1, hc⟩, Subtype.ext ?_⟩
    exact (Finset.orderEmbOfFin_unique hc (fun x => by simp) s.2).symm

theorem det_submatrix_mul {R l o : Type*} [CommRing R] {a d : ℕ}
    (A : Matrix l (Fin d) R) (B : Matrix (Fin d) o R) (r : Fin a → l) (c : Fin a → o) :
    ((A * B).submatrix r c).det = ∑ s : Incr a d, (A.submatrix r s.1).det * (B.submatrix s.1 c).det := by
  rw [GlobalTheory.det_submatrix_mul_eq_sum_minors]
  exact Fintype.sum_bijective toIncr toIncr_bijective _ _ fun S => rfl

theorem det_submatrix_one {a d : ℕ} (s s' : Incr a d) :
    ((1 : Matrix (Fin d) (Fin d) ℂ).submatrix s.1 s'.1).det = if s = s' then 1 else 0 := by
  obtain ⟨I, rfl⟩ := toIncr_bijective.2 s
  obtain ⟨J, rfl⟩ := toIncr_bijective.2 s'
  split_ifs with h
  · rw [← h, submatrix_one _ (toIncr I).2.injective, det_one]
  · have h' : I ≠ J := fun e => h (by rw [e])
    obtain ⟨x, hxI, hxJ⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne I J).mp h'
    have h1 : x ∈ Set.range (GlobalTheory.subsetEnum I) := by rw [GlobalTheory.range_subsetEnum]; exact hxI
    have h2 : x ∉ Set.range (GlobalTheory.subsetEnum J) := by rw [GlobalTheory.range_subsetEnum]; exact hxJ
    obtain ⟨i, rfl⟩ := h1
    exact det_eq_zero_of_row_eq_zero i fun j => one_apply_ne fun e => h2 ⟨j, e.symm⟩

theorem minors_orth {a d : ℕ} {u : Matrix (Fin d) (Fin d) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (s' s'' : Incr a d) :
    ∑ s : Incr a d, (u.submatrix s'.1 s.1).det * star (u.submatrix s''.1 s.1).det = if s' = s'' then 1 else 0 := by
  rw [← det_submatrix_one, ← (Matrix.mem_unitaryGroup_iff.1 hu), det_submatrix_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← det_conjTranspose, conjTranspose_submatrix, star_eq_conjTranspose]

theorem sum_norm_sq_eq {ι : Type*} [Fintype ι] (K : ι → ι → ℂ)
    (hK : ∀ i j, ∑ t, K i t * star (K j t) = if i = j then 1 else 0) (v : ι → ℂ) :
    ∑ t, ‖∑ i, K i t * v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  apply Complex.ofReal_injective
  have h (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [Complex.ofReal_sum, h, star_sum, star_mul', Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  have : ∀ j, ∑ t, K i t * v i * (star (K j t) * star (v j)) = (if i = j then 1 else 0) * (v i * star (v j)) := by
    intro j
    rw [← hK, Finset.sum_mul]
    exact Finset.sum_congr rfl fun t _ => by ring
  simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem prod_prod_sum {R T S : Type*} [CommSemiring R] [Fintype T] [DecidableEq T] [Fintype S] (n : T → ℕ)
    (f : ∀ τ, Fin (n τ) → S → R) :
    ∏ τ, ∏ j, ∑ s, f τ j s = ∑ t : ∀ τ, Fin (n τ) → S, ∏ τ, ∏ j, f τ j (t τ j) := by
  simp only [Fintype.prod_sum]

theorem polyDeriv_subst {σ κ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [Fintype κ] {F : W → ℂ}
    (hF : ContDiff ℂ (⊤ : ℕ∞) F) (s : σ → κ → ℂ)
    (j : σ → κ → σ) (Φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ)
    (hΦ : ∀ l, Φ (MvPolynomial.X l) = ∑ k, MvPolynomial.C (s l k) * MvPolynomial.X (j l k))
    (u : σ → W) (P : MvPolynomial σ ℂ) (x : W) :
    I2.polyDeriv (Φ P) u F x = I2.polyDeriv P (fun l => ∑ k, s l k • u (j l k)) F x := by
  induction P using MvPolynomial.induction_on generalizing x with
  | C a =>
    have h : (MvPolynomial.C a : MvPolynomial σ ℂ) = a • MvPolynomial.monomial 0 1 := by
      simp [MvPolynomial.smul_eq_C_mul]
    rw [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, h]
    simp [I2.polyDeriv_smul, I2.polyDeriv_monomial_one, I2.pdTerm_eq_itD,
      -MvPolynomial.monomial_zero']
  | add P Q hP hQ => simp only [map_add (f := _), I2.polyDeriv_add, hP, hQ]
  | mul_X P l hP =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, hΦ, Finset.mul_sum, I2.jof_polyDeriv_sum, GlobalTheory.ThFr.polyDeriv_mul_X hF, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_left_comm, MvPolynomial.C_mul', I2.polyDeriv_smul, GlobalTheory.ThFr.polyDeriv_mul_X hF, funext hP]
    simp

variable {D : D7} {a d : ℕ}

theorem applyAt0_eq (P : MvPolynomial (GL3Theta.Idx D a d) ℂ) (G : VC D a d → ℂ) :
    GL3Theta.applyAt0 D P G = I2.polyDeriv P (coordV D) G 0 := by
  unfold GL3Theta.applyAt0 I2.polyDeriv taylor
  refine Finset.sum_congr rfl fun α _ => ?_
  have h : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  rw [mul_assoc, mul_div_cancel₀ _ h]
  rfl

theorem applyAt0_comp {κ : Type} [Fintype κ] {G : VC D a d → ℂ} (hG : Differentiable ℂ G)
    (A : VC D a d →ₗ[ℂ] VC D a d) (s : GL3Theta.Idx D a d → κ → ℂ) (j : GL3Theta.Idx D a d → κ → GL3Theta.Idx D a d)
    (hA : ∀ l, A (coordV D l) = ∑ k, s l k • coordV D (j l k)) (P : MvPolynomial (GL3Theta.Idx D a d) ℂ) :
    GL3Theta.applyAt0 D P (fun z => G (A z)) = GL3Theta.applyAt0 D
      (MvPolynomial.aeval (fun l => ∑ k, MvPolynomial.C (s l k) * (MvPolynomial.X (j l k) : MvPolynomial _ ℂ)) P) G := by
  have hG' : ContDiff ℂ (⊤ : ℕ∞) G := contDiff_infty.2 fun k => I2.contDiff_of_differentiable_fd hG k
  rw [applyAt0_eq, applyAt0_eq, polyDeriv_subst hG' s j _ (fun l => MvPolynomial.aeval_X _ l)]
  have h := GlobalTheory.Jet.polyDeriv_comp_clm P (coordV D) hG (LinearMap.toContinuousLinearMap A) 0
  rw [map_zero] at h
  refine h.trans ?_
  congr 1
  funext l
  exact hA l

def mulR (u : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ) : VC D a d →ₗ[ℂ] VC D a d where
  toFun z := fun τ i j => ∑ k, z τ i k * u τ k j
  map_add' x y := by
    funext τ i j
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext τ i j
    simp [Finset.mul_sum, mul_assoc]

def mulL (u : D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ) : VC D a d →ₗ[ℂ] VC D a d where
  toFun z := fun τ i j => ∑ k, u τ i k * z τ k j
  map_add' x y := by
    funext τ i j
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext τ i j
    simp [Finset.mul_sum, mul_left_comm]

theorem mulR_coordV (u : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ) (l : GL3Theta.Idx D a d) :
    mulR u (coordV D l) = ∑ k, u l.1 l.2.2 k • coordV D (l.1, l.2.1, k) := by
  obtain ⟨τ, i, j⟩ := l
  funext τ' i' j'
  by_cases h1 : τ' = τ <;> by_cases h2 : i' = i <;>
    simp [mulR, coordV, Finset.sum_apply, h1, h2]

theorem mulL_coordV (u : D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ) (l : GL3Theta.Idx D a d) :
    mulL u (coordV D l) = ∑ k, u l.1 k l.2.1 • coordV D (l.1, k, l.2.2) := by
  obtain ⟨τ, i, j⟩ := l
  funext τ' i' j'
  by_cases h1 : τ' = τ <;> by_cases h2 : j' = j <;>
    simp [mulL, coordV, Finset.sum_apply, h1, h2]

theorem applyAt0_minorPol_mulR {n : D.what₂.Tau → ℕ} {G : VC D a d → ℂ} (hG : Differentiable ℂ G)
    (u : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ) (t : Tup D a d n) :
    GL3Theta.applyAt0 D (minorPol D t) (fun z => G (mulR u z)) =
      (∏ τ, (u τ).det ^ n τ) * GL3Theta.applyAt0 D (minorPol D t) G := by
  rw [applyAt0_comp hG (mulR u) (fun l k => u l.1 l.2.2 k) (fun l k => (l.1, l.2.1, k)) (mulR_coordV u),
    applyAt0_eq, applyAt0_eq, ← I2.polyDeriv_smul]
  congr 1
  unfold minorPol
  rw [map_prod, MvPolynomial.smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_prod, map_pow, ← Fin.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [AlgHom.map_det, RingHom.map_det, mul_comm, ← det_transpose (RingHom.mapMatrix _ _), ← det_mul]
  congr 1
  ext1 i i'
  simp [Matrix.mul_apply, mul_comm]

theorem applyAt0_minorPol_mulL {n : D.what₂.Tau → ℕ} {G : VC D a d → ℂ} (hG : Differentiable ℂ G)
    (u : D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ) (t : Tup D a d n) :
    GL3Theta.applyAt0 D (minorPol D t) (fun z => G (mulL u z)) =
      ∑ t' : Tup D a d n, (∏ τ, ∏ j, ((u τ).submatrix (t' τ j).1 (t τ j).1).det) *
        GL3Theta.applyAt0 D (minorPol D t') G := by
  rw [applyAt0_comp hG (mulL u) (fun l k => u l.1 k l.2.1) (fun l k => (l.1, k, l.2.2)) (mulL_coordV u)]
  simp only [applyAt0_eq, ← I2.polyDeriv_smul]
  rw [← I2.jof_polyDeriv_sum]
  congr 1
  unfold minorPol
  simp only [MvPolynomial.smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  rw [← prod_prod_sum n (fun τ j (s : Incr a d) => MvPolynomial.C ((u τ).submatrix s.1 (t τ j).1).det *
    (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, s.1 i, i') : MvPolynomial (GL3Theta.Idx D a d) ℂ)).det)]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun j _ => ?_
  have h := det_submatrix_mul ((u τ)ᵀ.map (MvPolynomial.C : ℂ →+* MvPolynomial (GL3Theta.Idx D a d) ℂ))
    (Matrix.of fun (i : Fin d) (i' : Fin a) => (MvPolynomial.X (τ, i, i') : MvPolynomial (GL3Theta.Idx D a d) ℂ))
    (t τ j).1 id
  rw [AlgHom.map_det]
  refine Eq.trans ?_ (h.trans (Finset.sum_congr rfl fun s _ => ?_))
  · congr 1
    ext1 i i'
    simp [Matrix.mul_apply]
  · rw [RingHom.map_det, ← det_transpose (RingHom.mapMatrix _ _)]
    rfl

end GlobalTheory.NormSum.Minor

open GlobalTheory.NormSum.Minor ReciprocityTheory.ChartRestriction.G in
theorem GlobalTheory.NormSum.applyAt0_minorPol_linear : ∀ (D : D7) (a d : ℕ) (n : D.what₂.Tau → ℕ) (G : VC D a d → ℂ), Differentiable ℂ G → (∀ (u : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ) (t : Tup D a d n), GL3Theta.applyAt0 D (minorPol D t) (fun z => G (fun τ => (Matrix.of (z τ) * u τ : Matrix _ _ ℂ))) = (∏ τ, (u τ).det ^ n τ) * GL3Theta.applyAt0 D (minorPol D t) G) ∧ (∀ (u : D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ), (∀ τ, u τ ∈ Matrix.unitaryGroup (Fin d) ℂ) → ∑ t : Tup D a d n, ‖GL3Theta.applyAt0 D (minorPol D t) (fun z => G (fun τ => (u τ * Matrix.of (z τ) : Matrix _ _ ℂ)))‖ ^ 2 = ∑ t : Tup D a d n, ‖GL3Theta.applyAt0 D (minorPol D t) G‖ ^ 2) ∧ (∀ (c : ℂ) P, GL3Theta.applyAt0 D P (c • G) = c * GL3Theta.applyAt0 D P G) ∧ ∀ G' P, Differentiable ℂ G' → GL3Theta.applyAt0 D P (G + G') = GL3Theta.applyAt0 D P G + GL3Theta.applyAt0 D P G' := by
  intro D a d n G hG
  refine ⟨fun u t => applyAt0_minorPol_mulR hG u t, fun u hu => ?_, fun c P => ?_, fun G' P hG' => ?_⟩
  · refine Eq.trans (Finset.sum_congr rfl fun t _ => ?_) (sum_norm_sq_eq
      (fun t' t : Tup D a d n => ∏ τ, ∏ j, ((u τ).submatrix (t' τ j).1 (t τ j).1).det) (fun t' t'' => ?_) _)
    · rw [← applyAt0_minorPol_mulL hG u t]
      rfl
    · simp only [star_prod, ← Finset.prod_mul_distrib]
      rw [← prod_prod_sum n (fun τ j (s : Incr a d) => ((u τ).submatrix (t' τ j).1 s.1).det *
        star ((u τ).submatrix (t'' τ j).1 s.1).det)]
      simp only [fun τ => minors_orth (a := a) (hu τ)]
      split_ifs with h
      · simp [h]
      · obtain ⟨τ, hτ⟩ := Function.ne_iff.1 h
        obtain ⟨j, hj⟩ := Function.ne_iff.1 hτ
        exact Finset.prod_eq_zero (Finset.mem_univ τ) (Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj))
  · rw [applyAt0_eq, applyAt0_eq, GlobalTheory.Jet.polyDeriv_smul_fun P _ hG]
  · rw [applyAt0_eq, applyAt0_eq, applyAt0_eq, GlobalTheory.Jet.polyDeriv_add_fun P _ hG hG']
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApplyAtOriginMinorProductLinearStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.applyAtOrigin_minorProduct_linear : ∀ (D : D7) (a d : ℕ) (n : D.what₂.Tau → ℕ) (G : VC D a d → ℂ), Differentiable ℂ G → (∀ (u : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ) (t : Tup D a d n), GL3Theta.applyAt0 D (minorPol D t) (fun z => G (fun τ => (Matrix.of (z τ) * u τ : Matrix _ _ ℂ))) = (∏ τ, (u τ).det ^ n τ) * GL3Theta.applyAt0 D (minorPol D t) G) ∧ (∀ (u : D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ), (∀ τ, u τ ∈ Matrix.unitaryGroup (Fin d) ℂ) → ∑ t : Tup D a d n, ‖GL3Theta.applyAt0 D (minorPol D t) (fun z => G (fun τ => (u τ * Matrix.of (z τ) : Matrix _ _ ℂ)))‖ ^ 2 = ∑ t : Tup D a d n, ‖GL3Theta.applyAt0 D (minorPol D t) G‖ ^ 2) ∧ (∀ (c : ℂ) P, GL3Theta.applyAt0 D P (c • G) = c * GL3Theta.applyAt0 D P G) ∧ ∀ G' P, Differentiable ℂ G' → GL3Theta.applyAt0 D P (G + G') = GL3Theta.applyAt0 D P G + GL3Theta.applyAt0 D P G' := by
  first | exact @GlobalTheory.NormSum.applyAt0_minorPol_linear | exact GlobalTheory.NormSum.applyAt0_minorPol_linear | (intros; apply GlobalTheory.NormSum.applyAt0_minorPol_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthoProductThetaMemThetaSpaceOfLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthoProductThetaMemThetaSpaceOfLattice
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ProdTheta

theorem coordB_add (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r)
    (z x : VC D N N') : coordB D T b k (z + x) = coordB D T b k z + coordB D T b k x := by
  simp only [coordB, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem coordB_differentiable (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (k : Fin r) : Differentiable ℂ (coordB D T b k) := by
  unfold coordB
  fun_prop

theorem neg_one_zpow_sum {ι : Type} (s : Finset ι) (m : ι → ℤ) :
    (-1 : ℂ) ^ (∑ k ∈ s, m k) = ∏ k ∈ s, (-1 : ℂ) ^ m k := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ (by norm_num), ih]

theorem pullB_mem_ThSp : ∀ (D : D7) (T : Tor D) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (g : ℂ → ℂ), (∀ z w : VC D N N', ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) = ∑ k, coordB D T b k z * (starRingEnd ℂ) (coordB D T b k w)) → (∀ x : VC D N N', x ∈ LaB D T b ↔ ∀ k, coordB D T b k x ∈ T.abelian₂) → Differentiable ℂ g → (∀ ω ∈ T.abelian₂, ∃ m : ℤ, q1 D T.abelian₂ ω = m ∧ ∀ z, (-1 : ℂ) ^ m * U1 T.abelian₂ ω g z = g z) → pullB D T b g ∈ ThSp D T (LaB D T b) := by
  intro D T N N' r b g hP hL hg hq
  refine ⟨?_, ?_⟩
  · unfold pullB
    have hc := coordB_differentiable D T b
    fun_prop
  · intro x hx z
    have hx' := (hL x).1 hx
    choose m hm hU using fun k => hq _ (hx' k)
    have hre : Real.sqrt D.host.d / 2 * (Hf D T x x).re = ((∑ k, m k : ℤ) : ℝ) := by
      unfold Hf
      rw [hP, Complex.div_ofReal_re, Complex.re_sum, Int.cast_sum, Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hm k, q1, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have hal : al D T x = ∏ k, (-1 : ℂ) ^ m k := by
      unfold al
      rw [hre, round_intCast, neg_one_zpow_sum]
    have hUU : U D T x (pullB D T b g) z = ∏ k, U1 T.abelian₂ (coordB D T b k x) g (coordB D T b k z) := by
      unfold U U1 pullB Hf
      rw [Finset.prod_mul_distrib, ← Complex.exp_sum, hP, hP]
      simp only [coordB_add]
      congr 2
      rw [Finset.sum_div, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hal, hUU, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => hU k _

end GlobalTheory.ProdTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthoProductThetaMemThetaSpaceOfLatticeStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthoProductTheta_mem_thetaSpace_of_lattice : ∀ (D : D7) (T : Tor D) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (g : ℂ → ℂ), (∀ z w : VC D N N', ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) = ∑ k, coordB D T b k z * (starRingEnd ℂ) (coordB D T b k w)) → (∀ x : VC D N N', x ∈ LaB D T b ↔ ∀ k, coordB D T b k x ∈ T.abelian₂) → Differentiable ℂ g → (∀ ω ∈ T.abelian₂, ∃ m : ℤ, q1 D T.abelian₂ ω = m ∧ ∀ z, (-1 : ℂ) ^ m * U1 T.abelian₂ ω g z = g z) → pullB D T b g ∈ ThSp D T (LaB D T b) := by
  first | exact @GlobalTheory.ProdTheta.pullB_mem_ThSp | exact GlobalTheory.ProdTheta.pullB_mem_ThSp | (intros; apply GlobalTheory.ProdTheta.pullB_mem_ThSp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormOneScalarAvoidingMatrixEigenvalues
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormOneScalarAvoidingMatrixEigenvalues
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormOneScalar

theorem exists_of_anti {E : Type} [Field E] [CharZero E] (c : E →+* E) (s : E) (hs : s ≠ 0) (hc : c s = -s)
    (n : ℕ) (γ : Matrix (Fin n) (Fin n) E) : ∃ z : E, z * c z = 1 ∧ z ≠ 1 ∧ (1 - z • γ).det ≠ 0 := by
  have hm : ∀ k : ℕ, ((k : E) + 1) - s ≠ 0 := by
    intro k h
    have h1 : s = (k : E) + 1 := by linear_combination -h
    have h2 : c s = s := by rw [h1]; simp
    apply hs
    have : (2 : E) * s = 0 := by linear_combination hc - h2
    simpa using this
  have hp : ∀ k : ℕ, ((k : E) + 1) + s ≠ 0 := by
    intro k h
    have h1 : s = -((k : E) + 1) := by linear_combination h
    have h2 : c s = s := by rw [h1]; simp
    apply hs
    have : (2 : E) * s = 0 := by linear_combination hc - h2
    simpa using this
  let f : ℕ → E := fun k => (((k : E) + 1) + s) / (((k : E) + 1) - s)
  have hf : Function.Injective f := by
    intro a b h
    have h' := (div_eq_div_iff (hm a) (hm b)).1 h
    have : (2 : E) * s * ((a : E) - b) = 0 := by linear_combination -h'
    have h3 : (a : E) - b = 0 := by
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (mul_ne_zero two_ne_zero hs)
      · exact h
    exact_mod_cast sub_eq_zero.1 h3
  have hP : γ.charpolyRev ≠ 0 := by
    intro h
    have := Matrix.eval_charpolyRev (M := γ)
    rw [h] at this
    simp at this
  have hfin : {z : E | γ.charpolyRev.IsRoot z}.Finite := Polynomial.finite_setOfPred_isRoot hP
  obtain ⟨z, ⟨k, rfl⟩, hz⟩ := (Set.infinite_range_of_injective hf).exists_notMem_finite hfin
  refine ⟨f k, ?_, ?_, ?_⟩
  · have h1 := hm k
    have h2 := hp k
    simp only [f, map_div₀, map_add (f := _), map_sub, map_natCast, map_one, hc, sub_neg_eq_add, ← sub_eq_add_neg]
    field_simp
  · intro h
    have h' := (div_eq_one_iff_eq (hm k)).1 h
    apply hs
    have : (2 : E) * s = 0 := by linear_combination h'
    simpa using this
  · intro h
    apply hz
    show Polynomial.eval (f k) γ.charpolyRev = 0
    rw [← h, Matrix.charpolyRev, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [hij] <;> exact mul_comm _ _

theorem exists_norm_one_det_ne_zero : ∀ (D : D7) (n : ℕ) (γ : Matrix (Fin n) (Fin n) D.host.E),
    ∃ z : D.host.E, z * D.host.conj z = 1 ∧ z ≠ 1 ∧ (1 - z • γ).det ≠ 0 := by
  intro D n γ
  have hs : D.host.sqrtMinusD ≠ 0 := by
    intro h
    have h1 := D.host.sqrtMinusD_sq
    rw [h] at h1
    have h2 : (D.host.d : D.host.E) = 0 := by linear_combination h1
    exact D.host.hyp.2.1.ne_zero (by exact_mod_cast h2)
  exact exists_of_anti (D.host.conj : D.host.E →+* D.host.E) D.host.sqrtMinusD hs D.host.conj_sqrtMinusD n γ

end GlobalTheory.NormOneScalar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormOneScalarAvoidingMatrixEigenvaluesStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normOne_scalar_avoiding_matrix_eigenvalues : ∀ (D : D7) (n : ℕ) (γ : Matrix (Fin n) (Fin n) D.host.E), ∃ z : D.host.E, z * D.host.conj z = 1 ∧ z ≠ 1 ∧ (1 - z • γ).det ≠ 0 := by
  first | exact @GlobalTheory.NormOneScalar.exists_norm_one_det_ne_zero | exact GlobalTheory.NormOneScalar.exists_norm_one_det_ne_zero | (intros; apply GlobalTheory.NormOneScalar.exists_norm_one_det_ne_zero <;> assumption)
end
end
