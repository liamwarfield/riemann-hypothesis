module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AlternatingMapSumSmulEqDetSmul
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.MemHomogIffIsHomogeneous
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ContinuousAevalMvPolynomial
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOneTmulOfForallFixed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemUnitaryGroupIffIsIsometry
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EqZeroOfForallLTensorEqZero
open TensorProduct

namespace GlobalTheory.ReducedAlg

theorem eq_zero_of_forall_lTensor_eq_zero {k : Type*} [Field k] {C M : Type*} [AddCommGroup C]
    [Module k C] [AddCommGroup M] [Module k M] {ι : Sort*} {N : ι → Type*}
    [∀ i, AddCommGroup (N i)] [∀ i, Module k (N i)] (φ : ∀ i, M →ₗ[k] N i)
    (hφ : ∀ m, (∀ i, φ i m = 0) → m = 0) (z : C ⊗[k] M)
    (hz : ∀ i, (φ i).lTensor C z = 0) : z = 0 := by
  classical
  let b := Module.Free.chooseBasis k C
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  rw [map_zero]
  ext j
  rw [Finsupp.coe_zero, Pi.zero_apply]
  have nat : ∀ (i : ι) (w : C ⊗[k] M),
      φ i (TensorProduct.equivFinsuppOfBasisLeft b w j) =
        TensorProduct.equivFinsuppOfBasisLeft b ((φ i).lTensor C w) j := by
    intro i w
    rw [TensorProduct.equivFinsuppOfBasisLeft_apply, TensorProduct.equivFinsuppOfBasisLeft_apply]
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c m => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  apply hφ
  intro i
  rw [nat, hz i, map_zero, Finsupp.coe_zero, Pi.zero_apply]

theorem isReduced_tensor_of_forall_prime {k : Type*} [Field k] (C A : Type*) [CommRing C]
    [Algebra k C] [CommRing A] [Algebra k A] [IsReduced A]
    (h : ∀ (p : Ideal A) [p.IsPrime], IsReduced (C ⊗[k] (A ⧸ p))) : IsReduced (C ⊗[k] A) := by
  classical
  refine ⟨fun x hx => ?_⟩
  refine eq_zero_of_forall_lTensor_eq_zero
    (fun p : {p : Ideal A // p.IsPrime} => (Ideal.Quotient.mkₐ k p.1).toLinearMap) ?_ x ?_
  · intro a ha
    have hmem : a ∈ nilradical A := by
      rw [nilradical_eq_sInf, Submodule.mem_sInf]
      intro J hJ
      have h1 := ha ⟨J, hJ⟩
      simpa [Ideal.Quotient.eq_zero_iff_mem] using h1
    exact IsReduced.eq_zero a (mem_nilradical.1 hmem)
  · intro p
    have := p.2
    have := h p.1
    have hF : ∀ w : C ⊗[k] A,
        Algebra.TensorProduct.map (AlgHom.id k C) (Ideal.Quotient.mkₐ k p.1) w =
          (Ideal.Quotient.mkₐ k p.1).toLinearMap.lTensor C w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul c a => simp
      | add u v hu hv => rw [map_add (f := _), map_add (f := _), hu, hv]
    rw [← hF]
    exact IsReduced.eq_zero _
      (hx.map (Algebra.TensorProduct.map (AlgHom.id k C) (Ideal.Quotient.mkₐ k p.1)))

theorem isReduced_field_tensor_domain {k : Type*} [Field k] [PerfectField k] (K A : Type*)
    [Field K] [Algebra k K] [CommRing A] [Algebra k A] [IsDomain A] [Algebra.FiniteType k A] :
    IsReduced (K ⊗[k] A) := by
  classical
  have hfp : Algebra.FinitePresentation k A := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  have hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Algebra.smoothLocus k A := by
    show Algebra.FormallySmooth k (Localization.AtPrime (⊥ : Ideal A))
    have hS : (⊥ : Ideal A).primeCompl = nonZeroDivisors A := by
      ext x
      simp [Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
    have hloc : IsLocalization (nonZeroDivisors A) (Localization.AtPrime (⊥ : Ideal A)) :=
      hS ▸ (inferInstance : IsLocalization (⊥ : Ideal A).primeCompl (Localization.AtPrime (⊥ : Ideal A)))
    have e1 : Algebra.EssFiniteType A (FractionRing A) := .of_isLocalization _ (nonZeroDivisors A)
    have e2 : Algebra.EssFiniteType k (FractionRing A) := .comp k A _
    exact (Algebra.FormallySmooth.iff_of_equiv ((IsLocalization.algEquiv (nonZeroDivisors A)
      (FractionRing A) (Localization.AtPrime (⊥ : Ideal A))).restrictScalars k)).1 inferInstance
  obtain ⟨v, ⟨f, rfl⟩, hv, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    hgen Algebra.isOpen_smoothLocus
  have hf0 : f ≠ 0 := by
    have := (PrimeSpectrum.mem_basicOpen f _).1 hv
    simpa using this
  have hsm : Algebra.Smooth k (Localization.Away f) :=
    Algebra.basicOpen_subset_smoothLocus_iff_smooth.1 hsub
  have hred : IsReduced (K ⊗[k] Localization.Away f) :=
    GlobalTheory.isReduced_of_smooth_of_isIntegrallyClosed K _
  have hinj : Function.Injective (algebraMap A (Localization.Away f)) :=
    IsLocalization.injective (Localization.Away f) (powers_le_nonZeroDivisors_of_noZeroDivisors hf0)
  exact isReduced_of_injective
    (Algebra.TensorProduct.map (AlgHom.id k K) (IsScalarTower.toAlgHom k A (Localization.Away f)))
    (Module.Flat.lTensor_preserves_injective_linearMap _ hinj)

theorem isReduced_field_tensor {k : Type*} [Field k] [PerfectField k] (K A : Type*)
    [Field K] [Algebra k K] [CommRing A] [Algebra k A] [IsReduced A] :
    IsReduced (K ⊗[k] A) := by
  apply IsReduced.tensorProduct_of_flat_of_forall_fg
  intro B hB
  have : IsReduced B := isReduced_of_injective B.val Subtype.val_injective
  have : Algebra.FiniteType k B := ⟨(Subalgebra.fg_top B).2 hB⟩
  refine isReduced_tensor_of_forall_prime K B (fun p _ => ?_)
  have : Algebra.FiniteType k (B ⧸ p) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k p)
      (Ideal.Quotient.mkₐ_surjective k p)
  exact isReduced_field_tensor_domain K (B ⧸ p)

theorem isReduced_tensor {k : Type*} [Field k] [PerfectField k] (A B : Type*)
    [CommRing A] [Algebra k A] [IsReduced A] [CommRing B] [Algebra k B] [IsReduced B] :
    IsReduced (A ⊗[k] B) := by
  refine isReduced_tensor_of_forall_prime A B (fun p _ => ?_)
  have : IsReduced (FractionRing (B ⧸ p) ⊗[k] A) := isReduced_field_tensor (FractionRing (B ⧸ p)) A
  have : IsReduced (A ⊗[k] FractionRing (B ⧸ p)) :=
    isReduced_of_injective (Algebra.TensorProduct.comm k A (FractionRing (B ⧸ p)))
      (Algebra.TensorProduct.comm k A (FractionRing (B ⧸ p))).injective
  exact isReduced_of_injective
    (Algebra.TensorProduct.map (AlgHom.id k A) (IsScalarTower.toAlgHom k (B ⧸ p) (FractionRing (B ⧸ p))))
    (Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective (B ⧸ p) _))

universe u

end GlobalTheory.ReducedAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueBaseChangeEqOfMem
open TensorProduct

namespace GlobalTheory

namespace FlatDescent

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  {N' : Type*} [AddCommGroup N'] [Module A N'] [Module B N'] [IsScalarTower A B N']

variable (A B N) in
def act : B ⊗[A] N →ₗ[B] N := LinearMap.liftBaseChange B (LinearMap.id : N →ₗ[A] N)

@[simp] theorem act_tmul (b : B) (n : N) : act A B N (b ⊗ₜ n) = b • n := by
  simp [act]

structure IsDescentDatum (θ : N →ₗ[B] B ⊗[A] N) : Prop where
  counit : ∀ n, act A B N (θ n) = n
  coassoc : ∀ n, (θ.restrictScalars A).lTensor B (θ n) = (TensorProduct.mk A B N 1).lTensor B (θ n)

def invariants (θ : N →ₗ[B] B ⊗[A] N) : Submodule A N :=
  LinearMap.ker (θ.restrictScalars A - TensorProduct.mk A B N 1)

@[simp] theorem mem_invariants {θ : N →ₗ[B] B ⊗[A] N} {n : N} :
    n ∈ invariants θ ↔ θ n = 1 ⊗ₜ n := by
  simp [invariants, sub_eq_zero]

variable (B) in
def canonical (M : Type*) [AddCommGroup M] [Module A M] :
    B ⊗[A] M →ₗ[B] B ⊗[A] (B ⊗[A] M) :=
  (TensorProduct.mk A B M 1).baseChange B

variable (B) in
theorem isDescentDatum_canonical (M : Type*) [AddCommGroup M] [Module A M] :
    IsDescentDatum (canonical (A := A) B M) := by
  constructor <;> intro x
  · induction x using TensorProduct.inductionOn with
    | tmul b m => simp [canonical, smul_tmul']
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction x using TensorProduct.inductionOn with
    | tmul b m => simp [canonical]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

variable (B) in
def extend (P : Submodule A N) : B ⊗[A] P →ₗ[B] N := LinearMap.liftBaseChange B P.subtype

@[simp] theorem extend_tmul (P : Submodule A N) (b : B) (n : P) :
    extend B P (b ⊗ₜ n) = b • (n : N) := by
  simp [extend]

theorem act_lTensor_subtype (P : Submodule A N) (x : B ⊗[A] P) :
    act A B N (P.subtype.lTensor B x) = extend B P x := by
  induction x using TensorProduct.inductionOn with
  | tmul b m => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem apply_extend (θ : N →ₗ[B] B ⊗[A] N) (x : B ⊗[A] invariants θ) :
    θ (extend B _ x) = (invariants θ).subtype.lTensor B x := by
  induction x using TensorProduct.inductionOn with
  | tmul b m => simp [mem_invariants.1 m.2, smul_tmul']
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem IsDescentDatum.bijective_extend [Module.Flat A B] {θ : N →ₗ[B] B ⊗[A] N}
    (h : IsDescentDatum θ) : Function.Bijective (extend B (invariants θ)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := B) _
      (invariants θ).injective_subtype
    rw [← apply_extend, hx, map_zero, map_zero]
  · intro n
    have hex := Module.Flat.lTensor_exact B
      (LinearMap.exact_subtype_ker_map (θ.restrictScalars A - TensorProduct.mk A B N 1))
    obtain ⟨x, hx⟩ := (hex (θ n)).1 (by
      rw [LinearMap.lTensor_sub, LinearMap.sub_apply, h.coassoc, sub_self])
    exact ⟨x, (act_lTensor_subtype (invariants θ) x).symm.trans
      ((congrArg (act A B N) hx).trans (h.counit n))⟩

theorem IsDescentDatum.isBaseChange [Module.Flat A B] {θ : N →ₗ[B] B ⊗[A] N}
    (h : IsDescentDatum θ) : IsBaseChange B (invariants θ).subtype :=
  IsBaseChange.of_equiv (LinearEquiv.ofBijective _ h.bijective_extend) fun n => by simp

section Amitsur

variable (B) (M : Type*) [AddCommGroup M] [Module A M]

def toInvariants : M →ₗ[A] invariants (canonical (A := A) B M) :=
  (TensorProduct.mk A B M 1).codRestrict _ fun m => by simp [canonical]

theorem bijective_toInvariants [Module.FaithfullyFlat A B] :
    Function.Bijective (toInvariants (A := A) B M) := by
  rw [← Module.FaithfullyFlat.lTensor_bijective_iff_bijective A B,
    ← Function.Bijective.of_comp_iff' (isDescentDatum_canonical (A := A) B M).bijective_extend]
  convert Function.bijective_id
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul b m => simp [toInvariants, smul_tmul']
  | add x y hx hy => simp_all

def amitsurDiff : B ⊗[A] M →ₗ[A] B ⊗[A] (B ⊗[A] M) :=
  (canonical B M).restrictScalars A - TensorProduct.mk A B (B ⊗[A] M) 1

@[simp] theorem amitsurDiff_tmul (b : B) (m : M) :
    amitsurDiff B M (b ⊗ₜ[A] m) =
      b ⊗ₜ[A] ((1 : B) ⊗ₜ[A] m) - (1 : B) ⊗ₜ[A] (b ⊗ₜ[A] m) := rfl

theorem amitsur_exact [Module.FaithfullyFlat A B] :
    Function.Injective (TensorProduct.mk A B M 1) ∧
      Function.Exact (TensorProduct.mk A B M 1) (amitsurDiff (A := A) B M) := by
  refine ⟨Module.FaithfullyFlat.tensorProduct_mk_injective M, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨m, hm⟩ := (bijective_toInvariants (A := A) B M).2 ⟨x, hx⟩
    exact ⟨m, congrArg Subtype.val hm⟩
  · rintro ⟨m, rfl⟩
    simp

end Amitsur

section Morphisms

variable {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']


variable (B) in
theorem bijective_baseChange_iff [Module.FaithfullyFlat A B] (g : M →ₗ[A] M') :
    Function.Bijective (g.baseChange B) ↔ Function.Bijective g :=
  Module.FaithfullyFlat.lTensor_bijective_iff_bijective A B g

end Morphisms

section Invertible

theorem invertible_of_isBaseChange [Module.FaithfullyFlat A B] {M : Type*} [AddCommGroup M]
    [Module A M] {j : M →ₗ[A] N} (hj : IsBaseChange B j) [Module.Invertible B N] :
    Module.Invertible A M := by
  have : Module.Finite A M := Descent.finite_of_isBaseChange hj
  have : Module.Projective A M := Descent.projective_of_isBaseChange hj
  let e : B ⊗[A] (Module.Dual A M ⊗[A] M) ≃ₗ[B] B ⊗[A] A :=
    AlgebraTensorModule.distribBaseChange A B _ _ ≪≫ₗ
      TensorProduct.congr (SymAlg.isBaseChange_dual hj).equiv hj.equiv ≪≫ₗ
        Module.Invertible.linearEquiv B N ≪≫ₗ (AlgebraTensorModule.rid A B B).symm
  have he : (contractLeft A M).baseChange B = e.toLinearMap := by
    ext ξ m
    apply (AlgebraTensorModule.rid A B B).injective
    simp [e, Module.Invertible.linearEquiv, hj.toDual_comp_apply, Algebra.algebraMap_eq_smul_one]
  refine ⟨(bijective_baseChange_iff B _).1 ?_⟩
  rw [he]
  exact e.bijective

variable (B) in
theorem IsDescentDatum.invertible_invariants [Module.FaithfullyFlat A B]
    {θ : N →ₗ[B] B ⊗[A] N} (h : IsDescentDatum θ) [Module.Invertible B N] :
    Module.Invertible A (invariants θ) :=
  invertible_of_isBaseChange h.isBaseChange


end Invertible

section Gluing



end Gluing

end FlatDescent

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOpenPartialHomeomorphAnalytic
namespace GlobalTheory.AffinePoints

open Topology Filter Set MvPolynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

theorem analyticAt_aevalTower {σ ι : Type*} [Fintype σ] [Fintype ι]
    (q : MvPolynomial ι (MvPolynomial σ 𝕜)) (w : (σ → 𝕜) × (ι → 𝕜)) :
    AnalyticAt 𝕜 (fun w : (σ → 𝕜) × (ι → 𝕜) =>
      (aevalTower (aeval w.1) w.2 : MvPolynomial ι (MvPolynomial σ 𝕜) →ₐ[𝕜] 𝕜) q) w := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    simp only [aevalTower_C]
    exact AnalyticAt.aeval_mvPolynomial (A := 𝕜) (f := fun w : (σ → 𝕜) × (ι → 𝕜) => w.1)
      (fun i => ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : σ => 𝕜) i).comp
        (ContinuousLinearMap.fst 𝕜 (σ → 𝕜) (ι → 𝕜))).analyticAt w) a
  | add P Q hP hQ => simp only [map_add (f := _)]; exact hP.add hQ
  | mul_X P i hP =>
    simp only [map_mul, aevalTower_X]
    exact hP.mul (((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι => 𝕜) i).comp
        (ContinuousLinearMap.snd 𝕜 (σ → 𝕜) (ι → 𝕜))).analyticAt w)

theorem hasDerivAt_aevalTower_line {R ι : Type*} [CommRing R] [Algebra 𝕜 R] [Fintype ι]
    (φ : R →ₐ[𝕜] 𝕜) (q : MvPolynomial ι R) (y v : ι → 𝕜) :
    HasDerivAt (fun t : 𝕜 => (aevalTower φ (y + t • v) : MvPolynomial ι R →ₐ[𝕜] 𝕜) q)
      (∑ i, (aevalTower φ y : MvPolynomial ι R →ₐ[𝕜] 𝕜) (pderiv i q) * v i) 0 := by
  classical
  induction q using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const (0 : 𝕜) (φ a)
  | add P Q hP hQ =>
    simp only [map_add (f := _), add_mul, Finset.sum_add_distrib]
    exact hP.add hQ
  | mul_X P i hP =>
    have hX : HasDerivAt (fun t : 𝕜 => y i + t * v i) (v i) 0 := by
      simpa using ((hasDerivAt_id (0 : 𝕜)).mul_const (v i)).const_add (y i)
    have h := hP.mul hX
    simp only [map_mul, aevalTower_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine HasDerivAt.congr_deriv h ?_
    have h1 : ∀ j, (aevalTower φ y : MvPolynomial ι R →ₐ[𝕜] 𝕜) (pderiv j (P * X i)) * v j =
        (aevalTower φ y : MvPolynomial ι R →ₐ[𝕜] 𝕜) (pderiv j P) * v j * y i +
        if i = j then (aevalTower φ y : MvPolynomial ι R →ₐ[𝕜] 𝕜) P * v j else 0 := by
      intro j
      rw [pderiv_mul, pderiv_X]
      by_cases hij : i = j
      · subst hij; simp; ring
      · simp [hij, Pi.single_eq_of_ne hij]; ring
    simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      ← Finset.sum_mul]
    simp

variable [CompleteSpace 𝕜] {A : Type*} [CommRing A] [Algebra 𝕜 A] {d : ℕ}

theorem exists_openPartialHomeomorph_analytic {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] (hdim : Module.finrank 𝕜 E = Module.finrank 𝕜 F) {Ψ : E → F} {x : E}
    (hΨ : AnalyticAt 𝕜 Ψ x) (hinj : Function.Injective (fderiv 𝕜 Ψ x)) :
    ∃ Φ : OpenPartialHomeomorph E F, (Φ : E → F) = Ψ ∧ x ∈ Φ.source ∧
      AnalyticOnNhd 𝕜 Φ.symm Φ.target := by
  haveI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  haveI : CompleteSpace F := FiniteDimensional.complete 𝕜 F
  have hsurj : Function.Surjective (fderiv 𝕜 Ψ x) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := (fderiv 𝕜 Ψ x : E →ₗ[𝕜] F))).mp hinj
  let Le := ContinuousLinearEquiv.ofBijective (fderiv 𝕜 Ψ x) (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj)
  have hLe : (Le : E →L[𝕜] F) = fderiv 𝕜 Ψ x := ContinuousLinearEquiv.coe_ofBijective _ _ _
  have hφ : HasStrictFDerivAt Ψ (Le : E →L[𝕜] F) x := by rw [hLe]; exact hΨ.hasStrictFDerivAt
  let Φ := hφ.toOpenPartialHomeomorph Ψ
  have hpS : x ∈ Φ.source := hφ.mem_toOpenPartialHomeomorph_source
  have hsymm : AnalyticAt 𝕜 Φ.symm (Φ x) :=
    Φ.analyticAt_symm' (i := Le) hpS hΨ hLe.symm
  obtain ⟨s, hs, hsan⟩ := hsymm.exists_mem_nhds_analyticOnNhd
  obtain ⟨T, hTs, hTo, hTp⟩ := mem_nhds_iff.mp hs
  refine ⟨(Φ.symm.restrOpen T hTo).symm, rfl, ⟨hpS, hTp⟩, fun z hz => hsan z (hTs hz.2)⟩

theorem exists_chart_of_etale (g : MvPolynomial (Fin d) 𝕜 →ₐ[𝕜] A) (hg : g.Etale)
    (p : A →ₐ[𝕜] 𝕜) :
    ∃ e : OpenPartialHomeomorph (A →ₐ[𝕜] 𝕜) (Fin d → 𝕜), p ∈ e.source ∧
      (e : (A →ₐ[𝕜] 𝕜) → Fin d → 𝕜) = coords g ∧
      ∀ a, AnalyticOnNhd 𝕜 (fun z => e.symm z a) e.target := by
  classical
  letI : Algebra (MvPolynomial (Fin d) 𝕜) A := g.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin d) 𝕜) A := hg
  haveI : IsScalarTower 𝕜 (MvPolynomial (Fin d) 𝕜) A :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  obtain ⟨ι, σ, _, _, P, hP⟩ := (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.1
    ‹Algebra.Etale (MvPolynomial (Fin d) 𝕜) A›).out
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite σ
  have hcard : Fintype.card σ = Fintype.card ι := by
    have := P.card_relations_le_card_vars_of_isFinite
    simp only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card] at this hP
    omega
  have hbij : Function.Bijective P.map :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨P.map_inj, hcard⟩
  let π : MvPolynomial ι (MvPolynomial (Fin d) 𝕜) →ₐ[𝕜] A := (aeval P.val).restrictScalars 𝕜
  have hπ : Function.Surjective π := P.aeval_val_surjective
  let ev : (Fin d → 𝕜) × (ι → 𝕜) → (MvPolynomial ι (MvPolynomial (Fin d) 𝕜) →ₐ[𝕜] 𝕜) :=
    fun w => aevalTower (aeval w.1) w.2
  let j : (A →ₐ[𝕜] 𝕜) → (Fin d → 𝕜) × (ι → 𝕜) := fun q => (coords g q, fun i => q (P.val i))
  have hjc : Continuous j :=
    (continuous_coords g).prodMk (continuous_pi fun _ => continuous_eval _)
  have hevj : ∀ q, ev (j q) = comap π q := by
    intro q
    refine MvPolynomial.algHom_ext' ?_ ?_
    · ext i
      simp [ev, j, π, coords, RingHom.algebraMap_toAlgebra]
    · intro i; simp [ev, j, π]
  have hker : ∀ a, π a = 0 ↔ a ∈ Ideal.span (range P.relation) := by
    intro a
    rw [P.span_range_relation_eq_ker]
    rw [P.ker_eq_ker_aeval_val]
    rfl
  have hex : ∀ w, (∀ r, ev w (P.relation r) = 0) → ∃ q, j q = w ∧ comap π q = ev w := by
    intro w hw
    obtain ⟨q, hq⟩ := exists_comap_eq_of_surjective π hπ (ev w) fun a ha => by
      have : Ideal.span (range P.relation) ≤ RingHom.ker (ev w) := by
        rw [Ideal.span_le]; rintro _ ⟨r, rfl⟩; exact hw r
      exact this ((hker a).1 ha)
    refine ⟨q, ?_, hq⟩
    ext i
    · simpa [ev, π, j, coords, RingHom.algebraMap_toAlgebra] using DFunLike.congr_fun hq (C (X i))
    · simpa [ev, π, j] using DFunLike.congr_fun hq (X i)
  have hjinj : Function.Injective j := by
    intro q q' h
    ext a
    obtain ⟨b, rfl⟩ := hπ a
    have := hevj q
    rw [h, hevj] at this
    exact (DFunLike.congr_fun this b).symm
  let Ψ : (Fin d → 𝕜) × (ι → 𝕜) → (Fin d → 𝕜) × (σ → 𝕜) :=
    fun w => (w.1, fun r => ev w (P.relation r))
  have hΨj : ∀ q, Ψ (j q) = (coords g q, 0) := by
    intro q
    ext r
    · rfl
    · change ev (j q) (P.relation r) = 0
      rw [hevj, comap_apply, (hker _).2 (Ideal.subset_span ⟨r, rfl⟩), map_zero]
  have hΨan : AnalyticAt 𝕜 Ψ (j p) :=
    analyticAt_fst.prod (analyticAt_pi_iff.2 fun r => analyticAt_aevalTower _ _)
  have hinj : Function.Injective (fderiv 𝕜 Ψ (j p)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨u, v⟩ huv
    have hline : HasDerivAt (fun t : 𝕜 => Ψ (j p + t • (u, v))) 0 0 := by
      have h1 : HasDerivAt (fun t : 𝕜 => j p + t • (u, v)) (u, v) 0 := by
        simpa using ((hasDerivAt_id (0 : 𝕜)).smul_const (u, v)).const_add (j p)
      have h2 : HasFDerivAt Ψ (fderiv 𝕜 Ψ (j p)) (j p + (0 : 𝕜) • (u, v)) := by
        simpa using hΨan.differentiableAt.hasFDerivAt
      have := h2.comp_hasDerivAt (0 : 𝕜) h1
      rwa [huv] at this
    have hu : u = 0 := by
      have h1 : HasDerivAt (fun t : 𝕜 => (j p).1 + t • u) u 0 := by
        simpa using ((hasDerivAt_id (0 : 𝕜)).smul_const u).const_add (j p).1
      have h2 := (ContinuousLinearMap.fst 𝕜 (Fin d → 𝕜) (σ → 𝕜)).hasFDerivAt.comp_hasDerivAt
        (0 : 𝕜) hline
      exact h1.unique h2
    subst hu
    have hv : ∀ r, ∑ i, ev (j p) (pderiv i (P.relation r)) * v i = 0 := by
      intro r
      have h1 := hasDerivAt_aevalTower_line (aeval (j p).1) (P.relation r) (j p).2 v
      have h2 := (((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : σ => 𝕜) r).comp
        (ContinuousLinearMap.snd 𝕜 (Fin d → 𝕜) (σ → 𝕜))).hasFDerivAt.comp_hasDerivAt (0 : 𝕜) hline)
      refine h1.unique ?_
      simpa [Function.comp_def, Ψ, ev] using h2
    have hdet : ((ev (j p)).toRingHom.mapMatrix P.jacobiMatrix).det ≠ 0 := by
      rw [← RingHom.map_det, hevj]
      have := (P.jacobian_isUnit.map p).ne_zero
      rw [P.jacobian_eq_jacobiMatrix_det, P.algebraMap_apply] at this
      exact this
    have hw : (fun s => v (P.map s)) = 0 := by
      refine Matrix.eq_zero_of_vecMul_eq_zero hdet ?_
      ext r
      rw [Pi.zero_apply, ← hv r, ← hbij.sum_comp]
      simp [Matrix.vecMul, dotProduct, P.jacobiMatrix_apply, mul_comm]
    have : v = 0 := by
      ext i
      obtain ⟨s, rfl⟩ := hbij.2 i
      exact congrFun hw s
    rw [this]; rfl
  obtain ⟨Φ, hΦ, hpS, hsymm⟩ := exists_openPartialHomeomorph_analytic
    (by simp [Module.finrank_prod, hcard]) hΨan hinj
  have hex' : ∀ z : Fin d → 𝕜, ∃ q : A →ₐ[𝕜] 𝕜, (z, 0) ∈ Φ.target →
      j q = Φ.symm (z, 0) ∧ comap π q = ev (Φ.symm (z, 0)) := by
    intro z
    by_cases hz : (z, 0) ∈ Φ.target
    · obtain ⟨q, hq⟩ := hex (Φ.symm (z, 0)) fun r => by
        have := congrFun (congrArg Prod.snd (Φ.right_inv hz)) r
        rwa [hΦ] at this
      exact ⟨q, fun _ => hq⟩
    · exact ⟨p, fun h => absurd h hz⟩
  choose s hs using hex'
  have han : ∀ a, AnalyticOnNhd 𝕜 (fun z => s z a) {z | (z, 0) ∈ Φ.target} := by
    intro a
    obtain ⟨b, rfl⟩ := hπ a
    have hop : IsOpen {z : Fin d → 𝕜 | (z, 0) ∈ Φ.target} :=
      Φ.open_target.preimage (continuous_id.prodMk continuous_const)
    refine AnalyticOnNhd.congr hop (f := fun z => ev (Φ.symm (z, 0)) b) ?_ ?_
    · intro z hz
      have h1 : AnalyticAt 𝕜 (fun z : Fin d → 𝕜 => Φ.symm (z, 0)) z :=
        AnalyticAt.comp (f := fun z : Fin d → 𝕜 => (z, (0 : σ → 𝕜))) (hsymm _ hz)
          (analyticAt_id.prod analyticAt_const)
      exact AnalyticAt.comp (f := fun z : Fin d → 𝕜 => Φ.symm (z, 0))
        (analyticAt_aevalTower b _) h1
    · intro z hz
      exact (DFunLike.congr_fun (hs z hz).2 b).symm
  have hmap : ∀ q, j q ∈ Φ.source → (coords g q, 0) ∈ Φ.target := by
    intro q hq
    have := Φ.map_source hq
    rwa [hΦ, hΨj] at this
  refine ⟨{ toFun := coords g
            invFun := s
            source := j ⁻¹' Φ.source
            target := {z | (z, 0) ∈ Φ.target}
            map_source' := hmap
            map_target' := fun z hz => ?_
            left_inv' := fun q hq => ?_
            right_inv' := fun z hz => ?_
            open_source := Φ.open_source.preimage hjc
            open_target := Φ.open_target.preimage (continuous_id.prodMk continuous_const)
            continuousOn_toFun := (continuous_coords g).continuousOn
            continuousOn_invFun := continuousOn_iff.2 fun a => (han a).continuousOn },
    hpS, rfl, han⟩
  · rw [mem_preimage, (hs z hz).1]; exact Φ.map_target hz
  · apply hjinj
    rw [(hs _ (hmap q hq)).1, ← hΨj, ← hΦ, Φ.left_inv hq]
  · have := Φ.right_inv hz
    rw [← (hs z hz).1, hΦ, hΨj] at this
    exact congrArg Prod.fst this

end GlobalTheory.AffinePoints
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.MvPolynomialIsHomogeneousComapWeighted
open TensorProduct Module

namespace GlobalTheory.GaloisDescent

section Decomposition

variable {ι M M' σ τ : Type*} [DecidableEq ι] [AddCommMonoid M] [AddCommMonoid M']
  [SetLike σ M] [AddSubmonoidClass σ M] [SetLike τ M'] [AddSubmonoidClass τ M']

end Decomposition

section Ideals

variable {K L A B G : Type*} [Field K] [Field L] [Algebra K L] [Ring A] [Ring B] [Algebra K A]
  [Algebra K B] [Algebra L B] [IsScalarTower K L B] {j : A →ₐ[K] B}

theorem ideal_map_comap_of_span (I : Ideal B) (N : Submodule K A)
    (h : Submodule.span L (j.toLinearMap '' N) = I.restrictScalars L) :
    (I.comap j).map j = I := by
  refine le_antisymm Ideal.map_comap_le fun x hx => ?_
  have hle : Submodule.span L (j.toLinearMap '' N) ≤ ((I.comap j).map j).restrictScalars L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    refine Ideal.mem_map_of_mem j ?_
    exact h.le (Submodule.subset_span ⟨a, ha, rfl⟩)
  exact hle (h.ge hx)

theorem ideal_map_comap_of_stable (hj : IsBaseChange L j.toLinearMap) (s : G → L →+* L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    (φ : G → B →+ B) (hφ : ∀ g l a, φ g (l • j a) = s g l • j a)
    (I : Ideal B) (hI : ∀ g, ∀ x ∈ I, φ g x ∈ I) : (I.comap j).map j = I :=
  ideal_map_comap_of_span I _ (span_image_comap_eq hj s hs φ hφ (I.restrictScalars L) hI)

section Graded

variable {ι σ τ : Type*} [DecidableEq ι] [AddMonoid ι] [SetLike σ A] [AddSubmonoidClass σ A]
  [SetLike τ B] [AddSubmonoidClass τ B] (𝒜 : ι → σ) (ℬ : ι → τ) [GradedRing 𝒜] [GradedRing ℬ]

end Graded

end Ideals

section Tensor

open Algebra.TensorProduct

variable {K L A G : Type*} [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A]

end Tensor

section Polynomial

open MvPolynomial

variable {K L G σ : Type*} [Field K] [Field L] [Algebra K L]


end Polynomial

end GlobalTheory.GaloisDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasChartsOfForallIsAffineOpen
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp)

namespace GlobalTheory.NatFun

variable {k : Type} [CommRing k]

section Points

scoped instance sectionsAlgebra (X : Over (Spec (CommRingCat.of k))) (U : X.left.Opens) :
    Algebra k Γ(X.left, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appLE ⊤ U le_top).hom.toAlgebra

theorem algebraMap_sections (X : Over (Spec (CommRingCat.of k))) (U : X.left.Opens) :
    algebraMap k Γ(X.left, U) =
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appLE ⊤ U le_top).hom := rfl

variable {X : Over (Spec (CommRingCat.of k))}
variable {A B C : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
  [CommRing C] [Algebra k C]

theorem spMap_injective : Function.Injective (spMap : (A →ₐ[k] B) → (sp B ⟶ sp A)) := by
  intro φ ψ h
  have h1 : (spMap φ).left = (spMap ψ).left := by rw [h]
  exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom (Spec.map_injective h1))

theorem spMap_surjective : Function.Surjective (spMap : (A →ₐ[k] B) → (sp B ⟶ sp A)) := by
  intro m
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (R := CommRingCat.of A) (S := CommRingCat.of B) m.left
  have h : CommRingCat.ofHom (algebraMap k A) ≫ φ = CommRingCat.ofHom (algebraMap k B) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ]
    exact Over.w m
  exact ⟨⟨φ.hom, fun c => congr(($h).hom c)⟩, Over.OverMorphism.ext hφ⟩

def affinePoint {U : X.left.Opens} (hU : IsAffineOpen U) : sp Γ(X.left, U) ⟶ X :=
  Over.homMk hU.fromSpec (by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec X.hom
      (isAffineOpen_top (Spec (CommRingCat.of k))) hU (le_top : U ≤ X.hom ⁻¹ᵁ ⊤)
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    change hU.fromSpec ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k Γ(X.left, U)))
    rw [← h, algebraMap_sections, CommRingCat.ofHom_hom, Spec.map_comp])

end Points

section Families

abbrev AlgClass (k : Type) [CommRing k] : Type 1 :=
  ∀ (A : Type) [CommRing A] [Algebra k A], Prop

variable {𝒯 𝒯' : AlgClass k} {X : Over (Spec (CommRingCat.of k))}



section
variable (A : Type) [CommRing A] [Algebra k A] (hA : 𝒯 A) (x : sp A ⟶ X)

end




end Families

end GlobalTheory.NatFun
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsBigOPowIffIteratedFDerivEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EqExpFderiv
universe u_1

namespace GlobalTheory.ExpOfFrechetDerivative

theorem eq_exp_fderiv {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ}
    (hd : DifferentiableAt ℂ f (0 : E)) (h0 : f (0 : E) ≠ (0 : ℂ))
    (hmul : ∀ x y : E, f (x + y) = f x * f y) (z : E) :
    f z = Complex.exp ((fderiv ℂ f (0 : E) : E → ℂ) z) := by
  set L := fderiv ℂ f (0 : E) with hL

  have hf0 : f 0 = 1 := by
    have h00 := hmul 0 0
    rw [add_zero] at h00
    have hfac : f 0 * (f 0 - 1) = 0 := by rw [mul_sub, mul_one, ← h00, sub_self]
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd h h0
    · exact sub_eq_zero.mp h

  have hD : ∀ x : E, HasFDerivAt f (f x • L) x := by
    intro x
    have h1 : HasFDerivAt f L (x - x) := by
      rw [sub_self]
      exact hd.hasFDerivAt
    have h2 : HasFDerivAt (fun y : E => f (y - x)) L x := by
      have h := h1.comp (f := fun y : E => y - x) x ((hasFDerivAt_id x).sub_const x)
      rw [ContinuousLinearMap.comp_id] at h
      exact h
    refine (h2.const_mul (f x)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    show f y = f x * f (y - x)
    rw [← hmul, add_sub_cancel]

  have hE : ∀ y : E, HasFDerivAt (fun y => f y * Complex.exp (-(L y)))
      (f y • (Complex.exp (-(L y)) • -L) + Complex.exp (-(L y)) • (f y • L)) y :=
    fun y => (hD y).mul (L.hasFDerivAt.neg.cexp)
  have hzero : ∀ y, fderiv ℂ (fun y => f y * Complex.exp (-(L y))) y = 0 := by
    intro y
    rw [(hE y).fderiv]
    ext v
    simp only [add_apply, smul_apply, neg_apply, zero_apply, smul_eq_mul]
    ring
  have hc := is_const_of_fderiv_eq_zero (fun y => (hE y).differentiableAt) hzero z 0
  simp only [map_zero, neg_zero, Complex.exp_zero, mul_one, hf0] at hc
  calc f z = f z * Complex.exp (-(L z)) * Complex.exp (L z) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = Complex.exp (L z) := by rw [hc, one_mul]

end GlobalTheory.ExpOfFrechetDerivative
end

open Filter Topology Asymptotics Complex
open scoped Real ComplexConjugate

namespace GlobalTheory.Doubling

noncomputable section

section Rigidity

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup G]
  [NormedSpace ℂ G]

end Rigidity

section Series

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup G]
  [NormedSpace ℂ G]

def quadPart (h : E → G) (z : E) : G := (2 : ℂ)⁻¹ • iteratedFDeriv ℂ 2 h 0 fun _ => z

end Series

section Character

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem eq_cexp_fderiv_of_map_add {f : E → ℂ} (hf : DifferentiableAt ℂ f 0) (h0 : f 0 ≠ 0)
    (hm : ∀ x y, f (x + y) = f x * f y) (z : E) : f z = cexp (fderiv ℂ f 0 z) := by
  first
  | exact @_root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv
  | exact _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv
  | (apply _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv ..)

end Character

section Alternating

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

end Alternating

section Lattice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]

end Lattice

end

end GlobalTheory.Doubling
end
