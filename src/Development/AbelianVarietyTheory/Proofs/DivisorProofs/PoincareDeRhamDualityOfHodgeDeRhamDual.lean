module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationOfOrthogonalPerfectPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorGluedPullbackBundlePower

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPairingPerfectOrthogonalOfKernelsZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingIsPerfectAbelianSchemesBothKernelsZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPolarizationPerfectPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationOrthogonalPerfect
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareCrystalPairingSwapEqNegFlip
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareCrystalPairingSwapEqNegFlip
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem pairing_swap_eq_neg_flip : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → AbDual.IsCorrForm (dp0 R) (𝟙 _) B A (AbDual.swap P) (-φ.flip) := by
  intro R _ A B _ _ P _ φ H
  exact SymmPoincare.isCorrForm_swap H

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareCrystalPairingSwapEqNegFlipStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareCrystalPairing_swap_eq_neg_flip : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → AbDual.IsCorrForm (dp0 R) (𝟙 _) B A (AbDual.swap P) (-φ.flip) := by
  first | exact @GlobalTheory.pairing_swap_eq_neg_flip | exact GlobalTheory.pairing_swap_eq_neg_flip | (intros; apply GlobalTheory.pairing_swap_eq_neg_flip <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationOrthogonalPerfect
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.PoincareKer.mem_fil_left : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] [Nontrivial R]
    (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B →
    SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left,
    AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ →
    ∀ x : HdR A, (∀ y ∈ Fil B, φ x y = 0) → x ∈ Fil A := by
  intro hHdR R _ _ A B _ _ g hA hB hgA hgB P hP φ hφ x hx
  have hφ' := GlobalTheory.T.poincareCrystalPairing_swap_eq_neg_flip R A B P hP.isLB φ hφ
  refine GlobalTheory.T.mem_hodgeFiltration_of_orthogonal_perfectPairing hHdR R B A g hB hA hgB hgA (AbDual.swap P) hP.swap (-φ.flip) hφ' x ?_
  intro y hy
  simp [hx y hy]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationOrthogonalPerfectStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_filtration_orthogonal_perfect : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] [Nontrivial R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → ∀ x : HdR A, (∀ y ∈ Fil B, φ x y = 0) → x ∈ Fil A := by
  first | exact @GlobalTheory.PoincareKer.mem_fil_left | exact GlobalTheory.PoincareKer.mem_fil_left | (intros; apply GlobalTheory.PoincareKer.mem_fil_left <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerfPairDualOfHalfDimKernelConditions
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerfPairDualOfHalfDimKernelConditions
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PerfPairField

open Module

theorem eq_zero_of_mem_of_flip_ker {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (φ : V →ₗ[K] W →ₗ[K] K) (A : Submodule K V) (B : Submodule K W)
    (hdim : finrank K A + finrank K B ≤ finrank K W)
    (h : ∀ y, (∀ x ∈ A, φ x y = 0) → y ∈ B) :
    ∀ x ∈ A, φ x = 0 → x = 0 := by
  intro x hx hφx
  set T : W →ₗ[K] Module.Dual K A := (φ.domRestrict A).flip with hT
  have hker : LinearMap.ker T ≤ B := by
    intro y hy
    apply h y
    intro a ha
    have := LinearMap.congr_fun (LinearMap.mem_ker.mp hy) ⟨a, ha⟩
    simpa [hT] using this
  have hrn := LinearMap.finrank_range_add_finrank_ker T
  have hkb := Submodule.finrank_mono hker
  have hdA : finrank K (Module.Dual K A) = finrank K A := Subspace.dual_finrank_eq
  have htop : LinearMap.range T = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_le (LinearMap.range T)
    omega
  have hx0 : (⟨x, hx⟩ : A) = 0 := by
    rw [← Module.forall_dual_apply_eq_zero_iff K]
    intro f
    obtain ⟨y, rfl⟩ : f ∈ LinearMap.range T := htop ▸ Submodule.mem_top
    simp [hT, hφx]
  simpa using congrArg Subtype.val hx0

end GlobalTheory.PerfPairField

open Module in
theorem GlobalTheory.PerfPairField.isPerfPair_of_kernel_conditions : ∀ (k : Type) [Field k] (M N : Type 1) [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N] [FiniteDimensional k M] [FiniteDimensional k N] (F : Submodule k M) (F' : Submodule k N) (g : ℕ), Module.finrank k M = 2 * g → Module.finrank k N = 2 * g → Module.finrank k F = g → Module.finrank k F' = g → ∀ φ : Module.Dual k M →ₗ[k] Module.Dual k N →ₗ[k] k, (∀ x, (∀ y ∈ F'.dualAnnihilator, φ x y = 0) → x ∈ F.dualAnnihilator) → (∀ y, (∀ x ∈ F.dualAnnihilator, φ x y = 0) → y ∈ F'.dualAnnihilator) → φ.IsPerfPair := by
  intro k _ M N _ _ _ _ _ _ F F' g hM hN hF hF' φ h1 h2
  have eM := Subspace.finrank_add_finrank_dualAnnihilator_eq F
  have eN := Subspace.finrank_add_finrank_dualAnnihilator_eq F'
  have dM : finrank k (Module.Dual k M) = 2 * g := by rw [Subspace.dual_finrank_eq, hM]
  have dN : finrank k (Module.Dual k N) = 2 * g := by rw [Subspace.dual_finrank_eq, hN]
  apply LinearMap.IsPerfPair.of_injective
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hA : x ∈ F.dualAnnihilator := h1 x (fun y _ => by simp [hx])
    exact GlobalTheory.PerfPairField.eq_zero_of_mem_of_flip_ker φ F.dualAnnihilator F'.dualAnnihilator
      (by omega) h2 x hA hx
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hB : y ∈ F'.dualAnnihilator := h2 y (fun x _ => by
      have := LinearMap.congr_fun hy x
      simpa using this)
    exact GlobalTheory.PerfPairField.eq_zero_of_mem_of_flip_ker φ.flip F'.dualAnnihilator F.dualAnnihilator
      (by omega) (fun x hx => h1 x (fun y hy => by simpa using hx y hy)) y hB hy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerfPairDualOfHalfDimKernelConditionsStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPerfPair_dual_of_half_dim_kernel_conditions : ∀ (k : Type) [Field k] (M N : Type 1) [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N] [FiniteDimensional k M] [FiniteDimensional k N] (F : Submodule k M) (F' : Submodule k N) (g : ℕ), Module.finrank k M = 2 * g → Module.finrank k N = 2 * g → Module.finrank k F = g → Module.finrank k F' = g → ∀ φ : Module.Dual k M →ₗ[k] Module.Dual k N →ₗ[k] k, (∀ x, (∀ y ∈ F'.dualAnnihilator, φ x y = 0) → x ∈ F.dualAnnihilator) → (∀ y, (∀ x ∈ F.dualAnnihilator, φ x y = 0) → y ∈ F'.dualAnnihilator) → φ.IsPerfPair := by
  first | exact @GlobalTheory.PerfPairField.isPerfPair_of_kernel_conditions | exact GlobalTheory.PerfPairField.isPerfPair_of_kernel_conditions | (intros; apply GlobalTheory.PerfPairField.isPerfPair_of_kernel_conditions <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPolarizationPerfectPairing
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FieldPerf

theorem finrank_of_rankAtStalk {k : Type} [Field k] {M : Type*} [AddCommGroup M] [Module k M]
    [Module.Finite k M] {n : ℕ} (h : ∀ p : PrimeSpectrum k, Module.rankAtStalk M p = n) :
    Module.finrank k M = n := by
  have e := h ⟨⊥, Ideal.isPrime_bot⟩
  rwa [Module.rankAtStalk_eq_finrank_of_free] at e

theorem isPerfPair : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[k] HdR B →ₗ[k] k, AbDual.IsCorrForm (dp0 k) (𝟙 _) A B P φ → φ.IsPerfPair := by
  intro H k _ A B _ _ g hA hB gA gB P hP φ hφ
  obtain ⟨HF, HH, -⟩ := GlobalTheory.T.abelianSchemeDeRham_free_hodgeSequence_baseChange H
  obtain ⟨fA, -, rA⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim HF hA gA
  obtain ⟨fB, -, rB⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim HF hB gB
  obtain ⟨-, -, fFA, -, rFA⟩ := HH k A g hA gA
  obtain ⟨-, -, fFB, -, rFB⟩ := HH k B g hB gB
  exact GlobalTheory.T.isPerfPair_dual_of_half_dim_kernel_conditions k (primDR A) (primDR B) (PrimitiveSubmodule A) (PrimitiveSubmodule B) g
    (finrank_of_rankAtStalk rA) (finrank_of_rankAtStalk rB)
    (finrank_of_rankAtStalk rFA) (finrank_of_rankAtStalk rFB) φ
    (GlobalTheory.T.hodge_filtration_orthogonal_perfect H k A B g hA hB gA gB P hP φ hφ)
    (GlobalTheory.T.mem_hodgeFiltration_of_orthogonal_perfectPairing H k A B g hA hB gA gB P hP φ hφ)

end GlobalTheory.FieldPerf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPolarizationPerfectPairingStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_polarization_perfect_pairing : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[k] HdR B →ₗ[k] k, AbDual.IsCorrForm (dp0 k) (𝟙 _) A B P φ → φ.IsPerfPair := by
  first | exact @GlobalTheory.FieldPerf.isPerfPair | exact GlobalTheory.FieldPerf.isPerfPair | (intros; apply GlobalTheory.FieldPerf.isPerfPair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerfectPairOfGeometricFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerfectPairOfGeometricFibres
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairFibres

section Algebra

open Module TensorProduct GlobalTheory.PrincipalPolPairing

variable {R Ω : Type} [CommRing R] [CommRing Ω] [Algebra R Ω]
  {M N M' N' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M'] [Module Ω M'] [AddCommGroup N'] [Module Ω N']
  {f : M →ₛₗ[algebraMap R Ω] M'} {f' : N →ₛₗ[algebraMap R Ω] N'}

theorem subsingleton_coker₂ [Module.Finite R M] [Module.Projective R M] [Module.Finite R N]
    [Module.Projective R N] (hf : Function.Bijective (GlobalTheory.DeRham.liftSemi f))
    (hf' : Function.Bijective (GlobalTheory.DeRham.liftSemi f')) (θ : Dual R M →ₗ[R] N)
    (φ' : Dual Ω M' →ₗ[Ω] Dual Ω (Dual Ω N')) (hφ : Function.Surjective φ')
    (h : ∀ (x : Dual R M) (y : Dual R N) (x' : Dual Ω M') (y' : Dual Ω N'),
      (∀ c, x' (f c) = algebraMap R Ω (x c)) →
      (∀ c, y' (f' c) = algebraMap R Ω (y c)) → φ' x' y' = algebraMap R Ω (y (θ x))) :
    Subsingleton (Ω ⊗[R] (N ⧸ LinearMap.range θ)) := by
  let e := LinearEquiv.ofBijective _ hf'
  haveI : Module.Finite Ω N' := Module.Finite.equiv e
  haveI : Module.Projective Ω N' := Module.Projective.of_equiv e
  let π : N' →ₗ[Ω] Ω ⊗[R] (N ⧸ LinearMap.range θ) :=
    (LinearMap.range θ).mkQ.baseChange Ω ∘ₗ e.symm.toLinearMap
  have hπ : Function.Surjective π :=
    (LinearMap.baseChange_surjective Ω (Submodule.mkQ_surjective _)).comp e.symm.surjective
  let θ' : Dual Ω M' →ₗ[Ω] N' := (Module.evalEquiv Ω N').symm.toLinearMap ∘ₗ φ'
  have hθ' : Function.Surjective θ' := (Module.evalEquiv Ω N').symm.surjective.comp hφ
  have k : π ∘ₗ θ' = 0 := by
    refine ext_corr hf fun x x' hx ↦ ?_
    have e₁ : θ' x' = f' (θ x) := by
      apply (Module.evalEquiv Ω N').injective
      refine ((Module.evalEquiv Ω N').apply_symm_apply _).trans (ext_corr hf' fun y y' hy ↦ ?_)
      rw [h x y x' y' hx hy, ← hy]
      rfl
    have e₂ : f' (θ x) = e (1 ⊗ₜ θ x) := (one_smul Ω (f' _)).symm
    rw [LinearMap.comp_apply, e₁, e₂]
    simp only [π, LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply, LinearMap.baseChange_tmul,
      LinearMap.zero_apply, Submodule.mkQ_apply]
    rw [(Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self θ x), tmul_zero]
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨a, rfl⟩ := (hπ.comp hθ') a
  obtain ⟨b, rfl⟩ := (hπ.comp hθ') b
  exact (LinearMap.congr_fun k a).trans (LinearMap.congr_fun k b).symm

end Algebra

open Module

theorem isPerfPair_of_fibres₂ : ∀ (R : Type) [CommRing R] (M N : Type 1) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N] (φ : Module.Dual R M →ₗ[R] Module.Dual R N →ₗ[R] R), (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω], ∃ (M' N' : Type 1) (_ : AddCommGroup M') (_ : Module Ω M') (_ : AddCommGroup N') (_ : Module Ω N') (f : M →ₛₗ[algebraMap R Ω] M') (f' : N →ₛₗ[algebraMap R Ω] N') (φ' : Module.Dual Ω M' →ₗ[Ω] Module.Dual Ω N' →ₗ[Ω] Ω), Function.Bijective (liftSemi f) ∧ Function.Bijective (liftSemi f') ∧ φ'.IsPerfPair ∧ ∀ (x : Module.Dual R M) (x' : Module.Dual Ω M') (y : Module.Dual R N) (y' : Module.Dual Ω N'), (∀ c, x' (f c) = algebraMap R Ω (x c)) → (∀ c, y' (f' c) = algebraMap R Ω (y c)) → φ' x' y' = algebraMap R Ω (φ x y)) → φ.IsPerfPair := by
  intro R _ M N _ _ _ _ _ _ _ _ φ h
  let E := Module.evalEquiv R M
  let E' := Module.evalEquiv R N
  have ev (z : Dual R (Dual R M)) (y : Dual R M) : y (E.symm z) = z y :=
    LinearMap.congr_fun (E.apply_symm_apply z) y
  have ev' (z : Dual R (Dual R N)) (y : Dual R N) : y (E'.symm z) = z y :=
    LinearMap.congr_fun (E'.apply_symm_apply z) y
  have s₁ : Function.Surjective (E'.symm.toLinearMap ∘ₗ φ) := by
    rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
    refine GlobalTheory.PrincipalPolPairing.subsingleton_of_fibres (R := R) fun p ↦ ?_
    obtain ⟨M', N', _, _, _, _, f, f', φ', hf, hf', hp, k⟩ := h (AlgebraicClosure p.asIdeal.ResidueField)
    exact subsingleton_coker₂ hf hf' _ φ' hp.bijective_left.2 fun x y x' y' hx hy ↦ by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ev', k x x' y y' hx hy]
  have s₂ : Function.Surjective (E.symm.toLinearMap ∘ₗ φ.flip) := by
    rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
    refine GlobalTheory.PrincipalPolPairing.subsingleton_of_fibres (R := R) fun p ↦ ?_
    obtain ⟨M', N', _, _, _, _, f, f', φ', hf, hf', hp, k⟩ := h (AlgebraicClosure p.asIdeal.ResidueField)
    exact subsingleton_coker₂ hf' hf _ φ'.flip hp.bijective_right.2 fun y x y' x' hy hx ↦ by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ev, LinearMap.flip_apply, LinearMap.flip_apply,
        k x x' y y' hx hy]
  refine LinearMap.IsPerfPair.of_bijective _ ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun z ↦ ?_⟩
  · refine LinearMap.ext fun c ↦ ?_
    obtain ⟨y, rfl⟩ := s₂ c
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ev, LinearMap.flip_apply, hx]
    rfl
  · obtain ⟨x, hx⟩ := s₁ (E'.symm z)
    exact ⟨x, E'.symm.injective hx⟩

end GlobalTheory.PairFibres
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerfectPairOfGeometricFibresStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPerfectPair_of_geometric_fibres : ∀ (R : Type) [CommRing R] (M N : Type 1) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N] (φ : Module.Dual R M →ₗ[R] Module.Dual R N →ₗ[R] R), (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω], ∃ (M' N' : Type 1) (_ : AddCommGroup M') (_ : Module Ω M') (_ : AddCommGroup N') (_ : Module Ω N') (f : M →ₛₗ[algebraMap R Ω] M') (f' : N →ₛₗ[algebraMap R Ω] N') (φ' : Module.Dual Ω M' →ₗ[Ω] Module.Dual Ω N' →ₗ[Ω] Ω), Function.Bijective (liftSemi f) ∧ Function.Bijective (liftSemi f') ∧ φ'.IsPerfPair ∧ ∀ (x : Module.Dual R M) (x' : Module.Dual Ω M') (y : Module.Dual R N) (y' : Module.Dual Ω N'), (∀ c, x' (f c) = algebraMap R Ω (x c)) → (∀ c, y' (f' c) = algebraMap R Ω (y c)) → φ' x' y' = algebraMap R Ω (φ x y)) → φ.IsPerfPair := by
  first | exact @GlobalTheory.PairFibres.isPerfPair_of_fibres₂ | exact GlobalTheory.PairFibres.isPerfPair_of_fibres₂ | (intros; apply GlobalTheory.PairFibres.isPerfPair_of_fibres₂ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingIsPerfectAbelianSchemesBothKernelsZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AbDual.isPerfPair_of_abelianHodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → φ.IsPerfPair := by
  intro H R _ A B _ _ g hA hB hgA hgB P hP φ hφ
  obtain ⟨Fr, -, BC⟩ := GlobalTheory.T.abelianSchemeDeRham_free_hodgeSequence_baseChange H
  obtain ⟨fA, pA, -⟩ := Published.AbelianDeRham.Free.prim Fr hA hgA
  obtain ⟨fB, pB, -⟩ := Published.AbelianDeRham.Free.prim Fr hB hgB
  refine GlobalTheory.T.isPerfectPair_of_geometric_fibres R (primDR A) (primDR B) φ ?_
  intro Ω _ _ _
  have iA := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback A (spMap (algebraMap R Ω))
  have iB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback B (spMap (algebraMap R Ω))
  obtain ⟨h, h₁, h₂⟩ := AbDual.exists_prod_pullback iA iB
  have hP' := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hP.isLB h
  have perf' := AbDual.IsPerfect.baseChange iA iB h₁ h₂ hP' (Cris.ChernExists.lbIso_refl hP') hP
  obtain ⟨φ', hφ', hcorr⟩ := hφ.pull hP.isLB (Published.AbelianDeRham.bcMor iA) (Published.AbelianDeRham.bcMor iB) h₁ h₂ hP'
    (Cris.ChernExists.lbIso_refl hP')
  have hA' := isAbelianScheme_pullback_obj (spMap (algebraMap R Ω)) A hA
  have hB' := isAbelianScheme_pullback_obj (spMap (algebraMap R Ω)) B hB
  have hgA' : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R Ω))).obj A).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hgA
  have hgB' : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R Ω))).obj B).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hgB
  exact ⟨primDR _, primDR _, inferInstance, inferInstance, inferInstance, inferInstance,
    (Published.AbelianDeRham.bcMor iA).pull, (Published.AbelianDeRham.bcMor iB).pull, φ',
    (BC R A g hA hgA Ω _ _ iA).1, (BC R B g hB hgB Ω _ _ iB).1,
    GlobalTheory.T.de_rham_polarization_perfect_pairing H Ω _ _ g hA' hB' hgA' hgB' _ perf' φ' hφ', fun x x' y y' hx hy ↦ hcorr x x' y y' hx hy⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingIsPerfectAbelianSchemesBothKernelsZeroStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_isPerfect_abelianSchemes_both_kernels_zero : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → φ.IsPerfPair := by
  first | exact @GlobalTheory.AbDual.isPerfPair_of_abelianHodgeDeRham | exact GlobalTheory.AbDual.isPerfPair_of_abelianHodgeDeRham | (intros; apply GlobalTheory.AbDual.isPerfPair_of_abelianHodgeDeRham <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPairingPerfectOrthogonalOfKernelsZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.PtExt.perfect_and_orthogonal : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → φ.IsPerfPair ∧ ∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0 := by
  intro hHdR R _ A B _ _ g hA hB hgA hgB P hP φ hφ
  exact ⟨GlobalTheory.T.pairing_isPerfect_abelianSchemes_both_kernels_zero hHdR R A B g hA hB hgA hgB P hP φ hφ,
    GlobalTheory.T.hodgeFiltrations_orthogonal_lineBundlePairing_product hHdR R A B g hA hB hgA hgB P hP.isLB φ hφ⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPairingPerfectOrthogonalOfKernelsZeroStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_pairing_perfect_and_hodge_filtration_isotropic : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → φ.IsPerfPair ∧ ∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0 := by
  first | exact @GlobalTheory.PtExt.perfect_and_orthogonal | exact GlobalTheory.PtExt.perfect_and_orthogonal | (intros; apply GlobalTheory.PtExt.perfect_and_orthogonal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareDeRhamDualityOfHodgeDeRhamDual
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PoincareDeRhamDualityProof

theorem poincareDeRhamDuality_of_hodge (H : GlobalTheory.Published.AbelianHodgeDeRham) (D : GlobalTheory.Published.DualAbelianScheme) :
    GlobalTheory.Published.PoincareDeRhamDuality := by
  intro R _ A B _ _ g hA hB hg hg' P hP φ hφ
  exact GlobalTheory.T.deRham_pairing_perfect_and_hodge_filtration_isotropic H R A B g hA hB hg hg' P
    (GlobalTheory.Published.PoincareDeRhamDuality.Test.isPerfect_of_isDual D hA hP) φ hφ

end GlobalTheory.PoincareDeRhamDualityProof
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareDeRhamDualityOfHodgeDeRhamDualStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareDeRhamDuality_of_hodgeDeRham_dual : GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.PoincareDeRhamDuality := by
  first | exact @GlobalTheory.PoincareDeRhamDualityProof.poincareDeRhamDuality_of_hodge | exact GlobalTheory.PoincareDeRhamDualityProof.poincareDeRhamDuality_of_hodge | (intros; apply GlobalTheory.PoincareDeRhamDualityProof.poincareDeRhamDuality_of_hodge <;> assumption)
end
