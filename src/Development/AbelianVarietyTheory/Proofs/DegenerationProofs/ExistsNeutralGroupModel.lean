module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGrpObjOfStrictBirationalLaw
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeakNeronModelBirationalGroupLaw
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStrictModelOfBirational
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothOfDefectZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnramifiedIdealLocusCharacterizationStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothFreeAwayStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothOfDefectZeroStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeakNeronModelBirationalGroupLawStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weakNeronModel_birational_groupLaw : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (n : ℕ) (M : Fin n → Model R A), (∀ i, (M i).Irr) → WeakNeron M → ∃ N : Model R A, BirLaw N ∧ ∃ c : ℕ, 1 ≤ c ∧ ∀ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso N N (transl (a ^ c)).hom := by
  first | exact @GlobalTheory.SS.NeutralModel.exists_birLaw | exact GlobalTheory.SS.NeutralModel.exists_birLaw | (intros; apply GlobalTheory.SS.NeutralModel.exists_birLaw <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGrpObjOfStrictBirationalLawStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_grpObj_of_strictBirationalLaw : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, Strict M → ∃ (G : Model R A) (_ : GrpObj G.Y), SmConn G.Y ∧ IsMonHom G.e.hom ∧ ∀ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso M M (transl a).hom → ∃ s : 𝟙_ (Over (Sp R)) ⟶ G.Y, spMap (algebraMap R K) ≫ s.left = a.left ≫ G.j := by
  first | exact @GlobalTheory.SS.exists_grpObj_of_strict | exact GlobalTheory.SS.exists_grpObj_of_strict | (intros; apply GlobalTheory.SS.exists_grpObj_of_strict <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeakNeronModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmoothFlatAlgebraFiniteCoverDecomp
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DefectBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DefectBounded
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem exists_pow_factor_free {B S M M' : Type} [CommRing B] [CommRing S] [Algebra B S] (b : B)
    [IsLocalization (Submonoid.powers b) S] [AddCommGroup M] [Module B M] [Module.FinitePresentation B M]
    [AddCommGroup M'] [Module B M'] [Module S M'] [IsScalarTower B S M'] [Module.Projective S M']
    (f : M →ₗ[B] M') [IsLocalizedModule (Submonoid.powers b) f] :
    ∃ (c n : ℕ) (s : M →ₗ[B] (Fin n → B)) (t : (Fin n → B) →ₗ[B] M), t ∘ₗ s = b ^ c • LinearMap.id := by
  classical
  have : Module.FinitePresentation S M' := _root_.FinitePresentation.of_isBaseChange f
    ((isLocalizedModule_iff_isBaseChange (Submonoid.powers b) S f).mp inferInstance)
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' S M'
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property p LinearMap.id hp
  let eS := Finsupp.linearEquivFunOnFinite S S (Fin n)
  let eB := Finsupp.linearEquivFunOnFinite B B (Fin n)
  let ℓ : (Fin n →₀ B) →ₗ[B] (Fin n →₀ S) := Finsupp.mapRange.linearMap (Algebra.linearMap B S)
  let p' : (Fin n →₀ S) →ₗ[S] M' := p ∘ₗ eS.toLinearMap
  let σ' : M' →ₗ[S] (Fin n →₀ S) := eS.symm.toLinearMap ∘ₗ σ
  have hpσ : ∀ x, p' (σ' x) = x := fun x => by
    simpa [p', σ'] using LinearMap.congr_fun hσ x
  obtain ⟨h, s₁, hh⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    (Submonoid.powers b) ℓ ((σ'.restrictScalars B) ∘ₗ f)
  obtain ⟨t, s₂, ht⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    (Submonoid.powers b) f ((p'.restrictScalars B) ∘ₗ ℓ)
  have key : f ∘ₗ (t ∘ₗ h) = f ∘ₗ ((s₂ * s₁) • LinearMap.id) := by
    refine LinearMap.ext fun m => ?_
    have e1 : f (t (h m)) = (s₂ : B) • p' (ℓ (h m)) := by
      simpa [Submonoid.smul_def] using LinearMap.congr_fun ht (h m)
    have e2 : ℓ (h m) = (s₁ : B) • σ' (f m) := by
      simpa [Submonoid.smul_def] using LinearMap.congr_fun hh m
    have e3 : p' ((s₁ : B) • σ' (f m)) = (s₁ : B) • f m := by
      have := (p'.restrictScalars B).map_smul (s₁ : B) (σ' (f m))
      rw [LinearMap.coe_restrictScalars] at this
      rw [this, hpσ]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e1, e2, e3, LinearMap.comp_apply,
      LinearMap.smul_apply, LinearMap.id_apply, Submonoid.smul_def, map_smul, Submonoid.coe_mul,
      mul_smul]
  obtain ⟨s₃, hs₃⟩ :=
    Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule (Submonoid.powers b) f _ _ key
  obtain ⟨k₁, hk₁⟩ := s₁.2
  obtain ⟨k₂, hk₂⟩ := s₂.2
  obtain ⟨k₃, hk₃⟩ := s₃.2
  dsimp only at hk₁ hk₂ hk₃
  refine ⟨k₃ + (k₂ + k₁), n, eB.toLinearMap ∘ₗ h, ((s₃ : B) • t) ∘ₗ eB.symm.toLinearMap, ?_⟩
  refine LinearMap.ext fun m => ?_
  have hm := LinearMap.congr_fun hs₃ m
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply, Submonoid.smul_def, Submonoid.smul_def, Submonoid.smul_def,
    Submonoid.coe_mul] at hm
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.id_apply, hm,
    ← hk₁, ← hk₂, ← hk₃, pow_add, pow_add, mul_smul, mul_smul, mul_smul]

theorem defect_bounded : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R), Irreducible π → ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B], Algebra.Smooth R (Localization.Away (algebraMap R B π)) → ∃ c : ℕ, ∀ (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (a : B →ₐ[R] R'), Defect a π c := by
  intro R _ _ _ π _ B _ _ _ hsm
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  have : Algebra.FinitePresentation R B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨c, n, s, t, hts⟩ := exists_pow_factor_free (S := Localization.Away (algebraMap R B π))
    (M' := Ω[Localization.Away (algebraMap R B π)⁄R]) (algebraMap R B π)
    (KaehlerDifferential.map R R B (Localization.Away (algebraMap R B π)))
  refine ⟨c, fun R' _ _ _ a => ?_⟩
  letI := a.toRingHom.toAlgebra
  intro w hw
  obtain ⟨⟨r, hr⟩, hrw⟩ := hw
  have hsw : s.baseChange R' w = 0 := by
    have h0 : r • s.baseChange R' w = 0 := by
      have hrw' : r • w = 0 := hrw
      rw [← LinearMap.map_smul, hrw', map_zero]
    exact (smul_eq_zero.mp h0).resolve_left (nonZeroDivisors.ne_zero hr)
  have hcomp : (t.baseChange R') (s.baseChange R' w) = (algebraMap R B π ^ c) • w := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hts, LinearMap.baseChange_smul,
      LinearMap.baseChange_id, LinearMap.smul_apply, LinearMap.id_apply]
  rw [hsw, map_zero] at hcomp
  have hπ : algebraMap R R' π = algebraMap B R' (algebraMap R B π) := (a.commutes π).symm
  rw [hπ, ← map_pow, algebraMap_smul, ← hcomp]

end GlobalTheory.SS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DefectBoundedStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_defect_bound_of_smooth_away : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R), Irreducible π → ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B], Algebra.Smooth R (Localization.Away (algebraMap R B π)) → ∃ c : ℕ, ∀ (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (a : B →ₐ[R] R'), Defect a π c := by
  first | exact @GlobalTheory.SS.defect_bounded | exact GlobalTheory.SS.defect_bounded | (intros; apply GlobalTheory.SS.defect_bounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmoothFlatAlgebraFiniteCoverDecomp
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.Smoothening

def GenOpen (K : Type) {R B C : Type} [CommRing R] [Field K] [Algebra R K] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
    (φ : B →ₐ[R] C) : Prop :=
  IsOpenImmersion (spMap (Algebra.TensorProduct.map (AlgHom.id K K) φ).toRingHom)

section
variable {R K B C D : Type} [CommRing R] [Field K] [Algebra R K] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
  [CommRing D] [Algebra R D]

theorem GenOpen.comp {φ : B →ₐ[R] C} {ψ : C →ₐ[R] D} (h : GenOpen K φ) (h' : GenOpen K ψ) : GenOpen K (ψ.comp φ) := by
  unfold GenOpen at *
  have e : spMap (Algebra.TensorProduct.map (AlgHom.id K K) (ψ.comp φ)).toRingHom =
      spMap (Algebra.TensorProduct.map (AlgHom.id K K) ψ).toRingHom ≫
        spMap (Algebra.TensorProduct.map (AlgHom.id K K) φ).toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x <;> simp
  rw [e]; infer_instance

theorem genOpen_away (f : B) : GenOpen K (IsScalarTower.toAlgHom R B (Localization.Away f)) := by
  unfold GenOpen
  letI : Algebra (K ⊗[R] B) (K ⊗[R] Localization.Away f) :=
    (Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom R B (Localization.Away f))).toRingHom.toAlgebra
  haveI : IsScalarTower K (K ⊗[R] B) (K ⊗[R] Localization.Away f) :=
    IsScalarTower.of_algHom (Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom R B (Localization.Away f)))
  have h := IsLocalization.tensorProduct_tensorProduct_right R K (Submonoid.powers f) (Localization.Away f) (by
    ext x; simp [RingHom.algebraMap_toAlgebra])
  rw [Submonoid.map_powers] at h
  exact IsOpenImmersion.of_isLocalization (R := CommRingCat.of (K ⊗[R] B)) (S := CommRingCat.of (K ⊗[R] Localization.Away f)) (Algebra.TensorProduct.includeRight (R := R) (A := K) f)

theorem genOpen_of_inj [IsDomain R] [IsFractionRing R K] {π : R} (hπ : π ≠ 0) (φ : B →ₐ[R] C) (hi : Function.Injective φ)
    (hs : ∀ b' : C, ∃ (n : ℕ) (b : B), algebraMap R C π ^ n * b' = φ b) : GenOpen K φ := by
  unfold GenOpen
  have hb : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id K K) φ) := by
    constructor
    · haveI : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
      exact Module.Flat.lTensor_preserves_injective_linearMap (M := K) φ.toLinearMap hi
    · intro x
      induction x using TensorProduct.induction_on with
      | zero => exact ⟨0, map_zero _⟩
      | add x y hx hy =>
        obtain ⟨x, rfl⟩ := hx; obtain ⟨y, rfl⟩ := hy
        exact ⟨x + y, map_add _ _ _⟩
      | tmul k c =>
        obtain ⟨n, b, hb⟩ := hs c
        have h0 : algebraMap R K (π ^ n) ≠ 0 := by
          simpa using fun h => absurd h hπ
        refine ⟨(k * (algebraMap R K (π ^ n))⁻¹) ⊗ₜ b, ?_⟩
        rw [Algebra.TensorProduct.map_tmul, ← hb, ← map_pow, ← Algebra.smul_def, ← TensorProduct.smul_tmul,
          AlgHom.id_apply, Algebra.smul_def, mul_comm, _root_.mul_assoc, inv_mul_cancel₀ h0, _root_.mul_one]
  have : IsIso (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id K K) φ).toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hb
  infer_instance

theorem smooth_away_away {π : R} (h : Algebra.Smooth R (Localization.Away (algebraMap R B π))) (f : B) :
    Algebra.Smooth R (Localization.Away (algebraMap R (Localization.Away f) π)) := by
  let p := algebraMap R B π
  let T := Localization.Away (algebraMap B (Localization.Away p) f)
  haveI : Algebra.Smooth (Localization.Away p) T := Algebra.Smooth.of_isLocalization_Away (algebraMap B (Localization.Away p) f)
  haveI : Algebra.Smooth R T := Algebra.Smooth.comp R (Localization.Away p) T
  haveI : IsLocalization.Away (f * p) T := inferInstance
  haveI : IsLocalization.Away (algebraMap B (Localization.Away f) p) (Localization.Away (algebraMap R (Localization.Away f) π)) := by
    rw [← IsScalarTower.algebraMap_apply]; infer_instance
  haveI : IsLocalization.Away (f * p) (Localization.Away (algebraMap R (Localization.Away f) π)) :=
    IsLocalization.Away.mul' (Localization.Away f) _ f p
  exact Algebra.Smooth.of_equiv ((IsLocalization.algEquiv (Submonoid.powers (f * p)) T
    (Localization.Away (algebraMap R (Localization.Away f) π))).restrictScalars R)

theorem smooth_away_of_inj {π : R} (h : Algebra.Smooth R (Localization.Away (algebraMap R B π)))
    (φ : B →ₐ[R] C) (hi : Function.Injective φ)
    (hs : ∀ b' : C, ∃ (n : ℕ) (b : B), algebraMap R C π ^ n * b' = φ b) :
    Algebra.Smooth R (Localization.Away (algebraMap R C π)) := by
  letI : Algebra B C := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algHom φ
  have hφ : ∀ b, algebraMap B (Localization.Away (algebraMap R C π)) b = algebraMap C _ (φ b) := fun b => rfl
  haveI : IsLocalization.Away (algebraMap R B π) (Localization.Away (algebraMap R C π)) := by
    refine IsLocalization.Away.mk _ ?_ ?_ ?_
    · rw [hφ, φ.commutes]; exact IsLocalization.Away.algebraMap_isUnit _
    · intro s
      obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj (algebraMap R C π) s
      obtain ⟨m, b, hb⟩ := hs c
      refine ⟨n + m, b, ?_⟩
      rw [hφ, hφ, φ.commutes, ← hb, map_mul, map_pow, ← hc]; ring
    · intro a b hab
      rw [hφ, hφ] at hab
      obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (algebraMap R C π) hab
      refine ⟨n, hi ?_⟩
      simpa using hn
  exact Algebra.Smooth.of_equiv ((IsLocalization.algEquiv (Submonoid.powers (algebraMap R B π))
    (Localization.Away (algebraMap R B π)) (Localization.Away (algebraMap R C π))).restrictScalars R)

def kaehlerAway (R : Type) {B : Type} [CommRing R] [CommRing B] [Algebra R B] (f : B) (D : Type) [CommRing D] [Algebra B D]
    [Algebra (Localization.Away f) D] [IsScalarTower B (Localization.Away f) D] :
    D ⊗[Localization.Away f] KaehlerDifferential R (Localization.Away f) ≃ₗ[D] D ⊗[B] KaehlerDifferential R B :=
  haveI : Algebra.FormallyEtale B (Localization.Away f) := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers f)
  (LinearEquiv.baseChange (Localization.Away f) D _ _
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B (Localization.Away f)).symm) ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange B (Localization.Away f) D D _

theorem defect_away (f : B) (a : Localization.Away f →ₐ[R] D) (π : R) (c : ℕ)
    (h : Defect (a.comp (IsScalarTower.toAlgHom R B (Localization.Away f))) π c) : Defect a π c := by
  letI := a.toRingHom.toAlgebra
  letI := (a.comp (IsScalarTower.toAlgHom R B (Localization.Away f))).toRingHom.toAlgebra
  haveI : IsScalarTower B (Localization.Away f) D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  intro w hw
  let e := kaehlerAway R f D
  apply e.injective
  rw [map_smul, map_zero]
  apply h
  obtain ⟨r, hr⟩ := hw
  refine ⟨r, ?_⟩
  rw [Submonoid.smul_def] at hr ⊢
  rw [← map_smul, hr, map_zero]

theorem free_of_away (f : C) (M : Type) [AddCommGroup M] [Module C M] (D : Type) [CommRing D] [Algebra C D]
    [IsLocalization.Away f D] (h : Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)) :
    Module.Free D (D ⊗[C] M) := by
  haveI : Module.Free (Localization.Away f) (Localization.Away f ⊗[C] M) :=
    Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers f) M)
  let e := IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f) D
  letI : Algebra (Localization.Away f) D := e.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower C (Localization.Away f) D := IsScalarTower.of_algHom e.toAlgHom
  exact Module.Free.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange C (Localization.Away f) D D M)
end

abbrev Pts (R B : Type) [CommRing R] [CommRing B] [Algebra R B] : Type 1 :=
  ∀ (R' : Type) [CommRing R'] [Algebra R R'], (B →ₐ[R] R') → Prop

def Cov (K : Type) {R B : Type} [CommRing R] [Field K] [Algebra R K] [CommRing B] [Algebra R B] (E : Pts R B) : Prop :=
  ∃ l : List (Σ C : CommAlgCat.{0} R, B →ₐ[R] C), (∀ x ∈ l, Algebra.Smooth R x.1 ∧ GenOpen K x.2) ∧
    ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → ∃ x ∈ l, ∃ a' : x.1 →ₐ[R] R', a'.comp x.2 = a

section
variable {R K B C : Type} [CommRing R] [Field K] [Algebra R K] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]

theorem Cov.empty {E : Pts R B} (h : ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), ¬ E R' a) : Cov K E :=
  ⟨[], by simp, fun R' _ _ a ha => (h R' a ha).elim⟩

theorem Cov.union {E E₁ E₂ : Pts R B} (h₁ : Cov K E₁) (h₂ : Cov K E₂)
    (h : ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → E₁ R' a ∨ E₂ R' a) : Cov K E := by
  obtain ⟨l₁, p₁, q₁⟩ := h₁
  obtain ⟨l₂, p₂, q₂⟩ := h₂
  refine ⟨l₁ ++ l₂, fun x hx => (List.mem_append.1 hx).elim (p₁ x) (p₂ x), fun R' _ _ a ha => ?_⟩
  rcases h R' a ha with h | h
  · obtain ⟨x, hx, r⟩ := q₁ R' a h
    exact ⟨x, List.mem_append_left _ hx, r⟩
  · obtain ⟨x, hx, r⟩ := q₂ R' a h
    exact ⟨x, List.mem_append_right _ hx, r⟩

theorem Cov.single {E : Pts R B} (φ : B →ₐ[R] C) (hs : Algebra.Smooth R C) (ho : GenOpen K φ)
    (h : ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → ∃ a' : C →ₐ[R] R', a'.comp φ = a) : Cov K E :=
  ⟨[⟨CommAlgCat.of R C, φ⟩], fun x hx => by
    obtain rfl := List.mem_singleton.1 hx
    exact ⟨hs, ho⟩, fun R' _ _ a ha => ⟨_, List.mem_singleton_self _, h R' a ha⟩⟩

theorem Cov.trans {E : Pts R B} {E' : Pts R C} (φ : B →ₐ[R] C) (ho : GenOpen K φ) (h' : Cov K E')
    (h : ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a →
      ∃ a' : C →ₐ[R] R', a'.comp φ = a ∧ E' R' a') : Cov K E := by
  obtain ⟨l, p, q⟩ := h'
  refine ⟨l.map fun x => ⟨x.1, x.2.comp φ⟩, fun x hx => ?_, fun R' _ _ a ha => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact ⟨(p y hy).1, ho.comp (p y hy).2⟩
  · obtain ⟨a', rfl, ha'⟩ := h R' a ha
    obtain ⟨x, hx, b, rfl⟩ := q R' a' ha'
    exact ⟨_, List.mem_map_of_mem hx, b, rfl⟩

def vanish (π : R) (E : Pts R B) : Ideal B where
  carrier := {b | ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → algebraMap R R' π ∣ a b}
  add_mem' hx hy R' _ _ a ha := by rw [map_add (f := _)]; exact dvd_add (hx R' a ha) (hy R' a ha)
  zero_mem' R' _ _ a _ := by rw [map_zero]; exact dvd_zero _
  smul_mem' c x hx R' _ _ a ha := by rw [smul_eq_mul, map_mul]; exact (hx R' a ha).mul_left _

theorem unit_or_dvd {π : R} {R' : Type} [CommRing R'] [Algebra R R'] (h : Unr π R') (x : R') :
    IsUnit x ∨ algebraMap R R' π ∣ x := by
  obtain ⟨_, _, h⟩ := h
  by_cases hx : IsUnit x
  · exact Or.inl hx
  · right
    rw [← Ideal.mem_span_singleton, ← h.maximalIdeal_eq]
    exact hx

theorem not_dvd_of_unit {π : R} {R' : Type} [CommRing R'] [Algebra R R'] (h : Unr π R') {x : R'} (hx : IsUnit x) :
    ¬ algebraMap R R' π ∣ x := by
  obtain ⟨_, _, h⟩ := h
  exact fun hd => h.not_isUnit (isUnit_of_dvd_unit hd hx)

theorem exists_lift (f : B) {R' : Type} [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R') (h : IsUnit (a f)) :
    ∃ a' : Localization.Away f →ₐ[R] R', a'.comp (IsScalarTower.toAlgHom R B (Localization.Away f)) = a := by
  refine ⟨IsLocalization.liftAlgHom (M := Submonoid.powers f) (f := a) ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    simpa using h.pow n
  · ext x; simp

theorem cov_of_generic [IsNoetherianRing B] (π : R) (Q : Pts R B)
    (hQ : ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), Q R' a → Unr π R')
    (H : ∀ E : Pts R B, (∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → Q R' a) →
      (∃ (R' : Type) (_ : CommRing R') (_ : Algebra R R') (a : B →ₐ[R] R'), E R' a) →
      ∃ f, f ∉ vanish π E ∧ Cov K (fun R' _ _ a => E R' a ∧ IsUnit (a f) : Pts R B)) : Cov K Q := by
  suffices h : ∀ (I : Ideal B) (E : Pts R B),
      (∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → Q R' a) → vanish π E = I → Cov K E from
    h _ Q (fun _ _ _ _ h => h) rfl
  intro I
  induction I using IsNoetherian.induction with
  | hgt I ih =>
    rintro E hE rfl
    by_cases hne : ∃ (R' : Type) (_ : CommRing R') (_ : Algebra R R') (a : B →ₐ[R] R'), E R' a
    · obtain ⟨f, hf, hc⟩ := H E hE hne
      let E' : Pts R B := fun R' _ _ a => E R' a ∧ algebraMap R R' π ∣ a f
      have h' : Cov K E' := by
        refine ih (vanish π E') (lt_of_le_of_ne (fun b hb R' _ _ a ha => hb R' a ha.1) fun e => hf ?_) E'
          (fun R' _ _ a ha => hE R' a ha.1) rfl
        rw [e]; exact fun R' _ _ a ha => ha.2
      exact hc.union h' fun R' _ _ a ha =>
        (unit_or_dvd (hQ R' a (hE R' a ha)) (a f)).imp (fun h => ⟨ha, h⟩) fun h => ⟨ha, h⟩
    · exact Cov.empty fun R' _ _ a ha => hne ⟨R', _, _, a, ha⟩

theorem vanish_away (π : R) (E : Pts R B)
    (hE : ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → Unr π R') (f : B) (b : Localization.Away f) :
    b ∈ (vanish π E).map (algebraMap B (Localization.Away f)) ↔
      ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : Localization.Away f →ₐ[R] R'),
        E R' (a.comp (IsScalarTower.toAlgHom R B (Localization.Away f))) → algebraMap R R' π ∣ a b := by
  constructor
  · intro hb
    have : (vanish π E).map (algebraMap B (Localization.Away f)) ≤
        vanish π (fun R' _ _ a => E R' (a.comp (IsScalarTower.toAlgHom R B (Localization.Away f)))) :=
      Ideal.map_le_iff_le_comap.2 fun x hx R' _ _ a ha => hx R' _ ha
    exact this hb
  · intro hb
    obtain ⟨n, x, hx⟩ := IsLocalization.Away.surj f b
    have h1 : x * f ∈ vanish π E := by
      intro R' _ _ a ha
      rw [map_mul]
      rcases unit_or_dvd (hE R' a ha) (a f) with h | h
      · obtain ⟨a', rfl⟩ := exists_lift f a h
        refine Dvd.dvd.mul_right ?_ _
        show _ ∣ a' (algebraMap B _ x)
        rw [← hx, map_mul]
        exact (hb R' a' ha).mul_right _
      · exact h.mul_left _
    have h2 := Ideal.mem_map_of_mem (algebraMap B (Localization.Away f)) h1
    rw [map_mul, ← hx, _root_.mul_assoc, ← pow_succ] at h2
    exact (Ideal.mul_unit_mem_iff_mem _ ((IsLocalization.Away.algebraMap_isUnit f).pow _)).1 h2

theorem vanish_isRadical (π : R) (E : Pts R B)
    (hE : ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → Unr π R') : (vanish π E).IsRadical := by
  rintro b ⟨n, hn⟩ R' _ _ a ha
  rcases unit_or_dvd (hE R' a ha) (a b) with h | h
  · exact (not_dvd_of_unit (hE R' a ha) (h.pow n) (map_pow a b n ▸ hn R' a ha)).elim
  · exact h
end

section
variable {R : Type} (K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  {π : R} (hπ : Irreducible π)
include hπ

theorem cov_zero (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B]
    (hB : Algebra.Smooth R (Localization.Away (algebraMap R B π))) :
    Cov K (fun R' _ _ a => Unr π R' ∧ Defect a π 0 : Pts R B) := by
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  refine cov_of_generic π _ (fun R' _ _ a h => h.1) ?_
  rintro E hE ⟨R', _, _, a, ha⟩
  obtain ⟨f, hf, hs⟩ := GlobalTheory.T.exists_smooth_of_defect_zero' R π hπ B hB R' a (hE R' a ha).1 (hE R' a ha).2
  exact ⟨f, fun h => not_dvd_of_unit (hE R' a ha).1 hf (h R' a ha),
    Cov.single _ hs (genOpen_away f) fun R'' _ _ b hb => exists_lift f b hb.2⟩

theorem cov_succ (hk : PerfectField (IsLocalRing.ResidueField R)) (c : ℕ)
    (ih : ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B],
      Algebra.Smooth R (Localization.Away (algebraMap R B π)) → Cov K (fun R' _ _ a => Unr π R' ∧ Defect a π c : Pts R B))
    (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B]
    (hB : Algebra.Smooth R (Localization.Away (algebraMap R B π))) :
    Cov K (fun R' _ _ a => Unr π R' ∧ Defect a π (c + 1) : Pts R B) := by
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  refine cov_of_generic π _ (fun R' _ _ a h => h.1) ?_
  rintro E hE ⟨R₀, _, _, a₀, ha₀⟩
  have hU : ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → Unr π R' :=
    fun R' _ _ a ha => (hE R' a ha).1
  let I := vanish π E
  let k := IsLocalRing.ResidueField R
  have hI : I ≠ ⊤ := fun h => not_dvd_of_unit (hU R₀ a₀ ha₀) (isUnit_one.map a₀)
    ((h ▸ Submodule.mem_top : (1 : B) ∈ I) R₀ a₀ ha₀)
  haveI : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  haveI : IsReduced (B ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).1 (vanish_isRadical π E hU)
  have hm : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R (B ⧸ I) r = 0 := by
    intro r hr
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hr
    rw [IsScalarTower.algebraMap_apply R B, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    intro R' _ _ a _
    rw [a.commutes]
    exact map_dvd _ hr
  letI : Algebra k (B ⧸ I) := (Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) (algebraMap R (B ⧸ I)) hm).toAlgebra
  haveI : IsScalarTower R k (B ⧸ I) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FiniteType k (B ⧸ I) := Algebra.FiniteType.of_restrictScalars_finiteType R k _
  obtain ⟨g, hg, hs, hfree⟩ := GlobalTheory.T.exists_smooth_free_away' k (B ⧸ I) ((B ⧸ I) ⊗[B] KaehlerDifferential R B)
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective g
  refine ⟨f, fun h => hg (Ideal.Quotient.eq_zero_iff_mem.2 h), ?_⟩
  let L := Localization.Away f
  let J : Ideal L := I.map (algebraMap B L)
  let jf := IsScalarTower.toAlgHom R B L
  haveI : IsLocalization.Away (Ideal.Quotient.mk I f) (L ⧸ J) := by
    have : IsLocalization (Algebra.algebraMapSubmonoid (B ⧸ I) (Submonoid.powers f)) (L ⧸ J) := inferInstance
    rwa [Algebra.algebraMapSubmonoid_powers] at this
  letI : Algebra k (L ⧸ J) := ((algebraMap (B ⧸ I) (L ⧸ J)).comp (algebraMap k (B ⧸ I))).toAlgebra
  haveI : IsScalarTower k (B ⧸ I) (L ⧸ J) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R k (L ⧸ J) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hs' : Algebra.Smooth k (L ⧸ J) := Algebra.Smooth.of_equiv
    ((IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk I f)) (Localization.Away (Ideal.Quotient.mk I f))
      (L ⧸ J)).restrictScalars k)
  have hfree' : Module.Free (L ⧸ J) ((L ⧸ J) ⊗[L] KaehlerDifferential R L) := by
    haveI := free_of_away (Ideal.Quotient.mk I f) _ (L ⧸ J) hfree
    haveI : Module.Free (L ⧸ J) ((L ⧸ J) ⊗[B] KaehlerDifferential R B) :=
      Module.Free.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange B (B ⧸ I) (L ⧸ J) (L ⧸ J) _)
    exact Module.Free.of_equiv (kaehlerAway R f (L ⧸ J)).symm
  haveI : Algebra.FiniteType R L := Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  haveI : Module.Flat R L := Module.Flat.trans R B L
  obtain ⟨B', _, _, φ, _, _, hi, hsurj, hpt⟩ := GlobalTheory.T.unramified_ideal_locus_characterization R π hπ L (fun R' _ _ a => E R' (a.comp jf))
    (fun R' _ _ a ha => hU R' _ ha) J (vanish_away π E hU f) k IsLocalRing.residue_surjective hs' hfree'
  refine Cov.trans (φ.comp jf) ((genOpen_away f).comp (genOpen_of_inj hπ.ne_zero φ hi hsurj))
    (ih B' (smooth_away_of_inj (smooth_away_away hB f) φ hi hsurj)) ?_
  rintro R' _ _ a ⟨ha, hu⟩
  obtain ⟨a', rfl⟩ := exists_lift f a hu
  obtain ⟨a'', rfl, hd⟩ := hpt R' a' c ha (defect_away f a' π _ (hE R' _ ha).2)
  exact ⟨a'', rfl, hU R' _ ha, hd⟩
end

theorem smoothening : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → PerfectField (IsLocalRing.ResidueField R) → ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B], Algebra.Smooth R (Localization.Away (algebraMap R B π)) → ∃ (n : ℕ) (C : Fin n → Type) (_ : ∀ i, CommRing (C i)) (_ : ∀ i, Algebra R (C i)) (φ : ∀ i, B →ₐ[R] C i), (∀ i, Algebra.Smooth R (C i) ∧ IsOpenImmersion (spMap (Algebra.TensorProduct.map (AlgHom.id K K) (φ i)).toRingHom)) ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), Unr π R' → ∃ (i : Fin n) (a' : C i →ₐ[R] R'), a'.comp (φ i) = a := by
  intro R K _ _ _ _ _ _ π hπ hk B _ _ _ _ hB
  have H : ∀ (c : ℕ) (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B],
      Algebra.Smooth R (Localization.Away (algebraMap R B π)) →
      Cov K (fun R' _ _ a => Unr π R' ∧ Defect a π c : Pts R B) := by
    intro c
    induction c with
    | zero => exact cov_zero K hπ
    | succ c ih => exact cov_succ K hπ hk c ih
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_defect_bound_of_smooth_away R π hπ B hB
  obtain ⟨l, p, q⟩ := H c B hB
  refine ⟨l.length, fun i => (l.get i).1, inferInstance, inferInstance, fun i => (l.get i).2,
    fun i => p _ (List.get_mem l i), fun R' _ _ a hu => ?_⟩
  obtain ⟨x, hx, r⟩ := q R' a ⟨hu, by haveI := hu.1; exact hc R' a⟩
  obtain ⟨i, rfl⟩ := List.get_of_mem hx
  exact ⟨i, r⟩

end GlobalTheory.SS.Smoothening
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmoothFlatAlgebraFiniteCoverDecompStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_flat_algebra_finite_cover_decomp : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → PerfectField (IsLocalRing.ResidueField R) → ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B], Algebra.Smooth R (Localization.Away (algebraMap R B π)) → ∃ (n : ℕ) (C : Fin n → Type) (_ : ∀ i, CommRing (C i)) (_ : ∀ i, Algebra R (C i)) (φ : ∀ i, B →ₐ[R] C i), (∀ i, Algebra.Smooth R (C i) ∧ IsOpenImmersion (spMap (Algebra.TensorProduct.map (AlgHom.id K K) (φ i)).toRingHom)) ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), Unr π R' → ∃ (i : Fin n) (a' : C i →ₐ[R] R'), a'.comp (φ i) = a := by
  first | exact @GlobalTheory.SS.Smoothening.smoothening | exact GlobalTheory.SS.Smoothening.smoothening | (intros; apply GlobalTheory.SS.Smoothening.smoothening <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeakNeronModel
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GlobalTheory.SS.WeakNeronEx
open GlobalTheory.AbLaw ReciprocityTheory.ChartRestriction.G.Out

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem sp_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (e : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem away_of_irreducible (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K]
    {π : V} (hπ : Irreducible π) : IsLocalization.Away π K := by
  refine (IsLocalization.iff_of_le_of_exists_dvd (M := Submonoid.powers π) (S := K)
    (nonZeroDivisors V) (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero) ?_).mpr
    inferInstance
  intro a ha
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    (nonZeroDivisors.ne_zero ha) hπ
  exact ⟨π ^ n, ⟨n, rfl⟩, hn.dvd⟩

section Ev
variable {X : Scheme.{0}} {L : Type} [Field L] (a : Sp L ⟶ X)

def ev (W : X.Opens) (h : ⊤ ≤ a ⁻¹ᵁ W) : Γ(X, W) →+* L :=
  (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom.comp (a.appLE W ⊤ h).hom

theorem ev_rs {W W' : X.Opens} (e : W' ≤ W) (h : ⊤ ≤ a ⁻¹ᵁ W) (h' : ⊤ ≤ a ⁻¹ᵁ W') (f : Γ(X, W)) :
    ev a W' h' (rs X e f) = ev a W h f := by
  have := congrArg (fun q => q.hom f) (Scheme.Hom.map_appLE a h' (homOfLE e).op)
  exact congrArg (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom this

theorem ev_ne_zero {W : X.Opens} (h : ⊤ ≤ a ⁻¹ᵁ W) (f : Γ(X, W)) :
    ev a W h f ≠ 0 ↔ ⊤ ≤ a ⁻¹ᵁ X.basicOpen f := by
  have e := Scheme.basicOpen_appLE a ⊤ W h f
  rw [top_inf_eq] at e
  rw [← e, ← isUnit_iff_ne_zero]
  constructor
  · intro hu
    have : IsUnit ((a.appLE W ⊤ h).hom f) := by
      have := hu.map (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom
      simpa [ev] using this
    exact (Scheme.basicOpen_of_isUnit _ this).ge
  · intro hu
    have : IsUnit ((a.appLE W ⊤ h).hom f) :=
      RingedSpace.isUnit_of_isUnit_germ (Sp L).toRingedSpace ⊤ _ fun x hx =>
        (Scheme.mem_basicOpen _ _ x hx).1 (hu hx)
    exact this.map (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom

theorem spMap_ev {W : X.Opens} (hW : IsAffineOpen W) (h : ⊤ ≤ a ⁻¹ᵁ W) :
    spMap (ev a W h) ≫ hW.fromSpec = a := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec a hW (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  have : spMap (ev a W h) = Spec.map (Scheme.ΓSpecIso (CommRingCat.of L)).hom ≫ Spec.map (a.appLE W ⊤ h) :=
    Spec.map_comp (a.appLE W ⊤ h) _
  rw [this, Category.assoc, e, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]
end Ev

theorem fromSpec_hom {X : Scheme.{0}} {K : Type} [CommRing K] (f : X ⟶ Sp K) {W : X.Opens} (hW : IsAffineOpen W) :
    hW.fromSpec ≫ f = spMap (cst f W) := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hW (le_top : W ≤ f ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at e
  rw [← e]
  rfl

theorem exists_min {V L : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field L] [Algebra V L]
    [IsFractionRing V L] {I : Type} [Finite I] [Nonempty I] (c : I → L) :
    ∃ i, ∀ j, ∃ t : V, c j = algebraMap V L t * c i := by
  obtain ⟨i, hi⟩ := Finite.exists_max (fun j => ValuationRing.valuation V L (c j))
  refine ⟨i, fun j => ?_⟩
  by_cases h0 : c i = 0
  · have := hi j
    simp only [h0, map_zero, le_zero_iff, Valuation.zero_iff] at this
    exact ⟨0, by simp [this]⟩
  · have : c j / c i ∈ (ValuationRing.valuation V L).integer := by
      rw [Valuation.mem_integer_iff, map_div₀]
      exact div_le_one_of_le₀ (hi j) zero_le'
    obtain ⟨t, ht⟩ := (ValuationRing.mem_integer_iff V L _).1 this
    exact ⟨t, by rw [ht, div_mul_cancel₀ _ h0]⟩

theorem exists_chart {X : Scheme.{0}} {H : LB X} {m : ℕ} (s : Fin (m + 1) → LB.Sec H)
    (hc : ⨆ i, nonzeroLocus (s i) = ⊤) (r : ∀ i, Fin (m + 1) → Γ(X, nonzeroLocus (s i)))
    (hr : ∀ i j k, rs X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s j).f k) =
        rs X (inf_le_left : nonzeroLocus (s i) ⊓ H.U k ≤ nonzeroLocus (s i)) (r i j) *
          rs X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s i).f k))
    {V L : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field L] [Algebra V L]
    [IsFractionRing V L] (a : Sp L ⟶ X) :
    ∃ (i : Fin (m + 1)) (h : ⊤ ≤ a ⁻¹ᵁ nonzeroLocus (s i)), ∀ j, ev a _ h (r i j) ∈ (algebraMap V L).range := by
  have hpt : ∀ W : X.Opens, a (IsLocalRing.closedPoint L) ∈ W → ⊤ ≤ a ⁻¹ᵁ W := fun W hW y _ => by
    have : y = IsLocalRing.closedPoint L := Subsingleton.elim (α := PrimeSpectrum L) _ _
    subst this
    exact hW
  have hx : a (IsLocalRing.closedPoint L) ∈ ⨆ i, nonzeroLocus (s i) := by rw [hc]; trivial
  obtain ⟨i₀, h₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h₀
  have hU : ⊤ ≤ a ⁻¹ᵁ H.U k := hpt _ (X.basicOpen_le _ hk)
  have hne : ev a _ hU ((s i₀).f k) ≠ 0 := (ev_ne_zero a hU _).2 (hpt _ hk)
  obtain ⟨i, hi⟩ := exists_min (V := V) (fun j => ev a _ hU ((s j).f k))
  have hne' : ev a _ hU ((s i).f k) ≠ 0 := by
    intro h
    obtain ⟨t, ht⟩ := hi i₀
    exact hne (by simpa [h] using ht)
  have hD : ⊤ ≤ a ⁻¹ᵁ nonzeroLocus (s i) :=
    hpt _ (TopologicalSpace.Opens.mem_iSup.2 ⟨k, (ev_ne_zero a hU _).1 hne' (x := IsLocalRing.closedPoint L) trivial⟩)
  have hI : ⊤ ≤ a ⁻¹ᵁ (nonzeroLocus (s i) ⊓ H.U k) := fun y hy => ⟨hD hy, hU hy⟩
  refine ⟨i, hD, fun j => ?_⟩
  obtain ⟨t, ht⟩ := hi j
  have e := congrArg (ev a _ hI) (hr i j k)
  rw [map_mul, ev_rs a _ hU, ev_rs a _ hU, ev_rs a _ hD, ht] at e
  exact ⟨t, mul_right_cancel₀ hne' e⟩

section Alg
variable (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  {D : Type} [CommRing D] [Algebra K D] [Algebra R D] [IsScalarTower R K D]


include K in
theorem flat_sub (B : Subalgebra R D) : Module.Flat R B := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, Submodule.eq_bot_iff]
  rintro x ⟨c, hc⟩
  have hu : IsUnit (algebraMap R D c) := by
    rw [IsScalarTower.algebraMap_apply R K D]
    exact (IsLocalization.map_units K c).map _
  have : algebraMap R D c * (x : D) = 0 := by
    rw [← Algebra.smul_def]
    exact congrArg Subtype.val hc
  exact Subtype.ext (hu.mul_right_eq_zero.1 this)

def gen (B : Subalgebra R D) : TensorProduct R K B →ₐ[K] D :=
  Algebra.TensorProduct.lift (Algebra.ofId K D) B.val (fun _ _ => Commute.all _ _)


omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem gen_injective (B : Subalgebra R D) : Function.Injective (gen R K B) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  letI : Algebra B (TensorProduct R K B) := Algebra.TensorProduct.rightAlgebra
  have hl : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) (TensorProduct R K B) :=
    IsLocalization.tensorRight K (nonZeroDivisors R)
  obtain ⟨⟨b, c⟩, e⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) x
  have e' := congrArg (gen R K B) e
  rw [map_mul, hx, zero_mul] at e'
  have hb : b = 0 := by
    apply Subtype.ext
    have : gen R K B (algebraMap B _ b) = (b : D) := by
      show gen R K B (1 ⊗ₜ b) = _
      simp [gen]
    rw [← this, ← e']; rfl
  rw [hb, map_zero] at e
  exact (IsLocalization.map_units (TensorProduct R K B) c).mul_left_eq_zero.1 e


omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem gen_surjective {I : Type} (r : I → D)
    (h : Function.Surjective (MvPolynomial.eval₂Hom (algebraMap K D) r)) :
    Function.Surjective (gen R K (Algebra.adjoin R (Set.range r))) := by
  intro d
  obtain ⟨p, rfl⟩ := h d
  refine ⟨MvPolynomial.aeval (fun i => (1 : K) ⊗ₜ (⟨r i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ :
    Algebra.adjoin R (Set.range r))) p, ?_⟩
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  simp [gen, MvPolynomial.aeval_def]

theorem smooth_away {π : R} (hπ : Irreducible π) (B : Type) [CommRing B] [Algebra R B]
    [Algebra.Smooth K (TensorProduct R K B)] : Algebra.Smooth R (Localization.Away (algebraMap R B π)) := by
  have := away_of_irreducible R K hπ
  have h₁ : Algebra.Smooth R K := Algebra.Smooth.of_isLocalization_Away π
  have h₂ : Algebra.Smooth R (TensorProduct R K B) := Algebra.Smooth.comp R K _
  letI : Algebra B (TensorProduct R K B) := Algebra.TensorProduct.rightAlgebra
  have hl : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers π)) (TensorProduct R K B) :=
    IsLocalization.tensorRight K (Submonoid.powers π)
  rw [Algebra.algebraMapSubmonoid_powers] at hl
  haveI : IsScalarTower R B (TensorProduct R K B) := Algebra.TensorProduct.right_isScalarTower
  exact Algebra.Smooth.of_equiv ((IsLocalization.algEquiv (Submonoid.powers (algebraMap R B π))
    (TensorProduct R K B) (Localization.Away (algebraMap R B π))).restrictScalars R)
end Alg

theorem exists_affine (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {X : Scheme.{0}} (f : X ⟶ Sp K) (hf : IsProjBy f) :
    ∃ (m : ℕ) (B : Fin m → Type) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra R (B i))
      (u : ∀ i, Sp (TensorProduct R K (B i)) ⟶ X),
      (∀ i, Algebra.FiniteType R (B i) ∧ Module.Flat R (B i) ∧ IsOpenImmersion (u i) ∧
        u i ≫ f = spMap (algebraMap K _)) ∧
      ∀ (V L : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra R V] [Field L] [Algebra V L]
        [IsFractionRing V L] (a : Sp L ⟶ X),
        a ≫ f ≫ spMap (algebraMap R K) = spMap ((algebraMap V L).comp (algebraMap R V)) →
        ∃ (i : Fin m) (b : B i →ₐ[R] V) (ψ : TensorProduct R K (B i) →+* L), spMap ψ ≫ u i = a ∧
          ∀ x, ψ (1 ⊗ₜ x) = algebraMap V L (b x) := by
  obtain ⟨H, -, m, s, hc, hs⟩ := hf
  choose haff r hr hsurj using hs
  letI : ∀ i, Algebra K Γ(X, nonzeroLocus (s i)) := fun i => (AbLaw.cst f _).toAlgebra
  letI : ∀ i, Algebra R Γ(X, nonzeroLocus (s i)) := fun i => ((AbLaw.cst f _).comp (algebraMap R K)).toAlgebra
  haveI : ∀ i, IsScalarTower R K Γ(X, nonzeroLocus (s i)) := fun i => IsScalarTower.of_algebraMap_eq fun _ => rfl
  let e : ∀ i, TensorProduct R K (Algebra.adjoin R (Set.range (r i))) ≃ₐ[K] Γ(X, nonzeroLocus (s i)) := fun i =>
    AlgEquiv.ofBijective (gen R K _) ⟨gen_injective R K _, gen_surjective R K _ (hsurj i)⟩
  refine ⟨m + 1, fun i => Algebra.adjoin R (Set.range (r i)), inferInstance, inferInstance,
    fun i => spMap (e i).symm.toAlgHom.toRingHom ≫ (haff i).fromSpec, fun i => ⟨?_, flat_sub R K _, ?_, ?_⟩, ?_⟩
  · exact Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)
  · haveI : IsIso (spMap (e i).symm.toAlgHom.toRingHom) :=
      inferInstanceAs (IsIso (Spec.map (e i).symm.toRingEquiv.toCommRingCatIso.hom))
    infer_instance
  · rw [Category.assoc, fromSpec_hom, sp_comp]
    exact congrArg spMap ((e i).symm.toAlgHom.comp_algebraMap)
  · intro V L _ _ _ _ _ _ _ a ha
    obtain ⟨i, h, hi⟩ := exists_chart s hc r hr (V := V) a
    have h₁ := spMap_ev a (haff i) h
    have h₂ : (ev a _ h).comp (algebraMap R _) = (algebraMap V L).comp (algebraMap R V) := by
      apply sp_inj
      have h₀ : a ≫ f = spMap ((ev a _ h).comp (cst f _)) := by
        rw [← sp_comp, ← fromSpec_hom f (haff i), reassoc_of% h₁]
      rw [← ha, reassoc_of% h₀, sp_comp]
      rfl
    letI : Algebra R L := ((algebraMap V L).comp (algebraMap R V)).toAlgebra
    haveI : IsScalarTower R V L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let φ : Γ(X, nonzeroLocus (s i)) →ₐ[R] L := ⟨ev a _ h, fun c => congrArg (fun q => q c) h₂⟩
    have hle : Algebra.adjoin R (Set.range (r i)) ≤ (IsScalarTower.toAlgHom R V L).range.comap φ := by
      rw [Algebra.adjoin_le_iff]
      rintro _ ⟨j, rfl⟩
      exact hi j
    let κ := AlgEquiv.ofInjective (IsScalarTower.toAlgHom R V L) (IsFractionRing.injective V L)
    refine ⟨i, κ.symm.toAlgHom.comp ((φ.comp (Subalgebra.val _)).codRestrict _ fun x => hle x.2),
      (ev a _ h).comp (e i).toAlgHom.toRingHom, ?_, fun x => ?_⟩
    · rw [← Category.assoc, sp_comp]
      refine Eq.trans ?_ h₁
      congr 2
      ext y
      simp
    · have h₃ : ∀ y, algebraMap V L (κ.symm y) = y := fun y =>
        congrArg Subtype.val (κ.apply_symm_apply y)
      refine Eq.trans ?_ (h₃ _).symm
      have h₄ : gen R K (Algebra.adjoin R (Set.range (r i))) (1 ⊗ₜ x) = x.1 := by simp [gen]
      exact congrArg (ev a _ h) h₄

theorem range_subset {V : Type} [CommRing V] [IsLocalRing V] {Y Z : Scheme.{0}} (b : Sp V ⟶ Y) (g : Z ⟶ Y)
    [IsOpenImmersion g] (h : b (IsLocalRing.closedPoint V) ∈ Set.range g) : Set.range b ⊆ Set.range g := by
  rintro _ ⟨y, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint y).map b.continuous).mem_open g.isOpenEmbedding.isOpen_range h

theorem exists_weakNeron : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K], PerfectField (IsLocalRing.ResidueField R) → ∀ (A : Over (Sp K)), Smooth A.hom → IsProper A.hom → GlobalTheory.AbLaw.IsProjBy A.hom → ∃ (n : ℕ) (M : Fin n → Model R A), (∀ i, (M i).Irr) ∧ WeakNeron M := by
  intro R K _ _ _ _ _ _ hperf A hsm hpr hproj
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, B, _, _, u, hB, hpt⟩ := exists_affine R K A.hom hproj
  have hs : ∀ i, Algebra.Smooth R (Localization.Away (algebraMap R (B i) π)) := fun i => by
    obtain ⟨-, -, h₃, h₄⟩ := hB i
    have h₅ : Smooth (spMap (algebraMap K (TensorProduct R K (B i)))) := by rw [← h₄]; infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at h₅
    haveI := RingHom.smooth_algebraMap.mp h₅
    exact smooth_away R K hπ (B i)
  have h₁ := fun i => by
    haveI := (hB i).1
    haveI := (hB i).2.1
    exact GlobalTheory.T.smooth_flat_algebra_finite_cover_decomp R K π hπ hperf (B i) (hs i)
  choose n C instR instA φ hC hlift using h₁
  have h₂ := fun i k => GlobalTheory.T.exists_scheme_model_of_affine_smooth_chart R K A hsm inferInstance inferInstance (C i k) (hC i k).1
    (spMap (Algebra.TensorProduct.map (AlgHom.id K K) (φ i k)).toRingHom ≫ u i)
    (by haveI := (hC i k).2; haveI := (hB i).2.2.1; infer_instance)
    (by
      rw [Category.assoc, (hB i).2.2.2, sp_comp]
      exact congrArg spMap (AlgHom.comp_algebraMap (Algebra.TensorProduct.map (AlgHom.id K K) (φ i k))))
  choose M g hg₁ hg₂ hg₃ hg₄ using h₂
  choose p N q hN hcov using fun i k => GlobalTheory.T.exists_cover_model_irreducible_specialFibre R K A (M i k)
  let e := Fintype.equivFin (Σ (i : Fin m) (k : Fin (n i)), Fin (p i k))
  refine ⟨_, fun t => N (e.symm t).1 (e.symm t).2.1 (e.symm t).2.2, fun t => (hN _ _ _).1, ?_⟩
  intro V L _ _ _ _ _ _ _ hmax a ha
  suffices h : ∃ i k l, ∃ b : Sp V ⟶ (N i k l).Y.left, b ≫ (N i k l).Y.hom = spMap (algebraMap R V) ∧
      spMap (algebraMap V L) ≫ b = a ≫ (N i k l).j by
    obtain ⟨i, k, l, h⟩ := h
    refine ⟨e ⟨i, k, l⟩, ?_⟩
    beta_reduce
    rw [e.symm_apply_apply]
    exact h
  have hunr : Unr π V := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hmax, hπ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton]
  obtain ⟨i, b, ψ, hψ, hb⟩ := hpt V L a ha
  obtain ⟨k, c, hc⟩ := hlift i V b hunr
  have hb₀ : (spMap c.toRingHom ≫ g i k) ≫ (M i k).Y.hom = spMap (algebraMap R V) := by
    rw [Category.assoc, hg₂, sp_comp]
    exact congrArg spMap (AlgHom.comp_algebraMap c)
  have hgen : spMap (algebraMap V L) ≫ spMap c.toRingHom ≫ g i k = a ≫ (M i k).j := by
    letI : Algebra R L := ((algebraMap V L).comp (algebraMap R V)).toAlgebra
    haveI : IsScalarTower R V L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let ψ₀ : TensorProduct R K (B i) →ₐ[R] L := ⟨ψ, fun x => by
      have := hb (algebraMap R _ x)
      rw [AlgHom.commutes] at this
      refine Eq.trans (congrArg ψ ?_) this
      exact ((Algebra.TensorProduct.includeRight : B i →ₐ[R] TensorProduct R K (B i)).commutes x).symm⟩
    let ψ' : TensorProduct R K (C i k) →ₐ[R] L := Algebra.TensorProduct.lift
      (ψ₀.comp Algebra.TensorProduct.includeLeft) ((IsScalarTower.toAlgHom R V L).comp c) fun _ _ => Commute.all _ _
    have e₁ : ψ'.toRingHom.comp (Algebra.TensorProduct.map (AlgHom.id K K) (φ i k)).toRingHom = ψ := by
      refine RingHom.ext fun x => ?_
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul x y =>
        have h₅ : c (φ i k y) = b y := congrArg (fun q => q y) hc
        show ψ' (x ⊗ₜ φ i k y) = _
        rw [Algebra.TensorProduct.lift_tmul]
        show ψ (x ⊗ₜ 1) * algebraMap V L (c (φ i k y)) = _
        rw [h₅, ← hb, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
    have e₂ : ψ'.toRingHom.comp (Algebra.TensorProduct.includeRight : C i k →ₐ[R] TensorProduct R K (C i k)).toRingHom =
        (algebraMap V L).comp c.toRingHom := by
      refine RingHom.ext fun x => ?_
      show ψ' (1 ⊗ₜ x) = _
      rw [Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
      rfl
    rw [← Category.assoc, sp_comp, ← e₂, ← sp_comp, Category.assoc, hg₃, ← Category.assoc, ← Category.assoc,
      sp_comp, e₁, hψ]
  have hsp : (spMap c.toRingHom ≫ g i k) (IsLocalRing.closedPoint V) ∈ (M i k).sp := by
    show (M i k).Y.hom ((spMap c.toRingHom ≫ g i k) _) = _
    rw [← Scheme.Hom.comp_apply, hb₀]
    haveI : IsLocalHom (algebraMap R V) := by
      apply ((IsLocalRing.local_hom_tfae (algebraMap R V)).out 1 3).2
      exact hmax.le
    exact IsLocalRing.comap_closedPoint (algebraMap R V)
  obtain ⟨l, hl⟩ := hcov i k _ hsp
  obtain ⟨-, hq, hj⟩ := hN i k l
  have hfac := IsOpenImmersion.lift_fac (q i k l).left _ (range_subset _ _ hl)
  refine ⟨i, k, l, IsOpenImmersion.lift (q i k l).left _ (range_subset _ _ hl), ?_, ?_⟩
  · rw [← Over.w (q i k l), ← Category.assoc, hfac, hb₀]
  · rw [← cancel_mono (q i k l).left, Category.assoc, hfac, Category.assoc, hj, hgen]

end GlobalTheory.SS.WeakNeronEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeakNeronModelStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weak_neron_model : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K], PerfectField (IsLocalRing.ResidueField R) → ∀ (A : Over (Sp K)), Smooth A.hom → IsProper A.hom → GlobalTheory.AbLaw.IsProjBy A.hom → ∃ (n : ℕ) (M : Fin n → Model R A), (∀ i, (M i).Irr) ∧ WeakNeron M := by
  first | exact @GlobalTheory.SS.WeakNeronEx.exists_weakNeron | exact GlobalTheory.SS.WeakNeronEx.exists_weakNeron | (intros; apply GlobalTheory.SS.WeakNeronEx.exists_weakNeron <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStrictModelOfBirationalStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_strict_model_of_birational : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, BirLaw M → ∃ N : Model R A, Strict N ∧ N.Le M := by
  first | exact @GlobalTheory.SS.exists_strict_le | exact GlobalTheory.SS.exists_strict_le | (intros; apply GlobalTheory.SS.exists_strict_le <;> assumption)
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
namespace GlobalTheory.SS

theorem exists_neutral_group_model : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → GlobalTheory.AbLaw.IsProjBy A.hom → ∃ (G : Model R A) (_ : GrpObj G.Y), SmConn G.Y ∧ IsMonHom G.e.hom ∧ ∃ c : ℕ, 1 ≤ c ∧ ∀ a : (𝟙_ (Over (Sp K)) ⟶ A), ∃ s : 𝟙_ (Over (Sp R)) ⟶ G.Y, spMap (algebraMap R K) ≫ s.left = (a ^ c).left ≫ G.j := by
  intro R K _ _ _ _ _ hS A _ _ hA hP
  have h1 := hS.1
  have h3 := hS.2.2.1
  have h4 := hS.2.2.2
  obtain ⟨n, M, hI, hW⟩ := GlobalTheory.T.exists_weak_neron_model R K inferInstance A hA.smooth hA.proper hP
  obtain ⟨N, hN, c, hc, hT⟩ := GlobalTheory.T.exists_weakNeronModel_birational_groupLaw R K hS A hA n M hI hW
  obtain ⟨N', hN', hle⟩ := GlobalTheory.T.exists_strict_model_of_birational R K hS A hA N hN
  obtain ⟨G, inst, hG, he, hs⟩ := GlobalTheory.T.exists_grpObj_of_strictBirationalLaw R K hS A hA N' hN'
  obtain ⟨b1, b2, b3, -, -⟩ := GlobalTheory.T.modelMapGenericallyOpenImmersion_calculus R K hS
  refine ⟨G, inst, hG, he, c, hc, fun a => hs (a ^ c) ?_⟩
  have e1 : GenIso N' N (𝟙 A) := b1 A N' N hN'.1.1 hle
  have e2 : GenIso N N' (𝟙 A) := (b3 A A N' N (Iso.refl A)).1 e1
  have e3 := b2 A A A N' N N _ _ hN.1 e1 (hT a)
  have e4 := b2 A A A N' N N' _ _ hN.1 e3 e2
  simpa only [Category.id_comp, Category.comp_id] using e4

end GlobalTheory.SS
