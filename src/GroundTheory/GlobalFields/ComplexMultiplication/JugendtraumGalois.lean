module

public import GroundTheory.GlobalFields.ComplexMultiplication.MainTheorem
public import GroundTheory.GlobalFields.ComplexMultiplication.HilbertClassField

@[expose] public section

section -- merged from GroundTheory.GlobalFields.ComplexMultiplication.JugendtraumUniformization
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField Module IsDedekindDomain WeierstrassCurve WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped nonZeroDivisors

section Points

variable {F : Type*} [Field F]

theorem vcPoint_eq_variableChangePoint (C : VariableChange F) {W W' : WeierstrassCurve F}
    (h : C • W = W') (P : W.toAffine.Point) : vcPoint C h P = variableChangePoint C h P := by
  rcases P with _ | ⟨x, y, hP⟩
  · rfl
  · rfl

theorem pointMapRing_eq_pointMapOfRingHom {L : Type*} [Field L] [DecidableEq F] [DecidableEq L]
    (φ : F →+* L) (W : WeierstrassCurve F) (P : W.toAffine.Point) :
    pointMapRing φ W P = pointMapOfRingHom φ P := by
  rcases P with _ | ⟨x, y, hP⟩
  · rfl
  · rfl

end Points

section Compare

variable {E₁ E₂ : WeierstrassCurve ℂ} [E₁.IsElliptic] [E₂.IsElliptic]

theorem exists_vcPoint_eq_of_isAnalyticUniformization {L : PeriodPair}
    {f₁ : ℂ →+ E₁.toAffine.Point} {f₂ : ℂ →+ E₂.toAffine.Point}
    (hf₁ : IsAnalyticUniformization L.lattice f₁) (hf₂ : IsAnalyticUniformization L.lattice f₂) :
    ∃ (D : VariableChange ℂ) (h : D • E₁ = E₂), ∀ z, f₂ z = vcPoint D h (f₁ z) := by
  obtain ⟨C₁, h₁, e₁⟩ := exists_vcPoint_of_isAnalyticUniformization hf₁
  obtain ⟨C₂, h₂, e₂⟩ := exists_vcPoint_of_isAnalyticUniformization hf₂
  have hinv : C₁⁻¹ • E₁ = weierstrassCurve L := by rw [← h₁, inv_smul_smul]
  refine ⟨C₂ * C₁⁻¹, by rw [mul_smul, hinv, h₂], fun z ↦ ?_⟩
  rw [vcPoint_mul_apply C₂ C₁⁻¹ hinv h₂, e₁ z, e₂ z]
  congr 1
  exact (vcPoint_inv_vcPoint C₁ h₁ _).symm

theorem j_eq_of_smul_eq {D : VariableChange ℂ} (h : D • E₁ = E₂) : E₂.j = E₁.j := by
  rw [← variableChange_j E₁ D]
  exact j_congr h.symm

theorem j_eq_of_isAnalyticUniformization {L : PeriodPair}
    {f₁ : ℂ →+ E₁.toAffine.Point} {f₂ : ℂ →+ E₂.toAffine.Point}
    (hf₁ : IsAnalyticUniformization L.lattice f₁) (hf₂ : IsAnalyticUniformization L.lattice f₂) :
    E₂.j = E₁.j := by
  obtain ⟨D, h, -⟩ := exists_vcPoint_eq_of_isAnalyticUniformization hf₁ hf₂
  exact j_eq_of_smul_eq h

theorem weberFunction_eq_of_isAnalyticUniformization {L : PeriodPair} (hE₁ : IsShortForm E₁)
    (hE₂ : IsShortForm E₂) {f₁ : ℂ →+ E₁.toAffine.Point} {f₂ : ℂ →+ E₂.toAffine.Point}
    (hf₁ : IsAnalyticUniformization L.lattice f₁) (hf₂ : IsAnalyticUniformization L.lattice f₂)
    (z : ℂ) : weberFunction E₂ (f₂ z) = weberFunction E₁ (f₁ z) := by
  obtain ⟨D, h, e⟩ := exists_vcPoint_eq_of_isAnalyticUniformization hf₁ hf₂
  rw [e z, vcPoint_eq_variableChangePoint]
  exact weberFunction_variableChangePoint D h hE₁ hE₂ _

end Compare

section Ideal

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [_root_.NumberField.IsTotallyComplex K]

variable {E₁ E₂ : WeierstrassCurve ℂ} [E₁.IsElliptic] [E₂.IsElliptic]


include hK in
theorem exists_unit_automorphismPoint_eq (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {E : WeierstrassCurve ℂ}
    [E.IsElliptic] {f : ℂ →+ E.toAffine.Point}
    (hf : IsAnalyticUniformization (idealLattice (algebraMap K ℂ) 𝔞) f)
    (ξ : MulAction.stabilizer (VariableChange ℂ) E) :
    ∃ ε : (𝓞 K)ˣ, ∀ z, automorphismPoint ξ (f z) =
      f (algebraMap K ℂ (algebraMap (𝓞 K) K ε) * z) := by
  classical
  have hL := lattice_idealPeriodPair (algebraMap K ℂ) hK 𝔞
  have hξ : ξ.1 • E = E := MulAction.mem_stabilizer_iff.mp ξ.2
  have hg := hf.vcPoint ξ.1 hξ
  rw [← hL] at hf hg
  obtain ⟨c, -, hcl, hcz⟩ := exists_mul_eq_of_isAnalyticUniformization hf hg
  rw [hL] at hcl
  obtain ⟨ε, rfl⟩ := exists_unit_of_forall_mem_iff (algebraMap K ℂ) hK _ hcl
  refine ⟨ε, fun z ↦ ?_⟩
  have e := hcz z
  rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, vcPointEquiv_apply] at e
  rw [automorphismPoint, ← vcPoint_eq_variableChangePoint, e]

end Ideal

end

end Elliptic
end GroundTheory.Global
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField Module IsDedekindDomain IntermediateField IdeleGroup WeierstrassCurve GroundTheory.Arith.Abelian
open GroundTheory.LocalField (restrictAb le_maximalAbelianExtension maximalAbelianExtension)
open scoped nonZeroDivisors

section Fixed

variable {K : Type*} [Field K] [Algebra K ℂ]

theorem forall_adjoin_apply_eq (σ : ℂ ≃ₐ[K] ℂ) {S : Set ℂ} (h : ∀ x ∈ S, σ x = x) :
    ∀ x ∈ IntermediateField.adjoin K S, σ x = x := by
  have hle : IntermediateField.adjoin K S ≤ fixedField (Subgroup.zpowers σ) := by
    rw [adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, mem_fixedField_iff]
    have hst : σ ∈ MulAction.stabilizer (ℂ ≃ₐ[K] ℂ) x := h x hx
    intro f hf
    exact (Subgroup.zpowers_le.2 hst) hf
  intro x hx
  exact (mem_fixedField_iff _ _).1 (hle hx) σ (Subgroup.mem_zpowers σ)

theorem le_of_forall_algEquiv {F₁ F₂ : IntermediateField K ℂ}
    (h : ∀ σ : ℂ ≃ₐ[K] ℂ, (∀ x ∈ F₂, σ x = x) → ∀ x ∈ F₁, σ x = x) : F₁ ≤ F₂ := by
  intro x hx
  have hx' : x ∈ (⊥ : IntermediateField F₂ ℂ) := by
    rw [mem_bot_iff_forall_algEquiv_apply_eq]
    intro τ
    exact h (τ.restrictScalars K) (fun y hy ↦ τ.commutes ⟨y, hy⟩) x hx
  obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.1 hx'
  exact a.2

theorem eq_of_forall_algEquiv {F₁ F₂ : IntermediateField K ℂ}
    (h : ∀ σ : ℂ ≃ₐ[K] ℂ, (∀ x ∈ F₁, σ x = x) ↔ (∀ x ∈ F₂, σ x = x)) : F₁ = F₂ :=
  le_antisymm (le_of_forall_algEquiv fun σ hσ ↦ (h σ).2 hσ)
    (le_of_forall_algEquiv fun σ hσ ↦ (h σ).1 hσ)

end Fixed

section Artin

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]

theorem exists_idele_artinMap_eq (σ : ℂ ≃ₐ[K] ℂ) :
    ∃ s : IdeleGroup K, ∀ x : maximalAbelianExtension K (algebraicClosure K ℂ),
      ((artinMap K (algebraicClosure K ℂ) (IdeleClassGroup.mk K s) x : algebraicClosure K ℂ) : ℂ) =
        σ ((x : algebraicClosure K ℂ) : ℂ) := by
  set Ω := algebraicClosure K ℂ
  set M := maximalAbelianExtension K Ω
  let σΩ : Ω ≃ₐ[K] Ω := σ.restrictNormal Ω
  obtain ⟨c, hc⟩ := artinMap_surjective (K := K) (Ω := Ω) (σΩ.restrictNormal M)
  obtain ⟨s, rfl⟩ := IdeleClassGroup.mk_surjective K c
  refine ⟨s, fun x ↦ ?_⟩
  rw [hc]
  have h1 : ((σΩ.restrictNormal M x : M) : Ω) = σΩ (x : Ω) :=
    AlgEquiv.restrictNormal_commutes σΩ M x
  rw [h1]
  exact AlgEquiv.restrictNormal_commutes σ Ω (x : Ω)

theorem forall_rayClassField_apply_eq_iff (σ : ℂ ≃ₐ[K] ℂ) (s : IdeleGroup K)
    (hs : ∀ x : maximalAbelianExtension K (algebraicClosure K ℂ),
      ((artinMap K (algebraicClosure K ℂ) (IdeleClassGroup.mk K s) x : algebraicClosure K ℂ) : ℂ) =
        σ ((x : algebraicClosure K ℂ) : ℂ))
    (𝔪 : Modulus K) :
    (∀ x ∈ 𝔪.rayClassField ℂ, σ x = x) ↔
      IdeleClassGroup.mk K s ∈ 𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) := by
  set M := 𝔪.rayClassField ℂ
  rw [← 𝔪.range_ideleClassNorm_rayClassField ℂ, ← ker_reciprocityMap, MonoidHom.mem_ker,
    reciprocityMap_mk]
  constructor
  · intro h
    refine AlgEquiv.ext fun z ↦ Subtype.ext ?_
    rw [ideleSymbol_apply_eq_of_artinMap σ s hs M z]
    exact h z z.2
  · intro h x hx
    have e := ideleSymbol_apply_eq_of_artinMap σ s hs M ⟨x, hx⟩
    rw [h] at e
    exact e.symm

end Artin

section Hilbert

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [_root_.NumberField.IsTotallyComplex K]


include hK in
theorem j_weierstrassCurve_idealPeriodPair_eq (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {E : WeierstrassCurve ℂ} [E.IsElliptic] {f : ℂ →+ E.toAffine.Point}
    (hf : IsAnalyticUniformization (idealLattice (algebraMap K ℂ) 𝔞) f) :
    (weierstrassCurve (idealPeriodPair (algebraMap K ℂ) hK 𝔞)).j = E.j := by
  rw [← lattice_idealPeriodPair (algebraMap K ℂ) hK 𝔞] at hf
  exact j_eq_of_isAnalyticUniformization hf
    (isAnalyticUniformization_toPointHom (idealPeriodPair (algebraMap K ℂ) hK 𝔞))


include hK in
theorem adjoin_j_eq_hilbertClassField_of_isAnalyticUniformization (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {E : WeierstrassCurve ℂ} [E.IsElliptic] {f : ℂ →+ E.toAffine.Point}
    (hf : IsAnalyticUniformization (idealLattice (algebraMap K ℂ) 𝔞) f) :
    K⟮E.j⟯ = hilbertClassField K ℂ := by
  rw [← j_weierstrassCurve_idealPeriodPair_eq hK 𝔞 hf]
  exact adjoin_j_eq_hilbertClassField hK
    (ellOf (algebraMap K ℂ) _ (latticeEnd_idealPeriodPair (algebraMap K ℂ) hK 𝔞))


include hK in
theorem mk_mem_map_standardOpenSubgroup_of_apply_j_eq (σ : ℂ ≃ₐ[K] ℂ) (s : IdeleGroup K)
    (hs : ∀ x : maximalAbelianExtension K (algebraicClosure K ℂ),
      ((artinMap K (algebraicClosure K ℂ) (IdeleClassGroup.mk K s) x : algebraicClosure K ℂ) : ℂ) =
        σ ((x : algebraicClosure K ℂ) : ℂ))
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {E : WeierstrassCurve ℂ} [E.IsElliptic]
    {f : ℂ →+ E.toAffine.Point} (hf : IsAnalyticUniformization (idealLattice (algebraMap K ℂ) 𝔞) f)
    (hj : σ E.j = E.j) :
    IdeleClassGroup.mk K s ∈ (standardOpenSubgroup K).map (IdeleClassGroup.mk K) := by
  have hfix : ∀ x ∈ (Modulus.one : Modulus K).rayClassField ℂ, σ x = x := by
    intro x hx
    have hx' : x ∈ K⟮E.j⟯ := by
      rw [adjoin_j_eq_hilbertClassField_of_isAnalyticUniformization hK 𝔞 hf]
      exact hx
    exact forall_adjoin_apply_eq σ (fun y hy ↦ by rw [Set.mem_singleton_iff.1 hy]; exact hj) x hx'
  rw [← Modulus.congruenceSubgroup_one]
  exact (forall_rayClassField_apply_eq_iff σ s hs Modulus.one).1 hfix

end Hilbert

end

end Elliptic
end GroundTheory.Global
