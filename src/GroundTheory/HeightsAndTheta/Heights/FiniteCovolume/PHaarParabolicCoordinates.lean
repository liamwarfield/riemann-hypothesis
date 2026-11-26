module

public import GroundTheory.AutomorphicForms.HaarSK
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerLevi
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.RelIndexNeZeroAndLeOfNsmulMem

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PHaarParabolicCoordinates
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal NNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem HaarParabolicCoordinates.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : ParabolicDecomposition.Statement h v) (h₂ : ArchUnimodular.Statement h v)
    (h₃ : MajorantStabCompact.Statement h v) (h₄ : LineStabHaar.Statement h v) :
    HaarParabolicCoordinates.Statement h v := by
  intro M μ _ x₀ hx₀ hiso
  have : μ.IsMulRightInvariant := h₂ μ
  have : CompactSpace M.stab := isCompact_iff_compactSpace.mp (h₃ M)
  set κ : Measure M.stab := Measure.haarMeasure ⊤ with hκ
  have : IsProbabilityMeasure κ :=
    ⟨by simpa using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts M.stab))⟩
  have hSK : Function.Surjective (HaarSK.mulMap (lineStab h v x₀) M.stab) := by
    intro g
    obtain ⟨p, k, hk, rfl, hp⟩ := h₁ M x₀ hx₀ hiso g
    exact ⟨(⟨p, hp⟩, ⟨k, hk⟩), rfl⟩
  obtain ⟨c, -, hc⟩ := HaarSK.exists_lintegral_eq μ (isClosed_lineStab h v x₀) (h₃ M) hSK
    (Measure.haar : Measure (lineStab h v x₀)) κ
  obtain ⟨ν, τ, hν, hτ, -, hτx, hP⟩ := h₄ x₀ hx₀ hiso Measure.haar
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    intro h0
    have h1 := hc 1 measurable_const
    rw [h0, zero_mul] at h1
    simp only [Pi.one_apply, lintegral_const, one_mul] at h1
    exact (Measure.IsOpenPosMeasure.open_pos Set.univ isOpen_univ Set.univ_nonempty) h1
  have := hν
  refine ⟨(c : ℝ≥0∞) • ν, κ, τ, Measure.IsHaarMeasure.smul ν hc0 ENNReal.coe_ne_top, inferInstance,
    inferInstance, hτ, hτx, fun f hf => ?_⟩
  have hφ : Measurable fun g : archUnitary h v => ∫⁻ k : M.stab, f (g * k) ∂κ :=
    (hf.comp (measurable_fst.mul (measurable_subtype_coe.comp measurable_snd))).lintegral_prod_right'
  have hPφ := hP _ hφ
  rw [hc f hf, hPφ, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_congr fun b => ?_
  have hswap : ∫⁻ x : vecFixGroup h v x₀, ∫⁻ k : M.stab, f ((x : archUnitary h v) * τ b * k) ∂κ ∂ν =
      ∫⁻ k : M.stab, ∫⁻ x : vecFixGroup h v x₀, f ((x : archUnitary h v) * (τ b * k)) ∂ν ∂κ := by
    rw [lintegral_lintegral_swap]
    · simp only [mul_assoc]
    · exact (hf.comp (((measurable_subtype_coe.comp measurable_fst).mul_const (τ b)).mul
        (measurable_subtype_coe.comp measurable_snd))).aemeasurable
  simp only [lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, hswap]
  ring

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PHyperbolicPairTransitive
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

namespace HyperbolicPairTransitive


omit [NumberField E] in
theorem sesq_swap (h : HermitianForm F E W) (x y : W) :
    h.toSesq y x = conj F E (h.toSesq x y) :=
  (h.isSymm.eq x y).symm


omit [NumberField E] in
theorem exists_unitary_of_preserves (h : HermitianForm F E W) [FiniteDimensional E W]
    (f : W →ₗ[E] W) (hf : ∀ x y, h.toSesq (f x) (f y) = h.toSesq x y) :
    ∃ g : h.unitaryGroup, ∀ z, (g : W ≃ₗ[E] W) z = f z := by
  have inj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun z hz => h.nonsingular.1 ?_
    ext y
    rw [← hf, hz, map_zero]
    rfl
  exact ⟨⟨LinearEquiv.ofInjectiveEndo f inj, fun x y => hf x y⟩, fun _ => rfl⟩

theorem exists_unitary_sub_smul (h : HermitianForm F E W) [FiniteDimensional E W] (u : W) (β : E)
    (hβ : β ≠ 0) (hs : β + conj F E β = h.toSesq u u) :
    ∃ g : h.unitaryGroup, ∀ z, (g : W ≃ₗ[E] W) z = z - (h.toSesq u z / β) • u := by
  have hβ' : conj F E β ≠ 0 := by
    intro h0; apply hβ; rw [← conj_conj (F := F) β, h0, map_zero]
  obtain ⟨g, hg⟩ := exists_unitary_of_preserves h
    (LinearMap.id - β⁻¹ • (h.toSesq u).smulRight u) (fun x y => by
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
        LinearMap.smulRight_apply, smul_smul, map_sub, LinearMap.map_smulₛₗ, map_smul,
        LinearMap.smul_apply, smul_eq_mul, conjHom_apply, map_mul, map_inv₀]
      rw [sesq_swap h x u, sesq_swap h u u, ← hs, map_add (f := _), conj_conj]
      field_simp
      simp only [conj_conj]
      ring)
  exact ⟨g, fun z => by
    rw [hg]
    simp [smul_smul, div_eq_inv_mul]⟩

theorem exists_unitary_carry (h : HermitianForm F E W) [FiniteDimensional E W] (x y c : W)
    (hxy : h.toSesq x x = h.toSesq y y) (hx : h.toSesq x x ≠ 0)
    (hxc : h.toSesq x c = 0) (hyc : h.toSesq y c = 0) :
    ∃ g : h.unitaryGroup, (g : W ≃ₗ[E] W) x = y ∧ (g : W ≃ₗ[E] W) c = c := by
  have hr : ∀ z, conj F E (h.toSesq z z) = h.toSesq z z := fun z => h.isSymm.eq z z
  have two : (2 : E) ≠ 0 := two_ne_zero
  by_cases hβ : h.toSesq (x - y) x = 0
  ·
    have hyx : h.toSesq y x = h.toSesq x x := by
      rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at hβ
      exact hβ.symm
    obtain ⟨g₁, hg₁⟩ := exists_unitary_sub_smul h (x + y) (2 * h.toSesq x x)
      (mul_ne_zero two hx) (by
        simp only [map_add (f := _), LinearMap.add_apply, map_mul, map_ofNat, hr]
        rw [sesq_swap h y x, hyx, hr, ← hxy]; ring)
    obtain ⟨g₂, hg₂⟩ := exists_unitary_sub_smul h y (h.toSesq y y / 2)
      (div_ne_zero (hxy ▸ hx) two) (by rw [map_div₀, map_ofNat, hr]; ring)
    refine ⟨g₂ * g₁, ?_, ?_⟩
    · change (g₂ : W ≃ₗ[E] W) ((g₁ : W ≃ₗ[E] W) x) = y
      have e1 : (g₁ : W ≃ₗ[E] W) x = -y := by
        rw [hg₁, map_add (f := _), LinearMap.add_apply, hyx, ← two_mul, div_self (mul_ne_zero two hx),
          one_smul]
        abel
      have hy : h.toSesq y y ≠ 0 := hxy ▸ hx
      rw [e1, hg₂, map_neg, neg_div, neg_smul, sub_neg_eq_add,
        show h.toSesq y y / (h.toSesq y y / 2) = 2 by field_simp, two_smul]
      abel
    · change (g₂ : W ≃ₗ[E] W) ((g₁ : W ≃ₗ[E] W) c) = c
      rw [hg₁, map_add (f := _), LinearMap.add_apply, hxc, hyc, add_zero, zero_div, zero_smul, sub_zero,
        hg₂, hyc, zero_div, zero_smul, sub_zero]
  · obtain ⟨g, hg⟩ := exists_unitary_sub_smul h (x - y) (h.toSesq (x - y) x) hβ (by
      simp only [map_sub, LinearMap.sub_apply, hr]
      rw [sesq_swap h x y, hxy, conj_conj]; ring)
    refine ⟨g, ?_, ?_⟩
    · rw [hg, div_self hβ, one_smul, sub_sub_cancel]
    · rw [hg, map_sub, LinearMap.sub_apply, hxc, hyc, sub_zero, zero_div, zero_smul, sub_zero]

theorem proof (h : HermitianForm F E W) [FiniteDimensional E W] :
    HyperbolicPairTransitive.Statement h := by
  intro v w v' w' ⟨hv, hw, hvw⟩ ⟨hv', hw', hvw'⟩
  have hwv : h.toSesq w v = 1 := by rw [sesq_swap h v w, hvw, map_one]
  have hwv' : h.toSesq w' v' = 1 := by rw [sesq_swap h v' w', hvw', map_one]
  have ee : ∀ a b : W, h.toSesq a a = 0 → h.toSesq b b = 0 → h.toSesq a b = 1 →
      h.toSesq b a = 1 → h.toSesq (a + b) (a + b) = 2 ∧ h.toSesq (a - b) (a - b) = -2 ∧
        h.toSesq (a - b) (a + b) = 0 := by
    intro a b ha hb hab hba
    simp only [map_add (f := _), map_sub, LinearMap.add_apply, LinearMap.sub_apply, ha, hb, hab, hba]
    norm_num
  obtain ⟨e1, f1, fe1⟩ := ee v w hv hw hvw hwv
  obtain ⟨e2, f2, fe2⟩ := ee v' w' hv' hw' hvw' hwv'
  have two : (2 : E) ≠ 0 := two_ne_zero
  obtain ⟨g₁, hg₁, -⟩ := exists_unitary_carry h (v + w) (v' + w') 0 (e1.trans e2.symm)
    (e1 ▸ two) (map_zero _) (map_zero _)
  have hf : h.toSesq ((g₁ : W ≃ₗ[E] W) (v - w)) (v' + w') = 0 := by
    rw [← hg₁, g₁.2, fe1]
  obtain ⟨g₂, hg₂, hc⟩ := exists_unitary_carry h ((g₁ : W ≃ₗ[E] W) (v - w)) (v' - w') (v' + w')
    (by rw [g₁.2, f1, f2]) (by rw [g₁.2, f1]; exact neg_ne_zero.2 two) hf fe2
  have key : ∀ z, (g₂ * g₁ : h.unitaryGroup) • z = (g₂ : W ≃ₗ[E] W) ((g₁ : W ≃ₗ[E] W) z) :=
    fun _ => rfl
  have hE : (g₂ : W ≃ₗ[E] W) ((g₁ : W ≃ₗ[E] W) (v + w)) = v' + w' := by rw [hg₁, hc]
  have hv2 : v = (2 : E)⁻¹ • ((v + w) + (v - w)) := by
    rw [add_add_sub_cancel, ← two_smul E v, smul_smul, inv_mul_cancel₀ two, one_smul]
  have hw2 : w = (2 : E)⁻¹ • ((v + w) - (v - w)) := by
    rw [add_sub_sub_cancel, ← two_smul E w, smul_smul, inv_mul_cancel₀ two, one_smul]
  refine ⟨g₂ * g₁, ?_, ?_⟩
  · rw [key, hv2, map_smul, map_smul, map_add (f := _), map_add (f := _), hE, hg₂, add_add_sub_cancel,
      ← two_smul E v', smul_smul, inv_mul_cancel₀ two, one_smul]
  · rw [key, hw2, map_smul, map_smul, map_sub, map_sub, hE, hg₂, add_sub_sub_cancel,
      ← two_smul E w', smul_smul, inv_mul_cancel₀ two, one_smul]

end HyperbolicPairTransitive

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PAdaptedReduction
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

section Transport

variable {h : HermitianForm F E W}

theorem sesq_unitary_smul (g : h.unitaryGroup) (x y : W) :
    h.toSesq (g • x) (g • y) = h.toSesq x y :=
  g.2 x y

theorem unitary_smul_scalar_smul (g : h.unitaryGroup) (a : E) (x : W) : g • (a • x) = a • (g • x) :=
  map_smul (g : W ≃ₗ[E] W) a x

theorem mem_inv_smul_iff {g : h.unitaryGroup} {La : AddSubgroup W} {x : W} :
    x ∈ g⁻¹ • La ↔ g • x ∈ La := by
  change x ∈ ((g⁻¹ : h.unitaryGroup) : W ≃ₗ[E] W) • La ↔ _
  rw [AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem lineCoeffs_inv_smul (g : h.unitaryGroup) (La : AddSubgroup W) (x : W) :
    lineCoeffs (E := E) (g⁻¹ • La) x = lineCoeffs (E := E) La (g • x) := by
  ext a
  change a • x ∈ g⁻¹ • La ↔ a • (g • x) ∈ La
  rw [mem_inv_smul_iff, unitary_smul_scalar_smul]

theorem dualLattice_inv_smul (g : h.unitaryGroup) (La : AddSubgroup W) :
    dualLattice h (g⁻¹ • La) = g⁻¹ • dualLattice h La := by
  ext y
  rw [mem_inv_smul_iff]
  change (∀ x ∈ g⁻¹ • La, h.toSesq y x ∈ integralClosure ℤ E) ↔
    ∀ x ∈ La, h.toSesq (g • y) x ∈ integralClosure ℤ E
  constructor
  · intro hy x hx
    have hx' : g⁻¹ • x ∈ g⁻¹ • La := by rw [mem_inv_smul_iff, smul_inv_smul]; exact hx
    have := hy _ hx'
    rwa [← sesq_unitary_smul g, smul_inv_smul] at this
  · intro hy x hx
    rw [mem_inv_smul_iff] at hx
    rw [← sesq_unitary_smul g]
    exact hy _ hx

theorem isDIntegral_inv_smul (g : h.unitaryGroup) {D : ℕ} {La : AddSubgroup W}
    (hLa : IsDIntegral h D La) : IsDIntegral h D (g⁻¹ • La) := by
  set γ : W ≃ₗ[E] W := ((g⁻¹ : h.unitaryGroup) : W ≃ₗ[E] W) with hγ
  have hinj : Function.Injective (DistribMulAction.toAddMonoidEnd (W ≃ₗ[E] W) W γ) :=
    fun x y hxy => γ.injective hxy
  have hrel : (g⁻¹ • La).relIndex (dualLattice h (g⁻¹ • La)) =
      La.relIndex (dualLattice h La) := by
    rw [dualLattice_inv_smul]
    change (γ • La).relIndex (γ • dualLattice h La) = _
    rw [AddSubgroup.pointwise_smul_def, AddSubgroup.pointwise_smul_def]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro a x hx
    rw [mem_inv_smul_iff] at hx ⊢
    rw [unitary_smul_scalar_smul]
    exact hLa.isLattice.smul_mem a _ hx
  · have hfg := hLa.isLattice.fg
    change (γ • La).FG
    rw [AddSubgroup.pointwise_smul_def]
    rw [AddSubgroup.fg_iff_exists_fin_addMonoidHom] at hfg ⊢
    obtain ⟨k, f, hf⟩ := hfg
    exact ⟨k, γ.toLinearMap.toAddMonoidHom.comp f, by
      rw [AddMonoidHom.range_comp, hf]
      rfl⟩
  · have hset : ((g⁻¹ • La : AddSubgroup W) : Set W) =
        γ.toLinearMap '' (La : Set W) := by
      ext y
      constructor
      · intro hy
        exact ⟨g • y, mem_inv_smul_iff.1 hy, inv_smul_smul g y⟩
      · rintro ⟨x, hx, rfl⟩
        change g⁻¹ • x ∈ g⁻¹ • La
        rw [mem_inv_smul_iff, smul_inv_smul]
        exact hx
    rw [hset, Submodule.span_image, hLa.isLattice.span_eq_top, Submodule.map_top,
      LinearMap.range_eq_top]
    exact LinearEquiv.surjective _
  · intro x hx y hy
    rw [mem_inv_smul_iff] at hx hy
    rw [← sesq_unitary_smul g]
    exact hLa.integral _ hx _ hy
  · rw [hrel]
    exact hLa.index_ne_zero
  · rw [hrel]
    exact hLa.index_le

end Transport

theorem AdaptedReduction.proof (h : HermitianForm F E W) [FiniteDimensional E W]
    (h₁ : HyperbolicPairTransitive.Statement h) (h₂ : LineNormalForm.Statement h)
    (h₃ : ComplementLattice.Statement h) : AdaptedReduction.Statement h := by
  intro v₀ w₀ hp h' hh' D
  obtain ⟨KK, hKK, n, hn, H⟩ := h₂ D
  obtain ⟨D', hD'⟩ := h₃ v₀ w₀ hp h' hh' D n hn
  refine ⟨KK, hKK, n, D', hn, fun La l hLa hl => ?_⟩
  obtain ⟨v, w, hvl, hvw, hK, hdec⟩ := H La l hLa hl
  obtain ⟨g, hgv, hgw⟩ := h₁ v₀ w₀ v w hp hvw
  have hI : lineCoeffs (E := E) (g⁻¹ • La) v₀ = lineCoeffs (E := E) La v := by
    rw [lineCoeffs_inv_smul, hgv]
  have hJ : lineCoeffs (E := E) (g⁻¹ • La) w₀ = lineCoeffs (E := E) La w := by
    rw [lineCoeffs_inv_smul, hgw]
  have hwv : h.toSesq w v = 1 := by
    rw [← h.isSymm.eq v w, hvw.2.2, map_one]
  have hsplit : ∀ x ∈ g⁻¹ • La, ∃ a ∈ lineCoeffs (E := E) (g⁻¹ • La) v₀,
      ∃ b ∈ lineCoeffs (E := E) (g⁻¹ • La) w₀,
        n • x - a • v₀ - b • w₀ ∈ hypComplement h v₀ w₀ := by
    intro x hx
    rw [mem_inv_smul_iff] at hx
    obtain ⟨ha, hb⟩ := hdec _ hx
    refine ⟨(n : E) * h.toSesq w (g • x), by rw [hI]; exact ha,
      (n : E) * h.toSesq v (g • x), by rw [hJ]; exact hb, ?_⟩
    rw [mem_hypComplement, ← sesq_unitary_smul g v₀, ← sesq_unitary_smul g w₀, hgv, hgw,
      ← Nat.cast_smul_eq_nsmul E, smul_sub, smul_sub, unitary_smul_scalar_smul, unitary_smul_scalar_smul,
      unitary_smul_scalar_smul, hgv, hgw]
    simp only [map_sub, map_smul, smul_eq_mul, hvw.1, hvw.2.1, hvw.2.2, hwv]
    constructor <;> ring
  refine ⟨g, g⁻¹ • La, smul_inv_smul g La, hgv ▸ hvl, ?_, hsplit,
    hD' _ (isDIntegral_inv_smul g hLa) hsplit⟩
  rw [hI, hJ]
  exact hK

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnfoldingTorus
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem invApply_mul {h : HermitianForm F E W} {v : Basis ι E W} (a b : archUnitary h v)
    (y : InfinitePlace E → ι → ℂ) : invApply (a * b) y = invApply b (invApply a y) := by
  funext w
  simp only [invApply, _root_.mul_inv_rev, Subgroup.coe_mul, Pi.mul_apply, Units.val_mul,
    Matrix.mulVec_mulVec]


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem invApply_of_mem_vecFixGroup {h : HermitianForm F E W} {v : Basis ι E W} {x₀ : W}
    {x : archUnitary h v} (hx : x ∈ vecFixGroup h v x₀) : invApply x (vecAt v x₀) = vecAt v x₀ :=
  funext fun w => mem_vecFixGroup.1 (inv_mem hx) w


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem len_invApply_of_mem_stab {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    {k : archUnitary h v} (hk : k ∈ M.stab) (y : InfinitePlace E → ι → ℂ) :
    M.len (invApply k y) = M.len y := by
  unfold Majorant.len
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  have hk' := inv_mem hk
  rw [Majorant.stab, Subgroup.mem_subgroupOf] at hk'
  have hA := mem_unitaryGroupMatrix.1 ((Subgroup.mem_pi _).1 hk' w (Set.mem_univ w))
  set A : Matrix ι ι ℂ := (((k⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
    with hA_def
  have hA' : Aᴴ * M.P w * A = M.P w := hA
  simp only [invApply]
  rw [← hA_def, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hA']


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem vecStabGroup_le_vecFixGroup [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
    (h : HermitianForm F E W) (v : Basis ι E W) (La : AddSubgroup W) (x₀ : W) :
    vecStabGroup h v La x₀ ≤ vecFixGroup h v x₀ := by
  rintro _ ⟨γ, hγ, rfl⟩
  have e := archEmbed_smul_vecAt h v (γ : h.unitaryGroup) x₀
  rw [show (γ : h.unitaryGroup) • x₀ = x₀ from MulAction.mem_stabilizer_iff.1 hγ] at e
  exact fun w => congrFun e w

theorem ae_forall_ne_zero (κ : Type*) [Fintype κ] : ∀ᵐ b : κ → ℂ, ∀ w, b w ≠ 0 := by
  rw [ae_all_iff]
  intro w
  have h0 : volume ((fun b : κ → ℂ => b w) ⁻¹' {0}) = 0 :=
    Measure.pi_eval_preimage_null _ (measure_singleton 0)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with b hb
  exact hb

theorem UnfoldingTorus.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : ∀ M : Majorant h v,
      UnfoldAlongSubgroup.Statement (archUnitary h v) ((InfinitePlace E → ℂ) × M.stab))
    (h₂ : HaarParabolicCoordinates.Statement h v) (h₃ : StabilizerCovolumeFinite.Statement h v) :
    UnfoldingTorus.Statement h v := by
  intro M μ _ D La x₀ hLa hx₀ hne hiso
  obtain ⟨ν, κ, τ, hν, -, hκ, hτm, hτ, hμ⟩ := h₂ M μ x₀ hne hiso
  obtain ⟨FD₀, hFD₀, h0, htop⟩ := h₃ D La x₀ hLa hx₀ hne hiso ν hν
  refine ⟨ν FD₀, h0, htop, fun FD hFD t ht => ?_⟩
  set y₀ := vecAt v x₀ with hy₀
  set wt : (InfinitePlace E → ℂ) → ℝ≥0∞ := fun b => ∏ w, ‖b w‖ₑ ^ (2 * (finrank E W - 2))
    with hwt
  set S := {g : archUnitary h v | M.len (invApply g y₀) < t} with hS_def
  set T := {b : InfinitePlace E → ℂ | M.len (fun w => b w • y₀ w) < t} with hT_def
  have hS : MeasurableSet S := measurableSet_below M y₀ t

  have : SecondCountableTopology (vecStabGroup h v La x₀) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have : DiscreteTopology (vecStabGroup h v La x₀) := by
    have := ArchLatticeDiscrete.proof h v La hLa.isLattice
    have hle : vecStabGroup h v La x₀ ≤ archLatticeGroup h v La := by
      rintro _ ⟨γ, -, rfl⟩
      exact ⟨(γ : h.unitaryGroup), γ.2, rfl⟩
    exact DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective hle)
  have : Countable (vecStabGroup h v La x₀) :=
    TopologicalSpace.separableSpace_iff_countable.1 inferInstance

  let s : (InfinitePlace E → ℂ) × M.stab → archUnitary h v := fun y => τ y.1 * y.2
  have hwtm : Measurable wt :=
    Finset.measurable_prod _ fun w _ => (measurable_pi_apply w).enorm.pow_const _
  have hsm' : Measurable s := (hτm.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
  have hsm : Measurable fun p : vecFixGroup h v x₀ × ((InfinitePlace E → ℂ) × M.stab) =>
      (p.1 : archUnitary h v) * s p.2 :=
    (measurable_subtype_coe.comp measurable_fst).mul (hsm'.comp measurable_snd)
  have hform : ∀ f : archUnitary h v → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μ =
      ∫⁻ y, ∫⁻ x, f (x * s y) ∂ν ∂((volume.withDensity wt).prod κ) := by
    intro f hf
    have hin : Measurable fun y => ∫⁻ x : vecFixGroup h v x₀, f (x * s y) ∂ν :=
      (hf.comp hsm).lintegral_prod_left'
    rw [hμ f hf, lintegral_prod _ hin.aemeasurable,
      lintegral_withDensity_eq_lintegral_mul _ hwtm hin.lintegral_prod_right']
    rfl

  have hf : Measurable (S.indicator (1 : archUnitary h v → ℝ≥0∞)) := measurable_one.indicator hS
  have hinv : ∀ x : vecFixGroup h v x₀, ∀ g,
      S.indicator (1 : archUnitary h v → ℝ≥0∞) (x * g) = S.indicator 1 g := by
    intro x g
    have hx : invApply (x : archUnitary h v) y₀ = y₀ := invApply_of_mem_vecFixGroup x.2
    simp only [hS_def, Set.indicator_apply, Set.mem_ofPred_eq, invApply_mul, hx, Pi.one_apply]
  have key := h₁ M μ (vecFixGroup h v x₀) ν ((volume.withDensity wt).prod κ) s hsm hform
    (vecStabGroup h v La x₀) (vecStabGroup_le_vecFixGroup h v La x₀) FD FD₀ hFD hFD₀ _ hf hinv
  rw [Set.inter_comm, ← Measure.restrict_apply hS, ← lintegral_indicator_one hS, key]
  congr 1

  have hmS : Measurable fun y => S.indicator (1 : archUnitary h v → ℝ≥0∞) (s y) := hf.comp hsm'
  rw [lintegral_prod _ hmS.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ hwtm hmS.lintegral_prod_right']
  refine lintegral_congr_ae ?_
  filter_upwards [ae_forall_ne_zero (InfinitePlace E)] with b hb
  have hk : ∀ k : M.stab, S.indicator (1 : archUnitary h v → ℝ≥0∞) (s (b, k)) =
      T.indicator 1 b := by
    intro k
    simp only [s, Set.indicator_apply, hS_def, hT_def, Set.mem_ofPred_eq, invApply_mul, hτ b hb,
      len_invApply_of_mem_stab M k.2, Pi.one_apply]
  simp only [Pi.mul_apply, hk, lintegral_const, measure_univ, mul_one]
  by_cases hbT : b ∈ T
  · simp [Set.indicator_of_mem hbT]
  · simp [Set.indicator_of_notMem hbT]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PVectorOrbitsFinite
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

theorem exists_finset_of_finite_image {α β : Type*} (s : Set α) (f : α → β) (hf : (f '' s).Finite)
    (P : α → α → Prop) (hP : ∀ x ∈ s, ∀ y ∈ s, f x = f y → P y x) :
    ∃ S : Finset α, (S : Set α) ⊆ s ∧ ∀ x ∈ s, ∃ y ∈ S, P y x := by
  classical
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨∅, by simp, fun x _ => isEmptyElim x⟩
  choose! g hg1 hg2 using fun b (hb : b ∈ f '' s) => hb
  refine ⟨hf.toFinset.image g, ?_, fun x hx => ?_⟩
  · intro y hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
    exact hg1 b (hf.mem_toFinset.1 hb)
  · have hb : f x ∈ f '' s := ⟨x, hx, rfl⟩
    exact ⟨g (f x), Finset.mem_image_of_mem _ (hf.mem_toFinset.2 hb),
      hP x hx _ (hg1 _ hb) (hg2 _ hb).symm⟩

section Vectors

variable {E : Type*} [Field E] [NumberField E] {W : Type*} [AddCommGroup W] [Module E W]

omit [NumberField E] in
theorem mem_ringMultiples {x y : W} : y ∈ ringMultiples E x ↔ ∃ a : 𝓞 E, (a : E) • x = y := by
  simp [ringMultiples]

theorem exists_unit_of_ringMultiples_eq {x b : W} (hb : b ≠ 0)
    (hxb : ringMultiples E x = ringMultiples E b) : ∃ ε : (𝓞 E)ˣ, x = ((ε : 𝓞 E) : E) • b := by
  have hx : x ∈ ringMultiples E b := hxb ▸ mem_ringMultiples.2 ⟨1, by simp⟩
  have hbx : b ∈ ringMultiples E x := hxb ▸ mem_ringMultiples.2 ⟨1, by simp⟩
  obtain ⟨a, ha⟩ := mem_ringMultiples.1 hx
  obtain ⟨c, hc⟩ := mem_ringMultiples.1 hbx
  have h1 : ((c : E) * (a : E)) • b = (1 : E) • b := by rw [mul_smul, ha, hc, one_smul]
  have hca : c * a = 1 := RingOfIntegers.ext (by simpa using smul_left_injective E hb h1)
  exact ⟨⟨a, c, by rw [mul_comm]; exact hca, hca⟩, ha.symm⟩

end Vectors

section Spaces

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W]

omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem unitary_smul_smul {h : HermitianForm F E W} (γ : h.unitaryGroup) (c : E) (w : W) :
    γ • (c • w) = c • (γ • w) := by
  simp only [Subgroup.smul_def, LinearEquiv.smul_def, map_smul]

theorem line_vectorOrbits (h : HermitianForm F E W) (h₂ : IsotropicScaling.Statement h)
    (h₃ : BoundedIndexSubgroupsFinite.Statement W) (h₅ : LineIndexNeZero.Statement E W)
    {D : ℕ} {La : AddSubgroup W} {VV : Set W} (hLa : IsDIntegral h D La) (hsub : VV ⊆ La)
    (hiso : ∀ x ∈ VV, x ≠ 0 ∧ h.toSesq x x = 0) {C : ℕ} (hC : ∀ x ∈ VV, lineIndex E La x ≤ C)
    {v₀ : W} (hv₀ : v₀ ∈ VV) :
    ∃ S : Finset W, (S : Set W) ⊆ VV ∧ ∀ x ∈ VV, x ∈ Submodule.span E {v₀} →
      ∃ y ∈ S, ∃ γ ∈ latticeStab h La, γ • y = x := by
  classical
  obtain ⟨N, hN, hγ⟩ := h₂ La v₀ hLa.isLattice hLa.integral (hsub hv₀) (hiso v₀ hv₀).1
    (hiso v₀ hv₀).2
  have hUfin : Finite ((𝓞 E)ˣ ⧸ congruenceUnits E N) := by
    have : (congruenceUnits E N).FiniteIndex := ⟨CongruenceUnitsFiniteIndex.proof E N hN⟩
    exact Subgroup.finite_quotient_of_finiteIndex
  let L : Set W := {x ∈ VV | x ∈ Submodule.span E {v₀}}
  have hspan : ∀ x ∈ L, Submodule.span E {x} = Submodule.span E {v₀} := by
    rintro x ⟨hx, hxs⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hxs
    have hc : c ≠ 0 := by
      rintro rfl
      exact (hiso _ hx).1 (zero_smul E v₀)
    exact Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc) v₀
  have hT : ∀ x ∈ L, ringMultiples E x ∈ {H : AddSubgroup W |
      H ≤ La ⊓ (Submodule.span E {v₀}).toAddSubgroup ∧
      H.relIndex (La ⊓ (Submodule.span E {v₀}).toAddSubgroup) ≠ 0 ∧
      H.relIndex (La ⊓ (Submodule.span E {v₀}).toAddSubgroup) ≤ C} := by
    intro x hxL
    have h1 := h₅ La x hLa.isLattice (hsub hxL.1) (hiso x hxL.1).1
    have h2 := hC x hxL.1
    unfold lineIndex at h1 h2
    rw [hspan x hxL] at h1 h2
    refine ⟨fun y hy => ?_, h1, h2⟩
    obtain ⟨a, rfl⟩ := mem_ringMultiples.1 hy
    exact ⟨hLa.isLattice.smul_mem a x (hsub hxL.1), Submodule.smul_mem _ _ hxL.2⟩
  have hTfin := h₃ (La ⊓ (Submodule.span E {v₀}).toAddSubgroup) La hLa.isLattice.fg inf_le_left C
  choose! b hbL hb using fun H (hH : H ∈ (fun x => ringMultiples E x) '' L) => hH
  have hunit : ∀ x ∈ L, ∃ ε : (𝓞 E)ˣ, x = ((ε : 𝓞 E) : E) • b (ringMultiples E x) := by
    intro x hx
    have hH : ringMultiples E x ∈ (fun x => ringMultiples E x) '' L := ⟨x, hx, rfl⟩
    exact exists_unit_of_ringMultiples_eq (hiso _ (hbL _ hH).1).1 (hb _ hH).symm
  choose! ε hε using hunit
  let f : W → AddSubgroup W × ((𝓞 E)ˣ ⧸ congruenceUnits E N) :=
    fun x => (ringMultiples E x, QuotientGroup.mk (ε x))
  have hfin : (f '' L).Finite :=
    (hTfin.prod Set.finite_univ).subset (by rintro _ ⟨x, hx, rfl⟩; exact ⟨hT x hx, trivial⟩)
  have hP : ∀ x ∈ L, ∀ y ∈ L, f x = f y → ∃ γ ∈ latticeStab h La, γ • y = x := by
    intro x hx y hy hxy
    simp only [f, Prod.mk.injEq] at hxy
    obtain ⟨hR, hQ⟩ := hxy
    rw [QuotientGroup.eq] at hQ
    have hδ : (ε y)⁻¹ * ε x ∈ congruenceUnits E N := by
      have := inv_mem hQ
      rwa [mul_inv_rev, inv_inv] at this
    obtain ⟨γ, hγS, hγv⟩ := hγ _ hδ
    refine ⟨γ, hγS, ?_⟩
    have hx' := hε x hx
    have hy' := hε y hy
    rw [hR] at hx'
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hy.2
    have key : (((ε y)⁻¹ * ε x : (𝓞 E)ˣ) : 𝓞 E) * ((ε y : 𝓞 E)) = (ε x : 𝓞 E) := by
      rw [← Units.val_mul, mul_comm, mul_inv_cancel_left]
    have keyE : ((((ε y)⁻¹ * ε x : (𝓞 E)ˣ) : 𝓞 E) : E) * ((ε y : 𝓞 E) : E) = ((ε x : 𝓞 E) : E) := by
      rw [← key]
      rfl
    rw [← hc, unitary_smul_smul, hγv, smul_smul, mul_comm, ← smul_smul, hc,
      congrArg (fun t => ((((ε y)⁻¹ * ε x : (𝓞 E)ˣ) : 𝓞 E) : E) • t) hy', smul_smul, keyE, ← hx']
  obtain ⟨S, hS, hcov⟩ := exists_finset_of_finite_image L f hfin
    (fun y x => ∃ γ ∈ latticeStab h La, γ • y = x) hP
  exact ⟨S, hS.trans fun x hx => hx.1, fun x hx hxs => hcov x ⟨hx, hxs⟩⟩

theorem VectorOrbitsFinite.proof (h : HermitianForm F E W) [FiniteDimensional E W]
    (h₁ : LinePairOrbitsFinite.Statement h) (h₂ : IsotropicScaling.Statement h)
    (h₃ : BoundedIndexSubgroupsFinite.Statement W) (h₅ : LineIndexNeZero.Statement E W) :
    VectorOrbitsFinite.Statement h := by
  classical
  intro D La VV hLa hsub hiso hst ⟨C, hC⟩
  obtain ⟨Sp, hSp, hcov⟩ := h₁ D
  have hline : ∀ x ∈ VV, ∃ p ∈ Sp, ∃ g : h.unitaryGroup, g • p.1 = La ∧
      p.2.map ((g : W ≃ₗ[E] W) : W →ₗ[E] W) = Submodule.span E {x} := by
    intro x hx
    refine hcov La _ hLa ⟨finrank_span_singleton (hiso x hx).1, fun a ha c hc => ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hc
    rw [h.toSesq.map_smulₛₗ a x, LinearMap.smul_apply, map_smul, (hiso x hx).2, smul_zero,
      smul_zero]
  choose! pf hpf gf hgf using hline
  have hfin : (pf '' VV).Finite := hSp.subset (by rintro _ ⟨x, hx, rfl⟩; exact hpf x hx)
  choose! rr hrr1 hrr2 using fun p (hp : p ∈ pf '' VV) => hp
  have hlines : ∀ p ∈ pf '' VV, ∃ S : Finset W, (S : Set W) ⊆ VV ∧ ∀ x ∈ VV,
      x ∈ Submodule.span E {rr p} → ∃ y ∈ S, ∃ γ ∈ latticeStab h La, γ • y = x :=
    fun p hp => line_vectorOrbits h h₂ h₃ h₅ hLa hsub hiso hC (hrr1 p hp)
  choose! Sl hSl1 hSl2 using hlines
  refine ⟨hfin.toFinset.biUnion Sl, ?_, fun x hx => ?_⟩
  · intro y hy
    obtain ⟨p, hp, hyp⟩ := Finset.mem_biUnion.1 hy
    exact hSl1 p (hfin.mem_toFinset.1 hp) hyp
  have hp : pf x ∈ pf '' VV := ⟨x, hx, rfl⟩
  set r := rr (pf x) with hr
  have hr1 : r ∈ VV := hrr1 _ hp
  have hr2 : pf r = pf x := hrr2 _ hp
  set γ₀ := gf r * (gf x)⁻¹ with hγ₀def
  have hγ₀ : γ₀ ∈ latticeStab h La := by
    refine MulAction.mem_stabilizer_iff.2 ?_
    rw [hγ₀def, mul_smul, inv_smul_eq_iff.2 (hgf x hx).1.symm, ← hr2]
    exact (hgf r hr1).1
  have hxm : x ∈ (pf x).2.map ((gf x : W ≃ₗ[E] W) : W →ₗ[E] W) := by
    rw [(hgf x hx).2]
    exact Submodule.mem_span_singleton_self x
  obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.1 hxm
  have hzx' : gf x • z = x := hzx
  have hγ₀x : γ₀ • x ∈ Submodule.span E {r} := by
    rw [hγ₀def, mul_smul, inv_smul_eq_iff.2 hzx'.symm, ← (hgf r hr1).2, hr2]
    exact Submodule.mem_map_of_mem hz
  obtain ⟨y, hy, γ, hγ, hγy⟩ := hSl2 _ hp _ (hst γ₀ hγ₀ x hx) hγ₀x
  refine ⟨y, Finset.mem_biUnion.2 ⟨pf x, hfin.mem_toFinset.2 hp, hy⟩, γ₀⁻¹ * γ,
    mul_mem (inv_mem hγ₀) hγ, ?_⟩
  rw [mul_smul, hγy, inv_smul_smul]

end Spaces

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PAdelicLatticeDictionary
set_option linter.unusedSectionVars false

noncomputable section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module Matrix TensorProduct NumberField IsDedekindDomain GroundTheory.Automorphic
open scoped Pointwise

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

section Span

variable {κ : Type*} [Fintype κ] (b : Basis κ F E) (v : Basis ι E W)

def coordSpan (c : F) : (ι × κ → 𝓞 F) →ₗ[ℤ] W :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun z => ∑ a : ι × κ, (algebraMap F E (c⁻¹ * algebraMap (𝓞 F) F (z a)) * b a.2) • v a.1
      map_zero' := by simp
      map_add' := fun z z' => by
        simp only [Pi.add_apply, map_add (f := _), mul_add, add_mul, add_smul, Finset.sum_add_distrib] }

theorem mem_range_coordSpan {c : F} (hc : c ≠ 0) {x : W}
    (hx : ∀ i k, IsIntegral ℤ (c * b.repr (v.repr x i) k)) :
    x ∈ LinearMap.range (coordSpan b v c) := by
  choose z hz using fun a : ι × κ =>
    (⟨⟨_, hx a.1 a.2⟩, rfl⟩ : ∃ z : 𝓞 F, algebraMap (𝓞 F) F z = c * b.repr (v.repr x a.1) a.2)
  refine ⟨z, ?_⟩
  show ∑ a : ι × κ, (algebraMap F E (c⁻¹ * algebraMap (𝓞 F) F (z a)) * b a.2) • v a.1 = x
  simp only [hz, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [Fintype.sum_prod_type]
  conv_rhs => rw [← v.sum_repr x]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  rw [← Finset.sum_smul]
  congr 1
  conv_rhs => rw [← b.sum_repr (v.repr x i)]
  simp only [Algebra.smul_def]

end Span

theorem isTorsionFree_int_of_module (K' V' : Type*) [Field K'] [CharZero K'] [AddCommGroup V']
    [Module K' V'] : Module.IsTorsionFree ℤ V' :=
  Module.IsTorsionFree.comap (S := K') (fun n : ℤ => (n : K'))
    (fun r hr => isRegular_iff_ne_zero.2 (Int.cast_ne_zero.2 (isRegular_iff_ne_zero.1 hr)))
    (fun r m => Int.cast_smul_eq_zsmul K' r m)

section DIntegral

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ F E) (h : HermitianForm F E W)
  (v : Basis ι E W)

theorem repr_repr_smul_inv_int (d : ℤ) (x : W) (i : ι) (k : κ) :
    b.repr (v.repr ((d : E)⁻¹ • x) i) k = (d : F)⁻¹ * b.repr (v.repr x i) k := by
  have : (d : E)⁻¹ = algebraMap F E (d : F)⁻¹ := by rw [map_inv₀, map_intCast]
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, this, ← Algebra.smul_def, map_smul,
    Finsupp.smul_apply, smul_eq_mul]

theorem repr_repr_nsmul (n : ℕ) (x : W) (i : ι) (k : κ) :
    b.repr (v.repr (n • x) i) k = n * b.repr (v.repr x i) k := by
  rw [map_nsmul, Finsupp.smul_apply, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]

theorem isDIntegral_dictLattice {d : ℤ} (hd0 : d ≠ 0)
    (hd : ∀ (g : unitaryPoints F E (gram h.toSesq v) (FinAdele F)) (x y : ι → F ⊗[F] E),
      x ∈ coreLattice b (gram h.toSesq v) g → y ∈ coreLattice b (gram h.toSesq v) g →
        IsIntegral ℤ ((d : E) * pairE (gram h.toSesq v) x y))
    {m : ℤ} (hm0 : m ≠ 0)
    (hm : ∀ (g : unitaryPoints F E (gram h.toSesq v) (FinAdele F)) (y : ι → F ⊗[F] E),
      (∀ x ∈ coreLattice b (gram h.toSesq v) g, IsIntegral ℤ (pairE (gram h.toSesq v) y x)) →
        (m : F) • y ∈ coreLattice b (gram h.toSesq v) g)
    (g : unitaryPoints F E (gram h.toSesq v) (FinAdele F)) :
    IsDIntegral h ((m * d * d).natAbs ^ finrank ℤ (ι × κ → 𝓞 F)) (dictLattice b h v d g) := by
  classical
  haveI : Module.IsTorsionFree ℤ W := isTorsionFree_int_of_module E W
  have hdE : (d : E) ≠ 0 := by exact_mod_cast hd0
  have hdF : (d : F) ≠ 0 := by exact_mod_cast hd0
  have hsmulL : ∀ (c : E) (x y : W), h.toSesq (c • x) y = conj F E c * h.toSesq x y := by
    intro c x y
    rw [LinearMap.map_smulₛₗ₂, smul_eq_mul]
    rfl
  have hsmulR : ∀ (c : E) (x y : W), h.toSesq x (c • y) = c * h.toSesq x y := by
    intro c x y
    rw [map_smul, smul_eq_mul]
  have hconjd : conj F E (d : E) = d := map_intCast _ _
  have hdI : IsIntegral ℤ (d : E) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := d))

  have hint : ∀ x ∈ dictLattice b h v d g, ∀ y ∈ dictLattice b h v d g, IsIntegral ℤ (h.toSesq x y) := by
    intro x hx y hy
    have e : h.toSesq x y = (d : E) * ((d : E) * pairE (gram h.toSesq v) (coordEquiv F v ((d : E)⁻¹ • x))
        (coordEquiv F v ((d : E)⁻¹ • y))) := by
      rw [pairE_coordEquiv, hsmulL, hsmulR, map_inv₀, hconjd]
      field_simp
    rw [e]
    exact hdI.mul (hd g _ _ hx hy)

  obtain ⟨m', hm'0, hm'⟩ := exists_int_isIntegral_coords b (isUnit_det_gram h v) g
  set c : F := (m' : F) * (d : F)⁻¹ with hcdef
  have hc : c ≠ 0 := mul_ne_zero (by exact_mod_cast hm'0) (inv_ne_zero hdF)
  have hcoordL : ∀ x ∈ dictLattice b h v d g, ∀ i k, IsIntegral ℤ (c * b.repr (v.repr x i) k) := by
    intro x hx i k
    have hx' : coordEquiv F v ((d : E)⁻¹ • x) ∈ coreLattice b (gram h.toSesq v) g := hx
    have := hm' _ (coreLattice_le_adelicLattice b g hx') (i, k)
    rw [vecCoords_coordEquiv, repr_repr_smul_inv_int] at this
    rw [hcdef, mul_assoc]
    exact this
  have hLQ : (dictLattice b h v d g).toIntSubmodule ≤ LinearMap.range (coordSpan b v c) :=
    fun x hx => mem_range_coordSpan b v hc (hcoordL x hx)

  set M : ℤ := m * d * d with hMdef
  have hM0 : M.natAbs ≠ 0 := Int.natAbs_ne_zero.2 (mul_ne_zero (mul_ne_zero hm0 hd0) hd0)
  have hLP : dictLattice b h v d g ≤ dualLattice h (dictLattice b h v d g) := fun x hx y hy => (mem_integralClosure_iff ℤ E).2 (hint x hx y hy)
  have hnL : ∀ y ∈ dualLattice h (dictLattice b h v d g), M.natAbs • y ∈ dictLattice b h v d g := by
    intro y hy
    have h1 : (m : F) • coordEquiv F v ((d : E) • y) ∈ coreLattice b (gram h.toSesq v) g := by
      refine hm g _ fun X hX => ?_
      set x0 := (coordEquiv F v).symm X
      have hx0 : (d : E) • x0 ∈ dictLattice b h v d g := by
        rw [mem_dictLattice, inv_smul_smul₀ hdE, AddEquiv.apply_symm_apply]
        exact hX
      have h2 := (mem_integralClosure_iff ℤ E).1 (hy _ hx0)
      rw [show X = coordEquiv F v x0 from (AddEquiv.apply_symm_apply _ X).symm, pairE_coordEquiv,
        hsmulL, hconjd, ← hsmulR]
      exact h2
    have hMy : M • y ∈ dictLattice b h v d g := by
      rw [mem_dictLattice]
      have e : (d : E)⁻¹ • (M • y) = m • ((d : E) • y) := by
        rw [← Int.cast_smul_eq_zsmul E M, ← Int.cast_smul_eq_zsmul E m, smul_smul, smul_smul, hMdef]
        congr 1
        push_cast
        field_simp
      rw [e, map_zsmul, ← Int.cast_smul_eq_zsmul F]
      exact h1
    have : (M.natAbs : ℤ) • y ∈ dictLattice b h v d g := by
      rcases Int.natAbs_eq M with hM | hM
      · rwa [← hM]
      · rw [show (M.natAbs : ℤ) = -M by omega, neg_smul]
        exact neg_mem hMy
    rwa [natCast_zsmul] at this
  have hcn : c * (M.natAbs : F) ≠ 0 := mul_ne_zero hc (by exact_mod_cast hM0)
  have hPQ : (dualLattice h (dictLattice b h v d g)).toIntSubmodule ≤ LinearMap.range (coordSpan b v (c * M.natAbs)) := by
    intro y hy
    refine mem_range_coordSpan b v hcn fun i k => ?_
    have := hcoordL _ (hnL y hy) i k
    rw [repr_repr_nsmul] at this
    rw [mul_assoc]
    exact this
  obtain ⟨hne, hle⟩ := relIndex_ne_zero_and_le_of_nsmul_mem hLP hPQ hM0 hnL
  refine ⟨⟨fun a x hx => ?_, ?_, ?_⟩, fun x hx y hy => (mem_integralClosure_iff ℤ E).2 (hint x hx y hy),
    hne, hle.trans (Nat.pow_le_pow_right (Nat.pos_of_ne_zero hM0)
      (LinearMap.finrank_range_le (coordSpan b v (c * M.natAbs))))⟩
  ·
    rw [mem_dictLattice, smul_comm, coordEquiv_smul]
    exact smul_mem_coreLattice b hx a
  ·
    haveI : Module.Finite ℤ (dictLattice b h v d g).toIntSubmodule :=
      Module.Finite.of_injective (Submodule.inclusion hLQ) (Submodule.inclusion_injective hLQ)
    have := Module.Finite.iff_fg.1 (inferInstance : Module.Finite ℤ (dictLattice b h v d g).toIntSubmodule)
    exact (Submodule.fg_iff_addSubgroup_fg _).1 this
  ·
    rw [eq_top_iff, ← v.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨n, hn0, hn⟩ := exists_int_smul_single_mem_coreLattice b g i
    have hmem : (d * n) • v i ∈ dictLattice b h v d g := by
      rw [mem_dictLattice]
      have e1 : (d : E)⁻¹ • ((d * n) • v i) = n • v i := by
        rw [← Int.cast_smul_eq_zsmul E (d * n), ← Int.cast_smul_eq_zsmul E n, smul_smul]
        congr 1
        push_cast
        field_simp
      have e2 : coordEquiv F v (v i) = Pi.single i (1 : F ⊗[F] E) := by
        funext j
        rw [coordEquiv_apply, Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
        by_cases hij : i = j
        · subst hij
          simp [Algebra.TensorProduct.one_def]
        · rw [if_neg hij, if_neg (Ne.symm hij), TensorProduct.tmul_zero]
      rw [e1, map_zsmul, e2, ← Int.cast_smul_eq_zsmul F]
      exact hn
    have hvi : v i = ((d * n : ℤ) : E)⁻¹ • ((d * n) • v i) := by
      rw [← Int.cast_smul_eq_zsmul E (d * n), inv_smul_smul₀ (by exact_mod_cast mul_ne_zero hd0 hn0)]
    rw [SetLike.mem_coe, hvi]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end DIntegral

variable [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

theorem AdelicLatticeDictionary.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    AdelicLatticeDictionary.Statement h v := by
  classical
  obtain ⟨d, hd0, hd⟩ := exists_int_isIntegral_pairE (Module.finBasis F E) (gram h.toSesq v)
  obtain ⟨m, hm0, hm⟩ := exists_int_smul_mem_coreLattice_of_dual (Module.finBasis F E)
    (isUnit_det_gram h v)
  exact ⟨coreStabilizer (Module.finBasis F E) (gram h.toSesq v), _,
    dictLattice (Module.finBasis F E) h v d,
    isCompact_coreStabilizer (Module.finBasis F E) _ (isUnit_det_gram h v),
    isOpen_coreStabilizer (Module.finBasis F E) _,
    fun g => isDIntegral_dictLattice (Module.finBasis F E) h v hd0 hd hm0 hm g,
    fun γ g => dictLattice_diagonal_mul d γ g,
    fun g g' => dictLattice_eq_iff hd0⟩

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
end
