module

public import Mathlib
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DetSqEqOneOfPreservesBilin

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StReducedBasisBound
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module MeasureTheory

noncomputable section

def ReducedBasisBound.Statement : Prop :=
  ∀ (d : ℕ) (t c : ℝ), 0 < t → ∃ C : ℝ, ∀ (L : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
    [DiscreteTopology L] [IsZLattice ℝ L], (∀ x ∈ L, x ≠ 0 → t ≤ ‖x‖) →
      ZLattice.covolume L ≤ c → ∃ b : Basis (Fin d) ℤ L, ∀ i, ‖(b i : EuclideanSpace ℝ (Fin d))‖ ≤ C

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsTorusIntegral
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory
open scoped ENNReal

noncomputable section

def TorusIntegralHomogeneous.Statement (κ : Type*) [Fintype κ] : Prop :=
  ∀ q : κ → ℝ, (∀ i, 0 < q i) → ∀ n : ℕ, ∃ C : ℝ≥0∞, 0 < C ∧ C < ⊤ ∧ ∀ t : ℝ, 0 < t →
    ∫⁻ b : κ → ℂ, {b : κ → ℂ | ∑ i, q i * ‖b i‖ ^ 2 < t ^ 2}.indicator
      (fun b => ∏ i, ‖b i‖ₑ ^ (2 * n)) b =
      C * ENNReal.ofReal (t ^ ((2 * n + 2) * Fintype.card κ))

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StIntegralFormCovolume
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module MeasureTheory

noncomputable section

variable (Q V K : Type*) [AddCommGroup Q] [Module ℚ Q] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Fintype K]

def IntegralFormCovolume.Statement : Prop :=
  ∀ (ψ : Q →+ V) (e : Basis K ℚ Q) (T : LinearMap.BilinForm ℚ Q) (μ : Measure V),
    μ.IsAddHaarMeasure → T.Nondegenerate → LinearIndependent ℝ (fun k => ψ (e k)) →
    finrank ℝ V = Fintype.card K →
    ∃ C : ℝ, ∀ (L : AddSubgroup Q) (k : ℤ), k ≠ 0 → L.FG → Submodule.span ℚ (L : Set Q) = ⊤ →
      (∀ x ∈ L, ∀ y ∈ L, ∃ n : ℤ, T x y = n) →
      (∀ y : Q, (∀ x ∈ L, ∃ n : ℤ, T y x = n) → k • y ∈ L) →
      ∃ _ : DiscreteTopology (AddSubgroup.toIntSubmodule (L.map ψ)),
        IsZLattice ℝ (AddSubgroup.toIntSubmodule (L.map ψ)) ∧
        ZLattice.covolume (AddSubgroup.toIntSubmodule (L.map ψ)) μ ^ 2 ≤
          C * |(k : ℝ)| ^ Fintype.card K

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsUnitsInvHaar
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

instance secondCountableTopology_units_complex : SecondCountableTopology ℂˣ :=
  Units.isOpenEmbedding_val.isInducing.secondCountableTopology

instance borelSpace_units_complex : BorelSpace ℂˣ where
  measurable_eq := by
    rw [congrArg (@borel ℂˣ) Units.isOpenEmbedding_val.isInducing.eq_induced, borel_comap,
      ← BorelSpace.measurable_eq (α := ℂ)]
    rfl

def UnitsInvHaar.Statement (I : Type*) [Fintype I] : Prop :=
  ∀ (ρ : Measure (I → ℂˣ)) [ρ.IsHaarMeasure], ∃ c : ℝ≥0, c ≠ 0 ∧
    ∀ (k : ℕ) (g : (I → ℂˣ) → ℝ≥0∞) (g' : (I → ℂ) → ℝ≥0∞), Measurable g →
      (∀ (b : I → ℂ) (hb : ∀ i, b i ≠ 0), g' b = g fun i => (Units.mk0 (b i) (hb i))⁻¹) →
      ∫⁻ a, (∏ i, ‖(a i : ℂ)‖ₑ⁻¹ ^ (2 * (k + 1))) * g a ∂ρ =
        c * ∫⁻ b, (∏ i, ‖b i‖ₑ ^ (2 * k)) * g' b

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsDoubleCoset
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory Topology
open scoped ENNReal

noncomputable section

section Slice

variable {G G₁ G₂ : Type*} [Group G] [Group G₁] [Group G₂] [TopologicalSpace G]
  [TopologicalSpace G₁] [TopologicalSpace G₂]

def sliceGroup (Φ : G ≃ₜ* G₁ × G₂) (Γ : Subgroup G) (K : Subgroup G₂) (s : G₂) : Subgroup G₁ :=
  (Γ ⊓ (Subgroup.prod ⊤ (K.map (MulAut.conj s).toMonoidHom)).comap
      Φ.toMulEquiv.toMonoidHom).map ((MonoidHom.fst G₁ G₂).comp Φ.toMulEquiv.toMonoidHom)

theorem mem_sliceGroup {Φ : G ≃ₜ* G₁ × G₂} {Γ : Subgroup G} {K : Subgroup G₂} {s : G₂} {x : G₁} :
    x ∈ sliceGroup Φ Γ K s ↔ ∃ γ ∈ Γ, s⁻¹ * (Φ γ).2 * s ∈ K ∧ (Φ γ).1 = x := by
  simp only [sliceGroup, Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_comap,
    Subgroup.mem_prod, Subgroup.mem_top, true_and, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.coe_fst]
  constructor
  · rintro ⟨γ, ⟨hγ, k, hk, hks⟩, rfl⟩
    refine ⟨γ, hγ, ?_, rfl⟩
    have : (Φ γ).2 = s * k * s⁻¹ := by
      have := hks.symm
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply] at this
      exact this
    rw [this]
    simpa [mul_assoc] using hk
  · rintro ⟨γ, hγ, hk, rfl⟩
    refine ⟨γ, ⟨hγ, s⁻¹ * (Φ γ).2 * s, hk, ?_⟩, rfl⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, mul_assoc,
      mul_inv_cancel, mul_one, mul_inv_cancel_left]
    rfl

end Slice

def DoubleCosetCovolume.Statement (G G₁ G₂ : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [Group G₁] [TopologicalSpace G₁]
    [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [T2Space G₁] [SecondCountableTopology G₁]
    [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] :
    Prop :=
  ∀ (Φ : G ≃ₜ* G₁ × G₂) (Γ : Subgroup G) [Countable Γ] (K : Subgroup G₂) (S : Finset G₂),
    IsCompact (K : Set G₂) → IsOpen (K : Set G₂) →
    (∀ γ ∈ Γ, (Φ γ).1 = 1 → γ = 1) →
    (∀ y : G₂, ∃ γ ∈ Γ, ∃ s ∈ S, ∃ k ∈ K, y = (Φ γ).2 * s * k) →
    (∀ s ∈ S, ∀ (μ₁ : Measure G₁) [μ₁.IsHaarMeasure], ∃ FD₁ : Set G₁,
      IsFundamentalDomain (sliceGroup Φ Γ K s) FD₁ μ₁ ∧ μ₁ FD₁ < ⊤) →
    ∀ (μ : Measure G) [μ.IsHaarMeasure], ∃ FD : Set G, IsFundamentalDomain Γ FD μ ∧ μ FD < ⊤

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusHaar
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory Module

theorem det_sq_eq_one_of_preserves_bilin {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (f : V →ₗ[ℝ] V) (hf : ∀ x y, B (f x) (f y) = B x y) : LinearMap.det f ^ 2 = 1 :=
  _root_.UpperTheory.Reformulated.B.Qm9.det_sq_eq_one_of_preserves_bilin B hB f hf

theorem measurePreserving_of_preserves_bilin {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] (μ : Measure V)
    [μ.IsAddHaarMeasure] (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (f : V →ₗ[ℝ] V) (hf : ∀ x y, B (f x) (f y) = B x y) : MeasurePreserving f μ μ := by
  have h2 := det_sq_eq_one_of_preserves_bilin B hB f hf
  have hd : LinearMap.det f ≠ 0 := by
    intro h
    rw [h] at h2
    norm_num at h2
  have habs : |LinearMap.det f| = 1 := by
    have : |LinearMap.det f| ^ 2 = 1 := by rw [sq_abs]; exact h2
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) two_ne_zero).1 this
  refine ⟨(LinearMap.continuous_of_finiteDimensional f).measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ hd, abs_inv, habs]
  simp

theorem map_eq_of_measurePreserving_coordinates {N V : Type*} [Group N] [TopologicalSpace N]
    [IsTopologicalGroup N] [LocallyCompactSpace N] [SecondCountableTopology N] [MeasurableSpace N]
    [BorelSpace N] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] (lam : Measure V)
    [IsFiniteMeasureOnCompacts lam] [lam.IsOpenPosMeasure] (φ : V ≃ₜ N)
    (hL : ∀ n : N, MeasurePreserving (fun x => φ.symm (n * φ x)) lam lam)
    (c : N → N) (hC : MeasurePreserving (fun x => φ.symm (c (φ x))) lam lam)
    (μ : Measure N) [μ.IsHaarMeasure] : μ.map c = μ := by
  have hφ : Measurable φ := φ.continuous.measurable
  have key : ∀ T : V → V, MeasurePreserving T lam lam →
      (lam.map φ).map (φ ∘ T ∘ φ.symm) = lam.map φ := by
    intro T hT
    rw [Measure.map_map (hφ.comp (hT.measurable.comp φ.symm.continuous.measurable)) hφ]
    have : (φ ∘ T ∘ φ.symm) ∘ φ = φ ∘ T := by
      funext x
      simp
    rw [this, ← Measure.map_map hφ hT.measurable, hT.map_eq]
  have hinv : (lam.map φ).IsMulLeftInvariant := by
    refine ⟨fun n => ?_⟩
    have e : (fun x => n * x) = φ ∘ (fun x => φ.symm (n * φ x)) ∘ φ.symm := by
      funext x
      simp
    rw [e]
    exact key _ (hL n)
  have : IsFiniteMeasureOnCompacts (lam.map φ) := by
    refine ⟨fun K hK => ?_⟩
    have e := φ.toMeasurableEquiv.map_apply (μ := lam) K
    simp only [Homeomorph.toMeasurableEquiv_coe] at e
    rw [e]
    exact (φ.isCompact_preimage.2 hK).measure_lt_top
  have : (lam.map φ).IsOpenPosMeasure := φ.continuous.isOpenPosMeasure_map φ.surjective
  have : (lam.map φ).IsHaarMeasure := {}
  have e : c = φ ∘ (fun x => φ.symm (c (φ x))) ∘ φ.symm := by
    funext x
    simp
  have hc : AEMeasurable c (lam.map φ) := by
    rw [φ.measurableEmbedding.aemeasurable_map_iff]
    simpa only [Function.comp_def, Homeomorph.apply_symm_apply] using
      (hφ.comp hC.measurable).aemeasurable (μ := lam)
  rw [Measure.isMulLeftInvariant_eq_smul μ (lam.map φ), Measure.map_smul _ hc]
  congr 1
  rw [e]
  exact key _ hC

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Matrix

noncomputable section

variable {ι : Type*} [Fintype ι]

def hForm (H : Matrix ι ι ℂ) (u z : ι → ℂ) : ℂ := star u ⬝ᵥ (H *ᵥ z)

section Form

variable (H : Matrix ι ι ℂ)

theorem hForm_add_left (u u' z : ι → ℂ) : hForm H (u + u') z = hForm H u z + hForm H u' z := by
  simp [hForm, star_add, add_dotProduct]

theorem hForm_add_right (u z z' : ι → ℂ) : hForm H u (z + z') = hForm H u z + hForm H u z' := by
  simp [hForm, mulVec_add, dotProduct_add]

theorem hForm_sub_left (u u' z : ι → ℂ) : hForm H (u - u') z = hForm H u z - hForm H u' z := by
  simp [hForm, star_sub, sub_dotProduct]

theorem hForm_sub_right (u z z' : ι → ℂ) : hForm H u (z - z') = hForm H u z - hForm H u z' := by
  simp [hForm, mulVec_sub, dotProduct_sub]

theorem hForm_neg_left (u z : ι → ℂ) : hForm H (-u) z = -hForm H u z := by
  simp [hForm, star_neg, neg_dotProduct]

theorem hForm_neg_right (u z : ι → ℂ) : hForm H u (-z) = -hForm H u z := by
  simp [hForm, mulVec_neg, dotProduct_neg]

theorem hForm_smul_left (c : ℂ) (u z : ι → ℂ) :
    hForm H (c • u) z = starRingEnd ℂ c * hForm H u z := by
  simp [hForm, star_smul, smul_dotProduct]

theorem hForm_smul_right (c : ℂ) (u z : ι → ℂ) : hForm H u (c • z) = c * hForm H u z := by
  simp [hForm, mulVec_smul, dotProduct_smul]

theorem hForm_zero_left (z : ι → ℂ) : hForm H 0 z = 0 := by simp [hForm]

theorem hForm_zero_right (u : ι → ℂ) : hForm H u 0 = 0 := by simp [hForm]

theorem hForm_conj {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (u z : ι → ℂ) :
    starRingEnd ℂ (hForm H u z) = hForm H z u := by
  simp only [hForm]
  conv_rhs => rw [star_dotProduct, star_mulVec, hH.eq, ← dotProduct_mulVec]
  rfl

theorem hForm_self_im {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (u : ι → ℂ) :
    (hForm H u u).im = 0 :=
  Complex.conj_eq_iff_im.1 (hForm_conj hH u u)

theorem hForm_mulVec (M : Matrix ι ι ℂ) (u z : ι → ℂ) :
    hForm H (M *ᵥ u) (M *ᵥ z) = hForm (Mᴴ * H * M) u z := by
  simp only [hForm]
  rw [star_mulVec, mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mul_assoc]

theorem hForm_mulVec_of_unitary {M : Matrix ι ι ℂ} (hM : Mᴴ * H * M = H) (u z : ι → ℂ) :
    hForm H (M *ᵥ u) (M *ᵥ z) = hForm H u z := by
  rw [hForm_mulVec, hM]

variable [DecidableEq ι]

theorem hForm_single (X : Matrix ι ι ℂ) (i j : ι) :
    hForm X (Pi.single i 1) (Pi.single j 1) = X i j := by
  simp [hForm]

theorem unitary_of_hForm {M : Matrix ι ι ℂ}
    (hM : ∀ u z, hForm H (M *ᵥ u) (M *ᵥ z) = hForm H u z) : Mᴴ * H * M = H := by
  ext i j
  have := hM (Pi.single i 1) (Pi.single j 1)
  rw [hForm_mulVec, hForm_single, hForm_single] at this
  exact this

theorem eq_zero_of_hForm {H : Matrix ι ι ℂ} (hd : IsUnit H.det) {u : ι → ℂ}
    (hu : ∀ z, hForm H u z = 0) : u = 0 := by
  have h1 : star u ᵥ* H = 0 := by
    ext j
    have := hu (Pi.single j 1)
    rw [hForm, dotProduct_mulVec, dotProduct_single_one] at this
    exact this
  have h2 : star u = 0 := by
    have := congrArg (fun r => r ᵥ* H⁻¹) h1
    simpa [vecMul_vecMul, mul_nonsing_inv H hd] using this
  simpa using congrArg star h2

theorem matrix_ext_mulVec {A B : Matrix ι ι ℂ} (h : ∀ z, A *ᵥ z = B *ᵥ z) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [mulVec_single_one] using this

end Form

def heisS (H : Matrix ι ι ℂ) (y : ι → ℂ) (t : ℝ) : ℂ :=
  ⟨-(hForm H y y).re / 2, t⟩

section S

variable {H : Matrix ι ι ℂ}

theorem heisS_im (y : ι → ℂ) (t : ℝ) : (heisS H y t).im = t := rfl

theorem heisS_spec (hH : H.IsHermitian) (y : ι → ℂ) (t : ℝ) :
    heisS H y t + starRingEnd ℂ (heisS H y t) + hForm H y y = 0 := by
  apply Complex.ext
  · simp only [heisS, Complex.add_re, Complex.conj_re, Complex.zero_re]
    ring
  · simp only [heisS, Complex.add_im, Complex.conj_im, Complex.zero_im, hForm_self_im hH]
    ring

theorem eq_heisS {y : ι → ℂ} {s : ℂ} (hs : s + starRingEnd ℂ s + hForm H y y = 0) :
    s = heisS H y s.im := by
  apply Complex.ext
  · have := congrArg Complex.re hs
    simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at this
    simp only [heisS]
    linarith
  · rfl

end S

variable [DecidableEq ι]

def heisMat (H : Matrix ι ι ℂ) (a y : ι → ℂ) (s : ℂ) : Matrix ι ι ℂ :=
  1 + vecMulVec (y + s • a) (star a ᵥ* H) - vecMulVec a (star y ᵥ* H)

section Heis

variable {H : Matrix ι ι ℂ} {a : ι → ℂ}

theorem heisMat_mulVec (y : ι → ℂ) (s : ℂ) (z : ι → ℂ) :
    heisMat H a y s *ᵥ z = z + hForm H a z • (y + s • a) - hForm H y z • a := by
  simp [heisMat, sub_mulVec, add_mulVec, vecMulVec_mulVec, hForm, dotProduct_mulVec]

theorem heisMat_zero : heisMat H a 0 0 = 1 := by
  simp [heisMat]

variable (hH : H.IsHermitian) (ha : hForm H a a = 0)
include hH ha

theorem heisMat_mulVec_self {y : ι → ℂ} (hy : hForm H a y = 0) (s : ℂ) :
    heisMat H a y s *ᵥ a = a := by
  have hya : hForm H y a = 0 := by rw [← hForm_conj hH, hy, map_zero]
  rw [heisMat_mulVec, ha, hya]
  simp

theorem heisMat_mul {y₁ y₂ : ι → ℂ} (h₁ : hForm H a y₁ = 0) (h₂ : hForm H a y₂ = 0)
    (s₁ s₂ : ℂ) :
    heisMat H a y₁ s₁ * heisMat H a y₂ s₂ =
      heisMat H a (y₁ + y₂) (s₁ + s₂ - hForm H y₁ y₂) := by
  have hya : hForm H y₁ a = 0 := by rw [← hForm_conj hH, h₁, map_zero]
  refine matrix_ext_mulVec fun z => ?_
  rw [← mulVec_mulVec, heisMat_mulVec, heisMat_mulVec, heisMat_mulVec]
  simp only [hForm_add_right, hForm_sub_right, hForm_smul_right, hForm_add_left, ha, h₂, hya]
  module

theorem heisMat_unitary {y : ι → ℂ} (hy : hForm H a y = 0) {s : ℂ}
    (hs : s + starRingEnd ℂ s + hForm H y y = 0) :
    (heisMat H a y s)ᴴ * H * heisMat H a y s = H := by
  have hya : hForm H y a = 0 := by rw [← hForm_conj hH, hy, map_zero]
  refine unitary_of_hForm H fun p q => ?_
  rw [heisMat_mulVec, heisMat_mulVec]
  simp only [hForm_add_right, hForm_sub_right, hForm_smul_right, hForm_add_left, hForm_sub_left,
    hForm_smul_left, ha, hy, hya, hForm_conj hH]
  linear_combination (hForm H a q * hForm H p a) * hs


omit hH ha in
theorem heisMat_conj {g : Matrix ι ι ℂ} (hg : gᴴ * H * g = H) (hga : g *ᵥ a = a) (y : ι → ℂ)
    (s : ℂ) : g * heisMat H a y s = heisMat H a (g *ᵥ y) s * g := by
  refine matrix_ext_mulVec fun z => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, heisMat_mulVec, heisMat_mulVec]
  conv_rhs => rw [← hga, hForm_mulVec_of_unitary H hg, hForm_mulVec_of_unitary H hg, hga]
  simp only [mulVec_add, mulVec_sub, mulVec_smul, hga]


omit ha in
theorem eq_of_mulVec_partner {b : ι → ℂ} (hab : hForm H a b = 1) {n m : Matrix ι ι ℂ}
    (hn : nᴴ * H * n = H) (hm : mᴴ * H * m = H)
    (hna : n *ᵥ a = a)
    (hn' : ∀ z, hForm H a z = 0 → ∃ c : ℂ, n *ᵥ z = z + c • a)
    (hm' : ∀ z, hForm H a z = 0 → ∃ c : ℂ, m *ᵥ z = z + c • a) (hnb : n *ᵥ b = m *ᵥ b) :
    n = m := by
  have hba : hForm H b a = 1 := by rw [← hForm_conj hH, hab, map_one]
  have hnba : hForm H (n *ᵥ b) a = 1 := by
    conv_lhs => rw [← hna]
    rw [hForm_mulVec_of_unitary H hn, hba]
  refine matrix_ext_mulVec fun p => ?_
  set p' := p - hForm H a p • b with hp'
  have hap' : hForm H a p' = 0 := by
    rw [hp', hForm_sub_right, hForm_smul_right, hab, mul_one, sub_self]
  have hp : p = p' + hForm H a p • b := by rw [hp']; abel
  obtain ⟨c, hc⟩ := hn' p' hap'
  obtain ⟨d, hd⟩ := hm' p' hap'
  have e1 := hForm_mulVec_of_unitary H hn b p'
  have e2 := hForm_mulVec_of_unitary H hm b p'
  rw [hc] at e1
  rw [hd, ← hnb] at e2
  rw [hForm_add_right, hForm_smul_right, hnba] at e1 e2
  have hcd : c = d := by linear_combination e1 - e2
  rw [hp, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, hc, hd, hcd, hnb]

theorem eq_heisMat {b : ι → ℂ} (hb : hForm H b b = 0) (hab : hForm H a b = 1)
    {n : Matrix ι ι ℂ} (hn : nᴴ * H * n = H) (hna : n *ᵥ a = a)
    (hn' : ∀ z, hForm H a z = 0 → ∃ c : ℂ, n *ᵥ z = z + c • a) :
    hForm H a (n *ᵥ b - b - hForm H b (n *ᵥ b - b) • a) = 0 ∧
    hForm H b (n *ᵥ b - b - hForm H b (n *ᵥ b - b) • a) = 0 ∧
    hForm H b (n *ᵥ b - b) + starRingEnd ℂ (hForm H b (n *ᵥ b - b)) +
      hForm H (n *ᵥ b - b - hForm H b (n *ᵥ b - b) • a)
        (n *ᵥ b - b - hForm H b (n *ᵥ b - b) • a) = 0 ∧
    n = heisMat H a (n *ᵥ b - b - hForm H b (n *ᵥ b - b) • a) (hForm H b (n *ᵥ b - b)) := by
  have hba : hForm H b a = 1 := by rw [← hForm_conj hH, hab, map_one]
  set u := n *ᵥ b - b with hu
  set s := hForm H b u with hs
  set y := u - s • a with hy
  have hanb : hForm H a (n *ᵥ b) = 1 := by
    conv_lhs => rw [← hna]
    rw [hForm_mulVec_of_unitary H hn, hab]
  have hau : hForm H a u = 0 := by rw [hu, hForm_sub_right, hanb, hab, sub_self]
  have h1 : hForm H a y = 0 := by rw [hy, hForm_sub_right, hForm_smul_right, hau, ha]; ring
  have h2 : hForm H b y = 0 := by rw [hy, hForm_sub_right, hForm_smul_right, hba, ← hs]; ring
  have hya : hForm H y a = 0 := by rw [← hForm_conj hH, h1, map_zero]
  have hbb := hForm_mulVec_of_unitary H hn b b
  have hnb : n *ᵥ b = b + u := by rw [hu]; abel
  rw [hnb, hb] at hbb
  have hub : hForm H u b = starRingEnd ℂ s := by rw [hs, hForm_conj hH]
  have huu : hForm H u u = hForm H y y := by
    have : u = y + s • a := by rw [hy]; abel
    rw [this]
    simp only [hForm_add_right, hForm_add_left, hForm_smul_right, hForm_smul_left, h1, hya, ha]
    ring
  have h3 : s + starRingEnd ℂ s + hForm H y y = 0 := by
    simp only [hForm_add_right, hForm_add_left, hb, hub, ← hs, huu] at hbb
    linear_combination hbb
  refine ⟨h1, h2, h3, ?_⟩
  refine eq_of_mulVec_partner hH hab hn (heisMat_unitary hH ha h1 h3) hna hn' ?_ ?_
  · intro z hz
    refine ⟨-hForm H y z, ?_⟩
    rw [heisMat_mulVec, hz]
    simp only [zero_smul, add_zero, neg_smul, sub_eq_add_neg]
  · have hyb : hForm H y b = 0 := by rw [← hForm_conj hH, h2, map_zero]
    rw [heisMat_mulVec, hab, hyb, hnb, hy]
    simp only [one_smul, zero_smul, sub_zero, sub_add_cancel]

end Heis

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
