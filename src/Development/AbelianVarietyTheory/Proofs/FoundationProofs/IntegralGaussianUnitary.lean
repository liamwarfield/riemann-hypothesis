module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOrthonormalBasisEigenOfInnerMap
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOrthonormalEigenbasis
open Module.End

namespace GlobalTheory.OrthonormalEigenbasis

theorem exists_eigenbasis_of_isometry {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (a : E →ₗ[ℂ] E) (ha : ∀ x y, inner ℂ (a x) (a y) = inner ℂ x y) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E) (l : Fin (Module.finrank ℂ E) → ℂ),
      ∀ i, a (b i) = l i • b i := by
  set a' := LinearMap.adjoint a with ha'

  have h1 : a' * a = 1 := by
    ext x
    apply ext_inner_right ℂ
    intro y
    rw [Module.End.mul_apply, ha', LinearMap.adjoint_inner_left, ha, Module.End.one_apply]
  have h2 : a * a' = 1 := mul_eq_one_comm.mp h1

  set A : E →ₗ[ℂ] E := a + a' with hAdef
  set B : E →ₗ[ℂ] E := Complex.I • (a' - a) with hBdef
  have hA : A.IsSymmetric := by
    intro x y
    simp only [hAdef, LinearMap.add_apply, inner_add_left, inner_add_right, ha',
      LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]
    ring
  have hB : B.IsSymmetric := by
    intro x y
    simp only [hBdef, LinearMap.smul_apply, LinearMap.sub_apply, inner_smul_left, inner_smul_right,
      inner_sub_left, inner_sub_right, ha', LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right,
      Complex.conj_I]
    ring
  have hAB : Commute A B := by
    have hc : Commute (a + a') (a' - a) := by
      show (a + a') * (a' - a) = (a' - a) * (a + a')
      simp only [add_mul, mul_add, sub_mul, mul_sub, h1, h2]
      abel
    exact hc.smul_right Complex.I
  have hV := LinearMap.IsSymmetric.directSum_isInternal_of_commute hA hB hAB
  have hV' := LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace hA hB

  have hT : Set.Finite {i : ℂ × ℂ | eigenspace A i.2 ⊓ eigenspace B i.1 ≠ ⊥} := by
    refine ((Module.End.finite_hasEigenvalue (f := B)).prod
      (Module.End.finite_hasEigenvalue (f := A))).subset fun i hi => ⟨?_, ?_⟩
    · exact Module.End.hasEigenvalue_iff.mpr (ne_bot_of_le_ne_bot hi inf_le_right)
    · exact Module.End.hasEigenvalue_iff.mpr (ne_bot_of_le_ne_bot hi inf_le_left)
  have : Finite {i : ℂ × ℂ // eigenspace A i.2 ⊓ eigenspace B i.1 ≠ ⊥} := hT.to_subtype
  have := Fintype.ofFinite {i : ℂ × ℂ // eigenspace A i.2 ⊓ eigenspace B i.1 ≠ ⊥}
  classical
  have hW := DirectSum.isInternal_ne_bot_iff.mpr hV
  have hW' := hV'.comp (Subtype.val_injective (p := fun i : ℂ × ℂ => eigenspace A i.2 ⊓ eigenspace B i.1 ≠ ⊥))

  refine ⟨hW.subordinateOrthonormalBasis rfl hW', fun i =>
    ((hW.subordinateOrthonormalBasisIndex rfl i hW').1.2 +
      Complex.I * (hW.subordinateOrthonormalBasisIndex rfl i hW').1.1) / 2, fun i => ?_⟩
  have hmem := hW.subordinateOrthonormalBasis_subordinate rfl i hW'
  rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff] at hmem
  have hsum : ∀ v, A v + Complex.I • B v = (2 : ℂ) • a v := by
    intro v
    simp only [hAdef, hBdef, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, smul_smul,
      Complex.I_mul_I, neg_one_smul, smul_sub, two_smul]
    abel
  calc a (hW.subordinateOrthonormalBasis rfl hW' i)
      = (2 : ℂ)⁻¹ • (A (hW.subordinateOrthonormalBasis rfl hW' i) +
          Complex.I • B (hW.subordinateOrthonormalBasis rfl hW' i)) := by
        rw [hsum, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
    _ = _ := by
        rw [hmem.1, hmem.2, smul_smul, ← add_smul, smul_smul]
        congr 1
        ring


open GlobalTheory.UnitaryTheta in
theorem exists_orthonormal_eigenbasis {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Sesq V) (hH : IsPosHerm H) (a : V →ₗ[ℂ] V) (ha : ∀ z w, H (a z) (a w) = H z w) :
    ∃ (n : ℕ) (e : Module.Basis (Fin n) ℂ V) (l : Fin n → ℂ),
      (∀ i j, H (e i) (e j) = if i = j then (1 : ℂ) else 0) ∧ ∀ i, ‖l i‖ = 1 ∧ a (e i) = l i • e i := by

  let cd : InnerProductSpace.Core ℂ V :=
    { inner := fun x y => H y x
      conj_inner_symm := fun x y => (hH.1 y x).symm
      re_inner_nonneg := fun x => by
        by_cases hx : x = 0
        · simp [hx]
        · exact (hH.2 x hx).le
      add_left := fun x y z => by
        show H z (x + y) = H z x + H z y
        exact map_add _ _ _
      smul_left := fun x y r => by
        show H y (r • x) = (starRingEnd ℂ) r * H y x
        rw [LinearMap.map_smulₛₗ, smul_eq_mul]
      definite := fun x hx => by
        by_contra h
        have := hH.2 x h
        simp [hx] at this }
  let _ : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore cd.toCore
  have hinner : ∀ x y : V, inner ℂ x y = H y x := fun _ _ => rfl
  obtain ⟨b, l, hb⟩ := exists_eigenbasis_of_isometry a (fun x y => by rw [hinner, hinner]; exact ha y x)
  refine ⟨Module.finrank ℂ V, b.toBasis, l, fun i j => ?_, fun i => ⟨?_, ?_⟩⟩
  · rw [OrthonormalBasis.coe_toBasis, ← hinner, orthonormal_iff_ite.mp b.orthonormal j i]
    exact if_congr eq_comm rfl rfl
  ·
    have h1 : ‖a (b i)‖ = ‖b i‖ := by
      rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), hinner, hinner, ha]
    rw [hb i, norm_smul, b.orthonormal.1 i, mul_one] at h1
    exact h1
  · rw [OrthonormalBasis.coe_toBasis]
    exact hb i

end GlobalTheory.OrthonormalEigenbasis
end

open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

noncomputable section

namespace GlobalTheory.UnitaryTheta

theorem exists_eigenbasis_of_isPosHerm {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Sesq V) (hH : IsPosHerm H) (a : V →ₗ[ℂ] V) (ha : ∀ z w, H (a z) (a w) = H z w) :
    ∃ (n : ℕ) (e : Module.Basis (Fin n) ℂ V) (l : Fin n → ℂ),
      (∀ i j, H (e i) (e j) = if i = j then 1 else 0) ∧ ∀ i, ‖l i‖ = 1 ∧ a (e i) = l i • e i := by
  first
  | exact @_root_.GlobalTheory.OrthonormalEigenbasis.exists_orthonormal_eigenbasis
  | exact _root_.GlobalTheory.OrthonormalEigenbasis.exists_orthonormal_eigenbasis
  | (apply _root_.GlobalTheory.OrthonormalEigenbasis.exists_orthonormal_eigenbasis <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrthonormalEigenbasis.exists_orthonormal_eigenbasis <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrthonormalEigenbasis.exists_orthonormal_eigenbasis <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrthonormalEigenbasis.exists_orthonormal_eigenbasis ..)

theorem unitary_exists_orthonormal_eigenbasis :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsPosHerm H →
      ∀ a : V ≃ₗ[ℂ] V, (∀ z w, H (a z) (a w) = H z w) →
        ∃ (n : ℕ) (e : Module.Basis (Fin n) ℂ V) (l : Fin n → ℂ),
          (∀ i j, H (e i) (e j) = if i = j then 1 else 0) ∧ ∀ i, ‖l i‖ = 1 ∧ a (e i) = l i • e i :=
  fun _ _ _ _ H hH a ha => exists_eigenbasis_of_isPosHerm H hH a.toLinearMap ha

end GlobalTheory.UnitaryTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralCexpGaussianPlane
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralCexpGaussianPlane
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta

theorem integral_cexp_gaussian_plane : ∀ l u v : ℂ, 0 < l.re → Integrable (fun z : ℂ => cexp (-(π : ℂ) * l * (z * conj z) + π * (u * conj z) + π * (z * conj v))) ∧ ∫ z : ℂ, cexp (-(π : ℂ) * l * (z * conj z) + π * (u * conj z) + π * (z * conj v)) = l⁻¹ * cexp (π * (u * conj v) / l) := by
  intro l u v hl
  have hl0 : l ≠ 0 := by
    intro h
    simp [h] at hl
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hb : (-(π : ℂ) * l).re < 0 := by
    have := mul_pos Real.pi_pos hl
    simpa using this
  set f : ℝ → ℂ := fun x => cexp ((-(π : ℂ) * l) * x ^ 2 + (π * (u + conj v)) * x + 0) with hf
  set g : ℝ → ℂ := fun y => cexp ((-(π : ℂ) * l) * y ^ 2 + (π * I * (conj v - u)) * y + 0) with hg
  have hfi : Integrable f := integrable_cexp_quadratic' hb _ _
  have hgi : Integrable g := integrable_cexp_quadratic' hb _ _
  have key : (fun z : ℂ => cexp (-(π : ℂ) * l * (z * conj z) + π * (u * conj z) + π * (z * conj v)))
      = (fun p : ℝ × ℝ => f p.1 * g p.2) ∘ Complex.measurableEquivRealProd := by
    funext z
    simp only [hf, hg, Function.comp, Complex.measurableEquivRealProd_apply, ← Complex.exp_add]
    congr 1
    have hz : z = z.re + z.im * I := (Complex.re_add_im z).symm
    have hc : conj z = z.re - z.im * I := by
      apply Complex.ext <;> simp
    rw [hc]
    generalize (z.re : ℂ) = a at hz ⊢
    generalize (z.im : ℂ) = b at hz ⊢
    subst hz
    linear_combination (π * l * b ^ 2) * Complex.I_sq
  have hmp := Complex.volume_preserving_equiv_real_prod
  refine ⟨?_, ?_⟩
  · rw [key, hmp.integrable_comp_emb Complex.measurableEquivRealProd.measurableEmbedding]
    exact hfi.mul_prod hgi
  · rw [key]
    have h1 := hmp.integral_comp' (fun p : ℝ × ℝ => f p.1 * g p.2)
    simp only [Function.comp_def]
    rw [h1, Measure.volume_eq_prod, integral_prod_mul, hf, hg, integral_cexp_quadratic hb,
      integral_cexp_quadratic hb]
    have h2 : (π : ℂ) / -(-(π : ℂ) * l) = l⁻¹ := by field_simp
    have h3 : (l⁻¹ : ℂ) ^ (1 / 2 : ℂ) * (l⁻¹ : ℂ) ^ (1 / 2 : ℂ) = l⁻¹ := by
      rw [← Complex.cpow_add _ _ (inv_ne_zero hl0)]
      norm_num
    rw [h2, mul_mul_mul_comm, h3, ← Complex.exp_add]
    congr 2
    field_simp
    linear_combination (π * (conj v - u) ^ 2) * Complex.I_sq

end GlobalTheory.UnitaryTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralCexpGaussianPlaneStatement
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_cexp_complex_gaussian_linear : ∀ l u v : ℂ, 0 < l.re → Integrable (fun z : ℂ => cexp (-(π : ℂ) * l * (z * conj z) + π * (u * conj z) + π * (z * conj v))) ∧ ∫ z : ℂ, cexp (-(π : ℂ) * l * (z * conj z) + π * (u * conj z) + π * (z * conj v)) = l⁻¹ * cexp (π * (u * conj v) / l) := by
  first | exact @GlobalTheory.UnitaryTheta.integral_cexp_gaussian_plane | exact GlobalTheory.UnitaryTheta.integral_cexp_gaussian_plane | (intros; apply GlobalTheory.UnitaryTheta.integral_cexp_gaussian_plane <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralGaussianUnitary
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta

theorem sesq_eq_sum_repr {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) {n : ℕ}
    (e : Module.Basis (Fin n) ℂ V) (he : ∀ i j, H (e i) (e j) = if i = j then 1 else 0) (z w : V) :
    H z w = ∑ i, e.repr z i * conj (e.repr w i) := by
  conv_lhs => rw [← e.sum_repr z, ← e.sum_repr w]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, he,
    smul_eq_mul, RingHom.id_apply, mul_ite, mul_one, mul_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

theorem repr_apply_of_eigen {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (e : Module.Basis (Fin n) ℂ V) (b : V →ₗ[ℂ] V) (l : Fin n → ℂ) (hl : ∀ i, b (e i) = l i • e i) (z : V)
    (i : Fin n) : e.repr (b z) i = l i * e.repr z i := by
  conv_lhs => rw [← e.sum_repr z]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, hl]
  simp [Finsupp.single_apply, mul_comm]

theorem det_of_eigen {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (e : Module.Basis (Fin n) ℂ V) (b : V →ₗ[ℂ] V) (l : Fin n → ℂ) (hl : ∀ i, b (e i) = l i • e i) :
    LinearMap.det b = ∏ i, l i := by
  rw [← LinearMap.det_toMatrix e, ← Matrix.det_diagonal]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, hl]
  simp [Matrix.diagonal_apply, Finsupp.single_apply]
  split_ifs with h1 h2 h2 <;> simp_all

theorem integral_gaussian_unitary : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ a : V ≃ₗ[ℂ] V, (∀ z w, H (a z) (a w) = H z w) → LinearMap.det (1 - (a : V →ₗ[ℂ] V)) ≠ 0 → ∃ κ : ℝ, κ ≠ 0 ∧ ∀ y v : V, Integrable (fun z => cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v)) μ ∧ ∫ z, cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v) ∂μ = κ / LinearMap.det (1 - (a : V →ₗ[ℂ] V)) * cexp (π * H y v) := by
  intro V _ _ _ _ _ μ _ H hH a ha hdet
  obtain ⟨n, e, l, he, hl⟩ := GlobalTheory.UnitaryTheta.unitary_exists_orthonormal_eigenbasis V H hH a ha
  have hb : ∀ i, (1 - (a : V →ₗ[ℂ] V)) (e i) = (1 - l i) • e i := fun i => by
    simp [(hl i).2, sub_smul]
  have hd := det_of_eigen e _ _ hb
  have hr : ∀ z i, e.repr (z - a z) i = (1 - l i) * e.repr z i := fun z i => by
    simpa using repr_apply_of_eigen e _ _ hb z i
  have hne : ∀ i, 1 - l i ≠ 0 := fun i => by
    rw [hd] at hdet
    exact Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ _)
  have hre : ∀ i, 0 < (1 - l i).re := fun i => by
    have h1 : (l i).re ≤ 1 := (hl i).1 ▸ re_le_norm (l i)
    have h2 : (l i).re ≠ 1 := by
      intro h
      apply hne i
      have h3 : (l i).re * (l i).re + (l i).im * (l i).im = 1 := by
        rw [← normSq_apply, normSq_eq_norm_sq, (hl i).1]; norm_num
      have h4 : (l i).im = 0 := by
        rw [h] at h3
        exact mul_self_eq_zero.1 (by linarith)
      apply Complex.ext <;> simp [h, h4]
    simp only [sub_re, one_re]
    exact sub_pos.2 (lt_of_le_of_ne h1 h2)
  let T : V ≃L[ℂ] (Fin n → ℂ) := e.equivFun.toContinuousLinearEquiv
  let Tm : V ≃ᵐ (Fin n → ℂ) := T.toHomeomorph.toMeasurableEquiv
  have hT : ∀ z i, Tm z i = e.repr z i := fun z i => rfl
  haveI : (μ.map Tm).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  have hν := Measure.isAddLeftInvariant_eq_smul (μ.map Tm) (volume : Measure (Fin n → ℂ))
  have hpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map Tm) (volume : Measure (Fin n → ℂ))
  set c := Measure.addHaarScalarFactor (μ.map Tm) (volume : Measure (Fin n → ℂ)) with hc
  refine ⟨(c : ℝ), by exact_mod_cast hpos.ne', fun y v => ?_⟩
  let g : Fin n → ℂ → ℂ := fun i z => cexp (-(π : ℂ) * (1 - l i) * (z * conj z) +
    π * (((1 - l i) * e.repr y i) * conj z) + π * (z * conj (e.repr v i)))
  have hg := fun i => GlobalTheory.T.integral_cexp_complex_gaussian_linear (1 - l i) ((1 - l i) * e.repr y i) (e.repr v i) (hre i)
  have hF : (fun z => cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v)) =
      (fun x : Fin n → ℂ => ∏ i, g i (x i)) ∘ Tm := by
    funext z
    simp only [Function.comp, g, hT, ← Complex.exp_sum, sesq_eq_sum_repr H e he, hr, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hint : Integrable (fun x : Fin n → ℂ => ∏ i, g i (x i)) volume :=
    Integrable.fintype_prod (f := g) fun i => (hg i).1
  rw [hF]
  refine ⟨?_, ?_⟩
  · rw [← integrable_map_equiv, hν]
    exact hint.smul_measure_nnreal
  · have h1 := integral_map_equiv (μ := μ) Tm (fun x : Fin n → ℂ => ∏ i, g i (x i))
    simp only [Function.comp_def]
    rw [← h1, hν, integral_smul_nnreal_measure, integral_fintype_prod_volume_eq_prod, hd,
      sesq_eq_sum_repr H e he, Finset.mul_sum, Complex.exp_sum]
    have h2 : ∀ i, ∫ z, g i z = (1 - l i)⁻¹ * cexp (π * (e.repr y i * conj (e.repr v i))) := fun i => by
      rw [show ∫ z, g i z = _ from (hg i).2]
      congr 2
      field_simp [hne i]
    simp only [h2, Finset.prod_mul_distrib, Finset.prod_inv_distrib, NNReal.smul_def, real_smul]
    ring

end GlobalTheory.UnitaryTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralGaussianUnitaryStatement
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_cexp_herm_gaussian_eq_div_det : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ a : V ≃ₗ[ℂ] V, (∀ z w, H (a z) (a w) = H z w) → LinearMap.det (1 - (a : V →ₗ[ℂ] V)) ≠ 0 → ∃ κ : ℝ, κ ≠ 0 ∧ ∀ y v : V, Integrable (fun z => cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v)) μ ∧ ∫ z, cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v) ∂μ = κ / LinearMap.det (1 - (a : V →ₗ[ℂ] V)) * cexp (π * H y v) := by
  first | exact @GlobalTheory.UnitaryTheta.integral_gaussian_unitary | exact GlobalTheory.UnitaryTheta.integral_gaussian_unitary | (intros; apply GlobalTheory.UnitaryTheta.integral_gaussian_unitary <;> assumption)
end
