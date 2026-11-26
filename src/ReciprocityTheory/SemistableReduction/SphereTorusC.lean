module

public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement

@[expose] public section

section -- merged from ReciprocityTheory.SemistableReduction.SphereTorusC
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric
open scoped Pointwise

private theorem toSphere_univ_ne_zero_of_pos {n : ℕ} (hn : 0 < n) :
    (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ 0 := by
  have : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    ⟨⟨EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℂ), 0, fun h => by
        simpa using congrArg norm h⟩⟩
  rw [Measure.toSphere_apply_univ]
  refine mul_ne_zero ?_ (measure_ball_pos _ _ one_pos).ne'
  exact_mod_cast (Module.finrank_pos (R := ℝ) (M := EuclideanSpace ℂ (Fin n))).ne'

private theorem toSphere_univ_ne_top' {n : ℕ} :
    (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ ⊤ := by
  exact measure_ne_top _ _

theorem isProbabilityMeasure_sphereProb {n : ℕ} (hn : 0 < n) :
    IsProbabilityMeasure (sphereProb n) := by
  constructor
  simp only [sphereProb, ProbabilityTheory.cond, Measure.smul_apply, Measure.restrict_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (toSphere_univ_ne_zero_of_pos hn) toSphere_univ_ne_top'

private theorem volume_preimage_linearIsometryEquiv {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n))
    (X : Set (EuclideanSpace ℂ (Fin n))) : volume (A ⁻¹' X) = volume X :=
  A.measurePreserving.measure_preimage_emb A.toHomeomorph.measurableEmbedding X

private theorem Ioo_smul_image_preimage_sphere_eq_preimage {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n)) (s : Set (UnitSphereC n)) :
    Set.Ioo (0 : ℝ) 1 • (Subtype.val '' ((fun z : UnitSphereC n =>
        (⟨A z, by simp⟩ : UnitSphereC n)) ⁻¹' s)) =
      A ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_smul, Set.mem_image]
  constructor
  · rintro ⟨r, hr, _, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨r, hr, _, ⟨⟨A z, by simp⟩, hz, rfl⟩, ?_⟩
    exact (map_smul A r (z : EuclideanSpace ℂ (Fin n))).symm
  · rintro ⟨r, hr, _, ⟨w, hw, rfl⟩, hx⟩
    refine ⟨r, hr, _, ⟨⟨A.symm w, by simp⟩, ?_, rfl⟩, ?_⟩
    · have hw' : (⟨A (A.symm (w : EuclideanSpace ℂ (Fin n))), by simp⟩ : UnitSphereC n) = w :=
        Subtype.ext (by simp)
      exact (congrArg (· ∈ s) hw').mpr hw
    · show r • A.symm (w : EuclideanSpace ℂ (Fin n)) = x
      calc r • A.symm (w : EuclideanSpace ℂ (Fin n))
          = A.symm (r • (w : EuclideanSpace ℂ (Fin n))) :=
            (map_smul A.symm r (w : EuclideanSpace ℂ (Fin n))).symm
        _ = x := by rw [hx, LinearIsometryEquiv.symm_apply_apply]

theorem measurePreserving_toSphere_isometry {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n)) :
    MeasurePreserving (fun z : UnitSphereC n => (⟨A z, by simp⟩ : UnitSphereC n))
      (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere
      (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere := by
  have hcont : Continuous (fun z : UnitSphereC n => (⟨A z, by simp⟩ : UnitSphereC n)) :=
    (A.continuous.comp continuous_subtype_val).subtype_mk _
  refine ⟨hcont.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hcont.measurable hs, Measure.toSphere_apply' (μ := volume) (hcont.measurable hs),
    Measure.toSphere_apply' (μ := volume) hs, Ioo_smul_image_preimage_sphere_eq_preimage A s,
    volume_preimage_linearIsometryEquiv]

def rotLIE {n : ℕ} (u : Fin n → Circle) : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) :=
  LinearIsometryEquiv.piLpCongrRight 2 fun j => rotation (u j)

theorem rotLIE_apply {n : ℕ} (u : Fin n → Circle) (x : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    (rotLIE u x).ofLp j = (u j : ℂ) * x.ofLp j := by
  rfl

def sphereRot {n : ℕ} (u : Fin n → Circle) (z : UnitSphereC n) : UnitSphereC n :=
  ⟨rotLIE u z, by simp⟩

private theorem measurePreserving_sphereProb_of_toSphere {n : ℕ} {f : UnitSphereC n → UnitSphereC n}
    (hf : MeasurePreserving f (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere
      (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere) :
    MeasurePreserving f (sphereProb n) (sphereProb n) := by
  refine ⟨hf.measurable, ?_⟩
  simp only [sphereProb, ProbabilityTheory.cond, Measure.restrict_univ]
  rw [Measure.map_smul _ hf.aemeasurable, hf.map_eq]

theorem measurePreserving_sphereRot {n : ℕ} (u : Fin n → Circle) :
    MeasurePreserving (sphereRot u) (sphereProb n) (sphereProb n) :=
  measurePreserving_sphereProb_of_toSphere (f := sphereRot u)
    (measurePreserving_toSphere_isometry (rotLIE u))

def blockRot {B n : ℕ} (θ : Fin B × Fin n → ℝ) (z : BlockSphere B n) : BlockSphere B n :=
  fun b => sphereRot (fun j => Circle.exp (2 * Real.pi * θ (b, j))) (z b)

private theorem coe_circle_exp_two_pi_mul (t : ℝ) :
    ((Circle.exp (2 * Real.pi * t) : Circle) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) := by
  rw [Circle.coe_exp]
  congr 1
  push_cast
  ring

theorem blockPoint_blockRot {B n : ℕ} (θ : Fin B × Fin n → ℝ) (z : BlockSphere B n) :
    blockPoint (blockRot θ z) = fun p => blockPoint z p * torusPoint θ p := by
  funext p
  obtain ⟨b, j⟩ := p
  show WithLp.ofLp (rotLIE (fun j' => Circle.exp (2 * Real.pi * θ (b, j')))
      (z b : EuclideanSpace ℂ (Fin n))) j =
    WithLp.ofLp (z b : EuclideanSpace ℂ (Fin n)) j * torusPoint θ (b, j)
  rw [rotLIE_apply]
  simp only [coe_circle_exp_two_pi_mul, torusPoint]
  ring

theorem measurePreserving_blockRot {B n : ℕ} (θ : Fin B × Fin n → ℝ) :
    MeasurePreserving (blockRot θ) (blockSphereProb B n) (blockSphereProb B n) := by
  have h : ∀ b : Fin B, MeasurePreserving
      (sphereRot (fun j => Circle.exp (2 * Real.pi * θ (b, j))))
      (sphereProb n) (sphereProb n) := fun b => measurePreserving_sphereRot _
  show MeasurePreserving (fun (z : BlockSphere B n) (b : Fin B) =>
      sphereRot (fun j => Circle.exp (2 * Real.pi * θ (b, j))) (z b))
    (Measure.pi fun _ => sphereProb n) (Measure.pi fun _ => sphereProb n)
  exact measurePreserving_pi (hf := h)

theorem sphereProb_coord_zero {n : ℕ} (j : Fin n) :
    sphereProb n {z | spherePoint z j = 0} = 0 := by
  let W : Submodule ℝ (EuclideanSpace ℂ (Fin n)) :=
    LinearMap.ker ((EuclideanSpace.proj j : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).restrictScalars ℝ).toLinearMap
  have hW : W ≠ ⊤ := by
    intro h
    have hmem : EuclideanSpace.single j (1 : ℂ) ∈ W := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker] at hmem
    change WithLp.ofLp (EuclideanSpace.single j (1 : ℂ)) j = 0 at hmem
    simp at hmem
  have hW0 : (volume : Measure (EuclideanSpace ℂ (Fin n))) (W : Set (EuclideanSpace ℂ (Fin n))) = 0 :=
    Measure.addHaar_submodule _ W hW
  have hmeas : MeasurableSet {z : UnitSphereC n | spherePoint z j = 0} := by
    have hc : Continuous fun z : UnitSphereC n => spherePoint z j := by
      exact (continuous_apply j).comp ((EuclideanSpace.equiv (Fin n) ℂ).continuous.comp
        continuous_subtype_val)
    exact (isClosed_singleton.preimage hc).measurableSet
  have hS : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere
      {z : UnitSphereC n | spherePoint z j = 0} = 0 := by
    rw [Measure.toSphere_apply' (μ := volume) hmeas]
    refine mul_eq_zero_of_right _ (measure_mono_null ?_ hW0)
    rintro x ⟨r, -, _, ⟨z, hz, rfl⟩, rfl⟩
    simp only [Set.mem_ofPred_eq, spherePoint] at hz
    show ((EuclideanSpace.proj j : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).restrictScalars ℝ)
      (r • (z : EuclideanSpace ℂ (Fin n))) = 0
    rw [map_smul]
    show r • WithLp.ofLp (z : EuclideanSpace ℂ (Fin n)) j = 0
    rw [hz, smul_zero]
  simp only [sphereProb, ProbabilityTheory.cond, Measure.restrict_univ, Measure.smul_apply,
    smul_eq_mul, hS, mul_zero]

theorem blockSphereProb_coord_zero {B n : ℕ} :
    blockSphereProb B n {z | ∃ p : Fin B × Fin n, blockPoint z p = 0} = 0 := by
  rw [Set.ofPred_exists]
  refine measure_iUnion_null fun p => ?_
  show (Measure.pi fun _ : Fin B => sphereProb n)
    (Function.eval p.1 ⁻¹' {w : UnitSphereC n | spherePoint w p.2 = 0}) = 0
  exact Measure.pi_eval_preimage_null _ (sphereProb_coord_zero p.2)

theorem norm_blockPoint_le {B n : ℕ} (z : BlockSphere B n) (p : Fin B × Fin n) :
    ‖blockPoint z p‖ ≤ 1 := by
  have h1 : ‖((z p.1 : UnitSphereC n) : EuclideanSpace ℂ (Fin n))‖ = 1 := norm_eq_of_mem_sphere _
  have h2 := EuclideanSpace.norm_eq ((z p.1 : UnitSphereC n) : EuclideanSpace ℂ (Fin n))
  rw [h1] at h2
  have h3 : ‖WithLp.ofLp ((z p.1 : UnitSphereC n) : EuclideanSpace ℂ (Fin n)) p.2‖ ^ 2 ≤
      ∑ i, ‖WithLp.ofLp ((z p.1 : UnitSphereC n) : EuclideanSpace ℂ (Fin n)) i‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ‖WithLp.ofLp ((z p.1 : UnitSphereC n) :
      EuclideanSpace ℂ (Fin n)) i‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ _)
  have h4 := Real.sqrt_le_sqrt h3
  rw [← h2, Real.sqrt_sq (norm_nonneg _)] at h4
  exact h4

end ReciprocityTheory.MultiplicativeHeights
end
end

section -- merged from ReciprocityTheory.SemistableReduction.ExistsDualDerivations
namespace ReciprocityTheory.MultiplicativeHeights

namespace DerivationAlgebraicIndependence

open MvPolynomial

section CoeffDer

variable {K Ω σ : Type*} [CommRing K] [CommRing Ω] [Algebra K Ω]

noncomputable def coeffMap (δ : Derivation K Ω Ω) (P : MvPolynomial σ Ω) : MvPolynomial σ Ω :=
  ∑ n ∈ P.support, monomial n (δ (AddMonoidAlgebra.coeff P n))

theorem coeff_coeffMap (δ : Derivation K Ω Ω) (P : MvPolynomial σ Ω) (n : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (coeffMap δ P) n = δ (AddMonoidAlgebra.coeff P n) := by
  classical
  unfold coeffMap
  rw [coeff_sum]
  by_cases h : n ∈ P.support
  · rw [Finset.sum_eq_single n]
    · rw [coeff_monomial, if_pos rfl]
    · intro b _ hb
      rw [coeff_monomial, if_neg hb]
    · intro hn
      exact absurd h hn
  · have h0 : AddMonoidAlgebra.coeff P n = 0 := by
      by_contra hc
      exact h (mem_support_iff.mpr hc)
    rw [h0, map_zero]
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [coeff_monomial, if_neg]
    rintro rfl
    exact h hb

theorem coeffMap_monomial (δ : Derivation K Ω Ω) (n : σ →₀ ℕ) (a : Ω) :
    coeffMap δ (monomial n a) = monomial n (δ a) := by
  classical
  ext m
  rw [coeff_coeffMap, coeff_monomial, coeff_monomial]
  split_ifs <;> simp

theorem coeffMap_add (δ : Derivation K Ω Ω) (P Q : MvPolynomial σ Ω) :
    coeffMap δ (P + Q) = coeffMap δ P + coeffMap δ Q := by
  ext m
  simp only [MvPolynomial.coeff_add, coeff_coeffMap, map_add (f := _)]

theorem coeffMap_smul (δ : Derivation K Ω Ω) (k : K) (P : MvPolynomial σ Ω) :
    coeffMap δ (k • P) = k • coeffMap δ P := by
  ext m
  rw [coeff_coeffMap, coeff_smul, coeff_smul, coeff_coeffMap,
    Derivation.map_smul]

theorem coeffMap_mul (δ : Derivation K Ω Ω) (P Q : MvPolynomial σ Ω) :
    coeffMap δ (P * Q) = P * coeffMap δ Q + Q * coeffMap δ P := by
  induction P using MvPolynomial.induction_on'
  · rename_i u a
    induction Q using MvPolynomial.induction_on'
    · rename_i v b
      rw [monomial_mul, coeffMap_monomial, coeffMap_monomial,
        coeffMap_monomial, monomial_mul, monomial_mul, Derivation.leibniz, smul_eq_mul,
        smul_eq_mul, map_add, add_comm v u]
    · rename_i p q hp hq
      simp only [mul_add, add_mul, coeffMap_add, hp, hq]
      ring
  · rename_i p q hp hq
    simp only [add_mul, mul_add, coeffMap_add, hp, hq]
    ring

noncomputable def coeffDer (δ : Derivation K Ω Ω) :
    Derivation K (MvPolynomial σ Ω) (MvPolynomial σ Ω) :=
  Derivation.mk' { toFun := coeffMap δ, map_add' := coeffMap_add δ, map_smul' := coeffMap_smul δ }
    (fun P Q => by simp only [LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]; exact coeffMap_mul δ P Q)

theorem coeffDer_apply (δ : Derivation K Ω Ω) (P : MvPolynomial σ Ω) :
    coeffDer δ P = coeffMap δ P := rfl

theorem coeffDer_C (δ : Derivation K Ω Ω) (a : Ω) :
    coeffDer (σ := σ) δ (C a) = C (δ a) := by
  simp only [coeffDer_apply, C_apply, coeffMap_monomial]

theorem coeffDer_X (δ : Derivation K Ω Ω) (v : σ) : coeffDer δ (X v : MvPolynomial σ Ω) = 0 := by
  rw [coeffDer_apply]
  show coeffMap δ (monomial (Finsupp.single v 1) 1) = 0
  rw [coeffMap_monomial, Derivation.map_one_eq_zero, map_zero]

end CoeffDer

private theorem exists_linearMap_dual_of_linearIndependent {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V]
    {D : ℕ} (v : Fin D → V) (hli : LinearIndependent Ω v) (a : Fin D) :
    ∃ g : V →ₗ[Ω] Ω, ∀ b, g (v b) = if a = b then 1 else 0 := by
  open Module in
  classical
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Basis.span hli).coord a)
  refine ⟨g, fun b => ?_⟩
  have hmem : v b ∈ Submodule.span Ω (Set.range v) := Submodule.subset_span ⟨b, rfl⟩
  have h1 : g (v b) = (Basis.span hli).coord a ⟨v b, hmem⟩ := LinearMap.congr_fun hg ⟨v b, hmem⟩
  have h2 : (⟨v b, hmem⟩ : Submodule.span Ω (Set.range v)) = Basis.span hli b :=
    Subtype.ext (by rw [Basis.span_apply])
  rw [h1, h2, Basis.coord_apply, Basis.repr_self]
  by_cases h : a = b
  · subst h
    simp
  · simp [h]

theorem exists_dual_derivations {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}
    (x : Fin m → Ω) (J : Fin D → Fin m)
    (hli : LinearIndependent Ω fun a => KaehlerDifferential.D K Ω (x (J a))) :
    ∃ δ : Fin D → Derivation K Ω Ω, ∀ a b, δ a (x (J b)) = if a = b then 1 else 0 := by
  choose g hg using exists_linearMap_dual_of_linearIndependent (fun a => KaehlerDifferential.D K Ω (x (J a))) hli
  exact ⟨fun a => (g a).compDer (KaehlerDifferential.D K Ω), fun a b => hg a b⟩

noncomputable def yPoly {Ω : Type*} [CommRing Ω] {D m : ℕ} (x : Fin m → Ω) (b : Fin D) :
    MvPolynomial (SVars D m) Ω :=
  -∑ k, X (Sum.inr (b.succ, k)) * C (x k)

noncomputable def gFam {Ω : Type*} [CommRing Ω] {D m : ℕ} (x : Fin m → Ω) :
    SVars D m ⊕ Fin D → MvPolynomial (SVars D m) Ω :=
  Sum.elim X (yPoly x)

private theorem coeffDer_linearCombinationPoly_apply {K Ω : Type*} [CommRing K] [CommRing Ω]
    [Algebra K Ω] {D m : ℕ} (δ : Derivation K Ω Ω) (x : Fin m → Ω) (b : Fin D) :
    coeffDer (σ := ReciprocityTheory.MultiplicativeHeights.SVars D m) δ (yPoly x b) =
      -∑ k, X (Sum.inr (b.succ, k)) * C (δ (x k)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [yPoly, map_neg, map_sum, Derivation.leibniz, coeffDer_X,
    coeffDer_C, smul_eq_mul, mul_zero, add_zero]

private theorem restrictScalars_pderiv_apply {K Ω σ : Type*} [CommRing K] [CommRing Ω]
    [Algebra K Ω] (w : σ) (f : MvPolynomial σ Ω) :
    ((pderiv w : Derivation Ω (MvPolynomial σ Ω) (MvPolynomial σ Ω)).restrictScalars K) f =
      pderiv w f := by
  exact congrFun (Derivation.coe_restrictScalars K _) f


set_option maxHeartbeats 800000 in
private theorem det_sum_X_mul_C_ne_zero_of_dual_family {Ω : Type*} [Field Ω] {D m : ℕ} (y : Fin D → Fin m → Ω)
    (J : Fin D → Fin m) (hy : ∀ a b, y a (J b) = if a = b then 1 else 0) :
    (Matrix.of fun a b : Fin D =>
      ∑ k, (X (Sum.inr (b.succ, k)) : MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω) * C (y a k)).det ≠ 0 := by
  classical
  obtain ⟨p, hp⟩ : ∃ p : ReciprocityTheory.MultiplicativeHeights.SVars D m → Ω, ∀ (b : Fin D) (k : Fin m),
      p (Sum.inr (b.succ, k)) = if k = J b then 1 else 0 :=
    ⟨Sum.elim (fun _ => 0)
      (fun q => Fin.cases (motive := fun _ => Ω) 0 (fun b => if q.2 = J b then 1 else 0) q.1),
      fun b k => by simp⟩
  intro h0
  have hmap : (eval p).mapMatrix (Matrix.of fun a b : Fin D =>
      ∑ k, (X (Sum.inr (b.succ, k)) : MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω) * C (y a k)) = 1 := by
    ext a b
    simp [RingHom.mapMatrix_apply, hp, hy, Matrix.one_apply]
  have h1 := RingHom.map_det (eval p) (Matrix.of fun a b : Fin D =>
      ∑ k, (X (Sum.inr (b.succ, k)) : MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω) * C (y a k))
  rw [h0, map_zero, hmap, Matrix.det_one] at h1
  exact zero_ne_one h1


set_option maxHeartbeats 800000 in
theorem gFam_indep {K Ω : Type*} [Field K] [CharZero K] [Field Ω] [Algebra K Ω] {D m : ℕ}
    (x : Fin m → Ω) (J : Fin D → Fin m) (δ : Fin D → Derivation K Ω Ω)
    (hδ : ∀ a b, δ a (x (J b)) = if a = b then 1 else 0) :
    AlgebraicIndependent K (gFam (D := D) x) := by
  classical
  have hz_inl : ∀ w, gFam (D := D) x (Sum.inl w) = X w := fun _ => rfl
  have hz_inr : ∀ b, gFam (D := D) x (Sum.inr b) = yPoly x b :=
    fun _ => rfl
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin D) (Fin D) (MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω),
      N = Matrix.of fun a b : Fin D =>
        ∑ k, (X (Sum.inr (b.succ, k)) : MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω) * C (δ a (x k)) :=
    ⟨_, rfl⟩
  have hNe : ∀ a b, N a b =
      ∑ k, (X (Sum.inr (b.succ, k)) : MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω) * C (δ a (x k)) := by
    intro a b
    rw [hN]
    rfl
  have hcd : ∀ a b, coeffDer (σ := ReciprocityTheory.MultiplicativeHeights.SVars D m) (δ a) (yPoly x b) =
      -N a b := by
    intro a b
    rw [hNe, coeffDer_linearCombinationPoly_apply]
  have hdet : N.det ≠ 0 := by
    rw [hN]
    exact det_sum_X_mul_C_ne_zero_of_dual_family (fun a k => δ a (x k)) J hδ
  refine algebraicIndependent_of_derivations (gFam (D := D) x)
    (Sum.elim (fun w : ReciprocityTheory.MultiplicativeHeights.SVars D m => (pderiv w : Derivation Ω (MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω)
        (MvPolynomial (ReciprocityTheory.MultiplicativeHeights.SVars D m) Ω)).restrictScalars K)
      (fun a : Fin D => coeffDer (σ := ReciprocityTheory.MultiplicativeHeights.SVars D m) (δ a))) ?_
  intro c hc
  have hmv : Matrix.mulVec N (fun b => c (Sum.inr b)) = 0 := by
    funext a
    have h1 := hc (Sum.inr a)
    simp only [Sum.elim_inr, Fintype.sum_sum_type, hz_inl, hz_inr, coeffDer_X, mul_zero,
      Finset.sum_const_zero, zero_add, hcd, mul_neg, Finset.sum_neg_distrib, neg_eq_zero] at h1
    show ∑ b, N a b * c (Sum.inr b) = 0
    exact (Finset.sum_congr rfl fun b _ => mul_comm (N a b) (c (Sum.inr b))).trans h1
  have hinr : ∀ b, c (Sum.inr b) = 0 := fun b =>
    congr_fun (Matrix.eq_zero_of_mulVec_eq_zero hdet hmv) b
  intro i
  rcases i with w | b
  · have h2 := hc (Sum.inl w)
    rw [Fintype.sum_sum_type] at h2
    simp only [Sum.elim_inl, hinr, zero_mul, Finset.sum_const_zero, add_zero,
      restrictScalars_pderiv_apply, hz_inl] at h2
    rw [Finset.sum_eq_single w] at h2
    · rw [pderiv_X_self, mul_one] at h2
      exact h2
    · intro w' _ hw'
      rw [pderiv_X_of_ne hw', mul_zero]
    · intro h
      exact absurd (Finset.mem_univ w) h
  · exact hinr b

def eIdx (D m : ℕ) (p : Fin (D + 1) × Fin (m + 1)) : SVars D m ⊕ Fin D :=
  Fin.cases (motive := fun _ => SVars D m ⊕ Fin D)
    (Fin.cases (motive := fun _ => SVars D m ⊕ Fin D) (Sum.inl (Sum.inl ())) Sum.inr p.1)
    (fun j => Sum.inl (Sum.inr (p.1, j))) p.2

theorem eIdx_injective (D m : ℕ) : Function.Injective (eIdx D m) := by
  rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
  induction j₁ using Fin.cases <;> induction j₂ using Fin.cases <;>
    induction i₁ using Fin.cases <;> induction i₂ using Fin.cases <;>
    simp_all [eIdx]

theorem sImage_eq {Ω : Type} [Field Ω] {D m : ℕ} (x : Fin m → Ω) (p : Fin (D + 1) × Fin (m + 1)) :
    sImage (D := D) x p =
      algebraMap (MvPolynomial (SVars D m) Ω) (SField Ω D m) (gFam x (eIdx D m p)) := by
  rcases p with ⟨i, j⟩
  induction j using Fin.cases <;> induction i using Fin.cases <;>
    simp [ReciprocityTheory.MultiplicativeHeights.sImage, eIdx, gFam, yPoly]

end DerivationAlgebraicIndependence

end ReciprocityTheory.MultiplicativeHeights
end
