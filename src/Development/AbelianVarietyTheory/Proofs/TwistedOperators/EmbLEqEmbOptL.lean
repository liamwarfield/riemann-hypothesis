module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FractionalBaseInclusion
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ISupEigenspaceEqTop

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbLEqEmbOptL
noncomputable section

namespace GlobalTheory.PackLoc

def embOpt {m N : ℕ} (e : Option (Fin m) ≃ Fin N) (h : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun a b => match e.symm a, e.symm b with
    | some i, some j => h i j
    | none, none => 1
    | _, _ => 0

def embOptL {m N : ℕ} (e : Option (Fin m) ≃ Fin N) (X : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun a b => match e.symm a, e.symm b with
    | some i, some j => X i j
    | _, _ => 0

theorem embH_eq_embOpt {n : ℕ} (e : Option (Fin n) ≃ Fin (n + 1)) (h : Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.SepReal.embH e h = embOpt e h := rfl

theorem embL_eq_embOptL {n : ℕ} (e : Option (Fin n) ≃ Fin (n + 1)) (X : Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.SepReal.embL e X = embOptL e X := rfl

theorem embOpt_one {m N : ℕ} (e : Option (Fin m) ≃ Fin N) : embOpt e 1 = 1 := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  cases a <;> cases b <;> simp [embOpt, Matrix.one_apply]

end GlobalTheory.PackLoc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSvd
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSvd
open Matrix Module

namespace GlobalTheory.RectSVD

theorem exists_orthonormalBasis_singularValues {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {p q : ℕ} (hp : finrank ℂ F = p) (hq : finrank ℂ E = q) (T : E →ₗ[ℂ] F) :
    ∃ (u : OrthonormalBasis (Fin p) ℂ F) (v : OrthonormalBasis (Fin q) ℂ E), ∀ i j,
      inner ℂ (u i) (T (v j)) =
        if (i : ℕ) = (j : ℕ) then ((T.singularValues i : ℝ) : ℂ) else 0 := by
  classical
  set v := T.isSymmetric_adjoint_comp_self.eigenvectorBasis hq with hv
  set σ : ℕ → ℝ := fun i => T.singularValues i with hσ
  have key : ∀ j k : Fin q, inner ℂ (T (v j)) (T (v k)) =
      if j = k then ((σ k : ℝ) : ℂ) ^ 2 else 0 := by
    intro j k
    have h1 := T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis hq k
    rw [← T.sq_singularValues_fin hq k] at h1
    rw [← LinearMap.adjoint_inner_right]
    change inner ℂ (v j) ((LinearMap.adjoint T ∘ₗ T) (v k)) = _
    rw [hv, h1, inner_smul_right, orthonormal_iff_ite.mp (OrthonormalBasis.orthonormal _)]
    split_ifs <;> simp [hσ]
  have hlt : ∀ i : ℕ, σ i ≠ 0 → i < p ∧ i < q := by
    intro i hi
    have h1 : i ∈ T.singularValues.support := Finsupp.mem_support_iff.mpr hi
    rw [T.support_singularValues, Finset.mem_range] at h1
    refine ⟨h1.trans_le (hp ▸ Submodule.finrank_le _), h1.trans_le (hq ▸ LinearMap.finrank_range_le T)⟩
  let w : Fin p → F := fun i =>
    if h : (i : ℕ) < q then ((σ i : ℂ))⁻¹ • T (v ⟨i, h⟩) else 0
  have hw : Orthonormal ℂ (({i : Fin p | σ i ≠ 0} : Set (Fin p)).domRestrict w) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨k, hk⟩
    have hi' : σ i ≠ 0 := hi
    have hk' : σ k ≠ 0 := hk
    have hkc : (σ k : ℂ) ≠ 0 := by exact_mod_cast hk'
    simp only [Set.domRestrict_apply, w, dif_pos (hlt _ hi').2, dif_pos (hlt _ hk').2,
      inner_smul_left, inner_smul_right, key, Subtype.mk.injEq, Fin.mk.injEq, Fin.ext_iff]
    split_ifs with h
    · rw [h]
      simp only [map_inv₀, Complex.conj_ofReal]
      field_simp
    · simp
  obtain ⟨u, hu⟩ := hw.exists_orthonormalBasis_extension_of_card_eq
    (by rw [hp, Fintype.card_fin])
  refine ⟨u, v, fun i j => ?_⟩
  by_cases hj : σ j = 0
  · have h0 : T (v j) = 0 := by
      have := key j j
      rw [if_pos rfl, hj] at this
      simpa using this
    rw [h0, inner_zero_right]
    split_ifs with h
    · have : T.singularValues i = 0 := by rw [h]; exact hj
      simp [this]
    · rfl
  · have hjc : (σ j : ℂ) ≠ 0 := by exact_mod_cast hj
    have h1 := hu ⟨j, (hlt _ hj).1⟩ hj
    have h2 : T (v j) = (σ j : ℂ) • u ⟨j, (hlt _ hj).1⟩ := by
      rw [h1]
      simp only [w, dif_pos j.isLt, Fin.eta, smul_smul, mul_inv_cancel₀ hjc, one_smul]
    rw [h2, inner_smul_right, orthonormal_iff_ite.mp u.orthonormal]
    simp only [Fin.ext_iff]
    split_ifs with h
    · simp [h, hσ]
    · simp

theorem exists_svd_singularValues (p q : ℕ) (B : Matrix (Fin p) (Fin q) ℂ) :
    ∃ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∃ V ∈ Matrix.unitaryGroup (Fin q) ℂ,
      B = U * (Matrix.of fun (i : Fin p) (j : Fin q) =>
        if (i : ℕ) = (j : ℕ) then (((Matrix.toEuclideanLin B).singularValues i : ℝ) : ℂ) else 0)
          * Vᴴ := by
  obtain ⟨u, v, h⟩ := exists_orthonormalBasis_singularValues
    (E := EuclideanSpace ℂ (Fin q)) (F := EuclideanSpace ℂ (Fin p)) (p := p) (q := q)
    (by simp) (by simp) (Matrix.toEuclideanLin B)
  have hU := (EuclideanSpace.basisFun (Fin p) ℂ).toMatrix_orthonormalBasis_mem_unitary u
  have hV := (EuclideanSpace.basisFun (Fin q) ℂ).toMatrix_orthonormalBasis_mem_unitary v
  refine ⟨_, hU, _, hV, ?_⟩
  set U := (EuclideanSpace.basisFun (Fin p) ℂ).toBasis.toMatrix u with hUd
  set V := (EuclideanSpace.basisFun (Fin q) ℂ).toBasis.toMatrix v with hVd
  have hD : (Matrix.of fun (i : Fin p) (j : Fin q) =>
      if (i : ℕ) = (j : ℕ) then (((Matrix.toEuclideanLin B).singularValues i : ℝ) : ℂ) else 0)
        = Uᴴ * B * V := by
    ext i j
    rw [Matrix.of_apply, ← h, Matrix.mul_assoc]
    simp [hUd, hVd, Matrix.mul_apply, Basis.toMatrix_apply, PiLp.inner_apply, Matrix.mulVec,
      dotProduct, mul_comm]
  have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have h2 : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hV
  rw [hD, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h2,
    Matrix.mul_one]

theorem exists_svd : ∀ (p q : ℕ) (B : Matrix (Fin p) (Fin q) ℂ),
    ∃ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∃ V ∈ Matrix.unitaryGroup (Fin q) ℂ, ∃ h : ℕ → ℝ,
      B = U * (Matrix.of fun (i : Fin p) (j : Fin q) =>
        if (i : ℕ) = (j : ℕ) then ((h i : ℝ) : ℂ) else 0) * Vᴴ := by
  intro p q B
  obtain ⟨U, hU, V, hV, h⟩ := exists_svd_singularValues p q B
  exact ⟨U, hU, V, hV, fun i => (Matrix.toEuclideanLin B).singularValues i, h⟩

end GlobalTheory.RectSVD
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSvdStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_mul_diagonal_real_mul_conjTranspose : ∀ (p q : ℕ) (B : Matrix (Fin p) (Fin q) ℂ), ∃ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∃ V ∈ Matrix.unitaryGroup (Fin q) ℂ, ∃ h : ℕ → ℝ, B = U * (Matrix.of fun (i : Fin p) (j : Fin q) => if (i : ℕ) = (j : ℕ) then ((h i : ℝ) : ℂ) else 0) * Vᴴ := by
  first | exact @GlobalTheory.RectSVD.exists_svd | exact GlobalTheory.RectSVD.exists_svd | (intros; apply GlobalTheory.RectSVD.exists_svd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FractionFieldEmbeddingCompat
noncomputable section

namespace GlobalTheory.Proof.FractionFieldEmbeddingCompat

open Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion

theorem fracExt_fracBase_algebraMap {D : D7} (c : NChoice D) (w : D.what₂.places.Pl) (y : D.ntw.O0 (c.twI w)) :
    fracExt c w (fracBase D (c.twI w) (algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y)) =
      algebraMap (c.Oe w) (FractionRing (c.Oe w)) (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)
        (algebraMap (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w))
          (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) y))) := by
  rw [← IsScalarTower.algebraMap_apply (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)]
  simp [fracExt, fracBase, IsFractionRing.map]

theorem embW_eq_of_tie {D : D7} {c : NChoice D} (h : NChTie D c) (w : D.what₂.places.Pl) (x : D.LL0) :
    c.embW w (x : D.what₂.LL) = fracExt c w (fracBase D (c.twI w) (embSide D (c.twI w) (c.sd w) x)) := by
  obtain ⟨y, z, hz, hyz⟩ := IsFractionRing.div_surjective (A := D.ntw.O0 (c.twI w)) (embSide D (c.twI w) (c.sd w) x)
  have hz0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
  have hz1 : algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) z ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hz0
  have hmul : embSide D (c.twI w) (c.sd w) x * algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) z =
      algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y := by
    rw [← hyz, div_mul_cancel₀ _ hz1]
  have e := h.embedding_baseField_condition w x y z hz0 hmul
  rw [← fracExt_fracBase_algebraMap, ← fracExt_fracBase_algebraMap, ← hmul, map_mul, map_mul] at e
  exact mul_right_cancel₀ ((map_ne_zero _).2 ((map_ne_zero _).2 hz1)) e

theorem embCompat : EmbCompat := by
  intro D c h K _ _ _ κ hκ w ιK hι
  subst hι
  ext x
  have e := embW_eq_of_tie h w (κ x)
  rw [hκ x] at e
  exact e

end GlobalTheory.Proof.FractionFieldEmbeddingCompat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousOnPolarLog
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

noncomputable section
namespace GlobalTheory.PolarLogCont

section
open scoped Matrix.Norms.L2Operator ComplexOrder
variable {n : Type} [Fintype n] [DecidableEq n]

def halfLog (g : Matrix n n ℂ) : Matrix n n ℂ := (1 / 2 : ℝ) • CFC.log (gᴴ * g)

theorem continuousOn_halfLog : ContinuousOn (halfLog (n := n)) {g | IsUnit g} := by
  have h : ContinuousOn (fun g : Matrix n n ℂ => CFC.log (gᴴ * g)) {g | IsUnit g} := by
    refine CFC.continuousOn_log.comp (by fun_prop) ?_
    intro g hg
    have hu : IsUnit g := hg
    refine ⟨?_, ?_⟩
    · show star (gᴴ * g) = gᴴ * g
      rw [star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
    · exact (show IsUnit gᴴ from hu.star).mul hu
  exact h.const_smul (1 / 2 : ℝ)

theorem halfLog_mul_exp (c Y : Matrix n n ℂ) (hc : cᴴ * c = 1) (hY : Yᴴ = Y) :
    halfLog (c * NormedSpace.exp Y) = Y := by
  have he : (NormedSpace.exp Y)ᴴ = NormedSpace.exp Y := by
    rw [← Matrix.exp_conjTranspose, hY]
  have h2 : NormedSpace.exp (Y + Y) = NormedSpace.exp Y * NormedSpace.exp Y :=
    Matrix.exp_add_of_commute _ _ (Commute.refl Y)
  have sq : (c * NormedSpace.exp Y)ᴴ * (c * NormedSpace.exp Y) = NormedSpace.exp (Y + Y) := by
    rw [conjTranspose_mul, he, h2]
    calc NormedSpace.exp Y * cᴴ * (c * NormedSpace.exp Y)
        = NormedSpace.exp Y * (cᴴ * c) * NormedSpace.exp Y := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hc, Matrix.mul_one]
  have hsa : IsSelfAdjoint (Y + Y) := by
    rw [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_add, hY]
  unfold halfLog
  rw [sq, CFC.log_exp _ hsa, ← two_smul ℝ Y, smul_smul]
  norm_num

end

theorem exists_continuousOn_polar_log : ∀ (p q : ℕ), ∃ L : Mat p q → (Fin p → Fin q → ℂ), ContinuousOn L {g | IsUnit g} ∧ ∀ (k : Mat p q) (B : Fin p → Fin q → ℂ), kᴴ * k = 1 → L (k * NormedSpace.exp (pY B)) = B := by
  intro p q
  refine ⟨fun g i j => halfLog g (Sum.inl i) (Sum.inr j), ?_, ?_⟩
  · have hc : Continuous fun (M : Mat p q) (i : Fin p) (j : Fin q) => M (Sum.inl i) (Sum.inr j) := by
      fun_prop
    exact hc.comp_continuousOn continuousOn_halfLog
  · intro k B hk
    funext i j
    show halfLog (k * NormedSpace.exp (pY B)) (Sum.inl i) (Sum.inr j) = B i j
    rw [halfLog_mul_exp k _ hk (pY_conjTranspose B)]
    simp [pY, pOf]

end GlobalTheory.PolarLogCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBiinvariantProbabilityOnCompactSubgroup
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory

theorem exists_biinvariant_probability_on_compact_subgroup :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (K : Subgroup G), IsCompact (K : Set G) → ∃ mK : Measure G, IsProbabilityMeasure mK ∧ mK (K : Set G)ᶜ = 0 ∧ (∀ k ∈ K, Measure.map (fun x => k * x) mK = mK) ∧ ∀ k ∈ K, Measure.map (fun x => x * k) mK = mK := by
  intro G _ _ _ _ _ _ _ K hK
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : BorelSpace K := Subtype.borelSpace (fun x => x ∈ (K : Set G))
  let μ : Measure K := Measure.haarMeasure ⊤
  have : IsProbabilityMeasure μ := ⟨by
    have := Measure.haarMeasure_self (G := K) (K₀ := ⊤)
    simpa using this⟩
  have : μ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  have hv : Measurable (Subtype.val : K → G) := measurable_subtype_coe
  have hKm : MeasurableSet (K : Set G) := hK.isClosed.measurableSet
  refine ⟨μ.map Subtype.val, inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.map_apply hv hKm.compl]
    have : (Subtype.val : K → G) ⁻¹' (K : Set G)ᶜ = ∅ := by
      ext x; simp
    rw [this]; simp
  · intro k hk
    rw [Measure.map_map (measurable_const_mul k) hv]
    have h1 : μ.map (fun x : K => (⟨k, hk⟩ : K) * x) = μ := map_mul_left_eq_self μ _
    conv_rhs => rw [← h1]
    rw [Measure.map_map hv (measurable_const_mul _)]
    rfl
  · intro k hk
    rw [Measure.map_map (measurable_mul_const k) hv]
    have h1 : μ.map (fun x : K => x * (⟨k, hk⟩ : K)) = μ := by
      have : (μ.map (fun x : K => x * (⟨k, hk⟩ : K))).IsHaarMeasure :=
        Measure.isHaarMeasure_map_mul_right μ _
      exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _
    conv_rhs => rw [← h1]
    rw [Measure.map_map hv (measurable_mul_const _)]
    rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapWithDensityOfJacobianComplexMatrices
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapWithDensityOfJacobianComplexMatrices
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory

theorem map_withDensity_of_jacobian_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (J : E → ℝ) (ψ : E → E) (hψ : Continuous ψ)
    (hb : Function.Bijective ψ)
    (h : ∀ B, ∃ P : E →L[ℝ] E, HasFDerivAt ψ P B ∧ |P.det| * J (ψ B) = J B) :
    Measure.map ψ (μ.withDensity fun B => ENNReal.ofReal (J B)) =
      μ.withDensity fun B => ENNReal.ofReal (J B) := by

  choose P hP hJ using h
  have hm : Measurable ψ := hψ.measurable
  ext A hA
  rw [Measure.map_apply hm hA, withDensity_apply _ hA, withDensity_apply _ (hm hA)]
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul μ (hm hA)
    (fun x _ => (hP x).hasFDerivWithinAt) hb.injective.injOn (fun y => ENNReal.ofReal (J y))
  rw [Set.image_preimage_eq A hb.surjective] at hcv
  rw [hcv]
  refine lintegral_congr (fun x => ?_)
  rw [← ENNReal.ofReal_mul (abs_nonneg _), hJ x]

theorem map_withDensity_of_jacobian : ∀ (p q : ℕ) (J : (Fin p → Fin q → ℂ) → ℝ) (ψ : (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ)), Continuous J → Continuous ψ → Function.Bijective ψ → (∀ B, ∃ P : (Fin p → Fin q → ℂ) →L[ℝ] (Fin p → Fin q → ℂ), HasFDerivAt ψ P B ∧ |P.det| * J (ψ B) = J B) → Measure.map ψ (volume.withDensity fun B => ENNReal.ofReal (J B)) = volume.withDensity fun B => ENNReal.ofReal (J B) := by

  intro p q J ψ _ hψ hb h
  haveI hrow : (volume : Measure (Fin q → ℂ)).IsAddHaarMeasure := by
    rw [volume_pi]; infer_instance
  haveI hall : (volume : Measure (Fin p → Fin q → ℂ)).IsAddHaarMeasure := by
    rw [volume_pi]; exact Measure.pi.isAddHaarMeasure _
  exact map_withDensity_of_jacobian_gen (volume : Measure (Fin p → Fin q → ℂ)) J ψ hψ hb h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapWithDensityOfJacobianComplexMatricesStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_withDensity_of_jacobian_complexMatrices : ∀ (p q : ℕ) (J : (Fin p → Fin q → ℂ) → ℝ) (ψ : (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ)), Continuous J → Continuous ψ → Function.Bijective ψ → (∀ B, ∃ P : (Fin p → Fin q → ℂ) →L[ℝ] (Fin p → Fin q → ℂ), HasFDerivAt ψ P B ∧ |P.det| * J (ψ B) = J B) → Measure.map ψ (volume.withDensity fun B => ENNReal.ofReal (J B)) = volume.withDensity fun B => ENNReal.ofReal (J B) := by
  first | exact @GlobalTheory.map_withDensity_of_jacobian | exact GlobalTheory.map_withDensity_of_jacobian | (intros; apply GlobalTheory.map_withDensity_of_jacobian <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasStrictFDerivAtExpTwoUpperRightBlockElementP
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasStrictFDerivAtExpTwoUpperRightBlockElementP
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

noncomputable section
namespace GlobalTheory.PolarU

def twoPYLin (p q : ℕ) : (Fin p → Fin q → ℂ) →ₗ[ℝ] Mat p q where
  toFun C := pY C + pY C
  map_add' B C := by rw [pY_add]; abel
  map_smul' t B := by rw [pY_smul, smul_add]; rfl

def entryLin {p q : ℕ} (a b : Ix p q) : Mat p q →ₗ[ℝ] ℂ where
  toFun M := M a b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open scoped Matrix.Norms.Operator in
theorem contDiff_exp_two_pY_entry (p q : ℕ) (a b : Ix p q) :
    ContDiff ℝ 1 (fun C : Fin p → Fin q → ℂ => NormedSpace.exp (pY C + pY C) a b) := by
  have h1 : ContDiff ℝ 1 (NormedSpace.exp : Mat p q → Mat p q) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  have h2 : ContDiff ℝ 1 (fun C : Fin p → Fin q → ℂ => (pY C + pY C : Mat p q)) :=
    (LinearMap.toContinuousLinearMap (twoPYLin p q)).contDiff
  have h3 : ContDiff ℝ 1 (fun M : Mat p q => M a b) :=
    (LinearMap.toContinuousLinearMap (entryLin a b)).contDiff
  exact h3.comp (h1.comp h2)

theorem hasStrictFDerivAt_exp_two_pY : ∀ (p q : ℕ) (B : Fin p → Fin q → ℂ), (∀ (V : Mat p q) (a b : Ix p q), HasDerivAt (fun t : ℝ => NormedSpace.exp (pY B + pY B + t • V) a b) ((NormedSpace.exp (pY B) * sAd (pY B) V * NormedSpace.exp (pY B)) a b) 0) → ∃ A : (Fin p → Fin q → ℂ) →L[ℝ] (Ix p q → Ix p q → ℂ), HasStrictFDerivAt (fun (C : Fin p → Fin q → ℂ) (a b : Ix p q) => NormedSpace.exp (pY C + pY C) a b) A B ∧ ∀ C, Matrix.of (A C) = NormedSpace.exp (pY B) * sAd (pY B) (pY C + pY C) * NormedSpace.exp (pY B) := by
  intro p q B h
  have hc : ContDiff ℝ 1 (fun (C : Fin p → Fin q → ℂ) (a b : Ix p q) =>
      NormedSpace.exp (pY C + pY C) a b) :=
    contDiff_pi.2 fun a => contDiff_pi.2 fun b => contDiff_exp_two_pY_entry p q a b
  have hs := hc.contDiffAt.hasStrictFDerivAt_fderiv (x := B) (by simp)
  refine ⟨_, hs, fun C => ?_⟩
  ext a b
  have hl : HasDerivAt (fun t : ℝ => B + t • C) C 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const C).const_add B
  have h1 := hs.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 a) b
  have h3 := h (pY C + pY C) a b
  have e : (fun t : ℝ => NormedSpace.exp (pY B + pY B + t • (pY C + pY C)) a b) =
      fun t : ℝ => NormedSpace.exp (pY (B + t • C) + pY (B + t • C)) a b := by
    funext t
    have e' : pY B + pY B + t • (pY C + pY C) = pY (B + t • C) + pY (B + t • C) := by
      rw [pY_add, pY_smul, smul_add]; abel
    rw [e']
  rw [e] at h3
  exact h2.unique h3

end GlobalTheory.PolarU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasStrictFDerivAtExpTwoUpperRightBlockElementPStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasStrictFDerivAt_exp_two_upperRightBlockElementP : ∀ (p q : ℕ) (B : Fin p → Fin q → ℂ), (∀ (V : Mat p q) (a b : Ix p q), HasDerivAt (fun t : ℝ => NormedSpace.exp (pY B + pY B + t • V) a b) ((NormedSpace.exp (pY B) * sAd (pY B) V * NormedSpace.exp (pY B)) a b) 0) → ∃ A : (Fin p → Fin q → ℂ) →L[ℝ] (Ix p q → Ix p q → ℂ), HasStrictFDerivAt (fun (C : Fin p → Fin q → ℂ) (a b : Ix p q) => NormedSpace.exp (pY C + pY C) a b) A B ∧ ∀ C, Matrix.of (A C) = NormedSpace.exp (pY B) * sAd (pY B) (pY C + pY C) * NormedSpace.exp (pY B) := by
  first | exact @GlobalTheory.PolarU.hasStrictFDerivAt_exp_two_pY | exact GlobalTheory.PolarU.hasStrictFDerivAt_exp_two_pY | (intros; apply GlobalTheory.PolarU.hasStrictFDerivAt_exp_two_pY <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SinhcAdMulVecOfAdSqEigen
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SinhcAdMulVecOfAdSqEigen
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU


open scoped Matrix.Norms.Operator in
theorem summable_sinhc_series_mat {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    Summable fun k : ℕ => (((2 * k + 1).factorial : ℂ)⁻¹) • A ^ (2 * k) := by
  have h0 : Summable fun m : ℕ => ‖((m.factorial : ℂ)⁻¹) • A ^ m‖ :=
    NormedSpace.norm_expSeries_summable' A
  have h1 : Summable fun k : ℕ => ‖(((2 * k).factorial : ℂ)⁻¹) • A ^ (2 * k)‖ :=
    h0.comp_injective (i := fun k : ℕ => 2 * k) (fun a b h => by simpa using h)
  refine Summable.of_norm_bounded h1 fun k => ?_
  rw [norm_smul, norm_smul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [norm_inv, norm_inv, Complex.norm_natCast, Complex.norm_natCast]
  refine inv_anti₀ (by exact_mod_cast Nat.factorial_pos _) ?_
  exact_mod_cast Nat.factorial_le (Nat.le_succ _)

theorem hasSum_shc_series (x : ℝ) :
    HasSum (fun k : ℕ => (((2 * k + 1).factorial : ℝ)⁻¹) * x ^ (2 * k)) (shc x) := by
  unfold shc
  split_ifs with hx
  · subst hx
    have := hasSum_single (f := fun k : ℕ => (((2 * k + 1).factorial : ℝ)⁻¹) * (0 : ℝ) ^ (2 * k)) 0
      (fun k hk => by simp [hk])
    simpa using this
  · have h := (Real.hasSum_sinh x).div_const x
    have e : (fun k : ℕ => (((2 * k + 1).factorial : ℝ)⁻¹) * x ^ (2 * k))
        = fun k : ℕ => x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) / x := by
      funext k
      rw [pow_succ]
      field_simp
    rw [e]
    exact h

theorem sinhcAd_mulVec_of_sq_eigen : ∀ (p q : ℕ) (Y : Mat p q) (v : Ix p q × Ix p q → ℂ) (x : ℝ),
    (adMat Y ^ 2) *ᵥ v = ((x : ℂ) ^ 2) • v → sinhcAd Y *ᵥ v = ((shc x : ℝ) : ℂ) • v := by
  intro p q Y v x h
  have hk : ∀ k : ℕ, (adMat Y ^ (2 * k)) *ᵥ v = ((x : ℂ) ^ (2 * k)) • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [mul_add, mul_one, pow_add, pow_add, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih,
        smul_smul, mul_comm]
  let L : Matrix (Ix p q × Ix p q) (Ix p q × Ix p q) ℂ →+ (Ix p q × Ix p q → ℂ) :=
    { toFun := fun M => M *ᵥ v
      map_zero' := Matrix.zero_mulVec v
      map_add' := fun M N => Matrix.add_mulVec M N v }
  have hL : Continuous L := continuous_id.matrix_mulVec continuous_const
  have h1 := (summable_sinhc_series_mat (adMat Y)).hasSum.map L hL
  have h2 : HasSum (fun k : ℕ => (((((2 * k + 1).factorial : ℝ)⁻¹) * x ^ (2 * k) : ℝ) : ℂ) • v)
      (((shc x : ℝ) : ℂ) • v) := (Complex.hasSum_ofReal.2 (hasSum_shc_series x)).smul_const v
  refine h1.unique ?_
  convert h2 using 1
  funext k
  show (_ • _) *ᵥ v = _
  rw [Matrix.smul_mulVec, hk, smul_smul]
  push_cast
  rfl

end GlobalTheory.PolarU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SinhcAdMulVecOfAdSqEigenStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sinhcAd_mulVec_of_adSq_eigen : ∀ (p q : ℕ) (Y : Mat p q) (v : Ix p q × Ix p q → ℂ) (x : ℝ), (adMat Y ^ 2) *ᵥ v = ((x : ℂ) ^ 2) • v → sinhcAd Y *ᵥ v = ((shc x : ℝ) : ℂ) • v := by
  first | exact @GlobalTheory.PolarU.sinhcAd_mulVec_of_sq_eigen | exact GlobalTheory.PolarU.sinhcAd_mulVec_of_sq_eigen | (intros; apply GlobalTheory.PolarU.sinhcAd_mulVec_of_sq_eigen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousPolarCoordinatesJacobian
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousPolarCoordinatesJacobian
noncomputable section
namespace GlobalTheory.PolarU
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

theorem continuous_sinhc_series {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] :
    Continuous fun x : A => ∑' k : ℕ, (((2 * k + 1).factorial : ℂ)⁻¹) • x ^ (2 * k) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  set R : ℝ := ‖x₀‖ + 1
  have hball : Metric.ball x₀ 1 ∈ nhds x₀ := Metric.ball_mem_nhds x₀ one_pos
  refine ContinuousOn.continuousAt ?_ hball
  have hsum : Summable fun k : ℕ => ((2 * k + 1).factorial : ℝ)⁻¹ * (‖(1 : A)‖ + R ^ (2 * k)) := by
    have h1 : Summable fun n : ℕ => R ^ n / (n.factorial : ℝ) := Real.summable_pow_div_factorial R
    have h2 : Summable fun k : ℕ => R ^ (2 * k) / ((2 * k).factorial : ℝ) := by
      have := h1.comp_injective (i := fun k : ℕ => 2 * k) (fun a b h => by simp only at h; omega)
      simpa only [Function.comp_def] using this
    have h3 : Summable fun n : ℕ => (1 : ℝ) ^ n / (n.factorial : ℝ) := Real.summable_pow_div_factorial 1
    have h4 : Summable fun k : ℕ => ((2 * k + 1).factorial : ℝ)⁻¹ := by
      have := h3.comp_injective (i := fun k : ℕ => 2 * k + 1) (fun a b h => by simp only at h; omega)
      simpa only [Function.comp_def, one_pow, one_div] using this
    refine (((h4.mul_left ‖(1 : A)‖)).add h2).of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    rw [mul_add, mul_comm _ ‖(1 : A)‖]
    gcongr
    have hf : ((2 * k).factorial : ℝ) ≤ ((2 * k + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    have hp : (0 : ℝ) < ((2 * k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hp hf) (by positivity)
  refine continuousOn_tsum (fun k => (continuous_const.smul (continuous_pow _)).continuousOn) hsum ?_
  intro k x hx
  have hxR : ‖x‖ ≤ R := by
    have := Metric.mem_ball.1 hx
    have h := norm_le_norm_add_norm_sub' x x₀
    rw [dist_eq_norm] at this
    simp only [R]; linarith
  have hpow : ‖x ^ (2 * k)‖ ≤ ‖(1 : A)‖ + R ^ (2 * k) := by
    rcases Nat.eq_zero_or_pos (2 * k) with h | h
    · rw [h, pow_zero, pow_zero]; linarith [norm_nonneg (1 : A)]
    · calc ‖x ^ (2 * k)‖ ≤ ‖x‖ ^ (2 * k) := norm_pow_le' x h
        _ ≤ R ^ (2 * k) := pow_le_pow_left₀ (norm_nonneg x) hxR _
        _ ≤ ‖(1 : A)‖ + R ^ (2 * k) := le_add_of_nonneg_left (norm_nonneg _)
  calc ‖(((2 * k + 1).factorial : ℂ)⁻¹) • x ^ (2 * k)‖
      ≤ ‖(((2 * k + 1).factorial : ℂ)⁻¹)‖ * ‖x ^ (2 * k)‖ := norm_smul_le _ _
    _ = ((2 * k + 1).factorial : ℝ)⁻¹ * ‖x ^ (2 * k)‖ := by rw [norm_inv, Complex.norm_natCast]
    _ ≤ ((2 * k + 1).factorial : ℝ)⁻¹ * (‖(1 : A)‖ + R ^ (2 * k)) := by gcongr

theorem continuous_adMat (p q : ℕ) : Continuous (adMat : Mat p q → _) := by
  unfold adMat
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply, Matrix.transpose_apply]
  exact ((continuous_apply_apply a.1 b.1).mul continuous_const).sub
    (continuous_const.mul (continuous_apply_apply b.2 a.2))

open scoped Matrix.Norms.Operator in
theorem continuous_sinhcAd (p q : ℕ) : Continuous (sinhcAd : Mat p q → _) := by
  unfold sinhcAd
  exact continuous_sinhc_series.comp (continuous_adMat p q)

theorem continuous_polJ : ∀ (p q : ℕ), Continuous (polJ : Mat p q → ℝ) := by
  intro p q
  unfold polJ
  exact Complex.continuous_re.comp
    (((continuous_sinhcAd p q).matrix_submatrix _ _).matrix_det)

end GlobalTheory.PolarU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousPolarCoordinatesJacobianStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_polarCoordinatesJacobian : ∀ (p q : ℕ), Continuous (polJ : Mat p q → ℝ) := by
  first | exact @GlobalTheory.PolarU.continuous_polJ | exact GlobalTheory.PolarU.continuous_polJ | (intros; apply GlobalTheory.PolarU.continuous_polJ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetAdSqEigenvectorMatrixUnitPNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetAdSqEigenvectorMatrixUnitPNeZero
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU


open scoped ComplexOrder in
theorem det_ne_zero_of_add_conjTranspose {n : Type} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℂ) (h : P + Pᴴ = (2 : ℂ) • (1 : Matrix n n ℂ)) : P.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0

  have hquad : star v ⬝ᵥ ((P + Pᴴ) *ᵥ v) = 2 * (star v ⬝ᵥ v) := by
    rw [h]
    first
      | simp [smul_mulVec, dotProduct_smul, smul_eq_mul]
      | simp [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]
      | simp [dotProduct_smul, smul_eq_mul]

  have hzero : star v ⬝ᵥ ((P + Pᴴ) *ᵥ v) = 0 := by
    have hstar : star v ᵥ* Pᴴ = star (P *ᵥ v) := (star_mulVec P v).symm
    rw [add_mulVec, dotProduct_add, dotProduct_mulVec (star v) Pᴴ v, hstar, hv]
    simp
  have hnorm : star v ⬝ᵥ v = 0 := by
    have h2 : (2 : ℂ) * (star v ⬝ᵥ v) = 0 := hquad.symm.trans hzero
    rcases mul_eq_zero.mp h2 with h2 | h2
    · norm_num at h2
    · exact h2
  exact dotProduct_star_self_eq_zero.mp hnorm

private lemma isLeft_ne_of_posIx_eq {p q : ℕ} (x y : Ix p q × Ix p q) (hx : ¬ sameBlock x.1 x.2)
    (hy : ¬ sameBlock y.1 y.2) (hne : y ≠ x) (h1 : posIx y.1 = posIx x.1)
    (h2 : posIx y.2 = posIx x.2) : x.1.isLeft ≠ y.1.isLeft := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  rcases x1 with i | i <;> rcases x2 with j | j <;> rcases y1 with k | k <;> rcases y2 with l | l <;>
    simp_all [sameBlock, posIx, Fin.ext_iff]

private lemma eigP_add_star_eigP_eq_zero {p q : ℕ} (x y : Ix p q × Ix p q) (hx : ¬ sameBlock x.1 x.2)
    (hy : ¬ sameBlock y.1 y.2) (hne : y ≠ x) : eigP x y + star (eigP y x) = 0 := by
  unfold eigP
  rw [if_neg hne, if_neg (Ne.symm hne)]
  by_cases h : posIx y.1 = posIx x.1 ∧ posIx y.2 = posIx x.2
  · have c1 : ¬ sameBlock y.1 y.2 ∧ posIx y.1 = posIx x.1 ∧ posIx y.2 = posIx x.2 := ⟨hy, h⟩
    have c2 : ¬ sameBlock x.1 x.2 ∧ posIx x.1 = posIx y.1 ∧ posIx x.2 = posIx y.2 :=
      ⟨hx, h.1.symm, h.2.symm⟩
    rw [if_pos c1, if_pos c2]
    have hL := isLeft_ne_of_posIx_eq x y hx hy hne h.1 h.2
    generalize x.1.isLeft = s at hL ⊢
    generalize y.1.isLeft = t at hL ⊢
    cases s <;> cases t <;> simp at hL ⊢
  · have c1 : ¬ (¬ sameBlock y.1 y.2 ∧ posIx y.1 = posIx x.1 ∧ posIx y.2 = posIx x.2) :=
      fun h' => h ⟨h'.2.1, h'.2.2⟩
    have c2 : ¬ (¬ sameBlock x.1 x.2 ∧ posIx x.1 = posIx y.1 ∧ posIx x.2 = posIx y.2) :=
      fun h' => h ⟨h'.2.1.symm, h'.2.2.symm⟩
    rw [if_neg c1, if_neg c2]
    simp

theorem eigenvectorMatrix_add_star {p q : ℕ} (ab cd : PIx p q) :
    eigP ab.1 cd.1 + star (eigP cd.1 ab.1) = if cd = ab then 2 else 0 := by
  by_cases hc : cd = ab
  · subst hc
    rw [if_pos rfl]
    norm_num [eigP]
  · rw [if_neg hc]
    exact eigP_add_star_eigP_eq_zero ab.1 cd.1 ab.2 cd.2 (fun h => hc (Subtype.ext h))

theorem det_eigenvectorMatrix_ne_zero :
    ∀ (p q : ℕ), (Matrix.of fun (cd ab : PIx p q) => eigP ab.1 cd.1).det ≠ 0 := by
  intro p q
  apply det_ne_zero_of_add_conjTranspose
  ext cd ab
  simp only [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  rw [eigenvectorMatrix_add_star]
  split_ifs <;> norm_num

end GlobalTheory.PolarU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetAdSqEigenvectorMatrixUnitPNeZeroStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_adSqEigenvectorMatrix_ne_zero : ∀ (p q : ℕ), (Matrix.of fun (cd ab : PIx p q) => eigP ab.1 cd.1).det ≠ 0 := by
  first | exact @GlobalTheory.PolarU.det_eigenvectorMatrix_ne_zero | exact GlobalTheory.PolarU.det_eigenvectorMatrix_ne_zero | (intros; apply GlobalTheory.PolarU.det_eigenvectorMatrix_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SinhcAdjointApplyMatrixUpperRightBlockElementP
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SinhcAdjointApplyMatrixUpperRightBlockElementP
noncomputable section
namespace GlobalTheory.PolarU.SinhcPres
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

variable {p q : ℕ}

theorem ad_sq_pY (B C : Fin p → Fin q → ℂ) : ∃ D,
    pY B * (pY B * pY C - pY C * pY B) - (pY B * pY C - pY C * pY B) * pY B = pY D := by
  refine ⟨fun i j => (pY B * (pY B * pY C - pY C * pY B) - (pY B * pY C - pY C * pY B) * pY B)
    (Sum.inl i) (Sum.inr j), ?_⟩
  have hh : (pY B * (pY B * pY C - pY C * pY B) - (pY B * pY C - pY C * pY B) * pY B)ᴴ =
      pY B * (pY B * pY C - pY C * pY B) - (pY B * pY C - pY C * pY B) * pY B := by
    simp only [conjTranspose_sub, conjTranspose_mul, pY_conjTranspose]
    noncomm_ring
  ext a b
  rcases a with i | i <;> rcases b with j | j
  · simp [pY, pOf, Matrix.mul_apply, Fintype.sum_sum_type]
  · simp only [pY, pOf, fromBlocks_apply₁₂, of_apply]
  · have := congrFun (congrFun hh (Sum.inr i)) (Sum.inl j)
    rw [← this]
    rfl
  · simp [pY, pOf, Matrix.mul_apply, Fintype.sum_sum_type]

theorem adMat_pow_pY (B C : Fin p → Fin q → ℂ) (k : ℕ) : ∃ D,
    adMat (pY B) ^ (2 * k) *ᵥ vecM (pY C) = vecM (pY D) := by
  induction k with
  | zero => exact ⟨C, by simp⟩
  | succ k ih =>
    obtain ⟨D, hD⟩ := ih
    obtain ⟨E, hE⟩ := ad_sq_pY B D
    refine ⟨E, ?_⟩
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ', pow_succ', ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hD, adMat_mulVec, adMat_mulVec, hE]

theorem summable_sinhc {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    Summable fun k : ℕ => (((2 * k + 1).factorial : ℂ)⁻¹) • A ^ (2 * k) := by
  open scoped Matrix.Norms.Operator in
  refine Summable.of_norm_bounded (g := fun k : ℕ => ‖((k.factorial : ℂ)⁻¹) • (A ^ 2) ^ k‖)
    (NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) (A ^ 2)) fun k => ?_
  rw [norm_smul, norm_smul, ← pow_mul, norm_inv, norm_inv, Complex.norm_natCast,
    Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine inv_anti₀ (by exact_mod_cast k.factorial_pos) ?_
  exact_mod_cast Nat.factorial_le (by omega)

theorem hasSum_sAd (Y V : Mat p q) (a b : Ix p q) :
    HasSum (fun k : ℕ => (((2 * k + 1).factorial : ℂ)⁻¹) * (adMat Y ^ (2 * k) *ᵥ vecM V) (a, b))
      (sAd Y V a b) := by
  have h := (summable_sinhc (adMat Y)).hasSum
  let f : Matrix (Ix p q × Ix p q) (Ix p q × Ix p q) ℂ →+ ℂ :=
    { toFun := fun M => (M *ᵥ vecM V) (a, b)
      map_zero' := by simp
      map_add' := fun M N => by simp [Matrix.add_mulVec] }
  have hf : Continuous f := by
    show Continuous fun M : Matrix (Ix p q × Ix p q) (Ix p q × Ix p q) ℂ => (M *ᵥ vecM V) (a, b)
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have h2 := h.map f hf
  convert (preTransparency := .reducible) h2 using 1
  · funext k
    simp [f, Matrix.smul_mulVec]
  · rfl

theorem sAd_pY : ∀ (p q : ℕ) (B C : Fin p → Fin q → ℂ),
    sAd (pY B) (pY C) = pY (sP (pY B) C) := by
  intro p q B C
  choose D hD using adMat_pow_pY B C
  have h := hasSum_sAd (pY B) (pY C)
  simp only [hD, vecM] at h
  ext a b
  rcases a with i | i <;> rcases b with j | j
  · have := h (Sum.inl i) (Sum.inl j)
    simp only [pY, pOf, fromBlocks_apply₁₁, Matrix.zero_apply, mul_zero] at this ⊢
    exact this.unique hasSum_zero
  · rfl
  · have h1 := h (Sum.inr i) (Sum.inl j)
    have h2 := (h (Sum.inl j) (Sum.inr i)).star
    show _ = star (sAd (pY B) (pY C) (Sum.inl j) (Sum.inr i))
    refine h1.unique ?_
    convert h2 using 2 with k
    simp [pY, pOf]
  · have := h (Sum.inr i) (Sum.inr j)
    simp only [pY, pOf, fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero] at this ⊢
    exact this.unique hasSum_zero

end GlobalTheory.PolarU.SinhcPres
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SinhcAdjointApplyMatrixUpperRightBlockElementPStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sinhcAdjointApplyMatrix_upperRightBlockElementP : ∀ (p q : ℕ) (B C : Fin p → Fin q → ℂ), sAd (pY B) (pY C) = pY (sP (pY B) C) := by
  first | exact @GlobalTheory.PolarU.SinhcPres.sAd_pY | exact GlobalTheory.PolarU.SinhcPres.sAd_pY | (intros; apply GlobalTheory.PolarU.SinhcPres.sAd_pY <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulMinorPoly
open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.JointHarm

namespace GlobalTheory.JointHarm

theorem sum_Ici_sub_succ {n : ℕ} (α : ℕ → ℕ) (hα : Antitone α) (h0 : α n = 0) (a : Fin n) :
    ∑ i ∈ Finset.Ici a, (α (i : ℕ) - α ((i : ℕ) + 1)) = α a := by
  have key : ∀ k, ∑ i ∈ Finset.Ico (a : ℕ) (a + k), (α i - α (i + 1)) + α (a + k) = α a := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← add_assoc, Finset.sum_Ico_succ_top (by omega)]
      have := hα (Nat.le_succ (a + k))
      simp only [Nat.succ_eq_add_one] at this
      omega
  have h1 := key (n - a)
  rw [show (a : ℕ) + (n - a) = n by have := a.2; omega, h0, add_zero] at h1
  rw [← h1]
  refine Finset.sum_bij (fun i _ => (i : ℕ)) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_Ici, Fin.le_def] at hi
    exact Finset.mem_Ico.2 ⟨hi, i.2⟩
  · intro i _ j _ h
    exact Fin.ext h
  · intro b hb
    rw [Finset.mem_Ico] at hb
    exact ⟨⟨b, hb.2⟩, Finset.mem_Ici.2 (Fin.le_def.2 hb.1), rfl⟩
  · intro _ _
    rfl

theorem exists_eq_mul_minorPoly (σ : Type) [DecidableEq σ] (p r : ℕ) (z : Fin p × Fin r → σ)
    (hz : Function.Injective z) (α : ℕ → ℕ) (hα : Antitone α) (h0 : ∀ i, min p r ≤ i → α i = 0)
    (P : MvPolynomial σ ℂ) (hP : BlockHW z α P) :
    ∃ Q : MvPolynomial σ ℂ, (∀ w, z w ∉ Q.vars) ∧ P = Q * minorPoly z α := by
  by_cases hP0 : P = 0
  · exact ⟨0, by simp, by simp [hP0]⟩
  obtain ⟨hru, hcu, hrw, hcw⟩ := hP
  have hrow : ∀ a : Fin p, ∀ m ∈ P.support, ∑ k, m (z (a, k)) = α a := fun a m hm => by
    exact_mod_cast (rowOp_eq_smul_iff z a P _).1 (hrw a) m hm
  have hcol : ∀ k : Fin r, ∀ m ∈ P.support, ∑ a, m (z (a, k)) = α k := fun k m hm => by
    exact_mod_cast (colOp_eq_smul_iff z k P _).1 (hcw k) m hm
  let e : Fin (min p r) → Fin p := Fin.castLE (min_le_left p r)
  let f : Fin (min p r) → Fin r := Fin.castLE (min_le_right p r)
  have hei : Function.Injective e := Fin.castLE_injective _
  have hfi : Function.Injective f := Fin.castLE_injective _
  have hve : ∀ a k, a ∉ Set.range e → z (a, k) ∉ P.vars := by
    intro a k ha hv
    obtain ⟨m, hm, hv⟩ := (mem_vars_iff_mem_support _).1 hv
    have h1 := hrow a m hm
    rw [h0 a (not_lt.1 fun h' => ha ⟨⟨a, h'⟩, rfl⟩), Finset.sum_eq_zero_iff] at h1
    exact Finsupp.mem_support_iff.1 hv (h1 k (Finset.mem_univ _))
  have hvf : ∀ a k, k ∉ Set.range f → z (a, k) ∉ P.vars := by
    intro a k hk hv
    obtain ⟨m, hm, hv⟩ := (mem_vars_iff_mem_support _).1 hv
    have h1 := hcol k m hm
    rw [h0 k (not_lt.1 fun h' => hk ⟨⟨k, h'⟩, rfl⟩), Finset.sum_eq_zero_iff] at h1
    exact Finsupp.mem_support_iff.1 hv (h1 a (Finset.mem_univ _))
  obtain ⟨Q, hQ, hPQ⟩ := eq_mul_prod_minors (fun w : Fin (min p r) × Fin (min p r) =>
      z (e w.1, f w.2)) (hz.comp (hei.prodMap hfi)) P (fun i => α i - α (i + 1))
    (fun a m hm => by
      rw [sum_Ici_sub_succ α hα (h0 _ le_rfl)]
      refine Eq.trans ?_ (hrow (e a) m hm)
      refine Fintype.sum_of_injective f hfi _ _ (fun k hk => ?_) fun _ => rfl
      by_contra h1
      exact hvf _ k hk ((mem_vars_iff_mem_support _).2 ⟨m, hm, Finsupp.mem_support_iff.2 h1⟩))
    (fun i j hij => by
      have h₁ := (rowOp_apply _ _ _ _).symm.trans (hru (e i) (e j) hij)
      refine ((rowAdd_invariant_iff (fun k => z (e i, f k)) (fun k => z (e j, f k))
        (fun k l h => hfi (by simpa using hz h))
        (fun k l h => hij.ne (hei (congrArg Prod.fst (hz h)))) P).out 3 2).1 (Eq.trans ?_ h₁)
      refine Fintype.sum_of_injective f hfi _ _ (fun k hk => ?_) fun _ => rfl
      rw [pderiv_eq_zero_of_notMem_vars (hvf _ k hk), mul_zero])
    (fun i j hij => by
      have h₁ := (colOp_apply _ _ _ _).symm.trans (hcu (f i) (f j) hij)
      refine ((rowAdd_invariant_iff (fun k => z (e k, f i)) (fun k => z (e k, f j))
        (fun k l h => hei (by simpa using hz h))
        (fun k l h => hij.ne (hfi (congrArg Prod.snd (hz h)))) P).out 3 2).1 (Eq.trans ?_ h₁)
      refine Fintype.sum_of_injective e hei _ _ (fun k hk => ?_) fun _ => rfl
      rw [pderiv_eq_zero_of_notMem_vars (hve k _ hk), mul_zero])
  have hPQ' : P = Q * minorPoly z α := hPQ
  refine ⟨Q, ?_, hPQ'⟩
  have hsub : ∀ s ∈ Q.vars, s ∈ P.vars := by
    intro s hs
    rw [mem_vars_iff_degreeOf_ne_zero] at hs ⊢
    rw [hPQ'] at hP0 ⊢
    rw [degreeOf_mul_eq (left_ne_zero_of_mul hP0) (right_ne_zero_of_mul hP0)]
    omega
  rintro ⟨a, k⟩ hw
  by_cases ha : a ∈ Set.range e
  · by_cases hk : k ∈ Set.range f
    · obtain ⟨a, rfl⟩ := ha
      obtain ⟨k, rfl⟩ := hk
      exact hQ (a, k) hw
    · exact hvf a k hk (hsub _ hw)
  · exact hve a k ha (hsub _ hw)

end GlobalTheory.JointHarm
end
