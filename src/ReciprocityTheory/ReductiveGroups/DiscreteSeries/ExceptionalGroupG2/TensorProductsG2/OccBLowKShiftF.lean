module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.ExistsKEquivariantMap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.ContinuousUnitaryMatrix

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.CuspProjectionOrthogonality
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.PosSemidefWeightedInnerNonneg
noncomputable section

open Finset MeasureTheory
open scoped ComplexOrder Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

def ob2TauF (dual : Bool) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ) (k : S7.KG ε)
    (ξ : Fin n → T.V) : Fin n → T.V :=
  fun c => ∑ d, (cond dual (star (S7.toMK k c d)) (S7.toMK k c d)) • T.op k (ξ d)

def ob2PsiCoef (dual : Bool) {ε : Fin n → Bool} {Λ : Fin n → ℝ} {T : S7.KType ε Λ}
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (ξ ζ : Fin n → T.V) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ c, inner ℂ (ξ c) (∑ d, (cond dual ((g⁻¹) d c) (g c d)) • Ψ g (ζ d))

def ob2SI {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ξ η : Fin n → V) : ℂ :=
  ∑ c, inner ℂ (ξ c) (η c)

theorem onb_sum_inner_independent {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℂ E) (c : OrthonormalBasis κ ℂ E) (F G : E →ₗ[ℂ] V) :
    ∑ j, inner ℂ (F (b j)) (G (b j)) = ∑ i, inner ℂ (F (c i)) (G (c i)) := by
  calc ∑ j, inner ℂ (F (b j)) (G (b j))
      = ∑ j, ∑ i, inner ℂ (c i) (b j) * inner ℂ (F (b j)) (G (c i)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have e : G (b j) = ∑ i, inner ℂ (c i) (b j) • G (c i) := by
          conv_lhs => rw [← c.sum_repr' (b j)]
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, map_smul]
        rw [e, inner_sum]
        simp only [inner_smul_right]
    _ = ∑ i, ∑ j, inner ℂ (c i) (b j) * inner ℂ (F (b j)) (G (c i)) := Finset.sum_comm
    _ = ∑ i, inner ℂ (F (c i)) (G (c i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have e : F (c i) = ∑ j, inner ℂ (b j) (c i) • F (b j) := by
          conv_lhs => rw [← b.sum_repr' (c i)]
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, map_smul]
        rw [e, sum_inner]
        simp only [inner_smul_left, inner_conj_symm]

theorem onb_sum_vector_inner_independent {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℂ E) (c : OrthonormalBasis κ ℂ E) (F G : E →ₗ[ℂ] (Fin n → V)) :
    ∑ j, ob2SI (F (b j)) (G (b j)) = ∑ i, ob2SI (F (c i)) (G (c i)) := by
  unfold ob2SI
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ =>
    onb_sum_inner_independent b c ((LinearMap.proj d).comp F) ((LinearMap.proj d).comp G)

theorem onb_expand_vector_inner {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ E) (ι₀ : E →ₗ[ℂ] (Fin n → V)) (z : Fin n → V) (y : E) :
    ∑ i, starRingEnd ℂ (ob2SI (ι₀ (b i)) z) * inner ℂ (b i) y = ob2SI z (ι₀ y) := by
  conv_rhs => rw [← b.sum_repr' y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ob2SI, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, inner_sum, inner_smul_right,
    inner_conj_symm, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => by ring

theorem k_type_op_inner_preserved {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ) (k : S7.KG ε) (x y : T.V) :
    inner ℂ (T.op k x) (T.op k y) = inner ℂ x y :=
  ContinuousLinearMap.inner_map_map_of_mem_unitary (T.τ k).2 x y

theorem k_matrix_conjTranspose_mul_self {ε : Fin n → Bool} (k : S7.KG ε) :
    (S7.toMK k)ᴴ * S7.toMK k = 1 := by
  have hk : S7.toMK k ∈ Kset ε := k.2
  have := (Matrix.mem_unitaryGroup_iff').1 hk.1
  simpa [Matrix.star_eq_conjTranspose] using this

theorem k_matrix_columns_orthonormal {ε : Fin n → Bool} (k : S7.KG ε) (e f : Fin n) :
    ∑ c, star (S7.toMK k c e) * S7.toMK k c f = if e = f then 1 else 0 := by
  have := congrFun (congrFun (k_matrix_conjTranspose_mul_self k) e) f
  simpa [Matrix.mul_apply, Matrix.one_apply] using this

theorem k_twist_vector_inner_preserved (dual : Bool) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ) (k : S7.KG ε)
    (ξ η : Fin n → T.V) : ob2SI (ob2TauF dual T k ξ) (ob2TauF dual T k η) = ob2SI ξ η := by
  have hc : ∀ e f, ∑ c, starRingEnd ℂ (cond dual (star (S7.toMK k c e)) (S7.toMK k c e)) *
      cond dual (star (S7.toMK k c f)) (S7.toMK k c f) = if e = f then 1 else 0 := by
    intro e f
    cases dual
    · simpa using k_matrix_columns_orthonormal k e f
    · have h := congrArg star (k_matrix_columns_orthonormal k e f)
      simp only [star_sum, star_mul, star_star] at h
      simp only [cond_true, Complex.star_def, Complex.conj_conj] at h ⊢
      conv_lhs => arg 2; ext c; rw [mul_comm]
      rw [h]
      split_ifs <;> simp
  unfold ob2SI ob2TauF
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, k_type_op_inner_preserved]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h1 : ∀ e', ∑ c, cond dual (star (S7.toMK k c e)) (S7.toMK k c e) *
      ((starRingEnd ℂ) (cond dual (star (S7.toMK k c e')) (S7.toMK k c e')) * inner ℂ (ξ e') (η e)) =
      (if e' = e then 1 else 0) * inner ℂ (ξ e') (η e) := fun e' => by
    rw [← hc e' e, Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [Finset.sum_congr rfl fun e' _ => h1 e']
  simp

def ob2B (dual : Bool) {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (g : Matrix (Fin n) (Fin n) ℂ) :
    (Fin n → V) →ₗ[ℂ] (Fin n → V) where
  toFun ζ c := ∑ d, oa1Phi dual g c d • Ψ g (ζ d)
  map_add' ζ ζ' := by funext c; simp [smul_add, Finset.sum_add_distrib]
  map_smul' a ζ := by funext c; simp [Finset.smul_sum, smul_comm a]

theorem psi_coef_eq_inner_twist (dual : Bool) {ε : Fin n → Bool} {Λ : Fin n → ℝ} {T : S7.KType ε Λ}
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (ξ ζ : Fin n → T.V) (g : Matrix (Fin n) (Fin n) ℂ) :
    ob2PsiCoef dual Ψ ξ ζ g = ob2SI ξ (ob2B dual Ψ g ζ) := rfl

theorem tensor_phi_k_mul (dual : Bool) {ε : Fin n → Bool} (k : S7.KG ε) (E : Matrix (Fin n) (Fin n) ℂ)
    (c d : Fin n) :
    oa1Phi dual (S7.toMK k * E) c d =
      ∑ e, cond dual (star (S7.toMK k c e)) (S7.toMK k c e) * oa1Phi dual E e d := by
  cases dual
  · simp [oa1Phi, Matrix.mul_apply]
  · have hki : (S7.toMK k)⁻¹ = (S7.toMK k)ᴴ := Matrix.inv_eq_left_inv (k_matrix_conjTranspose_mul_self k)
    simp only [oa1Phi, cond_true, Matrix.mul_inv_rev, hki, Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _

theorem psi_twist_k_mul (dual : Bool) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ)
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (k : S7.KG ε) (E : Matrix (Fin n) (Fin n) ℂ)
    (hΨ : Ψ (S7.toMK k * E) = T.op k * Ψ E) (ζ : Fin n → T.V) :
    ob2B dual Ψ (S7.toMK k * E) ζ = ob2TauF dual T k (ob2B dual Ψ E ζ) := by
  funext c
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ob2B, LinearMap.coe_mk, AddHom.coe_mk, ob2TauF, hΨ, tensor_phi_k_mul, ContinuousLinearMap.mul_apply,
    map_sum, map_smul, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

open scoped MatrixOrder in
theorem posSemidef_weighted_inner_nonneg {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosSemidef) {R : V →L[ℂ] V} (hR : R.IsPositive)
    (u : Fin n → V) : 0 ≤ ∑ c, ∑ d, M c d * inner ℂ (u c) (R (u d)) := by
  obtain ⟨S, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  have e : ∑ c, ∑ d, (star S * S) c d * inner ℂ (u c) (R (u d)) =
      ∑ e, inner ℂ (∑ c, S e c • u c) (R (∑ d, S e d • u d)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.star_apply, map_sum, map_smul, sum_inner, inner_sum, inner_smul_left,
      inner_smul_right, Finset.sum_mul, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
    simp only [Complex.star_def]
    ring
  rw [e]
  exact Finset.sum_nonneg fun e _ => hR.inner_nonneg_right _

theorem vector_inner_smul_right {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ξ η : Fin n → V) (a : ℂ) :
    ob2SI ξ (a • η) = a * ob2SI ξ η := by
  simp [ob2SI, Finset.mul_sum]

theorem psi_pairing_eq_inner (dual : Bool) {ε : Fin n → Bool} {Λ Λ' : Fin n → ℝ} {T : S7.KType ε Λ} {T' : S7.KType ε Λ'}
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V))
    (ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V)) (g : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, ∑ j, starRingEnd ℂ (ob2PsiCoef dual Ψ (ι₀ (stdOrthonormalBasis ℂ T'.V i))
        (ι₀ (stdOrthonormalBasis ℂ T'.V j)) g) *
      inner ℂ (stdOrthonormalBasis ℂ T'.V i) (Ψ' g (stdOrthonormalBasis ℂ T'.V j))) =
    ∑ j, ob2SI (ob2B dual Ψ g (ι₀ (stdOrthonormalBasis ℂ T'.V j)))
      (ι₀ (Ψ' g (stdOrthonormalBasis ℂ T'.V j))) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [psi_coef_eq_inner_twist]
  exact onb_expand_vector_inner _ ι₀ _ _

theorem psi_twist_exp_positive (dual : Bool) {ε : Fin n → Bool} {Λ : Fin n → ℝ} {T : S7.KType ε Λ}
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inP ε Y)
    (hR : (Ψ (NormedSpace.exp Y)).IsPositive) (u : Fin n → T.V) :
    0 ≤ ob2SI (ob2B dual Ψ (NormedSpace.exp Y) u) u := by
  set E := NormedSpace.exp Y with hEdef
  have hE : E.PosDef := S7.exp_noncompactPart_posDef hY
  set M : Matrix (Fin n) (Fin n) ℂ := cond dual (E⁻¹)ᵀ E with hMdef
  have hM : M.PosSemidef := by
    cases dual
    · exact hE.posSemidef
    · exact hE.inv.transpose.posSemidef
  have hφ : ∀ c d, oa1Phi dual E c d = M c d := by
    intro c d; cases dual <;> rfl
  have h0 := posSemidef_weighted_inner_nonneg hM hR u
  have e : ob2SI (ob2B dual Ψ E u) u = star (∑ c, ∑ d, M c d * inner ℂ (u c) (Ψ E (u d))) := by
    simp only [ob2SI, ob2B, LinearMap.coe_mk, AddHom.coe_mk, hφ, sum_inner, inner_smul_left, star_sum, star_mul',
      Complex.star_def, inner_conj_symm]
  rw [e]
  exact star_nonneg_iff.mpr h0

theorem k_matrix_of_one {ε : Fin n → Bool} : S7.toMK (1 : S7.KG ε) = 1 := rfl

theorem k_type_op_one {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ) : T.op 1 = 1 := by
  simp [S7.KType.op]

theorem psi_pairing_nonneg (dual : Bool) {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {T' : S7.KType ε (lowK ε lam')}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}
    (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ')
    (hpos : ∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive)
    (hpos' : ∀ X, inP ε X → (Ψ' (NormedSpace.exp X)).IsPositive)
    (ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V))
    (hK : ∀ (k : S7.KG ε) (v : T'.V), ι₀ (T'.op k v) = ob2TauF dual T k (ι₀ v))
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    0 ≤ ∑ i, ∑ j, starRingEnd ℂ (ob2PsiCoef dual Ψ (ι₀ (stdOrthonormalBasis ℂ T'.V i))
        (ι₀ (stdOrthonormalBasis ℂ T'.V j)) g) *
      inner ℂ (stdOrthonormalBasis ℂ T'.V i) (Ψ' g (stdOrthonormalBasis ℂ T'.V j)) := by
  rw [psi_pairing_eq_inner]
  obtain ⟨k0, hk0, Y, hY, rfl⟩ := polar_UJ (show g ∈ UJset ε from hg)
  obtain ⟨k, rfl⟩ := ffa_Kset hk0
  have hE : inUJ ε (NormedSpace.exp Y) := by
    have h1 : NormedSpace.exp Y ∈ UJset ε := by simpa using exp_smul_mem_UJset hY.1 1
    exact h1
  have hΨ : Ψ (S7.toMK k * NormedSpace.exp Y) = T.op k * Ψ (NormedSpace.exp Y) := by
    have := hP.1 k 1 _ hE
    rwa [k_matrix_of_one, Matrix.mul_one, k_type_op_one, mul_one] at this
  have hΨ' : Ψ' (S7.toMK k * NormedSpace.exp Y) = T'.op k * Ψ' (NormedSpace.exp Y) := by
    have := hP'.1 k 1 _ hE
    rwa [k_matrix_of_one, Matrix.mul_one, k_type_op_one, mul_one] at this
  set b := stdOrthonormalBasis ℂ T'.V
  set E := NormedSpace.exp Y
  have step : ∀ j, ob2SI (ob2B dual Ψ (S7.toMK k * E) (ι₀ (b j))) (ι₀ (Ψ' (S7.toMK k * E) (b j))) =
      ob2SI (ob2B dual Ψ E (ι₀ (b j))) (ι₀ (Ψ' E (b j))) := by
    intro j
    rw [psi_twist_k_mul dual T Ψ k E hΨ, hΨ', ContinuousLinearMap.mul_apply, hK, k_twist_vector_inner_preserved]
  rw [Finset.sum_congr rfl fun j _ => step j]
  have hQ := (hpos' Y hY).toLinearMap
  have hs := hQ.isSymmetric
  set c := hs.eigenvectorBasis rfl
  have h := onb_sum_vector_inner_independent b c ((ob2B dual Ψ E).comp ι₀) (ι₀.comp (Ψ' E : T'.V →ₗ[ℂ] T'.V))
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe] at h
  rw [h]
  refine Finset.sum_nonneg fun i _ => ?_
  have hc := hs.apply_eigenvectorBasis rfl i
  simp only [ContinuousLinearMap.coe_coe] at hc
  rw [hc, map_smul, vector_inner_smul_right]
  exact mul_nonneg (Complex.zero_le_real.mpr (hQ.nonneg_eigenvalues rfl i)) (psi_twist_exp_positive dual Ψ hY (hpos Y hY) _)

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

noncomputable section

open Finset MeasureTheory
open scoped ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

theorem psi_coef_expand (dual : Bool) {ε : Fin n → Bool} {Λ : Fin n → ℝ} {T : S7.KType ε Λ}
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (ξ ζ : Fin n → T.V) (g : Matrix (Fin n) (Fin n) ℂ) :
    ob2PsiCoef dual Ψ ξ ζ g = ∑ c, ∑ d, oa1Phi dual g c d * inner ℂ (ξ c) (Ψ g (ζ d)) := by
  simp only [ob2PsiCoef, inner_sum, inner_smul_right, oa1Phi]

section Psi

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}

theorem continuous_spherical_psi (hP : IsPsiFor ε lam T Ψ) :
    Continuous (fun g : Formalism.REAL.UJ ε => Ψ (Formalism.MainNotions.S.umat g)) :=
  (ffa_continuousOn hP.2.2.1).comp_continuous continuous_umat' (fun g => g.2)

theorem psi_twist_coef_memLp (dual : Bool) (hP : IsPsiFor ε lam T Ψ)
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε)) (ξ ζ : Fin n → T.V) :
    MemLp (fun g : Formalism.REAL.UJ ε => ob2PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
  simp_rw [psi_coef_expand]
  refine memLp_finsetSum _ fun c _ => memLp_finsetSum _ fun d _ => ?_
  refine (hWT (ζ d) (ξ c)).of_le ?_ (Filter.Eventually.of_forall fun g => ?_)
  · exact ((continuous_tensor_phi dual c d).mul (continuous_const.inner
      ((continuous_spherical_psi hP).clm_apply continuous_const))).aestronglyMeasurable
  · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_right (norm_tensor_phi_le_sqrt_hs g.2 dual c d) (norm_nonneg _)

theorem psi_term_integrable (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ')
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε)) (ξ ζ : Fin n → T.V) (u v : T'.V) :
    Integrable (fun g : Formalism.REAL.UJ ε => starRingEnd ℂ (ob2PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) *
      inner ℂ u (Ψ' (Formalism.MainNotions.S.umat g) v)) (Formalism.REAL.muG ε) := by
  have h1 := (psi_twist_coef_memLp dual hP hWT ξ ζ).star
  have h2 : MemLp (fun g : Formalism.REAL.UJ ε => inner ℂ u (Ψ' (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε) :=
    memLp_muG_of_haar ε (fun x => inner ℂ u (Ψ' x v)) 2
      (fun μ hμ => (pdA_coef u v).comp_memLp' (hP'.2.2.2.2 μ hμ))
  exact h1.integrable_mul h2

end Psi

theorem psi_twist_at_one (dual : Bool) {ε : Fin n → Bool} {Λ : Fin n → ℝ} {T : S7.KType ε Λ}
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (hΨ : Ψ 1 = 1) (u : Fin n → T.V) :
    ob2B dual Ψ 1 u = u := by
  funext c
  have hφ : ∀ d, oa1Phi dual 1 c d = if c = d then 1 else 0 := by
    intro d
    cases dual
    · simp [oa1Phi, Matrix.one_apply]
    · simp [oa1Phi, Matrix.one_apply, eq_comm]
  simp [ob2B, hφ, hΨ, ite_smul]

section Main

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}

def ob2Fij (dual : Bool) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V))
    (Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)) (ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V))
    (i j : Fin (Module.finrank ℂ T'.V)) (g : Formalism.REAL.UJ ε) : ℂ :=
  starRingEnd ℂ (ob2PsiCoef dual Ψ (ι₀ (stdOrthonormalBasis ℂ T'.V i)) (ι₀ (stdOrthonormalBasis ℂ T'.V j))
    (Formalism.MainNotions.S.umat g)) *
  inner ℂ (stdOrthonormalBasis ℂ T'.V i) (Ψ' (Formalism.MainNotions.S.umat g) (stdOrthonormalBasis ℂ T'.V j))

theorem psi_pairing_at_one_re_pos (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ')
    (ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V)) (hι₀ : ι₀ ≠ 0) :
    0 < (∑ i, ∑ j, ob2Fij (ε := ε) dual Ψ Ψ' ι₀ i j 1).re := by
  set b := stdOrthonormalBasis ℂ T'.V
  have e : (∑ i, ∑ j, ob2Fij (ε := ε) dual Ψ Ψ' ι₀ i j 1) =
      ∑ j, ob2SI (ob2B dual Ψ 1 (ι₀ (b j))) (ι₀ (Ψ' 1 (b j))) :=
    psi_pairing_eq_inner dual Ψ Ψ' ι₀ (1 : Matrix (Fin n) (Fin n) ℂ)
  rw [e]
  simp only [psi_twist_at_one dual Ψ hP.2.1, hP'.2.1, ContinuousLinearMap.one_apply]
  obtain ⟨j, hj⟩ : ∃ j, ι₀ (b j) ≠ 0 := by
    by_contra h
    push Not at h
    exact hι₀ (b.toBasis.ext fun j => by simpa using h j)
  obtain ⟨c, hc⟩ := Function.ne_iff.mp hj
  have key : ∀ x : T.V, (inner ℂ x x).re = ‖x‖ ^ 2 := fun x => inner_self_eq_norm_sq (𝕜 := ℂ) x
  simp only [ob2SI, Complex.re_sum, key]
  have hc' : ι₀ (b j) c ≠ 0 := by simpa using hc
  exact Finset.sum_pos' (fun j _ => Finset.sum_nonneg fun c _ => by positivity)
    ⟨j, Finset.mem_univ _, Finset.sum_pos' (fun c _ => by positivity)
      ⟨c, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hc') 2⟩⟩

theorem continuous_psi_pairing_sum (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ')
    (ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V)) :
    Continuous (fun g : Formalism.REAL.UJ ε => ∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g) := by
  have h1 := continuous_spherical_psi hP
  have h2 := continuous_spherical_psi hP'
  have h3 := continuous_tensor_phi (ε := ε) dual
  simp only [ob2Fij, psi_coef_expand]
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (Complex.continuous_conj.comp (continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun d _ =>
      (h3 c d).mul (continuous_const.inner (h1.clm_apply continuous_const)))).mul
      (continuous_const.inner (h2.clm_apply continuous_const))

theorem psi_pairing_trace_pos (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ')
    (hpos : ∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive)
    (hpos' : ∀ X, inP ε X → (Ψ' (NormedSpace.exp X)).IsPositive)
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε))
    (ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V)) (hι₀ : ι₀ ≠ 0)
    (hK : ∀ (k : S7.KG ε) (v : T'.V), ι₀ (T'.op k v) = ob2TauF dual T k (ι₀ v)) :
    0 < (∑ i, ∑ j, ∫ g : Formalism.REAL.UJ ε,
      starRingEnd ℂ (ob2PsiCoef dual Ψ (ι₀ (stdOrthonormalBasis ℂ T'.V i)) (ι₀ (stdOrthonormalBasis ℂ T'.V j))
        (Formalism.MainNotions.S.umat g)) *
      inner ℂ (stdOrthonormalBasis ℂ T'.V i) (Ψ' (Formalism.MainNotions.S.umat g) (stdOrthonormalBasis ℂ T'.V j))
        ∂(Formalism.REAL.muG ε)).re := by
  show 0 < (∑ i, ∑ j, ∫ g, ob2Fij dual Ψ Ψ' ι₀ i j g ∂(Formalism.REAL.muG ε)).re
  have hint : ∀ i j, Integrable (ob2Fij dual Ψ Ψ' ι₀ i j) (Formalism.REAL.muG ε) := fun i j =>
    psi_term_integrable dual hP hP' hWT _ _ _ _
  have hFi : Integrable (fun g => ∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g) (Formalism.REAL.muG ε) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j
  have hsum : ∫ g, (∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g) ∂(Formalism.REAL.muG ε) =
      ∑ i, ∑ j, ∫ g, ob2Fij dual Ψ Ψ' ι₀ i j g ∂(Formalism.REAL.muG ε) := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hint i j
  rw [← hsum]
  have hre : (∫ g, (∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g) ∂(Formalism.REAL.muG ε)).re =
      ∫ g, (∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g).re ∂(Formalism.REAL.muG ε) :=
    (integral_re hFi).symm
  rw [hre]
  have hG0 : 0 ≤ fun g : Formalism.REAL.UJ ε => (∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g).re := by
    intro g
    have h := psi_pairing_nonneg dual hP hP' hpos hpos' ι₀ hK (g := Formalism.MainNotions.S.umat g) g.2
    have h' := (Complex.le_def.mp h).1
    rw [Complex.zero_re] at h'
    exact h'
  have hGc : Continuous fun g : Formalism.REAL.UJ ε => (∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g).re :=
    Complex.continuous_re.comp (continuous_psi_pairing_sum dual hP hP' ι₀)
  rw [integral_pos_iff_support_of_nonneg hG0 hFi.re]
  exact hGc.isOpen_support.measure_pos _ ⟨1, Function.mem_support.mpr (psi_pairing_at_one_re_pos dual hP hP' ι₀ hι₀).ne'⟩

end Main

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.AestronglyMeasurablePsiInner
noncomputable section

open Finset MeasureTheory
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

def ob3PsiCoef (dual : Bool) {ε : Fin n → Bool} {Λ : Fin n → ℝ} {T : S7.KType ε Λ}
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (ξ ζ : Fin n → T.V) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ c, inner ℂ (ξ c) (∑ d, (cond dual ((g⁻¹) d c) (g c d)) • Ψ g (ζ d))

section Psi

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}

theorem psi_weighted_memLp {v₀ : T.V} (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    (v w : T.V) :
    MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε) := by
  have hC : ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have h := datumEmbedding_highest_ne_zero hgap hP hv₀
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.2 h)
  have hmem : ∀ u, (⟨uniformisationL2 ε Ψ v₀ u, datumEmbedding_mem_smooth hP v₀ u⟩ : smD ε (rreg ε)) ∈
      genSub (smE ε (rreg ε)) (datumV ε Ψ v₀) := fun u =>
    Submodule.mem_sInf.2 (fun S hS => hS.1 (Submodule.mem_comap.2 (Submodule.subset_span ⟨u, rfl⟩)))
  have h := (hW _ (hmem v) _ (hmem w)).const_mul (((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ)⁻¹)
  refine h.congr_norm ?_ (Filter.Eventually.of_forall fun g => ?_)
  · exact h.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun g => by
      simp only
      rw [formulaF hgap hP hv₀ (g := Formalism.MainNotions.S.umat g) g.2 v w]
      field_simp)
  · simp only
    rw [formulaF hgap hP hv₀ (g := Formalism.MainNotions.S.umat g) g.2 v w]
    congr 1
    field_simp

end Psi

theorem norm_unitary_inv_entry {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (c d : Fin n) :
    ‖(Formalism.MainNotions.S.umat g)⁻¹ d c‖ = ‖Formalism.MainNotions.S.umat g c d‖ := by
  have hg : inUJ ε (Formalism.MainNotions.S.umat g) := g.2
  have h1 : (Jm ε * (Formalism.MainNotions.S.umat g)ᴴ * Jm ε) * Formalism.MainNotions.S.umat g = 1 := by
    calc (Jm ε * (Formalism.MainNotions.S.umat g)ᴴ * Jm ε) * Formalism.MainNotions.S.umat g
        = Jm ε * ((Formalism.MainNotions.S.umat g)ᴴ * Jm ε * Formalism.MainNotions.S.umat g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, S7.Jm_mul_self]
  rw [Matrix.inv_eq_left_inv h1]
  simp only [Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  split_ifs <;> simp

theorem norm_unitary_entry_le_sqrt_hs {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (c d : Fin n) :
    ‖Formalism.MainNotions.S.umat g c d‖ ≤ Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) := by
  rw [← Real.sqrt_sq (norm_nonneg (Formalism.MainNotions.S.umat g c d))]
  apply Real.sqrt_le_sqrt
  unfold S7.hs
  calc ‖Formalism.MainNotions.S.umat g c d‖ ^ 2 ≤ ∑ j, ‖Formalism.MainNotions.S.umat g c j‖ ^ 2 :=
        Finset.single_le_sum (f := fun j => ‖Formalism.MainNotions.S.umat g c j‖ ^ 2) (fun j _ => sq_nonneg _) (mem_univ d)
    _ ≤ ∑ i, ∑ j, ‖Formalism.MainNotions.S.umat g i j‖ ^ 2 :=
        Finset.single_le_sum (f := fun i => ∑ j, ‖Formalism.MainNotions.S.umat g i j‖ ^ 2)
          (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (mem_univ c)

theorem norm_dual_entry_le_sqrt_hs (dual : Bool) {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (c d : Fin n) :
    ‖cond dual ((Formalism.MainNotions.S.umat g)⁻¹ d c) (Formalism.MainNotions.S.umat g c d)‖ ≤ Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) := by
  cases dual
  · exact norm_unitary_entry_le_sqrt_hs g c d
  · simp only [cond]; rw [norm_unitary_inv_entry]; exact norm_unitary_entry_le_sqrt_hs g c d

theorem continuous_dual_entry (dual : Bool) {ε : Fin n → Bool} (c d : Fin n) :
    Continuous (fun g : Formalism.REAL.UJ ε => cond dual ((Formalism.MainNotions.S.umat g)⁻¹ d c) (Formalism.MainNotions.S.umat g c d)) := by
  cases dual
  · exact (continuous_apply d).comp ((continuous_apply c).comp ((Units.continuous_val (M := Matrix (Fin n) (Fin n) ℂ)).comp continuous_subtype_val))
  · have e : (fun g : Formalism.REAL.UJ ε => cond true ((Formalism.MainNotions.S.umat g)⁻¹ d c) (Formalism.MainNotions.S.umat g c d)) =
        fun g : Formalism.REAL.UJ ε => ((((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
          Matrix (Fin n) (Fin n) ℂ) d c) := by
      funext g
      simp only [cond, Formalism.MainNotions.S.umat, Matrix.coe_units_inv]
    rw [e]
    exact (continuous_apply c).comp ((continuous_apply d).comp ((Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) ℂ)).comp continuous_subtype_val))

section Psi2

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}

theorem aestronglyMeasurable_psi_inner (hP : IsPsiFor ε lam T Ψ) (x y : T.V) :
    AEStronglyMeasurable (fun g : Formalism.REAL.UJ ε => inner ℂ x (Ψ (Formalism.MainNotions.S.umat g) y)) (Formalism.REAL.muG ε) := by
  have hΨm : AEStronglyMeasurable (fun g : Formalism.REAL.UJ ε => Ψ (Formalism.MainNotions.S.umat g)) (Formalism.REAL.muG ε) :=
    (hP.2.2.2.2 (Formalism.REAL.muG ε) (Formalism.REAL.instIsHaarMuG n ε)).aestronglyMeasurable
  exact (continuous_const.inner (continuous_id.clm_apply continuous_const)).comp_aestronglyMeasurable hΨm

theorem psi_inner_memLp (hP : IsPsiFor ε lam T Ψ) (x y : T.V) :
    MemLp (fun g : Formalism.REAL.UJ ε => inner ℂ x (Ψ (Formalism.MainNotions.S.umat g) y)) 2 (Formalism.REAL.muG ε) := by
  have hΨ : MemLp (fun g : Formalism.REAL.UJ ε => Ψ (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) :=
    hP.2.2.2.2 (Formalism.REAL.muG ε) (Formalism.REAL.instIsHaarMuG n ε)
  refine hΨ.of_le_mul (c := ‖x‖ * ‖y‖) (aestronglyMeasurable_psi_inner hP x y) (Filter.Eventually.of_forall fun g => ?_)
  calc ‖inner ℂ x (Ψ (Formalism.MainNotions.S.umat g) y)‖ ≤ ‖x‖ * ‖Ψ (Formalism.MainNotions.S.umat g) y‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖Ψ (Formalism.MainNotions.S.umat g)‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = ‖x‖ * ‖y‖ * ‖Ψ (Formalism.MainNotions.S.umat g)‖ := by ring

theorem psi_coef_memLp_of_weighted (dual : Bool) (hP : IsPsiFor ε lam T Ψ)
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε)) (ξ ζ : Fin n → T.V) :
    MemLp (fun g : Formalism.REAL.UJ ε => ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
  have e : (fun g : Formalism.REAL.UJ ε => ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) = fun g => ∑ c, ∑ d,
      cond dual ((Formalism.MainNotions.S.umat g)⁻¹ d c) (Formalism.MainNotions.S.umat g c d) *
        inner ℂ (ξ c) (Ψ (Formalism.MainNotions.S.umat g) (ζ d)) := by
    funext g
    simp only [ob3PsiCoef, inner_sum, inner_smul_right]
  rw [e]
  refine memLp_finsetSum _ fun c _ => memLp_finsetSum _ fun d _ => ?_
  refine (hWT (ζ d) (ξ c)).of_le (((continuous_dual_entry dual c d).aestronglyMeasurable).mul (aestronglyMeasurable_psi_inner hP _ _))
    (Filter.Eventually.of_forall fun g => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_right (norm_dual_entry_le_sqrt_hs dual g c d) (norm_nonneg _)

theorem psi_pairing_integrable (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ')
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε)) (ξ ζ : Fin n → T.V) (u' v' : T'.V) :
    Integrable (fun g : Formalism.REAL.UJ ε => starRingEnd ℂ (ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) *
      inner ℂ u' (Ψ' (Formalism.MainNotions.S.umat g) v')) (Formalism.REAL.muG ε) :=
  (psi_coef_memLp_of_weighted dual hP hWT ξ ζ).star.integrable_mul (psi_inner_memLp hP' u' v')

end Psi2

theorem clm_mul_apply_eq_comp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (A B : E →L[ℂ] E) (x : E) :
    (A * B) x = A (B x) := rfl

theorem dual_entry_mul_sum (dual : Bool) (K H : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) :
    cond dual ((K * H)⁻¹ d c) ((K * H) c d) =
      ∑ e, cond dual (K⁻¹ e c) (K c e) * cond dual (H⁻¹ d e) (H e d) := by
  cases dual
  · simp only [cond, Matrix.mul_apply]
  · simp only [cond, Matrix.mul_inv_rev, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _

section Psi3

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}

theorem psi_k_left_equivariant {Λ : Fin n → ℝ} {T : S7.KType ε Λ} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
    (hK : ∀ (k₁ k₂ : S7.KG ε) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Ψ (S7.toMK k₁ * g * S7.toMK k₂) = T.op k₁ * Ψ g * T.op k₂) (k : S7.KG ε) (h : Formalism.REAL.UJ ε) :
    Ψ (S7.toMK k * Formalism.MainNotions.S.umat h) = T.op k * Ψ (Formalism.MainNotions.S.umat h) := by
  have e := hK k 1 (Formalism.MainNotions.S.umat h) h.2
  have h1 : S7.toMK (1 : S7.KG ε) = 1 := rfl
  have h2 : T.op 1 = 1 := by simp [S7.KType.op]
  rwa [h1, mul_one, h2, mul_one] at e

theorem psi_coef_k_left_translate (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (k : S7.KG ε) (h : Formalism.REAL.UJ ε)
    (ξ ζ : Fin n → T.V) :
    ob3PsiCoef dual Ψ ξ ζ (S7.toMK k * Formalism.MainNotions.S.umat h) =
      ob3PsiCoef dual Ψ (fun e => ∑ c, starRingEnd ℂ (cond dual ((S7.toMK k)⁻¹ e c) (S7.toMK k c e)) •
        (ContinuousLinearMap.adjoint (T.op k)) (ξ c)) ζ (Formalism.MainNotions.S.umat h) := by
  have hΨ := psi_k_left_equivariant hP.1 k h
  have hL : ob3PsiCoef dual Ψ ξ ζ (S7.toMK k * Formalism.MainNotions.S.umat h) = ∑ c, ∑ d, ∑ e,
      cond dual ((S7.toMK k)⁻¹ e c) (S7.toMK k c e) *
        cond dual ((Formalism.MainNotions.S.umat h)⁻¹ d e) (Formalism.MainNotions.S.umat h e d) *
          inner ℂ (ξ c) (T.op k (Ψ (Formalism.MainNotions.S.umat h) (ζ d))) := by
    simp only [ob3PsiCoef, hΨ, dual_entry_mul_sum, clm_mul_apply_eq_comp, inner_sum, inner_smul_right,
      Finset.sum_mul]
  have hR : ob3PsiCoef dual Ψ (fun e => ∑ c, starRingEnd ℂ (cond dual ((S7.toMK k)⁻¹ e c) (S7.toMK k c e)) •
        (ContinuousLinearMap.adjoint (T.op k)) (ξ c)) ζ (Formalism.MainNotions.S.umat h) = ∑ e, ∑ d, ∑ c,
      cond dual ((S7.toMK k)⁻¹ e c) (S7.toMK k c e) *
        cond dual ((Formalism.MainNotions.S.umat h)⁻¹ d e) (Formalism.MainNotions.S.umat h e d) *
          inner ℂ (ξ c) (T.op k (Ψ (Formalism.MainNotions.S.umat h) (ζ d))) := by
    simp only [ob3PsiCoef, inner_sum, inner_smul_right, sum_inner, inner_smul_left,
      ContinuousLinearMap.adjoint_inner_left, RCLike.conj_conj, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => by ring
  rw [hL, hR]
  calc _ = ∑ c, ∑ e, ∑ d, cond dual ((S7.toMK k)⁻¹ e c) (S7.toMK k c e) *
        cond dual ((Formalism.MainNotions.S.umat h)⁻¹ d e) (Formalism.MainNotions.S.umat h e d) *
          inner ℂ (ξ c) (T.op k (Ψ (Formalism.MainNotions.S.umat h) (ζ d))) :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = _ := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun e _ => Finset.sum_comm

theorem psi_pairing_vanishing_spread (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ') {v₀' : T'.V} (hv₀' : v₀' ≠ 0)
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε))
    (h0 : ∀ (ξ ζ : Fin n → T.V) (v' : T'.V), ∫ g : Formalism.REAL.UJ ε,
      starRingEnd ℂ (ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) * inner ℂ v₀' (Ψ' (Formalism.MainNotions.S.umat g) v')
        ∂(Formalism.REAL.muG ε) = 0) :
    ∀ (ξ ζ : Fin n → T.V) (u' v' : T'.V), ∫ g : Formalism.REAL.UJ ε,
      starRingEnd ℂ (ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) * inner ℂ u' (Ψ' (Formalism.MainNotions.S.umat g) v')
        ∂(Formalism.REAL.muG ε) = 0 := by
  let W : Submodule ℂ T'.V :=
    { carrier := {u' | ∀ (ξ ζ : Fin n → T.V) (v' : T'.V), ∫ g : Formalism.REAL.UJ ε,
        starRingEnd ℂ (ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) * inner ℂ u' (Ψ' (Formalism.MainNotions.S.umat g) v')
          ∂(Formalism.REAL.muG ε) = 0}
      add_mem' := fun {a b} ha hb ξ ζ v' => by
        simp only [inner_add_left, mul_add]
        rw [integral_add (psi_pairing_integrable dual hP hP' hWT ξ ζ a v') (psi_pairing_integrable dual hP hP' hWT ξ ζ b v'),
          ha ξ ζ v', hb ξ ζ v', add_zero]
      zero_mem' := fun ξ ζ v' => by simp only [inner_zero_left, mul_zero, integral_zero]
      smul_mem' := fun c x hx ξ ζ v' => by
        have e : (fun g : Formalism.REAL.UJ ε => starRingEnd ℂ (ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) *
            inner ℂ (c • x) (Ψ' (Formalism.MainNotions.S.umat g) v')) = fun g => starRingEnd ℂ c *
              (starRingEnd ℂ (ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) * inner ℂ x (Ψ' (Formalism.MainNotions.S.umat g) v')) := by
          funext g
          rw [inner_smul_left]
          ring
        show ∫ g : Formalism.REAL.UJ ε, starRingEnd ℂ (ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) *
            inner ℂ (c • x) (Ψ' (Formalism.MainNotions.S.umat g) v') ∂(Formalism.REAL.muG ε) = 0
        rw [e, integral_const_mul, hx ξ ζ v', mul_zero] }
  have hst : ∀ k : S7.KG ε, ∀ v ∈ W, T'.op k v ∈ W := by
    intro k u hu ξ ζ v'
    let kk : Formalism.REAL.UJ ε := ⟨((k : S7.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ), (k : S7.UJ ε).2⟩
    rw [← integral_mul_left_eq_self (μ := Formalism.REAL.muG ε) _ kk]
    have e : ∀ g : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat (kk * g) =
        S7.toMK k * Formalism.MainNotions.S.umat g := fun g => rfl
    simp only [e, psi_coef_k_left_translate dual hP k, psi_k_left_equivariant hP'.1 k, clm_mul_apply_eq_comp,
      ContinuousLinearMap.inner_map_map_of_mem_unitary (T'.τ k).2]
    exact hu _ ζ v'
  have hv : v₀' ∈ W := h0
  rcases T'.irred W hst with hW | hW
  · exact absurd ((Submodule.mem_bot ℂ).1 (hW ▸ hv)) hv₀'
  · intro ξ ζ u' v'
    have hu : u' ∈ W := hW ▸ Submodule.mem_top
    exact hu ξ ζ v'

end Psi3

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

def occTauF (dual : Bool) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ) (k : S7.KG ε)
    (ξ : Fin n → T.V) : Fin n → T.V :=
  fun c => ∑ d, (cond dual (star (S7.toMK k c d)) (S7.toMK k c d)) • T.op k (ξ d)

def occPsiCoef (dual : Bool) {ε : Fin n → Bool} {Λ : Fin n → ℝ} {T : S7.KType ε Λ}
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (ξ ζ : Fin n → T.V) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ c, inner ℂ (ξ c) (∑ d, (cond dual ((g⁻¹) d c) (g c d)) • Ψ g (ζ d))

theorem occB_lowK_shiftF (dual : Bool) (ε : Fin n → Bool) (lam : Fin n → ℝ) (s : Fin n) :
    lowK ε (shiftF dual lam s) = cond dual (lowK ε lam - Pi.single s 1) (lowK ε lam + Pi.single s 1) := by
  exact lowWeight_shifted dual ε lam s

theorem occB_pieri (dual : Bool) {ε : Fin n → Bool} {Λ Λ' : Fin n → ℝ} (T : S7.KType ε Λ) (T' : S7.KType ε Λ')
    (s : Fin n) (hΛ : Λ' = cond dual (Λ - Pi.single s 1) (Λ + Pi.single s 1)) :
    ∃ ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V), ι₀ ≠ 0 ∧
      ∀ (k : S7.KG ε) (v : T'.V), ι₀ (T'.op k v) = occTauF dual T k (ι₀ v) := by
  exact pieri_standard_embedding dual T T' s hΛ

section Psi

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}

theorem occB_memLp_psi {v₀ : T.V} (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    (v w : T.V) :
    MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε) := by
  exact psi_weighted_memLp hgap hP hv₀ hW v w

theorem occB_trace_pos (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ')
    (hpos : ∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive)
    (hpos' : ∀ X, inP ε X → (Ψ' (NormedSpace.exp X)).IsPositive)
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε))
    (ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V)) (hι₀ : ι₀ ≠ 0)
    (hK : ∀ (k : S7.KG ε) (v : T'.V), ι₀ (T'.op k v) = occTauF dual T k (ι₀ v)) :
    0 < (∑ i, ∑ j, ∫ g : Formalism.REAL.UJ ε,
      starRingEnd ℂ (occPsiCoef dual Ψ (ι₀ (stdOrthonormalBasis ℂ T'.V i)) (ι₀ (stdOrthonormalBasis ℂ T'.V j))
        (Formalism.MainNotions.S.umat g)) *
      inner ℂ (stdOrthonormalBasis ℂ T'.V i) (Ψ' (Formalism.MainNotions.S.umat g) (stdOrthonormalBasis ℂ T'.V j))
        ∂(Formalism.REAL.muG ε)).re := by
  exact psi_pairing_trace_pos dual hP hP' hpos hpos' hWT ι₀ hι₀ hK

theorem occB_spread (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ') {v₀' : T'.V} (hv₀' : v₀' ≠ 0)
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε))
    (h0 : ∀ (ξ ζ : Fin n → T.V) (v' : T'.V), ∫ g : Formalism.REAL.UJ ε,
      starRingEnd ℂ (occPsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) * inner ℂ v₀' (Ψ' (Formalism.MainNotions.S.umat g) v')
        ∂(Formalism.REAL.muG ε) = 0) :
    ∀ (ξ ζ : Fin n → T.V) (u' v' : T'.V), ∫ g : Formalism.REAL.UJ ε,
      starRingEnd ℂ (occPsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) * inner ℂ u' (Ψ' (Formalism.MainNotions.S.umat g) v')
        ∂(Formalism.REAL.muG ε) = 0 := by
  exact psi_pairing_vanishing_spread dual hP hP' hv₀' hWT h0

theorem occB_pairing_ne (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ') {v₀' : T'.V}
    (hv₀' : v₀' ≠ 0)
    (hpos : ∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive)
    (hpos' : ∀ X, inP ε X → (Ψ' (NormedSpace.exp X)).IsPositive)
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε))
    (s : Fin n) (hlam' : lam' = shiftF dual lam s) :
    ∃ (ξ ζ : Fin n → T.V) (v' : T'.V), ∫ g : Formalism.REAL.UJ ε,
      starRingEnd ℂ (occPsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) * inner ℂ v₀' (Ψ' (Formalism.MainNotions.S.umat g) v')
        ∂(Formalism.REAL.muG ε) ≠ 0 := by
  have hΛ : lowK ε lam' = cond dual (lowK ε lam - Pi.single s 1) (lowK ε lam + Pi.single s 1) := by
    rw [hlam']; exact occB_lowK_shiftF dual ε lam s
  obtain ⟨ι₀, hι₀, hK⟩ := occB_pieri dual T T' s hΛ
  by_contra hne
  push Not at hne
  have hall := occB_spread dual hP hP' hv₀' hWT hne
  have hpos0 := occB_trace_pos dual hP hP' hpos hpos' hWT ι₀ hι₀ hK
  simp only [hall, Finset.sum_const_zero, Complex.zero_re, lt_self_iff_false] at hpos0

end Psi

end ReciprocityTheory.ChartRestriction.DS.G2
