module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfI
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfH
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfG
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfF
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix MeasureTheory

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

def jac (w : Ix ι r → ℂ) : ℂ := ∏ i : Ix ι r, if i.2.2 < i.2.1 then w (i.1, i.2.2, i.2.2) else 1

lemma continuous_lu : Continuous (lu (ι := ι) (r := r)) := by
  have hsl : ∀ (w0 : ι) (a b : Fin r), Continuous fun w : Ix ι r → ℂ => sl w w0 a b := by
    intro w0 a b
    by_cases h : b < a <;> simp [sl, h] <;> fun_prop
  have hup : ∀ (w0 : ι) (a b : Fin r), Continuous fun w : Ix ι r → ℂ => up w w0 a b := by
    intro w0 a b
    by_cases h : b < a <;> simp [up, h] <;> fun_prop
  refine continuous_pi fun i => ?_
  simp only [lu, Matrix.mul_apply, Matrix.add_apply]
  exact continuous_finsetSum _ fun k _ => (continuous_const.add (hsl _ _ _)).mul (hup _ _ _)

lemma continuous_jac : Continuous (jac (ι := ι) (r := r)) := by
  unfold jac
  refine continuous_finsetProd _ fun i _ => ?_
  by_cases h : i.2.2 < i.2.1 <;> simp [h] <;> fun_prop

lemma measurableSet_sS : MeasurableSet (sS ι r) := by
  unfold sS
  have h : {w : Ix ι r → ℂ | ∀ (τ : ι) (b : Fin r), w (τ, b, b) ≠ 0} =
      ⋂ τ : ι, ⋂ b : Fin r, (fun w : Ix ι r → ℂ => w (τ, b, b)) ⁻¹' {0}ᶜ := by
    ext w
    simp
  rw [h]
  exact MeasurableSet.iInter fun τ => MeasurableSet.iInter fun b =>
    measurable_pi_apply _ (measurableSet_singleton 0).compl

theorem lintegral_lu (g : (Ix ι r → ℂ) → ENNReal) :
    ∫⁻ v, g v = ∫⁻ w in sS ι r, ENNReal.ofReal (Complex.normSq (jac w)) * g (lu w) := by
  have hae : ∀ᵐ v ∂(volume : Measure (Ix ι r → ℂ)), v ∈ lu '' sS ι r := by
    refine measure_mono_null (fun v hv => ?_) (volume_BC_compl (ι := ι) (r := r))
    exact fun hB => hv (BC_subset_image (ι := ι) (r := r) hB)
  rw [show ∫⁻ v, g v = ∫⁻ v in lu '' sS ι r, g v by rw [Measure.restrict_eq_self_of_ae_mem hae],
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_sS
      (fun w _ => (hasFDerivAt_lu w).hasFDerivWithinAt) lu_injOn g]
  refine setLIntegral_congr_fun (measurableSet_sS (ι := ι) (r := r)) (fun w _ => ?_)
  rw [det_luD', abs_of_nonneg (Complex.normSq_nonneg _)]
  rfl

def eS (ι : Type*) [Fintype ι] (r : ℕ) : (Ix ι r → ℂ) ≃ᵐ (LoI ι r → ℂ) × (UpI ι r → ℂ) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Ix ι r => ℂ) (fun i => i.2.2 < i.2.1)

lemma eS_symm_apply (x : LoI ι r → ℂ) (y : UpI ι r → ℂ) (i : Ix ι r) :
    (eS ι r).symm (x, y) i = if h : i.2.2 < i.2.1 then x ⟨i, h⟩ else y ⟨i, h⟩ := rfl

def Nmat (x : LoI ι r → ℂ) (τ : ι) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => if h : b < a then x ⟨(τ, a, b), h⟩ else if a = b then 1 else 0

lemma jac_eS (x : LoI ι r → ℂ) (y : UpI ι r → ℂ) : jac ((eS ι r).symm (x, y)) = jacU y := by
  unfold jac jacU
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : i.2.2 < i.2.1 <;> simp [h, eS_symm_apply, dI]

lemma mem_sS_eS (x : LoI ι r → ℂ) (y : UpI ι r → ℂ) :
    (eS ι r).symm (x, y) ∈ sS ι r ↔ ∀ τ b, y (dI τ b) ≠ 0 := by
  simp [sS, eS_symm_apply, dI]

theorem lintegral_flat {g : (Ix ι r → ℂ) → ENNReal} (hg : Measurable g) :
    ∫⁻ v, g v = ∫⁻ x, ∫⁻ y, (if ∀ τ b, y (dI τ b) ≠ 0 then
      ENNReal.ofReal (Complex.normSq (jacU y)) * g (lu ((eS ι r).symm (x, y))) else 0) := by
  have hmp : MeasurePreserving (eS ι r) volume volume :=
    volume_preserving_piEquivPiSubtypeProd (fun _ : Ix ι r => ℂ) (fun i => i.2.2 < i.2.1)
  set F : (Ix ι r → ℂ) → ENNReal :=
    (sS ι r).indicator (fun w => ENNReal.ofReal (Complex.normSq (jac w)) * g (lu w)) with hF
  have hFm : Measurable F :=
    ((Complex.continuous_normSq.comp continuous_jac).measurable.ennreal_ofReal.mul
      (hg.comp continuous_lu.measurable)).indicator measurableSet_sS
  rw [lintegral_lu]
  first
  | rw [← lintegral_indicator measurableSet_sS]
  | rw [← lintegral_indicator _ measurableSet_sS]
  rw [← hmp.symm.lintegral_comp_emb (eS ι r).symm.measurableEmbedding, Measure.volume_eq_prod]
  refine (lintegral_prod _ ?_).trans ?_
  · exact (hFm.comp (eS ι r).symm.measurable).aemeasurable
  refine lintegral_congr fun x => lintegral_congr fun y => ?_
  by_cases h : ∀ τ b, y (dI τ b) ≠ 0
  · rw [if_pos h, Set.indicator_of_mem ((mem_sS_eS x y).2 h)]
    simp only [jac_eS]
  · rw [if_neg h]
    first
    | exact Set.indicator_of_notMem (fun hm => h ((mem_sS_eS x y).1 hm)) _
    | exact Set.indicator_of_not_mem (fun hm => h ((mem_sS_eS x y).1 hm)) _
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix MeasureTheory

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

def LA (A : ι → Matrix (Fin r) (Fin r) ℂ) : (Ix ι r → ℂ) →ₗ[ℂ] (Ix ι r → ℂ) where
  toFun v i := (A i.1 * Mt v i.1) i.2.1 i.2.2
  map_add' v v' := by
    funext i; simp only [Pi.add_apply, Matrix.mul_apply, Mt, Matrix.of_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    funext i; simp only [Pi.smul_apply, Matrix.mul_apply, Mt, Matrix.of_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring

def eB (ι : Type*) (r : ℕ) : Ix ι r ≃ Fin r × (ι × Fin r) where
  toFun i := (i.2.1, (i.1, i.2.2))
  invFun j := (j.2.1, j.1, j.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem det_LA (A : ι → Matrix (Fin r) (Fin r) ℂ) :
    LinearMap.det (LA A) = ∏ τ, (A τ).det ^ r := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Ix ι r)), ← Matrix.det_reindex_self (eB ι r)]
  have hM : Matrix.reindex (eB ι r) (eB ι r)
      (LinearMap.toMatrix (Pi.basisFun ℂ (Ix ι r)) (Pi.basisFun ℂ (Ix ι r)) (LA A)) =
      Matrix.blockDiagonal (fun k : ι × Fin r => A k.1) := by
    ext ⟨a, τ, b⟩ ⟨c, τ', d⟩
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, LinearMap.toMatrix_apply,
      Pi.basisFun_apply, Pi.basisFun_repr, Matrix.blockDiagonal_apply]
    simp only [eB, Equiv.coe_fn_symm_mk, LA, LinearMap.coe_mk, AddHom.coe_mk, Mt, Matrix.mul_apply,
      Matrix.of_apply]
    by_cases h : (τ, b) = (τ', d)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rw [if_pos rfl, Finset.sum_eq_single c]
      · simp
      · intro k _ hk
        simp [Pi.single_apply, hk]
      · simp
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun k _ => ?_
      have : ((τ, k, b) : Ix ι r) ≠ (τ', c, d) := by
        intro he
        apply h
        simp only [Prod.mk.injEq] at he ⊢
        exact ⟨he.1, he.2.2⟩
      simp [Pi.single_apply, this]
  rw [hM, Matrix.det_blockDiagonal, Fintype.prod_prod_type]
  simp [Finset.prod_const]

theorem lintegral_comp_LA (A : ι → Matrix (Fin r) (Fin r) ℂ) (hA : ∀ τ, (A τ).det ≠ 0)
    {F : (Ix ι r → ℂ) → ENNReal} (hF : Measurable F) :
    ∫⁻ v, F (LA A v) = ENNReal.ofReal (Complex.normSq (∏ τ, (A τ).det ^ r))⁻¹ * ∫⁻ v, F v := by
  have hdet : LinearMap.det ((LA A).restrictScalars ℝ) = Complex.normSq (∏ τ, (A τ).det ^ r) := by
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, det_LA]
  have hne : LinearMap.det ((LA A).restrictScalars ℝ) ≠ 0 := by
    rw [hdet, Ne, Complex.normSq_eq_zero]
    exact Finset.prod_ne_zero_iff.mpr fun τ _ => pow_ne_zero _ (hA τ)
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (Ix ι r → ℂ))) hne
  have hmeas : Measurable ((LA A).restrictScalars ℝ) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  calc ∫⁻ v, F (LA A v) = ∫⁻ v, F ((LA A).restrictScalars ℝ v) := rfl
    _ = ∫⁻ v, F v ∂(Measure.map ((LA A).restrictScalars ℝ) volume) :=
        (lintegral_map hF hmeas).symm
    _ = _ := by
        rw [hmap, lintegral_smul_measure, hdet,
          abs_of_nonneg (inv_nonneg.mpr (Complex.normSq_nonneg _)), smul_eq_mul]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix
open scoped ComplexConjugate

noncomputable section

variable {n : ℕ}

private lemma blockTriangular_inv_of_det_ne_zero {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.BlockTriangular id)
    (hd : M.det ≠ 0) : M⁻¹.BlockTriangular id := by
  letI := Matrix.invertibleOfIsUnitDet M (isUnit_iff_ne_zero.mpr hd)
  exact Matrix.blockTriangular_inv_of_blockTriangular hM

private lemma eq_of_mul_mul_eq_of_det_ne_zero {P Q X Y : Matrix (Fin n) (Fin n) ℂ} (hP : P.det ≠ 0) (hQ : Q.det ≠ 0)
    (h : P * X * Q = P * Y * Q) : X = Y := by
  have hP' := isUnit_iff_ne_zero.mpr hP
  have hQ' := isUnit_iff_ne_zero.mpr hQ
  have e : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Z = P⁻¹ * (P * Z * Q) * Q⁻¹ := by
    intro Z
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP', Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ', Matrix.mul_one]
  calc X = P⁻¹ * (P * X * Q) * Q⁻¹ := e X
    _ = P⁻¹ * (P * Y * Q) * Q⁻¹ := by rw [h]
    _ = Y := (e Y).symm

theorem gram_upper_unique {ε : Fin n → ℂ} (hε : ∀ a, ε a * ε a = 1)
    {β β' : Matrix (Fin n) (Fin n) ℂ} (hβ : β.BlockTriangular id) (hβ' : β'.BlockTriangular id)
    (hd : β.det ≠ 0) (hd' : β'.det ≠ 0)
    (h : β'ᵀ * diagonal ε * β'.map (starRingEnd ℂ) = βᵀ * diagonal ε * β.map (starRingEnd ℂ)) :
    ∃ D : Fin n → ℂ, (∀ a, ‖D a‖ = 1) ∧ β' = diagonal D * β := by
  classical
  have hε0 : ∀ a, ε a ≠ 0 := fun a h0 => by
    have := hε a
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have hu := isUnit_iff_ne_zero.mpr hd
  obtain ⟨γ, hγdef⟩ : ∃ γ : Matrix (Fin n) (Fin n) ℂ, γ = β' * β⁻¹ := ⟨_, rfl⟩
  have hγ : γ.BlockTriangular id := hγdef ▸ hβ'.mul (blockTriangular_inv_of_det_ne_zero hβ hd)
  have hγβ : β' = γ * β := by
    rw [hγdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
  have hγd : γ.det ≠ 0 := by
    intro h0
    apply hd'
    rw [hγβ, Matrix.det_mul, h0, zero_mul]
  have hbar : ∀ M : Matrix (Fin n) (Fin n) ℂ,
      (M.map (starRingEnd ℂ)).det = starRingEnd ℂ M.det := fun M => by
    rw [RingHom.map_det]; rfl

  have key : γᵀ * diagonal ε * γ.map (starRingEnd ℂ) = diagonal ε := by
    apply eq_of_mul_mul_eq_of_det_ne_zero (P := βᵀ) (Q := β.map (starRingEnd ℂ))
    · rwa [Matrix.det_transpose]
    · rw [hbar]; exact (map_ne_zero _).mpr hd
    · rw [← h, hγβ, Matrix.transpose_mul, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
  have hγinv := blockTriangular_inv_of_det_ne_zero hγ hγd
  have hγtu : IsUnit γᵀ.det := by rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr hγd

  have key2 : diagonal ε * γ.map (starRingEnd ℂ) = (γ⁻¹)ᵀ * diagonal ε := by
    rw [Matrix.transpose_nonsing_inv]
    conv_rhs => rw [← key]
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hγtu, Matrix.one_mul]
  have hoff : ∀ i j, i ≠ j → γ i j = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have e := congrFun (congrFun key2 i) j
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply, hγinv hlt, zero_mul,
        Matrix.map_apply] at e
      exact (map_eq_zero _).mp ((mul_eq_zero.mp e).resolve_left (hε0 i))
    · exact hγ hlt
  have hγdiag : γ = diagonal (fun a => γ a a) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ hij, hoff i j hij]
  refine ⟨fun a => γ a a, fun a => ?_, by rw [← hγdiag]; exact hγβ⟩
  have e := congrFun (congrFun key a) a
  rw [hγdiag] at e
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero _),
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq] at e
  have h2 : γ a a * starRingEnd ℂ (γ a a) = 1 := by
    have : ε a * (γ a a * starRingEnd ℂ (γ a a)) = ε a * 1 := by linear_combination e
    exact mul_left_cancel₀ (hε0 a) this
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h2
  have h3 : ‖γ a a‖ ^ 2 = 1 := by exact_mod_cast h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h3

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def Jd : Matrix (Fin r) (Fin r) ℂ := diagonal fun a => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

def gramT (β : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ := βᵀ * Jd X * β.map (starRingEnd ℂ)

def CmatSet : Set (Frame X.Ψ r) :=
  {β | ∀ τ a b, (b < a → β τ a b = 0) ∧ (a = b → 1 ≤ ‖β τ a b‖ ∧ ‖β τ a b‖ ≤ 2) ∧ (a < b → ‖β τ a b‖ ≤ 1)}

def SW : Set (Frame X.Ψ r) :=
  {y | y ∈ X.dom ∧ ∃ β ∈ CmatSet X, ∀ τ, gram τ.1 X.Gm (mat y τ) = gramT X (mat β τ)}

def Wf (y : Frame X.Ψ r) : ENNReal := (SW X).indicator 1 y

def uf (v : Ix X.Ψ r → ℂ) : Frame X.Ψ r := fun τ a b => v (τ, a, b)

lemma sgn_mul_self (p0 a : ℕ) : ((sgn p0 a : ℝ) : ℂ) * ((sgn p0 a : ℝ) : ℂ) = 1 := by
  unfold sgn
  split_ifs <;> norm_num

lemma CmatSet_diag_smul {β : Frame X.Ψ r} (hβ : β ∈ CmatSet X) {D : X.Ψ → Fin r → ℂ}
    (hD : ∀ τ a, ‖D τ a‖ = 1) : (fun τ => (diagonal (D τ) * mat β τ : Matrix (Fin r) (Fin r) ℂ)) ∈ CmatSet X := by
  simp only [CmatSet, Set.mem_setOf_eq] at hβ ⊢
  intro τ a b
  obtain ⟨h1, h2, h3⟩ := hβ τ a b
  simp only [Matrix.diagonal_mul, mat, Matrix.of_apply, norm_mul, hD, one_mul]
  exact ⟨fun h => by rw [h1 h, mul_zero], h2, h3⟩

lemma CmatSet_upper {β : Frame X.Ψ r} (hβ : β ∈ CmatSet X) (τ : X.Ψ) :
    (mat β τ).BlockTriangular id := fun a b h => (hβ τ a b).1 h

lemma CmatSet_det {β : Frame X.Ψ r} (hβ : β ∈ CmatSet X) (τ : X.Ψ) : (mat β τ).det ≠ 0 := by
  rw [Matrix.det_of_upperTriangular (CmatSet_upper X hβ τ)]
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  intro h0
  have h1 := ((hβ τ a a).2.1 rfl).1
  have h0' : β τ a a = 0 := h0
  rw [h0', norm_zero] at h1
  norm_num at h1

lemma mem_CmatSet_iff_Cy (β : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id)
    (y : UpI X.Ψ r → ℂ) :
    (fun τ => (β τ * Umat y τ : Matrix (Fin r) (Fin r) ℂ)) ∈ CmatSet X ↔ Lβ β y ∈ Cy X.Ψ r := by
  have hU : ∀ τ, (Umat y τ).BlockTriangular id := by
    intro τ a b h
    have h' : b < a := h
    simp only [Umat, Matrix.of_apply]
    rw [dite_eq_right (not_not.2 h')]
  have hP : ∀ τ, (β τ * Umat y τ).BlockTriangular id := fun τ => (hβ τ).mul (hU τ)
  simp only [Cy, CmatSet, Set.mem_setOf_eq]
  constructor
  · intro h i
    obtain ⟨⟨τ, a, b⟩, hi⟩ := i
    obtain ⟨_, h2, h3⟩ := h τ a b
    exact ⟨fun hab => h2 hab, fun hab => h3 (lt_of_le_of_ne (not_lt.1 hi) hab)⟩
  · intro h τ a b
    refine ⟨fun hab => hP τ hab, fun hab => ?_, fun hab => ?_⟩
    · subst hab
      exact (h ⟨(τ, a, a), lt_irrefl a⟩).1 rfl
    · exact (h ⟨(τ, a, b), not_lt.2 hab.le⟩).2 (ne_of_lt hab)

def UF (y : UpI X.Ψ r → ℂ) : Frame X.Ψ r := fun τ => Umat y τ

def β0 (y : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ := (mat (bOf X y) τ)⁻¹

lemma bOf_det {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) : (mat (bOf X y) τ).det ≠ 0 := by
  have h := bOf_mem (X := X) hy
  simp only [Bor, Set.mem_setOf_eq] at h
  exact (h τ).1

lemma β0_upper {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) : (β0 X y τ).BlockTriangular id := by
  have h := bOf_mem (X := X) hy
  simp only [Bor, Set.mem_setOf_eq] at h
  have hu : (mat (bOf X y) τ).BlockTriangular id := fun a c hac => (h τ).2 a c hac
  letI := (mat (bOf X y) τ).invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 (bOf_det X hy τ))
  exact Matrix.blockTriangular_inv_of_blockTriangular hu

lemma β0_det {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) : (β0 X y τ).det ≠ 0 := by
  intro h0
  have h1 := Matrix.det_mul (mat (bOf X y) τ) (mat (bOf X y) τ)⁻¹
  rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (bOf_det X hy τ)), Matrix.det_one] at h1
  have h0' : ((mat (bOf X y) τ)⁻¹).det = 0 := h0
  rw [h0', mul_zero] at h1
  exact one_ne_zero h1

lemma gram_rmul_eq {y b : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (rmul y b) τ) = gramT X (β0 X y τ * mat b τ) := by
  have hB := bOf_det X hy τ
  have hyB : gram τ.1 X.Gm (mat y τ * mat (bOf X y) τ) = Jd X := ortho_bOf (X := X) hy τ
  have hy' : mat y τ = mat y τ * mat (bOf X y) τ * (mat (bOf X y) τ)⁻¹ := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hB), Matrix.mul_one]
  have hgy : gram τ.1 X.Gm (mat y τ) = (β0 X y τ)ᵀ * Jd X * (β0 X y τ).map (starRingEnd ℂ) := by
    rw [hy', gram_mul, hyB]
    rfl
  show gram τ.1 X.Gm (mat y τ * mat b τ) = _
  rw [gram_mul, hgy]
  unfold gramT
  rw [Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

lemma UF_mem {y : UpI X.Ψ r → ℂ} (hy : ∀ τ b, y (dI τ b) ≠ 0) : UF X y ∈ Bor X.Ψ r := by
  simp only [Bor, Set.mem_setOf_eq]
  intro τ
  have hU : (Umat y τ).BlockTriangular id := by
    intro a b h
    have h' : b < a := h
    simp only [Umat, Matrix.of_apply]
    rw [dite_eq_right (not_not.2 h')]
  refine ⟨?_, fun a c h => hU h⟩
  show (Umat y τ).det ≠ 0
  rw [Matrix.det_of_upperTriangular hU]
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  have e : Umat y τ a a = y (dI τ a) := by
    unfold Umat dI
    rw [Matrix.of_apply, dite_eq_left (lt_irrefl a)]
  rw [e]
  exact hy τ a

private lemma mem_dom_rmul {y b : Frame X.Ψ r} (hy : y ∈ X.dom) (hb : b ∈ Bor X.Ψ r) :
    rmul y b ∈ X.dom := by
  simp only [Data.dom, GG, Set.mem_setOf_eq] at hy ⊢
  simp only [Bor, Set.mem_setOf_eq] at hb
  intro τ
  obtain ⟨hdet, hpos⟩ := hy τ
  obtain ⟨hbdet, hbup⟩ := hb τ
  have hup : (mat b τ).BlockTriangular id := fun a c h => hbup a c h
  have hdiag : ∀ a, mat b τ a a ≠ 0 := by
    have h := hbdet
    rw [Matrix.det_of_upperTriangular hup] at h
    exact fun a => Finset.prod_ne_zero_iff.1 h a (Finset.mem_univ a)
  refine ⟨?_, fun i => ?_⟩
  · show (mat y τ * mat b τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hdet hbdet
  · have hb2 : b ∈ Bor X.Ψ r := fun τ' => hb τ'
    rw [dmin_rmul (X := X) y hb2 τ i]
    set p := ∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) with hp
    have hp0 : p ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hdiag _
    have e : p * dmin X.Gm y τ i * conj p = (Complex.normSq p : ℂ) * dmin X.Gm y τ i := by
      rw [← Complex.mul_conj]
      ring
    rw [e, Complex.re_ofReal_mul]
    have hn : 0 < Complex.normSq p := Complex.normSq_pos.2 hp0
    have h3 := hpos i
    nlinarith

theorem Wf_rmul_UF {y : Frame X.Ψ r} (hy : y ∈ X.dom) {y' : UpI X.Ψ r → ℂ} (hy' : ∀ τ b, y' (dI τ b) ≠ 0) :
    Wf X (rmul y (UF X y')) = (Cy X.Ψ r).indicator 1 (Lβ (β0 X y) y') := by
  have hb := UF_mem X hy'
  have hdom : rmul y (UF X y') ∈ X.dom := mem_dom_rmul X hy hb
  have hb' := hb
  simp only [Bor, Set.mem_setOf_eq] at hb'
  have hβu : ∀ τ, (β0 X y τ).BlockTriangular id := fun τ => β0_upper X hy τ
  have key : rmul y (UF X y') ∈ SW X ↔ Lβ (β0 X y) y' ∈ Cy X.Ψ r := by
    rw [← mem_CmatSet_iff_Cy X (β0 X y) hβu y']
    constructor
    · rintro ⟨-, β, hβ, hg⟩
      have hU : ∀ τ, (mat (UF X y') τ).BlockTriangular id := fun τ a c h => (hb' τ).2 a c h
      have hD : ∀ τ, ∃ D : Fin r → ℂ, (∀ a, ‖D a‖ = 1) ∧
          mat β τ = diagonal D * (β0 X y τ * mat (UF X y') τ) := by
        intro τ
        refine gram_upper_unique (ε := fun a => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (fun a => sgn_mul_self X.p0 a)
          ((hβu τ).mul (hU τ)) (CmatSet_upper X hβ τ) ?_ (CmatSet_det X hβ τ) ?_
        · rw [Matrix.det_mul]
          exact mul_ne_zero (β0_det X hy τ) (hb' τ).1
        · exact (hg τ).symm.trans (gram_rmul_eq X hy τ)
      choose D hD1 hD2 using hD
      have e : (fun τ => (β0 X y τ * Umat y' τ : Matrix (Fin r) (Fin r) ℂ)) =
          fun τ => (diagonal (fun a => conj (D τ a)) * mat β τ : Matrix (Fin r) (Fin r) ℂ) := by
        funext τ
        have h1 : (fun a => conj (D τ a) * D τ a) = fun _ => (1 : ℂ) := by
          funext a
          rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hD1 τ a]
          norm_num
        rw [hD2 τ, ← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, h1, Matrix.diagonal_one, Matrix.one_mul]
        rfl
      rw [e]
      exact CmatSet_diag_smul X (D := fun τ a => conj (D τ a)) hβ (fun τ a => by simpa using hD1 τ a)
    · intro h
      exact ⟨hdom, fun τ => (β0 X y τ * Umat y' τ : Matrix (Fin r) (Fin r) ℂ), h, fun τ => gram_rmul_eq X hy τ⟩
  unfold Wf
  by_cases h : Lβ (β0 X y) y' ∈ Cy X.Ψ r
  · have h2 := key.2 h
    simp [Set.indicator_apply, h, h2]
  · have h2 : rmul y (UF X y') ∉ SW X := fun h' => h (key.1 h')
    simp [Set.indicator_apply, h, h2]

def invF (b : Frame X.Ψ r) : Frame X.Ψ r := fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)

lemma invF_mem' {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : invF X b ∈ Bor X.Ψ r := by
  simp only [Bor, Set.mem_setOf_eq] at hb ⊢
  intro τ
  obtain ⟨hd, hup⟩ := hb τ
  have hu : (mat b τ).BlockTriangular id := fun a c h => hup a c h
  letI := (mat b τ).invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 hd)
  have hinv := Matrix.blockTriangular_inv_of_blockTriangular hu
  refine ⟨?_, fun a c h => hinv h⟩
  intro h0
  have h1 := Matrix.det_mul (mat b τ) (mat b τ)⁻¹
  rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd), Matrix.det_one] at h1
  have h0' : ((mat b τ)⁻¹).det = 0 := h0
  rw [h0', mul_zero] at h1
  exact one_ne_zero h1

lemma rmul_invF {y b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : rmul (rmul y b) (invF X b) = y := by
  have hb' := hb
  simp only [Bor, Set.mem_setOf_eq] at hb'
  funext τ
  have hd := (hb' τ).1
  show mat y τ * mat b τ * (mat b τ)⁻¹ = y τ
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd), Matrix.mul_one]
  rfl

theorem Wf_rmul_not_dom {y b : Frame X.Ψ r} (hy : y ∉ X.dom) (hb : b ∈ Bor X.Ψ r) : Wf X (rmul y b) = 0 := by
  unfold Wf
  have h : rmul y b ∉ SW X := by
    rintro ⟨h1, -⟩
    apply hy
    have h2 := mem_dom_rmul X h1 (invF_mem' X hb)
    rwa [rmul_invF X hb] at h2
  simp [Set.indicator_apply, h]

lemma isClosed_imp {P : Prop} {S : Set ℂ} (hS : IsClosed S) : IsClosed {z : ℂ | P → z ∈ S} := by
  by_cases h : P
  · simpa [h] using hS
  · simp [h]

lemma continuous_coord (τ : X.Ψ) (a b : Fin r) : Continuous fun β : Frame X.Ψ r => β τ a b := (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply τ))

lemma isCompact_CmatSet : IsCompact (CmatSet X) := by
  have hS : ∀ a b : Fin r, IsCompact {z : ℂ | (b < a → z = 0) ∧ (a = b → 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2) ∧ (a < b → ‖z‖ ≤ 1)} := by
    intro a b
    apply Metric.isCompact_of_isClosed_isBounded
    · rw [Set.setOf_and, Set.setOf_and]
      refine IsClosed.inter (isClosed_imp (S := {0}) isClosed_singleton)
        (IsClosed.inter (isClosed_imp (S := {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2}) ?_) (isClosed_imp (S := {z : ℂ | ‖z‖ ≤ 1}) ?_))
      · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
      · exact isClosed_le continuous_norm continuous_const
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset ?_
      rintro z ⟨h1, h2, h3⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      rcases lt_trichotomy a b with h | h | h
      · linarith [h3 h]
      · exact (h2 h).2
      · rw [h1 h, norm_zero]
        norm_num
  have e : CmatSet X = Set.pi Set.univ fun τ => Set.pi Set.univ fun a => Set.pi Set.univ fun b =>
      {z : ℂ | (b < a → z = 0) ∧ (a = b → 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2) ∧ (a < b → ‖z‖ ≤ 1)} := by
    ext β
    simp [CmatSet, Set.mem_pi]
  rw [e]
  exact isCompact_univ_pi fun τ => isCompact_univ_pi fun a => isCompact_univ_pi fun b => hS a b

lemma continuous_entry {α : Type*} [TopologicalSpace α] {f : α → Frame X.Ψ r}
    (hf : ∀ τ a b, Continuous fun y => f y τ a b) :
    Continuous f := continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => hf τ a b

def gramF (y : Frame X.Ψ r) : Frame X.Ψ r := fun τ => gram τ.1 X.Gm (mat y τ)

def gramTF (β : Frame X.Ψ r) : Frame X.Ψ r := fun τ => gramT X (mat β τ)

lemma continuous_gramF : Continuous (gramF X) := by
  apply continuous_entry
  intro τ a b
  simp only [gramF, ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, mat]
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((continuous_coord X τ i a).mul continuous_const).mul (Complex.continuous_conj.comp (continuous_coord X τ j b))

lemma continuous_gramTF : Continuous (gramTF X) := by
  apply continuous_entry
  intro τ a b
  simp only [gramTF, gramT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, mat, Matrix.of_apply]
  exact continuous_finsetSum _ fun l _ =>
    (continuous_finsetSum _ fun k _ => (continuous_coord X τ k a).mul continuous_const).mul
      (Complex.continuous_conj.comp (continuous_coord X τ l b))

private lemma isOpen_X_dom : IsOpen X.dom := by
  have e : X.dom = ⋂ τ : X.Ψ, ({x : Frame X.Ψ r | (mat x τ).det ≠ 0} ∩
      ⋂ i : Fin (r + 1), {x : Frame X.Ψ r | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
    ext x
    simp [Data.dom, GG]
  rw [e]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · have hm : Continuous fun x : Frame X.Ψ r => mat x τ := continuous_apply τ
    exact isOpen_ne_fun hm.matrix_det continuous_const
  · have hg : Continuous fun x : Frame X.Ψ r => gram τ.1 X.Gm (mat x τ) :=
      (continuous_apply τ).comp (continuous_gramF X)
    have hc : Continuous fun x : Frame X.Ψ r => (dmin X.Gm x τ i).re := by
      unfold dmin lminor
      exact Complex.continuous_re.comp (hg.matrix_submatrix _ _).matrix_det
    exact isOpen_lt continuous_const (continuous_const.mul hc)

lemma measurableSet_SW : MeasurableSet (SW X) := by
  have e : SW X = X.dom ∩ gramF X ⁻¹' (gramTF X '' CmatSet X) := by
    ext y
    simp only [SW, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨h1, β, hβ, hg⟩
      exact ⟨h1, β, hβ, funext fun τ => (hg τ).symm⟩
    · rintro ⟨h1, β, hβ, hg⟩
      exact ⟨h1, β, hβ, fun τ => (congrFun hg τ).symm⟩
  rw [e]
  have h1 : MeasurableSet X.dom := (isOpen_X_dom X).measurableSet
  have h2 : IsClosed (gramF X ⁻¹' (gramTF X '' CmatSet X)) :=
    ((isCompact_CmatSet X).image (continuous_gramTF X)).isClosed.preimage (continuous_gramF X)
  exact h1.inter h2.measurableSet

lemma measurable_Wf : Measurable (Wf X) := measurable_one.indicator (measurableSet_SW X)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData Finset

noncomputable section

attribute [local instance] Classical.propDecidable

lemma prod_min_range (f : ℕ → ℝ) (n : ℕ) :
    ∏ a ∈ range n, ∏ b ∈ range n, f (min a b) = (∏ i ∈ range n, (∏ k ∈ range i, f k) ^ 2) * ∏ k ∈ range n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ∀ a ∈ range n, ∏ b ∈ range (n + 1), f (min a b) = (∏ b ∈ range n, f (min a b)) * f a := by
      intro a ha
      rw [prod_range_succ, min_eq_left (le_of_lt (mem_range.mp ha))]
    have h2 : ∏ b ∈ range (n + 1), f (min n b) = (∏ b ∈ range n, f b) * f n := by
      rw [prod_range_succ, min_self]
      congr 1
      exact prod_congr rfl fun b hb => by rw [min_eq_right (le_of_lt (mem_range.mp hb))]
    rw [prod_range_succ (fun a => ∏ b ∈ range (n + 1), f (min a b)) n, prod_congr rfl h1, prod_mul_distrib, ih, h2,
      prod_range_succ (fun i => (∏ k ∈ range i, f k) ^ 2) n, prod_range_succ f n]
    ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma upper_mul_diag {A B : Matrix (Fin r) (Fin r) ℂ} (hA : A.BlockTriangular id) (hB : B.BlockTriangular id)
    (k : Fin r) : (A * B) k k = A k k * B k k := by
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · intro j _ hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

lemma bOf_diag (y : Frame X.Ψ r) (τ : X.Ψ) (k : Fin r) : mat (bOf X y) τ k k = sOf X y τ k := by
  have h1 : mat (bOf X y) τ k k = uOf X y τ k k * sOf X y τ k := by
    show (uOf X y τ * Matrix.diagonal (sOf X y τ)) k k = _
    rw [Matrix.mul_diagonal]
  rw [h1]
  have h2 : uOf X y τ k k = 1 := by
    show uMat _ k k = 1
    unfold uMat
    simp
  rw [h2, one_mul]

lemma normSq_β0_diag {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) (k : Fin r) :
    Complex.normSq (β0 X y τ k k) = |(dOf X y τ k).re| := by
  have hinv : β0 X y τ * mat (bOf X y) τ = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (bOf_det X hy τ))
  have h1 := congrFun (congrFun hinv k) k
  rw [upper_mul_diag (β0_upper X hy τ) (upper_of_bor X (bOf_mem X hy) τ), bOf_diag, Matrix.one_apply_eq] at h1
  have hpos := abs_re_pos X hy τ k
  have hs : Complex.normSq (sOf X y τ k) = |(dOf X y τ k).re|⁻¹ := by
    rw [sOf, Complex.normSq_ofReal, ← pow_two, inv_pow, Real.sq_sqrt (abs_nonneg _)]
  have h2 := congrArg Complex.normSq h1
  rw [Complex.normSq_mul, hs, map_one] at h2
  field_simp at h2
  linarith

def δ (y : Frame X.Ψ r) (τ : X.Ψ) (k : Fin r) : ℝ := |(dOf X y τ k).re|

def fδ (y : Frame X.Ψ r) (τ : X.Ψ) (k : ℕ) : ℝ := if h : k < r then δ X y τ ⟨k, h⟩ else 1

lemma normSq_det_jac {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    Complex.normSq (LinearMap.det (Lβ (β0 X y))) * Complex.normSq (jacβ (β0 X y)) =
      ∏ i : Ix X.Ψ r, δ X y i.1 (min i.2.1 i.2.2) := by
  rw [det_Lβ _ (β0_upper X hy), jacβ, map_prod, map_prod]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : Ix X.Ψ r => i.2.2 < i.2.1)
    (fun i => δ X y i.1 (min i.2.1 i.2.2))]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : Ix X.Ψ r => i.2.2 < i.2.1)
    (fun i => Complex.normSq (if i.2.2 < i.2.1 then β0 X y i.1 i.2.2 i.2.2 else 1))]
  have e1 : ∏ i : UpI X.Ψ r, Complex.normSq (β0 X y i.1.1 i.1.2.1 i.1.2.1) =
      ∏ i : {i : Ix X.Ψ r // ¬ i.2.2 < i.2.1}, δ X y i.1.1 (min i.1.2.1 i.1.2.2) :=
    Finset.prod_congr rfl fun i _ => by rw [normSq_β0_diag X hy, min_eq_left (not_lt.1 i.2)]; rfl
  have e2 : ∏ i : {i : Ix X.Ψ r // ¬ i.2.2 < i.2.1},
      Complex.normSq (if i.1.2.2 < i.1.2.1 then β0 X y i.1.1 i.1.2.2 i.1.2.2 else 1) = 1 :=
    Finset.prod_eq_one fun i _ => by rw [if_neg i.2, map_one]
  have e3 : ∏ i : {i : Ix X.Ψ r // i.2.2 < i.2.1},
      Complex.normSq (if i.1.2.2 < i.1.2.1 then β0 X y i.1.1 i.1.2.2 i.1.2.2 else 1) =
      ∏ i : {i : Ix X.Ψ r // i.2.2 < i.2.1}, δ X y i.1.1 (min i.1.2.1 i.1.2.2) :=
    Finset.prod_congr rfl fun i _ => by rw [if_pos i.2, normSq_β0_diag X hy, min_eq_right i.2.le]; rfl
  rw [e1, e2, e3, mul_one, mul_comm]

lemma norm_dmin {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm y τ i‖ = ∏ k ∈ range i, fδ X y τ k := by
  rw [dmin_prod X hy τ i, norm_prod, ← Fin.prod_univ_eq_prod_range (fδ X y τ)]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hj : (j : ℕ) < r := lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ i.isLt)
  rw [fδ, dite_eq_left hj, δ]
  have hre := dOf_real X hy τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
  have hc : Fin.castLE (Nat.le_of_lt_succ i.isLt) j = (⟨j, hj⟩ : Fin r) := Fin.ext rfl
  rw [hc] at hre ⊢
  exact (Complex.abs_re_eq_norm.2 hre).symm

theorem exponent_identity {y : Frame X.Ψ r} (hy : y ∈ X.dom) (hlast : ∀ τ, ‖dmin X.Gm y τ (Fin.last r)‖ = 1) :
    Complex.normSq (LinearMap.det (Lβ (β0 X y))) * Complex.normSq (jacβ (β0 X y)) =
      ∏ τ, ∏ i : Fin r, ‖dmin X.Gm y τ i.castSucc‖ ^ 2 := by
  have hτ : ∀ τ : X.Ψ, ∏ a : Fin r, ∏ b : Fin r, δ X y τ (min a b) =
      ∏ i : Fin r, ‖dmin X.Gm y τ i.castSucc‖ ^ 2 := by
    intro τ
    have hp := prod_min_range (fδ X y τ) r
    have hl : ∏ k ∈ range r, fδ X y τ k = 1 := by
      have h1 := norm_dmin X hy τ (Fin.last r)
      rw [hlast τ, Fin.val_last] at h1
      exact h1.symm
    rw [hl, mul_one] at hp
    have hd : ∀ i : Fin r, ‖dmin X.Gm y τ i.castSucc‖ = ∏ k ∈ range (i : ℕ), fδ X y τ k := by
      intro i
      rw [norm_dmin X hy τ i.castSucc, Fin.coe_castSucc]
    have e1 : ∀ a b : Fin r, δ X y τ (min a b) = fδ X y τ (min (a : ℕ) (b : ℕ)) := by
      intro a b
      unfold fδ
      rw [dite_eq_left (min_lt_of_left_lt a.isLt)]
      congr 1
    simp only [hd, e1]
    simp only [Finset.prod_range] at hp ⊢
    exact hp
  rw [normSq_det_jac X hy]
  unfold Ix
  simp only [Fintype.prod_prod_type]
  exact Finset.prod_congr rfl fun τ _ => hτ τ

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
