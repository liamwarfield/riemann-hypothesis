module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriUniq
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.DensOn

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.QrMapMeasurableSetImage
noncomputable section

open Finset Matrix MeasureTheory InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

lemma qrA_Jm_one : Jm (fun _ : Fin N => true) = 1 := by
  unfold Jm
  simp

lemma qrA_unitary (k : UNgrp N) : (toM k)ᴴ * toM k = 1 := by
  have h : (toM k)ᴴ * Jm (fun _ : Fin N => true) * toM k = Jm (fun _ : Fin N => true) := k.2
  rwa [qrA_Jm_one, Matrix.mul_one] at h

lemma qrA_upMat_continuous : Continuous (upMat (N := N)) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  by_cases hab : a = b
  · simp only [upMat, if_pos hab]
    exact Complex.continuous_ofReal.comp ((continuous_apply a).comp continuous_fst)
  · by_cases h : a < b
    · simp only [upMat, if_neg hab, dif_pos h]
      exact (continuous_apply _).comp continuous_snd
    · simp only [upMat, if_neg hab, dif_neg h]
      exact continuous_const

theorem qrMap_continuous : Continuous (qrMap (N := N)) := by
  show Continuous fun kt : UNgrp N × TriCo N => toM kt.1 * upMat kt.2
  exact ((Units.continuous_val.comp continuous_subtype_val).comp continuous_fst).matrix_mul
    (qrA_upMat_continuous.comp continuous_snd)

lemma qrA_upMat_tri (t : TriCo N) : (upMat t).IsUpperTriangular := by
  intro i j hij
  have h1 : i ≠ j := ne_of_gt hij
  have h2 : ¬ i < j := not_lt.2 (le_of_lt hij)
  simp only [upMat, if_neg h1, dif_neg h2]

lemma qrA_upMat_diag (t : TriCo N) (i : Fin N) : upMat t i i = ((t.1 i : ℝ) : ℂ) := by
  simp [upMat]

lemma qrA_upMat_det (t : TriCo N) : (upMat t).det = ∏ j, ((t.1 j : ℝ) : ℂ) := by
  rw [Matrix.det_of_upperTriangular (qrA_upMat_tri t)]
  exact Finset.prod_congr rfl fun i _ => qrA_upMat_diag t i

lemma qrA_upMat_det_ne (t : TriCo N) (ht : t ∈ triPos N) : (upMat t).det ≠ 0 := by
  rw [qrA_upMat_det]
  exact Finset.prod_ne_zero_iff.2 fun j _ => Complex.ofReal_ne_zero.2 (ht j).ne'

lemma qrA_triCoOf_upMat (t : TriCo N) : triCoOf (upMat t) = t := by
  refine Prod.ext (funext fun j => ?_) (funext fun ab => ?_)
  · simp [triCoOf, upMat]
  · simp only [triCoOf, upMat, if_neg (ne_of_lt ab.2), dif_pos ab.2]

lemma qrA_mul_diag {A B : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsUpperTriangular)
    (hB : B.IsUpperTriangular) (i : Fin N) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

lemma qrA_inv_tri {R : Matrix (Fin N) (Fin N) ℂ} (hR : R.IsUpperTriangular) (hd : R.det ≠ 0) :
    (R⁻¹).IsUpperTriangular := by
  haveI : Invertible R := R.invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 hd)
  exact Matrix.blockTriangular_inv_of_blockTriangular hR

lemma qrA_upMat_cancel {A B : Matrix (Fin N) (Fin N) ℂ} {R : Matrix (Fin N) (Fin N) ℂ} (hd : R.det ≠ 0)
    (h : A * R = B * R) : A = B := by
  have hu : IsUnit R.det := isUnit_iff_ne_zero.2 hd
  calc A = A * R * R⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = B * R * R⁻¹ := by rw [h]
    _ = B := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

lemma qrA_tri_unique {U R R' : Matrix (Fin N) (Fin N) ℂ} {t t' : TriCo N} (ht : t ∈ triPos N)
    (ht' : t' ∈ triPos N) (hR : R = upMat t) (hR' : R' = upMat t')
    (h1 : U * R = R') (h2 : Uᴴ * R' = R) : t = t' := by
  subst hR
  subst hR'
  have hd := qrA_upMat_det_ne t ht
  have hd' := qrA_upMat_det_ne t' ht'
  have hRt := qrA_upMat_tri t
  have hRt' := qrA_upMat_tri t'
  have hu : IsUnit (upMat t).det := isUnit_iff_ne_zero.2 hd
  have hu' : IsUnit (upMat t').det := isUnit_iff_ne_zero.2 hd'
  have hU : U = upMat t' * (upMat t)⁻¹ := by
    rw [← h1, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  have hUh : Uᴴ = upMat t * (upMat t')⁻¹ := by
    rw [← h2, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu', Matrix.mul_one]
  have hUt : U.IsUpperTriangular := hU ▸ hRt'.mul (qrA_inv_tri hRt hd)
  have hUht : Uᴴ.IsUpperTriangular := hUh ▸ hRt.mul (qrA_inv_tri hRt' hd')
  have hinvd : ∀ M : Matrix (Fin N) (Fin N) ℂ, M.IsUpperTriangular → M.det ≠ 0 →
      ∀ i, M⁻¹ i i = (M i i)⁻¹ := by
    intro M hM hMd i
    have h := congrFun (congrFun (Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.2 hMd)) i) i
    rw [qrA_mul_diag hM (qrA_inv_tri hM hMd), Matrix.one_apply_eq] at h
    exact eq_inv_of_mul_eq_one_right h
  have hdiag : ∀ i, U i i = ((t'.1 i : ℝ) : ℂ) * (((t.1 i : ℝ) : ℂ))⁻¹ := by
    intro i
    rw [hU, qrA_mul_diag hRt' (qrA_inv_tri hRt hd), hinvd _ hRt hd, qrA_upMat_diag, qrA_upMat_diag]
  have hdiag' : ∀ i, Uᴴ i i = ((t.1 i : ℝ) : ℂ) * (((t'.1 i : ℝ) : ℂ))⁻¹ := by
    intro i
    rw [hUh, qrA_mul_diag hRt (qrA_inv_tri hRt' hd'), hinvd _ hRt' hd', qrA_upMat_diag, qrA_upMat_diag]
  have heq : ∀ i, t.1 i = t'.1 i := by
    intro i
    have e1 := hdiag' i
    rw [Matrix.conjTranspose_apply, hdiag i] at e1
    have ha := ht i
    have hb := ht' i
    have e2 : t'.1 i * (t.1 i)⁻¹ = t.1 i * (t'.1 i)⁻¹ := by
      have e3 : ((t'.1 i * (t.1 i)⁻¹ : ℝ) : ℂ) = ((t.1 i * (t'.1 i)⁻¹ : ℝ) : ℂ) := by
        push_cast
        rw [← e1]
        simp [Complex.conj_ofReal]
      exact_mod_cast e3
    field_simp at e2
    nlinarith
  have hU1 : U = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [hdiag i, heq i, Matrix.one_apply_eq]
      exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 (ht' i).ne')
    · rw [Matrix.one_apply_ne hij]
      rcases lt_or_gt_of_ne hij with h | h
      · have e := hUht h
        rw [Matrix.conjTranspose_apply] at e
        simpa using e
      · exact hUt h
  rw [hU1, Matrix.one_mul] at h1
  rw [← qrA_triCoOf_upMat t, h1, qrA_triCoOf_upMat]

theorem qrMap_injOn : Set.InjOn (qrMap (N := N)) (Set.univ ×ˢ triPos N) := by
  rintro ⟨k, t⟩ ⟨-, ht⟩ ⟨k', t'⟩ ⟨-, ht'⟩ h
  have h' : toM k * upMat t = toM k' * upMat t' := h
  have e1 : (toM k')ᴴ * toM k * upMat t = upMat t' := by
    rw [Matrix.mul_assoc, h', ← Matrix.mul_assoc, qrA_unitary, Matrix.one_mul]
  have e2 : ((toM k')ᴴ * toM k)ᴴ * upMat t' = upMat t := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, ← h',
      ← Matrix.mul_assoc, qrA_unitary, Matrix.one_mul]
  have htt : t = t' := qrA_tri_unique ht ht' rfl rfl e1 e2
  subst htt
  have hk : toM k = toM k' := qrA_upMat_cancel (qrA_upMat_det_ne t ht) h'
  have hk' : k = k' := Subtype.ext (Units.ext hk)
  rw [hk']

private theorem qrMap_measurableSet_image_lemma (N : ℕ) : PolishSpace (UNgrp N) := by
  obtain ⟨C, hC, hmem⟩ : ∃ C : Set (Fin N → Fin N → ℂ), IsClosed C ∧
      ∀ Z, Z ∈ C ↔ (Matrix.of Z)ᴴ * Matrix.of Z = 1 :=
    ⟨{Z | (Matrix.of Z)ᴴ * Matrix.of Z = 1},
      isClosed_eq ((continuous_id : Continuous fun Z : Fin N → Fin N → ℂ => Matrix.of Z).matrix_conjTranspose.matrix_mul
        (continuous_id : Continuous fun Z : Fin N → Fin N → ℂ => Matrix.of Z)) continuous_const,
      fun Z => Iff.rfl⟩
  haveI : PolishSpace C := hC.polishSpace
  have hCt : Continuous (fun Z : C => (Z : Fin N → Fin N → ℂ)) := continuous_subtype_val
  let e : UNgrp N ≃ₜ C :=
    { toFun := fun k => ⟨Matrix.of.symm (toM k), (hmem _).2 (qrA_unitary k)⟩
      invFun := fun Z => ⟨⟨Matrix.of Z.1, (Matrix.of Z.1)ᴴ, mul_eq_one_comm.1 ((hmem _).1 Z.2),
          (hmem _).1 Z.2⟩, by
        show (Matrix.of Z.1)ᴴ * Jm (fun _ : Fin N => true) * Matrix.of Z.1 = Jm (fun _ : Fin N => true)
        rw [qrA_Jm_one, Matrix.mul_one]
        exact (hmem _).1 Z.2⟩
      left_inv := fun k => Subtype.ext (Units.ext rfl)
      right_inv := fun Z => rfl
      continuous_toFun := continuous_induced_rng.2
        (Units.continuous_val.comp continuous_subtype_val :
          Continuous fun k : UNgrp N => ((k : (Matrix (Fin N) (Fin N) ℂ)ˣ) : Matrix (Fin N) (Fin N) ℂ))
      continuous_invFun := continuous_induced_rng.2 (Units.continuous_iff.2
        ⟨hCt, hCt.matrix_conjTranspose⟩) }
  exact e.isClosedEmbedding.polishSpace

theorem qrMap_measurableSet_image (S : Set (UNgrp N × TriCo N)) (hS : MeasurableSet S)
    (hS0 : S ⊆ Set.univ ×ˢ triPos N) : MeasurableSet (qrMap '' S) := by
  haveI : PolishSpace (UNgrp N) := qrMap_measurableSet_image_lemma N
  exact hS.image_of_continuousOn_injOn qrMap_continuous.continuousOn (qrMap_injOn.mono hS0)

lemma qrA_exists (Z : Matrix (Fin N) (Fin N) ℂ) (hZ : Z.det ≠ 0) :
    ∃ Q : Matrix (Fin N) (Fin N) ℂ, ∃ t : TriCo N, Qᴴ * Q = 1 ∧ t ∈ triPos N ∧ Q * upMat t = Z := by
  classical
  let f : Fin N → EuclideanSpace ℂ (Fin N) := fun j => WithLp.toLp 2 (Z.col j)
  have hli : LinearIndependent ℂ f := by
    have h0 := Matrix.linearIndependent_cols_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det Z).2 (isUnit_iff_ne_zero.2 hZ))
    exact h0.map' (WithLp.linearEquiv 2 ℂ (Fin N → ℂ)).symm.toLinearMap (LinearEquiv.ker _)
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin N)) = Fintype.card (Fin N) := by simp
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis hdim f
  have hgs : ∀ j, InnerProductSpace.gramSchmidt ℂ f j ≠ 0 := fun j =>
    InnerProductSpace.gramSchmidt_ne_zero j hli
  have hb : ∀ i, b i = InnerProductSpace.gramSchmidtNormed ℂ f i := by
    intro i
    refine InnerProductSpace.gramSchmidtOrthonormalBasis_apply hdim ?_
    intro h
    have := InnerProductSpace.gramSchmidtNormed_unit_length i hli
    rw [h, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix (Fin N) (Fin N) ℂ, ∀ a i, Q a i = (b i).ofLp a :=
    ⟨Matrix.of fun a i => (b i).ofLp a, fun _ _ => rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R : Matrix (Fin N) (Fin N) ℂ, ∀ i j, R i j = inner ℂ (b i) (f j) :=
    ⟨Matrix.of fun i j => inner ℂ (b i) (f j), fun _ _ => rfl⟩
  have hRup : R.IsUpperTriangular := by
    intro i j hji
    rw [hRdef]
    exact InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular hdim f hji
  have hself : ∀ j, inner ℂ (InnerProductSpace.gramSchmidt ℂ f j) (f j) =
      (‖InnerProductSpace.gramSchmidt ℂ f j‖ : ℂ) ^ 2 := by
    intro j
    have hf : f j = InnerProductSpace.gramSchmidt ℂ f j +
        ∑ i ∈ Finset.Iio j, (ℂ ∙ InnerProductSpace.gramSchmidt ℂ f i).starProjection (f j) := by
      rw [InnerProductSpace.gramSchmidt_def ℂ f j]
      abel
    rw [hf, inner_add_right, inner_sum, Finset.sum_eq_zero (fun i hi => ?_), add_zero,
      inner_self_eq_norm_sq_to_K]
    · rfl
    · rw [Submodule.starProjection_singleton, inner_smul_right,
        InnerProductSpace.gramSchmidt_orthogonal ℂ f (ne_of_gt (Finset.mem_Iio.1 hi)), mul_zero]
  have hdiag : ∀ j, R j j = ((‖InnerProductSpace.gramSchmidt ℂ f j‖ : ℝ) : ℂ) := by
    intro j
    have ha : ‖InnerProductSpace.gramSchmidt ℂ f j‖ ≠ 0 := norm_ne_zero_iff.2 (hgs j)
    rw [hRdef, hb j, InnerProductSpace.gramSchmidtNormed, inner_smul_left, hself j]
    simp only [map_inv₀, RCLike.conj_ofReal, Complex.conj_ofReal]
    change (((‖InnerProductSpace.gramSchmidt ℂ f j‖ : ℝ) : ℂ))⁻¹ *
        ((‖InnerProductSpace.gramSchmidt ℂ f j‖ : ℝ) : ℂ) ^ 2 = ((‖InnerProductSpace.gramSchmidt ℂ f j‖ : ℝ) : ℂ)
    have hc : ((‖InnerProductSpace.gramSchmidt ℂ f j‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha
    rw [sq, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have ht : triCoOf R ∈ triPos N := by
    intro j
    show 0 < (R j j).re
    rw [hdiag j, Complex.ofReal_re]
    exact norm_pos_iff.2 (hgs j)
  have hupR : upMat (triCoOf R) = R := by
    ext a c
    by_cases hac : a = c
    · subst hac
      simp only [upMat, triCoOf, if_true]
      rw [hdiag a, Complex.ofReal_re]
    · by_cases h : a < c
      · simp only [upMat, triCoOf, if_neg hac, dif_pos h]
      · simp only [upMat, if_neg hac, dif_neg h]
        exact (hRup (lt_of_le_of_ne (not_lt.1 h) (Ne.symm hac))).symm
  have hQ : Qᴴ * Q = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    have e := (orthonormal_iff_ite.1 b.orthonormal) i j
    rw [PiLp.inner_apply] at e
    rw [Matrix.one_apply, ← e]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.conjTranspose_apply, hQdef, hQdef, RCLike.inner_apply, Complex.star_def]
    ring
  have hQR : Q * R = Z := by
    ext a j
    rw [Matrix.mul_apply]
    have e := congrArg (fun v : EuclideanSpace ℂ (Fin N) => v.ofLp a) (b.sum_repr' (f j))
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      f, PiLp.toLp_apply, Matrix.col_apply] at e
    rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hQdef, hRdef]
    ring
  exact ⟨Q, triCoOf R, hQ, ht, by rw [hupR]; exact hQR⟩

theorem qrMap_image :
    qrMap '' (Set.univ ×ˢ triPos N) = {Z : Fin N → Fin N → ℂ | (Matrix.of Z).det ≠ 0} := by
  ext Z
  constructor
  · rintro ⟨⟨k, t⟩, ⟨-, ht⟩, rfl⟩
    show (toM k * upMat t).det ≠ 0
    rw [Matrix.det_mul]
    refine mul_ne_zero ?_ (qrA_upMat_det_ne t ht)
    intro h0
    have e := congrArg Matrix.det (qrA_unitary k)
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at e
    exact zero_ne_one e
  · intro hZ
    obtain ⟨Q, t, hQ, ht, hQt⟩ := qrA_exists (Matrix.of Z) hZ
    refine ⟨(⟨⟨Q, Qᴴ, mul_eq_one_comm.1 hQ, hQ⟩, ?_⟩, t), ⟨Set.mem_univ _, ht⟩, ?_⟩
    · show Qᴴ * Jm (fun _ : Fin N => true) * Q = Jm (fun _ : Fin N => true)
      rw [qrA_Jm_one, Matrix.mul_one]
      exact hQ
    · show Matrix.of.symm (Q * upMat t) = Z
      rw [hQt]
      rfl

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.LeftMulMapEqTransposeConj
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem matrix_space_volume_isAddHaar (N : ℕ) : (volume : Measure (Fin N → Fin N → ℂ)).IsAddHaarMeasure := by
  haveI hC : (volume : Measure ℂ).IsAddHaarMeasure := by infer_instance
  haveI hS : SigmaFinite (volume : Measure ℂ) := by infer_instance
  haveI h1 : (volume : Measure (Fin N → ℂ)).IsAddHaarMeasure := by
    rw [volume_pi]; exact Measure.pi.isAddHaarMeasure _
  haveI hS1 : SigmaFinite (volume : Measure (Fin N → ℂ)) := by infer_instance
  rw [volume_pi]; exact Measure.pi.isAddHaarMeasure _

def leftMulLinearMap (g : Matrix (Fin N) (Fin N) ℂ) :
    (Fin N → Fin N → ℂ) →ₗ[ℂ] (Fin N → Fin N → ℂ) where
  toFun Z := Matrix.of.symm (g * Matrix.of Z)
  map_add' Z W := by
    ext i j; simp [Matrix.mul_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c Z := by
    ext i j; simp [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

def rightMulLinear (g : Matrix (Fin N) (Fin N) ℂ) :
    (Fin N → Fin N → ℂ) →ₗ[ℂ] (Fin N → Fin N → ℂ) where
  toFun Z := Matrix.of.symm (Matrix.of Z * g)
  map_add' Z W := by
    ext i j; simp [Matrix.mul_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c Z := by
    ext i j; simp [Matrix.mul_apply, Finset.mul_sum]; ring_nf

theorem right_mul_map_eq_pi_toLin (g : Matrix (Fin N) (Fin N) ℂ) :
    rightMulLinear g = LinearMap.pi (fun i : Fin N => (Matrix.toLin' gᵀ).comp (LinearMap.proj i)) := by
  apply LinearMap.ext; intro Z; funext i j
  simp [rightMulLinear, Matrix.mul_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, mul_comm]

theorem det_right_mul_map_eq_det_pow (g : Matrix (Fin N) (Fin N) ℂ) :
    LinearMap.det (rightMulLinear g) = g.det ^ N := by
  rw [right_mul_map_eq_pi_toLin, LinearMap.det_pi]
  simp [LinearMap.det_toLin', Matrix.det_transpose]

def transposeLinearEquivAlt : (Fin N → Fin N → ℂ) ≃ₗ[ℂ] (Fin N → Fin N → ℂ) where
  toFun Z i j := Z j i
  invFun Z i j := Z j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem left_mul_map_eq_transpose_conj (g : Matrix (Fin N) (Fin N) ℂ) :
    leftMulLinearMap g = (transposeLinearEquivAlt (N := N)).toLinearMap ∘ₗ rightMulLinear gᵀ ∘ₗ
      (transposeLinearEquivAlt (N := N)).symm.toLinearMap := by
  apply LinearMap.ext; intro Z; funext i j
  show (∑ k, g i k * Z k j) = ∑ k, Z k j * g i k
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem det_left_mul_map_eq_det_pow (g : Matrix (Fin N) (Fin N) ℂ) :
    LinearMap.det (leftMulLinearMap g) = g.det ^ N := by
  rw [left_mul_map_eq_transpose_conj, LinearMap.det_conj, det_right_mul_map_eq_det_pow, Matrix.det_transpose]

theorem real_det_restrictScalars (f : (Fin N → Fin N → ℂ) →ₗ[ℂ] (Fin N → Fin N → ℂ)) (d : ℂ)
    (hf : LinearMap.det f = d ^ N) :
    LinearMap.det (f.restrictScalars ℝ) = (‖d‖ ^ 2) ^ N := by
  rw [LinearMap.det_restrictScalars, hf, map_pow, Algebra.norm_complex_apply,
    Complex.normSq_eq_norm_sq]

theorem zpow_neg_two_mul_eq_inv_sq_pow (x : ℝ) : x ^ (-(2 * (N : ℤ))) = ((x ^ 2) ^ N)⁻¹ := by
  rw [_root_.zpow_neg, ← pow_mul, show (2 * (N : ℤ)) = ((2 * N : ℕ) : ℤ) by push_cast; ring, zpow_natCast]

theorem map_volume_of_det_eq_pow (f : (Fin N → Fin N → ℂ) →ₗ[ℂ] (Fin N → Fin N → ℂ)) (d : ℂ) (hd : d ≠ 0)
    (hf : LinearMap.det f = d ^ N) :
    Measure.map (f.restrictScalars ℝ) volume = ENNReal.ofReal (‖d‖ ^ (-(2 * (N : ℤ)))) • volume := by
  have hdet := real_det_restrictScalars f d hf
  have hne : LinearMap.det (f.restrictScalars ℝ) ≠ 0 := by
    rw [hdet]; exact pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hd))
  haveI := matrix_space_volume_isAddHaar N
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ hne, hdet, zpow_neg_two_mul_eq_inv_sq_pow,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (sq_nonneg _) _))]

private theorem fdV0_det_cont_lemma (N : ℕ) :
    Continuous (fun Z : Fin N → Fin N → ℂ => (Matrix.of Z).det) :=
  Continuous.matrix_det (continuous_matrix fun i j => (continuous_apply j).comp (continuous_apply i))

theorem measurable_gl_density : Measurable (gmDens N) := by
  have h : gmDens N = fun Z => ENNReal.ofReal (((‖(Matrix.of Z).det‖ ^ 2) ^ N)⁻¹) := by
    funext Z; simp only [gmDens, zpow_neg_two_mul_eq_inv_sq_pow]
  rw [h]
  exact ENNReal.measurable_ofReal.comp
    (((fdV0_det_cont_lemma N).norm.measurable.pow_const 2).pow_const N).inv

theorem gl_density_left_mul (g : Matrix (Fin N) (Fin N) ℂ) (Z : Fin N → Fin N → ℂ) :
    gmDens N (Matrix.of.symm (g * Matrix.of Z)) =
      ENNReal.ofReal (‖g.det‖ ^ (-(2 * (N : ℤ)))) * gmDens N Z := by
  unfold gmDens
  rw [Equiv.apply_symm_apply, Matrix.det_mul, norm_mul, mul_zpow,
    ENNReal.ofReal_mul (zpow_nonneg (norm_nonneg _) _)]

theorem gl_density_right_mul (g : Matrix (Fin N) (Fin N) ℂ) (Z : Fin N → Fin N → ℂ) :
    gmDens N (Matrix.of.symm (Matrix.of Z * g)) =
      ENNReal.ofReal (‖g.det‖ ^ (-(2 * (N : ℤ)))) * gmDens N Z := by
  unfold gmDens
  rw [Equiv.apply_symm_apply, Matrix.det_mul, mul_comm (Matrix.of Z).det, norm_mul, mul_zpow,
    ENNReal.ofReal_mul (zpow_nonneg (norm_nonneg _) _)]

theorem map_gaussian_measure_eq {φ : (Fin N → Fin N → ℂ) → (Fin N → Fin N → ℂ)} (hφ : Measurable φ) {c : ENNReal}
    (hc0 : c ≠ 0) (hct : c ≠ ⊤) (hmap : Measure.map φ volume = c • volume)
    (hd : ∀ Z, gmDens N (φ Z) = c * gmDens N Z) : Measure.map φ (gmMeas N) = gmMeas N := by
  ext s hs
  have hD := measurable_gl_density (N := N)
  have key : ∀ Z, gmDens N Z = c⁻¹ * gmDens N (φ Z) := by
    intro Z; rw [hd, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
  have h1 : ∫⁻ Z in φ ⁻¹' s, gmDens N Z = c⁻¹ * ∫⁻ Z in φ ⁻¹' s, gmDens N (φ Z) := by
    rw [← lintegral_const_mul c⁻¹ (f := fun Z => gmDens N (φ Z)) (hD.comp hφ)]
    exact lintegral_congr fun Z => key Z
  simp only [gmMeas]
  rw [Measure.map_apply hφ hs, withDensity_apply _ (hφ hs), withDensity_apply _ hs, h1,
    ← setLIntegral_map hs hD hφ, hmap, Measure.restrict_smul, lintegral_smul_measure]
  try simp only [smul_eq_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

theorem ofReal_norm_det_zpow_ne_zero (g : Matrix (Fin N) (Fin N) ℂ) (hg : g.det ≠ 0) :
    ENNReal.ofReal (‖g.det‖ ^ (-(2 * (N : ℤ)))) ≠ 0 := by
  exact (ENNReal.ofReal_pos.mpr (zpow_pos (norm_pos_iff.mpr hg) _)).ne'

theorem map_volume_mul_left (g : Matrix (Fin N) (Fin N) ℂ) (hg : g.det ≠ 0) :
    Measure.map (fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (g * Matrix.of Z)) volume =
      ENNReal.ofReal (‖g.det‖ ^ (-(2 * (N : ℤ)))) • volume :=
  map_volume_of_det_eq_pow (leftMulLinearMap g) g.det hg (det_left_mul_map_eq_det_pow g)

theorem map_volume_mul_right (g : Matrix (Fin N) (Fin N) ℂ) (hg : g.det ≠ 0) :
    Measure.map (fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (Matrix.of Z * g)) volume =
      ENNReal.ofReal (‖g.det‖ ^ (-(2 * (N : ℤ)))) • volume :=
  map_volume_of_det_eq_pow (rightMulLinear g) g.det hg (det_right_mul_map_eq_det_pow g)

theorem gmMeas_map_mul_left (g : Matrix (Fin N) (Fin N) ℂ) (hg : g.det ≠ 0) :
    Measure.map (fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (g * Matrix.of Z)) (gmMeas N) = gmMeas N := by
  have hmeas : Measurable (fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (g * Matrix.of Z)) :=
    (leftMulLinearMap g).continuous_of_finiteDimensional.measurable
  exact map_gaussian_measure_eq hmeas (ofReal_norm_det_zpow_ne_zero g hg) ENNReal.ofReal_ne_top (map_volume_mul_left g hg)
    (gl_density_left_mul g)

theorem gmMeas_map_mul_right (g : Matrix (Fin N) (Fin N) ℂ) (hg : g.det ≠ 0) :
    Measure.map (fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (Matrix.of Z * g)) (gmMeas N) = gmMeas N := by
  have hmeas : Measurable (fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (Matrix.of Z * g)) :=
    (rightMulLinear g).continuous_of_finiteDimensional.measurable
  exact map_gaussian_measure_eq hmeas (ofReal_norm_det_zpow_ne_zero g hg) ENNReal.ofReal_ne_top (map_volume_mul_right g hg)
    (gl_density_right_mul g)

theorem gmMeas_compact_lt_top (K : Set (Fin N → Fin N → ℂ)) (hK : IsCompact K)
    (hK0 : ∀ Z ∈ K, (Matrix.of Z).det ≠ 0) : gmMeas N K < ⊤ := by
  have hcont : ContinuousOn
      (fun Z : Fin N → Fin N → ℂ => ‖(Matrix.of Z).det‖ ^ (-(2 * (N : ℤ)))) K :=
    ((fdV0_det_cont_lemma N).norm.continuousOn).zpow₀ _
      fun Z hZ => Or.inl (norm_ne_zero_iff.mpr (hK0 Z hZ))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  have hDle : ∀ Z ∈ K, gmDens N Z ≤ ENNReal.ofReal C := fun Z hZ =>
    ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hC Z hZ))
  simp only [gmMeas]
  rw [withDensity_apply _ hK.measurableSet]
  calc ∫⁻ Z in K, gmDens N Z ≤ ∫⁻ _ in K, ENNReal.ofReal C :=
        lintegral_mono_ae (ae_restrict_of_forall_mem hK.measurableSet hDle)
    _ = ENNReal.ofReal C * volume K := setLIntegral_const K _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.QRHaarA
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.QRH

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

def qrDom (N : ℕ) : Set (UNgrp N × TriCo N) := Set.univ ×ˢ triPos N

def glSet (N : ℕ) : Set (Fin N → Fin N → ℂ) := {Z | (Matrix.of Z).det ≠ 0}

theorem measurableSet_triPos : MeasurableSet (triPos N) := by
  unfold triPos
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun j =>
    measurableSet_lt measurable_const ((measurable_pi_apply j).comp measurable_fst)

theorem measurableSet_qrDom : MeasurableSet (qrDom N) :=
  MeasurableSet.univ.prod measurableSet_triPos

theorem continuous_det_of : Continuous fun Z : Fin N → Fin N → ℂ => (Matrix.of Z).det :=
  show Continuous fun Z : Matrix (Fin N) (Fin N) ℂ => Z.det from continuous_id.matrix_det

theorem measurableSet_glSet : MeasurableSet (glSet N) :=
  (isOpen_ne_fun continuous_det_of continuous_const).measurableSet

theorem measurable_qrMap : Measurable (qrMap (N := N)) := qrMap_continuous.measurable

def qrW (p : qrDom N) : Fin N → Fin N → ℂ := qrMap p.1

theorem range_qrW : Set.range (qrW (N := N)) = glSet N := by
  rw [show Set.range (qrW (N := N)) = qrMap '' qrDom N by
    ext Z; constructor
    · rintro ⟨p, rfl⟩; exact ⟨p.1, p.2, rfl⟩
    · rintro ⟨p, hp, rfl⟩; exact ⟨⟨p, hp⟩, rfl⟩]
  exact qrMap_image

theorem measurableEmbedding_qrW : MeasurableEmbedding (qrW (N := N)) := by
  refine ⟨?_, measurable_qrMap.comp measurable_subtype_coe, ?_⟩
  · intro p q h
    exact Subtype.ext (qrMap_injOn p.2 q.2 h)
  · intro s hs
    have h1 : MeasurableSet (Subtype.val '' s : Set (UNgrp N × TriCo N)) :=
      (MeasurableEmbedding.subtype_coe measurableSet_qrDom).measurableSet_image' hs
    have h2 : qrW '' s = qrMap '' (Subtype.val '' s) := by
      rw [Set.image_image]; rfl
    rw [h2]
    refine qrMap_measurableSet_image _ h1 ?_
    rintro _ ⟨p, _, rfl⟩
    exact p.2

def nuW (N : ℕ) : Measure (qrDom N) := (gmMeas N).comap qrW

def nuQR (N : ℕ) : Measure (UNgrp N × TriCo N) := (nuW N).map Subtype.val

theorem map_qrW_nuW : (nuW N).map qrW = (gmMeas N).restrict (glSet N) := by
  rw [nuW, measurableEmbedding_qrW.map_comap, range_qrW]

theorem map_qrMap_nuQR : (nuQR N).map qrMap = (gmMeas N).restrict (glSet N) := by
  rw [nuQR, Measure.map_map measurable_qrMap measurable_subtype_coe]
  exact map_qrW_nuW

theorem nuQR_apply (s : Set (UNgrp N × TriCo N)) (hs : MeasurableSet s) :
    nuQR N s = gmMeas N (qrW '' (Subtype.val ⁻¹' s)) := by
  rw [nuQR, Measure.map_apply measurable_subtype_coe hs, nuW, measurableEmbedding_qrW.comap_apply]

theorem nuQR_map_eq (φ : UNgrp N × TriCo N → UNgrp N × TriCo N) (hφ : Measurable φ)
    (hφW : ∀ p ∈ qrDom N, φ p ∈ qrDom N) (ψ : (Fin N → Fin N → ℂ) → (Fin N → Fin N → ℂ))
    (hψ : Measurable ψ) (hψm : (gmMeas N).map ψ = gmMeas N) (hψG : ψ ⁻¹' glSet N = glSet N)
    (hcomm : ∀ p ∈ qrDom N, qrMap (φ p) = ψ (qrMap p)) :
    (nuQR N).map φ = nuQR N := by
  let φW : qrDom N → qrDom N := fun p => ⟨φ p.1, hφW p.1 p.2⟩
  have hφWm : Measurable φW := (hφ.comp measurable_subtype_coe).subtype_mk
  have key : (nuW N).map φW = nuW N := by
    have h1 : ((nuW N).map φW).map qrW = (nuW N).map qrW := by
      rw [Measure.map_map measurableEmbedding_qrW.measurable hφWm]
      have hc : qrW ∘ φW = ψ ∘ qrW := by
        funext p; exact hcomm p.1 p.2
      rw [hc, ← Measure.map_map hψ measurableEmbedding_qrW.measurable, map_qrW_nuW]
      conv_lhs => rw [← hψG]
      rw [← Measure.restrict_map hψ measurableSet_glSet, hψm]
    have h2 := congrArg (fun m => m.comap qrW) h1
    simp only [measurableEmbedding_qrW.comap_map] at h2
    exact h2
  rw [nuQR, Measure.map_map hφ measurable_subtype_coe]
  have : φ ∘ Subtype.val = Subtype.val ∘ φW := rfl
  rw [this, ← Measure.map_map measurable_subtype_coe hφWm, key]

theorem det_toM_ne_zero (k : UNgrp N) : (toM k).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (k : (Matrix (Fin N) (Fin N) ℂ)ˣ).isUnit).ne_zero

theorem det_upMat (t : TriCo N) : (upMat t).det = ∏ j, ((t.1 j : ℝ) : ℂ) := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [upMat]
  · intro a b hba
    have h1 : a ≠ b := ne_of_gt hba
    have h2 : ¬ a < b := not_lt.mpr (le_of_lt hba)
    simp [upMat, h1, h2]

theorem det_upMat_ne_zero (t : TriCo N) (ht : t ∈ triPos N) : (upMat t).det ≠ 0 := by
  rw [det_upMat]
  exact Finset.prod_ne_zero_iff.mpr fun j _ => by
    exact_mod_cast (ne_of_gt (ht j))

theorem continuous_upMat : Continuous (upMat (N := N)) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [upMat]
  split_ifs with h1 h2
  · exact Complex.continuous_ofReal.comp ((continuous_apply a).comp continuous_fst)
  · exact (continuous_apply _).comp continuous_snd
  · exact continuous_const

theorem continuous_triCoOf : Continuous (triCoOf (N := N)) := by
  refine Continuous.prodMk (continuous_pi fun j => ?_) (continuous_pi fun ab => ?_)
  · exact Complex.continuous_re.comp ((continuous_apply j).comp (continuous_apply j))
  · exact (continuous_apply _).comp (continuous_apply _)

def triR (t0 : TriCo N) (t : TriCo N) : TriCo N := triCoOf (upMat t * upMat t0)

theorem continuous_triR (t0 : TriCo N) : Continuous (triR t0) :=
  continuous_triCoOf.comp (continuous_upMat.matrix_mul continuous_const)

theorem measurable_mulLeft_mat (g : Matrix (Fin N) (Fin N) ℂ) :
    Measurable fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (g * Matrix.of Z) := by
  have hc : Continuous fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (g * Matrix.of Z) := by
    exact (continuous_const.matrix_mul continuous_id : Continuous fun Z : Matrix (Fin N) (Fin N) ℂ => g * Z)
  exact hc.measurable

theorem measurable_mulRight_mat (g : Matrix (Fin N) (Fin N) ℂ) :
    Measurable fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (Matrix.of Z * g) := by
  have hc : Continuous fun Z : Fin N → Fin N → ℂ => Matrix.of.symm (Matrix.of Z * g) := by
    exact (continuous_id.matrix_mul continuous_const : Continuous fun Z : Matrix (Fin N) (Fin N) ℂ => Z * g)
  exact hc.measurable

theorem nuQR_map_left (k0 : UNgrp N) :
    (nuQR N).map (fun p : UNgrp N × TriCo N => (k0 * p.1, p.2)) = nuQR N := by
  refine nuQR_map_eq _ ((measurable_const_mul k0).comp measurable_fst |>.prodMk measurable_snd)
    (fun p hp => ⟨trivial, hp.2⟩) (fun Z => Matrix.of.symm (toM k0 * Matrix.of Z))
    (measurable_mulLeft_mat _) (gmMeas_map_mul_left _ (det_toM_ne_zero k0)) ?_ ?_
  · ext Z
    simp only [glSet, Set.mem_preimage, Set.mem_ofPred_eq]
    change (toM k0 * Matrix.of Z).det ≠ 0 ↔ _
    rw [Matrix.det_mul]
    exact ⟨fun h => right_ne_zero_of_mul h, fun h => mul_ne_zero (det_toM_ne_zero k0) h⟩
  · intro p _
    simp only [qrMap]
    change Matrix.of.symm (toM (k0 * p.1) * upMat p.2) = Matrix.of.symm (toM k0 * (toM p.1 * upMat p.2))
    rw [← Matrix.mul_assoc]; rfl

theorem nuQR_map_right (t0 : TriCo N) (h0 : t0 ∈ triPos N) :
    (nuQR N).map (fun p : UNgrp N × TriCo N => (p.1, triR t0 p.2)) = nuQR N := by
  refine nuQR_map_eq _ (measurable_fst.prodMk ((continuous_triR t0).measurable.comp measurable_snd))
    ?_ (fun Z => Matrix.of.symm (Matrix.of Z * upMat t0))
    (measurable_mulRight_mat _) (gmMeas_map_mul_right _ (det_upMat_ne_zero t0 h0)) ?_ ?_
  · intro p hp
    refine ⟨trivial, fun j => ?_⟩
    change 0 < (triR t0 p.2).1 j
    rw [triR, (upMat_triCoOf_mul p.2 t0).2 j]
    exact mul_pos (hp.2 j) (h0 j)
  · ext Z
    simp only [glSet, Set.mem_preimage, Set.mem_ofPred_eq]
    change (Matrix.of Z * upMat t0).det ≠ 0 ↔ _
    rw [Matrix.det_mul]
    exact ⟨fun h => left_ne_zero_of_mul h, fun h => mul_ne_zero h (det_upMat_ne_zero t0 h0)⟩
  · intro p _
    simp only [qrMap, triR]
    rw [(upMat_triCoOf_mul p.2 t0).1]
    change Matrix.of.symm (toM p.1 * (upMat p.2 * upMat t0)) = Matrix.of.symm ((toM p.1 * upMat p.2) * upMat t0)
    rw [Matrix.mul_assoc]

def kap (N : ℕ) : Measure (TriCo N) := (nuQR N).map Prod.snd

theorem kap_compl : kap N (triPos N)ᶜ = 0 := by
  rw [kap, Measure.map_apply measurable_snd measurableSet_triPos.compl,
    nuQR_apply _ (measurable_snd measurableSet_triPos.compl)]
  have : (Subtype.val ⁻¹' (Prod.snd ⁻¹' (triPos N)ᶜ) : Set (qrDom N)) = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun p hp => hp p.2.2
  rw [this, Set.image_empty, measure_empty]

theorem kap_compact [CompactSpace (UNgrp N)] (K : Set (TriCo N)) (hK : IsCompact K)
    (hKs : K ⊆ triPos N) : kap N K < ⊤ := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  rw [kap, Measure.map_apply measurable_snd hKm, nuQR_apply _ (measurable_snd hKm)]
  refine lt_of_le_of_lt (measure_mono ?_) (gmMeas_compact_lt_top (qrMap '' (Set.univ ×ˢ K))
    ((isCompact_univ.prod hK).image qrMap_continuous) ?_)
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨p.1, ⟨trivial, hp⟩, rfl⟩
  · rintro _ ⟨p, hp, rfl⟩
    have : qrMap p ∈ qrMap '' (Set.univ ×ˢ triPos N) := ⟨p, ⟨trivial, hKs hp.2⟩, rfl⟩
    rw [qrMap_image] at this
    exact this

theorem kap_inv (t0 : TriCo N) (h0 : t0 ∈ triPos N) : (kap N).map (triR t0) = kap N := by
  have hm : Measurable fun p : UNgrp N × TriCo N => (p.1, triR t0 p.2) :=
    measurable_fst.prodMk ((continuous_triR t0).measurable.comp measurable_snd)
  rw [kap, Measure.map_map (continuous_triR t0).measurable measurable_snd]
  have : triR t0 ∘ Prod.snd = Prod.snd ∘ (fun p : UNgrp N × TriCo N => (p.1, triR t0 p.2)) := rfl
  rw [this, ← Measure.map_map measurable_snd hm, nuQR_map_right t0 h0]

theorem kap_eq [CompactSpace (UNgrp N)] : ∃ c : ENNReal, c ≠ ⊤ ∧ kap N = c • triMeas N :=
  triMeas_unique (kap N) kap_compl kap_compact (fun t0 h0 => kap_inv t0 h0)

theorem nuQR_rect (μ : Measure (UNgrp N)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    [CompactSpace (UNgrp N)] (s : Set (UNgrp N)) (hs : MeasurableSet s) (t : Set (TriCo N))
    (ht : MeasurableSet t) (hfin : kap N t < ⊤) : nuQR N (s ×ˢ t) = μ s * kap N t := by
  set ρ : Measure (UNgrp N) := ((nuQR N).restrict (Prod.snd ⁻¹' t)).map Prod.fst with hρ
  have hρA : ∀ A, MeasurableSet A → ρ A = nuQR N (A ×ˢ t) := by
    intro A hA
    rw [hρ, Measure.map_apply measurable_fst hA, Measure.restrict_apply (measurable_fst hA)]
    rfl
  have hρu : ρ Set.univ = kap N t := by
    rw [hρA _ MeasurableSet.univ, kap, Measure.map_apply measurable_snd ht, Set.univ_prod]
  have : IsFiniteMeasure ρ := ⟨by rw [hρu]; exact hfin⟩
  have : ρ.IsMulLeftInvariant := ⟨fun g => by
    have hL : Measurable fun p : UNgrp N × TriCo N => (g * p.1, p.2) :=
      ((measurable_const_mul g).comp measurable_fst).prodMk measurable_snd
    rw [hρ, Measure.map_map (measurable_const_mul g) measurable_fst]
    have : (fun x => g * x) ∘ Prod.fst =
        Prod.fst ∘ (fun p : UNgrp N × TriCo N => (g * p.1, p.2)) := rfl
    rw [this, ← Measure.map_map measurable_fst hL]
    congr 1
    have := Measure.restrict_map (μ := nuQR N) hL (measurable_snd ht)
    rw [nuQR_map_left] at this
    exact this.symm⟩
  have hsm := Measure.isMulInvariant_eq_smul_of_compactSpace ρ μ
  have hc : ρ.haarScalarFactor μ = kap N t := by
    have := congrArg (fun m : Measure (UNgrp N) => m Set.univ) hsm
    simp only [smul_apply, measure_univ] at this
    rw [← hρu, this]
    simp
  rw [← hρA s hs, hsm, smul_apply, ENNReal.smul_def, smul_eq_mul, hc, mul_comm]

theorem nuQR_eq_prod (μ : Measure (UNgrp N)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    [CompactSpace (UNgrp N)] [SigmaFinite (kap N)] : μ.prod (kap N) = nuQR N := by
  refine Measure.prod_eq_generateFrom (C := {s | MeasurableSet s})
    (D := {t | MeasurableSet t ∧ kap N t < ⊤}) MeasurableSpace.generateFrom_measurableSet ?_
    MeasurableSpace.isPiSystem_measurableSet ?_ μ.toFiniteSpanningSetsIn
    ((kap N).toFiniteSpanningSetsIn.mono' fun t ht => ⟨ht.1, ht.2⟩) ?_
  · refine le_antisymm (MeasurableSpace.generateFrom_le fun t ht => ht.1) fun t ht => ?_
    rw [← Set.inter_univ t, ← iUnion_spanningSets (kap N), Set.inter_iUnion]
    exact MeasurableSet.iUnion fun n => MeasurableSpace.measurableSet_generateFrom
      ⟨ht.inter (measurableSet_spanningSets (kap N) n),
        lt_of_le_of_lt (measure_mono Set.inter_subset_right) (measure_spanningSets_lt_top (kap N) n)⟩
  · intro s hs t ht _
    exact ⟨hs.1.inter ht.1, lt_of_le_of_lt (measure_mono Set.inter_subset_left) hs.2⟩
  · intro s hs t ht
    exact nuQR_rect μ s hs t ht.1 ht.2

theorem norm_det_toM (k : UNgrp N) : ‖(toM k).det‖ = 1 := by
  have hk : inUJ (fun _ : Fin N => true) (toM k) := k.2
  have hJ : Jm (fun _ : Fin N => true) = 1 := by
    unfold Jm; simp
  unfold inUJ at hk
  rw [hJ, Matrix.mul_one] at hk
  have h1 := congrArg Matrix.det hk
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h1
  have h2 : Complex.normSq (toM k).det = 1 := by
    have h3 := Complex.normSq_eq_conj_mul_self (z := (toM k).det)
    have h4 : ((Complex.normSq (toM k).det : ℝ) : ℂ) = 1 := by rw [h3]; exact h1
    exact_mod_cast h4
  have h5 : ‖(toM k).det‖ ^ 2 = 1 := by rw [Complex.sq_norm, h2]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h5

theorem gmDens_mul (Z : Fin N → Fin N → ℂ) (hZ : Z ∈ glSet N) :
    gmDens N Z * ENNReal.ofReal (‖(Matrix.of Z).det‖ ^ (2 * N)) = 1 := by
  have hn : ‖(Matrix.of Z).det‖ ≠ 0 := norm_ne_zero_iff.mpr hZ
  rw [gmDens, ← ENNReal.ofReal_mul (zpow_nonneg (norm_nonneg _) _), ← zpow_natCast,
    ← zpow_add₀ hn]
  push_cast
  simp

theorem triDens_mul (t : TriCo N) (ht : t ∈ triPos N) :
    triDens t * ENNReal.ofReal ((∏ j, t.1 j) ^ (2 * N)) = ENNReal.ofReal (qrWt t) := by
  have hpos : ∀ j, 0 ≤ t.1 j ^ (-(2 * ((j : ℕ) : ℤ) + 1)) := fun j => zpow_nonneg (ht j).le _
  rw [triDens, ← ENNReal.ofReal_mul (Finset.prod_nonneg fun j _ => hpos j), ← Finset.prod_pow,
    ← Finset.prod_mul_distrib, qrWt]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  have hj := j.2
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (ne_of_gt (ht j))]
  congr 1
  omega

theorem d_qrMap (k : UNgrp N) (t : TriCo N) (ht : t ∈ triPos N) :
    ENNReal.ofReal (‖(Matrix.of (qrMap (k, t))).det‖ ^ (2 * N)) =
      ENNReal.ofReal ((∏ j, t.1 j) ^ (2 * N)) := by
  congr 2
  have : Matrix.of (qrMap (k, t)) = toM k * upMat t := by
    exact Matrix.of.apply_symm_apply _
  rw [this, Matrix.det_mul, norm_mul, norm_det_toM, one_mul, det_upMat, norm_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Complex.norm_real, Real.norm_of_nonneg (ht j).le]

end ReciprocityTheory.ChartRestriction.DS.QRH
end
end

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.QRH

variable {N : ℕ}

theorem qr_lintegral (μ : Measure (UNgrp N)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] :
    ∃ C : ℝ, 0 < C ∧ ∀ f : (Fin N → Fin N → ℂ) → ENNReal, Measurable f →
      ∫⁻ Z, f Z = ENNReal.ofReal C * ∫⁻ k, (∫⁻ t in triPos N, f (qrMap (k, t)) * ENNReal.ofReal (qrWt t)) ∂μ := by
  haveI hcpt : CompactSpace (UNgrp N) := by
    by_contra hnc
    rw [not_compactSpace_iff] at hnc
    have h1 := MeasureTheory.measure_univ_of_isMulLeftInvariant μ
    rw [measure_univ] at h1
    exact ENNReal.one_ne_top h1
  obtain ⟨c, hct, hkap⟩ := kap_eq (N := N)
  haveI : SigmaFinite (triMeas N) := by
    unfold triMeas triDens
    infer_instance
  haveI : SigmaFinite (kap N) := by
    rw [hkap]
    lift c to NNReal using hct
    show SigmaFinite (c • triMeas N)
    infer_instance
  have hprod := nuQR_eq_prod (N := N) μ
  have hcd : Continuous fun Z : Fin N → Fin N → ℂ => (Matrix.of Z).det :=
    Continuous.matrix_det (continuous_id : Continuous fun Z : Fin N → Fin N → ℂ => Matrix.of Z)
  have hdet : Measurable fun Z : Fin N → Fin N → ℂ => ENNReal.ofReal (‖(Matrix.of Z).det‖ ^ (2 * N)) :=
    ((hcd.norm.pow _).measurable).ennreal_ofReal
  have hgm : Measurable (gmDens N) := by
    have he : gmDens N = fun Z => ENNReal.ofReal ((‖(Matrix.of Z).det‖ ^ (2 * N))⁻¹) := by
      funext Z
      unfold gmDens
      rw [_root_.zpow_neg, show (2 * (N : ℤ)) = ((2 * N : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    rw [he]
    exact ((hcd.norm.pow _).measurable.inv).ennreal_ofReal
  have htd : Measurable (triDens (N := N)) := by
    unfold triDens
    first
    | fun_prop
    | measurability
  have key : ∀ f : (Fin N → Fin N → ℂ) → ENNReal, Measurable f →
      ∫⁻ Z, f Z = c * ∫⁻ k, (∫⁻ t in triPos N, f (qrMap (k, t)) * ENNReal.ofReal (qrWt t)) ∂μ := by
    intro f hf
    have hg : Measurable fun Z => f Z * ENNReal.ofReal (‖(Matrix.of Z).det‖ ^ (2 * N)) := hf.mul hdet
    have hgq : Measurable fun p : UNgrp N × TriCo N =>
        f (qrMap p) * ENNReal.ofReal (‖(Matrix.of (qrMap p)).det‖ ^ (2 * N)) := hg.comp measurable_qrMap
    have s1 : ∫⁻ Z, f Z = ∫⁻ Z in glSet N, f Z := by
      rw [← lintegral_add_compl f (measurableSet_glSet (N := N))]
      have hc : (glSet N)ᶜ = {Z : Fin N → Fin N → ℂ | (Matrix.of Z).det = 0} := by
        ext Z
        simp [glSet]
      rw [hc, setLIntegral_measure_zero _ _ volume_det_eq_zero, add_zero]
    have s2 : ∫⁻ Z in glSet N, f Z =
        ∫⁻ Z, f Z * ENNReal.ofReal (‖(Matrix.of Z).det‖ ^ (2 * N)) ∂((gmMeas N).restrict (glSet N)) := by
      unfold gmMeas
      rw [restrict_withDensity measurableSet_glSet, lintegral_withDensity_eq_lintegral_mul _ hgm hg]
      apply setLIntegral_congr_fun measurableSet_glSet
      intro Z hZ
      simp only [Pi.mul_apply]
      rw [mul_comm (f Z), ← mul_assoc, gmDens_mul Z hZ, one_mul]
    rw [s1, s2, ← map_qrMap_nuQR, lintegral_map hg measurable_qrMap, ← hprod,
      lintegral_prod _ hgq.aemeasurable, ← lintegral_const_mul' _ _ hct]
    apply lintegral_congr
    intro k
    rw [hkap, lintegral_smul_measure]
    congr 1
    unfold triMeas
    rw [lintegral_withDensity_eq_lintegral_mul _ htd (by
      first
      | exact hgq.comp measurable_prodMk_left
      | exact hgq.comp measurable_prod_mk_left)]
    apply setLIntegral_congr_fun measurableSet_triPos
    intro t ht
    simp only [Pi.mul_apply]
    rw [d_qrMap k t ht, mul_comm, mul_assoc, mul_comm _ (triDens t), triDens_mul t ht]
  have hc0 : c ≠ 0 := by
    intro h0
    have h1 := key (fun _ => 1) measurable_const
    rw [h0, zero_mul, lintegral_const, one_mul] at h1
    have hv : (volume : Measure (Fin N → Fin N → ℂ)) Set.univ ≠ 0 := by
      rw [MeasureTheory.volume_pi, Measure.pi_univ, Finset.prod_ne_zero_iff]
      intro i _
      rw [MeasureTheory.volume_pi, Measure.pi_univ, Finset.prod_ne_zero_iff]
      intro j _
      exact isOpen_univ.measure_ne_zero volume Set.univ_nonempty
    exact hv h1
  refine ⟨c.toReal, ENNReal.toReal_pos hc0 hct, ?_⟩
  intro f hf
  rw [ENNReal.ofReal_toReal hct]
  exact key f hf

end ReciprocityTheory.ChartRestriction.DS
