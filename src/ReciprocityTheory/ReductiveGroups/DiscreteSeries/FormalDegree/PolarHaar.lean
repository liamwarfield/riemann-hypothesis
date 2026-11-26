module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ProdShcSqEqJacPow
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.JacBound

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarRight
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CorePInvInUJ
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.JacAll
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.JacBaseA
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace Topology

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

namespace JacB

section Gen

variable {E 𝔸 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
  [CompleteSpace 𝔸]

theorem contDiff_exp_alg : ContDiff ℝ 1 (NormedSpace.exp : 𝔸 → 𝔸) := by
  first
  | exact contDiff_exp
  | exact NormedSpace.contDiff_exp
  | exact (NormedSpace.analyticOnNhd_exp (𝕂 := ℝ)).contDiff
  | exact (analyticOnNhd_exp (𝕂 := ℝ)).contDiff
  | exact contDiff_iff_contDiffAt.mpr fun x =>
      (analyticAt_exp_of_mem_ball (𝕂 := ℝ) x (by simp [expSeries_radius_eq_top])).contDiffAt
  | exact contDiff_iff_contDiffAt.mpr fun x =>
      (NormedSpace.analyticAt_exp_of_mem_ball (𝕂 := ℝ) x (by simp [NormedSpace.expSeries_radius_eq_top])).contDiffAt

theorem hasFDerivAt_exp_alg (x : 𝔸) :
    HasFDerivAt (NormedSpace.exp : 𝔸 → 𝔸) (fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) x) x := by
  first
  | exact ((contDiff_exp_alg (𝔸 := 𝔸)).differentiable one_ne_zero x).hasFDerivAt
  | exact ((contDiff_exp_alg (𝔸 := 𝔸)).differentiable le_rfl x).hasFDerivAt

theorem fderiv_exp_eq {x W D : 𝔸} (h : HasDerivAt (fun s : ℝ => NormedSpace.exp (x + s • W)) D 0) :
    fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) x W = D := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • W) W 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const W).const_add x
  have h2 := (hasFDerivAt_exp_alg (x + (0 : ℝ) • W)).comp_hasDerivAt (0 : ℝ) h1
  rw [zero_smul, add_zero] at h2
  exact h2.unique h

theorem contDiffAt_of_exp [FiniteDimensional ℝ 𝔸] {f : E → 𝔸} {z : E} (hf : ContinuousAt f z)
    (hg : ContDiffAt ℝ 1 (fun w => NormedSpace.exp (f w)) z)
    (hi : Function.Injective (fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) (f z))) :
    ContDiffAt ℝ 1 f z := by
  let e : 𝔸 ≃L[ℝ] 𝔸 :=
    (LinearEquiv.ofInjectiveEndo
      (fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) (f z) : 𝔸 →ₗ[ℝ] 𝔸) hi).toContinuousLinearEquiv
  have he : (e : 𝔸 →L[ℝ] 𝔸) = fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) (f z) := by
    ext v; rfl
  have hd : HasFDerivAt (NormedSpace.exp : 𝔸 → 𝔸) (e : 𝔸 →L[ℝ] 𝔸) (f z) := by
    rw [he]; exact hasFDerivAt_exp_alg _
  have hc : ContDiffAt ℝ 1 (NormedSpace.exp : 𝔸 → 𝔸) (f z) := contDiff_exp_alg.contDiffAt
  have h1 := hc.to_localInverse hd one_ne_zero
  have h2 := (hc.hasStrictFDerivAt' hd one_ne_zero).eventually_left_inverse
  have h3 := ContDiffAt.comp z (g := hc.localInverse hd one_ne_zero) h1 hg
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [hf.eventually h2] with w hw
  exact hw.symm

end Gen

variable {n : ℕ}

theorem shc_pos' (u : ℝ) : 0 < shc u := by
  unfold shc
  split_ifs with h
  · exact one_pos
  · rcases lt_or_gt_of_ne h with hu | hu
    · exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr hu) hu
    · exact div_pos (Real.sinh_pos_iff.mpr hu) hu

theorem jac_pos' {ε : Fin n → Bool} (y : PCoord ε → ℂ) : 0 < Jac y := by
  unfold Jac
  exact Finset.prod_pos (fun a _ => Finset.prod_pos (fun b _ => shc_pos' _))

def pmatLin (ε : Fin n → Bool) : (PCoord ε → ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := pmat
  map_add' z w := by
    ext a b
    simp only [pmat, Matrix.add_apply]
    split_ifs <;> simp
  map_smul' c z := by
    ext a b
    simp only [pmat, Matrix.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

def crdLin (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (PCoord ε → ℂ) where
  toFun X := fun ab => X ab.1.1 ab.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem crd_pmat {ε : Fin n → Bool} (z : PCoord ε → ℂ) : crdLin ε (pmat z) = z := by
  funext ab
  show pmat z ab.1.1 ab.1.2 = z ab
  simp only [pmat]
  rw [dite_eq_left ab.2]

def shcAdLin {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := shcAd y
  map_add' V W := by
    unfold shcAd
    rw [← Matrix.add_mul, ← Matrix.mul_add]
    congr 2
    ext i j
    simp only [Matrix.add_mul, Matrix.add_apply, Matrix.of_apply, mul_add]
  map_smul' c W := by
    unfold shcAd
    rw [RingHom.id_apply, ← Matrix.smul_mul, ← Matrix.mul_smul]
    congr 2
    ext i j
    simp only [Matrix.smul_mul, Matrix.smul_apply, Matrix.of_apply, mul_smul_comm]

theorem shcAd_eq_zero {ε : Fin n → Bool} (y : PCoord ε → ℂ) {W : Matrix (Fin n) (Fin n) ℂ}
    (h : shcAd y W = 0) : W = 0 := by
  unfold shcAd at h
  set U : Matrix (Fin n) (Fin n) ℂ :=
    ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have h1 : Uᴴ * U = 1 := (pmat_isHermitian y).eigenvectorUnitary.2.1
  have h2 : U * Uᴴ = 1 := (pmat_isHermitian y).eigenvectorUnitary.2.2
  set S := Matrix.of (fun i j => ((shc (pev y i - pev y j) : ℝ) : ℂ) * (Uᴴ * W * U) i j) with hS
  have h3 : S = 0 := by
    have : Uᴴ * (U * S * Uᴴ) * U = S := by
      calc Uᴴ * (U * S * Uᴴ) * U = (Uᴴ * U) * S * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
        _ = S := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    rw [← this, h, Matrix.mul_zero, Matrix.zero_mul]
  have h4 : Uᴴ * W * U = 0 := by
    ext i j
    have h5 : S i j = 0 := by rw [h3]; rfl
    rw [hS, Matrix.of_apply, mul_eq_zero] at h5
    rcases h5 with h5 | h5
    · exact absurd (Complex.ofReal_eq_zero.1 h5) (shc_pos' _).ne'
    · exact h5
  calc W = (U * Uᴴ) * W * (U * Uᴴ) := by rw [h2, Matrix.one_mul, Matrix.mul_one]
    _ = U * (Uᴴ * W * U) * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h4, Matrix.mul_zero, Matrix.zero_mul]

theorem exp_two (X : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp ((2 : ℝ) • X) = NormedSpace.exp X * NormedSpace.exp X := by
  rw [two_smul]
  first
  | exact Matrix.exp_add_of_commute _ _ (Commute.refl X)
  | exact Matrix.exp_add_of_commute (Commute.refl X)
  | exact NormedSpace.exp_add_of_commute (Commute.refl X)

theorem exp_two_actR {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g)
    (z : PCoord ε → ℂ) :
    NormedSpace.exp ((2 : ℝ) • pmat (actR g z)) = gᴴ * NormedSpace.exp ((2 : ℝ) • pmat z) * g := by
  obtain ⟨k, hk⟩ := actR_spec hg z
  have hk1 : (toMK k)ᴴ * toMK k = 1 := k.2.1.1
  have hz : (NormedSpace.exp (pmat z))ᴴ = NormedSpace.exp (pmat z) := (pmat_isHermitian z).exp
  have hw : (NormedSpace.exp (pmat (actR g z)))ᴴ = NormedSpace.exp (pmat (actR g z)) :=
    (pmat_isHermitian _).exp
  have h1 : (NormedSpace.exp (pmat z) * g)ᴴ * (NormedSpace.exp (pmat z) * g) =
      (toMK k * NormedSpace.exp (pmat (actR g z)))ᴴ * (toMK k * NormedSpace.exp (pmat (actR g z))) := by
    rw [hk]; rfl
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hz, hw, Matrix.mul_assoc _ (toMK k)ᴴ,
    ← Matrix.mul_assoc (toMK k)ᴴ, hk1, Matrix.one_mul] at h1
  rw [exp_two, exp_two, ← h1]
  simp only [Matrix.mul_assoc]

section Op

open scoped Matrix.Norms.Operator

def pmatC (ε : Fin n → Bool) : (PCoord ε → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (pmatLin ε)

def crdC (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (PCoord ε → ℂ) :=
  LinearMap.toContinuousLinearMap (crdLin ε)

theorem pmat_contDiff (ε : Fin n → Bool) : ContDiff ℝ 1 (fun z : PCoord ε → ℂ => pmat z) := by
  first
  | exact (pmatC ε).contDiff
  | exact ContinuousLinearMap.contDiff (pmatC ε)

theorem actR_continuous {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Continuous (actR (ε := ε) g) := by
  choose k hk using actR_spec hg
  have h1 : Continuous (fun z => (k z, actR g z)) := by
    rw [(polarM_isClosedEmbedding ε).isEmbedding.continuous_iff]
    have h2 : (polarM ∘ fun z => (k z, actR g z)) = fun z => NormedSpace.exp (pmat z) * g := by
      funext z; exact (hk z).symm
    rw [h2]
    exact ((contDiff_exp_alg.comp (pmat_contDiff ε)).mul contDiff_const).continuous
  exact continuous_snd.comp h1

theorem fderiv_exp_two {ε : Fin n → Bool} (y : PCoord ε → ℂ) (W : Matrix (Fin n) (Fin n) ℂ) :
    fderiv ℝ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((2 : ℝ) • pmat y) W = NormedSpace.exp (pmat y) * shcAd y W * NormedSpace.exp (pmat y) := by
  apply fderiv_exp_eq
  have h := hasDerivAt_exp_two y W
  have e : (fun s : ℝ => NormedSpace.exp ((2 : ℂ) • pmat y + (s : ℂ) • W)) =
      fun s : ℝ => NormedSpace.exp ((2 : ℝ) • pmat y + s • W) := by
    funext s
    rw [two_smul, two_smul, Complex.coe_smul]
  rw [e] at h
  exact h

theorem conj_cancel {A B X : Matrix (Fin n) (Fin n) ℂ}
    (h : NormedSpace.exp X * A * NormedSpace.exp X = NormedSpace.exp X * B * NormedSpace.exp X) :
    A = B := by
  have hu : IsUnit (NormedSpace.exp X) := Matrix.isUnit_exp X
  exact hu.mul_left_cancel (hu.mul_right_cancel h)

theorem fderiv_exp_two_inj {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    Function.Injective (fderiv ℝ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((2 : ℝ) • pmat y)) := by
  intro W1 W2 hW
  have h0 : fderiv ℝ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((2 : ℝ) • pmat y) (W1 - W2) = 0 := by
    rw [map_sub, hW, sub_self]
  rw [fderiv_exp_two] at h0
  have h1 : shcAd y (W1 - W2) = 0 :=
    conj_cancel (X := pmat y) (by rw [h0, Matrix.mul_zero, Matrix.zero_mul])
  exact sub_eq_zero.mp (shcAd_eq_zero y h1)

theorem actR_contDiff' {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    ContDiff ℝ 1 (actR (ε := ε) g) := by
  have h1 : ContDiff ℝ 1 (fun z : PCoord ε → ℂ => (2 : ℝ) • pmat (actR g z)) := by
    refine contDiff_iff_contDiffAt.2 fun z => contDiffAt_of_exp ?_ ?_ (fderiv_exp_two_inj _)
    · exact (((pmat_contDiff ε).continuous.comp (actR_continuous hg)).const_smul (2 : ℝ)).continuousAt
    · exact (((contDiff_const (c := gᴴ)).mul
        (contDiff_exp_alg.comp ((pmat_contDiff ε).const_smul (2 : ℝ)))).mul
        (contDiff_const (c := g))).contDiffAt.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun w => exp_two_actR hg w)
  have h2 := ((crdC ε).contDiff.comp h1).const_smul (1 / 2 : ℝ)
  convert h2 using 1
  funext z
  change actR g z = (1 / 2 : ℝ) • crdLin ε ((2 : ℝ) • pmat (actR g z))
  rw [map_smul, crd_pmat, smul_smul]
  norm_num

theorem shcAd_fderiv_actR {ε : Fin n → Bool} (y v : PCoord ε → ℂ) :
    shcAd y (pmat (fderiv ℝ (actR (ε := ε) (NormedSpace.exp (pmat y))) 0 v)) = pmat v := by
  have hg := exp_pmat_inUJ y
  have hY : (NormedSpace.exp (pmat y))ᴴ = NormedSpace.exp (pmat y) := (pmat_isHermitian y).exp
  have hD := ((actR_contDiff' hg).differentiable one_ne_zero 0).hasFDerivAt
  set D := fderiv ℝ (actR (ε := ε) (NormedSpace.exp (pmat y))) 0
  have h1 := ((pmatC ε).hasFDerivAt.comp 0 hD).const_smul (2 : ℝ)
  have h2 : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      (fderiv ℝ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
        ((2 : ℝ) • pmat y)) ((2 : ℝ) • pmat (actR (NormedSpace.exp (pmat y)) (0 : PCoord ε → ℂ))) := by
    rw [actR_exp_zero]; exact hasFDerivAt_exp_alg _
  have h3 := HasFDerivAt.comp (0 : PCoord ε → ℂ) h2 h1
  have h4 := ((pmatC ε).hasFDerivAt (x := 0)).const_smul (2 : ℝ)
  have h5 : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ)
        ((2 : ℝ) • pmatC ε (0 : PCoord ε → ℂ)) := by
    rw [map_zero, smul_zero]; exact hasFDerivAt_exp_zero
  have h6 := ((HasFDerivAt.comp (0 : PCoord ε → ℂ) h5 h4).const_mul
    (NormedSpace.exp (pmat y))).mul_const' (NormedSpace.exp (pmat y))
  have h7 := h3.unique (h6.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => by
    have := exp_two_actR hg z
    rw [hY] at this
    exact this))
  have h8 := congrArg (fun T => T v) h7
  have h9 : fderiv ℝ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((2 : ℝ) • pmat y) ((2 : ℝ) • pmat (D v)) =
      NormedSpace.exp (pmat y) * ((2 : ℝ) • pmat v) * NormedSpace.exp (pmat y) := h8
  rw [fderiv_exp_two] at h9
  have h10 : shcAdLin y ((2 : ℝ) • pmat (D v)) = (2 : ℝ) • pmat v := conj_cancel h9
  rw [map_smul] at h10
  exact smul_right_injective _ (two_ne_zero (α := ℝ)) h10

end Op

theorem jacBase' {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    |LinearMap.det ((fderiv ℝ (actR (ε := ε) (NormedSpace.exp (pmat y))) 0 :
      (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) : (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ))| * Jac y = 1 := by
  let S : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ) :=
    LinearMap.toContinuousLinearMap (crdLin ε ∘ₗ shcAdLin y ∘ₗ pmatLin ε)
  have hS : fderiv ℝ (shcAdC y) 0 = S := S.fderiv
  have h1 := detP y
  rw [hS] at h1
  set D := fderiv ℝ (actR (ε := ε) (NormedSpace.exp (pmat y))) 0 with hD
  have h2 : (S : (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ)) ∘ₗ (D : (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ)) =
      LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    change crdLin ε (shcAd y (pmat (D v))) = v
    rw [hD, shcAd_fderiv_actR, crd_pmat]
  have h3 := congrArg LinearMap.det h2
  rw [LinearMap.det_comp, LinearMap.det_id, h1] at h3
  rw [← abs_of_pos (jac_pos' y), ← abs_mul, mul_comm, h3, abs_one]

end JacB

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jall_pmat_add {ε : Fin n → Bool} (z w : PCoord ε → ℂ) : pmat (z + w) = pmat z + pmat w := by
  ext a b
  simp only [pmat, Pi.add_apply, Matrix.add_apply]
  split_ifs <;> simp

theorem jall_pmat_smul {ε : Fin n → Bool} (c : ℝ) (z : PCoord ε → ℂ) :
    pmat (c • z) = (c : ℂ) • pmat z := by
  ext a b
  simp only [pmat, Pi.smul_apply, Matrix.smul_apply]
  split_ifs <;> simp [Complex.real_smul, star_mul', Complex.conj_ofReal]

def adKL {ε : Fin n → Bool} (k : KG ε) : (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ) where
  toFun := adK k
  map_add' z w := by
    funext ab
    simp only [adK, jall_pmat_add, Matrix.mul_add, Matrix.add_mul, Pi.add_apply, Matrix.add_apply]
  map_smul' c z := by
    funext ab
    simp only [adK, jall_pmat_smul, Matrix.mul_smul, Matrix.smul_mul, Pi.smul_apply, Matrix.smul_apply,
      RingHom.id_apply, Complex.real_smul, smul_eq_mul]

theorem jall_adK_inv {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) : adK k⁻¹ (adK k z) = z := by
  have hk := toMK_facts k
  have h : pmat (adK k⁻¹ (adK k z)) = pmat z := by
    rw [pmat_adK, pmat_adK, toMK_inv, Matrix.conjTranspose_conjTranspose]
    calc (toMK k)ᴴ * (toMK k * pmat z * (toMK k)ᴴ) * toMK k
        = ((toMK k)ᴴ * toMK k) * pmat z * ((toMK k)ᴴ * toMK k) := by simp only [Matrix.mul_assoc]
      _ = pmat z := by rw [hk.1, Matrix.one_mul, Matrix.mul_one]
  rw [← pact_pmat_coords (adK k⁻¹ (adK k z)), h, pact_pmat_coords]

theorem jall_abs_det_adKL {ε : Fin n → Bool} (k : KG ε) : |LinearMap.det (adKL k)| = 1 := by
  have hinj : Function.Injective (adKL k) := fun x y hxy => by
    have := congrArg (adK k⁻¹) hxy
    simpa only [adKL, LinearMap.coe_mk, AddHom.coe_mk, jall_adK_inv] using this
  have hmp := adK_measurePreserving k
  have hcs : IsCompact ((adKL k) '' Metric.closedBall (0 : PCoord ε → ℂ) 1) :=
    (isCompact_closedBall 0 1).image (LinearMap.continuous_of_finiteDimensional _)
  have h1 : volume ((adK k) ⁻¹' ((adKL k) '' Metric.closedBall (0 : PCoord ε → ℂ) 1)) =
      volume ((adKL k) '' Metric.closedBall (0 : PCoord ε → ℂ) 1) :=
    hmp.measure_preimage hcs.isClosed.measurableSet.nullMeasurableSet
  have hpre : (adK k) ⁻¹' ((adKL k) '' Metric.closedBall (0 : PCoord ε → ℂ) 1) =
      Metric.closedBall (0 : PCoord ε → ℂ) 1 := Set.preimage_image_eq _ hinj
  rw [hpre, MeasureTheory.Measure.addHaar_image_linearMap] at h1
  have hpos : volume (Metric.closedBall (0 : PCoord ε → ℂ) 1) ≠ 0 :=
    (Metric.measure_closedBall_pos volume 0 one_pos).ne'
  have hfin : volume (Metric.closedBall (0 : PCoord ε → ℂ) 1) ≠ ⊤ :=
    (isCompact_closedBall (0 : PCoord ε → ℂ) 1).measure_lt_top.ne
  have h2 : ENNReal.ofReal |LinearMap.det (adKL k)| = 1 := by
    have h3 : 1 * volume (Metric.closedBall (0 : PCoord ε → ℂ) 1) =
        ENNReal.ofReal |LinearMap.det (adKL k)| * volume (Metric.closedBall (0 : PCoord ε → ℂ) 1) := by
      rw [one_mul]; exact h1
    exact ((ENNReal.mul_left_inj hpos hfin).mp h3).symm
  exact ENNReal.ofReal_eq_one.mp h2

def jdetA {ε : Fin n → Bool} (g : Matrix (Fin n) (Fin n) ℂ) (z : PCoord ε → ℂ) : ℝ :=
  LinearMap.det ((fderiv ℝ (actR (ε := ε) g) z : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) :
    (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ))

theorem jall_diff {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (z : PCoord ε → ℂ) :
    DifferentiableAt ℝ (actR (ε := ε) g) z := by
  first
  | exact (JacB.actR_contDiff' hg).differentiable one_ne_zero z
  | exact (JacB.actR_contDiff' hg).differentiable le_rfl z

theorem jall_chain {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hh : inUJ ε h)
    (z : PCoord ε → ℂ) : jdetA (g * h) z = jdetA h (actR g z) * jdetA g z := by
  unfold jdetA
  have hfun : actR (ε := ε) (g * h) = actR h ∘ actR g := funext (actR_mul hg hh)
  rw [hfun, fderiv_comp z (jall_diff hh (actR g z)) (jall_diff hg z)]
  exact LinearMap.det_comp _ _

theorem jall_fderiv_K {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) :
    fderiv ℝ (actR (ε := ε) (toMK k)) z = LinearMap.toContinuousLinearMap (adKL k⁻¹) := by
  have e : actR (ε := ε) (toMK k) = ⇑(LinearMap.toContinuousLinearMap (adKL k⁻¹)) := by
    funext w
    rw [actR_K]
    rfl
  rw [e]
  exact ContinuousLinearMap.fderiv _

theorem jall_abs_jdetA_K {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) :
    |jdetA (toMK k) z| = 1 := by
  unfold jdetA
  rw [jall_fderiv_K]
  exact jall_abs_det_adKL k⁻¹

theorem jall_inUJ_K {ε : Fin n → Bool} (k : KG ε) : inUJ ε (toMK k) := by
  first
  | exact k.1.2
  | exact k.val.property
  | exact k.2.1

theorem jall_actR_K_zero {ε : Fin n → Bool} (k : KG ε) : actR (ε := ε) (toMK k) 0 = 0 := by
  have hp0 : pmat (0 : PCoord ε → ℂ) = 0 := by
    ext a b
    simp [pmat]
  apply actR_of_eq_polarM (k := k)
  simp only [polarM, hp0, NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_one]

theorem jacAll {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (z : PCoord ε → ℂ) :
    |LinearMap.det ((fderiv ℝ (actR (ε := ε) g) z : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) :
      (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ))| * Jac (actR g z) = Jac z := by
  have hp0 : pmat (0 : PCoord ε → ℂ) = 0 := by
    ext a b
    simp [pmat]
  obtain ⟨k, hk⟩ := actR_spec hg z
  set w := actR g z with hw
  have hEz := exp_pmat_inUJ z
  have hEw := exp_pmat_inUJ w
  have hK := jall_inUJ_K k
  have h0z : actR (ε := ε) (NormedSpace.exp (pmat z)) 0 = z := by
    apply actR_of_eq_polarM (k := 1)
    simp only [polarM, hp0, NormedSpace.exp_zero, Matrix.one_mul]
    first
    | rfl
    | (rw [show toMK (1 : KG ε) = 1 from rfl, Matrix.one_mul])
    | simp
  have hc1 := jall_chain hEz hg 0
  rw [h0z] at hc1
  have hc2 := jall_chain hK hEw 0
  rw [jall_actR_K_zero] at hc2
  have hmul : NormedSpace.exp (pmat z) * g = toMK k * NormedSpace.exp (pmat w) := by
    rw [hk]; rfl
  rw [hmul, hc2] at hc1
  have hab : |jdetA g z| * |jdetA (ε := ε) (NormedSpace.exp (pmat z)) 0| = |jdetA (ε := ε) (NormedSpace.exp (pmat w)) 0| := by
    have := congrArg abs hc1
    rw [abs_mul, abs_mul, jall_abs_jdetA_K, mul_one] at this
    rw [this, mul_comm]
  have hbZ : |jdetA (ε := ε) (NormedSpace.exp (pmat z)) 0| * Jac z = 1 := JacB.jacBase' z
  have hcW : |jdetA (ε := ε) (NormedSpace.exp (pmat w)) 0| * Jac w = 1 := JacB.jacBase' w
  show |jdetA g z| * Jac w = Jac z
  linear_combination (-(|jdetA g z| * Jac w)) * hbZ + (Jac w * Jac z) * hab + Jac z * hcW

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem inv_inUJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    inUJ ε (Jm ε * gᴴ * Jm ε) ∧ (Jm ε * gᴴ * Jm ε) * g = 1 ∧ g * (Jm ε * gᴴ * Jm ε) = 1 := by
  have hJ : Jm ε * Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hJt : (Jm ε)ᴴ = Jm ε := Formalism.REAL.Jm_conjTranspose ε
  have hJJ : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have hg' : gᴴ * (Jm ε * g) = Jm ε := by
    unfold inUJ at hg
    rw [← Matrix.mul_assoc]; exact hg
  have h1 : Jm ε * gᴴ * Jm ε * g = 1 := by
    simp only [Matrix.mul_assoc]; rw [hg', hJ]
  have h2 : g * (Jm ε * gᴴ * Jm ε) = 1 := by
    first
    | exact mul_eq_one_comm.mp h1
    | exact Matrix.mul_eq_one_comm.mp h1
    | exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp h1
  have h3 : ∀ X : Matrix (Fin n) (Fin n) ℂ, g * (Jm ε * (gᴴ * X)) = Jm ε * X := fun X => by
    calc g * (Jm ε * (gᴴ * X)) = g * (Jm ε * gᴴ * Jm ε) * (Jm ε * X) := by
          simp only [Matrix.mul_assoc, hJJ]
      _ = Jm ε * X := by rw [h2, Matrix.one_mul]
  refine ⟨?_, h1, h2⟩
  unfold inUJ
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJt, Matrix.mul_assoc, hJJ, h3]

theorem coreP {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Measure.map (actR (ε := ε) g) (volume.withDensity fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z)) =
      volume.withDensity fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z) := by
  obtain ⟨hh, hhg, hgh⟩ := inv_inUJ hg
  set h := Jm ε * gᴴ * Jm ε with hdef
  have hleft : ∀ z, actR (ε := ε) h (actR g z) = z := fun z => by
    rw [← actR_mul hg hh, hgh, actR_one]
  have hright : ∀ z, actR (ε := ε) g (actR h z) = z := fun z => by
    rw [← actR_mul hh hg, hhg, actR_one]
  have hmeas : Measurable (actR (ε := ε) g) := (JacB.actR_continuous hg).measurable
  ext A hA
  rw [Measure.map_apply hmeas hA, withDensity_apply _ hA, withDensity_apply _ (hmeas hA)]
  have himg : actR (ε := ε) g '' (actR g ⁻¹' A) = A :=
    Set.image_preimage_eq A (fun y => ⟨actR h y, hright y⟩)
  calc ∫⁻ z in actR g ⁻¹' A, ENNReal.ofReal (Jac z)
        = ∫⁻ z in actR g ⁻¹' A, ENNReal.ofReal |(fderiv ℝ (actR (ε := ε) g) z).det| *
            ENNReal.ofReal (Jac (actR g z)) := by
          refine lintegral_congr (fun z => ?_)
          rw [← ENNReal.ofReal_mul (abs_nonneg _)]
          rw [← jacAll hg z]
    _ = ∫⁻ z in actR g '' (actR g ⁻¹' A), ENNReal.ofReal (Jac z) :=
          (lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hmeas hA)
            (fun z _ => (jall_diff hg z).hasFDerivAt.hasFDerivWithinAt)
            (fun x _ y _ hxy => by rw [← hleft x, hxy, hleft y]) (fun z => ENNReal.ofReal (Jac z))).symm
    _ = ∫⁻ z in A, ENNReal.ofReal (Jac z) := by rw [himg]

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def rmulPR (G : Matrix (Fin n) (Fin n) ℂ) (A : Fin n → Fin n → ℂ) : Fin n → Fin n → ℂ :=
  (Matrix.of A : Matrix (Fin n) (Fin n) ℂ) * G

def polarPR {ε : Fin n → Bool} (kz : KG ε × (PCoord ε → ℂ)) : Fin n → Fin n → ℂ := polarM kz

theorem continuous_rmulPR (G : Matrix (Fin n) (Fin n) ℂ) : Continuous (rmulPR G) := by
  unfold rmulPR
  exact (continuous_id.matrix_mul continuous_const :
    Continuous fun A : Matrix (Fin n) (Fin n) ℂ => A * G)

theorem measurable_polarPR (ε : Fin n → Bool) : Measurable (polarPR (ε := ε)) := by
  have h : Continuous (polarPR (ε := ε)) := polarM_continuous ε
  exact h.measurable

theorem rmulPR_polarPR {ε : Fin n → Bool} {G : Matrix (Fin n) (Fin n) ℂ} (hG : inUJ ε G)
    (z : PCoord ε → ℂ) : ∃ k' : KG ε, ∀ k : KG ε,
      rmulPR G (polarPR (k, z)) = polarPR (k * k', actR G z) := by
  have hE : inUJ ε (NormedSpace.exp (pmat z)) := exp_pmat_inUJ z
  have hEG : inUJ ε (NormedSpace.exp (pmat z) * G) := by
    unfold inUJ at hE hG ⊢
    rw [Matrix.conjTranspose_mul]
    calc Gᴴ * (NormedSpace.exp (pmat z))ᴴ * Jm ε * (NormedSpace.exp (pmat z) * G)
        = Gᴴ * ((NormedSpace.exp (pmat z))ᴴ * Jm ε * NormedSpace.exp (pmat z)) * G := by
          simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [hE, hG]
  obtain ⟨⟨k', w⟩, hkw⟩ := polarM_surj _ hEG
  have hw : actR G z = w := by
    funext ab
    have h1 : plog (NormedSpace.exp (pmat z) * G) = pmat w := by
      rw [← hkw, plog_polarM]
    simp only [actR, h1, pmat, dif_pos ab.2]
  refine ⟨k', fun k => ?_⟩
  rw [hw]
  simp only [rmulPR, polarPR, polarM] at hkw ⊢
  have hm : toMK (k * k') = toMK k * toMK k' := rfl
  show toMK k * NormedSpace.exp (pmat z) * G = _
  rw [Matrix.mul_assoc, ← hkw, hm, Matrix.mul_assoc]

theorem muPolarMat_mul_right (ε : Fin n → Bool) {G : Matrix (Fin n) (Fin n) ℂ} (hG : inUJ ε G) :
    Measure.map (rmulPR G) (muPolarMat ε) = muPolarMat ε := by
  have hP : Measurable (polarPR (ε := ε)) := measurable_polarPR ε
  have hR : Measurable (rmulPR G) := (continuous_rmulPR G).measurable
  have hA : Measurable (actR (ε := ε) G) := (JacB.actR_continuous hG).measurable
  have hc := coreP hG
  have : IsFiniteMeasure (dk ε) := by
    rw [isFiniteMeasure_iff, (dk_props ε).1.measure_univ]
    exact ENNReal.one_lt_top

  have key : ∀ S : Set (Fin n → Fin n → ℂ), MeasurableSet S →
      muPolarMat ε S = ∫⁻ z, dk ε {k | polarPR (k, z) ∈ S}
        ∂(volume.withDensity fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z)) := by
    intro S hS
    show (Measure.map (polarPR (ε := ε)) ((dk ε).prod
      (volume.withDensity fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z)))) S = _
    rw [Measure.map_apply hP hS, Measure.prod_apply_symm (hP hS)]
    rfl
  ext S hS
  rw [Measure.map_apply hR hS, key _ (hR hS), key _ hS]
  have step : ∀ z : PCoord ε → ℂ, dk ε {k | polarPR (k, z) ∈ rmulPR G ⁻¹' S} =
      dk ε {k | polarPR (k, actR G z) ∈ S} := by
    intro z
    obtain ⟨k', hk'⟩ := rmulPR_polarPR hG z
    have hset : {k | polarPR (k, z) ∈ rmulPR G ⁻¹' S} =
        (fun k => k * k') ⁻¹' {k | polarPR (k, actR G z) ∈ S} := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_preimage, hk']
    rw [hset, measure_preimage_mul_right]
  simp_rw [step]
  have hφ : Measurable fun w : PCoord ε → ℂ => dk ε {k | polarPR (k, w) ∈ S} :=
    measurable_measure_prodMk_right (hP hS)
  rw [← lintegral_map hφ hA, hc]

theorem muPolar_mul_right (ε : Fin n → Bool) (g : UJ ε) :
    Measure.map (fun x => x * g) (muPolar ε) = muPolar ε := by
  show Measure.map (fun x => x * g) (Measure.comap (intMuCD_eM ε) (muPolarMat ε)) =
    Measure.comap (intMuCD_eM ε) (muPolarMat ε)
  by_cases h : Function.Injective (intMuCD_eM ε) ∧
      ∀ s, MeasurableSet s → NullMeasurableSet (intMuCD_eM ε '' s) (muPolarMat ε)
  swap
  · simp only [Measure.comap, dif_neg h, Measure.map_zero]
  haveI : BorelSpace (UJ ε) := ⟨rfl⟩
  have hRm : Measurable (fun x : UJ ε => x * g) := (continuous_mul_const g).measurable
  have hG : inUJ ε (toM g) := g.2
  have h4 := muPolarMat_mul_right ε hG
  have hRM : Measurable (rmulPR (toM g)) := (continuous_rmulPR (toM g)).measurable
  ext S hS
  rw [Measure.map_apply hRm hS, Measure.comap_apply₀ _ _ h.1 h.2 (hRm hS).nullMeasurableSet,
    Measure.comap_apply₀ _ _ h.1 h.2 hS.nullMeasurableSet]
  have h1 : toM g * toM g⁻¹ = 1 := by
    rw [show toM g * toM g⁻¹ = toM (g * g⁻¹) from rfl, mul_inv_cancel]
    rfl
  have himg : intMuCD_eM ε '' ((fun x => x * g) ⁻¹' S) =
      rmulPR (toM g) ⁻¹' (intMuCD_eM ε '' S) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y * g, hy, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      refine ⟨y * g⁻¹, ?_, ?_⟩
      · show y * g⁻¹ * g ∈ S
        rw [inv_mul_cancel_right]
        exact hy
      · have hx : toM y = Matrix.of x * toM g := hxy
        show toM y * toM g⁻¹ = x
        rw [hx, Matrix.mul_assoc, h1, Matrix.mul_one]
        rfl
  rw [himg, ← Measure.map_apply₀ hRM.aemeasurable (by rw [h4]; exact h.2 S hS), h4]

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarHaarA
noncomputable section

open Finset Matrix MeasureTheory Topology
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

lemma fdph_muK_univ_ne_zero (ε : Fin n → Bool) : muK ε Set.univ ≠ 0 := by
  exact isOpen_univ.measure_ne_zero (muK ε) Set.univ_nonempty

lemma fdph_muK_univ_ne_top (ε : Fin n → Bool) : muK ε Set.univ ≠ ⊤ := by
  exact (isCompact_univ.measure_lt_top (μ := muK ε)).ne

instance fdph_dk_finite (ε : Fin n → Bool) : IsFiniteMeasure (dk ε) := by
  rw [dk_def]
  exact IsFiniteMeasure.average (μ := muK ε)

instance fdph_dk_openPos (ε : Fin n → Bool) : Measure.IsOpenPosMeasure (dk ε) := by
  rw [dk_def]
  exact Measure.isOpenPosMeasure_smul (muK ε) (ENNReal.inv_ne_zero.mpr (fdph_muK_univ_ne_top ε))

lemma fdph_shc_pos (u : ℝ) : 0 < shc u := pb_shc_pos u

lemma fdph_jac_pos {ε : Fin n → Bool} (z : PCoord ε → ℂ) : 0 < Jac z := by
  delta Jac
  exact Finset.prod_pos fun a _ => Finset.prod_pos fun b _ => fdph_shc_pos _

abbrev fdphNu (ε : Fin n → Bool) : Measure (PCoord ε → ℂ) :=
  (volume : Measure (PCoord ε → ℂ)).withDensity fun z => ENNReal.ofReal (Jac z)

instance fdph_nu_openPos (ε : Fin n → Bool) : Measure.IsOpenPosMeasure (fdphNu ε) := by
  refine ⟨fun U hU hne => ?_⟩
  have hm : Measurable fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z) :=
    ENNReal.measurable_ofReal.comp (jac_continuous ε).measurable
  rw [Ne, fdphNu, withDensity_apply_eq_zero hm]
  have hu : {x : PCoord ε → ℂ | ENNReal.ofReal (Jac x) ≠ 0} = Set.univ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, Ne, ENNReal.ofReal_eq_zero, not_le]
    exact fdph_jac_pos x
  rw [hu, Set.univ_inter]
  exact hU.measure_ne_zero volume hne

instance fdph_nu_finCpt (ε : Fin n → Bool) : IsFiniteMeasureOnCompacts (fdphNu ε) := by
  refine ⟨fun K hK => ?_⟩
  rw [fdphNu, withDensity_apply' _ K]
  exact setLIntegral_lt_top_of_isCompact hK.measure_lt_top.ne hK (f := fun z => (Jac z).toNNReal)
    (continuous_real_toNNReal.comp (jac_continuous ε))

def fdphPhi (ε : Fin n → Bool) (kz : KG ε × (PCoord ε → ℂ)) : UJ ε :=
  ⟨⟨polarM kz, Jm ε * (polarM kz)ᴴ * Jm ε,
    mul_eq_one_comm.mp (left_inv_of_inUJ ε _ (polarM_inUJ kz)), left_inv_of_inUJ ε _ (polarM_inUJ kz)⟩,
    polarM_inUJ kz⟩

lemma fdph_toM_phi (ε : Fin n → Bool) (kz : KG ε × (PCoord ε → ℂ)) : toM (fdphPhi ε kz) = polarM kz := rfl

lemma fdph_phi_continuous (ε : Fin n → Bool) : Continuous (fdphPhi ε) := by
  apply (isClosedEmbedding_toM ε).isEmbedding.continuous_iff.mpr
  change Continuous (fun kz => toM (fdphPhi ε kz))
  simpa only [fdph_toM_phi] using polarM_continuous ε

lemma fdph_preimage (ε : Fin n → Bool) (S : Set (UJ ε)) :
    Set.preimage (β := Fin n → Fin n → ℂ) polarM (Set.image (β := Fin n → Fin n → ℂ) (fun g : UJ ε => toM g) S) =
      fdphPhi ε ⁻¹' S := by
  let embed : UJ ε → Fin n → Fin n → ℂ := toM
  have he : Function.Injective embed := (isClosedEmbedding_toM ε).injective
  change (embed ∘ fdphPhi ε) ⁻¹' (embed '' S) = fdphPhi ε ⁻¹' S
  rw [Set.preimage_comp, Set.preimage_image_eq S he]

lemma fdph_apply (ε : Fin n → Bool) {S : Set (UJ ε)} (hS : MeasurableSet S) :
    muPolar ε S = ((dk ε).prod (fdphNu ε)) (fdphPhi ε ⁻¹' S) := by
  have hC : IsClosedEmbedding (Y := Fin n → Fin n → ℂ) (fun g : UJ ε => toM g) := isClosedEmbedding_toM ε
  have hE : MeasurableEmbedding (β := Fin n → Fin n → ℂ) (fun g : UJ ε => toM g) := hC.measurableEmbedding
  have hPc : Continuous (Y := Fin n → Fin n → ℂ) (polarM (ε := ε)) := (polarM_isClosedEmbedding ε).continuous
  have hP : Measurable (β := Fin n → Fin n → ℂ) (polarM (ε := ε)) := hPc.measurable
  delta muPolar muPolarMat
  rw [hE.comap_apply, Measure.map_apply hP (hE.measurableSet_image' hS), fdph_preimage]

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem muPolar_isHaar (ε : Fin n → Bool) : (muPolar ε).IsHaarMeasure := by
  haveI hR : (muPolar ε).IsMulRightInvariant := ⟨fun g => muPolar_mul_right ε g⟩
  have hinv : (muPolar ε).inv = muPolar ε := muPolar_inv ε
  haveI hL : (muPolar ε).IsMulLeftInvariant := by
    rw [← hinv]; infer_instance

  have hsurj : Function.Surjective (fdphPhi ε) := by
    intro g
    have hg : toM g ∈ UJset ε := g.2
    refine ⟨polarInv ε ⟨toM g, hg⟩, ?_⟩
    have h := fdph_toM_phi ε (polarInv ε ⟨toM g, hg⟩)
    rw [polarM_polarInv] at h
    exact Subtype.ext (Units.ext h)
  haveI hF : IsFiniteMeasureOnCompacts (muPolar ε) := by
    refine ⟨fun K hK => ?_⟩
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    rw [fdph_apply ε hKm, ← fdph_preimage]
    exact ((polarM_isClosedEmbedding ε).isCompact_preimage
      (hK.image (by fun_prop))).measure_lt_top
  haveI hO : (muPolar ε).IsOpenPosMeasure := by
    refine ⟨fun U hU hne => ?_⟩
    rw [fdph_apply ε hU.measurableSet]
    exact ((hU.preimage (fdph_phi_continuous ε)).measure_ne_zero _
      (hne.preimage hsurj))
  exact {}

end ReciprocityTheory.ChartRestriction.DS
