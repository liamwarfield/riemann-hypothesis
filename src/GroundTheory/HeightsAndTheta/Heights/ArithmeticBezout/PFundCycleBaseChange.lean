module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeLogBound
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SphereMeanSlice
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartGramMA
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PZeroLocusDimH
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChowDegree
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFundCycleBaseChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem localMult_map_of_flat {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (J W : Ideal A) [W.IsPrime] (W' : Ideal B) [W'.IsPrime] [W'.LiesOver W]
    (hfib : (W.map (algebraMap A B)).map (algebraMap B (Localization.AtPrime W')) =
      IsLocalRing.maximalIdeal (Localization.AtPrime W')) :
    localMult (J.map (algebraMap A B)) W' = localMult J W := by
  let := Localization.AtPrime.algebraOfLiesOver W W'
  have : IsLocalHom (algebraMap (Localization.AtPrime W) (Localization.AtPrime W')) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  have htow : (algebraMap (Localization.AtPrime W) (Localization.AtPrime W')).comp
      (algebraMap A (Localization.AtPrime W)) =
      (algebraMap B (Localization.AtPrime W')).comp (algebraMap A B) := by
    ext x
    exact Localization.localRingHom_to_map _ _ _ Ideal.LiesOver.over x
  have hmap : ∀ I : Ideal A, (I.map (algebraMap A (Localization.AtPrime W))).map
      (algebraMap (Localization.AtPrime W) (Localization.AtPrime W')) =
      (I.map (algebraMap A B)).map (algebraMap B (Localization.AtPrime W')) := by
    intro I
    rw [Ideal.map_map, Ideal.map_map, htow]
  have key := IsLocalRing.length_baseChange (Localization.AtPrime W) (Localization.AtPrime W')
    (Localization.AtPrime W ⧸ J.map (algebraMap A (Localization.AtPrime W)))
  rw [← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime W')
    (J.map (algebraMap A (Localization.AtPrime W)))).toLinearEquiv.length_eq, hmap,
    ← IsLocalization.AtPrime.map_eq_maximalIdeal W (Localization.AtPrime W), hmap, hfib] at key
  have : IsSimpleModule (Localization.AtPrime W')
      (Localization.AtPrime W' ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime W')) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal _))
  rw [Module.length_eq_one (R := Localization.AtPrime W')
    (M := Localization.AtPrime W' ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime W')), mul_one] at key
  unfold localMult
  rw [dite_eq_left ‹W'.IsPrime›, dite_eq_left ‹W.IsPrime›, key]

section MinimalPrimes

variable {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
  (hc : ∀ I : Ideal A, I.IsPrime → ∀ P ∈ (I.map f).minimalPrimes, P.comap f = I)
include hc

theorem comap_mem_minimalPrimes {J : Ideal A} {P : Ideal B} (hP : P ∈ (J.map f).minimalPrimes) :
    P.comap f ∈ J.minimalPrimes ∧ P ∈ ((P.comap f).map f).minimalPrimes := by
  have hPp : P.IsPrime := hP.1.1
  obtain ⟨W₀, hW₀, hW₀le⟩ :=
    Ideal.exists_minimalPrimes_le (Ideal.map_le_iff_le_comap.mp hP.1.2)
  have hW₀p : W₀.IsPrime := hW₀.1.1
  obtain ⟨P₀, hP₀, hP₀le⟩ :=
    Ideal.exists_minimalPrimes_le (Ideal.map_le_iff_le_comap.mpr hW₀le)
  have hP₀p : P₀.IsPrime := hP₀.1.1
  have hEq : P₀ = P :=
    le_antisymm hP₀le (hP.2 ⟨hP₀p, (Ideal.map_mono hW₀.1.2).trans hP₀.1.2⟩ hP₀le)
  subst hEq
  rw [hc W₀ hW₀p P₀ hP₀]
  exact ⟨hW₀, hP₀⟩

theorem mem_minimalPrimes_map {J W : Ideal A} (hW : W ∈ J.minimalPrimes) {P : Ideal B}
    (hP : P ∈ (W.map f).minimalPrimes) : P ∈ (J.map f).minimalPrimes := by
  have hWp : W.IsPrime := hW.1.1
  have hPp : P.IsPrime := hP.1.1
  refine ⟨⟨hPp, (Ideal.map_mono hW.1.2).trans hP.1.2⟩, fun Q hQ hQP => ?_⟩
  have hQp : Q.IsPrime := hQ.1
  obtain ⟨Q₀, hQ₀, hQ₀le⟩ := Ideal.exists_minimalPrimes_le hQ.2
  obtain ⟨h1, -⟩ := comap_mem_minimalPrimes f hc hQ₀
  have hle : Q₀.comap f ≤ W := by
    rw [← hc W hWp P hP]
    exact Ideal.comap_mono (hQ₀le.trans hQP)
  have hWQ : W ≤ Q₀.comap f := hW.2 h1.1 hle
  have hQ₀p : Q₀.IsPrime := hQ₀.1.1
  exact (hP.2 ⟨hQ₀p, Ideal.map_le_iff_le_comap.mpr hWQ⟩ (hQ₀le.trans hQP)).trans hQ₀le

end MinimalPrimes

theorem isRelevant_comap_map_iff {K L : Type*} [CommRing K] [CommRing L] (σ : K →+* L) {n : ℕ}
    (P : Ideal (MvPolynomial (Fin n) L)) :
    IsRelevant (P.comap (MvPolynomial.map σ)) ↔ IsRelevant P := by
  simp [IsRelevant, Ideal.mem_comap, MvPolynomial.map_X]

theorem fundCycle_apply {R : Type*} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (J W : Ideal (MvPolynomial (Fin n) R)) [Decidable (W ∈ relComps J)] :
    fundCycle J W = if W ∈ relComps J then localMult J W else 0 := by
  unfold fundCycle
  rw [Finsupp.onFinset_apply]
  congr

theorem FundCycleBaseChange.proof (h : MinimalPrimeComap.Statement) : FundCycleBaseChange.Statement := by
  classical
  intro K L _ _ _ σ n J
  have hc : ∀ I : Ideal (MvPolynomial (Fin n) K), I.IsPrime →
      ∀ P ∈ (I.map (MvPolynomial.map σ)).minimalPrimes, P.comap (MvPolynomial.map σ) = I :=
    fun I hI P hP => h K L σ (Fin n) I hI P hP
  have hrad := RadicalBaseChange.proof
  let := σ.toAlgebra
  let := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := K) (S := L)
  have : Module.Flat (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) L) :=
    Module.Flat.isBaseChange (R := K) (S := MvPolynomial (Fin n) K) (M := L)
      (N := MvPolynomial (Fin n) L) (h := Algebra.IsPushout.out (R := K) (S := MvPolynomial (Fin n) K) (R' := L)
        (S' := MvPolynomial (Fin n) L))
  have hsupp : ∀ W ∈ (fundCycle J).support, W ∈ relComps J := by
    intro W hW
    by_contra hn
    exact Finsupp.mem_support_iff.mp hW (by rw [fundCycle_apply, if_neg hn])
  have hone : ∀ W : Ideal (MvPolynomial (Fin n) K), W.IsPrime → ∀ P,
      P ∈ relComps (W.map (MvPolynomial.map σ)) → localMult (W.map (MvPolynomial.map σ)) P = 1 :=
    fun W hW P hP => localMult_eq_one_of_isRadical (hrad K L σ (Fin n) W hW.isRadical) hP.1
  ext P
  rw [Finsupp.finsetSum_apply, fundCycle_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  split_ifs with hP
  · obtain ⟨hWmin, hPW⟩ := comap_mem_minimalPrimes _ hc hP.1
    have hWrel : P.comap (MvPolynomial.map σ) ∈ relComps J :=
      ⟨hWmin, (isRelevant_comap_map_iff σ P).mpr hP.2⟩
    have hWp : (P.comap (MvPolynomial.map σ)).IsPrime := hWmin.1.1
    have hPp : P.IsPrime := hP.1.1.1
    have : P.LiesOver (P.comap (MvPolynomial.map σ)) := ⟨rfl⟩
    have hmult : localMult (J.map (MvPolynomial.map σ)) P =
        localMult J (P.comap (MvPolynomial.map σ)) :=
      localMult_map_of_flat J _ P (map_eq_maximalIdeal_of_isRadical
        (hrad K L σ (Fin n) _ hWp.isRadical) hPW)
    rw [hmult, Finset.sum_eq_single (P.comap (MvPolynomial.map σ))]
    · rw [fundCycle_apply J, if_pos hWrel,
        fundCycle_apply (Ideal.map (MvPolynomial.map σ) (P.comap (MvPolynomial.map σ))) P,
        if_pos ⟨hPW, hP.2⟩, hone _ hWp P ⟨hPW, hP.2⟩, mul_one]
    · intro W₀ hW₀ hne
      rw [fundCycle_apply (Ideal.map (MvPolynomial.map σ) W₀) P, if_neg, mul_zero]
      intro hPW₀
      exact hne (hc W₀ (hsupp W₀ hW₀).1.1.1 P hPW₀.1).symm
    · intro hW
      rw [Finsupp.notMem_support_iff.mp hW, zero_mul]
  · refine (Finset.sum_eq_zero fun W hW => ?_).symm
    rw [fundCycle_apply (Ideal.map (MvPolynomial.map σ) W) P, if_neg, mul_zero]
    intro hPW
    exact hP ⟨mem_minimalPrimes_map _ hc (hsupp W hW).1 hPW.1, hPW.2⟩

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SphereMean
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Measure Set Real

noncomputable section

namespace SphereMean

theorem setAverage_log_fst_sub (m : ℕ) :
    ⨍ y in ballSet (m + 1) 1, (log ‖y 0‖ - log (sqNorm y) / 2) = -(harmonic m : ℝ) / 2 := by
  obtain ⟨h1i, h1⟩ := integral_ballSet_neg_log_fst m
  obtain ⟨h2i, h2⟩ := integral_ballSet_neg_log_sqNorm m
  have hV : 0 < volume.real (ballSet (m + 1) 1) :=
    ENNReal.toReal_pos (volume_ballSet_one_pos _).ne' (volume_ballSet_one_ne_top _)
  have hfun : (fun y : Fin (m + 1) → ℂ => log ‖y 0‖ - log (sqNorm y) / 2) =
      fun y => (-log (sqNorm y)) / 2 - (-log ‖y 0‖) := by
    funext y
    ring
  rw [setAverage_eq, hfun, integral_sub (h2i.div_const 2) h1i, integral_div, h1, h2,
    harmonic_succ]
  push_cast
  rw [smul_eq_mul]
  field_simp
  ring

theorem volume_fst_eq_zero (m : ℕ) : volume {y : Fin (m + 1) → ℂ | y 0 = 0} = 0 := by
  let K : Submodule ℝ (Fin (m + 1) → ℂ) :=
    LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 1) => ℂ) 0)
  have hK : (K : Set (Fin (m + 1) → ℂ)) = {y | y 0 = 0} := by
    ext y
    simp only [K, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply, mem_ofPred_eq]
  have hne : K ≠ ⊤ := by
    intro h
    have : (Pi.single 0 1 : Fin (m + 1) → ℂ) ∈ K := h ▸ Submodule.mem_top
    simp only [K, LinearMap.mem_ker, LinearMap.proj_apply, Pi.single_eq_same] at this
    exact one_ne_zero this
  rw [← hK]
  exact addHaar_submodule _ _ hne

theorem setAverage_log_fst_normalized (m : ℕ) :
    ⨍ y in ballSet (m + 1) 1, log ‖((√(sqNorm y) : ℝ) : ℂ)⁻¹ * y 0‖ = -(harmonic m : ℝ) / 2 := by
  rw [← setAverage_log_fst_sub m]
  apply average_congr
  refine ae_restrict_of_ae ?_
  have h0 := measure_eq_zero_iff_ae_notMem.mp (volume_fst_eq_zero m)
  filter_upwards [h0] with y hy
  have hy' : y 0 ≠ 0 := fun h => hy h
  have hs : 0 < sqNorm y := sqNorm_pos_of_ne_zero (fun h => hy' (by simp [h]))
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    log_mul (inv_ne_zero (Real.sqrt_pos.mpr hs).ne') (norm_ne_zero_iff.mpr hy'), log_inv,
    log_sqrt hs.le]
  ring

theorem std_norm_eq (n : ℕ) (v : Fin n → ℂ) : (HermNorm.std n).norm v = √(sqNorm v) := by
  simp [HermNorm.norm, HermNorm.std, sqNorm]

end SphereMean


open SphereMean in
theorem sphereMeanLinear : SphereMeanLinear.Statement := by
  intro n p hp
  cases n with
  | zero => simp at hp
  | succ m =>

  let e := (Equiv.uniqueProd (Fin (m + 1)) (Fin 1)).symm
  let L1 : (Fin 1 × Fin (m + 1) → ℂ) ≃L[ℝ] (Fin (m + 1) → ℂ) :=
    (LinearEquiv.funCongrLeft ℝ ℂ e).toContinuousLinearEquiv
  have hL1 : ∀ u j, L1 u j = u (0, j) := by
    intro u j
    simp [L1, e]
  let G1 : (Fin (m + 1) → ℂ) → ℝ := fun v =>
    log ‖∑ j, (((√(sqNorm v) : ℝ) : ℂ)⁻¹ * v j) * star (p j)‖
  have hS : {u : Fin 1 × Fin (m + 1) → ℂ |
      ∀ i, (HermNorm.std (m + 1)).norm (fun j => u (i, j)) < 1} = L1 ⁻¹' ballSet (m + 1) 1 := by
    ext u
    simp only [mem_ofPred_eq, mem_preimage, ballSet, std_norm_eq, Fin.forall_fin_one]
    have : (fun j => u (0, j)) = L1 u := funext fun j => (hL1 u j).symm
    rw [this, Real.sqrt_lt' one_pos, one_pow]
  have hstep1 : sphereMean (HermNorm.std (m + 1)) 1
      (fun z => Real.log ‖∑ j, z (0, j) * star (p j)‖) = ⨍ u in L1 ⁻¹' ballSet (m + 1) 1, G1 (L1 u) := by
    unfold sphereMean
    rw [hS]
    congr 1
    funext u
    have : (fun j => u (0, j)) = L1 u := funext fun j => (hL1 u j).symm
    simp only [G1, std_norm_eq, this, hL1]
  rw [hstep1, setAverage_comp_linearEquiv volume volume L1 (ballSet (m + 1) 1) G1]

  let p' : EuclideanSpace ℂ (Fin (m + 1)) := WithLp.toLp 2 p
  have hp' : ‖p'‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [p', hp]
  have hon : Orthonormal ℂ (({0} : Set (Fin (m + 1))).domRestrict fun _ => p') := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [Subsingleton.elim i j, if_pos rfl,
      show (({0} : Set (Fin (m + 1))).domRestrict fun _ => p') j = p' from rfl,
      inner_self_eq_norm_sq_to_K, hp']
    simp
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hb0 : b 0 = p' := hb 0 (mem_singleton 0)
  let Ulin : (Fin (m + 1) → ℂ) ≃ₗ[ℂ] (Fin (m + 1) → ℂ) :=
    (WithLp.linearEquiv 2 ℂ (Fin (m + 1) → ℂ)).symm ≪≫ₗ b.repr.toLinearEquiv ≪≫ₗ
      WithLp.linearEquiv 2 ℂ (Fin (m + 1) → ℂ)
  let U : (Fin (m + 1) → ℂ) ≃L[ℝ] (Fin (m + 1) → ℂ) :=
    (Ulin.restrictScalars ℝ).toContinuousLinearEquiv
  have hUapp : ∀ v, U v = (b.repr (WithLp.toLp 2 v)).ofLp := fun v => rfl
  have hU0 : ∀ v, U v 0 = ∑ j, v j * star (p j) := by
    intro v
    rw [hUapp, OrthonormalBasis.repr_apply_apply, hb0, PiLp.inner_apply]
    simp [p', RCLike.inner_apply]
  have hUn : ∀ v, sqNorm (U v) = sqNorm v := by
    intro v
    have h := b.repr.norm_map (WithLp.toLp 2 v)
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq] at h
    have h2 := congrArg (· ^ 2) h
    simp only [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h2
    simpa [sqNorm, hUapp] using h2
  let G2 : (Fin (m + 1) → ℂ) → ℝ := fun w => log ‖((√(sqNorm w) : ℝ) : ℂ)⁻¹ * w 0‖
  have hG : ∀ v, G1 v = G2 (U v) := by
    intro v
    simp only [G1, G2, hUn, hU0, Finset.mul_sum, mul_assoc]
  have hB : ballSet (m + 1) 1 = U ⁻¹' ballSet (m + 1) 1 := by
    ext v
    simp [ballSet, hUn]
  have hstep2 : ⨍ v in ballSet (m + 1) 1, G1 v = ⨍ v in U ⁻¹' ballSet (m + 1) 1, G2 (U v) := by
    rw [← hB]
    congr 1
    funext v
    exact hG v
  rw [hstep2, setAverage_comp_linearEquiv volume volume U (ballSet (m + 1) 1) G2]
  simp only [G2]
  rw [setAverage_log_fst_normalized m]
  simp

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.HeightMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

theorem chowHeightMul_of_mahlerMul (hM : MahlerMul.Statement) : ChowHeightMul.Statement := by
  intro K _ _ n H k δ₁ δ₂ f₁ f₂ h₁ h₂
  unfold chowHt
  have hmah : ∀ σ : K →+* ℂ, mahler (H.normAt σ) k ((f₁ * f₂).map σ) =
      mahler (H.normAt σ) k (f₁.map σ) + mahler (H.normAt σ) k (f₂.map σ) := by
    intro σ
    rw [map_mul]
    exact hM n k _ _ _ (fun h => h₁ (map_injective σ σ.injective (by rw [h, map_zero])))
      (fun h => h₂ (map_injective σ σ.injective (by rw [h, map_zero])))
  rw [finsum_log_gaussNorm_mul h₁ h₂]
  simp_rw [hmah]
  rw [← mul_add]
  congr 1
  have hs : ∑ σ : K →+* ℂ, (mahler (H.normAt σ) k (f₁.map σ) + mahler (H.normAt σ) k (f₂.map σ) +
      (k : ℝ) * ((δ₁ + δ₂ : ℕ) : ℝ) * (harmonic (n - 1) : ℝ) / 2) =
      ∑ σ : K →+* ℂ, (mahler (H.normAt σ) k (f₁.map σ) + (k : ℝ) * δ₁ * (harmonic (n - 1) : ℝ) / 2) +
      ∑ σ : K →+* ℂ, (mahler (H.normAt σ) k (f₂.map σ) + (k : ℝ) * δ₂ * (harmonic (n - 1) : ℝ) / 2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    push_cast
    ring
  rw [hs]
  ring

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeMeetNull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem ConeMeetNull.null_of_mem_not_mem (hZ : ZeroLocusDimH.Statement) {n e : ℕ} (h : HermNorm n)
    (W W' : Ideal (MvPolynomial (Fin n) ℂ)) [W.IsPrime]
    (hW : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ ((e + 1 : ℕ) : WithBot ℕ∞))
    (g : MvPolynomial (Fin n) ℂ) (hgW' : g ∈ W') (hgW : g ∉ W) :
    Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W ∩ coneBall h W') = 0 := by
  set J : Ideal (MvPolynomial (Fin n) ℂ) := W ⊔ Ideal.span {g} with hJ

  have hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (e : ℕ) :=
    ZeroLocusDimH.le_of_add_one_le_succ
      ((ZeroLocusDimH.ringKrullDim_quot_sup_add_one_le W g hgW).trans hW)

  let φ : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ) :=
    (Matrix.transpose h.mat).mulVecLin.comp (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap
  have hφ : ∀ y, φ y = h.pointOf y := fun _ => rfl
  have hinj : Function.Injective φ := by
    have hu : IsUnit (Matrix.transpose h.mat) := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]; exact h.isUnit_det
    exact (Matrix.mulVec_injective_iff_isUnit.mpr hu).comp
      (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).injective
  obtain ⟨K, -, hK⟩ := (LinearMap.injective_iff_antilipschitz φ).mp hinj

  have hsub : coneBall h W ∩ coneBall h W' ⊆ φ ⁻¹' {x | ∀ q ∈ J, eval x q = 0} := by
    rintro y ⟨⟨-, hyW⟩, ⟨-, hyW'⟩⟩
    have hle : J ≤ RingHom.ker (eval (h.pointOf y)) := by
      refine sup_le (fun q hq => (RingHom.mem_ker).2 (hyW q hq)) ?_
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      exact hyW' g hgW'
    intro q hq
    rw [hφ]
    exact (RingHom.mem_ker).1 (hle hq)
  have hdimH : dimH (coneBall h W ∩ coneBall h W') ≤ 2 * (e : ENNReal) :=
    (dimH_mono hsub).trans ((hK.dimH_preimage_le _).trans (hZ n e J hdim))
  have hlt : dimH (coneBall h W ∩ coneBall h W') < (((2 * (e + 1) : ℕ) : NNReal) : ENNReal) := by
    refine hdimH.trans_lt ?_
    rw [ENNReal.coe_natCast]
    exact_mod_cast (by omega : 2 * e < 2 * (e + 1))
  rw [show ((2 * (e + 1) : ℕ) : ℝ) = (((2 * (e + 1) : ℕ) : NNReal) : ℝ) from
    (NNReal.coe_natCast _).symm]
  exact hausdorffMeasure_of_dimH_lt hlt

theorem ConeMeetNull.proof (hZ : ZeroLocusDimH.Statement) : ConeMeetNull.Statement := by
  intro n e h W W' hWp hW'p hne hW hW'
  by_cases hle : W' ≤ W
  ·
    have hnle : ¬ W ≤ W' := fun h' => hne (le_antisymm h' hle)
    obtain ⟨g, hgW, hgW'⟩ := Set.not_subset.mp hnle
    rw [Set.inter_comm]
    exact ConeMeetNull.null_of_mem_not_mem hZ h W' W hW' g hgW hgW'
  · obtain ⟨g, hgW', hgW⟩ := Set.not_subset.mp hle
    exact ConeMeetNull.null_of_mem_not_mem hZ h W W' hW g hgW' hgW

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChowFormHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem aeval_scale_of_isWeightedHomogeneous {σ R A : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] {w : σ → ℕ} {p : MvPolynomial σ R} {a : ℕ} (hp : IsWeightedHomogeneous w p a)
    (t : A) (u : σ → A) : aeval (fun j => t ^ w j * u j) p = t ^ a * aeval u p := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  have hw : ∑ j ∈ d.support, w j * d j = a := by
    rw [← hp (mem_support_iff.mp hd), Finsupp.weight_apply, Finsupp.sum]
    simp [smul_eq_mul, mul_comm]
  rw [hw]
  ring

variable {F : Type} [Field F] {n k : ℕ}

theorem scale_mem_incidence {I : Ideal (MvPolynomial (Fin n) F)}
    {u : Fin k × Fin n → AlgebraicClosure F} (hu : u ∈ incidence I k) (i : Fin k)
    (t : AlgebraicClosure F) : (fun ij => t ^ inGroup i ij * u ij) ∈ incidence I k := by
  obtain ⟨x, hx0, hxI, hux⟩ := hu
  refine ⟨x, hx0, hxI, fun i' => ?_⟩
  have hc : ∀ j : Fin n, t ^ inGroup i (i', j) * u (i', j) * x j =
      t ^ (if i' = i then 1 else 0) * (u (i', j) * x j) := fun j => by rw [mul_assoc]; rfl
  refine Eq.trans (Finset.sum_congr rfl fun j _ => hc j) ?_
  rw [← Finset.mul_sum, hux i', mul_zero]

theorem component_vanish_incidence {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : ∀ u ∈ incidence I k, aeval u f = 0) (i : Fin k)
    {a : ℕ} (ha : a ∈ weightSet (inGroup (n := n) i) f) :
    ∀ u ∈ incidence I k, aeval u (weightedHomogeneousComponent (inGroup (n := n) i) a f) = 0 := by
  classical
  intro u hu
  set w := inGroup (n := n) i
  set S := weightSet w f
  set q : Polynomial (AlgebraicClosure F) :=
    ∑ b ∈ S, Polynomial.C (aeval u (weightedHomogeneousComponent w b f)) * Polynomial.X ^ b with hq_def
  have hq : q = 0 := by
    apply Polynomial.funext
    intro t
    have h1 := hf _ (scale_mem_incidence hu i t)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← sum_weightSet_component (w := w) f, map_sum] at h1
    simp only [hq_def, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
    rw [← h1]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [aeval_scale_of_isWeightedHomogeneous (weightedHomogeneousComponent_isWeightedHomogeneous b f),
      mul_comm]
  have hc := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p a) hq
  simp only [hq_def, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at hc
  rw [Finset.sum_ite_eq, if_pos ha] at hc
  exact hc

theorem IsChowForm.exists_isWeightedHomogeneous_inGroup {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) (i : Fin k) :
    ∃ a, IsWeightedHomogeneous (inGroup (n := n) i) f a := by
  obtain ⟨a, ha⟩ := weightSet_nonempty (w := inGroup (n := n) i) hf.1
  have hvan : ∀ u ∈ incidence I k, aeval u f = 0 := (hf.2 f).mpr dvd_rfl
  obtain ⟨r, hr⟩ := (hf.2 _).mp (component_vanish_incidence hvan i ha)
  have hc := component_ne_zero_of_mem ha
  rw [hr] at hc
  refine isWeightedHomogeneous_of_mul_left (m := a) ?_ hf.1 (right_ne_zero_of_mul hc)
  rw [← hr]
  exact weightedHomogeneousComponent_isWeightedHomogeneous a f

theorem zero_mem_incidence {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsProjPrime P) (k : ℕ) :
    (0 : Fin k × Fin n → AlgebraicClosure F) ∈ incidence P k := by
  obtain ⟨j, hj⟩ := hP.isRelevant
  have hex : ∃ x ∈ zeroLocus (AlgebraicClosure F) P, x ≠ 0 := by
    by_contra h
    push Not at h
    apply hj
    have hrad : X j ∈ vanishingIdeal F (zeroLocus (AlgebraicClosure F) P) := by
      rw [mem_vanishingIdeal_iff]
      intro x hx
      rw [h x hx]
      simp
    rwa [vanishingIdeal_zeroLocus_eq_radical, hP.isPrime.radical] at hrad
  obtain ⟨x, hx, hx0⟩ := hex
  exact ⟨x, hx0, fun g hg => mem_zeroLocus_iff.mp hx g hg, fun i => by simp⟩

theorem IsChowForm.exists_multiHomog {P : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hP : IsProjPrime P) (hf : IsChowForm P k f) :
    ∃ δ, 1 ≤ δ ∧ IsMultiHomog δ f := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    exact ⟨1, le_rfl, fun d _ => funext fun i => i.elim0⟩
  choose a ha using fun i => hf.exists_isWeightedHomogeneous_inGroup i
  have hδ : IsMultiHomog (a ⟨0, hk⟩) f := (isMultiHomog_iff _ _).mpr fun i => by
    rw [hf.degrees_eq ha ⟨0, hk⟩ i]
    exact ha i
  refine ⟨a ⟨0, hk⟩, Nat.one_le_iff_ne_zero.mpr fun h0 => ?_, hδ⟩
  rw [h0] at hδ
  have hd0 : ∀ d ∈ f.support, d = 0 := by
    intro d hd
    have h := congrFun (hδ (mem_support_iff.mp hd))
    ext ij
    by_contra hne
    have h1 := h ij.1
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at h1
    have h2 := (Finset.sum_eq_zero_iff.mp h1) ij (Finsupp.mem_support_iff.mpr hne)
    simp [groupWeight] at h2
    exact hne h2
  have hC : f = C (AddMonoidAlgebra.coeff f 0) := by
    ext d
    rw [coeff_C]
    split_ifs with hd
    · rw [hd]
    · by_contra hne
      exact hd (hd0 d (mem_support_iff.mpr hne)).symm
  have hz := (hf.2 f).mpr dvd_rfl 0 (zero_mem_incidence hP k)
  rw [hC, aeval_C, map_eq_zero_iff _ (algebraMap F (AlgebraicClosure F)).injective] at hz
  exact hf.1 (by rw [hC, hz, C_0])

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPolyLocalGeneratorsDiff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Module

noncomputable section

variable {n : ℕ}

def polyDiff (p : Fin n → ℂ) : MvPolynomial (Fin n) ℂ →ₗ[ℂ] (Fin n → ℂ) where
  toFun f j := eval p (pderiv j f)
  map_add' f g := by ext j; simp
  map_smul' c f := by ext j; simp

theorem polyDiff_apply (p : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) (j : Fin n) :
    polyDiff p f j = eval p (pderiv j f) := rfl

def dotForm : (Fin n → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin n → ℂ) :=
  LinearMap.mk₂ ℂ (fun w v => ∑ j, w j * v j)
    (fun w w' v => by simp [add_mul, Finset.sum_add_distrib])
    (fun c w v => by simp [mul_assoc, Finset.mul_sum])
    (fun w v v' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c w v => by simp [mul_left_comm, Finset.mul_sum])

theorem dotForm_apply (w v : Fin n → ℂ) : dotForm w v = ∑ j, w j * v j := rfl

theorem mem_polyTangent_iff (S : Set (MvPolynomial (Fin n) ℂ)) (p v : Fin n → ℂ) :
    v ∈ polyTangent S p ↔ ∀ q ∈ S, dotForm (polyDiff p q) v = 0 := Iff.rfl

theorem polyTangent_eq_of_subset (S T : Set (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (hST : S ⊆ T) (h : ∀ f ∈ T, polyDiff p f ∈ Submodule.span ℂ (polyDiff p '' S)) :
    polyTangent S p = polyTangent T p := by
  ext v
  rw [mem_polyTangent_iff, mem_polyTangent_iff]
  refine ⟨fun hv f hf => ?_, fun hv f hf => hv f (hST hf)⟩
  have hle : Submodule.span ℂ (polyDiff p '' S) ≤ LinearMap.ker (dotForm.flip v) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.flip_apply]
    exact hv g hg
  have := hle (h f hf)
  simpa only [LinearMap.mem_ker, LinearMap.flip_apply] using this

def tanLinPoly (p w : Fin n → ℂ) : MvPolynomial (Fin n) ℂ := ∑ j, C (w j) * (X j - C (p j))

theorem eval_tanLinPoly (p w : Fin n → ℂ) : eval p (tanLinPoly p w) = 0 := by
  simp [tanLinPoly]

theorem tanLinPoly_add (p w w' : Fin n → ℂ) : tanLinPoly p (w + w') = tanLinPoly p w + tanLinPoly p w' := by
  simp only [tanLinPoly, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem tanLinPoly_smul (p w : Fin n → ℂ) (c : ℂ) : tanLinPoly p (c • w) = C c * tanLinPoly p w := by
  simp only [tanLinPoly, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem tanLinPoly_zero (p : Fin n → ℂ) : tanLinPoly p 0 = 0 := by
  simp [tanLinPoly]

theorem tanLinPoly_single (p : Fin n → ℂ) (i : Fin n) :
    tanLinPoly p (Pi.single i 1) = X i - C (p i) := by
  classical
  simp only [tanLinPoly, Pi.single_apply]
  simp

theorem polyDiff_tanLinPoly (p w : Fin n → ℂ) : polyDiff p (tanLinPoly p w) = w := by
  classical
  ext i
  simp [polyDiff_apply, tanLinPoly, Pi.single_apply]

theorem X_sub_C_mem_ker (p : Fin n → ℂ) (j : Fin n) :
    X j - C (p j) ∈ RingHom.ker (eval p) := by
  simp [RingHom.mem_ker]

theorem sub_tanLinPoly_mem_sq (p : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) :
    f - C (eval p f) - tanLinPoly p (polyDiff p f) ∈ RingHom.ker (eval p) ^ 2 := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a =>
    have h : polyDiff p (C a) = 0 := by ext j; simp [polyDiff_apply]
    simp [h, tanLinPoly_zero]
  | add f g hf hg =>
    have e : f + g - C (eval p (f + g)) - tanLinPoly p (polyDiff p (f + g)) =
        (f - C (eval p f) - tanLinPoly p (polyDiff p f)) +
          (g - C (eval p g) - tanLinPoly p (polyDiff p g)) := by
      rw [map_add (f := _), map_add (f := _), map_add (f := _), tanLinPoly_add]; ring
    rw [e]
    exact add_mem hf hg
  | mul_X f i hf =>
    have hd : polyDiff p (f * X i) = p i • polyDiff p f + eval p f • Pi.single i 1 := by
      ext j
      simp only [polyDiff_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Derivation.leibniz,
        pderiv_X, map_add]
      by_cases hij : i = j
      · subst hij
        simp only [Pi.single_eq_same, mul_one, map_mul, eval_X]
        ring
      · simp only [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne (Ne.symm hij), mul_zero, map_zero,
          map_mul, eval_X, zero_add, add_zero]
    have e : f * X i - C (eval p (f * X i)) - tanLinPoly p (polyDiff p (f * X i)) =
        C (p i) * (f - C (eval p f) - tanLinPoly p (polyDiff p f)) +
          (f - C (eval p f)) * (X i - C (p i)) := by
      rw [hd, tanLinPoly_add, tanLinPoly_smul, tanLinPoly_smul, tanLinPoly_single, map_mul, eval_X, map_mul]
      ring
    rw [e]
    refine add_mem (Ideal.mul_mem_left _ _ hf) ?_
    rw [pow_two]
    refine Ideal.mul_mem_mul ?_ (X_sub_C_mem_ker p i)
    simp [RingHom.mem_ker]

theorem mem_sq_of_polyDiff_eq_zero (p : Fin n → ℂ) {f : MvPolynomial (Fin n) ℂ}
    (h0 : eval p f = 0) (h1 : polyDiff p f = 0) : f ∈ RingHom.ker (eval p) ^ 2 := by
  simpa [h0, h1, tanLinPoly_zero] using sub_tanLinPoly_mem_sq p f

theorem mem_span_sup_sq_of_polyDiff_mem (p : Fin n → ℂ) {ι : Type*} [Fintype ι]
    (h : ι → MvPolynomial (Fin n) ℂ) (hh : ∀ i, eval p (h i) = 0) {f : MvPolynomial (Fin n) ℂ}
    (hf : eval p f = 0) (hd : polyDiff p f ∈ Submodule.span ℂ (Set.range (polyDiff p ∘ h))) :
    f ∈ Ideal.span (Set.range h) ⊔ RingHom.ker (eval p) ^ 2 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hd
  have hg0 : eval p (f - ∑ i, C (c i) * h i) = 0 := by simp [hf, hh]
  have hg1 : polyDiff p (f - ∑ i, C (c i) * h i) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, C_mul', map_smul]
    rw [← hc]
    simp
  have hsum : ∑ i, C (c i) * h i ∈ Ideal.span (Set.range h) :=
    sum_mem fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  have e : f = (f - ∑ i, C (c i) * h i) + ∑ i, C (c i) * h i := by ring
  rw [e]
  exact add_mem (Ideal.mem_sup_right (mem_sq_of_polyDiff_eq_zero p hg0 hg1))
    (Ideal.mem_sup_left hsum)

theorem maximalIdeal_le_span_of_le_sup_sq {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (T : Set R)
    (h : IsLocalRing.maximalIdeal R ≤ Ideal.span T ⊔ IsLocalRing.maximalIdeal R ^ 2) :
    IsLocalRing.maximalIdeal R ≤ Ideal.span T := by
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
    (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  rwa [Ideal.smul_eq_mul, ← pow_two]

theorem exists_polyDiff_basis (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) :
    ∃ q : Fin (n - finrank ℂ (polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) p)) →
        MvPolynomial (Fin n) ℂ,
      (∀ i, q i ∈ J) ∧ LinearIndependent ℂ (polyDiff p ∘ q) ∧
        ∀ f ∈ J, polyDiff p f ∈ Submodule.span ℂ (Set.range (polyDiff p ∘ q)) := by
  set D : Submodule ℂ (Fin n → ℂ) := (J.restrictScalars ℂ).map (polyDiff p) with hDdef
  have hinj : Function.Injective (dotForm : (Fin n → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin n → ℂ)) := by
    intro w w' hww
    ext j
    have := LinearMap.congr_fun hww (Pi.single j 1)
    classical
    simpa [dotForm_apply, Pi.single_apply] using this
  set W := D.map (dotForm : (Fin n → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin n → ℂ))
  have hW : finrank ℂ W = finrank ℂ D :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj D)).symm
  have hco : W.dualCoannihilator = polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) p := by
    ext v
    rw [Submodule.mem_dualCoannihilator, mem_polyTangent_iff]
    constructor
    · intro h q hq
      exact h _ (Submodule.mem_map_of_mem (Submodule.mem_map_of_mem (p := J.restrictScalars ℂ) hq))
    · rintro h _ ⟨w, ⟨q, hq, rfl⟩, rfl⟩
      exact h q hq
  have hsum := Subspace.finrank_add_finrank_dualCoannihilator_eq W
  rw [hco, hW, Module.finrank_fin_fun] at hsum
  have hD : finrank ℂ D = n - finrank ℂ (polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) p) := by
    omega
  let b := Module.finBasisOfFinrankEq ℂ D hD
  have hb : ∀ i, ∃ q ∈ J, polyDiff p q = (b i : Fin n → ℂ) := by
    intro i
    obtain ⟨q, hq, e⟩ := Submodule.mem_map.1 (b i).2
    exact ⟨q, hq, e⟩
  choose q hqJ hq using hb
  have hcomp : polyDiff p ∘ q = D.subtype ∘ b := funext hq
  refine ⟨q, hqJ, ?_, ?_⟩
  · rw [hcomp]
    exact b.linearIndependent.map' D.subtype (Submodule.ker_subtype D)
  · intro f hf
    have hspan : Submodule.span ℂ (Set.range (polyDiff p ∘ q)) = D := by
      rw [hcomp, Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
    rw [hspan]
    exact Submodule.mem_map_of_mem (p := J.restrictScalars ℂ) hf

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartChoiceAlgClosed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChartChoiceAlgClosed.Statement : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (q : MvPolynomial (Fin e × Fin n) F),
    IsProjPrime I → IsChowForm I (e + 1) f → Prime q → ∃ t : Fin n → F, ¬ q ∣ specFirst f t

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSectionOrderAlgClosed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial


open Classical in
def SectionOrderAlgClosed.Statement : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I →
      specFirst f u ≠ 0 ∧ ∀ q : MvPolynomial (Fin e × Fin n) F, Irreducible q →
        emultiplicity q (specFirst f u) =
          ∑ W ∈ (divCycle I u).support with Ideal.span {q} = incIdeal W e,
            ((divCycle I u W : ℕ) : ℕ∞)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowFormBirationalAlgClosed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChowFormBirationalAlgClosed.Statement : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] (n k : ℕ) (P : Ideal (MvPolynomial (Fin n) F))
    (g : MvPolynomial (Fin (k + 1) × Fin n) F) (c : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ P)),
    IsProjPrime P → IsChowForm P (k + 1) g → ∑ j, c j * genPt P j = 1 →
      ∃ t : Fin n → F, (∑ l, C (t l) * pderiv (0, l) g) ∉ incIdeal P (k + 1) ∧
        ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) *
              C (∑ l, algebraMap F (FractionRing (MvPolynomial (Fin n) F ⧸ P)) (t l) * genPt P l) =
            aeval (genSubst (genPt P) c) (∑ l, C (t l) * pderiv (0, l) g) * C (genPt P m)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartResidueDegreeAlgClosed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChartResidueDegreeAlgClosed.Statement : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] (n e : ℕ) (I W : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t u : Fin n → F)
    (q : MvPolynomial (Fin e × Fin n) F) (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I → Prime q → p = Ideal.span {q} →
      ¬ q ∣ specFirst f t → W ∈ relComps (I ⊔ Ideal.span {linForm u}) → q ∈ incIdeal W e →
        linForm t ∉ W →
          Module.length (Localization.AtPrime p) (ChartLoc I t e p ⧸ chartIdeal I t e p W) = 1

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartNormAlgClosed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChartNormAlgClosed.Statement : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t : Fin n → F)
    (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → (p = ⊥ ∨ ∃ q, Prime q ∧ p = Ideal.span {q}) →
      specFirst f t ∉ p → ∀ u : Fin n → F,
        algebraMap _ (Localization.AtPrime p) (specFirst f u) =
          algebraMap _ (Localization.AtPrime p) (specFirst f t) *
            LinearMap.det (LinearMap.mulLeft (Localization.AtPrime p)
              (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u)))

end

end GroundTheory.Heights₂.Heights
end
