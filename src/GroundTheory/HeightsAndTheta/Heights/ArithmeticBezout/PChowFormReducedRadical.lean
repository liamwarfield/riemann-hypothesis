module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFundCycleBaseChange
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.SmoothOfRegular
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Cartier
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsGraphAreaIntegral
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormReducedRadical
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

section Helpers

variable {F : Type*} [Field F] {n k : ℕ}

private theorem mem_incIdeal_iff_aux {P : Ideal (MvPolynomial (Fin n) F)} {g : MvPolynomial (Fin k × Fin n) F} :
    g ∈ incIdeal P k ↔ ∀ u ∈ incidence P k, aeval u g = 0 := by
  simp only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker]

private theorem incidence_mono {I W : Ideal (MvPolynomial (Fin n) F)} (hIW : I ≤ W)
    {u : Fin k × Fin n → AlgebraicClosure F} (hu : u ∈ incidence W k) : u ∈ incidence I k := by
  obtain ⟨x, hx0, hxW, hxu⟩ := hu
  exact ⟨x, hx0, fun g hg => hxW g (hIW hg), hxu⟩

private theorem exists_relComps_of_mem_incidence {J : Ideal (MvPolynomial (Fin n) F)}
    {u : Fin k × Fin n → AlgebraicClosure F} (hu : u ∈ incidence J k) :
    ∃ W ∈ relComps J, u ∈ incidence W k := by
  obtain ⟨x, hx0, hxJ, hxu⟩ := hu
  let φ : MvPolynomial (Fin n) F →ₐ[F] AlgebraicClosure F := aeval x
  have hP : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  have hJP : J ≤ RingHom.ker φ := fun g hg => RingHom.mem_ker.mpr (hxJ g hg)
  obtain ⟨W, hW, hWP⟩ := Ideal.exists_minimalPrimes_le hJP
  refine ⟨W, ⟨hW, ?_⟩, x, hx0, fun g hg => RingHom.mem_ker.mp (hWP hg), hxu⟩
  by_contra hrel
  apply hx0
  funext j
  have hj : X j ∈ W := by
    by_contra hj
    exact hrel ⟨j, hj⟩
  have := RingHom.mem_ker.mp (hWP hj)
  simpa [φ] using this

private theorem mem_support_fundCycle_iff {J : Ideal (MvPolynomial (Fin n) F)} (hJ : J.IsRadical)
    {W : Ideal (MvPolynomial (Fin n) F)} : W ∈ (fundCycle J).support ↔ W ∈ relComps J := by
  classical
  rw [Finsupp.mem_support_iff]
  unfold fundCycle
  rw [Finsupp.onFinset_apply]
  constructor
  · intro h
    by_contra h'
    exact h (if_neg h')
  · intro h
    rw [if_pos h, localMult_eq_one_of_isRadical hJ h.1]
    exact one_ne_zero

end Helpers

theorem ChowFormReduced.proof_of_prime_separate (hPrime : IncIdealPrime.Statement) (hSep : IncIdealSeparate.Statement) :
    ChowFormReduced.Statement := by
  classical
  intro F _ n k J h hJh hJr hch
  have hproj : ∀ W ∈ (fundCycle J).support, IsProjPrime W :=
    fun W hW => isProjPrime_of_mem_support_fundCycle hJh hW
  have hrel : ∀ W ∈ (fundCycle J).support, W ∈ relComps J :=
    fun W hW => (mem_support_fundCycle_iff hJr).mp hW

  have hspan : ∀ g, h ∣ g ↔ ∀ W ∈ (fundCycle J).support, g ∈ incIdeal W k := by
    intro g
    rw [← hch.2 g]
    constructor
    · intro hg W hW
      exact mem_incIdeal_iff_aux.mpr fun u hu => hg u (incidence_mono (hrel W hW).1.1.2 hu)
    · intro hg u hu
      obtain ⟨W, hW, huW⟩ := exists_relComps_of_mem_incidence hu
      exact mem_incIdeal_iff_aux.mp (hg W ((mem_support_fundCycle_iff hJr).mpr hW)) u huW

  have hsep : ∀ W ∈ (fundCycle J).support, ∀ W' ∈ (fundCycle J).support,
      incIdeal W' k ≤ incIdeal W k → W' = W := by
    intro W hW W' hW' hle
    have hne : incIdeal W' k ≠ ⊥ := fun hb => hch.1 (by
      have := (hspan h).mp dvd_rfl W' hW'
      rwa [hb, Ideal.mem_bot] at this)
    have hWW' : W' ≤ W := hSep F n k W W' (hproj W hW) (hproj W' hW') hne hle
    exact le_antisymm hWW' ((hrel W hW).1.2 (hrel W' hW').1.1 hWW')

  have hprin : ∀ W ∈ (fundCycle J).support, ∃ q, Prime q ∧ incIdeal W k = Ideal.span {q} := by
    intro W hW
    have hPW : (incIdeal W k).IsPrime := hPrime F n k W (hproj W hW).isPrime (hproj W hW).isRelevant
    have hhW : h ∈ incIdeal W k := (hspan h).mp dvd_rfl W hW
    obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hch.1
    have hprod : (UniqueFactorizationMonoid.factors h).prod ∈ incIdeal W k := by
      rwa [← hu, Ideal.mul_unit_mem_iff_mem _ u.isUnit] at hhW
    obtain ⟨q, hqf, hqW⟩ := (hPW.multiset_prod_mem_iff_exists_mem _).1 hprod
    have hq : Prime q := UniqueFactorizationMonoid.prime_of_factor q hqf
    have hqh : q ∣ h := UniqueFactorizationMonoid.dvd_of_mem_factors hqf
    have hqle : Ideal.span {q} ≤ incIdeal W k := (Ideal.span_singleton_le_iff_mem _).mpr hqW
    refine ⟨q, hq, le_antisymm ?_ hqle⟩
    have hqP : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
    have hinf : (fundCycle J).support.inf (fun W' => incIdeal W' k) ≤ Ideal.span {q} := by
      intro g hg
      rw [Ideal.mem_span_singleton]
      exact dvd_trans hqh ((hspan g).mpr fun W' hW' =>
        Finset.inf_le (f := fun W' => incIdeal W' k) hW' hg)
    obtain ⟨W', hW', hle⟩ := hqP.inf_le'.mp hinf
    have hW'W : W' = W := hsep W hW W' hW' (hle.trans hqle)
    rw [← hW'W]
    exact hle
  choose! q hq hqspan using hprin

  have hdvd₁ : (∏ W ∈ (fundCycle J).support, q W) ∣ h := by
    refine Finset.prod_dvd_of_isRelPrime ?_ fun W hW => ?_
    · intro W hW W' hW' hne
      refine (hq W hW).irreducible.isRelPrime_iff_not_dvd.mpr fun hdvd => hne ?_
      have hmem : q W' ∈ incIdeal W k := by
        rw [hqspan W hW]
        exact Ideal.mem_span_singleton.mpr hdvd
      refine (hsep W hW W' hW' ?_).symm
      rw [hqspan W' hW']
      exact (Ideal.span_singleton_le_iff_mem _).mpr hmem
    · have := (hspan h).mp dvd_rfl W hW
      rw [hqspan W hW] at this
      exact Ideal.mem_span_singleton.mp this
  have hdvd₂ : h ∣ ∏ W ∈ (fundCycle J).support, q W := by
    refine (hspan _).mpr fun W hW => ?_
    rw [hqspan W hW]
    exact Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem q hW)
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd hdvd₁ hdvd₂
  obtain ⟨r, hr, hur⟩ := (isUnit_iff_eq_C_of_isReduced (P := (u : MvPolynomial (Fin k × Fin n) F))).mp
    u.isUnit
  refine ⟨r, hr.ne_zero, q, fun W hW => ⟨(hq W hW).ne_zero, fun g => ?_⟩, ?_⟩
  · rw [← mem_incIdeal_iff_aux, hqspan W hW, Ideal.mem_span_singleton]
  · rw [Finset.prod_congr rfl fun W hW => by rw [fundCycle_apply_of_isRadical hJr hW, pow_one],
      ← hu, hur, mul_comm]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSphereMeanLinearBall
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Set

noncomputable section

namespace SphereMeanLinearBall

theorem std_norm (n : ℕ) (v : Fin n → ℂ) : (HermNorm.std n).norm v = √(∑ j, ‖v j‖ ^ 2) := by
  simp [HermNorm.norm, HermNorm.std]

theorem std_dualNorm (n : ℕ) (y : Fin n → ℂ) :
    (HermNorm.std n).dualNorm y = √(∑ j, ‖y j‖ ^ 2) := by
  simp [HermNorm.dualNorm, HermNorm.std]

theorem sum_sq_nrmv_le (n : ℕ) (w : Fin n → ℂ) :
    ∑ j, ‖nrmv (HermNorm.std n) w j‖ ^ 2 ≤ 1 := by
  have hS : 0 ≤ ∑ j, ‖w j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have e : ∀ j, ‖nrmv (HermNorm.std n) w j‖ ^ 2 = (∑ j, ‖w j‖ ^ 2)⁻¹ * ‖w j‖ ^ 2 := by
    intro j
    rw [nrmv, std_norm, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow, Real.sq_sqrt hS]
  rw [Finset.sum_congr rfl fun j _ => e j, ← Finset.mul_sum]
  rcases eq_or_ne (∑ j, ‖w j‖ ^ 2) 0 with h | h
  · simp [h]
  · rw [inv_mul_cancel₀ h]

theorem norm_sum_mul_le (n : ℕ) (a b : Fin n → ℂ) :
    ‖∑ j, a j * b j‖ ≤ √(∑ j, ‖a j‖ ^ 2) * √(∑ j, ‖b j‖ ^ 2) := by
  refine (norm_sum_le _ _).trans ?_
  simp_rw [norm_mul]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

theorem sum_sq_pos {n : ℕ} {y : Fin n → ℂ} (hy : y ≠ 0) : 0 < ∑ j, ‖y j‖ ^ 2 := by
  refine lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) fun h => hy ?_
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg ‖y j‖).mp h.symm
  funext j
  simpa using h0 j (Finset.mem_univ j)

theorem fsLog_nrmv_nonpos (n : ℕ) (y w : Fin n → ℂ) :
    fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y ≤ 0 := by
  rw [fsLog, std_dualNorm]
  refine Real.log_nonpos (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) ?_
  refine div_le_one_of_le₀ ?_ (Real.sqrt_nonneg _)
  refine (norm_sum_mul_le n _ _).trans ?_
  have h1 : √(∑ j, ‖nrmv (HermNorm.std n) w j‖ ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact sum_sq_nrmv_le n w
  exact mul_le_of_le_one_left (Real.sqrt_nonneg _) h1

end SphereMeanLinearBall


open SphereMeanLinearBall in
theorem SphereMeanLinearBall.proof (h1 : SphereMeanLinear.Statement) : SphereMeanLinearBall.Statement := by
  intro n y hy
  set g : (Fin n → ℂ) → ℝ := fun w => fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y with hg
  have hpos := sum_sq_pos hy
  set r : ℝ := √(∑ j, ‖y j‖ ^ 2) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hpos

  let p : Fin n → ℂ := fun j => ((r : ℂ))⁻¹ * star (y j)
  have hp : ∑ j, ‖p j‖ ^ 2 = 1 := by
    have e : ∀ j, ‖p j‖ ^ 2 = (∑ j, ‖y j‖ ^ 2)⁻¹ * ‖y j‖ ^ 2 := by
      intro j
      show ‖((r : ℂ))⁻¹ * star (y j)‖ ^ 2 = _
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr0.le, norm_star, mul_pow,
        inv_pow, hr, Real.sq_sqrt hpos.le]
    rw [Finset.sum_congr rfl fun j _ => e j, ← Finset.mul_sum, inv_mul_cancel₀ hpos.ne']
  have hkey : ∀ a : Fin n → ℂ, Real.log ‖∑ j, a j * star (p j)‖ = fsLog (HermNorm.std n) a y := by
    intro a
    have e : ∑ j, a j * star (p j) = ((r : ℂ))⁻¹ * ∑ j, a j * y j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [p, star_mul', star_inv₀, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
      ring
    rw [e, fsLog, std_dualNorm, ← hr, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hr0.le, div_eq_inv_mul]

  let e := (Equiv.uniqueProd (Fin n) (Fin 1)).symm
  let L1 : (Fin 1 × Fin n → ℂ) ≃L[ℝ] (Fin n → ℂ) :=
    (LinearEquiv.funCongrLeft ℝ ℂ e).toContinuousLinearEquiv
  have hL1 : ∀ u, (fun j => u (0, j)) = L1 u := by
    intro u
    funext j
    simp [L1, e]
  have hS : {u : Fin 1 × Fin n → ℂ | ∀ i, (HermNorm.std n).norm (fun j => u (i, j)) < 1} =
      L1 ⁻¹' ballH (HermNorm.std n) := by
    ext u
    simp only [mem_ofPred_eq, mem_preimage, ballH, Fin.forall_fin_one, hL1]
  have hmean : ⨍ w in ballH (HermNorm.std n), g w = -(harmonic (n - 1) : ℝ) / 2 := by
    rw [← h1 n p hp, sphereMean, hS,
      ← SphereMean.setAverage_comp_linearEquiv volume volume L1 (ballH (HermNorm.std n)) g]
    congr 1
    funext u
    rw [hkey]
    simp only [hg]
    rw [← hL1 u]
    rfl
  refine ⟨?_, fun w => fsLog_nrmv_nonpos n y w, hmean⟩
  rcases eq_or_ne (harmonic (n - 1)) 0 with hH | hH
  ·
    have hn1 : n - 1 = 0 := by
      by_contra hne
      exact (harmonic_pos hne).ne' hH
    have hn : n = 1 := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0
        exact absurd (Subsingleton.elim y 0) hy
      · omega
    subst hn
    have hz : g = 0 := by
      funext w
      simp only [hg, Pi.zero_apply, fsLog, std_dualNorm, nrmv, std_norm, Fin.sum_univ_one]
      rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _), norm_mul, norm_mul, norm_inv,
        Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
      have hy0 : y 0 ≠ 0 := fun h => hy (funext fun j => by rw [Subsingleton.elim j 0, h]; rfl)
      rcases eq_or_ne (w 0) 0 with hw | hw
      · simp [hw]
      · rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw), one_mul,
          div_self (norm_ne_zero_iff.mpr hy0), Real.log_one]
    rw [hz]
    exact integrableOn_zero
  ·
    by_contra hni
    have h0 : ⨍ w in ballH (HermNorm.std n), g w = 0 := by
      rw [setAverage_eq, integral_undef hni, smul_zero]
    rw [hmean] at h0
    exact hH (by exact_mod_cast (by linarith : (harmonic (n - 1) : ℝ) = 0))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartChoiceAlgClosed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartChoiceAlgClosed

variable {F : Type} [Field F] {n e : ℕ}

theorem isChowForm_iff_span {P : Ideal (MvPolynomial (Fin n) F)} {k : ℕ}
    {g : MvPolynomial (Fin k × Fin n) F} :
    IsChowForm P k g ↔ g ≠ 0 ∧ incIdeal P k = Ideal.span {g} := by
  have hmem : ∀ G : MvPolynomial (Fin k × Fin n) F,
      G ∈ incIdeal P k ↔ ∀ v ∈ incidence P k, aeval v G = 0 := fun G => by
    simp [incIdeal, Submodule.mem_iInf, RingHom.mem_ker]
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, ?_⟩
    ext G
    rw [hmem, Ideal.mem_span_singleton]
    exact h G
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun G => ?_⟩
    rw [← hmem, h, Ideal.mem_span_singleton]

def shiftVar (e n : ℕ) : Fin e × Fin n → Fin (e + 1) × Fin n := fun jm => (jm.1.succ, jm.2)

def splitFirst (F : Type) [Field F] (e n : ℕ) :
    MvPolynomial (Fin (e + 1) × Fin n) F →ₐ[F] MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F) :=
  aeval fun ij => Fin.cases (motive := fun _ => MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))
    (X ij.2) (fun j => C (X (j, ij.2))) ij.1

def joinFirst (F : Type) [Field F] (e n : ℕ) :
    MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F) →+* MvPolynomial (Fin (e + 1) × Fin n) F :=
  eval₂Hom (rename (shiftVar e n)).toRingHom (fun m => X (0, m))

theorem joinFirst_splitFirst (p : MvPolynomial (Fin (e + 1) × Fin n) F) :
    joinFirst F e n (splitFirst F e n p) = p := by
  have h : (joinFirst F e n).comp (splitFirst F e n).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [joinFirst, splitFirst, MvPolynomial.algebraMap_eq]
    · rintro ⟨i, m⟩
      induction i using Fin.cases <;> simp [joinFirst, splitFirst, shiftVar]
  exact RingHom.congr_fun h p

theorem joinFirst_C (a : MvPolynomial (Fin e × Fin n) F) :
    joinFirst F e n (C a) = rename (shiftVar e n) a := by
  simp [joinFirst]

theorem specFirst_rename_shiftVar (q : MvPolynomial (Fin e × Fin n) F) :
    specFirst (rename (shiftVar e n) q) 0 = q := by
  unfold specFirst
  rw [bind₁_rename]
  have : (specFirstVar (0 : Fin n → F) ∘ shiftVar e n) = X := by
    funext jm
    simp [specFirstVar, shiftVar]
  rw [this, bind₁_X_left]
  rfl

theorem specFirst_zero_of_isMultiHomog {δ : ℕ} (hδ : 1 ≤ δ) {f : MvPolynomial (Fin (e + 1) × Fin n) F}
    (hf : IsMultiHomog δ f) : specFirst f 0 = 0 := by
  classical
  unfold specFirst
  conv_lhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun s hs => ?_
  rw [bind₁_monomial]
  obtain ⟨i, hi, h0⟩ : ∃ i ∈ s.support, i.1 = 0 := by
    by_contra hno
    push Not at hno
    have hw := congrFun (hf (mem_support_iff.mp hs)) 0
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at hw
    have : ∑ c ∈ s.support, (s c • groupWeight (e + 1) n c) 0 = 0 := by
      refine Finset.sum_eq_zero fun c hc => ?_
      simp [groupWeight, Ne.symm (hno c hc)]
    omega
  rw [Finset.prod_eq_zero hi, mul_zero]
  obtain ⟨a, m⟩ := i
  simp only at h0
  subst h0
  simp [specFirstVar, zero_pow (Finsupp.mem_support_iff.mp hi)]

theorem eval_map_splitFirst (J : Ideal (MvPolynomial (Fin e × Fin n) F)) (t : Fin n → F)
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) :
    eval (fun m => Ideal.Quotient.mk J (C (t m))) (map (Ideal.Quotient.mk J) (splitFirst F e n f)) =
      Ideal.Quotient.mk J (specFirst f t) := by
  rw [eval_map]
  have h : (eval₂Hom (Ideal.Quotient.mk J) (fun m => Ideal.Quotient.mk J (C (t m)))).comp
      (splitFirst F e n).toRingHom = (Ideal.Quotient.mk J).comp (bind₁ (specFirstVar t)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [splitFirst, MvPolynomial.algebraMap_eq]
    · rintro ⟨i, m⟩
      induction i using Fin.cases <;> simp [splitFirst, specFirstVar]
  exact RingHom.congr_fun h f

end ChartChoiceAlgClosed


open ChartChoiceAlgClosed in
theorem ChartChoiceAlgClosed.proof (h₁ : IncIdealPrime.Statement) (h₂ : ChowFormMultiHomog.Statement) :
    ChartChoiceAlgClosed.Statement := by
  intro F _ _ n e I f q hI hf hq
  classical
  obtain ⟨hf0, hspan⟩ := isChowForm_iff_span.mp hf
  have hfp : Prime f := by
    have := h₁ F n (e + 1) I hI.isPrime hI.isRelevant
    rw [hspan] at this
    exact (Ideal.span_singleton_prime hf0).mp this
  obtain ⟨δ, hδ, hhom⟩ := h₂ F n (e + 1) I f hI hf

  have hndvd : ¬ rename (shiftVar e n) q ∣ f := by
    rintro ⟨g, hg⟩
    rcases hfp.2.2 (rename (shiftVar e n) q) g (hg ▸ dvd_refl f) with ⟨h, hh⟩ | ⟨h, hh⟩
    · have := congrArg (fun p => specFirst p 0) hh
      rw [specFirst_rename_shiftVar] at this
      unfold specFirst at this
      rw [map_mul] at this
      have h0 : specFirst f 0 = 0 := specFirst_zero_of_isMultiHomog hδ hhom
      unfold specFirst at h0
      rw [h0, zero_mul] at this
      exact hq.ne_zero this
    · have hunit : IsUnit (rename (shiftVar e n) q) := by
        refine isUnit_iff_exists_inv.mpr ⟨h, ?_⟩
        apply mul_left_cancel₀ hf0
        calc f * (rename (shiftVar e n) q * h) = rename (shiftVar e n) q * (f * h) := by ring
          _ = f * 1 := by rw [← hh, ← hg, mul_one]
      have := hunit.map (bind₁ (specFirstVar (0 : Fin n → F)))
      have h' : bind₁ (specFirstVar (0 : Fin n → F)) (rename (shiftVar e n) q) = q :=
        specFirst_rename_shiftVar q
      rw [h'] at this
      exact hq.not_isUnit this
  set J : Ideal (MvPolynomial (Fin e × Fin n) F) := Ideal.span {q} with hJ
  have : J.IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  set P := map (Ideal.Quotient.mk J) (splitFirst F e n f) with hP
  have hP0 : P ≠ 0 := by
    intro h0
    have hmem : splitFirst F e n f ∈ RingHom.ker (map (σ := Fin n) (Ideal.Quotient.mk J)) := by
      rw [RingHom.mem_ker]; exact h0
    rw [MvPolynomial.ker_map, Ideal.mk_ker, hJ, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton] at hmem
    apply hndvd
    have := map_dvd (joinFirst F e n) hmem
    rwa [joinFirst_splitFirst, joinFirst_C] at this

  let g : ℕ ↪ F := Infinite.natEmbedding F
  have hinj : Function.Injective fun k : ℕ => Ideal.Quotient.mk J (C (g k)) := by
    intro a b hab
    apply g.injective
    apply (algebraMap F (MvPolynomial (Fin e × Fin n) F ⧸ J)).injective
    exact hab
  by_contra hall
  push Not at hall
  apply hP0
  refine eq_zero_of_eval_zero_at_prod_finset P
    (fun _ => (Finset.range (P.totalDegree + 1)).image (fun k : ℕ => Ideal.Quotient.mk J (C (g k))))
    (fun i => ?_) (fun x hx => ?_)
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
    exact Nat.lt_succ_of_le (degreeOf_le_totalDegree P i)
  · choose k _ hk using fun i => Finset.mem_image.mp (hx i)
    have hx' : x = fun m => Ideal.Quotient.mk J (C ((fun m => g (k m)) m)) := by
      funext m
      rw [← hk m]
    rw [hx', hP, eval_map_splitFirst]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (hall _))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPolyLocalGenerators
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Module IsLocalRing

noncomputable section

theorem PolyLocalGenerators.proof : PolyLocalGenerators.Statement := by
  intro n m J hJ hdim p hp htan
  classical

  have H := exists_polyDiff_basis J p
  rw [htan] at H
  obtain ⟨q, hqJ, hli, hspan⟩ := H
  have hqp : ∀ i, eval p (q i) = 0 := fun i => hp _ (hqJ i)
  have htq : polyTangent (Set.range q) p = polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) p := by
    refine polyTangent_eq_of_subset _ _ p (by rintro _ ⟨i, rfl⟩; exact hqJ i) fun f hf => ?_
    have := hspan f hf
    rwa [Set.range_comp] at this

  set M : Ideal (MvPolynomial (Fin n) ℂ) := RingHom.ker (eval p) with hMdef
  have hevsurj : Function.Surjective (eval p : MvPolynomial (Fin n) ℂ →+* ℂ) :=
    fun c => ⟨C c, by simp⟩
  have hMmax : M.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hevsurj
  have : J.IsPrime := hJ
  let ev : (MvPolynomial (Fin n) ℂ ⧸ J) →+* ℂ := Ideal.Quotient.lift J (eval p) (fun x hx => hp x hx)
  set N : Ideal (MvPolynomial (Fin n) ℂ ⧸ J) := RingHom.ker ev with hNdef
  have hevsurj' : Function.Surjective ev :=
    fun c => ⟨Ideal.Quotient.mk J (C c), by simp [ev]⟩
  have hNmax : N.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hevsurj'
  have hNM : N.comap (Ideal.Quotient.mk J) = M := by
    ext x
    simp only [Ideal.mem_comap, hNdef, hMdef, RingHom.mem_ker, ev, Ideal.Quotient.lift_mk]

  let P := Localization.AtPrime M
  let S := Localization.AtPrime N
  let ψ : P →+* S := Localization.localRingHom M N (Ideal.Quotient.mk J) hNM.symm
  let _ : Algebra P S := ψ.toAlgebra
  have halg : ∀ x, algebraMap P S x = ψ x := fun _ => rfl
  have hψmk : ∀ x, ψ (algebraMap (MvPolynomial (Fin n) ℂ) P x) =
      algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) S (Ideal.Quotient.mk J x) :=
    fun x => Localization.localRingHom_to_map M N (Ideal.Quotient.mk J) hNM.symm x
  have hsurj : Function.Surjective (algebraMap P S) := by
    intro z
    obtain ⟨a, t, rfl⟩ := IsLocalization.exists_mk'_eq N.primeCompl z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (t : MvPolynomial (Fin n) ℂ ⧸ J)
    have hyM : y ∈ M.primeCompl := by
      intro hyM'
      have hyN : y ∈ N.comap (Ideal.Quotient.mk J) := by rw [hNM]; exact hyM'
      apply t.2
      rw [← hy]
      exact hyN
    refine ⟨IsLocalization.mk' P x ⟨y, hyM⟩, ?_⟩
    rw [halg, Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hy

  have hdimS : ringKrullDim S = m := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height N S,
      NumbersDVR.MaximalIdealHeightFG.proof ℂ (MvPolynomial (Fin n) ℂ ⧸ J) N hNmax, hdim]

  let f : Fin (n - m) → P := fun i => algebraMap (MvPolynomial (Fin n) ℂ) P (q i)
  have hf : ∀ i, f i ∈ RingHom.ker (algebraMap P S) := by
    intro i
    rw [RingHom.mem_ker, halg, hψmk, Ideal.Quotient.eq_zero_iff_mem.2 (hqJ i), map_zero]
  have hmP : maximalIdeal P = M.map (algebraMap (MvPolynomial (Fin n) ℂ) P) :=
    (Localization.AtPrime.map_eq_maximalIdeal (I := M)).symm

  have hJcov : J ≤ Ideal.span (Set.range q) ⊔ M ^ 2 := fun x hx =>
    mem_span_sup_sq_of_polyDiff_mem p q hqp (hp x hx) (hspan x hx)
  obtain ⟨Cc, hCc⟩ := Submodule.exists_isCompl (Submodule.span ℂ (Set.range (polyDiff p ∘ q)))
  have hfinD : finrank ℂ (Submodule.span ℂ (Set.range (polyDiff p ∘ q))) = n - m := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hmn : m ≤ n := by
    rw [← htan]
    exact (Submodule.finrank_le _).trans (Module.finrank_fin_fun ℂ).le
  have hfinC : finrank ℂ Cc = m := by
    have := Submodule.finrank_add_eq_of_isCompl hCc
    rw [hfinD, Module.finrank_fin_fun] at this
    omega
  let c := Module.finBasisOfFinrankEq ℂ Cc hfinC
  let y : Fin m → MvPolynomial (Fin n) ℂ := fun k => tanLinPoly p (c k)
  have hMcov : M ≤ Ideal.span (Set.range (Sum.elim q y)) ⊔ M ^ 2 := by
    intro x hx
    refine mem_span_sup_sq_of_polyDiff_mem p (Sum.elim q y) ?_ (RingHom.mem_ker.1 hx) ?_
    · rintro (i | k)
      · exact hqp i
      · exact eval_tanLinPoly p _
    · have htop : Submodule.span ℂ (Set.range (polyDiff p ∘ Sum.elim q y)) = ⊤ := by
        rw [eq_top_iff, ← hCc.sup_eq_top]
        apply sup_le
        · apply Submodule.span_mono
          rintro _ ⟨i, rfl⟩
          exact ⟨Sum.inl i, rfl⟩
        · intro v hv
          have hCspan : Cc = Submodule.span ℂ (Set.range (Cc.subtype ∘ c)) := by
            rw [Set.range_comp, Submodule.span_image, c.span_eq, Submodule.map_subtype_top]
          rw [hCspan] at hv
          refine Submodule.span_mono ?_ hv
          rintro _ ⟨k, rfl⟩
          exact ⟨Sum.inr k, by simp [y, polyDiff_tanLinPoly]⟩
      rw [htop]
      exact Submodule.mem_top

  let φ : MvPolynomial (Fin n) ℂ →+* S :=
    (algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) S).comp (Ideal.Quotient.mk J)
  have hmS : maximalIdeal S = M.map φ := by
    calc maximalIdeal S = N.map (algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) S) :=
          (Localization.AtPrime.map_eq_maximalIdeal (I := N)).symm
      _ = (M.map (Ideal.Quotient.mk J)).map (algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) S) := by
          rw [← hNM, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
      _ = M.map φ := Ideal.map_map _ _
  have hφq : ∀ i, φ (q i) = 0 := by
    intro i
    simp [φ, Ideal.Quotient.eq_zero_iff_mem.2 (hqJ i)]
  have hS_le : maximalIdeal S ≤ Ideal.span (Set.range (φ ∘ y)) := by
    refine maximalIdeal_le_span_of_le_sup_sq (R := S) (Set.range (φ ∘ y)) ?_
    rw [hmS]
    have h1 := Ideal.map_mono (f := φ) hMcov
    rw [Ideal.map_sup, Ideal.map_span, Ideal.map_pow] at h1
    refine h1.trans (sup_le_sup ?_ ?_)
    · refine Ideal.span_le.2 ?_
      rintro _ ⟨_, ⟨i | k, rfl⟩, rfl⟩
      · simp [hφq]
      · exact Ideal.subset_span ⟨k, rfl⟩
    · exact le_rfl
  have hμ : (maximalIdeal S).spanFinrank ≤ m := by
    have heq : maximalIdeal S = Ideal.span (Set.range (φ ∘ y)) := by
      refine le_antisymm hS_le (Ideal.span_le.2 ?_)
      rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, hmS]
      exact Ideal.mem_map_of_mem _ (RingHom.mem_ker.2 (eval_tanLinPoly p _))
    rw [heq]
    calc (Ideal.span (Set.range (φ ∘ y))).spanFinrank ≤ (Set.range (φ ∘ y)).ncard :=
          Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)
      _ ≤ (Set.univ : Set (Fin m)).ncard := by
          rw [← Set.image_univ]
          exact Set.ncard_image_le Set.finite_univ
      _ = m := by simp [Set.ncard_univ]

  have hcov : RingHom.ker (algebraMap P S) ≤ Ideal.span (Set.range f) ⊔ maximalIdeal P ^ 2 := by
    intro z hz
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M.primeCompl z
    have hx0 : algebraMap P S (algebraMap (MvPolynomial (Fin n) ℂ) P x) = 0 := by
      rw [← IsLocalization.mk'_spec P x s, map_mul, RingHom.mem_ker.1 hz, zero_mul]
    rw [halg, hψmk] at hx0
    obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff N.primeCompl S _).1 hx0
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (t : MvPolynomial (Fin n) ℂ ⧸ J)
    have hwx : w * x ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, hw, ht]
    have hwJ : w ∉ J := by
      intro hwJ
      apply t.2
      rw [← hw, Ideal.Quotient.eq_zero_iff_mem.2 hwJ]
      exact zero_mem _
    have hxJ : x ∈ J := (hJ.mem_or_mem hwx).resolve_left hwJ
    have hx' : algebraMap (MvPolynomial (Fin n) ℂ) P x ∈
        Ideal.span (Set.range f) ⊔ maximalIdeal P ^ 2 := by
      have h1 := Ideal.mem_map_of_mem (algebraMap (MvPolynomial (Fin n) ℂ) P) (hJcov hxJ)
      rw [Ideal.map_sup, Ideal.map_span, Ideal.map_pow, ← hmP, ← Set.range_comp] at h1
      exact h1
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ hx'

  have hker := GroundTheory.Arith.Jacobian.ker_le_span_of_spanFinrank_le (P := P) (S := S) hsurj f hf hcov
    m hμ hdimS.ge

  have hloc : ∀ x ∈ J, ∃ s ∈ M.primeCompl, s * x ∈ Ideal.span (Set.range q) := by
    intro x hx
    have hx1 : algebraMap (MvPolynomial (Fin n) ℂ) P x ∈ Ideal.span (Set.range f) := by
      apply hker
      rw [RingHom.mem_ker, halg, hψmk, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
    have hspanf : Ideal.span (Set.range f) =
        (Ideal.span (Set.range q)).map (algebraMap (MvPolynomial (Fin n) ℂ) P) := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    rw [hspanf] at hx1
    obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff M.primeCompl P).1 hx1
    rw [← map_mul, IsLocalization.eq_iff_exists M.primeCompl P] at e
    obtain ⟨c', hc'⟩ := e
    refine ⟨c' * s, M.primeCompl.mul_mem c'.2 hs, ?_⟩
    have e2 : (c' : MvPolynomial (Fin n) ℂ) * s * x = c' * a := by
      rw [← hc']
      ring
    rw [e2]
    exact Ideal.mul_mem_left _ _ ha
  choose! σ hσM hσ using hloc
  obtain ⟨s, hs⟩ := Ideal.fg_of_isNoetherianRing J
  have hsJ : ∀ x ∈ s, x ∈ J := fun x hx => by
    rw [← hs]
    exact Submodule.subset_span hx
  refine ⟨q, ∏ x ∈ s, σ x, hqJ, ?_, ?_, ?_⟩
  · rw [map_prod]
    refine Finset.prod_ne_zero_iff.2 fun x hx h0 => ?_
    exact hσM x (hsJ x hx) (RingHom.mem_ker.2 h0)
  · rw [htq, htan]
  · intro r hr
    have hle : J ≤ Submodule.comap (LinearMap.mulLeft (MvPolynomial (Fin n) ℂ) (∏ x ∈ s, σ x))
        (Ideal.span (Set.range q)) := by
      rw [← hs]
      refine Submodule.span_le.2 fun x hx => ?_
      have hxJ := hsJ x hx
      show (∏ x ∈ s, σ x) * x ∈ Ideal.span (Set.range q)
      rw [← Finset.mul_prod_erase s σ hx,
        show σ x * (∏ y ∈ s.erase x, σ y) * x = (∏ y ∈ s.erase x, σ y) * (σ x * x) by ring]
      exact Ideal.mul_mem_left _ _ (hσ x hxJ)
    exact hle hr

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSectionOrderAlgClosed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem SectionOrderAlgClosed.proof (h₁ : IncIdealBelow.Statement) (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₃ : ChartChoiceAlgClosed.Statement) (h₄ : Vertical.SpecFirstNeField.Statement)
    (h₅ : LocalizationPrimeDVR.Statement) (h₆ : EmultiplicityOrd.Statement) (h₇ : ChartFinite.Statement)
    (h₈ : ChartLocDomain.Statement) (h₉ : ChartNormAlgClosed.Statement)
    (h₁₀ : ChartLengthAlgClosed.Statement) (h₁₁ : LengthQuotientDet.Statement) :
    SectionOrderAlgClosed.Statement := by
  intro F _ _ n e I f u hI hf hu
  have hne : specFirst f u ≠ 0 := h₄ F n e I f u hI hf hu
  refine ⟨hne, fun q hq => ?_⟩
  have hqp : Prime q := hq.prime
  obtain ⟨t, ht⟩ := h₃ F n e I f q hI hf hqp

  have htI : linForm t ∉ I := by
    intro h
    have hmem := h₂ F n e I I f t hf le_rfl h
    rw [h₁ F n e I f hI hf, Ideal.mem_bot] at hmem
    exact ht (hmem ▸ dvd_zero q)
  let p : Ideal (MvPolynomial (Fin e × Fin n) F) := Ideal.span {q}
  have hpp : p.IsPrime := (Ideal.span_singleton_prime hqp.ne_zero).mpr hqp
  have htp : specFirst f t ∉ p := by
    rw [Ideal.mem_span_singleton]
    exact ht
  have : IsDiscreteValuationRing (Localization.AtPrime p) := h₅ _ q p hqp rfl
  have hem := h₆ _ q (specFirst f u) p hqp rfl hne
  have : Module.Finite (Localization.AtPrime p) (ChartLoc I t e p) := h₇ F n e I f t p hI hf htp
  obtain ⟨_, hinj, -⟩ := h₈ F n e I f t p hI hf htI
  have : Module.IsTorsionFree (Localization.AtPrime p) (ChartLoc I t e p) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact hinj
  have : Module.Free (Localization.AtPrime p) (ChartLoc I t e p) :=
    Module.free_of_finite_type_torsion_free'
  have hnorm := h₉ F n e I f t p hI hf (Or.inr ⟨q, hqp, rfl⟩) htp u
  have hunit : IsUnit (algebraMap _ (Localization.AtPrime p) (specFirst f t)) :=
    IsLocalization.map_units (Localization.AtPrime p) (⟨specFirst f t, htp⟩ : p.primeCompl)
  have hinjO : Function.Injective
      (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) :=
    IsLocalization.injective _ p.primeCompl_le_nonZeroDivisors
  have hdet : LinearMap.det (LinearMap.mulLeft (Localization.AtPrime p)
      (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u))) ≠ 0 := by
    intro h0
    apply hne
    apply hinjO
    rw [hnorm, h0, mul_zero, map_zero]
  have hlen := h₁₁ (Localization.AtPrime p) (ChartLoc I t e p) _ hdet
  rw [hem, hnorm, Ring.ord_mul_of_isUnit_left hunit, ← hlen]
  exact h₁₀ F n e I f t u q p hI hf hu hqp rfl ht

end

end GroundTheory.Heights₂.Heights
end
