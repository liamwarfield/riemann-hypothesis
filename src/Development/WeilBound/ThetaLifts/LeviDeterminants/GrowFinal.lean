module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowDef
public import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowSplit
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionNonzeroAdmissible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.GrowInt
section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.ContinuousOfMem
section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.GrowLine
noncomputable section

namespace PositivityTheory.ThKF0.Grow

open scoped Matrix NNReal ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Line

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def lineFn (f : SchwartzMap V ℂ) (A : V) (L : V →L[ℝ] ℝ) (c : ℝ) (p : V) (t : ℝ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L p + t ^ 2 * c : ℝ) : ℂ)) * f (p + t • A)

def lineD (f : SchwartzMap V ℂ) (A : V) (L : V →L[ℝ] ℝ) (c : ℝ) (p : V) (t : ℝ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L p + t ^ 2 * c : ℝ) : ℂ)) *
    (-(2 * Real.pi * Complex.I) * ((L p + 2 * t * c : ℝ) : ℂ) * f (p + t • A) + fderiv ℝ f (p + t • A) A)

theorem hasDerivAt_lineFn (f : SchwartzMap V ℂ) (A : V) (L : V →L[ℝ] ℝ) (c : ℝ) (p : V) (t : ℝ) :
    HasDerivAt (lineFn f A L c p) (lineD f A L c p t) t := by
  have h1 : HasDerivAt (fun s : ℝ => s * L p + s ^ 2 * c) (L p + 2 * t * c) t := by
    have a1 : HasDerivAt (fun s : ℝ => s * L p) (L p) t := by simpa using (hasDerivAt_id t).mul_const (L p)
    have a2 : HasDerivAt (fun s : ℝ => s ^ 2 * c) (2 * t * c) t := by
      simpa using ((hasDerivAt_id t).pow 2).mul_const c
    exact a1.fun_add a2
  have h2 := ((h1.ofReal_comp).const_mul (-(2 * Real.pi * Complex.I))).cexp
  have h3 : HasDerivAt (fun s : ℝ => p + s • A) A t := by
    simpa using ((hasDerivAt_id t).smul_const A).const_add p
  have h4 : HasDerivAt (fun s : ℝ => f (p + s • A)) (fderiv ℝ f (p + t • A) A) t :=
    (f.hasFDerivAt (p + t • A)).comp_hasDerivAt t h3
  refine (h2.fun_mul h4).congr_deriv ?_
  simp only [lineD]
  push_cast
  ring

theorem lineD_bound (f : SchwartzMap V ℂ) (A A₀ : V) (L : V →L[ℝ] ℝ) (c : ℝ) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : V) (t : ℝ), |t| ≤ 1 → ‖lineD f A L c (m + A₀) t‖ ≤ K * ((1 + ‖m‖) ^ k)⁻¹ := by
  set C₀ : ℝ := 2 ^ (k + 1) * (Finset.Iic (k + 1, 1)).sup (schwartzSeminormFamily ℂ V ℂ) f
  have hC0 : 0 ≤ C₀ := by positivity
  have b0 : ∀ q, (1 + ‖q‖) ^ (k + 1) * ‖f q‖ ≤ C₀ := fun q => by
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k + 1, 1)) (k := k + 1) (n := 0) le_rfl (by simp) f q
    rwa [norm_iteratedFDeriv_zero] at h
  have b1 : ∀ q, (1 + ‖q‖) ^ k * ‖fderiv ℝ f q‖ ≤ C₀ := fun q => by
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k + 1, 1)) (k := k + 1) (n := 1) le_rfl le_rfl f q
    rw [norm_iteratedFDeriv_one] at h
    refine le_trans ?_ h
    have hS : (1 : ℝ) ≤ 1 + ‖q‖ := by linarith [norm_nonneg q]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hS (Nat.le_succ k)) (norm_nonneg _)
  set R : ℝ := ‖A₀‖ + ‖A‖ with hR
  have hR0 : 0 ≤ R := by positivity
  set B : ℝ := ‖L‖ * (1 + ‖A‖ + ‖A‖ ) + 2 * |c| with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨(2 * Real.pi * B * C₀ + ‖A‖ * C₀) * (1 + R) ^ k, by positivity, fun m t ht => ?_⟩
  set p := m + A₀ with hp
  set q := p + t • A with hq
  have htA : ‖t • A‖ ≤ ‖A‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) ht
  have hpq : ‖p‖ ≤ ‖q‖ + ‖A‖ := by
    have : p = q - t • A := by simp [hq]
    rw [this]
    exact (norm_sub_le _ _).trans (by gcongr)
  have hmq : ‖m‖ ≤ ‖q‖ + R := by
    have : m = q - t • A - A₀ := by simp [hq, hp]
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    have := norm_sub_le q (t • A)
    rw [hR]
    linarith
  set S : ℝ := 1 + ‖q‖ with hS
  have hS1 : 1 ≤ S := by rw [hS]; linarith [norm_nonneg q]
  have hS0 : 0 < S := by linarith
  have hSk : 0 < S ^ k := by positivity
  have hf : S * ‖f q‖ ≤ C₀ * (S ^ k)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hSk]
    have := b0 q
    calc S * ‖f q‖ * S ^ k = S ^ (k + 1) * ‖f q‖ := by ring
      _ ≤ C₀ := this
  have hdf : ‖fderiv ℝ f q‖ ≤ C₀ * (S ^ k)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hSk, mul_comm]
    exact b1 q
  have hLp : |L p + 2 * t * c| ≤ S * B := by
    have h1 : |L p| ≤ ‖L‖ * (‖q‖ + ‖A‖) :=
      (L.le_opNorm p).trans (mul_le_mul_of_nonneg_left hpq (norm_nonneg _))
    have h2 : |2 * t * c| ≤ 2 * |c| := by
      rw [abs_mul, abs_mul, abs_two]
      have := abs_nonneg c
      nlinarith
    have h3 : ‖q‖ + ‖A‖ ≤ S * (1 + ‖A‖ + ‖A‖) := by
      have hA := norm_nonneg A
      have hq0 := norm_nonneg q
      nlinarith
    calc |L p + 2 * t * c| ≤ |L p| + |2 * t * c| := abs_add_le _ _
      _ ≤ ‖L‖ * (S * (1 + ‖A‖ + ‖A‖)) + S * (2 * |c|) := by
          have := mul_le_mul_of_nonneg_left h3 (norm_nonneg L)
          have h4 : 2 * |c| ≤ S * (2 * |c|) := le_mul_of_one_le_left (by positivity) hS1
          linarith
      _ = S * B := by rw [hB]; ring
  have hnorm : ‖lineD f A L c p t‖ ≤ (2 * Real.pi * B * C₀ + ‖A‖ * C₀) * (S ^ k)⁻¹ := by
    have hexp : ‖Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L p + t ^ 2 * c : ℝ) : ℂ))‖ = 1 := by
      have : -(2 * Real.pi * Complex.I) * ((t * L p + t ^ 2 * c : ℝ) : ℂ) =
          ((-(2 * Real.pi) * (t * L p + t ^ 2 * c) : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    have hc : ‖-(2 * Real.pi * Complex.I)‖ = 2 * Real.pi := by
      simp [abs_of_pos Real.pi_pos]
    rw [lineD, norm_mul, hexp, one_mul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, hc, Complex.norm_real, Real.norm_eq_abs]
    have h1 : 2 * Real.pi * |L p + 2 * t * c| * ‖f q‖ ≤ 2 * Real.pi * B * (C₀ * (S ^ k)⁻¹) := by
      calc 2 * Real.pi * |L p + 2 * t * c| * ‖f q‖ ≤ 2 * Real.pi * (S * B) * ‖f q‖ := by gcongr
        _ = 2 * Real.pi * B * (S * ‖f q‖) := by ring
        _ ≤ _ := by gcongr
    have h2 : ‖(fderiv ℝ f q) A‖ ≤ ‖A‖ * (C₀ * (S ^ k)⁻¹) := by
      refine ((fderiv ℝ f q).le_opNorm A).trans ?_
      rw [mul_comm]
      gcongr
    calc _ ≤ 2 * Real.pi * B * (C₀ * (S ^ k)⁻¹) + ‖A‖ * (C₀ * (S ^ k)⁻¹) := add_le_add h1 h2
      _ = _ := by ring
  refine hnorm.trans ?_
  have hT : 1 + ‖m‖ ≤ S * (1 + R) := by
    rw [hS]
    nlinarith [norm_nonneg q]
  have hT0 : 0 < 1 + ‖m‖ := by linarith [norm_nonneg m]
  have hinv : (S ^ k)⁻¹ ≤ (1 + R) ^ k * ((1 + ‖m‖) ^ k)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ hSk, ← mul_pow]
    exact pow_le_pow_left₀ hT0.le hT k
  calc _ ≤ (2 * Real.pi * B * C₀ + ‖A‖ * C₀) * ((1 + R) ^ k * ((1 + ‖m‖) ^ k)⁻¹) := by gcongr
    _ = _ := by ring

end Line

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_zero : evI F 0 = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem evI_sum {ι : Type} (s : Finset ι) (g : ι → AF F) : evI F (∑ i ∈ s, g i) = ∑ i ∈ s, evI F (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using evI_zero
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, evI_add, ih]

theorem evI_realAd (t : ℝ) : evI F (realAd F t) = algebraMap ℝ (mixedEmbedding.mixedSpace F) t := by
  change (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _) = _
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

def linForm (B : κ → mixedEmbedding.mixedSpace F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (∑ i, (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)) ∘ₗ (LinearMap.mulRight ℝ (B i)) ∘ₗ
      (LinearMap.proj i : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] mixedEmbedding.mixedSpace F))

theorem linForm_apply (B y : κ → mixedEmbedding.mixedSpace F) :
    linForm B y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * B i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [linForm, map_sum, LinearMap.sum_apply]

theorem phase_line (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (a b x : κ → AF F) (hb : At (evI F) b) (t : ℝ) :
    ψ (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * linForm (fun i => evI F (b i)) (fun i => evI F (x i)) +
        t ^ 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F ⅟(2 : AF F) * ∑ i, evI F (a i) * evI F (b i)) : ℝ) : ℂ)) := by
  have hz : At (evI F) (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) := by
    intro s hs
    have hsb : ∀ i, s * b i = 0 := fun i => by simpa using congrFun (hb s hs) i
    have e1 : ∀ i, s * (x i * (realAd F t * b i)) = x i * realAd F t * (s * b i) := fun i => by ring
    have e2 : ∀ i, s * (⅟(2 : AF F) * (realAd F t * a i * (realAd F t * b i))) =
        ⅟(2 : AF F) * (realAd F t * a i * realAd F t) * (s * b i) := fun i => by ring
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum, e1, e2, hsb, mul_zero, Finset.sum_const_zero,
      add_zero]
  rw [hψ.2.2 _ hz]
  congr 3
  have ev : evI F (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) =
      t • (∑ i, evI F (x i) * evI F (b i)) + (t ^ 2) • (evI F ⅟(2 : AF F) * ∑ i, evI F (a i) * evI F (b i)) := by
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, evI_add, evI_mul, evI_sum, evI_realAd, Algebra.smul_def, map_pow,
      Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  rw [ev, map_add (f := _), map_smul, map_smul, linForm_apply]
  simp [smul_eq_mul]


omit [Fintype κ] in
theorem snd_eq_zero {z : κ → AF F} (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  let w : AF F := LinearMap.inr F (Ainf F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) 1
  have e0 : evI F w = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h : w * z i = 0 := congrFun (hz w e0) i
  have h2 : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) * (z i).2 = 0 := congrArg Prod.snd h
  simpa using h2


open scoped Classical in
theorem schr_line (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (a b : κ → AF F) (ha : At (evI F) a) (hb : At (evI F) b)
    (f : SInf F κ) (g : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ) (x : κ → AF F) (t : ℝ) :
    schr ψ (realAd F t • a, realAd F t • b) (pureA F f g) x =
      lineFn f (fun i => evI F (a i)) (linForm fun i => evI F (b i))
        (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F ⅟(2 : AF F) * ∑ i, evI F (a i) * evI F (b i)))
        (fun i => evI F (x i)) t * g (fun i => (x i).2) := by
  have hat : At (evI F) (realAd F t • a) := fun s hs => by
    rw [smul_comm, ha s hs, smul_zero]
  have e : (fun i => evI F ((x + realAd F t • a) i)) = (fun i => evI F (x i)) + t • fun i => evI F (a i) := by
    funext i
    simp [evI_add, evI_mul, evI_realAd, Algebra.smul_def]
  have e2 : (fun i => ((x + realAd F t • a) i).2) = fun i => (x i).2 := by
    funext i
    have h := snd_eq_zero hat i
    show (x i).2 + ((realAd F t • a) i).2 = (x i).2
    rw [h, add_zero]
  show ψ _ * (f (fun i => evI F ((x + realAd F t • a) i)) * g (fun i => ((x + realAd F t • a) i).2)) = _
  rw [phase_line ψ hψ a b x hb t, e, e2, lineFn]
  exact (mul_assoc _ _ _).symm

end PositivityTheory.ThKF0.Grow
end
end

noncomputable section

namespace PositivityTheory.ThKF0.Grow

open scoped Matrix NNReal ENNReal Classical SchwartzMap LineDeriv
open NumberField IsDedekindDomain MeasureTheory Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open PositivityTheory.ThKF0.Split

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem borelV : BorelSpace (V F κ) := by
  have : BorelSpace (mixedEmbedding.mixedSpace F) := inferInstance
  exact Pi.borelSpace

theorem continuous_of_mem {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : Continuous Φ := by
  have := (continuous_comp_splitE F κ Φ hΦ).comp (continuous_splitE_symm F κ)
  simpa only [Function.comp_def, AddEquiv.apply_symm_apply] using this

theorem nsq_pure_lt_top {μ : @Measure (κ → AF F) (borel _)} (hμ : IsHaar μ) {u : V F κ → ℂ} (hu : Continuous u)
    (hu2 : ∫⁻ z, ‖u z‖ₑ ^ 2 < ⊤) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) : nsq μ (pureA F u g) < ⊤ := by
  haveI := volume_isAddHaar F κ
  haveI : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  haveI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  letI mY : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  letI mA : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : SigmaCompactSpace (κ → FiniteAdeleRing (𝓞 F) F) := sigmaCompactSpace_of_locallyCompact_secondCountable
  set ν : Measure (κ → FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hν
  haveI : SFinite ν := inferInstance
  haveI : MeasurableAdd (κ → mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  haveI : MeasurableAdd (κ → FiniteAdeleRing (𝓞 F) F) := ContinuousAdd.measurableAdd
  haveI : ν.IsAddHaarMeasure := by rw [hν]; infer_instance
  haveI : ((volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (κ → mixedEmbedding.mixedSpace F)) ν
  haveI hμH : Measure.IsAddHaarMeasure ((volume.prod ν).map (splitE F κ)) :=
    (splitE F κ).isAddHaarMeasure_map _ (continuous_splitE F κ) (continuous_splitE_symm F κ)
  let eh := Homeomorph.mk (splitE F κ).toEquiv (continuous_splitE F κ) (continuous_splitE_symm F κ)
  haveI : SecondCountableTopology (κ → AdeleRing (𝓞 F) F) := eh.symm.secondCountableTopology
  have hint : ∀ h : (κ → AdeleRing (𝓞 F) F) → ℝ≥0∞,
      ∫⁻ x, h x ∂((volume.prod ν).map (splitE F κ)) = ∫⁻ p, h (splitE F κ p) ∂(volume.prod ν) :=
    fun h => lintegral_map_equiv h eh.toMeasurableEquiv
  have hgc : Continuous g := hg.1.continuous
  have hC : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν < ⊤ := by
    have h1 : ∫⁻ y, ‖g y * g y‖ₑ ∂ν < ⊤ :=
      ((hgc.mul hgc).integrable_of_hasCompactSupport (hg.2.mul_left (f := g))).2
    refine (lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_)) h1)
    rw [enorm_mul, sq]
  haveI : μ.IsAddHaarMeasure := hμ
  rw [nsq, Measure.isAddLeftInvariant_eq_smul μ ((volume.prod ν).map (splitE F κ)), lintegral_smul_measure, hint]
  have e1 : ∀ p, ‖pureA F u g (splitE F κ p)‖ₑ ^ 2 = ‖u p.1‖ₑ ^ 2 * ‖g p.2‖ₑ ^ 2 := by
    intro p
    rw [pureA_splitE, enorm_mul, mul_pow]
  simp_rw [e1]
  rw [lintegral_prod_mul (hu.measurable.enorm.pow_const 2).aemeasurable
    (hgc.measurable.enorm.pow_const 2).aemeasurable]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top hu2 hC)

theorem enorm_add_sq_le (a b : ℂ) : ‖a + b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  simp only [enorm_eq_nnnorm]
  have : ‖a + b‖₊ ^ 2 ≤ 2 * ‖a‖₊ ^ 2 + 2 * ‖b‖₊ ^ 2 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    have h := norm_add_le a b
    have h0 := norm_nonneg (a + b)
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  exact_mod_cast this

omit [Fintype κ] in
theorem nsq_add_le (μ : @Measure (κ → AF F) (borel _)) {Φ : (κ → AF F) → ℂ} (hΦ : Continuous Φ) (Ψ : (κ → AF F) → ℂ) :
    nsq μ (Φ + Ψ) ≤ 2 * nsq μ Φ + 2 * nsq μ Ψ := by
  letI mA : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  unfold nsq
  rw [← lintegral_const_mul' _ _ (by simp), ← lintegral_const_mul' _ _ (by simp),
    ← lintegral_add_left ((hΦ.measurable.enorm.pow_const 2).const_mul 2)]
  exact lintegral_mono fun x => enorm_add_sq_le _ _

omit [Fintype κ] in
theorem nsq_smul (μ : @Measure (κ → AF F) (borel _)) (c : ℂ) (Φ : (κ → AF F) → ℂ) :
    nsq μ (c • Φ) = ‖c‖ₑ ^ 2 * nsq μ Φ := by
  unfold nsq
  rw [← lintegral_const_mul' _ _ (by simp [enorm_eq_nnnorm])]
  simp only [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow]

theorem nsq_lt_top {μ : @Measure (κ → AF F) (borel _)} (hμ : IsHaar μ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    nsq μ Φ < ⊤ := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    haveI := volume_isAddHaar F κ
    haveI := borelV (F := F) (κ := κ)
    refine nsq_pure_lt_top hμ f.continuous ?_ hg
    have := f.memLp 2 (volume : Measure (V F κ))
    have h2 := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by simp) (by simp) this
    simpa using h2
  | zero => simp [nsq]
  | add x x' hx _ h h' =>
    exact (nsq_add_le μ (continuous_of_mem hx) x').trans_lt
      (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) h, ENNReal.mul_lt_top (by simp) h'⟩)
  | smul a x _ h => rw [nsq_smul]; exact ENNReal.mul_lt_top (by simp [enorm_eq_nnnorm]) h

theorem weight_lt_top : ∃ k : ℕ, ∀ K : ℝ, ∫⁻ z : V F κ, ‖((K * ((1 + ‖z‖) ^ k)⁻¹ : ℝ) : ℂ)‖ₑ ^ 2 < ⊤ := by
  haveI := volume_isAddHaar F κ
  haveI := borelV (F := F) (κ := κ)
  refine ⟨Module.finrank ℝ (V F κ) + 1, fun K => ?_⟩
  have h := (integrable_one_add_norm (E := V F κ) (μ := volume) (r := ((2 * (Module.finrank ℝ (V F κ) + 1) : ℕ) : ℝ))
    (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ (V F κ))])).const_mul (K ^ 2)
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun z => ?_)) h.2
  beta_reduce
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← enorm_pow, ← Complex.ofReal_pow, ← ofReal_norm_eq_enorm,
    ← ofReal_norm_eq_enorm, Complex.norm_real, mul_pow, inv_pow, ← pow_mul, mul_comm _ 2]

omit [Fintype κ] in
theorem evI_inf (a : mixedEmbedding.mixedSpace F) : evI F (inf a) = a := RingEquiv.apply_symm_apply _ _

theorem inf_smul (t : ℝ) (a : mixedEmbedding.mixedSpace F) : inf (t • a) = realAd F t * inf a := by
  refine Prod.ext ?_ ?_
  · change _ = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t) *
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a
    rw [← map_mul, ← Algebra.smul_def]; rfl
  · change (0 : Af F) = 0 * 0
    rw [mul_zero]

omit [Fintype κ] in
theorem emb_smul (t : ℝ) (w : V F κ × V F κ) : emb (t • w) = realAd F t • emb w :=
  Prod.ext (funext fun i => inf_smul t (w.1 i)) (funext fun i => inf_smul t (w.2 i))

omit [Fintype κ] in
theorem at_inf (a : V F κ) : At (evI F) (fun i => inf (a i)) := fun u hu => funext fun i => by
  have h : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h, zero_mul]
  · change u.2 * 0 = 0
    rw [mul_zero]

def qc (w : V F κ × V F κ) : ℝ :=
  Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F ⅟(2 : AF F) * ∑ i, w.1 i * w.2 i)

theorem schr_emb {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : V F κ × V F κ) (f : SInf F κ) (g : (κ → Af F) → ℂ)
    (x : κ → AF F) (t : ℝ) : schr ψ (emb (t • w)) (pureA F f g) x =
      lineFn f w.1 (linForm w.2) (qc w) (fun i => evI F (x i)) t * g (fun i => (x i).2) := by
  have := schr_line ψ hψ _ _ (at_inf w.1) (at_inf w.2) f g x t
  simp only [evI_inf] at this
  rw [emb_smul]
  exact this

def dS (w : V F κ × V F κ) (f : SInf F κ) : SInf F κ :=
  ∂_{w.1} f + (-(2 * Real.pi * Complex.I)) • SchwartzMap.smulLeftCLM ℂ (linForm w.2) f

theorem dS_apply (w : V F κ × V F κ) (f : SInf F κ) (p : V F κ) :
    dS w f p = fderiv ℝ f p w.1 + -(2 * Real.pi * Complex.I) * ((linForm w.2 p : ℝ) * f p) := by
  simp [dS, SchwartzMap.smulLeftCLM_apply_apply (linForm w.2).hasTemperateGrowth, SchwartzMap.lineDerivOp_apply_eq_fderiv]

theorem hasDerivAt_pure {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : V F κ × V F κ) (f : SInf F κ) (g : (κ → Af F) → ℂ)
    (x : κ → AF F) : HasDerivAt (fun t : ℝ => schr ψ (emb (t • w)) (pureA F f g) x) (pureA F (dS w f) g x) 0 := by
  simp only [schr_emb hψ]
  refine ((hasDerivAt_lineFn f w.1 (linForm w.2) (qc w) (fun i => evI F (x i)) 0).mul_const _).congr_deriv ?_
  change _ = dS w f (fun i => evI F (x i)) * _
  rw [dS_apply, lineD]
  simp
  left; ring

theorem dR_pure {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : V F κ × V F κ) (f : SInf F κ) (g : (κ → Af F) → ℂ) :
    dR ψ w (pureA F f g) = pureA F (dS w f) g := funext fun x => (hasDerivAt_pure hψ w f g x).deriv

theorem schr_add (ψ : AddChar (AF F) ℂ) (w : Pt F κ) (Φ Ψ : (κ → AF F) → ℂ) :
    schr ψ w (Φ + Ψ) = schr ψ w Φ + schr ψ w Ψ := by funext x; simp [schr, mul_add]

theorem schr_smul (ψ : AddChar (AF F) ℂ) (w : Pt F κ) (c : ℂ) (Φ : (κ → AF F) → ℂ) :
    schr ψ w (c • Φ) = c • schr ψ w Φ := by funext x; simp [schr, mul_left_comm]

theorem exists_deriv {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : V F κ × V F κ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    ∃ Φ' ∈ schA F κ, ∀ x, HasDerivAt (fun t : ℝ => schr ψ (emb (t • w)) Φ x) (Φ' x) 0 := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    exact ⟨_, Submodule.subset_span ⟨dS w f, g, hg, rfl⟩, hasDerivAt_pure hψ w f g⟩
  | zero => exact ⟨0, zero_mem _, fun x => by simpa [schr] using hasDerivAt_const (0 : ℝ) (0 : ℂ)⟩
  | add a b _ _ h h' =>
    obtain ⟨a', ha, h⟩ := h
    obtain ⟨b', hb, h'⟩ := h'
    exact ⟨a' + b', add_mem ha hb, fun x => by simp only [schr_add]; exact (h x).fun_add (h' x)⟩
  | smul c a _ h =>
    obtain ⟨a', ha, h⟩ := h
    exact ⟨c • a', Submodule.smul_mem _ c ha, fun x => by simp only [schr_smul]; exact (h x).const_mul c⟩

theorem hasDerivAt_dR {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : V F κ × V F κ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ)
    (x : κ → AF F) : HasDerivAt (fun t : ℝ => schr ψ (emb (t • w)) Φ x) (dR ψ w Φ x) 0 := by
  obtain ⟨_, _, h⟩ := exists_deriv hψ w hΦ
  exact (h x).differentiableAt.hasDerivAt

theorem dR_mem {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : V F κ × V F κ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    dR ψ w Φ ∈ schA F κ := by
  obtain ⟨Φ', h1, h⟩ := exists_deriv hψ w hΦ
  rwa [show dR ψ w Φ = Φ' from funext fun x => (h x).deriv]

theorem derivOK : DerivOK := by
  intro F _ _ κ _ ψ hψ w Φ hΦ
  refine ⟨dR_mem hψ w hΦ, hasDerivAt_dR hψ w hΦ, fun m hm u hu x => ?_⟩
  unfold dR
  congr 1
  funext t
  have e : ((m : AF F) • u) ⬝ᵥ (emb (t • w)).2 = 0 := Finset.sum_eq_zero fun i _ => Prod.ext (by
    change ((m : AF F).1 * (u i).1) * _ = 0
    rw [(hu i).1, mul_zero, zero_mul]) (by
    change _ * (0 : Af F) = 0
    rw [mul_zero])
  simp only [schr]
  rw [add_dotProduct, e, add_zero, add_right_comm, hm u hu]

end PositivityTheory.ThKF0.Grow
end
end

noncomputable section

namespace PositivityTheory.ThKF0.Grow

open scoped Matrix NNReal ENNReal Classical SchwartzMap LineDeriv
open NumberField IsDedekindDomain MeasureTheory Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}

omit [Fintype κ] in
theorem exists_major {μ : @Measure (κ → AF F) (borel _)} {G₁ G₂ : (κ → AF F) → ℂ} (h₁ : Continuous G₁) (h₂ : Continuous G₂)
    (f₁ : nsq μ G₁ < ⊤) (f₂ : nsq μ G₂ < ⊤) :
    ∃ G : (κ → AF F) → ℂ, Continuous G ∧ nsq μ G < ⊤ ∧ ∀ x, ‖G₁ x‖ + ‖G₂ x‖ ≤ ‖G x‖ := by
  have c₁ : Continuous fun x => ((‖G₁ x‖ : ℝ) : ℂ) := Complex.continuous_ofReal.comp h₁.norm
  have c₂ : Continuous fun x => ((‖G₂ x‖ : ℝ) : ℂ) := Complex.continuous_ofReal.comp h₂.norm
  have e : ∀ G : (κ → AF F) → ℂ, nsq μ (fun x => ((‖G x‖ : ℝ) : ℂ)) = nsq μ G := fun G => by
    unfold nsq
    simp only [← ofReal_norm_eq_enorm, Complex.norm_real, norm_norm]
  refine ⟨(fun x => ((‖G₁ x‖ : ℝ) : ℂ)) + fun x => ((‖G₂ x‖ : ℝ) : ℂ), c₁.add c₂, (nsq_add_le μ c₁ _).trans_lt ?_, fun x => ?_⟩
  · rw [e, e]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) f₁, ENNReal.mul_lt_top (by simp) f₂⟩
  · rw [Pi.add_apply, ← Complex.ofReal_add, Complex.norm_real]
    exact le_abs_self _

omit [Fintype κ] in
theorem emb_zero : emb (0 : V F κ × V F κ) = 0 := by
  have : inf (0 : mixedEmbedding.mixedSpace F) = 0 := Prod.ext (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm) rfl
  exact Prod.ext (funext fun _ => this) (funext fun _ => this)

theorem schr_zero (Φ : (κ → AF F) → ℂ) (w : V F κ × V F κ) : schr ψ (emb ((0 : ℝ) • w)) Φ = Φ := by
  funext x; simp [emb_zero, schr]

theorem exists_dom (hψ : IsStd ψ) {μ : @Measure (κ → AF F) (borel _)} (hμ : IsHaar μ) (w : V F κ × V F κ)
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : ∃ G : (κ → AF F) → ℂ, Continuous G ∧ nsq μ G < ⊤ ∧
      ∀ t : ℝ, |t| ≤ 1 → ∀ x, ‖schr ψ (emb (t • w)) Φ x - Φ x‖ ≤ |t| * ‖G x‖ := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    obtain ⟨k, hk⟩ := weight_lt_top (F := F) (κ := κ)
    obtain ⟨K, hK0, hK⟩ := lineD_bound f w.1 0 (linForm w.2) (qc w) k
    have hu : Continuous fun z : V F κ => ((K * ((1 + ‖z‖) ^ k)⁻¹ : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_const.mul (Continuous.fun_inv₀ (by fun_prop) fun z => by positivity))
    refine ⟨pureA F (fun z => ((K * ((1 + ‖z‖) ^ k)⁻¹ : ℝ) : ℂ)) g, ?_, nsq_pure_lt_top hμ hu (hk K) hg, fun t ht x => ?_⟩
    · have h := PositivityTheory.ThKF0.Split.continuous_splitE_symm F κ
      exact (hu.comp h.fst).mul (hg.1.continuous.comp h.snd)
    · have e := congrFun (schr_zero (ψ := ψ) (pureA F f g) w) x
      rw [← e, schr_emb hψ, schr_emb hψ, ← sub_mul, norm_mul, pureA, norm_mul, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := lineFn f w.1 (linForm w.2) (qc w) fun i => evI F (x i))
        (fun s _ => (hasDerivAt_lineFn f w.1 (linForm w.2) (qc w) _ s).hasDerivWithinAt)
        (fun s hs => by simpa only [add_zero] using hK (fun i => evI F (x i)) s (abs_le.2 hs))
        (x := 0) (y := t) ⟨by norm_num, by norm_num⟩ (abs_le.1 ht)
      rw [sub_zero, Real.norm_eq_abs, mul_comm] at this
      refine this.trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
      rw [Complex.norm_real]
      exact le_abs_self _
  | zero => exact ⟨0, continuous_const, by simp [nsq], fun t _ x => by simp [schr]⟩
  | add a b _ _ h h' =>
    obtain ⟨G₁, c₁, f₁, h⟩ := h
    obtain ⟨G₂, c₂, f₂, h'⟩ := h'
    obtain ⟨G, c, f, hG⟩ := exists_major c₁ c₂ f₁ f₂
    refine ⟨G, c, f, fun t ht x => ?_⟩
    rw [schr_add, Pi.add_apply, Pi.add_apply, add_sub_add_comm]
    refine (norm_add_le _ _).trans ((add_le_add (h t ht x) (h' t ht x)).trans ?_)
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (hG x) (abs_nonneg _)
  | smul c a _ h =>
    obtain ⟨G, c₁, f₁, h⟩ := h
    refine ⟨c • G, c₁.const_smul c, by rw [nsq_smul]; exact ENNReal.mul_lt_top (by simp [enorm_eq_nnnorm]) f₁,
      fun t ht x => ?_⟩
    rw [schr_smul, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, ← smul_sub, norm_smul, norm_smul, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (h t ht x) (norm_nonneg _)

theorem slope_tendsto {φ : ℝ → ℂ} {d : ℂ} (h : HasDerivAt φ d 0) :
    Tendsto (fun n : ℕ => ((n : ℂ) + 1) * (φ (1 / ((n : ℝ) + 1)) - φ 0)) atTop (𝓝 d) := by
  have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall fun n => Set.mem_Ioi.2 Nat.one_div_pos_of_nat⟩
  refine (h.tendsto_slope_zero_right.comp h1).congr fun n => ?_
  simp

theorem schr_mem (hψ : IsStd ψ) (w : Pt F κ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : schr ψ w Φ ∈ schA F κ := by
  obtain ⟨v⟩ : Nonempty (Pl F) := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
    exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField F)⟩⟩
  exact (GlobalTheory.CompanionTheory.AdelicHeis.schr_mem_and_thetaSum F κ ψ hψ.1
    (fun h => GlobalTheory.PsiNontriv.psiV_ne_one ψ hψ v (by rw [h]; rfl)) hψ.2.1).1 _ _ hΦ

theorem Impl.dR (hψ : IsStd ψ) {μ : @Measure (κ → AF F) (borel _)} (hμ : IsHaar μ) {T : Module.End ℂ ((κ → AF F) → ℂ)}
    {s : Pt F κ →ₗ[AF F] Pt F κ} (hT : Impl ψ T s) {w w' : V F κ × V F κ} (hw : s (emb w) = emb w')
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : T (dR ψ w' Φ) = dR ψ w (T Φ) := by
  letI mA : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : μ.IsAddHaarMeasure := hμ
  let q : ℕ → (κ → AF F) → ℂ := fun n =>
    ((n : ℂ) + 1) • (schr ψ (emb ((1 / ((n : ℝ) + 1)) • w')) Φ - Φ) - Grow.dR ψ w' Φ
  have hq : ∀ n, q n ∈ schA F κ := fun n =>
    sub_mem (Submodule.smul_mem _ _ (sub_mem (schr_mem hψ _ hΦ) hΦ)) (dR_mem hψ w' hΦ)
  have meas : ∀ Θ ∈ schA F κ, Measurable fun x => ‖Θ x‖ₑ ^ 2 := fun Θ h =>
    (continuous_of_mem h).measurable.enorm.pow_const 2
  obtain ⟨G₁, c₁, f₁, h₁⟩ := exists_dom hψ hμ w' hΦ
  obtain ⟨G, -, f, hG⟩ := exists_major c₁ (continuous_of_mem (dR_mem hψ w' hΦ)) f₁ (nsq_lt_top hμ (dR_mem hψ w' hΦ))
  have lim : ∀ {u : ℕ → ℂ} {a : ℂ}, Tendsto u atTop (𝓝 a) → Tendsto (fun n => ‖u n‖ₑ ^ 2) atTop (𝓝 (‖a‖ₑ ^ 2)) :=
    fun h => ((ENNReal.continuous_pow 2).tendsto _).comp h.enorm
  have t0 : Tendsto (fun n => nsq μ (q n)) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := μ) (F := fun n x => ‖q n x‖ₑ ^ 2) (f := fun _ => 0)
      (fun x => ‖G x‖ₑ ^ 2) (fun n => meas _ (hq n)) (fun n => Eventually.of_forall fun x => ?_) f.ne
      (Eventually.of_forall fun x => ?_)
    · rw [lintegral_zero] at this
      exact this
    · refine pow_le_pow_left' (enorm_le_iff_norm_le.2 ((norm_sub_le _ _).trans (le_trans ?_ (hG x)))) 2
      have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h1 := h₁ (1 / ((n : ℝ) + 1)) (by
        rw [abs_of_pos (by positivity), div_le_one hp]; linarith [Nat.cast_nonneg (α := ℝ) n]) x
      rw [abs_of_pos (by positivity), one_div ((n : ℝ) + 1), inv_mul_eq_div, le_div_iff₀ hp, mul_comm, ← one_div] at h1
      refine add_le_add_left (le_trans (le_of_eq ?_) h1) _
      rw [Pi.smul_apply, norm_smul, Pi.sub_apply]
      congr 1
      rw [← Nat.cast_succ, Complex.norm_natCast, Nat.cast_succ]
    · have h := (slope_tendsto (hasDerivAt_dR hψ w' hΦ x)).sub_const (Grow.dR ψ w' Φ x)
      rw [sub_self, schr_zero] at h
      have h2 := lim h
      rw [enorm_zero, zero_pow two_ne_zero] at h2
      exact h2
  have hD : Grow.dR ψ w (T Φ) - T (Grow.dR ψ w' Φ) ∈ schA F κ :=
    sub_mem (dR_mem hψ w (hT.pres _ hΦ)) (hT.pres _ (dR_mem hψ w' hΦ))
  have t1 : ∀ x, Tendsto (fun n => T (q n) x) atTop (𝓝 ((Grow.dR ψ w (T Φ) - T (Grow.dR ψ w' Φ)) x)) := fun x => by
    have h := (slope_tendsto (hasDerivAt_dR hψ w (hT.pres _ hΦ) x)).sub_const (T (Grow.dR ψ w' Φ) x)
    rw [schr_zero] at h
    refine h.congr fun n => ?_
    have e : emb ((1 / ((n : ℝ) + 1)) • w') = s (emb ((1 / ((n : ℝ) + 1)) • w)) := by
      rw [emb_smul, emb_smul, map_smul, hw]
    simp only [q, map_sub, map_smul, e, hT.impl _ _ hΦ]
    rfl
  have t2 : nsq μ (Grow.dR ψ w (T Φ) - T (Grow.dR ψ w' Φ)) = 0 := by
    have h : ∫⁻ x, liminf (fun n => ‖T (q n) x‖ₑ ^ 2) atTop ∂μ ≤ liminf (fun n => ∫⁻ x, ‖T (q n) x‖ₑ ^ 2 ∂μ) atTop :=
      lintegral_liminf_le fun n => meas _ (hT.pres _ (hq n))
    simp only [fun x => (lim (t1 x)).liminf_eq] at h
    have e : (fun n => ∫⁻ x, ‖T (q n) x‖ₑ ^ 2 ∂μ) = fun n => nsq μ (q n) := funext fun n => hT.unit μ hμ _ (hq n)
    rw [e, t0.liminf_eq] at h
    exact le_antisymm h zero_le
  have t3 := (lintegral_eq_zero_iff (meas _ hD)).1 t2
  have t4 : (Grow.dR ψ w (T Φ) - T (Grow.dR ψ w' Φ)) =ᵐ[μ] 0 := t3.mono fun x hx => by simpa using hx
  exact (sub_eq_zero.1 (((continuous_of_mem hD).ae_eq_iff_eq μ continuous_const).1 t4)).symm

theorem dR_add (hψ : IsStd ψ) (w : V F κ × V F κ) {Φ Ψ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (hΨ : Ψ ∈ schA F κ) :
    dR ψ w (Φ + Ψ) = dR ψ w Φ + dR ψ w Ψ := funext fun x => by
  have := (hasDerivAt_dR hψ w hΦ x).fun_add (hasDerivAt_dR hψ w hΨ x)
  simp only [dR, schr_add] at this ⊢
  exact this.deriv

theorem dR_smul (hψ : IsStd ψ) (w : V F κ × V F κ) (c : ℂ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    dR ψ w (c • Φ) = c • dR ψ w Φ := funext fun x => by
  have := (hasDerivAt_dR hψ w hΦ x).const_mul c
  simp only [dR, schr_smul] at this ⊢
  exact this.deriv

theorem word_mem (hψ : IsStd ψ) (l : List (V F κ × V F κ)) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    word ψ l Φ ∈ schA F κ := by
  induction l with
  | nil => exact hΦ
  | cons w l ih => exact dR_mem hψ w ih

def wordL (hψ : IsStd ψ) (l : List (V F κ × V F κ)) : schA F κ →ₗ[ℂ] (κ → AF F) → ℂ where
  toFun Φ := word ψ l Φ
  map_add' Φ Ψ := by
    induction l with
    | nil => rfl
    | cons w l ih => exact (congrArg (dR ψ w) ih).trans (dR_add hψ w (word_mem hψ l Φ.2) (word_mem hψ l Ψ.2))
  map_smul' c Φ := by
    induction l with
    | nil => rfl
    | cons w l ih => exact (congrArg (dR ψ w) ih).trans (dR_smul hψ w c (word_mem hψ l Φ.2))

theorem linForm_sum {ι : Type} [Fintype ι] (a : ι → ℝ) (b : ι → V F κ) (p : V F κ) :
    linForm (∑ j, a j • b j) p = ∑ j, a j * linForm (b j) p := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [linForm_apply, Finset.sum_apply, Pi.smul_apply, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_comm

theorem dR_sum (hψ : IsStd ψ) {ι : Type} [Fintype ι] (a : ι → ℝ) (b : ι → V F κ × V F κ) {Φ : (κ → AF F) → ℂ}
    (hΦ : Φ ∈ schA F κ) : dR ψ (∑ j, a j • b j) Φ = ∑ j, (a j : ℂ) • dR ψ (b j) Φ := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    funext x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dR_pure hψ, Finset.sum_apply, Pi.smul_apply, pureA, dS_apply, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst,
      Prod.smul_snd, linForm_sum, map_sum, map_smul, smul_eq_mul, Complex.real_smul, Complex.ofReal_sum, Complex.ofReal_mul,
      Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  | zero =>
    have : ∀ w : V F κ × V F κ, dR ψ w 0 = 0 := fun w => by
      have := dR_smul hψ w 0 (zero_mem (schA F κ))
      rwa [zero_smul, zero_smul] at this
    simp [this]
  | add x y hx hy h h' => simp only [dR_add hψ _ hx hy, h, h', smul_add, Finset.sum_add_distrib]
  | smul c x hx h => simp only [dR_smul hψ _ c hx, h, Finset.smul_sum, smul_comm c]

omit [Fintype κ] in
theorem nsq_sum_le (μ : @Measure (κ → AF F) (borel _)) {ι : Type} (s : Finset ι) (Θ : ι → (κ → AF F) → ℂ)
    (h : ∀ j, Continuous (Θ j)) : nsq μ (∑ j ∈ s, Θ j) ≤ 2 ^ s.card * ∑ j ∈ s, nsq μ (Θ j) := by
  induction s using Finset.induction_on with
  | empty => simp [nsq]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.card_insert_of_notMem hj, pow_succ', mul_add, mul_assoc, mul_assoc]
    refine (nsq_add_le μ (h j) _).trans (add_le_add (mul_le_mul' le_rfl ?_) (mul_le_mul' le_rfl ih))
    exact le_mul_of_one_le_left' (one_le_pow₀ one_le_two)

theorem word_bound (hψ : IsStd ψ) {μ : @Measure (κ → AF F) (borel _)} (hμ : IsHaar μ) (n : ℕ) :
    ∀ Φ ∈ schA F κ, ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ l : List (V F κ × V F κ), l.length = n → ∀ c : ℝ≥0, (∀ w ∈ l, ‖w‖ ≤ c) →
      nsq μ (word ψ l Φ) ≤ C * (c : ℝ≥0∞) ^ (2 * n) := by
  induction n with
  | zero =>
    intro Φ hΦ
    refine ⟨nsq μ Φ, (nsq_lt_top hμ hΦ).ne, fun l hl c _ => ?_⟩
    rw [List.length_eq_zero_iff.1 hl]
    simp [word]
  | succ n ih =>
    intro Φ hΦ
    let b := Module.finBasis ℝ (V F κ × V F κ)
    choose C hC hC' using fun j => ih _ (dR_mem hψ (b j) hΦ)
    let K : _ → ℝ≥0 := fun j => ‖LinearMap.toContinuousLinearMap (b.coord j)‖₊
    refine ⟨2 ^ (Finset.univ : Finset (Fin (Module.finrank ℝ (V F κ × V F κ)))).card * ∑ j, (K j : ℝ≥0∞) ^ 2 * C j,
      ENNReal.mul_ne_top (by simp) (ENNReal.sum_ne_top.2 fun j _ => ENNReal.mul_ne_top (by simp) (hC j)), fun l hl c hc => ?_⟩
    obtain rfl | ⟨l', w, rfl⟩ := List.eq_nil_or_concat l
    · simp at hl
    have e : word ψ (l'.concat w) Φ = ∑ j, (b.repr w j : ℂ) • word ψ l' (dR ψ (b j) Φ) := by
      have e1 : word ψ (l'.concat w) Φ = wordL hψ l' ⟨dR ψ w Φ, dR_mem hψ w hΦ⟩ := by
        simp [word, wordL]
      have e2 : (⟨dR ψ w Φ, dR_mem hψ w hΦ⟩ : schA F κ) = ∑ j, (b.repr w j : ℂ) • ⟨dR ψ (b j) Φ, dR_mem hψ _ hΦ⟩ := by
        apply Subtype.ext
        have := dR_sum hψ (b.repr w) b hΦ
        rw [b.sum_repr] at this
        simpa using this
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e1, e2, map_sum]
      simp only [map_smul]
      rfl
    rw [e, mul_assoc, Finset.sum_mul]
    refine (nsq_sum_le μ _ _ fun j => (continuous_of_mem (word_mem hψ l' (dR_mem hψ _ hΦ))).const_smul _).trans
      (mul_le_mul' le_rfl (Finset.sum_le_sum fun j _ => ?_))
    have h1 := hC' j l' (by simpa using hl) c fun u hu => hc u (by simp [hu])
    have h2 : ‖(b.repr w j : ℂ)‖ₑ ≤ K j * c := by
      rw [enorm_eq_nnnorm, ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, Complex.norm_real]
      exact ((LinearMap.toContinuousLinearMap (b.coord j)).le_opNorm w).trans
        (mul_le_mul_of_nonneg_left (hc w (by simp)) (norm_nonneg _))
    rw [nsq_smul]
    refine (mul_le_mul' (pow_le_pow_left' h2 2) h1).trans (le_of_eq ?_)
    ring

theorem Impl.word (hψ : IsStd ψ) {μ : @Measure (κ → AF F) (borel _)} (hμ : IsHaar μ) {T : Module.End ℂ ((κ → AF F) → ℂ)}
    {s : Pt F κ →ₗ[AF F] Pt F κ} (hT : Impl ψ T s) {d : ℕ} {c : ℝ} (hc : 0 ≤ c) (hs : Bd s d c) {Φ : (κ → AF F) → ℂ}
    (hΦ : Φ ∈ schA F κ) (R : ℝ) (l : List (V F κ × V F κ)) (hl : ∀ w ∈ l, ‖w‖ ≤ R) :
    ∃ l' : List (V F κ × V F κ), l'.length = l.length ∧ (∀ w ∈ l', ‖w‖ ≤ c * R) ∧ T (word ψ l' Φ) = word ψ l (T Φ) := by
  induction l with
  | nil => exact ⟨[], rfl, by simp, rfl⟩
  | cons w l ih =>
    obtain ⟨l', h1, h2, h3⟩ := ih fun u hu => hl u (List.mem_cons_of_mem _ hu)
    obtain ⟨w', h4, h5⟩ := hs.inf w
    refine ⟨w' :: l', by simp [h1], fun u hu => ?_, ?_⟩
    · rcases List.mem_cons.1 hu with rfl | hu
      · exact h5.trans (mul_le_mul_of_nonneg_left (hl w List.mem_cons_self) hc)
      · exact h2 u hu
    · exact (hT.dR hψ hμ h4 (word_mem hψ l' hΦ)).trans (congrArg (Grow.dR ψ w) h3)

end PositivityTheory.ThKF0.Grow
end
end

noncomputable section

namespace PositivityTheory.ThKF0.Grow

open scoped Matrix NNReal ENNReal Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}

theorem dR_mult (hψ : IsStd ψ) (b : V F κ) (Θ : (κ → AF F) → ℂ) (x : κ → AF F) :
    dR ψ (0, b) Θ x = -(2 * Real.pi * Complex.I) * (linForm b fun i => evI F (x i) : ℝ) * Θ x := by
  have e : ∀ t : ℝ, schr ψ (emb (t • ((0, b) : V F κ × V F κ))) Θ x =
      Complex.exp (-(2 * Real.pi * Complex.I) * (linForm b fun i => evI F (x i) : ℝ) * t) * Θ x := fun t => by
    have h0 : (emb ((0, b) : V F κ × V F κ)).1 = 0 := congrArg Prod.fst (emb_zero (F := F) (κ := κ))
    have := phase_line ψ hψ 0 _ x (at_inf b) t
    simp only [evI_inf, Pi.zero_apply, evI_zero, zero_mul, Finset.sum_const_zero, mul_zero, map_zero, add_zero] at this
    rw [emb_smul, schr, Prod.smul_fst, Prod.smul_snd, h0]
    change ψ (x ⬝ᵥ (realAd F t • fun i => inf (b i)) + _ * (_ ⬝ᵥ (realAd F t • fun i => inf (b i)))) * _ = _
    rw [this, smul_zero, add_zero]
    push_cast
    ring_nf
  simp only [dR, e]
  have := ((((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul
    (-(2 * Real.pi * Complex.I) * (linForm b fun i => evI F (x i) : ℝ))).cexp).mul_const (Θ x)
  simpa using this.deriv

theorem word_mult (hψ : IsStd ψ) (b : V F κ) (j : ℕ) (Θ : (κ → AF F) → ℂ) (x : κ → AF F) :
    word ψ (List.replicate j (0, b)) Θ x = (-(2 * Real.pi * Complex.I) * (linForm b fun i => evI F (x i) : ℝ)) ^ j * Θ x := by
  induction j with
  | zero => simp [word]
  | succ j ih =>
    change dR ψ (0, b) (word ψ (List.replicate j (0, b)) Θ) x = _
    rw [dR_mult hψ, ih, pow_succ', mul_assoc (_ * _)]

theorem word_lev (hψ : IsStd ψ) (l : List (V F κ × V F κ)) {Θ : (κ → AF F) → ℂ} (hΘ : Θ ∈ schA F κ) {m : ℕ} (h : Lev m Θ) :
    Lev m (word ψ l Θ) := by
  induction l with
  | nil => exact h
  | cons w l ih => exact (derivOK F κ ψ hψ w _ (word_mem hψ l hΘ)).2.2 m ih

theorem list_bound (hψ : IsStd ψ) {μ : @Measure (κ → AF F) (borel _)} (hμ : IsHaar μ) {Φ : (κ → AF F) → ℂ}
    (hΦ : Φ ∈ schA F κ) (j : ℕ) (S : List (List (V F κ × V F κ))) : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ k : ℕ,
      ∀ T s d (y : ℝ≥0), 1 ≤ y → Impl ψ T s → Bd s d y → ∀ b : V F κ, ‖b‖ ≤ 1 →
        (S.map fun l => nsq μ (word ψ l (word ψ (List.replicate j (0, b)) (T Φ)))).sum ≤ C * (y : ℝ≥0∞) ^ k := by
  induction S with
  | nil => exact ⟨0, by simp, 0, by simp⟩
  | cons l S ih =>
    obtain ⟨C, hC, k, h⟩ := ih
    obtain ⟨C', hC', h'⟩ := word_bound hψ hμ (l.length + j) Φ hΦ
    obtain ⟨R, hR1, hR⟩ : ∃ R : ℝ≥0, 1 ≤ R ∧ ∀ w ∈ l, ‖w‖ ≤ R :=
      ⟨1 + (l.map nnnorm).sum, le_self_add, fun w hw => by
        have : ‖w‖₊ ≤ (l.map nnnorm).sum := List.single_le_sum (fun _ _ => zero_le) _ (List.mem_map_of_mem hw)
        exact NNReal.coe_le_coe.2 (this.trans le_add_self)⟩
    refine ⟨C' * (R : ℝ≥0∞) ^ (2 * (l.length + j)) + C, by finiteness, 2 * (l.length + j) + k,
      fun T s d y hy hT hs b hb => ?_⟩
    obtain ⟨l', h1, h2, h3⟩ := hT.word hψ hμ y.2 hs hΦ R (l ++ List.replicate j (0, b)) fun w hw => by
      rcases List.mem_append.1 hw with hw | hw
      · exact hR w hw
      · rw [List.eq_of_mem_replicate hw, Prod.norm_mk, norm_zero]
        exact max_le R.2 (hb.trans hR1)
    have hy' : (1 : ℝ≥0∞) ≤ y := by exact_mod_cast hy
    rw [List.map_cons, List.sum_cons, add_mul]
    refine add_le_add ?_ ((h T s d y hy hT hs b hb).trans (mul_le_mul' le_rfl (pow_le_pow_right₀ hy' le_add_self)))
    have e : word ψ l (word ψ (List.replicate j (0, b)) (T Φ)) = T (word ψ l' Φ) := by
      rw [h3, word, word, word, List.foldr_append]
    rw [e, hT.unit μ hμ _ (word_mem hψ l' hΦ)]
    refine (h' l' (by simpa using h1) (y * R) h2).trans ?_
    rw [ENNReal.coe_mul, mul_pow, mul_comm ((y : ℝ≥0∞) ^ _), ← mul_assoc]
    exact mul_le_mul' le_rfl (pow_le_pow_right₀ hy' le_self_add)

theorem core (hF : FinInv) (hS : Sob) (hψ : IsStd ψ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (j : ℕ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ T s (d : ℕ) (y : ℝ), 1 ≤ d → (d : ℝ) ≤ y → Impl ψ T s → Bd s d y → ∀ b : V F κ, ‖b‖ ≤ 1 →
      ∀ x, ‖word ψ (List.replicate j (0, b)) (T Φ) x‖ ≤ C * y ^ k := by
  obtain ⟨μ, hμ, S, C, k, h⟩ := hS F κ ψ hψ
  obtain ⟨m₀, hm₀, h₀⟩ := hF F κ ψ hψ Φ hΦ
  obtain ⟨C', hC', k', h'⟩ := list_bound hψ hμ hΦ j S
  lift C' to ℝ≥0 using hC'
  refine ⟨1 + C * m₀ ^ k * C', k + k', by positivity, fun T s d y hd hy hT hs b hb x => ?_⟩
  have hy1 : (1 : ℝ) ≤ y := le_trans (by exact_mod_cast hd) hy
  lift y to ℝ≥0 using zero_le_one.trans hy1
  have lev : Lev (m₀ * d) (T Φ) := fun u hu x => by
    have := congrFun (h₀ T s d y hT hs (u, 0) ⟨hu, fun _ => ⟨rfl, fun v => by simp⟩⟩) x
    simpa [schr] using this
  have h1 := (h (m₀ * d) (Nat.mul_pos hm₀ hd) _ (word_mem hψ _ (hT.pres _ hΦ))
    (word_lev hψ (List.replicate j (0, b)) (hT.pres _ hΦ) lev) x).trans
    (mul_le_mul' le_rfl (h' T s d y (by exact_mod_cast hy1) hT hs b hb))
  rw [enorm_eq_nnnorm] at h1
  have h2 : ‖word ψ (List.replicate j (0, b)) (T Φ) x‖ ^ 2 ≤ C * ((m₀ : ℝ) * d) ^ k * (C' * (y : ℝ) ^ k') := by
    exact_mod_cast h1
  have h3 : C * ((m₀ : ℝ) * d) ^ k * (C' * (y : ℝ) ^ k') ≤ C * m₀ ^ k * C' * (y : ℝ) ^ (k + k') := by
    calc _ ≤ C * ((m₀ : ℝ) * y) ^ k * (C' * (y : ℝ) ^ k') := by gcongr
      _ = _ := by ring
  have h4 : (1 : ℝ) ≤ (y : ℝ) ^ (k + k') := one_le_pow₀ hy1
  rw [add_mul]
  nlinarith [sq_nonneg (‖word ψ (List.replicate j (0, b)) (T Φ) x‖ - 1), norm_nonneg (word ψ (List.replicate j (0, b)) (T Φ) x)]

theorem weighted (hF : FinInv) (hS : Sob) (hT : TrBd) (hψ : IsStd ψ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (N : ℕ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ T s (d : ℕ) (y : ℝ), 1 ≤ d → (d : ℝ) ≤ y → Impl ψ T s → Bd s d y →
      ∀ x, ‖T Φ x‖ * (1 + ‖fun i => evI F (x i)‖) ^ N ≤ C * y ^ k := by
  obtain ⟨C₀, k₀, p₀, h₀⟩ := core hF hS hψ hΦ 0
  obtain ⟨C₁, k₁, p₁, h₁⟩ := core hF hS hψ hΦ N
  obtain ⟨c, hc, hb⟩ := hT F κ
  refine ⟨2 ^ (N - 1) * (C₀ + c ^ N * C₁), k₀ + k₁, by positivity, fun T s d y hd hy hI hs x => ?_⟩
  have hy1 : (1 : ℝ) ≤ y := le_trans (by exact_mod_cast hd) hy
  obtain ⟨b, hb1, hb2⟩ := hb fun i => evI F (x i)
  have a₀ : ‖T Φ x‖ ≤ C₀ * y ^ k₀ := h₀ T s d y hd hy hI hs b hb1 x
  have a₁ := h₁ T s d y hd hy hI hs b hb1 x
  rw [word_mult hψ, norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs, linForm_apply] at a₁
  have hπ : (1 : ℝ) ≤ ‖-(2 * Real.pi * Complex.I : ℂ)‖ := by
    simp only [norm_neg, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_ofNat, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    linarith [Real.pi_gt_three]
  have a₂ : ‖T Φ x‖ * ‖fun i => evI F (x i)‖ ^ N ≤ c ^ N * (C₁ * y ^ k₁) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left a₁ (by positivity))
    rw [← mul_assoc, ← mul_pow, mul_comm]
    refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hb2.trans ?_) N) (norm_nonneg _)
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (abs_nonneg _) hπ) hc
  have e₀ : y ^ k₀ ≤ y ^ (k₀ + k₁) := pow_le_pow_right₀ hy1 le_self_add
  have e₁ : y ^ k₁ ≤ y ^ (k₀ + k₁) := pow_le_pow_right₀ hy1 le_add_self
  calc _ ≤ ‖T Φ x‖ * (2 ^ (N - 1) * (1 ^ N + ‖fun i => evI F (x i)‖ ^ N)) :=
        mul_le_mul_of_nonneg_left (add_pow_le zero_le_one (norm_nonneg _) N) (norm_nonneg _)
    _ = 2 ^ (N - 1) * (‖T Φ x‖ + ‖T Φ x‖ * ‖fun i => evI F (x i)‖ ^ N) := by ring
    _ ≤ 2 ^ (N - 1) * (C₀ * y ^ (k₀ + k₁) + c ^ N * (C₁ * y ^ (k₀ + k₁))) :=
        mul_le_mul_of_nonneg_left (add_le_add (a₀.trans (mul_le_mul_of_nonneg_left e₀ p₀))
          (a₂.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e₁ p₁) (pow_nonneg hc N)))) (by positivity)
    _ = _ := by ring

open GlobalTheory.LFun GlobalTheory.ThK in
theorem weil_rep_rapid_decay_of_growth (hA : HtBd) (hF : FinInv) (hS : Sob) (hT : TrBd) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h (x : Fin n × Fin d → AF F),
    ‖om (g, h) Φ x‖ * (1 + ‖fun i => evI F (x i)‖) ^ N ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ N
  obtain ⟨C, -, hC⟩ := hA F E σ n d X W M
  obtain ⟨C', k, -, h⟩ := weighted hF hS hT hP.base.std hΦ N
  refine ⟨C' * C ^ k, k, fun g g' x => ?_⟩
  obtain ⟨m, h1, h2, h3⟩ := hC g g'
  rw [mul_assoc, ← mul_pow]
  exact h _ _ m _ h1 h2 (impl_sOf hP.weil g g') h3 x

end PositivityTheory.ThKF0.Grow
