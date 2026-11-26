module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.StSemilocRankFrac
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveSectionQuotLocal
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcResidue

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFibreMultiHomog
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
  GroundTheory.Heights₂.Heights.Inter.FibreMultiHomogeneous

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem FibreMultiHomog.proof : FibreMultiHomog.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' G hv hP
  classical
  refine cyc_isMultiHomogIdeal_of_isHomogeneous fun k n f hf => ?_
  rw [show (DirectSum.decompose (weightedHomogeneousSubmodule G.Φ (cycBlockWt k)) f n : MvPolynomial _ G.Φ) =
    weightedHomogeneousComponent (cycBlockWt k) n f from MvPolynomial.decompose'_apply _ _ f n]
  obtain ⟨b, hb, F, e⟩ := exists_clear G f
  rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker] at hf ⊢
  have hF : liftZ κ v F ∈ P' := by
    rw [← G.genericFibre_ker_target, RingHom.mem_ker, aeval_liftZ, ← e, map_mul, aeval_C]
    simp [hf]
  have hc : weightedHomogeneousComponent (cycBlockWt k.1) n (liftZ κ v F) ∈ P' := by
    have hH := cyc_isHomogeneous_of_isMultiHomogIdeal hP k.1
    have := hH n hF
    rwa [show (DirectSum.decompose (weightedHomogeneousSubmodule ℤ (cycBlockWt k.1)) (liftZ κ v F) n : MRing ι') =
      weightedHomogeneousComponent (cycBlockWt k.1) n (liftZ κ v F) from
        MvPolynomial.decompose'_apply _ _ (liftZ κ v F) n] at this
  rw [liftZ_component hv, ← G.genericFibre_ker_target, RingHom.mem_ker, aeval_liftZ, ← component_map, ← e,
    weightedHomogeneousComponent_C_mul, map_mul, aeval_C] at hc
  exact (mul_eq_zero.1 hc).resolve_left ((map_ne_zero _).2 hb)

end GroundTheory.Heights₂.Heights.Targets
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo CurveVerticalPointChart

noncomputable section

theorem CurveVertPointChart.proof (hF : CurveRingFinite.Statement) (hCP : CurveClosedPointChart.Statement) :
    CurveVertPointChart.Statement := by
  classical
  intro K _ ι _ Ω _ y s d hy hs hsP W hW c hc
  have hWp : W.IsPrime := hW.1.1.1
  have hPW : mCoordIdeal y ≤ W := le_sup_left.trans hW.1.1.2
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => ne_zero_of_X_notMem fun h => hc k (hPW h)

  have hv := IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical.full K ι (mCoordIdeal y) s d hy hs hsP W hW
  rw [IsHorizontal, ← Ne, Submodule.ne_bot_iff] at hv
  obtain ⟨n, hn, hn0⟩ := hv
  have hmax := chartPrimeB_isMaximal y (hF K ι Ω y hy) hPW hWp hc hyc hn0 (Ideal.mem_comap.mp hn)
  rw [curvePtIdeal_eq y hPW hWp hc hyc]
  have hmp : (chartPrimeB y c W hyc).IsPrime := hmax.isPrime

  have hrat : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ locSub y _ hmp := by
    obtain ⟨c', hyc', h'⟩ := hCP K ι Ω y hy _ hmax
    have hinv : ∀ k, y ⟨k, c' k⟩ / y ⟨k, c k⟩ ∈ locSub y _ hmp := by
      intro k
      obtain ⟨a, b, hb, hab⟩ := h' ⟨k, c k⟩
      have hab0 : (b : Ω) * (y ⟨k, c k⟩ / y ⟨k, c' k⟩) = a := hab
      have hab' : (a : Ω) * y ⟨k, c' k⟩ = b * y ⟨k, c k⟩ := by
        rw [← hab0]
        field_simp [hyc' k]
      refine mem_locSub.mpr ⟨b, a, ?_, ?_⟩
      · intro ha
        obtain ⟨e, g, hg, hgW, he⟩ := mem_chartPrimeB.mp ha
        obtain ⟨f, w, hw, hbw⟩ := exists_rep y hyc (mem_chart y hyc b)
        apply hb
        refine mem_chartPrimeB.mpr ⟨f, w, hw, ?_, hbw⟩
        have h1 : X ⟨k, c k⟩ * (HilbertSamuel.SmallSectionsNonzero.chartMono c e * w) ∈ W := by
          refine mem_of_aeval_eq y hPW
            (Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_mul hg
              (Inter.AvoidRing.isMultiHomog_X k (c' k)))
              (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c f))
            (Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_X k (c k))
              (Inter.AvoidRing.isMultiHomog_mul
                (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c e) hw))
            (by abel) ?_ (W.mul_mem_right _ (W.mul_mem_right _ hgW))
          simp only [map_mul, aeval_X, HilbertSamuel.SmallSectionsNonzero.aeval_chartMono]
          linear_combination (-(y ⟨k, c' k⟩ * ∏ k, y ⟨k, c k⟩ ^ f k)) * he +
            (y ⟨k, c k⟩ * ∏ k, y ⟨k, c k⟩ ^ e k) * hbw +
            ((∏ k, y ⟨k, c k⟩ ^ e k) * ∏ k, y ⟨k, c k⟩ ^ f k) * hab'
        exact mem_of_chartMono_mul hWp hc ((hWp.mem_or_mem h1).resolve_left (hc k))
      · rw [← hab0]
        field_simp [hyc' k, hyc k]
    intro p
    obtain ⟨a, b, hb, hab⟩ := h' p
    have hu : y p / y ⟨p.1, c' p.1⟩ ∈ locSub y _ hmp := mem_locSub.mpr ⟨a, b, hb, hab⟩
    have hprod := mul_mem hu (hinv p.1)
    have he : y p / y ⟨p.1, c' p.1⟩ * (y ⟨p.1, c' p.1⟩ / y ⟨p.1, c p.1⟩) = y p / y ⟨p.1, c p.1⟩ := by
      field_simp [hyc' p.1, hyc p.1]
    rwa [he] at hprod
  have hY : ∀ e : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ e k ≠ 0 := fun e =>
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)
  refine ⟨hmax, fun p => mem_locSub.mp (hrat p), fun e g hg => ⟨fun hgW => ?_, ?_⟩⟩
  · have hr : aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-(e k : ℤ)) ∈ chartRingZ y c :=
      (HilbertSamuel.LiftBirationalAmple.mem_chartLat_one y).mp
        (HilbertSamuel.LiftBirationalAmple.chartLat_form hg) c hyc
    have hinv : ∏ k, y ⟨k, c k⟩ ^ (-(e k : ℤ)) = (∏ k, y ⟨k, c k⟩ ^ e k)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun k _ => by rw [zpow_neg, zpow_natCast]
    rw [hinv] at hr
    obtain ⟨a, b, hb, hab⟩ := mem_locSub.mp (chart_le_locSub y _ hmp c hrat hr)
    have hab' : (b : Ω) * aeval y g = a * ∏ k, y ⟨k, c k⟩ ^ e k := by
      rw [← hab]
      field_simp [hY e]
    refine ⟨a, b, ?_, hb, hab'⟩
    obtain ⟨f, w, hw, hbw⟩ := exists_rep y hyc (mem_chart y hyc b)
    refine mem_chartPrimeB.mpr ⟨f + e, w * g, Inter.AvoidRing.isMultiHomog_mul hw hg, W.mul_mem_left _ hgW, ?_⟩
    rw [prod_pow_add, map_mul]
    linear_combination (-(∏ k, y ⟨k, c k⟩ ^ f k)) * hab' + (aeval y g) * hbw
  · rintro ⟨a, b, ha, hb, hab⟩
    obtain ⟨f, v, hv, hvW, hav⟩ := mem_chartPrimeB.mp ha
    obtain ⟨f', w, hw, hbw⟩ := exists_rep y hyc (mem_chart y hyc b)
    have hwW : w ∉ W := fun h => hb (mem_chartPrimeB.mpr ⟨f', w, hw, h, hbw⟩)
    have h1 : HilbertSamuel.SmallSectionsNonzero.chartMono c f * (w * g) ∈ W := by
      refine mem_of_aeval_eq y hPW
        (Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_mul
          (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c e)
          (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c f')) hv)
        (Inter.AvoidRing.isMultiHomog_mul (HilbertSamuel.SmallSectionsNonzero.isMultiHomog_chartMono c f)
          (Inter.AvoidRing.isMultiHomog_mul hw hg))
        (by abel) ?_ (W.mul_mem_left _ hvW)
      simp only [map_mul, HilbertSamuel.SmallSectionsNonzero.aeval_chartMono]
      linear_combination (-((∏ k, y ⟨k, c k⟩ ^ e k) * ∏ k, y ⟨k, c k⟩ ^ f' k)) * hav +
        ((∏ k, y ⟨k, c k⟩ ^ f k) * aeval y g) * hbw -
        ((∏ k, y ⟨k, c k⟩ ^ f k) * ∏ k, y ⟨k, c k⟩ ^ f' k) * hab
    exact (hWp.mem_or_mem (mem_of_chartMono_mul hWp hc h1)).resolve_left hwW

end

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointMultChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace CurveVerticalPointMultiplicity

variable {K : Type} {ι : K → Type}

theorem aeval_mul_of_homog [Fintype K] [∀ k, Fintype (ι k)] {S : Type*} [CommRing S] [Algebra ℤ S] (r : (Σ k, ι k) → S) (t : K → S) {f : MRing ι}
    {d : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f d) :
    aeval (fun p => r p * t p.1) f = aeval r f * ∏ k, t k ^ d k := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial, mul_assoc]
  congr 1
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  congr 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  dsimp only
  rw [Finset.prod_pow_eq_pow_sum, hf m hm k]

theorem map_aeval_int {S T : Type*} [CommRing S] [CommRing T] [Algebra ℤ S] [Algebra ℤ T] (φ : S →+* T) (r : (Σ k, ι k) → S)
    (f : MRing ι) : φ (aeval r f) = aeval (fun p => φ (r p)) f := by
  induction f using MvPolynomial.induction_on with
  | C n => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

end CurveVerticalPointMultiplicity


open CurveVerticalPointMultiplicity GroundTheory.Heights₂.Heights.VerticalPointMultiplicityChart in
theorem CurveVertPointMultChart.proof (hCh : CurveVertPointChart.Statement)
    (hN : CurveVertPointNagata.Statement) : CurveVertPointMultChart.Statement := by
  classical
  intro K _ ι _ Ω _ y s d hP hs hsP W hW c hc a b hb hab
  obtain ⟨hmax, hrat, -⟩ := hCh K ι Ω y s d hP hs hsP W hW c hc
  have hWp : W.IsPrime := hW.1.1.1
  have hmp : (curvePtIdeal y W).IsPrime := hmax.isPrime
  choose a' b' hb' hab' using hrat
  obtain ⟨Φ, hsurj, hker, hΦ⟩ := hN K ι Ω y s d hP hs hsP W hW c hc a' b' hb' hab'
  have hPW : mCoordIdeal y ≤ W := le_sup_left.trans hW.1.1.2
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => ne_zero_of_X_notMem fun h => hc k (hPW h)

  have hunit : ∀ x : (curvePtIdeal y W).primeCompl, IsUnit ((curveRing y).subtype x) := fun x =>
    isUnit_iff_ne_zero.mpr fun h => x.2 (by
      rw [show (x : curveRing y) = 0 from Subtype.ext h]; exact zero_mem _)
  let e : Localization.AtPrime (curvePtIdeal y W) →+* Ω := IsLocalization.lift hunit
  have hinj : Function.Injective e := by
    rw [IsLocalization.lift_injective_iff]
    intro x z
    rw [(IsLocalization.injective (M := (curvePtIdeal y W).primeCompl)
      (Localization.AtPrime (curvePtIdeal y W)) (le_nonZeroDivisors_of_noZeroDivisors fun h =>
        h (zero_mem _))).eq_iff]
    exact Subtype.val_injective.eq_iff.symm
  have hbc : b ∈ (curvePtIdeal y W).primeCompl := hb
  let r : (Σ k, ι k) → Localization.AtPrime (curvePtIdeal y W) := fun p =>
    IsLocalization.mk' _ (a' p) (⟨b' p, hb' p⟩ : (curvePtIdeal y W).primeCompl)
  have her : ∀ p, e (r p) = y p / y ⟨p.1, c p.1⟩ := fun p =>
    (IsLocalization.lift_mk'_spec _ _ _ _).mpr (hab' p).symm
  have hsr : aeval r s = IsLocalization.mk' _ a (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl) := by
    apply hinj
    rw [map_aeval_int, funext her]
    have key : aeval y s = aeval (fun p => y p / y ⟨p.1, c p.1⟩) s * ∏ k, y ⟨k, c k⟩ ^ d k := by
      rw [← aeval_mul_of_homog _ (fun k => y ⟨k, c k⟩) hs]
      exact congrArg (fun v => aeval v s) (funext fun p => (div_mul_cancel₀ _ (hyc p.1)).symm)
    have hpc : ∏ k, y ⟨k, c k⟩ ^ d k ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)
    symm
    refine (IsLocalization.lift_mk'_spec _ _ _ _).mpr ?_
    change (a : Ω) = (b : Ω) * _
    apply mul_right_cancel₀ hpc
    rw [mul_assoc, ← key, hab]

  have hXk : ∀ k, (X k : MvPolynomial K (Localization.AtPrime (curvePtIdeal y W))) ∈
      ((IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
        (MvPolynomial.C : _ →+* MvPolynomial K _)).primeCompl := fun k h => by
    have h1 := MvPolynomial.mem_map_C_iff.mp h (Finsupp.single k 1)
    rw [MvPolynomial.coeff_X, if_pos rfl] at h1
    exact (IsLocalRing.maximalIdeal _).ne_top_iff_one.mp (IsLocalRing.maximalIdeal.isMaximal _).ne_top h1
  have hprod : (∏ k, X k ^ d k : MvPolynomial K (Localization.AtPrime (curvePtIdeal y W))) ∈
      ((IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
        (MvPolynomial.C : _ →+* MvPolynomial K _)).primeCompl :=
    Submonoid.prod_mem _ fun k _ => Submonoid.pow_mem _ (hXk k) _
  have hbu : IsUnit (IsLocalization.mk' (Localization.AtPrime (curvePtIdeal y W)) (1 : curveRing y)
      (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl)) :=
    isUnit_iff_exists_inv.mpr ⟨algebraMap _ _ b, (IsLocalization.mk'_spec _ _ _).trans (map_one _)⟩
  have hΦs : Φ (algebraMap _ _ s) =
      algebraMap (Localization.AtPrime (curvePtIdeal y W)) (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
        (algebraMap (curveRing y) _ a) *
      (algebraMap (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W)))
          (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
          (MvPolynomial.C (IsLocalization.mk' (Localization.AtPrime (curvePtIdeal y W)) (1 : curveRing y)
            (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl))) *
        algebraMap (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W)))
          (mNagataRing K (Localization.AtPrime (curvePtIdeal y W))) (∏ k, X k ^ d k)) := by
    rw [hΦ s, aeval_mul_of_homog (fun p => MvPolynomial.C (r p)) X hs, ← map_aeval_int MvPolynomial.C, hsr,
      IsLocalization.mk'_eq_mul_mk'_one, map_mul, map_mul, map_mul, ← mul_assoc,
      IsScalarTower.algebraMap_apply (Localization.AtPrime (curvePtIdeal y W))
        (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W))) (mNagataRing K _), MvPolynomial.algebraMap_eq]
  have hv : IsUnit (algebraMap (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W)))
          (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
          (MvPolynomial.C (IsLocalization.mk' (Localization.AtPrime (curvePtIdeal y W)) (1 : curveRing y)
            (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl))) *
        algebraMap (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W)))
          (mNagataRing K (Localization.AtPrime (curvePtIdeal y W))) (∏ k, X k ^ d k)) :=
    ((hbu.map MvPolynomial.C).map _).mul (IsLocalization.map_units _ ⟨_, hprod⟩)

  have hJ : ((mCoordIdeal y ⊔ Ideal.span {s}).map (algebraMap _ (Localization.AtPrime W))).map Φ =
      (Ideal.span {algebraMap (curveRing y) (Localization.AtPrime (curvePtIdeal y W)) a}).map
        (algebraMap _ (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))) := by
    rw [Ideal.map_sup, Ideal.map_sup, (Ideal.map_eq_bot_iff_le_ker _).mpr hker.ge, bot_sup_eq,
      Ideal.map_span, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
      Set.image_singleton, hΦs, Ideal.span_singleton_mul_right_unit hv]

  have hmap : (IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
      (algebraMap _ (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))) =
      IsLocalRing.maximalIdeal (mNagataRing K (Localization.AtPrime (curvePtIdeal y W))) := by
    rw [IsScalarTower.algebraMap_eq (Localization.AtPrime (curvePtIdeal y W))
      (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W))) (mNagataRing K _), ← Ideal.map_map,
      MvPolynomial.algebraMap_eq, IsLocalization.AtPrime.map_eq_maximalIdeal]
  have : IsLocalHom (algebraMap (Localization.AtPrime (curvePtIdeal y W))
      (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))) := by
    refine ⟨fun x hx => ?_⟩
    by_contra hx'
    have h1 : x ∈ IsLocalRing.maximalIdeal _ := hx'
    have h2 := Ideal.mem_map_of_mem
      (algebraMap _ (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))) h1
    rw [hmap] at h2
    exact h2 hx
  have hfib : Module.length (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
      (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)) ⧸
        (IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
          (algebraMap _ (mNagataRing K (Localization.AtPrime (curvePtIdeal y W))))) = 1 := by
    rw [hmap]
    have : IsSimpleModule (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
        (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)) ⧸
          IsLocalRing.maximalIdeal (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩
    exact Module.length_eq_one _ _

  rw [multAt, dite_eq_left hWp, locLen, dite_eq_left hmp]
  congr 1
  rw [length_localizedModule_quotient, length_localizedModule_quotient,
    length_quotient_of_surjective Φ hsurj _ (hker.le.trans (Ideal.map_mono le_sup_left)), hJ,
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (mNagataRing K (Localization.AtPrime (curvePtIdeal y W)))
      (Ideal.span {algebraMap (curveRing y) (Localization.AtPrime (curvePtIdeal y W)) a})).toLinearEquiv.length_eq,
    IsLocalRing.length_baseChange, hfib, mul_one, Ideal.map_span, Set.image_singleton]

end

end GroundTheory.Heights₂.Heights.Targets
end
