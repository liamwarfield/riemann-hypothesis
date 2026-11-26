module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchAwayFromRim
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInvarianceOfDomain
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionImageSup
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBergmanDensChartSum
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPointHeightFS
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockGraphFibreRatio
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseTop
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPerturbMonomial
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionMetricPair
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockSectionsRank
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GeneratedVOfGeneratedMod
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConstantsDescend
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreRelLift
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedEffectiveSection
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedNonzeroSection
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGramChiDerivative
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGraphIsometricForms
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLocalChange
public import GroundTheory.AutomorphicForms.HermitianExistenceLocal
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PRootsOfUnityValuation
public import GroundTheory.HeightsAndTheta.Heights.Slopes
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftSpread
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullConeDegreeInt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameGenPtRel
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRatNoetherFrame
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormPrimeBound
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PReductionComplex
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResVolume
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockModuleFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionMetricPair
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionPullback
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionOrderAtPoint
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedSectionStep
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZeroCocycleSection
public import GroundTheory.HeightsAndTheta.Heights.Intersections.NormSegreSameOrbit
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PBlockRatioAlg
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingNoeth
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisTer
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PSwapCycles
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PBoundedSectionTransfer
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDiagFibreFubini
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageArithClosed
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveDegreeVert
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChart
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartDim
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PResAboveCover

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPolyNonnegAtZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Filter

def PolyNonnegAtZero.Statement : Prop :=
  ∀ (d : ℕ) (p : Polynomial ℝ) (c : ℝ), 0 < c →
    (∀ t : ℚ, 0 < t → 0 < p.eval (t : ℝ) → c * (t : ℝ) ^ d ≤ p.eval (t : ℝ)) →
    (∀ᶠ t in atTop, 0 < p.eval t) → 0 ≤ p.eval 0

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseResolution
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Set
  GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CP

noncomputable section

namespace VeroneseResolution

variable {D : ℕ}

def ix (a b : Fin (D + 1)) : Ix (Veronese.Idx D) := ⟨(), ⟨(min a b, max a b), min_le_max⟩⟩

theorem map_ix (w : Fin (D + 1) → ℂ) (a b : Fin (D + 1)) : Veronese.map D w (ix a b) = w a * w b := by
  rcases le_total a b with h | h
  · simp [Veronese.map, ix, min_eq_left h, max_eq_right h]
  · simp [Veronese.map, ix, min_eq_right h, max_eq_left h, mul_comm]

theorem x_ix (a b : Fin (D + 1)) : Veronese.x D (ix a b) = Veronese.t D a * Veronese.t D b := by
  rcases le_total a b with h | h
  · simp [Veronese.x, ix, min_eq_left h, max_eq_right h]
  · simp [Veronese.x, ix, min_eq_right h, max_eq_left h, mul_comm]

theorem ix_self (q : Ix (Veronese.Idx D)) : ix q.2.1.1 q.2.1.2 = q := by
  obtain ⟨⟨⟩, ⟨⟨a, b⟩, h⟩⟩ := q
  simp [ix, min_eq_left h, max_eq_right h]

theorem map_smul (s : ℂ) (v : Fin (D + 1) → ℂ) :
    Veronese.map D (s • v) = (s ^ 2) • Veronese.map D v := by
  funext q
  simp only [Veronese.map, Pi.smul_apply, smul_eq_mul]
  ring

def subst (f : MvPolynomial (Ix (Veronese.Idx D)) ℤ) : MvPolynomial (Fin (D + 1)) ℚ :=
  eval₂ (Int.castRingHom _) (fun q => X q.2.1.1 * X q.2.1.2) f

theorem algebraMap_subst (f : MvPolynomial (Ix (Veronese.Idx D)) ℤ) :
    algebraMap (MvPolynomial (Fin (D + 1)) ℚ) (Veronese.Fld D) (subst f) =
      Polynomial.eval 1 (coneMap ℤ (Veronese.x D) f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [subst, eval₂_C]
    simp [coneMap]
  | add p q hp hq => simp only [subst, eval₂_add, map_add (f := _), Polynomial.eval_add] at hp hq ⊢; rw [hp, hq]
  | mul_X p n hp =>
    simp only [subst, eval₂_mul, eval₂_X, map_mul, Polynomial.eval_mul] at hp ⊢
    rw [hp]
    simp [coneMap, Veronese.x, Veronese.t]

theorem eval_veronese (w : Fin (D + 1) → ℂ) (f : MvPolynomial (Ix (Veronese.Idx D)) ℤ) :
    eval (Veronese.map D w) (MvPolynomial.map (Int.castRingHom ℂ) f) = eval₂ (algebraMap ℚ ℂ) w (subst f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [subst, eval₂_C, eq_intCast, ← coe_eval₂Hom, map_intCast]
    simp
  | add p q hp hq => simp only [subst, eval₂_add, map_add (f := _)] at hp hq ⊢; rw [hp, hq]
  | mul_X p n hp =>
    simp only [subst, eval₂_mul, eval₂_X, map_mul, map_X, eval_X] at hp ⊢
    rw [hp]
    rfl

theorem subst_eq_zero {f : MvPolynomial (Ix (Veronese.Idx D)) ℤ} (hf : f ∈ coordIdeal ℤ (Veronese.x D)) :
    subst f = 0 := by
  have h0 : coneMap ℤ (Veronese.x D) f = 0 := hf
  apply IsFractionRing.injective (MvPolynomial (Fin (D + 1)) ℚ) (Veronese.Fld D)
  rw [algebraMap_subst, h0, map_zero, Polynomial.eval_zero]

theorem eval_veronese_eq_zero (w : Fin (D + 1) → ℂ) {f : MvPolynomial (Ix (Veronese.Idx D)) ℤ}
    (hf : f ∈ coordIdeal ℤ (Veronese.x D)) :
    eval (Veronese.map D w) (MvPolynomial.map (Int.castRingHom ℂ) f) = 0 := by
  rw [eval_veronese, subst_eq_zero hf, eval₂_zero]

theorem one_not_mem : (1 : MvPolynomial (Ix (Veronese.Idx D)) ℤ) ∉ coordIdeal ℤ (Veronese.x D) := by
  intro h
  have := eval_veronese_eq_zero 0 h
  simp at this

theorem mcPts_top_eq : mcPts (ι := GlobalTheory (Veronese.Idx D)) ⊤ = ∅ := by
  ext z
  simp only [mcPts, mem_ofPred_eq, Submodule.mem_top, mem_empty_iff_false, iff_false, not_and]
  intro _ h
  have := h 1 trivial
  simp at this

def quad (a b c d : Fin (D + 1)) : MvPolynomial (Ix (Veronese.Idx D)) ℤ :=
  X (ix a b) * X (ix c d) - X (ix a c) * X (ix b d)

theorem quad_mem (a b c d : Fin (D + 1)) : quad a b c d ∈ coordIdeal ℤ (Veronese.x D) := by
  change coneMap ℤ (Veronese.x D) (quad a b c d) = 0
  simp only [quad, coneMap, map_sub, map_mul, aeval_X, x_ix]
  ring

theorem quad_rel {z : Ix (Veronese.Idx D) → ℂ}
    (hz : ∀ f ∈ coordIdeal ℤ (Veronese.x D), eval z (MvPolynomial.map (Int.castRingHom ℂ) f) = 0)
    (a b c d : Fin (D + 1)) : z (ix a b) * z (ix c d) = z (ix a c) * z (ix b d) := by
  have := hz _ (quad_mem a b c d)
  simp only [quad, map_sub, map_mul, map_X, eval_X] at this
  exact sub_eq_zero.mp this

theorem chartVec_chartCoord_mk (i : Fin (D + 1)) (v : Fin (D + 1) → ℂ) (hv : v ≠ 0) (hvi : v i ≠ 0) :
    chartVec i (chartCoord i (Projectivization.mk ℂ v hv)) = (v i)⁻¹ • v := by
  rw [chartCoord_mk]
  funext m
  obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i m
  · simp [hvi]
  · simp [div_eq_inv_mul]

theorem rep_apply_ne_zero {i : Fin (D + 1)} {y : CP D} (hy : y ∈ chartDomain i) : y.rep i ≠ 0 := by
  rw [← Projectivization.mk_rep y] at hy
  exact (mk_mem_chartDomain i _ _).1 hy

theorem chartVec_chartCoord_rep {i : Fin (D + 1)} {y : CP D} (hy : y ∈ chartDomain i) :
    chartVec i (chartCoord i y) = (y.rep i)⁻¹ • y.rep := by
  conv_lhs => rw [← Projectivization.mk_rep y]
  exact chartVec_chartCoord_mk i _ _ (rep_apply_ne_zero hy)

def lift (p y : CP D) : Ix (Veronese.Idx D) → ℂ :=
  Veronese.map D (chartVec (chartIndex p) (chartCoord (chartIndex p) y))

theorem lift_eq {p y : CP D} (hy : y ∈ chartDomain (chartIndex p)) :
    lift p y = ((y.rep (chartIndex p))⁻¹ ^ 2) • Veronese.map D y.rep := by
  rw [lift, chartVec_chartCoord_rep hy, map_smul]

theorem lift_ne_zero (p y : CP D) : lift p y ⟨(), ⟨(chartIndex p, chartIndex p), le_rfl⟩⟩ ≠ 0 := by
  simp [lift, Veronese.map]

theorem holo_lift (p : CP D) (q : Ix (Veronese.Idx D)) :
    (projAtlas D).HoloOn (chartDomain (chartIndex p)) (fun y => lift p y q) := by
  intro j z hz
  set i := chartIndex p
  have hzi : chartVec j z i ≠ 0 := hz.2
  have hf : AnalyticAt ℂ (fun w : Fin D → ℂ =>
      (chartVec j w i)⁻¹ * chartVec j w q.2.1.1 * ((chartVec j w i)⁻¹ * chartVec j w q.2.1.2)) z :=
    ((((ProjFS.analyticAt_chartVec_apply j i z).inv hzi).mul (ProjFS.analyticAt_chartVec_apply j _ z)).mul
      (((ProjFS.analyticAt_chartVec_apply j i z).inv hzi).mul (ProjFS.analyticAt_chartVec_apply j _ z)))
  refine hf.congr ?_
  filter_upwards [ProjFS.eventually_chartVec_ne hzi] with w hw
  change _ = Veronese.map D (chartVec i (chartCoord i (chartInv j w))) q
  rw [ProjFS.chartVec_chartCoord_chartInv hw]
  rfl

def res (D : ℕ) : AnRes (ι := GlobalTheory (Veronese.Idx D)) (coordIdeal ℤ (Veronese.x D)) ⊤ D where
  homog := ⟨{1}, fun f hf => ⟨0, by
      rw [mem_singleton_iff.mp hf]
      intro m hm k
      rw [support_one, Finset.mem_singleton] at hm
      simp [hm]⟩, Ideal.span_singleton_one.symm⟩
  nondeg h := one_not_mem (h Submodule.mem_top)
  X := CP D
  A := projAtlas D
  U p := chartDomain (chartIndex p)
  isOpen_U _ := isOpen_chartDomain _
  mem_U p := mem_chartDomain_chartIndex p
  lift := lift
  holo := holo_lift
  mem p y _ := ⟨fun _ => ⟨⟨(chartIndex p, chartIndex p), le_rfl⟩, lift_ne_zero p y⟩,
    fun _ hf => eval_veronese_eq_zero _ hf⟩
  compat p p' y hy := by
    refine ⟨fun _ => ((y.rep (chartIndex p))⁻¹ ^ 2) / ((y.rep (chartIndex p'))⁻¹ ^ 2),
      fun _ => div_ne_zero (pow_ne_zero _ (inv_ne_zero (rep_apply_ne_zero hy.1)))
        (pow_ne_zero _ (inv_ne_zero (rep_apply_ne_zero hy.2))), ?_⟩
    rw [lift_eq hy.1, lift_eq hy.2]
    funext q
    have h1 : y.rep (chartIndex p) ≠ 0 := rep_apply_ne_zero hy.1
    have h2 : y.rep (chartIndex p') ≠ 0 := rep_apply_ne_zero hy.2
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  surj z hz _ := by
    obtain ⟨qi, hq0⟩ := hz.1 ()
    have rel := quad_rel hz.2

    obtain ⟨a, ha⟩ : ∃ a, z (ix a a) ≠ 0 := by
      set q : Ix (Veronese.Idx D) := ⟨(), qi⟩
      have hzq : z (ix q.2.1.1 q.2.1.2) ≠ 0 := by rw [ix_self]; exact hq0
      refine ⟨q.2.1.1, fun h0 => hzq ?_⟩
      have := rel q.2.1.1 q.2.1.2 q.2.1.1 q.2.1.2
      rw [h0, zero_mul] at this
      exact mul_self_eq_zero.mp this
    set w : Fin (D + 1) → ℂ := fun j => z (ix a j) with hw
    have hw0 : w ≠ 0 := fun h => ha (congrFun h a)
    have hmap : Veronese.map D w = z (ix a a) • z := by
      funext q
      rw [← ix_self q, map_ix, Pi.smul_apply, smul_eq_mul]
      exact rel a q.2.1.1 a q.2.1.2
    set p := Projectivization.mk ℂ w hw0
    have hp : p ∈ chartDomain (chartIndex p) := mem_chartDomain_chartIndex p
    have hwi : w (chartIndex p) ≠ 0 := hp
    refine ⟨p, fun _ => (w (chartIndex p))⁻¹ ^ 2 * z (ix a a),
      fun _ => mul_ne_zero (pow_ne_zero _ (inv_ne_zero hwi)) ha, ?_⟩
    change Veronese.map D (chartVec (chartIndex p) (chartCoord (chartIndex p) p)) = _
    rw [chartVec_chartCoord_mk _ w hw0 hwi, map_smul, hmap]
    funext q
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  inj p p' _ h := by
    obtain ⟨c, hc, hcz⟩ := h
    rw [lift_eq (mem_chartDomain_chartIndex p), lift_eq (mem_chartDomain_chartIndex p')] at hcz
    set v := p.rep
    set v' := p'.rep
    have hv : v (chartIndex p) ≠ 0 := rep_apply_ne_zero (mem_chartDomain_chartIndex p)
    have hv' : v' (chartIndex p') ≠ 0 := rep_apply_ne_zero (mem_chartDomain_chartIndex p')

    set e : ℂ := (v (chartIndex p))⁻¹⁻¹ ^ 2 * c () * (v' (chartIndex p'))⁻¹ ^ 2 with he
    have he0 : e ≠ 0 := by
      simp only [he]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (inv_ne_zero (inv_ne_zero hv))) (hc ()))
        (pow_ne_zero _ (inv_ne_zero hv'))
    have hab : ∀ a b, v a * v b = e * (v' a * v' b) := by
      intro a b
      have := congrFun hcz (ix a b)
      simp only [Pi.smul_apply, smul_eq_mul, map_ix] at this
      rw [he]
      field_simp at this ⊢
      linear_combination this
    set a := chartIndex p
    have hva' : v' a ≠ 0 := by
      intro h0
      have := hab a a
      rw [h0, zero_mul, mul_zero] at this
      exact hv (mul_self_eq_zero.mp this)
    rw [← Projectivization.mk_rep p, ← Projectivization.mk_rep p', Projectivization.mk_eq_mk_iff']
    refine ⟨v a / v' a, ?_⟩
    funext b
    simp only [Pi.smul_apply, smul_eq_mul]
    have h1 := hab a b
    have h2 := hab a a
    rw [div_mul_eq_mul_div, div_eq_iff hva']
    apply mul_left_cancel₀ hv
    linear_combination v' b * h2 - v' a * h1
  null j := by
    have : {x : CP D | lift x x ∈ mcPts (ι := GlobalTheory (Veronese.Idx D)) ⊤} = ∅ := by
      rw [mcPts_top_eq]; rfl
    change volume (_ ∩ chartInv j ⁻¹' {x : CP D | lift x x ∈ mcPts (ι := GlobalTheory (Veronese.Idx D)) ⊤}) = 0
    rw [this, preimage_empty, inter_empty, measure_empty]

theorem isSmoothVolume_fs (D : ℕ) : IsSmoothVolume (projAtlas D) (fsMeasure D) := by
  refine ⟨inferInstance, fun j => ⟨fsVolumeDensity j, (fsVolume D).smooth j,
    fun y _ => fsVolumeDensity_pos j y, fun S hS hsub => ?_⟩⟩
  have hsub' : S ⊆ chartDomain (N := D) j := hsub
  change fsMeasure D S = ∫⁻ y in univ ∩ chartInv j ⁻¹' S, ENNReal.ofReal (fsVolumeDensity j y)
  rw [univ_inter]
  have h := ProjFS.setLIntegral_fsMeasure_chartDomain (N := D) j (S.indicator 1) (measurable_one.indicator hS)
  rw [lintegral_indicator_one hS, Measure.restrict_apply hS, inter_eq_left.mpr hsub'] at h
  rw [h, ← lintegral_indicator ((measurable_chartInv j) hS)]
  congr 1
  funext y
  by_cases hy : chartInv j y ∈ S
  · have hy' : y ∈ chartInv j ⁻¹' S := hy
    rw [indicator_of_mem hy, indicator_of_mem hy', Pi.one_apply, one_mul]
  · have hy' : y ∉ chartInv j ⁻¹' S := hy
    rw [indicator_of_notMem hy, indicator_of_notMem hy', zero_mul]

theorem lift_self_eq (p : CP D) :
    lift p p = ((p.rep (chartIndex p))⁻¹ ^ 2) • Veronese.map D p.rep :=
  lift_eq (mem_chartDomain_chartIndex p)

end VeroneseResolution


open VeroneseResolution in
theorem VeroneseResolution.proof : VeroneseResolution.Statement := by
  intro D _
  refine ⟨⊤, res D, CP.instMeasurableSpace, CP.instBorelSpace, fsMeasure D, isSmoothVolume_fs D,
    fun g hg => ?_⟩
  have key : ∀ p : CP D, g (lift p p) = g (Veronese.map D p.rep) := fun p => by
    rw [lift_self_eq p]
    exact hg _ _ (pow_ne_zero _ (inv_ne_zero (rep_apply_ne_zero (mem_chartDomain_chartIndex p))))
  exact integral_congr_ae (Filter.Eventually.of_forall key)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPolyNonnegAtZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Filter Topology

theorem PolyNonnegAtZero.proof : PolyNonnegAtZero.Statement := by
  intro d p c hc hdom hev
  by_contra h0
  push Not at h0
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  let S : Set ℝ := {t | 0 ≤ t ∧ p.eval t ≤ 0}
  have h0S : (0 : ℝ) ∈ S := ⟨le_rfl, h0.le⟩
  have hbdd : BddAbove S := ⟨N, fun t ht => by
    by_contra hlt
    push Not at hlt
    exact absurd ht.2 (not_le.2 (hN t hlt.le))⟩
  have hclosed : IsClosed S :=
    (isClosed_le continuous_const continuous_id).inter
      (isClosed_le p.continuous continuous_const)
  have ht0S : sSup S ∈ S := hclosed.csSup_mem ⟨0, h0S⟩ hbdd
  obtain ⟨ht0nn, hpt0⟩ := ht0S
  have hpos : ∀ t, sSup S < t → 0 < p.eval t := by
    intro t ht
    by_contra hle
    push Not at hle
    exact absurd (le_csSup hbdd ⟨ht0nn.trans ht.le, hle⟩) (not_le.2 ht)
  have hlim : c * (sSup S) ^ d ≤ p.eval (sSup S) := by
    by_contra hlt
    push Not at hlt
    have hcont : Continuous fun t : ℝ => p.eval t - c * t ^ d :=
      p.continuous.sub (continuous_const.mul (continuous_pow d))
    have hev' : ∀ᶠ t in 𝓝 (sSup S), p.eval t - c * t ^ d < 0 :=
      hcont.continuousAt.eventually (gt_mem_nhds (by linarith))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev'
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show sSup S < sSup S + ε by linarith)
    have hqpos : (0 : ℝ) < q := lt_of_le_of_lt ht0nn hq1
    have hd : dist (q : ℝ) (sSup S) < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have h1 := hball hd
    have h2 := hdom q (by exact_mod_cast hqpos) (hpos q hq1)
    linarith
  rcases ht0nn.lt_or_eq with htpos | htz
  · have : 0 < c * (sSup S) ^ d := mul_pos hc (pow_pos htpos d)
    linarith
  · have hp0 : 0 ≤ p.eval (sSup S) := le_trans (mul_nonneg hc.le (pow_nonneg ht0nn d)) hlim
    rw [← htz] at hp0
    linarith

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedTopAlgebra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Filter Polynomial

theorem MixedTopAlgebra.clear_den (d : ℕ) (m : ℕ → ℝ) (Q x : ℝ) (hQ : Q ≠ 0) :
    Q ^ d * ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * m i * (x / Q) ^ i =
      ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * Q ^ (d - i) * x ^ i * m i := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hid : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hpow : Q ^ d = Q ^ (d - i) * Q ^ i := by rw [← pow_add, Nat.sub_add_cancel hid]
  rw [hpow, div_pow]
  field_simp

theorem MixedTopAlgebra.sum_ge (d : ℕ) (m : ℕ → ℝ) (hm : ∀ i, 1 ≤ i → i ≤ d → 0 ≤ m i)
    (Q x : ℝ) (hQ : 0 ≤ Q) (hx : 0 ≤ x) :
    Q * ∑ i ∈ Finset.range d, ((d - 1).choose i : ℝ) * Q ^ (d - 1 - i) * x ^ i * m i
        + x ^ d * m d ≤
      ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * Q ^ (d - i) * x ^ i * m i := by
  rw [Finset.sum_range_succ, Nat.choose_self, Nat.sub_self, pow_zero, Finset.mul_sum]
  simp only [Nat.cast_one, one_mul, mul_one]
  refine add_le_add (Finset.sum_le_sum fun i hi => ?_) le_rfl
  have hid : i < d := Finset.mem_range.mp hi
  have hpow : Q * Q ^ (d - 1 - i) = Q ^ (d - i) := by
    rw [← pow_succ']; congr 1; omega
  calc Q * (((d - 1).choose i : ℝ) * Q ^ (d - 1 - i) * x ^ i * m i)
      = ((d - 1).choose i : ℝ) * (Q * Q ^ (d - 1 - i)) * x ^ i * m i := by ring
    _ = ((d - 1).choose i : ℝ) * Q ^ (d - i) * x ^ i * m i := by rw [hpow]
    _ ≤ (d.choose i : ℝ) * Q ^ (d - i) * x ^ i * m i := by
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · simp
      · have hmi : 0 ≤ m i := hm i hi0 hid.le
        have hc : ((d - 1).choose i : ℝ) ≤ (d.choose i : ℝ) := by
          exact_mod_cast Nat.choose_le_choose i (Nat.sub_le d 1)
        gcongr

theorem MixedTopAlgebra.proof (hP : PolyNonnegAtZero.Statement) : MixedTopAlgebra.Statement := by
  intro d m hd hm hmd hST
  set P : Polynomial ℝ := ∑ i ∈ Finset.range (d + 1), C ((d.choose i : ℝ) * m i) * X ^ i with hPdef
  have heval : ∀ t : ℝ, P.eval t = ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * m i * t ^ i := by
    intro t; simp [P, eval_finsetSum]
  have h0 : P.eval 0 = m 0 := by
    rw [heval, Finset.sum_eq_single 0]
    · simp
    · intro i _ hi; simp [zero_pow hi]
    · intro h; simp at h
  rw [← h0]
  refine hP d P (m d) hmd ?_ ?_
  · intro t ht hPt
    obtain ⟨p, hp⟩ : ∃ p : ℕ, (p : ℤ) = t.num :=
      ⟨t.num.toNat, Int.toNat_of_nonneg (Rat.num_nonneg.mpr ht.le)⟩
    have hp1 : 1 ≤ p := by
      have : 0 < t.num := Rat.num_pos.mpr ht
      omega
    have hq0 : (0 : ℝ) < (t.den : ℝ) := by exact_mod_cast t.den_pos
    have htq : (t : ℝ) = (p : ℝ) / (t.den : ℝ) := by
      rw [Rat.cast_def, ← hp]; push_cast; rfl
    have hS := MixedTopAlgebra.clear_den d m (t.den : ℝ) (p : ℝ) hq0.ne'
    rw [← htq, ← heval] at hS
    have hSpos : 0 < ∑ i ∈ Finset.range (d + 1),
        (d.choose i : ℝ) * (t.den : ℝ) ^ (d - i) * (p : ℝ) ^ i * m i := by
      rw [← hS]; positivity
    have hT := hST t.den p t.den_pos hp1 hSpos
    have hge := MixedTopAlgebra.sum_ge d m hm (t.den : ℝ) (p : ℝ) hq0.le (by positivity)
    have hqd : (0 : ℝ) < (t.den : ℝ) ^ d := by positivity
    have hmt : (t.den : ℝ) ^ d * (m d * (t : ℝ) ^ d) = (p : ℝ) ^ d * m d := by
      rw [htq, div_pow]; field_simp
    refine le_of_mul_le_mul_left ?_ hqd
    rw [hmt, hS]
    nlinarith [mul_nonneg hq0.le hT]
  · have hlow : ∀ t : ℝ, 0 ≤ t → m 0 + m d * t ^ d ≤ P.eval t := by
      intro t ht
      have hsub : ({0, d} : Finset ℕ) ⊆ Finset.range (d + 1) := by
        intro i hi; simp at hi; simp; omega
      rw [heval]
      calc m 0 + m d * t ^ d = ∑ i ∈ ({0, d} : Finset ℕ), (d.choose i : ℝ) * m i * t ^ i := by
            rw [Finset.sum_pair (by omega)]; simp
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun i hi hi' => by
            have h1 : 1 ≤ i := by simp at hi'; omega
            have := hm i h1 (by simp at hi; omega)
            positivity
    filter_upwards [eventually_ge_atTop (max 1 ((|m 0| + 1) / m d))] with t ht
    have ht1 : 1 ≤ t := le_of_max_le_left ht
    have ht2 : (|m 0| + 1) / m d ≤ t := le_of_max_le_right ht
    have htd : t ≤ t ^ d := by
      calc t = t ^ 1 := (pow_one t).symm
        _ ≤ t ^ d := pow_le_pow_right₀ ht1 (by omega)
    have h3 : |m 0| + 1 ≤ m d * t := by rw [div_le_iff₀ hmd] at ht2; linarith
    have h4 : m d * t ≤ m d * t ^ d := mul_le_mul_of_nonneg_left htd hmd.le
    have h5 := hlow t (by linarith)
    linarith [neg_abs_le (m 0)]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem NoetherProjection.full : GroundTheory.Heights₂.Heights.HilbertSamuel.NoetherProjection.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.NoetherProjection.proof

theorem RootsLiftToZeros.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RootsLiftToZeros.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RootsLiftToZeros.proof

theorem FiniteSeparatingModel.full : GroundTheory.Heights₂.Heights.HilbertSamuel.FiniteSeparatingModel.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.FiniteSeparatingModel.proof NoetherProjection.full RootsLiftToZeros.full

theorem RootsNear.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RootsNear.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RootsNear.proof

theorem RootsBounded.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RootsBounded.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RootsBounded.proof

theorem PolyNonvanishDense.full : GroundTheory.Heights₂.Heights.HilbertSamuel.PolyNonvanishDense.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PolyNonvanishDense.proof

theorem RatPrimeDense.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RatPrimeDense.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RatPrimeDense.proof FiniteSeparatingModel.full RootsNear.full RootsBounded.full PolyNonvanishDense.full

theorem NonvanishingDense.full : GroundTheory.Heights₂.Heights.HilbertSamuel.NonvanishingDense.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.NonvanishingDense.proof RatPrimeDense.full

theorem AnResNullForm.full : GroundTheory.Heights₂.Heights.HilbertSamuel.AnResNullForm.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.AnResNullForm.proof NonvanishingDense.full

theorem BergmanDensChartSum.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BergmanDensChartSum.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BergmanDensChartSum.proof

theorem BergmanDensIntegrable.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BergmanDensIntegrable.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BergmanDensIntegrable.proof

theorem BergmanIntegrable.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BergmanIntegrable.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BergmanIntegrable.proof

theorem HilbFnValueSpan.full : GroundTheory.Heights₂.Heights.HilbertSamuel.HilbFnValueSpan.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.HilbFnValueSpan.proof

theorem BlockBirationalHilbert.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockBirationalHilbert.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockBirationalHilbert.proof HilbFnValueSpan.full

theorem BlockGraphFibreRatio.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockGraphFibreRatio.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockGraphFibreRatio.proof

theorem BlockGraphImage.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockGraphImage.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockGraphImage.proof

theorem BlockImageArith.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageArith.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageArith.proof

theorem EventualPolynomial.full : GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial.proof

theorem MultigradedHilbertPolynomial.full : GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedHilbertPolynomial.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedHilbertPolynomial.proof EventualPolynomial.full

theorem GenericFibreVar.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GenericFibreVar.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GenericFibreVar.proof

theorem Closed.FieldNumbers.HilbEventuallyPoly : GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly.Statement :=
  GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly.full

theorem GenFibreHomog.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GenFibreHomog.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GenFibreHomog.proof

theorem BlockImageHilb.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageHilb.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageHilb.proof

theorem PolySandwich.full : GroundTheory.Heights₂.Heights.HilbertSamuel.PolySandwich.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PolySandwich.proof

theorem BlockImageGenDeg.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageGenDeg.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageGenDeg.proof MultigradedHilbertPolynomial.full GenericFibreVar.full Closed.FieldNumbers.HilbEventuallyPoly GenFibreHomog.full BlockImageHilb.full BlockBirationalHilbert.full PolySandwich.full

theorem BlockImageMetrics.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageMetrics.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageMetrics.proof

theorem PolydiscSubmean.full : GroundTheory.Heights₂.Heights.HilbertSamuel.PolydiscSubmean.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PolydiscSubmean.proof

theorem ChartTaylorCover.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ChartTaylorCover.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ChartTaylorCover.proof

theorem UniformBergmanBound.full : GroundTheory.Heights₂.Heights.HilbertSamuel.UniformBergmanBound.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.UniformBergmanBound.proof PolydiscSubmean.full ChartTaylorCover.full

theorem SupNormAgainstL2.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SupNormAgainstL2.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SupNormAgainstL2.proof UniformBergmanBound.full

theorem ResolutionPullback.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionPullback.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionPullback.proof

theorem SupBoundBlock.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SupBoundBlock.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SupBoundBlock.proof SupNormAgainstL2.full ResolutionPullback.full NonvanishingDense.full

theorem BlockMeasureChange.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockMeasureChange.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockMeasureChange.proof SupBoundBlock.full

theorem BlockResolutionFormsIndependent.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionFormsIndependent.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionFormsIndependent.proof NonvanishingDense.full

theorem BlockResolutionInterpIntegral.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionInterpIntegral.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionInterpIntegral.proof

theorem BlockResolutionMetricPair.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMetricPair.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMetricPair.proof BergmanDensChartSum.full

theorem RankOfSections.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RankOfSections.Statement :=
  GroundTheory.Heights₂.Heights.Swarm.RankOfSections.closed

theorem GenericFibre.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GenericFibre.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GenericFibre.proof

theorem SectionsRank.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SectionsRank.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SectionsRank.proof

theorem BlockSectionsRank.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockSectionsRank.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockSectionsRank.proof RankOfSections.full GenericFibre.full SectionsRank.full BlockImageArith.full BlockImageGenDeg.full

theorem ChartSupBound.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ChartSupBound.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ChartSupBound.proof

theorem GramChiDerivative.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GramChiDerivative.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GramChiDerivative.proof

theorem MetricChange.full : GroundTheory.Heights₂.Heights.HilbertSamuel.MetricChange.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.MetricChange.proof GramChiDerivative.full BergmanIntegrable.full BergmanDensIntegrable.full UniformBergmanBound.full BergmanL1Convergence.full

theorem ResolutionImageSup.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionImageSup.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionImageSup.proof ChartSupBound.full

theorem ResolutionSupBound.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionSupBound.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionSupBound.proof ResolutionImageSup.full NonvanishingDense.full

theorem ProjFrameBasePtFree.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameBasePtFree.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameBasePtFree.proof

theorem ResolutionMetricPair.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMetricPair.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMetricPair.proof BergmanDensChartSum.full

theorem ResolutionFormsIndependent.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionFormsIndependent.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionFormsIndependent.proof NonvanishingDense.full

theorem ConstantShift.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantShift.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantShift.proof

theorem CoordArithOfFnField.full : GroundTheory.Heights₂.Heights.HilbertSamuel.CoordArithOfFnField.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.CoordArithOfFnField.proof

theorem ResolutionInterpIntegral.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionInterpIntegral.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionInterpIntegral.proof

theorem DoubleComplexVanish.full : GroundTheory.Heights₂.Heights.HilbertSamuel.DoubleComplexVanish.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.DoubleComplexVanish.proof

theorem SecEq.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SecEq.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SecEq.proof

theorem Closed.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cond : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.CondStatement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Conductor.proof SecEq.full

theorem RelSectionsLarge.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RelSectionsLarge.Statement :=
  GroundTheory.Heights₂.Heights.Targets.RelSectionsLarge.full

theorem SuccessiveMinimaSpan.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SuccessiveMinimaSpan.Statement :=
  GroundTheory.Heights₂.Heights.Targets.SuccessiveMinimaSpan.of_leaves Closed.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cond RelSectionsLarge.full

theorem SegrePrime.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SegrePrime.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SegrePrime.proof

theorem SegreHilb.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SegreHilb.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SegreHilb.proof

theorem SegreDimGe.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SegreDimGe.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SegreDimGe.proof

theorem MultiDegreePositive.full : GroundTheory.Heights₂.Heights.HilbertSamuel.MultiDegreePositive.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.MultiDegreePositive.proof SegrePrime.full SegreHilb.full SegreDimGe.full

theorem GenDegAmple.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegAmple.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegAmple.proof GenericFibreVar.full MultiDegreePositive.full

theorem GenDegMatAct.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegMatAct.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegMatAct.proof

theorem GenOnFibres.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GenOnFibres.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GenOnFibres.proof

theorem GeneratedRestrict.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedRestrict.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedRestrict.proof

theorem GeneratedEffectiveSection.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedEffectiveSection.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedEffectiveSection.proof

theorem GeneratedProductNonneg.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedProductNonneg.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedProductNonneg.proof GeneratedRestrict.full GeneratedEffectiveSection.full

theorem QuotPartGraded.full : GroundTheory.Heights₂.Heights.HilbertSamuel.QuotPartGraded.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.QuotPartGraded.proof

theorem GenerationOfH1GenAmple.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GenerationOfH1GenAmple.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GenerationOfH1GenAmple.proof QuotPartGraded.full

theorem GenTwistGenerated.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.proof

theorem GeneratedNonzeroSection.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedNonzeroSection.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedNonzeroSection.proof

theorem GradedSubquot.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GradedSubquot.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GradedSubquot.proof

theorem GraphIsometricForms.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometricForms.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometricForms.proof

theorem HyperplaneRegularSection.full : GroundTheory.Heights₂.Heights.HilbertSamuel.HyperplaneRegularSection.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.HyperplaneRegularSection.proof

theorem IntegralAgainstPositive.full : GroundTheory.Heights₂.Heights.HilbertSamuel.IntegralAgainstPositive.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.IntegralAgainstPositive.proof

theorem LiftBirationalAmple.full : GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.proof GeneratedNonzeroSection.full

theorem LocalRep.full : GroundTheory.Heights₂.Heights.HilbertSamuel.LocalRep.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.LocalRep.proof

theorem MetricTransportSmooth.full : GroundTheory.Heights₂.Heights.HilbertSamuel.MetricTransportSmooth.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.MetricTransportSmooth.proof

theorem MixedNumberPolynomial.full : GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.HilbertPositive.mixedNumber

theorem PolyNonnegAtZero.full : GroundTheory.Heights₂.Heights.HilbertSamuel.PolyNonnegAtZero.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PolyNonnegAtZero.proof

theorem MixedTopAlgebra.full : GroundTheory.Heights₂.Heights.HilbertSamuel.MixedTopAlgebra.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.MixedTopAlgebra.proof PolyNonnegAtZero.full

theorem NmSectionsFinite.full : GroundTheory.Heights₂.Heights.HilbertSamuel.NmSectionsFinite.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.NmSectionsFinite.proof Closed.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cond

theorem NmSectionsRankBound.full : GroundTheory.Heights₂.Heights.HilbertSamuel.NmSectionsRankBound.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.NmSectionsRankBound.proof NmSectionsFinite.full SecMRankBound.full

theorem PerturbMonomial.full : GroundTheory.Heights₂.Heights.HilbertSamuel.PerturbMonomial.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PerturbMonomial.proof GenDegAmple.full

theorem PointHeightFS.full : GroundTheory.Heights₂.Heights.HilbertSamuel.PointHeightFS.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PointHeightFS.proof

theorem ProjDegGenDeg.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjDegGenDeg.Statement :=
  GroundTheory.Heights₂.Heights.Swarm.ProjDegGenDeg.proof

theorem ProjFrameFibrePt.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameFibrePt.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameFibrePt.proof

theorem ProjFrameGenPtRel.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameGenPtRel.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameGenPtRel.proof

theorem ProjFrameGenPtTransc.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameGenPtTransc.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameGenPtTransc.proof

theorem TranscRatioDeg.full : GroundTheory.Heights₂.Heights.HilbertSamuel.TranscRatioDeg.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.TranscRatioDeg.proof

theorem RatioFieldDeg.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RatioFieldDeg.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RatioFieldDeg.proof

theorem ProjFrameFibreDeg.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameFibreDeg.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameFibreDeg.proof ProjFrameFibrePt.full ProjFrameGenPtRel.full ProjFrameGenPtTransc.full TranscRatioDeg.full RatioFieldDeg.full

theorem ProjFrameImage.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameImage.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameImage.proof

theorem RatNoetherFrame.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RatNoetherFrame.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RatNoetherFrame.proof

theorem RelLatticeFinite.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RelLatticeFinite.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RelLatticeFinite.proof RelSectionsLarge.full

theorem SectionOrderAtPoint.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SectionOrderAtPoint.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SectionOrderAtPoint.proof

theorem SectionProduct.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SectionProduct.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SectionProduct.proof

theorem SpanStepLocal.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SpanStepLocal.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SpanStepLocal.proof RelLatticeFinite.full

theorem SpanStepHomog.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SpanStepHomog.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SpanStepHomog.proof SpanStepLocal.full

theorem SerreGraded.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded.proof

theorem SectionSpanStep.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SectionSpanStep.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SectionSpanStep.proof SpanStepHomog.full SerreGraded.full

theorem SectionsDimZero.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SectionsDimZero.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SectionsDimZero.proof

theorem ShiftDegreePolynomial.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ShiftDegreePolynomial.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ShiftDegreePolynomial.proof MixedNumberPolynomial.full

theorem ShiftIntersectionPolynomial.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ShiftIntersectionPolynomial.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ShiftIntersectionPolynomial.proof

theorem SmallSectionPointHeight.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionPointHeight.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionPointHeight.proof SectionOrderAtPoint.full

theorem SublatticeDegree.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SublatticeDegree.Statement :=
  GroundTheory.Heights₂.Heights.Targets.SublatticeDegree.full

theorem SupBoundCount.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SupBoundCount.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SupBoundCount.proof

theorem TwoBlockFnField.full : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockFnField.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockFnField.proof

theorem TwoBlockHorizDiv.full : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockHorizDiv.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockHorizDiv.proof

theorem TwoBlockCoeffCycle.full : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockCoeffCycle.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockCoeffCycle.proof CoordArithOfFnField.full TwoBlockFnField.full TwoBlockHorizDiv.full

theorem TwoBlockCycleExpand.full : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockCycleExpand.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockCycleExpand.proof

theorem TwoBlockStepBound.full : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepBound.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepBound.proof RankOfSections.full

theorem VeroneseArith.full : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseArith.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseArith.proof

theorem VeroneseGenDeg.full : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGenDeg.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGenDeg.proof

theorem VeroneseGraphImage.full : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGraphImage.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGraphImage.proof

theorem VeroneseResolution.full : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseResolution.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseResolution.proof

theorem VeroneseSemipos.full : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseSemipos.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseSemipos.proof

theorem ZCombExpand.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ZCombExpand.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ZCombExpand.proof

theorem ZCombLimit.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ZCombLimit.Statement :=
  GroundTheory.Heights₂.Heights.Swarm.ZCombLimit.proof

theorem Closed.ReciprocityTheory.ChartRestriction.G.Geo.FibreFinite : ReciprocityTheory.ChartRestriction.G.Geo.FibreFiniteStatement :=
  ReciprocityTheory.ChartRestriction.G.Geo.fibreFinite

theorem Closed.FieldNumbers.LocalizedQuotientLength : GroundTheory.Heights₂.Heights.FieldNumbers.LocalizedQuotientLength.Statement :=
  GroundTheory.Heights₂.Heights.FieldNumbers.LocalizedQuotientLength.proof

theorem Closed.Inter.regularityLocalFlat_holds : GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds.proof

theorem Closed.Inter.regularityDehomogenization_holds : GroundTheory.Heights₂.Heights.Inter.regularityDehomogenization_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.regularityDehomogenization_holds.proof Closed.FieldNumbers.LocalizedQuotientLength Closed.Inter.regularityLocalFlat_holds

theorem Closed.Inter.LocRingFrac : GroundTheory.Heights₂.Heights.Inter.LocRingFrac.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingFrac.proof

theorem Closed.Inter.LocRingLocal : GroundTheory.Heights₂.Heights.Inter.LocRingLocal.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingLocal.proof Closed.Inter.LocRingFrac

theorem Closed.Inter.LocRingNoeth : GroundTheory.Heights₂.Heights.Inter.LocRingNoeth.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingNoeth.proof Closed.Inter.LocRingFrac

theorem Closed.Inter.LocRingPow : GroundTheory.Heights₂.Heights.Inter.LocRingPow.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingPow.proof

theorem Closed.Inter.regularityLocalDimension_holds : GroundTheory.Heights₂.Heights.Inter.regularityLocalDimension_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.regularityLocalDimension_holds.proof Closed.Inter.LocRingFrac Closed.Inter.LocRingLocal Closed.Inter.LocRingNoeth Closed.Inter.LocRingPow

theorem Closed.Inter.regularityLocalResidue_holds : GroundTheory.Heights₂.Heights.Inter.regularityLocalResidue_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.regularityLocalResidue_holds.proof

theorem Closed.Inter.regularityLocalCardinality_holds : GroundTheory.Heights₂.Heights.Inter.regularityLocalCardinality_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.regularityLocalCardinality_holds.proof Closed.Inter.regularityLocalDimension_holds Closed.Inter.regularityLocalResidue_holds

theorem Closed.PtsSumMeasurable : GroundTheory.Heights₂.Heights.PtsSumMeasurable.Statement :=
  GroundTheory.Heights₂.Heights.PtsSumMeasurable.proof

theorem Closed.Inter.TorusInvLevi : GroundTheory.Heights₂.Heights.Inter.TorusInvLevi.Statement :=
  GroundTheory.Heights₂.Heights.Inter.TorusInvLevi.proof

theorem Closed.Inter.SemiPosTwist : GroundTheory.Heights₂.Heights.Inter.SemiPosTwist.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SemiPosTwist.proof Closed.Inter.TorusInvLevi

theorem Closed.SegrePartition : GroundTheory.Heights₂.Heights.SegrePartition.Statement :=
  GroundTheory.Heights₂.Heights.SegrePartition.proof

theorem Closed.SegreChartDim : GroundTheory.Heights₂.Heights.SegreChartDim.Statement :=
  GroundTheory.Heights₂.Heights.SegreChartDim.proof

theorem Closed.SegreCoordGoodProj : GroundTheory.Heights₂.Heights.SegreCoordGoodProj.Statement :=
  GroundTheory.Heights₂.Heights.SegreCoordGoodProj.proof

theorem Closed.ComplexSets.DiscriminantCover : GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.full

theorem Closed.TubeCollarCompare : GroundTheory.Heights₂.Heights.TubeCollarCompare.Statement :=
  GroundTheory.Heights₂.Heights.TubeCollarCompare.proof

theorem Closed.SheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement :=
  GroundTheory.Heights₂.Heights.SheetImageAreaSet.proof

theorem Closed.ChartMassCompare : GroundTheory.Heights₂.Heights.ChartMassCompare.Statement :=
  GroundTheory.Heights₂.Heights.ChartMassCompare.of_open Closed.SheetImageAreaSet

theorem Closed.MassFinite : GroundTheory.Heights₂.Heights.MassFinite.Statement :=
  GroundTheory.Heights₂.Heights.MassFinite.full

theorem Closed.TubeCollarMass : GroundTheory.Heights₂.Heights.TubeCollarMass.Statement :=
  GroundTheory.Heights₂.Heights.TubeCollarMass.proof Closed.TubeCollarCompare Closed.ChartMassCompare Closed.MassFinite

theorem Closed.TubeDeepWeightMass : GroundTheory.Heights₂.Heights.TubeDeepWeightMass.Statement :=
  GroundTheory.Heights₂.Heights.TubeDeepWeightMass.proof

theorem Closed.ChartMassCompact : GroundTheory.Heights₂.Heights.ChartMassCompact.Statement :=
  GroundTheory.Heights₂.Heights.ChartMassCompact.of_open Closed.SheetImageAreaSet

theorem Closed.Inter.RegCurvBound : GroundTheory.Heights₂.Heights.Inter.RegCurvBound.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegCurvBound.proof Closed.Inter.TorusInvLevi

theorem Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoord : ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoordStatement :=
  GroundTheory.Heights₂.Heights.Targets.ImageCoord.proof

theorem Closed.Inter.BlockRatioAlg : GroundTheory.Heights₂.Heights.Inter.BlockRatioAlg.Statement :=
  GroundTheory.Heights₂.Heights.Inter.BlockRatioAlg.proof

theorem Closed.Inter.BlockGenFinite : GroundTheory.Heights₂.Heights.Inter.BlockGenFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.BlockGenFinite.proof Closed.Inter.BlockRatioAlg

theorem Closed.Inter.FibreIsolFinite : GroundTheory.Heights₂.Heights.Inter.FibreIsolFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.FibreIsolFinite.proof

theorem Closed.Inter.ChartRankAdjoin : GroundTheory.Heights₂.Heights.Inter.ChartRankAdjoin.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ChartRankAdjoin.proof

end GroundTheory.Heights₂.Heights.HilbertSamuel
