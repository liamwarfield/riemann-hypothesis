module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveRegularOffFinite
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimit
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeFormCompare

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

theorem SliceLength.proof (hV : IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.Statement)
    (hR : SliceReducedGeneral.Statement) (hM : SliceMultGeneral.Statement) :
    SliceLength.Statement := by
  intro n d J W u hJ hdim hu hW
  have hWp : W.IsPrime := hW.1.1
  obtain ⟨f₁, hf₁W, hf₁⟩ := hR n d J W u hJ hdim hu hW
  obtain ⟨f₂, hf₂W, hf₂⟩ := hM n d J W u hJ hdim hu hW
  have hf : f₁ * f₂ ∉ W := fun h => (hWp.mem_or_mem h).elim hf₁W hf₂W
  have hUo : IsOpen {x : Fin n → ℂ | eval x (f₁ * f₂) ≠ 0} :=
    isOpen_ne_fun (MvPolynomial.continuous_eval (p := f₁ * f₂)) continuous_const
  refine ⟨{x | eval x (f₁ * f₂) ≠ 0}, hUo, ?_, ?_⟩
  ·
    intro x hx
    rw [mem_closure_iff_nhds]
    intro t ht
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    apply hf
    refine hV n W (f₁ * f₂) x hWp hx ?_
    filter_upwards [ht] with y hyt hyW
    by_contra hne
    have hy : y ∈ t ∩ (zeroSet W ∩ {x | eval x (f₁ * f₂) ≠ 0}) := ⟨hyt, hyW, hne⟩
    rw [hempty] at hy
    exact hy
  ·
    rintro q ⟨hqW, hqf⟩
    rw [Set.mem_ofPred_eq, map_mul, mul_ne_zero_iff] at hqf
    obtain ⟨O₁, hO₁o, hO₁d, hO₁⟩ := hf₁ q hqW hqf.1
    obtain ⟨O₂, -, hO₂d, hO₂⟩ := hf₂ q hqW hqf.2
    exact (hO₁d.inter_of_isOpen_left hO₂d hO₁o).mono fun L (hL : L ∈ O₁ ∩ O₂) => ⟨hO₁ L hL.1, hO₂ L hL.2⟩

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitGoodPoints
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem LelongLimitGoodPoints.proof (hBr : DivisorGeneralPointBranches.Statement)
    (hLim : LelongLimitAtBranches.Statement) (hOrd : LocalOrder.Statement) :
    LelongLimitGoodPoints.Statement := by
  classical
  intro n d J u φ hJ hdim hu hφ
  obtain ⟨I, hI, hIdim, hgood⟩ := hBr n d J u hJ hdim hu
  refine ⟨I, hI, hIdim, fun q hqJ hqu hqI => ?_⟩
  obtain ⟨W, hWm, hqW, hone, hWloc, m, γ, ord, π, hcov, hsl, hmeet, hvan, hbij⟩ :=
    hgood q hqJ hqu hqI
  obtain ⟨N, hN, hlim⟩ :=
    hLim n d J W u q m γ ord π φ hJ hdim hu hWm hqW hφ hWloc hcov hsl hmeet hvan hbij
  have hmult := hOrd n d J W u q m γ ord hJ hdim hu hWm hqW hcov hsl hmeet hvan
  have hclosed : ∀ W' : Ideal (MvPolynomial (Fin n) ℂ), IsClosed (zeroSet W') := fun W' => by
    have : zeroSet W' = ⋂ p ∈ W', {x : Fin n → ℂ | MvPolynomial.eval x p = 0} := by
      ext x; simp [zeroSet]
    rw [this]
    exact isClosed_biInter fun p _ => isClosed_eq (MvPolynomial.continuous_eval p) continuous_const

  set O := ⋂ W' ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes \ {W}, (zeroSet W')ᶜ
  have hO : O ∈ 𝓝 q :=
    (Filter.biInter_mem
      ((Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).sdiff)).2 fun W' hW' =>
      (hclosed W').isOpen_compl.mem_nhds fun h => hW'.2 (hone W' hW'.1 h)
  refine ⟨N ∩ O, Filter.inter_mem hN hO, fun f hf hfc hfN => ?_⟩
  have hL : (∑ᶠ (W' : Ideal (MvPolynomial (Fin n) ℂ))
      (_ : W' ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
      (localMult (J ⊔ Ideal.span {linForm u}) W' : ℝ) * varInt W' d f φ) =
      (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d f φ := by
    rw [finsum_eq_single _ W fun W' hne => ?_, finsum_eq_dif, dite_eq_left hWm]
    rw [finsum_eq_dif]
    split_ifs with hW'
    · rw [varInt_eq_zero_of_vanish W' f φ fun x hx => image_eq_zero_of_notMem_tsupport fun hxs =>
        Set.mem_iInter₂.1 (hfN hxs).2 W' ⟨hW', hne⟩ hx, mul_zero]
    · rfl
  rw [hL, hmult]
  exact hlim f hf hfc fun x hx => (hfN hx).1

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitAtBranches
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem LelongLimitAtBranches.proof (hDec : BranchIntDecompose.Statement) (hSl : SliceBranchInt.Statement)
    (hLim : PolydiscLelongLimit.Statement) (hPr : IndefiniteRowSideFullHecke.ComplexSets.BranchProperAtPoint.Statement) :
    LelongLimitAtBranches.Statement := by
  intro n d J W u q m γ ord π φ hJ hdim hu hW hq hφ hzW hcov hsl hdisj hord _
  obtain ⟨NA, hNA, hA⟩ := hDec n d J u q m γ ord hJ hdim hu hcov hdisj hord
  obtain ⟨NB, hNB, hB⟩ := hSl n d J W u q m γ ord hJ hdim hu hW hq hzW hcov hsl hdisj hord
  have hpr : ∀ b, ∃ e > 0, ∀ τ ∈ Metric.ball 0 (γ b).radius, (γ b).toFun τ ∈ Metric.ball q e →
      τ ∈ Metric.ball 0 ((γ b).radius / 2) := fun b =>
    hPr n (d + 1) J u q q m γ hJ hdim hu hcov hdisj b 0 (Metric.mem_ball_self (γ b).radius_pos)
      (γ b).map_zero _ (Metric.ball_mem_nhds _ (half_pos (γ b).radius_pos))
  choose e he hpe using hpr
  refine ⟨NA ∩ NB ∩ ⋂ b, Metric.ball q (e b), inter_mem (inter_mem hNA hNB)
    (iInter_mem.2 fun b => Metric.ball_mem_nhds q (he b)), fun f hf hfc hfN => ?_⟩
  have hcons : ∀ (g : (Fin n → ℂ) → ℝ) (b : Fin m), (fun k => vecCons g φ k ∘ (γ b).toFun) =
      vecCons (g ∘ (γ b).toFun) fun k => φ k ∘ (γ b).toFun := fun g b => by
    funext k; refine Fin.cases ?_ (fun j => ?_) k <;> simp
  have hsum : (fun ε => ∑ b, ReciprocityTheory.AnForm.maInt
      (vecCons (fun τ => Real.log (‖linEval u ((γ b).toFun τ)‖ ^ 2 + ε) / 2) fun k => φ k ∘ (γ b).toFun)
      (f ∘ (γ b).toFun) (Metric.ball 0 (γ b).radius)) =ᶠ[𝓝[>] 0]
      fun ε => varInt J (d + 1) f (vecCons (logReg u ε) φ) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [hA f _ hf hfc (hfN.trans (Set.inter_subset_left.trans Set.inter_subset_left))
      (fun i => Fin.cases ⟨Set.univ, isOpen_univ, Set.subset_univ _, (contDiff_logReg u hε).contDiffOn⟩
        (fun j => hφ j) i)]
    exact Finset.sum_congr rfl fun b _ => by rw [hcons]; rfl
  refine Tendsto.congr' hsum ?_
  have hlim : ∀ b, Tendsto (fun ε => ReciprocityTheory.AnForm.maInt
      (vecCons (fun τ => Real.log (‖linEval u ((γ b).toFun τ)‖ ^ 2 + ε) / 2) fun k => φ k ∘ (γ b).toFun)
      (f ∘ (γ b).toFun) (Metric.ball 0 (γ b).radius)) (𝓝[>] 0) (𝓝 ((ord b : ℝ) * varInt W d f φ)) := by
    intro b
    have han : AnalyticOnNhd ℂ (γ b).toFun (Metric.ball 0 (γ b).radius) := fun w hw =>
      AnalyticAt.pi fun i => ReciprocityTheory.AnForm.Osgood.osgood (d + 1) _ (fun z => (γ b).toFun z i)
        Metric.isOpen_ball (differentiableOn_pi.1 (γ b).differentiableOn i) w hw
    have hγ : ContDiffOn ℝ ∞ (γ b).toFun (Metric.ball 0 (γ b).radius) :=
      (han.contDiffOn_of_completeSpace (n := ∞)).restrict_scalars ℝ
    rw [hB b f φ hf hfc (hfN.trans (Set.inter_subset_left.trans Set.inter_subset_right)) hφ]
    refine hLim d (ord b) (γ b).radius ((γ b).radius / 2) _ (f ∘ (γ b).toFun) _
      (half_lt_self (γ b).radius_pos) (hord b) (hf.comp_contDiffOn hγ) (fun τ hτ hne => hpe b τ hτ ?_)
      (fun k => ?_)
    · exact Set.mem_iInter.1 (Set.inter_subset_right (hfN (subset_tsupport f hne))) b
    · obtain ⟨U, hU, hsub, hφU⟩ := hφ k
      exact hφU.comp hγ fun τ hτ => hsub ((γ b).mapsTo hτ)
  have := tendsto_finsetSum Finset.univ fun b _ => hlim b
  convert this using 2
  push_cast
  rw [Finset.sum_mul]

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetComass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder

noncomputable section

namespace SheetComassAlt

theorem sheetJac_eq_norm_det {n d : ℕ} (s : (Fin d → ℂ) → Fin n → ℂ) (y : Fin d → ℂ)
    (hs : DifferentiableAt ℂ s y) :
    sheetJac s y = ‖((ReciprocityTheory.AnForm.A.jacC s y)ᴴ * ReciprocityTheory.AnForm.A.jacC s y).det‖ := by
  set S : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm.toLinearMap ∘ₗ
      ((fderiv ℂ s y : (Fin d → ℂ) →L[ℂ] (Fin n → ℂ)) : (Fin d → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ
        (WithLp.linearEquiv 2 ℂ (Fin d → ℂ)).toLinearMap with hS
  have hR : fderiv ℝ s y = (fderiv ℂ s y).restrictScalars ℝ := hs.fderiv_restrictScalars ℝ
  have e : (WithLp.linearEquiv 2 ℝ (Fin n → ℂ)).symm.toLinearMap ∘ₗ
      ((fderiv ℝ s y : (Fin d → ℂ) →L[ℝ] (Fin n → ℂ)) : (Fin d → ℂ) →ₗ[ℝ] (Fin n → ℂ)) ∘ₗ
        (WithLp.linearEquiv 2 ℝ (Fin d → ℂ)).toLinearMap = S.restrictScalars ℝ := by
    ext v : 1
    simp [hS, hR]
  rw [sheetJac, e, FrameJacobianSumAlt.areaJacobian_restrictScalars,
    FrameJacobianSumAlt.det_adjoint_comp]
  congr 2
  ext i j
  simp [hS, Matrix.mul_apply, ReciprocityTheory.AnForm.A.jacC, PiLp.inner_apply, mul_comm]

end SheetComassAlt

theorem SheetComass.proof : SheetComass.Statement := by
  intro n d J A φ R hφ
  choose U hUo hZU hφU using hφ
  have hK : IsCompact (zeroSet J ∩ Metric.closedBall (0 : Fin n → ℂ) R) :=
    (isCompact_closedBall (0 : Fin n → ℂ) R).inter_left (SheetSumMeasurable.isClosed_zeroSet J)
  obtain ⟨c, hc, hb⟩ := TubeFormComparison.exists_hessC_bound φ _ hK U hUo
    (fun i => Set.inter_subset_left.trans (hZU i))
    (fun i => (hφU i).of_le (WithTop.coe_le_coe.2 le_top))
  refine ⟨(d.factorial : ℝ) * (2 / Real.pi) ^ d * (3 ^ d * c ^ d), fun x hx s hs => ?_⟩
  obtain ⟨V, hV, hyV, hsd, hsx, -, -⟩ := hs
  have hsa : AnalyticAt ℂ s (A *ᵥ x) :=
    IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn hV hsd _ hyV
  have hφx : ∀ i, ContDiffAt ℝ 2 (φ i) (s (A *ᵥ x)) := fun i => by
    rw [hsx]
    exact ((hφU i).contDiffAt ((hUo i).mem_nhds (hZU i hx.1))).of_le (WithTop.coe_le_coe.2 le_top)
  set Jc := ReciprocityTheory.AnForm.A.jacC s (A *ᵥ x) with hJc
  set B := Jc.map (starRingEnd ℂ) with hB
  have hBJ : Bᴴ = Jcᵀ := by
    ext a b
    simp [hB]
  have hA : ∀ i, hessC (φ i ∘ s) (A *ᵥ x) = Bᴴ * hessC (φ i) x * B := fun i => by
    have h := ReciprocityTheory.AnForm.A.hessC_comp (φ i) s _ hsa (hφx i)
    rw [hsx] at h
    rw [hBJ]
    exact h
  have hle : ∀ k, ((fun _ : Fin d => (c : ℂ) • (Bᴴ * B)) k -
      (fun k => hessC (φ k ∘ s) (A *ᵥ x)) k).PosSemidef := fun k => by
    have e : (c : ℂ) • (Bᴴ * B) - Bᴴ * hessC (φ k) x * B =
        Bᴴ * (-hessC (φ k) x + (c : ℂ) • 1) * B := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      abel
    simp only [hA, e]
    exact (hb k x hx).2.conjTranspose_mul_mul_same B
  have hge : ∀ k, ((fun k => hessC (φ k ∘ s) (A *ᵥ x)) k +
      (fun _ : Fin d => (c : ℂ) • (Bᴴ * B)) k).PosSemidef := fun k => by
    have e : Bᴴ * hessC (φ k) x * B + (c : ℂ) • (Bᴴ * B) =
        Bᴴ * (hessC (φ k) x + (c : ℂ) • 1) * B := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    simp only [hA, e]
    exact (hb k x hx).1.conjTranspose_mul_mul_same B
  have key := ReciprocityTheory.AnForm.A.norm_mdisc_le_of_abs_le _ _ hle hge
  rw [ReciprocityTheory.AnForm.A.mdisc_const, Matrix.det_smul, Fintype.card_fin] at key
  have hconj : Bᴴ * B = (Jcᴴ * Jc).map (starRingEnd ℂ) := by
    rw [hBJ, hB]
    ext i j
    simp [Matrix.mul_apply, mul_comm]
  have hdet : ‖(Bᴴ * B).det‖ = sheetJac s (A *ᵥ x) := by
    have hm : ((Jcᴴ * Jc).map (starRingEnd ℂ)).det = starRingEnd ℂ (Jcᴴ * Jc).det :=
      (RingHom.map_det _ _).symm
    rw [SheetComassAlt.sheetJac_eq_norm_det s _ (hsd.differentiableAt (hV.mem_nhds hyV)), hconj, hm,
      Complex.norm_conj]
  have hre : (((c : ℂ) ^ d * (Bᴴ * B).det).re) ≤ c ^ d * sheetJac s (A *ᵥ x) := by
    refine (Complex.re_le_norm _).trans (le_of_eq ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hc, hdet]
  have hm : |(mdisc fun k => hessC (φ k ∘ s) (A *ᵥ x)).re| ≤ 3 ^ d * (c ^ d * sheetJac s (A *ᵥ x)) :=
    (Complex.abs_re_le_norm _).trans (key.trans (mul_le_mul_of_nonneg_left hre (by positivity)))
  unfold maDens
  rw [abs_mul, abs_of_nonneg (by positivity), mul_assoc _ (3 ^ d * c ^ d), mul_assoc (3 ^ d)]
  exact mul_le_mul_of_nonneg_left hm (by positivity)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegBallMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

namespace RegBallMass

variable {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (d + 1)) (Fin n) ℂ}

theorem chartDens_indicator_mono (hN : RegDensNonneg.Statement) (hA : IsFiniteProjection J A)
    (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) {S S' : Set (Fin n → ℂ)} (hS : S ⊆ S') (y : Fin (d + 1) → ℂ) :
    0 ≤ chartDens J A (S.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot) y ∧
      chartDens J A (S.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot) y ≤
        chartDens J A (S'.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot) y := by
  have hfin : (ComplexSets.fibre J A y).Finite := FiniteProjectionCluster.fibre_finite J A hA y
  have key : ∀ x ∈ ComplexSets.fibre J A y, ∀ h : ∃ s, IsSheetAt J A x s,
      0 ≤ ReciprocityTheory.AnForm.maDens (fun k => (vecCons (logReg u ε) fun _ => euclPot :
        Fin (d + 1) → (Fin n → ℂ) → ℝ) k ∘ h.choose) y := by
    intro x hx h
    have := hN n d J A u ε x h.choose hε h.choose_spec
    rwa [hx.2] at this
  unfold chartDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  constructor
  · refine Finset.sum_nonneg fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    split_ifs with h
    · exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (key x hx h)
    · exact le_rfl
  · refine Finset.sum_le_sum fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    split_ifs with h
    · exact mul_le_mul_of_nonneg_right
        (Set.indicator_le_indicator_of_subset hS (fun _ => zero_le_one) x) (key x hx h)
    · exact le_rfl

theorem measurable_chartDens_indicator (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ)) (hA : IsFiniteProjection J A)
    (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) {S : Set (Fin n → ℂ)} (hS : MeasurableSet S) :
    Measurable (chartDens J A (S.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot)) := by
  refine (SheetSumMeasurable.proof n (d + 1) J A _ _ hJ hdim hA (measurable_const.indicator hS)
    fun k => ?_).1
  refine Fin.cases ?_ (fun i => ?_) k
  · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_logReg u hε)
  · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_euclPot n)

end RegBallMass


open RegBallMass in
theorem RegBallMass.proof (hF : RegFixedBallMass.Statement) (hM : RegLelongMono.Statement)
    (hN : RegDensNonneg.Statement) : RegBallMass.Statement := by
  intro n d J A u K hJ hdim hA hu hK
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.exists_norm_le
  set c : ℝ := Real.sqrt (n + 1) with hc
  have hc0 : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hc2 : c ^ 2 = n + 1 := Real.sq_sqrt (by positivity)
  obtain ⟨M, hMb⟩ := hF n d J A u (R₀ + c) hJ hdim hA hu
  refine ⟨max M 0, le_max_right _ _, fun ε hε x hx r hr => ?_⟩
  set F : Set (Fin n → ℂ) → (Fin (d + 1) → ℂ) → ℝ := fun S =>
    chartDens J A (S.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot) with hFdef
  have h1 : Metric.ball x r ⊆ euclBall x (c * r) := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hr.1] at hy
    show Real.sqrt (euclPot (y - x)) < c * r
    rw [Real.sqrt_lt' (mul_pos hc0 hr.1), mul_pow, hc2]
    calc euclPot (y - x) = ∑ j, ‖(y - x) j‖ ^ 2 := rfl
      _ ≤ ∑ _j : Fin n, r ^ 2 :=
        Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hy j).le 2
      _ = n * r ^ 2 := by simp
      _ < (n + 1) * r ^ 2 := by nlinarith [pow_pos hr.1 2]
  have h2 : euclBall x c ⊆ Metric.closedBall 0 (R₀ + c) := by
    intro y hy
    have hy' : euclPot (y - x) < c ^ 2 := (Real.sqrt_lt' hc0).1 hy
    rw [Metric.mem_closedBall, dist_zero_right]
    have hyx : ‖y - x‖ ≤ c := by
      refine (pi_norm_le_iff_of_nonneg hc0.le).2 fun j => ?_
      have hj : ‖(y - x) j‖ ^ 2 ≤ euclPot (y - x) :=
        Finset.single_le_sum (f := fun j => ‖(y - x) j‖ ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ j)
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hc0.le two_ne_zero).1 (by linarith)
    calc ‖y‖ = ‖x + (y - x)‖ := by rw [add_sub_cancel]
      _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
      _ ≤ R₀ + c := add_le_add (hR₀ x hx) hyx
  have h3 : euclBall x (c * r) ⊆ euclBall x c := fun y hy =>
    show Real.sqrt (euclPot (y - x)) < c from
      lt_of_lt_of_le (show Real.sqrt (euclPot (y - x)) < c * r from hy)
        (mul_le_of_le_one_right hc0.le hr.2)
  have hpos : ∀ {S S' : Set (Fin n → ℂ)}, S ⊆ S' → ∀ y, 0 ≤ F S y ∧ F S y ≤ F S' y :=
    fun hS y => chartDens_indicator_mono hN hA u hε.1 hS y
  have hEm : ∀ ρ, MeasurableSet (euclBall x ρ) := fun ρ =>
    (isOpen_lt (((contDiff_euclPot n).continuous.comp
      (continuous_id.sub continuous_const)).sqrt) continuous_const).measurableSet
  obtain ⟨hIR, hIRle⟩ := hMb ε hε
  have hint : ∀ S, MeasurableSet S → S ⊆ Metric.closedBall 0 (R₀ + c) → Integrable (F S) :=
    fun S hS hSR => hIR.mono' (measurable_chartDens_indicator hJ hdim hA u hε.1 hS).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hpos hSR y).1]; exact (hpos hSR y).2)
  have hBI := hint _ Metric.isOpen_ball.measurableSet (h1.trans (h3.trans h2))
  refine ⟨hBI, ?_⟩
  have hmono := hM n d J A u ε x (c * r) c hJ hdim hA hε.1 (mul_pos hc0 hr.1)
    (mul_le_of_le_one_right hc0.le hr.2)
  have hI1 : ∫ y, F (Metric.ball x r) y ≤ ∫ y, F (euclBall x (c * r)) y :=
    integral_mono hBI (hint _ (hEm _) (h3.trans h2)) fun y => (hpos h1 y).2
  have hI2 : ∫ y, F (euclBall x c) y ≤ ∫ y, F (Metric.closedBall 0 (R₀ + c)) y :=
    integral_mono (hint _ (hEm _) h2) hIR fun y => (hpos h2 y).2
  have hI3 : ∫ y, F (euclBall x (c * r)) y ≤ r ^ (2 * d) * ∫ y, F (euclBall x c) y := by
    have : c ^ (2 * d) * ∫ y, F (euclBall x (c * r)) y ≤
        c ^ (2 * d) * (r ^ (2 * d) * ∫ y, F (euclBall x c) y) := by
      rw [← mul_assoc, ← mul_pow]; exact hmono
    exact le_of_mul_le_mul_left this (pow_pos hc0 _)
  calc ∫ y, F (Metric.ball x r) y ≤ r ^ (2 * d) * ∫ y, F (euclBall x c) y := hI1.trans hI3
    _ ≤ r ^ (2 * d) * max M 0 :=
      mul_le_mul_of_nonneg_left (hI2.trans (hIRle.trans (le_max_left _ _))) (pow_nonneg hr.1.le _)
    _ = max M 0 * r ^ (2 * d) := mul_comm _ _

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitOffZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm
open scoped ContDiff

theorem hessC_half_log_normSq_add {D : ℕ} (h : (Fin D → ℂ) → ℂ) (y : Fin D → ℂ)
    (hh : AnalyticAt ℂ h y) (hy : h y ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    hessC (fun w => Real.log (‖h w‖ ^ 2 + ε) / 2) y =
      ((ε / (2 * (‖h y‖ ^ 2 + ε) ^ 2) : ℝ) : ℂ) • hessC (fun w => ‖h w‖ ^ 2) y := by
  set L : (Fin D → ℂ) → ℝ := fun w => Real.log ‖h w‖ with hLdef
  set F : ℝ → ℝ := fun t => Real.log (Real.exp (2 * t) + ε) / 2 with hFdef
  set G : ℝ → ℝ := fun t => Real.exp (2 * t) with hGdef
  have hhc : ContDiffAt ℝ 2 h y := (hh.contDiffAt (n := 2)).restrict_scalars ℝ
  have hLc : ContDiffAt ℝ 2 L y := (hhc.norm ℝ hy).log (norm_ne_zero_iff.2 hy)
  have hL0 : hessC L y = 0 := ReciprocityTheory.AnForm.A.hessC_log_norm h y hh hy
  have he : ∀ t, HasDerivAt (fun t : ℝ => Real.exp (2 * t)) (Real.exp (2 * t) * 2) t := fun t => by
    simpa using ((hasDerivAt_id t).const_mul 2).exp
  have hFc : ContDiff ℝ 2 F :=
    ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).add contDiff_const).log
      (fun t => by simp only [Function.comp_apply, id]; positivity) |>.div_const 2
  have hGc : ContDiff ℝ 2 G := Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hF := HessCCompPluri.proof D F L y hFc.contDiffAt hLc hL0
  have hG := HessCCompPluri.proof D G L y hGc.contDiffAt hLc hL0
  have hdF : deriv F = fun t => Real.exp (2 * t) / (Real.exp (2 * t) + ε) := by
    funext t
    have hp : Real.exp (2 * t) + ε ≠ 0 := by positivity
    refine (((he t).add_const ε).log hp |>.div_const 2).deriv.trans ?_
    field_simp
  have hddF : ∀ t, deriv (deriv F) t = 2 * ε * Real.exp (2 * t) / (Real.exp (2 * t) + ε) ^ 2 := by
    intro t
    have hp : Real.exp (2 * t) + ε ≠ 0 := by positivity
    rw [hdF]
    refine ((he t).div ((he t).add_const ε) hp).deriv.trans ?_
    field_simp
    ring
  have hdG : deriv G = fun t => Real.exp (2 * t) * 2 := funext fun t => (he t).deriv
  have hddG : ∀ t, deriv (deriv G) t = Real.exp (2 * t) * 2 * 2 := fun t => by
    rw [hdG]
    exact ((he t).mul_const 2).deriv
  have hexp : ∀ w, h w ≠ 0 → Real.exp (2 * L w) = ‖h w‖ ^ 2 := fun w hw => by
    rw [hLdef, show 2 * Real.log ‖h w‖ = Real.log (‖h w‖ ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
  have hev : ∀ᶠ w in 𝓝 y, h w ≠ 0 := hh.continuousAt.eventually_ne hy
  have eF : hessC (fun w => Real.log (‖h w‖ ^ 2 + ε) / 2) y = hessC (fun w => F (L w)) y :=
    ReciprocityTheory.AnForm.A.hessC_congr' (hev.mono fun w hw => by simp only [hFdef, hexp w hw])
  have eG : hessC (fun w => ‖h w‖ ^ 2) y = hessC (fun w => G (L w)) y :=
    ReciprocityTheory.AnForm.A.hessC_congr' (hev.mono fun w hw => by simp only [hGdef, hexp w hw])
  rw [eF, eG, hF, hG, hddF, hddG, hexp y hy, smul_smul]
  congr 1
  have ha : 0 < ‖h y‖ ^ 2 := by positivity
  push_cast
  field_simp

theorem LelongLimitOffZero.proof (hM : ChartMassCompact.Statement) : LelongLimitOffZero.Statement := by
  classical
  intro n d J u f φ hJ hdim hu hf hfc hφ hdisj
  unfold varInt
  split_ifs with hA
  swap
  · exact tendsto_const_nhds
  set A := hA.choose with hAdef
  have hAf : IsFiniteProjection J A := hA.choose_spec
  have hZc : IsClosed (zeroSet J) := by
    have : zeroSet J = ⋂ q ∈ J, {x : Fin n → ℂ | MvPolynomial.eval x q = 0} := by
      ext x; simp [zeroSet]
    rw [this]
    exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
  have hK : IsCompact (tsupport f ∩ zeroSet J) := hfc.isCompact.inter_right hZc
  have hu0 : ∀ x ∈ tsupport f ∩ zeroSet J, linEval u x ≠ 0 := fun x hx h0 =>
    Set.disjoint_left.1 hdisj hx.1 ⟨hx.2, h0⟩
  set q : (Fin n → ℂ) → ℝ := fun x => ‖linEval u x‖ ^ 2 with hq
  have hqc : ContDiff ℝ ∞ q := (contDiff_norm_sq ℝ).comp (contDiff_linEval u)
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ tsupport f ∩ zeroSet J, m ≤ q x := by
    rcases (tsupport f ∩ zeroSet J).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne hqc.continuous.continuousOn
      exact ⟨q x₀, by have := hu0 x₀ hx₀; simp only [hq]; positivity, fun x hx => hmin hx⟩
  have hGi : Integrable (chartAbsDens J A f (vecCons q φ)) := by
    refine hM n (d + 1) J A f _ hJ hdim hAf hf.continuous.continuousOn (fun i => ?_) (Or.inl hfc)
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using smoothNear_of_contDiff (S := zeroSet J) hqc
    · simpa using hφ j
  have hb : ∀ ε : ℝ, 0 < ε → ∀ y, ‖chartDens J A f (vecCons (logReg u ε) φ) y‖ ≤
      ε / (2 * m ^ 2) * chartAbsDens J A f (vecCons q φ) y := by
    intro ε hε y
    rw [Real.norm_eq_abs]
    refine (abs_chartDens_le J A f _ y).trans ?_
    have hfin := (FibreBound.proof n (d + 1) J A hJ hdim hAf y).2.1
    unfold chartAbsDens
    refine sheetSum_le_mul hfin _ _ _ fun x hx s hs => ?_
    by_cases hfx : f x = 0
    · simp [hfx]
    have hxK : x ∈ tsupport f ∩ zeroSet J := ⟨subset_tsupport _ hfx, hx.1⟩
    obtain rfl : A *ᵥ x = y := hx.2
    obtain ⟨U, hU, hxU, hsd, hsx, -, -⟩ := hs
    have hsa : AnalyticAt ℂ s (A *ᵥ x) := analyticAt_pi_iff.2 fun i =>
      ReciprocityTheory.AnForm.Osgood.osgood _ U (fun z => s z i) hU (differentiableOn_pi.1 hsd i) _ hxU
    have hha : AnalyticAt ℂ (fun w => linEval u (s w)) (A *ᵥ x) := by
      unfold linEval
      exact Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul ((analyticAt_pi_iff.1 hsa) j)
    have hne : linEval u (s (A *ᵥ x)) ≠ 0 := by rw [hsx]; exact hu0 x hxK
    have hH0 := hessC_half_log_normSq_add (fun w => linEval u (s w)) _ hha hne hε
    simp only [hsx] at hH0
    have hH : hessC (logReg u ε ∘ s) (A *ᵥ x) =
        ((ε / (2 * (q x + ε) ^ 2) : ℝ) : ℂ) • hessC (q ∘ s) (A *ᵥ x) := hH0
    rw [vecCons_comp, vecCons_comp, maDens_cons_of_hessC_eq_smul (logReg u ε ∘ s) (q ∘ s) _ _ _ hH]
    have ha : m ≤ q x := hm x hxK
    have hc0 : 0 ≤ ε / (2 * (q x + ε) ^ 2) := by positivity
    have hc : ε / (2 * (q x + ε) ^ 2) ≤ ε / (2 * m ^ 2) :=
      div_le_div_of_nonneg_left hε.le (by positivity) (by nlinarith)
    calc |f x * (ε / (2 * (q x + ε) ^ 2) * maDens (Fin.cons (q ∘ s) fun k => φ k ∘ s) (A *ᵥ x))|
        = ε / (2 * (q x + ε) ^ 2) * |f x * maDens (Fin.cons (q ∘ s) fun k => φ k ∘ s) (A *ᵥ x)| := by
          rw [mul_left_comm, abs_mul, abs_of_nonneg hc0]
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
  have hlim : Tendsto (fun ε : ℝ => ε / (2 * m ^ 2) * ∫ y, chartAbsDens J A f (vecCons q φ) y)
      (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ => ε / (2 * m ^ 2) * ∫ y, chartAbsDens J A f (vecCons q φ) y) := by
      fun_prop
    exact tendsto_nhdsWithin_of_tendsto_nhds (hc.tendsto' 0 0 (by simp))
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  unfold chartInt
  rw [← integral_const_mul]
  exact norm_integral_le_of_norm_le (hGi.const_mul _) (Eventually.of_forall (hb ε hε))

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChartIntCountAdd
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace ChartIntCountAdd

variable {n d : ℕ}

theorem hasSum_indicator {E : ℕ → Set (Fin n → ℂ)} (hE : Pairwise (Function.onFun Disjoint E))
    (g : (Fin n → ℂ) → ℝ) (x : Fin n → ℂ) :
    HasSum (fun i => (E i).indicator g x) ((⋃ i, E i).indicator g x) := by
  by_cases hx : x ∈ ⋃ i, E i
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
    have hval : (⋃ i, E i).indicator g x = (E j).indicator g x := by
      simp [Set.indicator_of_mem hx, Set.indicator_of_mem hj]
    rw [hval]
    refine hasSum_single j fun i hi => ?_
    have hxi : x ∉ E i := fun hxi => Set.disjoint_left.1 (hE hi) hxi hj
    simp [hxi]
  · have h0 : ∀ i, (E i).indicator g x = 0 := fun i => by
      have hxi : x ∉ E i := fun h => hx (Set.mem_iUnion.2 ⟨i, h⟩)
      simp [hxi]
    have hu : (⋃ i, E i).indicator g x = 0 := by simp only [Set.indicator_of_notMem hx]
    simp only [h0, hu]
    exact hasSum_zero


open Classical in
theorem sheetSum_eq_sum {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {y : Fin d → ℂ}
    (hfin : (ComplexSets.fibre J A y).Finite) (F : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) :
    sheetSum J A F y =
      ∑ x ∈ hfin.toFinset, (if h : ∃ s, IsSheetAt J A x s then F x h.choose else 0) := by
  unfold sheetSum
  exact finsum_mem_eq_finite_toFinset_sum _ hfin

theorem hasSum_sheetSum {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {y : Fin d → ℂ}
    (hfin : (ComplexSets.fibre J A y).Finite) (F : ℕ → (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ)
    (G : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) (hF : ∀ x s, HasSum (fun i => F i x s) (G x s)) :
    HasSum (fun i => sheetSum J A (F i) y) (sheetSum J A G y) := by
  classical
  simp only [sheetSum_eq_sum hfin]
  refine hasSum_sum fun x _ => ?_
  by_cases h : ∃ s, IsSheetAt J A x s
  · simp only [dif_pos h]; exact hF x _
  · simp only [dif_neg h]; exact hasSum_zero

theorem abs_sheetSum_le {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {y : Fin d → ℂ}
    (hfin : (ComplexSets.fibre J A y).Finite) (F : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) :
    |sheetSum J A F y| ≤ sheetSum J A (fun x s => |F x s|) y := by
  classical
  rw [sheetSum_eq_sum hfin, sheetSum_eq_sum hfin]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  by_cases h : ∃ s, IsSheetAt J A x s
  · simp only [dif_pos h, le_refl]
  · simp only [dif_neg h, abs_zero, le_refl]

theorem sheetSum_mono {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {y : Fin d → ℂ}
    (hfin : (ComplexSets.fibre J A y).Finite) {F G : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ}
    (hFG : ∀ x s, F x s ≤ G x s) : sheetSum J A F y ≤ sheetSum J A G y := by
  classical
  rw [sheetSum_eq_sum hfin, sheetSum_eq_sum hfin]
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases h : ∃ s, IsSheetAt J A x s
  · simp only [dif_pos h]; exact hFG x _
  · simp only [dif_neg h, le_refl]

theorem indicator_mul (S : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℝ) (x : Fin n → ℂ) (c : ℝ) :
    S.indicator f x * c = S.indicator (fun z => f z * c) x := by
  by_cases hx : x ∈ S <;> simp [hx]

theorem abs_indicator_mul (S : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℝ) (x : Fin n → ℂ) (c : ℝ) :
    |S.indicator f x * c| = S.indicator (fun z => |f z * c|) x := by
  by_cases hx : x ∈ S <;> simp [hx]

theorem abs_indicator_mul_le (S : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℝ) (x : Fin n → ℂ) (c : ℝ) :
    |S.indicator f x * c| ≤ |f x * c| := by
  by_cases hx : x ∈ S <;> simp [hx] <;> positivity

end ChartIntCountAdd


open ChartIntCountAdd in
theorem ChartIntCountAdd.proof (hCM : ChartMassCompact.Statement) : ChartIntCountAdd.Statement := by
  intro n d W A f φ E hW hdim hA hf hfc hφ hEm hE
  have hfin : ∀ y, (ComplexSets.fibre W A y).Finite := fun y =>
    (ComplexSets.FibreBound.proof n d W A hW hdim hA y).2.1
  have hmeas : ∀ g : (Fin n → ℂ) → ℝ, Measurable g →
      Measurable (chartDens W A g φ) ∧ Measurable (chartAbsDens W A g φ) := fun g hg =>
    SheetSumMeasurable.proof n d W A g φ hW hdim hA hg hφ
  have hgm : ∀ i, Measurable ((E i).indicator f) := fun i => hf.measurable.indicator (hEm i)
  have hgu : Measurable ((⋃ i, E i).indicator f) := hf.measurable.indicator (MeasurableSet.iUnion hEm)

  have hdens : ∀ y, HasSum (fun i => chartDens W A ((E i).indicator f) φ y)
      (chartDens W A ((⋃ i, E i).indicator f) φ y) := by
    intro y
    unfold chartDens
    refine hasSum_sheetSum (hfin y) _ _ fun x s => ?_
    simp only [indicator_mul]
    exact hasSum_indicator hE _ x
  have habs : ∀ y, HasSum (fun i => chartAbsDens W A ((E i).indicator f) φ y)
      (chartAbsDens W A ((⋃ i, E i).indicator f) φ y) := by
    intro y
    unfold chartAbsDens
    refine hasSum_sheetSum (hfin y) _ _ fun x s => ?_
    simp only [abs_indicator_mul]
    exact hasSum_indicator hE _ x

  have hdom : Integrable (chartAbsDens W A ((⋃ i, E i).indicator f) φ) := by
    refine (hCM n d W A f φ hW hdim hA hf.continuousOn hφ (Or.inl hfc)).mono'
      (hmeas _ hgu).2.aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs]
    unfold chartAbsDens
    refine (abs_sheetSum_le (hfin y) _).trans (sheetSum_mono (hfin y) fun x s => ?_)
    rw [abs_abs]
    exact abs_indicator_mul_le _ _ _ _
  have hsum : (fun y => ∑' i, chartAbsDens W A ((E i).indicator f) φ y) =
      chartAbsDens W A ((⋃ i, E i).indicator f) φ := funext fun y => (habs y).tsum_eq
  exact hasSum_integral_of_dominated_convergence (μ := volume)
    (F := fun i => chartDens W A ((E i).indicator f) φ)
    (f := chartDens W A ((⋃ i, E i).indicator f) φ)
    (fun i => chartAbsDens W A ((E i).indicator f) φ)
    (fun i => (hmeas _ (hgm i)).1.aestronglyMeasurable)
    (fun i => ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]
      exact abs_sheetSum_le (hfin y) _)
    (ae_of_all _ fun y => (habs y).summable)
    (by rw [hsum]; exact hdom)
    (ae_of_all _ hdens)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarMassNearSmall
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ENNReal NNReal

noncomputable section

namespace VarMassNearSmall

variable {n d : ℕ}

theorem abs_sheetSum_le (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    {F G : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ} (hFG : ∀ x s, |F x s| ≤ G x s)
    {y : Fin d → ℂ} (hfin : (ComplexSets.fibre J A y).Finite) :
    |sheetSum J A F y| ≤ sheetSum J A G y := by
  classical
  unfold sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  split_ifs with h
  · exact hFG x _
  · simp

theorem volume_eq_zero_of_hausdorff {S : Set (Fin d → ℂ)} (hS : μH[((2 * d : ℕ) : ℝ)] S = 0) :
    volume S = 0 := by
  let E : ((Σ _ : Fin d, Fin 2) → ℝ) ≃L[ℝ] (Fin d → ℂ) :=
    (Pi.basis (fun _ : Fin d => Complex.basisOneI)).equivFun.symm.toContinuousLinearEquiv
  have hcard : Fintype.card (Σ _ : Fin d, Fin 2) = 2 * d := by
    simp [Fintype.card_sigma, mul_comm]
  have hT : volume (E ⁻¹' S) = 0 := by
    rw [← hausdorffMeasure_pi_real, hcard]
    have h := E.symm.lipschitzWith.hausdorffMeasure_image_le (d := ((2 * d : ℕ) : ℝ)) (by positivity) S
    rw [hS, mul_zero, nonpos_iff_eq_zero, ContinuousLinearEquiv.image_symm_eq_preimage] at h
    exact h
  have : (Measure.map E volume).IsAddHaarMeasure := E.isAddHaarMeasure_map volume
  have hac : (volume : Measure (Fin d → ℂ)) ≪ Measure.map E volume :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  apply hac
  exact (E.toHomeomorph.toMeasurableEquiv.map_apply S).trans hT

theorem volume_image_eq_zero (W I : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hI : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < d) :
    volume (A.mulVec '' (zeroSet W ∩ zeroSet I)) = 0 := by
  have hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (W ⊔ I)) < d :=
    (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective le_sup_right)).trans_lt hI
  have h0 := NullSmaller.proof n d (W ⊔ I) hdim
  let L : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin d → ℂ) :=
    (Matrix.mulVecLin A).toContinuousLinearMap.comp (EuclideanSpace.equiv (Fin n) ℂ).toContinuousLinearMap
  have hsub : A.mulVec '' (zeroSet W ∩ zeroSet I) ⊆ L '' zeroSetEuc (W ⊔ I) := by
    rintro _ ⟨x, ⟨hxW, hxI⟩, rfl⟩
    refine ⟨(EuclideanSpace.equiv (Fin n) ℂ).symm x, fun q hq => ?_, by simp only [L, ContinuousLinearMap.comp_apply]; rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hq
    have hx : (fun i => ((EuclideanSpace.equiv (Fin n) ℂ).symm x) i) = x := rfl
    rw [hx, map_add (f := _), hxW a ha, hxI b hb, add_zero]
  refine volume_eq_zero_of_hausdorff (le_antisymm ?_ bot_le)
  calc μH[((2 * d : ℕ) : ℝ)] (A.mulVec '' (zeroSet W ∩ zeroSet I))
      ≤ μH[((2 * d : ℕ) : ℝ)] (L '' zeroSetEuc (W ⊔ I)) := measure_mono hsub
    _ ≤ _ := L.lipschitz.hausdorffMeasure_image_le (by positivity) _
    _ = 0 := by rw [h0, mul_zero]

end VarMassNearSmall


open VarMassNearSmall in
theorem VarMassNearSmall.proof (hCMC : ChartMassCompact.Statement) : VarMassNearSmall.Statement := by
  classical
  intro n d W I φ f hW hdim hφ hI hf hfc δ hδ
  by_cases hA : ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection W A
  swap
  · refine ⟨Set.univ, isOpen_univ, Set.subset_univ _, fun χ _ _ _ => ?_⟩
    unfold varInt
    rw [dite_eq_right hA, abs_zero]
    exact hδ.le
  set A := hA.choose with hAdef
  have hAf : IsFiniteProjection W A := hA.choose_spec
  have hvar : ∀ g, varInt W d g φ = ∫ y, chartDens W A g φ y := fun g => by
    unfold varInt chartInt
    rw [dite_eq_left hA]
  have hfin : ∀ y, (ComplexSets.fibre W A y).Finite := fun y => (FibreBound.proof n d W A hW hdim hAf y).2.1
  have hS : IsClosed (zeroSet I) := SheetSumMeasurable.isClosed_zeroSet I
  set U : ℕ → Set (Fin n → ℂ) := fun k => Metric.thickening (1 / ((k : ℝ) + 1)) (zeroSet I) with hU
  set F : ℕ → (Fin d → ℂ) → ℝ := fun k => chartAbsDens W A ((U k).indicator fun x => |f x|) φ with hF
  set G := chartAbsDens W A (fun x => |f x|) φ with hG
  have hGi : Integrable G := hCMC n d W A _ φ hW hdim hAf (continuous_abs.comp hf).continuousOn hφ
    (Or.inl (hfc.comp_left abs_zero))
  have hFm : ∀ k, Measurable (F k) := fun k => (SheetSumMeasurable.proof n d W A _ φ hW hdim hAf
    ((continuous_abs.comp hf).measurable.indicator Metric.isOpen_thickening.measurableSet) hφ).2
  have hFG : ∀ k y, ‖F k y‖ ≤ G y := by
    intro k y
    rw [Real.norm_eq_abs]
    refine abs_sheetSum_le W A (fun x s => ?_) (hfin y)
    rw [abs_abs, abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    by_cases hx : x ∈ U k
    · simp [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, abs_zero]
      exact abs_nonneg _
  have hlim : ∀ᵐ y, Tendsto (fun k => F k y) atTop (𝓝 0) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (volume_image_eq_zero W I A hI)] with y hy
    have hx : ∀ x ∈ ComplexSets.fibre W A y, ∀ᶠ k in atTop, x ∉ U k := by
      intro x hxf
      have hxS : x ∉ zeroSet I := fun h => hy ⟨x, ⟨hxf.1, h⟩, hxf.2⟩
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hS.isOpen_compl x hxS
      obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
      filter_upwards [eventually_ge_atTop K] with k hk hxU
      obtain ⟨z, hz, hdist⟩ := Metric.mem_thickening_iff.1 hxU
      have hKk : (K : ℝ) + 1 ≤ (k : ℝ) + 1 := by
        have : (K : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      have hle : 1 / ((k : ℝ) + 1) ≤ 1 / ((K : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) hKk
      exact hball (show dist z x < ε by rw [dist_comm]; linarith) hz
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(eventually_all_finite (hfin y)).2 hx] with k hk
    symm
    show sheetSum W A _ y = 0
    unfold sheetSum
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
    refine Finset.sum_eq_zero fun x hxm => ?_
    rw [Set.Finite.mem_toFinset] at hxm
    split_ifs <;> simp [Set.indicator_of_notMem (hk x hxm)]
  have hT := tendsto_integral_of_dominated_convergence G (fun k => (hFm k).aestronglyMeasurable) hGi
    (fun k => Eventually.of_forall (hFG k)) hlim
  simp only [integral_zero] at hT
  obtain ⟨k, hk⟩ := ((tendsto_order.1 hT).2 δ hδ).exists
  refine ⟨U k, Metric.isOpen_thickening, Metric.self_subset_thickening (by positivity) _,
    fun χ hχ hχ1 hχU => ?_⟩
  have hFi : Integrable (F k) := hGi.mono' (hFm k).aestronglyMeasurable (Eventually.of_forall (hFG k))
  have hpt : ∀ y, ‖chartDens W A (fun x => χ x * f x) φ y‖ ≤ F k y := by
    intro y
    rw [Real.norm_eq_abs]
    refine abs_sheetSum_le W A (fun x s => ?_) (hfin y)
    by_cases hx : x ∈ U k
    · rw [Set.indicator_of_mem hx, abs_mul, abs_mul, abs_mul, abs_abs]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) (hχ1 x)) (abs_nonneg _)
    · have h0 : χ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hχU h)
      simp only [h0, zero_mul, abs_zero]
      positivity
  have h1 := norm_integral_le_of_norm_le hFi (Eventually.of_forall hpt)
  rw [Real.norm_eq_abs, ← hvar] at h1
  exact h1.trans hk.le

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelDivisorChartGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

theorem NormalModelDivisorChartGeneric.proof (h₁ : NormalModelGoodPointGeneric.Statement)
    (h₂ : NormalModelGoodPointChart.Statement) : NormalModelDivisorChartGeneric.Statement := by
  intro n d J u M hJ hd hu
  obtain ⟨B, hB, hBd, hgood⟩ := h₁ n d J u M hJ hd hu
  exact ⟨B, hB, hBd, fun w hw hu0 hwB => h₂ n d J u M w (hgood w hw hu0 hwB)⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PEnergyDensNonneg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A

noncomputable section

theorem EnergyDensNonneg.proof : EnergyDensNonneg.Statement := by
  intro n d s y v hs
  have hV : IsOpen {z | AnalyticAt ℂ s z} := isOpen_analyticAt ℂ s
  have hC : ∀ z ∈ {z | AnalyticAt ℂ s z}, ContDiffAt ℝ 2 (euclPot ∘ s) z := fun z hz =>
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp z
      (hz.restrictScalars (𝕜 := ℝ)).contDiffAt
  refine gradDensNonneg_thm d (fun _ => euclPot ∘ s) v _ hV
    (fun _ => fun z hz => (hC z hz).contDiffWithinAt) ?_ y hs
  intro _ z hz ξ
  rw [levi_comp ξ hz ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt,
    TubeFormComparison.levi_euclPot]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

end

end GroundTheory.Heights₂.Heights
end
