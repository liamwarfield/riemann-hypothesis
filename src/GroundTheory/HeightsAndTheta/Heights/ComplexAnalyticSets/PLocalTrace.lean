module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHomogDimZeroPow
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFundCycleBaseChange
public import GroundTheory.ArithmeticGeometry.EtaleCompletion.ModulesPullback
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularUFD
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionCluster
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularLocusDense

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalTrace
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

theorem isClosed_zeroSetIn_of_ideal {σ : Type*} (I : Ideal (MvPolynomial σ ℂ)) :
    IsClosed (zeroSetIn I) := by
  have h : zeroSetIn I = ⋂ q ∈ I, {z : σ → ℂ | eval z q = 0} := by
    ext z; simp [zeroSetIn]
  rw [h]
  exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const

theorem HolomorphicOnSubset.continuousWithinAt_trace {σ : Type*} [Fintype σ] {g : (σ → ℂ) → ℂ}
    {S : Set (σ → ℂ)} (hg : HolomorphicOnSubset g S) {z : σ → ℂ} (hz : z ∈ S) :
    ContinuousWithinAt g S z := by
  obtain ⟨V, hV, hzV, F, hF, hgF⟩ := hg z hz
  have hFc : ContinuousAt F z := (hF.differentiableAt (hV.mem_nhds hzV)).continuousAt
  refine hFc.continuousWithinAt.congr_of_eventuallyEq ?_ (hgF ⟨hz, hzV⟩)
  filter_upwards [inter_mem_nhdsWithin S (hV.mem_nhds hzV)] with x hx using hgF hx

theorem HolomorphicOnSubset.differentiableAt_comp {σ : Type*} [Fintype σ] {k : ℕ}
    {g : (σ → ℂ) → ℂ} {S : Set (σ → ℂ)} (hg : HolomorphicOnSubset g S)
    {s : (Fin k → ℂ) → σ → ℂ} {y : Fin k → ℂ} (hs : DifferentiableAt ℂ s y)
    (hS : ∀ᶠ y' in 𝓝 y, s y' ∈ S) : DifferentiableAt ℂ (fun y' => g (s y')) y := by
  obtain ⟨V, hV, hzV, F, hF, hgF⟩ := hg (s y) hS.self_of_nhds
  have hFd : DifferentiableAt ℂ F (s y) := hF.differentiableAt (hV.mem_nhds hzV)
  have hev : ∀ᶠ y' in 𝓝 y, s y' ∈ V := hs.continuousAt.preimage_mem_nhds (hV.mem_nhds hzV)
  refine (hFd.comp y hs).congr_of_eventuallyEq ?_
  filter_upwards [hS, hev] with y' h1 h2 using hgF ⟨h1, h2⟩

theorem LocalTrace.proof (hbc : LocalBranchedCovering.Statement) : LocalTrace.Statement := by
  intro σ _ I w U g hI hw hU hg
  obtain ⟨k, A, W, D, m, δ, hWo, hwW, hWc, hWU, hDo, hAwD, hwonly, hprop, hδd, hδne, hsheets,
    hopen⟩ := hbc σ I w U hI hw hU
  have hZc : IsClosed (zeroSetIn I) := isClosed_zeroSetIn_of_ideal I
  have hKc : IsCompact (zeroSetIn I ∩ closure W) := hWc.inter_left hZc
  have hgc : ContinuousOn g (zeroSetIn I ∩ U) := fun z hz => hg.continuousWithinAt_trace hz
  obtain ⟨M, hM⟩ : ∃ M, ∀ z ∈ zeroSetIn I ∩ closure W, ‖g z‖ ≤ M :=
    hKc.exists_bound_of_continuousOn (hgc.mono (Set.inter_subset_inter_right _ hWU))

  obtain ⟨f, hf⟩ : ∃ f : (Fin k → ℂ) → ℂ,
      ∀ y, f y = ∑ᶠ z ∈ {z | z ∈ zeroSetIn I ∩ W ∧ A z = y}, g z := ⟨_, fun _ => rfl⟩
  have hfsum : ∀ (s : Fin m → σ → ℂ) (y : Fin k → ℂ),
      (∀ j, s j ∈ zeroSetIn I ∩ W ∧ A (s j) = y) → Function.Injective s →
      (∀ z ∈ zeroSetIn I ∩ W, A z = y → z ∈ Set.range s) → f y = ∑ j, g (s j) := by
    intro s y hs hinj hcov
    have hset : {z | z ∈ zeroSetIn I ∩ W ∧ A z = y} = Set.range s := by
      ext z
      constructor
      · rintro ⟨hz, hAz⟩
        exact hcov z hz hAz
      · rintro ⟨j, rfl⟩
        exact hs j
    rw [hf, hset, finsum_mem_range hinj, finsum_eq_sum_of_fintype]
  have hmemU : ∀ z ∈ zeroSetIn I ∩ W, z ∈ zeroSetIn I ∩ U := fun z hz =>
    ⟨hz.1, hWU (subset_closure hz.2)⟩
  have hfd : DifferentiableOn ℂ f (D ∩ {t | δ t ≠ 0}) := by
    rintro y ⟨hyD, hyδ⟩
    obtain ⟨O, s, hOo, hyO, hsd, hsO⟩ := hsheets y hyD hyδ
    have hev : f =ᶠ[𝓝 y] fun y' => ∑ j, g (s j y') := by
      filter_upwards [hOo.mem_nhds hyO] with y' hy'
      exact hfsum (fun j => s j y') y' (hsO y' hy').1 (hsO y' hy').2.1 (hsO y' hy').2.2
    refine (DifferentiableAt.congr_of_eventuallyEq ?_ hev).differentiableWithinAt
    refine DifferentiableAt.fun_sum fun j _ => ?_
    refine hg.differentiableAt_comp ((hsd j).differentiableAt (hOo.mem_nhds hyO)) ?_
    filter_upwards [hOo.mem_nhds hyO] with y' hy' using hmemU _ ((hsO y' hy').1 j).1
  have hfb : ∀ y ∈ D ∩ {t | δ t ≠ 0}, ‖f y‖ ≤ m * M := by
    rintro y ⟨hyD, hyδ⟩
    obtain ⟨O, s, hOo, hyO, hsd, hsO⟩ := hsheets y hyD hyδ
    rw [hfsum (fun j => s j y) y (hsO y hyO).1 (hsO y hyO).2.1 (hsO y hyO).2.2]
    calc ‖∑ j, g (s j y)‖ ≤ ∑ j : Fin m, ‖g (s j y)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin m, M := Finset.sum_le_sum fun j _ =>
          hM _ ⟨((hsO y hyO).1 j).1.1, subset_closure ((hsO y hyO).1 j).1.2⟩
      _ = m * M := by simp
  obtain ⟨T, hTd, hTf⟩ := RiemannExtensionAnalytic.proof k D δ f hDo hδd hδne hfd (fun τ _ =>
    ⟨Set.univ, Filter.univ_mem, isBounded_iff_forall_norm_le.2 ⟨m * M, by
      rintro _ ⟨y, ⟨⟨_, hyD⟩, hyδ⟩, rfl⟩
      exact hfb y ⟨hyD, hyδ⟩⟩⟩)
  refine ⟨k, A, W ∩ A ⁻¹' D, D, m, T, hWo.inter (hDo.preimage A.continuous), ⟨hwW, hAwD⟩,
    fun z hz => hWU (subset_closure hz.1), hDo, hAwD,
    fun z hz hAz => hwonly z ⟨hz.1, hz.2.1⟩ hAz, hTd, ?_⟩
  intro y hyD

  have hseq : ∀ n : ℕ, ∃ t ∈ D ∩ Metric.ball y (1 / ((n : ℝ) + 1)), δ t ≠ 0 := fun n =>
    hδne _ (hDo.inter Metric.isOpen_ball) Set.inter_subset_left
      ⟨y, hyD, Metric.mem_ball_self (by positivity)⟩
  choose t ht htδ using hseq
  have htD : ∀ n, t n ∈ D := fun n => (ht n).1
  have httend : Tendsto t atTop (𝓝 y) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => le_of_lt (ht n).2)
      tendsto_one_div_add_atTop_nhds_zero_nat

  have hX : ∀ n, ∃ X : Fin m → σ → ℂ, (∀ j, X j ∈ zeroSetIn I ∩ W ∧ A (X j) = t n) ∧
      (∀ z ∈ zeroSetIn I ∩ W, A z = t n → z ∈ Set.range X) ∧ T (t n) = ∑ j, g (X j) := by
    intro n
    obtain ⟨O, s, hOo, hyO, hsd, hsO⟩ := hsheets (t n) (htD n) (htδ n)
    obtain ⟨h1, h2, h3⟩ := hsO (t n) hyO
    exact ⟨fun j => s j (t n), h1, h3, by rw [hTf ⟨htD n, htδ n⟩, hfsum _ (t n) h1 h2 h3]⟩
  choose X hXmem hXcov hXT using hX

  have hKm : IsCompact (Set.univ.pi fun _ : Fin m => zeroSetIn I ∩ closure W) :=
    isCompact_univ_pi fun _ => hKc
  obtain ⟨x, hxK, φ, hφ, hXφ⟩ := hKm.tendsto_subseq (x := X) (fun n => Set.mem_univ_pi.2 fun j =>
    ⟨(hXmem n j).1.1, subset_closure (hXmem n j).1.2⟩)
  have hxK' : ∀ j, x j ∈ zeroSetIn I ∩ closure W := fun j => Set.mem_univ_pi.1 hxK j
  have hxj : ∀ j, Tendsto (fun n => X (φ n) j) atTop (𝓝 (x j)) := fun j => tendsto_pi_nhds.1 hXφ j
  have htφ : Tendsto (fun n => t (φ n)) atTop (𝓝 y) := httend.comp hφ.tendsto_atTop
  have hAx : ∀ j, A (x j) = y := fun j =>
    tendsto_nhds_unique ((A.continuous.tendsto _).comp (hxj j))
      (Tendsto.congr (fun n => ((hXmem (φ n) j).2).symm) htφ)
  have hxW : ∀ j, x j ∈ W := fun j => hprop (x j) (hxK' j) (by rw [hAx j]; exact hyD)
  have hT1 : Tendsto (fun n => T (t (φ n))) atTop (𝓝 (T y)) :=
    (hTd.differentiableAt (hDo.mem_nhds hyD)).continuousAt.tendsto.comp htφ
  have hT2 : Tendsto (fun n => T (t (φ n))) atTop (𝓝 (∑ j, g (x j))) := by
    have hs : Tendsto (fun n => ∑ j, g (X (φ n) j)) atTop (𝓝 (∑ j, g (x j))) := by
      refine tendsto_finsetSum _ fun j _ => ?_
      exact (hgc (x j) ⟨(hxK' j).1, hWU (hxK' j).2⟩).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hxj j, Filter.Eventually.of_forall fun n =>
          hmemU _ (hXmem (φ n) j).1⟩)
    exact Tendsto.congr (fun n => (hXT (φ n)).symm) hs
  refine ⟨x, fun j => ⟨⟨(hxK' j).1, hxW j, by show A (x j) ∈ D; rw [hAx j]; exact hyD⟩, hAx j⟩,
    ?_, tendsto_nhds_unique hT1 hT2⟩

  rintro z ⟨hzZ, hzW, -⟩ hAz
  by_contra hz
  have hne : ∀ j, 0 < dist z (x j) := fun j => dist_pos.2 fun h => hz ⟨j, h.symm⟩
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hWo z hzW
  have hε : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ r ∧ ∀ j, 2 * ε < dist z (x j) := by
    refine Filter.Eventually.and (self_mem_nhdsWithin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε) (Filter.Eventually.and (nhdsWithin_le_nhds (Iic_mem_nhds hr) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ r)
      (Filter.eventually_all.2 fun j => nhdsWithin_le_nhds ?_))
    have h2 : Tendsto (fun ε : ℝ => 2 * ε) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_const_mul (2 : ℝ)).tendsto 0
    exact h2.eventually (gt_mem_nhds (hne j))
  obtain ⟨ε, hε0, hεr, hεd⟩ := hε.exists
  have hnbhd := hopen z ⟨hzZ, hzW⟩ ε hε0
  rw [hAz] at hnbhd
  have hev1 : ∀ᶠ n in atTop, t (φ n) ∈ A '' (zeroSetIn I ∩ Metric.ball z ε) := htφ hnbhd
  have hev2 : ∀ᶠ n in atTop, ∀ j, dist (X (φ n) j) (x j) < ε :=
    Filter.eventually_all.2 fun j => Metric.tendsto_nhds.1 (hxj j) ε hε0
  obtain ⟨n, ⟨z', ⟨hz'Z, hz'b⟩, hAz'⟩, hd⟩ := (hev1.and hev2).exists
  have hz'W : z' ∈ W := hrW (Metric.ball_subset_ball hεr hz'b)
  obtain ⟨j, hj⟩ := hXcov (φ n) z' ⟨hz'Z, hz'W⟩ hAz'
  have h1 := hd j
  rw [hj] at h1
  rw [Metric.mem_ball] at hz'b
  have h3 := dist_triangle z z' (x j)
  have h4 := hεd j
  rw [dist_comm] at hz'b
  linarith

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAreaGraphPiece
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace AreaGraphPiece

variable {k m : ℕ}

def pairPt (u : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin k ⊕ Fin m) :=
  WithLp.toLp 2 (Sum.elim (fun i => u i) (fun i => w i))

def firstPart (p : EuclideanSpace ℝ (Fin k ⊕ Fin m)) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun i => p (Sum.inl i))

theorem realGraphPt_eq (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin k)) : realGraphPt F x = pairPt x (F x) := rfl

theorem firstPart_pairPt (u : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℝ (Fin m)) :
    firstPart (pairPt u w) = u := by
  ext i
  simp [firstPart, pairPt]

theorem pairPt_add (u u' : EuclideanSpace ℝ (Fin k)) (w w' : EuclideanSpace ℝ (Fin m)) :
    pairPt u w + pairPt u' w' = pairPt (u + u') (w + w') := by
  ext i
  rcases i with i | i <;> simp [pairPt]

theorem pairPt_sub (u u' : EuclideanSpace ℝ (Fin k)) (w w' : EuclideanSpace ℝ (Fin m)) :
    pairPt u w - pairPt u' w' = pairPt (u - u') (w - w') := by
  ext i
  rcases i with i | i <;> simp [pairPt]

theorem pairPt_smul (c : ℝ) (u : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℝ (Fin m)) :
    c • pairPt u w = pairPt (c • u) (c • w) := by
  ext i
  rcases i with i | i <;> simp [pairPt]

theorem inner_pairPt (u u' : EuclideanSpace ℝ (Fin k)) (w w' : EuclideanSpace ℝ (Fin m)) :
    ⟪pairPt u w, pairPt u' w'⟫ = ⟪u, u'⟫ + ⟪w, w'⟫ := by
  simp [pairPt, PiLp.inner_apply, Fintype.sum_sum_type]

theorem norm_pairPt_sq (u : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℝ (Fin m)) :
    ‖pairPt u w‖ ^ 2 = ‖u‖ ^ 2 + ‖w‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_pairPt]

theorem norm_le_norm_pairPt (u : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℝ (Fin m)) :
    ‖u‖ ≤ ‖pairPt u w‖ := by
  have h := norm_pairPt_sq u w
  nlinarith [norm_nonneg u, norm_nonneg (pairPt u w), sq_nonneg ‖w‖]

theorem norm_pairPt_zero (w : EuclideanSpace ℝ (Fin m)) :
    ‖pairPt (0 : EuclideanSpace ℝ (Fin k)) w‖ = ‖w‖ := by
  have h := norm_pairPt_sq (0 : EuclideanSpace ℝ (Fin k)) w
  rw [norm_zero, zero_pow two_ne_zero, zero_add] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

def graphLin (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k ⊕ Fin m) where
  toFun x := pairPt x (A x)
  map_add' x y := by rw [map_add (f := _), pairPt_add]
  map_smul' c x := by rw [map_smul, pairPt_smul]; rfl

theorem graphLin_apply (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin k)) : graphLin A x = pairPt x (A x) := rfl

theorem adjoint_graphLin_comp (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    LinearMap.adjoint (graphLin A) ∘ₗ graphLin A =
      (1 : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) +
        LinearMap.adjoint (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ∘ₗ
          (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) := by
  apply LinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearMap.add_apply, inner_add_left,
    Module.End.one_apply, LinearMap.comp_apply, LinearMap.adjoint_inner_left, graphLin_apply,
    graphLin_apply, inner_pairPt]
  rfl

theorem normDet_graphLin (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    (graphLin A).normDet =
      graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) := by
  unfold graphJac
  rw [← adjoint_graphLin_comp, ← LinearMap.normDet_sq (graphLin A)]
  push_cast
  exact (Real.sqrt_sq (LinearMap.normDet_nonneg _)).symm

end AreaGraphPiece


open AreaGraphPiece in
theorem AreaGraphPiece.proof : AreaGraphPiece.Statement := by
  intro k m F A δ t hδ hF
  set L := graphLin A with hLdef
  have hδ1 : (δ : ℝ) < 1 := by exact_mod_cast hδ
  have hδ0 : (0 : ℝ) ≤ δ := δ.2

  have hsub : ∀ x y, realGraphPt F x - realGraphPt F y - L (x - y) =
      pairPt (0 : EuclideanSpace ℝ (Fin k)) (F x - F y - A (x - y)) := by
    intro x y
    rw [realGraphPt_eq, realGraphPt_eq, hLdef, graphLin_apply, pairPt_sub, pairPt_sub]
    simp
  have hL : ∀ v, ‖v‖ ≤ ‖L v‖ := fun v => norm_le_norm_pairPt v (A v)
  have hclose : ∀ x ∈ t, ∀ y ∈ t,
      |‖realGraphPt F x - realGraphPt F y‖ - ‖L (x - y)‖| ≤ δ * ‖L (x - y)‖ := by
    intro x hx y hy
    calc |‖realGraphPt F x - realGraphPt F y‖ - ‖L (x - y)‖|
        ≤ ‖realGraphPt F x - realGraphPt F y - L (x - y)‖ := abs_norm_sub_norm_le _ _
      _ = ‖F x - F y - A (x - y)‖ := by rw [hsub, norm_pairPt_zero]
      _ ≤ δ * ‖x - y‖ := hF x hx y hy
      _ ≤ δ * ‖L (x - y)‖ := mul_le_mul_of_nonneg_left (hL _) hδ0

  have himG : realGraphPt F '' t = (fun p => realGraphPt F (firstPart p)) '' (L '' t) := by
    rw [Set.image_image]
    refine Set.image_congr fun x _ => ?_
    rw [hLdef, graphLin_apply, firstPart_pairPt]
  have hlipG : LipschitzOnWith (1 + δ) (fun p => realGraphPt F (firstPart p)) (L '' t) := by
    refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
    obtain ⟨x, hx, rfl⟩ := hp
    obtain ⟨y, hy, rfl⟩ := hq
    simp only [hLdef, graphLin_apply, firstPart_pairPt, dist_eq_norm]
    rw [← graphLin_apply, ← graphLin_apply, ← map_sub, ← hLdef]
    have h := (abs_le.1 (hclose x hx y hy)).2
    push_cast
    linarith

  have himL : L '' t = (fun p => L (firstPart p)) '' (realGraphPt F '' t) := by
    rw [Set.image_image]
    refine Set.image_congr fun x _ => ?_
    rw [realGraphPt_eq, firstPart_pairPt]
  have hlipL : LipschitzOnWith (1 - δ)⁻¹ (fun p => L (firstPart p)) (realGraphPt F '' t) := by
    refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
    obtain ⟨x, hx, rfl⟩ := hp
    obtain ⟨y, hy, rfl⟩ := hq
    simp only [realGraphPt_eq, firstPart_pairPt, dist_eq_norm]
    rw [← realGraphPt_eq, ← realGraphPt_eq, ← map_sub]
    have h := (abs_le.1 (hclose x hx y hy)).1
    rw [NNReal.coe_inv, NNReal.coe_sub hδ.le, NNReal.coe_one, inv_mul_eq_div,
      le_div_iff₀ (by linarith)]
    nlinarith

  have harea : μH[(k : ℝ)] (L '' t) =
      ENNReal.ofReal (graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) *
        μH[(k : ℝ)] t := by
    have h := LinearMap.hausdorffMeasure_image L t
    rw [finrank_euclideanSpace_fin] at h
    rw [h, hLdef, normDet_graphLin]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  constructor
  · calc μH[(k : ℝ)] (realGraphPt F '' t)
        = μH[(k : ℝ)] ((fun p => realGraphPt F (firstPart p)) '' (L '' t)) := by rw [← himG]
      _ ≤ ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ (k : ℝ) * μH[(k : ℝ)] (L '' t) :=
          hlipG.hausdorffMeasure_image_le hk
      _ = _ := by rw [harea, ENNReal.rpow_natCast, mul_assoc]
  · have hle : μH[(k : ℝ)] (L '' t) ≤
        (((1 - δ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ k * μH[(k : ℝ)] (realGraphPt F '' t) := by
      calc μH[(k : ℝ)] (L '' t)
          = μH[(k : ℝ)] ((fun p => L (firstPart p)) '' (realGraphPt F '' t)) := by rw [← himL]
        _ ≤ (((1 - δ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ (k : ℝ) * μH[(k : ℝ)] (realGraphPt F '' t) :=
            hlipL.hausdorffMeasure_image_le hk
        _ = _ := by rw [ENNReal.rpow_natCast]
    have hne : (1 - δ : ℝ≥0) ≠ 0 := (tsub_pos_of_lt hδ).ne'
    calc ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k *
          ENNReal.ofReal (graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) *
            μH[(k : ℝ)] t
        = ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k * μH[(k : ℝ)] (L '' t) := by rw [harea, mul_assoc]
      _ ≤ ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k *
          ((((1 - δ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ k * μH[(k : ℝ)] (realGraphPt F '' t)) := by gcongr
      _ = μH[(k : ℝ)] (realGraphPt F '' t) := by
          rw [← mul_assoc, ← mul_pow, ← ENNReal.coe_mul, mul_inv_cancel₀ hne, ENNReal.coe_one,
            one_pow, one_mul]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchSheetAE
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

def BranchSheetAE.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (p : Fin n → ℂ)
    (γ : VarBranch J d p),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
      ∀ᵐ t ∂(volume.restrict (Metric.ball (0 : Fin d → ℂ) γ.radius)), ∃ s, IsSheetAt J A (γ.toFun t) s

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarietyMassLower
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

def VarietyMassLower.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → ∀ R : ℝ,
      ∃ c : ℝ, 0 < c ∧ ∀ z ∈ zeroSetEuc J, ‖z‖ ≤ R → ∀ ρ ∈ Set.Ioc (0 : ℝ) 1,
        ENNReal.ofReal (c * ρ ^ (2 * d)) ≤
          μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball z ρ)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeTubeVolume
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

def PrimeTubeVolume.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (K : Set (Fin n → ℂ)),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (k : ℕ) → IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1,
        volume (Metric.thickening r (zeroSet J ∩ K)) ≤
          ENNReal.ofReal (C * r ^ ((2 * n : ℤ) - 2 * k))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSmallSetTubeVolume
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

def SmallSetTubeVolume.Statement : Prop :=
  ∀ (n d : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (K : Set (Fin n → ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) → IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1,
        volume (Metric.thickening r (zeroSet I ∩ K)) ≤
          ENNReal.ofReal (C * r ^ ((2 * n + 2 : ℤ) - 2 * d))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StMaDensLogPow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ComplexSets

noncomputable section

def MaDensLogPow.Statement : Prop :=
  ∀ (e : ℕ) (φ₀ p : (Fin (e + 1 + 1) → ℂ) → ℝ) (y : Fin (e + 1 + 1) → ℂ),
    ContDiffAt ℝ 2 p y → 0 < p y →
      maDens (Fin.cons φ₀ fun _ : Fin (e + 1) => Real.log ∘ p) y =
        maDens (Fin.cons φ₀ fun _ : Fin (e + 1) => p) y / p y ^ (e + 1) -
          ((e + 1 : ℕ) : ℝ) * gradDens (Fin.cons φ₀ fun _ : Fin e => p) p p y / p y ^ (e + 2)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicFibreSumInt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ReciprocityTheory.AnForm.A

noncomputable section

def HolomorphicFibreSumInt.Statement : Prop :=
  ∀ (d : ℕ) (Ω : Set (Fin d → ℂ)) (τ : (Fin d → ℂ) → Fin d → ℂ) (H : (Fin d → ℂ) → ℝ),
    IsOpen Ω → DifferentiableOn ℂ τ Ω → (∀ y, {t | t ∈ Ω ∧ τ t = y}.Finite) →
    IntegrableOn (fun t => Complex.normSq (jacC τ t).det * H t) Ω →
      Integrable (fun y => ∑ᶠ t ∈ {t | t ∈ Ω ∧ τ t = y}, H t) ∧
        ∫ y, (∑ᶠ t ∈ {t | t ∈ Ω ∧ τ t = y}, H t) =
          ∫ t in Ω, Complex.normSq (jacC τ t).det * H t

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeGermFiniteProjection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def PrimeGermFiniteProjection.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (p : Fin k → (σ → ℂ) → ℂ),
    (∀ i, AnalyticAt ℂ (p i) w) → (holGermIdeal w p).IsPrime →
    ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
      (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → IsGermCombination w p (fun z => h (A z)) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) ∧
      (∀ i : σ, ∃ (n : ℕ) (b : Fin n → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (b j) (A w)) ∧
        IsGermCombination w p (fun z => z i ^ n + ∑ j, b j (A z) * z i ^ (j : ℕ))) ∧
      (∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
        ∃ (s : Finset (σ → ℕ)) (a : (σ → ℕ) → (Fin d → ℂ) → ℂ), (∀ m ∈ s, AnalyticAt ℂ (a m) (A w)) ∧
          IsGermCombination w p (fun z => g z - ∑ m ∈ s, a m (A z) * ∏ i, z i ^ m i))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalGeneratorsClearDenominators
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem LocalGeneratorsClearDenominators.polyOriginIdeal_isPrime : polyOriginIdeal.IsPrime :=
  polyOriginIdeal_isMaximal.isPrime

attribute [local instance] LocalGeneratorsClearDenominators.polyOriginIdeal_isPrime

def LocalGeneratorsClearDenominators.Statement : Prop :=
  ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (P : Ideal T) [P.IsPrime] (h : ℕ) (f : Fin h → T),
    (∀ i, f i ∈ P) →
    maximalIdeal (Localization.AtPrime P) ≤
        Ideal.span (Set.range fun i => algebraMap T (Localization.AtPrime P) (f i)) ⊔
          maximalIdeal (Localization.AtPrime P) ^ 2 →
      ∃ s ∉ P, ∀ x ∈ P, s * x ∈ Ideal.span (Set.range f)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartIntSumOffHyperplane
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

def ChartIntSumOffHyperplane.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (u : Fin n → ℂ)
    (m : ℕ) (f : (Fin n → ℂ) → ℝ) (F : Fin m → (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    linForm u ∉ J →
    (∀ x ∈ zeroSet J, linEval u x ≠ 0 → f x = ∑ b, F b x) →
    (∀ b, Integrable (chartDens J A (F b) φ)) →
      chartInt J A f φ = ∑ b, chartInt J A (F b) φ

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StMaDensChain
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

def MaDensChain.Statement : Prop :=
  ∀ (D : ℕ) (φ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (F : ℝ → ℝ) (g : (Fin (D + 1) → ℂ) → ℝ)
    (z : Fin (D + 1) → ℂ),
    ContDiff ℝ 2 F → ContDiffAt ℝ 2 g z →
      maDens (Fin.cons (F ∘ g) φ) z =
          deriv F (g z) * maDens (Fin.cons g φ) z + deriv (deriv F) (g z) * gradDens φ g g z ∧
        gradDens φ (F ∘ g) (F ∘ g) z = deriv F (g z) ^ 2 * gradDens φ g g z

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDerivationMinorOfDetection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem DerivationMinorOfDetection.polyOriginIdeal_isPrime : polyOriginIdeal.IsPrime :=
  polyOriginIdeal_isMaximal.isPrime

attribute [local instance] DerivationMinorOfDetection.polyOriginIdeal_isPrime

def DerivationMinorOfDetection.Statement : Prop :=
  ∀ (T : Type) [CommRing T] (P : Ideal T) [P.IsPrime] (h : ℕ) (f : Fin h → T), (∀ i, f i ∈ P) →
    (∀ a : Fin h → Localization.AtPrime P,
      ∑ i, a i * algebraMap T (Localization.AtPrime P) (f i) ∈ maximalIdeal (Localization.AtPrime P) ^ 2 →
        ∀ i, a i ∈ maximalIdeal (Localization.AtPrime P)) →
    (∀ g ∈ P, (∀ D : Derivation ℤ T T, D g ∈ P) →
      algebraMap T (Localization.AtPrime P) g ∈ maximalIdeal (Localization.AtPrime P) ^ 2) →
    ∃ D : Fin h → Derivation ℤ T T, (Matrix.of fun i j => D j (f i)).det ∉ P

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAffineCompletionNormal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem adicCompletion_isLocalRing_of_isMaximal {A : Type*} [CommRing A] (m : Ideal A) [m.IsMaximal]
    (fg : m.FG) : IsLocalRing (AdicCompletion m A) := by
  have := AdicCompletion.isMaximal_map_of_le m m le_rfl fg
  have := AdicCompletion.isAdicComplete_self m fg
  exact isLocalRing_of_isAdicComplete_maximal (m.map (algebraMap A (AdicCompletion m A)))

theorem AffineCompletionNormal.proof (hF : FlatNormalFibres.Statement) (hR : FormalFibresRegular.Statement) :
    AffineCompletionNormal.Statement := by
  intro σ _ I m hI hIC hm
  have : I.IsPrime := hI
  have : m.IsMaximal := hm
  have hloc := adicCompletion_isLocalRing_of_isMaximal m (Ideal.fg_of_isNoetherianRing m)
  refine hF (MvPolynomial σ ℂ ⧸ I) (AdicCompletion m (MvPolynomial σ ℂ ⧸ I)) inferInstance inferInstance hloc
    inferInstance inferInstance hIC fun P _ => ?_
  have := hR ℂ (MvPolynomial σ ℂ ⧸ I) inferInstance m hm P
  exact ⟨inferInstance, GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isIntegrallyClosed _⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarMassNearSmall
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def VarMassNearSmall.Statement : Prop :=
  ∀ (n d : ℕ) (W I : Ideal (MvPolynomial (Fin n) ℂ)) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (f : (Fin n → ℂ) → ℝ),
    W.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) →
    (∀ i, SmoothNear (zeroSet W) (φ i)) → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) →
    Continuous f → HasCompactSupport f →
      ∀ δ > 0, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ zeroSet I ⊆ U ∧
        ∀ χ : (Fin n → ℂ) → ℝ, Continuous χ → (∀ x, |χ x| ≤ 1) → tsupport χ ⊆ U →
          |varInt W d (fun x => χ x * f x) φ| ≤ δ

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarWirtinger
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ENNReal

noncomputable section

def VarWirtinger.Statement : Prop :=
  ∀ d : ℕ, ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ),
      J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
      ∀ B : Set (EuclideanSpace ℂ (Fin n)), MeasurableSet B → Bornology.IsBounded B →
        Integrable (chartDens J A (((fun x => WithLp.toLp 2 x) ⁻¹' B).indicator fun _ => 1)
            (fun _ => euclPot)) ∧
          μH[((2 * (d + 1) : ℕ) : ℝ)] (zeroSetEuc J ∩ B) =
            ENNReal.ofReal (c * ∫ y, chartDens J A (((fun x => WithLp.toLp 2 x) ⁻¹' B).indicator fun _ => 1)
              (fun _ => euclPot) y)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchChartInt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def BranchChartInt.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (p : Fin n → ℂ)
    (γ : VarBranch J d p) (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    Continuous g → (∀ k, SmoothNear (zeroSet J) (φ k)) →
    (∃ K : Set (Fin d → ℂ), IsCompact K ∧ K ⊆ Metric.ball 0 γ.radius ∧
      ∀ t ∈ Metric.ball 0 γ.radius, t ∉ K → g (γ.toFun t) = 0) →
      Integrable (chartDens J A (γ.image.indicator g) φ) ∧
        chartInt J A (γ.image.indicator g) φ =
          ReciprocityTheory.AnForm.maInt (fun k => φ k ∘ γ.toFun) (g ∘ γ.toFun) (Metric.ball 0 γ.radius)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPolydiscLelongLimit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix
open scoped ContDiff

noncomputable section

def PolydiscLelongLimit.Statement : Prop :=
  ∀ (d m : ℕ) (r ρ : ℝ) (F : (Fin (d + 1) → ℂ) → ℂ) (χ : (Fin (d + 1) → ℂ) → ℝ)
    (ψ : Fin d → (Fin (d + 1) → ℂ) → ℝ),
    ρ < r → VanishesToOrder F r m → ContDiffOn ℝ ∞ χ (Metric.ball 0 r) →
    (∀ τ ∈ Metric.ball (0 : Fin (d + 1) → ℂ) r, χ τ ≠ 0 → τ ∈ Metric.ball 0 ρ) →
    (∀ k, ContDiffOn ℝ ∞ (ψ k) (Metric.ball 0 r)) →
      Tendsto (fun ε : ℝ =>
          ReciprocityTheory.AnForm.maInt (vecCons (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) ψ) χ (Metric.ball 0 r))
        (𝓝[>] 0)
        (𝓝 ((m : ℝ) * ∫ w in Metric.ball (0 : Fin d → ℂ) r,
          χ (ReciprocityTheory.AnForm.A.hypIncl w) * ReciprocityTheory.AnForm.A.densHyp ψ w))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchInverseOffHypersurface
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

theorem BranchInverseOffHypersurface.proof (hinv : InjectiveHolomorphicInverse.Statement)
    (hproj : ProjectionInjectiveOffHypersurface.Statement) :
    BranchInverseOffHypersurface.Statement := by
  intro σ _ I k hI hk
  obtain ⟨h', hh', hloc⟩ := hproj σ I k hI hk
  refine ⟨h', hh', fun U φ ψ hU hφd hφi hφZ hψ => ?_⟩
  rintro _ ⟨⟨t, ht, rfl⟩, hz⟩
  obtain ⟨W, hWo, hzW, A, hA⟩ := hloc (φ t) (hφZ ht) hz
  have hU'o : IsOpen (U ∩ φ ⁻¹' W) := hφd.continuousOn.isOpen_inter_preimage hU hWo
  have hfd : DifferentiableOn ℂ (fun s => A (φ s)) (U ∩ φ ⁻¹' W) :=
    A.differentiable.differentiableOn.comp (hφd.mono Set.inter_subset_left) (Set.mapsTo_univ _ _)
  have hfi : Set.InjOn (fun s => A (φ s)) (U ∩ φ ⁻¹' W) := fun s hs s' hs' hss' =>
    hφi hs.1 hs'.1 (hA ⟨hφZ hs.1, hs.2⟩ ⟨hφZ hs'.1, hs'.2⟩ hss')
  obtain ⟨hOo, g, hgd, hgf⟩ := hinv k _ _ hU'o hfd hfi
  refine ⟨W ∩ A ⁻¹' ((fun s => A (φ s)) '' (U ∩ φ ⁻¹' W)), hWo.inter (hOo.preimage A.continuous),
    ⟨hzW, t, ⟨ht, hzW⟩, rfl⟩, fun y => g (A y), ?_, ?_⟩
  · exact hgd.comp A.differentiable.differentiableOn fun y hy => hy.2
  · rintro _ ⟨⟨⟨s, hs, rfl⟩, -⟩, hsW, -⟩
    show ψ (φ s) = g (A (φ s))
    rw [hψ s hs, hgf s ⟨hs, hsW⟩]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormMinimalFactorPoints
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def PrimitiveFormMinimalFactorPoints.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∀ (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
      (q : σ → Fin N → (Fin d → ℂ) → ℂ),
      (∀ j, AnalyticAt ℂ (a j) (A w)) → AnalyticAt ℂ δ (A w) → (∀ i j, AnalyticAt ℂ (q i j) (A w)) →
      (¬ ∀ᶠ y in 𝓝 (A w), δ y = 0) →
      (∀ᶠ z in 𝓝 w, z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) →
      (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
        (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) →
      (∀ i, ∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
      ∃ (n : ℕ) (b : Fin n → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (b j) (A w)) ∧
        (∀ᶠ z in 𝓝 w, z ∈ X → ℓ z ^ n + ∑ j, b j (A z) * ℓ z ^ (j : ℕ) = 0) ∧
        (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
          (Polynomial.X ^ n + ∑ j, Polynomial.C (b j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) ∧
        ∀ U ∈ 𝓝 w, ∀ᶠ y in 𝓝 (A w), δ y ≠ 0 → ∀ τ : ℂ, τ ^ n + ∑ j, b j y * τ ^ (j : ℕ) = 0 →
          (fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y) ∈ X ∩ U ∧
            A (fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y) = y ∧
            ℓ (fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y) = τ

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAnalyticRootBranch
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

noncomputable section

theorem AnalyticRootBranch.proof : AnalyticRootBranch.Statement := by
  intro d N a t₀ τ₀ ha hsep hroot
  set p : Polynomial ℂ := Polynomial.X ^ N + ∑ j, Polynomial.C (a j t₀) * Polynomial.X ^ (j : ℕ) with hp
  set F : (Fin d → ℂ) × ℂ → ℂ := fun v => v.2 ^ N + ∑ j, a j v.1 * v.2 ^ (j : ℕ) with hF
  have hFa : AnalyticAt ℂ F (t₀, τ₀) := by
    refine (analyticAt_snd.pow N).add (Finset.analyticAt_fun_sum _ fun j _ => ?_)
    exact ((ha j).comp (analyticAt_fst (p := (t₀, τ₀)))).mul (analyticAt_snd.pow _)
  have hcd : ContDiffAt ℂ 1 F (t₀, τ₀) := hFa.contDiffAt

  have hpe : ∀ s, p.eval s = F (t₀, s) := by
    intro s
    simp [hp, hF, Polynomial.eval_finsetSum]

  have hpart : fderiv ℂ F (t₀, τ₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ =
      (1 : ℂ →L[ℂ] ℂ).smulRight (p.derivative.eval τ₀) := by
    have h1 : HasFDerivAt (fun s : ℂ => F (t₀, s))
        (fderiv ℂ F (t₀, τ₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) τ₀ :=
      (hFa.differentiableAt.hasFDerivAt).comp τ₀
        ((hasFDerivAt_const t₀ τ₀).prodMk (hasFDerivAt_id τ₀))
    have h2 : (fun s : ℂ => F (t₀, s)) = fun s => p.eval s := funext fun s => (hpe s).symm
    rw [h2] at h1
    exact h1.unique (p.hasDerivAt τ₀).hasFDerivAt

  have hder : p.derivative.eval τ₀ ≠ 0 := by
    have h := hsep.eval₂_derivative_ne_zero (RingHom.id ℂ) (x := τ₀)
      (by rw [Polynomial.eval₂_id, hpe]; exact hroot)
    rwa [Polynomial.eval₂_id] at h
  have hinv : (fderiv ℂ F (t₀, τ₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [hpart]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ hder), ?_⟩
    ext; simp
  set ψ := hcd.implicitFunction one_ne_zero hinv with hψdef
  have hψt : ψ t₀ = τ₀ := hcd.implicitFunction_apply_self one_ne_zero hinv
  have hψcd : ContDiffAt ℂ 1 ψ t₀ := hcd.contDiffAt_implicitFunction one_ne_zero hinv
  obtain ⟨O, hOsub, hOo, ht₀O⟩ := eventually_nhds_iff.mp
    ((hcd.eventually_apply_implicitFunction one_ne_zero hinv).and (hψcd.eventually (by simp)))
  refine ⟨O, ψ, hOo, ht₀O, ?_, hψt, fun t ht => (hOsub t ht).1.trans hroot⟩
  refine RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn hOo fun t ht => ?_
  exact ((hOsub t ht).2.differentiableAt one_ne_zero).differentiableWithinAt

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
