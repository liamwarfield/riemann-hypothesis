module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHomogDimZeroPow
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularLocusDense
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionCluster
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoboundaryCriterion
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.AffineOfCone
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

noncomputable section

theorem SlabBound.affine : GroundTheory.Heights₂.Heights.SlabBound.Statement := by
  intro n d J A u hJ hA hu
  classical
  set φ : MvPolynomial (Fin d) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ J :=
    (GroundTheory.Heights₂.Heights.linProjHom J A : MvPolynomial (Fin d) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ J)
    with hφ
  set v : MvPolynomial (Fin n) ℂ ⧸ J := Ideal.Quotient.mk J (GroundTheory.Heights₂.Heights.linForm u) with hv
  have hv0 : v ≠ 0 := by
    rw [hv, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hu
  obtain ⟨p, hpm, hp⟩ := hA.finite.to_isIntegral v
  obtain ⟨q, hpq, hq⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hpm.ne_zero 0
  have hq0 : q.coeff 0 ≠ 0 := by
    intro h
    apply hq
    rw [map_zero, sub_zero]
    exact Polynomial.X_dvd_iff.mpr h
  have hqv : q.eval₂ φ v = 0 := by
    rw [hpq, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_X,
      Polynomial.eval₂_C, map_zero, sub_zero] at hp
    exact (mul_eq_zero.mp hp).resolve_left (pow_ne_zero _ hv0)
  refine ⟨q.coeff 0, hq0, fun R => ?_⟩
  let g : EuclideanSpace ℂ (Fin n) → ℂ := fun z =>
    ∑ i ∈ Finset.range (q.divX.natDegree + 1),
      eval (A.mulVec fun j => z j) (q.divX.coeff i) * (∑ j, u j * z j) ^ i
  have hg : Continuous g := by
    refine continuous_finsetSum _ fun i _ => ?_
    refine Continuous.mul ?_ ?_
    · exact (MvPolynomial.continuous_eval _).comp (by fun_prop)
    · fun_prop
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : EuclideanSpace ℂ (Fin n)) R).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨K, fun z hz hzR => ?_⟩
  let ev : MvPolynomial (Fin n) ℂ ⧸ J →+* ℂ :=
    Ideal.Quotient.lift J (eval fun j => z j) (fun a ha => hz a ha)
  have hevφ : ev.comp φ = eval (A.mulVec fun j => z j) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [ev, φ, GroundTheory.Heights₂.Heights.linProjHom]
    · intro i
      simp [ev, φ, GroundTheory.Heights₂.Heights.linProjHom, Matrix.mulVec, dotProduct]
  have hevv : ev v = ∑ j, u j * z j := by
    simp [ev, v, GroundTheory.Heights₂.Heights.linForm]
  have key : q.eval₂ (eval (A.mulVec fun j => z j)) (∑ j, u j * z j) = 0 := by
    have h1 := congrArg ev hqv
    rw [Polynomial.hom_eval₂, hevφ, hevv, map_zero] at h1
    exact h1
  have hsplit : eval (A.mulVec fun j => z j) (q.coeff 0) = -((∑ j, u j * z j) * g z) := by
    have h2 := congrArg (fun r => r.eval₂ (eval (A.mulVec fun j => z j)) (∑ j, u j * z j))
      (Polynomial.X_mul_divX_add q)
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C,
      key] at h2
    rw [Polynomial.eval₂_eq_sum_range] at h2
    linear_combination h2
  have hzb : z ∈ Metric.closedBall (0 : EuclideanSpace ℂ (Fin n)) R := mem_closedBall_zero_iff.mpr hzR
  rw [hsplit, norm_neg, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hK z hzb) (norm_nonneg _)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchInverseHolomorphic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

theorem BranchInverseHolomorphic.proof (hdim : BranchFillDimension.Statement)
    (hopen : NormalOpenMapping.Statement) (hreg : BranchInverseOffHypersurface.Statement)
    (hext : NormalRiemannExtension.Statement) (hirr : NormalLocallyIrreducible.Statement) :
    BranchInverseHolomorphic.Statement := by
  intro σ _ I h w k r φ B hI hIc hh hw hφd hφi hφZ hB hfill
  set Δ := Metric.ball (0 : Fin k → ℂ) r with hΔ
  have hk := hdim σ I h w k r φ B hI hh hw hφd hφi hφZ hB hfill
  set ψ : (σ → ℂ) → Fin k → ℂ := Function.invFunOn φ Δ with hψdef
  have hψφ : ∀ t ∈ Δ, ψ (φ t) = t := fun t ht => hφi.leftInvOn_invFunOn ht
  obtain ⟨O, hOo, hO⟩ := hopen σ I k Δ φ hI hIc hk Metric.isOpen_ball hφd hφi hφZ

  have hψc : ∀ z ∈ φ '' Δ, ContinuousWithinAt ψ (φ '' Δ) z := by
    rintro _ ⟨t, ht, rfl⟩
    rw [ContinuousWithinAt, hψφ t ht, tendsto_nhds]
    intro V hVo htV
    obtain ⟨O', hO'o, hO'⟩ := hopen σ I k (V ∩ Δ) φ hI hIc hk (hVo.inter Metric.isOpen_ball)
      (hφd.mono Set.inter_subset_right) (hφi.mono Set.inter_subset_right)
      (hφZ.mono_left Set.inter_subset_right)
    have hmem : φ t ∈ zeroSetIn I ∩ O' := hO' ▸ Set.mem_image_of_mem φ ⟨htV, ht⟩
    filter_upwards [inter_mem_nhdsWithin (φ '' Δ) (hO'o.mem_nhds hmem.2)] with z hz
    obtain ⟨⟨s, hs, rfl⟩, hzO'⟩ := hz
    have hs' : φ s ∈ φ '' (V ∩ Δ) := by rw [hO']; exact ⟨hφZ hs, hzO'⟩
    obtain ⟨s', hs'V, hss'⟩ := hs'
    rw [Set.mem_preimage, hψφ s hs, ← hφi hs'V.2 hs hss']
    exact hs'V.1
  obtain ⟨h', hh', hreg'⟩ := hreg σ I k hI hk
  have hψreg := hreg' Δ φ ψ Metric.isOpen_ball hφd hφi hφZ hψφ
  rw [hO] at hψreg hψc

  have hcoord : ∀ j : Fin k, ∃ g : (σ → ℂ) → ℂ, HolomorphicOnSubset g (zeroSetIn I ∩ O) ∧
      Set.EqOn g (fun z => ψ z j) ((zeroSetIn I ∩ O) \ {z | eval z h' = 0}) := by
    intro j
    refine hext σ I h' O (fun z => ψ z j) hI hIc hh' hOo ?_ ?_
    · intro z hz
      obtain ⟨U, hUo, hzU, F, hF, hFeq⟩ := hψreg z hz
      exact ⟨U, hUo, hzU, fun y => F y j, differentiableOn_pi.mp hF j,
        fun y hy => congrFun (hFeq hy) j⟩
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := r)).subset ?_
      rintro _ ⟨z, hz, rfl⟩
      have hz' : z ∈ φ '' Δ := by rw [hO]; exact hz.1
      obtain ⟨t, ht, rfl⟩ := hz'
      rw [Metric.mem_closedBall, dist_zero_right]
      show ‖ψ (φ t) j‖ ≤ r
      rw [hψφ t ht]
      exact (norm_le_pi_norm t j).trans (mem_ball_zero_iff.mp ht).le
  choose g hg hgeq using hcoord

  have hgψ : ∀ j, ∀ z ∈ zeroSetIn I ∩ O, g j z = ψ z j := by
    intro j z hz
    obtain ⟨B', -, hzB', hB'O, -, hdense⟩ := hirr σ I h' z hI hIc hh' hz.1 O (hOo.mem_nhds hz.2)
    set P := (zeroSetIn I ∩ B') \ {y | eval y h' = 0} with hP
    have hPsub : P ⊆ zeroSetIn I ∩ O := fun y hy => ⟨hy.1.1, hB'O hy.1.2⟩
    have : (𝓝[P] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hdense ⟨hz.1, hzB'⟩)
    have h1 : Tendsto (g j) (𝓝[P] z) (𝓝 (g j z)) := (((hg j).continuousWithinAt hz).mono hPsub).tendsto
    have h2 : Tendsto (fun y => ψ y j) (𝓝[P] z) (𝓝 (ψ z j)) :=
      (((continuous_apply j).continuousAt.comp_continuousWithinAt (hψc z hz)).mono hPsub).tendsto
    refine tendsto_nhds_unique h1 (h2.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hgeq j ⟨hPsub hy, hy.2⟩).symm
  refine ⟨ψ, ?_, hψφ⟩
  rw [hO]
  intro z hz
  choose U hUo hzU F hF hFeq using fun j => hg j z hz
  refine ⟨⋂ j, U j, isOpen_iInter_of_finite hUo, Set.mem_iInter.mpr hzU, fun y j => F j y,
    differentiableOn_pi.mpr fun j => (hF j).mono (Set.iInter_subset _ j), fun y hy => ?_⟩
  funext j
  show ψ y j = F j y
  rw [← hgψ j y hy.1]
  exact hFeq j ⟨hy.1, Set.mem_iInter.mp hy.2 j⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetPieceReachesCentre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem SheetPieceReachesCentre.proof : SheetPieceReachesCentre.Statement := by
  intro σ _ X w B d A D δ N U V hpar hU hV hcover hdisj hne
  obtain ⟨-, hwXB, hD, hDc, hmaps, hprop, hcentre, hδ, ⟨y₁, hy₁D, hy₁⟩, -, hchart, -⟩ := hpar
  set T : Set (σ → ℂ) := {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ U with hTdef

  have key : ∀ y ∈ D, y ∈ closure (A '' T) → ∃ x ∈ closure T, x ∈ X ∩ B ∧ A x = y := by
    intro y hyD hy
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hD y hyD
    have hKD : Metric.closedBall y (ε / 2) ⊆ D :=
      (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
    have hP := hprop _ hKD (isCompact_closedBall y (ε / 2))
    have hQsub : closure (T ∩ A ⁻¹' Metric.closedBall y (ε / 2)) ⊆
        {x | x ∈ X ∩ B ∧ A x ∈ Metric.closedBall y (ε / 2)} :=
      closure_minimal (fun x hx => ⟨hx.1.1.1, hx.2⟩) hP.isClosed
    have hQ : IsCompact (closure (T ∩ A ⁻¹' Metric.closedBall y (ε / 2))) :=
      hP.of_isClosed_subset isClosed_closure hQsub
    have hAQ : IsClosed (A '' closure (T ∩ A ⁻¹' Metric.closedBall y (ε / 2))) :=
      (hQ.image A.continuous).isClosed
    have hyK : y ∈ closure (A '' (T ∩ A ⁻¹' Metric.closedBall y (ε / 2))) := by
      rw [mem_closure_iff_nhds] at hy ⊢
      intro t ht
      obtain ⟨z, ⟨hzt, hzK⟩, x, hxT, rfl⟩ :=
        hy (t ∩ Metric.closedBall y (ε / 2)) (Filter.inter_mem ht (Metric.closedBall_mem_nhds y (half_pos hε)))
      exact ⟨A x, hzt, x, ⟨hxT, hzK⟩, rfl⟩
    obtain ⟨x, hxQ, rfl⟩ := closure_minimal (Set.image_mono subset_closure) hAQ hyK
    exact ⟨x, closure_mono Set.inter_subset_left hxQ, (hQsub hxQ).1, rfl⟩

  have hopen : IsOpen (A '' T) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, ⟨⟨hxXB, hδx⟩, hxU⟩, rfl⟩
    obtain ⟨O, V', g, hO, hV', hxV', hg, hAg, hXBV⟩ := hchart x hxXB hδx
    obtain ⟨y₀, hy₀O, hgy₀⟩ : x ∈ g '' O := hXBV ▸ ⟨hxXB, hxV'⟩
    have hAx : A x = y₀ := by rw [← hgy₀, hAg y₀ hy₀O]
    subst hAx
    have h1 : g ⁻¹' (U ∩ V') ∈ 𝓝 (A x) :=
      (hg (A x) hy₀O).continuousAt.preimage_mem_nhds (by rw [hgy₀]; exact (hU.inter hV').mem_nhds ⟨hxU, hxV'⟩)
    have h2 : δ ⁻¹' {0}ᶜ ∈ 𝓝 (A x) :=
      (hδ (A x) (hmaps hxXB)).continuousAt.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hδx)
    filter_upwards [h1, h2, hO.mem_nhds hy₀O] with y hy1 hy2 hy3
    have hgy : g y ∈ X ∩ B ∩ V' := hXBV ▸ ⟨y, hy3, rfl⟩
    refine ⟨g y, ⟨⟨hgy.1, ?_⟩, hy1.1⟩, hAg y hy3⟩
    rw [hAg y hy3]
    exact hy2

  have hreg : ∀ y ∈ D, IsRegularPointOf D y := fun y hy =>
    ⟨hy, d, ContinuousLinearMap.id ℂ _, D, D, id, hD, hD, hy, fun _ _ => analyticAt_id, fun _ _ => rfl,
      by rw [Set.inter_self, Set.image_id]⟩
  have hE : IsPreconnected (D \ {z | δ z = 0}) :=
    ManifoldZerosComplementConnected.proof (Fin d) D δ hDc hreg hδ ⟨y₁, hy₁D, hy₁⟩
  have hEsub : D \ {z | δ z = 0} ⊆ A '' T := by
    refine hE.subset_of_closure_inter_subset hopen ?_ ?_
    · obtain ⟨x₀, hx₀S, hx₀U⟩ := hne
      exact ⟨A x₀, ⟨hmaps hx₀S.1, hx₀S.2⟩, x₀, ⟨hx₀S, hx₀U⟩, rfl⟩
    · rintro y ⟨hy, hyD, hyδ⟩
      obtain ⟨x, hxcl, hxXB, rfl⟩ := key y hyD hy
      have hxS : x ∈ {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} := ⟨hxXB, hyδ⟩
      rcases hcover hxS with hxU | hxV
      · exact ⟨x, ⟨hxS, hxU⟩, rfl⟩
      · exfalso
        obtain ⟨z, hzV, hzS, hzU⟩ := mem_closure_iff.mp hxcl V hV hxV
        have hz : z ∈ {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ (U ∩ V) := ⟨hzS, hzU, hzV⟩
        rw [hdisj] at hz
        exact hz

  have hwD : A w ∈ D := hmaps hwXB
  have hwE : A w ∈ closure (D \ {z | δ z = 0}) := by
    by_contra hw
    rw [mem_closure_iff_nhds] at hw
    push Not at hw
    obtain ⟨t, ht, hte⟩ := hw
    have hzero : δ =ᶠ[𝓝 (A w)] 0 := by
      filter_upwards [ht, hD.mem_nhds hwD] with y hyt hyD
      by_contra hy
      exact (Set.not_nonempty_iff_eq_empty.mpr hte) ⟨y, hyt, hyD, hy⟩
    exact hy₁ (hδ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc hwD hzero hy₁D)
  obtain ⟨x, hxcl, hxXB, hAx⟩ := key (A w) hwD (closure_mono hEsub hwE)
  rw [← hcentre x hxXB hAx]
  exact hxcl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolGermPointIdealSpan
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

theorem hadamard_decomposition {σ : Type} [Fintype σ] {w : σ → ℂ} {f : (σ → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f w) :
    ∃ g : σ → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (g i) w) ∧
      ∀ᶠ z in 𝓝 w, f z = f w + ∑ i, (z i - w i) * g i z := by
  classical
  obtain ⟨p, r, hp⟩ := hf
  have hrad : p.shift.radius = p.radius := FormalMultilinearSeries.radius_shift p
  have hq : 0 < p.shift.radius := by rw [hrad]; exact lt_of_lt_of_le hp.r_pos hp.r_le
  have hG : HasFPowerSeriesOnBall p.shift.sum p.shift 0 p.shift.radius :=
    p.shift.hasFPowerSeriesOnBall hq
  refine ⟨fun i z => p.shift.sum (z - w) (Pi.single i 1), fun i => ?_, ?_⟩
  · have h2 : AnalyticAt ℂ (fun z : σ → ℂ => z - w) w := analyticAt_id.sub analyticAt_const
    have h3 : AnalyticAt ℂ p.shift.sum ((fun z : σ → ℂ => z - w) w) := by
      simpa using hG.analyticAt
    exact ((ContinuousLinearMap.apply ℂ ℂ (Pi.single i (1 : ℂ))).analyticAt _).comp
      (AnalyticAt.comp (g := p.shift.sum) (f := fun z : σ → ℂ => z - w) h3 h2)
  · filter_upwards [Metric.eball_mem_nhds w hp.r_pos] with z hz
    set y := z - w with hy
    have hy0 : y ∈ Metric.eball (0 : σ → ℂ) r := by
      rw [Metric.mem_eball] at hz ⊢
      rwa [edist_zero_right, hy, ← edist_eq_enorm_sub]
    have hy1 : y ∈ Metric.eball (0 : σ → ℂ) p.shift.radius :=
      Metric.eball_subset_eball (hrad ▸ hp.r_le) hy0
    have h1 := hp.hasSum hy0
    have h2 := hG.hasSum hy1
    rw [zero_add] at h2
    have h3 := (ContinuousLinearMap.apply ℂ ℂ y).hasSum h2
    have h4 : ∀ n, (ContinuousLinearMap.apply ℂ ℂ y) (p.shift n fun _ => y) =
        p (n + 1) fun _ => y := by
      intro n
      simp only [ContinuousLinearMap.apply_apply, FormalMultilinearSeries.shift,
        ContinuousMultilinearMap.curryRight_apply]
      congr 1
      funext j
      refine Fin.lastCases ?_ (fun k => ?_) j <;> simp
    simp only [h4, ContinuousLinearMap.apply_apply] at h3
    have h5 := (hasSum_nat_add_iff' 1).mpr h1
    simp only [Finset.range_one, Finset.sum_singleton, hp.coeff_zero] at h5
    have e := h5.unique h3
    have hwz : w + y = z := by rw [hy]; abel
    rw [hwz] at e
    have e2 : p.shift.sum y y = ∑ i, (z i - w i) * p.shift.sum y (Pi.single i 1) := by
      have hyy : p.shift.sum y y = p.shift.sum y (∑ i, Pi.single i (y i)) := by
        rw [Finset.univ_sum_single]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hyy, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (Pi.single i (y i) : σ → ℂ) = y i • Pi.single i 1 by
        ext j; by_cases h : j = i
        · subst h; simp
        · simp [h], map_smul, smul_eq_mul, hy, Pi.sub_apply]
    rw [← e2, ← e]
    ring

theorem HolGermPointIdealSpan.proof : HolGermPointIdealSpan.Statement := by
  intro σ _ w
  apply le_antisymm
  · rintro ⟨_, f, hf, rfl⟩ hφ
    have hfw : f w = 0 := hφ
    obtain ⟨g, hg, hfg⟩ := hadamard_decomposition hf
    have key : (⟨(f : Germ (𝓝 w) ℂ), f, hf, rfl⟩ : holGerms w) =
        ∑ i, polyGerm w (X i - C (w i)) * ⟨(g i : Germ (𝓝 w) ℂ), g i, hg i, rfl⟩ := by
      apply Subtype.ext
      change (f : Germ (𝓝 w) ℂ) = (holGerms w).subtype (∑ i, _)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_mul, Subring.coe_subtype]
      have hsum : ((fun z => ∑ i, (z i - w i) * g i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) =
          ∑ i, ((fun z : σ → ℂ => z i - w i : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) * (g i : Germ (𝓝 w) ℂ) := by
        change Germ.coeRingHom (𝓝 w) (fun z => ∑ i, (z i - w i) * g i z) = _
        set_option synthInstance.maxHeartbeats 100000 in
          rw [show (fun z => ∑ i, (z i - w i) * g i z : (σ → ℂ) → ℂ) =
            ∑ i, (fun z : σ → ℂ => z i - w i) * g i by
          funext z; simp [Finset.sum_apply], map_sum]
        rfl
      have hfe : (f : Germ (𝓝 w) ℂ) = ((fun z => ∑ i, (z i - w i) * g i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) :=
        Germ.coe_eq.mpr (hfg.mono fun z hz => by rw [hz, hfw, zero_add])
      rw [hfe, hsum]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      change _ = ((fun z : σ → ℂ => eval z (X i - C (w i)) : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)
      simp
    rw [key]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change holGermValue w (polyGerm w (X i - C (w i))) = 0
    rw [holGermValue_polyGerm]
    simp

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.IsAddHaarMeasureHausdorffMeasureEuclideanSpaceCo
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Measure

noncomputable section

theorem finrank_real_euclideanSpace_complex (d : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℂ (Fin d)) = 2 * d := by
  rw [((EuclideanSpace.equiv (Fin d) ℂ).toLinearEquiv.restrictScalars ℝ).finrank_eq]
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]

instance isAddHaarMeasure_hausdorffMeasure_euclideanSpace_complex (d : ℕ) :
    (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))).IsAddHaarMeasure := by
  have := isAddHaarMeasure_hausdorffMeasure (E := EuclideanSpace ℂ (Fin d))
  rwa [finrank_real_euclideanSpace_complex] at this

theorem map_hausdorffMeasure_euclideanSpace_apply (d : ℕ) (s : Set (Fin d → ℂ)) :
    (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))).map
        (EuclideanSpace.equiv (Fin d) ℂ) s =
      μH[((2 * d : ℕ) : ℝ)] (EuclideanSpace.equiv (Fin d) ℂ ⁻¹' s) :=
  (EuclideanSpace.equiv (Fin d) ℂ).toHomeomorph.toMeasurableEquiv.map_apply s

theorem nnreal_mul_ofReal_le (c : NNReal) (C η α : ℝ) :
    (c : ENNReal) * ENNReal.ofReal (C * η ^ α) ≤ ENNReal.ofReal (((c : ℝ) + 1) * C * η ^ α) := by
  have h1 : (c : ENNReal) ≤ ENNReal.ofReal ((c : ℝ) + 1) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  rw [mul_assoc, ENNReal.ofReal_mul (p := (c : ℝ) + 1) (by positivity)]
  exact mul_le_mul_of_nonneg_right h1 (zero_le)

theorem PolySublevel.equiv :
    GroundTheory.Heights₂.Heights.PolySublevel.Statement ↔ PolySublevel.Statement := by
  constructor
  · intro h d Q hQ R hR
    set e := EuclideanSpace.equiv (Fin d) ℂ
    set K := ‖(e : EuclideanSpace ℂ (Fin d) →L[ℂ] (Fin d → ℂ))‖
    have hK : 0 ≤ K := norm_nonneg _
    obtain ⟨C, α, hC, hα, hb⟩ := h d Q hQ ((K + 1) * R) (by positivity)
    have hc := isAddLeftInvariant_eq_smul
      ((μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))).map e)
      (volume : Measure (Fin d → ℂ))
    set c := addHaarScalarFactor
      ((μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))).map e)
      (volume : Measure (Fin d → ℂ))
    refine ⟨((c : ℝ) + 1) * C, α, by positivity, hα, fun η hη hη1 => ?_⟩
    calc _ ≤ μH[((2 * d : ℕ) : ℝ)]
          (e ⁻¹' {x : Fin d → ℂ | x ∈ Metric.ball 0 ((K + 1) * R) ∧ ‖eval x Q‖ ≤ η}) := by
          apply measure_mono
          rintro x ⟨hx, hxη⟩
          refine ⟨?_, hxη⟩
          rw [mem_ball_zero_iff] at hx ⊢
          calc ‖e x‖ = ‖(e : EuclideanSpace ℂ (Fin d) →L[ℂ] (Fin d → ℂ)) x‖ := rfl
            _ ≤ K * ‖x‖ := ContinuousLinearMap.le_opNorm _ x
            _ ≤ K * R := by gcongr
            _ < (K + 1) * R := by nlinarith
      _ = ((μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))).map e)
          {x : Fin d → ℂ | x ∈ Metric.ball 0 ((K + 1) * R) ∧ ‖eval x Q‖ ≤ η} :=
          (map_hausdorffMeasure_euclideanSpace_apply d _).symm
      _ = (c : ENNReal) *
          volume {x : Fin d → ℂ | x ∈ Metric.ball 0 ((K + 1) * R) ∧ ‖eval x Q‖ ≤ η} := by
          rw [hc]; rfl
      _ ≤ (c : ENNReal) * ENNReal.ofReal (C * η ^ α) := by gcongr; exact hb η hη hη1
      _ ≤ _ := nnreal_mul_ofReal_le c C η α
  · intro h d Q hQ R hR
    set e := EuclideanSpace.equiv (Fin d) ℂ
    set K := ‖(e.symm : (Fin d → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin d))‖
    have hK : 0 ≤ K := norm_nonneg _
    obtain ⟨C, α, hC, hα, hb⟩ := h d Q hQ ((K + 1) * R) (by positivity)
    have hc := isAddLeftInvariant_eq_smul (volume : Measure (Fin d → ℂ))
      ((μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))).map e)
    set c := addHaarScalarFactor (volume : Measure (Fin d → ℂ))
      ((μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))).map e)
    refine ⟨((c : ℝ) + 1) * C, α, by positivity, hα, fun η hη hη1 => ?_⟩
    calc _ = (c : ENNReal) * ((μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))).map e)
          {x : Fin d → ℂ | x ∈ Metric.ball 0 R ∧ ‖eval x Q‖ ≤ η} := by
          conv_lhs => rw [hc]
          rfl
      _ = (c : ENNReal) * μH[((2 * d : ℕ) : ℝ)]
          (e ⁻¹' {x : Fin d → ℂ | x ∈ Metric.ball 0 R ∧ ‖eval x Q‖ ≤ η}) := by
          rw [map_hausdorffMeasure_euclideanSpace_apply]
      _ ≤ (c : ENNReal) * μH[((2 * d : ℕ) : ℝ)]
          {x : EuclideanSpace ℂ (Fin d) | x ∈ Metric.ball 0 ((K + 1) * R) ∧
            ‖eval (fun i => x i) Q‖ ≤ η} := by
          gcongr
          rintro x ⟨hx, hxη⟩
          refine ⟨?_, hxη⟩
          rw [mem_ball_zero_iff] at hx ⊢
          calc ‖x‖ = ‖(e.symm : (Fin d → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin d)) (e x)‖ := by simp
            _ ≤ K * ‖e x‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ K * R := by gcongr
            _ < (K + 1) * R := by nlinarith
      _ ≤ (c : ENNReal) * ENNReal.ofReal (C * η ^ α) := by gcongr; exact hb η hη hη1
      _ ≤ _ := nnreal_mul_ofReal_le c C η α

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPolyGermPointPow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter Asymptotics

noncomputable section

namespace PolyGermPointPow

theorem coeff_eq_zero_of_isBigO {P : Polynomial ℂ} {k : ℕ}
    (h : (fun t => P.eval t) =O[𝓝 0] fun t : ℂ => ‖t‖ ^ k) : ∀ d < k, P.coeff d = 0 := by
  induction k with
  | zero => intro d hd; exact absurd hd (Nat.not_lt_zero _)
  | succ k ih =>
    have hn : (fun t : ℂ => ‖t‖) =O[𝓝 0] fun _ => (1 : ℝ) := (continuous_norm.tendsto (0 : ℂ)).isBigO_one ℝ
    have hk := ih (h.trans (by simpa [pow_succ] using (isBigO_refl (fun t : ℂ => ‖t‖ ^ k) _).mul hn))
    obtain ⟨Q, hQ⟩ := Polynomial.X_pow_dvd_iff.mpr hk
    intro d hd
    rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hd | hd
    · exact hk d hd
    rw [hd, hQ, Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, Polynomial.coeff_zero_eq_eval_zero]
    obtain ⟨c, hc⟩ := h.bound
    have h1 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖Q.eval t‖ ≤ c * ‖t‖ := by
      filter_upwards [nhdsWithin_le_nhds hc, self_mem_nhdsWithin] with t ht ht0
      rw [hQ, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, norm_mul, norm_pow, norm_pow,
        norm_norm, pow_succ] at ht
      have hp : 0 < ‖t‖ ^ k := pow_pos (norm_pos_iff.mpr ht0) k
      exact le_of_mul_le_mul_left (by linarith) hp
    have h2 : Tendsto (fun t => ‖Q.eval t‖) (𝓝[≠] 0) (𝓝 ‖Q.eval 0‖) :=
      ((Q.continuous.tendsto 0).norm).mono_left nhdsWithin_le_nhds
    have h3 : Tendsto (fun t : ℂ => c * ‖t‖) (𝓝[≠] 0) (𝓝 0) := by
      simpa using ((continuous_norm.tendsto (0 : ℂ)).const_mul c).mono_left nhdsWithin_le_nhds
    exact norm_le_zero_iff.mp (le_of_tendsto_of_tendsto h2 h3 h1)

theorem eval_smul_of_isHomogeneous {σ : Type} [Fintype σ] {h : MvPolynomial σ ℂ} {d : ℕ}
    (hh : h.IsHomogeneous d) (t : ℂ) (v : σ → ℂ) : eval (t • v) h = t ^ d * eval v h :=
  _root_.UpperTheory.Reformulated.B.HomogeneousEvalSmul.eval_smul_of_isHomogeneous hh t v

variable {σ : Type} [Fintype σ] (w : σ → ℂ)

def bigOIdeal (k : ℕ) : Ideal (holGerms w) where
  carrier := {φ | ∃ f : (σ → ℂ) → ℂ, (f : Germ (𝓝 w) ℂ) = (φ : Germ (𝓝 w) ℂ) ∧
    f =O[𝓝 w] fun z => ‖z - w‖ ^ k}
  add_mem' := by
    rintro φ ψ ⟨f, hf, hfO⟩ ⟨g, hg, hgO⟩
    exact ⟨f + g, by rw [Subring.coe_add, ← hf, ← hg]; rfl, hfO.add hgO⟩
  zero_mem' := ⟨0, rfl, isBigO_zero _ _⟩
  smul_mem' := by
    rintro c φ ⟨f, hf, hfO⟩
    obtain ⟨a, ha, hac⟩ := c.2
    refine ⟨a * f, ?_, ?_⟩
    · rw [smul_eq_mul, Subring.coe_mul, ← hf, ← hac]; rfl
    · show (fun z => a z * f z) =O[𝓝 w] fun z => ‖z - w‖ ^ k
      simpa using (ha.continuousAt.tendsto.isBigO_one ℝ).mul hfO

theorem bigOIdeal_zero : bigOIdeal w 0 = ⊤ := by
  refine eq_top_iff.mpr fun φ _ => ?_
  obtain ⟨f, hf, hfφ⟩ := φ.2
  exact ⟨f, hfφ, by simpa using hf.continuousAt.tendsto.isBigO_one ℝ⟩

theorem pointIdeal_le_bigOIdeal_one : holGermPointIdeal w ≤ bigOIdeal w 1 := by
  intro φ hφ
  obtain ⟨f, hf, hfφ⟩ := φ.2
  have h0 : f w = 0 := by
    have : (Germ.valueRingHom (x := w)) (f : Germ (𝓝 w) ℂ) = 0 := by rw [hfφ]; exact hφ
    exact this
  refine ⟨f, hfφ, ?_⟩
  have := hf.differentiableAt.hasFDerivAt.isBigO_sub
  simp only [h0, sub_zero] at this
  simpa using this.norm_right

theorem bigOIdeal_mul_le (a b : ℕ) : bigOIdeal w a * bigOIdeal w b ≤ bigOIdeal w (a + b) := by
  rw [Ideal.mul_le]
  rintro φ ⟨f, hf, hfO⟩ ψ ⟨g, hg, hgO⟩
  refine ⟨f * g, ?_, ?_⟩
  · rw [Subring.coe_mul, ← hf, ← hg]; rfl
  · show (fun z => f z * g z) =O[𝓝 w] fun z => ‖z - w‖ ^ (a + b)
    simpa [pow_add] using hfO.mul hgO

theorem pointIdeal_pow_le (k : ℕ) : holGermPointIdeal w ^ k ≤ bigOIdeal w k := by
  induction k with
  | zero => rw [pow_zero, Ideal.one_eq_top, bigOIdeal_zero]
  | succ k ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono ih (pointIdeal_le_bigOIdeal_one w)).trans (bigOIdeal_mul_le w k 1)

theorem mem_pow_ker_of_isBigO {k : ℕ} {q : MvPolynomial σ ℂ}
    (hq : (fun z => eval z q) =O[𝓝 w] fun z => ‖z - w‖ ^ k) :
    q ∈ RingHom.ker (MvPolynomial.eval w) ^ k := by
  set q' := bind₁ (fun i => X i + C (w i)) q with hq'def
  have hev : ∀ y, eval y q' = eval (y + w) q := by
    intro y
    rw [hq'def, show (eval y : MvPolynomial σ ℂ →+* ℂ) = eval₂Hom (RingHom.id ℂ) y from rfl, eval₂Hom_bind₁]
    have hfun : (fun i => eval₂Hom (RingHom.id ℂ) y (X i + C (w i))) = y + w := by
      ext i
      simp only [map_add (f := _), eval₂Hom_X', eval₂Hom_C, RingHom.id_apply, Pi.add_apply]
    rw [hfun]
    rfl

  have hcomp : ∀ d < k, homogeneousComponent d q' = 0 := by
    intro d hd
    by_cases hdT : d ∈ Finset.range (q'.totalDegree + 1)
    swap
    · exact homogeneousComponent_eq_zero _ _ (by simpa [Nat.lt_succ_iff] using hdT)
    refine MvPolynomial.funext fun v => ?_
    let P : Polynomial ℂ := ∑ e ∈ Finset.range (q'.totalDegree + 1),
      Polynomial.monomial e (eval v (homogeneousComponent e q'))
    have hP : ∀ t, P.eval t = eval (t • v + w) q := by
      intro t
      rw [← hev]
      conv_rhs => rw [← sum_homogeneousComponent q']
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_monomial, map_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous e q'), mul_comm]
    have hT : Tendsto (fun t : ℂ => t • v + w) (𝓝 0) (𝓝 w) := by
      simpa using ((continuous_id.smul continuous_const).add continuous_const).tendsto (0 : ℂ)
        (f := fun t : ℂ => t • v + w)
    have hPO : (fun t => P.eval t) =O[𝓝 0] fun t : ℂ => ‖t‖ ^ k := by
      simp_rw [hP]
      refine (hq.comp_tendsto hT).trans (IsBigO.of_bound (‖v‖ ^ k) (Eventually.of_forall fun t => ?_))
      simp [norm_smul, mul_pow, mul_comm]
    have hc := coeff_eq_zero_of_isBigO hPO d hd
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
      Finsupp.single_apply, Finset.sum_ite_eq', if_pos hdT] at hc
    simpa using hc
  have hmem : q' ∈ idealOfVars σ ℂ ^ k := by
    refine (mem_pow_idealOfVars_iff' k q').mpr fun x hx => ?_
    have := congrArg (AddMonoidAlgebra.coeff · x) (hcomp _ hx)
    simpa [coeff_homogeneousComponent, AddMonoidAlgebra.coeff] using this
  have hback : bind₁ (fun i => X i - C (w i)) q' = q := by
    rw [hq'def, bind₁_bind₁]
    simp [bind₁_X_right]
  have := Ideal.mem_map_of_mem (bind₁ (fun i => (X i - C (w i) : MvPolynomial σ ℂ))) hmem
  rw [Ideal.map_pow, idealOfVars, Ideal.map_span, ← Set.range_comp, hback] at this
  rw [GroundTheory.Heights₂.Heights.GradientAtPoint.ker_eval_eq_span]
  simpa [Function.comp_def, bind₁_X_right] using this

end PolyGermPointPow

theorem PolyGermPointPow.proof : PolyGermPointPow.Statement := by
  intro σ _ w k q hq
  obtain ⟨f, hf, hfO⟩ := PolyGermPointPow.pointIdeal_pow_le w k hq
  have hf' : (f : Germ (𝓝 w) ℂ) = ((fun z => eval z q : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) := hf
  exact PolyGermPointPow.mem_pow_ker_of_isBigO w (hfO.congr' (Germ.coe_eq.mp hf') EventuallyEq.rfl)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetPieceProductAnalytic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter

noncomputable section

namespace SheetPieceProductAnalytic

def tailL (d : ℕ) : (Fin (d + 1) → ℂ) →L[ℂ] (Fin d → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ

theorem tailL_apply {d : ℕ} (p : Fin (d + 1) → ℂ) (i : Fin d) : tailL d p i = p i.succ := rfl

theorem tailL_cons {d : ℕ} (a : ℂ) (y : Fin d → ℂ) : tailL d (Fin.cons a y) = y := by
  ext i
  simp [tailL_apply]

theorem cons_tailL {d : ℕ} (p : Fin (d + 1) → ℂ) : (Fin.cons (p 0) (tailL d p) : Fin (d + 1) → ℂ) = p := by
  ext i
  cases i using Fin.cases <;> simp [tailL_apply]

def prodFn {σ : Type} [Fintype σ] (X B U : Set (σ → ℂ)) {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (ℓ : (σ → ℂ) →L[ℂ] ℂ) (p : Fin (d + 1) → ℂ) : ℂ :=
  ∏ᶠ x ∈ {x | x ∈ X ∩ B ∧ x ∈ U ∧ A x = tailL d p}, (p 0 - ℓ x)

theorem exists_ne_zero_of_open {d : ℕ} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ}
    (hδ : AnalyticOnNhd ℂ δ D) (hD : IsPreconnected D) (hne : ∃ y ∈ D, δ y ≠ 0)
    (V : Set (Fin (d + 1) → ℂ)) (hV : IsOpen V) (hVW : V ⊆ tailL d ⁻¹' D) (hVne : V.Nonempty) :
    ∃ p ∈ V, δ (tailL d p) ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨p, hp⟩ := hVne
  have hc : Continuous fun y : Fin d → ℂ => (Fin.cons (p 0) y : Fin (d + 1) → ℂ) := by
    refine continuous_pi fun i => ?_
    cases i using Fin.cases
    · simpa using continuous_const
    · simpa using continuous_apply _
  have hev : δ =ᶠ[𝓝 (tailL d p)] 0 := by
    have hmem : (fun y : Fin d → ℂ => (Fin.cons (p 0) y : Fin (d + 1) → ℂ)) ⁻¹' V ∈ 𝓝 (tailL d p) := by
      refine hc.continuousAt.preimage_mem_nhds ?_
      show V ∈ 𝓝 (Fin.cons (p 0) (tailL d p) : Fin (d + 1) → ℂ)
      rw [cons_tailL]
      exact hV.mem_nhds hp
    filter_upwards [hmem] with y hy
    have := h _ hy
    rwa [tailL_cons] at this
  obtain ⟨y, hy, hy0⟩ := hne
  exact hy0 (hδ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hD (hVW hp) hev hy)

theorem differentiableAt_prodFn (hsec : UnbranchedFibreSections.Statement)
    {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {w : σ → ℂ} {B : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ} {N : ℕ}
    {U V : Set (σ → ℂ)} (ℓ : (σ → ℂ) →L[ℂ] ℂ)
    (hP : IsLocalParametrisation X w B A D δ N) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ⊆ U ∪ V)
    (hdisj : {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ (U ∩ V) = ∅)
    {p₀ : Fin (d + 1) → ℂ} (hp₀ : tailL d p₀ ∈ D) (hδp₀ : δ (tailL d p₀) ≠ 0) :
    DifferentiableAt ℂ (prodFn X B U A ℓ) p₀ := by
  classical
  obtain ⟨r, g, hr, -, hrδ, hg, hfib⟩ := hsec σ X w B d A D δ N hP _ hp₀ hδp₀
  set y₀ := tailL d p₀ with hy₀def
  have hy₀ : y₀ ∈ ball y₀ r := mem_ball_self hr
  have hconst : ∀ i, ∀ y ∈ ball y₀ r, (g i y ∈ U ↔ g i y₀ ∈ U) := by
    intro i
    have hgc : ContinuousOn (g i) (ball y₀ r) := (hg i).continuousOn
    have hS : ∀ y ∈ ball y₀ r, g i y ∈ X ∩ B ∧ δ (A (g i y)) ≠ 0 := by
      intro y hy
      have hx : g i y ∈ {x | x ∈ X ∩ B ∧ A x = y} := by
        rw [(hfib y hy).2]
        exact ⟨i, rfl⟩
      exact ⟨hx.1, by rw [hx.2]; exact hrδ y hy⟩
    have hopU := hgc.isOpen_inter_preimage isOpen_ball hU
    have hopV := hgc.isOpen_inter_preimage isOpen_ball hV
    have hdj : Disjoint (ball y₀ r ∩ g i ⁻¹' U) (ball y₀ r ∩ g i ⁻¹' V) := by
      rw [Set.disjoint_left]
      rintro y ⟨hy, hyU⟩ ⟨-, hyV⟩
      have : g i y ∈ {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ (U ∩ V) := ⟨hS y hy, hyU, hyV⟩
      rw [hdisj] at this
      exact this
    have hcv : ball y₀ r ⊆ (ball y₀ r ∩ g i ⁻¹' U) ∪ (ball y₀ r ∩ g i ⁻¹' V) := by
      intro y hy
      rcases hcov (hS y hy) with h | h
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩
    have hc : IsPreconnected (ball y₀ r) := (convex_ball y₀ r).isPreconnected
    intro y hy
    constructor
    · intro hyU
      by_contra hy0U
      have hy0V : y₀ ∈ ball y₀ r ∩ g i ⁻¹' V := (hcv hy₀).resolve_left fun h => hy0U h.2
      have hsub := hc.subset_right_of_subset_union hopU hopV hdj hcv ⟨y₀, hy₀, hy0V⟩
      exact Set.disjoint_left.1 hdj ⟨hy, hyU⟩ (hsub hy)
    · intro hy0U
      exact (hc.subset_left_of_subset_union hopU hopV hdj hcv ⟨y₀, hy₀, hy₀, hy0U⟩ hy).2
  set I : Finset (Fin N) := Finset.univ.filter fun i => g i y₀ ∈ U with hIdef
  have hrep : ∀ p : Fin (d + 1) → ℂ, tailL d p ∈ ball y₀ r →
      prodFn X B U A ℓ p = ∏ i ∈ I, (p 0 - ℓ (g i (tailL d p))) := by
    intro p hp
    have hset : {x | x ∈ X ∩ B ∧ x ∈ U ∧ A x = tailL d p} =
        (fun i => g i (tailL d p)) '' (I : Set (Fin N)) := by
      ext x
      constructor
      · rintro ⟨hxB, hxU, hxA⟩
        have hx : x ∈ Set.range (fun i => g i (tailL d p)) := by
          rw [← (hfib _ hp).2]
          exact ⟨hxB, hxA⟩
        obtain ⟨i, rfl⟩ := hx
        exact ⟨i, by simpa [hIdef] using (hconst i _ hp).1 hxU, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        have hx : g i (tailL d p) ∈ {x | x ∈ X ∩ B ∧ A x = tailL d p} := by
          rw [(hfib _ hp).2]
          exact ⟨i, rfl⟩
        exact ⟨hx.1, (hconst i _ hp).2 (by simpa [hIdef] using hi), hx.2⟩
    unfold prodFn
    rw [hset, finprod_mem_image ((hfib _ hp).1.injOn), finprod_mem_coe_finset]
  have hev : prodFn X B U A ℓ =ᶠ[𝓝 p₀] fun p => ∏ i ∈ I, (p 0 - ℓ (g i (tailL d p))) := by
    have hmem : tailL d ⁻¹' ball y₀ r ∈ 𝓝 p₀ :=
      (tailL d).continuous.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds hy₀)
    filter_upwards [hmem] with p hp using hrep p hp
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  have hfac : ∀ i, DifferentiableAt ℂ (fun p : Fin (d + 1) → ℂ => p 0 - ℓ (g i (tailL d p))) p₀ := by
    intro i
    have h1 : DifferentiableAt ℂ (fun p : Fin (d + 1) → ℂ => p 0) p₀ := differentiableAt_apply 0 p₀
    have h2 : DifferentiableAt ℂ (fun p => ℓ (g i (tailL d p))) p₀ :=
      ℓ.differentiableAt.comp _ (((hg i) _ hy₀).differentiableAt.comp _ (tailL d).differentiableAt)
    exact h1.sub h2
  refine Finset.induction_on I ?_ ?_
  · simp
  · intro j s hj ih
    simp only [Finset.prod_insert hj]
    exact (hfac j).mul ih

theorem isBounded_prodFn {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {w : σ → ℂ} {B : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ} {N : ℕ}
    (U : Set (σ → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ)
    (hP : IsLocalParametrisation X w B A D δ N) {p₀ : Fin (d + 1) → ℂ} (hp₀ : tailL d p₀ ∈ D) :
    ∃ Nb ∈ 𝓝 p₀, Bornology.IsBounded
      (prodFn X B U A ℓ '' (Nb ∩ tailL d ⁻¹' D ∩ {p | δ (tailL d p) ≠ 0})) := by
  obtain ⟨-, -, hD, -, -, hprop, -, -, -, hcard, -, -⟩ := hP
  obtain ⟨ρ, hρ, hρD⟩ := Metric.isOpen_iff.1 hD _ hp₀
  set y₀ := tailL d p₀ with hy₀def
  have hK : IsCompact {x | x ∈ X ∩ B ∧ A x ∈ closedBall y₀ (ρ / 2)} :=
    hprop _ ((closedBall_subset_ball (half_lt_self hρ)).trans hρD) (isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 (hK.image ℓ.continuous).isBounded
  set C : ℝ := max 1 (‖p₀ 0‖ + 1 + M) with hCdef
  refine ⟨tailL d ⁻¹' ball y₀ (ρ / 2) ∩ {p | ‖p 0‖ < ‖p₀ 0‖ + 1}, ?_, ?_⟩
  · refine Filter.inter_mem ((tailL d).continuous.continuousAt.preimage_mem_nhds
      (isOpen_ball.mem_nhds (mem_ball_self (half_pos hρ)))) ?_
    exact (isOpen_lt (continuous_norm.comp (continuous_apply 0)) continuous_const).mem_nhds (by simp)
  rw [isBounded_iff_forall_norm_le]
  refine ⟨C ^ N, ?_⟩
  rintro _ ⟨p, ⟨⟨⟨hpb, hpn⟩, hpD⟩, hpδ⟩, rfl⟩
  have hpn' : ‖p 0‖ < ‖p₀ 0‖ + 1 := hpn
  have hsub : {x | x ∈ X ∩ B ∧ x ∈ U ∧ A x = tailL d p} ⊆ {x | x ∈ X ∩ B ∧ A x = tailL d p} :=
    fun x hx => ⟨hx.1, hx.2.2⟩
  have hfin : {x | x ∈ X ∩ B ∧ A x = tailL d p}.encard = N := hcard _ hpD hpδ
  have hsfin : {x | x ∈ X ∩ B ∧ x ∈ U ∧ A x = tailL d p}.Finite :=
    (Set.finite_of_encard_eq_coe hfin).subset hsub
  have hcardle : hsfin.toFinset.card ≤ N := by
    have h1 := Set.encard_le_encard hsub
    rw [hfin, ← hsfin.coe_toFinset, Set.encard_coe_eq_coe_finsetCard] at h1
    exact_mod_cast h1
  have hbd : ∀ x ∈ hsfin.toFinset, ‖p 0 - ℓ x‖ ≤ C := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    have hxK : x ∈ {x | x ∈ X ∩ B ∧ A x ∈ closedBall y₀ (ρ / 2)} :=
      ⟨hx.1, by rw [hx.2.2]; exact ball_subset_closedBall hpb⟩
    have hMx := hM _ ⟨x, hxK, rfl⟩
    calc ‖p 0 - ℓ x‖ ≤ ‖p 0‖ + ‖ℓ x‖ := norm_sub_le _ _
      _ ≤ ‖p₀ 0‖ + 1 + M := by linarith
      _ ≤ C := le_max_right _ _
  unfold prodFn
  rw [finprod_mem_eq_finite_toFinset_prod _ hsfin]
  calc ‖∏ x ∈ hsfin.toFinset, (p 0 - ℓ x)‖ ≤ ∏ x ∈ hsfin.toFinset, ‖p 0 - ℓ x‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ _x ∈ hsfin.toFinset, C := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hbd
    _ = C ^ hsfin.toFinset.card := Finset.prod_const C
    _ ≤ C ^ N := pow_le_pow_right₀ (le_max_left _ _) hcardle

end SheetPieceProductAnalytic


open SheetPieceProductAnalytic in
theorem SheetPieceProductAnalytic.proof (hsec : UnbranchedFibreSections.Statement) :
    SheetPieceProductAnalytic.Statement := by
  intro σ _ X w B d A D δ N U V ℓ hP hU hV hcov hdisj
  have hP' := hP
  obtain ⟨-, -, hD, hDc, -, -, -, hδ, hne, -, -, -⟩ := hP'
  have hW : IsOpen (tailL d ⁻¹' D) := hD.preimage (tailL d).continuous
  have hgd : DifferentiableOn ℂ (fun p => δ (tailL d p)) (tailL d ⁻¹' D) := fun p hp =>
    ((hδ _ hp).differentiableAt.comp p (tailL d).differentiableAt).differentiableWithinAt
  obtain ⟨F, hF, hFG⟩ := RiemannExtensionAnalytic.proof (d + 1) (tailL d ⁻¹' D) (fun p => δ (tailL d p))
    (prodFn X B U A ℓ) hW hgd (fun V' hV' hsub hne' => exists_ne_zero_of_open hδ hDc hne V' hV' hsub hne')
    (fun p hp => (differentiableAt_prodFn hsec ℓ hP hU hV hcov hdisj hp.1 hp.2).differentiableWithinAt)
    (fun p hp => isBounded_prodFn U ℓ hP hp)
  have hFa : AnalyticOnNhd ℂ F (tailL d ⁻¹' D) := RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn hW hF
  have hcons : ∀ z, tailL d (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ) = A z := fun z => tailL_cons _ _
  refine ⟨fun z => F (Fin.cons (ℓ z) (A z)), fun z hz => ?_, fun z hz hδz => ?_⟩
  · have hm : (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ) ∈ tailL d ⁻¹' D := by
      rw [Set.mem_preimage, hcons]
      exact hz
    have hlin : AnalyticAt ℂ (fun z => (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ)) z := by
      rw [analyticAt_pi_iff]
      intro i
      cases i using Fin.cases
      · simpa using ℓ.analyticAt z
      · rename_i j
        simp only [Fin.cons_succ]
        exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) j).comp A).analyticAt z
    exact AnalyticAt.comp (g := F) (f := fun z => (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ)) (hFa _ hm) hlin
  · have hm : (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ) ∈
        tailL d ⁻¹' D ∩ {p | δ (tailL d p) ≠ 0} := by
      refine ⟨?_, ?_⟩
      · rw [Set.mem_preimage, hcons]
        exact hz
      · show δ (tailL d _) ≠ 0
        rw [hcons]
        exact hδz
    show F _ = _
    rw [hFG hm]
    simp only [prodFn, hcons, Fin.cons_zero]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolGermsNoetherian
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem HolGermsNoetherian.proof (hN : AnalyticGermsNoetherian.Statement) : HolGermsNoetherian.Statement :=
  fun σ _ w => hN σ w

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
