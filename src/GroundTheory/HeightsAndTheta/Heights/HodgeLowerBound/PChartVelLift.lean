module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StChartVelLift

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PChartVelLift
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem hasDerivAt_eval_comp {σ : Type*} [Fintype σ] (f : MvPolynomial σ ℂ) {γ : ℂ → σ → ℂ} {w : σ → ℂ} {t : ℂ}
    (hγ : HasDerivAt γ w t) :
    HasDerivAt (fun s => eval (γ s) f) (∑ i, eval (γ t) (pderiv i f) * w i) t := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const t a
  | add p q hp hq =>
    have hf : (fun s => eval (γ s) (p + q)) = fun s => eval (γ s) p + eval (γ s) q := by
      funext s
      simp
    rw [hf]
    refine (hp.add hq).congr_deriv ?_
    simp only [map_add (f := _), add_mul, Finset.sum_add_distrib]
  | mul_X p n hp =>
    have hn : HasDerivAt (fun s => γ s n) (w n) t := hasDerivAt_pi.1 hγ n
    have hf : (fun s => eval (γ s) (p * X n)) = fun s => eval (γ s) p * γ s n := by
      funext s
      simp
    rw [hf]
    refine (hp.mul hn).congr_deriv ?_
    have hs : ∑ i, eval (γ t) (pderiv i (p * X n)) * w i =
        ∑ i, eval (γ t) (pderiv i p) * w i * γ t n + ∑ i, eval (γ t) p * ((Pi.single n (1 : ℂ) : σ → ℂ) i * w i) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add (f := _), map_mul, eval_X]
      by_cases h : i = n
      · subst h
        simp
        ring
      · simp [h, Ne.symm h]
        ring
    rw [hs, ← Finset.mul_sum, ← Finset.sum_mul]
    congr 2
    simp [Pi.single_apply]

theorem ChartVelLift.proof (hP : ProjHoloLocal.Statement) : ChartVelLift.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X k y hy v hv
  classical
  have hcompat : ReciprocityTheory.AnForm.M.IsCompatChart X.M.atlas (X.S.R.chart k) := X.S.R.compat k
  have hx : (X.S.R.chart k).symm y ∈ (X.S.R.chart k).source := (X.S.R.chart k).map_target hy
  obtain ⟨U, hUo, hxU, s, hs, hshol⟩ := X.M.sections ((X.S.R.chart k).symm y)
  obtain ⟨j, hj⟩ := X.M.atlas.cover ((X.S.R.chart k).symm y)

  set V : Set (Fin D.n → ℂ) := (X.S.R.chart k).target ∩
    (X.S.R.chart k).symm ⁻¹' (U ∩ (X.M.atlas.chart j).source) with hV
  have hVo : IsOpen V := (X.S.R.chart k).continuousOn_symm.isOpen_inter_preimage (X.S.R.chart k).open_target
    (hUo.inter (X.M.atlas.chart j).open_source)

  have hanal : ∀ u ∈ V, ∀ p, AnalyticAt ℂ (fun u => s ((X.S.R.chart k).symm u) p) u := by
    intro u hu p
    have h1 : AnalyticAt ℂ (X.M.atlas.chart j ∘ (X.S.R.chart k).symm) u :=
      (hcompat j).2 u ⟨hu.1, hu.2.2⟩
    have h2 : AnalyticAt ℂ ((fun y' => s y' p) ∘ (X.M.atlas.chart j).symm)
        ((X.M.atlas.chart j ∘ (X.S.R.chart k).symm) u) := by
      refine hshol p j _ ⟨(X.M.atlas.chart j).map_source hu.2.2, ?_⟩
      show (X.M.atlas.chart j).symm ((X.M.atlas.chart j) ((X.S.R.chart k).symm u)) ∈ U
      rw [(X.M.atlas.chart j).left_inv hu.2.2]
      exact hu.2.1
    refine (h2.comp h1).congr ?_
    filter_upwards [hVo.mem_nhds hu] with u' hu'
    simp only [Function.comp_apply]
    rw [(X.M.atlas.chart j).left_inv hu'.2.2]

  set L : ℂ → Fin D.n → ℂ := fun σ => y + σ • v with hL
  have hLd : ∀ σ, HasDerivAt L v σ := fun σ => by
    have h := ((hasDerivAt_id σ).smul_const v).const_add y
    simp only [id, one_smul] at h
    exact h
  have hL0 : L 0 = y := by simp [hL]
  set T : Set ℂ := L ⁻¹' V with hT
  have hTo : IsOpen T := hVo.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have hT0 : (0 : ℂ) ∈ T := by
    show L 0 ∈ V
    rw [hL0]
    exact ⟨hy, hxU, hj⟩
  set γ : ℂ → (Σ k, ι k) → ℂ := fun σ => s ((X.S.R.chart k).symm (L σ)) with hγdef
  have hγd : ∀ σ ∈ T, DifferentiableAt ℂ γ σ := fun σ hσ =>
    differentiableAt_pi.2 fun p => (hanal (L σ) hσ p).differentiableAt.comp σ (hLd σ).differentiableAt
  have hγmem : ∀ σ ∈ T, γ σ ∈ mcPts (mCoordIdeal D.y) ∧
      X.M.proj (γ σ) = (X.S.R.chart k).symm (L σ) := fun σ hσ => hs _ hσ.2.1
  have hγ0 : γ 0 = s ((X.S.R.chart k).symm y) := by simp [hγdef, hL0]
  have hγw : HasDerivAt γ (deriv γ 0) 0 := (hγd 0 hT0).hasDerivAt
  have hTn : T ∈ 𝓝 (0 : ℂ) := hTo.mem_nhds hT0

  have hline : (fun σ => X.S.R.chart k (X.M.proj (γ σ))) =ᶠ[𝓝 0] L := by
    filter_upwards [hTn] with σ hσ
    rw [(hγmem σ hσ).2, (X.S.R.chart k).right_inv hσ.1]
  have hz : γ 0 ∈ mcPts (mCoordIdeal D.y) := (hγmem 0 hT0).1
  have hpz : X.M.proj (γ 0) = (X.S.R.chart k).symm y := by rw [(hγmem 0 hT0).2, hL0]
  refine ⟨γ 0, hz, hpz, deriv γ 0, ⟨γ, rfl, hγw, ?_, (hLd 0).congr_of_eventuallyEq hline⟩, ?_, ?_⟩
  · filter_upwards [hTn] with σ hσ
    exact ⟨hγd σ hσ, (hγmem σ hσ).1⟩
  ·
    intro f hf
    have hder := hasDerivAt_eval_comp (map (Int.castRingHom ℂ) f) hγw
    have hzero : (fun σ => eval (γ σ) (map (Int.castRingHom ℂ) f)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
      filter_upwards [hTn] with σ hσ
      exact (hγmem σ hσ).1.2 f hf
    exact hder.unique ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hzero)
  ·
    intro c hwc
    obtain ⟨W, hWo, hzW, F, hFd, hF⟩ :=
      hP II Ψ K ι Ω E D X.M (X.S.R.chart k) hcompat (γ 0) hz (by rw [hpz]; exact hx)
    have hFz : HasFDerivAt F (fderiv ℂ F (γ 0)) (γ 0) :=
      (hFd.differentiableAt (hWo.mem_nhds hzW)).hasFDerivAt

    have hWγ : ∀ᶠ σ in 𝓝 (0 : ℂ), γ σ ∈ W := hγw.continuousAt.preimage_mem_nhds (hWo.mem_nhds hzW)
    have h1 : fderiv ℂ F (γ 0) (deriv γ 0) = v := by
      refine (hFz.comp_hasDerivAt (0 : ℂ) hγw).unique ((hLd 0).congr_of_eventuallyEq ?_)
      filter_upwards [hTn, hWγ, hline] with σ hσ hσW hσl
      rw [Function.comp_apply, ← (hF (γ σ) ⟨hσW, (hγmem σ hσ).1⟩).2]
      exact hσl

    set δ : ℂ → (Σ k, ι k) → ℂ := fun σ => torusSmul (fun k => Complex.exp (σ * c k)) (γ 0) with hδ
    have hδ0 : δ 0 = γ 0 := by
      funext p
      simp [hδ, torusSmul]
    have hδd : HasDerivAt δ (torusSmul c (γ 0)) 0 := by
      refine hasDerivAt_pi.2 fun p => ?_
      have h := (((hasDerivAt_id (0 : ℂ)).mul_const (c p.1)).cexp).mul_const (γ 0 p)
      simpa [hδ, torusSmul] using h
    have hδmem : ∀ σ, δ σ ∈ mcPts (mCoordIdeal D.y) := fun σ =>
      ComponentDataEquivalence.mcPts_torus D.arith.2.1.2.1 hz fun k => Complex.exp_ne_zero _
    have hδproj : ∀ σ, X.M.proj (δ σ) = X.M.proj (γ 0) := fun σ =>
      ((X.M.fibre (γ 0) hz (δ σ) (hδmem σ)).2 ⟨_, fun k => Complex.exp_ne_zero _, rfl⟩).symm
    have hWδ : ∀ᶠ σ in 𝓝 (0 : ℂ), δ σ ∈ W := by
      have := hδd.continuousAt.preimage_mem_nhds (hWo.mem_nhds (hδ0 ▸ hzW))
      exact this
    have h2 : fderiv ℂ F (γ 0) (torusSmul c (γ 0)) = 0 := by
      have hFz' : HasFDerivAt F (fderiv ℂ F (γ 0)) (δ 0) := hδ0 ▸ hFz
      refine (hFz'.comp_hasDerivAt (0 : ℂ) hδd).unique
        ((hasDerivAt_const (0 : ℂ) (X.S.R.chart k (X.M.proj (γ 0)))).congr_of_eventuallyEq ?_)
      filter_upwards [hWδ] with σ hσW
      rw [Function.comp_apply, ← (hF (δ σ) ⟨hσW, hδmem σ⟩).2, hδproj σ]
    exact hv (h1.symm.trans (hwc ▸ h2))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelFibreSumAeSheet
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

namespace ModelFibreSumAlmostEverywhere

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}
  (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

theorem exists_sheet (L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (r : ℝ) (E : Set M.Xc) (hP : IsArithVar P (e + 1))
    (hL : IsSmoothHerm L) (x : M.Xc) (hx : x ∉ modelBad M Ψ E) :
    ∃ γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ, IsSheet P Ψ (modelQ M Ψ x) (modelW M Ψ x) γ ∧
      maDensity (fun (_ : Fin e) y' => r * Real.log (L.h (γ y'))) (modelQ M Ψ x) =
        pushDens M.atlas (fun _ => modelPot M L r) (modelQ M Ψ) x := by
  classical
  obtain ⟨k0⟩ := hP.1
  have hPh : IsMultiHomogIdeal P := hP.2.1.2.1
  set j := chartIdx M.atlas x with hjdef
  have hj : x ∈ (M.atlas.chart j).source := Classical.choose_spec (M.atlas.cover x)
  set u := M.atlas.chart j x with hudef
  have hsu : (M.atlas.chart j).symm u = x := (M.atlas.chart j).left_inv hj
  have huU : u ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelU M x :=
    ⟨(M.atlas.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact mem_modelU M x⟩
  obtain ⟨hQa, hQd⟩ := modelQ_good_of_notMem M Ψ E x hx j hj
  set Q := modelQ M Ψ ∘ (M.atlas.chart j).symm with hQdef
  set Df := fderiv ℂ Q u with hDf
  have hdet : Df.det ≠ 0 := hQd
  set Ce := Df.toContinuousLinearEquivOfDetNeZero hdet with hCe
  have hCe' : (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) = Df :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero Df hdet
  have hstrict : HasStrictFDerivAt Q (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) u := by
    rw [hCe']; exact hQa.hasStrictFDerivAt
  set F := hstrict.toOpenPartialHomeomorph Q with hF
  have hFc : (F : (Fin e → ℂ) → (Fin e → ℂ)) = Q := hstrict.toOpenPartialHomeomorph_coe
  have hus : u ∈ F.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hyt : Q u ∈ F.target := hstrict.image_mem_toOpenPartialHomeomorph_target
  have hσu : F.symm (Q u) = u := by
    have := F.left_inv hus
    rwa [hFc] at this
  have hy0 : Q u = modelQ M Ψ x := by simp only [hQdef, Function.comp_apply, hsu]
  have hσa : AnalyticAt ℂ F.symm (Q u) := by
    refine F.analyticAt_symm (i := Ce) hyt ?_ ?_
    · rw [hσu, hFc]; exact hQa
    · rw [hσu, hFc, hCe']
  have hσd : HasFDerivAt F.symm (Ce.symm : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) (Q u) := by
    refine F.hasFDerivAt_symm hyt ?_
    rw [hσu, hFc, hCe']
    exact hQa.differentiableAt.hasFDerivAt
  set γ₀ : (Fin e → ℂ) → (Σ k, ι k) → ℂ :=
    fun y' => modelLift M x ((M.atlas.chart j).symm (F.symm y')) with hγ₀
  have hγ₀a : AnalyticAt ℂ γ₀ (Q u) := (analyticAt_lift_chart M x j huU).comp_of_eq hσa hσu
  have hγ₀u : γ₀ (Q u) = modelLift M x x := by simp only [hγ₀, hσu, hsu]
  set ψ0 : (Fin e → ℂ) → ℂ := fun y' => Ψ (segre (γ₀ y')) 0 with hψ0
  have hψ0a : AnalyticAt ℂ ψ0 (Q u) :=
    analyticAt_pi_iff.mp ((analyticAt_segre_lift M Ψ x j huU).comp_of_eq hσa hσu) 0
  have hψ0u : ψ0 (Q u) ≠ 0 := by
    simp only [hψ0, hγ₀u]; exact psi_zero_ne_of_not_mem_bad M Ψ hx
  set c : (Fin e → ℂ) → K → ℂ := fun y' => Function.update (fun _ => (1 : ℂ)) k0 (ψ0 y')⁻¹
    with hcdef
  have hc_ne : ∀ y', ψ0 y' ≠ 0 → ∀ k, c y' k ≠ 0 := by
    intro y' h k
    by_cases hk : k = k0
    · subst hk; simp [hcdef, h]
    · simp [hcdef, Function.update_of_ne hk]
  have hca : ∀ k, AnalyticAt ℂ (fun y' => c y' k) (Q u) := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp only [hcdef, Function.update_self]; exact hψ0a.inv hψ0u
    · simp only [hcdef, Function.update_of_ne hk]; exact analyticAt_const
  set γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun y' => bsmul (c y') (γ₀ y') with hγdef
  have hγa : AnalyticAt ℂ γ (Q u) :=
    analyticAt_pi_iff.mpr fun p => (hca p.1).mul (analyticAt_pi_iff.mp hγ₀a p)
  have hprod : ∀ y', ∏ k, c y' k = (ψ0 y')⁻¹ := fun y' => by
    simp [hcdef, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  have hseg : ∀ y', segre (γ y') = (ψ0 y')⁻¹ • segre (γ₀ y') := fun y' => by
    rw [← hprod y']; exact segre_smul (c y') (γ₀ y')
  refine ⟨γ, ⟨?_, ?_⟩, ?_⟩
  · rw [← hy0, hseg]
    simp only [hψ0, hγ₀u]
    rfl
  · rw [← hy0]
    have hU : ∀ᶠ y' in 𝓝 (Q u),
        F.symm y' ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelU M x :=
      hσa.continuousAt.preimage_mem_nhds (by
        rw [hσu]; exact ((M.atlas.chart j).isOpen_inter_preimage_symm (modelU_isOpen M x)).mem_nhds huU)
    filter_upwards [hγa.eventually_analyticAt, hU, F.open_target.mem_nhds hyt,
      hψ0a.continuousAt.eventually_ne hψ0u] with y' ha hUy ht h0
    refine ⟨ha.differentiableAt,
      mcPts_smul hPh (c y') (hc_ne y' h0) ((modelLift_spec M x).1 _ hUy.2).1, ?_⟩
    have hq : Q (F.symm y') = y' := by
      have := F.right_inv ht
      rwa [hFc] at this
    rw [hQdef, Function.comp_apply, modelQ_eq_local M Ψ hUy.2] at hq
    rw [hseg, map_smul]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_zero]
      exact inv_mul_cancel₀ h0
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
      rw [← congrFun hq i, div_eq_inv_mul]
  · rw [← hy0]
    have hblk : ∀ k, ∃ i, γ₀ (Q u) ⟨k, i⟩ ≠ 0 := by
      rw [hγ₀u]; exact (lift_mem M x).1
    have hH : cxHessian (fun y' => r * Real.log (L.h (γ y'))) (Q u) =
        cxHessian (fun y' => r * Real.log (L.h (γ₀ y'))) (Q u) := by
      set G : (Fin e → ℂ) → ℂ :=
        fun y' => ((-(r * (L.a k0 : ℝ)) : ℝ) : ℂ) * Complex.log (ψ0 y' / ψ0 (Q u)) with hG
      set C : ℝ := -(r * (L.a k0 : ℝ) * Real.log ‖ψ0 (Q u)‖) with hC
      have hGa : AnalyticAt ℂ G (Q u) := by
        refine analyticAt_const.mul ((hψ0a.div analyticAt_const hψ0u).clog ?_)
        show ψ0 (Q u) / ψ0 (Q u) ∈ Complex.slitPlane
        rw [div_self hψ0u]
        exact Complex.one_mem_slitPlane
      have heq : (fun y' => r * Real.log (L.h (γ y'))) =ᶠ[𝓝 (Q u)]
          fun y' => r * Real.log (L.h (γ₀ y')) + (G y').re + C := by
        filter_upwards [hψ0a.continuousAt.eventually_ne hψ0u,
          hγ₀a.continuousAt.eventually (isOpen_blockNonzero.mem_nhds hblk)] with y' h0 hb
        have hpos : 0 < L.h (γ₀ y') := L.pos _ hb
        have hn0 : ‖(ψ0 y')⁻¹‖ ^ L.a k0 ≠ 0 :=
          zpow_ne_zero _ (norm_ne_zero_iff.mpr (inv_ne_zero h0))
        simp only [hγdef]
        rw [show bsmul (c y') (γ₀ y') = fun p => c y' p.1 * γ₀ y' p from rfl, L.smul _ _ (hc_ne y' h0),
          prod_norm_update_zpow, Real.log_mul hn0 hpos.ne',
          hG, hC, Complex.re_ofReal_mul, Complex.log_re, norm_div,
          Real.log_div (norm_ne_zero_iff.mpr h0) (norm_ne_zero_iff.mpr hψ0u), Real.log_zpow,
          norm_inv, Real.log_inv]
        ring
      rw [cxHessian_congr heq, cxHessian_add_re (φ := fun y' => r * Real.log (L.h (γ₀ y'))) C
        (contDiffAt_const.mul (pot_contDiffAt hL hγ₀a hblk)) hGa]
    have hmd : maDensity (fun (_ : Fin e) y' => r * Real.log (L.h (γ y'))) (Q u) =
        maDensity (fun (_ : Fin e) y' => r * Real.log (L.h (γ₀ y'))) (Q u) := by
      simp only [maDensity, hH]
    rw [hmd, maDensity_eq_maDens]
    have hcd : ∀ i : Fin e, ContDiffAt ℝ 2
        (fun v => r * Real.log (L.h (modelLift M x ((M.atlas.chart j).symm v)))) (F.symm (Q u)) := by
      intro i
      rw [hσu]
      exact contDiffAt_const.mul (pot_contDiffAt hL (analyticAt_lift_chart M x j huU)
        (by rw [hsu]; exact (lift_mem M x).1))
    have hcomp : ReciprocityTheory.AnForm.maDens (fun (_ : Fin e) y' => r * Real.log (L.h (γ₀ y'))) (Q u) =
        ReciprocityTheory.AnForm.maDens
          (fun (_ : Fin e) v => r * Real.log (L.h (modelLift M x ((M.atlas.chart j).symm v))))
          (F.symm (Q u)) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC F.symm (Q u)).det :=
      ReciprocityTheory.AnForm.A.maDens_comp
        (fun (_ : Fin e) v => r * Real.log (L.h (modelLift M x ((M.atlas.chart j).symm v))))
        F.symm (Q u) hσa hcd
    have hdetinv : LinearMap.det ((Ce.symm : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = (LinearMap.det (Df : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)))⁻¹ := by
      have := ContinuousLinearEquiv.det_coe_symm Ce
      rw [hCe'] at this
      exact this
    have hloc : ReciprocityTheory.AnForm.maDens
        (fun (_ : Fin e) v => r * Real.log (L.h (modelLift M x ((M.atlas.chart j).symm v)))) u =
        locDens M.atlas (fun _ => modelPot M L r) j u := by
      unfold locDens
      rw [hsu]
      rfl
    rw [hcomp, hσu, ReciprocityTheory.AnForm.A.det_jacC, hσd.fderiv, hdetinv, hloc, Complex.normSq_inv,
      Complex.normSq_eq_norm_sq]
    unfold pushDens
    rw [div_eq_mul_inv]

end ModelFibreSumAlmostEverywhere

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StAPrimeChartLeviLocal
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)
open scoped ContDiff

def APrimeChartLeviLocal.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (k : Fin X.S.R.N),
    ∀ y₀ ∈ (X.S.R.chart k).target, ∃ W : Set (Fin D.n → ℂ), IsOpen W ∧ y₀ ∈ W ∧
      ∃ f : (Fin D.n → ℂ) → ℝ, ContDiffOn ℝ ∞ f W ∧
        ∀ z ∈ mcPts (mCoordIdeal D.y), X.M.proj z ∈ (X.S.R.chart k).source →
          X.S.R.chart k (X.M.proj z) ∈ W → ∀ w v, IsChartVel X.M (X.S.R.chart k) z w v →
            levi (fun y => Real.log (D.A'.h y)) z w = levi f (X.S.R.chart k (X.M.proj z)) v

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PAPrimeChartMargin
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)

theorem levi_real_smul {κ : Type*} [Fintype κ] (φ : (κ → ℂ) → ℝ) (z w : κ → ℂ) (r : ℝ) :
    levi φ z (r • w) = r ^ 2 * levi φ z w := by
  unfold levi
  have h : Complex.I • (r • w) = r • (Complex.I • w) := smul_comm _ _ _
  rw [h]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem IsChartVel.real_smul {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)}
    {d : ℕ} {M : CxModel P d} {e : OpenPartialHomeomorph M.Xc (Fin d → ℂ)} {z w : (Σ k, ι k) → ℂ}
    {v : Fin d → ℂ} (h : IsChartVel M e z w v) (r : ℝ) : IsChartVel M e z (r • w) (r • v) := by
  obtain ⟨γ, h0, hd, hev, hv⟩ := h
  have hm : HasDerivAt (fun s : ℂ => (r : ℂ) * s) (r : ℂ) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul (r : ℂ)
  have ht : Tendsto (fun s : ℂ => (r : ℂ) * s) (𝓝 0) (𝓝 0) := by
    simpa using hm.continuousAt.tendsto
  have hsw : ∀ {κ : Type} (u : κ → ℂ), (r : ℂ) • u = r • u := fun u => by
    funext p
    simp [Complex.real_smul]
  refine ⟨fun s => γ ((r : ℂ) * s), by simpa using h0, ?_, ?_, ?_⟩
  · have hd' : HasDerivAt γ w ((r : ℂ) * 0) := by simpa using hd
    have h' := hd'.scomp (0 : ℂ) hm
    rw [hsw] at h'
    exact h'
  · filter_upwards [ht.eventually hev] with s hs
    exact ⟨hs.1.comp s (differentiableAt_id.const_mul _), hs.2⟩
  · have hv' : HasDerivAt (fun s => e (M.proj (γ s))) v ((r : ℂ) * 0) := by simpa using hv
    have h' := hv'.scomp (0 : ℂ) hm
    rw [hsw] at h'
    exact h'

theorem APrimeChartMargin.proof (hQ : APrimeChartLevi.Statement) (hL : ChartVelLift.Statement) :
    APrimeChartMargin.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X
  have hk : ∀ k : Fin X.S.R.N, ∃ c : ℝ, 0 < c ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ w, X.M.proj z ∈ X.S.R.mid k →
      ∀ v : Fin D.n → ℂ, IsChartVel X.M (X.S.R.chart k) z w v →
        c * ‖v‖ ^ 2 ≤ levi (fun y => Real.log (D.A'.h y)) z w := by
    intro k
    obtain ⟨Q, hcont, hrep⟩ := hQ II Ψ K ι Ω E D O Lt X k
    set e := X.S.R.chart k with he
    have hpos : ∀ y ∈ e.target, ∀ v, v ≠ 0 → 0 < Q y v := by
      intro y hy v hv
      obtain ⟨z, hz, hpz, w, hw, hcone, hnt⟩ := hL II Ψ K ι Ω E D O Lt X k y hy v hv
      have hs : X.M.proj z ∈ e.source := by rw [hpz]; exact e.map_target hy
      have hr := hrep z hz hs w v hw
      rw [hpz, e.right_inv hy] at hr
      rw [← hr]
      exact D.A'_pos.2 z hz w hcone hnt
    set S := (e '' closure (X.S.R.mid k)) ×ˢ Metric.sphere (0 : Fin D.n → ℂ) 1 with hS
    have hcpt : IsCompact S :=
      (isClosed_closure.isCompact.image_of_continuousOn
        (e.continuousOn.mono (X.S.R.closure_mid k))).prod (isCompact_sphere 0 1)
    have hsub : S ⊆ e.target ×ˢ Set.univ := by
      rintro ⟨y, u⟩ ⟨⟨x, hx, rfl⟩, -⟩
      exact ⟨e.map_source (X.S.R.closure_mid k hx), Set.mem_univ _⟩
    obtain ⟨c, hc, hcle⟩ : ∃ c : ℝ, 0 < c ∧ ∀ p ∈ S, c ≤ Q p.1 p.2 := by
      rcases S.eq_empty_or_nonempty with hE | hne
      · exact ⟨1, one_pos, by simp [hE]⟩
      · obtain ⟨p, hp, hmin⟩ := hcpt.exists_isMinOn hne (hcont.mono hsub)
        refine ⟨Q p.1 p.2, hpos p.1 (hsub hp).1 p.2 ?_, fun q hq => hmin hq⟩
        intro h0
        have h2 := hp.2
        rw [h0, Metric.mem_sphere, dist_self] at h2
        exact zero_ne_one h2
    refine ⟨c, hc, fun z hz w hm v hv => ?_⟩
    have hs : X.M.proj z ∈ e.source := X.S.R.mid_subset_source k hm
    have hy : e (X.M.proj z) ∈ e '' closure (X.S.R.mid k) := ⟨_, subset_closure hm, rfl⟩
    have h1 := hrep z hz hs w v hv
    rcases eq_or_ne v 0 with rfl | hv0
    · have h2 := hrep z hz hs _ _ (hv.real_smul 0)
      rw [levi_real_smul, smul_zero] at h2
      rw [h1, ← h2]
      simp
    · have hn : 0 < ‖v‖ := norm_pos_iff.2 hv0
      have h2 := hrep z hz hs _ _ (hv.real_smul ‖v‖⁻¹)
      rw [levi_real_smul] at h2
      have hu : (e (X.M.proj z), ‖v‖⁻¹ • v) ∈ S := by
        refine ⟨hy, ?_⟩
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
          inv_mul_cancel₀ hn.ne']
      have h3 := hcle _ hu
      rw [← h2] at h3
      calc c * ‖v‖ ^ 2 ≤ (‖v‖⁻¹ ^ 2 * levi (fun y => Real.log (D.A'.h y)) z w) * ‖v‖ ^ 2 :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = levi (fun y => Real.log (D.A'.h y)) z w := by
          field_simp
  choose ck hck hmk using hk
  have hne : (insert 1 (Finset.univ.image ck)).Nonempty := Finset.insert_nonempty _ _
  refine ⟨(insert 1 (Finset.univ.image ck)).min' hne, ?_, ?_⟩
  · rcases Finset.mem_insert.1 (Finset.min'_mem _ hne) with h | h
    · rw [h]
      exact one_pos
    · obtain ⟨k, -, hk⟩ := Finset.mem_image.1 h
      rw [← hk]
      exact hck k
  · intro z hz w k hm v hv
    exact le_trans (mul_le_mul_of_nonneg_right (Finset.min'_le _ _ (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem _ (Finset.mem_univ k)))) (by positivity)) (hmk k z hz w hm v hv)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
