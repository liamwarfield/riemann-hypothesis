module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormBound
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRatNoetherFrame
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPacking
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResVolume

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgeSheet
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge

open ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}
  (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

theorem exists_sheet_brW (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι)
    (hP : IsArithVar P (e + 1)) (hL : ∀ j, IsSmoothHerm (L j)) (hs : IsSectionOn P A s)
    (x : R.X) (hx : x ∉ brBad R Ψ) :
    ∃ γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ, IsSheet P Ψ (brQ R Ψ x) (brW R Ψ x) γ ∧
      logNorm A s (γ (brQ R Ψ x)) * maDensity (fun j y' => pot L j (γ y')) (brQ R Ψ x) =
        logNorm A s (R.lift x x) * pushDens R.A (fun j => potOf R (L j)) (brQ R Ψ) x := by
  classical
  obtain ⟨k0⟩ := hP.1
  have hPh : IsMultiHomogIdeal P := hP.2.1.2.1
  set j := chartIdx R.A x with hjdef
  have hj : x ∈ (R.A.chart j).source := Classical.choose_spec (R.A.cover x)
  set u := R.A.chart j x with hudef
  have hsu : (R.A.chart j).symm u = x := (R.A.chart j).left_inv hj
  have huU : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact R.mem_U x⟩
  obtain ⟨hQa, hQd⟩ := brGood R Ψ x hx j hj
  set Q := brQ R Ψ ∘ (R.A.chart j).symm with hQdef
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
  have hy0 : Q u = brQ R Ψ x := by simp only [hQdef, Function.comp_apply, hsu]
  have hσa : AnalyticAt ℂ F.symm (Q u) := by
    refine F.analyticAt_symm (i := Ce) hyt ?_ ?_
    · rw [hσu, hFc]; exact hQa
    · rw [hσu, hFc, hCe']
  have hσd : HasFDerivAt F.symm (Ce.symm : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) (Q u) := by
    refine F.hasFDerivAt_symm hyt ?_
    rw [hσu, hFc, hCe']
    exact hQa.differentiableAt.hasFDerivAt
  set γ₀ : (Fin e → ℂ) → (Σ k, ι k) → ℂ :=
    fun y' => R.lift x ((R.A.chart j).symm (F.symm y')) with hγ₀
  have hγ₀a : AnalyticAt ℂ γ₀ (Q u) := (analyticAt_lift_chart R x j huU).comp_of_eq hσa hσu
  have hγ₀u : γ₀ (Q u) = R.lift x x := by simp only [hγ₀, hσu, hsu]
  set ψ0 : (Fin e → ℂ) → ℂ := fun y' => Ψ (segre (γ₀ y')) 0 with hψ0
  have hψ0a : AnalyticAt ℂ ψ0 (Q u) :=
    analyticAt_pi_iff.mp ((analyticAt_segre_lift R Ψ x j huU).comp_of_eq hσa hσu) 0
  have hψ0u : ψ0 (Q u) ≠ 0 := by
    simp only [hψ0, hγ₀u]; exact projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx
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
        F.symm y' ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
      hσa.continuousAt.preimage_mem_nhds (by
        rw [hσu]; exact ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds huU)
    filter_upwards [hγa.eventually_analyticAt, hU, F.open_target.mem_nhds hyt,
      hψ0a.continuousAt.eventually_ne hψ0u] with y' ha hUy ht h0
    refine ⟨ha.differentiableAt, mcPts_smul hPh (c y') (hc_ne y' h0) (R.mem x _ hUy.2), ?_⟩
    have hq : Q (F.symm y') = y' := by
      have := F.right_inv ht
      rwa [hFc] at this
    rw [hQdef, Function.comp_apply, brQ_eq_local R Ψ hUy.2] at hq
    rw [hseg, map_smul]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_zero]
      exact inv_mul_cancel₀ h0
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
      rw [← congrFun hq i, div_eq_inv_mul]
  · rw [← hy0]
    obtain ⟨a, ha, hsa, -⟩ := hs
    have hlog : logNorm A s (γ (Q u)) = logNorm A s (R.lift x x) := by
      show logNorm A s (bsmul (c (Q u)) (γ₀ (Q u))) = _
      rw [logNorm_bsmul A ha hsa (hc_ne _ hψ0u), hγ₀u]
    rw [hlog]
    congr 1
    have hblk : ∀ k, ∃ i, γ₀ (Q u) ⟨k, i⟩ ≠ 0 := by
      rw [hγ₀u]; exact (R.mem x x (R.mem_U x)).1
    have hH : ∀ i, cxHessian (fun y' => pot L i (γ y')) (Q u) =
        cxHessian (fun y' => pot L i (γ₀ y')) (Q u) := by
      intro i
      set G : (Fin e → ℂ) → ℂ :=
        fun y' => ((-((L i).a k0 : ℝ) : ℝ) : ℂ) * Complex.log (ψ0 y' / ψ0 (Q u)) with hG
      set C : ℝ := -(((L i).a k0 : ℝ) * Real.log ‖ψ0 (Q u)‖) with hC
      have hGa : AnalyticAt ℂ G (Q u) := by
        refine analyticAt_const.mul ((hψ0a.div analyticAt_const hψ0u).clog ?_)
        show ψ0 (Q u) / ψ0 (Q u) ∈ Complex.slitPlane
        rw [div_self hψ0u]
        exact Complex.one_mem_slitPlane
      have heq : (fun y' => pot L i (γ y')) =ᶠ[𝓝 (Q u)]
          fun y' => pot L i (γ₀ y') + (G y').re + C := by
        filter_upwards [hψ0a.continuousAt.eventually_ne hψ0u,
          hγ₀a.continuousAt.eventually (isOpen_blockNonzero.mem_nhds hblk)] with y' h0 hb
        have hpos : 0 < (L i).h (γ₀ y') := (L i).pos _ hb
        have hn0 : ‖(ψ0 y')⁻¹‖ ^ (L i).a k0 ≠ 0 :=
          zpow_ne_zero _ (norm_ne_zero_iff.mpr (inv_ne_zero h0))
        simp only [pot, hγdef]
        rw [show bsmul (c y') (γ₀ y') = fun p => c y' p.1 * γ₀ y' p from rfl, (L i).smul _ _ (hc_ne y' h0), prod_norm_update_zpow, Real.log_mul hn0 hpos.ne',
          hG, hC, Complex.re_ofReal_mul, Complex.log_re, norm_div,
          Real.log_div (norm_ne_zero_iff.mpr h0) (norm_ne_zero_iff.mpr hψ0u), Real.log_zpow,
          norm_inv, Real.log_inv]
        ring
      rw [cxHessian_congr heq, cxHessian_add_re (φ := fun y' => pot L i (γ₀ y')) C
        (pot_contDiffAt (hL i) hγ₀a hblk) hGa]
    have hmd : maDensity (fun i y' => pot L i (γ y')) (Q u) =
        maDensity (fun i y' => pot L i (γ₀ y')) (Q u) := by
      simp only [maDensity, hH]
    rw [hmd, maDensity_eq_maDens]
    have hcd : ∀ i, ContDiffAt ℝ 2 (fun v => pot L i (R.lift x ((R.A.chart j).symm v)))
        (F.symm (Q u)) := by
      intro i
      rw [hσu]
      exact pot_contDiffAt (hL i) (analyticAt_lift_chart R x j huU)
        (by rw [hsu]; exact (R.mem x x (R.mem_U x)).1)
    have hcomp : ReciprocityTheory.AnForm.maDens (fun i y' => pot L i (γ₀ y')) (Q u) =
        ReciprocityTheory.AnForm.maDens (fun i v => pot L i (R.lift x ((R.A.chart j).symm v)))
          (F.symm (Q u)) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC F.symm (Q u)).det :=
      ReciprocityTheory.AnForm.A.maDens_comp (fun i v => pot L i (R.lift x ((R.A.chart j).symm v)))
        F.symm (Q u) hσa hcd
    have hdetinv : LinearMap.det ((Ce.symm : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = (LinearMap.det (Df : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)))⁻¹ := by
      have := ContinuousLinearEquiv.det_coe_symm Ce
      rw [hCe'] at this
      exact this
    have hloc : ReciprocityTheory.AnForm.maDens (fun i v => pot L i (R.lift x ((R.A.chart j).symm v))) u =
        locDens R.A (fun i => potOf R (L i)) j u := by
      unfold locDens
      rw [hsu]
      rfl
    rw [hcomp, hσu, ReciprocityTheory.AnForm.A.det_jacC, hσd.fderiv, hdetinv, hloc, Complex.normSq_inv,
      Complex.normSq_eq_norm_sq]
    unfold pushDens
    rw [div_eq_mul_inv]

end GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmallSectionCountLeOfIntegralMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter NumberField Topology

noncomputable section

set_option linter.unusedSectionVars false

section Lemmas

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem isClosed_liesOver {F : Type} [Field F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (sg : F →+* ℂ) :
    IsClosed {z | LiesOver y sg z} := by
  have : {z | LiesOver y sg z} = ⋂ (d : K → ℕ) (g : MRing ι) (h : MRing ι) (θ : F)
      (_ : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d) (_ : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h d) (_ : aeval y g = algebraMap F Ω θ * aeval y h),
      {z : (Σ k, ι k) → ℂ | eval z (map (Int.castRingHom ℂ) g) = sg θ * eval z (map (Int.castRingHom ℂ) h)} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rfl
  rw [this]
  refine isClosed_iInter fun d => isClosed_iInter fun g => isClosed_iInter fun h => isClosed_iInter fun θ =>
    isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
  exact isClosed_eq (MvPolynomial.continuous_eval _) (continuous_const.mul (MvPolynomial.continuous_eval _))

theorem isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z; simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem not_mem_mCoordIdeal {y : (Σ k, ι k) → Ω} {f : MRing ι} {d : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f d)
    (h0 : aeval y f ≠ 0) : f ∉ mCoordIdeal y := by
  intro hmem
  rw [mCoordIdeal, RingHom.mem_ker, ProjLine.mConeMap_eq_of_isMultiHomog y hf] at hmem
  rcases mul_eq_zero.1 hmem with h | h
  · exact h0 (MvPolynomial.C_eq_zero.1 h)
  · exact (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (MvPolynomial.X_ne_zero k)) h

theorem isMultiHomog_mul {f g : MRing ι} {df dg : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f df)
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g dg) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f * g) (df + dg) := by
  classical
  intro m hm k
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf a ha k, hg b hb k]

theorem norm_le_of_isSmallH {F : Type} [Field F] [Fintype (F →+* ℂ)] [Algebra F Ω]
    (hND : NonvanishingDense.Statement) {y : (Σ k, ι k) → Ω} {d : ℕ} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {τ : ℕ} {s : Ω}
    (θ : F) (har : IsArithVar (mCoordIdeal y) d) (hb : Birational y) (hA : IsSmoothHerm A)
    (hex : ∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z)
    (hs : IsSmallH (mCoordIdeal y) y A τ s)
    {dg dh : K → ℕ} {g h : MRing ι} (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g dg) (hh : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h dh)
    (hdeg : ∀ k, (dg k : ℤ) = dh k + τ * A.a k) (hgh : aeval y g = algebraMap F Ω θ * s * aeval y h)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) {sg : F →+* ℂ} (hzs : LiesOver y sg z) :
    ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤
      ‖sg θ‖ * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := by
  obtain ⟨e, g1, h1, hg1, hh1, hne, hrep⟩ := hb (algebraMap F Ω θ)
  set ev : MRing ι → ((Σ k, ι k) → ℂ) → ℂ := fun f z => eval z (map (Int.castRingHom ℂ) f) with hev

  have hpt : ∀ z' ∈ mcPts (mCoordIdeal y), LiesOver y sg z' → ev h1 z' ≠ 0 →
      ‖ev g z'‖ ≤ ‖sg θ‖ * ‖ev h z'‖ * A.h z' ^ τ := by
    intro z' hz' hl hh0
    have hsm := hs (dg + e) (e + dh) (g * h1) (g1 * h) z' (isMultiHomog_mul hg hh1)
      (isMultiHomog_mul hg1 hh) (fun k => by simp only [Pi.add_apply, Nat.cast_add, hdeg k]; ring)
      (by rw [map_mul, map_mul, hgh, hrep]; ring) hz'
    have hrel := hl e g1 h1 θ hg1 hh1 hrep
    simp only [map_mul, norm_mul] at hsm
    change ‖ev g z'‖ * ‖ev h1 z'‖ ≤ ‖ev g1 z'‖ * ‖ev h z'‖ * A.h z' ^ τ at hsm
    rw [show ev g1 z' = sg θ * ev h1 z' from hrel, norm_mul] at hsm
    have hp : 0 < ‖ev h1 z'‖ := norm_pos_iff.2 hh0
    nlinarith [hsm, hp]

  set R : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  set U : Set ((Σ k, ι k) → ℂ) := R ∩ ⋂ sg' : {sg' : F →+* ℂ // sg' ≠ sg}, {z | LiesOver y sg'.1 z}ᶜ
  have hUo : IsOpen U := isOpen_blockNonzero.inter
    (isOpen_iInter_of_finite fun sg' => (isClosed_liesOver y sg'.1).isOpen_compl)
  have hzU : z ∈ U := ⟨hz.1, Set.mem_iInter.2 fun sg' hl => sg'.2 ((hex z hz).unique hl hzs)⟩
  set φ : ((Σ k, ι k) → ℂ) → ℝ := fun z => ‖ev g z‖ - ‖sg θ‖ * ‖ev h z‖ * A.h z ^ τ
  have hφ : ContinuousAt φ z := by
    have hAc : ContinuousAt A.h z :=
      (hA.continuousOn).continuousAt (isOpen_blockNonzero.mem_nhds hz.1)
    exact ((MvPolynomial.continuous_eval _).norm.continuousAt).sub
      ((continuousAt_const.mul (MvPolynomial.continuous_eval _).norm.continuousAt).mul (hAc.pow τ))
  by_contra hcon
  have hpos : 0 < φ z := by simp only [φ]; linarith [not_le.1 hcon]
  have hnb : {z' | 0 < φ z'} ∩ U ∈ 𝓝 z :=
    Filter.inter_mem (hφ.eventually (lt_mem_nhds hpos)) (hUo.mem_nhds hzU)
  have hcl := hND K ι (mCoordIdeal y) d h1 har (not_mem_mCoordIdeal hh1 hne) hz
  obtain ⟨z', ⟨hφ', hU'⟩, hz'P, hz'h⟩ := mem_closure_iff_nhds.1 hcl _ hnb
  obtain ⟨sg'', hl'', -⟩ := hex z' hz'P
  have hsg : sg'' = sg := by
    by_contra hne'
    exact (Set.mem_iInter.1 hU'.2 ⟨sg'', hne'⟩) hl''
  subst hsg
  have := hpt z' hz'P hl'' hz'h
  simp only [Set.mem_ofPred_eq, φ] at hφ'
  linarith

theorem isSmallH_mul {F : Type} [Field F] [Fintype (F →+* ℂ)] [Algebra F Ω]
    (hND : NonvanishingDense.Statement) {y : (Σ k, ι k) → Ω} {d : ℕ} {A A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {τ : ℕ}
    (har : IsArithVar (mCoordIdeal y) d) (hb : Birational y) (hA : IsSmoothHerm A)
    (hex : ∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) (ha : A'.a = A.a) (θ : F)
    (hkey : ∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z →
      ‖sg θ‖ * A.h z ^ τ ≤ A'.h z ^ τ)
    {s : Ω} (hs : IsSmallH (mCoordIdeal y) y A τ s) :
    IsSmallH (mCoordIdeal y) y A' τ (algebraMap F Ω θ * s) := by
  intro dg dh g h z hg hh hdeg hgh hz
  obtain ⟨sg, hsg, -⟩ := hex z hz
  have h1 := norm_le_of_isSmallH hND θ har hb hA hex hs hg hh (fun k => by rw [← ha]; exact hdeg k)
    (by rw [hgh]) hz hsg
  calc ‖eval z (map (Int.castRingHom ℂ) g)‖
      ≤ ‖sg θ‖ * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := h1
    _ = ‖eval z (map (Int.castRingHom ℂ) h)‖ * (‖sg θ‖ * A.h z ^ τ) := by ring
    _ ≤ ‖eval z (map (Int.castRingHom ℂ) h)‖ * A'.h z ^ τ :=
        mul_le_mul_of_nonneg_left (hkey z hz sg hsg) (norm_nonneg _)

theorem mul_mem_chartLatNm {F : Type} [Field F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ)
    {θ : F} (hθ : IsIntegral ℤ θ) {s : Ω} (hs : s ∈ chartLatNm y a τ) :
    algebraMap F Ω θ * s ∈ chartLatNm y a τ := by
  intro c hc
  have h := hs c hc
  rw [mul_assoc]
  have hθ' : IsIntegral (chartRingZ y c) (algebraMap F Ω θ) := (hθ.algebraMap).tower_top
  exact (integralClosure (chartRingZ y c) Ω).mul_mem hθ' h

theorem smallSectionCount_le_of_integral_mul {F : Type} [Field F] [Algebra F Ω] {y : (Σ k, ι k) → Ω} {A A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (ha : A'.a = A.a) {τ : ℕ}
    (hfin : {s : chartLatNm y A'.a τ | IsSmallH (mCoordIdeal y) y A' τ (s : Ω)}.Finite)
    {θ : F} (hθ : IsIntegral ℤ θ) (hθ0 : θ ≠ 0)
    (hmul : ∀ s : Ω, IsSmallH (mCoordIdeal y) y A τ s →
      IsSmallH (mCoordIdeal y) y A' τ (algebraMap F Ω θ * s)) :
    smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ ≤
      smallSectionCount (IsSmallH (mCoordIdeal y) y A') (chartLatNm y A'.a) τ := by
  unfold smallSectionCount
  have : Finite {s : chartLatNm y A'.a τ // IsSmallH (mCoordIdeal y) y A' τ (s : Ω)} := hfin.to_subtype
  have hθ0' : algebraMap F Ω θ ≠ 0 := (map_ne_zero _).2 hθ0
  have hc : Nat.card {s : chartLatNm y A.a τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)} ≤
      Nat.card {s : chartLatNm y A'.a τ // IsSmallH (mCoordIdeal y) y A' τ (s : Ω)} := by
    refine Nat.card_le_card_of_injective
      (fun s => (⟨⟨algebraMap F Ω θ * (s.1 : Ω), by rw [ha]; exact mul_mem_chartLatNm y A.a τ hθ s.1.2⟩,
        hmul _ s.2⟩ : {s : chartLatNm y A'.a τ // IsSmallH (mCoordIdeal y) y A' τ (s : Ω)})) ?_
    intro s t hst
    have h := congrArg (fun u : {s : chartLatNm y A'.a τ // IsSmallH (mCoordIdeal y) y A' τ (s : Ω)} =>
      ((u.1 : chartLatNm y A'.a τ) : Ω)) hst
    exact Subtype.ext (Subtype.ext (mul_left_cancel₀ hθ0' h))
  rcases Nat.eq_zero_or_pos (Nat.card {s : chartLatNm y A.a τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)})
    with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hc)

end Lemmas

theorem ArithmeticVolumeNefDual.proof (hG7p : ArithmeticVolumeNef.Statement) (hPk : PackingStatement) (hU : UnitApprox.Statement)
    (hND : NonvanishingDense.Statement) (hTw : TwistMetric.Statement) : ArithmeticVolumeNefDual.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y D a A P0 Λ II hD hII har hb ha hP0 hsp hconj hΛpos hΛconj hΛsum hex hmon

  have hn : (0 : ℝ) < Fintype.card (F →+* ℂ) := by
    rw [NumberField.Embeddings.card]; exact_mod_cast Module.finrank_pos
  set m : ℝ := (∑ sg, Real.log (Λ sg)) / Fintype.card (F →+* ℂ) with hm_def
  have hm : m ≤ 0 := div_nonpos_of_nonpos_of_nonneg hΛsum hn.le
  set u : (F →+* ℂ) → ℝ := fun sg => Real.log (Λ sg) - m with hu_def
  have hu_conj : ∀ sg, u (ComplexEmbedding.conjugate sg) = u sg := fun sg => by simp only [u, hΛconj]
  have hu_sum : ∑ sg, u sg = 0 := by
    simp only [u]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hm_def,
      mul_div_cancel₀ _ hn.ne', sub_self]
  obtain ⟨C, hC⟩ := hU F u hu_conj hu_sum
  obtain ⟨c, hc⟩ := hTw K ι Ω F y D A P0 II u hD hII har hb hP0 hsp hconj hex hu_conj hu_sum
  have hden : ∀ τ : ℕ, 0 ≤ ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := fun τ => by positivity

  have hδ : ∀ δ : ℝ, 0 < δ →
      limsup (fun τ : ℕ => smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ /
        ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) atTop ≤
        II K ι (mCoordIdeal y) (D + 1) (fun _ => A) + c * δ := by
    intro δ hδ
    obtain ⟨A', ha', hsp', hconj', hpt, hII'⟩ := hc δ hδ
    have ha'' : A'.a = fun k => (a k : ℤ) := ha'.trans ha

    have hmon' : MonomialsBounded (mCoordIdeal y) A' a := by
      intro z hz μ hμ
      obtain ⟨sg, hsg, -⟩ := hex z hz
      have hAz : 0 < A.h z := A.pos z hz.1
      rw [hpt z hz sg hsg]
      calc ‖∏ p, z p ^ μ p‖ ≤ Λ sg * A.h z := hmon z hz sg hsg μ hμ
        _ = Real.exp (u sg + m) * A.h z := by
            rw [show u sg + m = Real.log (Λ sg) by simp only [u]; ring, Real.exp_log (hΛpos sg)]
        _ ≤ Real.exp (u sg + δ) * A.h z :=
            mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) hAz.le
    have hG := hG7p K ι Ω y D a A' P0 II hD hII har hb ha'' hP0 hsp' hmon' hconj'
    obtain ⟨hfin, C', hC'⟩ := hPk K ι Ω y D A' (chartLatNm y A'.a) har hb hsp'.1 (fun _ => le_rfl)
    refine le_trans ?_ (hG.trans hII')
    refine limsup_le_limsup ?_ ?_ ?_
    ·
      refine eventually_atTop.2 ⟨⌈C / δ⌉₊, fun τ hτ => div_le_div_of_nonneg_right ?_ (hden τ)⟩
      obtain ⟨ε, hε⟩ := hC τ
      have hCτ : C ≤ τ * δ := (div_le_iff₀ hδ).1 (Nat.ceil_le.1 hτ)
      have hε0 : ((ε : 𝓞 F) : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 ε.ne_zero
      refine smallSectionCount_le_of_integral_mul ha' (hfin τ) (RingOfIntegers.isIntegral_coe _) hε0 fun s hs => ?_
      refine isSmallH_mul hND har hb hsp.1 hex ha' _ ?_ hs
      intro z hz sg hsg
      have hAz : 0 < A.h z := A.pos z hz.1
      have hpos : 0 < ‖sg ((ε : 𝓞 F) : F)‖ := norm_pos_iff.2 ((map_ne_zero sg).2 hε0)
      have hlog : Real.log ‖sg ((ε : 𝓞 F) : F)‖ ≤ τ * u sg + τ * δ := by
        linarith [(abs_le.1 (hε sg)).2]
      rw [← mul_add, Real.log_le_iff_le_exp hpos, Real.exp_nat_mul] at hlog
      rw [hpt z hz sg hsg, mul_pow]
      exact mul_le_mul_of_nonneg_right hlog (pow_nonneg hAz.le τ)
    · exact isCoboundedUnder_le_of_le atTop (fun k => div_nonneg (Real.log_natCast_nonneg _) (hden k))
    · refine isBoundedUnder_of_eventually_le (a := |C'| * 2 ^ (D + 1) * ((D + 1).factorial : ℝ))
        (eventually_atTop.2 ⟨1, fun k hk => ?_⟩)
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hkp : (0 : ℝ) < (k : ℝ) ^ (D + 1) := by positivity
      rw [div_le_iff₀ (by positivity)]
      have h2 : C' * ((k : ℝ) + 1) ^ (D + 1) ≤ |C'| * (2 * (k : ℝ)) ^ (D + 1) :=
        calc C' * ((k : ℝ) + 1) ^ (D + 1) ≤ |C'| * ((k : ℝ) + 1) ^ (D + 1) :=
              mul_le_mul_of_nonneg_right (le_abs_self C') (by positivity)
          _ ≤ |C'| * (2 * (k : ℝ)) ^ (D + 1) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) _) (abs_nonneg C')
      calc smallSectionCount (IsSmallH (mCoordIdeal y) y A') (chartLatNm y A'.a) k
          ≤ |C'| * (2 * (k : ℝ)) ^ (D + 1) := (hC' k).trans h2
        _ = |C'| * 2 ^ (D + 1) * ((D + 1).factorial : ℝ) *
              ((k : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
            rw [mul_pow]; field_simp

  refine le_of_forall_pos_lt_add fun η hη => ?_
  have hδ0 : 0 < η / (|c| + 1) := by positivity
  have hcη : c * (η / (|c| + 1)) < η := by
    calc c * (η / (|c| + 1)) ≤ |c| * (η / (|c| + 1)) := mul_le_mul_of_nonneg_right (le_abs_self c) hδ0.le
      _ < (|c| + 1) * (η / (|c| + 1)) := mul_lt_mul_of_pos_right (by linarith) hδ0
      _ = η := by field_simp
  linarith [hδ _ hδ0]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.UnipotentCharacter
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics Module

noncomputable section

section Bounded

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {P : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {τ : ℕ} {s : Ω}

theorem IsBoundedH.mono {c c' : ℝ} (hs : IsBoundedH P y A τ c s) (hc : c ≤ c') :
    IsBoundedH P y A τ c' s := by
  intro dg dh g h z hg hh hd he hz
  refine (hs dg dh g h z hg hh hd he hz).trans ?_
  have h0 : 0 ≤ A.h z ^ τ := pow_nonneg (A.pos z hz.1).le τ
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (norm_nonneg (eval z (map (Int.castRingHom ℂ) h)))) h0

theorem IsSmallH.isBoundedH_one (hs : IsSmallH P y A τ s) : IsBoundedH P y A τ 1 s := by
  intro dg dh g h z hg hh hd he hz
  simpa [one_mul] using hs dg dh g h z hg hh hd he hz

end Bounded

section Count

variable {r : ℕ}

theorem exists_shortLatticeBasis (L : Submodule ℤ (EuclideanSpace ℝ (Fin r))) [DiscreteTopology L]
    [IsZLattice ℝ L] (S : Set (EuclideanSpace ℝ (Fin r))) (hSL : S ⊆ L)
    (hLS : (L : Set (EuclideanSpace ℝ (Fin r))) ⊆ Submodule.span ℝ S) {c : ℝ} (hc : ∀ v ∈ S, ‖v‖ ≤ c) :
    Nonempty (ShortLatticeBasis L c) := by
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℝ S
  have htop : Submodule.span ℝ b = ⊤ := by
    rw [hspan, eq_top_iff, ← IsZLattice.span_top (K := ℝ) (L := L)]
    exact Submodule.span_le.2 hLS
  let bb : Basis b ℝ (EuclideanSpace ℝ (Fin r)) :=
    Basis.mk hli (by rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq, htop])
  let e : b ≃ Fin (finrank ℝ (EuclideanSpace ℝ (Fin r))) := bb.indexEquiv (finBasis ℝ _)
  exact ⟨{ vec := fun i => ((e.symm i : b) : EuclideanSpace ℝ (Fin r))
           mem := fun i => hSL (hbS (e.symm i).2)
           linearIndependent := hli.comp e.symm e.symm.injective
           norm_le := fun i => hc _ (hbS (e.symm i).2) }⟩

theorem log_ncard_ball_le (L : Submodule ℤ (EuclideanSpace ℝ (Fin r))) [DiscreteTopology L] [IsZLattice ℝ L]
    {c : ℝ} (hc : 0 ≤ c) (B : ShortLatticeBasis L c) :
    {x | x ∈ L ∧ ‖x‖ ≤ (1 : ℝ)}.Finite ∧
      Real.log ({x | x ∈ L ∧ ‖x‖ ≤ (1 : ℝ)}.ncard : ℝ) ≤
        Real.log 6 + r * Real.log (1 + r * c) - Real.log (ZLattice.covolume L) := by
  obtain ⟨hfin, hcount⟩ := LatticeCount.proof (EuclideanSpace ℝ (Fin r)) L c 1 B zero_le_one
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin r)) = r := finrank_euclideanSpace_fin
  rw [hdim] at hcount
  have hV := SmallBallVolume.proof r
  have hN1 : (1 : ℝ) ≤ ({x | x ∈ L ∧ ‖x‖ ≤ (1 : ℝ)}.ncard : ℝ) := by
    have : 0 < {x | x ∈ L ∧ ‖x‖ ≤ (1 : ℝ)}.ncard :=
      (Set.ncard_pos hfin).2 ⟨0, L.zero_mem, by simp⟩
    exact_mod_cast this
  have hcov := ZLattice.covolume_pos L
  have hq : 0 < (1 + (r : ℝ) * c) ^ r := by positivity
  refine ⟨hfin, ?_⟩
  have h1 : ({x | x ∈ L ∧ ‖x‖ ≤ (1 : ℝ)}.ncard : ℝ) ≤ 6 * (1 + (r : ℝ) * c) ^ r / ZLattice.covolume L := by
    rw [le_div_iff₀ hcov]
    calc _ ≤ unitBallVolume r * (1 + (r : ℝ) * c) ^ r := hcount
      _ ≤ 6 * (1 + (r : ℝ) * c) ^ r := mul_le_mul_of_nonneg_right hV hq.le
  calc _ ≤ Real.log (6 * (1 + (r : ℝ) * c) ^ r / ZLattice.covolume L) :=
        Real.log_le_log (by linarith) h1
    _ = _ := by
      rw [Real.log_div (by positivity) hcov.ne', Real.log_mul (by norm_num) hq.ne', Real.log_pow]

theorem log_card_le_of_injective {α : Type*} {V : Type*} [NormedAddCommGroup V] [Module ℤ V]
    (L : Submodule ℤ V) (f : α → V) (hf : Function.Injective f) (hmem : ∀ a, f a ∈ L ∧ ‖f a‖ ≤ 1)
    (hfin : {x | x ∈ L ∧ ‖x‖ ≤ (1 : ℝ)}.Finite) :
    Real.log (Nat.card α) ≤ Real.log ({x | x ∈ L ∧ ‖x‖ ≤ (1 : ℝ)}.ncard : ℝ) := by
  have hle : Nat.card α ≤ {x | x ∈ L ∧ ‖x‖ ≤ (1 : ℝ)}.ncard := by
    have := hfin.to_subtype
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_le_card_of_injective (fun a => ⟨f a, hmem a⟩)
      (fun a b h => hf (congrArg Subtype.val h))
  have hpos : 0 < {x | x ∈ L ∧ ‖x‖ ≤ (1 : ℝ)}.ncard :=
    (Set.ncard_pos hfin).2 ⟨0, L.zero_mem, by simp⟩
  rcases Nat.eq_zero_or_pos (Nat.card α) with h0 | h0
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_nonneg (by exact_mod_cast hpos)
  · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hle)

end Count

section Asymptotics

theorem isBigO_natCast_add_one :
    (fun n : ℕ => (n : ℝ) + 1) =O[atTop] fun n : ℕ => (n : ℝ) := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  linarith

theorem isLittleO_natCast_pow_pow {p q : ℕ} (h : p < q) :
    (fun n : ℕ => (n : ℝ) ^ p) =o[atTop] fun n : ℕ => (n : ℝ) ^ q :=
  (isLittleO_pow_pow_atTop_of_lt h).comp_tendsto tendsto_natCast_atTop_atTop

theorem eventually_error_le (D : ℕ) (C c : ℝ) (hc : 0 ≤ c) (r : ℕ → ℕ)
    (hr : ∀ n, (r n : ℝ) ≤ C * ((n : ℝ) + 1) ^ D) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.log 6 + (r n : ℝ) * Real.log (1 + r n * c) ≤
      ε * ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
  set C₀ := max C 0 with hC₀
  have hC₀0 : 0 ≤ C₀ := le_max_right _ _
  set k := C₀ * c with hk
  have hk0 : 0 ≤ k := mul_nonneg hC₀0 hc

  have hbound : ∀ n : ℕ, (r n : ℝ) * Real.log (1 + r n * c) ≤
      C₀ * ((n : ℝ) + 1) ^ D * (Real.log (1 + k) + D * Real.log ((n : ℝ) + 1)) := by
    intro n
    have hm1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ D := one_le_pow₀ (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
    have hrn : (r n : ℝ) ≤ C₀ * ((n : ℝ) + 1) ^ D :=
      (hr n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hlog0 : 0 ≤ Real.log (1 + r n * c) := Real.log_nonneg (by nlinarith [(r n).cast_nonneg (α := ℝ)])
    have hlog : Real.log (1 + r n * c) ≤ Real.log (1 + k) + D * Real.log ((n : ℝ) + 1) := by
      have h1 : 1 + (r n : ℝ) * c ≤ (1 + k) * ((n : ℝ) + 1) ^ D := by
        have : (r n : ℝ) * c ≤ k * ((n : ℝ) + 1) ^ D := by
          rw [hk, mul_assoc, mul_comm c, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right hrn hc
        nlinarith
      calc Real.log (1 + r n * c) ≤ Real.log ((1 + k) * ((n : ℝ) + 1) ^ D) :=
            Real.log_le_log (by nlinarith [(r n).cast_nonneg (α := ℝ)]) h1
        _ = _ := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    calc (r n : ℝ) * Real.log (1 + r n * c) ≤ C₀ * ((n : ℝ) + 1) ^ D * Real.log (1 + r n * c) :=
          mul_le_mul_of_nonneg_right hrn hlog0
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)

  have hpow : (fun n : ℕ => ((n : ℝ) + 1) ^ D) =O[atTop] fun n : ℕ => (n : ℝ) ^ D :=
    isBigO_natCast_add_one.pow D
  have h1 : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) := by
    simpa using isLittleO_natCast_pow_pow (p := 0) (q := D + 1) (Nat.succ_pos D)
  have h2 : (fun n : ℕ => ((n : ℝ) + 1) ^ D) =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) :=
    hpow.trans_isLittleO (isLittleO_natCast_pow_pow (Nat.lt_succ_self D))
  have hlogn : (fun n : ℕ => Real.log ((n : ℝ) + 1)) =o[atTop] fun n : ℕ => (n : ℝ) := by
    have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact (Real.isLittleO_log_id_atTop.comp_tendsto ht).trans_isBigO isBigO_natCast_add_one
  have h3 : (fun n : ℕ => ((n : ℝ) + 1) ^ D * Real.log ((n : ℝ) + 1)) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := by
    have := hpow.mul_isLittleO hlogn
    refine this.congr_right ?_
    intro n
    rw [pow_succ]
  have hB : (fun n : ℕ => Real.log 6 +
      C₀ * ((n : ℝ) + 1) ^ D * (Real.log (1 + k) + D * Real.log ((n : ℝ) + 1))) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := by
    have := (h1.const_mul_left (Real.log 6)).add
      ((h2.const_mul_left (C₀ * Real.log (1 + k))).add (h3.const_mul_left (C₀ * D)))
    refine this.congr_left ?_
    intro n
    ring
  have hF : (0 : ℝ) < ((D + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  filter_upwards [hB.def (div_pos hε hF)] with n hn
  have hpos : 0 ≤ (n : ℝ) ^ (D + 1) := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos] at hn
  calc Real.log 6 + (r n : ℝ) * Real.log (1 + r n * c)
      ≤ Real.log 6 + C₀ * ((n : ℝ) + 1) ^ D * (Real.log (1 + k) + D * Real.log ((n : ℝ) + 1)) := by
        linarith [hbound n]
    _ ≤ |Real.log 6 + C₀ * ((n : ℝ) + 1) ^ D * (Real.log (1 + k) + D * Real.log ((n : ℝ) + 1))| :=
        le_abs_self _
    _ ≤ ε / ((D + 1).factorial : ℝ) * (n : ℝ) ^ (D + 1) := hn
    _ = ε * ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by ring

end Asymptotics

theorem G7.proof (hG1 : SuccessiveMinimaSpan.Statement) (hE : EuclideanSections.Statement) : G7.Statement := by
  intro K _ ι _ Ω _ _ y D A P0 II hD hII har hb hA hc
  obtain ⟨r, φ, hinj, hdisc, hlat, hnorm, ⟨Cr, hr⟩, hdeg⟩ := hE K ι Ω y D A P0 II hD hII har hb hA hc
  obtain ⟨C, hC⟩ := hG1 K ι Ω y D A P0 hD har hb hA
  set c := max C 0 with hcdef
  have hc0 : 0 ≤ c := le_max_right _ _

  have key : ∀ n : ℕ, ∀ [DiscreteTopology (imageLattice (φ n))] [IsZLattice ℝ (imageLattice (φ n))],
      smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n ≤
        Real.log 6 + r n * Real.log (1 + r n * c) -
          Real.log (ZLattice.covolume (imageLattice (φ n))) := by
    intro n _ _

    have hle : AddSubgroup.closure
        {s | s ∈ chartLat y A.a n ∧ IsBoundedH (mCoordIdeal y) y A n C s} ≤ chartLat y A.a n :=
      (hC n).le
    have hsp : ∀ (t : Ω) (ht : t ∈ AddSubgroup.closure
        {s | s ∈ chartLat y A.a n ∧ IsBoundedH (mCoordIdeal y) y A n C s}),
        φ n ⟨t, hle ht⟩ ∈ Submodule.span ℝ
          (φ n '' {s : chartLat y A.a n | IsBoundedH (mCoordIdeal y) y A n c (s : Ω)}) := by
      intro t ht
      induction ht using AddSubgroup.closure_induction with
      | mem x hx =>
        exact Submodule.subset_span ⟨⟨x, hx.1⟩, hx.2.mono (le_max_left _ _), rfl⟩
      | zero =>
        have : (⟨0, hle (zero_mem _)⟩ : chartLat y A.a n) = 0 := rfl
        rw [this, map_zero]
        exact zero_mem _
      | add x z hx hz ihx ihz =>
        have : (⟨x + z, hle (add_mem hx hz)⟩ : chartLat y A.a n) = ⟨x, hle hx⟩ + ⟨z, hle hz⟩ := rfl
        rw [this, map_add (f := _)]
        exact add_mem ihx ihz
      | neg x hx ihx =>
        have : (⟨-x, hle (neg_mem hx)⟩ : chartLat y A.a n) = -⟨x, hle hx⟩ := rfl
        rw [this, map_neg]
        exact neg_mem ihx
    obtain ⟨B⟩ := exists_shortLatticeBasis (imageLattice (φ n))
      (φ n '' {s : chartLat y A.a n | IsBoundedH (mCoordIdeal y) y A n c (s : Ω)})
      (by rintro _ ⟨s, -, rfl⟩; exact ⟨s, rfl⟩)
      (by
        rintro _ ⟨s, rfl⟩
        have hs : (s : Ω) ∈ AddSubgroup.closure
            {s | s ∈ chartLat y A.a n ∧ IsBoundedH (mCoordIdeal y) y A n C s} := by
          rw [hC n]; exact s.2
        exact hsp s hs)
      (by rintro _ ⟨s, hs, rfl⟩; exact hnorm n c s hc0 hs)
    obtain ⟨hfin, hlog⟩ := log_ncard_ball_le (imageLattice (φ n)) hc0 B
    refine le_trans ?_ hlog
    exact log_card_le_of_injective (imageLattice (φ n))
      (fun a : {s : chartLat y A.a n // IsSmallH (mCoordIdeal y) y A n (s : Ω)} => φ n a.1)
      (fun a b h => Subtype.val_injective (hinj n h))
      (fun a => ⟨⟨a.1, rfl⟩, hnorm n 1 a.1 zero_le_one (IsSmallH.isBoundedH_one a.2)⟩) hfin

  have hu0 : ∀ n : ℕ, 0 ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n /
      ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
    intro n
    apply div_nonneg _ (by positivity)
    exact Real.log_natCast_nonneg _
  refine le_of_forall_pos_le_add fun ε hε => ?_
  refine Filter.limsup_le_of_le (isCoboundedUnder_le_of_le atTop hu0) ?_
  filter_upwards [hdeg (ε / 2) (half_pos hε), eventually_error_le D Cr c hc0 r hr (half_pos hε),
    eventually_ge_atTop 1] with n h1 h2 hn
  have := hdisc n
  have : IsZLattice ℝ (imageLattice (φ n)) := hlat n
  have h1' : -Real.log (ZLattice.covolume (imageLattice (φ n))) ≤
      (II K ι (mCoordIdeal y) (D + 1) (fun _ => A) + ε / 2) *
        ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := h1
  have hk := key n
  have hN : 0 < (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  rw [div_le_iff₀ hN]
  nlinarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PArithKleiman
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ArithKleiman.trivial_hyps (P P0 : Ideal (MRing ι)) :
    ((constLine (ι := ι) 0).a = fun k => ((0 : K → ℕ) k : ℤ)) ∧ IsSemipositiveRel P0 P (constLine (ι := ι) 0) ∧
      MonomialsBounded P (constLine (ι := ι) 0) 0 ∧ IsConjInvariantH (constLine (ι := ι) 0) := by
  have hh : (constLine (ι := ι) 0).h = fun _ => 1 := by
    funext z
    show Real.exp (-0) = 1
    simp
  refine ⟨by funext k; rfl, ⟨?_, fun z _ w _ => ?_⟩, fun z _ μ hμ => ?_, fun z => by rw [hh]⟩
  · show ContDiffOn ℝ _ (fun _ => Real.exp (-(0 : ℝ))) _
    exact contDiffOn_const
  · have hf : (fun z => Real.log ((constLine (ι := ι) 0).h z)) = fun _ => (0 : ℝ) := by
      rw [hh]
      funext z
      simp
    rw [hf]
    simp [leviForm]
  · have h0 : ∀ p, μ p = 0 := by
      rintro ⟨k, i⟩
      have := hμ k
      simp only [Pi.zero_apply, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies] at this
      exact this i
    rw [hh]
    simp [h0]

theorem ArithKleiman.proof (hMix : MixedKleiman.Statement) : ArithKleiman.Statement := by
  intro K _ ι _ P P0 D A II hII hP hP0 hsemi hnef hconj hW
  obtain ⟨ha, hs, hm, hc⟩ := ArithKleiman.trivial_hyps (ι := ι) P P0
  have h := hMix K ι P P0 (D + 1) A (constLine 0) 0 II hII (Nat.succ_pos D) hP hP0 hsemi hnef hconj hW ha hs hm hc
    (D + 1) le_rfl
  have hl : (fun i : Fin (D + 1) => if (i : ℕ) < D + 1 then A else constLine 0) = fun _ => A :=
    funext fun i => if_pos i.isLt
  rwa [hl] at h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.LerpSelfZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

noncomputable section

theorem Weight.lerp_self_zero {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
    {L : HolLineBundle A} (W : Weight L) : W.lerp W 0 = W := by
  cases W
  simp only [Weight.lerp, zero_mul, add_zero]

theorem SupNormAgainstL2.proof (h : UniformBergmanBound.Statement) : SupNormAgainstL2.Statement := by
  intro D X _ _ _ _ _ A L W dV hW
  obtain ⟨C, hC⟩ := h A L W W dV hW hW
  refine ⟨⟨Real.sqrt C, fun n hn s hs x => ?_⟩, fun n s hs M hM => ?_⟩
  · set V : Submodule ℂ (Fin A.n → X → ℂ) := ℂ ∙ s
    have hV : V ≤ L.sections n := (Submodule.span_singleton_le_iff_mem _ _).2 hs
    have hB := hC n hn 0 ⟨le_rfl, zero_le_one⟩ V hV x
    rw [Weight.lerp_self_zero] at hB
    set r := ptNormSq W n s x / sectionL2NormSq W dV n s
    have hr0 : 0 ≤ r := div_nonneg (ptNormSq_nonneg W n s x) (sectionL2NormSq_nonneg W dV n s)
    have hbdd : BddAbove (range fun v : V => ptNormSq W n (v : Fin A.n → X → ℂ) x /
        sectionL2NormSq W dV n v) := by
      refine ⟨r, ?_⟩
      rintro _ ⟨⟨v, hv⟩, rfl⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
      simp only [ptNormSq_smul, sectionL2NormSq_smul]
      rcases eq_or_ne c 0 with rfl | hc
      · simpa using hr0
      · rw [mul_div_mul_left _ _ (by positivity)]
    have hle : r ≤ bergman W dV V n x :=
      le_ciSup hbdd (⟨s, Submodule.mem_span_singleton_self s⟩ : V)
    have hrC : r ≤ C * (n : ℝ) ^ D := hle.trans hB
    rcases (sectionL2NormSq_nonneg W dV n s).eq_or_lt with h0 | hpos
    · rw [ptNormSq_eq_zero_of_l2NormSq_eq_zero W dV hs h0.symm x, Real.sqrt_zero]
      positivity
    · have hpt : ptNormSq W n s x ≤ C * ((n : ℝ) ^ D * sectionL2NormSq W dV n s) := by
        rw [← mul_assoc, ← div_le_iff₀ hpos]; exact hrC
      calc Real.sqrt (ptNormSq W n s x)
          ≤ Real.sqrt (C * ((n : ℝ) ^ D * sectionL2NormSq W dV n s)) := Real.sqrt_le_sqrt hpt
        _ = Real.sqrt C * Real.sqrt ((n : ℝ) ^ D) * Real.sqrt (sectionL2NormSq W dV n s) := by
          rw [Real.sqrt_mul' _ (by positivity), Real.sqrt_mul (by positivity), mul_assoc]
  · have := dV.isProb
    obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure dV.μ
    have hM0 : 0 ≤ M := (Real.sqrt_nonneg _).trans (hM x₀)
    have hpt : ∀ y, ptNormSq W n s y ≤ M ^ 2 := fun y => by
      have h1 := Real.sq_sqrt (ptNormSq_nonneg W n s y)
      have h2 := hM y
      nlinarith [Real.sqrt_nonneg (ptNormSq W n s y)]
    have hl2 : sectionL2NormSq W dV n s ≤ M ^ 2 := by
      calc sectionL2NormSq W dV n s ≤ ∫ _ : X, M ^ 2 ∂dV.μ :=
            integral_mono_of_nonneg (Eventually.of_forall fun y => ptNormSq_nonneg W n s y)
              (integrable_const _) (Eventually.of_forall hpt)
        _ = M ^ 2 := by simp
    calc Real.sqrt (sectionL2NormSq W dV n s) ≤ Real.sqrt (M ^ 2) := Real.sqrt_le_sqrt hl2
      _ = M := Real.sqrt_sq hM0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
