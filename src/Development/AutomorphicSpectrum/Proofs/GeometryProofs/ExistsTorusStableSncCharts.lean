module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartIdealLocalizationMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStableEigenTangents

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBis
theorem UpperTheory.Reformulated.B.DYdc4.main :
    ∀ (n a : ℕ) (G : Finset (Fin n)),
      G.card = a → ∃ (τ : Equiv.Perm (Fin n)), ∀ (j : Fin n), (↑j : ℕ) < a ↔ (τ : Fin n → Fin n) j ∈ G := by
  intro n a G hG
  have ha : a ≤ n := by
    have h := G.card_le_univ
    rw [Fintype.card_fin, hG] at h
    exact h
  have hp : Fintype.card {x : Fin n // (x : ℕ) < a} = a := by
    have e : Fin a ≃ {x : Fin n // (x : ℕ) < a} :=
      { toFun := fun i => ⟨Fin.castLE ha i, i.isLt⟩
        invFun := fun x => ⟨x.1.1, x.2⟩
        left_inv := fun i => rfl
        right_inv := fun x => rfl }
    rw [← Fintype.card_congr e, Fintype.card_fin]
  have hq : Fintype.card {x : Fin n // x ∈ G} = a := by
    rw [Fintype.card_coe, hG]
  let e : {x : Fin n // (x : ℕ) < a} ≃ {x : Fin n // x ∈ G} :=
    Fintype.equivOfCardEq (hp.trans hq.symm)
  refine ⟨e.extendSubtype, fun j => ⟨fun h => e.extendSubtype_mem j h, fun h => ?_⟩⟩
  by_contra h'
  exact e.extendSubtype_not_mem j h' h
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularLocalChartCoords
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularLocalChartCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.ChartParams

theorem eval_unren_eq_zero {σ : Type} [Fintype σ] (Q : Ideal (MvPolynomial σ ℂ))
    (v : Fin (Fintype.card σ) → ℂ)
    (hv : v ∈ ReciprocityTheory.AnForm.R.zeroSet (Q.map (ReciprocityTheory.AnForm.R.renR σ : MvPolynomial σ ℂ →+* _))) :
    ∀ f ∈ Q, eval (fun q => v (Fintype.equivFin σ q)) f = 0 := by
  intro f hf
  have h1 := hv (ReciprocityTheory.AnForm.R.renC σ f) (Ideal.mem_map_of_mem _ hf)
  have h2 := ReciprocityTheory.AnForm.R.eval_renC (fun q => v (Fintype.equivFin σ q)) f
  have h3 : ReciprocityTheory.AnForm.R.renPt (fun q => v (Fintype.equivFin σ q)) = v := by
    funext j; simp [ReciprocityTheory.AnForm.R.renPt]
  rw [h3, h1] at h2
  exact h2.symm

theorem analyticOnNhd_rescale {σ : Type} {n m : ℕ} (e : σ ≃ Fin m) (g : (Fin n → ℂ) → Fin m → ℂ)
    (V : Set (Fin n → ℂ)) (hg : AnalyticOnNhd ℂ g V) (ε : ℝ) (hεV : Metric.ball 0 ε ⊆ V) (hε : 0 < ε) :
    ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ q, AnalyticAt ℂ (fun s => g ((ε : ℂ) • s) (e q)) t := by
  intro t ht q
  have hmem : (ε : ℂ) • t ∈ V := by
    apply hεV
    rw [mem_ball_zero_iff] at ht ⊢
    rw [norm_smul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    nlinarith
  have h1 : AnalyticAt ℂ (fun s : Fin n → ℂ => (ε : ℂ) • s) t :=
    ((ε : ℂ) • ContinuousLinearMap.id ℂ (Fin n → ℂ)).analyticAt t
  have h2 : AnalyticAt ℂ (fun s => g ((ε : ℂ) • s)) t :=
    AnalyticAt.comp (f := fun s : Fin n → ℂ => (ε : ℂ) • s) (hg _ hmem) h1
  exact (analyticAt_pi_iff (f := fun l s => g ((ε : ℂ) • s) l)).mp h2 (e q)

theorem eq_zero_of_fderiv_eq_zero {σ : Type} [Fintype σ] {n m : ℕ} (e : σ ≃ Fin m)
    (r : Fin n → MvPolynomial (Fin m) ℂ) (gm : (Fin n → ℂ) → σ → ℂ) (ε : ℂ) (hε : ε ≠ 0)
    (t : Fin n → ℂ) (hgm : DifferentiableAt ℂ gm t)
    (hr : ∀ᶠ s in nhds t, ReciprocityTheory.AnForm.R.evalFam r (fun j => gm s (e.symm j)) = ε • s)
    (v : Fin n → ℂ) (hv : fderiv ℂ gm t v = 0) : v = 0 := by
  let R : (σ → ℂ) → Fin n → ℂ := fun y i => eval (fun j => y (e.symm j)) (r i)
  have hR : DifferentiableAt ℂ R (gm t) := by
    have han : AnalyticAt ℂ R (gm t) := by
      rw [analyticAt_pi_iff]
      intro i
      refine ReciprocityTheory.AnForm.R.analyticAt_eval_of_pi
        (f := fun (y : σ → ℂ) (j : Fin m) => y (e.symm j)) (fun l => ?_) (r i)
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) (e.symm l)).analyticAt _
    exact han.differentiableAt
  have hc : HasFDerivAt (R ∘ gm) ((fderiv ℂ R (gm t)).comp (fderiv ℂ gm t)) t :=
    hR.hasFDerivAt.comp t hgm.hasFDerivAt
  have hs : HasFDerivAt (R ∘ gm) (ε • ContinuousLinearMap.id ℂ (Fin n → ℂ)) t := by
    have h0 : HasFDerivAt (fun s : Fin n → ℂ => ε • s)
        (ε • ContinuousLinearMap.id ℂ (Fin n → ℂ)) t :=
      (hasFDerivAt_id t).const_smul ε
    exact h0.congr_of_eventuallyEq hr
  have heq := hc.unique hs
  have h1 := congrArg (fun L => L v) heq
  simp only [ContinuousLinearMap.comp_apply, hv, map_zero, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply] at h1
  exact (smul_eq_zero.mp h1.symm).resolve_left hε

theorem sncChart_of_regular_parameters : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J))
    (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC P)) (n : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (c : (k : K) → J k)
    (w : (Σ k, J k) → ℂ), w ∈ mcPts P → (∀ k, w ⟨k, c k⟩ ≠ 0) →
    ∀ (a : ℕ) (r : Fin n → MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ)
      (h : MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ)
      [IsRegularLocalRing (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
        (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w)))],
    ringKrullDim (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
      (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))) = n → a ≤ n →
    Ideal.span (Set.range fun i => algebraMap _ (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
      (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))) (r i)) =
      Ideal.map (algebraMap _ (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
        (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))))
        (ReciprocityTheory.AnForm.R.ptIdeal (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))) →
    (∀ i, eval (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w)) (r i) = 0) →
    eval (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w)) h ≠ 0 →
    (∀ v ∈ ReciprocityTheory.AnForm.R.zeroSet (Cmp.SncRes.ideal (pC P) c), eval v h ≠ 0 →
      ((fun q => v (Fintype.equivFin (Σ k, J k) q)) ∈ Bd ↔ ∃ i : Fin n, (i : ℕ) < a ∧ eval v (r i) = 0)) →
    ∃ (χ : SncChart P n Bd) (O : Set ((Σ k, J k) → ℂ)), IsOpen O ∧ w ∈ O ∧
      ∀ z ∈ O ∩ mcPts P, ∃ t : Fin n → ℂ, ‖t‖ ≤ 1 / 2 ∧ ∃ c' : K → ℂ, (∀ k, c' k ≠ 0) ∧
        z = torusSmul c' (χ.γ t) := by
  intro K _ J _ P hP n Bd c w hw hwc a r h _ hdim haN hspan hr0 hh0 hbd
  classical
  set I := Cmp.SncRes.ideal (pC P) c with hI
  set p := ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w) with hp
  have hcone : ∀ z, z ∈ mcPts P → (∀ k, z ⟨k, c k⟩ ≠ 0) →
      ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c z) ∈ ReciprocityTheory.AnForm.R.zeroSet I := by
    intro z hz hzc
    have h1 := (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hP c z hzc).1
      ((mem_mcPts_iff_conePts_pC P z).1 hz)
    exact ReciprocityTheory.AnForm.R.renPt_zero _ _ h1
  have hpz : p ∈ ReciprocityTheory.AnForm.R.zeroSet I := hcone w hw hwc
  obtain ⟨U, V, g, hU, hpU, hV, hg, hbij, hrg⟩ :=
    ReciprocityTheory.AnForm.R.exists_holo_coords I p n hdim r hspan

  have hsolve : ∀ v ∈ U ∩ ReciprocityTheory.AnForm.R.zeroSet I,
      ReciprocityTheory.AnForm.R.evalFam r v ∈ V ∧ g (ReciprocityTheory.AnForm.R.evalFam r v) = v := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := hbij.surjOn hv
    rw [hrg u hu]
    exact ⟨hu, rfl⟩
  have hr0' : ReciprocityTheory.AnForm.R.evalFam r p = 0 := funext hr0
  obtain ⟨h0V, hg0⟩ := hsolve p ⟨hpU, hpz⟩
  rw [hr0'] at h0V hg0

  have hcont0 : ContinuousAt g 0 := (hg 0 h0V).continuousAt
  have hnear : ∀ᶠ u in nhds (0 : Fin n → ℂ), u ∈ V ∧ eval (g u) h ≠ 0 := by
    have hVn : ∀ᶠ u in nhds (0 : Fin n → ℂ), u ∈ V := hV.mem_nhds h0V
    refine hVn.and ?_
    have hc : ContinuousAt (fun u => eval (g u) h) 0 :=
      (MvPolynomial.continuous_eval h).continuousAt.comp hcont0
    refine hc.eventually_ne ?_
    rw [hg0]; exact hh0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hnear
  have hεV : Metric.ball (0 : Fin n → ℂ) ε ⊆ V := fun u hu => (hball u hu).1
  have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have hsc : ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1, (ε : ℂ) • t ∈ Metric.ball (0 : Fin n → ℂ) ε := by
    intro t ht
    rw [mem_ball_zero_iff] at ht ⊢
    rw [norm_smul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    nlinarith
  let e := Fintype.equivFin (Σ k, J k)
  let gm : (Fin n → ℂ) → (Σ k, J k) → ℂ := fun t q => g ((ε : ℂ) • t) (e q)

  have hzs : ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1, g ((ε : ℂ) • t) ∈ ReciprocityTheory.AnForm.R.zeroSet I :=
    fun t ht => (hbij.mapsTo (hεV (hsc t ht))).2
  have hchart : ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1,
      gm t ∈ ReciprocityTheory.AnForm.R.conePts (pC P) ∧ ∀ k, gm t ⟨k, c k⟩ = 1 := by
    intro t ht
    have h1 := ReciprocityTheory.AnForm.R.conePts_of_chartIdeal hP c (gm t)
      (eval_unren_eq_zero _ _ (hzs t ht))
    exact ⟨h1.1, h1.2.1⟩
  have hcoord : ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1,
      ReciprocityTheory.AnForm.R.evalFam r (g ((ε : ℂ) • t)) = (ε : ℂ) • t :=
    fun t ht => hrg _ (hεV (hsc t ht))
  have han : AnalyticOnNhd ℂ gm (Metric.ball 0 1) := fun t ht =>
    AnalyticAt.pi (f := fun q s => g ((ε : ℂ) • s) (e q))
      (analyticOnNhd_rescale e g V hg ε hεV hε t ht)
  refine ⟨SncChart.mk gm a haN han ?_ ?_ ?_ ?_, {z | (∀ k, z ⟨k, c k⟩ ≠ 0) ∧
              ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c z) ∈ U ∧
              ‖ReciprocityTheory.AnForm.R.evalFam r (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c z))‖ < ε / 2},
            ?_, ⟨hwc, hpU, ?_⟩, ?_⟩
  · exact fun t ht => (mem_mcPts_iff_conePts_pC P _).2 (hchart t ht).1
  · intro t ht v ⟨c', hc'⟩
    have hdiff : DifferentiableAt ℂ gm t := (han t ht).differentiableAt
    have hcomp : ∀ k, c' k = 0 := by
      intro k
      have h1 := congrFun hc' ⟨k, c k⟩
      have h2 : (fun s => gm s ⟨k, c k⟩) =ᶠ[nhds t] fun _ => (1 : ℂ) := by
        filter_upwards [Metric.isOpen_ball.mem_nhds ht] with s hs using (hchart s hs).2 k
      have h3 : HasFDerivAt (fun s => gm s ⟨k, c k⟩)
          ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) ⟨k, c k⟩).comp
            (fderiv ℂ gm t)) t :=
        (hasFDerivAt_pi'.1 hdiff.hasFDerivAt) ⟨k, c k⟩
      have h4 := h3.unique ((hasFDerivAt_const (1 : ℂ) t).congr_of_eventuallyEq h2)
      have h5 := congrArg (fun L => L v) h4
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
        ContinuousLinearMap.zero_apply] at h5
      rw [h1] at h5
      simpa [torusSmul, (hchart t ht).2 k] using h5
    have hzero : fderiv ℂ gm t v = 0 := by
      rw [hc']; funext q; simp [torusSmul, hcomp q.1]
    refine eq_zero_of_fderiv_eq_zero e r gm (ε : ℂ) hεc t hdiff ?_ v hzero
    filter_upwards [Metric.isOpen_ball.mem_nhds ht] with s hs
    have : (fun j => gm s (e.symm j)) = g ((ε : ℂ) • s) := by
      funext j; simp [gm]
    rw [this]
    exact hcoord s hs
  · intro t ht t' ht' c' hc' he
    have hone : ∀ k, c' k = 1 := by
      intro k
      have h1 := congrFun he ⟨k, c k⟩
      simpa [torusSmul, (hchart t ht).2 k, (hchart t' ht').2 k] using h1.symm
    have hgg : g ((ε : ℂ) • t) = g ((ε : ℂ) • t') := by
      funext j
      have h1 := congrFun he (e.symm j)
      simpa [gm, torusSmul, hone] using h1
    have h2 := (hcoord t ht).symm.trans ((congrArg _ hgg).trans (hcoord t' ht'))
    exact smul_right_injective _ hεc h2
  · intro t ht
    have h1 := hbd (g ((ε : ℂ) • t)) (hzs t ht) (hball _ (hsc t ht)).2
    refine h1.trans ?_
    have h2 : ∀ i, eval (g ((ε : ℂ) • t)) (r i) = (ε : ℂ) * t i := fun i =>
      congrFun (hcoord t ht) i
    simp only [h2, mul_eq_zero, hεc, false_or]
  · have hA : IsOpen {z : (Σ k, J k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0} := by
      have : {z : (Σ k, J k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0} = ⋂ k, {z | z ⟨k, c k⟩ ≠ 0} := by
        ext z; simp
      rw [this]
      exact isOpen_iInter_of_finite fun k => isOpen_ne_fun (continuous_apply _) continuous_const
    have hf : ContinuousOn (fun z : (Σ k, J k) → ℂ =>
        ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c z))
        {z : (Σ k, J k) → ℂ | ∀ k, z ⟨k, c k⟩ ≠ 0} := by
      refine continuousOn_pi.2 fun j => ?_
      simp only [ReciprocityTheory.AnForm.R.renPt, ReciprocityTheory.AnForm.R.affCoord, Function.comp_apply]
      exact (continuous_apply _).continuousOn.div (continuous_apply _).continuousOn
        fun z hz => hz _
    have hev : Continuous (ReciprocityTheory.AnForm.R.evalFam r) :=
      continuous_pi fun l => MvPolynomial.continuous_eval (p := r l)
    have hT : IsOpen (U ∩ ReciprocityTheory.AnForm.R.evalFam r ⁻¹' {u | ‖u‖ < ε / 2}) :=
      hU.inter (isOpen_lt continuous_norm continuous_const |>.preimage hev)
    have := hf.isOpen_inter_preimage hA hT
    exact this
  · show ‖ReciprocityTheory.AnForm.R.evalFam r p‖ < ε / 2
    rw [hr0', norm_zero]; positivity
  · rintro z ⟨⟨hzc, hzU, hzn⟩, hzm⟩
    obtain ⟨hv1, hv2⟩ := hsolve _ ⟨hzU, hcone z hzm hzc⟩
    set v := ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c z) with hv
    set u := ReciprocityTheory.AnForm.R.evalFam r v with hu
    refine ⟨(ε : ℂ)⁻¹ • u, ?_, fun k => z ⟨k, c k⟩, hzc, ?_⟩
    · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
      rw [inv_mul_le_iff₀ hε]
      linarith
    · funext q
      show z q = z ⟨q.1, c q.1⟩ * g ((ε : ℂ) • (ε : ℂ)⁻¹ • u) (e q)
      rw [smul_inv_smul₀ hεc, hv2]
      have hvq : v (e q) = ReciprocityTheory.AnForm.R.affCoord c z q := by
        show ReciprocityTheory.AnForm.R.affCoord c z (e.symm (e q)) = _
        rw [Equiv.symm_apply_apply]
      rw [hvq]
      simp only [ReciprocityTheory.AnForm.R.affCoord]
      rw [mul_div_cancel₀ _ (hzc q.1)]

end GlobalTheory.CompanionTheory.Ar.ChartParams
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularLocalChartCoordsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_local_chart_coords : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J))
    (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC P)) (n : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (c : (k : K) → J k)
    (w : (Σ k, J k) → ℂ), w ∈ mcPts P → (∀ k, w ⟨k, c k⟩ ≠ 0) →
    ∀ (a : ℕ) (r : Fin n → MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ)
      (h : MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ)
      [IsRegularLocalRing (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
        (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w)))],
    ringKrullDim (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
      (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))) = n → a ≤ n →
    Ideal.span (Set.range fun i => algebraMap _ (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
      (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))) (r i)) =
      Ideal.map (algebraMap _ (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC P) c)
        (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))))
        (ReciprocityTheory.AnForm.R.ptIdeal (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))) →
    (∀ i, eval (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w)) (r i) = 0) →
    eval (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w)) h ≠ 0 →
    (∀ v ∈ ReciprocityTheory.AnForm.R.zeroSet (Cmp.SncRes.ideal (pC P) c), eval v h ≠ 0 →
      ((fun q => v (Fintype.equivFin (Σ k, J k) q)) ∈ Bd ↔ ∃ i : Fin n, (i : ℕ) < a ∧ eval v (r i) = 0)) →
    ∃ (χ : SncChart P n Bd) (O : Set ((Σ k, J k) → ℂ)), IsOpen O ∧ w ∈ O ∧
      ∀ z ∈ O ∩ mcPts P, ∃ t : Fin n → ℂ, ‖t‖ ≤ 1 / 2 ∧ ∃ c' : K → ℂ, (∀ k, c' k ≠ 0) ∧
        z = torusSmul c' (χ.γ t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartParams.sncChart_of_regular_parameters | exact GlobalTheory.CompanionTheory.Ar.ChartParams.sncChart_of_regular_parameters | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartParams.sncChart_of_regular_parameters <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdjoinInverseElementForm
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdjoinInverseElementForm
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ggeo

theorem exists_numerator_of_mem_adjoin_insert_inv :
    ∀ (T : Type) (Ω : Type) [Field Ω] [CharZero Ω] (u : T → Ω) (f : Ω) (S : Subalgebra ℚ Ω),
    S = Algebra.adjoin ℚ (insert f⁻¹ (Set.range u)) → ∀ F : MvPolynomial T ℚ, aeval u F = f → f ≠ 0 → ∀ s : S,
    ∃ (G : MvPolynomial T ℚ) (k : ℕ), (s : Ω) * f ^ k = aeval u G := by
  intro T Ω _ _ u f S hS F hF hf s
  obtain ⟨s, hs⟩ := s
  subst hS
  show ∃ (G : MvPolynomial T ℚ) (k : ℕ), s * f ^ k = aeval u G
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | ⟨i, rfl⟩
    · exact ⟨1, 1, by simp [hf]⟩
    · exact ⟨X i, 0, by simp⟩
  | algebraMap q => exact ⟨C q, 0, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨G₁, k₁, h₁⟩ := ihx
    obtain ⟨G₂, k₂, h₂⟩ := ihy
    refine ⟨G₁ * F ^ k₂ + G₂ * F ^ k₁, k₁ + k₂, ?_⟩
    simp only [map_add (f := _), map_mul, map_pow, hF, ← h₁, ← h₂]
    ring
  | mul x y _ _ ihx ihy =>
    obtain ⟨G₁, k₁, h₁⟩ := ihx
    obtain ⟨G₂, k₂, h₂⟩ := ihy
    refine ⟨G₁ * G₂, k₁ + k₂, ?_⟩
    simp only [map_mul, ← h₁, ← h₂]
    ring

end GlobalTheory.CompanionTheory.Ggeo
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdjoinInverseElementFormStatement
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoin_inverse_element_form : ∀ (T : Type) (Ω : Type) [Field Ω] [CharZero Ω] (u : T → Ω) (f : Ω) (S : Subalgebra ℚ Ω),
    S = Algebra.adjoin ℚ (insert f⁻¹ (Set.range u)) → ∀ F : MvPolynomial T ℚ, aeval u F = f → f ≠ 0 → ∀ s : S,
    ∃ (G : MvPolynomial T ℚ) (k : ℕ), (s : Ω) * f ^ k = aeval u G := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.exists_numerator_of_mem_adjoin_insert_inv | exact GlobalTheory.CompanionTheory.Ggeo.exists_numerator_of_mem_adjoin_insert_inv | (intros; apply GlobalTheory.CompanionTheory.Ggeo.exists_numerator_of_mem_adjoin_insert_inv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerDifferentialsSpanLocal
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerDifferentialsSpanLocal
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Kaehler

theorem derivation_mem_span {S B M : Type} [CommRing S] [Algebra ℚ S] [CommRing B]
    [AddCommGroup M] [Module B M] (ψ : S →+* B) (D₀ : S →+ M)
    (leib : ∀ a b, D₀ (a * b) = ψ a • D₀ b + ψ b • D₀ a)
    {n : ℕ} (z : Fin n → S)
    (hz : Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤) (s : S) :
    D₀ s ∈ Submodule.span B (Set.range fun i => D₀ (z i)) := by
  let _ : Module S M := Module.compHom M ψ
  let _ : Module ℚ M := Module.compHom M (algebraMap ℚ S)
  have : IsScalarTower ℚ S M := ⟨fun q a x => by
    change ψ (q • a) • x = ψ (algebraMap ℚ S q) • (ψ a • x)
    rw [Algebra.smul_def, map_mul, mul_smul]⟩
  have hsm : ∀ (a : S) (x : M), a • x = ψ a • x := fun _ _ => rfl
  let D : Derivation ℚ S M := Derivation.mk' D₀.toRatLinearMap (fun a b => by
    simpa [hsm] using leib a b)
  have hD : ∀ a, D a = D₀ a := fun _ => rfl
  let L := D.liftKaehlerDifferential
  have hL : ∀ a, L (KaehlerDifferential.D ℚ S a) = D₀ a := fun a => by
    simp [L, hD]
  have key : ∀ x : Ω[S⁄ℚ], L x ∈ Submodule.span B (Set.range fun i => D₀ (z i)) := by
    intro x
    have hx : x ∈ Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) := by
      rw [hz]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      rw [hL]
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add y w _ _ hy hw => rw [map_add]; exact add_mem hy hw
    | smul a y _ hy =>
      rw [map_smul, hsm]
      exact Submodule.smul_mem _ _ hy
  simpa [hL] using key (KaehlerDifferential.D ℚ S s)

theorem maximalIdeal_eq_span_of_span_D :
    ∀ (S B : Type) [CommRing S] [Algebra ℚ S] [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [Algebra ℂ B] (ψ : S →+* B) (φ : S →+* ℂ),
    (∀ s, ψ s - algebraMap ℂ B (φ s) ∈ IsLocalRing.maximalIdeal B) →
    ∀ (T : Set S), IsLocalRing.maximalIdeal B = Ideal.span ((fun s => ψ s - algebraMap ℂ B (φ s)) '' T) →
    ∀ (n : ℕ) (z : Fin n → S),
    Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ →
    IsLocalRing.maximalIdeal B = Ideal.span (Set.range fun i => ψ (z i) - algebraMap ℂ B (φ (z i))) := by
  intro S B _ _ _ _ _ _ ψ φ hmem T hT n z hz
  set m := IsLocalRing.maximalIdeal B with hm
  set f : S → B := fun s => ψ s - algebraMap ℂ B (φ s) with hf
  set J : Ideal B := Ideal.span (Set.range fun i => f (z i)) with hJ
  have hJm : J ≤ m := by
    rw [hJ, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem (z i)
  let D₀ : S →+ m.Cotangent :=
    { toFun := fun s => m.toCotangent ⟨f s, hmem s⟩
      map_zero' := by
        have : (⟨f 0, hmem 0⟩ : m) = 0 := by ext; simp [hf]
        rw [this, map_zero]
      map_add' := fun a b => by
        rw [← map_add (f := _)]
        congr 1
        ext
        simp [hf]
        ring }
  have hD₀ : ∀ s, D₀ s = m.toCotangent ⟨f s, hmem s⟩ := fun _ => rfl
  have leib : ∀ a b, D₀ (a * b) = ψ a • D₀ b + ψ b • D₀ a := by
    intro a b
    rw [hD₀, hD₀, hD₀, ← map_smul, ← map_smul, ← map_add (f := _), Ideal.toCotangent_eq]
    have h2 : f a * f b ∈ m ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul (hmem a) (hmem b)
    have : ((⟨f (a * b), hmem (a * b)⟩ : m) : B)
        - ((ψ a • (⟨f b, hmem b⟩ : m) + ψ b • (⟨f a, hmem a⟩ : m) : m) : B) = -(f a * f b) := by
      simp [hf]
      ring
    rw [this]
    exact (m ^ 2).neg_mem h2
  have hspan : ∀ s, D₀ s ∈ Submodule.span B (Set.range fun i => D₀ (z i)) :=
    derivation_mem_span ψ D₀ leib z hz
  let Q : Submodule B m.Cotangent := Submodule.map m.toCotangent (Submodule.comap m.subtype J)
  have hPQ : Submodule.span B (Set.range fun i => D₀ (z i)) ≤ Q := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨f (z i), hmem (z i)⟩, Ideal.subset_span ⟨i, rfl⟩, rfl⟩
  have hfs : ∀ s, f s ∈ J ⊔ m • m := by
    intro s
    obtain ⟨y, hyJ, hy⟩ := hPQ (hspan s)
    have hy' := (Ideal.toCotangent_eq (I := m)).1 (hy.trans (hD₀ s))
    have hsub : f s = (y : B) - ((y : B) - f s) := by ring
    rw [hsub]
    refine Submodule.sub_mem _ (Submodule.mem_sup_left hyJ) (Submodule.mem_sup_right ?_)
    simpa [pow_two] using hy'
  have hle : m ≤ J ⊔ m • m := by
    conv_lhs => rw [hT]
    rw [Ideal.span_le]
    rintro _ ⟨s, _, rfl⟩
    exact hfs s
  apply le_antisymm _ hJm
  exact Submodule.le_of_le_smul_of_le_jacobson (IsNoetherian.noetherian m)
    (by simpa only [Ideal.jacobson_bot] using
      (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal B))) hle

end GlobalTheory.CompanionTheory.Kaehler
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerDifferentialsSpanLocalStatement
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_differentials_span_local : ∀ (S B : Type) [CommRing S] [Algebra ℚ S] [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [Algebra ℂ B] (ψ : S →+* B) (φ : S →+* ℂ),
    (∀ s, ψ s - algebraMap ℂ B (φ s) ∈ IsLocalRing.maximalIdeal B) →
    ∀ (T : Set S), IsLocalRing.maximalIdeal B = Ideal.span ((fun s => ψ s - algebraMap ℂ B (φ s)) '' T) →
    ∀ (n : ℕ) (z : Fin n → S),
    Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ →
    IsLocalRing.maximalIdeal B = Ideal.span (Set.range fun i => ψ (z i) - algebraMap ℂ B (φ (z i))) := by
  first | exact @GlobalTheory.CompanionTheory.Kaehler.maximalIdeal_eq_span_of_span_D | exact GlobalTheory.CompanionTheory.Kaehler.maximalIdeal_eq_span_of_span_D | (intros; apply GlobalTheory.CompanionTheory.Kaehler.maximalIdeal_eq_span_of_span_D <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTorusStableSncCharts
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.SncCpt

open ReciprocityTheory.AnForm.R (locRing locPt ptIdeal renPt renC renR zeroSet)

theorem exists_ev {m : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ)) (p : Fin m → ℂ) (hI : ∀ g ∈ I, eval p g = 0) :
    ∃ π : locRing I p →+* ℂ, ∀ g, π (algebraMap _ _ g) = eval p g := by
  let π0 : locPt p →+* ℂ := IsLocalization.lift (M := (ptIdeal p).primeCompl)
    (g := (eval p : MvPolynomial (Fin m) ℂ →+* ℂ))
    (fun s => isUnit_iff_ne_zero.2 (fun h => s.2 (RingHom.mem_ker.2 h)))
  have h0 : ∀ g, π0 (algebraMap _ _ g) = eval p g := fun g => IsLocalization.lift_eq _ g
  have hk : ∀ a ∈ Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) I, π0 a = 0 := by
    have : Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) I ≤ RingHom.ker π0 := by
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      simp only [Ideal.mem_comap, RingHom.mem_ker, h0, hI g hg]
    exact fun a ha => this ha
  refine ⟨Ideal.Quotient.lift _ π0 hk, fun g => ?_⟩
  exact (Ideal.Quotient.lift_mk _ π0 hk).trans (h0 g)

theorem isUnit_loc {m : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ)) (p : Fin m → ℂ)
    (g : MvPolynomial (Fin m) ℂ) (hg : eval p g ≠ 0) : IsUnit (algebraMap _ (locRing I p) g) := by
  have := (IsLocalization.map_units (locPt p)
    (⟨g, fun h => hg (RingHom.mem_ker.mp h)⟩ : (ptIdeal p).primeCompl)).map
    (algebraMap (locPt p) (locRing I p))
  rwa [← IsScalarTower.algebraMap_apply] at this

theorem span_eq_of_unit {B ι' : Type*} [CommRing B] (a b : ι' → B) (u : ι' → B) (hu : ∀ i, IsUnit (u i))
    (h : ∀ i, a i = b i * u i) : Ideal.span (Set.range a) = Ideal.span (Set.range b) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [h i]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨v, hv⟩ := (hu i).exists_right_inv
    have : b i = a i * v := by rw [h i, _root_.mul_assoc, hv, _root_.mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem exists_perm (n a : ℕ) (G : Finset (Fin n)) (hG : G.card = a) :
    ∃ τ : Equiv.Perm (Fin n), ∀ j : Fin n, (j : ℕ) < a ↔ τ j ∈ G :=
  _root_.UpperTheory.Reformulated.B.DYdc4.main n a G hG

end GlobalTheory.CompanionTheory.Ar.SncCpt

namespace GlobalTheory.CompanionTheory.Ar.SncCpt

open ReciprocityTheory.AnForm.R (locRing locPt ptIdeal renPt renC renR zeroSet)

theorem snc_params : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)),
    ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) → Cmp.IsSncModel y n bd →
    ∀ (c : (k : K) → J k) (w : (Σ k, J k) → ℂ), w ∈ mcPts (mCoordIdeal y) → (∀ k, w ⟨k, c k⟩ ≠ 0) →
    [IsLocalRing (locRing (Cmp.SncRes.ideal (pC (mCoordIdeal y)) c) (renPt (ReciprocityTheory.AnForm.R.affCoord c w)))] →
    [IsNoetherianRing (locRing (Cmp.SncRes.ideal (pC (mCoordIdeal y)) c) (renPt (ReciprocityTheory.AnForm.R.affCoord c w)))] →
    ∃ (a : ℕ) (r : Fin n → MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ)
      (h : MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ), a ≤ n ∧
      Ideal.span (Set.range fun i => algebraMap _ (locRing (Cmp.SncRes.ideal (pC (mCoordIdeal y)) c)
        (renPt (ReciprocityTheory.AnForm.R.affCoord c w))) (r i)) =
        Ideal.map (algebraMap _ (locRing (Cmp.SncRes.ideal (pC (mCoordIdeal y)) c) (renPt (ReciprocityTheory.AnForm.R.affCoord c w))))
          (ptIdeal (renPt (ReciprocityTheory.AnForm.R.affCoord c w))) ∧
      (∀ i, eval (renPt (ReciprocityTheory.AnForm.R.affCoord c w)) (r i) = 0) ∧
      eval (renPt (ReciprocityTheory.AnForm.R.affCoord c w)) h ≠ 0 ∧
      ∀ v ∈ zeroSet (Cmp.SncRes.ideal (pC (mCoordIdeal y)) c), eval v h ≠ 0 →
        ((fun q => v (Fintype.equivFin (Σ k, J k) q)) ∈ mcPts (mCoordIdeal y) ∩ mcPts bd ↔
          ∃ i : Fin n, (i : ℕ) < a ∧ eval v (r i) = 0) := by
  intro K _ J _ Ω _ _ y n bd hPh hS c w hw hwc _ _
  classical
  obtain ⟨u, hu⟩ : ∃ u : (Σ k, J k) → Ω, u = fun p => y p / y ⟨p.1, c p.1⟩ := ⟨_, rfl⟩
  obtain ⟨I, hI⟩ : ∃ I, I = Cmp.SncRes.ideal (pC (mCoordIdeal y)) c := ⟨_, rfl⟩
  obtain ⟨pt, hpt⟩ : ∃ pt, pt = renPt (ReciprocityTheory.AnForm.R.affCoord c w) := ⟨_, rfl⟩
  obtain ⟨CI, hCI⟩ : ∃ CI, CI = ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c := ⟨_, rfl⟩
  rw [← hI, ← hpt]
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    have hmem : (X ⟨k, c k⟩ : MRing J) ∈ mCoordIdeal y := by
      apply RingHom.mem_ker.2
      simp [mConeMap, h0]
    have := hw.2 _ hmem
    simp only [map_X, eval_X] at this
    exact hwc k this
  have hz0 : ∀ g ∈ CI, eval (ReciprocityTheory.AnForm.R.affCoord c w) g = 0 := by
    rw [hCI]
    exact (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hPh c w hwc).1 ((mem_mcPts_iff_conePts_pC _ _).1 hw)
  have hrenI : ∀ g ∈ CI, renC (Σ k, J k) g ∈ I := by
    intro g hg
    rw [hI, Cmp.SncRes.ideal]
    rw [hCI] at hg
    have := (ReciprocityTheory.AnForm.R.mem_map_renR_iff (ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c)
      (renR (Σ k, J k) g)).2 (by simpa using hg)
    exact this
  have hI0 : ∀ g ∈ I, eval pt g = 0 := by
    rw [hpt, hI]
    exact ReciprocityTheory.AnForm.R.renPt_zero _ _ (by rw [← hCI]; exact hz0)
  have hker : ∀ G : MvPolynomial (Σ k, J k) ℚ, aeval u G = (0 : Ω) → map (algebraMap ℚ ℂ) G ∈ CI := by
    rw [hu, hCI]
    exact GlobalTheory.T.rational_relation_in_chart_ideal K J Ω y c hc
  obtain ⟨m, f, aa, hf, ha, hsum, hl⟩ := hS c hc
  rw [← hu] at hf ha
  have hpoly : ∀ s ∈ Algebra.adjoin ℚ (Set.range u), ∃ G : MvPolynomial (Σ k, J k) ℚ, aeval u G = s := by
    intro s hs
    rw [Algebra.adjoin_range_eq_range_aeval] at hs
    exact hs
  choose F hF using fun l => hpoly (f l) (hf l)
  choose A hAa using fun l => hpoly (aa l) (ha l)
  obtain ⟨l, hl0⟩ : ∃ l, eval (ReciprocityTheory.AnForm.R.affCoord c w) (map (algebraMap ℚ ℂ) (F l)) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h1 : aeval u (∑ l, A l * F l - 1) = (0 : Ω) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sub, map_sum, map_mul, hF, hAa, hsum, map_one, sub_self]
    have h2 := hz0 _ (hker _ h1)
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sub, map_sum, map_mul, hcon] at h2
  have hf0 : f l ≠ 0 := by
    intro h0
    exact hl0 (hz0 _ (hker (F l) (by rw [hF]; exact h0)))
  obtain ⟨S, hSdef⟩ : ∃ S : Subalgebra ℚ Ω, S = Algebra.adjoin ℚ (insert (f l)⁻¹ (Set.range u)) := ⟨_, rfl⟩
  obtain ⟨-, z, nn, hnn, -, hsp, hiff⟩ := hl l hf0 S (by rw [hSdef, hu])
  rw [← hu] at hiff

  have hmemS : ∀ G : MvPolynomial (Σ k, J k) ℚ, aeval u G ∈ S := by
    intro G
    rw [hSdef]
    have h1 : aeval u G ∈ Algebra.adjoin ℚ (Set.range u) := by
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨G, rfl⟩
    exact Algebra.adjoin_mono (Set.subset_insert _ _) h1
  have hS' : S = Algebra.adjoin ℚ (insert (aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) (F l) : Ω)⁻¹
      (Set.range fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩)) := by
    rw [← hu, hF, hSdef]
  have hnum := GlobalTheory.T.adjoin_inverse_element_form (Σ k, J k) Ω u (f l) S hSdef (F l) (hF l) hf0
  choose Z kk hZ using fun i => hnum (z i)
  let fS : S := ⟨f l, by rw [← hF l]; exact hmemS _⟩
  have hhom : ∀ (R : Type) [CommRing R] (θ : MvPolynomial (Σ k, J k) ℂ →+* R), (∀ g ∈ CI, θ g = 0) →
      IsUnit (θ (map (algebraMap ℚ ℂ) (F l))) → ∃ ψ : S →+* R, ∀ (G : MvPolynomial (Σ k, J k) ℚ) (s : S),
        (s : Ω) = aeval u G → ψ s = θ (map (algebraMap ℚ ℂ) G) := by
    intro R _ θ h1 h2
    have := GlobalTheory.T.chart_ideal_localization_map K J Ω y c hc R θ (by rw [← hCI]; exact h1) (F l) h2 S hS'
    rwa [← hu] at this
  have hval : ∀ (R : Type) [CommRing R] (θ : MvPolynomial (Σ k, J k) ℂ →+* R) (ψ : S →+* R),
      (∀ (G : MvPolynomial (Σ k, J k) ℚ) (s : S), (s : Ω) = aeval u G → ψ s = θ (map (algebraMap ℚ ℂ) G)) →
      ∀ i, ψ (z i) * θ (map (algebraMap ℚ ℂ) (F l)) ^ kk i = θ (map (algebraMap ℚ ℂ) (Z i)) := by
    intro R _ θ ψ h i
    have h1 : ψ fS = θ (map (algebraMap ℚ ℂ) (F l)) := h _ _ (hF l).symm
    rw [← h1, ← map_pow, ← map_mul]
    exact h _ _ (by simpa [fS] using hZ i)
  haveI : IsLocalRing (locRing I pt) := by subst hI hpt; assumption
  haveI : IsNoetherianRing (locRing I pt) := by subst hI hpt; assumption
  have hev : ∀ g, eval pt (renR (Σ k, J k) g) = eval (ReciprocityTheory.AnForm.R.affCoord c w) g := by
    intro g
    rw [hpt]
    exact ReciprocityTheory.AnForm.R.eval_renC _ g
  let θB : MvPolynomial (Σ k, J k) ℂ →+* locRing I pt :=
    (algebraMap _ (locRing I pt)).comp (renR (Σ k, J k)).toRingHom
  have hθB : ∀ g, θB g = algebraMap _ (locRing I pt) (renR (Σ k, J k) g) := fun _ => rfl
  have hkillB : ∀ g ∈ I, algebraMap _ (locRing I pt) g = 0 := by
    intro g hg
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hg)
  obtain ⟨ψ, hψ⟩ := hhom _ θB (fun g hg => hkillB _ (hrenI g hg)) (by
    rw [hθB]
    exact isUnit_loc _ _ _ (by rw [hev]; exact hl0))
  obtain ⟨π, hπ⟩ := exists_ev I pt hI0
  let φ0 : S →+* ℂ := π.comp ψ
  have hφ0 : ∀ (G : MvPolynomial (Σ k, J k) ℚ) (s : S), (s : Ω) = aeval u G →
      φ0 s = eval (ReciprocityTheory.AnForm.R.affCoord c w) (map (algebraMap ℚ ℂ) G) := by
    intro G s hs
    show π (ψ s) = _
    rw [hψ G s hs, hθB, hπ, hev]
  have hιC : ∀ a : ℂ, algebraMap ℂ (locRing I pt) a = algebraMap (MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ) (locRing I pt) (C a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ) (locRing I pt) a]
    rfl
  have hι : ∀ a : ℂ, π (algebraMap ℂ (locRing I pt) a) = a := by
    intro a
    rw [hιC, hπ, eval_C]
  have hmax : ∀ s, ψ s - algebraMap ℂ (locRing I pt) (φ0 s) ∈ IsLocalRing.maximalIdeal (locRing I pt) := by
    intro s
    by_contra hn
    have hu' : IsUnit (ψ s - algebraMap ℂ (locRing I pt) (φ0 s)) := by
      simpa using hn
    have := hu'.map π
    rw [map_sub, hι] at this
    simp [φ0] at this
  have hKp : I ≤ ptIdeal pt := fun g hg => RingHom.mem_ker.2 (hI0 g hg)
  have hm := ReciprocityTheory.AnForm.R.maximalIdeal_locRing hKp
  let sp : (Σ k, J k) → S := fun p => ⟨u p, by simpa using hmemS (X p)⟩
  have hsp1 : ∀ p, ψ (sp p) = algebraMap (MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ) (locRing I pt) (X (Fintype.equivFin (Σ k, J k) p)) := by
    intro p
    rw [hψ (X p) (sp p) (by simp [sp]), hθB]
    simp
  have hsp2 : ∀ p, φ0 (sp p) = pt (Fintype.equivFin (Σ k, J k) p) := by
    intro p
    rw [hφ0 (X p) (sp p) (by simp [sp]), hpt]
    simp
  have hT : IsLocalRing.maximalIdeal (locRing I pt) =
      Ideal.span ((fun s => ψ s - algebraMap ℂ (locRing I pt) (φ0 s)) '' Set.range sp) := by
    refine hm.trans ((congrArg (fun L => Ideal.map (algebraMap (MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ) (locRing I pt)) L) (ReciprocityTheory.AnForm.R.ptIdeal_eq_span pt)).trans ?_)
    simp only [Ideal.map_span]
    apply congrArg
    ext b
    simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and]
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨(Fintype.equivFin (Σ k, J k)).symm i, ?_⟩
      rw [hsp1, hsp2, hιC]
      simp
    · rintro ⟨p, rfl⟩
      refine ⟨Fintype.equivFin (Σ k, J k) p, ?_⟩
      rw [hsp1, hsp2, hιC]
      simp
  have hgen := GlobalTheory.T.kaehler_differentials_span_local S (locRing I pt) ψ φ0 hmax (Set.range sp) hT n z hsp

  let Fr := renR (Σ k, J k) (map (algebraMap ℚ ℂ) (F l))
  let Zr : Fin n → MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ :=
    fun i => renR (Σ k, J k) (map (algebraMap ℚ ℂ) (Z i))
  let r0 : Fin n → MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ :=
    fun i => Zr i - C (φ0 (z i)) * Fr ^ kk i
  have hvB := hval _ θB ψ hψ
  have hFu : IsUnit (algebraMap (MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ) (locRing I pt) Fr) :=
    isUnit_loc _ _ _ (by show eval pt (renR (Σ k, J k) _) ≠ 0; rw [hev]; exact hl0)
  have hr0B : ∀ i, algebraMap (MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ) (locRing I pt) (r0 i) =
      (ψ (z i) - algebraMap ℂ (locRing I pt) (φ0 (z i))) *
        (algebraMap (MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ) (locRing I pt) Fr) ^ kk i := by
    intro i
    have h1 := hvB i
    rw [hθB, hθB] at h1
    simp only [r0, map_sub, map_mul, map_pow]
    rw [hιC, sub_mul, h1]
  have hspan0 : Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ)
      (locRing I pt) (r0 i)) = IsLocalRing.maximalIdeal (locRing I pt) := by
    rw [hgen]
    exact span_eq_of_unit _ _ (fun i => (algebraMap (MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ)
      (locRing I pt) Fr) ^ kk i) (fun i => hFu.pow _) hr0B
  have hvpt : ∀ i, φ0 (z i) * eval pt Fr ^ kk i = eval pt (Zr i) := by
    intro i
    have h1 := hval ℂ (eval (ReciprocityTheory.AnForm.R.affCoord c w)) φ0 hφ0 i
    simpa only [Fr, Zr, hev] using h1
  have hptF : eval pt Fr ≠ 0 := by
    show eval pt (renR (Σ k, J k) _) ≠ 0
    rw [hev]
    exact hl0
  let Gd : Finset (Fin n) := Finset.univ.filter fun i => (i : ℕ) < nn ∧ φ0 (z i) = 0
  let Bad : Finset (Fin n) := Finset.univ.filter fun i => (i : ℕ) < nn ∧ φ0 (z i) ≠ 0
  obtain ⟨τ, hτ⟩ := exists_perm n Gd.card Gd rfl
  refine ⟨Gd.card, fun i => r0 (τ i), Fr * ∏ i ∈ Bad, Zr i, by simpa using Gd.card_le_univ, ?_, ?_, ?_, ?_⟩
  · rw [← hm, ← hspan0]
    apply congrArg
    exact τ.surjective.range_comp (fun i => algebraMap (MvPolynomial (Fin (Fintype.card (Σ k, J k))) ℂ)
      (locRing I pt) (r0 i))
  · intro i
    simp only [r0, map_sub, map_mul, map_pow, eval_C]
    rw [hvpt, sub_self]
  · rw [map_mul, map_prod]
    refine mul_ne_zero hptF (Finset.prod_ne_zero_iff.2 fun i hi => ?_)
    rw [← hvpt]
    have hi' : (i : ℕ) < nn ∧ φ0 (z i) ≠ 0 := by simpa [Bad] using hi
    exact mul_ne_zero hi'.2 (pow_ne_zero _ hptF)
  · intro v hv hvh
    rw [map_mul, map_prod] at hvh
    have hvF : eval v Fr ≠ 0 := left_ne_zero_of_mul hvh
    have hvZ : ∀ i ∈ Bad, eval v (Zr i) ≠ 0 := fun i hi =>
      Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hvh) i hi
    obtain ⟨v', hv'⟩ : ∃ v' : (Σ k, J k) → ℂ, v' = fun q => v (Fintype.equivFin (Σ k, J k) q) := ⟨_, rfl⟩
    rw [← hv']
    have hvv : renPt v' = v := by
      funext j
      simp [hv', renPt]
    have hev' : ∀ g, eval v (renR (Σ k, J k) g) = eval v' g := fun g => by
      have := ReciprocityTheory.AnForm.R.eval_renC v' g
      rw [hvv] at this
      exact this
    have hzc : ∀ g ∈ CI, eval v' g = 0 := fun g hg => by
      rw [← hev']
      exact hv _ (hrenI g hg)
    have hcone := ReciprocityTheory.AnForm.R.conePts_of_chartIdeal hPh c v' (by rw [← hCI]; exact hzc)
    have hvP : v' ∈ mcPts (mCoordIdeal y) := (mem_mcPts_iff_conePts_pC _ _).2 hcone.1
    obtain ⟨φ, hφ⟩ := hhom ℂ (eval v') hzc (isUnit_iff_ne_zero.2 (by rw [← hev']; exact hvF))
    have hvφ : ∀ i, φ (z i) * eval v Fr ^ kk i = eval v (Zr i) := by
      intro i
      have h1 := hval ℂ (eval v') φ hφ i
      simpa only [Fr, Zr, hev'] using h1
    have hq := hiff (RingHom.ker φ) (RingHom.ker_isPrime φ)
    have haev : ∀ g : MRing J, aeval u g = aeval u (map (algebraMap ℤ ℚ) g) := fun g =>
      (MvPolynomial.aeval_map_algebraMap ℚ u g).symm
    have hgbd : ∀ (g : MRing J) (s : S), (s : Ω) = aeval u g →
        φ s = eval v' (map (Int.castRingHom ℂ) g) := by
      intro g s hs
      rw [hφ (map (algebraMap ℤ ℚ) g) s (hs.trans (haev g)), map_map]
      congr 2
    have hL : (∀ g ∈ bd, ∀ s : S, (s : Ω) = aeval u g → s ∈ RingHom.ker φ) ↔ v' ∈ mcPts bd := by
      constructor
      · intro H
        refine ⟨hvP.1, fun g hg => ?_⟩
        have hs : aeval u g ∈ S := by
          rw [haev]
          exact hmemS _
        rw [← hgbd g ⟨_, hs⟩ rfl]
        exact H g hg _ rfl
      · rintro ⟨-, H⟩ g hg s hs
        exact RingHom.mem_ker.2 ((hgbd g s hs).trans (H g hg))
    constructor
    · rintro ⟨-, hb⟩
      obtain ⟨i, hi, hzi⟩ := hq.1 (hL.2 hb)
      have hφz : φ (z i) = 0 := hzi
      have hZ0 : eval v (Zr i) = 0 := by
        rw [← hvφ, hφz, zero_mul]
      have hg0 : φ0 (z i) = 0 := by
        by_contra hne
        exact hvZ i (by simp [Bad, hi, hne]) hZ0
      refine ⟨τ.symm i, (hτ _).2 (by simpa [Gd] using ⟨hi, hg0⟩), ?_⟩
      show eval v (r0 (τ (τ.symm i))) = 0
      rw [τ.apply_symm_apply]
      simp only [r0, map_sub, map_mul, map_pow, eval_C, hZ0, hg0, zero_mul, sub_zero]
    · rintro ⟨j, hj, hj0⟩
      have hG := (hτ j).1 hj
      obtain ⟨hi, hg0⟩ : ((τ j : Fin n) : ℕ) < nn ∧ φ0 (z (τ j)) = 0 := by simpa [Gd] using hG
      have h1 : eval v (Zr (τ j)) = 0 := by
        have h2 : eval v (r0 (τ j)) = 0 := hj0
        simpa only [r0, map_sub, map_mul, map_pow, eval_C, hg0, zero_mul, sub_zero] using h2
      have h2 : φ (z (τ j)) = 0 := by
        have h3 := hvφ (τ j)
        rw [h1] at h3
        exact (mul_eq_zero.1 h3).resolve_right (pow_ne_zero _ hvF)
      exact ⟨hvP, hL.1 (hq.2 ⟨τ j, hi, h2⟩)⟩

end GlobalTheory.CompanionTheory.Ar.SncCpt

namespace GlobalTheory.CompanionTheory.Ar.SncCpt

theorem reg_at : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (n + 1) → Cmp.IsSncModel y n bd →
    ∀ (c : (k : K) → J k) (w : (Σ k, J k) → ℂ), w ∈ mcPts (mCoordIdeal y) → (∀ k, w ⟨k, c k⟩ ≠ 0) →
    IsRegularLocalRing (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC (mCoordIdeal y)) c)
        (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))) ∧
    ringKrullDim (ReciprocityTheory.AnForm.R.locRing (Cmp.SncRes.ideal (pC (mCoordIdeal y)) c)
      (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w))) = n := by
  intro K _ J _ Ω _ _ y n bd hA hS c w hw hwc
  have hPh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) := isMultiHomogIdeal_pC hA.2.1.2.1
  have hwc' : w ∈ ReciprocityTheory.AnForm.R.conePts (pC (mCoordIdeal y)) := (mem_mcPts_iff_conePts_pC _ _).1 hw
  let x : Cmp.SncRes.Pts (pC (mCoordIdeal y)) := ⟨Cmp.SncRes.proj w, w, hwc', rfl⟩
  have hso : ReciprocityTheory.AnForm.R.SameOrbit (Cmp.SncRes.rep x) w :=
    Cmp.SncRes.sameOrbit_of_proj_eq (Cmp.SncRes.rep_mem x).1 hwc'.1 (Cmp.SncRes.proj_rep x)
  have hco : Cmp.SncRes.coord (pC (mCoordIdeal y)) c x = ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w) := by
    unfold Cmp.SncRes.coord
    rw [ReciprocityTheory.AnForm.R.affCoord_eq_of_sameOrbit c hso]
  have hx : x ∈ Cmp.SncRes.src (pC (mCoordIdeal y)) c := by
    intro k
    obtain ⟨d, hd, he⟩ := hso
    rw [show Cmp.SncRes.rep x ⟨k, c k⟩ = d k * w ⟨k, c k⟩ from congrFun he _]
    exact mul_ne_zero (hd k) (hwc k)
  have := GlobalTheory.T.snc_resolution_regular_local_ring K J Ω y n bd hA hS c x hx
  rwa [hco] at this

theorem exists_sncCharts : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)), Cmp.IsSncModel y n bd → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (n + 1) → (∀ z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → torusSmul c z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd) → ∃ (nc : ℕ) (χ : Fin nc → SncChart (mCoordIdeal y) n (mcPts (mCoordIdeal y) ∩ mcPts bd)), ∀ z ∈ mcPts (mCoordIdeal y), ∃ a, ∃ t : Fin n → ℂ, ‖t‖ ≤ 1 / 2 ∧ ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c ((χ a).γ t) := by
  intro K _ J _ Ω _ _ y n bd hS hA _
  have hPh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) := isMultiHomogIdeal_pC hA.2.1.2.1
  have key : ∀ w : mcPts (mCoordIdeal y), ∃ (χ : SncChart (mCoordIdeal y) n (mcPts (mCoordIdeal y) ∩ mcPts bd))
      (O : Set ((Σ k, J k) → ℂ)), IsOpen O ∧ (w : (Σ k, J k) → ℂ) ∈ O ∧
      ∀ z ∈ O ∩ mcPts (mCoordIdeal y), ∃ t : Fin n → ℂ, ‖t‖ ≤ 1 / 2 ∧ ∃ c' : K → ℂ, (∀ k, c' k ≠ 0) ∧
        z = torusSmul c' (χ.γ t) := by
    rintro ⟨w, hw⟩
    obtain ⟨c, hc, -⟩ := ReciprocityTheory.AnForm.R.exists_chart w hw.1
    obtain ⟨hreg, hdim⟩ := reg_at K J Ω y n bd hA hS c w hw hc
    have hzero : ∀ g ∈ Cmp.SncRes.ideal (pC (mCoordIdeal y)) c,
        eval (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord c w)) g = 0 := by
      refine ReciprocityTheory.AnForm.R.renPt_zero _ _ ?_
      exact (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hPh c w hc).1 ((mem_mcPts_iff_conePts_pC _ _).1 hw)
    obtain ⟨hl, hn⟩ := ReciprocityTheory.AnForm.R.locRing_isLocalRing_isNoetherian _ _ hzero
    obtain ⟨a, r, h, ha, hr, hr0, hh, hb⟩ := snc_params K J Ω y n bd hPh hS c w hw hc
    exact GlobalTheory.T.regular_local_chart_coords K J _ hPh n _ c w hw hc a r h hdim ha hr hr0 hh hb
  choose χ O hO hwO hcov using key
  obtain ⟨m, e, he⟩ := GlobalTheory.T.finite_torus_translates_cover K J _ hPh _ O hO (fun z hz => ⟨⟨z, hz⟩, hwO ⟨z, hz⟩⟩)
  refine ⟨m, fun a => χ (e a), fun z hz => ?_⟩
  obtain ⟨a, c, hc, h1, h2⟩ := he z hz
  obtain ⟨t, ht, c', hc', h3⟩ := hcov (e a) _ ⟨h1, h2⟩
  refine ⟨a, t, ht, fun k => (c k)⁻¹ * c' k, fun k => mul_ne_zero (inv_ne_zero (hc k)) (hc' k), ?_⟩
  funext q
  have := congrFun h3 q
  simp only [torusSmul] at this ⊢
  rw [mul_assoc, ← this, ← mul_assoc, inv_mul_cancel₀ (hc q.1), one_mul]

end GlobalTheory.CompanionTheory.Ar.SncCpt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTorusStableSncChartsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torus_stable_snc_charts : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)), Cmp.IsSncModel y n bd → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (n + 1) → (∀ z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → torusSmul c z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd) → ∃ (nc : ℕ) (χ : Fin nc → SncChart (mCoordIdeal y) n (mcPts (mCoordIdeal y) ∩ mcPts bd)), ∀ z ∈ mcPts (mCoordIdeal y), ∃ a, ∃ t : Fin n → ℂ, ‖t‖ ≤ 1 / 2 ∧ ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c ((χ a).γ t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncCpt.exists_sncCharts | exact GlobalTheory.CompanionTheory.Ar.SncCpt.exists_sncCharts | (intros; apply GlobalTheory.CompanionTheory.Ar.SncCpt.exists_sncCharts <;> assumption)
end
