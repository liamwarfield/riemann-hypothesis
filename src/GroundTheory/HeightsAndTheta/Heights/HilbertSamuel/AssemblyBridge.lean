module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsExtra
section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ContinuousMinorRatioLift
section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ProjectionPullbackZeroSetNull
section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.HasStrictFDerivAtEquiv
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
  Topology Filter Set

namespace pullbackPushforward_holds

section Orbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem sameOrbit_comm {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  simp [← mul_assoc, inv_mul_cancel₀ (hc p.1)]

theorem sameOrbit_tr {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (h' : SameOrbit z' z'') :
    SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨d, hd, rfl⟩ := h'
  exact ⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), by funext p; simp [mul_assoc]⟩

theorem segre_of_sameOrbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    ∃ μ : ℂ, μ ≠ 0 ∧ segre z = μ • segre z' := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨∏ k, c k, Finset.prod_ne_zero_iff.mpr fun k _ => hc k, segre_smul c z'⟩

variable {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem sameOrbit_comp {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {z z' : (Σ k', ι' k') → ℂ} (h : SameOrbit z z') :
    SameOrbit (fun p => z (v p)) (fun p => z' (v p)) := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => c (κ k), fun k => hc _, ?_⟩
  funext p
  show c (v p).1 * z' (v p) = c (κ p.1) * z' (v p)
  rw [hv.2.2.1 p]

end Orbit

theorem hasStrictFDerivAt_equiv {n : ℕ} {Q : (Fin n → ℂ) → (Fin n → ℂ)} {u : Fin n → ℂ}
    (hQ : AnalyticAt ℂ Q u)
    (hd : LinearMap.det (fderiv ℂ Q u : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0) :
    ∃ e : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ), HasStrictFDerivAt Q (e : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) u := by
  refine ⟨(LinearMap.equivOfDetNeZero _ hd).toContinuousLinearEquiv, ?_⟩
  have h : ((LinearMap.equivOfDetNeZero _ hd).toContinuousLinearEquiv :
      (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) = fderiv ℂ Q u := by
    ext1 w
    rfl
  rw [h]
  exact hQ.hasStrictFDerivAt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {P' J' : Ideal (MRing ι')} {n : ℕ} (R : AnLogRes P' J' n) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}

theorem pullPt_sameOrbit (hv : IsBlockMap κ v) {x z : R.X} (hz : z ∈ R.U x) :
    SameOrbit (pullPt R v z) (fun p => R.lift x z (v p)) :=
  sameOrbit_comp hv (R.compat z x z ⟨R.mem_U z, hz⟩)

theorem pullQ_eq_local (hv : IsBlockMap κ v) (Φ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    {x z : R.X} (hz : z ∈ R.U x) :
    pullQ R v Φ z = fun i => Φ (segre (fun p => R.lift x z (v p))) i.succ /
      Φ (segre (fun p => R.lift x z (v p))) 0 := by
  obtain ⟨μ, hμ, hseg⟩ := segre_of_sameOrbit (pullPt_sameOrbit R hv hz)
  funext i
  simp only [pullQ, hseg, map_smul, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hμ

theorem analyticAt_segre_pull (Φ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (x : R.X)
    (j : Fin R.A.n) {u : Fin n → ℂ} (hu : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) :
    AnalyticAt ℂ (fun w => Φ (segre (fun p => R.lift x ((R.A.chart j).symm w) (v p)))) u := by
  classical
  have hl := analyticAt_lift_chart R x j hu
  have hs : AnalyticAt ℂ (fun w => segre (fun p => R.lift x ((R.A.chart j).symm w) (v p))) u := by
    refine analyticAt_pi_iff.mpr fun i => ?_
    simp only [segre]
    exact Finset.analyticAt_fun_prod _ fun k _ => analyticAt_pi_iff.mp hl _
  exact (LinearMap.toContinuousLinearMap Φ).analyticAt _ |>.comp hs

theorem analyticAt_pullQ (hv : IsBlockMap κ v) (Φ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (x : R.X) (j : Fin R.A.n) (hj : x ∈ (R.A.chart j).source)
    (h0 : Φ (segre (pullPt R v x)) 0 ≠ 0) :
    AnalyticAt ℂ (pullQ R v Φ ∘ (R.A.chart j).symm) (R.A.chart j x) := by
  set u := R.A.chart j x
  have hsu : (R.A.chart j).symm u = x := (R.A.chart j).left_inv hj
  have hu : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact R.mem_U x⟩
  have hH := analyticAt_segre_pull R (v := v) Φ x j hu
  have hH0 : AnalyticAt ℂ (fun w => Φ (segre (fun p => R.lift x ((R.A.chart j).symm w) (v p))) 0) u :=
    analyticAt_pi_iff.mp hH 0
  have hne : Φ (segre (fun p => R.lift x ((R.A.chart j).symm u) (v p))) 0 ≠ 0 := by
    rw [hsu]; exact h0
  have hF : AnalyticAt ℂ (fun w => fun i : Fin n =>
      Φ (segre (fun p => R.lift x ((R.A.chart j).symm w) (v p))) i.succ /
        Φ (segre (fun p => R.lift x ((R.A.chart j).symm w) (v p))) 0) u :=
    analyticAt_pi_iff.mpr fun i => (analyticAt_pi_iff.mp hH i.succ).div hH0 hne
  refine hF.congr ?_
  filter_upwards [((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds hu] with w hw
  exact (pullQ_eq_local R hv Φ hw.2).symm

theorem det_pullQ_chart (hv : IsBlockMap κ v) (Φ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    {x : R.X} {j k : Fin R.A.n} (hj : x ∈ (R.A.chart j).source) (hk : x ∈ (R.A.chart k).source)
    (h0 : Φ (segre (pullPt R v x)) 0 ≠ 0) :
    LinearMap.det (fderiv ℂ (pullQ R v Φ ∘ (R.A.chart j).symm) (R.A.chart j x) :
        (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) =
      LinearMap.det (fderiv ℂ (pullQ R v Φ ∘ (R.A.chart k).symm) (R.A.chart k x) :
        (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) *
      LinearMap.det (fderiv ℂ (R.A.chart k ∘ (R.A.chart j).symm) (R.A.chart j x) :
        (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) := by
  set u := R.A.chart j x
  have hsu : (R.A.chart j).symm u = x := (R.A.chart j).left_inv hj
  set T := R.A.chart k ∘ (R.A.chart j).symm with hTdef
  have huk : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' (R.A.chart k).source :=
    ⟨(R.A.chart j).map_source hj, by rw [mem_preimage, hsu]; exact hk⟩
  have hT : AnalyticAt ℂ T u := R.A.holo j k u huk
  have hTu : T u = R.A.chart k x := by simp only [hTdef, Function.comp_apply, hsu]
  have hQk := analyticAt_pullQ R hv Φ x k hk h0
  have heq : pullQ R v Φ ∘ (R.A.chart j).symm =ᶠ[𝓝 u] (pullQ R v Φ ∘ (R.A.chart k).symm) ∘ T := by
    filter_upwards [((R.A.chart j).isOpen_inter_preimage_symm (R.A.chart k).open_source).mem_nhds
      huk] with w hw
    simp only [hTdef, Function.comp_apply, (R.A.chart k).left_inv hw.2]
  rw [heq.fderiv_eq, fderiv_comp u (by rw [hTu]; exact hQk.differentiableAt) hT.differentiableAt,
    hTu]
  exact LinearMap.det_comp _ _

theorem eval_lift_eq_zero_iff {f : MRing ι'} {a : K' → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) {x z : R.X}
    (hz : z ∈ R.U x) :
    eval (R.lift z z) (map (Int.castRingHom ℂ) f) = 0 ↔
      eval (R.lift x z) (map (Int.castRingHom ℂ) f) = 0 := by
  obtain ⟨c, hc, hzc⟩ := R.compat z x z ⟨R.mem_U z, hz⟩
  rw [hzc, eval_smul_homog f a hf c]
  have : ∏ k, c k ^ a k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  simp [this]

theorem isOpen_chart_ne {f : MRing ι'} {a : K' → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) (j : Fin R.A.n) :
    IsOpen ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | eval (R.lift x x) (map (Int.castRingHom ℂ) f) ≠ 0}) := by
  rw [isOpen_iff_mem_nhds]
  rintro u1 ⟨hu1, h1⟩
  set x1 := (R.A.chart j).symm u1
  have hV : (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x1 ∈ 𝓝 u1 :=
    ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x1)).mem_nhds ⟨hu1, R.mem_U x1⟩
  have hcont : ContinuousAt (fun u => eval (R.lift x1 ((R.A.chart j).symm u))
      (map (Int.castRingHom ℂ) f)) u1 :=
    (MvPolynomial.continuous_eval _).continuousAt.comp
      (analyticAt_lift_chart R x1 j ⟨hu1, R.mem_U x1⟩).continuousAt
  have hne : eval (R.lift x1 ((R.A.chart j).symm u1)) (map (Int.castRingHom ℂ) f) ≠ 0 := h1
  filter_upwards [hV, hcont.eventually_ne hne] with u hu hne'
  exact ⟨hu.1, fun h => hne' ((eval_lift_eq_zero_iff R hf hu.2).mp h)⟩

theorem fzero_null (hP' : IsArithVar P' (n + 1)) {f : MRing ι'} {a : K' → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a)
    (hfP : f ∉ P') (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | eval (R.lift x x) (map (Int.castRingHom ℂ) f) = 0}) = 0 := by
  classical
  obtain ⟨Ψ', hΨ'⟩ := goodProjExists K' ι' P' n hP'
  have hJf : IsMultiHomogIdeal (Ideal.span {f}) :=
    ⟨{f}, fun g hg => ⟨a, by rw [Set.mem_singleton_iff.mp hg]; exact hf⟩, rfl⟩
  have hJP : ¬ Ideal.span {f} ≤ P' := fun h => hfP (h (Ideal.subset_span rfl))
  have hnull := projB_null Ψ' hP' hΨ' hJf hJP
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, -⟩
  set x0 := (R.A.chart j).symm u0
  set V := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0 with hVdef
  have hV : IsOpen V := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV u0 ⟨hu0, R.mem_U x0⟩
  set g : (Fin n → ℂ) → ℂ := fun u => eval (R.lift x0 ((R.A.chart j).symm u))
    (map (Int.castRingHom ℂ) f) with hgdef
  have hga : AnalyticOnNhd ℂ g V := fun u hu =>
    analyticAt_eval_poly _ fun p => analyticAt_pi_iff.mp (analyticAt_lift_chart R x0 j hu) p
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, g, hga.mono hball, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    set N := ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | Ψ' (segre (R.lift x x)) 0 = 0}) ∪
      ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | Ψ' (segre (R.lift x x)) 0 ≠ 0 ∧
        ∃ k, x ∈ (R.A.chart k).source ∧
          LinearMap.det (fderiv ℂ (brQ R Ψ' ∘ (R.A.chart k).symm) (R.A.chart k x) :
            (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0}) with hNdef
    have hN : volume N = 0 :=
      measure_union_null (psi0_null R Ψ' hP' hΨ' j) (ram_null R Ψ' hP' hΨ' j)
    obtain ⟨u1, hu1B, hu1N⟩ : ∃ u1 ∈ Metric.ball u0 r, u1 ∉ N := by
      by_contra h
      push Not at h
      exact (Metric.measure_ball_pos volume u0 hr).ne' (measure_mono_null h hN)
    have hu1t : u1 ∈ (R.A.chart j).target := (hball hu1B).1
    set x1 := (R.A.chart j).symm u1
    have hx1 : x1 ∈ (R.A.chart j).source := (R.A.chart j).map_target hu1t
    have hcx1 : R.A.chart j x1 = u1 := (R.A.chart j).right_inv hu1t
    have h01 : Ψ' (segre (R.lift x1 x1)) 0 ≠ 0 := fun h => hu1N (Or.inl ⟨hu1t, h⟩)
    have hdet1 : LinearMap.det (fderiv ℂ (brQ R Ψ' ∘ (R.A.chart j).symm) u1 :
        (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0 := by
      intro h
      exact hu1N (Or.inr ⟨hu1t, h01, j, hx1, by rw [hcx1]; exact h⟩)
    have hQa : AnalyticAt ℂ (brQ R Ψ' ∘ (R.A.chart j).symm) u1 := by
      have := analyticAt_brQ R Ψ' x1 j hx1 h01
      rwa [hcx1] at this
    obtain ⟨e, he⟩ := hasStrictFDerivAt_equiv hQa hdet1
    have hcont0 : ContinuousOn (fun u => Ψ' (segre (R.lift x0 ((R.A.chart j).symm u))) 0) V :=
      fun u hu => (analyticAt_pi_iff.mp (analyticAt_segre_lift R Ψ' x0 j hu) 0).continuousAt.continuousWithinAt
    set O := Metric.ball u0 r ∩
      (fun u => Ψ' (segre (R.lift x0 ((R.A.chart j).symm u))) 0) ⁻¹' {0}ᶜ with hOdef
    have hO : IsOpen O :=
      (hcont0.mono hball).isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton
    have hu1O : u1 ∈ O := by
      refine ⟨hu1B, ?_⟩
      obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq R (hball hu1B).2 Ψ'
      show Ψ' (segre (R.lift x0 x1)) 0 ≠ 0
      intro h
      apply h01
      rw [hμeq, Pi.smul_apply, smul_eq_mul, h, mul_zero]
    have himg : (brQ R Ψ' ∘ (R.A.chart j).symm) '' O ∈
        𝓝 ((brQ R Ψ' ∘ (R.A.chart j).symm) u1) := by
      rw [← he.map_nhds_eq_of_equiv]
      exact Filter.image_mem_map (hO.mem_nhds hu1O)
    refine (Measure.measure_pos_of_mem_nhds (μ := volume) himg).ne' (measure_mono_null ?_ hnull)
    rintro _ ⟨u, huO, rfl⟩
    set x := (R.A.chart j).symm u
    have hxU : x ∈ R.U x0 := (hball huO.1).2
    obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq R hxU Ψ'
    have h0x : Ψ' (segre (R.lift x x)) 0 ≠ 0 := by
      rw [hμeq, Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero hμ huO.2
    obtain ⟨z2, hz2, hsz2, hΨz2⟩ := brW_mem_fibre R Ψ' hP'.1 hP'.2.1.2.1 h0x
    refine ⟨z2, hz2, ?_, ?_⟩
    · have hso : SameOrbit z2 (R.lift x x) :=
        sameOrbit_of_segre (R.mem x x (R.mem_U x)).1 _ (inv_ne_zero h0x) (by rw [hsz2]; rfl)
      refine mem_mcPts_of_sameOrbit hJf hso ⟨(R.mem x x (R.mem_U x)).1, fun g' hg' => ?_⟩
      obtain ⟨r', rfl⟩ := Ideal.mem_span_singleton'.mp hg'
      rw [map_mul, eval_mul, (eval_lift_eq_zero_iff R hf hxU).mpr (hall u huO.1), mul_zero]
    · rw [hsz2, hΨz2]
      rfl
  · rintro w ⟨⟨-, hw0⟩, hwb⟩
    exact (eval_lift_eq_zero_iff R hf (hball hwb).2).mp hw0

end pullbackPushforward_holds

end GroundTheory.Heights₂.Heights.Inter
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
  Topology Filter Set

namespace pullbackPushforward_holds

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {P' J' : Ideal (MRing ι')} {n : ℕ} (R : AnLogRes P' J' n) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}

theorem orbit_subsingleton (t : (Σ k', ι' k') → ℂ) :
    {x : R.X | R.lift x x ∉ mcPts J' ∧ SameOrbit (R.lift x x) t}.Subsingleton := by
  rintro x ⟨hx, hxt⟩ x' ⟨-, hx't⟩
  exact R.inj x x' hx (sameOrbit_tr hxt (sameOrbit_comm hx't))

theorem not_flat_pull (hGen : BlockGenFinite.Statement) (hv : IsBlockMap κ v)
    (hP' : IsArithVar P' (n + 1)) (hP : IsArithVar (imageZ v P') (n + 1))
    (Φ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (hΦ : IsGoodProj (imageZ v P') Φ)
    (j : Fin R.A.n) {O : Set (Fin n → ℂ)} (hO : IsOpen O) (hOt : O ⊆ (R.A.chart j).target)
    (hne : O.Nonempty) (h0 : ∀ u ∈ O, Φ (segre (pullPt R v ((R.A.chart j).symm u))) 0 ≠ 0)
    (han : AnalyticOnNhd ℂ (pullQ R v Φ ∘ (R.A.chart j).symm) O)
    (hdet : ∀ u ∈ O, LinearMap.det (fderiv ℂ (pullQ R v Φ ∘ (R.A.chart j).symm) u :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0) : False := by
  classical
  obtain ⟨f, a, hf, hfP, hfin⟩ := hGen K ι K' ι' κ v P' n hv hP' hP
  set O' := O ∩ ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | R.lift x x ∉ mcPts J'}) ∩
    ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | eval (R.lift x x) (map (Int.castRingHom ℂ) f) ≠ 0}) with hO'def
  have hO' : IsOpen O' := (hO.inter (isOpen_chart_notB R j)).inter (isOpen_chart_ne R hf j)
  have hne' : O'.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hsub : O ⊆ ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | R.lift x x ∈ mcPts J'}) ∪
        ((R.A.chart j).target ∩
          (R.A.chart j).symm ⁻¹' {x | eval (R.lift x x) (map (Int.castRingHom ℂ) f) = 0}) := by
      intro u hu
      by_cases hB : R.lift ((R.A.chart j).symm u) ((R.A.chart j).symm u) ∈ mcPts J'
      · exact Or.inl ⟨hOt hu, hB⟩
      by_cases hF : eval (R.lift ((R.A.chart j).symm u) ((R.A.chart j).symm u))
          (map (Int.castRingHom ℂ) f) = 0
      · exact Or.inr ⟨hOt hu, hF⟩
      have : u ∈ O' := ⟨⟨hu, hOt hu, hB⟩, hOt hu, hF⟩
      rw [h] at this
      exact absurd this (Set.notMem_empty u)
    exact (hO.measure_pos volume hne).ne'
      (measure_mono_null hsub (measure_union_null (R.null j) (fzero_null R hP' hf hfP j)))
  obtain ⟨y, hy⟩ := exists_infinite_fibre hO' hne' (han.mono fun u hu => hu.1.1)
    (fun u hu => hdet u hu.1.1)
  have hSinf : ((R.A.chart j).symm '' (O' ∩ (pullQ R v Φ ∘ (R.A.chart j).symm) ⁻¹' {y})).Infinite :=
    Set.Infinite.image ((R.A.chart j).symm.injOn.mono fun u hu => hu.1.1.2.1) hy
  have hF := fibreFinite K ι (imageZ v P') n Φ hP hΦ y
  choose! uw huw using fun w (hw : w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre (imageZ v P') Φ y) => hw
  choose T hT using fun w => hfin (uw w)
  refine hSinf ((hF.biUnion fun w _ => (T w).finite_toSet.biUnion fun t _ =>
    (orbit_subsingleton R t).finite).subset ?_)
  rintro _ ⟨u, ⟨huO', hqu⟩, rfl⟩
  set x := (R.A.chart j).symm u
  have hxB : R.lift x x ∉ mcPts J' := huO'.1.2.2
  have hxf : eval (R.lift x x) (map (Int.castRingHom ℂ) f) ≠ 0 := huO'.2.2
  have h0x : Φ (segre (pullPt R v x)) 0 ≠ 0 := h0 u huO'.1.1
  have hqx : pullQ R v Φ x = y := hqu
  have hw := IntersectionWithSection.pullW_mem_fibre hv hP R Φ h0x
  rw [hqx] at hw
  obtain ⟨hu1, hu2, -⟩ := huw _ hw
  have hso : SameOrbit (pullPt R v x) (uw (pullW R v Φ x)) :=
    sameOrbit_of_segre hu1.1 (Φ (segre (pullPt R v x)) 0) h0x
      (by rw [hu2]; simp [pullW, smul_smul, mul_inv_cancel₀ h0x])
  obtain ⟨t, ht, hxt⟩ := hT (pullW R v Φ x) (R.lift x x) (R.mem x x (R.mem_U x)) hxf hso
  exact Set.mem_biUnion hw (Set.mem_biUnion (Finset.mem_coe.mpr ht) ⟨hxB, hxt⟩)

theorem projection_pullback_zeroSet_null (hGen : BlockGenFinite.Statement) (hv : IsBlockMap κ v)
    (hP' : IsArithVar P' (n + 1)) (hP : IsArithVar (imageZ v P') (n + 1))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (hΨ : IsGoodProj (imageZ v P') Ψ)
    (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | Ψ (segre (pullPt R v x)) 0 = 0}) = 0 := by
  classical
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, -⟩
  set x0 := (R.A.chart j).symm u0
  set V := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0 with hVdef
  have hV : IsOpen V := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV u0 ⟨hu0, R.mem_U x0⟩
  set f : (Fin n → ℂ) → ℂ := fun u => Ψ (segre (fun p => R.lift x0 ((R.A.chart j).symm u) (v p))) 0
    with hfdef
  have hfa : AnalyticOnNhd ℂ f V := fun u hu =>
    analyticAt_pi_iff.mp (analyticAt_segre_pull R (v := v) Ψ x0 j hu) 0
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, f, hfa.mono hball, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    have hgood := hΨ _ (IntersectionWithSection.comp_mem_mcPts hv (R.mem x0 x0 (R.mem_U x0)))
    obtain ⟨i0, hi0⟩ : ∃ i0, Ψ (segre (pullPt R v x0)) i0 ≠ 0 := by
      by_contra h
      push Not at h
      exact hgood (funext h)
    have hi0ne : i0 ≠ 0 := by
      rintro rfl
      exact hi0 (hall u0 (Metric.mem_ball_self hr))
    set m : Fin n := i0.pred hi0ne
    have hm : m.succ = i0 := Fin.succ_pred i0 hi0ne
    set Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) :=
      (LinearMap.funLeft ℂ ℂ (Equiv.swap (0 : Fin (n + 1)) i0)).comp Ψ with hΨ'def
    have hΨ'app : ∀ w i, Ψ' w i = Ψ w (Equiv.swap 0 i0 i) := fun w i => rfl
    have hΨ' : IsGoodProj (imageZ v P') Ψ' := by
      intro z hz h
      refine hΨ z hz (funext fun i => ?_)
      have := congrFun h (Equiv.swap 0 i0 i)
      rw [hΨ'app, Equiv.swap_apply_self] at this
      exact this
    have hg'c : ContinuousOn (fun u => Ψ' (segre (fun p => R.lift x0 ((R.A.chart j).symm u) (v p))) 0)
        (Metric.ball u0 r) := fun u hu =>
      (analyticAt_pi_iff.mp (analyticAt_segre_pull R (v := v) Ψ' x0 j (hball hu)) 0).continuousAt.continuousWithinAt
    set O := Metric.ball u0 r ∩
      (fun u => Ψ' (segre (fun p => R.lift x0 ((R.A.chart j).symm u) (v p))) 0) ⁻¹' {0}ᶜ with hOdef
    have hO : IsOpen O := hg'c.isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton
    have hu0O : u0 ∈ O := by
      refine ⟨Metric.mem_ball_self hr, ?_⟩
      show Ψ' (segre (pullPt R v x0)) 0 ≠ 0
      rw [hΨ'app, Equiv.swap_apply_left]
      exact hi0
    have h0O : ∀ u ∈ O, Ψ' (segre (pullPt R v ((R.A.chart j).symm u))) 0 ≠ 0 := by
      intro u hu
      obtain ⟨μ, hμ, hμeq⟩ := segre_of_sameOrbit (pullPt_sameOrbit R hv (hball hu.1).2)
      rw [hμeq, map_smul, Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero hμ hu.2
    have hanO : AnalyticOnNhd ℂ (pullQ R v Ψ' ∘ (R.A.chart j).symm) O := by
      intro u hu
      have := analyticAt_pullQ R hv Ψ' _ j ((R.A.chart j).map_target (hball hu.1).1) (h0O u hu)
      rwa [(R.A.chart j).right_inv (hball hu.1).1] at this
    have hzero : ∀ u ∈ O, (pullQ R v Ψ' ∘ (R.A.chart j).symm) u m = 0 := by
      intro u hu
      simp only [Function.comp_apply, pullQ]
      rw [hm, hΨ'app, Equiv.swap_apply_right]
      obtain ⟨μ, hμ, hμeq⟩ := segre_of_sameOrbit (pullPt_sameOrbit R hv (hball hu.1).2)
      rw [hμeq, map_smul, Pi.smul_apply, smul_eq_mul]
      have : f u = 0 := hall u hu.1
      simp only [hfdef] at this
      rw [this, mul_zero, zero_div]
    have hdetO : ∀ u ∈ O, LinearMap.det (fderiv ℂ (pullQ R v Ψ' ∘ (R.A.chart j).symm) u :
        (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0 := by
      intro u hu
      have hcoord : (fun w => (pullQ R v Ψ' ∘ (R.A.chart j).symm) w m) =ᶠ[𝓝 u] fun _ => 0 := by
        filter_upwards [hO.mem_nhds hu] with w hw
        exact hzero w hw
      have hd : HasFDerivAt (fun w => (pullQ R v Ψ' ∘ (R.A.chart j).symm) w m)
          ((ContinuousLinearMap.proj m).comp (fderiv ℂ (pullQ R v Ψ' ∘ (R.A.chart j).symm) u)) u :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) m).hasFDerivAt.comp u
          (hanO u hu).differentiableAt.hasFDerivAt
      have hd0 : HasFDerivAt (fun w => (pullQ R v Ψ' ∘ (R.A.chart j).symm) w m)
          (0 : (Fin n → ℂ) →L[ℂ] ℂ) u :=
        (hasFDerivAt_const (0 : ℂ) u).congr_of_eventuallyEq hcoord
      have hrow := hd.unique hd0
      refine det_eq_zero_of_coord m fun w => ?_
      have := congrArg (fun T : (Fin n → ℂ) →L[ℂ] ℂ => T w) hrow
      simpa using this
    exact not_flat_pull R hGen hv hP' hP Ψ' hΨ' j hO (fun u hu => (hball hu.1).1) ⟨u0, hu0O⟩ h0O
      hanO hdetO
  · rintro w ⟨⟨-, hw0⟩, hwb⟩
    obtain ⟨μ, hμ, hμeq⟩ := segre_of_sameOrbit (pullPt_sameOrbit R hv (hball hwb).2)
    have h := congrArg (fun s => Ψ s 0) hμeq
    simp only [map_smul, Pi.smul_apply, smul_eq_mul] at h
    have hw0' : Ψ (segre (pullPt R v ((R.A.chart j).symm w))) 0 = 0 := hw0
    rw [hw0'] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hμ

theorem ram_pull_null (hGen : BlockGenFinite.Statement) (hv : IsBlockMap κ v)
    (hP' : IsArithVar P' (n + 1)) (hP : IsArithVar (imageZ v P') (n + 1))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (hΨ : IsGoodProj (imageZ v P') Ψ)
    (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | Ψ (segre (pullPt R v x)) 0 ≠ 0 ∧
      ∃ k, x ∈ (R.A.chart k).source ∧
        LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
          (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0}) = 0 := by
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, h00, -⟩
  set x0 := (R.A.chart j).symm u0
  set V := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0 with hVdef
  have hV : IsOpen V := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
  have hgc : ContinuousOn (fun u => Ψ (segre (fun p => R.lift x0 ((R.A.chart j).symm u) (v p))) 0) V :=
    fun u hu => (analyticAt_pi_iff.mp (analyticAt_segre_pull R (v := v) Ψ x0 j hu) 0).continuousAt.continuousWithinAt
  set O := V ∩ (fun u => Ψ (segre (fun p => R.lift x0 ((R.A.chart j).symm u) (v p))) 0) ⁻¹' {0}ᶜ
    with hOdef
  have hO : IsOpen O := hgc.isOpen_inter_preimage hV isOpen_compl_singleton
  have hu0O : u0 ∈ O := ⟨⟨hu0, R.mem_U x0⟩, h00⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO u0 hu0O
  have h0 : ∀ u ∈ Metric.ball u0 r, Ψ (segre (pullPt R v ((R.A.chart j).symm u))) 0 ≠ 0 := by
    intro u hu
    obtain ⟨μ, hμ, hμeq⟩ := segre_of_sameOrbit (pullPt_sameOrbit R hv (hball hu).1.2)
    rw [hμeq, map_smul, Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hμ (hball hu).2
  have hQa : AnalyticOnNhd ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (Metric.ball u0 r) := by
    intro u hu
    have := analyticAt_pullQ R hv Ψ _ j ((R.A.chart j).map_target (hball hu).1.1) (h0 u hu)
    rwa [(R.A.chart j).right_inv (hball hu).1.1] at this
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, fun u => LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) u :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)), fun u hu => analyticAt_det_fderiv (hQa u hu), ?_, ?_⟩
  · by_contra hall
    push Not at hall
    exact not_flat_pull R hGen hv hP' hP Ψ hΨ j Metric.isOpen_ball (fun u hu => (hball hu).1.1)
      ⟨u0, Metric.mem_ball_self hr⟩ h0 hQa hall
  · rintro w ⟨⟨hwt, hw0, k, hk, hdk⟩, -⟩
    have := det_pullQ_chart R hv Ψ (j := j) ((R.A.chart j).map_target hwt) hk hw0
    rw [(R.A.chart j).right_inv hwt] at this
    show LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) w :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0
    rw [this, hdk, zero_mul]

theorem pullBad_null (hGen : BlockGenFinite.Statement) (hv : IsBlockMap κ v)
    (hP' : IsArithVar P' (n + 1)) (hP : IsArithVar (imageZ v P') (n + 1))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (hΨ : IsGoodProj (imageZ v P') Ψ)
    (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' pullBad R v Ψ) = 0 := by
  have h3 : pullBad R v Ψ ⊆ {x | R.lift x x ∈ mcPts J'} ∪ {x | Ψ (segre (pullPt R v x)) 0 = 0} ∪
      {x | Ψ (segre (pullPt R v x)) 0 ≠ 0 ∧ ∃ k, x ∈ (R.A.chart k).source ∧
        LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
          (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0} := by
    rintro x ((h | h) | ⟨k, hk, hn⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · by_cases h0 : Ψ (segre (pullPt R v x)) 0 = 0
      · exact Or.inl (Or.inr h0)
      · refine Or.inr ⟨h0, k, hk, ?_⟩
        by_contra hd
        exact hn ⟨analyticAt_pullQ R hv Ψ x k hk h0, hd⟩
  refine measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono h3)) ?_
  simp only [Set.preimage_union, Set.inter_union_distrib_left]
  exact measure_union_null (measure_union_null (R.null j) (projection_pullback_zeroSet_null R hGen hv hP' hP Ψ hΨ j))
    (ram_pull_null R hGen hv hP' hP Ψ hΨ j)

end pullbackPushforward_holds

end GroundTheory.Heights₂.Heights.Inter
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
  Topology Filter Set

namespace pullbackPushforward_holds

section Minor

variable {Ω : Type} [Fintype Ω]

def minorRatio (b a : Ω → ℂ) : ℝ :=
  ‖fun il : Ω × Ω => a il.1 * b il.2 - a il.2 * b il.1‖ / ‖a‖

theorem minorRatio_nonneg (b a : Ω → ℂ) : 0 ≤ minorRatio b a :=
  div_nonneg (norm_nonneg _) (norm_nonneg _)

theorem minorRatio_smul (b a : Ω → ℂ) {μ : ℂ} (hμ : μ ≠ 0) : minorRatio b (μ • a) = minorRatio b a := by
  unfold minorRatio
  have h : (fun il : Ω × Ω => (μ • a) il.1 * b il.2 - (μ • a) il.2 * b il.1) =
      μ • fun il : Ω × Ω => a il.1 * b il.2 - a il.2 * b il.1 := by
    funext il
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, norm_smul, norm_smul]
  exact mul_div_mul_left _ _ (norm_ne_zero_iff.mpr hμ)

theorem minorRatio_self (b : Ω → ℂ) : minorRatio b b = 0 := by
  unfold minorRatio
  have h : (fun il : Ω × Ω => b il.1 * b il.2 - b il.2 * b il.1) = 0 := by
    funext il
    simp only [Pi.zero_apply]
    ring
  rw [h, norm_zero, zero_div]

theorem continuousAt_minorRatio (b : Ω → ℂ) {a : Ω → ℂ} (ha : a ≠ 0) :
    ContinuousAt (minorRatio b) a := by
  unfold minorRatio
  refine ContinuousAt.div ?_ continuous_norm.continuousAt (norm_ne_zero_iff.mpr ha)
  refine (continuous_norm.comp (continuous_pi fun il => ?_)).continuousAt
  exact ((continuous_apply il.1).mul continuous_const).sub ((continuous_apply il.2).mul continuous_const)

theorem eq_smul_of_minorRatio {b a : Ω → ℂ} (hb : b ≠ 0) (ha : a ≠ 0) (h : minorRatio b a = 0) :
    ∃ μ : ℂ, μ ≠ 0 ∧ a = μ • b := by
  unfold minorRatio at h
  rw [div_eq_zero_iff, or_iff_left (norm_ne_zero_iff.mpr ha), norm_eq_zero] at h
  have hm : ∀ i l, a i * b l = a l * b i := fun i l => by
    have := congrFun h (i, l)
    simp only [Pi.zero_apply] at this
    exact sub_eq_zero.mp this
  obtain ⟨l0, hl0⟩ : ∃ l0, b l0 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hb (funext hc)
  have heq : a = (a l0 / b l0) • b := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hl0]
    exact hm i l0
  refine ⟨a l0 / b l0, fun h0 => ha ?_, heq⟩
  rw [heq, h0, zero_smul]

end Minor

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem continuous_segre : Continuous (segre : ((Σ k, ι k) → ℂ) → ((k : K) → ι k) → ℂ) :=
  continuous_pi fun _ => continuous_finsetProd _ fun _ _ => continuous_apply _

theorem segre_ne_zero {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : segre z ≠ 0 := by
  choose p hp using hz
  intro h
  have := congrFun h p
  simp only [segre, Pi.zero_apply] at this
  exact (Finset.prod_ne_zero_iff.mpr fun k _ => hp k) this

variable {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {P' J' : Ideal (MRing ι')} {n : ℕ} (R : AnLogRes P' J' n) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}

theorem continuousAt_lift (x : R.X) : ContinuousAt (fun x' => R.lift x x') x := by
  obtain ⟨j, hj⟩ := R.A.cover x
  have hu : R.A.chart j x ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, (R.A.chart j).left_inv hj]; exact R.mem_U x⟩
  have h1 : ContinuousAt (fun x' => R.lift x ((R.A.chart j).symm (R.A.chart j x'))) x :=
    ContinuousAt.comp (f := R.A.chart j) (g := fun w => R.lift x ((R.A.chart j).symm w))
      (analyticAt_lift_chart R x j hu).continuousAt ((R.A.chart j).continuousAt hj)
  refine h1.congr ?_
  filter_upwards [(R.A.chart j).open_source.mem_nhds hj] with x' hx'
  rw [(R.A.chart j).left_inv hx']

theorem continuous_minorRatio_lift [DecidableEq K'] (b : ((k : K') → ι' k) → ℂ) :
    Continuous (fun x' : R.X => minorRatio b (segre (R.lift x' x'))) := by
  refine continuous_iff_continuousAt.mpr fun x' => ?_
  have hne : segre (R.lift x' x') ≠ 0 := segre_ne_zero (R.mem x' x' (R.mem_U x')).1
  have h1 : ContinuousAt (fun x'' => minorRatio b (segre (R.lift x' x''))) x' :=
    ContinuousAt.comp (g := minorRatio b) (continuousAt_minorRatio b hne)
      (continuous_segre.continuousAt.comp (continuousAt_lift R x'))
  refine h1.congr ?_
  filter_upwards [(R.isOpen_U x').mem_nhds (R.mem_U x')] with x'' hx''
  obtain ⟨μ, hμ, hμeq⟩ := segre_of_sameOrbit (R.compat x'' x' x'' ⟨R.mem_U x'', hx''⟩)
  rw [hμeq, minorRatio_smul b _ hμ]

theorem isolated_of_not_pullBad (hv : IsBlockMap κ v)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {x : R.X} (hx : x ∉ pullBad R v Ψ) :
    ∃ ε > 0, ∀ z'' ∈ mcPts P', SameOrbit (fun p => z'' (v p)) (pullPt R v x) →
      dist z'' (R.lift x x) < ε → SameOrbit z'' (R.lift x x) := by
  classical
  have hxB : R.lift x x ∉ mcPts J' := fun h => hx (Or.inl (Or.inl h))
  have hz' := R.mem x x (R.mem_U x)
  obtain ⟨j, hj⟩ := R.A.cover x
  have hgood : AnalyticAt ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) ∧
      LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
        (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0 := by
    by_contra h
    exact hx (Or.inr ⟨j, hj, h⟩)
  obtain ⟨e, he⟩ := hasStrictFDerivAt_equiv hgood.1 hgood.2
  have hinj := (he.toOpenPartialHomeomorph (pullQ R v Ψ ∘ (R.A.chart j).symm)).injOn
  set V := (R.A.chart j).source ∩
    (R.A.chart j) ⁻¹' (he.toOpenPartialHomeomorph (pullQ R v Ψ ∘ (R.A.chart j).symm)).source with hVdef
  have hVo : IsOpen V := (R.A.chart j).isOpen_inter_preimage
    (he.toOpenPartialHomeomorph (pullQ R v Ψ ∘ (R.A.chart j).symm)).open_source
  have hxV : x ∈ V := ⟨hj, he.mem_toOpenPartialHomeomorph_source⟩
  have hb : segre (R.lift x x) ≠ 0 := segre_ne_zero hz'.1
  have hθc := continuous_minorRatio_lift R (segre (R.lift x x))
  have hθpos : ∀ x' ∈ Vᶜ, 0 < minorRatio (segre (R.lift x x)) (segre (R.lift x' x')) := by
    intro x' hx'
    refine lt_of_le_of_ne (minorRatio_nonneg _ _) (Ne.symm fun h0 => hx' ?_)
    obtain ⟨μ, hμ, hμeq⟩ := eq_smul_of_minorRatio hb (segre_ne_zero (R.mem x' x' (R.mem_U x')).1) h0
    have hso : SameOrbit (R.lift x' x') (R.lift x x) := sameOrbit_of_segre hz'.1 μ hμ hμeq
    rw [← R.inj x x' hxB (sameOrbit_comm hso)]
    exact hxV
  obtain ⟨m0, hm0, hm0le⟩ : ∃ m0 : ℝ, 0 < m0 ∧
      ∀ x' ∈ Vᶜ, m0 ≤ minorRatio (segre (R.lift x x)) (segre (R.lift x' x')) := by
    rcases (Vᶜ).eq_empty_or_nonempty with hC | hC
    · exact ⟨1, one_pos, fun x' hx' => by rw [hC] at hx'; exact absurd hx' (Set.notMem_empty x')⟩
    · obtain ⟨x1, hx1, hmin⟩ := (hVo.isClosed_compl.isCompact).exists_isMinOn hC hθc.continuousOn
      exact ⟨_, hθpos x1 hx1, fun x' hx' => isMinOn_iff.mp hmin x' hx'⟩
  have hDc : ContinuousAt (fun z : (Σ k', ι' k') → ℂ => minorRatio (segre (R.lift x x)) (segre z))
      (R.lift x x) :=
    ContinuousAt.comp (g := minorRatio (segre (R.lift x x))) (continuousAt_minorRatio _ hb)
      continuous_segre.continuousAt
  obtain ⟨ε1, hε1, hball1⟩ := Metric.continuousAt_iff.mp hDc m0 hm0
  obtain ⟨g, hgJ, hg0⟩ : ∃ g ∈ J', eval (R.lift x x) (map (Int.castRingHom ℂ) g) ≠ 0 := by
    by_contra h
    push Not at h
    exact hxB ⟨hz'.1, h⟩
  have hgc : ContinuousAt (fun z : (Σ k', ι' k') → ℂ => eval z (map (Int.castRingHom ℂ) g))
      (R.lift x x) :=
    (MvPolynomial.continuous_eval _).continuousAt
  obtain ⟨ε2, hε2, hball2⟩ := Metric.continuousAt_iff.mp hgc _ (norm_pos_iff.mpr hg0)
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun z'' hz'' hzv hd => ?_⟩
  have hd1 : dist z'' (R.lift x x) < ε1 := lt_of_lt_of_le hd (min_le_left _ _)
  have hd2 : dist z'' (R.lift x x) < ε2 := lt_of_lt_of_le hd (min_le_right _ _)
  have hzB : z'' ∉ mcPts J' := by
    intro h
    have h2 : dist (eval z'' (map (Int.castRingHom ℂ) g)) (eval (R.lift x x) (map (Int.castRingHom ℂ) g)) <
        ‖eval (R.lift x x) (map (Int.castRingHom ℂ) g)‖ := hball2 hd2
    rw [h.2 g hgJ, dist_zero_left] at h2
    exact lt_irrefl _ h2
  obtain ⟨x'', hx''⟩ := R.surj z'' hz'' hzB
  have hθx'' : minorRatio (segre (R.lift x x)) (segre (R.lift x'' x'')) < m0 := by
    obtain ⟨μ, hμ, hμeq⟩ := segre_of_sameOrbit hx''
    have h1 : dist (minorRatio (segre (R.lift x x)) (segre z''))
        (minorRatio (segre (R.lift x x)) (segre (R.lift x x))) < m0 := hball1 hd1
    rw [minorRatio_self, Real.dist_eq, sub_zero] at h1
    rw [hμeq, minorRatio_smul _ _ hμ]
    exact lt_of_le_of_lt (le_abs_self _) h1
  have hx''V : x'' ∈ V := by
    by_contra hc
    exact absurd (hm0le x'' hc) (not_le.mpr hθx'')
  have hso : SameOrbit (pullPt R v x'') (pullPt R v x) :=
    sameOrbit_tr (sameOrbit_comp hv hx'') hzv
  have hq : pullQ R v Ψ x'' = pullQ R v Ψ x := by
    obtain ⟨μ, hμ, hμeq⟩ := segre_of_sameOrbit hso
    funext i
    simp only [pullQ, hμeq, map_smul, Pi.smul_apply, smul_eq_mul]
    exact mul_div_mul_left _ _ hμ
  have hxx : x'' = x := by
    have h1 : (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x'') =
        (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) := by
      simp only [Function.comp_apply, (R.A.chart j).left_inv hx''V.1, (R.A.chart j).left_inv hj, hq]
    have h2 : R.A.chart j x'' = R.A.chart j x :=
      hinj hx''V.2 hxV.2 (by rw [HasStrictFDerivAt.toOpenPartialHomeomorph_coe]; exact h1)
    exact (R.A.chart j).injOn hx''V.1 hj h2
  rw [hxx] at hx''
  exact sameOrbit_comm hx''

theorem pullFib_finite (hIsol : FibreIsolFinite.Statement) (hv : IsBlockMap κ v)
    (hP' : IsArithVar P' (n + 1)) (hP : IsArithVar (imageZ v P') (n + 1))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (hΨ : IsGoodProj (imageZ v P') Ψ)
    (y : Fin n → ℂ) : (pullQ R v Ψ ⁻¹' {y} \ pullBad R v Ψ).Finite := by
  classical
  have hF := fibreFinite K ι (imageZ v P') n Ψ hP hΨ y
  choose! uw huw using fun w (hw : w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre (imageZ v P') Ψ y) => hw
  choose T hT using fun w => hIsol K ι K' ι' κ v P' n hv hP' (uw w)
  refine (hF.biUnion fun w _ => (T w).finite_toSet.biUnion fun t _ =>
    (orbit_subsingleton R t).finite).subset ?_
  rintro x ⟨hqx, hx⟩
  have hxB : R.lift x x ∉ mcPts J' := fun h => hx (Or.inl (Or.inl h))
  have h0x : Ψ (segre (pullPt R v x)) 0 ≠ 0 := fun h => hx (Or.inl (Or.inr h))
  have hw := IntersectionWithSection.pullW_mem_fibre hv hP R Ψ h0x
  rw [show pullQ R v Ψ x = y from hqx] at hw
  obtain ⟨hu1, hu2, -⟩ := huw _ hw
  have hso : SameOrbit (pullPt R v x) (uw (pullW R v Ψ x)) :=
    sameOrbit_of_segre hu1.1 (Ψ (segre (pullPt R v x)) 0) h0x
      (by rw [hu2]; simp [pullW, smul_smul, mul_inv_cancel₀ h0x])
  obtain ⟨ε, hε, hiso⟩ := isolated_of_not_pullBad R hv Ψ hx
  obtain ⟨t, ht, hxt⟩ := hT (pullW R v Ψ x) (R.lift x x) (R.mem x x (R.mem_U x)) hso
    ⟨ε, hε, fun z'' hz'' hzu hd => hiso z'' hz'' (sameOrbit_tr hzu (sameOrbit_comm hso)) hd⟩
  exact Set.mem_biUnion hw (Set.mem_biUnion (Finset.mem_coe.mpr ht) ⟨hxB, hxt⟩)

end pullbackPushforward_holds

end GroundTheory.Heights₂.Heights.Inter
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M

theorem pullbackPushforward_holds.proof (hGen : BlockGenFinite.Statement) (hIsol : FibreIsolFinite.Statement) :
    pullbackPushforward_holds.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' J' n R Ψ hv hP' hP hΨ
  exact ⟨fun j => pullbackPushforward_holds.pullBad_null R hGen hv hP' hP Ψ hΨ j,
    fun y => pullbackPushforward_holds.pullFib_finite R hIsol hv hP' hP Ψ hΨ y⟩

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionMixedBridge
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

theorem ResolutionMixedBridge.proof : ResolutionMixedBridge.Statement := by
  intro D Ω _ _ κ _ d M m₁ hM hm₁
  have hex : ∃ Ψ : (((k : Unit) → GlobalTheory κ k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ),
      IsGoodProj (coordIdeal ℤ d.x) Ψ :=
    goodProjExists Unit (GlobalTheory κ) (coordIdeal ℤ d.x) D d.arith
  set B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (GlobalTheory κ) := (HermLine.ofCone m₁).tensor (HermLine.ofCone d.m).inv with hBdef
  have hB0 : B.a = 0 := by
    funext k
    simp [B, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.inv, HermLine.ofCone]
  have hgl : logRatio d.m m₁ = logNorm B.inv 1 := by
    funext z
    rw [logNorm_inv_one]
    simp only [B, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.inv, HermLine.ofCone, logRatio, div_eq_mul_inv]
  have hBs : IsSmoothHerm B.inv :=
    isSmoothHerm_inv (isSmoothHerm_tensor (gbamix_smoothHerm_ofCone hm₁)
      (isSmoothHerm_inv (gbamix_smoothHerm_ofCone d.smooth)))
  have hsec : IsSectionOn (coordIdeal ℤ d.x) B.inv 1 := isSectionOn_inv_one d.arith.2.1.1 hB0
  have key := AnResBridge.bridge d.R hex.choose (fun j => HermLine.ofCone (M j)) B.inv 1 d.arith
    hex.choose_spec (fun j => gbamix_smoothHerm_ofCone (hM j)) hBs hsec
  unfold ptsIntegral
  rw [dite_eq_left hex, hgl]
  exact key

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionMixedBridge
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

theorem BlockResolutionMixedBridge.proof : BlockResolutionMixedBridge.Statement := by
  intro D K _ _ ι _ Ω _ _ d L A₁ hL hdeg hA₁
  have hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ),
      IsGoodProj (mCoordIdeal d.y) Ψ :=
    goodProjExists K ι (mCoordIdeal d.y) D d.arith
  set B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := A₁.tensor d.A.inv with hBdef
  have hB0 : B.a = 0 := by
    funext k
    simp [B, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.inv, hdeg, d.deg]
  have hgl : (fun z => Real.log (A₁.h z / d.A.h z)) = logNorm B.inv 1 := by
    funext z
    rw [logNorm_inv_one]
    simp only [B, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.inv, div_eq_mul_inv]
  have hBs : IsSmoothHerm B.inv :=
    isSmoothHerm_inv (isSmoothHerm_tensor hA₁ (isSmoothHerm_inv d.semipos.1))
  have hsec : IsSectionOn (mCoordIdeal d.y) B.inv 1 := isSectionOn_inv_one d.arith.2.1.1 hB0
  have key := AnResBridge.bridge d.R hex.choose L B.inv 1 d.arith hex.choose_spec hL hBs hsec
  have hgr : (fun x => Real.log (A₁.h (blockPt d x) / d.A.h (blockPt d x))) =
      fun x => logNorm B.inv 1 (d.R.lift x x) :=
    funext fun x => congrFun hgl (d.R.lift x x)
  unfold ptsIntegral
  rw [dite_eq_left hex, hgl, hgr]
  exact key

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem BlockResolutionMixedBridge.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMixedBridge.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMixedBridge.proof

theorem ResolutionMixedBridge.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedBridge.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedBridge.proof

theorem Closed.Inter.pullbackPushforward_holds : GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds.proof Closed.Inter.BlockGenFinite Closed.Inter.FibreIsolFinite

theorem Closed.ReciprocityTheory.ChartRestriction.G.Geo.ResBridge : ReciprocityTheory.ChartRestriction.G.Geo.ResBridgeStatement :=
  ReciprocityTheory.ChartRestriction.G.Geo.resBridge

end GroundTheory.Heights₂.Heights.HilbertSamuel
