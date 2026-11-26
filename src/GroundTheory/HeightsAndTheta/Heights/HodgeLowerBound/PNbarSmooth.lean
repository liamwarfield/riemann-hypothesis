module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PNbarSmooth
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace NbarSmooth

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem smoothAlong_pow {S : Set ((Σ k, ι k) → ℂ)} {f : ((Σ k, ι k) → ℂ) → ℝ} (hf : SmoothAlong S f) (n : ℕ) :
    SmoothAlong S fun z => f z ^ n := by
  intro z hz
  obtain ⟨U, hU, F, hF, hfF⟩ := hf z hz
  exact ⟨U, hU, fun w => F w ^ n, hF.pow n, fun w hw => by show f w ^ n = F w ^ n; rw [hfF w hw]⟩

theorem hermOfFun_h_of_mem {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {a : K → ℤ}
    {F : ((Σ k, ι k) → ℂ) → ℝ}
    (hF : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) (hpos : 0 < F z) : (hermOfFun ι a F).h z = F z := by
  obtain ⟨c, hc, hzc⟩ := exists_eq_smul_orbitRep z
  set w := orbitRep z with hw
  have hwz : w = torusSmul c⁻¹ z := by
    funext p
    rw [hzc]
    simp [torusSmul, inv_mul_cancel_left₀ (hc p.1)]
  have hcinv : ∀ k, c⁻¹ k ≠ 0 := fun k => by simpa using hc k
  have hwP : w ∈ mcPts P := by rw [hwz]; exact mcPts_smul hP c⁻¹ hcinv hz
  have hP' := prod_norm_zpow_pos hc a
  have hFz : F z = (∏ k, ‖c k‖ ^ a k) * F w := by rw [hzc]; exact hF w hwP c hc
  have hRz : refNorm a z = (∏ k, ‖c k‖ ^ a k) * refNorm a w := by rw [hzc]; exact refNorm_smul a c w
  have hFw : 0 < F w := by
    rw [hFz] at hpos
    exact pos_of_mul_pos_right hpos hP'.le
  have hRw := refNorm_pos a hwP.1
  show refNorm a z * Real.exp (Real.log (F w / refNorm a w)) = F z
  rw [Real.exp_log (div_pos hFw hRw), hRz, hFz]
  field_simp

end NbarSmooth


open MuRegSmooth TopNPoly NbarSmooth in
theorem NbarSmooth.proof (hE : HermExtend.Statement) (hP : ProjSmoothAlong.Statement)
    (hVS : VertFactorSmooth.Statement) : NbarSmooth.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q t hsm
  set P := mCoordIdeal D.y with hPdef
  set a : K → ℤ := (q : ℤ) • muTwDeg X.H B + (p : ℤ) • D.a' with ha
  set F : ((Σ k, ι k) → ℂ) → ℝ := fun z => (X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z))) ^ q *
    (∏ p' ∈ D.SB B, D.vertFactor p' z) ^ q * D.A'.h z ^ p with hFdef
  have hSB : ∀ p' ∈ D.SB B, p' ∈ D.S := fun p' hp' => (Finset.mem_filter.1 hp').1
  have hMH : IsMultiHomogIdeal P := D.arith.2.1.2.1
  have hpos : ∀ z ∈ mcPts P, 0 < F z := by
    intro z hz
    have h2 : 0 < ∏ p' ∈ D.SB B, D.vertFactor p' z := Finset.prod_pos fun p' hp' =>
      VertFactorPos.proof II Ψ K ι Ω E D p' (hSB p' hp') z hz
    exact mul_pos (mul_pos (pow_pos (mul_pos (X.S.ref.pos z hz.1) (Real.exp_pos _)) q) (pow_pos h2 q))
      (pow_pos (D.A'.pos z hz.1) p)
  have hhom : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z := by
    intro z hz c hc
    have hcz : torusSmul c z ∈ mcPts P := mcPts_smul hMH c hc hz
    have hproj : X.M.proj (torusSmul c z) = X.M.proj z := ((X.M.fibre z hz _ hcz).2 ⟨c, hc, rfl⟩).symm
    have href : X.S.ref.h (torusSmul c z) = (∏ k, ‖c k‖ ^ X.H.aMu k) * X.S.ref.h z := by
      have := X.S.ref.smul c z hc
      rw [X.S.ref_deg] at this
      exact this
    have hA : D.A'.h (torusSmul c z) = (∏ k, ‖c k‖ ^ D.a' k) * D.A'.h z := by
      have := D.A'.smul c z hc
      rw [D.A'_deg] at this
      exact this
    have hV : ∀ p' ∈ D.SB B, D.vertFactor p' (torusSmul c z) =
        (∏ k, ‖c k‖ ^ D.vdeg p' k) * D.vertFactor p' z :=
      fun p' hp' => (hVS II Ψ K ι Ω E D p' (hSB p' hp')).1 z hz c hc
    have hk : ∀ k, ‖c k‖ ^ a k = (‖c k‖ ^ (muTwDeg X.H B) k) ^ q * (‖c k‖ ^ D.a' k) ^ p := by
      intro k
      have hx : ‖c k‖ ≠ 0 := norm_ne_zero_iff.mpr (hc k)
      have hak : a k = (q : ℤ) * (muTwDeg X.H B) k + (p : ℤ) * D.a' k := by
        simp only [ha, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hak, zpow_add₀ hx, zpow_mul', zpow_natCast, zpow_mul', zpow_natCast]
    have hprod : (∏ k, ‖c k‖ ^ a k) = ((∏ k, ‖c k‖ ^ X.H.aMu k) *
        ∏ p' ∈ D.SB B, ∏ k, ‖c k‖ ^ D.vdeg p' k) ^ q * (∏ k, ‖c k‖ ^ D.a' k) ^ p := by
      rw [Finset.prod_congr rfl fun k _ => hk k, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow,
        muTwDeg, prod_norm_zpow_add_sum hc]
    simp only [hFdef]
    rw [hproj, href, hA, Finset.prod_congr rfl hV, Finset.prod_mul_distrib, hprod]
    ring
  have hsmooth : SmoothAlong (mcPts P) F :=
    smoothAlong_mul (smoothAlong_mul
      (smoothAlong_pow (smoothAlong_mul (smoothAlong_of_contDiffOn X.S.ref_smooth)
        (smoothAlong_exp (hP II Ψ K ι Ω E D X.M _ hsm))) q)
      (smoothAlong_pow (smoothAlong_prod _ fun p' hp' => (hVS II Ψ K ι Ω E D p' (hSB p' hp')).2) q))
      (smoothAlong_pow (smoothAlong_of_contDiffOn D.A'_pos.1) p)
  obtain ⟨Z, hZa, hZs, hZh⟩ := hE K ι P a F hMH hpos hhom hsmooth
  show IsSmoothHerm (smoothRep P (hermOfFun ι a F))
  exact smoothRep_smooth_of (Z := Z) hZa hZs fun z hz =>
    (hZh z hz).trans (hermOfFun_h_of_mem hMH hhom hz (hpos z hz)).symm

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StAPrimeChartMargin
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)

def APrimeChartMargin.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt),
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ w, ∀ k : Fin X.S.R.N, X.M.proj z ∈ X.S.R.mid k →
      ∀ v : Fin D.n → ℂ, IsChartVel X.M (X.S.R.chart k) z w v →
        c * ‖v‖ ^ 2 ≤ levi (fun y => Real.log (D.A'.h y)) z w

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StProjHoloLocal
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def ProjHoloLocal.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (M : XModel D)
    (e : OpenPartialHomeomorph M.Xc (Fin D.n → ℂ)), ReciprocityTheory.AnForm.M.IsCompatChart M.atlas e →
    ∀ z ∈ mcPts (mCoordIdeal D.y), M.proj z ∈ e.source →
      ∃ W : Set ((Σ k, ι k) → ℂ), IsOpen W ∧ z ∈ W ∧ ∃ F : ((Σ k, ι k) → ℂ) → Fin D.n → ℂ,
        DifferentiableOn ℂ F W ∧
          ∀ z' ∈ W ∩ mcPts (mCoordIdeal D.y), M.proj z' ∈ e.source ∧ e (M.proj z') = F z'

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuSheetLeviNonneg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open GroundTheory.Heights₂.Heights.Regular (RegChartData)
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.A (coordDiv)
open ReciprocityTheory.AnForm.M (FinHolAtlas)

theorem analyticAt_pi_of_eventually_differentiableAt {d m : ℕ} {f : (Fin d → ℂ) → Fin m → ℂ} {y : Fin d → ℂ}
    (h : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ f y') : AnalyticAt ℂ f y := by
  obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.1 h
  refine AnalyticAt.pi fun i => ReciprocityTheory.AnForm.Osgood.osgood d U (fun w => f w i) hUo (fun z hz => ?_) y hyU
  exact (differentiableAt_pi.mp (hU z hz) i).differentiableWithinAt

theorem RegChartData.contDiffAt_u {n : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas n X}
    (R : RegChartData A) (j : Fin R.N) {ξ : Fin n → ℂ} (hξ : ξ ∈ (R.chart j).target \ coordDiv (R.S j)) :
    ContDiffAt ℝ 2 (R.u j) ξ := by
  have hp : (R.chart j).symm ξ ∈ (R.chart j).source := (R.chart j).map_target hξ.1
  have hYo : R.Yo ∈ 𝓝 ((R.chart j).symm ξ) := by
    refine Filter.mem_of_superset (((R.chart j).isOpen_inter_preimage
      (ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed (R.S j)).isOpen_compl).mem_nhds ⟨hp, ?_⟩)
      fun x hx => (R.mem_Yo j x hx.1).2 hx.2
    change (R.chart j) ((R.chart j).symm ξ) ∉ coordDiv (R.S j)
    rw [(R.chart j).right_inv hξ.1]
    exact hξ.2
  obtain ⟨i, hi⟩ := A.cover ((R.chart j).symm ξ)
  have hti : (A.chart i) ((R.chart j).symm ξ) ∈ (A.chart i).target := (A.chart i).map_source hi
  have h1 : ContDiffAt ℝ 2 (R.ph ∘ (A.chart i).symm) ((A.chart i) ((R.chart j).symm ξ)) := by
    refine ((R.ph_smooth i).contDiffAt (Filter.inter_mem ((A.chart i).open_target.mem_nhds hti) ?_)).of_le
      (by first | simp | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤) | exact WithTop.coe_le_coe.mpr le_top)
    refine (A.chart i).continuousAt_symm hti |>.preimage_mem_nhds ?_
    rw [(A.chart i).left_inv hi]
    exact hYo
  have hτ : AnalyticAt ℂ ((A.chart i) ∘ (R.chart j).symm) ξ := ((R.compat j i).2) ξ ⟨hξ.1, hi⟩
  have h2 : ContDiffAt ℝ 2 (fun ξ' => R.ph ((R.chart j).symm ξ')) ξ := by
    refine (h1.comp ξ hτ.restrictScalars.contDiffAt).congr_of_eventuallyEq ?_
    filter_upwards [(R.chart j).continuousAt_symm hξ.1 |>.preimage_mem_nhds
      ((A.chart i).open_source.mem_nhds hi)] with ξ' h
    simp only [Function.comp_apply, (A.chart i).left_inv h]
  have hq : ContDiffAt ℝ 2 (R.q j) ξ :=
    ((R.q_smooth j).contDiffAt ((R.chart j).open_target.mem_nhds hξ.1)).of_le (by first | simp | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤) | exact WithTop.coe_le_coe.mpr le_top)
  exact hq.add h2

theorem LogLogRegularisationSetting.log_h_eq {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)}
    {n : ℕ} {M : CxModel P n} {Xo : Set ((Σ k, ι k) → ℂ)} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (S : LogLogRegularisationSetting M Xo A)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) (hY : M.proj z ∈ S.R.Yo) :
    Real.log (A.h z) = S.R.ph (M.proj z) + Real.log (S.ref.h z) := by
  obtain ⟨z', ⟨hz'o, hz'⟩, hp⟩ := S.Yo_sub _ hY
  obtain ⟨c, hc, rfl⟩ := (M.fibre z' hz' _ hz).1 hp
  have hph := S.ph_eq z' ⟨hz'o, hz'⟩ (by rw [hp]; exact hY)
  have hA : A.h (torusSmul c z') = (∏ k, ‖c k‖ ^ A.a k) * A.h z' := A.smul c z' hc
  have hR : S.ref.h (torusSmul c z') = (∏ k, ‖c k‖ ^ A.a k) * S.ref.h z' := by
    rw [← S.ref_deg]; exact S.ref.smul c z' hc
  have hpos : 0 < ∏ k, ‖c k‖ ^ A.a k := Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hc k)) _
  rw [hA, hR, Real.log_mul hpos.ne' (A.pos z' hz'.1).ne', Real.log_mul hpos.ne' (S.ref.pos z' hz'.1).ne', ← hp,
    hph]
  ring

theorem MuSheetLeviNonneg.proof (hH : SheetChartHolo.Statement) (hR : RefAlongSheet.Statement) :
    MuSheetLeviNonneg.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X Q _
  filter_upwards [hH K ι (mCoordIdeal D.y) D.n X.M X.S.R Q] with y hy w γ hγ
  obtain ⟨j, hsrc, hYo, hev⟩ := hy w γ hγ
  have hγev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ γ y' ∈ mcPts (mCoordIdeal D.y) :=
    hγ.2.mono fun _ h => ⟨h.1, h.2.1⟩
  obtain ⟨G, hG, hGeq⟩ := hR K ι _ D.n X.M D.Xo (muLine X.H) X.S γ y j hγev hsrc hev
  set g : (Fin D.n → ℂ) → Fin D.n → ℂ := fun y'' => X.S.R.chart j (X.M.proj (γ y'')) with hgdef
  have hg : AnalyticAt ℂ g y := analyticAt_pi_of_eventually_differentiableAt (hev.mono fun _ h => h.2)
  have hgy : g y ∈ (X.S.R.chart j).target \ coordDiv (X.S.R.S j) :=
    ⟨(X.S.R.chart j).map_source hsrc, (X.S.R.mem_Yo j _ hsrc).1 hYo⟩
  have hUo : IsOpen ((X.S.R.chart j).target \ coordDiv (X.S.R.S j)) :=
    (X.S.R.chart j).open_target.sdiff (ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed _)
  have hC2 : ContDiffOn ℝ 2 (X.S.R.u j) ((X.S.R.chart j).target \ coordDiv (X.S.R.S j)) :=
    fun ξ hξ => (RegChartData.contDiffAt_u X.S.R j hξ).contDiffWithinAt
  have hL := ((ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm _ _ _ hUo hC2).1 (X.S.R.u_psh j)).2
  have hgU : ∀ᶠ y' in 𝓝 y, g y' ∈ (X.S.R.chart j).target \ coordDiv (X.S.R.S j) :=
    hg.continuousAt.preimage_mem_nhds (hUo.mem_nhds hgy)
  have heq : (fun y' => phMu X.H (γ y')) =ᶠ[𝓝 y] fun y' => (X.S.R.u j ∘ g) y' + 1 * (G y').re := by
    filter_upwards [hγev, hev, hgU, hGeq] with y' h1 h2 h3 h4
    have hY' : X.M.proj (γ y') ∈ X.S.R.Yo := (X.S.R.mem_Yo j _ h2.1).2 h3.2
    have hl := X.S.log_h_eq h1.2 hY'
    show Real.log ((muLine X.H).h (γ y')) =
      X.S.R.q j (g y') + X.S.R.ph ((X.S.R.chart j).symm (g y')) + 1 * (G y').re
    rw [hl, h4, hgdef]
    simp only [(X.S.R.chart j).left_inv h2.1]
    ring
  have hu2 : ContDiffAt ℝ 2 (X.S.R.u j) (g y) := RegChartData.contDiffAt_u X.S.R j hgy
  have hcomp : ContDiffAt ℝ 2 (X.S.R.u j ∘ g) y := hu2.comp y hg.restrictScalars.contDiffAt
  have hre : ContDiffAt ℝ 2 (fun y' => (G y').re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y hG.restrictScalars.contDiffAt
  refine ⟨(hcomp.add (contDiffAt_const.mul hre)).congr_of_eventuallyEq heq, fun v => ?_⟩
  change 0 ≤ levi (fun y' => phMu X.H (γ y')) y v
  rw [ReciprocityTheory.AnForm.levi_congr heq, ReciprocityTheory.AnForm.levi_add_smul 1 hcomp hre,
    ReciprocityTheory.AnForm.levi_re_analytic hG, ReciprocityTheory.AnForm.levi_comp v hg hu2]
  simpa using hL _ hgy _

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.POmNVbInt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem OmNVbInt.proof (hT : TpCuspIntegrable.Statement) (hS : NbarSmooth.Statement) : OmNVbInt.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q _ _
  filter_upwards [X.S.eventually_chartLevi X.S_tied] with t ht
  exact hT II Ψ K ι Ω E D O Lt X B p q t (hS II Ψ K ι Ω E D O Lt X B p q t ht.1)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PBoundaryNull
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem BoundaryNull.proof : BoundaryNull.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D
  classical
  exact BoundaryPtsNull.proof II Ψ K ι Ω E D

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPushDown
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem PushDown.proof (hAI3 : Inter.PushforwardArithIntersection.Statement) (hStep : Inter.PFStep.Statement)
    (hArith : HodgeFlagArith.Statement) : PushDown.Statement := by
  intro II hII Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl H B
  have hPF := Inter.PushforwardProjLineFlag.proof hAI3 hStep
  have hY := hArith II Ψ K ι Ω E D Pl H B
  have hX : IsArithVar (imageZ Pl.xV (Pl.flagPrime B)) (D.n + 1) := by
    rw [Pl.imageZ_forget_flagPrime]
    exact D.arith
  refine ⟨fun G J L L' N hJ hL hL' hN => ?_, fun d r L L' N hdr hd hL hL' hN => ?_⟩
  · have h := hPF II hII.1 K ι (K ⊕ (Ψ × Fin (D.N - 1))) Pl.ιY Sum.inl Pl.xV (Pl.flagPrime B) (D.n + 1) D.flagDim0
      G J L L' N Pl.isBlockMap_xV hY hX hJ hL hL' hN
    rwa [Pl.imageZ_forget_flagPrime] at h
  · exact hII.2.2.2 K ι (K ⊕ (Ψ × Fin (D.N - 1))) Pl.ιY Sum.inl Pl.xV (Pl.flagPrime B) (D.n + 1) d r L L' N
      Pl.isBlockMap_xV (by rw [hdr]; exact hY) hX hd hL hL' hN

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ModelProjObjects
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}

def modelU (M : CxModel P e) (x : M.Xc) : Set M.Xc :=
  (M.sections x).choose

def modelLift (M : CxModel P e) (x : M.Xc) : M.Xc → (Σ k, ι k) → ℂ :=
  (M.sections x).choose_spec.2.2.choose

theorem modelU_isOpen (M : CxModel P e) (x : M.Xc) : IsOpen (modelU M x) :=
  (M.sections x).choose_spec.1

theorem mem_modelU (M : CxModel P e) (x : M.Xc) : x ∈ modelU M x :=
  (M.sections x).choose_spec.2.1

theorem modelLift_spec (M : CxModel P e) (x : M.Xc) :
    (∀ y ∈ modelU M x, modelLift M x y ∈ mcPts P ∧ M.proj (modelLift M x y) = y) ∧
      ∀ p, M.atlas.HoloOn (modelU M x) fun y => modelLift M x y p :=
  (M.sections x).choose_spec.2.2.choose_spec

def modelPot (M : CxModel P e) (L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ) : LocPot M.Xc where
  U := modelU M
  isOpen_U := modelU_isOpen M
  mem_U := mem_modelU M
  φ x y := c * Real.log (L.h (modelLift M x y))

def modelQ (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : M.Xc) : Fin e → ℂ :=
  fun i => Ψ (segre (modelLift M x x)) i.succ / Ψ (segre (modelLift M x x)) 0

def modelCrit (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Set M.Xc :=
  {x | Ψ (segre (modelLift M x x)) 0 = 0 ∨ ∃ j, x ∈ (M.atlas.chart j).source ∧
    ¬ (AnalyticAt ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (M.atlas.chart j x) ∧
      LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (M.atlas.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)}

def modelBad (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (E : Set M.Xc) : Set M.Xc :=
  E ∪ modelCrit M Ψ

theorem modelQ_good_of_notMem (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (E : Set M.Xc) : ∀ x ∉ modelBad M Ψ E, ∀ j, x ∈ (M.atlas.chart j).source →
      AnalyticAt ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (M.atlas.chart j x) ∧
        LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (M.atlas.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0 := by
  intro x hx j hj
  by_contra h
  exact hx (Or.inr (Or.inr ⟨j, hj, h⟩))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelLogIntegrable
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm.A (coordDiv)

namespace ModelLogIntegrableAlt

theorem volume_coordDiv {D : ℕ} (S : Finset (Fin D)) : volume (coordDiv S) = 0 := by
  have h : coordDiv S = ⋃ i ∈ S, (fun z : Fin D → ℂ => z i) ⁻¹' {0} := by
    ext z
    simp [coordDiv]
  rw [h]
  refine (measure_biUnion_null_iff S.countable_toSet).2 fun i _ => ?_
  rw [volume_pi]
  exact Measure.pi_eval_preimage_null _ (measure_singleton 0)

theorem target_inter_compl_Yo_subset {D : ℕ} {X : Type*} [TopologicalSpace X]
    {A : ReciprocityTheory.AnForm.M.FinHolAtlas D X} (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A) (j : Fin R.N) :
    (R.chart j).target ∩ (R.chart j).symm ⁻¹' R.Yoᶜ ⊆ coordDiv (R.S j) := by
  rintro y ⟨hy, hyY⟩
  have h := R.mem_Yo j _ ((R.chart j).map_target hy)
  rw [(R.chart j).right_inv hy] at h
  by_contra hc
  exact hyY (h.2 hc)

end ModelLogIntegrableAlt


open ModelLogIntegrableAlt in
theorem ModelLogIntegrable.proof (hM : ModelPtsIntegrable.Statement) : ModelLogIntegrable.Statement := by
  intro K _ ι _ P e M R L c N u C C' g hP hL hN hu hbd hg
  let _ : MeasurableSpace M.Xc := borel M.Xc
  have _ : BorelSpace M.Xc := ⟨rfl⟩
  obtain ⟨B, hB⟩ := R.f_bdd
  refine hM K ι P e M R.N R.chart L c N R.Yoᶜ u g hP hL hN R.compat (fun x => ?_)
    (fun j => measure_mono_null (target_inter_compl_Yo_subset R j) (volume_coordDiv _))
    (fun j Q hQ hQc => ?_) (fun z hz hzN hzE => hg z hz hzN (not_not.mp hzE))
  · obtain ⟨j, hj⟩ := R.cover x
    exact ⟨j, R.toPotentialCharts.mid_subset_source j (R.toPotentialCharts.inner_subset_mid j hj)⟩

  have hQp : Q ⊆ GroundTheory.Heights₂.Heights.LogInt.polydisc (Fin e) 1 := by
    intro y hy
    have hb : ‖y‖ < 1 := by simpa using R.target_subset j (hQ hy)
    intro i _
    simpa using (norm_le_pi_norm y i).trans hb.le
  set G : (Fin e → ℂ) → ℝ := fun y => |C| + |C'| * (Real.exp 1 + B) +
    |C'| * ∑ i ∈ R.S j, 2 * |Real.log ‖y i‖| with hGdef
  have hG : IntegrableOn G Q := by
    refine IntegrableOn.mono_set ?_ hQp
    refine ((integrableOn_const (GroundTheory.Heights₂.Heights.LogInt.volume_polydisc_ne_top 1)).add
      (Integrable.const_mul (integrable_finsetSum _ fun i _ =>
        ((GroundTheory.Heights₂.Heights.LogInt.integrableOn_log_norm_coord 1 i).abs.const_mul 2)) _))
  have hmeas : AEStronglyMeasurable (fun y => u ((R.chart j).symm y)) (volume.restrict Q) :=
    (hu.comp_aemeasurable (((R.chart j).continuousOn_symm.mono hQ).aemeasurable
      hQc.isClosed.measurableSet)).aestronglyMeasurable
  refine Integrable.mono' hG hmeas ?_
  filter_upwards [ae_restrict_mem hQc.isClosed.measurableSet,
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp (volume_coordDiv (R.S j)))] with y hyQ hyD
  have hyt := hQ hyQ
  have hYo : (R.chart j).symm y ∈ R.Yo := by
    have h := R.mem_Yo j _ ((R.chart j).map_target hyt)
    rw [(R.chart j).right_inv hyt] at h
    exact h.2 hyD
  have h1 := hbd _ hYo
  have hr1 := R.one_le_r _ hYo
  have hrc := R.r_chart j y ⟨hyt, hyD⟩
  set r := R.r ((R.chart j).symm y) with hrdef
  have hlog0 : 0 ≤ Real.log r := Real.log_nonneg hr1
  have hlogr : Real.log r ≤ r := by linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < r)]
  have hf : R.f j y ≤ B := (le_abs_self _).trans (hB j y hyt)
  have hsum : ∑ i ∈ R.S j, Real.log (‖y i‖ ^ 2)⁻¹ ≤ ∑ i ∈ R.S j, 2 * |Real.log ‖y i‖| := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Real.log_inv, Real.log_pow]
    push_cast
    linarith [neg_abs_le (Real.log ‖y i‖)]
  have hrb : r ≤ Real.exp 1 + B + ∑ i ∈ R.S j, 2 * |Real.log ‖y i‖| := by
    rw [hrc]; linarith
  have hC : C + C' * Real.log r ≤ |C| + |C'| * r := by
    have := mul_le_mul_of_nonneg_right (le_abs_self C') hlog0
    have := mul_le_mul_of_nonneg_left hlogr (abs_nonneg C')
    linarith [le_abs_self C]
  have hC2 : |C'| * r ≤ |C'| * (Real.exp 1 + B) + |C'| * ∑ i ∈ R.S j, 2 * |Real.log ‖y i‖| := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C')
  rw [Real.norm_eq_abs, hGdef]
  linarith

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PRefAlongSheet
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas)

theorem analyticAt_holoOn_comp_chartSymm {e m : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas e X}
    {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : ReciprocityTheory.AnForm.M.IsCompatChart A ψ) {V : Set X}
    {F : X → ℂ} (hF : A.HoloOn V F) {g : (Fin m → ℂ) → Fin e → ℂ} {y : Fin m → ℂ} (hg : AnalyticAt ℂ g y)
    (hgy : g y ∈ ψ.target) (hV : ψ.symm (g y) ∈ V) :
    AnalyticAt ℂ (fun y' => F (ψ.symm (g y'))) y := by
  obtain ⟨i, hi⟩ := A.cover (ψ.symm (g y))
  have hτ : AnalyticAt ℂ (A.chart i ∘ ψ.symm) (g y) := (hψ i).2 (g y) ⟨hgy, hi⟩
  have hFi : AnalyticAt ℂ (F ∘ (A.chart i).symm) ((A.chart i ∘ ψ.symm) (g y)) := by
    refine hF i _ ⟨(A.chart i).map_source hi, ?_⟩
    show (A.chart i).symm (A.chart i (ψ.symm (g y))) ∈ V
    rw [(A.chart i).left_inv hi]
    exact hV
  refine ((hFi.comp hτ).comp hg).congr ?_
  have hc : ContinuousAt (fun y' => ψ.symm (g y')) y := (ψ.continuousAt_symm hgy).comp hg.continuousAt
  filter_upwards [hc.preimage_mem_nhds ((A.chart i).open_source.mem_nhds hi)] with y' hy'
  simp only [Function.comp_apply, (A.chart i).left_inv hy']

theorem RefAlongSheet.proof : RefAlongSheet.Statement := by
  intro K _ ι _ P n M Xo A S γ y j hγ hsrc hev
  classical
  obtain ⟨g, hg'⟩ : ∃ g : (Fin n → ℂ) → Fin n → ℂ, g = fun y'' => S.R.chart j (M.proj (γ y'')) := ⟨_, rfl⟩
  have hg : AnalyticAt ℂ g y := by
    obtain ⟨V, hV, hVo, hyV⟩ := eventually_nhds_iff.1 (hev.mono fun _ h => h.2)
    refine AnalyticAt.pi fun i => ReciprocityTheory.AnForm.Osgood.osgood n V (fun w => g w i) hVo (fun z hz => ?_) y hyV
    rw [hg']
    exact (differentiableAt_pi.mp (hV z hz) i).differentiableWithinAt
  have hγc : ∀ p, AnalyticAt ℂ (fun w => γ w p) y := by
    intro p
    obtain ⟨V, hV, hVo, hyV⟩ := eventually_nhds_iff.1 (hγ.mono fun _ h => h.1)
    exact ReciprocityTheory.AnForm.Osgood.osgood n V (fun w => γ w p) hVo
      (fun z hz => (differentiableAt_pi.mp (hV z hz) p).differentiableWithinAt) y hyV
  have hgy : g y ∈ (S.R.chart j).target := by rw [hg']; exact (S.R.chart j).map_source hsrc
  have hxy : (S.R.chart j).symm (g y) = M.proj (γ y) := by rw [hg']; exact (S.R.chart j).left_inv hsrc
  obtain ⟨U, hUo, hx0U, hUth, s, hs, hsh, G1, hG1, hG1eq⟩ :=
    S.th_ref (M.proj (γ y)) (M.proj (γ y)) (S.R.th.mem_U _)
  obtain ⟨W, hWo, hx0W, G2, hG2, hG2eq⟩ := S.R.q_th j (M.proj (γ y)) (M.proj (γ y)) ⟨S.R.th.mem_U _, hsrc⟩
  obtain ⟨x', hx'⟩ : ∃ x' : (Fin n → ℂ) → M.Xc, x' = fun y' => (S.R.chart j).symm (g y') := ⟨_, rfl⟩
  have hsxy : x' y = M.proj (γ y) := by rw [hx']; exact hxy
  have hx'c : ContinuousAt x' y := by
    rw [hx']; exact ((S.R.chart j).continuousAt_symm hgy).comp hg.continuousAt
  have hsc : ∀ p, AnalyticAt ℂ (fun y' => s (x' y') p) y := fun p => by
    rw [hx']
    exact analyticAt_holoOn_comp_chartSymm (S.R.compat j) (hsh p) hg hgy (by rw [hxy]; exact hx0U)
  have hG1x : AnalyticAt ℂ (fun y' => G1 (x' y')) y := by
    rw [hx']
    exact analyticAt_holoOn_comp_chartSymm (S.R.compat j) hG1 hg hgy (by rw [hxy]; exact hx0U)
  have hG2x : AnalyticAt ℂ (fun y' => G2 (x' y')) y := by
    rw [hx']
    exact analyticAt_holoOn_comp_chartSymm (S.R.compat j) hG2 hg hgy (by rw [hxy]; exact hx0W)
  have hs0 : s (M.proj (γ y)) ∈ mcPts P := (hs _ hx0U).1
  choose i hi using hs0.1
  obtain ⟨cf, hcf⟩ : ∃ cf : K → (Fin n → ℂ) → ℂ,
      cf = fun k y' => γ y' ⟨k, i k⟩ / s (x' y') ⟨k, i k⟩ := ⟨_, rfl⟩
  have hsi : ∀ k, s (x' y) ⟨k, i k⟩ ≠ 0 := fun k => by rw [hsxy]; exact hi k
  have hcfa : ∀ k, AnalyticAt ℂ (cf k) y := fun k => by
    rw [hcf]; exact (hγc _).div (hsc _) (hsi k)
  have hne : ∀ᶠ y' in 𝓝 y, ∀ k, s (x' y') ⟨k, i k⟩ ≠ 0 :=
    Filter.eventually_all.2 fun k => (hsc _).continuousAt.eventually_ne (hsi k)
  have hUWn : U ∩ W ∈ 𝓝 (x' y) := (hUo.inter hWo).mem_nhds (by rw [hsxy]; exact ⟨hx0U, hx0W⟩)
  have hgood : ∀ᶠ y' in 𝓝 y, (x' y' ∈ U ∩ W ∧ M.proj (γ y') ∈ (S.R.chart j).source ∧ γ y' ∈ mcPts P) ∧
      ∀ k, s (x' y') ⟨k, i k⟩ ≠ 0 := by
    filter_upwards [hx'c.preimage_mem_nhds hUWn, hev, hγ, hne] with y' h1 h2 h3 h4
    exact ⟨⟨h1, h2.1, h3.2⟩, h4⟩
  have key : ∀ y', ((x' y' ∈ U ∩ W ∧ M.proj (γ y') ∈ (S.R.chart j).source ∧ γ y' ∈ mcPts P) ∧
      ∀ k, s (x' y') ⟨k, i k⟩ ≠ 0) →
      (∀ k, cf k y' ≠ 0) ∧ Real.log (S.ref.h (γ y')) = ∑ k, (S.ref.a k : ℝ) * Real.log ‖cf k y'‖ +
        (S.R.q j (S.R.chart j (M.proj (γ y'))) - (G2 (x' y')).re - (G1 (x' y')).re) := by
    rintro y' ⟨⟨⟨hU', hW'⟩, hsrc', hγ'⟩, hne'⟩
    have hxp : x' y' = M.proj (γ y') := by rw [hx', hg']; exact (S.R.chart j).left_inv hsrc'
    obtain ⟨hsm, hsp⟩ := hs _ hU'
    obtain ⟨c, hc, hγc'⟩ := (M.fibre _ hsm _ hγ').1 (by rw [hsp, hxp])
    have hck : ∀ k, cf k y' = c k := fun k => by
      have h := congrFun hγc' ⟨k, i k⟩
      rw [hcf]
      show γ y' ⟨k, i k⟩ / s (x' y') ⟨k, i k⟩ = c k
      rw [h]
      exact mul_div_cancel_right₀ (c k) (hne' k)
    have hh : S.ref.h (γ y') = (∏ k, ‖c k‖ ^ S.ref.a k) * S.ref.h (s (x' y')) := by
      rw [hγc']; exact S.ref.smul c _ hc
    have hpos : ∀ k, 0 < ‖c k‖ := fun k => norm_pos_iff.2 (hc k)
    have hlog : Real.log (S.ref.h (γ y')) =
        ∑ k, (S.ref.a k : ℝ) * Real.log ‖c k‖ + Real.log (S.ref.h (s (x' y'))) := by
      rw [hh, Real.log_mul (Finset.prod_pos fun k _ => zpow_pos (hpos k) _).ne' (S.ref.pos _ hsm.1).ne',
        Real.log_prod fun k _ => (zpow_pos (hpos k) _).ne']
      simp only [Real.log_zpow]
    have h1 := hG1eq _ hU'
    have hsrc'' : x' y' ∈ (S.R.chart j).source := by rw [hxp]; exact hsrc'
    have h2 := hG2eq _ ⟨⟨hW', hUth hU'⟩, hsrc''⟩
    refine ⟨fun k => by rw [hck]; exact hc k, ?_⟩
    rw [hlog, ← hxp]
    simp only [hck]
    linarith
  have hcy : ∀ k, cf k y ≠ 0 := (key y hgood.self_of_nhds).1
  refine ⟨fun y' => ∑ k, ((S.ref.a k : ℝ) : ℂ) * (Complex.log (cf k y' / cf k y) + (Real.log ‖cf k y‖ : ℂ)) -
    (G1 (x' y') + G2 (x' y')), ?_, ?_⟩
  · have hterm : ∀ k, AnalyticAt ℂ (fun y' => ((S.ref.a k : ℝ) : ℂ) *
        (Complex.log (cf k y' / cf k y) + (Real.log ‖cf k y‖ : ℂ))) y := fun k => by
      have hl : AnalyticAt ℂ (fun y' => Complex.log (cf k y' / cf k y)) y := by
        refine ((hcfa k).div analyticAt_const (hcy k)).clog ?_
        show cf k y / cf k y ∈ Complex.slitPlane
        rw [div_self (hcy k)]
        exact Complex.one_mem_slitPlane
      exact analyticAt_const.mul (hl.add analyticAt_const)
    have hsum : AnalyticAt ℂ (fun y' => ∑ k, ((S.ref.a k : ℝ) : ℂ) *
        (Complex.log (cf k y' / cf k y) + (Real.log ‖cf k y‖ : ℂ))) y := by
      have h := Finset.analyticAt_sum (𝕜 := ℂ) (f := fun k y' => ((S.ref.a k : ℝ) : ℂ) *
        (Complex.log (cf k y' / cf k y) + (Real.log ‖cf k y‖ : ℂ))) Finset.univ fun k _ => hterm k
      convert h using 1
      ext y'
      simp [Finset.sum_apply]
    have hG12 : AnalyticAt ℂ (fun y' => G1 (x' y') + G2 (x' y')) y := hG1x.add hG2x
    exact hsum.sub hG12
  · filter_upwards [hgood] with y' hy'
    obtain ⟨hnz, heq⟩ := key y' hy'
    rw [heq]
    have hl : ∀ k, Real.log ‖cf k y' / cf k y‖ = Real.log ‖cf k y'‖ - Real.log ‖cf k y‖ := fun k => by
      rw [norm_div, Real.log_div (norm_ne_zero_iff.2 (hnz k)) (norm_ne_zero_iff.2 (hcy k))]
    simp only [Complex.sub_re, Complex.add_re, Complex.re_sum, Complex.re_ofReal_mul, Complex.log_re,
      Complex.ofReal_re, hl, sub_add_cancel]
    ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PSheetChartHolo
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open GroundTheory.Heights₂.Heights.Regular (RegChartData)
open ReciprocityTheory.AnForm.A (coordDiv)
open ReciprocityTheory.AnForm.M (IsCompatChart)

namespace SheetChartHolo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem segre_torusSmul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    segre (torusSmul c z) = (∏ k, c k) • segre z := by
  funext i
  simp [segre, torusSmul, Finset.prod_mul_distrib]

theorem coordDiv_null {n : ℕ} (S : Finset (Fin n)) : volume (coordDiv S) = 0 := by
  have hsub : coordDiv S ⊆ ⋃ i ∈ (S : Set (Fin n)),
      ((LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℝ] ℂ) : Submodule ℝ (Fin n → ℂ)) :
        Set (Fin n → ℂ)) := by
    rintro z ⟨i, hi, hz⟩
    exact Set.mem_biUnion hi (by simp [hz])
  refine measure_mono_null hsub ((measure_biUnion_null_iff S.countable_toSet).2 fun i _ => ?_)
  refine Measure.addHaar_submodule _ _ fun htop => ?_
  have : (Pi.single i (1 : ℂ) : Fin n → ℂ) ∈
      LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℝ] ℂ) := by
    rw [htop]; trivial
  simp at this

def patchMap {n : ℕ} (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {X : Type}
    [TopologicalSpace X] (ψ : OpenPartialHomeomorph X (Fin n → ℂ)) (s : X → (Σ k, ι k) → ℂ)
    (ξ : Fin n → ℂ) : Fin n → ℂ :=
  fun i => Q (segre (s (ψ.symm ξ))) i.succ / Q (segre (s (ψ.symm ξ))) 0


omit [∀ k, Fintype (ι k)] in
theorem patchMap_eq {P : Ideal (MRing ι)} {n : ℕ} (M : CxModel P n)
    (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (ψ : OpenPartialHomeomorph M.Xc (Fin n → ℂ)) (s : M.Xc → (Σ k, ι k) → ℂ)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) {x' : M.Xc} (hzx : M.proj z = x')
    (hsrc : x' ∈ ψ.source) (hs : s x' ∈ mcPts P ∧ M.proj (s x') = x') {y : Fin n → ℂ}
    (hQ : Q (segre z) = Fin.cons 1 y) :
    Q (segre (s (ψ.symm (ψ x')))) 0 ≠ 0 ∧ patchMap Q ψ s (ψ x') = y := by
  rw [ψ.left_inv hsrc]
  obtain ⟨c, -, hc⟩ := (M.fibre _ hs.1 z hz).1 (hs.2.trans hzx.symm)
  have hQ' : Q (segre z) = (∏ k, c k) • Q (segre (s x')) := by
    rw [congrArg (fun w => Q (segre w)) hc, segre_torusSmul, map_smul]
  have h0 := congrFun hQ' 0
  rw [hQ] at h0
  simp only [Fin.cons_zero, Pi.smul_apply, smul_eq_mul] at h0
  have hne : Q (segre (s x')) 0 ≠ 0 := by
    intro h
    rw [h, mul_zero] at h0
    exact one_ne_zero h0
  refine ⟨hne, funext fun i => ?_⟩
  have hi := congrFun hQ' i.succ
  rw [hQ] at hi
  simp only [Fin.cons_succ, Pi.smul_apply, smul_eq_mul] at hi
  simp only [patchMap]
  rw [ψ.left_inv hsrc, div_eq_iff hne, hi]
  linear_combination (Q (segre (s x')) i.succ) * h0

theorem patchMap_analyticAt {P : Ideal (MRing ι)} {n : ℕ} (M : CxModel P n)
    (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (ψ : OpenPartialHomeomorph M.Xc (Fin n → ℂ)) (hψ : IsCompatChart M.atlas ψ) (U : Set M.Xc)
    (s : M.Xc → (Σ k, ι k) → ℂ) (hsh : ∀ p, M.atlas.HoloOn U fun y => s y p) {ξ : Fin n → ℂ}
    (hξ : ξ ∈ ψ.target) (hU : ψ.symm ξ ∈ U) (h0 : Q (segre (s (ψ.symm ξ))) 0 ≠ 0) :
    AnalyticAt ℂ (patchMap Q ψ s) ξ := by
  classical
  have hcoord : ∀ p, AnalyticAt ℂ (fun ξ' => s (ψ.symm ξ') p) ξ := by
    intro p
    obtain ⟨i, hi⟩ := M.atlas.cover (ψ.symm ξ)
    have hg : AnalyticAt ℂ ((fun y => s y p) ∘ (M.atlas.chart i).symm)
        (M.atlas.chart i (ψ.symm ξ)) :=
      hsh p i _ ⟨(M.atlas.chart i).map_source hi, by
        rw [Set.mem_preimage, (M.atlas.chart i).left_inv hi]; exact hU⟩
    have hh : AnalyticAt ℂ (M.atlas.chart i ∘ ψ.symm) ξ := (hψ i).2 ξ ⟨hξ, hi⟩
    refine (AnalyticAt.comp (g := (fun y => s y p) ∘ (M.atlas.chart i).symm)
      (f := M.atlas.chart i ∘ ψ.symm) hg hh).congr ?_
    have hev : ∀ᶠ ξ' in 𝓝 ξ, ψ.symm ξ' ∈ (M.atlas.chart i).source :=
      (ψ.continuousAt_symm hξ).preimage_mem_nhds ((M.atlas.chart i).open_source.mem_nhds hi)
    filter_upwards [hev] with ξ' h'
    simp [Function.comp_def, (M.atlas.chart i).left_inv h']
  have hseg : AnalyticAt ℂ (fun ξ' => segre (s (ψ.symm ξ'))) ξ :=
    AnalyticAt.pi fun m => Finset.univ.analyticAt_fun_prod fun k _ => hcoord ⟨k, m k⟩
  have hQa : AnalyticAt ℂ (fun ξ' => Q (segre (s (ψ.symm ξ')))) ξ :=
    ((LinearMap.toContinuousLinearMap Q).analyticAt _).comp hseg
  have hQm : ∀ m, AnalyticAt ℂ (fun ξ' => Q (segre (s (ψ.symm ξ'))) m) ξ := fun m =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ) m).analyticAt _).comp hQa
  exact AnalyticAt.pi fun i => (hQm i.succ).div (hQm 0) h0

theorem proof : SheetChartHolo.Statement := by
  intro K _ ι _ P n M R Q
  classical

  have hpatch : ∀ x : M.Xc, ∃ (j : Fin R.N) (U : Set M.Xc) (s : M.Xc → (Σ k, ι k) → ℂ),
      IsOpen U ∧ x ∈ U ∧ x ∈ (R.chart j).source ∧ (∀ y ∈ U, s y ∈ mcPts P ∧ M.proj (s y) = y) ∧
        ∀ p, M.atlas.HoloOn U fun y => s y p := by
    intro x
    obtain ⟨j, hj⟩ := R.cover x
    obtain ⟨U, hU, hxU, s, hs, hsh⟩ := M.sections x
    exact ⟨j, U, s, hU, hxU, R.mid_subset_source j (R.inner_subset_mid j hj), hs, hsh⟩
  choose j U s hU hxU hxj hs hsh using hpatch

  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x => U x ∩ (R.chart (j x)).source)
    (fun x => (hU x).inter (R.chart (j x)).open_source)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxU x, hxj x⟩)
  let F : M.Xc → (Fin n → ℂ) → (Fin n → ℂ) := fun x => patchMap Q (R.chart (j x)) (s x)
  let V : M.Xc → Set (Fin n → ℂ) := fun x => {ξ | ξ ∈ (R.chart (j x)).target ∧
    (R.chart (j x)).symm ξ ∈ U x ∧ Q (segre (s x ((R.chart (j x)).symm ξ))) 0 ≠ 0}
  have hF : ∀ x, ∀ ξ ∈ V x, AnalyticAt ℂ (F x) ξ := fun x ξ hξ =>
    patchMap_analyticAt M Q _ (R.compat (j x)) (U x) (s x) (hsh x) hξ.1 hξ.2.1 hξ.2.2
  let f' : M.Xc → (Fin n → ℂ) → ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ)) := fun x ξ =>
    (fderiv ℂ (F x) ξ).restrictScalars ℝ
  let Crit : M.Xc → Set (Fin n → ℂ) := fun x => {ξ | ξ ∈ V x ∧ (f' x ξ).det = 0}

  let B : Set (Fin n → ℂ) :=
    ⋃ x ∈ (t : Set M.Xc), (F x '' (V x ∩ coordDiv (R.S (j x))) ∪ F x '' Crit x)
  have hB : volume B = 0 := by
    refine (measure_biUnion_null_iff t.countable_toSet).2 fun x _ => measure_union_null ?_ ?_
    · refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
        (measure_mono_null Set.inter_subset_right (coordDiv_null _))
      intro ξ hξ
      exact ((hF x ξ hξ.1).differentiableAt.restrictScalars ℝ).differentiableWithinAt
    · refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume (f' := f' x)
        (fun ξ hξ => ?_) (fun ξ hξ => hξ.2)
      exact ((hF x ξ hξ.1).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  rw [ae_iff]
  refine measure_mono_null ?_ hB
  intro y hy
  simp only [Set.mem_ofPred_eq] at hy
  by_contra hyB
  apply hy
  intro w γ hγ
  obtain ⟨-, hev⟩ := hγ
  have hev0 := hev.self_of_nhds

  obtain ⟨x, hxt, hxU', hxsrc⟩ : ∃ x ∈ t, M.proj (γ y) ∈ U x ∧
      M.proj (γ y) ∈ (R.chart (j x)).source := by
    have h := ht (Set.mem_univ (M.proj (γ y)))
    simp only [Set.mem_iUnion] at h
    obtain ⟨x, hx, h⟩ := h
    exact ⟨x, hx, h⟩
  set ψ := R.chart (j x) with hψ
  set ξ0 := ψ (M.proj (γ y)) with hξ0
  obtain ⟨hne0, hFy⟩ := patchMap_eq M Q ψ (s x) hev0.2.1 rfl hxsrc (hs x _ hxU') hev0.2.2
  have hξ0V : ξ0 ∈ V x := ⟨ψ.map_source hxsrc, by rw [ψ.left_inv hxsrc]; exact hxU', hne0⟩
  have hξ0div : ξ0 ∉ coordDiv (R.S (j x)) := fun h =>
    hyB (Set.mem_biUnion hxt (Or.inl ⟨ξ0, ⟨hξ0V, h⟩, hFy⟩))
  have hξ0crit : (f' x ξ0).det ≠ 0 := fun h =>
    hyB (Set.mem_biUnion hxt (Or.inr ⟨ξ0, ⟨hξ0V, h⟩, hFy⟩))
  have hYo : M.proj (γ y) ∈ R.Yo := (R.mem_Yo (j x) _ hxsrc).2 hξ0div
  refine ⟨j x, hxsrc, hYo, ?_⟩

  have hbij : Function.Bijective (fderiv ℂ (F x) ξ0) := by
    have hu : IsUnit (LinearMap.det ((f' x ξ0 : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)) :
        (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ))) := isUnit_iff_ne_zero.2 hξ0crit
    have h2 := (Module.End.isUnit_iff _).1 ((LinearMap.isUnit_iff_isUnit_det
      ((f' x ξ0 : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)) : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ))).2 hu)
    exact h2
  let e : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearEquiv.ofBijective (fderiv ℂ (F x) ξ0)
      (LinearMap.ker_eq_bot.2 hbij.1) (LinearMap.range_eq_top.2 hbij.2)
  have hcd : ContDiffAt ℂ 1 (F x) ξ0 := (hF x ξ0 hξ0V).contDiffAt
  have hder : HasFDerivAt (F x) (e : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) ξ0 := by
    rw [ContinuousLinearEquiv.coe_ofBijective]
    exact (hF x ξ0 hξ0V).differentiableAt.hasFDerivAt
  have hn1 : (1 : WithTop ℕ∞) ≠ 0 := one_ne_zero

  set G := hcd.localInverse hder hn1 with hGdef
  have hG : ContDiffAt ℂ 1 G y := by
    have := hcd.to_localInverse hder hn1
    have hFy' : F x ξ0 = y := hFy
    rwa [hFy'] at this
  have hleft : ∀ᶠ ξ in 𝓝 ξ0, G (F x ξ) = ξ :=
    (hcd.hasStrictFDerivAt' hder hn1).eventually_left_inverse

  have hmem : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P := hev.mono fun _ h => h.2.1
  have hpc : Tendsto (fun y' => M.proj (γ y')) (𝓝 y) (𝓝 (M.proj (γ y))) :=
    (M.cont _ hev0.2.1).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hev0.1.continuousAt, hmem⟩)
  have hsrc_ev : ∀ᶠ y' in 𝓝 y, M.proj (γ y') ∈ U x ∩ ψ.source :=
    hpc (((hU x).inter ψ.open_source).mem_nhds ⟨hxU', hxsrc⟩)
  have hφc : Tendsto (fun y' => ψ (M.proj (γ y'))) (𝓝 y) (𝓝 ξ0) :=
    (ψ.continuousAt hxsrc).tendsto.comp hpc
  have heq : ∀ᶠ y' in 𝓝 y, ψ (M.proj (γ y')) = G y' := by
    filter_upwards [hsrc_ev, hev, hφc.eventually hleft] with y' h1 h2 h3
    have h4 := (patchMap_eq M Q ψ (s x) h2.2.1 rfl h1.2 (hs x _ h1.1) h2.2.2).2
    rw [← h3]
    exact congrArg G h4
  have hGd : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ G y' :=
    (hG.eventually (by simp)).mono fun _ h => h.differentiableAt one_ne_zero
  filter_upwards [hsrc_ev, heq.eventually_nhds, hGd] with y' h1 h2 h3
  exact ⟨h1.2, h3.congr_of_eventuallyEq h2⟩

end SheetChartHolo

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
