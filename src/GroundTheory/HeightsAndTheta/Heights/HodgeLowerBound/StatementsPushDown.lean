module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherFurther
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsRegAboveWeight
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorPos
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagRatioTrdeg

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def PushDown.Statement : Prop :=
  ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
    (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D) (H : HodgeData D) (B : AdaptedBasis H),
    (∀ (G : GenFibre Pl.xV (Pl.flagPrime B))
        (J : IFamily G.Φ (fibreIdx Pl.ιY (Sum.inl : K → K ⊕ (Ψ × Fin (D.N - 1)))))
        (L : Fin (D.n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (L' : Fin (D.n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine Pl.ιY)
        (N : Fin D.flagDim0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine Pl.ιY),
        IsFieldIntersection J → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm Sum.inl Pl.xV (L j) (L' j)) →
        (∀ j, IsSmoothHerm (N j)) →
        II _ Pl.ιY (Pl.flagPrime B) (D.n + 1 + D.flagDim0) (Fin.append L' N) =
          (J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inl G) D.flagDim0 (fun j => fibreDeg Sum.inl (N j).a) : ℝ) *
            II K ι (mCoordIdeal D.y) (D.n + 1) L) ∧
    (∀ (d r : ℕ) (L : Fin d → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (L' : Fin d → ReciprocityTheory.ChartRestriction.G.Geo.HermLine Pl.ιY) (N : Fin r → ReciprocityTheory.ChartRestriction.G.Geo.HermLine Pl.ιY),
        d + r = D.n + 1 + D.flagDim0 → D.n + 1 < d → (∀ j, IsSmoothHerm (L j)) →
        (∀ j, IsPullHerm Sum.inl Pl.xV (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) →
        II _ Pl.ιY (Pl.flagPrime B) (d + r) (Fin.append L' N) = 0)

section Bot

variable {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}

end Bot

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuRegSmooth
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Metric Set

namespace MuRegSmooth

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem smoothAlong_mul {S : Set ((Σ k, ι k) → ℂ)} {f g : ((Σ k, ι k) → ℂ) → ℝ} (hf : SmoothAlong S f)
    (hg : SmoothAlong S g) : SmoothAlong S fun z => f z * g z := by
  intro z hz
  obtain ⟨U, hU, F, hF, hfF⟩ := hf z hz
  obtain ⟨V, hV, G, hG, hgG⟩ := hg z hz
  refine ⟨U ∩ V, Filter.inter_mem hU hV, fun w => F w * G w,
    (hF.mono inter_subset_left).mul (hG.mono inter_subset_right), fun w hw => ?_⟩
  show f w * g w = F w * G w
  rw [hfF w ⟨hw.1.1, hw.2⟩, hgG w ⟨hw.1.2, hw.2⟩]

theorem smoothAlong_prod {S : Set ((Σ k, ι k) → ℂ)} {α : Type} (s : Finset α)
    {f : α → ((Σ k, ι k) → ℂ) → ℝ} (hf : ∀ p ∈ s, SmoothAlong S (f p)) :
    SmoothAlong S fun z => ∏ p ∈ s, f p z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro z _
    exact ⟨univ, univ_mem, fun _ => 1, contDiffOn_const, fun w _ => by simp⟩
  | insert a s ha ih =>
    have h := smoothAlong_mul (hf a (Finset.mem_insert_self a s))
      (ih fun p hp => hf p (Finset.mem_insert_of_mem hp))
    intro z hz
    obtain ⟨U, hU, G, hG, hfG⟩ := h z hz
    exact ⟨U, hU, G, hG, fun w hw => by
      show ∏ p ∈ insert a s, f p w = G w
      rw [Finset.prod_insert ha]; exact hfG w hw⟩

theorem smoothAlong_exp {S : Set ((Σ k, ι k) → ℂ)} {f : ((Σ k, ι k) → ℂ) → ℝ} (hf : SmoothAlong S f) :
    SmoothAlong S fun z => Real.exp (f z) := by
  intro z hz
  obtain ⟨U, hU, F, hF, hfF⟩ := hf z hz
  exact ⟨U, hU, fun w => Real.exp (F w), Real.contDiff_exp.comp_contDiffOn hF,
    fun w hw => by show Real.exp (f w) = Real.exp (F w); rw [hfF w hw]⟩


omit [∀ k, Fintype (ι k)] in
theorem isOpen_blocks : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z; simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem smoothAlong_of_contDiffOn {P : Ideal (MRing ι)} {f : ((Σ k, ι k) → ℂ) → ℝ}
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) : SmoothAlong (mcPts P) f :=
  fun _ hz => ⟨_, isOpen_blocks.mem_nhds hz.1, f, hf, fun _ _ => rfl⟩

theorem regWeight_smooth {P : Ideal (MRing ι)} {d : ℕ} {M : CxModel P d} {Xo : Set ((Σ k, ι k) → ℂ)}
    {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (S : LogLogRegularisationSetting M Xo A) (hS : S.IsTied) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (S.regWeight t) := by
  have hball : ∀ j, ∃ δ : ℝ, 0 < δ ∧
      cthickening δ (S.R.chart j '' closure (S.R.mid j)) ⊆ (S.R.chart j).target := by
    intro j
    have hK : IsCompact (S.R.chart j '' closure (S.R.mid j)) :=
      isClosed_closure.isCompact.image_of_continuousOn
        ((S.R.chart j).continuousOn.mono (S.R.closure_mid j))
    have hsub : S.R.chart j '' closure (S.R.mid j) ⊆ (S.R.chart j).target :=
      image_subset_iff.2 fun x hx => (S.R.chart j).map_source (S.R.closure_mid j hx)
    exact hK.exists_cthickening_subset_open (S.R.chart j).open_target hsub
  choose δ hδ hδs using hball
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, t < δ j :=
    Filter.eventually_all.2 fun j => nhdsWithin_le_nhds (gt_mem_nhds (hδ j))
  filter_upwards [hev, hS.compare, self_mem_nhdsWithin] with t htδ hcmp ht
  have ht0 : (0 : ℝ) < t := ht
  exact (Regular.GlueRegularised.proof M.Xc d M.atlas S.R S.ρ S.η S.Cη (S.K t) t (S.e1 t) S.cutoff ht0
    (ht0.trans_le (S.e1_ge t ht0))
    (fun j x hx => ((closedBall_subset_closedBall (htδ j).le).trans
      (closedBall_subset_cthickening (mem_image_of_mem _ hx) _)).trans (hδs j)) hcmp).1

theorem prod_norm_zpow_add_sum {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (a : K → ℤ) (s : Finset ℕ) (b : ℕ → K → ℤ) :
    (∏ k, ‖c k‖ ^ (a + ∑ p ∈ s, b p) k) = (∏ k, ‖c k‖ ^ a k) * ∏ p ∈ s, ∏ k, ‖c k‖ ^ b p k := by
  rw [Finset.prod_comm, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h0 : ‖c k‖ ≠ 0 := norm_ne_zero_iff.mpr (hc k)
  have hsum : ∀ s' : Finset ℕ, ‖c k‖ ^ (∑ p ∈ s', b p k) = ∏ p ∈ s', ‖c k‖ ^ b p k := by
    intro s'
    induction s' using Finset.induction_on with
    | empty => simp
    | insert q s' hq ih => rw [Finset.sum_insert hq, Finset.prod_insert hq, zpow_add₀ h0, ih]
  rw [Pi.add_apply, Finset.sum_apply, zpow_add₀ h0, hsum]

end MuRegSmooth


open MuRegSmooth TopNPoly in
theorem MuRegSmooth.proof (hE : HermExtend.Statement) (hP : ProjSmoothAlong.Statement)
    (hVS : VertFactorSmooth.Statement) (hV : VertFactorPos.Statement) : MuRegSmooth.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B
  filter_upwards [regWeight_smooth X.S X.S_tied] with t ht
  have hPm : IsMultiHomogIdeal (mCoordIdeal D.y) := D.arith.2.1.2.1
  set F : ((Σ k, ι k) → ℂ) → ℝ := fun z =>
    X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z)) * ∏ p ∈ D.SB B, D.vertFactor p z with hFdef
  have hpos : ∀ z ∈ mcPts (mCoordIdeal D.y), 0 < F z := fun z hz =>
    mul_pos (mul_pos (X.S.ref.pos z hz.1) (Real.exp_pos _))
      (Finset.prod_pos fun p hp => hV II Ψ K ι Ω E D p (Finset.mem_filter.1 hp).1 z hz)
  have hhom : ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      F (torusSmul c z) = (∏ k, ‖c k‖ ^ muTwDeg X.H B k) * F z := by
    intro z hz c hc
    have hcz : torusSmul c z ∈ mcPts (mCoordIdeal D.y) := mcPts_smul hPm c hc hz
    have hproj : X.M.proj (torusSmul c z) = X.M.proj z :=
      ((X.M.fibre z hz _ hcz).2 ⟨c, hc, rfl⟩).symm
    have href : X.S.ref.h (torusSmul c z) = (∏ k, ‖c k‖ ^ X.H.aMu k) * X.S.ref.h z := by
      rw [show torusSmul c z = fun p => c p.1 * z p from rfl, X.S.ref.smul c z hc, X.S.ref_deg]
      rfl
    have hvf : ∏ p ∈ D.SB B, D.vertFactor p (torusSmul c z) =
        (∏ p ∈ D.SB B, ∏ k, ‖c k‖ ^ D.vdeg p k) * ∏ p ∈ D.SB B, D.vertFactor p z := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun p hp =>
        (hVS II Ψ K ι Ω E D p (Finset.mem_filter.1 hp).1).1 z hz c hc
    simp only [hFdef]
    rw [href, hproj, hvf, muTwDeg, prod_norm_zpow_add_sum hc]
    ring
  have hsm : SmoothAlong (mcPts (mCoordIdeal D.y)) F :=
    smoothAlong_mul (smoothAlong_mul (smoothAlong_of_contDiffOn X.S.ref_smooth)
      (smoothAlong_exp (hP II Ψ K ι Ω E D X.M _ ht)))
      (smoothAlong_prod _ fun p hp => (hVS II Ψ K ι Ω E D p (Finset.mem_filter.1 hp).1).2)
  obtain ⟨Z, hZa, hZs, hZh⟩ := hE K ι (mCoordIdeal D.y) (muTwDeg X.H B) F hPm hpos hhom hsm
  unfold muReg
  refine smoothRep_smooth_of (Z := Z) hZa hZs fun z hz => ?_
  obtain ⟨c, hc, hzc⟩ := exists_eq_smul_orbitRep z
  have hw0 := orbitRep_blocks hz.1
  have hwP : orbitRep z ∈ mcPts (mCoordIdeal D.y) := by
    have h := mcPts_smul hPm (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k)) hz
    convert h using 1
    funext p
    have hp : z p = c p.1 * orbitRep z p := congrFun hzc p
    rw [hp, ← mul_assoc, inv_mul_cancel₀ (hc _), one_mul]
  have hG0 : 0 < X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z))) :=
    mul_pos (X.S.ref.pos _ hw0) (Real.exp_pos _)
  have hreg : (X.S.regLine t).h (orbitRep z) =
      X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z))) :=
    hermOfFun_h_orbitRep hz.1 hG0
  have hFw : (X.S.regLine t).h (orbitRep z) * ∏ p ∈ D.SB B, D.vertFactor p (orbitRep z) = F (orbitRep z) := by
    rw [hreg]
  rw [hZh z hz, hermOfFun_h_smul hc hzc hz.1 (by rw [hFw]; exact hpos _ hwP), hFw]
  conv_lhs => rw [hzc]
  exact hhom _ hwP c hc

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PProjSmoothAlong
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open scoped ContDiff

theorem ProjSmoothAlong.proof (hO : HoloInjDerivInj.Statement) (hL : LocalOrbitChart.Statement) :
    ProjSmoothAlong.Statement := by
  intro II Ψ hΨ K hK ι hι Ω hΩ hQΩ E hE1 hE2 D M g hg z₀ hz₀
  set S := mcPts (mCoordIdeal D.y) with hS
  set x₀ := M.proj z₀ with hx₀
  obtain ⟨j, hj⟩ := M.atlas.cover x₀
  set e := M.atlas.chart j with he
  obtain ⟨W, hWo, hxW, s, hs, hsh⟩ := M.sections x₀
  obtain ⟨N, hNo, hzN, κ, hκa, hκt, hκi⟩ := hL K ι Ω D.y D.n D.arith D.smoothGeneric z₀ hz₀
  set σ : (Fin D.n → ℂ) → (Σ k, ι k) → ℂ := fun u => s (e.symm u) with hσ
  set f : (Fin D.n → ℂ) → (Fin D.n → ℂ) := fun u => κ (σ u) with hf
  set u₀ := e x₀ with hu₀
  set T := e.target ∩ e.symm ⁻¹' W with hT
  have hTo : IsOpen T := e.isOpen_inter_preimage_symm hWo
  have hσa : AnalyticOnNhd ℂ σ T := fun u hu => AnalyticAt.pi fun p => hsh p j u hu
  have hu₀t : u₀ ∈ e.target := e.map_source hj
  have hsymm₀ : e.symm u₀ = x₀ := e.left_inv hj
  have hu₀T : u₀ ∈ T := ⟨hu₀t, by simp only [Set.mem_preimage, hsymm₀]; exact hxW⟩

  have hσ₀ : σ u₀ = s x₀ := by simp only [hσ, hsymm₀]
  obtain ⟨hsx₀S, hsx₀p⟩ := hs x₀ hxW
  obtain ⟨c₀, hc₀, hc₀e⟩ := (M.fibre z₀ hz₀ (s x₀) hsx₀S).1 hsx₀p.symm
  have hsx₀N : s x₀ ∈ N := hc₀e ▸ (hκt z₀ hzN c₀ hc₀).1
  have hκs₀ : κ (s x₀) = κ z₀ := hc₀e ▸ (hκt z₀ hzN c₀ hc₀).2

  set T' := T ∩ σ ⁻¹' N with hT'
  have hT'o : IsOpen T' := hσa.continuousOn.isOpen_inter_preimage hTo hNo
  have hu₀T' : u₀ ∈ T' := ⟨hu₀T, by simp only [Set.mem_preimage, hσ₀]; exact hsx₀N⟩
  have hfa : AnalyticOnNhd ℂ f T' := fun u hu => (hκa (σ u) hu.2).comp (hσa u hu.1)
  have hinj : Set.InjOn f T' := by
    intro u hu u' hu' hfu
    obtain ⟨hmS, hmp⟩ := hs (e.symm u) hu.1.2
    obtain ⟨hmS', hmp'⟩ := hs (e.symm u') hu'.1.2
    obtain ⟨c, hc, hce⟩ := hκi (σ u) ⟨hu.2, hmS⟩ (σ u') ⟨hu'.2, hmS'⟩ hfu
    have hpe : M.proj (σ u) = M.proj (σ u') := (M.fibre (σ u) hmS (σ u') hmS').2 ⟨c, hc, hce⟩
    have h2 : e.symm u = e.symm u' := by
      simp only [hσ] at hpe
      rw [← hmp, ← hmp', hpe]
    rw [← e.right_inv hu.1.1, ← e.right_inv hu'.1.1, h2]

  have hDinj : Function.Injective (fderiv ℂ f u₀) := hO D.n f T' hT'o hfa hinj u₀ hu₀T'
  set Lc : (Fin D.n → ℂ) ≃L[ℂ] (Fin D.n → ℂ) :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℂ f u₀ : (Fin D.n → ℂ) →ₗ[ℂ] (Fin D.n → ℂ)) hDinj).toContinuousLinearEquiv
    with hLc
  have hFD : HasFDerivAt f (Lc : (Fin D.n → ℂ) →L[ℂ] (Fin D.n → ℂ)) u₀ := by
    have hcoe : (Lc : (Fin D.n → ℂ) →L[ℂ] (Fin D.n → ℂ)) = fderiv ℂ f u₀ := by
      ext v; rfl
    rw [hcoe]
    exact (hfa u₀ hu₀T').differentiableAt.hasFDerivAt
  have hcd : ContDiffAt ℂ ω f u₀ := (hfa u₀ hu₀T').contDiffAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  set linv := hcd.localInverse hFD hn with hlinv
  have hlinv_cd : ContDiffAt ℂ ω linv (f u₀) := hcd.to_localInverse hFD hn
  have hlinv₀ : linv (f u₀) = u₀ := hcd.localInverse_apply_image hFD hn
  have hleft : ∀ᶠ u in 𝓝 u₀, linv (f u) = u := (hcd.hasStrictFDerivAt' hFD hn).eventually_left_inverse
  have hfu₀ : f u₀ = κ z₀ := by simp only [hf, hσ₀, hκs₀]

  set Φ : ((Σ k, ι k) → ℂ) → (Fin D.n → ℂ) := fun z => linv (κ z) with hΦ
  have hΦcd : ContDiffAt ℂ ω Φ z₀ := by
    have h1 : ContDiffAt ℂ ω linv (κ z₀) := hfu₀ ▸ hlinv_cd
    exact h1.comp z₀ (hκa z₀ hzN).contDiffAt
  have hΦ₀ : Φ z₀ = u₀ := by simp only [hΦ, ← hfu₀, hlinv₀]
  obtain ⟨V₁, hV₁, hΦV₁⟩ := hΦcd.contDiffOn (m := ∞) le_top (fun _ => rfl)
  have hΦV₁R : ContDiffOn ℝ ∞ Φ V₁ := hΦV₁.restrict_scalars ℝ
  set V₂ := V₁ ∩ Φ ⁻¹' e.target with hV₂
  have hV₂n : V₂ ∈ 𝓝 z₀ :=
    inter_mem hV₁ (hΦcd.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds (hΦ₀ ▸ hu₀t)))
  have hgs : ContDiffOn ℝ ∞ (g ∘ e.symm) e.target := by
    have := hg j
    simpa [ReciprocityTheory.AnForm.M.FinHolAtlas.Smooth, ReciprocityTheory.AnForm.M.FinHolAtlas.SmoothOn] using this
  have hGV₂ : ContDiffOn ℝ ∞ (fun z => g (e.symm (Φ z))) V₂ :=
    hgs.comp (hΦV₁R.mono Set.inter_subset_left) (fun z hz => hz.2)

  have hcont : ContinuousWithinAt M.proj S z₀ := M.cont z₀ hz₀
  have htend : Tendsto (fun w => e (M.proj w)) (𝓝[S] z₀) (𝓝 u₀) :=
    (e.continuousAt hj).tendsto.comp hcont.tendsto
  have hev1 : ∀ᶠ w in 𝓝[S] z₀, M.proj w ∈ e.source ∩ W :=
    hcont.tendsto ((e.open_source.inter hWo).mem_nhds ⟨hj, hxW⟩)
  have hev2 : ∀ᶠ w in 𝓝[S] z₀, linv (f (e (M.proj w))) = e (M.proj w) := htend.eventually hleft
  have hev3 : ∀ᶠ w in 𝓝[S] z₀, w ∈ N := nhdsWithin_le_nhds (hNo.mem_nhds hzN)
  have hev : ∀ᶠ w in 𝓝[S] z₀, (M.proj w ∈ e.source ∩ W ∧ linv (f (e (M.proj w))) = e (M.proj w)) ∧ w ∈ N :=
    (hev1.and hev2).and hev3
  rw [eventually_nhdsWithin_iff] at hev
  refine ⟨V₂ ∩ {w | w ∈ S → (M.proj w ∈ e.source ∩ W ∧ linv (f (e (M.proj w))) = e (M.proj w)) ∧ w ∈ N},
    inter_mem hV₂n hev, fun z => g (e.symm (Φ z)), hGV₂.mono Set.inter_subset_left, ?_⟩
  rintro w ⟨⟨-, hw⟩, hwS⟩
  obtain ⟨⟨⟨hxe, hxW'⟩, hli⟩, hwN⟩ := hw hwS
  obtain ⟨hsS, hsp⟩ := hs (M.proj w) hxW'
  obtain ⟨c, hc, hce⟩ := (M.fibre w hwS (s (M.proj w)) hsS).1 hsp.symm
  have hfe : f (e (M.proj w)) = κ w := by
    simp only [hf, hσ, e.left_inv hxe]
    rw [hce]
    exact (hκt w hwN c hc).2
  have hΦw : Φ w = e (M.proj w) := by
    simp only [hΦ]
    rw [← hfe, hli]
  simp only [hΦw, e.left_inv hxe]

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StNbarLeviChart
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)

def NbarLeviChart.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B p q : ℕ) (t : ℝ),
    X.M.atlas.Smooth (X.S.regWeight t) →
    ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ w, IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal D.y) z w →
    ∀ k : Fin X.S.R.N, X.M.proj z ∈ X.S.R.mid k →
      ∃ v : Fin D.n → ℂ, IsChartVel X.M (X.S.R.chart k) z w v ∧
        levi (fun y => Real.log ((X.NbarQ B p q t).h y)) z w =
          q * levi (X.S.R.chartFun (X.S.regWeight t) k) (X.S.R.chart k (X.M.proj z)) v +
            p * levi (fun y => Real.log (D.A'.h y)) z w

section Inhabitants

namespace Line

open GroundTheory.Heights₂.Heights (CP)

end Line

end Inhabitants

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagArithVar
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter GroundTheory.Heights₂.Heights.CoordinateConeArithVar

namespace FlagArithVar

variable (Ψ : Type) (N : ℕ)

theorem yFl_eq (q : FlBlock Ψ N) (A : FlIdx Ψ N q) :
    yFl Ψ N ⟨q, A⟩ = ((genMatFr ℚ Ψ N q.1).submatrix (Fin.castLE (step_le q.2)) A.1).det := by
  rw [yFl, RingHom.map_det]
  congr 1

def leadIdx (q : FlBlock Ψ N) : FlIdx Ψ N q := ⟨Fin.castLE (step_le q.2), Fin.strictMono_castLE _⟩

theorem yFl_lead (q : FlBlock Ψ N) : yFl Ψ N ⟨q, leadIdx Ψ N q⟩ = leadMinor (genMatFr ℚ Ψ N q.1) q.2 := by
  rw [yFl_eq, leadMinor, pivotMinor]
  congr 2
  funext c
  apply Fin.ext
  have := c.isLt
  simp only [leadIdx, Fin.val_castLE, pivotCols]
  split_ifs with h
  · rfl
  · simp only [Fin.val_castLE]; omega

theorem yFl_eq_flagMinor (q : FlBlock Ψ N) (A : FlIdx Ψ N q) :
    yFl Ψ N ⟨q, A⟩ = flagMinor (genMatFr ℚ Ψ N q.1) q.2
      ⟨Finset.univ.image A.1, by rw [Finset.card_image_of_injective _ A.2.injective, Finset.card_fin]⟩ := by
  rw [yFl_eq, flagMinor]
  congr 2
  exact Finset.orderEmbOfFin_unique _ (fun x => Finset.mem_image_of_mem _ (Finset.mem_univ x)) A.2

theorem flagMinor_eq_yFl (τ : Ψ) (i : Fin (N - 1)) (S : PluckerBlocks N N i) :
    flagMinor (genMatFr ℚ Ψ N τ) i S = yFl Ψ N ⟨(τ, i), ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩⟩ := by
  rw [yFl_eq, flagMinor]

theorem coneRatios_eq : coneRatios (yFl Ψ N) (leadIdx Ψ N) = Set.range (flagMinorRatio ℚ Ψ N) := by
  ext x
  constructor
  · rintro ⟨⟨q, A⟩, rfl⟩
    refine ⟨(q.1, ⟨q.2, ⟨Finset.univ.image A.1,
      by rw [Finset.card_image_of_injective _ A.2.injective, Finset.card_fin]⟩⟩), ?_⟩
    show flagMinor _ _ _ / leadMinor _ _ = yFl Ψ N ⟨q, A⟩ / yFl Ψ N ⟨q, leadIdx Ψ N q⟩
    rw [yFl_lead, yFl_eq_flagMinor]
  · rintro ⟨⟨τ, i, S⟩, rfl⟩
    refine ⟨⟨(τ, i), ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩⟩, ?_⟩
    show yFl Ψ N _ / yFl Ψ N ⟨(τ, i), leadIdx Ψ N (τ, i)⟩ = flagMinor _ _ _ / leadMinor _ _
    rw [yFl_lead, flagMinor_eq_yFl]

theorem toSubfield_adjoin_rat {E : Type} [Field E] [Algebra ℚ E] (s : Set E) :
    (IntermediateField.adjoin ℚ s).toSubfield = Subfield.closure s := by
  rw [IntermediateField.adjoin_toSubfield]
  refine le_antisymm (Subfield.closure_le.2 (Set.union_subset ?_ Subfield.subset_closure))
    (Subfield.closure_mono Set.subset_union_right)
  rintro _ ⟨q, rfl⟩
  rw [eq_ratCast]
  exact SubfieldClass.ratCast_mem _ q

theorem trdeg_int_adjoin {E : Type} [Field E] [Algebra ℚ E] (s : Set E) :
    Algebra.trdeg ℤ (IntermediateField.adjoin ℚ s) = Algebra.trdeg ℤ (Subfield.closure s) := by
  rw [← (RingEquiv.subfieldCongr (toSubfield_adjoin_rat s)).toIntAlgEquiv.trdeg_eq]
  exact AlgEquiv.trdeg_eq (RingEquiv.refl _).toIntAlgEquiv

theorem trdeg_int_eq_rat {L : Type} [Field L] (I : Algebra ℚ L) :
    Algebra.trdeg ℤ L = @Algebra.trdeg ℚ L _ _ I := by
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic _ (nonZeroDivisors ℤ)
  have : FaithfulSMul ℤ ℚ := (faithfulSMul_iff_algebraMap_injective ℤ ℚ).mpr Int.cast_injective
  have : FaithfulSMul ℚ L := (faithfulSMul_iff_algebraMap_injective ℚ L).mpr (algebraMap ℚ L).injective
  rw [← trdeg_add_eq ℤ ℚ (A := L), trdeg_eq_zero, zero_add]

theorem trdeg_closure_of_rat {E : Type} [Field E] {iQ : Algebra ℚ E} (s : Set E) {c : Cardinal}
    (h : @Algebra.trdeg ℚ (IntermediateField.adjoin ℚ s) _ _ (IntermediateField.adjoin ℚ s).algebra' = c) :
    Algebra.trdeg ℤ (Subfield.closure s) = c := by
  rw [← trdeg_int_adjoin, trdeg_int_eq_rat (IntermediateField.adjoin ℚ s).algebra']
  exact h

end FlagArithVar


open FlagArithVar in
theorem FlagArithVar.proof : FlagArithVar.Statement := by
  intro Ψ _ _ _ N hN
  have hc : ∀ q, yFl Ψ N ⟨q, leadIdx Ψ N q⟩ ≠ 0 := fun q => by
    rw [yFl_lead]; exact GenLeadMinorNeZero.full ℚ Ψ N q.1 q.2
  have hK : Nonempty (FlBlock Ψ N) := ⟨(Classical.arbitrary Ψ, ⟨0, by omega⟩)⟩
  have hhor : IsHorizontal (PFl Ψ N) := horizontal (yFl Ψ N)
  refine ⟨hK, ⟨RingHom.ker_isPrime _, isMultiHomogIdeal (yFl Ψ N), relevant (yFl Ψ N) _ hc⟩, hhor, ?_⟩
  have htr := ConeTrdeg.full _ (FlIdx Ψ N) (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField (yFl Ψ N) (leadIdx Ψ N))
    (ratioPtL (yFl Ψ N) (leadIdx Ψ N)) (birational (yFl Ψ N) _ hc)
    (fun k ↦ ⟨leadIdx Ψ N k, fun h0 ↦ by
      have h1 := congrArg Subtype.val h0
      simp [ratioPtL, ratioPt, hc] at h1⟩)
    (by rw [mCoordIdeal_ratioPtL (yFl Ψ N) _ hc]; exact hhor)
  have hL : Algebra.trdeg ℤ (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField (yFl Ψ N) (leadIdx Ψ N)) = ((dimFl Ψ N : ℕ) : Cardinal) := by
    have h := trdeg_closure_of_rat _ (FlagRatioTrdeg.full ℚ Ψ N)
    rw [GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField, coneRatios_eq, trdeg_int_adjoin]
    exact h
  rw [mCoordIdeal_ratioPtL (yFl Ψ N) _ hc, hL] at htr
  have : (PFl Ψ N).IsPrime := RingHom.ker_isPrime _
  have hA := IntDomainDim.full (MRing (FlIdx Ψ N) ⧸ PFl Ψ N) (algebraMap_injective _ hhor)
  rw [hA]
  unfold PFl
  rw [htr, ← Nat.cast_add, Cardinal.toENat_nat]
  push_cast
  ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsModelPtsIntegrable
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm.M (IsCompatChart)

def ModelPtsIntegrable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (M : CxModel P e) (n : ℕ) (ψ : Fin n → OpenPartialHomeomorph M.Xc (Fin e → ℂ)) (L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ)
    (N : Set ((Σ k, ι k) → ℂ)) (E : Set M.Xc) (v : M.Xc → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → IsSmoothHerm L → IsPtsNull P e N →
    (∀ j, IsCompatChart M.atlas (ψ j)) → (∀ x, ∃ j, x ∈ (ψ j).source) →
    (∀ j, volume ((ψ j).target ∩ (ψ j).symm ⁻¹' E) = 0) →
    (∀ j, ∀ Q ⊆ (ψ j).target, IsCompact Q → IntegrableOn (fun y => v ((ψ j).symm y)) Q) →
    (∀ z ∈ mcPts P, z ∉ N → M.proj z ∉ E → g z = v (M.proj z)) →
      IsPtsIntegrable P (fun (_ : Fin e) z => c * Real.log (L.h z)) g

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitTTop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem ComponentSetting.mixN_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
    {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]
    (X : ComponentSetting D O Lt) (B : ℕ) (t : ℝ) : X.mixN B (D.n + 1) t = arLimFun X.H X.S B t := by
  unfold ComponentSetting.mixN arLimFun
  congr 1
  funext j
  simp [j.is_lt]

theorem StokesLimitTTop.proof (hE : TopNMixedExpand.Statement) (hM : TopNMixedLimit.Statement) :
    StokesLimitTTop.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q hII hAr hp hpq
  have hlim : ∀ k ∈ Finset.range (D.n + 2), ∃ L : ℝ, Tendsto (X.mixN B k) (𝓝[>] 0) (𝓝 L) := by
    intro k hk
    rcases Nat.lt_or_ge k (D.n + 1) with h | h
    · exact hM II Ψ K ι Ω E D O Lt X B hII hAr k (Nat.lt_succ_iff.1 h)
    · have hk' : k = D.n + 1 := le_antisymm (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) h
      subst hk'
      obtain ⟨L, hL⟩ := hAr
      exact ⟨L, hL.congr fun t => (X.mixN_top B t).symm⟩
  choose! L hL using hlim
  refine ⟨∑ k ∈ Finset.range (D.n + 2), ((D.n + 1).choose k : ℝ) * ((p : ℝ) / q) ^ (D.n + 1 - k) * L k, ?_⟩
  refine Tendsto.congr' ((hE II Ψ K ι Ω E D O Lt X B p q hII hp hpq).mono fun t ht => ht.symm) ?_
  exact tendsto_finsetSum _ fun k hk => (hL k hk).const_mul _

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StNbarSmooth
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)

def NbarSmooth.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B p q : ℕ) (t : ℝ),
    X.M.atlas.Smooth (X.S.regWeight t) → IsSmoothHerm (X.NbarQ B p q t)

section Inhabitants

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

end Inhabitants

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PBdPtsNull
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem BdPtsNull.proof (h : ParamImageNull.Statement) : BdPtsNull.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D
  classical
  refine h K ι (mCoordIdeal D.y) D.n D.nCharts (fun _ => Metric.ball 0 1)
    (fun a => {t | t ∈ Metric.ball (0 : Fin D.n → ℂ) 1 ∧ ∃ i : Fin D.n, (i : ℕ) < (D.chart a).a ∧ t i = 0})
    (fun a => (D.chart a).γ) D.Bd (fun _ => Metric.isOpen_ball) (fun _ _ ht => ht.1) ?_
    (fun a => (D.chart a).analytic) ?_
  · intro a
    refine measure_mono_null (t := ⋃ i : Fin D.n, {t : Fin D.n → ℂ | t i = 0}) ?_
      (measure_iUnion_null fun i => ?_)
    · rintro t ⟨-, i, -, hi⟩
      exact Set.mem_iUnion.2 ⟨i, hi⟩
    · rw [volume_pi]
      exact Measure.pi_hyperplane _ i 0
  · rintro z ⟨hz, -⟩
    obtain ⟨a, t, ht, c, hc, rfl⟩ := D.chart_cover z (D.bd_subset hz)
    have htb : t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1 :=
      mem_ball_zero_iff.2 (lt_of_le_of_lt ht (by norm_num))
    have hγ : (D.chart a).γ t ∈ D.Bd := by
      have h' := D.bd_torus _ hz c⁻¹ (fun k => inv_ne_zero (hc k))
      convert h' using 1
      funext p
      simp [torusSmul, hc p.1]
    exact ⟨a, t, ⟨htb, ((D.chart a).boundary t htb).1 hγ⟩, c, hc, rfl⟩

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PDivisorPreimageNull
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Set
open ReciprocityTheory.AnForm.A (coordDiv)

theorem volume_coordDiv {D : ℕ} (S : Finset (Fin D)) : volume (coordDiv S) = 0 := by
  have h : coordDiv S = ⋃ i ∈ S, (fun z : Fin D → ℂ => z i) ⁻¹' {0} := by
    ext z
    simp [coordDiv]
  rw [h]
  exact measure_iUnion_null fun i => measure_iUnion_null fun _ =>
    Measure.pi_eval_preimage_null (fun _ : Fin D => (volume : Measure ℂ)) (measure_singleton 0)

theorem DivisorPreimageNull.proof (h : ParamImageNull.Statement) : DivisorPreimageNull.Statement := by
  intro K _ ι _ P d M R
  classical
  have hloc : ∀ x : M.Xc, ∃ W : Set M.Xc, IsOpen W ∧ x ∈ W ∧ ∃ j : Fin R.N, W ⊆ (R.chart j).source ∧
      ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y ∈ W, s y ∈ mcPts P ∧ M.proj (s y) = y) ∧
        ∀ p, M.atlas.HoloOn W fun y => s y p := by
    intro x
    obtain ⟨U, hU, hxU, s, hs, hhol⟩ := M.sections x
    obtain ⟨j, hj⟩ := R.cover x
    refine ⟨U ∩ (R.chart j).source, hU.inter (R.chart j).open_source,
      ⟨hxU, R.mid_subset_source j (R.inner_subset_mid j hj)⟩, j, inter_subset_right, s,
      fun y hy => hs y hy.1, fun p i => ?_⟩
    exact (hhol p i).mono (inter_subset_inter_right _ (preimage_mono inter_subset_left))
  choose W hWo hxW j hWj s hs hhol using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hWo (fun x _ => mem_iUnion.2 ⟨x, hxW x⟩)
  let xs : Fin t.card → M.Xc := fun i => (t.equivFin.symm i : M.Xc)
  refine h K ι P d t.card (fun i => R.chart (j (xs i)) '' W (xs i))
    (fun i => R.chart (j (xs i)) '' W (xs i) ∩ coordDiv (R.S (j (xs i))))
    (fun i w => s (xs i) ((R.chart (j (xs i))).symm w)) {z | M.proj z ∉ R.Yo}
    (fun i => (R.chart (j (xs i))).isOpen_image_of_subset_source (hWo _) (hWj _))
    (fun i => inter_subset_left)
    (fun i => measure_mono_null inter_subset_right (volume_coordDiv _)) ?_ ?_
  · rintro i w ⟨y, hyW, rfl⟩
    refine analyticAt_pi_iff.2 fun p => ?_
    exact GroundTheory.Heights₂.Heights.Regular.analyticAt_comp_symm_of_holoOn (R.compat _) (hhol (xs i) p) hyW
      (hWj _ hyW)
  · rintro z ⟨hzY, hz⟩
    obtain ⟨x, hxt, hzW⟩ := mem_iUnion₂.1 (ht (mem_univ (M.proj z)))
    obtain ⟨i, rfl⟩ : ∃ i, xs i = x := ⟨t.equivFin ⟨x, hxt⟩, by simp [xs]⟩
    have hsrc := hWj (xs i) hzW
    have hdiv : R.chart (j (xs i)) (M.proj z) ∈ coordDiv (R.S (j (xs i))) := by
      by_contra hc
      exact hzY ((R.mem_Yo _ _ hsrc).2 hc)
    refine ⟨i, R.chart (j (xs i)) (M.proj z), ⟨⟨M.proj z, hzW, rfl⟩, hdiv⟩, ?_⟩
    have hγ : s (xs i) ((R.chart (j (xs i))).symm (R.chart (j (xs i)) (M.proj z))) = s (xs i) (M.proj z) := by
      rw [(R.chart (j (xs i))).left_inv hsrc]
    rw [hγ]
    obtain ⟨hsm, hsp⟩ := hs (xs i) (M.proj z) hzW
    exact (M.fibre _ hsm z hz).1 hsp

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PParamImageNull
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem ParamImageNull.segre_torusSmul {K : Type} [Fintype K] {ι : K → Type} (c : K → ℂ) (v : (Σ k, ι k) → ℂ) :
    segre (torusSmul c v) = (∏ k, c k) • segre v := by
  funext x
  simp [segre, torusSmul, Finset.prod_mul_distrib]

theorem ParamImageNull.differentiableAt_segre_comp {K : Type} [Fintype K] {ι : K → Type} {d : ℕ}
    {f : (Fin d → ℂ) → (Σ k, ι k) → ℂ} {w : Fin d → ℂ} (hf : DifferentiableAt ℂ f w) :
    DifferentiableAt ℂ (fun u => segre (f u)) w := by
  refine differentiableAt_pi.2 fun x => ?_
  simp only [segre]
  have hk : ∀ k, DifferentiableAt ℂ (fun u => f u ⟨k, x k⟩) w := fun k => differentiableAt_pi.1 hf ⟨k, x k⟩
  fun_prop

theorem ParamImageNull.proof : ParamImageNull.Statement := by
  intro K _ ι _ P d m V A γ N _hV hAV hA hγ hN Ψ _
  classical
  set G : Fin m → (Fin d → ℂ) → Fin (d + 1) → ℂ := fun i w => Ψ (segre (γ i w)) with hG
  set F : Fin m → (Fin d → ℂ) → Fin d → ℂ := fun i w l => G i w l.succ / G i w 0 with hF
  have hsub : {y : Fin d → ℂ | ∃ z ∈ mcPts P, z ∈ N ∧ Ψ (segre z) = Fin.cons 1 y} ⊆
      ⋃ i, F i '' (A i ∩ {w | G i w 0 ≠ 0}) := by
    rintro y ⟨z, hzP, hzN, hzy⟩
    obtain ⟨i, w, hw, c, hc, rfl⟩ := hN z ⟨hzN, hzP⟩
    rw [ParamImageNull.segre_torusSmul, map_smul] at hzy
    have h0 := congrFun hzy 0
    simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_zero] at h0
    have hG0 : G i w 0 ≠ 0 := by
      intro h
      rw [hG] at h
      simp only at h
      rw [h, mul_zero] at h0
      exact zero_ne_one h0
    refine Set.mem_iUnion.2 ⟨i, w, ⟨hw, hG0⟩, ?_⟩
    funext l
    have hl := congrFun hzy l.succ
    simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_succ] at hl
    simp only [hF]
    rw [div_eq_iff hG0, ← hl]
    have h0' : (∏ k, c k) * G i w 0 = 1 := h0
    calc G i w l.succ = G i w l.succ * ((∏ k, c k) * G i w 0) := by rw [h0', mul_one]
      _ = (∏ k, c k) * Ψ (segre (γ i w)) l.succ * G i w 0 := by simp only [hG]; ring
  refine measure_mono_null hsub (measure_iUnion_null fun i => ?_)
  refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
    (measure_mono_null Set.inter_subset_left (hA i))
  intro w ⟨hwA, hw0⟩
  have hγw : DifferentiableAt ℂ (γ i) w := (hγ i w (hAV i hwA)).differentiableAt
  have hGw : DifferentiableAt ℂ (G i) w :=
    (LinearMap.toContinuousLinearMap Ψ).differentiableAt.comp w (ParamImageNull.differentiableAt_segre_comp hγw)
  have hFw : DifferentiableAt ℂ (F i) w := by
    refine differentiableAt_pi.2 fun l => ?_
    show DifferentiableAt ℂ (fun u => G i u l.succ / G i u 0) w
    simp only [div_eq_mul_inv]
    exact (differentiableAt_pi.1 hGw l.succ).mul ((differentiableAt_pi.1 hGw 0).inv hw0)
  exact (hFw.restrictScalars ℝ).differentiableWithinAt

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PBoundaryPtsNull
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem segre_torusSmul {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) : segre (torusSmul c z) = (∏ k, c k) • segre z := by
  funext i
  simp [segre, torusSmul, Finset.prod_mul_distrib]

theorem volume_coord_hyperplane {m : ℕ} (i : Fin m) : volume {t : Fin m → ℂ | t i = 0} = 0 := by
  rw [volume_pi]
  exact Measure.pi_hyperplane _ i 0

theorem differentiable_segre {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    Differentiable ℂ (segre : ((Σ k, ι k) → ℂ) → ((k : K) → ι k) → ℂ) := by
  refine differentiable_pi.2 fun i => ?_
  unfold segre
  fun_prop

theorem BoundaryPtsNull.proof : BoundaryPtsNull.Statement := by
  intro II T _ _ K _ ι _ Ω _ _ E _ _ D Ψ _
  classical
  let F : Fin D.nCharts → (Fin D.n → ℂ) → Fin D.n → ℂ := fun a t j =>
    Ψ (segre ((D.chart a).γ t)) j.succ / Ψ (segre ((D.chart a).γ t)) 0
  let s : Fin D.nCharts → Fin D.n → Set (Fin D.n → ℂ) := fun a i =>
    {t | ‖t‖ < 1 ∧ t i = 0 ∧ Ψ (segre ((D.chart a).γ t)) 0 ≠ 0}
  refine measure_mono_null (t := ⋃ a, ⋃ i, F a '' s a i) ?_
    (measure_iUnion_null fun a => measure_iUnion_null fun i => ?_)
  · rintro y ⟨z, hz, hzB, hΨ⟩
    obtain ⟨a, t, ht, c, hc, rfl⟩ := D.chart_cover z hz
    have hγB : (D.chart a).γ t ∈ D.Bd := by
      have := D.bd_torus _ hzB (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k))
      convert this using 1
      funext x
      simp [torusSmul, hc]
    have ht1 : ‖t‖ < 1 := by linarith
    obtain ⟨i, -, hi⟩ := ((D.chart a).boundary t (mem_ball_zero_iff.2 ht1)).1 hγB
    rw [segre_torusSmul, map_smul] at hΨ
    have h0 := congrFun hΨ 0
    simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_zero] at h0
    have hv0 : Ψ (segre ((D.chart a).γ t)) 0 ≠ 0 := fun h => by simp [h] at h0
    refine Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨i, t, ⟨ht1, hi, hv0⟩, ?_⟩⟩
    funext j
    have hj := congrFun hΨ j.succ
    simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_succ] at hj
    show Ψ (segre ((D.chart a).γ t)) j.succ / Ψ (segre ((D.chart a).γ t)) 0 = y j
    rw [div_eq_iff hv0, ← hj]
    linear_combination (-(Ψ (segre ((D.chart a).γ t)) j.succ)) * h0
  · refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
      (measure_mono_null (fun t ht => ht.2.1) (volume_coord_hyperplane i))
    intro t ht
    have hγ : DifferentiableAt ℂ (D.chart a).γ t :=
      ((D.chart a).analytic t (mem_ball_zero_iff.2 ht.1)).differentiableAt
    have hS : DifferentiableAt ℂ (fun t => segre ((D.chart a).γ t)) t := by
      have := differentiable_segre.differentiableAt.comp t hγ
      exact this
    have hG : DifferentiableAt ℂ (fun t => Ψ (segre ((D.chart a).γ t))) t := by
      have := (LinearMap.toContinuousLinearMap Ψ).differentiableAt.comp t hS
      exact this
    have hF : DifferentiableAt ℂ (F a) t := by
      refine differentiableAt_pi.2 fun j => ?_
      have hn : DifferentiableAt ℂ (fun t => Ψ (segre ((D.chart a).γ t)) j.succ) t :=
        differentiableAt_pi.1 hG j.succ
      have hd : DifferentiableAt ℂ (fun t => Ψ (segre ((D.chart a).γ t)) 0) t :=
        differentiableAt_pi.1 hG 0
      show DifferentiableAt ℂ
        (fun t => Ψ (segre ((D.chart a).γ t)) j.succ / Ψ (segre ((D.chart a).γ t)) 0) t
      simp only [div_eq_mul_inv]
      exact hn.mul (hd.inv ht.2.2)
    exact (hF.restrictScalars ℝ).differentiableWithinAt

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsRefAlongSheet
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def RefAlongSheet.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (M : CxModel P n) (Xo : Set ((Σ k, ι k) → ℂ)) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (S : LogLogRegularisationSetting M Xo A)
    (γ : (Fin n → ℂ) → (Σ k, ι k) → ℂ) (y : Fin n → ℂ) (j : Fin S.R.N),
    (∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ γ y' ∈ mcPts P) →
    M.proj (γ y) ∈ (S.R.chart j).source →
    (∀ᶠ y' in 𝓝 y, M.proj (γ y') ∈ (S.R.chart j).source ∧
      DifferentiableAt ℂ (fun y'' => S.R.chart j (M.proj (γ y''))) y') →
    ∃ G : (Fin n → ℂ) → ℂ, AnalyticAt ℂ G y ∧ ∀ᶠ y' in 𝓝 y,
      Real.log (S.ref.h (γ y')) = S.R.q j (S.R.chart j (M.proj (γ y'))) + (G y').re

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsSheetChartHolo
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open GroundTheory.Heights₂.Heights.Regular (RegChartData)

def SheetChartHolo.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (M : CxModel P n) (R : RegChartData M.atlas) (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    ∀ᵐ y : Fin n → ℂ, ∀ (w : ((k : K) → ι k) → ℂ) (γ : (Fin n → ℂ) → (Σ k, ι k) → ℂ),
      IsSheet P Q y w γ → ∃ j : Fin R.N, M.proj (γ y) ∈ (R.chart j).source ∧ M.proj (γ y) ∈ R.Yo ∧
        ∀ᶠ y' in 𝓝 y, M.proj (γ y') ∈ (R.chart j).source ∧
          DifferentiableAt ℂ (fun y'' => R.chart j (M.proj (γ y''))) y'

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
