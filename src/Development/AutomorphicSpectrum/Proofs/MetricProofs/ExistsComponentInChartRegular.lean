module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DetMemSubring
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeI

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsComponentInChartRegular
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsComponentInChartRegular
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

open GlobalTheory.CompanionTheory.Ar.TiePrimes (dh mem_coord_iff homog_X eval₂_eq_dh_mul exists_form aeval_eq_dh_mul adjoin_eq
  mem_Wp_iff regAt_iff)

theorem exists_point_of_prime : ∀ {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K]
    {J : K → Type} [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (tie : CoordTie ℤ ξ (seg y)) (Q : Ideal (MRing J))
    (hQ : Q.IsPrime) (hle : mCoordIdeal y ≤ Q) (c : ∀ k, J k)
    (hc : ∀ k, (MvPolynomial.X ⟨k, c k⟩ : MRing J) ∉ Q),
    ∃ P : Cpt ξ, InChart ξ (seg y) c P ∧ ∀ a ∈ regAt ξ P, RegAt y Q a := by
  intro Sc Ω _ ξ K _ J _ y tie W hWp hPW c hcX
  classical
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 =>
    hcX k (hPW ((mem_coord_iff y (homog_X _)).2 (by simpa using h0)))
  have hx : seg y c ≠ 0 := GlobalTheory.CompanionTheory.Ar.TiePrimes.seg_ne hc
  haveI : IsDomain (MRing J ⧸ W) := Ideal.Quotient.isDomain W
  let F := FractionRing (MRing J ⧸ W)
  let y' : (Σ k, J k) → F := fun q => algebraMap (MRing J ⧸ W) F (Ideal.Quotient.mk W (MvPolynomial.X q))
  have ae : ∀ f : MRing J, MvPolynomial.eval₂ (Int.castRingHom F) y' f =
      algebraMap (MRing J ⧸ W) F (Ideal.Quotient.mk W f) := by
    intro f
    have e : MvPolynomial.eval₂Hom (Int.castRingHom F) y' =
        (algebraMap (MRing J ⧸ W) F).comp (Ideal.Quotient.mk W) :=
      MvPolynomial.ringHom_ext (fun a => by simp) (fun q => by simp [y'])
    exact RingHom.congr_fun e f
  have hzero : ∀ f : MRing J, MvPolynomial.eval₂ (Int.castRingHom F) y' f = 0 ↔ f ∈ W := by
    intro f
    rw [ae, map_eq_zero_iff _ (IsFractionRing.injective (MRing J ⧸ W) F), Ideal.Quotient.eq_zero_iff_mem]
  have hc' : ∀ k, y' ⟨k, c k⟩ ≠ 0 := fun k h0 => hcX k ((hzero _).1 (by simpa using h0))
  have memW : ∀ (g : MRing J) (d : K → ℕ), IsMultiHomog g d → (g ∈ W ↔ dh y' c g = 0) := by
    intro g d hg
    have h0 : (∏ k, y' ⟨k, c k⟩ ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc' k)
    rw [← hzero, eval₂_eq_dh_mul y' c hc' hg, mul_eq_zero, or_iff_left h0]
  let A := Algebra.adjoin ℤ (Set.range fun j => seg y j / seg y c)
  have hdhA : ∀ f, dh y c f ∈ A := fun f => by
    show dh y c f ∈ Algebra.adjoin ℤ _
    rw [adjoin_eq hc]
    exact ⟨f, rfl⟩
  let φ : MRing J →+* A := ((dh y c).codRestrict A hdhA : MRing J →ₐ[ℤ] A).toRingHom
  have hφ : ∀ f, ((φ f : A) : Ω) = dh y c f := fun f => rfl
  have hsurj : Function.Surjective φ := by
    rintro ⟨a, ha⟩
    have ha' : a ∈ (dh y c).range := by
      rw [← adjoin_eq hc]
      exact ha
    obtain ⟨f, rfl⟩ := ha'
    exact ⟨f, Subtype.ext rfl⟩
  let Q : Ideal (MRing J) := RingHom.ker (dh y' c : MRing J →+* F)
  haveI hQ : Q.IsPrime := RingHom.ker_isPrime _
  have hker : RingHom.ker φ ≤ Q := by
    intro f hf
    have hf0 : dh y c f = 0 := by
      rw [← hφ, RingHom.mem_ker.1 hf]
      rfl
    obtain ⟨D, G, hG, e⟩ := exists_form c f
    have e₁ : dh y c G = dh y c f := e Ω _ fun k => div_self (hc k)
    have e₂ : dh y' c G = dh y' c f := e F _ fun k => div_self (hc' k)
    have hGP : G ∈ W := hPW ((mem_coord_iff y hG).2 (by
      rw [aeval_eq_dh_mul y c hc hG, e₁, hf0, zero_mul]))
    show dh y' c f = 0
    rw [← e₂]
    exact (memW G D hG).1 hGP
  let I : Ideal A := Q.map φ
  have hI : I.IsPrime := Ideal.map_isPrime_of_surjective hsurj hker
  obtain ⟨p, ⟨hin, hunit⟩, -⟩ := GlobalTheory.T.prime_chart_existsUnique_point Sc Ω ξ ℤ _ (seg y) tie c hx I hI
  have hI' : ∀ g : MRing J, φ g ∈ I ↔ g ∈ Q := by
    intro g
    refine ⟨fun h => ?_, Ideal.mem_map_of_mem φ⟩
    obtain ⟨x, hx', e⟩ := (Ideal.mem_map_iff_of_surjective φ hsurj).1 h
    have : g - x ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker, map_sub, e, sub_self]
    have h2 := Q.add_mem (hker this) hx'
    simpa using h2
  have key : ∀ (g : MRing J) (d : K → ℕ), IsMultiHomog g d →
      (g ∈ GlobalTheory.CompanionTheory.Ar.TiePrimes.Wp tie p ↔ g ∈ W) := by
    intro g d hg
    rw [mem_Wp_iff tie hin hg, memW g d hg, ← hφ, ← hunit (φ g), not_not, hI' g]
    rfl
  refine ⟨p, hin, fun a ha => ?_⟩
  obtain ⟨d, g, h, hg, hh, hW, e⟩ := (regAt_iff tie p a).1 ha
  exact ⟨d, g, h, hg, hh, fun hm => hW ((key h d hh).2 hm), e⟩

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsComponentInChartRegularStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_component_in_chart_regular : ∀ {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K]
    {J : K → Type} [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (tie : CoordTie ℤ ξ (seg y)) (Q : Ideal (MRing J))
    (hQ : Q.IsPrime) (hle : mCoordIdeal y ≤ Q) (c : ∀ k, J k)
    (hc : ∀ k, (MvPolynomial.X ⟨k, c k⟩ : MRing J) ∉ Q),
    ∃ P : Cpt ξ, InChart ξ (seg y) c P ∧ ∀ a ∈ regAt ξ P, RegAt y Q a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.exists_point_of_prime | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.exists_point_of_prime | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.exists_point_of_prime <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.VolumeModelCritChartEqZero
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.VolumeModelCritChartEqZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Push.Crit

open MvPolynomial MeasureTheory Filter Topology Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
  GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.ModelFibreSumAlmostEverywhere

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}
  (M : CxModel P e)

theorem fib_finite (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (y : Fin e → ℂ) :
    (modelQ M Ψ ⁻¹' {y} ∩ {x | Ψ (segre (modelLift M x x)) 0 ≠ 0}).Finite := by
  refine Set.Finite.of_finite_image (f := modelW M Ψ) ((fibreFinite K ι P e Ψ hP hΨ y).subset ?_)
    ((modelW_injOn M Ψ).mono fun x hx => hx.2)
  rintro _ ⟨x, hx, rfl⟩
  have := modelW_mem_fibre M Ψ hP.1 hP.2.1.2.1 hx.2
  rwa [show modelQ M Ψ x = y from hx.1] at this

theorem psi_lift_eq {x z : M.Xc} (hz : z ∈ modelU M x)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    ∃ μ : ℂ, μ ≠ 0 ∧ Ψ (segre (modelLift M z z)) = μ • Ψ (segre (modelLift M x z)) := by
  obtain ⟨c, hc, hzc⟩ := lift_compat M hz
  exact ⟨∏ k, c k, Finset.prod_ne_zero_iff.mpr fun k _ => hc k, by rw [hzc, segre_smul, map_smul]⟩

theorem not_flat (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin M.atlas.n) {O : Set (Fin e → ℂ)}
    (hO : IsOpen O) (hOt : O ⊆ (M.atlas.chart j).target) (hne : O.Nonempty)
    (h0 : ∀ u ∈ O, Ψ (segre (modelLift M ((M.atlas.chart j).symm u) ((M.atlas.chart j).symm u))) 0 ≠ 0)
    (han : AnalyticOnNhd ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) O)
    (hdet : ∀ u ∈ O, LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) u :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0) : False := by
  obtain ⟨y, hy⟩ := exists_infinite_fibre hO hne han hdet
  refine (fib_finite M Ψ hP hΨ y).not_infinite ((Set.Infinite.image
    (Set.InjOn.mono (s₁ := O ∩ (modelQ M Ψ ∘ (M.atlas.chart j).symm) ⁻¹' {y})
      (fun u hu => hOt hu.1) (M.atlas.chart j).symm.injOn) hy).mono ?_)
  rintro _ ⟨u, ⟨huO, hqu⟩, rfl⟩
  exact ⟨hqu, h0 u huO⟩

theorem det_chart (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {x : M.Xc}
    {j k : Fin M.atlas.n} (hj : x ∈ (M.atlas.chart j).source) (hk : x ∈ (M.atlas.chart k).source)
    (h0 : Ψ (segre (modelLift M x x)) 0 ≠ 0) :
    LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (M.atlas.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) =
      LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart k).symm) (M.atlas.chart k x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) *
      LinearMap.det (fderiv ℂ (M.atlas.chart k ∘ (M.atlas.chart j).symm) (M.atlas.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := by
  set u := M.atlas.chart j x
  have hsu : (M.atlas.chart j).symm u = x := (M.atlas.chart j).left_inv hj
  set T := M.atlas.chart k ∘ (M.atlas.chart j).symm with hTdef
  have huk : u ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (M.atlas.chart k).source :=
    ⟨(M.atlas.chart j).map_source hj, by rw [mem_preimage, hsu]; exact hk⟩
  have hT : AnalyticAt ℂ T u := M.atlas.holo j k u huk
  have hTu : T u = M.atlas.chart k x := by simp only [hTdef, Function.comp_apply, hsu]
  have hQk := analyticAt_modelQ M Ψ x k hk h0
  have heq : modelQ M Ψ ∘ (M.atlas.chart j).symm =ᶠ[𝓝 u] (modelQ M Ψ ∘ (M.atlas.chart k).symm) ∘ T := by
    filter_upwards [((M.atlas.chart j).isOpen_inter_preimage_symm (M.atlas.chart k).open_source).mem_nhds
      huk] with v hv
    simp only [hTdef, Function.comp_apply, (M.atlas.chart k).left_inv hv.2]
  rw [heq.fderiv_eq, fderiv_comp u (by rw [hTu]; exact hQk.differentiableAt) hT.differentiableAt,
    hTu]
  exact LinearMap.det_comp _ _

theorem ram_null (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin M.atlas.n) :
    volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' {x | Ψ (segre (modelLift M x x)) 0 ≠ 0 ∧
      ∃ k, x ∈ (M.atlas.chart k).source ∧
        LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart k).symm) (M.atlas.chart k x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0}) = 0 := by
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, h00, -⟩
  set x0 := (M.atlas.chart j).symm u0
  set V := (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelU M x0 with hVdef
  have hV : IsOpen V := (M.atlas.chart j).isOpen_inter_preimage_symm (modelU_isOpen M x0)
  have hgc : ContinuousOn (fun u => Ψ (segre (modelLift M x0 ((M.atlas.chart j).symm u))) 0) V :=
    fun u hu => (analyticAt_pi_iff.mp (analyticAt_segre_lift M Ψ x0 j hu) 0).continuousAt.continuousWithinAt
  set O := V ∩ (fun u => Ψ (segre (modelLift M x0 ((M.atlas.chart j).symm u))) 0) ⁻¹' {0}ᶜ with hOdef
  have hO : IsOpen O := hgc.isOpen_inter_preimage hV isOpen_compl_singleton
  have hl0 : Ψ (segre (modelLift M x0 ((M.atlas.chart j).symm u0))) 0 ≠ 0 := h00
  have hu0O : u0 ∈ O := ⟨⟨hu0, mem_modelU M x0⟩, hl0⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO u0 hu0O
  have h0 : ∀ u ∈ Metric.ball u0 r,
      Ψ (segre (modelLift M ((M.atlas.chart j).symm u) ((M.atlas.chart j).symm u))) 0 ≠ 0 := by
    intro u hu
    obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq M (hball hu).1.2 Ψ
    rw [hμeq, Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hμ (hball hu).2
  have hQa : AnalyticOnNhd ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (Metric.ball u0 r) := by
    intro u hu
    have := analyticAt_modelQ M Ψ _ j ((M.atlas.chart j).map_target (hball hu).1.1) (h0 u hu)
    rwa [(M.atlas.chart j).right_inv (hball hu).1.1] at this
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, fun u => LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) u :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)), fun u hu => analyticAt_det_fderiv (hQa u hu), ?_, ?_⟩
  · by_contra hall
    push Not at hall
    exact not_flat M Ψ hP hΨ j Metric.isOpen_ball (fun u hu => (hball hu).1.1)
      ⟨u0, Metric.mem_ball_self hr⟩ h0 hQa hall
  · rintro w ⟨⟨hwt, hw0, k, hk, hdk⟩, -⟩
    have := det_chart M Ψ (j := j) ((M.atlas.chart j).map_target hwt) hk hw0
    rw [(M.atlas.chart j).right_inv hwt] at this
    show LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) w :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0
    rw [this, hdk, zero_mul]

theorem psi0_null (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin M.atlas.n) :
    volume ((M.atlas.chart j).target ∩
      (M.atlas.chart j).symm ⁻¹' {x | Ψ (segre (modelLift M x x)) 0 = 0}) = 0 := by
  classical
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, -⟩
  set x0 := (M.atlas.chart j).symm u0
  set V := (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelU M x0 with hVdef
  have hV : IsOpen V := (M.atlas.chart j).isOpen_inter_preimage_symm (modelU_isOpen M x0)
  have hu0V : u0 ∈ V := ⟨hu0, mem_modelU M x0⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV u0 hu0V
  set f : (Fin e → ℂ) → ℂ := fun u => Ψ (segre (modelLift M x0 ((M.atlas.chart j).symm u))) 0 with hfdef
  have hfa : AnalyticOnNhd ℂ f V := fun u hu =>
    analyticAt_pi_iff.mp (analyticAt_segre_lift M Ψ x0 j hu) 0
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, f, hfa.mono hball, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    have hgood := hΨ _ (lift_mem M x0)
    obtain ⟨i0, hi0⟩ : ∃ i0, Ψ (segre (modelLift M x0 x0)) i0 ≠ 0 := by
      by_contra h
      push Not at h
      exact hgood (funext h)
    have hi0ne : i0 ≠ 0 := by
      rintro rfl
      exact hi0 (hall u0 (Metric.mem_ball_self hr))
    set m : Fin e := i0.pred hi0ne
    have hm : m.succ = i0 := Fin.succ_pred i0 hi0ne
    set Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) :=
      (LinearMap.funLeft ℂ ℂ (Equiv.swap (0 : Fin (e + 1)) i0)).comp Ψ with hΨ'def
    have hΨ'app : ∀ w i, Ψ' w i = Ψ w (Equiv.swap 0 i0 i) := fun w i => rfl
    have hΨ' : IsGoodProj P Ψ' := by
      intro z hz h
      refine hΨ z hz (funext fun i => ?_)
      have := congrFun h (Equiv.swap 0 i0 i)
      rw [hΨ'app, Equiv.swap_apply_self] at this
      exact this
    have hg'c : ContinuousOn (fun u => Ψ' (segre (modelLift M x0 ((M.atlas.chart j).symm u))) 0)
        (Metric.ball u0 r) := fun u hu =>
      (analyticAt_pi_iff.mp (analyticAt_segre_lift M Ψ' x0 j (hball hu)) 0).continuousAt.continuousWithinAt
    set O := Metric.ball u0 r ∩
      (fun u => Ψ' (segre (modelLift M x0 ((M.atlas.chart j).symm u))) 0) ⁻¹' {0}ᶜ with hOdef
    have hO : IsOpen O := hg'c.isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton
    have hu0O : u0 ∈ O := by
      refine ⟨Metric.mem_ball_self hr, ?_⟩
      show Ψ' (segre (modelLift M x0 x0)) 0 ≠ 0
      rw [hΨ'app, Equiv.swap_apply_left]
      exact hi0
    have h0O : ∀ u ∈ O,
        Ψ' (segre (modelLift M ((M.atlas.chart j).symm u) ((M.atlas.chart j).symm u))) 0 ≠ 0 := by
      intro u hu
      obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq M (hball hu.1).2 Ψ'
      rw [hμeq, Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero hμ hu.2
    have hanO : AnalyticOnNhd ℂ (modelQ M Ψ' ∘ (M.atlas.chart j).symm) O := by
      intro u hu
      have := analyticAt_modelQ M Ψ' _ j ((M.atlas.chart j).map_target (hball hu.1).1) (h0O u hu)
      rwa [(M.atlas.chart j).right_inv (hball hu.1).1] at this
    have hzero : ∀ u ∈ O, (modelQ M Ψ' ∘ (M.atlas.chart j).symm) u m = 0 := by
      intro u hu
      simp only [Function.comp_apply, modelQ]
      rw [hm, hΨ'app, Equiv.swap_apply_right]
      obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq M (hball hu.1).2 Ψ
      rw [hμeq, Pi.smul_apply, smul_eq_mul]
      have : f u = 0 := hall u hu.1
      simp only [hfdef] at this
      rw [this, mul_zero, zero_div]
    have hdetO : ∀ u ∈ O, LinearMap.det (fderiv ℂ (modelQ M Ψ' ∘ (M.atlas.chart j).symm) u :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0 := by
      intro u hu
      have hcoord : (fun v => (modelQ M Ψ' ∘ (M.atlas.chart j).symm) v m) =ᶠ[𝓝 u] fun _ => 0 := by
        filter_upwards [hO.mem_nhds hu] with v hv
        exact hzero v hv
      have hd : HasFDerivAt (fun v => (modelQ M Ψ' ∘ (M.atlas.chart j).symm) v m)
          ((ContinuousLinearMap.proj m).comp (fderiv ℂ (modelQ M Ψ' ∘ (M.atlas.chart j).symm) u)) u :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) m).hasFDerivAt.comp u
          (hanO u hu).differentiableAt.hasFDerivAt
      have hd0 : HasFDerivAt (fun v => (modelQ M Ψ' ∘ (M.atlas.chart j).symm) v m)
          (0 : (Fin e → ℂ) →L[ℂ] ℂ) u :=
        (hasFDerivAt_const (0 : ℂ) u).congr_of_eventuallyEq hcoord
      have hrow := hd.unique hd0
      refine det_eq_zero_of_coord m fun v => ?_
      have := congrArg (fun T : (Fin e → ℂ) →L[ℂ] ℂ => T v) hrow
      simpa using this
    exact not_flat M Ψ' hP hΨ' j hO (fun u hu => (hball hu.1).1) ⟨u0, hu0O⟩ h0O hanO hdetO
  · rintro w ⟨⟨hwt, hw0⟩, hwb⟩
    obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq M (hball hwb).2 Ψ
    have := congrFun hμeq 0
    rw [Pi.smul_apply, smul_eq_mul] at this
    have hw0' : Ψ (segre (modelLift M ((M.atlas.chart j).symm w) ((M.atlas.chart j).symm w))) 0 = 0 := hw0
    rw [hw0'] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hμ

theorem modelCrit_null : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (n : ℕ) (M : CxModel P n) (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (j : Fin M.atlas.n),
    ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (n + 1) → IsGoodProj P Q →
      volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelCrit M Q) = 0 := by
  intro K _ ι _ P n M Q j hP hQ
  refine measure_mono_null ?_ (measure_union_null (psi0_null M Q hP hQ j) (ram_null M Q hP hQ j))
  rintro u ⟨hu, hc⟩
  by_cases h0 : Q (segre (modelLift M ((M.atlas.chart j).symm u) ((M.atlas.chart j).symm u))) 0 = 0
  · exact Or.inl ⟨hu, h0⟩
  · refine Or.inr ⟨hu, h0, ?_⟩
    rcases hc with h | ⟨k, hk, hbad⟩
    · exact absurd h h0
    · refine ⟨k, hk, ?_⟩
      by_contra hd
      exact hbad ⟨analyticAt_modelQ M Q _ k hk h0, hd⟩

end GlobalTheory.CompanionTheory.Ar.Giv.Push.Crit
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.VolumeModelCritChartEqZeroStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_modelCrit_chart_eq_zero : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (j : Fin M.atlas.n), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (n + 1) → IsGoodProj P Q → volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelCrit M Q) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Push.Crit.modelCrit_null | exact GlobalTheory.CompanionTheory.Ar.Giv.Push.Crit.modelCrit_null | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Push.Crit.modelCrit_null <;> assumption)
end
end
