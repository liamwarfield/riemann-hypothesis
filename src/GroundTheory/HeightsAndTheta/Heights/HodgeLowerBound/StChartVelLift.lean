module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PNbarSmooth

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StChartVelLift
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def ChartVelLift.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (k : Fin X.S.R.N),
    ∀ y ∈ (X.S.R.chart k).target, ∀ v : Fin D.n → ℂ, v ≠ 0 →
      ∃ z ∈ mcPts (mCoordIdeal D.y), X.M.proj z = (X.S.R.chart k).symm y ∧ ∃ w,
        IsChartVel X.M (X.S.R.chart k) z w v ∧ IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal D.y) z w ∧
          ∀ c : K → ℂ, w ≠ torusSmul c z

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelFibreFinite
section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsModelFibreFinite
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def ModelFibreFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → ∀ y, (modelQ M Ψ ⁻¹' {y} \ modelCrit M Ψ).Finite

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

theorem ModelFibreFinite.proof : ModelFibreFinite.Statement := by
  intro K _ ι _ P e M Ψ hP hΨ y
  classical
  obtain ⟨k0⟩ := hP.1
  have hH : IsMultiHomogIdeal P := hP.2.1.2.1
  let f : M.Xc → (((k : K) → ι k) → ℂ) := fun x =>
    (Ψ (segre (modelLift M x x)) 0)⁻¹ • segre (modelLift M x x)
  refine Set.Finite.of_finite_image (f := f) ((fibreFinite K ι P e Ψ hP hΨ y).subset ?_) ?_
  · rintro _ ⟨x, ⟨hxy, hx0⟩, rfl⟩
    have hq : modelQ M Ψ x = y := hxy
    have hl := (modelLift_spec M x).1 x (mem_modelU M x)
    have hlam : Ψ (segre (modelLift M x x)) 0 ≠ 0 := fun h => hx0 (Or.inl h)
    refine ⟨fun p => Function.update (1 : K → ℂ) k0 (Ψ (segre (modelLift M x x)) 0)⁻¹ p.1 *
      modelLift M x x p, mcPts_smul hH _ ?_ hl.1, ?_, ?_⟩
    · intro k
      by_cases hk : k = k0
      · subst hk
        simp [hlam]
      · simp [Function.update_of_ne hk]
    · rw [segre_smul, Finset.prod_update_of_mem (Finset.mem_univ _)]
      simp [f]
    · show Ψ ((Ψ (segre (modelLift M x x)) 0)⁻¹ • segre (modelLift M x x)) = Fin.cons 1 y
      rw [map_smul]
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [hlam]
      · rw [← hq]
        simp [modelQ, div_eq_inv_mul]
  · rintro x1 ⟨_, h1⟩ x2 ⟨_, h2⟩ heq
    have l1 := (modelLift_spec M x1).1 x1 (mem_modelU M x1)
    have l2 := (modelLift_spec M x2).1 x2 (mem_modelU M x2)
    have hlam1 : Ψ (segre (modelLift M x1 x1)) 0 ≠ 0 := fun h => h1 (Or.inl h)
    have hlam2 : Ψ (segre (modelLift M x2 x2)) 0 ≠ 0 := fun h => h2 (Or.inl h)
    have hseg : segre (modelLift M x1 x1) =
        (Ψ (segre (modelLift M x1 x1)) 0 / Ψ (segre (modelLift M x2 x2)) 0) •
          segre (modelLift M x2 x2) := by
      have := congrArg (fun w => Ψ (segre (modelLift M x1 x1)) 0 • w) heq
      simp only [f, smul_smul, mul_inv_cancel₀ hlam1, one_smul] at this
      rw [div_eq_mul_inv]
      exact this
    obtain ⟨c, hc, hcz⟩ := sameOrbit_of_segre l2.1.1 _ (div_ne_zero hlam1 hlam2) hseg
    rw [← l1.2, ← l2.2]
    exact ((M.fibre _ l2.1 _ l1.1).2 ⟨c, hc, hcz⟩).symm

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StAPrimeChartLevi
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)

def APrimeChartLevi.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (k : Fin X.S.R.N),
    ∃ Q : (Fin D.n → ℂ) → (Fin D.n → ℂ) → ℝ,
      ContinuousOn (fun p : (Fin D.n → ℂ) × (Fin D.n → ℂ) => Q p.1 p.2)
        ((X.S.R.chart k).target ×ˢ Set.univ) ∧
      ∀ z ∈ mcPts (mCoordIdeal D.y), X.M.proj z ∈ (X.S.R.chart k).source → ∀ w v,
        IsChartVel X.M (X.S.R.chart k) z w v →
          levi (fun y => Real.log (D.A'.h y)) z w = Q (X.S.R.chart k (X.M.proj z)) v

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PNbarChartSemipos
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)

theorem NbarChartSemipos.proof (hS : NbarSmooth.Statement) (hL : NbarLeviChart.Statement)
    (hA : APrimeChartMargin.Statement) : NbarChartSemipos.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X
  obtain ⟨c, hc, hAc⟩ := hA II Ψ K ι Ω E D O Lt X
  refine ⟨c, hc, fun B p q t δ hs hl hqp => ⟨hS II Ψ K ι Ω E D O Lt X B p q t hs, fun z hz w hw => ?_⟩⟩
  obtain ⟨k, hk⟩ := X.S.R.cover (X.M.proj z)
  have hk' : X.M.proj z ∈ X.S.R.mid k := X.S.R.inner_subset_mid k hk
  obtain ⟨v, hv, heq⟩ := hL II Ψ K ι Ω E D O Lt X B p q t hs z hz w hw k hk'
  have h1 := hl k _ hk' v
  have h2 := hAc z hz w k hk' v hv
  show 0 ≤ levi _ z w
  rw [heq]
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hv2 : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h1 hq, mul_le_mul_of_nonneg_left h2 hp,
    mul_le_mul_of_nonneg_right hqp hv2]

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PProjHoloLocal
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem holoOn_comp_compatChart_symm {d : ℕ} {X : Type} [TopologicalSpace X]
    {A : ReciprocityTheory.AnForm.M.FinHolAtlas d X} {e : OpenPartialHomeomorph X (Fin d → ℂ)}
    (he : ReciprocityTheory.AnForm.M.IsCompatChart A e) {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g)
    {u : Fin d → ℂ} (hu : u ∈ e.target) (huU : e.symm u ∈ U) :
    DifferentiableAt ℂ (g ∘ e.symm) u := by
  obtain ⟨j, hj⟩ := A.cover (e.symm u)
  have h1 : AnalyticAt ℂ (A.chart j ∘ e.symm) u := (he j).2 u ⟨hu, hj⟩
  have h2 : AnalyticAt ℂ (g ∘ (A.chart j).symm) ((A.chart j ∘ e.symm) u) := by
    refine hg j _ ⟨(A.chart j).map_source hj, ?_⟩
    show (A.chart j).symm (A.chart j (e.symm u)) ∈ U
    rw [(A.chart j).left_inv hj]
    exact huU
  have h3 : g ∘ e.symm =ᶠ[𝓝 u] (g ∘ (A.chart j).symm) ∘ (A.chart j ∘ e.symm) := by
    have : ∀ᶠ u' in 𝓝 u, e.symm u' ∈ (A.chart j).source :=
      (e.continuousAt_symm hu).preimage_mem_nhds ((A.chart j).open_source.mem_nhds hj)
    filter_upwards [this] with u' hu'
    simp only [Function.comp, (A.chart j).left_inv hu']
  exact (h2.comp h1).differentiableAt.congr_of_eventuallyEq h3

theorem ProjHoloLocal.proof (hL : LocalOrbitChart.Statement)
    (hO : IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse.Statement) : ProjHoloLocal.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D M e he z hz hze

  obtain ⟨N, hNo, hzN, κ, hκ, hκt, hκs⟩ := hL K ι Ω D.y D.n D.arith D.smoothGeneric z hz

  obtain ⟨U, hUo, hxU, s, hs, hsh⟩ := M.sections (M.proj z)
  obtain ⟨c, hc, hcz⟩ := (M.fibre z hz _ (hs _ hxU).1).1 (hs _ hxU).2.symm
  have hsxN : s (M.proj z) ∈ N := by rw [hcz]; exact (hκt z hzN c hc).1
  have hκsx : κ (s (M.proj z)) = κ z := by rw [hcz]; exact (hκt z hzN c hc).2
  have hsd : ∀ u ∈ e.target, e.symm u ∈ U → DifferentiableAt ℂ (s ∘ e.symm) u := fun u hu huU =>
    differentiableAt_pi.2 fun p => holoOn_comp_compatChart_symm he (hsh p) hu huU

  have hex : e (M.proj z) ∈ e.target := e.map_source hze
  have hexU : e.symm (e (M.proj z)) ∈ U := by rw [e.left_inv hze]; exact hxU
  have hTn : e.target ∩ e.symm ⁻¹' U ∩ (s ∘ e.symm) ⁻¹' N ∈ 𝓝 (e (M.proj z)) := by
    refine Filter.inter_mem (Filter.inter_mem (e.open_target.mem_nhds hex) ?_) ?_
    · exact (e.continuousAt_symm hex).preimage_mem_nhds (hUo.mem_nhds hexU)
    · refine (hsd _ hex hexU).continuousAt.preimage_mem_nhds (hNo.mem_nhds ?_)
      show s (e.symm (e (M.proj z))) ∈ N
      rw [e.left_inv hze]
      exact hsxN
  obtain ⟨T, hTsub, hTo, hxT⟩ := mem_nhds_iff.1 hTn
  have hψd : DifferentiableOn ℂ (κ ∘ s ∘ e.symm) T := fun u hu =>
    ((hκ _ (hTsub hu).2).differentiableAt.comp u
      (hsd u (hTsub hu).1.1 (hTsub hu).1.2)).differentiableWithinAt
  have hψi : Set.InjOn (κ ∘ s ∘ e.symm) T := by
    intro u hu u' hu' h
    have h1 := hs _ (hTsub hu).1.2
    have h2 := hs _ (hTsub hu').1.2
    obtain ⟨c', hc', hcc⟩ := hκs _ ⟨(hTsub hu).2, h1.1⟩ _ ⟨(hTsub hu').2, h2.1⟩ h
    have hp : M.proj (s (e.symm u)) = M.proj (s (e.symm u')) :=
      (M.fibre _ h1.1 _ h2.1).2 ⟨c', hc', hcc⟩
    rw [h1.2, h2.2] at hp
    exact e.symm.injOn (hTsub hu).1.1 (hTsub hu').1.1 hp

  obtain ⟨hψo, g, hg, hgψ⟩ := hO D.n T (κ ∘ s ∘ e.symm) hTo hψd hψi

  obtain ⟨O, hOo, hOeq⟩ :=
    continuousOn_iff'.1 M.cont (e.source ∩ e ⁻¹' T) (e.isOpen_inter_preimage hTo)
  refine ⟨O ∩ (N ∩ κ ⁻¹' ((κ ∘ s ∘ e.symm) '' T)),
    hOo.inter (hκ.continuousOn.isOpen_inter_preimage hNo hψo), ?_, g ∘ κ, ?_, ?_⟩
  · refine ⟨?_, hzN, e (M.proj z), hxT, ?_⟩
    · have hz' : z ∈ M.proj ⁻¹' (e.source ∩ e ⁻¹' T) ∩ mcPts (mCoordIdeal D.y) := ⟨⟨hze, hxT⟩, hz⟩
      rw [hOeq] at hz'
      exact hz'.1
    · show κ (s (e.symm (e (M.proj z)))) = κ z
      rw [e.left_inv hze]
      exact hκsx
  · intro w hw
    exact ((hg.differentiableAt (hψo.mem_nhds hw.2.2)).comp w
      (hκ w hw.2.1).differentiableAt).differentiableWithinAt
  · rintro z' ⟨⟨hz'O, hz'N, -⟩, hz'⟩
    have hp : z' ∈ M.proj ⁻¹' (e.source ∩ e ⁻¹' T) ∩ mcPts (mCoordIdeal D.y) := by
      rw [hOeq]
      exact ⟨hz'O, hz'⟩
    obtain ⟨⟨hpe, hpT⟩, -⟩ := hp
    refine ⟨hpe, ?_⟩
    have hpU : M.proj z' ∈ U := by
      have h := (hTsub hpT).1.2
      rwa [Set.mem_preimage, e.left_inv hpe] at h
    obtain ⟨c', hc', hcc⟩ := (M.fibre z' hz' _ (hs _ hpU).1).1 (hs _ hpU).2.symm
    have hκ' : κ (s (M.proj z')) = κ z' := by rw [hcc]; exact (hκt z' hz'N c' hc').2
    have hψz : (κ ∘ s ∘ e.symm) (e (M.proj z')) = κ z' := by
      show κ (s (e.symm (e (M.proj z')))) = κ z'
      rw [e.left_inv hpe]
      exact hκ'
    show e (M.proj z') = g (κ z')
    rw [← hψz, hgψ _ hpT]

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelFibreSumAeFibres
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

namespace ModelFibreSumAlmostEverywhere

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}
  (M : CxModel P e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

theorem lift_mem (x : M.Xc) : modelLift M x x ∈ mcPts P :=
  ((modelLift_spec M x).1 x (mem_modelU M x)).1

theorem proj_lift (x : M.Xc) : M.proj (modelLift M x x) = x :=
  ((modelLift_spec M x).1 x (mem_modelU M x)).2

theorem lift_compat {x z : M.Xc} (hz : z ∈ modelU M x) :
    ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ modelLift M z z = fun p => c p.1 * modelLift M x z p := by
  have h1 := (modelLift_spec M x).1 z hz
  obtain ⟨c, hc, h⟩ := (M.fibre _ h1.1 _ (lift_mem M z)).mp (h1.2.trans (proj_lift M z).symm)
  exact ⟨c, hc, h⟩

theorem proj_eq_of_segre {x : M.Xc} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) (μ : ℂ) (hμ : μ ≠ 0)
    (h : segre z = μ • segre (modelLift M x x)) : M.proj z = x := by
  obtain ⟨c, hc, hzc⟩ := sameOrbit_of_segre (lift_mem M x).1 μ hμ h
  have := (M.fibre _ (lift_mem M x) _ hz).mpr ⟨c, hc, hzc⟩
  rw [← this, proj_lift]

theorem modelQ_eq_local {x z : M.Xc} (hz : z ∈ modelU M x) :
    modelQ M Ψ z = fun i => Ψ (segre (modelLift M x z)) i.succ / Ψ (segre (modelLift M x z)) 0 := by
  obtain ⟨c, hc, hzc⟩ := lift_compat M hz
  have hpc : ∏ k, c k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  funext i
  simp only [modelQ, hzc, segre_smul, map_smul, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hpc

theorem analyticAt_lift_chart (x : M.Xc) (j : Fin M.atlas.n) {u : Fin e → ℂ}
    (hu : u ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelU M x) :
    AnalyticAt ℂ (fun v => modelLift M x ((M.atlas.chart j).symm v)) u :=
  analyticAt_pi_iff.mpr fun p => (modelLift_spec M x).2 p j u hu

theorem analyticAt_segre_lift (x : M.Xc) (j : Fin M.atlas.n) {u : Fin e → ℂ}
    (hu : u ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelU M x) :
    AnalyticAt ℂ (fun v => Ψ (segre (modelLift M x ((M.atlas.chart j).symm v)))) u := by
  classical
  have hl := analyticAt_lift_chart M x j hu
  have hs : AnalyticAt ℂ (fun v => segre (modelLift M x ((M.atlas.chart j).symm v))) u := by
    refine analyticAt_pi_iff.mpr fun i => ?_
    simp only [segre]
    exact Finset.analyticAt_fun_prod _ fun k _ => analyticAt_pi_iff.mp hl _
  exact (LinearMap.toContinuousLinearMap Ψ).analyticAt _ |>.comp hs

theorem analyticAt_modelQ (x : M.Xc) (j : Fin M.atlas.n) (hj : x ∈ (M.atlas.chart j).source)
    (h0 : Ψ (segre (modelLift M x x)) 0 ≠ 0) :
    AnalyticAt ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (M.atlas.chart j x) := by
  set u := M.atlas.chart j x
  have hsu : (M.atlas.chart j).symm u = x := (M.atlas.chart j).left_inv hj
  have hu : u ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelU M x :=
    ⟨(M.atlas.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact mem_modelU M x⟩
  have hH := analyticAt_segre_lift M Ψ x j hu
  have hH0 : AnalyticAt ℂ (fun v => Ψ (segre (modelLift M x ((M.atlas.chart j).symm v))) 0) u :=
    analyticAt_pi_iff.mp hH 0
  have hne : Ψ (segre (modelLift M x ((M.atlas.chart j).symm u))) 0 ≠ 0 := by rw [hsu]; exact h0
  have hF : AnalyticAt ℂ (fun v => fun i : Fin e =>
      Ψ (segre (modelLift M x ((M.atlas.chart j).symm v))) i.succ /
        Ψ (segre (modelLift M x ((M.atlas.chart j).symm v))) 0) u :=
    analyticAt_pi_iff.mpr fun i => (analyticAt_pi_iff.mp hH i.succ).div hH0 hne
  refine hF.congr ?_
  filter_upwards [((M.atlas.chart j).isOpen_inter_preimage_symm (modelU_isOpen M x)).mem_nhds hu,
    hH0.continuousAt.eventually_ne hne] with v hv hv0
  exact (modelQ_eq_local M Ψ hv.2).symm

theorem psi_zero_ne_of_not_mem_bad {E : Set M.Xc} {x : M.Xc} (hx : x ∉ modelBad M Ψ E) :
    Ψ (segre (modelLift M x x)) 0 ≠ 0 :=
  fun h => hx (Or.inr (Or.inl h))

theorem notMem_of_notMem_bad {E : Set M.Xc} {x : M.Xc} (hx : x ∉ modelBad M Ψ E) : x ∉ E :=
  fun h => hx (Or.inl h)

def modelW (x : M.Xc) : ((k : K) → ι k) → ℂ :=
  (Ψ (segre (modelLift M x x)) 0)⁻¹ • segre (modelLift M x x)

theorem modelW_mem_fibre (hK : Nonempty K) (hPh : IsMultiHomogIdeal P) {x : M.Xc}
    (h0 : Ψ (segre (modelLift M x x)) 0 ≠ 0) : modelW M Ψ x ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ (modelQ M Ψ x) := by
  classical
  obtain ⟨k0⟩ := hK
  let c : K → ℂ := Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre (modelLift M x x)) 0)⁻¹
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [c, h0]
    · simp [c, Function.update_of_ne hk]
  have hpc : ∏ k, c k = (Ψ (segre (modelLift M x x)) 0)⁻¹ := by
    simp [c, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  refine ⟨fun p => c p.1 * modelLift M x x p, mcPts_smul hPh c hc (lift_mem M x), ?_, ?_⟩
  · rw [segre_smul, hpc]; rfl
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [modelW, h0]
    · simp only [modelW, map_smul, Pi.smul_apply, smul_eq_mul, Fin.cons_succ, modelQ]
      rw [div_eq_inv_mul]

theorem modelW_injOn : Set.InjOn (modelW M Ψ) {x | Ψ (segre (modelLift M x x)) 0 ≠ 0} := by
  intro x hx x' hx' hw
  have h := congrArg (fun v => Ψ (segre (modelLift M x x)) 0 • v) hw
  simp only [modelW, smul_smul, mul_inv_cancel₀ (show Ψ (segre (modelLift M x x)) 0 ≠ 0 from hx),
    one_smul] at h
  have := proj_eq_of_segre M (lift_mem M x)
    (Ψ (segre (modelLift M x x)) 0 * (Ψ (segre (modelLift M x' x')) 0)⁻¹)
    (by simp [show Ψ (segre (modelLift M x x)) 0 ≠ 0 from hx,
      show Ψ (segre (modelLift M x' x')) 0 ≠ 0 from hx']) h
  rw [proj_lift] at this
  exact this

theorem mem_fibre_data {y : Fin e → ℂ} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P)
    (hΨz : Ψ (segre z) = Fin.cons 1 y) :
    Ψ (segre (modelLift M (M.proj z) (M.proj z))) 0 ≠ 0 ∧ modelQ M Ψ (M.proj z) = y ∧
      modelW M Ψ (M.proj z) = segre z := by
  obtain ⟨c, hc, hxc⟩ := (M.fibre _ hz _ (lift_mem M (M.proj z))).mp (proj_lift M _).symm
  have hseg : segre (modelLift M (M.proj z) (M.proj z)) = (∏ k, c k) • segre z := by
    rw [hxc]; exact segre_smul c z
  have hpc : ∏ k, c k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hΨx : Ψ (segre (modelLift M (M.proj z) (M.proj z))) = (∏ k, c k) • Fin.cons 1 y := by
    rw [hseg, map_smul, hΨz]
  have h0 : Ψ (segre (modelLift M (M.proj z) (M.proj z))) 0 = ∏ k, c k := by simp [hΨx]
  refine ⟨by rw [h0]; exact hpc, ?_, ?_⟩
  · funext i
    simp only [modelQ, hΨx, h0, Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
    field_simp
  · rw [modelW, h0, hseg, smul_smul, inv_mul_cancel₀ hpc, one_smul]

theorem image_bad_null {E : Set M.Xc}
    (hE : ∀ j, volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' E) = 0) :
    volume (modelQ M Ψ '' (modelBad M Ψ E ∩ {x | Ψ (segre (modelLift M x x)) 0 ≠ 0})) = 0 := by
  set A := M.atlas
  set G : Set M.Xc := {x | Ψ (segre (modelLift M x x)) 0 ≠ 0}
  set D : Fin A.n → Set (Fin e → ℂ) := fun j => {u | u ∈ (A.chart j).target ∧
    (A.chart j).symm u ∈ G ∧ ¬ (AnalyticAt ℂ (modelQ M Ψ ∘ (A.chart j).symm) u ∧
      LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (A.chart j).symm) u :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)}
  have han : ∀ j, ∀ u ∈ (A.chart j).target, (A.chart j).symm u ∈ G →
      AnalyticAt ℂ (modelQ M Ψ ∘ (A.chart j).symm) u := by
    intro j u hu hG
    have := analyticAt_modelQ M Ψ _ j ((A.chart j).map_target hu) hG
    rwa [(A.chart j).right_inv hu] at this
  have hsub : modelQ M Ψ '' (modelBad M Ψ E ∩ G) ⊆
      (⋃ j, (modelQ M Ψ ∘ (A.chart j).symm) ''
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (E ∩ G))) ∪
      ⋃ j, (modelQ M Ψ ∘ (A.chart j).symm) '' D j := by
    rintro _ ⟨x, ⟨hxb, hxG⟩, rfl⟩
    rcases hxb with hxE | hxc
    · obtain ⟨j, hj⟩ := A.cover x
      refine Or.inl (Set.mem_iUnion.mpr ⟨j, A.chart j x, ⟨(A.chart j).map_source hj, ?_⟩, ?_⟩)
      · rw [Set.mem_preimage, (A.chart j).left_inv hj]; exact ⟨hxE, hxG⟩
      · simp [(A.chart j).left_inv hj]
    · rcases hxc with h0 | ⟨j, hj, hbad⟩
      · exact absurd h0 hxG
      · refine Or.inr (Set.mem_iUnion.mpr ⟨j, A.chart j x, ⟨(A.chart j).map_source hj, ?_, hbad⟩, ?_⟩)
        · show (A.chart j).symm (A.chart j x) ∈ G
          rw [(A.chart j).left_inv hj]; exact hxG
        · simp [(A.chart j).left_inv hj]
  refine measure_mono_null hsub (measure_union_null (measure_iUnion_null fun j => ?_)
    (measure_iUnion_null fun j => ?_))
  · refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
      (measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left))
        (hE j))
    intro u hu
    exact ((han j u hu.1 hu.2.2).differentiableAt.restrictScalars ℝ).differentiableWithinAt
  · refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun u => (fderiv ℂ (modelQ M Ψ ∘ (A.chart j).symm) u).restrictScalars ℝ) ?_ ?_
    · intro u hu
      exact ((han j u hu.1 hu.2.1).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    · intro u hu
      have h0 : LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (A.chart j).symm) u :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0 := by
        by_contra h
        exact hu.2.2 ⟨han j u hu.1 hu.2.1, h⟩
      have := abs_det_restrictScalars (fderiv ℂ (modelQ M Ψ ∘ (A.chart j).symm) u)
      rw [h0, norm_zero, zero_pow two_ne_zero, abs_eq_zero] at this
      exact this

end ModelFibreSumAlmostEverywhere

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
