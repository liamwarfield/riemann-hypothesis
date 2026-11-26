module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.MainEq
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousSecondCayleyBlockMap

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.VacLin
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Atop

open PositivityTheory.SiegelWeilFormula.KMain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cosetSum_const_mul {G : Type} [Group G] (Pp Γ : Subgroup G) (a : ℂ) (f : G → ℂ) (g : G) :
    GlobalTheory.Eis.cosetSum Pp Γ (fun y => a * f y) g = a * GlobalTheory.Eis.cosetSum Pp Γ f g := by
  simp only [GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term]
  exact tsum_mul_left

theorem ident_lincomb (hT : TAll) (hSK : SecK) (hEW : EisWk) (d : SD σ) (c : ℂ) {k : ℕ} (a : Fin k → ℂ)
    (Ψ : Fin k → d.Fn) (hK : ∀ i, d.KFin (Ψ i))
    (hI : ∀ i x, HolValueAt (fun z => d.eis (d.sec0 (Ψ i)) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I (Ψ i) x))
    (x : d.G) :
    HolValueAt (fun z => d.eis (d.sec0 (∑ i, a i • Ψ i)) (s0 d.m d.n) z x) (s0 d.m d.n)
      (c * d.I (∑ i, a i • Ψ i) x) := by
  have hsch : ∀ i, a i • Ψ i ∈ d.sch := fun i => d.sch.smul_mem _ (hK i).1
  have hv : d.I (∑ i, a i • Ψ i) x = ∑ i, a i * d.I (Ψ i) x := by
    rw [I_sum d hT.2.2.2.1 hT.2.2.2.2 Finset.univ _ (fun i _ => hsch i), Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [I_smul d hT.2.2.2.1 (a i) (hK i).1]
    rfl
  have key : ∀ i, HolValueAt (fun z => a i * d.eis (d.sec0 (Ψ i)) (s0 d.m d.n) z x) (s0 d.m d.n)
      (a i * (c * d.I (Ψ i) x)) := fun i => (holValueAt_const (a i) _).mul (hI i x)
  have hconv : ∀ i, ∃ t : ℝ, ∀ z : ℂ, t < z.re → GlobalTheory.Eis.CosetConv (par2 σ d.Y) (rat2 σ d.Y)
      (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 (Ψ i) y) x := by
    intro i
    obtain ⟨U, pp, Ê, t, -, -, -, -, -, -, -, hc⟩ := eisAll_of hSK hEW d _ (hK i) (s0 d.m d.n)
    refine ⟨t, fun z hz => ?_⟩
    obtain ⟨u, hu, hle⟩ := (hc z hz).1 {x} isCompact_singleton
    exact Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => hle x rfl q) hu
  choose tt htt using hconv
  have hsec : d.sec0 (∑ i, a i • Ψ i) = fun y => ∑ i, a i * d.sec0 (Ψ i) y := by
    funext y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← secl_apply, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    rfl
  have heq : EqRight (fun z => ∑ i, a i * d.eis (d.sec0 (Ψ i)) (s0 d.m d.n) z x)
      (fun z => d.eis (d.sec0 (∑ i, a i • Ψ i)) (s0 d.m d.n) z x) := by
    refine ⟨∑ i, |tt i|, fun z hz => ?_⟩
    have hz' : ∀ i, tt i < z.re := fun i =>
      lt_of_le_of_lt ((le_abs_self _).trans
        (Finset.single_le_sum (fun j _ => abs_nonneg (tt j)) (Finset.mem_univ i))) hz
    have hc' : ∀ i ∈ Finset.univ, GlobalTheory.Eis.CosetConv (par2 σ d.Y) (rat2 σ d.Y)
        (fun y => a i * (((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 (Ψ i) y)) x := fun i _ =>
      (htt i z (hz' i)).of_norm_le (C := ‖a i‖) fun y => (norm_mul _ _).le
    have := cosetSum_finsum (par2 σ d.Y) (rat2 σ d.Y) Finset.univ
      (fun i y => a i * (((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 (Ψ i) y)) x hc'
    show ∑ i, a i * d.eis (d.sec0 (Ψ i)) (s0 d.m d.n) z x = d.eis (d.sec0 (∑ i, a i • Ψ i)) (s0 d.m d.n) z x
    rw [hsec]
    unfold SD.eis
    have e2 : (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * ∑ i, a i * d.sec0 (Ψ i) y) =
        fun y => ∑ i, a i * (((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 (Ψ i) y) := by
      funext y
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e2, this]
    exact Finset.sum_congr rfl fun i _ => (cosetSum_const_mul _ _ _ _ _).symm
  have hval : c * d.I (∑ i, a i • Ψ i) x = ∑ i, a i * (c * d.I (Ψ i) x) := by
    rw [hv, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hval]
  exact (holValueAt_finsum Finset.univ fun i _ => key i).congr heq

end PositivityTheory.SiegelWeilFormula.Atop

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.VacCore
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.VacDataOf
noncomputable section

open Set Filter Topology GlobalTheory.Cont

namespace PositivityTheory.SiegelWeilFormula.Atop

theorem vacData_of {G : Type} [TopologicalSpace G] (h : ℂ → G → ℂ) (s₀ : ℂ) (v : G → ℂ)
    (U : Set ℂ) (p : Polynomial ℂ) (Ê : ℂ → G → ℂ) (t : ℝ) (hU : IsOpen U) (hR : IsRightDomain U) (hs : s₀ ∈ U)
    (hp : p ≠ 0) (hd : ∀ g, DifferentiableOn ℂ (Ê · g) U)
    (hc : ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ))
    (he : ∀ z : ℂ, t < z.re → ∀ g, Ê z g = p.eval z * h z g) (hv : ∀ g, HolValueAt (h · g) s₀ (v g)) :
    ∃ (r : ℝ) (F : ℂ → G → ℂ), 0 < r ∧ ContinuousOn (fun y : ℂ × G => F y.1 y.2) (Metric.ball s₀ r ×ˢ Set.univ) ∧
      (∀ g, DifferentiableOn ℂ (F · g) (Metric.ball s₀ r)) ∧ (∀ g, F s₀ g = v g) ∧
      ∀ g, ∀ z ∈ Metric.ball s₀ r, HolValueAt (h · g) z (F z g) := by
  classical

  set S := p.roots.toFinset with hS
  have hroot : ∀ z, p.eval z = 0 → z ∈ S := fun z hz => by
    rw [hS, Multiset.mem_toFinset, Polynomial.mem_roots hp]; exact hz
  set σ₁ : ℝ := |t| + ∑ a ∈ S, |a.re| with hσ₁
  have hright : ∀ z : ℂ, σ₁ < z.re → t < z.re ∧ p.eval z ≠ 0 := by
    intro z hz
    have h0 : 0 ≤ ∑ a ∈ S, |a.re| := Finset.sum_nonneg fun a _ => abs_nonneg _
    have ht := le_abs_self t
    refine ⟨by linarith, fun h0' => ?_⟩
    have hz' : |z.re| ≤ ∑ a ∈ S, |a.re| :=
      Finset.single_le_sum (f := fun a : ℂ => |a.re|) (fun a _ => abs_nonneg _) (hroot z h0')
    have := le_abs_self z.re
    linarith [abs_nonneg t]

  set Q : ℂ → G → ℂ := fun z g => Ê z g / p.eval z with hQ
  have hpan : ∀ z, AnalyticAt ℂ (fun z => p.eval z) z := fun z => p.differentiable.analyticAt z
  have hmer : ∀ g, IsMerExt (h · g) U (Q · g) := by
    intro g
    refine ⟨hR, fun z hz => ?_, ⟨σ₁, fun z hz => ?_⟩⟩
    · exact (((hd g).analyticAt (hU.mem_nhds hz)).meromorphicAt).div (hpan z).meromorphicAt
    · obtain ⟨h1, h2⟩ := hright z hz
      show Ê z g / p.eval z = h z g
      rw [he z h1 g, mul_div_cancel_left₀ _ h2]
  have hext : ∀ g z, z ∈ U → IsExtAt (h · g) z (Q · g) := fun g z hz => ⟨U, hz, hmer g⟩
  have htend : ∀ g, Tendsto (Q · g) (𝓝[≠] s₀) (𝓝 (v g)) := fun g => (hext g s₀ hs).holValueAt_iff.1 (hv g)

  have hnhds : U ∩ ((((S.erase s₀ : Finset ℂ) : Set ℂ))ᶜ) ∈ 𝓝 s₀ :=
    Filter.inter_mem (hU.mem_nhds hs) ((Finset.finite_toSet _).isClosed.isOpen_compl.mem_nhds (by simp))
  obtain ⟨r₁, hr₁, hball⟩ := Metric.mem_nhds_iff.1 hnhds
  have hbU : ∀ z ∈ Metric.ball s₀ r₁, z ∈ U := fun z hz => (hball hz).1
  have hbp : ∀ z ∈ Metric.ball s₀ r₁, z ≠ s₀ → p.eval z ≠ 0 := fun z hz hne h0 =>
    (hball hz).2 (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hne, hroot z h0⟩))
  have hQd : ∀ g, ∀ z ∈ Metric.ball s₀ r₁, z ≠ s₀ → DifferentiableAt ℂ (Q · g) z := fun g z hz hne =>
    ((hd g).differentiableAt (hU.mem_nhds (hbU z hz))).div (p.differentiable z) (hbp z hz hne)

  set F : ℂ → G → ℂ := fun z g => Function.update (fun w => Q w g) s₀ (v g) z with hF
  have hFQ : ∀ g z, z ≠ s₀ → F z g = Q z g := fun g z hne => by
    show Function.update (fun w => Q w g) s₀ (v g) z = Q z g
    exact Function.update_of_ne hne _ _
  have hFs : ∀ g, F s₀ g = v g := fun g => by
    show Function.update (fun w => Q w g) s₀ (v g) s₀ = v g
    exact Function.update_self _ _ _
  have hFd : ∀ g, DifferentiableOn ℂ (F · g) (Metric.ball s₀ r₁) := by
    intro g
    refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff (Metric.ball_mem_nhds s₀ hr₁)).1 ⟨?_, ?_⟩
    · intro z hz
      have hne : z ≠ s₀ := fun e => hz.2 (Set.mem_singleton_iff.2 e)
      refine ((hQd g z hz.1 hne).congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [isOpen_ne.mem_nhds hne] with w hw
      exact hFQ g w hw
    · show ContinuousAt (Function.update (fun w => Q w g) s₀ (v g)) s₀
      exact continuousAt_update_same.2 (htend g)
  have hHol : ∀ g, ∀ z ∈ Metric.ball s₀ r₁, HolValueAt (h · g) z (F z g) := by
    intro g z hz
    by_cases hne : z = s₀
    · subst hne; rw [hFs]; exact hv g
    · rw [hFQ g z hne]
      exact (hext g z (hbU z hz)).holValueAt_iff.2
        ((hQd g z hz hne).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

  set ρ : ℝ := 3 * r₁ / 4 with hρ
  have hρ0 : ρ ≠ 0 := by rw [hρ]; positivity
  set K : ℂ × G → ℝ → ℂ := fun y θ => (circleMap 0 ρ θ * Complex.I) •
    ((circleMap s₀ ρ θ - y.1)⁻¹ • (Ê (circleMap s₀ ρ θ) y.2 / p.eval (circleMap s₀ ρ θ))) with hK
  have hcirc : ∀ θ, circleMap s₀ ρ θ ∈ Metric.ball s₀ r₁ := fun θ => by
    rw [Metric.mem_ball, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_pos (by rw [hρ]; positivity)]
    rw [hρ]; linarith
  have hrep : ∀ y ∈ Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G),
      F y.1 y.2 = (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, K y θ := by
    rintro ⟨z, g⟩ ⟨hz, -⟩
    have hzρ : z ∈ Metric.ball s₀ ρ := Metric.ball_subset_ball (by rw [hρ]; linarith) hz
    have hcl : Metric.closedBall s₀ ρ ⊆ Metric.ball s₀ r₁ := Metric.closedBall_subset_ball (by rw [hρ]; linarith)
    rw [← Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      (s := ∅) Set.countable_empty hzρ ((hFd g).continuousOn.mono hcl)
      (fun x hx => (hFd g).differentiableAt (Metric.isOpen_ball.mem_nhds (hcl (Metric.ball_subset_closedBall hx.1))))]
    congr 1
    unfold circleIntegral
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [hK, deriv_circleMap]
    rw [hFQ g _ (circleMap_ne_center hρ0)]
  have hcont : ContinuousOn (fun y : ℂ × G => (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, K y θ)
      (Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) := by
    rw [continuousOn_iff_continuous_restrict]
    show Continuous fun x : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) =>
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, K x.1 θ
    suffices hI : Continuous fun x : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) =>
        ∫ θ in (0 : ℝ)..2 * Real.pi, K x.1 θ from
      (continuous_const : Continuous fun _ : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) =>
        (2 * Real.pi * Complex.I : ℂ)⁻¹).smul hI
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (x : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G))) θ => K x.1 θ) ?_ 0 (2 * Real.pi)
    show Continuous fun q : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) × ℝ => (circleMap 0 ρ q.2 * Complex.I) •
      ((circleMap s₀ ρ q.2 - q.1.1.1)⁻¹ • (Ê (circleMap s₀ ρ q.2) q.1.1.2 / p.eval (circleMap s₀ ρ q.2)))
    have hc1 : Continuous fun q : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) × ℝ => circleMap s₀ ρ q.2 :=
      (continuous_circleMap s₀ ρ).comp continuous_snd
    have hE : Continuous fun q : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) × ℝ =>
        Ê (circleMap s₀ ρ q.2) q.1.1.2 :=
      hc.comp_continuous (f := fun q : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) × ℝ =>
        (circleMap s₀ ρ q.2, q.1.1.2)) (hc1.prodMk (continuous_snd.comp (continuous_subtype_val.comp continuous_fst)))
        (fun q => ⟨hbU _ (hcirc q.2), Set.mem_univ _⟩)
    have hP : Continuous fun q : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) × ℝ => p.eval (circleMap s₀ ρ q.2) :=
      p.continuous.comp hc1
    have hz : Continuous fun q : ↥(Metric.ball s₀ (r₁ / 2) ×ˢ (Set.univ : Set G)) × ℝ => q.1.1.1 :=
      continuous_fst.comp (continuous_subtype_val.comp continuous_fst)
    refine ((continuous_circleMap 0 ρ).comp continuous_snd |>.mul continuous_const).smul ?_
    refine ((hc1.sub hz).inv₀ fun q => ?_).smul (hE.div hP fun q => ?_)
    · have hq : q.1.1.1 ∈ Metric.ball s₀ ρ := Metric.ball_subset_ball (by rw [hρ]; linarith) q.1.2.1
      exact sub_ne_zero.2 (circleMap_ne_mem_ball hq q.2)
    · exact hbp _ (hcirc q.2) (circleMap_ne_center hρ0)
  refine ⟨r₁ / 2, F, by positivity, hcont.congr hrep, fun g => (hFd g).mono (Metric.ball_subset_ball (by linarith)),
    hFs, fun g z hz => hHol g z (Metric.ball_subset_ball (by linarith) hz)⟩

end PositivityTheory.SiegelWeilFormula.Atop

end
end

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Atop

open PositivityTheory.SiegelWeilFormula.KMain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem genAt (hG : AbsSt.GenCore) (c : ℂ) (hT : TAll) (hAux : AuxiliaryPrimeFunction) (hFM : FockMem) (hLo : LocOpEx)
    (hLI : LocInst) (hGS : GSplit) (hGI : GIinv) (hGD : GIdil) (hPK : PolyKFin) (hSK : SecK) (hEW : EisWk)
    (d : SD σ) (R : RD d) (w : InfinitePlace F) {Ψ : Mx F E d.m d.n → ℂ} (hΨ : Ψ ∈ R.away w)
    {φ : PX d.m d.n →ₗ[ℂ] d.Fn} (hφ : R.IsLift w Ψ φ)
    (hvac : ∀ x, HolValueAt (fun z => d.eis (d.sec0 (φ 1)) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I (φ 1) x))
    (P : PX d.m d.n) (x : d.G) :
    HolValueAt (fun z => d.eis (d.sec0 (φ P)) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I (φ P) x) := by
  have hEA := eisAll_of hSK hEW d
  obtain ⟨hTB, -, -, hTT, hTA⟩ := hT
  obtain ⟨L, hL⟩ := hLo F E σ d R w
  obtain ⟨sL, ρ, p, q, e, -, hLD, hsL, hρ⟩ := hLI F E σ d R w L hL
  have hfock := (hFM F E σ d R).2.1 w Ψ hΨ
  have hKF : ∀ P, d.KFin (φ P) := fun P =>
    hPK F E σ d R (φ P) (hφ P).1 (by rw [(hφ P).2]; exact hfock.1 P)
  have hom : ∀ k : GR d.n, InK (mR k) → ∀ P, d.om (R.ι w k) (φ P) = φ (ρ k P) := by
    intro k hk P
    have h1 := (hL k (fP P) (isSw_fP P)).2 Ψ hfock.2 (φ P) (hφ P).1 (hφ P).2
    rw [hρ k P hk] at h1
    have hmem : d.om (R.ι w k) (φ P) - φ (ρ k P) ∈ d.sch := d.sch.sub_mem (om_mem d _ (hφ P).1) (hφ _).1
    refine sub_eq_zero.mp ((hTB F E σ d).2.2 _ hmem ?_)
    rw [← Tl_apply, map_sub, Tl_apply, Tl_apply, h1, (hφ _).2, sub_self]
  let Il : PX d.m d.n →ₗ[ℂ] (d.G → ℂ) :=
    { toFun := fun P => c • d.I (φ P)
      map_add' := fun P Q => by rw [map_add (f := _), I_add d hTT hTA (hφ P).1 (hφ Q).1, smul_add]
      map_smul' := fun a P => by rw [map_smul, I_smul d hTT a (hφ P).1, RingHom.id_apply, smul_comm] }
  let sl : PX d.m d.n →ₗ[ℂ] (d.G → ℂ) := (secl d).comp φ
  obtain ⟨-, -, hTG, hLC, hT2, hSC⟩ := hAux F E σ d
  have hE1 : d.Eis (d.sec0 (φ 1)) (s0 d.m d.n) := hEA (φ 1) (hKF 1)
  obtain ⟨U, pp, Ê, t, hUo, hRD, hs0, hp, hhol, hcont, hinv, hconv⟩ := hE1 (s0 d.m d.n)
  have hCore : AbsSt.GlobCore (fun _ => true) (2 * Real.pi) sL ρ d.G (par2 σ d.Y) (rat2 σ d.Y) (R.ι w) (s0 d.m d.n)
      d.Ht sl Il :=
    { ιcont := R.cont w
      split := by
        intro g
        obtain ⟨x, y, c, r, hr, hg, hx⟩ := hGS F E σ d R w L hL Ψ hΨ φ hφ g
        refine ⟨x, y, c, r, hr, hg, fun y' => ⟨(hx y').1, fun P => ?_⟩⟩
        rw [hsL]
        exact (hx y').2 P
      Icont := by
        show Continuous (c • d.I (φ 1))
        exact ((hTA F E σ d).2.2 (φ 1) (hφ 1).1).2.1.const_smul c
      Ileft := by
        intro γ hγ g
        show c * d.I (φ 1) (γ * g) = c * d.I (φ 1) g
        rw [((hTA F E σ d).2.2 (φ 1) (hφ 1).1).2.2 γ hγ g]
      Ik := by
        intro P g k hk
        show c * thetaMean d.om d.S d.μ d.D (φ P) (g * R.ι w k) = c * thetaMean d.om d.S d.μ d.D (φ (ρ k P)) g
        unfold thetaMean
        simp only [map_mul, Module.End.mul_apply, (hTT F E σ d (φ P) (hφ P).1).2, hom k hk P]
      Iinv := by
        intro g a b P
        show c * d.I (φ (hOp (fun _ => true) (2 * Real.pi) a b P)) g = 0
        rw [hGI F E σ d R w Ψ hΨ φ hφ g a b P, mul_zero]
      Idil := by
        intro g X a ha
        obtain ⟨U, H, hU, hR, hc, hH⟩ := hGD F E σ d R w Ψ hΨ φ hφ g X a ha
        refine ⟨U, fun y z => c * H y z, hU, hR, continuousOn_const.mul hc,
          fun y => ⟨(hH y).1.const_mul c, fun t => ?_, fun r => ?_⟩⟩
        · show c * H y t = c * d.I (φ 1) (g * R.ι w (y * a t))
          rw [(hH y).2.1 t]
        · show iteratedDeriv r (fun z => c * H y z) 0 = c * d.I (φ ((dil (2 * Real.pi) X ^ r) 1)) (g * R.ι w y)
          rw [iteratedDeriv_const_mul' c r (H y)]
          show c * iteratedDeriv r (H y) 0 = _
          rw [(hH y).2.2 r]
      eis := ⟨U, pp, Ê, t, hUo, hRD, hs0, hp, hhol, hcont, hinv, hconv⟩ }
  have hVac : AbsSt.VacData (par2 σ d.Y) (rat2 σ d.Y) (s0 d.m d.n) d.Ht sl Il := by
    obtain ⟨r, Fv, hr, hFc, hFd, hF0, hFv⟩ := vacData_of (fun z g => d.eis (d.sec0 (φ 1)) (s0 d.m d.n) z g)
      (s0 d.m d.n) (fun g => c * d.I (φ 1) g) U pp Ê t hUo hRD hs0 hp hhol hcont (fun z hz g => (hconv z hz).2 g)
      hvac
    exact ⟨r, Fv, hr, hFc, hFd, hF0, hFv⟩
  exact hG d.m d.n (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ hLD
    d.G (par2 σ d.Y) (rat2 σ d.Y) (R.ι w) (s0 d.m d.n) d.Ht sl Il hCore hVac P x

end PositivityTheory.SiegelWeilFormula.Atop

end
end
