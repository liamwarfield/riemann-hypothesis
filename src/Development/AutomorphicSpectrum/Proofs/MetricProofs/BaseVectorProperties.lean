module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFifth
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviChartRegularityStatementHolds
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagRatioFieldEq
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagMinorTrdeg
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseVectorProperties
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseVectorProperties
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem eval_eq_zero_of_mem_mCoordIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {w : (Σ k, ι k) → ℂ} {f : MRing ι} (hf : f ∈ mCoordIdeal w) : eval w (map (Int.castRingHom ℂ) f) = 0 := by
  have h : (mConeMap w : MRing ι →+* MvPolynomial K ℂ) f = 0 := RingHom.mem_ker.mp hf
  have key : ((MvPolynomial.eval (fun _ : K => (1 : ℂ))).comp (mConeMap w : MRing ι →+* MvPolynomial K ℂ) : MRing ι →+* ℂ)
      = (MvPolynomial.eval w).comp (MvPolynomial.map (Int.castRingHom ℂ)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [mConeMap]
    · intro p
      simp [mConeMap]
  have := RingHom.congr_fun key f
  simp only [RingHom.comp_apply] at this
  rw [← this, h, map_zero]

theorem bvec_good : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, FC.bvec BM l b ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt (BM.F l) (mCoordIdeal (FC.bvec BM l b)) ∧ (∀ k, FC.bvec BM l b ⟨k, (BM.F l).c k⟩ = 1) ∧ SameOrbit (FC.bvec BM l b) (BM.Rb.lift b b) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM l b hb
  have hgood : M.GoodAt (BM.F l) (mCoordIdeal (BM.Rb.lift b b)) := BM.good l b hb
  have hne : ∀ k, BM.Rb.lift b b ⟨k, (BM.F l).c k⟩ ≠ 0 := fun k =>
    GlobalTheory.CompanionTheory.Ar.PB.FibreCount.chart_ne (hgood.1 k)
  have hbv : ∀ q, GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec BM l b q
      = (BM.Rb.lift b b ⟨q.1, (BM.F l).c q.1⟩)⁻¹ * BM.Rb.lift b b q := fun q => by
    simp only [GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec, div_eq_inv_mul]
  have horb : SameOrbit (GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec BM l b) (BM.Rb.lift b b) := by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit
    exact ⟨fun k => (BM.Rb.lift b b ⟨k, (BM.F l).c k⟩)⁻¹, fun k => inv_ne_zero (hne k), funext hbv⟩
  have hideal : mCoordIdeal (GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec BM l b) = mCoordIdeal (BM.Rb.lift b b) :=
    GlobalTheory.CompanionTheory.Ar.PB.FibreCount.mCoordIdeal_eq_of_orbit horb
  have hone : ∀ k, GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec BM l b ⟨k, (BM.F l).c k⟩ = 1 := fun k => by
    rw [hbv]; exact inv_mul_cancel₀ (hne k)
  have hmem : BM.Rb.lift b b ∈ mcPts (mCoordIdeal M.x) := BM.Rb.mem b b (BM.Rb.mem_U b)
  have hpt : GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec BM l b ∈ mcPts (mCoordIdeal M.x) := by
    simp only [mcPts, Set.mem_ofPred_eq]
    refine ⟨fun k => ⟨(BM.F l).c k, by rw [hone k]; exact one_ne_zero⟩, fun f hf => ?_⟩
    apply eval_eq_zero_of_mem_mCoordIdeal
    rw [hideal]
    exact GlobalTheory.CompanionTheory.Ar.PB.CPts.mCoordIdeal_le hmem hf
  refine ⟨hpt, ?_, hone, horb⟩
  rw [hideal]
  exact hgood

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseVectorPropertiesStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_vector_properties : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, FC.bvec BM l b ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt (BM.F l) (mCoordIdeal (FC.bvec BM l b)) ∧ (∀ k, FC.bvec BM l b ⟨k, (BM.F l).c k⟩ = 1) ∧ SameOrbit (FC.bvec BM l b) (BM.Rb.lift b b) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_good | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_good | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_good <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalSectionOfPotentialOnModel
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalSectionOfPotentialOnModel
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

theorem isCompatChart_atlas {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X) (j : Fin A.n) :
    IsCompatChart A (A.chart j) :=
  fun k => ⟨A.holo k j, A.holo j k⟩

theorem potential_pos_of_section :
    ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (M : XModel D) (Φ : LocPot M.Xc), IsPotential M.atlas Φ → (∀ x, ∀ y₀ ∈ (Φ).U x ∩ Set.univ, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Φ).U x ∩ Set.univ ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (mCoordIdeal D.y) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Φ).φ x y' - (fun z => Real.log (D.A'.h z)) (s y') = (G y').re) → IsPosPot M.atlas Φ := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D M Φ hΦ hloc x j y hy v hv
  classical
  set e := M.atlas.chart j with he
  have hcompat : IsCompatChart M.atlas e := isCompatChart_atlas M.atlas j
  have hsrc : e.symm y ∈ e.source := e.map_target hy.1
  obtain ⟨U, hUo, hyU, hUsub, s, hs, hsh, G, hG, hrel⟩ := hloc x (e.symm y) ⟨hy.2, trivial⟩
  set V : Set (Fin D.n → ℂ) := e.target ∩ e.symm ⁻¹' U with hV
  have hVo : IsOpen V := e.isOpen_inter_preimage_symm hUo
  have hyV : y ∈ V := ⟨hy.1, hyU⟩
  have hVn : V ∈ 𝓝 y := hVo.mem_nhds hyV
  set τ : (Fin D.n → ℂ) → (Σ k, ι k) → ℂ := fun u => s (e.symm u) with hτdef
  have hτ : AnalyticOnNhd ℂ τ V := fun u hu => analyticAt_pi_iff.2 fun p => hsh p j u hu
  have hg : AnalyticAt ℂ (G ∘ e.symm) y := hG j y hyV
  have hτmem : ∀ u ∈ V, τ u ∈ mcPts (mCoordIdeal D.y) ∧ M.proj (τ u) = e.symm u := fun u hu => hs _ hu.2
  have hz : τ y ∈ mcPts (mCoordIdeal D.y) := (hτmem y hyV).1
  have hpz : M.proj (τ y) = e.symm y := (hτmem y hyV).2
  have hτy : AnalyticAt ℂ τ y := hτ y hyV
  set w := fderiv ℂ τ y v with hwdef

  set L : ℂ → Fin D.n → ℂ := fun σ => y + σ • v with hL
  have hLd : HasDerivAt L v 0 := by
    have h := ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add y
    simp only [id, one_smul] at h
    exact h
  have hL0 : L 0 = y := by simp [hL]
  have hLn : ∀ᶠ σ in 𝓝 (0 : ℂ), L σ ∈ V :=
    hLd.continuousAt.preimage_mem_nhds (by rw [hL0]; exact hVn)
  set γ : ℂ → (Σ k, ι k) → ℂ := fun σ => τ (L σ) with hγdef
  have hγ0 : γ 0 = τ y := by simp [hγdef, hL0]
  have hγw : HasDerivAt γ w 0 :=
    (hτy.differentiableAt.hasFDerivAt).comp_hasDerivAt_of_eq (0 : ℂ) hLd hL0.symm

  have htan : IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal D.y) (τ y) w := by
    intro f hf
    have hder := hasDerivAt_eval_comp (map (Int.castRingHom ℂ) f) hγw
    rw [hγ0] at hder
    have hzero : (fun σ => eval (γ σ) (map (Int.castRingHom ℂ) f)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
      filter_upwards [hLn] with σ hσ
      exact (hτmem _ hσ).1.2 f hf
    exact hder.unique ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hzero)

  have hnt : ∀ c : K → ℂ, w ≠ torusSmul c (τ y) := by
    intro c hwc
    obtain ⟨W, hWo, hzW, F, hFd, hF⟩ :=
      projHoloLocal II Ψ K ι Ω E D M e hcompat (τ y) hz (by rw [hpz]; exact hsrc)
    have hFz : HasFDerivAt F (fderiv ℂ F (τ y)) (τ y) :=
      (hFd.differentiableAt (hWo.mem_nhds hzW)).hasFDerivAt
    have hFγ : HasFDerivAt F (fderiv ℂ F (τ y)) (γ 0) := hγ0 ▸ hFz
    have hWγ : ∀ᶠ σ in 𝓝 (0 : ℂ), γ σ ∈ W :=
      hγw.continuousAt.preimage_mem_nhds (hWo.mem_nhds (hγ0 ▸ hzW))
    have h1 : fderiv ℂ F (τ y) w = v := by
      refine (hFγ.comp_hasDerivAt (0 : ℂ) hγw).unique (hLd.congr_of_eventuallyEq ?_)
      filter_upwards [hLn, hWγ] with σ hσ hσW
      rw [Function.comp_apply, ← (hF (γ σ) ⟨hσW, (hτmem _ hσ).1⟩).2, (hτmem _ hσ).2, e.right_inv hσ.1]
    set δ : ℂ → (Σ k, ι k) → ℂ := fun σ => torusSmul (fun k => Complex.exp (σ * c k)) (τ y) with hδ
    have hδ0 : δ 0 = τ y := by
      funext p
      simp [hδ, torusSmul]
    have hδd : HasDerivAt δ (torusSmul c (τ y)) 0 := by
      refine hasDerivAt_pi.2 fun p => ?_
      have h := (((hasDerivAt_id (0 : ℂ)).mul_const (c p.1)).cexp).mul_const (τ y p)
      simpa [hδ, torusSmul] using h
    have hδmem : ∀ σ, δ σ ∈ mcPts (mCoordIdeal D.y) := fun σ =>
      ComponentDataEquivalence.mcPts_torus D.arith.2.1.2.1 hz fun k => Complex.exp_ne_zero _
    have hδproj : ∀ σ, M.proj (δ σ) = M.proj (τ y) := fun σ =>
      ((M.fibre (τ y) hz (δ σ) (hδmem σ)).2 ⟨_, fun k => Complex.exp_ne_zero _, rfl⟩).symm
    have hWδ : ∀ᶠ σ in 𝓝 (0 : ℂ), δ σ ∈ W :=
      hδd.continuousAt.preimage_mem_nhds (hWo.mem_nhds (hδ0 ▸ hzW))
    have h2 : fderiv ℂ F (τ y) (torusSmul c (τ y)) = 0 := by
      have hFz' : HasFDerivAt F (fderiv ℂ F (τ y)) (δ 0) := hδ0 ▸ hFz
      refine (hFz'.comp_hasDerivAt (0 : ℂ) hδd).unique
        ((hasDerivAt_const (0 : ℂ) (e (M.proj (τ y)))).congr_of_eventuallyEq ?_)
      filter_upwards [hWδ] with σ hσW
      rw [Function.comp_apply, ← (hF (δ σ) ⟨hσW, hδmem σ⟩).2, hδproj σ]
    exact hv (h1.symm.trans (hwc ▸ h2))

  have hO : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∈ 𝓝 (τ y) :=
    MuRegSmooth.isOpen_blocks.mem_nhds hz.1
  have hlogA : ContDiffAt ℝ 2 (fun z => Real.log (D.A'.h z)) (τ y) :=
    ((D.A'_pos.1.contDiffAt hO).of_le (WithTop.coe_le_coe.2 le_top)).log (D.A'.pos _ hz.1).ne'
  have hc1 : ContDiffAt ℝ 2 ((fun z => Real.log (D.A'.h z)) ∘ τ) y :=
    hlogA.comp y (hτy.restrictScalars.contDiffAt (n := 2))
  have hc2 : ContDiffAt ℝ 2 (fun u => ((G ∘ e.symm) u).re) y := by
    have h := (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp y
      (hg.restrictScalars.contDiffAt (n := 2))
    simpa only [Function.comp_def, Complex.reCLM_apply] using h
  have hev : (Φ.φ x ∘ e.symm) =ᶠ[𝓝 y]
      fun u => ((fun z => Real.log (D.A'.h z)) ∘ τ) u + (1 : ℝ) * ((G ∘ e.symm) u).re := by
    filter_upwards [hVn] with u hu
    have := hrel _ hu.2
    simp only [Function.comp_apply, one_mul, hτdef]
    linarith
  have hpos := D.A'_pos.2 (τ y) hz w htan hnt
  rw [levi_congr hev, levi_add_smul 1 hc1 hc2, levi_re_analytic hg, levi_comp v hτy hlogA]
  rw [mul_zero, add_zero]
  exact hpos

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalSectionOfPotentialOnModelStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_section_of_potential_on_model : ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (M : XModel D) (Φ : LocPot M.Xc), IsPotential M.atlas Φ → (∀ x, ∀ y₀ ∈ (Φ).U x ∩ Set.univ, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Φ).U x ∩ Set.univ ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (mCoordIdeal D.y) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Φ).φ x y' - (fun z => Real.log (D.A'.h z)) (s y') = (G y').re) → IsPosPot M.atlas Φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.potential_pos_of_section | exact GlobalTheory.CompanionTheory.Ar.Giv.potential_pos_of_section | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.potential_pos_of_section <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameMinorValueFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameMinorValueFormula
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.TwRead
open GlobalTheory.CompanionTheory.Ar.PB.CPts GlobalTheory.CompanionTheory.Ar.PB.ValRing

section Read

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} (M : FlagModel y Ψ N j)


include M in
theorem off_step {p : Ψ × Fin N} {A : Matrix (Fin N) (Fin N) ℂ} (hA : IsBlockDiag j A) (I : Finset (Fin N))
    (hI : ¬ IsStepRows N j p.2 I) : minorIJ A I (stepCols N j p.2) = 0 :=
  ((GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le).2.1 A I hA hI).resolve_right
    (Finset.nonempty_iff_ne_empty.1 (stepCols_nonempty M.j_le p.2))

theorem pluck_eq {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) {zb : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hzb : zb ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal zb)) {p : Ψ × Fin N} {k : K}
    (hp : M.blk p = some k) {A : Matrix (Fin N) (Fin N) ℂ} (hA : IsBlockDiag j A) {z : (Σ k, ι k) → ℂ} {α : ℂ}
    (hz : ∀ m : ι k, z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ A I (stepCols N j p.2))
    (I₀ : Finset (Fin N)) (hI₀ : IsStepRows N j p.2 I₀) :
    pluck M F zb k z I₀ = α * minorIJ A I₀ (stepCols N j p.2) := by
  let val := regVal hzb
  let uA : (Σ k, ι k) → Finset (Fin N) → regRing M.x zb :=
    fun q I => ⟨F.u q I, exists_isValueAt hzb (hG.2.1 q I).1⟩
  let vA : Finset (Fin N) → (Σ k, ι k) → regRing M.x zb :=
    fun I q => ⟨F.u' I q, exists_isValueAt hzb (hG.2.1 q I).2⟩
  have rel : ∀ I', IsStepRows N j p.2 I' →
      ∑ m : ι k, val (vA I₀ ⟨k, m⟩) * val (uA ⟨k, m⟩ I') = if I₀ = I' then 1 else 0 := fun I' hI' => by
    have e : ∑ m : ι k, vA I₀ ⟨k, m⟩ * uA ⟨k, m⟩ I' = if I₀ = I' then 1 else 0 := by
      apply Subtype.ext
      have := hF.2.2.1 p k hp I₀ I' hI₀ hI'
      split_ifs at this ⊢ <;> simpa [uA, vA] using this
    have e' := congrArg val e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at e'
    simp only [map_mul] at e'
    rw [e']
    split_ifs <;> simp
  have key : ∀ I, (∑ m : ι k, val (vA I₀ ⟨k, m⟩) * val (uA ⟨k, m⟩ I)) * minorIJ A I (stepCols N j p.2) =
      if I = I₀ then minorIJ A I₀ (stepCols N j p.2) else 0 := fun I => by
    by_cases hI : IsStepRows N j p.2 I
    · rw [rel I hI]
      by_cases e : I = I₀
      · subst e; simp
      · simp [e, Ne.symm e]
    · have e : I ≠ I₀ := fun e => hI (e ▸ hI₀)
      rw [off_step M hA I hI, if_neg e, mul_zero]
  have read : ∑ m : ι k, val (vA I₀ ⟨k, m⟩) * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ A I (stepCols N j p.2) =
      minorIJ A I₀ (stepCols N j p.2) := by
    calc _ = ∑ I, (∑ m : ι k, val (vA I₀ ⟨k, m⟩) * val (uA ⟨k, m⟩ I)) * minorIJ A I (stepCols N j p.2) := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun m _ => ?_
          rw [mul_assoc]
          rfl
      _ = _ := by simp only [key]; simp
  rw [← read, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hz m, mul_left_comm]
  rfl

end Read

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (p : Ψ × Fin N) (k : K) (A g : Matrix (Fin N) (Fin N) ℂ) (z : (Σ k, ι k) → ℂ) (α : ℂ) (J : Finset (Fin N)), M.IsFrame F → zb ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal zb) → M.blk p = some k → IsBlockDiag j A → (∀ m : ι k, z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ A I (stepCols N j p.2)) → twMinor M F zb p.2 k g z J = α * minorIJ (g * A) J (stepCols N j p.2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F zb p k A g z α J hF hzb hG hp hA hz
  unfold twMinor
  rw [(GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le).1 g A J (stepCols N j p.2), Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun I _ => ?_
  split_ifs with hI
  · rw [pluck_eq M hF hzb hG hp hA hz I hI]
    ring
  · rw [off_step M hA I hI]
    ring

end GlobalTheory.CompanionTheory.Ar.PB.WMan.TwRead
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameMinorValueFormulaStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_minor_value_formula : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (p : Ψ × Fin N) (k : K) (A g : Matrix (Fin N) (Fin N) ℂ) (z : (Σ k, ι k) → ℂ) (α : ℂ) (J : Finset (Fin N)), M.IsFrame F → zb ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal zb) → M.blk p = some k → IsBlockDiag j A → (∀ m : ι k, z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ A I (stepCols N j p.2)) → twMinor M F zb p.2 k g z J = α * minorIJ (g * A) J (stepCols N j p.2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.TwRead.main | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.TwRead.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.TwRead.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithmeticHeight
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithmeticHeight
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Cover

open GlobalTheory.CompanionTheory.Ar.PB.ValRing

section Val

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem isValueAt_of_orbit {y : (Σ k, ι k) → Ω} {s : Ω} {z z' : (Σ k, ι k) → ℂ} {v : ℂ}
    (ho : SameOrbit z' z) (hv : IsValueAt y s z v) : IsValueAt y s z' v := by
  obtain ⟨c, hc, rfl⟩ := ho
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
  have hne : (∏ k, c k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  refine ⟨d, g, h, hg, hh, hy, heq, ?_, ?_⟩
  · rw [eval_smul_homog h d hh c z]
    exact mul_ne_zero hne hz0
  · rw [eval_smul_homog h d hh c z, eval_smul_homog g d hg c z, mul_div_mul_left _ _ hne]

theorem valAt_eq_of_orbit {y : (Σ k, ι k) → Ω} {s : Ω} {z z' : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) (hz' : z' ∈ mcPts (mCoordIdeal y)) (ho : SameOrbit z' z)
    (hs : ∃ v, IsValueAt y s z v) : valAt y s z' = valAt y s z := by
  obtain ⟨v, hv⟩ := hs
  rw [valAt_eq hz hv, valAt_eq hz' (isValueAt_of_orbit ho hv)]

end Val

section Points

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem fstPt_mem {k₀ : K} {P' : Ideal (MRing fun o : Option K => ι (o.getD k₀))} {Q : Ideal (MRing ι)}
    (hI : imageZ (fun p : (Σ k, ι k) => (⟨some p.1, p.2⟩ : Σ o : Option K, ι (o.getD k₀))) P' = Q)
    {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (hz : z ∈ mcPts P') : fstPt k₀ z ∈ mcPts Q := by
  subst hI
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 (some k)
    exact ⟨i, hi⟩
  · have := hz.2 _ hf
    exact (CPts.eval_rename_block _ z f).symm.trans this

end Points

section Minors

variable {N j : ℕ}

theorem minorIJ_shear {C : Finset (Fin N)} {ca cb : Fin N} (t : ℂ) (h : cb ∉ C) :
    minorIJ (1 + Matrix.single cb ca t) C C = 1 := by
  have e : (1 + Matrix.single cb ca t).submatrix (C.orderEmbOfFin rfl) (C.orderEmbOfFin rfl) =
      (1 : Matrix (Fin N) (Fin N) ℂ).submatrix (C.orderEmbOfFin rfl) (C.orderEmbOfFin rfl) := by
    ext x y
    have hx : cb ≠ C.orderEmbOfFin rfl x := fun e => h (e ▸ Finset.orderEmbOfFin_mem _ _ _)
    simp [Matrix.add_apply, Matrix.single_apply, hx]
  have h1 := CPts.minorIJ_one (R := ℂ) C
  unfold minorIJ at h1 ⊢
  rw [dif_pos rfl] at h1 ⊢
  rw [e, h1]

theorem cb_notMem {a ca cb : Fin N} (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) :
    cb ∉ stepCols N j a := by
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : (a : ℕ) + 1 ≤ j
  · simp only [lastCol, if_pos h] at hca
    rw [if_pos h]
    omega
  · simp only [lastCol, if_neg h] at hca
    rw [if_neg h]
    omega

end Minors

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem pluck_of_flag (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F)
    {zb : (Σ k, baseIdx ι M.blk k) → ℂ} (hzb : zb ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal zb))
    {p : Ψ × Fin N} {k : K} (hp : M.blk p = some k) {w : (Σ k, ι k) → ℂ} {H : Matrix (Fin N) (Fin N) ℂ}
    (hH : IsBlockDiag j H) {A : ℂ}
    (hw : ∀ m : ι k, w ⟨k, m⟩ = A * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ H I (stepCols N j p.2))
    {I : Finset (Fin N)} (hI : IsStepRows N j p.2 I) :
    pluck M F zb k w I = A * minorIJ H I (stepCols N j p.2) := by
  let val := CPts.regVal hzb
  let uA : (Σ k, ι k) → Finset (Fin N) → CPts.regRing M.x zb :=
    fun q I => ⟨F.u q I, exists_isValueAt hzb (hG.2.1 q I).1⟩
  let vA : Finset (Fin N) → (Σ k, ι k) → CPts.regRing M.x zb :=
    fun I q => ⟨F.u' I q, exists_isValueAt hzb (hG.2.1 q I).2⟩
  have rel : ∀ I', IsStepRows N j p.2 I' →
      ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) zb * valAt M.x (F.u ⟨k, m⟩ I') zb = if I = I' then 1 else 0 :=
    fun I' hI' => by
      have e : ∑ m : ι k, vA I ⟨k, m⟩ * uA ⟨k, m⟩ I' = if I = I' then 1 else 0 := by
        apply Subtype.ext
        have := hF.2.2.1 p k hp I I' hI hI'
        split_ifs at this ⊢ <;> simpa [uA, vA] using this
      have e' := congrArg val e
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at e'
      simp only [map_mul] at e'
      refine e'.trans ?_
      split_ifs <;> simp
  unfold pluck
  simp only [hw]
  calc ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) zb *
        (A * ∑ I', valAt M.x (F.u ⟨k, m⟩ I') zb * minorIJ H I' (stepCols N j p.2))
      = A * ∑ I', (∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) zb * valAt M.x (F.u ⟨k, m⟩ I') zb) *
          minorIJ H I' (stepCols N j p.2) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun I' _ => Finset.sum_congr rfl fun m _ => by ring
    _ = A * minorIJ H I (stepCols N j p.2) := by
        congr 1
        rw [Finset.sum_eq_single I]
        · rw [rel I hI, if_pos rfl, one_mul]
        · intro I' _ hne
          by_cases hs : IsStepRows N j p.2 I'
          · rw [rel I' hs, if_neg (Ne.symm hne), zero_mul]
          · rw [minorIJ_block_zero hH hs, mul_zero]
        · simp

theorem twMinor_of_flag (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F)
    {zb : (Σ k, baseIdx ι M.blk k) → ℂ} (hzb : zb ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal zb))
    {p : Ψ × Fin N} {k : K} (hp : M.blk p = some k) {w : (Σ k, ι k) → ℂ} {H : Matrix (Fin N) (Fin N) ℂ}
    (hH : IsBlockDiag j H) {A : ℂ}
    (hw : ∀ m : ι k, w ⟨k, m⟩ = A * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ H I (stepCols N j p.2))
    (g : Matrix (Fin N) (Fin N) ℂ) (J : Finset (Fin N)) :
    twMinor M F zb p.2 k g w J = A * minorIJ (g * H) J (stepCols N j p.2) := by
  unfold twMinor
  rw [minorIJ_mul_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun I hI => by
    rw [pluck_of_flag M hF hzb hG hp hH hw (Finset.mem_filter.1 hI).2]]
  refine (Finset.sum_congr rfl fun I _ => by ring).trans (Finset.sum_subset (Finset.filter_subset _ _) fun I _ hI => ?_)
  have hs : ¬ IsStepRows N j p.2 I := fun h => hI (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  rw [minorIJ_block_zero hH hs, mul_zero, mul_zero]

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2) → ∀ z ∈ mcPts (wP M τ a k₀ ca cb), ∃ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h ∧ z ∈ wO M Rb τ a k₀ ca cb F kb V r h := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb hb hba hblk hca hcb hA z hz
  obtain ⟨hW, -, -, hImg, -⟩ := GlobalTheory.T.flag_adjacent_swap_varieties_arithmetic K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hba hblk hca hcb hA
  obtain ⟨bs, fr, -⟩ := CPts.main K ι Φ y Ψ N j M
  have hz1 : fstPt k₀ z ∈ mcPts (mCoordIdeal y) := fstPt_mem hImg hz
  have hzb : baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x) := bs _ hz1
  obtain ⟨F, hF, hG⟩ := fr _ hzb
  have hnon : Nonempty Rb.X := by
    obtain ⟨x, -⟩ := Rb.surj _ hzb fun h => by
      have := h.2 1 Submodule.mem_top
      simp at this
    exact ⟨x⟩
  obtain ⟨r, hr1, hr2⟩ := GlobalTheory.T.exists_continuous_orbit_section _ _ _ n Rb hnon
  have hx0 := hr1 _ hzb
  obtain ⟨kb, V, bl, hsrc, hV, hBC⟩ := GlobalTheory.T.exists_base_chart_at_good_point K ι Φ y Ψ N j M n Rb F (r (baseOf M k₀ z))
    (by rw [CovMap.mCoordIdeal_eq_of_sameOrbit hx0]; exact hG)
  obtain ⟨hblm, hblnorm, hblgood, hblorb⟩ := hBC.2.2.2.2 _ hV
  rw [(Rb.A.chart kb).left_inv hsrc] at hblorb
  generalize hzc : bl (Rb.A.chart kb (r (baseOf M k₀ z))) = zc at hblm hblnorm hblgood hblorb
  have horb : SameOrbit zc (baseOf M k₀ z) := orbit_trans (orbit_symm hblorb) hx0
  have hval : ∀ s, (∃ v, IsValueAt M.x s zc v) → valAt M.x s (baseOf M k₀ z) = valAt M.x s zc :=
    fun s hs => valAt_eq_of_orbit hblm hzb (orbit_symm horb) hs
  obtain ⟨c₀, hc₀, he⟩ := horb
  let c : Option K → ℂ := fun o => o.elim 1 fun k => if h : ∀ p, M.blk p ≠ some k then c₀ ⟨k, h⟩ else 1
  have hc : ∀ o, c o ≠ 0 := fun o => by
    rcases o with _ | k
    · exact one_ne_zero
    · by_cases h : ∀ p, M.blk p ≠ some k
      · simp only [c, Option.elim_some, dif_pos h]
        exact hc₀ _
      · simp only [c, Option.elim_some, dif_neg h]
        exact one_ne_zero
  let z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ := fun p => c p.1 * z p
  have hz' : z' ∈ mcPts (wP M τ a k₀ ca cb) := mcPts_smul hW.2.1.2.1 c hc hz
  have hbp : basePart M.blk (fstPt k₀ z') = zc := by
    rw [he]
    funext q
    obtain ⟨⟨k, hk⟩, m⟩ := q
    show c (some k) * z ⟨some k, m⟩ = c₀ ⟨k, hk⟩ * z ⟨some k, m⟩
    simp only [c, Option.elim_some, dif_pos hk]
  have hbp2 : basePart M.blk (sndPt k₀ z') = zc := by
    rw [← hbp]
    funext q
    obtain ⟨⟨k, hk⟩, m⟩ := q
    have hne : k ≠ k₀ := fun e => hk (τ, a) (e ▸ hblk)
    show z' (v₁ k₀ ⟨k, m⟩) = z' (v₀ k₀ ⟨k, m⟩)
    rw [v₁_ne hne]
    rfl
  obtain ⟨h, t, H1, H2⟩ := (GlobalTheory.T.log_period_statement K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hba hblk hca hcb hA F z' hF
    (hbp ▸ hblm) (hbp ▸ hblgood) (hbp ▸ hblnorm)).1 hz'
  have hh := H1.2.1
  refine ⟨F, kb, V, bl, r, h, ⟨hb, hba, hblk, hca, hcb, hA, hF, hBC, hr1, hr2, hh⟩, hz, hsrc, ?_, ?_, ?_⟩
  · rw [hzc] at *
    exact hV
  · intro p k hp
    obtain ⟨A, hA0, hA'⟩ := H1.2.2 p k hp
    have hk : c (some k) = 1 := by
      simp only [c, Option.elim_some]
      exact dif_neg fun e => e p hp
    have hw : ∀ m : ι k, fstPt k₀ z ⟨k, m⟩ =
        A * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z) * minorIJ (h p.1) I (stepCols N j p.2) := fun m => by
      have e : fstPt k₀ z' ⟨k, m⟩ = fstPt k₀ z ⟨k, m⟩ := by
        show c (some k) * z ⟨some k, m⟩ = z ⟨some k, m⟩
        rw [hk, one_mul]
      rw [← e, hA' m, hbp]
      congr 1
      exact Finset.sum_congr rfl fun I _ => by
        rw [hval _ (exists_isValueAt hblm (hblgood.2.1 _ I).1)]
    rw [twMinor_of_flag M hF hzb hG hp (hh p.1).1 hw, Matrix.nonsing_inv_mul _ (hh p.1).2.isUnit, CPts.minorIJ_one,
      mul_one]
    exact hA0
  · obtain ⟨A, hA0, hA'⟩ := H2.2.2 (τ, a) k₀ hblk
    have hbd := (H2.2.1 τ).1
    rw [Function.update_self] at hbd
    have hw : ∀ m : ι k₀, sndPt k₀ z ⟨k₀, m⟩ = A * ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z) *
        minorIJ (h τ * (1 + Matrix.single cb ca t)) I (stepCols N j a) := fun m => by
      have e : sndPt k₀ z' ⟨k₀, m⟩ = sndPt k₀ z ⟨k₀, m⟩ := by
        show z' (v₁ k₀ ⟨k₀, m⟩) = z (v₁ k₀ ⟨k₀, m⟩)
        rw [v₁_self]
        exact one_mul _
      rw [← e, hA' m, hbp2, show (τ, a).1 = τ from rfl, Function.update_self]
      congr 1
      exact Finset.sum_congr rfl fun I _ => by
        rw [hval _ (exists_isValueAt hblm (hblgood.2.1 _ I).1)]
    have := twMinor_of_flag M hF hzb hG (p := (τ, a)) hblk hbd hw (h τ)⁻¹ (stepCols N j a)
    refine fun e0 => hA0 ?_
    rw [show (τ, a).2 = a from rfl] at this
    rw [this, Matrix.nonsing_inv_mul_cancel_left _ _ (hh τ).2.isUnit, minorIJ_shear t (cb_notMem hca hcb), mul_one] at e0
    exact e0

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Cover
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithmeticHeightStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_arithmetic_height : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2) → ∀ z ∈ mcPts (wP M τ a k₀ ca cb), ∃ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h ∧ z ∈ wO M Rb τ a k₀ ca cb F kb V r h := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Cover.main | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Cover.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Cover.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PushDownOfArithIntersectionSystem
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PushDownOfArithIntersectionSystem
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv


open GroundTheory.Heights₂.Heights.LowerBoundFree in
theorem hodgeFlagArith : HodgeFlagArith.Statement :=
  HodgeFlagArith.proof HodgeFlagNeZero.proof
    (HodgeFlagRatioTrdeg.proof HodgeFlagRatioFieldEq.full HodgeFlagMinorTrdeg.proof)

theorem pushDown :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement →
      GroundTheory.Heights₂.Heights.LowerBoundFree.PushDown.Statement := fun h =>
  GroundTheory.Heights₂.Heights.LowerBoundFree.PushDown.proof (GlobalTheory.T.generic_degree_of_arith_system h) GlobalTheory.CompanionTheory.Ar.Giv.ProjF.pfStep hodgeFlagArith

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PushDownOfArithIntersectionSystemStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.push_down_of_arith_intersection_system : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → GroundTheory.Heights₂.Heights.LowerBoundFree.PushDown.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.pushDown | exact GlobalTheory.CompanionTheory.Ar.Giv.pushDown | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.pushDown <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartThird
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartThird
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Mem

theorem blockDiag_transvection {N j : ℕ} {ca cb : Fin N} (hc : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) (t : ℂ) :
    IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) := fun x y hxy => by
  have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) x y = 0 := Matrix.one_apply_ne fun e => hxy (by rw [e])
  have h2 : Matrix.single cb ca t x y = 0 := by
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hxy hc.symm
  rw [Matrix.add_apply, h1, h2, add_zero]

theorem det_transvection' {N : ℕ} {ca cb : Fin N} (hc : ca ≠ cb) (t : ℂ) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).det = 1 :=
  Matrix.det_transvection_of_ne cb ca hc.symm t

theorem cols_same_block {N j : ℕ} {a b ca cb : Fin N} (hb : (b : ℕ) = a + 1) (hbj : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j := by
  have := b.2
  have := cb.2
  unfold lastCol at hca
  split_ifs at hca <;> omega

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ w ∈ wD ε V, wPhi M F bl h ε k₀ τ ca cb w ∈ mcPts (wP M τ a k₀ ca cb) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hW w hw
  obtain ⟨-, hE⟩ := GlobalTheory.T.flag_adjacent_chart_second K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hW
  obtain ⟨hHB, hbase, hX⟩ := hE w hw
  obtain ⟨hb, hbj, hblk, hca, hcb, hvar, hF, hBC, -, -, -⟩ := hW
  obtain ⟨hmc, hnorm, hgood, -⟩ := hBC.2.2.2.2 (wB ε w) hw
  have hbase' : basePart M.blk (fstPt k₀ (wPhi M F bl h ε k₀ τ ca cb w)) = bl (wB ε w) := hbase
  have hc : ca ≠ cb := fun e => by rw [e] at hcb; omega
  refine (GlobalTheory.T.log_period_statement K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hbj hblk hca hcb hvar F
    (wPhi M F bl h ε k₀ τ ca cb w) hF (by rw [hbase']; exact hmc) (by rw [hbase']; exact hgood)
    (by rw [hbase']; exact hnorm)).2 ⟨fun τ' => wH h ε τ' w, wT ε w, ?_, ?_⟩
  · refine ⟨(hX τ a).1.1, hHB, fun p k hk => ⟨1, one_ne_zero, fun m => ?_⟩⟩
    rw [one_mul]
    exact (hX p.1 p.2).1.2 k hk m
  · refine ⟨(hX τ a).2.1, fun τ' => ?_, fun p k hk => ⟨1, one_ne_zero, fun m => ?_⟩⟩
    · by_cases e : τ' = τ
      · subst e
        rw [Function.update_self]
        refine ⟨(hHB τ').1.mul (blockDiag_transvection (cols_same_block hb hbj hca hcb) _), ?_⟩
        rw [Matrix.det_mul, det_transvection' hc, mul_one]
        exact (hHB τ').2
      · rw [Function.update_of_ne e]
        exact hHB τ'
    · rw [one_mul]
      have hm := (hX p.1 p.2).2.2 k hk m
      by_cases e : p.1 = τ
      · rw [if_pos e] at hm
        rw [e, Function.update_self]
        rw [e] at hm
        exact hm
      · rw [if_neg e] at hm
        rw [Function.update_of_ne e]
        exact hm

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Mem
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartThirdStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wPhi_mem_mcPts_wP : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ w ∈ wD ε V, wPhi M F bl h ε k₀ τ ca cb w ∈ mcPts (wP M τ a k₀ ca cb) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Mem.main | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Mem.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Mem.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalDegreeBound
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalDegreeBound
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.POpn

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

theorem continuous_upV (v : (Σ k, ιk k) → (Σ k, ι k)) : Continuous (upV v) := by
  refine continuous_pi fun q => ?_
  unfold upV
  by_cases h : ∃ q', v q' = q
  · simp only [dif_pos h]
    exact continuous_apply _
  · simp only [dif_neg h]
    exact continuous_const

theorem continuous_pBase (M : FlagModel y Ψ N j) (v : (Σ k, ιk k) → (Σ k, ι k)) : Continuous (pBase M v) := by
  refine continuous_pi fun q => ?_
  exact (continuous_apply (⟨q.1.1, q.2⟩ : Σ k, ι k)).comp (continuous_upV v)

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∃ O' : Set ((Σ k, ιk k) → ℂ), IsOpen O' ∧ pO M Rb keep v F kb V r h = O' ∩ mcPts (mCoordIdeal (y ∘ v)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε hc
  obtain ⟨hBM, hkp, -, hBC, hr, hrc, -⟩ := hc
  have hmaps : Set.MapsTo (pBase M v) (mcPts (mCoordIdeal (y ∘ v))) (mcPts (mCoordIdeal M.x)) :=
    (GlobalTheory.T.blockMap_frame_restriction K ι Φ y Ψ N j M keep Kk ιk κ v hBM hkp).1
  have key : ∀ z₀ ∈ pO M Rb keep v F kb V r h,
      pO M Rb keep v F kb V r h ∈ 𝓝[mcPts (mCoordIdeal (y ∘ v))] z₀ := by
    rintro z₀ ⟨hz₀, hsrc, hV₀, hm⟩
    have hbm := hmaps hz₀
    have hG : M.GoodAt F (mCoordIdeal (pBase M v z₀)) := by
      obtain ⟨-, -, hgood, horb⟩ := hBC.2.2.2.2 _ hV₀
      rw [(Rb.A.chart kb).left_inv hsrc] at horb
      rwa [CovMap.mCoordIdeal_eq_of_sameOrbit (orbit_trans (orbit_symm (hr _ hbm)) horb)]
    have hrb : ContinuousWithinAt (fun z => r (pBase M v z)) (mcPts (mCoordIdeal (y ∘ v))) z₀ :=
      (hrc _ hbm).comp (continuous_pBase M v).continuousWithinAt hmaps
    have e₁ := hrb.tendsto.eventually_mem ((Rb.A.chart kb).open_source.mem_nhds hsrc)
    have e₂ := (((Rb.A.chart kb).continuousAt hsrc).tendsto.comp hrb.tendsto).eventually_mem (hBC.1.mem_nhds hV₀)
    have tw := GlobalTheory.CompanionTheory.Ar.PB.WMan.Opn.continuousWithinAt_twMinor M F (continuous_pBase M v) (continuous_upV v) hmaps hz₀ hG
    have e₃ : ∀ᶠ z in 𝓝[mcPts (mCoordIdeal (y ∘ v))] z₀, ∀ p k, keep p → M.blk p = some k →
        twMinor M F (pBase M v z) p.2 k (h p.1)⁻¹ (upV v z) (stepCols N j p.2) ≠ 0 := by
      refine eventually_all.2 fun p => eventually_all.2 fun k => ?_
      by_cases hp : keep p ∧ M.blk p = some k
      · exact ((tw p.2 k (h p.1)⁻¹ (stepCols N j p.2)).tendsto.eventually_ne
          (hm p k hp.1 hp.2)).mono fun _ hz _ _ => hz
      · exact Eventually.of_forall fun _ h₁ h₂ => absurd ⟨h₁, h₂⟩ hp
    filter_upwards [self_mem_nhdsWithin, e₁, e₂, e₃] with z h₀ h₁ h₂ h₃
    exact ⟨h₀, h₁, h₂, h₃⟩
  choose! U hU hmem hsub using fun z₀ (hz : z₀ ∈ pO M Rb keep v F kb V r h) =>
    mem_nhdsWithin.1 (key z₀ hz)
  refine ⟨⋃ z₀ ∈ pO M Rb keep v F kb V r h, U z₀, isOpen_biUnion hU, Set.Subset.antisymm ?_ ?_⟩
  · intro z hz
    exact ⟨Set.mem_biUnion hz (hmem z hz), hz.1⟩
  · rintro z ⟨hz, hzA⟩
    obtain ⟨z₀, h₀, hz₀⟩ := Set.mem_iUnion₂.1 hz
    exact hsub z₀ h₀ ⟨hz₀, hzA⟩

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.PFl.POpn
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalDegreeBoundStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameData_local_degree_bound : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∃ O' : Set ((Σ k, ιk k) → ℂ), IsOpen O' ∧ pO M Rb keep v F kb V r h = O' ∩ mcPts (mCoordIdeal (y ∘ v)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PFl.POpn.main | exact GlobalTheory.CompanionTheory.Ar.PB.PFl.POpn.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PFl.POpn.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPointTriangularChangeOrbit
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPointTriangularChangeOrbit
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

private theorem sum_eq_sum_orderEmbOfFin_of_zero_off {N : ℕ} (S : Finset (Fin N)) (F : Fin N → ℂ)
    (hz : ∀ a, a ∉ S → F a = 0) :
    ∑ a, F a = ∑ z : Fin S.card, F (S.orderEmbOfFin rfl z) := by
  calc ∑ a, F a = ∑ a ∈ S, F a :=
        (Finset.sum_subset (Finset.subset_univ S) (fun a _ ha => hz a ha)).symm
    _ = ∑ i : S, F i := (Finset.sum_coe_sort S F).symm
    _ = ∑ z : Fin S.card, F (S.orderEmbOfFin rfl z) :=
        (Fintype.sum_equiv (S.orderIsoOfFin rfl).toEquiv _ _
          (fun z => by simp [Finset.coe_orderIsoOfFin_apply])).symm

private theorem minorIJ_mul_of_block {N : ℕ} (h B : Matrix (Fin N) (Fin N) ℂ) (S I : Finset (Fin N))
    (hB : ∀ a c, c ∈ S → a ∉ S → B a c = 0) :
    minorIJ (h * B) I S = minorIJ h I S * minorIJ B S S := by
  unfold minorIJ
  by_cases e : I.card = S.card
  · rw [dite_eq_left e, dite_eq_left e, dite_eq_left rfl, ← Matrix.det_mul]
    congr 1
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    exact sum_eq_sum_orderEmbOfFin_of_zero_off S (fun a => h (I.orderEmbOfFin e x) a * B a (S.orderEmbOfFin rfl y))
      (fun a ha => by rw [hB a _ (Finset.orderEmbOfFin_mem S rfl y) ha, mul_zero])
  · rw [dite_eq_right e, dite_eq_right e, zero_mul]

private theorem apply_eq_zero_of_mem_stepCols_not_mem {N j : ℕ} (B : Matrix (Fin N) (Fin N) ℂ) (i : Fin N)
    (hd : IsBlockDiag j B) (ht : B.BlockTriangular id) :
    ∀ a c, c ∈ stepCols N j i → a ∉ stepCols N j i → B a c = 0 := by
  intro a c hc ha
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc ha
  have hi := i.isLt
  by_cases hblk : ((a : ℕ) < N - j ↔ (c : ℕ) < N - j)
  · apply ht
    show c < a
    rw [Fin.lt_def]
    split_ifs at hc ha <;> omega
  · exact hd a c hblk

private theorem minorIJ_ne_zero_of_blockTriangular {N : ℕ} (B : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N))
    (ht : B.BlockTriangular id) (hdet : B.det ≠ 0) : minorIJ B S S ≠ 0 := by
  unfold minorIJ
  rw [dite_eq_left rfl]
  have hdiag : ∀ a, B a a ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular ht] at hdet
    exact fun a => (Finset.prod_ne_zero_iff.mp hdet) a (Finset.mem_univ a)
  have htS : (B.submatrix (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl)).BlockTriangular id :=
    fun x y hxy => ht ((S.orderEmbOfFin rfl).strictMono hxy)
  rw [Matrix.det_of_isUpperTriangular htS]
  exact Finset.prod_ne_zero_iff.mpr (fun z _ => hdiag _)

theorem sameOrbit_flagPt_mul : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (h B : Ψ → Matrix (Fin N) (Fin N) ℂ), (∀ τ', IsBlockDiag j (B τ') ∧ (B τ').BlockTriangular id ∧ (B τ').det ≠ 0) → SameOrbit (FC.flagPt M F b fun τ' => h τ' * B τ') (FC.flagPt M F b h) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F b h B hB
  refine Exists.intro (fun k => if hk : ∀ p, M.blk p ≠ some k then (1 : ℂ) else
    minorIJ (B (not_forall.1 hk).choose.1) (stepCols N j (not_forall.1 hk).choose.2)
      (stepCols N j (not_forall.1 hk).choose.2)) ⟨fun k => ?_, ?_⟩
  · dsimp only
    split_ifs with hk
    · exact one_ne_zero
    · generalize (not_forall.1 hk).choose = p
      exact minorIJ_ne_zero_of_blockTriangular (B p.1) (stepCols N j p.2) (hB p.1).2.1 (hB p.1).2.2
  · funext q
    simp only [flagPt]
    split_ifs with hk
    · rw [one_mul]
    · generalize (not_forall.1 hk).choose = p
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun I _ => ?_)
      rw [minorIJ_mul_of_block (h p.1) (B p.1) (stepCols N j p.2) I
        (apply_eq_zero_of_mem_stepCols_not_mem (B p.1) p.2 (hB p.1).1 (hB p.1).2.1)]
      ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPointTriangularChangeOrbitStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_point_triangular_change_orbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (h B : Ψ → Matrix (Fin N) (Fin N) ℂ), (∀ τ', IsBlockDiag j (B τ') ∧ (B τ').BlockTriangular id ∧ (B τ').det ≠ 0) → SameOrbit (FC.flagPt M F b fun τ' => h τ' * B τ') (FC.flagPt M F b h) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.sameOrbit_flagPt_mul | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.sameOrbit_flagPt_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.sameOrbit_flagPt_mul <;> assumption)
end
end
